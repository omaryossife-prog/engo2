"""
Phase 0 (v2): AST-based dependency analysis of main.py for the split plan.

Differences from analyze_main_deps.py (v1):
  * Tracks imports (so each new module knows exactly which stdlib/3rd-party
    names it needs), AnnAssign, and names bound inside top-level try/if blocks.
  * Tracks `global X` rebinding (shared mutable state that CANNOT be moved to a
    different module than its users without breaking semantics).
  * Resolves each reference by scope (ignores locals/params that shadow a
    top-level name) instead of matching any ast.Name with the same text.
  * Finds module-level side effects (executable statements) and dynamic-name
    hazards (__file__, globals(), getattr on module, string class names).
  * Computes strongly-connected components (cycles) between definitions.
  * Emits machine-readable JSON (deps_graph.json) + a human report.

Usage:  python -I analyze_main_deps_v2.py main.py [--out DIR]
"""
from __future__ import annotations

import ast
import builtins
import json
import sys
from collections import defaultdict
from pathlib import Path

BUILTINS = set(dir(builtins))


# --------------------------------------------------------------------------- #
# Collect top-level bindings
# --------------------------------------------------------------------------- #
def _targets(node):
    """Names bound by an assignment-like target."""
    if isinstance(node, ast.Name):
        yield node.id
    elif isinstance(node, (ast.Tuple, ast.List)):
        for e in node.elts:
            yield from _targets(e)
    elif isinstance(node, ast.Starred):
        yield from _targets(node.value)


def collect_bindings(body, out, kind_prefix=""):
    """
    out: name -> list of (kind, node). Descends into top-level Try/If so names
    bound in `try: import x / except: x = None` are seen.
    """
    for node in body:
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            out[node.name].append(("function", node))
        elif isinstance(node, ast.ClassDef):
            out[node.name].append(("class", node))
        elif isinstance(node, ast.Assign):
            for t in node.targets:
                for n in _targets(t):
                    out[n].append(("assign", node))
        elif isinstance(node, ast.AnnAssign):
            for n in _targets(node.target):
                out[n].append(("assign", node))
        elif isinstance(node, ast.AugAssign):
            for n in _targets(node.target):
                out[n].append(("assign", node))
        elif isinstance(node, ast.Import):
            for a in node.names:
                nm = (a.asname or a.name).split(".")[0]
                out[nm].append(("import", node))
        elif isinstance(node, ast.ImportFrom):
            for a in node.names:
                nm = a.asname or a.name
                out[nm].append(("import", node))
        elif isinstance(node, ast.Try):
            collect_bindings(node.body, out)
            for h in node.handlers:
                collect_bindings(h.body, out)
            collect_bindings(node.orelse, out)
            collect_bindings(node.finalbody, out)
        elif isinstance(node, ast.If):
            collect_bindings(node.body, out)
            collect_bindings(node.orelse, out)


# --------------------------------------------------------------------------- #
# Scope-aware free-name collection
# --------------------------------------------------------------------------- #
class FreeNames(ast.NodeVisitor):
    """Collect names that are *read* from module scope inside a def/class/stmt."""

    def __init__(self):
        self.free = set()
        self.global_decl = set()
        self.scopes = [set()]  # stack of local-binding sets

    # helpers
    def _is_local(self, name):
        return any(name in s for s in self.scopes[1:]) if len(self.scopes) > 1 else False

    def _bind(self, name):
        self.scopes[-1].add(name)

    def _bind_args(self, args: ast.arguments):
        for a in (*args.posonlyargs, *args.args, *args.kwonlyargs):
            self._bind(a.arg)
        if args.vararg:
            self._bind(args.vararg.arg)
        if args.kwarg:
            self._bind(args.kwarg.arg)

    def _prescan_locals(self, node):
        """Names assigned anywhere in a function body (Python scoping rule)."""
        loc = set()

        class P(ast.NodeVisitor):
            def visit_Name(s, n):
                if isinstance(n.ctx, (ast.Store, ast.Del)):
                    loc.add(n.id)

            def visit_FunctionDef(s, n):
                loc.add(n.name)  # do not descend

            visit_AsyncFunctionDef = visit_FunctionDef

            def visit_ClassDef(s, n):
                loc.add(n.name)

            def visit_Lambda(s, n):
                pass

            def visit_Import(s, n):
                for a in n.names:
                    loc.add((a.asname or a.name).split(".")[0])

            def visit_ImportFrom(s, n):
                for a in n.names:
                    loc.add(a.asname or a.name)

            def visit_ExceptHandler(s, n):
                if n.name:
                    loc.add(n.name)
                s.generic_visit(n)

            def visit_Global(s, n):
                for x in n.names:
                    loc.discard(x)

            def visit_ListComp(s, n):
                pass

            visit_SetComp = visit_DictComp = visit_GeneratorExp = visit_ListComp

        p = P()
        for stmt in node.body:
            p.visit(stmt)
        # `global` names are NOT local
        for sub in ast.walk(node):
            if isinstance(sub, ast.Global):
                for x in sub.names:
                    loc.discard(x)
        return loc

    def visit_FunctionDef(self, node):
        for d in node.decorator_list:
            self.visit(d)
        for default in (*node.args.defaults, *node.args.kw_defaults):
            if default is not None:
                self.visit(default)
        # annotations are strings under `from __future__ import annotations`,
        # but may still be evaluated by tools; count them as references.
        for a in (*node.args.posonlyargs, *node.args.args, *node.args.kwonlyargs):
            if a.annotation is not None:
                self.visit(a.annotation)
        if node.returns is not None:
            self.visit(node.returns)
        loc = self._prescan_locals(node)
        self.scopes.append(set(loc))
        self._bind_args(node.args)
        for stmt in node.body:
            self.visit(stmt)
        self.scopes.pop()

    visit_AsyncFunctionDef = visit_FunctionDef

    def visit_Lambda(self, node):
        for default in (*node.args.defaults, *node.args.kw_defaults):
            if default is not None:
                self.visit(default)
        self.scopes.append(set())
        self._bind_args(node.args)
        self.visit(node.body)
        self.scopes.pop()

    def _comp(self, node):
        self.scopes.append(set())
        for gen in node.generators:
            self.visit(gen.iter) if False else None
        # bind targets first (comprehension scope), then visit
        for gen in node.generators:
            for n in ast.walk(gen.target):
                if isinstance(n, ast.Name):
                    self._bind(n.id)
        for gen in node.generators:
            self.visit(gen.iter)
            for c in gen.ifs:
                self.visit(c)
        if isinstance(node, ast.DictComp):
            self.visit(node.key)
            self.visit(node.value)
        else:
            self.visit(node.elt)
        self.scopes.pop()

    visit_ListComp = visit_SetComp = visit_DictComp = visit_GeneratorExp = _comp

    def visit_ClassDef(self, node):
        for d in node.decorator_list:
            self.visit(d)
        for b in node.bases:
            self.visit(b)
        for k in node.keywords:
            self.visit(k.value)
        # class body: its own names are class-scope (not visible to methods),
        # approximate by scanning body statements normally.
        for stmt in node.body:
            self.visit(stmt)

    def visit_Global(self, node):
        self.global_decl.update(node.names)

    def visit_Name(self, node):
        if isinstance(node.ctx, ast.Load):
            if not self._is_local(node.id):
                self.free.add(node.id)
        elif node.id in self.global_decl:
            self.free.add(node.id)

    def visit_ExceptHandler(self, node):
        if node.name:
            self._bind(node.name)
        self.generic_visit(node)


def free_names_of(node):
    v = FreeNames()
    v.visit(node)
    return v.free, v.global_decl


# --------------------------------------------------------------------------- #
# SCC (Tarjan)
# --------------------------------------------------------------------------- #
def sccs(graph):
    index = {}
    low = {}
    stack = []
    on = set()
    out = []
    counter = [0]
    sys.setrecursionlimit(10000)

    def strong(v):
        index[v] = low[v] = counter[0]
        counter[0] += 1
        stack.append(v)
        on.add(v)
        for w in graph.get(v, ()):
            if w not in index:
                strong(w)
                low[v] = min(low[v], low[w])
            elif w in on:
                low[v] = min(low[v], index[w])
        if low[v] == index[v]:
            comp = []
            while True:
                w = stack.pop()
                on.discard(w)
                comp.append(w)
                if w == v:
                    break
            out.append(comp)

    for v in list(graph):
        if v not in index:
            strong(v)
    return out


# --------------------------------------------------------------------------- #
def main():
    argv = sys.argv[1:]
    path = Path(argv[0] if argv else "main.py")
    outdir = Path(argv[argv.index("--out") + 1]) if "--out" in argv else Path(".")
    src = path.read_text(encoding="utf-8")
    tree = ast.parse(src, filename=str(path))
    lines = src.splitlines()

    bindings = defaultdict(list)
    collect_bindings(tree.body, bindings)

    import_names = {n for n, b in bindings.items() if any(k == "import" for k, _ in b)}
    defs = {}      # defs we may move: class/function/assign
    for n, b in bindings.items():
        for kind, node in b:
            if kind in ("class", "function", "assign"):
                defs.setdefault(n, (kind, node))

    # name -> list of nodes for multiply-bound names (e.g. try/except fallback)
    multi = {n: [(k, x.lineno) for k, x in b] for n, b in bindings.items() if len(b) > 1}

    # per-definition free names
    uses_defs = {}
    uses_imports = {}
    uses_unknown = {}
    rebinds = {}
    for name, (kind, node) in defs.items():
        free, gdecl = free_names_of(node)
        free.discard(name)
        uses_defs[name] = sorted(f for f in free if f in defs and f != name)
        uses_imports[name] = sorted(f for f in free if f in import_names and f not in defs)
        uses_unknown[name] = sorted(
            f for f in free if f not in defs and f not in import_names and f not in BUILTINS
        )
        rebinds[name] = sorted(gdecl)

    # other top-level statements that reference definitions (side effects)
    side_effects = []
    for node in tree.body:
        if isinstance(node, (ast.Expr, ast.If, ast.Try, ast.For, ast.While, ast.With)):
            # skip pure import-guard Trys
            seg = ast.get_source_segment(src, node) or ""
            free, _ = free_names_of(node)
            side_effects.append(
                {
                    "line": node.lineno,
                    "end": node.end_lineno,
                    "kind": type(node).__name__,
                    "refs_defs": sorted(f for f in free if f in defs),
                    "head": seg.strip().splitlines()[0][:90],
                }
            )
    # module-level assignments that call into definitions at import time
    import_time_calls = []
    for node in tree.body:
        if isinstance(node, (ast.Assign, ast.AnnAssign)):
            val = node.value
            if val is not None and any(isinstance(s, ast.Call) for s in ast.walk(val)):
                free, _ = free_names_of(val)
                refs = sorted(f for f in free if f in defs)
                if refs:
                    tgt = [n for t in (node.targets if isinstance(node, ast.Assign) else [node.target]) for n in _targets(t)]
                    import_time_calls.append({"line": node.lineno, "targets": tgt, "calls_defs": refs})

    # reverse graph
    used_by = defaultdict(set)
    for n, refs in uses_defs.items():
        for r in refs:
            used_by[r].add(n)

    # cycles
    graph = {n: set(r) for n, r in uses_defs.items()}
    cycles = [sorted(c) for c in sccs(graph) if len(c) > 1]

    # dynamic hazards
    hazards = []
    for i, ln in enumerate(lines, 1):
        s = ln.strip()
        if s.startswith("#"):
            continue
        for pat in ("__file__", "globals()", "sys.modules", "__name__", "__main__",
                    "inspect.getsource", "importlib", "pickle", "__import__", "locals()"):
            if pat in s:
                hazards.append((i, pat, s[:110]))
                break

    # Cross-module mutable state: names rebound via `global`
    global_rebound = defaultdict(list)
    for n, g in rebinds.items():
        for x in g:
            global_rebound[x].append(n)

    # output ---------------------------------------------------------------
    report = {
        "file": str(path),
        "total_lines": len(lines),
        "defs": {},
        "imports": sorted(import_names),
        "multi_bound": multi,
        "cycles": cycles,
        "side_effects": side_effects,
        "import_time_calls": import_time_calls,
        "global_rebound": {k: sorted(v) for k, v in global_rebound.items()},
        "hazards": hazards,
    }
    for n, (kind, node) in sorted(defs.items(), key=lambda kv: kv[1][1].lineno):
        start = min([d.lineno for d in getattr(node, "decorator_list", [])] + [node.lineno])
        report["defs"][n] = {
            "kind": kind,
            "start": start,
            "end": node.end_lineno,
            "size": node.end_lineno - start + 1,
            "uses_defs": uses_defs[n],
            "uses_imports": uses_imports[n],
            "unknown_names": uses_unknown[n],
            "used_by": sorted(used_by.get(n, ())),
            "rebinds_globals": rebinds[n],
        }
    outdir.mkdir(parents=True, exist_ok=True)
    (outdir / "deps_graph.json").write_text(
        json.dumps(report, ensure_ascii=False, indent=1), encoding="utf-8"
    )

    # human report
    w = []
    w.append(f"{path}: {len(lines)} lines, {len(defs)} movable top-level names "
             f"({sum(1 for k,_ in defs.values() if k=='class')} classes, "
             f"{sum(1 for k,_ in defs.values() if k=='function')} functions, "
             f"{sum(1 for k,_ in defs.values() if k=='assign')} assignments), "
             f"{len(import_names)} imported names\n")
    w.append("== Names bound more than once at top level (try/except fallbacks etc.) ==")
    for n, v in multi.items():
        w.append(f"  {n}: {v}")
    w.append("\n== Module-level side effects (must stay in import order) ==")
    for s in side_effects:
        w.append(f"  L{s['line']}-{s['end']} {s['kind']}: {s['head']}  -> refs {s['refs_defs']}")
    w.append("\n== Import-time calls in assignments ==")
    for s in import_time_calls:
        w.append(f"  L{s['line']} {s['targets']} calls {s['calls_defs']}")
    w.append("\n== `global X` rebinding (shared mutable state) ==")
    for k, v in global_rebound.items():
        w.append(f"  {k}: rebound by {v}; read by {sorted(used_by.get(k, []))}")
    w.append("\n== Cycles between top-level defs (must be in same module or broken) ==")
    w.append("  " + ("none" if not cycles else ""))
    for c in cycles:
        w.append(f"  {c}")
    w.append("\n== Names used but not defined/imported/builtin (possible bugs) ==")
    any_unknown = False
    for n, d in report["defs"].items():
        if d["unknown_names"]:
            any_unknown = True
            w.append(f"  {n}: {d['unknown_names']}")
    if not any_unknown:
        w.append("  none")
    w.append("\n== Dynamic-name hazards ==")
    for ln, pat, s in hazards:
        w.append(f"  L{ln} [{pat}] {s}")
    w.append("\n== Per-definition table (source order) ==")
    w.append(f"{'start':>6} {'end':>6} {'size':>5}  {'kind':<8} {'name':<42} out in")
    for n, d in report["defs"].items():
        w.append(f"{d['start']:>6} {d['end']:>6} {d['size']:>5}  {d['kind']:<8} {n:<42} "
                 f"{len(d['uses_defs']):>3} {len(d['used_by']):>3}")
    (outdir / "deps_report_v2.txt").write_text("\n".join(w) + "\n", encoding="utf-8")
    print("\n".join(w[:1]))
    print(f"wrote {outdir/'deps_graph.json'} and {outdir/'deps_report_v2.txt'}")


if __name__ == "__main__":
    main()
