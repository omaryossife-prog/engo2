"""
Mechanical, verbatim splitter for main.py -> several modules.

* Never edits code: every top-level statement (with its leading comments) is
  copied byte-for-byte into exactly one module.
* The only generated text is each module's import header (original import
  statements copied verbatim + explicit `from engo_x import name, ...`).
* Reads main.py, writes everything into --out (main.py itself is untouched).

Usage: python -I split_main.py main.py --out split_out
"""
from __future__ import annotations

import ast
import builtins
import importlib.util
import sys
from collections import defaultdict
from pathlib import Path

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("an", HERE / "analyze_main_deps_v2.py")
an = importlib.util.module_from_spec(spec)
spec.loader.exec_module(an)

HEADER_END = 66  # statements ending at/before this line are the import header

# module name -> list of (first_line, last_line) ranges of ORIGINAL file (inclusive),
# matched against each statement's own [lineno..end_lineno] (decorators included).
MODULES = {
    "engo_base": [(68, 943)],
    "engo_widgets": [(944, 1256), (2071, 3903)],
    "engo_office": [(1257, 2070)],
    "engo_document": [(3904, 11511)],
    "engo_ai_core": [(11512, 13127)],
    "engo_markdown": [(13128, 13862)],
    "engo_ai_chat": [(13863, 16505)],
    "engo_ai_workers": [(16506, 18009)],
    "engo_live": [(18010, 21555)],
    "engo_app_dialogs": [(21556, 23201)],
    "main": [(23202, 10**9)],
}
# statements forced into a module regardless of range (by bound name)
FORCE = {"APP_VERSION": "main", "_ANNOTATION_CLIPBOARD": "engo_document", "resource_path": "engo_base",
         "AIRequestWorker": "engo_ai_core", "TextAnnotationEditorDialog": "engo_widgets"}
# names only referenced through strings (globals().get("...")) -> must be imported
FORCE_IMPORT = {"main": ["_MATH_TEXT_CACHE"]}


def module_of(node):
    for nm in an_bound(node):
        if nm in FORCE:
            return FORCE[nm]
    for mod, ranges in MODULES.items():
        for a, b in ranges:
            if a <= node.lineno and node.end_lineno <= b:
                return mod
    raise SystemExit(f"statement at line {node.lineno}-{node.end_lineno} not covered by any module")


def an_bound(node):
    d = defaultdict(list)
    an.collect_bindings([node], d)
    return set(d)


def stmt_start(node):
    return min([node.lineno] + [x.lineno for x in getattr(node, "decorator_list", [])])


def main():
    argv = sys.argv[1:]
    src_path = Path(argv[0])
    out = Path(argv[argv.index("--out") + 1])
    src = src_path.read_text(encoding="utf-8")
    lines = src.splitlines(keepends=True)
    tree = ast.parse(src)

    header = [n for n in tree.body if n.end_lineno <= HEADER_END]
    body = [n for n in tree.body if n.end_lineno > HEADER_END]
    assert header and all(isinstance(n, (ast.ImportFrom, ast.Import, ast.Try)) for n in header), "unexpected header"
    first_future = header[0]
    assert isinstance(first_future, ast.ImportFrom) and first_future.module == "__future__"

    # names provided by header imports -> node
    hdr_names = defaultdict(list)
    for n in header[1:]:
        for nm in an_bound(n):
            hdr_names[nm].append(n)

    # segments: statement text incl. leading comment/blank lines since previous stmt
    segs = []  # (module, node, text)
    prev_end = HEADER_END
    for n in body:
        start_incl_comments = prev_end + 1
        text = "".join(lines[start_incl_comments - 1:n.end_lineno])
        segs.append((module_of(n), n, text))
        prev_end = n.end_lineno
    assert prev_end == len(lines) or not "".join(lines[prev_end:]).strip(), "trailing text lost"

    # who defines each movable name
    owner = {}
    for mod, n, _ in segs:
        for nm in an_bound(n):
            if nm in hdr_names:
                continue
            owner.setdefault(nm, mod)

    # per-module free-name usage
    uses = defaultdict(set)
    for mod, n, _ in segs:
        free, _g = an.free_names_of(n)
        uses[mod] |= free
    for mod, names in FORCE_IMPORT.items():
        uses[mod] |= set(names)

    out.mkdir(parents=True, exist_ok=True)
    cross = defaultdict(lambda: defaultdict(set))  # mod -> srcmod -> names
    for mod in MODULES:
        defined_here = {nm for m, n, _ in segs if m == mod for nm in an_bound(n)}
        for nm in sorted(uses[mod]):
            if nm in owner and owner[nm] != mod and nm not in defined_here:
                cross[mod][owner[nm]].add(nm)

    # module-level graph + cycle check
    g = {m: set(cross[m]) for m in MODULES}
    cyc = [c for c in an.sccs(g) if len(c) > 1]
    if cyc:
        print("MODULE IMPORT CYCLES:", cyc)
        for c in cyc:
            for a in c:
                for b in c:
                    if b in cross[a]:
                        print(f"  {a} -> {b}: {sorted(cross[a][b])[:8]}")
        raise SystemExit(1)

    for mod in MODULES:
        parts = []
        used = uses[mod]
        hdr_nodes = [first_future]
        # header nodes that bind a used name (keep original order)
        need = []
        for n in header[1:]:
            if an_bound(n) & used:
                need.append(n)
        hdr_nodes += need
        h = []
        h.append("".join(lines[first_future.lineno - 1:first_future.end_lineno]).rstrip("\n") + "\n\n")
        for n in need:
            h.append("".join(lines[n.lineno - 1:n.end_lineno]).rstrip("\n") + "\n")
        imports = []
        for srcmod in sorted(cross[mod]):
            names = sorted(cross[mod][srcmod])
            imports.append(f"from {srcmod} import (\n" + "".join(f"    {x},\n" for x in names) + ")\n")
        banner = f"# Auto-split from main.py (verbatim move; do not reformat).\n"
        text = banner + "".join(h) + ("\n" + "".join(imports) if imports else "") + "\n"
        body_text = "".join(t for m, _, t in segs if m == mod)
        if not body_text.startswith("\n"):
            body_text = "\n" + body_text
        fname = "main.py" if mod == "main" else f"{mod}.py"
        (out / fname).write_text(text + body_text, encoding="utf-8", newline="")
        print(f"{fname:<22} {len((text+body_text).splitlines()):>6} lines  imports-from: {sorted(cross[mod])}")


if __name__ == "__main__":
    main()
