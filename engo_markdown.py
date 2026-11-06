# Auto-split from main.py (verbatim move; do not reformat).
from __future__ import annotations

import io
import uuid
import re
import html as html_module
import threading
from collections import OrderedDict, deque
from pathlib import Path
from PyQt6.QtCore import QObject, Qt, QSize, QSizeF, QRect, QRectF, QPoint, QPointF, QEvent, QTimer, QPropertyAnimation, QParallelAnimationGroup, QVariantAnimation, QEasingCurve, QSettings, QUrl, QThread, QRunnable, QThreadPool, QMarginsF, QStandardPaths, QDir, pyqtSignal, QBuffer, QByteArray, QIODevice, QMimeData, QSignalBlocker
from PyQt6.QtGui import QColor, QPalette, QImage, QPixmap, QIcon, QFileSystemModel, QPainter, QPen, QBrush, QKeySequence, QShortcut, QAction, QCursor, QPolygonF, QPainterPath, QPainterPathStroker, QDesktopServices, QPdfWriter, QPageSize, QTextDocument, QTextCursor, QFont, QDrag, QContextMenuEvent, QMouseEvent
from PyQt6.QtWidgets import (
    QApplication, QMainWindow, QWidget, QFrame, QLabel, QPushButton, QToolButton, QBoxLayout,
    QCheckBox, QColorDialog, QFileDialog, QHBoxLayout, QVBoxLayout, QScrollArea, QAbstractScrollArea,
    QListWidget, QListWidgetItem, QListView, QAbstractItemView, QTreeWidget, QTreeWidgetItem, QTreeView, QSpinBox,
    QSizePolicy, QStatusBar, QMessageBox, QSplitter, QTabWidget, QDialog,
    QDialogButtonBox, QInputDialog, QButtonGroup, QLineEdit, QStackedWidget, QTabBar, QMenu, QComboBox,
    QTextBrowser, QTextEdit, QProgressBar, QGridLayout, QStyledItemDelegate, QStyle, QSlider, QWidgetAction, QToolTip, QGraphicsOpacityEffect
)



def _normalize_markdown_for_display(markdown_text: str) -> str:
    """Repair common malformed model Markdown without changing fenced code contents."""
    value = str(markdown_text or "").replace("\r\n", "\n").replace("\r", "\n").lstrip("\ufeff")
    # Some models wrap the entire answer in a Markdown code fence instead of returning Markdown.
    wrapper = re.match(r"^\s*```(?:markdown|md|gfm)?\s*\n(.*)\n```\s*$", value, flags=re.I | re.S)
    if wrapper:
        value = wrapper.group(1)
    lines = value.split("\n")
    inside_fence = False
    fence_char = "`"
    fence_len = 3
    fixed = []
    for line in lines:
        match = re.match(r"^\s{0,3}(`{3,}|~{3,})(.*)$", line)
        if match:
            token = match.group(1)
            if not inside_fence:
                inside_fence = True
                fence_char = token[0]
                fence_len = len(token)
            elif token[0] == fence_char and len(token) >= fence_len:
                inside_fence = False
            fixed.append(line)
            continue
        if not inside_fence:
            # Turn typographic bullets into Markdown list markers and normalize 1) lists.
            line = re.sub(r"^(\s*)[•▪◦‣]\s+", r"\1- ", line)
            line = re.sub(r"^(\s*)(\d+)[)]\s+", r"\1\2. ", line)
            # Close an accidental unmatched inline code span on the same line.
            if line.count("`") % 2:
                line += "`"
        fixed.append(line)
    if inside_fence:
        fixed.append(fence_char * fence_len)
    value = "\n".join(fixed).strip()
    # Do not leave unmatched strong/strike delimiters visible as literal punctuation.
    for delimiter in ("**", "~~"):
        count = len(re.findall(re.escape(delimiter), value))
        if count % 2:
            value += delimiter
    return value


def _escape_raw_html_for_markdown(source: str) -> str:
    """Escape raw HTML tags outside code blocks while preserving Markdown and code syntax."""
    output = []
    in_fence = False
    fence_char = "`"
    fence_len = 3
    tag_pattern = re.compile(r"</?[A-Za-z][A-Za-z0-9:-]*(?:\s+[^<>]*?)?\s*/?>|<!--.*?-->")
    inline_code_pattern = re.compile(r"(`+)(.+?)\1")
    for line in str(source or "").splitlines():
        fence = re.match(r"^\s{0,3}(`{3,}|~{3,})", line)
        if fence:
            token = fence.group(1)
            if not in_fence:
                in_fence, fence_char, fence_len = True, token[0], len(token)
            elif token[0] == fence_char and len(token) >= fence_len:
                in_fence = False
            output.append(line)
            continue
        if in_fence:
            output.append(line)
            continue
        saved = []
        def protect_code(match):
            saved.append(match.group(0))
            return f"ENGO_INLINE_CODE_{len(saved)-1}_TOKEN"
        protected = inline_code_pattern.sub(protect_code, line)
        protected = tag_pattern.sub(lambda m: html_module.escape(m.group(0), quote=False), protected)
        for index, original in enumerate(saved):
            protected = protected.replace(f"ENGO_INLINE_CODE_{index}_TOKEN", original)
        output.append(protected)
    return "\n".join(output)


def _prepare_chat_markdown(markdown_text: str) -> str:
    """Normalize common LaTeX math tokens so Markdown output stays readable in Qt."""
    value = _normalize_markdown_for_display(markdown_text)
    value = re.sub(r"\\\[(.*?)\\\]", lambda m: "\n\n" + m.group(1).strip() + "\n\n", value, flags=re.S)
    value = re.sub(r"\\\((.*?)\\\)", lambda m: m.group(1).strip(), value, flags=re.S)
    value = re.sub(r"\$\$(.*?)\$\$", lambda m: "\n\n" + m.group(1).strip() + "\n\n", value, flags=re.S)
    value = re.sub(r"(?<!\\)\$(?!\$)([^$\n]+)(?<!\\)\$", lambda m: m.group(1).strip(), value)
    # LaTeX commands contain ONE literal backslash; use raw strings so they match model output.
    replacements = {
        r"\times": "×", r"\cdot": "·", r"\div": "÷", r"\pm": "±",
        r"\leq": "≤", r"\geq": "≥", r"\neq": "≠", r"\approx": "≈",
        r"\pi": "π", r"\theta": "θ", r"\alpha": "α", r"\beta": "β",
        r"\Delta": "Δ", r"\sqrt": "√", r"\infty": "∞", r"\rightarrow": "→",
        r"\Rightarrow": "⇒", r"\sum": "Σ", r"\int": "∫", r"\degree": "°",
        r"\%": "%", r"\,": " ", r"\;": " ", r"\!": "",
    }
    for source, target in replacements.items():
        value = value.replace(source, target)
    value = re.sub(r"\\(?:text|mathrm|mathbf|operatorname)\s*\{([^{}]*)\}", r"\1", value)
    value = re.sub(r"\\frac\s*\{([^{}]*)\}\s*\{([^{}]*)\}", r"(\1) / (\2)", value)
    value = re.sub(r"\\(?:left|right)", "", value)
    value = value.replace("\\{", "{").replace("\\}", "}")
    # Common equation subscripts/superscripts (DBT_2, x^{2}, 10^{-3}).
    sub = str.maketrans("0123456789+-=()", "₀₁₂₃₄₅₆₇₈₉₊₋₌₍₎")
    sup = str.maketrans("0123456789+-=()", "⁰¹²³⁴⁵⁶⁷⁸⁹⁺⁻⁼⁽⁾")
    value = re.sub(r"_\{?([0-9]+)\}?", lambda m: m.group(1).translate(sub), value)
    value = re.sub(r"\^\{?([0-9+\-=()]+)\}?", lambda m: m.group(1).translate(sup), value)
    # Common LaTeX temperature notation such as ^\\circ C should display as °C (without a stray caret).
    value = re.sub(r"\\textdegree", "°", value, flags=re.I)
    value = re.sub(r"\^\s*\\circ\s*\{?C\}?", "°C", value, flags=re.I)
    value = re.sub(r"\\circ\s*\{?C\}?", "°C", value, flags=re.I)
    value = re.sub(r"\\circ", "°", value, flags=re.I)
    value = re.sub(r"\\(?:quad|qquad|,|;|!)", " ", value)
    value = re.sub(r"\\(?:begin|end)\{(?:aligned|array|equation\*?|gather\*?)\}", "", value)
    value = value.replace(r"\\", "\n")
    value = re.sub(r"\^°C", "°C", value, flags=re.I)
    return value


class _LatexHtmlParser:
    """Small dependency-free LaTeX math renderer for Qt's rich-text HTML subset."""

    SYMBOLS = {
        "times": "×", "cdot": "·", "div": "÷", "pm": "±", "mp": "∓",
        "le": "≤", "leq": "≤", "ge": "≥", "geq": "≥", "neq": "≠",
        "approx": "≈", "equiv": "≡", "propto": "∝", "sim": "∼",
        "pi": "π", "theta": "θ", "alpha": "α", "beta": "β", "gamma": "γ",
        "delta": "δ", "Delta": "Δ", "epsilon": "ε", "varepsilon": "ϵ",
        "zeta": "ζ", "eta": "η", "iota": "ι", "kappa": "κ", "lambda": "λ",
        "mu": "μ", "nu": "ν", "xi": "ξ", "rho": "ρ", "sigma": "σ",
        "Sigma": "Σ", "tau": "τ", "phi": "φ", "varphi": "ϕ", "Phi": "Φ",
        "chi": "χ", "psi": "ψ", "omega": "ω", "Omega": "Ω",
        "infty": "∞", "partial": "∂", "nabla": "∇", "sum": "∑",
        "prod": "∏", "int": "∫", "iint": "∬", "oint": "∮",
        "rightarrow": "→", "leftarrow": "←", "leftrightarrow": "↔",
        "Rightarrow": "⇒", "Leftarrow": "⇐", "Leftrightarrow": "⇔",
        "to": "→", "mapsto": "↦", "therefore": "∴", "because": "∵",
        "degree": "°", "circ": "°", "angle": "∠", "perp": "⊥",
        "parallel": "∥", "in": "∈", "notin": "∉", "subset": "⊂",
        "subseteq": "⊆", "supset": "⊃", "supseteq": "⊇", "cup": "∪",
        "cap": "∩", "emptyset": "∅", "forall": "∀", "exists": "∃",
        "neg": "¬", "land": "∧", "lor": "∨", "top": "⊤", "bot": "⊥",
        "ldots": "…", "cdots": "⋯", "vdots": "⋮", "ddots": "⋱",
        "prime": "′", "dagger": "†", "hbar": "ℏ", "ell": "ℓ",
        "Re": "ℜ", "Im": "ℑ", "{": "{", "}": "}", "%": "%",
        "_": "_", "#": "#", "$": "$", "&": "&",
    }
    OPERATORS = {"lim", "limsup", "liminf", "max", "min", "sup", "inf", "log", "ln", "lg", "sin", "cos", "tan", "cot", "sec", "csc", "arcsin", "arccos", "arctan", "sinh", "cosh", "tanh", "det", "dim", "ker", "Pr", "argmax", "argmin"}
    SPACING = {",": " ", ";": "  ", ":": " ", "!": "", "quad": "　", "qquad": "　　", "enspace": " ", "thinspace": " "}

    def __init__(self, source: str):
        self.source = str(source or "")
        self.pos = 0
        self.length = len(self.source)

    def _skip_spaces(self):
        while self.pos < self.length and self.source[self.pos].isspace():
            self.pos += 1

    def _read_raw_group(self, opening="{", closing="}"):
        self._skip_spaces()
        if self.pos >= self.length or self.source[self.pos] != opening:
            return self._read_atom()
        self.pos += 1
        start = self.pos
        depth = 1
        while self.pos < self.length:
            char = self.source[self.pos]
            if char == "\\":
                self.pos += 2
                continue
            if char == opening:
                depth += 1
            elif char == closing:
                depth -= 1
                if depth == 0:
                    result = self.source[start:self.pos]
                    self.pos += 1
                    return result
            self.pos += 1
        return self.source[start:]

    def _read_atom(self):
        self._skip_spaces()
        if self.pos >= self.length:
            return ""
        if self.source[self.pos] == "{":
            self.pos += 1
            return self._parse(stop_at_brace=True)
        if self.source[self.pos] == "\\":
            return self._parse_command()
        char = self.source[self.pos]
        self.pos += 1
        return html_module.escape(char, quote=False)

    def _parse_command(self):
        self.pos += 1  # backslash
        if self.pos >= self.length:
            return "\\"
        if self.source[self.pos] == "\\":
            self.pos += 1
            return "<br/>"
        if self.source[self.pos].isalpha():
            start = self.pos
            while self.pos < self.length and self.source[self.pos].isalpha():
                self.pos += 1
            command = self.source[start:self.pos]
        else:
            command = self.source[self.pos]
            self.pos += 1

        if command in self.SPACING:
            return self.SPACING[command]
        if command in ("left", "right", "displaystyle", "textstyle", "scriptstyle", "scriptscriptstyle", "limits", "nolimits", "small", "big", "Big", "bigg", "Bigg", "middle"):
            return ""
        if command in ("begin", "end"):
            self._read_raw_group()
            return ""
        if command == "frac" or command in ("dfrac", "tfrac", "cfrac"):
            numerator = self._read_atom()
            denominator = self._read_atom()
            return ("<span class='engo-math-frac'>"
                    "<span class='engo-math-frac-num'>" + numerator + "</span>"
                    "<span class='engo-math-frac-den'>" + denominator + "</span></span>")
        if command == "binom":
            numerator = self._read_atom()
            denominator = self._read_atom()
            return ("<span class='engo-math-binomial'>(<span class='engo-math-frac'>"
                    "<span class='engo-math-frac-num'>" + numerator + "</span>"
                    "<span class='engo-math-frac-den'>" + denominator + "</span></span>)</span>")
        if command == "sqrt":
            self._skip_spaces()
            root_index = ""
            if self.pos < self.length and self.source[self.pos] == "[":
                root_index = self._read_raw_group("[", "]")
            radicand = self._read_atom()
            index_html = ("<sup class='engo-math-root-index'>" + html_module.escape(root_index, quote=False) + "</sup>") if root_index else ""
            return "√" + index_html + "<span class='engo-math-radicand'>" + radicand + "</span>"
        if command in ("text", "textrm", "textnormal", "mathrm", "operatorname", "mathsf", "mathtt"):
            raw = self._read_raw_group()
            return "<span class='engo-math-text' dir='auto'>" + html_module.escape(raw, quote=False).replace("\n", " ") + "</span>"
        if command in ("mathbf", "boldsymbol", "bm"):
            raw = self._read_raw_group()
            return "<strong class='engo-math-bold'>" + _latex_raw_to_html(raw) + "</strong>"
        if command in ("mathit", "mathcal", "mathfrak", "mathbb"):
            raw = self._read_raw_group()
            return "<span class='engo-math-variant'>" + _latex_raw_to_html(raw) + "</span>"
        if command in ("overline", "bar", "widehat", "hat", "tilde", "vec", "underline", "overrightarrow", "overleftarrow", "overleftrightarrow"):
            arg = self._read_atom()
            accents = {"overline": "¯", "bar": "¯", "widehat": "ˆ", "hat": "ˆ", "tilde": "˜", "vec": "⃗", "overrightarrow": "→", "overleftarrow": "←", "overleftrightarrow": "↔"}
            if command == "underline":
                return "<span style='text-decoration:underline'>" + arg + "</span>"
            return "<span class='engo-math-accent'>" + arg + accents.get(command, "") + "</span>"
        if command == "boxed":
            return "<span class='engo-math-boxed'>" + self._read_atom() + "</span>"
        if command == "cancel":
            return "<span style='text-decoration:line-through'>" + self._read_atom() + "</span>"
        if command in ("label", "notag", "nonumber"):
            if command == "label":
                self._read_raw_group()
            return ""
        if command == "tag":
            return "<span class='engo-math-tag'>(" + html_module.escape(self._read_raw_group(), quote=False) + ")</span>"
        if command == "color" or command == "textcolor":
            self._read_raw_group()  # ignore model-selected colors; the application theme owns colors
            if command == "textcolor":
                return self._read_atom()
            return ""
        if command in self.OPERATORS:
            return "<span class='engo-math-operator'>" + command + "</span>"
        if command in self.SYMBOLS:
            return html_module.escape(self.SYMBOLS[command], quote=False)
        # Unknown LaTeX commands are shown as readable words, not silently discarded.
        return html_module.escape(command, quote=False)

    def _parse(self, stop_at_brace=False):
        output = []
        while self.pos < self.length:
            char = self.source[self.pos]
            if char == "}" and stop_at_brace:
                self.pos += 1
                break
            if char == "{":
                self.pos += 1
                output.append(self._parse(stop_at_brace=True))
                continue
            if char in "^_":
                self.pos += 1
                atom = self._read_atom()
                if char == "^":
                    output.append("<sup class='engo-math-script'>" + atom + "</sup>")
                else:
                    output.append("<sub class='engo-math-script'>" + atom + "</sub>")
                continue
            if char == "\\":
                output.append(self._parse_command())
                continue
            if char == "&":
                self.pos += 1
                output.append("<span class='engo-math-align-gap'>　</span>")
                continue
            if char == "\n":
                self.pos += 1
                output.append("<br/>")
                continue
            self.pos += 1
            output.append(html_module.escape(char, quote=False))
        return "".join(output)

    def render(self):
        return self._parse()


def _latex_raw_to_html(source: str) -> str:
    # Re-enter the parser for nested commands inside style wrappers.
    return _LatexHtmlParser(source).render()


_MATH_TEXT_CACHE = OrderedDict()
_MATH_TEXT_CACHE_LIMIT = 180
_MATH_TEXT_LOCK = threading.RLock()
_STIX_MATH_FONTS_READY = None


def _render_latex_math_png(source: str, font_pt: float, color: str, display: bool = False):
    """Render a TeX expression to a tightly-cropped transparent PNG using Matplotlib MathText."""
    expression = str(source or "").strip()
    if not expression:
        return None
    # Normalize common LaTeX aliases to the MathText subset.
    expression = re.sub(r"\\(?:dfrac|tfrac|cfrac)\b", r"\\frac", expression)
    expression = re.sub(r"\\operatorname\s*\{([^{}]+)\}", r"\\mathrm{\1}", expression)
    expression = re.sub(r"\\textstyle\b", "", expression)
    expression = re.sub(r"\\label\s*\{[^{}]*\}", "", expression)
    expression = re.sub(r"\\tag\s*\{([^{}]*)\}", r"\\qquad (\1)", expression)
    expression = expression.replace(r"\textdegree", r"^\circ")
    expression = expression.replace(r"\degree", r"^\circ")
    # Display equations use a larger MathText font and a centered block in Qt.
    # MathText does not implement the TeX \displaystyle switch itself.
    expression = expression.replace(r"\displaystyle", "")

    try:
        from matplotlib import rc_context, get_data_path
        from matplotlib import font_manager
        from matplotlib.font_manager import FontProperties
        from matplotlib.mathtext import math_to_image
        dpi = 180
        size = max(8.0, float(font_pt) * (1.22 if display else 1.0))
        key = (expression, round(size, 2), str(color or "#202020"), dpi, bool(display))
        with _MATH_TEXT_LOCK:
            cached = _MATH_TEXT_CACHE.get(key)
            if cached is not None:
                _MATH_TEXT_CACHE.move_to_end(key)
                return cached
            # Matplotlib bundles STIXGeneral and its large-symbol fonts. Explicitly
            # register those files before MathText resolves the family. The old
            # generic family name "STIX" is not registered on many Windows builds,
            # which produced repeated findfont warnings and DejaVu fallback.
            global _STIX_MATH_FONTS_READY
            if _STIX_MATH_FONTS_READY is None:
                stix_dir = Path(get_data_path()) / "fonts" / "ttf"
                try:
                    for font_path in stix_dir.glob("STIX*.ttf"):
                        font_manager.fontManager.addfont(str(font_path))
                    font_manager.findfont("STIXGeneral", fallback_to_default=False)
                    _STIX_MATH_FONTS_READY = True
                except Exception:
                    _STIX_MATH_FONTS_READY = False
            stix_available = bool(_STIX_MATH_FONTS_READY)
            base_family = "STIXGeneral" if stix_available else "DejaVu Sans"
            math_fontset = "stix" if stix_available else "dejavusans"
            buffer = io.BytesIO()
            properties = FontProperties(family=base_family, size=size)
            with rc_context({
                "savefig.transparent": True,
                "figure.facecolor": (0, 0, 0, 0),
                "savefig.facecolor": (0, 0, 0, 0),
                "savefig.edgecolor": (0, 0, 0, 0),
                "savefig.pad_inches": 0.025,
                "mathtext.fontset": math_fontset,
            }):
                math_to_image(
                    "$" + expression + "$", buffer, prop=properties,
                    dpi=dpi, format="png", color=str(color or "#202020"),
                )
            data = buffer.getvalue()
            if not data:
                return None
            _MATH_TEXT_CACHE[key] = data
            _MATH_TEXT_CACHE.move_to_end(key)
            while len(_MATH_TEXT_CACHE) > _MATH_TEXT_CACHE_LIMIT:
                _MATH_TEXT_CACHE.popitem(last=False)
            return data
    except Exception:
        return None


def _math_png_html(source: str, display: bool, resources, color: str, font_pt: float):
    """Create an HTML image slot backed by a QTextDocument image resource."""
    if resources is None:
        return None
    png_data = _render_latex_math_png(source, font_pt, color, display)
    if not png_data:
        return None
    try:
        image = QImage.fromData(QByteArray(png_data), "PNG")
        if image.isNull():
            return None
        # MathText renders at 180 dpi; DPR 1.875 maps it back to normal UI text sizing.
        image.setDevicePixelRatio(1.875)
        resource_url = "engo-math://" + uuid.uuid4().hex
        resources.append((resource_url, image))
        image_tag = f"<img src='{resource_url}' align='middle' style='border:0; background:transparent;'/>"
        if display:
            return "<div class='engo-math-display' dir='ltr' align='center'>" + image_tag + "</div>"
        return "<span class='engo-math-inline' dir='ltr'>" + image_tag + "</span>"
    except Exception:
        return None


def _split_latex_environment_rows(body: str):
    """Split a matrix/aligned body at top-level row and column separators."""
    rows, current, depth, i = [], [], 0, 0
    while i < len(body):
        char = body[i]
        if char == "\\":
            if i + 1 < len(body) and body[i + 1] == "\\" and depth == 0:
                rows.append("".join(current).strip())
                current = []
                i += 2
                continue
            # Preserve escaped commands and escaped braces as-is.
            current.append(body[i:i + 2])
            i += 2
            continue
        if char == "{":
            depth += 1
        elif char == "}" and depth:
            depth -= 1
        current.append(char)
        i += 1
    if current or not rows:
        rows.append("".join(current).strip())

    result = []
    for row in rows:
        cells, cell, depth, j = [], [], 0, 0
        while j < len(row):
            char = row[j]
            if char == "\\":
                cell.append(row[j:j + 2])
                j += 2
                continue
            if char == "{":
                depth += 1
            elif char == "}" and depth:
                depth -= 1
            if char == "&" and depth == 0:
                cells.append("".join(cell).strip())
                cell = []
            else:
                cell.append(char)
            j += 1
        cells.append("".join(cell).strip())
        result.append(cells)
    return result


def _latex_environment_to_html(source: str, resources, color: str, font_pt: float):
    """Render common aligned, matrix, and cases environments as accessible Qt tables."""
    match = re.search(
        r"\\begin\{(aligned|alignedat|gathered|align\*?|split|gather\*?|equation\*?|matrix|pmatrix|bmatrix|Bmatrix|vmatrix|Vmatrix|cases|array)\}(.*?)\\end\{\1\}",
        source, flags=re.S,
    )
    if not match:
        return None
    environment, body = match.group(1), match.group(2)
    if environment == "array":
        body = re.sub(r"^\s*\{[^{}]*\}", "", body, count=1)
    elif environment == "alignedat":
        body = re.sub(r"^\s*\{\s*\d+\s*\}", "", body, count=1)
    rows = _split_latex_environment_rows(body)
    if not rows:
        return None
    cell_font = float(font_pt) * 1.12
    table_rows = []
    for cells in rows:
        rendered_cells = []
        for cell in cells:
            if not cell:
                rendered_cells.append("&nbsp;")
                continue
            cell_html = _latex_math_to_html(
                cell, False, resources=resources, color=color, font_pt=cell_font,
                allow_environment=False,
            )
            rendered_cells.append(cell_html)
        table_rows.append("<tr>" + "".join("<td>" + item + "</td>" for item in rendered_cells) + "</tr>")

    table = "<table class='engo-math-matrix'><tbody>" + "".join(table_rows) + "</tbody></table>"
    if environment == "cases":
        table = "<table class='engo-math-cases'><tbody>" + "".join(table_rows) + "</tbody></table>"
        content = "<span class='engo-math-left-brace'>{</span>" + table
    elif environment in ("pmatrix",):
        content = "<span class='engo-math-delimiter'>(</span>" + table + "<span class='engo-math-delimiter'>)</span>"
    elif environment in ("bmatrix",):
        content = "<span class='engo-math-delimiter'>[</span>" + table + "<span class='engo-math-delimiter'>]</span>"
    elif environment in ("Bmatrix",):
        content = "<span class='engo-math-delimiter'>{</span>" + table + "<span class='engo-math-delimiter'>}</span>"
    elif environment == "vmatrix":
        content = "<span class='engo-math-delimiter'>|</span>" + table + "<span class='engo-math-delimiter'>|</span>"
    elif environment == "Vmatrix":
        content = "<span class='engo-math-delimiter'>‖</span>" + table + "<span class='engo-math-delimiter'>‖</span>"
    else:
        content = table
    return "<div class='engo-math-display' dir='ltr' align='center'>" + content + "</div>"


def _latex_math_to_html(source: str, display: bool = False, resources=None,
                        color: str = "#202020", font_pt: float = 12.5,
                        allow_environment: bool = True) -> str:
    source = str(source or "").strip()
    if allow_environment:
        environment_html = _latex_environment_to_html(source, resources, color, font_pt)
        if environment_html is not None:
            return environment_html
    image_html = _math_png_html(source, display, resources, color, font_pt)
    if image_html is not None:
        return image_html
    # Graceful fallback keeps formulas readable even if Matplotlib is unavailable
    # or the model uses a LaTeX command outside MathText's supported subset.
    rendered = _LatexHtmlParser(source).render()
    if display:
        return "<div class='engo-math-display' dir='ltr'><span class='engo-math-body'>" + rendered + "</span></div>"
    return "<span class='engo-math-inline' dir='ltr'>" + rendered + "</span>"


def _extract_math_for_markdown(source: str, resources=None, color: str = "#202020", font_pt: float = 12.5):
    """Replace TeX math with safe slots before Markdown parsing; keep code untouched."""
    code_blocks = []

    def hold_code(match):
        token = f"ENGOCODEKEEP{len(code_blocks)}TOKEN"
        code_blocks.append((token, match.group(0)))
        return token

    value = re.sub(r"(?ms)^[ \t]{0,3}(`{3,}|~{3,})[^\n]*\n.*?^[ \t]{0,3}\1[ \t]*$", hold_code, source)
    value = re.sub(r"(?<!`)`+[^`\n]+`+(?!`)", hold_code, value)

    math_slots = []

    def hold_math(match, display):
        token = f"ENGOMATHSLOT{len(math_slots)}TOKEN"
        math_slots.append((token, _latex_math_to_html(
            match.group(1), display, resources=resources, color=color, font_pt=font_pt,
        )))
        return ("\n\n" + token + "\n\n") if display else token

    value = re.sub(r"\$\$(.+?)\$\$", lambda m: hold_math(m, True), value, flags=re.S)
    value = re.sub(r"\\\[(.*?)\\\]", lambda m: hold_math(m, True), value, flags=re.S)
    value = re.sub(r"\\\((.+?)\\\)", lambda m: hold_math(m, False), value, flags=re.S)
    value = re.sub(r"(?<!\\)\$(?!\$)([^$\n]+?)(?<!\\)\$", lambda m: hold_math(m, False), value)

    # Older model replies sometimes emit a standalone TeX equation without $...$.
    # Auto-wrap only obvious equation-only lines; prose, lists, tables, and code stay intact.
    repaired_lines = []
    for line in value.split("\n"):
        stripped = line.strip()
        has_equation = bool(re.search(r"(?:=|\\approx|\\equiv|\\simeq)", stripped))
        has_tex_math = bool(re.search(
            r"(?:\\(?:begin|frac|dfrac|tfrac|sqrt|mathbf|mathrm|times|cdot|pi|Delta|theta|alpha|beta|sum|int)\b|[A-Za-z][A-Za-z0-9']*[_^]\{)",
            stripped,
        ))
        starts_like_formula = bool(re.match(r"^(?:\\begin\{|[A-Za-z][A-Za-z0-9']*[_^]\{|\\(?:frac|dfrac|tfrac|sqrt|sum|int)\b|[A-Za-z][A-Za-z0-9']*\s*=)", stripped))
        is_markdown_structure = bool(re.match(r"^(?:#{1,6}\s|[-*+]\s|>\s|\||```|~~~)", stripped))
        contains_arabic = bool(re.search(r"[\u0600-\u06FF]", stripped))
        if stripped and has_equation and has_tex_math and starts_like_formula and not is_markdown_structure and not contains_arabic:
            token = f"ENGOMATHSLOT{len(math_slots)}TOKEN"
            math_slots.append((token, _latex_math_to_html(
                stripped, True, resources=resources, color=color, font_pt=font_pt,
            )))
            repaired_lines.extend(["", token, ""])
        else:
            repaired_lines.append(line)
    value = "\n".join(repaired_lines)

    # Also typeset common unwrapped identifiers such as P_{v1}, T_{db}, and x^2
    # when they occur inside ordinary Arabic/English prose or Markdown table cells.
    def hold_bare_identifier(match):
        token = f"ENGOMATHSLOT{len(math_slots)}TOKEN"
        math_slots.append((token, _latex_math_to_html(
            match.group(1), False, resources=resources, color=color, font_pt=font_pt,
        )))
        return token

    value = re.sub(
        r"(?<![\w$`\\])([A-Za-z][A-Za-z0-9']*(?:(?:_\{[^{}\n]+\}|\^\{[^{}\n]+\}|_[A-Za-z0-9]+|\^[A-Za-z0-9]+))+)",
        hold_bare_identifier,
        value,
    )

    # Restore fenced and inline code only after math scanning, so $ and TeX in code stay literal.
    for token, original in code_blocks:
        value = value.replace(token, original)
    return value, math_slots


def _replace_markdown_strikethrough(source: str):
    """Protect GFM ~~strike~~ spans so Markdown can still format their contents."""
    code_blocks = []

    def hold_code(match):
        token = f"ENGOSTRIKECODE{len(code_blocks)}TOKEN"
        code_blocks.append((token, match.group(0)))
        return token

    value = re.sub(r"(?ms)^[ \t]{0,3}(`{3,}|~{3,})[^\n]*\n.*?^[ \t]{0,3}\1[ \t]*$", hold_code, source)
    value = re.sub(r"(?<!`)`+[^`\n]+`+(?!`)", hold_code, value)
    value = re.sub(r"~~(?=\S)(.+?\S)~~", lambda m: "ENGOSTRIKEOPEN" + m.group(1) + "ENGOSTRIKECLOSE", value)
    for token, original in code_blocks:
        value = value.replace(token, original)
    return value


def _render_markdown_html(markdown_text: str, font_pt: float = 12.5, resources=None, math_color: str = "#202020") -> str:
    """Render Markdown plus inline/display LaTeX into HTML supported by QTextBrowser."""
    source = _normalize_markdown_for_display(markdown_text or "")
    source, math_slots = _extract_math_for_markdown(
        source, resources=resources, color=math_color, font_pt=font_pt,
    )
    source = _replace_markdown_strikethrough(source)
    direction = "rtl" if re.search(r"[\u0600-\u06FF]", source) else "ltr"
    try:
        import markdown as markdown_lib
        # Escape raw model HTML; only the small, generated math fragments below are trusted.
        safe_source = _escape_raw_html_for_markdown(source)
        body = markdown_lib.markdown(
            safe_source,
            extensions=["tables", "fenced_code", "sane_lists", "nl2br"],
            output_format="html5",
        )
    except Exception:
        doc = QTextDocument()
        doc.setMarkdown(source)
        rendered = doc.toHtml()
        match = re.search(r"<body[^>]*>(.*?)</body>", rendered, flags=re.I | re.S)
        body = match.group(1) if match else "<pre>" + html_module.escape(source) + "</pre>"

    # Match inline keyboard shortcuts/code badges to the active palette.  The chat
    # browser passes its current text color here: dark text means Light theme.
    try:
        light_chat_palette = QColor(math_color).lightness() < 150
    except Exception:
        light_chat_palette = True
    if light_chat_palette:
        inline_code_bg = "#e8eef6"
        inline_code_fg = "#244b80"
        inline_code_border = "#d1dbe8"
        table_border = "#b8c5d5"
        code_block_bg = "#f1f4f8"
        table_header_bg = "#e7edf5"
        table_header_fg = "#263449"
        link_fg = "#245fbd"
    else:
        inline_code_bg = "#18202b"
        inline_code_fg = "#c7dbff"
        inline_code_border = "#35465e"
        table_border = "#4b5b73"
        code_block_bg = "rgba(120,140,170,0.13)"
        table_header_bg = "#27364b"
        table_header_fg = "#edf3ff"
        link_fg = "#73a8ff"

    # The markers are plain text during Markdown parsing. Restore generated math afterward
    # so formulas are not interpreted as emphasis, underscores, or table syntax.
    for token, math_html in math_slots:
        block_match = re.compile(r"<p>\s*" + re.escape(token) + r"\s*</p>", flags=re.I)
        body, count = block_match.subn(lambda _m, value=math_html: value, body, count=1)
        if not count:
            body = body.replace(token, math_html)
        else:
            body = body.replace(token, math_html)
    body = body.replace("ENGOSTRIKEOPEN", "<del>").replace("ENGOSTRIKECLOSE", "</del>")

    return f"""<!doctype html><html><head><meta charset='utf-8'><style>
      body {{ font-family: 'Segoe UI', Arial, sans-serif; font-size: {float(font_pt):.1f}pt; line-height: 1.48; }}
      p {{ margin: 0.28em 0 0.72em 0; }} h1,h2,h3,h4 {{ margin: 0.9em 0 0.4em 0; line-height: 1.25; }}
      ul,ol {{ margin-top: 0.25em; margin-bottom: 0.7em; }} li {{ margin: 0.16em 0; }}
      table {{ border-collapse: collapse; margin: 0.65em 0; }} th,td {{ border: 1px solid {table_border}; padding: 5px 8px; }}
      th {{ background: {table_header_bg}; color: {table_header_fg}; font-weight: bold; }}
      pre {{ white-space: pre-wrap; background: {code_block_bg}; padding: 8px; border-radius: 6px; }}
      code {{ background: {inline_code_bg}; color: {inline_code_fg}; border: 1px solid {inline_code_border}; padding: 1px 4px; border-radius: 4px; }}
      blockquote {{ border-left: 3px solid #7297d8; margin-left: 0; padding-left: 10px; }}
      a {{ color: {link_fg}; }} hr {{ border: 0; border-top: 1px solid #78869a; }}
      sup, sub {{ font-size: 75%; line-height: 0; }}
      .engo-math-inline {{ direction: ltr; unicode-bidi: embed; white-space: nowrap; font-family: 'Cambria Math','Times New Roman',serif; font-size: 1.04em; }}
      .engo-math-display {{ direction: ltr; unicode-bidi: embed; text-align: center; margin: 0.85em 0; padding: 0.35em 0.2em; font-family: 'Cambria Math','Times New Roman',serif; font-size: 1.12em; white-space: normal; }}
      .engo-math-body {{ direction: ltr; }}
      .engo-math-frac {{ display: inline-block; vertical-align: middle; text-align: center; line-height: 1.08; margin: 0 2px; }}
      .engo-math-frac-num {{ display: block; border-bottom: 1px solid currentColor; padding: 0 3px 2px; }}
      .engo-math-frac-den {{ display: block; padding: 2px 3px 0; }}
      .engo-math-binomial {{ white-space: nowrap; }}
      .engo-math-operator {{ font-style: normal; }} .engo-math-bold {{ font-weight: bold; }}
      .engo-math-text {{ font-style: normal; }} .engo-math-variant {{ font-style: italic; }}
      .engo-math-accent {{ text-decoration: overline; }} .engo-math-boxed {{ border: 1px solid currentColor; padding: 1px 4px; }}
      .engo-math-root-index {{ font-size: 65%; vertical-align: top; }}
      .engo-math-radicand {{ border-top: 1px solid currentColor; padding: 0 2px; }}
      .engo-math-tag {{ margin-left: 0.8em; font-size: 80%; }} .engo-math-align-gap {{ padding: 0 0.15em; }}
      .engo-math-inline img {{ vertical-align: middle; border: 0; }}
      .engo-math-display {{ text-align: center; margin: 0.9em 0; padding: 0.45em 0.25em; }}
      .engo-math-matrix, .engo-math-cases {{ display: inline-table; border-collapse: separate; border-spacing: 0.5em 0.16em; margin: 0 0.12em; vertical-align: middle; }}
      .engo-math-matrix td, .engo-math-cases td {{ border: 0; padding: 0 0.12em; text-align: center; background: transparent; }}
      .engo-math-cases td:first-child {{ text-align: right; }} .engo-math-cases td:last-child {{ text-align: left; }}
      .engo-math-delimiter {{ font-family: 'Cambria Math','STIX Two Math',serif; font-size: 2.1em; vertical-align: middle; }}
      .engo-math-left-brace {{ font-family: 'Cambria Math','STIX Two Math',serif; font-size: 3.2em; line-height: 0.7; vertical-align: middle; margin-right: 0.12em; }}
    </style></head><body><div dir='{direction}'>{body}</div></body></html>"""


def _set_markdown_document(document: QTextDocument, markdown_text: str, font_pt: float = 12.5, math_color: str = "#202020"):
    resources = []
    rendered_html = _render_markdown_html(
        markdown_text, font_pt, resources=resources, math_color=math_color,
    )
    for resource_url, image in resources:
        document.addResource(
            QTextDocument.ResourceType.ImageResource, QUrl(resource_url), image,
        )
    document.setHtml(rendered_html)
    return rendered_html


def _set_markdown_browser(browser: QTextBrowser, markdown_text: str, font_pt: float = 12.5):
    try:
        math_color = browser.palette().text().color().name()
    except Exception:
        math_color = "#202020"
    _set_markdown_document(browser.document(), markdown_text, font_pt, math_color)
