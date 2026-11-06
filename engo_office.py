# Auto-split from main.py (verbatim move; do not reformat).
from __future__ import annotations

import os
import tempfile
import io
import hashlib
import zipfile
from copy import deepcopy
try:
    from lxml import etree as office_etree
    OFFICE_XML_BACKEND_ERROR = None
except ImportError as _office_xml_import_error:
    # Keep the PDF viewer and the rest of Engo usable even when the optional
    # native Office XML dependency has not been installed yet. The launcher
    # installs it before startup; direct launches show a helpful message.
    office_etree = None
    OFFICE_XML_BACKEND_ERROR = str(_office_xml_import_error)
import re
import html as html_module
import base64
from pathlib import Path
import pymupdf as fitz  # use the maintained import name; keep fitz alias for existing calls
from PIL import Image, ImageOps, ImageChops, ImageFilter
from PyQt6.QtCore import QObject, Qt, QSize, QSizeF, QRect, QRectF, QPoint, QPointF, QEvent, QTimer, QPropertyAnimation, QParallelAnimationGroup, QVariantAnimation, QEasingCurve, QSettings, QUrl, QThread, QRunnable, QThreadPool, QMarginsF, QStandardPaths, QDir, pyqtSignal, QBuffer, QByteArray, QIODevice, QMimeData, QSignalBlocker
from PyQt6.QtWidgets import (
    QApplication, QMainWindow, QWidget, QFrame, QLabel, QPushButton, QToolButton, QBoxLayout,
    QCheckBox, QColorDialog, QFileDialog, QHBoxLayout, QVBoxLayout, QScrollArea, QAbstractScrollArea,
    QListWidget, QListWidgetItem, QListView, QAbstractItemView, QTreeWidget, QTreeWidgetItem, QTreeView, QSpinBox,
    QSizePolicy, QStatusBar, QMessageBox, QSplitter, QTabWidget, QDialog,
    QDialogButtonBox, QInputDialog, QButtonGroup, QLineEdit, QStackedWidget, QTabBar, QMenu, QComboBox,
    QTextBrowser, QTextEdit, QProgressBar, QGridLayout, QStyledItemDelegate, QStyle, QSlider, QWidgetAction, QToolTip, QGraphicsOpacityEffect
)

from engo_base import (
    APP_NAME,
    IMAGE_DOCUMENT_EXTENSIONS,
    engo_ui_theme_tokens,
)
from engo_widgets import (
    make_icon,
)



def _office_html_run(run) -> str:
    """Convert one Word/PowerPoint run into safe, read-only HTML."""
    text = html_module.escape(str(getattr(run, "text", "") or "")).replace("\n", "<br>")
    if not text:
        return ""
    style = []
    font = getattr(run, "font", None)
    try:
        if font and font.name:
            style.append("font-family:'" + html_module.escape(str(font.name), quote=True) + "'")
    except Exception:
        pass
    try:
        if font and font.size:
            style.append(f"font-size:{max(6, min(48, int(font.size.pt)))}pt")
    except Exception:
        pass
    try:
        color = font.color.rgb if font else None
        if color:
            style.append(f"color:#{color}")
    except Exception:
        pass
    if getattr(run, "bold", False):
        style.append("font-weight:700")
    if getattr(run, "italic", False):
        style.append("font-style:italic")
    if getattr(run, "underline", False):
        style.append("text-decoration:underline")
    # Read back highlights written by Engo from the native DOCX/PPTX OOXML runs.
    try:
        xml_run = getattr(run, "_r", None)
        if xml_run is not None:
            for node in xml_run.iter():
                tag = str(getattr(node, "tag", ""))
                if tag.endswith("}highlight"):
                    rgb = next((child.get("val") for child in node if str(child.tag).endswith("}srgbClr")), None)
                    if rgb:
                        style.append(f"background-color:#{str(rgb).upper()}")
                    else:
                        style.append("background-color:#fff2a8")
                    break
                if tag.endswith("}highlight") and node.get("val"):
                    style.append("background-color:#fff2a8")
                    break
    except Exception:
        pass
    if style:
        text = f'<span style="{";".join(style)}">{text}</span>'
    return text


def _office_html_shell(title: str, body: str) -> str:
    safe_title = html_module.escape(str(title or "Document"))
    return f"""<!DOCTYPE html><html><head><meta charset="utf-8"><style>
    body {{ font-family: "Segoe UI", Arial, sans-serif; color:#242b35; background:#fff; margin:26px; line-height:1.55; }}
    h1,h2,h3,h4 {{ color:#20364f; margin:18px 0 8px; }}
    p {{ margin:5px 0 9px; }}
    table {{ border-collapse:collapse; width:100%; margin:12px 0 18px; }}
    td,th {{ border:1px solid #aeb8c5; padding:6px 9px; vertical-align:top; }}
    th {{ background:#eaf0f7; font-weight:700; }}
    img {{ max-width:100%; height:auto; }}
    .doc-title {{ color:#60738a; border-bottom:1px solid #d5dde7; padding-bottom:10px; margin-bottom:20px; font-size:10pt; }}
    .slide {{ background:#fff; border:1px solid #cbd5e1; border-radius:8px; padding:22px; margin:8px 0; }}
    .slide-title {{ color:#1e3a5f; font-size:19pt; font-weight:700; margin-bottom:16px; }}
    .slide-shape {{ margin:8px 0; padding:7px 10px; border-left:3px solid #7a9cc6; }}
    .slide-image {{ display:block; margin:10px auto; }}
    .slide-note {{ color:#60738a; font-style:italic; }}
    </style><title>{safe_title}</title></head><body>{body}</body></html>"""


def _require_office_xml_backend():
    if office_etree is None:
        raise RuntimeError(
            "Native Word/PowerPoint support needs lxml.\n"
            "Close Engo and start it with run.bat; the launcher will install "
            "the missing package automatically.\n\n"
            f"Details: {OFFICE_XML_BACKEND_ERROR or 'lxml is unavailable'}"
        )


def _docx_document_to_html(path: str) -> str:
    """Read DOCX paragraphs, tables and embedded pictures without editing the source."""
    _require_office_xml_backend()
    from docx import Document
    from docx.text.paragraph import Paragraph
    from docx.table import Table
    from docx.oxml.ns import qn

    document = Document(path)
    parts = [f'<div class="doc-title">{html_module.escape(Path(path).name)} · Native Word</div>']
    body_element = document.element.body
    for block in body_element.iterchildren():
        if block.tag.endswith("}p"):
            paragraph = Paragraph(block, document)
            style_name = str(getattr(getattr(paragraph, "style", None), "name", "") or "")
            heading_match = re.search(r"Heading\s+(\d+)", style_name, re.IGNORECASE)
            if heading_match:
                tag = "h" + str(max(1, min(6, int(heading_match.group(1)))))
            elif style_name.casefold() in ("title", "subtitle"):
                tag = "h1" if style_name.casefold() == "title" else "h3"
            else:
                tag = "p"
            content = "".join(_office_html_run(run) for run in paragraph.runs)
            if not content:
                content = html_module.escape(str(paragraph.text or "")).replace("\n", "<br>")
            align = ""
            try:
                if paragraph.alignment is not None:
                    align = {0:"left", 1:"center", 2:"right", 3:"justify"}.get(int(paragraph.alignment), "")
            except Exception:
                pass
            style = f' style="text-align:{align}"' if align else ""
            if content.strip():
                parts.append(f"<{tag}{style}>{content}</{tag}>")
            # Keep inline images readable even when Word places them within a run.
            try:
                for blip in paragraph._p.xpath('.//a:blip'):
                    rid = blip.get(qn('r:embed'))
                    related = document.part.related_parts.get(rid) if rid else None
                    if related is not None:
                        mime = str(getattr(related, 'content_type', 'image/png') or 'image/png')
                        encoded = base64.b64encode(related.blob).decode('ascii')
                        parts.append(f'<p><img src="data:{mime};base64,{encoded}"></p>')
            except Exception:
                pass
        elif block.tag.endswith("}tbl"):
            table = Table(block, document)
            rows = []
            for row_index, row in enumerate(table.rows):
                cells = []
                for cell in row.cells:
                    cell_html = "<br>".join(
                        html_module.escape(str(p.text or "")) for p in cell.paragraphs if str(p.text or "").strip()
                    )
                    tag = "th" if row_index == 0 else "td"
                    cells.append(f"<{tag}>{cell_html}</{tag}>")
                rows.append("<tr>" + "".join(cells) + "</tr>")
            parts.append("<table>" + "".join(rows) + "</table>")
    return _office_html_shell(Path(path).name, "".join(parts))


def _pptx_slides_to_html(path: str) -> list[str]:
    """Read PPTX slides as non-editable pages with text, tables and embedded pictures."""
    _require_office_xml_backend()
    from pptx import Presentation
    from pptx.enum.shapes import MSO_SHAPE_TYPE
    from pptx.enum.dml import MSO_FILL

    presentation = Presentation(path)
    output = []
    for slide_number, slide in enumerate(presentation.slides, 1):
        parts = [f'<div class="doc-title">{html_module.escape(Path(path).name)} · Slide {slide_number} of {len(presentation.slides)} · Native PowerPoint</div>']
        try:
            fill = slide.background.fill
            if fill.type == MSO_FILL.SOLID:
                rgb = fill.fore_color.rgb
                bg = ("#" + str(rgb)) if rgb is not None else "#ffffff"
            else:
                bg = "#ffffff"
        except Exception:
            bg = "#ffffff"
        parts.append(f'<div class="slide" style="background:{bg}">')
        title_done = False
        for shape in slide.shapes:
            shape_left = max(0, min(100, round(float(shape.left) / max(1, presentation.slide_width) * 100)))
            width_pct = max(8, min(100 - shape_left, round(float(shape.width) / max(1, presentation.slide_width) * 100)))
            shape_style = f'margin-left:{shape_left}%;width:{width_pct}%;'
            try:
                if shape.shape_type == MSO_SHAPE_TYPE.PICTURE:
                    mime = str(getattr(shape.image, "content_type", "image/png") or "image/png")
                    encoded = base64.b64encode(shape.image.blob).decode("ascii")
                    parts.append(f'<div class="slide-shape" style="{shape_style}"><img class="slide-image" src="data:{mime};base64,{encoded}"></div>')
                    continue
            except Exception:
                pass
            try:
                if getattr(shape, "has_table", False):
                    table_html = []
                    for row_index, row in enumerate(shape.table.rows):
                        cells = []
                        for cell in row.cells:
                            cell_text = html_module.escape(str(cell.text or "")).replace("\n", "<br>")
                            tag = "th" if row_index == 0 else "td"
                            cells.append(f"<{tag}>{cell_text}</{tag}>")
                        table_html.append("<tr>" + "".join(cells) + "</tr>")
                    parts.append(f'<div class="slide-shape" style="{shape_style}"><table>{"".join(table_html)}</table></div>')
                    continue
            except Exception:
                pass
            try:
                if getattr(shape, "has_text_frame", False):
                    paragraph_html = []
                    for paragraph in shape.text_frame.paragraphs:
                        runs = "".join(_office_html_run(run) for run in paragraph.runs)
                        if not runs:
                            runs = html_module.escape(str(paragraph.text or "")).replace("\n", "<br>")
                        if runs.strip():
                            paragraph_html.append(f"<p>{runs}</p>")
                    if paragraph_html:
                        block = "".join(paragraph_html)
                        if not title_done and getattr(shape, "is_placeholder", False):
                            parts.append(f'<div class="slide-title">{block}</div>')
                            title_done = True
                        else:
                            parts.append(f'<div class="slide-shape" style="{shape_style}">{block}</div>')
                    continue
            except Exception:
                pass
            try:
                if getattr(shape, "has_chart", False):
                    chart = shape.chart
                    chart_rows = []
                    try:
                        categories = [str(cat.label) for cat in chart.plots[0].categories]
                    except Exception:
                        categories = []
                    series_html = []
                    for series in chart.series:
                        values = list(series.values)
                        series_html.append("<tr><th>" + html_module.escape(str(series.name)) + "</th>" +
                                           "".join(f"<td>{html_module.escape(str(v))}</td>" for v in values) + "</tr>")
                    if categories:
                        chart_rows.append("<tr><th>Category</th>" + "".join(f"<td>{html_module.escape(v)}</td>" for v in categories) + "</tr>")
                    chart_rows.extend(series_html)
                    parts.append(f'<div class="slide-shape" style="{shape_style}"><strong>Chart data</strong><table>{"".join(chart_rows)}</table></div>')
                    continue
            except Exception:
                pass
        parts.append("</div>")
        output.append(_office_html_shell(Path(path).name, "".join(parts)))
    return output


_OFFICE_W_NS = "http://schemas.openxmlformats.org/wordprocessingml/2006/main"
_OFFICE_A_NS = "http://schemas.openxmlformats.org/drawingml/2006/main"
_OFFICE_XML_SPACE = "http://www.w3.org/XML/1998/namespace"


def _office_normalized_text_map(nodes):
    """Join OOXML text nodes and create a map back to their original character offsets."""
    normalized = []
    mapping = []
    pending_space = None
    for node in nodes:
        value = str(node.text or "")
        for offset, char in enumerate(value):
            if char.isspace():
                if normalized and pending_space is None:
                    pending_space = (node, offset)
                continue
            if pending_space is not None:
                normalized.append(" ")
                mapping.append(pending_space)
                pending_space = None
            normalized.append(char)
            mapping.append((node, offset))
    return "".join(normalized), mapping


def _office_set_run_highlight(run, kind: str, color: str = "FFF2A8"):
    if kind == "word":
        rpr_tag = f"{{{_OFFICE_W_NS}}}rPr"
        highlight_tag = f"{{{_OFFICE_W_NS}}}highlight"
        val_attr = f"{{{_OFFICE_W_NS}}}val"
        rpr = run.find(rpr_tag)
        if rpr is None:
            rpr = office_etree.Element(rpr_tag)
            run.insert(0, rpr)
        for old in list(rpr.findall(highlight_tag)):
            rpr.remove(old)
        highlight = office_etree.SubElement(rpr, highlight_tag)
        highlight.set(val_attr, "yellow")
        return

    rpr_tag = f"{{{_OFFICE_A_NS}}}rPr"
    highlight_tag = f"{{{_OFFICE_A_NS}}}highlight"
    color_tag = f"{{{_OFFICE_A_NS}}}srgbClr"
    rpr = run.find(rpr_tag)
    if rpr is None:
        rpr = office_etree.Element(rpr_tag)
        run.insert(0, rpr)
    for old in list(rpr.findall(highlight_tag)):
        rpr.remove(old)
    highlight = office_etree.SubElement(rpr, highlight_tag)
    rgb = office_etree.SubElement(highlight, color_tag)
    rgb.set("val", str(color or "FFF2A8").lstrip("#").upper())


def _office_apply_match_to_paragraph(paragraph, selection: str, kind: str) -> bool:
    """Apply native Office text highlighting to one paragraph, splitting runs when safe."""
    text_tag = f"{{{_OFFICE_W_NS if kind == 'word' else _OFFICE_A_NS}}}{'t'}"
    run_tag = f"{{{_OFFICE_W_NS if kind == 'word' else _OFFICE_A_NS}}}{'r'}"
    nodes = []
    for run in paragraph.iter(run_tag):
        for node in run.iter(text_tag):
            nodes.append(node)
    if not nodes:
        return False

    source_text, mapping = _office_normalized_text_map(nodes)
    wanted = " ".join(str(selection or "").split())
    if not wanted:
        return False
    start = source_text.find(wanted)
    if start < 0:
        # Try a case-insensitive match but retain the original positional map.
        start = source_text.casefold().find(wanted.casefold())
    if start < 0:
        return False
    end = start + len(wanted)
    spans = {}
    for node, char_offset in mapping[start:end]:
        run = node.getparent()
        while run is not None and run.tag != run_tag:
            run = run.getparent()
        if run is None:
            continue
        key = id(run)
        spans.setdefault(key, [run, {}])[1].setdefault(node, []).append(char_offset)

    changed = False
    for run, node_spans in spans.values():
        # Exact character-level highlighting: split simple single-text runs into
        # before / selected / after clones. Complex runs are highlighted as one
        # unit rather than risking loss of fields, drawings, or run properties.
        if len(node_spans) == 1:
            node, offsets = next(iter(node_spans.items()))
            original = str(node.text or "")
            lo, hi = min(offsets), max(offsets) + 1
            children = list(run)
            text_nodes = [child for child in children if child.tag == text_tag]
            safe_children = all(child.tag in (text_tag, f"{{{_OFFICE_W_NS if kind == 'word' else _OFFICE_A_NS}}}{'rPr'}") for child in children)
            if len(text_nodes) == 1 and safe_children:
                chunks = []
                if lo > 0:
                    chunks.append((original[:lo], False))
                chunks.append((original[lo:hi], True))
                if hi < len(original):
                    chunks.append((original[hi:], False))
                if len(chunks) > 1:
                    parent = run.getparent()
                    if parent is not None:
                        insert_at = parent.index(run)
                        parent.remove(run)
                        for chunk_text, selected in chunks:
                            clone = deepcopy(run)
                            clone_text = clone.find(text_tag)
                            clone_text.text = chunk_text
                            if chunk_text[:1].isspace() or chunk_text[-1:].isspace():
                                clone_text.set(f"{{{_OFFICE_XML_SPACE}}}space", "preserve")
                            else:
                                clone_text.attrib.pop(f"{{{_OFFICE_XML_SPACE}}}space", None)
                            if selected:
                                _office_set_run_highlight(clone, kind)
                            parent.insert(insert_at, clone)
                            insert_at += 1
                        changed = True
                        continue
        _office_set_run_highlight(run, kind)
        changed = True
    return changed


def _office_highlight_same_file(path: str, selections: list[str]) -> int:
    """Persist text highlights inside DOCX/PPTX OOXML without changing source text."""
    _require_office_xml_backend()
    path = os.path.abspath(str(path or ""))
    suffix = Path(path).suffix.lower()
    if suffix not in (".docx", ".pptx"):
        raise ValueError("Only DOCX and PPTX files can store native Engo text highlights.")
    if not os.path.isfile(path):
        raise FileNotFoundError(path)
    kind = "word" if suffix == ".docx" else "powerpoint"
    fd, temp_path = tempfile.mkstemp(prefix=".engo_office_", suffix=suffix, dir=os.path.dirname(path) or None)
    os.close(fd)
    try:
        with zipfile.ZipFile(path, "r") as source_zip:
            members = source_zip.infolist()
            payloads = {info.filename: source_zip.read(info.filename) for info in members}
            package_comment = source_zip.comment
        targets = (["word/document.xml"] if kind == "word" else sorted(
            name for name in payloads if re.fullmatch(r"ppt/slides/slide\d+\.xml", name)
        ))
        if not targets or any(name not in payloads for name in targets):
            raise ValueError("The Office document is missing its main content XML.")

        roots = {}
        paragraphs_by_target = {}
        changed_targets = set()
        for target in targets:
            root = office_etree.fromstring(payloads[target])
            roots[target] = root
            if kind == "word":
                paragraphs_by_target[target] = root.findall(".//{%s}p" % _OFFICE_W_NS)
            else:
                paragraphs_by_target[target] = root.findall(".//{%s}p" % _OFFICE_A_NS)

        matched_selections = 0
        for selection in selections:
            parts = [item.strip() for item in re.split(r"[\r\n\u2028\u2029]+", str(selection or "")) if item.strip()]
            if not parts:
                continue
            # Each selected line/paragraph must identify exactly one native
            # paragraph in the entire Office package. This permits the user to
            # queue highlights in any order without silently targeting another
            # repeated phrase.
            selection_matched = True
            for part in parts:
                normalized_part = " ".join(part.split())
                matches = []
                for target in targets:
                    for paragraph in paragraphs_by_target[target]:
                        if kind == "word":
                            text_nodes = paragraph.findall(".//{%s}t" % _OFFICE_W_NS)
                        else:
                            text_nodes = paragraph.findall(".//{%s}t" % _OFFICE_A_NS)
                        paragraph_text, _ = _office_normalized_text_map(text_nodes)
                        probe = paragraph_text
                        needle = normalized_part
                        if needle not in probe:
                            probe, needle = probe.casefold(), needle.casefold()
                        if needle and needle in probe:
                            matches.append((target, paragraph))
                            if len(matches) > 1:
                                break
                    if len(matches) > 1:
                        break
                if not matches:
                    raise ValueError("The selected text was not found in the original Office text. No changes were saved.")
                if len(matches) > 1:
                    raise ValueError("This text appears more than once. Select a longer phrase so Engo can identify the exact occurrence safely. No changes were saved.")
                target, paragraph = matches[0]
                if not _office_apply_match_to_paragraph(paragraph, part, "word" if kind == "word" else "ppt"):
                    selection_matched = False
                    break
                changed_targets.add(target)
            if selection_matched:
                matched_selections += 1

        if not changed_targets or matched_selections == 0:
            raise ValueError("The selected text could not be matched exactly to the Office document. No changes were saved.")

        for target in changed_targets:
            payloads[target] = office_etree.tostring(
                roots[target], encoding="UTF-8", xml_declaration=True, standalone=True
            )
        with zipfile.ZipFile(temp_path, "w") as target_zip:
            for info in members:
                target_zip.writestr(info, payloads[info.filename])
            target_zip.comment = package_comment
        # Atomic replacement keeps the original intact if package writing fails.
        os.replace(temp_path, path)
        return matched_selections
    except Exception:
        try:
            if os.path.exists(temp_path):
                os.remove(temp_path)
        except OSError:
            pass
        raise


class OfficeDocumentReaderDialog(QDialog):
    """Native-format DOCX/PPTX reader with text selection and saved text highlights."""

    askAISelected = pyqtSignal(str, str)

    def __init__(self, path: str, language: str = "en", parent=None):
        super().__init__(parent)
        self.path = os.path.abspath(path)
        self.language = "ar" if str(language or "en").lower().startswith("ar") else "en"
        self._slides = []
        self._slide_index = 0
        self._active_tool = "select"
        self._ignore_office_drag = False
        self._pending_highlights: list[str] = []
        self.setObjectName("officeNativeReader")
        self.setWindowTitle(("قراءة " if self.language == "ar" else "Reading ") + Path(path).name)
        self.setAttribute(Qt.WidgetAttribute.WA_DeleteOnClose, True)
        self.resize(1080, 820)
        if self.language == "ar":
            self.setLayoutDirection(Qt.LayoutDirection.RightToLeft)
        layout = QVBoxLayout(self)
        header = QHBoxLayout()
        title = QLabel(Path(path).name)
        title.setStyleSheet("font-weight:700;font-size:13pt;padding:4px 2px;")
        header.addWidget(title, 1)
        self.native_badge = QLabel("")
        self.native_badge.setStyleSheet("font-size:9pt;font-weight:700;padding:5px 9px;border:1px solid palette(mid);border-radius:6px;")
        header.addWidget(self.native_badge)
        layout.addLayout(header)

        tools = QHBoxLayout()
        self.select_tool_btn = QPushButton("تحديد" if self.language == "ar" else "Select")
        self.select_tool_btn.setIcon(make_icon("select", "#6f9edc", 16))
        self.select_tool_btn.setCheckable(True)
        self.select_tool_btn.setChecked(True)
        self.highlight_tool_btn = QPushButton("تظليل النص" if self.language == "ar" else "Highlight text")
        self.highlight_tool_btn.setIcon(make_icon("highlight", "#d7ae35", 16))
        self.highlight_tool_btn.setCheckable(True)
        self.select_tool_btn.clicked.connect(lambda: self._set_active_tool("select"))
        self.highlight_tool_btn.clicked.connect(lambda: self._set_active_tool("highlight"))
        self.save_changes_btn = QPushButton("حفظ التغييرات" if self.language == "ar" else "Save changes")
        self.save_changes_btn.setIcon(make_icon("save", "#6fa9e8", 16))
        self.save_changes_btn.setEnabled(False)
        self.save_changes_btn.clicked.connect(self._commit_native_highlights)
        self.discard_changes_btn = QPushButton("تجاهل" if self.language == "ar" else "Discard")
        self.discard_changes_btn.setEnabled(False)
        self.discard_changes_btn.clicked.connect(self._discard_native_highlights)
        self.tool_group = QButtonGroup(self)
        self.tool_group.setExclusive(True)
        self.tool_group.addButton(self.select_tool_btn)
        self.tool_group.addButton(self.highlight_tool_btn)
        tools.addWidget(self.select_tool_btn)
        tools.addWidget(self.highlight_tool_btn)
        tools.addWidget(self.save_changes_btn)
        tools.addWidget(self.discard_changes_btn)
        self.tool_hint = QLabel("اسحب فوق النص. ابدأ من النص نفسه؛ السحب من صورة أو مساحة فارغة لا يحدد الكلمات." if self.language == "ar" else
                                "Drag over text. Start on the text itself; a drag starting on an image or blank space will not select words.")
        self.tool_hint.setWordWrap(True)
        self.tool_hint.setStyleSheet("color:palette(mid);font-size:9pt;padding:3px 6px;")
        tools.addWidget(self.tool_hint, 1)
        layout.addLayout(tools)

        nav = QHBoxLayout()
        self.previous_btn = QPushButton("السابق" if self.language == "ar" else "Previous")
        self.next_btn = QPushButton("التالي" if self.language == "ar" else "Next")
        self.page_label = QLabel("")
        self.page_label.setAlignment(Qt.AlignmentFlag.AlignCenter)
        self.previous_btn.clicked.connect(self._previous_slide)
        self.next_btn.clicked.connect(self._next_slide)
        nav.addWidget(self.previous_btn)
        nav.addWidget(self.page_label, 1)
        nav.addWidget(self.next_btn)
        layout.addLayout(nav)
        self.browser = QTextBrowser(self)
        self.browser.setReadOnly(True)
        self.browser.setOpenLinks(False)
        self.browser.setOpenExternalLinks(False)
        self.browser.setTextInteractionFlags(Qt.TextInteractionFlag.TextSelectableByMouse | Qt.TextInteractionFlag.LinksAccessibleByMouse)
        self.browser.setContextMenuPolicy(Qt.ContextMenuPolicy.CustomContextMenu)
        self.browser.customContextMenuRequested.connect(self._show_selection_menu_at)
        self.browser.viewport().installEventFilter(self)
        layout.addWidget(self.browser, 1)

        # Respect the application theme for the reader chrome; document content
        # retains the fonts and colors encoded in the original Office document.
        theme = "dark"
        try:
            settings = getattr(parent, "settings", None)
            if settings is not None:
                theme = settings.value("ui_theme", "dark", type=str)
        except Exception:
            pass
        self.apply_theme(theme)
        ext = Path(path).suffix.lower()
        if ext == ".docx":
            self._slides = [_docx_document_to_html(path)]
        elif ext == ".pptx":
            self._slides = _pptx_slides_to_html(path)
            if not self._slides:
                raise ValueError("The PowerPoint file does not contain readable slides.")
        else:
            raise ValueError("Only modern Word (.docx) and PowerPoint (.pptx) files are supported.")
        self._show_slide(0)

    def apply_theme(self, theme=None):
        if theme is None:
            try:
                theme = self.parent().settings.value("ui_theme", "dark", type=str)
            except Exception:
                theme = "dark"
        tokens = engo_ui_theme_tokens(theme)
        self.setStyleSheet(f"""
            QDialog#officeNativeReader {{ background:{tokens['window']}; color:{tokens['text']}; }}
            QDialog#officeNativeReader QLabel {{ color:{tokens['text']}; }}
            QDialog#officeNativeReader QPushButton {{ background:{tokens['raised']}; color:{tokens['text']};
                border:1px solid {tokens['border']}; border-radius:6px; padding:6px 11px; }}
            QDialog#officeNativeReader QPushButton:hover {{ background:{tokens['hover']}; border-color:{tokens['border_strong']}; }}
            QDialog#officeNativeReader QPushButton:checked {{ background:{tokens['selection']}; border-color:{tokens['accent']}; }}
            QDialog#officeNativeReader QTextBrowser {{ background:{tokens['panel']}; color:{tokens['text']};
                border:1px solid {tokens['border']}; border-radius:7px; padding:8px; selection-background-color:{tokens['accent']}; selection-color:#ffffff; }}
        """)

    def apply_language(self, language=None):
        raw = str(language or self.language or "en").lower()
        self.language = "ar" if raw.startswith("ar") else "en"
        is_ar = self.language == "ar"
        self.setLayoutDirection(Qt.LayoutDirection.RightToLeft if is_ar else Qt.LayoutDirection.LeftToRight)
        self.select_tool_btn.setText("تحديد" if is_ar else "Select")
        self.highlight_tool_btn.setText("تظليل النص" if is_ar else "Highlight text")
        self.previous_btn.setText("السابق" if is_ar else "Previous")
        self.next_btn.setText("التالي" if is_ar else "Next")
        self.save_changes_btn.setText("حفظ التغييرات" if is_ar else "Save changes")
        self.discard_changes_btn.setText("تجاهل" if is_ar else "Discard")
        self._refresh_pending_highlight_controls()
        is_word = Path(self.path).suffix.lower() == ".docx"
        self.native_badge.setText(("Word أصلي" if is_word else "PowerPoint أصلي") if is_ar else
                                  ("NATIVE WORD" if is_word else "NATIVE POWERPOINT"))
        self.setWindowTitle(("قراءة " if is_ar else "Reading ") + Path(self.path).name)
        self._set_active_tool(self._active_tool)
        self._show_slide(self._slide_index)

    def _set_active_tool(self, tool: str):
        self._active_tool = "highlight" if str(tool) == "highlight" else "select"
        is_ar = self.language == "ar"
        self.tool_hint.setText(
            ("اسحب فوق النص لحفظ التظليل مباشرة في ملف Office الأصلي، دون تغيير الكلمات." if is_ar else
             "Drag over text to save the highlight directly in the original Office file without changing its words.")
            if self._active_tool == "highlight" else
            ("اسحب فوق النص ثم اختر نسخ أو تظليل أو سؤال Engo AI. ابدأ السحب من النص نفسه." if is_ar else
             "Drag over text, then choose Copy, Highlight, or Ask Engo AI. Start the drag on the text itself.")
        )

    def eventFilter(self, watched, event):
        if watched is self.browser.viewport():
            if event.type() == QEvent.Type.MouseButtonPress and event.button() == Qt.MouseButton.LeftButton:
                try:
                    cursor = self.browser.cursorForPosition(event.pos())
                    block_text = cursor.block().text()
                    position = cursor.positionInBlock()
                    candidate_index = position if 0 <= position < len(block_text) else position - 1
                    candidate = block_text[candidate_index] if 0 <= candidate_index < len(block_text) else ""
                    # U+FFFC is QTextDocument's inline-object marker (for example an image).
                    # A drag must begin on a real non-whitespace text character.
                    self._ignore_office_drag = not bool(candidate and not candidate.isspace() and candidate != "\ufffc")
                except Exception:
                    self._ignore_office_drag = True
                if self._ignore_office_drag:
                    return True
            elif event.type() == QEvent.Type.MouseButtonRelease and event.button() == Qt.MouseButton.LeftButton:
                if self._ignore_office_drag:
                    self._ignore_office_drag = False
                    return True
                pos = QPoint(event.pos())
                QTimer.singleShot(0, lambda p=pos: self._handle_text_selection_release(p))
        return super().eventFilter(watched, event)

    def _selected_text(self) -> str:
        return str(self.browser.textCursor().selectedText() or "").replace("\u2029", "\n").replace("\u2028", "\n").strip()

    def _handle_text_selection_release(self, local_pos: QPoint):
        selected = self._selected_text()
        if not selected:
            return
        if self._active_tool == "highlight":
            self._queue_native_highlight(selected)
        else:
            self._show_selection_menu(self.browser.viewport().mapToGlobal(local_pos), selected)

    def _show_selection_menu_at(self, local_pos: QPoint):
        selected = self._selected_text()
        if selected:
            self._show_selection_menu(self.browser.viewport().mapToGlobal(local_pos), selected)

    def _show_selection_menu(self, global_pos: QPoint, selected: str):
        is_ar = self.language == "ar"
        menu = QMenu(self)
        copy_action = menu.addAction(make_icon("copy", "#8ec8ff", 16), "نسخ النص" if is_ar else "Copy text")
        highlight_action = menu.addAction(make_icon("highlight", "#d7ae35", 16), "تظليل النص" if is_ar else "Highlight text")
        menu.addSeparator()
        ask_action = menu.addAction(make_icon("ai", "#9fbaff", 16), "اسأل Engo AI عن النص" if is_ar else "Ask Engo AI about this text")
        chosen = menu.exec(global_pos)
        if chosen is copy_action:
            QApplication.clipboard().setText(selected)
        elif chosen is highlight_action:
            self._queue_native_highlight(selected)
        elif chosen is ask_action:
            self.askAISelected.emit(selected, self.path)

    def _queue_native_highlight(self, selected: str):
        selected = str(selected or "").strip()
        if not selected:
            return
        if selected not in self._pending_highlights:
            self._pending_highlights.append(selected)
        self._refresh_pending_highlight_controls()
        is_ar = self.language == "ar"
        self.tool_hint.setText(
            (f"تمت إضافة {len(self._pending_highlights)} عبارة إلى التغييرات المعلقة. اضغط «حفظ التغييرات» لكتابتها في نفس ملف Office." if is_ar else
             f"{len(self._pending_highlights)} passage(s) queued. Press Save changes to write them into this same Office file.")
        )

    def _refresh_pending_highlight_controls(self):
        has_pending = bool(getattr(self, "_pending_highlights", []))
        if hasattr(self, "save_changes_btn"):
            self.save_changes_btn.setEnabled(has_pending)
        if hasattr(self, "discard_changes_btn"):
            self.discard_changes_btn.setEnabled(has_pending)

    def _discard_native_highlights(self):
        self._pending_highlights.clear()
        self._refresh_pending_highlight_controls()
        self._set_active_tool(self._active_tool)

    def _commit_native_highlights(self):
        if not self._pending_highlights:
            return True
        try:
            # OOXML formatting markup is written back into this very same DOCX/PPTX.
            # Text nodes and the source document's actual wording are not rewritten.
            count = _office_highlight_same_file(self.path, list(self._pending_highlights))
            self._pending_highlights.clear()
            self._refresh_pending_highlight_controls()
            is_ar = self.language == "ar"
            self.tool_hint.setText(
                (f"تم حفظ التظليل في نفس ملف Office دون تغيير النص · {count}" if is_ar else
                 f"Highlights saved into the same Office file; text unchanged · {count}")
            )
            self._slides = [_docx_document_to_html(self.path)] if Path(self.path).suffix.lower() == ".docx" else _pptx_slides_to_html(self.path)
            self._show_slide(self._slide_index)
            return True
        except Exception as exc:
            QMessageBox.warning(self, APP_NAME, ("تعذر حفظ التظليل في ملف Office الأصلي:\n" if self.language == "ar" else
                                                   "Could not save the highlight in the original Office file:\n") + str(exc))
            return False

    def closeEvent(self, event):
        if self._pending_highlights:
            is_ar = self.language == "ar"
            box = QMessageBox(self)
            box.setIcon(QMessageBox.Icon.Question)
            box.setWindowTitle("تغييرات غير محفوظة" if is_ar else "Unsaved changes")
            box.setText("لديك تظليلات لم تُحفظ في ملف Office. هل تريد حفظها في نفس الملف؟" if is_ar else
                        "You have unsaved highlights. Save them into the same Office file?")
            save_button = box.addButton("حفظ" if is_ar else "Save", QMessageBox.ButtonRole.AcceptRole)
            discard_button = box.addButton("تجاهل" if is_ar else "Discard", QMessageBox.ButtonRole.DestructiveRole)
            cancel_button = box.addButton("إلغاء" if is_ar else "Cancel", QMessageBox.ButtonRole.RejectRole)
            box.exec()
            clicked = box.clickedButton()
            if clicked is save_button:
                if not self._commit_native_highlights():
                    event.ignore()
                    return
            elif clicked is discard_button:
                self._pending_highlights.clear()
            else:
                event.ignore()
                return
        event.accept()

    def _show_slide(self, index: int):
        self._slide_index = max(0, min(int(index), len(self._slides) - 1))
        self.browser.setHtml(self._slides[self._slide_index])
        is_presentation = Path(self.path).suffix.lower() == ".pptx"
        self.previous_btn.setVisible(is_presentation)
        self.next_btn.setVisible(is_presentation)
        self.page_label.setText(
            (f"الشريحة {self._slide_index + 1} من {len(self._slides)}" if self.language == "ar" else f"Slide {self._slide_index + 1} of {len(self._slides)}")
            if is_presentation else ("مستند Word · تحديد وتظليل أصلي" if self.language == "ar" else "Word document · native selection and highlighting")
        )
        self.previous_btn.setEnabled(self._slide_index > 0)
        self.next_btn.setEnabled(self._slide_index < len(self._slides) - 1)

    def _previous_slide(self):
        self._show_slide(self._slide_index - 1)

    def _next_slide(self):
        self._show_slide(self._slide_index + 1)


def is_image_document(path: str) -> bool:
    return Path(str(path or "")).suffix.lower() in IMAGE_DOCUMENT_EXTENSIONS


def prepare_document_for_viewer(source_path: str) -> str:
    """Return a PDF path for the viewer; image inputs become a one-page cached PDF."""
    source_path = os.path.abspath(str(source_path or ""))
    if Path(source_path).suffix.lower() == ".pdf":
        return source_path
    if not is_image_document(source_path):
        raise ValueError("Unsupported file type. Open a PDF or a common image file.")
    if not os.path.isfile(source_path):
        raise FileNotFoundError(source_path)
    stat = os.stat(source_path)
    cache_key = hashlib.sha256(
        f"{os.path.normcase(source_path)}|{stat.st_size}|{stat.st_mtime_ns}".encode("utf-8", errors="replace")
    ).hexdigest()
    cache_dir = Path.home() / ".engopdfviewer" / "image_cache"
    cache_dir.mkdir(parents=True, exist_ok=True)
    cached_pdf = cache_dir / f"{cache_key}.pdf"
    if cached_pdf.is_file() and cached_pdf.stat().st_size > 100:
        return str(cached_pdf)
    with Image.open(source_path) as original:
        try:
            original.seek(0)  # Animated formats are represented by their first frame.
        except Exception:
            pass
        image = ImageOps.exif_transpose(original).convert("RGBA")
        # Flatten transparency onto white so transparent PNGs remain legible in PDF.
        background = Image.new("RGB", image.size, "white")
        background.paste(image, mask=image.getchannel("A"))
        image = background
        max_side = 14000
        if max(image.size) > max_side:
            ratio = max_side / float(max(image.size))
            resampling = getattr(Image, "Resampling", Image)
            image = image.resize((max(1, round(image.width * ratio)), max(1, round(image.height * ratio))), resampling.LANCZOS)
        stream = io.BytesIO()
        image.save(stream, format="JPEG", quality=94, optimize=True)
        image_bytes = stream.getvalue()
        width_pt = max(72.0, image.width * 0.75)
        height_pt = max(72.0, image.height * 0.75)
    doc = fitz.open()
    try:
        page = doc.new_page(width=width_pt, height=height_pt)
        page.insert_image(page.rect, stream=image_bytes, keep_proportion=False)
        temp = str(cached_pdf.with_suffix(".tmp.pdf"))
        doc.save(temp, garbage=4, deflate=True)
        os.replace(temp, cached_pdf)
    finally:
        doc.close()
    return str(cached_pdf)
