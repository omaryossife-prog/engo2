# Auto-split from main.py (verbatim move; do not reformat).
from __future__ import annotations

import math
import os
import json
import io
import re
import threading
from pathlib import Path
import pymupdf as fitz  # use the maintained import name; keep fitz alias for existing calls
from PIL import Image, ImageOps, ImageChops, ImageFilter
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

from engo_ai_core import (
    AIRequestWorker,
)
from engo_base import (
    engo_ui_theme_tokens,
)
from engo_widgets import (
    make_icon,
)




class PDFTextSearchWorker(QThread):
    resultsReady = pyqtSignal(object)
    progressText = pyqtSignal(str)
    failed = pyqtSignal(str)

    def __init__(self, path: str, query: str):
        super().__init__()
        self.path = str(path)
        self.query = str(query or "").strip()
        self._cancel_event = threading.Event()

    def cancel(self):
        self._cancel_event.set()

    def run(self):
        try:
            results = []
            with fitz.open(self.path) as doc:
                total = doc.page_count
                for page_index in range(total):
                    if self._cancel_event.is_set():
                        return
                    if page_index % 10 == 0:
                        self.progressText.emit(f"Searching page {page_index + 1} of {total}…")
                    page = doc.load_page(page_index)
                    for rect in page.search_for(self.query):
                        page_rect = page.rect
                        box = [
                            max(0.0, min(1.0, rect.x0 / max(page_rect.width, 1))),
                            max(0.0, min(1.0, rect.y0 / max(page_rect.height, 1))),
                            max(0.0, min(1.0, rect.width / max(page_rect.width, 1))),
                            max(0.0, min(1.0, rect.height / max(page_rect.height, 1))),
                        ]
                        excerpt = page.get_textbox(rect).strip() or self.query
                        results.append({"page": page_index + 1, "box": box, "excerpt": excerpt,
                                        "kind": "text", "source": "exact"})
            self.resultsReady.emit(results)
        except Exception as exc:
            self.failed.emit(str(exc))


class AISemanticSearchWorker(AIRequestWorker):
    """Search every PDF page in small multimodal batches for concepts, handwriting and figures."""
    resultsReady = pyqtSignal(object)
    progressText = pyqtSignal(str)
    searchFailed = pyqtSignal(str)

    def __init__(self, path, provider, model, api_key, query):
        super().__init__(path, provider, model, api_key, query, [], False, [], "search", 0)
        self.search_query = str(query or "").strip()
        # Full-page visual search needs more time than a normal text-only chat request.
        # A longer connect/read window is paired with smaller/adaptive image batches below.
        self.CONNECT_TIMEOUT_SECONDS = 45
        self.READ_TIMEOUT_SECONDS = 90

    @staticmethod
    def _parse_search_json(answer: str):
        text = str(answer or "").strip()
        text = re.sub(r"^```(?:json)?\s*|\s*```$", "", text, flags=re.I)
        start = text.find("{")
        end = text.rfind("}")
        if start >= 0 and end > start:
            payload = json.loads(text[start:end + 1])
        else:
            payload = json.loads(text)
        if isinstance(payload, list):
            return payload
        return payload.get("results", []) if isinstance(payload, dict) else []

    def run(self):
        try:
            doc = fitz.open(self.path)
            try:
                total = doc.page_count
                all_results = []
                batch_size = 2
                batch_count = max(1, math.ceil(total / batch_size))

                def inspect_batch(indices: list[int], retry_count: int = 0):
                    self._check_cancelled()
                    batch_label = (f"page {indices[0] + 1}" if len(indices) == 1 else
                                   f"pages {indices[0] + 1}–{indices[-1] + 1}")
                    self.progressText.emit(f"AI is examining {batch_label} of {total}…")
                    text_parts = []
                    images = []
                    for page_index in indices:
                        self._check_cancelled()
                        page = doc.load_page(page_index)
                        page_text = page.get_text("text").strip()
                        text_parts.append(f"PAGE {page_index + 1} SELECTABLE TEXT:\n{page_text[:7000] if page_text else '[No selectable text; inspect the page image for handwriting or visual content.]'}")
                        # Slightly smaller images reduce upload and provider processing time.
                        scale = min(1.0, 820.0 / max(float(page.rect.width), float(page.rect.height), 1.0))
                        pix = page.get_pixmap(matrix=fitz.Matrix(scale, scale), alpha=False)
                        img = Image.frombytes("RGB", (pix.width, pix.height), pix.samples)
                        img.thumbnail((820, 820), Image.Resampling.LANCZOS)
                        buff = io.BytesIO()
                        img.save(buff, format="JPEG", quality=68, optimize=True)
                        images.append({"label": f"Full page image · PDF page {page_index + 1}",
                                       "mime": "image/jpeg", "data": buff.getvalue()})
                    prompt = (
                        "You are the document-search engine inside Engo PDF Viewer & AI Study Agent. Search these supplied PDF pages for the user's target. "
                        "This is semantic/visual search, not literal string search: accept paraphrases, equivalent terms, handwriting, "
                        "equations, labels inside pictures, charts, diagrams, and scanned content. Inspect BOTH extracted text and page images. "
                        'Return JSON only as an object with this structure: {"results":[{"page":1,"excerpt":"short visible evidence",'
                        '"reason":"why it matches","kind":"text|solution|diagram|chart|image|table",'
                        '"box":[0.1,0.2,0.3,0.1],"occurrences_on_page":1}]}. ' 
                        "Page is 1-based within the original PDF. box is normalized [x,y,width,height] in 0..1 around the matched area, "
                        "not the entire page; set box to null only if location cannot be identified. One result per distinct location. "
                        "Do not invent matches. If a page does not contain the target, omit it. Return an empty results array if none match.\n\n"
                        f"USER'S SEARCH TARGET: {self.search_query}\n\n" + "\n\n".join(text_parts)
                    )
                    try:
                        answer = self._call_provider(prompt, images, stream=False)
                    except Exception as exc:
                        self._check_cancelled()
                        error_text = str(exc).casefold()
                        is_timeout = any(token in error_text for token in ("timed out", "timeout", "read timeout", "socket.timeout"))
                        if is_timeout and len(indices) > 1:
                            # A slow multi-page request is automatically split into one-page
                            # requests, so the user does not have to restart the whole search.
                            middle = max(1, len(indices) // 2)
                            self.progressText.emit(
                                f"The provider is taking too long for {batch_label}; retrying the pages separately…"
                            )
                            inspect_batch(indices[:middle], retry_count=0)
                            inspect_batch(indices[middle:], retry_count=0)
                            return
                        if is_timeout and retry_count < 2:
                            wait_seconds = retry_count + 1
                            self.progressText.emit(
                                f"Timeout on {batch_label}; retrying automatically ({retry_count + 1}/2)…"
                            )
                            if self._cancel_event.wait(wait_seconds):
                                self._check_cancelled()
                            inspect_batch(indices, retry_count=retry_count + 1)
                            return
                        raise
                    self._check_cancelled()
                    parsed = self._parse_search_json(answer)
                    allowed = {i + 1 for i in indices}
                    for item in parsed:
                        if not isinstance(item, dict):
                            continue
                        try:
                            page_number = int(item.get("page", 0))
                        except Exception:
                            continue
                        if page_number not in allowed:
                            continue
                        box = item.get("box")
                        clean_box = None
                        if isinstance(box, (list, tuple)) and len(box) == 4:
                            try:
                                values = [float(v) for v in box]
                                if all(math.isfinite(v) for v in values) and values[2] > 0 and values[3] > 0:
                                    x, y, w, h = values
                                    x = max(0.0, min(0.995, x)); y = max(0.0, min(0.995, y))
                                    w = max(0.005, min(1.0 - x, w)); h = max(0.005, min(1.0 - y, h))
                                    clean_box = [x, y, w, h]
                            except Exception:
                                clean_box = None
                        all_results.append({
                            "page": page_number, "box": clean_box,
                            "excerpt": str(item.get("excerpt") or self.search_query).strip()[:500],
                            "reason": str(item.get("reason") or "").strip()[:500],
                            "kind": str(item.get("kind") or "text").strip().lower(),
                            "source": "ai", "occurrences": max(1, int(item.get("occurrences_on_page", 1) or 1)),
                        })

                for batch_start in range(0, total, batch_size):
                    self._check_cancelled()
                    indices = list(range(batch_start, min(total, batch_start + batch_size)))
                    batch_number = batch_start // batch_size + 1
                    self.progressText.emit(f"Preparing AI search batch {batch_number}/{batch_count}…")
                    inspect_batch(indices)
                self.resultsReady.emit(all_results)
            finally:
                doc.close()
        except InterruptedError:
            self.searchFailed.emit("AI search was cancelled.")
        except Exception as exc:
            self.searchFailed.emit(str(exc))


class PDFSearchDialog(QDialog):
    searchRequested = pyqtSignal(str, str)
    resultActivated = pyqtSignal(object)
    closedByUser = pyqtSignal()

    def __init__(self, path: str, parent=None):
        super().__init__(parent)
        self.setObjectName("pdfSearchDialog")
        self.path = os.path.abspath(path)
        self._language = "en"
        self._theme = "dark"
        self._has_result_state = False
        self._last_results = []
        self._last_mode = "text"
        self.setWindowTitle(f"Search PDF · {Path(path).name}")
        self.setMinimumSize(580, 500)
        self.resize(720, 590)
        root = QVBoxLayout(self)
        title = QLabel("Search this entire PDF")
        title.setStyleSheet("font-size: 15pt; font-weight: 700;")
        root.addWidget(title)
        hint = QLabel("Exact text finds literal selectable words. AI search looks for meaning, handwriting, equations, diagrams, charts, and images.")
        hint.setWordWrap(True)
        root.addWidget(hint)
        row = QHBoxLayout()
        self.query_edit = QLineEdit()
        self.query_edit.setPlaceholderText("Enter a word, phrase, concept, formula, or describe a figure…")
        self.query_edit.returnPressed.connect(self._start_search)
        row.addWidget(self.query_edit, 1)
        self.mode_combo = QComboBox()
        self.mode_combo.addItem("Exact text", "text")
        self.mode_combo.addItem("AI semantic / visual", "ai")
        self.mode_combo.addItem("Tag", "tag")
        row.addWidget(self.mode_combo)
        self.tag_combo = QComboBox()
        self.tag_combo.setMinimumWidth(150)
        self.tag_combo.setToolTip("Choose a tag to list all regions assigned to it")
        self.tag_combo.currentIndexChanged.connect(self._tag_selection_changed)
        self.tag_combo.hide()
        row.addWidget(self.tag_combo)
        self.search_btn = QPushButton("Search")
        self.search_btn.setObjectName("primary")
        self.search_btn.clicked.connect(self._start_search)
        row.addWidget(self.search_btn)
        self.mode_combo.currentIndexChanged.connect(self._mode_changed)
        root.addLayout(row)
        self._refresh_tag_options()
        self.status = QLabel("Enter what you want to find.")
        self.status.setWordWrap(True)
        self._update_mode_controls()
        root.addWidget(self.status)
        self.results = QListWidget()
        self.results.setWordWrap(True)
        self.results.setSpacing(3)
        self.results.itemDoubleClicked.connect(self._activate_item)
        root.addWidget(self.results, 1)
        footer = QHBoxLayout()
        self.count_label = QLabel("")
        footer.addWidget(self.count_label, 1)
        self.hide_btn = QPushButton("Hide")
        self.hide_btn.setIcon(make_icon("sidebar", "#9aa6b8", 16))
        self.hide_btn.setToolTip("Hide this search window without clearing the selected PDF result")
        self.hide_btn.clicked.connect(self.hide)
        footer.addWidget(self.hide_btn)
        self.close_btn = QPushButton("Close search")
        self.close_btn.setIcon(make_icon("close", "#e58b8b", 16))
        self.close_btn.setToolTip("Close search and clear all highlighted search results")
        self.close_btn.clicked.connect(self.close)
        footer.addWidget(self.close_btn)
        self._closed_by_user = False
        root.addLayout(footer)
        self.apply_context_from_parent()

    def _parent_setting(self, key, default):
        try:
            parent = self.parent()
            settings = getattr(parent, "settings", None)
            if settings is not None:
                return settings.value(key, default, type=str)
        except Exception:
            pass
        return default

    def apply_context_from_parent(self):
        self.apply_theme(self._parent_setting("ui_theme", "dark"))
        self.apply_language(self._parent_setting("interface_language", "en"))

    def apply_theme(self, theme=None):
        tokens = engo_ui_theme_tokens(theme or self._parent_setting("ui_theme", "dark"))
        c = {
            "bg": tokens["window"], "panel": tokens["panel"], "field": tokens["input"],
            "text": tokens["text"], "muted": tokens["muted"], "border": tokens["border"],
            "soft": tokens["selection"], "soft_text": tokens["selection_text"],
            "hover": tokens["hover"], "accent": tokens["accent"], "scroll": tokens["scrollbar"],
        }
        pal = QPalette(self.palette())
        for role, key in ((QPalette.ColorRole.Window,"bg"), (QPalette.ColorRole.WindowText,"text"),
                          (QPalette.ColorRole.Base,"field"), (QPalette.ColorRole.AlternateBase,"panel"),
                          (QPalette.ColorRole.Text,"text"), (QPalette.ColorRole.Button,"panel"),
                          (QPalette.ColorRole.ButtonText,"text"), (QPalette.ColorRole.Highlight,"soft"),
                          (QPalette.ColorRole.HighlightedText,"soft_text")):
            pal.setColor(role, QColor(c[key]))
        self.setPalette(pal)
        self.setStyleSheet(f"""
            QDialog#pdfSearchDialog {{ background:{c['bg']}; color:{c['text']}; }}
            QDialog#pdfSearchDialog QWidget {{ color:{c['text']}; }}
            QDialog#pdfSearchDialog QLabel {{ color:{c['text']}; background:transparent; }}
            QDialog#pdfSearchDialog QLineEdit, QDialog#pdfSearchDialog QComboBox {{
                background:{c['field']}; color:{c['text']}; border:1px solid {c['border']};
                border-radius:7px; padding:7px 9px; selection-background-color:{c['accent']}; selection-color:#ffffff;
            }}
            QDialog#pdfSearchDialog QLineEdit:focus, QDialog#pdfSearchDialog QComboBox:focus {{ border-color:{c['accent']}; }}
            QDialog#pdfSearchDialog QComboBox QAbstractItemView {{ background:{c['field']}; color:{c['text']};
                border:1px solid {c['border']}; selection-background-color:{c['soft']}; selection-color:{c['soft_text']}; outline:0; }}
            QDialog#pdfSearchDialog QListWidget {{ background:{c['panel']}; color:{c['text']}; border:1px solid {c['border']};
                border-radius:8px; padding:5px; outline:0; }}
            QDialog#pdfSearchDialog QListWidget::item {{ padding:7px; border-radius:5px; }}
            QDialog#pdfSearchDialog QListWidget::item:selected {{ background:{c['soft']}; color:{c['soft_text']}; }}
            QDialog#pdfSearchDialog QListWidget::item:hover:!selected {{ background:{c['hover']}; }}
            QDialog#pdfSearchDialog QPushButton {{ background:{c['panel']}; color:{c['text']}; border:1px solid {c['border']};
                border-radius:7px; padding:7px 12px; }}
            QDialog#pdfSearchDialog QPushButton:hover {{ background:{c['hover']}; border-color:{c['accent']}; }}
            QDialog#pdfSearchDialog QPushButton#primary {{ background:{c['accent']}; color:#ffffff; border-color:{c['accent']}; font-weight:700; }}
            QDialog#pdfSearchDialog QPushButton#primary:hover {{ background:{c['hover']}; color:{c['text']}; }}
            QDialog#pdfSearchDialog QScrollBar:vertical {{ background:{c['bg']}; width:9px; margin:2px; }}
            QDialog#pdfSearchDialog QScrollBar::handle:vertical {{ background:{c['scroll']}; border-radius:4px; min-height:24px; }}
            QDialog#pdfSearchDialog QToolTip {{ background:{c['panel']}; color:{c['text']}; border:1px solid {c['border']}; padding:5px; }}
        """)

    def _tr(self, english):
        if self._language != "ar":
            return english
        return {
            "Search this entire PDF": "البحث في ملف PDF بالكامل",
            "Exact text finds literal selectable words. AI search looks for meaning, handwriting, equations, diagrams, charts, and images.": "البحث النصي يعثر على الكلمات القابلة للتحديد كما هي. أما بحث AI فيبحث عن المعنى والكتابة اليدوية والمعادلات والرسوم البيانية والصور.",
            "Enter a word, phrase, concept, formula, or describe a figure…": "اكتب كلمة أو عبارة أو مفهومًا أو معادلة، أو صف شكلًا تريد البحث عنه…",
            "Exact text": "بحث نصي مطابق", "AI semantic / visual": "بحث دلالي / بصري بالذكاء الاصطناعي",
            "Tag": "وسم", "Choose a tag…": "اختر وسمًا…", "Choose a tag to list all regions assigned to it": "اختر وسمًا لعرض كل المناطق المرتبطة به",
            "Search": "بحث", "Show tag results": "عرض نتائج الوسم", "Enter what you want to find.": "اكتب ما تريد العثور عليه.",
            "The program tag library is empty. Create a tag with the Tag tool first.": "مكتبة الوسوم فارغة. أنشئ وسمًا أولًا من أداة الوسوم.",
            "Choose a program tag to display its regions in this PDF.": "اختر وسمًا لعرض المناطق المرتبطة به في ملف PDF الحالي.",
            "Choose a tag first.": "اختر وسمًا أولًا.", "Finding all regions tagged": "جارٍ العثور على كل المناطق المصنفة بالوسم",
            "Hide": "إخفاء", "Close search": "إغلاق البحث", "Hide this search window without clearing the selected PDF result": "إخفاء نافذة البحث دون مسح النتيجة المحددة في ملف PDF",
            "Close search and clear all highlighted search results": "إغلاق البحث ومسح كل نتائج البحث المميزة",
            "Search closed. Open Search again to start a new search.": "تم إغلاق البحث. افتح نافذة البحث مجددًا لبدء بحث جديد.",
            "Type a word, phrase, or concept first.": "اكتب كلمة أو عبارة أو مفهومًا أولًا.", "Starting search…": "جارٍ بدء البحث…", "Searching…": "جارٍ البحث…",
            "Exact text search finished.": "انتهى البحث النصي المطابق.",
            "AI search finished. Visual positions are model-estimated; open a result to inspect it.": "انتهى بحث AI. مواضع النتائج المرئية تقديرية؛ افتح النتيجة لفحصها.",
            "No matches were found. Try AI search for paraphrases, handwriting, or images.": "لم يتم العثور على نتائج. جرّب بحث AI للعثور على إعادة الصياغة أو الكتابة اليدوية أو الصور.",
            "This tag has no assigned regions in the current PDF.": "لا توجد مناطق مرتبطة بهذا الوسم في ملف PDF الحالي.",
            "No matching regions were identified in this PDF.": "لم يتم العثور على مناطق مطابقة في ملف PDF هذا.",
            "Matching region": "منطقة مطابقة", "Page": "صفحة", "page(s)": "صفحة", "region(s)": "منطقة",
            "exact match(es)": "تطابق نصي", "estimated occurrence(s)": "ظهورًا تقديريًا", "tagged region(s)": "منطقة موسومة",
            "A PDF search is still running. You can hide this window and continue reading; results will appear when ready.": "لا يزال البحث في ملف PDF جاريًا. يمكنك إخفاء النافذة ومتابعة القراءة؛ ستظهر النتائج عند اكتمال البحث.",
            "A search is already running. Wait for it to finish or cancel it by closing Search.": "يوجد بحث قيد التنفيذ بالفعل. انتظر اكتماله أو ألغِه بإغلاق نافذة البحث.",
        }.get(english, english)

    def apply_language(self, language=None):
        value = str(language or self._parent_setting("interface_language", "en")).lower()
        self._language = "ar" if value.startswith("ar") else "en"
        ar = self._language == "ar"
        self.setLayoutDirection(Qt.LayoutDirection.RightToLeft if ar else Qt.LayoutDirection.LeftToRight)
        self.setWindowTitle(("بحث في PDF · " if ar else "Search PDF · ") + Path(self.path).name)
        self.findChild(QLabel).setText(self._tr("Search this entire PDF"))
        labels = self.findChildren(QLabel)
        if len(labels) > 1:
            labels[1].setText(self._tr("Exact text finds literal selectable words. AI search looks for meaning, handwriting, equations, diagrams, charts, and images."))
        self.query_edit.setPlaceholderText(self._tr("Enter a word, phrase, concept, formula, or describe a figure…"))
        for i, source in enumerate(("Exact text", "AI semantic / visual", "Tag")):
            if i < self.mode_combo.count(): self.mode_combo.setItemText(i, self._tr(source))
        if self.tag_combo.count(): self.tag_combo.setItemText(0, self._tr("Choose a tag…"))
        self.tag_combo.setToolTip(self._tr("Choose a tag to list all regions assigned to it"))
        self.hide_btn.setText(self._tr("Hide")); self.close_btn.setText(self._tr("Close search"))
        self.hide_btn.setToolTip(self._tr("Hide this search window without clearing the selected PDF result"))
        self.close_btn.setToolTip(self._tr("Close search and clear all highlighted search results"))
        self._update_mode_controls()
        if self._has_result_state:
            self.set_results(self._last_results, self._last_mode)

    def showEvent(self, event):
        self.apply_context_from_parent()
        self._closed_by_user = False
        self._refresh_tag_options()
        self._update_mode_controls()
        super().showEvent(event)

    def _refresh_tag_options(self):
        """Refresh this PDF's tags, including names recovered from its live annotations."""
        parent = self.parent()
        try:
            tags = parent.document_tags(self.path) if parent is not None else []
        except Exception:
            tags = []
        current = self.tag_combo.currentData() if hasattr(self, "tag_combo") else None
        self.tag_combo.blockSignals(True)
        self.tag_combo.clear()
        self.tag_combo.addItem(self._tr("Choose a tag…"), "")
        for name in tags:
            self.tag_combo.addItem(str(name), str(name))
            try:
                color = parent._tag_color(parent._open_document_tab_by_path(self.path), str(name))
                if QColor(color).isValid():
                    self.tag_combo.setItemData(self.tag_combo.count() - 1, QColor(color), Qt.ItemDataRole.ForegroundRole)
                    self.tag_combo.setItemIcon(self.tag_combo.count() - 1, make_icon("tag", color, 15))
            except Exception:
                pass
        if current:
            index = self.tag_combo.findData(current)
            if index >= 0:
                self.tag_combo.setCurrentIndex(index)
        self.tag_combo.blockSignals(False)

    def _update_mode_controls(self, *_):
        is_tag_mode = str(self.mode_combo.currentData() or "text") == "tag"
        self.query_edit.setVisible(not is_tag_mode)
        self.tag_combo.setVisible(is_tag_mode)
        self.search_btn.setText(self._tr("Show tag results") if is_tag_mode else self._tr("Search"))
        if is_tag_mode:
            if self.tag_combo.count() <= 1:
                self.status.setText(self._tr("The program tag library is empty. Create a tag with the Tag tool first."))
            else:
                self.status.setText(self._tr("Choose a program tag to display its regions in this PDF."))
        else:
            self.status.setText(self._tr("Enter what you want to find."))

    def _mode_changed(self, *_):
        self._refresh_tag_options()
        self._update_mode_controls()
        if str(self.mode_combo.currentData() or "") == "tag" and self.tag_combo.currentData():
            self._start_tag_search()

    def _tag_selection_changed(self, *_):
        if str(self.mode_combo.currentData() or "") == "tag" and self.tag_combo.currentData():
            self._start_tag_search()

    def _start_tag_search(self):
        tag_name = str(self.tag_combo.currentData() or "").strip()
        if not tag_name:
            self.status.setText(self._tr("Choose a tag first."))
            return
        self.results.clear()
        self.count_label.clear()
        self.status.setText(("جارٍ العثور على كل المناطق المرتبطة بالوسم '" if self._language == "ar" else "Finding all regions tagged '") + tag_name + "'…")
        self.search_btn.setEnabled(False)
        self.searchRequested.emit(tag_name, "tag")

    def closeEvent(self, event):
        self._closed_by_user = True
        self.closedByUser.emit()
        super().closeEvent(event)

    def clear_search_state(self):
        self._has_result_state = False
        self._last_results = []
        self.results.clear()
        self.query_edit.clear()
        self.count_label.clear()
        self.status.setText(self._tr("Search closed. Open Search again to start a new search."))
        self.search_btn.setEnabled(True)
        self.query_edit.setEnabled(True)
        self.tag_combo.setEnabled(True)
        self.mode_combo.setEnabled(True)

    def _start_search(self):
        mode = str(self.mode_combo.currentData() or "text")
        if mode == "tag":
            self._start_tag_search()
            return
        query = self.query_edit.text().strip()
        if not query:
            self.status.setText(self._tr("Type a word, phrase, or concept first."))
            self.query_edit.setFocus()
            return
        self.results.clear()
        self.count_label.setText("")
        self.status.setText(self._tr("Starting search…"))
        self.search_btn.setEnabled(False)
        self.searchRequested.emit(query, mode)

    def set_busy(self, busy: bool):
        self.search_btn.setEnabled(not busy)
        self.query_edit.setEnabled(not busy)
        self.tag_combo.setEnabled(not busy)
        self.mode_combo.setEnabled(not busy)

    def set_progress(self, message: str):
        value = str(message or "Searching…")
        if self._language == "ar":
            replacements = (("Searching page ", "جارٍ البحث في الصفحة "), (" of ", " من "),
                            ("AI is examining pages ", "يفحص AI الصفحات "), ("AI is examining page ", "يفحص AI الصفحة "),
                            ("The provider is taking too long for ", "استغرق مزود الخدمة وقتًا طويلًا في "),
                            ("; retrying the pages separately…", "؛ ستتم إعادة تجربة الصفحات كلٌّ على حدة…"),
                            ("Timeout on ", "انتهت مهلة الاتصال في "), ("; retrying automatically (", "؛ إعادة المحاولة تلقائيًا ("),
                            ("A PDF search is still running. You can hide this window and continue reading; results will appear when ready.", self._tr("A PDF search is still running. You can hide this window and continue reading; results will appear when ready.")))
            for old, new in replacements: value = value.replace(old, new)
        self.status.setText(value)

    def set_results(self, results: list[dict], mode: str):
        self._has_result_state = True
        self._last_results = list(results or [])
        self._last_mode = str(mode or "text")
        self.results.clear()
        occurrence_count = sum(int(item.get("occurrences", 1) or 1) for item in results)
        pages = sorted({int(item.get("page", 1)) for item in results})
        for index, result in enumerate(results):
            page = int(result.get("page", 1))
            excerpt = str(result.get("excerpt") or "Matching region")
            reason = str(result.get("reason") or "")
            label = (f"صفحة {page}  ·  {excerpt[:155]}" if self._language == "ar" else f"Page {page}  ·  {excerpt[:155]}")
            if reason:
                label += f"\n{reason[:180]}"
            tag_color = str(result.get("tag_color") or "")
            item = (QListWidgetItem(make_icon("tag", tag_color, 16), label)
                    if mode == "tag" and QColor(tag_color).isValid() else QListWidgetItem(label))
            item.setData(Qt.ItemDataRole.UserRole, result)
            item.setToolTip(reason or excerpt)
            self.results.addItem(item)
        if mode == "ai":
            self.status.setText(self._tr("AI search finished. Visual positions are model-estimated; open a result to inspect it."))
            self.count_label.setText((f"{occurrence_count} ظهورًا تقديريًا · {len(pages)} صفحة · {len(results)} منطقة" if self._language == "ar" else f"{occurrence_count} estimated occurrence(s) · {len(pages)} page(s) · {len(results)} region(s)"))
        elif mode == "tag":
            tag_name = str(results[0].get("tag") or "") if results else str(self.tag_combo.currentData() or "")
            self.status.setText((f"كل المناطق المرتبطة بالوسم '{tag_name}' معروضة أدناه. انقر مرتين على نتيجة للانتقال إليها." if self._language == "ar" else f"All regions tagged '{tag_name}' are listed below. Double-click a result to jump to it."))
            self.count_label.setText((f"{len(results)} منطقة موسومة · {len(pages)} صفحة" if self._language == "ar" else f"{len(results)} tagged region(s) · {len(pages)} page(s)"))
        else:
            self.status.setText(self._tr("Exact text search finished."))
            self.count_label.setText((f"{len(results)} تطابق نصي · {len(pages)} صفحة" if self._language == "ar" else f"{len(results)} exact match(es) · {len(pages)} page(s)"))
        if not results:
            if mode == "text":
                self.status.setText(self._tr("No matches were found. Try AI search for paraphrases, handwriting, or images."))
            elif mode == "tag":
                self.status.setText(self._tr("This tag has no assigned regions in the current PDF."))
            else:
                self.status.setText(self._tr("No matching regions were identified in this PDF."))

    def _activate_item(self, item):
        payload = item.data(Qt.ItemDataRole.UserRole)
        if isinstance(payload, dict):
            self.resultActivated.emit(payload)
