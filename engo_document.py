# Auto-split from main.py (verbatim move; do not reformat).
from __future__ import annotations

import math
import os
import tempfile
import io
import re
import time
import zlib
from collections import OrderedDict, deque
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

from engo_base import (
    APP_NAME,
    DEFAULT_ANNOTATION_COLORS,
    DEFAULT_BG,
    DEFAULT_INK,
    _engo_translate_tooltip,
    engo_ui_theme_tokens,
    normalize_ui_theme,
)
from engo_widgets import (
    AnnotationColorEditDialog,
    ResponsiveSidebarTabs,
    TextAnnotationEditorDialog,
    _SmartPageThemeSignals,
    _SmartPageThemeTask,
    _ellipse_resize_preview_rect,
    _engo_file_dialog,
    _recognize_pen_shape,
    apply_page_theme_to_image,
    color_tuple,
    image_to_qimage,
    make_icon,
)


# In-app clipboard for native PDF annotations (copy / paste between open PDFs).
_ANNOTATION_CLIPBOARD = None


class DocumentCanvas(QWidget):
    """Efficient, single-canvas PDF viewer. Each PDF page is rendered as one complete page."""
    def __init__(self, tab: "DocumentTab"):
        super().__init__()
        self.tab = tab
        # Secondary linked canvases render into a separate scroll area while still
        # using the original DocumentTab as their PDF/annotation data model.
        self.display_scroll = None
        self._pan_active = False
        self._pan_scroll_area = None
        self._pan_start_global = QPoint()
        self._pan_start_h = 0
        self._pan_start_v = 0
        # Smooth zoom is painted by the real PDF canvas itself.  No grabbed
        # viewport snapshot or floating preview image is placed above the page.
        self._zoom_visual_scale = 1.0
        self._zoom_visual_anchor = QPointF(0.0, 0.0)
        self.external_zoom_callback = None
        # Linked secondary canvases use an external scroll area and need their
        # owner to update the visible page when Scroll mode is disabled.
        self.external_page_turn_callback = None
        self.read_only = False
        self.setMouseTracking(True)
        self.setCursor(Qt.CursorShape.ArrowCursor)
        self.setAttribute(Qt.WidgetAttribute.WA_OpaquePaintEvent, True)
        self.grabGesture(Qt.GestureType.PinchGesture)
        self.page_rects: dict[int, QRectF] = {}
        self.page_scales: dict[int, float] = {}
        self.cache: OrderedDict[tuple, QPixmap] = OrderedDict()
        self.cache_limit = 10
        # Smart Theme used to run synchronously inside paintEvent, which stalled
        # scrolling and page navigation. Render a legacy-speed dark preview first,
        # then replace it with the exact Smart Theme result from one low-priority
        # worker. A small queue prevents rapid scrolling from building huge jobs.
        self._smart_theme_pool = QThreadPool(self)
        self._smart_theme_pool.setMaxThreadCount(1)
        try:
            self._smart_theme_pool.setThreadPriority(QThread.Priority.LowPriority)
        except (AttributeError, TypeError):
            pass
        self._smart_theme_pending = set()
        self._smart_theme_done = set()
        self._smart_theme_signals = {}
        self._smart_theme_max_pending = 3
        # The old implementation keyed worker jobs by (page, width, height).
        # Every zoom/resize therefore created a new Smart Theme job and showed
        # the non-smart preview again. These master caches are keyed by page
        # content revision + theme colors, never by the current screen size.
        self._smart_theme_final_cache = OrderedDict()
        self._smart_theme_preview_cache = OrderedDict()
        self._smart_theme_master_limit = 10
        self._smart_theme_master_bytes_limit = 128 * 1024 * 1024
        self._view_w = 900
        self._view_h = 760
        self._drawing = False
        self._draw_page = -1
        self._draw_start = QPointF()
        self._draw_current = QPointF()
        self._draw_points: list[QPointF] = []
        # Native text selection is anchored to the word under the initial press.
        # It is never activated midway through a drag that began on blank/image space.
        self._text_selecting = False
        self._text_selection_page = -1
        self._text_selection_tool = ""
        self._text_selection_words = []
        self._text_selection_start_word = -1
        self._text_selection_end_word = -1
        self._text_selection_display_rects = []
        self._text_selection_text = ""
        self._pdf_word_cache = {}
        self._pdf_word_box_cache = {}
        self._dragging_annotation = False
        self._drag_page = -1
        self._drag_xref = 0
        self._drag_kind = "move"
        self._drag_handle = ""
        self._drag_start = QPointF()
        self._drag_original_rect = QRectF()
        self._drag_preview_rect = QRectF()
        self._drag_moved = False
        self._drag_rotation_center = QPointF()
        self._drag_rotation_start_angle = 0.0
        self._drag_rotation_delta = 0.0
        self._drag_rotation_step = 1.0
        self._drag_aspect_ratio = 0.0
        self._drag_control_start = QPointF()
        self._drag_control_anchor = QPointF()
        self._drag_control_mode = ""
        self._drag_control_meta = {}
        self._drag_control_preview_pos = QPointF()
        self._drag_control_geometry = None
        self._drag_target_page = -1
        self._drag_target_display_rect = QRectF()
        self._drag_pointer_offset = QPointF()
        self._drag_group_items = []
        self._drag_group_delta = QPointF()
        self._annotation_edit_mode = False
        self._marquee_active = False
        self._marquee_start = QPointF()
        self._marquee_current = QPointF()
        self._marquee_additive = False
        self._marquee_page = -1
        self._marquee_previous = []
        self._marquee_restore_selection = []
        self.ai_focus = None  # (page_index, normalized box [x,y,w,h], label, semantic kind)
        # Match the known-good 15.28.25 behavior: focus is visible unless the learner turns it off.
        self.ai_focus_visible = True
        self.search_highlights: dict[int, list[list[float]]] = {}
        # The laser is anchored to the current explained region. It moves only when
        # the tutor supplies a new focus_page_region tool call, never on a timer.
        self._laser_phase = 0.0
        self._laser_timer = QTimer(self)  # retained for compatibility; intentionally never started
        # Defer mouse context menus by the platform double-click interval so a
        # right-button double-click can be recognized as the Pen/Select toggle.
        # Keyboard context-menu requests remain immediate.
        self._pending_context_menu = None
        self._context_menu_timer = QTimer(self)
        self._context_menu_timer.setSingleShot(True)
        self._context_menu_timer.timeout.connect(self._show_pending_context_menu)
        self._suppress_context_menu = False
        self._suppress_context_menu_timer = QTimer(self)
        self._suppress_context_menu_timer.setSingleShot(True)
        self._suppress_context_menu_timer.timeout.connect(self._clear_context_menu_suppression)

    def set_zoom_visual_transform(self, scale: float, anchor: QPointF):
        self._zoom_visual_anchor = QPointF(anchor)
        self.set_zoom_visual_scale(scale)

    def set_zoom_visual_scale(self, scale: float):
        self._zoom_visual_scale = max(0.12, min(6.0, float(scale)))
        self.update()

    def clear_zoom_visual_transform(self):
        self._zoom_visual_scale = 1.0
        self._zoom_visual_anchor = QPointF(0.0, 0.0)
        self.update()

    def _map_from_zoom_visual(self, point: QPointF) -> QPointF:
        """Convert a pointer position back to the unscaled document coordinates."""
        scale = float(getattr(self, "_zoom_visual_scale", 1.0))
        if abs(scale - 1.0) < 0.001:
            return QPointF(point)
        anchor = self._zoom_visual_anchor
        return QPointF(anchor.x() + (point.x() - anchor.x()) / scale,
                       anchor.y() + (point.y() - anchor.y()) / scale)

    def clear_cache(self, clear_smart: bool = False):
        """Clear size-specific page rasters without discarding stable Smart Theme results."""
        self.cache.clear()
        if clear_smart:
            self._smart_theme_done.clear()
            self._smart_theme_final_cache.clear()
            self._smart_theme_preview_cache.clear()
        self.update()

    def set_ai_focus(self, page_index: int, normalized_box=None, label: str = "", kind: str = "text"):
        box = None
        if isinstance(normalized_box, (list, tuple)) and len(normalized_box) == 4:
            try:
                box = [max(0.0, min(1.0, float(v))) for v in normalized_box]
                if box[2] <= 0 or box[3] <= 0:
                    box = None
            except Exception:
                box = None
        safe_kind = str(kind or "text").strip().lower()
        self.ai_focus = (int(page_index), box, str(label or "Engo is explaining this area"), safe_kind) if box else None
        if box:
            # A newly registered target should never inherit an uninitialized hidden state.
            # The live lesson checkbox is applied immediately afterward and remains the user's
            # explicit on/off control.
            self.ai_focus_visible = True
        self._laser_timer.stop()
        self.update()

    def set_ai_focus_visible(self, visible: bool):
        self.ai_focus_visible = bool(visible)
        self._laser_timer.stop()
        self.update()

    def _advance_ai_laser(self):
        # Kept as a no-op for compatibility with older calls. Focus changes only
        # when Gemini explicitly identifies the next item being explained.
        self._laser_timer.stop()
        self.update()

    def clear_ai_focus(self):
        self.ai_focus = None
        self._laser_timer.stop()
        self.update()

    def invalidate_page(self, index: int | None = None):
        """Invalidate raster/theme data only for changed page content."""
        if index is None:
            self.cache.clear()
            self._smart_theme_done.clear()
            self._smart_theme_final_cache.clear()
            self._smart_theme_preview_cache.clear()
            self.__dict__.setdefault("_smart_stale", {}).clear()
            self.__dict__.setdefault("_smart_raw_bands", {}).clear()
        else:
            page_index = int(index)
            # Remember the page's current Smart Theme result and its band map so
            # the edited page can keep its smart colors while the new pass runs.
            try:
                stale_store = self.__dict__.setdefault("_smart_stale", {})
                raw_bands = self.__dict__.setdefault("_smart_raw_bands", {})
                finals = [k for k in self._smart_theme_final_cache.keys()
                          if k and int(k[0]) == page_index]
                if finals:
                    old_identity = finals[-1]
                    entry = raw_bands.get(old_identity)
                    old_pixmap = self._smart_theme_final_cache.get(old_identity)
                    if entry is not None and old_pixmap is not None and not old_pixmap.isNull():
                        stale_store[page_index] = (entry[0], entry[1], entry[2], old_pixmap,
                                                   str(old_identity[2]), str(old_identity[3]))
                for k in [k for k in raw_bands.keys() if k and int(k[0]) == page_index]:
                    raw_bands.pop(k, None)
            except Exception:
                pass
            for key in list(self.cache.keys()):
                if key and int(key[0]) == page_index:
                    self.cache.pop(key, None)
            for store in (self._smart_theme_final_cache, self._smart_theme_preview_cache):
                for key in list(store.keys()):
                    if key and int(key[0]) == page_index:
                        store.pop(key, None)
            for key in list(self._smart_theme_done):
                if key and int(key[0]) == page_index:
                    self._smart_theme_done.discard(key)
        self.update()

    def _document_is_available(self) -> bool:
        """Check document lifetime without truth-testing a PyMuPDF Document.

        bool(Document) calls Document.__len__ (page_count), which raises
        ValueError after close. Always inspect the explicit is_closed flag.
        """
        if getattr(self.tab, "_document_closing", False):
            return False
        doc = getattr(self.tab, "doc", None)
        if doc is None:
            return False
        try:
            return not bool(getattr(doc, "is_closed", False))
        except RuntimeError:
            return False

    def set_viewport_size(self, width: int, height: int):
        self._view_w, self._view_h = max(width, 300), max(height, 300)
        if self._document_is_available():
            self.relayout()
        else:
            self.page_rects.clear()
            self.page_scales.clear()
            self.setMinimumSize(self._view_w, self._view_h)
            self.resize(self._view_w, self._view_h)
            self.update()

    def _target_display_page_width(self, available_width: float,
                                   available_height: float | None = None,
                                   *, book_mode: bool = False) -> float:
        """Return one common on-screen page width for the entire document.

        A4 portrait, A4 landscape, and individually rotated pages must have the
        same displayed width. Their heights remain proportional to their own
        page aspect ratios. Custom zoom is a multiplier of the selected Fit
        baseline, not a raw PDF-point-to-pixel scale shared by all page sizes.
        """
        slot_width = max(100.0, float(available_width) / (2.0 if book_mode else 1.0))
        fit_mode = (getattr(self.tab, "custom_base_fit_mode", "width")
                    if self.tab.fit_mode == "custom" else self.tab.fit_mode)
        base_width = slot_width
        if fit_mode == "page" and available_height and self.tab.page_sizes:
            # Choose a common width small enough that even the tallest page
            # fits vertically. This keeps all page widths identical in Fit Page.
            height_limited_widths = [
                max(1.0, float(available_height)) * max(float(w), 1.0) / max(float(h), 1.0)
                for w, h in self.tab.page_sizes
            ]
            if height_limited_widths:
                base_width = min(base_width, min(height_limited_widths))
        multiplier = float(self.tab.custom_scale) if self.tab.fit_mode == "custom" else 1.0
        return max(80.0, min(12000.0, base_width * multiplier))

    def _scale_width(self, page_index: int, avail_w: float, avail_h: float | None = None) -> float:
        w, _h = self.tab.page_sizes[page_index]
        target_width = self._target_display_page_width(avail_w, avail_h, book_mode=False)
        return min(12.0, max(0.05, target_width / max(float(w), 1.0)))

    def relayout(self):
        # A deferred resize/layout callback can run after close_tab() has closed
        # the PDF. Never evaluate bool(doc): PyMuPDF implements that via
        # page_count and raises ValueError("document closed").
        if not self._document_is_available() or not getattr(self.tab, "page_sizes", None):
            self.page_rects.clear()
            self.page_scales.clear()
            self.cache.clear()
            self._smart_theme_done.clear()
            self.setMinimumSize(self._view_w, self._view_h)
            self.resize(self._view_w, self._view_h)
            self.update()
            return

        margin = 30
        gap_y = 24
        gap_x = 20
        self.page_rects = {}
        self.page_scales = {}
        count = len(self.tab.page_sizes)
        book_mode = bool(getattr(self.tab, "book_mode", False))
        scroll_mode = bool(getattr(self.tab, "scroll_mode", True))

        if book_mode:
            # Book controls whether pages form a left/right spread. Scroll controls
            # whether all spreads are stacked vertically or only the current spread
            # is present (page-at-a-time).
            first_spread = (int(self.tab.current_page) // 2) * 2
            first_indices = range(0, count, 2) if scroll_mode else [first_spread]
            rows = []
            max_content_width = 0
            y = margin
            available_pair_w = max(260, self._view_w - 2 * margin - gap_x)
            available_h = max(250, self._view_h - 2 * margin)
            target_page_w = self._target_display_page_width(
                available_pair_w, available_h, book_mode=True)
            for first in first_indices:
                indices = [first] if first + 1 >= count else [first, first + 1]
                widths = [float(self.tab.page_sizes[k][0]) for k in indices]
                heights = [float(self.tab.page_sizes[k][1]) for k in indices]
                scaled_widths = [max(1, round(target_page_w)) for _w in widths]
                scaled_heights = [max(1, round(target_page_w * h / max(w, 1.0)))
                                  for w, h in zip(widths, heights)]
                page_scales = [min(12.0, max(0.05, target_page_w / max(w, 1.0)))
                               for w in widths]
                row_w = sum(scaled_widths) + (gap_x if len(indices) == 2 else 0)
                row_h = max(scaled_heights)
                max_content_width = max(max_content_width, row_w)
                rows.append((indices, scaled_widths, scaled_heights, page_scales,
                             row_w, row_h, y))
                y += row_h + gap_y

            canvas_w = max(self._view_w, max_content_width + margin * 2)
            if scroll_mode:
                canvas_h = max(self._view_h, y - gap_y + margin)
            else:
                row_h = rows[0][5] if rows else 0
                canvas_h = max(self._view_h, row_h + margin * 2)
                rows = [(*rows[0][:6], max(margin, (canvas_h - row_h) / 2))] if rows else []

            for indices, sws, shs, page_scales, row_w, row_h, row_y in rows:
                x = (canvas_w - row_w) / 2
                for pos, index in enumerate(indices):
                    pw, ph = sws[pos], shs[pos]
                    py = row_y + (row_h - ph) / 2
                    self.page_rects[index] = QRectF(x, py, pw, ph)
                    self.page_scales[index] = page_scales[pos]
                    x += pw + gap_x
        else:
            # Without Book, each spread is a single page. With Scroll disabled,
            # only the currently selected page is laid out and wheel input turns it.
            visible_indices = range(count) if scroll_mode else [int(self.tab.current_page)]
            computed = []
            max_page_w = 0
            y = margin
            avail_w = max(260, self._view_w - 2 * margin)
            avail_h = max(260, self._view_h - 2 * margin)
            target_page_w = self._target_display_page_width(avail_w, avail_h, book_mode=False)
            for i in visible_indices:
                pw_pt, ph_pt = self.tab.page_sizes[i]
                scale = min(12.0, max(0.05, target_page_w / max(float(pw_pt), 1.0)))
                pw = max(1, round(target_page_w))
                ph = max(1, round(target_page_w * float(ph_pt) / max(float(pw_pt), 1.0)))
                computed.append((i, pw, ph, y, scale))
                max_page_w = max(max_page_w, pw)
                y += ph + gap_y
            canvas_w = max(self._view_w, max_page_w + margin * 2)
            if scroll_mode:
                canvas_h = max(self._view_h, y - gap_y + margin)
            else:
                page_h = computed[0][2] if computed else 0
                canvas_h = max(self._view_h, page_h + margin * 2)
                y = max(margin, (canvas_h - page_h) / 2)
                if computed:
                    i, pw, ph, _old_y, scale = computed[0]
                    computed[0] = (i, pw, ph, y, scale)
            for i, pw, ph, py, scale in computed:
                self.page_rects[i] = QRectF((canvas_w - pw) / 2, py, pw, ph)
                self.page_scales[i] = scale

        self.setMinimumSize(round(canvas_w), round(canvas_h))
        self.resize(round(canvas_w), round(canvas_h))
        self.update()

    def _page_render_revision(self, index: int) -> int:
        versions = getattr(self.tab, "page_render_versions", None)
        try:
            return int(versions[int(index)])
        except (TypeError, ValueError, IndexError, KeyError):
            return int(getattr(self.tab, "render_version", 0))

    def _smart_theme_identity(self, index: int):
        """Stable identity for one page's recolored pixels, independent of zoom."""
        return (int(index), self._page_render_revision(index),
                str(self.tab.bg_color), str(self.tab.ink_color))

    def _smart_master_cache_bytes(self) -> int:
        total = 0
        for store in (self._smart_theme_final_cache, self._smart_theme_preview_cache):
            for pixmap in store.values():
                if pixmap is not None and not pixmap.isNull():
                    total += int(pixmap.width()) * int(pixmap.height()) * 4
        return total

    def _remember_smart_master(self, store, identity, pixmap):
        if pixmap is None or pixmap.isNull():
            return
        store[identity] = pixmap
        store.move_to_end(identity)
        # The combined page-master LRU is capped by both page count and memory.
        # Evict previews first; final Smart Theme results are more valuable.
        while (len(self._smart_theme_final_cache) + len(self._smart_theme_preview_cache) > 1
               and (len(self._smart_theme_final_cache) + len(self._smart_theme_preview_cache)
                    > self._smart_theme_master_limit
                    or self._smart_master_cache_bytes() > self._smart_theme_master_bytes_limit)):
            victim_store = (self._smart_theme_preview_cache
                            if self._smart_theme_preview_cache
                            else self._smart_theme_final_cache)
            if not victim_store:
                break
            evicted_identity, _evicted_pixmap = victim_store.popitem(last=False)
            if (evicted_identity not in self._smart_theme_final_cache
                    and evicted_identity not in self._smart_theme_preview_cache):
                self._smart_theme_done.discard(evicted_identity)

    @staticmethod
    def _fit_smart_master(pixmap: QPixmap, width: int, height: int) -> QPixmap:
        if pixmap.isNull():
            return QPixmap()
        if pixmap.width() == width and pixmap.height() == height:
            return pixmap
        # This happens only after the viewport settles, not on every animation
        # frame. Keep the result sharp while avoiding another Smart Theme pass.
        return pixmap.scaled(
            max(1, int(width)), max(1, int(height)),
            Qt.AspectRatioMode.IgnoreAspectRatio,
            Qt.TransformationMode.SmoothTransformation,
        )

    def _cache_rendered_page(self, cache_key, pixmap: QPixmap):
        self.cache[cache_key] = pixmap
        self.cache.move_to_end(cache_key)
        while len(self.cache) > self.cache_limit:
            self.cache.popitem(last=False)

    _SMART_BAND_ROWS = 16

    @classmethod
    def _smart_band_hashes(cls, image_bytes, width: int, height: int):
        """CRC of every horizontal band of a rendered RGB page (cheap change map)."""
        try:
            stride = int(width) * 3
            band = stride * cls._SMART_BAND_ROWS
            view = memoryview(image_bytes)
            total = min(len(view), stride * int(height))
            return [zlib.crc32(view[i:i + band]) for i in range(0, total, band)]
        except Exception:
            return None

    def _queue_smart_theme_image(self, identity, image_bytes: bytes,
                                 width: int, height: int):
        if (identity in self._smart_theme_pending
                or identity in self._smart_theme_done
                or len(self._smart_theme_pending) >= self._smart_theme_max_pending):
            return False
        try:
            bands = self._smart_band_hashes(image_bytes, width, height)
            if bands is not None:
                self.__dict__.setdefault("_smart_raw_bands", {})[identity] = (int(width), int(height), bands)
        except Exception:
            pass
        signals = _SmartPageThemeSignals(self)
        signals.finished.connect(self._on_smart_theme_image_ready)
        self._smart_theme_signals[identity] = signals
        self._smart_theme_pending.add(identity)
        task = _SmartPageThemeTask(
            identity, image_bytes, width, height,
            self.tab.bg_color, self.tab.ink_color, signals
        )
        try:
            self._smart_theme_pool.start(task, -1)
            return True
        except Exception:
            self._smart_theme_pending.discard(identity)
            self._smart_theme_signals.pop(identity, None)
            try:
                signals.deleteLater()
            except Exception:
                pass
            return False

    def _schedule_cached_smart_theme_page(self, index: int, scale: float, identity):
        """Retry a deferred page once a worker slot becomes available."""
        if (identity in self._smart_theme_pending or identity in self._smart_theme_done
                or identity not in self._smart_theme_preview_cache
                or len(self._smart_theme_pending) >= self._smart_theme_max_pending):
            return
        if not self._document_is_available() or identity != self._smart_theme_identity(index):
            return
        try:
            page = self.tab.doc.load_page(index)
            pix = page.get_pixmap(matrix=fitz.Matrix(scale, scale), alpha=False, annots=True)
            self._queue_smart_theme_image(
                identity, bytes(pix.samples), int(pix.width), int(pix.height)
            )
        except Exception:
            # Leave the fast preview cached. A later explicit content/theme change
            # can try again; never spin a retry loop in paintEvent.
            self._smart_theme_done.add(identity)

    def _on_smart_theme_image_ready(self, identity, image_bytes, width: int, height: int):
        self._smart_theme_pending.discard(identity)
        signals = self._smart_theme_signals.pop(identity, None)
        if signals is not None:
            try:
                signals.deleteLater()
            except RuntimeError:
                pass

        # The document may have been edited, rotated, recolored, or closed while
        # OpenCV was running. A stale result must never replace the current page.
        try:
            page_index = int(identity[0])
            if (not self._document_is_available()
                    or identity != self._smart_theme_identity(page_index)):
                return
        except Exception:
            return

        if not image_bytes:
            self._smart_theme_done.add(identity)
            return
        try:
            qimage = QImage(
                image_bytes, int(width), int(height), int(width) * 3,
                QImage.Format.Format_RGB888
            ).copy()
            if qimage.isNull():
                self._smart_theme_done.add(identity)
                return
            final_pixmap = QPixmap.fromImage(qimage)
            self.__dict__.setdefault("_smart_stale", {}).pop(page_index, None)
            self._remember_smart_master(self._smart_theme_final_cache, identity, final_pixmap)
            self._smart_theme_preview_cache.pop(identity, None)
            self._smart_theme_done.add(identity)

            # Populate only the currently displayed size. Future zoom/resize
            # requests scale this stable master instead of rerunning the filter.
            page_rect = self.page_rects.get(page_index)
            if page_rect is not None and not page_rect.isEmpty():
                w, h = max(1, round(page_rect.width())), max(1, round(page_rect.height()))
                page_version = self._page_render_revision(page_index)
                cache_key = (page_index, w, h, self.tab.dark_mode,
                             self.tab.smart_page_theme, self.tab.bg_color,
                             self.tab.ink_color, page_version)
                self._cache_rendered_page(cache_key, final_pixmap)
                self.update(page_rect.adjusted(-2, -2, 2, 2).toAlignedRect())
            else:
                self.update()
        except Exception:
            self._smart_theme_done.add(identity)

    def _panel_animation_active(self) -> bool:
        """True while the text-chat panel is animating its width (see _animate_ai_panel)."""
        try:
            until = float(getattr(self.window(), "_chat_panel_anim_until", 0.0) or 0.0)
            return until > 0.0 and time.monotonic() < until
        except Exception:
            return False

    def _render_page(self, index: int, rect: QRectF) -> QPixmap:
        if not self._document_is_available():
            return QPixmap()
        scale = self.page_scales.get(index, 1.0)
        w, h = max(1, round(rect.width())), max(1, round(rect.height()))
        page_version = self._page_render_revision(index)
        cache_key = (index, w, h, self.tab.dark_mode, self.tab.smart_page_theme,
                     self.tab.bg_color, self.tab.ink_color, page_version)
        smart_enabled = bool(self.tab.dark_mode and self.tab.smart_page_theme)
        if cache_key not in self.cache and self._panel_animation_active():
            # Mid-animation the viewport changes size every frame. Re-rendering
            # (MuPDF + theme filter) for each intermediate size is what froze the
            # motion, so reuse the nearest already-rendered image of this page
            # (same theme/version) and let paintEvent scale it. The exact-size
            # render happens once, right after the animation ends.
            for cached_key in reversed(list(self.cache.keys())):
                if cached_key[0] == index and cached_key[3:] == cache_key[3:]:
                    cached = self.cache.get(cached_key)
                    if cached is not None and not cached.isNull():
                        return cached
        if cache_key in self.cache:
            pixmap = self.cache.pop(cache_key)
            self.cache[cache_key] = pixmap
            if smart_enabled:
                identity = self._smart_theme_identity(index)
                if identity in self._smart_theme_preview_cache and identity not in self._smart_theme_pending and identity not in self._smart_theme_done:
                    self._schedule_cached_smart_theme_page(index, scale, identity)
            return pixmap

        if smart_enabled:
            identity = self._smart_theme_identity(index)
            final_master = self._smart_theme_final_cache.get(identity)
            if final_master is not None:
                self._smart_theme_final_cache.move_to_end(identity)
                self._cache_rendered_page(cache_key, final_master)
                return final_master

            preview_master = self._smart_theme_preview_cache.get(identity)
            if preview_master is not None:
                self._smart_theme_preview_cache.move_to_end(identity)
                self._cache_rendered_page(cache_key, preview_master)
                if identity not in self._smart_theme_pending and identity not in self._smart_theme_done:
                    self._schedule_cached_smart_theme_page(index, scale, identity)
                return preview_master

            # First render for this page revision/theme only. Keep a stable preview
            # and queue one full filter pass. Zoom or layout changes reuse this image.
            page = self.tab.doc.load_page(index)
            pix = page.get_pixmap(matrix=fitz.Matrix(scale, scale), alpha=False, annots=True)
            image = Image.frombytes("RGB", (pix.width, pix.height), pix.samples)
            preview = apply_page_theme_to_image(
                image, True, self.tab.bg_color, self.tab.ink_color, smart=False
            )
            preview_pixmap = QPixmap.fromImage(image_to_qimage(preview))
            # After an edit (move / resize / recolor of an annotation) only a few
            # bands of the page really changed. Keep the already smart-themed
            # pixels everywhere else instead of flashing the whole page back to
            # the plain theme until the new Smart Theme pass finishes.
            try:
                stale = self.__dict__.get("_smart_stale", {}).get(index)
                if (stale is not None and stale[0] == int(pix.width) and stale[1] == int(pix.height)
                        and stale[4] == str(self.tab.bg_color) and stale[5] == str(self.tab.ink_color)):
                    new_bands = self._smart_band_hashes(bytes(pix.samples), int(pix.width), int(pix.height))
                    old_bands = stale[2]
                    if new_bands is not None and len(new_bands) == len(old_bands):
                        # Start from the previous Smart Theme page and re-theme ONLY
                        # the bands that changed (with a little context around
                        # them) using the real Smart filter, right now. The page
                        # therefore never falls back to the plain theme.
                        rows = self._SMART_BAND_ROWS
                        page_w, page_h = int(pix.width), int(pix.height)
                        changed = [i for i, (n, o) in enumerate(zip(new_bands, old_bands)) if n != o]
                        groups = []
                        for band_no in changed:
                            if groups and band_no <= groups[-1][1] + 1:
                                groups[-1][1] = band_no
                            else:
                                groups.append([band_no, band_no])
                        raw_image = Image.frombytes("RGB", (page_w, page_h), bytes(pix.samples)) if groups else None
                        composite = QPixmap(stale[3])
                        painter_c = QPainter(composite)
                        context_rows = rows * 3
                        for first_band, last_band in groups:
                            y0 = first_band * rows
                            y1 = min(page_h, (last_band + 1) * rows)
                            cy0 = max(0, y0 - context_rows)
                            cy1 = min(page_h, y1 + context_rows)
                            themed_crop = apply_page_theme_to_image(
                                raw_image.crop((0, cy0, page_w, cy1)), True,
                                self.tab.bg_color, self.tab.ink_color, smart=True)
                            painter_c.drawImage(0, y0, image_to_qimage(
                                themed_crop.crop((0, y0 - cy0, page_w, y1 - cy0))))
                        painter_c.end()
                        preview_pixmap = composite
            except Exception:
                pass
            self._remember_smart_master(self._smart_theme_preview_cache, identity, preview_pixmap)
            self._cache_rendered_page(cache_key, preview_pixmap)
            self._queue_smart_theme_image(
                identity, bytes(pix.samples), int(pix.width), int(pix.height)
            )
            return preview_pixmap

        page = self.tab.doc.load_page(index)
        pix = page.get_pixmap(matrix=fitz.Matrix(scale, scale), alpha=False, annots=True)
        image = Image.frombytes("RGB", (pix.width, pix.height), pix.samples)
        themed_image = apply_page_theme_to_image(
            image, self.tab.dark_mode, self.tab.bg_color, self.tab.ink_color,
            smart=self.tab.smart_page_theme,
        )
        result = QPixmap.fromImage(image_to_qimage(themed_image))
        self._cache_rendered_page(cache_key, result)
        return result

    def paintEvent(self, event):
        painter = QPainter(self)
        try:
            # The canvas area around/between PDF pages belongs to the APP theme,
            # never to the per-page recoloring theme. Page Theme changes only the
            # rendered PDF pixels in _render_page(); margins, gaps and the empty
            # area below the currently visible page must stay consistent with
            # the main Engo interface (Dark, Midnight, Grass, Pink, Orange, Light).
            host = self.window()
            theme_settings = getattr(host, "settings", None)
            if theme_settings is None:
                # Be defensive for embedded/secondary canvases: walk the parent
                # chain before falling back to the default application theme.
                parent = self.parentWidget()
                while parent is not None and theme_settings is None:
                    theme_settings = getattr(parent, "settings", None)
                    parent = parent.parentWidget() if hasattr(parent, "parentWidget") else None
            ui_theme = theme_settings.value("ui_theme", "dark", type=str) if theme_settings is not None else "dark"
            canvas_background = QColor(engo_ui_theme_tokens(ui_theme)["raised"])
        except Exception:
            canvas_background = QColor("#252525")
        painter.fillRect(event.rect(), canvas_background)
        if not self._document_is_available():
            painter.end()
            return

        # Apply the live zoom transform to the real page drawing. The page,
        # text-selection geometry, annotation previews and tags all scale
        # together as one document scene; the old page is never left behind
        # under a separately scaled screenshot.
        visual_scale = float(getattr(self, "_zoom_visual_scale", 1.0))
        visual_anchor = QPointF(getattr(self, "_zoom_visual_anchor", QPointF()))
        painter.save()
        if abs(visual_scale - 1.0) >= 0.001:
            # Keep the live zoom visually smooth, matching the original V7 reader.
            # Stable page masters keep this interpolation inexpensive.
            painter.setRenderHint(QPainter.RenderHint.SmoothPixmapTransform, True)
            painter.translate(visual_anchor)
            painter.scale(visual_scale, visual_scale)
            painter.translate(-visual_anchor)
            # Inverse-transform the paint clip so pages that move into view
            # during zoom are not skipped by the normal lazy-render culling.
            clip = QRectF(event.rect())
            inv = 1.0 / max(0.001, visual_scale)
            p1 = QPointF(visual_anchor.x() + (clip.left() - visual_anchor.x()) * inv,
                         visual_anchor.y() + (clip.top() - visual_anchor.y()) * inv)
            p2 = QPointF(visual_anchor.x() + (clip.right() - visual_anchor.x()) * inv,
                         visual_anchor.y() + (clip.bottom() - visual_anchor.y()) * inv)
            scene_clip = QRectF(p1, p2).normalized().adjusted(-4, -4, 4, 4)
        else:
            scene_clip = QRectF(event.rect()).adjusted(-3, -3, 3, 3)

        # Use the transformed paint clip to avoid rasterizing pages that remain
        # far outside the viewport during the animation.
        for index, rect in self.page_rects.items():
            if not rect.intersects(scene_clip):
                continue
            shadow = rect.translated(0, 4)
            painter.fillRect(shadow, QColor(0, 0, 0, 68))
            pixmap = self._render_page(index, rect)
            # While the text chat slides open/closed the page is re-scaled every
            # frame; bilinear scaling of a full page master is what made that
            # motion stutter. Use the cheap transform for those frames only - the
            # settled layout is re-rendered sharp right after the animation.
            if (not self._panel_animation_active()
                    and (abs(visual_scale - 1.0) >= 0.001
                         or pixmap.width() != max(1, round(rect.width()))
                         or pixmap.height() != max(1, round(rect.height())))):
                painter.setRenderHint(QPainter.RenderHint.SmoothPixmapTransform, True)
            painter.drawPixmap(rect.toRect(), pixmap)
            # Region tags are re-drawn above the themed page image so each tag keeps
            # its own chosen color in both light and dark page themes.
            if abs(visual_scale - 1.0) < 0.001:
                try:
                    tag_page = self.tab.doc.load_page(index)
                    host = self.window()
                    color_lookup = getattr(host, "_tag_color", None)
                    for tag_annot in list(tag_page.annots() or []):
                        info = tag_annot.info or {}
                        if str(info.get("title") or "") != "Engo Region Tag":
                            continue
                        tag_name = str(info.get("content") or "").strip()
                        if not tag_name:
                            continue
                        tag_rect = self._annotation_rect_display(index, tag_annot, page=tag_page).intersected(rect)
                        if tag_rect.isEmpty():
                            continue
                        color_text = color_lookup(self.tab, tag_name) if callable(color_lookup) else "#f2bd55"
                        tag_color = QColor(str(color_text or "#f2bd55"))
                        if not tag_color.isValid():
                            tag_color = QColor("#f2bd55")
                        painter.save()
                        painter.setRenderHint(QPainter.RenderHint.Antialiasing, True)
                        outline_color = QColor(tag_color); outline_color.setAlpha(94)
                        painter.setPen(QPen(outline_color, 1.7))
                        fill_color = QColor(tag_color); fill_color.setAlpha(14)
                        painter.setBrush(QBrush(fill_color))
                        painter.drawRoundedRect(tag_rect, 3, 3)
                        label_h = 17.0
                        label_w = min(max(42.0, len(tag_name) * 7.0 + 14.0), max(42.0, tag_rect.width() + 24.0))
                        label_rect = QRectF(tag_rect.left(), max(rect.top(), tag_rect.top() - label_h), label_w, label_h)
                        label_color = QColor(tag_color); label_color.setAlpha(84)
                        painter.setPen(Qt.PenStyle.NoPen)
                        painter.setBrush(QBrush(label_color))
                        painter.drawRoundedRect(label_rect, 3, 3)
                        text_color = QColor("#15202b") if (tag_color.lightness() > 145) else QColor("#ffffff")
                        text_color.setAlpha(205)
                        painter.setPen(QPen(text_color))
                        font = painter.font(); font.setPointSizeF(7.0); font.setBold(True)
                        painter.setFont(font)
                        painter.drawText(label_rect.adjusted(5, 0, -4, 0), Qt.AlignmentFlag.AlignVCenter | Qt.AlignmentFlag.AlignLeft, tag_name)
                        painter.restore()
                except Exception:
                    pass
            # Search hits are drawn as a translucent yellow overlay on every matching page.
            for box in self.search_highlights.get(index, []):
                try:
                    nx, ny, nw, nh = [float(v) for v in box]
                    hit_rect = QRectF(rect.left() + nx * rect.width(), rect.top() + ny * rect.height(),
                                      max(4.0, nw * rect.width()), max(4.0, nh * rect.height())).intersected(rect)
                    painter.setRenderHint(QPainter.RenderHint.Antialiasing, True)
                    painter.setPen(QPen(QColor(255, 210, 70, 235), 2.0))
                    painter.setBrush(QBrush(QColor(255, 210, 70, 72)))
                    painter.drawRoundedRect(hit_rect, 3, 3)
                except Exception:
                    continue
            focus = self.ai_focus if self.ai_focus_visible else None
            if focus and int(focus[0]) == int(index):
                try:
                    if len(focus) >= 4:
                        _focus_page, norm_box, focus_label, focus_kind = focus
                    else:
                        _focus_page, norm_box, focus_label = focus
                        focus_kind = "text"
                    nx, ny, nw, nh = [max(0.0, min(1.0, float(v))) for v in norm_box]
                    # Clamp width/height to the page boundaries.
                    nw, nh = min(nw, 1.0 - nx), min(nh, 1.0 - ny)
                    focus_rect = QRectF(rect.x() + nx * rect.width(), rect.y() + ny * rect.height(),
                                         max(12.0, nw * rect.width()), max(8.0, nh * rect.height()))
                    focus_rect = focus_rect.intersected(rect)
                    painter.setRenderHint(QPainter.RenderHint.Antialiasing, True)
                    visual_kinds = {"diagram", "chart", "photo", "image", "figure", "graph", "plot", "drawing", "table"}
                    solution_kinds = {"solution", "worked_solution"}
                    if str(focus_kind).lower() in visual_kinds:
                        # Cool cyan distinguishes genuine visual material (chart/photo/diagram)
                        # from any written content, including handwritten text.
                        edge, fill = QColor(32, 205, 230, 225), QColor(20, 205, 230, 28)
                    elif str(focus_kind).lower() in solution_kinds:
                        edge, fill = QColor(95, 218, 132, 225), QColor(70, 210, 120, 28)
                    else:
                        edge, fill = QColor(255, 190, 58, 205), QColor(255, 190, 58, 24)
                    painter.setPen(QPen(edge, 2.5, Qt.PenStyle.SolidLine))
                    painter.setBrush(QBrush(fill))
                    painter.drawRoundedRect(focus_rect, 5, 5)
                except Exception:
                    pass
            # Temporary tutor marks are painted over the real PDF page surface.
            # They are not part of the rendered PDF and are discarded with the lesson
            # unless the learner explicitly saves them as PDF annotations.
            try:
                live_marks = getattr(self.tab, "_live_teaching_marks", {}).get(index, [])
                for mark in live_marks:
                    painter.save()
                    painter.setRenderHint(QPainter.RenderHint.Antialiasing, True)
                    if mark.get("type") == "arrow":
                        start = mark.get("start", [0, 0])
                        end = mark.get("end", [0, 0])
                        x1 = rect.left() + float(start[0]) * rect.width()
                        y1 = rect.top() + float(start[1]) * rect.height()
                        x2 = rect.left() + float(end[0]) * rect.width()
                        y2 = rect.top() + float(end[1]) * rect.height()
                        painter.setPen(QPen(QColor(15, 112, 220, 245), max(2.2, rect.width() / 420.0),
                                             Qt.PenStyle.SolidLine, Qt.PenCapStyle.RoundCap, Qt.PenJoinStyle.RoundJoin))
                        painter.drawLine(QPointF(x1, y1), QPointF(x2, y2))
                        angle = math.atan2(y2 - y1, x2 - x1)
                        head = max(9.0, rect.width() / 58.0)
                        p1 = QPointF(x2 - head * math.cos(angle - math.pi / 6), y2 - head * math.sin(angle - math.pi / 6))
                        p2 = QPointF(x2 - head * math.cos(angle + math.pi / 6), y2 - head * math.sin(angle + math.pi / 6))
                        painter.drawLine(QPointF(x2, y2), p1)
                        painter.drawLine(QPointF(x2, y2), p2)
                    painter.restore()
            except Exception:
                pass
            # PDF links are native link objects, not annotations. Render exactly
            # one compact in-page badge (chain icon + destination page), with no
            # second/outer rectangle around the original drag-selection area.
            try:
                link_page = self.tab.doc.load_page(index)
                link_rects = []
                for link_info in link_page.get_links():
                    if link_info.get("from") is None:
                        continue
                    kind = int(link_info.get("kind", -1))
                    target_page = (int(link_info.get("page", -1)) + 1
                                   if kind == fitz.LINK_GOTO and int(link_info.get("page", -1)) >= 0 else None)
                    uri = str(link_info.get("uri") or "")
                    link_rects.append((fitz.Rect(link_info["from"]), target_page, kind, uri))
                for raw_entry in getattr(self.tab, "_link_overlay_rects", {}).get(index, []):
                    values = tuple(raw_entry)
                    if len(values) >= 5:
                        link_rects.append((fitz.Rect(values[:4]), int(values[4]), int(fitz.LINK_GOTO), ""))
                    else:
                        link_rects.append((fitz.Rect(values[:4]), None, int(fitz.LINK_GOTO), ""))
                seen_link_rects = set()
                for source_rect, target_page, kind, uri in link_rects:
                    identity = self._page_link_identity(index, source_rect, target_page, kind, uri)
                    if identity in seen_link_rects:
                        continue
                    seen_link_rects.add(identity)
                    badge = self._link_badge_display(index, source_rect, page=link_page)
                    if badge.isEmpty():
                        continue
                    selected_link = getattr(self.tab, "selected_page_link", None) == identity
                    painter.setRenderHint(QPainter.RenderHint.Antialiasing, True)
                    border = QColor(130, 205, 255, 255) if selected_link else QColor(205, 231, 255, 245)
                    fill = QColor(30, 105, 180, 245) if selected_link else QColor(25, 83, 140, 218)
                    painter.setPen(QPen(border, 2.0 if selected_link else 0.9, Qt.PenStyle.SolidLine))
                    painter.setBrush(QBrush(fill))
                    painter.drawRoundedRect(badge, 4, 4)
                    # Draw a small chain-link glyph using vector geometry.
                    icon_cx = badge.left() + min(10.0, badge.width() * 0.22)
                    icon_cy = badge.center().y()
                    painter.save()
                    painter.translate(icon_cx, icon_cy)
                    painter.rotate(-35)
                    painter.setPen(QPen(QColor("#f1f8ff"), 1.45, Qt.PenStyle.SolidLine,
                                         Qt.PenCapStyle.RoundCap, Qt.PenJoinStyle.RoundJoin))
                    painter.setBrush(Qt.BrushStyle.NoBrush)
                    painter.drawRoundedRect(QRectF(-4.8, -2.1, 7.0, 4.2), 2.0, 2.0)
                    painter.drawRoundedRect(QRectF(1.0, -2.1, 7.0, 4.2), 2.0, 2.0)
                    painter.restore()
                    if target_page is not None and target_page > 0:
                        painter.setFont(QFont("Segoe UI", 8, QFont.Weight.DemiBold))
                        painter.setPen(QColor("#ffffff"))
                        text_rect = QRectF(badge.left() + min(18.0, badge.width() * 0.42), badge.top(),
                                           max(8.0, badge.width() - min(20.0, badge.width() * 0.45)), badge.height())
                        painter.drawText(text_rect, Qt.AlignmentFlag.AlignCenter, str(target_page))
            except Exception:
                pass
            painter.setPen(QPen(QColor("#434b59"), 1))
            painter.setBrush(Qt.BrushStyle.NoBrush)
            painter.drawRect(rect)
        # Draw the selected annotation's true outline: polygon vertices, pen strokes,
        # highlight quads, ellipse perimeter, or the natural rectangle for text/notes.
        selected = self.tab.selected_annotation
        if selected and selected[0] in self.page_rects:
            page_index, xref = selected
            try:
                page = self.tab.doc.load_page(page_index)
                annot = next((a for a in (page.annots() or []) if a.xref == xref), None)
                if annot is not None:
                    geometry = self._annotation_selection_geometry(page_index, annot, page=page)
                    if (self._dragging_annotation and self._drag_xref == xref
                            and self._drag_kind == "resize" and self._drag_control_mode == "vertex"):
                        geometry = self._geometry_with_vertex_preview(geometry)
                    bounds = geometry["bounds"]
                    if not bounds.isEmpty():
                        painter.setRenderHint(QPainter.RenderHint.Antialiasing, True)
                        painter.save()
                        if self._dragging_annotation and self._drag_xref == xref:
                            if self._drag_kind == "rotate":
                                painter.translate(bounds.center())
                                painter.rotate(self._drag_rotation_delta)
                                painter.translate(-bounds.center())
                            elif self._drag_control_mode != "vertex":
                                target = self._drag_preview_rect
                                sx = target.width() / max(bounds.width(), 1.0)
                                sy = target.height() / max(bounds.height(), 1.0)
                                painter.translate(target.left(), target.top())
                                painter.scale(sx, sy)
                                painter.translate(-bounds.left(), -bounds.top())
                        painter.setPen(QPen(QColor("#5b9cff"), 2.0, Qt.PenStyle.SolidLine,
                                             Qt.PenCapStyle.RoundCap, Qt.PenJoinStyle.RoundJoin))
                        painter.setBrush(Qt.BrushStyle.NoBrush)
                        # A selected Pen-tool shape keeps its own stroke untouched:
                        # no blue glow over its sides while it is merely selected.
                        # The preview outline is only needed while it is being
                        # moved / resized / rotated.
                        _sel_info = dict(annot.info or {})
                        _is_pen_shape_sel = (
                            str(_sel_info.get("title") or "").strip().lower() == "engo pen shape"
                            or str(_sel_info.get("content") or "").strip().lower().startswith("pen shape"))
                        if not _is_pen_shape_sel or (self._dragging_annotation and self._drag_xref == xref):
                            for shape_path in geometry["paths"]:
                                painter.drawPath(shape_path)
                        if self._annotation_edit_mode and len(getattr(self.tab, "selected_annotations", []) or []) == 1:
                            painter.setPen(QPen(QColor("#eaf2ff"), 1.0))
                            painter.setBrush(QBrush(QColor("#5b9cff")))
                            for handle in geometry.get("handles", []):
                                point = handle.get("point", QPointF())
                                if handle.get("name") == "scale":
                                    painter.save()
                                    painter.translate(point)
                                    painter.rotate(45)
                                    painter.drawRoundedRect(QRectF(-4.8, -4.8, 9.6, 9.6), 1.6, 1.6)
                                    painter.restore()
                                else:
                                    painter.drawEllipse(point, 4.7, 4.7)
                            selected_info = dict(annot.info or {})
                            is_point = "pen shape · point" in str(selected_info.get("content") or "").lower()
                            if not is_point:
                                rotate_absolute = self._rotation_handle_center(bounds)
                                edge_y = bounds.top() if rotate_absolute.y() < bounds.top() else bounds.bottom()
                                painter.setPen(QPen(QColor("#8eb8ff"), 1.4, Qt.PenStyle.SolidLine))
                                painter.drawLine(QPointF(bounds.center().x(), edge_y), rotate_absolute)
                                painter.setPen(QPen(QColor("#f2f7ff"), 1.2))
                                painter.setBrush(QBrush(QColor("#337fe6")))
                                painter.drawEllipse(rotate_absolute, 7.0, 7.0)
                                painter.setPen(QPen(QColor("#ffffff"), 1.0))
                                painter.setFont(QFont("Segoe UI", 8, QFont.Weight.DemiBold))
                                painter.drawText(QRectF(rotate_absolute.x()-6.5, rotate_absolute.y()-7.0, 13.0, 14.0),
                                                 Qt.AlignmentFlag.AlignCenter, "↻")
                        painter.restore()
                        if len(getattr(self.tab, "selected_annotations", []) or []) == 1:
                            painter.save()
                            painter.setRenderHint(QPainter.RenderHint.Antialiasing, True)
                            painter.setPen(QPen(QColor("#74a7ff"), 1.0))
                            painter.setBrush(QBrush(QColor(35, 53, 80, 238)))
                            painter.setPen(QColor("#f4f8ff"))
                            painter.setFont(QFont("Segoe UI", 7, QFont.Weight.Bold))
                            selected_type = int((annot.type or (0, ""))[0])
                            text_note_types = (getattr(fitz, "PDF_ANNOT_FREE_TEXT", 2),
                                               getattr(fitz, "PDF_ANNOT_TEXT", 0))
                            host = self.window()
                            is_arabic = str(getattr(getattr(host, "settings", None), "value", lambda *_a, **_k: "en")(
                                "interface_language", "en", type=str) or "en").lower().startswith("ar")
                            if selected_type in text_note_types:
                                content_rect, size_rect, color_rect = self._annotation_text_action_rects(bounds)
                                painter.drawRoundedRect(content_rect, 6, 6)
                                painter.drawRoundedRect(size_rect, 6, 6)
                                content_label = "تعديل المحتوى" if is_arabic else "Edit content"
                                size_label = (("تم" if is_arabic else "Done") if self._annotation_edit_mode
                                              else ("تعديل الحجم" if is_arabic else "Edit size"))
                                painter.drawText(content_rect, Qt.AlignmentFlag.AlignCenter, content_label)
                                painter.drawText(size_rect, Qt.AlignmentFlag.AlignCenter, size_label)
                                if self._annotation_edit_mode:
                                    painter.drawRoundedRect(color_rect, 6, 6)
                                    painter.drawText(color_rect, Qt.AlignmentFlag.AlignCenter,
                                                     "اللون" if is_arabic else "Color")
                            else:
                                edit_rect = self._annotation_edit_button_rect(bounds)
                                painter.drawRoundedRect(edit_rect, 6, 6)
                                painter.setFont(QFont("Segoe UI", 8, QFont.Weight.Bold))
                                painter.drawText(edit_rect, Qt.AlignmentFlag.AlignCenter,
                                                 (("تم" if is_arabic else "Done") if self._annotation_edit_mode
                                                  else ("تعديل" if is_arabic else "Edit")))
                                if self._annotation_edit_mode:
                                    color_rect = self._annotation_color_button_rect(bounds)
                                    painter.drawRoundedRect(color_rect, 6, 6)
                                    painter.drawText(color_rect, Qt.AlignmentFlag.AlignCenter,
                                                     "اللون" if is_arabic else "Color")
                            painter.restore()
                        if self._dragging_annotation:
                            painter.setPen(QColor("#dce8ff"))
                            caption_rect = QRectF(bounds.left(), max(2, bounds.top() - 46), 210, 18)
                            painter.setBrush(QColor(27, 38, 57, 235))
                            painter.drawRoundedRect(caption_rect, 5, 5)
                            caption = (f"Rotate · {self._drag_rotation_delta:+.0f}°" if self._drag_kind == "rotate"
                                       else "Drag nodes to resize · drag inside to move")
                            painter.drawText(caption_rect.adjusted(7, 0, -4, 0), Qt.AlignmentFlag.AlignVCenter, caption)
            except Exception:
                pass
        # Additional selected annotations (Windows-style multi-selection).
        # The active item is drawn above with resize/rotate grips; the others show
        # their own true outlines and move together during a group drag.
        try:
            active_selection = self.tab.selected_annotation
            for selected_item in list(getattr(self.tab, "selected_annotations", []) or []):
                if selected_item == active_selection:
                    continue
                page_index, xref = selected_item
                if page_index not in self.page_rects:
                    continue
                page = self.tab.doc.load_page(int(page_index))
                annot = next((a for a in (page.annots() or []) if int(a.xref) == int(xref)), None)
                if annot is None:
                    continue
                geometry = self._annotation_selection_geometry(page_index, annot, page=page)
                painter.save()
                if self._dragging_annotation and self._drag_group_items:
                    painter.translate(self._drag_group_delta)
                painter.setRenderHint(QPainter.RenderHint.Antialiasing, True)
                painter.setPen(QPen(QColor("#5b9cff"), 1.8, Qt.PenStyle.DashLine,
                                    Qt.PenCapStyle.RoundCap, Qt.PenJoinStyle.RoundJoin))
                painter.setBrush(Qt.BrushStyle.NoBrush)
                for shape_path in geometry["paths"]:
                    painter.drawPath(shape_path)
                painter.restore()
        except Exception:
            pass

        # Native text selection paints only actual PDF word bounds. It is distinct
        # from the rectangular/scanned-image selection path below.
        if self._text_selection_display_rects:
            painter.save()
            if self._text_selection_tool == "highlight":
                painter.setPen(QPen(QColor(220, 170, 35, 190), 0.8))
                painter.setBrush(QBrush(QColor(245, 211, 78, 125)))
            else:
                painter.setPen(QPen(QColor(67, 130, 220, 155), 0.8))
                painter.setBrush(QBrush(QColor(86, 151, 244, 105)))
            for text_rect in self._text_selection_display_rects:
                painter.drawRoundedRect(QRectF(text_rect).adjusted(0, 0.5, 0, -0.5), 1.5, 1.5)
            painter.restore()

        # Windows-like rubber-band selection: left-to-right selects contained
        # annotations; right-to-left selects anything touched by the rectangle.
        if self._marquee_active:
            painter.save()
            marquee = QRectF(self._marquee_start, self._marquee_current).normalized()
            painter.setPen(QPen(QColor("#4f9cff"), 1.2, Qt.PenStyle.DashLine))
            painter.setBrush(QBrush(QColor(70, 145, 245, 38)))
            painter.drawRect(marquee)
            painter.restore()

        if self._drawing and self._draw_page in self.page_rects:
            tool = self.tab.active_tool
            painter.setRenderHint(QPainter.RenderHint.Antialiasing, True)
            if tool == "pen":
                painter.setPen(QPen(QColor(self.tab.annotation_colors.get("pen", DEFAULT_ANNOTATION_COLORS["pen"])), 3, Qt.PenStyle.SolidLine, Qt.PenCapStyle.RoundCap, Qt.PenJoinStyle.RoundJoin))
                if len(self._draw_points) > 1:
                    painter.drawPolyline(QPolygonF(self._draw_points))
                elif self._draw_points:
                    painter.drawPoint(self._draw_points[0])
            else:
                r = QRectF(self._draw_start, self._draw_current).normalized()
                if tool == "highlight":
                    highlight = QColor(self.tab.annotation_colors.get("highlight", DEFAULT_ANNOTATION_COLORS["highlight"]))
                    highlight.setAlpha(180)
                    fill = QColor(self.tab.annotation_colors.get("highlight", DEFAULT_ANNOTATION_COLORS["highlight"]))
                    fill.setAlpha(75)
                    painter.setPen(QPen(highlight, 1))
                    painter.setBrush(QBrush(fill))
                elif tool == "link":
                    painter.setPen(QPen(QColor(80, 150, 255, 220), 2, Qt.PenStyle.DashLine))
                    painter.setBrush(QBrush(QColor(80, 150, 255, 40)))
                else:
                    painter.setPen(QPen(QColor(80, 180, 255, 220), 1, Qt.PenStyle.DashLine))
                    painter.setBrush(QBrush(QColor(80, 180, 255, 30)))
                painter.drawRect(r)
        painter.restore()
        painter.end()

    def _page_at(self, point: QPointF):
        for index, rect in self.page_rects.items():
            if rect.contains(point):
                return index, rect
        return -1, QRectF()

    def _display_rect_for_pdf_rect(self, index: int, page_rect: QRectF, pdf_rect) -> QRectF:
        r = fitz.Rect(pdf_rect)
        points = [
            self._pdf_to_display(index, page_rect, fitz.Point(r.x0, r.y0)),
            self._pdf_to_display(index, page_rect, fitz.Point(r.x1, r.y0)),
            self._pdf_to_display(index, page_rect, fitz.Point(r.x1, r.y1)),
            self._pdf_to_display(index, page_rect, fitz.Point(r.x0, r.y1)),
        ]
        xs = [p.x() for p in points]
        ys = [p.y() for p in points]
        return QRectF(min(xs), min(ys), max(xs)-min(xs), max(ys)-min(ys)).normalized()

    def _text_words_for_page(self, index: int):
        cached = self._pdf_word_cache.get(int(index))
        if cached is not None:
            return cached
        page = self.tab.doc.load_page(int(index))
        try:
            # sort=True gives a stable top-to-bottom reading sequence. This is
            # important when a drag spans several lines: the selected range must
            # include every word between the two visible endpoints.
            try:
                words = list(page.get_text("words", sort=True) or [])
            except TypeError:
                words = list(page.get_text("words") or [])
        except Exception:
            words = []
        normalized = [tuple(word) for word in words if len(word) >= 8 and str(word[4] or "").strip()]
        self._pdf_word_cache[int(index)] = normalized
        return normalized

    def _text_word_boxes(self, index: int, page_rect: QRectF):
        # The PDF-to-screen transform is unchanged for repeated pointer-move
        # events. Cache it per page geometry instead of recalculating every word
        # on every mouse move, which also makes long text drags smoother.
        try:
            page_rotation = int(self.tab.doc.load_page(int(index)).rotation)
        except Exception:
            page_rotation = 0
        geometry_key = (
            round(page_rect.x(), 2), round(page_rect.y(), 2),
            round(page_rect.width(), 2), round(page_rect.height(), 2), page_rotation,
        )
        cached = self._pdf_word_box_cache.get(int(index))
        if cached is not None and cached[0] == geometry_key:
            return cached[1]
        entries = []
        for word_index, word in enumerate(self._text_words_for_page(index)):
            try:
                rect = fitz.Rect(word[:4])
                display_rect = self._display_rect_for_pdf_rect(index, page_rect, rect)
                if display_rect.width() > 0.5 and display_rect.height() > 0.5:
                    entries.append((word_index, word, rect, display_rect))
            except Exception:
                continue
        self._pdf_word_box_cache[int(index)] = (geometry_key, entries)
        return entries

    def _text_word_at(self, index: int, page_rect: QRectF, point: QPointF):
        matches = []
        for entry in self._text_word_boxes(index, page_rect):
            word_rect = entry[3]
            if word_rect.adjusted(-2.0, -2.0, 2.0, 2.0).contains(point):
                center = word_rect.center()
                distance = (center.x()-point.x())**2 + (center.y()-point.y())**2
                matches.append((distance, entry))
        return min(matches, key=lambda item: item[0])[1] if matches else None

    def _nearest_text_word(self, index: int, page_rect: QRectF, point: QPointF, max_distance: float = 30.0):
        best = None
        best_distance = float("inf")
        for entry in self._text_word_boxes(index, page_rect):
            rect = entry[3]
            dx = max(rect.left()-point.x(), 0.0, point.x()-rect.right())
            dy = max(rect.top()-point.y(), 0.0, point.y()-rect.bottom())
            distance = math.hypot(dx, dy)
            if distance < best_distance:
                best_distance, best = distance, entry
        return best if best is not None and best_distance <= max_distance else None

    def _clear_text_selection(self):
        self._text_selecting = False
        self._text_selection_page = -1
        self._text_selection_tool = ""
        self._text_selection_words = []
        self._text_selection_start_word = -1
        self._text_selection_end_word = -1
        self._text_selection_display_rects = []
        self._text_selection_text = ""
        self._text_selection_records = []
        self.update()

    def has_active_pointer_selection(self) -> bool:
        """Whether Escape should cancel an in-progress PDF selection/drag."""
        return bool(
            self._drawing
            or self._marquee_active
            or self._text_selecting
            or self._dragging_annotation
            or self._text_selection_display_rects
        )

    def cancel_active_pointer_selection(self) -> bool:
        """Cancel the current mouse selection without changing the active tool."""
        if not self.has_active_pointer_selection():
            return False

        # Native text selection can be used for asking about text or translating it.
        if self._text_selecting or self._text_selection_display_rects:
            self._clear_text_selection()

        # AI region, translation region, highlight, tag, link, shape, and pen
        # previews all share _drawing. Dropping this state ensures the later
        # mouse release cannot commit the rectangle or stroke.
        if self._drawing:
            self._drawing = False
            self._draw_page = -1
            self._draw_start = QPointF()
            self._draw_current = QPointF()
            self._draw_points = []

        # Restore the annotations that were selected before a marquee began.
        if self._marquee_active:
            # Keep marquee commit behavior identical to the original Select tool,
            # but restore the pre-drag selection when Escape cancels the gesture.
            previous = list(self._marquee_restore_selection or [])
            self._marquee_active = False
            self._marquee_page = -1
            self._marquee_previous = []
            self._marquee_restore_selection = []
            self._marquee_additive = False
            self._marquee_start = QPointF()
            self._marquee_current = QPointF()
            if previous:
                self.tab.set_annotation_selection(previous)
            else:
                self.tab.clear_annotation_selection()

        # A selected annotation can also be dragged/resized/rotated with a live
        # preview. Escape discards that preview; it never commits the transform.
        if self._dragging_annotation:
            self._dragging_annotation = False
            self._drag_page = -1
            self._drag_xref = 0
            self._drag_kind = "move"
            self._drag_handle = ""
            self._drag_moved = False
            self._drag_rotation_delta = 0.0
            self._drag_rotation_step = 1.0
            self._drag_aspect_ratio = 0.0
            self._drag_control_mode = ""
            self._drag_control_meta = {}
            self._drag_control_preview_pos = QPointF()
            self._drag_control_geometry = None
            self._drag_target_page = -1
            self._drag_target_display_rect = QRectF()
            self._drag_group_items = []
            self._drag_group_delta = QPointF()
            self._drag_original_rect = QRectF()
            self._drag_preview_rect = QRectF()

        self.setCursor(self._tool_default_cursor())
        self.update()
        return True

    def _begin_text_selection(self, index: int, page_rect: QRectF, word_entry):
        self._clear_text_selection()
        self._text_selecting = True
        self._text_selection_page = int(index)
        self._text_selection_tool = str(self.tab.active_tool or "select")
        self._text_selection_words = self._text_words_for_page(index)
        self._text_selection_start_word = int(word_entry[0])
        self._text_selection_end_word = int(word_entry[0])
        self._text_selection_current_page_rect = QRectF(page_rect)
        if self._text_selection_tool == "select":
            self.tab.clear_annotation_selection()
        self._refresh_text_selection_preview()
        self.setCursor(Qt.CursorShape.IBeamCursor)
        self.update()

    def _update_text_selection(self, point: QPointF):
        if not self._text_selecting or self._text_selection_page < 0:
            return
        page_rect = self.page_rects.get(self._text_selection_page, QRectF())
        if page_rect.isEmpty():
            return
        endpoint = self._nearest_text_word(self._text_selection_page, page_rect, point, max_distance=34.0)
        if endpoint is not None:
            self._text_selection_end_word = int(endpoint[0])
        self._refresh_text_selection_preview()
        self.update()

    def _refresh_text_selection_preview(self):
        words = self._text_selection_words
        first = self._text_selection_start_word
        last = self._text_selection_end_word
        if not words or first < 0 or last < 0:
            self._text_selection_display_rects = []
            self._text_selection_text = ""
            self._text_selection_records = []
            return
        low, high = sorted((first, last))
        page_rect = self.page_rects.get(self._text_selection_page, QRectF())
        display_by_index = {
            entry[0]: entry[3]
            for entry in self._text_word_boxes(self._text_selection_page, page_rect)
        }
        text_parts = []
        previous_line = None
        previous_block = None
        selected_records = []
        line_rects = OrderedDict()
        for idx in range(low, high + 1):
            word = words[idx]
            token = str(word[4] or "").strip()
            if not token:
                continue
            block_no, line_no = int(word[5]), int(word[6])
            display_rect = display_by_index.get(idx)
            if display_rect is not None:
                line_rects.setdefault((block_no, line_no), []).append(display_rect)
            if previous_line is None:
                pass
            elif block_no != previous_block:
                text_parts.append("\n\n")
            elif line_no != previous_line:
                text_parts.append("\n")
            else:
                text_parts.append(" ")
            text_parts.append(token)
            previous_block, previous_line = block_no, line_no
            selected_records.append(word)

        # Draw one continuous selection band per line (or per separate column
        # segment), rather than a row of isolated word boxes. A drag from the
        # first line to a lower line therefore looks and behaves like normal text
        # selection while still preserving the exact underlying word records.
        display_rects = []
        for _line_key, rects in line_rects.items():
            rects = sorted(rects, key=lambda r: (r.left(), r.top()))
            segment = None
            for rect in rects:
                if segment is None:
                    segment = QRectF(rect)
                    continue
                gap = rect.left() - segment.right()
                join_limit = max(7.0, min(segment.height(), rect.height()) * 2.4)
                if gap <= join_limit and abs(rect.center().y() - segment.center().y()) <= max(5.0, rect.height()):
                    segment = segment.united(rect)
                else:
                    display_rects.append(segment)
                    segment = QRectF(rect)
            if segment is not None:
                display_rects.append(segment)

        self._text_selection_display_rects = display_rects
        self._text_selection_text = "".join(text_parts).strip()
        self._text_selection_records = selected_records

    def _show_pdf_text_selection_menu(self, global_pos: QPoint, text: str, page_index: int, records):
        if not text.strip():
            return
        host = self.window()
        is_ar = str(getattr(getattr(host, "settings", None), "value", lambda *_a, **_k: "en")(
            "interface_language", "en", type=str) or "en").lower().startswith("ar")
        menu = QMenu(self)
        copy_action = menu.addAction(make_icon("copy", "#8ec8ff", 16), "نسخ النص" if is_ar else "Copy text")
        highlight_action = menu.addAction(make_icon("highlight", "#f2cf52", 16), "تظليل النص" if is_ar else "Highlight text")
        menu.addSeparator()
        ask_action = menu.addAction(make_icon("ai", "#9fbaff", 16), "اسأل Engo AI عن النص" if is_ar else "Ask Engo AI about this text")
        chosen = menu.exec(global_pos)
        if chosen is copy_action:
            QApplication.clipboard().setText(text)
            if callable(getattr(host, "show_status", None)):
                host.show_status("تم نسخ النص المحدد" if is_ar else "Selected text copied")
        elif chosen is highlight_action:
            self.tab.add_highlight_words(int(page_index), records)
        elif chosen is ask_action:
            panel = getattr(host, "ai_panel", None)
            if panel is not None:
                try:
                    if callable(getattr(host, "_refresh_ai_chat_context", None)):
                        host._refresh_ai_chat_context(self.tab)
                    panel.set_document(self.tab.path, Path(self.tab.path).name)
                    if not panel.isVisible():
                        host._animate_ai_panel(True)
                    QTimer.singleShot(260, lambda p=panel, value=text: p._ask_about_selected_chat_text(value, "document"))
                except Exception as exc:
                    QMessageBox.warning(self, APP_NAME, str(exc))

    def _translate_selected_pdf_words(self, index: int, records, selected_text: str):
        """Translate selected native PDF text without uploading a full page crop."""
        try:
            page = self.tab.doc.load_page(int(index))
            boxes = [fitz.Rect(word[:4]) for word in records if len(word) >= 5]
            if not boxes:
                self._clear_text_selection()
                return
            clip = fitz.Rect(
                min(box.x0 for box in boxes), min(box.y0 for box in boxes),
                max(box.x1 for box in boxes), max(box.y1 for box in boxes),
            )
            # A small margin prevents tight glyph ascenders/descenders from being
            # clipped in the preview image. The text itself is sent separately.
            clip = fitz.Rect(clip.x0 - 3.0, clip.y0 - 3.0, clip.x1 + 3.0, clip.y1 + 3.0)
            # Text word boxes use unrotated PDF coordinates, so CropBox is the
            # correct clipping boundary even when the displayed page is rotated.
            clip = clip & page.cropbox
            if clip.is_empty or clip.width <= 0 or clip.height <= 0:
                raise RuntimeError("The selected PDF text has no visible area.")
            # Native PDF text is sent as text only. No rasterization, JPEG encoding,
            # or image upload is needed for this path, which makes it noticeably
            # lighter than translating a scanned/handwritten region.
            self.tab.translateRegionSelected.emit(
                int(index), b"",
                (float(clip.x0), float(clip.y0), float(clip.x1), float(clip.y1)),
                str(selected_text or "").strip(),
            )
            self.tab.set_tool("select")
            # Synchronize the shared toolbar and linked-pane tool state after the
            # selection is consumed, exactly as the rectangle translation path does.
            host = self.window()
            primary = host.active_tab() if callable(getattr(host, "active_tab", None)) else None
            if primary is not None and getattr(primary, "_linked_view_secondary", None) is self.tab:
                primary.active_tool = "select"
            setter = getattr(host, "_set_view_target_tab", None)
            if callable(setter):
                setter(self.tab)
            tool_setter = getattr(host, "_set_tool", None)
            if callable(tool_setter):
                tool_setter("select", quiet=True)
            help_setter = getattr(host, "_show_selected_tool_context_help", None)
            if callable(help_setter):
                help_setter("select")
        except Exception as exc:
            host = self.window()
            status = getattr(host, "show_status", None)
            if callable(status):
                status(f"Could not translate selected text: {exc}")
        finally:
            self._clear_text_selection()

    def _finish_text_selection(self, global_pos: QPoint):
        index = self._text_selection_page
        tool = self._text_selection_tool
        text = str(self._text_selection_text or "").strip()
        records = list(getattr(self, "_text_selection_records", []) or [])
        self._text_selecting = False
        self.setCursor(Qt.CursorShape.ArrowCursor)
        if not text or not records:
            self._clear_text_selection()
            return
        if tool == "highlight":
            self.tab.add_highlight_words(index, records)
            self._clear_text_selection()
        else:
            self._show_pdf_text_selection_menu(global_pos, text, index, records)
            self.update()

    def _pdf_to_display(self, index: int, rect: QRectF, point: fitz.Point) -> QPointF:
        page = self.tab.doc.load_page(index)
        p = fitz.Point(point)
        try:
            p = p * page.rotation_matrix
        except Exception:
            pass
        return QPointF(rect.left() + p.x / max(page.rect.width, 1) * rect.width(),
                       rect.top() + p.y / max(page.rect.height, 1) * rect.height())

    def _display_to_pdf(self, index: int, rect: QRectF, point: QPointF) -> fitz.Point:
        page = self.tab.doc.load_page(index)
        x = (point.x() - rect.x()) * page.rect.width / max(rect.width(), 1)
        y = (point.y() - rect.y()) * page.rect.height / max(rect.height(), 1)
        p = fitz.Point(x, y)
        try:
            return p * page.derotation_matrix
        except Exception:
            return p

    def _rect_to_pdf(self, index, page_rect, selection: QRectF) -> fitz.Rect:
        selection = selection.normalized().intersected(page_rect)
        points = [QPointF(selection.left(), selection.top()), QPointF(selection.right(), selection.top()),
                  QPointF(selection.right(), selection.bottom()), QPointF(selection.left(), selection.bottom())]
        mapped = [self._display_to_pdf(index, page_rect, p) for p in points]
        clip = fitz.Rect(min(p.x for p in mapped), min(p.y for p in mapped),
                         max(p.x for p in mapped), max(p.y for p in mapped))
        # Most PDF APIs (including get_text clip) use unrotated page coordinates.
        # The rendered canvas follows page.rect (rotated), so the inverse transform
        # above is mandatory. Intersect with CropBox to avoid out-of-page spillover.
        try:
            page = self.tab.doc.load_page(int(index))
            crop_box = fitz.Rect(page.cropbox)
            clip = clip & crop_box
        except Exception:
            pass
        return clip

    def _rect_to_render_clip(self, index, page_rect, selection: QRectF) -> fitz.Rect:
        """Map selection to page.rect coordinates for get_pixmap(), including rotation.

        PyMuPDF applies the page rotation when rasterizing. Its get_pixmap(clip=...)
        therefore expects coordinates in the rotated page.rect space, not the
        unrotated CropBox coordinates returned by _rect_to_pdf(). Using the latter
        after Rotate crops an unrelated area of the page.
        """
        visible = QRectF(selection).normalized().intersected(QRectF(page_rect))
        if visible.isEmpty() or page_rect.isEmpty():
            return fitz.Rect()
        page = self.tab.doc.load_page(int(index))
        page_bounds = fitz.Rect(page.rect)
        sx = float(page_bounds.width) / max(float(page_rect.width()), 1.0)
        sy = float(page_bounds.height) / max(float(page_rect.height()), 1.0)
        clip = fitz.Rect(
            (visible.left() - page_rect.left()) * sx,
            (visible.top() - page_rect.top()) * sy,
            (visible.right() - page_rect.left()) * sx,
            (visible.bottom() - page_rect.top()) * sy,
        )
        return clip & page_bounds

    def _map_path(self, index, page_rect, points):
        return [self._display_to_pdf(index, page_rect, p) for p in points]

    def _annotation_rect_display(self, index: int, annot, page=None) -> QRectF:
        """Map an annotation's PDF rectangle to canvas pixels for hit-testing/selection."""
        # PyMuPDF Annot wrappers are page-owned.  Keep the originating Page alive
        # while reading an annotation instead of relying on a detached wrapper.
        page = page if page is not None else self.tab.doc.load_page(index)
        display_page = self.page_rects.get(index, QRectF())
        if display_page.isEmpty():
            return QRectF()
        rect = fitz.Rect(annot.rect)
        corners = [fitz.Point(rect.x0, rect.y0), fitz.Point(rect.x1, rect.y0),
                   fitz.Point(rect.x1, rect.y1), fitz.Point(rect.x0, rect.y1)]
        try:
            corners = [pt * page.rotation_matrix for pt in corners]
        except Exception:
            pass
        xs = [pt.x for pt in corners]
        ys = [pt.y for pt in corners]
        x0, x1 = min(xs), max(xs)
        y0, y1 = min(ys), max(ys)
        return QRectF(
            display_page.left() + x0 / max(page.rect.width, 1) * display_page.width(),
            display_page.top() + y0 / max(page.rect.height, 1) * display_page.height(),
            max(2.0, (x1 - x0) / max(page.rect.width, 1) * display_page.width()),
            max(2.0, (y1 - y0) / max(page.rect.height, 1) * display_page.height()),
        )

    def _link_rect_display(self, index: int, source_rect, page=None) -> QRectF:
        """Map a PDF link rectangle into the visible canvas coordinate space."""
        try:
            page = page if page is not None else self.tab.doc.load_page(index)
            display_page = self.page_rects.get(index, QRectF())
            if display_page.isEmpty() or source_rect is None:
                return QRectF()
            source = fitz.Rect(source_rect)
            corners = [fitz.Point(source.x0, source.y0), fitz.Point(source.x1, source.y0),
                       fitz.Point(source.x1, source.y1), fitz.Point(source.x0, source.y1)]
            try:
                corners = [point * page.rotation_matrix for point in corners]
            except Exception:
                pass
            xs = [point.x for point in corners]
            ys = [point.y for point in corners]
            page_w, page_h = max(page.rect.width, 1), max(page.rect.height, 1)
            return QRectF(
                display_page.left() + min(xs) / page_w * display_page.width(),
                display_page.top() + min(ys) / page_h * display_page.height(),
                max(2.0, (max(xs) - min(xs)) / page_w * display_page.width()),
                max(2.0, (max(ys) - min(ys)) / page_h * display_page.height()),
            )
        except Exception:
            return QRectF()

    @staticmethod
    def _page_link_identity(index: int, source_rect, target_page=None, kind=None, uri=""):
        return (int(index), tuple(round(float(value), 2) for value in fitz.Rect(source_rect)),
                None if target_page is None else int(target_page), int(kind if kind is not None else -1), str(uri or ""))

    def _link_badge_display(self, index: int, source_rect, page=None) -> QRectF:
        """Return the only visible/clickable rectangle used for an in-page link."""
        link_bounds = self._link_rect_display(index, source_rect, page=page)
        if link_bounds.isEmpty():
            return QRectF()
        badge_w = min(64.0, max(34.0, link_bounds.width() - 6.0))
        badge_h = min(22.0, max(15.0, link_bounds.height() - 6.0))
        return QRectF(link_bounds.center().x() - badge_w / 2.0,
                      link_bounds.center().y() - badge_h / 2.0, badge_w, badge_h)

    def _page_link_at(self, pos: QPointF):
        """Find a link only when its single visible badge is clicked."""
        index, _display_rect = self._page_at(pos)
        if index < 0:
            return None
        try:
            page = self.tab.doc.load_page(index)
            entries = []
            seen = set()
            for link_info in page.get_links():
                if link_info.get("from") is None:
                    continue
                kind = int(link_info.get("kind", -1))
                raw_target = int(link_info.get("page", -1))
                target_page = raw_target + 1 if kind == fitz.LINK_GOTO and raw_target >= 0 else None
                uri = str(link_info.get("uri") or "")
                source = fitz.Rect(link_info["from"])
                identity = self._page_link_identity(index, source, target_page, kind, uri)
                if identity not in seen:
                    seen.add(identity)
                    entries.append({"index": index, "source": source, "target_page": target_page,
                                    "kind": kind, "uri": uri, "identity": identity})
            for raw_entry in getattr(self.tab, "_link_overlay_rects", {}).get(index, []):
                values = tuple(raw_entry)
                if len(values) < 4:
                    continue
                source = fitz.Rect(values[:4])
                target_page = int(values[4]) if len(values) >= 5 else None
                kind = int(fitz.LINK_GOTO)
                identity = self._page_link_identity(index, source, target_page, kind, "")
                if identity not in seen:
                    seen.add(identity)
                    entries.append({"index": index, "source": source, "target_page": target_page,
                                    "kind": kind, "uri": "", "identity": identity})
            for entry in entries:
                if self._link_badge_display(index, entry["source"], page=page).contains(pos):
                    return entry
        except Exception:
            return None
        return None

    def _point_over_pdf_link(self, pos: QPointF) -> bool:
        return self._page_link_at(pos) is not None

    def _open_page_link(self, entry) -> bool:
        if not entry:
            return False
        try:
            kind = int(entry.get("kind", -1))
            if kind == fitz.LINK_GOTO and entry.get("target_page") is not None:
                self.tab.go_to_page(max(0, int(entry["target_page"]) - 1))
                return True
            if kind == fitz.LINK_URI and entry.get("uri"):
                QDesktopServices.openUrl(QUrl(entry["uri"]))
                return True
        except Exception:
            return False
        return False

    def _activate_pdf_link(self, pos: QPointF) -> bool:
        """Compatibility wrapper: activate only the compact visible link badge."""
        entry = self._page_link_at(pos)
        if entry is None:
            return False
        return self._open_page_link(entry)

    def _annotation_selection_geometry(self, index: int, annot, page=None):
        """Return page-space annotation paths and resize grips matching the real shape.

        Lines, polygons, polylines, ink and highlights are represented by their
        actual PDF vertices. Circles use an ellipse path and cardinal grips;
        rectangular note/text annotations keep their natural rectangular outline.
        """
        page = page if page is not None else self.tab.doc.load_page(int(index))
        bounds = self._annotation_rect_display(int(index), annot, page=page)
        if bounds.isEmpty():
            return {"bounds": QRectF(), "paths": [], "handles": [], "kind": "rect", "closed": False}
        subtype = int((annot.type or (0, ""))[0])
        type_line = getattr(fitz, "PDF_ANNOT_LINE", 3)
        type_polygon = getattr(fitz, "PDF_ANNOT_POLYGON", 6)
        type_polyline = getattr(fitz, "PDF_ANNOT_POLY_LINE", 7)
        type_ink = getattr(fitz, "PDF_ANNOT_INK", 15)
        type_highlight = getattr(fitz, "PDF_ANNOT_HIGHLIGHT", 8)
        type_circle = getattr(fitz, "PDF_ANNOT_CIRCLE", 5)

        def to_display(point):
            display_page = self.page_rects[int(index)]
            mapped = fitz.Point(point)
            try:
                mapped = mapped * page.rotation_matrix
            except Exception:
                pass
            return QPointF(display_page.left() + mapped.x / max(page.rect.width, 1) * display_page.width(),
                           display_page.top() + mapped.y / max(page.rect.height, 1) * display_page.height())

        paths = []
        handles = []
        editable_groups = []
        kind = "rect"
        closed = False
        raw_vertices = list(annot.vertices or [])

        if subtype == type_circle:
            kind, closed = "circle", True
            path = QPainterPath()
            path.addEllipse(bounds)
            paths.append(path)
            shape_label = str((annot.info or {}).get("content") or "").lower()
            is_point = "pen shape · point" in shape_label or "pen shape - point" in shape_label
            if not is_point:
                shape_info = dict(annot.info or {})
                is_pen_circle = (str(shape_info.get("title") or "").strip().lower() == "engo pen shape"
                                 or "pen shape" in shape_label)
                if not is_pen_circle:
                    cx, cy = bounds.center().x(), bounds.center().y()
                    handles = [
                        {"name": "p0", "point": QPointF(cx, bounds.top()), "anchor": QPointF(cx, cy), "mode": "circle_axis", "axis": "vertical"},
                        {"name": "p1", "point": QPointF(bounds.right(), cy), "anchor": QPointF(cx, cy), "mode": "circle_axis", "axis": "horizontal"},
                        {"name": "p2", "point": QPointF(cx, bounds.bottom()), "anchor": QPointF(cx, cy), "mode": "circle_axis", "axis": "vertical"},
                        {"name": "p3", "point": QPointF(bounds.left(), cy), "anchor": QPointF(cx, cy), "mode": "circle_axis", "axis": "horizontal"},
                    ]
        elif subtype == type_highlight and len(raw_vertices) >= 4:
            kind, closed = "highlight", True
            display_vertices = [to_display(point) for point in raw_vertices]
            indexed_points = []
            for quad_index, n in enumerate(range(0, len(display_vertices) - 3, 4)):
                # PyMuPDF stores Quad vertices as UL, UR, LL, LR; the visible
                # polygon path is UL -> UR -> LR -> LL. Keep source indices so
                # dragging a grip edits exactly that PDF vertex, not its AABB.
                source_indices = [0, 1, 3, 2]
                quad = [display_vertices[n + source_index] for source_index in source_indices]
                if len(quad) == 4:
                    path = QPainterPath(quad[0])
                    for point in quad[1:]:
                        path.lineTo(point)
                    path.closeSubpath()
                    paths.append(path)
                    editable_groups.append({"kind": "highlight", "group_index": quad_index,
                                            "points": list(quad), "source_indices": source_indices,
                                            "closed": True})
                    for point, source_index in zip(quad, source_indices):
                        indexed_points.append((quad_index, source_index, point))
            selected_points = indexed_points if len(indexed_points) <= 12 else []
            if not selected_points and indexed_points:
                selected_points = [
                    min(indexed_points, key=lambda item: item[2].x()),
                    max(indexed_points, key=lambda item: item[2].x()),
                    min(indexed_points, key=lambda item: item[2].y()),
                    max(indexed_points, key=lambda item: item[2].y()),
                ]
            if selected_points:
                for i, (quad_index, source_index, point) in enumerate(selected_points):
                    others = [item[2] for item in indexed_points
                              if item[0] != quad_index or item[1] != source_index]
                    anchor_point = max(others, key=lambda p: math.hypot(p.x()-point.x(), p.y()-point.y())) if others else bounds.center()
                    handles.append({"name": f"p{i}", "point": point, "anchor": anchor_point,
                                    "mode": "bounds", "group_index": quad_index,
                                    "source_index": source_index})
        elif subtype in (type_line, type_polygon, type_polyline) and len(raw_vertices) >= 2:
            display_vertices = [to_display(point) for point in raw_vertices]
            if subtype == type_line:
                kind, closed = "line", False
                display_vertices = display_vertices[:2]
            elif subtype == type_polygon:
                kind, closed = "polygon", True
            else:
                kind, closed = "polyline", False
            path = QPainterPath(display_vertices[0])
            for point in display_vertices[1:]:
                path.lineTo(point)
            if closed:
                path.closeSubpath()
            paths.append(path)
            editable_groups.append({"kind": kind, "group_index": 0,
                                    "points": list(display_vertices),
                                    "source_indices": list(range(len(display_vertices))),
                                    "closed": bool(closed)})
            # Lines and polygons expose their actual endpoints/corners. Long polylines
            # are reduced to meaningful control points to avoid covering the shape.
            if len(display_vertices) <= 12:
                selected_indices = list(range(len(display_vertices)))
            else:
                selected_indices = [0, len(display_vertices)-1]
                selected_indices.extend([
                    min(range(len(display_vertices)), key=lambda j: display_vertices[j].x()),
                    max(range(len(display_vertices)), key=lambda j: display_vertices[j].x()),
                    min(range(len(display_vertices)), key=lambda j: display_vertices[j].y()),
                    max(range(len(display_vertices)), key=lambda j: display_vertices[j].y()),
                ])
                selected_indices = list(dict.fromkeys(selected_indices))[:12]
            for n, vertex_index in enumerate(selected_indices):
                point = display_vertices[vertex_index]
                others = [p for j, p in enumerate(display_vertices) if j != vertex_index]
                anchor_point = max(others, key=lambda p: math.hypot(p.x()-point.x(), p.y()-point.y())) if others else bounds.center()
                handles.append({"name": f"p{n}", "point": point, "anchor": anchor_point,
                                "mode": "vertex", "group_index": 0,
                                "source_index": vertex_index})
        elif subtype == type_ink and raw_vertices:
            kind, closed = "ink", False
            # Ink vertices are stored as one or more independent strokes.
            if isinstance(raw_vertices[0], (tuple, list)) and len(raw_vertices[0]) >= 2 \
                    and isinstance(raw_vertices[0][0], (int, float)):
                raw_strokes = [raw_vertices]
            else:
                raw_strokes = raw_vertices
            mapped_strokes = []
            for stroke_index, stroke in enumerate(raw_strokes):
                display_points = [to_display(point) for point in stroke]
                if len(display_points) < 2:
                    continue
                path = QPainterPath(display_points[0])
                for point in display_points[1:]:
                    path.lineTo(point)
                paths.append(path)
                mapped_strokes.append((stroke_index, display_points))
                editable_groups.append({"kind": "ink", "group_index": int(stroke_index),
                                        "points": list(display_points),
                                        "source_indices": list(range(len(display_points))),
                                        "closed": False})
            # Actual pen path endpoints and directional extrema act as resize nodes.
            candidates = []
            for stroke_index, points in mapped_strokes:
                local_indices = [0, len(points)-1,
                                 min(range(len(points)), key=lambda j: points[j].x()),
                                 max(range(len(points)), key=lambda j: points[j].x()),
                                 min(range(len(points)), key=lambda j: points[j].y()),
                                 max(range(len(points)), key=lambda j: points[j].y())]
                for point_index in dict.fromkeys(local_indices):
                    candidates.append((stroke_index, point_index, points[point_index]))
            # Keep at most eight useful nodes for complex drawings.
            if len(candidates) > 8:
                selected = [candidates[0], candidates[-1]]
                selected.extend([min(candidates, key=lambda item: item[2].x()),
                                 max(candidates, key=lambda item: item[2].x()),
                                 min(candidates, key=lambda item: item[2].y()),
                                 max(candidates, key=lambda item: item[2].y())])
                seen = set()
                candidates = [item for item in selected if not ((item[0], item[1]) in seen or seen.add((item[0], item[1])))]
            for n, (stroke_index, point_index, point) in enumerate(candidates):
                all_others = [item[2] for item in candidates if item[0] != stroke_index or item[1] != point_index]
                anchor_point = max(all_others, key=lambda p: math.hypot(p.x()-point.x(), p.y()-point.y())) if all_others else bounds.center()
                handles.append({"name": f"p{n}", "point": point, "anchor": anchor_point,
                                "mode": "vertex", "group_index": stroke_index,
                                "stroke_index": stroke_index, "source_index": point_index})
        else:
            # Native square, text box and sticky-note annotations are rectangular.
            path = QPainterPath()
            path.addRect(bounds)
            paths.append(path)
            kind = "rect"
            corners = [("tl", QPointF(bounds.left(), bounds.top())),
                       ("tr", QPointF(bounds.right(), bounds.top())),
                       ("bl", QPointF(bounds.left(), bounds.bottom())),
                       ("br", QPointF(bounds.right(), bounds.bottom()))]
            handles = [{"name": name, "point": point, "anchor": QPointF(
                bounds.right() if "l" in name else bounds.left(),
                bounds.bottom() if "t" in name else bounds.top()), "mode": "rect"}
                for name, point in corners]
            # Pen-recognized closed shapes are edited from their corners only.
            # Side grips add redundant control points directly over the drawn
            # outline and make the selection look cluttered.
            shape_info = dict(annot.info or {})
            is_pen_shape = (str(shape_info.get("title") or "").strip().lower() == "engo pen shape"
                            or str(shape_info.get("content") or "").strip().lower().startswith("pen shape"))
            if not is_pen_shape:
                handles.extend([
                    {"name": "edge_top", "point": QPointF(bounds.center().x(), bounds.top()),
                     "anchor": QPointF(bounds.center().x(), bounds.bottom()), "mode": "edge", "side": "top"},
                    {"name": "edge_bottom", "point": QPointF(bounds.center().x(), bounds.bottom()),
                     "anchor": QPointF(bounds.center().x(), bounds.top()), "mode": "edge", "side": "bottom"},
                    {"name": "edge_left", "point": QPointF(bounds.left(), bounds.center().y()),
                     "anchor": QPointF(bounds.right(), bounds.center().y()), "mode": "edge", "side": "left"},
                    {"name": "edge_right", "point": QPointF(bounds.right(), bounds.center().y()),
                     "anchor": QPointF(bounds.left(), bounds.center().y()), "mode": "edge", "side": "right"},
                ])

        if not paths:
            path = QPainterPath()
            path.addRect(bounds)
            paths = [path]
            kind = "rect"
        # Use the actual geometry's bounds, not the often over-padded /Rect that
        # MuPDF stores for lines and freehand strokes. This keeps rotate handles
        # centered on the visible object instead of offsetting/expanding it.
        path_bounds = QRectF()
        for shape_path in paths:
            shape_rect = shape_path.boundingRect()
            path_bounds = shape_rect if path_bounds.isEmpty() else path_bounds.united(shape_rect)
        if not path_bounds.isEmpty():
            center = path_bounds.center()
            # For a Point, keep the exact visible circle bounds. Inflating this
            # rectangle makes the uniform-scale grip use a larger baseline than
            # the actual dot, causing a noticeable jump on the first resize.
            point_content = str((annot.info or {}).get("content") or "").lower()
            is_point_annotation = ("pen shape · point" in point_content or
                                   "pen shape - point" in point_content)
            if is_point_annotation:
                bounds = QRectF(path_bounds)
            else:
                min_w = 12.0 if path_bounds.width() < 12.0 else path_bounds.width()
                min_h = 12.0 if path_bounds.height() < 12.0 else path_bounds.height()
                bounds = QRectF(center.x()-min_w/2.0, center.y()-min_h/2.0, min_w, min_h)
        # One dedicated uniform-scale grip is available for every selected shape.
        # Compute it only after the true path bounds are known (not the PDF /Rect,
        # which is padded for Line and Ink annotations).
        display_page = self.page_rects.get(int(index), QRectF())
        scale_x = bounds.right() + 15.0
        scale_y = bounds.bottom() + 15.0
        if not display_page.isEmpty():
            if scale_x > display_page.right() - 5.0:
                scale_x = bounds.left() - 15.0
            if scale_y > display_page.bottom() - 5.0:
                scale_y = bounds.top() - 15.0
            scale_x = min(max(scale_x, display_page.left() + 5.0), display_page.right() - 5.0)
            scale_y = min(max(scale_y, display_page.top() + 5.0), display_page.bottom() - 5.0)
        handles.append({"name": "scale", "point": QPointF(scale_x, scale_y),
                        "anchor": QPointF(bounds.center()), "mode": "scale"})
        return {"bounds": QRectF(bounds), "paths": paths, "handles": handles,
                "editable_groups": editable_groups, "kind": kind, "closed": closed}

    def _geometry_with_vertex_preview(self, geometry):
        """Build live preview paths after moving one real PDF vertex.

        Unlike the old AABB-based resize path, this keeps every untouched vertex
        fixed and moves only the grip the user is dragging. The pointer and all
        preview points stay in the same visible-page coordinate frame.
        """
        groups = geometry.get("editable_groups") or []
        meta = self._drag_control_meta or {}
        target = QPointF(self._drag_control_preview_pos)
        group_index = int(meta.get("group_index", meta.get("stroke_index", 0)))
        source_index = int(meta.get("source_index", -1))
        paths = []
        all_points = []
        updated_handles = []
        for group in groups:
            points = [QPointF(point) for point in group.get("points", [])]
            source_indices = list(group.get("source_indices", range(len(points))))
            if int(group.get("group_index", 0)) == group_index:
                try:
                    local_index = source_indices.index(source_index)
                    if 0 <= local_index < len(points):
                        points[local_index] = QPointF(target)
                except ValueError:
                    pass
            if not points:
                continue
            path = QPainterPath(points[0])
            for point in points[1:]:
                path.lineTo(point)
            if group.get("closed"):
                path.closeSubpath()
            paths.append(path)
            all_points.extend(points)
        if not all_points:
            return geometry
        left = min(point.x() for point in all_points)
        right = max(point.x() for point in all_points)
        top = min(point.y() for point in all_points)
        bottom = max(point.y() for point in all_points)
        bounds = QRectF(left, top, max(12.0, right-left), max(12.0, bottom-top))
        for handle in geometry.get("handles", []):
            updated = dict(handle)
            if (int(updated.get("group_index", updated.get("stroke_index", 0))) == group_index
                    and int(updated.get("source_index", -999)) == source_index):
                updated["point"] = QPointF(target)
            updated_handles.append(updated)
        result = dict(geometry)
        result.update({"paths": paths, "handles": updated_handles, "bounds": bounds})
        return result

    def _annotation_at(self, index: int, pos: QPointF):
        """Return stable annotation data, never a page-owned PyMuPDF Annot wrapper.

        PyMuPDF annotations are tied to their Page object. Returning an Annot from
        this helper used to let the local Page be released before mouse handlers
        read xref/info/rect from the wrapper; that can destabilize selection, most
        noticeably on the linked supplementary canvas.
        """
        try:
            if not self._document_is_available():
                return None
            page = self.tab.doc.load_page(int(index))
            annotations = list(page.annots() or [])
            # Later annotations visually sit above earlier annotations.
            for annot in reversed(annotations):
                geometry = self._annotation_selection_geometry(index, annot, page=page)
                bounds = geometry["bounds"]
                xref = int(annot.xref)
                hit = False
                # A filled/closed shape can be selected from its interior; open strokes
                # use a stroked path so the empty corners of their bounding rectangle
                # are not treated as part of the annotation.
                for shape_path in geometry["paths"]:
                    if geometry["closed"] and shape_path.contains(pos):
                        hit = True
                        break
                    stroker = QPainterPathStroker()
                    stroker.setWidth(18.0)
                    if stroker.createStroke(shape_path).contains(pos):
                        hit = True
                        break
                if geometry["kind"] == "rect" and bounds.adjusted(-3, -3, 3, 3).contains(pos):
                    hit = True
                # Native line annotations have tiny PDF hit rectangles at their
                # endpoints. Treat the visible endpoint grips as part of the line
                # hit target so double-clicking the tip is reliable.
                if not hit and geometry.get("kind") == "line":
                    for grip in geometry.get("handles", []):
                        point = grip.get("point", QPointF())
                        if math.hypot(pos.x() - point.x(), pos.y() - point.y()) <= 22.0:
                            hit = True
                            break
                is_selected = ((int(index), xref) in (getattr(self.tab, "selected_annotations", []) or [])
                               or self.tab.selected_annotation == (int(index), xref))
                if not hit and is_selected:
                    hit = (self._rotation_handle_at(bounds, pos) or
                           bool(self._resize_handle_at(bounds, pos, geometry)))
                if hit:
                    info = dict(getattr(annot, "info", {}) or {})
                    label = (info.get("content") or info.get("title") or "PDF annotation")
                    return xref, QRectF(bounds), str(label), geometry
        except Exception:
            return None
        return None

    def wheelEvent(self, event):
        angle_delta = event.angleDelta().y()
        pixel_delta = event.pixelDelta().y()
        delta = angle_delta or pixel_delta
        scroll_area = self.display_scroll or self.tab.scroll
        if event.modifiers() & Qt.KeyboardModifier.ControlModifier:
            if delta:
                anchor = self.mapTo(scroll_area.viewport(), event.position().toPoint())
                # Angle-wheel notches get a moderately stronger response; smooth
                # touchpad pixel deltas use a smaller divisor so fine finger motion
                # is perceptible without turning into large jumps.
                factor = math.exp(delta / (1320.0 if angle_delta else 390.0))
                if self.external_zoom_callback is not None:
                    self.external_zoom_callback(factor, anchor)
                else:
                    self.tab.zoom_by(factor, anchor)
                event.accept()
                return
        elif delta:
            # Scroll OFF keeps one page (or one Book spread) in the canvas.
            # Both normal and linked-secondary panes can pan a zoomed page and
            # turn pages only after reaching the corresponding vertical edge.
            bar = scroll_area.verticalScrollBar()
            if not self.tab.scroll_mode:
                at_edge = ((delta > 0 and bar.value() <= bar.minimum()) or
                           (delta < 0 and bar.value() >= bar.maximum()))
                if at_edge:
                    now = time.monotonic()
                    if now - getattr(self.tab, "_last_page_wheel_turn", 0.0) >= 0.28:
                        step = 2 if self.tab.book_mode else 1
                        target = self.tab.current_page + (-step if delta > 0 else step)
                        callback = self.external_page_turn_callback
                        if callable(callback):
                            callback(target)
                        else:
                            self.tab.go_to_page(target)
                        self.tab._last_page_wheel_turn = now
                else:
                    amount = int(pixel_delta) if pixel_delta else int((angle_delta / 120.0) * max(3, bar.singleStep() * 3))
                    bar.setValue(bar.value() - amount)
            elif self.display_scroll is not None:
                amount = int(pixel_delta) if pixel_delta else int((angle_delta / 120.0) * max(3, bar.singleStep() * 3))
                bar.setValue(bar.value() - amount)
            else:
                self.tab.scroll_continuously(angle_delta, pixel_delta)
            event.accept()
            return
        super().wheelEvent(event)

    def _resize_handle_at(self, bounds: QRectF, pos: QPointF, geometry=None):
        if geometry:
            for item in geometry.get("handles", []):
                point = item.get("point", QPointF())
                if math.hypot(pos.x() - point.x(), pos.y() - point.y()) <= 11.0:
                    return str(item.get("name") or "")
            return ""
        points = {
            "tl": QPointF(bounds.left(), bounds.top()),
            "tr": QPointF(bounds.right(), bounds.top()),
            "bl": QPointF(bounds.left(), bounds.bottom()),
            "br": QPointF(bounds.right(), bounds.bottom()),
        }
        for handle, point in points.items():
            if math.hypot(pos.x() - point.x(), pos.y() - point.y()) <= 10.0:
                return handle
        return ""

    def _annotation_edit_button_rect(self, bounds: QRectF) -> QRectF:
        """Legacy single Edit pill used by non-text annotations."""
        page_index = self.tab.selected_annotation[0] if self.tab.selected_annotation else -1
        page_bounds = self.page_rects.get(page_index, QRectF())
        y = bounds.top() - 27.0
        if not page_bounds.isEmpty() and y < page_bounds.top() + 4:
            y = bounds.bottom() + 5.0
        x = max(page_bounds.left() + 3 if not page_bounds.isEmpty() else 3,
                min(bounds.right() - 48, (page_bounds.right() - 50) if not page_bounds.isEmpty() else bounds.right() - 48))
        return QRectF(x, y, 46, 21)

    def _annotation_text_action_rects(self, bounds):
        """Content, size, and optional color actions for one selected text/note."""
        page_index = self.tab.selected_annotation[0] if self.tab.selected_annotation else -1
        page_bounds = self.page_rects.get(page_index, QRectF())
        content_w, size_w, color_w, gap, h = 84.0, 68.0, 48.0, 4.0, 22.0
        total_w = content_w + gap + size_w + gap + color_w
        y = bounds.top() - h - 5.0
        if not page_bounds.isEmpty() and y < page_bounds.top() + 3:
            y = bounds.bottom() + 5.0
        left_limit = page_bounds.left() + 3 if not page_bounds.isEmpty() else 3.0
        right_limit = page_bounds.right() - total_w - 3 if not page_bounds.isEmpty() else bounds.right() - total_w
        preferred_x = bounds.right() - total_w
        x = max(left_limit, min(preferred_x, right_limit))
        content_rect = QRectF(x, y, content_w, h)
        size_rect = QRectF(x + content_w + gap, y, size_w, h)
        color_rect = QRectF(size_rect.right() + gap, y, color_w, h)
        return content_rect, size_rect, color_rect

    def _annotation_color_button_rect(self, bounds):
        """Place a compact Color action beside the regular Edit/Done action."""
        edit_rect = self._annotation_edit_button_rect(bounds)
        page_index = self.tab.selected_annotation[0] if self.tab.selected_annotation else -1
        page_bounds = self.page_rects.get(page_index, QRectF())
        width, gap = 48.0, 4.0
        x = edit_rect.left() - width - gap
        if not page_bounds.isEmpty() and x < page_bounds.left() + 3:
            x = edit_rect.right() + gap
        if not page_bounds.isEmpty():
            x = min(x, page_bounds.right() - width - 3)
            x = max(page_bounds.left() + 3, x)
        return QRectF(x, edit_rect.top(), width, edit_rect.height())

    def _selected_annotation_action_at(self, page_index: int, pos: QPointF) -> bool:
        """Return True when the pointer is over a floating action for the selected annotation.

        These controls can sit just outside the annotation bounds. Give them priority
        over PDF text selection so a click on Edit/Color is never swallowed by the
        underlying document text.
        """
        try:
            selected = list(getattr(self.tab, "selected_annotations", []) or [])
            if len(selected) != 1 or int(selected[0][0]) != int(page_index):
                return False
            xref = int(selected[0][1])
            page = self.tab.doc.load_page(int(page_index))
            annot = next((item for item in (page.annots() or []) if int(item.xref) == xref), None)
            if annot is None:
                return False
            geometry = self._annotation_selection_geometry(int(page_index), annot)
            bounds = geometry.get("bounds") if geometry else None
            if bounds is None:
                return False
            annot_type = int((annot.type or (0, ""))[0])
            text_note_types = (getattr(fitz, "PDF_ANNOT_FREE_TEXT", 2),
                               getattr(fitz, "PDF_ANNOT_TEXT", 0))
            if annot_type in text_note_types:
                content_rect, size_rect, color_rect = self._annotation_text_action_rects(bounds)
                return (content_rect.contains(pos) or size_rect.contains(pos) or
                        (self._annotation_edit_mode and color_rect.contains(pos)))
            edit_rect = self._annotation_edit_button_rect(bounds)
            color_rect = self._annotation_color_button_rect(bounds)
            return edit_rect.contains(pos) or (self._annotation_edit_mode and color_rect.contains(pos))
        except (RuntimeError, ValueError, TypeError, AttributeError, IndexError):
            return False
        except Exception:
            return False

    def _tool_default_cursor(self):
        tool = str(getattr(self.tab, "active_tool", "") or "")
        if tool == "select":
            return Qt.CursorShape.ArrowCursor
        if tool == "pan":
            return Qt.CursorShape.OpenHandCursor
        return Qt.CursorShape.CrossCursor

    def _selected_annotation_control_at(self, page_index: int, pos: QPointF) -> str:
        """Report which control of the single selected annotation lies under ``pos``.

        Returns "action" for the floating Edit/Done/Color pills (always live, so
        they work from Pen and every other tool), "rotate" or a grip name for the
        rotate/resize grips while Edit mode is on, otherwise "".
        """
        try:
            if self._selected_annotation_action_at(page_index, pos):
                return "action"
            if not self._annotation_edit_mode:
                return ""
            selected = list(getattr(self.tab, "selected_annotations", []) or [])
            if len(selected) != 1 or int(selected[0][0]) != int(page_index):
                return ""
            page = self.tab.doc.load_page(int(page_index))
            xref = int(selected[0][1])
            annot = next((a for a in (page.annots() or []) if int(a.xref) == xref), None)
            if annot is None:
                return ""
            geometry = self._annotation_selection_geometry(int(page_index), annot, page=page)
            bounds = geometry.get("bounds") if geometry else None
            if bounds is None or bounds.isEmpty():
                return ""
            content = str((annot.info or {}).get("content") or "").lower()
            is_point = "pen shape · point" in content or "pen shape - point" in content
            if not is_point and self._rotation_handle_at(bounds, pos):
                return "rotate"
            return str(self._resize_handle_at(bounds, pos, geometry) or "")
        except Exception:
            return ""

    def _open_annotation_editor(self, page_index: int, xref: int):
        try:
            page = self.tab.doc.load_page(int(page_index))
            annot = next((a for a in (page.annots() or []) if int(a.xref) == int(xref)), None)
            if annot is None:
                return False
            annot_type = int((annot.type or (0, ""))[0])
            info = dict(annot.info or {})
            if annot_type == getattr(fitz, "PDF_ANNOT_FREE_TEXT", 2):
                fontsize, fontname = 11, "Helv"
                try:
                    da = str(self.tab.doc.xref_get_key(int(xref), "DA")[1] or "")
                    size_match = re.search(r"([0-9]+(?:\.[0-9]+)?)\s+Tf", da)
                    font_match = re.search(r"/([A-Za-z0-9]+)\s+[0-9.]+\s+Tf", da)
                    if size_match: fontsize = float(size_match.group(1))
                    if font_match: fontname = font_match.group(1)
                except Exception:
                    pass
                dlg = TextAnnotationEditorDialog(info.get("content", ""), fontsize, fontname, self)
                if dlg.exec() == QDialog.DialogCode.Accepted:
                    text, new_size, new_font = dlg.values()
                    self.tab.update_freetext_annotation(int(page_index), int(xref), text, new_size, new_font)
                    self._annotation_edit_mode = False
                    self.update()
                    return True
                return False
            if annot_type == getattr(fitz, "PDF_ANNOT_TEXT", 0):
                text, ok = QInputDialog.getMultiLineText(self, "Edit sticky note", "Note text:", str(info.get("content") or ""))
                if ok:
                    self.tab.update_text_note(int(page_index), int(xref), text)
                    self.update()
                    return True
                return False
            return False
        except Exception as exc:
            QMessageBox.warning(self, APP_NAME, f"Could not edit this annotation:\n{exc}")
            return False

    def _annotation_color_hex(self, annot):
        """Read the visible stroke/text color of a selected annotation as #RRGGBB."""
        try:
            annot_type = int((annot.type or (0, ""))[0])
            if annot_type == getattr(fitz, "PDF_ANNOT_FREE_TEXT", 2):
                da = str(self.tab.doc.xref_get_key(int(annot.xref), "DA")[1] or "")
                match = re.search(r"([-+]?(?:\d+\.?\d*|\.\d+))\s+([-+]?(?:\d+\.?\d*|\.\d+))\s+([-+]?(?:\d+\.?\d*|\.\d+))\s+rg", da)
                if match:
                    values = [max(0.0, min(1.0, float(value))) for value in match.groups()]
                    return QColor.fromRgbF(*values).name()
                gray = re.search(r"([-+]?(?:\d+\.?\d*|\.\d+))\s+g(?:\s|$)", da)
                if gray:
                    value = max(0.0, min(1.0, float(gray.group(1))))
                    return QColor.fromRgbF(value, value, value).name()
            colors = dict(annot.colors or {})
            values = colors.get("stroke") or colors.get("fill") or []
            if isinstance(values, (tuple, list)) and len(values) >= 3:
                rgb = [max(0.0, min(1.0, float(value))) for value in values[:3]]
                return QColor.fromRgbF(*rgb).name()
            if isinstance(values, (tuple, list)) and len(values) == 1:
                value = max(0.0, min(1.0, float(values[0])))
                return QColor.fromRgbF(value, value, value).name()
        except Exception:
            pass
        return "#808080"

    def _annotation_background_color_hex(self, annot):
        try:
            values = (dict(annot.colors or {})).get("stroke") or []
            if isinstance(values, (tuple, list)) and len(values) >= 3:
                rgb = [max(0.0, min(1.0, float(value))) for value in values[:3]]
                return QColor.fromRgbF(*rgb).name()
            if isinstance(values, (tuple, list)) and len(values) == 1:
                value = max(0.0, min(1.0, float(values[0])))
                return QColor.fromRgbF(value, value, value).name()
        except Exception:
            pass
        return None

    def _open_annotation_color_editor(self, page_index: int, xref: int):
        try:
            page = self.tab.doc.load_page(int(page_index))
            annot = next((item for item in (page.annots() or []) if int(item.xref) == int(xref)), None)
            if annot is None:
                return False
            host = self.window()
            settings = getattr(host, "settings", None)
            is_ar = str(settings.value("interface_language", "en", type=str) if settings is not None else "en").lower().startswith("ar")
            is_freetext = int((annot.type or (0, ""))[0]) == getattr(fitz, "PDF_ANNOT_FREE_TEXT", 2)
            dialog = AnnotationColorEditDialog(
                self, self._annotation_color_hex(annot), is_ar,
                background_color=self._annotation_background_color_hex(annot),
                allow_background=is_freetext,
            )
            if dialog.exec() != QDialog.DialogCode.Accepted:
                return False
            changed = self.tab.update_annotation_color(
                int(page_index), int(xref), dialog.selected_color,
                background_color=dialog.selected_background_color,
            )
            if changed:
                self._annotation_edit_mode = True
                self.update()
            return bool(changed)
        except Exception as exc:
            QMessageBox.warning(self, APP_NAME,
                                (f"تعذر تعديل لون التعليق التوضيحي:\n{exc}" if self._context_is_arabic() else
                                 f"Could not change annotation color:\n{exc}"))
            return False

    def _context_is_arabic(self):
        try:
            settings = getattr(self.window(), "settings", None)
            return bool(settings and str(settings.value("interface_language", "en", type=str)).lower().startswith("ar"))
        except Exception:
            return False

    def _rotation_handle_center(self, bounds: QRectF) -> QPointF:
        x = bounds.center().x()
        page_index = self.tab.selected_annotation[0] if self.tab.selected_annotation else -1
        page_bounds = self.page_rects.get(page_index, QRectF())
        above = bounds.top() - 22.0
        below = bounds.bottom() + 22.0
        if page_bounds.isEmpty():
            return QPointF(x, above if above >= 10.0 else below)
        if above >= page_bounds.top() + 8.0:
            return QPointF(x, above)
        if below <= page_bounds.bottom() - 8.0:
            return QPointF(x, below)
        return QPointF(x, max(page_bounds.top() + 8.0, min(above, page_bounds.bottom() - 8.0)))

    def _rotation_handle_at(self, bounds: QRectF, pos: QPointF) -> bool:
        handle = self._rotation_handle_center(bounds)
        return math.hypot(pos.x() - handle.x(), pos.y() - handle.y()) <= 10.0

    def _cursor_for_handle(self, handle):
        if handle == "rotate":
            return Qt.CursorShape.PointingHandCursor
        if handle == "scale":
            return Qt.CursorShape.SizeFDiagCursor
        if handle in ("edge_left", "edge_right"):
            return Qt.CursorShape.SizeHorCursor
        if handle in ("edge_top", "edge_bottom"):
            return Qt.CursorShape.SizeVerCursor
        if handle in ("tl", "br"):
            return Qt.CursorShape.SizeFDiagCursor
        if handle in ("tr", "bl"):
            return Qt.CursorShape.SizeBDiagCursor
        return Qt.CursorShape.SizeAllCursor

    def _preview_annotation_transform(self, pos: QPointF):
        page_rect = self.page_rects.get(self._drag_page, QRectF())
        if page_rect.isEmpty():
            return
        original = self._drag_original_rect
        raw_pos = QPointF(pos)
        dx, dy = raw_pos.x() - self._drag_start.x(), raw_pos.y() - self._drag_start.y()
        if self._drag_kind == "rotate":
            # Do not clamp the pointer to page bounds: rotation is measured around
            # the object center in canvas coordinates and must remain continuous
            # even when the cursor travels outside the page edge.
            pos = raw_pos
            center = self._drag_rotation_center
            current_angle = math.degrees(math.atan2(pos.y() - center.y(), pos.x() - center.x()))
            delta = current_angle - self._drag_rotation_start_angle
            while delta > 180:
                delta -= 360
            while delta < -180:
                delta += 360
            if self._drag_rotation_step > 1.0:
                delta = round(delta / self._drag_rotation_step) * self._drag_rotation_step
            self._drag_rotation_delta = delta
        elif self._drag_kind == "move":
            # Keep the cursor attached to the exact point grabbed on the object.
            # A single object can be dropped on another visible page. A group stays
            # together on its source page and is clamped as one bounding unit.
            pos = raw_pos
            x = pos.x() - self._drag_pointer_offset.x()
            y = pos.y() - self._drag_pointer_offset.y()
            target_page, target_rect = self._page_at(pos)
            effective_pos = QPointF(pos)
            if self._drag_group_items:
                dx_group, dy_group = dx, dy
                group_pages = {int(item[0]) for item in self._drag_group_items}
                if len(group_pages) == 1:
                    union = QRectF(self._drag_group_items[0][2])
                    for _page_index, _xref, item_rect in self._drag_group_items[1:]:
                        union = union.united(QRectF(item_rect))
                    dx_group = min(max(dx_group, page_rect.left()-union.left()), page_rect.right()-union.right())
                    dy_group = min(max(dy_group, page_rect.top()-union.top()), page_rect.bottom()-union.bottom())
                self._drag_group_delta = QPointF(dx_group, dy_group)
                self._drag_preview_rect = original.translated(dx_group, dy_group)
                self._drag_target_page = self._drag_page
                self._drag_target_display_rect = QRectF(page_rect)
            else:
                target_display = QRectF(target_rect) if target_page >= 0 else QRectF()
                # In page-at-a-time mode, allow dropping just beyond the top/bottom
                # edge to send the object to the adjacent page. The target page is
                # represented by a virtual rectangle at its natural place in the
                # continuous sequence, without enabling continuous Scroll mode.
                if target_page < 0 and not self.tab.scroll_mode:
                    current_index = int(self._drag_page)
                    gap = 24.0
                    source_scale = float(self.page_scales.get(current_index, 1.0))
                    if self.tab.book_mode:
                        # Only the current spread is visible when Book is on and
                        # Scroll is off. Allow an edge-drop to the matching page in
                        # the previous/next spread (same left/right column).
                        first = (current_index // 2) * 2
                        spread_rects = [self.page_rects[i] for i in (first, first+1)
                                        if i in self.page_rects]
                        row_top = min((r.top() for r in spread_rects), default=page_rect.top())
                        row_bottom = max((r.bottom() for r in spread_rects), default=page_rect.bottom())
                        direction = -1 if pos.y() < row_top else (1 if pos.y() > row_bottom else 0)
                        candidate = current_index + direction*2
                    else:
                        row_top, row_bottom = page_rect.top(), page_rect.bottom()
                        direction = -1 if pos.y() < row_top else (1 if pos.y() > row_bottom else 0)
                        candidate = current_index + direction
                    if direction and 0 <= candidate < len(self.tab.page_sizes):
                        target_w = max(1.0, float(self.tab.page_sizes[candidate][0]) * source_scale)
                        target_h = max(1.0, float(self.tab.page_sizes[candidate][1]) * source_scale)
                        target_x = page_rect.center().x() - target_w/2.0
                        if self.tab.book_mode:
                            sibling = candidate + 1 if candidate % 2 == 0 else candidate - 1
                            sibling_h = (float(self.tab.page_sizes[sibling][1]) * source_scale
                                         if 0 <= sibling < len(self.tab.page_sizes) else target_h)
                            target_row_h = max(target_h, sibling_h)
                            vertical_offset = (target_row_h - target_h) / 2.0
                            if direction < 0:
                                target_row_top = row_top - target_row_h - gap
                                target_y = target_row_top + vertical_offset
                                pointer_shift = -gap - vertical_offset
                            else:
                                target_row_top = row_bottom + gap
                                target_y = target_row_top + vertical_offset
                                pointer_shift = gap + vertical_offset
                        else:
                            target_y = (row_top - target_h - gap) if direction < 0 else (row_bottom + gap)
                            pointer_shift = -gap if direction < 0 else gap
                        target_display = QRectF(target_x, target_y, target_w, target_h)
                        target_page = candidate
                        effective_pos = QPointF(pos.x(), pos.y() + pointer_shift)
                if target_page >= 0 and not target_display.isEmpty():
                    x = effective_pos.x() - self._drag_pointer_offset.x()
                    y = effective_pos.y() - self._drag_pointer_offset.y()
                    x = min(max(x, target_display.left()), max(target_display.left(), target_display.right()-original.width()))
                    y = min(max(y, target_display.top()), max(target_display.top(), target_display.bottom()-original.height()))
                    self._drag_target_page = target_page
                    self._drag_target_display_rect = QRectF(target_display)
                else:
                    self._drag_target_page = -1
                    self._drag_target_display_rect = QRectF()
                    x = effective_pos.x() - self._drag_pointer_offset.x()
                    y = effective_pos.y() - self._drag_pointer_offset.y()
                self._drag_preview_rect = QRectF(x, y, original.width(), original.height())
                self._drag_group_delta = QPointF(dx, dy)
        elif (self._drag_handle.startswith("p") or self._drag_handle == "scale"
              or self._drag_handle.startswith("edge_")):
            # All pointer movement is expressed in the visible page's own 2-D
            # coordinate plane. Clamp only to the rendered page rectangle; never
            # mix unrotated PDF X/Y with rotated canvas X/Y.
            pos = QPointF(min(max(raw_pos.x(), page_rect.left()), page_rect.right()),
                          min(max(raw_pos.y(), page_rect.top()), page_rect.bottom()))
            anchor = self._drag_control_anchor
            start = self._drag_control_start
            mode = self._drag_control_mode
            if mode == "scale":
                # Uniformly scale the complete annotation around its own center.
                # The page and pointer are both in canvas coordinates here; the
                # commit path remaps the full geometry through the same page matrix.
                base_distance = max(8.0, math.hypot(start.x()-anchor.x(), start.y()-anchor.y()))
                factor = max(0.05, min(20.0, math.hypot(pos.x()-anchor.x(), pos.y()-anchor.y()) / base_distance))
                half_w = max(1.0, original.width()/2.0)
                half_h = max(1.0, original.height()/2.0)
                max_factor = min(
                    (anchor.x()-page_rect.left())/half_w,
                    (page_rect.right()-anchor.x())/half_w,
                    (anchor.y()-page_rect.top())/half_h,
                    (page_rect.bottom()-anchor.y())/half_h,
                )
                factor = min(factor, max(0.05, max_factor))
                new_w, new_h = original.width()*factor, original.height()*factor
                self._drag_preview_rect = QRectF(anchor.x()-new_w/2.0, anchor.y()-new_h/2.0, new_w, new_h)
            elif mode == "vertex":
                # Endpoint/corner grips now move the selected vertex directly.
                # Other vertices remain stationary instead of being stretched
                # according to the annotation's axis-aligned bounding rectangle.
                self._drag_control_preview_pos = QPointF(pos)
                preview_geometry = self._geometry_with_vertex_preview(self._drag_control_geometry or {})
                self._drag_preview_rect = QRectF(preview_geometry.get("bounds", original))
            elif mode == "edge":
                # A mid-side grip moves only that side, perpendicular to its edge.
                # The opposite side stays fixed, so squares naturally become rectangles.
                side = str((self._drag_control_meta or {}).get("side") or "")
                left, top = original.left(), original.top()
                right, bottom = original.right(), original.bottom()
                if side == "top":
                    top = min(max(pos.y(), page_rect.top()), bottom - 14.0)
                elif side == "bottom":
                    bottom = max(min(pos.y(), page_rect.bottom()), top + 14.0)
                elif side == "left":
                    left = min(max(pos.x(), page_rect.left()), right - 14.0)
                elif side == "right":
                    right = max(min(pos.x(), page_rect.right()), left + 14.0)
                self._drag_preview_rect = QRectF(QPointF(left, top), QPointF(right, bottom)).normalized()
            elif mode == "circle_axis":
                # A circle can become an ellipse by dragging one cardinal side.
                # Horizontal grips alter width only; vertical grips alter height
                # only. The center and the perpendicular diameter remain fixed.
                grip_name = str((self._drag_control_meta or {}).get("name") or self._drag_handle)
                self._drag_preview_rect = _ellipse_resize_preview_rect(
                    original, grip_name, pos, page_rect
                )
            else:
                # Highlight quads are resized as a whole to preserve their
                # word/line geometry; they are not treated as free polygon nodes.
                dx0, dy0 = start.x()-anchor.x(), start.y()-anchor.y()
                sx = (pos.x()-anchor.x()) / dx0 if abs(dx0) > 2.0 else 1.0
                sy = (pos.y()-anchor.y()) / dy0 if abs(dy0) > 2.0 else 1.0
                sx, sy = max(0.05, min(20.0, sx)), max(0.05, min(20.0, sy))
                xs = [anchor.x() + (value-anchor.x())*sx for value in (original.left(), original.right())]
                ys = [anchor.y() + (value-anchor.y())*sy for value in (original.top(), original.bottom())]
                self._drag_preview_rect = QRectF(QPointF(min(xs), min(ys)),
                                                  QPointF(max(xs), max(ys))).normalized()
        else:
            left, top, right, bottom = original.left(), original.top(), original.right(), original.bottom()
            if "l" in self._drag_handle:
                left = min(max(left + dx, page_rect.left()), right - 14)
            if "r" in self._drag_handle:
                right = max(min(right + dx, page_rect.right()), left + 14)
            if "t" in self._drag_handle:
                top = min(max(top + dy, page_rect.top()), bottom - 14)
            if "b" in self._drag_handle:
                bottom = max(min(bottom + dy, page_rect.bottom()), top + 14)
            if self._drag_aspect_ratio > 0 and self._drag_handle:
                # Keep circles circular and recognized squares square while scaling.
                ratio = self._drag_aspect_ratio
                anchor_x = right if "l" in self._drag_handle else left
                anchor_y = bottom if "t" in self._drag_handle else top
                max_w = (anchor_x - page_rect.left()) if "l" in self._drag_handle else (page_rect.right() - anchor_x)
                max_h = (anchor_y - page_rect.top()) if "t" in self._drag_handle else (page_rect.bottom() - anchor_y)
                desired_w, desired_h = abs(right-left), abs(bottom-top)
                new_w = min(desired_w, desired_h * ratio, max_w, max_h * ratio)
                new_h = new_w / max(ratio, 1e-6)
                if "l" in self._drag_handle:
                    left = anchor_x - new_w
                else:
                    right = anchor_x + new_w
                if "t" in self._drag_handle:
                    top = anchor_y - new_h
                else:
                    bottom = anchor_y + new_h
            self._drag_preview_rect = QRectF(QPointF(left, top), QPointF(right, bottom)).normalized()
        self._drag_moved = self._drag_moved or abs(dx) + abs(dy) >= 3
        self.update()

    def _activate_link_cursor(self, pos: QPointF) -> bool:
        try:
            return self._point_over_pdf_link(pos)
        except Exception:
            return False

    def mousePressEvent(self, event):
        doc = getattr(self.tab, "doc", None)
        if doc is None or getattr(doc, "is_closed", True):
            return
        if (event.button() != Qt.MouseButton.RightButton
                and self._context_menu_timer.isActive()):
            # A different click means the user continued interacting instead of
            # choosing a context-menu action; do not pop a stale deferred menu.
            self._context_menu_timer.stop()
            self._pending_context_menu = None
        # In a linked two-pane view, toolbar actions follow the last pane the
        # user interacted with (primary or supplementary).
        try:
            host = self.window()
            setter = getattr(host, "_set_view_target_tab", None)
            if callable(setter):
                setter(self.tab)
        except RuntimeError:
            pass
        if event.button() != Qt.MouseButton.LeftButton:
            return super().mousePressEvent(event)
        pos = self._map_from_zoom_visual(QPointF(event.position()))
        # A fresh pointer action clears an old text-selection overlay. If the drag
        # begins on non-text content, no later move over text can switch modes.
        if self._text_selection_display_rects and not self._text_selecting:
            self._clear_text_selection()
        # The floating Edit / Done / Color pills (and, in Edit mode, the rotate and
        # resize grips) of the selected shape stay usable from ANY tool, e.g. right
        # after drawing a shape with Pen. Such a press is handled like in Select.
        force_select = False
        if self.tab.active_tool != "select" and not self.read_only:
            _fs_index, _fs_rect = self._page_at(pos)
            if _fs_index >= 0 and self._selected_annotation_control_at(_fs_index, pos):
                force_select = True
        if self.tab.active_tool == "pan" and not force_select:
            # Hand mode pans the containing scroll area, including linked/read-only panes.
            scroll_area = self.display_scroll or getattr(self.tab, "scroll", None)
            if isinstance(scroll_area, QAbstractScrollArea):
                self._pan_scroll_area = scroll_area
                self._pan_start_global = event.globalPosition().toPoint()
                self._pan_start_h = int(scroll_area.horizontalScrollBar().value())
                self._pan_start_v = int(scroll_area.verticalScrollBar().value())
                self._pan_active = True
                self.setCursor(Qt.CursorShape.ClosedHandCursor)
                event.accept()
                return
        if self.read_only:
            # Read-only panes can still select a link badge; navigation requires a
            # deliberate double-click, matching the editable canvas behavior.
            link_entry = self._page_link_at(pos)
            if link_entry is not None:
                self.tab.select_page_link(link_entry["identity"])
                self.update()
                event.accept()
                return
            return super().mousePressEvent(event)
        # In Select, annotation/link hit-testing has priority; otherwise a press
        # that starts on an actual selectable PDF word becomes a text selection.
        # Highlight uses the same rule, but a blank/image-started drag remains an
        # area highlight even if the pointer later crosses over text.
        current_tool = str(self.tab.active_tool or "")
        if current_tool in ("select", "highlight") and not force_select:
            text_page_index, text_page_rect = self._page_at(pos)
            if text_page_index >= 0:
                has_annotation = self._annotation_at(text_page_index, pos) is not None
                has_link = self._page_link_at(pos) is not None
                action_hit = (current_tool == "select" and
                              self._selected_annotation_action_at(text_page_index, pos))
                if not action_hit and (current_tool == "highlight" or (not has_annotation and not has_link)):
                    word_entry = self._text_word_at(text_page_index, text_page_rect, pos)
                    if word_entry is not None:
                        self._begin_text_selection(text_page_index, text_page_rect, word_entry)
                        event.accept()
                        return
        if self.tab.active_tool == "select" or force_select:
            index, rect = self._page_at(pos)
            if index >= 0:
                selected_now_pre = list(getattr(self.tab, "selected_annotations", []) or [])
                # The Edit pill floats above the selected annotation and can sit
                # outside the annotation's own hit rectangle; test it first.
                if len(selected_now_pre) == 1 and int(selected_now_pre[0][0]) == int(index):
                    selected_xref_pre = int(selected_now_pre[0][1])
                    selected_page_pre = self.tab.doc.load_page(int(index))
                    selected_annot_pre = next((a for a in (selected_page_pre.annots() or [])
                                               if int(a.xref) == selected_xref_pre), None)
                    if selected_annot_pre is not None:
                        selected_geometry_pre = self._annotation_selection_geometry(index, selected_annot_pre)
                        selected_bounds_pre = selected_geometry_pre.get("bounds") if selected_geometry_pre else None
                        if selected_bounds_pre is not None:
                            selected_type_pre = int((selected_annot_pre.type or (0, ""))[0])
                            text_note_types = (getattr(fitz, "PDF_ANNOT_FREE_TEXT", 2),
                                               getattr(fitz, "PDF_ANNOT_TEXT", 0))
                            if selected_type_pre in text_note_types:
                                content_rect, size_rect, color_rect = self._annotation_text_action_rects(selected_bounds_pre)
                                if content_rect.contains(pos):
                                    self._open_annotation_editor(index, selected_xref_pre)
                                    self.update()
                                    event.accept()
                                    return
                                if self._annotation_edit_mode and color_rect.contains(pos):
                                    self._open_annotation_color_editor(index, selected_xref_pre)
                                    event.accept()
                                    return
                                if size_rect.contains(pos):
                                    self._annotation_edit_mode = not self._annotation_edit_mode
                                    self.update()
                                    event.accept()
                                    return
                            else:
                                if self._annotation_edit_button_rect(selected_bounds_pre).contains(pos):
                                    self._annotation_edit_mode = not self._annotation_edit_mode
                                    self.update()
                                    event.accept()
                                    return
                                if (self._annotation_edit_mode and
                                        self._annotation_color_button_rect(selected_bounds_pre).contains(pos)):
                                    self._open_annotation_color_editor(index, selected_xref_pre)
                                    event.accept()
                                    return
                hit = self._annotation_at(index, pos)
                if hit is not None:
                    xref, bounds, _label, geometry = hit
                    selected_now = list(getattr(self.tab, "selected_annotations", []) or [])
                    item = (int(index), int(xref))
                    was_selected = item in selected_now
                    modifiers = event.modifiers()
                    ctrl_add = bool(modifiers & (Qt.KeyboardModifier.ControlModifier | Qt.KeyboardModifier.ShiftModifier))
                    if ctrl_add:
                        self._annotation_edit_mode = False
                        if item in selected_now:
                            remaining = [entry for entry in selected_now if entry != item]
                            self.tab.set_annotation_selection(remaining)
                        else:
                            self.tab.select_annotation(index, xref, additive=True)
                        self.setCursor(Qt.CursorShape.ArrowCursor)
                        self.update()
                        event.accept()
                        return
                    if (index, xref) not in selected_now:
                        self._annotation_edit_mode = False
                        self.tab.select_annotation(index, xref)
                        self.setCursor(Qt.CursorShape.ArrowCursor)
                        self.update()
                        event.accept()
                        return
                    if not self._annotation_edit_mode or len(selected_now) != 1:
                        # Select mode is selection-only. Editing/moving/resizing is
                        # explicitly unlocked by the Edit pill on a single object.
                        self.setCursor(Qt.CursorShape.ArrowCursor)
                        self.update()
                        event.accept()
                        return
                        return
                    if not was_selected:
                        self.tab.select_annotation(index, xref)
                    else:
                        # Make the clicked item the active member while retaining
                        # the current multi-selection.
                        self.tab.select_annotation(index, xref, additive=True)
                    selected_items = list(getattr(self.tab, "selected_annotations", []) or [item])
                    group_items = list(selected_items)
                    is_group_drag = was_selected and len(group_items) > 1
                    if is_group_drag:
                        resolved_group = []
                        for group_page_index, group_xref in group_items:
                            group_page = self.tab.doc.load_page(int(group_page_index))
                            group_annot = next((a for a in (group_page.annots() or [])
                                                if int(a.xref) == int(group_xref)), None)
                            if group_annot is not None:
                                group_geometry = self._annotation_selection_geometry(
                                    group_page_index, group_annot, page=group_page)
                                resolved_group.append((int(group_page_index), int(group_xref),
                                                       QRectF(group_geometry["bounds"])))
                        group_items = resolved_group
                    try:
                        _hit_page = self.tab.doc.load_page(int(index))
                        _hit_annot = next((a for a in (_hit_page.annots() or []) if int(a.xref) == int(xref)), None)
                        _hit_content = str(((_hit_annot.info or {}).get("content") if _hit_annot else "") or "").lower()
                        _is_point = "pen shape · point" in _hit_content or "pen shape - point" in _hit_content
                    except Exception:
                        _is_point = False
                    rotate_hit = self._rotation_handle_at(bounds, pos) if was_selected and not is_group_drag and not _is_point else False
                    handle = self._resize_handle_at(bounds, pos, geometry) if was_selected and not is_group_drag and not rotate_hit else ""
                    # Points have only the dedicated uniform-scale grip (no
                    # cardinal resize nodes and no rotation grip). Do not turn
                    # that grip into a move drag: it must resize the dot itself.
                    if _is_point and handle != "scale":
                        handle = ""
                    self._dragging_annotation = True
                    self._drag_page = index
                    self._drag_xref = xref
                    self._drag_kind = "rotate" if rotate_hit else ("resize" if handle else "move")
                    self._drag_handle = "rotate" if rotate_hit else handle
                    self._drag_start = pos
                    self._drag_original_rect = QRectF(bounds)
                    self._drag_preview_rect = QRectF(bounds)
                    self._drag_rotation_center = bounds.center()
                    self._drag_rotation_start_angle = math.degrees(math.atan2(pos.y() - bounds.center().y(), pos.x() - bounds.center().x())) if rotate_hit else 0.0
                    self._drag_rotation_delta = 0.0
                    self._drag_rotation_step = 1.0
                    self._drag_aspect_ratio = 0.0
                    self._drag_control_start = QPointF()
                    self._drag_control_anchor = QPointF()
                    self._drag_control_mode = ""
                    self._drag_control_meta = {}
                    self._drag_control_preview_pos = QPointF()
                    self._drag_control_geometry = geometry
                    self._drag_pointer_offset = QPointF(pos.x()-bounds.left(), pos.y()-bounds.top())
                    self._drag_target_page = int(index)
                    self._drag_target_display_rect = QRectF(rect)
                    self._drag_group_items = list(group_items) if is_group_drag else []
                    self._drag_group_delta = QPointF()
                    if handle and (handle.startswith("p") or handle == "scale" or handle.startswith("edge_")):
                        selected_grip = next((item for item in geometry.get("handles", []) if item.get("name") == handle), None)
                        if selected_grip is not None:
                            self._drag_control_start = QPointF(selected_grip.get("point", QPointF()))
                            self._drag_control_anchor = QPointF(selected_grip.get("anchor", bounds.center()))
                            self._drag_control_mode = str(selected_grip.get("mode") or "vertex")
                            self._drag_control_meta = dict(selected_grip)
                            self._drag_control_preview_pos = QPointF(self._drag_control_start)
                    if was_selected and not is_group_drag and (handle or rotate_hit):
                        try:
                            shape_page = self.tab.doc.load_page(index)
                            selected_annot = next((a for a in (shape_page.annots() or []) if int(a.xref) == int(xref)), None)
                            if selected_annot is not None:
                                shape_code = int((selected_annot.type or (0, ""))[0])
                                shape_info = dict(selected_annot.info or {})
                                shape_name = str(shape_info.get("content") or "").lower()
                                if rotate_hit and shape_code == getattr(fitz, "PDF_ANNOT_FREE_TEXT", 2):
                                    self._drag_rotation_step = 90.0
                                if handle and not str(handle).startswith(("edge_", "p")) and (
                                        shape_code == getattr(fitz, "PDF_ANNOT_SQUARE", 4) and
                                        ("square" in shape_name or abs(bounds.width()-bounds.height()) <= max(4.0, bounds.width()*0.08))):
                                    self._drag_aspect_ratio = bounds.width() / max(bounds.height(), 1.0)
                        except Exception:
                            self._drag_aspect_ratio = 0.0
                    self._drag_moved = False
                    self.setCursor(self._cursor_for_handle(self._drag_handle) if self._drag_handle else Qt.CursorShape.SizeAllCursor)
                    self.update()
                    return

                # Empty-space drag starts a Windows-style selection marquee.
                self._annotation_edit_mode = False
                self._marquee_active = True
                self._marquee_start = QPointF(pos)
                self._marquee_current = QPointF(pos)
                self._marquee_page = int(index)
                self._marquee_additive = bool(event.modifiers() & (Qt.KeyboardModifier.ControlModifier | Qt.KeyboardModifier.ShiftModifier))
                current_selection = list(getattr(self.tab, "selected_annotations", []) or [])
                self._marquee_previous = current_selection if self._marquee_additive else []
                self._marquee_restore_selection = current_selection
                if not self._marquee_additive:
                    self.tab.clear_annotation_selection()
                self.setCursor(Qt.CursorShape.CrossCursor)
                self.update()
                event.accept()
                return
            link_entry = self._page_link_at(pos)
            if link_entry is not None:
                self.tab.select_page_link(link_entry["identity"])
                self.update()
                event.accept()
                return
            # Empty canvas-space drag also starts a marquee. This mirrors the
            # Windows Explorer gesture and allows a selection box to begin in the
            # page margins before enclosing annotations on one or more visible pages.
            self._marquee_active = True
            self._marquee_start = QPointF(pos)
            self._marquee_current = QPointF(pos)
            self._marquee_page = -1
            self._marquee_additive = bool(event.modifiers() & (Qt.KeyboardModifier.ControlModifier | Qt.KeyboardModifier.ShiftModifier))
            current_selection = list(getattr(self.tab, "selected_annotations", []) or [])
            self._marquee_previous = current_selection if self._marquee_additive else []
            self._marquee_restore_selection = current_selection
            if not self._marquee_additive:
                self.tab.clear_annotation_selection()
            self.setCursor(Qt.CursorShape.CrossCursor)
            self.update()
            event.accept()
            return
        # Starting a new annotation intentionally clears the previous selection.
        self._annotation_edit_mode = False
        self.tab.clear_annotation_selection()
        index, rect = self._page_at(pos)
        if index < 0:
            return
        self._drawing = True
        self._draw_page = index
        self._draw_start = pos
        self._draw_current = pos
        self._draw_points = [pos]
        self.setCursor(Qt.CursorShape.CrossCursor)
        self.update()

    def mouseDoubleClickEvent(self, event):
        if event.button() == Qt.MouseButton.RightButton:
            doc = getattr(self.tab, "doc", None)
            pos = self._map_from_zoom_visual(QPointF(event.position()))
            page_index, _page_rect = self._page_at(pos)
            if (not self.read_only and doc is not None
                    and not getattr(doc, "is_closed", True) and page_index >= 0):
                # Cancel the deferred single-right-click menu and suppress the
                # context event that some platforms send after the second release.
                self._context_menu_timer.stop()
                self._pending_context_menu = None
                self._suppress_context_menu = True
                self._suppress_context_menu_timer.start(
                    max(250, QApplication.doubleClickInterval())
                )

                # This gesture is intentionally a two-state toggle: Pen on the
                # first right double-click, Select on the next, regardless of
                # which other annotation tool was active beforehand.
                next_tool = "select" if self.tab.active_tool == "pen" else "pen"
                try:
                    host = self.window()
                    setter = getattr(host, "_set_view_target_tab", None)
                    if callable(setter):
                        setter(self.tab)
                    tool_setter = getattr(host, "_set_tool", None)
                    if callable(tool_setter):
                        tool_setter(next_tool, quiet=True)
                    else:
                        self.tab.set_tool(next_tool)
                except (RuntimeError, AttributeError):
                    self.tab.set_tool(next_tool)
                self.update()
                event.accept()
                return

        if event.button() == Qt.MouseButton.LeftButton:
            # Qt sends a double-click as a second press event. Clear any stale
            # drag preview from the preceding single-click so regularization or
            # adding an arrowhead cannot be followed by an unintended move.
            self._dragging_annotation = False
            self._drag_page = -1
            self._drag_xref = 0
            self._drag_handle = ""
            self._drag_control_mode = ""
            self._drag_control_meta = {}
            self._drag_control_geometry = None
            self._drag_group_items = []
            pos = self._map_from_zoom_visual(QPointF(event.position()))
            entry = self._page_link_at(pos)
            if entry is not None:
                self.tab.select_page_link(entry["identity"])
                self._open_page_link(entry)
                self.update()
                event.accept()
                return
            if not self.read_only and self.tab.active_tool == "select":
                index, _page_rect = self._page_at(pos)
                if index >= 0:
                    hit = self._annotation_at(index, pos)
                    if hit is not None:
                        xref = int(hit[0])
                        self.tab.select_annotation(index, xref)
                        self._annotation_edit_mode = False
                        page_obj = self.tab.doc.load_page(int(index))
                        annot_obj = next((a for a in (page_obj.annots() or []) if int(a.xref) == xref), None)
                        annot_type = int((annot_obj.type or (0, ""))[0]) if annot_obj else -1
                        if annot_type in (getattr(fitz, "PDF_ANNOT_FREE_TEXT", 2), getattr(fitz, "PDF_ANNOT_TEXT", 0)):
                            self._open_annotation_editor(index, xref)
                            self.update()
                            event.accept()
                            return
                        self.tab.normalize_annotation_shape(index, xref, click_pos=pos, canvas=self)
                        self.update()
                        event.accept()
                        return
        return super().mouseDoubleClickEvent(event)

    def mouseMoveEvent(self, event):
        doc = getattr(self.tab, "doc", None)
        if doc is None or getattr(doc, "is_closed", True):
            return
        pos = self._map_from_zoom_visual(QPointF(event.position()))
        if self._text_selecting:
            self._update_text_selection(pos)
            event.accept()
            return
        if self._pan_active:
            scroll_area = self._pan_scroll_area
            if scroll_area is None:
                self._pan_active = False
            else:
                delta = event.globalPosition().toPoint() - self._pan_start_global
                scroll_area.horizontalScrollBar().setValue(self._pan_start_h - delta.x())
                scroll_area.verticalScrollBar().setValue(self._pan_start_v - delta.y())
                self.setCursor(Qt.CursorShape.ClosedHandCursor)
                event.accept()
                return
        if self.tab.active_tool == "pan":
            self.setCursor(Qt.CursorShape.OpenHandCursor)
            return super().mouseMoveEvent(event)
        if self.read_only:
            self.setCursor(Qt.CursorShape.PointingHandCursor if self._activate_link_cursor(pos) else Qt.CursorShape.ArrowCursor)
            return super().mouseMoveEvent(event)
        if self._marquee_active:
            self._marquee_current = QPointF(pos)
            self.update()
            return
        if self._dragging_annotation:
            self._preview_annotation_transform(pos)
            self.setCursor(self._cursor_for_handle(self._drag_handle) if self._drag_handle else Qt.CursorShape.SizeAllCursor)
            return
        if not self._drawing:
            if self.tab.active_tool != "select":
                _ctl_index, _ctl_rect = self._page_at(pos)
                _ctl = self._selected_annotation_control_at(_ctl_index, pos) if _ctl_index >= 0 else ""
                if _ctl:
                    self.setCursor(Qt.CursorShape.PointingHandCursor if _ctl == "action"
                                   else self._cursor_for_handle(_ctl))
                    return super().mouseMoveEvent(event)
                if self.tab.active_tool not in ("highlight",):
                    self.setCursor(self._tool_default_cursor())
            if self.tab.active_tool in ("select", "highlight"):
                index, page_rect = self._page_at(pos)
                hit = self._annotation_at(index, pos) if index >= 0 else None
                link_hit = self._page_link_at(pos) if index >= 0 else None
                text_hit = self._text_word_at(index, page_rect, pos) if index >= 0 else None
                if text_hit is not None and (self.tab.active_tool == "highlight" or (hit is None and link_hit is None)):
                    self.setCursor(Qt.CursorShape.IBeamCursor)
                elif self.tab.active_tool == "highlight":
                    self.setCursor(Qt.CursorShape.CrossCursor)
                elif hit is not None:
                    xref, bounds, _label, geometry = hit
                    current = self.tab.selected_annotation == (index, xref)
                    is_point = "pen shape · point" in str(_label).lower() or "pen shape - point" in str(_label).lower()
                    if current and self._annotation_edit_mode:
                        if not is_point and self._rotation_handle_at(bounds, pos):
                            handle = "rotate"
                        else:
                            handle = self._resize_handle_at(bounds, pos, geometry)
                        self.setCursor(self._cursor_for_handle(handle) if handle else Qt.CursorShape.SizeAllCursor)
                    else:
                        # In Select mode a normal hover never advertises that an
                        # object can be moved; the Edit pill explicitly unlocks that.
                        self.setCursor(Qt.CursorShape.ArrowCursor)
                elif self._point_over_pdf_link(pos):
                    self.setCursor(Qt.CursorShape.PointingHandCursor)
                else:
                    self.setCursor(Qt.CursorShape.ArrowCursor)
            return super().mouseMoveEvent(event)
        self._draw_current = pos
        if self.tab.active_tool == "pen":
            rect = self.page_rects.get(self._draw_page, QRectF())
            if rect.contains(self._draw_current):
                self._draw_points.append(self._draw_current)
        self.update()

    def mouseReleaseEvent(self, event):
        doc = getattr(self.tab, "doc", None)
        if doc is None or getattr(doc, "is_closed", True):
            self._drawing = False
            self._dragging_annotation = False
            return
        if event.button() != Qt.MouseButton.LeftButton:
            return super().mouseReleaseEvent(event)
        if self._pan_active:
            self._pan_active = False
            self._pan_scroll_area = None
            self.setCursor(Qt.CursorShape.OpenHandCursor if self.tab.active_tool == "pan" else Qt.CursorShape.ArrowCursor)
            event.accept()
            return
        if self._text_selecting:
            self._update_text_selection(self._map_from_zoom_visual(QPointF(event.position())))
            self._finish_text_selection(event.globalPosition().toPoint())
            event.accept()
            return
        if self._marquee_active:
            self._marquee_current = self._map_from_zoom_visual(QPointF(event.position()))
            start_point = QPointF(self._marquee_start)
            end_point = QPointF(self._marquee_current)
            marquee = QRectF(start_point, end_point).normalized()
            contained_mode = end_point.x() >= start_point.x()
            chosen = list(self._marquee_previous) if self._marquee_additive else []
            if marquee.width() >= 3.0 or marquee.height() >= 3.0:
                for page_index, visible_page_rect in list(self.page_rects.items()):
                    if not marquee.intersects(visible_page_rect):
                        continue
                    try:
                        page = self.tab.doc.load_page(int(page_index))
                        for annot in list(page.annots() or []):
                            geometry = self._annotation_selection_geometry(page_index, annot, page=page)
                            bounds = geometry["bounds"]
                            matches = marquee.contains(bounds) if contained_mode else marquee.intersects(bounds)
                            item = (int(page_index), int(annot.xref))
                            if matches and item not in chosen:
                                chosen.append(item)
                    except Exception:
                        continue
            self._marquee_active = False
            self._marquee_page = -1
            self._marquee_previous = []
            self._marquee_restore_selection = []
            self.tab.set_annotation_selection(chosen)
            self.setCursor(Qt.CursorShape.ArrowCursor)
            self.update()
            event.accept()
            return
        if self._dragging_annotation:
            # Consume the release coordinates as well; some platforms do not
            # deliver a final mouse-move event at the exact drop location.
            self._preview_annotation_transform(self._map_from_zoom_visual(QPointF(event.position())))
            page_index, xref = self._drag_page, self._drag_xref
            new_bounds = QRectF(self._drag_preview_rect)
            moved = self._drag_moved
            drag_kind = self._drag_kind
            rotation_delta = float(self._drag_rotation_delta)
            target_page = int(self._drag_target_page)
            target_display_rect = QRectF(self._drag_target_display_rect)
            group_items = list(self._drag_group_items)
            group_delta = QPointF(self._drag_group_delta)
            original_bounds = QRectF(self._drag_original_rect)
            control_mode = str(self._drag_control_mode or "")
            control_meta = dict(self._drag_control_meta or {})
            control_target = QPointF(self._drag_control_preview_pos)
            self._dragging_annotation = False
            self._drag_page = -1
            self._drag_xref = 0
            self._drag_handle = ""
            self._drag_kind = "move"
            self._drag_rotation_step = 1.0
            self._drag_aspect_ratio = 0.0
            self._drag_control_mode = ""
            self._drag_control_meta = {}
            self._drag_control_preview_pos = QPointF()
            self._drag_control_geometry = None
            self._drag_target_page = -1
            self._drag_target_display_rect = QRectF()
            self._drag_group_items = []
            self._drag_group_delta = QPointF()
            self.setCursor(self._tool_default_cursor())
            if moved:
                if drag_kind == "rotate":
                    self.tab.rotate_annotation(page_index, xref, rotation_delta, canvas=self)
                elif group_items:
                    self.tab.transform_annotations_group(group_items, group_delta, canvas=self)
                elif target_page < 0:
                    # Drop on the page margins cancels the drag safely.
                    pass
                elif target_page != page_index:
                    self.tab.move_annotation_to_page(page_index, xref, target_page, new_bounds,
                                                    canvas=self, target_display_rect=target_display_rect)
                elif drag_kind == "resize" and control_mode == "vertex":
                    self.tab.transform_annotation_vertex(page_index, xref, control_meta,
                                                          control_target, canvas=self)
                else:
                    self.tab.transform_annotation(page_index, xref, original_bounds, new_bounds, canvas=self)
            self.update()
            return
        if not self._drawing:
            return super().mouseReleaseEvent(event)
        self._draw_current = self._map_from_zoom_visual(QPointF(event.position()))
        tool = self.tab.active_tool
        index = self._draw_page
        page_rect = self.page_rects.get(index, QRectF())
        selection = QRectF(self._draw_start, self._draw_current).normalized().intersected(page_rect)
        self._drawing = False
        self.setCursor(Qt.CursorShape.ArrowCursor if tool == "select" else Qt.CursorShape.CrossCursor)
        try:
            if tool in ("ai_select", "translate_select") and selection.width() > 10 and selection.height() > 10:
                # Render the exact selected area; works with text, charts, scans, and handwriting.
                clip = self._rect_to_pdf(index, page_rect, selection)
                page = self.tab.doc.load_page(index)
                scale = min(2.0, 1700.0 / max(float(clip.width), float(clip.height), 1.0))
                pix = page.get_pixmap(matrix=fitz.Matrix(scale, scale), clip=clip, alpha=False)
                image = Image.frombytes("RGB", (pix.width, pix.height), pix.samples)
                image.thumbnail((1700, 1700), Image.Resampling.LANCZOS)
                buffer = io.BytesIO()
                image.save(buffer, format="JPEG", quality=90, optimize=True)
                if tool == "translate_select":
                    # Read selectable text from the SAME in-memory page that produced
                    # the crop image. Re-opening tab.path in the worker is incorrect
                    # after an unsaved Rotate action: disk coordinates still describe
                    # the old orientation and can point to a completely different area.
                    try:
                        selected_text = str(page.get_text("text", clip=clip) or "").strip()
                    except Exception:
                        selected_text = ""
                    self.tab.translateRegionSelected.emit(
                        index, buffer.getvalue(),
                        (float(clip.x0), float(clip.y0), float(clip.x1), float(clip.y1)),
                        selected_text,
                    )
                else:
                    self.tab.aiRegionSelected.emit(index, buffer.getvalue())
                self.tab.set_tool("select")
                # A supplementary tab owns its own tool state. Also reset the
                # primary tab when its linked secondary pane completed a crop,
                # then refresh the shared toolbar against the pane just used.
                try:
                    host = self.window()
                    primary = host.active_tab() if callable(getattr(host, "active_tab", None)) else None
                    if primary is not None and getattr(primary, "_linked_view_secondary", None) is self.tab:
                        primary.active_tool = "select"
                    setter = getattr(host, "_set_view_target_tab", None)
                    if callable(setter):
                        setter(self.tab)
                    help_setter = getattr(host, "_show_selected_tool_context_help", None)
                    if callable(help_setter):
                        help_setter("select")
                except (RuntimeError, AttributeError):
                    pass
            elif tool == "highlight" and selection.width() > 3 and selection.height() > 3:
                # The drag began on non-text content, so preserve area/image markup.
                # Text highlighting is handled only by the anchored word-selection path.
                self.tab.add_area_highlight(index, self._rect_to_pdf(index, page_rect, selection))
            elif tool == "tag" and selection.width() > 8 and selection.height() > 8:
                host = self.window()
                selected_tag = getattr(host, "_selected_region_tag", None)
                tag_name, tag_color = selected_tag(self.tab) if callable(selected_tag) else ("", "#f2bd55")
                if not tag_name:
                    editor = getattr(host, "open_tag_manager", None)
                    if callable(editor):
                        editor(self.tab)
                        tag_name, tag_color = selected_tag(self.tab) if callable(selected_tag) else ("", "#f2bd55")
                if tag_name:
                    self.tab.add_tag_region(index, self._rect_to_pdf(index, page_rect, selection), tag_name, tag_color)
            elif tool == "pen" and (len(self._draw_points) < 2 or sum(
                    math.hypot(b.x()-a.x(), b.y()-a.y())
                    for a, b in zip(self._draw_points, self._draw_points[1:])) < 4.0):
                # A click (or unavoidable sub-4px hand jitter) places a native point.
                self.tab.add_point(index, self._display_to_pdf(index, page_rect, self._draw_start))
            elif tool == "pen" and len(self._draw_points) >= 2:
                display_points = list(self._draw_points)
                if not display_points or math.hypot(self._draw_current.x() - display_points[-1].x(),
                                                     self._draw_current.y() - display_points[-1].y()) > 0.5:
                    if page_rect.contains(self._draw_current):
                        display_points.append(self._draw_current)
                pdf_points = self._map_path(index, page_rect, display_points)
                recognized = _recognize_pen_shape(pdf_points)
                if recognized:
                    self.tab.add_recognized_shape(index, recognized)
                else:
                    self.tab.add_ink(index, pdf_points)
            elif tool == "note":
                answer, ok = QInputDialog.getMultiLineText(self, "Add note", "Write your note:")
                if ok and answer.strip():
                    self.tab.add_note(index, self._display_to_pdf(index, page_rect, self._draw_start), answer.strip())
            elif tool == "text":
                if selection.width() < 45 or selection.height() < 24:
                    x = min(max(self._draw_start.x(), page_rect.left() + 4), page_rect.right() - 180)
                    y = min(max(self._draw_start.y(), page_rect.top() + 4), page_rect.bottom() - 58)
                    selection = QRectF(x, y, min(180, page_rect.width() - 8), min(54, page_rect.height() - 8))
                answer, ok = QInputDialog.getMultiLineText(self, "Add text box", "Text to place on the page:")
                if ok and answer.strip():
                    self.tab.add_text(index, self._rect_to_pdf(index, page_rect, selection), answer.strip())
            elif tool == "link" and selection.width() > 8 and selection.height() > 8:
                target, ok = QInputDialog.getInt(self, "Link pages", "Open page number:",
                                                  min(index + 2, self.tab.page_count), 1, self.tab.page_count)
                if ok:
                    self.tab.add_page_link(index, self._rect_to_pdf(index, page_rect, selection), target - 1)
        except Exception as exc:
            QMessageBox.warning(self, APP_NAME, f"Could not add annotation:\n{exc}")
        self._draw_points = []
        self.update()

    def _clear_context_menu_suppression(self):
        self._suppress_context_menu = False

    def _show_pending_context_menu(self):
        pending = self._pending_context_menu
        self._pending_context_menu = None
        if pending is None or self.read_only:
            return
        local_pos, global_pos = pending
        self._show_context_menu_at(QPointF(local_pos), global_pos)

    def contextMenuEvent(self, event):
        if self.read_only:
            return super().contextMenuEvent(event)
        pos = QPointF(event.pos())
        index, _page_rect = self._page_at(pos)
        if index < 0:
            return super().contextMenuEvent(event)

        # A right double-click is handled in mouseDoubleClickEvent. Do not let
        # the second release reopen a context menu after the tool has toggled.
        if (event.reason() == QContextMenuEvent.Reason.Mouse
                and self._suppress_context_menu):
            self._suppress_context_menu = False
            self._suppress_context_menu_timer.stop()
            event.accept()
            return

        if event.reason() == QContextMenuEvent.Reason.Mouse:
            # Only defer when this spot would actually show one of our custom
            # context menus. Empty-page right clicks with no paste target retain
            # their previous no-menu behavior and need no delay.
            hit = self._annotation_at(index, pos)
            has_link = hit is None and self._page_link_at(pos) is not None
            has_paste = hit is None and not has_link and isinstance(_ANNOTATION_CLIPBOARD, dict)
            if hit is not None or has_link or has_paste:
                # Windows may request the context menu after the first right-button
                # release, before Qt delivers the double-click event. Wait one native
                # double-click interval so a double-click can take precedence.
                self._pending_context_menu = (QPoint(event.pos()), QPoint(event.globalPos()))
                self._context_menu_timer.start(QApplication.doubleClickInterval() + 50)
                event.accept()
                return
            return super().contextMenuEvent(event)

        # Keyboard/context-menu-key requests should not wait for a mouse gesture.
        self._show_context_menu_at(pos, QPoint(event.globalPos()))
        event.accept()

    def _show_context_menu_at(self, pos: QPointF, global_pos: QPoint):
        if self.read_only:
            return
        index, page_rect = self._page_at(pos)
        if index < 0:
            return
        hit = self._annotation_at(index, pos)
        if hit is None:
            link_entry = self._page_link_at(pos)
            if link_entry is not None:
                self.tab.select_page_link(link_entry["identity"])
                menu = QMenu(self)
                delete_link_action = menu.addAction(make_icon("delete", "#e79aa5", 16), "Delete link")
                chosen = menu.exec(global_pos)
                if chosen is delete_link_action:
                    self.tab.delete_selected_annotation()
                return
            if not isinstance(_ANNOTATION_CLIPBOARD, dict):
                return
            menu = QMenu(self)
            paste_action = menu.addAction(make_icon("copy", "#8ec8ff", 16), "Paste annotation here")
            chosen = menu.exec(global_pos)
            if chosen is paste_action:
                target_point = self._display_to_pdf(index, page_rect, pos)
                self.tab.paste_annotation(index, target_point)
            return

        xref, _bounds, raw_label = hit[:3]
        self.tab.select_annotation(index, xref)
        menu = QMenu(self)
        label = str(raw_label or "PDF annotation").strip().replace("\n", " ")
        if len(label) > 44:
            label = label[:41] + "…"
        heading = menu.addAction(label or "PDF annotation")
        heading.setEnabled(False)
        menu.addSeparator()
        copy_action = menu.addAction(make_icon("copy", "#8ec8ff", 16), "Copy annotation")
        remove_action = menu.addAction(make_icon("delete", "#e79aa5", 16), "Delete annotation  ·  Delete")
        chosen = menu.exec(global_pos)
        if chosen is copy_action:
            self.tab.copy_annotation(index, xref)
        elif chosen is remove_action:
            self.tab.delete_selected_annotation()

    def event(self, event):
        if event.type() == QEvent.Type.Gesture:
            pinch = event.gesture(Qt.GestureType.PinchGesture)
            if pinch and pinch.state() == Qt.GestureState.GestureUpdated:
                current_factor = float(pinch.scaleFactor())
                previous_factor = float(pinch.lastScaleFactor())
                factor = current_factor / previous_factor if previous_factor > 0 else 1.0
                factor = max(0.91, min(1.09, factor))
                if abs(factor - 1.0) > 0.001:
                    scroll_area = self.display_scroll or self.tab.scroll
                    anchor = scroll_area.viewport().mapFromGlobal(QCursor.pos())
                    if self.external_zoom_callback is not None:
                        self.external_zoom_callback(factor, anchor)
                    else:
                        self.tab.zoom_by(factor, anchor)
                return True
        if event.type() == QEvent.Type.NativeGesture:
            try:
                if event.gestureType() == Qt.NativeGestureType.ZoomNativeGesture:
                    native_delta = float(event.value())
                    factor = max(0.90, min(1.10, math.exp(native_delta * 0.68)))
                    if abs(factor - 1.0) > 0.001:
                        scroll_area = self.display_scroll or self.tab.scroll
                        anchor = scroll_area.viewport().mapFromGlobal(QCursor.pos())
                        if self.external_zoom_callback is not None:
                            self.external_zoom_callback(factor, anchor)
                        else:
                            self.tab.zoom_by(factor, anchor)
                        return True
            except Exception:
                pass
        return super().event(event)


class PageOverviewGrid(QListWidget):
    """Full-screen page gallery with responsive columns and deterministic navigation."""
    keyActionRequested = pyqtSignal(str)
    metricsChanged = pyqtSignal()

    def __init__(self, parent=None):
        super().__init__(parent)
        self._last_responsive_metrics = None
        self._updating_responsive_metrics = False

    def update_responsive_metrics(self):
        """Fit six or more page tiles across desktop screens without stale item sizes."""
        if self._updating_responsive_metrics:
            return

        viewport_width = max(1, int(self.viewport().width()))
        # QListWidget's viewport is already smaller than the outer window. Reserve
        # the gallery's 5px inner padding on each side and account for inter-item
        # spacing before dividing the width. This prevents a nominal sixth column
        # from falling just outside the viewport (the previous 5-column symptom).
        spacing = max(0, int(self.spacing()))
        usable_width = max(1, viewport_width - 12)
        if usable_width >= 1180:
            columns = max(6, min(12, usable_width // 250))
        else:
            columns = max(1, min(5, usable_width // 230))
        columns = min(columns, max(1, (usable_width + spacing) // 150))
        tile_width = max(140, (usable_width - spacing * (columns - 1)) // columns)

        # The former 270px icon-height limit made portrait pages look narrow even
        # when each column had 240px available. Give the icon enough height to use
        # its natural portrait ratio; QIcon keeps the PDF image aspect ratio intact.
        icon_width = max(112, tile_width - 20)
        icon_height = max(180, int(round(icon_width * 1.50)))
        tile_height = icon_height + 48
        metrics = (tile_width, tile_height, icon_width, icon_height)
        if metrics == self._last_responsive_metrics:
            return

        self._last_responsive_metrics = metrics
        self._updating_responsive_metrics = True
        try:
            cell_size = QSize(tile_width, tile_height)
            self.setGridSize(cell_size)
            self.setIconSize(QSize(icon_width, icon_height))
            # QListWidgetItem.setSizeHint() overrides QListView.setGridSize().
            # Update every existing item whenever the window/viewport is resized.
            for index in range(self.count()):
                item = self.item(index)
                if item is not None:
                    item.setSizeHint(QSize(cell_size))
            self.doItemsLayout()
        finally:
            self._updating_responsive_metrics = False
        self.metricsChanged.emit()

    def resizeEvent(self, event):
        super().resizeEvent(event)
        self.update_responsive_metrics()

    def keyPressEvent(self, event):
        key_actions = {
            Qt.Key.Key_Escape: "escape",
            Qt.Key.Key_Return: "open",
            Qt.Key.Key_Enter: "open",
            Qt.Key.Key_Left: "left",
            Qt.Key.Key_Right: "right",
            Qt.Key.Key_Up: "up",
            Qt.Key.Key_Down: "down",
        }
        action = key_actions.get(event.key())
        if action is not None:
            self.keyActionRequested.emit(action)
            event.accept()
            return
        super().keyPressEvent(event)


class BookSpreadThumbnailList(QListWidget):
    """Thumbnail list with one explicit, exclusive outline for the active book spread."""

    def __init__(self, parent=None):
        super().__init__(parent)
        self._book_spread_selection = False
        self._active_spread_first = 0
        self.setSelectionMode(QAbstractItemView.SelectionMode.SingleSelection)
        # Pixel-based scrolling lets the sidebar follow the active spread smoothly
        # and by the exact amount needed to keep both thumbnails visible.
        self.setVerticalScrollMode(QAbstractItemView.ScrollMode.ScrollPerPixel)

    def set_book_spread_selection(self, enabled: bool):
        enabled = bool(enabled)
        if self._book_spread_selection == enabled:
            return

        self._book_spread_selection = enabled
        if enabled:
            # Book mode draws its own two-page frame. Disable Qt's per-item
            # selection completely; otherwise a stale/current item can remain
            # highlighted separately from the spread frame.
            self.clearSelection()
            self.setSelectionMode(QAbstractItemView.SelectionMode.NoSelection)
        else:
            self.setSelectionMode(QAbstractItemView.SelectionMode.SingleSelection)

        self.viewport().update()

    def set_active_spread(self, first_page_index: int):
        """Set the first zero-based page in the active spread (0, 2, 4, ...)."""
        try:
            first = max(0, int(first_page_index))
        except (TypeError, ValueError):
            first = 0
        first = (first // 2) * 2
        if self.count():
            first = min(first, self.count() - 1)
            first = (first // 2) * 2
        if self._active_spread_first != first:
            self._active_spread_first = first
            self.viewport().update()

    def ensure_active_spread_visible(self):
        """Scroll the thumbnail sidebar just enough to show the complete active spread."""
        if not self._book_spread_selection or self.count() <= 0:
            return

        first_item = self.item(self._active_spread_first)
        if first_item is None:
            return
        last_item = self.item(min(self._active_spread_first + 1, self.count() - 1))
        if last_item is None:
            last_item = first_item

        first_rect = self.visualItemRect(first_item)
        last_rect = self.visualItemRect(last_item)
        if not first_rect.isValid() or not last_rect.isValid():
            return

        spread_rect = first_rect.united(last_rect)
        viewport_height = int(self.viewport().height())
        if viewport_height <= 0:
            return

        # visualItemRect() is viewport-relative. Translate its overflow into
        # a pixel delta for the sidebar's own vertical scrollbar.
        delta = 0
        if spread_rect.height() > viewport_height:
            delta = int(spread_rect.top())
        elif spread_rect.top() < 0:
            delta = int(spread_rect.top())
        elif spread_rect.bottom() > viewport_height:
            delta = int(spread_rect.bottom() - viewport_height)

        if delta:
            bar = self.verticalScrollBar()
            bar.setValue(bar.value() + delta)

        self.viewport().update()

    def paintEvent(self, event):
        super().paintEvent(event)
        if not self._book_spread_selection or self.count() <= 0:
            return

        # Do not use currentRow(): NoSelection mode intentionally has no selected
        # row, and Qt's current index is not the source of truth for a page spread.
        first_row = self._active_spread_first
        first_item = self.item(first_row)
        if first_item is None:
            return
        last_item = self.item(min(first_row + 1, self.count() - 1))
        if last_item is None:
            last_item = first_item

        first_rect = self.visualItemRect(first_item)
        last_rect = self.visualItemRect(last_item)
        if not first_rect.isValid() or not last_rect.isValid():
            return

        frame_rect = first_rect.united(last_rect).adjusted(2, 2, -2, -2)
        if frame_rect.isEmpty() or not frame_rect.intersects(self.viewport().rect()):
            return

        accent = self.palette().color(QPalette.ColorRole.Link)
        if not accent.isValid():
            accent = self.palette().color(QPalette.ColorRole.Highlight)
        accent.setAlpha(235)

        painter = QPainter(self.viewport())
        painter.setRenderHint(QPainter.RenderHint.Antialiasing, True)
        painter.setPen(QPen(accent, 2.0))
        painter.setBrush(Qt.BrushStyle.NoBrush)
        painter.drawRoundedRect(QRectF(frame_rect), 9.0, 9.0)
        painter.end()


class DocumentTab(QWidget):
    currentPageChanged = pyqtSignal(int, int)
    documentChanged = pyqtSignal()
    titleChanged = pyqtSignal(str)
    historyChanged = pyqtSignal(bool, bool)
    annotationSelectionChanged = pyqtSignal(bool)
    aiRegionSelected = pyqtSignal(int, bytes)
    translateRegionSelected = pyqtSignal(int, bytes, object, str)

    def __init__(self, path: str, dark_mode=False, bg=DEFAULT_BG, ink=DEFAULT_INK, parent=None, annotation_colors=None, smart_page_theme=False):
        super().__init__(parent)
        self.path = os.path.abspath(path)
        self.doc = fitz.open(self.path)
        if self.doc.is_encrypted and not self.doc.authenticate(""):
            self.doc.close()
            password, ok = QInputDialog.getText(parent, "Password required", "PDF password:", QLineEdit.EchoMode.Password)
            self.doc = fitz.open(self.path)
            if not ok or not self.doc.authenticate(password):
                self.doc.close()
                raise ValueError("This PDF could not be opened without a valid password.")
        self.page_count = self.doc.page_count
        if not self.page_count:
            self.doc.close()
            raise ValueError("This PDF contains no pages.")
        self.page_sizes = []
        for i in range(self.page_count):
            page = self.doc.load_page(i)
            self.page_sizes.append((float(page.rect.width), float(page.rect.height)))
        self.current_page = 0
        self.dark_mode = bool(dark_mode)
        self.smart_page_theme = bool(smart_page_theme)
        self.bg_color = bg
        self.ink_color = ink
        self.annotation_colors = dict(DEFAULT_ANNOTATION_COLORS)
        self.annotation_colors.update(annotation_colors or {})
        # Book and Scroll are independent layout options.
        # Default: single pages in a continuous vertical document.
        self.book_mode = False
        self.scroll_mode = True
        self.fit_mode = "width"
        self.custom_scale = 1.0
        self.custom_base_fit_mode = "width"
        self.active_tool = "select"
        # Selection is per-document tab. PDF page links are not annotations,
        # so they retain a geometry-based identity instead of an xref.
        self.selected_annotation: tuple[int, int] | None = None
        self.selected_annotations: list[tuple[int, int]] = []
        self.selected_page_link: tuple | None = None
        # Keep newly drawn link rectangles visible immediately; MuPDF may not
        # expose an inserted link through Page.get_links() until the document is saved.
        self._link_overlay_rects: dict[int, list[tuple[float, float, float, float, int]]] = {}
        # Live tutor annotations are temporary screen-only overlays and never mutate the PDF.
        self._live_teaching_marks: dict[int, list[dict]] = {}
        self.dirty = False
        # PyMuPDF's native is_dirty flag can become true after some read/selection
        # paths materialize annotation objects. Keep a persisted-content baseline so
        # merely selecting text, links, or annotations never creates a save prompt.
        # The signature tracks actual PDF content (rotations, annotations and links).
        try:
            self._saved_pdf_signature = self._pdf_persistence_signature(self.doc)
        except Exception:
            self._saved_pdf_signature = None
        self.undo_stack: list[bytes] = []
        self.redo_stack: list[bytes] = []
        self._history_limit = 25
        self._history_bytes_limit = 128 * 1024 * 1024
        self._restoring_history = False
        self.render_version = 0  # document-level change counter retained for compatibility
        # A page's raster/theme cache must not be invalidated when a different
        # page is edited. Per-page revisions also keep Smart Theme independent of
        # transient viewport dimensions (zoom/sidebar/chat resizing).
        self.page_render_versions = [0] * self.page_count
        self._thumbnail_cache = OrderedDict()
        self._thumbnail_cache_limit = 420
        # Page Overview renders sharper previews only for visible tiles. The LRU
        # stays small; off-screen tiles revert to the normal sidebar thumbnails.
        self._page_overview_preview_cache = OrderedDict()
        self._page_overview_preview_cache_limit = 32
        self._sidebar_visible = True
        self._linked_view_secondary = None
        self._linked_saved_view_modes = None
        self._linked_splitter = None
        self._secondary_scroll = None
        self._secondary_canvas = None
        self._secondary_thumbnails = None
        self._secondary_thumb_column = None
        self._syncing_secondary_page = False
        self._document_closing = False
        self._layout_timer = QTimer(self)
        self._layout_timer.setSingleShot(True)
        self._zoom_target_scale = None
        self._zoom_anchor_state = None
        self._zoom_anchor_point = None
        self._zoom_base_scale = None
        self._zoom_timer = QTimer(self)
        self._zoom_timer.setSingleShot(True)
        self._zoom_timer.setInterval(105)
        self._zoom_timer.timeout.connect(self._advance_primary_zoom)
        self._zoom_visual_current_factor = 1.0
        self._zoom_visual_target_factor = 1.0
        self._zoom_commit_pending = False
        self._secondary_zoom_target_scale = None
        self._secondary_zoom_anchor_state = None
        self._secondary_zoom_anchor_point = None
        self._secondary_zoom_base_scale = None
        self._secondary_zoom_timer = QTimer(self)
        self._secondary_zoom_timer.setSingleShot(True)
        self._secondary_zoom_timer.setInterval(105)
        self._secondary_zoom_timer.timeout.connect(self._advance_secondary_zoom)
        self._secondary_zoom_visual_current_factor = 1.0
        self._secondary_zoom_visual_target_factor = 1.0
        self._secondary_zoom_commit_pending = False
        self._zoom_animation_timer = QTimer(self)
        self._zoom_animation_timer.setInterval(16)
        self._zoom_animation_timer.timeout.connect(self._tick_zoom_animation)
        self._sidebar_metrics_timer = QTimer(self)
        self._sidebar_metrics_timer.setSingleShot(True)
        self._sidebar_metrics_timer.setInterval(55)
        self._sidebar_metrics_timer.timeout.connect(self._update_sidebar_thumbnail_metrics)
        self._layout_deferred_by_focus = False
        self._layout_timer.timeout.connect(self._relayout)
        self._build_ui()
        self._select_all_shortcut = QShortcut(QKeySequence.StandardKey.SelectAll, self.canvas)
        self._select_all_shortcut.setContext(Qt.ShortcutContext.WidgetWithChildrenShortcut)
        self._select_all_shortcut.activated.connect(self._select_all_annotations_on_current_page)
        self._build_thumbnails()
        self._build_outline()
        self._schedule_sidebar_metrics_update()
        self._schedule_layout()
        self._last_page_wheel_turn = 0.0
        self.scroll.verticalScrollBar().valueChanged.connect(self._on_scroll)
        self.scroll.horizontalScrollBar().valueChanged.connect(lambda _: self.canvas.update())
        self.scroll.viewport().installEventFilter(self)

    def _select_all_annotations_on_current_page(self):
        if self.doc is None or getattr(self.doc, "is_closed", True):
            return
        try:
            page = self.doc.load_page(max(0, min(int(self.current_page), self.page_count - 1)))
            items = [(int(self.current_page), int(a.xref)) for a in (page.annots() or [])]
            self.canvas._annotation_edit_mode = False
            self.set_annotation_selection(items)
        except Exception:
            pass

    @property
    def view_mode(self):
        """Backward-compatible combined label for older integrations."""
        if self.book_mode:
            return "book"
        return "continuous" if self.scroll_mode else "single"

    @view_mode.setter
    def view_mode(self, mode):
        # Legacy callers select a familiar preset. The toolbar itself uses the
        # independent set_layout_modes() API and never treats these as exclusive.
        value = str(mode or "continuous").lower()
        if value == "book":
            self.book_mode = True
        elif value == "single":
            self.book_mode = False
            self.scroll_mode = False
        else:
            self.book_mode = False
            self.scroll_mode = True
        if hasattr(self, "thumbnails"):
            self._sync_sidebar_selection()

    def _build_ui(self):
        layout = QHBoxLayout(self)
        layout.setContentsMargins(0, 0, 0, 0)
        layout.setSpacing(0)
        self.splitter = QSplitter(Qt.Orientation.Horizontal)
        self.splitter.setChildrenCollapsible(False)
        self.sidebar = QFrame()
        self.sidebar.setObjectName("documentSidebar")
        self.sidebar.setMinimumWidth(0)
        self.sidebar.setMaximumWidth(228)
        side_layout = QVBoxLayout(self.sidebar)
        side_layout.setContentsMargins(10, 10, 10, 10)
        side_layout.setSpacing(8)
        sidebar_language = "en"
        # Use a readable fallback if the owner window's settings are not available yet.
        sidebar_icon_color = "#29466f"
        try:
            owner_window = parent.window() if isinstance(parent, QWidget) else parent
            owner_settings = getattr(owner_window, "settings", None) or getattr(parent, "settings", None)
            if owner_settings is not None:
                sidebar_language = str(owner_settings.value("interface_language", "en", type=str) or "en")
                sidebar_theme = normalize_ui_theme(owner_settings.value("ui_theme", "dark", type=str))
                sidebar_icon_color = engo_ui_theme_tokens(sidebar_theme)["text"]
        except Exception:
            pass
        self._sidebar_language = "ar" if str(sidebar_language).lower().startswith("ar") else "en"
        # Keep the page-overview control in the same navigation strip as Pages
        # and Contents; a separate header row wastes sidebar height.
        self.side_tabs = ResponsiveSidebarTabs(self.sidebar, sidebar_language)
        self.thumbnails = BookSpreadThumbnailList()
        self.thumbnails.setObjectName("thumbnails")
        self.thumbnails.setIconSize(QSize(78, 95))
        self.thumbnails.setSpacing(6)
        self.thumbnails.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        self.thumbnails.setTextElideMode(Qt.TextElideMode.ElideNone)
        self.thumbnails.itemClicked.connect(self._thumbnail_clicked)
        # Pages remains a single tab in the sidebar. When two PDFs are combined,
        # its content changes to two independent thumbnail columns.
        self.pages_panel = QWidget()
        pages_layout = QHBoxLayout(self.pages_panel)
        pages_layout.setContentsMargins(0, 0, 0, 0)
        pages_layout.setSpacing(5)
        self._primary_thumb_column = QWidget()
        primary_thumb_layout = QVBoxLayout(self._primary_thumb_column)
        primary_thumb_layout.setContentsMargins(0, 0, 0, 0)
        primary_thumb_layout.setSpacing(3)
        self._primary_thumb_label = QLabel(Path(getattr(self, "display_path", self.path)).name)
        self._primary_thumb_label.setObjectName("sideHeader")
        self._primary_thumb_label.setAlignment(Qt.AlignmentFlag.AlignHCenter | Qt.AlignmentFlag.AlignVCenter)
        self._primary_thumb_label.setTextFormat(Qt.TextFormat.PlainText)
        self._primary_thumb_label.setWordWrap(True)
        self._primary_thumb_label.setMinimumWidth(0)
        _primary_header_policy = QSizePolicy(QSizePolicy.Policy.Ignored, QSizePolicy.Policy.Minimum)
        _primary_header_policy.setHeightForWidth(True)
        self._primary_thumb_label.setSizePolicy(_primary_header_policy)
        primary_thumb_layout.addWidget(self._primary_thumb_label)
        primary_thumb_layout.addWidget(self.thumbnails, 1)
        pages_layout.addWidget(self._primary_thumb_column, 1)
        self._secondary_thumb_column = QWidget()
        secondary_thumb_layout = QVBoxLayout(self._secondary_thumb_column)
        secondary_thumb_layout.setContentsMargins(0, 0, 0, 0)
        secondary_thumb_layout.setSpacing(3)
        self._secondary_thumb_label = QLabel("SUPPLEMENTARY")
        self._secondary_thumb_label.setObjectName("sideHeader")
        self._secondary_thumb_label.setAlignment(Qt.AlignmentFlag.AlignHCenter | Qt.AlignmentFlag.AlignVCenter)
        self._secondary_thumb_label.setTextFormat(Qt.TextFormat.PlainText)
        self._secondary_thumb_label.setWordWrap(True)
        self._secondary_thumb_label.setMinimumWidth(0)
        _secondary_header_policy = QSizePolicy(QSizePolicy.Policy.Ignored, QSizePolicy.Policy.Minimum)
        _secondary_header_policy.setHeightForWidth(True)
        self._secondary_thumb_label.setSizePolicy(_secondary_header_policy)
        secondary_thumb_layout.addWidget(self._secondary_thumb_label)
        self._secondary_thumbnails = QListWidget()
        self._secondary_thumbnails.setObjectName("thumbnails")
        self._secondary_thumbnails.setIconSize(QSize(54, 70))
        self._secondary_thumbnails.setSpacing(4)
        self._secondary_thumbnails.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        self._secondary_thumbnails.setTextElideMode(Qt.TextElideMode.ElideNone)
        self._secondary_thumbnails.itemClicked.connect(self._linked_secondary_thumbnail_clicked)
        secondary_thumb_layout.addWidget(self._secondary_thumbnails, 1)
        pages_layout.addWidget(self._secondary_thumb_column, 1)
        self._secondary_thumb_column.hide()
        self.outline = QTreeWidget()
        self.outline.setObjectName("outline")
        self.outline.setHeaderHidden(True)
        self.outline.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        self.outline.setTextElideMode(Qt.TextElideMode.ElideRight)
        self.outline.itemClicked.connect(self._outline_clicked)
        self.side_tabs.addTab(self.pages_panel, make_icon("pages", sidebar_icon_color, 15), "Pages")
        self.side_tabs.addTab(self.outline, make_icon("contents", sidebar_icon_color, 15), "Contents")
        # Re-apply the language after both buttons exist; this keeps the custom
        # sidebar switcher localized even when a document is opened after startup.
        self.side_tabs.setLanguage(sidebar_language)
        self.page_overview_btn = QToolButton(self.side_tabs._nav_host)
        self.page_overview_btn.setObjectName("pageOverviewButton")
        self.page_overview_btn.setIcon(make_icon("fullscreen", sidebar_icon_color, 16))
        self.page_overview_btn.setIconSize(QSize(16, 16))
        self.page_overview_btn.setToolButtonStyle(Qt.ToolButtonStyle.ToolButtonIconOnly)
        self.page_overview_btn.setFixedHeight(32)
        self.page_overview_btn.setMinimumWidth(34)
        self.page_overview_btn.setMaximumWidth(42)
        self.page_overview_btn.setAutoRaise(False)
        self.page_overview_btn.setCursor(Qt.CursorShape.PointingHandCursor)
        self.page_overview_btn.setToolTip(_engo_translate_tooltip("Show all PDF pages", self._sidebar_language))
        self.page_overview_btn.setAccessibleName("Show all PDF pages")
        self.page_overview_btn.setCheckable(True)
        self.page_overview_btn.clicked.connect(lambda _checked=False: self.show_page_overview())
        self.page_overview_btn.setProperty("engoIconName", "fullscreen")
        self.side_tabs.setTrailingWidget(self.page_overview_btn)
        side_layout.addWidget(self.side_tabs, 1)
        self.sidebar.installEventFilter(self)
        self.thumbnails.installEventFilter(self)
        self.thumbnails.viewport().installEventFilter(self)
        self._secondary_thumbnails.installEventFilter(self)
        self._secondary_thumbnails.viewport().installEventFilter(self)
        self.splitter.addWidget(self.sidebar)

        self.scroll = QScrollArea()
        self.scroll.setObjectName("readerScroll")
        self.scroll.setWidgetResizable(False)
        self.scroll.setAlignment(Qt.AlignmentFlag.AlignLeft | Qt.AlignmentFlag.AlignTop)
        self.scroll.setFrameShape(QFrame.Shape.NoFrame)
        self.scroll.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAsNeeded)
        self.scroll.setVerticalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAsNeeded)
        self.canvas = DocumentCanvas(self)
        self.scroll.setWidget(self.canvas)
        self.splitter.addWidget(self.scroll)
        self.splitter.setStretchFactor(0, 0)
        self.splitter.setStretchFactor(1, 1)
        self.splitter.setSizes([205, 1000])
        layout.addWidget(self.splitter)

        # Full-area page overview: it replaces both the sidebar and reader canvas,
        # while reusing the thumbnails already generated for the sidebar. Reusing
        # those cached previews avoids a second Smart Page Theme/image-processing pass.
        self._page_overview_active = False
        owner_window = self.window()
        overview_host = owner_window.centralWidget() if hasattr(owner_window, "centralWidget") else None
        self._page_overview_host = overview_host if isinstance(overview_host, QWidget) else self
        self._page_overview_overlay = QFrame(self._page_overview_host)
        self._page_overview_overlay.setObjectName("pageOverviewOverlay")
        self._page_overview_overlay.setGeometry(self._page_overview_host.rect())
        self._page_overview_host.installEventFilter(self)
        overview_layout = QVBoxLayout(self._page_overview_overlay)
        overview_layout.setContentsMargins(18, 14, 18, 16)
        overview_layout.setSpacing(10)

        overview_header = QHBoxLayout()
        overview_header.setContentsMargins(0, 0, 0, 0)
        overview_header.setSpacing(10)
        self._page_overview_title = QLabel(self._overview_text("All pages", "كل صفحات الملف"), self._page_overview_overlay)
        self._page_overview_title.setObjectName("pageOverviewTitle")
        self._page_overview_title.setTextFormat(Qt.TextFormat.PlainText)
        self._page_overview_title.setWordWrap(True)
        self._page_overview_title.setSizePolicy(QSizePolicy.Policy.Expanding, QSizePolicy.Policy.Preferred)
        self._page_overview_title.setMinimumWidth(0)
        self._page_overview_title.setAlignment(
            Qt.AlignmentFlag.AlignRight | Qt.AlignmentFlag.AlignVCenter
            if getattr(self, "_sidebar_language", "en") == "ar"
            else Qt.AlignmentFlag.AlignLeft | Qt.AlignmentFlag.AlignVCenter
        )
        self._page_overview_title.setLayoutDirection(
            Qt.LayoutDirection.RightToLeft if getattr(self, "_sidebar_language", "en") == "ar"
            else Qt.LayoutDirection.LeftToRight
        )
        overview_header.addWidget(self._page_overview_title, 1)
        # Separate filename and count labels so bidirectional Arabic/Latin text
        # never reorders. Both labels intentionally share the same visual style.
        self._page_overview_count = QLabel(self._overview_text("Number of pages:0", "عدد الصفحات:0"), self._page_overview_overlay)
        self._page_overview_count.setObjectName("pageOverviewCount")
        self._page_overview_count.setTextFormat(Qt.TextFormat.PlainText)
        self._page_overview_count.setWordWrap(False)
        self._page_overview_count.setSizePolicy(QSizePolicy.Policy.Preferred, QSizePolicy.Policy.Preferred)
        self._page_overview_count.setAlignment(
            Qt.AlignmentFlag.AlignRight | Qt.AlignmentFlag.AlignVCenter
            if getattr(self, "_sidebar_language", "en") == "ar"
            else Qt.AlignmentFlag.AlignLeft | Qt.AlignmentFlag.AlignVCenter
        )
        self._page_overview_count.setLayoutDirection(
            Qt.LayoutDirection.RightToLeft if getattr(self, "_sidebar_language", "en") == "ar"
            else Qt.LayoutDirection.LeftToRight
        )
        self._page_overview_count.setMinimumWidth(0)
        overview_header.addWidget(self._page_overview_count, 0)
        overview_header.addStretch(1)
        # Keep the keyboard hint on the same header row, immediately beside
        # the close control (rather than consuming a separate row below it).
        self._page_overview_hint = QLabel(self._overview_text(
            "Double-click or press Enter to open · Esc to close",
            "دبل كليك أو Enter لفتح الصفحة · Esc للخروج"
        ), self._page_overview_overlay)
        self._page_overview_hint.setObjectName("pageOverviewHint")
        self._page_overview_hint.setAlignment(Qt.AlignmentFlag.AlignVCenter | Qt.AlignmentFlag.AlignTrailing)
        self._page_overview_hint.setWordWrap(False)
        self._page_overview_hint.setSizePolicy(QSizePolicy.Policy.Maximum, QSizePolicy.Policy.Preferred)
        overview_header.addWidget(self._page_overview_hint, 0, Qt.AlignmentFlag.AlignVCenter)
        self._page_overview_close_btn = QToolButton(self._page_overview_overlay)
        self._page_overview_close_btn.setObjectName("pageOverviewClose")
        self._page_overview_close_btn.setToolButtonStyle(Qt.ToolButtonStyle.ToolButtonIconOnly)
        self._page_overview_close_btn.setAutoRaise(False)
        self._page_overview_close_btn.setFixedSize(36, 36)
        self._page_overview_close_btn.setIconSize(QSize(18, 18))
        self._page_overview_close_btn.setContentsMargins(0, 0, 0, 0)
        self._page_overview_close_btn.setLayoutDirection(Qt.LayoutDirection.LeftToRight)
        self._page_overview_close_btn.setFocusPolicy(Qt.FocusPolicy.NoFocus)
        self._page_overview_close_btn.setCursor(Qt.CursorShape.PointingHandCursor)
        self._page_overview_close_btn.setToolTip(_engo_translate_tooltip("Close page overview", self._sidebar_language))
        self._page_overview_close_btn.clicked.connect(lambda _checked=False: self.close_page_overview())
        overview_header.addWidget(self._page_overview_close_btn)
        overview_layout.addLayout(overview_header)

        self.page_overview_grid = PageOverviewGrid(self._page_overview_overlay)
        self.page_overview_grid.setObjectName("pageOverviewGrid")
        self.page_overview_grid.setViewMode(QListView.ViewMode.IconMode)
        self.page_overview_grid.setFlow(QListView.Flow.LeftToRight)
        self.page_overview_grid.setWrapping(True)
        self.page_overview_grid.setResizeMode(QListView.ResizeMode.Adjust)
        self.page_overview_grid.setMovement(QListView.Movement.Static)
        self.page_overview_grid.setSelectionMode(QAbstractItemView.SelectionMode.SingleSelection)
        self.page_overview_grid.setFocusPolicy(Qt.FocusPolicy.StrongFocus)
        self._page_overview_overlay.setFocusPolicy(Qt.FocusPolicy.StrongFocus)
        # The grid computes tile/icon dimensions from the full available width.
        # At desktop widths this gives six or more columns rather than leaving
        # a large unused strip on the right side of the gallery.
        self.page_overview_grid.setItemAlignment(Qt.AlignmentFlag.AlignHCenter | Qt.AlignmentFlag.AlignVCenter)
        self.page_overview_grid.update_responsive_metrics()
        self.page_overview_grid.metricsChanged.connect(self._on_page_overview_metrics_changed)
        self.page_overview_grid.setSpacing(1)
        self.page_overview_grid.setWordWrap(True)
        self.page_overview_grid.setTextElideMode(Qt.TextElideMode.ElideNone)
        self.page_overview_grid.setUniformItemSizes(True)
        self.page_overview_grid.setVerticalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAsNeeded)
        self.page_overview_grid.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        self.page_overview_grid.setVerticalScrollMode(QAbstractItemView.ScrollMode.ScrollPerPixel)
        self.page_overview_grid.itemDoubleClicked.connect(self._open_page_from_overview)
        self.page_overview_grid.keyActionRequested.connect(self._handle_page_overview_key)
        # Keyboard routing is installed on QApplication only while the gallery
        # is open. Do not register QShortcut objects here: MainWindow has global
        # Escape/arrow shortcuts that can win the ShortcutMap arbitration.
        self._page_overview_key_shortcuts = []  # compatibility; no competing shortcuts
        self._page_overview_refresh_timer = QTimer(self)
        self._page_overview_refresh_timer.setSingleShot(True)
        self._page_overview_refresh_timer.setInterval(90)
        self._page_overview_refresh_timer.timeout.connect(self._refresh_page_overview_visible_previews)
        self.page_overview_grid.verticalScrollBar().valueChanged.connect(
            lambda _value: self._schedule_page_overview_preview_refresh()
        )
        overview_layout.addWidget(self.page_overview_grid, 1)
        self._page_overview_overlay.hide()

        # Local filters handle geometry/child events. Keyboard events are routed
        # by the temporary QApplication filter installed only while overview is open.
        self._page_overview_overlay.installEventFilter(self)
        self.page_overview_grid.installEventFilter(self)
        self.page_overview_grid.viewport().installEventFilter(self)
        self._page_overview_app_filter_installed = False

    def _on_page_overview_metrics_changed(self):
        """Discard visible previews rendered for the previous tile size and reload them lazily."""
        if not getattr(self, "_page_overview_active", False):
            return
        grid = self.page_overview_grid
        viewport_rect = grid.viewport().rect()
        for index in range(grid.count()):
            item = grid.item(index)
            if item is None or not bool(item.data(Qt.ItemDataRole.UserRole + 1)):
                continue
            if grid.visualItemRect(item).intersects(viewport_rect):
                page_index = item.data(Qt.ItemDataRole.UserRole)
                item.setIcon(self._page_overview_placeholder_icon(int(page_index)))
                item.setData(Qt.ItemDataRole.UserRole + 1, False)
        self._schedule_page_overview_preview_refresh()

    def _handle_page_overview_key(self, action_name: str):
        """Handle page-gallery navigation using the visible geometry of the grid."""
        if not getattr(self, "_page_overview_active", False):
            return
        grid = getattr(self, "page_overview_grid", None)
        if grid is None or grid.count() <= 0:
            return
        if action_name == "escape":
            self.close_page_overview()
            return
        if action_name == "open":
            selected = grid.currentItem()
            if selected is None:
                selected = grid.item(0)
            if selected is not None:
                self._open_page_from_overview(selected)
            return
        if action_name not in ("left", "right", "up", "down"):
            return

        current = grid.currentItem()
        if current is None:
            current = grid.item(0)
            grid.setCurrentItem(current)
        current_rect = grid.visualItemRect(current)
        if not current_rect.isValid():
            return
        origin = current_rect.center()
        directional = []
        for index in range(grid.count()):
            candidate = grid.item(index)
            if candidate is current:
                continue
            rect = grid.visualItemRect(candidate)
            if not rect.isValid():
                continue
            delta_x = rect.center().x() - origin.x()
            delta_y = rect.center().y() - origin.y()
            if action_name == "left":
                primary, cross = -delta_x, abs(delta_y)
            elif action_name == "right":
                primary, cross = delta_x, abs(delta_y)
            elif action_name == "up":
                primary, cross = -delta_y, abs(delta_x)
            else:
                primary, cross = delta_y, abs(delta_x)
            if primary > 1:
                # Prefer the closest item in the requested direction and strongly
                # penalize crossing into another visual row/column.
                directional.append((primary + cross * 2.4, candidate))
        if directional:
            candidate = min(directional, key=lambda pair: pair[0])[1]
            grid.setCurrentItem(candidate)
            candidate.setSelected(True)
            grid.scrollToItem(candidate, QAbstractItemView.ScrollHint.EnsureVisible)

    def _overview_text(self, english: str, arabic: str) -> str:
        return arabic if getattr(self, "_sidebar_language", "en") == "ar" else english

    def _page_overview_placeholder_icon(self, page_index: int) -> QIcon:
        source_item = self.thumbnails.item(int(page_index)) if hasattr(self, "thumbnails") else None
        return source_item.icon() if source_item is not None else QIcon()

    def _page_overview_preview_pixmap(self, page_index: int) -> QPixmap:
        """Render a sharp preview on demand, without starting Smart Theme work again."""
        page_index = int(page_index)
        page_revision = int((getattr(self, "page_render_versions", []) or [self.render_version])[page_index])
        key = (page_index, page_revision, bool(self.dark_mode), bool(self.smart_page_theme),
               str(self.bg_color), str(self.ink_color), 560)
        cache = getattr(self, "_page_overview_preview_cache", None)
        if cache is None:
            self._page_overview_preview_cache = OrderedDict()
            cache = self._page_overview_preview_cache
        cached = cache.get(key)
        if cached is not None and not cached.isNull():
            cache.move_to_end(key)
            return cached

        # If Smart Page Theme has already produced a master for this page, reuse
        # it directly. Otherwise use the fast base page palette for this temporary
        # navigation preview; never queue or run the Smart Theme algorithm here.
        pixmap = None
        if self.dark_mode and self.smart_page_theme:
            try:
                canvas = getattr(self, "canvas", None)
                identity = canvas._smart_theme_identity(page_index) if canvas is not None else None
                if identity is not None:
                    final_store = getattr(canvas, "_smart_theme_final_cache", {})
                    preview_store = getattr(canvas, "_smart_theme_preview_cache", {})
                    candidate = final_store.get(identity) or preview_store.get(identity)
                    if candidate is not None and not candidate.isNull() and max(candidate.width(), candidate.height()) >= 320:
                        pixmap = QPixmap(candidate)
            except (RuntimeError, AttributeError, TypeError):
                pixmap = None

        if pixmap is None or pixmap.isNull():
            page = self.doc.load_page(page_index)
            page_rect = page.rect
            max_side = max(float(page_rect.width), float(page_rect.height), 1.0)
            scale = min(0.72, 560.0 / max_side)
            render = page.get_pixmap(matrix=fitz.Matrix(scale, scale), alpha=False, annots=True)
            image = Image.frombytes("RGB", (render.width, render.height), render.samples)
            themed = apply_page_theme_to_image(
                image, self.dark_mode, self.bg_color, self.ink_color, smart=False
            )
            pixmap = QPixmap.fromImage(image_to_qimage(themed))

        cache[key] = pixmap
        cache.move_to_end(key)
        while len(cache) > int(getattr(self, "_page_overview_preview_cache_limit", 32)):
            cache.popitem(last=False)
        return pixmap

    def _schedule_page_overview_preview_refresh(self):
        timer = getattr(self, "_page_overview_refresh_timer", None)
        if timer is not None and getattr(self, "_page_overview_active", False):
            timer.start()

    def _refresh_page_overview_visible_previews(self):
        """Upgrade only visible low-res placeholders; release large icons off-screen."""
        if not getattr(self, "_page_overview_active", False):
            return
        grid = self.page_overview_grid
        viewport_rect = grid.viewport().rect()
        visible_to_render = []
        for item_index in range(grid.count()):
            item = grid.item(item_index)
            page_index = item.data(Qt.ItemDataRole.UserRole)
            if page_index is None:
                continue
            page_index = int(page_index)
            is_visible = grid.visualItemRect(item).intersects(viewport_rect)
            high_res = bool(item.data(Qt.ItemDataRole.UserRole + 1))
            if is_visible and not high_res:
                visible_to_render.append((item, page_index))
            elif not is_visible and high_res:
                item.setIcon(self._page_overview_placeholder_icon(page_index))
                item.setData(Qt.ItemDataRole.UserRole + 1, False)

        # Limit each event-loop slice so opening/scrolling a large PDF stays responsive.
        for item, page_index in visible_to_render[:3]:
            try:
                source_pixmap = self._page_overview_preview_pixmap(page_index)
                preview_box = self.page_overview_grid.iconSize()
                scaled = source_pixmap.scaled(
                    preview_box, Qt.AspectRatioMode.KeepAspectRatio,
                    Qt.TransformationMode.SmoothTransformation,
                )
                centered = QPixmap(preview_box)
                centered.fill(Qt.GlobalColor.transparent)
                painter = QPainter(centered)
                painter.setRenderHint(QPainter.RenderHint.SmoothPixmapTransform, True)
                painter.drawPixmap(
                    (preview_box.width() - scaled.width()) // 2,
                    (preview_box.height() - scaled.height()) // 2,
                    scaled,
                )
                painter.end()
                item.setIcon(QIcon(centered))
                item.setData(Qt.ItemDataRole.UserRole + 1, True)
            except (RuntimeError, IndexError, ValueError):
                continue
        if len(visible_to_render) > 3:
            QTimer.singleShot(25, self._refresh_page_overview_visible_previews)

    def _style_page_overview(self):
        """Apply the active interface palette without changing PDF page themes."""
        owner = self.window()
        settings = getattr(owner, "settings", None)
        theme_name = settings.value("ui_theme", "dark", type=str) if settings is not None else "dark"
        tokens = engo_ui_theme_tokens(theme_name)
        self._page_overview_overlay.setStyleSheet(f"""
            QFrame#pageOverviewOverlay {{ background: {tokens['window']}; }}
            QLabel#pageOverviewTitle, QLabel#pageOverviewCount {{
                color: {tokens['text']}; font-size: 15pt; font-weight: 750;
                padding: 0px; margin: 0px;
            }}
            QLabel#pageOverviewHint {{ color: {tokens['muted']}; font-size: 9pt; }}
            QListWidget#pageOverviewGrid {{
                background: {tokens['window']}; color: {tokens['text']};
                border: 0; outline: 0; padding: 5px;
            }}
            QListWidget#pageOverviewGrid::item {{
                background: transparent; color: {tokens['text']};
                border: 2px solid transparent; border-radius: 12px;
                padding: 3px 2px; margin: 0px;
            }}
            QListWidget#pageOverviewGrid::item:hover {{
                background: transparent; color: {tokens['accent']};
                border-color: {tokens['border']};
            }}
            QListWidget#pageOverviewGrid::item:selected {{
                background: transparent; color: {tokens['accent']};
                border: 2px solid {tokens['accent']}; border-radius: 12px;
            }}
            QToolButton#pageOverviewClose {{
                background: {tokens['panel_alt']}; color: {tokens['text']};
                border: 1px solid {tokens['border']}; border-radius: 8px;
                padding: 0px; margin: 0px;
            }}
            QToolButton#pageOverviewClose:hover {{ background: {tokens['hover']}; border-color: {tokens['accent']}; }}
        """)
        # Draw a symmetric X into a transparent icon canvas. An icon-only
        # QToolButton centers the artwork geometrically, avoiding font baseline
        # and glyph-bearing offsets that kept the previous × character low.
        close_glyph = QPixmap(18, 18)
        close_glyph.fill(Qt.GlobalColor.transparent)
        glyph_painter = QPainter(close_glyph)
        glyph_painter.setRenderHint(QPainter.RenderHint.Antialiasing, True)
        glyph_pen = QPen(QColor(tokens["text"]))
        glyph_pen.setWidthF(2.0)
        glyph_pen.setCapStyle(Qt.PenCapStyle.RoundCap)
        glyph_painter.setPen(glyph_pen)
        glyph_painter.drawLine(QPointF(4.5, 4.5), QPointF(13.5, 13.5))
        glyph_painter.drawLine(QPointF(13.5, 4.5), QPointF(4.5, 13.5))
        glyph_painter.end()
        self._page_overview_close_btn.setIcon(QIcon(close_glyph))
        self.page_overview_btn.setIcon(make_icon("fullscreen", tokens["text"], 16))
        self.page_overview_btn.setAutoRaise(False)

    def show_page_overview(self):
        """Show all pages in a scrollable gallery with sharp, lazy-loaded previews."""
        if self._page_overview_active or not self.doc or getattr(self.doc, "is_closed", False):
            return
        grid = self.page_overview_grid
        grid.update_responsive_metrics()
        grid.setUpdatesEnabled(False)
        grid.clear()
        try:
            for page_index in range(self.page_count):
                placeholder = self._page_overview_placeholder_icon(page_index)
                item = QListWidgetItem(placeholder, self._overview_text(
                    f"Page {page_index + 1}", f"صفحة {page_index + 1}"
                ))
                item.setData(Qt.ItemDataRole.UserRole, page_index)
                item.setData(Qt.ItemDataRole.UserRole + 1, False)
                item.setTextAlignment(Qt.AlignmentFlag.AlignHCenter)
                item.setToolTip(self._overview_text(
                    f"Double-click to open page {page_index + 1}",
                    f"اضغط مرتين لفتح الصفحة {page_index + 1}"
                ))
                item.setSizeHint(grid.gridSize())
                grid.addItem(item)
        finally:
            grid.setUpdatesEnabled(True)

        if grid.count() == 0:
            return
        self._style_page_overview()
        file_name = os.path.basename(str(getattr(self, "path", "") or "")).strip()
        if not file_name:
            file_name = self._overview_text("Untitled document", "مستند بدون اسم")
        # Filename and page count are separate widgets with explicit text
        # direction, so Arabic names and the Latin .pdf extension never mix
        # with the numeric page count in the same bidi paragraph.
        self._page_overview_title.setText(file_name)
        self._page_overview_title.setLayoutDirection(
            Qt.LayoutDirection.RightToLeft if getattr(self, "_sidebar_language", "en") == "ar"
            else Qt.LayoutDirection.LeftToRight
        )
        self._page_overview_title.setAlignment(
            Qt.AlignmentFlag.AlignRight | Qt.AlignmentFlag.AlignVCenter
            if getattr(self, "_sidebar_language", "en") == "ar"
            else Qt.AlignmentFlag.AlignLeft | Qt.AlignmentFlag.AlignVCenter
        )
        self._page_overview_count.setText(self._overview_text(
            f"Number of pages:{self.page_count}",
            f"عدد الصفحات:{self.page_count}"
        ))
        self._page_overview_count.setLayoutDirection(
            Qt.LayoutDirection.RightToLeft if getattr(self, "_sidebar_language", "en") == "ar"
            else Qt.LayoutDirection.LeftToRight
        )
        self._page_overview_title.setToolTip(str(getattr(self, "path", "") or file_name))
        current_item = None
        for item_index in range(grid.count()):
            candidate = grid.item(item_index)
            if int(candidate.data(Qt.ItemDataRole.UserRole)) == int(self.current_page):
                current_item = candidate
                break
        if current_item is not None:
            grid.setCurrentItem(current_item)
            current_item.setSelected(True)
            grid.scrollToItem(current_item, QAbstractItemView.ScrollHint.PositionAtCenter)
        self._page_overview_active = True
        # Install last so this filter runs before the main window's global
        # shortcut handlers. ShortcutOverride is consumed first, preventing
        # MainWindow's Escape/arrow shortcuts from stealing gallery keys.
        app = QApplication.instance()
        if app is not None and not self._page_overview_app_filter_installed:
            app.installEventFilter(self)
            self._page_overview_app_filter_installed = True
        self.page_overview_btn.setChecked(True)
        self._page_overview_overlay.setGeometry(self._page_overview_host.rect())
        self._page_overview_overlay.show()
        self._page_overview_overlay.raise_()
        # Focus the list after it is visible so keyboard navigation works
        # immediately, without requiring a click inside the gallery first.
        self.page_overview_grid.setFocus(Qt.FocusReason.OtherFocusReason)
        self._schedule_page_overview_preview_refresh()

    def close_page_overview(self):
        """Return from the page gallery to the exact previous document layout."""
        if not getattr(self, "_page_overview_active", False):
            return
        self._page_overview_active = False
        # Restore the normal Engo shortcuts immediately after leaving the gallery.
        app = QApplication.instance()
        if app is not None and self._page_overview_app_filter_installed:
            app.removeEventFilter(self)
            self._page_overview_app_filter_installed = False
        timer = getattr(self, "_page_overview_refresh_timer", None)
        if timer is not None:
            timer.stop()
        self._page_overview_overlay.hide()
        if hasattr(self, "page_overview_btn"):
            self.page_overview_btn.setChecked(False)

    def _open_page_from_overview(self, item):
        if item is None:
            return
        page_index = item.data(Qt.ItemDataRole.UserRole)
        if page_index is None:
            return
        page_index = max(0, min(int(page_index), self.page_count - 1))
        self.close_page_overview()
        self.go_to_page(page_index)

    def enable_linked_view(self, secondary_tab: "DocumentTab"):
        """Show two independently scrolling PDFs in this (primary) document tab."""
        if secondary_tab is None or secondary_tab is self:
            self.disable_linked_view()
            return
        if self._linked_view_secondary is secondary_tab and self._linked_splitter is not None:
            return
        self.disable_linked_view()
        self._linked_view_secondary = secondary_tab
        self._linked_saved_view_modes = (
            (self.book_mode, self.scroll_mode, self.fit_mode, self.custom_scale, self.custom_base_fit_mode),
            (secondary_tab.book_mode, secondary_tab.scroll_mode, secondary_tab.fit_mode,
             secondary_tab.custom_scale, secondary_tab.custom_base_fit_mode),
        )
        # In the side-by-side workspace both panes should react to available width
        # in the same fit mode. Preserve the secondary's prior preference for Unlink.
        secondary_tab.fit_mode = self.fit_mode
        if self.fit_mode == "custom":
            secondary_tab.custom_scale = self.custom_scale
            secondary_tab.custom_base_fit_mode = self.custom_base_fit_mode
        # A linked study shows two separate PDFs side by side. Book spreads are
        # disabled while linked, but Scroll remains a real user option. Apply the
        # primary document's Scroll state to both visible panes for consistency.
        linked_scroll_mode = bool(self.scroll_mode)
        self.book_mode, self.scroll_mode = False, linked_scroll_mode
        self.thumbnails.set_book_spread_selection(False)
        secondary_tab.book_mode, secondary_tab.scroll_mode = False, linked_scroll_mode
        secondary_tab.canvas.clear_cache()
        self.canvas.clear_cache()
        self._linked_splitter = QSplitter(Qt.Orientation.Horizontal)
        self._linked_splitter.setChildrenCollapsible(False)
        self._linked_splitter.setObjectName("linkedPdfSplitter")
        # Reparent the existing primary scroll area into the paired view.
        self.scroll.setParent(self._linked_splitter)
        self._linked_splitter.addWidget(self.scroll)
        self._secondary_scroll = QScrollArea()
        self._secondary_scroll.setObjectName("readerScroll")
        self._secondary_scroll.setWidgetResizable(False)
        self._secondary_scroll.setAlignment(Qt.AlignmentFlag.AlignLeft | Qt.AlignmentFlag.AlignTop)
        self._secondary_scroll.setFrameShape(QFrame.Shape.NoFrame)
        self._secondary_scroll.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAsNeeded)
        self._secondary_scroll.setVerticalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAsNeeded)
        self._secondary_canvas = DocumentCanvas(secondary_tab)
        self._secondary_canvas.display_scroll = self._secondary_scroll
        self._secondary_canvas.external_zoom_callback = self._linked_zoom_secondary
        self._secondary_canvas.external_page_turn_callback = self._linked_go_to_secondary_page
        # Both linked PDFs remain fully editable.  The secondary canvas uses its
        # own DocumentTab as the annotation/history model; it is not a preview.
        self._secondary_canvas.read_only = False
        secondary_tab.set_tool(self.active_tool)
        self._secondary_scroll.setWidget(self._secondary_canvas)
        self._secondary_scroll.viewport().installEventFilter(self)
        self._secondary_scroll.verticalScrollBar().valueChanged.connect(self._on_secondary_scroll)
        self._secondary_scroll.horizontalScrollBar().valueChanged.connect(lambda _v: self._secondary_canvas.update() if self._secondary_canvas else None)
        self._linked_splitter.addWidget(self._secondary_scroll)
        self._linked_splitter.setStretchFactor(0, 1)
        self._linked_splitter.setStretchFactor(1, 1)
        self._linked_splitter.setSizes([1, 1])
        self._linked_splitter.splitterMoved.connect(
            lambda *_args: QTimer.singleShot(0, self._relayout_linked_secondary)
        )
        self.splitter.addWidget(self._linked_splitter)
        self.splitter.setStretchFactor(1, 1)
        self._primary_thumb_label.setText(f"PRIMARY · {Path(getattr(self, 'display_path', self.path)).name}")
        self._primary_thumb_label.updateGeometry()
        self._primary_thumb_label.parentWidget().updateGeometry()
        self._secondary_thumb_label.setText(f"SECONDARY · {Path(secondary_tab.path).name}")
        self._secondary_thumb_label.updateGeometry()
        self._secondary_thumb_label.parentWidget().updateGeometry()
        self._secondary_thumb_column.show()
        self.thumbnails.setIconSize(QSize(54, 70))
        self.thumbnails.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        self._secondary_thumbnails.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        self._schedule_sidebar_metrics_update()
        for row in range(self.thumbnails.count()):
            item = self.thumbnails.item(row)
            if item is not None:
                item.setSizeHint(QSize(74, 88))
        self._build_linked_thumbnails(secondary_tab)
        secondary_tab.currentPageChanged.connect(self._on_secondary_document_page_changed)
        self._relayout()
        QTimer.singleShot(80, self._relayout_linked_secondary)
        self._sync_secondary_sidebar_selection()

    def disable_linked_view(self):
        """Restore the normal one-PDF page canvas and sidebar."""
        secondary = self._linked_view_secondary
        if secondary is not None:
            try:
                secondary.currentPageChanged.disconnect(self._on_secondary_document_page_changed)
            except Exception:
                pass
        if self._linked_splitter is not None:
            try:
                old_splitter = self.splitter.replaceWidget(1, self.scroll)
                if old_splitter is not None:
                    old_splitter.deleteLater()
            except Exception:
                try:
                    self.scroll.setParent(self.splitter)
                    self.splitter.addWidget(self.scroll)
                    self._linked_splitter.deleteLater()
                except Exception:
                    pass
        saved_modes = self._linked_saved_view_modes
        if saved_modes is not None:
            try:
                primary_saved = saved_modes[0]
                self.book_mode, self.scroll_mode = primary_saved[:2]
                if len(primary_saved) >= 4:
                    self.fit_mode, self.custom_scale = primary_saved[2], float(primary_saved[3])
                if len(primary_saved) >= 5:
                    self.custom_base_fit_mode = primary_saved[4] if primary_saved[4] in ("width", "page") else "width"
                if secondary is not None:
                    secondary_saved = saved_modes[1]
                    secondary.book_mode, secondary.scroll_mode = secondary_saved[:2]
                    if len(secondary_saved) >= 4:
                        secondary.fit_mode, secondary.custom_scale = secondary_saved[2], float(secondary_saved[3])
                    if len(secondary_saved) >= 5:
                        secondary.custom_base_fit_mode = secondary_saved[4] if secondary_saved[4] in ("width", "page") else "width"
                    secondary._relayout()
            except Exception:
                pass
        self._linked_saved_view_modes = None
        self._linked_view_secondary = None
        self._linked_splitter = None
        self._secondary_scroll = None
        self._secondary_canvas = None
        self._secondary_thumbnails.clear()
        self._secondary_thumb_column.hide()
        self._primary_thumb_label.setText(Path(getattr(self, "display_path", self.path)).name)
        self.thumbnails.setIconSize(QSize(78, 95))
        self.thumbnails.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        self._schedule_sidebar_metrics_update()
        for row in range(self.thumbnails.count()):
            item = self.thumbnails.item(row)
            if item is not None:
                item.setSizeHint(QSize(142, 112))
        self._relayout()
        self._sync_sidebar_selection()

    def _build_linked_thumbnails(self, secondary_tab: "DocumentTab"):
        self._secondary_thumbnails.clear()
        self._secondary_thumbnails.setUpdatesEnabled(False)
        try:
            revisions = getattr(secondary_tab, "page_render_versions", None) or [secondary_tab.render_version] * secondary_tab.page_count
            thumb_cache = getattr(secondary_tab, "_thumbnail_cache", None)
            if thumb_cache is None:
                secondary_tab._thumbnail_cache = OrderedDict()
                thumb_cache = secondary_tab._thumbnail_cache
            for i in range(secondary_tab.page_count):
                page_revision = int(revisions[i]) if i < len(revisions) else int(secondary_tab.render_version)
                # Linked sidebar icons are displayed at 54x70. Render at over
                # 2x their display resolution; the cache tag invalidates old icons.
                sidebar_render_px = 204
                cache_key = (int(i), page_revision, bool(secondary_tab.dark_mode),
                             bool(secondary_tab.smart_page_theme), str(secondary_tab.bg_color),
                             str(secondary_tab.ink_color), 54, 70, "linked-hq-v4", sidebar_render_px)
                qpix = thumb_cache.get(cache_key)
                if qpix is not None and not qpix.isNull():
                    thumb_cache.move_to_end(cache_key)
                else:
                    page = secondary_tab.doc.load_page(i)
                    page_rect = page.rect
                    max_page_side = max(float(page_rect.width), float(page_rect.height), 1.0)
                    render_scale = min(0.76, sidebar_render_px / max_page_side)
                    pix = page.get_pixmap(matrix=fitz.Matrix(render_scale, render_scale), alpha=False, annots=True)
                    img = Image.frombytes("RGB", (pix.width, pix.height), pix.samples)
                    img = apply_page_theme_to_image(
                        img, secondary_tab.dark_mode, secondary_tab.bg_color, secondary_tab.ink_color,
                        smart=secondary_tab.smart_page_theme,
                    )
                    qpix = QPixmap.fromImage(image_to_qimage(img)).scaled(
                        54, 70, Qt.AspectRatioMode.KeepAspectRatio,
                        Qt.TransformationMode.SmoothTransformation,
                    )
                    thumb_cache[cache_key] = qpix
                    thumb_cache.move_to_end(cache_key)
                    while len(thumb_cache) > secondary_tab._thumbnail_cache_limit:
                        thumb_cache.popitem(last=False)
                item = QListWidgetItem(QIcon(qpix), f"{i + 1}")
                item.setData(Qt.ItemDataRole.UserRole, i)
                item.setToolTip(f"{Path(secondary_tab.path).name} · Page {i + 1}")
                item.setSizeHint(QSize(74, 88))
                self._secondary_thumbnails.addItem(item)
        except Exception:
            pass
        finally:
            self._secondary_thumbnails.setUpdatesEnabled(True)
        self._sync_secondary_sidebar_selection()

    def _linked_secondary_thumbnail_clicked(self, item):
        if self._linked_view_secondary is not None:
            self._linked_go_to_secondary_page(int(item.data(Qt.ItemDataRole.UserRole)))

    def _linked_go_to_secondary_page(self, index: int):
        tab = self._linked_view_secondary
        if tab is None or self._secondary_scroll is None or self._secondary_canvas is None:
            return
        index = max(0, min(int(index), tab.page_count - 1))
        if tab.selected_annotation and tab.selected_annotation[0] != index:
            tab.clear_annotation_selection()
        tab.current_page = index
        if not tab.scroll_mode:
            # Only the active page exists in the secondary canvas in Scroll OFF.
            self._relayout_linked_secondary()
        self._sync_secondary_sidebar_selection()
        self._syncing_secondary_page = True
        try:
            tab.currentPageChanged.emit(tab.current_page, tab.page_count)
        finally:
            self._syncing_secondary_page = False
        QTimer.singleShot(0, lambda idx=index: self._scroll_linked_secondary_to_page(idx))

    def _scroll_linked_secondary_to_page(self, index: int):
        if self._secondary_canvas is None or self._secondary_scroll is None:
            return
        rect = self._secondary_canvas.page_rects.get(index)
        if rect is None:
            self._relayout_linked_secondary()
            rect = self._secondary_canvas.page_rects.get(index)
        if rect is not None:
            self._secondary_scroll.verticalScrollBar().setValue(max(0, round(rect.top() - 18)))
            self._secondary_scroll.horizontalScrollBar().setValue(max(0, round(rect.left() - 15)) if rect.width() > self._secondary_scroll.viewport().width() else 0)

    def _chat_focus_layout_paused(self) -> bool:
        """Avoid expensive PDF raster/layout work while the document pane slides away."""
        try:
            main_window = self.window()
            return bool(getattr(main_window, "_chat_focus_mode", False) or
                        getattr(main_window, "_chat_focus_transition_active", False))
        except RuntimeError:
            return False

    def _relayout_linked_secondary(self):
        if self._chat_focus_layout_paused():
            self._layout_deferred_by_focus = True
            return
        secondary = self._linked_view_secondary
        if (self._secondary_canvas is not None and self._secondary_scroll is not None
                and secondary is not None and not getattr(secondary, "_document_closing", False)
                and getattr(secondary, "doc", None) is not None
                and not bool(getattr(secondary.doc, "is_closed", False))):
            width = self._secondary_scroll.viewport().width()
            height = self._secondary_scroll.viewport().height()
            self._secondary_canvas.set_viewport_size(width, height)
            self.restore_chat_viewport_anchors()
            # Annotation geometry helpers on DocumentTab use its canonical canvas.
            # Keep that invisible canvas at the same scale/layout as this visible pane.
            if self._linked_view_secondary is not None:
                self._linked_view_secondary.canvas.set_viewport_size(width, height)

    def _linked_zoom_secondary(self, factor: float, anchor: QPoint | None = None):
        """Smoothly scale the real linked PDF canvas, then commit one high-res layout."""
        tab = self._linked_view_secondary
        canvas = self._secondary_canvas
        scroll_area = self._secondary_scroll
        if tab is None or canvas is None or scroll_area is None:
            return
        factor = max(0.50, min(2.0, float(factor)))
        if self._secondary_zoom_target_scale is None:
            if tab.fit_mode != "custom":
                tab.custom_base_fit_mode = tab.fit_mode if tab.fit_mode in ("width", "page") else "width"
                tab.custom_scale = 1.0
                tab.fit_mode = "custom"
            self._secondary_zoom_base_scale = max(0.05, float(tab.custom_scale))
            viewport = scroll_area.viewport()
            anchor = self._zoom_anchor_line(scroll_area, anchor)
            self._secondary_zoom_anchor_point = QPoint(anchor)
            canvas_anchor = QPointF(scroll_area.horizontalScrollBar().value() + anchor.x(),
                                    scroll_area.verticalScrollBar().value() + anchor.y())
            canvas.set_zoom_visual_transform(1.0, canvas_anchor)
            self._secondary_zoom_visual_current_factor = 1.0
            self._secondary_zoom_visual_target_factor = 1.0
            self._secondary_zoom_commit_pending = False
            self._secondary_zoom_target_scale = self._secondary_zoom_base_scale
        self._secondary_zoom_target_scale = max(
            0.12, min(6.0, float(self._secondary_zoom_target_scale) * factor))
        base = max(0.05, float(self._secondary_zoom_base_scale or tab.custom_scale or 1.0))
        self._secondary_zoom_visual_target_factor = self._secondary_zoom_target_scale / base
        self._secondary_zoom_commit_pending = False
        if not self._zoom_animation_timer.isActive():
            self._zoom_animation_timer.start()
        self._secondary_zoom_timer.start()


    def _on_secondary_document_page_changed(self, current: int, _total: int):
        if self._syncing_secondary_page:
            return
        self._sync_secondary_sidebar_selection()
        if self._secondary_canvas is not None:
            self._secondary_canvas.update()
            QTimer.singleShot(0, lambda idx=int(current): self._scroll_linked_secondary_to_page(idx))

    def _sync_secondary_sidebar_selection(self):
        tab = self._linked_view_secondary
        if tab is None:
            return
        item = self._secondary_thumbnails.item(tab.current_page)
        if item and self._secondary_thumbnails.currentItem() is not item:
            self._secondary_thumbnails.blockSignals(True)
            self._secondary_thumbnails.setCurrentItem(item)
            self._secondary_thumbnails.blockSignals(False)

    def _on_secondary_scroll(self, _value):
        tab = self._linked_view_secondary
        if tab is None or self._secondary_canvas is None or self._secondary_scroll is None:
            return
        if not tab.scroll_mode or not self._secondary_canvas.page_rects:
            return
        visible = QRectF(self._secondary_scroll.horizontalScrollBar().value(), self._secondary_scroll.verticalScrollBar().value(),
                         self._secondary_scroll.viewport().width(), self._secondary_scroll.viewport().height())
        candidates = [(idx, rect) for idx, rect in self._secondary_canvas.page_rects.items() if rect.intersects(visible)]
        if not candidates:
            return
        target_line = visible.top() + min(visible.height() * 0.42, 260)
        selected = min(candidates, key=lambda pair: abs(pair[1].center().y() - target_line))[0]
        if selected != tab.current_page:
            tab.current_page = max(0, min(selected, tab.page_count - 1))
            self._syncing_secondary_page = True
            try:
                tab.currentPageChanged.emit(tab.current_page, tab.page_count)
            finally:
                self._syncing_secondary_page = False
            self._sync_secondary_sidebar_selection()

    def _schedule_sidebar_metrics_update(self):
        timer = getattr(self, "_sidebar_metrics_timer", None)
        if timer is not None:
            timer.start()

    def _update_sidebar_thumbnail_metrics(self):
        """Fit thumbnail rows to their viewport so the sidebar never scrolls horizontally."""
        lists = [self.thumbnails]
        if self._secondary_thumbnails is not None:
            lists.append(self._secondary_thumbnails)
        linked = self._linked_view_secondary is not None
        for list_widget in lists:
            try:
                viewport_width = max(68, int(list_widget.viewport().width()) - 4)
                item_width = min(180 if not linked else 118, viewport_width)
                icon_width = min(78 if not linked else 54, max(30, item_width - (36 if not linked else 22)))
                icon_height = max(38, int(round(icon_width * 1.22)))
                list_widget.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
                list_widget.setIconSize(QSize(icon_width, icon_height))
                item_height = max(70, icon_height + 17)
                for index in range(list_widget.count()):
                    item = list_widget.item(index)
                    if item is not None:
                        item.setSizeHint(QSize(item_width, item_height))
            except (RuntimeError, AttributeError):
                continue

    def _build_thumbnails(self):
        self.thumbnails.clear()
        self.thumbnails.setUpdatesEnabled(False)
        try:
            linked = self._linked_view_secondary is not None
            icon_w, icon_h = (54, 70) if linked else (78, 95)
            item_w, item_h = (74, 88) if linked else (142, 112)
            revisions = getattr(self, "page_render_versions", None) or [self.render_version] * self.page_count
            thumb_cache = getattr(self, "_thumbnail_cache", None)
            if thumb_cache is None:
                self._thumbnail_cache = OrderedDict()
                thumb_cache = self._thumbnail_cache
            for i in range(self.page_count):
                page_revision = int(revisions[i]) if i < len(revisions) else int(self.render_version)
                # Render at ~2.2x display resolution, then downsample once with
                # SmoothTransformation. Avoid enlarging the old 0.15x raster.
                # A modest extra quality bump over the previous sidebar pass.
                # Render at ~2.9x the displayed icon size and downsample only once.
                # The cache tag changes so earlier, softer sidebar icons are not reused.
                sidebar_render_px = max(icon_w, icon_h) * 2.9
                cache_key = (int(i), page_revision, bool(self.dark_mode),
                             bool(self.smart_page_theme), str(self.bg_color),
                             str(self.ink_color), icon_w, icon_h, "sidebar-hq-v4",
                             int(round(sidebar_render_px)))
                qpix = thumb_cache.get(cache_key)
                if qpix is not None and not qpix.isNull():
                    thumb_cache.move_to_end(cache_key)
                else:
                    page = self.doc.load_page(i)
                    page_rect = page.rect
                    max_page_side = max(float(page_rect.width), float(page_rect.height), 1.0)
                    render_scale = min(0.82, sidebar_render_px / max_page_side)
                    pix = page.get_pixmap(matrix=fitz.Matrix(render_scale, render_scale), alpha=False, annots=True)
                    img = Image.frombytes("RGB", (pix.width, pix.height), pix.samples)
                    img = apply_page_theme_to_image(
                        img, self.dark_mode, self.bg_color, self.ink_color,
                        smart=self.smart_page_theme,
                    )
                    qpix = QPixmap.fromImage(image_to_qimage(img)).scaled(
                        icon_w, icon_h, Qt.AspectRatioMode.KeepAspectRatio,
                        Qt.TransformationMode.SmoothTransformation,
                    )
                    thumb_cache[cache_key] = qpix
                    thumb_cache.move_to_end(cache_key)
                    while len(thumb_cache) > self._thumbnail_cache_limit:
                        thumb_cache.popitem(last=False)
                item = QListWidgetItem(QIcon(qpix), str(i + 1))
                item.setToolTip(f"Page {i + 1}")
                item.setData(Qt.ItemDataRole.UserRole, i)
                item.setSizeHint(QSize(item_w, item_h))
                self.thumbnails.addItem(item)
            self.thumbnails.setIconSize(QSize(icon_w, icon_h))
        except Exception:
            pass
        self.thumbnails.setUpdatesEnabled(True)
        if self.thumbnails.count():
            self._sync_sidebar_selection()

    def _build_outline(self):
        self.outline.clear()
        try:
            toc = self.doc.get_toc()
            stack = []
            for level, title, page_num, *rest in toc:
                item = QTreeWidgetItem([title or f"Page {page_num}"])
                item.setData(0, Qt.ItemDataRole.UserRole, max(0, int(page_num) - 1))
                item.setToolTip(0, f"Page {page_num}")
                while len(stack) >= level:
                    stack.pop()
                if stack:
                    stack[-1].addChild(item)
                else:
                    self.outline.addTopLevelItem(item)
                stack.append(item)
            self.outline.expandToDepth(1)
        except Exception:
            pass
        if self.outline.topLevelItemCount() == 0:
            item = QTreeWidgetItem(["No table of contents in this PDF"])
            item.setDisabled(True)
            self.outline.addTopLevelItem(item)

    def resizeEvent(self, event):
        super().resizeEvent(event)
        if getattr(self, "_page_overview_active", False):
            try:
                self._page_overview_overlay.setGeometry(self._page_overview_host.rect())
                self._page_overview_overlay.raise_()
            except RuntimeError:
                pass
        # The outer workspace splitter may resize the whole PDF host while the
        # linked secondary canvas is nested two levels below it. Reflow both panes.
        if getattr(self, "_linked_view_secondary", None) is not None:
            if self._chat_focus_layout_paused():
                self._layout_deferred_by_focus = True
            else:
                self._schedule_layout(0)

    def _schedule_layout(self, delay_ms: int = 0):
        """Coalesce layout requests into the next Qt event-loop turn.

        During animated panel resizing the PDF must follow the changing viewport
        continuously. Smart Theme now reuses its stable page master, so these cheap
        layout passes do not rerun image processing or allocate resized bitmaps.
        """
        if getattr(self, "_document_closing", False):
            return
        timer = getattr(self, "_layout_timer", None)
        if timer is not None:
            try:
                animating = time.monotonic() < float(
                    getattr(self.window(), "_chat_panel_anim_until", 0.0) or 0.0)
            except Exception:
                animating = False
            if animating:
                # Text-chat open/close: lay the PDF out at most every ~45 ms
                # instead of on every animation frame.
                if not timer.isActive():
                    timer.start(max(45, int(delay_ms)))
                return
            timer.start(max(0, int(delay_ms)))

    @staticmethod
    def _capture_vertical_scroll_anchor(scroll_area, canvas, viewport_fraction: float = 0.42):
        """Capture a page-relative reading point so horizontal resizing cannot jump the PDF vertically."""
        if scroll_area is None or canvas is None:
            return None
        try:
            bar = scroll_area.verticalScrollBar()
            viewport_height = max(1, int(scroll_area.viewport().height()))
            fraction = max(0.10, min(0.90, float(viewport_fraction)))
            document_y = float(bar.value()) + viewport_height * fraction
            rects = getattr(canvas, "page_rects", {}) or {}
            if not rects:
                return {"fallback_ratio": (bar.value() / max(1, bar.maximum())),
                        "viewport_fraction": fraction}
            page_index, page_rect = min(
                rects.items(),
                key=lambda pair: (0.0 if pair[1].top() <= document_y <= pair[1].bottom()
                                  else min(abs(document_y - pair[1].top()), abs(document_y - pair[1].bottom())))
            )
            page_height = max(1.0, float(page_rect.height()))
            page_fraction = max(0.0, min(1.0, (document_y - float(page_rect.top())) / page_height))
            return {"page_index": int(page_index), "page_fraction": page_fraction,
                    "viewport_fraction": fraction}
        except (RuntimeError, AttributeError, TypeError, ValueError):
            return None

    @staticmethod
    def _restore_vertical_scroll_anchor(scroll_area, canvas, anchor):
        if scroll_area is None or canvas is None or not anchor:
            return
        try:
            bar = scroll_area.verticalScrollBar()
            viewport_height = max(1, int(scroll_area.viewport().height()))
            page_index = anchor.get("page_index")
            rect = (getattr(canvas, "page_rects", {}) or {}).get(int(page_index)) if page_index is not None else None
            if rect is not None:
                document_y = float(rect.top()) + max(0.0, min(1.0, float(anchor.get("page_fraction", 0.0)))) * float(rect.height())
                target = document_y - viewport_height * max(0.10, min(0.90, float(anchor.get("viewport_fraction", 0.42))))
            else:
                ratio = max(0.0, min(1.0, float(anchor.get("fallback_ratio", 0.0))))
                target = ratio * bar.maximum()
            bar.setValue(max(bar.minimum(), min(bar.maximum(), int(round(target)))))
        except (RuntimeError, AttributeError, TypeError, ValueError):
            pass

    def begin_chat_viewport_anchor_preservation(self):
        """Keep the same PDF reading point visible while the chat panel changes canvas width."""
        anchors = []
        primary = self._capture_vertical_scroll_anchor(self.scroll, self.canvas)
        if primary is not None:
            anchors.append((self.scroll, self.canvas, primary))
        if self._secondary_scroll is not None and self._secondary_canvas is not None:
            secondary = self._capture_vertical_scroll_anchor(self._secondary_scroll, self._secondary_canvas)
            if secondary is not None:
                anchors.append((self._secondary_scroll, self._secondary_canvas, secondary))
        self._chat_open_viewport_anchors = anchors
        self.restore_chat_viewport_anchors()

    def restore_chat_viewport_anchors(self):
        for scroll_area, canvas, anchor in list(getattr(self, "_chat_open_viewport_anchors", []) or []):
            self._restore_vertical_scroll_anchor(scroll_area, canvas, anchor)

    def end_chat_viewport_anchor_preservation(self):
        self.restore_chat_viewport_anchors()
        self._chat_open_viewport_anchors = []

    def _relayout(self):
        if getattr(self, "_document_closing", False):
            return
        if self._chat_focus_layout_paused():
            self._layout_deferred_by_focus = True
            return
        self._layout_deferred_by_focus = False
        doc = getattr(self, "doc", None)
        if doc is None or bool(getattr(doc, "is_closed", False)):
            return
        if not hasattr(self, "scroll"):
            return
        self.canvas.set_viewport_size(self.scroll.viewport().width(), self.scroll.viewport().height())
        self.restore_chat_viewport_anchors()
        self.canvas.update()
        self._relayout_linked_secondary()
        self.restore_chat_viewport_anchors()

    def scroll_continuously(self, angle_delta: int = 0, pixel_delta: int = 0) -> bool:
        """Scroll the complete multi-page PDF vertically; never turn pages with the wheel here."""
        delta = int(pixel_delta or angle_delta)
        if not delta:
            return False
        bar = self.scroll.verticalScrollBar()
        if pixel_delta:
            amount = int(pixel_delta)
        else:
            # One mouse-wheel notch scrolls a few text lines, just like a normal document.
            lines = max(3, int(round(bar.singleStep() * 3)))
            amount = int((angle_delta / 120.0) * lines)
        if amount:
            bar.setValue(bar.value() - amount)
        return True

    def handle_page_wheel(self, delta: int) -> bool:
        """Legacy page-turn helper; deliberately unused by the main continuous PDF viewer."""
        return False

    def eventFilter(self, obj, event):
        # This is a temporary QApplication event filter while page overview is
        # active. Intercept ShortcutOverride BEFORE Qt's shortcut map evaluates
        # the main window's Escape/Left/Right bindings, then consume KeyPress.
        # It works regardless of whether focus is on the grid, viewport, header,
        # close button, or another child inside the full-area overlay.
        if getattr(self, "_page_overview_active", False):
            if event.type() in (QEvent.Type.ShortcutOverride, QEvent.Type.KeyPress):
                key_to_action = {
                    Qt.Key.Key_Escape: "escape",
                    Qt.Key.Key_Return: "open",
                    Qt.Key.Key_Enter: "open",
                    Qt.Key.Key_Left: "left",
                    Qt.Key.Key_Right: "right",
                    Qt.Key.Key_Up: "up",
                    Qt.Key.Key_Down: "down",
                }
                action_name = key_to_action.get(event.key())
                modifiers = event.modifiers()
                modified = bool(modifiers & (
                    Qt.KeyboardModifier.ControlModifier
                    | Qt.KeyboardModifier.AltModifier
                    | Qt.KeyboardModifier.MetaModifier
                ))
                if action_name and not modified:
                    event.accept()
                    if event.type() == QEvent.Type.KeyPress:
                        self._handle_page_overview_key(action_name)
                    return True
        if obj is getattr(self, "_page_overview_host", None) and event.type() == QEvent.Type.Resize:
            if getattr(self, "_page_overview_active", False):
                try:
                    self._page_overview_overlay.setGeometry(obj.rect())
                    self._page_overview_overlay.raise_()
                    self._schedule_page_overview_preview_refresh()
                except RuntimeError:
                    pass
        if event.type() == QEvent.Type.Resize and (
            obj is self.sidebar or obj is self.thumbnails or obj is self.thumbnails.viewport()
            or obj is self._secondary_thumbnails or obj is self._secondary_thumbnails.viewport()
        ):
            self._schedule_sidebar_metrics_update()
        if obj is self._secondary_scroll.viewport() if self._secondary_scroll is not None else False:
            if event.type() == QEvent.Type.Resize:
                if self._chat_focus_layout_paused():
                    self._layout_deferred_by_focus = True
                else:
                    # Keep the document geometry in sync with each animation frame;
                    # cached page masters make this a cheap paint-time scale operation.
                    self._schedule_layout(0)
            elif event.type() == QEvent.Type.Wheel and event.modifiers() & Qt.KeyboardModifier.ControlModifier:
                delta = event.angleDelta().y()
                if delta == 0:
                    delta = event.pixelDelta().y()
                if delta and self._linked_view_secondary is not None:
                    # Use the pointer's vertical coordinate only; the zoom helper
                    # replaces X with the horizontal viewport center to prevent
                    # unwanted sideways auto-centering toward the cursor.
                    anchor = self._secondary_scroll.viewport().mapFromGlobal(
                        event.globalPosition().toPoint()
                    )
                    self._linked_zoom_secondary(
                        math.exp(delta / (1320.0 if event.angleDelta().y() else 390.0)),
                        anchor,
                    )
                    return True
        # During _build_ui(), sidebar resize events can arrive before the reader
        # QScrollArea is assigned. QWidget also exposes a callable scroll() method,
        # so guard the attribute and its type before accessing viewport().
        reader_scroll = getattr(self, "scroll", None)
        reader_viewport = reader_scroll.viewport() if isinstance(reader_scroll, QScrollArea) else None
        if reader_viewport is not None and obj is reader_viewport:
            if event.type() == QEvent.Type.Resize:
                if self._chat_focus_layout_paused():
                    self._layout_deferred_by_focus = True
                else:
                    # Keep the document geometry in sync with each animation frame;
                    # cached page masters make this a cheap paint-time scale operation.
                    self._schedule_layout(0)
            elif event.type() == QEvent.Type.Wheel and event.modifiers() & Qt.KeyboardModifier.ControlModifier:
                delta = event.angleDelta().y()
                if delta == 0:
                    delta = event.pixelDelta().y()
                if delta:
                    anchor = self.scroll.viewport().mapFromGlobal(event.globalPosition().toPoint())
                    self.zoom_by(math.exp(delta / (1320.0 if event.angleDelta().y() else 390.0)), anchor)
                    return True
            elif event.type() == QEvent.Type.Wheel and not self.scroll_mode:
                delta = event.angleDelta().y() or event.pixelDelta().y()
                if delta:
                    # A zoomed single page can still be panned internally. Turn to
                    # the previous/next page only when the current page reaches the
                    # corresponding vertical edge (or already fits the viewport).
                    bar = self.scroll.verticalScrollBar()
                    at_edge = ((delta > 0 and bar.value() <= bar.minimum()) or
                               (delta < 0 and bar.value() >= bar.maximum()))
                    if at_edge:
                        now = time.monotonic()
                        if now - self._last_page_wheel_turn >= 0.28:
                            step = 2 if self.book_mode else 1
                            self.go_to_page(self.current_page + (-step if delta > 0 else step))
                            self._last_page_wheel_turn = now
                        return True
            # In Scroll mode, QScrollArea handles normal wheel/touchpad gestures
            # as continuous vertical document scrolling.
            elif event.type() == QEvent.Type.NativeGesture:
                try:
                    if event.gestureType() == Qt.NativeGestureType.ZoomNativeGesture:
                        factor = max(0.94, min(1.06, math.exp(float(event.value()) * 0.45)))
                        if abs(factor - 1.0) > 0.001:
                            self.zoom_by(factor, self.scroll.viewport().mapFromGlobal(QCursor.pos()))
                            return True
                except Exception:
                    pass
        return super().eventFilter(obj, event)

    def _on_scroll(self, _value):
        # Page rotation temporarily changes page geometry and scrollbar ranges.
        # Ignore those programmatic scroll updates until the rotated target page
        # has been restored to the reading center; otherwise the active page can
        # jump to its neighbour and the next Rotate click acts on that page.
        if getattr(self, "_rotation_selection_lock", False):
            return
        if not self.scroll_mode or not self.canvas.page_rects:
            return

        scroll_y = float(self.scroll.verticalScrollBar().value())
        viewport_height = float(self.scroll.viewport().height())
        if viewport_height <= 0:
            return

        if self.book_mode:
            # In Book + Scroll mode the sidebar follows complete spreads only:
            # pages 1–2, 3–4, 5–6, etc. Never derive the selection from whichever
            # individual page happens to intersect the viewport.
            #
            # Pick the spread whose actual laid-out row center is nearest the
            # viewport's reading center. This remains correct with mixed page
            # sizes/orientations and when two or more spreads are partly visible.
            reading_y = scroll_y + (viewport_height * 0.50)
            spread_rows = []

            for first in range(0, self.page_count, 2):
                rects = [
                    self.canvas.page_rects[index]
                    for index in (first, first + 1)
                    if index in self.canvas.page_rects
                ]
                if not rects:
                    continue

                row_top = min(float(rect.top()) for rect in rects)
                row_bottom = max(float(rect.bottom()) for rect in rects)
                row_center = (row_top + row_bottom) / 2.0
                spread_rows.append((first, row_center))

            if not spread_rows:
                return

            selected = min(
                spread_rows,
                key=lambda row: (abs(row[1] - reading_y), row[0])
            )[0]
            selected = (int(selected) // 2) * 2
        else:
            visible = QRectF(
                self.scroll.horizontalScrollBar().value(),
                scroll_y,
                self.scroll.viewport().width(),
                viewport_height
            )
            candidates = [
                (idx, rect) for idx, rect in self.canvas.page_rects.items()
                if rect.intersects(visible)
            ]
            if not candidates:
                return
            reading_y = scroll_y + (viewport_height * 0.50)
            selected = min(
                candidates,
                key=lambda pair: abs(float(pair[1].center().y()) - reading_y)
            )[0]

        selected = max(0, min(int(selected), max(0, self.page_count - 1)))
        if selected != self.current_page:
            self.current_page = selected
            self._sync_sidebar_selection()
            self.currentPageChanged.emit(self.current_page, self.page_count)

    def _sync_sidebar_selection(self):
        spread_active = bool(self.book_mode and self._linked_view_secondary is None)
        try:
            self.thumbnails.set_book_spread_selection(spread_active)
        except (AttributeError, RuntimeError):
            pass

        page_index = (
            (int(self.current_page) // 2) * 2
            if spread_active else int(self.current_page)
        )

        if spread_active:
            # The list's only visual selection is the custom frame around exactly
            # this spread. Do not also set a Qt current/selected item.
            try:
                self.thumbnails.set_active_spread(page_index)
                self.thumbnails.ensure_active_spread_visible()
            except (AttributeError, RuntimeError):
                pass
        else:
            item = self.thumbnails.item(page_index)
            if item and self.thumbnails.currentItem() is not item:
                self.thumbnails.blockSignals(True)
                self.thumbnails.setCurrentItem(item)
                self.thumbnails.blockSignals(False)
            else:
                self.thumbnails.viewport().update()

    def _thumbnail_clicked(self, item):
        self.go_to_page(int(item.data(Qt.ItemDataRole.UserRole)))

    def _outline_clicked(self, item, _column=0):
        page = item.data(0, Qt.ItemDataRole.UserRole)
        if page is not None:
            self.go_to_page(int(page))

    def go_to_page(self, index):
        if not self.page_count:
            return
        index = max(0, min(int(index), self.page_count - 1))
        if self.book_mode:
            index = (index // 2) * 2
        if self.selected_annotation and self.selected_annotation[0] != index:
            self.clear_annotation_selection()
        self.current_page = index
        # In page-at-a-time mode the canvas contains only the active page/spread.
        if not self.scroll_mode:
            self._relayout()
        QTimer.singleShot(0, lambda idx=index: self._scroll_to_page(idx))
        self._sync_sidebar_selection()
        self.currentPageChanged.emit(self.current_page, self.page_count)

    def _scroll_to_page(self, index):
        rect = self.canvas.page_rects.get(index)
        if rect is None:
            self._relayout()
            rect = self.canvas.page_rects.get(index)
        if rect is not None:
            self.scroll.verticalScrollBar().setValue(max(0, round(rect.top() - 18)))
            self.scroll.horizontalScrollBar().setValue(max(0, round(rect.left() - 15)) if rect.width() > self.scroll.viewport().width() else 0)
            self.canvas.update()

    def set_layout_modes(self, book=None, scroll=None):
        """Change Book/Scroll presentation only; never mark or rewrite PDF content."""
        next_book = self.book_mode if book is None else bool(book)
        next_scroll = self.scroll_mode if scroll is None else bool(scroll)
        linked_secondary = self._linked_view_secondary
        if linked_secondary is not None:
            # Book is unavailable in the paired two-document layout, but Scroll
            # ON/OFF must work for both visible document panes.
            next_book = False
        if (next_book, next_scroll) == (self.book_mode, self.scroll_mode):
            return
        self.book_mode, self.scroll_mode = next_book, next_scroll
        if self.book_mode:
            self.current_page = (self.current_page // 2) * 2
        self.canvas.clear_cache()
        if linked_secondary is not None:
            linked_secondary.book_mode = False
            linked_secondary.scroll_mode = next_scroll
            linked_secondary.canvas.clear_cache()
            self._relayout_linked_secondary()
        self._relayout()
        self.go_to_page(self.current_page)
        if linked_secondary is not None:
            self._sync_secondary_sidebar_selection()
            QTimer.singleShot(0, self._relayout_linked_secondary)
        self.documentChanged.emit()

    def set_view_mode(self, mode):
        """Legacy preset API retained for existing app integrations."""
        value = str(mode or "").lower()
        if value == "book":
            self.set_layout_modes(book=True)
        elif value == "single":
            self.set_layout_modes(book=False, scroll=False)
        elif value == "continuous":
            self.set_layout_modes(book=False, scroll=True)

    def _capture_fit_view_anchor(self, scroll_area=None, canvas=None):
        """Capture the page position under the viewport's reading line before refitting."""
        scroll_area = scroll_area or self.scroll
        canvas = canvas or self.canvas
        if scroll_area is None or canvas is None:
            return None
        try:
            viewport = scroll_area.viewport()
            anchor_x = max(0, int(viewport.width() // 2))
            anchor_y = max(0, min(int(viewport.height() * 0.42), 260))
            doc_x = float(scroll_area.horizontalScrollBar().value() + anchor_x)
            doc_y = float(scroll_area.verticalScrollBar().value() + anchor_y)
            page_index, page_rect = canvas._page_at(QPointF(doc_x, doc_y))

            if page_index < 0 or page_rect.isEmpty():
                # The reading line can fall in the gap between pages or in the
                # side margin of a narrow page. Anchor to the nearest laid-out page
                # instead of falling back to page zero.
                best_distance = float("inf")
                for candidate_index, candidate_rect in canvas.page_rects.items():
                    dx = max(candidate_rect.left() - doc_x, 0.0, doc_x - candidate_rect.right())
                    dy = max(candidate_rect.top() - doc_y, 0.0, doc_y - candidate_rect.bottom())
                    distance = dx * dx + dy * dy
                    if distance < best_distance:
                        best_distance = distance
                        page_index, page_rect = candidate_index, candidate_rect

            if page_index < 0 or page_rect.isEmpty():
                page_index = max(0, min(int(self.current_page), self.page_count - 1))
                page_rect = canvas.page_rects.get(page_index)
                if page_rect is None or page_rect.isEmpty():
                    return None

            frac_x = max(0.0, min(1.0, (doc_x - page_rect.left()) / max(page_rect.width(), 1.0)))
            frac_y = max(0.0, min(1.0, (doc_y - page_rect.top()) / max(page_rect.height(), 1.0)))
            return (int(page_index), frac_x, frac_y, anchor_x, anchor_y)
        except (RuntimeError, AttributeError, ValueError):
            return None

    def _restore_fit_view_anchor(self, anchor, scroll_area=None, canvas=None):
        """Restore the same normalized point of the same PDF page after refitting."""
        if not anchor:
            return
        scroll_area = scroll_area or self.scroll
        canvas = canvas or self.canvas
        if scroll_area is None or canvas is None:
            return
        try:
            page_index, frac_x, frac_y, anchor_x, anchor_y = anchor
            page_rect = canvas.page_rects.get(int(page_index))
            if page_rect is None or page_rect.isEmpty():
                return
            target_x = page_rect.left() + float(frac_x) * page_rect.width() - int(anchor_x)
            target_y = page_rect.top() + float(frac_y) * page_rect.height() - int(anchor_y)
            scroll_area.horizontalScrollBar().setValue(round(target_x))
            scroll_area.verticalScrollBar().setValue(round(target_y))
            canvas.update()
        except (RuntimeError, AttributeError, TypeError, ValueError):
            return

    def set_fit_mode(self, mode):
        if mode not in ("width", "page"):
            return
        self._zoom_timer.stop()
        self._zoom_target_scale = None
        self._zoom_anchor_state = None
        self._zoom_base_scale = None
        self._zoom_visual_current_factor = 1.0
        self._zoom_visual_target_factor = 1.0
        self._zoom_commit_pending = False
        self._secondary_zoom_timer.stop()
        self._secondary_zoom_target_scale = None
        self._secondary_zoom_anchor_state = None
        self._secondary_zoom_base_scale = None
        self._secondary_zoom_visual_current_factor = 1.0
        self._secondary_zoom_visual_target_factor = 1.0
        self._secondary_zoom_commit_pending = False
        if hasattr(self, "_zoom_animation_timer"):
            self._zoom_animation_timer.stop()
        if getattr(self, "canvas", None) is not None:
            self.canvas.clear_zoom_visual_transform()
        if getattr(self, "_secondary_canvas", None) is not None:
            self._secondary_canvas.clear_zoom_visual_transform()

        # Fit operations must preserve the page and reading position currently
        # visible. Calling go_to_page() here used to snap the viewport to the top
        # of current_page (and could appear to jump back to page one when the
        # tracked page lagged behind the scroll position).
        linked_primary = None
        linked_scroll = None
        linked_canvas = None
        try:
            host = self.window()
            primary_lookup = getattr(host, "_linked_primary_for_path", None)
            candidate = primary_lookup(self.path) if callable(primary_lookup) else None
            if candidate is not None and getattr(candidate, "_linked_view_secondary", None) is self:
                linked_primary = candidate
                linked_scroll = candidate._secondary_scroll
                linked_canvas = candidate._secondary_canvas
        except (RuntimeError, AttributeError):
            linked_primary = None

        if linked_primary is not None and linked_scroll is not None and linked_canvas is not None:
            linked_primary._secondary_zoom_timer.stop()
            linked_primary._secondary_zoom_target_scale = None
            linked_primary._secondary_zoom_anchor_state = None
            anchor = self._capture_fit_view_anchor(linked_scroll, linked_canvas)
            self.fit_mode = mode
            self.custom_base_fit_mode = mode
            linked_primary._relayout_linked_secondary()
            QTimer.singleShot(0, lambda a=anchor, owner=linked_primary, sc=linked_scroll, cv=linked_canvas:
                              self._restore_fit_view_anchor(a, sc, cv)
                              if getattr(owner, "_linked_view_secondary", None) is self else None)
        else:
            anchor = self._capture_fit_view_anchor(self.scroll, self.canvas)
            self.fit_mode = mode
            self.custom_base_fit_mode = mode
            self._relayout()
            QTimer.singleShot(0, lambda a=anchor: self._restore_fit_view_anchor(a))

        self.documentChanged.emit()

    def _zoom_anchor_line(self, scroll_area, pointer_anchor=None):
        """Use the viewport's horizontal center and only the pointer's vertical Y.

        This creates a horizontal zoom anchor line instead of pinning a single
        X/Y point under the pointer. The page stays centered horizontally while
        zoom still follows the paragraph/region under the mouse vertically.
        """
        if scroll_area is None:
            return QPoint()
        viewport = scroll_area.viewport()
        width = max(1, int(viewport.width()))
        height = max(1, int(viewport.height()))
        pointer_y = height // 2 if pointer_anchor is None else int(pointer_anchor.y())
        pointer_y = max(0, min(height - 1, pointer_y))
        return QPoint(width // 2, pointer_y)

    def _capture_zoom_anchor_state(self, scroll_area, canvas, anchor=None, fallback_page=None):
        if scroll_area is None or canvas is None:
            return None
        # Ignore pointer X completely. Capture the page point at the horizontal
        # viewport center and at the pointer's Y coordinate.
        anchor = self._zoom_anchor_line(scroll_area, anchor)
        old_x = scroll_area.horizontalScrollBar().value() + int(anchor.x())
        old_y = scroll_area.verticalScrollBar().value() + int(anchor.y())
        page_index, page_rect = canvas._page_at(QPointF(old_x, old_y))
        if page_index < 0 or page_rect is None or page_rect.isEmpty():
            page_index = int(self.current_page if fallback_page is None else fallback_page)
            page_rect = canvas.page_rects.get(page_index)
        if page_rect is None or page_rect.isEmpty():
            return None
        frac_x = max(0.0, min(1.0, (old_x - page_rect.left()) / max(page_rect.width(), 1.0)))
        frac_y = max(0.0, min(1.0, (old_y - page_rect.top()) / max(page_rect.height(), 1.0)))
        return (int(page_index), frac_x, frac_y, int(anchor.x()), int(anchor.y()))

    @staticmethod
    def _restore_zoom_anchor_state(state, scroll_area, canvas):
        if not state or scroll_area is None or canvas is None:
            return
        page_index, frac_x, frac_y, anchor_x, anchor_y = state
        rect = canvas.page_rects.get(int(page_index))
        if rect is None or rect.isEmpty():
            return
        scroll_area.horizontalScrollBar().setValue(round(rect.left() + frac_x * rect.width() - anchor_x))
        scroll_area.verticalScrollBar().setValue(round(rect.top() + frac_y * rect.height() - anchor_y))

    def _tick_zoom_animation(self):
        """Interpolate the real canvas paint transform at display refresh cadence."""
        still_animating = False
        alpha = 0.47  # more responsive catch-up while retaining smooth easing
        epsilon = 0.0012

        if self._zoom_target_scale is not None and self.canvas is not None:
            current = float(self._zoom_visual_current_factor)
            target = float(self._zoom_visual_target_factor)
            delta = target - current
            if abs(delta) <= epsilon:
                current = target
            else:
                current += delta * alpha
                still_animating = True
            self._zoom_visual_current_factor = current
            self.canvas.set_zoom_visual_scale(current)
            if self._zoom_commit_pending and not still_animating and abs(target - current) <= epsilon:
                self._advance_primary_zoom()

        if (self._secondary_zoom_target_scale is not None
                and self._secondary_canvas is not None):
            current = float(self._secondary_zoom_visual_current_factor)
            target = float(self._secondary_zoom_visual_target_factor)
            delta = target - current
            secondary_animating = abs(delta) > epsilon
            if secondary_animating:
                current += delta * alpha
                still_animating = True
            else:
                current = target
            self._secondary_zoom_visual_current_factor = current
            self._secondary_canvas.set_zoom_visual_scale(current)
            if (self._secondary_zoom_commit_pending and not secondary_animating
                    and abs(target - current) <= epsilon):
                self._advance_secondary_zoom()

        # Do not keep repainting at 60Hz after the visual scale has settled;
        # the debounce/commit timers will finalize the high-resolution layout.
        if not still_animating:
            self._zoom_animation_timer.stop()

    def _advance_primary_zoom(self):
        """Commit the settled real-canvas scale and render the final page sharply."""
        target_value = self._zoom_target_scale
        if (self._document_closing or target_value is None or self.doc is None
                or getattr(self.doc, "is_closed", True)):
            self._zoom_timer.stop()
            self._zoom_target_scale = None
            if getattr(self, "canvas", None) is not None:
                self.canvas.clear_zoom_visual_transform()
            return
        target = max(0.12, min(6.0, float(target_value)))
        base = max(0.05, float(self._zoom_base_scale or self.custom_scale or 1.0))
        target_visual = target / base
        if abs(float(self._zoom_visual_current_factor) - target_visual) > 0.0012:
            self._zoom_commit_pending = True
            if not self._zoom_animation_timer.isActive():
                self._zoom_animation_timer.start()
            return

        scroll_area, canvas = self.scroll, self.canvas
        anchor = self._zoom_anchor_point or QPoint(scroll_area.viewport().width() // 2,
                                                   scroll_area.viewport().height() // 2)
        anchor_state = self._capture_zoom_anchor_state(scroll_area, canvas, anchor)
        self.custom_scale = target
        self.fit_mode = "custom"
        self._zoom_target_scale = None
        self._zoom_base_scale = None
        self._zoom_visual_current_factor = 1.0
        self._zoom_visual_target_factor = 1.0
        self._zoom_commit_pending = False
        canvas.clear_zoom_visual_transform()
        self._zoom_anchor_state = anchor_state
        self._relayout()
        self._restore_zoom_anchor_state(anchor_state, scroll_area, canvas)
        self._zoom_anchor_point = None
        self.documentChanged.emit()

    def _advance_secondary_zoom(self):
        """Commit the settled linked-canvas scale and refresh only its own document."""
        tab = self._linked_view_secondary
        target_value = self._secondary_zoom_target_scale
        if (tab is None or self._secondary_canvas is None or self._secondary_scroll is None
                or target_value is None or getattr(tab, "_document_closing", False)):
            self._secondary_zoom_timer.stop()
            self._secondary_zoom_target_scale = None
            if self._secondary_canvas is not None:
                self._secondary_canvas.clear_zoom_visual_transform()
            return
        target = max(0.12, min(6.0, float(target_value)))
        base = max(0.05, float(self._secondary_zoom_base_scale or tab.custom_scale or 1.0))
        target_visual = target / base
        if abs(float(self._secondary_zoom_visual_current_factor) - target_visual) > 0.0012:
            self._secondary_zoom_commit_pending = True
            if not self._zoom_animation_timer.isActive():
                self._zoom_animation_timer.start()
            return

        scroll_area, canvas = self._secondary_scroll, self._secondary_canvas
        anchor = self._secondary_zoom_anchor_point or QPoint(
            scroll_area.viewport().width() // 2, scroll_area.viewport().height() // 2)
        anchor_state = self._capture_zoom_anchor_state(
            scroll_area, canvas, anchor, fallback_page=tab.current_page)
        tab.custom_scale = target
        tab.fit_mode = "custom"
        self._secondary_zoom_target_scale = None
        self._secondary_zoom_base_scale = None
        self._secondary_zoom_visual_current_factor = 1.0
        self._secondary_zoom_visual_target_factor = 1.0
        self._secondary_zoom_commit_pending = False
        canvas.clear_zoom_visual_transform()
        self._secondary_zoom_anchor_state = anchor_state
        self._relayout_linked_secondary()
        self._restore_zoom_anchor_state(anchor_state, scroll_area, canvas)
        self._secondary_zoom_anchor_point = None
        tab.documentChanged.emit()


    def zoom_by(self, factor: float, anchor: QPoint | None = None):
        if self.doc is None or getattr(self.doc, "is_closed", True):
            return
        # Route the supplementary tab's zoom to the visible right-hand canvas.
        try:
            host = self.window()
            primary_lookup = getattr(host, "_linked_primary_for_path", None)
            primary = primary_lookup(self.path) if callable(primary_lookup) else None
            if primary is not None and getattr(primary, "_linked_view_secondary", None) is self:
                primary._linked_zoom_secondary(factor, anchor)
                return
        except (RuntimeError, AttributeError):
            pass

        factor = max(0.50, min(2.0, float(factor)))
        if self._zoom_target_scale is None:
            if self.fit_mode != "custom":
                self.custom_base_fit_mode = self.fit_mode if self.fit_mode in ("width", "page") else "width"
                self.custom_scale = 1.0
                self.fit_mode = "custom"
            self._zoom_base_scale = max(0.05, float(self.custom_scale))
            viewport = self.scroll.viewport()
            anchor = self._zoom_anchor_line(self.scroll, anchor)
            self._zoom_anchor_point = QPoint(anchor)
            canvas_anchor = QPointF(self.scroll.horizontalScrollBar().value() + anchor.x(),
                                    self.scroll.verticalScrollBar().value() + anchor.y())
            self.canvas.set_zoom_visual_transform(1.0, canvas_anchor)
            self._zoom_visual_current_factor = 1.0
            self._zoom_visual_target_factor = 1.0
            self._zoom_commit_pending = False
            self._zoom_target_scale = self._zoom_base_scale

        self._zoom_target_scale = max(0.12, min(6.0, float(self._zoom_target_scale) * factor))
        base = max(0.05, float(self._zoom_base_scale or self.custom_scale or 1.0))
        self._zoom_visual_target_factor = self._zoom_target_scale / base
        self._zoom_commit_pending = False
        if not self._zoom_animation_timer.isActive():
            self._zoom_animation_timer.start()
        self._zoom_timer.start()


    def fit_width(self):
        self.set_fit_mode("width")

    def fit_page(self):
        self.set_fit_mode("page")

    def set_tool(self, tool):
        self.active_tool = tool
        cursor = (Qt.CursorShape.ArrowCursor if tool == "select" else
                  Qt.CursorShape.OpenHandCursor if tool == "pan" else Qt.CursorShape.CrossCursor)
        self.canvas.setCursor(cursor)
        self.canvas.update()
        # A linked pair shares the active annotation/selection tool, while each
        # document still writes annotations into its own PDF.
        try:
            main = self.window()
            stack = getattr(main, "tabs", None)
            if stack is not None:
                for i in range(stack.count()):
                    primary = stack.widget(i)
                    if getattr(primary, "_linked_view_secondary", None) is self:
                        if primary._secondary_canvas is not None:
                            primary._secondary_canvas.setCursor(
                                Qt.CursorShape.ArrowCursor if tool == "select" else
                                Qt.CursorShape.OpenHandCursor if tool == "pan" else Qt.CursorShape.CrossCursor)
                            primary._secondary_canvas.update()
                    elif getattr(primary, "_linked_view_secondary", None) is not None and primary._linked_view_secondary is not self:
                        continue
        except (RuntimeError, AttributeError):
            pass
        if self._linked_view_secondary is not None and self._secondary_canvas is not None:
            self._linked_view_secondary.active_tool = tool
            self._secondary_canvas.setCursor(
                Qt.CursorShape.ArrowCursor if tool == "select" else
                Qt.CursorShape.OpenHandCursor if tool == "pan" else Qt.CursorShape.CrossCursor)
            self._secondary_canvas.update()

    def _update_linked_display(self, page_index=None, clear_cache=False):
        """Refresh the paired visible canvas when this tab is the supplementary PDF."""
        try:
            main = self.window()
            stack = getattr(main, "tabs", None)
            if stack is None:
                return
            for i in range(stack.count()):
                primary = stack.widget(i)
                if getattr(primary, "_linked_view_secondary", None) is self:
                    canvas = getattr(primary, "_secondary_canvas", None)
                    if canvas is not None:
                        if clear_cache:
                            canvas.clear_cache()
                        elif page_index is not None:
                            canvas.invalidate_page(int(page_index))
                        else:
                            canvas.update()
                    if clear_cache:
                        primary._build_linked_thumbnails(self)
        except Exception:
            pass

    def select_annotation(self, page_index: int, xref: int, additive: bool = False):
        """Select one annotation, optionally adding it to the current selection."""
        item = (int(page_index), int(xref))
        self.selected_page_link = None
        if additive:
            if item not in self.selected_annotations:
                self.selected_annotations.append(item)
        else:
            self.selected_annotations = [item]
        self.selected_annotation = item
        self.annotationSelectionChanged.emit(True)
        self.canvas.update()
        self._update_linked_display()

    def set_annotation_selection(self, items):
        """Replace selection with a de-duplicated list of page/xref pairs."""
        unique = []
        for page_index, xref in items or []:
            item = (int(page_index), int(xref))
            if item not in unique:
                unique.append(item)
        self.selected_page_link = None
        self.selected_annotations = unique
        self.selected_annotation = unique[-1] if unique else None
        self.annotationSelectionChanged.emit(bool(unique))
        self.canvas.update()
        self._update_linked_display()

    def select_page_link(self, identity: tuple):
        """Select a native PDF link without opening it (single-click behavior)."""
        self.selected_annotation = None
        self.selected_annotations = []
        self.selected_page_link = tuple(identity) if identity is not None else None
        self.annotationSelectionChanged.emit(self.selected_page_link is not None)
        self.canvas.update()
        self._update_linked_display()

    def clear_annotation_selection(self):
        had_selection = (self.selected_annotation is not None or bool(self.selected_annotations)
                         or self.selected_page_link is not None)
        if had_selection:
            self.selected_annotation = None
            self.selected_annotations = []
            self.selected_page_link = None
            self.annotationSelectionChanged.emit(False)
            self.canvas.update()
            self._update_linked_display()

    def delete_selected_annotation(self) -> bool:
        """Delete selected annotations or a selected native PDF link as one undoable action."""
        if self.selected_page_link is not None:
            identity = tuple(self.selected_page_link)
            try:
                page_index = int(identity[0])
                page = self.doc.load_page(page_index)
                # PyMuPDF may expose only previously materialized links until the
                # page is reloaded. Reload unconditionally so a new link is found
                # even when the same page already contains other links.
                try:
                    page = self.doc.reload_page(page)
                except Exception:
                    pass
                matches = []
                for link_info in list(page.get_links() or []):
                    if link_info.get("from") is None:
                        continue
                    kind = int(link_info.get("kind", -1))
                    raw_page = int(link_info.get("page", -1))
                    target_page = raw_page + 1 if kind == fitz.LINK_GOTO and raw_page >= 0 else None
                    link_identity = self.canvas._page_link_identity(
                        page_index, link_info["from"], target_page, kind, str(link_info.get("uri") or "")
                    )
                    if link_identity == identity:
                        matches.append(link_info)
                overlays = list(self._link_overlay_rects.get(page_index, []))
                target_rect = tuple(identity[1]) if len(identity) > 1 else ()
                kept_overlays = []
                removed_overlay = False
                for raw in overlays:
                    values = tuple(raw)
                    rect_key = tuple(round(float(v), 2) for v in values[:4])
                    target_key = int(values[4]) if len(values) >= 5 else None
                    if rect_key == target_rect and (identity[2] is None or target_key == int(identity[2])):
                        removed_overlay = True
                    else:
                        kept_overlays.append(raw)
                if not matches and not removed_overlay:
                    self.clear_annotation_selection()
                    return False
                self._record_undo()
                for link_info in matches:
                    page.delete_link(link_info)
                if kept_overlays:
                    self._link_overlay_rects[page_index] = kept_overlays
                else:
                    self._link_overlay_rects.pop(page_index, None)
                self.selected_page_link = None
                self.annotationSelectionChanged.emit(False)
                self._changed(page_index)
                self.canvas.update()
                self._update_linked_display(page_index)
                return True
            except Exception as exc:
                QMessageBox.warning(self, APP_NAME, f"Could not remove the selected link:\n{exc}")
                return False

        selected = list(self.selected_annotations or ([self.selected_annotation] if self.selected_annotation else []))
        if not selected:
            return False
        try:
            by_page = {}
            for index, xref in selected:
                by_page.setdefault(int(index), set()).add(int(xref))
            existing = []
            for index, xrefs in by_page.items():
                page = self.doc.load_page(index)
                for annot in list(page.annots() or []):
                    if int(annot.xref) in xrefs:
                        existing.append((index, int(annot.xref)))
            if not existing:
                self.clear_annotation_selection()
                return False
            self._record_undo()
            changed_pages = set()
            for index, xref in existing:
                page = self.doc.load_page(index)
                target = next((a for a in (page.annots() or []) if int(a.xref) == xref), None)
                if target is not None:
                    page.delete_annot(target)
                    changed_pages.add(index)
            self.selected_annotation = None
            self.selected_annotations = []
            self.annotationSelectionChanged.emit(False)
            for index in changed_pages:
                self._changed(index)
            self.canvas.update()
            self._update_linked_display()
            return True
        except Exception as exc:
            QMessageBox.warning(self, APP_NAME, f"Could not remove selected annotations:\n{exc}")
            return False

    def copy_annotation(self, page_index: int, xref: int) -> bool:
        """Copy a native annotation into Engo's in-app annotation clipboard."""
        global _ANNOTATION_CLIPBOARD
        try:
            page = self.doc.load_page(int(page_index))
            annot = next((a for a in (page.annots() or []) if int(a.xref) == int(xref)), None)
            if annot is None:
                return False

            def serialize_points(value):
                if hasattr(value, "x") and hasattr(value, "y"):
                    return [float(value.x), float(value.y)]
                if isinstance(value, (tuple, list)):
                    return [serialize_points(part) for part in value]
                return value

            annot_type = annot.type or (0, "")
            _ANNOTATION_CLIPBOARD = {
                "type": int(annot_type[0]),
                "type_name": str(annot_type[1] or "PDF annotation"),
                "rect": [float(v) for v in fitz.Rect(annot.rect)],
                "vertices": serialize_points(annot.vertices or []),
                "info": dict(annot.info or {}),
                "colors": dict(annot.colors or {}),
                "opacity": float(annot.opacity) if annot.opacity is not None else -1.0,
                "rotation": int(getattr(annot, "rotation", -1)),
                "line_ends": [int(v) for v in (getattr(annot, "line_ends", (0, 0)) or (0, 0))],
                "border": dict(annot.border or {}),
                "default_appearance": str(self.doc.xref_get_key(int(annot.xref), "DA")[1]
                                           if self.doc.xref_get_key(int(annot.xref), "DA")[0] == "string" else ""),
            }
            try:
                main = self.window()
                if hasattr(main, "show_status"):
                    main.show_status("Annotation copied · right-click an empty place and choose Paste here")
            except Exception:
                pass
            return True
        except Exception as exc:
            QMessageBox.warning(self, APP_NAME, f"Could not copy annotation:\n{exc}")
            return False

    def paste_annotation(self, page_index: int, destination: fitz.Point) -> bool:
        """Paste the copied annotation with its top-left corner at the target point."""
        global _ANNOTATION_CLIPBOARD
        data = _ANNOTATION_CLIPBOARD
        if not isinstance(data, dict):
            return False
        try:
            page = self.doc.load_page(int(page_index))
            source_rect = fitz.Rect(data.get("rect", (0, 0, 0, 0)))
            target = fitz.Point(destination)
            dx, dy = float(target.x - source_rect.x0), float(target.y - source_rect.y0)
            subtype = int(data.get("type", -1))
            vertices = data.get("vertices") or []
            info = dict(data.get("info") or {})
            colors = dict(data.get("colors") or {})
            border = dict(data.get("border") or {})
            opacity = float(data.get("opacity", -1.0))
            content = str(info.get("content") or "")
            new_rect = fitz.Rect(source_rect.x0 + dx, source_rect.y0 + dy,
                                 source_rect.x1 + dx, source_rect.y1 + dy) & page.rect
            if new_rect.is_empty:
                return False

            self._record_undo()
            if subtype == getattr(fitz, "PDF_ANNOT_HIGHLIGHT", 8):
                quads = []
                for n in range(0, len(vertices) - 3, 4):
                    pts = [fitz.Point(float(vertices[n + k][0]) + dx,
                                      float(vertices[n + k][1]) + dy) for k in range(4)]
                    quads.append(fitz.Quad(pts[0], pts[1], pts[2], pts[3]))
                if not quads:
                    raise RuntimeError("The copied highlight has no quadrilateral geometry.")
                updated = page.add_highlight_annot(quads)
            elif subtype == getattr(fitz, "PDF_ANNOT_INK", 15):
                strokes = vertices
                if strokes and isinstance(strokes[0], (tuple, list)) and len(strokes[0]) >= 2 \
                        and isinstance(strokes[0][0], (int, float)):
                    strokes = [strokes]
                shifted_strokes = []
                for stroke in strokes:
                    points = [(float(point[0]) + dx, float(point[1]) + dy) for point in stroke]
                    if len(points) >= 2:
                        shifted_strokes.append(points)
                if not shifted_strokes:
                    raise RuntimeError("The copied pen mark has no stroke geometry.")
                updated = page.add_ink_annot(shifted_strokes)
            elif subtype == getattr(fitz, "PDF_ANNOT_LINE", 3):
                if len(vertices) < 2:
                    raise RuntimeError("The copied line has no editable point geometry.")
                shifted = [(float(pt[0]) + dx, float(pt[1]) + dy) for pt in vertices[:2]]
                updated = page.add_line_annot(shifted[0], shifted[1])
            elif subtype == getattr(fitz, "PDF_ANNOT_POLYGON", 6):
                shifted = [(float(pt[0]) + dx, float(pt[1]) + dy) for pt in vertices]
                if len(shifted) < 3:
                    raise RuntimeError("The copied polygon has no editable point geometry.")
                updated = page.add_polygon_annot(shifted)
            elif subtype == getattr(fitz, "PDF_ANNOT_POLY_LINE", 7):
                shifted = [(float(pt[0]) + dx, float(pt[1]) + dy) for pt in vertices]
                if len(shifted) < 2:
                    raise RuntimeError("The copied polyline has no editable point geometry.")
                updated = page.add_polyline_annot(shifted)
            elif subtype == getattr(fitz, "PDF_ANNOT_CIRCLE", 5):
                updated = page.add_circle_annot(new_rect)
            elif subtype == getattr(fitz, "PDF_ANNOT_TEXT", 0):
                updated = page.add_text_annot(fitz.Point(new_rect.x0, new_rect.y0), content or "Note")
            elif subtype == getattr(fitz, "PDF_ANNOT_FREE_TEXT", 2):
                # FreeText stores its text color/font in /DA; its fill is reported
                # by PyMuPDF as the annotation's stroke color, and set_colors()
                # is not supported for this subtype.
                da_match = re.search(
                    r"([0-9.]+)\s+([0-9.]+)\s+([0-9.]+)\s+rg\s+/([A-Za-z0-9]+)\s+([0-9.]+)\s+Tf",
                    str(data.get("default_appearance") or "")
                )
                text_color = tuple(float(da_match.group(i)) for i in (1, 2, 3)) if da_match else (0.15, 0.2, 0.3)
                font_name = da_match.group(4) if da_match else "Helv"
                font_size = float(da_match.group(5)) if da_match else 11.0
                fill_color = colors.get("stroke") or None
                updated = page.add_freetext_annot(new_rect, content or "Text", fontsize=font_size,
                                                   fontname=font_name, text_color=text_color,
                                                   fill_color=fill_color, align=0)
            elif subtype == getattr(fitz, "PDF_ANNOT_SQUARE", 4):
                updated = page.add_rect_annot(new_rect)
            else:
                raise RuntimeError(f"Copy/paste is not yet supported for {data.get('type_name', 'this annotation type')}.")

            if subtype == getattr(fitz, "PDF_ANNOT_LINE", 3):
                line_ends = data.get("line_ends") or [0, 0]
                updated.set_line_ends(int(line_ends[0]), int(line_ends[1]))
            if subtype != getattr(fitz, "PDF_ANNOT_FREE_TEXT", 2) and (colors.get("stroke") or colors.get("fill")):
                updated.set_colors(stroke=colors.get("stroke"), fill=colors.get("fill"))
            if border.get("width") is not None and subtype not in (
                    getattr(fitz, "PDF_ANNOT_TEXT", 0), getattr(fitz, "PDF_ANNOT_HIGHLIGHT", 8)):
                updated.set_border(width=float(border.get("width", 1.0)))
            if opacity >= 0:
                updated.set_opacity(opacity)
            copied_rotation = int(data.get("rotation", -1))
            point_geometry_types = {
                getattr(fitz, "PDF_ANNOT_HIGHLIGHT", 8), getattr(fitz, "PDF_ANNOT_INK", 15),
                getattr(fitz, "PDF_ANNOT_LINE", 3), getattr(fitz, "PDF_ANNOT_POLYGON", 6),
                getattr(fitz, "PDF_ANNOT_POLY_LINE", 7),
            }
            if copied_rotation >= 0 and subtype not in point_geometry_types:
                try:
                    updated.set_rotation(copied_rotation)
                except Exception:
                    pass
            if info.get("title") or info.get("content"):
                updated.set_info(title=str(info.get("title") or ""), content=content)
            updated.update()
            new_xref = int(updated.xref)
            self.selected_annotation = (int(page_index), new_xref)
            self.selected_annotations = [(int(page_index), new_xref)]
            self.annotationSelectionChanged.emit(True)
            self._changed(int(page_index))
            self.canvas.update()
            self._update_linked_display(int(page_index))
            return True
        except Exception as exc:
            QMessageBox.warning(self, APP_NAME, f"Could not paste annotation:\n{exc}")
            self.canvas.update()
            return False

    def rotate_annotation(self, page_index: int, xref: int, delta_degrees: float, canvas=None):
        """Rotate an annotation in the exact visible page coordinate system.

        The preview uses canvas pixels (where +Y points down).  Commit now uses
        that same coordinate frame, including the page's own rotation and display
        scaling, before mapping points back into PDF coordinates.  This keeps the
        pivot fixed and prevents apparent growth / vertical drift on rotated pages.
        """
        canvas = canvas or self.canvas
        snapshot = None
        created_new = False
        page_index, xref = int(page_index), int(xref)
        try:
            delta = float(delta_degrees)
            if abs(delta) < 0.5:
                return False
            snapshot = self.doc.tobytes(deflate=True)
            page = self.doc.load_page(page_index)
            annot = next((a for a in (page.annots() or []) if int(a.xref) == xref), None)
            if annot is None:
                self.clear_annotation_selection()
                return False

            original_xref = xref
            subtype = int((annot.type or (0, ""))[0])
            info = dict(annot.info or {})
            colors = dict(annot.colors or {})
            opacity = annot.opacity
            border = dict(annot.border or {})
            original_line_ends = tuple(getattr(annot, "line_ends", (0, 0)) or (0, 0))
            current_rotation = max(0, int(getattr(annot, "rotation", -1)))

            highlight_type = getattr(fitz, "PDF_ANNOT_HIGHLIGHT", 8)
            ink_type = getattr(fitz, "PDF_ANNOT_INK", 15)
            line_type = getattr(fitz, "PDF_ANNOT_LINE", 3)
            polygon_type = getattr(fitz, "PDF_ANNOT_POLYGON", 6)
            polyline_type = getattr(fitz, "PDF_ANNOT_POLY_LINE", 7)
            square_type = getattr(fitz, "PDF_ANNOT_SQUARE", 4)
            circle_type = getattr(fitz, "PDF_ANNOT_CIRCLE", 5)
            free_text_type = getattr(fitz, "PDF_ANNOT_FREE_TEXT", 2)

            vertices = list(annot.vertices or [])
            source_rect = fitz.Rect(annot.rect)
            geometry_kind = None
            geometry_groups = []

            if subtype in (square_type, circle_type):
                source_cx = (source_rect.x0 + source_rect.x1) / 2.0
                source_cy = (source_rect.y0 + source_rect.y1) / 2.0
                if subtype == circle_type:
                    source_points = [fitz.Point(
                        source_cx + source_rect.width/2.0*math.cos(2.0*math.pi*i/96.0),
                        source_cy + source_rect.height/2.0*math.sin(2.0*math.pi*i/96.0))
                        for i in range(96)]
                else:
                    source_points = [fitz.Point(source_rect.x0, source_rect.y0),
                                     fitz.Point(source_rect.x1, source_rect.y0),
                                     fitz.Point(source_rect.x1, source_rect.y1),
                                     fitz.Point(source_rect.x0, source_rect.y1)]
                geometry_kind = "polygon"
                geometry_groups = [source_points]
            elif subtype == highlight_type:
                if len(vertices) < 4:
                    raise RuntimeError("The highlight has no editable geometry.")
                geometry_kind = "highlight"
                geometry_groups = [vertices[i:i+4] for i in range(0, len(vertices)-3, 4)]
            elif subtype == ink_type:
                if vertices and isinstance(vertices[0], (tuple, list)) and len(vertices[0]) >= 2 \
                        and isinstance(vertices[0][0], (int, float)):
                    vertices = [vertices]
                geometry_kind = "ink"
                geometry_groups = [list(stroke) for stroke in vertices if len(stroke) >= 2]
            elif subtype in (line_type, polygon_type, polyline_type):
                if len(vertices) < (2 if subtype != polygon_type else 3):
                    raise RuntimeError("The selected shape has no editable point geometry.")
                geometry_kind = "line" if subtype == line_type else ("polygon" if subtype == polygon_type else "polyline")
                geometry_groups = [vertices]

            if geometry_kind:
                display_rect = canvas.page_rects.get(page_index, QRectF())
                if display_rect.isEmpty():
                    raise RuntimeError("The PDF page is not currently visible in the active canvas.")
                page_rect = fitz.Rect(page.rect)
                page_rotation = page.rotation_matrix
                page_derotation = page.derotation_matrix
                display_w = max(float(display_rect.width()), 1.0)
                display_h = max(float(display_rect.height()), 1.0)
                page_w = max(float(page_rect.width), 1.0)
                page_h = max(float(page_rect.height), 1.0)

                def pdf_to_canvas(point):
                    rotated = fitz.Point(point) * page_rotation
                    return (float(display_rect.left()) + rotated.x / page_w * display_w,
                            float(display_rect.top()) + rotated.y / page_h * display_h)

                def canvas_to_pdf(point):
                    x, y = point
                    page_point = fitz.Point(
                        (x-float(display_rect.left())) * page_w / display_w,
                        (y-float(display_rect.top())) * page_h / display_h,
                    )
                    return page_point * page_derotation

                # Convert all actual vertices to the same canvas coordinates used by
                # the pointer/preview. Rotate around the object's visual bounding-box
                # center; never use the screen/window origin or a global X/Y axis.
                display_groups = [[pdf_to_canvas(point) for point in group]
                                  for group in geometry_groups]
                all_display_points = [point for group in display_groups for point in group]
                if not all_display_points:
                    raise RuntimeError("The selected shape has no points to rotate.")
                min_x = min(point[0] for point in all_display_points)
                max_x = max(point[0] for point in all_display_points)
                min_y = min(point[1] for point in all_display_points)
                max_y = max(point[1] for point in all_display_points)
                center_x, center_y = (min_x+max_x)/2.0, (min_y+max_y)/2.0
                radians = math.radians(delta)
                cosine, sine = math.cos(radians), math.sin(radians)

                def rotate_point(point):
                    dx, dy = point[0]-center_x, point[1]-center_y
                    turned = (center_x + dx*cosine - dy*sine,
                              center_y + dx*sine + dy*cosine)
                    return canvas_to_pdf(turned)

                rotated_groups = [[rotate_point(point) for point in group]
                                  for group in display_groups]
                self._record_undo()
                # Add the rotated geometry first; remove the old annotation only
                # after MuPDF confirms that the replacement is present.
                if geometry_kind == "highlight":
                    quads = [fitz.Quad(points[0], points[1], points[2], points[3])
                             for points in rotated_groups if len(points) >= 4]
                    updated = page.add_highlight_annot(quads)
                elif geometry_kind == "ink":
                    strokes = [[(float(point.x), float(point.y)) for point in group]
                               for group in rotated_groups if len(group) >= 2]
                    updated = page.add_ink_annot(strokes)
                elif geometry_kind == "line":
                    points = rotated_groups[0]
                    updated = page.add_line_annot(points[0], points[1])
                elif geometry_kind == "polyline":
                    updated = page.add_polyline_annot(rotated_groups[0])
                else:
                    updated = page.add_polygon_annot(rotated_groups[0])
                created_new = True
                if geometry_kind == "line":
                    updated.set_line_ends(int(original_line_ends[0]), int(original_line_ends[1]))
                if colors.get("stroke") or colors.get("fill"):
                    updated.set_colors(stroke=colors.get("stroke"), fill=colors.get("fill"))
                if border.get("width") is not None and subtype != highlight_type:
                    updated.set_border(width=float(border.get("width", 1.0)))
                if opacity is not None and opacity >= 0:
                    updated.set_opacity(opacity)
                if info.get("content") or info.get("title"):
                    updated.set_info(title=str(info.get("title") or ""),
                                     content=str(info.get("content") or ""))
                updated.update()
                new_xref = int(updated.xref)

                page = self.doc.load_page(page_index)
                current_items = list(page.annots() or [])
                if not any(int(item.xref) == new_xref for item in current_items):
                    raise RuntimeError("The rotated annotation could not be verified.")
                old = next((item for item in current_items if int(item.xref) == original_xref), None)
                if old is None:
                    raise RuntimeError("The original annotation disappeared before rotation completed.")
                page.delete_annot(old)
                remaining = [int(item.xref) for item in (page.annots() or [])]
                if original_xref in remaining or new_xref not in remaining:
                    raise RuntimeError("MuPDF could not replace the original shape safely.")
                xref = new_xref
            else:
                supported = {
                    getattr(fitz, "PDF_ANNOT_CARET", 14),
                    free_text_type,
                    getattr(fitz, "PDF_ANNOT_FILE_ATTACHMENT", 17),
                    getattr(fitz, "PDF_ANNOT_STAMP", 13),
                    getattr(fitz, "PDF_ANNOT_TEXT", 0),
                }
                if subtype not in supported:
                    raise RuntimeError("Rotation is not supported for this PDF annotation type.")
                self._record_undo()
                target_rotation = current_rotation + delta
                if subtype == free_text_type:
                    target_rotation = round(target_rotation / 90.0) * 90.0
                annot.set_rotation(int(round(target_rotation)))
                annot.update()
                refreshed_page = self.doc.load_page(page_index)
                if not any(int(item.xref) == original_xref for item in (refreshed_page.annots() or [])):
                    raise RuntimeError("The rotated annotation could not be verified.")

            old_item = (page_index, original_xref)
            new_item = (page_index, int(xref))
            self.selected_annotation = new_item
            current_items = list(self.selected_annotations or [old_item])
            self.selected_annotations = [new_item if item == old_item else item for item in current_items]
            if new_item not in self.selected_annotations:
                self.selected_annotations.append(new_item)
            self.annotationSelectionChanged.emit(True)
            self._changed(page_index)
            self.canvas.update()
            self._update_linked_display(page_index)
            return True
        except Exception as exc:
            if snapshot is not None and created_new:
                try:
                    self._replace_document_state(snapshot)
                except Exception:
                    pass
            QMessageBox.warning(self, APP_NAME, f"Could not rotate annotation:\n{exc}")
            self.canvas.update()
            self._update_linked_display(page_index)
            return False

    def normalize_annotation_shape(self, page_index: int, xref: int, click_pos=None, canvas=None) -> bool:
        """Regularize a hand-drawn/native shape on deliberate double-click.

        Quadrilaterals become squares, triangles become equilateral, ellipses become
        circles, and lines snap to their nearest horizontal/vertical orientation.
        Double-clicking a line endpoint instead adds a closed arrowhead there.
        All calculations use the target PDF page coordinate frame.
        """
        canvas = canvas or self.canvas
        page_index, xref = int(page_index), int(xref)
        snapshot = None
        created_xref = None
        try:
            page = self.doc.load_page(page_index)
            annot = next((a for a in (page.annots() or []) if int(a.xref) == xref), None)
            if annot is None:
                return False
            subtype = int((annot.type or (0, ""))[0])
            original_subtype = subtype
            line_type = getattr(fitz, "PDF_ANNOT_LINE", 3)
            polygon_type = getattr(fitz, "PDF_ANNOT_POLYGON", 6)
            square_type = getattr(fitz, "PDF_ANNOT_SQUARE", 4)
            circle_type = getattr(fitz, "PDF_ANNOT_CIRCLE", 5)
            ink_type = getattr(fitz, "PDF_ANNOT_INK", 15)
            raw_annotation_vertices = list(annot.vertices or [])
            vertices = [] if subtype == ink_type else [fitz.Point(v) for v in raw_annotation_vertices]
            source_rect = fitz.Rect(annot.rect)
            source_is_ink = False
            # A hand-drawn shape may intentionally remain an Ink annotation if
            # the initial recognizer was uncertain. Double-click gives it a second,
            # explicit chance to recognize and regularize the user's approximation.
            if subtype == ink_type:
                raw_ink = raw_annotation_vertices
                if raw_ink and isinstance(raw_ink[0], (tuple, list)) and len(raw_ink[0]) >= 2 \
                        and isinstance(raw_ink[0][0], (int, float)):
                    raw_ink = [raw_ink]
                recognized_ink = None
                for stroke in raw_ink:
                    try:
                        stroke_points = [fitz.Point(float(pt[0]), float(pt[1])) if isinstance(pt, (tuple, list))
                                         else fitz.Point(pt) for pt in stroke]
                        candidate = _recognize_pen_shape(stroke_points)
                        if candidate and candidate.get("kind") in ("line", "square", "rectangle", "circle", "triangle", "quadrilateral"):
                            recognized_ink = candidate
                            break
                    except Exception:
                        continue
                if recognized_ink:
                    source_is_ink = True
                    kind = str(recognized_ink.get("kind"))
                    if kind == "line":
                        subtype = line_type
                        vertices = [fitz.Point(pt) for pt in recognized_ink.get("points", [])]
                    elif kind in ("triangle", "quadrilateral"):
                        subtype = polygon_type
                        vertices = [fitz.Point(pt) for pt in recognized_ink.get("points", [])]
                    elif kind == "circle":
                        subtype = circle_type
                        source_rect = fitz.Rect(recognized_ink.get("rect"))
                    else:
                        # Treat every four-sided freehand loop as a square when
                        # the user explicitly double-clicks to regularize it.
                        subtype = square_type
                        source_rect = fitz.Rect(recognized_ink.get("rect"))
            info = dict(annot.info or {})
            colors = dict(annot.colors or {})
            opacity = float(annot.opacity)
            border = dict(annot.border or {})

            # A line endpoint double-click means "add arrowhead". A double-click
            # elsewhere on the line straightens it to the closer page-axis direction.
            if subtype == line_type and len(vertices) >= 2:
                page_rect_display = canvas.page_rects.get(page_index, QRectF())
                display_ends = [canvas._pdf_to_display(page_index, page_rect_display, p) for p in vertices[:2]]
                nearest_index = None
                if click_pos is not None and not page_rect_display.isEmpty():
                    distances = [math.hypot(QPointF(click_pos).x()-p.x(), QPointF(click_pos).y()-p.y())
                                 for p in display_ends]
                    nearest = min(range(2), key=lambda i: distances[i])
                    line_display_length = math.hypot(display_ends[1].x()-display_ends[0].x(),
                                                     display_ends[1].y()-display_ends[0].y())
                    # Keep the endpoint hit radius below half the length of short
                    # lines, so a double-click at their midpoint still straightens
                    # the line instead of accidentally creating an arrowhead.
                    endpoint_tolerance = min(22.0, max(5.0, line_display_length * 0.24),
                                             max(4.0, line_display_length * 0.38))
                    if distances[nearest] <= endpoint_tolerance:
                        nearest_index = nearest

                # Native Line annotations can update the endpoint style in place.
                # For a recognized Ink line, recreate it as a true PDF Line first.
                if nearest_index is not None and not source_is_ink:
                    old_ends = tuple(getattr(annot, "line_ends", (fitz.PDF_ANNOT_LE_NONE, fitz.PDF_ANNOT_LE_NONE)) or
                                     (fitz.PDF_ANNOT_LE_NONE, fitz.PDF_ANNOT_LE_NONE))
                    start_code = int(old_ends[0]) if len(old_ends) > 0 else int(fitz.PDF_ANNOT_LE_NONE)
                    end_code = int(old_ends[1]) if len(old_ends) > 1 else int(fitz.PDF_ANNOT_LE_NONE)
                    if nearest_index == 0:
                        start_code = int(fitz.PDF_ANNOT_LE_OPEN_ARROW)
                    else:
                        end_code = int(fitz.PDF_ANNOT_LE_OPEN_ARROW)
                    self._record_undo()
                    page = self.doc.load_page(page_index)
                    current = next((a for a in (page.annots() or []) if int(a.xref) == xref), None)
                    if current is None:
                        return False
                    current.set_line_ends(start_code, end_code)
                    current.update()
                    self.selected_annotation = (page_index, xref)
                    self.selected_annotations = [(page_index, xref)]
                    self.annotationSelectionChanged.emit(True)
                    self._changed(page_index)
                    canvas.update()
                    self._update_linked_display(page_index)
                    return True

                # Mid-line double-click snaps to the nearest horizontal/vertical
                # orientation. For a recognized Ink line, endpoint double-click
                # preserves its direction and adds the arrow to the clicked end.
                a, b = display_ends
                dx, dy = b.x()-a.x(), b.y()-a.y()
                length = max(2.0, math.hypot(dx, dy))
                center = QPointF((a.x()+b.x())/2.0, (a.y()+b.y())/2.0)
                if nearest_index is not None:
                    p1, p2 = a, b
                elif abs(dx) >= abs(dy):
                    p1 = QPointF(center.x()-length/2.0, center.y())
                    p2 = QPointF(center.x()+length/2.0, center.y())
                else:
                    p1 = QPointF(center.x(), center.y()-length/2.0)
                    p2 = QPointF(center.x(), center.y()+length/2.0)
                replacement_points = [canvas._display_to_pdf(page_index, page_rect_display, p)
                                      for p in (p1, p2)]
                snapshot = self.doc.tobytes(deflate=True)
                self._record_undo()
                page = self.doc.load_page(page_index)
                current = next((a for a in (page.annots() or []) if int(a.xref) == xref), None)
                if current is None:
                    raise RuntimeError("The line changed before it could be straightened.")
                updated = page.add_line_annot(replacement_points[0], replacement_points[1])
                created_xref = int(updated.xref)
                if source_is_ink:
                    old_ends = (int(fitz.PDF_ANNOT_LE_NONE), int(fitz.PDF_ANNOT_LE_NONE))
                else:
                    old_ends = tuple(getattr(current, "line_ends", (0, 0)) or (0, 0))
                start_code, end_code = int(old_ends[0]), int(old_ends[1])
                if nearest_index == 0:
                    start_code = int(fitz.PDF_ANNOT_LE_OPEN_ARROW)
                elif nearest_index == 1:
                    end_code = int(fitz.PDF_ANNOT_LE_OPEN_ARROW)
                updated.set_line_ends(start_code, end_code)
                if colors.get("stroke") or colors.get("fill"):
                    updated.set_colors(stroke=colors.get("stroke"), fill=colors.get("fill"))
                if border.get("width") is not None:
                    updated.set_border(width=float(border.get("width", 1.0)))
                if opacity >= 0:
                    updated.set_opacity(opacity)
                updated.set_info(title=str(info.get("title") or ""), content=str(info.get("content") or ""))
                updated.update()
                page = self.doc.load_page(page_index)
                current_items = list(page.annots() or [])
                if not any(int(a.xref) == created_xref for a in current_items):
                    raise RuntimeError("The straightened line could not be verified.")
                old = next((a for a in current_items if int(a.xref) == xref), None)
                if old is None:
                    raise RuntimeError("The original line could not be found for replacement.")
                page.delete_annot(old)
                remaining = {int(a.xref) for a in (page.annots() or [])}
                if xref in remaining or created_xref not in remaining:
                    raise RuntimeError("The line could not be replaced safely.")

            else:
                replacement_kind = None
                replacement_data = None
                if subtype == polygon_type and len(vertices) == 3:
                    # Preserve the centroid and approximate size/orientation, but
                    # rebuild all three points at exactly equal angular intervals.
                    cx = sum(p.x for p in vertices) / 3.0
                    cy = sum(p.y for p in vertices) / 3.0
                    side_lengths = [math.hypot(vertices[(i+1)%3].x-vertices[i].x,
                                               vertices[(i+1)%3].y-vertices[i].y) for i in range(3)]
                    side = sum(side_lengths) / 3.0
                    radius = side / math.sqrt(3.0)
                    angle = math.atan2(vertices[0].y-cy, vertices[0].x-cx)
                    replacement_data = [fitz.Point(cx + radius*math.cos(angle + 2*math.pi*i/3),
                                                   cy + radius*math.sin(angle + 2*math.pi*i/3))
                                        for i in range(3)]
                    replacement_kind = "polygon"
                elif subtype == polygon_type and len(vertices) == 4:
                    # Find the dominant edge orientation by averaging double angles;
                    # opposite edges then reinforce the same square orientation.
                    cx = sum(p.x for p in vertices) / 4.0
                    cy = sum(p.y for p in vertices) / 4.0
                    edges = [(vertices[(i+1)%4].x-vertices[i].x,
                              vertices[(i+1)%4].y-vertices[i].y) for i in range(4)]
                    c2 = s2 = total = 0.0
                    for ex, ey in edges:
                        length = math.hypot(ex, ey)
                        if length <= 1e-6:
                            continue
                        angle = math.atan2(ey, ex)
                        c2 += length*math.cos(2*angle)
                        s2 += length*math.sin(2*angle)
                        total += length
                    theta = 0.5*math.atan2(s2, c2) if total else 0.0
                    ux, uy = math.cos(theta), math.sin(theta)
                    vx, vy = -uy, ux
                    projections_u = [(p.x-cx)*ux + (p.y-cy)*uy for p in vertices]
                    projections_v = [(p.x-cx)*vx + (p.y-cy)*vy for p in vertices]
                    span_u = max(projections_u)-min(projections_u)
                    span_v = max(projections_v)-min(projections_v)
                    side = max(2.0, (span_u+span_v)/2.0)
                    h = side/2.0
                    replacement_data = [
                        fitz.Point(cx-h*ux-h*vx, cy-h*uy-h*vy),
                        fitz.Point(cx+h*ux-h*vx, cy+h*uy-h*vy),
                        fitz.Point(cx+h*ux+h*vx, cy+h*uy+h*vy),
                        fitz.Point(cx-h*ux+h*vx, cy-h*uy+h*vy),
                    ]
                    replacement_kind = "polygon"
                elif subtype == circle_type:
                    cx = (source_rect.x0+source_rect.x1)/2.0
                    cy = (source_rect.y0+source_rect.y1)/2.0
                    diameter = max(2.0, (source_rect.width+source_rect.height)/2.0)
                    replacement_kind = "circle"
                    replacement_data = fitz.Rect(cx-diameter/2.0, cy-diameter/2.0,
                                                  cx+diameter/2.0, cy+diameter/2.0)
                elif subtype == square_type:
                    cx = (source_rect.x0+source_rect.x1)/2.0
                    cy = (source_rect.y0+source_rect.y1)/2.0
                    side = max(2.0, (source_rect.width+source_rect.height)/2.0)
                    replacement_kind = "square"
                    replacement_data = fitz.Rect(cx-side/2.0, cy-side/2.0,
                                                  cx+side/2.0, cy+side/2.0)
                else:
                    return False

                if replacement_kind == "circle" and abs(source_rect.width-source_rect.height) < 1.0:
                    return False
                if replacement_kind == "square" and abs(source_rect.width-source_rect.height) < 1.0:
                    return False
                if replacement_kind == "polygon" and vertices:
                    # Avoid needless rewrites when the existing geometry is already
                    # within a sub-point tolerance of the regular target.
                    if all(math.hypot(a.x-b.x, a.y-b.y) < 0.35 for a, b in zip(vertices, replacement_data)):
                        return False

                snapshot = self.doc.tobytes(deflate=True)
                self._record_undo()
                page = self.doc.load_page(page_index)
                current = next((a for a in (page.annots() or []) if int(a.xref) == xref), None)
                if current is None:
                    raise RuntimeError("The shape changed before it could be regularized.")
                if replacement_kind == "polygon":
                    updated = page.add_polygon_annot(replacement_data)
                elif replacement_kind == "circle":
                    updated = page.add_circle_annot(replacement_data)
                else:
                    updated = page.add_rect_annot(replacement_data)
                created_xref = int(updated.xref)
                if colors.get("stroke") or colors.get("fill"):
                    updated.set_colors(stroke=colors.get("stroke"), fill=colors.get("fill"))
                if border.get("width") is not None:
                    updated.set_border(width=float(border.get("width", 1.0)))
                if opacity >= 0:
                    updated.set_opacity(opacity)
                updated.set_info(title=str(info.get("title") or ""), content=str(info.get("content") or ""))
                updated.update()
                page = self.doc.load_page(page_index)
                current_items = list(page.annots() or [])
                if not any(int(a.xref) == created_xref for a in current_items):
                    raise RuntimeError("The regularized shape could not be verified.")
                old = next((a for a in current_items if int(a.xref) == xref), None)
                if old is None:
                    raise RuntimeError("The original shape could not be found for replacement.")
                page.delete_annot(old)
                remaining = {int(a.xref) for a in (page.annots() or [])}
                if xref in remaining or created_xref not in remaining:
                    raise RuntimeError("The old shape could not be replaced safely.")

            # Refresh the selected xref after a replacement while keeping the item selected.
            if created_xref is not None:
                xref = int(created_xref)
            self.selected_annotation = (page_index, xref)
            self.selected_annotations = [(page_index, xref)]
            self.annotationSelectionChanged.emit(True)
            self._changed(page_index)
            canvas.update()
            self._update_linked_display(page_index)
            return True
        except Exception as exc:
            try:
                if snapshot is not None:
                    self._replace_document_state(snapshot)
            except Exception:
                pass
            QMessageBox.warning(self, APP_NAME, f"Could not adjust shape:\n{exc}")
            canvas.update()
            self._update_linked_display(page_index)
            return False

    def transform_annotation_vertex(self, page_index: int, xref: int, handle_meta: dict,
                                    target_display_point: QPointF, canvas=None) -> bool:
        """Move exactly one editable vertex in the PDF page's own coordinate frame.

        This deliberately does not scale the annotation's bounding rectangle.
        A dragged endpoint/corner is mapped from the visible, rotated page back
        through that page's derotation matrix, then only its matching PDF vertex
        is replaced. All other vertices remain byte-for-byte at their original
        coordinates, preventing the X/Y plane drift and constrained-looking
        movement caused by AABB scaling.
        """
        canvas = canvas or self.canvas
        page_index, xref = int(page_index), int(xref)
        snapshot = None
        new_xref = None
        try:
            display_page = canvas.page_rects.get(page_index, QRectF())
            if display_page.isEmpty():
                raise RuntimeError("The page is not visible in the active PDF pane.")
            page = self.doc.load_page(page_index)
            annot = next((item for item in (page.annots() or []) if int(item.xref) == xref), None)
            if annot is None:
                self.clear_annotation_selection()
                return False

            subtype = int((annot.type or (0, ""))[0])
            info = dict(annot.info or {})
            colors = dict(annot.colors or {})
            opacity = annot.opacity
            border = dict(annot.border or {})
            original_line_ends = tuple(getattr(annot, "line_ends", (0, 0)) or (0, 0))
            meta = dict(handle_meta or {})
            source_index = int(meta.get("source_index", -1))
            group_index = int(meta.get("group_index", meta.get("stroke_index", 0)))
            if source_index < 0:
                raise RuntimeError("The selected handle has no source vertex index.")

            # This is the only coordinate conversion used for the dragged point.
            # It maps visible canvas pixels -> rotated page plane -> unrotated PDF.
            target_pdf = canvas._display_to_pdf(page_index, display_page,
                                                QPointF(target_display_point))

            line_type = getattr(fitz, "PDF_ANNOT_LINE", 3)
            polygon_type = getattr(fitz, "PDF_ANNOT_POLYGON", 6)
            polyline_type = getattr(fitz, "PDF_ANNOT_POLY_LINE", 7)
            ink_type = getattr(fitz, "PDF_ANNOT_INK", 15)
            highlight_type = getattr(fitz, "PDF_ANNOT_HIGHLIGHT", 8)
            vertices = list(annot.vertices or [])

            if subtype in (line_type, polygon_type, polyline_type):
                if not 0 <= source_index < len(vertices):
                    raise RuntimeError("The selected vertex is no longer available.")
                points = [fitz.Point(point) for point in vertices]
                points[source_index] = fitz.Point(target_pdf)
                replacement_kind = "line" if subtype == line_type else ("polygon" if subtype == polygon_type else "polyline")
                replacement_data = [(float(point.x), float(point.y)) for point in points]
            elif subtype == ink_type:
                if vertices and isinstance(vertices[0], (tuple, list)) and len(vertices[0]) >= 2 \
                        and isinstance(vertices[0][0], (int, float)):
                    strokes = [list(vertices)]
                else:
                    strokes = [list(stroke) for stroke in vertices]
                if not 0 <= group_index < len(strokes) or not 0 <= source_index < len(strokes[group_index]):
                    raise RuntimeError("The selected pen point is no longer available.")
                strokes[group_index][source_index] = (float(target_pdf.x), float(target_pdf.y))
                replacement_data = [[(float(point[0]), float(point[1])) if isinstance(point, (tuple, list))
                                     else (float(point.x), float(point.y)) for point in stroke]
                                    for stroke in strokes if len(stroke) >= 2]
                replacement_kind = "ink"
            elif subtype == highlight_type:
                flat_index = group_index * 4 + source_index
                if not 0 <= flat_index < len(vertices):
                    raise RuntimeError("The selected highlight corner is no longer available.")
                points = [fitz.Point(point) for point in vertices]
                points[flat_index] = fitz.Point(target_pdf)
                replacement_data = [fitz.Quad(points[n], points[n+1], points[n+2], points[n+3])
                                     for n in range(0, len(points)-3, 4)]
                replacement_kind = "highlight"
            else:
                raise RuntimeError("This annotation does not expose editable point handles.")

            if replacement_kind == "line" and len(replacement_data) != 2:
                raise RuntimeError("A line must have exactly two endpoints.")
            if replacement_kind == "polygon" and len(replacement_data) < 3:
                raise RuntimeError("A polygon must have at least three vertices.")
            if replacement_kind == "polyline" and len(replacement_data) < 2:
                raise RuntimeError("A polyline must have at least two vertices.")

            # Capture undo only after all input and coordinate validation passes.
            snapshot = self.doc.tobytes(deflate=True)
            self._record_undo()
            page = self.doc.load_page(page_index)
            annot = next((item for item in (page.annots() or []) if int(item.xref) == xref), None)
            if annot is None:
                raise RuntimeError("The original annotation changed before the vertex update.")

            if replacement_kind == "line":
                updated = page.add_line_annot(replacement_data[0], replacement_data[1])
            elif replacement_kind == "polygon":
                updated = page.add_polygon_annot(replacement_data)
            elif replacement_kind == "polyline":
                updated = page.add_polyline_annot(replacement_data)
            elif replacement_kind == "ink":
                updated = page.add_ink_annot(replacement_data)
            else:
                updated = page.add_highlight_annot(replacement_data)

            if replacement_kind == "line":
                updated.set_line_ends(int(original_line_ends[0]), int(original_line_ends[1]))
            if colors.get("stroke") or colors.get("fill"):
                updated.set_colors(stroke=colors.get("stroke"), fill=colors.get("fill"))
            if border.get("width") is not None and replacement_kind != "highlight":
                updated.set_border(width=float(border.get("width", 1.0)))
            if opacity is not None and opacity >= 0:
                updated.set_opacity(opacity)
            if info.get("title") or info.get("content"):
                updated.set_info(title=str(info.get("title") or ""), content=str(info.get("content") or ""))
            updated.update()
            new_xref = int(updated.xref)

            # Delete the old object only after the replacement has been created
            # and updated successfully; this avoids duplicate/lost marks.
            page.delete_annot(annot)
            remaining = {int(item.xref) for item in (page.annots() or [])}
            if xref in remaining or new_xref not in remaining:
                raise RuntimeError("MuPDF could not complete the single-vertex replacement.")

            new_item = (page_index, new_xref)
            old_item = (page_index, xref)
            selected = list(self.selected_annotations or [old_item])
            self.selected_annotations = [new_item if item == old_item else item for item in selected]
            self.selected_annotation = new_item
            self.annotationSelectionChanged.emit(True)
            self._changed(page_index)
            canvas.update()
            self._update_linked_display(page_index)
            return True
        except Exception as exc:
            # If a native PDF operation fails after creating the replacement,
            # remove that new object and restore the pre-operation document bytes.
            try:
                if snapshot is not None:
                    self._replace_document_state(snapshot)
                elif new_xref is not None:
                    page = self.doc.load_page(page_index)
                    created = next((item for item in (page.annots() or []) if int(item.xref) == int(new_xref)), None)
                    if created is not None:
                        page.delete_annot(created)
            except Exception:
                pass
            QMessageBox.warning(self, APP_NAME, f"Could not move the selected point:\n{exc}")
            canvas.update()
            self._update_linked_display(page_index)
            return False

    def transform_annotation(self, page_index: int, xref: int, old_display: QRectF,
                             new_display: QRectF, canvas=None, record_undo=True):
        """Move/resize a native annotation using the geometry of the canvas that received the drag.

        Highlight and Ink annotations do not expose a mutable PDF /Rect entry in
        MuPDF. They must be rebuilt from their quads/strokes; calling set_rect()
        on them prints native MuPDF errors and leaves the original geometry intact.
        """
        canvas = canvas or self.canvas
        original_xref = int(xref)
        try:
            page = self.doc.load_page(int(page_index))
            annot = next((a for a in (page.annots() or []) if int(a.xref) == int(xref)), None)
            if annot is None:
                self.clear_annotation_selection()
                return False
            if old_display == new_display or new_display.width() < 2 or new_display.height() < 2:
                return False
            page_rect = canvas.page_rects.get(int(page_index), QRectF())
            if page_rect.isEmpty():
                raise RuntimeError("The page is not currently laid out in the active PDF pane.")

            annot_type = annot.type or (0, "")
            subtype_code = int(annot_type[0])
            info = dict(annot.info or {})
            colors = dict(annot.colors or {})
            opacity = annot.opacity
            border = dict(annot.border or {})
            original_line_ends = tuple(getattr(annot, "line_ends", (0, 0)) or (0, 0))

            def remap_pdf_point(point):
                display_point = canvas._pdf_to_display(page_index, page_rect, fitz.Point(point))
                fx = (display_point.x() - old_display.left()) / max(old_display.width(), 1.0)
                fy = (display_point.y() - old_display.top()) / max(old_display.height(), 1.0)
                target = QPointF(new_display.left() + fx * new_display.width(),
                                 new_display.top() + fy * new_display.height())
                return canvas._display_to_pdf(page_index, page_rect, target)

            # Validate and build replacement geometry before touching the document.
            replacement_kind = "rect"
            replacement_data = None
            if subtype_code == getattr(fitz, "PDF_ANNOT_HIGHLIGHT", 8):
                vertices = list(annot.vertices or [])
                if len(vertices) < 4:
                    raise RuntimeError("This highlight has no editable quadrilateral geometry.")
                quads = []
                for n in range(0, len(vertices) - 3, 4):
                    mapped = [remap_pdf_point(vertices[n + k]) for k in range(4)]
                    quads.append(fitz.Quad(mapped[0], mapped[1], mapped[2], mapped[3]))
                replacement_kind, replacement_data = "highlight", quads
            elif subtype_code == getattr(fitz, "PDF_ANNOT_INK", 15):
                vertices = list(annot.vertices or [])
                if not vertices:
                    raise RuntimeError("This pen stroke has no editable path data.")
                # PyMuPDF returns Ink vertices as a list of strokes, each a list
                # of (x, y) pairs. Accept a flat stroke too for older PDF writers.
                if vertices and isinstance(vertices[0], (tuple, list)) and len(vertices[0]) >= 2 \
                        and isinstance(vertices[0][0], (int, float)):
                    vertices = [vertices]
                mapped_strokes = []
                for stroke in vertices:
                    mapped = [remap_pdf_point(point) for point in stroke]
                    if len(mapped) >= 2:
                        mapped_strokes.append([(float(point.x), float(point.y)) for point in mapped])
                if not mapped_strokes:
                    raise RuntimeError("This pen stroke could not be mapped to the page.")
                replacement_kind, replacement_data = "ink", mapped_strokes
            elif subtype_code in (getattr(fitz, "PDF_ANNOT_LINE", 3),
                                   getattr(fitz, "PDF_ANNOT_POLYGON", 6),
                                   getattr(fitz, "PDF_ANNOT_POLY_LINE", 7)):
                vertices = list(annot.vertices or [])
                if len(vertices) < 2:
                    raise RuntimeError("This shape has no editable point geometry.")
                mapped = [remap_pdf_point(point) for point in vertices]
                mapped_points = [(float(point.x), float(point.y)) for point in mapped]
                if subtype_code == getattr(fitz, "PDF_ANNOT_LINE", 3):
                    replacement_kind, replacement_data = "line", mapped_points[:2]
                elif subtype_code == getattr(fitz, "PDF_ANNOT_POLYGON", 6):
                    replacement_kind, replacement_data = "polygon", mapped_points
                else:
                    replacement_kind, replacement_data = "polyline", mapped_points
            else:
                # These are the rectangular annotation types created by Engo's
                # Note/Text tools and scanned-page highlight fallback.
                supported_rect_types = {
                    getattr(fitz, "PDF_ANNOT_SQUARE", 4),
                    getattr(fitz, "PDF_ANNOT_CIRCLE", 5),
                    getattr(fitz, "PDF_ANNOT_TEXT", 0),
                    getattr(fitz, "PDF_ANNOT_FREE_TEXT", 2),
                }
                if subtype_code not in supported_rect_types:
                    raise RuntimeError(
                        f"Moving this PDF annotation type ({annot_type[1] or 'unknown'}) is not supported."
                    )
                replacement_data = canvas._rect_to_pdf(page_index, page_rect, new_display)
                if replacement_data.is_empty:
                    raise RuntimeError("The new annotation bounds are empty.")

            if record_undo:
                self._record_undo()
            # Coordinate conversion above loads the page repeatedly. PyMuPDF can
            # invalidate older Page / Annot wrappers when load_page() is called
            # again, so reacquire both immediately before mutating the document.
            page = self.doc.load_page(int(page_index))
            annot = next((a for a in (page.annots() or []) if int(a.xref) == int(xref)), None)
            if annot is None:
                raise RuntimeError("The original annotation was no longer available for editing.")
            if replacement_kind in ("highlight", "ink", "line", "polygon", "polyline"):
                # Rebuild geometries whose PDF /Rect entry is not mutable.
                if replacement_kind == "highlight":
                    updated = page.add_highlight_annot(replacement_data)
                elif replacement_kind == "ink":
                    updated = page.add_ink_annot(replacement_data)
                elif replacement_kind == "line":
                    updated = page.add_line_annot(replacement_data[0], replacement_data[1])
                elif replacement_kind == "polygon":
                    updated = page.add_polygon_annot(replacement_data)
                else:
                    updated = page.add_polyline_annot(replacement_data)
                if replacement_kind == "line":
                    updated.set_line_ends(int(original_line_ends[0]), int(original_line_ends[1]))
                if colors.get("stroke") or colors.get("fill"):
                    updated.set_colors(stroke=colors.get("stroke"), fill=colors.get("fill"))
                if border.get("width") is not None and replacement_kind != "highlight":
                    updated.set_border(width=float(border.get("width", 2.0)))
                if opacity is not None and opacity >= 0:
                    updated.set_opacity(opacity)
                if info.get("content") or info.get("title"):
                    updated.set_info(title=info.get("title", ""), content=info.get("content", ""))
                updated.update()
                new_xref = int(updated.xref)
                old_xref = int(xref)
                page.delete_annot(annot)
                remaining_xrefs = [int(a.xref) for a in (page.annots() or [])]
                if old_xref in remaining_xrefs:
                    stale = next((a for a in (page.annots() or []) if int(a.xref) == old_xref), None)
                    if stale is not None:
                        page.delete_annot(stale)
                    remaining_xrefs = [int(a.xref) for a in (page.annots() or [])]
                if old_xref in remaining_xrefs or new_xref not in remaining_xrefs:
                    # Do not leave two visible marks behind if MuPDF rejected the
                    # replacement/deletion sequence.
                    current_new = next((a for a in (page.annots() or []) if int(a.xref) == new_xref), None)
                    if current_new is not None:
                        page.delete_annot(current_new)
                    raise RuntimeError("MuPDF could not replace the original drawing cleanly; no duplicate was kept.")
                xref = new_xref
            else:
                annot.set_rect(replacement_data)
                annot.update()
                refreshed = next((a for a in (page.annots() or []) if int(a.xref) == int(xref)), None)
                if refreshed is None:
                    raise RuntimeError("The PDF no longer exposes this annotation after resizing.")
                verified = canvas._annotation_rect_display(page_index, refreshed, page=page)
                if verified.isEmpty():
                    raise RuntimeError("The PDF viewer could not verify the new annotation bounds.")

            old_item = (int(page_index), original_xref)
            new_item = (int(page_index), int(xref))
            self.selected_annotation = new_item
            selected_items = list(self.selected_annotations or [old_item])
            self.selected_annotations = [new_item if item == old_item else item for item in selected_items]
            if new_item not in self.selected_annotations:
                self.selected_annotations.append(new_item)
            self.annotationSelectionChanged.emit(True)
            self._changed(int(page_index))
            self.canvas.update()
            self._update_linked_display(int(page_index))
            return True
        except Exception as exc:
            QMessageBox.warning(self, APP_NAME, f"Could not move or resize annotation:\n{exc}")
            self.canvas.update()
            self._update_linked_display(int(page_index))
            return False

    def transform_annotations_group(self, items, delta: QPointF, canvas=None) -> bool:
        """Move a multi-selection together with one undo step."""
        canvas = canvas or self.canvas
        items = list(items or [])
        if len(items) < 2 or (abs(delta.x()) + abs(delta.y())) < 1.0:
            return False
        snapshot = self.doc.tobytes(deflate=True)
        original_selection = list(self.selected_annotations or [])
        original_active = self.selected_annotation
        self._record_undo()
        moved_items = []
        try:
            for page_index, xref, original_bounds in items:
                old_rect = QRectF(original_bounds)
                new_rect = old_rect.translated(delta)
                if not self.transform_annotation(int(page_index), int(xref), old_rect,
                                                  new_rect, canvas=canvas, record_undo=False):
                    raise RuntimeError("One of the selected objects could not be moved.")
                moved_items.append(self.selected_annotation)
            self.selected_annotations = [item for item in moved_items if item]
            self.selected_annotation = self.selected_annotations[-1] if self.selected_annotations else None
            self.annotationSelectionChanged.emit(bool(self.selected_annotations))
            canvas.update()
            self._update_linked_display()
            return True
        except Exception as exc:
            # A group move is atomic: roll back every member and restore the
            # original selection references if any member fails.
            try:
                self._replace_document_state(snapshot)
            except Exception:
                pass
            self.selected_annotations = original_selection
            self.selected_annotation = original_active
            self.annotationSelectionChanged.emit(bool(original_selection))
            canvas.update()
            self._update_linked_display()
            QMessageBox.warning(self, APP_NAME, f"Could not move the selected group:\n{exc}")
            return False

    def move_annotation_to_page(self, source_page_index: int, xref: int, target_page_index: int,
                                new_display_rect: QRectF, canvas=None, target_display_rect=None) -> bool:
        """Drag one annotation to another page in the same PDF without rasterizing it."""
        canvas = canvas or self.canvas
        source_page_index, target_page_index, xref = int(source_page_index), int(target_page_index), int(xref)
        snapshot = None
        created_target = False
        try:
            snapshot = self.doc.tobytes(deflate=True)
            if source_page_index == target_page_index:
                return False
            source_display = canvas.page_rects.get(source_page_index, QRectF())
            target_display = (QRectF(target_display_rect) if target_display_rect is not None
                              else canvas.page_rects.get(target_page_index, QRectF()))
            if source_display.isEmpty() or target_display.isEmpty():
                raise RuntimeError("The source or destination page geometry is unavailable.")
            source_page = self.doc.load_page(source_page_index)
            annot = next((a for a in (source_page.annots() or []) if int(a.xref) == xref), None)
            if annot is None:
                raise RuntimeError("The selected annotation no longer exists.")
            subtype = int((annot.type or (0, ""))[0])
            info = dict(annot.info or {})
            colors = dict(annot.colors or {})
            opacity = annot.opacity
            border = dict(annot.border or {})
            source_line_ends = tuple(getattr(annot, "line_ends", (0, 0)) or (0, 0))
            source_rect = fitz.Rect(annot.rect)
            vertices = list(annot.vertices or [])
            default_appearance = self.doc.xref_get_key(int(annot.xref), "DA")
            default_appearance_text = str(default_appearance[1] if default_appearance and default_appearance[0] == "string" else "")
            original_bounds = canvas._annotation_selection_geometry(source_page_index, annot, page=source_page)["bounds"]
            if original_bounds.isEmpty() or new_display_rect.isEmpty():
                raise RuntimeError("The object position could not be calculated.")
            dx = float(new_display_rect.left() - original_bounds.left())
            dy = float(new_display_rect.top() - original_bounds.top())
            # Cache every source-page transform while its Page wrapper is still
            # alive. Loading the destination page can orphan the source wrapper in
            # PyMuPDF, so never read source_page after this point.
            source_page_rect = fitz.Rect(source_page.rect)
            source_rotation = source_page.rotation_matrix
            target_page = self.doc.load_page(target_page_index)
            target_page_rect = fitz.Rect(target_page.rect)
            target_derotation = target_page.derotation_matrix

            def map_point(point):
                # Use the already-held Page transforms directly. Calling load_page
                # for every vertex can invalidate Annot wrappers during a move.
                source_rotated = fitz.Point(point) * source_rotation
                display_x = source_display.left() + source_rotated.x / max(source_page_rect.width, 1) * source_display.width()
                display_y = source_display.top() + source_rotated.y / max(source_page_rect.height, 1) * source_display.height()
                destination_x = display_x + dx
                destination_y = display_y + dy
                target_rotated = fitz.Point(
                    (destination_x-target_display.left()) * target_page_rect.width / max(target_display.width(), 1),
                    (destination_y-target_display.top()) * target_page_rect.height / max(target_display.height(), 1),
                )
                return target_rotated * target_derotation

            def mapped_rect(rect):
                r = fitz.Rect(rect)
                corners = [fitz.Point(r.x0, r.y0), fitz.Point(r.x1, r.y0),
                           fitz.Point(r.x1, r.y1), fitz.Point(r.x0, r.y1)]
                mapped = [map_point(point) for point in corners]
                result = fitz.Rect(min(point.x for point in mapped), min(point.y for point in mapped),
                                   max(point.x for point in mapped), max(point.y for point in mapped))
                # mapped points are back in the target page's unrotated PDF
                # coordinates; intersecting them with target_page.rect (the
                # rotated display rectangle) corrupts/empties drops on 90° pages.
                return result

            self._record_undo()
            # Coordinate mapping above may load other pages; reacquire the target
            # page immediately before creating the replacement annotation.
            target_page = self.doc.load_page(target_page_index)
            new_annot = None
            if subtype == getattr(fitz, "PDF_ANNOT_HIGHLIGHT", 8):
                quads = []
                for n in range(0, len(vertices)-3, 4):
                    pts = [map_point(vertices[n+k]) for k in range(4)]
                    quads.append(fitz.Quad(pts[0], pts[1], pts[2], pts[3]))
                if not quads:
                    raise RuntimeError("The highlight has no editable geometry.")
                new_annot = target_page.add_highlight_annot(quads)
            elif subtype == getattr(fitz, "PDF_ANNOT_INK", 15):
                if vertices and isinstance(vertices[0], (tuple, list)) and len(vertices[0]) >= 2 \
                        and isinstance(vertices[0][0], (int, float)):
                    vertices = [vertices]
                strokes = []
                for stroke in vertices:
                    mapped = [map_point(point) for point in stroke]
                    if len(mapped) >= 2:
                        strokes.append([(float(point.x), float(point.y)) for point in mapped])
                if not strokes:
                    raise RuntimeError("The pen drawing has no stroke geometry.")
                new_annot = target_page.add_ink_annot(strokes)
            elif subtype in (getattr(fitz, "PDF_ANNOT_LINE", 3),
                              getattr(fitz, "PDF_ANNOT_POLYGON", 6),
                              getattr(fitz, "PDF_ANNOT_POLY_LINE", 7)):
                mapped = [map_point(point) for point in vertices]
                points = [(float(point.x), float(point.y)) for point in mapped]
                if subtype == getattr(fitz, "PDF_ANNOT_LINE", 3) and len(points) >= 2:
                    new_annot = target_page.add_line_annot(points[0], points[1])
                elif subtype == getattr(fitz, "PDF_ANNOT_POLYGON", 6) and len(points) >= 3:
                    new_annot = target_page.add_polygon_annot(points)
                elif len(points) >= 2:
                    new_annot = target_page.add_polyline_annot(points)
                else:
                    raise RuntimeError("The shape has no editable point geometry.")
            elif subtype == getattr(fitz, "PDF_ANNOT_SQUARE", 4):
                new_annot = target_page.add_rect_annot(mapped_rect(source_rect))
            elif subtype == getattr(fitz, "PDF_ANNOT_CIRCLE", 5):
                new_annot = target_page.add_circle_annot(mapped_rect(source_rect))
            elif subtype == getattr(fitz, "PDF_ANNOT_TEXT", 0):
                anchor = map_point(fitz.Point(source_rect.x0, source_rect.y0))
                new_annot = target_page.add_text_annot(anchor, str(info.get("content") or "Note"), icon="Note")
            elif subtype == getattr(fitz, "PDF_ANNOT_FREE_TEXT", 2):
                da_match = re.search(r"([0-9.]+)\s+([0-9.]+)\s+([0-9.]+)\s+rg\s+/([A-Za-z0-9]+)\s+([0-9.]+)\s+Tf", default_appearance_text)
                text_color = tuple(float(da_match.group(i)) for i in (1,2,3)) if da_match else (0.15,0.2,0.3)
                font_name = da_match.group(4) if da_match else "Helv"
                font_size = float(da_match.group(5)) if da_match else 11.0
                new_annot = target_page.add_freetext_annot(mapped_rect(source_rect),
                    str(info.get("content") or "Text"), fontsize=font_size,
                    fontname=font_name, text_color=text_color, fill_color=colors.get("stroke") or None, align=0)
            else:
                raise RuntimeError(f"Moving {annot.type[1] if annot.type else 'this annotation'} between pages is not supported yet.")

            if new_annot is None:
                raise RuntimeError("The destination annotation could not be created.")
            if subtype == getattr(fitz, "PDF_ANNOT_LINE", 3):
                new_annot.set_line_ends(int(source_line_ends[0]), int(source_line_ends[1]))
            created_target = True
            if subtype != getattr(fitz, "PDF_ANNOT_FREE_TEXT", 2) and (colors.get("stroke") or colors.get("fill")):
                try:
                    new_annot.set_colors(stroke=colors.get("stroke"), fill=colors.get("fill"))
                except Exception:
                    pass
            if border.get("width") is not None and subtype not in (
                    getattr(fitz, "PDF_ANNOT_TEXT", 0), getattr(fitz, "PDF_ANNOT_HIGHLIGHT", 8)):
                new_annot.set_border(width=float(border.get("width", 1.0)))
            if opacity is not None and opacity >= 0:
                new_annot.set_opacity(opacity)
            if info.get("title") or info.get("content"):
                new_annot.set_info(title=str(info.get("title") or ""), content=str(info.get("content") or ""))
            new_annot.update()
            new_xref = int(new_annot.xref)

            # Verify the destination first; only then remove the source.
            target_page = self.doc.load_page(target_page_index)
            if not any(int(a.xref) == new_xref for a in (target_page.annots() or [])):
                raise RuntimeError("The moved object could not be verified on the destination page.")
            source_page = self.doc.load_page(source_page_index)
            old = next((a for a in (source_page.annots() or []) if int(a.xref) == xref), None)
            if old is None:
                raise RuntimeError("The original object disappeared before the move completed.")
            source_page.delete_annot(old)
            if any(int(a.xref) == xref for a in (source_page.annots() or [])):
                raise RuntimeError("The original object could not be removed after the move.")

            self.selected_annotation = (target_page_index, new_xref)
            self.selected_annotations = [(target_page_index, new_xref)]
            self.annotationSelectionChanged.emit(True)
            self._changed(source_page_index)
            self._changed(target_page_index)
            self._update_linked_display(source_page_index)
            self._update_linked_display(target_page_index)
            if not self.scroll_mode and target_page_index != self.current_page:
                self.go_to_page(target_page_index)
            return True
        except Exception as exc:
            # If the destination object was partially created, restore the
            # pre-drop document snapshot so no duplicate or half-move remains.
            if snapshot is not None and created_target:
                try:
                    self._replace_document_state(snapshot)
                except Exception:
                    pass
            QMessageBox.warning(self, APP_NAME, f"Could not move annotation to another page:\n{exc}")
            canvas.update()
            self._update_linked_display(source_page_index)
            return False

    def _record_undo(self):
        """Capture the current PDF state before a persistent edit, for document-scoped undo."""
        if self._restoring_history:
            return
        try:
            self.undo_stack.append(self.doc.tobytes(deflate=True))
            self.redo_stack.clear()
            while len(self.undo_stack) > self._history_limit or (len(self.undo_stack) > 1 and sum(len(x) for x in self.undo_stack) > self._history_bytes_limit):
                self.undo_stack.pop(0)
            self.historyChanged.emit(bool(self.undo_stack), bool(self.redo_stack))
        except Exception as exc:
            QMessageBox.warning(self, APP_NAME, f"Undo snapshot could not be created:\n{exc}")

    def _replace_document_state(self, data: bytes):
        """Restore an in-memory PDF snapshot without changing the file on disk."""
        self._restoring_history = True
        try:
            old_doc = self.doc
            new_doc = fitz.open(stream=data, filetype="pdf")
            self.doc = new_doc
            self._link_overlay_rects.clear()
            try:
                old_doc.close()
            except Exception:
                pass
            self.page_count = self.doc.page_count
            self.page_sizes = [
                (float(self.doc.load_page(i).rect.width), float(self.doc.load_page(i).rect.height))
                for i in range(self.page_count)
            ]
            self.render_version += 1
            self.page_render_versions = [self.render_version] * self.page_count
            self._thumbnail_cache.clear()
            self._build_thumbnails()
            # Keep the current page valid after undoing/redoing page rotations.
            self.current_page = max(0, min(self.current_page, self.page_count - 1))
            if self.thumbnails.count():
                self._sync_sidebar_selection()
            self.selected_annotation = None
            self.selected_annotations = []
            self.selected_page_link = None
            self.annotationSelectionChanged.emit(False)
            self.canvas.clear_cache(clear_smart=True)
            self._relayout()
            self.go_to_page(self.current_page)
            self.dirty = True
            self.titleChanged.emit(self.tab_title())
            self.documentChanged.emit()
        finally:
            self._restoring_history = False
        self.historyChanged.emit(bool(self.undo_stack), bool(self.redo_stack))

    def undo(self):
        if not self.undo_stack:
            return
        try:
            current = self.doc.tobytes(deflate=True)
            snapshot = self.undo_stack.pop()
            self.redo_stack.append(current)
            if len(self.redo_stack) > self._history_limit:
                self.redo_stack.pop(0)
            self._replace_document_state(snapshot)
        except Exception as exc:
            QMessageBox.warning(self, APP_NAME, f"Undo failed:\n{exc}")

    def redo(self):
        if not self.redo_stack:
            return
        try:
            current = self.doc.tobytes(deflate=True)
            snapshot = self.redo_stack.pop()
            self.undo_stack.append(current)
            if len(self.undo_stack) > self._history_limit:
                self.undo_stack.pop(0)
            self._replace_document_state(snapshot)
        except Exception as exc:
            QMessageBox.warning(self, APP_NAME, f"Redo failed:\n{exc}")

    def _changed(self, page_index):
        self.dirty = True
        self.render_version += 1
        try:
            page_index = int(page_index)
            if 0 <= page_index < self.page_count:
                if len(self.page_render_versions) != self.page_count:
                    self.page_render_versions = [self.render_version] * self.page_count
                self.page_render_versions[page_index] += 1
                for key in list(self._thumbnail_cache.keys()):
                    if key and int(key[0]) == page_index:
                        self._thumbnail_cache.pop(key, None)
        except (AttributeError, IndexError, TypeError, ValueError):
            pass
        self.canvas.invalidate_page(page_index)
        self._update_linked_display(page_index)
        self.titleChanged.emit(self.tab_title())
        self.documentChanged.emit()
        self.historyChanged.emit(bool(self.undo_stack), bool(self.redo_stack))

    def _rotation_anchor_layout_rect(self, page_index: int) -> QRectF:
        """Return the displayed page rectangle, or its complete Book spread."""
        page_index = max(0, min(int(page_index), max(0, self.page_count - 1)))
        if self.book_mode:
            first = (page_index // 2) * 2
            rects = [QRectF(self.canvas.page_rects[index])
                     for index in (first, first + 1)
                     if index in self.canvas.page_rects]
            if rects:
                combined = QRectF(rects[0])
                for rect in rects[1:]:
                    combined = combined.united(rect)
                return combined
        rect = self.canvas.page_rects.get(page_index)
        return QRectF(rect) if rect is not None else QRectF()

    def rotate_pages_clockwise(self, page_indices=None) -> bool:
        """Rotate pages clockwise while keeping the originally targeted page active.

        A 90-degree rotation can change a page's displayed height/width dramatically.
        In Scroll mode that changes the page beneath the viewport center. The
        selection lock prevents those programmatic geometry updates from being
        mistaken for user navigation, and the same page-local reading point is
        restored before normal scroll-based page tracking resumes.
        """
        if page_indices is None:
            indices = list(range(self.page_count))
        else:
            indices = sorted({int(i) for i in page_indices if 0 <= int(i) < self.page_count})
        if not indices:
            return False

        # For a single-page operation, the requested page is authoritative. For
        # Rotate All, keep the page that was active when the action began.
        anchor_page = (indices[0] if len(indices) == 1 else
                       max(0, min(int(self.current_page), self.page_count - 1)))
        if self.book_mode:
            anchor_page = (anchor_page // 2) * 2
        old_rect = self._rotation_anchor_layout_rect(anchor_page)
        old_v = self.scroll.verticalScrollBar().value()
        old_h = self.scroll.horizontalScrollBar().value()
        viewport = self.scroll.viewport()
        viewport_width = max(1, int(viewport.width()))
        viewport_height = max(1, int(viewport.height()))

        # Preserve the point that was at the viewport center, expressed as a
        # normalized position inside the page/spread. Clamp it because a short
        # page may not fill the viewport in one or both dimensions.
        if not old_rect.isEmpty():
            center_x = old_h + viewport_width * 0.5
            center_y = old_v + viewport_height * 0.5
            x_fraction = max(0.0, min(1.0, (center_x - old_rect.left()) / max(old_rect.width(), 1.0)))
            y_fraction = max(0.0, min(1.0, (center_y - old_rect.top()) / max(old_rect.height(), 1.0)))
        else:
            x_fraction = y_fraction = 0.5

        snapshot = self.doc.tobytes(deflate=True)
        self._record_undo()
        rotation_serial = int(getattr(self, "_page_rotation_serial", 0)) + 1
        self._page_rotation_serial = rotation_serial
        self._rotation_selection_lock = True
        self.current_page = anchor_page
        try:
            for index in indices:
                page = self.doc.load_page(index)
                page.set_rotation((int(page.rotation) + 90) % 360)

            self.page_sizes = [
                (float(self.doc.load_page(i).rect.width), float(self.doc.load_page(i).rect.height))
                for i in range(self.page_count)
            ]
            self.dirty = True
            self.render_version += 1
            if len(self.page_render_versions) != self.page_count:
                self.page_render_versions = [self.render_version] * self.page_count
            for changed_index in indices:
                self.page_render_versions[changed_index] += 1
                self.canvas.invalidate_page(changed_index)
                for key in list(self._thumbnail_cache.keys()):
                    if key and int(key[0]) == changed_index:
                        self._thumbnail_cache.pop(key, None)
            self.selected_annotation = None
            self.selected_annotations = []
            self.selected_page_link = None
            self.annotationSelectionChanged.emit(False)
            self._build_thumbnails()
            if self.thumbnails.count():
                self._sync_sidebar_selection()
            self._relayout()
            self._update_linked_display(clear_cache=True)
            self.titleChanged.emit(self.tab_title())
            self.documentChanged.emit()
            self.historyChanged.emit(bool(self.undo_stack), bool(self.redo_stack))

            def restore_reading_position(serial=rotation_serial, page_index=anchor_page,
                                         xf=x_fraction, yf=y_fraction,
                                         vw=viewport_width, vh=viewport_height):
                # A rapid second click supersedes the previous restore callback.
                if serial != getattr(self, "_page_rotation_serial", -1):
                    return
                try:
                    if getattr(self, "_document_closing", False):
                        return
                    rect = self._rotation_anchor_layout_rect(page_index)
                    if not rect.isEmpty():
                        target_x = rect.left() + xf * rect.width() - vw * 0.5
                        target_y = rect.top() + yf * rect.height() - vh * 0.5
                        hbar = self.scroll.horizontalScrollBar()
                        vbar = self.scroll.verticalScrollBar()
                        hbar.setValue(max(hbar.minimum(), min(hbar.maximum(), round(target_x))))
                        vbar.setValue(max(vbar.minimum(), min(vbar.maximum(), round(target_y))))
                    # Keep the exact requested page/spread active after all
                    # programmatic scroll changes have completed.
                    self.current_page = page_index
                    self._sync_sidebar_selection()
                    self.currentPageChanged.emit(self.current_page, self.page_count)
                finally:
                    if serial == getattr(self, "_page_rotation_serial", -1):
                        self._rotation_selection_lock = False

            QTimer.singleShot(0, restore_reading_position)
            return True
        except Exception as exc:
            try:
                self._replace_document_state(snapshot)
            except Exception:
                pass
            finally:
                if rotation_serial == getattr(self, "_page_rotation_serial", -1):
                    self._rotation_selection_lock = False
            QMessageBox.warning(self, APP_NAME, f"Could not rotate PDF page(s):\n{exc}")
            return False

    def add_highlight_words(self, index: int, word_records):
        """Create a native PDF highlight from the exact words selected by the text tool."""
        page = self.doc.load_page(int(index))
        line_words = {}
        for word in list(word_records or []):
            if len(word) < 8 or not str(word[4] or "").strip():
                continue
            word_rect = fitz.Rect(word[:4]) & page.cropbox
            if word_rect.is_empty or word_rect.width <= 0 or word_rect.height <= 0:
                continue
            line_key = (int(word[5]), int(word[6]))
            line_words.setdefault(line_key, []).append(word_rect)
        merged_runs = []
        for _line_key, selected_words in line_words.items():
            selected_words.sort(key=lambda r: (r.x0, r.x1))
            run = fitz.Rect(selected_words[0])
            for word_rect in selected_words[1:]:
                gap_limit = max(2.0, min(run.height, word_rect.height) * 0.65)
                if word_rect.x0 <= run.x1 + gap_limit:
                    run |= word_rect
                else:
                    merged_runs.append(fitz.Rect(run))
                    run = fitz.Rect(word_rect)
            merged_runs.append(fitz.Rect(run))
        if not merged_runs:
            return False
        self._record_undo()
        annot = page.add_highlight_annot([rect.quad for rect in merged_runs])
        annot.set_colors(stroke=color_tuple(self.annotation_colors.get("highlight", DEFAULT_ANNOTATION_COLORS["highlight"])))
        annot.set_opacity(0.38)
        annot.update()
        self._changed(int(index))
        return True

    def add_area_highlight(self, index: int, rect: fitz.Rect):
        """Create an area/image highlight without converting crossed text into text markup."""
        page = self.doc.load_page(int(index))
        rect = fitz.Rect(rect) & page.rect
        if rect.is_empty or rect.width < 1 or rect.height < 1:
            return False
        self._record_undo()
        annot = page.add_rect_annot(rect)
        hi_color = color_tuple(self.annotation_colors.get("highlight", DEFAULT_ANNOTATION_COLORS["highlight"]))
        annot.set_colors(stroke=hi_color, fill=hi_color)
        annot.set_border(width=0)
        annot.set_opacity(0.28)
        annot.update()
        self._changed(int(index))
        return True

    def add_highlight(self, index: int, rect: fitz.Rect):
        page = self.doc.load_page(index)
        rect = fitz.Rect(rect) & page.rect
        if rect.is_empty or rect.width < 1 or rect.height < 1:
            return
        # Prefer genuine text highlights. Merge adjacent selected words on each
        # line into a continuous quad so a sentence/phrase looks like one stroke,
        # not a row of separately highlighted word boxes. All quads are stored in
        # one PDF Highlight annotation, including multi-line selections.
        words = page.get_text("words", sort=True)
        line_words = {}
        for word in words:
            if len(word) < 8:
                continue
            word_rect = fitz.Rect(word[:4])
            if word_rect.intersects(rect) and word_rect.width > 0 and word_rect.height > 0:
                line_key = (int(word[5]), int(word[6]))
                line_words.setdefault(line_key, []).append(word_rect)
        merged_runs = []
        for _line_key, selected_words in line_words.items():
            selected_words.sort(key=lambda r: (r.x0, r.x1))
            run = fitz.Rect(selected_words[0])
            for word_rect in selected_words[1:]:
                # Normal inter-word spaces should remain inside the same strip;
                # a larger gap starts a separate visual run on that line.
                gap_limit = max(2.0, min(run.height, word_rect.height) * 0.65)
                if word_rect.x0 <= run.x1 + gap_limit:
                    run |= word_rect
                else:
                    merged_runs.append(fitz.Rect(run))
                    run = fitz.Rect(word_rect)
            merged_runs.append(fitz.Rect(run))
        self._record_undo()
        if merged_runs:
            quads = [r.quad for r in merged_runs]
            annot = page.add_highlight_annot(quads)
            annot.set_colors(stroke=color_tuple(self.annotation_colors.get("highlight", DEFAULT_ANNOTATION_COLORS["highlight"])))
            annot.set_opacity(0.38)
            annot.update()
        else:
            # Scanned pages may have no text layer; use a translucent area mark as a fallback.
            annot = page.add_rect_annot(rect)
            hi_color = color_tuple(self.annotation_colors.get("highlight", DEFAULT_ANNOTATION_COLORS["highlight"]))
            annot.set_colors(stroke=hi_color, fill=hi_color)
            annot.set_border(width=0)
            annot.set_opacity(0.28)
            annot.update()
        self._changed(index)

    def add_recognized_shape(self, index: int, shape: dict):
        """Create a native PDF shape annotation recognized from the pen stroke."""
        try:
            page = self.doc.load_page(int(index))
            kind = str(shape.get("kind") or "")
            self._record_undo()
            if kind == "line":
                points = shape.get("points") or []
                if len(points) < 2:
                    return self.add_ink(index, points)
                annot = page.add_line_annot(points[0], points[-1])
            elif kind in ("square", "rectangle"):
                rect = fitz.Rect(shape.get("rect")) & page.rect
                annot = page.add_rect_annot(rect)
            elif kind == "circle":
                rect = fitz.Rect(shape.get("rect")) & page.rect
                annot = page.add_circle_annot(rect)
            elif kind in ("triangle", "quadrilateral"):
                points = shape.get("points") or []
                minimum = 3 if kind == "triangle" else 4
                if len(points) < minimum:
                    raise RuntimeError("The recognized polygon does not have enough corners.")
                annot = page.add_polygon_annot(points)
            else:
                return False
            pen_color = color_tuple(self.annotation_colors.get("pen", DEFAULT_ANNOTATION_COLORS["pen"]))
            annot.set_colors(stroke=pen_color)
            annot.set_border(width=2.2)
            annot.set_opacity(0.95)
            annot.set_info(title="Engo Pen Shape", content=f"Pen shape · {kind.title()}")
            annot.update()
            self.selected_annotation = (int(index), int(annot.xref))
            self.selected_annotations = [(int(index), int(annot.xref))]
            self.annotationSelectionChanged.emit(True)
            self._changed(index)
            return True
        except Exception as exc:
            QMessageBox.warning(self, APP_NAME, f"Could not create recognized shape:\n{exc}")
            return False

    def add_point(self, index: int, point: fitz.Point):
        """Place a compact filled point using the active Pen color."""
        try:
            page = self.doc.load_page(int(index))
            color = color_tuple(self.annotation_colors.get("pen", DEFAULT_ANNOTATION_COLORS["pen"]))
            # A small, screen-independent PDF-space dot; it remains a move-only object.
            radius = 2.1
            rect = fitz.Rect(float(point.x) - radius, float(point.y) - radius,
                             float(point.x) + radius, float(point.y) + radius) & page.rect
            if rect.is_empty or rect.width < 0.5 or rect.height < 0.5:
                return False
            self._record_undo()
            annot = page.add_circle_annot(rect)
            annot.set_colors(stroke=color, fill=color)
            annot.set_border(width=0.45)
            annot.set_opacity(0.98)
            annot.set_info(title="Engo Pen Shape", content="Pen shape · Point")
            annot.update()
            self.selected_annotation = (int(index), int(annot.xref))
            self.selected_annotations = [(int(index), int(annot.xref))]
            self.annotationSelectionChanged.emit(True)
            self._changed(index)
            return True
        except Exception as exc:
            QMessageBox.warning(self, APP_NAME, f"Could not create point:\n{exc}")
            return False

    def add_ink(self, index: int, points: list[fitz.Point]):
        if len(points) < 2:
            return
        page = self.doc.load_page(index)
        self._record_undo()
        annot = page.add_ink_annot([[(float(point.x), float(point.y)) for point in points]])
        annot.set_colors(stroke=color_tuple(self.annotation_colors.get("pen", DEFAULT_ANNOTATION_COLORS["pen"])))
        annot.set_border(width=2.0)
        annot.set_opacity(0.95)
        annot.update()
        self._changed(index)

    def add_tag_region(self, index: int, rect: fitz.Rect, tag_name: str, color: str):
        """Attach a persistent user-defined tag to a rectangular PDF region."""
        try:
            page = self.doc.load_page(int(index))
            rect = fitz.Rect(rect) & page.rect
            if rect.is_empty or rect.width < 4 or rect.height < 4:
                return False
            tag_name = str(tag_name or "").strip()[:32]
            if not tag_name:
                return False
            rgb = color_tuple(color)
            self._record_undo()
            annot = page.add_rect_annot(rect)
            annot.set_colors(stroke=rgb)
            annot.set_border(width=2.0)
            annot.set_opacity(0.98)
            annot.set_info(title="Engo Region Tag", content=tag_name)
            annot.update()
            self.selected_annotation = (int(index), int(annot.xref))
            self.selected_annotations = [(int(index), int(annot.xref))]
            self.annotationSelectionChanged.emit(True)
            self._changed(index)
            return True
        except Exception as exc:
            QMessageBox.warning(self, APP_NAME, f"Could not tag this region:\n{exc}")
            return False

    def add_note(self, index: int, point: fitz.Point, text: str):
        page = self.doc.load_page(index)
        self._record_undo()
        annot = page.add_text_annot(point, text, icon="Note")
        annot.set_info(title="Engo PDF Note", content=text)
        annot.set_colors(stroke=color_tuple(self.annotation_colors.get("note", DEFAULT_ANNOTATION_COLORS["note"])))
        annot.update()
        self._changed(index)

    def add_text(self, index: int, rect: fitz.Rect, text: str):
        page = self.doc.load_page(index)
        rect = fitz.Rect(rect) & page.rect
        if rect.is_empty:
            return
        self._record_undo()
        annot = page.add_freetext_annot(rect, str(text or ""), fontsize=11, fontname="Helv",
                                        text_color=color_tuple(self.annotation_colors.get("text_ink", DEFAULT_ANNOTATION_COLORS["text_ink"])),
                                        fill_color=color_tuple(self.annotation_colors.get("text_fill", DEFAULT_ANNOTATION_COLORS["text_fill"])), align=0)  # Keep PDF text boxes left-aligned (LTR canvas layout).
        annot.set_info(title="Engo PDF Text", content=str(text or ""))
        annot.set_border(width=0.4)
        annot.update()
        self._changed(index)

    def add_teacher_arrow(self, index: int, start_norm, end_norm, label: str = "Teacher pointer"):
        """Insert a vector arrow annotation using page-normalized coordinates."""
        page = self.doc.load_page(max(0, min(int(index), self.page_count - 1)))
        def _point(values):
            x, y = float(values[0]), float(values[1])
            return fitz.Point(max(0.0, min(1.0, x)) * page.rect.width,
                              max(0.0, min(1.0, y)) * page.rect.height)
        start, end = _point(start_norm), _point(end_norm)
        if math.hypot(end.x-start.x, end.y-start.y) < 8:
            return False
        self._record_undo()
        annot = page.add_line_annot(start, end)
        annot.set_line_ends(0, fitz.PDF_ANNOT_LE_OPEN_ARROW)
        annot.set_colors(stroke=(0.16, 0.55, 0.96))
        annot.set_border(width=2.2)
        annot.set_info(title="Engo Teacher Arrow", content=str(label or "Teacher pointer")[:240])
        annot.update()
        self._changed(index)
        return True

    def update_annotation_color(self, index: int, xref: int, color: str, background_color=None) -> bool:
        """Recolor an existing toolbar-created annotation and retain undo support."""
        page_index = int(index)
        old_xref = int(xref)
        selected_color = QColor(str(color))
        if not selected_color.isValid():
            return False
        rgb = (selected_color.redF(), selected_color.greenF(), selected_color.blueF())
        try:
            page = self.doc.load_page(page_index)
            annot = next((item for item in (page.annots() or []) if int(item.xref) == old_xref), None)
            if annot is None:
                return False
            annot_type = int((annot.type or (0, ""))[0])
            info = dict(annot.info or {})
            colors = dict(annot.colors or {})
            border = dict(annot.border or {})

            self._record_undo()
            if annot_type == getattr(fitz, "PDF_ANNOT_FREE_TEXT", 2):
                # FreeText annotations reject Annot.set_colors(). Their text color
                # lives in /DA, while the optional background is stored in /C.
                da = str(self.doc.xref_get_key(old_xref, "DA")[1] or "")
                size_match = re.search(r"([0-9]+(?:\.[0-9]+)?)\s+Tf", da)
                font_match = re.search(r"/([A-Za-z0-9]+)\s+[0-9.]+\s+Tf", da)
                fontsize = float(size_match.group(1)) if size_match else 11.0
                fontname = font_match.group(1) if font_match else "Helv"
                align_value = self.doc.xref_get_key(old_xref, "Q")
                try:
                    alignment = int(align_value[1]) if align_value and align_value[0] == "int" else 0
                except Exception:
                    alignment = 0
                fill = colors.get("stroke") or None
                if background_color is not None:
                    picked_background = QColor(str(background_color))
                    if not picked_background.isValid():
                        return False
                    fill = (picked_background.redF(), picked_background.greenF(), picked_background.blueF())
                if isinstance(fill, (tuple, list)) and len(fill) not in (1, 3, 4):
                    fill = None
                rect = fitz.Rect(annot.rect)
                content = str(info.get("content") or "")
                title = str(info.get("title") or "Engo PDF Text")
                subject = str(info.get("subject") or "")
                flags = int(getattr(annot, "flags", 4))
                try:
                    opacity = float(getattr(annot, "opacity", -1))
                except Exception:
                    opacity = -1.0
                page.delete_annot(annot)
                updated = page.add_freetext_annot(
                    rect, content, fontsize=max(6.0, min(48.0, fontsize)),
                    fontname=fontname, text_color=rgb, fill_color=fill, align=alignment
                )
                if float(border.get("width", 0.0) or 0.0) > 0:
                    updated.set_border(width=float(border.get("width", 0.4)))
                updated.set_info(title=title, content=content, subject=subject)
                try:
                    updated.flags = flags
                except Exception:
                    pass
                if opacity >= 0:
                    try:
                        updated.set_opacity(opacity)
                    except Exception:
                        pass
                updated.update()
                new_xref = int(updated.xref)
                self.selected_annotation = (page_index, new_xref)
                self.selected_annotations = [(page_index, new_xref)]
                self.annotationSelectionChanged.emit(True)
            else:
                # Highlight and Ink accept a stroke only; filled shapes preserve
                # their fill by recoloring both stroke and fill together.
                fill_values = colors.get("fill")
                if isinstance(fill_values, (tuple, list)) and len(fill_values) > 0:
                    annot.set_colors(stroke=rgb, fill=rgb)
                else:
                    annot.set_colors(stroke=rgb)
                annot.update()
                self.selected_annotation = (page_index, old_xref)
                self.selected_annotations = [(page_index, old_xref)]
                self.annotationSelectionChanged.emit(True)
            self._changed(page_index)
            return True
        except Exception as exc:
            QMessageBox.warning(self, APP_NAME, f"Could not change annotation color:\n{exc}")
            return False

    def update_freetext_annotation(self, index: int, xref: int, text: str, fontsize: int, fontname: str):
        page = self.doc.load_page(int(index))
        old = next((a for a in (page.annots() or []) if int(a.xref) == int(xref)), None)
        if old is None:
            return False
        old_info = dict(old.info or {})
        old_rect = fitz.Rect(old.rect)
        old_colors = dict(old.colors or {})
        old_border = dict(old.border or {})
        stroke = old_colors.get("stroke") or color_tuple(self.annotation_colors.get("text_ink", DEFAULT_ANNOTATION_COLORS["text_ink"]))
        fill = old_colors.get("fill") or color_tuple(self.annotation_colors.get("text_fill", DEFAULT_ANNOTATION_COLORS["text_fill"]))
        self._record_undo()
        page.delete_annot(old)
        new_annot = page.add_freetext_annot(old_rect, str(text or ""), fontsize=max(6, min(48, int(fontsize))),
                                            fontname=str(fontname or "Helv"), text_color=stroke, fill_color=fill, align=0)  # Never inherit the app RTL layout.
        new_annot.set_border(width=float(old_border.get("width", 0.4) or 0.4))
        new_annot.set_info(title=str(old_info.get("title") or "Engo PDF Text"),
                           content=str(text or ""), subject=str(old_info.get("subject") or ""))
        new_annot.update()
        self.selected_annotation = (int(index), int(new_annot.xref))
        self.selected_annotations = [(int(index), int(new_annot.xref))]
        self.annotationSelectionChanged.emit(True)
        self._changed(index)
        return True

    def update_text_note(self, index: int, xref: int, text: str):
        page = self.doc.load_page(int(index))
        annot = next((a for a in (page.annots() or []) if int(a.xref) == int(xref)), None)
        if annot is None:
            return False
        self._record_undo()
        annot.set_info(title=str((annot.info or {}).get("title") or "Engo PDF Note"), content=str(text or ""))
        annot.update()
        self._changed(index)
        return True

    def add_page_link(self, index: int, rect: fitz.Rect, destination: int):
        if destination == index:
            QMessageBox.information(self, APP_NAME, "Choose a different destination page.")
            return
        page = self.doc.load_page(index)
        self._record_undo()
        page.insert_link({"kind": fitz.LINK_GOTO, "from": rect, "page": destination,
                          "to": fitz.Point(0, 0), "zoom": 0})
        self._link_overlay_rects.setdefault(int(index), []).append(
            (float(rect.x0), float(rect.y0), float(rect.x1), float(rect.y1), int(destination) + 1)
        )
        identity = (int(index), tuple(round(float(value), 2) for value in rect),
                    int(destination) + 1, int(fitz.LINK_GOTO), "")
        self.select_page_link(identity)
        self._changed(index)
        if self.parent() and hasattr(self.parent(), "show_status"):
            self.parent().show_status(f"Link created: page {index + 1} → page {destination + 1}")

    def set_theme(self, enabled, bg, ink, smart_page_theme=None):
        self.dark_mode, self.bg_color, self.ink_color = bool(enabled), bg, ink
        if smart_page_theme is not None:
            self.smart_page_theme = bool(smart_page_theme)
        self.canvas.clear_cache(clear_smart=False)
        self._build_thumbnails()
        self._relayout()
        self._update_linked_display(clear_cache=True)

    def has_unsaved_changes(self) -> bool:
        """Return true only for explicit edits or persisted PDF-content differences.

        MuPDF's is_dirty flag is not sufficient on its own: reading/selection paths
        can materialize native annotation state without changing the PDF. Compare
        the actual persisted structure against the last-opened/last-saved baseline
        before treating a native dirty flag as a real edit.
        """
        if bool(getattr(self, "dirty", False)):
            return True
        try:
            native_dirty = bool(getattr(self.doc, "is_dirty", False))
        except Exception:
            native_dirty = False
        if not native_dirty:
            return False
        baseline = getattr(self, "_saved_pdf_signature", None)
        if baseline is None:
            # Fail safe only when a baseline could not be established.
            return True
        try:
            current = self._pdf_persistence_signature(self.doc)
            return current != baseline
        except Exception:
            return True

    def tab_title(self):
        base = Path(getattr(self, "display_path", self.path)).name
        return f"● {base}" if self.has_unsaved_changes() else base

    @staticmethod
    def _pdf_persistence_signature(document):
        """Detailed PDF signature used to verify annotations survived serialization."""
        page_data = []
        for page_number in range(document.page_count):
            page = document.load_page(page_number)
            annotations = []
            for annot in list(page.annots() or []):
                info = dict(annot.info or {})
                rect = tuple(round(float(value), 3) for value in annot.rect)
                annot_type = tuple(annot.type or (-1, ""))
                annotations.append((
                    int(annot_type[0]), str(annot_type[1]), rect,
                    str(info.get("title") or ""), str(info.get("content") or ""),
                    str(info.get("subject") or ""), str(info.get("name") or ""),
                ))
            links = []
            for link in list(page.get_links() or []):
                link_rect = tuple(round(float(value), 3) for value in link.get("from", ()))
                links.append((int(link.get("kind", -1)), int(link.get("page", -1)),
                              str(link.get("uri") or ""), link_rect))
            page_data.append((int(page.rotation), tuple(annotations), tuple(sorted(links))))
        return tuple(page_data)

    def save(self, save_as=False):
        """Write a verified PDF snapshot atomically, including every native annotation."""
        original_path = self.path
        target = original_path
        image_source = bool(getattr(self, "is_image_source", False))
        office_source = bool(getattr(self, "is_office_source", False))
        if save_as or image_source or office_source:
            source_for_name = str(getattr(self, "source_path", original_path) or original_path)
            suggested = str(Path(source_for_name).with_name(Path(source_for_name).stem + "_edited.pdf"))
            target = _engo_file_dialog(self, "Save edited document as PDF", "حفظ المستند المعدّل كملف PDF", suggested, "PDF files (*.pdf)", save=True)
            if not target:
                return False
            if not target.lower().endswith(".pdf"):
                target += ".pdf"
        target = os.path.abspath(target)
        directory = os.path.dirname(target)
        fd, temp_path = tempfile.mkstemp(prefix=".engo_save_", suffix=".pdf", dir=directory)
        original_doc = self.doc
        payload = None
        replaced = False
        try:
            # Serialize to bytes first. This captures live PyMuPDF annotation updates
            # even when a UI code path did not set DocumentTab.dirty itself.
            payload = original_doc.tobytes(
                garbage=4, deflate=True, deflate_images=True, deflate_fonts=True
            )
            if not payload or not payload.startswith(b"%PDF-"):
                raise RuntimeError("The edited document did not produce a valid PDF stream.")

            # Some PDF edits (notably newly inserted links) become fully enumerable
            # only after MuPDF serializes the in-memory document. Compare the actual
            # on-disk temp file with that normalized serialized snapshot, not with
            # the pre-save in-memory view.
            serialized_doc = fitz.open(stream=payload, filetype="pdf")
            try:
                serialized_signature = self._pdf_persistence_signature(serialized_doc)
            finally:
                serialized_doc.close()

            with os.fdopen(fd, "wb") as output_file:
                fd = -1
                output_file.write(payload)
                output_file.flush()
                os.fsync(output_file.fileno())

            verification_doc = fitz.open(temp_path)
            try:
                verified_signature = self._pdf_persistence_signature(verification_doc)
                if verified_signature != serialized_signature:
                    raise RuntimeError(
                        "The saved PDF did not retain all page rotations, annotations, and links. "
                        "The original file has been left untouched."
                    )
            finally:
                verification_doc.close()

            # Close the source handle only after a valid replacement is ready;
            # Windows may otherwise reject the atomic replace while the source is open.
            try:
                original_doc.close()
            except Exception:
                pass
            os.replace(temp_path, target)
            replaced = True
            temp_path = ""
            new_doc = fitz.open(target)
            self.doc = new_doc
            self.path = target
            self.source_path = target
            self.display_path = target
            self.is_image_source = False
            self.is_office_source = False
            try:
                self._primary_thumb_label.setText(Path(target).name)
                self._primary_thumb_label.updateGeometry()
                self._primary_thumb_label.parentWidget().updateGeometry()
            except Exception:
                pass
            self.selected_annotation = None
            self.selected_annotations = []
            self.selected_page_link = None
            self.annotationSelectionChanged.emit(False)
            self.page_count = self.doc.page_count
            self.page_sizes = [
                (float(self.doc.load_page(i).rect.width), float(self.doc.load_page(i).rect.height))
                for i in range(self.page_count)
            ]
            self.dirty = False
            try:
                self._saved_pdf_signature = self._pdf_persistence_signature(self.doc)
            except Exception:
                self._saved_pdf_signature = None
            self.render_version += 1
            self.page_render_versions = [self.render_version] * self.page_count
            self._thumbnail_cache.clear()
            self.canvas.clear_cache(clear_smart=True)
            self._build_thumbnails()
            if self.thumbnails.count():
                self._sync_sidebar_selection()
            self._build_outline()
            self._relayout()
            self.titleChanged.emit(self.tab_title())
            self.documentChanged.emit()
            self.historyChanged.emit(bool(self.undo_stack), bool(self.redo_stack))
            return True
        except Exception as exc:
            # Keep the edited in-memory document alive even if the final disk replace
            # is blocked by permissions, cloud sync, antivirus, or another process.
            try:
                if getattr(original_doc, "is_closed", False) and payload:
                    self.doc = fitz.open(stream=payload, filetype="pdf")
                    self.dirty = not replaced
                    if replaced:
                        self.path = target
                elif not getattr(original_doc, "is_closed", False):
                    self.doc = original_doc
            except Exception:
                pass
            QMessageBox.critical(
                self, APP_NAME,
                f"Could not complete PDF save. Your in-memory edits have been kept. If the replacement did not complete, the original PDF remains untouched.\n\n{exc}"
            )
            return False
        finally:
            if fd >= 0:
                try:
                    os.close(fd)
                except Exception:
                    pass
            if temp_path and os.path.exists(temp_path):
                try:
                    os.remove(temp_path)
                except Exception:
                    pass

    def close_document(self):
        """Close a PDF only after making every deferred paint/layout safe."""
        if getattr(self, "_document_closing", False):
            return
        self._document_closing = True
        timer = getattr(self, "_layout_timer", None)
        if timer is not None:
            try:
                timer.stop()
            except RuntimeError:
                pass
        for canvas in (getattr(self, "canvas", None), getattr(self, "_secondary_canvas", None)):
            if canvas is not None:
                try:
                    canvas.page_rects.clear()
                    canvas.page_scales.clear()
                    canvas.cache.clear()
                    canvas.update()
                except RuntimeError:
                    pass
        doc = getattr(self, "doc", None)
        try:
            if doc is not None and not bool(getattr(doc, "is_closed", False)):
                doc.close()
        except Exception:
            pass
