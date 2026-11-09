# Auto-split from main.py (verbatim move; do not reformat).
from __future__ import annotations

import math
import time
from functools import lru_cache
from pathlib import Path
import pymupdf as fitz  # use the maintained import name; keep fitz alias for existing calls
from PIL import Image, ImageOps, ImageChops, ImageFilter
try:
    import numpy as _engo_np
    import cv2 as _engo_cv2
except Exception:
    _engo_np = None
    _engo_cv2 = None
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
    DEFAULT_ANNOTATION_COLORS,
    IMAGE_DOCUMENT_EXTENSIONS,
    POWERPOINT_DOCUMENT_EXTENSIONS,
    WORD_DOCUMENT_EXTENSIONS,
    _engo_dialog_host_settings,
    _engo_translate_tooltip,
    engo_ui_theme_tokens,
    normalize_ui_theme,
)




class ResponsiveSidebarTabs(QWidget):
    """Compact Pages/Contents switcher that stacks its buttons when the sidebar narrows."""
    def __init__(self, parent=None, language="en"):
        super().__init__(parent)
        self.setObjectName("sideTabs")
        self._language = "ar" if str(language).lower().startswith("ar") else "en"
        self._current_index = -1
        self._buttons = []
        self._stack = QStackedWidget(self)
        self._stack.setObjectName("sidebarTabStack")

        self._nav_host = QWidget(self)
        self._nav_host.setObjectName("sidebarTabNav")
        # Pages, Contents and the compact page-overview action live in one grid so
        # the sidebar can shrink freely (drag-resize) and re-flow when squeezed:
        #   wide   : [ Pages ][ Contents ][ overview ]
        #   narrow : [        Pages        ]
        #            [ Contents ][ overview ]
        self._nav_layout = QGridLayout(self._nav_host)
        self._nav_layout.setContentsMargins(0, 0, 0, 0)
        self._nav_layout.setHorizontalSpacing(5)
        self._nav_layout.setVerticalSpacing(3)
        self._nav_host.setFixedHeight(32)
        self._trailing_widget = None
        # Keep the strip narrow enough to be dragged small, but never so small
        # that the Contents label and the overview action are crushed.
        self.setMinimumWidth(96)

        root = QVBoxLayout(self)
        root.setContentsMargins(0, 0, 0, 0)
        root.setSpacing(0)
        root.addWidget(self._nav_host, 0)
        root.addWidget(self._stack, 1)
        self._vertical_nav = None

    def addTab(self, widget, icon, text):
        original = str(text or "")
        localized = {"Pages": "الصفحات", "Contents": "المحتوى"}.get(original, original) if self._language == "ar" else original
        button = QPushButton(localized, self._nav_host)
        button.setObjectName("sideTabButton")
        button.setProperty("engoOriginalText", original)
        button.setProperty("engoIconName", "pages" if original == "Pages" else "contents")
        button.setToolTip("Show page thumbnails" if original == "Pages" else "Show the document outline")
        button.setProperty("engoOriginalToolTip", button.toolTip())
        button.setIcon(icon)
        button.setIconSize(QSize(15, 15))
        button.setCheckable(True)
        button.setCursor(Qt.CursorShape.PointingHandCursor)
        button.setMinimumWidth(0)
        button.setFixedHeight(32)
        # Ignored: the button never forces a minimum sidebar width, so the splitter
        # can always be dragged narrower (this is what the extra icon had broken).
        button.setSizePolicy(QSizePolicy.Policy.Ignored, QSizePolicy.Policy.Fixed)
        index = self._stack.addWidget(widget)
        button.clicked.connect(lambda _checked=False, i=index: self.setCurrentIndex(i))
        self._buttons.append(button)
        if self._current_index < 0:
            self.setCurrentIndex(0)
        self._vertical_nav = None
        self._update_nav_mode()
        return index

    def setTrailingWidget(self, widget):
        """Place one compact action beside the responsive Pages/Contents tabs."""
        if self._trailing_widget is widget:
            return
        if self._trailing_widget is not None:
            self._nav_layout.removeWidget(self._trailing_widget)
            self._trailing_widget.setParent(None)
        self._trailing_widget = widget
        if widget is not None:
            widget.setParent(self._nav_host)
            widget.setFixedHeight(32)
            widget.setSizePolicy(QSizePolicy.Policy.Fixed, QSizePolicy.Policy.Fixed)
            widget.show()
        self._vertical_nav = None
        self._update_nav_mode()

    def count(self):
        return self._stack.count()

    def currentIndex(self):
        return self._current_index

    def widget(self, index):
        return self._stack.widget(int(index))

    def setCurrentIndex(self, index):
        index = int(index)
        if not 0 <= index < self._stack.count():
            return
        self._current_index = index
        self._stack.setCurrentIndex(index)
        for i, button in enumerate(self._buttons):
            active = (i == index)
            button.setChecked(active)
            button.setProperty("sidebarTabActive", active)
            button.style().unpolish(button)
            button.style().polish(button)
            button.update()

    def setLanguage(self, language):
        self._language = "ar" if str(language).lower().startswith("ar") else "en"
        for button in self._buttons:
            original = str(button.property("engoOriginalText") or button.text())
            button.setText({"Pages": "الصفحات", "Contents": "المحتوى"}.get(original, original) if self._language == "ar" else original)
            source_tip = "Show page thumbnails" if original == "Pages" else "Show the document outline"
            button.setToolTip(_engo_translate_tooltip(source_tip, self._language))
            button.setProperty("engoOriginalToolTip", source_tip)
            button.setProperty("engoRenderedToolTip", button.toolTip())
        self._update_nav_mode()

    def setIconColor(self, color=None):
        """Refresh sidebar glyphs using an explicit color or the current app theme."""
        if not color:
            try:
                host = self.window()
                settings = getattr(host, "settings", None)
                theme_name = settings.value("ui_theme", "dark", type=str) if settings is not None else "dark"
                color = engo_ui_theme_tokens(theme_name)["text"]
            except Exception:
                color = "#e6efff"
        color = str(color)
        icon_widgets = list(self._buttons)
        if self._trailing_widget is not None:
            icon_widgets.append(self._trailing_widget)
        for button in icon_widgets:
            icon_name = str(button.property("engoIconName") or "")
            if not icon_name:
                continue
            button.setIcon(make_icon(icon_name, color, 18))
            button.setIconSize(QSize(15, 15) if button in self._buttons else QSize(16, 16))
            button.update()

        # The compact page-overview action is a real third sidebar card, not a
        # transparent floating glyph. Keep its shape/states aligned with Pages
        # and Contents while allowing it to remain narrower than the text tabs.
        if self._trailing_widget is not None and self._trailing_widget.objectName() == "pageOverviewButton":
            try:
                host = self.window()
                settings = getattr(host, "settings", None)
                theme_name = normalize_ui_theme(
                    settings.value("ui_theme", "dark", type=str) if settings is not None else "dark"
                )
                tokens = engo_ui_theme_tokens(theme_name)
                selected_bg = tokens["panel"] if theme_name == "midnight" else tokens["selection"]
                self._trailing_widget.setStyleSheet(f"""
                    QToolButton#pageOverviewButton {{
                        background: {tokens['panel_alt']}; color: {tokens['muted']};
                        border: 1px solid {tokens['border']}; border-radius: 7px;
                        padding: 0px; margin: 0px;
                    }}
                    QToolButton#pageOverviewButton:hover {{
                        background: {tokens['hover']}; color: {tokens['text']};
                        border: 1px solid {tokens['accent']};
                    }}
                    QToolButton#pageOverviewButton:checked,
                    QToolButton#pageOverviewButton:checked:hover {{
                        background: {selected_bg}; color: {tokens['text']};
                        border: 1px solid {tokens['accent']};
                        border-bottom: 1px solid {tokens['accent']};
                    }}
                """)
                self._trailing_widget.setAutoRaise(False)
            except (RuntimeError, AttributeError):
                pass

    def showEvent(self, event):
        super().showEvent(event)
        # Parent theme application can happen before a tab is first shown.
        # Resolve the active palette here instead of calling setIconColor without
        # a color argument (which previously raised TypeError on every show).
        self.setIconColor()

    def _update_nav_mode(self):
        # Below this width the strip re-flows into two rows:
        # Pages on top, Contents + the overview action underneath.
        vertical = self.width() < 176
        if vertical == self._vertical_nav:
            return
        self._vertical_nav = vertical
        lay = self._nav_layout
        items = list(self._buttons)
        if self._trailing_widget is not None:
            items.append(self._trailing_widget)
        for w in items:
            lay.removeWidget(w)
        for c in range(4):
            lay.setColumnStretch(c, 0)
        pages = self._buttons[0] if len(self._buttons) > 0 else None
        contents = self._buttons[1] if len(self._buttons) > 1 else None
        trailing = self._trailing_widget
        if vertical:
            if pages is not None:
                lay.addWidget(pages, 0, 0, 1, 2)
            if contents is not None:
                lay.addWidget(contents, 1, 0)
            if trailing is not None:
                lay.addWidget(trailing, 1, 1, Qt.AlignmentFlag.AlignVCenter)
            lay.setColumnStretch(0, 1)
            self._nav_host.setFixedHeight(32 + 3 + 32)
        else:
            col = 0
            for b in self._buttons:
                lay.addWidget(b, 0, col)
                lay.setColumnStretch(col, 1)
                col += 1
            if trailing is not None:
                lay.addWidget(trailing, 0, col, Qt.AlignmentFlag.AlignVCenter)
            self._nav_host.setFixedHeight(32)
        for b in self._buttons:
            b.setFixedHeight(32)
            b.setSizePolicy(QSizePolicy.Policy.Ignored, QSizePolicy.Policy.Fixed)
            b.show()
        lay.activate()

    def resizeEvent(self, event):
        super().resizeEvent(event)
        self._update_nav_mode()

class EngoFileSystemModel(QFileSystemModel):
    """Home file tree with consistent in-app file and image glyphs (no OS icons)."""

    _engo_icons = {}

    @classmethod
    def _make_engo_icon(cls, kind: str) -> QIcon:
        cached = cls._engo_icons.get(kind)
        if cached is not None:
            return cached
        size = 24
        pixmap = QPixmap(size, size)
        pixmap.fill(Qt.GlobalColor.transparent)
        painter = QPainter(pixmap)
        painter.setRenderHint(QPainter.RenderHint.Antialiasing, True)
        # File-type colors are intentional and independent from the active UI theme:
        # PDF red, PowerPoint yellow, Word blue, and images retain their green accent.
        accent = QColor({
            "pdf": "#e34b4b",
            "powerpoint": "#e2bd38",
            "word": "#3985d6",
            "image": "#59bca0",
            "file": "#75a7e8",
        }.get(kind, "#75a7e8"))
        pale = QColor(accent)
        pale.setAlpha(42)
        outline = QColor(accent)
        outline.setAlpha(235)
        page = QPainterPath()
        page.moveTo(5.0, 2.5)
        page.lineTo(14.8, 2.5)
        page.lineTo(20.0, 7.7)
        page.lineTo(20.0, 21.0)
        page.quadTo(20.0, 22.0, 19.0, 22.0)
        page.lineTo(6.0, 22.0)
        page.quadTo(4.5, 22.0, 4.5, 20.5)
        page.lineTo(4.5, 4.0)
        page.quadTo(4.5, 2.5, 5.0, 2.5)
        page.closeSubpath()
        painter.setPen(QPen(outline, 1.25))
        painter.setBrush(QBrush(pale))
        painter.drawPath(page)
        fold = QPainterPath()
        fold.moveTo(14.5, 2.8)
        fold.lineTo(14.5, 7.9)
        fold.lineTo(19.6, 7.9)
        painter.setBrush(QBrush(accent))
        painter.setPen(QPen(outline, 1.0))
        painter.drawPath(fold)
        painter.setPen(QPen(outline, 1.25, Qt.PenStyle.SolidLine, Qt.PenCapStyle.RoundCap))
        if kind == "image":
            painter.setBrush(Qt.BrushStyle.NoBrush)
            painter.drawEllipse(QRectF(8.2, 10.0, 2.8, 2.8))
            mountain = QPainterPath()
            mountain.moveTo(7.2, 18.4)
            mountain.lineTo(11.5, 14.2)
            mountain.lineTo(14.0, 16.2)
            mountain.lineTo(16.2, 13.7)
            mountain.lineTo(18.3, 18.4)
            painter.drawPath(mountain)
        else:
            painter.drawLine(QPointF(8.0, 11.0), QPointF(16.8, 11.0))
            painter.drawLine(QPointF(8.0, 14.0), QPointF(16.8, 14.0))
            painter.drawLine(QPointF(8.0, 17.0), QPointF(14.4, 17.0))
        painter.end()
        icon = QIcon(pixmap)
        cls._engo_icons[kind] = icon
        return icon

    def data(self, index, role=Qt.ItemDataRole.DisplayRole):
        if (index.isValid() and index.column() == 0
                and role == Qt.ItemDataRole.DecorationRole):
            try:
                if self.isDir(index):
                    return QIcon()
                path = self.filePath(index)
                suffix = Path(path).suffix.lower()
                if suffix == ".pdf":
                    kind = "pdf"
                elif suffix in POWERPOINT_DOCUMENT_EXTENSIONS:
                    kind = "powerpoint"
                elif suffix in WORD_DOCUMENT_EXTENSIONS:
                    kind = "word"
                elif suffix in IMAGE_DOCUMENT_EXTENSIONS:
                    kind = "image"
                else:
                    kind = "file"
                return self._make_engo_icon(kind)
            except (RuntimeError, TypeError, OSError):
                return self._make_engo_icon("file")
        return super().data(index, role)


class MiddleMouseAutoScroll(QObject):
    """Browser-style middle-button auto-scroll for Engo's scrollable views.

    Click the wheel once to anchor the scroll marker, move the pointer away to
    control direction and speed, and click the wheel again (or press Esc) to stop.
    The timer drives the scroll bars directly, so this works with PDF canvases,
    page lists, text browsers, and nested scroll areas without synthesizing wheel
    events or interfering with the PDF canvas' left-button tools.
    """

    _DEAD_ZONE = 14
    _MAX_SPEED = 1750.0  # pixels per second
    _TIMER_INTERVAL_MS = 16

    def __init__(self, owner: QWidget):
        super().__init__(owner)
        self._owner = owner
        self._app = QApplication.instance()
        self._area = None
        self._anchor = QPoint()
        self._last_tick = 0.0
        self._fraction_x = 0.0
        self._fraction_y = 0.0
        self._marker = None
        self._active = False
        self._timer = QTimer(self)
        self._timer.setTimerType(Qt.TimerType.PreciseTimer)
        self._timer.setInterval(self._TIMER_INTERVAL_MS)
        self._timer.timeout.connect(self._tick)
        if self._app is not None:
            self._app.installEventFilter(self)

    @property
    def active(self) -> bool:
        return self._active

    def _owns_widget(self, widget: QWidget) -> bool:
        try:
            return widget is self._owner or self._owner.isAncestorOf(widget)
        except RuntimeError:
            return False

    def _find_scroll_area(self, widget):
        """Return the nearest ancestor scroll area that can actually scroll."""
        while isinstance(widget, QWidget):
            if isinstance(widget, QAbstractScrollArea):
                try:
                    vertical = widget.verticalScrollBar()
                    horizontal = widget.horizontalScrollBar()
                    if (vertical.maximum() > vertical.minimum() or
                            horizontal.maximum() > horizontal.minimum()):
                        return widget
                except RuntimeError:
                    pass
            try:
                widget = widget.parentWidget()
            except RuntimeError:
                break
        return None

    def _scroll_area_at(self, global_pos: QPoint, watched):
        candidate = None
        try:
            candidate = QApplication.widgetAt(global_pos)
        except RuntimeError:
            pass
        if not isinstance(candidate, QWidget):
            candidate = watched if isinstance(watched, QWidget) else None
        if not isinstance(candidate, QWidget) or not self._owns_widget(candidate):
            return None
        return self._find_scroll_area(candidate)

    def _show_anchor_marker(self, area: QAbstractScrollArea):
        try:
            window = area.window()
            marker = QLabel("✥", window)
            marker.setObjectName("middleAutoScrollMarker")
            marker.setAlignment(Qt.AlignmentFlag.AlignCenter)
            marker.setFixedSize(30, 30)
            marker.setAttribute(Qt.WidgetAttribute.WA_TransparentForMouseEvents, True)
            marker.setAttribute(Qt.WidgetAttribute.WA_ShowWithoutActivating, True)
            marker.setStyleSheet(
                "QLabel#middleAutoScrollMarker {"
                "background: rgba(24, 32, 45, 235);"
                "color: #eaf1ff;"
                "border: 1px solid #91b4ed;"
                "border-radius: 15px;"
                "font-family: 'Segoe UI Symbol';"
                "font-size: 19px;"
                "font-weight: 600;"
                "padding: 0px;"
                "}"
            )
            self._marker = marker
            self._move_marker()
            marker.show()
            marker.raise_()
        except (RuntimeError, AttributeError):
            self._marker = None

    def _move_marker(self):
        marker = self._marker
        if marker is None:
            return
        try:
            window = marker.parentWidget()
            if window is None:
                return
            local = window.mapFromGlobal(self._anchor)
            marker.move(local.x() - marker.width() // 2,
                        local.y() - marker.height() // 2)
        except RuntimeError:
            self._marker = None

    def start(self, area: QAbstractScrollArea, anchor: QPoint):
        self.stop()
        self._area = area
        self._anchor = QPoint(anchor)
        self._fraction_x = 0.0
        self._fraction_y = 0.0
        self._last_tick = time.monotonic()
        self._active = True
        self._show_anchor_marker(area)
        self._timer.start()

    def stop(self):
        self._timer.stop()
        self._active = False
        self._area = None
        marker, self._marker = self._marker, None
        if marker is not None:
            try:
                marker.hide()
                marker.deleteLater()
            except RuntimeError:
                pass
        self._fraction_x = 0.0
        self._fraction_y = 0.0

    @classmethod
    def _velocity(cls, distance: int) -> float:
        """Smoothly convert pointer distance from the anchor to scroll speed."""
        magnitude = abs(int(distance)) - cls._DEAD_ZONE
        if magnitude <= 0:
            return 0.0
        speed = min(cls._MAX_SPEED, 18.0 * (magnitude ** 1.22))
        return speed if distance > 0 else -speed

    @staticmethod
    def _advance_bar(bar, velocity: float, dt: float, remainder: float) -> float:
        if velocity == 0.0:
            return 0.0
        amount = velocity * dt + remainder
        step = int(amount)  # truncate toward zero while retaining fractional motion
        if step == 0:
            return amount
        old_value = bar.value()
        new_value = max(bar.minimum(), min(bar.maximum(), old_value + step))
        if new_value != old_value:
            bar.setValue(new_value)
        # Drop accumulated motion when a boundary is reached; it must not cause
        # an unexpected jump if the user moves the pointer back into the page.
        if new_value in (bar.minimum(), bar.maximum()) and new_value != old_value + step:
            return 0.0
        return amount - step

    def _tick(self):
        if not self._active:
            return
        area = self._area
        try:
            if area is None or not area.isVisible():
                self.stop()
                return
            vertical = area.verticalScrollBar()
            horizontal = area.horizontalScrollBar()
            # A destroyed/closing window or scroll area can invalidate its native
            # Qt handle between timer ticks. The exception path safely disarms it.
            now = time.monotonic()
            dt = max(0.001, min(0.05, now - self._last_tick))
            self._last_tick = now
            pointer = QCursor.pos()
            dx = pointer.x() - self._anchor.x()
            dy = pointer.y() - self._anchor.y()
            vx = self._velocity(dx) if horizontal.maximum() > horizontal.minimum() else 0.0
            vy = self._velocity(dy) if vertical.maximum() > vertical.minimum() else 0.0
            self._fraction_x = self._advance_bar(horizontal, vx, dt, self._fraction_x)
            self._fraction_y = self._advance_bar(vertical, vy, dt, self._fraction_y)
            self._move_marker()
        except (RuntimeError, AttributeError):
            self.stop()

    def eventFilter(self, watched, event):
        event_type = event.type()
        if event_type in (QEvent.Type.MouseButtonPress, QEvent.Type.MouseButtonDblClick):
            try:
                if event.button() == Qt.MouseButton.MiddleButton:
                    if self._active:
                        self.stop()
                        event.accept()
                        return True
                    global_pos = event.globalPosition().toPoint()
                    area = self._scroll_area_at(global_pos, watched)
                    if area is not None:
                        self.start(area, global_pos)
                        event.accept()
                        return True
                elif self._active and event.button() in (
                    Qt.MouseButton.LeftButton, Qt.MouseButton.RightButton
                ):
                    # A normal click cancels auto-scroll but is still delivered to
                    # the underlying control (selection, annotation, or button).
                    self.stop()
            except (RuntimeError, AttributeError):
                self.stop()
        elif self._active and event_type == QEvent.Type.KeyPress:
            try:
                if event.key() == Qt.Key.Key_Escape:
                    self.stop()
            except AttributeError:
                pass
        elif self._active and event_type == QEvent.Type.Wheel:
            # Hand control back to the user's wheel/touchpad gesture naturally.
            self.stop()
        elif self._active and event_type == QEvent.Type.ApplicationDeactivate:
            self.stop()
        return False


def image_to_qimage(image: Image.Image) -> QImage:
    image = image.convert("RGB")
    w, h = image.size
    return QImage(image.tobytes(), w, h, w * 3, QImage.Format.Format_RGB888).copy()


def color_tuple(hex_color: str):
    c = QColor(hex_color)
    return (c.redF(), c.greenF(), c.blueF())


def apply_page_theme_to_image(image: Image.Image, enabled: bool, bg: str, ink: str,
                              smart: bool = False) -> Image.Image:
    """Apply the display-only page palette to a rendered RGB image.

    Classic mode preserves the legacy two-color grayscale behavior. Smart mode
    recolors neutral paper, dark ink and blue ink while preserving other colors.
    Non-target colors receive only a restrained saturation/brightness lift.
    A local paper-context check suppresses mild gray scan blemishes without
    flattening the antialiased edges around real writing or colored markers.
    """
    source = image.convert("RGB")
    if not enabled:
        return source
    try:
        if not smart:
            return ImageOps.colorize(ImageOps.grayscale(source), black=ink, white=bg)

        def _shift_mask(mask: Image.Image, dx: int, dy: int) -> Image.Image:
            """Shift an 8-bit mask without wraparound; pixels outside are zero."""
            width, height = mask.size
            shifted = Image.new("L", (width, height), 0)
            source_x0 = max(0, -dx)
            source_y0 = max(0, -dy)
            source_x1 = min(width, width - dx)
            source_y1 = min(height, height - dy)
            if source_x1 > source_x0 and source_y1 > source_y0:
                shifted.paste(
                    mask.crop((source_x0, source_y0, source_x1, source_y1)),
                    (max(0, dx), max(0, dy)),
                )
            return shifted

        def _fast_max_filter(mask: Image.Image, kernel_size: int) -> Image.Image:
            """Exact square maximum filter with an optional native C++ backend.

            OpenCV's rectangular dilation is mathematically identical to Pillow's
            odd-sized MaxFilter for these masks, but runs in optimized native code.
            If OpenCV is unavailable, retain the exact Pillow-compatible fallback.
            """
            size = max(1, int(kernel_size) | 1)
            if size <= 1:
                return mask
            if _engo_cv2 is not None and _engo_np is not None:
                try:
                    array = _engo_np.asarray(mask, dtype=_engo_np.uint8)
                    kernel = _engo_cv2.getStructuringElement(
                        _engo_cv2.MORPH_RECT, (size, size)
                    )
                    filtered = _engo_cv2.dilate(
                        array, kernel, borderType=_engo_cv2.BORDER_REPLICATE
                    )
                    return Image.fromarray(filtered, mode="L")
                except Exception:
                    pass
            if _engo_np is not None:
                try:
                    # Exact separable square max filter without image copies per
                    # offset. This pure-NumPy fallback is also fast and needs no
                    # OpenCV installation; its output matches MaxFilter exactly.
                    array = _engo_np.asarray(mask, dtype=_engo_np.uint8)
                    radius = size // 2
                    horizontal = array.copy()
                    for offset in range(1, radius + 1):
                        _engo_np.maximum(horizontal[:, offset:], array[:, :-offset],
                                         out=horizontal[:, offset:])
                        _engo_np.maximum(horizontal[:, :-offset], array[:, offset:],
                                         out=horizontal[:, :-offset])
                    filtered = horizontal.copy()
                    for offset in range(1, radius + 1):
                        _engo_np.maximum(filtered[offset:, :], horizontal[:-offset, :],
                                         out=filtered[offset:, :])
                        _engo_np.maximum(filtered[:-offset, :], horizontal[offset:, :],
                                         out=filtered[:-offset, :])
                    return Image.fromarray(filtered, mode="L")
                except Exception:
                    pass
            radius = size // 2
            horizontal = mask
            for offset in range(1, radius + 1):
                horizontal = ImageChops.lighter(horizontal, _shift_mask(mask, -offset, 0))
                horizontal = ImageChops.lighter(horizontal, _shift_mask(mask, offset, 0))
            result = horizontal
            for offset in range(1, radius + 1):
                result = ImageChops.lighter(result, _shift_mask(horizontal, 0, -offset))
                result = ImageChops.lighter(result, _shift_mask(horizontal, 0, offset))
            return result

        hue, saturation, value = source.convert("HSV").split()
        red, green, blue = source.split()

        bg_color = QColor(str(bg))
        ink_color = QColor(str(ink))
        background_layer = Image.new(
            "RGB", source.size, (bg_color.red(), bg_color.green(), bg_color.blue())
        )
        ink_layer = Image.new(
            "RGB", source.size, (ink_color.red(), ink_color.green(), ink_color.blue())
        )

        max_rgb = ImageChops.lighter(ImageChops.lighter(red, green), blue)
        min_rgb = ImageChops.darker(ImageChops.darker(red, green), blue)
        chroma = ImageChops.subtract(max_rgb, min_rgb)
        luminance = ImageOps.grayscale(source)

        # Slightly improve the liveliness of preserved colored content. The hue
        # stays unchanged; saturation rises by only 6%, and brightness receives
        # at most a 2.5% lift. Neutral scan texture and black handwriting are not
        # boosted, preventing unwanted emphasis of grayscale defects.
        colored_pixels = saturation.point(lambda v: 255 if v >= 34 else 0)
        boosted_saturation = saturation.point(
            lambda v: min(255, int(round(v * 1.06)))
        )
        boosted_value = value.point(
            lambda v: min(255, int(round(v + (255 - v) * 0.025)))
        )
        boosted_colors = Image.merge(
            "HSV", (hue, boosted_saturation, boosted_value)
        ).convert("RGB")
        enhanced_source = Image.composite(boosted_colors, source, colored_pixels)

        # Detect green highlighter pigment before recoloring ink. Its expanded
        # footprint protects black handwriting and antialiased pen edges.
        green_hue = hue.point(lambda h: 255 if 48 <= h <= 116 else 0)
        green_sat = saturation.point(
            lambda v: 0 if v <= 26 else (255 if v >= 48 else int((v - 26) * 255 / 22))
        )
        green_value = value.point(lambda v: 255 if 92 <= v <= 252 else 0)
        green_highlighter_core = ImageChops.multiply(
            ImageChops.multiply(green_hue, green_sat), green_value
        )
        green_highlighter_region = _fast_max_filter(green_highlighter_core, 9)
        outside_green_highlighter = ImageOps.invert(green_highlighter_region)

        # Keep the V11 handwriting recognition thresholds: they were tuned to
        # preserve real pen strokes while distinguishing isolated scan defects.
        black_core_value = luminance.point(lambda v: 255 if v <= 92 else 0)
        black_core_neutral = chroma.point(lambda v: 255 if v <= 50 else 0)
        black_core = ImageChops.multiply(black_core_value, black_core_neutral)
        black_neighborhood = _fast_max_filter(black_core, 5)
        black_edge_neutral = chroma.point(lambda v: 255 if v <= 58 else 0)
        black_region = ImageChops.multiply(black_neighborhood, black_edge_neutral)
        black_coverage = luminance.point(
            lambda v: 255 if v <= 78 else (0 if v >= 255 else int((255 - v) * 255 / 177))
        )
        black_ink_mask = ImageChops.multiply(black_region, black_coverage)

        # Blue handwriting receives the same careful edge handling. Saturated
        # colored marks with other hues remain outside this mask.
        blue_hue = hue.point(lambda h: 140 <= h <= 185 and 255 or 0)
        blue_sat = saturation.point(
            lambda v: 0 if v <= 82 else (255 if v >= 125 else int((v - 82) * 255 / 43))
        )
        blue_value = value.point(
            lambda v: 0 if v <= 45 else (255 if v >= 82 else int((v - 45) * 255 / 37))
        )
        blue_core = ImageChops.multiply(ImageChops.multiply(blue_hue, blue_sat), blue_value)
        blue_neighborhood = _fast_max_filter(blue_core, 5)
        blue_edge_neutral = chroma.point(lambda v: 255 if v <= 62 else 0)
        blue_edge_region = ImageChops.multiply(blue_neighborhood, blue_edge_neutral)
        blue_region = ImageChops.lighter(blue_core, blue_edge_region)
        blue_edge_coverage = luminance.point(
            lambda v: 255 if v <= 78 else (0 if v >= 255 else int((255 - v) * 255 / 177))
        )
        blue_ink_mask = ImageChops.lighter(
            blue_core, ImageChops.multiply(blue_edge_region, blue_edge_coverage)
        )

        # Standard white-paper detection remains conservative. In addition, catch
        # mildly gray pixels only when a clearly white paper area exists nearby.
        # This local-context test targets scan dust/shadows instead of labeling
        # every gray pixel as paper, which was the source of previous halos.
        paper_value = value.point(lambda v: 255 if v >= 242 else 0)
        paper_neutral = saturation.point(lambda v: 255 if v <= 18 else 0)
        paper_mask = ImageChops.multiply(paper_value, paper_neutral)

        # A wider local paper window catches faint scanner dust, gray mottling,
        # and low-contrast background stains that were still visible after the
        # previous pass. The stroke guards below are deliberately wider too, so
        # pale handwriting edges are not mistaken for page defects.
        nearby_white_paper = _fast_max_filter(luminance, 25).point(
            lambda v: 255 if v >= 246 else 0
        )
        mild_gray_scan = value.point(lambda v: 255 if 204 <= v <= 241 else 0)
        neutral_scan = saturation.point(lambda v: 255 if v <= 24 else 0)
        scan_defect_mask = ImageChops.multiply(
            ImageChops.multiply(mild_gray_scan, neutral_scan), nearby_white_paper
        )
        paper_mask = ImageChops.lighter(paper_mask, scan_defect_mask)

        # Protect only the actual ink neighborhoods already detected above.
        # The previous 17x17 dilation created a wide untouched gray/white halo
        # around every printed or handwritten stroke. black_region/blue_region
        # already include a narrow 5x5 antialias fringe, so no extra dilation is
        # needed. The marker's detected band protects its own soft boundary.
        dark_stroke_protection = black_region
        blue_stroke_protection = blue_region
        # Only the detected marker pigment needs protection from scan cleanup.
        # Do not dilate this paper-protection mask: doing so leaves pale rings
        # around the edges of otherwise clean highlighter strokes.
        marker_protection = green_highlighter_core
        protected_content = ImageChops.lighter(
            ImageChops.lighter(dark_stroke_protection, blue_stroke_protection),
            marker_protection,
        )
        paper_mask = ImageChops.multiply(paper_mask, ImageOps.invert(protected_content))

        result = Image.composite(background_layer, enhanced_source, paper_mask)

        # Keep black AND blue handwriting over a green highlighter exactly as
        # written. Exclude both each pen's core and its antialiased edge region
        # from Smart Theme recoloring, so colored marker text stays legible and
        # does not turn into pale ink over a bright green highlight.
        black_region = ImageChops.multiply(black_region, outside_green_highlighter)
        black_ink_mask = ImageChops.multiply(black_ink_mask, outside_green_highlighter)
        blue_region = ImageChops.multiply(blue_region, outside_green_highlighter)
        blue_ink_mask = ImageChops.multiply(blue_ink_mask, outside_green_highlighter)

        result = Image.composite(background_layer, result, black_region)
        result = Image.composite(ink_layer, result, black_ink_mask)
        result = Image.composite(background_layer, result, blue_region)
        result = Image.composite(ink_layer, result, blue_ink_mask)
        return result
    except Exception:
        # A malformed custom palette or unusual image codec must never make a PDF
        # unavailable. Preserve the original page if smart recoloring fails.
        return source


def _qt_thread_is_running(worker) -> bool:
    """Safely query a Qt worker whose C++ QObject may already have been deleted."""
    if worker is None:
        return False
    try:
        return bool(worker.isRunning())
    except RuntimeError:
        return False


# All interface icons are drawn as clean vector strokes at runtime: no font glyphs,
# emoji, or external icon packs are used. They stay crisp at every Windows DPI scale.
@lru_cache(maxsize=160)
def make_icon(name: str, color: str = "#b7c6dc", size: int = 18) -> QIcon:
    pm = QPixmap(size, size)
    pm.fill(Qt.GlobalColor.transparent)
    painter = QPainter(pm)
    painter.setRenderHint(QPainter.RenderHint.Antialiasing, True)
    painter.scale(size / 24.0, size / 24.0)
    pen = QPen(QColor(color), 1.75, Qt.PenStyle.SolidLine,
               Qt.PenCapStyle.RoundCap, Qt.PenJoinStyle.RoundJoin)
    painter.setPen(pen)
    painter.setBrush(Qt.BrushStyle.NoBrush)

    def line(x1, y1, x2, y2):
        painter.drawLine(QPointF(x1, y1), QPointF(x2, y2))

    def path(points, close=False, fill=False):
        pth = QPainterPath()
        if not points:
            return
        pth.moveTo(QPointF(*points[0]))
        for xy in points[1:]:
            pth.lineTo(QPointF(*xy))
        if close:
            pth.closeSubpath()
        if fill:
            painter.save()
            painter.setPen(Qt.PenStyle.NoPen)
            painter.setBrush(QColor(color))
            painter.drawPath(pth)
            painter.restore()
        else:
            painter.drawPath(pth)

    if name == "close":
        # Balanced, centered vector X: avoids platform-dependent native tab-close glyphs.
        line(7, 7, 17, 17)
        line(17, 7, 7, 17)
    elif name == "tag":
        path([(3, 5), (13, 5), (21, 13), (13, 21), (3, 11), (3, 5)])
        painter.drawEllipse(QRectF(6, 8, 2.4, 2.4))
    elif name in ("toolbar_hide", "toolbar_show"):
        painter.drawRoundedRect(QRectF(3, 4, 18, 16), 2, 2)
        line(3, 9, 21, 9)
        if name == "toolbar_hide":
            path([(8, 16), (12, 12), (16, 16)])
        else:
            path([(8, 13), (12, 17), (16, 13)])
    elif name == "home":
        path([(2.5, 11), (12, 3), (21.5, 11)])
        path([(5, 10), (5, 21), (19, 21), (19, 10)])
        path([(10, 21), (10, 14), (14, 14), (14, 21)])
    elif name == "open":
        path([(3, 9), (3, 6), (10, 6), (12, 8), (21, 8), (21, 18), (3, 18), (3, 9)])
        line(12, 4, 12, 13); line(9, 7, 12, 4); line(15, 7, 12, 4)
    elif name == "search":
        painter.drawEllipse(QRectF(3.5, 3.5, 12, 12))
        line(14.5, 14.5, 21, 21)
    elif name == "save":
        path([(5, 3), (17, 3), (21, 7), (21, 21), (3, 21), (3, 3), (5, 3)])
        painter.drawRect(QRectF(7, 3.5, 9, 6))
        painter.drawRect(QRectF(7, 14, 10, 7))
        line(10, 4, 10, 8); line(13, 4, 13, 8)
    elif name == "save_as":
        path([(5, 3), (15, 3), (20, 8), (20, 14), (17, 14), (17, 9), (14, 9), (14, 6), (5, 6), (5, 21), (13, 21)])
        painter.drawEllipse(QRectF(12.5, 12.5, 9, 9))
        line(17, 14.5, 17, 19.5); line(14.5, 17, 19.5, 17)
    elif name == "sidebar":
        painter.drawRoundedRect(QRectF(3, 4, 18, 16), 2, 2)
        line(9, 4, 9, 20); line(5.5, 8, 7, 8); line(5.5, 11, 7, 11); line(12, 8, 18, 8); line(12, 12, 18, 12); line(12, 16, 17, 16)
    elif name == "continuous":
        painter.drawRoundedRect(QRectF(4, 3, 16, 7), 1.5, 1.5)
        painter.drawRoundedRect(QRectF(4, 12, 16, 8), 1.5, 1.5)
        line(7, 6.5, 17, 6.5); line(7, 15.5, 17, 15.5); line(7, 18, 14, 18)
    elif name == "book":
        path([(3, 5), (8, 4), (12, 6), (12, 20), (8, 18), (3, 19), (3, 5)])
        path([(21, 5), (16, 4), (12, 6), (12, 20), (16, 18), (21, 19), (21, 5)])
        line(6, 8, 9, 8); line(6, 11, 9, 11); line(15, 8, 18, 8); line(15, 11, 18, 11)
    elif name == "voice_learn":
        # Open book + live audio waves: identifies a spoken tutor teaching from a PDF.
        path([(2.5, 6), (6.5, 4.5), (11.5, 6.5), (11.5, 20),
              (7, 18), (2.5, 19), (2.5, 6)])
        path([(21.5, 6), (17.5, 4.5), (12.5, 6.5), (12.5, 20),
              (17, 18), (21.5, 19), (21.5, 6)])
        line(5, 9, 8.5, 9); line(5, 12, 8.5, 12); line(5, 15, 8.5, 15)
        # A small waveform on the right page, with sound arcs above it.
        for x, top, bottom in ((15, 10, 14), (17, 8, 16), (19, 10, 14)):
            line(x, top, x, bottom)
        wave = QPainterPath(QPointF(16.2, 2.2))
        wave.cubicTo(QPointF(20.2, 4.2), QPointF(20.2, 7.2), QPointF(16.2, 9.2))
        painter.drawPath(wave)
    elif name in ("zoom_in", "zoom_out"):
        painter.drawEllipse(QRectF(3, 3, 13, 13)); line(14, 14, 21, 21)
        line(6.5, 9.5, 12.5, 9.5)
        if name == "zoom_in": line(9.5, 6.5, 9.5, 12.5)
    elif name == "fit_width":
        line(3, 12, 21, 12); path([(7, 8), (3, 12), (7, 16)]); path([(17, 8), (21, 12), (17, 16)])
        line(8, 5, 16, 5); line(8, 19, 16, 19)
    elif name == "fit_page":
        path([(9, 3), (3, 3), (3, 9)]); path([(15, 3), (21, 3), (21, 9)])
        path([(3, 15), (3, 21), (9, 21)]); path([(21, 15), (21, 21), (15, 21)])
        painter.drawRect(QRectF(8, 8, 8, 8))
    elif name == "rotate_cw":
        # Page rotation: a clear clockwise circular arrow.
        arc = QPainterPath(QPointF(19, 9))
        arc.cubicTo(QPointF(17, 4), QPointF(10, 2.5), QPointF(6, 6))
        arc.cubicTo(QPointF(2.5, 9.5), QPointF(3.5, 16), QPointF(8, 19))
        arc.cubicTo(QPointF(12, 21.5), QPointF(18, 19.5), QPointF(20, 15))
        painter.drawPath(arc)
        path([(14, 5), (20, 5), (20, 11)])
    elif name == "previous":
        path([(15, 5), (8, 12), (15, 19)])
    elif name == "next":
        path([(9, 5), (16, 12), (9, 19)])
    elif name == "select":
        path([(5, 3), (5, 19), (9, 15), (12, 21), (15, 19), (12, 13), (18, 13), (5, 3)], close=True, fill=True)
    elif name == "highlight":
        path([(5, 16), (14, 7), (18, 11), (9, 20), (5, 20), (5, 16)])
        line(13, 8, 17, 12); line(4, 21, 12, 21); line(14, 5, 16, 3)
    elif name == "pen":
        path([(4, 18), (5, 14), (16, 3), (21, 8), (10, 19), (4, 20), (4, 18)])
        line(13, 6, 18, 11); line(4, 20, 8, 16)
    elif name == "note":
        path([(4, 4), (20, 4), (20, 16), (12, 16), (7, 20), (7, 16), (4, 16), (4, 4)])
        line(8, 8, 16, 8); line(8, 11, 16, 11)
    elif name == "text":
        painter.drawRoundedRect(QRectF(4, 3, 16, 18), 2, 2)
        line(8, 7, 16, 7); line(12, 7, 12, 17); line(9, 17, 15, 17)
    elif name == "link":
        painter.drawRoundedRect(QRectF(2.5, 7, 12, 9), 4, 4)
        painter.drawRoundedRect(QRectF(9.5, 7, 12, 9), 4, 4)
        line(8, 11.5, 16, 11.5)
    elif name == "unlink":
        painter.drawRoundedRect(QRectF(2.5, 7, 12, 9), 4, 4)
        painter.drawRoundedRect(QRectF(9.5, 7, 12, 9), 4, 4)
        line(8, 11.5, 16, 11.5)
        line(4, 20, 20, 4)
    elif name in ("undo", "redo"):
        if name == "undo":
            path([(8, 7), (4, 7), (8, 3)]); curve = QPainterPath(QPointF(4, 7)); curve.cubicTo(QPointF(7, 4), QPointF(18, 4), QPointF(18, 12)); curve.cubicTo(QPointF(18, 17), QPointF(14, 19), QPointF(10, 19)); painter.drawPath(curve)
        else:
            path([(16, 7), (20, 7), (16, 3)]); curve = QPainterPath(QPointF(20, 7)); curve.cubicTo(QPointF(17, 4), QPointF(6, 4), QPointF(6, 12)); curve.cubicTo(QPointF(6, 17), QPointF(10, 19), QPointF(14, 19)); painter.drawPath(curve)
    elif name == "delete":
        line(4, 6, 20, 6); line(9, 3, 15, 3); line(6, 8, 7, 21); line(18, 8, 17, 21)
        line(7, 21, 17, 21); line(9, 10, 9.5, 18); line(14.5, 10, 14, 18)
    elif name in ("hand", "pan"):
        # Open hand / grab cursor, matching the standard PDF hand tool.
        hand_path = QPainterPath(QPointF(7.4, 11.2))
        hand_path.lineTo(7.4, 6.7)
        hand_path.cubicTo(QPointF(7.4, 4.2), QPointF(11.0, 4.2), QPointF(11.0, 6.7))
        hand_path.lineTo(11.0, 10.2)
        hand_path.lineTo(11.0, 5.2)
        hand_path.cubicTo(QPointF(11.0, 2.9), QPointF(14.4, 2.9), QPointF(14.4, 5.2))
        hand_path.lineTo(14.4, 10.4)
        hand_path.lineTo(14.4, 6.5)
        hand_path.cubicTo(QPointF(14.4, 4.3), QPointF(17.7, 4.3), QPointF(17.7, 6.5))
        hand_path.lineTo(17.7, 12.0)
        hand_path.lineTo(18.8, 10.9)
        hand_path.cubicTo(QPointF(21.5, 8.7), QPointF(23.1, 12.3), QPointF(21.0, 15.0))
        hand_path.lineTo(17.3, 20.1)
        hand_path.cubicTo(QPointF(16.5, 21.2), QPointF(15.2, 21.7), QPointF(13.8, 21.7))
        hand_path.lineTo(10.8, 21.7)
        hand_path.cubicTo(QPointF(9.2, 21.7), QPointF(8.0, 20.7), QPointF(7.4, 19.2))
        hand_path.lineTo(4.0, 13.4)
        hand_path.cubicTo(QPointF(2.6, 10.8), QPointF(5.6, 9.2), QPointF(7.4, 11.2))
        painter.drawPath(hand_path)
    elif name == "theme":
        painter.drawEllipse(QRectF(3, 3, 18, 18))
        painter.setBrush(QColor(color)); painter.drawPie(QRectF(3, 3, 18, 18), 90 * 16, 180 * 16)
        painter.setBrush(Qt.BrushStyle.NoBrush); painter.drawEllipse(QRectF(7, 7, 2, 2)); painter.drawEllipse(QRectF(14, 6, 2, 2)); painter.drawEllipse(QRectF(15, 15, 2, 2))
    elif name == "present":
        painter.drawRoundedRect(QRectF(3, 3, 18, 13), 2, 2)
        path([(10, 6.5), (10, 12.5), (15, 9.5)], close=True, fill=True)
        line(12, 16, 12, 20); line(8, 20, 16, 20)
    elif name in ("pin", "pin_off"):
        path([(8, 4), (16, 4), (15, 9), (18, 12), (18, 14), (6, 14), (6, 12), (9, 9), (8, 4)])
        line(12, 14, 12, 22)
        if name == "pin_off":
            line(4, 4, 20, 20)
    elif name == "fullscreen":
        path([(9, 3), (3, 3), (3, 9)]); path([(15, 3), (21, 3), (21, 9)])
        path([(3, 15), (3, 21), (9, 21)]); path([(21, 15), (21, 21), (15, 21)])
    elif name == "minimize":
        path([(3, 9), (3, 3), (9, 3)]); path([(15, 3), (21, 3), (21, 9)])
        path([(3, 15), (3, 21), (9, 21)]); path([(21, 15), (21, 21), (15, 21)])
        line(3, 3, 9, 9); line(21, 3, 15, 9)
        line(3, 21, 9, 15); line(21, 21, 15, 15)
    elif name == "plus":
        line(12, 4, 12, 20); line(4, 12, 20, 12)
    elif name == "paste":
        path([(8, 5), (5, 5), (5, 21), (19, 21), (19, 5), (16, 5)])
        painter.drawRoundedRect(QRectF(8, 3, 8, 5), 1.5, 1.5)
        line(8, 11, 16, 11); line(8, 14, 16, 14); line(8, 17, 13, 17)
    elif name == "pages":
        painter.drawRoundedRect(QRectF(3, 4, 13, 16), 1.5, 1.5)
        path([(7, 2.5), (19, 2.5), (21, 4.5), (21, 18)])
        line(6, 8, 13, 8); line(6, 11, 13, 11); line(6, 14, 11, 14)
    elif name == "contents":
        for y in (5, 11, 17):
            painter.drawEllipse(QRectF(3, y - 1, 2, 2)); line(8, y, 21, y)
    elif name == "palette":
        path([(12, 3), (5, 5), (3, 11), (5, 17), (10, 21), (15, 20), (14, 16), (16, 14), (20, 14), (21, 10), (18, 5), (12, 3)])
        for x, y in [(8, 8), (13, 6), (17, 9), (8, 13)]:
            painter.drawEllipse(QRectF(x - 1, y - 1, 2, 2))
    elif name == "ai":
        path([(12, 3), (13.8, 8.2), (19, 10), (13.8, 11.8), (12, 17), (10.2, 11.8), (5, 10), (10.2, 8.2), (12, 3)], close=True)
        path([(19, 15), (20, 18), (23, 19), (20, 20), (19, 23), (18, 20), (15, 19), (18, 18), (19, 15)], close=True)
    elif name == "chat":
        path([(4, 4), (20, 4), (20, 16), (12, 16), (7, 20), (7, 16), (4, 16), (4, 4)])
        for x in (8, 12, 16): painter.drawEllipse(QRectF(x - 0.8, 9, 1.6, 1.6))
    elif name == "mic":
        painter.drawRoundedRect(QRectF(8, 3, 8, 13), 4, 4)
        path([(5, 11), (5, 13), (7, 17), (12, 19), (17, 17), (19, 13), (19, 11)])
        line(12, 19, 12, 22); line(8, 22, 16, 22)
    elif name == "volume":
        # Compact speaker with two clean sound waves; matches the app's outline icons.
        path([(3, 9), (7, 9), (13, 4), (13, 20), (7, 15), (3, 15), (3, 9)])
        wave1 = QPainterPath(QPointF(16, 9))
        wave1.cubicTo(QPointF(18.7, 11), QPointF(18.7, 13), QPointF(16, 15))
        painter.drawPath(wave1)
        wave2 = QPainterPath(QPointF(18, 5.5))
        wave2.cubicTo(QPointF(23, 9), QPointF(23, 15), QPointF(18, 18.5))
        painter.drawPath(wave2)
    elif name == "pause":
        painter.drawRoundedRect(QRectF(5, 4, 5, 16), 1.2, 1.2)
        painter.drawRoundedRect(QRectF(14, 4, 5, 16), 1.2, 1.2)
    elif name == "play":
        path([(7, 4), (20, 12), (7, 20), (7, 4)], close=True, fill=True)
    elif name == "stop":
        painter.drawRoundedRect(QRectF(5, 5, 14, 14), 2, 2)
    elif name == "send":
        path([(3, 3), (22, 11), (3, 21), (7, 12), (3, 3)], close=True)
        line(7, 12, 22, 11)
    elif name == "settings":
        painter.drawEllipse(QRectF(7, 7, 10, 10)); painter.drawEllipse(QRectF(10, 10, 4, 4))
        for angle in range(0, 360, 45):
            painter.save(); painter.translate(12,12); painter.rotate(angle); line(0,-7,0,-10); painter.restore()
    elif name == "export":
        path([(5, 3), (15, 3), (20, 8), (20, 21), (5, 21), (5, 3)])
        line(14, 3, 14, 9); line(14, 9, 20, 9); line(12, 18, 12, 11); path([(9,14),(12,11),(15,14)])
    elif name == "copy":
        painter.drawRoundedRect(QRectF(8, 7, 12, 14), 2, 2)
        path([(5, 16), (3, 16), (3, 3), (15, 3), (15, 5)])
        line(11, 11, 17, 11); line(11, 15, 17, 15); line(11, 18, 15, 18)
    elif name == "summarize":
        for y in (6, 11, 16):
            painter.drawEllipse(QRectF(3, y-1, 2, 2)); line(8,y,19,y)
        path([(18, 2), (19, 5), (22, 6), (19, 7), (18, 10), (17, 7), (14, 6), (17, 5), (18, 2)])
    elif name == "review":
        path([(2, 12), (6, 7), (12, 5), (18, 7), (22, 12), (18, 17), (12, 19), (6, 17), (2, 12)])
        painter.drawEllipse(QRectF(9, 9, 6, 6))
    elif name == "explain":
        painter.drawEllipse(QRectF(6, 3, 12, 12)); path([(9, 15), (9, 18), (15, 18), (15, 15)]); line(10,21,14,21)
        line(12,6,12,10); painter.drawEllipse(QRectF(11.3,11.5,1.4,1.4))
    elif name == "translate":
        line(3,5,15,5); line(9,3,9,5); path([(5,8),(9,13),(13,8)]); line(5,8,13,8)
        path([(13,13),(21,21),(16,21),(13,13)]); line(16,16,20,16)
    elif name == "ocr":
        path([(8,3),(3,3),(3,8)]); path([(16,3),(21,3),(21,8)]); path([(3,16),(3,21),(8,21)]); path([(21,16),(21,21),(16,21)])
        line(7,9,17,9); line(7,12,17,12); line(7,15,14,15)
    elif name == "clear":
        line(5,5,19,19); line(19,5,5,19)
    else:
        painter.drawRoundedRect(QRectF(4, 4, 16, 16), 3, 3)
        line(8, 12, 16, 12)
    painter.end()
    return QIcon(pm)


class MotionButton(QPushButton):
    """Lightweight button using Qt's native hover styling (no paint effects)."""
    def __init__(self, text="", parent=None):
        super().__init__(text, parent)


def _configure_color_dialog(dialog, is_ar=False):
    """Force a Qt-owned color dialog so Engo themes and Arabic layout apply on Windows."""
    try:
        dialog.setOption(QColorDialog.ColorDialogOption.DontUseNativeDialog, True)
        dialog.setLayoutDirection(
            Qt.LayoutDirection.RightToLeft if is_ar else Qt.LayoutDirection.LeftToRight
        )
        dialog.setAttribute(Qt.WidgetAttribute.WA_StyledBackground, True)
        if not is_ar:
            return
        translations = {
            "Basic colors:": "الألوان الأساسية:",
            "Custom colors:": "الألوان المخصصة:",
            "Hue:": "درجة اللون:",
            "Sat:": "التشبع:",
            "Saturation:": "التشبع:",
            "Val:": "القيمة:",
            "Value:": "القيمة:",
            "Red:": "أحمر:",
            "Green:": "أخضر:",
            "Blue:": "أزرق:",
            "Alpha channel:": "قناة ألفا:",
            "HTML:": "HTML:",
            "OK": "موافق",
            "Cancel": "إلغاء",
            "Add to Custom Colors": "إضافة إلى الألوان المخصصة",
            "Pick Screen Color": "اختيار لون من الشاشة",
            "Show Details...": "إظهار التفاصيل...",
            "Hide Details...": "إخفاء التفاصيل...",
        }
        for widget in dialog.findChildren(QLabel):
            source = widget.text().strip()
            if source in translations:
                widget.setText(translations[source])
        for widget_class in (QPushButton, QToolButton):
            for widget in dialog.findChildren(widget_class):
                source = widget.text().strip()
                if source in translations:
                    widget.setText(translations[source])
                tip = widget.toolTip().strip()
                if tip in translations:
                    widget.setToolTip(translations[tip])
    except (AttributeError, RuntimeError):
        # Never let a cosmetic dialog adjustment block a user's color selection.
        pass


def _engo_file_dialog(parent, title_en, title_ar, start_path, name_filter, *, save=False, multiple=False, native=False):
    """Themed, translatable Qt file picker used instead of Windows native dialogs."""
    if native and not save:
        # Real Windows (native) open dialog, titled in the current interface language.
        try:
            _host = parent.window() if parent is not None else None
            _settings = getattr(_host, "settings", None)
            _lang = str(_settings.value("interface_language", "en", type=str) if _settings is not None else "en").lower()
        except Exception:
            _lang = "en"
        _title = title_ar if _lang.startswith("ar") else title_en
        _raw = str(start_path or Path.home())
        _filters = str(name_filter or "All files (*.*)")
        if multiple:
            _files, _ = QFileDialog.getOpenFileNames(parent, _title, _raw, _filters)
            return [str(x) for x in _files]
        _file, _ = QFileDialog.getOpenFileName(parent, _title, _raw, _filters)
        return str(_file or "")
    dialog = QFileDialog(parent)
    dialog.setOption(QFileDialog.Option.DontUseNativeDialog, True)
    dialog.setViewMode(QFileDialog.ViewMode.Detail)
    filters = [part.strip() for part in str(name_filter or "All files (*.*)").split(";;") if part.strip()]
    dialog.setNameFilters(filters or ["All files (*.*)"])

    try:
        host = parent.window() if parent is not None else None
        settings = getattr(host, "settings", None)
        language = str(settings.value("interface_language", "en", type=str) if settings is not None else "en").lower()
        theme = normalize_ui_theme(settings.value("ui_theme", "dark", type=str) if settings is not None else "dark")
    except Exception:
        language, theme = "en", "dark"
    is_ar = language.startswith("ar")
    direction = Qt.LayoutDirection.RightToLeft if is_ar else Qt.LayoutDirection.LeftToRight
    dialog.setLayoutDirection(direction)
    dialog.setWindowTitle(title_ar if is_ar else title_en)

    raw_path = str(start_path or Path.home())
    candidate = Path(raw_path).expanduser()
    if save:
        if candidate.is_absolute() and candidate.suffix:
            dialog.setDirectory(str(candidate.parent))
            dialog.selectFile(candidate.name)
        elif candidate.suffix:
            dialog.setDirectory(str(Path.cwd()))
            dialog.selectFile(raw_path)
        else:
            dialog.setDirectory(raw_path)
        dialog.setAcceptMode(QFileDialog.AcceptMode.AcceptSave)
        dialog.setFileMode(QFileDialog.FileMode.AnyFile)
        dialog.setConfirmOverwrite(True)
    else:
        dialog.setDirectory(raw_path if candidate.is_dir() else str(candidate.parent if candidate.suffix else candidate))
        dialog.setAcceptMode(QFileDialog.AcceptMode.AcceptOpen)
        dialog.setFileMode(QFileDialog.FileMode.ExistingFiles if multiple else QFileDialog.FileMode.ExistingFile)

    if theme == "light":
        c = {"bg":"#f4f6fa", "panel":"#ffffff", "field":"#ffffff", "text":"#263449", "muted":"#68788f", "border":"#c8d2df", "selected":"#dce9ff", "selected_text":"#173f83", "accent":"#3269d8"}
    elif theme == "midnight":
        c = {"bg":"#0b1628", "panel":"#14233b", "field":"#0e1a2d", "text":"#e6efff", "muted":"#9fb2d1", "border":"#304969", "selected":"#29466f", "selected_text":"#ffffff", "accent":"#79a8ff"}
    else:
        c = {"bg":"#151515", "panel":"#202020", "field":"#181818", "text":"#eeeeee", "muted":"#aaaaaa", "border":"#414141", "selected":"#344a6c", "selected_text":"#ffffff", "accent":"#6f97d8"}
    palette = QPalette(dialog.palette())
    for role, key in ((QPalette.ColorRole.Window,"bg"), (QPalette.ColorRole.WindowText,"text"),
                      (QPalette.ColorRole.Base,"field"), (QPalette.ColorRole.AlternateBase,"panel"),
                      (QPalette.ColorRole.Text,"text"), (QPalette.ColorRole.Button,"panel"),
                      (QPalette.ColorRole.ButtonText,"text"), (QPalette.ColorRole.Highlight,"selected"),
                      (QPalette.ColorRole.HighlightedText,"selected_text"),
                      (QPalette.ColorRole.ToolTipBase,"panel"), (QPalette.ColorRole.ToolTipText,"text")):
        palette.setColor(role, QColor(c[key]))
    dialog.setPalette(palette)
    dialog.setStyleSheet(f"""
        QFileDialog {{ background:{c['bg']}; color:{c['text']}; }}
        QFileDialog QLabel {{ color:{c['text']}; }}
        QFileDialog QTreeView, QFileDialog QListView, QFileDialog QTableView {{ background:{c['field']}; color:{c['text']}; border:1px solid {c['border']}; selection-background-color:{c['selected']}; selection-color:{c['selected_text']}; outline:0; }}
        QFileDialog QTreeView::item, QFileDialog QListView::item, QFileDialog QTableView::item {{ padding:4px; }}
        QFileDialog QHeaderView::section {{ background:{c['panel']}; color:{c['text']}; border:0; border-bottom:1px solid {c['border']}; padding:6px; }}
        QFileDialog QLineEdit, QFileDialog QComboBox {{ background:{c['field']}; color:{c['text']}; border:1px solid {c['border']}; border-radius:5px; padding:5px 7px; selection-background-color:{c['selected']}; selection-color:{c['selected_text']}; }}
        QFileDialog QPushButton, QFileDialog QToolButton {{ background:{c['panel']}; color:{c['text']}; border:1px solid {c['border']}; border-radius:6px; padding:5px 9px; }}
        QFileDialog QPushButton:hover, QFileDialog QToolButton:hover {{ background:{c['selected']}; border-color:{c['accent']}; }}
        QFileDialog QScrollBar:vertical {{ background:transparent; width:9px; margin:2px; }}
        QFileDialog QScrollBar::handle:vertical {{ background:{c['border']}; border-radius:4px; min-height:24px; }}
        QToolTip {{ background:{c['panel']}; color:{c['text']}; border:1px solid {c['border']}; padding:5px; }}
    """)
    if is_ar:
        translations = {
            "Look in:": "بحث في:", "File name:": "اسم الملف:", "File type:": "نوع الملف:",
            "Name": "الاسم", "Size": "الحجم", "Type": "النوع", "Date Modified": "تاريخ التعديل",
            "Open": "فتح", "Save": "حفظ", "Cancel": "إلغاء", "New Folder": "مجلد جديد",
            "Create New Folder": "إنشاء مجلد جديد", "Show hidden files": "إظهار الملفات المخفية",
        }
        for label in dialog.findChildren(QLabel):
            original = label.text().strip()
            if original in translations:
                label.setText(translations[original])
        for button in dialog.findChildren(QPushButton):
            original = button.text().replace("&", "").strip()
            if original in translations:
                button.setText(translations[original])
        for edit in dialog.findChildren(QLineEdit):
            edit.setLayoutDirection(Qt.LayoutDirection.LeftToRight)
            edit.setAlignment(Qt.AlignmentFlag.AlignLeft | Qt.AlignmentFlag.AlignVCenter)
            if edit.objectName() == "fileNameEdit":
                edit.setPlaceholderText("اسم الملف")
    accepted = dialog.exec() == QDialog.DialogCode.Accepted
    selected = [str(x) for x in dialog.selectedFiles()] if accepted else []
    if multiple:
        return selected
    return selected[0] if selected else ""


class PageThemePreview(QFrame):
    """Paint an isolated page-theme swatch, independent of the application QSS."""
    def __init__(self, bg, ink, is_ar=False, parent=None):
        super().__init__(parent)
        self.bg_color = QColor(str(bg))
        self.ink_color = QColor(str(ink))
        self.is_ar = bool(is_ar)
        self.setObjectName("pageThemeCardPreview")
        self.setAttribute(Qt.WidgetAttribute.WA_TransparentForMouseEvents, True)
        # Do not rely on inherited QSS/palette brushes for the preview surface.
        # paintEvent fills the complete preview with the target page palette.
        self.setAttribute(Qt.WidgetAttribute.WA_StyledBackground, False)
        self.setMinimumHeight(48)
        self.setSizePolicy(QSizePolicy.Policy.Expanding, QSizePolicy.Policy.Expanding)
        self.setLayoutDirection(
            Qt.LayoutDirection.RightToLeft if self.is_ar else Qt.LayoutDirection.LeftToRight
        )

    def paintEvent(self, event):
        painter = QPainter(self)
        painter.setRenderHint(QPainter.RenderHint.Antialiasing, True)
        rect = QRectF(self.rect()).adjusted(0.5, 0.5, -0.5, -0.5)
        if rect.width() <= 1 or rect.height() <= 1:
            painter.end()
            return

        # Fill first, so a parent/application stylesheet can never leak its
        # current UI-theme background into the page-theme sample area.
        painter.setPen(QPen(self.ink_color, 1.0))
        painter.setBrush(self.bg_color)
        painter.drawRoundedRect(rect, 6.0, 6.0)

        label = "Aa  نص الصفحة" if self.is_ar else "Aa  Page text"
        text_rect = rect.adjusted(9, 3, -9, -12)
        painter.setPen(self.ink_color)
        sample_font = QFont(self.font())
        sample_font.setPointSize(10)
        sample_font.setWeight(QFont.Weight.DemiBold)
        painter.setFont(sample_font)
        alignment = Qt.AlignmentFlag.AlignVCenter
        alignment |= Qt.AlignmentFlag.AlignRight if self.is_ar else Qt.AlignmentFlag.AlignLeft
        painter.drawText(text_rect, alignment, label)

        line_y = rect.bottom() - 7
        line_left = rect.left() + 9
        line_right = rect.right() - 9
        if line_right > line_left:
            painter.setPen(QPen(self.ink_color, 1.5, Qt.PenStyle.SolidLine, Qt.PenCapStyle.RoundCap))
            painter.drawLine(int(line_left), int(line_y), int(line_right), int(line_y))
        painter.end()


class PageThemeCard(QFrame):
    """Clickable preview card for one built-in or user-saved page theme."""
    clicked = pyqtSignal()

    def __init__(self, name, display_name, bg, ink, selected=False, is_custom=False, is_ar=False, parent=None):
        super().__init__(parent)
        self.theme_name = str(name)
        self.bg = QColor(str(bg)).name()
        self.ink = QColor(str(ink)).name()
        self.is_ar = bool(is_ar)
        self.setObjectName("pageThemeCard")
        self.setCursor(Qt.CursorShape.PointingHandCursor)
        self.setAttribute(Qt.WidgetAttribute.WA_StyledBackground, True)
        self.setProperty("selectedCard", bool(selected))
        self.setMinimumSize(150, 112)
        self.setMaximumHeight(122)
        root = QVBoxLayout(self)
        root.setContentsMargins(9, 8, 9, 8)
        root.setSpacing(6)
        title_row = QHBoxLayout()
        title = QLabel(str(display_name))
        title.setObjectName("pageThemeCardTitle")
        title.setAttribute(Qt.WidgetAttribute.WA_TransparentForMouseEvents, True)
        title_row.addWidget(title, 1)
        if is_custom:
            mark = QLabel("✦")
            mark.setObjectName("pageThemeCardCustom")
            mark.setAttribute(Qt.WidgetAttribute.WA_TransparentForMouseEvents, True)
            title_row.addWidget(mark)
        root.addLayout(title_row)

        # This swatch deliberately paints its own page palette. The card frame
        # continues to use the current app theme, but the sample surface and its
        # sample text always use the page theme represented by this card.
        preview = PageThemePreview(self.bg, self.ink, self.is_ar, self)
        root.addWidget(preview, 1)

        meta = QLabel(f"{self.bg.upper()}   ·   {self.ink.upper()}")
        meta.setObjectName("pageThemeCardMeta")
        meta.setAttribute(Qt.WidgetAttribute.WA_TransparentForMouseEvents, True)
        root.addWidget(meta)
        self._apply_card_style()

    def _apply_card_style(self):
        selected = bool(self.property("selectedCard"))
        try:
            settings = _engo_dialog_host_settings(self)
            theme = settings.value("ui_theme", "dark", type=str) if settings is not None else "dark"
        except Exception:
            theme = "dark"
        t = engo_ui_theme_tokens(theme)
        title_color = t["accent"] if selected else t["text"]
        border_color = t["accent"] if selected else t["border"]
        card_bg = t.get("selection", t.get("panel_alt", t["window"])) if selected else "transparent"
        border_width = 2 if selected else 1
        self.setStyleSheet(
            f"QFrame#pageThemeCard {{ background: {card_bg}; color: {t['text']}; "
            f"border: {border_width}px solid {border_color}; border-radius: 10px; }} "
            f"QLabel#pageThemeCardTitle {{ color: {title_color}; background: transparent; font-weight: 700; border: none; padding: 0; }} "
            f"QLabel#pageThemeCardMeta {{ color: {t['muted']}; background: transparent; font-size: 9px; border: none; padding: 0; }} "
            f"QLabel#pageThemeCardCustom {{ color: {t['accent']}; background: transparent; border: none; padding: 0; }}"
        )

    def set_selected(self, selected):
        self.setProperty("selectedCard", bool(selected))
        self._apply_card_style()

    def mousePressEvent(self, event):
        if event.button() == Qt.MouseButton.LeftButton:
            self.clicked.emit()
            event.accept()
            return
        super().mousePressEvent(event)


class ColorSwatchButton(QPushButton):
    """A compact circular color-only control used by all Engo color editors."""
    def __init__(self, color="#808080", parent=None, diameter=30):
        super().__init__(parent)
        self._diameter = max(24, int(diameter))
        self.setFixedSize(self._diameter, self._diameter)
        self.setCursor(Qt.CursorShape.PointingHandCursor)
        self.setFocusPolicy(Qt.FocusPolicy.StrongFocus)
        self.setText("")
        self.setColor(color)

    def color(self):
        return str(self.property("engoSwatchColor") or "#808080")

    def setColor(self, color):
        value = QColor(str(color))
        if not value.isValid():
            value = QColor("#808080")
        value = value.name()
        self.setProperty("engoSwatchColor", value)
        self.setAccessibleName(f"Selected color {value}")
        self.setToolTip(value.upper())
        diameter = self._diameter
        radius = diameter // 2
        self.setStyleSheet(
            f"QPushButton {{ background-color:{value}; border:1px solid palette(mid); "
            f"border-radius:{radius}px; padding:0; min-width:{diameter}px; max-width:{diameter}px; "
            f"min-height:{diameter}px; max-height:{diameter}px; }} "
            f"QPushButton:hover, QPushButton:focus {{ border:2px solid palette(highlight); }}"
        )
        self.update()


def _set_compact_dialog_button_heights(button_box, height=26):
    """Keep dialog action buttons slightly shorter without changing their widths."""
    height = max(22, int(height))
    for button in button_box.buttons():
        button.setFixedHeight(height)
        # A local rule takes precedence over the shared 30px popup-button QSS.
        button.setStyleSheet(
            f"QPushButton {{ min-height:{height}px; max-height:{height}px; "
            f"padding-top:1px; padding-bottom:1px; }}"
        )


class PageThemeEditorDialog(QDialog):
    """Create or edit a named page palette without exposing raw color fields."""
    def __init__(self, parent, name="", bg="#1e1e1e", ink="#e0e0e0", is_ar=False, allow_delete=False):
        super().__init__(parent)
        self._is_ar = bool(is_ar)
        self.delete_requested = False
        self.bg = QColor(str(bg)).name()
        self.ink = QColor(str(ink)).name()
        self.setWindowTitle(("إضافة مظهر صفحة" if not name else "تعديل مظهر الصفحة") if self._is_ar else ("Add page theme" if not name else "Edit page theme"))
        self.setMinimumWidth(410)
        self.setModal(True)
        root = QVBoxLayout(self)
        root.setContentsMargins(18, 16, 18, 14)
        root.setSpacing(10)
        root.addWidget(QLabel("اسم المظهر" if self._is_ar else "Theme name"))
        self.name_edit = QLineEdit(str(name))
        self.name_edit.setPlaceholderText("مثال: أخضر هادئ" if self._is_ar else "Example: Soft green")
        root.addWidget(self.name_edit)
        root.addWidget(QLabel("ألوان معاينة الصفحة" if self._is_ar else "Page preview colors"))
        self.bg_button = ColorSwatchButton(self.bg, self)
        self.ink_button = ColorSwatchButton(self.ink, self)
        self.bg_button.clicked.connect(lambda: self._pick_color("bg"))
        self.ink_button.clicked.connect(lambda: self._pick_color("ink"))
        root.addWidget(self._color_row("خلفية الصفحة" if self._is_ar else "Page background", self.bg_button))
        root.addWidget(self._color_row("لون النص" if self._is_ar else "Text / ink", self.ink_button))
        self.preview = QFrame()
        self.preview.setMinimumHeight(66)
        preview_layout = QVBoxLayout(self.preview)
        preview_layout.setContentsMargins(10, 7, 10, 7)
        self.preview_label = QLabel("Aa  Engo PDF · 123" )
        self.preview_label.setStyleSheet("font-size: 16px; font-weight: 700; background: transparent; border: none;")
        preview_layout.addWidget(self.preview_label)
        root.addWidget(self.preview)
        row = QHBoxLayout()
        if allow_delete:
            delete_text = "حذف المظهر" if self._is_ar else "Delete theme"
            delete_btn = QPushButton(delete_text)
            delete_btn.setObjectName("danger")
            delete_btn.clicked.connect(self._request_delete)
            row.addWidget(delete_btn)
        row.addStretch(1)
        cancel = QPushButton("إلغاء" if self._is_ar else "Cancel")
        save = QPushButton("حفظ" if self._is_ar else "Save")
        save.setObjectName("primary")
        cancel.clicked.connect(self.reject)
        save.clicked.connect(self._accept_if_valid)
        row.addWidget(cancel)
        row.addWidget(save)
        root.addLayout(row)
        self._refresh_color_buttons()

    def _color_row(self, label_text, button):
        row = QHBoxLayout()
        label = QLabel(label_text)
        row.addWidget(label, 1)
        row.addWidget(button)
        wrapper = QWidget()
        wrapper.setLayout(row)
        return wrapper

    def _refresh_color_buttons(self):
        self.bg_button.setColor(self.bg)
        self.ink_button.setColor(self.ink)
        self.bg_button.setToolTip(("لون الخلفية: " if self._is_ar else "Background color: ") + self.bg.upper())
        self.ink_button.setToolTip(("لون النص: " if self._is_ar else "Text color: ") + self.ink.upper())
        self.preview.setStyleSheet(f"QFrame {{ background: {self.bg}; border: 1px solid {self.ink}; border-radius: 7px; }}")
        self.preview_label.setStyleSheet(f"color: {self.ink}; font-size: 16px; font-weight: 700; background: transparent; border: none;")

    def _pick_color(self, which):
        current = self.bg if which == "bg" else self.ink
        picker = QColorDialog(QColor(current), self)
        _configure_color_dialog(picker, self._is_ar)
        picker.setWindowTitle(("خلفية الصفحة" if which == "bg" else "لون النص") if self._is_ar else ("Page background" if which == "bg" else "Text / ink color"))
        if picker.exec() == QDialog.DialogCode.Accepted and picker.currentColor().isValid():
            if which == "bg":
                self.bg = picker.currentColor().name()
            else:
                self.ink = picker.currentColor().name()
            self._refresh_color_buttons()

    def _accept_if_valid(self):
        if not self.name_edit.text().strip():
            QMessageBox.warning(self, "مظهر الصفحة" if self._is_ar else "Page theme", "اكتب اسمًا للمظهر أولًا." if self._is_ar else "Enter a theme name first.")
            self.name_edit.setFocus()
            return
        self.accept()

    def _request_delete(self):
        self.delete_requested = True
        self.accept()


class PageThemeDialog(QDialog):
    """Palette-card manager for built-in and user-defined document themes."""
    BUILTIN_THEMES = {
        "Dark": {"bg": "#101010", "ink": "#eeeeee"},
        "Obsidian": {"bg": "#1e1e1e", "ink": "#e0e0e0"},
        "Midnight": {"bg": "#101827", "ink": "#dce8ff"},
        "Sepia": {"bg": "#302820", "ink": "#f0dfbd"},
        "Slate": {"bg": "#232a31", "ink": "#dce4ec"},
        # Both new presets intentionally use a deeper page background so white
        # scans and handwriting recolor into a calm, dark green / rose surface.
        "Grass": {"bg": "#102117", "ink": "#d9f0dc"},
        "Pink": {"bg": "#23131d", "ink": "#f8dce8"},
        "Orange": {"bg": "#2b1b10", "ink": "#ffe1c5"},
    }

    def __init__(self, parent, enabled: bool, bg: str, ink: str, custom_themes=None, smart_enabled: bool = False):
        super().__init__(parent)
        try:
            parent_settings = getattr(parent, "settings", None)
            language_value = parent_settings.value("interface_language", "en", type=str) if parent_settings is not None else "en"
        except Exception:
            language_value = "en"
        self._is_ar = str(language_value or "en").lower().startswith("ar")
        self._theme_name_map = {
            "Dark": "داكن", "Obsidian": "سبج", "Midnight": "منتصف الليل",
            "Sepia": "بني دافئ", "Slate": "رمادي مزرق", "Grass": "عشبي", "Pink": "وردي", "Orange": "برتقالي",
        }
        self.setObjectName("pageThemeDialog")
        self.setWindowTitle("مظهر الصفحة" if self._is_ar else "Page Themes")
        self.setLayoutDirection(Qt.LayoutDirection.RightToLeft if self._is_ar else Qt.LayoutDirection.LeftToRight)
        self.setAttribute(Qt.WidgetAttribute.WA_StyledBackground, True)
        self.setModal(True)
        self.setMinimumSize(600, 520)
        self.resize(680, 610)
        self.enabled = bool(enabled)
        # Smart Theme is a refinement of page recoloring, never a standalone mode.
        self.smart_enabled = bool(smart_enabled and self.enabled)
        self.bg = QColor(str(bg)).name()
        self.ink = QColor(str(ink)).name()
        self.custom_themes = {
            str(name): {"bg": QColor(str(values.get("bg", self.bg))).name(),
                        "ink": QColor(str(values.get("ink", self.ink))).name()}
            for name, values in dict(custom_themes or {}).items() if isinstance(values, dict)
        }
        self._selected_key = self._find_theme_key(self.bg, self.ink)
        root = QVBoxLayout(self)
        root.setContentsMargins(18, 16, 18, 14)
        root.setSpacing(10)
        heading = QLabel("مظاهر الصفحات" if self._is_ar else "PAGE THEMES")
        heading.setObjectName("dialogHeading")
        root.addWidget(heading)
        self.toggle = QCheckBox("تفعيل ألوان مظهر الصفحة" if self._is_ar else "Enable page recoloring")
        self.toggle.setChecked(self.enabled)
        self.smart_toggle = QCheckBox("ثيم ذكي" if self._is_ar else "Smart Theme")
        self.smart_toggle.setToolTip(
            "يحوّل الأبيض إلى لون خلفية المظهر، والأسود والأزرق إلى لون النص، مع الحفاظ على باقي الألوان كما هي."
            if self._is_ar else
            "Maps white to the theme background and black/blue ink to the theme text color, while preserving other colors."
        )
        self.smart_toggle.setChecked(self.smart_enabled)
        self.smart_toggle.setEnabled(self.enabled)
        self.smart_toggle.toggled.connect(self._toggle_smart)
        # Keep the dependent option beside its prerequisite. A subdued disabled
        # state makes the dependency clear before page recoloring is enabled.
        try:
            active_theme = parent_settings.value("ui_theme", "dark", type=str) if parent_settings is not None else "dark"
            dialog_tokens = engo_ui_theme_tokens(active_theme)
            self.smart_toggle.setStyleSheet(
                "QCheckBox:disabled { color: " + dialog_tokens["muted"] + "; }"
                "QCheckBox::indicator:disabled { background: " + dialog_tokens["panel_alt"] + "; "
                "border: 1px solid " + dialog_tokens["border"] + "; }"
            )
        except Exception:
            pass
        theme_switch_row = QHBoxLayout()
        theme_switch_row.setContentsMargins(0, 0, 0, 0)
        # Keep both related checkboxes together as one compact control group.
        # The previous stretch factor on the first checkbox pushed Smart Theme
        # to the opposite edge of the dialog, leaving an unnecessarily large gap.
        theme_switch_row.setSpacing(10)
        theme_switch_row.addWidget(self.toggle, 0)
        theme_switch_row.addWidget(self.smart_toggle, 0)
        theme_switch_row.addStretch(1)
        root.addLayout(theme_switch_row)
        hint = QLabel("اختر بطاقة لمعاينة ألوان خلفية الصفحة والنص. يمكنك إضافة مظاهر خاصة بك أو تعديلها لاحقًا." if self._is_ar else "Select a card to preview its page background and text colors. Add your own themes and edit them later.")
        hint.setObjectName("dialogHint")
        hint.setWordWrap(True)
        root.addWidget(hint)

        self.cards_scroll = QScrollArea()
        self.cards_scroll.setObjectName("pageThemeCardsScroll")
        self.cards_scroll.setWidgetResizable(True)
        self.cards_scroll.setFrameShape(QFrame.Shape.NoFrame)
        self.cards_scroll.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        self.cards_widget = QWidget()
        self.cards_grid = QGridLayout(self.cards_widget)
        self.cards_grid.setContentsMargins(2, 2, 8, 2)
        self.cards_grid.setHorizontalSpacing(9)
        self.cards_grid.setVerticalSpacing(9)
        self.cards_scroll.setWidget(self.cards_widget)
        root.addWidget(self.cards_scroll, 1)

        manage = QHBoxLayout()
        self.add_theme_btn = QPushButton("إضافة مظهر جديد" if self._is_ar else "Add new theme")
        self.add_theme_btn.setObjectName("primary")
        self.add_theme_btn.clicked.connect(self.add_named_theme)
        self.edit_theme_btn = QPushButton("تعديل المظهر المحدد" if self._is_ar else "Edit selected theme")
        self.edit_theme_btn.clicked.connect(self.edit_named_theme)
        manage.addWidget(self.add_theme_btn, 1)
        manage.addWidget(self.edit_theme_btn, 1)
        root.addLayout(manage)

        buttons = QDialogButtonBox(QDialogButtonBox.StandardButton.Cancel | QDialogButtonBox.StandardButton.Apply)
        # Compact action buttons keep more room for the theme cards while
        # retaining readable labels on Windows.
        buttons.button(QDialogButtonBox.StandardButton.Apply).setText("تطبيق" if self._is_ar else "Apply")
        buttons.button(QDialogButtonBox.StandardButton.Cancel).setText("إلغاء" if self._is_ar else "Cancel")
        _set_compact_dialog_button_heights(buttons, 26)
        buttons.button(QDialogButtonBox.StandardButton.Apply).clicked.connect(self.accept)
        buttons.rejected.connect(self.reject)
        root.addWidget(buttons)
        self.toggle.toggled.connect(self._toggle_colors)
        self._refresh_cards()

    def _find_theme_key(self, bg, ink):
        for name, values in self.BUILTIN_THEMES.items():
            if str(values.get("bg", "")).lower() == str(bg).lower() and str(values.get("ink", "")).lower() == str(ink).lower():
                return "builtin:" + name
        for name, values in self.custom_themes.items():
            if str(values.get("bg", "")).lower() == str(bg).lower() and str(values.get("ink", "")).lower() == str(ink).lower():
                return "custom:" + name
        return "current"

    def _entries(self):
        items = [("builtin:" + name, self._theme_name_map.get(name, name) if self._is_ar else name,
                  values["bg"], values["ink"], False) for name, values in self.BUILTIN_THEMES.items()]
        items.extend(("custom:" + name, name, values.get("bg", self.bg), values.get("ink", self.ink), True)
                     for name, values in sorted(self.custom_themes.items(), key=lambda item: item[0].casefold()))
        if self._selected_key == "current" or not any(key == self._selected_key for key, *_ in items):
            if self._find_theme_key(self.bg, self.ink) == "current":
                items.insert(0, ("current", "الإعدادات الحالية" if self._is_ar else "Current colors", self.bg, self.ink, False))
        return items

    def _refresh_cards(self):
        while self.cards_grid.count():
            item = self.cards_grid.takeAt(0)
            widget = item.widget()
            if widget is not None:
                widget.deleteLater()
        self._cards = {}
        entries = self._entries()
        for position, (key, display_name, bg, ink, is_custom) in enumerate(entries):
            card = PageThemeCard(key, display_name, bg, ink, selected=(key == self._selected_key), is_custom=is_custom, is_ar=self._is_ar, parent=self.cards_widget)
            card.clicked.connect(lambda k=key, b=bg, i=ink: self._select_card(k, b, i))
            self.cards_grid.addWidget(card, position // 3, position % 3)
            self._cards[key] = card
        for column in range(3):
            self.cards_grid.setColumnStretch(column, 1)
        self.edit_theme_btn.setEnabled(self._selected_key.startswith("custom:"))

    def _select_card(self, key, bg, ink):
        self._selected_key = key
        self.bg, self.ink = str(bg), str(ink)
        # Selecting a palette only marks it as the pending choice. The user
        # explicitly controls whether page recoloring is enabled.
        self._refresh_cards()

    def _toggle_colors(self, enabled):
        self.enabled = bool(enabled)
        self.smart_toggle.setEnabled(self.enabled)
        if not self.enabled and self.smart_toggle.isChecked():
            previous = self.smart_toggle.blockSignals(True)
            self.smart_toggle.setChecked(False)
            self.smart_toggle.blockSignals(previous)
        self.smart_enabled = bool(self.enabled and self.smart_toggle.isChecked())

    def _toggle_smart(self, checked):
        checked = bool(checked)
        if checked and not self.toggle.isChecked():
            previous = self.smart_toggle.blockSignals(True)
            self.smart_toggle.setChecked(False)
            self.smart_toggle.blockSignals(previous)
            checked = False
        self.smart_enabled = bool(checked and self.toggle.isChecked())

    def add_named_theme(self):
        editor = PageThemeEditorDialog(self, "", self.bg, self.ink, self._is_ar, allow_delete=False)
        if editor.exec() != QDialog.DialogCode.Accepted:
            return
        name = editor.name_edit.text().strip()
        if name in self.BUILTIN_THEMES:
            QMessageBox.information(self, "مظهر الصفحة" if self._is_ar else "Page theme", "هذا الاسم مخصص لمظهر مدمج. اختر اسمًا آخر." if self._is_ar else "That name belongs to a built-in theme. Choose another name.")
            return
        if name in self.custom_themes:
            box = QMessageBox(QMessageBox.Icon.Question, "استبدال المظهر؟" if self._is_ar else "Replace theme?", f"{('هل تريد استبدال المظهر المحفوظ' if self._is_ar else 'Replace the saved theme')} ‘{name}’؟", QMessageBox.StandardButton.Yes | QMessageBox.StandardButton.No, self)
            if self._is_ar:
                box.button(QMessageBox.StandardButton.Yes).setText("نعم")
                box.button(QMessageBox.StandardButton.No).setText("لا")
            if box.exec() != QMessageBox.StandardButton.Yes:
                return
        self.custom_themes[name] = {"bg": editor.bg, "ink": editor.ink}
        self._selected_key = "custom:" + name
        self.bg, self.ink = editor.bg, editor.ink
        self._refresh_cards()

    def edit_named_theme(self):
        if not self._selected_key.startswith("custom:"):
            return
        old_name = self._selected_key.partition(":")[2]
        values = self.custom_themes.get(old_name)
        if not isinstance(values, dict):
            return
        editor = PageThemeEditorDialog(self, old_name, values.get("bg", self.bg), values.get("ink", self.ink), self._is_ar, allow_delete=True)
        if editor.exec() != QDialog.DialogCode.Accepted:
            return
        if editor.delete_requested:
            box = QMessageBox(QMessageBox.Icon.Question, "حذف المظهر؟" if self._is_ar else "Delete theme?", f"{('هل تريد حذف المظهر' if self._is_ar else 'Delete the theme')} ‘{old_name}’؟", QMessageBox.StandardButton.Yes | QMessageBox.StandardButton.No, self)
            if self._is_ar:
                box.button(QMessageBox.StandardButton.Yes).setText("نعم")
                box.button(QMessageBox.StandardButton.No).setText("لا")
            if box.exec() == QMessageBox.StandardButton.Yes:
                del self.custom_themes[old_name]
                self._selected_key = "builtin:Obsidian"
                fallback = self.BUILTIN_THEMES["Obsidian"]
                self.bg, self.ink = fallback["bg"], fallback["ink"]
                self._refresh_cards()
            return
        new_name = editor.name_edit.text().strip()
        if new_name in self.BUILTIN_THEMES or (new_name != old_name and new_name in self.custom_themes):
            QMessageBox.information(self, "مظهر الصفحة" if self._is_ar else "Page theme", "هذا الاسم مستخدم بالفعل. اختر اسمًا آخر." if self._is_ar else "That name is already in use. Choose another name.")
            return
        if new_name != old_name:
            del self.custom_themes[old_name]
        self.custom_themes[new_name] = {"bg": editor.bg, "ink": editor.ink}
        self._selected_key = "custom:" + new_name
        self.bg, self.ink = editor.bg, editor.ink
        self._refresh_cards()


class AnnotationColorsDialog(QDialog):
    """Color controls for all tools that create PDF annotations."""
    OPTIONS = [
        ("pen", "Pen / drawing color"),
        ("highlight", "Highlight color"),
        ("note", "Sticky note marker color"),
        ("text_ink", "Text box font color"),
        ("text_fill", "Text box background color"),
    ]

    def __init__(self, parent, colors):
        super().__init__(parent)
        try:
            parent_settings = getattr(parent, "settings", None)
            language_value = parent_settings.value("interface_language", "en", type=str) if parent_settings is not None else "en"
        except Exception:
            language_value = "en"
        self._is_ar = str(language_value or "en").lower().startswith("ar")
        self.setWindowTitle("ألوان التعليقات التوضيحية" if self._is_ar else "Annotation Colors")
        self.setLayoutDirection(Qt.LayoutDirection.RightToLeft if self._is_ar else Qt.LayoutDirection.LeftToRight)
        self.setAttribute(Qt.WidgetAttribute.WA_StyledBackground, True)
        self.setMinimumWidth(375)
        self.colors = dict(DEFAULT_ANNOTATION_COLORS)
        self.colors.update(colors or {})
        self._buttons = {}
        layout = QVBoxLayout(self)
        layout.setContentsMargins(20, 18, 20, 16)
        layout.setSpacing(10)
        heading = QLabel("ألوان التعليقات التوضيحية" if self._is_ar else "ANNOTATION COLORS")
        heading.setObjectName("dialogHeading")
        layout.addWidget(heading)
        hint = QLabel("تُستخدم هذه الألوان للتعليقات التوضيحية الجديدة، بينما تحتفظ التعليقات الحالية بألوانها المحفوظة." if self._is_ar else "These colors are used for new annotations. Existing annotations keep their saved colors.")
        hint.setObjectName("dialogHint")
        hint.setWordWrap(True)
        layout.addWidget(hint)
        for key, title in self.OPTIONS:
            row = QHBoxLayout()
            translated_title = {"Pen / drawing color":"لون القلم / الرسم", "Highlight color":"لون التظليل", "Sticky note marker color":"لون علامة الملاحظة اللاصقة", "Text box font color":"لون خط مربع النص", "Text box background color":"لون خلفية مربع النص"}.get(title, title)
            label = QLabel(translated_title if self._is_ar else title)
            label.setObjectName("dialogLabel")
            row.addWidget(label, 1)
            btn = ColorSwatchButton(self.colors[key], self)
            btn.clicked.connect(lambda checked=False, k=key: self._pick(k))
            self._buttons[key] = btn
            row.addWidget(btn)
            layout.addLayout(row)
        reset = QPushButton("استعادة الافتراضي" if self._is_ar else "Restore defaults")
        reset.clicked.connect(self._reset)
        layout.addWidget(reset, 0, Qt.AlignmentFlag.AlignLeft)
        box = QDialogButtonBox(QDialogButtonBox.StandardButton.Cancel | QDialogButtonBox.StandardButton.Save)
        box.button(QDialogButtonBox.StandardButton.Save).setText("حفظ الألوان" if self._is_ar else "Save colors")
        box.button(QDialogButtonBox.StandardButton.Cancel).setText("إلغاء" if self._is_ar else "Cancel")
        _set_compact_dialog_button_heights(box, 26)
        box.accepted.connect(self.accept)
        box.rejected.connect(self.reject)
        layout.addWidget(box)
        self._refresh()

    def _refresh(self):
        for key, button in self._buttons.items():
            color = self.colors[key]
            button.setColor(color)

    def _pick(self, key):
        color_picker = QColorDialog(QColor(self.colors[key]), self)
        _configure_color_dialog(color_picker, self._is_ar)
        labels_ar = {"pen":"لون القلم / الرسم", "highlight":"لون التظليل", "note":"لون علامة الملاحظة اللاصقة", "text_ink":"لون خط مربع النص", "text_fill":"لون خلفية مربع النص"}
        color_picker.setWindowTitle(labels_ar.get(key, key) if self._is_ar else self._label_for(key))
        color_picker.setLayoutDirection(Qt.LayoutDirection.RightToLeft if self._is_ar else Qt.LayoutDirection.LeftToRight)
        color = color_picker.currentColor() if color_picker.exec() == QDialog.DialogCode.Accepted else QColor()
        if color.isValid():
            self.colors[key] = color.name()
            self._refresh()

    def _label_for(self, key):
        title = dict(self.OPTIONS).get(key, key)
        if self._is_ar:
            return {"Pen / drawing color":"لون القلم / الرسم", "Highlight color":"لون التظليل", "Sticky note marker color":"لون علامة الملاحظة اللاصقة", "Text box font color":"لون خط مربع النص", "Text box background color":"لون خلفية مربع النص"}.get(title, title)
        return title

    def _reset(self):
        self.colors = dict(DEFAULT_ANNOTATION_COLORS)
        self._refresh()



class AnnotationColorEditDialog(QDialog):
    """Choose one annotation color, or both text/background colors for FreeText."""
    def __init__(self, parent, current_color="#808080", is_ar=False,
                 background_color=None, allow_background=False):
        super().__init__(parent)
        self._is_ar = bool(is_ar)
        self._background_changed = False
        self._allow_background = bool(allow_background)
        self.setWindowTitle("تعديل ألوان التعليق التوضيحي" if self._is_ar else "Edit annotation colors")
        self.setModal(True)
        self.setMinimumWidth(300)
        self.setLayoutDirection(Qt.LayoutDirection.RightToLeft if self._is_ar else Qt.LayoutDirection.LeftToRight)
        root = QVBoxLayout(self)
        root.setContentsMargins(18, 16, 18, 14)
        root.setSpacing(12)

        text_row = QHBoxLayout()
        text_label = QLabel("لون الخط" if self._is_ar else "Text color")
        text_label.setObjectName("dialogLabel")
        text_row.addWidget(text_label, 1)
        self.swatch = ColorSwatchButton(current_color, self, diameter=34)
        self.swatch.clicked.connect(lambda: self._choose_color(self.swatch, False))
        text_row.addWidget(self.swatch, 0, Qt.AlignmentFlag.AlignVCenter)
        root.addLayout(text_row)

        self.background_swatch = None
        if self._allow_background:
            background_row = QHBoxLayout()
            background_label = QLabel("لون الخلفية" if self._is_ar else "Background color")
            background_label.setObjectName("dialogLabel")
            background_row.addWidget(background_label, 1)
            self.background_swatch = ColorSwatchButton(background_color or "#ffffff", self, diameter=34)
            self.background_swatch.clicked.connect(
                lambda: self._choose_color(self.background_swatch, True)
            )
            background_row.addWidget(self.background_swatch, 0, Qt.AlignmentFlag.AlignVCenter)
            root.addLayout(background_row)

        hint = QLabel("اضغط على الدائرة لتغيير اللون." if self._is_ar else "Click a color circle to change it.")
        hint.setObjectName("dialogHint")
        root.addWidget(hint)
        buttons = QDialogButtonBox(QDialogButtonBox.StandardButton.Cancel | QDialogButtonBox.StandardButton.Save)
        buttons.button(QDialogButtonBox.StandardButton.Save).setText("حفظ" if self._is_ar else "Save")
        buttons.button(QDialogButtonBox.StandardButton.Cancel).setText("إلغاء" if self._is_ar else "Cancel")
        _set_compact_dialog_button_heights(buttons, 26)
        buttons.accepted.connect(self.accept)
        buttons.rejected.connect(self.reject)
        root.addWidget(buttons)

    @property
    def selected_color(self):
        return self.swatch.color()

    @property
    def selected_background_color(self):
        return self.background_swatch.color() if self._background_changed and self.background_swatch is not None else None

    def _choose_color(self, swatch, is_background=False):
        picker = QColorDialog(QColor(swatch.color()), self)
        _configure_color_dialog(picker, self._is_ar)
        picker.setWindowTitle(("لون الخلفية" if is_background else "لون الخط") if self._is_ar else
                              ("Background color" if is_background else "Text color"))
        picker.setLayoutDirection(Qt.LayoutDirection.RightToLeft if self._is_ar else Qt.LayoutDirection.LeftToRight)
        if picker.exec() == QDialog.DialogCode.Accepted and picker.currentColor().isValid():
            swatch.setColor(picker.currentColor().name())
            if is_background:
                self._background_changed = True


def _distance_point_to_segment(point, start, end):
    px, py = float(point.x), float(point.y)
    ax, ay = float(start.x), float(start.y)
    bx, by = float(end.x), float(end.y)
    dx, dy = bx - ax, by - ay
    denom = dx * dx + dy * dy
    if denom <= 1e-9:
        return math.hypot(px - ax, py - ay)
    t = max(0.0, min(1.0, ((px - ax) * dx + (py - ay) * dy) / denom))
    return math.hypot(px - (ax + t * dx), py - (ay + t * dy))


def _rdp_simplify(points, epsilon):
    """Iterative Ramer-Douglas-Peucker simplification for long pen paths."""
    if len(points) <= 2:
        return list(points)
    keep = {0, len(points) - 1}
    stack = [(0, len(points) - 1)]
    while stack:
        start_i, end_i = stack.pop()
        start, end = points[start_i], points[end_i]
        best_distance, best_index = 0.0, -1
        for i in range(start_i + 1, end_i):
            distance = _distance_point_to_segment(points[i], start, end)
            if distance > best_distance:
                best_distance, best_index = distance, i
        if best_index >= 0 and best_distance > epsilon:
            keep.add(best_index)
            stack.append((start_i, best_index))
            stack.append((best_index, end_i))
    return [points[i] for i in sorted(keep)]


def _simplify_closed_path(points, epsilon):
    """Simplify a closed stroke without collapsing its coincident endpoints."""
    if len(points) < 4:
        return list(points)
    # Split the loop at its farthest pair, simplify both open arcs, then join.
    origin = points[0]
    best_i = max(range(1, len(points)),
                 key=lambda i: (points[i].x-origin.x)**2 + (points[i].y-origin.y)**2)
    anchor = points[best_i]
    best_j = max((i for i in range(len(points)) if i not in (best_i, (best_i-1) % len(points))),
                 key=lambda i: (points[i].x-anchor.x)**2 + (points[i].y-anchor.y)**2)
    if best_j < best_i:
        best_i, best_j = best_j, best_i
    arc1 = points[best_i:best_j + 1]
    arc2 = points[best_j:] + points[:best_i + 1]
    a = _rdp_simplify(arc1, epsilon)
    b = _rdp_simplify(arc2, epsilon)
    combined = a[:-1] + b[:-1]
    # Remove adjacent duplicates caused by noisy pen samples.
    result = []
    for pt in combined:
        if not result or math.hypot(pt.x - result[-1].x, pt.y - result[-1].y) > max(1.0, epsilon * 0.18):
            result.append(pt)
    return result


def _recognize_pen_shape(points):
    """Recognize approximate hand-drawn shapes without requiring a perfect closure.

    Classification is corner-first: rough triangles and quadrilaterals are identified
    before circle fitting, preventing square/triangle strokes from being misread as
    circles. Small closing gaps and uneven/wavy sides are intentionally tolerated.
    """
    try:
        pts = [fitz.Point(float(pt.x), float(pt.y)) for pt in points]
    except Exception:
        return None
    clean = []
    for pt in pts:
        if not clean or math.hypot(pt.x-clean[-1].x, pt.y-clean[-1].y) >= 0.65:
            clean.append(pt)
    if len(clean) < 3:
        return None
    xs, ys = [pt.x for pt in clean], [pt.y for pt in clean]
    x0, x1, y0, y1 = min(xs), max(xs), min(ys), max(ys)
    width, height = x1-x0, y1-y0
    diagonal = math.hypot(width, height)
    if diagonal < 9:
        return None

    path_len = sum(math.hypot(b.x-a.x, b.y-a.y) for a, b in zip(clean, clean[1:]))
    endpoint = math.hypot(clean[-1].x-clean[0].x, clean[-1].y-clean[0].y)
    max_deviation = max((_distance_point_to_segment(pt, clean[0], clean[-1])
                         for pt in clean[1:-1]), default=0.0)
    # Accept a visibly hand-drawn line, including gentle wobble and short overshoots.
    if endpoint >= max(9.0, diagonal*0.50) and path_len/max(endpoint, 1e-6) <= 1.62 \
            and max_deviation <= max(6.0, diagonal*0.13):
        return {"kind": "line", "points": [clean[0], clean[-1]]}

    # The pen does not need to return exactly to the first point. A gap approaching
    # two-fifths of the diagonal is acceptable when the path otherwise wraps a shape.
    close_tolerance = max(12.0, diagonal*0.24)
    is_closed = endpoint <= close_tolerance and path_len >= diagonal*1.22
    ring = clean[:-1] if endpoint <= max(2.5, diagonal*0.045) else list(clean)
    if not is_closed or len(ring) < 3 or min(width, height) < 7:
        return None

    # Compute a normalized ellipse fit once. Polygon corners are still given
    # priority below, but the fit lets a smooth circle remain a circle even when
    # high-level simplification leaves only four broad arc points.
    ratio = width/max(height, 1e-6)
    radial_error = 1.0
    cx, cy = (x0+x1)/2.0, (y0+y1)/2.0
    if 0.42 <= ratio <= 2.40 and len(ring) >= 8:
        rx, ry = max(width/2.0, 1e-6), max(height/2.0, 1e-6)
        radii = [math.hypot((pt.x-cx)/rx, (pt.y-cy)/ry) for pt in ring]
        mean_r = sum(radii)/len(radii)
        radial_error = math.sqrt(sum((r-mean_r)**2 for r in radii)/len(radii))/max(mean_r, 1e-6)

    # Progressive simplification tolerates curved corners and uneven hand movement.
    simplified = []
    epsilon = max(3.0, diagonal*0.032)
    for _ in range(8):
        candidate = _simplify_closed_path(ring, epsilon)
        if len(candidate) >= 3:
            simplified = candidate
            if len(candidate) <= 4:
                break
        epsilon *= 1.28

    # Distinguish a smooth oval from a hand-drawn quadrilateral. Both can reduce
    # to four broad points, so use the original stroke's arc length as well as its
    # normalized radial fit: a square is mostly straight edges, while an oval's
    # curved perimeter is measurably longer than its four-chord approximation.
    simplified_perimeter = sum(
        math.hypot(simplified[(i+1) % len(simplified)].x-simplified[i].x,
                   simplified[(i+1) % len(simplified)].y-simplified[i].y)
        for i in range(len(simplified))
    ) if len(simplified) >= 3 else 0.0
    closed_path_length = path_len + endpoint
    curve_excess = (closed_path_length / max(simplified_perimeter, 1e-6)) - 1.0
    # A smooth oval has nearly constant normalized radius around its center.
    # Boxes can have a similarly long, wobbly pen path, but their normalized
    # radius varies markedly between side midpoints and corners. Tighten the
    # radial-fit tolerance so an imperfect square cannot become a circle.
    looks_like_oval = (len(ring) >= 8 and len(simplified) >= 4
                       and radial_error <= 0.09 and curve_excess >= 0.025)
    if looks_like_oval:
        diameter = (width+height)/2.0
        return {"kind": "circle", "rect": fitz.Rect(cx-diameter/2, cy-diameter/2,
                                                      cx+diameter/2, cy+diameter/2)}

    # Rough rectangles / squares (including mildly rotated ones).
    if len(simplified) == 4:
        vectors, lengths = [], []
        for i in range(4):
            a, b = simplified[i], simplified[(i+1)%4]
            dx, dy = b.x-a.x, b.y-a.y
            lengths.append(math.hypot(dx, dy))
            vectors.append((dx, dy))
        if min(lengths) >= max(6.0, diagonal*0.085):
            angle_scores = []
            for i in range(4):
                ax, ay = vectors[i-1]
                bx, by = vectors[i]
                denom = max(math.hypot(ax, ay)*math.hypot(bx, by), 1e-6)
                angle_scores.append(abs((ax*bx+ay*by)/denom))
            if sum(angle_scores)/4.0 <= 0.56 and min(angle_scores) <= 0.82:
                axis_aligned = all(min(abs(v[0]), abs(v[1])) <= max(6.0, diagonal*0.13)
                                   for v in vectors)
                # A hand-drawn box whose corners are close to 90 degrees and whose
                # sides lie within ~15 degrees of horizontal/vertical is snapped to
                # a true upright rectangle (right angles, rotation 0).
                near_right = max(angle_scores) <= 0.36
                near_axis = all(min(abs(v[0]), abs(v[1])) / max(math.hypot(v[0], v[1]), 1e-6) <= 0.26
                                for v in vectors)
                if axis_aligned or (near_right and near_axis):
                    bx0 = min(pt.x for pt in simplified); bx1 = max(pt.x for pt in simplified)
                    by0 = min(pt.y for pt in simplified); by1 = max(pt.y for pt in simplified)
                    cx, cy = (bx0+bx1)/2.0, (by0+by1)/2.0
                    box_ratio = (bx1-bx0)/max(by1-by0, 1e-6)
                    if 0.70 <= box_ratio <= 1.42:
                        side = (bx1-bx0 + by1-by0)/2.0
                        return {"kind": "square", "rect": fitz.Rect(cx-side/2, cy-side/2,
                                                                       cx+side/2, cy+side/2)}
                    return {"kind": "rectangle", "rect": fitz.Rect(bx0, by0, bx1, by1)}
                return {"kind": "quadrilateral", "points": simplified}

    # A triangle may have one extra wobble point near a corner. Drop the least
    # salient point and retain the three dominant corners.
    triangle_points = None
    if len(simplified) == 3:
        triangle_points = simplified
    elif len(simplified) == 4:
        best = None
        for skip in range(4):
            candidate = [pt for i, pt in enumerate(simplified) if i != skip]
            edges = [math.hypot(candidate[(i+1)%3].x-candidate[i].x,
                                candidate[(i+1)%3].y-candidate[i].y) for i in range(3)]
            if min(edges) >= max(6.0, diagonal*0.09):
                removed = simplified[skip]
                score = _distance_point_to_segment(removed, candidate[-1], candidate[0])
                if best is None or score < best[0]:
                    best = (score, candidate)
        if best is not None:
            triangle_points = best[1]
    if triangle_points is not None:
        side_lengths = [math.hypot(triangle_points[(i+1)%3].x-triangle_points[i].x,
                                   triangle_points[(i+1)%3].y-triangle_points[i].y) for i in range(3)]
        if min(side_lengths) >= max(6.0, diagonal*0.09):
            return {"kind": "triangle", "points": triangle_points}

    # Remaining smooth closed paths are tested as circles/ellipses. Polygonal shapes
    # have already been claimed above, so a forgiving radial tolerance won't turn a
    # rough square or triangle into a circle.
    if looks_like_oval:
        diameter = (width+height)/2.0
        return {"kind": "circle", "rect": fitz.Rect(cx-diameter/2, cy-diameter/2,
                                                      cx+diameter/2, cy+diameter/2)}
    return None


def _ellipse_resize_preview_rect(original_rect: QRectF, handle_name: str,
                                 pointer: QPointF, page_rect: QRectF) -> QRectF:
    """Resize one ellipse axis from a cardinal grip, keeping its center fixed.

    p0/p2 (top/bottom) change only height; p1/p3 (right/left) change only width.
    All values are canvas coordinates, so page rotation and zoom stay consistent.
    """
    rect = QRectF(original_rect).normalized()
    name = str(handle_name or "")
    cx, cy = rect.center().x(), rect.center().y()
    if name in ("p0", "p2"):
        max_radius = max(2.0, min(cy - page_rect.top(), page_rect.bottom() - cy))
        min_radius = min(7.0, max_radius)
        radius = min(max_radius, max(min_radius, abs(float(pointer.y()) - cy)))
        return QRectF(rect.left(), cy - radius, rect.width(), radius * 2.0).normalized()
    if name in ("p1", "p3"):
        max_radius = max(2.0, min(cx - page_rect.left(), page_rect.right() - cx))
        min_radius = min(7.0, max_radius)
        radius = min(max_radius, max(min_radius, abs(float(pointer.x()) - cx)))
        return QRectF(cx - radius, rect.top(), radius * 2.0, rect.height()).normalized()
    return rect


class _SmartPageThemeSignals(QObject):
    finished = pyqtSignal(object, object, int, int)


class _SmartPageThemeTask(QRunnable):
    """Apply Smart Page Theme off the GUI thread to an already-rendered RGB page."""
    def __init__(self, cache_key, image_bytes: bytes, width: int, height: int,
                 bg: str, ink: str, signals: _SmartPageThemeSignals):
        super().__init__()
        self.cache_key = cache_key
        self.image_bytes = bytes(image_bytes)
        self.width = int(width)
        self.height = int(height)
        self.bg = str(bg)
        self.ink = str(ink)
        self.signals = signals
        self.setAutoDelete(True)

    def run(self):
        result = b""
        try:
            source = Image.frombytes("RGB", (self.width, self.height), self.image_bytes)
            themed = apply_page_theme_to_image(
                source, True, self.bg, self.ink, smart=True
            )
            result = themed.tobytes()
        except Exception:
            # Keep the fast preview already in the canvas cache if an unusual
            # image or codec fails; never crash the rendering thread or the UI.
            result = b""
        try:
            self.signals.finished.emit(
                self.cache_key, result, self.width, self.height
            )
        except RuntimeError:
            # The owning canvas may have closed while the worker was finishing.
            pass


class TextAnnotationEditorDialog(QDialog):
    """Editor for PDF FreeText and sticky-note annotations."""
    @staticmethod
    def _left_to_right_text_option():
        from PyQt6.QtGui import QTextOption
        option = QTextOption()
        option.setTextDirection(Qt.LayoutDirection.LeftToRight)
        option.setAlignment(Qt.AlignmentFlag.AlignLeft)
        option.setWrapMode(QTextOption.WrapMode.WordWrap)
        return option

    def __init__(self, text="", fontsize=11, fontname="Helv", parent=None):
        super().__init__(parent)
        try:
            host_window = parent.window() if parent is not None else None
            host_settings = getattr(host_window, "settings", None)
            language_value = host_settings.value("interface_language", "en", type=str) if host_settings is not None else "en"
        except Exception:
            language_value = "en"
        self._is_ar = str(language_value or "en").lower().startswith("ar")
        self.setWindowTitle("تعديل نص PDF" if self._is_ar else "Edit PDF text")
        self.setLayoutDirection(Qt.LayoutDirection.RightToLeft if self._is_ar else Qt.LayoutDirection.LeftToRight)
        self.setAttribute(Qt.WidgetAttribute.WA_StyledBackground, True)
        self.resize(520, 390)
        root = QVBoxLayout(self)
        root.setContentsMargins(14, 12, 14, 12)
        root.setSpacing(8)
        self.editor = QTextEdit()
        self.editor.setAcceptRichText(False)
        self.editor.setLayoutDirection(Qt.LayoutDirection.LeftToRight)
        self.editor.setAlignment(Qt.AlignmentFlag.AlignLeft)
        self.editor.document().setDefaultTextOption(self._left_to_right_text_option())
        self.editor.setPlainText(str(text or ""))
        self.editor.setPlaceholderText("اكتب النص الخاص بهذا التعليق التوضيحي…" if self._is_ar else "Write the text for this PDF annotation…")
        root.addWidget(self.editor, 1)
        style_row = QHBoxLayout()
        style_row.addWidget(QLabel("الخط" if self._is_ar else "Font"))
        self.font_combo = QComboBox()
        for label, label_ar, value in [("Regular", "عادي", "Helv"), ("Bold", "عريض", "HelvB"), ("Italic", "مائل", "HelvI"), ("Bold italic", "عريض مائل", "HelvBI")]:
            self.font_combo.addItem(label_ar if self._is_ar else label, value)
        idx = self.font_combo.findData(fontname)
        self.font_combo.setCurrentIndex(idx if idx >= 0 else 0)
        style_row.addWidget(self.font_combo)
        style_row.addSpacing(10)
        style_row.addWidget(QLabel("الحجم" if self._is_ar else "Size"))
        self.size_spin = QSpinBox()
        self.size_spin.setRange(6, 48)
        self.size_spin.setValue(max(6, min(48, int(round(float(fontsize or 11))))))
        self.size_spin.setSuffix(" pt")
        style_row.addWidget(self.size_spin)
        style_row.addStretch(1)
        root.addLayout(style_row)
        hint = QLabel("يُطبّق التنسيق العريض والمائل والحجم على التعليق النصي بالكامل. لا تدعم تعليقات PDF النصية تنسيقات مختلطة موثوقة داخل مربع نص واحد." if self._is_ar else "Bold, italic and size apply to the whole PDF text annotation. PDF FreeText annotations do not support reliable mixed formatting within one text box.")
        hint.setObjectName("dialogHint")
        hint.setWordWrap(True)
        root.addWidget(hint)
        buttons = QDialogButtonBox(QDialogButtonBox.StandardButton.Cancel | QDialogButtonBox.StandardButton.Save)
        buttons.button(QDialogButtonBox.StandardButton.Save).setObjectName("primary")
        buttons.button(QDialogButtonBox.StandardButton.Save).setText("حفظ" if self._is_ar else "Save")
        buttons.button(QDialogButtonBox.StandardButton.Cancel).setText("إلغاء" if self._is_ar else "Cancel")
        buttons.accepted.connect(self.accept)
        buttons.rejected.connect(self.reject)
        root.addWidget(buttons)

    def values(self):
        return self.editor.toPlainText(), int(self.size_spin.value()), str(self.font_combo.currentData() or "Helv")
