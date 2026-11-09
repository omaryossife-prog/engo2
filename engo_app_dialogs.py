# Auto-split from main.py (verbatim move; do not reformat).
from __future__ import annotations

import math
import os
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

from engo_ai_core import (
    AI_PROVIDER_LABELS,
    _provider_key_service,
)
from engo_base import (
    DEFAULT_ANNOTATION_COLORS,
    DEFAULT_BG,
    DEFAULT_INK,
    _engo_apply_dialog_consistency,
    _engo_apply_windows_caption_theme,
    engo_ui_theme_tokens,
    is_supported_document,
    normalize_ui_theme,
    resource_path,
)
from engo_document import (
    DocumentCanvas,
    DocumentTab,
)



DOCUMENT_TAB_MIME = "application/x-engo-pdf-document-tab"
_DOCUMENT_TAB_DRAG_REGISTRY = {}


class DocumentTabBar(QTabBar):
    """Stable tab drag targets with visual link feedback, reorder, and tear-off."""

    def __init__(self, owner):
        super().__init__(owner)
        self.owner = owner
        self._pressed_tab = None
        self._press_global = QPoint()
        self._drag_active = False
        self._link_target_tab = None
        self._link_target_pos = QPoint()
        self._press_tab_rects = {}
        self._drop_indicator_x = None
        self._drop_insert_index = None
        # Keep tab geometry stable during a drag. We handle reorder/link gestures
        # ourselves so a dragged tab cannot jump over the tab the user is targeting.
        self.setMovable(False)
        self._external_link_target_index = -1
        self.setAcceptDrops(True)
        self.setElideMode(Qt.TextElideMode.ElideRight)
        self.setDrawBase(False)

        # Poll the global pointer as a fallback. Some Windows/Qt combinations stop
        # delivering QTabBar mouseMove events after the pointer leaves the tab strip.
        self._tearoff_poll = QTimer(self)
        self._tearoff_poll.setInterval(10)
        self._tearoff_poll.timeout.connect(self._poll_tearoff_drag)

    def mousePressEvent(self, event):
        if event.button() == Qt.MouseButton.LeftButton:
            index = self.tabAt(event.position().toPoint())
            self._pressed_tab = (self.owner._tab_order[index]
                                 if 0 <= index < len(self.owner._tab_order) else None)
            # Keep the initial tab hit zones stable for the duration of the drag.
            self._press_tab_rects = {
                tab: QRect(self.tabRect(i))
                for i, tab in enumerate(self.owner._tab_order)
                if i < self.count() and self.isTabVisible(i)
            }
            self._press_global = event.globalPosition().toPoint()
            self._drag_active = False
            self._link_target_tab = None
            if self._pressed_tab is not None:
                self._tearoff_poll.start()
        super().mousePressEvent(event)

    def _clear_press_state(self):
        self._tearoff_poll.stop()
        self._pressed_tab = None
        self._drag_active = False
        self._link_target_tab = None
        self._link_target_pos = QPoint()
        self._press_tab_rects = {}
        self._drop_indicator_x = None
        self._drop_insert_index = None
        self.update()

    def forget_tab(self, tab):
        """Forget drag references before a tab is moved or permanently closed."""
        if tab is None:
            return
        if self._pressed_tab is tab or self._link_target_tab is tab:
            self._clear_press_state()
            return
        self._press_tab_rects.pop(tab, None)
        self.update()

    def _safe_tab_index(self, tab):
        """Return a tab index without allowing deleted Qt wrappers to break paint."""
        if tab is None:
            return -1
        try:
            return self.owner.tabs.indexOf(tab)
        except (RuntimeError, TypeError):
            return -1

    def _insertion_target_for_position(self, pos):
        """Return the real tab-order insertion index and the visible green marker x."""
        visible = []
        order_without_source = [tab for tab in self.owner._tab_order if tab is not self._pressed_tab]
        for tab in order_without_source:
            index = self._safe_tab_index(tab)
            if index < 0 or index >= self.count() or not self.isTabVisible(index):
                continue
            rect = self.tabRect(index)
            if not rect.isNull():
                visible.append((rect.center().x(), rect, order_without_source.index(tab)))
        visible.sort(key=lambda item: item[0])
        if not visible:
            return 0, max(3, min(self.width() - 3, pos.x()))
        insert_at = len(order_without_source)
        marker_x = visible[-1][1].right() + 3
        for i, (center_x, _rect, actual_index) in enumerate(visible):
            if pos.x() < center_x:
                insert_at = actual_index
                marker_x = visible[0][1].left() - 3 if i == 0 else (visible[i - 1][1].right() + _rect.left()) // 2
                break
            insert_at = min(len(order_without_source), actual_index + 1)
        marker_x = max(3, min(self.width() - 3, int(marker_x)))
        return insert_at, marker_x

    def _distance_outside_tabbar(self, global_pos):
        """Return how far the pointer has clearly left the tab strip."""
        local_pos = self.mapFromGlobal(global_pos)
        dx = max(0, -local_pos.x(), local_pos.x() - self.width() + 1)
        dy = max(0, -local_pos.y(), local_pos.y() - self.height() + 1)
        return math.hypot(dx, dy)

    def _is_deliberate_tearoff(self, global_pos):
        # A normal click can drift a few pixels outside a short tab strip.
        # Require a clearly intentional excursion before launching a QDrag;
        # reordering/linking inside the strip keeps the normal drag threshold.
        minimum_clearance = max(8, int(QApplication.startDragDistance()))
        return self._distance_outside_tabbar(global_pos) >= minimum_clearance

    def _begin_tearoff(self, global_pos):
        tab = self._pressed_tab
        if tab is None or self._safe_tab_index(tab) < 0:
            self._clear_press_state()
            return
        self._clear_press_state()
        self.owner._start_document_tab_drag(tab, global_pos)

    def _poll_tearoff_drag(self):
        tab = self._pressed_tab
        if tab is None:
            self._tearoff_poll.stop()
            return
        try:
            buttons = QApplication.mouseButtons()
            if not (buttons & Qt.MouseButton.LeftButton):
                self._clear_press_state()
                return
            global_pos = QCursor.pos()
            distance = (global_pos - self._press_global).manhattanLength()
            if (distance >= QApplication.startDragDistance()
                    and self._is_deliberate_tearoff(global_pos)):
                self._begin_tearoff(global_pos)
        except RuntimeError:
            self._clear_press_state()

    def _find_link_target(self, pos):
        """Only the central 60% of another visible tab is a link drop zone."""
        source_tab = self._pressed_tab
        if source_tab is None or self._safe_tab_index(source_tab) < 0 or not self.rect().contains(pos):
            return None
        for candidate in self.owner._tab_order:
            if candidate is source_tab:
                continue
            index = self._safe_tab_index(candidate)
            if index < 0 or index >= self.count() or not self.isTabVisible(index):
                continue
            rect = self.tabRect(index)
            if rect.isNull() or not rect.contains(pos):
                continue
            relative_x = pos.x() - rect.left()
            if rect.width() * 0.20 <= relative_x <= rect.width() * 0.80:
                return candidate
        return None

    def paintEvent(self, event):
        super().paintEvent(event)
        if not self._drag_active and self._external_link_target_index < 0 and self._drop_indicator_x is None:
            return

        # A QTabBar may receive a queued repaint after a document has been
        # closed or moved to another window.  Never let an invalid PyQt wrapper
        # escape from paintEvent; that would also skip QPainter.end().
        source_index = self._safe_tab_index(self._pressed_tab)
        target_index = self._safe_tab_index(self._link_target_tab)
        if self._pressed_tab is not None and source_index < 0:
            self._clear_press_state()
            source_index = -1
            target_index = -1
        elif self._link_target_tab is not None and target_index < 0:
            self._link_target_tab = None

        painter = QPainter(self)
        if not painter.isActive():
            return
        try:
            painter.setRenderHint(QPainter.RenderHint.Antialiasing, True)
            green = QColor(39, 190, 112)
            target_indices = set()
            if target_index >= 0:
                target_indices.add(target_index)
            if self._external_link_target_index >= 0:
                target_indices.add(self._external_link_target_index)
            if source_index >= 0:
                source_rect = self.tabRect(source_index).adjusted(2, 2, -2, -2)
                painter.setPen(QPen(QColor(39, 190, 112, 190), 2))
                painter.setBrush(QColor(39, 190, 112, 32))
                painter.drawRoundedRect(source_rect, 7, 7)
            for idx in target_indices:
                if not (0 <= idx < self.count()):
                    continue
                target_rect = self.tabRect(idx).adjusted(2, 2, -2, -2)
                painter.setPen(QPen(green, 2))
                painter.setBrush(QColor(39, 190, 112, 82))
                painter.drawRoundedRect(target_rect, 7, 7)
                painter.setPen(QColor(205, 255, 224))
                painter.drawText(target_rect.adjusted(4, 0, -7, 0),
                                 Qt.AlignmentFlag.AlignRight | Qt.AlignmentFlag.AlignVCenter,
                                 "🔗")
            if self._drop_indicator_x is not None and self._link_target_tab is None:
                x = int(self._drop_indicator_x)
                painter.setPen(Qt.PenStyle.NoPen)
                painter.setBrush(QColor(39, 190, 112, 65))
                painter.drawRoundedRect(QRectF(x - 5, 3, 10, max(8, self.height() - 6)), 5, 5)
                painter.setBrush(QColor(72, 235, 145))
                painter.drawRoundedRect(QRectF(x - 2, 2, 4, max(10, self.height() - 4)), 2, 2)
        finally:
            painter.end()

    def mouseMoveEvent(self, event):
        if self._pressed_tab is not None and (event.buttons() & Qt.MouseButton.LeftButton):
            global_pos = event.globalPosition().toPoint()
            distance = (global_pos - self._press_global).manhattanLength()
            if distance >= QApplication.startDragDistance():
                self._drag_active = True
                over_tab_bar = self.rect().contains(self.mapFromGlobal(global_pos))
                if not over_tab_bar:
                    if self._is_deliberate_tearoff(global_pos):
                        self._begin_tearoff(global_pos)
                    # Small movements just outside the strip are not a tear-off.
                    # Keep the event here so a click/drag cannot be reinterpreted
                    # by Qt as another tab interaction while the button is held.
                    event.accept()
                    return
                pos = event.position().toPoint()
                new_target = self._find_link_target(pos)
                if new_target is not self._link_target_tab:
                    self._link_target_tab = new_target
                    self.update()
                if new_target is not None:
                    self._link_target_pos = QPoint(pos)
                    self._drop_indicator_x = None
                    self._drop_insert_index = None
                    source_name = Path(self._pressed_tab.path).name
                    target_name = Path(new_target.path).name
                    self.owner.show_status(f"🔗 Release to link {source_name} + {target_name}")
                else:
                    insert_at, marker_x = self._insertion_target_for_position(pos)
                    self._drop_insert_index = insert_at
                    self._drop_indicator_x = marker_x
                    self.owner.show_status("Release at the green marker to move this tab to that position")
                self.update()
                event.accept()
                return
        super().mouseMoveEvent(event)

    def mouseReleaseEvent(self, event):
        was_dragging = self._drag_active
        source_tab = self._pressed_tab
        target_tab = self._link_target_tab
        release_pos = event.position().toPoint()
        insertion_index = self._drop_insert_index
        super().mouseReleaseEvent(event)
        if not was_dragging:
            self._clear_press_state()
            return

        source_index = self._safe_tab_index(source_tab)
        target_index = self._safe_tab_index(target_tab)
        if source_index >= 0 and target_index >= 0 and source_index != target_index:
            self._clear_press_state()
            self.owner._link_tabs_in_window(source_index, target_index)
            return

        # A drag that did not land in the green link zone reorders the tabs.
        if self.rect().contains(release_pos) and source_index >= 0:
            drop_index = insertion_index
            if drop_index is None:
                drop_index, _marker = self._insertion_target_for_position(release_pos)
            drop_index = max(0, min(int(drop_index), max(0, self.count() - 1)))
            if drop_index != source_index:
                self.moveTab(source_index, drop_index)
                self.setCurrentIndex(drop_index)
                self.owner.tabs.setCurrentIndex(drop_index)
                self.owner.show_status("Tabs reordered")
        self._clear_press_state()

    def dragLeaveEvent(self, event):
        if self._external_link_target_index >= 0:
            self._external_link_target_index = -1
            self.update()
        super().dragLeaveEvent(event)

    def dragEnterEvent(self, event):
        mime = event.mimeData()
        if mime.hasFormat(DOCUMENT_TAB_MIME) or mime.hasUrls():
            event.acceptProposedAction()
        else:
            event.ignore()

    def dragMoveEvent(self, event):
        mime = event.mimeData()
        if mime.hasFormat(DOCUMENT_TAB_MIME):
            pos = event.position().toPoint()
            target_index = self.tabAt(pos)
            link_target = -1
            try:
                token = bytes(mime.data(DOCUMENT_TAB_MIME)).decode("ascii")
                entry = _DOCUMENT_TAB_DRAG_REGISTRY.get(token)
                if entry and target_index >= 0:
                    _source_window, source_tab = entry
                    target_tab = self.owner.tabs.widget(target_index)
                    rect = self.tabRect(target_index)
                    rel_x = pos.x() - rect.left()
                    center_drop = rect.width() * 0.20 <= rel_x <= rect.width() * 0.80
                    if target_tab is not source_tab and center_drop:
                        link_target = target_index
                        self.owner.show_status(f"🔗 Release to link {Path(source_tab.path).name} + {Path(target_tab.path).name}")
                    else:
                        self.owner.show_status("Release near a tab edge to reorder/move · release in its green center to link")
                elif entry:
                    self.owner.show_status("Release here to move this PDF tab into the window")
            except Exception:
                pass
            if link_target != self._external_link_target_index:
                self._external_link_target_index = link_target
                self.update()
            event.acceptProposedAction()
        elif mime.hasUrls():
            event.acceptProposedAction()
        else:
            event.ignore()

    def contextMenuEvent(self, event):
        index = self.tabAt(event.pos())
        if not (0 <= index < len(self.owner._tab_order)):
            return super().contextMenuEvent(event)
        tab = self.owner._tab_order[index]
        menu = QMenu(self)
        primary = self.owner._linked_primary_for_path(tab.path)
        companion = self.owner.linked_supplementary_tab(tab.path)
        pair_action = None
        if companion is not None or primary is not None:
            pair_action = menu.addAction("Unlink this PDF pair")
        elif sum(1 for i in range(self.owner.tabs.count()) if isinstance(self.owner.tabs.widget(i), DocumentTab)) >= 2:
            pair_action = menu.addAction("Link with another PDF…")
        close_others_action = None
        if self.owner.tabs.count() > 1:
            if pair_action is not None:
                menu.addSeparator()
            close_others_action = menu.addAction("Close Other Tabs")
        if not menu.actions():
            return super().contextMenuEvent(event)
        chosen = menu.exec(event.globalPos())
        if chosen is pair_action:
            if companion is not None or primary is not None:
                self.owner._unlink_document_relationships(tab)
                self.owner._refresh_linked_tab_layout()
                self.owner._refresh_ai_chat_context(tab)
                self.owner._refresh_linked_context_label()
                self.owner._update_controls()
                self.owner.show_status("PDF pair unlinked · both PDFs are independent tabs")
            else:
                self.owner.doc_tabbar.setCurrentIndex(index)
                self.owner.tabs.setCurrentIndex(index)
                self.owner.configure_linked_pdfs()
        elif chosen is close_others_action:
            self.owner._close_other_tabs(tab)

    def dropEvent(self, event):
        mime = event.mimeData()
        if mime.hasFormat(DOCUMENT_TAB_MIME):
            pos = event.position().toPoint()
            target_index = self.tabAt(pos)
            if target_index >= 0:
                rect = self.tabRect(target_index)
                rel_x = pos.x() - rect.left()
                if not (rect.width() * 0.20 <= rel_x <= rect.width() * 0.80):
                    target_index = -1
            self._external_link_target_index = -1
            self.update()
            if self.owner._receive_document_tab_drop(mime, self.mapToGlobal(pos), target_index):
                event.setDropAction(Qt.DropAction.MoveAction)
                event.accept()
            else:
                event.ignore()
            return
        if mime.hasUrls():
            paths = [u.toLocalFile() for u in mime.urls()
                     if u.isLocalFile() and is_supported_document(u.toLocalFile())]
            if paths:
                for path in paths:
                    self.owner.open_pdf(path)
                event.acceptProposedAction()
                return
        event.ignore()


def _theme_preview_pixmap(theme: str, size=QSize(150, 84)) -> QPixmap:
    """Draw a compact preview directly from the active centralized theme tokens."""
    t = engo_ui_theme_tokens(theme)
    c = {
        "bg": t["window"], "top": t["panel"], "side": t["input"],
        "panel": t["card"], "line": t["border"], "text": t["text"],
        "muted": t["muted"], "accent": t["accent"],
    }
    w, h = max(100, int(size.width())), max(60, int(size.height()))
    pix = QPixmap(w, h)
    pix.fill(QColor(c["bg"]))
    p = QPainter(pix)
    p.setRenderHint(QPainter.RenderHint.Antialiasing, True)
    p.setPen(Qt.PenStyle.NoPen)
    p.setBrush(QColor(c["top"]))
    p.drawRoundedRect(QRectF(0.5, 0.5, w - 1, h - 1), 7, 7)
    p.setBrush(QColor(c["bg"]))
    p.drawRoundedRect(QRectF(3, 3, w - 6, h - 6), 5, 5)
    p.setBrush(QColor(c["top"]))
    p.drawRoundedRect(QRectF(3, 3, w - 6, 13), 5, 5)
    p.setBrush(QColor(c["side"]))
    p.drawRoundedRect(QRectF(4, 17, 27, h - 21), 3, 3)
    p.setBrush(QColor(c["accent"]))
    p.drawRoundedRect(QRectF(7, 24, 21, 5), 2, 2)
    left = 36
    p.setBrush(QColor(c["panel"]))
    p.drawRoundedRect(QRectF(left, 20, w - left - 7, h - 28), 4, 4)
    p.setBrush(QColor(c["accent"]))
    p.drawRoundedRect(QRectF(left + 6, 26, max(20, w - left - 19), 7), 2, 2)
    p.setBrush(QColor(c["line"]))
    p.drawRoundedRect(QRectF(left + 6, 38, max(16, (w - left - 22) * .72), 3), 1, 1)
    p.drawRoundedRect(QRectF(left + 6, 44, max(16, (w - left - 22) * .52), 3), 1, 1)
    p.setBrush(QColor(c["muted"]))
    p.setOpacity(.75)
    p.drawRoundedRect(QRectF(left + 6, 53, max(14, (w - left - 22) * .85), 2), 1, 1)
    p.end()
    return pix

class ThemePreviewButton(QToolButton):
    """Selectable theme card with a miniature preview of the actual palette."""
    def __init__(self, theme: str, label: str, parent=None, preview_size=QSize(142, 78)):
        super().__init__(parent)
        self.theme_value = str(theme)
        self.setObjectName("themePreviewCard")
        self.setCheckable(True)
        self.setToolButtonStyle(Qt.ToolButtonStyle.ToolButtonTextUnderIcon)
        self.setIcon(QIcon(_theme_preview_pixmap(self.theme_value, preview_size)))
        self.setIconSize(preview_size)
        self.setText(label)
        self.setCursor(Qt.CursorShape.PointingHandCursor)
        self.setFocusPolicy(Qt.FocusPolicy.StrongFocus)
        self.setFixedSize(preview_size.width() + 22, preview_size.height() + 48)
        self.setAccessibleName(label)


class FirstRunSetupDialog(QDialog):
    """Mandatory two-step setup shown only when Engo has no saved local settings."""
    def __init__(self, parent=None):
        super().__init__(parent)
        self.selected_language = None
        self.selected_theme = None
        self._preview_theme = "dark"
        self._theme_transition_animation = None
        self.setProperty("engoOwnThemePreview", True)
        self.setObjectName("firstRunSetupDialog")
        self.setWindowTitle("Welcome to Engo · First-time setup")
        self.setModal(True)
        self.setMinimumSize(620, 500)
        self.resize(700, 560)
        self.setWindowFlags(self.windowFlags() & ~Qt.WindowType.WindowCloseButtonHint)

        root = QVBoxLayout(self)
        root.setContentsMargins(22, 20, 22, 18)
        root.setSpacing(14)

        hero = QFrame(self)
        hero.setObjectName("firstRunHero")
        hero_layout = QHBoxLayout(hero)
        hero_layout.setContentsMargins(18, 14, 18, 14)
        hero_layout.setSpacing(13)
        mark = QLabel("E")
        mark.setObjectName("firstRunMark")
        mark.setAlignment(Qt.AlignmentFlag.AlignCenter)
        mark.setFixedSize(48, 48)
        copy = QVBoxLayout()
        copy.setSpacing(2)
        title = QLabel("Welcome to (Engo) مرحبًا بك في ")
        title.setObjectName("firstRunTitle")
        subtitle = QLabel("Let's set up your study space in two quick steps")
        subtitle.setObjectName("firstRunSubtitle")
        copy.addWidget(title)
        copy.addWidget(subtitle)
        hero_layout.addWidget(mark)
        hero_layout.addLayout(copy, 1)
        root.addWidget(hero)

        self.step_label = QLabel("STEP 1 OF 2  ·  LANGUAGE")
        self.step_label.setObjectName("firstRunStep")
        root.addWidget(self.step_label)
        self.stack = QStackedWidget(self)
        self.stack.setObjectName("firstRunStack")
        root.addWidget(self.stack, 1)

        # Step one: language selection.
        language_page = QWidget()
        language_page.setObjectName("firstRunLanguagePage")
        language_page.setAutoFillBackground(True)
        self.language_page = language_page
        language_layout = QVBoxLayout(language_page)
        language_layout.setContentsMargins(4, 4, 4, 4)
        language_layout.setSpacing(12)
        self.language_heading = QLabel("Choose your interface language / اختر لغة الواجهة")
        self.language_heading.setObjectName("firstRunPageTitle")
        self.language_caption = QLabel("You can change this later in Settings.")
        self.language_caption.setObjectName("firstRunPageCaption")
        language_layout.addWidget(self.language_heading)
        language_layout.addWidget(self.language_caption)
        language_cards = QHBoxLayout()
        language_cards.setSpacing(12)
        self.language_group = QButtonGroup(self)
        self.language_group.setExclusive(True)
        self.language_cards = {}
        for code, label in (
            ("en", "English interface"),
            ("ar", "واجهة بالعربية"),
        ):
            card = QToolButton(language_page)
            card.setObjectName("firstRunLanguageCard")
            card.setCheckable(True)
            card.setToolButtonStyle(Qt.ToolButtonStyle.ToolButtonTextOnly)
            card.setText(label)
            card.setFixedSize(240, 124)
            card.setCursor(Qt.CursorShape.PointingHandCursor)
            card.clicked.connect(lambda _checked=False, value=code: self._choose_language(value))
            self.language_group.addButton(card)
            self.language_cards[code] = card
            language_cards.addWidget(card, 1)
        language_layout.addLayout(language_cards)
        language_layout.addStretch(1)
        self.stack.addWidget(language_page)

        # Step two: visual theme selection.
        theme_page = QWidget()
        theme_page.setObjectName("firstRunThemePage")
        theme_page.setAutoFillBackground(True)
        self.theme_page = theme_page
        theme_layout = QVBoxLayout(theme_page)
        theme_layout.setContentsMargins(4, 4, 4, 4)
        theme_layout.setSpacing(11)
        self.theme_heading = QLabel("Choose your theme")
        self.theme_heading.setObjectName("firstRunPageTitle")
        self.theme_caption = QLabel("Preview each look and choose the one you prefer.")
        self.theme_caption.setObjectName("firstRunPageCaption")
        theme_layout.addWidget(self.theme_heading)
        theme_layout.addWidget(self.theme_caption)
        theme_cards_widget = QWidget(theme_page)
        theme_cards_widget.setObjectName("firstRunThemeCards")
        theme_cards_widget.setAutoFillBackground(True)
        self.theme_cards_widget = theme_cards_widget
        theme_cards = QGridLayout(theme_cards_widget)
        theme_cards.setContentsMargins(0, 0, 0, 0)
        theme_cards.setHorizontalSpacing(8)
        theme_cards.setVerticalSpacing(8)
        self.theme_group = QButtonGroup(self)
        self.theme_group.setExclusive(True)
        self.theme_cards = {}
        theme_labels = {"light": "Light", "dark": "Dark", "midnight": "Midnight",
                        "grass": "Grass", "pink": "Pink", "orange": "Orange"}
        for position, value in enumerate(("light", "dark", "midnight", "grass", "pink", "orange")):
            card = ThemePreviewButton(value, theme_labels[value], theme_page, QSize(142, 80))
            card.clicked.connect(lambda _checked=False, key=value: self._choose_theme(key))
            self.theme_group.addButton(card)
            self.theme_cards[value] = card
            theme_cards.addWidget(card, position // 3, position % 3)
        for column in range(3):
            theme_cards.setColumnStretch(column, 1)
        theme_layout.addWidget(theme_cards_widget)
        self.theme_tip = QLabel("You can change the theme any time from Settings.")
        self.theme_tip.setObjectName("firstRunPageCaption")
        theme_layout.addWidget(self.theme_tip)
        theme_layout.addStretch(1)
        self.stack.addWidget(theme_page)

        footer = QHBoxLayout()
        self.back_button = QPushButton("Back")
        self.back_button.setObjectName("firstRunSecondary")
        self.back_button.clicked.connect(self._go_back)
        self.back_button.hide()
        footer.addWidget(self.back_button)
        footer.addStretch(1)
        self.next_button = QPushButton("Continue")
        self.next_button.setObjectName("firstRunPrimary")
        self.next_button.setEnabled(False)
        self.next_button.clicked.connect(self._on_next_clicked)
        footer.addWidget(self.next_button)
        root.addLayout(footer)
        self._apply_wizard_language("en")
        self._apply_wizard_style(self._preview_theme)

    def _choose_language(self, code):
        self.selected_language = code
        for key, card in self.language_cards.items():
            card.setChecked(key == code)
        self.next_button.setEnabled(True)

    def _choose_theme(self, theme):
        self.selected_theme = normalize_ui_theme(theme)
        for key, card in self.theme_cards.items():
            card.setChecked(key == self.selected_theme)
        self.next_button.setEnabled(True)
        self._animate_theme_preview(self.selected_theme)

    def _animate_theme_preview(self, theme):
        """Quickly fade the wizard while applying the chosen live theme preview."""
        theme = normalize_ui_theme(theme)
        old_animation = self._theme_transition_animation
        if old_animation is not None:
            try:
                old_animation.stop()
            except RuntimeError:
                pass
        fade_out = QPropertyAnimation(self, b"windowOpacity", self)
        fade_out.setDuration(75)
        fade_out.setEasingCurve(QEasingCurve.Type.OutCubic)
        fade_out.setStartValue(float(self.windowOpacity()))
        fade_out.setEndValue(0.76)
        self._theme_transition_animation = fade_out

        def apply_and_fade_back():
            self._apply_wizard_style(theme)
            fade_in = QPropertyAnimation(self, b"windowOpacity", self)
            fade_in.setDuration(115)
            fade_in.setEasingCurve(QEasingCurve.Type.OutCubic)
            fade_in.setStartValue(float(self.windowOpacity()))
            fade_in.setEndValue(1.0)
            self._theme_transition_animation = fade_in
            fade_in.finished.connect(lambda: setattr(self, "_theme_transition_animation", None))
            fade_in.start()

        fade_out.finished.connect(apply_and_fade_back)
        fade_out.start()

    def _apply_wizard_language(self, language):
        is_ar = language == "ar"
        self.step_label.setText("الخطوة ١ من ٢ · اللغة" if is_ar else "STEP 1 OF 2  ·  LANGUAGE")
        self.language_heading.setText("اختر لغة واجهة Engo" if is_ar else "Choose your interface language")
        self.language_caption.setText("يمكنك تغيير اللغة لاحقًا من الإعدادات." if is_ar else "You can change this later in Settings.")
        # Keep each language card in its own language, without duplicate headings.
        self.language_cards["en"].setText("English interface")
        self.language_cards["ar"].setText("واجهة بالعربية")
        self.language_cards["en"].setLayoutDirection(Qt.LayoutDirection.LeftToRight)
        self.language_cards["ar"].setLayoutDirection(Qt.LayoutDirection.RightToLeft)

    def _go_to_theme(self):
        if not self.selected_language:
            return
        is_ar = self.selected_language == "ar"
        self.stack.setCurrentIndex(1)
        self.step_label.setText("الخطوة ٢ من ٢ · المظهر" if is_ar else "STEP 2 OF 2  ·  APPEARANCE")
        self.theme_heading.setText("اختر مظهر Engo" if is_ar else "Choose your Engo theme")
        self.theme_caption.setText("شاهد معاينة كل ثيم واختر الشكل الأنسب لك." if is_ar else "Preview each theme and choose the look you prefer.")
        self.theme_tip.setText("يمكنك تغيير الثيم في أي وقت من الإعدادات." if is_ar else "You can change the theme any time from Settings.")
        theme_labels = {"light": ("فاتح" if is_ar else "Light"),
                        "dark": ("داكن" if is_ar else "Dark"),
                        "midnight": ("منتصف الليل" if is_ar else "Midnight"),
                        "grass": ("عشبي" if is_ar else "Grass"),
                        "pink": ("وردي" if is_ar else "Pink"),
                        "orange": ("برتقالي" if is_ar else "Orange")}
        for key, card in self.theme_cards.items():
            card.setText(theme_labels[key])
            card.setLayoutDirection(Qt.LayoutDirection.RightToLeft if is_ar else Qt.LayoutDirection.LeftToRight)
        self.back_button.setText("رجوع" if is_ar else "Back")
        self.back_button.show()
        self.next_button.setText("ابدأ استخدام Engo" if is_ar else "Start using Engo")
        self.next_button.setEnabled(bool(self.selected_theme))

    def _on_next_clicked(self):
        if self.stack.currentIndex() == 0:
            self._go_to_theme()
        elif self.selected_language and self.selected_theme:
            self.accept()

    def _go_back(self):
        if self.stack.currentIndex() == 1:
            self.stack.setCurrentIndex(0)
            self.back_button.hide()
            self.next_button.setText("متابعة" if self.selected_language == "ar" else "Continue")
            self.next_button.setEnabled(bool(self.selected_language))
            self._apply_wizard_language(self.selected_language or "en")
            self.step_label.setText("الخطوة ١ من ٢ · اللغة" if self.selected_language == "ar" else "STEP 1 OF 2  ·  LANGUAGE")

    def values(self):
        return {"interface_language": self.selected_language or "en", "ui_theme": self.selected_theme or "dark"}

    def reject(self):
        # This is a required first-run step; do not silently continue with an
        # unconfigured interface. The user can finish setup with two selections.
        return

    def closeEvent(self, event):
        event.ignore()

    def _apply_wizard_style(self, theme=None):
        """Apply one complete, high-contrast palette to every first-run surface."""
        theme = normalize_ui_theme(theme or self._preview_theme)
        self._preview_theme = theme
        c = engo_ui_theme_tokens(theme)
        # Accent hues differ in brightness across palettes. Use the higher-contrast
        # foreground for primary actions instead of forcing white on pale accents.
        accent_text = "#ffffff" if theme == "light" else "#17202b"

        palette = QPalette(self.palette())
        palette_roles = {
            QPalette.ColorRole.Window: c["window"],
            QPalette.ColorRole.WindowText: c["text"],
            QPalette.ColorRole.Base: c["input"],
            QPalette.ColorRole.AlternateBase: c["panel"],
            QPalette.ColorRole.Text: c["text"],
            QPalette.ColorRole.Button: c["raised"],
            QPalette.ColorRole.ButtonText: c["text"],
            QPalette.ColorRole.Highlight: c["selection"],
            QPalette.ColorRole.HighlightedText: c["selection_text"],
            QPalette.ColorRole.ToolTipBase: c["panel"],
            QPalette.ColorRole.ToolTipText: c["text"],
            QPalette.ColorRole.PlaceholderText: c["muted"],
        }
        for role, color in palette_roles.items():
            palette.setColor(role, QColor(color))
        self.setPalette(palette)
        self.setAutoFillBackground(True)
        for widget in (self.stack, self.language_page, self.theme_page, self.theme_cards_widget):
            widget.setPalette(palette)
            widget.setAutoFillBackground(True)

        self.setStyleSheet(f"""
            QDialog#firstRunSetupDialog {{ background:{c['window']}; color:{c['text']}; }}
            QDialog#firstRunSetupDialog QWidget {{ color:{c['text']}; }}
            QStackedWidget#firstRunStack {{ background:{c['panel']}; border:1px solid {c['border']}; border-radius:12px; }}
            QWidget#firstRunLanguagePage, QWidget#firstRunThemePage, QWidget#firstRunThemeCards {{
                background:{c['panel']}; color:{c['text']};
            }}
            QFrame#firstRunHero {{ background:{c['panel_alt']}; border:1px solid {c['border']};
                border-left:4px solid {c['accent']}; border-radius:14px; }}
            QLabel#firstRunMark {{ background:{c['accent']}; color:#ffffff; border-radius:12px;
                font-size:22pt; font-weight:850; }}
            QLabel#firstRunTitle {{ color:{c['text']}; font-size:15pt; font-weight:850; }}
            QLabel#firstRunSubtitle {{ color:{c['muted']}; font-size:9pt; }}
            QLabel#firstRunStep {{ color:{c['accent']}; font-size:8pt; font-weight:850;
                letter-spacing:1px; padding:2px 4px; }}
            QLabel#firstRunPageTitle {{ color:{c['text']}; font-size:15pt; font-weight:800; }}
            QLabel#firstRunPageCaption {{ color:{c['muted']}; font-size:9pt; }}
            QToolButton#firstRunLanguageCard {{ background:{c['card']}; color:{c['text']};
                border:1px solid {c['border']}; border-radius:12px; font-size:14pt;
                font-weight:800; padding:16px; }}
            QToolButton#firstRunLanguageCard:hover {{ background:{c['hover']}; border-color:{c['accent']}; }}
            QToolButton#firstRunLanguageCard:checked {{ background:{c['selection']};
                color:{c['selection_text']}; border:2px solid {c['accent']}; }}
            QToolButton#themePreviewCard {{ background:{c['card']}; color:{c['text']};
                border:1px solid {c['border']}; border-radius:10px; padding:7px;
                font-size:9pt; font-weight:800; }}
            QToolButton#themePreviewCard:hover {{ background:{c['hover']}; border-color:{c['accent']}; }}
            QToolButton#themePreviewCard:checked {{ background:{c['selection']};
                color:{c['selection_text']}; border:2px solid {c['accent']}; }}
            QPushButton#firstRunPrimary {{ background:{c['accent']}; color:{accent_text};
                border:1px solid {c['accent']}; border-radius:8px; padding:9px 18px;
                min-width:150px; min-height:34px; font-weight:800; }}
            QPushButton#firstRunPrimary:hover:enabled {{ background:{c['accent_hover']}; color:{accent_text}; }}
            QPushButton#firstRunPrimary:disabled {{ background:{c['raised']}; color:{c['muted']};
                border-color:{c['border']}; }}
            QPushButton#firstRunSecondary {{ background:{c['raised']}; color:{c['text']};
                border:1px solid {c['border']}; border-radius:8px; padding:8px 15px;
                min-height:34px; font-weight:700; }}
            QPushButton#firstRunSecondary:hover {{ background:{c['hover']}; border-color:{c['accent']}; }}
        """)
        # Keep the real Windows caption and native window controls in sync with
        # the same live preview palette (Qt stylesheets cannot paint the caption).
        _engo_apply_windows_caption_theme(self, theme)
        QTimer.singleShot(80, lambda obj=self, current=theme:
                          _engo_apply_windows_caption_theme(obj, current))


class _SettingsNoWheelSlider(QSlider):
    """Discrete settings slider that never consumes the mouse wheel.

    The settings dialog uses a scroll area. Ignoring wheel events here lets
    the event propagate to that scroll area instead of accidentally changing
    the slider value while the user is scrolling through the settings page.
    Values remain changeable with a deliberate click, drag, or keyboard input.
    """
    def wheelEvent(self, event):
        event.ignore()


class _SettingsNoWheelComboBox(QComboBox):
    """Settings dropdown that never changes its selection from a mouse wheel.

    Scrolling the settings page can leave the cursor resting over a dropdown
    (such as the interface-language combo) for a moment. A plain QComboBox
    would treat that scroll as "select the next/previous item" and silently
    change the value. Ignoring the wheel event here lets the scroll pass
    through to the settings scroll area instead, while clicking the dropdown
    to open it and choosing an item still works exactly as before, and so
    does keyboard navigation.
    """
    def wheelEvent(self, event):
        event.ignore()


class AppSettingsDialog(QDialog):
    """Application-wide interface preferences: scale, theme and language."""
    def __init__(self, settings: QSettings, parent=None, language="en"):
        super().__init__(parent)
        self.settings = settings
        self.reset_requested = False
        self.language = "ar" if str(language).lower() == "ar" else "en"
        self.setObjectName("appSettingsDialog")
        self.setLayoutDirection(Qt.LayoutDirection.RightToLeft if self.language == "ar" else Qt.LayoutDirection.LeftToRight)
        self.setWindowTitle("إعدادات البرنامج" if self.language == "ar" else "Engo · Application settings")
        self.setModal(True)
        self.setMinimumSize(520, 560)
        screen = QApplication.primaryScreen()
        available = screen.availableGeometry() if screen else QRect(0, 0, 1200, 900)
        self.resize(min(640, max(540, available.width() - 100)), min(700, max(600, available.height() - 90)))

        is_ar = self.language == "ar"
        root = QVBoxLayout(self)
        root.setContentsMargins(16, 16, 16, 14)
        root.setSpacing(12)

        # Hero header gives the window a clear identity and hierarchy.
        hero = QFrame(self)
        hero.setObjectName("settingsHero")
        hero_layout = QHBoxLayout(hero)
        hero_layout.setContentsMargins(16, 14, 16, 14)
        hero_layout.setSpacing(12)
        hero_mark = QLabel("✦")
        hero_mark.setObjectName("settingsHeroMark")
        hero_mark.setAlignment(Qt.AlignmentFlag.AlignCenter)
        hero_mark.setFixedSize(42, 42)
        hero_copy = QVBoxLayout()
        hero_copy.setSpacing(3)
        eyebrow = QLabel("ENGO")
        eyebrow.setObjectName("settingsEyebrow")
        hero_title = QLabel("خصّص تجربة Engo" if is_ar else "Personalize Engo")
        hero_title.setObjectName("settingsHeroTitle")
        hero_subtitle = QLabel(
            "تحكّم في مظهر البرنامج واللغة ووضوح النصوص." if is_ar
            else "Fine-tune the interface, language and reading comfort."
        )
        hero_subtitle.setObjectName("settingsHeroSubtitle")
        hero_subtitle.setWordWrap(True)
        hero_copy.addWidget(eyebrow)
        hero_copy.addWidget(hero_title)
        hero_copy.addWidget(hero_subtitle)
        hero_layout.addWidget(hero_mark, 0, Qt.AlignmentFlag.AlignVCenter)
        hero_layout.addLayout(hero_copy, 1)
        root.addWidget(hero)

        scroll = QScrollArea(self)
        scroll.setObjectName("settingsScroll")
        scroll.setWidgetResizable(True)
        scroll.setFrameShape(QFrame.Shape.NoFrame)
        scroll.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        scroll.setVerticalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAsNeeded)
        scroll.viewport().setObjectName("settingsViewport")
        content = QWidget()
        content.setObjectName("settingsContent")
        content_layout = QVBoxLayout(content)
        content_layout.setContentsMargins(2, 2, 5, 2)
        content_layout.setSpacing(10)

        def section(title_text, caption_text=None):
            card = QFrame(content)
            card.setObjectName("settingsCard")
            card_layout = QVBoxLayout(card)
            card_layout.setContentsMargins(14, 12, 14, 12)
            card_layout.setSpacing(8)
            header = QVBoxLayout()
            header.setSpacing(2)
            title_label = QLabel(title_text)
            title_label.setObjectName("settingsSectionTitle")
            header.addWidget(title_label)
            if caption_text:
                caption = QLabel(caption_text)
                caption.setObjectName("settingsSectionCaption")
                caption.setWordWrap(True)
                header.addWidget(caption)
            card_layout.addLayout(header)
            content_layout.addWidget(card)
            return card_layout

        def field_row(layout, label_text, combo):
            row = QFrame()
            row.setObjectName("settingsFieldRow")
            row_layout = QHBoxLayout(row)
            row_layout.setContentsMargins(2, 7, 2, 7)
            row_layout.setSpacing(14)
            label = QLabel(label_text)
            label.setObjectName("settingsFieldLabel")
            label.setMinimumWidth(145)
            label.setSizePolicy(QSizePolicy.Policy.Expanding, QSizePolicy.Policy.Preferred)
            combo.setObjectName("settingsCombo")
            combo.setMinimumHeight(36)
            combo.setMinimumWidth(190)
            combo.setSizePolicy(QSizePolicy.Policy.Expanding, QSizePolicy.Policy.Fixed)
            row_layout.addWidget(label, 1)
            row_layout.addWidget(combo, 1)
            layout.addWidget(row)

        def slider_row(layout, label_text, combo, values, suffix, low_text=None, high_text=None):
            """Show a dotted, discrete slider while retaining the combo as the saved-value bridge."""
            row = QFrame()
            row.setObjectName("settingsFieldRow")
            row_layout = QHBoxLayout(row)
            row_layout.setContentsMargins(2, 7, 2, 7)
            row_layout.setSpacing(14)
            label = QLabel(label_text)
            label.setObjectName("settingsFieldLabel")
            label.setMinimumWidth(145)
            label.setSizePolicy(QSizePolicy.Policy.Expanding, QSizePolicy.Policy.Preferred)

            control = QWidget(row)
            control_layout = QVBoxLayout(control)
            control_layout.setContentsMargins(0, 0, 0, 0)
            control_layout.setSpacing(0)
            slider_line = QHBoxLayout()
            slider_line.setContentsMargins(0, 0, 0, 0)
            slider_line.setSpacing(10)
            slider_line.setDirection(QBoxLayout.Direction.LeftToRight)
            slider = _SettingsNoWheelSlider(Qt.Orientation.Horizontal, control)
            slider.setObjectName("settingsSlider")
            # Keep the slider widget and the fixed endpoint labels in their
            # existing physical positions. Only invert the slider's visual/value
            # travel for Arabic: the accent then starts at the RIGHT and grows
            # toward the LEFT as the selected value increases. English remains
            # the normal left-to-right progression. The endpoint labels below
            # are deliberately not reordered or moved.
            slider.setLayoutDirection(Qt.LayoutDirection.LeftToRight)
            slider.setInvertedAppearance(is_ar)
            slider.setInvertedControls(False)
            slider.setRange(0, max(0, len(values) - 1))
            slider.setSingleStep(1)
            slider.setPageStep(1)
            slider.setTickInterval(1)
            slider.setTickPosition(QSlider.TickPosition.TicksBelow)
            slider.setTracking(True)
            slider.setMinimumHeight(32)
            slider.setSizePolicy(QSizePolicy.Policy.Expanding, QSizePolicy.Policy.Fixed)
            value_label = QLabel(control)
            value_label.setObjectName("settingsSliderValue")
            value_label.setAlignment(Qt.AlignmentFlag.AlignCenter)
            value_label.setMinimumWidth(62)
            value_label.setSizePolicy(QSizePolicy.Policy.Fixed, QSizePolicy.Policy.Fixed)
            slider_line.addWidget(slider, 1)
            slider_line.addWidget(value_label, 0)
            control_layout.addLayout(slider_line)

            endpoints = QHBoxLayout()
            endpoints.setContentsMargins(2, 0, 2, 0)
            endpoints.setSpacing(4)
            endpoints.setDirection(QBoxLayout.Direction.LeftToRight)
            # Keep endpoint labels in their original physical positions; they
            # are not reordered when the Arabic accent-page colors are swapped.
            high_label = QLabel(str(high_text if high_text is not None else values[-1]) + suffix)
            low_label = QLabel(str(low_text if low_text is not None else values[0]) + suffix)
            for endpoint in (low_label, high_label):
                endpoint.setObjectName("settingsSliderRangeLabel")
            # Physical order intentionally remains unchanged in both languages.
            endpoints.addWidget(low_label)
            endpoints.addStretch(1)
            endpoints.addWidget(high_label)
            control_layout.addLayout(endpoints)

            # Keep the old combo objects as an internal compatibility layer for
            # settings persistence and other code that expects currentData().
            combo.setObjectName("settingsCombo")
            combo.setParent(self)
            combo.hide()
            current_index = combo.currentIndex()
            slider.setValue(max(0, min(slider.maximum(), current_index)))

            def update_value(index):
                index = max(0, min(len(values) - 1, int(index)))
                shown = f"{values[index]}{suffix}"
                value_label.setText(shown)
                if combo.currentIndex() != index:
                    combo.setCurrentIndex(index)

            def sync_from_combo(index):
                index = max(0, min(slider.maximum(), int(index)))
                if slider.value() != index:
                    slider.setValue(index)
                update_value(index)

            slider.valueChanged.connect(update_value)
            combo.currentIndexChanged.connect(sync_from_combo)
            update_value(slider.value())

            row_layout.addWidget(label, 1)
            row_layout.addWidget(control, 2)
            layout.addWidget(row)
            # Keep a reference to prevent the slider from being garbage-collected
            # and make it easy to inspect or extend later.
            return slider

        appearance_title = "المظهر" if is_ar else "Appearance"
        appearance_caption = ("اضبط كثافة الواجهة والثيم العام للبرنامج. لن يُطبَّق اختيار الثيم إلا بعد الضغط على حفظ التغييرات." if is_ar
                              else "Choose the interface density and overall app theme. Theme changes apply only after you click Save changes.")
        appearance = section(appearance_title, appearance_caption)

        self.scale_combo = QComboBox()
        scale_options = [
            ("90% · مضغوط", "0.90"), ("100% · افتراضي", "1.00"),
            ("110%", "1.10"), ("125%", "1.25"), ("150% · كبير", "1.50")
        ] if is_ar else [
            ("90% · Compact", "0.90"), ("100% · Default", "1.00"),
            ("110%", "1.10"), ("125%", "1.25"), ("150% · Large", "1.50")
        ]
        for label, value in scale_options:
            self.scale_combo.addItem(label, value)
        saved_scale = str(settings.value("ui_scale", "1.00", type=str) or "1.00")
        self.scale_combo.setCurrentIndex(max(0, self.scale_combo.findData(saved_scale)))
        self.scale_slider = slider_row(
            appearance, "حجم الواجهة" if is_ar else "Interface scale", self.scale_combo,
            ["90", "100", "110", "125", "150"], "%", "90", "150"
        )

        self.theme_combo = QComboBox(self)  # retained as the stable settings-value interface
        theme_options = [
            (("داكن" if is_ar else "Dark"), "dark"),
            (("منتصف الليل" if is_ar else "Midnight"), "midnight"),
            (("فاتح" if is_ar else "Light"), "light"),
            ( ("عشبي" if is_ar else "Grass"), "grass"),
            ( ("وردي" if is_ar else "Pink"), "pink"),
            ( ("برتقالي" if is_ar else "Orange"), "orange"),
        ]
        for label, value in theme_options:
            self.theme_combo.addItem(label, value)
        saved_theme = normalize_ui_theme(settings.value("ui_theme", "dark", type=str))
        self.theme_combo.setCurrentIndex(max(0, self.theme_combo.findData(saved_theme)))
        self.theme_combo.hide()
        theme_picker = QFrame(content)
        theme_picker.setObjectName("settingsThemePicker")
        theme_picker_layout = QVBoxLayout(theme_picker)
        theme_picker_layout.setContentsMargins(2, 7, 2, 4)
        theme_picker_layout.setSpacing(7)
        theme_picker_label = QLabel("معاينة الثيم" if is_ar else "Theme preview")
        theme_picker_label.setObjectName("settingsFieldLabel")
        theme_picker_layout.addWidget(theme_picker_label)
        theme_cards_layout = QGridLayout()
        theme_cards_layout.setContentsMargins(0, 0, 0, 0)
        theme_cards_layout.setHorizontalSpacing(8)
        theme_cards_layout.setVerticalSpacing(8)
        self.theme_card_group = QButtonGroup(self)
        self.theme_card_group.setExclusive(True)
        self.theme_card_buttons = {}
        theme_card_labels = {
            "light": "فاتح" if is_ar else "Light",
            "dark": "داكن" if is_ar else "Dark",
            "midnight": "منتصف الليل" if is_ar else "Midnight",
            "grass": "عشبي" if is_ar else "Grass",
            "pink": "وردي" if is_ar else "Pink",
            "orange": "برتقالي" if is_ar else "Orange",
        }
        for position, theme_value in enumerate(("light", "dark", "midnight", "grass", "pink", "orange")):
            theme_card = ThemePreviewButton(theme_value, theme_card_labels[theme_value], theme_picker, QSize(132, 73))
            theme_card.clicked.connect(lambda _checked=False, value=theme_value: self._select_theme_card(value))
            self.theme_card_group.addButton(theme_card)
            self.theme_card_buttons[theme_value] = theme_card
            theme_cards_layout.addWidget(theme_card, position // 3, position % 3)
        for column in range(3):
            theme_cards_layout.setColumnStretch(column, 1)
        theme_picker_layout.addLayout(theme_cards_layout)
        appearance.addWidget(theme_picker)
        self._sync_theme_card_selection()
        self.theme_combo.currentIndexChanged.connect(self._on_theme_selection_changed)

        language = section(
            "اللغة" if is_ar else "Language",
            "لغة عناصر Engo والقوائم والنوافذ الأساسية." if is_ar else "Language used across the main Engo interface and common dialogs."
        )
        self.language_combo = _SettingsNoWheelComboBox()
        self.language_combo.addItem("الإنجليزية" if is_ar else "English", "en")
        self.language_combo.addItem("العربية", "ar")
        saved_language = str(settings.value("interface_language", "en", type=str) or "en")
        self.language_combo.setCurrentIndex(max(0, self.language_combo.findData(saved_language)))
        field_row(language, "لغة الواجهة" if is_ar else "Interface language", self.language_combo)

        typography = section(
            "الخطوط والقراءة" if is_ar else "Typography & reading",
            "اختَر حجمًا مريحًا لكل نوع من النصوص بشكل مستقل." if is_ar else "Set comfortable text sizes independently for chat, typing and translation."
        )

        def font_combo(setting_key, default, sizes):
            combo = _SettingsNoWheelComboBox()
            for size in sizes:
                combo.addItem(f"{size} pt", str(size))
            saved = str(settings.value(setting_key, default, type=str) or default)
            combo.setCurrentIndex(max(0, combo.findData(saved)))
            return combo

        chat_sizes = [10, 11, 12, 13, 14, 15, 16, 18]
        self.chat_font_combo = font_combo("ui_chat_font_pt", "13", chat_sizes)
        self.chat_font_slider = slider_row(
            typography, "حجم خط رسائل الشات" if is_ar else "Chat message font",
            self.chat_font_combo, chat_sizes, " pt", str(chat_sizes[0]), str(chat_sizes[-1])
        )
        typing_sizes = [10, 11, 12, 13, 14, 15, 16, 18]
        self.typing_font_combo = font_combo("ui_typing_font_pt", "12", typing_sizes)
        self.typing_font_slider = slider_row(
            typography, "حجم خط الكتابة" if is_ar else "Typing / composer font",
            self.typing_font_combo, typing_sizes, " pt", str(typing_sizes[0]), str(typing_sizes[-1])
        )
        translation_sizes = [10, 11, 12, 13, 14, 15, 16, 18, 20, 22]
        self.translation_font_combo = font_combo("ui_translation_font_pt", "13", translation_sizes)
        self.translation_font_slider = slider_row(
            typography, "حجم خط الترجمة" if is_ar else "Translation font",
            self.translation_font_combo, translation_sizes, " pt", str(translation_sizes[0]), str(translation_sizes[-1])
        )

        note = QFrame(content)
        note.setObjectName("settingsNotice")
        note_layout = QHBoxLayout(note)
        note_layout.setContentsMargins(12, 10, 12, 10)
        note_layout.setSpacing(9)
        note_icon = QLabel("i")
        note_icon.setObjectName("settingsNoticeIcon")
        note_icon.setAlignment(Qt.AlignmentFlag.AlignCenter)
        note_icon.setFixedSize(22, 22)
        note_text = QLabel(
            "تؤثر هذه التفضيلات على واجهة Engo فقط، ولا تغيّر مظهر صفحات PDF. قد تظل بعض رسائل مزوّدي الخدمة المتخصصة باللغة الإنجليزية."
            if is_ar else
            "These preferences affect the Engo interface, not PDF page appearance. Some specialist provider messages may remain in English."
        )
        note_text.setObjectName("settingsNoticeText")
        note_text.setWordWrap(True)
        note_layout.addWidget(note_icon, 0, Qt.AlignmentFlag.AlignTop)
        note_layout.addWidget(note_text, 1)
        content_layout.addWidget(note)

        maintenance = section(
            "البيانات والصيانة" if is_ar else "Data & maintenance",
            "امسح الملفات المؤقتة أو احذف المحادثات أو أعد Engo إلى إعداداته الافتراضية." if is_ar
            else "Clean temporary files, remove saved conversations or restore Engo's default settings."
        )

        def maintenance_action(title_text, caption_text, button_text, object_name, callback):
            row = QFrame(content)
            row.setObjectName("settingsMaintenanceRow")
            row_layout = QHBoxLayout(row)
            row_layout.setContentsMargins(2, 7, 2, 7)
            row_layout.setSpacing(12)
            text_column = QVBoxLayout()
            text_column.setSpacing(2)
            title_label = QLabel(title_text)
            title_label.setObjectName("settingsMaintenanceTitle")
            caption_label = QLabel(caption_text)
            caption_label.setObjectName("settingsMaintenanceCaption")
            caption_label.setWordWrap(True)
            text_column.addWidget(title_label)
            text_column.addWidget(caption_label)
            row_layout.addLayout(text_column, 1)
            action_button = QPushButton(button_text)
            action_button.setObjectName(object_name)
            action_button.setMinimumSize(114, 32)
            action_button.setCursor(Qt.CursorShape.PointingHandCursor)
            action_button.clicked.connect(callback)
            row_layout.addWidget(action_button, 0, Qt.AlignmentFlag.AlignVCenter)
            maintenance.addWidget(row)
            return action_button

        maintenance_action(
            "إعدادات الذكاء الاصطناعي" if is_ar else "AI settings",
            "إدارة مزوّدي الذكاء الاصطناعي ومفاتيح API والنماذج وإعدادات الصوت والترجمة." if is_ar
            else "Manage AI providers, API keys, model IDs, voice and translation preferences.",
            "Ai فتح اعدادات" if is_ar else "Open AI settings",
            "settingsMaintenanceButton", self._open_ai_settings_action
        )

        maintenance_action(
            "مسح الكاش" if is_ar else "Clear cache",
            "يحذف صور المعاينة والملفات المؤقتة وبيانات النماذج المخزّنة فقط. لا يحذف المحادثات أو ملفاتك." if is_ar
            else "Removes cached previews, temporary files and cached model lists only. Your chats and documents stay untouched.",
            "مسح الكاش" if is_ar else "Clear cache",
            "settingsMaintenanceButton", self._clear_cache_action
        )
        maintenance_action(
            "حذف كل المحادثات" if is_ar else "Delete all conversations",
            "يحذف المحادثات المحفوظة في كل ملفات PDF وصور المرفقات الخاصة بها نهائيًا." if is_ar
            else "Permanently deletes saved chats across all PDFs and the images attached to those chats.",
            "حذف المحادثات" if is_ar else "Delete chats",
            "settingsDangerButton", self._delete_chats_action
        )
        maintenance_action(
            "إعادة ضبط البرنامج" if is_ar else "Reset application",
            "يعيد التفضيلات للوضع الافتراضي ويحذف مفاتيح API المحفوظة. تبقى المحادثات ولوحات الشرح وملفات PDF كما هي." if is_ar
            else "Restores default preferences and removes saved API keys. Conversations, lesson boards and PDFs are kept.",
            "إعادة ضبط" if is_ar else "Reset Engo",
            "settingsResetButton", self._reset_program_action
        )

        content_layout.addStretch(1)
        scroll.setWidget(content)
        root.addWidget(scroll, 1)

        footer = QFrame(self)
        footer.setObjectName("settingsFooter")
        footer_layout = QHBoxLayout(footer)
        footer_layout.setContentsMargins(0, 8, 0, 0)
        footer_layout.setSpacing(8)
        footer_layout.addStretch(1)
        buttons = QDialogButtonBox(QDialogButtonBox.StandardButton.Cancel | QDialogButtonBox.StandardButton.Save)
        cancel_button = buttons.button(QDialogButtonBox.StandardButton.Cancel)
        save_button = buttons.button(QDialogButtonBox.StandardButton.Save)
        cancel_button.setText("إلغاء" if is_ar else "Cancel")
        save_button.setText("حفظ التغييرات" if is_ar else "Save changes")
        save_button.setObjectName("settingsSave")
        cancel_button.setObjectName("settingsCancel")
        buttons.accepted.connect(self.accept)
        buttons.rejected.connect(self.reject)
        footer_layout.addWidget(buttons)
        root.addWidget(footer)

        # Dialog styling is local and palette-aware, so it remains polished in all
        # five app themes without changing the rest of the window stylesheet.
        try:
            settings.sync()
        except Exception:
            pass
        active_theme = normalize_ui_theme(settings.value("ui_theme", "dark", type=str))
        colors = self._theme_style_colors(active_theme)
        c = colors
        # Apply the same theme to native Windows controls and combo popup views;
        # QSS alone can leave light system surfaces inside a dark dialog.
        dialog_palette = QPalette(self.palette())
        for role, color_key in (
            (QPalette.ColorRole.Window, "bg"),
            (QPalette.ColorRole.WindowText, "text"),
            (QPalette.ColorRole.Base, "input"),
            (QPalette.ColorRole.AlternateBase, "card"),
            (QPalette.ColorRole.Text, "text"),
            (QPalette.ColorRole.Button, "card"),
            (QPalette.ColorRole.ButtonText, "text"),
            (QPalette.ColorRole.Highlight, "accent"),
        ):
            dialog_palette.setColor(role, QColor(c[color_key]))
        dialog_palette.setColor(QPalette.ColorRole.HighlightedText, QColor("#ffffff"))
        dialog_palette.setColor(QPalette.ColorRole.PlaceholderText, QColor(c["muted"]))
        dialog_palette.setColor(QPalette.ColorRole.ToolTipBase, QColor(c["card"]))
        dialog_palette.setColor(QPalette.ColorRole.ToolTipText, QColor(c["text"]))
        self.setPalette(dialog_palette)
        self.setAutoFillBackground(True)
        for themed_widget in self.findChildren(QWidget):
            themed_widget.setPalette(dialog_palette)
            if isinstance(themed_widget, QLabel):
                themed_widget.setAutoFillBackground(False)
                themed_widget.setAttribute(Qt.WidgetAttribute.WA_StyledBackground, False)
            elif isinstance(themed_widget, (QFrame, QScrollArea)):
                themed_widget.setAutoFillBackground(True)
        for themed_widget in (hero, scroll, scroll.viewport(), content, footer, buttons):
            themed_widget.setPalette(dialog_palette)
        self.setAttribute(Qt.WidgetAttribute.WA_StyledBackground, True)
        scroll.setAttribute(Qt.WidgetAttribute.WA_StyledBackground, True)
        scroll.viewport().setAttribute(Qt.WidgetAttribute.WA_StyledBackground, True)
        scroll.viewport().setAutoFillBackground(True)
        content.setAttribute(Qt.WidgetAttribute.WA_StyledBackground, True)
        content.setAutoFillBackground(True)
        self.setStyleSheet(self._build_theme_stylesheet(c, self.language))
        # Re-apply the shared native palette after the local stylesheet is ready.
        _engo_apply_dialog_consistency(self, active_theme, is_ar)
        self._active_theme = active_theme
        self._base_theme_stylesheet = self.styleSheet()
        self._base_theme_colors = dict(colors)

    def _open_ai_settings_action(self):
        main_window = self.parent()
        opener = getattr(main_window, "open_ai_provider_settings", None)
        if callable(opener):
            opener(self)

    @staticmethod
    def _build_theme_stylesheet(c, language="en"):
        is_ar = str(language).lower().startswith("ar")
        # Arabic keeps the slider's already-correct right-to-left numeric travel,
        # but the accent segment is painted on the opposite Qt page portion.
        # Swap only the two page colors: values, handle travel, and the fixed
        # endpoint labels remain untouched.
        slider_sub_page = c["border"] if is_ar else c["accent"]
        slider_add_page = c["accent"] if is_ar else c["border"]
        return f"""
            QDialog#appSettingsDialog {{ background: {c['bg']}; color: {c['text']}; }}
            QDialog#appSettingsDialog QLabel {{ background: transparent; color: {c['text']}; }}
            QFrame#settingsHero {{ background:transparent; border:0; border-radius:0; }}
            QLabel#settingsHeroMark {{ color:{c['accent']}; background:transparent; border:0; border-radius:0; font-size:21pt; font-weight:800; }}
            QLabel#settingsEyebrow {{ color:{c['accent']}; font-size:7pt; font-weight:800; letter-spacing:1.2px; }}
            QLabel#settingsHeroTitle {{ color:{c['text']}; font-size:16pt; font-weight:800; }}
            QLabel#settingsHeroSubtitle {{ color:{c['muted']}; font-size:8.5pt; }}
            QScrollArea#settingsScroll, QWidget#settingsContent {{ background:transparent; border:0; }}
            QFrame#settingsCard {{ background:transparent; border:0; border-radius:0; }}
            QLabel#settingsSectionTitle {{ color:{c['text']}; font-size:10pt; font-weight:800; }}
            QLabel#settingsSectionCaption {{ color:{c['muted']}; font-size:8pt; }}
            QFrame#settingsFieldRow {{ background:transparent; border:0; }}
            QLabel#settingsFieldLabel {{ color:{c['text']}; font-size:8.5pt; font-weight:650; }}
            QComboBox#settingsCombo {{ background:{c['input']}; color:{c['text']}; border:1px solid {c['border']}; border-radius:8px; padding:5px 30px 5px 10px; min-height:26px; selection-background-color:{c['accent']}; }}
            QComboBox#settingsCombo:hover {{ background:{c['hover']}; border-color:{c['accent']}; }}
            QComboBox#settingsCombo:focus {{ border:1px solid {c['accent']}; }}
            QSlider#settingsSlider {{ background:transparent; min-height:28px; }}
            QSlider#settingsSlider::groove:horizontal {{ height:5px; background:{c['border']}; border:0; border-radius:2px; }}
            QSlider#settingsSlider::sub-page:horizontal {{ background:{slider_sub_page}; border-radius:2px; }}
            QSlider#settingsSlider::add-page:horizontal {{ background:{slider_add_page}; border-radius:2px; }}
            QSlider#settingsSlider::handle:horizontal {{ background:{c['accent']}; border:2px solid {c['bg']}; width:15px; height:15px; margin:-6px 0; border-radius:8px; }}
            QSlider#settingsSlider::handle:horizontal:hover {{ background:{c['accent_hover']}; }}
            QSlider#settingsSlider::tick-mark {{ background:{c['muted']}; width:2px; height:5px; }}
            QLabel#settingsSliderValue {{ background:{c['accent_soft']}; color:{c['text']}; border:1px solid {c['border']}; border-radius:7px; padding:3px 7px; font-weight:800; }}
            QLabel#settingsSliderRangeLabel {{ background:transparent; color:{c['muted']}; border:0; padding:0; font-size:7.2pt; }}
            QToolButton#themePreviewCard {{ background:{c['field']}; color:{c['text']}; border:1px solid {c['border']}; border-radius:10px; padding:6px; font-size:8.5pt; font-weight:800; }}
            QToolButton#themePreviewCard:hover {{ background:{c['hover']}; border-color:{c['accent']}; }}
            QToolButton#themePreviewCard:checked {{ background:{c['accent_soft']}; color:{c['text']}; border:2px solid {c['accent']}; }}
            QComboBox#settingsCombo::drop-down {{ subcontrol-origin:padding; subcontrol-position:top right; width:27px; border-left:1px solid {c['border']}; border-top-right-radius:8px; border-bottom-right-radius:8px; background:{c['input']}; }}
            QComboBox#settingsCombo::down-arrow {{ image:url("{c['combo_arrow']}"); width:12px; height:8px; border:0; }}
            QComboBox#settingsCombo QAbstractItemView {{ background:{c['input']}; color:{c['text']}; border:1px solid {c['border']}; outline:0; padding:4px; selection-background-color:{c['accent_soft']}; selection-color:{c['text']}; }}
            QDialog#appSettingsDialog QWidget#settingsViewport, QDialog#appSettingsDialog QWidget#settingsContent {{ background:{c['bg']}; color:{c['text']}; }}
            QDialog#appSettingsDialog QAbstractItemView {{ background:{c['input']}; color:{c['text']}; selection-background-color:{c['accent_soft']}; selection-color:{c['text']}; outline:0; }}
            QDialog#appSettingsDialog QToolTip {{ background:{c['card']}; color:{c['text']}; border:1px solid {c['border']}; padding:5px 7px; }}
            QFrame#settingsNotice {{ background:transparent; border:0; border-radius:0; }}
            QLabel#settingsNoticeIcon {{ background:transparent; color:{c['accent']}; border:0; border-radius:0; font-weight:800; font-size:9pt; }}
            QLabel#settingsNoticeText {{ color:{c['muted']}; font-size:7.8pt; }}
            QFrame#settingsMaintenanceRow {{ background:transparent; border:0; }}
            QLabel#settingsMaintenanceTitle {{ color:{c['text']}; font-size:9pt; font-weight:750; }}
            QLabel#settingsMaintenanceCaption {{ color:{c['muted']}; font-size:7.7pt; }}
            QPushButton#settingsMaintenanceButton {{ background:{c['accent_soft']}; color:{c['text']}; border:1px solid {c['border']}; border-radius:8px; padding:4px 10px; font-weight:700; }}
            QPushButton#settingsMaintenanceButton:hover {{ background:{c['hover']}; border-color:{c['accent']}; }}
            QPushButton#settingsDangerButton {{ background:{c['danger_soft']}; color:{c['danger']}; border:1px solid {c['danger_border']}; border-radius:8px; padding:4px 10px; font-weight:700; }}
            QPushButton#settingsDangerButton:hover {{ background:{c['danger_soft']}; border-color:{c['danger']}; }}
            QPushButton#settingsResetButton {{ background:{c['danger']}; color:#ffffff; border:1px solid {c['danger']}; border-radius:8px; padding:4px 10px; font-weight:750; }}
            QPushButton#settingsResetButton:hover {{ background:{c['danger']}; border-color:{c['danger']}; }}
            QFrame#settingsFooter {{ background:transparent; border:0; }}
            QDialogButtonBox QPushButton {{ min-width:90px; min-height:30px; border-radius:7px; padding:4px 10px; font-weight:700; }}
            QPushButton#settingsCancel {{ background:{c['card']}; color:{c['text']}; border:1px solid {c['border']}; }}
            QPushButton#settingsCancel:hover {{ background:{c['hover']}; border-color:{c['accent']}; }}
            QPushButton#settingsSave {{ background:{c['accent']}; color:#ffffff; border:1px solid {c['accent']}; }}
            QPushButton#settingsSave:hover {{ background:{c['accent']}; border-color:{c['accent']}; }}
            QScrollBar:vertical {{ background:transparent; width:10px; margin:3px 1px; }}
            QScrollBar::handle:vertical {{ background:{c['scroll']}; border-radius:4px; min-height:28px; }}
            QScrollBar::add-line:vertical, QScrollBar::sub-line:vertical {{ height:0; }}
        """

    @staticmethod
    def _theme_style_colors(theme):
        active_theme = normalize_ui_theme(theme)
        t = engo_ui_theme_tokens(active_theme)
        danger = "#c43f4d" if active_theme == "light" else "#e17b89"
        return {
            "bg": t["window"], "hero_a": t["panel_alt"], "hero_b": t["panel"],
            "card": t["panel"], "field": t["input"], "border": t["border"],
            "text": t["text"], "muted": t["muted"], "accent": t["accent"],
            # Keep the settings dialog stylesheet self-contained for every theme.
            # Older/custom token sets may omit accent_hover, so fall back safely.
            "accent_hover": t.get("accent_hover", t["accent"]),
            "accent_soft": t["selection"], "notice": t["panel_alt"],
            "notice_border": t["border_strong"], "input": t["input"],
            "hover": t["hover"], "scroll": t["scrollbar"],
            "danger": danger,
            "danger_soft": {
                "light": "#fff0f1", "midnight": "#3c2635", "dark": "#332626",
                "grass": "#26382a", "pink": "#38252d", "orange": "#3b2b1d",
            }.get(active_theme, "#332626"),
            "danger_border": {
                "light": "#e8b9bf", "midnight": "#754153", "dark": "#69444a",
                "grass": "#49634d", "pink": "#70414d", "orange": "#765332",
            }.get(active_theme, "#69444a"),
            "combo_arrow": resource_path("combo_chevron_light.png" if active_theme == "light" else "combo_chevron_dark.png").replace("\\", "/"),
        }

    def apply_theme(self, theme=None):
        """Restyle this already-open settings window from the shared theme tokens."""
        theme = normalize_ui_theme(theme or self.settings.value("ui_theme", "dark", type=str))
        colors = self._theme_style_colors(theme)
        self.setStyleSheet(self._build_theme_stylesheet(colors, self.language))
        _engo_apply_dialog_consistency(self, theme, self.language == "ar")
        self._active_theme = theme

    def _on_theme_selection_changed(self, _index=-1):
        """Update only the selected card; the app theme changes only after Save."""
        self._sync_theme_card_selection()

    def _select_theme_card(self, theme_value):
        index = self.theme_combo.findData(str(theme_value))
        if index >= 0:
            self.theme_combo.setCurrentIndex(index)

    def _sync_theme_card_selection(self):
        selected = str(self.theme_combo.currentData() or "dark")
        for key, button in getattr(self, "theme_card_buttons", {}).items():
            button.setChecked(key == selected)

    @staticmethod
    def _is_path_within(path_value, parent_value):
        try:
            path_text = os.path.normcase(os.path.abspath(str(path_value)))
            parent_text = os.path.normcase(os.path.abspath(str(parent_value)))
            return os.path.commonpath([path_text, parent_text]) == parent_text
        except Exception:
            return False

    @staticmethod
    def _empty_directory_safely(directory, protected_files=None, protected_roots=None):
        """Empty one dedicated cache directory without following symlinks or touching protected data."""
        stats = {"files": 0, "bytes": 0, "skipped": 0, "errors": 0}
        try:
            root = Path(directory)
            if not root.exists() or root.is_symlink() or not root.is_dir():
                return stats
            resolved_root = root.resolve()
            protected_files = {
                os.path.normcase(str(Path(value).resolve(strict=False)))
                for value in (protected_files or set())
            }
            protected_roots = [Path(value).resolve(strict=False) for value in (protected_roots or [])]
            # Refuse obviously unsafe roots, even if a malformed Qt path is returned.
            if resolved_root == Path.home().resolve() or any(resolved_root == item for item in protected_roots):
                stats["skipped"] += 1
                return stats
            for current, directories, filenames in os.walk(str(root), topdown=False, followlinks=False):
                current_path = Path(current)
                for filename in filenames:
                    target = current_path / filename
                    try:
                        resolved_target = target.resolve(strict=False)
                        if os.path.normcase(str(resolved_target)) in protected_files:
                            stats["skipped"] += 1
                            continue
                        if target.is_symlink():
                            target.unlink()
                            stats["files"] += 1
                            continue
                        size = target.stat().st_size
                        target.unlink()
                        stats["files"] += 1
                        stats["bytes"] += max(0, int(size))
                    except FileNotFoundError:
                        continue
                    except Exception:
                        stats["errors"] += 1
                for dirname in directories:
                    target_dir = current_path / dirname
                    try:
                        if target_dir.is_symlink():
                            target_dir.unlink()
                        else:
                            target_dir.rmdir()
                    except OSError:
                        # Non-empty directories contain a locked or protected file.
                        pass
                    except Exception:
                        stats["errors"] += 1
            try:
                root.rmdir()
            except OSError:
                pass
        except Exception:
            stats["errors"] += 1
        return stats

    def _perform_cache_cleanup(self, main_window=None):
        """Remove Engo's disposable disk caches; keep chat and lesson-board stores intact."""
        targets = []
        cache_location = QStandardPaths.writableLocation(QStandardPaths.StandardLocation.CacheLocation)
        if cache_location:
            targets.append(Path(cache_location))
        targets.append(Path.home() / ".engopdfviewer" / "image_cache")
        app_data_location = QStandardPaths.writableLocation(QStandardPaths.StandardLocation.AppDataLocation)
        protected_roots = [Path(app_data_location)] if app_data_location else []

        protected_files = set()
        image_cache_root = Path.home() / ".engopdfviewer" / "image_cache"
        if main_window is not None:
            try:
                for tab in main_window.findChildren(DocumentTab):
                    current_path = str(getattr(tab, "path", "") or "")
                    if current_path and self._is_path_within(current_path, image_cache_root):
                        protected_files.add(current_path)
            except Exception:
                pass

        total = {"files": 0, "bytes": 0, "skipped": 0, "errors": 0}
        seen = set()
        home_root = Path.home().resolve()
        app_data_resolved = Path(app_data_location).resolve() if app_data_location else None
        for target in targets:
            try:
                resolved = target.resolve(strict=False)
                key = os.path.normcase(str(resolved))
                if key in seen:
                    continue
                seen.add(key)
                # CacheLocation must never be allowed to resolve to a parent of AppDataLocation.
                if app_data_resolved is not None and (resolved == app_data_resolved or app_data_resolved.is_relative_to(resolved)):
                    total["skipped"] += 1
                    continue
                if resolved == home_root:
                    total["skipped"] += 1
                    continue
                part = self._empty_directory_safely(target, protected_files, protected_roots)
                for name in total:
                    total[name] += part[name]
            except Exception:
                total["errors"] += 1

        # Remove only explicitly known cache entries from QSettings. Recent files,
        # saved preferences, conversations and lesson-board records are not caches.
        for key in list(self.settings.allKeys()):
            if (key == "tag_usage_cache_json" or key.startswith("ai_available_models_")
                    or key.startswith("handwriting_transcription_cache/")):
                self.settings.remove(key)
        self.settings.sync()

        # Release in-memory render/math caches too, without touching stored chat messages.
        math_cache = globals().get("_MATH_TEXT_CACHE")
        try:
            if math_cache is not None:
                math_cache.clear()
        except Exception:
            pass
        if main_window is not None:
            try:
                for canvas in main_window.findChildren(DocumentCanvas):
                    canvas.clear_cache()
            except Exception:
                pass
            try:
                panel = getattr(main_window, "ai_panel", None)
                if panel is not None:
                    panel._provider_changed(panel.provider_combo.currentIndex())
            except Exception:
                pass
        return total

    def _clear_cache_action(self):
        is_ar = self.language == "ar"
        title = "مسح الكاش" if is_ar else "Clear cache"
        message = (
            "سيتم حذف صور المعاينة والملفات المؤقتة وقوائم الموديلات المخزّنة. لن يتم حذف المحادثات أو صور مرفقاتها أو لوحات الشرح أو ملفات PDF. هل تريد المتابعة؟"
            if is_ar else
            "This removes cached previews, temporary files and cached model lists. Conversations, their attached images, lesson boards and PDFs will not be deleted. Continue?"
        )
        answer = QMessageBox.question(
            self, title, message,
            QMessageBox.StandardButton.Yes | QMessageBox.StandardButton.No,
            QMessageBox.StandardButton.No
        )
        if answer != QMessageBox.StandardButton.Yes:
            return
        stats = self._perform_cache_cleanup(self.parent())
        size_mb = stats["bytes"] / (1024.0 * 1024.0)
        result = (
            f"تم حذف {stats['files']} ملف كاش ({size_mb:.1f} MB)."
            if is_ar else f"Removed {stats['files']} cached file(s) ({size_mb:.1f} MB)."
        )
        if stats["skipped"]:
            result += (f"\nتم الإبقاء على {stats['skipped']} ملف قيد الاستخدام." if is_ar
                       else f"\nKept {stats['skipped']} item(s) currently in use.")
        if stats["errors"]:
            result += (f"\nتعذر حذف {stats['errors']} عنصر." if is_ar
                       else f"\nCould not remove {stats['errors']} item(s).")
        QMessageBox.information(self, title, result)

    def _delete_chats_action(self):
        is_ar = self.language == "ar"
        main_window = self.parent()
        panel = getattr(main_window, "ai_panel", None)
        if panel is None:
            QMessageBox.warning(self, "Engo", "AI chat storage is not available.")
            return
        if bool(getattr(panel, "_busy", False)):
            QMessageBox.information(
                self, "Engo",
                "انتظر انتهاء رد الذكاء الاصطناعي قبل حذف المحادثات." if is_ar
                else "Wait for the current AI response to finish before deleting conversations."
            )
            return
        try:
            count = panel.chat_store.count_all_chats()
        except Exception as exc:
            QMessageBox.warning(self, "Engo", str(exc))
            return
        title = "حذف كل المحادثات" if is_ar else "Delete all conversations"
        message = (
            f"سيتم حذف {count} محادثة من جميع ملفات PDF نهائيًا، بما في ذلك الرسائل وصور المرفقات. لا يمكن التراجع عن ذلك. لن يتم حذف ملفات PDF أو لوحات الشرح أو مفاتيح API. هل تريد المتابعة؟"
            if is_ar else
            f"This permanently deletes {count} conversation(s) across all PDFs, including messages and attached images. This cannot be undone. PDFs, lesson boards and API keys will be kept. Continue?"
        )
        answer = QMessageBox.question(
            self, title, message,
            QMessageBox.StandardButton.Yes | QMessageBox.StandardButton.No,
            QMessageBox.StandardButton.No
        )
        if answer != QMessageBox.StandardButton.Yes:
            return
        try:
            deleted = panel.delete_all_conversations()
            if hasattr(main_window, "show_status"):
                main_window.show_status("All saved conversations deleted")
            QMessageBox.information(
                self, title,
                (f"تم حذف {deleted} محادثة وصور مرفقاتها." if is_ar else
                 f"Deleted {deleted} conversation(s) and their attached images.")
            )
        except Exception as exc:
            QMessageBox.warning(self, title, str(exc))

    def _delete_provider_credentials(self):
        removed, failed = [], []
        try:
            import keyring  # type: ignore
        except Exception:
            return removed, failed
        for provider in AI_PROVIDER_LABELS:
            try:
                existing = keyring.get_password(_provider_key_service(), provider)
                if existing:
                    keyring.delete_password(_provider_key_service(), provider)
                    removed.append(provider)
            except Exception:
                failed.append(provider)
        return removed, failed

    def _reset_program_action(self):
        """Request a full reset, then let MainWindow close and relaunch cleanly."""
        is_ar = self.language == "ar"
        title = "إعادة ضبط Engo" if is_ar else "Reset Engo"
        message = (
            "سيتم إغلاق Engo وإعادة تشغيله من البداية، وستظهر شاشات الترحيب لاختيار اللغة والثيم كأنك تستخدم البرنامج لأول مرة.\n\n"
            "سيتم مسح إعدادات البرنامج والملفات الأخيرة والجلسة المحفوظة ومفاتيح API.\n\n"
            "ستظل ملفات PDF وتعليقاتها والمحادثات ومرفقاتها ولوحات الشرح محفوظة ولن يتم حذفها.\n\n"
            "هل تريد المتابعة؟"
            if is_ar else
            "Engo will close and restart from the beginning. The welcome setup will appear so you can choose the interface language and theme as if you were using the app for the first time.\n\n"
            "Application preferences, recent-file history, the saved session and API keys will be cleared.\n\n"
            "Your PDFs and annotations, conversations and attachments, and lesson boards will be preserved.\n\n"
            "Continue with Reset Engo?"
        )
        answer = QMessageBox.question(
            self, title, message,
            QMessageBox.StandardButton.Yes | QMessageBox.StandardButton.No,
            QMessageBox.StandardButton.No
        )
        if answer != QMessageBox.StandardButton.Yes:
            return

        # Do not mutate settings here. The owning MainWindow must first close all
        # windows cleanly (including any save/stop-task prompts), then clear QSettings
        # and relaunch so startup detects an empty profile and opens FirstRunSetupDialog.
        self.reset_requested = True
        self.accept()

    def values(self):
        return {"ui_scale": str(self.scale_combo.currentData() or "1.00"),
                "ui_theme": str(self.theme_combo.currentData() or "dark"),
                "interface_language": str(self.language_combo.currentData() or "en"),
                "ui_chat_font_pt": str(self.chat_font_combo.currentData() or "13"),
                "ui_typing_font_pt": str(self.typing_font_combo.currentData() or "12"),
                "ui_translation_font_pt": str(self.translation_font_combo.currentData() or "13")}
