# Auto-split from main.py (verbatim move; do not reformat).
from __future__ import annotations

import math
import os
import json
import io
import uuid
import hashlib
import re
import html as html_module
from pathlib import Path
from PIL import Image, ImageOps, ImageChops, ImageFilter
from PyQt6.QtCore import QObject, Qt, QSize, QSizeF, QRect, QRectF, QPoint, QPointF, QEvent, QTimer, QPropertyAnimation, QParallelAnimationGroup, QVariantAnimation, QEasingCurve, QSettings, QUrl, QThread, QRunnable, QThreadPool, QMarginsF, QStandardPaths, QDir, pyqtSignal, QBuffer, QByteArray, QIODevice, QMimeData, QSignalBlocker
from PyQt6.QtGui import QColor, QPalette, QImage, QPixmap, QIcon, QFileSystemModel, QPainter, QPen, QBrush, QKeySequence, QShortcut, QAction, QCursor, QPolygonF, QPainterPath, QPainterPathStroker, QDesktopServices, QPdfWriter, QPageSize, QTextDocument, QTextCursor, QTextOption, QFont, QDrag, QContextMenuEvent, QMouseEvent
from PyQt6.QtWidgets import (
    QApplication, QMainWindow, QWidget, QFrame, QLabel, QPushButton, QToolButton, QBoxLayout,
    QCheckBox, QColorDialog, QFileDialog, QHBoxLayout, QVBoxLayout, QScrollArea, QAbstractScrollArea,
    QListWidget, QListWidgetItem, QListView, QAbstractItemView, QTreeWidget, QTreeWidgetItem, QTreeView, QSpinBox,
    QSizePolicy, QStatusBar, QMessageBox, QSplitter, QTabWidget, QDialog,
    QDialogButtonBox, QInputDialog, QButtonGroup, QLineEdit, QStackedWidget, QTabBar, QMenu, QComboBox,
    QTextBrowser, QTextEdit, QProgressBar, QGridLayout, QStyledItemDelegate, QStyle, QSlider, QWidgetAction, QToolTip, QGraphicsOpacityEffect
)

from engo_ai_core import (
    AIChatStore,
    AI_DEFAULT_MODELS,
    AI_PROVIDER_LABELS,
)
from engo_base import (
    APP_NAME,
    _engo_apply_menu_consistency,
    _engo_menu_colors,
    _engo_translate_tooltip,
    engo_ui_theme_tokens,
    is_office_document,
    normalize_ui_theme,
)
from engo_markdown import (
    _set_markdown_browser,
    _set_markdown_document,
)
from engo_widgets import (
    MotionButton,
    _engo_file_dialog,
    make_icon,
)



class AIChatMessageBrowser(QTextBrowser):
    """Selectable message text with a contextual action and drag-edge autoscroll."""
    selectionQuestionRequested = pyqtSignal(str)
    _EDGE_ZONE = 42
    _AUTO_SCROLL_INTERVAL_MS = 24

    def __init__(self, parent=None):
        super().__init__(parent)
        self._selection_dragging = False
        self._selection_scroll_area = None
        self._selection_scroll_direction = 0
        self._selection_scroll_timer = QTimer(self)
        self._selection_scroll_timer.setInterval(self._AUTO_SCROLL_INTERVAL_MS)
        self._selection_scroll_timer.timeout.connect(self._auto_scroll_selection_tick)
        self.ask_selection_btn = QToolButton(self)
        self.ask_selection_btn.setObjectName("chatSelectionAsk")
        self._interface_language = "en"
        self.ask_selection_btn.setText("Ask about selection")
        self.ask_selection_btn.setToolTip("Add selected text to a new question in the same conversation")
        self.ask_selection_btn.setCursor(Qt.CursorShape.PointingHandCursor)
        self.ask_selection_btn.setFixedHeight(27)
        self.ask_selection_btn.clicked.connect(self._ask_about_selection)
        self.ask_selection_btn.hide()
        self.selectionChanged.connect(lambda: QTimer.singleShot(0, self._update_selection_ask_button))

    def apply_language(self, language=None):
        """Localize the floating selection action using the active interface language."""
        value = str(language or self._interface_language or "en").strip().lower()
        self._interface_language = "ar" if value.startswith("ar") else "en"
        is_ar = self._interface_language == "ar"
        self.ask_selection_btn.setText("اسأل عن المحدد" if is_ar else "Ask about selection")
        self.ask_selection_btn.setToolTip(
            "إضافة النص المحدد إلى سؤال جديد في نفس المحادثة"
            if is_ar else
            "Add selected text to a new question in the same conversation"
        )
        self.ask_selection_btn.setLayoutDirection(
            Qt.LayoutDirection.RightToLeft if is_ar else Qt.LayoutDirection.LeftToRight
        )
        if self.ask_selection_btn.isVisible():
            self.ask_selection_btn.adjustSize()
            cursor_rect = self.cursorRect(self.textCursor())
            x = max(6, min(self.width() - self.ask_selection_btn.width() - 8, cursor_rect.left()))
            y = max(4, cursor_rect.top() - 31)
            self.ask_selection_btn.move(x, y)

    def _ask_about_selection(self):
        selected = str(self.textCursor().selectedText() or "").replace("\u2029", "\n").replace("\u2028", "\n").strip()
        self.ask_selection_btn.hide()
        if selected:
            self.selectionQuestionRequested.emit(selected)

    def _update_selection_ask_button(self):
        # Bubbles may be created after the chat panel's last language-change pass.
        # Resolve the live language from the owning MainWindow whenever a selection
        # action is shown, so newly rendered/cached transcript pages are localized too.
        try:
            owner_settings = getattr(self.window(), "settings", None)
            if owner_settings is not None:
                current_language = owner_settings.value("interface_language", "en", type=str)
                normalized_language = "ar" if str(current_language or "en").lower().startswith("ar") else "en"
                if normalized_language != self._interface_language:
                    self.apply_language(normalized_language)
        except (RuntimeError, AttributeError, TypeError):
            pass
        selected = str(self.textCursor().selectedText() or "").strip()
        if not selected:
            self.ask_selection_btn.hide()
            return
        cursor = self.textCursor()
        rect = self.cursorRect(cursor)
        x = max(6, min(self.width() - self.ask_selection_btn.sizeHint().width() - 8, rect.left()))
        y = max(4, rect.top() - 31)
        self.ask_selection_btn.adjustSize()
        self.ask_selection_btn.setFixedHeight(27)
        self.ask_selection_btn.move(x, y)
        self.ask_selection_btn.raise_()
        self.ask_selection_btn.show()

    def _find_transcript_scroll_area(self):
        widget = self.parentWidget()
        while isinstance(widget, QWidget):
            if isinstance(widget, QScrollArea) and widget.objectName() == "aiTranscript":
                return widget
            widget = widget.parentWidget()
        return None

    def _selection_edge_direction(self, global_pos: QPoint):
        area = self._selection_scroll_area or self._find_transcript_scroll_area()
        if area is None:
            return 0
        viewport = area.viewport()
        pos = viewport.mapFromGlobal(global_pos)
        if pos.x() < -8 or pos.x() > viewport.width() + 8:
            return 0
        zone = min(self._EDGE_ZONE, max(18, viewport.height() // 5))
        if pos.y() <= zone:
            return -1
        if pos.y() >= viewport.height() - zone:
            return 1
        return 0

    def _update_selection_autoscroll(self, global_pos: QPoint):
        self._selection_scroll_direction = self._selection_edge_direction(global_pos)
        if self._selection_scroll_direction:
            if not self._selection_scroll_timer.isActive():
                self._selection_scroll_timer.start()
        else:
            self._selection_scroll_timer.stop()

    def _auto_scroll_selection_tick(self):
        if not self._selection_dragging:
            self._selection_scroll_timer.stop()
            return
        area = self._selection_scroll_area
        if area is None:
            area = self._find_transcript_scroll_area()
            self._selection_scroll_area = area
        if area is None or not area.isVisible():
            self._selection_scroll_timer.stop()
            return
        global_pos = QCursor.pos()
        direction = self._selection_edge_direction(global_pos)
        self._selection_scroll_direction = direction
        if not direction:
            self._selection_scroll_timer.stop()
            return
        viewport = area.viewport()
        view_pos = viewport.mapFromGlobal(global_pos)
        zone = min(self._EDGE_ZONE, max(18, viewport.height() // 5))
        distance = zone - view_pos.y() if direction < 0 else view_pos.y() - (viewport.height() - zone)
        step = max(2, min(32, 2 + int(max(0, distance) * 0.72)))
        bar = area.verticalScrollBar()
        old_value = bar.value()
        bar.setValue(old_value + direction * step)
        if bar.value() == old_value:
            self._selection_scroll_timer.stop()
            return
        # Scrolling the parent moves the selected QTextBrowser beneath the stationary
        # pointer. Re-issue the current mouse position so QTextBrowser extends the
        # selection into the newly revealed text instead of only moving the viewport.
        local_pos = self.mapFromGlobal(global_pos)
        synthetic = QMouseEvent(
            QEvent.Type.MouseMove, QPointF(local_pos), QPointF(global_pos),
            Qt.MouseButton.NoButton, Qt.MouseButton.LeftButton,
            QApplication.keyboardModifiers()
        )
        super().mouseMoveEvent(synthetic)

    def mousePressEvent(self, event):
        if event.button() == Qt.MouseButton.LeftButton:
            self._selection_dragging = True
            self._selection_scroll_area = self._find_transcript_scroll_area()
        super().mousePressEvent(event)

    def mouseMoveEvent(self, event):
        super().mouseMoveEvent(event)
        if self._selection_dragging and (event.buttons() & Qt.MouseButton.LeftButton):
            self._update_selection_autoscroll(event.globalPosition().toPoint())
        elif self._selection_scroll_timer.isActive():
            self._selection_scroll_timer.stop()

    def mouseReleaseEvent(self, event):
        super().mouseReleaseEvent(event)
        if event.button() == Qt.MouseButton.LeftButton:
            self._selection_dragging = False
            self._selection_scroll_direction = 0
            self._selection_scroll_timer.stop()
            self._selection_scroll_area = None
            QTimer.singleShot(0, self._update_selection_ask_button)

    def contextMenuEvent(self, event):
        selected_text = self.textCursor().selectedText()
        selected_text = str(selected_text or "").replace("\u2029", "\n").replace("\u2028", "\n").strip()

        # Keep QTextBrowser's native actions (Copy, Select All, and link actions)
        # and add the AI action only when an actual text selection exists.
        menu = self.createStandardContextMenu()
        if selected_text:
            menu.addSeparator()
            ask_action = menu.addAction(make_icon("chat", "#9ebcff", 16), "Ask Engo AI about selected text…")
            ask_action.triggered.connect(
                lambda _checked=False, text=selected_text: self.selectionQuestionRequested.emit(text)
            )
        menu.exec(event.globalPos())
        menu.deleteLater()


class ClickableChatImageLabel(QLabel):
    """Image thumbnail that opens its saved original in a dedicated preview window."""
    clicked = pyqtSignal()

    def mousePressEvent(self, event):
        if event.button() == Qt.MouseButton.LeftButton:
            self.clicked.emit()
            event.accept()
            return
        super().mousePressEvent(event)


class ClickableChatPassageLabel(QLabel):
    """Saved PDF excerpt that can be clicked to return to its source location."""
    clicked = pyqtSignal()

    def mousePressEvent(self, event):
        if event.button() == Qt.MouseButton.LeftButton:
            self.clicked.emit()
            event.accept()
            return
        super().mousePressEvent(event)


class ChatImagePreviewDialog(QDialog):
    """Resizable, zoomable popup for images attached to chat messages."""

    def __init__(self, image_path: str, title: str = "Attached image", parent=None):
        super().__init__(parent, Qt.WindowType.Window)
        self.image_path = os.path.abspath(str(image_path or ""))
        self._source_pixmap = QPixmap(self.image_path)
        self._zoom_factor = 1.0
        self.setWindowTitle(str(title or "Attached image"))
        self.setModal(False)
        self.setAttribute(Qt.WidgetAttribute.WA_DeleteOnClose, True)
        self.setMinimumSize(420, 300)
        self.setSizeGripEnabled(True)

        screen = QApplication.primaryScreen()
        available = screen.availableGeometry() if screen is not None else QRect(0, 0, 1200, 850)
        start_width = min(980, max(520, int(available.width() * 0.72)))
        start_height = min(820, max(420, int(available.height() * 0.78)))
        self.resize(start_width, start_height)
        self.move(available.center() - self.rect().center())

        root = QVBoxLayout(self)
        root.setContentsMargins(10, 10, 10, 10)
        root.setSpacing(8)
        toolbar = QHBoxLayout()
        self.file_label = QLabel(os.path.basename(self.image_path) or "Attached image")
        self.file_label.setTextFormat(Qt.TextFormat.PlainText)
        self.file_label.setMinimumWidth(0)
        self.file_label.setSizePolicy(QSizePolicy.Policy.Expanding, QSizePolicy.Policy.Preferred)
        toolbar.addWidget(self.file_label, 1)

        self.zoom_out_btn = QToolButton(self)
        self.zoom_out_btn.setText("−")
        self.zoom_out_btn.setFixedSize(32, 30)
        self.zoom_out_btn.setToolTip("Zoom out")
        self.zoom_out_btn.clicked.connect(lambda: self._change_zoom(1 / 1.2))
        toolbar.addWidget(self.zoom_out_btn)
        self.zoom_label = QLabel("Fit")
        self.zoom_label.setMinimumWidth(48)
        self.zoom_label.setAlignment(Qt.AlignmentFlag.AlignCenter)
        toolbar.addWidget(self.zoom_label)
        self.zoom_in_btn = QToolButton(self)
        self.zoom_in_btn.setText("+")
        self.zoom_in_btn.setFixedSize(32, 30)
        self.zoom_in_btn.setToolTip("Zoom in")
        self.zoom_in_btn.clicked.connect(lambda: self._change_zoom(1.2))
        toolbar.addWidget(self.zoom_in_btn)
        self.fit_btn = QToolButton(self)
        self.fit_btn.setText("Fit")
        self.fit_btn.setToolTip("Fit image to window")
        self.fit_btn.clicked.connect(self._reset_zoom)
        toolbar.addWidget(self.fit_btn)
        self.close_btn = QToolButton(self)
        self.close_btn.setText("×")
        self.close_btn.setFixedSize(32, 30)
        self.close_btn.setToolTip("Close image preview")
        self.close_btn.clicked.connect(self.close)
        toolbar.addWidget(self.close_btn)
        root.addLayout(toolbar)

        self.image_scroll = QScrollArea(self)
        self.image_scroll.setWidgetResizable(False)
        self.image_scroll.setAlignment(Qt.AlignmentFlag.AlignCenter)
        self.image_scroll.setFrameShape(QFrame.Shape.StyledPanel)
        self.image_scroll.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAsNeeded)
        self.image_scroll.setVerticalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAsNeeded)
        self.image_scroll.setStyleSheet("QScrollArea { background: #171b22; border: 1px solid #394456; border-radius: 6px; }")
        self.image_label = QLabel()
        self.image_label.setAlignment(Qt.AlignmentFlag.AlignCenter)
        self.image_label.setStyleSheet("QLabel { background: #171b22; border: 0; }")
        if self._source_pixmap.isNull():
            self.image_label.setText("Image file is no longer available.")
            self.image_label.setMinimumSize(260, 180)
        self.image_scroll.setWidget(self.image_label)
        root.addWidget(self.image_scroll, 1)
        QTimer.singleShot(0, self._render_image)

    def _change_zoom(self, factor: float):
        self._zoom_factor = max(0.20, min(5.0, self._zoom_factor * float(factor)))
        self._render_image()

    def _reset_zoom(self):
        self._zoom_factor = 1.0
        self._render_image()

    def _render_image(self):
        if self._source_pixmap.isNull():
            return
        viewport = self.image_scroll.viewport().size()
        viewport_width = max(80, int(viewport.width()) - 24)
        viewport_height = max(80, int(viewport.height()) - 24)
        fit_scale = min(viewport_width / max(1, self._source_pixmap.width()),
                        viewport_height / max(1, self._source_pixmap.height()), 1.0)
        scale = max(0.02, fit_scale * self._zoom_factor)
        target = QSize(max(1, round(self._source_pixmap.width() * scale)),
                       max(1, round(self._source_pixmap.height() * scale)))
        rendered = self._source_pixmap.scaled(
            target, Qt.AspectRatioMode.KeepAspectRatio,
            Qt.TransformationMode.SmoothTransformation,
        )
        self.image_label.setPixmap(rendered)
        self.image_label.resize(rendered.size())
        self.zoom_label.setText(f"{int(round(self._zoom_factor * 100))}%" if self._zoom_factor != 1.0 else "Fit")

    def resizeEvent(self, event):
        super().resizeEvent(event)
        QTimer.singleShot(0, self._render_image)


class AIMessageBubble(QFrame):
    """Responsive chat bubble with markdown/table rendering and visual region attachments."""
    selectionQuestionRequested = pyqtSignal(str, str)
    selectedTextLocationActivated = pyqtSignal(str, int, object)

    def __init__(self, role: str, content: str, width: int = 520, created_at: str = "", attachments=None, parent=None, font_pt: float = 13.0, selected_text_context: str = "", selected_text_location=None, language: str = "en"):
        super().__init__(parent)
        self.role = role
        self._font_pt = max(8.0, min(24.0, float(font_pt or 13.0)))
        self._content = str(content or "")
        self._attachments = list(attachments or [])
        self._selected_text_context = str(selected_text_context or "").strip()
        self._selected_text_location = dict(selected_text_location) if isinstance(selected_text_location, dict) else None
        is_user = role == "user"
        row = QHBoxLayout(self)
        row.setContentsMargins(1, 2, 1, 2)
        row.setSpacing(0)
        bubble_width = max(230, int(width))
        self._bubble_width = bubble_width
        if is_user:
            row.addStretch(1)
        card = QFrame()
        self.card = card
        card.setObjectName("aiUserCard" if is_user else "aiAssistantCard")
        card.setMaximumWidth(bubble_width)
        card.setMinimumWidth(min(210, bubble_width))
        card_layout = QVBoxLayout(card)
        card_layout.setContentsMargins(13, 9, 13, 10)
        card_layout.setSpacing(5)
        heading_row = QHBoxLayout()
        heading = QLabel("YOU" if is_user else "ENGO AI")
        heading.setObjectName("aiBubbleRole")
        heading_row.addWidget(heading)
        heading_row.addStretch(1)
        if created_at:
            stamp = QLabel(str(created_at).split(".")[0])
            stamp.setObjectName("aiBubbleTime")
            heading_row.addWidget(stamp)
        card_layout.addLayout(heading_row)

        if self._attachments:
            attachment_grid = QGridLayout()
            attachment_grid.setContentsMargins(0, 2, 0, 3)
            attachment_grid.setHorizontalSpacing(6)
            attachment_grid.setVerticalSpacing(6)
            visible_attachments = self._attachments[:8]
            attachment_columns = 4 if bubble_width >= 610 else (3 if bubble_width >= 480 else 2)
            for attachment_index, attachment in enumerate(visible_attachments):
                path = attachment.get("path", "") if isinstance(attachment, dict) else str(attachment)
                if not path or not os.path.isfile(path):
                    continue
                thumb = ClickableChatImageLabel()
                thumb.setObjectName("aiAttachmentThumb")
                thumb.setAlignment(Qt.AlignmentFlag.AlignCenter)
                thumb.setCursor(Qt.CursorShape.PointingHandCursor)
                pix = QPixmap(path)
                if not pix.isNull():
                    thumb.setPixmap(pix.scaled(132, 92, Qt.AspectRatioMode.KeepAspectRatio,
                                               Qt.TransformationMode.SmoothTransformation))
                    thumb.setFixedSize(138, 98)
                    if isinstance(attachment, dict) and attachment.get("page_index") is not None:
                        tip = f"Attached image · page {int(attachment.get('page_index')) + 1}"
                    else:
                        tip = str(attachment.get("label") or "Attached image") if isinstance(attachment, dict) else "Attached image"
                    thumb.setToolTip(tip + " · click to open · saved with this message")
                    thumb.setAccessibleName(tip + " · open image preview")
                    thumb.clicked.connect(
                        lambda image_path=path, image_title=tip: self.open_attachment_preview(image_path, image_title)
                    )
                    attachment_grid.addWidget(thumb, attachment_index // attachment_columns, attachment_index % attachment_columns)
            if len(self._attachments) > len(visible_attachments):
                more = QLabel(f"+{len(self._attachments) - len(visible_attachments)} more")
                more.setObjectName("aiAttachmentMore")
                more.setAlignment(Qt.AlignmentFlag.AlignCenter)
                more.setFixedSize(82, 42)
                attachment_grid.addWidget(more, len(visible_attachments) // attachment_columns, len(visible_attachments) % attachment_columns)
            card_layout.addLayout(attachment_grid)

        self.body = AIChatMessageBrowser()
        self.body.selectionQuestionRequested.connect(
            lambda selected, source_role=role: self.selectionQuestionRequested.emit(selected, source_role)
        )
        self.body.setObjectName("aiBubbleContent")
        self.body.setOpenExternalLinks(True)
        self.body.setFrameShape(QFrame.Shape.NoFrame)
        self.body.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        self.body.setVerticalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        self.body.setLineWrapMode(QTextEdit.LineWrapMode.WidgetWidth)
        self.body.setWordWrapMode(QTextOption.WrapMode.WrapAtWordBoundaryOrAnywhere)
        self.body.setTextInteractionFlags(Qt.TextInteractionFlag.TextSelectableByMouse | Qt.TextInteractionFlag.LinksAccessibleByMouse)
        self.body.setStyleSheet("QTextBrowser { background: transparent; border: 0; }")
        chat_font = self.body.font()
        chat_font.setPointSizeF(self._font_pt)
        self.body.setFont(chat_font)
        self.body_width = max(180, bubble_width - 28)
        self.body.setFixedWidth(self.body_width)
        self.body.document().setTextWidth(self.body_width - 8)
        try:
            light_message_theme = self.body.palette().text().color().lightness() < 150
        except Exception:
            light_message_theme = True
        if light_message_theme:
            message_document_css = (
                "table { border-collapse: collapse; } "
                "th, td { border: 1px solid #b8c5d5; padding: 4px; } "
                "th { background: #e7edf5; color: #263449; } "
                "code { background: #e8eef6; color: #244b80; border: 1px solid #d1dbe8; }"
            )
        else:
            message_document_css = (
                "table { border-collapse: collapse; } "
                "th, td { border: 1px solid #4b5b73; padding: 4px; } "
                "th { background: #27364b; color: #edf3ff; } "
                "code { background: #18202b; color: #c7dbff; border: 1px solid #35465e; }"
            )
        self.body.document().setDefaultStyleSheet(message_document_css)
        self.set_content(self._content)
        card_layout.addWidget(self.body)
        if is_user and self._selected_text_context:
            selected_card = QFrame(card)
            selected_card.setObjectName("aiSelectedPassageCard")
            selected_layout = QVBoxLayout(selected_card)
            selected_layout.setContentsMargins(8, 6, 8, 6)
            selected_layout.setSpacing(4)
            selected_card.setToolTip(
                "الضغط على المقطع يعيدك إلى مكانه في الملف" if str(language or "en").lower().startswith("ar")
                else "Click the passage to return to its source in the PDF"
            )
            selected_title_row = QHBoxLayout()
            is_ar_message = str(language or "en").lower().startswith("ar")
            selected_title = QLabel(("النص المحدد من الملف" if self._selected_text_location else "النص المحدد") if is_ar_message else "Selected passage")
            selected_title.setObjectName("aiSelectedPassageTitle")
            selected_title_row.addWidget(selected_title, 1)
            if self._selected_text_location and self._selected_text_location.get("path") and self._selected_text_location.get("page_index") is not None:
                jump_btn = QToolButton(selected_card)
                jump_btn.setObjectName("aiSelectedPassageJump")
                jump_btn.setText("عرض في PDF" if is_ar_message else "Show in PDF")
                jump_btn.setCursor(Qt.CursorShape.PointingHandCursor)
                jump_btn.setToolTip("الانتقال إلى النص المحدد في الصفحة" if is_ar_message else "Jump to the selected text in the PDF")
                jump_btn.clicked.connect(lambda _checked=False, loc=dict(self._selected_text_location): self.selectedTextLocationActivated.emit(str(loc.get("path") or ""), int(loc.get("page_index", 0)), loc.get("box")))
                selected_title_row.addWidget(jump_btn, 0, Qt.AlignmentFlag.AlignRight)
            selected_layout.addLayout(selected_title_row)
            selected_preview = ClickableChatPassageLabel(self._selected_text_context)
            selected_preview.setObjectName("aiSelectedPassagePreview")
            selected_preview.setWordWrap(True)
            selected_preview.setTextFormat(Qt.TextFormat.PlainText)
            selected_preview.setToolTip(
                ("اضغط للرجوع إلى موضع النص في PDF" if is_ar_message else "Click to return to this passage in the PDF")
                if self._selected_text_location else self._selected_text_context
            )
            has_saved_location = bool(
                self._selected_text_location
                and self._selected_text_location.get("path")
                and self._selected_text_location.get("page_index") is not None
            )
            if has_saved_location:
                selected_preview.setCursor(Qt.CursorShape.PointingHandCursor)
                selected_preview.clicked.connect(
                    lambda loc=dict(self._selected_text_location): self.selectedTextLocationActivated.emit(
                        str(loc.get("path") or ""), int(loc.get("page_index", 0)), loc.get("box")
                    )
                )
            selected_layout.addWidget(selected_preview)
            card_layout.addWidget(selected_card)
        if not is_user:
            footer_row = QHBoxLayout()
            footer_row.setContentsMargins(0, -1, 0, 0)
            footer_row.setSpacing(3)
            footer_row.addStretch(1)
            self.copy_button = QToolButton()
            self.copy_button.setObjectName("aiMessageCopyButton")
            self.copy_button.setIcon(make_icon("copy", "#9fb2ce", 15))
            self.copy_button.setIconSize(QSize(15, 15))
            self.copy_button.setFixedSize(25, 23)
            self.copy_button.setAutoRaise(True)
            self.copy_button.setCursor(Qt.CursorShape.PointingHandCursor)
            self.copy_button.setToolTip("Copy this answer")
            self.copy_button.setStyleSheet("QToolButton { border:0; border-radius:5px; padding:3px; background:transparent; } QToolButton:hover { background:rgba(105,150,220,45); }")
            self.copy_button.clicked.connect(self.copy_message)
            footer_row.addWidget(self.copy_button)
            card_layout.addLayout(footer_row)
        row.addWidget(card)
        if not is_user:
            row.addStretch(1)

    def open_attachment_preview(self, image_path: str, title: str = "Attached image"):
        """Open a chat attachment without navigating away from the conversation."""
        image_path = os.path.abspath(str(image_path or ""))
        if not os.path.isfile(image_path):
            return
        current = getattr(self, "_attachment_preview_dialog", None)
        try:
            if current is not None and current.isVisible():
                if os.path.normcase(str(getattr(current, "image_path", ""))) == os.path.normcase(image_path):
                    current.raise_()
                    current.activateWindow()
                    return
                current.close()
        except RuntimeError:
            self._attachment_preview_dialog = None
        dialog = ChatImagePreviewDialog(image_path, title, self.window())
        self._attachment_preview_dialog = dialog
        dialog.destroyed.connect(lambda *_: setattr(self, "_attachment_preview_dialog", None))
        dialog.show()
        dialog.raise_()
        dialog.activateWindow()

    def copy_message(self):
        """Copy this assistant response as reusable plain text/Markdown."""
        QApplication.clipboard().setText(self._content)
        if hasattr(self, "copy_button"):
            self.copy_button.setToolTip("Copied")

    def set_bubble_width(self, width: int):
        """Resize an existing bubble without rebuilding or reparsing its Markdown."""
        bubble_width = max(230, int(width))
        if bubble_width == getattr(self, "_bubble_width", None):
            return
        self._bubble_width = bubble_width
        self.card.setMaximumWidth(bubble_width)
        self.card.setMinimumWidth(min(210, bubble_width))
        body_width = max(180, bubble_width - 28)
        if body_width == self.body_width:
            self.updateGeometry()
            return
        self.body_width = body_width
        self.body.setFixedWidth(body_width)
        self.body.document().setTextWidth(body_width - 8)
        height = max(30, int(math.ceil(self.body.document().size().height())) + 13)
        self.body.setFixedHeight(min(height, 9000))
        self.updateGeometry()

    def set_font_size(self, font_pt: float):
        self._font_pt = max(8.0, min(24.0, float(font_pt or 13.0)))
        font = self.body.font()
        font.setPointSizeF(self._font_pt)
        self.body.setFont(font)
        self.set_content(self._content)

    def set_content(self, content: str):
        self._content = str(content or "")
        _set_markdown_browser(self.body, self._content or "…", self._font_pt)
        self.body.document().setDefaultFont(self.body.font())
        self.body.document().setTextWidth(self.body_width - 8)
        height = max(30, int(math.ceil(self.body.document().size().height())) + 13)
        self.body.setFixedHeight(min(height, 9000))
        self.updateGeometry()


class AIChatConversationDelegate(QStyledItemDelegate):
    """Paint saved-chat rows from Engo's active theme tokens (never fixed colors)."""
    def __init__(self, parent=None, settings=None):
        super().__init__(parent)
        self.settings = settings

    def _colors(self):
        try:
            raw_theme = self.settings.value("ui_theme", "dark", type=str) if self.settings is not None else "dark"
        except Exception:
            raw_theme = "dark"
        tokens = engo_ui_theme_tokens(raw_theme)
        return {
            "normal": tokens["panel"],
            "hover": tokens["hover"],
            "selected": tokens["selection"],
            "text": tokens["text"],
            "selected_text": tokens["selection_text"],
            "muted": tokens["muted"],
            "danger": "#d97782" if normalize_ui_theme(raw_theme) != "light" else "#b54752",
        }

    def paint(self, painter, option, index):
        colors = self._colors()
        painter.save()
        rect = option.rect
        selected = bool(option.state & QStyle.StateFlag.State_Selected)
        hovered = bool(option.state & QStyle.StateFlag.State_MouseOver)
        bg = colors["selected"] if selected else (colors["hover"] if hovered else colors["normal"])
        painter.fillRect(rect, QColor(bg))

        title = str(index.data(Qt.ItemDataRole.DisplayRole) or "Conversation")
        painter.setPen(QColor(colors["selected_text"] if selected else colors["text"]))
        text_rect = rect.adjusted(12, 0, -39, 0)
        painter.drawText(text_rect, Qt.AlignmentFlag.AlignVCenter | Qt.AlignmentFlag.AlignLeft, title)

        # Small trash-can glyph; click handling remains in AIChatPanel.eventFilter.
        cx = rect.right() - 19
        cy = rect.center().y()
        icon_color = QColor(colors["danger"] if hovered else colors["muted"])
        painter.setPen(QPen(icon_color, 1.35, Qt.PenStyle.SolidLine, Qt.PenCapStyle.RoundCap))
        painter.setBrush(Qt.BrushStyle.NoBrush)
        painter.drawLine(QPoint(cx - 5, cy - 5), QPoint(cx + 5, cy - 5))
        painter.drawLine(QPoint(cx - 2, cy - 7), QPoint(cx + 2, cy - 7))
        painter.drawLine(QPoint(cx - 4, cy - 4), QPoint(cx - 3, cy + 6))
        painter.drawLine(QPoint(cx + 4, cy - 4), QPoint(cx + 3, cy + 6))
        painter.drawLine(QPoint(cx - 3, cy + 6), QPoint(cx + 3, cy + 6))
        painter.drawLine(QPoint(cx - 1, cy - 2), QPoint(cx - 1, cy + 4))
        painter.drawLine(QPoint(cx + 1, cy - 2), QPoint(cx + 1, cy + 4))
        painter.restore()

    def sizeHint(self, option, index):
        base = super().sizeHint(option, index)
        return QSize(max(base.width(), 160), max(34, base.height()))


class AIChatPanel(QFrame):
    """Compact, per-document AI chat with quick actions and Markdown/PDF export."""
    requestSent = pyqtSignal(str, str, object, bool, str, int)

    def __init__(self, settings: QSettings, main_window):
        super().__init__()
        self.settings = settings
        self.main_window = main_window
        self._chat_font_pt = max(8.0, min(24.0, settings.value("ui_chat_font_pt", 13, type=float)))
        self._typing_font_pt = max(8.0, min(24.0, settings.value("ui_typing_font_pt", 12, type=float)))
        self.setObjectName("aiPanel")
        # Allow the chat dock to become narrower; the provider/model selectors
        # below use ignored horizontal size hints so they can contract instead
        # of forcing the controls row to overlap.
        self.setMinimumWidth(330)
        self.setMaximumWidth(720)
        self.document_path = ""
        self.document_name = "No PDF open"
        self.chat_scope_key = ""
        self._pending_request_scope = None
        self.chat_store = AIChatStore()
        self.messages_by_document: dict[str, list[dict[str, str]]] = {}
        self.active_chat_ids: dict[str, int] = {}
        self._loaded_chat_ids_by_scope: dict[str, int] = {}
        # Keep a small number of fully rendered transcript pages alive. Switching
        # document tabs can then show an existing widget tree instead of rebuilding
        # Markdown/equations/tables on every selection change.
        self._transcript_pages: dict[tuple[str, int], dict] = {}
        self._active_transcript_page_key = None
        self._transcript_page_cache_limit = 5
        self.selected_regions: dict[str, list[dict]] = {}
        self._pending_selected_text = ""
        self._pending_selected_text_source_role = "assistant"
        self._pending_selected_text_location = None
        self._live_bubble = None
        self._live_path = ""
        self._live_text = ""
        self._loading_chat_combo = False
        self._chat_delete_pressed_id = None
        self._busy = False
        self._chat_bubbles = []
        self._chat_search_current = -1
        self._chat_search_matches = []
        self._loading_phase = 0
        self._loading_status_text = "Preparing your request"
        self._loading_timer = QTimer(self)
        self._loading_timer.setInterval(380)
        self._loading_timer.timeout.connect(self._animate_chat_loading)
        self._build()
        self.apply_language()

    def apply_language(self, language=None):
        """Apply the current interface language to dynamic AI composer controls."""
        if language is None:
            try:
                language = self.settings.value("interface_language", "en", type=str)
            except Exception:
                language = "en"
        is_ar = str(language or "en").lower().startswith("ar")
        busy = bool(getattr(self, "_busy", False))
        for message_browser in self.findChildren(AIChatMessageBrowser):
            try:
                message_browser.apply_language("ar" if is_ar else "en")
            except RuntimeError:
                pass
        button = getattr(self, "send_btn", None)
        if button is not None:
            if busy:
                button.setText("إيقاف" if is_ar else "Stop")
                button.setToolTip("إيقاف استجابة الذكاء الاصطناعي الحالية" if is_ar else "Stop the current AI response")
            else:
                button.setText("إرسال" if is_ar else "Send")
                button.setToolTip("إرسال الرسالة" if is_ar else "Send message")
        prompt = getattr(self, "prompt_edit", None)
        if prompt is not None:
            if getattr(self, "_pending_selected_text", ""):
                placeholder = (
                    "اكتب ما تريد السؤال عنه بخصوص النص المحدد…" if is_ar
                    else "Type what you want to ask about the selected text…"
                )
            else:
                placeholder = (
                    "اكتب رسالتك إلى Engo AI…  ·  Enter للإرسال · Shift+Enter لسطر جديد · Ctrl+V للصق صورة"
                    if is_ar else
                    "Message Engo AI…  ·  Enter to send · Shift+Enter for a new line · Paste an image with Ctrl+V"
                )
            prompt.setPlaceholderText(placeholder)

        # Chat-panel controls that are created dynamically or whose labels are
        # intentionally excluded from the generic MainWindow translation pass.
        dual = str(getattr(self, "chat_scope_key", "") or "").startswith("ENGO_DUAL::")
        if hasattr(self, "chat_heading"):
            self.chat_heading.setText(
                ("محادثة Engo AI لملفين" if dual else "محادثة Engo AI") if is_ar
                else ("Dual File Engo AI Chat" if dual else "Engo AI Chat")
            )
        if hasattr(self, "chat_subtitle"):
            self.chat_subtitle.setText(
                (("محادثة مشتركة لملفي PDF المرتبطين" if dual else "مساعدك الدراسي لملفات PDF")) if is_ar
                else (("One shared conversation for both linked PDFs" if dual else "Your PDF study assistant"))
            )
        if hasattr(self, "pdf_actions_btn"):
            self.pdf_actions_btn.setText("إجراءات PDF ▾" if is_ar else "PDF actions ▾")
        if hasattr(self, "export_btn"):
            self.export_btn.setText("تصدير" if is_ar else "Export")
        if hasattr(self, "close_panel_btn"):
            self.close_panel_btn.setToolTip("إغلاق قسم المحادثة" if is_ar else "Close AI chat")
            self.close_panel_btn.setAccessibleName("إغلاق قسم محادثة AI" if is_ar else "Close AI chat panel")

        # Saved passage cards are not rebuilt when the interface language changes;
        # update their labels in place so the transcript itself remains untouched.
        for bubble in self.findChildren(AIMessageBubble):
            if bubble.role != "user" or not getattr(bubble, "_selected_text_context", ""):
                continue
            has_location = bool(
                getattr(bubble, "_selected_text_location", None)
                and bubble._selected_text_location.get("path")
                and bubble._selected_text_location.get("page_index") is not None
            )
            title_label = bubble.findChild(QLabel, "aiSelectedPassageTitle")
            if title_label is not None:
                title_label.setText(("النص المحدد من الملف" if has_location else "النص المحدد") if is_ar else "Selected passage")
            preview_label = bubble.findChild(QLabel, "aiSelectedPassagePreview")
            if preview_label is not None:
                preview_label.setToolTip(("اضغط للرجوع إلى موضع النص في الملف" if is_ar else "Click to return to this passage in the PDF") if has_location else bubble._selected_text_context)
            jump_button = bubble.findChild(QToolButton, "aiSelectedPassageJump")
            if jump_button is not None:
                jump_button.setText("عرض في PDF" if is_ar else "Show in PDF")
                jump_button.setToolTip("الانتقال إلى النص المحدد في الصفحة" if is_ar else "Jump to the selected text in the PDF")
            passage_card = bubble.findChild(QFrame, "aiSelectedPassageCard")
            if passage_card is not None and has_location:
                passage_card.setToolTip("الضغط على المقطع يعيدك إلى مكانه في الملف" if is_ar else "Click the passage to return to its source in the PDF")
        if hasattr(self, "new_chat_btn"):
            self.new_chat_btn.setText("+ محادثة جديدة" if is_ar else "+ New chat")
            self.new_chat_btn.setToolTip(
                ("بدء محادثة مشتركة جديدة لملفي PDF المرتبطين" if dual else "بدء محادثة محفوظة جديدة لهذا الملف") if is_ar
                else ("Start a new shared conversation for both linked PDFs" if dual else "Start a new saved conversation for this PDF")
            )
        if hasattr(self, "chat_combo"):
            self.chat_combo.setToolTip(
                ("المحادثات المحفوظة لملفي PDF المرتبطين" if dual else "المحادثات المحفوظة لملف PDF الحالي") if is_ar
                else ("Saved conversations for this linked PDF pair" if dual else "Saved conversations for the current PDF")
            )
        if hasattr(self, "chat_search_btn"):
            self.chat_search_btn.setToolTip("ابحث داخل هذه المحادثة" if is_ar else "Search inside this conversation")
        if hasattr(self, "chat_search_edit"):
            self.chat_search_edit.setPlaceholderText("ابحث عن نص في هذه المحادثة…" if is_ar else "Find text in this conversation…")
        if hasattr(self, "chat_search_prev_btn"):
            self.chat_search_prev_btn.setToolTip("النتيجة السابقة" if is_ar else "Previous match")
        if hasattr(self, "chat_search_next_btn"):
            self.chat_search_next_btn.setToolTip("النتيجة التالية" if is_ar else "Next match")
        if hasattr(self, "chat_search_close_btn"):
            self.chat_search_close_btn.setToolTip("إغلاق البحث في المحادثة" if is_ar else "Close conversation search")
        if hasattr(self, "document_label"):
            if not getattr(self, "document_path", ""):
                self.document_label.setText("افتح ملف PDF لطرح الأسئلة حوله." if is_ar else "Open a PDF to ask questions about it.")
            else:
                self.document_label.setText(("سياق PDF · " if is_ar else "PDF context · ") + str(getattr(self, "document_name", "")))
        if hasattr(self, "jump_bottom_btn"):
            self.jump_bottom_btn.setText("↓ آخر رسالة" if is_ar else "↓ Latest message")
            self.jump_bottom_btn.setToolTip("انتقل إلى أحدث رسالة في هذه المحادثة" if is_ar else "Scroll to the latest message in this conversation")
        if hasattr(self, "attachment_label"):
            self.attachment_label.setText("المرفقات" if is_ar else "Attachments")
        if hasattr(self, "clear_attachment_btn"):
            self.clear_attachment_btn.setText("مسح" if is_ar else "Clear")
            self.clear_attachment_btn.setToolTip("إزالة الصور ومناطق PDF والنصوص المحددة المرفقة" if is_ar else "Remove pending images, PDF regions, and selected chat text")
        if hasattr(self, "pending_selected_text_title"):
            source_role = getattr(self, "_pending_selected_text_source_role", "assistant").casefold()
            if source_role == "user":
                selected_title = "مقطع محدد من رسالتك" if is_ar else "Selected passage from your message"
            elif source_role == "document":
                selected_title = "نص محدد من ملف PDF" if is_ar else "Selected text from the PDF document"
            else:
                selected_title = "مقطع محدد من رد Engo AI" if is_ar else "Selected passage from Engo AI's reply"
            self.pending_selected_text_title.setText(selected_title)
        if hasattr(self, "remove_pending_selected_text_btn"):
            self.remove_pending_selected_text_btn.setToolTip("إزالة النص المحدد" if is_ar else "Remove selected chat text")
        if hasattr(self, "add_region_btn"):
            self.add_region_btn.setToolTip("إضافة صورة أو لصقها من الحافظة أو تحديد منطقة من ملف PDF" if is_ar else "Add an image, paste from clipboard, or select a region from the PDF")
        if hasattr(self, "provider_combo"):
            self.provider_combo.setToolTip("اختر خدمة الذكاء الاصطناعي التي ستستقبل سؤالك" if is_ar else "Choose which AI service receives your question")
        if hasattr(self, "model_combo"):
            self.model_combo.setToolTip("اختر نموذج هذه المحادثة. حدّث النماذج المتاحة من إعدادات مزود AI." if is_ar else "Choose the model for this chat. Refresh available models in AI provider settings.")
        if hasattr(self, "include_context"):
            self.include_context.setText("سياق PDF" if is_ar else "PDF context")
            self.include_context.setToolTip("إرفاق نص PDF أو معاينات الصفحات. إجراءات الصفحة الحالية ترفقها دائمًا." if is_ar else "Include PDF text or page previews. Current-page actions always include the current page.")
        if hasattr(self, "voice_btn"):
            self.voice_btn.setText("اسأل بالصوت" if is_ar else "Ask by voice")
            self.voice_btn.setToolTip(_engo_translate_tooltip(
                "Record one spoken question, send it to the selected AI, and read its answer aloud", language))
        if hasattr(self, "read_answer_btn"):
            self.read_answer_btn.setText("اقرأ آخر إجابة" if is_ar else "Read latest")
            self.read_answer_btn.setToolTip(_engo_translate_tooltip("Read the latest AI answer aloud", language))
        if hasattr(self, "stop_audio_btn"):
            self.stop_audio_btn.setText("إيقاف الصوت" if is_ar else "Stop audio")
            self.stop_audio_btn.setToolTip(_engo_translate_tooltip("Stop the spoken answer", language))
        if hasattr(self, "pending_header") and hasattr(self, "pending_images_layout"):
            self._refresh_attachment_label()

        # Rebuild only the empty-state welcome bubble. Actual user/assistant chat
        # messages must remain untouched when the interface language changes.
        if hasattr(self, "transcript_layout") and not getattr(self, "_busy", False):
            scope = self.chat_scope_key or self.document_path
            if not self.messages_by_document.get(scope, []):
                QTimer.singleShot(0, self._render_transcript)

    def showEvent(self, event):
        """Reflow cached messages after the panel receives its real splitter width.

        The chat can be restored while hidden during application startup. In that
        state QScrollArea.viewport().width() may still be 0, which used to make
        every restored assistant message keep the 250 px fallback width. The
        delayed passes below run after Qt has applied the initial window geometry
        and after the normal chat-panel reveal animation.
        """
        super().showEvent(event)
        for delay_ms in (0, 110, 270):
            QTimer.singleShot(delay_ms, self._reflow_after_show)

    def _reflow_after_show(self):
        if not self.isVisible() or not hasattr(self, "transcript"):
            return
        viewport_width = int(self.transcript.viewport().width())
        # Skip the collapsed frame of the reveal animation. A later scheduled
        # pass will catch the panel once it has useful horizontal space.
        if viewport_width < 300:
            return
        self.reflow_transcript_bubbles_batched(batch_size=4, interval_ms=0)

    def _initial_transcript_bubble_width(self) -> int:
        """Return a useful width even if the transcript is rendered while hidden."""
        viewport_width = int(self.transcript.viewport().width())
        if viewport_width < 260:
            panel_width = int(self.width())
            if panel_width >= 300:
                viewport_width = panel_width - 18
            else:
                # A conservative normal chat width is preferable to persisting
                # a very narrow bubble when the panel has not been laid out yet.
                viewport_width = 520
        return max(250, viewport_width - 28)

    def apply_font_preferences(self, chat_font_pt: float, typing_font_pt: float):
        self._chat_font_pt = max(8.0, min(24.0, float(chat_font_pt or 13.0)))
        self._typing_font_pt = max(8.0, min(24.0, float(typing_font_pt or 12.0)))
        if hasattr(self, "prompt_edit"):
            font = self.prompt_edit.font()
            font.setPointSizeF(self._typing_font_pt)
            self.prompt_edit.setFont(font)
            self.prompt_edit.setStyleSheet(f"font-size: {self._typing_font_pt:.1f}pt;")
        for bubble in self.findChildren(AIMessageBubble):
            try:
                bubble.set_font_size(self._chat_font_pt)
            except RuntimeError:
                continue

    def _build(self):
        layout = QVBoxLayout(self)
        layout.setContentsMargins(12, 10, 12, 10)
        layout.setSpacing(7)

        # Slim top bar: saved conversations and secondary actions only.
        header = QHBoxLayout()
        header.setSpacing(6)
        icon = QLabel()
        self.chat_header_icon = icon
        icon.setPixmap(make_icon("ai", "#91b4ff", 20).pixmap(QSize(22, 22)))
        header.addWidget(icon)
        name_box = QVBoxLayout()
        name_box.setSpacing(0)
        self.chat_heading = QLabel("Engo AI Chat")
        self.chat_heading.setObjectName("aiTitle")
        self.chat_subtitle = QLabel("Your PDF study assistant")
        self.chat_subtitle.setObjectName("aiMuted")
        name_box.addWidget(self.chat_heading)
        name_box.addWidget(self.chat_subtitle)
        header.addLayout(name_box, 1)
        self.pdf_actions_btn = QPushButton("PDF actions ▾")
        self.pdf_actions_btn.setObjectName("aiPdfActions")
        self.pdf_actions_btn.setFixedHeight(34)
        self.pdf_actions_btn.setSizePolicy(QSizePolicy.Policy.Preferred, QSizePolicy.Policy.Fixed)
        self.pdf_actions_btn.setIcon(make_icon("summarize", "#9ebcff", 15))
        self.pdf_actions_btn.setToolTip("Summarize/review the whole PDF or ask about the current page")
        self.pdf_actions_btn.clicked.connect(self._show_pdf_actions_menu)
        header.addWidget(self.pdf_actions_btn)
        self.export_btn = QPushButton("Export")
        self.export_btn.setObjectName("aiExport")
        self.export_btn.setFixedHeight(34)
        self.export_btn.setSizePolicy(QSizePolicy.Policy.Preferred, QSizePolicy.Policy.Fixed)
        self.export_btn.setIcon(make_icon("export", "#b7c6dc", 15))
        self.export_btn.setToolTip("Export this conversation as Markdown or a formatted PDF report")
        self.export_btn.clicked.connect(self._export_menu)
        header.addWidget(self.export_btn)
        self.focus_mode_btn = MotionButton(parent=self)
        self.focus_mode_btn.setObjectName("aiFocusMode")
        self.focus_mode_btn.setIcon(make_icon("fullscreen", "#b7c6dc", 16))
        self.focus_mode_btn.setFixedSize(32, 34)
        self.focus_mode_btn.setToolTip("Expand chat · hide the PDF and app controls (Ctrl+Shift+F)")
        self.focus_mode_btn.setAccessibleName("Enter chat focus mode")
        self.focus_mode_btn.clicked.connect(lambda _checked=False: self.main_window.toggle_chat_focus_mode())
        header.addWidget(self.focus_mode_btn)
        self.close_panel_btn = QPushButton("×")
        self.close_panel_btn.setObjectName("aiClosePanel")
        self.close_panel_btn.setFixedSize(36, 34)
        self.close_panel_btn.setContentsMargins(0, 0, 0, 0)
        self.close_panel_btn.setStyleSheet("text-align:center; padding:0px;")
        self.close_panel_btn.setCursor(Qt.CursorShape.PointingHandCursor)
        self.close_panel_btn.setToolTip("Close AI chat")
        self.close_panel_btn.setAccessibleName("Close AI chat panel")
        self.close_panel_btn.clicked.connect(self.main_window.close_ai_panel)
        header.addWidget(self.close_panel_btn)
        layout.addLayout(header)

        self.chat_session_container = QWidget(self)
        chat_session_row = QHBoxLayout(self.chat_session_container)
        chat_session_row.setContentsMargins(0, 0, 0, 0)
        chat_session_row.setSpacing(6)
        self.chat_combo = QComboBox()
        self.chat_combo.setObjectName("aiChatSelector")
        self.chat_combo.setToolTip("Saved conversations for the current PDF")
        self.chat_combo.setMaxVisibleItems(12)
        self.chat_combo.setItemDelegate(AIChatConversationDelegate(self.chat_combo, self.settings))
        self.chat_combo.currentIndexChanged.connect(self._select_saved_chat)
        self.chat_combo.view().setMouseTracking(True)
        self.chat_combo.view().viewport().setMouseTracking(True)
        self.chat_combo.view().viewport().installEventFilter(self)
        chat_session_row.addWidget(self.chat_combo, 1)
        self.chat_search_btn = QPushButton()
        self.chat_search_btn.setObjectName("aiChatSearch")
        self.chat_search_btn.setIcon(make_icon("search", "#aebfda", 15))
        # Both session-row action buttons share the exact same outer height.
        # The search button keeps its compact square width; the new-chat button
        # keeps a text-driven width but uses the same fixed 30 px height.
        self.chat_search_btn.setFixedSize(32, 30)
        self.chat_search_btn.setMinimumHeight(30)
        self.chat_search_btn.setMaximumHeight(30)
        self.chat_search_btn.setContentsMargins(0, 0, 0, 0)
        self.chat_search_btn.setToolTip("Search inside this conversation")
        self.chat_search_btn.clicked.connect(self._toggle_chat_search)
        chat_session_row.addWidget(self.chat_search_btn, 0, Qt.AlignmentFlag.AlignVCenter)
        self.new_chat_btn = QPushButton("+ New chat")
        self.new_chat_btn.setObjectName("aiNewChat")
        # Match the search control's outer geometry explicitly. Do not derive
        # the height from a pre-show QWidget geometry, which can vary before
        # polish/layout on some Qt styles and make this button look taller.
        self.new_chat_btn.setFixedHeight(30)
        self.new_chat_btn.setMinimumHeight(30)
        self.new_chat_btn.setMaximumHeight(30)
        self.new_chat_btn.setContentsMargins(0, 0, 0, 0)
        self.new_chat_btn.setSizePolicy(QSizePolicy.Policy.Preferred, QSizePolicy.Policy.Fixed)
        self.new_chat_btn.setToolTip("Start a new saved conversation for this PDF")
        self.new_chat_btn.clicked.connect(self._new_conversation)
        chat_session_row.addWidget(self.new_chat_btn, 0, Qt.AlignmentFlag.AlignVCenter)
        layout.addWidget(self.chat_session_container)

        self.chat_search_row = QWidget()
        search_row_layout = QHBoxLayout(self.chat_search_row)
        search_row_layout.setContentsMargins(0, 0, 0, 0)
        search_row_layout.setSpacing(5)
        self.chat_search_edit = QLineEdit()
        self.chat_search_edit.setPlaceholderText("Find text in this conversation…")
        self.chat_search_edit.returnPressed.connect(lambda: self._find_in_chat(False))
        self.chat_search_edit.textChanged.connect(self._reset_chat_search)
        search_row_layout.addWidget(self.chat_search_edit, 1)
        self.chat_search_prev_btn = QPushButton("↑")
        self.chat_search_prev_btn.setFixedWidth(30)
        self.chat_search_prev_btn.setToolTip("Previous match")
        self.chat_search_prev_btn.clicked.connect(lambda: self._find_in_chat(True))
        search_row_layout.addWidget(self.chat_search_prev_btn)
        self.chat_search_next_btn = QPushButton("↓")
        self.chat_search_next_btn.setFixedWidth(30)
        self.chat_search_next_btn.setToolTip("Next match")
        self.chat_search_next_btn.clicked.connect(lambda: self._find_in_chat(False))
        search_row_layout.addWidget(self.chat_search_next_btn)
        self.chat_search_count = QLabel("")
        self.chat_search_count.setMinimumWidth(48)
        search_row_layout.addWidget(self.chat_search_count)
        self.chat_search_close_btn = QPushButton("×")
        self.chat_search_close_btn.setFixedWidth(28)
        self.chat_search_close_btn.setToolTip("Close conversation search")
        self.chat_search_close_btn.clicked.connect(self._toggle_chat_search)
        search_row_layout.addWidget(self.chat_search_close_btn)
        self.chat_search_row.hide()
        layout.addWidget(self.chat_search_row)

        self.document_label = QLabel("Open a PDF to start a conversation.")
        self.document_label.setObjectName("aiContextLabel")
        self.document_label.setWordWrap(False)
        self.document_label.setMaximumHeight(25)
        self.document_label.setToolTip("The current PDF provides context to questions when enabled")
        # The selected conversation name is already visible in chat_combo.
        # Keep this context label alive for compatibility with existing update
        # code, but do not show the redundant strip beneath the conversation row.
        self.document_label.hide()

        # Conversation gets almost all available vertical space.
        self.transcript = QScrollArea()
        self.transcript.setObjectName("aiTranscript")
        self.transcript.setWidgetResizable(True)
        self.transcript.setFrameShape(QFrame.Shape.NoFrame)
        self.transcript.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        self.transcript.setVerticalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAsNeeded)
        self.transcript_body = QWidget()
        self.transcript_body.setObjectName("aiTranscriptBody")
        self.transcript_layout = QVBoxLayout(self.transcript_body)
        self.transcript_layout.setContentsMargins(9, 9, 9, 10)
        self.transcript_layout.setSpacing(8)
        self.transcript_layout.addStretch(1)
        self.transcript.setWidget(self.transcript_body)
        layout.addWidget(self.transcript, 1)
        self.transcript.verticalScrollBar().valueChanged.connect(self._update_chat_jump_button)
        self.transcript.verticalScrollBar().rangeChanged.connect(lambda *_: self._update_chat_jump_button())

        jump_row = QHBoxLayout()
        jump_row.setContentsMargins(0, 0, 2, 0)
        jump_row.addStretch(1)
        self.jump_bottom_btn = QPushButton("↓ Latest message")
        self.jump_bottom_btn.setObjectName("aiJumpLatest")
        self.jump_bottom_btn.setToolTip("Scroll to the latest message in this conversation")
        self.jump_bottom_btn.clicked.connect(self._scroll_chat_to_bottom)
        self.jump_bottom_btn.hide()
        jump_row.addWidget(self.jump_bottom_btn)
        layout.addLayout(jump_row)

        self.busy_label = QLabel("")
        self.busy_label.setObjectName("aiBusyLabel")
        self.busy_label.setMaximumHeight(36)
        self.busy_label.setWordWrap(True)
        layout.addWidget(self.busy_label)

        # Composer panel mirrors a modern messenger: images above the draft, then
        # the prompt and a compact control rail below it.
        self.composer_frame = QFrame()
        self.composer_frame.setObjectName("aiComposer")
        composer_layout = QVBoxLayout(self.composer_frame)
        composer_layout.setContentsMargins(9, 8, 9, 8)
        composer_layout.setSpacing(7)

        self.pending_header = QWidget()
        pending_header_layout = QHBoxLayout(self.pending_header)
        pending_header_layout.setContentsMargins(0, 0, 0, 0)
        pending_header_layout.setSpacing(6)
        self.attachment_label = QLabel("Attachments")
        self.attachment_label.setObjectName("aiMuted")
        pending_header_layout.addWidget(self.attachment_label, 1)
        self.clear_attachment_btn = QPushButton("Clear")
        self.clear_attachment_btn.setObjectName("aiClearAttachments")
        self.clear_attachment_btn.setIcon(make_icon("clear", "#c8d4e6", 12))
        self.clear_attachment_btn.setToolTip("Remove pending images, PDF regions, and selected chat text")
        self.clear_attachment_btn.clicked.connect(self.clear_selected_region)
        pending_header_layout.addWidget(self.clear_attachment_btn)
        composer_layout.addWidget(self.pending_header)

        self.pending_selected_text_frame = QFrame()
        self.pending_selected_text_frame.setObjectName("aiPendingSelectedText")
        selected_text_layout = QHBoxLayout(self.pending_selected_text_frame)
        selected_text_layout.setContentsMargins(8, 5, 6, 5)
        selected_text_layout.setSpacing(7)
        quote_mark = QLabel("❝")
        quote_mark.setObjectName("aiPendingQuoteMark")
        selected_text_layout.addWidget(quote_mark, 0, Qt.AlignmentFlag.AlignTop)
        selected_text_details = QVBoxLayout()
        selected_text_details.setContentsMargins(0, 0, 0, 0)
        selected_text_details.setSpacing(2)
        self.pending_selected_text_title = QLabel("Selected chat passage")
        self.pending_selected_text_title.setObjectName("aiPendingSelectedTitle")
        selected_text_details.addWidget(self.pending_selected_text_title)
        self.pending_selected_text_preview = QLabel("")
        self.pending_selected_text_preview.setObjectName("aiPendingSelectedPreview")
        self.pending_selected_text_preview.setTextFormat(Qt.TextFormat.PlainText)
        self.pending_selected_text_preview.setWordWrap(True)
        self.pending_selected_text_preview.setMaximumHeight(48)
        selected_text_details.addWidget(self.pending_selected_text_preview)
        selected_text_layout.addLayout(selected_text_details, 1)
        self.remove_pending_selected_text_btn = QPushButton("×")
        self.remove_pending_selected_text_btn.setObjectName("aiPendingRemove")
        self.remove_pending_selected_text_btn.setFixedSize(22, 22)
        self.remove_pending_selected_text_btn.setToolTip("Remove selected chat text")
        self.remove_pending_selected_text_btn.clicked.connect(self._clear_pending_selected_text)
        selected_text_layout.addWidget(self.remove_pending_selected_text_btn, 0, Qt.AlignmentFlag.AlignTop)
        self.pending_selected_text_frame.hide()
        composer_layout.addWidget(self.pending_selected_text_frame)

        self.pending_images_scroll = QScrollArea()
        self.pending_images_scroll.setObjectName("aiPendingImages")
        self.pending_images_scroll.setWidgetResizable(True)
        self.pending_images_scroll.setFixedHeight(86)
        self.pending_images_scroll.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAsNeeded)
        self.pending_images_scroll.setVerticalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        self.pending_images_widget = QWidget()
        self.pending_images_layout = QHBoxLayout(self.pending_images_widget)
        self.pending_images_layout.setContentsMargins(2, 2, 2, 2)
        self.pending_images_layout.setSpacing(7)
        self.pending_images_layout.addStretch(1)
        self.pending_images_scroll.setWidget(self.pending_images_widget)
        composer_layout.addWidget(self.pending_images_scroll)
        self.pending_header.hide()
        self.pending_images_scroll.hide()

        self.prompt_edit = QTextEdit()
        self.prompt_edit.setObjectName("aiPrompt")
        self.prompt_edit.textChanged.connect(lambda *_: self.main_window._clear_context_help())
        prompt_font = self.prompt_edit.font()
        prompt_font.setPointSizeF(self._typing_font_pt)
        self.prompt_edit.setFont(prompt_font)
        self.prompt_edit.setStyleSheet(f"font-size: {self._typing_font_pt:.1f}pt;")
        self.prompt_edit.setPlaceholderText("Message Engo AI…  ·  Enter to send · Shift+Enter for a new line · Paste an image with Ctrl+V")
        self.prompt_edit.setMinimumHeight(58)
        self.prompt_edit.setMaximumHeight(116)
        self.prompt_edit.installEventFilter(self)
        self.prompt_edit.textChanged.connect(self._update_send_button_state)
        composer_layout.addWidget(self.prompt_edit)

        controls = QHBoxLayout()
        controls.setSpacing(6)
        self.add_region_btn = QPushButton("＋")
        self.add_region_btn.setObjectName("aiAddImage")
        self.add_region_btn.setFixedSize(37, 32)
        self.add_region_btn.setToolTip("Add an image, paste from clipboard, or select a region from the PDF")
        self.add_region_btn.clicked.connect(self._show_add_menu)
        controls.addWidget(self.add_region_btn)

        self.provider_combo = QComboBox()
        self.provider_combo.setObjectName("aiProviderSelector")
        self.provider_combo.setMinimumWidth(0)
        self.provider_combo.setMaximumWidth(155)
        self.provider_combo.setSizePolicy(QSizePolicy.Policy.Ignored, QSizePolicy.Policy.Fixed)
        for provider, label in AI_PROVIDER_LABELS.items():
            self.provider_combo.addItem(label, provider)
        preferred = self.settings.value("ai_provider", "deepseek", type=str)
        pref_index = max(0, self.provider_combo.findData(preferred))
        self.provider_combo.setCurrentIndex(pref_index)
        self.provider_combo.currentIndexChanged.connect(self._provider_changed)
        self.provider_combo.setToolTip("Choose which AI service receives your question")
        controls.addWidget(self.provider_combo, 2)

        self.model_combo = QComboBox()
        self.model_combo.setObjectName("aiModelSelector")
        self.model_combo.setEditable(True)
        self.model_combo.setInsertPolicy(QComboBox.InsertPolicy.NoInsert)
        self.model_combo.setMinimumWidth(0)
        self.model_combo.setMaximumWidth(225)
        self.model_combo.setSizePolicy(QSizePolicy.Policy.Ignored, QSizePolicy.Policy.Fixed)
        self.model_combo.setMinimumContentsLength(1)
        if self.model_combo.lineEdit() is not None:
            self.model_combo.lineEdit().setMinimumWidth(0)
            self.model_combo.lineEdit().setSizePolicy(QSizePolicy.Policy.Ignored, QSizePolicy.Policy.Fixed)
        self.model_combo.setToolTip("Choose the model for this chat. Refresh available models in AI provider settings.")
        self.model_combo.currentTextChanged.connect(self._chat_model_changed)
        controls.addWidget(self.model_combo, 3)

        self.include_context = QCheckBox("PDF context")
        self.include_context.setChecked(True)
        self.include_context.setToolTip("Include PDF text or page previews. Current-page actions always include the current page.")
        controls.addWidget(self.include_context)

        # One compact action button changes from Send to Stop while the AI is
        # generating. Keep stop_btn as an alias for older MainWindow callbacks;
        # it is the same widget, not a second control taking layout space.
        self.send_btn = QPushButton("Send")
        self.send_btn.setObjectName("aiSend")
        self.send_btn.setIcon(make_icon("send", "#ffffff", 16))
        self.send_btn.setMinimumWidth(77)
        self.send_btn.setMaximumWidth(77)
        self.send_btn.setMinimumHeight(34)
        self.send_btn.setDefault(True)
        self.send_btn.setToolTip("Send message")
        self.send_btn.clicked.connect(self._handle_send_stop_clicked)
        controls.addWidget(self.send_btn)
        self.stop_btn = self.send_btn
        composer_layout.addLayout(controls)

        voice_tools = QHBoxLayout()
        voice_tools.setSpacing(6)
        self.voice_btn = QPushButton("Ask by voice")
        self.voice_btn.setIcon(make_icon("mic", "#b7c6dc", 16))
        self.voice_btn.setIconSize(QSize(16, 16))
        self.voice_btn.setObjectName("aiVoice")
        self.voice_btn.setProperty("recording", False)
        self.voice_btn.setProperty("transcribing", False)
        self.voice_btn.setToolTip("Record one spoken question, send it to the selected AI, and read its answer aloud")
        self.voice_btn.clicked.connect(self.main_window.start_voice_input)
        voice_tools.addWidget(self.voice_btn, 1)
        self.read_answer_btn = QPushButton("Read latest")
        self.read_answer_btn.setIcon(make_icon("volume", "#b7c6dc", 16))
        self.read_answer_btn.setIconSize(QSize(16, 16))
        self.read_answer_btn.setObjectName("aiReadAnswer")
        self.read_answer_btn.setToolTip("Read the latest AI answer aloud")
        self.read_answer_btn.clicked.connect(self.main_window.speak_latest_answer)
        voice_tools.addWidget(self.read_answer_btn, 1)
        self.stop_audio_btn = QPushButton("Stop audio")
        self.stop_audio_btn.setIcon(make_icon("stop", "#b7c6dc", 15))
        self.stop_audio_btn.setIconSize(QSize(15, 15))
        self.stop_audio_btn.setObjectName("aiStopAudio")
        self.stop_audio_btn.setToolTip("Stop the spoken answer")
        self.stop_audio_btn.clicked.connect(self.main_window.stop_audio)
        voice_tools.addWidget(self.stop_audio_btn)
        composer_layout.addLayout(voice_tools)
        layout.addWidget(self.composer_frame)

        self._provider_changed(self.provider_combo.currentIndex())
        self._refresh_attachment_label()
        self.set_document("", "No PDF open")

    def prepare_chat_content_transition(self):
        """Keep the pane visually empty while its side-to-side motion runs."""
        self.composer_frame.setMaximumHeight(16777215)
        for bubble in getattr(self, "_chat_bubbles", []):
            try:
                bubble.setMaximumHeight(16777215)
            except RuntimeError:
                continue
        for widget in (getattr(self, "transcript", None), getattr(self, "composer_frame", None)):
            if widget is not None:
                widget.hide()

    def reveal_chat_content(self, stagger_messages: bool = True):
        """Reveal the chat surface after the panel has reached its final width."""
        # A close animation intentionally collapses maximumHeight. Always restore
        # the natural limits before a later re-open/exit reveal to avoid a stuck
        # one-pixel composer or messages after the full-screen transition.
        try:
            self.composer_frame.setMaximumHeight(16777215)
        except (RuntimeError, AttributeError):
            pass
        for bubble in getattr(self, "_chat_bubbles", []):
            try:
                bubble.setMaximumHeight(16777215)
            except (RuntimeError, AttributeError):
                continue
        for widget in (getattr(self, "transcript", None), getattr(self, "composer_frame", None)):
            if widget is not None:
                widget.show()
        self.updateGeometry()
        if stagger_messages:
            QTimer.singleShot(35, self._stagger_existing_messages)
        QTimer.singleShot(65, self._reflow_after_show)

    def _stagger_existing_messages(self):
        if not self.isVisible() or not self.transcript.isVisible():
            return
        # A short, cascading height reveal gives the conversation a clear arrival
        # after the pane slides in, without graphics effects on QTextBrowser trees.
        bubbles = list(getattr(self, "_chat_bubbles", [])[-14:])
        for index, bubble in enumerate(bubbles):
            try:
                target_height = max(42, int(bubble.sizeHint().height()))
                bubble.setMaximumHeight(1)
                animation = QPropertyAnimation(bubble, b"maximumHeight", bubble)
                animation.setDuration(118)
                animation.setStartValue(1)
                animation.setEndValue(target_height)
                animation.setEasingCurve(QEasingCurve.Type.OutCubic)
                animation.finished.connect(lambda b=bubble: b.setMaximumHeight(16777215))
                QTimer.singleShot(index * 17, animation.start)
            except (RuntimeError, AttributeError):
                continue

    def hide_chat_content_for_transition(self):
        """Collapse the content before the pane/focus surface moves away."""
        for widget in (getattr(self, "transcript", None), getattr(self, "composer_frame", None)):
            if widget is not None:
                widget.hide()

    def animate_chat_content_close(self):
        """Cascade message collapse as the dock begins sliding closed."""
        bubbles = list(getattr(self, "_chat_bubbles", [])[-14:])
        for index, bubble in enumerate(reversed(bubbles)):
            try:
                start_height = max(1, int(bubble.height() or bubble.sizeHint().height()))
                animation = QPropertyAnimation(bubble, b"maximumHeight", bubble)
                animation.setDuration(104)
                animation.setStartValue(start_height)
                animation.setEndValue(1)
                animation.setEasingCurve(QEasingCurve.Type.InCubic)
                self._closing_bubble_animations = getattr(self, "_closing_bubble_animations", [])
                self._closing_bubble_animations.append(animation)
                QTimer.singleShot(index * 8, animation.start)
            except (RuntimeError, AttributeError):
                continue
        composer = self.composer_frame
        try:
            composer_start = max(1, int(composer.height() or composer.sizeHint().height()))
            composer_animation = QPropertyAnimation(composer, b"maximumHeight", composer)
            composer_animation.setDuration(112)
            composer_animation.setStartValue(composer_start)
            composer_animation.setEndValue(1)
            composer_animation.setEasingCurve(QEasingCurve.Type.InCubic)
            self._closing_composer_animation = composer_animation
            composer_animation.start()
        except (RuntimeError, AttributeError):
            composer.hide()

    def _animate_bubble_in(self, bubble):
        """Use a light height reveal instead of rasterizing nested text widgets."""
        if bubble is not None:
            try:
                if self.transcript.isVisible() and self.isVisible():
                    target_height = max(42, int(bubble.sizeHint().height()))
                    bubble.setMaximumHeight(1)
                    animation = QPropertyAnimation(bubble, b"maximumHeight", bubble)
                    animation.setDuration(155)
                    animation.setStartValue(1)
                    animation.setEndValue(target_height)
                    animation.setEasingCurve(QEasingCurve.Type.OutCubic)
                    animation.finished.connect(lambda b=bubble: b.setMaximumHeight(16777215))
                    self._last_bubble_animation = animation
                    animation.start()
                else:
                    bubble.update()
            except RuntimeError:
                pass

    def set_focus_mode_button(self, focused: bool):
        if focused:
            self.focus_mode_btn.setIcon(make_icon("minimize", "#b7c6dc", 16))
            self.focus_mode_btn.setToolTip("Exit chat focus mode · show the PDF and app controls (Esc)")
            self.focus_mode_btn.setAccessibleName("Exit chat focus mode")
        else:
            self.focus_mode_btn.setIcon(make_icon("fullscreen", "#b7c6dc", 16))
            self.focus_mode_btn.setToolTip("Expand chat · hide the PDF and app controls (Ctrl+Shift+F)")
            self.focus_mode_btn.setAccessibleName("Enter chat focus mode")

    def _toggle_chat_search(self):
        visible = not self.chat_search_row.isVisible()
        self.chat_search_row.setVisible(visible)
        if visible:
            self.chat_search_edit.setFocus()
            self.chat_search_edit.selectAll()
        else:
            self.chat_search_edit.clear()
            self.chat_search_count.clear()
            self._chat_search_matches = []
            self._chat_search_current = -1

    def _reset_chat_search(self, _text=""):
        self._chat_search_matches = []
        self._chat_search_current = -1
        self.chat_search_count.clear()

    def _find_in_chat(self, backwards=False):
        query = self.chat_search_edit.text().strip()
        if not query:
            is_ar = str(self.settings.value("interface_language", "en", type=str) or "en").lower().startswith("ar")
            self.chat_search_count.setText("اكتب نصًا للبحث" if is_ar else "Type text")
            return
        matches = []
        for bubble_index, bubble in enumerate(self._chat_bubbles):
            body = getattr(bubble, "body", None)
            if body is None:
                continue
            document = body.document()
            cursor = QTextCursor(document)
            while True:
                found = document.find(query, cursor)
                if found.isNull():
                    break
                matches.append((bubble_index, found))
                cursor = QTextCursor(found)
                cursor.setPosition(found.selectionEnd())
        if not matches:
            self._chat_search_matches = []
            self._chat_search_current = -1
            is_ar = str(self.settings.value("interface_language", "en", type=str) or "en").lower().startswith("ar")
            self.chat_search_count.setText("لا توجد نتائج" if is_ar else "No match")
            return
        current_key = None
        if 0 <= self._chat_search_current < len(self._chat_search_matches):
            old_index, old_cursor = self._chat_search_matches[self._chat_search_current]
            current_key = (old_index, old_cursor.selectionStart())
        keys = [(i, c.selectionStart()) for i, c in matches]
        if current_key in keys:
            index = keys.index(current_key)
            index = (index + (-1 if backwards else 1)) % len(matches)
        else:
            index = len(matches) - 1 if backwards else 0
        self._chat_search_matches = matches
        self._chat_search_current = index
        bubble_index, found_cursor = matches[index]
        bubble = self._chat_bubbles[bubble_index]
        body = bubble.body
        body.setTextCursor(found_cursor)
        body.ensureCursorVisible()
        # The matching text lives inside a QTextBrowser embedded in the outer
        # transcript QScrollArea.  ensureCursorVisible() only affects the inner
        # browser, so explicitly scroll the OUTER area to the matched character.
        self._scroll_chat_search_match_into_view(body, found_cursor)
        self.chat_search_count.setText(f"{index + 1}/{len(matches)}")

    def _scroll_chat_search_match_into_view(self, body, match_cursor):
        """Bring the exact matched line into the visible transcript viewport."""
        def apply_scroll():
            try:
                if body is None or not body.isVisible():
                    return
                # Anchor at the beginning of the selection, not at the end.
                anchor = QTextCursor(match_cursor)
                anchor.setPosition(match_cursor.selectionStart())
                cursor_rect = body.cursorRect(anchor)
                content_point = body.mapTo(self.transcript_body, cursor_rect.topLeft())
                bar = self.transcript.verticalScrollBar()
                viewport_height = max(1, self.transcript.viewport().height())
                # Keep the hit comfortably inside the viewport (slightly above
                # center), so the selected text and its surrounding line are visible.
                desired_top = content_point.y() - int(viewport_height * 0.38)
                bar.setValue(max(bar.minimum(), min(bar.maximum(), desired_top)))
                self._update_chat_jump_button()
            except (RuntimeError, AttributeError):
                # The chat may have been switched/re-rendered while a queued
                # scroll was waiting; in that case there is nothing to move.
                return

        # Defer until Qt has applied cursor/layout geometry.  A second pass
        # handles late document/layout size updates in long Markdown replies.
        QTimer.singleShot(0, apply_scroll)
        QTimer.singleShot(60, apply_scroll)

    def _scroll_chat_to_bottom(self):
        try:
            bar = self.transcript.verticalScrollBar()
            bar.setValue(bar.maximum())
            QTimer.singleShot(45, lambda: bar.setValue(bar.maximum()))
            QTimer.singleShot(130, lambda: bar.setValue(bar.maximum()))
            QTimer.singleShot(0, self._update_chat_jump_button)
        except RuntimeError:
            pass

    def _update_chat_jump_button(self, *_args):
        if not hasattr(self, "jump_bottom_btn"):
            return
        bar = self.transcript.verticalScrollBar()
        self.jump_bottom_btn.setVisible(bar.maximum() - bar.value() > 24)

    def _set_activity(self, message: str, animate: bool = True):
        raw_message = str(message or "Working")
        is_ar = str(self.settings.value("interface_language", "en", type=str) or "en").lower().startswith("ar")
        if is_ar:
            raw_message = {
                "Engo AI is preparing a reply": "يجهّز Engo AI الإجابة",
                "Preparing request": "جارٍ تجهيز الطلب",
                "Receiving answer…": "جارٍ استلام الإجابة…",
                "Working": "جارٍ العمل",
            }.get(raw_message, raw_message)
        self._loading_status_text = raw_message
        self._loading_phase = 0
        if animate:
            if not self._loading_timer.isActive():
                self._loading_timer.start()
            self._animate_chat_loading()
        else:
            self._loading_timer.stop()
            self.busy_label.setText(self._loading_status_text)

    def _animate_chat_loading(self):
        dots = "." * (self._loading_phase % 4)
        self._loading_phase += 1
        if hasattr(self, "busy_label") and self.busy_label.isVisible():
            self.busy_label.setText(f"{self._loading_status_text}{dots}")
        if self._live_bubble is not None and not self._live_text:
            self._live_bubble.set_content(f"*{self._loading_status_text}{dots}*")

    def _stop_activity_animation(self):
        self._loading_timer.stop()

    def _popup_parent(self):
        """Return the real top-level owner for native popups opened by this embedded panel.

        AIChatPanel is a child widget inside the main splitter, not a top-level window.
        Passing it as the owner of a native QFileDialog/QMenu can make Qt use its
        child QWidgetWindow as a transient parent, producing:
        ``QWidgetWindow(aiPanelWindow) must be a top level window``.
        Always anchor popups to the actual application window instead.
        """
        owner = getattr(self, "main_window", None)
        try:
            if isinstance(owner, QWidget) and owner.isWindow():
                return owner
        except RuntimeError:
            pass
        try:
            top = self.window()
            if isinstance(top, QWidget) and top.isWindow():
                return top
        except RuntimeError:
            pass
        return None

    def _apply_popup_menu_style(self, menu: QMenu, theme: str | None = None):
        """Apply the same menu palette used by every other Engo popup."""
        if menu is None:
            return
        try:
            owner_settings = getattr(self.main_window, "settings", self.settings)
            owner_settings.sync()
            active_theme = theme if theme is not None else owner_settings.value("ui_theme", "dark", type=str)
        except Exception:
            active_theme = theme or "dark"
        _engo_apply_menu_consistency(menu, active_theme)
        self._add_menu_icon_color = _engo_menu_colors(active_theme)["fg"]

    def _show_add_menu(self):
        menu = QMenu(self._popup_parent())
        self._apply_popup_menu_style(menu)
        is_ar = str(self.settings.value("interface_language", "en", type=str) or "en").lower().startswith("ar")
        menu.setLayoutDirection(Qt.LayoutDirection.RightToLeft if is_ar else Qt.LayoutDirection.LeftToRight)
        icon_color = getattr(self, "_add_menu_icon_color", "#d9e2f0")
        danger_icon_color = "#dc777f" if normalize_ui_theme(self.settings.value("ui_theme", "dark", type=str)) != "light" else "#b54747"
        # Keep the PDF question-region action at the very top of the + menu.
        # It enters the existing AI region-selection workflow; the selected
        # crop is then attached to the chat as a pending visual context.
        ask_about_region = menu.addAction(
            make_icon("select", icon_color, 16),
            "تحديد منطقة للسؤال عنها" if is_ar else "Select area to ask AI about",
        )
        add_file = menu.addAction(make_icon("open", icon_color, 16), "إضافة صورة من ملف…" if is_ar else "Add image from file…")
        paste_image = menu.addAction(make_icon("paste", icon_color, 16), "لصق صورة من الحافظة" if is_ar else "Paste image from clipboard")
        menu.addSeparator()
        clear = menu.addAction(make_icon("clear", danger_icon_color, 15), "مسح المرفقات المعلّقة" if is_ar else "Clear pending attachments")
        chosen = menu.exec(self.add_region_btn.mapToGlobal(self.add_region_btn.rect().topLeft()))
        if chosen is ask_about_region:
            self.main_window.start_ai_region_selection()
        elif chosen is add_file:
            self.add_image_file()
        elif chosen is paste_image:
            self.paste_clipboard_image()
        elif chosen is clear:
            self.clear_selected_region()

    @staticmethod
    def _encode_qimage(image: QImage) -> bytes:
        if image.isNull():
            return b""
        data = QByteArray()
        buffer = QBuffer(data)
        if not buffer.open(QIODevice.OpenModeFlag.WriteOnly):
            return b""
        ok = image.convertToFormat(QImage.Format.Format_RGB32).save(buffer, "JPEG", 90)
        buffer.close()
        return bytes(data) if ok else b""

    def _add_pending_image(self, data: bytes, label: str = "Pasted image", page_index=None):
        if not self.document_path:
            is_ar = str(self.settings.value("interface_language", "en", type=str) or "en").lower().startswith("ar")
            self.main_window.show_status("افتح ملف PDF قبل إرفاق الصور" if is_ar else "Open a PDF before attaching images")
            return
        try:
            with Image.open(io.BytesIO(bytes(data))) as source:
                image = source.convert("RGB")
                image.thumbnail((1800, 1800), Image.Resampling.LANCZOS)
                output = io.BytesIO()
                image.save(output, format="JPEG", quality=88, optimize=True)
                normalized = output.getvalue()
            regions = self.selected_regions.setdefault(self.document_path, [])
            is_ar = str(self.settings.value("interface_language", "en", type=str) or "en").lower().startswith("ar")
            fallback_label = (f"صورة {len(regions) + 1}" if is_ar else f"Image {len(regions) + 1}")
            regions.append({
                "page_index": int(page_index) if page_index is not None else None,
                "data": normalized,
                "label": str(label or fallback_label),
            })
            self._refresh_attachment_label()
            is_ar = str(self.settings.value("interface_language", "en", type=str) or "en").lower().startswith("ar")
            self.main_window.show_status((f"تم إرفاق {regions[-1]['label']}" if is_ar else f"Attached {regions[-1]['label']}"))
        except Exception as exc:
            is_ar = str(self.settings.value("interface_language", "en", type=str) or "en").lower().startswith("ar")
            QMessageBox.warning(self._popup_parent(), "إضافة صورة" if is_ar else "Add image", (f"تعذر تحميل هذه الصورة:\n{exc}" if is_ar else f"Could not load this image:\n{exc}"))

    def add_image_file(self):
        if not self.document_path:
            is_ar = str(self.settings.value("interface_language", "en", type=str) or "en").lower().startswith("ar")
            self.main_window.show_status("افتح ملف PDF قبل إرفاق الصور" if is_ar else "Open a PDF before attaching images")
            return
        path = _engo_file_dialog(
            self._popup_parent(), "Attach image", "إرفاق صورة", str(Path.home()),
            "Images (*.png *.jpg *.jpeg *.webp *.bmp *.tif *.tiff);;All files (*.*)",
            native=True,
        )
        if not path:
            return
        try:
            with Image.open(path) as source:
                image = source.convert("RGB")
                image.thumbnail((1800, 1800), Image.Resampling.LANCZOS)
                output = io.BytesIO()
                image.save(output, format="JPEG", quality=88, optimize=True)
                self._add_pending_image(output.getvalue(), Path(path).name)
        except Exception as exc:
            is_ar = str(self.settings.value("interface_language", "en", type=str) or "en").lower().startswith("ar")
            QMessageBox.warning(self._popup_parent(), "إرفاق صورة" if is_ar else "Attach image", (f"تعذرت قراءة الصورة:\n{exc}" if is_ar else f"Could not read image:\n{exc}"))

    def paste_clipboard_image(self):
        image = QApplication.clipboard().image()
        if image.isNull():
            is_ar = str(self.settings.value("interface_language", "en", type=str) or "en").lower().startswith("ar")
            self.main_window.show_status("لا توجد صورة في الحافظة للصقها" if is_ar else "Clipboard has no image to paste")
            return
        data = self._encode_qimage(image)
        if data:
            is_ar = str(self.settings.value("interface_language", "en", type=str) or "en").lower().startswith("ar")
            self._add_pending_image(data, "صورة من الحافظة" if is_ar else "Pasted image")
        else:
            is_ar = str(self.settings.value("interface_language", "en", type=str) or "en").lower().startswith("ar")
            self.main_window.show_status("تعذرت قراءة الصورة من الحافظة" if is_ar else "Could not read the clipboard image")

    def _pdf_actions_is_arabic(self) -> bool:
        return str(self.settings.value("interface_language", "en", type=str) or "en").lower().startswith("ar")

    def _load_custom_pdf_actions(self) -> list[dict]:
        raw = self.settings.value("ai_custom_pdf_actions", [])
        if isinstance(raw, str):
            try:
                raw = json.loads(raw)
            except Exception:
                raw = []
        if not isinstance(raw, (list, tuple)):
            return []
        actions = []
        for item in raw:
            if not isinstance(item, dict):
                continue
            title = str(item.get("title") or "").strip()
            prompt = str(item.get("prompt") or "").strip()
            if not title or not prompt:
                continue
            mode = str(item.get("mode") or "document").strip().lower()
            if mode not in {"page", "document"}:
                mode = "document"
            actions.append({
                "id": str(item.get("id") or uuid.uuid4().hex),
                "title": title[:70],
                "prompt": prompt[:6000],
                "mode": mode,
            })
        return actions

    def _save_custom_pdf_actions(self, actions: list[dict]):
        self.settings.setValue("ai_custom_pdf_actions", actions)
        self.settings.sync()

    def _add_custom_pdf_action(self):
        is_ar = self._pdf_actions_is_arabic()
        title, ok = QInputDialog.getText(
            self._popup_parent(),
            "إضافة إجراء PDF" if is_ar else "Add PDF action",
            "اسم الإجراء:" if is_ar else "Action name:",
            QLineEdit.EchoMode.Normal,
        )
        if not ok or not str(title).strip():
            return
        prompt, ok = QInputDialog.getMultiLineText(
            self._popup_parent(),
            "تعليمات الإجراء" if is_ar else "Action instructions",
            "ما الذي تريد من Engo AI تنفيذه؟" if is_ar else "What should Engo AI do?",
            "",
        )
        if not ok or not str(prompt).strip():
            return
        scope, ok = QInputDialog.getItem(
            self._popup_parent(),
            "نطاق الإجراء" if is_ar else "Action scope",
            "يُطبّق على:" if is_ar else "Apply to:",
            ["صفحة PDF الحالية", "ملف PDF بالكامل"] if is_ar else ["Current PDF page", "Entire PDF"],
            1,
            False,
        )
        if not ok:
            return
        mode = "page" if scope in {"صفحة PDF الحالية", "Current PDF page"} else "document"
        actions = self._load_custom_pdf_actions()
        actions.append({
            "id": uuid.uuid4().hex,
            "title": str(title).strip()[:70],
            "prompt": str(prompt).strip()[:6000],
            "mode": mode,
        })
        self._save_custom_pdf_actions(actions)
        self.main_window.show_status("تمت إضافة إجراء PDF" if is_ar else "PDF action added")
        QTimer.singleShot(120, self._show_pdf_actions_menu)

    def _delete_custom_pdf_action(self, action_id: str):
        actions = self._load_custom_pdf_actions()
        updated = [item for item in actions if item.get("id") != str(action_id)]
        if len(updated) != len(actions):
            self._save_custom_pdf_actions(updated)
            self.main_window.show_status("تم حذف الإجراء المخصص" if self._pdf_actions_is_arabic() else "Custom action deleted")

    def _show_pdf_actions_menu(self):
        is_ar = self._pdf_actions_is_arabic()
        menu = QMenu(self._popup_parent())
        # Read the currently active theme from the owning window (the chat panel may
        # hold a QSettings instance created before the last theme change).
        theme_settings = self.settings
        try:
            owner = getattr(self, "main_window", None)
            if owner is not None and hasattr(owner, "settings"):
                theme_settings = owner.settings
            theme_settings.sync()
            theme = normalize_ui_theme(theme_settings.value("ui_theme", "dark", type=str))
        except Exception:
            theme = normalize_ui_theme(self.settings.value("ui_theme", "dark", type=str))
        menu_colors = _engo_menu_colors(theme)
        menu_palette = {
            "bg": menu_colors["bg"],
            "text": menu_colors["fg"],
            "border": menu_colors["border"],
            "hover": menu_colors["hover"],
            "muted": menu_colors["muted"],
        }
        menu_text = menu_colors["fg"]
        trash_color = "#b54747" if theme == "light" else "#e17b89"
        _engo_apply_menu_consistency(menu, theme, is_ar)
        # Embedded custom-action rows use the same palette as their parent menu.
        mp = QPalette(menu.palette())

        builtins = [
            ("تلخيص ملف PDF بالكامل" if is_ar else "Summarize entire PDF",
             "Summarize the entire PDF in clear sections. Include key ideas, definitions, formulas, examples, and a short final recap. Cite page numbers when possible.", "document", "summarize"),
            ("مراجعة ملف PDF بالكامل" if is_ar else "Review entire PDF",
             "Review the entire PDF as a study assistant. Identify its subject, structure, key claims, unclear parts, and what deserves attention. Do not solve a specific problem unless needed.", "document", "review"),
            ("اسأل عن الصفحة الحالية" if is_ar else "Ask about current page",
             "Explain the current PDF page and answer questions about its text, images, charts, formulas, and handwriting. Mention the page number and distinguish visible facts from assumptions.", "page", "chat"),
            ("قراءة النص والكتابة اليدوية في الصفحة" if is_ar else "Read text / handwriting on current page",
             "Transcribe all legible text on the current PDF page, including handwriting, equations, and labels. Preserve line breaks and mark uncertain words with [?].", "page", "ocr"),
            ("إضافة منطقة من الصفحة إلى الرسالة التالية" if is_ar else "Add region from page to next message",
             None, "selection", "select"),
        ]
        builtin_actions = []
        for label, prompt, mode, icon_name in builtins:
            action = menu.addAction(make_icon(icon_name, menu_text, 16), label)
            builtin_actions.append((action, prompt, mode))
        custom_actions = self._load_custom_pdf_actions()
        if custom_actions:
            menu.addSeparator()
            custom_header = menu.addAction("إجراءات مخصصة" if is_ar else "My actions")
            custom_header.setEnabled(False)
            for item in custom_actions:
                row = QWidget(menu)
                row.setAttribute(Qt.WidgetAttribute.WA_StyledBackground, True)
                row.setAutoFillBackground(True)
                row.setPalette(mp)
                row.setLayoutDirection(Qt.LayoutDirection.RightToLeft if is_ar else Qt.LayoutDirection.LeftToRight)
                row.setStyleSheet(f"QWidget {{ background:{menu_palette['bg']}; color:{menu_palette['text']}; }}")
                row_layout = QHBoxLayout(row)
                row_layout.setContentsMargins(4, 2, 4, 2)
                row_layout.setSpacing(6)
                run_button = QPushButton(item["title"])
                run_button.setCursor(Qt.CursorShape.PointingHandCursor)
                run_button.setStyleSheet(
                    f"QPushButton {{ text-align:{'right' if is_ar else 'left'}; color:{menu_text}; background:{menu_palette['bg']}; border:0; padding:7px 9px; min-width:190px; }} "
                    f"QPushButton:hover {{ color:{menu_text}; background:{menu_palette['hover']}; border-radius:4px; }}"
                )
                delete_button = QToolButton()
                delete_button.setCursor(Qt.CursorShape.PointingHandCursor)
                delete_button.setToolTip("حذف هذا الإجراء" if is_ar else "Delete this custom action")
                delete_button.setIcon(make_icon("trash", trash_color, 15))
                delete_button.setFixedSize(27, 27)
                delete_button.setStyleSheet(
                    f"QToolButton {{ color:{menu_palette['text']}; background:transparent; border:0; border-radius:4px; }} "
                    "QToolButton:hover { background:rgba(220,70,70,0.22); }"
                )
                row_layout.addWidget(run_button, 1)
                row_layout.addWidget(delete_button, 0)
                widget_action = QWidgetAction(menu)
                widget_action.setDefaultWidget(row)
                menu.addAction(widget_action)
                run_button.clicked.connect(
                    lambda _checked=False, p=item["prompt"], m=item["mode"], target=menu: (target.close(), self.send_quick(p, m))
                )
                delete_button.clicked.connect(
                    lambda _checked=False, aid=item["id"], target=menu: (target.close(), self._delete_custom_pdf_action(aid))
                )
        menu.addSeparator()
        add_action = menu.addAction(
            make_icon("plus", menu_text, 16),
            "إضافة إجراء…" if is_ar else "Add action…",
        )
        add_action.setToolTip("أنشئ إجراءً مخصصًا واحفظه في هذه القائمة" if is_ar else "Create and save a custom action in this menu")
        chosen = menu.exec(self.pdf_actions_btn.mapToGlobal(self.pdf_actions_btn.rect().bottomLeft()))
        if chosen is add_action:
            self._add_custom_pdf_action()
            return
        for action, prompt, mode in builtin_actions:
            if chosen is action:
                if mode == "selection":
                    self.main_window.start_ai_region_selection()
                else:
                    self.send_quick(prompt, mode)
                return

    def eventFilter(self, obj, event):
        chat_view = self.chat_combo.view() if hasattr(self, "chat_combo") else None
        if chat_view is not None and obj is chat_view.viewport():
            event_type = event.type()
            if event_type in (QEvent.Type.MouseButtonPress, QEvent.Type.MouseButtonRelease) and event.button() == Qt.MouseButton.LeftButton:
                point = event.position().toPoint()
                index = chat_view.indexAt(point)
                row_rect = chat_view.visualRect(index) if index.isValid() else QRect()
                in_delete_area = bool(index.isValid() and point.x() >= row_rect.right() - 36)
                if event_type == QEvent.Type.MouseButtonPress:
                    self._chat_delete_pressed_id = int(self.chat_combo.itemData(index.row())) if in_delete_area and self.chat_combo.itemData(index.row()) is not None else None
                    if self._chat_delete_pressed_id is not None:
                        return True
                else:
                    pressed_id = self._chat_delete_pressed_id
                    self._chat_delete_pressed_id = None
                    if pressed_id is not None:
                        if in_delete_area and int(self.chat_combo.itemData(index.row()) or -1) == pressed_id:
                            self.chat_combo.hidePopup()
                            QTimer.singleShot(0, lambda value=pressed_id: self._delete_saved_chat(value))
                        return True
        if obj is self.prompt_edit and event.type() == QEvent.Type.KeyPress:
            modifiers = event.modifiers()
            if event.key() in (Qt.Key.Key_Return, Qt.Key.Key_Enter):
                if (modifiers & Qt.KeyboardModifier.ShiftModifier) or (modifiers & Qt.KeyboardModifier.ControlModifier):
                    # Shift+Enter (and Ctrl+Enter for compatibility) inserts a
                    # newline. Plain Enter sends the current message.
                    self.prompt_edit.insertPlainText("\n")
                else:
                    self.send_typed()
                return True
            if event.key() == Qt.Key.Key_V and modifiers & Qt.KeyboardModifier.ControlModifier:
                mime = QApplication.clipboard().mimeData()
                if mime and mime.hasImage():
                    self.paste_clipboard_image()
                    return True
        return super().eventFilter(obj, event)

    def _chat_model_preference_key(self, provider: str) -> str:
        scope_key = str(self.chat_scope_key or self.document_path or "")
        chat_id = int(self.active_chat_ids.get(scope_key, 0) or 0) if scope_key else 0
        return f"ai_chat_{chat_id}_model_{provider}" if chat_id > 0 else f"ai_chat_model_{provider}"

    def _store_chat_model(self, provider: str, model: str):
        provider = str(provider or "deepseek")
        model = str(model or "").strip()
        if not model:
            return
        # Remember the last chosen model as the default for future conversations,
        # but keep an independent override for each existing conversation.
        self.settings.setValue(f"ai_chat_model_{provider}", model)
        self.settings.setValue(self._chat_model_preference_key(provider), model)

    def _provider_changed(self, _index):
        provider = str(self.provider_combo.currentData() or "deepseek")
        self.settings.setValue("ai_provider", provider)
        self.model_combo.blockSignals(True)
        self.model_combo.clear()
        try:
            raw = self.settings.value(f"ai_available_models_{provider}", "[]", type=str)
            model_ids = json.loads(raw) if isinstance(raw, str) else list(raw or [])
        except Exception:
            model_ids = []
        saved = str(self.settings.value(self._chat_model_preference_key(provider),
                     self.settings.value(f"ai_chat_model_{provider}",
                     self.settings.value(f"ai_model_{provider}", AI_DEFAULT_MODELS[provider], type=str), type=str), type=str)
                     or AI_DEFAULT_MODELS[provider]).strip()
        if not model_ids:
            model_ids = [AI_DEFAULT_MODELS[provider]]
        for model_id in model_ids:
            self.model_combo.addItem(str(model_id), str(model_id))
        idx = self.model_combo.findData(saved)
        if idx >= 0:
            self.model_combo.setCurrentIndex(idx)
        else:
            self.model_combo.setEditText(saved)
        self.model_combo.blockSignals(False)
        self.model_combo.setToolTip(f"Model for this conversation · {len(model_ids)} model(s) available. Refresh the list in AI provider settings.")

    def _chat_model_changed(self, model_text):
        provider = str(self.provider_combo.currentData() or "deepseek")
        self._store_chat_model(provider, str(model_text or "").strip())


    def _scope_key_for_path(self, path: str | None = None) -> str:
        target = os.path.abspath(path or self.document_path) if (path or self.document_path) else ""
        if not target:
            return ""
        if target == self.document_path and self.chat_scope_key:
            return self.chat_scope_key
        resolver = getattr(self.main_window, "_ai_chat_scope_key", None)
        return resolver(target) if callable(resolver) else target

    def _chat_pref_key(self, scope_key: str) -> str:
        value = str(scope_key or "")
        canonical = value if value.startswith("ENGO_DUAL::") else os.path.abspath(value)
        digest = hashlib.sha1(canonical.encode("utf-8", errors="replace")).hexdigest()
        return f"ai_last_chat_{digest}"

    def _dual_chat_pair_label(self, scope_key: str | None = None) -> str:
        """Resolve a stable, order-independent display label from the linked PDF pair."""
        scope = str(scope_key or self.chat_scope_key or self.document_path or "")
        if not scope.startswith("ENGO_DUAL::"):
            return ""
        try:
            host = self.main_window
            lookup = getattr(host, "_open_document_tab_by_path", None)
            resolver = getattr(host, "_linked_pair_for_tab", None)
            tab = lookup(self.document_path) if callable(lookup) and self.document_path else None
            primary, secondary = resolver(tab) if callable(resolver) and tab is not None else (None, None)
            pair_paths = None
            if primary is not None and secondary is not None:
                pair_paths = [primary.path, secondary.path]
            if pair_paths is None:
                current = os.path.normcase(os.path.abspath(self.document_path or ""))
                for primary_path, secondary_path in getattr(host, "_linked_pdf_pairs", {}).items():
                    first = os.path.normcase(os.path.abspath(primary_path))
                    second = os.path.normcase(os.path.abspath(secondary_path))
                    if current in (first, second):
                        pair_paths = [primary_path, secondary_path]
                        break
            if pair_paths:
                paths = sorted(
                    [os.path.abspath(value) for value in pair_paths],
                    key=lambda value: os.path.normcase(value),
                )
                names = [Path(value).stem or Path(value).name for value in paths]
                return " + ".join(names)
        except Exception:
            pass
        return "Dual File Engo AI Chat"

    def _refresh_chat_combo(self, preferred_id=None, create_if_empty=True):
        if not self.document_path:
            return
        scope_key = self.chat_scope_key or self.document_path
        if scope_key.startswith("ENGO_DUAL::"):
            pair_label = self._dual_chat_pair_label(scope_key)
            self.chat_store.update_dual_chat_titles(scope_key, pair_label)
        else:
            pair_label = None
        chats = self.chat_store.list_chats(scope_key)
        if not chats and create_if_empty:
            preferred_id = self.chat_store.create_chat(scope_key, pair_label)
            if scope_key.startswith("ENGO_DUAL::"):
                self.chat_store.update_dual_chat_titles(scope_key, pair_label)
            chats = self.chat_store.list_chats(scope_key)
        if preferred_id is None:
            preferred_id = self.active_chat_ids.get(scope_key)
        if preferred_id is None:
            stored = self.settings.value(self._chat_pref_key(scope_key), 0, type=int)
            preferred_id = stored or (int(chats[0]["id"]) if chats else None)
        valid_ids = {int(item["id"]) for item in chats}
        if preferred_id not in valid_ids and chats:
            preferred_id = int(chats[0]["id"])
        self._loading_chat_combo = True
        try:
            self.chat_combo.clear()
            for chat in chats:
                self.chat_combo.addItem(str(chat["title"] or "New conversation"), int(chat["id"]))
            selected_index = self.chat_combo.findData(preferred_id) if preferred_id is not None else -1
            if selected_index >= 0:
                self.chat_combo.setCurrentIndex(selected_index)
        finally:
            self._loading_chat_combo = False
        if preferred_id is not None:
            preferred_id = int(preferred_id)
            self.active_chat_ids[scope_key] = preferred_id
            self.settings.setValue(self._chat_pref_key(scope_key), preferred_id)

    def _transcript_history_signature(self, scope_key=None):
        """Cheap in-memory signature used to detect a chat updated off-screen."""
        scope_key = str(scope_key if scope_key is not None else (self.chat_scope_key or self.document_path))
        history = self.messages_by_document.get(scope_key, [])
        tail = []
        for item in history[-3:]:
            content = str(item.get("content", ""))
            digest = hashlib.sha1(content.encode("utf-8", errors="replace")).hexdigest()
            tail.append((str(item.get("created_at", "")), str(item.get("role", "")), digest,
                         len(item.get("attachments", []) or [])))
        return (len(history), tuple(tail))

    def _store_active_transcript_page_state(self):
        key = self._active_transcript_page_key
        if key is None:
            return
        entry = self._transcript_pages.get(key)
        if entry is None:
            return
        entry.update({
            "body": self.transcript_body,
            "layout": self.transcript_layout,
            "bubbles": list(self._chat_bubbles),
            "live_bubble": self._live_bubble,
            "live_path": self._live_path,
            "live_text": self._live_text,
            "scroll": int(self.transcript.verticalScrollBar().value()),
            # Keep the signature captured at render time. The active chat scope may
            # already have changed when this method stores the outgoing page.
            "viewport_width": self._initial_transcript_bubble_width(),
        })

    def _activate_transcript_page(self, force_render=False):
        """Switch to the cached widget tree for the selected document/chat."""
        self._store_active_transcript_page_state()
        # Detach the outgoing body without deleting it; cached transcript pages
        # live outside the scroll area until they become active again. This avoids
        # QStackedWidget's max-size-across-pages behavior, which can create blank
        # scroll space when a short chat is shown after a long one.
        detached_body = self.transcript.takeWidget()
        scope_key = self.chat_scope_key or self.document_path or "__welcome__"
        chat_id = int(self.active_chat_ids.get(scope_key, 0) or 0)
        key = (str(scope_key), chat_id)
        current_width = self._initial_transcript_bubble_width()
        entry = self._transcript_pages.get(key)
        is_new = entry is None
        if is_new:
            # Reuse the initial page once; later pages get their own persistent
            # widget/layout so returning to a document does not recreate its bubbles.
            if self._active_transcript_page_key is None and not self._transcript_pages:
                body = detached_body or self.transcript_body
                transcript_layout = self.transcript_layout
            else:
                body = QWidget()
                body.setObjectName("aiTranscriptBody")
                transcript_layout = QVBoxLayout(body)
                transcript_layout.setContentsMargins(9, 9, 9, 10)
                transcript_layout.setSpacing(8)
                transcript_layout.addStretch(1)
            entry = {
                "body": body, "layout": transcript_layout, "bubbles": [],
                "live_bubble": None, "live_path": "", "live_text": "",
                "scroll": 0, "history_signature": None,
                "viewport_width": current_width,
            }
            self._transcript_pages[key] = entry
        self._active_transcript_page_key = key
        # Dict insertion order doubles as a small LRU order for page widgets.
        self._transcript_pages[key] = self._transcript_pages.pop(key)
        self.transcript_body = entry["body"]
        self.transcript_layout = entry["layout"]
        self._chat_bubbles = list(entry.get("bubbles", []))
        self._live_bubble = entry.get("live_bubble")
        self._live_path = str(entry.get("live_path", ""))
        self._live_text = str(entry.get("live_text", ""))
        self.transcript.setWidget(self.transcript_body)
        signature = self._transcript_history_signature()
        needs_render = bool(force_render or is_new or entry.get("history_signature") != signature
                            or abs(int(entry.get("viewport_width", current_width)) - current_width) >= 8)
        if needs_render:
            self._render_transcript()
        else:
            saved_scroll = int(entry.get("scroll", 0))
            page_key = key
            QTimer.singleShot(0, lambda k=page_key, v=saved_scroll:
                               self.transcript.verticalScrollBar().setValue(v)
                               if self._active_transcript_page_key == k else None)
            self._update_chat_jump_button()
        # Bound retained pages to avoid accumulating widgets indefinitely.
        while len(self._transcript_pages) > self._transcript_page_cache_limit:
            oldest_key = next(iter(self._transcript_pages))
            if oldest_key == self._active_transcript_page_key:
                self._transcript_pages[oldest_key] = self._transcript_pages.pop(oldest_key)
                continue
            stale = self._transcript_pages.pop(oldest_key)
            stale_body = stale.get("body")
            if stale_body is not None:
                stale_body.deleteLater()

    def _activate_chat_for_document(self, path: str):
        path = os.path.abspath(path)
        self.document_path = path
        resolver = getattr(self.main_window, "_ai_chat_scope_key", None)
        # Always ask the window for the current scope. The same primary PDF can
        # switch between an individual chat and a pair-owned chat after Link/Unlink.
        resolved_scope = resolver(path) if callable(resolver) else path
        self.chat_scope_key = str(resolved_scope or path)
        existing = self.active_chat_ids.get(self.chat_scope_key)
        self._refresh_chat_combo(existing)
        self._provider_changed(self.provider_combo.currentIndex())
        chat_id = self.active_chat_ids.get(self.chat_scope_key)
        loaded_id = self._loaded_chat_ids_by_scope.get(self.chat_scope_key)
        if chat_id is not None and (loaded_id != int(chat_id) or self.chat_scope_key not in self.messages_by_document):
            self.messages_by_document[self.chat_scope_key] = self.chat_store.load_messages(chat_id)
            self._loaded_chat_ids_by_scope[self.chat_scope_key] = int(chat_id)
        elif self.chat_scope_key not in self.messages_by_document:
            self.messages_by_document[self.chat_scope_key] = []

    def _delete_saved_chat(self, chat_id: int):
        scope_key = self.chat_scope_key or self.document_path
        if not scope_key or self._busy:
            return
        chat_id = int(chat_id)
        title = self.chat_store.get_chat_title(chat_id)
        is_ar = str(self.settings.value("interface_language", "en", type=str) or "en").lower().startswith("ar")
        answer = QMessageBox.question(
            self._popup_parent(),
            "حذف المحادثة؟" if is_ar else "Delete conversation?",
            (f"هل تريد حذف محادثة '{title}' نهائيًا؟\n\nسيتم حذف جميع الرسائل والصور المرفقة بهذه المحادثة. لا يمكن التراجع عن هذا الإجراء." if is_ar else f"Delete '{title}' permanently?\n\nAll messages and attached images in this conversation will be removed. This cannot be undone."),
            QMessageBox.StandardButton.Yes | QMessageBox.StandardButton.No,
            QMessageBox.StandardButton.No,
        )
        if answer != QMessageBox.StandardButton.Yes:
            return

        current_id = self.active_chat_ids.get(scope_key)
        was_active = current_id is not None and int(current_id) == chat_id
        if not self.chat_store.delete_chat(chat_id):
            QMessageBox.warning(self._popup_parent(), "تعذر حذف المحادثة" if is_ar else "Delete conversation", "لم يتم العثور على المحادثة أو ربما حُذفت بالفعل." if is_ar else "The conversation could not be found or was already deleted.")
            return

        if was_active:
            self.active_chat_ids.pop(scope_key, None)
            self.messages_by_document.pop(scope_key, None)
            self.settings.remove(self._chat_pref_key(scope_key))
            remaining = self.chat_store.list_chats(scope_key)
            next_id = int(remaining[0]["id"]) if remaining else None
            self._refresh_chat_combo(next_id, create_if_empty=False)
            active_id = self.active_chat_ids.get(scope_key)
            self.messages_by_document[scope_key] = self.chat_store.load_messages(active_id) if active_id else []
            if active_id:
                self._loaded_chat_ids_by_scope[scope_key] = int(active_id)
            else:
                self._loaded_chat_ids_by_scope.pop(scope_key, None)
            self._activate_transcript_page(force_render=True)
            deleted_page = self._transcript_pages.pop((str(scope_key), chat_id), None)
            if deleted_page is not None:
                deleted_body = deleted_page.get("body")
                if deleted_body is not None and deleted_body is not self.transcript_body:
                    deleted_body.deleteLater()
        else:
            self._refresh_chat_combo(current_id)
        self.main_window.show_status("تم حذف المحادثة" if is_ar else "Conversation deleted")

    def delete_all_conversations(self) -> int:
        """Remove all saved chats, then rebuild the active transcript as a fresh conversation."""
        if self._busy:
            raise RuntimeError("Wait for the current AI response to finish before deleting conversations.")
        count = self.chat_store.delete_all_chats()
        for key in list(self.settings.allKeys()):
            if key.startswith("ai_last_chat_") or re.match(r"^ai_chat_\d+_model_", key):
                self.settings.remove(key)
        self.settings.sync()

        self._clear_pending_selected_text()
        self.selected_regions.clear()
        self.messages_by_document.clear()
        self.active_chat_ids.clear()
        self._loaded_chat_ids_by_scope.clear()
        self._chat_bubbles = []
        self._live_bubble = None
        self._live_path = ""
        self._live_text = ""
        current_body = getattr(self, "transcript_body", None)
        for entry in list(self._transcript_pages.values()):
            body = entry.get("body") if isinstance(entry, dict) else None
            if body is not None and body is not current_body:
                try:
                    body.deleteLater()
                except RuntimeError:
                    pass
        self._transcript_pages.clear()
        self._active_transcript_page_key = None

        scope_key = self.chat_scope_key or self.document_path
        if self.document_path and scope_key:
            self._refresh_chat_combo(preferred_id=None, create_if_empty=True)
            fresh_id = self.active_chat_ids.get(scope_key)
            self.messages_by_document[scope_key] = []
            if fresh_id:
                self._loaded_chat_ids_by_scope[scope_key] = int(fresh_id)
            self._activate_transcript_page(force_render=True)
        else:
            self._loading_chat_combo = True
            try:
                self.chat_combo.clear()
            finally:
                self._loading_chat_combo = False
            self._render_transcript()
        self._refresh_attachment_label()
        return count

    def _select_saved_chat(self, index):
        if self._loading_chat_combo or not self.document_path or index < 0 or self._busy:
            return
        self._clear_pending_selected_text()
        chat_id = self.chat_combo.itemData(index)
        if chat_id is None:
            return
        chat_id = int(chat_id)
        scope_key = self.chat_scope_key or self.document_path
        self.active_chat_ids[scope_key] = chat_id
        self.settings.setValue(self._chat_pref_key(scope_key), chat_id)
        self._provider_changed(self.provider_combo.currentIndex())
        self.messages_by_document[scope_key] = self.chat_store.load_messages(chat_id)
        self._loaded_chat_ids_by_scope[scope_key] = int(chat_id)
        self._activate_transcript_page(force_render=True)

    def _new_conversation(self):
        if not self.document_path or self._busy:
            return
        self._clear_pending_selected_text()
        scope_key = self.chat_scope_key or self.document_path
        title = self._dual_chat_pair_label(scope_key) if scope_key.startswith("ENGO_DUAL::") else None
        chat_id = self.chat_store.create_chat(scope_key, title)
        if scope_key.startswith("ENGO_DUAL::"):
            self.chat_store.update_dual_chat_titles(scope_key, title)
        self.active_chat_ids[scope_key] = chat_id
        self.settings.setValue(self._chat_pref_key(scope_key), chat_id)
        self._provider_changed(self.provider_combo.currentIndex())
        self.messages_by_document[scope_key] = []
        self._loaded_chat_ids_by_scope[scope_key] = int(chat_id)
        self.selected_regions.pop(self.document_path, None)
        self._refresh_chat_combo(chat_id)
        self._refresh_attachment_label()
        self._activate_transcript_page(force_render=True)
        self.prompt_edit.setFocus()

    def set_document(self, path: str, name: str):
        new_document_path = os.path.abspath(path) if path else ""
        if new_document_path != self.document_path and self._pending_selected_text:
            self._clear_pending_selected_text()
        self.document_path = new_document_path
        self.document_name = name or "No PDF open"
        is_ar = str(self.settings.value("interface_language", "en", type=str) or "en").lower().startswith("ar")
        if not self.document_path:
            self.chat_scope_key = ""
            self.chat_heading.setText("محادثة Engo AI" if is_ar else "Engo AI Chat")
            self.chat_subtitle.setText("مساعدك الدراسي لملفات PDF" if is_ar else "Your PDF study assistant")
            self.document_label.setText("افتح ملف PDF لطرح الأسئلة حوله." if is_ar else "Open a PDF to ask questions about it.")
            self.prompt_edit.setEnabled(False)
            self._update_send_button_state()
            self.add_region_btn.setEnabled(False)
            self.clear_attachment_btn.setEnabled(False)
            self.pdf_actions_btn.setEnabled(False)
            self.new_chat_btn.setEnabled(False)
            self.chat_combo.clear()
            self.chat_combo.setEnabled(False)
            self.include_context.setEnabled(False)
            self.voice_btn.setEnabled(False)
            self.read_answer_btn.setEnabled(False)
            self._refresh_attachment_label()
            self._activate_transcript_page()
            return
        self._activate_chat_for_document(self.document_path)
        is_office_source = is_office_document(self.document_path)
        if is_office_source:
            # Office context arrives through selected native text. Never pass DOCX/PPTX
            # to the PDF extraction worker or offer PDF-page tools for that source.
            self.include_context.setChecked(False)
            self.include_context.setEnabled(False)
        else:
            self.include_context.setEnabled(not self._busy and not is_office_document(self.document_path))
        is_dual = self.chat_scope_key.startswith("ENGO_DUAL::")
        self.chat_heading.setText(
            (("محادثة Engo AI لملفين" if is_dual else "محادثة Engo AI")) if is_ar
            else ("Dual File Engo AI Chat" if is_dual else "Engo AI Chat")
        )
        self.chat_subtitle.setText(
            (("محادثة مشتركة لملفي PDF المرتبطين" if is_dual else
              ("اسأل عن النص المحدد من مستند Office" if is_office_source else "مساعدك الدراسي لملفات PDF"))) if is_ar
            else ("One shared conversation for both linked PDFs" if is_dual else
                  ("Ask about selected text from the Office document" if is_office_source else "Your PDF study assistant"))
        )
        self.chat_combo.setToolTip(
            (("المحادثات المحفوظة لملفي PDF المرتبطين" if is_dual else
              ("المحادثات المحفوظة لمستند Office الحالي" if is_office_source else "المحادثات المحفوظة لملف PDF الحالي"))) if is_ar
            else ("Saved conversations for this linked PDF pair" if is_dual else
                  ("Saved conversations for the current Office document" if is_office_source else "Saved conversations for the current PDF"))
        )
        self.new_chat_btn.setToolTip(
            (("بدء محادثة مشتركة جديدة لملفي PDF المرتبطين" if is_dual else "بدء محادثة محفوظة جديدة لهذا الملف")) if is_ar
            else ("Start a new shared conversation for both linked PDFs" if is_dual else
                  ("Start a new saved conversation for this Office document" if is_office_source else "Start a new saved conversation for this PDF"))
        )
        self.prompt_edit.setEnabled(True)
        self._update_send_button_state()
        self.add_region_btn.setEnabled(not self._busy and not is_office_source)
        self.pdf_actions_btn.setEnabled(not self._busy and not is_office_source)
        self.new_chat_btn.setEnabled(not self._busy)
        self.chat_combo.setEnabled(not self._busy)
        self.include_context.setEnabled(not self._busy and not is_office_source)
        self.voice_btn.setEnabled(not self._busy)
        self.read_answer_btn.setEnabled(not self._busy)
        if is_office_source:
            self.document_label.setText(("مستند Office · النص المحدد فقط · " if is_ar else "Office document · selected text only · ") + self.document_name)
        else:
            self.document_label.setText(("سياق PDF · " if is_ar else "PDF context · ") + self.document_name)
        self._refresh_attachment_label()
        self._activate_transcript_page()

    def set_selected_region(self, path: str, page_index: int, image_bytes: bytes, source_path: str | None = None):
        # Regions are stored with the active chat owner, but retain the true source
        # PDF so a crop from the secondary pane remains identifiable in a dual chat.
        path = os.path.abspath(path)
        source_path = os.path.abspath(source_path or path)
        regions = self.selected_regions.setdefault(path, [])
        source_name = Path(source_path).name
        is_ar = str(self.settings.value("interface_language", "en", type=str) or "en").lower().startswith("ar")
        region_label = (f"{source_name} · صفحة {int(page_index) + 1} · منطقة {len(regions) + 1}" if is_ar
                        else f"{source_name} · page {int(page_index) + 1} · region {len(regions) + 1}")
        regions.append({
            "page_index": int(page_index),
            "source_path": source_path,
            "data": bytes(image_bytes),
            "label": region_label,
        })
        if path != self.document_path:
            return
        self._refresh_attachment_label()
        is_ar = str(self.settings.value("interface_language", "en", type=str) or "en").lower().startswith("ar")
        self.main_window.show_status((f"تمت إضافة منطقة رقم {len(regions)} من الصفحة {page_index + 1} · يمكنك إضافة المزيد أو الإرسال" if is_ar else f"Added region {len(regions)} from page {page_index + 1} · add more or send"))

    def remove_pending_attachment(self, index: int):
        if not self.document_path:
            return
        regions = self.selected_regions.get(self.document_path, [])
        if 0 <= index < len(regions):
            regions.pop(index)
        if not regions:
            self.selected_regions.pop(self.document_path, None)
        self._refresh_attachment_label()

    def clear_selected_region(self):
        if self.document_path:
            self.selected_regions.pop(self.document_path, None)
        self._clear_pending_selected_text()
        self._refresh_attachment_label()

    def _clear_pending_selected_text(self):
        self._pending_selected_text = ""
        self._pending_selected_text_source_role = "assistant"
        self._pending_selected_text_location = None
        if hasattr(self, "pending_selected_text_frame"):
            self.pending_selected_text_frame.hide()
        if hasattr(self, "prompt_edit"):
            is_ar = str(self.settings.value("interface_language", "en", type=str) or "en").lower().startswith("ar")
            self.prompt_edit.setPlaceholderText(
                "اكتب رسالتك إلى Engo AI…  ·  Enter للإرسال · Shift+Enter لسطر جديد · Ctrl+V للصق صورة"
                if is_ar else
                "Message Engo AI…  ·  Enter to send · Shift+Enter for a new line · Paste an image with Ctrl+V"
            )
        if hasattr(self, "clear_attachment_btn"):
            has_regions = bool(self.selected_regions.get(self.document_path)) if self.document_path else False
            self.clear_attachment_btn.setEnabled(has_regions and not self._busy)

    def _set_pending_selected_text(self, selected_text: str, source_role: str = "assistant", location=None):
        text = str(selected_text or "").replace("\u2029", "\n").replace("\u2028", "\n").strip()
        if not text:
            return
        self._pending_selected_text = text
        self._pending_selected_text_source_role = str(source_role or "assistant")
        self._pending_selected_text_location = dict(location) if isinstance(location, dict) else None
        role = self._pending_selected_text_source_role.casefold()
        source_label = ("your message" if role == "user" else
                        (("the Office document" if is_office_document(self.document_path) else "the PDF document")
                         if role == "document" else "Engo AI's reply"))
        is_ar = str(self.settings.value("interface_language", "en", type=str) or "en").lower().startswith("ar")
        if is_ar:
            self.pending_selected_text_title.setText(
                "مقطع محدد من رسالتك" if role == "user" else
                (("نص محدد من مستند Office" if is_office_document(self.document_path) else "نص محدد من ملف PDF")
                 if role == "document" else "مقطع محدد من رد Engo AI")
            )
        else:
            self.pending_selected_text_title.setText(f"Selected passage from {source_label}")
        preview = text if len(text) <= 320 else text[:317].rstrip() + "…"
        self.pending_selected_text_preview.setText(preview)
        self.pending_selected_text_preview.setToolTip(text)
        self.pending_selected_text_frame.show()
        self.prompt_edit.setPlaceholderText(
            "اكتب ما تريد السؤال عنه بخصوص النص المحدد…"
            if str(self.settings.value("interface_language", "en", type=str) or "en").lower().startswith("ar")
            else "Type what you want to ask about the selected text…"
        )
        self.prompt_edit.setFocus()
        self._update_send_button_state()

    def _refresh_attachment_label(self):
        regions = self.selected_regions.get(self.document_path, []) if self.document_path else []
        count = len(regions)
        if count:
            pages = [str(int(item["page_index"]) + 1) for item in regions if item.get("page_index") is not None]
            unique_pages = list(dict.fromkeys(pages))
            pages_text = ", ".join(unique_pages[:6]) + ("…" if len(unique_pages) > 6 else "")
            is_ar = str(self.settings.value("interface_language", "en", type=str) or "en").lower().startswith("ar")
            if is_ar:
                detail = f" · صفحات PDF: {pages_text}" if pages_text else ""
                self.attachment_label.setText(f"{count} مرفق جاهز{detail}" if count == 1 else f"{count} مرفقات جاهزة{detail}")
            else:
                detail = f" · PDF page(s) {pages_text}" if pages_text else ""
                self.attachment_label.setText(f"{count} attachment(s) ready{detail}")
            self.pending_header.show()
            self.pending_images_scroll.show()
            self.clear_attachment_btn.setEnabled(not self._busy)
        else:
            is_ar = str(self.settings.value("interface_language", "en", type=str) or "en").lower().startswith("ar")
            self.attachment_label.setText("المرفقات" if is_ar else "Attachments")
            self.pending_header.hide()
            self.pending_images_scroll.hide()
            self.clear_attachment_btn.setEnabled(bool(self._pending_selected_text) and not self._busy)

        while self.pending_images_layout.count():
            item = self.pending_images_layout.takeAt(0)
            widget = item.widget()
            if widget is not None:
                widget.deleteLater()
        for index, region in enumerate(regions):
            card = QFrame()
            card.setObjectName("aiPendingCard")
            card_layout = QVBoxLayout(card)
            card_layout.setContentsMargins(5, 4, 5, 4)
            card_layout.setSpacing(2)
            top = QHBoxLayout()
            top.setContentsMargins(0, 0, 0, 0)
            label = str(region.get("label") or f"Image {index + 1}")
            short_label = label if len(label) <= 20 else label[:17] + "…"
            title = QLabel(short_label)
            title.setObjectName("aiPendingLabel")
            title.setToolTip(label)
            top.addWidget(title, 1)
            remove = QPushButton("×")
            remove.setObjectName("aiPendingRemove")
            remove.setFixedSize(19, 19)
            remove.setToolTip("إزالة هذا المرفق" if str(self.settings.value("interface_language", "en", type=str) or "en").lower().startswith("ar") else "Remove this attachment")
            remove.clicked.connect(lambda _checked=False, i=index: self.remove_pending_attachment(i))
            top.addWidget(remove)
            card_layout.addLayout(top)
            preview = QLabel()
            preview.setObjectName("aiPendingPreview")
            preview.setFixedSize(90, 47)
            preview.setAlignment(Qt.AlignmentFlag.AlignCenter)
            qimg = QImage.fromData(bytes(region.get("data") or b""))
            if not qimg.isNull():
                preview.setPixmap(QPixmap.fromImage(qimg).scaled(
                    preview.size(), Qt.AspectRatioMode.KeepAspectRatio,
                    Qt.TransformationMode.SmoothTransformation))
            else:
                preview.setText("صورة" if str(self.settings.value("interface_language", "en", type=str) or "en").lower().startswith("ar") else "Image")
            card_layout.addWidget(preview, 0, Qt.AlignmentFlag.AlignHCenter)
            self.pending_images_layout.addWidget(card)
            self._animate_bubble_in(card)
        self.pending_images_layout.addStretch(1)

    def send_typed(self):
        stop_voice = getattr(self.main_window, "_stop_voice_input_for_send", None)
        if callable(stop_voice):
            stop_voice()
        text = self.prompt_edit.toPlainText().strip()
        if not text or not self.document_path or self._busy:
            return
        selected_context = self._pending_selected_text
        selected_source_role = self._pending_selected_text_source_role
        selected_location = dict(self._pending_selected_text_location) if isinstance(self._pending_selected_text_location, dict) else None
        self.prompt_edit.clear()
        self._clear_pending_selected_text()
        self._submit(
            text, "custom", selected_text_context=selected_context,
            selected_text_source_role=selected_source_role,
            selected_text_location=selected_location
        )

    def send_quick(self, prompt: str, mode: str):
        if not self.document_path or self._busy:
            return
        regions = self.selected_regions.get(self.document_path, [])
        if mode == "selection" and not regions:
            self.append_message_for(self.document_path, "assistant", "Select at least one page region first using **+ Add region**.")
            return
        self._submit(prompt, mode)

    def _submit(self, prompt: str, mode: str, selected_text_context: str = "",
                selected_text_source_role: str = "assistant", selected_text_location=None):
        regions = list(self.selected_regions.get(self.document_path, []))
        # Keep the visible user message concise and render selected chat text as a
        # separate quoted attachment. The exact passage is persisted as metadata and
        # is appended to the model prompt for this and future turns.
        message = str(prompt)
        request_prompt = message
        selected_text_context = str(selected_text_context or "").strip()
        if selected_text_context:
            source_role = str(selected_text_source_role).casefold()
            source_label = ("the user's message" if source_role == "user" else
                            ("the Office document" if source_role == "document" and is_office_document(self.document_path) else
                             ("the PDF document" if source_role == "document" else "Engo AI's reply")))
            context_guidance = (
                "Use only this selected native Office passage and the conversation; no PDF context was extracted."
                if source_role == "document" and is_office_document(self.document_path) else
                "Use the surrounding conversation and PDF context when relevant."
            )
            request_prompt += (
                "\n\nThe user wants you to answer the following question specifically about a passage "
                f"selected from {source_label}. {context_guidance}\n"
                "<<<BEGIN SELECTED CHAT PASSAGE>>>\n"
                f"{selected_text_context}\n"
                "<<<END SELECTED CHAT PASSAGE>>>"
            )
        stored_images = [{"page_index": r.get("page_index"), "data": r.get("data"), "label": r.get("label")} for r in regions]
        self._pending_request_scope = None
        self.append_message_for(
            self.document_path, "user", message,
            attachment_images=stored_images if stored_images else None,
            page_index=regions[0].get("page_index") if regions else None,
            selected_text_context=selected_text_context,
            selected_text_source_role=selected_text_source_role,
            selected_text_location=selected_text_location
        )
        # Attached regions become part of saved chat history. Clear the pending tray after sending;
        # follow-up questions can refer to those images from the recent conversation history.
        self.selected_regions.pop(self.document_path, None)
        self._refresh_attachment_label()
        current_page = 0
        active_tab = self.main_window.active_tab()
        if active_tab and os.path.abspath(active_tab.path) == os.path.abspath(self.document_path):
            current_page = int(active_tab.current_page)
        self.set_busy(True)
        self.start_streaming(self.document_path)
        self.requestSent.emit(self.document_path, request_prompt, stored_images, self.include_context.isChecked(), mode, current_page)

    def append_message_for(self, path: str, role: str, text: str,
                           attachment_image: bytes | None = None, page_index: int | None = None,
                           attachment_images: list[dict] | None = None,
                           selected_text_context: str = "", selected_text_source_role: str = "assistant",
                           selected_text_location=None):
        if not path:
            return
        path = os.path.abspath(path)
        pending = self._pending_request_scope
        if role != "user" and pending and os.path.abspath(pending[0]) == path:
            scope_key = pending[1]
        else:
            scope_key = self._scope_key_for_path(path)
        chat_id = self.active_chat_ids.get(scope_key)
        if chat_id is None:
            title = self._dual_chat_pair_label(scope_key) if scope_key.startswith("ENGO_DUAL::") else None
            chat_id = self.chat_store.create_chat(scope_key, title)
            if scope_key.startswith("ENGO_DUAL::"):
                self.chat_store.update_dual_chat_titles(scope_key, title)
            self.active_chat_ids[scope_key] = chat_id
            self.settings.setValue(self._chat_pref_key(scope_key), chat_id)
            self._loaded_chat_ids_by_scope[scope_key] = int(chat_id)
        self.chat_store.add_message(
            chat_id, role, str(text), attachment_image=attachment_image,
            page_index=page_index, attachment_images=attachment_images,
            selected_text_context=selected_text_context,
            selected_text_source_role=selected_text_source_role,
            selected_text_location=selected_text_location
        )
        self.messages_by_document[scope_key] = self.chat_store.load_messages(chat_id)
        self._loaded_chat_ids_by_scope[scope_key] = int(chat_id)
        if path == self.document_path and scope_key == (self.chat_scope_key or self.document_path):
            self._refresh_chat_combo(chat_id)
            self._render_transcript()
            if self._chat_bubbles:
                self._animate_bubble_in(self._chat_bubbles[-1])

    def start_streaming(self, path: str):
        path = os.path.abspath(path)
        if path != self.document_path or self._live_bubble is not None:
            self._live_path = path
            self._live_text = ""
            return
        self._live_path = path
        self._live_text = ""
        self._set_activity("Engo AI is preparing your reply", animate=True)
        # _render_transcript leaves a stretch item at the end; insert the live bubble above it.
        if self.transcript_layout.count():
            last = self.transcript_layout.takeAt(self.transcript_layout.count() - 1)
            if last.widget():
                last.widget().deleteLater()
        viewport_width = self._initial_transcript_bubble_width()
        is_ar = str(self.settings.value("interface_language", "en", type=str) or "en").lower().startswith("ar")
        loading_text = "*يجهّز Engo AI إجابته…*" if is_ar else "*Engo AI is preparing your reply…*"
        self._live_bubble = AIMessageBubble("assistant", loading_text, viewport_width, font_pt=self._chat_font_pt)
        self._connect_message_bubble_actions(self._live_bubble)
        self.transcript_layout.addWidget(self._live_bubble)
        self._animate_bubble_in(self._live_bubble)
        self.transcript_layout.addStretch(1)
        QTimer.singleShot(0, self._scroll_chat_to_bottom)

    def append_stream_delta(self, path: str, delta: str):
        path = os.path.abspath(path)
        if path != self.document_path:
            return
        if self._live_bubble is None or self._live_path != path:
            self.start_streaming(path)
        if not self._live_text:
            self._stop_activity_animation()
            self.busy_label.setText("جارٍ استلام الإجابة…" if str(self.settings.value("interface_language", "en", type=str) or "en").lower().startswith("ar") else "Receiving answer…")
        self._live_text += str(delta)
        if self._live_bubble is not None:
            self._live_bubble.set_content(self._live_text)
            QTimer.singleShot(0, self._scroll_chat_to_bottom)

    def set_pending_request_scope(self, path: str):
        self._pending_request_scope = (os.path.abspath(path), self._scope_key_for_path(path))

    def clear_pending_request_scope(self):
        self._pending_request_scope = None

    def messages_for_path(self, path: str | None = None):
        target = os.path.abspath(path or self.document_path) if (path or self.document_path) else ""
        scope_key = self._scope_key_for_path(target) if target else ""
        return self.messages_by_document.get(scope_key, []) if scope_key else []

    def api_history_for(self, path: str):
        # Keep recent turns to avoid unbounded prompt growth. Document context is attached separately.
        # Selected chat passages are private model context: append them only to the API payload,
        # never to the user-facing transcript message or chat exports.
        pending = self._pending_request_scope
        if pending and os.path.abspath(path) == pending[0]:
            scope_key = pending[1]
        else:
            scope_key = self._scope_key_for_path(path)
        history = [dict(item) for item in self.messages_by_document.get(scope_key, [])[-20:]]
        for item in history:
            passage = str(item.get("selected_text_context") or "").strip()
            if passage:
                source_role = str(item.get("selected_text_source_role") or "assistant")
                source_label = "the user's message" if source_role.casefold() == "user" else "Engo AI's reply"
                item["content"] = (
                    str(item.get("content") or "")
                    + "\n\n[Selected chat passage from " + source_label + "]\n"
                    + passage
                )
        return history

    def _transcript_bubbles_in_view(self, overscan: float = 0.45):
        """Return a small, stable set of bubbles around the visible transcript viewport."""
        if not self.isVisible() or not hasattr(self, "transcript"):
            return []
        viewport = self.transcript.viewport()
        bar = self.transcript.verticalScrollBar()
        top = max(0, int(bar.value() - viewport.height() * max(0.0, float(overscan))))
        bottom = int(bar.value() + viewport.height() * (1.0 + max(0.0, float(overscan))))
        bubbles = list(self._chat_bubbles)
        if self._live_bubble is not None and self._live_bubble not in bubbles:
            bubbles.append(self._live_bubble)
        visible = []
        for bubble in bubbles:
            if bubble is None:
                continue
            try:
                bubble_y = bubble.mapTo(self.transcript_body, QPoint(0, 0)).y()
                if bubble_y + bubble.height() >= top and bubble_y <= bottom:
                    visible.append(bubble)
            except RuntimeError:
                continue
        return visible

    def _reflow_bubble_subset(self, bubbles, viewport_width: int) -> bool:
        """Resize a small preselected bubble batch without scanning the full chat history."""
        viewport_width = max(250, int(viewport_width) - 28)
        user_width = min(640, max(260, int(viewport_width * 0.68)))
        assistant_width = viewport_width
        changed = False
        for bubble in bubbles:
            if bubble is None:
                continue
            width = user_width if bubble.role == "user" else assistant_width
            if getattr(bubble, "_bubble_width", None) != width:
                bubble.set_bubble_width(width)
                changed = True
        if changed:
            self.transcript_body.updateGeometry()
        return changed

    def reflow_transcript_bubbles_batched(self, batch_size: int = 2, interval_ms: int = 8):
        """Reflow the complete transcript in small event-loop-friendly batches.

        A generation token makes a newer resize supersede any older queued pass.
        This avoids one large QTextDocument layout burst after a focus transition.
        """
        if not self.isVisible() or not hasattr(self, "transcript"):
            return
        self._transcript_reflow_generation = getattr(self, "_transcript_reflow_generation", 0) + 1
        generation = self._transcript_reflow_generation
        bubbles = list(self._chat_bubbles)
        if self._live_bubble is not None and self._live_bubble not in bubbles:
            bubbles.append(self._live_bubble)
        if not bubbles:
            return
        viewport_width = self._initial_transcript_bubble_width()
        user_width = min(640, max(260, int(viewport_width * 0.68)))
        assistant_width = viewport_width
        bar = self.transcript.verticalScrollBar()
        stick_to_bottom = bar.value() >= bar.maximum() - 18
        old_value = bar.value()
        batch_size = max(1, int(batch_size))
        interval_ms = max(0, int(interval_ms))
        cursor = 0

        def process_batch():
            nonlocal cursor
            if generation != self._transcript_reflow_generation or not self.isVisible():
                return
            end = min(len(bubbles), cursor + batch_size)
            changed = False
            for bubble in bubbles[cursor:end]:
                if bubble is None:
                    continue
                try:
                    width = user_width if bubble.role == "user" else assistant_width
                    if getattr(bubble, "_bubble_width", None) != width:
                        bubble.set_bubble_width(width)
                        changed = True
                except RuntimeError:
                    continue
            cursor = end
            if changed:
                self.transcript_body.updateGeometry()
            if cursor < len(bubbles):
                QTimer.singleShot(interval_ms, process_batch)
                return
            current_bar = self.transcript.verticalScrollBar()
            current_bar.setValue(current_bar.maximum() if stick_to_bottom else min(old_value, current_bar.maximum()))

        process_batch()

    def _reflow_transcript_bubbles(self, visible_only: bool = False, restore_scroll: bool = True):
        """Resize existing bubbles to the live viewport without rebuilding Markdown.

        During Chat Focus motion we reflow only the visible messages (plus a screen of
        breathing room). That lets the conversation expand with the panel instead of
        snapping to its new width after the animation has ended, while keeping long
        histories inexpensive to animate.
        """
        if not self.isVisible() or not hasattr(self, "transcript"):
            return
        viewport = self.transcript.viewport()
        viewport_width = max(250, viewport.width() - 28)
        user_bubble_width = min(640, max(260, int(viewport_width * 0.68)))
        assistant_bubble_width = viewport_width
        bubbles = list(self._chat_bubbles)
        if self._live_bubble is not None and self._live_bubble not in bubbles:
            bubbles.append(self._live_bubble)

        bar = self.transcript.verticalScrollBar()
        stick_to_bottom = bar.value() >= bar.maximum() - 18
        old_value = bar.value()
        if visible_only:
            # Include one viewport above and below the visible window so the next
            # messages are already at the correct width as the user scrolls.
            visible_top = max(0, old_value - viewport.height())
            visible_bottom = old_value + (viewport.height() * 2)
        else:
            visible_top = visible_bottom = None

        changed = False
        for bubble in bubbles:
            if bubble is None:
                continue
            if visible_only:
                try:
                    bubble_y = bubble.mapTo(self.transcript_body, QPoint(0, 0)).y()
                    if bubble_y + bubble.height() < visible_top or bubble_y > visible_bottom:
                        continue
                except RuntimeError:
                    continue
            width = user_bubble_width if bubble.role == "user" else assistant_bubble_width
            previous_width = getattr(bubble, "_bubble_width", None)
            if previous_width != width:
                bubble.set_bubble_width(width)
                changed = True

        if changed:
            self.transcript_body.updateGeometry()

        if restore_scroll:
            def restore_scroll_position():
                try:
                    current_bar = self.transcript.verticalScrollBar()
                    current_bar.setValue(current_bar.maximum() if stick_to_bottom else old_value)
                except RuntimeError:
                    pass
            QTimer.singleShot(0, restore_scroll_position)
        elif stick_to_bottom:
            # Avoid queuing a new zero-delay callback on every animation frame.
            bar.setValue(bar.maximum())

    def _connect_message_bubble_actions(self, bubble):
        """Route a selected transcript passage back into this conversation."""
        if bubble is not None:
            bubble.selectionQuestionRequested.connect(self._ask_about_selected_chat_text)
            bubble.selectedTextLocationActivated.connect(self.main_window.jump_to_pdf_selection)

    def _ask_about_selected_chat_text(self, selected_text: str, source_role: str = "assistant", location=None):
        """Attach a selected passage to the composer so the user can write a custom question."""
        selected_text = str(selected_text or "").replace("\u2029", "\n").replace("\u2028", "\n").strip()
        if not selected_text or not self.document_path:
            return
        is_ar = str(self.settings.value("interface_language", "en", type=str) or "en").lower().startswith("ar")
        if self._busy:
            QMessageBox.information(
                self._popup_parent(), "Engo AI مشغول" if is_ar else "Engo AI is busy",
                "انتظر حتى تنتهي الإجابة الحالية، ثم حدّد المقطع مرة أخرى." if is_ar else "Wait for the current answer to finish, then select the passage again."
            )
            return
        self._set_pending_selected_text(selected_text, source_role, location)
        self.main_window.show_status("تم إرفاق المقطع المحدد من المحادثة · اكتب سؤالك" if is_ar else "Selected chat passage attached · type your question and press Send")

    def _render_transcript(self):
        self._stop_activity_animation()
        self._live_bubble = None
        self._live_path = ""
        self._live_text = ""
        self._chat_bubbles = []
        self._chat_search_matches = []
        self._chat_search_current = -1
        history = self.messages_by_document.get(self.chat_scope_key or self.document_path, [])
        interface_language = str(self.settings.value("interface_language", "en", type=str) or "en")
        while self.transcript_layout.count():
            item = self.transcript_layout.takeAt(0)
            widget = item.widget()
            if widget is not None:
                widget.deleteLater()
        viewport_width = max(250, self.transcript.viewport().width() - 28)
        # User messages stay compact and right-aligned. Assistant replies use the full
        # conversation width so Markdown, equations, and tables have room to render.
        user_bubble_width = min(640, max(260, int(viewport_width * 0.68)))
        assistant_bubble_width = viewport_width
        if not history:
            is_ar = str(self.settings.value("interface_language", "en", type=str) or "en").lower().startswith("ar")
            if self.document_path:
                if is_ar:
                    welcome = (
                        f"## مرحبًا بك في Engo AI\n\nيمكنك طرح أسئلة حول **{self.document_name}**. حدّد منطقة واحدة أو أكثر باستخدام **+ إضافة منطقة**، "
                        "أو استخدم **إجراءات PDF** لتلخيص الملف بالكامل أو مراجعته أو السؤال عن الصفحة الحالية.\n\n"
                        "يمكنني فهم النصوص المطبوعة والكتابة اليدوية والمعادلات والمخططات والصفحات الممسوحة ضوئيًا، عندما يدعم النموذج المحدد معالجة الصور."
                    )
                else:
                    welcome = (
                        f"## Welcome to Engo AI\n\nAsk questions about **{self.document_name}**. Select one or more regions with **+ Add region**, "
                        "or use **PDF actions** to summarize/review the entire file or ask about the current page.\n\n"
                        "I can interpret printed text, handwriting, formulas, charts, and scanned pages when the selected model supports vision."
                    )
            else:
                welcome = (
                    "## مرحبًا بك في Engo AI\n\nافتح ملف PDF لبدء المحادثة. تُحفظ المحادثات على هذا الكمبيوتر ويمكنك متابعتها لاحقًا."
                    if is_ar else
                    "## Welcome to Engo AI\n\nOpen a PDF to start a conversation. Saved chats remain on this computer and can be continued later."
                )
            bubble = AIMessageBubble("assistant", welcome, assistant_bubble_width, font_pt=self._chat_font_pt)
            self._connect_message_bubble_actions(bubble)
            self._chat_bubbles.append(bubble)
            self.transcript_layout.addWidget(bubble)
        else:
            for item in history:
                attachments = item.get("attachments", [])
                # Compat with chat database versions before v9.
                if not attachments and item.get("attachment_path"):
                    attachments = [{"path": item["attachment_path"], "page_index": item.get("page_index")}]
                role = str(item.get("role", "assistant"))
                message_width = user_bubble_width if role == "user" else assistant_bubble_width
                bubble = AIMessageBubble(
                    role, item.get("content", ""), message_width,
                    item.get("created_at", ""), attachments=attachments, font_pt=self._chat_font_pt,
                    selected_text_context=item.get("selected_text_context", ""),
                    selected_text_location=item.get("selected_text_location"),
                    language=interface_language
                )
                self._connect_message_bubble_actions(bubble)
                self._chat_bubbles.append(bubble)
                self.transcript_layout.addWidget(bubble)
        self.transcript_layout.addStretch(1)
        # Store the rendered page so switching document tabs does not rebuild it.
        self._store_active_transcript_page_state()
        active_page = self._transcript_pages.get(self._active_transcript_page_key)
        if active_page is not None:
            active_page["history_signature"] = self._transcript_history_signature()
        page_key = self._active_transcript_page_key
        def scroll_if_still_active(expected_key=page_key):
            if self._active_transcript_page_key == expected_key:
                self._scroll_chat_to_bottom()
        # The transcript follows the newest message after a real page rebuild;
        # stale timers from a previous page must never move the newly active chat.
        QTimer.singleShot(0, scroll_if_still_active)
        QTimer.singleShot(70, scroll_if_still_active)
        QTimer.singleShot(180, scroll_if_still_active)

    def _handle_send_stop_clicked(self):
        if self._busy:
            self.main_window.cancel_ai_request()
        else:
            self.send_typed()

    def _update_send_button_state(self):
        """Restyle and localize the single composer action as Send or Stop."""
        busy = bool(self._busy)
        is_ar = str(self.settings.value("interface_language", "en", type=str) or "en").lower().startswith("ar")
        if busy:
            self.send_btn.setText("إيقاف" if is_ar else "Stop")
            self.send_btn.setIcon(make_icon("stop", "#ffffff", 16))
            self.send_btn.setObjectName("aiStop")
            self.send_btn.setToolTip("إيقاف استجابة الذكاء الاصطناعي الحالية" if is_ar else "Stop the current AI response")
            # Keep this same button available so the user can interrupt generation.
            self.send_btn.setEnabled(True)
            self.send_btn.setDefault(False)
        else:
            self.send_btn.setText("إرسال" if is_ar else "Send")
            self.send_btn.setObjectName("aiSend")
            self.send_btn.setToolTip("إرسال الرسالة" if is_ar else "Send message")
            has_text = bool(self.prompt_edit.toPlainText().strip()) if hasattr(self, "prompt_edit") else False
            can_send = bool(self.document_path and has_text)
            self.send_btn.setEnabled(can_send)
            self.send_btn.setDefault(can_send)
            active_theme = str(self.settings.value("ui_theme", "dark", type=str) or "dark").lower()
            send_icon_color = "#ffffff" if can_send or active_theme != "light" else "#8291a6"
            self.send_btn.setIcon(make_icon("send", send_icon_color, 16))
        # QSS selectors use the object name, so force a polish after switching it.
        style = self.send_btn.style()
        style.unpolish(self.send_btn)
        style.polish(self.send_btn)
        self.send_btn.update()

    def set_busy(self, busy: bool):
        self._busy = bool(busy)
        if not busy:
            self._stop_activity_animation()
            self.busy_label.setText("")
        elif not self.busy_label.text():
            self._set_activity("Preparing request", animate=True)
        self._update_send_button_state()
        self.prompt_edit.setEnabled(bool(self.document_path) and not busy)
        self.provider_combo.setEnabled(not busy)
        self.close_panel_btn.setEnabled(True)
        self.export_btn.setEnabled(bool(self.document_path) and not busy)
        office_source = is_office_document(self.document_path)
        self.pdf_actions_btn.setEnabled(bool(self.document_path) and not busy and not office_source)
        self.add_region_btn.setEnabled(bool(self.document_path) and not busy and not office_source)
        self.new_chat_btn.setEnabled(bool(self.document_path) and not busy)
        self.chat_combo.setEnabled(bool(self.document_path) and not busy)
        self.include_context.setEnabled(bool(self.document_path) and not busy and not office_source)
        self.clear_attachment_btn.setEnabled(
            bool(self.selected_regions.get(self.document_path) or self._pending_selected_text) and not busy
        )
        self.voice_btn.setEnabled(bool(self.document_path) and not busy)
        self.read_answer_btn.setEnabled(bool(self.document_path) and not busy)
        self.stop_audio_btn.setEnabled(True)

    def _export_menu(self):
        menu = QMenu(self._popup_parent())
        md_action = menu.addAction(make_icon("export", "#b7c6dc", 15), "Export as Markdown (.md)")
        pdf_action = menu.addAction(make_icon("export", "#b7c6dc", 15), "Export as PDF (.pdf)")
        chosen = menu.exec(self.export_btn.mapToGlobal(self.export_btn.rect().bottomLeft()))
        if chosen is md_action:
            self.export_markdown()
        elif chosen is pdf_action:
            self.export_pdf()

    def _current_chat_title(self):
        scope_key = self.chat_scope_key or self.document_path
        chat_id = self.active_chat_ids.get(scope_key)
        return self.chat_store.get_chat_title(chat_id) if chat_id else "Engo AI Chat"

    def _markdown_export_text(self):
        exported_at = __import__("datetime").datetime.now().astimezone().strftime("%Y-%m-%d %H:%M")
        lines = [
            "# Engo PDF Viewer & AI Study Agent — AI Study Conversation", "",
            f"**Conversation:** {self._current_chat_title()}",
            f"**PDF:** {Path(self.document_path).name}",
            f"**Exported:** {exported_at}", "",
            "---", ""
        ]
        for item in self.messages_by_document.get(self.chat_scope_key or self.document_path, []):
            role = "Your question" if item.get("role") == "user" else "Engo AI answer"
            lines.extend([f"## {role}", "", item.get("content", "")])
            lines.extend(["", "---", ""])
        lines.append("*Exported locally by Engo PDF Viewer & AI Study Agent.*")
        return "\n".join(lines)

    @staticmethod
    def _markdown_to_html_fragment(markdown_text: str) -> str:
        temp_doc = QTextDocument()
        _set_markdown_document(temp_doc, markdown_text or " ", 12.0)
        rendered = temp_doc.toHtml()
        match = re.search(r"<body[^>]*>(.*?)</body>", rendered, flags=re.IGNORECASE | re.DOTALL)
        if match:
            return match.group(1)
        return html_module.escape(markdown_text).replace("\n", "<br>")

    def export_markdown(self):
        if not self.document_path:
            return
        default_name = f"{Path(self.document_path).stem}_Engo_AI_chat.md"
        path = _engo_file_dialog(self, "Export AI conversation", "تصدير محادثة AI", default_name, "Markdown (*.md)", save=True)
        if not path:
            return
        if not path.lower().endswith(".md"):
            path += ".md"
        try:
            Path(path).write_text(self._markdown_export_text(), encoding="utf-8")
            is_ar = str(self.settings.value("interface_language", "en", type=str) or "en").lower().startswith("ar")
            self.main_window.show_status((f"تم تصدير المحادثة إلى {path}" if is_ar else f"Chat exported to {path}"))
        except Exception as exc:
            is_ar = str(self.settings.value("interface_language", "en", type=str) or "en").lower().startswith("ar")
            QMessageBox.warning(self._popup_parent(), "تصدير المحادثة" if is_ar else "Export chat", (f"تعذر تصدير ملف Markdown:\n{exc}" if is_ar else f"Could not export Markdown:\n{exc}"))

    def export_pdf(self):
        if not self.document_path:
            return
        default_name = f"{Path(self.document_path).stem}_Engo_AI_chat.pdf"
        path = _engo_file_dialog(self, "Export AI conversation as a formatted PDF", "تصدير محادثة AI كملف PDF منسّق", default_name, "PDF (*.pdf)", save=True)
        if not path:
            return
        if not path.lower().endswith(".pdf"):
            path += ".pdf"
        try:
            exported_at = __import__("datetime").datetime.now().astimezone().strftime("%d %B %Y · %H:%M")
            title = html_module.escape(self._current_chat_title())
            source_name = html_module.escape(Path(self.document_path).name)
            chunks = []
            for index, item in enumerate(self.messages_by_document.get(self.chat_scope_key or self.document_path, []), 1):
                is_user = item.get("role") == "user"
                role = "QUESTION" if is_user else "ENGO AI · RESPONSE"
                accent = "#466ed0" if is_user else "#167c68"
                fill = "#f1f5ff" if is_user else "#effaf6"
                body = self._markdown_to_html_fragment(item.get("content", ""))
                stamp = html_module.escape(str(item.get("created_at", "")))
                chunks.append(
                    f'<table width="100%" cellspacing="0" cellpadding="0" border="0">'
                    f'<tr><td bgcolor="{fill}" style="background-color:{fill}; padding:12px; border-left:4px solid {accent};">'
                    f'<p style="color:{accent}; font-size:9pt; font-weight:bold; margin:0 0 5px 0;">{index:02d} · {role} '
                    f'<span style="color:#778399; font-size:8pt; font-weight:normal;">{stamp}</span></p>'
                    f'<div style="color:#1f2937; font-size:10pt; line-height:1.45;">{body}</div>'
                    f'</td></tr></table><br/>'
                )
            if not chunks:
                chunks.append('<p style="color:#667085;">No messages in this conversation yet.</p>')
            html_doc = f'''<!DOCTYPE html><html><head><meta charset="utf-8"><style>
              body {{ font-family: "Segoe UI", Arial; color: #192338; font-size: 10pt; }}
              h1 {{ color: #1c2a42; font-size: 24pt; margin: 0 0 5px 0; }}
              h2 {{ color: #53627a; font-size: 12pt; margin-top: 24px; }}
              p {{ margin-top: 4px; margin-bottom: 6px; }}
              hr {{ color: #dbe2ee; }}
              code {{ background-color: #edf1f7; color: #35425a; }}
              blockquote {{ border-left: 3px solid #9eb0cf; margin-left: 8px; padding-left: 10px; color: #53627a; }}
              table {{ border-collapse: collapse; }}
            </style></head><body>
            <table width="100%" cellspacing="0" cellpadding="0"><tr>
              <td><p style="font-size:9pt; letter-spacing:2px; color:#5675ad; font-weight:bold;">ENGO PDF VIEWER</p>
              <h1>AI Study Conversation</h1><p style="font-size:13pt; color:#4c5c73;">{title}</p></td>
            </tr></table>
            <hr/><p><b>Source PDF:</b> {source_name}</p><p><b>Exported:</b> {html_module.escape(exported_at)}</p>
            <p style="font-size:9pt; color:#6b778c;">A formatted transcript of the saved conversation. The original PDF is not modified by this export.</p>
            <br/>{''.join(chunks)}
            <hr/><p style="font-size:8pt; color:#778399;">Generated locally by Engo PDF Viewer & AI Study Agent.</p>
            </body></html>'''
            writer = QPdfWriter(path)
            writer.setTitle(f"Engo AI Study Conversation - {Path(self.document_path).name}")
            writer.setCreator(APP_NAME)
            writer.setResolution(96)
            writer.setPageSize(QPageSize(QPageSize.PageSizeId.A4))
            doc = QTextDocument()
            doc.setDefaultFont(QFont("Segoe UI", 10))
            doc.setDocumentMargin(34)
            doc.setHtml(html_doc)
            doc.setPageSize(QSizeF(writer.width(), writer.height()))
            doc.print(writer)
            is_ar = str(self.settings.value("interface_language", "en", type=str) or "en").lower().startswith("ar")
            self.main_window.show_status((f"تم تصدير المحادثة بصيغة PDF إلى {path}" if is_ar else f"Formatted chat PDF exported to {path}"))
        except Exception as exc:
            is_ar = str(self.settings.value("interface_language", "en", type=str) or "en").lower().startswith("ar")
            QMessageBox.warning(self._popup_parent(), "تصدير المحادثة" if is_ar else "Export chat", (f"تعذر تصدير ملف PDF:\n{exc}" if is_ar else f"Could not export PDF:\n{exc}"))
