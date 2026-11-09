# Auto-split from main.py (verbatim move; do not reformat).
from __future__ import annotations

import colorsys
import os
import sys
import json
import io
import uuid
import hashlib
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
import base64
import time
from pathlib import Path
import pymupdf as fitz  # use the maintained import name; keep fitz alias for existing calls
from PIL import Image, ImageOps, ImageChops, ImageFilter
from PyQt6.QtCore import QObject, Qt, QSize, QSizeF, QRect, QRectF, QPoint, QPointF, QEvent, QTimer, QPropertyAnimation, QParallelAnimationGroup, QVariantAnimation, QEasingCurve, QSettings, QUrl, QThread, QRunnable, QThreadPool, QMarginsF, QStandardPaths, QDir, pyqtSignal, QBuffer, QByteArray, QIODevice, QMimeData, QSignalBlocker, QProcess
from PyQt6.QtNetwork import QLocalServer, QLocalSocket
from PyQt6.QtGui import QColor, QPalette, QImage, QPixmap, QIcon, QFileSystemModel, QPainter, QPen, QBrush, QKeySequence, QShortcut, QAction, QCursor, QPolygonF, QPainterPath, QPainterPathStroker, QDesktopServices, QPdfWriter, QPageSize, QTextDocument, QTextCursor, QFont, QDrag, QContextMenuEvent, QMouseEvent
from PyQt6.QtWidgets import (
    QApplication, QMainWindow, QWidget, QFrame, QLabel, QPushButton, QToolButton, QBoxLayout,
    QCheckBox, QColorDialog, QFileDialog, QHBoxLayout, QVBoxLayout, QScrollArea, QAbstractScrollArea,
    QListWidget, QListWidgetItem, QListView, QAbstractItemView, QTreeWidget, QTreeWidgetItem, QTreeView, QSpinBox,
    QSizePolicy, QStatusBar, QMessageBox, QSplitter, QTabWidget, QDialog,
    QDialogButtonBox, QInputDialog, QButtonGroup, QLineEdit, QStackedWidget, QTabBar, QMenu, QComboBox,
    QTextBrowser, QTextEdit, QProgressBar, QGridLayout, QStyledItemDelegate, QStyle, QSlider, QWidgetAction, QToolTip, QGraphicsOpacityEffect
)

from engo_ai_chat import (
    AIChatConversationDelegate,
    AIChatPanel,
)
from engo_ai_core import (
    AISettingsDialog,
    AIRequestWorker,
    AI_DEFAULT_MODELS,
    AI_PROVIDER_LABELS,
    AI_TRANSLATION_DEFAULT_MODEL,
    GeminiTranslateWorker,
    TranslationCardDialog,
    _get_provider_key,
)
from engo_ai_workers import (
    AISemanticSearchWorker,
    PDFSearchDialog,
    PDFTextSearchWorker,
)
from engo_app_dialogs import (
    AppSettingsDialog,
    DOCUMENT_TAB_MIME,
    DocumentTabBar,
    FirstRunSetupDialog,
    _DOCUMENT_TAB_DRAG_REGISTRY,
)
from engo_base import (
    APP_DATA_NAME,
    APP_NAME,
    APP_ORG,
    DEFAULT_ANNOTATION_COLORS,
    DEFAULT_BG,
    DEFAULT_INK,
    EngoDialogConsistencyFilter,
    EngoTooltipTranslationFilter,
    HOME_FOOTER_TEXT,
    IPC_SERVER_NAME,
    UI_ACCENT,
    _ENGO_TOOLTIP_TRANSLATIONS,
    _engo_apply_dialog_consistency,
    _engo_apply_menu_consistency,
    _engo_apply_windows_caption_theme,
    _engo_translate_tooltip,
    engo_theme_qpalette,
    engo_ui_theme_tokens,
    is_office_document,
    is_supported_document,
    normalize_ui_theme,
    resource_path,
)
from engo_document import (
    DocumentTab,
)
from engo_live import (
    GeminiLiveTutorWorker,
    LiveTutorDialog,
    SpeechPlaybackWorker,
    TeachBoardPanel,
    VoiceInputWorker,
)
from engo_markdown import (
    _MATH_TEXT_CACHE,
    _prepare_chat_markdown,
)
from engo_office import (
    OfficeDocumentReaderDialog,
    is_image_document,
    prepare_document_for_viewer,
)
from engo_widgets import (
    AnnotationColorsDialog,
    EngoFileSystemModel,
    MiddleMouseAutoScroll,
    MotionButton,
    PageThemeDialog,
    ResponsiveSidebarTabs,
    _configure_color_dialog,
    _engo_file_dialog,
    _qt_thread_is_running,
    apply_page_theme_to_image,
    color_tuple,
    make_icon,
)


APP_VERSION = "2.3.6"  # V17 Smart Theme cache/per-page render fix


class MainWindow(QMainWindow):
    pdfSearchWorkerFinished = pyqtSignal(object)
    _open_windows = []

    def __init__(self, register_ipc=True):
        super().__init__()
        self._register_ipc = bool(register_ipc)
        MainWindow._open_windows.append(self)
        self._closing_complete = False
        self.pdfSearchWorkerFinished.connect(self._finalize_pdf_search_worker)
        self.settings = QSettings(APP_ORG, "EngoPDFViewer")
        app = QApplication.instance()
        if app is not None:
            try:
                app._engo_settings = self.settings
            except Exception:
                pass
        # Only show first-run onboarding when this profile has no saved preferences at all.
        # Existing installs upgrading from an earlier version already have keys and skip it.
        try:
            self._needs_first_run_setup = len(self.settings.allKeys()) == 0
        except Exception:
            self._needs_first_run_setup = not self.settings.contains("ui_theme")
        # PDF linking is an explicit, session-only action.
        # pairs and silently re-linked PDFs when both were opened together; discard
        # that legacy setting so multi-file opens always start independently.
        self._linked_pdf_pairs = {}
        try:
            self.settings.remove("linked_pdf_pairs")
            self.settings.sync()
        except Exception:
            pass
        # Old builds cached AI handwriting transcriptions per crop. Remove these so the new
        # Gemini-only translation workflow never reuses or persists prior OCR/translation text.
        try:
            for saved_key in self.settings.allKeys():
                if saved_key.startswith("handwriting_transcription_cache/"):
                    self.settings.remove(saved_key)
            self.settings.sync()
        except Exception:
            pass
        self.dark_mode = self.settings.value("dark_mode", False, type=bool)
        self.smart_page_theme = self.settings.value("smart_page_theme", False, type=bool)
        self.bg_color = self.settings.value("page_bg", DEFAULT_BG, type=str)
        self.ink_color = self.settings.value("page_ink", DEFAULT_INK, type=str)
        raw_themes = self.settings.value("custom_page_themes", "{}")
        try:
            self.custom_page_themes = json.loads(raw_themes) if isinstance(raw_themes, str) else dict(raw_themes)
        except Exception:
            self.custom_page_themes = {}
        raw_annot_colors = self.settings.value("annotation_colors", "{}")
        try:
            self.annotation_colors = dict(DEFAULT_ANNOTATION_COLORS)
            self.annotation_colors.update(json.loads(raw_annot_colors) if isinstance(raw_annot_colors, str) else dict(raw_annot_colors))
        except Exception:
            self.annotation_colors = dict(DEFAULT_ANNOTATION_COLORS)
        self._fullscreen = False
        self._presentation = False
        self._pre_present_mode = None
        self._pre_fullscreen_geometry = None
        self._pre_fullscreen_maximized = False
        self._pre_fullscreen_visibility = None
        self._toolbar_pinned = self.settings.value(
            "toolbar_pinned", self.settings.value("toolbar_visible", True, type=bool), type=bool
        )
        self._fullscreen_toolbar_pinned = self._toolbar_pinned  # compatibility alias for older state handlers
        self._toolbar_manually_hidden = not self._toolbar_pinned
        self._fullscreen_toolbar_animation = None
        self._fullscreen_toolbar_natural_height = 0
        self._theme_transition_animation = None
        self._theme_transition_restore = []  # retained for compatibility with older state handlers
        self._theme_transition_overlays = []
        self._files_screen_active = False
        self._context_help_suppressed = False
        self._files_previous_topbar_visible = True
        self._files_previous_topbar_max_height = 16777215
        self._files_previous_workspace_sizes = None
        self._files_previous_ai_visible = False
        self._files_previous_board_visible = False
        self._files_previous_ai_checked = False
        self._chat_focus_mode = False
        self._chat_focus_restore = None
        self._chat_focus_animation = None
        self._chat_focus_chrome_animations = []
        self._chat_focus_chrome_tracks = []
        self._chat_focus_transition_active = False
        # Two quick Space taps in the PDF reader open the text chat. The first
        # tap is left untouched; auto-repeat while holding Space never counts.
        self._space_double_tap_at = 0.0
        self._fullscreen_toolbar_hide_timer = QTimer(self)
        self._fullscreen_toolbar_hide_timer.setSingleShot(True)
        self._fullscreen_toolbar_hide_timer.setInterval(420)
        self._fullscreen_toolbar_hide_timer.timeout.connect(self._hide_fullscreen_toolbar)
        self._ai_worker: AIRequestWorker | None = None
        self._voice_input_worker: VoiceInputWorker | None = None
        self._speech_worker: SpeechPlaybackWorker | None = None
        self._live_tutor_worker: GeminiLiveTutorWorker | None = None
        self._live_tutor_dialog: LiveTutorDialog | None = None
        self._pdf_search_dialog: PDFSearchDialog | None = None
        self._pdf_search_worker = None
        self._pdf_search_generation = 0
        self._pdf_search_path = ""
        self._active_pdf_search_results: list[dict] = []
        self._speak_next_response = False
        self._teaching_payload = None
        self._close_after_cancel = False
        # Debounce toolbar reflow while the window is being resized.  The timer
        # runs after Qt has recalculated child geometry, so density is selected
        # from the real width available to the toolbar rather than a stale width.
        self._toolbar_density_timer = QTimer(self)
        self._toolbar_density_timer.setSingleShot(True)
        self._toolbar_density_timer.setInterval(70)
        self._toolbar_density_timer.timeout.connect(self._apply_toolbar_density)
        # Re-evaluate responsive spacing when Windows/Qt moves the window to a
        # monitor with a different logical DPI or available screen geometry.
        self._responsive_screen_reflow_timer = QTimer(self)
        self._responsive_screen_reflow_timer.setSingleShot(True)
        self._responsive_screen_reflow_timer.setInterval(180)
        self._responsive_screen_reflow_timer.timeout.connect(self._refresh_responsive_toolbar)
        self._responsive_screen_handle = None
        # After the first visible layout, toolbar density is locked. It may change
        # only after a real, user-originated horizontal resize of the main window.
        # Opening dialogs, changing pages, switching Home/PDF, pinning the toolbar,
        # or resizing child panels must never collapse/reflow the toolbar.
        self._toolbar_density_initialized = False
        self._toolbar_density_user_resize_pending = False
        self._toolbar_density_last_width = None
        self._toolbar_density_initial_pass_scheduled = False
        self._live_tutor_toolbar_locked = False
        self.setWindowTitle(APP_NAME)
        # Keep a practical minimum for split-screen use; maximized windows use the
        # active display's available geometry, including 4K and high-DPI monitors.
        self.setMinimumSize(620, 430)
        self.resize(1500, 900)
        icon_path = resource_path("engopdfviewer.ico")
        if os.path.exists(icon_path):
            app_icon = QIcon(icon_path)
            self.setWindowIcon(app_icon)
            app = QApplication.instance()
            if app is not None:
                app.setWindowIcon(app_icon)
        self.setAcceptDrops(True)
        self._build_ui()
        # Home is the first screen. Hide the complete document-tab strip as well
        # as the PDF toolbar so the Home page occupies the full content area.
        # The strip is shown again only when a document view becomes active.
        self._files_screen_active = True
        self.tab_strip.hide()
        self._files_previous_topbar_visible = True
        self._files_previous_topbar_max_height = 16777215 if self._toolbar_pinned else 3
        self.topbar.hide()
        self._sync_toolbar_pin_button()
        self._apply_style()
        self._apply_user_interface_preferences()
        self._apply_interface_language()
        self._set_default_context_help(force=True)
        self._shortcuts()
        self._install_fullscreen_mouse_filter()
        # Browser-like middle-click auto-scroll is shared by the PDF reader,
        # thumbnails, transcript browsers, and other scrollable child widgets.
        self._middle_auto_scroll = MiddleMouseAutoScroll(self)
        self._update_controls()
        if self._register_ipc:
            self._setup_ipc_server()

    def _setup_ipc_server(self):
        """Accept PDF paths from later double-click launches and open them in this window."""
        self._ipc_server = QLocalServer(self)
        self._ipc_server.newConnection.connect(self._accept_ipc_connections)
        if not self._ipc_server.listen(IPC_SERVER_NAME):
            # A stale endpoint can remain after a crash; the startup client check has
            # already failed, so it is now safe to clear the stale server name.
            QLocalServer.removeServer(IPC_SERVER_NAME)
            self._ipc_server.listen(IPC_SERVER_NAME)

    def _accept_ipc_connections(self):
        while self._ipc_server.hasPendingConnections():
            sock = self._ipc_server.nextPendingConnection()
            sock.readyRead.connect(lambda s=sock: self._read_ipc_socket(s))
            sock.disconnected.connect(sock.deleteLater)
            if sock.bytesAvailable():
                self._read_ipc_socket(sock)

    def _read_ipc_socket(self, sock):
        try:
            previous = sock.property("engoIpcBuffer") or ""
            chunk = bytes(sock.readAll()).decode("utf-8", errors="replace")
            raw = previous + chunk
            if "\n" not in raw:
                sock.setProperty("engoIpcBuffer", raw)
                return
            message, _remainder = raw.split("\n", 1)
            sock.setProperty("engoIpcBuffer", "")
            payload = json.loads(message)
            paths = payload if isinstance(payload, list) else []
            valid = [os.path.abspath(path) for path in paths
                     if isinstance(path, str) and is_supported_document(path) and os.path.isfile(path)]
            if valid:
                QTimer.singleShot(0, lambda values=valid: [self.open_pdf(value) for value in values])
            else:
                QTimer.singleShot(0, self._bring_to_front)
            sock.write(b"OK\n")
            sock.flush()
        except Exception:
            QTimer.singleShot(0, self._bring_to_front)

    def _bring_to_front(self):
        if self.isMinimized():
            self.showNormal()
        self.raise_()
        self.activateWindow()

    def _build_ui(self):
        central = QWidget()
        central.setObjectName("mainRoot")
        outer = QVBoxLayout(central)
        outer.setContentsMargins(0, 0, 0, 0)
        outer.setSpacing(0)

        # Tabs are always the first row. Qt's native movable QTabBar reflows them live.
        self.tab_strip = QFrame()
        self.tab_strip.setObjectName("tabStrip")
        # Document tabs are a file-order control, not reading content: always
        # arrange them from left to right in every UI language.
        self.tab_strip.setLayoutDirection(Qt.LayoutDirection.LeftToRight)
        tab_row = QHBoxLayout(self.tab_strip)
        tab_row.setDirection(QBoxLayout.Direction.LeftToRight)
        tab_row.setContentsMargins(11, 5, 10, 5)
        tab_row.setSpacing(9)
        self.logo_mark = QLabel("E")
        self.logo_mark.setObjectName("logoMark")
        self.logo_mark.setAlignment(Qt.AlignmentFlag.AlignCenter)
        self.logo_mark.setFixedSize(29, 29)
        icon_path = resource_path("engopdfviewer.ico")
        if os.path.exists(icon_path):
            self.logo_mark.setText("")
            self.logo_mark.setPixmap(QIcon(icon_path).pixmap(QSize(28, 28)))
        tab_row.addWidget(self.logo_mark)
        self.brand_name = QLabel(APP_NAME)
        self.brand_name.setObjectName("brandTitle")
        tab_row.addWidget(self.brand_name)
        self._tab_order: list[DocumentTab] = []
        self.doc_tabbar = DocumentTabBar(self)
        self.doc_tabbar.setObjectName("documentTabBar")
        self.doc_tabbar.setLayoutDirection(Qt.LayoutDirection.LeftToRight)
        self.doc_tabbar.setShape(QTabBar.Shape.RoundedNorth)
        self.doc_tabbar.setExpanding(False)
        self.doc_tabbar.setUsesScrollButtons(True)
        # Use our own fixed-size vector close buttons. Native QTabBar close glyphs
        # are style/DPI dependent and were misaligned on several Windows setups.
        self.doc_tabbar.setTabsClosable(False)
        self.doc_tabbar.setElideMode(Qt.TextElideMode.ElideRight)
        self.doc_tabbar.setDrawBase(False)
        self.doc_tabbar.currentChanged.connect(self._on_top_tab_changed)
        self.doc_tabbar.currentChanged.connect(lambda _index: self._schedule_brand_title_update())
        self.doc_tabbar.tabMoved.connect(self._on_tabs_moved)
        self.doc_tabbar.tabMoved.connect(lambda *_args: self._schedule_brand_title_update())
        tab_row.addWidget(self.doc_tabbar, 1)
        self.new_tab_btn = self._button("", "tabAdd", "plus")
        self.new_tab_btn.setFixedSize(31, 29)
        self.new_tab_btn.setAccessibleName("Open PDF in a new tab")
        self.new_tab_btn.setToolTip("Open PDF in a new tab (Ctrl+O)")
        self.new_tab_btn.clicked.connect(self.open_dialog)
        tab_row.addWidget(self.new_tab_btn)
        self.link_docs_btn = self._button("", "tabAdd", "link")
        self.link_docs_btn.setFixedSize(31, 29)
        self.link_docs_btn.setAccessibleName("Combine two PDF tabs")
        self.link_docs_btn.setToolTip("Link two open PDFs as one study conversation: primary + supplementary")
        self.link_docs_btn.clicked.connect(self.configure_linked_pdfs)
        self.link_docs_btn.setEnabled(False)
        tab_row.addWidget(self.link_docs_btn)
        outer.addWidget(self.tab_strip)

        self.topbar = QFrame()
        self.topbar.setObjectName("topbar")
        self.topbar.setLayoutDirection(Qt.LayoutDirection.LeftToRight)
        top = QVBoxLayout(self.topbar)
        top.setContentsMargins(5, 4, 5, 4)
        top.setSpacing(3)
        self.toolbar_row_primary = QWidget(self.topbar)
        self.toolbar_row_secondary = QWidget(self.topbar)
        self.toolbar_row_primary.setLayoutDirection(Qt.LayoutDirection.LeftToRight)
        self.toolbar_row_secondary.setLayoutDirection(Qt.LayoutDirection.LeftToRight)
        primary_row = QHBoxLayout(self.toolbar_row_primary)
        primary_row.setContentsMargins(0, 0, 0, 0)
        primary_row.setSpacing(2)
        secondary_row = QHBoxLayout(self.toolbar_row_secondary)
        secondary_row.setContentsMargins(0, 0, 0, 0)
        secondary_row.setSpacing(2)
        primary_row.setAlignment(Qt.AlignmentFlag.AlignLeft)
        secondary_row.setAlignment(Qt.AlignmentFlag.AlignLeft)
        top.addWidget(self.toolbar_row_primary)
        top.addWidget(self.toolbar_row_secondary)
        self.toolbar_row_secondary.hide()
        self._toolbar_primary_layout = primary_row
        self._toolbar_secondary_layout = secondary_row

        def make_group(name):
            frame = QFrame()
            frame.setLayoutDirection(Qt.LayoutDirection.LeftToRight)
            frame.setObjectName("toolbarGroup")
            frame.setProperty("groupName", name)
            lay = QHBoxLayout(frame)
            lay.setContentsMargins(2, 2, 2, 2)
            lay.setSpacing(1)
            return frame, lay

        # File actions.
        self.file_group, file_row = make_group("file")
        self.open_btn = self._button("Home", "primary", "home")
        self.open_btn.setObjectName("homeTopButton")
        self.open_btn.setToolTip("Home · recent PDFs, settings, and last session")
        self.open_btn.setAccessibleName("Home")
        self.open_btn.clicked.connect(self._show_files_screen)
        file_row.addWidget(self.open_btn)
        self.save_btn = QToolButton()
        self.save_btn.setObjectName("saveSplitButton")
        self.save_btn.setText("Save")
        self.save_btn.setIcon(make_icon("save", "#b7c6dc", 18))
        self.save_btn.setIconSize(QSize(17, 17))
        self.save_btn.setToolButtonStyle(Qt.ToolButtonStyle.ToolButtonTextBesideIcon)
        self.save_btn.setPopupMode(QToolButton.ToolButtonPopupMode.MenuButtonPopup)
        self.save_btn.setCursor(Qt.CursorShape.PointingHandCursor)
        self.save_btn.setFocusPolicy(Qt.FocusPolicy.NoFocus)
        self.save_btn.setMinimumHeight(28)
        self.save_btn.setToolTip("Save changes · use the arrow for Save As")
        self.save_btn.setAccessibleName("Save PDF · dropdown for Save As")
        self.save_btn.clicked.connect(lambda: self.save_active(False))
        self.save_menu = QMenu(self.save_btn)
        save_as_action = self.save_menu.addAction(make_icon("save_as", "#b7c6dc", 18), "Save As…")
        save_as_action.setToolTip("Save a copy to another PDF path (Ctrl+Shift+S)")
        save_as_action.triggered.connect(lambda: self.save_active(True))
        self.save_btn.setMenu(self.save_menu)
        self.save_as_btn = self.save_btn  # compatibility for the existing enable/disable path
        file_row.addWidget(self.save_btn)
        self.search_btn = self._button("Search", "action", "search", "#91d5c4")
        self.search_btn.setToolTip("Search this entire PDF · exact text or AI search for concepts, handwriting, and images")
        self.search_btn.setAccessibleName("Search the whole PDF")
        self.search_btn.clicked.connect(self.open_pdf_search)
        file_row.addWidget(self.search_btn)
        primary_row.addWidget(self.file_group)

        # View layout actions.
        self.view_group_frame, view_row = make_group("view")
        self.sidebar_btn = self._button("Sidebar", "action", "sidebar")
        self.sidebar_btn.setObjectName("sidebarToggleButton")
        self.sidebar_btn.setCheckable(True)
        self.sidebar_btn.setToolTip("Show or hide page thumbnails and table of contents")
        self.sidebar_btn.clicked.connect(lambda: self._toggle_sidebar(self.active_tab()))
        view_row.addWidget(self.sidebar_btn)
        self.continuous_btn = self._button("Scroll", "mode", "continuous")
        self.continuous_btn.setToolTip("Scroll · connect pages vertically; turn off to show one page/spread at a time")
        self.continuous_btn.setCheckable(True)
        self.book_btn = self._button("Book", "mode", "book")
        self.book_btn.setToolTip("Book · show two pages side by side; can be combined with Scroll")
        self.book_btn.setCheckable(True)
        self.view_group = QButtonGroup(self)
        self.view_group.setExclusive(False)
        self.view_group.addButton(self.continuous_btn)
        self.view_group.addButton(self.book_btn)
        self.continuous_btn.clicked.connect(lambda checked: self._set_layout_option("scroll", checked))
        self.book_btn.clicked.connect(self._handle_book_or_unlink)
        view_row.addWidget(self.continuous_btn)
        view_row.addWidget(self.book_btn)
        primary_row.addWidget(self.view_group_frame)

        # Zoom and fit actions.
        self.zoom_group_frame, zoom_row = make_group("zoom")
        self.zoom_out_btn = self._button("Zoom Out", "action", "zoom_out")
        self.zoom_out_btn.setToolTip("Zoom out (Ctrl + mouse wheel down / Ctrl+-)")
        self.zoom_out_btn.clicked.connect(lambda: self._zoom(1 / 1.15))
        zoom_row.addWidget(self.zoom_out_btn)
        self.zoom_label = QLabel("Fit Width")
        self.zoom_label.setObjectName("zoomLabel")
        self.zoom_label.setMinimumWidth(46)
        self.zoom_label.setAlignment(Qt.AlignmentFlag.AlignCenter)
        self.zoom_label.setToolTip("Current zoom level")
        zoom_row.addWidget(self.zoom_label)
        self.zoom_in_btn = self._button("Zoom In", "action", "zoom_in")
        self.zoom_in_btn.setToolTip("Zoom in (Ctrl + mouse wheel up / touchpad pinch)")
        self.zoom_in_btn.clicked.connect(lambda: self._zoom(1.15))
        zoom_row.addWidget(self.zoom_in_btn)
        self.fit_width_btn = self._button("Fit Width", "action", "fit_width")
        self.fit_width_btn.setToolTip("Fit page to the available width")
        self.fit_width_btn.clicked.connect(lambda: self._set_fit_mode("width"))
        zoom_row.addWidget(self.fit_width_btn)
        self.fit_page_btn = self._button("Fit Page", "action", "fit_page")
        self.fit_page_btn.setToolTip("Fit the complete page inside the window")
        self.fit_page_btn.clicked.connect(lambda: self._set_fit_mode("page"))
        zoom_row.addWidget(self.fit_page_btn)
        primary_row.addWidget(self.zoom_group_frame)

        # Page navigation.
        self.navigation_group, nav_row = make_group("navigation")
        self.prev_btn = self._button("Previous", "action", "previous")
        self.prev_btn.setToolTip("Previous page (Left / Page Up)")
        self.prev_btn.clicked.connect(lambda: self._navigate(-1))
        nav_row.addWidget(self.prev_btn)
        self.page_spin = QSpinBox()
        self.page_spin.setObjectName("pageSpin")
        self.page_spin.setRange(1, 1)
        self.page_spin.setFixedWidth(48)
        self.page_spin.setAlignment(Qt.AlignmentFlag.AlignCenter)
        self.page_spin.setKeyboardTracking(False)
        self.page_spin.setToolTip("Jump to page number")
        self.page_spin.editingFinished.connect(self._jump_to_page)
        nav_row.addWidget(self.page_spin)
        self.page_total = QLabel("/ 0")
        self.page_total.setObjectName("muted")
        self.page_total.setMinimumWidth(28)
        nav_row.addWidget(self.page_total)
        self.next_btn = self._button("Next", "action", "next")
        self.next_btn.setToolTip("Next page (Right / Page Down)")
        self.next_btn.clicked.connect(lambda: self._navigate(1))
        nav_row.addWidget(self.next_btn)
        self.rotate_page_btn = QToolButton()
        self.rotate_page_btn.setObjectName("rotatePageAction")
        self.rotate_page_btn.setText("Rotate")
        self.rotate_page_btn.setIcon(make_icon("rotate_cw", "#b7c6dc", 18))
        self.rotate_page_btn.setIconSize(QSize(17, 17))
        self.rotate_page_btn.setToolButtonStyle(Qt.ToolButtonStyle.ToolButtonTextBesideIcon)
        self.rotate_page_btn.setPopupMode(QToolButton.ToolButtonPopupMode.MenuButtonPopup)
        self.rotate_page_btn.setMinimumHeight(28)
        self.rotate_page_btn.setCursor(Qt.CursorShape.PointingHandCursor)
        self.rotate_page_btn.setFocusPolicy(Qt.FocusPolicy.NoFocus)
        self.rotate_page_btn.setToolTip("Rotate the current PDF page 90° clockwise; use the arrow for the whole file")
        self.rotate_page_btn.setAccessibleName("Rotate current page clockwise; menu rotates all pages")
        self.rotate_page_menu = QMenu(self.rotate_page_btn)
        rotate_all_action = self.rotate_page_menu.addAction("Rotate all pages 90° clockwise")
        rotate_all_action.triggered.connect(self.rotate_all_pages_active)
        self.rotate_page_btn.setMenu(self.rotate_page_menu)
        self.rotate_page_btn.clicked.connect(self.rotate_current_page_active)
        nav_row.addWidget(self.rotate_page_btn)
        primary_row.addWidget(self.navigation_group)

        # One coherent annotation group with consistently drawn icons and visible action names.
        self.annotation_group_frame = QFrame()
        self.annotation_group_frame.setObjectName("annotationGroup")
        annotation = QHBoxLayout(self.annotation_group_frame)
        annotation.setContentsMargins(2, 2, 2, 2)
        annotation.setSpacing(1)
        self.tool_buttons = {}
        self.tool_group = QButtonGroup(self)
        self.tool_group.setExclusive(True)
        tool_items = [
            ("select", "Select", "Select annotations, read, or activate links", "#b7c6dc"),
            ("pen", "Pen", "Draw freehand ink on the page", "#80adff"),
            ("highlight", "Highlight", "Highlight selectable text or mark a scanned area", "#f0cf65"),
            ("note", "Note", "Add a sticky-note comment", "#c5a0ff"),
            ("text", "Text", "Place editable text on the page", "#83d6c5"),
            ("link", "Link", "Draw an internal link to another page", "#7ad4dc"),
        ]
        # Annotation/note tools are intentionally icon-only. Keep full labels in
        # tooltips and accessibility names; leave every other toolbar group untouched.
        for key, label, tip, color in tool_items:
            if key == "select":
                # Select and Hand share one toolbar slot. The main button keeps the
                # currently active mode; its menu arrow switches between the two.
                btn = QToolButton()
                btn.setObjectName("selectTool")
                btn.setIcon(make_icon("select", color, 18))
                btn.setIconSize(QSize(18, 18))
                btn.setToolButtonStyle(Qt.ToolButtonStyle.ToolButtonIconOnly)
                btn.setPopupMode(QToolButton.ToolButtonPopupMode.MenuButtonPopup)
                btn.setCheckable(True)
                btn.setFixedSize(40, 29)
                btn.setCursor(Qt.CursorShape.PointingHandCursor)
                btn.setFocusPolicy(Qt.FocusPolicy.NoFocus)
                btn.setToolTip(tip + " · use the menu to switch to Hand/Pan")
                btn.setAccessibleName("Select / Hand tool")
                btn.setProperty("engoIconName", "select")
                btn.setProperty("engoIconBaseColor", color)
                self.select_tool_btn = btn
                self.select_tool_menu = QMenu(btn)
                self.select_action = QAction(make_icon("select", color, 18), "Select", self.select_tool_menu)
                self.select_action.setCheckable(True)
                self.pan_action = QAction(make_icon("hand", color, 18), "Hand", self.select_tool_menu)
                self.pan_action.setCheckable(True)
                self.select_tool_menu.addAction(self.select_action)
                self.select_tool_menu.addAction(self.pan_action)
                self.select_action.triggered.connect(lambda checked=False: self._set_tool("select"))
                self.pan_action.triggered.connect(lambda checked=False: self._set_tool("pan"))
                self.select_tool_menu.aboutToShow.connect(self._refresh_select_tool_menu)
                btn.setMenu(self.select_tool_menu)
                btn.clicked.connect(self._select_tool_button_clicked)
            else:
                btn = self._button("", "tool", key, color)
                btn.setCheckable(True)
                btn.setToolTip(tip)
                btn.setAccessibleName(label)
                btn.setFixedSize(32, 29)
                btn.clicked.connect(lambda checked=False, t=key: self._set_tool(t))
            self.tool_group.addButton(btn)
            self.tool_buttons[key] = btn
            annotation.addWidget(btn)
        self.tag_tool_btn = QToolButton()
        self.tag_tool_btn.setObjectName("tagTool")
        self.tag_tool_btn.setIcon(make_icon("tag", "#d5b1ff", 18))
        self.tag_tool_btn.setIconSize(QSize(18, 18))
        self.tag_tool_btn.setToolButtonStyle(Qt.ToolButtonStyle.ToolButtonIconOnly)
        self.tag_tool_btn.setPopupMode(QToolButton.ToolButtonPopupMode.MenuButtonPopup)
        self.tag_tool_btn.setCheckable(True)
        self.tag_tool_btn.setFixedSize(40, 29)
        self.tag_tool_btn.setCursor(Qt.CursorShape.PointingHandCursor)
        self.tag_tool_btn.setFocusPolicy(Qt.FocusPolicy.NoFocus)
        self.tag_tool_btn.setToolTip("Tag region · drag over an area to assign the selected tag; use the arrow to choose or edit tags")
        self.tag_tool_btn.setAccessibleName("Tag region and choose tag")
        self.tag_menu = QMenu(self.tag_tool_btn)
        self.tag_tool_btn.setMenu(self.tag_menu)
        self.tag_tool_btn.clicked.connect(lambda: self._set_tool("tag"))
        self.tool_group.addButton(self.tag_tool_btn)
        self.tool_buttons["tag"] = self.tag_tool_btn
        annotation.addWidget(self.tag_tool_btn)
        self.tool_buttons["select"].setChecked(True)
        self.undo_btn = self._button("", "history", "undo")
        self.undo_btn.setAccessibleName("Undo")
        self.undo_btn.setFixedSize(32, 29)
        self.undo_btn.setToolTip("Undo last PDF edit (Ctrl+Z)")
        self.undo_btn.clicked.connect(self.undo_active)
        annotation.addWidget(self.undo_btn)
        self.redo_btn = self._button("", "history", "redo")
        self.redo_btn.setAccessibleName("Redo")
        self.redo_btn.setFixedSize(32, 29)
        self.redo_btn.setToolTip("Redo the last undone edit (Ctrl+Y)")
        self.redo_btn.clicked.connect(self.redo_active)
        annotation.addWidget(self.redo_btn)
        self.delete_btn = self._button("", "deleteTool", "delete", "#e79aa5")
        self.delete_btn.setAccessibleName("Delete annotation")
        self.delete_btn.setFixedSize(32, 29)
        self.delete_btn.setToolTip("Delete the selected annotation (Delete key)")
        self.delete_btn.clicked.connect(self.delete_selected_active)
        annotation.addWidget(self.delete_btn)
        self.annot_colors_btn = self._button("", "action", "palette", "#b8a2ff")
        self.annot_colors_btn.setAccessibleName("Annotation colors")
        self.annot_colors_btn.setFixedSize(32, 29)
        self.annot_colors_btn.setToolTip("Annotation colors · pen, highlight, note, and text box")
        self.annot_colors_btn.clicked.connect(self.open_annotation_colors)
        annotation.addWidget(self.annot_colors_btn)
        primary_row.addWidget(self.annotation_group_frame)

        # Utility actions.
        self.utility_group, utility_row = make_group("utility")
        self.theme_btn = self._button("Page Theme", "action", "theme", "#91b4ff")
        self.theme_btn.setToolTip("Page Theme · dark mode and custom document colors")
        self.theme_btn.clicked.connect(self.open_page_theme)
        utility_row.addWidget(self.theme_btn)
        self.ai_chat_btn = self._button("AI Chat", "action", "ai", "#9fbaff")
        self.ai_chat_btn.setCheckable(True)
        self.ai_chat_btn.setToolTip("Open the AI study chat for summaries, explanations, translation, and OCR")
        self.ai_chat_btn.clicked.connect(self.toggle_ai_panel)
        utility_row.addWidget(self.ai_chat_btn)
        self.live_tutor_btn = self._button("Audio lesson with AI", "action", "voice_learn", "#7dd8c2")
        # Do not pin this button to a wide minimum: its caption is allowed to collapse to icon-only.
        self.live_tutor_btn.setMinimumWidth(0)
        self.live_tutor_btn.setSizePolicy(QSizePolicy.Policy.Minimum, QSizePolicy.Policy.Fixed)
        self.live_tutor_btn.setToolTip("Audio lesson with AI · a live spoken lesson based on the current PDF page")
        self.live_tutor_btn.setAccessibleName("Audio lesson with AI")
        # Defer opening until the toolbar mouse-release event has fully finished;
        # otherwise the newly shown lesson window can race with the same click.
        self.live_tutor_btn.clicked.connect(lambda: QTimer.singleShot(0, self.open_live_tutor))
        utility_row.addWidget(self.live_tutor_btn)
        self.translate_btn = self._button("Translate", "action", "translate", "#8fe0c0")
        self.translate_btn.setToolTip("Translate a selected PDF region in Engo · choose a region, then see a popup card")
        self.translate_btn.clicked.connect(self.start_translate_selection)
        utility_row.addWidget(self.translate_btn)
        self.present_btn = self._button("Present", "action", "present")
        self.present_btn.setToolTip("Presentation mode (F5)")
        self.present_btn.clicked.connect(self.toggle_presentation)
        utility_row.addWidget(self.present_btn)
        self.full_btn = self._button("Full Screen", "action", "fullscreen")
        self.full_btn.setToolTip("Toggle distraction-free full screen (F11)")
        self.full_btn.clicked.connect(self.toggle_fullscreen)
        utility_row.addWidget(self.full_btn)
        self.toolbar_pin_btn = self._button("", "action", "pin", "#b6c9e6")
        self.toolbar_pin_btn.setObjectName("toolbarPinButton")
        self.toolbar_pin_btn.setFixedSize(30, 29)
        self.toolbar_pin_btn.setCheckable(True)
        self.toolbar_pin_btn.setChecked(True)
        self.toolbar_pin_btn.setToolTip("Unpin toolbar · it will auto-hide when the pointer leaves")
        self.toolbar_pin_btn.setAccessibleName("Pin toolbar")
        self.toolbar_pin_btn.toggled.connect(self._set_toolbar_pinned)
        utility_row.addWidget(self.toolbar_pin_btn)
        # Keep the utility buttons packed together; no stretch spacer is inserted
        # between actions, and the group itself does not expand into empty width.
        utility_row.setSpacing(2)
        self.utility_group.setSizePolicy(QSizePolicy.Policy.Minimum, QSizePolicy.Policy.Fixed)
        primary_row.addWidget(self.utility_group)
        self._toolbar_groups = [self.file_group, self.view_group_frame, self.zoom_group_frame,
                                self.navigation_group, self.annotation_group_frame, self.utility_group]

        outer.addWidget(self.topbar)

        self.workspace = QSplitter(Qt.Orientation.Horizontal)
        self.workspace.setObjectName("workspaceSplitter")
        # The document stays on the left and AI chat stays docked on the right
        # regardless of the Windows display language / Qt locale direction.
        # Explicit LTR ordering also makes the chat reveal/collapse animation
        # sweep consistently in opposite directions when opening vs. closing.
        self.workspace.setLayoutDirection(Qt.LayoutDirection.LeftToRight)
        self.workspace.setChildrenCollapsible(False)
        self.tabs = QStackedWidget()
        self.tabs.setObjectName("documentStack")
        self.document_host = QStackedWidget()
        self.document_host.setObjectName("documentHost")
        self.welcome_page = self._build_welcome_page()
        self.document_host.addWidget(self.welcome_page)
        self.document_host.addWidget(self.tabs)
        self.document_host.setCurrentWidget(self.welcome_page)
        self.workspace.addWidget(self.document_host)
        self.ai_panel = AIChatPanel(self.settings, self)
        self.ai_panel.requestSent.connect(self.send_ai_request)
        # Coalesce transcript reflow after a resize settles. Rebuilding every
        # time the window emits resizeEvent can interrupt smooth splitter motion.
        self._chat_transcript_resize_timer = QTimer(self)
        self._chat_transcript_resize_timer.setSingleShot(True)
        self._chat_transcript_resize_timer.setInterval(150)
        self._chat_transcript_resize_timer.timeout.connect(self._finish_chat_transcript_resize)
        # A dragged splitter changes the chat viewport without resizing the main
        # window. Keep the visible assistant bubbles following that live width,
        # then reflow the full transcript once the splitter stops moving.
        self._chat_transcript_live_reflow_timer = QTimer(self)
        self._chat_transcript_live_reflow_timer.setInterval(45)
        self._chat_transcript_live_reflow_timer.timeout.connect(
            self._reflow_visible_chat_transcript_during_resize
        )
        self.workspace.splitterMoved.connect(self._on_workspace_splitter_moved)
        self.ai_panel.hide()
        self.workspace.addWidget(self.ai_panel)
        self.teach_board = TeachBoardPanel(self)
        self.teach_board.hide()
        self.workspace.addWidget(self.teach_board)
        self.workspace.setStretchFactor(0, 1)
        self.workspace.setStretchFactor(1, 0)
        self.workspace.setStretchFactor(2, 0)
        self.workspace.setSizes([1160, 500, 0])
        outer.addWidget(self.workspace, 1)

        self.status = QStatusBar()
        self.status.setObjectName("appStatus")
        self.status.setSizeGripEnabled(False)
        self.context_help_icon = QLabel("ⓘ")
        self.context_help_icon.setObjectName("contextHelpIcon")
        self.context_help_icon.setAlignment(Qt.AlignmentFlag.AlignCenter)
        self.context_help_icon.setAttribute(Qt.WidgetAttribute.WA_TransparentForMouseEvents, True)
        self.context_help_label = QLabel("")
        self.context_help_label.setObjectName("contextHelpLabel")
        self.context_help_label.setMinimumWidth(0)
        self.context_help_label.setSizePolicy(QSizePolicy.Policy.Expanding, QSizePolicy.Policy.Preferred)
        self.context_help_label.setTextInteractionFlags(Qt.TextInteractionFlag.NoTextInteraction)
        self.context_help_label.setAttribute(Qt.WidgetAttribute.WA_TransparentForMouseEvents, True)
        self.status.addWidget(self.context_help_icon, 0)
        self.status.addWidget(self.context_help_label, 1)
        outer.addWidget(self.status)
        self.setCentralWidget(central)
        self._sidebar_animation = None
        self._view_animation = None
        self._apply_toolbar_density()
        self._schedule_toolbar_density_update()
    def _build_welcome_page(self):
        page = QWidget()
        page.setObjectName("filesHome")
        page_row = QHBoxLayout(page)
        page_row.setContentsMargins(0, 0, 0, 0)
        page_row.setSpacing(0)
        # The Home sidebar is placed in its own splitter so its complete width
        # (browser, navigation, Settings and footer) can be resized by dragging.
        # Keep the user's selected width in QSettings across restarts.
        self.home_sidebar = QFrame()
        self.home_sidebar.setObjectName("homeSidebar")
        self._home_sidebar_reference_width = 325
        self._home_sidebar_min_width = max(160, round(self._home_sidebar_reference_width * 0.70))
        self._home_sidebar_max_width = round(self._home_sidebar_reference_width * 1.70)
        try:
            saved_home_sidebar_width = int(self.settings.value(
                "home_sidebar_width", self._home_sidebar_reference_width, type=int
            ))
        except (TypeError, ValueError):
            saved_home_sidebar_width = self._home_sidebar_reference_width
        saved_home_sidebar_width = max(
            self._home_sidebar_min_width,
            min(self._home_sidebar_max_width, saved_home_sidebar_width),
        )
        self.home_sidebar.setMinimumWidth(self._home_sidebar_min_width)
        self.home_sidebar.setMaximumWidth(self._home_sidebar_max_width)
        self.home_sidebar.setSizePolicy(QSizePolicy.Policy.Preferred, QSizePolicy.Policy.Expanding)
        side = QVBoxLayout(self.home_sidebar)
        side.setContentsMargins(10, 10, 10, 12)
        side.setSpacing(7)
        self.home_side_title = QLabel("Home")
        self.home_side_title.setObjectName("homeSideTitle")
        side.addWidget(self.home_side_title)
        self.home_nav_btn = QPushButton("⌂   Home")
        self.home_nav_btn.setObjectName("homeNavActive")
        self.home_nav_btn.clicked.connect(self._refresh_files_home)
        self.home_nav_btn.hide()  # the large Home heading is the single sidebar Home label
        self.return_to_docs_btn = QPushButton("Return to open files")
        self.return_to_docs_btn.setObjectName("homeNav")
        self.return_to_docs_btn.setFixedHeight(30)
        self.return_to_docs_btn.setProperty("homeActionHeight", True)
        self.return_to_docs_btn.setSizePolicy(QSizePolicy.Policy.Expanding, QSizePolicy.Policy.Fixed)
        self.return_to_docs_btn.setIcon(make_icon("previous", "#b7c6dc", 16))
        self.return_to_docs_btn.setIconSize(QSize(16, 16))
        # Keep the return arrow on the RIGHT side of the label in both UI languages.
        self.return_to_docs_btn.setLayoutDirection(Qt.LayoutDirection.RightToLeft)
        self.return_to_docs_btn.setToolTip("Return to open PDFs")
        self.return_to_docs_btn.setAccessibleName("Return to open PDFs")
        self.return_to_docs_btn.setVisible(self.tabs.count() > 0)
        self.return_to_docs_btn.clicked.connect(self._show_document_area)
        # Both navigation buttons fill the same sidebar width, so their
        # outlined rectangles stay identical in Arabic and English.
        side.addWidget(self.return_to_docs_btn)
        side.addSpacing(5)
        self.home_settings_btn = QPushButton("Settings")
        self.home_settings_btn.setObjectName("homeSettingsNav")
        self.home_settings_btn.setFixedHeight(30)
        self.home_settings_btn.setProperty("homeActionHeight", True)
        self.home_settings_btn.setSizePolicy(QSizePolicy.Policy.Expanding, QSizePolicy.Policy.Fixed)
        self.home_settings_btn.setIcon(make_icon("settings", "#b7c6dc", 18))
        self.home_settings_btn.setIconSize(QSize(18, 18))
        self.home_settings_btn.setToolTip("Settings")
        self.home_settings_btn.setAccessibleName("Application settings")
        self.home_settings_btn.clicked.connect(self.open_app_settings)
        side.addWidget(self.home_settings_btn)
        # Let the file browser consume the sidebar height; keep Settings directly
        # underneath it instead of leaving a large empty spacer before the footer.
        side.addStretch(0)
        self.home_side_footer = QLabel(HOME_FOOTER_TEXT)
        self.home_side_footer.setObjectName("homeSideFooter")
        self.home_side_footer.setWordWrap(True)
        self.home_side_footer.setLayoutDirection(Qt.LayoutDirection.LeftToRight)
        self.home_side_footer.setAlignment(Qt.AlignmentFlag.AlignLeft | Qt.AlignmentFlag.AlignVCenter)
        side.addWidget(self.home_side_footer)
        self.home_page_splitter = QSplitter(Qt.Orientation.Horizontal, page)
        self.home_page_splitter.setObjectName("homePageSplitter")
        # Keep the sidebar on the physical left in both Arabic and English.
        self.home_page_splitter.setLayoutDirection(Qt.LayoutDirection.LeftToRight)
        self.home_page_splitter.setChildrenCollapsible(False)
        self.home_page_splitter.setHandleWidth(7)
        self.home_page_splitter.addWidget(self.home_sidebar)
        content = QWidget()
        content.setObjectName("filesHomeContent")
        content.setMinimumWidth(0)
        self.home_page_splitter.addWidget(content)
        self.home_page_splitter.setStretchFactor(0, 0)
        self.home_page_splitter.setStretchFactor(1, 1)
        self.home_page_splitter.setCollapsible(0, False)
        self.home_page_splitter.setCollapsible(1, False)
        self._home_sidebar_desired_width = saved_home_sidebar_width
        self._home_sidebar_width_restored = False
        self.home_page_splitter.setSizes([saved_home_sidebar_width, 1100])
        page_row.addWidget(self.home_page_splitter, 1)

        self._home_sidebar_save_timer = QTimer(self)
        self._home_sidebar_save_timer.setSingleShot(True)
        self._home_sidebar_save_timer.setInterval(300)
        self._home_sidebar_save_timer.timeout.connect(self._save_home_sidebar_width)
        self.home_page_splitter.splitterMoved.connect(self._schedule_home_sidebar_width_save)
        root = QVBoxLayout(content)
        root.setContentsMargins(34, 26, 34, 22)
        root.setSpacing(18)

        header = QHBoxLayout()
        logo = QLabel()
        logo.setObjectName("filesHomeLogo")
        logo.setFixedSize(66, 66)
        icon_path = resource_path("engopdfviewer.ico")
        if os.path.exists(icon_path):
            logo.setPixmap(QIcon(icon_path).pixmap(QSize(62, 62)))
        else:
            logo.setText("E")
            logo.setAlignment(Qt.AlignmentFlag.AlignCenter)
        header.addWidget(logo)
        brand_col = QVBoxLayout()
        # Tighten the title/subtitle stack so the tagline sits a little closer
        # to the product name without changing the surrounding header geometry.
        brand_col.setSpacing(0)
        brand = QLabel(APP_NAME)
        brand.setObjectName("filesHomeTitle")
        subtitle = QLabel("Your study space for PDFs, notes & an AI teacher")
        subtitle.setObjectName("filesHomeSubtitle")
        brand_col.addWidget(brand)
        brand_col.addWidget(subtitle)
        header.addLayout(brand_col, 1)
        root.addLayout(header)

        hero = QFrame()
        hero.setObjectName("filesHero")
        hero_layout = QVBoxLayout(hero)
        hero_layout.setContentsMargins(24, 22, 24, 22)
        hero_layout.setSpacing(10)
        greeting = QLabel("Welcome back")
        greeting.setObjectName("filesHeroTitle")
        hero_layout.addWidget(greeting)
        hint = QLabel("Open PDF, Word, PowerPoint or image files to read them. You can also drop supported files here.")
        hint.setObjectName("filesHeroHint")
        hint.setWordWrap(True)
        hero_layout.addWidget(hint)
        actions = QHBoxLayout()
        self.files_open_new_btn = QPushButton("＋  Open documents or images")
        self.files_open_new_btn.setObjectName("filesPrimaryButton")
        # Keep the button at its natural content width; only its height is shared
        # with the adjacent Restore button.
        self.files_open_new_btn.setFixedHeight(31)
        self.files_open_new_btn.setProperty("homeActionHeight", True)
        self.files_open_new_btn.setSizePolicy(QSizePolicy.Policy.Preferred, QSizePolicy.Policy.Fixed)
        self.files_open_new_btn.clicked.connect(self.open_dialog)
        actions.addWidget(self.files_open_new_btn)
        self.files_restore_btn = QPushButton("↺  Reopen last session")
        self.files_restore_btn.setObjectName("filesSecondaryButton")
        self.files_restore_btn.setFixedHeight(31)
        self.files_restore_btn.setProperty("homeActionHeight", True)
        self.files_restore_btn.setSizePolicy(QSizePolicy.Policy.Preferred, QSizePolicy.Policy.Fixed)
        self.files_restore_btn.clicked.connect(self._restore_last_session)
        actions.addWidget(self.files_restore_btn)
        actions.addStretch(1)
        hero_layout.addLayout(actions)
        self.last_session_summary = QLabel("")
        self.last_session_summary.setObjectName("filesSessionSummary")
        self.last_session_summary.setWordWrap(True)
        hero_layout.addWidget(self.last_session_summary)
        drop_hint = QLabel("DROP PDF, WORD, POWERPOINT OR IMAGE FILES HERE")
        drop_hint.setObjectName("filesDropHint")
        drop_hint.setAlignment(Qt.AlignmentFlag.AlignCenter)
        hero_layout.addWidget(drop_hint)
        root.addWidget(hero)

        # Compact, expandable file tree: folders are navigable through tree branches
        # and supported documents open on double-click.
        browser = QFrame()
        browser.setObjectName("homeFileBrowser")
        browser_layout = QVBoxLayout(browser)
        browser_layout.setContentsMargins(12, 9, 12, 9)
        browser_layout.setSpacing(6)
        browser_header = QHBoxLayout()
        self.home_browser_title = QLabel("Browse files")
        self.home_browser_title.setObjectName("filesSectionTitle")
        browser_header.addWidget(self.home_browser_title)
        browser_header.addStretch(1)
        browser_layout.addLayout(browser_header)
        browser_path_row = QHBoxLayout()
        # Start at the Windows computer root (available drives), not the user's
        # profile directory. An empty QFileSystemModel root exposes the drives.
        self.home_browser_path = QLineEdit("This PC")
        self.home_browser_path.setObjectName("homeBrowserPath")
        self.home_browser_path.setPlaceholderText("This PC")
        self.home_browser_path.returnPressed.connect(self._home_browser_go)
        self.home_browser_path.setMaximumHeight(25)
        self.home_browser_path.setToolTip("Enter a folder path and press Enter")
        browser_path_row.addWidget(self.home_browser_path, 1)
        browser_layout.addLayout(browser_path_row)

        # A horizontal breadcrumb strip makes deep folder branches navigable.
        # Its own horizontal scrollbar appears only when the path is wider than
        # the available sidebar width; clicking any segment jumps to that folder.
        self.home_browser_breadcrumb_scroll = QScrollArea(browser)
        self.home_browser_breadcrumb_scroll.setObjectName("homeBrowserBreadcrumbScroll")
        self.home_browser_breadcrumb_scroll.setWidgetResizable(False)
        self.home_browser_breadcrumb_scroll.setFrameShape(QFrame.Shape.NoFrame)
        self.home_browser_breadcrumb_scroll.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAsNeeded)
        self.home_browser_breadcrumb_scroll.setVerticalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        self.home_browser_breadcrumb_scroll.setFixedHeight(39)
        self.home_browser_breadcrumb_scroll.setLayoutDirection(Qt.LayoutDirection.LeftToRight)
        self.home_browser_breadcrumb_host = QWidget()
        self.home_browser_breadcrumb_host.setObjectName("homeBrowserBreadcrumbHost")
        self.home_browser_breadcrumb_host.setLayoutDirection(Qt.LayoutDirection.LeftToRight)
        self.home_browser_breadcrumb_layout = QHBoxLayout(self.home_browser_breadcrumb_host)
        self.home_browser_breadcrumb_layout.setContentsMargins(1, 1, 1, 2)
        self.home_browser_breadcrumb_layout.setSpacing(3)
        self.home_browser_breadcrumb_scroll.setWidget(self.home_browser_breadcrumb_host)
        # The path editor below is the single navigation indicator.  Do not
        # show a second breadcrumb strip above the tree.
        self.home_browser_breadcrumb_scroll.hide()

        self.home_browser_model = EngoFileSystemModel(self)
        self.home_browser_model.setReadOnly(True)
        self.home_browser_model.setFilter(
            QDir.Filter.Drives | QDir.Filter.AllDirs | QDir.Filter.Files | QDir.Filter.NoDotAndDotDot
        )
        self.home_browser_model.setNameFilters([
            "*.pdf", "*.png", "*.jpg", "*.jpeg", "*.webp",
            "*.bmp", "*.tif", "*.tiff", "*.gif", "*.docx", "*.pptx",
        ])
        self.home_browser_model.setNameFilterDisables(False)
        self.home_browser_tree = QTreeView()
        self.home_browser_tree.setObjectName("homeBrowserTree")
        self.home_browser_tree.setModel(self.home_browser_model)
        self.home_browser_tree.setHeaderHidden(True)
        self.home_browser_tree.setRootIsDecorated(True)
        self.home_browser_tree.setItemsExpandable(True)
        self.home_browser_tree.setExpandsOnDoubleClick(True)
        self.home_browser_tree.setAnimated(True)
        self.home_browser_tree.setIndentation(17)
        self.home_browser_tree.setUniformRowHeights(True)
        self.home_browser_tree.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAsNeeded)
        self.home_browser_tree.setHorizontalScrollMode(QAbstractItemView.ScrollMode.ScrollPerPixel)
        self.home_browser_tree.setTextElideMode(Qt.TextElideMode.ElideNone)
        self.home_browser_tree.horizontalScrollBar().setSingleStep(28)
        self.home_browser_tree.setSelectionBehavior(QAbstractItemView.SelectionBehavior.SelectRows)
        self.home_browser_tree.setSelectionMode(QAbstractItemView.SelectionMode.SingleSelection)
        self.home_browser_tree.setEditTriggers(QAbstractItemView.EditTrigger.NoEditTriggers)
        self.home_browser_tree.setSortingEnabled(True)
        self.home_browser_tree.sortByColumn(0, Qt.SortOrder.AscendingOrder)
        self.home_browser_tree.setColumnHidden(1, True)
        self.home_browser_tree.setColumnHidden(2, True)
        self.home_browser_tree.setColumnHidden(3, True)
        self.home_browser_tree.setMinimumHeight(100)
        self.home_browser_tree.doubleClicked.connect(self._home_browser_tree_activated)
        self.home_browser_tree.clicked.connect(self._home_browser_branch_clicked)
        self.home_browser_tree.expanded.connect(self._home_browser_branch_expanded)
        self.home_browser_tree.collapsed.connect(self._home_browser_branch_collapsed)
        self.home_browser_tree.expanded.connect(lambda *_: self._home_browser_schedule_tree_width())
        self.home_browser_tree.collapsed.connect(lambda *_: self._home_browser_schedule_tree_width())
        self.home_browser_model.directoryLoaded.connect(lambda *_: self._home_browser_schedule_tree_width())
        self.home_browser_model.rowsInserted.connect(lambda *_: self._home_browser_schedule_tree_width())
        self.home_browser_tree.installEventFilter(self)
        self.home_browser_tree.viewport().installEventFilter(self)
        browser_layout.addWidget(self.home_browser_tree, 1)
        root.addWidget(browser)
        # The quick browser belongs in Home navigation, not in the main content column.
        root.removeWidget(browser)
        browser.setMinimumWidth(0)
        browser.setSizePolicy(QSizePolicy.Policy.Expanding, QSizePolicy.Policy.Expanding)
        browser_layout.setContentsMargins(7, 7, 7, 7)
        browser_layout.setSpacing(5)
        browser_path_row.setContentsMargins(0, 0, 0, 0)
        browser_path_row.setSpacing(3)
        self.home_browser_tree.setSizePolicy(QSizePolicy.Policy.Expanding, QSizePolicy.Policy.Expanding)
        # Place the file browser in the sidebar immediately above Settings.
        # Do not reference an undefined legacy `side_label` name here: this path
        # runs while the Home page is being constructed at application startup.
        browser_insert_index = side.indexOf(self.home_settings_btn)
        if browser_insert_index < 0:
            browser_insert_index = side.indexOf(self.home_side_footer)
        if browser_insert_index < 0:
            side.addWidget(browser, 1)
        else:
            side.insertWidget(browser_insert_index, browser, 1)
        side.setStretch(side.indexOf(browser), 1)
        self._home_browser_current_dir = ""  # Empty means This PC / available drives.
        self._home_browser_breadcrumb_focus_dir = ""
        self._refresh_home_browser()
        QTimer.singleShot(180, self._home_browser_schedule_tree_width)

        recent_header = QHBoxLayout()
        recent_title = QLabel("Recent files")
        recent_title.setObjectName("filesSectionTitle")
        recent_header.addWidget(recent_title)
        recent_header.addStretch(1)
        self.recent_count_label = QLabel("")
        self.recent_count_label.setObjectName("filesSectionHint")
        recent_header.addWidget(self.recent_count_label)
        root.addLayout(recent_header)

        self.recent_files_host = QWidget()
        self.recent_files_layout = QVBoxLayout(self.recent_files_host)
        self.recent_files_layout.setContentsMargins(0, 0, 0, 0)
        self.recent_files_layout.setSpacing(7)
        self.recent_files_scroll = QScrollArea()
        self.recent_files_scroll.setObjectName("recentFilesScroll")
        self.recent_files_scroll.setWidgetResizable(True)
        self.recent_files_scroll.setFrameShape(QFrame.Shape.NoFrame)
        self.recent_files_scroll.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        self.recent_files_scroll.setVerticalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAsNeeded)
        self.recent_files_scroll.setWidget(self.recent_files_host)
        self.recent_files_scroll.setMinimumHeight(150)
        self.recent_files_scroll.setSizePolicy(QSizePolicy.Policy.Expanding, QSizePolicy.Policy.Expanding)
        root.addWidget(self.recent_files_scroll, 1)
        self._refresh_files_home()
        return page

    def _restore_home_sidebar_width(self):
        """Apply the saved sidebar width after the Home splitter has a real size."""
        if getattr(self, "_home_sidebar_width_restored", False):
            return
        splitter = getattr(self, "home_page_splitter", None)
        if splitter is None:
            return
        try:
            available = int(splitter.width())
            if available <= 0:
                return
            desired = int(getattr(self, "_home_sidebar_desired_width", self._home_sidebar_reference_width))
            desired = max(self._home_sidebar_min_width, min(self._home_sidebar_max_width, desired))
            # Use the actual splitter extent so the first pane restores to the
            # selected pixel width rather than merely a saved proportion.
            desired = min(desired, max(self._home_sidebar_min_width, available - splitter.handleWidth() - 1))
            remainder = max(1, available - splitter.handleWidth() - desired)
            splitter.setSizes([desired, remainder])
            self._home_sidebar_width_restored = True
        except (RuntimeError, AttributeError, TypeError, ValueError):
            pass

    def _schedule_home_sidebar_width_save(self, *_args):
        """Debounce persistence while the user drags the Home sidebar splitter."""
        timer = getattr(self, "_home_sidebar_save_timer", None)
        if timer is not None:
            timer.start()

    def _save_home_sidebar_width(self):
        """Persist the current Home sidebar width, bounded to 70%-170% of baseline."""
        splitter = getattr(self, "home_page_splitter", None)
        if splitter is None:
            return
        try:
            sizes = splitter.sizes()
            width = int(sizes[0]) if sizes else int(self.home_sidebar.width())
            width = max(self._home_sidebar_min_width, min(self._home_sidebar_max_width, width))
            self.settings.setValue("home_sidebar_width", width)
            self.settings.sync()
        except (RuntimeError, AttributeError, TypeError, ValueError):
            pass

    def _refresh_home_browser(self):
        if not hasattr(self, "home_browser_tree"):
            return
        current = str(getattr(self, "_home_browser_current_dir", "") or "").strip()
        self._home_browser_breadcrumb_focus_dir = current
        self._home_browser_refreshing = True
        language = str(self.settings.value("interface_language", "en", type=str) or "en").lower()
        is_ar = language.startswith("ar")
        try:
            if not current:
                # QFileSystemModel exposes the available drives at its invalid root.
                # This is the native equivalent of the Windows "This PC" view.
                self._home_browser_current_dir = ""
                self.home_browser_path.setText("هذا الكمبيوتر" if is_ar else "This PC")
                root_index = self.home_browser_model.setRootPath("")
                self.home_browser_tree.setRootIndex(root_index)
            else:
                folder = os.path.abspath(os.path.expanduser(current))
                if not os.path.isdir(folder):
                    self._home_browser_current_dir = ""
                    self.home_browser_path.setText("هذا الكمبيوتر" if is_ar else "This PC")
                    root_index = self.home_browser_model.setRootPath("")
                    self.home_browser_tree.setRootIndex(root_index)
                else:
                    self._home_browser_current_dir = folder
                    self.home_browser_path.setText(folder)
                    root_index = self.home_browser_model.setRootPath(folder)
                    self.home_browser_tree.setRootIndex(root_index)
            self.home_browser_tree.collapseAll()
        except Exception as exc:
            self.home_browser_path.setToolTip(f"Unable to browse folder: {exc}")
        self._home_browser_refreshing = False
        self._home_browser_update_breadcrumb()

    def _home_browser_schedule_tree_width(self, *_args):
        """Debounce width measurement while QFileSystemModel loads/expands folders."""
        if not hasattr(self, "home_browser_tree"):
            return
        timer = getattr(self, "_home_browser_tree_width_timer", None)
        if timer is None:
            timer = QTimer(self)
            timer.setSingleShot(True)
            timer.setInterval(90)
            timer.timeout.connect(self._home_browser_update_tree_width)
            self._home_browser_tree_width_timer = timer
        timer.start()

    def _home_browser_update_tree_width(self):
        """Give the tree column enough width for complete names and enable real horizontal scrolling."""
        tree = getattr(self, "home_browser_tree", None)
        model = getattr(self, "home_browser_model", None)
        if tree is None or model is None:
            return
        try:
            metrics = tree.fontMetrics()
            indentation = max(0, int(tree.indentation()))
            widest = max(180, int(tree.viewport().width()) - 4)
            visited = 0
            root = tree.rootIndex()

            def measure(parent_index, depth=0):
                nonlocal widest, visited
                if visited >= 3000:
                    return
                rows = model.rowCount(parent_index)
                for row in range(rows):
                    if visited >= 3000:
                        break
                    index = model.index(row, 0, parent_index)
                    if not index.isValid():
                        continue
                    visited += 1
                    label = str(model.data(index, Qt.ItemDataRole.DisplayRole) or "")
                    text_width = metrics.horizontalAdvance(label)
                    required = text_width + 58 + depth * indentation
                    widest = max(widest, required)
                    if tree.isExpanded(index) and depth < 24:
                        measure(index, depth + 1)

            measure(root)
            tree.setColumnWidth(0, int(widest))
            bar = tree.horizontalScrollBar()
            bar.setSingleStep(28)
            bar.setPageStep(max(80, tree.viewport().width() - 24))
            # Re-evaluate the breadcrumb's scroll range after the containing browser resized.
            breadcrumb = getattr(self, "home_browser_breadcrumb_scroll", None)
            if breadcrumb is not None and breadcrumb.isVisible():
                QTimer.singleShot(0, lambda area=breadcrumb: area.horizontalScrollBar().setPageStep(max(60, area.viewport().width() - 20)))
        except (RuntimeError, AttributeError, TypeError, ValueError):
            pass

    def _home_browser_update_breadcrumb(self):
        """Legacy compatibility hook; navigation is now shown in the path editor."""
        scroll = getattr(self, "home_browser_breadcrumb_scroll", None)
        if scroll is not None:
            scroll.hide()
        current = str(getattr(self, "_home_browser_breadcrumb_focus_dir", "") or getattr(self, "_home_browser_current_dir", "") or "")
        if hasattr(self, "home_browser_path"):
            if current and os.path.isdir(current):
                self.home_browser_path.setText(os.path.abspath(current))
            elif not getattr(self, "_home_browser_current_dir", ""):
                language = str(self.settings.value("interface_language", "en", type=str) or "en").lower()
                self.home_browser_path.setText("هذا الكمبيوتر" if language.startswith("ar") else "This PC")

    def _home_browser_branch_clicked(self, index):
        """Show the folder branch the user is currently navigating in the breadcrumb."""
        if getattr(self, "_home_browser_refreshing", False):
            return
        try:
            if index.isValid() and self.home_browser_model.isDir(index):
                self._home_browser_breadcrumb_focus_dir = self.home_browser_model.filePath(index)
                self.home_browser_path.setText(self._home_browser_breadcrumb_focus_dir)
        except (RuntimeError, TypeError, OSError):
            pass

    def _home_browser_branch_expanded(self, index):
        if getattr(self, "_home_browser_refreshing", False):
            return
        try:
            if index.isValid() and self.home_browser_model.isDir(index):
                self._home_browser_breadcrumb_focus_dir = self.home_browser_model.filePath(index)
                self.home_browser_path.setText(self._home_browser_breadcrumb_focus_dir)
        except (RuntimeError, TypeError, OSError):
            pass

    def _home_browser_branch_collapsed(self, index):
        if getattr(self, "_home_browser_refreshing", False):
            return
        try:
            if not index.isValid() or not self.home_browser_model.isDir(index):
                return
            collapsed_path = os.path.abspath(self.home_browser_model.filePath(index))
            focus = os.path.abspath(str(getattr(self, "_home_browser_breadcrumb_focus_dir", "") or collapsed_path))
            try:
                is_inside = os.path.commonpath([collapsed_path, focus]) == collapsed_path
            except ValueError:
                is_inside = False
            if is_inside:
                self._home_browser_breadcrumb_focus_dir = collapsed_path
                self.home_browser_path.setText(collapsed_path)
        except (RuntimeError, TypeError, OSError):
            pass

    def _home_browser_navigate_to(self, path):
        target = os.path.abspath(os.path.normpath(str(path or "")))
        if target and os.path.isdir(target):
            self._home_browser_current_dir = target
            self._home_browser_breadcrumb_focus_dir = target
            self._refresh_home_browser()

    def _home_browser_go(self):
        """Navigate to a typed path or return to the This PC drive list."""
        entered = self.home_browser_path.text().strip().strip('"').strip()
        entered = os.path.expandvars(os.path.expanduser(entered))
        if entered.casefold() in {"this pc", "هذا الكمبيوتر", "computer", "my computer"}:
            self._home_browser_current_dir = ""
            self._refresh_home_browser()
            self.home_browser_tree.setFocus()
            return
        folder = os.path.abspath(os.path.expanduser(entered)) if entered else ""
        if folder and os.path.isdir(folder):
            self._home_browser_current_dir = folder
            self._refresh_home_browser()
            self.home_browser_tree.setFocus()
        else:
            QMessageBox.information(self, "File browser", "The folder path does not exist.")

    def _home_browser_tree_activated(self, index):
        if not index.isValid() or index.column() != 0:
            return
        path = str(self.home_browser_model.filePath(index) or "")
        # Directories are expanded/collapsed by QTreeView itself. Only supported
        # documents are opened as tabs when the user double-clicks their names.
        if path and os.path.isfile(path) and is_supported_document(path):
            self.open_pdf(path)

    def _show_files_screen(self):
        if not hasattr(self, "document_host"):
            return
        if self._chat_focus_mode:
            self.toggle_chat_focus_mode(False, animate=False)
        # Save the user's previous workspace only on the first transition into Files.
        # Repeated clicks on Files must keep it as a full-workspace home screen.
        if not self._files_screen_active:
            self._files_previous_topbar_visible = bool(self.topbar.isVisible()) if hasattr(self, "topbar") else True
            self._files_previous_topbar_max_height = int(self.topbar.maximumHeight()) if hasattr(self, "topbar") else 16777215
            self._files_previous_workspace_sizes = list(self.workspace.sizes()) if hasattr(self, "workspace") else None
            self._files_previous_ai_visible = bool(getattr(self, "ai_panel", None) and self.ai_panel.isVisible())
            self._files_previous_board_visible = bool(getattr(self, "teach_board", None) and self.teach_board.isVisible())
            self._files_previous_ai_checked = bool(getattr(self, "ai_chat_btn", None) and self.ai_chat_btn.isChecked())
            self._files_screen_active = True

        self._refresh_files_home()
        self.setWindowTitle(f"{APP_NAME} · Home")
        # Home is a full-page destination: hide the whole row that contains the
        # brand, document tabs, New Tab and Link buttons. This prevents the tab
        # strip from remaining visible above the Home screen.
        if hasattr(self, "tab_strip"):
            self.tab_strip.hide()
        if hasattr(self, "topbar"):
            self.topbar.hide()
        # Home is a top-level workspace page, not a third panel beside a still-open chat.
        if hasattr(self, "ai_panel"):
            self.ai_panel.hide()
        if hasattr(self, "ai_chat_btn"):
            self.ai_chat_btn.setChecked(False)
        if hasattr(self, "teach_board"):
            self.teach_board.hide()
        if hasattr(self, "_pdf_search_dialog") and self._pdf_search_dialog is not None:
            try:
                self._pdf_search_dialog.hide()
            except RuntimeError:
                pass
        self.document_host.setCurrentWidget(self.welcome_page)
        self.return_to_docs_btn.setVisible(self.tabs.count() > 0)
        if hasattr(self, "workspace"):
            total = max(1, self.workspace.width())
            self.workspace.setSizes([total, 0, 0])
        self._update_controls()
        self._set_default_context_help(force=True)

    def _show_document_area(self):
        if hasattr(self, "document_host") and self.tabs.count() > 0:
            # Document tabs belong to the document workspace only. Reveal the
            # complete strip when returning from Home or activating a document.
            if hasattr(self, "tab_strip"):
                self.tab_strip.show()
            self.document_host.setCurrentWidget(self.tabs)
            if self._files_screen_active:
                self._files_screen_active = False
                self.setWindowTitle(APP_NAME)
                if hasattr(self, "topbar"):
                    self.topbar.setMaximumHeight(self._files_previous_topbar_max_height)
                    self.topbar.setVisible(self._files_previous_topbar_visible)
                if hasattr(self, "ai_panel"):
                    self.ai_panel.setVisible(self._files_previous_ai_visible)
                if hasattr(self, "ai_chat_btn"):
                    self.ai_chat_btn.setChecked(self._files_previous_ai_checked and self._files_previous_ai_visible)
                if hasattr(self, "teach_board"):
                    self.teach_board.setVisible(self._files_previous_board_visible)
                sizes = self._files_previous_workspace_sizes
                if sizes and len(sizes) >= 3:
                    total_saved = max(1, sum(max(0, int(v)) for v in sizes[:3]))
                    total_now = max(1, self.workspace.width())
                    restored = [max(0, round(total_now * max(0, int(v)) / total_saved)) for v in sizes[:3]]
                    self.workspace.setSizes(restored)
                else:
                    self.workspace.setSizes([self.workspace.width(), 0, 0])
                self._files_previous_workspace_sizes = None
            self._update_controls()
            # Returning from Home reveals the PDF toolbar without necessarily
            # resizing the main window. Re-measure it after Qt has restored the
            # topbar's actual width; otherwise the construction-time two-row
            # layout can remain until the user drags the window border.
            self._schedule_toolbar_density_update()
            QTimer.singleShot(110, self._apply_toolbar_density)
            QTimer.singleShot(280, self._apply_toolbar_density)
            self._set_default_context_help(force=True)

    def open_app_settings(self):
        original_theme = normalize_ui_theme(self.settings.value("ui_theme", "dark", type=str))
        dialog = AppSettingsDialog(
            self.settings, self,
            language=str(self.settings.value("interface_language", "en", type=str) or "en"),
        )
        result = dialog.exec()
        if getattr(dialog, "reset_requested", False):
            self._begin_reset_and_restart(dialog)
            return
        if result == QDialog.DialogCode.Accepted:
            for key, value in dialog.values().items():
                self.settings.setValue(key, value)
            self.settings.sync()
            selected_theme = normalize_ui_theme(self.settings.value("ui_theme", "dark", type=str))
            if selected_theme != original_theme:
                # The selected theme is committed only now, after Save changes.
                self._animate_theme_transition()
            else:
                self._apply_style()
                self._apply_user_interface_preferences()
            self._apply_interface_language()
            self.show_status("Application settings updated")

    def open_ai_provider_settings(self, parent_dialog=None):
        """Open provider/model credentials from the central application settings."""
        try:
            self.settings.sync()
        except Exception:
            pass
        dialog_parent = parent_dialog if isinstance(parent_dialog, QWidget) else self
        dlg = AISettingsDialog(self.settings, dialog_parent)
        if dlg.exec() == QDialog.DialogCode.Accepted:
            panel = getattr(self, "ai_panel", None)
            if panel is not None:
                try:
                    panel._provider_changed(panel.provider_combo.currentIndex())
                except (RuntimeError, AttributeError):
                    pass
            is_ar = str(self.settings.value("interface_language", "en", type=str) or "en").lower().startswith("ar")
            self.show_status("تم حفظ إعدادات مزوّدي الذكاء الاصطناعي" if is_ar else "AI provider settings saved")

    def close_ai_panel(self):
        """Close the chat panel, leaving full-screen chat first when necessary."""
        if self._chat_focus_mode:
            self.toggle_chat_focus_mode(False)
            QTimer.singleShot(760, lambda: self._animate_ai_panel(False) if self.ai_panel.isVisible() else None)
        else:
            self._animate_ai_panel(False)

    def _begin_reset_and_restart(self, reset_dialog):
        """Close every Engo window, clear the profile, and relaunch into first-run setup."""
        app = QApplication.instance()
        if app is None:
            return

        # Prevent Qt from quitting between closing the last window and completing
        # the reset/relaunch workflow. Close the settings-owning window first so
        # any unsaved-document prompt can cancel before other windows are touched.
        app.setQuitOnLastWindowClosed(False)
        windows = [w for w in list(MainWindow._open_windows)
                   if not getattr(w, "_closing_complete", False)]
        ordered = ([self] if self in windows else []) + [w for w in windows if w is not self]
        for window in ordered:
            window._reset_shutdown_requested = True

        for window in ordered:
            if not getattr(window, "_closing_complete", False):
                try:
                    window.close()
                except Exception:
                    pass

        self._continue_reset_shutdown(reset_dialog)

    def _continue_reset_shutdown(self, reset_dialog):
        """Wait for approved worker cancellation/close events, or abort on a veto."""
        app = QApplication.instance()
        if app is None:
            return
        live = [w for w in list(MainWindow._open_windows)
                if not getattr(w, "_closing_complete", False)]
        pending = [w for w in live if getattr(w, "_close_after_cancel", False)]
        blocked = [w for w in live if not getattr(w, "_close_after_cancel", False)]

        if pending:
            QTimer.singleShot(250, lambda d=reset_dialog: self._continue_reset_shutdown(d))
            return
        if blocked:
            for window in live:
                window._reset_shutdown_requested = False
            # If the original window closed before another detached window vetoed
            # closing, hand the single-instance listener to one remaining window.
            if not any(getattr(w, "_register_ipc", False) for w in live) and live:
                live[0]._register_ipc = True
                QTimer.singleShot(180, live[0]._setup_ipc_server)
            app.setQuitOnLastWindowClosed(True)
            is_ar = getattr(reset_dialog, "language", "en") == "ar"
            QMessageBox.information(
                live[0] if live else None,
                "إعادة ضبط Engo" if is_ar else "Reset Engo",
                "تم إلغاء إعادة الضبط لأن إحدى نوافذ Engo ما زالت مفتوحة. أغلقها ثم حاول مرة أخرى."
                if is_ar else
                "Reset was cancelled because an Engo window is still open. Close it and try again."
            )
            return

        # All windows have closed. Preserve user content by only clearing QSettings
        # and disposable caches; chat and lesson-board databases remain untouched.
        failed_credentials = []
        cache_errors = 0
        try:
            _removed, failed_credentials = reset_dialog._delete_provider_credentials()
            cache_stats = reset_dialog._perform_cache_cleanup(None)
            cache_errors = int(cache_stats.get("errors", 0))
            self.settings.clear()
            self.settings.sync()
            if self.settings.allKeys():
                raise RuntimeError("Some Engo preferences could not be cleared.")
        except Exception as exc:
            app.setQuitOnLastWindowClosed(True)
            is_ar = getattr(reset_dialog, "language", "en") == "ar"
            message = (f"تعذرت إعادة ضبط Engo بالكامل: {exc}" if is_ar
                       else f"Could not complete the reset: {exc}")
            QMessageBox.critical(None, "إعادة ضبط Engo" if is_ar else "Reset Engo", message)
            return

        # Launch without the old command-line document paths. A fresh process sees
        # an empty QSettings profile and displays the welcome language/theme wizard.
        is_compiled_app = bool(getattr(sys, "frozen", False) or globals().get("__compiled__"))
        if is_compiled_app:
            # Nuitka standalone builds may expose __compiled__ instead of the
            # PyInstaller-style sys.frozen flag. In either case, relaunch the EXE
            # itself without passing its path as an extra document argument.
            executable = sys.executable
            arguments = []
            working_directory = str(Path(sys.executable).resolve().parent)
        else:
            executable = sys.executable
            script_path = str(Path(sys.argv[0]).resolve())
            arguments = [script_path]
            working_directory = str(Path(script_path).parent)

        try:
            launch_result = QProcess.startDetached(executable, arguments, working_directory)
            started = bool(launch_result[0]) if isinstance(launch_result, tuple) else bool(launch_result)
        except Exception:
            started = False

        if not started:
            is_ar = getattr(reset_dialog, "language", "en") == "ar"
            details = ("تمت إعادة ضبط إعدادات Engo، لكن تعذرت إعادة التشغيل تلقائيًا. شغّل Engo يدويًا لعرض شاشات الترحيب."
                       if is_ar else
                       "Engo settings were reset, but automatic restart failed. Start Engo manually to see the welcome setup.")
            if failed_credentials:
                details += "\nتعذر التأكد من حذف بعض مفاتيح API." if is_ar else "\nSome API credentials could not be confirmed as deleted."
            if cache_errors:
                details += f"\nتعذر حذف {cache_errors} عنصر كاش." if is_ar else f"\n{cache_errors} cache item(s) could not be removed."
            QMessageBox.warning(None, "إعادة ضبط Engo" if is_ar else "Reset Engo", details)
            app.quit()
            return

        # No completion popup is needed: the relaunched application opens the
        # welcome screens immediately after the old process exits.
        app.quit()

    def _animate_theme_transition(self):
        """Cross-fade cached old-window snapshots over the newly themed UI.

        All expensive stylesheet/palette work is completed before animation starts.
        The transition itself only animates opacity effects on static pixmaps, so
        Qt does not have to repolish and relayout the application halfway through.
        """
        previous = getattr(self, "_theme_transition_animation", None)
        if previous is not None:
            try:
                previous.stop()
            except RuntimeError:
                pass
            try:
                previous.deleteLater()
            except RuntimeError:
                pass
            self._theme_transition_animation = None

        # Remove any snapshot left by an interrupted transition before capturing
        # the current, already-updated interface for a new transition.
        for _window, overlay, _effect in getattr(self, "_theme_transition_overlays", []):
            try:
                overlay.hide()
                overlay.deleteLater()
            except RuntimeError:
                pass
        self._theme_transition_overlays = []
        self._theme_transition_restore = []

        app = QApplication.instance()
        all_engo_windows = [
            window for window in list(MainWindow._open_windows)
            if not getattr(window, "_closing_complete", False)
        ]
        visible_windows = []
        if app is not None:
            for window in app.topLevelWidgets():
                try:
                    belongs_to_engo = any(
                        (window is host) or host.isAncestorOf(window)
                        for host in all_engo_windows
                    )
                    if belongs_to_engo and window.isVisible() and window.width() > 1 and window.height() > 1:
                        visible_windows.append(window)
                except RuntimeError:
                    continue

        # Capture what the user currently sees. These labels sit above the live
        # widgets while the theme is applied underneath them.
        snapshots = []
        for window in visible_windows:
            try:
                pixmap = window.grab()
                if pixmap.isNull():
                    continue
                overlay = QLabel(window)
                overlay.setObjectName("engoThemeTransitionSnapshot")
                overlay.setPixmap(pixmap)
                overlay.setScaledContents(False)
                overlay.setAlignment(Qt.AlignmentFlag.AlignLeft | Qt.AlignmentFlag.AlignTop)
                overlay.setAttribute(Qt.WidgetAttribute.WA_TransparentForMouseEvents, True)
                overlay.setAttribute(Qt.WidgetAttribute.WA_NoSystemBackground, True)
                overlay.setStyleSheet("background: transparent; border: 0; padding: 0; margin: 0;")
                overlay.setGeometry(window.rect())
                effect = QGraphicsOpacityEffect(overlay)
                effect.setOpacity(1.0)
                overlay.setGraphicsEffect(effect)
                overlay.show()
                overlay.raise_()
                snapshots.append((window, overlay, effect))
            except (RuntimeError, AttributeError):
                continue

        # Apply the new theme once, with no animation callback running. This is
        # the expensive part that previously happened at 50% of the old fade and
        # caused the visible pause/stutter reported by the user.
        for host in all_engo_windows:
            try:
                host.settings.sync()
                host._apply_style()
                host._apply_user_interface_preferences()
                host._apply_interface_language()
            except (RuntimeError, AttributeError):
                continue

        if not snapshots:
            self._theme_transition_animation = None
            return

        # Refit and raise overlays after any stylesheet-driven layout/palette work.
        active_snapshots = []
        for window, overlay, effect in snapshots:
            try:
                if not window.isVisible():
                    overlay.deleteLater()
                    continue
                overlay.setGeometry(window.rect())
                overlay.raise_()
                active_snapshots.append((window, overlay, effect))
            except RuntimeError:
                try:
                    overlay.deleteLater()
                except RuntimeError:
                    pass
        self._theme_transition_overlays = active_snapshots

        if not active_snapshots:
            self._theme_transition_animation = None
            self._theme_transition_overlays = []
            return

        animation_group = QParallelAnimationGroup(self)
        for _window, _overlay, effect in active_snapshots:
            animation = QPropertyAnimation(effect, b"opacity", animation_group)
            animation.setDuration(320)
            animation.setStartValue(1.0)
            animation.setEndValue(0.0)
            animation.setEasingCurve(QEasingCurve.Type.OutCubic)
            animation_group.addAnimation(animation)

        def finish_transition():
            for _window, overlay, _effect in list(self._theme_transition_overlays):
                try:
                    overlay.hide()
                    overlay.deleteLater()
                except RuntimeError:
                    pass
            self._theme_transition_overlays = []
            self._theme_transition_restore = []
            self._theme_transition_animation = None
            try:
                animation_group.deleteLater()
            except RuntimeError:
                pass

        animation_group.finished.connect(finish_transition)
        self._theme_transition_animation = animation_group

        # Let Qt finish relayout and paint the new theme under the old snapshots
        # before starting the cross-fade. Native property animations avoid a Python
        # per-frame loop and keep the transition smooth across multiple windows.
        QTimer.singleShot(0, animation_group.start)

    def _apply_popup_menu_style(self, menu: QMenu, theme: str | None = None):
        """Apply the shared Engo popup palette to toolbar and context menus."""
        if menu is None:
            return
        if theme is None:
            try:
                self.settings.sync()
            except Exception:
                pass
            theme = self.settings.value("ui_theme", "dark", type=str)
        _engo_apply_menu_consistency(
            menu,
            theme,
            str(self.settings.value("interface_language", "en", type=str) or "en").lower().startswith("ar"),
        )

    def _apply_user_interface_preferences(self):
        scale_text = str(self.settings.value("ui_scale", "1.00", type=str) or "1.00")
        try:
            scale = max(0.85, min(1.6, float(scale_text)))
        except Exception:
            scale = 1.0
        theme = normalize_ui_theme(self.settings.value("ui_theme", "dark", type=str))
        check_icon_path = resource_path("checkbox_checked.png").replace("\\", "/")
        combo_chevron_asset = "combo_chevron_light.png" if theme == "light" else "combo_chevron_dark.png"
        combo_chevron_path = resource_path(combo_chevron_asset).replace("\\", "/")
        combo_chevron_up_asset = "combo_chevron_up_light.png" if theme == "light" else "combo_chevron_up_dark.png"
        combo_chevron_up_path = resource_path(combo_chevron_up_asset).replace("\\", "/")
        theme = normalize_ui_theme(theme)
        # Always start from the immutable base stylesheet. Recoloring the previously
        # recolored stylesheet caused Light/Dark/Midnight switches to accumulate.
        stylesheet = getattr(self, "_base_app_stylesheet", self.styleSheet())

        # Neutral Dark = black/graphite. Midnight = unmistakably navy/blue.
        # Legacy QSS still contains old hard-coded colors, but current semantic
        # token colors must pass through unchanged. Otherwise the generic hue
        # converter would turn the new accent (and other named colors) into gray.
        protected_theme_colors = {
            str(color).lower() for color in engo_ui_theme_tokens(theme).values()
        }
        dark_overrides = {
            # Convert the previous blue-gray surfaces to a restrained graphite ramp.
            "#151820": "#171717", "#1d222c": "#202020", "#252c38": "#262626",
            "#333c4a": "#383838", "#171b23": "#1b1b1b", "#171c25": "#1c1c1c",
            "#202630": "#242424", "#202a39": "#292929", "#151a22": "#161616",
            "#141820": "#171717", "#1b202a": "#1d1d1d", "#1b2029": "#1d1d1d",
            "#111722": "#151515", "#222731": "#222222", "#191f29": "#202020",
            "#2b3440": "#303030", "#242b37": "#242424", "#2b4164": "#3b4148",
            "#303b4c": "#303030", "#3a4960": "#383838", "#202938": "#242424",
        }
        midnight_overrides = {
            "#151820": "#091321", "#1d222c": "#111e33", "#252c38": "#1b2a43",
            "#333c4a": "#2b3e5e", "#171b23": "#0e1728", "#171c25": "#101a2d",
            "#202630": "#14223a", "#202a39": "#1b2c49", "#151a22": "#0c1525",
            "#141820": "#0a1220", "#1b202a": "#121d30", "#1b2029": "#121d30",
            "#111722": "#091321", "#222731": "#18263f", "#191f29": "#142039",
        }
        grass_overrides = {
            "#151820": "#101b13", "#1d222c": "#18251b", "#252c38": "#223228",
            "#333c4a": "#354b3b", "#171b23": "#121e15", "#171c25": "#152218",
            "#202630": "#1e2d20", "#202a39": "#25372a", "#151a22": "#101a13",
            "#141820": "#101910", "#1b202a": "#1c2a20", "#1b2029": "#1b291f",
            "#111722": "#101a13", "#222731": "#203024", "#191f29": "#17251b",
        }
        pink_overrides = {
            "#151820": "#1b1118", "#1d222c": "#281924", "#252c38": "#34212e",
            "#333c4a": "#54374a", "#171b23": "#1c1219", "#171c25": "#211620",
            "#202630": "#2a1c26", "#202a39": "#382434", "#151a22": "#1b1118",
            "#141820": "#1a1118", "#1b202a": "#261923", "#1b2029": "#261923",
            "#111722": "#1b1118", "#222731": "#30202b", "#191f29": "#241720",
        }
        orange_overrides = {
            "#151820": "#1d160f", "#1d222c": "#281d14", "#252c38": "#352519",
            "#333c4a": "#59412c", "#171b23": "#21180f", "#171c25": "#241a11",
            "#202630": "#302318", "#202a39": "#3a291a", "#151a22": "#19130e",
            "#141820": "#1b140e", "#1b202a": "#2b1e13", "#1b2029": "#2b1e13",
            "#111722": "#1d160f", "#222731": "#352519", "#191f29": "#281d14",
        }

        def recolor(match):
            original = match.group(0).lower()
            if original in protected_theme_colors:
                return original
            if theme == "dark" and original in dark_overrides:
                return dark_overrides[original]
            if theme == "midnight" and original in midnight_overrides:
                return midnight_overrides[original]
            if theme == "grass" and original in grass_overrides:
                return grass_overrides[original]
            if theme == "pink" and original in pink_overrides:
                return pink_overrides[original]
            if theme == "orange" and original in orange_overrides:
                return orange_overrides[original]
            if theme == "light":
                light_palette = {
                    "#151820": "#f3f5f9", "#1d222c": "#ffffff", "#252c38": "#e9eef5",
                    "#333c4a": "#d1d9e5", "#e9edf5": "#1d2735", "#9aa6b8": "#687588",
                    "#171b23": "#e7ebf2", "#171c25": "#f5f7fb", "#202630": "#ffffff",
                    "#202a39": "#eaf0f8", "#303b4c": "#e0e7f1", "#2b3546": "#dbe6f7",
                    "#2b3442": "#e6edf7", "#aab5c7": "#59677b", "#eef2f9": "#202b3b",
                    "#edf2fb": "#202b3b", "#edf2fc": "#202b3b", "#f2f5fb": "#202b3b",
                    "#f3f6fc": "#202b3b", "#dce6f7": "#2b3a50", "#e2e9f5": "#273346",
                    "#151a22": "#ffffff", "#252e3a": "#edf1f7", "#2a323e": "#e5ebf4",
                }
                return light_palette.get(original, original)
            try:
                r = int(original[1:3], 16) / 255.0
                g = int(original[3:5], 16) / 255.0
                b = int(original[5:7], 16) / 255.0
                h, lightness, saturation = colorsys.rgb_to_hls(r, g, b)
                hue_deg = h * 360.0
                if theme == "dark":
                    # Desaturate blue/slate cast into neutral graphite while keeping
                    # semantic red/green/gold states and contrast levels intact.
                    if 185.0 <= hue_deg <= 270.0 and saturation > 0.08:
                        saturation *= 0.045
                elif theme == "midnight":
                    # Tint neutral and existing blue-gray low/mid tones toward navy.
                    is_blue_family = 185.0 <= hue_deg <= 275.0
                    is_dark_neutral = saturation < 0.20 and lightness < 0.62
                    if lightness < 0.60 and (is_blue_family or is_dark_neutral):
                        h = 220.0 / 360.0
                        saturation = max(0.24, min(0.52, saturation * 1.45 + 0.08))
                elif theme in ("grass", "pink", "orange"):
                    # Give legacy blue/slate surfaces a coherent green, rose, or
                    # orange family. Keep semantic colors and bright text intact.
                    is_blue_family = 185.0 <= hue_deg <= 275.0
                    is_dark_neutral = saturation < 0.20 and lightness < 0.66
                    target_hue = {"grass": 145.0, "pink": 333.0, "orange": 28.0}[theme]
                    if is_blue_family:
                        h = target_hue / 360.0
                        saturation = max(0.32, min(0.78, saturation * 0.88 + 0.10))
                    elif is_dark_neutral and lightness < 0.62:
                        h = target_hue / 360.0
                        saturation = max(0.12, min(0.30, saturation * 0.55 + 0.12))
                rr, gg, bb = colorsys.hls_to_rgb(h, lightness, saturation)
                return "#{:02x}{:02x}{:02x}".format(round(rr * 255), round(gg * 255), round(bb * 255))
            except Exception:
                return original

        stylesheet = re.sub(r"#[0-9a-fA-F]{6}", recolor, stylesheet)
        if abs(scale - 1.0) > 0.005:
            def scale_font(match):
                try:
                    return f"{match.group(1)}{float(match.group(2))*scale:.2f}pt"
                except Exception:
                    return match.group(0)
            stylesheet = re.sub(r"(font-size:\s*)([0-9]+(?:\.[0-9]+)?)pt", scale_font, stylesheet)
        if theme == "light":
            # The original app was designed dark-first. Apply a deliberate light palette
            # to every major surface and text editor instead of only swapping a few hexes.
            stylesheet += r"""
            QWidget { color: #253246; }
            QMainWindow, QWidget#mainRoot { background: #eef2f7; }
            QFrame#tabStrip, QFrame#topbar { background: #e5eaf1; border-color: #c8d1de; }
            QFrame#toolbarGroup, QFrame#annotationGroup { background: #f7f9fc; border-color: #cbd4e0; }
            QFrame#vline { color: #c5ceda; }
            QFrame#documentSidebar { background:#e9eef5; border-right:1px solid #cbd4e0; }
            QStackedWidget#documentStack, QScrollArea#readerScroll { background:#e3e8ef; border:0; }
            QLabel#sideHeader { color:#65758b; }
            QWidget#sideTabs, QWidget#sidebarTabNav, QStackedWidget#sidebarTabStack { background:transparent; border:0; }
            QPushButton#sideTabButton { background:#e5ebf3; color:#53647b; border:1px solid #c8d2df; border-radius:7px; padding:6px 8px; font-size:8pt; font-weight:700; }
            QPushButton#sideTabButton:checked { background:#ffffff; color:#26364c; border-color:#8ba9dc; }
            QPushButton#sideTabButton:hover { background:#f7f9fc; color:#26364c; }
            QListWidget#thumbnails, QTreeWidget#outline { background:#f8fafc; color:#26364c; border:0; }
            QListWidget#thumbnails::item:selected, QTreeWidget#outline::item:selected { background:#dce9ff; color:#204c91; border-color:#9cb9e8; }
            QListWidget#thumbnails::item:hover { background:#e9eff7; }
            QSpinBox#pageSpin { background:#ffffff; color:#24344b; border:1px solid #c6d0de; }
            QStatusBar#appStatus { background:#e9eef5; color:#65758b; border-top:1px solid #cbd4e0; }
            QLabel#contextHelpIcon { color:#3269d8; font-size:9pt; font-weight:850; padding:0 5px 0 8px; }
            QLabel#contextHelpLabel { color:#596b83; font-size:8pt; font-weight:600; padding:2px 8px 2px 2px; }
            QLabel#brandTitle, QLabel#zoomLabel { color: #1f2d42; }
            QTabBar#documentTabBar::tab { background: #e6ebf2; color: #526176; border-color: #c7d0dd; }
            QTabBar#documentTabBar::tab:selected { background: #ffffff; color: #1d2b40; border-color: #8ba9dc; }
            QTabBar#documentTabBar::tab:hover { background: #f7f9fc; color: #1d2b40; }
            QPushButton, QToolButton { background: #f8fafc; color: #263449; border-color: #c6d0de; }
            QPushButton:hover, QToolButton:hover { background: #e8eef7; border-color: #9eb4d3; }
            QPushButton:pressed, QToolButton:pressed { background: #dbe5f2; }
            QPushButton:disabled, QToolButton:disabled { background: #edf0f4; color: #9aa5b3; border-color: #d9dfe7; }
            QPushButton#primary, QPushButton#aiSend, QPushButton#filesPrimaryButton { background: #3269d8; color: #ffffff; border-color: #2459c2; }
            QPushButton#primary:hover, QPushButton#aiSend:hover, QPushButton#filesPrimaryButton:hover { background: #245bc7; color: #ffffff; }
            /* Home's secondary action must never inherit its dark-theme hover colors. */
            QPushButton#filesSecondaryButton { color:#26364d; background:#f7f9fc; border:1px solid #c6d0de; border-radius:7px; padding:4px 9px; min-height:25px; }
            QPushButton#filesSecondaryButton:hover:enabled { color:#1d3d70; background:#e5edf8; border-color:#91acd0; }
            QPushButton#filesSecondaryButton:pressed:enabled { color:#17345e; background:#d7e3f3; border-color:#7f9fc9; }
            QPushButton#filesSecondaryButton:disabled { color:#929eae; background:#edf0f4; border-color:#d9dfe7; }
            QPushButton#action, QPushButton#tool, QPushButton#mode, QPushButton#compact { color: #34445b; }
            QPushButton#tool:checked, QPushButton#mode:checked { background: #dce9ff; color: #173f83; border-color: #6d99e6; }
            QToolButton#tagTool:checked { background:#dce9ff; color:#173f83; border-color:#6d99e6; border-bottom:3px solid #6d99e6; }
            QToolButton#selectTool { background:#f8fafc; color:#34445b; border:1px solid #c6d0de; border-radius:7px; padding:2px; }
            QToolButton#selectTool:hover { background:#eef3fa; color:#34445b; border-color:#a9bad0; }
            QToolButton#selectTool:checked { background:#dce9ff; color:#173f83; border-color:#6d99e6; border-bottom:3px solid #6d99e6; }
            QToolButton#selectTool:checked:hover { background:#dce9ff; color:#173f83; border-color:#6d99e6; }
            QPushButton#tool:hover, QPushButton#action:hover, QPushButton#history:hover,
            QToolButton#tagTool:hover, QToolButton#rotatePageAction:hover { color:#34445b; }
            QToolButton#selectTool::menu-button { width:12px; border-left:1px solid #c6d0de; }
            QPushButton#toolbarPinButton, QPushButton#tabAdd, QPushButton#history { background:#f7f9fc; color:#33445b; border-color:#c6d0de; }
            QPushButton#toolbarPinButton:checked { background:#e2efe9; border-color:#9bc7b4; }
            QPushButton#deleteTool { background:#f7f9fc; color:#ef4444; border-color:#c6d0de; }
            QPushButton#deleteTool:hover:enabled { background:#e8eef7; border-color:#9eb4d3; }
            QPushButton#deleteTool:disabled { background:#edf0f4; border-color:#d9dfe7; }
            QLineEdit, QTextEdit, QPlainTextEdit, QTextBrowser, QComboBox, QSpinBox, QDoubleSpinBox {
                background: #ffffff; color: #202c3e; border-color: #c7d1df; selection-background-color: #a9c6f5; selection-color: #10213a;
            }
            QComboBox QAbstractItemView { background:#ffffff; color:#263449; border:1px solid #c6d0de; outline:0; padding:4px; selection-background-color:#e3edfc; selection-color:#173f83; }
            QComboBox#aiChatSelector {
                background:#ffffff; color:#263449; border:1px solid #c6d0de; border-radius:7px;
                padding:5px 28px 5px 9px; min-height:29px;
            }
            QComboBox#aiChatSelector:hover {
                background:#f8fbff; color:#263449; border-color:#9eb4d3;
            }
            QComboBox#aiChatSelector::drop-down {
                subcontrol-origin:padding; subcontrol-position:top right; width:24px;
                background:#f4f7fb; border-left:1px solid #d5deea;
                border-top-right-radius:7px; border-bottom-right-radius:7px;
            }
            QComboBox#aiChatSelector::down-arrow,
            QComboBox#aiProviderSelector::down-arrow,
            QComboBox#aiModelSelector::down-arrow {
                image:url("{combo_chevron_path}"); width:12px; height:8px; border:0;
            }
            QComboBox#aiProviderSelector::down-arrow,
            QComboBox#aiModelSelector::down-arrow {
                image:url("{combo_chevron_up_path}"); width:12px; height:8px; border:0;
            }
            QComboBox#aiChatSelector QAbstractItemView {
                background:#ffffff; color:#263449; border:1px solid #c6d0de; outline:0;
                padding:4px; selection-background-color:#e3edfc; selection-color:#173f83;
            }
            QComboBox#aiChatSelector QAbstractItemView::item {
                background:#ffffff; color:#263449; min-height:25px; padding:6px 9px; border-radius:4px;
            }
            QComboBox#aiChatSelector QAbstractItemView::item:hover,
            QComboBox#aiChatSelector QAbstractItemView::item:selected {
                background:#e3edfc; color:#173f83;
            }
            QPushButton#aiNewChat {
                background:#edf3fb; color:#28528d; border:1px solid #c4d2e5;
                border-radius:7px; padding:5px 8px;
            }
            QPushButton#aiNewChat:hover { background:#e1ebf8; border-color:#a7bddb; }
            QComboBox#aiProviderSelector, QComboBox#aiModelSelector {
                background:#ffffff; color:#263449; border:1px solid #c6d0de; border-radius:7px;
                padding:4px 28px 4px 7px; min-height:28px;
            }
            QComboBox#aiProviderSelector:hover, QComboBox#aiModelSelector:hover {
                background:#f8fbff; color:#263449; border-color:#9eb4d3;
            }
            QComboBox#aiProviderSelector::drop-down, QComboBox#aiModelSelector::drop-down {
                subcontrol-origin:padding; subcontrol-position:top right; width:22px;
                border-left:1px solid #d5deea; border-top-right-radius:7px; border-bottom-right-radius:7px;
            }
            QComboBox#aiProviderSelector QLineEdit, QComboBox#aiModelSelector QLineEdit {
                background:transparent; color:#263449; border:0; selection-background-color:#c8dcfb; selection-color:#173f83;
            }
            QComboBox#aiProviderSelector QAbstractItemView, QComboBox#aiModelSelector QAbstractItemView {
                background:#ffffff; color:#263449; border:1px solid #c6d0de; outline:0; padding:4px;
                selection-background-color:#e3edfc; selection-color:#173f83;
            }
            QComboBox#aiProviderSelector QAbstractItemView::item, QComboBox#aiModelSelector QAbstractItemView::item {
                background:#ffffff; color:#263449; min-height:25px; padding:6px 9px; border-radius:4px;
            }
            QComboBox#aiProviderSelector QAbstractItemView::item:hover,
            QComboBox#aiProviderSelector QAbstractItemView::item:selected,
            QComboBox#aiModelSelector QAbstractItemView::item:hover,
            QComboBox#aiModelSelector QAbstractItemView::item:selected {
                background:#e3edfc; color:#173f83;
            }
            QScrollBar:vertical, QScrollBar:horizontal { background: #edf1f6; }
            QScrollBar::handle:vertical, QScrollBar::handle:horizontal { background: #c0cad8; }
            QFrame#aiPanel { background: #f0f3f8; color: #202c3e; border-left: 1px solid #d1d9e4; }
            QFrame#aiComposer { background:#f7f9fc; border:1px solid #d1dbe7; }
            QFrame#aiPendingCard { background:#eef3f9; border-color:#d0d9e5; }
            QLabel#aiPendingLabel { color:#53647b; }
            QLabel#aiPendingPreview { background:#ffffff; border-color:#d0d9e5; }
            QPushButton#aiPendingRemove { background:#f3e9ec; color:#884552; border-color:#ddc5cb; }
            QScrollArea#aiTranscript, QWidget#aiTranscriptBody { background: #e9eef5; border-color: #cbd4e0; }
            QFrame#aiAssistantCard { background: #ffffff; border: 1px solid #d4dce7; }
            QFrame#aiUserCard { background: #e8f0ff; border: 1px solid #bfd1f0; }
            QLabel#aiTitle { color: #1d2b40; }
            QLabel#aiMuted, QLabel#aiBusyLabel, QLabel#aiModelLabel, QLabel#aiSectionTitle { color: #65758c; }
            QLabel#aiContextLabel { color: #33445c; background: #e6edf7; border-color: #c9d6e7; }
            QLabel#aiPendingSelectedTitle { color: #315d9d; }
            QLabel#aiPendingSelectedPreview { color: #33445c; }
            QLabel#aiPendingQuoteMark, QLabel#aiBubbleRole { color: #315d9d; }
            QLabel#aiBubbleTime { color: #718096; }
            QTextBrowser#aiBubbleContent { color: #202c3e; background: transparent; }
            QTextEdit#aiPrompt { background: #ffffff; color: #202c3e; border: 1px solid #c6d0de; selection-background-color: #b7cdf2; }
            QTextEdit#aiPrompt:focus { border-color: #6f96dc; }
            QPushButton#aiAddImage, QPushButton#aiQuickAction, QPushButton#aiNewChat,
            QPushButton#aiPdfActions, QPushButton#aiFocusMode, QPushButton#aiRegionButton,
            QPushButton#aiClearAttachments, QPushButton#translationQuiet { background: #f8fafc; color: #2d3c52; border-color: #c8d2df; }
            QPushButton#aiPdfActions, QPushButton#aiExport, QPushButton#aiFocusMode,
            QPushButton#aiClosePanel, QPushButton#aiChatSearch {
                background:#f7f9fc; color:#2c3e58; border:1px solid #bdcada;
                border-radius:7px; font-weight:650;
            }
            QPushButton#aiPdfActions:hover, QPushButton#aiExport:hover, QPushButton#aiFocusMode:hover,
            QPushButton#aiClosePanel:hover, QPushButton#aiChatSearch:hover {
                background:#e8eff9; color:#203957; border-color:#8fa9ce;
            }
            QPushButton#aiClosePanel { font-size:20pt; font-weight:900; padding:0px; }
            QPushButton#aiPdfActions:pressed, QPushButton#aiExport:pressed, QPushButton#aiFocusMode:pressed,
            QPushButton#aiClosePanel:pressed, QPushButton#aiChatSearch:pressed {
                background:#dbe7f6; border-color:#7d9bc6;
            }
            QPushButton#aiSelectRegion { background: #e7effd; color: #244c89; border-color: #a9c0e5; }
            QCheckBox { color:#34445b; spacing:7px; }
            QCheckBox::indicator {
                width:15px; height:15px; background:#ffffff;
                border:1px solid #aebdd0; border-radius:4px;
            }
            QCheckBox::indicator:hover { background:#f5f8fd; border-color:#789bc8; }
            QCheckBox::indicator:unchecked { background:#ffffff; border:1px solid #aebdd0; }
            QCheckBox::indicator:checked {
                background:{UI_ACCENT}; border:1px solid #4776d2; border-radius:4px;
                image:url("{check_icon_path}");
            }
            QCheckBox::indicator:disabled { background:#edf1f6; border-color:#d5dce6; }
            QPushButton#aiSend:disabled {
                background:#e7edf5; color:#8291a6; border:1px solid #cbd5e2;
            }
            QPushButton#aiSend:disabled:hover {
                background:#e7edf5; color:#8291a6; border-color:#cbd5e2;
            }
            QPushButton#aiVoice, QPushButton#aiReadAnswer { background:#e7edf7; color:#2b466f; border-color:#bdcbe0; }
            QPushButton#aiVoice:hover, QPushButton#aiReadAnswer:hover { background:#dce7f7; border-color:#99b2d8; }
            QPushButton#aiVoice[recording="true"] { background:#3269d8; color:#ffffff; border-color:#2459c2; }
            QPushButton#aiVoice[transcribing="true"] { background:#e5eaf1; color:#66758a; border-color:#c7d0dd; }
            QPushButton#aiStopAudio { background:#e7edf7; color:#2b466f; border-color:#bdcbe0; }
            QPushButton#aiStopAudio:hover { background:#dce7f7; border-color:#99b2d8; }
            QFrame#aiPendingSelectedText { background: #edf4ff; border-color: #c8d9f2; }
            QFrame#aiSettingsGroup, QFrame#translationCard { background: #f7f9fc; border-color: #d0d9e5; }
            QFrame#translationSource { background: #eef2f7; border-color: #d2dbe7; }
            QLabel#translationTitle, QLabel#dialogHeading { color: #1d2b40; }
            QLabel#translationMuted, QLabel#dialogHint { color: #66758a; }
            QLabel#dialogLabel { color: #34445b; }
            QTextBrowser#translationResult { background: #ffffff; color: #202c3e; border-color: #cbd4e0; }
            QFrame#teachBoard { background: #f2f5f9; border-left-color: #cbd4e0; }
            QLabel#teachBoardTitle { color: #315d9d; }
            QLabel#teachBoardLesson { color: #202c3e; }
            QLabel#teachBoardSpoken, QLabel#teachBoardFooter { color: #5f6f84; }
            QTextBrowser#teachBoardText { background: #ffffff; color: #202c3e; border-color: #cbd4e0; }
            QFrame#homeSidebar { background: #e8edf4; border-right-color: #cbd4e0; }
            QLabel#homeSideTitle { color: #1d2b40; font-size: 13pt; font-weight: 850; padding: 2px 8px 5px 8px; }
            QLabel#homeSideCaption { color: #68788e; font-size: 7.5pt; font-weight: 800; }
            QLabel#homeSideFooter { color: #68788e; font-weight: 600; }
            QPushButton#homeNav, QPushButton#homeNavActive { font-size: 9pt; font-weight: 700; }
            QPushButton#homeNav, QPushButton#homeSettingsNav { color: #40516a; }
            QPushButton#homeNav:hover, QPushButton#homeSettingsNav:hover { background: #dce5f1; color: #1f2d42; }
            QPushButton#homeSettingsNav { font-size: 10.5pt; font-weight: 800; min-height: 36px; padding: 6px 10px; border-radius: 7px; }
            QPushButton#homeNav { font-size: 9pt; font-weight: 750; min-height: 36px; padding: 6px 10px; border-radius: 7px; }
            QPushButton#aiVoice, QPushButton#aiReadAnswer, QPushButton#aiStopAudio { font-weight: 700; padding: 7px 12px; }
            QPushButton#homeNavActive { background: #d8e6fb; color: #1e4e94; border-color: #9db9e7; }
            QWidget#filesHome { background: #f1f4f8; }
            QLabel#filesHomeTitle, QLabel#filesHeroTitle, QLabel#filesSectionTitle { color: #1d2b40; font-weight: 800; }
            QLabel#filesHomeTitle { font-size: 23pt; }
            QLabel#filesHeroTitle { font-size: 19pt; }
            QLabel#filesHomeSubtitle { color: #53647b; font-weight: 650; }
            QLabel#filesHeroHint, QLabel#filesSectionHint, QLabel#filesEmptyHint { color: #607087; font-weight: 600; }
            QLabel#filesSectionTitle { font-size: 13pt; }
            QFrame#filesHero, QFrame#recentFileRow { background: #ffffff; border-color: #ccd5e1; }
            QFrame#homeFileBrowser { background: #ffffff; border: 1px solid #ccd5e1; border-radius: 10px; }
            QLineEdit#homeBrowserPath { color: #202c3e; font-size: 9pt; font-weight: 700; }
            QTreeView#homeBrowserTree { background: #f8fafc; color: #202c3e; border: 1px solid #d1d9e5; border-radius: 7px; padding: 4px; outline: 0; font-size: 8.5pt; font-weight: 650; }
            QTreeView#homeBrowserTree::item { padding: 5px 5px; border-radius: 4px; font-weight: 650; }
            QTreeView#homeBrowserTree::item:selected { background: #dce8fa; color: #173b70; }
            QTreeView#homeBrowserTree::item:hover:!selected { background: #edf2f9; color: #263449; }
            QLabel#filesSessionSummary { color: #334a68; background: #eaf0f8; border-color: #cad7e8; font-weight: 700; }
            QLabel#filesDropHint { color: #46628c; background: #e8eef6; border-color: #aebed2; font-weight: 800; }
            QLabel#recentPdfIcon { color: #315d9d; background: #e3ecfa; }
            QLabel#recentFileName { color: #26364c; font-weight: 800; }
            QLabel#recentFilePath, QLabel#recentFileWhen { color: #6e7e93; font-weight: 600; }
            QPushButton#filesPrimaryButton, QPushButton#filesSecondaryButton { font-size: 9pt; font-weight: 750; }
            QPushButton#filesSecondaryButton { color: #33445c; background: #f7f9fc; border-color: #c6d0de; }
            QToolButton#saveSplitButton, QToolButton#rotatePageAction { background: #f8fafc; color: #33445c; border-color: #c7d1df; }
            QToolButton#chatSelectionAsk { background: #3269d8; color: #ffffff; border-color: #2459c2; }
            /* Keep light-theme toolbar hover surfaces light so dark icons stay legible. */
            QFrame#topbar QPushButton#tool:!checked:hover,
            QFrame#topbar QToolButton#selectTool:!checked:hover,
            QFrame#topbar QToolButton#tagTool:!checked:hover,
            QFrame#topbar QPushButton#action:hover,
            QFrame#topbar QPushButton#compact:hover,
            QFrame#topbar QPushButton#history:hover,
            QFrame#topbar QPushButton#tabAdd:hover,
            QFrame#topbar QPushButton#toolbarPinButton:hover,
            QFrame#topbar QToolButton#saveSplitButton:hover,
            QFrame#topbar QToolButton#rotatePageAction:hover {
                background: #e5edf8; color: #263449; border-color: #a9bbd2;
            }
            QFrame#topbar QPushButton#deleteTool:hover:enabled {
                background: #fbecef; color: #dc3545; border-color: #e7b7c0;
            }
            QFrame#topbar QPushButton#tool:checked:hover,
            QFrame#topbar QToolButton#selectTool:checked:hover {
                background: #dce9ff; color: #173f83; border-color: #6d99e6;
            }
            QFrame#topbar QToolButton#tagTool:checked, QFrame#topbar QToolButton#tagTool:checked:hover {
                background: #dce9ff; color: #173f83; border-color: #6d99e6;
            }
            """
        stylesheet = stylesheet.replace("{combo_chevron_path}", combo_chevron_path)
        stylesheet = stylesheet.replace("{combo_chevron_up_path}", combo_chevron_up_path)
        stylesheet = stylesheet.replace("{check_icon_path}", check_icon_path)
        stylesheet = stylesheet.replace("{UI_ACCENT}", UI_ACCENT)
        popup_tokens = engo_ui_theme_tokens(theme)
        popup = {
            "bg": popup_tokens["panel"], "fg": popup_tokens["text"],
            "border": popup_tokens["border"], "hover": popup_tokens["hover"],
            "hover_fg": popup_tokens["text"], "muted": popup_tokens["muted"],
            "selected": popup_tokens["selection"],
            "selected_border": popup_tokens["border_strong"],
            "selected_fg": popup_tokens["selection_text"],
            "field": popup_tokens["input"], "scroll": popup_tokens["scrollbar"],
        }
        stylesheet += f"""
            QDialog, QMessageBox, QInputDialog, QColorDialog {{ background:{popup['bg']}; color:{popup['fg']}; }}
            QDialog QLabel, QMessageBox QLabel, QInputDialog QLabel, QColorDialog QLabel {{ color:{popup['fg']}; }}
            QDialog QLineEdit, QDialog QTextEdit, QInputDialog QLineEdit {{ background:{popup['field']}; color:{popup['fg']}; border:1px solid {popup['border']}; selection-background-color:{popup['hover']}; selection-color:{popup['hover_fg']}; }}
            QToolTip {{ background:{popup['bg']}; color:{popup['fg']}; border:1px solid {popup['border']}; padding:5px 7px; }}
            QListWidget#thumbnails::item:selected, QTreeWidget#outline::item:selected {{ background:{popup['selected']}; color:{popup['selected_fg']}; border:1px solid {popup['selected_border']}; }}
            QListWidget#thumbnails::item:hover:!selected, QTreeWidget#outline::item:hover:!selected {{ background:{popup['hover']}; color:{popup['fg']}; }}
            QComboBox QAbstractItemView, QComboBox QAbstractItemView::viewport {{ background:{popup['field']}; color:{popup['fg']}; selection-background-color:{popup['hover']}; selection-color:{popup['hover_fg']}; outline:0; }}
            QComboBox QAbstractItemView::item:selected {{ background:{popup['hover']}; color:{popup['hover_fg']}; }}
        """
        # The central palette also drives custom dialogs and controls that have
        # legacy ID-specific QSS rules. Keep active primary actions accented; only
        # neutral / disabled surfaces use the raised and muted palette tokens.
        theme_tokens = engo_ui_theme_tokens(theme)
        app = QApplication.instance()
        if app is not None:
            shared_palette = engo_theme_qpalette(app.palette(), theme)
            app.setPalette(shared_palette)
            self.setPalette(shared_palette)
        stylesheet += f"""
            QPushButton#filesSecondaryButton, QPushButton#tabAdd,
            QToolButton#saveSplitButton, QToolButton#rotatePageAction,
            QToolButton#selectTool:!checked, QToolButton#tagTool:!checked {{
                background:{theme_tokens['raised']}; color:{theme_tokens['text']};
                border-color:{theme_tokens['border']}; }}
            QPushButton#filesSecondaryButton:hover, QPushButton#tabAdd:hover,
            QToolButton#saveSplitButton:hover, QToolButton#rotatePageAction:hover,
            QToolButton#selectTool:!checked:hover, QToolButton#tagTool:!checked:hover {{
                background:{theme_tokens['hover']}; color:{theme_tokens['text']};
                border-color:{theme_tokens['border_strong']}; }}
            QPushButton#filesSecondaryButton:pressed, QPushButton#tabAdd:pressed,
            QToolButton#saveSplitButton:pressed, QToolButton#rotatePageAction:pressed {{
                background:{theme_tokens['pressed']}; }}
            QPushButton#aiSend:disabled, QPushButton#aiSend:disabled:hover {{
                background:{theme_tokens['panel_alt']}; color:{theme_tokens['muted']};
                border-color:{theme_tokens['border']}; }}
            QToolButton#saveSplitButton::menu-button,
            QToolButton#rotatePageAction::menu-button,
            QToolButton#selectTool::menu-button, QToolButton#tagTool::menu-button {{
                background:{theme_tokens['raised']}; border-left:1px solid {theme_tokens['border']}; }}
            QComboBox {{ background:{theme_tokens['input']}; color:{theme_tokens['text']};
                border-color:{theme_tokens['border']}; selection-background-color:{theme_tokens['selection']};
                selection-color:{theme_tokens['selection_text']}; }}
            QComboBox:hover {{ background:{theme_tokens['hover']}; border-color:{theme_tokens['border_strong']}; }}
            QComboBox::drop-down {{ background:{theme_tokens['raised']}; border-left:1px solid {theme_tokens['border']}; }}
            QComboBox QAbstractItemView {{ background:{theme_tokens['panel']}; color:{theme_tokens['text']};
                border:1px solid {theme_tokens['border']}; selection-background-color:{theme_tokens['selection']};
                selection-color:{theme_tokens['selection_text']}; outline:0; }}
        """
        if theme == "light":
            stylesheet += f"""
                QPushButton#homeTopButton {{ background:{theme_tokens['accent']}; color:#ffffff;
                    border-color:{theme_tokens['accent']}; }}
                QPushButton#homeTopButton:hover {{ background:{theme_tokens['accent_hover']};
                    border-color:{theme_tokens['accent_hover']}; }}
                QPushButton#filesPrimaryButton {{ background:{theme_tokens['accent']}; color:#ffffff;
                    border-color:{theme_tokens['accent']}; }}
            """
        else:
            stylesheet += f"""
                QPushButton#homeTopButton, QPushButton#filesPrimaryButton {{
                    background:{theme_tokens['raised']}; color:{theme_tokens['text']};
                    border-color:{theme_tokens['border']}; }}
                QPushButton#homeTopButton:hover, QPushButton#filesPrimaryButton:hover {{
                    background:{theme_tokens['hover']}; border-color:{theme_tokens['border_strong']}; }}
                QPushButton#homeTopButton:pressed, QPushButton#filesPrimaryButton:pressed {{
                    background:{theme_tokens['pressed']}; }}
            """
        self.setStyleSheet(stylesheet)
        # Explicit view palettes prevent Windows/system accent colors (including purple)
        # from tinting the selected page in the Pages/Contents sidebar.
        for view_class in (QListWidget, QTreeWidget):
            for view in self.findChildren(view_class):
                try:
                    if view.objectName() not in ("thumbnails", "outline"):
                        continue
                    view_palette = QPalette(view.palette())
                    for color_group in (QPalette.ColorGroup.Active, QPalette.ColorGroup.Inactive, QPalette.ColorGroup.Disabled):
                        view_palette.setColor(color_group, QPalette.ColorRole.Highlight, QColor(popup["selected"]))
                        view_palette.setColor(color_group, QPalette.ColorRole.HighlightedText, QColor(popup["selected_fg"]))
                        view_palette.setColor(color_group, QPalette.ColorRole.Base, QColor(popup["field"]))
                        view_palette.setColor(color_group, QPalette.ColorRole.Text, QColor(popup["fg"]))
                    view.setPalette(view_palette)
                    view.viewport().setPalette(view_palette)
                except RuntimeError:
                    pass
        # Menus are separate native popup windows in Qt, so style them explicitly
        # whenever the application theme changes (including the Select / Hand menu).
        for popup_menu in self.findChildren(QMenu):
            try:
                _engo_apply_menu_consistency(
                    popup_menu, theme,
                    str(self.settings.value("interface_language", "en", type=str) or "en").lower().startswith("ar"),
                )
            except RuntimeError:
                continue
        for search_dialog in self.findChildren(PDFSearchDialog):
            try: search_dialog.apply_theme(theme)
            except RuntimeError: pass
        for translation_dialog in self.findChildren(TranslationCardDialog):
            try: translation_dialog.apply_theme(theme)
            except RuntimeError: pass
        is_ar_ui = str(self.settings.value("interface_language", "en", type=str) or "en").lower().startswith("ar")
        for child_dialog in self.findChildren(QDialog):
            try:
                if isinstance(child_dialog, AppSettingsDialog):
                    child_dialog.apply_theme(theme)
                elif isinstance(child_dialog, OfficeDocumentReaderDialog):
                    child_dialog.apply_theme(theme)
                elif child_dialog.objectName() == "tagManagerDialog":
                    self._apply_tag_manager_dialog_theme(child_dialog)
                elif isinstance(child_dialog, (QMessageBox, QInputDialog, QColorDialog, QFileDialog)):
                    _engo_apply_dialog_consistency(child_dialog, theme, is_ar_ui)
                else:
                    # Refresh the native palette for any other open dialog while
                    # leaving its specialized local QSS intact.
                    _engo_apply_dialog_consistency(child_dialog, theme, is_ar_ui)
            except RuntimeError:
                pass
        # Refresh a live lesson window from the same tokens after the application
        # theme changes, including when it is already open behind another dialog.
        live_dialog = getattr(self, "_live_tutor_dialog", None)
        if live_dialog is not None:
            try:
                live_dialog.configure_window_theme(True)
            except RuntimeError:
                self._live_tutor_dialog = None
        # Refresh document palettes rendered in the teaching dialog and any visible
        # chat markdown colors after Qt has applied the new stylesheet.
        app = QApplication.instance()
        if app is not None:
            font = QFont(app.font())
            base = float(self.settings.value("ui_base_font_pt", 9.0, type=float))
            font.setPointSizeF(max(7.0, min(15.0, base * scale)))
            app.setFont(font)
        # A live tutor window is a separate top-level dialog with its own stylesheet;
        # refresh it after changing the application theme so it cannot drift visually.
        live_dialog = getattr(self, "_live_tutor_dialog", None)
        if live_dialog is not None:
            try:
                live_dialog.configure_window_theme(True)
            except (RuntimeError, AttributeError):
                pass
        self._apply_text_font_preferences()

    def _apply_text_font_preferences(self):
        chat_pt = self.settings.value("ui_chat_font_pt", 13.0, type=float)
        typing_pt = self.settings.value("ui_typing_font_pt", 12.0, type=float)
        translation_pt = self.settings.value("ui_translation_font_pt", 13.0, type=float)
        panel = getattr(self, "ai_panel", None)
        if panel is not None:
            try:
                panel.apply_font_preferences(chat_pt, typing_pt)
            except (RuntimeError, AttributeError):
                pass
        for dialog in self.findChildren(TranslationCardDialog):
            try:
                dialog.set_font_size(translation_pt)
            except RuntimeError:
                continue

    def _apply_interface_language(self):
        language = str(self.settings.value("interface_language", "en", type=str) or "en").lower()
        language = "ar" if language.startswith("ar") else "en"
        previous_toolbar_language = getattr(self, "_toolbar_caption_language", None)
        self.setLayoutDirection(Qt.LayoutDirection.RightToLeft if language == "ar" else Qt.LayoutDirection.LeftToRight)
        # Toolbars are icon/action rails, not reading columns: preserve their left-to-right
        # control order regardless of the chosen language.
        tab_strip = getattr(self, "tab_strip", None)
        if tab_strip is not None:
            tab_strip.setLayoutDirection(Qt.LayoutDirection.LeftToRight)
            tab_layout = tab_strip.layout()
            if tab_layout is not None:
                tab_layout.setDirection(QBoxLayout.Direction.LeftToRight)
        doc_tabbar = getattr(self, "doc_tabbar", None)
        if doc_tabbar is not None:
            doc_tabbar.setLayoutDirection(Qt.LayoutDirection.LeftToRight)
        topbar = getattr(self, "topbar", None)
        if topbar is not None:
            topbar.setLayoutDirection(Qt.LayoutDirection.LeftToRight)
            for row_widget in (getattr(self, "toolbar_row_primary", None), getattr(self, "toolbar_row_secondary", None)):
                if row_widget is not None:
                    row_widget.setLayoutDirection(Qt.LayoutDirection.LeftToRight)
            for group in getattr(self, "_toolbar_groups", []):
                group.setLayoutDirection(Qt.LayoutDirection.LeftToRight)
        translations = {
            # Product and brand names are deliberately not translated.
            "Engo PDF Viewer & AI Study Agent": "Engo PDF Viewer & AI Study Agent", "Engo PDF": "Engo PDF", "ENGO": "ENGO",
            "ENGO · LIVE AI TEACHER": "ENGO · مدرس الذكاء الاصطناعي المباشر",
            "Lesson with AI": "AI حصة صوتية مع", "Audio lesson with AI": "AI حصة صوتية مع", "Voice && AI Teacher": "Audio lesson with AI",
            "ENGO AI": "ENGO AI", "Engo AI Chat": "Engo AI · المحادثة",
            "Home": "الرئيسية", "Return to open PDFs": "العودة إلى ملفات PDF المفتوحة", "Return to open files": "العودة إلى الملفات المفتوحة",
            "Quick file browser": "متصفح الملفات السريع", "Browse files": "تصفح الملفات", "This PC": "هذا الكمبيوتر", "Go to parent folder": "الانتقال إلى المجلد الأب", "Choose folder…": "اختر مجلدًا…",
            "Go": "انتقال", "Open selected": "فتح المحدد", "No PDF or image files in this folder": "لا توجد ملفات PDF أو صور في هذا المجلد",
            "Settings": "الإعدادات",
            "Open PDF files": "فتح ملفات PDF", "Open PDF": "فتح ملف PDF",
            "Open documents or images": "فتح ملفات نصية أو صور",
            "＋  Open documents or images": "＋  فتح ملفات نصية أو صور",
            "DROP PDF, WORD, POWERPOINT OR IMAGE FILES HERE": "أفلت ملفات PDF أو Word أو PowerPoint أو الصور هنا",
            "Open PDF, Word, PowerPoint or image files to read them. You can also drop supported files here.": "افتح ملفات PDF أو Word أو PowerPoint أو الصور لقراءتها. ويمكنك أيضًا إفلات الملفات المدعومة هنا.",
            "Reopen last session": "استعادة الجلسة السابقة",
            "Welcome back": "مرحبًا بعودتك", "Recent files": "الملفات الأخيرة",
            "Search": "بحث", "Save": "حفظ", "Open": "فتح", "Close": "إغلاق",
            "Select": "تحديد", "Hand": "يد", "Select text": "تحديد النص", "Highlight text": "تظليل النص", "Copy text": "نسخ النص",
            "Audio lesson with AI": "AI حصة صوتية مع",
            "Send": "إرسال", "Stop": "إيقاف", "PDF context": "سياق PDF",
            "Save As…": "حفظ باسم…", "Read latest": "اقرأ آخر إجابة",
            "Stop audio": "إيقاف الصوت", "Ask by voice": "اسأل بالصوت",
            "Ask by voice": "اسأل بالصوت", "Read latest": "اقرأ آخر إجابة", "Stop audio": "إيقاف الصوت",
            "Record one spoken question, send it to the selected AI, and read its answer aloud": "سجّل سؤالك صوتيًا وأرسله إلى المساعد المحدد واستمع إلى إجابته.",
            "Read the latest AI answer aloud": "اقرأ أحدث إجابة من الذكاء الاصطناعي بصوت مسموع.",
            "Stop the spoken answer": "أوقف قراءة الإجابة صوتيًا.",
            "Pages": "الصفحات", "Contents": "المحتوى", "LIBRARY": "المكتبة",
            "Sidebar": "الشريط الجانبي", "Scroll": "تمرير", "Book": "ككتاب",
            "Book · show two pages side by side; can be combined with Scroll": "ككتاب · عرض صفحتين جنبًا إلى جنب، ويمكن دمجه مع التمرير",
            "Unlink": "إلغاء الربط",
            "Fit width": "ملاءمة العرض", "Page Theme": "مظهر الصفحة",
            "AI Chat": "AI محادثة مع", "Voice && AI Teacher": "المدرس الصوتي وAI",
            "Translate": "ترجمة", "Present": "عرض", "Full Screen": "ملء الشاشة",
            "Your PDF study assistant": "مساعدك الدراسي لملفات PDF",
            "PDF actions ▾": "إجراءات PDF ▾", "PDF actions": "إجراءات PDF",
            "Export": "تصدير", "+ New chat": "+ محادثة جديدة",
            "Open a PDF to start a conversation.": "افتح ملف PDF لبدء محادثة.",
            "Open a PDF to ask questions about it.": "افتح ملف PDF لطرح الأسئلة حوله.",
            "Start full-page lesson": "ابدأ شرح الصفحة بالكامل",
            "End conversation": "إنهاء المحادثة", "Use current PDF pages": "استخدم صفحات PDF الحالية",
            "Hold SPACE to talk · release to send": "اضغط مطولًا على SPACE للتحدث ثم اتركه للإرسال",
            "Pause lesson": "إيقاف الشرح مؤقتًا", "Teacher voice": "صوت المدرّس",
            "Speaking language": "لغة التحدث", "Session mode": "وضع الجلسة",
            "Extra teacher personality & instructions": "شخصية المدرّس وتعليمات إضافية",
            "Teacher setup": "شخصية المدرّس والتعليمات الإضافية",
            "Teacher personality & extra instructions": "شخصية المدرّس والتعليمات الإضافية",
            "Teacher personality & instructions": "شخصية المدرّس والتعليمات الإضافية",
            "Save instructions": "حفظ التعليمات", "Cancel": "إلغاء",
            "Saved · applies next session": "تم الحفظ · يُطبّق في الحصة القادمة",
            "Show focus rectangle": "إظهار مستطيل التركيز", "Clear rectangle": "مسح التحديد",
            "Select area to ask about": "حدد منطقة للسؤال عنها", "CURRENT PDF PAGE": "صفحة PDF الحالية",
            "PRIMARY PDF": "ملف PDF الأساسي", "SUPPLEMENTARY PDF": "ملف PDF إضافي",
            "TEACHING BOARD · formulas and examples": "لوحة الشرح · القوانين والأمثلة",
            "Save for this PDF": "حفظ لهذا الملف", "Export all .md": "تصدير الكل بصيغة MD",
            "Export all PDF": "تصدير الكل PDF", "LIVE TRANSCRIPT": "النص المباشر للمحادثة",
            "Engo AI is preparing a reply": "يجهّز Engo AI الرد",
            "Your speech, typed messages, and Engo AI replies appear here during the conversation.": "سيظهر هنا كلامك ورسائلك المكتوبة وردود Engo AI أثناء المحادثة.",
            "Type a question or tell Engo how to edit the board…": "اكتب سؤالًا أو اطلب من Engo تعديل لوحة الشرح…",
            "Bold": "عريض", "Italic": "مائل", "Regular": "عادي",
            "Dark": "داكن", "Midnight": "منتصف الليل", "Light": "فاتح",
            "Grass": "عشبي", "Pink": "وردي", "Orange": "برتقالي",
            "Dark theme": "ثيم البرنامج", "Light theme": "الثيم الفاتح",
            "Message Engo AI…  ·  Enter to send · Shift+Enter for a new line · Paste an image with Ctrl+V": "اكتب رسالتك إلى Engo AI…",
            "↓ Latest message": "↓ آخر رسالة",
            "Engo AI Chat": "محادثة Engo AI", "Dual File Engo AI Chat": "محادثة Engo AI لملفين",
            "Your PDF study assistant": "مساعدك الدراسي لملفات PDF",
            "One shared conversation for both linked PDFs": "محادثة مشتركة لملفي PDF المرتبطين",
            "PDF context · ": "سياق PDF · ", "Attachments": "المرفقات", "Clear": "مسح",
            "Selected chat passage": "مقطع محدد من المحادثة",
            "Find text in this conversation…": "ابحث عن نص في هذه المحادثة…",
            "Previous match": "النتيجة السابقة", "Next match": "النتيجة التالية",
            "Close conversation search": "إغلاق البحث في المحادثة",
            "Add image from file…": "إضافة صورة من ملف…",
            "Paste image from clipboard": "لصق صورة من الحافظة",
            "Select region from current PDF": "تحديد منطقة من ملف PDF الحالي",
            "Clear pending attachments": "مسح المرفقات المعلّقة",
            "Add an image, paste from clipboard, or select a region from the PDF": "إضافة صورة أو لصقها من الحافظة أو تحديد منطقة من ملف PDF",
            "Remove pending images, PDF regions, and selected chat text": "إزالة الصور ومناطق PDF والنصوص المحددة المرفقة",
            "Remove selected chat text": "إزالة النص المحدد من المحادثة",
            "Search inside this conversation": "ابحث داخل هذه المحادثة",
            "Saved conversations for the current PDF": "المحادثات المحفوظة لملف PDF الحالي",
            "Saved conversations for this linked PDF pair": "المحادثات المحفوظة لملفي PDF المرتبطين",
            "Start a new saved conversation for this PDF": "بدء محادثة محفوظة جديدة لهذا الملف",
            "Start a new shared conversation for both linked PDFs": "بدء محادثة مشتركة جديدة لملفي PDF المرتبطين",
            "Scroll to the latest message in this conversation": "انتقل إلى أحدث رسالة في هذه المحادثة",
            "Open a PDF to ask questions about it.": "افتح ملف PDF لطرح الأسئلة حوله.",
            "Type what you want to ask about the selected text…": "اكتب ما تريد السؤال عنه بخصوص النص المحدد…",
            "Choose which AI service receives your question": "اختر خدمة الذكاء الاصطناعي التي ستستقبل سؤالك",
            "Include PDF text or page previews. Current-page actions always include the current page.": "إرفاق نص PDF أو معاينات الصفحات. إجراءات الصفحة الحالية ترفقها دائمًا.",
            "Record one spoken question, send it to the selected AI, and read its answer aloud": "سجّل سؤالك صوتيًا وأرسله إلى المساعد المحدد واستمع إلى إجابته.",
            "Read the latest AI answer aloud": "اقرأ أحدث إجابة من الذكاء الاصطناعي بصوت مسموع.",
            "PAGE THEME": "مظهر الصفحة", "Saved themes": "المظاهر المحفوظة", "Current settings": "الإعدادات الحالية",
            "Obsidian": "سبج", "Sepia": "بني دافئ", "Slate": "رمادي مزرق",
            "Dark Mode / Custom Document Colors": "الوضع الداكن / ألوان مخصصة للمستند", "Recolors rendered page pixels, including scanned notes and embedded images.": "يغيّر ألوان الصفحة المعروضة، بما في ذلك الملاحظات الممسوحة ضوئيًا والصور المضمّنة.",
            "Page background": "خلفية الصفحة", "Text / ink": "لون النص", "Text / ink color": "لون النص", "Quick presets": "مظاهر سريعة",
            "Save current as…": "حفظ الإعدادات الحالية باسم…", "Delete saved theme": "حذف المظهر المحفوظ", "Apply": "تطبيق",
            "ANNOTATION COLORS": "ألوان التعليقات التوضيحية", "Annotation Colors": "ألوان التعليقات التوضيحية",
            "These colors are used for new annotations. Existing annotations keep their saved colors.": "تُستخدم هذه الألوان للتعليقات التوضيحية الجديدة، بينما تحتفظ التعليقات الحالية بألوانها المحفوظة.",
            "Pen / drawing color": "لون القلم / الرسم", "Highlight color": "لون التظليل", "Sticky note marker color": "لون علامة الملاحظة اللاصقة",
            "Text box font color": "لون خط مربع النص", "Text box background color": "لون خلفية مربع النص", "Save colors": "حفظ الألوان",
        }
        translations.update(_ENGO_TOOLTIP_TRANSLATIONS)
        _reverse_ui_translations = {translated: source for source, translated in translations.items() if source != translated}
        def _translate_widget_tooltip(value):
            source = str(value or "")
            if language == "ar":
                return translations.get(source, _engo_translate_tooltip(source, "ar"))
            return _reverse_ui_translations.get(source, _engo_translate_tooltip(source, "en"))
        # Window titles are not QLabel/Button text, so translate them explicitly.
        dialog_title_translations = {"Page Theme": "مظهر الصفحة", "Annotation Colors": "ألوان التعليقات التوضيحية"}
        for dialog_widget in self.findChildren(QDialog):
            try:
                original_title = dialog_widget.property("engoOriginalWindowTitle")
                if original_title is None:
                    original_title = dialog_widget.windowTitle()
                    dialog_widget.setProperty("engoOriginalWindowTitle", original_title)
                if dialog_widget.objectName() == "tagManagerDialog":
                    apply_tag_language = getattr(dialog_widget, "_engo_apply_language", None)
                    if callable(apply_tag_language): apply_tag_language(language)
                elif dialog_widget.objectName() == "pdfSearchDialog":
                    dialog_widget.apply_language(language)
                elif dialog_widget.objectName() == "aiProviderSettingsDialog":
                    dialog_widget.apply_language(language)
                elif dialog_widget.objectName() == "translationCard":
                    dialog_widget.apply_language(language)
                else:
                    dialog_widget.setWindowTitle(dialog_title_translations.get(str(original_title), str(original_title)) if language == "ar" else str(original_title))
            except (RuntimeError, AttributeError):
                pass
        protected_brand_texts = {APP_NAME, APP_DATA_NAME, "Engo PDF Viewer", "Engo PDF Viewer & AI Study Agent", "Engo PDF"}

        # QLabel and button-family text, preserving the untranslated product identity.
        for widget_class in (QLabel, QPushButton, QToolButton, QCheckBox):
            for widget in self.findChildren(widget_class):
                try:
                    # Top-toolbar captions are responsive and deliberately managed by
                    # _apply_toolbar_density. Translating them here restores their full
                    # source labels on every open_live_tutor() call, which makes the bar
                    # overflow and appear crushed when the voice dialog opens.
                    _topbar = getattr(self, "topbar", None)
                    if (_topbar is not None and isinstance(widget, (QPushButton, QToolButton))
                            and _topbar.isAncestorOf(widget)):
                        continue
                    original = widget.property("engoOriginalText")
                    if original is None:
                        original = widget.text()
                        widget.setProperty("engoOriginalText", original)
                    original = str(original or "")
                    if original in protected_brand_texts or widget.objectName() in ("brandTitle", "brandName", "homeSideTitle"):
                        widget.setText(original)
                    else:
                        widget.setText(translations.get(original, original) if language == "ar" else original)
                    tooltip_original = widget.property("engoOriginalToolTip")
                    if tooltip_original is None:
                        tooltip_original = widget.toolTip()
                        widget.setProperty("engoOriginalToolTip", tooltip_original)
                    tip = str(tooltip_original or "")
                    if tip:
                        rendered_tip = _translate_widget_tooltip(tip)
                        widget.setToolTip(rendered_tip)
                        widget.setProperty("engoRenderedToolTip", rendered_tip)
                except RuntimeError:
                    continue

        # Tooltips can belong to any QWidget (combos, edits, trees, tabs, custom
        # controls), not only labels and buttons. Translate every descendant and
        # preserve its source string for a clean switch back to English.
        for widget in self.findChildren(QWidget):
            try:
                original_tip = widget.property("engoOriginalToolTip")
                if original_tip is None:
                    original_tip = widget.toolTip()
                    widget.setProperty("engoOriginalToolTip", original_tip)
                if original_tip:
                    rendered_tip = _translate_widget_tooltip(original_tip)
                    widget.setToolTip(rendered_tip)
                    widget.setProperty("engoRenderedToolTip", rendered_tip)
            except RuntimeError:
                continue

        for widget in self.findChildren(QTextEdit):
            if widget.objectName() == "teacherInstructionsEdit":
                placeholder_original = widget.property("engoOriginalPlaceholder")
                if placeholder_original is None:
                    placeholder_original = widget.placeholderText()
                    widget.setProperty("engoOriginalPlaceholder", placeholder_original)
                widget.setPlaceholderText(
                    "أضف تعليمات للمدرس الذكي… مثال: كن صبورًا، استخدم أمثلة مصرية، واشرح الرموز ببطء واختبر فهمي بعد كل موضوع."
                    if language == "ar" else str(placeholder_original or "")
                )

        # Translate menu actions such as the Select / Hand dropdown, retaining
        # their original English labels so switching languages remains reversible.
        for action in self.findChildren(QAction):
            try:
                original = action.property("engoOriginalText")
                if original is None:
                    original = action.text()
                    action.setProperty("engoOriginalText", original)
                original = str(original or "")
                action.setText(translations.get(original, original) if language == "ar" else original)
                original_tip = action.property("engoOriginalToolTip")
                if original_tip is None:
                    original_tip = action.toolTip()
                    action.setProperty("engoOriginalToolTip", original_tip)
                if original_tip:
                    action.setToolTip(_translate_widget_tooltip(original_tip))
            except RuntimeError:
                continue
        if hasattr(self, "select_tool_btn"):
            self._refresh_selector_tool_button()

        # Translate combo-box captions without changing their stable item data.
        for combo in self.findChildren(QComboBox):
            try:
                originals = combo.property("engoOriginalItems")
                if originals is None:
                    originals = [combo.itemText(i) for i in range(combo.count())]
                    combo.setProperty("engoOriginalItems", originals)
                for index, original in enumerate(originals):
                    if index < combo.count():
                        combo.setItemText(index, translations.get(str(original), str(original)) if language == "ar" else str(original))
            except RuntimeError:
                continue

        # Responsive PDF sidebar buttons are translated like the former native tabs.
        # Update discovered widgets and explicitly visit the document stack so tabs
        # opened dynamically always receive the current interface language.
        for sidebar_tabs in self.findChildren(ResponsiveSidebarTabs):
            try:
                sidebar_tabs.setLanguage(language)
            except RuntimeError:
                pass
        document_stack = getattr(self, "tabs", None)
        if document_stack is not None:
            try:
                for tab_index in range(document_stack.count()):
                    document_tab = document_stack.widget(tab_index)
                    sidebar_tabs = getattr(document_tab, "side_tabs", None)
                    if isinstance(sidebar_tabs, ResponsiveSidebarTabs):
                        sidebar_tabs.setLanguage(language)
            except (RuntimeError, AttributeError):
                pass

        # Document tab captions are kept reversible; file names are not translated.
        for tabbar in self.findChildren(QTabBar):
            try:
                originals = tabbar.property("engoOriginalTabs")
                if originals is None:
                    originals = [tabbar.tabText(i) for i in range(tabbar.count())]
                    tabbar.setProperty("engoOriginalTabs", originals)
                for index, original in enumerate(originals):
                    if index < tabbar.count():
                        tabbar.setTabText(index, translations.get(str(original), str(original)) if language == "ar" else str(original))
            except RuntimeError:
                continue

        # Placeholders are translated too, while keeping their original English source for toggling back.
        for widget_class in (QLineEdit, QTextEdit):
            for widget in self.findChildren(widget_class):
                try:
                    original = widget.property("engoOriginalPlaceholder")
                    if original is None:
                        original = widget.placeholderText()
                        widget.setProperty("engoOriginalPlaceholder", original)
                    value = str(original or "")
                    widget.setPlaceholderText(translations.get(value, value) if language == "ar" else value)
                except RuntimeError:
                    continue

        # Re-apply specialized dialog and tag-menu translations after the generic
        # widget pass, which intentionally handles ordinary static labels only.
        for search_dialog in self.findChildren(PDFSearchDialog):
            try: search_dialog.apply_language(language)
            except RuntimeError: pass
        for child_dialog in self.findChildren(QDialog):
            try:
                if isinstance(child_dialog, OfficeDocumentReaderDialog):
                    child_dialog.apply_language(language)
                elif child_dialog.objectName() == "tagManagerDialog":
                    apply_tag_language = getattr(child_dialog, "_engo_apply_language", None)
                    if callable(apply_tag_language): apply_tag_language(language)
            except RuntimeError:
                pass
        active_tag_tab = self._view_target_tab() or self.active_tab()
        if isinstance(active_tag_tab, DocumentTab):
            self._refresh_tag_menu(active_tag_tab)

        if hasattr(self, "open_btn"):
            self.open_btn.setText("الرئيسية" if language == "ar" else "Home")
        if hasattr(self, "return_to_docs_btn"):
            self.return_to_docs_btn.setText("العودة إلى الملفات المفتوحة" if language == "ar" else "Return to open files")
            self.return_to_docs_btn.setIcon(make_icon("next" if language == "ar" else "previous", "#b7c6dc", 16))
            # QPushButton places its icon after the text in RTL layout direction.
            self.return_to_docs_btn.setLayoutDirection(Qt.LayoutDirection.RightToLeft)
            tip = "العودة إلى ملفات PDF المفتوحة" if language == "ar" else "Return to open PDFs"
            self.return_to_docs_btn.setToolTip(tip)
            self.return_to_docs_btn.setAccessibleName(tip)
        if hasattr(self, "home_settings_btn"):
            self.home_settings_btn.setText("الإعدادات" if language == "ar" else "Settings")
            tip = "الإعدادات" if language == "ar" else "Settings"
            self.home_settings_btn.setToolTip(tip)
            self.home_settings_btn.setAccessibleName(tip)
        if hasattr(self, "home_nav_btn"):
            self.home_nav_btn.setText("⌂   الرئيسية" if language == "ar" else "⌂   Home")
        if hasattr(self, "home_side_title"):
            self.home_side_title.setText("الرئيسية" if language == "ar" else "Home")
        # The product/version signature is intentionally never localized. Keep its
        # content, paragraph direction, and alignment LTR even in the Arabic UI.
        footer = getattr(self, "home_side_footer", None)
        if footer is not None:
            footer.setText(HOME_FOOTER_TEXT)
            footer.setLayoutDirection(Qt.LayoutDirection.LeftToRight)
            footer.setAlignment(Qt.AlignmentFlag.AlignLeft | Qt.AlignmentFlag.AlignVCenter)
        if hasattr(self, "home_browser_title"):
            self.home_browser_title.setText("تصفح الملفات" if language == "ar" else "Browse files")
        if hasattr(self, "home_browser_path") and not str(getattr(self, "_home_browser_current_dir", "") or "").strip():
            self.home_browser_path.setText("هذا الكمبيوتر" if language == "ar" else "This PC")

        # AI composer labels are dynamic (Send/Stop) and can be reset whenever the
        # prompt text changes. Apply the language directly instead of relying only
        # on the generic descendant-widget translation pass.
        ai_panel = getattr(self, "ai_panel", None)
        if ai_panel is not None:
            try:
                ai_panel.apply_language(language)
            except (RuntimeError, AttributeError):
                pass

        # Toolbar text is recalculated only on an actual language change or its first
        # setup. Calling _apply_interface_language() when opening Lesson with AI must
        # never restore long labels or alter the user's chosen toolbar density.
        self._toolbar_caption_language = language
        if hasattr(self, "save_btn") and (previous_toolbar_language != language
                or not getattr(self, "_toolbar_density_initialized", False)):
            self._apply_toolbar_density(force=True)
        if hasattr(self, "recent_files_layout"):
            self._refresh_files_home()

        if hasattr(self, "context_help_label"):
            direction = Qt.LayoutDirection.RightToLeft if language == "ar" else Qt.LayoutDirection.LeftToRight
            self.status.setLayoutDirection(direction)
            self.context_help_label.setLayoutDirection(direction)
            self.context_help_label.setAlignment(
                Qt.AlignmentFlag.AlignVCenter | (Qt.AlignmentFlag.AlignRight if language == "ar" else Qt.AlignmentFlag.AlignLeft)
            )
            self._set_default_context_help()

    @staticmethod
    def _relative_opened_time(timestamp, language="en", action="opened"):
        is_ar = str(language or "en").lower().startswith("ar")
        try:
            seconds = max(0, int(time.time() - float(timestamp)))
        except Exception:
            return "تم فتحه سابقًا" if is_ar and action == "opened" else ("تم الحفظ سابقًا" if is_ar else "Previously opened")
        if is_ar:
            verb = "تم فتحه" if action == "opened" else "تم حفظه"
            if seconds < 60:
                return f"{verb} الآن"
            if seconds < 3600:
                value = max(1, seconds // 60)
                return f"{verb} منذ {value} دقيقة"
            if seconds < 86400:
                value = max(1, seconds // 3600)
                return f"{verb} منذ {value} ساعة"
            if seconds < 30 * 86400:
                value = max(1, seconds // 86400)
                return f"{verb} منذ {value} يوم"
            return f"{verb} في {time.strftime('%d/%m/%Y', time.localtime(float(timestamp)))}"
        verb = "Opened" if action == "opened" else "Saved"
        if seconds < 60:
            return f"{verb} just now"
        if seconds < 3600:
            value = max(1, seconds // 60)
            return f"{verb} {value} minute{'s' if value != 1 else ''} ago"
        if seconds < 86400:
            value = max(1, seconds // 3600)
            return f"{verb} {value} hour{'s' if value != 1 else ''} ago"
        if seconds < 30 * 86400:
            value = max(1, seconds // 86400)
            return f"{verb} {value} day{'s' if value != 1 else ''} ago"
        return time.strftime(f"{verb} %d %b %Y", time.localtime(float(timestamp)))

    def _load_recent_files(self):
        raw = self.settings.value("recent_files_json", "[]", type=str)
        try:
            entries = json.loads(raw)
            if not isinstance(entries, list):
                return []
        except Exception:
            return []
        clean, seen = [], set()
        for entry in entries:
            if not isinstance(entry, dict):
                continue
            path = os.path.abspath(str(entry.get("path", ""))) if entry.get("path") else ""
            key = os.path.normcase(path)
            if not path or key in seen or not os.path.isfile(path):
                continue
            seen.add(key)
            try:
                stamp = float(entry.get("opened_at", 0))
            except Exception:
                stamp = 0.0
            clean.append({"path": path, "opened_at": stamp})
            if len(clean) >= 40:
                break
        return clean

    def _record_recent_file(self, path):
        path = os.path.abspath(path or "")
        if not path or not os.path.isfile(path):
            return
        key = os.path.normcase(path)
        entries = [item for item in self._load_recent_files()
                   if os.path.normcase(item["path"]) != key]
        entries.insert(0, {"path": path, "opened_at": time.time()})
        self.settings.setValue("recent_files_json", json.dumps(entries[:40], ensure_ascii=False))
        self.settings.sync()
        if hasattr(self, "recent_files_layout"):
            self._refresh_files_home()

    def _clear_recent_files_ui(self):
        layout = getattr(self, "recent_files_layout", None)
        if layout is None:
            return
        while layout.count():
            item = layout.takeAt(0)
            widget = item.widget()
            if widget is not None:
                widget.deleteLater()

    def _refresh_files_home(self):
        if not hasattr(self, "recent_files_layout"):
            return
        self._clear_recent_files_ui()
        recent = self._load_recent_files()
        language = str(self.settings.value("interface_language", "en", type=str) or "en").lower()
        is_ar = language.startswith("ar")
        self.recent_count_label.setText((f"{len(recent)} ملف حديث" if is_ar else f"{len(recent)} recent") if recent else ("لا توجد ملفات حديثة" if is_ar else "No recent files yet"))
        last_session = self._read_last_session()
        last_entries = [item for item in (last_session or {}).get("tabs", [])
                        if isinstance(item, dict) and os.path.isfile(str(item.get("source_path") or item.get("path", "")))]
        has_last_session = bool(last_entries)
        self.files_restore_btn.setEnabled(has_last_session)
        if is_ar:
            self.files_restore_btn.setText(f"↺  استعادة الجلسة السابقة · {len(last_entries)} ملف" if has_last_session else "↺  استعادة الجلسة السابقة")
        else:
            self.files_restore_btn.setText(f"↺  Reopen last session · {len(last_entries)} document(s)" if has_last_session else "↺  Reopen last session")
        if has_last_session:
            names = [Path(str(item.get("source_path") or item.get("path", ""))).name for item in last_entries[:4]]
            if len(last_entries) > 4:
                names.append(f"+{len(last_entries) - 4} more")
            saved_at = self._relative_opened_time(last_session.get("saved_at", 0), language, "saved")
            self.last_session_summary.setText(("آخر جلسة · " if is_ar else "Last session · ") + "  ·  ".join(names) + f"   ({saved_at})")
            self.last_session_summary.show()
        else:
            self.last_session_summary.setText("لم يتم حفظ جلسة سابقة بعد" if is_ar else "No previous session saved yet")
            self.last_session_summary.show()
        if not recent:
            empty = QLabel("ستظهر هنا ملفات PDF والصور التي فتحتها مؤخرًا، مع وقت آخر فتح لكل ملف." if is_ar else "Your recently opened PDFs and images will appear here, along with when you last opened them.")
            empty.setObjectName("filesEmptyHint")
            empty.setWordWrap(True)
            self.recent_files_layout.addWidget(empty)
            return
        for entry in recent[:40]:
            path = entry["path"]
            row = QFrame()
            row.setObjectName("recentFileRow")
            row.setSizePolicy(QSizePolicy.Policy.Expanding, QSizePolicy.Policy.Fixed)
            row.setMinimumHeight(78)
            row.setMaximumHeight(82)
            row_layout = QHBoxLayout(row)
            row_layout.setContentsMargins(12, 8, 12, 8)
            row_layout.setSpacing(10)
            file_icon = QLabel("IMG" if is_image_document(path) else "PDF")
            file_icon.setObjectName("recentPdfIcon")
            file_icon.setAlignment(Qt.AlignmentFlag.AlignCenter)
            file_icon.setFixedSize(42, 42)
            row_layout.addWidget(file_icon)
            text_col = QVBoxLayout()
            name = QLabel(Path(path).name)
            name.setObjectName("recentFileName")
            name.setToolTip(path)
            where = QLabel(path)
            where.setObjectName("recentFilePath")
            where.setToolTip(path)
            when = QLabel(self._relative_opened_time(entry.get("opened_at", 0), language, "opened"))
            when.setObjectName("recentFileWhen")
            text_col.addWidget(name)
            text_col.addWidget(where)
            text_col.addWidget(when)
            row_layout.addLayout(text_col, 1)
            open_button = QPushButton("فتح" if is_ar else "Open")
            open_button.setObjectName("filesSecondaryButton")
            open_button.setProperty("recentFileAction", True)
            # Fifth home-screen action: compact the Open button in each recent-file card.
            # Keep its width text-driven (with a 72px minimum); reduce only its height.
            open_button.setMinimumWidth(80)
            open_button.setFixedHeight(27)
            open_button.clicked.connect(lambda _checked=False, value=path: self.open_pdf(value))
            row_layout.addWidget(open_button)
            self.recent_files_layout.addWidget(row)
        # A single recent file must remain a compact card at the top of the list;
        # the trailing stretch consumes empty viewport height, not the card itself.
        self.recent_files_layout.addStretch(1)

    def _read_last_session(self):
        raw = self.settings.value("last_session_json", "", type=str)
        try:
            data = json.loads(raw) if raw else None
            return data if isinstance(data, dict) else None
        except Exception:
            return None

    def _session_snapshot(self):
        entries = []
        for i in range(self.tabs.count()):
            tab = self.tabs.widget(i)
            if not isinstance(tab, DocumentTab):
                continue
            scroll_area = tab.scroll
            if tab._linked_view_secondary is not None and tab._secondary_scroll is not None:
                # Primary is visible in the left pane; the supplementary document
                # gets its own live scrollbar snapshot below.
                pass
            entries.append({
                "path": os.path.abspath(tab.path),
                "source_path": os.path.abspath(str(getattr(tab, "source_path", tab.path) or tab.path)),
                "page": int(tab.current_page),
                "book": bool(tab.book_mode),
                "scroll": bool(tab.scroll_mode),
                "fit_mode": str(tab.fit_mode),
                "custom_scale": float(tab.custom_scale),
                "custom_base_fit_mode": str(getattr(tab, "custom_base_fit_mode", "width")),
                "sidebar_visible": bool(tab._sidebar_visible),
                "h_scroll": int(scroll_area.horizontalScrollBar().value()),
                "v_scroll": int(scroll_area.verticalScrollBar().value()),
                "splitter_sizes": [int(value) for value in tab.splitter.sizes()],
                "linked_splitter_sizes": ([int(value) for value in tab._linked_splitter.sizes()]
                                           if tab._linked_splitter is not None else []),
            })
        # Apply the visible supplementary scrollbar snapshot after every tab
        # entry has been collected, regardless of the tab ordering.
        for i in range(self.tabs.count()):
            primary_tab = self.tabs.widget(i)
            if not isinstance(primary_tab, DocumentTab):
                continue
            secondary = getattr(primary_tab, "_linked_view_secondary", None)
            secondary_scroll = getattr(primary_tab, "_secondary_scroll", None)
            if secondary is not None and secondary_scroll is not None:
                for item in entries:
                    if os.path.normcase(item["path"]) == os.path.normcase(os.path.abspath(secondary.path)):
                        item["h_scroll"] = int(secondary_scroll.horizontalScrollBar().value())
                        item["v_scroll"] = int(secondary_scroll.verticalScrollBar().value())
                        break
        active = self.active_tab()
        target = self._view_target_tab()
        return {
            "version": 1,
            "saved_at": time.time(),
            "tabs": entries,
            "active_path": os.path.abspath(str(getattr(active, "source_path", active.path))) if active is not None else "",
            "view_target_path": os.path.abspath(str(getattr(target, "source_path", target.path))) if target is not None else "",
            "linked_pairs": [[os.path.abspath(primary), os.path.abspath(companion)]
                             for primary, companion in self._linked_pdf_pairs.items()],
            "window_maximized": bool(self.isMaximized()),
            "window_geometry": base64.b64encode(bytes(self.saveGeometry())).decode("ascii"),
            "workspace_sizes": [int(value) for value in (
                self._chat_focus_restore.get("workspace_sizes", self.workspace.sizes())
                if self._chat_focus_mode and self._chat_focus_restore else self.workspace.sizes()
            )],
            "toolbar_visible": bool(getattr(self, "_toolbar_pinned", True)),
            "toolbar_pinned": bool(getattr(self, "_toolbar_pinned", True)),
            "ai_panel_visible": bool(self.ai_panel.isVisible()),
            "teach_board_visible": bool(
                self._chat_focus_restore.get("board_visible", False)
                if self._chat_focus_mode and self._chat_focus_restore else self.teach_board.isVisible()
            ),
        }

    _session_close_burst_until = 0.0

    @staticmethod
    def _refresh_session_after_window_close():
        live = [window for window in MainWindow._open_windows if not getattr(window, "_closing_complete", False)]
        if live:
            live[0]._save_last_session(force=True)

    def _save_last_session(self, force=False):
        try:
            now = time.monotonic()
            if not force and now < MainWindow._session_close_burst_until:
                return
            if not force:
                # When Windows closes several top-level windows in one burst, keep
                # the snapshot captured by the first close event. A delayed refresh
                # below prunes windows that were intentionally closed while Engo stays open.
                MainWindow._session_close_burst_until = now + 1.8
            windows = [window for window in list(MainWindow._open_windows)
                       if not getattr(window, "_closing_complete", False)]
            snapshots = []
            for window in windows:
                try:
                    item = window._session_snapshot()
                    if item.get("tabs"):
                        snapshots.append(item)
                except Exception:
                    continue
            if snapshots:
                combined_tabs = [entry for item in snapshots for entry in item.get("tabs", [])]
                payload = {
                    "version": 2, "saved_at": time.time(), "windows": snapshots,
                    "tabs": combined_tabs,
                    "active_path": snapshots[0].get("active_path", ""),
                }
                self.settings.setValue("last_session_json", json.dumps(payload, ensure_ascii=False))
            else:
                self.settings.remove("last_session_json")
            self.settings.sync()
        except Exception as exc:
            try:
                self.show_status(f"Could not save the last session: {exc}")
            except Exception:
                pass

    def _restore_last_session(self):
        saved = self._read_last_session()
        if not saved:
            _ar = str(self.settings.value("interface_language", "en", type=str) or "en").lower().startswith("ar")
            QMessageBox.information(self, "الجلسة السابقة" if _ar else "Last session", "لا توجد جلسة مستندات يمكن استعادتها بعد." if _ar else "There is no restorable document session yet.",)
            self._refresh_files_home()
            return
        snapshots = saved.get("windows") if isinstance(saved.get("windows"), list) else [saved]
        snapshots = [item for item in snapshots if isinstance(item, dict) and item.get("tabs")]
        if not snapshots:
            _ar = str(self.settings.value("interface_language", "en", type=str) or "en").lower().startswith("ar")
            QMessageBox.information(self, "الجلسة السابقة" if _ar else "Last session", "لا توجد جلسة مستندات يمكن استعادتها بعد." if _ar else "There is no restorable document session yet.",)
            self._refresh_files_home()
            return
        # Restore the first saved window into this instance, then recreate each
        # additional detached window with its own tabs, active document and geometry.
        for index, item in enumerate(snapshots):
            target = self if index == 0 else MainWindow(register_ipc=False)
            restored = target._restore_single_window_session(item)
            if not restored:
                if index > 0:
                    target.close()
                return
            if index > 0:
                target.show()
                target.raise_()
                target.activateWindow()
        self._refresh_files_home()
        self.show_status(f"Restored last session · {len(snapshots)} window(s)")

    def _ask_localized(self, title_en, title_ar, text_en, text_ar, buttons, default, labels_ar):
        """Question box whose title, text and buttons follow the interface language."""
        is_ar = str(self.settings.value("interface_language", "en", type=str) or "en").lower().startswith("ar")
        box = QMessageBox(self)
        box.setIcon(QMessageBox.Icon.Question)
        box.setWindowTitle(title_ar if is_ar else title_en)
        box.setText(text_ar if is_ar else text_en)
        box.setStandardButtons(buttons)
        box.setDefaultButton(default)
        if is_ar:
            for std, label in labels_ar.items():
                btn = box.button(std)
                if btn is not None:
                    btn.setText(label)
        for choice_button in box.buttons():
            choice_button.setMinimumWidth(96)
            choice_button.setFixedHeight(28)
        box.setAttribute(Qt.WidgetAttribute.WA_StyledBackground, True)
        _engo_apply_dialog_consistency(box)
        QTimer.singleShot(0, lambda dialog=box: _engo_apply_dialog_consistency(dialog))
        return QMessageBox.StandardButton(box.exec())

    def _restore_single_window_session(self, snapshot):
        entries = snapshot.get("tabs", []) if isinstance(snapshot, dict) else []
        valid_entries = [entry for entry in entries if isinstance(entry, dict)
                         and os.path.isfile(str(entry.get("source_path") or entry.get("path", "")))
                         and is_supported_document(str(entry.get("source_path") or entry.get("path", "")))]
        if not valid_entries:
            _ar = str(self.settings.value("interface_language", "en", type=str) or "en").lower().startswith("ar")
            QMessageBox.information(self, "الجلسة السابقة" if _ar else "Last session", "لا توجد جلسة مستندات يمكن استعادتها بعد." if _ar else "There is no restorable document session yet.",)
            self._refresh_files_home()
            return False
        if self.tabs.count():
            choice = self._ask_localized(
                "Restore last session", "استعادة الجلسة السابقة",
                "Close the currently open tabs and reopen the previous session?",
                "هل تريد إغلاق التبويبات المفتوحة حاليًا وفتح الجلسة السابقة؟",
                QMessageBox.StandardButton.Yes | QMessageBox.StandardButton.No,
                QMessageBox.StandardButton.Yes,
                {QMessageBox.StandardButton.Yes: "نعم", QMessageBox.StandardButton.No: "لا"})
            if choice != QMessageBox.StandardButton.Yes:
                return False
            # Resolve all unsaved changes before removing any tabs, so Cancel
            # never leaves the current workspace half-closed.
            for index in range(self.tabs.count()):
                tab = self.tabs.widget(index)
                if isinstance(tab, DocumentTab) and tab.has_unsaved_changes():
                    choice = self._ask_localized(
                        "Unsaved PDF changes", "تغييرات PDF غير محفوظة",
                        f"Save changes to {Path(tab.path).name} before replacing the current workspace?",
                        f"هل تريد حفظ التغييرات في {Path(tab.path).name} قبل استبدال مساحة العمل الحالية؟",
                        QMessageBox.StandardButton.Save | QMessageBox.StandardButton.Discard | QMessageBox.StandardButton.Cancel,
                        QMessageBox.StandardButton.Save,
                        {QMessageBox.StandardButton.Save: "حفظ", QMessageBox.StandardButton.Discard: "تجاهل",
                         QMessageBox.StandardButton.Cancel: "إلغاء"})
                    if choice == QMessageBox.StandardButton.Cancel:
                        return False
                    if choice == QMessageBox.StandardButton.Save and not tab.save(False):
                        return False
            # Tear down linked splitters before closing either PDF, then remove
            # the old tabs cleanly from both the stack and the tab bar.
            for index in range(self.tabs.count()):
                tab = self.tabs.widget(index)
                if isinstance(tab, DocumentTab) and tab._linked_view_secondary is not None:
                    tab.disable_linked_view()
            self._linked_pdf_pairs.clear()
            for index in reversed(range(self.tabs.count())):
                tab = self.tabs.widget(index)
                if isinstance(tab, DocumentTab):
                    tab.close_document()
                self.tabs.removeWidget(tab)
                if index < self.doc_tabbar.count():
                    close_button = self.doc_tabbar.tabButton(index, QTabBar.ButtonPosition.RightSide)
                    if close_button is not None:
                        self.doc_tabbar.setTabButton(index, QTabBar.ButtonPosition.RightSide, None)
                        close_button.deleteLater()
                    self.doc_tabbar.removeTab(index)
                    self._schedule_brand_title_update()
                if isinstance(tab, DocumentTab):
                    tab.deleteLater()
            self._tab_order.clear()
        for entry in valid_entries:
            self.open_pdf(str(entry.get("source_path") or entry["path"]))
        # Restore explicit links only because the user explicitly requested the
        # previous session. Ordinary multi-file opening never auto-links files.
        for pair in snapshot.get("linked_pairs", []):
            if not isinstance(pair, (list, tuple)) or len(pair) != 2:
                continue
            primary_path, secondary_path = map(str, pair)
            if self._open_document_tab_by_path(primary_path) and self._open_document_tab_by_path(secondary_path):
                self._apply_linked_pdf_pair(primary_path, secondary_path)
        for entry in valid_entries:
            tab = self._open_document_tab_by_path(str(entry.get("source_path") or entry["path"]))
            if tab is None:
                continue
            try:
                tab.current_page = max(0, min(int(entry.get("page", 0)), tab.page_count - 1))
                tab.book_mode = bool(entry.get("book", False))
                if tab.book_mode:
                    tab.current_page = (tab.current_page // 2) * 2
                tab.scroll_mode = bool(entry.get("scroll", True))
                tab.fit_mode = entry.get("fit_mode", "width") if entry.get("fit_mode") in ("width", "page", "custom") else "width"
                tab.custom_scale = max(0.12, min(6.0, float(entry.get("custom_scale", 1.0))))
                base_fit = str(entry.get("custom_base_fit_mode", "width"))
                tab.custom_base_fit_mode = base_fit if base_fit in ("width", "page") else "width"
                tab._sidebar_visible = bool(entry.get("sidebar_visible", True))
                tab.sidebar.setVisible(tab._sidebar_visible)
                tab.sidebar.setMaximumWidth(218 if tab._sidebar_visible else 0)
                tab._relayout()
                tab._sync_sidebar_selection()
                tab.canvas.update()
            except Exception:
                pass
        # Make sure the primary linked tabs have their split view rebuilt after
        # restoring each document's page and zoom state.
        self._refresh_linked_tab_layout()
        active_path = os.path.normcase(os.path.abspath(snapshot.get("active_path", "")))
        active_tab = self._open_document_tab_by_path(active_path) if active_path else None
        if active_tab is not None:
            primary = self._linked_primary_for_path(active_tab.path)
            if primary is not None:
                active_tab = primary
            index = self.tabs.indexOf(active_tab)
            if index >= 0:
                self.doc_tabbar.setCurrentIndex(index)
                self.tabs.setCurrentIndex(index)
        view_path = os.path.normcase(os.path.abspath(snapshot.get("view_target_path", "")))
        view_tab = self._open_document_tab_by_path(view_path) if view_path else None
        self._linked_view_target = view_tab if view_tab is not None else self.active_tab()
        self._refresh_view_target_style()
        self._update_controls()
        self._show_document_area()
        try:
            self._toolbar_pinned = bool(snapshot.get("toolbar_pinned", snapshot.get("toolbar_visible", True)))
            self._toolbar_manually_hidden = not self._toolbar_pinned
            self._fullscreen_toolbar_pinned = self._toolbar_pinned
            self.topbar.setVisible(True)
            self.topbar.setMaximumHeight(16777215 if self._toolbar_pinned else 3)
            self._sync_toolbar_pin_button()
            if snapshot.get("ai_panel_visible"):
                self.ai_panel.show()
                self.ai_chat_btn.setChecked(True)
            else:
                self.ai_panel.hide()
                self.ai_chat_btn.setChecked(False)
            if snapshot.get("teach_board_visible"):
                self.teach_board.show()
            else:
                self.teach_board.hide()
            workspace_sizes = snapshot.get("workspace_sizes", [])
            if isinstance(workspace_sizes, list) and len(workspace_sizes) >= 3:
                self.workspace.setSizes([max(0, int(value)) for value in workspace_sizes[:3]])
            geometry = snapshot.get("window_geometry", "")
            if geometry:
                self.restoreGeometry(QByteArray(base64.b64decode(geometry.encode("ascii"))))
            if snapshot.get("window_maximized"):
                self.showMaximized()
            else:
                self.showNormal()
        except Exception:
            pass
        # A restored normal/maximized geometry may differ from the constructor
        # size. Reflow once the restored geometry reaches the toolbar layout.
        self._schedule_toolbar_density_update()
        QTimer.singleShot(120, self._apply_toolbar_density)
        QTimer.singleShot(340, self._apply_toolbar_density)
        # Apply saved viewport positions after all canvases have completed layout.
        def restore_scroll_positions():
            for entry in valid_entries:
                tab = self._open_document_tab_by_path(entry["path"])
                if tab is None:
                    continue
                h, v = int(entry.get("h_scroll", 0)), int(entry.get("v_scroll", 0))
                primary = self._linked_primary_for_path(tab.path)
                if primary is not None and primary._secondary_scroll is not None:
                    primary._secondary_scroll.horizontalScrollBar().setValue(h)
                    primary._secondary_scroll.verticalScrollBar().setValue(v)
                else:
                    tab.scroll.horizontalScrollBar().setValue(h)
                    tab.scroll.verticalScrollBar().setValue(v)
                splitter_sizes = entry.get("splitter_sizes", [])
                if isinstance(splitter_sizes, list) and len(splitter_sizes) >= 2:
                    try:
                        tab.splitter.setSizes([max(0, int(v)) for v in splitter_sizes[:2]])
                    except Exception:
                        pass
                linked_sizes = entry.get("linked_splitter_sizes", [])
                if tab._linked_splitter is not None and isinstance(linked_sizes, list) and len(linked_sizes) >= 2:
                    try:
                        tab._linked_splitter.setSizes([max(0, int(v)) for v in linked_sizes[:2]])
                    except Exception:
                        pass
                tab.sidebar.setVisible(tab._sidebar_visible)
                tab.sidebar.setMaximumWidth(218 if tab._sidebar_visible else 0)
            self._refresh_files_home()
        QTimer.singleShot(450, restore_scroll_positions)
        self.show_status(f"Restored last session · {len(valid_entries)} PDF file(s)")
        return True

    def _offer_restore_last_session(self):
        snapshot = self._read_last_session()
        snapshots = snapshot.get("windows") if snapshot and isinstance(snapshot.get("windows"), list) else ([snapshot] if snapshot else [])
        entries = []
        for item in snapshots:
            if isinstance(item, dict):
                saved_tabs = item.get("tabs", [])
                if isinstance(saved_tabs, list):
                    entries.extend(entry for entry in saved_tabs if isinstance(entry, dict))
        count = sum(1 for entry in entries if os.path.isfile(str(entry.get("path", ""))))
        if count < 1:
            self._show_files_screen()
            return
        is_ar = str(self.settings.value("interface_language", "en", type=str) or "en").lower().startswith("ar")
        box = QMessageBox(self)
        box.setIcon(QMessageBox.Icon.Question)
        box.setWindowTitle("مرحبًا بعودتك إلى Engo" if is_ar else "Welcome back to Engo")
        box.setText(
            f"هل تريد فتح الجلسة السابقة؟\n\nكان هناك {count} ملف PDF مفتوحًا عند إغلاق Engo آخر مرة."
            if is_ar else
            f"Open your last session?\n\n{count} PDF file(s) were open when you last closed Engo."
        )
        box.setStandardButtons(QMessageBox.StandardButton.Yes | QMessageBox.StandardButton.No)
        box.setDefaultButton(QMessageBox.StandardButton.Yes)
        if is_ar:
            box.button(QMessageBox.StandardButton.Yes).setText("فتح الجلسة")
            box.button(QMessageBox.StandardButton.No).setText("ليس الآن")
        # Startup restore actions use the same 28px height and text-driven width
        # as Save / Discard / Cancel in the exit confirmation.
        for choice_button in box.buttons():
            choice_button.setMinimumWidth(96)
            choice_button.setFixedHeight(28)
        box.setAttribute(Qt.WidgetAttribute.WA_StyledBackground, True)
        _engo_apply_dialog_consistency(box)
        # A second queued pass handles native Windows message-box children created
        # lazily when exec() opens the dialog.
        QTimer.singleShot(0, lambda dialog=box: _engo_apply_dialog_consistency(dialog))
        choice = box.exec()
        if choice == QMessageBox.StandardButton.Yes:
            self._restore_last_session()
        else:
            self._show_files_screen()

    def _button(self, text, kind, icon_name=None, icon_color="#b7c6dc"):
        btn = MotionButton(text)
        btn.setObjectName(kind.split()[0])
        if icon_name:
            btn.setIcon(make_icon(icon_name, icon_color, 18))
            btn.setProperty("engoIconName", str(icon_name))
            btn.setProperty("engoIconBaseColor", str(icon_color))
            btn.setIconSize(QSize(17, 17))
        btn.setCursor(Qt.CursorShape.PointingHandCursor)
        btn.setFocusPolicy(Qt.FocusPolicy.NoFocus)
        btn.setMinimumHeight(28)
        btn.setSizePolicy(QSizePolicy.Policy.Fixed, QSizePolicy.Policy.Fixed)
        if kind.split()[0] == "compact":
            btn.setFixedSize(30, 29)
            btn.setProperty("compactAction", True)
        if kind.split()[0] == "tabAdd":
            btn.setIconSize(QSize(17, 17))
        btn.setAccessibleName(text or btn.toolTip())
        return btn

    def _vline(self):
        line = QFrame()
        line.setObjectName("vline")
        line.setFrameShape(QFrame.Shape.VLine)
        return line

    def _apply_windows_titlebar_theme(self, palette=None):
        """Apply the same native Windows caption treatment used by all dialogs."""
        theme = normalize_ui_theme(self.settings.value("ui_theme", "dark", type=str))
        return _engo_apply_windows_caption_theme(self, theme, self.settings)

    def _apply_style(self):
        theme_tokens = engo_ui_theme_tokens(self.settings.value("ui_theme", "dark", type=str))
        ui_bg = theme_tokens["window"]
        ui_text = theme_tokens["text"]
        ui_muted = theme_tokens["muted"]
        ui_accent = theme_tokens["accent"]
        check_icon_path = resource_path("checkbox_checked.png").replace(os.sep, "/")
        # The AI provider/model combo arrows are embedded in this f-string
        # stylesheet, so resolve the theme-specific asset in this scope first.
        current_ui_theme = normalize_ui_theme(self.settings.value("ui_theme", "dark", type=str))
        combo_chevron_asset = "combo_chevron_light.png" if current_ui_theme == "light" else "combo_chevron_dark.png"
        combo_chevron_path = resource_path(combo_chevron_asset).replace("\\", "/")
        combo_chevron_up_asset = (
            "combo_chevron_up_light.png" if current_ui_theme == "light" else "combo_chevron_up_dark.png"
        )
        combo_chevron_up_path = resource_path(combo_chevron_up_asset).replace("\\", "/")
        base_stylesheet = f"""
        QWidget {{ color: {ui_text}; font-family: 'Segoe UI'; font-size: 8pt; }}
        QMainWindow, QWidget#mainRoot {{ background: {ui_bg}; }}
        QFrame#tabStrip {{ background: #171b23; border-bottom: 1px solid #303847; }}
        QLabel#logoMark {{ color: white; font-size: 14pt; font-weight: 800; border-radius: 8px;
            background: qlineargradient(x1:0,y1:0,x2:1,y2:1,stop:0 #4988ff,stop:1 #8959ef); }}
        QLabel#brandTitle {{ font-size: 9pt; font-weight: 750; color: #edf2fc; padding-right: 4px; }}
        QWidget#filesHome {{ background: #171c25; }}
        QScrollArea#recentFilesScroll {{ background: transparent; border: 0; }}
        QScrollArea#recentFilesScroll > QWidget > QWidget {{ background: transparent; }}
        QLabel#filesHomeTitle {{ color: #f2f5fb; font-size: 23pt; font-weight: 750; }}
        QLabel#filesHomeSubtitle {{ color: #9caabe; font-size: 10pt; }}
        QLabel#filesHeroTitle {{ color: #f3f6fc; font-size: 19pt; font-weight: 700; }}
        QLabel#filesHeroHint, QLabel#filesSectionHint, QLabel#filesEmptyHint {{ color: #aab5c7; font-size: 9pt; }}
        QLabel#filesSessionSummary {{ color: #b5c9e8; background: #263347; border: 1px solid #3b506f; border-radius: 7px; padding: 7px 9px; font-size: 8.5pt; }}
        QLabel#filesSectionTitle {{ color: #eef2f9; font-size: 13pt; font-weight: 700; }}
        QLabel#filesDropHint {{ color: #8fa6c8; background: #202938; border: 1px dashed #50627d; border-radius: 9px; padding: 12px; font-weight: 700; letter-spacing: 2px; }}
        QFrame#filesHero {{ background: #202a39; border: 1px solid #35465e; border-radius: 15px; }}
        QFrame#homeFileBrowser {{ background: #202630; border: 1px solid #354154; border-radius: 10px; }}
        QTreeView#homeBrowserTree {{ background: #171c25; color: #e9edf5; border: 1px solid #354154; border-radius: 7px; padding: 4px; outline: 0; }}
        QTreeView#homeBrowserTree::item {{ padding: 5px 5px; border-radius: 4px; }}
        QTreeView#homeBrowserTree::item:selected {{ background: #304563; color: #ffffff; }}
        QTreeView#homeBrowserTree::item:hover:!selected {{ background: #252e3b; color: #f0f4fb; }}
        QFrame#recentFileRow {{ background: #202630; border: 1px solid #303b4b; border-radius: 9px; }}
        QLabel#recentPdfIcon {{ color: #a9c5ff; background: #2b3a54; border-radius: 8px; font-weight: 800; }}
        QLabel#recentFileName {{ color: #edf2fb; font-size: 10pt; font-weight: 650; }}
        QLabel#recentFilePath, QLabel#recentFileWhen {{ color: #94a1b5; font-size: 8pt; }}
        QPushButton#filesPrimaryButton {{ color: white; background: #497ff0; border: 1px solid #6494fb; border-radius: 8px; padding: 10px 15px; font-weight: 700; }}
        QPushButton#filesPrimaryButton:hover {{ background: #5b8df6; }}
        QPushButton#filesSecondaryButton {{ color: #dce6f7; background: #303b4c; border: 1px solid #48576d; border-radius: 7px; padding: 3px 9px; min-height: 24px; }}
        QPushButton#filesSecondaryButton:hover {{ background: #3a4960; }}
        QTabBar#documentTabBar {{ background: transparent; qproperty-drawBase: 0; }}
        QTabBar#documentTabBar::tab {{ background: #202631; color: #aab5c8; border: 1px solid #333d4d;
            border-radius: 9px; padding: 6px 2px 7px 10px; margin-right: 5px; min-width: 118px; max-width: 280px; }}
        QTabBar#documentTabBar::tab:selected {{ background: #2b3546; color: #f4f7fd; border: 1px solid #536b91;
            border-top: 2px solid {ui_accent}; }}
        QTabBar#documentTabBar::tab:hover {{ background: #2b3442; color: white; }}
        QToolButton#documentTabCloseButton {{ background: transparent; border: 1px solid transparent;
            border-radius: 6px; padding: 0; margin: 0; min-width: 20px; max-width: 20px;
            min-height: 20px; max-height: 20px; }}
        QToolButton#documentTabCloseButton:hover {{ background: #8b5260; border-color: #b56a78; }}
        QToolButton#documentTabCloseButton:pressed {{ background: #6f3440; border-color: #d18a96; }}
        QFrame#topbar {{ background: #1b202a; border-bottom: 1px solid #333d4a; }}
        QToolButton#saveSplitButton {{ background: #252c38; border: 1px solid #4d6687; border-radius: 7px; color: #e3edfc; padding: 3px 6px; font-size: 7.5pt; font-weight: 650; }}
        QToolButton#saveSplitButton:hover {{ background: #303d51; border-color: #82a9dc; }}
        QToolButton#saveSplitButton::menu-button {{ border-left: 1px solid #52647b; width: 15px; }}
        QFrame#toolbarGroup {{ background: #202630; border: 1px solid #303b4a; border-radius: 9px; }}
        QFrame#annotationGroup {{ background: #191f29; border: 1px solid #3a4658; border-radius: 9px; }}
        QLabel#zoomLabel {{ color: #e2ebfb; font-weight: 700; font-size: 8pt; padding: 0 2px; }}
        QLabel#muted {{ color: {ui_muted}; font-size: 8pt; }}
        QPushButton {{ background: #252d39; border: 1px solid #384456; border-radius: 7px;
            padding: 3px 3px; min-height: 22px; spacing: 3px; color: #d8e1ef; font-size: 7.5pt; font-weight: 550; }}
        QPushButton:hover {{ background: #303b4b; border-color: #53657d; }}
        QPushButton:pressed {{ background: #151b25; border-color: #465670; }}
        QPushButton:disabled {{ color: #626d7d; background: #202630; border-color: #2c3441; }}
        QPushButton#primary {{ background: qlineargradient(x1:0,y1:0,x2:0,y2:1,stop:0 #638ff7,stop:1 #4775df);
            border: 1px solid #6994f7; color: white; font-weight: 750; padding-left: 6px; padding-right: 7px; }}
        QPushButton#primary:hover {{ background: #7099fa; border-color: #9ab8ff; }}
        QPushButton#action {{ background: #252c38; border: 1px solid #344052; color: #d1dced; }}
        QPushButton#action:hover {{ background: #303949; border-color: #536681; color: #f2f6ff; }}
        QToolButton#rotatePageAction {{ background: #252c38; border: 1px solid #344052; border-radius: 7px;
            color: #d1dced; padding: 3px 5px; font-size: 7.5pt; font-weight: 550; }}
        QToolButton#rotatePageAction:hover {{ background: #303949; border-color: #536681; color: #f2f6ff; }}
        QToolButton#rotatePageAction:disabled {{ color: #626d7d; background: #202630; border-color: #2c3441; }}
        QToolButton#rotatePageAction::menu-button {{ border-left: 1px solid #46546a; width: 15px; }}
        QPushButton#mode {{ background: transparent; border: 1px solid transparent; color: #aab7ca; padding-left: 6px; padding-right: 6px; }}
        QPushButton#mode:checked {{ background: #2c4266; border: 1px solid #547cbd; color: #f3f7ff; }}
        QPushButton#compact {{ padding: 1px; min-width: 28px; max-width: 30px; }}
        QPushButton#pageNavArrow {{ background: #252d39; border: 1px solid #3b485a; border-radius: 6px;
            padding: 1px; color: #d6e2f6; font-size: 11pt; font-weight: 700; }}
        QPushButton#pageNavArrow:hover:enabled {{ background: #334153; border-color: #637b9a; }}
        QPushButton#pageNavArrow:disabled {{ color: #626d7d; background: #202630; border-color: #2c3441; }}
        QPushButton#tool {{ background: transparent; border: 1px solid transparent; border-radius: 7px; color: #c4cedd;
            padding: 3px 3px; font-size: 7.5pt; font-weight: 600; }}
        QPushButton#tool:hover {{ background: #2a3546; border-color: #3b4b62; }}
        QPushButton#tool:checked {{ background: qlineargradient(x1:0,y1:0,x2:0,y2:1,stop:0 #426ca6,stop:1 #294b7b);
            border: 1px solid #8fc0ff; border-bottom: 3px solid #79d6bb; color: #ffffff; font-weight: 800; }}
        QPushButton#tool[linkedPaneTarget="secondary"], QPushButton#action[linkedPaneTarget="secondary"],
        QPushButton#history[linkedPaneTarget="secondary"], QPushButton#deleteTool[linkedPaneTarget="secondary"],
        QToolButton#tagTool[linkedPaneTarget="secondary"], QToolButton#selectTool[linkedPaneTarget="secondary"] {{ background: rgba(214, 166, 55, 42); border: 1px solid rgba(238, 193, 91, 145); }}
        QPushButton#tool:checked[linkedPaneTarget="secondary"], QToolButton#tagTool:checked[linkedPaneTarget="secondary"],
        QToolButton#selectTool:checked[linkedPaneTarget="secondary"] {{
            background: qlineargradient(x1:0,y1:0,x2:0,y2:1,stop:0 #8c6a25,stop:1 #614817);
            border: 1px solid #f6cf70; border-bottom: 3px solid #f6cf70; color: #fff8e5; font-weight: 800; }}
        QToolButton#selectTool {{ background: transparent; border: 1px solid transparent; border-radius: 7px; padding: 2px; }}
        QToolButton#selectTool:hover {{ background: #2a3546; border-color: #3b4b62; }}
        QToolButton#selectTool:checked {{ background: qlineargradient(x1:0,y1:0,x2:0,y2:1,stop:0 #426ca6,stop:1 #294b7b);
            border: 1px solid #8fc0ff; border-bottom: 3px solid #79d6bb; }}
        QToolButton#selectTool::menu-button {{ width: 12px; border-left: 1px solid rgba(180,190,210,80); }}
        QToolButton#tagTool {{ background: transparent; border: 1px solid transparent; border-radius: 7px; padding: 2px; }}
        QToolButton#tagTool:hover {{ background: #2a3546; border-color: #3b4b62; }}
        QToolButton#tagTool:checked {{ background: #3b3152; border: 1px solid #d5b1ff; border-bottom: 3px solid #d5b1ff; }}
        QToolButton#tagTool::menu-button {{ width: 12px; border-left: 1px solid rgba(180,190,210,80); }}
        QPushButton#toolbarPinButton {{ background: #242b37; border: 1px solid #354156; border-radius: 7px; padding: 1px; }}
        QPushButton#toolbarPinButton:hover {{ background: #30415a; border-color: #70a58f; }}
        QPushButton#toolbarPinButton:checked {{ background: #28483e; border: 1px solid #60b695; }}
        QPushButton#history {{ background: #242d39; border: 1px solid #3b485a; color: #d6e2f6; padding: 4px 6px; }}
        QPushButton#history:hover {{ background: #334153; border-color: #637b9a; }}
        QPushButton#deleteTool {{ background: #252c38; border: 1px solid #344052; color: #ef4444; padding: 4px 6px; }}
        QPushButton#deleteTool:hover:enabled {{ background: #303949; border-color: #536681; color: #ef4444; }}
        QPushButton#deleteTool:disabled {{ color: #b44a50; background: #202630; border-color: #2c3441; }}
        QPushButton#tabAdd {{ background: #242b37; color: #c0d2f2; border: 1px solid #354156; border-radius: 8px; padding: 1px; }}
        QPushButton#tabAdd:hover {{ background: #30415a; border-color: #5b7eaf; }}
        QFrame#vline {{ color: #3b4554; margin: 2px 3px; }}
        QStackedWidget#documentStack {{ background: #222731; border: 0; }}
        QFrame#documentSidebar {{ background: #1b2029; border-right: 1px solid #303846; }}
        QLabel#sideHeader {{ color: #8694a9; font-size: 8pt; letter-spacing: 1.2px; font-weight: 800; }}
        QWidget#sideTabs, QWidget#sidebarTabNav, QStackedWidget#sidebarTabStack {{ background:transparent; border:0; }}
        QPushButton#sideTabButton {{ background:#202630; color:#aebbd0; border:1px solid #354154; border-radius:7px; padding:6px 8px; font-size:8pt; font-weight:700; }}
        QPushButton#sideTabButton:checked {{ background:#2b3b57; color:#eef4ff; border-color:#5276b4; }}
        QPushButton#sideTabButton:hover {{ background:#252f3e; color:#ffffff; }}
        QListWidget#thumbnails, QTreeWidget#outline {{ background: #171b22; border: 0; outline: 0; }}
        QListWidget#thumbnails::item {{ padding: 5px; border: 1px solid transparent; border-radius: 7px; }}
        QListWidget#thumbnails::item:selected {{ background: #2b3b57; border-color: #5276b4; }}
        QListWidget#thumbnails::item:hover {{ background: #252c37; }}
        QTreeWidget#outline::item {{ padding: 5px; }}
        QTreeWidget#outline::item:selected {{ background: #2b3b57; border-radius: 4px; }}
        QScrollArea#readerScroll {{ background: #292e38; border: 0; }}
        QSpinBox#pageSpin {{ background: #141820; border: 1px solid #394352; border-radius: 6px; padding: 3px; }}
        QSpinBox::up-button, QSpinBox::down-button {{ width: 0; border: 0; }}
        QStatusBar#appStatus {{ background: #1a1f29; color: #93a0b3; border-top: 1px solid #303846; }}
        QLabel#contextHelpIcon {{ color:#8fb2f0; font-size:9pt; font-weight:800; padding:0 5px 0 8px; }}
        QLabel#contextHelpLabel {{ color:#9aa8bc; font-size:8pt; padding:2px 8px 2px 2px; }}
        QFrame#aiPanel {{ background: #1b202a; border-left: 1px solid #3a4557; }}
        QFrame#aiComposer {{ background: #202733; border: 1px solid #354256; border-radius: 12px; }}
        QScrollArea#aiPendingImages {{ background: transparent; border: 0; }}
        QFrame#aiPendingCard {{ background: #252f3d; border: 1px solid #3c4d65; border-radius: 8px; }}
        QLabel#aiPendingLabel {{ color: #bdc9dc; font-size: 7pt; }}
        QLabel#aiPendingPreview {{ background: #161c25; border: 1px solid #334257; border-radius: 5px; }}
        QPushButton#aiPendingRemove {{ background: #34303a; border: 1px solid #554451; border-radius: 5px; padding: 0; color: #f2cdd6; font-size: 10pt; }}
        QPushButton#aiPendingRemove:hover {{ background: #704050; border-color: #a86a7c; }}
        QPushButton#aiAddImage {{ background: #2a3444; border: 1px solid #455a78; border-radius: 8px; color: #d6e6ff; font-size: 19pt; font-weight: 400; padding: 0; }}
        QPushButton#aiAddImage:hover {{ background: #354b6b; border-color: #7196ce; }}
        QComboBox#aiChatSelector, QComboBox#translateTarget {{ background: #151a22; border: 1px solid #364357; border-radius: 7px; padding: 5px 7px; color: #e4ebf8; }}
        QPushButton#aiNewChat {{ background: #283549; border: 1px solid #415979; border-radius: 7px; padding: 5px 8px; color: #dce9ff; }}
        QPushButton#aiNewChat:hover {{ background: #344968; border-color: #6688b9; }}
        QComboBox#aiProviderSelector, QComboBox#aiModelSelector, QComboBox#aiLanguageSelector {{
            background:#151a22; border:1px solid #364357; border-radius:7px;
            padding:4px 7px; color:#e4ebf8; min-height:28px;
        }}
        QComboBox#aiProviderSelector:hover, QComboBox#aiModelSelector:hover, QComboBox#aiLanguageSelector:hover {{
            background:#1b2432; border-color:#526b8d; color:#e4ebf8;
        }}
        QComboBox#aiProviderSelector::drop-down, QComboBox#aiModelSelector::drop-down, QComboBox#aiLanguageSelector::drop-down {{
            subcontrol-origin:padding; subcontrol-position:top right; width:22px;
            border-left:1px solid #364357; border-top-right-radius:7px; border-bottom-right-radius:7px;
        }}
        QComboBox#aiProviderSelector::down-arrow, QComboBox#aiModelSelector::down-arrow {{
            image:url("{combo_chevron_up_path}"); width:12px; height:8px; border:0;
        }}
        QComboBox#aiProviderSelector QLineEdit, QComboBox#aiModelSelector QLineEdit, QComboBox#aiLanguageSelector QLineEdit {{
            background:transparent; border:0; color:#e4ebf8; selection-background-color:#3b5a8d;
        }}
        QComboBox#aiProviderSelector QAbstractItemView, QComboBox#aiModelSelector QAbstractItemView, QComboBox#aiLanguageSelector QAbstractItemView {{
            background:#151a22; color:#e4ebf8; border:1px solid #364357; outline:0;
            padding:4px; selection-background-color:#344a6c; selection-color:#ffffff;
        }}
        QComboBox#aiProviderSelector QAbstractItemView::item, QComboBox#aiModelSelector QAbstractItemView::item, QComboBox#aiLanguageSelector QAbstractItemView::item {{
            color:#e4ebf8; min-height:25px; padding:6px 9px; border-radius:4px;
        }}
        QComboBox#aiProviderSelector QAbstractItemView::item:hover,
        QComboBox#aiProviderSelector QAbstractItemView::item:selected,
        QComboBox#aiModelSelector QAbstractItemView::item:hover,
        QComboBox#aiModelSelector QAbstractItemView::item:selected {{
            background:#344a6c; color:#ffffff;
        }}
        QPushButton#aiPdfActions {{ background:#283750; border:1px solid #435d83; border-radius:7px; padding:5px 8px; color:#dfebff; }}
        QPushButton#aiPdfActions:hover {{ background:#334a6c; border-color:#6587b8; }}
        QPushButton#aiFocusMode {{ background:#252f3e; border:1px solid #3d506a; border-radius:7px; padding:3px; }}
        QPushButton#aiFocusMode:hover {{ background:#33465f; border-color:#6b8ebd; }}
        QPushButton#aiRegionButton {{ background:#24314a; border:1px solid #486795; border-radius:7px; padding:4px 7px; color:#dce8ff; }}
        QPushButton#aiRegionButton:hover {{ background:#304668; border-color:#779bd5; }}
        QPushButton#aiClearAttachments {{ background:#282e3a; border:1px solid #3d4655; border-radius:7px; padding:4px 7px; color:#aab7ca; }}
        QPushButton#aiClearAttachments:hover {{ background:#3c2d37; border-color:#895a6c; color:#f3c7d3; }}
        QLabel#aiAttachmentThumb {{ background:#18202b; border:1px solid #4a5f7c; border-radius:7px; padding:2px; }}
        QLabel#aiAttachmentMore {{ background:#35465e; border:1px solid #506c93; border-radius:7px; color:#e9f1ff; font-weight:bold; }}
        QFrame#teachBoard {{ background:#1a222e; border-left:1px solid #3d4d63; }}
        QLabel#teachBoardTitle {{ color:#96b8ff; font-weight:800; letter-spacing:1px; }}
        QLabel#teachBoardStep {{ color:#f3cc77; background:#332c20; border:1px solid #655333; border-radius:7px; padding:4px 7px; }}
        QLabel#teachBoardLesson {{ color:#eff4ff; font-size:10pt; font-weight:800; }}
        QLabel#teachBoardSpoken, QLabel#teachBoardFooter {{ color:#aab8cc; font-size:8pt; }}
        QTextBrowser#teachBoardText {{ background:#121923; color:#e4ebf7; border:1px solid #334359; border-radius:9px; padding:10px; }}
        QPushButton#primary:disabled {{ background:#334052; color:#91a0b4; border:1px solid #46556a; }}
        QPushButton#aiStop {{ background:#6e3742; border:1px solid #a85b6c; color:white; border-radius:7px; padding:5px 9px; }}
        QPushButton#aiStop:hover {{ background:#854655; }}
        QFrame#translationCard {{ background:#1d2430; border:1px solid #3d4d63; border-radius:14px; }}
        QLabel#translationTitle {{ color:#f1f5ff; font-size:11pt; font-weight:800; }}
        QLabel#translationMuted {{ color:#96a6bc; font-size:8pt; }}
        QFrame#translationSource {{ background:#202b39; border:1px solid #334861; border-radius:10px; }}
        QLabel#translationPreview {{ background:#131923; border:1px solid #354257; border-radius:7px; }}
        QLabel#translationSection {{ color:#8fabc9; font-size:8pt; font-weight:800; letter-spacing:1px; }}
        QComboBox#translationTarget {{ background:#151a22; border:1px solid #364357; border-radius:7px; padding:5px 7px; color:#e4ebf8; }}
        QTextBrowser#translationResult {{ background:#151a22; color:#e8effa; border:1px solid #303d50; border-radius:9px; padding:10px; font-size:13pt; selection-background-color:#3b5a8d; }}
        QPushButton#translationPrimary {{ background:#32836c; border:1px solid #55a98c; border-radius:8px; padding:6px 11px; color:white; font-weight:750; }}
        QPushButton#translationPrimary:hover {{ background:#3c9a7d; }}
        QPushButton#translationPrimary:disabled {{ color:#718a85; background:#283b38; border-color:#38544d; }}
        QPushButton#translationQuiet {{ background:#242d39; border:1px solid #3b485a; border-radius:7px; padding:4px 8px; color:#d6e2f6; }}
        QPushButton#translationClose {{ background:#2a303b; border:1px solid #3d4655; border-radius:8px; font-size:14pt; }}
        QPushButton#translationClose:hover {{ background:#583a44; border-color:#986575; }}
        QLabel#aiTitle {{ color: #f1f5ff; font-size: 10pt; font-weight: 800; }}
        QLabel#aiMuted, QLabel#aiBusyLabel {{ color: #8f9db2; font-size: 7.5pt; }}
        QLabel#aiContextLabel {{ color: #b7c6dd; background: #202b3b; border: 1px solid #33445d; border-radius: 7px; padding: 7px; font-size: 7.5pt; }}
        QLabel#aiModelLabel {{ color: #8798b2; font-size: 7pt; }}
        QLabel#aiSectionTitle {{ color: #8795aa; font-size: 7pt; letter-spacing: 1px; font-weight: 800; padding-top: 2px; }}
        QPushButton#aiQuickAction {{ text-align: left; background: #232b38; border: 1px solid #34445a; border-radius: 7px; padding: 6px 7px; min-height: 27px; font-size: 7.5pt; }}
        QPushButton#aiQuickAction:hover {{ background: #2d3b50; border-color: #5a76a1; }}
        QPushButton#aiSelectRegion {{ background: #24314a; border: 1px solid #486795; color: #dce8ff; text-align: center; padding: 7px; }}
        QPushButton#aiSelectRegion:hover {{ background: #304668; border-color: #779bd5; }}
        QScrollArea#aiTranscript {{ background: #141820; border: 1px solid #303b4c; border-radius: 9px; }}
        QWidget#aiTranscriptBody {{ background: #141820; }}
        QFrame#aiAssistantCard {{ background: #242b37; border: 1px solid #344154; border-radius: 12px; }}
        QFrame#aiUserCard {{ background: #2b4164; border: 1px solid #3f5c87; border-radius: 12px; }}
        QFrame#aiPendingSelectedText {{ background: rgba(91,140,220,35); border: 1px solid #49658b; border-radius: 8px; }}
        QLabel#aiPendingSelectedTitle {{ color: #a9c6f5; font-size: 7pt; font-weight: 800; }}
        QLabel#aiPendingSelectedPreview {{ color: #d8e3f5; font-size: 8pt; }}
        QLabel#aiPendingQuoteMark {{ color: #9ebcff; font-size: 20pt; font-weight: 800; }}
        QLabel#aiBubbleRole {{ color: #9ebcff; font-size: 7pt; font-weight: 800; letter-spacing: 0.6px; }}
        QLabel#aiBubbleTime {{ color: #8997ad; font-size: 6.5pt; }}
        QTextBrowser#aiBubbleContent {{ background: transparent; border: 0; padding: 0; color: #e2e9f5; font-size: 11pt; selection-background-color: #3b5a8d; }}
        QTextEdit#aiPrompt {{ background: #151a22; border: 1px solid #3a4658; border-radius: 8px; padding: 7px; color: #eef3fd; font-size: 11pt; selection-background-color: #3b5a8d; }}
        QTextEdit#aiPrompt:focus {{ border-color: #638de0; }}
        QPushButton#aiStop {{ background: #a63b46; border: 1px solid #d45b65; color: white; border-radius: 8px; padding: 6px 10px; font-weight: 750; }}
        QPushButton#aiStop:hover {{ background: #c74754; }}
        QPushButton#aiStop:disabled {{ background: #51343a; border-color: #67414a; color: #b8a3a7; }}
        QPushButton#aiSend {{ background: #4f7fe8; border: 1px solid #6792f3; color: white; border-radius: 8px; padding: 6px 8px; font-weight: 750; }}
        QPushButton#aiSend:hover {{ background: #6491f5; }}
        QPushButton#aiSend:disabled {{ background: #303b50; border-color: #3c4a63; color: #7988a1; }}
        QPushButton#aiVoice {{ background:#252f3e; border:1px solid #40516a; color:#dce7f8; border-radius:7px; padding:6px 10px; font-weight:650; }}
        QPushButton#aiVoice[recording="true"] {{ background:#405878; border:1px solid #6686b2; color:#ffffff; font-weight:750; }}
        QPushButton#aiVoice[transcribing="true"] {{ background:#414957; border:1px solid #687487; color:#f0f3f8; }}
        QPushButton#aiReadAnswer {{ background:#252f3e; border:1px solid #40516a; color:#dce7f8; }}
        QPushButton#aiStopAudio {{ background:#2b3442; border:1px solid #45556d; color:#dfe9f8; }}
        QPushButton#aiStopAudio:hover {{ background:#34445a; }}
        QFrame#aiSettingsGroup {{ background: #252e3a; border: 1px solid #364457; border-radius: 8px; }}
        QDialog {{ background: #202630; }}
        QLabel#dialogHeading {{ font-size: 10pt; font-weight: 800; letter-spacing: 1px; color: #e8efff; }}
        QLabel#dialogHint {{ color: #9ca9bc; }}
        QLabel#dialogLabel {{ color: #dce4f1; }}
        QPushButton#presetButton {{ padding: 5px 7px; background: #2a323e; }}
        QCheckBox {{ spacing: 7px; }}
        QCheckBox::indicator {{ width: 15px; height: 15px; }}
        QCheckBox::indicator:unchecked {{ background: #303846; border: 1px solid #576477; border-radius: 4px; }}
        QCheckBox::indicator:checked {{ background: {ui_accent}; border: 1px solid {ui_accent}; border-radius: 4px; image: url("{check_icon_path}"); }}
        QScrollBar:vertical {{ background: #202630; width: 12px; margin: 2px; }}
        QScrollBar::handle:vertical {{ background: #4b5667; border-radius: 5px; min-height: 30px; }}
        QScrollBar::add-line:vertical, QScrollBar::sub-line:vertical {{ height: 0; }}
        QScrollBar:horizontal {{ background: #202630; height: 12px; margin: 2px; }}
        QScrollBar::handle:horizontal {{ background: #4b5667; border-radius: 5px; min-width: 30px; }}
        QScrollBar::add-line:horizontal, QScrollBar::sub-line:horizontal {{ width: 0; }}
        QFrame#homeSidebar {{ background: #111722; border-right: 1px solid #303b4b; }}
        QLabel#homeSideTitle {{ color: #eef3ff; font-size: 13pt; font-weight: 850; padding: 2px 8px 5px 8px; }}
        QLabel#homeSideCaption {{ color: #73839b; font-size: 7.5pt; font-weight: 800; letter-spacing: 1px; padding: 4px 9px; }}
        QLabel#homeSideFooter {{ color: #72829a; padding: 8px 7px; font-size: 7pt; font-weight: 550; line-height: 1.25; }}
        QPushButton#homeNav, QPushButton#homeNavActive, QPushButton#homeSettingsNav {{ text-align: left; padding: 10px 11px; border-radius: 8px; min-height: 20px; font-size: 9pt; font-weight: 700; }}
        QPushButton#homeNav, QPushButton#homeSettingsNav {{ color: #b6c2d5; background: transparent; border: 1px solid transparent; }}
        QPushButton#homeNav:hover, QPushButton#homeSettingsNav:hover {{ background: #202b3b; color: #f2f6ff; }}
        QPushButton#homeSettingsNav, QPushButton#homeNav {{ min-height: 42px; padding: 6px 10px; border-radius: 7px; border: 1px solid {theme_tokens['border']}; }}
        QPushButton#homeSettingsNav {{ font-size: 10.5pt; font-weight: 800; text-align: center; }}
        QPushButton#homeNav {{ font-size: 9pt; font-weight: 750; }}
        QPushButton#aiVoice, QPushButton#aiReadAnswer, QPushButton#aiStopAudio {{ font-weight: 700; padding: 7px 12px; }}
        QPushButton#homeNavActive {{ color: #ffffff; background: #2c4773; border: 1px solid #4d72ad; font-weight: 750; }}
        QLineEdit#homeBrowserPath {{ font-size: 9pt; font-weight: 700; }}
        QTreeView#homeBrowserTree {{ font-size: 8.5pt; font-weight: 650; }}
        QTreeView#homeBrowserTree::item {{ font-weight: 650; }}
        QLabel#filesHomeSubtitle, QLabel#filesHeroHint, QLabel#filesSectionHint, QLabel#filesEmptyHint {{ font-weight: 600; }}
        QLabel#filesSessionSummary {{ font-weight: 700; }}
        QLabel#recentFileName {{ font-weight: 800; }}
        QLabel#recentFilePath, QLabel#recentFileWhen {{ font-weight: 600; }}
        QPushButton#filesPrimaryButton, QPushButton#filesSecondaryButton {{ font-size: 9pt; font-weight: 750; }}
        QPushButton[searchActive="true"] {{ background: #244b43; border: 1px solid #51b69c; color: #d7fff1; }}
        QToolButton#chatSelectionAsk {{ color: white; background: #3d70cf; border: 1px solid #79a5f5; border-radius: 7px; padding: 3px 10px; font-weight: 700; }}
        QToolButton#chatSelectionAsk:hover {{ background: #5688e6; }}
        """
        # Theme overrides are generated only from named tokens. This keeps the
        # component palette consistent and makes new themes additive instead of
        # requiring hand-edits to dozens of widget-specific colors.
        t = theme_tokens
        theme_stylesheet = f"""
        QWidget {{ color:{t['text']}; }}
        QMainWindow, QWidget#mainRoot, QStackedWidget#documentStack, QWidget#filesHome,
        QWidget#filesHomeContent {{ background:{t['window']}; color:{t['text']}; }}
        QScrollArea#homeBrowserBreadcrumbScroll {{ background:transparent; border:0; }}
        QWidget#homeBrowserBreadcrumbHost {{ background:transparent; }}
        QToolButton#homeBrowserCrumb {{ color:{t['text']}; background:{t['panel']}; border:1px solid {t['border']}; border-radius:5px; padding:2px 7px; min-height:21px; font-size:7.5pt; font-weight:650; }}
        QToolButton#homeBrowserCrumb:hover {{ background:{t['raised']}; border-color:{t['accent']}; }}
        QToolButton#homeBrowserCrumb[breadcrumbCurrent="true"] {{ background:{t['selection']}; color:{t['selection_text']}; border-color:{t['accent']}; }}
        QLabel#homeBrowserCrumbSeparator {{ color:{t['muted']}; font-size:11pt; font-weight:700; padding:0 1px; }}
        QScrollArea#homeBrowserBreadcrumbScroll QScrollBar:horizontal {{ height:7px; background:{t['panel']}; margin:0; }}
        QScrollArea#homeBrowserBreadcrumbScroll QScrollBar::handle:horizontal {{ background:{t['muted']}; border-radius:3px; min-width:24px; }}
        QScrollArea#homeBrowserBreadcrumbScroll QScrollBar::add-line:horizontal,
        QScrollArea#homeBrowserBreadcrumbScroll QScrollBar::sub-line:horizontal {{ width:0; }}
        QTreeView#homeBrowserTree QScrollBar:horizontal {{ height:9px; background:{t['panel']}; margin:0; }}
        QTreeView#homeBrowserTree QScrollBar::handle:horizontal {{ background:{t['scrollbar']}; border-radius:4px; min-width:30px; }}
        QTreeView#homeBrowserTree QScrollBar::add-line:horizontal,
        QTreeView#homeBrowserTree QScrollBar::sub-line:horizontal {{ width:0; }}
        QFrame#tabStrip, QFrame#topbar {{ background:{t['panel']}; border-color:{t['border']}; }}
        QFrame#toolbarGroup, QFrame#annotationGroup, QFrame#aiComposer,
        QFrame#filesHero, QFrame#homeFileBrowser, QFrame#recentFileRow,
        QFrame#aiSettingsGroup, QFrame#aiAssistantCard, QFrame#translationCard {{
            background:{t['panel_alt']}; color:{t['text']}; border-color:{t['border']}; }}
        QFrame#documentSidebar, QFrame#aiPanel, QFrame#teachBoard, QFrame#homeSidebar {{
            background:{t['panel']}; color:{t['text']}; border-color:{t['border']}; }}
        QSplitter#homePageSplitter {{ background:transparent; border:0; }}
        QSplitter#homePageSplitter::handle:horizontal {{
            background:{t['border']}; width:7px; margin:0px;
        }}
        QSplitter#homePageSplitter::handle:horizontal:hover,
        QSplitter#homePageSplitter::handle:horizontal:pressed {{ background:{t['accent']}; }}
        QStatusBar#appStatus {{ background:{t['status']}; color:{t['muted']}; border-top:1px solid {t['border']}; }}
        QLabel#contextHelpIcon {{ color:{t['accent']}; }}
        QLabel#contextHelpLabel {{ color:{t['muted']}; }}
        QLabel#brandTitle, QLabel#filesHomeTitle, QLabel#filesHeroTitle,
        QLabel#filesSectionTitle, QLabel#homeSideTitle, QLabel#aiTitle,
        QLabel#teachBoardLesson, QLabel#translationTitle {{ color:{t['text']}; }}
        /* Settings is intentionally a little larger; both labels remain bold. */
        /* Settings label: slightly smaller than the previous 12pt size. */
        QPushButton#homeSettingsNav {{ font-size:10.5pt; font-weight:800; text-align:center; }}
        QPushButton#homeNav {{ font-size:9pt; font-weight:750; }}
        QLabel#filesHomeSubtitle, QLabel#filesHeroHint, QLabel#filesSectionHint,
        QLabel#filesEmptyHint, QLabel#recentFilePath, QLabel#recentFileWhen,
        QLabel#dialogHint, QLabel#homeSideFooter, QLabel#aiMuted {{ color:{t['muted']}; }}
        QPushButton#homeNav, QPushButton#homeSettingsNav {{
            background:{t['panel_alt']}; color:{t['text']}; border:1px solid {t['border']};
            border-radius:7px; padding:6px 10px; min-height:36px;
        }}
        QPushButton#homeNav {{ font-size:9pt; font-weight:750; }}
        QPushButton#homeSettingsNav {{ font-size:10.5pt; font-weight:800; text-align:center; }}
        QPushButton#homeNav:hover, QPushButton#homeSettingsNav:hover {{
            background:{t['hover']}; border-color:{t['border_strong']};
        }}
        QPushButton#homeNav:pressed, QPushButton#homeSettingsNav:pressed {{ background:{t['pressed']}; }}
        QPushButton, QToolButton {{ background:{t['raised']}; color:{t['text']}; border-color:{t['border']}; }}
        QPushButton:hover, QToolButton:hover {{ background:{t['hover']}; border-color:{t['border_strong']}; }}
        QPushButton:pressed, QToolButton:pressed {{ background:{t['pressed']}; }}
        QPushButton:disabled, QToolButton:disabled {{ color:{t['muted']}; background:{t['panel_alt']}; border-color:{t['border']}; }}
        QPushButton#primary, QPushButton#filesPrimaryButton, QPushButton#aiSend {{
            background:{t['accent']}; color:#ffffff; border-color:{t['accent']}; }}
        QPushButton#primary:hover, QPushButton#filesPrimaryButton:hover, QPushButton#aiSend:hover {{
            background:{t['accent_hover']}; border-color:{t['accent_hover']}; }}
        QPushButton#aiVoice, QPushButton#aiReadAnswer, QPushButton#aiStopAudio,
        QPushButton#aiPdfActions, QPushButton#aiNewChat, QPushButton#aiFocusMode,
        QPushButton#aiClearAttachments, QPushButton#aiChatSearch {{
            background:{t['raised']}; color:{t['text']}; border-color:{t['border']}; }}
        QPushButton#aiAddImage {{ background:{t['raised']}; color:{t['text']};
            border:1px solid {t['border']}; border-radius:8px; font-size:19pt; padding:0; }}
        QPushButton#aiAddImage:hover {{ background:{t['hover']}; color:{t['text']};
            border-color:{t['accent']}; }}
        QPushButton#aiAddImage:pressed {{ background:{t['pressed']}; color:{t['text']};
            border-color:{t['accent']}; }}
        QPushButton#aiAddImage:disabled {{ background:{t['panel_alt']}; color:{t['muted']};
            border-color:{t['border']}; }}
        QLineEdit, QTextEdit, QPlainTextEdit, QTextBrowser, QComboBox, QSpinBox,
        QTreeView#homeBrowserTree, QListWidget#thumbnails, QTreeWidget#outline {{
            background:{t['input']}; color:{t['text']}; border-color:{t['border']};
            selection-background-color:{t['selection']}; selection-color:{t['selection_text']}; }}
        QFrame#aiTranscript, QWidget#aiTranscriptBody, QTextBrowser#aiBubbleContent,
        QTextBrowser#teachBoardText, QTextBrowser#translationResult {{
            background:{t['input']}; color:{t['text']}; border-color:{t['border']}; }}
        QFrame#aiUserCard {{ background:{t['selection']}; border-color:{t['border_strong']}; }}
        QFrame#aiSelectedPassageCard {{ background:{t['panel_alt']}; border:1px solid {t['border']}; border-radius:7px; }}
        QLabel#aiSelectedPassageTitle {{ color:{t['accent']}; font-size:8pt; font-weight:800; }}
        QLabel#aiSelectedPassagePreview {{ color:{t['text']}; background:transparent; padding:2px 0; }}
        QToolButton#aiSelectedPassageJump {{ color:{t['accent']}; background:{t['raised']}; border:1px solid {t['border']}; border-radius:5px; padding:3px 7px; font-weight:650; }}
        QToolButton#aiSelectedPassageJump:hover {{ background:{t['hover']}; border-color:{t['accent']}; }}
        QFrame#aiPendingCard, QFrame#aiPendingSelectedText, QFrame#translationSource {{
            background:{t['panel_alt']}; border-color:{t['border']}; }}
        QTabBar#documentTabBar::tab {{ background:{t['panel_alt']}; color:{t['muted']}; border-color:{t['border']}; }}
        QTabBar#documentTabBar::tab:selected {{ background:{t['raised']}; color:{t['text']}; border-color:{t['border_strong']}; }}
        QTabBar#documentTabBar::tab:hover {{ background:{t['hover']}; color:{t['text']}; }}
        QPushButton#sideTabButton {{ background:{t['panel_alt']}; color:{t['muted']}; border:1px solid {t['border']}; border-radius:7px; }}
        QPushButton#sideTabButton:checked {{
            background:{t['panel'] if current_ui_theme == 'midnight' else t['selection']};
            color:{t['text']}; border:1px solid {t['accent']}; border-bottom:1px solid {t['accent']};
        }}
        QPushButton#sideTabButton:checked:hover {{
            background:{t['panel'] if current_ui_theme == 'midnight' else t['selection']};
            color:{t['text']}; border:1px solid {t['accent']}; border-bottom:1px solid {t['accent']};
        }}
        /* Sidebar visibility is a functional toggle, not an active tool state.
           Keep its appearance identical to a normal, idle toolbar action even
           while the sidebar is open; only normal hover/press feedback remains. */
        QPushButton#sidebarToggleButton:checked {{
            background:{t['raised']}; color:{t['text']}; border:1px solid {t['border']};
            font-weight:550;
        }}
        QPushButton#sidebarToggleButton:checked:hover {{
            background:{t['hover']}; color:{t['text']}; border:1px solid {t['border_strong']};
            font-weight:550;
        }}
        QPushButton#sidebarToggleButton:checked:pressed {{
            background:{t['pressed']}; color:{t['text']}; border:1px solid {t['border']};
            font-weight:550;
        }}
        QListWidget#thumbnails::item:selected, QTreeWidget#outline::item:selected,
        QTreeView#homeBrowserTree::item:selected {{ background:{t['selection']}; color:{t['selection_text']}; }}
        QScrollArea#readerScroll {{ background:{t['raised']}; }}
        QScrollBar:vertical, QScrollBar:horizontal {{ background:{t['panel']}; }}
        QScrollBar::handle:vertical, QScrollBar::handle:horizontal {{ background:{t['scrollbar']}; }}
        QToolTip {{ background:{t['panel']}; color:{t['text']}; border:1px solid {t['border_strong']}; padding:5px 7px; }}
        QCheckBox {{ color:{t['text']}; }}
        QCheckBox::indicator:unchecked {{ background:{t['input']}; border:1px solid {t['border_strong']}; }}
        QCheckBox::indicator:checked {{ background:{t['accent']}; border:1px solid {t['accent']}; }}

        /* Chat selectors use the same theme tokens as the rest of Engo. */
        QComboBox#aiChatSelector, QComboBox#aiProviderSelector, QComboBox#aiModelSelector {{
            background:{t['input']}; color:{t['text']}; border:1px solid {t['border']};
            border-radius:7px; selection-background-color:{t['selection']};
            selection-color:{t['selection_text']};
        }}
        QComboBox#aiChatSelector:hover, QComboBox#aiProviderSelector:hover,
        QComboBox#aiModelSelector:hover {{ background:{t['hover']}; color:{t['text']}; border-color:{t['border_strong']}; }}
        QComboBox#aiChatSelector::drop-down, QComboBox#aiProviderSelector::drop-down,
        QComboBox#aiModelSelector::drop-down {{ background:{t['raised']}; border-left:1px solid {t['border']}; }}
        QComboBox#aiChatSelector QAbstractItemView,
        QComboBox#aiProviderSelector QAbstractItemView,
        QComboBox#aiModelSelector QAbstractItemView {{ background:{t['panel']}; color:{t['text']};
            border:1px solid {t['border']}; selection-background-color:{t['selection']};
            selection-color:{t['selection_text']}; outline:0; }}
        QPushButton#aiAddImage {{ background:{t['raised']}; color:{t['text']};
            border:1px solid {t['border']}; border-radius:8px; }}
        QPushButton#aiAddImage:hover {{ background:{t['hover']}; color:{t['text']}; border-color:{t['accent']}; }}
        QPushButton#aiAddImage:pressed {{ background:{t['pressed']}; color:{t['text']}; border-color:{t['accent']}; }}
        QPushButton#aiAddImage:disabled {{ background:{t['panel_alt']}; color:{t['muted']}; border-color:{t['border']}; }}
        /* ID-specific toolbar controls must override legacy dark-first QSS above. */
        QPushButton#homeTopButton, QPushButton#tabAdd,
        QPushButton#filesSecondaryButton, QToolButton#saveSplitButton,
        QToolButton#rotatePageAction, QToolButton#selectTool:!checked,
        QToolButton#tagTool:!checked {{ background:{t['raised']}; color:{t['text']};
            border-color:{t['border']}; }}
        QPushButton#homeTopButton:hover, QPushButton#tabAdd:hover,
        QPushButton#filesSecondaryButton:hover, QToolButton#saveSplitButton:hover,
        QToolButton#rotatePageAction:hover, QToolButton#selectTool:!checked:hover,
        QToolButton#tagTool:!checked:hover {{ background:{t['hover']}; color:{t['text']};
            border-color:{t['border_strong']}; }}
        QToolButton#selectTool:checked, QToolButton#tagTool:checked {{
            background:{t['selection']}; color:{t['selection_text']}; border-color:{t['border_strong']}; }}
        QToolButton#saveSplitButton::menu-button, QToolButton#rotatePageAction::menu-button,
        QToolButton#selectTool::menu-button, QToolButton#tagTool::menu-button {{
            background:{t['raised']}; border-left:1px solid {t['border']}; }}
        QPushButton#aiSend:disabled, QPushButton#aiSend:disabled:hover {{
            background:{t['panel_alt']}; color:{t['muted']}; border-color:{t['border']}; }}
        QComboBox {{ background:{t['input']}; color:{t['text']}; border-color:{t['border']};
            selection-background-color:{t['selection']}; selection-color:{t['selection_text']}; }}
        QComboBox:hover {{ background:{t['hover']}; border-color:{t['border_strong']}; }}
        QComboBox::drop-down {{ subcontrol-origin:padding; subcontrol-position:top right;
            width:25px; background:{t['raised']}; border-left:1px solid {t['border']}; }}
        QComboBox::down-arrow {{ image:url("{combo_chevron_path}"); width:12px; height:8px; border:0; }}
        QComboBox QAbstractItemView {{ background:{t['panel']}; color:{t['text']};
            border:1px solid {t['border']}; selection-background-color:{t['selection']};
            selection-color:{t['selection_text']}; outline:0; }}
        """
        if current_ui_theme != "light":
            theme_stylesheet += f"""
                QPushButton#homeTopButton, QPushButton#filesPrimaryButton {{
                    background:{t['raised']}; color:{t['text']}; border-color:{t['border']}; }}
                QPushButton#homeTopButton:hover, QPushButton#filesPrimaryButton:hover {{
                    background:{t['hover']}; border-color:{t['border_strong']}; }}
                QPushButton#homeTopButton:pressed, QPushButton#filesPrimaryButton:pressed {{
                    background:{t['pressed']}; }}
            """
            if current_ui_theme == "dark":
                theme_stylesheet += f"""
                    QPushButton#aiSend:enabled {{ background:{t['raised']}; color:{t['text']}; border-color:{t['border']}; }}
                    QPushButton#aiSend:enabled:hover {{ background:{t['hover']}; border-color:{t['border_strong']}; }}
                    QPushButton#aiSend:enabled:pressed {{ background:{t['pressed']}; }}
                """
        else:
            theme_stylesheet += f"""
                QPushButton#homeTopButton, QPushButton#filesPrimaryButton {{
                    background:{t['accent']}; color:#ffffff; border-color:{t['accent']}; }}
                QPushButton#homeTopButton:hover, QPushButton#filesPrimaryButton:hover {{
                    background:{t['accent_hover']}; border-color:{t['accent_hover']}; }}
            """
        # Home screen buttons are 70% of their previous vertical size.
        # Widths remain unchanged: sidebar buttons still fill their column, while
        # the two hero actions keep their natural text-dependent widths.
        theme_stylesheet += """
        QPushButton#homeNav[homeActionHeight="true"],
        QPushButton#homeSettingsNav[homeActionHeight="true"] {
            min-height: 30px; max-height: 30px;
            padding-top: 2px; padding-bottom: 2px;
        }
        QPushButton#filesPrimaryButton[homeActionHeight="true"],
        QPushButton#filesSecondaryButton[homeActionHeight="true"] {
            min-height: 31px; max-height: 31px;
            padding-top: 2px; padding-bottom: 2px;
        }
        QPushButton#filesSecondaryButton[recentFileAction="true"] {
            min-height: 27px; max-height: 27px;
            padding-top: 0px; padding-bottom: 0px;
        }
        """
        base_stylesheet += "\n" + theme_stylesheet
        self._base_app_stylesheet = base_stylesheet
        self.setStyleSheet(base_stylesheet)
        # Force a consistent blue selection color across text controls and item views;
        # do not inherit the Windows accent (which may be purple).
        ui_theme_name = normalize_ui_theme(self.settings.value("ui_theme", "dark", type=str))
        selection_bg = theme_tokens["selection"]
        selection_fg = theme_tokens["selection_text"]
        app = QApplication.instance()
        app_palette = engo_theme_qpalette(app.palette(), ui_theme_name) if app is not None else engo_theme_qpalette(self.palette(), ui_theme_name)
        if app is not None:
            app.setPalette(app_palette)
        self.setPalette(app_palette)
        self.setStyleSheet(self.styleSheet() + f"\nQLineEdit, QTextEdit, QPlainTextEdit, QTextBrowser, QComboBox QLineEdit {{ selection-background-color:{selection_bg}; selection-color:{selection_fg}; }}\nQListWidget#thumbnails::item:selected, QTreeWidget#outline::item:selected {{ background:{selection_bg}; color:{selection_fg}; border:1px solid #5b8fd4; }}\n")
        if hasattr(self, "ai_panel"):
            try:
                chat_combo = self.ai_panel.chat_combo
                delegate = chat_combo.itemDelegate()
                if isinstance(delegate, AIChatConversationDelegate):
                    delegate.settings = self.settings
                chat_combo.update()
                chat_combo.view().viewport().update()
                chat_combo.view().setPalette(app_palette if app is not None else chat_combo.palette())
            except (AttributeError, RuntimeError):
                pass
        # Keep functional icons legible in the Light theme; do not leave pale glyphs
        # designed for dark backgrounds on white/gray controls.
        current_theme = normalize_ui_theme(self.settings.value("ui_theme", "dark", type=str))
        _current_tokens = engo_ui_theme_tokens(current_theme)
        icon_color = "#33445b" if current_theme == "light" else _current_tokens["text"]
        for widget_class in (QPushButton, QToolButton):
            for icon_widget in self.findChildren(widget_class):
                icon_name = icon_widget.property("engoIconName")
                if icon_name:
                    icon_widget.setIcon(make_icon(str(icon_name), icon_color, 18))
        # The document sidebar's Pages/Contents glyphs need a stronger contrast
        # than the pale dark-theme defaults when the Light theme is active.
        sidebar_icon_color = _current_tokens["text"]
        for sidebar_tabs in self.findChildren(ResponsiveSidebarTabs):
            try:
                sidebar_tabs.setIconColor(sidebar_icon_color)
            except RuntimeError:
                pass
        # Refresh the full-page gallery's close glyph and its overlay palette after
        # theme changes, including when the overview is already visible.
        for document_tab in self.findChildren(DocumentTab):
            try:
                if hasattr(document_tab, "_page_overview_overlay"):
                    document_tab._style_page_overview()
            except (RuntimeError, AttributeError):
                pass
        # The Home glyph is a fixed brand/navigation mark, intentionally white in all themes.
        if hasattr(self, "open_btn"):
            self.open_btn.setIcon(make_icon("home", "#ffffff", 18))
            self.open_btn.setIconSize(QSize(18, 18))
        if hasattr(self, "delete_btn"):
            # Keep the trash glyph semantically red in every app theme; the button
            # surface and border are theme-driven by the stylesheet below.
            self.delete_btn.setIcon(make_icon("delete", "#ef4444", 18))
        if hasattr(self, "select_tool_btn"):
            self._refresh_selector_tool_button()
        if hasattr(self, "save_btn"):
            self.save_btn.setIcon(make_icon("save", icon_color, 18))
        if hasattr(self, "rotate_page_btn"):
            self.rotate_page_btn.setIcon(make_icon("rotate_cw", icon_color, 18))
        if hasattr(self, "tag_tool_btn"):
            self.tag_tool_btn.setIcon(make_icon("tag", "#315f9e" if current_theme == "light" else ("#79a8ff" if current_theme == "midnight" else "#d5d5d5"), 18))
        if hasattr(self, "home_settings_btn"):
            home_icon_color = (
                "#40516a" if current_theme == "light" else
                ("#9fc0ff" if current_theme == "midnight" else "#c4d0e2")
            )
            self.home_settings_btn.setIcon(make_icon("settings", home_icon_color, 18))
            self.home_settings_btn.setIconSize(QSize(18, 18))
        # AI chat header icons were originally assigned pale dark-theme colors
        # at widget construction. Refresh them explicitly after every theme change.
        if hasattr(self, "ai_panel"):
            try:
                chat = self.ai_panel
                chat_icon_color = (
                    "#315d9d" if current_theme == "light"
                    else ("#9fc0ff" if current_theme == "midnight" else "#e1e8f2")
                )
                if hasattr(chat, "chat_header_icon"):
                    chat.chat_header_icon.setPixmap(make_icon("ai", chat_icon_color, 20).pixmap(QSize(22, 22)))
                if hasattr(chat, "pdf_actions_btn"):
                    chat.pdf_actions_btn.setIcon(make_icon("summarize", chat_icon_color, 15))
                if hasattr(chat, "export_btn"):
                    chat.export_btn.setIcon(make_icon("export", chat_icon_color, 15))
                if hasattr(chat, "focus_mode_btn"):
                    chat.focus_mode_btn.setIcon(make_icon("fullscreen", chat_icon_color, 16))
                if hasattr(chat, "chat_search_btn"):
                    chat.chat_search_btn.setIcon(make_icon("search", chat_icon_color, 15))
                if hasattr(chat, "voice_btn"):
                    voice_color = "#ffffff" if chat.voice_btn.property("recording") else chat_icon_color
                    chat.voice_btn.setIcon(make_icon("mic", voice_color, 16))
                    chat.voice_btn.setIconSize(QSize(16, 16))
                if hasattr(chat, "read_answer_btn"):
                    chat.read_answer_btn.setIcon(make_icon("volume", chat_icon_color, 16))
                    chat.read_answer_btn.setIconSize(QSize(16, 16))
                if hasattr(chat, "stop_audio_btn"):
                    chat.stop_audio_btn.setIcon(make_icon("stop", chat_icon_color, 15))
                    chat.stop_audio_btn.setIconSize(QSize(15, 15))
            except (AttributeError, RuntimeError):
                pass

        # Re-apply the shared popup system after every theme refresh, including
        # dialogs that were already open when the user switched Light/Dark/Midnight.
        for popup_dialog in self.findChildren(QDialog):
            try:
                _engo_apply_dialog_consistency(popup_dialog, current_theme)
            except RuntimeError:
                pass
        # Preserve the standard Windows caption buttons and recolor their real
        # title-bar surface to match this same palette. Retry after the window is shown.
        self._apply_windows_titlebar_theme(theme_tokens)
        QTimer.singleShot(80, lambda colors=dict(theme_tokens): self._apply_windows_titlebar_theme(colors))


    def _sync_toolbar_pin_button(self):
        if not hasattr(self, "toolbar_pin_btn"):
            return
        pinned = bool(getattr(self, "_toolbar_pinned", True))
        self.toolbar_pin_btn.blockSignals(True)
        self.toolbar_pin_btn.setChecked(pinned)
        self.toolbar_pin_btn.setIcon(make_icon("pin" if pinned else "pin_off", "#33445b" if str(self.settings.value("ui_theme", "dark", type=str)).lower() == "light" else "#b6c9e6", 18))
        self.toolbar_pin_btn.setToolTip(
            "Unpin toolbar · it will auto-hide when the pointer leaves" if pinned
            else "Pin toolbar open · keep it visible"
        )
        self.toolbar_pin_btn.setAccessibleName("Unpin toolbar" if pinned else "Pin toolbar")
        self.toolbar_pin_btn.blockSignals(False)

    def _set_toolbar_pinned(self, pinned: bool):
        self._toolbar_pinned = bool(pinned)
        self._fullscreen_toolbar_pinned = self._toolbar_pinned
        self._toolbar_manually_hidden = not self._toolbar_pinned
        self.settings.setValue("toolbar_pinned", self._toolbar_pinned)
        self.settings.setValue("toolbar_visible", self._toolbar_pinned)
        self.settings.sync()
        if self._toolbar_pinned:
            self._fullscreen_toolbar_hide_timer.stop()
            self._animate_fullscreen_toolbar(True)
        else:
            self._fullscreen_toolbar_hide_timer.stop()
            QTimer.singleShot(0, self._schedule_toolbar_auto_hide)
        self._sync_toolbar_pin_button()
        self.show_status("Toolbar pinned" if self._toolbar_pinned else "Toolbar will auto-hide · move to its top edge to reveal")

    def _schedule_toolbar_auto_hide(self):
        if self._toolbar_pinned or self._presentation or not self.topbar.isVisible():
            return
        top_left = self.topbar.mapToGlobal(QPoint(0, 0))
        toolbar_rect = QRect(top_left, self.topbar.size()).adjusted(-2, -2, 2, 2)
        if toolbar_rect.contains(QCursor.pos()):
            self._fullscreen_toolbar_hide_timer.stop()
        elif not self._fullscreen_toolbar_hide_timer.isActive():
            self._fullscreen_toolbar_hide_timer.start()

    def toggle_toolbar_visibility(self, visible=None):
        # Ctrl+Shift+B now toggles the same pin state as the single toolbar pin.
        if visible is None:
            visible = not bool(getattr(self, "_toolbar_pinned", True))
        self._set_toolbar_pinned(bool(visible))

    def _schedule_toolbar_density_update(self, force=False):
        """Schedule the one-time startup pass or a user-resized width pass only."""
        initialized = bool(getattr(self, "_toolbar_density_initialized", False))
        user_resize = bool(getattr(self, "_toolbar_density_user_resize_pending", False))
        if getattr(self, "_live_tutor_toolbar_locked", False) and not user_resize:
            return
        if initialized and not (force or user_resize):
            return
        timer = getattr(self, "_toolbar_density_timer", None)
        if timer is not None:
            timer.start()
        else:
            QTimer.singleShot(0, lambda: self._apply_toolbar_density(force=force))

    def _apply_toolbar_density(self, force=False):
        """Choose toolbar density at startup or after a real user width resize.

        Once initialized, normal UI actions cannot reflow or collapse the toolbar.
        """
        initialized = bool(getattr(self, "_toolbar_density_initialized", False))
        user_resize = bool(getattr(self, "_toolbar_density_user_resize_pending", False))
        if getattr(self, "_live_tutor_toolbar_locked", False) and not user_resize:
            return
        if initialized and not (force or user_resize):
            return
        if not hasattr(self, "save_btn") or not hasattr(self, "topbar"):
            return

        buttons = {
            "open": self.open_btn, "save": self.save_btn,
            "search": self.search_btn, "sidebar": self.sidebar_btn,
            "continuous": self.continuous_btn, "book": self.book_btn,
            "zoom_out": self.zoom_out_btn, "zoom_in": self.zoom_in_btn,
            "fit_width": self.fit_width_btn, "fit_page": self.fit_page_btn,
            "previous": self.prev_btn, "next": self.next_btn, "rotate": self.rotate_page_btn,
            "theme": self.theme_btn, "ai": self.ai_chat_btn,
            "tutor": self.live_tutor_btn, "translate": self.translate_btn,
            "present": self.present_btn, "full": self.full_btn,
        }
        active_document_for_toolbar = self.active_tab()
        is_active_pair = bool(active_document_for_toolbar is not None and
                              self.linked_supplementary_tab(active_document_for_toolbar.path) is not None)
        is_arabic_ui = str(self.settings.value("interface_language", "en", type=str) or "en").lower().startswith("ar")
        book_caption = ("إلغاء الربط" if is_active_pair else "ككتاب") if is_arabic_ui else ("Unlink" if is_active_pair else "Book")
        full_labels = ({
            "open": "الرئيسية", "save": "حفظ", "search": "بحث",
            "sidebar": "الشريط الجانبي", "continuous": "تمرير", "book": book_caption,
            "zoom_out": "تصغير", "zoom_in": "تكبير", "fit_width": "ملاءمة العرض",
            "fit_page": "ملاءمة الصفحة", "previous": "السابق", "next": "التالي", "rotate": "تدوير",
            "theme": "مظهر الصفحة", "ai": "AI محادثة مع", "tutor": "AI حصة صوتية مع",
            "translate": "ترجمة", "present": "عرض", "full": "ملء الشاشة",
        } if is_arabic_ui else {
            "open": "Home", "save": "Save", "search": "Search",
            "sidebar": "Sidebar", "continuous": "Scroll", "book": book_caption,
            "zoom_out": "Zoom Out", "zoom_in": "Zoom In", "fit_width": "Fit Width",
            "fit_page": "Fit Page", "previous": "Previous", "next": "Next", "rotate": "Rotate",
            "theme": "Page Theme", "ai": "AI Chat", "tutor": "Audio lesson with AI",
            "translate": "Translate", "present": "Present", "full": "Full Screen",
        })
        compact_labels = ({
            "open": "الرئيسية", "save": "حفظ", "search": "بحث",
            "sidebar": "صفحات", "continuous": "تمرير", "book": book_caption,
            "zoom_out": "", "zoom_in": "", "fit_width": "عرض", "fit_page": "صفحة",
            "previous": "سابق", "next": "التالي", "rotate": "تدوير",
            "theme": "ثيم", "ai": "AI محادثة مع", "tutor": "AI حصة صوتية مع", "translate": "ترجمة",
            "present": "عرض", "full": "ملء",
        } if is_arabic_ui else {
            "open": "Home", "save": "Save", "search": "Search",
            "sidebar": "Pages", "continuous": "Scroll", "book": book_caption,
            "zoom_out": "", "zoom_in": "", "fit_width": "Fit W", "fit_page": "Fit P",
            "previous": "Prev", "next": "Next", "rotate": "Rot",
            "theme": "Theme", "ai": "AI Chat", "tutor": "Audio lesson with AI", "translate": "Translate",
            "present": "Present", "full": "Full",
        })
        priority = [
            "open", "save", "search", "tutor", "ai", "translate", "sidebar",
            "continuous", "book", "theme", "present", "full",
            "fit_width", "fit_page", "previous", "next", "rotate", "zoom_out", "zoom_in",
        ]
        group_for_key = {
            "open": self.file_group, "save": self.file_group,
            "search": self.file_group,
            "sidebar": self.view_group_frame, "continuous": self.view_group_frame,
            "book": self.view_group_frame,
            "zoom_out": self.zoom_group_frame, "zoom_in": self.zoom_group_frame,
            "fit_width": self.zoom_group_frame, "fit_page": self.zoom_group_frame,
            "previous": self.navigation_group, "next": self.navigation_group, "rotate": self.navigation_group,
            "theme": self.utility_group, "ai": self.utility_group,
            "tutor": self.utility_group, "translate": self.utility_group,
            "present": self.utility_group, "full": self.utility_group,
        }

        groups = list(self._toolbar_groups)
        # Use the MAIN WINDOW width for every density calculation.  The child
        # topbar can temporarily report a much smaller width during first show,
        # Home/PDF transitions, or dialog activation; that stale child geometry
        # was the source of the startup two-row layout.
        measured_width = int(self.width())
        available_width = max(0, measured_width - 36)
        row_gap = 2

        def set_caption(key, value):
            button = buttons[key]
            if button.text() != value:
                button.setText(value)
                button.updateGeometry()

        def group_width(group):
            layout = group.layout()
            if layout is not None:
                layout.invalidate()
                layout.activate()
            return max(int(group.sizeHint().width()), int(group.minimumSizeHint().width()))

        def row_width(row_groups):
            if not row_groups:
                return 0
            return sum(group_width(group) for group in row_groups) + row_gap * (len(row_groups) - 1)

        # Measure the minimum icon-only layout first.
        for key in buttons:
            set_caption(key, "")
        # Startup is deliberately ONE row. The toolbar may collapse captions
        # to fit, but it must not split merely because Qt has not completed its
        # first layout pass. A second row is permitted only after a genuine
        # user-originated horizontal resize has been observed.
        split = bool(user_resize and row_width(groups) > available_width)
        row_groups = [groups[:4], groups[4:]] if split else [groups]

        # Captions are promoted independently. A short window can therefore keep
        # the important labels while other actions collapse, rather than switching
        # the entire toolbar abruptly between "all text" and "all icons".
        for row in row_groups:
            row_set = set(row)
            row_keys = [key for key in priority if group_for_key[key] in row_set]
            for key in row_keys:
                set_caption(key, full_labels[key])
                if row_width(row) <= available_width:
                    continue
                # The AI lesson action keeps its descriptive caption in both
                # languages; the toolbar can wrap to a second row rather than
                # silently reducing this named feature to an icon.
                if key == "tutor":
                    continue
                # Keep toolbar density resilient when a future button is added
                # to the priority list before its compact caption is defined.
                set_caption(key, compact_labels.get(key, full_labels.get(key, "")))
                if row_width(row) > available_width:
                    set_caption(key, "")

        # Keep the teacher button caption governed by the same width-fitting
        # pass as every other toolbar action. Do not force it back after fitting.
        self.ai_chat_btn.setAccessibleName("AI محادثة مع" if is_arabic_ui else "AI Chat")
        self.live_tutor_btn.setAccessibleName("AI حصة صوتية مع" if is_arabic_ui else "Audio lesson with AI")
        # Preserve the requested mixed Arabic/Latin caption order instead of letting
        # inherited RTL layout reverse the punctuation and the leading "ai" token.
        for ai_caption_button in (self.ai_chat_btn, self.live_tutor_btn):
            ai_caption_button.setLayoutDirection(Qt.LayoutDirection.LeftToRight)

        # Keep groups compact on ordinary screens, but distribute the available
        # breathing room between groups on wide/4K logical work areas.  This keeps
        # the toolbar from looking stranded at the far left on a large monitor,
        # without stretching individual buttons or changing their hit targets.
        primary_layout = self._toolbar_primary_layout
        secondary_layout = self._toolbar_secondary_layout
        for group in groups:
            primary_layout.removeWidget(group)
            secondary_layout.removeWidget(group)

        def responsive_row_spacing(row_groups):
            if len(row_groups) < 2 or measured_width < 1700:
                return 2
            base_width = row_width(row_groups)
            free_width = max(0, available_width - base_width)
            if free_width < 240:
                return 2
            gap_slots = max(1, len(row_groups) - 1)
            # Use about 46% of spare width for inter-group breathing room and
            # leave the rest as balanced outer margins. The cap avoids absurd
            # gaps on very wide 4K/ultrawide monitors at 100% Windows scaling.
            extra_gap = min(190, int((free_width / gap_slots) * 0.46))
            return 2 + max(0, extra_gap)

        primary_groups = groups[:4] if split else groups
        secondary_groups = groups[4:] if split else []
        primary_spacing = responsive_row_spacing(primary_groups)
        secondary_spacing = responsive_row_spacing(secondary_groups) if split else 2
        primary_layout.setSpacing(primary_spacing)
        secondary_layout.setSpacing(secondary_spacing)
        primary_layout.setAlignment(
            Qt.AlignmentFlag.AlignHCenter if primary_spacing > 2 else Qt.AlignmentFlag.AlignLeft
        )
        secondary_layout.setAlignment(
            Qt.AlignmentFlag.AlignHCenter if secondary_spacing > 2 else Qt.AlignmentFlag.AlignLeft
        )

        for group in primary_groups:
            primary_layout.addWidget(group)
        if split:
            for group in secondary_groups:
                secondary_layout.addWidget(group)
            self.toolbar_row_secondary.show()
        else:
            self.toolbar_row_secondary.hide()
        primary_layout.invalidate()
        secondary_layout.invalidate()
        primary_layout.activate()
        secondary_layout.activate()
        outer_layout = self.topbar.layout()
        if outer_layout is not None:
            outer_layout.invalidate()
            outer_layout.activate()

        self._toolbar_density_mode = "adaptive"
        self._toolbar_wrapped = split
        self._toolbar_density_required_width = (
            row_width(primary_groups) + max(0, primary_spacing - 2) * max(0, len(primary_groups) - 1)
            if not split else
            max(
                row_width(primary_groups) + max(0, primary_spacing - 2) * max(0, len(primary_groups) - 1),
                row_width(secondary_groups) + max(0, secondary_spacing - 2) * max(0, len(secondary_groups) - 1),
            )
        )
        self._toolbar_group_spacing = primary_spacing

        # Preserve accessibility and full labels in tooltips whenever captions hide.
        self.annot_colors_btn.setText("")
        for key, button in buttons.items():
            if not button.text() and button.toolTip():
                button.setAccessibleName(button.toolTip())
        self.zoom_out_btn.setToolTip("Zoom out (Ctrl + mouse wheel down / Ctrl+-)")
        self.zoom_in_btn.setToolTip("Zoom in (Ctrl + mouse wheel up / touchpad pinch). Mouse wheel without Ctrl turns pages.")
        self.translate_btn.setAccessibleName("Translate selected PDF area inside Engo")
        self.live_tutor_btn.setAccessibleName("AI حصة صوتية مع" if is_arabic_ui else "Audio lesson with AI")
        self.live_tutor_btn.setToolTip("AI حصة صوتية مع · شرح صوتي مباشر للصفحة" if is_arabic_ui else "Audio lesson with AI · open the live spoken AI teacher")
        self.ai_chat_btn.setAccessibleName("AI محادثة مع" if is_arabic_ui else "AI Chat")
        self.search_btn.setToolTip("Search this entire PDF · exact text or AI search for concepts, handwriting, and images")
        save_tip_source = "Save changes · use the arrow for Save As"
        save_tip = _engo_translate_tooltip(save_tip_source, "ar" if is_arabic_ui else "en")
        self.save_btn.setToolTip(save_tip)
        self.save_btn.setProperty("engoOriginalToolTip", save_tip_source)
        self.save_btn.setProperty("engoRenderedToolTip", save_tip)
        self.save_btn.setAccessibleName("حفظ ملف PDF · استخدم السهم لحفظ نسخة" if is_arabic_ui else "Save PDF · dropdown for Save As")
        self.topbar.updateGeometry()
        self.topbar.update()
        if self.isVisible():
            self._toolbar_density_initialized = True
            self._toolbar_density_last_width = int(self.width())
            self._toolbar_density_user_resize_pending = False

    def _connect_responsive_screen_signal(self):
        """Listen for monitor/DPI changes so wide-toolbar spacing is recalculated."""
        try:
            handle = self.windowHandle()
            if handle is None or handle is getattr(self, "_responsive_screen_handle", None):
                return
            previous = getattr(self, "_responsive_screen_handle", None)
            if previous is not None:
                try:
                    previous.screenChanged.disconnect(self._on_responsive_screen_changed)
                except Exception:
                    pass
            handle.screenChanged.connect(self._on_responsive_screen_changed)
            self._responsive_screen_handle = handle
        except Exception:
            # Screen-change notifications are an enhancement; normal resize
            # handling and Qt's native DPI scaling remain available regardless.
            pass

    def _on_responsive_screen_changed(self, _screen=None):
        timer = getattr(self, "_responsive_screen_reflow_timer", None)
        if timer is not None:
            timer.start()
        else:
            QTimer.singleShot(180, self._refresh_responsive_toolbar)

    def _refresh_responsive_toolbar(self):
        """Reflow toolbar labels and spacing after a monitor/DPI transition."""
        if not hasattr(self, "topbar"):
            return
        try:
            self._apply_toolbar_density(force=True)
            self._schedule_brand_title_update()
            self.topbar.updateGeometry()
        except Exception:
            pass

    def showEvent(self, event):
        super().showEvent(event)
        self._connect_responsive_screen_signal()
        if not getattr(self, "_home_sidebar_width_restored", False):
            QTimer.singleShot(0, self._restore_home_sidebar_width)
        self._apply_windows_titlebar_theme()
        QTimer.singleShot(100, self._apply_windows_titlebar_theme)
        # Perform one final density calculation after the native window manager
        # has applied the initial normal/maximized geometry. Later UI actions do
        # not trigger reflow; only a spontaneous horizontal resize does.
        if (not getattr(self, "_toolbar_density_initialized", False)
                and not getattr(self, "_toolbar_density_initial_pass_scheduled", False)):
            self._toolbar_density_initial_pass_scheduled = True
            QTimer.singleShot(180, lambda: self._apply_toolbar_density(force=True))

    def _schedule_brand_title_update(self):
        """Re-evaluate the top-left brand label after the tab strip has reflowed."""
        if not hasattr(self, "brand_name") or getattr(self, "_brand_title_update_pending", False):
            return
        self._brand_title_update_pending = True
        QTimer.singleShot(0, self._update_brand_title_visibility)

    def _update_brand_title_visibility(self):
        """Use the full product name, then 'Engo', then no label as tabs need room."""
        self._brand_title_update_pending = False
        if not all(hasattr(self, name) for name in ("brand_name", "tab_strip", "logo_mark", "doc_tabbar", "new_tab_btn", "link_docs_btn")):
            return
        try:
            tab_layout = self.tab_strip.layout()
            margins = tab_layout.contentsMargins()
            spacing = max(0, int(tab_layout.spacing()))
            fixed_width = (
                int(margins.left()) + int(margins.right())
                + int(self.logo_mark.sizeHint().width())
                + int(self.new_tab_btn.sizeHint().width())
                + int(self.link_docs_btn.sizeHint().width())
                + spacing * 4
            )
            available = max(0, int(self.tab_strip.width()) - fixed_width)

            # Estimate the natural width needed by every open tab rather than
            # relying on the tab bar's clipped viewport width.
            tab_count = int(self.doc_tabbar.count())
            tabs_needed = 0
            for tab_index in range(tab_count):
                try:
                    tab_width = int(self.doc_tabbar.tabRect(tab_index).width())
                except Exception:
                    tab_width = 0
                tabs_needed += max(118, tab_width)
            if tab_count > 1:
                tabs_needed += (tab_count - 1) * 5 + 25  # inter-tab gaps + scroll controls
            try:
                tabs_needed = max(tabs_needed, int(self.doc_tabbar.sizeHint().width()))
            except Exception:
                pass

            title_space = max(0, available - tabs_needed)
            metrics = self.brand_name.fontMetrics()
            full_width = metrics.horizontalAdvance(APP_NAME) + 18
            short_width = metrics.horizontalAdvance("Engo") + 18

            if int(self.width()) < 900:
                # In a compact window the short brand keeps the PDF tabs useful.
                title = "Engo" if title_space >= short_width + 8 else ""
            elif title_space >= full_width + 54:
                title = APP_NAME
            elif title_space >= short_width + 8:
                title = "Engo"
            else:
                title = ""

            if self.brand_name.text() != title:
                self.brand_name.setText(title)
            self.brand_name.setVisible(bool(title))
        except Exception:
            # A failed sizing estimate must not interfere with opening/using tabs.
            self.brand_name.setText("Engo")
            self.brand_name.setVisible(self.width() >= 760)

    def resizeEvent(self, event):
        super().resizeEvent(event)
        self._schedule_brand_title_update()
        # Only a system-originated horizontal resize of the active main window
        # (typically the user dragging its edge, maximizing, or restoring it)
        # may change toolbar density. Dialogs and child-layout changes are ignored.
        try:
            old_size = event.oldSize()
            old_width = int(old_size.width()) if old_size.isValid() else int(getattr(self, "_toolbar_density_last_width", self.width()) or self.width())
            new_width = int(self.width())
            spontaneous = bool(event.spontaneous())
            active_main_window = bool(self.isActiveWindow())
            tutor_dialog = getattr(self, "_live_tutor_dialog", None)
            tutor_is_active = bool(tutor_dialog is not None and tutor_dialog.isVisible() and tutor_dialog.isActiveWindow())
            tutor_toolbar_locked = bool(getattr(self, "_live_tutor_toolbar_locked", False))
            if tutor_toolbar_locked:
                # Opening/activating the modal tutor can cause Qt/Windows to emit a
                # spontaneous resize for the parent. Never treat that as a user resize.
                self._toolbar_density_user_resize_pending = False
            elif (getattr(self, "_toolbar_density_initialized", False)
                    and spontaneous and active_main_window and not tutor_is_active
                    and new_width != old_width):
                self._toolbar_density_user_resize_pending = True
                self._schedule_toolbar_density_update()
            elif not getattr(self, "_toolbar_density_initialized", False):
                self._schedule_toolbar_density_update()
            self._toolbar_density_last_width = new_width
        except Exception:
            # Layout stability is more important than a speculative reflow.
            pass
        if hasattr(self, "ai_panel") and self.ai_panel.isVisible():
            if not getattr(self, "_chat_focus_transition_active", False):
                timer = getattr(self, "_chat_transcript_resize_timer", None)
                if timer is not None:
                    timer.start(130)

    def _shortcuts(self):
        bindings = [
            ("Ctrl+O", self.open_dialog), ("Alt+O", self._show_files_screen), ("Ctrl+S", lambda: self.save_active(False)),
            ("Ctrl+Shift+S", lambda: self.save_active(True)), ("Ctrl+F", self.open_pdf_search), ("F11", self.toggle_fullscreen),
            ("Ctrl+Shift+F", self.toggle_chat_focus_mode), ("Ctrl+Shift+B", self.toggle_toolbar_visibility),
            ("F5", self.toggle_presentation), ("Escape", self.exit_modes),
            # Match the toolbar Translate button exactly: Insert starts the same
            # PDF-region translation selection workflow as clicking the icon.
            ("Insert", self.start_translate_selection),
            ("Ctrl+W", lambda: self.close_tab(self.tabs.currentIndex())),
            ("Ctrl+Tab", lambda: self._step_tab(1)), ("Ctrl+Shift+Tab", lambda: self._step_tab(-1)),
            ("Ctrl+Z", self.undo_active), ("Ctrl+Y", self.redo_active),
            ("Delete", self.delete_selected_active), ("Backspace", self.delete_selected_active),
            ("Ctrl+Plus", lambda: self._zoom(1.15)), ("Ctrl+=", lambda: self._zoom(1.15)),
            ("Ctrl+-", lambda: self._zoom(1 / 1.15)),
            ("Left", lambda: self._navigate(-1)), ("Right", lambda: self._navigate(1)),
            ("PageUp", lambda: self._navigate(-1)), ("PageDown", lambda: self._navigate(1)),
        ]
        self._shortcuts_list = []
        for seq, cb in bindings:
            shortcut = QShortcut(QKeySequence(seq), self)
            shortcut.activated.connect(cb)
            self._shortcuts_list.append(shortcut)

    def active_tab(self) -> DocumentTab | None:
        w = self.tabs.currentWidget()
        return w if isinstance(w, DocumentTab) else None

    def _view_target_tab(self) -> DocumentTab | None:
        """Return the pane that should receive pane-specific toolbar actions."""
        primary = self.active_tab()
        target = getattr(self, "_linked_view_target", None)
        if primary is None:
            return None
        secondary = getattr(primary, "_linked_view_secondary", None)
        if secondary is not None and target in (primary, secondary):
            return target
        return primary

    def _set_view_target_tab(self, tab):
        primary = self.active_tab()
        if primary is None:
            return
        secondary = getattr(primary, "_linked_view_secondary", None)
        if tab is primary or (secondary is not None and tab is secondary):
            self._linked_view_target = tab
            # Each PDF keeps its own active annotation tool. Reflect the pane just
            # clicked in the shared toolbar before applying its primary/secondary tint.
            active_tool = str(getattr(tab, "active_tool", "select") or "select")
            for key, button in getattr(self, "tool_buttons", {}).items():
                active = (key == active_tool) or (key == "select" and active_tool == "pan")
                button.setProperty("activeTool", active)
                if button.isChecked() != active:
                    button.setChecked(active)
                button.style().unpolish(button)
                button.style().polish(button)
                button.update()
            self._refresh_selector_tool_button(tab)
            self._refresh_view_target_style()
            self._refresh_tag_menu(tab)
            self._refresh_ai_chat_context(tab)
            self._update_controls()

    def _refresh_view_target_style(self):
        """Subtly tint pane-specific controls when the supplementary PDF is active."""
        primary = self.active_tab()
        secondary = getattr(primary, "_linked_view_secondary", None) if primary else None
        target = self._view_target_tab()
        is_secondary = bool(secondary is not None and target is secondary)
        controls = [getattr(self, name, None) for name in (
            "search_btn", "zoom_out_btn", "zoom_in_btn",
            "fit_width_btn", "fit_page_btn", "prev_btn", "next_btn", "rotate_page_btn",
            "undo_btn", "redo_btn", "delete_btn", "tag_tool_btn")]
        controls.extend(getattr(self, "tool_buttons", {}).values())
        for widget in controls:
            if widget is None:
                continue
            widget.setProperty("linkedPaneTarget", "secondary" if is_secondary else "primary")
            widget.style().unpolish(widget)
            widget.style().polish(widget)
            widget.update()
        # Scroll and Unlink are pair-wide actions; keep them neutral and shared.
        for widget in (getattr(self, "continuous_btn", None), getattr(self, "book_btn", None)):
            if widget is not None:
                widget.setStyleSheet(
                    "QPushButton { background-color: rgba(125, 150, 165, 28); border: 1px solid rgba(150, 175, 190, 85); }"
                    if is_secondary else ""
                )

    def open_pdf_search(self):
        tab = self._view_target_tab()
        if tab is None:
            self.show_status("Open a PDF before searching.")
            return
        worker = self._pdf_search_worker
        worker_running = _qt_thread_is_running(worker)
        if worker is not None and not worker_running:
            # Do not keep a Python wrapper to a QThread whose C++ object has gone away.
            self._pdf_search_worker = None
        if self._pdf_search_dialog is None or self._pdf_search_dialog.path != tab.path:
            self._pdf_search_dialog = PDFSearchDialog(tab.path, self)
            self._pdf_search_dialog.searchRequested.connect(self._start_pdf_search)
            self._pdf_search_dialog.resultActivated.connect(self._activate_pdf_search_result)
            self._pdf_search_dialog.closedByUser.connect(self._on_pdf_search_dialog_closed)
        self._pdf_search_dialog.apply_context_from_parent()
        self._pdf_search_dialog.show()
        self._pdf_search_dialog.raise_()
        self._pdf_search_dialog.activateWindow()
        if worker_running:
            self._pdf_search_dialog.set_busy(True)
            self._pdf_search_dialog.set_progress("A PDF search is still running. You can hide this window and continue reading; results will appear when ready.")
        else:
            self._pdf_search_dialog.set_busy(False)
            self._pdf_search_dialog.query_edit.setFocus()

    def _start_pdf_search(self, query: str, mode: str):
        dialog = self._pdf_search_dialog
        if dialog is None:
            return
        if _qt_thread_is_running(self._pdf_search_worker):
            dialog.set_progress("A search is already running. Wait for it to finish or cancel it by closing Search.")
            dialog.set_busy(False)
            return
        path = dialog.path
        self._pdf_search_generation += 1
        generation = self._pdf_search_generation
        if mode == "text":
            worker = PDFTextSearchWorker(path, query)
            worker.resultsReady.connect(lambda results, p=path, g=generation: self._on_pdf_search_results(p, results, "text", g))
            worker.progressText.connect(lambda message, p=path, g=generation: self._on_pdf_search_progress(p, g, message))
            worker.failed.connect(lambda message, p=path, g=generation: self._on_pdf_search_failed(message, p, g))
        elif mode == "tag":
            dialog.set_busy(True)
            # Read annotations from the live DocumentTab rather than reopening the
            # file from disk, so tagged regions are searchable before the user saves.
            tab = self._open_document_tab_by_path(path)
            if tab is None:
                self._on_pdf_search_failed("The PDF is no longer open.", path, generation)
                return
            tag_name = str(query or "").strip()
            results = []
            try:
                total_pages = int(tab.page_count)
                for page_index in range(total_pages):
                    if page_index % 20 == 0:
                        dialog.set_progress(f"Looking for tag '{tag_name}' · page {page_index + 1}/{total_pages}…")
                        QApplication.processEvents()
                    page = tab.doc.load_page(page_index)
                    page_rect = page.rect
                    for annot in list(page.annots() or []):
                        info = annot.info or {}
                        if (str(info.get("title") or "") != "Engo Region Tag"
                                or self._canonical_tag_name(str(info.get("content") or "").strip()).casefold() != tag_name.casefold()):
                            continue
                        rect = fitz.Rect(annot.rect) & page_rect
                        if rect.is_empty or page_rect.width <= 0 or page_rect.height <= 0:
                            continue
                        box = [
                            max(0.0, min(1.0, rect.x0 / page_rect.width)),
                            max(0.0, min(1.0, rect.y0 / page_rect.height)),
                            max(0.0, min(1.0, rect.width / page_rect.width)),
                            max(0.0, min(1.0, rect.height / page_rect.height)),
                        ]
                        excerpt = page.get_textbox(rect).strip()
                        stroke = (annot.colors or {}).get("stroke")
                        tag_color = ""
                        if isinstance(stroke, (tuple, list)) and len(stroke) >= 3:
                            try:
                                tag_color = QColor.fromRgbF(*[max(0.0, min(1.0, float(v))) for v in stroke[:3]]).name()
                            except Exception:
                                tag_color = ""
                        if not tag_color:
                            try:
                                tag_color = self._tag_color(tab, tag_name)
                            except Exception:
                                tag_color = ""
                        results.append({
                            "page": page_index + 1,
                            "box": box,
                            "excerpt": excerpt[:220] if excerpt else f"Tagged region · {tag_name}",
                            "reason": f"Tag: {tag_name}",
                            "kind": "tag",
                            "tag": tag_name,
                            "tag_color": tag_color,
                            "source": "annotation",
                        })
            except Exception as exc:
                self._on_pdf_search_failed(f"Could not read tag annotations: {exc}", path, generation)
                return
            self._on_pdf_search_results(path, results, "tag", generation)
            dialog.set_busy(False)
            return
        else:
            tab = self._open_document_tab_by_path(path)
            page_total = tab.page_count if tab is not None else 0
            answer = QMessageBox.question(
                self._pdf_search_dialog, "AI search across the whole PDF",
                f"AI search will inspect all {page_total or 'available'} pages in image/text batches using Google Gemini, "
                "regardless of the provider or model selected for chat. Page content will be sent to Google and may use "
                "paid Gemini API credits. Continue?",
                QMessageBox.StandardButton.Yes | QMessageBox.StandardButton.No,
                QMessageBox.StandardButton.No
            )
            if answer != QMessageBox.StandardButton.Yes:
                dialog.set_busy(False)
                dialog.set_progress("AI search cancelled before sending anything.")
                return
            # PDF AI search is a Google-only document feature. It deliberately does not
            # inherit the provider/model currently selected in the chat panel.
            provider = "gemini"
            model = str(self.settings.value(
                "ai_model_gemini", AI_DEFAULT_MODELS["gemini"], type=str
            ) or AI_DEFAULT_MODELS["gemini"])
            key = _get_provider_key(self.settings, "gemini")
            if not key:
                dialog.set_progress("No Google Gemini API key is configured. Open AI Settings and add your Gemini key.")
                dialog.set_busy(False)
                return
            worker = AISemanticSearchWorker(path, provider, model, key, query)
            worker.resultsReady.connect(lambda results, p=path, g=generation: self._on_pdf_search_results(p, results, "ai", g))
            worker.progressText.connect(lambda message, p=path, g=generation: self._on_pdf_search_progress(p, g, message))
            worker.searchFailed.connect(lambda message, p=path, g=generation: self._on_pdf_search_failed(message, p, g))
        self._pdf_search_worker = worker
        dialog.set_busy(True)
        worker.finished.connect(lambda w=worker: self.pdfSearchWorkerFinished.emit(w))
        worker.start()

    def _finalize_pdf_search_worker(self, worker):
        """Release the completed search worker on the GUI thread and clear its reference."""
        is_current_worker = self._pdf_search_worker is worker
        if is_current_worker:
            self._pdf_search_worker = None
        dialog = self._pdf_search_dialog
        if is_current_worker and dialog is not None:
            try:
                if not dialog._closed_by_user:
                    dialog.set_busy(False)
            except RuntimeError:
                pass
        try:
            worker.deleteLater()
        except RuntimeError:
            pass
        self._maybe_finish_pending_close()

    def _on_pdf_search_dialog_closed(self):
        """A true close clears search state; Hide deliberately does not emit this signal."""
        dialog = self._pdf_search_dialog
        if dialog is None:
            return
        # Invalidate queued callbacks from a request that was closed by the user.
        self._pdf_search_generation += 1
        worker = self._pdf_search_worker
        if _qt_thread_is_running(worker):
            try:
                if os.path.normcase(os.path.abspath(getattr(worker, "path", ""))) == os.path.normcase(dialog.path):
                    worker.cancel()
            except Exception:
                pass
        path = dialog.path
        tab = self._open_document_tab_by_path(path)
        if tab is not None:
            tab.canvas.search_highlights = {}
            tab.canvas.update()
            tab._update_linked_display()
        self._active_pdf_search_results = []
        self._pdf_search_path = ""
        if hasattr(self, "search_btn"):
            self.search_btn.setProperty("searchActive", False)
            self.search_btn.style().unpolish(self.search_btn)
            self.search_btn.style().polish(self.search_btn)
            self.search_btn.update()
        try:
            dialog.clear_search_state()
        except RuntimeError:
            pass

    def _on_pdf_search_progress(self, path: str, generation: int, message: str):
        dialog = self._pdf_search_dialog
        if generation != self._pdf_search_generation or dialog is None or dialog.path != path or dialog._closed_by_user:
            return
        dialog.set_progress(message)

    def _on_pdf_search_results(self, path: str, results, mode: str, generation: int | None = None):
        dialog = self._pdf_search_dialog
        if generation is not None and generation != self._pdf_search_generation:
            return
        if dialog is not None and dialog.path == path and dialog._closed_by_user:
            return
        clean = [dict(item) for item in (results or []) if isinstance(item, dict)]
        self._active_pdf_search_results = clean
        self._pdf_search_path = path
        if dialog is not None and dialog.path == path:
            dialog.set_results(clean, mode)
        # Paint every result on its page, not only the selected list item.
        tab = self._open_document_tab_by_path(path)
        if tab is not None:
            grouped = {}
            for item in clean:
                box = item.get("box")
                if isinstance(box, (list, tuple)) and len(box) == 4:
                    grouped.setdefault(int(item.get("page", 1)) - 1, []).append([float(v) for v in box])
            tab.canvas.search_highlights = grouped
            tab.canvas.update()
            tab._update_linked_display()

    def _on_pdf_search_failed(self, message: str, path: str | None = None, generation: int | None = None):
        dialog = self._pdf_search_dialog
        if generation is not None and generation != self._pdf_search_generation:
            return
        if dialog is not None and not dialog._closed_by_user and (path is None or dialog.path == path):
            dialog.set_progress(f"Search failed: {message}")
            dialog.set_busy(False)

    def _activate_pdf_search_result(self, result):
        if not isinstance(result, dict):
            return
        path = self._pdf_search_path or (self._pdf_search_dialog.path if self._pdf_search_dialog else "")
        tab = self._open_document_tab_by_path(path)
        if tab is None:
            self.open_pdf(path)
            tab = self._open_document_tab_by_path(path)
        if tab is None:
            return
        index = max(0, int(result.get("page", 1)) - 1)
        linked_primary = self._linked_primary_for_path(path)
        current_index = self.tabs.indexOf(linked_primary) if linked_primary is not None else self.tabs.indexOf(tab)
        if current_index >= 0:
            self.doc_tabbar.setCurrentIndex(current_index)
            self.tabs.setCurrentIndex(current_index)
        self.search_btn.setProperty("searchActive", True)
        self.search_btn.style().unpolish(self.search_btn)
        self.search_btn.style().polish(self.search_btn)
        self.search_btn.update()
        tab.canvas.search_highlights = {}
        box = result.get("box")
        if isinstance(box, (list, tuple)) and len(box) == 4:
            tab.canvas.search_highlights[index] = [[float(v) for v in box]]
        tab.go_to_page(index)
        tab.canvas.update()
        tab._update_linked_display()
        self.show_status(f"Search result · {Path(path).name} · page {index + 1}")

    def open_dialog(self):
        paths = _engo_file_dialog(
            self, "Open documents or images", "فتح ملفات نصية أو صور", str(Path.home()),
            "Supported documents (*.pdf *.png *.jpg *.jpeg *.webp *.bmp *.tif *.tiff *.gif *.docx *.pptx);;PDF files (*.pdf);;Images (*.png *.jpg *.jpeg *.webp *.bmp *.tif *.tiff *.gif);;Word documents (*.docx);;PowerPoint presentations (*.pptx)",
            multiple=True, native=True
        )
        for path in paths:
            self.open_pdf(path)

    def _connect_document_tab(self, tab):
        """Bind one document tab's signals to the window that currently owns it."""
        for signal in (tab.currentPageChanged, tab.documentChanged, tab.titleChanged,
                       tab.historyChanged, tab.annotationSelectionChanged,
                       tab.aiRegionSelected, tab.translateRegionSelected):
            try:
                signal.disconnect()
            except (TypeError, RuntimeError):
                pass
        tab.currentPageChanged.connect(
            lambda current, total, source_tab=tab: self._on_document_page_changed(source_tab, current, total))
        tab.documentChanged.connect(self._update_controls)
        tab.titleChanged.connect(lambda title, t=tab: self._refresh_tab_title(t, title))
        tab.historyChanged.connect(self._update_history_controls)
        tab.annotationSelectionChanged.connect(self._update_selection_controls)
        tab.aiRegionSelected.connect(lambda page_index, data, t=tab: self._on_ai_region_selected(t, page_index, data))
        tab.translateRegionSelected.connect(
            lambda page_index, data, clip, selected_text, t=tab:
                self._on_translate_region_selected(t, page_index, data, clip, selected_text))

    def _detach_document_tab(self, tab):
        """Remove a live document widget from this window without closing its PDF.

        This is a MOVE operation, not a close operation.  The DocumentTab must
        remain alive so the destination window can adopt the exact same widget
        and preserve its loaded document, page, zoom, annotations and history.
        """
        index = self.tabs.indexOf(tab)
        if index < 0:
            return False
        # Stop drag polling and discard any references held by the source tabbar
        # before the widget is removed/reparented.  Otherwise paintEvent can try
        # to query a QWidget that has already been destroyed by another path.
        try:
            self.doc_tabbar.forget_tab(tab)
        except (AttributeError, RuntimeError):
            pass
        old_current = self.doc_tabbar.currentIndex()
        self._unlink_document_relationships(tab)
        for signal in (tab.currentPageChanged, tab.documentChanged, tab.titleChanged,
                       tab.historyChanged, tab.annotationSelectionChanged,
                       tab.aiRegionSelected, tab.translateRegionSelected):
            try:
                signal.disconnect()
            except (TypeError, RuntimeError):
                pass
        close_button = self.doc_tabbar.tabButton(index, QTabBar.ButtonPosition.RightSide)
        if close_button is not None:
            self.doc_tabbar.setTabButton(index, QTabBar.ButtonPosition.RightSide, None)
            close_button.deleteLater()
        bar_blocked = self.doc_tabbar.blockSignals(True)
        stack_blocked = self.tabs.blockSignals(True)
        try:
            self.doc_tabbar.removeTab(index)
            self._schedule_brand_title_update()
            self.tabs.removeWidget(tab)
            if tab in self._tab_order:
                self._tab_order.remove(tab)
        finally:
            self.doc_tabbar.blockSignals(bar_blocked)
            self.tabs.blockSignals(stack_blocked)
        # QStackedWidget.removeWidget() hides the widget but deliberately does
        # not destroy it.  Do NOT call deleteLater() here: _adopt_document_tab()
        # in the receiving window reparents and inserts this same live widget.
        # Also avoid setParent(None), which can briefly create a native
        # QWidgetWindow on Windows while the tab is between its two stacks.
        if self.tabs.count():
            selected = min(max(0, old_current), self.tabs.count() - 1)
            self.doc_tabbar.setCurrentIndex(selected)
            self.tabs.setCurrentIndex(selected)
            self._on_tab_changed(selected)
            self._refresh_linked_tab_layout()
            self._refresh_linked_context_label()
        else:
            self.ai_panel.set_document("", "No PDF open")
            self.ai_panel.hide()
            self.ai_chat_btn.setChecked(False)
            self._show_files_screen()
            self._update_controls()
        return True

    def _reload_linked_pair_settings(self):
        # Kept for compatibility with existing call sites. Links are intentionally
        # session-local and must never be reloaded from persistent settings.
        return

    def _adopt_document_tab(self, tab, activate=True):
        """Adopt a live document widget from another window as a normal tab."""
        existing = self._open_document_tab_by_path(tab.path)
        if existing is not None:
            idx = self.tabs.indexOf(existing)
            self.doc_tabbar.setCurrentIndex(idx)
            self.tabs.setCurrentIndex(idx)
            return existing
        self._reload_linked_pair_settings()
        tab.setParent(self.tabs)
        self._connect_document_tab(tab)
        index = self.tabs.addWidget(tab)
        self._tab_order.insert(index, tab)
        self.doc_tabbar.insertTab(index, tab.tab_title())
        self._install_tab_close_button(index, tab)
        icon_path = resource_path("engopdfviewer.ico")
        if os.path.exists(icon_path):
            self.doc_tabbar.setTabIcon(index, QIcon(icon_path))
        if activate:
            self.doc_tabbar.setCurrentIndex(index)
            self.tabs.setCurrentIndex(index)
        self._refresh_linked_tab_layout()
        self._refresh_linked_context_label()
        self._show_document_area()
        self._update_controls()
        return tab

    def _show_tab_drag_hint(self, source_index, target_index):
        if (0 <= source_index < len(self._tab_order) and
                0 <= target_index < len(self._tab_order)):
            source = Path(self._tab_order[source_index].path).name
            target = Path(self._tab_order[target_index].path).name
            self.show_status(f"Reorder tabs · use Link to combine {source} + {target}")

    def _link_tabs_in_window(self, source_index, target_index):
        if not (0 <= source_index < len(self._tab_order) and
                0 <= target_index < len(self._tab_order)):
            return
        supplementary = self._tab_order[source_index]
        primary = self._tab_order[target_index]
        if supplementary is primary:
            return
        answer = QMessageBox.question(
            self, "Link these PDF tabs?",
            f"Do you want to link these two PDFs as one study session?\n\n"
            f"Primary: {Path(primary.path).name}\n"
            f"Supplementary: {Path(supplementary.path).name}\n\n"
            "The tab you dragged will become the supplementary document.",
            QMessageBox.StandardButton.Yes | QMessageBox.StandardButton.No,
            QMessageBox.StandardButton.Yes)
        if answer == QMessageBox.StandardButton.Yes:
            self._apply_linked_pdf_pair(primary.path, supplementary.path, start_new_dual_chat=True)
        else:
            self.show_status("Tabs remain independent")

    def _start_document_tab_drag(self, tab_or_index, global_pos):
        """Run a real Qt drag; if no Engo window accepts it, tear it off into a new window."""
        if isinstance(tab_or_index, int):
            index = tab_or_index
            if not (0 <= index < len(self._tab_order)):
                return
            tab = self._tab_order[index]
        else:
            tab = tab_or_index
            index = self.tabs.indexOf(tab)
            if index < 0:
                return

        token = uuid.uuid4().hex
        _DOCUMENT_TAB_DRAG_REGISTRY[token] = (self, tab)
        mime = QMimeData()
        mime.setData(DOCUMENT_TAB_MIME, QByteArray(token.encode("ascii")))
        drag = QDrag(self.doc_tabbar)
        drag.setMimeData(mime)
        try:
            current_index = self.tabs.indexOf(tab)
            if current_index >= 0:
                drag.setPixmap(self.doc_tabbar.grab(self.doc_tabbar.tabRect(current_index)))
                drag.setHotSpot(QPoint(18, 12))
        except Exception:
            pass
        try:
            result = drag.exec(Qt.DropAction.MoveAction)
        except Exception:
            result = Qt.DropAction.IgnoreAction
        finally:
            _DOCUMENT_TAB_DRAG_REGISTRY.pop(token, None)

        # An ignored OS drop creates a detached window only when the pointer was
        # actually released outside this MainWindow. Releasing over this window's
        # PDF/workspace area must never tear the tab off accidentally.
        if result != Qt.DropAction.MoveAction and self.tabs.indexOf(tab) >= 0:
            release_pos = QCursor.pos()
            safe_frame = self.frameGeometry().adjusted(-12, -12, 12, 12)
            if not safe_frame.contains(release_pos):
                self._spawn_detached_document_window(tab, release_pos)
            else:
                current_index = self.tabs.indexOf(tab)
                if current_index >= 0:
                    self.doc_tabbar.setCurrentIndex(current_index)
                    self.tabs.setCurrentIndex(current_index)

    def _spawn_detached_document_window(self, tab, global_pos):
        """Move one existing DocumentTab into a new top-level Engo window."""
        if tab is None or self.tabs.indexOf(tab) < 0:
            return False
        detached_window = MainWindow(register_ipc=False)
        if not self._detach_document_tab(tab):
            detached_window.close()
            return False
        detached_window._adopt_document_tab(tab, activate=True)
        screen = QApplication.screenAt(global_pos) or QApplication.primaryScreen()
        if screen is not None:
            area = screen.availableGeometry()
            width = min(1500, max(760, int(area.width() * 0.82)))
            height = min(980, max(520, int(area.height() * 0.82)))
            left = max(area.left(), min(global_pos.x() - width // 2, area.right() - width + 1))
            top = max(area.top(), min(global_pos.y() - 24, area.bottom() - height + 1))
            detached_window.setGeometry(left, top, width, height)
        detached_window.showNormal()
        detached_window.raise_()
        detached_window.activateWindow()
        if self.tabs.count() == 0:
            QTimer.singleShot(0, self.close)
        return True

    def _receive_document_tab_drop(self, mime, global_pos, target_index=-1):
        if not mime.hasFormat(DOCUMENT_TAB_MIME):
            return False
        try:
            token = bytes(mime.data(DOCUMENT_TAB_MIME)).decode("ascii")
            entry = _DOCUMENT_TAB_DRAG_REGISTRY.get(token)
            if not entry:
                return False
            source_window, dragged_tab = entry
            if source_window is self:
                source_index = self.tabs.indexOf(dragged_tab)
                if source_index >= 0:
                    if 0 <= target_index < len(self._tab_order) and target_index != source_index:
                        self._link_tabs_in_window(source_index, target_index)
                    elif target_index < 0:
                        # Dragging a tab out of the tab strip into the reader/workspace
                        # creates an independent top-level window, matching the original tear-off UX.
                        self._spawn_detached_document_window(dragged_tab, global_pos)
                    else:
                        self.doc_tabbar.setCurrentIndex(source_index)
                        self.tabs.setCurrentIndex(source_index)
                    return True
                return False
            existing = self._open_document_tab_by_path(dragged_tab.path)
            if existing is not None:
                # The destination already has this PDF. Move focus to its tab
                # and remove the duplicate source tab rather than leaving a copy.
                if source_window._detach_document_tab(dragged_tab):
                    try:
                        dragged_tab.close_document()
                    except Exception:
                        pass
                    if source_window.tabs.count() == 0:
                        QTimer.singleShot(0, source_window.close)
                target = self.tabs.indexOf(existing)
                if target >= 0:
                    self.doc_tabbar.setCurrentIndex(target)
                    self.tabs.setCurrentIndex(target)
                return True

            # Move a tab between windows. A release in the green center of
            # another tab explicitly requests linking after the move; edge/outside
            # drops only move the tab.
            if not source_window._detach_document_tab(dragged_tab):
                return False
            self._adopt_document_tab(dragged_tab, activate=True)
            if 0 <= target_index < len(self._tab_order):
                source_index = self.tabs.indexOf(dragged_tab)
                if source_index >= 0 and source_index != target_index:
                    self._link_tabs_in_window(source_index, target_index)
            else:
                self.show_status(f"Moved tab · {Path(dragged_tab.path).name}")
            if source_window.tabs.count() == 0:
                QTimer.singleShot(0, source_window.close)
            return True
        except Exception as exc:
            QMessageBox.warning(self, "Move PDF tab", f"The tab could not be moved:\n{exc}")
            return False

    def open_office_document(self, path: str):
        """Open DOCX/PPTX directly in its native OOXML format; never convert to PDF."""
        if office_etree is None:
            is_ar = str(self.settings.value("interface_language", "en", type=str) or "en").lower().startswith("ar")
            QMessageBox.warning(
                self, APP_NAME,
                ("قراءة Word وPowerPoint تحتاج إلى مكتبة lxml. أغلق Engo وشغّله من run.bat لتثبيتها تلقائيًا."
                 if is_ar else
                 "Word and PowerPoint reading needs the lxml package. Close Engo and launch it with run.bat to install it automatically.")
            )
            return
        source_path = os.path.abspath(str(path or ""))
        if not os.path.isfile(source_path) or not is_office_document(source_path):
            QMessageBox.information(self, APP_NAME, "Choose a modern Word (.docx) or PowerPoint (.pptx) file.")
            return
        language = str(self.settings.value("interface_language", "en", type=str) or "en")
        is_ar = language.lower().startswith("ar")
        readers = getattr(self, "_office_reader_windows", None)
        if readers is None:
            readers = {}
            self._office_reader_windows = readers
        key = os.path.normcase(source_path)
        existing = readers.get(key)
        if existing is not None:
            try:
                existing.showNormal()
                existing.raise_()
                existing.activateWindow()
                return
            except RuntimeError:
                readers.pop(key, None)
        try:
            reader = OfficeDocumentReaderDialog(source_path, language, self)
            readers[key] = reader
            reader.finished.connect(lambda _result=0, k=key, store=readers: store.pop(k, None))
            reader.askAISelected.connect(self._ask_about_office_text)
            reader.show()
            reader.raise_()
            reader.activateWindow()
            self._record_recent_file(source_path)
            self.show_status(("تم فتح ملف Office بصيغته الأصلية · " if is_ar else
                              "Opened Office document in its native format · ") + Path(source_path).name)
        except Exception as exc:
            QMessageBox.critical(
                self, APP_NAME,
                ("تعذرت قراءة هذا الملف. تأكد من تثبيت python-docx وpython-pptx وأن الملف غير تالف.\n\n" if is_ar else
                 "Could not read this file. Make sure python-docx and python-pptx are installed and the file is valid.\n\n") + str(exc)
            )

    def _ask_about_office_text(self, selected_text: str, source_path: str):
        selected_text = str(selected_text or "").strip()
        if not selected_text:
            return
        panel = getattr(self, "ai_panel", None)
        if panel is None:
            return
        is_ar = str(self.settings.value("interface_language", "en", type=str) or "en").lower().startswith("ar")
        try:
            panel.set_document(source_path, Path(source_path).name)
            if not panel.isVisible():
                self._animate_ai_panel(True)
            QTimer.singleShot(260, lambda p=panel, value=selected_text: p._ask_about_selected_chat_text(value, "document"))
            self.show_status("تم إرفاق النص المحدد من مستند Office إلى محادثة AI" if is_ar else "Selected Office text attached to the AI chat")
        except Exception as exc:
            QMessageBox.warning(self, APP_NAME, str(exc))

    def open_pdf(self, path):
        source_path = os.path.abspath(str(path or ""))
        if is_office_document(source_path):
            self.open_office_document(source_path)
            return
        if not is_supported_document(source_path):
            QMessageBox.information(self, APP_NAME, "Please choose a PDF, image, DOCX, or PPTX file.")
            return
        try:
            viewer_path = prepare_document_for_viewer(source_path)
        except Exception as exc:
            QMessageBox.critical(self, APP_NAME, f"Could not prepare this document:\n{exc}")
            return
        is_image = is_image_document(source_path)
        for i in range(self.tabs.count()):
            tab = self.tabs.widget(i)
            existing_source = os.path.abspath(str(getattr(tab, "source_path", tab.path))) if isinstance(tab, DocumentTab) else ""
            if isinstance(tab, DocumentTab) and (os.path.normcase(tab.path) == os.path.normcase(viewer_path) or os.path.normcase(existing_source) == os.path.normcase(source_path)):
                primary = self._linked_primary_for_path(path)
                if primary is not None:
                    i = self.tabs.indexOf(primary)
                self.doc_tabbar.setCurrentIndex(i)
                self.tabs.setCurrentIndex(i)
                self._show_document_area()
                self._record_recent_file(source_path)
                self._update_controls()
                self._refresh_linked_context_label()
                return
        try:
            tab = DocumentTab(viewer_path, self.dark_mode, self.bg_color, self.ink_color, self,
                              self.annotation_colors, self.smart_page_theme)
            tab.source_path = source_path
            tab.display_path = source_path
            tab.is_image_source = bool(is_image)
            try:
                tab._primary_thumb_label.setText(Path(source_path).name)
            except Exception:
                pass
        except Exception as exc:
            QMessageBox.critical(self, APP_NAME, f"Could not open document:\n{exc}")
            return
        self._connect_document_tab(tab)
        idx = self.tabs.addWidget(tab)
        # Opening a document and changing its viewing layout must never rewrite
        # embedded PDF annotations. Tag reconciliation is deliberately excluded
        # from this path; the tag catalogue and view controls are read-only here.
        try:
            current_language = str(self.settings.value("interface_language", "en", type=str) or "en")
            tab.side_tabs.setLanguage(current_language)
        except (AttributeError, RuntimeError):
            pass
        self._tab_order.insert(idx, tab)
        self.doc_tabbar.addTab(tab.tab_title())
        self._schedule_brand_title_update()
        self._install_tab_close_button(idx, tab)
        self._refresh_tab_title(tab, tab.tab_title())
        icon_path = resource_path("engopdfviewer.ico")
        if os.path.exists(icon_path):
            self.doc_tabbar.setTabIcon(idx, QIcon(icon_path))
        # If this PDF is the supplementary half of a saved pair, open the
        # primary tab instead so the combined view is what the user sees.
        primary_target = self._linked_primary_for_path(path)
        target_index = self.tabs.indexOf(primary_target) if primary_target is not None else idx
        self.doc_tabbar.setCurrentIndex(target_index)
        self.tabs.setCurrentIndex(target_index)
        tab.go_to_page(0)
        self._refresh_linked_tab_layout()
        self._refresh_linked_context_label()
        self._show_document_area()
        self._record_recent_file(source_path)
        self.show_status(f"Opened {Path(source_path).name}  ·  {tab.page_count} page(s)")
        self._update_controls()

    def _open_document_tab_by_path(self, path: str):
        wanted = os.path.normcase(os.path.abspath(path or ""))
        for i in range(self.tabs.count()):
            tab = self.tabs.widget(i)
            if isinstance(tab, DocumentTab):
                candidates = (tab.path, getattr(tab, "source_path", tab.path))
                if any(os.path.normcase(os.path.abspath(value or "")) == wanted for value in candidates):
                    return tab
        return None

    def linked_supplementary_tab(self, primary_path: str):
        companion = self._linked_pdf_pairs.get(os.path.normcase(os.path.abspath(primary_path or "")))
        if not companion:
            return None
        return self._open_document_tab_by_path(companion)

    def _linked_pair_for_tab(self, tab: DocumentTab | None):
        """Return (primary, supplementary) when *tab* belongs to either side."""
        if tab is None:
            return (None, None)
        supplementary = self.linked_supplementary_tab(tab.path)
        if supplementary is not None:
            return (tab, supplementary)
        primary = self._linked_primary_for_path(tab.path)
        if primary is not None:
            return (primary, tab)
        return (None, None)

    def _linked_payload_for(self, document_path: str):
        """Return the other member of a linked pair, regardless of argument direction."""
        tab = self._open_document_tab_by_path(document_path)
        primary, secondary = self._linked_pair_for_tab(tab) if tab is not None else (None, None)
        if primary is None or secondary is None:
            return []
        companion = secondary if os.path.normcase(os.path.abspath(primary.path)) == os.path.normcase(os.path.abspath(document_path)) else primary
        return [{"path": companion.path, "page_index": int(companion.current_page), "name": Path(companion.path).name}]

    def _ai_chat_scope_key(self, path: str) -> str:
        """Return a per-PDF key, or a stable pair-specific key for linked documents."""
        tab = self._open_document_tab_by_path(path)
        primary, secondary = self._linked_pair_for_tab(tab) if tab is not None else (None, None)
        if primary is None or secondary is None:
            return os.path.abspath(path)
        pair = sorted([
            os.path.normcase(os.path.abspath(primary.path)),
            os.path.normcase(os.path.abspath(secondary.path)),
        ])
        canonical = "ENGO_DUAL::" + hashlib.sha1(
            json.dumps(pair, ensure_ascii=False).encode("utf-8")
        ).hexdigest()

        # Older releases hashed [primary, secondary] in display order. Migrate
        # both permutations so A+B and B+A resolve to the very same saved chats.
        legacy_keys = []
        for ordered_pair in (pair, list(reversed(pair))):
            legacy_digest = hashlib.sha1(
                json.dumps(ordered_pair, ensure_ascii=False).encode("utf-8")
            ).hexdigest()
            legacy_keys.append("ENGO_DUAL::" + legacy_digest)
        panel = getattr(self, "ai_panel", None)
        store = getattr(panel, "chat_store", None) if panel is not None else None
        if store is not None:
            store.migrate_chat_scopes(legacy_keys, canonical)
            # Carry forward the last selected conversation from either legacy
            # orientation when the canonical preference has not been written yet.
            pref_key = panel._chat_pref_key(canonical)
            if not panel.settings.contains(pref_key):
                valid_chat_ids = {int(row["id"]) for row in store.list_chats(canonical)}
                for legacy_scope in legacy_keys:
                    old_pref = panel.settings.value(panel._chat_pref_key(legacy_scope), 0, type=int)
                    if old_pref and int(old_pref) in valid_chat_ids:
                        panel.settings.setValue(pref_key, int(old_pref))
                        break
        return canonical

    def _refresh_ai_chat_context(self, preferred_tab=None, start_new_dual_chat=False):
        """Immediately bind Engo AI to the correct individual or linked-pair chat scope."""
        panel = getattr(self, "ai_panel", None)
        if panel is None:
            return
        candidate = preferred_tab if isinstance(preferred_tab, DocumentTab) else None
        if candidate is None or self.tabs.indexOf(candidate) < 0:
            candidate = self._view_target_tab() or self.active_tab()
        if candidate is None or self.tabs.indexOf(candidate) < 0:
            return

        primary, secondary = self._linked_pair_for_tab(candidate)
        is_dual = primary is not None and secondary is not None
        context_tab = primary if is_dual else candidate
        desired_scope = self._ai_chat_scope_key(context_tab.path)
        current_path = os.path.normcase(os.path.abspath(panel.document_path or ""))
        desired_path = os.path.normcase(os.path.abspath(context_tab.path))
        current_scope = str(getattr(panel, "chat_scope_key", "") or "")
        if current_path != desired_path or current_scope != desired_scope:
            panel.set_document(context_tab.path, Path(context_tab.path).name)
        else:
            # On a simple tab reselect, the conversation list and title are already
            # correct. Avoid rebuilding the combo and its saved-chat model again.
            pass

        if is_dual:
            panel.chat_combo.setToolTip("Saved conversations for this linked PDF pair")
            panel.new_chat_btn.setToolTip("Start a new shared conversation for both linked PDFs")
        else:
            panel.chat_combo.setToolTip("Saved conversations for the current PDF")
            panel.new_chat_btn.setToolTip("Start a new saved conversation for this PDF")

        self._refresh_linked_context_label()

    def _refresh_linked_context_label(self):
        if not hasattr(self, "ai_panel"):
            return
        primary = self.active_tab()
        if primary is None:
            return
        companion = self.linked_supplementary_tab(primary.path)
        if companion:
            self.ai_panel.document_label.setText(f"Combined study · Primary: {Path(primary.path).name}  +  Supplementary: {Path(companion.path).name}")
            self.ai_panel.document_label.setToolTip(f"One conversation includes the current page from both PDFs.\nPrimary: {primary.path}\nSupplementary: {companion.path}")
        else:
            self.ai_panel.document_label.setText(f"PDF context · {Path(primary.path).name}")
            self.ai_panel.document_label.setToolTip("The current PDF provides context to questions when enabled")

    def _linked_primary_for_path(self, path: str):
        wanted = os.path.normcase(os.path.abspath(path or ""))
        for primary, companion in self._linked_pdf_pairs.items():
            if os.path.normcase(os.path.abspath(companion)) == wanted:
                return self._open_document_tab_by_path(primary)
        return None

    def _refresh_linked_tab_layout(self):
        """Hide supplementary tabs in the tab bar and activate a paired two-page view."""
        companion_keys = {
            os.path.normcase(os.path.abspath(companion))
            for primary, companion in self._linked_pdf_pairs.items()
            if self._open_document_tab_by_path(primary) is not None
        }
        for index in range(self.tabs.count()):
            tab = self.tabs.widget(index)
            if isinstance(tab, DocumentTab):
                hidden_as_companion = os.path.normcase(os.path.abspath(tab.path)) in companion_keys
                self.doc_tabbar.setTabVisible(index, not hidden_as_companion)
        for index in range(self.tabs.count()):
            candidate_title_tab = self.tabs.widget(index)
            if isinstance(candidate_title_tab, DocumentTab):
                self._refresh_tab_title(candidate_title_tab, candidate_title_tab.tab_title())
        active = self.active_tab()
        for index in range(self.tabs.count()):
            candidate = self.tabs.widget(index)
            if not isinstance(candidate, DocumentTab):
                continue
            companion = self.linked_supplementary_tab(candidate.path)
            if candidate is active and companion is not None:
                candidate.enable_linked_view(companion)
            elif candidate._linked_view_secondary is not None and candidate._linked_view_secondary is not companion:
                candidate.disable_linked_view()
        if active is not None and self.linked_supplementary_tab(active.path) is not None:
            active.set_layout_modes(book=False, scroll=active.scroll_mode)
        self._update_controls()

    def _unlink_document_relationships(self, tab: DocumentTab):
        wanted = os.path.normcase(os.path.abspath(tab.path))
        changed = False
        for primary, companion in list(self._linked_pdf_pairs.items()):
            primary_key = os.path.normcase(os.path.abspath(primary))
            companion_key = os.path.normcase(os.path.abspath(companion))
            if wanted in (primary_key, companion_key):
                parent_tab = self._open_document_tab_by_path(primary)
                companion_tab = self._open_document_tab_by_path(companion)
                if parent_tab is not None:
                    parent_tab.disable_linked_view()
                    # Unlink returns to single-page mode; do not silently
                    # re-enable a previously saved Book spread.
                    parent_tab.set_layout_modes(book=False, scroll=parent_tab.scroll_mode)
                if companion_tab is not None:
                    companion_tab.set_layout_modes(book=False, scroll=companion_tab.scroll_mode)
                self._linked_pdf_pairs.pop(primary, None)
                changed = True

    def configure_linked_pdfs(self):
        open_tabs = [self.tabs.widget(i) for i in range(self.tabs.count())
                     if isinstance(self.tabs.widget(i), DocumentTab)]
        if len(open_tabs) < 2:
            QMessageBox.information(self, "Combine PDF tabs", "Open at least two PDF tabs first.\n\nChoose one as the primary document and the other as the supplementary document.")
            return
        dialog = QDialog(self)
        dialog.setWindowTitle("Combine PDF tabs · one study session")
        dialog.setMinimumWidth(520)
        root = QVBoxLayout(dialog)
        intro = QLabel("Choose the two PDF files only. They will appear side by side in one tab, each with independent scrolling and page thumbnails. No page numbers are requested: Engo AI and Voice & Learn always use the page currently displayed in each PDF.")
        intro.setWordWrap(True)
        root.addWidget(intro)
        primary_combo = QComboBox()
        secondary_combo = QComboBox()
        secondary_combo.addItem("No supplementary PDF · unlink", "")
        for item in open_tabs:
            label = f"{Path(item.path).name} · {item.page_count} pages"
            primary_combo.addItem(label, item.path)
            secondary_combo.addItem(label, item.path)
        active = self.active_tab()
        if active:
            primary_combo.setCurrentIndex(max(0, primary_combo.findData(active.path)))
        current_primary_path = str(primary_combo.currentData() or "")
        old_secondary = self._linked_pdf_pairs.get(os.path.normcase(os.path.abspath(current_primary_path)), "")
        if old_secondary:
            old_norm = os.path.normcase(os.path.abspath(old_secondary))
            for combo_index in range(secondary_combo.count()):
                candidate = str(secondary_combo.itemData(combo_index) or "")
                if candidate and os.path.normcase(os.path.abspath(candidate)) == old_norm:
                    secondary_combo.setCurrentIndex(combo_index)
                    break
        root.addWidget(QLabel("Primary PDF · main document"))
        root.addWidget(primary_combo)
        root.addWidget(QLabel("Supplementary PDF · related document"))
        root.addWidget(secondary_combo)
        note = QLabel("Only the two PDF files are linked; page selection is automatic and follows the currently visible page in each document. The files remain separate on disk, and unlinking restores both original tabs. Annotations stay in their original PDFs.")
        note.setWordWrap(True)
        note.setObjectName("dialogHint")
        root.addWidget(note)
        buttons = QDialogButtonBox(QDialogButtonBox.StandardButton.Ok | QDialogButtonBox.StandardButton.Cancel)
        buttons.accepted.connect(dialog.accept)
        buttons.rejected.connect(dialog.reject)
        root.addWidget(buttons)
        primary_combo.currentIndexChanged.connect(lambda _i: self._refresh_companion_combo(primary_combo, secondary_combo))
        self._refresh_companion_combo(primary_combo, secondary_combo)
        if dialog.exec() != QDialog.DialogCode.Accepted:
            return
        primary_path = os.path.abspath(str(primary_combo.currentData() or ""))
        secondary_value = str(secondary_combo.currentData() or "").strip()
        secondary_path = os.path.abspath(secondary_value) if secondary_value else ""
        if not primary_path:
            QMessageBox.warning(self, "Combine PDF tabs", "Choose a primary PDF.")
            return
        self._apply_linked_pdf_pair(primary_path, secondary_path, start_new_dual_chat=bool(secondary_path))

    def _apply_linked_pdf_pair(self, primary_path, secondary_path, start_new_dual_chat=False):
        """Activate a primary/supplementary PDF pair for this app session."""
        primary_path = os.path.abspath(primary_path or "")
        secondary_path = os.path.abspath(secondary_path or "") if secondary_path else ""
        if not primary_path:
            return False
        primary_key = os.path.normcase(primary_path)
        secondary_key = os.path.normcase(secondary_path) if secondary_path else ""
        if secondary_key and primary_key == secondary_key:
            QMessageBox.warning(self, "Combine PDF tabs", "The primary and supplementary PDFs must be different.")
            return False
        # Another Engo window may have changed this shared relationship.
        self._reload_linked_pair_settings()
        for old_primary, old_secondary in list(self._linked_pdf_pairs.items()):
            old_primary_key = os.path.normcase(os.path.abspath(old_primary))
            old_secondary_key = os.path.normcase(os.path.abspath(old_secondary))
            if old_primary_key in {primary_key, secondary_key} or old_secondary_key in {primary_key, secondary_key}:
                old_tab = self._open_document_tab_by_path(old_primary)
                if old_tab is not None:
                    old_tab.disable_linked_view()
                self._linked_pdf_pairs.pop(old_primary, None)
        if secondary_path:
            self._linked_pdf_pairs[primary_key] = secondary_path
        primary_tab = self._open_document_tab_by_path(primary_path)
        if primary_tab is not None:
            idx = self.tabs.indexOf(primary_tab)
            self.tabs.setCurrentIndex(idx)
            self.doc_tabbar.setCurrentIndex(idx)
        self._refresh_linked_tab_layout()
        if primary_tab is not None and hasattr(self, "ai_panel"):
            # Resolve the dual scope only after the relationship is registered and
            # the linked canvas exists. The panel must not keep the old single-PDF chat.
            self._refresh_ai_chat_context(
                primary_tab,
                start_new_dual_chat=bool(secondary_path and start_new_dual_chat)
            )
        self._refresh_linked_context_label()
        self._update_controls()
        if secondary_path:
            self.show_status(f"Combined tab ready · {Path(primary_path).name} + {Path(secondary_path).name}")
        else:
            self.show_status(f"Supplementary PDF unlinked · {Path(primary_path).name} is now independent")
        return True

    @staticmethod
    def _refresh_companion_combo(primary_combo, secondary_combo):
        primary_value = str(primary_combo.currentData() or "")
        primary_path = os.path.normcase(os.path.abspath(primary_value)) if primary_value else ""
        current_secondary = str(secondary_combo.currentData() or "")
        for i in range(secondary_combo.count()):
            value = str(secondary_combo.itemData(i) or "")
            enabled = (i == 0) or bool(value and os.path.normcase(os.path.abspath(value)) != primary_path)
            model = secondary_combo.model()
            item = model.item(i) if hasattr(model, "item") else None
            if item is not None:
                item.setEnabled(enabled)
        current_norm = os.path.normcase(os.path.abspath(current_secondary)) if current_secondary else ""
        if current_norm and current_norm == primary_path:
            secondary_combo.setCurrentIndex(0)

    def _install_tab_close_button(self, index, tab):
        """Install a DPI-stable close button inset from the tab's right edge."""
        container = QWidget(self.doc_tabbar)
        container.setObjectName("documentTabCloseContainer")
        container.setFixedSize(27, 22)
        container.setAttribute(Qt.WidgetAttribute.WA_TranslucentBackground, True)
        container.setStyleSheet("background: transparent; border: none;")
        close_layout = QHBoxLayout(container)
        close_layout.setContentsMargins(0, 0, 6, 0)
        close_layout.setSpacing(0)
        button = QToolButton(container)
        button.setObjectName("documentTabCloseButton")
        button.setIcon(make_icon("close", "#b9c6d8", 16))
        button.setIconSize(QSize(12, 12))
        button.setFixedSize(20, 20)
        button.setAutoRaise(True)
        button.setCursor(Qt.CursorShape.PointingHandCursor)
        button.setFocusPolicy(Qt.FocusPolicy.NoFocus)
        title = tab.tab_title()
        container.setToolTip(f"Close {title}")
        container.setAccessibleName(f"Close tab {title}")
        button.setToolTip(f"Close {title}")
        button.setAccessibleName(f"Close tab {title}")
        button.clicked.connect(lambda _checked=False, target=tab: self._close_tab_for_document(target))
        close_layout.addWidget(button)
        self.doc_tabbar.setTabButton(index, QTabBar.ButtonPosition.RightSide, container)
        return container

    def _close_tab_for_document(self, tab):
        """Resolve the document's current index at click time, including after tab moves."""
        index = self.tabs.indexOf(tab)
        if index < 0 and tab in self._tab_order:
            index = self._tab_order.index(tab)
        if index >= 0:
            self.close_tab(index)

    def _display_tab_title(self, tab):
        title = tab.tab_title()
        companion = self.linked_supplementary_tab(tab.path)
        if companion is not None:
            title = f"{title}  +  {Path(companion.path).name}"
        return title

    def _refresh_tab_title(self, tab, title):
        idx = self.tabs.indexOf(tab)
        if idx >= 0:
            title = self._display_tab_title(tab)
            tags = self.document_tags(tab.path)
            tab_tip = tab.path + ("\nTags: " + ", ".join(tags) if tags else "")
            self.doc_tabbar.setTabToolTip(idx, tab_tip)
            self.doc_tabbar.setTabText(idx, title)
            self._schedule_brand_title_update()
            close_button = self.doc_tabbar.tabButton(idx, QTabBar.ButtonPosition.RightSide)
            if close_button is not None:
                close_button.setToolTip(f"Close {title}")
                close_button.setAccessibleName(f"Close tab {title}")
                inner_close = close_button.findChild(QToolButton, "documentTabCloseButton")
                if inner_close is not None:
                    inner_close.setToolTip(f"Close {title}")
                    inner_close.setAccessibleName(f"Close tab {title}")
            if os.path.exists(resource_path("engopdfviewer.ico")):
                self.doc_tabbar.setTabIcon(idx, QIcon(resource_path("engopdfviewer.ico")))

    def _on_top_tab_changed(self, index):
        if 0 <= index < self.tabs.count():
            self.tabs.setCurrentIndex(index)
            # Choosing a document tab while the Files home is visible returns
            # directly to the existing document workspace.
            self._show_document_area()
        self._on_tab_changed(index)

    def _on_tabs_moved(self, source, destination):
        if source == destination or not (0 <= source < len(self._tab_order)):
            return
        # Keep an explicit tab->document order mapping. QTabBar can emit
        # currentChanged during a drag, before tabMoved, so using only stack
        # indices here can accidentally switch the active PDF.
        moved = self._tab_order.pop(source)
        self._tab_order.insert(destination, moved)
        widgets = [self.tabs.widget(i) for i in range(self.tabs.count())]
        for widget in widgets:
            self.tabs.removeWidget(widget)
        for i, widget in enumerate(self._tab_order):
            self.tabs.insertWidget(i, widget)
        selected_index = self.doc_tabbar.currentIndex()
        if 0 <= selected_index < len(self._tab_order):
            selected_widget = self._tab_order[selected_index]
            self.tabs.setCurrentWidget(selected_widget)
            self._on_tab_changed(selected_index)
        self._update_controls()

    def _on_tab_changed(self, _index):
        tab = self.active_tab()
        self._linked_view_target = tab
        if tab:
            self._on_page_changed(tab.current_page, tab.page_count)
            self.continuous_btn.setChecked(tab.scroll_mode)
            self._sync_book_unlink_button(tab)
            self._set_tool(tab.active_tool, quiet=True)
            self.delete_btn.setEnabled(bool(tab.selected_annotation is not None or tab.selected_annotations or tab.selected_page_link is not None))
            if hasattr(self, "ai_panel"):
                self.ai_panel.set_document(tab.path, Path(tab.path).name)
                self._refresh_linked_context_label()
        elif hasattr(self, "ai_panel"):
            self.ai_panel.set_document("", "No PDF open")
        self._refresh_linked_tab_layout()
        if tab is not None:
            self._refresh_tag_menu(tab)
        if tab is not None and hasattr(self, "ai_panel"):
            self._refresh_ai_chat_context(tab)
        self._update_controls()

    def _on_document_page_changed(self, source_tab: DocumentTab, current: int, total: int):
        """The last interacted linked pane controls the shared page indicator."""
        if source_tab is self._view_target_tab():
            self._on_page_changed(current, total)
            return
        worker = getattr(self, "_live_tutor_worker", None)
        if (worker is not None and worker.isRunning()
                and worker.secondary_pdf_path
                and os.path.normcase(os.path.abspath(source_tab.path)) == os.path.normcase(os.path.abspath(worker.secondary_pdf_path))
                and int(current) != int(worker.secondary_page_index)):
            path = os.path.abspath(source_tab.path)
            page_index = int(current)
            QTimer.singleShot(220, lambda p=path, pg=page_index: self._auto_sync_live_secondary_page(p, pg))

    def _on_page_changed(self, current, total):
        self.page_spin.blockSignals(True)
        self.page_spin.setRange(1, max(1, total))
        self.page_spin.setValue(current + 1 if total else 1)
        self.page_spin.blockSignals(False)
        self.page_total.setText(f"/ {total}")
        tab = self.active_tab()
        if tab:
            self.zoom_label.setText({"width": "Fit width", "page": "Fit page"}.get(tab.fit_mode, f"{int(tab.custom_scale * 100)}%"))
            self.prev_btn.setEnabled(current > 0)
            self.next_btn.setEnabled(current < total - (2 if tab.book_mode else 1))
            live_worker = getattr(self, "_live_tutor_worker", None)
            if (live_worker is not None and live_worker.isRunning()
                    and live_worker.secondary_pdf_path
                    and os.path.normcase(os.path.abspath(tab.path)) == os.path.normcase(live_worker.secondary_pdf_path)
                    and int(current) != int(live_worker.secondary_page_index)):
                path = os.path.abspath(tab.path)
                page_index = int(current)
                QTimer.singleShot(220, lambda p=path, pg=page_index: self._auto_sync_live_secondary_page(p, pg))
            if (live_worker is not None and live_worker.isRunning()
                    and os.path.normcase(os.path.abspath(tab.path)) == os.path.normcase(live_worker.pdf_path)
                    and int(current) != int(live_worker.page_index)):
                # Coalesce rapid page navigation so the live session receives only the latest page.
                path = os.path.abspath(tab.path)
                page_index = int(current)
                QTimer.singleShot(220, lambda p=path, pg=page_index: self._auto_sync_live_page(p, pg))

    def _auto_sync_live_page(self, pdf_path: str, page_index: int):
        worker = getattr(self, "_live_tutor_worker", None)
        if worker is None or not worker.isRunning():
            return
        tab = self.active_tab()
        if (tab is None or os.path.normcase(os.path.abspath(tab.path)) != os.path.normcase(os.path.abspath(pdf_path))
                or int(tab.current_page) != int(page_index)):
            return
        try:
            page_text, page_image, actual_index = self._capture_live_page(tab.path, page_index)
            if self._live_tutor_dialog is not None:
                self._live_tutor_dialog.set_page_preview(page_image, actual_index + 1, tab.page_count)
                self._live_tutor_dialog.set_status(f"Following PDF page {actual_index + 1} · live reference syncing")
                board_context = getattr(self._live_tutor_dialog, "_board_markdown", "")
            else:
                board_context = None
            worker.update_page_context(actual_index, page_text, page_image, board_context)
        except Exception as exc:
            self.show_status(f"Could not sync the page to Voice & Learn: {exc}")

    def _auto_sync_live_secondary_page(self, pdf_path: str, page_index: int):
        worker = getattr(self, "_live_tutor_worker", None)
        if worker is None or not worker.isRunning():
            return
        tab = self._open_document_tab_by_path(pdf_path)
        if tab is None or int(tab.current_page) != int(page_index):
            return
        try:
            page_text, page_image, actual_index = self._capture_live_page(tab.path, page_index)
            if self._live_tutor_dialog is not None:
                self._live_tutor_dialog.set_secondary_page_preview(page_image, actual_index + 1, tab.page_count,
                                                                   tab.path, Path(tab.path).name)
                self._live_tutor_dialog.set_status(f"Supplementary PDF page {actual_index + 1} syncing")
            worker.update_secondary_page_context(actual_index, page_text, page_image, tab.page_count)
        except Exception as exc:
            self.show_status(f"Could not sync supplementary page to Voice & Learn: {exc}")

    def _jump_to_page(self):
        tab = self._view_target_tab()
        if tab:
            tab.go_to_page(self.page_spin.value() - 1)

    def _navigate(self, direction):
        tab = self._view_target_tab()
        if not tab:
            return
        step = 2 if tab.book_mode else 1
        tab.go_to_page(tab.current_page + direction * step)

    def rotate_current_page_active(self):
        tab = self._view_target_tab() or self.active_tab()
        if tab is None:
            return
        page_number = int(tab.current_page) + 1
        if tab.rotate_pages_clockwise([tab.current_page]):
            self.show_status(f"Page {page_number} rotated 90° clockwise · Save or Ctrl+Z to undo")
            self._update_controls()

    def rotate_all_pages_active(self):
        tab = self._view_target_tab() or self.active_tab()
        if tab is None:
            return
        total = int(tab.page_count)
        if tab.rotate_pages_clockwise():
            self.show_status(f"All {total} pages rotated 90° clockwise · Save or Ctrl+Z to undo")
            self._update_controls()

    def _zoom(self, factor):
        tab = self._view_target_tab()
        if tab:
            tab.zoom_by(factor)
            self.zoom_label.setText(f"{int(tab.custom_scale * 100)}%")

    def _set_fit_mode(self, mode):
        tab = self._view_target_tab()
        if tab:
            tab.set_fit_mode(mode)
            self.zoom_label.setText("Fit width" if mode == "width" else "Fit page")

    def _sync_book_unlink_button(self, tab=None):
        """Reuse the Book control as a direct Unlink action for grouped PDFs."""
        button = getattr(self, "book_btn", None)
        if button is None:
            return
        linked = bool(tab is not None and any(self._linked_pair_for_tab(tab)))
        is_arabic_ui = str(self.settings.value("interface_language", "en", type=str) or "en").lower().startswith("ar")
        if linked:
            button.setCheckable(False)
            button.setChecked(False)
            button.setText("إلغاء الربط" if is_arabic_ui else "Unlink")
            button.setIcon(make_icon("unlink", "#e79aa5", 17))
            button.setToolTip("إلغاء ربط ملفي PDF واستعادة التبويبين الأصليين" if is_arabic_ui else "Unlink this PDF pair and restore both original tabs")
            button.setAccessibleName("إلغاء ربط ملفي PDF" if is_arabic_ui else "Unlink the currently combined PDF pair")
            button.setEnabled(True)
        else:
            button.setCheckable(True)
            button.setText("ككتاب" if is_arabic_ui else "Book")
            button.setIcon(make_icon("book", "#b7c6dc", 18))
            button.setToolTip("ككتاب · عرض صفحتين جنبًا إلى جنب، ويمكن دمجه مع التمرير" if is_arabic_ui else "Book · show two pages side by side; can be combined with Scroll")
            button.setAccessibleName("عرض صفحتين ككتاب" if is_arabic_ui else "Book view · show two pages side by side")
            button.setChecked(bool(tab.book_mode) if tab is not None else False)
            button.setEnabled(tab is not None)

    def _handle_book_or_unlink(self, checked=False):
        # The last clicked pane is the target. It can be the supplementary PDF,
        # so resolve the pair in either direction before deciding Book vs Unlink.
        tab = self._view_target_tab() or self.active_tab()
        if tab is None:
            return
        primary, companion = self._linked_pair_for_tab(tab)
        if primary is not None and companion is not None:
            primary_name = Path(primary.path).name
            companion_name = Path(companion.path).name
            self._unlink_document_relationships(tab)
            self._refresh_linked_tab_layout()
            self._refresh_linked_context_label()
            # Preserve focus on the pane the user had selected; it is now an
            # ordinary independent tab. Its Book mode remains OFF after unlink.
            target_index = self.tabs.indexOf(tab)
            if target_index >= 0:
                self.doc_tabbar.setCurrentIndex(target_index)
                self.tabs.setCurrentIndex(target_index)
                self._linked_view_target = tab
            self._refresh_selector_tool_button(tab)
            self._refresh_view_target_style()
            self._refresh_tag_menu(tab)
            self._refresh_ai_chat_context(tab)
            self._refresh_linked_context_label()
            self._update_controls()
            self.show_status(f"PDF pair unlinked · {primary_name} and {companion_name} are independent tabs")
            return
        self._set_layout_option("book", checked)

    def _set_layout_option(self, option, checked):
        # Scroll is pair-wide in linked mode. Book belongs to the focused PDF
        # when the documents are independent.
        target_tab = self._view_target_tab() or self.active_tab()
        owner_tab = self.active_tab()
        if target_tab is None or owner_tab is None:
            return
        pair_primary, pair_secondary = self._linked_pair_for_tab(target_tab)
        if pair_primary is not None and pair_secondary is not None:
            tab = pair_primary
            book = False
            scroll = bool(checked) if option == "scroll" else tab.scroll_mode
        else:
            tab = target_tab
            book = bool(checked) if option == "book" else tab.book_mode
            scroll = bool(checked) if option == "scroll" else tab.scroll_mode
        tab.set_layout_modes(book=book, scroll=scroll)
        self._sync_book_unlink_button(tab)
        self.continuous_btn.setChecked(tab.scroll_mode)
        self.next_btn.setEnabled(tab.current_page < tab.page_count - (2 if tab.book_mode else 1))
        self._update_controls()

    def _set_view_mode(self, mode):
        """Compatibility hook for older actions; toolbar controls use independent toggles."""
        tab = self.active_tab()
        if tab:
            tab.set_view_mode(mode)
            self.continuous_btn.setChecked(tab.scroll_mode)
            self._sync_book_unlink_button(tab)

    def _select_tool_button_clicked(self):
        tab = self._view_target_tab()
        # Clicking the main face reselects the currently displayed Select/Hand mode;
        # choosing the other mode is intentionally done from the dropdown.
        self._set_tool("pan" if tab is not None and tab.active_tool == "pan" else "select")

    def _refresh_select_tool_menu(self, tab=None):
        if not hasattr(self, "select_action"):
            return
        tab = tab or self._view_target_tab()
        mode = str(getattr(tab, "active_tool", "select") or "select") if tab else "select"
        self.select_action.setChecked(mode == "select")
        self.pan_action.setChecked(mode == "pan")

    def _refresh_selector_tool_button(self, tab=None):
        if not hasattr(self, "select_tool_btn"):
            return
        tab = tab or self._view_target_tab()
        mode = str(getattr(tab, "active_tool", "select") or "select") if tab else "select"
        is_pan = mode == "pan"
        theme = str(self.settings.value("ui_theme", "dark", type=str) or "dark").lower()
        icon_color = "#33445b" if theme == "light" else ("#d6e4ff" if theme == "midnight" else "#e4e4e4")
        icon_name = "hand" if is_pan else "select"
        self.select_tool_btn.setIcon(make_icon(icon_name, icon_color, 18))
        self.select_tool_btn.setProperty("engoIconName", icon_name)
        self.select_tool_btn.setProperty("activeTool", True)
        self.select_tool_btn.setChecked(mode in ("select", "pan"))
        if str(self.settings.value("interface_language", "en", type=str) or "en").lower().startswith("ar"):
            self.select_tool_btn.setToolTip("أداة اليد · اسحب لتحريك الصفحة" if is_pan else "أداة التحديد · استخدم القائمة للتبديل إلى اليد")
            self.select_tool_btn.setAccessibleName("تحديد / يد")
        else:
            self.select_tool_btn.setToolTip("Hand · drag to pan the page" if is_pan else "Select · use the menu to switch to Hand/Pan")
            self.select_tool_btn.setAccessibleName("Select / Hand tool")
        self.select_action.setIcon(make_icon("select", icon_color, 18))
        self.pan_action.setIcon(make_icon("hand", icon_color, 18))
        self._refresh_select_tool_menu(tab)
        self.select_tool_btn.style().unpolish(self.select_tool_btn)
        self.select_tool_btn.style().polish(self.select_tool_btn)
        self.select_tool_btn.update()

    def _set_tool(self, tool, quiet=False):
        if tool not in self.tool_buttons and tool != "pan":
            return
        tab = self._view_target_tab()
        if tab:
            tab.set_tool(tool)
        for key, button in self.tool_buttons.items():
            active = (key == tool) or (key == "select" and tool == "pan")
            button.setProperty("activeTool", active)
            if button.isChecked() != active:
                button.setChecked(active)
            button.style().unpolish(button)
            button.style().polish(button)
            button.update()
        self._refresh_selector_tool_button(tab)
        self._refresh_view_target_style()
        if not quiet and hasattr(self, "context_help_label"):
            self._show_selected_tool_context_help(tool)

    def _chat_focus_pane_width(self) -> int:
        """Return the actual width available to splitter panes, excluding visible handles."""
        splitter_width = max(1, int(self.workspace.width()))
        visible_panes = 0
        for index in range(self.workspace.count()):
            widget = self.workspace.widget(index)
            if widget is not None and not widget.isHidden():
                visible_panes += 1
        visible_handles = max(0, visible_panes - 1)
        return max(1, splitter_width - visible_handles * int(self.workspace.handleWidth()))

    def _stop_chat_focus_animations(self):
        animation = getattr(self, "_chat_focus_animation", None)
        if animation is not None:
            try:
                animation.stop()
                animation.deleteLater()
            except RuntimeError:
                pass
            self._chat_focus_animation = None
        # Chrome no longer owns separate QPropertyAnimation timers. Its height
        # is driven by the same QVariantAnimation as the workspace splitter.
        for animation in list(getattr(self, "_chat_focus_chrome_animations", [])):
            try:
                animation.stop()
                animation.deleteLater()
            except RuntimeError:
                pass
        self._chat_focus_chrome_animations = []
        self._chat_focus_chrome_tracks = []
        timer = getattr(self, "_chat_transcript_resize_timer", None)
        if timer is not None:
            timer.stop()
        live_reflow_timer = getattr(self, "_chat_transcript_live_reflow_timer", None)
        if live_reflow_timer is not None:
            live_reflow_timer.stop()
        self._chat_focus_transition_active = False

    def _prepare_chat_focus_chrome_tracks(self, entering: bool):
        """Prepare toolbar/tab/status heights for the shared focus animation clock."""
        saved = self._chat_focus_restore or {}
        visibility = saved.get("chrome_visible", {})
        heights = saved.get("chrome_heights", {})
        maximums = saved.get("chrome_maximum_heights", {})
        tracks = []

        for widget in (self.tab_strip, self.topbar, self.status):
            key = widget.objectName()
            should_be_visible = bool(visibility.get(key, not widget.isHidden()))
            restore_maximum = int(maximums.get(key, 16777215))
            if not should_be_visible:
                if not entering:
                    widget.hide()
                    widget.setMaximumHeight(restore_maximum)
                continue

            target_height = max(1, int(heights.get(key, widget.sizeHint().height())))
            if entering:
                if widget.isHidden():
                    continue
                start_height = max(0, min(int(widget.height()), target_height))
                widget.setMaximumHeight(start_height)
                end_height = 0
            else:
                if widget.isHidden():
                    # Reveal from zero, not from the stale height kept while hidden.
                    widget.setMaximumHeight(0)
                    widget.show()
                    start_height = 0
                else:
                    # A reversed transition continues from its current visible height.
                    start_height = max(0, min(int(widget.height()), target_height))
                    widget.setMaximumHeight(start_height)
                end_height = target_height

            tracks.append({
                "widget": widget,
                "start": start_height,
                "end": end_height,
                "restore_maximum": restore_maximum,
                "last_height": start_height,
            })
        return tracks

    def _on_workspace_splitter_moved(self, *_args):
        """Keep assistant messages responsive while the user drags the chat divider."""
        if not hasattr(self, "ai_panel") or not self.ai_panel.isVisible():
            return
        # Chat Focus has its own single-clock live reflow; don't run a second
        # resize loop while that animation is controlling the splitter.
        if getattr(self, "_chat_focus_transition_active", False):
            return
        live_timer = getattr(self, "_chat_transcript_live_reflow_timer", None)
        if live_timer is not None and not live_timer.isActive():
            live_timer.start()
        resize_timer = getattr(self, "_chat_transcript_resize_timer", None)
        if resize_timer is not None:
            # Restart this inactivity timer on every drag event. Its timeout
            # stops live updates and performs a complete, batched transcript pass.
            resize_timer.start(150)

    def _reflow_visible_chat_transcript_during_resize(self):
        """Resize only on-screen bubbles at the current viewport width, at ~22 FPS."""
        if (not hasattr(self, "ai_panel") or not self.ai_panel.isVisible()
                or getattr(self, "_chat_focus_transition_active", False)):
            return
        panel = self.ai_panel
        viewport_width = int(panel.transcript.viewport().width())
        visible_bubbles = panel._transcript_bubbles_in_view(overscan=0.30)
        if visible_bubbles:
            panel._reflow_bubble_subset(visible_bubbles, viewport_width)

    def _finish_chat_transcript_resize(self):
        """Stop live drag updates and catch every off-screen message up to the final width."""
        live_timer = getattr(self, "_chat_transcript_live_reflow_timer", None)
        if live_timer is not None:
            live_timer.stop()
        if hasattr(self, "ai_panel") and self.ai_panel.isVisible():
            self.ai_panel.reflow_transcript_bubbles_batched()

    def _schedule_chat_transcript_reflow(self, delay: int = 130):
        """Reflow existing bubbles once the animated panel width has settled."""
        timer = getattr(self, "_chat_transcript_resize_timer", None)
        if timer is not None:
            timer.start(max(0, int(delay)))
        else:
            QTimer.singleShot(max(0, int(delay)), self.ai_panel.reflow_transcript_bubbles_batched)

    def _start_chat_focus_width_animation(self, start_width: int, end_width: int,
                                          finished_callback, duration: int = 720,
                                          chrome_entering: bool | None = None):
        """Animate the chat and app chrome using one clock and one splitter coordinate system.

        Widths are measured in pane pixels (the splitter width minus its visible handles),
        never in the splitter's outer width. Visible transcript bubbles are reflowed in
        tiny rotating batches so QTextDocument layout cannot block the animation at a
        particular width breakpoint.
        """
        animation = QVariantAnimation(self)
        animation.setDuration(int(duration))
        animation.setStartValue(0.0)
        animation.setEndValue(1.0)
        animation.setEasingCurve(QEasingCurve.Type.InOutCubic)
        last_position = None
        last_reflow_at = 0.0
        last_reflow_width = -1
        pane_total_start = self._chat_focus_pane_width()
        start_width = max(0, min(pane_total_start, int(start_width)))
        end_width = max(0, min(pane_total_start, int(end_width)))
        chrome_tracks = (self._prepare_chat_focus_chrome_tracks(chrome_entering)
                         if chrome_entering is not None else [])
        self._chat_focus_chrome_tracks = chrome_tracks

        # Map the visible message set once. Re-scanning a long chat history every
        # animation frame is itself expensive and can create a width-specific hitch.
        visible_reflow_bubbles = self.ai_panel._transcript_bubbles_in_view(overscan=0.35)
        reflow_cursor = 0
        reflow_batch_size = 2

        def reflow_visible_batch(viewport_width: int):
            nonlocal reflow_cursor
            if not visible_reflow_bubbles:
                return
            count = len(visible_reflow_bubbles)
            take = min(reflow_batch_size, count)
            batch = [visible_reflow_bubbles[(reflow_cursor + offset) % count]
                     for offset in range(take)]
            self.ai_panel._reflow_bubble_subset(batch, viewport_width)
            reflow_cursor = (reflow_cursor + take) % count

        def apply_progress(progress):
            nonlocal last_position, last_reflow_at, last_reflow_width
            value = max(0.0, min(1.0, float(progress)))
            pane_total = self._chat_focus_pane_width()
            width = int(round(start_width + (end_width - start_width) * value))
            width = max(0, min(pane_total, width))
            handle_position = max(0, min(pane_total, pane_total - width))
            if handle_position != last_position:
                self.workspace.moveSplitter(handle_position, 1)
                last_position = handle_position

            # Drive the top chrome from this exact frame too; it owns no separate clock.
            for track in chrome_tracks:
                height = int(round(track["start"] +
                                   (track["end"] - track["start"]) * value))
                if height != track["last_height"]:
                    track["widget"].setMaximumHeight(max(0, height))
                    track["last_height"] = height

            if self.ai_panel.isVisible():
                now = time.monotonic()
                viewport_width = int(self.ai_panel.transcript.viewport().width())
                if (abs(viewport_width - last_reflow_width) >= 7
                        and now - last_reflow_at >= 0.040):
                    reflow_visible_batch(viewport_width)
                    last_reflow_at = now
                    last_reflow_width = viewport_width

        # Prime only the first small batch; the rest follows the live width updates.
        if self.ai_panel.isVisible():
            viewport_width = int(self.ai_panel.transcript.viewport().width())
            reflow_visible_batch(viewport_width)
            last_reflow_width = viewport_width
            last_reflow_at = time.monotonic()

        def finish_transition():
            for track in chrome_tracks:
                track["widget"].setMaximumHeight(max(0, int(track["end"])))
                track["last_height"] = int(track["end"])
            finished_callback()

        animation.valueChanged.connect(apply_progress)
        animation.finished.connect(finish_transition)
        self._chat_focus_animation = animation
        animation.start()

    def toggle_chat_focus_mode(self, force: bool | None = None, animate: bool = True):
        """Expand the existing chat into a distraction-free, full-workspace view."""
        entering = (not self._chat_focus_mode) if force is None else bool(force)
        if entering == self._chat_focus_mode:
            return
        if entering:
            if getattr(self, "_files_screen_active", False):
                return
            if not self.active_tab():
                self.show_status("Open a PDF before entering chat focus mode")
                return
            if not self.ai_panel.isVisible():
                self._animate_ai_panel(True)
                QTimer.singleShot(260, lambda: self.toggle_chat_focus_mode(True, animate=animate)
                                  if self.ai_panel.isVisible() and not self._chat_focus_mode else None)
                return
            self._enter_chat_focus_mode(animate=animate)
        else:
            self._leave_chat_focus_mode(animate=animate)

    def _enter_chat_focus_mode(self, animate: bool = True):
        if self._chat_focus_mode or not self.ai_panel.isVisible():
            return
        self._stop_chat_focus_animations()
        if getattr(self, "_view_animation", None) is not None:
            try:
                self._view_animation.stop()
            except RuntimeError:
                pass
            self._view_animation = None

        sizes = list(self.workspace.sizes())
        total_width = max(1, self.workspace.width())
        chat_width = int(sizes[1]) if len(sizes) > 1 and sizes[1] > 0 else max(405, self.ai_panel.width())
        chat_width = max(0, min(total_width, chat_width))
        board_width = int(sizes[2]) if len(sizes) > 2 else 0
        # If the user reverses an exit animation, keep the original pre-focus
        # snapshot rather than saving the temporary in-between widget constraints.
        if self._chat_focus_restore is None:
            self._chat_focus_restore = {
                "workspace_sizes": sizes[:3],
                "chat_width": chat_width,
                "board_width": board_width,
                "board_visible": self.teach_board.isVisible(),
                "panel_minimum_width": self.ai_panel.minimumWidth(),
                "panel_maximum_width": self.ai_panel.maximumWidth(),
                "document_minimum_width": self.document_host.minimumWidth(),
                "document_maximum_width": self.document_host.maximumWidth(),
                "chrome_visible": {
                    self.tab_strip.objectName(): not self.tab_strip.isHidden(),
                    self.topbar.objectName(): not self.topbar.isHidden(),
                    self.status.objectName(): not self.status.isHidden(),
                },
                "chrome_heights": {
                    widget.objectName(): max(1, int(widget.height()))
                    for widget in (self.tab_strip, self.topbar, self.status)
                },
                "chrome_maximum_heights": {
                    widget.objectName(): int(widget.maximumHeight())
                    for widget in (self.tab_strip, self.topbar, self.status)
                },
                "topbar_maximum_height": self.topbar.maximumHeight(),
                "window_title": self.windowTitle(),
                "ai_checked": self.ai_chat_btn.isChecked(),
            }
        self._chat_focus_mode = True
        self.ai_panel.hide_chat_content_for_transition()
        self.ai_panel.focus_mode_btn.setEnabled(False)
        self.setWindowTitle("Engo AI Chat")
        self.ai_panel.set_focus_mode_button(True)
        self.ai_chat_btn.setChecked(True)

        # The board is a companion panel, not part of the focused chat surface.
        self.teach_board.hide()
        self.document_host.setMinimumWidth(0)
        self.ai_panel.setMinimumWidth(0)
        self.ai_panel.setMaximumWidth(16777215)
        self.ai_panel.show()

        if animate:
            # Keep existing bubbles intact while the pane moves. Visible messages
            # are reflowed at a coalesced cadence inside the shared animation loop.
            pane_total = self._chat_focus_pane_width()
            chat_width = max(0, min(pane_total, chat_width))
            self._chat_focus_transition_active = True
            self.workspace.setSizes([max(0, pane_total - chat_width), chat_width, 0])
            self._start_chat_focus_width_animation(
                chat_width, pane_total, self._finish_chat_focus_enter, duration=520,
                chrome_entering=True
            )
        else:
            for widget in (self.tab_strip, self.topbar, self.status):
                widget.hide()
                widget.setMaximumHeight(int(self._chat_focus_restore.get(
                    "chrome_maximum_heights", {}).get(widget.objectName(), 16777215)))
            self._finish_chat_focus_enter()

    def _finish_chat_focus_enter(self):
        if not self._chat_focus_mode:
            return
        self.document_host.hide()
        self.teach_board.hide()
        self.ai_panel.setMaximumWidth(16777215)
        self.ai_panel.setMinimumWidth(0)
        self.ai_panel.show()
        # The chrome has reached zero on the shared animation clock. Hide it now
        # and restore its unconstrained maximum only after it is out of the layout.
        saved = self._chat_focus_restore or {}
        maximums = saved.get("chrome_maximum_heights", {})
        for widget in (self.tab_strip, self.topbar, self.status):
            widget.hide()
            widget.setMaximumHeight(int(maximums.get(widget.objectName(), 16777215)))
        self._chat_focus_chrome_tracks = []
        pane_total = self._chat_focus_pane_width()
        self.workspace.setSizes([0, pane_total, 0])
        self.ai_panel.reveal_chat_content(stagger_messages=True)
        self.ai_panel.prompt_edit.setFocus()
        self.ai_panel.focus_mode_btn.setEnabled(True)
        self._chat_focus_transition_active = False
        self._schedule_chat_transcript_reflow(120)

    def _leave_chat_focus_mode(self, animate: bool = True):
        if not self._chat_focus_mode:
            return
        # Capture the live width before stopping an in-flight animation. This also
        # makes a quick reverse-toggle continue from the current position smoothly.
        live_sizes = list(self.workspace.sizes())
        pane_total = self._chat_focus_pane_width()
        live_chat_width = (int(live_sizes[1]) if len(live_sizes) > 1 and live_sizes[1] > 0
                           else int(self.ai_panel.width()))
        live_chat_width = max(0, min(pane_total, live_chat_width))
        self._stop_chat_focus_animations()
        saved = self._chat_focus_restore or {}
        self._chat_focus_mode = False
        if animate:
            self.ai_panel.animate_chat_content_close()
        else:
            self.ai_panel.hide_chat_content_for_transition()
        self.ai_panel.focus_mode_btn.setEnabled(False)
        self.setWindowTitle(str(saved.get("window_title") or APP_NAME))
        self.ai_panel.set_focus_mode_button(False)

        chat_width = max(405, int(saved.get("chat_width", 500) or 500))
        chat_width = min(chat_width, max(0, pane_total - 220)) if pane_total > 220 else pane_total
        self.document_host.setMinimumWidth(0)
        self.document_host.show()
        self.ai_panel.setMinimumWidth(0)
        self.ai_panel.setMaximumWidth(16777215)
        self.ai_panel.show()
        self.teach_board.hide()

        if animate:
            pane_total = self._chat_focus_pane_width()
            live_chat_width = max(0, min(pane_total, live_chat_width))
            chat_width = max(0, min(pane_total, chat_width))
            self._chat_focus_transition_active = True
            self.workspace.setSizes([max(0, pane_total - live_chat_width), live_chat_width, 0])
            self._start_chat_focus_width_animation(
                live_chat_width, chat_width, self._finish_chat_focus_exit, duration=520,
                chrome_entering=False
            )
        else:
            for widget in (self.tab_strip, self.topbar, self.status):
                visible = bool(saved.get("chrome_visible", {}).get(widget.objectName(), True))
                widget.setVisible(visible)
                widget.setMaximumHeight(int(saved.get("chrome_maximum_heights", {}).get(
                    widget.objectName(), 16777215)))
            self._finish_chat_focus_exit()

    def _finish_chat_focus_exit(self):
        if self._chat_focus_mode:
            return
        saved = self._chat_focus_restore or {}
        self.document_host.show()
        self.document_host.setMinimumWidth(int(saved.get("document_minimum_width", 0)))
        self.document_host.setMaximumWidth(int(saved.get("document_maximum_width", 16777215)))
        self.ai_panel.setMinimumWidth(int(saved.get("panel_minimum_width", 405)))
        self.ai_panel.setMaximumWidth(int(saved.get("panel_maximum_width", 720)))
        if saved.get("board_visible", False):
            self.teach_board.show()
        else:
            self.teach_board.hide()
        self.ai_panel.reveal_chat_content(stagger_messages=True)

        saved_sizes = saved.get("workspace_sizes") or []
        if len(saved_sizes) >= 3 and sum(max(0, int(v)) for v in saved_sizes[:3]) > 0:
            old_total = max(1, sum(max(0, int(v)) for v in saved_sizes[:3]))
            new_total = self._chat_focus_pane_width()
            restored = [max(0, round(new_total * max(0, int(v)) / old_total)) for v in saved_sizes[:3]]
            self.workspace.setSizes(restored)
        else:
            pane_total = self._chat_focus_pane_width()
            fallback_chat = min(int(saved.get("chat_width", 500)), max(0, pane_total - 1))
            self.workspace.setSizes([max(1, pane_total - fallback_chat), fallback_chat, 0])
        self.ai_chat_btn.setChecked(bool(saved.get("ai_checked", True)))
        for widget in (self.tab_strip, self.topbar, self.status):
            widget.setMaximumHeight(int(saved.get("chrome_maximum_heights", {}).get(
                widget.objectName(), 16777215)))
            widget.setVisible(bool(saved.get("chrome_visible", {}).get(widget.objectName(), True)))
        self.topbar.setMaximumHeight(int(saved.get("topbar_maximum_height", 16777215)))
        self.ai_panel.focus_mode_btn.setEnabled(True)
        self._chat_focus_restore = None
        self._chat_focus_transition_active = False
        self._schedule_toolbar_density_update()
        QTimer.singleShot(0, self._apply_toolbar_density)
        QTimer.singleShot(90, self._apply_toolbar_density)
        QTimer.singleShot(0, self._relayout_active_pdf_after_focus)
        self._schedule_chat_transcript_reflow(140)

    def _relayout_active_pdf_after_focus(self):
        if self._chat_focus_mode or self._chat_focus_transition_active:
            return
        tab = self.active_tab()
        if tab is not None:
            tab._relayout()


    def _relayout_active_pdf_after_panel_animation(self):
        """Render the PDF sharply at its final size once the chat motion has ended."""
        try:
            tab = self.active_tab()
            if tab is not None:
                tab._relayout()
                tab.canvas.update()
        except (RuntimeError, AttributeError):
            pass

    def _animate_ai_panel(self, show: bool, preferred_width: int | None = None, board_width: int | None = None):
        """Reveal/collapse the text chat with the same soft width animation as the Sidebar."""
        if getattr(self, "_files_screen_active", False):
            return
        panel = self.ai_panel
        if getattr(self, "_view_animation", None) is not None:
            try:
                self._view_animation.stop()
            except RuntimeError:
                pass
            self._view_animation = None

        self._chat_panel_anim_until = 0.0
        # Preserve the same page-relative reading point while the chat closes too.
        # Releasing the anchor before the close animation lets the wider PDF canvas
        # reflow and changes the vertical scroll position when the chat disappears.
        close_anchor_tab = None
        if not show and panel.isVisible():
            close_anchor_tab = self.active_tab()
            if close_anchor_tab is not None:
                try:
                    close_anchor_tab.begin_chat_viewport_anchor_preservation()
                except (RuntimeError, AttributeError):
                    close_anchor_tab = None
        total_width = max(1, self.workspace.width())
        if show:
            if panel.isVisible() and panel.width() > 0:
                self.ai_chat_btn.setChecked(True)
                if preferred_width:
                    current_sizes = list(self.workspace.sizes())
                    current_board = current_sizes[2] if len(current_sizes) > 2 else 0
                    chat = max(320, min(720, int(preferred_width)))
                    self.workspace.setSizes([max(1, total_width - chat - current_board), chat, current_board])
                    # setSizes() is programmatic and does not reliably emit splitterMoved.
                    # Explicitly refresh assistant widths after the viewport gets its new geometry.
                    QTimer.singleShot(0, self._reflow_visible_chat_transcript_during_resize)
                    QTimer.singleShot(45, self._finish_chat_transcript_resize)
                panel.prompt_edit.setFocus()
                return

            # Capture the visible page-relative reading point before the reader
            # viewport gets narrower. DocumentTab restores this anchor during each
            # resize pass, so opening chat does not pull the PDF toward another page.
            viewport_anchor_tab = self.active_tab()
            if viewport_anchor_tab is not None:
                try:
                    viewport_anchor_tab.begin_chat_viewport_anchor_preservation()
                except (RuntimeError, AttributeError):
                    viewport_anchor_tab = None

            if board_width is None:
                sizes_now = list(self.workspace.sizes())
                board_width = sizes_now[2] if len(sizes_now) > 2 and self.teach_board.isVisible() else 0
            board_width = max(0, min(int(board_width or 0), max(0, total_width - 320)))
            chat_width = int(preferred_width or min(660, max(430, int(total_width * 0.34))))
            chat_width = max(320, min(chat_width, max(320, total_width - board_width - 260)))

            panel.setMinimumWidth(0)
            panel.setMaximumWidth(0)
            panel.prepare_chat_content_transition()
            panel.show()
            self.workspace.setSizes([max(1, total_width - board_width), 0, board_width])
            self.ai_chat_btn.setChecked(True)

            self._chat_panel_anim_until = time.monotonic() + 0.240 + 0.32
            anim = QPropertyAnimation(panel, b"maximumWidth", self)
            anim.setDuration(240)
            anim.setStartValue(0)
            anim.setEndValue(chat_width)
            anim.setEasingCurve(QEasingCurve.Type.OutCubic)
            anim.valueChanged.connect(
                lambda value, total=total_width, board=board_width: self.workspace.setSizes(
                    [max(0, total - max(0, min(total, int(value))) - board),
                     max(0, min(total, int(value))), board]
                )
            )
            # Keep visible assistant messages in step with the opening animation too.
            # setSizes() is not a user drag, so splitterMoved is not a dependable trigger.
            anim.valueChanged.connect(
                lambda _value: self._reflow_visible_chat_transcript_during_resize()
            )

            def finish_open(p=panel, target=chat_width, board=board_width, anchor_tab=viewport_anchor_tab):
                try:
                    self._chat_panel_anim_until = 0.0
                    p.setMaximumWidth(720)
                    p.setMinimumWidth(405)
                    p.reveal_chat_content(stagger_messages=True)
                    now = max(1, self.workspace.width())
                    self.workspace.setSizes([max(1, now - target - board), target, board])
                    p.prompt_edit.setFocus()
                    # The transcript may have been rendered while this panel was hidden,
                    # when its viewport reported a tiny/default width. Reflow the complete
                    # history only after the final splitter geometry has been applied.
                    QTimer.singleShot(35, self._finish_chat_transcript_resize)
                    QTimer.singleShot(0, self._relayout_active_pdf_after_panel_animation)
                    if anchor_tab is not None:
                        # Let the final coalesced PDF layout finish, then release
                        # the temporary anchor so normal user scrolling is untouched.
                        QTimer.singleShot(135, anchor_tab.end_chat_viewport_anchor_preservation)
                except RuntimeError:
                    if anchor_tab is not None:
                        try:
                            anchor_tab.end_chat_viewport_anchor_preservation()
                        except Exception:
                            pass
            anim.finished.connect(finish_open)
            self._view_animation = anim
            anim.start()
        else:
            if not panel.isVisible():
                self.ai_chat_btn.setChecked(False)
                return
            start_width = max(1, panel.width())
            current_sizes = list(self.workspace.sizes())
            board_width = (max(0, int(current_sizes[2]))
                           if len(current_sizes) > 2 and self.teach_board.isVisible() else 0)
            panel.setMinimumWidth(0)
            panel.setMaximumWidth(start_width)
            panel.animate_chat_content_close()
            self._chat_panel_anim_until = time.monotonic() + 0.210 + 0.32
            anim = QPropertyAnimation(panel, b"maximumWidth", self)
            anim.setDuration(210)
            anim.setStartValue(start_width)
            anim.setEndValue(0)
            anim.setEasingCurve(QEasingCurve.Type.InCubic)
            # Drive the splitter as the panel width changes. With the workspace
            # forced LTR above, the right edge remains docked while the left
            # edge travels back toward the right, reversing the opening sweep.
            anim.valueChanged.connect(
                lambda value, total=total_width, board=board_width: self.workspace.setSizes(
                    [max(0, total - max(0, min(total, int(value))) - board),
                     max(0, min(total, int(value))), board]
                )
            )
            self.ai_chat_btn.setChecked(False)

            def finish_close(p=panel, anchor_tab=close_anchor_tab):
                try:
                    self._chat_panel_anim_until = 0.0
                    p.hide()
                    p.setMaximumWidth(720)
                    p.setMinimumWidth(405)
                    self.teach_board.hide()
                    self.workspace.setSizes([max(1, self.workspace.width()), 0, 0])
                    self._set_default_context_help(force=True)
                    QTimer.singleShot(0, self._relayout_active_pdf_after_panel_animation)
                    # Closing chat must return keyboard focus to the PDF canvas.
                    # Otherwise the hidden prompt editor keeps focus and prevents
                    # the double-Space reader shortcut from being recognized.
                    closed_tab = self.active_tab()
                    if closed_tab is not None:
                        QTimer.singleShot(30, lambda t=closed_tab: getattr(t, "canvas", None).setFocus()
                                          if getattr(t, "canvas", None) is not None else None)
                    if anchor_tab is not None:
                        # Let the final full-width PDF layout settle while the
                        # page-relative anchor is still active, then release it.
                        QTimer.singleShot(160, anchor_tab.end_chat_viewport_anchor_preservation)
                except RuntimeError:
                    if anchor_tab is not None:
                        try:
                            anchor_tab.end_chat_viewport_anchor_preservation()
                        except (RuntimeError, AttributeError):
                            pass
            anim.finished.connect(finish_close)
            self._view_animation = anim
            anim.start()

    def toggle_ai_panel(self):
        if self._chat_focus_mode:
            self.toggle_chat_focus_mode(False)
            return
        if getattr(self, "_files_screen_active", False):
            self.ai_chat_btn.setChecked(False)
            return
        if not self.active_tab():
            self.ai_chat_btn.setChecked(False)
            self.show_status("Open a PDF before starting an AI chat")
            return
        self._animate_ai_panel(not self.ai_panel.isVisible())

    def start_ai_region_selection(self):
        tab = self.active_tab()
        is_ar = self._context_help_language() == "ar"
        if not tab:
            self.show_status("افتح ملف PDF أولًا" if is_ar else "Open a PDF first")
            return
        if not self.ai_panel.isVisible():
            self._animate_ai_panel(True)
        self.ai_panel.set_document(tab.path, Path(tab.path).name)
        for key, button in self.tool_buttons.items():
            button.setChecked(key == "select")
        tab.set_tool("ai_select")
        self._show_selected_tool_context_help("ai_select")
        self.show_status(
            "اسحب مستطيلًا حول النص أو المعادلة أو الرسم أو الكتابة اليدوية لإرفاقها بسؤال AI · اضغط Esc للإلغاء"
            if is_ar else
            "Drag around text, an equation, diagram, or handwriting to attach it to your AI question · Press Esc to cancel"
        )

    def _capture_live_page(self, pdf_path: str, page_index: int):
        """Render the exact PDF page using the same saved page theme as the main viewer."""
        absolute_path = os.path.abspath(pdf_path)
        theme_tab = None
        for i in range(self.tabs.count()):
            candidate = self.tabs.widget(i)
            if isinstance(candidate, DocumentTab) and os.path.normcase(os.path.abspath(candidate.path)) == os.path.normcase(absolute_path):
                theme_tab = candidate
                break
        with fitz.open(absolute_path) as doc:
            if doc.page_count <= 0:
                raise RuntimeError("The PDF has no pages.")
            page_index = max(0, min(int(page_index), doc.page_count - 1))
            page = doc.load_page(page_index)
            text = str(page.get_text("text") or "").strip()
            scale = min(2.2, 1700.0 / max(float(page.rect.width), float(page.rect.height), 1.0))
            pix = page.get_pixmap(matrix=fitz.Matrix(scale, scale), alpha=False, annots=True)
            image = Image.frombytes("RGB", (pix.width, pix.height), pix.samples)
            # DocumentCanvas applies this exact grayscale-to-custom-colors transformation
            # when dark page theme is enabled. Mirror it here so Voice & Learn's page preview
            # looks like the page the user is actually viewing, not the unthemed original.
            if theme_tab is not None:
                image = apply_page_theme_to_image(
                    image, theme_tab.dark_mode,
                    str(theme_tab.bg_color or DEFAULT_BG),
                    str(theme_tab.ink_color or DEFAULT_INK),
                    smart=bool(getattr(theme_tab, "smart_page_theme", False)),
                )
            image.thumbnail((1700, 1700), Image.Resampling.LANCZOS)
            buffer = io.BytesIO()
            image.save(buffer, format="JPEG", quality=88, optimize=True)
            return text[:16000], buffer.getvalue(), page_index

    def _unlock_toolbar_after_tutor_close(self):
        worker = getattr(self, "_live_tutor_worker", None)
        if worker is None or not _qt_thread_is_running(worker):
            self._live_tutor_toolbar_locked = False
            self._toolbar_density_user_resize_pending = False

    def open_live_tutor(self):
        tab = self.active_tab()
        worker = self._live_tutor_worker
        worker_running = _qt_thread_is_running(worker)
        if tab is None and not worker_running:
            self.show_status("Open a PDF before starting Voice & Learn")
            return
        if worker is not None and not worker_running:
            self._live_tutor_worker = None
            worker = None
        companion = self.linked_supplementary_tab(tab.path) if tab is not None else None

        # Create/connect the native PyQt dialog once, then reuse it after it is closed.
        try:
            dialog = self._live_tutor_dialog
            if dialog is None:
                dialog = LiveTutorDialog(self)
                dialog.startRequested.connect(lambda d=dialog: self.start_live_tutor(d))
                dialog.stopRequested.connect(self.stop_live_tutor)
                dialog.pauseRequested.connect(self.set_live_tutor_paused)
                dialog.refreshRequested.connect(lambda d=dialog: self.refresh_live_tutor_page(d))
                dialog.previousPageRequested.connect(lambda d=dialog: self.navigate_live_tutor_page(-1, d))
                dialog.nextPageRequested.connect(lambda d=dialog: self.navigate_live_tutor_page(1, d))
                dialog.secondaryPreviousPageRequested.connect(lambda d=dialog: self.navigate_live_tutor_secondary_page(-1, d))
                dialog.secondaryNextPageRequested.connect(lambda d=dialog: self.navigate_live_tutor_secondary_page(1, d))
                dialog.voicePreferencesChanged.connect(self._save_live_tutor_voice_preferences)
                dialog.lessonDetailChanged.connect(self._save_live_tutor_detail_preference)
                dialog.teacherInstructionsChanged.connect(self._save_live_tutor_teacher_instructions)
                dialog.pttStarted.connect(lambda: self.set_live_tutor_push_to_talk(True))
                dialog.pttStopped.connect(lambda: self.set_live_tutor_push_to_talk(False))
                dialog.textMessageRequested.connect(self.send_live_tutor_text_message)
                dialog.manualRegionSelected.connect(lambda page_idx, box, crop, d=dialog: self.set_live_manual_region(page_idx, box, crop, d))
                dialog.focusOverlayVisibilityChanged.connect(lambda visible, d=dialog: self.set_live_focus_visibility(d, visible))
                dialog.clearFocusRequested.connect(lambda d=dialog: self.clear_live_focus(d))
                dialog.finished.connect(lambda _result: self._unlock_toolbar_after_tutor_close())
                self._live_tutor_dialog = dialog
            # A stale C++ wrapper can occur if Qt has already destroyed a dialog.
            dialog.objectName()
        except RuntimeError:
            self._live_tutor_dialog = None
            QTimer.singleShot(0, self.open_live_tutor)
            return
        except Exception as exc:
            QMessageBox.warning(self, "Engo · Voice & Learn", f"Could not open the voice window:\n{exc}")
            return

        # If the dialog was closed while Gemini Live was connected, reopen the
        # existing session first. Never block access to its End button just because
        # the main window is now focused on a different linked PDF pair.
        if worker_running and worker is not None:
            session_primary = os.path.abspath(worker.pdf_path)
            session_secondary = os.path.abspath(getattr(worker, "secondary_pdf_path", "") or "")
            wanted_primary = os.path.abspath(tab.path) if tab is not None else ""
            wanted_secondary = os.path.abspath(companion.path) if companion is not None else ""
            pair_changed = (
                not wanted_primary
                or os.path.normcase(session_primary) != os.path.normcase(wanted_primary)
                or os.path.normcase(session_secondary) != os.path.normcase(wanted_secondary)
            )
            dialog.pdf_path = session_primary
            dialog.secondary_pdf_path = session_secondary
            if pair_changed and wanted_primary:
                # Apply the newly selected PDF pair only after the old session's
                # worker has fully stopped; page/focus events still belong to the
                # old pair until that point.
                dialog._pending_next_pdf_path = wanted_primary
                dialog._pending_next_secondary_path = wanted_secondary
            else:
                dialog._pending_next_pdf_path = ""
                dialog._pending_next_secondary_path = ""
            try:
                paused = bool(worker._pause_event.is_set())
                stopping = bool(worker._stop_event.is_set())
            except Exception:
                paused = False
                stopping = False
            dialog.set_session_active(True, paused=paused)
            if stopping:
                dialog.start_btn.setEnabled(False)
                dialog.stop_btn.setEnabled(False)
                dialog.ptt_btn.setEnabled(False)
                dialog.pause_btn.setEnabled(False)
                dialog.text_input.setEnabled(False)
                dialog.send_text_btn.setEnabled(False)
            dialog.configure_voice_preferences(
                str(self.settings.value("live_tutor_voice_name", "Orus", type=str) or "Orus"),
                str(self.settings.value("live_tutor_speaking_style", "egyptian", type=str) or "egyptian"),
                str(self.settings.value("live_tutor_detail_mode", "detailed", type=str) or "detailed"),
            )
            dialog.configure_teacher_instructions(str(self.settings.value("live_tutor_teacher_instructions", "", type=str) or ""))
            dialog.configure_window_theme(True)
            if not getattr(self, "_toolbar_density_initialized", False) and hasattr(self, "save_btn"):
                self._toolbar_density_user_resize_pending = False
                self._apply_toolbar_density(force=True)
            self._live_tutor_toolbar_locked = True
            self._toolbar_density_user_resize_pending = False
            self._toolbar_density_timer.stop()
            self._toolbar_caption_language = str(self.settings.value("interface_language", "en", type=str) or "en").lower().split("-")[0]
            self._apply_interface_language()
            if stopping:
                dialog.set_status("Ending conversation… the live connection is shutting down.")
            elif pair_changed:
                session_label = Path(session_primary).name
                dialog.set_status(
                    f"A live session is still connected to {session_label}. End that conversation before starting on the newly selected PDF pair."
                )
            else:
                dialog.set_status("Live session reconnected · continue speaking, pause, or end the conversation.")
            dialog.setWindowModality(Qt.WindowModality.WindowModal)
            dialog.show()
            dialog.raise_()
            dialog.activateWindow()
            return

        if tab is None:
            self.show_status("Open a PDF before starting Voice & Learn")
            return
        dialog.pdf_path = os.path.abspath(tab.path)
        dialog.configure_voice_preferences(
            str(self.settings.value("live_tutor_voice_name", "Orus", type=str) or "Orus"),
            str(self.settings.value("live_tutor_speaking_style", "egyptian", type=str) or "egyptian"),
            str(self.settings.value("live_tutor_detail_mode", "detailed", type=str) or "detailed"),
        )
        dialog.configure_teacher_instructions(str(self.settings.value("live_tutor_teacher_instructions", "", type=str) or ""))
        dialog.configure_window_theme(True)
        # Finish one stable baseline pass before locking (important if the learner
        # opens the voice lesson immediately after the main window first appears).
        if not getattr(self, "_toolbar_density_initialized", False) and hasattr(self, "save_btn"):
            self._toolbar_density_user_resize_pending = False
            self._apply_toolbar_density(force=True)
        # Opening the live tutor is not a toolbar resize. Freeze the current labels
        # and rows and discard a stale density timer; only a real manual width resize
        # may reflow while the lesson dialog is open.
        self._toolbar_density_locked_before_tutor = bool(getattr(self, "_toolbar_density_initialized", False))
        self._live_tutor_toolbar_locked = True
        self._toolbar_density_user_resize_pending = False
        self._toolbar_density_timer.stop()
        self._toolbar_caption_language = str(self.settings.value("interface_language", "en", type=str) or "en").lower().split("-")[0]
        self._apply_interface_language()
        dialog.set_status("Preparing the currently displayed PDF page(s)…")
        dialog.setWindowModality(Qt.WindowModality.WindowModal)
        dialog.show()
        dialog.raise_()
        dialog.activateWindow()

        primary_path = os.path.abspath(tab.path)
        # Defer image rendering until the window has a real layout/viewport. This avoids
        # doing two large QPixmap resizes while the combined dialog is still hidden.
        def load_primary_preview():
            current_primary = self._open_document_tab_by_path(primary_path)
            if current_primary is None or self._live_tutor_dialog is not dialog:
                return
            try:
                page_text, page_image, page_index = self._capture_live_page(current_primary.path, current_primary.current_page)
                dialog.pdf_path = os.path.abspath(current_primary.path)
                dialog.set_page_preview(page_image, page_index + 1, current_primary.page_count)
                dialog.set_status(f"Primary PDF ready · page {page_index + 1} of {current_primary.page_count}")
            except Exception as exc:
                dialog.set_status(f"Could not prepare the primary page: {exc}")
                return

            current_companion = self.linked_supplementary_tab(current_primary.path)
            if current_companion is None:
                dialog.clear_secondary_page_preview()
                dialog.set_status("Ready · one PDF is active. Link another open tab to add a supplementary reference.")
                return

            secondary_path = os.path.abspath(current_companion.path)
            def load_secondary_preview():
                # Resolve the tab again in case it was unlinked/closed while the preview queued.
                latest_companion = self._open_document_tab_by_path(secondary_path)
                if (latest_companion is None or self._live_tutor_dialog is not dialog
                        or self.linked_supplementary_tab(primary_path) is None):
                    dialog.clear_secondary_page_preview()
                    return
                try:
                    sec_text, sec_image, sec_index = self._capture_live_page(latest_companion.path, latest_companion.current_page)
                    dialog.set_secondary_page_preview(sec_image, sec_index + 1, latest_companion.page_count,
                                                      latest_companion.path, Path(latest_companion.path).name)
                    dialog.set_status(
                        f"Ready · both visible pages are linked: primary {current_primary.current_page + 1}, "
                        f"supplementary {latest_companion.current_page + 1}."
                    )
                except Exception as exc:
                    dialog.clear_secondary_page_preview()
                    dialog.set_status(f"Primary page ready · supplementary preview unavailable: {exc}")
            QTimer.singleShot(80, load_secondary_preview)

        QTimer.singleShot(60, load_primary_preview)

    def _save_live_tutor_voice_preferences(self, voice_name: str, speaking_style: str):
        self.settings.setValue("live_tutor_voice_name", str(voice_name or "Orus"))
        self.settings.setValue("live_tutor_speaking_style", str(speaking_style or "egyptian"))
        self.settings.sync()

    def _save_live_tutor_detail_preference(self, detail_mode: str):
        detail_mode = str(detail_mode or "detailed").lower()
        if detail_mode not in {"brief", "detailed"}:
            detail_mode = "detailed"
        self.settings.setValue("live_tutor_detail_mode", detail_mode)
        self.settings.sync()

    def _save_live_tutor_teacher_instructions(self, instructions: str):
        self.settings.setValue("live_tutor_teacher_instructions", str(instructions or "")[:4000])
        self.settings.sync()

    def _handle_live_tutor_navigation(self, target: str, page_number: int = 0, dialog=None):
        target = str(target or "next").strip().lower()
        if target == "next":
            self.navigate_live_tutor_page(1, dialog)
        elif target == "previous":
            self.navigate_live_tutor_page(-1, dialog)
        elif target == "first":
            self.navigate_live_tutor_page(0, dialog, target_page=1)
        elif target == "last":
            self.navigate_live_tutor_page(0, dialog, target_page=-1)
        elif target == "number":
            self.navigate_live_tutor_page(0, dialog, target_page=max(1, int(page_number or 1)))

    def navigate_live_tutor_page(self, delta: int, dialog=None, target_page: int | None = None):
        dialog = dialog or self._live_tutor_dialog
        if dialog is None:
            return
        path = os.path.normcase(os.path.abspath(getattr(dialog, "pdf_path", "") or ""))
        tab = None
        for i in range(self.tabs.count()):
            candidate = self.tabs.widget(i)
            if isinstance(candidate, DocumentTab) and os.path.normcase(os.path.abspath(candidate.path)) == path:
                tab = candidate
                if self.tabs.currentIndex() != i:
                    self.tabs.setCurrentIndex(i)
                    try:
                        self.doc_tabbar.setCurrentIndex(i)
                    except Exception:
                        pass
                break
        if tab is None:
            dialog.set_status("The source PDF is no longer open. Reopen it to navigate pages.")
            return
        if target_page is None:
            target = max(0, min(tab.page_count - 1, int(tab.current_page) + int(delta)))
        elif int(target_page) == -1:
            target = max(0, tab.page_count - 1)
        else:
            target = max(0, min(tab.page_count - 1, int(target_page) - 1))
        if target == tab.current_page:
            return
        tab.go_to_page(target)
        worker = self._live_tutor_worker
        if worker is None or not worker.isRunning():
            # Keep the separate tutor window useful even before the live session starts.
            try:
                page_text, page_image, actual_index = self._capture_live_page(tab.path, target)
                dialog.pdf_path = os.path.abspath(tab.path)
                dialog.set_page_preview(page_image, actual_index + 1, tab.page_count)
                dialog.set_status(f"Preview ready · page {actual_index + 1}. Start the lesson when ready.")
            except Exception as exc:
                dialog.set_status(f"Could not show page {target + 1}: {exc}")
        else:
            dialog.set_status(f"Moving to page {target + 1} · the tutor will begin explaining this page.")

    def navigate_live_tutor_secondary_page(self, direction: int, dialog=None):
        dialog = dialog or self._live_tutor_dialog
        if dialog is None or not dialog.secondary_pdf_path:
            return
        tab = self._open_document_tab_by_path(dialog.secondary_pdf_path)
        if tab is None:
            dialog.set_status("Supplementary PDF tab is no longer open.")
            return
        target = max(0, min(tab.page_count - 1, int(tab.current_page) + int(direction)))
        if target == tab.current_page:
            return
        tab.go_to_page(target)
        try:
            page_text, page_image, actual_index = self._capture_live_page(tab.path, target)
            dialog.set_secondary_page_preview(page_image, actual_index + 1, tab.page_count, tab.path, Path(tab.path).name)
            worker = self._live_tutor_worker
            if worker is not None and worker.isRunning():
                worker.update_secondary_page_context(actual_index, page_text, page_image, tab.page_count)
            dialog.set_status(f"Supplementary reference moved to page {actual_index + 1}.")
        except Exception as exc:
            dialog.set_status(f"Could not update supplementary page: {exc}")

    def start_live_tutor(self, dialog=None):
        dialog = dialog or self._live_tutor_dialog
        if dialog is None:
            self.open_live_tutor()
            return
        if _qt_thread_is_running(self._live_tutor_worker):
            dialog.set_status("A live session is already running.")
            return
        if self._live_tutor_worker is not None:
            self._live_tutor_worker = None
        pdf_path = os.path.abspath(getattr(dialog, "pdf_path", "") or "")
        tab = None
        for i in range(self.tabs.count()):
            candidate = self.tabs.widget(i)
            if isinstance(candidate, DocumentTab) and os.path.normcase(os.path.abspath(candidate.path)) == os.path.normcase(pdf_path):
                tab = candidate
                break
        if tab is None:
            tab = self.active_tab()
        if tab is None:
            dialog.set_status("Open a PDF before starting a live session.")
            return
        api_key = _get_provider_key(self.settings, "gemini")
        if not api_key:
            dialog.set_status("Google Gemini API key is missing.")
            QMessageBox.information(self, "Google Gemini key needed",
                "Voice & Learn requires a Google Gemini API key with access to Gemini Live.\n\n"
                "Open Application Settings → AI settings → Google Gemini → API key, save it, then start the conversation again.")
            return
        model = str(self.settings.value("ai_model_gemini_live", "gemini-3.8-live", type=str) or "gemini-3.8-live")
        try:
            page_text, page_image, page_index = self._capture_live_page(tab.path, tab.current_page)
        except Exception as exc:
            QMessageBox.warning(self, "Engo · Voice & Learn", f"Could not prepare the page:\n{exc}")
            return
        dialog.pdf_path = os.path.abspath(tab.path)
        secondary_document = None
        companion_tab = self.linked_supplementary_tab(tab.path)
        secondary_preview = None
        if companion_tab is not None:
            try:
                secondary_text, secondary_image, secondary_index = self._capture_live_page(companion_tab.path, companion_tab.current_page)
                secondary_document = {"path": companion_tab.path, "page_index": secondary_index,
                                      "page_count": companion_tab.page_count, "text": secondary_text, "image": secondary_image,
                                      "name": Path(companion_tab.path).name}
                secondary_preview = (secondary_image, secondary_index + 1, companion_tab.page_count,
                                     companion_tab.path, Path(companion_tab.path).name)
            except Exception as exc:
                secondary_document = None
                secondary_preview = None
                dialog.set_status(f"Supplementary PDF unavailable: {exc}")
        # Refresh both visual previews in separate queued GUI turns. The worker below still
        # receives the exact page text and image captured from both currently displayed panes.
        primary_preview = (page_image, page_index + 1, tab.page_count)
        def apply_primary_preview():
            try:
                if self._live_tutor_dialog is dialog and dialog.isVisible():
                    dialog.set_page_preview(*primary_preview)
            except Exception as exc:
                dialog.set_status(f"Primary preview refresh failed: {exc}")
        def apply_secondary_preview():
            try:
                if self._live_tutor_dialog is not dialog or not dialog.isVisible():
                    return
                if secondary_preview:
                    dialog.set_secondary_page_preview(*secondary_preview)
                else:
                    dialog.clear_secondary_page_preview()
            except Exception as exc:
                dialog.set_status(f"Supplementary preview refresh failed: {exc}")
        QTimer.singleShot(0, apply_primary_preview)
        QTimer.singleShot(100, apply_secondary_preview)
        self._clear_live_page_teaching_marks()
        dialog.clear_teaching_marks()
        # Start every lesson with the active-item rectangle enabled on the PDF page.
        dialog.set_focus_overlay_visible(True)
        dialog.transcript_view.clear()
        dialog._transcript_markdown = ""
        dialog._last_speaker = ""
        if not dialog._board_has_notes:
            dialog.reset_board(f"PAGE {page_index + 1} NOTES · cumulative summary")
        voice_name = dialog.current_voice_name()
        speaking_style = dialog.current_speaking_style()
        lesson_detail = dialog.current_lesson_detail()
        teacher_instructions = dialog.current_teacher_instructions()
        self._save_live_tutor_voice_preferences(voice_name, speaking_style)
        self._save_live_tutor_teacher_instructions(teacher_instructions)
        self._save_live_tutor_detail_preference(lesson_detail)
        worker = GeminiLiveTutorWorker(api_key, model, tab.path, page_index, page_text, page_image,
                                       voice_name=voice_name, speaking_style=speaking_style,
                                       initial_board_markdown=dialog._board_markdown,
                                       lesson_detail=lesson_detail, teacher_instructions=teacher_instructions,
                                       secondary_document=secondary_document)
        worker.status.connect(dialog.set_status)
        worker.transcript.connect(dialog.append_transcript)
        worker.board_update.connect(dialog.update_board)
        worker.board_command.connect(dialog.apply_board_action)
        worker.focus_requested.connect(self._on_live_focus_requested)
        worker.focus_clear_requested.connect(self._schedule_live_focus_clear)
        worker.teacher_arrow_requested.connect(self._on_live_teacher_arrow_overlay_requested)
        worker.page_navigation_requested.connect(lambda target, number, d=dialog: self._handle_live_tutor_navigation(target, number, d))
        worker.failed.connect(lambda message, d=dialog: self._on_live_tutor_failure(d, message))
        worker.finished.connect(lambda w=worker, d=dialog: self._on_live_tutor_worker_finished(w, d))
        if dialog._manual_region and int(dialog._manual_region.get("page_index", -1)) == page_index:
            worker.set_manual_target(page_index, dialog._manual_region.get("box", []), dialog._manual_region.get("image", b""))
        self._live_tutor_worker = worker
        # The worker creates selectable-text geometry before the first spoken turn;
        # it emits the initial focus once that geometry is ready.
        dialog.set_session_active(True)
        detail_label = "brief" if lesson_detail == "brief" else "detailed"
        dialog.set_status(f"Connecting · {detail_label} lesson · microphone sends only while you hold SPACE")
        self.show_status("Starting Engo AI teacher…")
        worker.start()

    def set_live_manual_region(self, page_index: int, box, crop_image: bytes, dialog=None):
        dialog = dialog or self._live_tutor_dialog
        worker = self._live_tutor_worker
        if worker is not None and worker.isRunning():
            if not worker.set_manual_target(page_index, box, crop_image):
                if dialog is not None:
                    dialog.set_status("Could not register the selected area. Please select it again.")
                return
        tab = self._live_tutor_document_tab(dialog)
        if tab is not None:
            page_index = max(0, min(int(page_index), tab.page_count - 1))
            tab.canvas.set_ai_focus(page_index, box, "Manually selected area", "manual")
            tab.canvas.set_ai_focus_visible(True)
            tab.canvas.update()
        if dialog is not None:
            try:
                _txt, preview_image, _actual = self._capture_live_page(tab.path, page_index) if tab is not None else ("", b"", page_index)
                if preview_image:
                    dialog.set_page_preview(preview_image, page_index + 1, tab.page_count)
                dialog.set_focus_region(page_index, box, "Manually selected area", "manual")
            except Exception:
                pass
            dialog.set_status("Area selected · ask about it by voice or text. Use Clear rectangle to remove it.")

    def send_live_tutor_text_message(self, message: str):
        worker = self._live_tutor_worker
        if worker is None or not _qt_thread_is_running(worker):
            if self._live_tutor_dialog is not None:
                self._live_tutor_dialog.set_status("Voice & Learn is not connected. Start the session first.")
            return
        worker.send_typed_message(message)

    def set_live_tutor_push_to_talk(self, active: bool):
        worker = self._live_tutor_worker
        if worker is not None and _qt_thread_is_running(worker):
            worker.set_push_to_talk(bool(active))

    def set_live_tutor_paused(self, paused: bool):
        worker = self._live_tutor_worker
        if worker is not None and _qt_thread_is_running(worker):
            worker.set_paused(bool(paused))
        elif self._live_tutor_dialog is not None:
            self._live_tutor_dialog.set_status("The live session is not connected. Start a new conversation first.")

    def _live_tutor_document_tab(self, dialog=None):
        worker = self._live_tutor_worker
        path = os.path.abspath((getattr(worker, "pdf_path", "") if worker else "") or
                               (getattr(dialog, "pdf_path", "") if dialog else ""))
        for i in range(self.tabs.count()):
            candidate = self.tabs.widget(i)
            if isinstance(candidate, DocumentTab) and path and os.path.normcase(os.path.abspath(candidate.path)) == os.path.normcase(path):
                return candidate
        return self.active_tab()

    def set_live_focus_visibility(self, dialog=None, visible=True):
        if dialog is not None:
            dialog.set_focus_overlay_visible(bool(visible))
        tab = self._live_tutor_document_tab(dialog)
        if tab is not None:
            tab.canvas.set_ai_focus_visible(bool(visible))
        worker = self._live_tutor_worker
        if worker is not None and getattr(worker, "secondary_pdf_path", ""):
            secondary_tab = self._open_document_tab_by_path(worker.secondary_pdf_path)
            if secondary_tab is not None:
                secondary_tab.canvas.set_ai_focus_visible(bool(visible))
                primary_tab = self._open_document_tab_by_path(worker.pdf_path)
                if primary_tab is not None and primary_tab._secondary_canvas is not None:
                    primary_tab._secondary_canvas.set_ai_focus_visible(bool(visible))

    def clear_live_focus(self, dialog=None):
        self._clear_live_focus_overlays()
        tab = self._live_tutor_document_tab(dialog)
        if tab is not None:
            tab.canvas.clear_ai_focus()
        worker = self._live_tutor_worker
        if worker is not None and getattr(worker, "secondary_pdf_path", ""):
            secondary_tab = self._open_document_tab_by_path(worker.secondary_pdf_path)
            if secondary_tab is not None:
                secondary_tab.canvas.clear_ai_focus()
                primary_tab = self._open_document_tab_by_path(worker.pdf_path)
                if primary_tab is not None and primary_tab._secondary_canvas is not None:
                    primary_tab._secondary_canvas.clear_ai_focus()
        worker = self._live_tutor_worker
        if worker is not None and worker.isRunning():
            worker.clear_manual_target()
        if dialog is not None:
            dialog.clear_focus()

    def stop_live_tutor(self):
        worker = self._live_tutor_worker
        if worker is not None and _qt_thread_is_running(worker):
            if self._live_tutor_dialog is not None:
                dialog = self._live_tutor_dialog
                dialog.set_status("Ending conversation…")
                dialog.stop_btn.setEnabled(False)
                dialog.start_btn.setEnabled(False)
                dialog.ptt_btn.setEnabled(False)
                dialog.pause_btn.setEnabled(False)
                self.clear_live_focus(dialog)
            worker.cancel()
            self.show_status("Ending Engo AI voice session…")
        elif self._live_tutor_dialog is not None:
            self._live_tutor_dialog.set_session_active(False)
            self._live_tutor_toolbar_locked = False

    def refresh_live_tutor_page(self, dialog=None):
        dialog = dialog or self._live_tutor_dialog
        if dialog is None:
            return
        path = os.path.abspath(getattr(dialog, "pdf_path", "") or "")
        tab = None
        for i in range(self.tabs.count()):
            candidate = self.tabs.widget(i)
            if isinstance(candidate, DocumentTab) and os.path.normcase(os.path.abspath(candidate.path)) == os.path.normcase(path):
                tab = candidate
                break
        if tab is None:
            tab = self.active_tab()
        if tab is None:
            dialog.set_status("Open a PDF before refreshing the page context.")
            return
        try:
            page_text, page_image, page_index = self._capture_live_page(tab.path, tab.current_page)
            dialog.pdf_path = os.path.abspath(tab.path)
            dialog.set_page_preview(page_image, page_index + 1, tab.page_count)
            worker = self._live_tutor_worker
            companion = self.linked_supplementary_tab(tab.path)
            secondary_ready = False
            if companion is not None:
                secondary_text, secondary_image, secondary_index = self._capture_live_page(companion.path, companion.current_page)
                dialog.set_secondary_page_preview(secondary_image, secondary_index + 1, companion.page_count,
                                                  companion.path, Path(companion.path).name)
                secondary_ready = True
                if worker is not None and worker.isRunning():
                    worker.update_secondary_page_context(secondary_index, secondary_text, secondary_image, companion.page_count)
            else:
                dialog.clear_secondary_page_preview()
            if worker is not None and worker.isRunning():
                worker.update_page_context(page_index, page_text, page_image)
                if secondary_ready:
                    dialog.set_status(f"Both PDF pages queued · primary {page_index + 1}, supplementary {companion.current_page + 1}.")
                else:
                    dialog.set_status(f"Page {page_index + 1} queued as the new live reference.")
            else:
                dialog.set_status(f"Preview updated · primary page {page_index + 1}" + (" and supplementary page." if secondary_ready else ". Start the session when ready."))
        except Exception as exc:
            dialog.set_status(f"Could not refresh page: {exc}")

    def _clear_live_page_teaching_marks(self):
        """Discard unsaved teacher overlays from all PDF canvases."""
        try:
            for index in range(self.tabs.count()):
                tab = self.tabs.widget(index)
                marks = getattr(tab, "_live_teaching_marks", None)
                if marks:
                    marks.clear()
                    canvas = getattr(tab, "canvas", None)
                    if canvas is not None:
                        canvas.update()
                    secondary = getattr(tab, "_secondary_canvas", None)
                    if secondary is not None:
                        secondary.update()
        except Exception:
            pass

    def _append_live_teaching_mark(self, source: str, page_index: int, mark: dict):
        """Store a temporary overlay against the correct PDF page and repaint its visible surface."""
        worker = self._live_tutor_worker
        if worker is None:
            return None
        source_key = str(source or "primary").lower()
        target_path = worker.secondary_pdf_path if source_key == "supplementary" else worker.pdf_path
        tab = self._open_document_tab_by_path(target_path)
        if tab is None:
            return None
        page_index = max(0, min(int(page_index), tab.page_count - 1))
        payload = dict(mark)
        payload["page_index"] = page_index
        payload["source"] = source_key
        items = tab._live_teaching_marks.setdefault(page_index, [])
        # Avoid duplicate screen overlays when a model adds an optional extra mark
        # on top of the automatically generated one for the same focused item.
        duplicate = False
        for old in items:
            if old.get("type") != payload.get("type"):
                continue
            if payload.get("type") == "arrow":
                a0, b0 = old.get("start", [0, 0]), old.get("end", [0, 0])
                a1, b1 = payload.get("start", [0, 0]), payload.get("end", [0, 0])
                duplicate = max(abs(float(a0[i]) - float(a1[i])) for i in range(2)) < 0.035 and max(abs(float(b0[i]) - float(b1[i])) for i in range(2)) < 0.035
            if duplicate:
                break
        if not duplicate:
            items.append(payload)
        target_canvas = tab.canvas
        if source_key == "supplementary":
            primary_tab = self._open_document_tab_by_path(worker.pdf_path)
            if primary_tab is not None and primary_tab._linked_view_secondary is tab and primary_tab._secondary_canvas is not None:
                target_canvas = primary_tab._secondary_canvas
        target_canvas.update()
        return tab

    def _on_live_teacher_arrow_overlay_requested(self, source: str, page_index: int, start, end, label: str):
        dialog = self._live_tutor_dialog
        if dialog is not None:
            dialog.add_teaching_arrow_overlay(source, page_index, start, end, label)
        self._append_live_teaching_mark(source, page_index, {
            "type": "arrow", "start": list(start), "end": list(end), "label": str(label or "Teacher pointer")[:160]
        })

    def _clear_live_focus_overlays(self):
        """Remove stale AI focus rectangles from every open PDF surface."""
        try:
            for index in range(self.tabs.count()):
                tab = self.tabs.widget(index)
                canvas = getattr(tab, "canvas", None)
                if canvas is not None and hasattr(canvas, "clear_ai_focus"):
                    canvas.clear_ai_focus()
                secondary = getattr(tab, "_secondary_canvas", None)
                if secondary is not None and hasattr(secondary, "clear_ai_focus"):
                    secondary.clear_ai_focus()
        except Exception:
            pass
        dialog = getattr(self, "_live_tutor_dialog", None)
        if dialog is not None and hasattr(dialog, "clear_focus_regions"):
            dialog.clear_focus_regions()

    def _schedule_live_focus_clear(self):
        """Clear a finished voice target after its queued speech has actually played."""
        generation = int(getattr(self, "_live_focus_generation", 0))
        started_at = time.monotonic()
        quiet_since = [None]

        def poll_playback(token=generation):
            if token != int(getattr(self, "_live_focus_generation", 0)):
                return
            current_worker = getattr(self, "_live_tutor_worker", None)
            speaker_event = getattr(current_worker, "_speaker_playing_event", None)
            speaker_queue = getattr(current_worker, "_speaker_queue", None)
            try:
                audio_busy = bool(speaker_event and speaker_event.is_set()) or bool(speaker_queue and not speaker_queue.empty())
            except Exception:
                audio_busy = False
            if audio_busy:
                quiet_since[0] = None
                # Safety ceiling avoids a stale rectangle if an audio device fails.
                if time.monotonic() - started_at < 75.0:
                    QTimer.singleShot(180, poll_playback)
                    return
            if quiet_since[0] is None:
                quiet_since[0] = time.monotonic()
            if time.monotonic() - quiet_since[0] < 0.58 and time.monotonic() - started_at < 75.0:
                QTimer.singleShot(140, poll_playback)
                return
            if token == int(getattr(self, "_live_focus_generation", 0)):
                self._clear_live_focus_overlays()

        QTimer.singleShot(580, poll_playback)

    def jump_to_pdf_selection(self, path: str, page_index: int, normalized_box):
        """Navigate to a PDF passage saved with a chat message and flash it yellow."""
        tab = self._open_document_tab_by_path(path)
        if tab is None or not getattr(tab, "page_count", 0):
            is_ar = str(self.settings.value("interface_language", "en", type=str) or "en").lower().startswith("ar")
            self.show_status("الملف الذي يحتوي على النص المحدد غير مفتوح" if is_ar else "The PDF containing this selected passage is not open")
            return
        try:
            page_index = max(0, min(int(page_index), int(tab.page_count) - 1))
            box = [max(0.0, min(1.0, float(v))) for v in normalized_box]
            if len(box) != 4 or box[2] <= 0 or box[3] <= 0:
                raise ValueError("invalid saved selection location")
            box[2] = min(box[2], 1.0 - box[0])
            box[3] = min(box[3], 1.0 - box[1])
        except Exception:
            self.show_status("تعذّر تحديد موضع النص المحفوظ" if str(self.settings.value("interface_language", "en", type=str) or "en").lower().startswith("ar") else "Could not resolve the saved text location")
            return
        tab_index = self.tabs.indexOf(tab)
        if tab_index >= 0:
            self.tabs.setCurrentWidget(tab)
            try:
                self.doc_tabbar.setCurrentIndex(tab_index)
            except Exception:
                pass
        tab.go_to_page(page_index)
        canvas = tab.canvas
        canvas.set_temporary_selection_highlight(page_index, box)

        def scroll_to_passage():
            try:
                active_canvas = tab.canvas
                scroll = getattr(active_canvas, "display_scroll", None) or tab.scroll
                rect = active_canvas.page_rects.get(page_index)
                if rect is None:
                    tab._relayout()
                    rect = active_canvas.page_rects.get(page_index)
                if rect is None:
                    return
                viewport = scroll.viewport()
                center_x = rect.left() + (box[0] + box[2] / 2.0) * rect.width()
                center_y = rect.top() + (box[1] + box[3] / 2.0) * rect.height()
                scroll.verticalScrollBar().setValue(round(center_y - viewport.height() * 0.38))
                if rect.width() > viewport.width():
                    scroll.horizontalScrollBar().setValue(round(center_x - viewport.width() * 0.5))
                else:
                    scroll.horizontalScrollBar().setValue(0)
                active_canvas.update()
            except (RuntimeError, AttributeError):
                pass

        QTimer.singleShot(100, scroll_to_passage)
        self.show_status("تم الانتقال إلى النص المحدد" if str(self.settings.value("interface_language", "en", type=str) or "en").lower().startswith("ar") else "Jumped to the selected passage")

    def _on_live_focus_requested(self, page_index: int, box, label: str, kind: str = "text", source: str = "primary"):
        """Show the current tutor target and scroll the real PDF viewport to it."""
        self._live_focus_generation = int(getattr(self, "_live_focus_generation", 0)) + 1
        worker = self._live_tutor_worker
        if worker is None:
            return
        source = str(source or "primary").lower()
        target_path = worker.secondary_pdf_path if source == "supplementary" else worker.pdf_path
        tab = self._open_document_tab_by_path(target_path)
        if tab is None:
            tab = self._live_tutor_document_tab(self._live_tutor_dialog)
        if tab is None or not getattr(tab, "page_count", 0):
            self.show_status("Engo focus received, but the PDF tab could not be found.")
            return
        try:
            vals = [max(0.0, min(1.0, float(v))) for v in box]
            if len(vals) != 4 or vals[2] <= 0 or vals[3] <= 0:
                raise ValueError("invalid focus rectangle")
            vals[2] = min(vals[2], 1.0 - vals[0])
            vals[3] = min(vals[3], 1.0 - vals[1])
            box = vals
        except Exception:
            self.show_status("Engo focus received invalid page coordinates; waiting for a corrected region.")
            return
        page_index = max(0, min(int(page_index), tab.page_count - 1))

        # Make the document containing the current target visible. In a linked pair,
        # keep the primary tab active and use its secondary viewport for the companion.
        primary_tab = None
        target_canvas = tab.canvas
        if source == "supplementary":
            primary_tab = self._open_document_tab_by_path(worker.pdf_path)
            if (primary_tab is not None and primary_tab._linked_view_secondary is tab
                    and primary_tab._secondary_canvas is not None):
                if self.tabs.indexOf(primary_tab) >= 0 and self.tabs.currentWidget() is not primary_tab:
                    self.tabs.setCurrentWidget(primary_tab)
                    try:
                        self.doc_tabbar.setCurrentIndex(self.tabs.indexOf(primary_tab))
                    except Exception:
                        pass
                primary_tab._linked_go_to_secondary_page(page_index)
                target_canvas = primary_tab._secondary_canvas
                target_canvas.set_ai_focus(page_index, box, label, kind)
            else:
                tab.go_to_page(page_index)
                if self.tabs.indexOf(tab) >= 0 and self.tabs.currentWidget() is not tab:
                    self.tabs.setCurrentWidget(tab)
                    try:
                        self.doc_tabbar.setCurrentIndex(self.tabs.indexOf(tab))
                    except Exception:
                        pass
        else:
            if self.tabs.indexOf(tab) >= 0 and self.tabs.currentWidget() is not tab:
                self.tabs.setCurrentWidget(tab)
                try:
                    self.doc_tabbar.setCurrentIndex(self.tabs.indexOf(tab))
                except Exception:
                    pass
            tab.go_to_page(page_index)

        # Clear stale focus only after a valid target has been received and normalized.
        self._clear_live_focus_overlays()
        if target_canvas is tab.canvas:
            tab.canvas.set_ai_focus(page_index, box, label, kind)
        elif target_canvas is not None:
            target_canvas.set_ai_focus(page_index, box, label, kind)
        if self._live_tutor_dialog is not None:
            visible = bool(self._live_tutor_dialog.focus_visible_checkbox.isChecked())
        else:
            visible = True
        tab.canvas.set_ai_focus_visible(visible)
        target_canvas.set_ai_focus_visible(visible)
        target_canvas.update()

        def _scroll_exact_focus_region():
            try:
                canvas = target_canvas
                scroll = getattr(canvas, "display_scroll", None)
                if scroll is None:
                    scroll = tab.scroll
                rect = canvas.page_rects.get(page_index)
                if rect is None:
                    if canvas is tab.canvas:
                        tab._relayout()
                    elif primary_tab is not None:
                        primary_tab._relayout_linked_secondary()
                    rect = canvas.page_rects.get(page_index)
                if rect is None:
                    return
                viewport = scroll.viewport()
                center_x = rect.left() + (box[0] + box[2] / 2.0) * rect.width()
                center_y = rect.top() + (box[1] + box[3] / 2.0) * rect.height()
                # Place the target around the upper-middle of the viewport so the
                # learner can see both the item and the following explanation context.
                vertical = scroll.verticalScrollBar()
                horizontal = scroll.horizontalScrollBar()
                vertical.setValue(round(center_y - viewport.height() * 0.38))
                if rect.width() > viewport.width():
                    horizontal.setValue(round(center_x - viewport.width() * 0.50))
                else:
                    horizontal.setValue(0)
                canvas.update()
            except (RuntimeError, AttributeError, TypeError, ValueError):
                pass

        # go_to_page() schedules its own page-top scroll at 0 ms. Run after it so
        # the focus region, not just the top of the page, ends up in view.
        QTimer.singleShot(80, _scroll_exact_focus_region)
        QTimer.singleShot(220, _scroll_exact_focus_region)

        if self._live_tutor_dialog is not None:
            try:
                _text, image_bytes, _actual_idx = self._capture_live_page(tab.path, page_index)
                if source == "supplementary":
                    self._live_tutor_dialog.set_secondary_page_preview(image_bytes, page_index + 1, tab.page_count,
                                                                         tab.path, Path(tab.path).name)
                    self._live_tutor_dialog.set_secondary_focus_region(page_index, box, label, kind)
                else:
                    self._live_tutor_dialog.set_page_preview(image_bytes, page_index + 1, tab.page_count)
                    self._live_tutor_dialog.set_focus_region(page_index, box, label, kind)
            except Exception:
                pass
        self.show_status(f"Engo focus · {'supplementary' if source == 'supplementary' else 'primary'} PDF · page {page_index + 1} · {label[:80]}")

    def _on_live_teacher_arrow_requested(self, source: str, page_index: int, start, end, label: str):
        worker = self._live_tutor_worker
        if worker is None:
            return
        source = str(source or "primary").lower()
        target_path = worker.secondary_pdf_path if source == "supplementary" else worker.pdf_path
        tab = self._open_document_tab_by_path(target_path)
        if tab is None:
            return
        try:
            page_index = max(0, min(int(page_index), tab.page_count - 1))
            if tab.add_teacher_arrow(page_index, start, end, label):
                target_canvas = tab.canvas
                if source == "supplementary":
                    primary_tab = self._open_document_tab_by_path(worker.pdf_path)
                    if primary_tab is not None and primary_tab._linked_view_secondary is tab and primary_tab._secondary_canvas is not None:
                        target_canvas = primary_tab._secondary_canvas
                target_canvas.update()
                self.show_status(f"Engo teacher · arrow added on page {page_index + 1}")
        except Exception as exc:
            self.show_status(f"Could not draw teacher arrow: {exc}")

    def _on_live_tutor_failure(self, dialog, message: str):
        dialog.set_status("Live session error · see transcript below")
        dialog.append_transcript("Engo", str(message))
        self.show_status("Gemini Live voice session failed")

    def _on_live_tutor_worker_finished(self, worker, dialog):
        if self._live_tutor_worker is worker:
            self._live_tutor_worker = None
        self._live_tutor_toolbar_locked = False
        self._toolbar_density_user_resize_pending = False
        try:
            dialog.set_session_active(False)
            # Unsaved teacher marks are temporary lesson overlays; discard them from both
            # the tutor preview and the real PDF canvas when the session ends.
            dialog.clear_teaching_marks()
            self._clear_live_page_teaching_marks()
            self.clear_live_focus(dialog)
            pending_primary = str(getattr(dialog, "_pending_next_pdf_path", "") or "")
            pending_secondary = str(getattr(dialog, "_pending_next_secondary_path", "") or "")
            dialog._pending_next_pdf_path = ""
            dialog._pending_next_secondary_path = ""
            ready_for = ""
            if pending_primary:
                next_tab = self._open_document_tab_by_path(pending_primary)
                if next_tab is not None:
                    dialog.pdf_path = os.path.abspath(next_tab.path)
                    ready_for = Path(next_tab.path).name
                    try:
                        _text, image_bytes, page_index = self._capture_live_page(next_tab.path, next_tab.current_page)
                        dialog.set_page_preview(image_bytes, page_index + 1, next_tab.page_count)
                    except Exception:
                        pass
                    if pending_secondary:
                        secondary_tab = self._open_document_tab_by_path(pending_secondary)
                        if secondary_tab is not None:
                            try:
                                _text, image_bytes, page_index = self._capture_live_page(secondary_tab.path, secondary_tab.current_page)
                                dialog.set_secondary_page_preview(image_bytes, page_index + 1, secondary_tab.page_count,
                                                                  secondary_tab.path, Path(secondary_tab.path).name)
                            except Exception:
                                dialog.clear_secondary_page_preview()
                        else:
                            dialog.clear_secondary_page_preview()
                    else:
                        dialog.clear_secondary_page_preview()
            if not dialog.status_label.text().startswith("Live session error"):
                if ready_for:
                    dialog.set_status(f"Previous session ended · ready to start a lesson on {ready_for}.")
                else:
                    dialog.set_status("Session ended · Start full-page lesson to reconnect.")
        except RuntimeError:
            pass
        try:
            worker.deleteLater()
        except RuntimeError:
            pass
        self._maybe_finish_pending_close()

    def start_translate_selection(self):
        # In a linked pair, the user can activate either pane. Always target the
        # currently focused pane instead of silently forcing translation to the primary PDF.
        tab = self._view_target_tab() or self.active_tab()
        if not isinstance(tab, DocumentTab):
            self.show_status("Open a PDF before translating")
            return
        self._set_view_target_tab(tab)
        for button in self.tool_buttons.values():
            button.setChecked(False)
        tab.set_tool("translate_select")
        self._show_selected_tool_context_help("translate_select")
        self.show_status(
            f"Engo Translate · {Path(tab.path).name} · drag around the text, handwriting, formula, or chart to translate"
        )

    # Backwards-compatible name for any older signal/shortcut paths.
    def start_google_translate_selection(self):
        self.start_translate_selection()

    def _on_translate_region_selected(self, tab, page_index, image_bytes, clip_rect=None, selected_text=""):
        if not isinstance(tab, DocumentTab) or not image_bytes:
            return
        target = self.settings.value("translate_target", "ar", type=str)
        source = self.settings.value("translate_source", "auto", type=str)
        dialog = TranslationCardDialog(
            image_bytes, page_index, target, self,
            font_pt=self.settings.value("ui_translation_font_pt", 13.0, type=float),
        )
        dialog.pdf_path = os.path.abspath(tab.path)
        dialog.clip_rect = tuple(clip_rect) if clip_rect else None
        dialog.translateRequested.connect(
            lambda _code, d=dialog, data=bytes(image_bytes), pg=int(page_index),
                   pdf_path=dialog.pdf_path, clip=dialog.clip_rect, sc=source, tc=target,
                   txt=str(selected_text or ""):
                self._run_gemini_translation(data, pg, sc, tc, d, pdf_path, clip, txt)
        )
        dialog.show()
        dialog.raise_()
        dialog.activateWindow()
        # Language choices are in AI Settings; the popup itself contains only the translation.
        dialog.translateRequested.emit(str(target))
        self.show_status(f"Translating selected area from {source} to {target}…")

    def _run_gemini_translation(self, image_bytes: bytes, page_index: int, source_code: str,
                                target_code: str, dialog: TranslationCardDialog, pdf_path: str,
                                clip_rect=None, selected_text: str | None = None):
        self.settings.setValue("translate_source", str(source_code or "auto"))
        self.settings.setValue("translate_target", str(target_code or "ar"))
        # Translation always uses Google Gemini and its own saved API key, regardless of the chat provider.
        saved_translation_model = str(self.settings.value(
            "ai_translation_model_gemini", AI_TRANSLATION_DEFAULT_MODEL, type=str
        ) or AI_TRANSLATION_DEFAULT_MODEL).strip()
        # This is an internal translation-only setting, not the learner's chat
        # model choice. Keep it on the current low-latency Flash-Lite model even
        # when an older release left a larger general-purpose model in QSettings.
        model = AI_TRANSLATION_DEFAULT_MODEL if not saved_translation_model or saved_translation_model != AI_TRANSLATION_DEFAULT_MODEL else saved_translation_model
        if model != saved_translation_model:
            self.settings.setValue("ai_translation_model_gemini", model)
        api_key = _get_provider_key(self.settings, "gemini")
        dialog.begin_translation()
        worker = GeminiTranslateWorker(
            pdf_path, page_index, clip_rect, image_bytes, target_code, source_code, model, api_key,
            selected_text=selected_text,
        )
        worker.progress.connect(lambda message, d=dialog: self._safe_translation_update(d, "set_progress", message))
        worker.streamed.connect(lambda delta, d=dialog: self._safe_translation_update(d, "append_delta", delta))
        worker.succeeded.connect(lambda result, d=dialog: self._safe_translation_update(d, "show_result", result))
        worker.failed.connect(lambda error, d=dialog: self._safe_translation_update(d, "show_error", error))
        worker.cancelled.connect(lambda d=dialog: self._safe_translation_update(d, "show_error", "Translation stopped."))
        worker.finished.connect(lambda w=worker: self._cleanup_translation_worker(w))
        if not hasattr(self, "_translation_workers"):
            self._translation_workers = []
        self._translation_workers.append(worker)
        worker.start()

    @staticmethod
    def _safe_translation_update(dialog, method_name: str, value: str):
        try:
            if dialog.isVisible():
                getattr(dialog, method_name)(value)
        except (RuntimeError, AttributeError):
            # The user may close the translation card before the provider finishes.
            pass

    def _cleanup_translation_worker(self, worker):
        try:
            if worker in self._translation_workers:
                self._translation_workers.remove(worker)
        except Exception:
            pass
        worker.deleteLater()
        self._maybe_finish_pending_close()

    def _on_ai_region_selected(self, tab, page_index, image_bytes):
        if not isinstance(tab, DocumentTab):
            return
        if not self.ai_panel.isVisible():
            self._animate_ai_panel(True)
        self._refresh_ai_chat_context(tab)
        chat_owner_path = self.ai_panel.document_path or tab.path
        self.ai_panel.set_selected_region(chat_owner_path, page_index, image_bytes, source_path=tab.path)
        self.show_status(f"Selected {Path(tab.path).name} · page {page_index + 1} region attached to Engo AI")

    def _update_ask_by_voice_button(self, listening: bool):
        button = self.ai_panel.voice_btn
        button.setProperty("recording", bool(listening))
        button.setProperty("transcribing", False)
        button.setStyleSheet("")
        button.style().unpolish(button)
        button.style().polish(button)
        theme_name = str(self.settings.value("ui_theme", "dark", type=str) or "dark").lower()
        voice_icon_color = "#ffffff" if listening else (
            "#315d9d" if theme_name == "light" else
            ("#9fc0ff" if theme_name == "midnight" else "#e1e8f2")
        )
        button.setIcon(make_icon("mic", voice_icon_color, 16))
        if listening:
            button.setText("Listening · Tap to stop")
            button.setToolTip("Microphone is active. Tap to stop and keep the recognized text in the chat box; it will not be sent automatically.")
            button.setEnabled(True)
        else:
            button.setText("Ask by voice")
            button.setToolTip("Record your speech and insert the transcription into the chat box. Press Send when ready.")
            button.setEnabled(bool(self.ai_panel.document_path) and not self.ai_panel._busy)

    def start_voice_input(self):
        tab = self.active_tab()
        if not tab:
            self.show_status("Open a PDF before asking by voice")
            return
        if self._speech_worker and self._speech_worker.isRunning():
            self._speech_worker.cancel()
        self._teaching_payload = None
        current_worker = self._voice_input_worker
        if current_worker is not None and current_worker.isRunning():
            current_worker.cancel()
            self.ai_panel.voice_btn.setText("Transcribing…")
            theme_name = str(self.settings.value("ui_theme", "dark", type=str) or "dark").lower()
            muted_icon = "#8a96a8" if theme_name == "light" else "#9aa7ba"
            self.ai_panel.voice_btn.setIcon(make_icon("mic", muted_icon, 16))
            self.ai_panel.voice_btn.setToolTip("Finishing the current speech phrase and placing it in the chat box")
            self.ai_panel.voice_btn.setProperty("recording", False)
            self.ai_panel.voice_btn.setProperty("transcribing", True)
            self.ai_panel.voice_btn.setStyleSheet("")
            self.ai_panel.voice_btn.style().unpolish(self.ai_panel.voice_btn)
            self.ai_panel.voice_btn.style().polish(self.ai_panel.voice_btn)
            self.ai_panel.voice_btn.setEnabled(False)
            self.ai_panel._set_activity("Finishing transcription…", animate=True)
            self.show_status("Stopping voice input · recognized words will stay in the chat box")
            return
        language = str(self.settings.value("voice_input_language", "ar-EG", type=str) or "ar-EG")
        # Capture the current draft so voice can append to text already typed or pasted.
        initial_text = self.ai_panel.prompt_edit.toPlainText().strip()
        worker = VoiceInputWorker(language, initial_text=initial_text)
        self._voice_input_worker = worker
        worker.progress.connect(self._on_voice_progress)
        worker.partialText.connect(self._on_voice_partial_text)
        worker.recognized.connect(self._on_voice_recognized)
        worker.failed.connect(self._on_voice_failure)
        worker.finished.connect(self._on_voice_worker_finished)
        self._voice_input_ignore_updates = False
        self.ai_panel.prompt_edit.setReadOnly(True)
        self._update_ask_by_voice_button(True)
        self.ai_panel._set_activity("Listening · tap to stop", animate=True)
        self.show_status("Voice input started · transcription appears in the chat box; press Send when ready")
        worker.start()

    def _on_voice_progress(self, message):
        text = str(message or "Listening…")
        if "Listening" in text:
            self.ai_panel._set_activity(text, animate=True)
        else:
            self.ai_panel._set_activity(text, animate=False)
        self.show_status(text)

    def _on_voice_partial_text(self, text):
        # Live recognition fills the normal chat editor but never submits a request.
        if bool(getattr(self, "_voice_input_ignore_updates", False)):
            return
        editor = self.ai_panel.prompt_edit
        value = str(text or "")
        if value and editor.toPlainText() != value:
            editor.setPlainText(value)
            editor.moveCursor(QTextCursor.MoveOperation.End)
        self.ai_panel._update_send_button_state()

    def _on_voice_recognized(self, text):
        # Final pass only synchronizes the draft; the user explicitly presses Send.
        if bool(getattr(self, "_voice_input_ignore_updates", False)):
            return
        self._on_voice_partial_text(text)
        if text:
            self.show_status("Voice transcription ready · review it and press Send")

    def _on_voice_failure(self, message):
        self.ai_panel._set_activity(str(message), animate=False)
        self.show_status("Voice input could not finish")
        QMessageBox.warning(self, "Ask by voice", str(message))

    def _stop_voice_input_for_send(self):
        """Stop microphone capture without allowing a late partial result to overwrite Send."""
        worker = getattr(self, "_voice_input_worker", None)
        if worker is not None and _qt_thread_is_running(worker):
            self._voice_input_ignore_updates = True
            worker.cancel()
            self.ai_panel.prompt_edit.setReadOnly(False)
            self._update_ask_by_voice_button(False)

    def _on_voice_worker_finished(self):
        worker = self._voice_input_worker
        self._voice_input_worker = None
        self._voice_input_ignore_updates = False
        self.ai_panel.prompt_edit.setReadOnly(False)
        self._update_ask_by_voice_button(False)
        if worker:
            worker.deleteLater()
        self._maybe_finish_pending_close()
        if not self.ai_panel._busy and self.ai_panel.busy_label.text().startswith(("Listening", "Recognizing", "Finishing transcription")):
            self.ai_panel._stop_activity_animation()
            self.ai_panel.busy_label.clear()

    @staticmethod
    def _speech_text(text: str) -> str:
        value = str(text or "")
        value = re.sub(r"```.*?```", " ", value, flags=re.S)
        value = re.sub(r"!\[[^\]]*\]\([^)]*\)", " ", value)
        value = re.sub(r"\[([^\]]+)\]\([^)]*\)", r"\1", value)
        value = _prepare_chat_markdown(value)
        value = re.sub(r"°\s*C", " درجة مئوية ", value, flags=re.I)
        value = re.sub(r"\^\s*°\s*C", " درجة مئوية ", value, flags=re.I)
        value = re.sub(r"\bkJ\s*/\s*kg\b", " كيلوجول لكل كيلوجرام ", value, flags=re.I)
        value = re.sub(r"\bkg\b", " كيلوجرام ", value, flags=re.I)
        value = re.sub(r"\bDBT\b", "درجة الحرارة الجافة", value, flags=re.I)
        value = re.sub(r"\bRH\b", "الرطوبة النسبية", value, flags=re.I)
        value = re.sub(r"^\s*\|?\s*:?-{3,}.*$", "", value, flags=re.M)
        value = re.sub(r"^\s{0,3}#{1,6}\s*", "", value, flags=re.M)
        value = re.sub(r"^\s*[-*+]\s+", "", value, flags=re.M)
        value = re.sub(r"^\s*\d+[.)]\s+", "", value, flags=re.M)
        value = re.sub(r"^\s*>\s?", "", value, flags=re.M)
        value = re.sub(r"[*_`~|]", " ", value)
        value = re.sub(r"\$+", " ", value)
        value = value.replace("\\", " ")
        # Say mathematical subscripts/superscripts as words, while preserving decimal points.
        subscript_map = str.maketrans("₀₁₂₃₄₅₆₇₈₉", "0123456789")
        superscript_map = str.maketrans("⁰¹²³⁴⁵⁶⁷⁸⁹", "0123456789")
        value = re.sub(r"([A-Za-z])([₀-₉]+)", lambda m: m.group(1) + " تحت " + m.group(2).translate(subscript_map), value)
        value = re.sub(r"([A-Za-z0-9])([⁰-⁹]+)", lambda m: m.group(1) + " أس " + m.group(2).translate(superscript_map), value)
        # Turn common symbols into words so SAPI does not announce punctuation.
        spoken_symbols = {"=": " يساوي ", "+": " زائد ", "−": " ناقص ", "-": " ناقص ",
                          "×": " في ", "÷": " على ", "≤": " أقل من أو يساوي ",
                          "≥": " أكبر من أو يساوي ", "≠": " لا يساوي ", "→": " ينتج عنه ",
                          "%": " في المئة ", "√": " الجذر التربيعي ", "π": " باي "}
        for symbol, spoken in spoken_symbols.items():
            value = value.replace(symbol, spoken)
        value = re.sub(r"[\[\]{}<>]", " ", value)
        # A dot between digits is a decimal separator, not sentence punctuation.
        value = re.sub(r"(?<!\d)\.(?!\d)", " ", value)
        value = re.sub(r"[،,:;!؟?]+", " ", value)
        value = re.sub(r"\s+", " ", value)
        return value.strip()

    def _start_speech(self, steps: list[dict], language: str | None = None):
        if self._speech_worker and self._speech_worker.isRunning():
            self._speech_worker.cancel()
            self._speech_worker.wait(900)
        language = language or str(self.settings.value("voice_input_language", "ar-EG", type=str) or "ar-EG")
        worker = SpeechPlaybackWorker(steps, language)
        self._speech_worker = worker
        worker.stepStarted.connect(self._on_teaching_step)
        worker.playbackFinished.connect(self._on_speech_finished)
        worker.failed.connect(self._on_speech_failure)
        worker.finished.connect(self._on_speech_worker_finished)
        self.show_status("Speaking answer… use Stop audio to interrupt")
        worker.start()

    def speak_latest_answer(self):
        self._teaching_payload = None
        path = self.ai_panel.document_path
        messages = self.ai_panel.messages_for_path(path) if path else []
        answer = next((str(item.get("content") or "") for item in reversed(messages)
                       if item.get("role") == "assistant" and str(item.get("content") or "").strip()), "")
        answer = self._speech_text(answer)
        if not answer:
            self.show_status("There is no AI answer to read yet")
            return
        self._start_speech([{"say": answer, "board": ""}])

    def stop_audio(self):
        if self._voice_input_worker and self._voice_input_worker.isRunning():
            self._voice_input_worker.cancel()
        if self._speech_worker and self._speech_worker.isRunning():
            self._speech_worker.cancel()
            self.show_status("Audio stopped")
        if self._ai_worker and self._ai_worker.isRunning() and self.ai_panel._busy:
            # Stop both the current AI generation and any pending spoken playback.
            self.cancel_ai_request()
        tab = self.active_tab()
        if tab:
            tab.canvas.update()

    def _on_speech_finished(self):
        self.show_status("Spoken explanation finished")

    def _on_speech_failure(self, message):
        self.show_status(str(message))
        QMessageBox.information(self, "Engo voice", str(message))

    def _on_speech_worker_finished(self):
        worker = self._speech_worker
        self._speech_worker = None
        if worker:
            worker.deleteLater()

    @staticmethod
    def _parse_teaching_payload(raw: str) -> dict:
        text = str(raw or "").strip()
        text = re.sub(r"^```(?:json)?\s*|\s*```$", "", text, flags=re.I).strip()
        first, last = text.find("{"), text.rfind("}")
        if first >= 0 and last > first:
            text = text[first:last + 1]
        payload = json.loads(text)
        if not isinstance(payload, dict):
            raise ValueError("The AI did not return a teaching plan.")
        steps = payload.get("steps")
        if not isinstance(steps, list) or not steps:
            raise ValueError("The AI returned no teaching steps. Try again or choose another model.")
        clean_steps = []
        for item in steps[:8]:
            if not isinstance(item, dict):
                continue
            page = item.get("page", 1)
            try:
                page = max(1, int(page))
            except Exception:
                page = 1
            box = item.get("box")
            if not isinstance(box, (list, tuple)) or len(box) != 4:
                box = None
            clean_steps.append({
                "say": str(item.get("say") or "").strip(),
                "board": str(item.get("board") or "").strip(),
                "page": page,
                "box": box,
                "label": str(item.get("label") or "Current region").strip(),
            })
        payload["steps"] = clean_steps
        if not clean_steps:
            raise ValueError("The AI returned no readable teaching steps.")
        return payload

    def _begin_teaching(self, raw_answer: str):
        try:
            payload = self._parse_teaching_payload(raw_answer)
        except Exception as exc:
            self.ai_panel.append_message_for(self.ai_panel.document_path, "assistant",
                "I couldn't format the teaching plan returned by the selected model. Try another model or ask again.\n\n" + str(exc))
            self.show_status("Could not parse teaching plan")
            return
        self._teaching_payload = payload
        steps = payload["steps"]
        lesson_text = "\n\n".join(f"**{i + 1}.** {step['say']}" for i, step in enumerate(steps))
        self.ai_panel.append_message_for(self.ai_panel.document_path, "assistant", f"## {payload.get('title', 'Current-page lesson')}\n\n{payload.get('overview', '')}\n\n{lesson_text}")
        self.teach_board.set_lesson(str(payload.get("title") or "Current-page lesson"),
                                    str(payload.get("overview") or "Follow each spoken step."),
                                    str(steps[0].get("board") or ""))
        self.teach_board.show()
        total_width = max(1, self.workspace.width())
        board_width = min(380, max(290, int(total_width * .23)))
        chat_width = min(530, max(430, int(total_width * .31)))
        self._animate_ai_panel(True, preferred_width=chat_width, board_width=board_width)
        self._start_speech(steps)

    def _on_teaching_step(self, index: int, step: dict):
        # Plain "Read latest" audio speaks without steering the page; structured lesson
        # playback alone drives the live page highlight and board.
        if not self._teaching_payload:
            return
        payload = self._teaching_payload or {}
        steps = payload.get("steps", [])
        self.teach_board.set_step(index, len(steps), step)
        tab = self.active_tab()
        if not tab:
            return
        page_index = max(0, min(int(step.get("page", 1)) - 1, tab.page_count - 1))
        if page_index != tab.current_page:
            tab.go_to_page(page_index)
        tab.canvas.set_ai_focus(page_index, step.get("box"), step.get("label"))
        tab.canvas.update()

    def send_ai_request(self, path, question, selected_images, include_context, mode, current_page_index=0):
        if self._speech_worker and self._speech_worker.isRunning():
            self._speech_worker.cancel()
        if mode != "teach":
            self._teaching_payload = None
        if self._ai_worker and self._ai_worker.isRunning():
            self.ai_panel.append_message_for(path, "assistant", "An AI request is already running. Please wait for it to finish.")
            self.ai_panel.set_busy(False)
            return
        provider = self.ai_panel.provider_combo.currentData()
        api_key = _get_provider_key(self.settings, provider)
        if not api_key:
            self.ai_panel.append_message_for(path, "assistant",
                f"No API key is configured for {AI_PROVIDER_LABELS.get(provider, provider)}. Open Application Settings → AI settings, add the key, then send your question again.")
            self.ai_panel.set_busy(False)
            return
        model = str(self.ai_panel.model_combo.currentData() or self.ai_panel.model_combo.currentText() or
                    self.settings.value(f"ai_chat_model_{provider}", AI_DEFAULT_MODELS[provider], type=str)).strip()
        if not model:
            model = AI_DEFAULT_MODELS[provider]
        self.ai_panel._store_chat_model(provider, model)
        self.ai_panel.set_pending_request_scope(path)
        history = self.ai_panel.api_history_for(path)
        if history and history[-1].get("role") == "user":
            history = history[:-1]
        supplemental_documents = self._linked_payload_for(path)
        pdf_snapshots = {}
        for snapshot_tab in [self._open_document_tab_by_path(path)] + [
                self._open_document_tab_by_path(item.get("path", "")) for item in supplemental_documents]:
            if snapshot_tab is None:
                continue
            try:
                if (not getattr(snapshot_tab.doc, "is_closed", True)
                        and snapshot_tab.has_unsaved_changes()):
                    pdf_snapshots[snapshot_tab.path] = snapshot_tab.doc.tobytes(garbage=4, deflate=True)
            except Exception:
                # Disk-backed reads remain available as a fallback if snapshotting fails.
                pass
        worker = AIRequestWorker(path, provider, model, api_key, question, history, include_context,
                                 selected_images, mode, current_page_index,
                                 supplemental_documents=supplemental_documents, pdf_snapshots=pdf_snapshots)
        # Long Arabic + LaTeX explanations were cut at the default 2500-token output limit.
        worker.max_output_tokens = 8192
        worker.streamed.connect(self._on_ai_delta)
        worker.succeeded.connect(self._on_ai_success)
        worker.failed.connect(self._on_ai_failure)
        worker.cancelled.connect(self._on_ai_cancelled)
        worker.progress.connect(self._on_ai_progress)
        worker.finished.connect(self._on_ai_worker_finished)
        self._ai_worker = worker
        self.ai_panel.set_busy(True)
        self.show_status(f"Sending request to {AI_PROVIDER_LABELS.get(provider, provider)}…")
        worker.start()

    def cancel_ai_request(self):
        """Cancel the current AI request while keeping the UI responsive."""
        worker = self._ai_worker
        if worker is None or not worker.isRunning():
            self.ai_panel.set_busy(False)
            return
        self.ai_panel.busy_label.setText("Stopping response…")
        self.ai_panel.stop_btn.setEnabled(False)
        self.show_status("Stop requested for AI response…")
        worker.cancel()

    def _on_ai_cancelled(self, path):
        self._speak_next_response = False
        self.ai_panel.append_message_for(path, "assistant", "_Response stopped by user._")
        self.show_status("AI response stopped")

    def _on_ai_delta(self, path, delta):
        self.ai_panel.busy_label.setText("Receiving answer…")
        self.ai_panel.append_stream_delta(path, delta)

    def _on_ai_success(self, path, answer):
        worker = self._ai_worker
        mode = getattr(worker, "mode", "custom") if worker is not None else "custom"
        if mode == "teach" and os.path.abspath(path) == os.path.abspath(self.ai_panel.document_path):
            self._begin_teaching(answer)
            return
        # Re-rendering the saved assistant message replaces the temporary live bubble.
        self.ai_panel.append_message_for(path, "assistant", answer)
        if self._speak_next_response and os.path.abspath(path) == os.path.abspath(self.ai_panel.document_path):
            self._speak_next_response = False
            self._teaching_payload = None
            clean = self._speech_text(answer)
            if clean:
                self._start_speech([{"say": clean, "board": ""}])
        self.show_status("AI response received")

    def _on_ai_progress(self, path, message):
        if self.ai_panel.document_path == path:
            self.ai_panel._set_activity(str(message or "Working"), animate=True)
        self.show_status(message)

    def _friendly_ai_error_message(self, error):
        raw = str(error or "").strip()
        low = raw.lower()
        network_terms = ("urlerror", "temporary failure", "name or service not known",
                         "getaddrinfo", "network is unreachable", "connection refused", "connection reset",
                         "failed to establish a new connection", "ssl", "nodename", "no route to host", "internet")
        busy_terms = ("429", "rate limit", "rate_limit", "overloaded", "resource_exhausted", "503", "502", "504",
                      "capacity", "temporarily unavailable", "server is busy", "high demand", "read timeout",
                      "did not send data before", "timed out", "timeout")
        model_terms = ("model not found", "does not exist", "unsupported model", "unknown model", "invalid model", "model id", "404", "empty response", "no content", "returned no output")
        if any(term in low for term in network_terms):
            return "**مشكلة في اتصال الإنترنت**\n\nلم يتمكن Engo من الوصول إلى مزود الذكاء الاصطناعي. افحص اتصال الإنترنت أو الـVPN/Proxy ثم أعد المحاولة. لم يتم تبديل الموديل تلقائيًا."
        if any(term in low for term in busy_terms):
            return "**الموديل مشغول أو عليه ضغط**\n\nالخدمة رفضت الطلب مؤقتًا أو وصلت إلى حد الاستخدام. انتظر قليلًا أو اختر موديلًا آخر من القائمة بجوار اسم مزود الخدمة في المحادثة ثم أعد الإرسال."
        if any(term in low for term in model_terms):
            return "**الموديل غير متاح لهذا الحساب**\n\nاختر موديلًا آخر من القائمة بجوار مزود الخدمة في المحادثة، أو افتح إعدادات AI واضغط Refresh available models لتحديث القائمة."
        return "**تعذر إكمال طلب AI**\n\nراجع تفاصيل الخطأ أدناه، وتأكد من صحة مفتاح API وإعدادات مزود الخدمة."

    def _on_ai_failure(self, path, error):
        self._speak_next_response = False
        friendly = self._friendly_ai_error_message(error)
        # Raw HTML (<details>) is escaped by the chat renderer and Qt cannot collapse it, so it was shown as literal text.
        # Use plain Markdown only: a bold label followed by a code block.
        _is_ar = str(self.settings.value("interface_language", "en", type=str) or "en").lower().startswith("ar")
        _details_label = "التفاصيل التقنية" if _is_ar else "Technical details"
        self.ai_panel.append_message_for(path, "assistant", f"{friendly}\n\n**{_details_label}**\n\n```text\n{str(error)[:1800]}\n```")
        self.show_status("AI request failed · see the suggested fix in chat")

    def _on_ai_worker_finished(self):
        worker = self._ai_worker
        self._ai_worker = None
        self.ai_panel.set_busy(False)
        self.ai_panel.clear_pending_request_scope()
        if worker is not None:
            worker.deleteLater()
        self._maybe_finish_pending_close()

    def _maybe_finish_pending_close(self):
        if not self._close_after_cancel:
            return
        ai_active = self._ai_worker is not None and self._ai_worker.isRunning()
        translation_active = any(w.isRunning() for w in getattr(self, "_translation_workers", []))
        live_active = self._live_tutor_worker is not None and self._live_tutor_worker.isRunning()
        search_active = _qt_thread_is_running(self._pdf_search_worker)
        if not ai_active and not translation_active and not live_active and not search_active:
            self._close_after_cancel = False
            QTimer.singleShot(0, self.close)

    def open_page_theme(self):
        dlg = PageThemeDialog(
            self, self.dark_mode, self.bg_color, self.ink_color,
            self.custom_page_themes, self.smart_page_theme,
        )
        if dlg.exec() == QDialog.DialogCode.Accepted:
            self.dark_mode = dlg.toggle.isChecked()
            self.smart_page_theme = dlg.smart_toggle.isChecked()
            self.bg_color, self.ink_color = dlg.bg, dlg.ink
            self.custom_page_themes = dict(dlg.custom_themes)
            self.settings.setValue("dark_mode", self.dark_mode)
            self.settings.setValue("smart_page_theme", self.smart_page_theme)
            self.settings.setValue("page_bg", self.bg_color)
            self.settings.setValue("page_ink", self.ink_color)
            self.settings.setValue("custom_page_themes", json.dumps(self.custom_page_themes, ensure_ascii=False))
            for i in range(self.tabs.count()):
                tab = self.tabs.widget(i)
                if isinstance(tab, DocumentTab):
                    tab.set_theme(self.dark_mode, self.bg_color, self.ink_color, self.smart_page_theme)
            # Keep the PAGE inside Voice & Learn synchronized with the actual document theme.
            if self._live_tutor_dialog is not None and self._live_tutor_dialog.isVisible():
                self.refresh_live_tutor_page(self._live_tutor_dialog)
            self.show_status("Page Theme updated")

    def open_annotation_colors(self):
        dlg = AnnotationColorsDialog(self, self.annotation_colors)
        if dlg.exec() == QDialog.DialogCode.Accepted:
            self.annotation_colors = dict(dlg.colors)
            self.settings.setValue("annotation_colors", json.dumps(self.annotation_colors))
            # Apply immediately to open tabs, so every tab uses the same saved color palette.
            for i in range(self.tabs.count()):
                tab = self.tabs.widget(i)
                if isinstance(tab, DocumentTab):
                    tab.annotation_colors = dict(self.annotation_colors)
                    tab.canvas.update()
            self.show_status("Annotation colors saved for new highlights, pen strokes, notes, and text boxes")

    def _all_document_tags(self):
        """Read the legacy per-document tag registry (used only for migration)."""
        raw = self.settings.value("document_tags_json", "{}", type=str)
        try:
            data = json.loads(raw) if raw else {}
            return data if isinstance(data, dict) else {}
        except Exception:
            return {}

    def _document_tag_key(self, path):
        return os.path.normcase(os.path.abspath(path or ""))

    @staticmethod
    def _tag_default_palette():
        return ["#f2bd55", "#66c7e8", "#9b8cff", "#62c98b", "#f08080",
                "#e38bc8", "#7ca8ff", "#c5a65f", "#53c9b5", "#d28a55"]

    def _tag_aliases(self):
        raw = self.settings.value("tag_aliases_json", "{}", type=str)
        try:
            data = json.loads(raw) if raw else {}
            return data if isinstance(data, dict) else {}
        except Exception:
            return {}

    def _canonical_tag_name(self, name):
        value = str(name or "").strip()[:32]
        aliases = self._tag_aliases()
        seen = set()
        while value and value.casefold() not in seen:
            seen.add(value.casefold())
            match = next((v for k, v in aliases.items() if str(k).casefold() == value.casefold()), None)
            if not match:
                break
            value = str(match).strip()[:32]
        return value

    def _deleted_tag_names(self):
        raw = self.settings.value("deleted_tag_names_json", "[]", type=str)
        try:
            values = json.loads(raw) if raw else []
            return {str(value).strip().casefold() for value in values if str(value).strip()} if isinstance(values, list) else set()
        except Exception:
            return set()

    def _save_tag_library(self, library):
        clean = {}
        if isinstance(library, dict):
            for name, color in library.items():
                name = str(name or "").strip()[:32]
                if not name or any(str(existing).casefold() == name.casefold() for existing in clean):
                    continue
                color = str(color or "")
                if not QColor(color).isValid():
                    color = self._tag_default_palette()[len(clean) % len(self._tag_default_palette())]
                clean[name] = QColor(color).name()
        self.settings.setValue("tag_library_json", json.dumps(clean, ensure_ascii=False))
        self.settings.remove("tag_usage_cache_json")
        self.settings.sync()
        return clean

    def _tag_library(self):
        """Return the program-wide tag catalogue, migrating older per-PDF settings once."""
        raw = self.settings.value("tag_library_json", None)
        if raw is not None:
            try:
                parsed = json.loads(raw) if isinstance(raw, str) else dict(raw)
                if isinstance(parsed, dict):
                    return parsed
            except Exception:
                pass

        # One-time migration: merge each old document's tag list and first known color
        # into a single application-wide catalogue.
        library = {}
        old_tags = self._all_document_tags()
        old_colors = self._all_document_tag_colors()
        for doc_key, names in old_tags.items():
            if not isinstance(names, list):
                continue
            color_map = old_colors.get(doc_key, {}) if isinstance(old_colors, dict) else {}
            if not isinstance(color_map, dict):
                color_map = {}
            for name in names:
                name = str(name or "").strip()[:32]
                if not name or any(existing.casefold() == name.casefold() for existing in library):
                    continue
                color = str(color_map.get(name) or "")
                if not QColor(color).isValid():
                    color = self._tag_default_palette()[len(library) % len(self._tag_default_palette())]
                library[name] = QColor(color).name()

        # Recover tags from PDFs currently open in this app if the older preference
        # list was absent (for example, a PDF was moved from another PC).
        try:
            for tab_index in range(self.tabs.count()):
                tab = self.tabs.widget(tab_index)
                if not isinstance(tab, DocumentTab) or getattr(tab.doc, "is_closed", True):
                    continue
                for page_index in range(tab.page_count):
                    page = tab.doc.load_page(page_index)
                    for annot in list(page.annots() or []):
                        info = annot.info or {}
                        if str(info.get("title") or "") != "Engo Region Tag":
                            continue
                        name = str(info.get("content") or "").strip()[:32]
                        if not name or name.casefold() in self._deleted_tag_names():
                            continue
                        if any(existing.casefold() == name.casefold() for existing in library):
                            continue
                        stroke = (annot.colors or {}).get("stroke")
                        color = ""
                        if isinstance(stroke, (tuple, list)) and len(stroke) >= 3:
                            try:
                                color = QColor.fromRgbF(*[max(0.0, min(1.0, float(v))) for v in stroke[:3]]).name()
                            except Exception:
                                color = ""
                        library[name] = color if QColor(color).isValid() else self._tag_default_palette()[len(library) % len(self._tag_default_palette())]
        except Exception:
            pass
        return self._save_tag_library(library)

    def _sync_tag_annotations_in_tab(self, tab, library=None):
        """Apply global rename/delete/color changes to this PDF's embedded tag annotations."""
        if not isinstance(tab, DocumentTab) or getattr(tab.doc, "is_closed", True):
            return
        library = library if isinstance(library, dict) else self._tag_library()
        aliases = self._tag_aliases()
        deleted = self._deleted_tag_names()
        changed_pages = []
        undo_recorded = False
        for page_index in range(tab.page_count):
            try:
                page = tab.doc.load_page(page_index)
                for annot in list(page.annots() or []):
                    info = annot.info or {}
                    if str(info.get("title") or "") != "Engo Region Tag":
                        continue
                    old_name = str(info.get("content") or "").strip()
                    if not old_name:
                        continue
                    if old_name.casefold() in deleted:
                        if not undo_recorded:
                            tab._record_undo()
                            undo_recorded = True
                        page.delete_annot(annot)
                        if page_index not in changed_pages:
                            changed_pages.append(page_index)
                        continue
                    canonical = self._canonical_tag_name(old_name)
                    target_name = next((n for n in library if str(n).casefold() == canonical.casefold()), None)
                    if target_name is None:
                        # Register a tag carried by an external PDF so it becomes
                        # available in the shared application library.
                        stroke = (annot.colors or {}).get("stroke")
                        color = ""
                        if isinstance(stroke, (tuple, list)) and len(stroke) >= 3:
                            try:
                                color = QColor.fromRgbF(*[max(0.0, min(1.0, float(v))) for v in stroke[:3]]).name()
                            except Exception:
                                color = ""
                        library[old_name] = color if QColor(color).isValid() else self._tag_default_palette()[len(library) % len(self._tag_default_palette())]
                        target_name = old_name
                        self._save_tag_library(library)
                    desired_color = str(library.get(target_name) or "")
                    stroke = (annot.colors or {}).get("stroke")
                    current_color = ""
                    if isinstance(stroke, (tuple, list)) and len(stroke) >= 3:
                        try:
                            current_color = QColor.fromRgbF(*[max(0.0, min(1.0, float(v))) for v in stroke[:3]]).name()
                        except Exception:
                            current_color = ""
                    needs_name = target_name != old_name
                    needs_color = QColor(desired_color).isValid() and current_color.casefold() != QColor(desired_color).name().casefold()
                    if needs_name or needs_color:
                        if not undo_recorded:
                            tab._record_undo()
                            undo_recorded = True
                        if needs_name:
                            annot.set_info(title="Engo Region Tag", content=target_name)
                        if needs_color:
                            annot.set_colors(stroke=color_tuple(desired_color))
                        annot.update()
                        if page_index not in changed_pages:
                            changed_pages.append(page_index)
            except Exception:
                continue
        if changed_pages:
            for page_index in changed_pages:
                tab._changed(page_index)

    def document_tags(self, path=None):
        """Return the shared tag catalogue without modifying any open PDF.

        This method is called while rebuilding menus and refreshing ordinary UI
        controls. It must remain read-only: synchronizing embedded PDF annotations
        here made unrelated actions (including changing Book/Scroll view) appear
        to edit the document and triggered false Save prompts.
        """
        return list(self._tag_library().keys())

    def _save_document_tags(self, path, tags):
        """Compatibility shim: older callers now update the global tag library."""
        library = self._tag_library()
        wanted = {str(item).strip() for item in (tags or []) if str(item).strip()}
        for name in wanted:
            if not any(existing.casefold() == name.casefold() for existing in library):
                library[name[:32]] = self._tag_default_palette()[len(library) % len(self._tag_default_palette())]
        return self._save_tag_library(library)

    def _all_document_tag_colors(self):
        raw = self.settings.value("document_tag_colors_json", "{}", type=str)
        try:
            data = json.loads(raw) if raw else {}
            return data if isinstance(data, dict) else {}
        except Exception:
            return {}

    def _tag_color(self, tab, tag_name):
        library = self._tag_library()
        canonical = self._canonical_tag_name(tag_name)
        for name, color in library.items():
            if str(name).casefold() == canonical.casefold() and QColor(str(color)).isValid():
                return QColor(str(color)).name()
        palette = self._tag_default_palette()
        index = next((i for i, name in enumerate(library) if str(name).casefold() == canonical.casefold()), 0)
        return palette[index % len(palette)]

    def _save_tag_color(self, path, tag_name, color):
        library = self._tag_library()
        canonical = self._canonical_tag_name(tag_name)
        for existing in list(library):
            if existing.casefold() == canonical.casefold():
                library[existing] = QColor(color).name()
                break
        self._save_tag_library(library)

    def _tag_usage_summary(self, tag_names):
        """Count tag uses in open PDFs and the app's recent-file catalogue, with file-stat caching."""
        wanted = {str(name).casefold(): str(name) for name in tag_names}
        totals = {name: {"regions": 0, "documents": 0} for name in tag_names}
        paths = {}
        open_tabs = {}
        try:
            for index in range(self.tabs.count()):
                tab = self.tabs.widget(index)
                if isinstance(tab, DocumentTab) and not getattr(tab.doc, "is_closed", True):
                    key = self._document_tag_key(tab.path)
                    paths[key] = tab.path
                    open_tabs[key] = tab
        except Exception:
            pass
        try:
            for entry in self._load_recent_files():
                path = str(entry.get("path") or "")
                if path:
                    paths.setdefault(self._document_tag_key(path), path)
        except Exception:
            pass

        raw_cache = self.settings.value("tag_usage_cache_json", "{}", type=str)
        try:
            cache = json.loads(raw_cache) if raw_cache else {}
            if not isinstance(cache, dict):
                cache = {}
        except Exception:
            cache = {}
        aliases = self._tag_aliases()
        deleted = self._deleted_tag_names()
        for key, path in paths.items():
            try:
                stat = os.stat(path)
                stamp = int(stat.st_mtime_ns)
                size = int(stat.st_size)
            except OSError:
                continue
            cached = cache.get(key, {}) if key not in open_tabs else {}
            counts = None
            if (isinstance(cached, dict) and cached.get("mtime") == stamp and cached.get("size") == size
                    and isinstance(cached.get("counts"), dict)):
                counts = cached["counts"]
            if counts is None:
                doc = None
                should_close = False
                try:
                    if key in open_tabs:
                        doc = open_tabs[key].doc
                    else:
                        doc = fitz.open(path)
                        should_close = True
                    counts = {}
                    for page_index in range(doc.page_count):
                        page = doc.load_page(page_index)
                        for annot in list(page.annots() or []):
                            info = annot.info or {}
                            if str(info.get("title") or "") != "Engo Region Tag":
                                continue
                            raw_name = str(info.get("content") or "").strip()
                            if not raw_name or raw_name.casefold() in deleted:
                                continue
                            canonical = raw_name
                            seen_aliases = set()
                            while canonical.casefold() not in seen_aliases:
                                seen_aliases.add(canonical.casefold())
                                alias = next((v for k2, v in aliases.items() if str(k2).casefold() == canonical.casefold()), None)
                                if not alias:
                                    break
                                canonical = str(alias).strip()
                            match = next((actual for folded, actual in wanted.items() if folded == canonical.casefold()), None)
                            if match:
                                counts[match] = int(counts.get(match, 0)) + 1
                except Exception:
                    counts = {}
                finally:
                    if should_close and doc is not None:
                        try:
                            doc.close()
                        except Exception:
                            pass
                if key not in open_tabs:
                    cache[key] = {"mtime": stamp, "size": size, "counts": counts}
            for name, count in counts.items():
                if name in totals and int(count or 0) > 0:
                    totals[name]["regions"] += int(count)
                    totals[name]["documents"] += 1
        try:
            self.settings.setValue("tag_usage_cache_json", json.dumps(cache, ensure_ascii=False))
        except Exception:
            pass
        return totals

    def _selected_region_tag(self, tab):
        key = self._document_tag_key(getattr(tab, "path", ""))
        selected = getattr(self, "_selected_region_tags", {}).get(key, "")
        if selected not in self.document_tags(tab.path):
            selected = self.document_tags(tab.path)[0] if self.document_tags(tab.path) else ""
        return selected, self._tag_color(tab, selected) if selected else "#f2bd55"

    def _select_region_tag(self, tag_name, tab=None):
        tab = tab or self._view_target_tab() or self.active_tab()
        if tab is None:
            return
        name = str(tag_name or "").strip()
        if name and name not in self.document_tags(tab.path):
            return
        if not hasattr(self, "_selected_region_tags"):
            self._selected_region_tags = {}
        self._selected_region_tags[self._document_tag_key(tab.path)] = name
        self._refresh_tag_menu(tab)
        if name:
            self._set_tool("tag", quiet=True)
            self.show_status(f"Tag selected: {name} · drag over a page region to assign it")

    def _apply_tag_manager_dialog_theme(self, dialog):
        """Apply the active Engo theme to the tag manager and its child controls."""
        theme = normalize_ui_theme(self.settings.value("ui_theme", "dark", type=str))
        # Use the same six-theme semantic tokens as the main window and every
        # other popup. Previously Grass/Pink/Orange fell through to Dark here.
        tokens = engo_ui_theme_tokens(theme)
        c = {
            "bg": tokens["window"], "card": tokens["panel"], "field": tokens["input"],
            "text": tokens["text"], "muted": tokens["muted"], "border": tokens["border"],
            "soft": tokens["selection"], "soft_text": tokens["selection_text"],
            "hover": tokens["hover"], "accent": tokens["accent"],
            "danger": "#b54755" if theme == "light" else "#f0a2ad",
            "danger_bg": tokens["panel_alt"], "scroll": tokens["scrollbar"],
        }
        palette = QPalette(dialog.palette())
        for role, key in ((QPalette.ColorRole.Window,"bg"), (QPalette.ColorRole.WindowText,"text"),
                          (QPalette.ColorRole.Base,"field"), (QPalette.ColorRole.AlternateBase,"card"),
                          (QPalette.ColorRole.Text,"text"), (QPalette.ColorRole.Button,"card"),
                          (QPalette.ColorRole.ButtonText,"text"), (QPalette.ColorRole.Highlight,"soft"),
                          (QPalette.ColorRole.HighlightedText,"soft_text")):
            palette.setColor(role, QColor(c[key]))
        dialog.setPalette(palette)
        dialog.setAttribute(Qt.WidgetAttribute.WA_StyledBackground, True)
        dialog.setStyleSheet(f"""
            QDialog#tagManagerDialog {{ background:{c['bg']}; color:{c['text']}; }}
            QDialog#tagManagerDialog QWidget {{ color:{c['text']}; }}
            QLabel#tagManagerTitle {{ color:{c['text']}; font-size:16pt; font-weight:750; }}
            QLabel#tagManagerSubtitle, QLabel#tagManagerFooter {{ color:{c['muted']}; }}
            QLabel#tagManagerHint {{ color:{c['text']}; padding:0; background:transparent; border:0; border-radius:0; }}
            QListWidget#tagManagerList {{ background:transparent; border:0; outline:0; padding:3px; }}
            QListWidget#tagManagerList::item {{ border:0; padding:0; background:transparent; }}
            QListWidget#tagManagerList QScrollBar:vertical {{ background:{c['bg']}; width:8px; margin:3px 1px; border-radius:4px; }}
            QListWidget#tagManagerList QScrollBar::handle:vertical {{ background:{c['scroll']}; min-height:24px; border-radius:4px; }}
            QListWidget#tagManagerList QScrollBar::add-line:vertical, QListWidget#tagManagerList QScrollBar::sub-line:vertical {{ height:0; }}
            QFrame#tagManagerCard {{ background:transparent; border:0; border-radius:0; }}
            QLabel#tagManagerName {{ color:{c['text']}; font-size:10.5pt; font-weight:700; }}
            QLabel#tagManagerMeta {{ color:{c['muted']}; font-size:8.5pt; }}
            QLabel#tagManagerStatus {{ background:transparent; border:0; border-radius:0; padding:0; font-size:8pt; font-weight:800; }}
            QLabel#tagManagerStatus[used="true"] {{ color:#3d9b6b; }}
            QLabel#tagManagerStatus[used="false"] {{ color:{c['muted']}; }}
            QPushButton#tagManagerAction {{ color:{c['text']}; background:{c['hover']}; border:1px solid {c['border']}; border-radius:8px; padding:4px 8px; }}
            QPushButton#tagManagerAction:hover {{ background:{c['soft']}; border-color:{c['accent']}; }}
            QPushButton#tagManagerDelete {{ color:{c['danger']}; background:{c['danger_bg']}; border:1px solid {c['border']}; border-radius:8px; padding:4px; }}
            QPushButton#tagManagerDelete:hover {{ border-color:{c['danger']}; }}
            QPushButton#tagManagerPrimary {{ color:#ffffff; background:{c['accent']}; border:1px solid {c['accent']}; border-radius:9px; padding:9px 14px; font-weight:700; }}
            QPushButton#tagManagerPrimary:hover {{ background:{c['soft']}; color:{c['soft_text']}; }}
            QPushButton#tagManagerClose {{ color:{c['text']}; background:{c['card']}; border:1px solid {c['border']}; border-radius:8px; padding:8px 16px; }}
            QToolTip {{ background:{c['card']}; color:{c['text']}; border:1px solid {c['border']}; padding:5px 7px; }}
            QInputDialog, QMessageBox, QColorDialog {{ background:{c['bg']}; color:{c['text']}; }}
            QLineEdit, QTextEdit {{ background:{c['field']}; color:{c['text']}; border:1px solid {c['border']}; selection-background-color:{c['accent']}; selection-color:#ffffff; }}
        """)
        direction = Qt.LayoutDirection.RightToLeft if str(self.settings.value("interface_language", "en", type=str)).lower().startswith("ar") else Qt.LayoutDirection.LeftToRight
        dialog.setLayoutDirection(direction)
        for child in dialog.findChildren(QWidget):
            try: child.setLayoutDirection(direction)
            except RuntimeError: pass

    def _refresh_tag_menu(self, tab=None):
        if not hasattr(self, "tag_menu"):
            return
        tab = tab or self._view_target_tab() or self.active_tab()
        self.tag_menu.clear()
        tags = self.document_tags(tab.path) if tab is not None else []
        selected, selected_color = self._selected_region_tag(tab) if tab is not None else ("", "#d5b1ff")
        for name in tags:
            color = self._tag_color(tab, name)
            action = self.tag_menu.addAction(make_icon("tag", color, 15), name)
            action.setCheckable(True)
            action.setChecked(name == selected)
            action.triggered.connect(lambda checked=False, value=name, owner=tab: self._select_region_tag(value, owner))
        is_ar = str(self.settings.value("interface_language", "en", type=str) or "en").lower().startswith("ar")
        if not tags:
            empty = self.tag_menu.addAction("لا توجد وسوم بعد" if is_ar else "No tags yet")
            empty.setEnabled(False)
        self.tag_menu.addSeparator()
        edit = self.tag_menu.addAction("تعديل الوسوم…" if is_ar else "Edit tags…")
        edit.triggered.connect(lambda _checked=False, owner=tab: self.open_tag_manager(owner))
        self.tag_menu.setLayoutDirection(Qt.LayoutDirection.RightToLeft if is_ar else Qt.LayoutDirection.LeftToRight)
        self._apply_popup_menu_style(self.tag_menu)
        if hasattr(self, "tag_tool_btn"):
            self.tag_tool_btn.setIcon(make_icon("tag", selected_color if selected else "#d5b1ff", 18))
            self.tag_tool_btn.setToolTip(
                ((f"وسم منطقة · الوسم الحالي: {selected}. اسحب فوق المنطقة لإسناد الوسم، أو استخدم السهم لاختيار الوسوم وتعديلها") if selected else "وسم منطقة · أنشئ وسمًا أو اختر وسمًا من قائمة السهم")
                if is_ar else
                (f"Tag region · current tag: {selected}. Drag over an area to assign it; use the arrow to choose or edit tags"
                 if selected else "Tag region · create or choose a tag from the arrow menu")
            )

    @staticmethod
    def _has_tag_annotations(tab, tag_name):
        try:
            for page_index in range(tab.page_count):
                page = tab.doc.load_page(page_index)
                for annot in list(page.annots() or []):
                    info = annot.info or {}
                    if (str(info.get("title") or "") == "Engo Region Tag"
                            and str(info.get("content") or "").strip() == str(tag_name)):
                        return True
        except Exception:
            return False
        return False

    def _update_tag_annotation_records(self, tab, old_name=None, new_name=None, new_color=None, delete=False):
        """Rename, recolor or remove all PDF region annotations for one tag."""
        changed_pages = []
        for page_index in range(tab.page_count):
            page = tab.doc.load_page(page_index)
            for annot in list(page.annots() or []):
                info = annot.info or {}
                if str(info.get("title") or "") != "Engo Region Tag":
                    continue
                if str(info.get("content") or "").strip() != str(old_name or ""):
                    continue
                if page_index not in changed_pages:
                    changed_pages.append(page_index)
                if delete:
                    page.delete_annot(annot)
                else:
                    annot.set_info(title="Engo Region Tag", content=str(new_name if new_name is not None else old_name))
                    if new_color:
                        annot.set_colors(stroke=color_tuple(new_color))
                    annot.update()
        if changed_pages:
            for page_index in changed_pages:
                tab._changed(page_index)
        return bool(changed_pages)

    def open_tag_manager(self, tab=None):
        """Manage the program-wide tag library shared by every PDF."""
        tab = tab or self._view_target_tab() or self.active_tab()
        dialog = QDialog(self)
        dialog.setObjectName("tagManagerDialog")
        dialog.setWindowTitle("Manage tag library")
        dialog.setMinimumSize(580, 460)
        dialog.resize(680, 570)
        self._apply_tag_manager_dialog_theme(dialog)
        root = QVBoxLayout(dialog)
        root.setContentsMargins(20, 18, 20, 16)
        root.setSpacing(12)
        header = QHBoxLayout()
        heading = QVBoxLayout()
        is_ar = str(self.settings.value("interface_language", "en", type=str) or "en").lower().startswith("ar")
        title = QLabel("مكتبة الوسوم" if is_ar else "Tag library")
        title.setObjectName("tagManagerTitle")
        subtitle = QLabel("مجموعة واحدة مشتركة لكل ملفات PDF" if is_ar else "One shared collection for all your PDFs")
        subtitle.setObjectName("tagManagerSubtitle")
        heading.addWidget(title)
        heading.addWidget(subtitle)
        header.addLayout(heading, 1)
        add_btn = QPushButton("＋  وسم جديد" if is_ar else "＋  New tag")
        add_btn.setObjectName("tagManagerPrimary")
        header.addWidget(add_btn)
        root.addLayout(header)
        hint = QLabel("تُحفظ الوسوم داخل Engo نفسه، وليس داخل ملف PDF واحد. توضح حالتا مستخدم / غير مستخدم التعيينات الموجودة في ملفات PDF الأخيرة والمفتوحة حاليًا." if is_ar else "Tags are saved in Engo itself, not inside one PDF. Used / Unused reflects assignments found in your recent and currently open PDFs.")
        hint.setObjectName("tagManagerHint")
        hint.setWordWrap(True)
        root.addWidget(hint)
        listing = QListWidget()
        listing.setObjectName("tagManagerList")
        listing.setSpacing(5)
        listing.setSelectionMode(QListWidget.SelectionMode.NoSelection)
        # Keep the tag list inside the dialog and scroll it when the library grows.
        listing.setVerticalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAsNeeded)
        listing.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        listing.setVerticalScrollMode(QAbstractItemView.ScrollMode.ScrollPerPixel)
        listing.setMinimumHeight(150)
        root.addWidget(listing, 1)
        footer = QHBoxLayout()
        footer.setContentsMargins(2, 0, 2, 0)
        footer_label = QLabel("")
        footer_label.setObjectName("tagManagerFooter")
        footer.addWidget(footer_label, 1)
        close_btn = QPushButton("تم" if is_ar else "Done")
        close_btn.setObjectName("tagManagerClose")
        close_btn.clicked.connect(dialog.accept)
        footer.addWidget(close_btn)
        root.addLayout(footer)

        def refresh(preferred_name=None):
            listing.clear()
            tags = self.document_tags(tab.path if tab is not None else None)
            usage = self._tag_usage_summary(tags)
            selected_name = preferred_name or (self._selected_region_tag(tab)[0] if tab is not None else "")
            for name in tags:
                color = self._tag_color(tab, name)
                stats = usage.get(name, {"regions": 0, "documents": 0})
                count = int(stats.get("regions", 0))
                docs = int(stats.get("documents", 0))
                used = count > 0
                item = QListWidgetItem()
                item.setData(Qt.ItemDataRole.UserRole, name)
                item.setSizeHint(QSize(0, 58))
                listing.addItem(item)
                card = QFrame()
                card.setObjectName("tagManagerCard")
                # Subtle border marks only the tag selected for the current PDF tool;
                # it is separate from the Used / Unused lifecycle state.
                card.setProperty("selectedForTool", name == selected_name)
                card_layout = QHBoxLayout(card)
                card_layout.setContentsMargins(10, 5, 8, 5)
                card_layout.setSpacing(8)
                # Show the tag's color through its icon only. The old vertical
                # color strip and filled "TAG" tile used space without adding
                # information that the colored tag glyph does not already convey.
                tag_icon_label = QLabel()
                tag_icon_label.setAlignment(Qt.AlignmentFlag.AlignCenter)
                tag_icon_label.setFixedSize(28, 28)
                tag_icon_label.setPixmap(make_icon("tag", color, 22).pixmap(QSize(24, 24)))
                tag_icon_label.setToolTip(f"{name} · {color}")
                card_layout.addWidget(tag_icon_label)
                details = QVBoxLayout()
                details.setSpacing(2)
                name_label = QLabel(name)
                name_label.setObjectName("tagManagerName")
                meta_row = QHBoxLayout()
                meta_row.setSpacing(7)
                meta = QLabel((f"{count} منطقة · {docs} ملف PDF" if is_ar else f"{count} {'region' if count == 1 else 'regions'} · {docs} {'PDF' if docs == 1 else 'PDFs'}"))
                meta.setObjectName("tagManagerMeta")
                meta_row.addWidget(meta)
                state_label = QLabel(("مستخدم" if used else "غير مستخدم") if is_ar else ("USED" if used else "UNUSED"))
                state_label.setObjectName("tagManagerStatus")
                state_label.setProperty("used", used)
                meta_row.addWidget(state_label)
                meta_row.addStretch(1)
                details.addWidget(name_label)
                details.addLayout(meta_row)
                card_layout.addLayout(details, 1)
                rename_btn = QPushButton("إعادة تسمية" if is_ar else "Rename")
                rename_btn.setObjectName("tagManagerAction")
                rename_btn.setToolTip((f"إعادة تسمية {name} في مكتبة الوسوم بالكامل" if is_ar else f"Rename {name} everywhere in the tag library"))
                rename_btn.clicked.connect(lambda _checked=False, value=name: rename_tag(value))
                card_layout.addWidget(rename_btn)
                color_btn = QPushButton()
                color_btn.setObjectName("tagManagerAction")
                color_btn.setIcon(make_icon("palette", color, 16))
                color_btn.setFixedWidth(38)
                color_btn.setToolTip((f"تغيير اللون المشترك للوسم {name}" if is_ar else f"Change the shared color for {name}"))
                color_btn.setAccessibleName((f"تغيير لون {name}" if is_ar else f"Change color for {name}"))
                color_btn.clicked.connect(lambda _checked=False, value=name: recolor_tag(value))
                card_layout.addWidget(color_btn)
                delete_btn = QPushButton()
                delete_btn.setObjectName("tagManagerDelete")
                delete_btn.setIcon(make_icon("delete", "#e79aa5", 16))
                delete_btn.setFixedWidth(38)
                delete_btn.setToolTip((f"حذف {name} من مكتبة الوسوم العامة" if is_ar else f"Delete {name} from the global tag library"))
                delete_btn.setAccessibleName((f"حذف {name}" if is_ar else f"Delete {name}"))
                delete_btn.clicked.connect(lambda _checked=False, value=name: remove_tag(value))
                card_layout.addWidget(delete_btn)
                listing.setItemWidget(item, card)
            total_uses = sum(int(value.get("regions", 0)) for value in usage.values())
            footer_label.setText((f"{len(tags)} وسم · {total_uses} استخدام في ملفات PDF الأخيرة والمفتوحة" if is_ar else f"{len(tags)} tags  ·  {total_uses} uses found across recent/open PDFs"))
            active_for_tag_menu = self._view_target_tab() or self.active_tab() or tab
            if isinstance(active_for_tag_menu, DocumentTab):
                self._refresh_tag_menu(active_for_tag_menu)

        def rename_tag(old_name):
            prompt = QInputDialog(dialog)
            prompt.setInputMode(QInputDialog.InputMode.TextInput)
            prompt.setWindowTitle("إعادة تسمية الوسم" if is_ar else "Rename tag")
            prompt.setLabelText("اسم الوسم الجديد:" if is_ar else "New tag name:")
            prompt.setTextValue(old_name)
            prompt.setOkButtonText("موافق" if is_ar else "OK")
            prompt.setCancelButtonText("إلغاء" if is_ar else "Cancel")
            self._apply_tag_manager_dialog_theme(prompt)
            ok = prompt.exec() == QDialog.DialogCode.Accepted
            new_name = prompt.textValue()
            new_name = str(new_name or "").strip()[:32]
            if not ok or not new_name or new_name == old_name:
                return
            library = self._tag_library()
            if any(str(existing).casefold() == new_name.casefold() for existing in library):
                QMessageBox.information(dialog, "وسم موجود" if is_ar else "Existing tag", "يوجد وسم آخر بهذا الاسم بالفعل." if is_ar else "Another tag already uses that name.")
                return
            color = self._tag_color(tab, old_name)
            library = {name: value for name, value in library.items() if name.casefold() != old_name.casefold()}
            library[new_name] = color
            self._save_tag_library(library)
            aliases = self._tag_aliases()
            for alias, target in list(aliases.items()):
                if str(target).casefold() == old_name.casefold():
                    aliases[alias] = new_name
            aliases[old_name] = new_name
            self.settings.setValue("tag_aliases_json", json.dumps(aliases, ensure_ascii=False))
            deleted = [v for v in self._deleted_tag_names() if v != old_name.casefold()]
            self.settings.setValue("deleted_tag_names_json", json.dumps(deleted, ensure_ascii=False))
            self.settings.sync()
            for index in range(self.tabs.count()):
                current = self.tabs.widget(index)
                if not isinstance(current, DocumentTab):
                    continue
                if self._has_tag_annotations(current, old_name):
                    current._record_undo()
                    self._update_tag_annotation_records(current, old_name=old_name, new_name=new_name, new_color=color)
                key = self._document_tag_key(current.path)
                selected = getattr(self, "_selected_region_tags", {}).get(key, "")
                if str(selected).casefold() == old_name.casefold():
                    self._selected_region_tags[key] = new_name
            refresh(new_name)

        def recolor_tag(name):
            current = QColor(self._tag_color(tab, name))
            color_picker = QColorDialog(current, dialog)
            _configure_color_dialog(color_picker, is_ar)
            color_picker.setWindowTitle((f"اختر اللون المشترك للوسم {name}" if is_ar else f"Choose shared color for {name}"))
            color_picker.setOption(QColorDialog.ColorDialogOption.ShowAlphaChannel, False)
            self._apply_tag_manager_dialog_theme(color_picker)
            color = color_picker.currentColor() if color_picker.exec() == QDialog.DialogCode.Accepted else QColor()
            if not color.isValid():
                return
            self._save_tag_color(None, name, color.name())
            for index in range(self.tabs.count()):
                current_tab = self.tabs.widget(index)
                if isinstance(current_tab, DocumentTab) and self._has_tag_annotations(current_tab, name):
                    current_tab._record_undo()
                    self._update_tag_annotation_records(current_tab, old_name=name, new_color=color.name())
            refresh(name)

        def remove_tag(name):
            usage = self._tag_usage_summary([name]).get(name, {"regions": 0, "documents": 0})
            delete_text = (f"هل تريد حذف الوسم '{name}' من مكتبة الوسوم المشتركة؟\n\n"
                           f"يُستخدم حاليًا في {usage.get('documents', 0)} من ملفات PDF الأخيرة أو المفتوحة. "
                           "ستُحذف مناطقه من الملفات المفتوحة الآن، ومن الملفات الأخرى عند فتحها لاحقًا.") if is_ar else (
                           f"Delete '{name}' from the shared tag library?\n\n"
                           f"It is currently used in {usage.get('documents', 0)} recent/open PDF(s). "
                           "Its assigned regions will be removed from PDFs currently open now, and from other PDFs the next time they are opened.")
            box = QMessageBox(QMessageBox.Icon.Question, "حذف الوسم من المكتبة" if is_ar else "Delete tag from library", delete_text,
                              QMessageBox.StandardButton.Yes | QMessageBox.StandardButton.No, dialog)
            self._apply_tag_manager_dialog_theme(box)
            if is_ar:
                box.button(QMessageBox.StandardButton.Yes).setText("نعم")
                box.button(QMessageBox.StandardButton.No).setText("لا")
            answer = box.exec()
            if answer != QMessageBox.StandardButton.Yes:
                return
            for index in range(self.tabs.count()):
                current_tab = self.tabs.widget(index)
                if isinstance(current_tab, DocumentTab) and self._has_tag_annotations(current_tab, name):
                    current_tab._record_undo()
                    self._update_tag_annotation_records(current_tab, old_name=name, delete=True)
                    current_tab.clear_annotation_selection()
            library = {existing: color for existing, color in self._tag_library().items()
                       if existing.casefold() != name.casefold()}
            self._save_tag_library(library)
            aliases_before_delete = self._tag_aliases()
            deleted = self._deleted_tag_names()
            deleted.add(name.casefold())
            # Keep tombstones for every legacy spelling that was renamed into this
            # tag, so those older PDF annotations cannot resurrect a deleted tag.
            for alias, target in aliases_before_delete.items():
                if self._canonical_tag_name(alias).casefold() == name.casefold() or str(target).casefold() == name.casefold():
                    deleted.add(str(alias).casefold())
            self.settings.setValue("deleted_tag_names_json", json.dumps(sorted(deleted), ensure_ascii=False))
            aliases = {alias: target for alias, target in aliases_before_delete.items()
                       if str(alias).casefold() != name.casefold() and str(target).casefold() != name.casefold()}
            self.settings.setValue("tag_aliases_json", json.dumps(aliases, ensure_ascii=False))
            for index in range(self.tabs.count()):
                current_tab = self.tabs.widget(index)
                if isinstance(current_tab, DocumentTab):
                    key = self._document_tag_key(current_tab.path)
                    if getattr(self, "_selected_region_tags", {}).get(key, "").casefold() == name.casefold():
                        self._selected_region_tags[key] = next(iter(library), "")
            self.settings.sync()
            refresh()

        def add_tag():
            prompt = QInputDialog(dialog)
            prompt.setInputMode(QInputDialog.InputMode.TextInput)
            prompt.setWindowTitle("إنشاء وسم" if is_ar else "Create a tag")
            prompt.setLabelText("اسم الوسم:" if is_ar else "Tag name:")
            prompt.setOkButtonText("إنشاء" if is_ar else "Create")
            prompt.setCancelButtonText("إلغاء" if is_ar else "Cancel")
            self._apply_tag_manager_dialog_theme(prompt)
            ok = prompt.exec() == QDialog.DialogCode.Accepted
            name = prompt.textValue()
            name = str(name or "").strip()[:32]
            if not ok or not name:
                return
            library = self._tag_library()
            if any(str(existing).casefold() == name.casefold() for existing in library):
                QMessageBox.information(dialog, "وسم موجود" if is_ar else "Existing tag", "هذا الوسم موجود بالفعل في مكتبة البرنامج." if is_ar else "This tag already exists in the program library.")
                return
            library[name] = self._tag_default_palette()[len(library) % len(self._tag_default_palette())]
            self._save_tag_library(library)
            deleted = [value for value in self._deleted_tag_names() if value != name.casefold()]
            self.settings.setValue("deleted_tag_names_json", json.dumps(deleted, ensure_ascii=False))
            aliases = {key: value for key, value in self._tag_aliases().items() if key.casefold() != name.casefold()}
            self.settings.setValue("tag_aliases_json", json.dumps(aliases, ensure_ascii=False))
            if tab is not None:
                self._selected_region_tags = getattr(self, "_selected_region_tags", {})
                self._selected_region_tags[self._document_tag_key(tab.path)] = name
            self.settings.sync()
            refresh(name)

        def apply_tag_manager_language(language=None):
            nonlocal is_ar
            is_ar = str(language or self.settings.value("interface_language", "en", type=str)).lower().startswith("ar")
            dialog.setWindowTitle("إدارة مكتبة الوسوم" if is_ar else "Manage tag library")
            title.setText("مكتبة الوسوم" if is_ar else "Tag library")
            subtitle.setText("مجموعة واحدة مشتركة لكل ملفات PDF" if is_ar else "One shared collection for all your PDFs")
            add_btn.setText("＋  وسم جديد" if is_ar else "＋  New tag")
            hint.setText("تُحفظ الوسوم داخل Engo نفسه، وليس داخل ملف PDF واحد. توضح حالتا مستخدم / غير مستخدم التعيينات الموجودة في ملفات PDF الأخيرة والمفتوحة حاليًا." if is_ar else "Tags are saved in Engo itself, not inside one PDF. Used / Unused reflects assignments found in your recent and currently open PDFs.")
            close_btn.setText("تم" if is_ar else "Done")
            direction = Qt.LayoutDirection.RightToLeft if is_ar else Qt.LayoutDirection.LeftToRight
            dialog.setLayoutDirection(direction)
            for child in dialog.findChildren(QWidget):
                try: child.setLayoutDirection(direction)
                except RuntimeError: pass
            refresh(self._selected_region_tag(tab)[0] if tab is not None else None)

        dialog._engo_apply_language = apply_tag_manager_language
        add_btn.clicked.connect(add_tag)
        dialog.setWindowTitle("إدارة مكتبة الوسوم" if is_ar else "Manage tag library")
        refresh(self._selected_region_tag(tab)[0] if tab is not None else None)
        dialog.exec()
        for index in range(self.tabs.count()):
            current = self.tabs.widget(index)
            if isinstance(current, DocumentTab):
                self._refresh_tag_menu(current)
        if tab is not None:
            self._refresh_tab_title(tab, tab.tab_title())
        self._update_controls()

    def manage_document_tags(self):
        # Compatibility alias for older menus/shortcuts.
        self.open_tag_manager()

    def save_active(self, save_as=False):
        tab = self.active_tab()
        if tab:
            companion = self.linked_supplementary_tab(tab.path) if not save_as else None
            targets = [tab] + ([companion] if companion is not None else [])
            pending = [target for target in targets if target.has_unsaved_changes() or (save_as and target is tab)]
            if not pending:
                self.show_status("No unsaved annotations")
                return
            old_primary_path = tab.path
            saved = []
            for target in pending:
                if not target.save(save_as if target is tab else False):
                    return
                saved.append(Path(target.path).name)
                self._refresh_tab_title(target, target.tab_title())
            if save_as and os.path.normcase(os.path.abspath(old_primary_path)) != os.path.normcase(os.path.abspath(tab.path)):
                old_key = os.path.normcase(os.path.abspath(old_primary_path))
                companion_path = self._linked_pdf_pairs.pop(old_key, None)
                if companion_path:
                    self._linked_pdf_pairs[os.path.normcase(os.path.abspath(tab.path))] = companion_path
                    self._refresh_linked_tab_layout()
                    self._refresh_linked_context_label()
            if len(saved) > 1:
                self.show_status("Saved both PDFs · " + " + ".join(saved))
            else:
                self.show_status(f"Saved {saved[0]}")

    def _close_other_tabs(self, keep_tab):
        if keep_tab is None or self.tabs.indexOf(keep_tab) < 0:
            return
        keep_tabs = {keep_tab}
        if isinstance(keep_tab, DocumentTab):
            primary, secondary = self._linked_pair_for_tab(keep_tab)
            if primary is not None:
                keep_tabs.add(primary)
            if secondary is not None:
                keep_tabs.add(secondary)
        for index in reversed(range(self.tabs.count())):
            candidate = self.tabs.widget(index)
            if candidate in keep_tabs:
                continue
            current_index = self.tabs.indexOf(candidate)
            if current_index >= 0:
                self.close_tab(current_index)
                # A cancelled save prompt leaves the target alive; stop rather than
                # silently removing more tabs after the user chose to cancel.
                if self.tabs.indexOf(candidate) >= 0:
                    return
        keep_index = self.tabs.indexOf(keep_tab)
        if keep_index >= 0:
            self.doc_tabbar.setCurrentIndex(keep_index)
            self.tabs.setCurrentIndex(keep_index)
            self._on_tab_changed(keep_index)
        self.show_status("Closed other tabs")

    def close_tab(self, index):
        if index < 0 or index >= self.tabs.count():
            return
        tab = self.tabs.widget(index)
        if tab is None:
            return

        primary = secondary = None
        if isinstance(tab, DocumentTab):
            primary, secondary = self._linked_pair_for_tab(tab)
        targets = [primary, secondary] if primary is not None and secondary is not None else [tab]
        targets = [item for item in targets if item is not None]

        # Ask about every modified PDF before closing either member of a pair.
        save_targets = []
        for target in targets:
            if not isinstance(target, DocumentTab) or not target.has_unsaved_changes():
                continue
            choice = QMessageBox.question(
                self, APP_NAME,
                f"Save changes to {Path(target.path).name} before closing?",
                QMessageBox.StandardButton.Save | QMessageBox.StandardButton.Discard | QMessageBox.StandardButton.Cancel,
                QMessageBox.StandardButton.Save)
            if choice == QMessageBox.StandardButton.Cancel:
                return
            if choice == QMessageBox.StandardButton.Save:
                save_targets.append(target)
        for target in save_targets:
            if not target.save(False):
                return

        is_pair = primary is not None and secondary is not None
        if is_pair:
            pair_key = os.path.normcase(os.path.abspath(primary.path))
            try:
                primary.disable_linked_view()
            except Exception:
                pass
            self._linked_pdf_pairs.pop(pair_key, None)
            closing_tabs = targets
        else:
            if isinstance(tab, DocumentTab):
                self._unlink_document_relationships(tab)
                self._refresh_linked_tab_layout()
            closing_tabs = [tab]

        # Remove in descending index order so the remaining indices stay valid.
        indexed = [(self.tabs.indexOf(item), item) for item in closing_tabs]
        indexed = [(idx, item) for idx, item in indexed if idx >= 0]
        bar_blocker = QSignalBlocker(self.doc_tabbar)
        stack_blocker = QSignalBlocker(self.tabs)
        for current_index, target in sorted(indexed, key=lambda pair: pair[0], reverse=True):
            if isinstance(target, DocumentTab):
                # A close can race with the tabbar's drag-paint timer.  Clear
                # references before close_document()/deleteLater() invalidate
                # the underlying C++ QWidget.
                try:
                    self.doc_tabbar.forget_tab(target)
                except (AttributeError, RuntimeError):
                    pass
                target.close_document()
            self.tabs.removeWidget(target)
            if target in self._tab_order:
                self._tab_order.remove(target)
            close_button = self.doc_tabbar.tabButton(current_index, QTabBar.ButtonPosition.RightSide)
            if close_button is not None:
                self.doc_tabbar.setTabButton(current_index, QTabBar.ButtonPosition.RightSide, None)
                close_button.deleteLater()
            self.doc_tabbar.removeTab(current_index)
            self._schedule_brand_title_update()
            if isinstance(target, DocumentTab):
                target.deleteLater()
        del stack_blocker
        del bar_blocker

        if self.tabs.count() > 0:
            target_index = max(0, min(self.doc_tabbar.currentIndex(), self.tabs.count() - 1))
            self.doc_tabbar.setCurrentIndex(target_index)
            self.tabs.setCurrentIndex(target_index)
            self._on_tab_changed(target_index)
        else:
            self._linked_view_target = None
            self.ai_panel.set_document("", "No PDF open")
            self.ai_panel.hide()
            self.ai_chat_btn.setChecked(False)
            self._show_files_screen()
            self._update_controls()

    def _step_tab(self, direction):
        if self.tabs.count():
            next_index = (self.tabs.currentIndex() + direction) % self.tabs.count()
            self.doc_tabbar.setCurrentIndex(next_index)
            self.tabs.setCurrentIndex(next_index)

    def _update_controls(self, *_args):
        primary_tab = self.active_tab()
        tab = self._view_target_tab()
        document_view_visible = (not hasattr(self, "document_host") or
                                 self.document_host.currentWidget() is self.tabs)
        enabled = primary_tab is not None and document_view_visible
        for widget in (self.save_btn, self.save_as_btn, self.search_btn, self.sidebar_btn, self.continuous_btn, self.book_btn,
                       self.zoom_out_btn, self.zoom_in_btn, self.fit_width_btn, self.fit_page_btn,
                       self.prev_btn, self.next_btn, self.rotate_page_btn, self.page_spin, self.theme_btn, self.present_btn,
                       self.undo_btn, self.redo_btn, self.ai_chat_btn, self.translate_btn):
            widget.setEnabled(enabled)
        self.annot_colors_btn.setEnabled(True)
        if hasattr(self, "select_tool_btn"):
            self.select_tool_btn.setEnabled(enabled)
        if hasattr(self, "tag_tool_btn"):
            self.tag_tool_btn.setEnabled(enabled)
            self._refresh_tag_menu(tab if primary_tab is not None else None)
        if hasattr(self, "link_docs_btn"):
            open_pdf_count = sum(1 for i in range(self.tabs.count()) if isinstance(self.tabs.widget(i), DocumentTab))
            self.link_docs_btn.setEnabled(open_pdf_count >= 2)
        if enabled:
            try:
                sidebar_primary, _sidebar_secondary = self._linked_pair_for_tab(tab)
                sidebar_owner = sidebar_primary if sidebar_primary is not None else tab
                self.sidebar_btn.setChecked(bool(getattr(sidebar_owner, "_sidebar_visible", True)))
            except Exception:
                self.sidebar_btn.setChecked(bool(getattr(tab, "_sidebar_visible", True)))
            self.page_spin.setRange(1, tab.page_count)
            self.page_spin.setValue(tab.current_page + 1)
            self.page_total.setText(f"/ {tab.page_count}")
            linked_active = self.linked_supplementary_tab(tab.path) is not None
            self.continuous_btn.setEnabled(True)
            self.continuous_btn.setChecked(tab.scroll_mode)
            # Page rotation is intentionally unavailable in Book spread mode.
            # Disable both the main action and its menu action together.
            rotate_allowed = not bool(tab.book_mode)
            self.rotate_page_btn.setEnabled(rotate_allowed)
            if hasattr(self, "rotate_page_menu"):
                for action in self.rotate_page_menu.actions():
                    action.setEnabled(rotate_allowed)
            self._sync_book_unlink_button(tab)
            self.zoom_label.setText({"width": "Fit width", "page": "Fit page"}.get(tab.fit_mode, f"{int(tab.custom_scale * 100)}%"))
            self.prev_btn.setEnabled(tab.current_page > 0)
            self.next_btn.setEnabled(tab.current_page < tab.page_count - (2 if tab.book_mode else 1))
            companion_for_save = self.linked_supplementary_tab(tab.path)
            pair_dirty = bool(tab.has_unsaved_changes() or (companion_for_save is not None and companion_for_save.has_unsaved_changes()))
            is_arabic_ui = str(self.settings.value("interface_language", "en", type=str) or "en").lower().startswith("ar")
            self.save_btn.setText(("حفظ *" if pair_dirty else "حفظ") if is_arabic_ui else ("Save *" if pair_dirty else "Save"))
            self.save_btn.setAccessibleName("حفظ ملف PDF · استخدم السهم لحفظ نسخة" if is_arabic_ui else "Save PDF · dropdown for Save As")
            self._update_history_controls()
            self.delete_btn.setEnabled(bool(tab.selected_annotation is not None or tab.selected_annotations or tab.selected_page_link is not None))
        else:
            self.sidebar_btn.setChecked(False)
            self._sync_book_unlink_button(None)
            self.page_spin.setRange(1, 1)
            self.page_spin.setValue(1)
            self.page_total.setText("/ 0")
            self.zoom_label.setText("—")
            is_arabic_ui = str(self.settings.value("interface_language", "en", type=str) or "en").lower().startswith("ar")
            self.save_btn.setText("حفظ" if is_arabic_ui else "Save")
            self.save_btn.setAccessibleName("حفظ ملف PDF" if is_arabic_ui else "Save PDF")
            self.prev_btn.setEnabled(False)
            self.next_btn.setEnabled(False)
            self.rotate_page_btn.setEnabled(False)
            if hasattr(self, "rotate_page_menu"):
                for action in self.rotate_page_menu.actions():
                    action.setEnabled(False)
            self.undo_btn.setEnabled(False)
            self.redo_btn.setEnabled(False)
            self.delete_btn.setEnabled(False)
        self._refresh_view_target_style()

    def _update_selection_controls(self, selected: bool):
        tab = self._view_target_tab() or self.active_tab()
        has_selection = bool(tab and (tab.selected_annotation is not None or tab.selected_annotations or tab.selected_page_link is not None))
        self.delete_btn.setEnabled(bool(selected and has_selection))
        if tab and selected:
            self.show_status("Link selected · press Delete to remove it" if tab.selected_page_link is not None
                             else "Annotation selected · press Delete to remove it, or Ctrl+Z to undo")

    def delete_selected_active(self):
        tab = self._view_target_tab() or self.active_tab()
        was_link = bool(tab is not None and tab.selected_page_link is not None)
        if tab and tab.delete_selected_annotation():
            self.show_status("Link removed · Ctrl+Z to undo" if was_link
                             else "Annotation removed · Ctrl+Z to undo")
            self._update_controls()

    def _update_history_controls(self, *_args):
        tab = self._view_target_tab() or self.active_tab()
        self.undo_btn.setEnabled(bool(tab and tab.undo_stack))
        self.redo_btn.setEnabled(bool(tab and tab.redo_stack))

    def undo_active(self):
        tab = self._view_target_tab() or self.active_tab()
        if tab:
            tab.undo()
            self.show_status("Undo")
            self._update_history_controls()

    def redo_active(self):
        tab = self._view_target_tab() or self.active_tab()
        if tab:
            tab.redo()
            self.show_status("Redo")
            self._update_history_controls()

    def _context_help_language(self):
        value = str(self.settings.value("interface_language", "en", type=str) or "en").lower()
        return "ar" if value.startswith("ar") else "en"

    def _context_help_default_text(self):
        is_ar = self._context_help_language() == "ar"
        if bool(getattr(self, "_files_screen_active", False)):
            return ("مساعد Engo: مرّر فوق أي زر لمعرفة وظيفته · اسحب ملف PDF أو صورة إلى النافذة لفتحها"
                    if is_ar else
                    "Engo helper: hover over any button to learn what it does · drop a supported document here to open it")
        live_dialog = getattr(self, "_live_tutor_dialog", None)
        try:
            if live_dialog is not None and live_dialog.isVisible():
                return ("حصة Engo AI: اضغط مطولًا على SPACE للتحدث واتركه لإرسال سؤالك · استخدم أزرار الصفحة للتنقل"
                        if is_ar else
                        "Engo AI lesson: hold SPACE to speak and release to send · use the page controls to navigate")
        except RuntimeError:
            pass
        panel = getattr(self, "ai_panel", None)
        try:
            if panel is not None and panel.isVisible():
                return ("مساعد المحادثة: اكتب سؤالك أو استخدم الميكروفون · يمكنك إرفاق صورة أو تضمين سياق PDF"
                        if is_ar else
                        "Chat helper: type a question or use the microphone · attach an image or include PDF context")
        except RuntimeError:
            pass
        if self.active_tab() is not None:
            return ("مساعد PDF: مرّر فوق أي أداة لمعرفة وظيفتها · عجلة الماوس للتمرير بين الصفحات"
                    if is_ar else
                    "PDF helper: hover over any tool to learn its function · use the mouse wheel to move through pages")
        return ("مساعد Engo: مرّر فوق أي أداة لمعرفة وظيفتها · افتح ملف PDF لبدء الدراسة"
                if is_ar else
                "Engo helper: hover over any tool to learn its function · open a PDF to start studying")

    def _set_context_help(self, text, force=False):
        label = getattr(self, "context_help_label", None)
        if label is None:
            return
        if self._context_help_suppressed and not force:
            return
        self._context_help_suppressed = False
        label.setText(str(text or ""))
        label.show()
        icon = getattr(self, "context_help_icon", None)
        if icon is not None:
            icon.setText("ⓘ" if text else "")
            icon.show()

    def _clear_context_help(self):
        """Clear the previous hover hint when the user starts another action."""
        label = getattr(self, "context_help_label", None)
        if label is not None:
            label.clear()
        icon = getattr(self, "context_help_icon", None)
        if icon is not None:
            icon.clear()

    def _set_default_context_help(self, force=False):
        if self._context_help_suppressed and not force:
            return
        self._set_context_help(self._context_help_default_text(), force=True)

    def _hide_context_help(self):
        self._context_help_suppressed = True
        label = getattr(self, "context_help_label", None)
        if label is not None:
            label.clear()
        icon = getattr(self, "context_help_icon", None)
        if icon is not None:
            icon.clear()

    def _is_chat_interaction_widget(self, watched):
        if not isinstance(watched, QWidget):
            return False
        for name in ("ai_panel", "teach_board", "_live_tutor_dialog"):
            root = getattr(self, name, None)
            if root is None:
                continue
            try:
                if watched is root or root.isAncestorOf(watched):
                    return True
            except RuntimeError:
                continue
        return False

    def _context_help_for_widget(self, widget):
        if widget is None:
            return ""
        is_ar = self._context_help_language() == "ar"
        # Purpose-written guidance for the controls used most often. These strings
        # are kept separate from tooltips so the bottom helper can be more instructive.
        pairs = {
            "new_tab_btn": ("فتح ملف PDF أو صورة في تبويب جديد.", "Open a PDF or image in a new tab."),
            "link_docs_btn": ("اربط ملفي PDF لعرضهما معًا واستخدام سياقهما في محادثة واحدة.", "Link two PDFs to view them together and use both as context in one chat."),
            "open_btn": ("افتح Home للوصول إلى الملفات الأخيرة والإعدادات والجلسة السابقة.", "Open Home to access recent files, settings, and your previous session."),
            "save_btn": ("احفظ تعديلات ملف PDF الحالي. استخدم السهم لاختيار حفظ نسخة.", "Save changes to the current PDF. Use the arrow to save a copy."),
            "search_btn": ("ابحث داخل الملف عن نص أو مفهوم أو معادلة أو شكل.", "Search the document for text, concepts, equations, or figures."),
            "sidebar_btn": ("أظهر الصور المصغرة وفهرس الصفحات للتنقل بسرعة داخل الملف.", "Show page thumbnails and the document outline for faster navigation."),
            "continuous_btn": ("فعّل التمرير المتصل لعرض الصفحات رأسيًا في مساحة واحدة.", "Enable continuous scrolling to place pages in one vertical reading area."),
            "book_btn": ("اعرض صفحتين متجاورتين مثل الكتاب. يمكن استخدامه مع التمرير.", "Show two pages side by side like a book. This can be combined with scrolling."),
            "zoom_out_btn": ("قلّل تكبير صفحة PDF.", "Zoom out on the PDF page."),
            "zoom_in_btn": ("كبّر صفحة PDF. يمكنك أيضًا استخدام Ctrl مع عجلة الماوس.", "Zoom in on the PDF page. You can also hold Ctrl while using the mouse wheel."),
            "fit_width_btn": ("اضبط التكبير لملاءمة عرض الصفحة مع المساحة المتاحة.", "Fit the page to the available width."),
            "fit_page_btn": ("اضبط التكبير لإظهار الصفحة كاملة داخل النافذة.", "Fit the complete page inside the window."),
            "prev_btn": ("انتقل إلى الصفحة السابقة.", "Go to the previous page."),
            "next_btn": ("انتقل إلى الصفحة التالية.", "Go to the next page."),
            "rotate_page_btn": ("أدر الصفحة الحالية ٩٠ درجة. استخدم القائمة لتدوير كل الصفحات.", "Rotate the current page 90 degrees. Use the menu to rotate every page."),
            "undo_btn": ("تراجع عن آخر تعديل في ملف PDF.", "Undo the last PDF edit."),
            "redo_btn": ("أعد تنفيذ التعديل الذي تراجعت عنه.", "Redo the last undone edit."),
            "delete_btn": ("احذف التعليق أو العنصر المحدد من الصفحة.", "Delete the selected annotation or item from the page."),
            "annot_colors_btn": ("اختر لون القلم والتظليل والملاحظات ومربع النص.", "Choose colors for the pen, highlights, notes, and text boxes."),
            "theme_btn": ("غيّر ألوان عرض صفحة PDF دون تعديل ألوان واجهة Engo.", "Change the PDF page viewing colors without changing Engo's interface theme."),
            "ai_chat_btn": ("افتح المحادثة النصية لطرح الأسئلة وتلخيص الملف وشرح محتواه.", "Open text chat to ask questions, summarize the PDF, and explain its contents."),
            "live_tutor_btn": ("ابدأ حصة صوتية يشرح فيها Engo محتوى الصفحة خطوة بخطوة.", "Start a live spoken lesson where Engo teaches the page step by step."),
            "translate_btn": ("حدد منطقة في الصفحة لترجمتها داخل نافذة ترجمة.", "Select an area on the page to translate it in a translation card."),
            "present_btn": ("اعرض الصفحة في وضع تقديم خالٍ من المشتتات.", "Show the page in a distraction-free presentation mode."),
            "full_btn": ("اعرض Engo بملء الشاشة. اضغط F11 للعودة.", "Use Engo in full-screen mode. Press F11 to return."),
            "toolbar_pin_btn": ("ثبّت شريط الأدوات أو اسمح له بالاختفاء تلقائيًا.", "Pin the toolbar or allow it to hide automatically."),
            "home_settings_btn": ("غيّر لغة الواجهة والثيم وحجم الخط، أو نفّذ عمليات الصيانة.", "Change the interface language, theme, and text size, or run maintenance actions."),
            "files_open_new_btn": ("اختر ملف PDF أو Word أو PowerPoint أو صورة لقراءته.", "Choose a PDF, Word, PowerPoint, or image file to read."),
            "files_restore_btn": ("استعد آخر جلسة وافتح الملفات التي كنت تعمل عليها.", "Restore your last session and reopen the files you were using."),
            "home_browser_path": ("اكتب مسار مجلد ثم اضغط Enter للانتقال إليه.", "Enter a folder path and press Enter to navigate to it."),
            "home_browser_tree": ("افتح المجلدات بالسهم بجوارها، وانقر مرتين على PDF أو صورة أو Word أو PowerPoint لفتحها.", "Expand folders with their arrows, then double-click a PDF, image, Word, or PowerPoint file to open it."),
        }
        for attr, values in pairs.items():
            try:
                if getattr(self, attr, None) is widget:
                    return values[0] if is_ar else values[1]
            except RuntimeError:
                continue

        # Annotation tools have task-specific instructions, including what to do next.
        for key, button in getattr(self, "tool_buttons", {}).items():
            if button is widget:
                tool_pairs = {
                    "select": ("أداة التحديد: انقر على تعليق لتحديده أو على رابط لفتحه. أثناء سحب مستطيل التحديد اضغط Esc لإلغائه.", "Select: click an annotation to select it or a link to open it. Press Esc to cancel a selection rectangle while dragging."),
                    "pen": ("القلم: اسحب على الصفحة للرسم أو كتابة الملاحظات. اضغط Esc لإلغاء الرسم الجاري.", "Pen: drag on the page to draw or write notes. Press Esc to cancel the stroke in progress."),
                    "highlight": ("التظليل: اسحب فوق النص أو المنطقة لتظليلها. اضغط Esc لإلغاء التحديد قبل إفلات الماوس.", "Highlight: drag over text or an area to highlight it. Press Esc to cancel before releasing the mouse."),
                    "note": ("ملاحظة: انقر على الموضع الذي تريد إضافة ملاحظة لاصقة إليه. اضغط Esc لإلغاء وضعها أثناء السحب.", "Note: click where you want to place a sticky note. Press Esc to cancel its placement while dragging."),
                    "text": ("نص: انقر على الصفحة لوضع مربع نص ثم اكتب محتواه. اضغط Esc لإلغاء السحب الجاري.", "Text: click the page to place a text box, then type. Press Esc to cancel the placement in progress."),
                    "link": ("رابط: اسحب لتحديد منطقة الرابط، ثم اختر وجهته. اضغط Esc لإلغاء تحديد المنطقة.", "Link: drag to mark the link area, then choose its destination. Press Esc to cancel the area selection."),
                    "tag": ("وسم: اسحب فوق منطقة لإسناد الوسم إليها. اضغط Esc لإلغاء التحديد قبل إفلات الماوس.", "Tag: drag over an area to assign the tag. Press Esc to cancel before releasing the mouse."),
                }
                values = tool_pairs.get(key)
                if values:
                    return values[0] if is_ar else values[1]
        if widget is getattr(self, "select_tool_btn", None):
            tab = self._view_target_tab() or self.active_tab()
            mode = str(getattr(tab, "active_tool", "select") or "select") if tab else "select"
            if is_ar:
                return "أداة اليد: اسحب الصفحة لتحريكها." if mode == "pan" else "أداة التحديد: انقر على العناصر لتحديدها. افتح السهم للتبديل إلى أداة اليد."
            return "Hand: drag the page to pan." if mode == "pan" else "Select: click items to select them. Open the arrow to switch to Hand."

        # Chat panel controls: show a concise hint in the permanent bottom helper.
        # The helper remains visible while the user clicks, types, or moves between
        # chat widgets; it is not a transient hover bubble.
        panel = getattr(self, "ai_panel", None)
        if panel is not None:
            chat_pairs = {
                "prompt_edit": ("اكتب سؤالك هنا. استخدم Shift+Enter لسطر جديد، وEnter للإرسال.", "Type your question here. Use Shift+Enter for a new line and Enter to send."),
                "provider_combo": ("اختر خدمة الذكاء الاصطناعي التي ستستقبل سؤالك.", "Choose which AI provider will receive your question."),
                "model_combo": ("اختر الموديل المستخدم في هذه المحادثة.", "Choose the model used for this conversation."),
                "include_context": ("فعّل هذا الخيار لإرسال نص الصفحة أو معاينتها مع سؤالك.", "Enable this option to include page text or a page preview with your question."),
                "send_btn": (("أوقف استجابة Engo AI الحالية." if getattr(panel, "_busy", False) else "أرسل رسالتك إلى Engo AI. أثناء التوليد يتحول الزر إلى إيقاف."), ("Stop the current Engo AI response." if getattr(panel, "_busy", False) else "Send your message to Engo AI. While generating, this button becomes Stop.")),
                "voice_btn": ("تحدث بدل الكتابة؛ ستُضاف نتيجة التعرف على الكلام إلى مربع الرسالة.", "Speak instead of typing; the transcription is inserted into the message box."),
                "read_answer_btn": ("استمع إلى أحدث إجابة من Engo AI.", "Listen to the latest Engo AI answer."),
                "stop_audio_btn": ("أوقف قراءة الإجابة الصوتية.", "Stop the spoken answer."),
                "chat_combo": ("انتقل بين المحادثات المحفوظة لهذا الملف.", "Switch between saved conversations for this PDF."),
                "new_chat_btn": ("ابدأ محادثة جديدة مرتبطة بملف PDF الحالي.", "Start a new conversation linked to the current PDF."),
                "pdf_actions_btn": ("اطلب تلخيص الملف أو مراجعة الصفحة الحالية.", "Ask Engo to summarize the PDF or review the current page."),
                "export_btn": ("صدّر المحادثة إلى Markdown أو تقرير PDF.", "Export this conversation as Markdown or a PDF report."),
                "add_region_btn": ("أرفق صورة أو الصقها من الحافظة، أو حدد منطقة من ملف PDF لإضافتها إلى سؤالك.", "Attach an image, paste one from the clipboard, or select a PDF region to add to your question."),
                "clear_attachment_btn": ("أزل كل المرفقات المحددة قبل إرسال السؤال.", "Remove all pending attachments before sending your question."),
                "remove_pending_selected_text_btn": ("أزل النص المحدد من قائمة المرفقات.", "Remove the selected passage from pending attachments."),
                "chat_search_btn": ("ابحث عن كلمة أو عبارة داخل رسائل هذه المحادثة.", "Find a word or phrase in this conversation."),
                "chat_search_prev_btn": ("انتقل إلى نتيجة البحث السابقة.", "Go to the previous search result."),
                "chat_search_next_btn": ("انتقل إلى نتيجة البحث التالية.", "Go to the next search result."),
                "chat_search_close_btn": ("أغلق البحث داخل المحادثة.", "Close conversation search."),
                "jump_bottom_btn": ("انتقل مباشرة إلى أحدث رسالة.", "Jump to the latest message."),
                "focus_mode_btn": ("وسّع مساحة المحادثة وأخفِ بقية واجهة البرنامج.", "Expand the chat and hide the rest of the application interface."),
                "close_panel_btn": ("أغلق قسم محادثة AI.", "Close the AI chat panel."),
                "pdf_actions_btn": ("لخّص ملف PDF أو اطلب مراجعة الصفحة الحالية.", "Summarize the PDF or ask for a review of the current page."),
                "prompt_edit": ("اكتب سؤالك هنا. Enter للإرسال وShift+Enter لسطر جديد.", "Type your question here. Enter sends; Shift+Enter inserts a new line."),
                "add_image_btn": ("أرفق صورة من جهازك أو الصق صورة من الحافظة داخل المحادثة.", "Attach an image from your device or paste one from the clipboard."),
                "attachment_menu_btn": ("افتح خيارات إرفاق الصور والنصوص ومناطق صفحات PDF.", "Open attachment options for images, text, and PDF page regions."),
                "document_label": ("الملف الذي يوفّر سياقًا للمحادثة الحالية.", "The document providing context to this conversation."),
                "chat_search_edit": ("اكتب كلمة أو عبارة للبحث داخل رسائل المحادثة.", "Enter a word or phrase to search within this conversation."),
                "jump_bottom_btn": ("انتقل إلى أحدث رسالة في المحادثة.", "Jump to the newest message in the conversation."),
                "clear_attachment_btn": ("أزل المرفقات المعلّقة قبل إرسال رسالتك.", "Remove pending attachments before sending your message."),
            }
            for attr, values in chat_pairs.items():
                if getattr(panel, attr, None) is widget:
                    return values[0] if is_ar else values[1]

        # Prefer a localized status tip, then a tooltip; avoid exposing long file paths.
        try:
            tip = str(widget.statusTip() or widget.toolTip() or "").strip()
        except RuntimeError:
            tip = ""
        if tip:
            return _engo_translate_tooltip(tip, "ar" if is_ar else "en")
        return ""

    def _show_selected_tool_context_help(self, tool=None):
        if self._context_help_suppressed:
            return
        tab = self._view_target_tab() or self.active_tab()
        active = str(tool or getattr(tab, "active_tool", "select") or "select")
        is_ar = self._context_help_language() == "ar"
        values = {
            "select": ("أداة التحديد جاهزة. انقر على عنصر لتحديده. أثناء سحب مستطيل التحديد اضغط Esc لإلغائه.", "Select is ready. Click an item to select it. Press Esc to cancel a selection rectangle while dragging."),
            "pan": ("أداة اليد جاهزة. اسحب الصفحة لتحريكها.", "Hand is ready. Drag the page to pan."),
            "pen": ("القلم جاهز. اسحب على الصفحة للرسم أو الكتابة. اضغط Esc لإلغاء الرسم الجاري.", "Pen is ready. Drag on the page to draw or write. Press Esc to cancel the stroke in progress."),
            "highlight": ("التظليل جاهز. اسحب فوق النص أو المنطقة لتمييزها. اضغط Esc لإلغاء التحديد قبل إفلات الماوس.", "Highlight is ready. Drag over text or an area to mark it. Press Esc to cancel before releasing the mouse."),
            "note": ("الملاحظات جاهزة. انقر لوضع ملاحظة لاصقة. اضغط Esc لإلغاء وضعها الجاري.", "Sticky notes are ready. Click to place a note. Press Esc to cancel the placement in progress."),
            "text": ("أداة النص جاهزة. انقر لوضع مربع نص. اضغط Esc لإلغاء وضعه الجاري.", "Text is ready. Click to place a text box. Press Esc to cancel the placement in progress."),
            "link": ("أداة الرابط جاهزة. اسحب لتحديد منطقة الرابط. اضغط Esc لإلغاء التحديد.", "Link is ready. Drag to mark the link area. Press Esc to cancel the selection."),
            "tag": ("أداة الوسم جاهزة. اسحب فوق المنطقة لإسناد الوسم. اضغط Esc لإلغاء التحديد.", "Tag is ready. Drag over an area to assign the tag. Press Esc to cancel the selection."),
            "translate_select": ("أداة الترجمة جاهزة. اسحب حول النص أو الكتابة اليدوية لترجمتها. اضغط Esc لإلغاء التحديد.", "Translation is ready. Drag around text or handwriting to translate it. Press Esc to cancel the selection."),
            "ai_select": ("تحديد منطقة للسؤال عنها: اسحب حول النص أو المعادلة أو الرسم لإرفاقها بسؤالك. اضغط Esc للإلغاء والعودة للماوس العادي.", "Ask AI about an area: drag around text, an equation, or a diagram to attach it to your question. Press Esc to cancel and return to the normal pointer."),
        }
        selected = values.get(active)
        self._set_context_help((selected[0] if is_ar else selected[1]) if selected else self._context_help_default_text())

    def _context_help_hover_target(self, watched):
        node = watched if isinstance(watched, QWidget) else None
        while node is not None and node is not self:
            message = self._context_help_for_widget(node)
            if message:
                return message
            try:
                node = node.parentWidget()
            except RuntimeError:
                break
        return ""

    def show_status(self, message):
        self.status.showMessage(message, 5000)

    def _toggle_sidebar(self, tab=None):
        # A linked view has one shared Library/sidebar attached to the primary
        # DocumentTab. The active target may be the supplementary PDF, but its
        # own (hidden) sidebar is not part of the visible splitter.
        target = self._view_target_tab() or tab or self.active_tab()
        if target is None:
            return
        primary, _secondary = self._linked_pair_for_tab(target)
        sidebar_owner = primary if primary is not None else target
        sidebar = sidebar_owner.sidebar
        if self._sidebar_animation:
            self._sidebar_animation.stop()
        if sidebar.maximumWidth() > 20:
            start, end = sidebar.width(), 0
            sidebar_owner._sidebar_visible = False
        else:
            sidebar.setVisible(True)
            start, end = 0, 218
            sidebar_owner._sidebar_visible = True
        self.sidebar_btn.setChecked(bool(sidebar_owner._sidebar_visible))
        anim = QPropertyAnimation(sidebar, b"maximumWidth", self)
        anim.setDuration(190)
        anim.setStartValue(start)
        anim.setEndValue(end)
        anim.setEasingCurve(QEasingCurve.Type.OutCubic)
        if end == 0:
            anim.finished.connect(lambda s=sidebar: s.setVisible(False))
        else:
            sidebar.setMaximumWidth(218)
        self._sidebar_animation = anim
        anim.start()

    def _install_fullscreen_mouse_filter(self):
        """Observe pointer movement anywhere in this window for the collapsed top edge."""
        app = QApplication.instance()
        if app is not None:
            app.installEventFilter(self)
        self.setMouseTracking(True)
        central = self.centralWidget()
        if central is not None:
            for child in central.findChildren(QWidget):
                child.setMouseTracking(True)
        if hasattr(self, "topbar"):
            self._fullscreen_toolbar_natural_height = max(54, self.topbar.sizeHint().height())

    def _is_chat_context_help_control(self, watched):
        """Return True only for chat controls that should surface help in the bottom bar."""
        panel = getattr(self, "ai_panel", None)
        if panel is None or not isinstance(watched, QWidget):
            return False
        control_names = (
            "send_btn", "voice_btn", "read_answer_btn", "stop_audio_btn",
            "provider_combo", "model_combo", "include_context", "add_region_btn",
            "chat_combo", "new_chat_btn", "pdf_actions_btn", "export_btn",
            "chat_search_btn", "chat_search_prev_btn", "chat_search_next_btn",
            "chat_search_close_btn", "chat_search_edit", "jump_bottom_btn",
            "clear_attachment_btn", "remove_pending_selected_text_btn",
            "focus_mode_btn", "close_panel_btn", "document_label", "prompt_edit",
            "add_image_btn", "add_region_btn", "attachment_menu_btn", "remove_pending_selected_text_btn",
        )
        node = watched
        while node is not None:
            if any(node is getattr(panel, name, None) for name in control_names):
                return True
            if node is panel:
                break
            try:
                node = node.parentWidget()
            except RuntimeError:
                break
        return False

    def _is_pdf_reader_space_target(self, watched) -> bool:
        """Only enable the double-Space chat shortcut while focus is in the PDF reader."""
        if (self._files_screen_active or self._presentation or self._chat_focus_mode
                or not hasattr(self, "ai_panel") or self.ai_panel.isVisible()):
            return False
        tab = self.active_tab()
        if tab is None or not isinstance(watched, QWidget):
            return False
        app = QApplication.instance()
        if app is not None and app.activeModalWidget() is not None:
            return False
        if getattr(tab, "_page_overview_active", False):
            return False
        # Space remains normal in editors, controls, lists, and buttons. The
        # shortcut works from the document surface or other passive areas of the
        # main window, even when Qt has left focus on QMainWindow itself.
        non_reader_targets = (QLineEdit, QTextEdit, QComboBox, QSpinBox, QCheckBox,
                              QAbstractItemView, QPushButton, QToolButton)
        node = watched
        while node is not None:
            if isinstance(node, non_reader_targets):
                return False
            if node is self:
                return True
            try:
                node = node.parentWidget()
            except RuntimeError:
                return False
        return False

    def _escape_cancel_active_pdf_selection(self):
        """Cancel a live pointer gesture and leave any crosshair tool on normal Select.

        Escape is a universal cancel for tools that switch the PDF pointer to a
        crosshair/plus cursor (AI region, translate, pen, highlight, note, text,
        link, tag, and future drawing tools), even before the user starts dragging.
        A plain Select marquee/text drag is cancelled without changing Select.
        """
        candidates = []
        for candidate in (self._view_target_tab(), self.active_tab()):
            if candidate is not None and candidate not in candidates:
                candidates.append(candidate)
        primary = self.active_tab()
        secondary = getattr(primary, "_linked_view_secondary", None) if primary is not None else None
        if secondary is not None and secondary not in candidates:
            candidates.append(secondary)

        for tab in candidates:
            canvas = getattr(tab, "canvas", None)
            checker = getattr(canvas, "has_active_pointer_selection", None)
            cancel = getattr(canvas, "cancel_active_pointer_selection", None)
            has_gesture = bool(callable(checker) and checker())
            active_tool = str(getattr(tab, "active_tool", "select") or "select")
            # DocumentTab maps every active tool except Select and Hand/Pan to
            # Qt.CrossCursor. Treat all such modes identically on Escape.
            crosshair_mode = active_tool not in ("", "select", "pan")

            cancelled_gesture = bool(callable(cancel) and has_gesture and cancel())
            if not cancelled_gesture and not crosshair_mode:
                continue

            if crosshair_mode:
                try:
                    tab.set_tool("select")
                except Exception:
                    try:
                        if canvas is not None:
                            canvas.setCursor(Qt.CursorShape.ArrowCursor)
                    except (RuntimeError, AttributeError):
                        pass

                # Keep the toolbar, Select/Hand split button, linked canvas, and
                # bottom helper text in sync with the reset tool.
                is_view_target = tab is (self._view_target_tab() or self.active_tab())
                if is_view_target:
                    for key, button in getattr(self, "tool_buttons", {}).items():
                        try:
                            active = key == "select"
                            button.setProperty("activeTool", active)
                            if button.isChecked() != active:
                                button.setChecked(active)
                            button.style().unpolish(button)
                            button.style().polish(button)
                            button.update()
                        except RuntimeError:
                            pass
                    try:
                        self._refresh_selector_tool_button(tab)
                        self._refresh_view_target_style()
                        self._show_selected_tool_context_help("select")
                    except Exception:
                        pass
            elif cancelled_gesture:
                # A marquee or text selection started from normal Select: keep
                # Select active, but restore its ordinary arrow cursor.
                try:
                    if canvas is not None:
                        canvas.setCursor(Qt.CursorShape.ArrowCursor)
                    self._show_selected_tool_context_help("select")
                except Exception:
                    pass
            return True
        return False

    def eventFilter(self, watched, event):
        try:
            is_our_widget = watched is self
            if isinstance(watched, QWidget) and not is_our_widget:
                node = watched
                while node is not None:
                    if node is self:
                        is_our_widget = True
                        break
                    try:
                        node = node.parentWidget()
                    except RuntimeError:
                        node = None
            if is_our_widget:
                event_type = event.type()
                if event_type in (QEvent.Type.ShortcutOverride, QEvent.Type.KeyPress):
                    try:
                        escape_key = event.key() == Qt.Key.Key_Escape
                        no_modifiers = event.modifiers() == Qt.KeyboardModifier.NoModifier
                    except (AttributeError, RuntimeError):
                        escape_key = no_modifiers = False
                    if escape_key and no_modifiers:
                        if event_type == QEvent.Type.ShortcutOverride:
                            # Mark Escape as owned by the PDF reader while a drag
                            # selection is active, instead of triggering exit_modes.
                            escape_tabs = []
                            for candidate in (self._view_target_tab(), self.active_tab(),
                                              getattr(self.active_tab(), "_linked_view_secondary", None)):
                                if candidate is not None and candidate not in escape_tabs:
                                    escape_tabs.append(candidate)
                            has_pending = any(
                                (callable(getattr(getattr(tab, "canvas", None), "has_active_pointer_selection", None))
                                 and tab.canvas.has_active_pointer_selection())
                                or str(getattr(tab, "active_tool", "select") or "select") not in ("", "select", "pan")
                                for tab in escape_tabs
                            )
                            if has_pending:
                                event.accept()
                                return True
                        elif self._escape_cancel_active_pdf_selection():
                            event.accept()
                            return True
                if event_type == QEvent.Type.KeyPress:
                    key = event.key()
                    if key == Qt.Key.Key_Space:
                        is_repeat = bool(event.isAutoRepeat())
                        if not is_repeat and self._is_pdf_reader_space_target(watched):
                            now = time.monotonic()
                            previous = float(getattr(self, "_space_double_tap_at", 0.0) or 0.0)
                            if previous and 0.0 <= now - previous <= 2.0:
                                self._space_double_tap_at = 0.0
                                event.accept()
                                self._animate_ai_panel(True)
                                return True
                            # Consume the first tap too: it is only a candidate
                            # for the double-tap gesture and must not scroll the PDF.
                            self._space_double_tap_at = now
                            event.accept()
                            return True
                        elif not is_repeat:
                            self._space_double_tap_at = 0.0
                    elif not bool(event.isAutoRepeat()):
                        self._space_double_tap_at = 0.0
                if (watched is getattr(self, "home_browser_tree", None)
                        or watched is getattr(getattr(self, "home_browser_tree", None), "viewport", lambda: None)()):
                    if event_type == QEvent.Type.Resize:
                        self._home_browser_schedule_tree_width()
                if event_type == QEvent.Type.ToolTip:
                    # Never show a floating tooltip over the pointer anywhere in
                    # Engo. Route the hint into the permanent bottom helper bar.
                    QToolTip.hideText()
                    hint = self._context_help_hover_target(watched) or self._context_help_for_widget(watched)
                    if hint:
                        self._set_context_help(hint)
                    else:
                        self._clear_context_help()
                    event.accept()
                    return True
                elif event_type == QEvent.Type.Enter:
                    # Enter is delivered even when a widget has mouseTracking
                    # disabled. Use it as the primary hover signal so the bottom
                    # helper updates immediately, without waiting for a tooltip
                    # timeout or for the user to click the control.
                    hint = self._context_help_hover_target(watched) or self._context_help_for_widget(watched)
                    if hint:
                        self._set_context_help(hint)
                elif event_type == QEvent.Type.Leave:
                    # A pointer crossing from a parent widget into one of its
                    # children should keep the relevant hint. Resolve the widget
                    # now under the cursor instead of blindly clearing on Leave.
                    try:
                        pointer_widget = QApplication.widgetAt(QCursor.pos())
                    except Exception:
                        pointer_widget = None
                    hint = self._context_help_hover_target(pointer_widget) if pointer_widget is not None else ""
                    if hint:
                        self._set_context_help(hint)
                    else:
                        self._clear_context_help()
                if event_type in (QEvent.Type.MouseButtonPress, QEvent.Type.MouseButtonDblClick):
                    # The helper is a persistent status-bar hint, not a transient
                    # hover bubble. Clicking a tool should never clear the last useful
                    # description; replace it only when the clicked control has a hint.
                    hint = self._context_help_hover_target(watched) or self._context_help_for_widget(watched)
                    if hint:
                        self._set_context_help(hint)
                elif event_type == QEvent.Type.Wheel:
                    # A page scroll is a new interaction: remove the previous control hint.
                    self._clear_context_help()
                elif event_type == QEvent.Type.KeyPress:
                    focused_name = str(getattr(watched, "objectName", lambda: "")() or "")
                    if focused_name in ("aiPrompt", "liveTutorTextInput", "teacherInstructionsEdit"):
                        self._clear_context_help()
                    else:
                        hint = self._context_help_hover_target(watched) or self._context_help_for_widget(watched)
                        if hint:
                            self._set_context_help(hint)
                elif event_type == QEvent.Type.MouseMove:
                    try:
                        no_buttons_down = event.buttons() == Qt.MouseButton.NoButton
                    except Exception:
                        no_buttons_down = True
                    if no_buttons_down:
                        try:
                            pointer_widget = QApplication.widgetAt(QCursor.pos())
                        except Exception:
                            pointer_widget = None
                        hint = self._context_help_hover_target(pointer_widget) if pointer_widget is not None else ""
                        if hint:
                            self._set_context_help(hint)
                        else:
                            # Moving over a PDF canvas, blank surface, or chat body
                            # clears the previous control hint instead of leaving stale text.
                            self._clear_context_help()
                elif event_type == QEvent.Type.FocusIn:
                    focused_name = str(getattr(watched, "objectName", lambda: "")() or "")
                    if focused_name in ("aiPrompt", "liveTutorTextInput", "teacherInstructionsEdit"):
                        hint = self._context_help_hover_target(watched) or self._context_help_for_widget(watched)
                        self._set_context_help(hint or (
                            "اكتب سؤالك هنا. Enter للإرسال وShift+Enter لسطر جديد."
                            if self._context_help_language() == "ar" else
                            "Type your question here. Enter sends; Shift+Enter inserts a new line."
                        ))
            if is_our_widget and not self._presentation and not self._toolbar_pinned:
                if event.type() == QEvent.Type.MouseMove:
                    global_pos = event.globalPosition().toPoint()
                    local_y = global_pos.y() - self.frameGeometry().top()
                    topbar_edge_y = self.topbar.mapToGlobal(QPoint(0, 0)).y()
                    near_reveal_edge = (global_pos.y() <= self.frameGeometry().top() + 9) if self._fullscreen else (abs(global_pos.y() - topbar_edge_y) <= 9)
                    if near_reveal_edge:
                        self._fullscreen_toolbar_hide_timer.stop()
                        self._show_fullscreen_toolbar()
                    elif self.topbar.isVisible():
                        top_left = self.topbar.mapToGlobal(QPoint(0, 0))
                        toolbar_rect = QRect(top_left, self.topbar.size()).adjusted(-2, -2, 2, 2)
                        if toolbar_rect.contains(global_pos):
                            self._fullscreen_toolbar_hide_timer.stop()
                        elif not self._fullscreen_toolbar_hide_timer.isActive():
                            self._fullscreen_toolbar_hide_timer.start()
                elif event.type() == QEvent.Type.Leave:
                    if self.topbar.isVisible():
                        top_left = self.topbar.mapToGlobal(QPoint(0, 0))
                        toolbar_rect = QRect(top_left, self.topbar.size()).adjusted(-2, -2, 2, 2)
                        if not toolbar_rect.contains(QCursor.pos()) and not self._fullscreen_toolbar_hide_timer.isActive():
                            self._fullscreen_toolbar_hide_timer.start()
        except (RuntimeError, AttributeError):
            pass
        return super().eventFilter(watched, event)

    def _animate_fullscreen_toolbar(self, show_toolbar: bool):
        if self._presentation:
            return
        if self._fullscreen_toolbar_animation is not None:
            self._fullscreen_toolbar_animation.stop()
        if show_toolbar:
            self.topbar.show()
            target = max(54, self.topbar.sizeHint().height(), self._fullscreen_toolbar_natural_height)
            start = max(3, self.topbar.maximumHeight())
            # maximumHeight can be Qt's large default before the first animation.
            if start > target:
                start = 3
                self.topbar.setMaximumHeight(3)
        else:
            if self._toolbar_pinned:
                return
            target = 3
            start = min(max(3, self.topbar.height()), max(54, self._fullscreen_toolbar_natural_height))
        animation = QPropertyAnimation(self.topbar, b"maximumHeight", self)
        animation.setDuration(190)
        animation.setStartValue(int(start))
        animation.setEndValue(int(target))
        animation.setEasingCurve(QEasingCurve.Type.OutCubic)
        if not show_toolbar:
            animation.finished.connect(lambda: self.topbar.setMaximumHeight(3) if not self._toolbar_pinned else None)
        self._fullscreen_toolbar_animation = animation
        animation.start()

    def _show_fullscreen_toolbar(self):
        if not self._presentation:
            self.topbar.show()
            self._animate_fullscreen_toolbar(True)

    def _hide_fullscreen_toolbar(self):
        if not self._presentation and not self._toolbar_pinned:
            self._animate_fullscreen_toolbar(False)

    def _set_fullscreen_toolbar_pinned(self, pinned: bool):
        # Backwards-compatible callback; the same pin button works in both modes.
        self._set_toolbar_pinned(pinned)

    def toggle_fullscreen(self):
        if self._chat_focus_mode:
            # Restore the regular workspace first so Full Screen can save the
            # real tab/toolbar visibility instead of the temporary chat layout.
            self.toggle_chat_focus_mode(False)
            QTimer.singleShot(300, self.toggle_fullscreen)
            return
        if not self._fullscreen:
            # Keep the exact normal geometry/state so leaving full screen does not
            # unexpectedly minimize or resize a previously windowed application.
            self._pre_fullscreen_maximized = self.isMaximized()
            self._pre_fullscreen_geometry = QRect(self.normalGeometry() if self._pre_fullscreen_maximized else self.geometry())
            self._pre_fullscreen_visibility = (
                self.tab_strip.isVisible(), self.status.isVisible(), self.topbar.isVisible()
            )
            self._fullscreen = True
            self._fullscreen_toolbar_pinned = bool(self._toolbar_pinned)
            self._fullscreen_toolbar_hide_timer.stop()
            if self._fullscreen_toolbar_animation is not None:
                self._fullscreen_toolbar_animation.stop()
            self.tab_strip.hide()
            self.status.hide()
            self.topbar.setMaximumHeight(16777215 if self._toolbar_pinned else 3)
            self.topbar.show()  # a 3px reveal strip remains at the very top edge when unpinned
            self._sync_toolbar_pin_button()
            self.showFullScreen()
            if not self._toolbar_pinned:
                self._fullscreen_toolbar_hide_timer.start()
        else:
            self._fullscreen = False
            self._fullscreen_toolbar_pinned = bool(self._toolbar_pinned)
            self._fullscreen_toolbar_hide_timer.stop()
            if self._fullscreen_toolbar_animation is not None:
                self._fullscreen_toolbar_animation.stop()
            self.topbar.setMaximumHeight(16777215 if self._toolbar_pinned else 3)
            was_tab_visible, was_status_visible, was_topbar_visible = self._pre_fullscreen_visibility or (True, True, True)
            self.tab_strip.setVisible(was_tab_visible)
            self.status.setVisible(was_status_visible)
            self.topbar.setVisible(was_topbar_visible or not self._toolbar_pinned)
            self._sync_toolbar_pin_button()
            if not self._toolbar_pinned:
                self._fullscreen_toolbar_hide_timer.start()
            self.showNormal()
            if self._pre_fullscreen_maximized:
                self.showMaximized()
            elif self._pre_fullscreen_geometry is not None:
                self.setGeometry(self._pre_fullscreen_geometry)
                self.showNormal()
            self._pre_fullscreen_geometry = None
            self._pre_fullscreen_visibility = None

    def toggle_presentation(self):
        if self._chat_focus_mode:
            self.toggle_chat_focus_mode(False)
            QTimer.singleShot(300, self.toggle_presentation)
            return
        tab = self.active_tab()
        if not tab:
            return
        self._presentation = not self._presentation
        if self._presentation:
            self._pre_present_chat_visible = bool(self.ai_panel.isVisible()) if hasattr(self, "ai_panel") else False
            self._pre_present_board_visible = bool(self.teach_board.isVisible()) if hasattr(self, "teach_board") else False
            self._pre_present_ai_checked = bool(self.ai_chat_btn.isChecked()) if hasattr(self, "ai_chat_btn") else False
            if hasattr(self, "ai_panel"):
                self.ai_panel.hide()
            if hasattr(self, "teach_board"):
                self.teach_board.hide()
            if hasattr(self, "ai_chat_btn"):
                self.ai_chat_btn.setChecked(False)
            self._pre_present_mode = (self._fullscreen, tab.book_mode, tab.scroll_mode, tab.fit_mode, tab._sidebar_visible)
            tab.set_layout_modes(book=True, scroll=False)
            tab.set_fit_mode("page")
            tab.sidebar.hide()
            self.topbar.hide()
            self.tab_strip.hide()
            self.status.hide()
            self.showFullScreen()
        else:
            self.showNormal()
            self.topbar.show()
            self.tab_strip.show()
            self.status.show()
            book_mode, scroll_mode, fit_mode, side_visible = False, True, "width", True
            if self._pre_present_mode:
                was_full, book_mode, scroll_mode, fit_mode, side_visible = self._pre_present_mode
                if was_full:
                    self.showFullScreen()
                    self.topbar.hide(); self.tab_strip.hide(); self.status.hide()
            tab.set_layout_modes(book=book_mode, scroll=scroll_mode)
            tab.set_fit_mode(fit_mode)
            tab.sidebar.setVisible(side_visible)
            tab._sidebar_visible = side_visible
            self._fullscreen = bool(self._pre_present_mode and self._pre_present_mode[0])
            if hasattr(self, "ai_panel"):
                self.ai_panel.setVisible(bool(getattr(self, "_pre_present_chat_visible", False)))
            if hasattr(self, "teach_board"):
                self.teach_board.setVisible(bool(getattr(self, "_pre_present_board_visible", False)))
            if hasattr(self, "ai_chat_btn"):
                self.ai_chat_btn.setChecked(bool(getattr(self, "_pre_present_ai_checked", False)) and bool(getattr(self, "_pre_present_chat_visible", False)))
        self._presentation = bool(self._presentation)

    def exit_modes(self):
        if self._chat_focus_mode:
            self.toggle_chat_focus_mode(False)
        elif self._presentation:
            self.toggle_presentation()
        elif self._fullscreen:
            self.toggle_fullscreen()

    def dragEnterEvent(self, event):
        mime = event.mimeData()
        if mime.hasFormat(DOCUMENT_TAB_MIME):
            event.acceptProposedAction()
        elif mime.hasUrls() and any(u.isLocalFile() and is_supported_document(u.toLocalFile()) for u in mime.urls()):
            event.acceptProposedAction()
        else:
            event.ignore()

    def dragMoveEvent(self, event):
        mime = event.mimeData()
        if mime.hasFormat(DOCUMENT_TAB_MIME) or (mime.hasUrls() and any(
                u.isLocalFile() and is_supported_document(u.toLocalFile()) for u in mime.urls())):
            event.acceptProposedAction()
        else:
            event.ignore()

    def dropEvent(self, event):
        mime = event.mimeData()
        if mime.hasFormat(DOCUMENT_TAB_MIME):
            global_pos = self.mapToGlobal(event.position().toPoint())
            bar_pos = self.doc_tabbar.mapFromGlobal(global_pos)
            target_index = self.doc_tabbar.tabAt(bar_pos) if self.doc_tabbar.rect().contains(bar_pos) else -1
            if self._receive_document_tab_drop(mime, global_pos, target_index):
                event.setDropAction(Qt.DropAction.MoveAction)
                event.accept()
            else:
                event.ignore()
            return
        paths = [u.toLocalFile() for u in mime.urls()
                 if u.isLocalFile() and is_supported_document(u.toLocalFile())]
        for path in paths:
            self.open_pdf(path)
        if paths:
            event.acceptProposedAction()
        else:
            event.ignore()

    def closeEvent(self, event):
        sidebar_save_timer = getattr(self, "_home_sidebar_save_timer", None)
        if sidebar_save_timer is not None:
            sidebar_save_timer.stop()
        self._save_home_sidebar_width()
        auto_scroll = getattr(self, "_middle_auto_scroll", None)
        if auto_scroll is not None:
            auto_scroll.stop()
        translation_workers = [w for w in getattr(self, "_translation_workers", []) if w.isRunning()]
        ai_active = self._ai_worker is not None and self._ai_worker.isRunning()
        voice_active = self._voice_input_worker is not None and self._voice_input_worker.isRunning()
        speech_active = self._speech_worker is not None and self._speech_worker.isRunning()
        live_active = self._live_tutor_worker is not None and self._live_tutor_worker.isRunning()
        search_active = _qt_thread_is_running(self._pdf_search_worker)
        if ai_active or translation_workers or voice_active or speech_active or live_active or search_active:
            if self._close_after_cancel:
                event.ignore()
                return
            choice = QMessageBox.question(
                self, APP_NAME,
                "An AI, translation, search, voice, or live tutoring task is still running. Stop it and close Engo PDF Viewer & AI Study Agent?",
                QMessageBox.StandardButton.Yes | QMessageBox.StandardButton.No,
                QMessageBox.StandardButton.Yes
            )
            if choice == QMessageBox.StandardButton.No:
                event.ignore()
                return
            self._close_after_cancel = True
            if ai_active:
                self._ai_worker.cancel()
            for worker in translation_workers:
                try:
                    worker.cancel()
                except Exception:
                    pass
            if voice_active:
                try:
                    self._voice_input_worker.cancel()
                except Exception:
                    pass
            if speech_active:
                try:
                    self._speech_worker.cancel()
                except Exception:
                    pass
            if live_active:
                try:
                    self._live_tutor_worker.cancel()
                except Exception:
                    pass
            if search_active:
                try:
                    self._pdf_search_worker.cancel()
                except Exception:
                    pass
            try:
                self.ai_panel.busy_label.setText("Stopping tasks before closing…")
                self.ai_panel.stop_btn.setEnabled(False)
            except Exception:
                pass
            self.show_status("Stopping AI, search, translation, and voice tasks; Engo will close automatically…")
            event.ignore()
            self._maybe_finish_pending_close()
            return
        self._close_after_cancel = False
        session_active_tab = self.active_tab()
        session_view_target = self._view_target_tab()
        for i in range(self.tabs.count()):
            tab = self.tabs.widget(i)
            if isinstance(tab, DocumentTab) and tab.has_unsaved_changes():
                self.doc_tabbar.setCurrentIndex(i)
                self.tabs.setCurrentIndex(i)
                choice = QMessageBox.question(self, APP_NAME,
                    f"Save changes to {Path(tab.path).name} before exiting?",
                    QMessageBox.StandardButton.Save | QMessageBox.StandardButton.Discard | QMessageBox.StandardButton.Cancel,
                    QMessageBox.StandardButton.Save)
                if choice == QMessageBox.StandardButton.Cancel:
                    event.ignore(); return
                if choice == QMessageBox.StandardButton.Save and not tab.save(False):
                    event.ignore(); return
        if session_active_tab is not None:
            active_index = self.tabs.indexOf(session_active_tab)
            if active_index >= 0:
                self.doc_tabbar.setCurrentIndex(active_index)
                self.tabs.setCurrentIndex(active_index)
        if session_view_target is not None:
            self._linked_view_target = session_view_target
        reset_shutdown = bool(getattr(self, "_reset_shutdown_requested", False))
        if not reset_shutdown:
            self._save_last_session()
        for i in range(self.tabs.count()):
            tab = self.tabs.widget(i)
            if isinstance(tab, DocumentTab):
                tab.close_document()
        try:
            self.ai_panel.chat_store.close()
        except Exception:
            pass
        event.accept()
        self._closing_complete = True
        if self in MainWindow._open_windows:
            MainWindow._open_windows.remove(self)
        if MainWindow._open_windows and not reset_shutdown:
            QTimer.singleShot(2200, MainWindow._refresh_session_after_window_close)
        # If the original single-instance window is closed while a detached
        # document window remains, hand the local IPC listener to that window.
        if self._register_ipc:
            server = getattr(self, "_ipc_server", None)
            if server is not None:
                try:
                    server.close()
                except Exception:
                    pass
            QLocalServer.removeServer(IPC_SERVER_NAME)
            self._register_ipc = False
            candidates = [window for window in MainWindow._open_windows if not window.isHidden()]
            if candidates and not reset_shutdown:
                successor = candidates[0]
                successor._register_ipc = True
                QTimer.singleShot(180, successor._setup_ipc_server)


def _startup_pdf_arguments(arguments):
    paths = []
    for arg in arguments:
        if not arg or arg.startswith("-") or arg.startswith("/") and os.name != "nt":
            continue
        candidate = os.path.abspath(arg.strip('"'))
        if is_supported_document(candidate) and os.path.isfile(candidate):
            paths.append(candidate)
    # Maintain launch order, without opening the same selected file twice.
    unique = []
    seen = set()
    for path in paths:
        key = os.path.normcase(path)
        if key not in seen:
            unique.append(path)
            seen.add(key)
    return unique


def main():
    # Do not pass a clicked PDF path to Qt's own argument parser; consume it below.
    app = QApplication([sys.argv[0]])
    app.setApplicationName(APP_DATA_NAME)
    app.setApplicationDisplayName(APP_NAME)
    app.setOrganizationName(APP_ORG)
    app.setStyle("Fusion")
    # A single app-wide filter keeps every modal popup consistent, including
    # QMessageBox/QInputDialog/QColorDialog/QFileDialog and custom QDialogs.
    _engo_dialog_filter = EngoDialogConsistencyFilter(app)
    app.installEventFilter(_engo_dialog_filter)
    app._engo_dialog_filter = _engo_dialog_filter  # retain a strong reference
    _engo_tooltip_filter = EngoTooltipTranslationFilter(app)
    app.installEventFilter(_engo_tooltip_filter)
    app._engo_tooltip_filter = _engo_tooltip_filter  # retain a strong reference
    startup_paths = _startup_pdf_arguments(sys.argv[1:])

    # Windows starts the EXE with the clicked PDF path when Engo is the default
    # PDF handler. Relay that path to an existing app instance instead of silently
    # starting an invisible duplicate process.
    client = QLocalSocket()
    client.connectToServer(IPC_SERVER_NAME)
    if client.waitForConnected(300):
        try:
            payload = json.dumps(startup_paths, ensure_ascii=False).encode("utf-8") + b"\n"
            client.write(payload)
            client.flush()
            client.waitForBytesWritten(1000)
            client.waitForReadyRead(1000)
        finally:
            client.disconnectFromServer()
        return 0

    window = MainWindow()
    if getattr(window, "_needs_first_run_setup", False):
        first_run = FirstRunSetupDialog()
        if first_run.exec() != QDialog.DialogCode.Accepted:
            window.close()
            return 0
        for key, value in first_run.values().items():
            window.settings.setValue(key, value)
        window.settings.setValue("first_run_complete", True)
        window.settings.sync()
        window._needs_first_run_setup = False
        window._apply_style()
        window._apply_user_interface_preferences()
        window._apply_interface_language()
    window.showMaximized()
    if startup_paths:
        QTimer.singleShot(120, lambda values=startup_paths: [window.open_pdf(path) for path in values])
    else:
        QTimer.singleShot(260, window._offer_restore_last_session)
    return app.exec()


if __name__ == "__main__":
    raise SystemExit(main())
