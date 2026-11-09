# Auto-split from main.py (verbatim move; do not reformat).
from __future__ import annotations

import os
import json
import io
import uuid
import sqlite3
import re
import base64
import urllib.request
import urllib.error
import urllib.parse
import socket
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

from engo_base import (
    _engo_translate_tooltip,
    engo_ui_theme_tokens,
    is_office_document,
    normalize_ui_theme,
    resource_path,
)
from engo_widgets import (
    _set_compact_dialog_button_heights,
)



AI_PROVIDER_LABELS = {
    "openai": "Chat GPT",
    "claude": "Claude",
    "gemini": "Google Gemini",
    "deepseek": "DeepSeek",
}
AI_DEFAULT_MODELS = {
    "openai": "gpt-4.1",
    "claude": "claude-sonnet-4-5",
    "gemini": "gemini-3.8-flash",
    "deepseek": "deepseek-chat",
}
# Translation is a latency-sensitive task, so it uses a dedicated Gemini Flash-Lite
# model by default instead of inheriting a possibly slower reasoning/chat model.
AI_TRANSLATION_DEFAULT_MODEL = "gemini-3.5-flash-lite"
# Chat model IDs are discovered from each provider API and cached per account.

AI_SYSTEM_PROMPT = (
    "You are Engo AI, an accurate study assistant inside a PDF reader. Use the supplied PDF context "
    "and selected page images as primary evidence. A selected crop/image is an additional clue, not a restriction: "
    "when full PDF context is enabled, use all supplied document text and linked companion-document context to answer "
    "cross-page and cross-file questions. Answer in the user's language, usually Arabic if they "
    "write Arabic. For math/engineering problems, explain steps and units. If a scan or handwriting is "
    "unclear, say what cannot be read instead of inventing it. Distinguish facts visible in the supplied "
    "pages from assumptions. Do not claim to have read pages that were not supplied.\n\n"
    "FORMATTING REQUIREMENTS: Write every normal chat answer in clean GitHub-Flavored Markdown. "
    "Use ##/### headings when useful, ordered or unordered lists for steps, **bold** for important "
    "terms and results, *italics* sparingly, Markdown tables for real comparisons or structured values, "
    "blockquote syntax for quotations, and fenced code blocks only for actual code. Do not wrap the "
    "whole answer in a code fence and do not emit raw HTML. Keep paragraphs readable and avoid excessive "
    "formatting.\n\n"
    "MATHEMATICS: Write inline formulas with $...$ and important standalone formulas on their own lines "
    "inside $$...$$. Use standard LaTeX notation for fractions (\\frac), roots (\\sqrt), Greek "
    "letters, units, subscripts (P_{v1}) and superscripts (x^2). Use \\dfrac or \\frac for stacked "
    "fractions, \\sqrt[n]{...} for indexed roots, braces around multi-character exponents and indices, "
    "\\begin{aligned} for aligned multi-step derivations, \\begin{cases} for piecewise definitions, "
    "and pmatrix/bmatrix/matrix for matrices when appropriate. Keep every equation intact and on its "
    "own line when it is a calculation. Explain the substitution and final result in ordinary prose; "
    "bold the final answer. Never put a formula inside a code block. In Arabic answers, keep the prose "
    "Arabic and let the formula itself remain left-to-right. Do not replace a real formula with a vague "
    "text description."
)


AI_KEY_URLS = {
    "openai": "https://platform.openai.com/api-keys",
    "claude": "https://platform.claude.com/settings/keys",
    "gemini": "https://aistudio.google.com/app/apikey",
    "deepseek": "https://platform.deepseek.com/api_keys",
}


# Provider API key storage.
# Windows Credential Manager via the `keyring` package is preferred. A QSettings
# fallback preserves usability on systems where no credential backend is available.
# The fallback is not encrypted, so the settings dialog warns the user when used.
def _provider_key_service() -> str:
    return "EngoPDFViewer.AIProviders"


def _get_provider_key(settings: QSettings, provider: str) -> str:
    provider = str(provider or "").strip().lower()
    if provider not in AI_PROVIDER_LABELS:
        return ""
    try:
        import keyring  # type: ignore
        value = keyring.get_password(_provider_key_service(), provider)
        if value:
            return str(value).strip()
    except Exception:
        # Missing/locked keyring is handled by the local settings fallback.
        pass
    try:
        value = settings.value(f"ai_key_{provider}", "", type=str)
        return str(value or "").strip()
    except Exception:
        return ""


def _save_provider_key(settings: QSettings, provider: str, key: str) -> bool:
    """Save a provider key; return True only when keyring storage succeeded.

    Empty strings clear both the preferred keyring entry and the fallback setting.
    """
    provider = str(provider or "").strip().lower()
    if provider not in AI_PROVIDER_LABELS:
        return False
    key = str(key or "").strip()
    service = _provider_key_service()

    try:
        import keyring  # type: ignore
        if key:
            keyring.set_password(service, provider, key)
            # Verify the backend accepted the value before deleting any fallback.
            if keyring.get_password(service, provider) != key:
                raise RuntimeError("Credential store did not verify the saved key")
        else:
            try:
                existing = keyring.get_password(service, provider)
                if existing:
                    keyring.delete_password(service, provider)
            except Exception:
                # A missing credential is already the desired state.
                pass
        settings.remove(f"ai_key_{provider}")
        settings.sync()
        return True
    except Exception:
        # Best effort to avoid an old keyring value shadowing the fallback key.
        try:
            import keyring  # type: ignore
            if key:
                old = keyring.get_password(service, provider)
                if old and old != key:
                    try:
                        keyring.delete_password(service, provider)
                    except Exception:
                        pass
            else:
                old = keyring.get_password(service, provider)
                if old:
                    try:
                        keyring.delete_password(service, provider)
                    except Exception:
                        pass
        except Exception:
            pass
        try:
            if key:
                settings.setValue(f"ai_key_{provider}", key)
            else:
                settings.remove(f"ai_key_{provider}")
            settings.sync()
        except Exception:
            pass
        return False


class GeminiTranslateWorker(QThread):
    """Translate a selected PDF crop with Google Gemini; never save translation/transcription results."""
    succeeded = pyqtSignal(str)
    failed = pyqtSignal(str)
    progress = pyqtSignal(str)
    streamed = pyqtSignal(str)
    cancelled = pyqtSignal()

    def __init__(self, pdf_path: str, page_index: int, clip_rect, image_bytes: bytes,
                 target_code: str, source_code: str = "auto", model: str = "", api_key: str = "",
                 selected_text: str | None = None):
        super().__init__()
        self.pdf_path = os.path.abspath(pdf_path)
        self.page_index = int(page_index)
        self.clip_rect = tuple(clip_rect) if clip_rect else None
        self.image_bytes = bytes(image_bytes or b"")
        self.target_code = str(target_code or "ar")
        self.source_code = str(source_code or "auto")
        self.model = str(model or AI_DEFAULT_MODELS.get("gemini", ""))
        self.api_key = str(api_key or "")
        # None means legacy caller / fallback to the file on disk. An empty string
        # means this precise in-memory selection contains no selectable text, so
        # translate its matching image instead of reading stale disk coordinates.
        self.selected_text = None if selected_text is None else str(selected_text)
        self._cancel_event = threading.Event()
        self._response_lock = threading.Lock()
        self._active_response = None

    def cancel(self):
        self._cancel_event.set()
        with self._response_lock:
            response = self._active_response
        if response is not None:
            try:
                response.close()
            except Exception:
                pass

    def _check_cancelled(self):
        if self._cancel_event.is_set():
            raise InterruptedError("Translation cancelled.")

    def _extract_selectable_text(self) -> str:
        if self.selected_text is not None:
            return self.selected_text.strip()
        try:
            with fitz.open(self.pdf_path) as doc:
                if not 0 <= self.page_index < doc.page_count:
                    return ""
                page = doc.load_page(self.page_index)
                if self.clip_rect and len(self.clip_rect) == 4:
                    return str(page.get_text("text", clip=fitz.Rect(*self.clip_rect)) or "").strip()
                return str(page.get_text("text") or "").strip()
        except Exception as exc:
            raise RuntimeError(f"Could not read the selected PDF area: {exc}")

    @staticmethod
    def _language_name(code: str) -> str:
        names = {"ar": "Arabic", "en": "English", "ru": "Russian", "fr": "French",
                 "de": "German", "es": "Spanish", "tr": "Turkish", "zh-CN": "Simplified Chinese",
                 "ja": "Japanese"}
        return names.get(code, code or "the target language")

    # Translation requests can take longer than short chat prompts, especially when
    # Gemini must read handwriting from a scanned PDF crop. These are inactivity
    # timeouts (not total request deadlines), so streaming can continue indefinitely
    # as long as the service keeps sending data.
    CONNECT_TIMEOUT_SECONDS = 20
    TEXT_READ_TIMEOUT_SECONDS = 100
    IMAGE_READ_TIMEOUT_SECONDS = 150
    MAX_TRANSLATION_IMAGE_SIDE = 1400

    def _prepare_translation_image(self) -> bytes:
        """Normalize and downsize the selected crop before uploading it to Gemini."""
        raw = bytes(self.image_bytes or b"")
        if not raw:
            return raw
        try:
            with Image.open(io.BytesIO(raw)) as source:
                image = ImageOps.exif_transpose(source).convert("RGB")
                image.thumbnail(
                    (self.MAX_TRANSLATION_IMAGE_SIDE, self.MAX_TRANSLATION_IMAGE_SIDE),
                    Image.Resampling.LANCZOS,
                )
                output = io.BytesIO()
                image.save(output, format="JPEG", quality=86, optimize=True, progressive=True)
                optimized = output.getvalue()
                # Always return the normalized JPEG: input bytes may come from a
                # future image source with a different encoding or larger dimensions.
                return optimized
        except Exception:
            # The selection renderer normally supplies a valid image. If an unusual
            # image codec fails, preserve the original bytes rather than losing it.
            return raw

    def _gemini_request(self, prompt: str, include_image: bool) -> str:
        self._check_cancelled()
        if not self.api_key:
            raise RuntimeError(
                "The translation service is not configured. Open AI Settings and add the translation service key, then retry."
            )
        request_worker = AIRequestWorker(
            self.pdf_path, "gemini", self.model, self.api_key, prompt, [], False, [], "custom", self.page_index
        )
        request_worker._cancel_event = self._cancel_event
        request_worker._response_lock = self._response_lock
        request_worker._set_active_response = self._set_response
        request_worker._clear_active_response = self._clear_response
        request_worker.temperature = 0.0
        # Translation is a focused, single-turn task. Start showing the answer as soon
        # as Gemini emits its first token, rather than buffering the full response.
        request_worker.CONNECT_TIMEOUT_SECONDS = self.CONNECT_TIMEOUT_SECONDS
        request_worker.READ_TIMEOUT_SECONDS = (
            self.IMAGE_READ_TIMEOUT_SECONDS if include_image else self.TEXT_READ_TIMEOUT_SECONDS
        )
        request_worker.max_output_tokens = 2048
        stream_state = {"received": False}
        def _forward_translation_delta(_path, delta):
            value = str(delta or "")
            if value:
                stream_state["received"] = True
                self.streamed.emit(value)
        request_worker.streamed.connect(_forward_translation_delta)
        request_worker.progress.connect(lambda _path, message: self.progress.emit(str(message or "")))
        request_worker.system_prompt = (
            "You are a literal translation engine, not an editor. Translate only the words that are actually present. "
            "Do not improve grammar, polish style, correct content, add missing words, infer unstated meaning, summarize, "
            "explain, answer, or add a heading. Preserve the author's wording, order, numbers, labels, punctuation, and "
            "line structure where the target language permits. Output only the translated text. Never include the source text."
        )
        images = []
        if include_image:
            prepared_image = self._prepare_translation_image()
            images = [{"label": "Selected PDF crop: translate only visible writing", "mime": "image/jpeg", "data": prepared_image}]
        result = ""
        # A read timeout before the first token is safe to retry once. Never replay
        # after streaming has begun, because that would duplicate translated text.
        for attempt in range(2):
            self._check_cancelled()
            try:
                result = str(request_worker._call_provider(prompt, images, stream=True) or "").strip()
                break
            except Exception as exc:
                message = str(exc)
                lowered = message.lower()
                transient = any(token in lowered for token in (
                    "winerror 10054", "connection reset", "forcibly closed", "connection aborted",
                    "timed out", "timeout", "read timeout", "socket.timeout",
                    "temporarily unavailable", "http 429", "http 500", "http 502", "http 503", "http 504"
                ))
                if not transient or stream_state["received"] or attempt >= 1 or self._cancel_event.is_set():
                    if "http 402" in lowered or "insufficient balance" in lowered:
                        raise RuntimeError(
                            message + "\n\nThe translation service reports insufficient balance or billing access. "
                            "Check the API project's billing/quota or update the translation service key."
                        )
                    if "winerror 10054" in lowered or "forcibly closed" in lowered or "connection reset" in lowered:
                        raise RuntimeError(
                            message + "\n\nThe connection was reset by the server or network. Check internet/firewall, "
                            "then retry. Engo does not save the translation or transcription."
                        )
                    raise
                if "read timeout" in lowered or "timed out" in lowered or "timeout" in lowered:
                    self.progress.emit(f"Translation service is responding slowly; retrying once ({attempt + 1}/2)…")
                else:
                    self.progress.emit(f"Connection interrupted; retrying ({attempt + 1}/2)…")
                if self._cancel_event.wait(1.0 + 0.5 * attempt):
                    self._check_cancelled()
        self._check_cancelled()
        result = re.sub(r"^```(?:text|txt|markdown)?\s*|\s*```$", "", result, flags=re.I).strip()
        # The UI intentionally displays only the provider's translated output; no text is persisted.
        return result

    def _set_response(self, response):
        with self._response_lock:
            self._active_response = response
        if self._cancel_event.is_set():
            try:
                response.close()
            except Exception:
                pass
            self._check_cancelled()

    def _clear_response(self, response):
        with self._response_lock:
            if self._active_response is response:
                self._active_response = None

    @staticmethod
    def _split_long_translation_text(text: str, max_chars: int = 6500) -> list[str]:
        """Split long selectable PDF text near line/word boundaries without dropping bytes."""
        value = str(text or "")
        if len(value) <= max_chars:
            return [value] if value else []
        chunks = []
        start = 0
        while start < len(value):
            end = min(len(value), start + max_chars)
            if end < len(value):
                search_start = start + int(max_chars * 0.60)
                boundary = max(value.rfind("\n", search_start, end), value.rfind(" ", search_start, end))
                if boundary > start:
                    end = boundary + 1
            chunks.append(value[start:end])
            start = end
        return chunks

    def run(self):
        try:
            self._check_cancelled()
            text = self._extract_selectable_text()
            target = self._language_name(self.target_code)
            if len(text.strip()) >= 2:
                source_hint = "Detect the source language automatically" if self.source_code == "auto" else f"The source language is {self._language_name(self.source_code)}"
                text_chunks = self._split_long_translation_text(text)
                translated_parts = []
                for chunk_index, text_chunk in enumerate(text_chunks, start=1):
                    self._check_cancelled()
                    if len(text_chunks) > 1:
                        self.progress.emit(f"Translating text part {chunk_index} of {len(text_chunks)}…")
                    else:
                        self.progress.emit("Translating selected text…")
                    prompt = (
                        f"Translate the source text below into {target}. {source_hint}. Translate literally and faithfully. "
                        "Do not correct, enhance, rewrite, explain, summarize, or add any content. Keep names, numbers, equations, "
                        "and line order. Return the translation only, without a heading or quotation marks.\n\n"
                        "SOURCE TEXT — translate exactly what is written:\n" + text_chunk
                    )
                    translated_part = self._gemini_request(prompt, include_image=False)
                    translated_parts.append(translated_part)
                    if chunk_index < len(text_chunks):
                        # Keep a visual paragraph boundary between independently
                        # translated pieces instead of joining the last/first words.
                        self.streamed.emit("\n")
                translated = "\n".join(translated_parts).strip()
            else:
                if len(self.image_bytes) < 100:
                    raise RuntimeError("The selected area is empty. Select the handwritten text again.")
                source_hint = "Detect the source language from the image" if self.source_code == "auto" else f"The writing is expected to be in {self._language_name(self.source_code)}"
                prompt = (
                    f"Read the handwriting visibly present in the attached crop and translate it into {target}. {source_hint}. "
                    "First read the visible words internally, then output only their direct translation. Translate only what is visibly written. "
                    "Do not improve, correct, complete, explain, summarize, infer omitted words, or add context. Keep the original order, "
                    "numbers, symbols, labels, and line breaks as closely as the target language allows. If a word is unreadable, put "
                    "[unreadable] exactly in that place. If absolutely no writing can be read, output exactly [TEXT_UNREADABLE]. "
                    "Return the translated result only. Do not include the source transcription, notes, or a heading."
                )
                self.progress.emit("Reading handwriting and translating…")
                translated = self._gemini_request(prompt, include_image=True)
                if translated.strip() == "[TEXT_UNREADABLE]":
                    raise RuntimeError(
                        "The handwriting could not be read clearly. Select a larger, sharper area and try again. "
                        "No transcription or translation was saved."
                    )
            self._check_cancelled()
            if not translated.strip():
                raise RuntimeError("The translation service returned no text. Try selecting the text again.")
            self.succeeded.emit(translated.strip())
        except InterruptedError:
            self.cancelled.emit()
        except Exception as exc:
            self.failed.emit(str(exc))


class TranslationCardDialog(QDialog):
    """Minimal popup whose visible content is only the translated text."""
    translateRequested = pyqtSignal(str)

    @staticmethod
    def localized_text(key: str, language: str = "en", **values) -> str:
        """Return translation UI text in the application's interface language."""
        lang = "ar" if str(language or "en").strip().lower().startswith("ar") else "en"
        messages = {
            "text_loading": {
                "ar": "جارٍ ترجمة النص المحدد",
                "en": "Translating selected text",
            },
            "region_loading": {
                "ar": "جاري المعالجة والترجمة",
                "en": "Processing and translating",
            },
            "text_status": {
                "ar": "جارٍ ترجمة النص المحدد من {source} إلى {target}…",
                "en": "Translating selected text from {source} to {target}…",
            },
            "region_status": {
                "ar": "جاري المعالجة والترجمة للمنطقة المحددة من {source} إلى {target}…",
                "en": "Processing and translating the selected region from {source} to {target}…",
            },
            "text_part": {
                "ar": "جارٍ ترجمة الجزء {current} من {total}",
                "en": "Translating part {current} of {total}",
            },
            "connection_retry": {
                "ar": "انقطع الاتصال؛ جارٍ إعادة المحاولة",
                "en": "Connection interrupted; retrying",
            },
        }
        template = messages.get(str(key), {}).get(lang)
        if template is None:
            template = messages.get(str(key), {}).get("en", str(key))
        try:
            return template.format(**values)
        except (KeyError, ValueError):
            return template

    def __init__(self, image_bytes: bytes, page_index: int, default_target: str = "ar", parent=None, font_pt: float = 13.0):
        super().__init__(parent)
        self._font_pt = max(8.0, min(28.0, float(font_pt or 13.0)))
        self.image_bytes = bytes(image_bytes or b"")
        self.page_index = int(page_index)
        self.setWindowTitle("Translation")
        self.setObjectName("translationCard")
        self.setMinimumSize(320, 130)
        self.resize(510, 270)
        self.setWindowModality(Qt.WindowModality.NonModal)
        self.setAttribute(Qt.WidgetAttribute.WA_DeleteOnClose, True)
        root = QVBoxLayout(self)
        root.setContentsMargins(14, 12, 14, 12)
        root.setSpacing(6)
        self.loading_label = QLabel("Preparing translation")
        self.loading_label.setObjectName("translationLoading")
        self.loading_label.hide()
        root.addWidget(self.loading_label)
        self._loading_phase = 0
        self._loading_message = "Translating selected area"
        self._loading_timer = QTimer(self)
        self._loading_timer.setInterval(380)
        self._loading_timer.timeout.connect(self._animate_translation_loading)
        self.result_view = QTextBrowser()
        self.result_view.setObjectName("translationResult")
        translation_font = self.result_view.font()
        translation_font.setPointSizeF(self._font_pt)
        self.result_view.setFont(translation_font)
        self.result_view.setOpenExternalLinks(False)
        self.result_view.setPlaceholderText("")
        self.result_view.setContextMenuPolicy(Qt.ContextMenuPolicy.DefaultContextMenu)
        self.result_view.clear()
        root.addWidget(self.result_view, 1)
        self._streamed_text = ""
        self._translation_language = "en"
        self.apply_context_from_parent()

    def _translation_parent_setting(self, key, default):
        try:
            owner = self.parent()
            settings = getattr(owner, "settings", None)
            if settings is not None:
                return settings.value(key, default, type=str)
        except Exception:
            pass
        return default

    def apply_context_from_parent(self):
        self.apply_language(self._translation_parent_setting("interface_language", "en"))
        self.apply_theme(self._translation_parent_setting("ui_theme", "dark"))

    def _default_loading_message(self):
        key = "text_loading" if self.selection_kind == "text" else "region_loading"
        return self.localized_text(key, self._translation_language)

    def apply_language(self, language=None):
        self._translation_language = "ar" if str(language or "en").lower().startswith("ar") else "en"
        is_ar = self._translation_language == "ar"
        self.setLayoutDirection(Qt.LayoutDirection.RightToLeft if is_ar else Qt.LayoutDirection.LeftToRight)
        self.setWindowTitle("ترجمة" if is_ar else "Translation")
        if not self._loading_timer.isActive() and not self._streamed_text and self.loading_label.isVisible():
            self._loading_message = "جارٍ ترجمة المنطقة المحددة" if is_ar else "Translating selected area"
        elif not self._streamed_text and self.loading_label.isVisible():
            self._loading_message = "جارٍ ترجمة المنطقة المحددة" if is_ar else "Translating selected area"

    def apply_theme(self, theme=None):
        tokens = engo_ui_theme_tokens(theme or self._translation_parent_setting("ui_theme", "dark"))
        c = {
            "bg": tokens["window"], "panel": tokens["panel"], "text": tokens["text"],
            "muted": tokens["muted"], "border": tokens["border"],
            "accent": tokens["accent"], "selection": tokens["selection"],
            "selection_text": tokens["selection_text"],
        }
        palette = QPalette(self.palette())
        for role, key in ((QPalette.ColorRole.Window,"bg"), (QPalette.ColorRole.WindowText,"text"),
                          (QPalette.ColorRole.Base,"panel"), (QPalette.ColorRole.AlternateBase,"bg"),
                          (QPalette.ColorRole.Text,"text"), (QPalette.ColorRole.Button,"panel"),
                          (QPalette.ColorRole.ButtonText,"text"), (QPalette.ColorRole.Highlight,"selection"),
                          (QPalette.ColorRole.HighlightedText,"selection_text"),
                          (QPalette.ColorRole.ToolTipBase,"panel"), (QPalette.ColorRole.ToolTipText,"text")):
            palette.setColor(role, QColor(c[key]))
        self.setPalette(palette)
        self.setStyleSheet(f"""
            QDialog#translationCard {{ background:{c['bg']}; color:{c['text']}; }}
            QDialog#translationCard QLabel#translationLoading {{ color:{c['accent']}; background:transparent; font-weight:650; }}
            QDialog#translationCard QTextBrowser#translationResult {{ background:{c['panel']}; color:{c['text']}; border:1px solid {c['border']}; border-radius:8px; padding:8px; selection-background-color:{c['selection']}; selection-color:{c['selection_text']}; }}
            QDialog#translationCard QToolTip {{ background:{c['panel']}; color:{c['text']}; border:1px solid {c['border']}; padding:5px; }}
        """)

    def set_font_size(self, font_pt: float):
        self._font_pt = max(8.0, min(28.0, float(font_pt or 13.0)))
        font = self.result_view.font()
        font.setPointSizeF(self._font_pt)
        self.result_view.setFont(font)

    def begin_translation(self, language_label: str = ""):
        self._streamed_text = ""
        self.result_view.clear()
        self._loading_message = "جارٍ ترجمة المنطقة المحددة" if self._translation_language == "ar" else "Translating selected area"
        self._loading_phase = 0
        self.loading_label.show()
        self._loading_timer.start()
        self._animate_translation_loading()

    def _animate_translation_loading(self):
        dots = "." * (self._loading_phase % 4)
        self._loading_phase += 1
        self.loading_label.setText(f"{self._loading_message}{dots}")

    def _stop_translation_loading(self):
        self._loading_timer.stop()
        self.loading_label.hide()

    def append_delta(self, delta: str):
        if not self._streamed_text:
            self._stop_translation_loading()
        value = str(delta)
        self._streamed_text += value
        cursor = self.result_view.textCursor()
        cursor.movePosition(QTextCursor.MoveOperation.End)
        cursor.insertText(value)
        self.result_view.setTextCursor(cursor)

    @staticmethod
    def _provider_neutral_message(message: str) -> str:
        """Keep implementation/provider names out of the user-facing translation card."""
        value = str(message or "").strip()
        if not value:
            return "Translation failed. Please try again."
        # Replace vendor names and provider-specific setup wording while preserving
        # actionable information such as billing, connectivity, or retry guidance.
        value = re.sub(
            r"(?i)\s*translation uses (?:google\s+)?gemini directly;\s*it does not use the chat\s*gpt or deepseek key\.?",
            "", value,
        )
        substitutions = (
            (r"(?i)google\s+gemini\s+api\s+key", "translation service key"),
            (r"(?i)gemini\s+api\s+key", "translation service key"),
            (r"(?i)google\s+gemini\s+api", "translation service"),
            (r"(?i)google\s+gemini", "translation service"),
            (r"(?i)gemini", "translation service"),
            (r"(?i)chat\s*gpt\s*/?\s*or\s*deepseek[^.]*\.", ""),
        )
        for pattern, replacement in substitutions:
            value = re.sub(pattern, replacement, value)
        value = re.sub(r"[ \t]{2,}", " ", value)
        value = re.sub(r"\n{3,}", "\n\n", value).strip()
        return value or "Translation failed. Please try again."

    def set_progress(self, message: str):
        value = self._provider_neutral_message(message or "Translating selected area")
        # Provider-specific retry text is intentionally generalized in this popup.
        if "connection interrupted" in value.lower():
            value = "انقطع الاتصال؛ جارٍ إعادة المحاولة" if self._translation_language == "ar" else "Connection interrupted; retrying"
        elif self._translation_language == "ar" and value == "Translating selected area":
            value = "جارٍ ترجمة المنطقة المحددة"
        self._loading_message = value.rstrip(".· ")
        if not self._loading_timer.isActive():
            self.loading_label.show()
            self._loading_timer.start()

    def show_result(self, text: str):
        self._stop_translation_loading()
        self._streamed_text = str(text or "")
        self.result_view.setPlainText(self._streamed_text or ("لم يتم إرجاع ترجمة." if self._translation_language == "ar" else "No translation returned."))
        self.result_view.moveCursor(QTextCursor.MoveOperation.Start)

    def show_error(self, error: str):
        self._stop_translation_loading()
        message = self._provider_neutral_message(error or "Translation failed.")
        partial = str(self._streamed_text or "").strip()
        if partial:
            notice = (
                "\n\n[الترجمة غير مكتملة بسبب انقطاع الاتصال. احتفظنا بالجزء الذي وصل.]"
                if self._translation_language == "ar" else
                "\n\n[Translation is incomplete because the connection was interrupted. The received text was preserved.]"
            )
            self.result_view.setPlainText(partial + notice)
            self.result_view.moveCursor(QTextCursor.MoveOperation.Start)
            # Keep only translated content in the clipboard action; never copy the warning.
            self._streamed_text = partial
            return
        lowered = message.casefold()
        if "read timeout" in lowered or "did not send data before" in lowered:
            message = (
                "خدمة الترجمة استغرقت وقتًا أطول من المعتاد حتى بعد إعادة المحاولة. جرّب تحديد مساحة أصغر أو أوضح، أو أعد المحاولة بعد قليل."
                if self._translation_language == "ar" else
                "The translation service took longer than usual, even after retrying. Select a smaller or clearer area, or try again shortly."
            )
        self._streamed_text = ""
        self.result_view.setPlainText(message)

    def copy_result(self):
        if self._streamed_text:
            QApplication.clipboard().setText(self._streamed_text)

class AIChatStore:
    """Persistent local chat database with support for multiple image attachments per message."""
    def __init__(self):
        root = QStandardPaths.writableLocation(QStandardPaths.StandardLocation.AppDataLocation)
        if not root:
            root = str(Path.home() / ".engo_pdf_viewer")
        self.root = Path(root)
        self.root.mkdir(parents=True, exist_ok=True)
        self.db_path = self.root / "ai_chats.sqlite3"
        self.connection = sqlite3.connect(str(self.db_path))
        self.connection.row_factory = sqlite3.Row
        self.connection.execute("PRAGMA foreign_keys = ON")
        self.connection.execute("""CREATE TABLE IF NOT EXISTS chats (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            pdf_path TEXT NOT NULL,
            title TEXT NOT NULL DEFAULT 'New conversation',
            created_at TEXT NOT NULL DEFAULT CURRENT_TIMESTAMP,
            updated_at TEXT NOT NULL DEFAULT CURRENT_TIMESTAMP,
            conversation_number INTEGER NOT NULL DEFAULT 0
        )""")
        self.connection.execute("""CREATE TABLE IF NOT EXISTS messages (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            chat_id INTEGER NOT NULL,
            role TEXT NOT NULL,
            content TEXT NOT NULL,
            created_at TEXT NOT NULL DEFAULT CURRENT_TIMESTAMP,
            attachment_path TEXT,
            page_index INTEGER,
            attachments_json TEXT NOT NULL DEFAULT '[]',
            FOREIGN KEY(chat_id) REFERENCES chats(id) ON DELETE CASCADE
        )""")
        message_columns = {row[1] for row in self.connection.execute("PRAGMA table_info(messages)").fetchall()}
        if "attachment_path" not in message_columns:
            self.connection.execute("ALTER TABLE messages ADD COLUMN attachment_path TEXT")
        if "page_index" not in message_columns:
            self.connection.execute("ALTER TABLE messages ADD COLUMN page_index INTEGER")
        if "attachments_json" not in message_columns:
            self.connection.execute("ALTER TABLE messages ADD COLUMN attachments_json TEXT NOT NULL DEFAULT '[]'")
        if "selected_text_context" not in message_columns:
            self.connection.execute("ALTER TABLE messages ADD COLUMN selected_text_context TEXT NOT NULL DEFAULT ''")
        if "selected_text_source_role" not in message_columns:
            self.connection.execute("ALTER TABLE messages ADD COLUMN selected_text_source_role TEXT NOT NULL DEFAULT 'assistant'")
        if "selected_text_location_json" not in message_columns:
            self.connection.execute("ALTER TABLE messages ADD COLUMN selected_text_location_json TEXT NOT NULL DEFAULT ''")
        chat_columns = {row[1] for row in self.connection.execute("PRAGMA table_info(chats)").fetchall()}
        if "conversation_number" not in chat_columns:
            self.connection.execute("ALTER TABLE chats ADD COLUMN conversation_number INTEGER NOT NULL DEFAULT 0")

        # Give every saved chat a stable per-PDF sequence label such as "(2) HVAC".
        # This also replaces titles auto-generated from the first user message by older builds.
        chat_rows = self.connection.execute(
            "SELECT id, pdf_path, conversation_number FROM chats ORDER BY pdf_path, id"
        ).fetchall()
        counters = {}
        for chat_row in chat_rows:
            raw_scope = str(chat_row["pdf_path"] or "")
            if raw_scope.startswith("ENGO_DUAL::"):
                # Pair-specific titles are refreshed when the pair is active, because
                # only the live linked tabs can resolve both user-facing file names.
                # Keep existing titles here rather than destroying them at startup.
                continue
            stored_path = os.path.abspath(raw_scope)
            counters[stored_path] = counters.get(stored_path, 0) + 1
            number = counters[stored_path]
            file_label = Path(stored_path).stem or "PDF"
            title = f"({number}) {file_label}"
            self.connection.execute(
                "UPDATE chats SET conversation_number=?, title=? WHERE id=?",
                (number, title, int(chat_row["id"]))
            )

        self.connection.execute("CREATE INDEX IF NOT EXISTS idx_chats_pdf_updated ON chats(pdf_path, updated_at)")
        self.connection.execute("CREATE INDEX IF NOT EXISTS idx_messages_chat ON messages(chat_id, id)")
        self.connection.commit()

    @staticmethod
    def _storage_key(pdf_path: str) -> str:
        value = str(pdf_path or "")
        return value if value.startswith("ENGO_DUAL::") else os.path.abspath(value)

    def list_chats(self, pdf_path: str):
        scope_key = self._storage_key(pdf_path)
        rows = self.connection.execute(
            "SELECT id, title, created_at, updated_at FROM chats WHERE pdf_path=? ORDER BY updated_at DESC, id DESC",
            (scope_key,)
        ).fetchall()
        return [dict(row) for row in rows]

    def update_dual_chat_titles(self, scope_key: str, pair_label: str) -> None:
        """Refresh numbered pair titles, e.g. '(1) A + B', without touching messages."""
        canonical = self._storage_key(scope_key)
        if not canonical.startswith("ENGO_DUAL::"):
            return
        label = str(pair_label or "Dual File Engo AI Chat").strip()
        rows = self.connection.execute(
            "SELECT id FROM chats WHERE pdf_path=? ORDER BY id ASC", (canonical,)
        ).fetchall()
        updates = []
        for number, row in enumerate(rows, 1):
            updates.append((f"({number}) {label}", number, int(row["id"])))
        if updates:
            self.connection.executemany(
                "UPDATE chats SET title=?, conversation_number=? WHERE id=?", updates
            )
            self.connection.commit()

    def create_chat(self, pdf_path: str, title: str | None = None) -> int:
        scope_key = self._storage_key(pdf_path)
        if scope_key.startswith("ENGO_DUAL::"):
            row = self.connection.execute(
                "SELECT COALESCE(MAX(conversation_number), 0) + 1 AS next_number FROM chats WHERE pdf_path=?",
                (scope_key,)
            ).fetchone()
            number = int(row["next_number"] or 1) if row else 1
            pair_label = str(title or "Dual File Engo AI Chat").strip()
            display_title = f"({number}) {pair_label}"
        else:
            row = self.connection.execute(
                "SELECT COALESCE(MAX(conversation_number), 0) + 1 AS next_number FROM chats WHERE pdf_path=?",
                (scope_key,)
            ).fetchone()
            number = int(row["next_number"] or 1) if row else 1
            file_label = Path(scope_key).stem or "PDF"
            display_title = f"({number}) {file_label}"
        cur = self.connection.execute(
            "INSERT INTO chats(pdf_path, title, updated_at, conversation_number) VALUES(?, ?, CURRENT_TIMESTAMP, ?)",
            (scope_key, display_title, number)
        )
        self.connection.commit()
        return int(cur.lastrowid)

    def load_messages(self, chat_id: int):
        rows = self.connection.execute(
            "SELECT role, content, created_at, attachment_path, page_index, attachments_json, "
            "selected_text_context, selected_text_source_role, selected_text_location_json "
            "FROM messages WHERE chat_id=? ORDER BY id",
            (int(chat_id),)
        ).fetchall()
        result = []
        for row in rows:
            item = dict(row)
            try:
                attachments = json.loads(item.get("attachments_json") or "[]")
            except Exception:
                attachments = []
            if not attachments and item.get("attachment_path"):
                attachments = [{"path": item["attachment_path"], "page_index": item.get("page_index")}]
            item["attachments"] = [
                {
                    "path": str(a.get("path", "")),
                    "page_index": a.get("page_index"),
                    "label": str(a.get("label") or "Attached image"),
                }
                for a in attachments if isinstance(a, dict) and a.get("path")
            ]
            try:
                location = json.loads(item.get("selected_text_location_json") or "")
                item["selected_text_location"] = location if isinstance(location, dict) else None
            except Exception:
                item["selected_text_location"] = None
            result.append(item)
        return result

    def add_message(self, chat_id: int, role: str, content: str,
                    attachment_image: bytes | None = None, page_index: int | None = None,
                    attachment_images: list[dict] | None = None,
                    selected_text_context: str = "", selected_text_source_role: str = "assistant",
                    selected_text_location: dict | None = None):
        content = str(content)
        source_images = list(attachment_images or [])
        if attachment_image:
            source_images.insert(0, {"page_index": page_index, "data": bytes(attachment_image), "label": "Selected region"})
        stored_attachments = []
        try:
            attachment_dir = self.root / "chat_attachments"
            attachment_dir.mkdir(parents=True, exist_ok=True)
            for item in source_images:
                data = item.get("data") if isinstance(item, dict) else None
                if not data:
                    continue
                attachment_file = attachment_dir / f"chat_{int(chat_id)}_{uuid.uuid4().hex}.jpg"
                attachment_file.write_bytes(bytes(data))
                stored_attachments.append({
                    "path": str(attachment_file),
                    "page_index": item.get("page_index"),
                    "label": str(item.get("label") or "Selected region"),
                })
        except Exception:
            # Keep any successfully written attachments; the chat text must still be saved.
            pass
        first_path = stored_attachments[0]["path"] if stored_attachments else None
        first_page = stored_attachments[0].get("page_index") if stored_attachments else page_index
        self.connection.execute(
            "INSERT INTO messages(chat_id, role, content, attachment_path, page_index, attachments_json, "
            "selected_text_context, selected_text_source_role, selected_text_location_json) "
            "VALUES(?, ?, ?, ?, ?, ?, ?, ?, ?)",
            (int(chat_id), str(role), content, first_path, first_page,
             json.dumps(stored_attachments, ensure_ascii=False),
             str(selected_text_context or ""), str(selected_text_source_role or "assistant"),
             json.dumps(selected_text_location, ensure_ascii=False) if isinstance(selected_text_location, dict) else "")
        )
        self.connection.execute("UPDATE chats SET updated_at=CURRENT_TIMESTAMP WHERE id=?", (int(chat_id),))
        self.connection.commit()

    def migrate_chat_scopes(self, old_scope_keys, canonical_scope_key: str):
        """Move all legacy ordered-pair chat rows into one order-independent pair scope."""
        canonical = str(canonical_scope_key or "")
        changed = False
        for old_key in dict.fromkeys(str(key or "") for key in (old_scope_keys or [])):
            if not old_key or old_key == canonical:
                continue
            self.connection.execute(
                "UPDATE chats SET pdf_path=? WHERE pdf_path=?",
                (canonical, old_key)
            )
            changed = changed or self.connection.execute("SELECT changes()").fetchone()[0] > 0
        if changed:
            # Preserve old titles until the active pair can supply both file names.
            self.connection.commit()
        return changed

    def delete_chat(self, chat_id: int) -> bool:
        """Permanently delete a conversation and its stored attachment images."""
        chat_id = int(chat_id)
        rows = self.connection.execute(
            "SELECT attachment_path, attachments_json FROM messages WHERE chat_id=?",
            (chat_id,)
        ).fetchall()
        paths = set()
        for row in rows:
            if row["attachment_path"]:
                paths.add(str(row["attachment_path"]))
            try:
                values = json.loads(row["attachments_json"] or "[]")
            except Exception:
                values = []
            for value in values if isinstance(values, list) else []:
                if isinstance(value, dict) and value.get("path"):
                    paths.add(str(value["path"]))
        cur = self.connection.execute("DELETE FROM chats WHERE id=?", (chat_id,))
        self.connection.commit()
        if cur.rowcount:
            attachment_root = (self.root / "chat_attachments").resolve()
            for raw_path in paths:
                try:
                    candidate = Path(raw_path).resolve()
                    if candidate.is_relative_to(attachment_root) and candidate.is_file():
                        candidate.unlink()
                except Exception:
                    pass
            return True
        return False

    def count_all_chats(self) -> int:
        row = self.connection.execute("SELECT COUNT(*) AS total FROM chats").fetchone()
        return int(row["total"] or 0) if row else 0

    def delete_all_chats(self) -> int:
        """Delete every conversation and its attachment images, but keep the chat database."""
        rows = self.connection.execute(
            "SELECT attachment_path, attachments_json FROM messages"
        ).fetchall()
        paths = set()
        for row in rows:
            if row["attachment_path"]:
                paths.add(str(row["attachment_path"]))
            try:
                values = json.loads(row["attachments_json"] or "[]")
            except Exception:
                values = []
            for value in values if isinstance(values, list) else []:
                if isinstance(value, dict) and value.get("path"):
                    paths.add(str(value["path"]))

        count = self.count_all_chats()
        try:
            self.connection.execute("BEGIN IMMEDIATE")
            self.connection.execute("DELETE FROM messages")
            self.connection.execute("DELETE FROM chats")
            self.connection.commit()
        except Exception:
            self.connection.rollback()
            raise

        attachment_root = (self.root / "chat_attachments").resolve()
        for raw_path in paths:
            try:
                candidate = Path(raw_path).resolve()
                if candidate.is_relative_to(attachment_root) and candidate.is_file():
                    candidate.unlink()
            except Exception:
                # A locked image can be cleaned on the next cache/data maintenance pass.
                pass
        # The dedicated attachment directory contains only chat-upload images.
        # Remove any orphan files left by interrupted saves as part of deleting all chats.
        raw_attachment_root = self.root / "chat_attachments"
        try:
            if raw_attachment_root.exists() and not raw_attachment_root.is_symlink():
                for current, directories, filenames in os.walk(str(raw_attachment_root), topdown=False, followlinks=False):
                    current_path = Path(current)
                    for filename in filenames:
                        candidate = current_path / filename
                        try:
                            candidate.unlink()
                        except Exception:
                            pass
                    for dirname in directories:
                        candidate_dir = current_path / dirname
                        try:
                            if candidate_dir.is_symlink():
                                candidate_dir.unlink()
                            else:
                                candidate_dir.rmdir()
                        except Exception:
                            pass
                try:
                    raw_attachment_root.rmdir()
                except Exception:
                    pass
        except Exception:
            pass
        return count

    def get_chat_title(self, chat_id: int) -> str:
        row = self.connection.execute("SELECT title FROM chats WHERE id=?", (int(chat_id),)).fetchone()
        return str(row["title"]) if row else "Engo AI conversation"

    def close(self):
        try:
            self.connection.commit()
            self.connection.close()
        except Exception:
            pass


class ProviderModelsWorker(QThread):
    """Fetch model IDs actually exposed by the provider account behind an API key."""
    succeeded = pyqtSignal(str, object)
    failed = pyqtSignal(str, str)

    def __init__(self, provider: str, api_key: str, parent=None):
        super().__init__(parent)
        self.provider = str(provider)
        self.api_key = str(api_key or "").strip()

    def run(self):
        try:
            provider = self.provider
            if not self.api_key:
                raise ValueError("Add the provider API key first.")
            headers = {"Accept": "application/json", "User-Agent": "EngoPDFViewer/1.0"}
            if provider == "openai":
                url = "https://api.openai.com/v1/models"
                headers["Authorization"] = f"Bearer {self.api_key}"
            elif provider == "claude":
                url = "https://api.anthropic.com/v1/models?limit=1000"
                headers["x-api-key"] = self.api_key
                headers["anthropic-version"] = "2023-06-01"
            elif provider == "gemini":
                url = "https://generativelanguage.googleapis.com/v1beta/models?key=" + urllib.parse.quote(self.api_key)
            elif provider == "deepseek":
                url = "https://api.deepseek.com/models"
                headers["Authorization"] = f"Bearer {self.api_key}"
            else:
                raise ValueError("Unsupported provider.")
            # Enumerate every provider page instead of silently showing only the
            # first page of a large account's model catalogue.
            all_entries = []
            next_url = url
            for _page_number in range(30):
                request = urllib.request.Request(next_url, headers=headers, method="GET")
                with urllib.request.urlopen(request, timeout=25) as response:
                    payload = json.loads(response.read().decode("utf-8", errors="replace"))
                if not isinstance(payload, dict):
                    break
                entries = payload.get("data", payload.get("models", [])) or []
                all_entries.extend(item for item in entries if isinstance(item, dict))
                parsed = urllib.parse.urlsplit(next_url)
                query = dict(urllib.parse.parse_qsl(parsed.query, keep_blank_values=True))
                next_token = str(payload.get("nextPageToken") or "").strip()
                if provider == "gemini" and next_token:
                    query["pageToken"] = next_token
                    next_url = urllib.parse.urlunsplit((parsed.scheme, parsed.netloc, parsed.path,
                                                        urllib.parse.urlencode(query), parsed.fragment))
                    continue
                if payload.get("has_more") and entries:
                    cursor = str(payload.get("last_id") or entries[-1].get("id") or "").strip()
                    if cursor and provider == "openai":
                        query["after"] = cursor
                    elif cursor and provider == "claude":
                        query["after_id"] = cursor
                    else:
                        break
                    next_url = urllib.parse.urlunsplit((parsed.scheme, parsed.netloc, parsed.path,
                                                        urllib.parse.urlencode(query), parsed.fragment))
                    continue
                break
            entries = all_entries
            ids = []
            for item in entries or []:
                if not isinstance(item, dict):
                    continue
                model_id = str(item.get("id") or item.get("name") or "").strip()
                if model_id.startswith("models/"):
                    model_id = model_id.split("/", 1)[1]
                if not model_id:
                    continue
                if provider == "gemini":
                    methods = item.get("supportedGenerationMethods") or []
                    if "generateContent" not in methods:
                        continue
                elif provider == "openai":
                    low = model_id.lower()
                    if not (low.startswith(("gpt-", "o1", "o3", "o4", "chatgpt-"))):
                        continue
                    if any(part in low for part in ("embedding", "moderation", "whisper", "tts", "transcribe")):
                        continue
                elif provider == "claude" and not model_id.lower().startswith("claude-"):
                    continue
                elif provider == "deepseek" and not model_id.lower().startswith("deepseek-"):
                    continue
                ids.append(model_id)
            ids = sorted(set(ids), key=lambda value: ("preview" in value.lower(), value.lower()))
            if not ids:
                raise ValueError("The provider returned no chat-capable models for this key. Check key permissions or use a custom model ID.")
            self.succeeded.emit(provider, ids)
        except urllib.error.HTTPError as exc:
            detail = ""
            try:
                detail = exc.read().decode("utf-8", errors="replace")[:500]
            except Exception:
                pass
            self.failed.emit(self.provider, f"HTTP {exc.code}: {detail or exc.reason}")
        except Exception as exc:
            self.failed.emit(self.provider, str(exc))


class _AINoWheelComboBox(QComboBox):
    """Prevent accidental setting changes while the AI settings page scrolls."""
    def wheelEvent(self, event):
        # Ignore wheel changes on the combo itself so the containing scroll area
        # receives the wheel and deliberate click/keyboard selection stays intact.
        event.ignore()


class AISettingsDialog(QDialog):
    """Configure API keys and overridable model IDs for supported providers."""
    def __init__(self, settings: QSettings, parent=None):
        super().__init__(parent)
        self.settings = settings
        self.setObjectName("aiProviderSettingsDialog")
        self.setWindowTitle("Engo AI · Provider Settings")
        self.setMinimumSize(640, 560)
        self.setModal(True)
        self.key_edits = {}
        self.model_status = {}
        self.model_refresh_buttons = {}
        self._model_workers = {}
        self.lang_controls = {}

        # Keep the settings window compact; its content scrolls independently so
        # every provider and language option remains available on smaller screens.
        screen = QApplication.primaryScreen()
        available_geometry = screen.availableGeometry() if screen else QRect(0, 0, 1400, 900)
        dialog_height = max(560, min(720, available_geometry.height() - 90))
        self.resize(min(780, max(660, available_geometry.width() - 100)), dialog_height)

        root = QVBoxLayout(self)
        root.setContentsMargins(16, 15, 16, 14)
        root.setSpacing(11)

        hero = QFrame(self)
        hero.setObjectName("aiSettingsHero")
        hero_layout = QHBoxLayout(hero)
        hero_layout.setContentsMargins(16, 13, 16, 13)
        hero_layout.setSpacing(12)
        hero_mark = QLabel("✦")
        hero_mark.setObjectName("aiSettingsHeroMark")
        hero_mark.setAlignment(Qt.AlignmentFlag.AlignCenter)
        hero_mark.setFixedSize(42, 42)
        hero_copy = QVBoxLayout()
        hero_copy.setSpacing(3)
        hero_title = QLabel("AI CONNECTIONS")
        hero_title.setObjectName("aiSettingsHeroTitle")
        hero_subtitle = QLabel(
            "Connect providers, manage model access and tune voice and translation preferences."
        )
        hero_subtitle.setObjectName("aiSettingsHeroSubtitle")
        hero_subtitle.setWordWrap(True)
        hero_copy.addWidget(hero_title)
        hero_copy.addWidget(hero_subtitle)
        hero_layout.addWidget(hero_mark, 0, Qt.AlignmentFlag.AlignVCenter)
        hero_layout.addLayout(hero_copy, 1)
        root.addWidget(hero)

        content_widget = QWidget(self)
        content_widget.setObjectName("aiSettingsContent")
        content_widget.setAttribute(Qt.WidgetAttribute.WA_StyledBackground, True)
        content_layout = QVBoxLayout(content_widget)
        content_layout.setContentsMargins(3, 3, 3, 3)
        content_layout.setSpacing(8)

        intro = QLabel(
            "Add an API key from the provider's official website, then refresh available models. "
            "Website session tokens are not supported, and API billing may be separate from consumer subscriptions. "
            "PDF text or selected images are sent only when you submit a request."
        )
        intro.setObjectName("aiSettingsUsageHint")
        intro.setWordWrap(True)
        intro.setContentsMargins(2, 1, 2, 1)
        content_layout.addWidget(intro)
        form = QVBoxLayout()
        form.setSpacing(7)
        for provider, label in AI_PROVIDER_LABELS.items():
            group = QFrame()
            group.setObjectName("aiSettingsGroup")
            gl = QVBoxLayout(group)
            gl.setContentsMargins(14, 11, 14, 11)
            gl.setSpacing(8)
            label_widget = QLabel(label)
            label_widget.setObjectName("dialogLabel")
            gl.addWidget(label_widget)
            key_row = QHBoxLayout()
            key_row.addWidget(QLabel("API key"), 0)
            key_edit = QLineEdit(_get_provider_key(self.settings, provider))
            key_edit.setEchoMode(QLineEdit.EchoMode.Password)
            key_edit.setPlaceholderText("Paste API key here")
            key_edit.setClearButtonEnabled(True)
            key_row.addWidget(key_edit, 1)
            self.key_edits[provider] = key_edit
            key_page_btn = QPushButton("Get key ↗")
            key_page_btn.setObjectName("aiSettingsAction")
            key_page_btn.setToolTip(f"Open the official {label} key page in your browser")
            key_page_btn.clicked.connect(lambda _checked=False, p=provider: QDesktopServices.openUrl(QUrl(AI_KEY_URLS[p])))
            key_row.addWidget(key_page_btn)
            gl.addLayout(key_row)
            model_row = QHBoxLayout()
            refresh_btn = QPushButton("Refresh available models")
            refresh_btn.setObjectName("aiSettingsAction")
            refresh_btn.setToolTip("Fetch the models your API key can currently access from the provider.")
            refresh_btn.clicked.connect(lambda _checked=False, p=provider: self._refresh_provider_models(p))
            model_row.addWidget(refresh_btn)
            status = QLabel(self._model_status_text(provider))
            status.setObjectName("dialogHint")
            status.setWordWrap(True)
            model_row.addWidget(status, 1)
            self.model_refresh_buttons[provider] = refresh_btn
            self.model_status[provider] = status
            gl.addLayout(model_row)
            form.addWidget(group)

        live_group = QFrame()
        live_group.setObjectName("aiSettingsGroup")
        live_layout = QVBoxLayout(live_group)
        live_layout.setContentsMargins(14, 11, 14, 11)
        live_layout.setSpacing(8)
        live_label = QLabel("GEMINI REALTIME VOICE")
        live_label.setObjectName("dialogLabel")
        live_layout.addWidget(live_label)
        live_row = QHBoxLayout()
        live_row.addWidget(QLabel("Live model"))
        # Gemini Live is intentionally fixed to the fast realtime-audio model.
        # Keeping this as a read-only label prevents obsolete/unsupported thinking
        # variants saved by older builds from being selected again.
        live_model_label = QLabel("Gemini 3.8 Live · realtime audio")
        live_model_label.setObjectName("aiSettingsFixedValue")
        live_model_label.setMinimumWidth(360)
        live_model_label.setToolTip("Fixed model for fast, bidirectional Gemini Live voice sessions")
        live_model_label.setLayoutDirection(Qt.LayoutDirection.LeftToRight)
        live_model_label.setAlignment(Qt.AlignmentFlag.AlignLeft | Qt.AlignmentFlag.AlignVCenter)
        live_row.addWidget(live_model_label, 1)
        live_layout.addLayout(live_row)
        self.settings.setValue("ai_model_gemini_live", "gemini-3.8-live")
        live_hint = QLabel("The Voice & Learn window uses Gemini Live in push-to-talk mode: hold Space only while speaking. API access and billing depend on your Google AI account.")
        live_hint.setObjectName("dialogHint")
        live_hint.setWordWrap(True)
        live_layout.addWidget(live_hint)
        self.live_model_label = live_model_label
        form.addWidget(live_group)

        # Translation preferences live here; text and handwriting are translated by Google Gemini.
        language_group = QFrame()
        language_group.setObjectName("aiSettingsGroup")
        language_layout = QVBoxLayout(language_group)
        language_layout.setContentsMargins(14, 11, 14, 11)
        language_layout.setSpacing(8)
        language_title = QLabel("TRANSLATION & VOICE")
        language_title.setObjectName("dialogLabel")
        language_layout.addWidget(language_title)
        language_row = QHBoxLayout()
        language_row.addWidget(QLabel("From"))
        source_combo = _AINoWheelComboBox()
        source_combo.setObjectName("aiLanguageSelector")
        for label, code in [("Auto detect", "auto"), ("Arabic", "ar"), ("English", "en"), ("Russian", "ru"),
                            ("French", "fr"), ("German", "de"), ("Spanish", "es"), ("Turkish", "tr"),
                            ("Chinese (Simplified)", "zh-CN"), ("Japanese", "ja")]:
            source_combo.addItem(label, code)
        saved_source = self.settings.value("translate_source", "auto", type=str)
        source_combo.setCurrentIndex(max(0, source_combo.findData(saved_source)))
        language_row.addWidget(source_combo, 1)
        language_row.addWidget(QLabel("To"))
        target_combo = _AINoWheelComboBox()
        target_combo.setObjectName("aiLanguageSelector")
        for label, code in [("Arabic", "ar"), ("English", "en"), ("Russian", "ru"), ("French", "fr"),
                            ("German", "de"), ("Spanish", "es"), ("Turkish", "tr"),
                            ("Chinese (Simplified)", "zh-CN"), ("Japanese", "ja")]:
            target_combo.addItem(label, code)
        saved_target = self.settings.value("translate_target", "ar", type=str)
        target_combo.setCurrentIndex(max(0, target_combo.findData(saved_target)))
        language_row.addWidget(target_combo, 1)
        language_layout.addLayout(language_row)
        self.lang_controls["source"] = source_combo
        self.lang_controls["target"] = target_combo
        handwriting_note = QLabel("Selected text is translated directly. For handwriting or scanned pages, the translation service reads and translates only the visible writing. Engo does not save translation results or handwriting transcriptions.")
        handwriting_note.setObjectName("dialogHint")
        handwriting_note.setWordWrap(True)
        language_layout.addWidget(handwriting_note)
        voice_row = QHBoxLayout()
        voice_row.addWidget(QLabel("Voice input language"))
        voice_combo = _AINoWheelComboBox()
        voice_combo.setObjectName("aiLanguageSelector")
        for label, code in [("Arabic (Egypt)", "ar-EG"), ("English (US)", "en-US"), ("Russian", "ru-RU"), ("French", "fr-FR")]:
            voice_combo.addItem(label, code)
        saved_voice = self.settings.value("voice_input_language", "ar-EG", type=str)
        voice_combo.setCurrentIndex(max(0, voice_combo.findData(saved_voice)))
        voice_row.addWidget(voice_combo, 1)
        language_layout.addLayout(voice_row)
        self.lang_controls["voice"] = voice_combo
        form.addWidget(language_group)
        content_layout.addLayout(form)
        storage_notice = QFrame(content_widget)
        storage_notice.setObjectName("aiSettingsNotice")
        storage_notice_layout = QHBoxLayout(storage_notice)
        storage_notice_layout.setContentsMargins(12, 10, 12, 10)
        storage_notice_layout.setSpacing(9)
        storage_icon = QLabel("i")
        storage_icon.setObjectName("aiSettingsNoticeIcon")
        storage_icon.setAlignment(Qt.AlignmentFlag.AlignCenter)
        storage_icon.setFixedSize(22, 22)
        storage_hint = QLabel(
            "Keys are saved to Windows Credential Manager when available. If the OS keyring is unavailable, "
            "the app falls back to local QSettings storage; use a Windows account you trust."
        )
        storage_hint.setObjectName("dialogHint")
        storage_hint.setWordWrap(True)
        storage_notice_layout.addWidget(storage_icon, 0, Qt.AlignmentFlag.AlignTop)
        storage_notice_layout.addWidget(storage_hint, 1)
        content_layout.addWidget(storage_notice)

        scroll = QScrollArea(self)
        scroll.setObjectName("aiSettingsScroll")
        scroll.setWidgetResizable(True)
        scroll.setFrameShape(QFrame.Shape.NoFrame)
        scroll.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        scroll.setVerticalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAsNeeded)
        scroll.viewport().setObjectName("aiSettingsViewport")
        scroll.viewport().setAttribute(Qt.WidgetAttribute.WA_StyledBackground, True)
        scroll.setWidget(content_widget)
        root.addWidget(scroll, 1)

        buttons = QDialogButtonBox(QDialogButtonBox.StandardButton.Cancel | QDialogButtonBox.StandardButton.Save)
        buttons.button(QDialogButtonBox.StandardButton.Save).setObjectName("aiSettingsSave")
        buttons.button(QDialogButtonBox.StandardButton.Save).setText("Save settings")
        buttons.button(QDialogButtonBox.StandardButton.Cancel).setObjectName("aiSettingsCancel")
        _set_compact_dialog_button_heights(buttons, 26)
        buttons.accepted.connect(self._save)
        buttons.rejected.connect(self.reject)
        root.addWidget(buttons)
        self.keyring_secure = True

        # Resolve the active application theme from the owning main window immediately
        # before styling. This avoids stale/default QSettings reads when the dialog is
        # opened from the chat panel after a theme change.
        theme_settings = self.settings
        try:
            # parent.window() resolves directly to the MainWindow even when the
            # immediate parent (the chat panel) also exposes its own QSettings.
            host = parent.window() if parent is not None else None
            host_settings = getattr(host, "settings", None)
            if host_settings is not None and hasattr(host_settings, "value"):
                theme_settings = host_settings
            else:
                owner = parent
                while owner is not None:
                    candidate_settings = getattr(owner, "settings", None)
                    if candidate_settings is not None and hasattr(candidate_settings, "value"):
                        theme_settings = candidate_settings
                    owner = owner.parent() if hasattr(owner, "parent") else None
            theme_settings.sync()
        except Exception:
            pass
        try:
            theme_value = theme_settings.value("ui_theme", "dark", type=str)
        except Exception:
            theme_value = "dark"
        active_theme = normalize_ui_theme(theme_value)
        self._active_ui_theme = active_theme
        theme_tokens = engo_ui_theme_tokens(active_theme)
        palette = {
            "bg": theme_tokens["window"],
            "hero1": theme_tokens["panel_alt"],
            "hero2": theme_tokens["panel"],
            "card": theme_tokens["panel"],
            "field": theme_tokens["input"],
            "border": theme_tokens["border"],
            "text": theme_tokens["text"],
            "muted": theme_tokens["muted"],
            "accent": theme_tokens["accent"],
            "soft": theme_tokens["selection"],
            "notice": theme_tokens["panel_alt"],
            "notice_border": theme_tokens["border_strong"],
            "hover": theme_tokens["hover"],
        }
        pc = palette
        # Apply an explicit QPalette as well as QSS. On Windows the native widget
        # palette can otherwise leak light surfaces into child controls/popups even
        # when the dialog stylesheet is dark.
        dialog_palette = QPalette(self.palette())
        for role, color_key in (
            (QPalette.ColorRole.Window, "bg"),
            (QPalette.ColorRole.WindowText, "text"),
            (QPalette.ColorRole.Base, "field"),
            (QPalette.ColorRole.AlternateBase, "card"),
            (QPalette.ColorRole.Text, "text"),
            (QPalette.ColorRole.Button, "card"),
            (QPalette.ColorRole.ButtonText, "text"),
            (QPalette.ColorRole.Highlight, "accent"),
        ):
            dialog_palette.setColor(role, QColor(pc[color_key]))
        dialog_palette.setColor(QPalette.ColorRole.HighlightedText, QColor("#ffffff"))
        dialog_palette.setColor(QPalette.ColorRole.PlaceholderText, QColor(pc["muted"]))
        dialog_palette.setColor(QPalette.ColorRole.ToolTipBase, QColor(pc["card"]))
        dialog_palette.setColor(QPalette.ColorRole.ToolTipText, QColor(pc["text"]))
        self.setPalette(dialog_palette)
        self.setAutoFillBackground(True)
        for themed_widget in (hero, content_widget, scroll, scroll.viewport(), buttons):
            themed_widget.setPalette(dialog_palette)
        # Explicitly propagate the palette through all nested controls. Windows native
        # styles can otherwise paint child frames/combos with a light system surface.
        for themed_widget in self.findChildren(QWidget):
            themed_widget.setPalette(dialog_palette)
            if isinstance(themed_widget, QLabel):
                themed_widget.setAutoFillBackground(False)
                themed_widget.setAttribute(Qt.WidgetAttribute.WA_StyledBackground, False)
            elif isinstance(themed_widget, (QFrame, QScrollArea)):
                themed_widget.setAutoFillBackground(True)
        self.setAttribute(Qt.WidgetAttribute.WA_StyledBackground, True)
        content_widget.setAttribute(Qt.WidgetAttribute.WA_StyledBackground, True)
        content_widget.setAutoFillBackground(True)
        scroll.setAttribute(Qt.WidgetAttribute.WA_StyledBackground, True)
        scroll.viewport().setAttribute(Qt.WidgetAttribute.WA_StyledBackground, True)
        scroll.viewport().setAutoFillBackground(True)

        self.setStyleSheet(f"""
            QDialog#aiProviderSettingsDialog {{ background-color:{pc['bg']}; color:{pc['text']}; }}
            QDialog#aiProviderSettingsDialog QWidget {{ color:{pc['text']}; }}
            QDialog#aiProviderSettingsDialog QLabel {{ background:transparent; color:{pc['text']}; border:0; padding:0; }}
            QDialog#aiProviderSettingsDialog QFrame#aiSettingsHero {{ background:transparent; border:0; border-radius:0; }}
            QDialog#aiProviderSettingsDialog QLabel#aiSettingsHeroMark {{ color:{pc['accent']}; background:transparent; border:0; border-radius:0; font-size:21pt; font-weight:800; }}
            QDialog#aiProviderSettingsDialog QLabel#aiSettingsHeroTitle {{ color:{pc['text']}; font-size:12pt; font-weight:850; letter-spacing:1px; }}
            QDialog#aiProviderSettingsDialog QLabel#aiSettingsHeroSubtitle {{ color:{pc['muted']}; font-size:8.3pt; }}
            QDialog#aiProviderSettingsDialog QScrollArea#aiSettingsScroll {{ background:{pc['bg']}; border:0; }}
            QDialog#aiProviderSettingsDialog QWidget#aiSettingsViewport, QDialog#aiProviderSettingsDialog QWidget#aiSettingsContent {{ background-color:{pc['bg']}; color:{pc['text']}; }}
            QDialog#aiProviderSettingsDialog QLabel#aiSettingsUsageHint {{ background:transparent; color:{pc['text']}; border:0; border-radius:0; padding:0; font-size:8.5pt; }}
            QDialog#aiProviderSettingsDialog QFrame#aiSettingsGroup {{ background:transparent; border:0; border-radius:0; }}
            QDialog#aiProviderSettingsDialog QLabel#dialogLabel {{ color:{pc['text']}; font-size:9pt; font-weight:800; }}
            QDialog#aiProviderSettingsDialog QLabel#dialogHint {{ color:{pc['muted']}; font-size:7.8pt; }}
            QDialog#aiProviderSettingsDialog QLineEdit, QDialog#aiProviderSettingsDialog QComboBox {{ background:{pc['field']}; color:{pc['text']}; border:1px solid {pc['border']}; border-radius:8px; padding:6px 9px; min-height:25px; selection-background-color:{pc['accent']}; selection-color:#ffffff; }}
            QDialog#aiProviderSettingsDialog QLineEdit:focus, QDialog#aiProviderSettingsDialog QComboBox:focus {{ background:{pc['field']}; color:{pc['text']}; border:1px solid {pc['accent']}; }}
            QDialog#aiProviderSettingsDialog QComboBox::drop-down {{ width:25px; border-left:1px solid {pc['border']}; background:{pc['field']}; }}
            QDialog#aiProviderSettingsDialog QComboBox QAbstractItemView {{ background:{pc['field']}; color:{pc['text']}; border:1px solid {pc['border']}; padding:4px; selection-background-color:{pc['soft']}; selection-color:{pc['text']}; outline:0; }}
            QDialog#aiProviderSettingsDialog QComboBox QAbstractItemView::viewport {{ background:{pc['field']}; }}
            QDialog#aiProviderSettingsDialog QComboBox QAbstractItemView::item {{ background:transparent; color:{pc['text']}; padding:5px 7px; }}
            QDialog#aiProviderSettingsDialog QComboBox QAbstractItemView::item:selected {{ background:{pc['soft']}; color:{pc['text']}; }}
            QDialog#aiProviderSettingsDialog QAbstractItemView {{ background:{pc['field']}; color:{pc['text']}; selection-background-color:{pc['soft']}; selection-color:{pc['text']}; outline:0; }}
            QDialog#aiProviderSettingsDialog QToolTip {{ background:{pc['card']}; color:{pc['text']}; border:1px solid {pc['border']}; padding:5px 7px; }}
            QDialog#aiProviderSettingsDialog QPushButton#aiSettingsAction {{ background:{pc['soft']}; color:{pc['text']}; border:1px solid {pc['border']}; border-radius:8px; padding:4px 10px; min-height:24px; font-weight:700; }}
            QDialog#aiProviderSettingsDialog QPushButton#aiSettingsAction:hover {{ background:{pc['hover']}; color:{pc['text']}; border-color:{pc['accent']}; }}
            QDialog#aiProviderSettingsDialog QPushButton#aiSettingsAction:pressed {{ background:{pc['accent']}; color:#ffffff; border-color:{pc['accent']}; }}
            QDialog#aiProviderSettingsDialog QPushButton#aiSettingsAction:disabled {{ color:{pc['muted']}; background:{pc['field']}; border-color:{pc['border']}; }}
            QDialog#aiProviderSettingsDialog QFrame#aiSettingsNotice {{ background:transparent; border:0; border-radius:0; }}
            QDialog#aiProviderSettingsDialog QLabel#aiSettingsNoticeIcon {{ background:transparent; color:{pc['accent']}; border:0; border-radius:0; font-weight:800; }}
            QDialog#aiProviderSettingsDialog QDialogButtonBox QPushButton {{ min-width:90px; min-height:26px; max-height:26px; border-radius:7px; padding:1px 10px; font-weight:700; }}
            QDialog#aiProviderSettingsDialog QPushButton#aiSettingsCancel {{ background:{pc['card']}; color:{pc['text']}; border:1px solid {pc['border']}; }}
            QDialog#aiProviderSettingsDialog QPushButton#aiSettingsCancel:hover {{ background:{pc['hover']}; color:{pc['text']}; border-color:{pc['accent']}; }}
            QDialog#aiProviderSettingsDialog QPushButton#aiSettingsSave {{ background:{pc['accent']}; color:#ffffff; border:1px solid {pc['accent']}; }}
            QDialog#aiProviderSettingsDialog QPushButton#aiSettingsSave:hover {{ background:{pc['hover']}; color:{pc['text']}; border-color:{pc['accent']}; }}
            QDialog#aiProviderSettingsDialog QScrollBar:vertical {{ background:transparent; width:10px; margin:3px 1px; }}
            QDialog#aiProviderSettingsDialog QScrollBar::handle:vertical {{ background:{pc['border']}; border-radius:4px; min-height:28px; }}
            QDialog#aiProviderSettingsDialog QScrollBar::add-line:vertical, QDialog#aiProviderSettingsDialog QScrollBar::sub-line:vertical {{ height:0; }}
        """)

        self.apply_language(self.settings.value("interface_language", "en", type=str))

    def _ai_tr(self, source):
        text = str(source or "")
        if getattr(self, "_ai_language", "en") != "ar":
            return text
        exact = {
            "Engo AI · Provider Settings": "إعدادات مزوّدي الذكاء الاصطناعي · Engo",
            "AI CONNECTIONS": "اتصالات الذكاء الاصطناعي",
            "Connect providers, manage model access and tune voice and translation preferences.": "اربط مزوّدي الذكاء الاصطناعي، وأدر الوصول إلى النماذج، واضبط تفضيلات الصوت والترجمة.",
            "Add an API key from the provider's official website, then refresh available models. Website session tokens are not supported, and API billing may be separate from consumer subscriptions. PDF text or selected images are sent only when you submit a request.": "أضف مفتاح API من الموقع الرسمي للمزوّد، ثم حدّث قائمة النماذج المتاحة. رموز جلسات المواقع غير مدعومة، وقد تُحاسب واجهة API بشكل منفصل عن اشتراكات الاستخدام العادي. لا يُرسل نص PDF أو الصور المحددة إلا عند إرسال طلب.",
            "API key": "مفتاح API", "Paste API key here": "الصق مفتاح API هنا", "Get key ↗": "الحصول على المفتاح ↗",
            "Refresh available models": "تحديث النماذج المتاحة",
            "GEMINI REALTIME VOICE": "الصوت الفوري من Gemini", "Live model": "النموذج الفوري",
            "The Voice & Learn window uses Gemini Live in push-to-talk mode: hold Space only while speaking. API access and billing depend on your Google AI account.": "تستخدم نافذة الصوت والتعلّم وضع التحدث بالضغط المستمر مع Gemini Live: اضغط مطولًا على Space أثناء الكلام فقط. يعتمد الوصول إلى API والفوترة على حساب Google AI الخاص بك.",
            "TRANSLATION & VOICE": "الترجمة والصوت", "From": "من", "To": "إلى",
            "Selected text is translated directly. For handwriting or scanned pages, the translation service reads and translates only the visible writing. Engo does not save translation results or handwriting transcriptions.": "تُترجم النصوص المحددة مباشرة. أما الكتابة اليدوية والصفحات الممسوحة ضوئيًا، فتقرأ خدمة الترجمة الكتابة الظاهرة فقط وتترجمها. لا يحفظ Engo نتائج الترجمة أو تفريغ الكتابة اليدوية.",
            "Voice input language": "لغة الإدخال الصوتي",
            "Keys are saved to Windows Credential Manager when available. If the OS keyring is unavailable, the app falls back to local QSettings storage; use a Windows account you trust.": "تُحفظ المفاتيح في Windows Credential Manager عند توفره. إذا لم تتوفر خدمة حفظ المفاتيح في النظام، فسيستخدم البرنامج تخزين QSettings المحلي؛ استخدم حساب Windows تثق به.",
            "Save settings": "حفظ الإعدادات", "Cancel": "إلغاء", "Loading…": "جارٍ التحميل…",
            "Enter an API key above, then refresh.": "أدخل مفتاح API بالأعلى، ثم حدّث القائمة.",
            "Contacting provider…": "جارٍ الاتصال بمزوّد الخدمة…",
            "Not fetched yet": "لم يتم جلب النماذج بعد",
            "Auto detect": "اكتشاف تلقائي", "Arabic": "العربية", "English": "الإنجليزية", "Russian": "الروسية",
            "French": "الفرنسية", "German": "الألمانية", "Spanish": "الإسبانية", "Turkish": "التركية",
            "Chinese (Simplified)": "الصينية (المبسطة)", "Japanese": "اليابانية", "Arabic (Egypt)": "العربية (مصر)",
            "English (US)": "الإنجليزية (الولايات المتحدة)",
            "Gemini 3.8 Live · realtime audio": "Gemini 3.8 Live · صوت فوري",
        }
        if text in exact:
            return exact[text]
        import re as _re
        match = _re.fullmatch(r"(\d+) models cached · choose the model beside the chat provider", text)
        if match:
            return f"{match.group(1)} نموذج محفوظ · اختر النموذج بجوار مزوّد المحادثة"
        match = _re.fullmatch(r"Found (\d+) available models\. Save settings to use them in chat\.", text)
        if match:
            return f"تم العثور على {match.group(1)} نموذج متاح. احفظ الإعدادات لاستخدامها في المحادثة."
        if text.startswith("Could not load models:"):
            return "تعذّر تحميل النماذج: " + text.partition(":")[2].strip()
        if text.startswith("Open the official ") and text.endswith(" key page in your browser"):
            provider = text[len("Open the official "):-len(" key page in your browser")]
            return f"فتح صفحة مفاتيح {provider} الرسمية في المتصفح"
        if text.startswith("Fetch the models your API key can currently access"):
            return "جلب النماذج التي يستطيع مفتاح API الوصول إليها حاليًا من المزوّد."
        if text.startswith("Model ID for native, bidirectional Gemini Live"):
            return "معرّف النموذج لجلسات Gemini Live الصوتية ثنائية الاتجاه."
        return _engo_translate_tooltip(text, "ar") if str(getattr(self, "_ai_language", "en")) == "ar" else text

    def apply_language(self, language=None):
        value = str(language or self.settings.value("interface_language", "en", type=str) or "en").lower()
        self._ai_language = "ar" if value.startswith("ar") else "en"
        is_ar = self._ai_language == "ar"
        direction = Qt.LayoutDirection.RightToLeft if is_ar else Qt.LayoutDirection.LeftToRight
        self.setLayoutDirection(direction)
        self.setWindowTitle(self._ai_tr("Engo AI · Provider Settings"))
        # Capture each source string once so switching Arabic/English is reversible.
        for widget_class in (QLabel, QPushButton, QToolButton, QCheckBox):
            for widget in self.findChildren(widget_class):
                try:
                    original = widget.property("engoAiSourceText")
                    if original is None:
                        original = widget.text()
                        widget.setProperty("engoAiSourceText", original)
                    widget.setText(self._ai_tr(original) if is_ar else str(original or ""))
                    tip = widget.property("engoAiSourceToolTip")
                    if tip is None:
                        tip = widget.toolTip()
                        widget.setProperty("engoAiSourceToolTip", tip)
                    if tip:
                        widget.setToolTip(self._ai_tr(tip) if is_ar else str(tip))
                    widget.setLayoutDirection(direction)
                except RuntimeError:
                    continue
        for combo in self.findChildren(QComboBox):
            try:
                originals = combo.property("engoAiSourceItems")
                if originals is None:
                    originals = [combo.itemText(i) for i in range(combo.count())]
                    combo.setProperty("engoAiSourceItems", originals)
                for index, original in enumerate(originals):
                    if index < combo.count():
                        combo.setItemText(index, self._ai_tr(original) if is_ar else str(original))
                tip = combo.property("engoAiSourceToolTip")
                if tip is None:
                    tip = combo.toolTip()
                    combo.setProperty("engoAiSourceToolTip", tip)
                if tip:
                    combo.setToolTip(self._ai_tr(tip) if is_ar else str(tip))
                combo.setLayoutDirection(direction)
            except RuntimeError:
                continue
        for edit in self.findChildren(QLineEdit):
            try:
                original = edit.property("engoAiSourcePlaceholder")
                if original is None:
                    original = edit.placeholderText()
                    edit.setProperty("engoAiSourcePlaceholder", original)
                edit.setPlaceholderText(self._ai_tr(original) if is_ar else str(original or ""))
                edit.setLayoutDirection(direction)
            except RuntimeError:
                continue
        # API keys and provider model IDs are identifiers, not prose. Keep their
        # editable text left-to-right even while Arabic labels and surrounding UI are RTL.
        for edit in self.key_edits.values():
            try:
                edit.setLayoutDirection(Qt.LayoutDirection.LeftToRight)
                edit.setAlignment(Qt.AlignmentFlag.AlignLeft | Qt.AlignmentFlag.AlignVCenter)
            except RuntimeError:
                pass
        try:
            self.live_model_label.setLayoutDirection(Qt.LayoutDirection.LeftToRight)
            self.live_model_label.setAlignment(Qt.AlignmentFlag.AlignLeft | Qt.AlignmentFlag.AlignVCenter)
        except (RuntimeError, AttributeError):
            pass
        # Status labels are refreshed from their source state after language changes.
        for provider, label in self.model_status.items():
            try:
                source = label.property("engoAiSourceText")
                if source is None:
                    source = label.text()
                    label.setProperty("engoAiSourceText", source)
                label.setText(self._ai_tr(source) if is_ar else str(source or ""))
            except RuntimeError:
                pass

    def _model_status_text(self, provider):
        try:
            raw = self.settings.value(f"ai_available_models_{provider}", "[]", type=str)
            models = json.loads(raw) if isinstance(raw, str) else list(raw or [])
            return f"{len(models)} models cached · choose the model beside the chat provider" if models else "Not fetched yet"
        except Exception:
            return "Not fetched yet"

    def _refresh_provider_models(self, provider):
        key = self.key_edits[provider].text().strip()
        if not key:
            self.model_status[provider].setProperty("engoAiSourceText", "Enter an API key above, then refresh.")
            self.model_status[provider].setText(self._ai_tr("Enter an API key above, then refresh."))
            return
        old = self._model_workers.get(provider)
        if old is not None and old.isRunning():
            return
        button = self.model_refresh_buttons[provider]
        button.setEnabled(False)
        button.setText(self._ai_tr("Loading…"))
        self.model_status[provider].setProperty("engoAiSourceText", "Contacting provider…")
        self.model_status[provider].setText(self._ai_tr("Contacting provider…"))
        worker = ProviderModelsWorker(provider, key, self)
        worker.succeeded.connect(self._on_models_loaded)
        worker.failed.connect(self._on_models_failed)
        worker.finished.connect(lambda p=provider, w=worker: self._on_models_worker_finished(p, w))
        self._model_workers[provider] = worker
        worker.start()

    def _on_models_loaded(self, provider, model_ids):
        self.settings.setValue(f"ai_available_models_{provider}", json.dumps(list(model_ids)))
        source = f"Found {len(model_ids)} available models. Save settings to use them in chat."
        self.model_status[provider].setProperty("engoAiSourceText", source)
        self.model_status[provider].setText(self._ai_tr(source))

    def _on_models_failed(self, provider, message):
        source = f"Could not load models: {message}"
        self.model_status[provider].setProperty("engoAiSourceText", source)
        self.model_status[provider].setText(self._ai_tr(source))

    def _on_models_worker_finished(self, provider, worker):
        self.model_refresh_buttons[provider].setEnabled(True)
        self.model_refresh_buttons[provider].setText(self._ai_tr("Refresh available models"))
        if self._model_workers.get(provider) is worker:
            self._model_workers.pop(provider, None)
        worker.deleteLater()

    def _save(self):
        secure_all = True
        for provider in AI_PROVIDER_LABELS:
            key = self.key_edits[provider].text().strip()
            if not _save_provider_key(self.settings, provider, key):
                secure_all = False
            # Model choice belongs to the current chat composer, not provider settings.
        self.settings.setValue("ai_model_gemini_live", "gemini-3.8-live")
        self.settings.setValue("translate_source", str(self.lang_controls["source"].currentData() or "auto"))
        self.settings.setValue("translate_target", str(self.lang_controls["target"].currentData() or "ar"))
        self.settings.setValue("voice_input_language", str(self.lang_controls["voice"].currentData() or "ar-EG"))
        self.keyring_secure = secure_all
        self.settings.sync()
        self.accept()


class AIRequestWorker(QThread):
    succeeded = pyqtSignal(str, str)
    failed = pyqtSignal(str, str)
    progress = pyqtSignal(str, str)
    streamed = pyqtSignal(str, str)
    cancelled = pyqtSignal(str)

    CONNECT_TIMEOUT_SECONDS = 25
    READ_TIMEOUT_SECONDS = 45

    def __init__(self, path: str, provider: str, model: str, api_key: str, question: str,
                 history: list[dict[str, str]], include_context: bool, selected_images, mode: str,
                 current_page_index: int = 0, supplemental_documents: list[dict] | None = None,
                 pdf_snapshots: dict[str, bytes] | None = None):
        super().__init__()
        self._cancel_event = threading.Event()
        self._response_lock = threading.Lock()
        self._active_response = None
        self.path = path
        self.provider = provider
        self.model = model
        self.api_key = api_key
        self.question = question
        self.history = history[-20:]
        office_source = is_office_document(path)
        self.include_context = bool(include_context and not office_source)
        if office_source and mode in ("page", "teach"):
            mode = "custom"
        if isinstance(selected_images, (bytes, bytearray)):
            self.selected_images = [{"page_index": None, "data": bytes(selected_images), "label": "User-selected region"}] if selected_images else []
        else:
            self.selected_images = list(selected_images or [])
        self.mode = mode
        self.system_prompt = AI_SYSTEM_PROMPT
        self.current_page_index = max(0, int(current_page_index or 0))
        self.supplemental_documents = ([] if office_source else
                                       [dict(item) for item in (supplemental_documents or [])
                                        if isinstance(item, dict) and item.get("path")])
        self.pdf_snapshots = {
            os.path.normcase(os.path.abspath(path)): bytes(data)
            for path, data in (pdf_snapshots or {}).items()
            if path and data
        }

    def _open_pdf(self, path: str):
        snapshot = self.pdf_snapshots.get(os.path.normcase(os.path.abspath(path or "")))
        if snapshot:
            return fitz.open(stream=snapshot, filetype="pdf")
        return fitz.open(path)

    def cancel(self):
        """Request cancellation and close an active HTTP response to interrupt a blocked read."""
        self._cancel_event.set()
        with self._response_lock:
            response = self._active_response
        if response is not None:
            try:
                response.close()
            except Exception:
                pass

    def _check_cancelled(self):
        if self._cancel_event.is_set():
            raise InterruptedError("AI request cancelled by user.")

    def _set_active_response(self, response):
        with self._response_lock:
            self._active_response = response
        if self._cancel_event.is_set():
            try:
                response.close()
            except Exception:
                pass
            self._check_cancelled()

    def _clear_active_response(self, response):
        with self._response_lock:
            if self._active_response is response:
                self._active_response = None

    @staticmethod
    def _readable_timeout_message():
        return ("The AI service did not send data before the read timeout. "
                "Try a shorter question, a faster model, or fewer attached page images. "
                "You can use Stop at any time to cancel a slow response.")

    @staticmethod
    def _is_program_help_question(question: str) -> bool:
        """Detect explicit questions about Engo's own controls, settings, and workflows.

        This deliberately errs on the conservative side: the in-app program manual is
        not added to ordinary PDF-study prompts, so it does not consume model tokens
        unless the user is asking how to operate or configure Engo itself.
        """
        text = str(question or "").strip().lower()
        if not text:
            return False
        app_refs = (
            "engo", "البرنامج", "التطبيق", "الواجهة", "الشاشة", "الزر", "زر ",
            "الأيقونة", "ايقونة", "القائمة", "الشريط", "التول بار", "التولبار",
            "sidebar", "toolbar", "settings", "setting", "menu", "button", "icon",
            "in the app", "in engo", "pdf viewer", "this program", "this app",
        )
        feature_terms = (
            "files", "file", "open", "save", "search", "sidebar", "scroll", "book", "fit width",
            "fit page", "zoom", "link", "unlink", "annotation", "highlight", "pen",
            "sticky note", "text box", "translate", "translation", "voice", "ai teacher",
            "ask by voice", "full screen", "fullscreen", "present", "chat", "conversation", "session",
            "theme", "tab", "checkbox", "select", "resize", "rotate", "undo", "redo", "copy", "paste",
            "dual", "primary", "secondary", "microphone", "send button", "stop button", "feature", "tool",
            "export", "print", "attach", "attachment", "recent files", "restore", "reopen", "dialog",
            "الملفات", "ملف", "فتح", "حفظ", "بحث", "سايدبار", "الجانب", "التمرير", "بووك",
            "التكبير", "التصغير", "ملاءمة", "ربط", "فك الربط", "هايلايت", "القلم",
            "النوت", "ملاحظة", "مربع النص", "ترجمة", "فويس", "محادثة", "الشات",
            "الشاشة الكاملة", "عرض تقديمي", "التحديد", "نسخ", "لصق", "إعدادات", "الثيم",
            "التبويب", "التاب", "المحادثات", "استعادة الجلسة", "آخر جلسة", "اخر جلسة", "جلسة", "الجلسات",
            "استعيد", "استرجاع", "الميكروفون", "الصوت", "الثيم", "لون الصفحة", "ميزة", "مميزات",
            "خاصية", "وظيفة", "أداة", "اداة", "الأدوات", "زر", "تصدير", "طباعة", "مرفق", "الملفات الأخيرة",
            "التدوير", "تغيير الحجم", "حذف", "التراجع",
            "الإعادة", "الارسال", "الإرسال", "علامة الصح", "مربع الاختيار", "التعليم", "المدرس الصوتي",
        )
        how_terms = (
            "where", "how", "how do", "how can", "which button", "which icon", "shortcut",
            "what", "why", "why does", "why is", "difference", "how does", "what does",
            "not working", "doesn't work", "isn't working", "where can i", "where do i",
            "فين", "اين", "أين", "ازاي", "إزاي", "كيف", "اعمل", "أعمل", "استخدم",
            "استخدام", "اضغط", "أضغط", "مكان", "موجود", "افعل", "أفعل", "اعداد", "إعداد",
            "الفرق", "يعني ايه", "يعني اي", "ايه وظيفة", "ما وظيفة", "ما هو", "شرح", "مش شغال", "مش بيشتغل",
            "بيعمل ايه", "بتعمل ايه", "بيعمل اي", "بتعمل اي", "ايه لازمة", "ايه فايدة", "ازاي استخدم",
            "ليه", "لماذا", "ازاي اصل", "اوصل", "اعرف منين", "فين الاقي", "فين ألاقي",
            "ازاي اخلي", "ازاي اغير", "ازاي احذف", "ازاي افتح", "ازاي اقفل", "ازاي استعيد",
        )
        has_feature = any(term in text for term in feature_terms)
        has_app_reference = any(term in text for term in app_refs)
        is_how_to = any(term in text for term in how_terms)
        return has_feature and (has_app_reference or is_how_to)

    def _load_program_manual_on_demand(self) -> str:
        """Read the companion Markdown manual only for application-help questions."""
        try:
            manual_path = Path(resource_path("ENGO_PROGRAM_GUIDE.md"))
            if manual_path.is_file():
                return manual_path.read_text(encoding="utf-8")
        except Exception:
            pass
        return ""

    def run(self):
        try:
            self.progress.emit(self.path, "Preparing your question and reading the Office document…" if is_office_document(self.path) else "Preparing your question and reading the PDF…")
            self._check_cancelled()
            program_help = self._is_program_help_question(self.question)
            if not program_help and len(str(self.question or "").strip()) <= 180:
                recent_user_turns = [
                    str(item.get("content") or "") for item in self.history[-6:]
                    if str(item.get("role") or "") == "user"
                ]
                short_follow_up = any(token in str(self.question or "").lower() for token in (
                    "فين", "ازاي", "إزاي", "اين", "أين", "where", "how", "which", "ده", "دي",
                    "دا", "زر", "مكان", "مش شغال", "does it", "what about", "and if"
                ))
                program_help = short_follow_up and any(
                    self._is_program_help_question(previous) for previous in recent_user_turns[-2:]
                )
            if program_help:
                manual = self._load_program_manual_on_demand()
                if manual:
                    self.system_prompt = (
                        self.system_prompt
                        + "\n\nENGO APPLICATION HELP MODE: The user is asking about Engo PDF Viewer & AI Study Agent itself, "
                          "not only the PDF subject. Use the following in-app manual as the authoritative map of "
                          "the actual controls, locations, and workflows. Give exact button names and where they are "
                          "located. Do not invent menu items or claim a feature exists unless the manual describes it. "
                          "If a feature is not documented, say so clearly.\n\n"
                        + "<ENGO_PROGRAM_GUIDE>\n" + manual + "\n</ENGO_PROGRAM_GUIDE>"
                    )
            context = ""
            images: list[dict[str, object]] = []
            sampled_images = []
            has_user_selected_regions = any(
                isinstance(item, dict) and bool(item.get("data")) for item in self.selected_images
            )
            # Native PDF text selected from the document is sent inside explicit
            # delimiters by the chat panel. Treat it as a scoped user selection too,
            # even though it does not require an image attachment.
            has_manual_selected_text = (
                "<<<BEGIN SELECTED CHAT PASSAGE>>>" in str(self.question or "")
                and "<<<END SELECTED CHAT PASSAGE>>>" in str(self.question or "")
            )
            has_selected_scope = has_user_selected_regions or has_manual_selected_text
            if self.mode in ("page", "teach") and not program_help and not has_selected_scope:
                # Page-specific actions always include the current page, even if the user
                # disabled whole-document context in the chat options.
                context, sampled_images = self._read_page_context(self.path, self.current_page_index)
                images.extend(sampled_images)
            elif self.include_context and not program_help:
                context, sampled_images = self._read_pdf_context(self.path)
                images.extend(sampled_images)
                if self.mode == "custom" or self.supplemental_documents:
                    # In a combined study, always attach the visible primary page image as well
                    # as the companion page, even when whole-document text context is enabled.
                    # This makes the conversation follow the two pages actually shown side by side.
                    current_page_label = f"Current PDF page {self.current_page_index + 1}"
                    if not any(current_page_label in str(item.get("label", "")) for item in images):
                        _page_note, visible_page_images = self._read_page_context(self.path, self.current_page_index)
                        images.extend(visible_page_images)
            elif self.supplemental_documents and not program_help and not has_selected_scope:
                # A linked pair is an explicit request to discuss the currently visible pages.
                # Keep both images available even when whole-document context is switched off.
                context, visible_page_images = self._read_page_context(self.path, self.current_page_index)
                images.extend(visible_page_images)
            # A linked companion PDF contributes its currently displayed page to the same
            # request. The primary file remains the owner of the saved conversation.
            if not program_help and (self.include_context or (self.mode in ("page", "teach") and not has_selected_scope) or (self.supplemental_documents and not has_selected_scope)):
                for supplement in self.supplemental_documents[:2]:
                    self._check_cancelled()
                    companion_path = os.path.abspath(str(supplement.get("path") or ""))
                    if not companion_path or not os.path.isfile(companion_path) or os.path.normcase(companion_path) == os.path.normcase(os.path.abspath(self.path)):
                        continue
                    companion_page = max(0, int(supplement.get("page_index", 0) or 0))
                    companion_name = str(supplement.get("name") or Path(companion_path).name)
                    if self.include_context and self.mode not in ("page", "teach"):
                        # In dual-file mode, include the COMPLETE companion document as
                        # well as its currently visible page. A selected crop is an
                        # additional clue, never a restriction to that crop or file.
                        companion_context, companion_sample_images = self._read_pdf_context(companion_path)
                        context += (
                            f"\n\n--- COMPLETE LINKED PDF: {companion_name} ---\n"
                            f"{companion_context}\n--- END COMPLETE LINKED PDF: {companion_name} ---"
                        )
                        for companion_image in companion_sample_images:
                            companion_image = dict(companion_image)
                            companion_image["label"] = f"LINKED PDF SAMPLE · {companion_name} · {companion_image.get('label', 'page image')}"
                            images.append(companion_image)
                    companion_page_context, companion_page_images = self._read_page_context(companion_path, companion_page)
                    context += (
                        f"\n\n--- CURRENTLY DISPLAYED LINKED PDF PAGE: {companion_name} · page {companion_page + 1} ---\n"
                        f"{companion_page_context}\n--- END CURRENTLY DISPLAYED LINKED PDF PAGE ---"
                    )
                    for companion_image in companion_page_images:
                        companion_image = dict(companion_image)
                        companion_image["label"] = f"CURRENT LINKED PAGE · {companion_name} · {companion_image.get('label', 'page image')}"
                        images.append(companion_image)
            translation_only = "literal translation engine" in str(self.system_prompt or "").casefold()
            if not program_help and not has_selected_scope and not translation_only and not is_office_document(self.path) and "USER-DEFINED REGION TAGS" not in context:
                try:
                    tag_doc = self._open_pdf(self.path)
                    try:
                        tagged_context, tagged_images = self._read_tagged_regions(tag_doc, max_images=16)
                    finally:
                        tag_doc.close()
                    if tagged_context:
                        context = (context + "\n\n" if context else "") + tagged_context
                        images.extend(tagged_images)
                except Exception:
                    pass
            for index, item in enumerate(self.selected_images, 1):
                data = item.get("data") if isinstance(item, dict) else None
                if data:
                    page_index = item.get("page_index")
                    page_note = f" from page {int(page_index) + 1}" if page_index is not None else ""
                    label = item.get("label") or f"User-selected region {index}{page_note}"
                    images.insert(index - 1, {"label": str(label), "mime": "image/jpeg", "data": bytes(data)})
            user_content = self.question
            if context:
                user_content += "\n\n--- PDF CONTENT CONTEXT (extracted locally from this file) ---\n" + context + "\n--- END PDF CONTENT CONTEXT ---"
            if images:
                labels = ", ".join(str(item["label"]) for item in images)
                if has_user_selected_regions:
                    if self.include_context:
                        user_content += (
                            f"\n\nAttached page images and user-selected region(s): {labels}. "
                            "SCOPE PRIORITY (80/20): The user manually selected a specific region. Make that region the primary subject of the answer and devote roughly 80% of the analysis and response to what is visible/readable in that region. Use the remaining PDF context (about 20%) only to clarify a symbol, definition, nearby step, reference, or essential dependency. Do not drift into unrelated sections or provide a whole-document answer unless explicitly asked. Identify when a contextual fact comes from outside the selected region."
                        )
                    else:
                        user_content += (
                            f"\n\nAttached user-selected region(s): {labels}. "
                            "STRICT SCOPE (100%): Answer using ONLY the manually selected region(s) and the user's question. Do not use, infer from, or summarize unrelated pages, the rest of the PDF, linked documents, or tagged regions. If the selected crop is unclear or insufficient, say exactly what cannot be read or what extra context is needed instead of guessing from the rest of the file."
                        )
                else:
                    user_content += (
                        f"\n\nAttached page images and selected regions: {labels}. "
                        "When PDF context is enabled, use the full extracted text of the primary PDF and every linked companion PDF when needed. "
                        "Identify which file and page each piece of evidence comes from and compare them only when the question requires it."
                    )
            if has_manual_selected_text:
                if self.include_context:
                    user_content += (
                        "\n\nSELECTED NATIVE PDF TEXT PRIORITY (80/20): The passage between "
                        "<<<BEGIN SELECTED CHAT PASSAGE>>> and <<<END SELECTED CHAT PASSAGE>>> "
                        "is the exact text the user selected in the PDF. Make it the primary subject and devote roughly 80% "
                        "of the analysis and answer to that passage. Use the remaining PDF context only to clarify directly "
                        "relevant symbols, definitions, nearby steps, or dependencies. Do not drift into unrelated sections."
                    )
                else:
                    user_content += (
                        "\n\nSTRICT SELECTED-PASSAGE SCOPE (100%): The passage between "
                        "<<<BEGIN SELECTED CHAT PASSAGE>>> and <<<END SELECTED CHAT PASSAGE>>> "
                        "is the only document content you may use for this answer. Do not rely on other pages, the rest of the PDF, "
                        "linked files, or region tags. If it is insufficient, explain what is missing rather than guessing."
                    )
            if "USER-DEFINED REGION TAGS" in context:
                user_content += (
                    "\n\nTAG-SCOPED REQUEST RULE: When the user's question names one of the region tags, "
                    "use only the tagged regions with that exact tag name for the requested summary/list/analysis. "
                    "Do not mix in untagged text, full-page text, or other tags just because their subject is similar. "
                    "This tag-scope rule overrides the general full-document and crop-reference guidance above, "
                    "unless the user explicitly asks for comparisons or broader context."
                )
            if not program_help and not is_office_document(self.path) and not self.include_context and not images and not has_manual_selected_text:
                user_content += "\n\nNo PDF text or page image was supplied for this request. If the question refers to the file, ask for context rather than guessing."
            elif not program_help and is_office_document(self.path):
                user_content += "\n\nSOURCE FORMAT: The selected passage above comes from a native Word or PowerPoint document. The original Office text was not converted to PDF. Answer using the selected Office passage; do not assume PDF pages or images were provided."
            self._check_cancelled()
            self.progress.emit(self.path, f"Connecting to {AI_PROVIDER_LABELS.get(self.provider, self.provider)}…")
            if self.mode == "teach":
                self.progress.emit(self.path, "Planning a page-linked lesson and board notes…")
                user_content += (
                    "\n\nTEACHING MODE: Return valid JSON only, with no Markdown fences, using this exact shape: "
                    '{"title":"short lesson title","overview":"one concise overview","steps":['
                    '{"say":"one short spoken explanation","board":"formula, example, or key note for the side board",'
                    '"page":1,"box":[0.1,0.2,0.3,0.12],"label":"short region label"}]} . '
                    "Return 3 to 6 steps. 'page' is a 1-based PDF page number. 'box' is an approximate normalized "
                    "[x,y,width,height] rectangle from 0 to 1 relative to the page, tightly around the item currently "
                    "being explained. If no reliable region can be located, use null for box. Each step's 'say' should "
                    "be natural spoken language, maximum 2 sentences; board can contain examples or equations. Use only "
                    "what is visible on the supplied current page. The JSON must contain only title, overview, and steps."
                )
                answer = self._call_provider(user_content, images, stream=False)
            elif self.include_context and self.mode == "document" and len(context) > 22000 and not sampled_images:
                answer = self._answer_large_document(context, images)
            else:
                self.progress.emit(self.path, "Waiting for the first answer tokens… (Stop is available)")
                answer = self._call_provider(user_content, images, stream=True)
            self._check_cancelled()
            if not str(answer or "").strip():
                raise RuntimeError("The model returned an empty response. It may be temporarily overloaded or unavailable; try again or select another model.")
            self.succeeded.emit(self.path, answer)
        except InterruptedError:
            self.cancelled.emit(self.path)
        except Exception as exc:
            if self._cancel_event.is_set():
                self.cancelled.emit(self.path)
            else:
                self.failed.emit(self.path, str(exc))

    def _read_tagged_regions(self, doc, page_indices=None, max_images=16):
        """Expose user-tagged page regions to AI, including crops for scanned content."""
        sections = []
        images = []
        indices = range(doc.page_count) if page_indices is None else list(page_indices)
        for page_index in indices:
            self._check_cancelled()
            try:
                page = doc.load_page(int(page_index))
                for annot in list(page.annots() or []):
                    info = annot.info or {}
                    if str(info.get("title") or "") != "Engo Region Tag":
                        continue
                    tag_name = str(info.get("content") or "").strip()
                    if not tag_name:
                        continue
                    clip = fitz.Rect(annot.rect) & page.rect
                    if clip.is_empty:
                        continue
                    text = str(page.get_text("text", clip=clip) or "").strip()
                    sections.append(
                        f"[Tag: {tag_name} | PDF page {int(page_index) + 1}]\n" +
                        (text[:9000] if text else "[No selectable text in this tagged area; inspect its attached crop image.]"))
                    if len(images) < max_images:
                        scale = min(1.5, 1300.0 / max(float(clip.width), float(clip.height), 1.0))
                        pix = page.get_pixmap(matrix=fitz.Matrix(scale, scale), clip=clip, alpha=False, annots=False)
                        img = Image.frombytes("RGB", (pix.width, pix.height), pix.samples)
                        img.thumbnail((1300, 1300), Image.Resampling.LANCZOS)
                        buff = io.BytesIO()
                        img.save(buff, format="JPEG", quality=82, optimize=True)
                        images.append({"label": f"User-tagged region · {tag_name} · PDF page {int(page_index) + 1}",
                                       "mime": "image/jpeg", "data": buff.getvalue()})
            except Exception:
                continue
        if not sections:
            return "", []
        tag_names = sorted({
            line.split(" | PDF page", 1)[0].replace("[Tag: ", "", 1)
            for section in sections for line in section.splitlines()[:1]
        }, key=str.casefold)
        header = (
            "USER-DEFINED REGION TAGS (created by the reader): " + ", ".join(tag_names) + "\n"
            "The following excerpts and crop images are the exact areas the reader assigned to each tag. "
            "When the user's question names a tag, use only the regions carrying that exact tag for the requested summary, "
            "list, or analysis. Do not mix in untagged page content or regions with other tags unless the user asks for that. "
            "The page number is the original 1-based PDF page number.\n\n"
        )
        return header + "\n\n".join(sections), images

    def _read_page_context(self, path: str, page_index: int):
        doc = self._open_pdf(path)
        try:
            if doc.page_count <= 0:
                return "[The PDF has no pages.]", []
            self._check_cancelled()
            page_index = max(0, min(int(page_index), doc.page_count - 1))
            page = doc.load_page(page_index)
            text = page.get_text("text").strip()
            # A page-mode question may still refer to a tag that spans other pages.
            # Include all tagged regions from this live PDF, not only this visible page.
            tagged_context, tagged_images = self._read_tagged_regions(doc, max_images=16)
            scale = min(1.8, 1550.0 / max(float(page.rect.width), float(page.rect.height), 1.0))
            pix = page.get_pixmap(matrix=fitz.Matrix(scale, scale), alpha=False)
            img = Image.frombytes("RGB", (pix.width, pix.height), pix.samples)
            img.thumbnail((1550, 1550), Image.Resampling.LANCZOS)
            buff = io.BytesIO()
            img.save(buff, format="JPEG", quality=84, optimize=True)
            context = f"[Current PDF page: {page_index + 1} of {doc.page_count}]\n"
            context += text if text else "[No selectable text on this page; use the attached page image to read it.]"
            if tagged_context:
                context += "\n\n" + tagged_context
            image = {"label": f"Current PDF page {page_index + 1} (full-page image)", "mime": "image/jpeg", "data": buff.getvalue()}
            return context, [image] + tagged_images
        finally:
            doc.close()

    def _read_pdf_context(self, path: str):
        doc = self._open_pdf(path)
        try:
            total = doc.page_count
            segments = []
            char_count = 0
            truncated_at = None
            for i in range(total):
                self._check_cancelled()
                if i == 0 or (i + 1) % 5 == 0:
                    self.progress.emit(self.path, f"Reading PDF text: page {i + 1}/{total}…")
                text = doc.load_page(i).get_text("text").strip()
                if not text:
                    continue
                block = f"[Page {i + 1}]\n{text}"
                remaining = 120000 - char_count
                if remaining <= 0:
                    truncated_at = i + 1
                    break
                if len(block) > remaining:
                    block = block[:remaining]
                    truncated_at = i + 1
                segments.append(block)
                char_count += len(block)
                if char_count >= 120000:
                    break
            extracted = "\n\n".join(segments)
            tagged_context, tagged_images = self._read_tagged_regions(doc, max_images=16)
            if tagged_context:
                extracted = (extracted + "\n\n" if extracted else "") + tagged_context
            images = list(tagged_images)
            # Scanned/image-only PDFs have almost no selectable text. Attach compact
            # page samples across the whole file for providers that support vision inputs.
            if len(extracted.strip()) < 900 and total > 0:
                max_pages = min(10, total)
                if total <= max_pages:
                    indices = list(range(total))
                else:
                    indices = sorted(set(round(i * (total - 1) / (max_pages - 1)) for i in range(max_pages)))
                labels = []
                for sample_number, index in enumerate(indices, 1):
                    self._check_cancelled()
                    self.progress.emit(self.path, f"Rendering scanned page {sample_number}/{len(indices)}…")
                    page = doc.load_page(index)
                    scale = min(1.4, 1100.0 / max(float(page.rect.width), float(page.rect.height), 1.0))
                    pix = page.get_pixmap(matrix=fitz.Matrix(scale, scale), alpha=False)
                    image = Image.frombytes("RGB", (pix.width, pix.height), pix.samples)
                    image.thumbnail((1100, 1100), Image.Resampling.LANCZOS)
                    buff = io.BytesIO()
                    image.save(buff, format="JPEG", quality=76, optimize=True)
                    images.append({"label": f"PDF page {index + 1} (scan preview)", "mime": "image/jpeg", "data": buff.getvalue()})
                    labels.append(str(index + 1))
                scanned_note = (
                    f"This PDF has little selectable text. Attached image previews cover pages: {', '.join(labels)}. "
                    "Use only those previews as visual evidence; if the file contains more pages than previews, do not claim every page was read."
                )
                extracted = (extracted + "\n\n" if extracted else "") + scanned_note
            elif extracted:
                if truncated_at:
                    extracted += f"\n\n[Context limit reached at around page {truncated_at}; this extract is partial. Total document pages: {total}.]"
                else:
                    extracted += f"\n\n[Total pages in the PDF: {total}.]"
            else:
                extracted = f"[No selectable text could be extracted from this PDF. Total pages: {total}.]"
            return extracted, images
        finally:
            doc.close()

    def _answer_large_document(self, context: str, selected_images: list[dict[str, object]]) -> str:
        """Map/reduce long text PDFs for document-wide summary/review prompts."""
        paragraphs = context.split("\n\n")
        chunks = []
        current = []
        current_len = 0
        target = 18000
        for paragraph in paragraphs:
            if current and current_len + len(paragraph) + 2 > target:
                chunks.append("\n\n".join(current))
                current = []
                current_len = 0
            # A single page paragraph can itself be very long; split it safely.
            while len(paragraph) > target:
                if current:
                    chunks.append("\n\n".join(current))
                    current, current_len = [], 0
                chunks.append(paragraph[:target])
                paragraph = paragraph[target:]
            if paragraph:
                current.append(paragraph)
                current_len += len(paragraph) + 2
        if current:
            chunks.append("\n\n".join(current))
        tag_scope_rule = (
            "\n\nTAG-SCOPED REQUEST RULE: If the question names a region tag, use only regions carrying that exact tag; "
            "ignore untagged text and other tags unless the user explicitly asks for broader comparison."
            if "USER-DEFINED REGION TAGS" in context else ""
        )
        if len(chunks) <= 1:
            return self._call_provider(self.question + "\n\nPDF context:\n" + context + tag_scope_rule, selected_images)

        partials = []
        for index, chunk in enumerate(chunks, 1):
            self._check_cancelled()
            self.progress.emit(self.path, f"Analyzing PDF section {index}/{len(chunks)}…")
            self.streamed.emit(self.path, f"\n\n### Analyzing section {index}/{len(chunks)}\n\n")
            prompt = (
                f"The user asked: {self.question}\n\n"
                f"Analyze section {index} of {len(chunks)} from the same PDF. "
                + tag_scope_rule + " "
                + "Extract only information relevant to the user's task. Preserve key concepts, definitions, "
                "formulas, units, examples, and page references. Be concise but don't omit important details. "
                "Do not present this section as if it were the entire document.\n\n"
                f"SECTION {index}/{len(chunks)}:\n{chunk}"
            )
            partials.append(f"SECTION {index} SUMMARY:\n" + self._call_provider(prompt, [], stream=True))

        self._check_cancelled()
        self.progress.emit(self.path, "Combining section analyses into the final answer…")
        self.streamed.emit(self.path, "\n\n---\n\n### Writing the final answer\n\n")
        final_prompt = (
            f"Original user request: {self.question}\n\n"
            + tag_scope_rule + "\n\n"
            + "Synthesize these section analyses into one coherent answer about the whole document. "
            "Remove repetition, preserve important formulas/definitions, and mention if the PDF context "
            "was truncated by the reader's safety limit. Do not add facts that are not in the summaries.\n\n"
            + "\n\n".join(partials)
        )
        return self._call_provider(final_prompt, selected_images, stream=True)

    def _call_provider(self, user_content: str, images: list[dict[str, object]], stream: bool = False) -> str:
        provider = self.provider
        if provider == "openai":
            return self._call_openai_responses(user_content, images, stream=stream)
        if provider == "claude":
            return self._call_claude(user_content, images, stream=stream)
        if provider == "deepseek":
            return self._call_openai_compatible(user_content, images, stream=stream)
        if provider == "gemini":
            return self._call_gemini(user_content, images, stream=stream)
        raise RuntimeError("Unknown AI provider.")

    def _image_parts_openai(self, images):
        result = []
        for item in images:
            raw = bytes(item["data"])
            encoded = base64.b64encode(raw).decode("ascii")
            mime = str(item["mime"])
            result.append({"type": "text", "text": f"[{item['label']}]"})
            result.append({"type": "image_url", "image_url": {"url": f"data:{mime};base64,{encoded}", "detail": "high"}})
        return result

    def _call_openai_responses(self, user_content, images, stream: bool = False):
        """Use OpenAI's current Responses API, including native input_image parts."""
        url = "https://api.openai.com/v1/responses"
        input_items = []
        for item in self.history:
            role = item.get("role")
            if role in ("user", "assistant"):
                prior_content = item.get("content", "")
                history_attachments = self._history_attachment_paths(item) if role == "user" else []
                if history_attachments:
                    parts = [{"type": "input_text", "text": prior_content}]
                    for page_number, image_path in history_attachments:
                        try:
                            encoded_prior = base64.b64encode(Path(image_path).read_bytes()).decode("ascii")
                            parts.append({"type": "input_text", "text": f"[Previously attached crop from PDF page {page_number}]"})
                            parts.append({"type": "input_image", "image_url": f"data:image/jpeg;base64,{encoded_prior}", "detail": "high"})
                        except Exception:
                            continue
                    input_items.append({"role": role, "content": parts})
                else:
                    input_items.append({"role": role, "content": prior_content})
        current_parts = [{"type": "input_text", "text": user_content}]
        for item in images:
            encoded = base64.b64encode(bytes(item["data"])).decode("ascii")
            current_parts.append({"type": "input_text", "text": f"[{item['label']}]"})
            current_parts.append({
                "type": "input_image",
                "image_url": f"data:{item['mime']};base64,{encoded}",
                "detail": "high"
            })
        input_items.append({"role": "user", "content": current_parts})
        payload = {
            "model": self.model,
            "instructions": self.system_prompt,
            "input": input_items,
            "max_output_tokens": 2500,
            "store": False
        }
        if stream:
            payload["stream"] = True
        req = urllib.request.Request(url, data=json.dumps(payload).encode("utf-8"), headers={
            "Authorization": f"Bearer {self.api_key}",
            "Content-Type": "application/json",
            "Accept": "text/event-stream" if stream else "application/json",
            "User-Agent": "EngoPDFViewer/9.0",
        }, method="POST")
        if stream:
            return self._stream_json_events(req, self._openai_responses_delta)
        data = self._http_json(req)
        if isinstance(data.get("output_text"), str) and data["output_text"].strip():
            return data["output_text"].strip()
        collected = []
        for item in data.get("output", []):
            for part in item.get("content", []):
                if part.get("type") in ("output_text", "text") and part.get("text"):
                    collected.append(part["text"])
        if collected:
            return "\n".join(collected).strip()
        if data.get("error"):
            raise RuntimeError(data["error"].get("message", "OpenAI returned an error."))
        raise RuntimeError("OpenAI returned an empty or unexpected response.")

    @staticmethod
    def _anthropic_image_block(raw: bytes, mime: str = "image/jpeg") -> dict[str, object]:
        # Anthropic Messages API accepts base64 images with an explicit media type.
        allowed = {"image/jpeg", "image/png", "image/gif", "image/webp"}
        if mime not in allowed:
            mime = "image/jpeg"
        return {
            "type": "image",
            "source": {
                "type": "base64",
                "media_type": mime,
                "data": base64.b64encode(raw).decode("ascii"),
            },
        }

    def _claude_content_blocks(self, text: str, images: list[dict[str, object]]) -> list[dict[str, object]]:
        blocks: list[dict[str, object]] = [{"type": "text", "text": text}]
        for item in images:
            label = str(item.get("label") or "Attached PDF image")
            blocks.append({"type": "text", "text": f"[{label}]"})
            blocks.append(self._anthropic_image_block(bytes(item["data"]), str(item.get("mime") or "image/jpeg")))
        return blocks

    def _call_claude(self, user_content, images, stream: bool = False):
        """Call Anthropic's Messages API; supports text, PDF crops/images, history, and SSE streaming."""
        url = "https://api.anthropic.com/v1/messages"
        messages: list[dict[str, object]] = []
        for item in self.history:
            role = item.get("role")
            if role not in ("user", "assistant"):
                continue
            prior_content = str(item.get("content", ""))
            history_attachments = self._history_attachment_paths(item) if role == "user" else []
            if not history_attachments:
                messages.append({"role": role, "content": prior_content})
                continue
            blocks: list[dict[str, object]] = [{"type": "text", "text": prior_content}]
            for page_number, image_path in history_attachments:
                try:
                    raw = Path(image_path).read_bytes()
                    suffix = Path(image_path).suffix.lower()
                    mime = {".png": "image/png", ".gif": "image/gif", ".webp": "image/webp"}.get(suffix, "image/jpeg")
                    blocks.append({"type": "text", "text": f"[Previously attached crop from PDF page {page_number}]"})
                    blocks.append(self._anthropic_image_block(raw, mime))
                except Exception:
                    continue
            messages.append({"role": role, "content": blocks})

        current_content: object = self._claude_content_blocks(user_content, images) if images else user_content
        messages.append({"role": "user", "content": current_content})
        payload: dict[str, object] = {
            "model": self.model,
            "system": self.system_prompt,
            "messages": messages,
            "max_tokens": 4096,
        }
        if stream:
            payload["stream"] = True
        req = urllib.request.Request(
            url,
            data=json.dumps(payload).encode("utf-8"),
            headers={
                "x-api-key": self.api_key,
                "anthropic-version": "2023-06-01",
                "Content-Type": "application/json",
                "Accept": "text/event-stream" if stream else "application/json",
                "User-Agent": "EngoPDFViewer/15.4",
            },
            method="POST",
        )
        if stream:
            return self._stream_json_events(req, self._claude_delta)
        data = self._http_json(req)
        if data.get("error"):
            err = data.get("error")
            raise RuntimeError(err.get("message", str(err)) if isinstance(err, dict) else str(err))
        try:
            text = "\n".join(str(part.get("text", "")) for part in data.get("content", []) if part.get("type") == "text" and part.get("text"))
            return text.strip() or "Claude returned an empty response."
        except Exception:
            raise RuntimeError("Claude returned an unexpected response format.")

    @staticmethod
    def _claude_delta(data):
        if data.get("type") == "error" or data.get("error"):
            error = data.get("error", data)
            raise RuntimeError(error.get("message", str(error)) if isinstance(error, dict) else str(error))
        if data.get("type") == "content_block_delta":
            delta = data.get("delta") or {}
            if delta.get("type") == "text_delta":
                return str(delta.get("text") or "")
        return ""

    def _call_openai_compatible(self, user_content, images, stream: bool = False):
        # DeepSeek official model IDs: deepseek-flash (vision) and deepseek-v4-pro (text-only).
        url = "https://api.deepseek.com/chat/completions"
        if images and self.model == "deepseek-v4-pro":
            raise RuntimeError(
                "DeepSeek V4 Pro is text-only and cannot read PDF page images. "
                "Choose DeepSeek V4.1 Flash (deepseek-flash) for screenshots, scans, handwriting, or page images."
            )
        user_parts = [{"type": "text", "text": user_content}]
        user_parts.extend(self._image_parts_openai(images))
        messages = [{"role": "system", "content": self.system_prompt}]
        for item in self.history:
            if item.get("role") in ("user", "assistant"):
                prior_content = item.get("content", "")
                history_attachments = self._history_attachment_paths(item) if item.get("role") == "user" else []
                if history_attachments:
                    prior_parts = [{"type": "text", "text": prior_content}]
                    for page_number, image_path in history_attachments:
                        try:
                            image_data = Path(image_path).read_bytes()
                            image_label = f"Previously attached crop from PDF page {page_number}"
                            prior_parts.extend(self._image_parts_openai([{"data": image_data, "mime": "image/jpeg", "label": image_label}]))
                        except Exception:
                            continue
                    messages.append({"role": item["role"], "content": prior_parts})
                else:
                    messages.append({"role": item["role"], "content": prior_content})
        messages.append({"role": "user", "content": user_parts if images else user_content})
        payload = {"model": self.model, "messages": messages, "max_tokens": 2500, "temperature": float(getattr(self, "temperature", 0.35))}
        if stream:
            payload["stream"] = True
        body = json.dumps(payload).encode("utf-8")
        req = urllib.request.Request(url, data=body, headers={
            "Authorization": f"Bearer {self.api_key}",
            "Content-Type": "application/json",
            "Accept": "text/event-stream" if stream else "application/json",
            "User-Agent": "EngoPDFViewer/9.0",
        }, method="POST")
        if stream:
            return self._stream_json_events(req, self._chat_completion_delta)
        data = self._http_json(req)
        try:
            content = data["choices"][0]["message"]["content"]
            if isinstance(content, list):
                content = "\n".join(str(part.get("text", "")) for part in content if isinstance(part, dict))
            return str(content).strip() or "The provider returned an empty response."
        except Exception:
            raise RuntimeError("DeepSeek returned an unexpected response format.")

    def _call_gemini(self, user_content, images, stream: bool = False):
        method = "streamGenerateContent?alt=sse" if stream else "generateContent"
        url = f"https://generativelanguage.googleapis.com/v1beta/models/{urllib.parse.quote(self.model, safe='')}:{method}&key={urllib.parse.quote(self.api_key)}" if stream else f"https://generativelanguage.googleapis.com/v1beta/models/{urllib.parse.quote(self.model, safe='')}:generateContent?key={urllib.parse.quote(self.api_key)}"
        parts = [{"text": user_content}]
        for item in images:
            parts.append({"text": f"[{item['label']}]"})
            parts.append({"inline_data": {"mime_type": str(item["mime"]), "data": base64.b64encode(bytes(item["data"])).decode("ascii")}})
        contents = []
        for item in self.history:
            role = item.get("role")
            if role in ("user", "assistant"):
                prior_parts = [{"text": item.get("content", "")}]
                history_attachments = self._history_attachment_paths(item) if role == "user" else []
                for page_number, image_path in history_attachments:
                    try:
                        prior_parts.append({"text": f"[Previously attached crop from PDF page {page_number}]"})
                        prior_parts.append({"inline_data": {"mime_type": "image/jpeg", "data": base64.b64encode(Path(image_path).read_bytes()).decode("ascii")}})
                    except Exception:
                        continue
                contents.append({"role": "user" if role == "user" else "model", "parts": prior_parts})
        contents.append({"role": "user", "parts": parts})
        generation_config = {
            "temperature": float(getattr(self, "temperature", 0.35)),
            "maxOutputTokens": int(getattr(self, "max_output_tokens", 2500)),
        }
        if str(self.model).strip() == "gemini-3.5-flash-lite":
            # Translation is a literal extraction task. Explicit MINIMAL thinking
            # avoids spending latency on multi-step reasoning that is not needed.
            generation_config["thinkingConfig"] = {"thinkingLevel": "minimal"}
        payload = {
            "systemInstruction": {"parts": [{"text": self.system_prompt}]},
            "contents": contents,
            "generationConfig": generation_config,
        }
        req = urllib.request.Request(url, data=json.dumps(payload).encode("utf-8"), headers={
            "Content-Type": "application/json", "Accept": "text/event-stream" if stream else "application/json", "User-Agent": "EngoPDFViewer/9.0"
        }, method="POST")
        if stream:
            return self._stream_json_events(req, self._gemini_delta)
        data = self._http_json(req)
        try:
            parts_out = data["candidates"][0]["content"]["parts"]
            text = "\n".join(str(part.get("text", "")) for part in parts_out if part.get("text"))
            return text.strip() or "Gemini returned an empty response."
        except Exception:
            if data.get("promptFeedback", {}).get("blockReason"):
                raise RuntimeError(f"Gemini blocked this prompt: {data['promptFeedback']['blockReason']}")
            raise RuntimeError("Gemini returned an unexpected response format.")

    @staticmethod
    def _history_attachment_paths(item):
        """Return [(page_number, path)] for current or legacy saved attachments."""
        result = []
        attachments = item.get("attachments") or []
        for attachment in attachments:
            if not isinstance(attachment, dict):
                continue
            path = attachment.get("path")
            if path and os.path.isfile(path):
                try:
                    page_number = int(attachment.get("page_index") or 0) + 1
                except Exception:
                    page_number = 1
                result.append((page_number, path))
        if not result and item.get("attachment_path") and os.path.isfile(item["attachment_path"]):
            try:
                page_number = int(item.get("page_index") or 0) + 1
            except Exception:
                page_number = 1
            result.append((page_number, item["attachment_path"]))
        return result

    @staticmethod
    def _openai_responses_delta(data):
        if data.get("type") == "error":
            raise RuntimeError(data.get("message") or data.get("error", {}).get("message") or "OpenAI streaming error")
        return str(data.get("delta") or "") if data.get("type") == "response.output_text.delta" else ""

    @staticmethod
    def _chat_completion_delta(data):
        if data.get("error"):
            error = data.get("error")
            raise RuntimeError(error.get("message", str(error)) if isinstance(error, dict) else str(error))
        try:
            content = data["choices"][0].get("delta", {}).get("content", "")
            if isinstance(content, list):
                return "".join(str(x.get("text", "")) for x in content if isinstance(x, dict))
            return str(content or "")
        except (KeyError, IndexError, TypeError):
            return ""

    @staticmethod
    def _gemini_delta(data):
        if data.get("error"):
            error = data["error"]
            raise RuntimeError(error.get("message", str(error)) if isinstance(error, dict) else str(error))
        try:
            parts = data["candidates"][0]["content"]["parts"]
            return "".join(str(part.get("text", "")) for part in parts if part.get("text"))
        except (KeyError, IndexError, TypeError):
            return ""

    def _open_with_retry(self, req):
        """Retry transient overload/rate-limit errors such as HTTP 503 without resending on other errors."""
        retry_codes = {429, 500, 502, 503, 504}
        for attempt in range(3):
            self._check_cancelled()
            try:
                return urllib.request.urlopen(req, timeout=self.CONNECT_TIMEOUT_SECONDS)
            except urllib.error.HTTPError as exc:
                if exc.code not in retry_codes or attempt >= 2:
                    raise
                wait_seconds = 2 * (attempt + 1)
                self.progress.emit(
                    self.path,
                    f"Provider is busy (HTTP {exc.code}). Retrying automatically in {wait_seconds}s ({attempt + 1}/2)…"
                )
                try:
                    exc.close()
                except Exception:
                    pass
                if self._cancel_event.wait(wait_seconds):
                    self._check_cancelled()
        raise RuntimeError("The AI provider is temporarily unavailable. Please retry shortly.")

    def _stream_json_events(self, req, delta_parser):
        """Read SSE incrementally; surface text as it arrives and allow Stop to cancel it."""
        chunks = []
        response = None
        try:
            self._check_cancelled()
            response = self._open_with_retry(req)
            self._set_active_response(response)
            self.progress.emit(self.path, "Connected to the AI service — waiting for response tokens…")
            try:
                response.fp.raw._sock.settimeout(self.READ_TIMEOUT_SECONDS)
            except Exception:
                pass
            while True:
                self._check_cancelled()
                raw_line = response.readline()
                if not raw_line:
                    break
                line = raw_line.decode("utf-8", errors="replace").strip()
                if not line or line.startswith(":") or not line.startswith("data:"):
                    continue
                raw = line[5:].strip()
                if raw == "[DONE]":
                    break
                try:
                    payload = json.loads(raw)
                except Exception:
                    continue
                delta = delta_parser(payload)
                if delta:
                    text_delta = str(delta)
                    chunks.append(text_delta)
                    self.progress.emit(self.path, "Receiving answer…")
                    self.streamed.emit(self.path, text_delta)
        except urllib.error.HTTPError as exc:
            try:
                raw_error = exc.read().decode("utf-8", errors="replace")
                parsed = json.loads(raw_error)
                detail = parsed.get("error", {}).get("message") or parsed.get("message") or raw_error[:1200]
            except Exception:
                detail = str(exc)
            raise RuntimeError(f"API request failed (HTTP {exc.code}): {detail}")
        except urllib.error.URLError as exc:
            reason = getattr(exc, "reason", None)
            if isinstance(reason, (TimeoutError, socket.timeout)):
                raise RuntimeError("Timed out while connecting to the AI service. Check your connection, then retry.")
            raise RuntimeError(f"Could not connect to the AI service: {exc.reason}. Check internet access and firewall settings.")
        except (TimeoutError, socket.timeout):
            if self._cancel_event.is_set():
                raise InterruptedError("AI request cancelled by user.")
            raise RuntimeError(self._readable_timeout_message())
        finally:
            if response is not None:
                self._clear_active_response(response)
                try:
                    response.close()
                except Exception:
                    pass
        self._check_cancelled()
        result = "".join(chunks).strip()
        if not result:
            raise RuntimeError("The AI service returned an empty streaming response. Check the selected model and its streaming support.")
        return result

    def _http_json(self, req):
        response = None
        try:
            self._check_cancelled()
            response = self._open_with_retry(req)
            self._set_active_response(response)
            try:
                response.fp.raw._sock.settimeout(self.READ_TIMEOUT_SECONDS)
            except Exception:
                pass
            chunks = []
            while True:
                self._check_cancelled()
                part = response.read(8192)
                if not part:
                    break
                chunks.append(part)
            raw = b"".join(chunks)
        except urllib.error.HTTPError as exc:
            try:
                message = exc.read().decode("utf-8", errors="replace")
                parsed = json.loads(message)
                detail = parsed.get("error", {}).get("message") or parsed.get("message") or message[:1500]
            except Exception:
                detail = str(exc)
            raise RuntimeError(f"API request failed (HTTP {exc.code}): {detail}")
        except urllib.error.URLError as exc:
            reason = getattr(exc, "reason", None)
            if isinstance(reason, (TimeoutError, socket.timeout)):
                raise RuntimeError("Timed out while connecting to the AI service. Check your connection, then retry.")
            raise RuntimeError(f"Could not connect to the AI service: {exc.reason}. Check internet access and firewall settings.")
        except (TimeoutError, socket.timeout):
            if self._cancel_event.is_set():
                raise InterruptedError("AI request cancelled by user.")
            raise RuntimeError(self._readable_timeout_message())
        finally:
            if response is not None:
                self._clear_active_response(response)
                try:
                    response.close()
                except Exception:
                    pass
        self._check_cancelled()
        try:
            return json.loads(raw.decode("utf-8"))
        except Exception:
            raise RuntimeError("The AI service returned invalid JSON.")
