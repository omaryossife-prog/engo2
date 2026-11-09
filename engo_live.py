# Auto-split from main.py (verbatim move; do not reformat).
from __future__ import annotations

import math
import asyncio
import queue
import os
import sys
import json
import tempfile
import io
import sqlite3
import subprocess
import re
import base64
import threading
import time
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
    engo_ui_theme_tokens,
    normalize_ui_theme,
    resource_path,
)
from engo_markdown import (
    _set_markdown_browser,
    _set_markdown_document,
)
from engo_widgets import (
    MiddleMouseAutoScroll,
    _engo_file_dialog,
    make_icon,
)



class VoiceInputWorker(QThread):
    """Continuous push-to-talk transcription that fills the chat draft without sending it."""
    recognized = pyqtSignal(str)
    partialText = pyqtSignal(str)
    failed = pyqtSignal(str)
    progress = pyqtSignal(str)

    def __init__(self, language: str = "ar-EG", initial_text: str = ""):
        super().__init__()
        self.language = str(language or "ar-EG")
        self.initial_text = str(initial_text or "").strip()
        self._cancel_event = threading.Event()
        self._chunks = []
        self._chunks_lock = threading.Lock()

    def cancel(self):
        """Stop microphone capture; recognized words remain in the chat composer."""
        self._cancel_event.set()

    def run(self):
        stop_listening = None
        try:
            import speech_recognition as sr
            import pyaudio  # noqa: F401 - SpeechRecognition requires this for microphone capture
        except Exception as exc:
            self.failed.emit(
                "Microphone support is missing PyAudio in the Python environment used by Engo.\n\n"
                f"Python: {sys.executable}\n\n"
                "Close Engo PDF Viewer & AI Study Agent, then run Fix_Microphone.bat from the same folder as run.bat. "
                "After installation finishes, restart the viewer.\n\n"
                f"Technical detail: {exc}"
            )
            return

        recognizer = sr.Recognizer()
        try:
            self.progress.emit("Listening · tap to stop")
            # Calibrate in a short, separate context. listen_in_background() opens
            # the AudioSource itself inside its worker thread, so passing a source
            # that is still inside `with` causes SpeechRecognition's nested-context
            # AssertionError. Keep one source instance, but never hold it open here.
            source = sr.Microphone()
            with source as calibration_source:
                recognizer.adjust_for_ambient_noise(calibration_source, duration=0.45)
            if self._cancel_event.is_set():
                return

            def on_audio(recognizer_instance, audio):
                if self._cancel_event.is_set():
                    return
                try:
                    chunk = recognizer_instance.recognize_google(audio, language=self.language).strip()
                except sr.UnknownValueError:
                    return
                except Exception as exc:
                    # A single transient recognition failure should not discard
                    # earlier recognized phrases or terminate microphone capture.
                    self.progress.emit(f"Listening · {exc}")
                    return
                if not chunk:
                    return
                with self._chunks_lock:
                    if self._chunks and self._chunks[-1].casefold() == chunk.casefold():
                        return
                    self._chunks.append(chunk)
                    spoken = " ".join(self._chunks).strip()
                combined = " ".join(part for part in (self.initial_text, spoken) if part).strip()
                self.partialText.emit(combined)
                self.progress.emit("Listening · tap to stop")

            # The SpeechRecognition background listener owns the source context.
            stop_listening = recognizer.listen_in_background(
                source, on_audio, phrase_time_limit=4
            )
            while not self._cancel_event.wait(0.10):
                pass
            # Wait for any phrase already captured to finish recognition before
            # publishing the final draft and allowing the user to edit/send it.
            stopper, stop_listening = stop_listening, None
            try:
                stopper(wait_for_stop=True)
            except Exception:
                pass
            with self._chunks_lock:
                spoken = " ".join(self._chunks).strip()
            combined = " ".join(part for part in (self.initial_text, spoken) if part).strip()
            if combined:
                self.recognized.emit(combined)
        except Exception as exc:
            if not self._cancel_event.is_set():
                self.failed.emit(str(exc))
            else:
                with self._chunks_lock:
                    spoken = " ".join(self._chunks).strip()
                combined = " ".join(part for part in (self.initial_text, spoken) if part).strip()
                if combined:
                    self.recognized.emit(combined)
        finally:
            if stop_listening is not None:
                try:
                    stop_listening(wait_for_stop=True)
                except Exception:
                    pass


class SpeechPlaybackWorker(QThread):
    """Play local Windows TTS using modern OneCore voices, with a legacy SAPI fallback."""
    stepStarted = pyqtSignal(int, object)
    playbackFinished = pyqtSignal()
    failed = pyqtSignal(str)

    def __init__(self, steps: list[dict], voice_language: str = "ar-EG"):
        super().__init__()
        self.steps = [dict(x) for x in (steps or []) if isinstance(x, dict)]
        self.voice_language = str(voice_language or "ar-EG")
        self._cancel_event = threading.Event()
        self._process = None
        self._process_lock = threading.Lock()

    def cancel(self):
        self._cancel_event.set()
        with self._process_lock:
            process = self._process
        if process is not None and process.poll() is None:
            try:
                process.terminate()
            except Exception:
                pass

    @staticmethod
    def _powershell_command(text_path: str, wave_path: str, language: str) -> list[str]:
        """Build a Unicode-safe PowerShell command for OneCore, then legacy SAPI.

        Modern Windows speech voices (including Narrator voices) are exposed through
        Windows.Media.SpeechSynthesis / WinRT. System.Speech only sees the older SAPI
        voice set on many Windows builds, so it is retained only as a compatibility fallback.
        PowerShell writes numeric exit codes; Python never decodes locale-dependent stderr.
        """
        text_b64 = base64.b64encode(text_path.encode("utf-8")).decode("ascii")
        wave_b64 = base64.b64encode(wave_path.encode("utf-8")).decode("ascii")
        script = (
            "$ErrorActionPreference = 'Stop'; "
            "$exitCode = 0; $synth = $null; $stream = $null; $reader = $null; $player = $null; $sapi = $null; "
            "try { "
            f"$textPath = [System.Text.Encoding]::UTF8.GetString([System.Convert]::FromBase64String('{text_b64}')); "
            f"$wavePath = [System.Text.Encoding]::UTF8.GetString([System.Convert]::FromBase64String('{wave_b64}')); "
            f"$lang = '{language}'; "
            "$text = [System.IO.File]::ReadAllText($textPath, [System.Text.Encoding]::UTF8); "
            "$winrtVoice = $null; "
            "try { "
            "Add-Type -AssemblyName System.Runtime.WindowsRuntime; "
            "[Windows.Media.SpeechSynthesis.SpeechSynthesizer, Windows.Media, ContentType = WindowsRuntime] | Out-Null; "
            "[Windows.Storage.Streams.DataReader, Windows.Storage.Streams, ContentType = WindowsRuntime] | Out-Null; "
            "$winrtVoice = [Windows.Media.SpeechSynthesis.SpeechSynthesizer]::AllVoices | Where-Object { $_.Language.ToLower().StartsWith($lang) } | Select-Object -First 1 "
            "} catch { $winrtVoice = $null }; "
            "if ($winrtVoice) { "
            "$asTaskGeneric = ([System.WindowsRuntimeSystemExtensions].GetMethods() | Where-Object { $_.Name -eq 'AsTask' -and $_.GetParameters().Count -eq 1 -and $_.GetParameters()[0].ParameterType.Name -eq 'IAsyncOperation`1' } | Select-Object -First 1); "
            "if (-not $asTaskGeneric) { throw 'WinRT async bridge unavailable' }; "
            "function Wait-WinRT($operation, $resultType) { $task = $script:asTaskGeneric.MakeGenericMethod($resultType).Invoke($null, @($operation)); $task.Wait(-1) | Out-Null; return $task.Result }; "
            "$synth = New-Object Windows.Media.SpeechSynthesis.SpeechSynthesizer; "
            "$synth.Voice = $winrtVoice; $synth.Options.SpeakingRate = 1.0; "
            "$stream = Wait-WinRT $synth.SynthesizeTextToStreamAsync($text) ([Windows.Media.SpeechSynthesis.SpeechSynthesisStream]); "
            "$reader = New-Object Windows.Storage.Streams.DataReader($stream.GetInputStreamAt(0)); "
            "Wait-WinRT $reader.LoadAsync([uint32]$stream.Size) ([uint32]) | Out-Null; "
            "$bytes = New-Object 'System.Byte[]' ([int]$stream.Size); $reader.ReadBytes($bytes); "
            "[System.IO.File]::WriteAllBytes($wavePath, $bytes); "
            "$player = New-Object System.Media.SoundPlayer($wavePath); $player.Load(); $player.PlaySync() "
            "} else { "
            "Add-Type -AssemblyName System.Speech; "
            "$sapi = New-Object System.Speech.Synthesis.SpeechSynthesizer; "
            "$legacyVoice = $sapi.GetInstalledVoices() | Where-Object { $_.Enabled -and $_.VoiceInfo.Culture.Name.ToLower().StartsWith($lang) } | Select-Object -First 1; "
            "if ($lang -eq 'ar' -and -not $legacyVoice) { $exitCode = 20 } "
            "else { if ($legacyVoice) { $sapi.SelectVoice($legacyVoice.VoiceInfo.Name) }; $sapi.Rate = 0; $sapi.Speak($text) } "
            "} "
            "} catch { $exitCode = 21 } "
            "finally { "
            "if ($player) { $player.Dispose() }; if ($reader) { $reader.Dispose() }; if ($stream) { $stream.Dispose() }; "
            "if ($synth) { $synth.Dispose() }; if ($sapi) { $sapi.Dispose() }; "
            "if (Test-Path -LiteralPath $wavePath) { Remove-Item -LiteralPath $wavePath -Force -ErrorAction SilentlyContinue } "
            "}; exit $exitCode"
        )
        encoded_script = base64.b64encode(script.encode("utf-16le")).decode("ascii")
        return [
            "powershell.exe", "-NoLogo", "-NoProfile", "-NonInteractive", "-STA",
            "-ExecutionPolicy", "Bypass", "-EncodedCommand", encoded_script,
        ]

    def run(self):
        if os.name != "nt":
            self.failed.emit("ميزة القراءة المحلية تستخدم محرك Windows Speech، وهي متاحة على Windows فقط.")
            return

        language = re.sub(r"[^a-z]", "", self.voice_language.split("-")[0].lower())[:3] or "ar"
        for index, step in enumerate(self.steps):
            if self._cancel_event.is_set():
                break
            self.stepStarted.emit(index, step)
            text_to_speak = str(step.get("say") or step.get("text") or "").strip()
            if not text_to_speak:
                continue

            # Select the speech language from the actual content rather than the mic setting.
            if re.search(r"[\u0600-\u06FF]", text_to_speak):
                speak_language = "ar"
            elif re.search(r"[A-Za-z]", text_to_speak):
                speak_language = "en"
            else:
                speak_language = language

            text_path = None
            wave_path = None
            try:
                with tempfile.NamedTemporaryFile("w", encoding="utf-8", suffix=".txt", delete=False) as handle:
                    handle.write(text_to_speak)
                    text_path = handle.name
                with tempfile.NamedTemporaryFile("wb", suffix=".wav", delete=False) as handle:
                    wave_path = handle.name

                creation_flags = getattr(subprocess, "CREATE_NO_WINDOW", 0)
                process = subprocess.Popen(
                    self._powershell_command(text_path, wave_path, speak_language),
                    stdin=subprocess.DEVNULL,
                    stdout=subprocess.DEVNULL,
                    stderr=subprocess.DEVNULL,
                    creationflags=creation_flags,
                )
                with self._process_lock:
                    self._process = process

                while process.poll() is None and not self._cancel_event.is_set():
                    time.sleep(0.05)

                if self._cancel_event.is_set() and process.poll() is None:
                    process.terminate()
                    try:
                        process.wait(timeout=1.0)
                    except Exception:
                        process.kill()
                elif process.returncode == 20:
                    raise RuntimeError(
                        "لم يعثر Windows على صوت عربي متاح للقراءة. افتح Settings > Time & language > Speech > Manage voices > Add voices، وثبّت صوتًا عربيًا مثل Hoda أو Naayf، ثم أعد تشغيل Engo."
                    )
                elif process.returncode:
                    raise RuntimeError(
                        "تعذر تشغيل محرك تحويل النص إلى كلام في Windows. تأكد أن مكونات Windows Speech تعمل، ثم جرّب إعادة تشغيل الجهاز."
                    )
            except Exception as exc:
                if not self._cancel_event.is_set():
                    self.failed.emit(str(exc) or "حدث خطأ غير متوقع أثناء تشغيل القراءة الصوتية.")
                    return
            finally:
                with self._process_lock:
                    self._process = None
                for temp_path in (text_path, wave_path):
                    if temp_path:
                        try:
                            os.unlink(temp_path)
                        except OSError:
                            pass

        if not self._cancel_event.is_set():
            self.playbackFinished.emit()


class TeachBoardPanel(QFrame):
    """Side board for the current lesson, examples, and the spoken step."""
    def __init__(self, parent=None):
        super().__init__(parent)
        self.setObjectName("teachBoard")
        self.setMinimumWidth(250)
        self.setMaximumWidth(480)
        layout = QVBoxLayout(self)
        layout.setContentsMargins(12, 10, 12, 10)
        layout.setSpacing(8)
        header = QHBoxLayout()
        title = QLabel("TEACHING BOARD")
        title.setObjectName("teachBoardTitle")
        header.addWidget(title, 1)
        self.step_label = QLabel("Ready")
        self.step_label.setObjectName("teachBoardStep")
        header.addWidget(self.step_label)
        layout.addLayout(header)
        self.lesson_title = QLabel("Teach the current page")
        self.lesson_title.setObjectName("teachBoardLesson")
        self.lesson_title.setWordWrap(True)
        layout.addWidget(self.lesson_title)
        self.spoken_note = QLabel("Open Voice & Learn to follow a live explanation, highlighted PDF regions, and board examples here.")
        self.spoken_note.setObjectName("teachBoardSpoken")
        self.spoken_note.setWordWrap(True)
        layout.addWidget(self.spoken_note)
        self.board_text = QTextBrowser()
        self.board_text.setObjectName("teachBoardText")
        self.board_text.setPlaceholderText("Examples and formulas will appear here.")
        layout.addWidget(self.board_text, 1)
        self.footer = QLabel("Page highlights move with the spoken explanation.")
        self.footer.setObjectName("teachBoardFooter")
        self.footer.setWordWrap(True)
        layout.addWidget(self.footer)

    def set_lesson(self, title: str, overview: str, board: str = ""):
        self.lesson_title.setText(str(title or "Current-page lesson"))
        self.spoken_note.setText(str(overview or "Follow each step as Engo explains it."))
        self.board_text.setPlainText(str(board or "The board will update with each step."))
        self.step_label.setText("Ready")

    def set_step(self, index: int, total: int, step: dict):
        self.step_label.setText(f"Step {index + 1}/{total}")
        self.spoken_note.setText(str(step.get("say") or ""))
        board = str(step.get("board") or "")
        label = str(step.get("label") or "Current region")
        self.board_text.setPlainText((label + "\n\n" + board).strip())
        page = step.get("page")
        if page:
            self.footer.setText(f"Following page {page}: highlighted region changes with each spoken step.")
        else:
            self.footer.setText("Follow the current explanation; this step has no reliable page rectangle.")


class GeminiLiveTutorWorker(QThread):
    """Gemini Live audio session with strict push-to-talk, page focus and a Markdown board."""
    status = pyqtSignal(str)
    transcript = pyqtSignal(str, str)  # speaker, incremental text
    board_update = pyqtSignal(str, str)
    # Explicit board operations let Engo append, replace/edit, or clear the live Markdown board.
    board_command = pyqtSignal(str, str, str)  # mode, title, content
    focus_requested = pyqtSignal(int, object, str, str, str)
    # Compatibility signal for the current UI. The legacy tutor deliberately does not
    # clear focus between turns; focus stays on the item until a new item is focused.
    focus_clear_requested = pyqtSignal()
    teacher_arrow_requested = pyqtSignal(str, int, object, object, str)
    page_navigation_requested = pyqtSignal(str, int)  # target: next/previous/first/last/number, one-based page number
    failed = pyqtSignal(str)

    def __init__(self, api_key: str, model: str, pdf_path: str, page_index: int,
                 page_text: str, page_image: bytes, voice_name: str = "Orus",
                 speaking_style: str = "egyptian", initial_board_markdown: str = "",
                 lesson_detail: str = "detailed", teacher_instructions: str = "",
                 secondary_document: dict | None = None):
        super().__init__()
        self.api_key = str(api_key or "")
        self.model = str(model or "gemini-3.8-live")
        self.pdf_path = os.path.abspath(pdf_path)
        self.page_index = int(page_index)
        self.page_text = str(page_text or "")[:16000]
        self.page_image = bytes(page_image or b"")
        self.secondary_document = dict(secondary_document or {})
        self.secondary_pdf_path = os.path.abspath(str(self.secondary_document.get("path") or "")) if self.secondary_document.get("path") else ""
        self.secondary_page_index = max(0, int(self.secondary_document.get("page_index", 0) or 0))
        self.secondary_page_text = str(self.secondary_document.get("text") or "")[:16000]
        self.secondary_page_image = bytes(self.secondary_document.get("image") or b"")
        self.secondary_page_count = max(1, int(self.secondary_document.get("page_count", 1) or 1))
        self.secondary_page_layout: list[dict] = []
        self.document_roadmap = ""
        self.roadmap_contact_sheet: bytes | None = None
        self.current_page_layout: list[dict] = []
        self.voice_name = str(voice_name or "Orus")
        self.speaking_style = str(speaking_style or "egyptian")
        self.lesson_detail = str(lesson_detail or "detailed").lower()
        if self.lesson_detail not in {"brief", "detailed"}:
            self.lesson_detail = "detailed"
        self.teacher_instructions = str(teacher_instructions or "").strip()[:4000]
        self._board_markdown = str(initial_board_markdown or "")[:24000]
        # Tracks the most recent learner instruction so a model tool-call cannot erase notes merely because a new session/page starts.
        self._latest_user_text = ""
        self._text_message_queue: queue.Queue[str] = queue.Queue()
        self._stop_event = threading.Event()
        self._pause_event = threading.Event()
        self._resume_event = threading.Event()
        self._model_turn_active = threading.Event()
        self._paused_turn_done = threading.Event()
        self._assistant_text_lock = threading.Lock()
        self._assistant_turn_text = ""
        self._paused_resume_excerpt = ""
        # The microphone device may stay initialized, but captured audio is discarded unless
        # Space/the talk button is held. This prevents Gemini's own speaker audio from looping back.
        self._ptt_event = threading.Event()
        self._ptt_commands: queue.Queue[bool] = queue.Queue()
        self._mic_queue: queue.Queue[bytes] = queue.Queue(maxsize=48)
        # Keep only a short audio buffer. A huge queue made follow-up turns feel delayed
        # because audio could be generated far ahead of what the user had actually heard.
        # Backpressure still prevents dropping PCM chunks and chopping sentences.
        self._speaker_queue: queue.Queue[bytes] = queue.Queue(maxsize=12)
        # Track queued and currently playing voice output so the UI can clear focus
        # only after the spoken explanation has actually finished.
        self._speaker_playing_event = threading.Event()
        self._page_update_queue: queue.Queue[tuple[int, str, bytes, str | None]] = queue.Queue(maxsize=4)
        self._secondary_page_update_queue: queue.Queue[tuple[int, str, bytes, int]] = queue.Queue(maxsize=2)
        # Compact memory of pages already visited in this live conversation, so follow-up
        # questions can refer to prior explanations even after the visible page changes.
        self._visited_page_memory: list[dict[str, str | int]] = []
        self._pending_page_image: bytes | None = None
        self._pending_secondary_page_image: bytes | None = None
        self._page_lock = threading.Lock()
        self._output_error_reported = False
        self._input_stream = None
        self._speaker_thread = None
        self._auto_lesson_active = False
        self._auto_lesson_turns = 0
        self._max_auto_lesson_turns = 64
        self._lesson_focus_count = 0
        self._lesson_board_count = 0
        self._last_focus_box: list[float] | None = None
        self._last_focus_label = ""
        self._last_focus_center_y: float | None = None
        self._focus_history: list[dict] = []
        self._explicit_focus_jump = threading.Event()
        # Separate question turns from completion of the automatic page lesson.
        self._user_question_pending = False
        self._resume_after_question = False
        self._manual_target_lock = threading.Lock()
        self._manual_target: dict | None = None
        # Snapshot the user's manually drawn area for the next spoken/typed question.
        # This must survive the live API's turn-complete event until its focus tool call
        # is validated; otherwise the model can replace the user's exact selection.
        self._active_manual_question_target: dict | None = None
        self._manual_context_dirty = threading.Event()
        # Comprehension gate: wait at meaningful problem/section boundaries and once at page end,
        # not after every formula, algebra line, or focus target.
        self._understanding_state = "teaching"  # teaching / awaiting_confirmation / awaiting_clarification / reexplaining / confirmed / completed
        self._understanding_reply_active = False
        self._understanding_reply_origin = ""
        self._understanding_reply_buffer = ""
        self._pending_typed_comprehension_guidance = ""
        self._page_final_check_asked = False
        self._page_understanding_confirmed = False
        self._page_lesson_completed = False

    @staticmethod
    def _looks_like_direct_focus_request(text: str) -> bool:
        """Detect explicit requests to inspect a particular page item, for validation only."""
        value = re.sub(r"\s+", " ", str(text or "").casefold()).strip()
        cues = (
            "اشرح المعادلة", "اشرح الحل", "اشرح المسألة", "اشرح السؤال", "اشرح الرسم", "اشرح الصورة",
            "اشرح الجدول", "اشرح الجزء", "اشرح المثال", "اشرح الفقرة", "وضح المعادلة", "وضح الحل",
            "الحاجة اللي", "الجزء اللي", "السطر اللي", "المعادلة اللي", "الرسم اللي", "الصورة اللي",
            "اللي فوق", "اللي تحت", "في أعلى", "في اسفل", "في أسفل", "في آخر الصفحة", "اول المعادلة",
            "السؤال رقم", "المسألة رقم", "المثال رقم", "المعادلة رقم", "روح للمعادلة", "حددلي",
            "point to", "focus on", "show me the", "where is the", "explain the equation", "explain the solution",
            "explain the problem", "explain question", "the diagram", "the chart", "the graph", "the figure",
            "the image", "the paragraph", "the formula", "the part above", "the part below", "specific item",
        )
        return any(cue in value for cue in cues)

    @staticmethod
    def _board_clear_requested(text: str) -> bool:
        value = re.sub(r"\s+", " ", str(text or "").casefold()).strip()
        cues = (
            "امسح البورد", "امسح كل البورد", "امسح كل الملاحظات", "فضي البورد", "افرغ البورد",
            "احذف ملاحظات البورد", "امسح الملاحظات", "clear the board", "clear all board notes",
            "erase the board", "delete all board notes",
        )
        return any(cue in value for cue in cues)

    @staticmethod
    def _board_rewrite_requested(text: str) -> bool:
        value = re.sub(r"\s+", " ", str(text or "").casefold()).strip()
        cues = (
            "اعد كتابة البورد", "أعد كتابة البورد", "استبدل البورد", "اختصر البورد", "لخص البورد",
            "رتب البورد من جديد", "رتب البورد كله", "اعمل اعادة تنظيم للبورد", "صحح البورد كله",
            "rewrite the board", "replace the board", "rewrite all board notes", "shorten the whole board",
            "summarize the whole board", "reorganize the board", "rewrite the entire board",
        )
        return any(cue.casefold() in value for cue in cues)

    @staticmethod
    def _classify_understanding_reply(text: str) -> str:
        """Return yes/no/clarification for a pending comprehension check."""
        value = re.sub(r"\s+", " ", str(text or "").casefold()).strip()
        if not value:
            return "unclear"
        negative_patterns = (
            r"(^|[\s،,.!?؛])(?:لا|لأ|لأه|مش فاهم(?:ة)?|مش واضح|مش مستوعب|ما فهمتش|مافهمتش|لم أفهم|"
            r"not understand|don't understand|do not understand|don't get it|do not get it|no|nope)(?=$|[\s،,.!?؛])",
        )
        is_negative = any(re.search(pattern, value) for pattern in negative_patterns)
        if is_negative:
            detail_cues = (
                "ازاي", "إزاي", "ليه", "لماذا", "خطوة", "الخطوة", "الجزء", "الحته", "الحته", "المعادلة",
                "الحساب", "المقصود", "معنى", "الرمز", "الرقم", "اللي", "because", "how", "why", "step", "part", "formula", "equation", "mean",
            )
            return "clarification" if any(cue in value for cue in detail_cues) or len(value.split()) >= 6 else "no"
        positive_pattern = (
            r"(^|[\s،,.!?؛])(?:آه|اه|ايوه|أيوه|أيوة|ايوة|نعم|تمام|ماشي|كمل|كمّل|اكمل|أكمل|فاهم|فاهمة|فهمت|واضح|"
            r"yes|yeah|yep|understood|got it|i understand)(?=$|[\s،,.!?؛])"
        )
        if re.search(positive_pattern, value):
            return "yes"
        return "clarification"

    def _begin_understanding_reply(self):
        state = str(getattr(self, "_understanding_state", "teaching"))
        self._understanding_reply_active = state in {"awaiting_confirmation", "awaiting_clarification"}
        self._understanding_reply_origin = state if self._understanding_reply_active else ""
        self._understanding_reply_buffer = ""

    def _apply_understanding_reply(self, text: str, *, cumulative: bool = False):
        """Update the comprehension gate from typed text or live input transcription."""
        if not text:
            return
        if cumulative:
            self._understanding_reply_buffer = (self._understanding_reply_buffer + " " + str(text)).strip()[-1600:]
            value = self._understanding_reply_buffer
            origin = self._understanding_reply_origin
        else:
            origin = str(getattr(self, "_understanding_state", "teaching"))
            value = str(text).strip()
        if origin == "awaiting_confirmation":
            decision = self._classify_understanding_reply(value)
            if decision == "yes":
                self._understanding_state = "confirmed"
                if self._page_final_check_asked:
                    self._page_understanding_confirmed = True
                self._auto_lesson_active = True
            elif decision == "no":
                self._understanding_state = "awaiting_clarification"
                self._page_understanding_confirmed = False
                self._auto_lesson_active = True
            else:
                self._understanding_state = "reexplaining"
                self._page_understanding_confirmed = False
                self._auto_lesson_active = True
        elif origin == "awaiting_clarification":
            # The learner is now identifying the confusing point; explain that point
            # differently, then ask the comprehension question again.
            self._understanding_state = "reexplaining"
            self._page_understanding_confirmed = False
            self._auto_lesson_active = True

    def _comprehension_turn_guidance(self) -> str:
        state = str(getattr(self, "_understanding_state", "teaching"))
        if state == "awaiting_confirmation":
            if self._page_final_check_asked:
                return (
                    "FINAL WHOLE-PAGE COMPREHENSION RESPONSE: The learner is answering your separate question about whether the WHOLE PAGE is understood. "
                    "If they clearly say yes, give a brief final recap and call finish_page_lesson now; do not move to another lesson item. "
                    "If they say no, ask which exact part of the page is still unclear and WAIT. Re-explain that part, ask the whole-page check again, and wait."
                )
            return (
                "COMPREHENSION RESPONSE: The learner is answering your last 'did you understand?' check. "
                "If they clearly say yes/understood, immediately move to the next not-yet-covered meaningful part/problem. "
                "If they say no or do not understand, ask what exact point is unclear and WAIT; do not move on. "
                "If they name the confusing point directly, explain that exact point again in a simpler/different way, then ask whether it is clear and WAIT again."
            )
        if state == "awaiting_clarification":
            return (
                "THE LEARNER IS ABOUT TO IDENTIFY THE STICKING POINT: They already said they did not understand, "
                "and you have asked what is unclear. Listen carefully to the exact point they are about to name. "
                "Do not ask them again what is unclear; explain the point they identify in a simpler/different way, "
                "then ask whether it is clear now and WAIT. Do not move to the next lesson item."
            )
        if state == "reexplaining":
            return (
                "RE-EXPLAIN THE STICKING POINT: The learner has identified what is unclear. Focus on that exact point, "
                "explain it again with a different, simpler explanation and a concrete small example if useful. "
                "Then ask if this explanation is clear now and WAIT for an explicit yes before advancing."
            )
        if state == "confirmed":
            if self._page_understanding_confirmed:
                return (
                    "WHOLE PAGE UNDERSTANDING CONFIRMED: The learner explicitly confirmed that the entire page is clear. "
                    "Give a concise final recap and call finish_page_lesson now. Do not teach another item."
                )
            return (
                "UNDERSTANDING CONFIRMED: The learner clearly said they understand. Continue with the next uncovered part/problem now. "
                "Do not repeat the previous explanation. Continue through the whole next problem or clearly labeled part without interrupting its internal steps; ask whether it is understood only when that complete unit is finished, before moving to a different one."
            )
        return (
            "The learner is asking a normal question/interruption. Answer it first. Do not mark the page complete because a question was answered. "
            "Resume the lesson only when it is appropriate or the learner confirms understanding and wants to continue."
        )

    @staticmethod
    def _is_page_comprehension_question(text: str) -> bool:
        value = re.sub(r"\s+", " ", str(text or "").casefold()).strip()
        cues = (
            "الصفحة كلها", "كل الصفحة", "الصفحة بالكامل", "كل اللي في الصفحة", "كل ما في الصفحة",
            "خلصنا الصفحة", "انتهينا من الصفحة", "شرح الصفحة خلص", "غطينا الصفحة", "كل اللي شرحناه",
            "الدرس كله", "everything on the page", "whole page", "entire page", "finished the page",
            "covered the full page", "whole lesson",
        )
        return any(cue in value for cue in cues)

    def cancel(self):
        self._ptt_event.clear()
        self._pause_event.clear()
        self._resume_event.clear()
        self._stop_event.set()

    @staticmethod
    def _last_spoken_point(text: str) -> str:
        value = re.sub(r"\s+", " ", str(text or "")).strip()
        if not value:
            return "the last point you were explaining"
        parts = re.split(r"(?<=[.!?؟。])\s+", value)
        candidate = next((part.strip() for part in reversed(parts) if part.strip()), value)
        return candidate[-420:]

    def _remember_assistant_transcript(self, text: str):
        with self._assistant_text_lock:
            self._assistant_turn_text = (self._assistant_turn_text + " " + str(text or "")).strip()[-6000:]

    def _begin_model_turn(self):
        """Mark an outbound tutor turn before its first audio/text frame arrives."""
        self._model_turn_active.set()
        self._paused_turn_done.clear()
        with self._assistant_text_lock:
            self._assistant_turn_text = ""

    def set_paused(self, paused: bool):
        """Pause speech output without ending the Gemini session; resume from its last spoken point."""
        paused = bool(paused) and not self._stop_event.is_set()
        if paused:
            with self._assistant_text_lock:
                self._paused_resume_excerpt = self._last_spoken_point(self._assistant_turn_text)
            self._resume_event.clear()
            self._paused_turn_done.clear()
            if not self._model_turn_active.is_set():
                self._paused_turn_done.set()
            self._pause_event.set()
            self._clear_queue(self._speaker_queue)
            self.status.emit("Lesson paused · the live session is still connected")
        else:
            if self._pause_event.is_set():
                # Keep audio output muted until the in-flight Gemini turn reaches its
                # boundary. send_loop clears this only when it is safe to request the repeat.
                self._resume_event.set()
                self.status.emit("Resuming · waiting for the current audio turn, then repeating the last point")

    def send_typed_message(self, text: str):
        """Queue a typed user message for the live session; it uses the same context/tools as speech."""
        text = str(text or "").strip()
        if text and not self._stop_event.is_set() and not self._pause_event.is_set():
            self._latest_user_text = text[:8000]
            previous_understanding_state = str(self._understanding_state)
            self._pending_typed_comprehension_guidance = ""
            self._apply_understanding_reply(text, cumulative=False)
            if previous_understanding_state == "awaiting_confirmation" and self._understanding_state == "awaiting_clarification":
                self._pending_typed_comprehension_guidance = (
                    "The learner just answered NO to the comprehension check. Ask exactly what part is unclear, "
                    "then stop and wait. Do not move to the next part."
                )
            elif previous_understanding_state == "awaiting_confirmation" and self._understanding_state == "reexplaining":
                self._pending_typed_comprehension_guidance = self._comprehension_turn_guidance()
            elif previous_understanding_state == "awaiting_clarification":
                self._pending_typed_comprehension_guidance = self._comprehension_turn_guidance()
            elif self._understanding_state == "confirmed":
                self._pending_typed_comprehension_guidance = self._comprehension_turn_guidance()
            self._user_question_pending = True
            self._resume_after_question = False
            value = text.casefold()
            resume_cues = ("continue the lesson", "resume the lesson", "كمّل الشرح", "كمل الشرح", "اكمل الشرح", "كمّل الدرس", "كمل الدرس", "كمل من حيث وقفنا")
            manual = self._get_manual_target()
            with self._manual_target_lock:
                self._active_manual_question_target = (dict(manual) if manual and int(manual.get("page_index", -1)) == int(self.page_index) and not any(cue.casefold() in value for cue in resume_cues) else None)
            if any(cue in value for cue in resume_cues):
                self._auto_lesson_active = True
            self._text_message_queue.put(text[:8000])

    def set_manual_target(self, page_index: int, box, crop_image: bytes):
        """Register a user-drawn region. It stays active until changed or cleared."""
        try:
            vals = [max(0.0, min(1.0, float(v))) for v in box]
            if len(vals) != 4 or vals[2] <= 0 or vals[3] <= 0:
                return False
            vals[2] = min(vals[2], 1.0 - vals[0])
            vals[3] = min(vals[3], 1.0 - vals[1])
            with self._manual_target_lock:
                self._manual_target = {"page_index": int(page_index), "box": vals, "image": bytes(crop_image or b""), "label": "manual selection"}
            self._manual_context_dirty.set()
            return True
        except Exception:
            return False

    def clear_manual_target(self):
        with self._manual_target_lock:
            self._manual_target = None
            self._active_manual_question_target = None
        self._manual_context_dirty.set()

    def _get_manual_target(self):
        with self._manual_target_lock:
            return dict(self._manual_target) if self._manual_target else None

    def _get_active_manual_question_target(self):
        with self._manual_target_lock:
            return dict(self._active_manual_question_target) if self._active_manual_question_target else None

    def set_push_to_talk(self, active: bool):
        """Enable microphone transmission only during a physical Space/button hold."""
        active = bool(active) and not self._stop_event.is_set() and not self._pause_event.is_set()
        if active:
            self._user_question_pending = True
            self._resume_after_question = False
            manual = self._get_manual_target()
            with self._manual_target_lock:
                self._active_manual_question_target = (dict(manual) if manual and int(manual.get("page_index", -1)) == int(self.page_index) else None)
            self._clear_queue(self._mic_queue)
            # Stop queued playback before accepting an interruption, so the mic is less likely
            # to recapture the tutor's own previous words from the speakers.
            self._clear_queue(self._speaker_queue)
            self._ptt_event.set()
        else:
            self._ptt_event.clear()
        self._ptt_commands.put(active)

    def update_page_context(self, page_index: int, page_text: str, page_image: bytes, board_markdown: str | None = None):
        """Queue the visible PDF page and its page-specific board into the current live session."""
        item = (int(page_index), str(page_text or "")[:16000], bytes(page_image or b""),
                None if board_markdown is None else str(board_markdown or "")[:24000])
        try:
            self._page_update_queue.put_nowait(item)
        except queue.Full:
            try:
                self._page_update_queue.get_nowait()
            except queue.Empty:
                pass
            try:
                self._page_update_queue.put_nowait(item)
            except queue.Full:
                pass

    def update_secondary_page_context(self, page_index: int, page_text: str, page_image: bytes, page_count: int = 1):
        if not self.secondary_pdf_path:
            return
        item = (int(page_index), str(page_text or "")[:16000], bytes(page_image or b""), max(1, int(page_count or 1)))
        try:
            self._secondary_page_update_queue.put_nowait(item)
        except queue.Full:
            try:
                self._secondary_page_update_queue.get_nowait()
            except queue.Empty:
                pass
            try:
                self._secondary_page_update_queue.put_nowait(item)
            except queue.Full:
                pass

    @staticmethod
    def _tool_declarations():
        return [{"function_declarations": [
            {
                "name": "write_to_board",
                "description": "Operate Engo's visible Markdown teaching board. Use mode=append to add the next concise lesson note, example, equation, Markdown table, or recap; mode=replace to edit/rewrite the current board in response to a user request; mode=clear to clear it only when the user explicitly asks. The current board content is included in your instructions, so preserve material unless asked to change it.",
                "parameters": {
                    "type": "OBJECT",
                    "properties": {
                        "mode": {"type": "STRING", "enum": ["append", "replace", "clear"], "description": "append for a new section, replace to edit the whole board, clear to erase it when requested."},
                        "title": {"type": "STRING", "description": "Short heading for the board section or board title."},
                        "content": {"type": "STRING", "description": "Markdown content: explanations, equations, examples, lists, or tables. Empty only when mode=clear."}
                    },
                    "required": ["mode", "title", "content"]
                }
            },
            {
                "name": "focus_page_region",
                "description": "Highlight the exact item you are CURRENTLY explaining on the full page. Use selectable-text geometry when the visible wording matches a supplied text block. page is the current one-based page. box is [LEFT, TOP, WIDTH, HEIGHT], normalized 0..1 for the full page. kind must classify what the item actually is: ordinary printed writing, handwriting, equation, problem text, worked solution, table, diagram/drawing, chart/graph, or photo/image. Handwritten WORDS are still handwriting/text, not a picture. Use diagram/chart/photo only for genuine visual content, including hand-drawn diagrams. If the learner specifically asks about an item or named area, jump directly to it regardless of reading order and set user_requested_target=true. During automatic lessons, stay in top-to-bottom order. Use a tight box around the item itself; allow taller boxes for a multi-line worked solution, but never a full-page or mostly blank box.",
                "parameters": {
                    "type": "OBJECT",
                    "properties": {
                        "source": {"type": "STRING", "enum": ["primary", "supplementary"], "description": "Which displayed PDF page to focus. Use supplementary when the target is on the companion document."},
                        "page": {"type": "INTEGER", "description": "One-based page number within the chosen source PDF."},
                        "box": {"type": "ARRAY", "items": {"type": "NUMBER"}, "description": "Normalized [x,y,width,height] rectangle, each value from 0 to 1."},
                        "label": {"type": "STRING", "description": "Short description of the exact content in the region, preferably the actual wording or specific item name."},
                        "kind": {"type": "STRING", "enum": ["text", "handwriting", "equation", "problem", "solution", "table", "diagram", "chart", "photo", "image", "figure", "graph", "plot", "drawing", "other"], "description": "Semantic item type. Handwritten text belongs to handwriting; a hand-drawn chart or sketch belongs to diagram/chart."},
                        "user_requested_target": {"type": "BOOLEAN", "description": "True when responding to a specific learner request to explain/focus a named or non-next item; this allows jumping to it."}
                    },
                    "required": ["source", "page", "box", "label", "kind", "user_requested_target"]
                }
            },
            {
                "name": "navigate_pdf_page",
                "description": "Navigate the actual PDF viewer when the learner explicitly asks to go to another page, the next/previous page, the first/last page, or a specific page number. Do not merely say you will navigate; call this tool. If the learner asks about the previous page's content without asking to navigate, answer from the prior-page conversation memory instead.",
                "parameters": {
                    "type": "OBJECT",
                    "properties": {
                        "target": {"type": "STRING", "enum": ["next", "previous", "first", "last", "number"], "description": "Navigation target requested by the learner."},
                        "page_number": {"type": "INTEGER", "description": "One-based page number, required only when target=number."}
                    },
                    "required": ["target"]
                }
            },
            {
                "name": "finish_page_lesson",
                "description": "Call only after all page content has been taught AND the learner has explicitly answered yes to a separate whole-page comprehension check. Never call this merely because a segment or question answer is complete.",
                "parameters": {
                    "type": "OBJECT",
                    "properties": {"summary": {"type": "STRING", "description": "Short final recap of the completed page."}},
                    "required": ["summary"]
                }
            },
            {
                "name": "resume_page_lesson",
                "description": "After answering an interruption, call this only when the question is related to the ongoing lesson and it is appropriate to resume. Do not call it for unrelated standalone questions or when the learner asks only for an answer. This does not mark the page complete.",
                "parameters": {
                    "type": "OBJECT",
                    "properties": {"reason": {"type": "STRING", "description": "Brief reason for resuming the lesson."}},
                    "required": ["reason"]
                }
            }
        ]}]

    def _read_pdf_page_layout(self, page_index: int, pdf_path: str | None = None) -> list[dict]:
        """Return normalized selectable text blocks for either linked PDF source."""
        found = []
        try:
            with fitz.open(pdf_path or self.pdf_path) as doc:
                if not len(doc):
                    return found
                page = doc.load_page(max(0, min(int(page_index), len(doc) - 1)))
                pw, ph = float(page.rect.width), float(page.rect.height)
                for block in page.get_text("blocks")[:80]:
                    if len(block) < 5:
                        continue
                    text = re.sub(r"\s+", " ", str(block[4] or "")).strip()
                    if not text:
                        continue
                    x0, y0, x1, y1 = map(float, block[:4])
                    x = max(0.0, min(1.0, x0 / max(1.0, pw)))
                    y = max(0.0, min(1.0, y0 / max(1.0, ph)))
                    w = max(0.0, min(1.0 - x, (x1 - x0) / max(1.0, pw)))
                    h = max(0.0, min(1.0 - y, (y1 - y0) / max(1.0, ph)))
                    if w > 0.01 and h > 0.003:
                        found.append({"box": [round(x, 4), round(y, 4), round(w, 4), round(h, 4)], "text": text[:180]})
        except Exception:
            return []
        return found

    def _match_layout_box(self, label: str, kind: str, excluded_boxes=None, layout_items=None):
        """Anchor text focus to a not-yet-covered PDF text block when one matches."""
        if str(kind or "text").lower() in {"manual", "diagram", "chart", "photo", "image", "figure", "graph", "plot", "drawing", "table"}:
            return None
        words = lambda text: {w.casefold() for w in re.findall(r"[A-Za-z0-9]+|[\u0600-\u06ff]+", str(text or ""))
                              if len(w) >= 3 and w.casefold() not in {
                                  "the", "and", "for", "from", "this", "that", "with", "about", "page", "text", "line", "item",
                                  "problem", "question", "equation", "solution", "diagram", "chart", "figure", "graph", "plot",
                                  "drawing", "table", "handwriting", "definition", "example", "answer", "section", "part", "area",
                                  "الموجود", "اللي", "على", "في", "من", "ده", "دي", "هذا", "هذه", "عن", "الى", "إلى",
                                  "السؤال", "المسألة", "المعادلة", "الحل", "الرسم", "رسمة", "شكل", "جدول", "مخطط", "صورة",
                                  "تعريف", "مثال", "فقرة", "الجزء", "جزء", "مسألة", "سؤال", "صفحة", "نص", "سطر"}}
        label_words = words(label)
        if len(label_words) < 2:
            return None
        best, best_score, best_hits = None, 0.0, 0
        for item in (self.current_page_layout if layout_items is None else layout_items)[:80]:
            candidate_box = item.get("box")
            if excluded_boxes and isinstance(candidate_box, (list, tuple)) and len(candidate_box) == 4:
                cx, cy, cw, ch = [float(v) for v in candidate_box]
                overlaps_used = False
                for old_box in excluded_boxes:
                    if not isinstance(old_box, (list, tuple)) or len(old_box) != 4:
                        continue
                    ox, oy, ow, oh = [float(v) for v in old_box]
                    ix1, iy1 = max(cx, ox), max(cy, oy)
                    ix2, iy2 = min(cx + cw, ox + ow), min(cy + ch, oy + oh)
                    inter = max(0.0, ix2 - ix1) * max(0.0, iy2 - iy1)
                    smaller = max(1e-6, min(cw * ch, ow * oh))
                    if inter / smaller > 0.66:
                        overlaps_used = True
                        break
                if overlaps_used:
                    continue
            block_words = words(item.get("text", ""))
            hits = len(label_words & block_words)
            score = hits / max(1, len(label_words))
            if hits > best_hits or (hits == best_hits and score > best_score):
                best, best_score, best_hits = item, score, hits
        if best is not None and best_hits >= 2 and best_score >= 0.38:
            box = best.get("box")
            if isinstance(box, (list, tuple)) and len(box) == 4:
                return [float(v) for v in box]
        return None

    @staticmethod
    def _make_focus_grid_image(image_bytes: bytes) -> bytes:
        """Faint 10% coordinate grid, so vision coordinates map to the page instead of guesswork."""
        if not image_bytes:
            return b""
        try:
            from PIL import ImageDraw, ImageFont
            im = Image.open(io.BytesIO(image_bytes)).convert("RGB")
            w, h = im.size
            draw = ImageDraw.Draw(im, "RGBA")
            try:
                font = ImageFont.truetype("arial.ttf", max(12, min(20, w // 70)))
            except Exception:
                font = ImageFont.load_default()
            for i in range(1, 10):
                x, y = round(w * i / 10), round(h * i / 10)
                draw.line((x, 0, x, h), fill=(40, 135, 220, 48), width=1)
                draw.line((0, y, w, y), fill=(40, 135, 220, 48), width=1)
                draw.text((x + 2, 2), f"{i/10:.1f}", font=font, fill=(10, 90, 180, 205), stroke_width=1, stroke_fill=(255,255,255,180))
                draw.text((2, y + 2), f"{i/10:.1f}", font=font, fill=(10, 90, 180, 205), stroke_width=1, stroke_fill=(255,255,255,180))
            buff = io.BytesIO()
            im.save(buff, format="JPEG", quality=88, optimize=True)
            return buff.getvalue()
        except Exception:
            return image_bytes

    def _prepare_document_roadmap(self):
        """Read the first up-to-10 pages before teaching and make a labeled visual overview sheet."""
        roadmap_parts = []
        thumbs = []
        self.current_page_layout = self._read_pdf_page_layout(self.page_index)
        if self.secondary_pdf_path:
            self.secondary_page_layout = self._read_pdf_page_layout(self.secondary_page_index, self.secondary_pdf_path)
        try:
            with fitz.open(self.pdf_path) as doc:
                page_total = len(doc)
                n = min(10, page_total)
                for i in range(n):
                    page = doc.load_page(i)
                    text = re.sub(r"\s+", " ", str(page.get_text("text") or "")).strip()
                    if text:
                        roadmap_parts.append(f"PAGE {i + 1}: {text[:1250]}")
                    else:
                        roadmap_parts.append(f"PAGE {i + 1}: no selectable text; inspect its scanned/image content in the visual overview.")
                    # Compact thumbnail only for global topic/sequence recognition; never use it for focus coordinates.
                    scale = min(0.58, 270.0 / max(float(page.rect.width), 1.0), 340.0 / max(float(page.rect.height), 1.0))
                    pix = page.get_pixmap(matrix=fitz.Matrix(scale, scale), alpha=False)
                    thumb = Image.frombytes("RGB", (pix.width, pix.height), pix.samples)
                    thumb.thumbnail((270, 330), Image.Resampling.LANCZOS)
                    thumbs.append((i + 1, thumb.copy()))
        except Exception as exc:
            roadmap_parts.append(f"Document roadmap could not be prepared: {exc}")
        self.document_roadmap = "\n\n".join(roadmap_parts)[:14000]
        if thumbs:
            try:
                tile_w, tile_h, label_h = 290, 370, 30
                cols = 2
                rows = math.ceil(len(thumbs) / cols)
                sheet = Image.new("RGB", (cols * tile_w, rows * tile_h), "#dfe4eb")
                from PIL import ImageDraw, ImageFont
                draw = ImageDraw.Draw(sheet)
                try:
                    font = ImageFont.truetype("arial.ttf", 16)
                except Exception:
                    font = ImageFont.load_default()
                for idx, (page_num, thumb) in enumerate(thumbs):
                    x = (idx % cols) * tile_w
                    y = (idx // cols) * tile_h
                    draw.rectangle((x, y, x + tile_w - 1, y + tile_h - 1), fill="white", outline="#8793a4", width=1)
                    draw.rectangle((x, y, x + tile_w - 1, y + label_h), fill="#25334b")
                    draw.text((x + 10, y + 6), f"Document overview · page {page_num}", fill="white", font=font)
                    xx = x + (tile_w - thumb.width) // 2
                    yy = y + label_h + 5 + (tile_h - label_h - thumb.height) // 2
                    sheet.paste(thumb, (xx, yy))
                buff = io.BytesIO()
                sheet.save(buff, format="JPEG", quality=72, optimize=True)
                self.roadmap_contact_sheet = buff.getvalue()
            except Exception:
                self.roadmap_contact_sheet = None

        # Keep the return contract in sync with the caller in _run_live().
        # Previously this function only populated instance fields and returned None,
        # causing: "cannot unpack non-iterable NoneType object" before voice startup.
        return self.document_roadmap, self.roadmap_contact_sheet

    def _system_instruction(self) -> str:
        with self._page_lock:
            current_page_index = self.page_index
            current_page_text = self.page_text
        manual = self._get_manual_target()
        manual_instruction = ""
        if manual and int(manual.get("page_index", -1)) == current_page_index:
            mb = manual.get("box", [0, 0, 1, 1])
            manual_instruction = (
                f"\nMANUAL SELECTION ACTIVE on page {current_page_index + 1}, normalized box "
                f"[left={mb[0]:.3f}, top={mb[1]:.3f}, width={mb[2]:.3f}, height={mb[3]:.3f}]. "
                "A close-up image of this exact region was supplied. If the learner asks about the selected area, address it first rather than choosing the next region in sequence. "
                "Do not move the focus box away from the manual selection unless the learner asks for a different target or automatic lesson resumption is explicitly appropriate.\n"
            )
        dialect_instructions = {
            "egyptian": "Speak in natural everyday Egyptian Arabic (Masri / اللهجة المصرية), like a patient Egyptian university tutor. Use familiar Egyptian phrasing such as 'خلينا نفهم' and 'بص' where appropriate, while preserving technical terms and mathematical accuracy. Avoid formal MSA unless a technical definition needs it.",
            "msa": "Speak in clear Modern Standard Arabic (العربية الفصحى) with a calm teaching voice, preserving technical terms and mathematical accuracy.",
            "auto": "Match the learner's spoken language and dialect naturally. If they speak Arabic, answer in the same Arabic dialect where possible.",
        }
        dialect_instruction = dialect_instructions.get(self.speaking_style, dialect_instructions["egyptian"])
        if self.lesson_detail == "brief":
            detail_instruction = (
                "SESSION MODE: QUICK REVIEW. This is revision, not a first-time full lecture. Rapidly retrieve the central definitions, formulas, links and likely exam traps; explain each in a compact way, use one tiny example or memory cue where valuable. Keep the explanation flowing through all steps that belong to the same problem or sub-question. Ask for understanding only at a real boundary: after finishing a complete problem, a clearly separate labeled part (such as a/b), or a distinct topic/section before moving to the next one. Never interrupt for each formula, line, calculation, paragraph, or focus target. Still scan the entire page and do not omit any important formula, worked result, diagram or conclusion. Use roughly 3-6 focus targets depending on page density, and finish with one concise whole-page check and recap."
            )
        else:
            detail_instruction = (
                "LESSON DETAIL: DETAILED TEACHING. Behave like an excellent private teacher, not a narrator. Build understanding in a repeatable cycle: (1) identify and accurately read the key statement/term, (2) explain it in simple language, (3) explain WHY it is true or useful and HOW it connects to the previous idea, (4) demonstrate a worked example or practical application, (5) ask one short retrieval question when suitable, then correct/reinforce the learner's answer, and (6) give a memorable cue or analogy. For equations and worked problems, explain every meaningful symbol, assumption, transformation, unit and step; never jump over algebra, and explain the entire chain of steps in one uninterrupted flow. Treat the steps within one problem as a single teaching unit; pause for an understanding check only after the complete problem or a clearly separate labeled sub-question has been fully explained, before moving to the next problem/part/topic. Explain every relevant diagram/chart/table, axes, labels, arrows, relationships and conclusions. Cover all meaningful content top-to-bottom; do not silently skip a definition, note, formula, example, caption or conclusion. Do not mechanically read whole paragraphs verbatim. Update the board with clear definitions, worked steps, examples, memory hooks and short review questions. Use enough focus targets to cover the actual page density, usually 5-10 or more when needed. Never invent illegible content; say exactly what is unclear. At the end, ask one separate whole-page understanding check and WAIT for a clear yes; only then give a concise recap and mark the page complete."
            )
        instruction = (
            "You are Engo, a real-time voice teacher inside a desktop PDF viewer. The user expects you to teach the WHOLE currently displayed PDF page automatically, from the top to the bottom, not merely the currently highlighted crop. "
            "Introduce yourself as Engo only once when this live conversation first starts. Never introduce yourself again merely because the learner moved to another PDF page, asked a follow-up, or resumed the lesson. Keep the same conversation identity across all pages until the session is ended and a genuinely new session starts. "
            "When Engo sends the explicit start-page-lesson prompt, begin with the first meaningful section/problem on the page. Explain a complete problem or labeled sub-question continuously, including all of its internal steps, without stopping to ask after every small step or focus target. Ask the learner whether it is understood only after finishing that complete problem/part or a distinct section/topic, just before moving to a different one. Cover every important section, paragraph, equation, table, chart and figure. Use navigate_pdf_page for explicit page-change commands. Remember prior spoken turns and the recent-page memory for follow-up questions about earlier pages. "
            "The user may interrupt at any time by holding Space or typing a question. Treat the question as a separate task; do not infer that answering it completes the page. If the question belongs to the lesson and continuation makes sense, call resume_page_lesson after the answer; otherwise wait. When all page content has been taught, ask a separate whole-page understanding question and WAIT; call finish_page_lesson only after a clear affirmative reply. Never answer silence or a page update alone.\n\n"
            f"{dialect_instruction}\n{detail_instruction}\nSpeak naturally at a teaching pace. Teach the ideas rather than merely reading the page word-for-word. Do not assume a selected rectangle limits the lesson; the full page image and page text are your scope.\n\n"
            "COMPREHENSION CHECK LOOP (MANDATORY, BUT NOT AFTER EVERY SMALL STEP): Keep one complete problem together. While solving it, explain its setup, formulas, substitutions, calculations, algebra, and conclusion in a continuous flow; do NOT ask whether the learner understands after each line, equation, transformation, paragraph, or focus-rectangle move. If a question has clearly labeled independent parts (for example a, b, c), finish one whole labeled part before asking; then wait before starting the next labeled part. Likewise, finish a complete problem or a distinct section/concept before asking and moving to another problem/topic/section. Use natural Egyptian Arabic for one brief check, such as 'كده المسألة/الجزء ده واضح؟'. Then STOP and WAIT. If the learner says yes, proceed to the next complete unit. If they say no, ask which exact point is unclear, wait, and re-explain only that point differently with a small example; check again after the re-explanation. Do not repeat the check during the same uninterrupted explanation. At the end of all page content, ask one separate page-wide check (for example 'كده الصفحة كلها بقت واضحة؟') and WAIT. Only after an explicit yes to that final page-wide check may you call finish_page_lesson. Never say the page/lesson is complete before that confirmation.\n\n"
            "VOICE LESSON VISUAL POLICY: During voice lessons, NEVER draw or request arrows, pointers, marks, captions, text boxes, or other page annotations. Use ONLY the movable focus rectangle to show the item currently being explained.\n\n"
            "TRANSCRIPT FORMATTING: Write every textual answer and teaching explanation as clean, valid GitHub-Flavored Markdown so the Engo transcript can render it (ordinary paragraphs are valid Markdown). Use **bold** for important terms, headings and bullets only when useful, and numbered lists for ordered steps. Format equations with readable mathematical notation; never expose raw formatting characters such as unmatched underscores, asterisks, dollar-sign math delimiters, or backticks as decoration. Do not say Markdown symbols aloud. Keep the spoken explanation natural and make the displayed text concise and readable.\n\n"
                "VISUAL FOCUS: The current full-page image may have a faint 10%-coordinate grid. Every box maps to the full current page, not the overview montage. If selectable text-block geometry is supplied, use the exact matching box for printed text/equations instead of guessing. First classify the semantic content: printed text and handwritten words/equations are text; a handwritten sketch, plotted chart, diagram, photo or real graphic is visual content. Visual graphics use a cyan rectangle, worked solutions use green, and all writing (including handwriting) uses amber. No laser dot or floating caption is shown. Do not draw arrows or any other page markup during the voice lesson; use only the focus rectangle. AUTOMATIC LESSON: plan in top-to-bottom reading order and cover all important items. MANDATORY FOCUS SYNCHRONIZATION: before you start explaining every new distinct paragraph, equation, worked-solution step, table, chart, or diagram, call focus_page_region for that exact item; wait for the tool result before speaking about it. When your explanation moves to a different item, move the rectangle first. Never keep the old rectangle displayed while explaining a new item, and never move it repeatedly without matching your spoken explanation. Use a box around the complete meaningful content, not a tiny token or a single handwritten glyph. For handwriting, include the full handwritten line, complete equation, or complete worked-solution step with modest margins; do not split one handwritten line into tiny boxes and do not guess based on a small ink fragment. A handwriting focus box must cover a readable phrase/line (normally at least about 15% of page width unless the actual item is visibly shorter) and must include ascenders, descenders, and punctuation. Before focusing a new item, verify it is a genuinely different target; after its explanation/audio finishes, release that rectangle before advancing unless the next target is already ready. Recheck the target against the page image and grid before every focus call. For selectable printed text use the supplied PDF text-block geometry when matched. If the handwriting is faint or ambiguous, use a broader box around the whole likely line/solution and say that the handwriting is unclear rather than focusing a small incorrect mark. If you cannot identify a different target confidently, do not invent coordinates—say briefly that the visual target is uncertain and continue explaining with the best available reference. USER-DIRECTED REQUEST: if the learner asks for a specific item, question, solution, graph, diagram, equation, paragraph or named content, locate that exact item immediately even if it is above/behind the current item, call focus_page_region with user_requested_target=true, answer it, then resume the automatic lesson from the next uncovered item. Do not reject a user-directed jump as backwards or out of order. Do not use a large generic rectangle for a specific question; a multi-line solution may need a taller horizontal box, but no mostly blank/page-sized region. Do not use the overview montage for precise coordinates.\n\n"
            "TEACHING BOARD: The board is a real editable Markdown workspace available to you as a tool, not merely an automatic transcript. At the beginning, call write_to_board with mode=append for a compact outline. After each 1-2 related focus targets, add a concise note/example/equation/table. Before appending, compare against the supplied current board and NEVER repeat the same definition, equation, example, heading or paragraph. If already present, add only genuinely new information; the app also rejects duplicates. Do not create near-identical paraphrases just to increase board updates. When the learner asks you to add an example, explain something ON the board, make a table, fix a mistake, simplify, reorganize, or rewrite the notes, call write_to_board with mode=append or mode=replace as appropriate. Use mode=replace to actually edit the existing board and refer to the current board text below; use mode=clear only if the learner explicitly asks to clear it. Do not claim you changed the board unless you call the tool. Use Markdown headings, **bold**, lists, Markdown tables and `inline code`; use readable equation notation such as F = ma, x², √x, or `a/b`, not raw LaTeX delimiters.\n\n"
            "DOCUMENT ROADMAP: Before this lesson, the application reviewed the first up to 10 pages below and may provide a contact sheet of those pages. Use these pages ONLY to understand the book's subject, definitions, notation and teaching sequence. Do not teach all those pages now. The only target for this lesson is the most recently provided full-size image of the currently displayed page.\n"
            + (f"\nLINKED SUPPLEMENTARY PDF: {Path(self.secondary_pdf_path).name}, page {self.secondary_page_index + 1} of {self.secondary_page_count}. This is a SECOND source shown beside the primary page. Use it to find the answer/solution when the primary page contains the question, compare related material, and explain cross-document links. The primary page remains the main lesson path; do not confuse page numbers between files.\nSUPPLEMENTARY PAGE TEXT:\n{self.secondary_page_text[:12000]}\n" if self.secondary_pdf_path else "")
            + (self.document_roadmap or "[No extracted text was available from the first pages; use the overview sheet if present and the current-page image carefully.]") + "\n\n"
            "PAGE NAVIGATION AND RECALL: If the learner asks to go to the next page, previous page, first/last page, or a numbered page, call navigate_pdf_page with the correct target. Do not only say you will go there; use the tool so the viewer actually changes pages. If the learner asks what you explained on an earlier page, answer using your conversation memory plus the RECENTLY VISITED PAGE MEMORY below. Compare previous/current concepts when asked, and be honest if the exact detail is not in memory. Do not introduce yourself again when navigating.\n\n"
            "RECENTLY VISITED PAGE MEMORY (use for recall and cross-page questions; do not mistake this for the current page to teach):\n"
            + ("\n\n".join(f"PAGE {m['page_number']}\nEXTRACTED TEXT: {m.get('text','')}\nBOARD / LESSON NOTES:\n{m.get('board','')}" for m in self._visited_page_memory[-6:]) or "[No previously visited pages in this live session yet.] ") + "\n\n"
            "TEXT BLOCK GEOMETRY FOR THE CURRENT FULL-SIZE PAGE (normalized [left, top, width, height]; use these exact boxes for matching selectable text blocks instead of estimating; this list may be empty for scans/handwriting):\n"
            + json.dumps(self.current_page_layout[:60], ensure_ascii=False) + "\n\n"
            "CURRENT TEACHING BOARD MARKDOWN (the app will apply your requested append/replace/clear operation):\n" + (self._board_markdown or "[Board is currently empty]") + "\n\n"
            "QUESTION VS PAGE COMPLETION: A one-off answer is NEVER proof that a page is finished. During a question turn, never say the page lesson is complete and never call finish_page_lesson. Answer the question first. If it is related to the ongoing lesson and resuming is sensible, call resume_page_lesson; the application will continue from the next uncovered item. For unrelated standalone questions, or if the learner seems to want only the answer, do not resume automatically; wait. Only say the page is complete after you actually covered all important page content.\n\n"
            f"PDF file: {Path(self.pdf_path).name}. Current page number: {current_page_index + 1}.\n"
            "EXTRACTED TEXT FROM THE CURRENT PAGE (may be empty or imperfect):\n" + (current_page_text or "[No selectable text was found; use the page image.]")
            + manual_instruction
        )
        if self.teacher_instructions:
            instruction += "\n\nUSER-DEFINED TEACHER PERSONALITY AND ADDITIONAL INSTRUCTIONS:\n" + self.teacher_instructions
        return instruction

    @staticmethod
    def _clear_queue(q):
        try:
            while True:
                q.get_nowait()
        except queue.Empty:
            return

    def _audio_callback(self, indata, frames, time_info, status):
        # Do not even copy the input buffer while PTT is released. No idle/assistant audio
        # is queued or sent to Gemini.
        if self._stop_event.is_set() or self._pause_event.is_set() or not self._ptt_event.is_set():
            return
        try:
            chunk = bytes(indata)
            self._mic_queue.put_nowait(chunk)
        except queue.Full:
            # Drop the oldest chunk rather than accumulate seconds of audio latency.
            try:
                self._mic_queue.get_nowait()
                self._mic_queue.put_nowait(bytes(indata))
            except (queue.Empty, queue.Full):
                pass

    def _speaker_loop_windows(self):
        """Play Gemini PCM chunks through Windows WinMM directly, without Python audio output/TTS."""
        import ctypes
        from ctypes import wintypes

        class WAVEFORMATEX(ctypes.Structure):
            _fields_ = [
                ("wFormatTag", wintypes.WORD),
                ("nChannels", wintypes.WORD),
                ("nSamplesPerSec", wintypes.DWORD),
                ("nAvgBytesPerSec", wintypes.DWORD),
                ("nBlockAlign", wintypes.WORD),
                ("wBitsPerSample", wintypes.WORD),
                ("cbSize", wintypes.WORD),
            ]

        class WAVEHDR(ctypes.Structure):
            _fields_ = [
                ("lpData", ctypes.c_void_p),
                ("dwBufferLength", wintypes.DWORD),
                ("dwBytesRecorded", wintypes.DWORD),
                ("dwUser", ctypes.c_size_t),
                ("dwFlags", wintypes.DWORD),
                ("dwLoops", wintypes.DWORD),
                ("lpNext", ctypes.c_void_p),
                ("reserved", ctypes.c_size_t),
            ]

        winmm = ctypes.WinDLL("winmm")
        wave_out_open = winmm.waveOutOpen
        wave_out_open.argtypes = [ctypes.POINTER(wintypes.HANDLE), wintypes.UINT,
                                  ctypes.POINTER(WAVEFORMATEX), ctypes.c_size_t, ctypes.c_size_t, wintypes.DWORD]
        wave_out_open.restype = wintypes.UINT
        wave_out_prepare = winmm.waveOutPrepareHeader
        wave_out_prepare.argtypes = [wintypes.HANDLE, ctypes.POINTER(WAVEHDR), wintypes.UINT]
        wave_out_prepare.restype = wintypes.UINT
        wave_out_write = winmm.waveOutWrite
        wave_out_write.argtypes = [wintypes.HANDLE, ctypes.POINTER(WAVEHDR), wintypes.UINT]
        wave_out_write.restype = wintypes.UINT
        wave_out_unprepare = winmm.waveOutUnprepareHeader
        wave_out_unprepare.argtypes = [wintypes.HANDLE, ctypes.POINTER(WAVEHDR), wintypes.UINT]
        wave_out_unprepare.restype = wintypes.UINT
        wave_out_reset = winmm.waveOutReset
        wave_out_reset.argtypes = [wintypes.HANDLE]
        wave_out_reset.restype = wintypes.UINT
        wave_out_close = winmm.waveOutClose
        wave_out_close.argtypes = [wintypes.HANDLE]
        wave_out_close.restype = wintypes.UINT

        fmt = WAVEFORMATEX(1, 1, 24000, 48000, 2, 16, 0)  # PCM, mono, 24 kHz, 16-bit
        handle = wintypes.HANDLE()
        result = wave_out_open(ctypes.byref(handle), 0xFFFFFFFF, ctypes.byref(fmt), 0, 0, 0)
        if result != 0:
            raise RuntimeError(f"Windows waveOutOpen failed with multimedia error {result}.")

        slots = [{"header": WAVEHDR(), "buffer": None, "prepared": False, "pending": False}
                 for _ in range(4)]
        slot_index = 0
        header_size = ctypes.sizeof(WAVEHDR)

        def reset_output():
            try:
                wave_out_reset(handle)
            except Exception:
                pass
            self._speaker_playing_event.clear()
            for slot in slots:
                if slot["prepared"]:
                    try:
                        wave_out_unprepare(handle, ctypes.byref(slot["header"]), header_size)
                    except Exception:
                        pass
                slot["header"] = WAVEHDR()
                slot["buffer"] = None
                slot["prepared"] = False
                slot["pending"] = False

        def refresh_speaker_state():
            active = not self._speaker_queue.empty()
            if not active:
                for queued_slot in slots:
                    if queued_slot["pending"] and not (int(queued_slot["header"].dwFlags) & 0x00000001):
                        active = True
                        break
            if active:
                self._speaker_playing_event.set()
            else:
                self._speaker_playing_event.clear()

        try:
            while not self._stop_event.is_set():
                refresh_speaker_state()
                if self._pause_event.is_set():
                    # Stop the currently queued WinMM buffers and wait without consuming
                    # further chunks. Resume is handled by a fresh model prompt.
                    reset_output()
                    while self._pause_event.is_set() and not self._stop_event.is_set():
                        time.sleep(0.02)
                    continue
                if self._ptt_event.is_set():
                    # Flush already-buffered assistant audio immediately when the user starts talking.
                    reset_output()
                    while self._ptt_event.is_set() and not self._stop_event.is_set():
                        time.sleep(0.01)
                    continue
                try:
                    chunk = self._speaker_queue.get(timeout=0.04)
                except queue.Empty:
                    refresh_speaker_state()
                    continue
                if chunk:
                    self._speaker_playing_event.set()
                if not chunk or self._stop_event.is_set():
                    continue
                slot = slots[slot_index]
                while slot["pending"] and not (int(slot["header"].dwFlags) & 0x00000001):  # WHDR_DONE
                    if self._stop_event.is_set() or self._ptt_event.is_set() or self._pause_event.is_set():
                        break
                    time.sleep(0.002)
                if self._stop_event.is_set():
                    break
                if self._pause_event.is_set():
                    reset_output()
                    continue
                if self._ptt_event.is_set():
                    reset_output()
                    while self._ptt_event.is_set() and not self._stop_event.is_set():
                        time.sleep(0.01)
                    continue
                if slot["prepared"]:
                    code = wave_out_unprepare(handle, ctypes.byref(slot["header"]), header_size)
                    if code != 0:
                        reset_output()
                        continue
                buffer = ctypes.create_string_buffer(len(chunk))
                ctypes.memmove(buffer, bytes(chunk), len(chunk))
                header = WAVEHDR()
                header.lpData = ctypes.cast(buffer, ctypes.c_void_p)
                header.dwBufferLength = len(chunk)
                slot["header"] = header
                slot["buffer"] = buffer  # keep PCM memory alive until Windows finishes playback
                code = wave_out_prepare(handle, ctypes.byref(slot["header"]), header_size)
                if code != 0:
                    raise RuntimeError(f"Windows waveOutPrepareHeader failed with multimedia error {code}.")
                slot["prepared"] = True
                code = wave_out_write(handle, ctypes.byref(slot["header"]), header_size)
                if code != 0:
                    raise RuntimeError(f"Windows waveOutWrite failed with multimedia error {code}.")
                slot["pending"] = True
                self._speaker_playing_event.set()
                slot_index = (slot_index + 1) % len(slots)
        finally:
            reset_output()
            self._speaker_playing_event.clear()
            wave_out_close(handle)

    def _speaker_loop(self):
        try:
            if os.name == "nt":
                # Output is delegated to the native Windows audio system; sounddevice is used only for mic capture.
                self._speaker_loop_windows()
            else:
                # Development fallback for non-Windows platforms.
                import sounddevice as sd
                with sd.RawOutputStream(samplerate=24000, channels=1, dtype="int16") as output:
                    while not self._stop_event.is_set():
                        if self._pause_event.is_set():
                            time.sleep(0.02)
                            continue
                        try:
                            chunk = self._speaker_queue.get(timeout=0.12)
                        except queue.Empty:
                            self._speaker_playing_event.clear()
                            continue
                        if chunk and not self._stop_event.is_set() and not self._ptt_event.is_set():
                            self._speaker_playing_event.set()
                            output.write(chunk)
                        if self._speaker_queue.empty():
                            self._speaker_playing_event.clear()
        except Exception as exc:
            if not self._stop_event.is_set() and not self._output_error_reported:
                self._output_error_reported = True
                self.failed.emit("Gemini Live connected, but Windows speaker output failed. Check the default output device and volume. " + str(exc))

    async def _run_live(self):
        try:
            from google import genai
            from google.genai import types
            import sounddevice as sd
        except Exception as exc:
            raise RuntimeError(
                "Realtime voice needs the Google GenAI SDK and sounddevice for microphone capture. Close Engo and run install.bat from the current version folder, "
                "then restart the program. Technical detail: " + str(exc)
            )

        self.status.emit("Reviewing the first pages to understand the document before teaching…")
        self.document_roadmap, self.roadmap_contact_sheet = await asyncio.to_thread(self._prepare_document_roadmap)
        client = genai.Client(api_key=self.api_key)
        config = {
            "response_modalities": ["AUDIO"],
            "speech_config": {"voice_config": {"prebuilt_voice_config": {"voice_name": self.voice_name}}},
            "system_instruction": {"parts": [{"text": self._system_instruction()}]},
            "input_audio_transcription": {},
            "output_audio_transcription": {},
            "tools": self._tool_declarations(),
        }
        self.status.emit(f"Connecting to Engo AI · {self.model}…")
        async with client.aio.live.connect(model=self.model, config=config) as session:
            if self._stop_event.is_set():
                return
            # Do not send the initial PDF image as a standalone realtime event. Queue it and
            # send it immediately before the first held-to-talk audio turn, preventing unsolicited replies.
            self._pending_page_image = self._make_focus_grid_image(self.page_image) if self.page_image else None
            # Give Gemini the first-pages overview before the target page. The prompt makes
            # clear that only the subsequent full-resolution image is used for page coordinates.
            if self.roadmap_contact_sheet:
                # Send the overview image without an intermediate text turn; otherwise Live can
                # start speaking about the overview before the target page has been supplied.
                await session.send_realtime_input(
                    video=types.Blob(data=self.roadmap_contact_sheet, mime_type="image/jpeg")
                )
            self._input_stream = sd.RawInputStream(
                samplerate=16000, channels=1, dtype="int16", blocksize=1024,
                callback=self._audio_callback
            )
            self._input_stream.start()
            self._speaker_thread = threading.Thread(target=self._speaker_loop, name="EngoLiveSpeaker", daemon=True)
            self._speaker_thread.start()
            self._auto_lesson_active = True
            self._auto_lesson_turns = 0
            self._user_question_pending = False
            self._resume_after_question = False
            self._lesson_focus_count = 0
            self._lesson_board_count = 0
            self._last_focus_box = None
            self._last_focus_label = ""
            self._last_focus_center_y = None
            self._focus_history = []
            self._understanding_state = "teaching"
            self._understanding_reply_active = False
            self._understanding_reply_origin = ""
            self._understanding_reply_buffer = ""
            self._pending_typed_comprehension_guidance = ""
            self._page_final_check_asked = False
            self._page_understanding_confirmed = False
            self._page_lesson_completed = False
            continuation_queue: asyncio.Queue[str] = asyncio.Queue(maxsize=1)
            # Kick off an autonomous lesson of the entire displayed page. This is an explicit
            # textual request paired with the page image, not an idle microphone event.
            if self._pending_page_image:
                await session.send_realtime_input(
                    video=types.Blob(data=self._pending_page_image, mime_type="image/jpeg")
                )
                self._pending_page_image = None
            if self.secondary_page_image:
                # The second visual is always the companion page. The instruction labels
                # distinguish it from the primary page and its independent page numbering.
                await session.send_realtime_input(
                    video=types.Blob(data=self._make_focus_grid_image(self.secondary_page_image), mime_type="image/jpeg")
                )
            self._begin_model_turn()
            await session.send_realtime_input(text=(
                (f"There are TWO linked PDFs. Primary: {Path(self.pdf_path).name}, page {self.page_index + 1}. "
                 f"Supplementary: {Path(self.secondary_pdf_path).name}, page {self.secondary_page_index + 1}. "
                 "The first full-size page image is PRIMARY; the next full-size page image is SUPPLEMENTARY. "
                 "These are the exact two pages currently displayed in the combined PDF tab. Keep their independent page numbers and use both images/text when answering. The learner may ask about either or compare them.\n" if self.secondary_pdf_path else "")
                + "START THE FULL PAGE LESSON NOW. This is the beginning of a new live conversation: introduce yourself as Engo once in one short natural sentence, then begin teaching the currently displayed PDF page from its first meaningful part, "
                "not just one region. Start speaking immediately. First call write_to_board with a compact outline, "
                "then explain ONLY the first meaningful part/problem, calling focus_page_region for its exact location. "
                "Explain the first complete problem or labeled part from beginning to end, including all internal solution steps, without pausing for repeated checks. "
                "Ask one brief understanding question only after that complete problem/part, before starting a different problem/part/section; if they say yes, continue, and if no, clarify and re-explain only the unclear point. "
                "Do not repeat the check after each line, formula, calculation, or focus target. At the end, ask whether the WHOLE PAGE is clear "
                "and WAIT for an explicit yes before calling finish_page_lesson with a one-sentence recap."
            ))
            self.status.emit("Teaching the whole page · hold SPACE and speak to interrupt with a question")

            async def send_loop():
                ptt_active = False
                while not self._stop_event.is_set():
                    if self._resume_event.is_set() and not ptt_active and not self._ptt_event.is_set():
                        # Let the current model turn reach its boundary before sending the
                        # resume instruction. Keep the speaker muted during this wait so
                        # unpausing cannot play the unfinished tail of the old response.
                        while not self._stop_event.is_set() and not self._paused_turn_done.is_set():
                            await asyncio.sleep(0.025)
                        if self._stop_event.is_set():
                            break
                        # The learner may press Pause again while this wait is in progress.
                        if not self._resume_event.is_set():
                            continue
                        self._resume_event.clear()
                        self._pause_event.clear()
                        while not continuation_queue.empty():
                            try:
                                continuation_queue.get_nowait()
                            except asyncio.QueueEmpty:
                                break
                        with self._assistant_text_lock:
                            last_point = self._paused_resume_excerpt
                        if self._pause_event.is_set():
                            continue
                        self._user_question_pending = True
                        self._resume_after_question = bool(self._auto_lesson_active)
                        self._latest_user_text = "Resume the tutor after a temporary pause."
                        self._begin_model_turn()
                        await session.send_realtime_input(text=(
                            "The learner has resumed after temporarily pausing your speech. Repeat ONLY the last interrupted sentence or teaching point once, not the earlier explanation. "
                            f"The last point the learner was following was: {last_point}. "
                            "Then continue the same lesson from the next uncovered idea, preserving all existing conversation context and board notes. "
                            "Do not introduce yourself again, do not restart the page, and do not repeat an entire previous answer."
                        ))
                        self.status.emit("Resumed · repeating the last point, then continuing the lesson")
                    # Automatically continue between spoken turns until the tutor explicitly
                    # marks the full page lesson complete or the safety turn cap is reached.
                    if not ptt_active and not self._ptt_event.is_set() and not self._pause_event.is_set():
                        try:
                            continuation_prompt = continuation_queue.get_nowait()
                        except asyncio.QueueEmpty:
                            continuation_prompt = None
                        if continuation_prompt and self._auto_lesson_active:
                            # Let the last PCM chunks drain before asking Gemini for the next section;
                            # otherwise a new generation can overlap the tail of the previous speech.
                            while (not self._stop_event.is_set() and not self._ptt_event.is_set() and not self._pause_event.is_set()
                                   and not self._speaker_queue.empty()):
                                await asyncio.sleep(0.015)
                            # Short settling interval after playback queue drains; avoid the old
                            # sluggish gap between chunks while still preventing two turns overlapping.
                            await asyncio.sleep(0.12)
                            if self._stop_event.is_set() or self._ptt_event.is_set() or self._pause_event.is_set():
                                continue
                            self._auto_lesson_turns += 1
                            if self._pending_page_image:
                                await session.send_realtime_input(
                                    video=types.Blob(data=self._pending_page_image, mime_type="image/jpeg")
                                )
                                self._pending_page_image = None
                            self._begin_model_turn()
                            await session.send_realtime_input(text=continuation_prompt)
                            self.status.emit("Continuing the page lesson… hold SPACE if you want to ask something")
                    # Coalesce page navigation and update the visual reference without touching
                    # microphone capture state.
                    try:
                        page_index, page_text, page_image, incoming_board_markdown = self._page_update_queue.get_nowait()
                    except queue.Empty:
                        page_index = None
                    if page_index is not None:
                        # Store a new visual frame for the next spoken turn instead of sending
                        # it as a standalone realtime input (which can make a model answer unprompted).
                        focus_page_image = self._make_focus_grid_image(page_image) if page_image else b""
                        if page_image:
                            if ptt_active:
                                await session.send_realtime_input(video=types.Blob(data=focus_page_image, mime_type="image/jpeg"))
                                self._pending_page_image = None
                            else:
                                self._pending_page_image = focus_page_image
                        new_layout = await asyncio.to_thread(self._read_pdf_page_layout, page_index)
                        with self._page_lock:
                            page_changed = int(page_index) != int(self.page_index)
                            previous_page_index = int(self.page_index)
                            previous_page_text = str(self.page_text or "")
                            previous_board_markdown = str(self._board_markdown or "")
                            if page_changed and (previous_page_text.strip() or previous_board_markdown.strip()):
                                memory_item = {
                                    "page_number": previous_page_index + 1,
                                    "text": previous_page_text[:2600],
                                    "board": previous_board_markdown[:4200],
                                }
                                self._visited_page_memory.append(memory_item)
                                self._visited_page_memory = self._visited_page_memory[-6:]
                            self.page_index, self.page_text = page_index, page_text[:16000]
                            self.page_image = bytes(page_image or b"")
                            self.current_page_layout = new_layout
                            manual_ref = self._get_manual_target()
                            if manual_ref and int(manual_ref.get("page_index", -1)) != int(page_index):
                                self.clear_manual_target()
                            with self._manual_target_lock:
                                active_manual_ref = self._active_manual_question_target
                                if active_manual_ref and int(active_manual_ref.get("page_index", -1)) != int(page_index):
                                    self._active_manual_question_target = None
                            if incoming_board_markdown is not None:
                                self._board_markdown = incoming_board_markdown[:24000]
                        # Page navigation is reference context, not a user utterance. Update
                        # the session system context without triggering an unsolicited answer.
                        updated_instruction = self._system_instruction()
                        await session.send_context_update(
                            system_instruction=types.Content(parts=[types.Part(text=updated_instruction)])
                        )
                        self.status.emit(f"Live reference updated · page {page_index + 1}")
                        if page_changed:
                            # A genuinely different displayed page begins a fresh lesson,
                            # whether the previous page was complete or not. Region focus calls
                            # on the same page do not come through this path.
                            self._auto_lesson_active = True
                            self._auto_lesson_turns = 0
                            self._lesson_focus_count = 0
                            self._lesson_board_count = 0
                            self._last_focus_box = None
                            self._last_focus_label = ""
                            self._last_focus_center_y = None
                            self._focus_history = []
                            self._understanding_state = "teaching"
                            self._understanding_reply_active = False
                            self._understanding_reply_origin = ""
                            self._understanding_reply_buffer = ""
                            self._pending_typed_comprehension_guidance = ""
                            self._page_final_check_asked = False
                            self._page_understanding_confirmed = False
                            self._page_lesson_completed = False
                            self._explicit_focus_jump.clear()
                            while not continuation_queue.empty():
                                try:
                                    continuation_queue.get_nowait()
                                except asyncio.QueueEmpty:
                                    break
                            if not ptt_active:
                                try:
                                    continuation_queue.put_nowait(
                                        f"The PDF viewer is now showing page {page_index + 1}. Continue in the SAME live conversation; do NOT introduce yourself again. Start at the top of this new page. The new page image will be sent before this prompt. Use the board content for this page and the RECENTLY VISITED PAGE MEMORY when relevant. Call write_to_board with a concise outline only if the current page board is empty, and move focus before each item. Keep all steps of each problem together in one uninterrupted explanation; do not ask after each formula, line, calculation, paragraph, or focus target. Ask only after completing a whole problem/labeled part or a distinct section/topic, before moving to the next one. At the end, ask one whole-page understanding check and WAIT for a clear yes before calling finish_page_lesson. Do not treat navigation itself as a spoken question."
                                    )
                                except asyncio.QueueFull:
                                    pass

                    # The supplementary PDF has its own page navigation and image reference.
                    # Updating it changes context only; it must not start a new spoken lesson.
                    try:
                        secondary_update = self._secondary_page_update_queue.get_nowait()
                    except queue.Empty:
                        secondary_update = None
                    if secondary_update is not None:
                        sec_index, sec_text, sec_image, sec_count = secondary_update
                        self.secondary_page_index = sec_index
                        self.secondary_page_text = sec_text
                        self.secondary_page_image = sec_image
                        self.secondary_page_count = sec_count
                        self.secondary_page_layout = await asyncio.to_thread(self._read_pdf_page_layout, sec_index, self.secondary_pdf_path)
                        if sec_image:
                            self._pending_secondary_page_image = self._make_focus_grid_image(sec_image)
                        updated_instruction = self._system_instruction()
                        await session.send_context_update(system_instruction=types.Content(parts=[types.Part(text=updated_instruction)]))
                        self.status.emit(f"Supplementary reference updated · {Path(self.secondary_pdf_path).name} · page {sec_index + 1}")

                    # A manual region changes the context/visual reference, but must not trigger a reply by itself.
                    if self._manual_context_dirty.is_set():
                        self._manual_context_dirty.clear()
                        await session.send_context_update(
                            system_instruction=types.Content(parts=[types.Part(text=self._system_instruction())])
                        )
                        manual_ref = self._get_manual_target()
                        if manual_ref and int(manual_ref.get("page_index", -1)) == self.page_index:
                            # Do not upload the crop until the learner asks; this avoids extra visual tokens
                            # and ensures changing a selection never triggers an unsolicited response.
                            self.status.emit("Manual selection ready · ask about it by voice or text")
                        else:
                            # Clearing a crop makes the full page the next visual reference, on demand.
                            self._pending_page_image = self._make_focus_grid_image(self.page_image) if self.page_image else None
                            self.status.emit("Manual selection cleared · full page restored")

                    # Typed questions/board requests have the same live context and tool access as speech.
                    # They are sent only while PTT is released, and take priority over a queued continuation.
                    if not ptt_active and not self._ptt_event.is_set() and not self._pause_event.is_set():
                        try:
                            typed_message = self._text_message_queue.get_nowait()
                        except queue.Empty:
                            typed_message = None
                        if typed_message:
                            if self._looks_like_direct_focus_request(typed_message):
                                self._explicit_focus_jump.set()
                            while not continuation_queue.empty():
                                try:
                                    continuation_queue.get_nowait()
                                except asyncio.QueueEmpty:
                                    break
                            if self._pending_page_image:
                                await session.send_realtime_input(
                                    video=types.Blob(data=self._pending_page_image, mime_type="image/jpeg")
                                )
                                self._pending_page_image = None
                            if self._pending_secondary_page_image:
                                await session.send_realtime_input(video=types.Blob(data=self._pending_secondary_page_image, mime_type="image/jpeg"))
                                self._pending_secondary_page_image = None
                            manual_ref = self._get_manual_target()
                            if manual_ref and manual_ref.get("image") and int(manual_ref.get("page_index", -1)) == self.page_index:
                                await session.send_realtime_input(video=types.Blob(data=manual_ref["image"], mime_type="image/jpeg"))
                            comprehension_guidance = self._pending_typed_comprehension_guidance or self._comprehension_turn_guidance()
                            self._pending_typed_comprehension_guidance = ""
                            self._begin_model_turn()
                            await session.send_realtime_input(text=(
                                comprehension_guidance + "\n\n" +
                                "The learner typed this message into Engo (not speech). Answer it in the same conversation. "
                                + ("The most recent crop is the manually selected area; explain that exact area first unless the user requests something else. " if manual_ref and int(manual_ref.get("page_index", -1)) == self.page_index else "")
                                + "IMPORTANT: If the message names or requests a specific item, question, worked solution, equation, paragraph, diagram, chart, photo or table on the displayed page, first locate and focus THAT exact target, even if it is not the next item in reading order. Call focus_page_region and set user_requested_target=true. Do not force it to the current/next item. "
                                "If it asks to change, write, explain, or make examples on the teaching board, use write_to_board with the proper append/replace/clear mode. "
                                "Answer this as a separate question: do not call finish_page_lesson merely because your answer is complete. If it belongs to the ongoing lesson and should resume, call resume_page_lesson after answering; otherwise answer and wait. User message: " + typed_message
                            ))
                            self.status.emit("Engo AI is answering your typed message…")

                    command = None
                    try:
                        command = self._ptt_commands.get_nowait()
                    except queue.Empty:
                        pass
                    if command is True and not ptt_active:
                        self._begin_understanding_reply()
                        comprehension_guidance = self._comprehension_turn_guidance()
                        try:
                            await session.send_context_update(
                                system_instruction=types.Content(parts=[types.Part(text=self._system_instruction() + "\n\n" + comprehension_guidance)])
                            )
                        except Exception:
                            # The existing session instruction still contains the complete
                            # comprehension protocol; a transient context refresh must not
                            # block the learner's microphone turn.
                            pass
                        # If the learner starts talking just as an automatic continuation was
                        # queued, cancel that stale prompt. The question takes priority; the
                        # normal turn-complete handler will enqueue a fresh resume afterwards.
                        while not continuation_queue.empty():
                            try:
                                continuation_queue.get_nowait()
                            except asyncio.QueueEmpty:
                                break
                        ptt_active = True
                        # Send the latest visible page immediately before the learner's audio,
                        # never as a free-standing input that could trigger an unsolicited reply.
                        if self._pending_page_image:
                            await session.send_realtime_input(
                                video=types.Blob(data=self._pending_page_image, mime_type="image/jpeg")
                            )
                            self._pending_page_image = None
                        if self._pending_secondary_page_image:
                            await session.send_realtime_input(video=types.Blob(data=self._pending_secondary_page_image, mime_type="image/jpeg"))
                            self._pending_secondary_page_image = None
                        manual_ref = self._get_manual_target()
                        if manual_ref and manual_ref.get("image") and int(manual_ref.get("page_index", -1)) == self.page_index:
                            await session.send_realtime_input(video=types.Blob(data=manual_ref["image"], mime_type="image/jpeg"))
                            await session.send_context_update(
                                system_instruction=types.Content(parts=[types.Part(text=self._system_instruction() + "\nThe learner is speaking now and the last image is their manually selected crop. Prioritize it if their spoken question refers to the selection; do not narrate page completion just because this question is answered.")])
                            )
                        self.status.emit("Listening · keep holding SPACE to talk; release it to send your question")
                    elif command is False and ptt_active:
                        # Drain the last captured chunks before ending this audio turn.
                        while True:
                            try:
                                final_chunk = self._mic_queue.get_nowait()
                            except queue.Empty:
                                break
                            if final_chunk:
                                await session.send_realtime_input(
                                    audio=types.Blob(data=final_chunk, mime_type="audio/pcm;rate=16000")
                                )
                        # With default server VAD, audio_stream_end closes the push-to-talk turn.
                        self._begin_model_turn()
                        await session.send_realtime_input(audio_stream_end=True)
                        ptt_active = False
                        self.status.emit("Processing your question · hold SPACE again after the answer")

                    if ptt_active:
                        try:
                            audio_bytes = await asyncio.to_thread(self._mic_queue.get, True, 0.04)
                        except queue.Empty:
                            continue
                        if audio_bytes and not self._stop_event.is_set():
                            await session.send_realtime_input(
                                audio=types.Blob(data=audio_bytes, mime_type="audio/pcm;rate=16000")
                            )
                    else:
                        await asyncio.sleep(0.025)

            async def receive_loop():
                # IMPORTANT: google-genai's session.receive() iterator may end after one
                # completed model turn. Re-enter it for every subsequent turn; otherwise
                # FIRST_COMPLETED below shuts down the session immediately after the first reply.
                while not self._stop_event.is_set():
                    received_any = False
                    async for response in session.receive():
                        received_any = True
                        if self._stop_event.is_set():
                            return
                        server_content = getattr(response, "server_content", None)
                        if server_content is not None:
                            incoming = getattr(server_content, "input_transcription", None)
                            if incoming is not None and str(getattr(incoming, "text", "") or "").strip():
                                incoming_text = str(incoming.text)
                                self.transcript.emit("You", incoming_text)
                                # Keep a short voice-command context for protecting the persistent board.
                                # Repeated/incremental transcript fragments are harmless to the intent checks.
                                self._latest_user_text = (self._latest_user_text + " " + incoming_text)[-3000:]
                                if self._understanding_reply_active:
                                    self._apply_understanding_reply(incoming_text, cumulative=True)
                                if self._looks_like_direct_focus_request(incoming_text):
                                    self._explicit_focus_jump.set()
                                incoming_norm = re.sub(r"\s+", " ", incoming_text.casefold()).strip()
                                if any(cue in incoming_norm for cue in ("continue the lesson", "resume the lesson", "كمّل الشرح", "كمل الشرح", "اكمل الشرح", "كمّل الدرس", "كمل الدرس", "كمل من حيث وقفنا")):
                                    self._auto_lesson_active = True
                                    self._resume_after_question = True
                                    with self._manual_target_lock:
                                        self._active_manual_question_target = None
                            outgoing = getattr(server_content, "output_transcription", None)
                            if outgoing is not None and str(getattr(outgoing, "text", "") or "").strip():
                                outgoing_text = str(outgoing.text)
                                if not self._model_turn_active.is_set():
                                    self._begin_model_turn()
                                self._remember_assistant_transcript(outgoing_text)
                                if self._is_page_comprehension_question(self._assistant_turn_text):
                                    self._page_final_check_asked = True
                                # Keep collecting the current response while paused so Resume
                                # can quote its final point, but do not advance the visible log.
                                if not self._pause_event.is_set():
                                    self.transcript.emit("Engo AI", outgoing_text)
                            model_turn = getattr(server_content, "model_turn", None)
                            if model_turn is not None:
                                self._model_turn_active.set()
                                self._paused_turn_done.clear()
                                for part in (getattr(model_turn, "parts", None) or []):
                                    inline = getattr(part, "inline_data", None)
                                    data = getattr(inline, "data", None) if inline is not None else None
                                    if data:
                                        if isinstance(data, str):
                                            try:
                                                data = base64.b64decode(data)
                                            except Exception:
                                                data = b""
                                        if data and not self._ptt_event.is_set() and not self._pause_event.is_set():
                                            # Never drop an older PCM chunk: that caused words and sentence endings
                                            # to vanish on long responses. Apply gentle backpressure until playback catches up.
                                            chunk = bytes(data)
                                            while (not self._stop_event.is_set() and not self._ptt_event.is_set()
                                                   and not self._pause_event.is_set()):
                                                try:
                                                    self._speaker_queue.put_nowait(chunk)
                                                    break
                                                except queue.Full:
                                                    await asyncio.sleep(0.008)
                            if bool(getattr(server_content, "interrupted", False)):
                                self._clear_queue(self._speaker_queue)
                                self.status.emit("Engo AI interrupted · listening to you…")
                            elif bool(getattr(server_content, "turn_complete", False)):
                                self._model_turn_active.clear()
                                # Always signal the boundary: the learner may have resumed
                                # just before this event arrived, so checking only _pause_event
                                # here could otherwise leave send_loop waiting forever.
                                self._paused_turn_done.set()
                                if self._pause_event.is_set():
                                    self.status.emit("Lesson paused · press Resume & repeat last point to continue")
                                elif self._user_question_pending:
                                    self._user_question_pending = False
                                    self._understanding_reply_active = False
                                    state = str(self._understanding_state)
                                    if self._page_lesson_completed:
                                        self._understanding_state = "completed"
                                        self._auto_lesson_active = False
                                        self.status.emit("Page lesson complete · waiting for your next question")
                                    elif state == "awaiting_clarification":
                                        self._auto_lesson_active = True
                                        self._resume_after_question = False
                                        self.status.emit("Waiting for you to tell Engo which point is unclear")
                                    elif state == "reexplaining":
                                        self._auto_lesson_active = True
                                        self._understanding_state = "awaiting_confirmation"
                                        self._resume_after_question = False
                                        self.status.emit("Explanation repeated · waiting for your understanding confirmation")
                                    elif state == "confirmed" and self._page_understanding_confirmed:
                                        # The learner confirmed the final whole-page check. If the
                                        # model did not call finish_page_lesson in the same turn,
                                        # request only that final bookkeeping action now.
                                        self._auto_lesson_active = True
                                        self._resume_after_question = False
                                        try:
                                            continuation_queue.put_nowait(
                                                "The learner has explicitly confirmed that the WHOLE PAGE is understood. Give a concise final recap and call finish_page_lesson now. Do not move to another page or teach another item."
                                            )
                                        except asyncio.QueueFull:
                                            pass
                                        self.status.emit("Whole page understood · finishing the page lesson")
                                    elif state == "confirmed":
                                        # The model has received a clear yes. Its response should
                                        # start the next uncovered unit in this same live turn.
                                        self._auto_lesson_active = True
                                        self._understanding_state = "awaiting_confirmation"
                                        self._resume_after_question = False
                                        with self._manual_target_lock:
                                            self._active_manual_question_target = None
                                        self.status.emit("Understood · Engo is moving to the next part")
                                    else:
                                        should_resume = bool(self._resume_after_question and self._auto_lesson_active)
                                        self._resume_after_question = False
                                        if should_resume and not self._pause_event.is_set():
                                            self._auto_lesson_active = True
                                            self._understanding_state = "teaching"
                                            try:
                                                continuation_queue.put_nowait(
                                                    "The learner's question has been answered and you explicitly chose to resume. Continue from the next uncovered item and move its focus rectangle first. Keep all steps within the same problem/labeled part together; ask for understanding only after finishing that complete problem/part or a distinct section/topic, not after every calculation or focus move. Do not finish the page without the final page-wide confirmation."
                                                )
                                            except asyncio.QueueFull:
                                                pass
                                            self.status.emit("Question answered · resuming the lesson")
                                        else:
                                            self._auto_lesson_active = False
                                            self.status.emit("Question answered · lesson paused; ask to continue when ready")
                                elif self._auto_lesson_active and not self._ptt_event.is_set() and not self._pause_event.is_set():
                                    # One spoken teaching unit has ended. The tutor should have
                                    # asked its understanding check; now wait instead of sending
                                    # an automatic continuation prompt.
                                    self._understanding_state = "awaiting_confirmation"
                                    self._understanding_reply_active = False
                                    self.focus_clear_requested.emit()
                                    self.status.emit("Waiting for your understanding confirmation · say yes to continue or no to clarify")
                                elif self._page_lesson_completed:
                                    self.focus_clear_requested.emit()
                                    self.status.emit("Page lesson complete · waiting for your next question")
                                else:
                                    self.focus_clear_requested.emit()
                                    self.status.emit("Answer complete · the page was not marked complete")

                        tool_call = getattr(response, "tool_call", None)
                        if tool_call is not None:
                            calls = getattr(tool_call, "function_calls", None) or []
                            function_responses = []
                            for call in calls:
                                name = str(getattr(call, "name", "") or "")
                                args = getattr(call, "args", {}) or {}
                                if not isinstance(args, dict):
                                    try: args = json.loads(str(args))
                                    except Exception: args = {}
                                call_id = getattr(call, "id", None)
                                result = {"ok": True}
                                if name == "write_to_board":
                                    mode = str(args.get("mode") or "append").strip().lower()
                                    if mode not in {"append", "replace", "clear"}:
                                        mode = "append"
                                    title = str(args.get("title") or "Lesson notes").strip()
                                    content = str(args.get("content") or "").strip()
                                    if mode == "clear" and not self._board_clear_requested(self._latest_user_text):
                                        result = {"ok": False, "message": "Board clearing is destructive. The learner has not explicitly asked to clear it. Preserve all existing notes and use append instead. Only clear after a direct learner request such as 'امسح البورد'."}
                                    elif mode == "clear":
                                        self._board_markdown = ""
                                        self.board_command.emit("clear", title, "")
                                        result["message"] = "The board was cleared because the learner explicitly requested it."
                                    elif not content:
                                        result = {"ok": False, "message": "Board content was empty. Provide Markdown content for append or replace mode."}
                                    else:
                                        section = f"## {title}\n\n{content}" if title else content
                                        normalize = lambda value: re.sub(r"\s+", " ", re.sub(r"[^\w]+", " ", str(value or "").casefold())).strip()
                                        norm_content = normalize(content)
                                        norm_board = normalize(self._board_markdown)
                                        # Starting a new lesson may tempt the model to rewrite its outline. Never let that silently erase an existing page board.
                                        if mode == "replace" and norm_board and not self._board_rewrite_requested(self._latest_user_text):
                                            mode = "append"
                                        if mode == "append" and norm_content and len(norm_content) >= 18 and norm_content in norm_board:
                                            result = {"ok": False, "message": "Duplicate prevented: this note is already on the board. Do not repeat it; add a concise note about the next uncovered concept, an actual new example, or a missing equation."}
                                        elif mode == "replace" and normalize(section) == normalize(self._board_markdown):
                                            result = {"ok": True, "message": "The board already contains this exact content; no duplicate edit was made. Continue with a new uncovered concept."}
                                        else:
                                            self._lesson_board_count += 1
                                            if mode == "append":
                                                self._board_markdown = (self._board_markdown.rstrip() + "\n\n---\n\n" + section).strip() if self._board_markdown.strip() else section
                                            else:
                                                self._board_markdown = section
                                            self.board_command.emit(mode, title, content)
                                            result["message"] = ("Board section appended." if mode == "append" else "Board replaced with the edited Markdown.") + " The live board operation has been applied."
                                elif name == "navigate_pdf_page":
                                    target = str(args.get("target") or "next").strip().lower()
                                    if target not in {"next", "previous", "first", "last", "number"}:
                                        result = {"ok": False, "message": "Unsupported navigation target. Use next, previous, first, last, or number."}
                                    else:
                                        try:
                                            requested_page = int(args.get("page_number") or 1) if target == "number" else 0
                                        except Exception:
                                            requested_page = 1
                                        if target == "number" and requested_page < 1:
                                            result = {"ok": False, "message": "Page numbers start at 1. Ask for a valid page number."}
                                        else:
                                            self.page_navigation_requested.emit(target, requested_page)
                                            result = {"ok": True, "target": target, "page_number": requested_page or None,
                                                      "message": "Navigation request sent to the PDF viewer. Continue the lesson when the new page image arrives; do not reintroduce yourself."}
                                elif name == "resume_page_lesson":
                                    if self._user_question_pending and self._auto_lesson_active:
                                        self._resume_after_question = True
                                        result = {"ok": True, "message": "Answer the learner's question fully; then the app will resume from the next uncovered item. This does not complete the page."}
                                    else:
                                        result = {"ok": False, "message": "No in-progress lesson is currently eligible for automatic resumption. Answer and wait."}
                                elif name == "finish_page_lesson":
                                    if not self._page_understanding_confirmed:
                                        result = {"ok": False, "message": "Do NOT finish yet. First ask the learner a separate whole-page comprehension question and WAIT. Only after the learner clearly answers yes/understood may you call finish_page_lesson."}
                                        if call_id is not None:
                                            function_responses.append(types.FunctionResponse(id=call_id, name=name, response=result))
                                        continue
                                    page_text_length = len(self.page_text.strip())
                                    # The user's detail choice controls lesson depth. A fixed high minimum used
                                    # to trap short/scanned pages in an endless continuation loop.
                                    layout_items = len(self.current_page_layout or [])
                                    if self.lesson_detail == "brief":
                                        estimated_items = max(2, min(4, math.ceil(max(page_text_length, 300) / 1500), max(2, layout_items)))
                                        minimum_focus_calls = estimated_items
                                    else:
                                        estimated_items = max(3, min(7, math.ceil(max(page_text_length, 900) / 1400), max(3, layout_items)))
                                        minimum_focus_calls = estimated_items
                                    # Board appends are encouraged but must not trap completion forever;
                                    # a duplicate note or pre-existing board should not stop a completed lesson.
                                    if self._lesson_focus_count < minimum_focus_calls:
                                        result = {
                                            "ok": False,
                                            "message": (
                                                "The lesson is not complete yet. Continue through the next items on the page, "
                                                f"you need at least {minimum_focus_calls} distinct valid focus targets (currently {self._lesson_focus_count}). "
                                                "Move top-to-bottom, avoid previously covered regions, and only finish after all important content on the page has been covered. Board update count must not block completion."
                                            ),
                                        }
                                    else:
                                        self._auto_lesson_active = False
                                        self._page_lesson_completed = True
                                        self._understanding_state = "completed"
                                        summary = str(args.get("summary") or "The displayed page lesson is complete.")
                                        self.status.emit("Full page lesson complete · hold SPACE or type to ask Engo AI a question")
                                        recap_section = f"## Final recap\n\n{summary}"
                                        self._board_markdown = (self._board_markdown.rstrip() + "\n\n---\n\n" + recap_section).strip() if self._board_markdown.strip() else recap_section
                                        self.board_update.emit("Final recap", summary)
                                        result["message"] = "Full-page lesson marked complete. Continue listening for the learner's next voice or typed question."
                                elif name == "draw_page_arrow":
                                    # Voice lessons no longer create arrows on the PDF page.
                                    result = {"ok": False, "message": "Page arrows are disabled during voice lessons. Use the focus rectangle only."}
                                elif name == "focus_page_region":
                                    focus_source = str(args.get("source") or "primary").strip().lower()
                                    if focus_source not in {"primary", "supplementary"} or (focus_source == "supplementary" and not self.secondary_pdf_path):
                                        focus_source = "primary"
                                    if focus_source == "supplementary":
                                        current_idx = int(self.secondary_page_index)
                                        page_text = self.secondary_page_text
                                        focus_layout = self.secondary_page_layout
                                    else:
                                        with self._page_lock:
                                            current_idx = int(self.page_index)
                                            page_text = self.page_text
                                        focus_layout = self.current_page_layout
                                    try:
                                        page_number = int(args.get("page", current_idx + 1))
                                    except Exception:
                                        page_number = current_idx + 1
                                    page_idx = page_number - 1
                                    label = str(args.get("label") or "Current item").strip()
                                    kind = str(args.get("kind") or "text").strip().lower()
                                    allowed_kinds = {"text", "handwriting", "equation", "problem", "solution", "worked_solution", "table", "diagram", "chart", "photo", "image", "figure", "graph", "plot", "drawing", "manual", "other"}
                                    if kind not in allowed_kinds:
                                        kind = "other"
                                    user_requested_target = bool(args.get("user_requested_target", False)) or self._explicit_focus_jump.is_set()
                                    raw_box = args.get("box")
                                    box = None
                                    try:
                                        vals = [float(v) for v in raw_box]
                                        if len(vals) == 4 and all(math.isfinite(v) for v in vals):
                                            # Contract is [left, top, width, height], not corner coordinates.
                                            x, y, w, h = vals
                                            if (0 <= x <= 1 and 0 <= y <= 1 and
                                                0 < w <= 1 and 0 < h <= 1 and
                                                x + w <= 1.02 and y + h <= 1.02):
                                                box = [max(0.0, x), max(0.0, y), min(w, 1.0 - max(0.0, x)), min(h, 1.0 - max(0.0, y))]
                                    except Exception:
                                        box = None
                                    label_lc = label.lower()
                                    # A manual drag-selection is authoritative for the next user question.
                                    # Lock the exact box and prevent both model coordinates and PDF text matching
                                    # from silently substituting a different item.
                                    active_manual = self._get_active_manual_question_target()
                                    manual_locked = bool(active_manual and int(active_manual.get("page_index", -1)) == current_idx)
                                    if manual_locked:
                                        page_idx = current_idx
                                        box = list(active_manual.get("box") or [])
                                        label = "Manually selected region"
                                        label_lc = label.lower()
                                        kind = "manual"
                                        user_requested_target = True
                                    visual_target = kind in {"manual", "diagram", "chart", "photo", "image", "figure", "graph", "plot", "drawing", "table"}
                                    solution_target = kind in {"solution", "worked_solution", "handwriting"}
                                    if not manual_locked and kind == "handwriting" and box:
                                        # Handwritten characters are noisy and often have no
                                        # selectable text geometry. Expand very tight model
                                        # boxes to a readable line-sized focus target.
                                        center_x = box[0] + box[2] / 2.0
                                        center_y = box[1] + box[3] / 2.0
                                        width = min(0.92, max(0.15, box[2]))
                                        height = min(0.42, max(0.038, box[3]))
                                        x = max(0.0, min(1.0 - width, center_x - width / 2.0))
                                        y = max(0.0, min(1.0 - height, center_y - height / 2.0))
                                        box = [x, y, width, height]
                                    # For selectable text, anchor estimated labels to PDF block geometry;
                                    # never run this override against a manual selection.
                                    excluded_boxes = [item.get("box") for item in self._focus_history[-16:]] if not user_requested_target else None
                                    matched_box = None if manual_locked else self._match_layout_box(label, kind, excluded_boxes=excluded_boxes, layout_items=focus_layout)
                                    use_matched_box = bool(matched_box)
                                    if use_matched_box and kind == "handwriting" and box:
                                        # Never let fuzzy layout text matching jump to a different
                                        # part of a handwriting-heavy page. The matched text block
                                        # must lie mostly inside the model's visually selected area.
                                        mx, my, mw, mh = [float(v) for v in matched_box]
                                        bx, by, bw, bh = [float(v) for v in box]
                                        ix1, iy1 = max(mx, bx), max(my, by)
                                        ix2, iy2 = min(mx + mw, bx + bw), min(my + mh, by + bh)
                                        intersection = max(0.0, ix2 - ix1) * max(0.0, iy2 - iy1)
                                        matched_area = max(1e-6, mw * mh)
                                        use_matched_box = (intersection / matched_area) >= 0.70
                                    if not manual_locked and use_matched_box and (user_requested_target or kind in {"text", "equation", "problem", "solution", "worked_solution", "handwriting"}):
                                        box = matched_box
                                    # Re-apply the handwriting minimum AFTER text-block matching too.
                                    # A fuzzy OCR/layout match can otherwise replace the broad model
                                    # rectangle with a tiny word/glyph box, which is especially poor
                                    # for cursive writing and multi-line worked solutions.
                                    if not manual_locked and kind == "handwriting" and box:
                                        center_x = box[0] + box[2] / 2.0
                                        center_y = box[1] + box[3] / 2.0
                                        width = min(0.92, max(0.15, box[2]))
                                        height = min(0.42, max(0.038, box[3]))
                                        x = max(0.0, min(1.0 - width, center_x - width / 2.0))
                                        y = max(0.0, min(1.0 - height, center_y - height / 2.0))
                                        box = [x, y, width, height]
                                    error_message = ""
                                    if page_idx != current_idx:
                                        error_message = f"Wrong page number. The visible target is page {current_idx + 1}; call focus_page_region for that page only."
                                    elif not box:
                                        error_message = "Invalid box. Use [left, top, width, height] normalized to the entire full page, with all values from 0 to 1."
                                    elif not manual_locked and (box[2] < 0.035 or box[3] < 0.012):
                                        error_message = "The box is too small to show the item. Select the actual text/equation with a little margin."
                                    elif not manual_locked and not visual_target and (box[3] > (0.42 if solution_target else 0.25) or (box[3] > 0.12 and box[3] > box[2] * 0.85) or (box[2] > 0.98 and box[3] > 0.15)):
                                        error_message = "That rectangle is too tall or too large for this written item. Select the actual lines or the complete worked solution, but do not include a large blank region or the whole page."
                                    else:
                                        cx, cy = box[0] + box[2] / 2, box[1] + box[3] / 2
                                        prev = self._last_focus_box
                                        if prev is not None:
                                            same_label = re.sub(r"\W+", " ", label_lc).strip() == re.sub(r"\W+", " ", self._last_focus_label.lower()).strip()
                                            ix1, iy1 = max(box[0], prev[0]), max(box[1], prev[1])
                                            ix2, iy2 = min(box[0] + box[2], prev[0] + prev[2]), min(box[1] + box[3], prev[1] + prev[3])
                                            inter = max(0.0, ix2 - ix1) * max(0.0, iy2 - iy1)
                                            smaller = max(1e-6, min(box[2] * box[3], prev[2] * prev[3]))
                                            if not user_requested_target:
                                                if same_label and inter / smaller > 0.72:
                                                    error_message = "This is essentially the same target you just explained. Move to the next uncovered item below it."
                                                elif inter / smaller > 0.88:
                                                    error_message = "This target overlaps the previous target almost completely. Select a different, not-yet-explained item."
                                                elif self._last_focus_center_y is not None and cy < self._last_focus_center_y - 0.065:
                                                    error_message = "Reading order moved backwards. Continue from the next item lower on the page. If the learner explicitly asked for a different item, set user_requested_target=true."
                                                elif self._last_focus_center_y is not None and cy - self._last_focus_center_y > 0.42:
                                                    error_message = "This jump skips a large section of the page. Cover intermediate items in order, unless the learner explicitly requested this target."
                                                if not error_message:
                                                    for old in self._focus_history[-16:]:
                                                        old_box = old.get("box")
                                                        if not isinstance(old_box, (list, tuple)) or len(old_box) != 4:
                                                            continue
                                                        ox, oy, ow, oh = [float(v) for v in old_box]
                                                        ix1, iy1 = max(box[0], ox), max(box[1], oy)
                                                        ix2, iy2 = min(box[0] + box[2], ox + ow), min(box[1] + box[3], oy + oh)
                                                        inter_old = max(0.0, ix2 - ix1) * max(0.0, iy2 - iy1)
                                                        smaller_old = max(1e-6, min(box[2] * box[3], ow * oh))
                                                        if inter_old / smaller_old > 0.86:
                                                            error_message = "This region was already explained earlier on this page. Select the next uncovered region; use the text-block list and do not revisit old targets."
                                                            break
                                    if error_message:
                                        result = {"ok": False, "message": error_message}
                                        self.status.emit("Checking target position · asking Engo AI to correct the focus")
                                    else:
                                        self._lesson_focus_count += 1
                                        if user_requested_target:
                                            self._explicit_focus_jump.clear()
                                        # A user-requested detour must not corrupt the automatic
                                        # lesson's reading-order cursor. After answering, the next
                                        # continuation can resume from its prior uncovered position.
                                        if not user_requested_target:
                                            self._last_focus_box = list(box)
                                            self._last_focus_label = label
                                            self._last_focus_center_y = box[1] + box[3] / 2
                                            self._focus_history.append({"box": list(box), "label": label, "kind": kind})
                                            self._focus_history = self._focus_history[-24:]
                                        self.status.emit(f"Explaining page {page_idx + 1} · {label[:90]}")
                                        self.focus_requested.emit(page_idx, box, label, kind, focus_source)
                                        result = {"ok": True, "page": page_idx + 1, "kind": kind, "user_requested_target": user_requested_target,
                                                  "message": ("Focus is locked to the learner's exact hand-drawn selection; do not substitute another page item. Explain that crop first." if manual_locked else ("Focus set on the learner-requested target. Explain that exact item, then resume the automatic lesson from its next uncovered item." if user_requested_target else "Focus set on the current item. Explain only this item, then move to the next uncovered item in top-to-bottom reading order. No page re-render was needed."))}
                                if call_id is not None:
                                    function_responses.append(types.FunctionResponse(id=call_id, name=name, response=result))
                            if function_responses:
                                await session.send_tool_response(function_responses=function_responses)
                    if not received_any:
                        # The server closed the receive stream rather than ending a normal turn.
                        return

            async def wait_for_stop():
                await asyncio.to_thread(self._stop_event.wait)

            tasks = [asyncio.create_task(send_loop()), asyncio.create_task(receive_loop()), asyncio.create_task(wait_for_stop())]
            done, pending = await asyncio.wait(tasks, return_when=asyncio.FIRST_COMPLETED)
            if not self._stop_event.is_set():
                for task in done:
                    if task is not tasks[2] and task.exception() is not None:
                        raise task.exception()
                # If the server closed a loop without a local Stop, end the session cleanly.
                self._stop_event.set()
            for task in pending:
                task.cancel()
            await asyncio.gather(*pending, return_exceptions=True)

    def _read_pdf_page(self, page_index: int):
        with fitz.open(self.pdf_path) as doc:
            if doc.page_count <= 0:
                raise RuntimeError("The PDF has no pages.")
            page_index = max(0, min(int(page_index), doc.page_count - 1))
            page = doc.load_page(page_index)
            text = str(page.get_text("text") or "").strip()
            scale = min(2.2, 1700.0 / max(float(page.rect.width), float(page.rect.height), 1.0))
            pix = page.get_pixmap(matrix=fitz.Matrix(scale, scale), alpha=False)
            img = Image.frombytes("RGB", (pix.width, pix.height), pix.samples)
            img.thumbnail((1700, 1700), Image.Resampling.LANCZOS)
            buff = io.BytesIO()
            img.save(buff, format="JPEG", quality=88, optimize=True)
            return page_index, text, buff.getvalue()

    def run(self):
        try:
            if not self.api_key:
                raise RuntimeError("Add a Google Gemini API key in AI Settings before starting Voice & Learn.")
            asyncio.run(self._run_live())
        except Exception as exc:
            if not self._stop_event.is_set():
                message = str(exc)
                if "402" in message or "Insufficient Balance" in message:
                    message += "\n\nThe Google AI API account/key may have insufficient balance or no billing access for this model."
                self.failed.emit(message)
        finally:
            self._stop_event.set()
            if self._input_stream is not None:
                try:
                    self._input_stream.stop()
                    self._input_stream.close()
                except Exception:
                    pass
                self._input_stream = None
            if self._speaker_thread is not None:
                try:
                    self._speaker_thread.join(timeout=1.5)
                except Exception:
                    pass
                self._speaker_thread = None
            self.status.emit("Live voice session ended.")



class LiveTutorDialog(QDialog):
    """Separate live-tutor window: push-to-talk, PDF focus pointer, and Markdown board."""
    startRequested = pyqtSignal()
    stopRequested = pyqtSignal()
    pauseRequested = pyqtSignal(bool)
    refreshRequested = pyqtSignal()
    pttStarted = pyqtSignal()
    pttStopped = pyqtSignal()
    focusOverlayVisibilityChanged = pyqtSignal(bool)
    clearFocusRequested = pyqtSignal()
    previousPageRequested = pyqtSignal()
    nextPageRequested = pyqtSignal()
    voicePreferencesChanged = pyqtSignal(str, str)
    lessonDetailChanged = pyqtSignal(str)
    teacherInstructionsChanged = pyqtSignal(str)
    textMessageRequested = pyqtSignal(str)
    manualRegionSelected = pyqtSignal(int, object, bytes)
    secondaryPreviousPageRequested = pyqtSignal()
    secondaryNextPageRequested = pyqtSignal()

    def __init__(self, parent=None):
        super().__init__(parent, Qt.WindowType.Window)
        self.setWindowTitle("Audio lesson with AI")
        self.setObjectName("liveTutorDialog")
        # The lesson window is a fixed work canvas (PDF at left, lesson board at right).
        # Arabic changes the text language, not the order of the work areas or controls.
        self.setProperty("engoForceLTRLayout", True)
        self.setLayoutDirection(Qt.LayoutDirection.LeftToRight)
        self.setMinimumSize(1040, 690)
        self.resize(1320, 830)
        # The live lesson is a focused work mode. Keep the PDF toolbar behind it
        # from receiving mouse/keyboard input while this window is open.
        # WindowModal blocks the parent PDF window without locking unrelated apps.
        self.setWindowModality(Qt.WindowModality.WindowModal)
        self.page_number = 1
        self.page_count = 1
        self.pdf_path = ""
        self._board_identity = None
        self._source_pixmap = QPixmap()
        self._secondary_source_pixmap = QPixmap()
        self.secondary_pdf_path = ""
        self.secondary_page_number = 1
        self.secondary_page_count = 1
        self.secondary_pdf_name = ""
        self._secondary_focus_page_number = None
        self._secondary_focus_box = None
        self._secondary_focus_kind = "text"
        self._focus_page_number = None
        self._focus_box = None
        self._focus_label = ""
        self._focus_kind = "text"
        self._focus_visible = True
        self._laser_phase = 0.0
        self._board_markdown = ""
        self._board_has_notes = False
        self._space_down = False
        self._session_active = False
        self._tutor_paused = False
        self._last_speaker = ""
        self._voice_loading_phase = 0
        self._voice_loading_timer = QTimer(self)
        self._voice_loading_timer.setInterval(380)
        self._voice_loading_timer.timeout.connect(self._animate_voice_loading)
        self._manual_select_mode = False
        self._manual_start_norm = None
        self._manual_drag_box = None
        self._scaled_preview_size = QSize(0, 0)
        self._primary_preview_zoom = 1.0
        self._secondary_preview_zoom = 1.0
        self._manual_region = None
        self._teaching_marks: list[dict] = []
        self._window_dark_theme = True
        self._laser_timer = QTimer(self)  # retained for compatibility; no automatic laser animation
        root = QVBoxLayout(self)
        root.setContentsMargins(14, 12, 14, 12)
        root.setSpacing(10)
        header = QHBoxLayout()
        title = QLabel("Audio lesson with AI")
        self.dialog_title_label = title
        title.setObjectName("dialogHeading")
        # Keep the header text directly on the dialog surface; no separate label tiles.
        title.setAutoFillBackground(False)
        title.setStyleSheet("background: transparent; border: none;")
        header.addWidget(title)
        header.addStretch(1)
        self.status_label = QLabel("Ready · Start the full-page lesson. Hold SPACE or type to ask about any item on the page.")
        self.status_label.setObjectName("dialogHint")
        self.status_label.setAutoFillBackground(False)
        self.status_label.setStyleSheet("background: transparent; border: none;")
        header.addWidget(self.status_label, 2)
        root.addLayout(header)
        buttons = QHBoxLayout()
        self.start_btn = QPushButton("Start full-page lesson")
        self.start_btn.setObjectName("startAction")
        self.start_btn.setIcon(make_icon("voice_learn", "#ffffff", 17))
        self.start_btn.setToolTip("Start one live lesson for the current PDF page")
        self.start_btn.clicked.connect(self.startRequested.emit)
        buttons.addWidget(self.start_btn)
        self.stop_btn = QPushButton("End conversation")
        self.stop_btn.setIcon(make_icon("stop", "#e58b8b", 16))
        self.stop_btn.clicked.connect(self.stopRequested.emit)
        self.stop_btn.setEnabled(False)
        buttons.addWidget(self.stop_btn)
        self.refresh_btn = QPushButton("Use current PDF pages")
        self.refresh_btn.setIcon(make_icon("pages", "#9fb6d8", 16))
        self.refresh_btn.setToolTip("Update Gemini with both currently displayed PDF pages when a combined tab is active")
        self.refresh_btn.clicked.connect(self.refreshRequested.emit)
        buttons.addWidget(self.refresh_btn)
        self.ptt_btn = QPushButton("Hold SPACE to talk · release to send")
        self.ptt_btn.setObjectName("talkButton")
        self.ptt_btn.setIcon(make_icon("mic", "#183b70" if str(getattr(self.parent(), "settings", QSettings()).value("ui_theme", "dark", type=str)).lower() == "light" else "#ffffff", 17))
        self.ptt_btn.setMinimumHeight(36)
        self.ptt_btn.setToolTip("Hold the Space key or hold this button while speaking. Microphone audio is not sent when released.")
        self.ptt_btn.setEnabled(False)
        self.ptt_btn.pressed.connect(self._begin_ptt)
        self.ptt_btn.released.connect(self._end_ptt)
        buttons.addWidget(self.ptt_btn, 1)
        self.pause_btn = QPushButton("Pause lesson")
        self.pause_btn.setObjectName("pauseAction")
        self.pause_btn.setIcon(make_icon("pause", "#d6deeb", 16))
        self.pause_btn.setToolTip("Pause the lesson without ending the session. Resume repeats the last point, then continues.")
        self.pause_btn.setEnabled(False)
        self.pause_btn.clicked.connect(self._toggle_tutor_pause)
        buttons.addWidget(self.pause_btn)
        root.addLayout(buttons)

        voice_row = QHBoxLayout()
        teacher_voice_label = QLabel("Teacher voice")
        teacher_voice_label.setObjectName("voiceSettingLabel")
        teacher_voice_label.setAutoFillBackground(False)
        voice_row.addWidget(teacher_voice_label)
        self.voice_combo = QComboBox()
        self.voice_combo.setMinimumWidth(150)
        self.voice_combo.addItem("Male voice · Orus", "Orus")
        self.voice_combo.addItem("Female voice · Kore", "Kore")
        self.voice_combo.setToolTip("Select the natural Gemini Live voice. Changes apply to the next session.")
        self.voice_combo.currentIndexChanged.connect(self._emit_voice_preferences)
        voice_row.addWidget(self.voice_combo)
        voice_row.addSpacing(16)
        speaking_language_label = QLabel("Speaking language")
        speaking_language_label.setObjectName("voiceSettingLabel")
        speaking_language_label.setAutoFillBackground(False)
        voice_row.addWidget(speaking_language_label)
        self.dialect_combo = QComboBox()
        self.dialect_combo.setMinimumWidth(210)
        self.dialect_combo.addItem("Egyptian Arabic · مصري", "egyptian")
        self.dialect_combo.addItem("Modern Standard Arabic · فصحى", "msa")
        self.dialect_combo.addItem("Match my language · تلقائي", "auto")
        self.dialect_combo.setToolTip("Gemini native audio infers the spoken language; this choice guides its dialect and wording.")
        self.dialect_combo.currentIndexChanged.connect(self._emit_voice_preferences)
        voice_row.addWidget(self.dialect_combo)
        voice_row.addSpacing(12)
        lesson_detail_label = QLabel("Session mode")
        lesson_detail_label.setObjectName("voiceSettingLabel")
        lesson_detail_label.setAutoFillBackground(False)
        voice_row.addWidget(lesson_detail_label)
        self.detail_combo = QComboBox()
        self.detail_combo.setMinimumWidth(150)
        self.detail_combo.addItem("شرح تفصيلي · Explain", "detailed")
        self.detail_combo.addItem("مراجعة سريعة · Quick review", "brief")
        self.detail_combo.setCurrentIndex(0)
        self.detail_combo.setToolTip("شرح لتعلّم وفهم المحتوى بالكامل، أو مراجعة سريعة لاسترجاع أهم النقاط. Applies to the next session.")
        self.detail_combo.currentIndexChanged.connect(self._emit_lesson_detail_preference)
        voice_row.addWidget(self.detail_combo)
        self.voice_setting_hint = QLabel("Saved · applies next session")
        self.voice_setting_hint.setObjectName("voiceSettingLabel")
        self.voice_setting_hint.setAutoFillBackground(False)
        voice_row.addWidget(self.voice_setting_hint)

        # Teacher personality is intentionally hidden behind a compact settings
        # icon so it does not consume vertical space in the live lesson window.
        self.teacher_preferences_btn = QToolButton()
        self.teacher_preferences_btn.setObjectName("teacherPreferencesButton")
        self.teacher_preferences_btn.setText("Teacher personality & extra instructions")
        self.teacher_preferences_btn.setIcon(make_icon("settings", "#405b83", 16))
        # Keep a visible text label beside the icon; this control must be
        # understandable without relying on a tooltip or icon recognition.
        self.teacher_preferences_btn.setToolButtonStyle(Qt.ToolButtonStyle.ToolButtonTextBesideIcon)
        self.teacher_preferences_btn.setMinimumHeight(32)
        self.teacher_preferences_btn.setMinimumWidth(220)
        self.teacher_preferences_btn.setMaximumWidth(300)
        self.teacher_preferences_btn.setSizePolicy(QSizePolicy.Policy.Minimum, QSizePolicy.Policy.Fixed)
        self.teacher_preferences_btn.setAccessibleName("Teacher personality & extra instructions")
        self.teacher_preferences_btn.setToolTip("Edit the AI teacher personality and extra instructions")
        self.teacher_preferences_btn.clicked.connect(self._open_teacher_preferences_dialog)
        voice_row.addWidget(self.teacher_preferences_btn)
        voice_row.addStretch(1)
        root.addLayout(voice_row)

        # A separate modal editor keeps custom teacher instructions accessible
        # without leaving a large text box permanently on the lesson screen.
        self.teacher_preferences_dialog = QDialog(self)
        self.teacher_preferences_dialog.setObjectName("teacherPreferencesDialog")
        self.teacher_preferences_dialog.setProperty("engoForceLTRLayout", True)
        self.teacher_preferences_dialog.setLayoutDirection(Qt.LayoutDirection.LeftToRight)
        self.teacher_preferences_dialog.setModal(True)
        self.teacher_preferences_dialog.setWindowModality(Qt.WindowModality.WindowModal)
        self.teacher_preferences_dialog.resize(590, 390)
        teacher_dialog_layout = QVBoxLayout(self.teacher_preferences_dialog)
        teacher_dialog_layout.setContentsMargins(18, 16, 18, 16)
        teacher_dialog_layout.setSpacing(10)
        self.teacher_preferences_dialog_title = QLabel("Teacher personality & instructions")
        self.teacher_preferences_dialog_title.setObjectName("dialogHeading")
        teacher_dialog_layout.addWidget(self.teacher_preferences_dialog_title)
        teacher_dialog_hint = QLabel("Your instructions are saved and included in the next lesson session.")
        teacher_dialog_hint.setObjectName("dialogHint")
        teacher_dialog_hint.setWordWrap(True)
        teacher_dialog_layout.addWidget(teacher_dialog_hint)
        self.teacher_instructions_edit = QTextEdit()
        self.teacher_instructions_edit.setObjectName("teacherInstructionsEdit")
        self.teacher_instructions_edit.setLayoutDirection(Qt.LayoutDirection.LeftToRight)
        self.teacher_instructions_edit.setAcceptRichText(False)
        self.teacher_instructions_edit.setTabChangesFocus(True)
        self.teacher_instructions_edit.setMinimumHeight(205)
        self.teacher_instructions_edit.setPlaceholderText(
            "Add instructions for your AI teacher… e.g. be patient, use Egyptian examples, explain symbols slowly, quiz me after each topic."
        )
        saved_teacher_instructions = ""
        try:
            saved_teacher_instructions = str(self.parent().settings.value("live_tutor_teacher_instructions", "", type=str) or "")[:4000]
        except Exception:
            pass
        self.teacher_instructions_edit.setPlainText(saved_teacher_instructions)
        teacher_dialog_layout.addWidget(self.teacher_instructions_edit, 1)
        self.teacher_preferences_hint = QLabel("Saved · applies next session")
        self.teacher_preferences_hint.setObjectName("dialogHint")
        teacher_dialog_layout.addWidget(self.teacher_preferences_hint)
        teacher_dialog_buttons = QHBoxLayout()
        teacher_dialog_buttons.addStretch(1)
        self.teacher_preferences_cancel_btn = QPushButton("Cancel")
        self.teacher_preferences_cancel_btn.clicked.connect(self.teacher_preferences_dialog.reject)
        teacher_dialog_buttons.addWidget(self.teacher_preferences_cancel_btn)
        self.teacher_preferences_save_btn = QPushButton("Save instructions")
        self.teacher_preferences_save_btn.setObjectName("startAction")
        self.teacher_preferences_save_btn.clicked.connect(self._save_teacher_preferences_dialog)
        teacher_dialog_buttons.addWidget(self.teacher_preferences_save_btn)
        teacher_dialog_layout.addLayout(teacher_dialog_buttons)

        focus_row = QHBoxLayout()
        self.focus_visible_checkbox = QCheckBox("Show focus rectangle")
        # The active lesson target must remain visible on the PDF page by default.
        # Learners can still turn the rectangle off manually from this checkbox.
        self.focus_visible_checkbox.setChecked(True)
        self.focus_visible_checkbox.toggled.connect(self._on_focus_visibility_toggled)
        focus_row.addWidget(self.focus_visible_checkbox)
        self.clear_focus_btn = QPushButton("Clear rectangle")
        self.clear_focus_btn.clicked.connect(self.clearFocusRequested.emit)
        focus_row.addWidget(self.clear_focus_btn)
        self.manual_select_btn = QPushButton("Select area to ask about")
        self.manual_select_btn.setCheckable(True)
        self.manual_select_btn.setToolTip("Enable, drag a box around text, handwriting, a formula, chart, or drawing, then ask by voice or text.")
        self.manual_select_btn.toggled.connect(self._toggle_manual_select)
        focus_row.addWidget(self.manual_select_btn)
        focus_row.addStretch(1)
        root.addLayout(focus_row)
        splitter = QSplitter(Qt.Orientation.Horizontal)
        splitter.setChildrenCollapsible(False)
        left = QFrame()
        left_layout = QVBoxLayout(left)
        left_layout.setContentsMargins(0, 0, 8, 0)
        page_title = QLabel("CURRENT PDF PAGE")
        page_title.setObjectName("teachBoardTitle")
        left_layout.addWidget(page_title)
        self.page_preview_row = QWidget()
        preview_row_layout = QHBoxLayout(self.page_preview_row)
        preview_row_layout.setContentsMargins(0, 0, 0, 0)
        preview_row_layout.setSpacing(8)
        primary_preview_frame = QFrame()
        primary_preview_layout = QVBoxLayout(primary_preview_frame)
        primary_preview_layout.setContentsMargins(0, 0, 0, 0)
        primary_preview_layout.setSpacing(4)
        self.primary_source_label = QLabel("PRIMARY PDF")
        self.primary_source_label.setObjectName("dialogHint")
        primary_preview_layout.addWidget(self.primary_source_label)
        self.page_label = QLabel("PDF page preview")
        self.page_label.setAlignment(Qt.AlignmentFlag.AlignCenter)
        self.page_label.setMinimumSize(1, 1)
        self.page_label.setObjectName("livePagePreview")
        self.page_scroll = QScrollArea()
        self.page_scroll.setWidgetResizable(False)
        self.page_scroll.setAlignment(Qt.AlignmentFlag.AlignCenter)
        self.page_scroll.setWidget(self.page_label)
        # Event filters are installed after the entire dialog has been constructed.
        # Installing them here can dispatch a Qt event before the supplementary
        # preview widgets below have been created.
        self.page_label.grabGesture(Qt.GestureType.PinchGesture)
        self.page_label.setFocusPolicy(Qt.FocusPolicy.StrongFocus)
        self.page_label.setMouseTracking(True)
        primary_preview_layout.addWidget(self.page_scroll, 1)
        self.page_caption = QLabel("Page 1")
        self.page_caption.setObjectName("dialogHint")
        primary_preview_layout.addWidget(self.page_caption)

        # Keep primary-page navigation directly beneath the primary PDF preview,
        # matching the supplementary PDF's navigation placement.
        primary_nav = QHBoxLayout()
        primary_nav.setContentsMargins(0, 0, 0, 0)
        primary_nav.setSpacing(6)
        self.previous_page_btn = QPushButton("←")
        self.previous_page_btn.setObjectName("pageNavArrow")
        self.previous_page_btn.setFixedSize(32, 25)
        self.previous_page_btn.setToolTip("Previous page in the primary PDF")
        self.previous_page_btn.setAccessibleName("Previous page in the primary PDF")
        self.previous_page_btn.clicked.connect(self.previousPageRequested.emit)
        self.page_position_label = QLabel("Page 1 / 1")
        self.page_position_label.setObjectName("dialogHint")
        self.page_position_label.setAlignment(Qt.AlignmentFlag.AlignCenter)
        self.next_page_btn = QPushButton("→")
        self.next_page_btn.setObjectName("pageNavArrow")
        self.next_page_btn.setFixedSize(32, 25)
        self.next_page_btn.setToolTip("Next page in the primary PDF")
        self.next_page_btn.setAccessibleName("Next page in the primary PDF")
        self.next_page_btn.clicked.connect(self.nextPageRequested.emit)
        primary_nav.addStretch(1)
        primary_nav.addWidget(self.previous_page_btn)
        primary_nav.addWidget(self.page_position_label)
        primary_nav.addWidget(self.next_page_btn)
        primary_nav.addStretch(1)
        primary_preview_layout.addLayout(primary_nav)
        preview_row_layout.addWidget(primary_preview_frame, 1)

        self.secondary_preview_frame = QFrame()
        secondary_preview_layout = QVBoxLayout(self.secondary_preview_frame)
        secondary_preview_layout.setContentsMargins(0, 0, 0, 0)
        secondary_preview_layout.setSpacing(4)
        self.secondary_source_label = QLabel("SUPPLEMENTARY PDF")
        self.secondary_source_label.setObjectName("dialogHint")
        secondary_preview_layout.addWidget(self.secondary_source_label)
        self.secondary_page_label = QLabel("Supplementary page preview")
        self.secondary_page_label.setAlignment(Qt.AlignmentFlag.AlignCenter)
        self.secondary_page_label.setMinimumSize(1, 1)
        self.secondary_page_label.setObjectName("livePagePreview")
        self.secondary_page_scroll = QScrollArea()
        self.secondary_page_scroll.setWidgetResizable(False)
        self.secondary_page_scroll.setAlignment(Qt.AlignmentFlag.AlignCenter)
        self.secondary_page_scroll.setWidget(self.secondary_page_label)
        self.secondary_page_label.grabGesture(Qt.GestureType.PinchGesture)
        secondary_preview_layout.addWidget(self.secondary_page_scroll, 1)
        self.secondary_page_caption = QLabel("Supplementary page")
        self.secondary_page_caption.setObjectName("dialogHint")
        secondary_preview_layout.addWidget(self.secondary_page_caption)
        secondary_nav = QHBoxLayout()
        self.secondary_prev_btn = QPushButton("←")
        self.secondary_prev_btn.setToolTip("Previous page in supplementary PDF")
        self.secondary_prev_btn.clicked.connect(self.secondaryPreviousPageRequested.emit)
        self.secondary_next_btn = QPushButton("→")
        self.secondary_next_btn.setToolTip("Next page in supplementary PDF")
        self.secondary_next_btn.clicked.connect(self.secondaryNextPageRequested.emit)
        secondary_nav.addWidget(self.secondary_prev_btn)
        secondary_nav.addWidget(self.secondary_next_btn)
        secondary_nav.addStretch(1)
        secondary_preview_layout.addLayout(secondary_nav)
        self.secondary_preview_frame.hide()
        preview_row_layout.addWidget(self.secondary_preview_frame, 1)
        left_layout.addWidget(self.page_preview_row, 1)
        # Middle-button auto-scroll is scoped to the PDF preview row only, so
        # it works on either displayed page without hijacking the teaching board
        # or the live transcript elsewhere in this dialog.
        self._preview_middle_auto_scroll = MiddleMouseAutoScroll(self.page_preview_row)
        splitter.addWidget(left)
        right = QSplitter(Qt.Orientation.Vertical)
        right.setChildrenCollapsible(False)
        board_frame = QFrame()
        board_layout = QVBoxLayout(board_frame)
        board_layout.setContentsMargins(0, 0, 0, 4)
        board_heading = QLabel("TEACHING BOARD · formulas and examples")
        board_heading.setObjectName("teachBoardTitle")
        board_layout.addWidget(board_heading)
        self.board_title = QLabel("Your teacher's board")
        self.board_title.setObjectName("teachBoardLesson")
        self.board_layout = QTextBrowser()
        self.board_layout.setObjectName("teachBoardText")
        self.board_layout.setLayoutDirection(Qt.LayoutDirection.LeftToRight)
        board_font = self.board_layout.font()
        board_font.setPointSizeF(10.0)
        self.board_layout.setFont(board_font)
        _set_markdown_browser(self.board_layout, "Your AI teacher will write formulas, definitions, and worked examples here when they are useful.", 9.5)
        board_layout.addWidget(self.board_title)
        board_actions = QHBoxLayout()
        self.save_board_btn = QPushButton("Save for this PDF")
        self.save_board_btn.setToolTip("Save this board inside Engo, linked to the current PDF and page.")
        self.save_board_btn.clicked.connect(lambda: self._save_current_board(show_message=True))
        board_actions.addWidget(self.save_board_btn)
        self.export_md_btn = QPushButton("Export all .md")
        self.export_md_btn.setToolTip("Export the saved teaching boards for every page of this PDF into one Markdown file.")
        self.export_md_btn.clicked.connect(self.export_board_markdown)
        board_actions.addWidget(self.export_md_btn)
        self.export_pdf_btn = QPushButton("Export all PDF")
        self.export_pdf_btn.setToolTip("Export the saved teaching boards for every page of this PDF into one PDF file.")
        self.export_pdf_btn.clicked.connect(self.export_board_pdf)
        board_actions.addWidget(self.export_pdf_btn)
        board_layout.addLayout(board_actions)
        self.board_saved_label = QLabel("Auto-save per page is on · export buttons combine notes from all pages")
        self.board_saved_label.setObjectName("dialogHint")
        board_layout.addWidget(self.board_saved_label)
        board_layout.addWidget(self.board_layout, 1)
        right.addWidget(board_frame)
        conversation_frame = QFrame()
        conversation_layout = QVBoxLayout(conversation_frame)
        conversation_layout.setContentsMargins(0, 4, 0, 0)
        conversation_heading = QLabel("LIVE TRANSCRIPT")
        conversation_heading.setObjectName("teachBoardTitle")
        conversation_layout.addWidget(conversation_heading)
        self.transcript_view = QTextBrowser()
        self.transcript_view.setObjectName("liveTranscript")
        transcript_font = self.transcript_view.font()
        transcript_font.setPointSizeF(13.0)
        self.transcript_view.setFont(transcript_font)
        self.transcript_view.setMinimumWidth(0)
        self.transcript_view.setSizePolicy(QSizePolicy.Policy.Expanding, QSizePolicy.Policy.Expanding)
        self.transcript_view.setLineWrapMode(QTextEdit.LineWrapMode.WidgetWidth)
        self.transcript_view.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        self.transcript_view.setVerticalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAsNeeded)
        self.transcript_view.setFrameShape(QFrame.Shape.NoFrame)
        self.transcript_view.document().setDocumentMargin(12)
        self._transcript_markdown = ""
        self.transcript_view.setPlaceholderText("Your speech, typed messages, and Engo AI replies appear here during the conversation.")
        conversation_layout.addWidget(self.transcript_view, 1)
        self.voice_loading_label = QLabel("Engo AI is preparing a reply")
        self.voice_loading_label.setObjectName("voiceReplyLoading")
        self.voice_loading_label.setStyleSheet("color:#8fb4ff; font-size:10.5pt; font-weight:600; background:transparent; padding:2px 10px;")
        self.voice_loading_label.hide()
        conversation_layout.addWidget(self.voice_loading_label)
        typed_row = QHBoxLayout()
        self.text_input = QLineEdit()
        self.text_input.setPlaceholderText("Type a question or tell Engo how to edit the board…")
        self.text_input.returnPressed.connect(self._send_typed_message)
        typed_row.addWidget(self.text_input, 1)
        self.send_text_btn = QPushButton("Send")
        self.send_text_btn.setObjectName("primary")
        self.send_text_btn.setToolTip("Send a typed question or board instruction to Engo AI")
        self.send_text_btn.clicked.connect(self._send_typed_message)
        typed_row.addWidget(self.send_text_btn)
        conversation_layout.addLayout(typed_row)
        right.addWidget(conversation_frame)
        right.setSizes([390, 300])
        splitter.addWidget(right)
        splitter.setSizes([540, 680])
        root.addWidget(splitter, 1)
        note = QLabel("Push-to-talk mode: Gemini receives microphone audio only while you hold SPACE or the talk button. Windows speech voices are used for local lesson playback; the AI teacher's natural voice is generated by Gemini and played through your computer's audio device. Headphones are still recommended.")
        note.setObjectName("dialogHint")
        note.setWordWrap(True)
        root.addWidget(note)
        # Install filters only after every child widget (including both PDF previews
        # and the message input) exists. Qt may deliver events during widget setup;
        # registering earlier can re-enter eventFilter with a partially-built dialog.
        for child in self.findChildren(QWidget):
            child.installEventFilter(self)
        self.set_page_navigation(1, 1)
        self._apply_window_theme(True)

    def _set_start_button_caption(self, is_ar: bool | None = None):
        """Keep the full-page lesson button caption localized in every state."""
        if is_ar is None:
            try:
                settings = getattr(self.parent(), "settings", None)
                language = str(settings.value("interface_language", "en", type=str) if settings is not None else "en")
                is_ar = language.lower().startswith("ar")
            except Exception:
                is_ar = False

        if self._session_active:
            caption = "الشرح جارٍ" if is_ar else "Conversation active"
            tooltip = "الحصة الصوتية نشطة حاليًا" if is_ar else "The live lesson is currently active"
        else:
            caption = "ابدأ شرح الصفحة بالكامل" if is_ar else "Start full-page lesson"
            tooltip = "ابدأ حصة صوتية لشرح الصفحة الحالية بالكامل" if is_ar else "Start one live lesson for the current PDF page"

        self.start_btn.setText(caption)
        self.start_btn.setToolTip(tooltip)
        self.start_btn.setAccessibleName(caption)

    def _apply_window_theme(self, enabled: bool = True):
        """Apply the exact application palette to the live lesson and its child editor."""
        parent = self.parent()
        try:
            settings = getattr(parent, "settings", None)
            if settings is not None:
                settings.sync()
            theme_name = normalize_ui_theme(
                settings.value("ui_theme", "dark", type=str) if settings is not None else "dark"
            )
            ui_language = str(
                settings.value("interface_language", "en", type=str) if settings is not None else "en"
            ).lower()
        except Exception:
            theme_name, ui_language = "dark", "en"

        t = engo_ui_theme_tokens(theme_name)
        c = {
            "bg": t["window"], "panel": t["panel"], "panel_alt": t["panel_alt"],
            "raised": t["raised"], "fg": t["text"], "muted": t["muted"],
            "field": t["input"], "border": t["border"], "accent": t["accent"],
            "accent_hover": t["accent_hover"], "hover": t["hover"],
            "pressed": t["pressed"], "selection": t["selection"],
            "selection_fg": t["selection_text"],
        }
        is_ar = ui_language.startswith("ar")
        combo_chevron_asset = "combo_chevron_light.png" if theme_name == "light" else "combo_chevron_dark.png"
        combo_chevron_path = resource_path(combo_chevron_asset).replace("\\", "/")
        dialog_title = "حصة صوتية مع AI" if is_ar else "Audio lesson with AI"
        self._set_start_button_caption(is_ar)
        self.setWindowTitle(dialog_title)
        self.setLayoutDirection(Qt.LayoutDirection.LeftToRight)
        self.teacher_preferences_dialog.setLayoutDirection(Qt.LayoutDirection.LeftToRight)
        if hasattr(self, "dialog_title_label"):
            self.dialog_title_label.setText(dialog_title)

        live_palette = QPalette(self.palette())
        for role, color in (
            (QPalette.ColorRole.Window, c["bg"]),
            (QPalette.ColorRole.WindowText, c["fg"]),
            (QPalette.ColorRole.Base, c["field"]),
            (QPalette.ColorRole.AlternateBase, c["panel"]),
            (QPalette.ColorRole.Text, c["fg"]),
            (QPalette.ColorRole.Button, c["raised"]),
            (QPalette.ColorRole.ButtonText, c["fg"]),
            (QPalette.ColorRole.Highlight, c["selection"]),
            (QPalette.ColorRole.HighlightedText, c["selection_fg"]),
            (QPalette.ColorRole.ToolTipBase, c["panel"]),
            (QPalette.ColorRole.ToolTipText, c["fg"]),
            (QPalette.ColorRole.PlaceholderText, c["muted"]),
        ):
            live_palette.setColor(role, QColor(color))
        self.setPalette(live_palette)
        self.setAutoFillBackground(True)
        for child in self.findChildren(QWidget):
            child.setPalette(live_palette)
            if isinstance(child, (QFrame, QScrollArea)):
                child.setAutoFillBackground(True)

        self.setStyleSheet(f"""
            QDialog#liveTutorDialog {{ background-color: {c['bg']}; color: {c['fg']}; }}
            QDialog#liveTutorDialog QWidget {{ color: {c['fg']}; }}
            QDialog#liveTutorDialog QFrame {{ background-color: {c['panel']}; border-color: {c['border']}; }}
            QDialog#liveTutorDialog QLabel {{ color: {c['fg']}; background: transparent; }}
            QDialog#liveTutorDialog QLabel#dialogHint {{ color: {c['muted']}; }}
            QDialog#liveTutorDialog QTextBrowser,
            QDialog#liveTutorDialog QTextEdit,
            QDialog#liveTutorDialog QLineEdit {{ background-color: {c['field']}; color: {c['fg']};
                border: 1px solid {c['border']}; border-radius: 6px; padding: 6px;
                selection-background-color: {c['selection']}; selection-color: {c['selection_fg']}; }}
            QDialog#liveTutorDialog QFrame#teacherPreferencesBox {{ background: transparent; border: 0; }}
            QDialog#liveTutorDialog QTextBrowser#liveTranscript {{ background-color: {c['field']};
                color: {c['fg']}; border: 1px solid {c['border']}; border-radius: 8px; padding: 0px; }}
            QDialog#liveTutorDialog QTextBrowser#teachBoardText {{ background-color: {c['field']};
                color: {c['fg']}; border: 1px solid {c['border']}; }}
            QDialog#liveTutorDialog QPushButton,
            QDialog#liveTutorDialog QToolButton {{ background-color: {c['raised']}; color: {c['fg']};
                border: 1px solid {c['border']}; border-radius: 6px; padding: 6px 10px; }}
            QDialog#liveTutorDialog QPushButton:hover,
            QDialog#liveTutorDialog QToolButton:hover {{ background-color: {c['hover']};
                color: {c['fg']}; border-color: {c['accent']}; }}
            QDialog#liveTutorDialog QPushButton:pressed,
            QDialog#liveTutorDialog QToolButton:pressed {{ background-color: {c['pressed']}; }}
            QDialog#liveTutorDialog QPushButton:disabled {{ background-color: {c['panel_alt']};
                color: {c['muted']}; border-color: {c['border']}; }}
            QDialog#liveTutorDialog QPushButton#primary,
            QDialog#liveTutorDialog QPushButton#startAction {{ background-color: {c['accent']};
                color: #ffffff; border: 1px solid {c['accent']}; font-weight: 700; }}
            QDialog#liveTutorDialog QPushButton#primary:hover,
            QDialog#liveTutorDialog QPushButton#startAction:hover {{ background-color: {c['accent_hover']};
                color: #ffffff; border-color: {c['accent_hover']}; }}
            QDialog#liveTutorDialog QPushButton#talkButton {{ background-color: {c['raised']};
                color: {c['fg']}; border: 1px solid {c['border']}; font-weight: 700; }}
            QDialog#liveTutorDialog QPushButton#talkButton:hover {{ background-color: {c['hover']};
                border-color: {c['accent']}; }}
            QDialog#liveTutorDialog QPushButton#talkListening {{ background-color: #d92d3e;
                color: #ffffff; border: 1px solid #ff9aa4; font-weight: 800; }}
            QDialog#liveTutorDialog QPushButton#pauseAction:disabled {{ background-color: {c['panel_alt']};
                color: {c['muted']}; border-color: {c['border']}; }}
            QDialog#liveTutorDialog QComboBox {{ background-color: {c['field']}; color: {c['fg']};
                border: 1px solid {c['border']}; border-radius: 5px; padding: 5px 27px 5px 7px; }}
            QDialog#liveTutorDialog QComboBox::drop-down {{ subcontrol-origin: padding; subcontrol-position: top right;
                width: 24px; background: {c['raised']}; border-left: 1px solid {c['border']}; }}
            QDialog#liveTutorDialog QComboBox::down-arrow {{ image: url("{combo_chevron_path}"); width: 12px; height: 8px; border: 0; }}
            QDialog#liveTutorDialog QComboBox:hover {{ background-color: {c['hover']};
                border-color: {c['accent']}; }}
            QDialog#liveTutorDialog QComboBox QAbstractItemView,
            QDialog#liveTutorDialog QComboBox QAbstractItemView::viewport {{
                background-color: {c['field']}; color: {c['fg']}; border: 1px solid {c['border']};
                selection-background-color: {c['selection']}; selection-color: {c['selection_fg']}; outline: 0; }}
            QDialog#liveTutorDialog QCheckBox {{ color: {c['fg']}; spacing: 6px; }}
            QDialog#liveTutorDialog QToolTip {{ background-color: {c['panel']}; color: {c['fg']};
                border: 1px solid {c['border']}; padding: 5px 7px; }}
        """)
        self.teacher_preferences_dialog.setPalette(live_palette)
        self.teacher_preferences_dialog.setAutoFillBackground(True)
        self.teacher_preferences_dialog.setStyleSheet(f"""
            QDialog#teacherPreferencesDialog {{ background-color: {c['bg']}; color: {c['fg']}; }}
            QDialog#teacherPreferencesDialog QWidget {{ color: {c['fg']}; }}
            QDialog#teacherPreferencesDialog QLabel {{ color: {c['fg']}; background: transparent; }}
            QDialog#teacherPreferencesDialog QTextEdit {{ background-color: {c['field']}; color: {c['fg']};
                border: 1px solid {c['border']}; border-radius: 7px; padding: 8px;
                selection-background-color: {c['selection']}; selection-color: {c['selection_fg']}; }}
            QDialog#teacherPreferencesDialog QPushButton {{ background-color: {c['raised']}; color: {c['fg']};
                border: 1px solid {c['border']}; border-radius: 6px; padding: 7px 14px; }}
            QDialog#teacherPreferencesDialog QPushButton:hover {{ background-color: {c['hover']};
                border-color: {c['accent']}; }}
            QDialog#teacherPreferencesDialog QPushButton#startAction {{ background-color: {c['accent']};
                color: #ffffff; border-color: {c['accent']}; font-weight: 700; }}
        """)
        try:
            icon_fg = "#ffffff" if getattr(self, "_space_down", False) else c["fg"]
            self.ptt_btn.setIcon(make_icon("mic", icon_fg, 17))
            self.start_btn.setIcon(make_icon("voice_learn", "#ffffff", 17))
            self.stop_btn.setIcon(make_icon("stop", "#e58b8b" if theme_name != "light" else "#a64b59", 16))
            self.refresh_btn.setIcon(make_icon("pages", c["accent"], 16))
            self.pause_btn.setIcon(make_icon("play" if self._tutor_paused else "pause", c["fg"], 16))
        except (AttributeError, RuntimeError):
            pass

    def configure_window_theme(self, enabled: bool = True):
        # Kept as a compatibility method for callers from older builds; the dialog
        # now always follows the application theme and has no independent toggle.
        self._apply_window_theme(True)

    def _open_teacher_preferences_dialog(self):
        parent = self.parent()
        language = "en"
        try:
            language = str(parent.settings.value("interface_language", "en", type=str) or "en").lower()
        except Exception:
            pass
        is_ar = language == "ar"
        self.teacher_preferences_dialog.setWindowTitle("شخصية المدرّس والتعليمات الإضافية" if is_ar else "Teacher personality & extra instructions")
        self.teacher_preferences_dialog_title.setText("شخصية المدرّس والتعليمات الإضافية" if is_ar else "Teacher personality & extra instructions")
        self.teacher_preferences_btn.setText("شخصية المدرّس والتعليمات الإضافية" if is_ar else "Teacher personality & extra instructions")
        self.teacher_preferences_btn.setAccessibleName("شخصية المدرّس والتعليمات الإضافية" if is_ar else "Teacher personality & extra instructions")
        self.teacher_instructions_edit.setPlaceholderText(
            "اكتب أسلوب المدرّس والتعليمات الإضافية… مثال: كن صبورًا، استخدم أمثلة مصرية، واشرح الرموز ببطء." if is_ar else
            "Add instructions for your AI teacher… e.g. be patient, use Egyptian examples, explain symbols slowly, quiz me after each topic."
        )
        self.teacher_preferences_save_btn.setText("حفظ التعليمات" if is_ar else "Save instructions")
        self.teacher_preferences_cancel_btn.setText("إلغاء" if is_ar else "Cancel")
        self.teacher_preferences_hint.setText("يتم الحفظ وتطبيق التعليمات في الحصة القادمة" if is_ar else "Saved · applies next session")
        self.teacher_preferences_btn.setToolTip("تعديل شخصية المدرّس والتعليمات الإضافية" if is_ar else "Edit the AI teacher personality and extra instructions")
        self.teacher_preferences_dialog.show()
        self.teacher_preferences_dialog.raise_()
        self.teacher_preferences_dialog.activateWindow()
        self.teacher_instructions_edit.setFocus()

    def _save_teacher_preferences_dialog(self):
        self._emit_teacher_instructions()
        self.teacher_preferences_dialog.accept()

    def current_teacher_instructions(self) -> str:
        return str(self.teacher_instructions_edit.toPlainText() or "").strip()[:4000]

    def configure_teacher_instructions(self, value: str):
        value = str(value or "")[:4000]
        if self.teacher_instructions_edit.toPlainText() != value:
            self.teacher_instructions_edit.blockSignals(True)
            self.teacher_instructions_edit.setPlainText(value)
            self.teacher_instructions_edit.blockSignals(False)

    def _emit_teacher_instructions(self):
        value = self.current_teacher_instructions()
        try:
            is_ar = str(self.parent().settings.value("interface_language", "en", type=str) or "en").lower() == "ar"
        except Exception:
            is_ar = False
        self.teacher_preferences_hint.setText("تم الحفظ · يُطبّق في الحصة القادمة" if is_ar else "Saved · applies next session")
        self.teacherInstructionsChanged.emit(value)
        if self._session_active:
            self.status_label.setText("تم حفظ تعليمات المدرّس · ستُطبق في الحصة القادمة." if is_ar else "Teacher instructions saved · they will apply to the next session.")

    def configure_voice_preferences(self, voice_name: str = "Orus", speaking_style: str = "egyptian", lesson_detail: str = "detailed"):
        voice_index = self.voice_combo.findData(str(voice_name or "Orus"))
        style_index = self.dialect_combo.findData(str(speaking_style or "egyptian"))
        detail_index = self.detail_combo.findData(str(lesson_detail or "detailed"))
        self.voice_combo.blockSignals(True)
        self.dialect_combo.blockSignals(True)
        self.detail_combo.blockSignals(True)
        self.voice_combo.setCurrentIndex(voice_index if voice_index >= 0 else 0)
        self.dialect_combo.setCurrentIndex(style_index if style_index >= 0 else 0)
        self.detail_combo.setCurrentIndex(detail_index if detail_index >= 0 else 1)
        self.voice_combo.blockSignals(False)
        self.dialect_combo.blockSignals(False)
        self.detail_combo.blockSignals(False)

    def current_lesson_detail(self) -> str:
        return str(self.detail_combo.currentData() or "detailed")

    def current_voice_name(self) -> str:
        return str(self.voice_combo.currentData() or "Orus")

    def current_speaking_style(self) -> str:
        return str(self.dialect_combo.currentData() or "egyptian")

    def _emit_voice_preferences(self, *_args):
        self.voice_setting_hint.setText("Saved · applies next session")
        self.voicePreferencesChanged.emit(self.current_voice_name(), self.current_speaking_style())
        if self._session_active:
            self.status_label.setText("Voice/language preference saved; it will apply when you start the next session.")

    def _emit_lesson_detail_preference(self, *_args):
        self.voice_setting_hint.setText("Saved · applies next session")
        self.lessonDetailChanged.emit(self.current_lesson_detail())
        if self._session_active:
            self.status_label.setText("Lesson detail preference saved; it will apply when you start the next session.")

    def set_page_navigation(self, current_page: int, page_count: int):
        self.page_number = max(1, int(current_page or 1))
        self.page_count = max(1, int(page_count or 1))
        self.page_position_label.setText(f"Page {self.page_number} / {self.page_count}")
        self.previous_page_btn.setEnabled(self.page_number > 1)
        self.next_page_btn.setEnabled(self.page_number < self.page_count)

    def event(self, event):
        if event.type() in (QEvent.Type.WindowDeactivate, QEvent.Type.ApplicationDeactivate):
            if self._space_down:
                self._end_ptt()
        return super().event(event)

    def _begin_ptt(self):
        if not self._session_active or self._tutor_paused or self._space_down:
            return
        self._space_down = True
        self.ptt_btn.setObjectName("talkListening")
        self.ptt_btn.setIcon(make_icon("mic", "#ffffff", 17))
        self.ptt_btn.style().unpolish(self.ptt_btn)
        self.ptt_btn.style().polish(self.ptt_btn)
        self.ptt_btn.setText("LISTENING · RELEASE SPACE TO SEND")
        self.status_label.setText("Listening · release Space to send your question")
        self.pttStarted.emit()

    def _end_ptt(self):
        if not self._space_down:
            return
        self._space_down = False
        self.ptt_btn.setObjectName("talkButton")
        try:
            theme_name = str(self.parent().settings.value("ui_theme", "dark", type=str) or "dark").lower()
        except Exception:
            theme_name = "dark"
        self.ptt_btn.setIcon(make_icon("mic", "#183b70" if theme_name == "light" else "#ffffff", 17))
        self.ptt_btn.style().unpolish(self.ptt_btn)
        self.ptt_btn.style().polish(self.ptt_btn)
        self.ptt_btn.setText("Hold SPACE to talk · release to send")
        if self._session_active:
            self.status_label.setText("Processing your question…")
        self.pttStopped.emit()

    def _toggle_tutor_pause(self):
        if not self._session_active:
            return
        self._tutor_paused = not self._tutor_paused
        if self._tutor_paused:
            if self._space_down:
                self._end_ptt()
            self.pause_btn.setText("Resume & repeat last point")
            self.pause_btn.setIcon(make_icon("play", "#ffffff", 16))
            self.ptt_btn.setEnabled(False)
            self.text_input.setEnabled(False)
            self.send_text_btn.setEnabled(False)
            self.status_label.setText("Lesson paused · your conversation is still connected")
        else:
            self.pause_btn.setText("Pause lesson")
            self.pause_btn.setIcon(make_icon("pause", "#d6deeb", 16))
            self.ptt_btn.setEnabled(True)
            self.text_input.setEnabled(True)
            self.send_text_btn.setEnabled(True)
            self.status_label.setText("Resuming · Engo will repeat the last point, then continue")
        self.pauseRequested.emit(self._tutor_paused)

    def _toggle_manual_select(self, enabled: bool):
        self._manual_select_mode = bool(enabled)
        self._manual_start_norm = None
        self._manual_drag_box = None
        self.page_label.setCursor(Qt.CursorShape.CrossCursor if enabled else Qt.CursorShape.ArrowCursor)
        self.status_label.setText("Drag a rectangle around the exact area, then ask about it by voice or text." if enabled else "Manual selection is off.")
        self._rescale_preview()

    def _preview_point_to_norm(self, point):
        size = self._scaled_preview_size
        if size.width() <= 0 or size.height() <= 0:
            return None
        ox = (self.page_label.width() - size.width()) / 2.0
        oy = (self.page_label.height() - size.height()) / 2.0
        px, py = float(point.x()) - ox, float(point.y()) - oy
        if px < 0 or py < 0 or px > size.width() or py > size.height():
            return None
        return (max(0.0, min(1.0, px / size.width())), max(0.0, min(1.0, py / size.height())))

    def _make_manual_crop(self, box):
        if self._source_pixmap.isNull():
            return b""
        try:
            buff = QBuffer()
            buff.open(QIODevice.OpenModeFlag.WriteOnly)
            self._source_pixmap.save(buff, "PNG")
            buff.close()
            img = Image.open(io.BytesIO(bytes(buff.data()))).convert("RGB")
            x, y, w, h = box
            x0 = max(0, min(img.width - 1, int(x * img.width)))
            y0 = max(0, min(img.height - 1, int(y * img.height)))
            x1 = max(x0 + 1, min(img.width, int((x + w) * img.width)))
            y1 = max(y0 + 1, min(img.height, int((y + h) * img.height)))
            out = io.BytesIO()
            img.crop((x0, y0, x1, y1)).save(out, format="JPEG", quality=92, optimize=True)
            return out.getvalue()
        except Exception:
            return b""

    def eventFilter(self, obj, event):
        if obj is self.page_label and self._manual_select_mode:
            if event.type() == QEvent.Type.MouseButtonPress and event.button() == Qt.MouseButton.LeftButton:
                point = self._preview_point_to_norm(event.position().toPoint())
                if point is not None:
                    self._manual_start_norm = point
                    self._manual_drag_box = [point[0], point[1], 0.0, 0.0]
                    self._rescale_preview()
                    event.accept()
                    return True
            elif event.type() == QEvent.Type.MouseMove and self._manual_start_norm is not None:
                point = self._preview_point_to_norm(event.position().toPoint())
                if point is not None:
                    x0, y0 = self._manual_start_norm
                    self._manual_drag_box = [min(x0, point[0]), min(y0, point[1]), abs(point[0] - x0), abs(point[1] - y0)]
                    self._rescale_preview()
                    event.accept()
                    return True
            elif event.type() == QEvent.Type.MouseButtonRelease and event.button() == Qt.MouseButton.LeftButton and self._manual_start_norm is not None:
                point = self._preview_point_to_norm(event.position().toPoint())
                start = self._manual_start_norm
                self._manual_start_norm = None
                self._manual_drag_box = None
                if point is not None:
                    x0, y0 = start
                    box = [min(x0, point[0]), min(y0, point[1]), abs(point[0] - x0), abs(point[1] - y0)]
                    if box[2] >= 0.012 and box[3] >= 0.008:
                        self._focus_page_number = self.page_number
                        self._focus_box = list(box)
                        self._focus_label = "Manually selected region"
                        self._focus_kind = "manual"
                        crop = self._make_manual_crop(box)
                        self._manual_region = {"page_index": self.page_number - 1, "box": list(box), "image": crop}
                        self.manualRegionSelected.emit(self.page_number - 1, list(box), crop)
                        self.status_label.setText("Area selected · ask about it by holding SPACE or typing below.")
                    else:
                        self.status_label.setText("Selection too small. Drag a bigger rectangle around the content.")
                self.manual_select_btn.blockSignals(True)
                self.manual_select_btn.setChecked(False)
                self.manual_select_btn.blockSignals(False)
                self._manual_select_mode = False
                self.page_label.setCursor(Qt.CursorShape.ArrowCursor)
                self._rescale_preview()
                event.accept()
                return True
        # Use guarded lookups and identity checks: eventFilter can be re-entered by
        # Qt during construction, and future optional preview layouts must not turn
        # an otherwise harmless event into an AttributeError / application crash.
        secondary_scroll = getattr(self, "secondary_page_scroll", None)
        secondary_label = getattr(self, "secondary_page_label", None)
        primary_scroll = getattr(self, "page_scroll", None)
        primary_label = getattr(self, "page_label", None)
        preview_is_secondary = (
            (secondary_scroll is not None and obj is secondary_scroll.viewport())
            or (secondary_label is not None and obj is secondary_label)
        )
        preview_is_primary = (
            (primary_scroll is not None and obj is primary_scroll.viewport())
            or (primary_label is not None and obj is primary_label)
        )
        if event.type() == QEvent.Type.Gesture and (preview_is_primary or preview_is_secondary):
            try:
                pinch = event.gesture(Qt.GestureType.PinchGesture)
                if pinch and pinch.state() == Qt.GestureState.GestureUpdated:
                    self._zoom_preview(float(pinch.scaleFactor()), secondary=preview_is_secondary)
                    event.accept()
                    return True
            except Exception:
                pass
        if event.type() == QEvent.Type.NativeGesture and (preview_is_primary or preview_is_secondary):
            try:
                if event.gestureType() == Qt.NativeGestureType.ZoomNativeGesture:
                    factor = 1.0 + float(event.value())
                    if factor > 0.05:
                        self._zoom_preview(factor, secondary=preview_is_secondary)
                        event.accept()
                        return True
            except Exception:
                pass
        if (preview_is_primary or preview_is_secondary) and event.type() == QEvent.Type.Wheel:
            if self._scroll_preview_from_wheel(event, secondary=preview_is_secondary):
                event.accept()
                return True
        if obj is self.page_label and event.type() == QEvent.Type.KeyPress:
            if event.key() == Qt.Key.Key_Left:
                self.previousPageRequested.emit()
                return True
            if event.key() == Qt.Key.Key_Right:
                self.nextPageRequested.emit()
                return True
        if event.type() in (QEvent.Type.WindowDeactivate, QEvent.Type.ApplicationDeactivate):
            if self._space_down:
                self._end_ptt()
        if event.type() in (QEvent.Type.KeyPress, QEvent.Type.KeyRelease):
            try:
                is_space = event.key() == Qt.Key.Key_Space
                auto_repeat = bool(event.isAutoRepeat())
            except Exception:
                is_space, auto_repeat = False, False
            # Preserve normal spaces while typing a message; Space is push-to-talk elsewhere in the tutor window.
            if is_space and obj is self.text_input and self.text_input.hasFocus():
                return super().eventFilter(obj, event)
            if is_space and self._session_active and not self._tutor_paused and self.isVisible() and self.isActiveWindow():
                if event.type() == QEvent.Type.KeyPress:
                    if not auto_repeat:
                        self._begin_ptt()
                    return True
                if event.type() == QEvent.Type.KeyRelease:
                    if not auto_repeat:
                        self._end_ptt()
                    return True
        return super().eventFilter(obj, event)

    def _send_typed_message(self):
        message = self.text_input.text().strip()
        if not message:
            return
        if self._tutor_paused:
            self.set_status("Resume the lesson before sending a typed message.")
            return
        if not self._session_active:
            self.set_status("Start the Voice & Learn session before sending a message.")
            return
        self.textMessageRequested.emit(message)
        self.append_transcript("You (typed)", message)
        self.text_input.clear()
        self.set_status("Sending your message to Engo AI…")

    def apply_board_action(self, mode: str, title: str, content: str):
        mode = str(mode or "append").strip().lower()
        title = str(title or "Lesson notes").strip()
        content = str(content or "").strip()
        if mode == "clear":
            self._board_markdown = ""
            self._board_has_notes = False
            self.board_title.setText(f"PAGE {self.page_number} NOTES · empty board")
            self.board_layout.clear()
            try:
                if self._board_identity:
                    with sqlite3.connect(self._board_store_path(), timeout=5) as conn:
                        conn.execute("DELETE FROM lesson_boards WHERE pdf_path=? AND page_number=?", self._board_identity)
                        conn.commit()
            except Exception:
                pass
            self.board_saved_label.setText("Board cleared by Engo AI · no saved notes remain for this page")
            return
        if not content:
            return
        if mode == "replace":
            self._board_markdown = (f"## {title}\n\n{content}" if title else content).strip()
            self._board_has_notes = True
            self.board_title.setText(f"PAGE {self.page_number} NOTES · edited by Engo AI")
            _set_markdown_browser(self.board_layout, self._board_markdown, 9.5)
            self.board_layout.verticalScrollBar().setValue(0)
            self._save_current_board(show_message=False)
            return
        self.update_board(title, content)

    def _on_focus_visibility_toggled(self, visible: bool):
        self._focus_visible = bool(visible)
        self._laser_timer.stop()
        self._rescale_preview()
        self._rescale_secondary_preview()
        self.focusOverlayVisibilityChanged.emit(bool(visible))

    def set_focus_overlay_visible(self, visible: bool):
        self._focus_visible = bool(visible)
        self.focus_visible_checkbox.blockSignals(True)
        self.focus_visible_checkbox.setChecked(bool(visible))
        self.focus_visible_checkbox.blockSignals(False)
        self._laser_timer.stop()
        self._rescale_preview()
        self._rescale_secondary_preview()

    def clear_focus(self):
        self._focus_page_number = None
        self._focus_box = None
        self._focus_label = ""
        self._focus_kind = "text"
        self._manual_region = None
        self._secondary_focus_page_number = None
        self._secondary_focus_box = None
        self._laser_timer.stop()
        self._rescale_preview()
        self._rescale_secondary_preview()

    def _advance_preview_laser(self):
        # Deliberate no-op: the laser follows the focus target supplied by Gemini and
        # must not wander around randomly while the explanation is stationary.
        self._laser_timer.stop()

    def _board_store_path(self) -> str:
        root = QStandardPaths.writableLocation(QStandardPaths.StandardLocation.AppDataLocation)
        if not root:
            root = str(Path.home() / ".engopdfviewer")
        os.makedirs(root, exist_ok=True)
        return os.path.join(root, "lesson_boards.sqlite3")

    def _save_current_board(self, show_message: bool = False):
        identity = self._board_identity
        markdown = str(self._board_markdown or "").strip()
        if not identity or not identity[0] or not markdown:
            if show_message:
                QMessageBox.information(self, "Save lesson board", "There are no lesson notes to save yet.")
            return False
        try:
            with sqlite3.connect(self._board_store_path(), timeout=5) as conn:
                conn.execute("""CREATE TABLE IF NOT EXISTS lesson_boards (
                    pdf_path TEXT NOT NULL, page_number INTEGER NOT NULL,
                    title TEXT NOT NULL DEFAULT '', markdown TEXT NOT NULL,
                    updated_at TEXT NOT NULL, PRIMARY KEY (pdf_path, page_number))""")
                conn.execute("""INSERT INTO lesson_boards(pdf_path, page_number, title, markdown, updated_at)
                    VALUES(?,?,?,?,?) ON CONFLICT(pdf_path, page_number) DO UPDATE SET
                    title=excluded.title, markdown=excluded.markdown, updated_at=excluded.updated_at""",
                    (identity[0], int(identity[1]), self.board_title.text(), markdown,
                     time.strftime("%Y-%m-%d %H:%M:%S")))
                conn.commit()
            self.board_saved_label.setText(f"Saved inside Engo · page {identity[1]} · auto-save on")
            if show_message:
                QMessageBox.information(self, "Lesson board saved", "These notes are saved locally inside Engo and linked to this PDF and page.")
            return True
        except Exception as exc:
            self.board_saved_label.setText("Could not save board automatically")
            if show_message:
                QMessageBox.warning(self, "Save lesson board", f"Could not save the board locally:\n{exc}")
            return False

    def _load_board_for_identity(self, identity):
        self._board_markdown = ""
        self._board_has_notes = False
        self.board_title.setText(f"PAGE {identity[1]} NOTES · cumulative summary")
        default_text = "The tutor will collect this page's main points, formulas, and examples here."
        try:
            db_path = self._board_store_path()
            if os.path.exists(db_path):
                with sqlite3.connect(db_path, timeout=5) as conn:
                    conn.execute("""CREATE TABLE IF NOT EXISTS lesson_boards (
                        pdf_path TEXT NOT NULL, page_number INTEGER NOT NULL,
                        title TEXT NOT NULL DEFAULT '', markdown TEXT NOT NULL,
                        updated_at TEXT NOT NULL, PRIMARY KEY (pdf_path, page_number))""")
                    row = conn.execute("SELECT title, markdown, updated_at FROM lesson_boards WHERE pdf_path=? AND page_number=?",
                                       (identity[0], int(identity[1]))).fetchone()
                if row and str(row[1] or "").strip():
                    self.board_title.setText(str(row[0] or f"PAGE {identity[1]} NOTES · saved board"))
                    self._board_markdown = str(row[1])
                    self._board_has_notes = True
                    _set_markdown_browser(self.board_layout, self._board_markdown, 9.5)
                    self.board_saved_label.setText(f"Restored saved board · page {identity[1]} · {row[2]}")
                    self.board_layout.verticalScrollBar().setValue(self.board_layout.verticalScrollBar().maximum())
                    return
        except Exception:
            pass
        _set_markdown_browser(self.board_layout, default_text, 9.5)
        self.board_saved_label.setText("Auto-save per page is on · export buttons combine notes from all pages")

    def _collect_all_boards_for_pdf(self):
        """Return all saved lesson boards for this PDF in page order, including current unsaved edits."""
        if not self.pdf_path:
            return []
        pdf_key = os.path.normcase(os.path.abspath(self.pdf_path))
        self._save_current_board(show_message=False)
        rows_by_page = {}
        db_path = self._board_store_path()
        try:
            with sqlite3.connect(db_path, timeout=5) as conn:
                conn.execute("""CREATE TABLE IF NOT EXISTS lesson_boards (
                    pdf_path TEXT NOT NULL, page_number INTEGER NOT NULL,
                    title TEXT NOT NULL DEFAULT '', markdown TEXT NOT NULL,
                    updated_at TEXT NOT NULL, PRIMARY KEY (pdf_path, page_number))""")
                rows = conn.execute(
                    "SELECT page_number, title, markdown, updated_at FROM lesson_boards WHERE pdf_path=? ORDER BY page_number",
                    (pdf_key,)
                ).fetchall()
            for number, title, markdown, updated_at in rows:
                if str(markdown or "").strip():
                    rows_by_page[int(number)] = {
                        "page": int(number), "title": str(title or "Lesson notes"),
                        "markdown": str(markdown).strip(), "updated_at": str(updated_at or "")
                    }
        except Exception as exc:
            self.board_saved_label.setText(f"Could not load all saved boards: {exc}")
        # The current page may have edits not persisted yet (e.g. the user exports immediately).
        current_markdown = str(self._board_markdown or "").strip()
        if self._board_identity and self._board_identity[0] == pdf_key and current_markdown:
            rows_by_page[int(self.page_number)] = {
                "page": int(self.page_number), "title": self.board_title.text() or "Lesson notes",
                "markdown": current_markdown, "updated_at": time.strftime("%Y-%m-%d %H:%M:%S")
            }
        return [rows_by_page[k] for k in sorted(rows_by_page)]

    def _combined_board_markdown(self, boards):
        source_stem = Path(self.pdf_path).stem if self.pdf_path else "Engo"
        parts = [f"# {source_stem} — Complete Lesson Boards", "", f"Pages with saved notes: {len(boards)}", ""]
        for item in boards:
            parts.extend([
                "---", "", f"# Page {item['page']} — {item['title']}", "",
                item["markdown"].strip(), ""
            ])
        return "\n".join(parts).strip() + "\n"

    def export_board_markdown(self):
        boards = self._collect_all_boards_for_pdf()
        if not boards:
            QMessageBox.information(self, "Export lesson boards", "No saved lesson notes were found for this PDF. Start a lesson first.")
            return
        source_stem = Path(self.pdf_path).stem if self.pdf_path else "Engo"
        default_path = str(Path.home() / f"{source_stem}_all_pages_lesson_boards.md")
        path = _engo_file_dialog(
            self, "Export all lesson boards for this PDF as Markdown", "تصدير جميع لوحات الدرس لهذا الملف بصيغة Markdown", default_path,
            "Markdown files (*.md);;All files (*.*)", save=True)
        if not path:
            return
        if not path.lower().endswith(".md"):
            path += ".md"
        try:
            Path(path).write_text(self._combined_board_markdown(boards), encoding="utf-8")
            self.board_saved_label.setText(f"All pages exported to Markdown · {len(boards)} pages · {path}")
        except Exception as exc:
            QMessageBox.warning(self, "Export Markdown", f"Could not export all lesson boards:\n{exc}")

    def export_board_pdf(self):
        boards = self._collect_all_boards_for_pdf()
        if not boards:
            QMessageBox.information(self, "Export lesson boards", "No saved lesson notes were found for this PDF. Start a lesson first.")
            return
        source_stem = Path(self.pdf_path).stem if self.pdf_path else "Engo"
        default_path = str(Path.home() / f"{source_stem}_all_pages_lesson_boards.pdf")
        path = _engo_file_dialog(
            self, "Export all lesson boards for this PDF as PDF", "تصدير جميع لوحات الدرس لهذا الملف بصيغة PDF", default_path,
            "PDF files (*.pdf)", save=True)
        if not path:
            return
        if not path.lower().endswith(".pdf"):
            path += ".pdf"
        try:
            writer = QPdfWriter(path)
            writer.setTitle(f"{source_stem} — Complete Lesson Boards")
            writer.setCreator(APP_NAME)
            writer.setResolution(96)
            writer.setPageSize(QPageSize(QPageSize.PageSizeId.A4))
            writer.setPageMargins(QMarginsF(18, 18, 18, 18))
            doc = QTextDocument()
            doc.setDefaultFont(QFont("Segoe UI", 10))
            doc.setDocumentMargin(20)
            _set_markdown_document(doc, self._combined_board_markdown(boards), 12.0)
            doc.setPageSize(QSizeF(writer.width(), writer.height()))
            doc.print(writer)
            self.board_saved_label.setText(f"All pages exported to PDF · {len(boards)} pages of notes · {path}")
        except Exception as exc:
            QMessageBox.warning(self, "Export PDF", f"Could not export all lesson boards to PDF:\n{exc}")

    def set_page_preview(self, image_bytes: bytes, page_number: int, page_count: int | None = None):
        new_page = int(page_number)
        pdf_key = os.path.normcase(os.path.abspath(self.pdf_path)) if self.pdf_path else ""
        new_identity = (pdf_key, new_page) if pdf_key else None
        if new_identity != self._board_identity and new_identity is not None:
            self._save_current_board(show_message=False)
            self._board_identity = new_identity
            self._load_board_for_identity(new_identity)
            self._focus_page_number = None
            self._focus_box = None
            self._focus_label = ""
            self._manual_region = None
        if page_count is not None:
            self.set_page_navigation(new_page, page_count)
        elif new_page != self.page_number:
            self.set_page_navigation(new_page, self.page_count)
        pixmap = QPixmap()
        pixmap.loadFromData(bytes(image_bytes or b""))
        if not pixmap.isNull():
            self._source_pixmap = pixmap
        self.page_number = new_page
        self.page_caption.setText(f"Current PDF page · {self.page_number}")
        self._rescale_preview()

    def set_secondary_page_preview(self, image_bytes: bytes, page_number: int, page_count: int,
                                   pdf_path: str = "", source_name: str = "Supplementary PDF"):
        self.secondary_pdf_path = os.path.abspath(pdf_path) if pdf_path else self.secondary_pdf_path
        self.secondary_pdf_name = str(source_name or "Supplementary PDF")
        self.secondary_page_number = max(1, int(page_number or 1))
        self.secondary_page_count = max(1, int(page_count or 1))
        pixmap = QPixmap()
        pixmap.loadFromData(bytes(image_bytes or b""))
        if not pixmap.isNull():
            self._secondary_source_pixmap = pixmap
        self.secondary_source_label.setText(f"SUPPLEMENTARY · {self.secondary_pdf_name}")
        self.secondary_page_caption.setText(f"Page {self.secondary_page_number} / {self.secondary_page_count}")
        self.secondary_prev_btn.setEnabled(self.secondary_page_number > 1)
        self.secondary_next_btn.setEnabled(self.secondary_page_number < self.secondary_page_count)
        self.secondary_preview_frame.show()
        self._rescale_preview()
        self._rescale_secondary_preview()

    def clear_secondary_page_preview(self):
        self.secondary_pdf_path = ""
        self.secondary_pdf_name = ""
        self._secondary_source_pixmap = QPixmap()
        self._secondary_focus_page_number = None
        self._secondary_focus_box = None
        self.secondary_preview_frame.hide()

    def set_secondary_focus_region(self, page_index: int, normalized_box, label: str = "", kind: str = "text"):
        self._secondary_focus_page_number = int(page_index) + 1
        self._secondary_focus_box = None
        if isinstance(normalized_box, (list, tuple)) and len(normalized_box) == 4:
            try:
                vals = [max(0.0, min(1.0, float(v))) for v in normalized_box]
                if vals[2] > 0 and vals[3] > 0:
                    vals[2] = min(vals[2], 1.0 - vals[0])
                    vals[3] = min(vals[3], 1.0 - vals[1])
                    self._secondary_focus_box = vals
            except Exception:
                pass
        self._secondary_focus_kind = str(kind or "text").lower()
        self._rescale_secondary_preview()

    def _rescale_secondary_preview(self):
        if not hasattr(self, "secondary_page_scroll") or self._secondary_source_pixmap.isNull():
            return
        size = self.secondary_page_scroll.viewport().size()
        if size.width() <= 0 or size.height() <= 0:
            return
        base = self._secondary_source_pixmap.scaled(
            size - QSize(20, 20), Qt.AspectRatioMode.KeepAspectRatio,
            Qt.TransformationMode.SmoothTransformation)
        zoom = max(0.55, min(3.0, float(self._secondary_preview_zoom)))
        target_size = QSize(max(1, round(base.width() * zoom)), max(1, round(base.height() * zoom)))
        preview = self._secondary_source_pixmap.scaled(
            target_size, Qt.AspectRatioMode.KeepAspectRatio, Qt.TransformationMode.SmoothTransformation)
        box = self._secondary_focus_box
        if self._focus_visible and box and self._secondary_focus_page_number == self.secondary_page_number:
            nx, ny, nw, nh = box
            x, y = nx * preview.width(), ny * preview.height()
            w = min(max(8.0, nw * preview.width()), preview.width() - x)
            h = min(max(8.0, nh * preview.height()), preview.height() - y)
            painter = QPainter(preview)
            painter.setRenderHint(QPainter.RenderHint.Antialiasing, True)
            visual_kinds = {"diagram", "chart", "photo", "image", "figure", "graph", "plot", "drawing", "table"}
            solution_kinds = {"solution", "worked_solution"}
            if self._secondary_focus_kind in visual_kinds:
                edge, fill = QColor(32, 205, 230, 225), QColor(20, 205, 230, 28)
            elif self._secondary_focus_kind in solution_kinds:
                edge, fill = QColor(95, 218, 132, 225), QColor(70, 210, 120, 28)
            else:
                edge, fill = QColor(255, 190, 58, 205), QColor(255, 190, 58, 24)
            painter.setPen(QPen(edge, 2.5))
            painter.setBrush(QBrush(fill))
            painter.drawRoundedRect(QRectF(x, y, max(8.0, w), max(8.0, h)), 5, 5)
            painter.end()
        self._paint_teaching_marks(preview, "supplementary", self.secondary_page_number)
        self.secondary_page_label.setPixmap(preview)
        self.secondary_page_label.setFixedSize(preview.size())

    def _refresh_teaching_mark_views(self):
        """Repaint temporary lesson-only arrows and text on the tutor's page previews."""
        self._rescale_preview()
        if self._secondary_source_pixmap and not self._secondary_source_pixmap.isNull():
            self._rescale_secondary_preview()

    def add_teaching_arrow_overlay(self, source: str, page_index: int, start, end, label: str = ""):
        try:
            a = [max(0.0, min(1.0, float(start[0]))), max(0.0, min(1.0, float(start[1])))]
            b = [max(0.0, min(1.0, float(end[0]))), max(0.0, min(1.0, float(end[1])))]
            if len(a) != 2 or len(b) != 2:
                return
            source_key = str(source or "primary")
            source_path = self.pdf_path if source_key == "primary" else self.secondary_pdf_path
            # Prevent a model's optional extra tool call from duplicating the automatic
            # arrow generated for the same focused region.
            for existing in self._teaching_marks:
                if existing.get("type") == "arrow" and existing.get("source") == source_key and int(existing.get("page_index", -1)) == int(page_index):
                    old_a, old_b = existing.get("start", [0, 0]), existing.get("end", [0, 0])
                    if max(abs(float(old_a[i]) - a[i]) for i in range(2)) < 0.035 and max(abs(float(old_b[i]) - b[i]) for i in range(2)) < 0.035:
                        return
            self._teaching_marks.append({"type": "arrow", "source": source_key, "pdf_path": source_path, "page_index": int(page_index),
                                         "start": a, "end": b, "label": str(label or "Teacher pointer")[:160]})
            self._refresh_teaching_mark_views()
            self.set_status(f"Temporary teaching arrow displayed · {len(self._teaching_marks)} mark(s) in this lesson")
        except Exception as exc:
            self.set_status(f"Could not display temporary arrow: {exc}")

    def clear_teaching_marks(self):
        self._teaching_marks.clear()
        self._refresh_teaching_mark_views()

    def _paint_teaching_marks(self, pixmap, source: str, page_number: int):
        if pixmap.isNull() or not self._teaching_marks:
            return
        painter = QPainter(pixmap)
        painter.setRenderHint(QPainter.RenderHint.Antialiasing, True)
        for mark in self._teaching_marks:
            if mark.get("source") != source or int(mark.get("page_index", -1)) + 1 != int(page_number):
                continue
            if mark.get("type") == "arrow":
                start, end = mark.get("start", [0, 0]), mark.get("end", [0, 0])
                x1, y1 = float(start[0]) * pixmap.width(), float(start[1]) * pixmap.height()
                x2, y2 = float(end[0]) * pixmap.width(), float(end[1]) * pixmap.height()
                pen = QPen(QColor(17, 115, 231, 245), max(2.5, pixmap.width() / 420.0))
                pen.setCapStyle(Qt.PenCapStyle.RoundCap)
                painter.setPen(pen)
                painter.drawLine(QPointF(x1, y1), QPointF(x2, y2))
                angle = math.atan2(y2 - y1, x2 - x1)
                head = max(10.0, pixmap.width() / 55.0)
                p1 = QPointF(x2 - head * math.cos(angle - math.pi / 6), y2 - head * math.sin(angle - math.pi / 6))
                p2 = QPointF(x2 - head * math.cos(angle + math.pi / 6), y2 - head * math.sin(angle + math.pi / 6))
                painter.drawLine(QPointF(x2, y2), p1)
                painter.drawLine(QPointF(x2, y2), p2)
        painter.end()

    def clear_focus_regions(self):
        """Clear the previous spoken target before the tutor starts the next item."""
        self._focus_page_number = None
        self._focus_box = None
        self._focus_label = ""
        self._focus_kind = "text"
        self._secondary_focus_page_number = None
        self._secondary_focus_box = None
        self._secondary_focus_kind = "text"
        self._rescale_preview()
        self._rescale_secondary_preview()

    def set_focus_region(self, page_index: int, normalized_box, label: str = "", kind: str = "text"):
        """Draw only a semantic-color focus rectangle on the tutor's own page preview."""
        self._focus_page_number = int(page_index) + 1
        self._focus_box = None
        if isinstance(normalized_box, (list, tuple)) and len(normalized_box) == 4:
            try:
                box = [max(0.0, min(1.0, float(v))) for v in normalized_box]
                if box[2] > 0 and box[3] > 0:
                    box[2] = min(box[2], 1.0 - box[0])
                    box[3] = min(box[3], 1.0 - box[1])
                    self._focus_box = box
            except (TypeError, ValueError):
                self._focus_box = None
        self._focus_label = str(label or "Engo is explaining this area")
        self._focus_kind = str(kind or "text").lower()
        self._laser_timer.stop()
        self._rescale_preview()

    def _rescale_preview(self):
        if self._source_pixmap.isNull():
            return
        size = self.page_scroll.viewport().size()
        if size.width() <= 0 or size.height() <= 0:
            return
        base = self._source_pixmap.scaled(
            size - QSize(20, 20), Qt.AspectRatioMode.KeepAspectRatio,
            Qt.TransformationMode.SmoothTransformation)
        zoom = max(0.55, min(3.0, float(self._primary_preview_zoom)))
        target_size = QSize(max(1, round(base.width() * zoom)), max(1, round(base.height() * zoom)))
        preview = self._source_pixmap.scaled(
            target_size, Qt.AspectRatioMode.KeepAspectRatio, Qt.TransformationMode.SmoothTransformation)
        self._scaled_preview_size = QSize(preview.size())
        if self._focus_visible and self._focus_box and self._focus_page_number == self.page_number and not preview.isNull():
            nx, ny, nw, nh = self._focus_box
            x, y = nx * preview.width(), ny * preview.height()
            w, h = max(8.0, nw * preview.width()), max(8.0, nh * preview.height())
            w, h = min(w, preview.width() - x), min(h, preview.height() - y)
            target = QRectF(x, y, w, h)
            painter = QPainter(preview)
            painter.setRenderHint(QPainter.RenderHint.Antialiasing, True)
            visual_kinds = {"diagram", "chart", "photo", "image", "figure", "graph", "plot", "drawing", "table"}
            solution_kinds = {"solution", "worked_solution"}
            if self._focus_kind == "manual":
                edge, fill = QColor(190, 120, 255, 235), QColor(175, 80, 255, 40)
            elif self._focus_kind in visual_kinds:
                edge, fill = QColor(32, 205, 230, 225), QColor(20, 205, 230, 28)
            elif self._focus_kind in solution_kinds:
                edge, fill = QColor(95, 218, 132, 225), QColor(70, 210, 120, 28)
            else:
                edge, fill = QColor(255, 190, 58, 205), QColor(255, 190, 58, 24)
            painter.setPen(QPen(edge, 2.5))
            painter.setBrush(QBrush(fill))
            painter.drawRoundedRect(target, 5, 5)
            painter.end()
        self._paint_teaching_marks(preview, "primary", self.page_number)
        if self._manual_select_mode and self._manual_drag_box and not preview.isNull():
            nx, ny, nw, nh = self._manual_drag_box
            drag_rect = QRectF(nx * preview.width(), ny * preview.height(), max(2.0, nw * preview.width()), max(2.0, nh * preview.height()))
            dp = QPainter(preview)
            dp.setRenderHint(QPainter.RenderHint.Antialiasing, True)
            dp.setPen(QPen(QColor(190, 120, 255, 240), 2, Qt.PenStyle.DashLine))
            dp.setBrush(QBrush(QColor(175, 80, 255, 38)))
            dp.drawRect(drag_rect)
            dp.end()
        self.page_label.setPixmap(preview)
        self.page_label.setFixedSize(preview.size())

    def _zoom_preview(self, factor: float, secondary: bool = False):
        attr = "_secondary_preview_zoom" if secondary else "_primary_preview_zoom"
        current = float(getattr(self, attr, 1.0))
        setattr(self, attr, max(0.55, min(3.0, current * float(factor))))
        (self._rescale_secondary_preview if secondary else self._rescale_preview)()

    def _scroll_preview_from_wheel(self, event, secondary: bool = False) -> bool:
        """Scroll within the current PDF page; wheel gestures never change page number."""
        scroll_area = self.secondary_page_scroll if secondary else self.page_scroll
        horizontal = scroll_area.horizontalScrollBar()
        vertical = scroll_area.verticalScrollBar()
        pixel = event.pixelDelta()
        angle = event.angleDelta()
        dx = int(pixel.x())
        dy = int(pixel.y())
        if not dx:
            dx = int(round(angle.x() / 120.0 * max(1, horizontal.singleStep()) * 3))
        if not dy:
            dy = int(round(angle.y() / 120.0 * max(1, vertical.singleStep()) * 3))
        if event.modifiers() & Qt.KeyboardModifier.ControlModifier:
            zoom_delta = int(pixel.y() or angle.y())
            if zoom_delta:
                self._zoom_preview(math.exp(zoom_delta / 480.0), secondary=secondary)
                return True
        if event.modifiers() & Qt.KeyboardModifier.ShiftModifier and not dx:
            dx, dy = dy, 0
        if dx:
            horizontal.setValue(horizontal.value() - dx)
        if dy:
            vertical.setValue(vertical.value() - dy)
        # Accept wheel/touchpad input even at a scroll boundary; never bubble it up
        # to a parent control that might interpret it as PDF page navigation.
        return bool(dx or dy)

    def resizeEvent(self, event):
        super().resizeEvent(event)
        QTimer.singleShot(0, self._rescale_preview)
        QTimer.singleShot(0, self._rescale_secondary_preview)

    def set_session_active(self, active: bool, paused: bool = False):
        self._session_active = bool(active)
        self._tutor_paused = bool(paused) if active else False
        self.start_btn.setEnabled(not active)
        self._set_start_button_caption()
        self.stop_btn.setEnabled(active)
        self.refresh_btn.setEnabled(True)
        self.ptt_btn.setEnabled(bool(active and not self._tutor_paused))
        self.ptt_btn.setObjectName("talkButton")
        try:
            theme_name = str(self.parent().settings.value("ui_theme", "dark", type=str) or "dark").lower()
        except Exception:
            theme_name = "dark"
        self.ptt_btn.setIcon(make_icon("mic", "#183b70" if theme_name == "light" else "#ffffff", 17))
        self.ptt_btn.style().unpolish(self.ptt_btn)
        self.ptt_btn.style().polish(self.ptt_btn)
        self.pause_btn.setEnabled(active)
        self.pause_btn.setText("Resume & repeat last point" if self._tutor_paused else "Pause lesson")
        self.pause_btn.setIcon(make_icon("play" if self._tutor_paused else "pause", "#ffffff" if self._tutor_paused else "#d6deeb", 16))
        self.text_input.setEnabled(bool(active and not self._tutor_paused))
        self.send_text_btn.setEnabled(bool(active and not self._tutor_paused))
        if not active:
            self._end_ptt()
            self._set_voice_loading(False)
            self.ptt_btn.setText("Hold SPACE to talk · release to send")

    def _animate_voice_loading(self):
        dots = "." * (self._voice_loading_phase % 4)
        self._voice_loading_phase += 1
        self.voice_loading_label.setText(f"Engo AI is preparing a reply{dots}")

    def _set_voice_loading(self, active: bool):
        if active:
            self._voice_loading_phase = 0
            self.voice_loading_label.show()
            if not self._voice_loading_timer.isActive():
                self._voice_loading_timer.start()
            self._animate_voice_loading()
        else:
            self._voice_loading_timer.stop()
            self.voice_loading_label.hide()

    def set_status(self, message: str):
        self.status_label.setText(str(message or ""))
        lowered = str(message or "").casefold()
        if any(word in lowered for word in ("failed", "error", "stopped", "ended", "disconnected")):
            self._set_voice_loading(False)

    def append_transcript(self, speaker: str, chunk: str):
        chunk = str(chunk or "")
        if not chunk:
            return
        if str(speaker).casefold().startswith("you"):
            self._set_voice_loading(True)
        elif str(speaker).casefold().startswith("engo ai"):
            self._set_voice_loading(False)
        if speaker != self._last_speaker:
            if self._transcript_markdown:
                self._transcript_markdown += "\n\n"
            self._transcript_markdown += f"**{speaker}:** "
            self._last_speaker = speaker
        self._transcript_markdown += chunk
        _set_markdown_browser(self.transcript_view, self._transcript_markdown, 13.0)
        # QTextBrowser recalculates its document layout after setHtml(); scrolling in the
        # same stack frame can use the previous maximum and leave the newest speech clipped.
        QTimer.singleShot(0, self._scroll_transcript_to_bottom)
        QTimer.singleShot(45, self._scroll_transcript_to_bottom)

    def _scroll_transcript_to_bottom(self):
        try:
            bar = self.transcript_view.verticalScrollBar()
            bar.setValue(bar.maximum())
        except RuntimeError:
            pass

    def reset_board(self, title: str = "Your teacher's board", content: str = ""):
        self._board_markdown = ""
        self._board_has_notes = False
        self.board_title.setText(str(title or "Your teacher's board"))
        if content:
            _set_markdown_browser(self.board_layout, str(content), 9.5)
        else:
            _set_markdown_browser(self.board_layout, "The lesson notes, key points, and examples will be collected here as the tutor explains the page.", 9.5)

    def update_board(self, title: str, content: str):
        title = str(title or "Lesson notes").strip()
        content = str(content or "").strip()
        if not content:
            return
        # A cumulative board: append each distinct concept once, not on every retry/continuation.
        section = f"## {title}\n\n{content}"
        normalize = lambda value: re.sub(r"\s+", " ", re.sub(r"[^\w]+", " ", str(value or "").casefold())).strip()
        current_norm = normalize(self._board_markdown)
        content_norm = normalize(content)
        if normalize(section) == current_norm or (len(content_norm) >= 18 and content_norm in current_norm):
            return
        if self._board_has_notes:
            self._board_markdown = (self._board_markdown.rstrip() + "\n\n---\n\n" + section).strip()
        else:
            self._board_markdown = section
            self._board_has_notes = True
        self.board_title.setText(f"PAGE {self.page_number} NOTES · cumulative summary")
        _set_markdown_browser(self.board_layout, self._board_markdown, 9.5)
        self.board_layout.verticalScrollBar().setValue(self.board_layout.verticalScrollBar().maximum())
        self._save_current_board(show_message=False)

    def closeEvent(self, event):
        preview_auto_scroll = getattr(self, "_preview_middle_auto_scroll", None)
        if preview_auto_scroll is not None:
            preview_auto_scroll.stop()
        # Closing this auxiliary window must not silently cancel the live worker.
        # Keep the session and its controls/state intact so the user can reopen
        # the dialog and explicitly end or continue the same conversation.
        self._end_ptt()
        self._laser_timer.stop()
        if self._session_active:
            # Hide safely: pause the tutor's audio but keep the Gemini connection
            # alive, so reopening the window restores Resume and End controls.
            if not self._tutor_paused:
                self._toggle_tutor_pause()
            self.set_status("Window hidden · the live session is paused and still connected. Reopen Voice & AI Teacher to resume or end it.")
        event.accept()
