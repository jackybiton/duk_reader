from __future__ import annotations

import asyncio
import base64
import csv
import ctypes
import difflib
import hashlib
import html
import io
import json
import os
import queue
import re
import shutil
import subprocess
import sys
import tempfile
import threading
import traceback
import time
import unicodedata
import urllib.error
import urllib.request
import uuid
import wave
import zipfile
from ctypes import wintypes
from concurrent.futures import ThreadPoolExecutor, as_completed
from dataclasses import asdict, dataclass
from datetime import datetime
from decimal import Decimal, InvalidOperation, ROUND_HALF_UP
from pathlib import Path
from typing import Callable

import numpy as np
import pypdfium2 as pdfium
import edge_tts
import truststore
from PIL import Image, ImageGrab, ImageTk
import tkinter as tk
from tkinter import filedialog, messagebox, ttk

from offline_ai import AI_ARTIFACTS, OfflineAiCancelled, OfflineAiManager


CUSTOMER_EDITION = os.environ.get("DUK_CUSTOMER_EDITION", "").strip() == "1"
GIGAPDF_OCR_EDITION = (
    not CUSTOMER_EDITION
    and os.environ.get("DUK_GIGAPDF_OCR_EDITION", "").strip() == "1"
)
APP_NAME = (
    "קורא דוחות ללקוחות"
    if CUSTOMER_EDITION
    else "קורא דוחות — ניסוי GigaPDF OCR"
    if GIGAPDF_OCR_EDITION
    else "קורא דוחות"
)
APP_VERSION = "1.0.9" if CUSTOMER_EDITION else "1.6.13-giga1" if GIGAPDF_OCR_EDITION else "1.6.15"
OCR_CACHE_VERSION = "1.5.2-giga1" if GIGAPDF_OCR_EDITION else "1.5.2"
OCR_DPI = 300
NEURAL_SPEECH_CACHE_LIMIT = 400
CUSTOMER_UPDATE_MANIFEST_URL = "https://yaakovserver.com/reportreader-api/v1/updates/windows"
PRIVATE_UPDATE_MANIFEST_URL = "https://yaakovserver.com/reportreader-api/v1/updates/windows-private"
AUTH_LOGIN_URL = "https://yaakovserver.com/reportreader-api/v1/auth/login"
AUTH_STATUS_URL = "https://yaakovserver.com/reportreader-api/v1/auth/status"
OCR_RULES_PUBLIC_URL = "https://yaakovserver.com/reportreader-api/v1/ocr-rules"
OCR_RULES_SUBMIT_URL = "https://yaakovserver.com/reportreader-api/v1/ocr-rules/submissions"
OCR_RULES_SYNC_INTERVAL_SECONDS = 3 * 24 * 60 * 60
RULE_SYNC_FILE_LOCK = threading.Lock()
FINANCE_BRIDGE_FOLDER = "DukFinanceBridge"
FINANCE_CLIENTS_FILE = "finance-clients.json"
FINANCE_PENDING_FOLDER = "pending-repair-jobs"
PRIVATE_PIPER_VOICE_CHOICE = "Piper עברי SASpeech - איכותי אופליין"
VOICE_CHOICES = (
    "מיכאל - איכותי אופליין",
    "שאול - איכותי אופליין",
) + (() if CUSTOMER_EDITION else (PRIVATE_PIPER_VOICE_CHOICE,)) + (
    "הילה - איכותי אונליין",
    "אברי - איכותי אונליין",
    "אסף - אופליין בסיסי",
) + (() if CUSTOMER_EDITION else ("אברי מוקלט - אופליין",))
LOCAL_VOICE_MODELS = {
    "local-michael": (
        "offline_voice_models/michael.onnx",
        "offline_voice_models/model.config.json",
    ),
    "local-shaul": (
        "offline_voice_models/shaul.onnx",
        "offline_voice_models/model.config.json",
    ),
}
if not CUSTOMER_EDITION:
    LOCAL_VOICE_MODELS["local-saspeech"] = (
        "private_voice_models/he_IL-saspeech-medium.onnx",
        "private_voice_models/he_IL-saspeech-medium.onnx.json",
    )
RECORDED_AVRI_VOICE = "recorded-avri"
RECORDED_AVRI_EDGE_VOICE = "he-IL-AvriNeural"
RECORDED_AVRI_GAP_MARKER = "\u0001duk-gap\u0001"
PAYMENT_MODE_HOURLY = "hourly"
PAYMENT_MODE_ISSUE = "issue"
PAYMENT_MODE_LABELS = {
    PAYMENT_MODE_HOURLY: "לפי זמן ומחיר לשעה",
    PAYMENT_MODE_ISSUE: "לפי סוג הבעיה",
}
DEFAULT_BILLING_ISSUES = ("דיבוק", "בעיה", "נתק", "תגים", "חסרות", "יתירות")


def enable_windows_dpi_awareness() -> None:
    """Keep Tk geometry in real screen pixels, including high-DPI displays."""
    if os.name != "nt":
        return
    try:
        ctypes.windll.user32.SetProcessDpiAwarenessContext(ctypes.c_void_p(-4))
    except Exception:
        try:
            ctypes.windll.user32.SetProcessDPIAware()
        except Exception:
            pass


def windows_work_area(widget: tk.Misc) -> tuple[int, int, int, int]:
    """Return the usable desktop rectangle without covering the taskbar."""
    if os.name == "nt":
        rectangle = wintypes.RECT()
        try:
            if ctypes.windll.user32.SystemParametersInfoW(
                0x0030, 0, ctypes.byref(rectangle), 0,
            ):
                return rectangle.left, rectangle.top, rectangle.right, rectangle.bottom
        except Exception:
            pass
    return 0, 0, widget.winfo_screenwidth(), widget.winfo_screenheight()


def fit_window_to_work_area(
    window: tk.Toplevel | tk.Tk,
    desired_width: int,
    desired_height: int,
    minimum_width: int = 640,
    minimum_height: int = 480,
) -> None:
    """Fit a window inside the current work area and keep it resizable."""
    left, top, right, bottom = windows_work_area(window)
    work_width = max(360, right - left)
    work_height = max(320, bottom - top)
    width = min(desired_width, max(340, work_width - 28))
    height = min(desired_height, max(300, work_height - 28))
    x = left + max(0, (work_width - width) // 2)
    y = top + max(0, (work_height - height) // 2)
    window.geometry(f"{width}x{height}+{x}+{y}")
    window.minsize(min(minimum_width, width), min(minimum_height, height))
    window.resizable(True, True)


class NativeRtlEntry(tk.Frame):
    """A real Windows Unicode edit control with native bidirectional editing.

    Tk's Entry can align Hebrew to the right, but it does not provide complete
    bidirectional caret/delete behavior.  The Windows EDIT control does, so the
    correction dialog uses it while retaining a Tk StringVar interface.
    """

    def __init__(
        self,
        master: tk.Misc,
        textvariable: tk.StringVar,
        height: int = 34,
        **kwargs,
    ) -> None:
        super().__init__(
            master, height=height, bg="#FFFDF7",
            highlightthickness=1, highlightbackground="#CDB68E",
        )
        self._variable = textvariable
        self._native_hwnd = 0
        self._poll_job: str | None = None
        self._variable_trace = ""
        self._fallback: ttk.Entry | None = None
        self.pack_propagate(False)
        self.grid_propagate(False)
        if os.name != "nt":
            self._fallback = ttk.Entry(
                self, textvariable=textvariable, justify="right", **kwargs,
            )
            self._fallback.pack(fill="both", expand=True)
            return

        self.update_idletasks()
        user32 = ctypes.windll.user32
        user32.CreateWindowExW.argtypes = (
            wintypes.DWORD, wintypes.LPCWSTR, wintypes.LPCWSTR, wintypes.DWORD,
            ctypes.c_int, ctypes.c_int, ctypes.c_int, ctypes.c_int,
            wintypes.HWND, wintypes.HMENU, wintypes.HINSTANCE, wintypes.LPVOID,
        )
        user32.CreateWindowExW.restype = wintypes.HWND
        user32.GetWindowTextLengthW.argtypes = (wintypes.HWND,)
        user32.GetWindowTextLengthW.restype = ctypes.c_int
        user32.GetWindowTextW.argtypes = (
            wintypes.HWND, wintypes.LPWSTR, ctypes.c_int,
        )
        user32.GetWindowTextW.restype = ctypes.c_int
        user32.SetWindowTextW.argtypes = (wintypes.HWND, wintypes.LPCWSTR)
        user32.SetWindowTextW.restype = wintypes.BOOL
        user32.SendMessageW.argtypes = (
            wintypes.HWND, wintypes.UINT, wintypes.WPARAM, wintypes.LPARAM,
        )
        user32.SendMessageW.restype = ctypes.c_ssize_t
        user32.MoveWindow.argtypes = (
            wintypes.HWND, ctypes.c_int, ctypes.c_int, ctypes.c_int,
            ctypes.c_int, wintypes.BOOL,
        )
        user32.MoveWindow.restype = wintypes.BOOL
        user32.SetFocus.argtypes = (wintypes.HWND,)
        user32.SetFocus.restype = wintypes.HWND
        user32.DestroyWindow.argtypes = (wintypes.HWND,)
        user32.DestroyWindow.restype = wintypes.BOOL
        extended_style = 0x00000200 | 0x00002000 | 0x00400000
        style = 0x40000000 | 0x10000000 | 0x00010000 | 0x00000002 | 0x00000080
        self._native_hwnd = int(user32.CreateWindowExW(
            extended_style, "EDIT", textvariable.get(), style,
            0, 0, 100, height, self.winfo_id(), None, None, None,
        ) or 0)
        if not self._native_hwnd:
            self._fallback = ttk.Entry(
                self, textvariable=textvariable, justify="right", **kwargs,
            )
            self._fallback.pack(fill="both", expand=True)
            return
        default_gui_font = ctypes.windll.gdi32.GetStockObject(17)
        user32.SendMessageW(self._native_hwnd, 0x0030, default_gui_font, True)
        user32.SendMessageW(self._native_hwnd, 0x00D3, 0x0003, (8 << 16) | 8)
        self.bind("<Configure>", self._resize_native, add="+")
        self.bind("<Destroy>", self._destroy_native, add="+")
        self._variable_trace = textvariable.trace_add("write", self._variable_changed)
        self.after_idle(self._resize_native)
        self._poll_job = self.after(70, self._poll_native_text)

    def _read_native(self) -> str:
        if not self._native_hwnd:
            return self._variable.get()
        user32 = ctypes.windll.user32
        length = int(user32.GetWindowTextLengthW(self._native_hwnd))
        buffer = ctypes.create_unicode_buffer(length + 1)
        user32.GetWindowTextW(self._native_hwnd, buffer, length + 1)
        return buffer.value

    def _variable_changed(self, *_args) -> None:
        if not self._native_hwnd:
            return
        value = self._variable.get()
        if value != self._read_native():
            ctypes.windll.user32.SetWindowTextW(self._native_hwnd, value)

    def _poll_native_text(self) -> None:
        if not self.winfo_exists() or not self._native_hwnd:
            return
        value = self._read_native()
        if value != self._variable.get():
            self._variable.set(value)
        self._poll_job = self.after(70, self._poll_native_text)

    def _resize_native(self, _event=None) -> None:
        if self._native_hwnd:
            ctypes.windll.user32.MoveWindow(
                self._native_hwnd, 0, 0,
                max(1, self.winfo_width()), max(1, self.winfo_height()), True,
            )

    def _destroy_native(self, event=None) -> None:
        if event is not None and event.widget is not self:
            return
        if self._poll_job:
            try:
                self.after_cancel(self._poll_job)
            except tk.TclError:
                pass
            self._poll_job = None
        if self._variable_trace:
            try:
                self._variable.trace_remove("write", self._variable_trace)
            except tk.TclError:
                pass
            self._variable_trace = ""
        if self._native_hwnd:
            try:
                ctypes.windll.user32.DestroyWindow(self._native_hwnd)
            except Exception:
                pass
            self._native_hwnd = 0

    def get(self) -> str:
        if self._fallback is not None:
            return self._fallback.get()
        value = self._read_native()
        if value != self._variable.get():
            self._variable.set(value)
        return value

    def focus_set(self) -> None:
        if self._fallback is not None:
            self._fallback.focus_set()
        elif self._native_hwnd:
            ctypes.windll.user32.SetFocus(self._native_hwnd)


@dataclass
class ReportRow:
    page: str = ""
    start: str = ""
    line: str = ""
    first_word: str = ""
    problem_word: str = ""
    problem_type: str = ""
    description: str = ""
    source_pdf_page: int = 0
    confidence: float = 0.0
    row_left: float = 0.0
    row_top: float = 0.0
    row_right: float = 1.0
    row_bottom: float = 0.0
    ocr_start: str = ""
    ocr_first_word: str = ""
    ocr_problem_word: str = ""
    ocr_problem_type: str = ""
    ocr_description: str = ""
    manual_start: str | None = None
    manual_first_word: str | None = None
    manual_problem_word: str | None = None
    manual_problem_type: str | None = None
    manual_description: str | None = None
    ai_start: str | None = None
    ai_first_word: str | None = None
    ai_problem_word: str | None = None
    ai_problem_type: str | None = None
    ai_description: str | None = None
    ai_reviewed: bool = False
    ai_confidence: float = 0.0
    ai_reason: str = ""
    report_kind: str = "classic"


@dataclass
class OcrWord:
    text: str
    x: int
    y: int
    w: int
    h: int
    conf: float

    @property
    def cx(self) -> float:
        return self.x + self.w / 2

    @property
    def cy(self) -> float:
        return self.y + self.h / 2


def resource_path(name: str) -> Path:
    root = Path(getattr(sys, "_MEIPASS", Path(__file__).resolve().parent))
    return root / name


def app_data_dir() -> Path:
    base = Path(os.environ.get("LOCALAPPDATA", tempfile.gettempdir()))
    target = base / (
        "DukReportReaderClients"
        if CUSTOMER_EDITION
        else "DukReportReaderGigaOcrTest"
        if GIGAPDF_OCR_EDITION
        else "DukReportReader"
    )
    target.mkdir(parents=True, exist_ok=True)
    return target


def version_key(value: object) -> tuple[int, ...]:
    numbers = [int(part) for part in re.findall(r"\d+", str(value or ""))]
    return tuple((numbers + [0, 0, 0])[:4])


def customer_auth_path() -> Path:
    return app_data_dir() / "auth.json"


def load_customer_auth() -> dict:
    try:
        value = json.loads(customer_auth_path().read_text(encoding="utf-8"))
    except (OSError, ValueError, TypeError):
        value = {}
    return value if isinstance(value, dict) else {}


def save_customer_auth(value: dict) -> None:
    temporary = customer_auth_path().with_suffix(".json.tmp")
    temporary.write_text(json.dumps(value, ensure_ascii=False, indent=2), encoding="utf-8")
    temporary.replace(customer_auth_path())


def clear_customer_auth() -> None:
    try:
        customer_auth_path().unlink(missing_ok=True)
    except OSError:
        pass


def customer_device_id() -> str:
    value = load_customer_auth().get("device_id", "")
    if isinstance(value, str) and re.fullmatch(r"[A-Za-z0-9._-]{8,100}", value):
        return value
    return "windows-" + uuid.uuid4().hex


def api_json_request(url: str, payload: dict, token: str = "", timeout: int = 25) -> tuple[int, dict]:
    headers = {
        "Accept": "application/json",
        "Content-Type": "application/json; charset=utf-8",
        "User-Agent": f"DukReportReaderClients/{APP_VERSION}",
    }
    if token:
        headers["Authorization"] = "Bearer " + token
    request = urllib.request.Request(
        url, data=json.dumps(payload, ensure_ascii=False).encode("utf-8"),
        headers=headers, method="POST",
    )
    try:
        with urllib.request.urlopen(request, timeout=timeout) as response:
            status = int(response.status)
            body = response.read(256 * 1024)
    except urllib.error.HTTPError as error:
        status = int(error.code)
        body = error.read(256 * 1024)
    try:
        value = json.loads(body.decode("utf-8"))
    except (UnicodeError, ValueError, TypeError):
        value = {"error": f"תשובת שרת לא תקינה ({status})"}
    return status, value if isinstance(value, dict) else {}


def finance_bridge_dir() -> Path:
    base = Path(os.environ.get("LOCALAPPDATA", tempfile.gettempdir()))
    target = base / FINANCE_BRIDGE_FOLDER
    target.mkdir(parents=True, exist_ok=True)
    return target


def load_finance_context() -> dict:
    """Load the user/client snapshot published by Finance Maaser.

    The report reader is also usable before the finance application publishes a
    snapshot, so a missing or partially-written file simply returns no clients.
    """
    snapshot_path = finance_bridge_dir() / FINANCE_CLIENTS_FILE
    try:
        payload = json.loads(snapshot_path.read_text(encoding="utf-8"))
    except (OSError, ValueError, TypeError):
        return {"username": "", "clients": []}

    raw_clients = payload.get("clients", []) if isinstance(payload, dict) else []
    if not isinstance(raw_clients, list):
        raw_clients = []

    clients: list[dict] = []
    seen: set[str] = set()
    for item in raw_clients:
        if isinstance(item, str):
            item = {"name": item}
        if not isinstance(item, dict):
            continue
        name = str(item.get("name", "")).strip()
        key = name.casefold()
        if not name or key in seen:
            continue
        seen.add(key)
        try:
            repair_rate = max(0.0, float(item.get("repairRate", 0) or 0))
        except (TypeError, ValueError):
            repair_rate = 0.0
        clients.append({
            "id": str(item.get("id", "")).strip(),
            "name": name,
            "repairRate": repair_rate,
        })
    return {
        "username": str(payload.get("username", "")).strip() if isinstance(payload, dict) else "",
        "clients": sorted(clients, key=lambda item: item["name"]),
    }


def load_finance_clients() -> list[dict]:
    return list(load_finance_context()["clients"])


def queue_finance_repair_job(job: dict) -> Path:
    """Atomically queue one finance job using its stable timer session id.

    Each job has its own file. This lets the report and finance applications run
    concurrently without both rewriting one shared JSON array. Repeating Finish
    after a crash is idempotent because it targets the same session file.
    """
    session_id = re.sub(r"[^A-Za-z0-9_-]", "", str(job.get("sessionId", "")))
    if not session_id:
        raise ValueError("missing timer session id")
    pending_dir = finance_bridge_dir() / FINANCE_PENDING_FOLDER
    pending_dir.mkdir(parents=True, exist_ok=True)
    destination = pending_dir / f"{session_id}.json"
    if destination.exists():
        return destination
    temporary = pending_dir / f".{session_id}-{os.getpid()}-{uuid.uuid4().hex}.tmp"
    try:
        with temporary.open("w", encoding="utf-8") as stream:
            json.dump(job, stream, ensure_ascii=False, indent=2)
            stream.flush()
            os.fsync(stream.fileno())
        try:
            temporary.replace(destination)
        except FileExistsError:
            pass
    finally:
        try:
            temporary.unlink()
        except FileNotFoundError:
            pass
    return destination


def timer_payment(seconds: float, rate: float) -> Decimal:
    try:
        value = (Decimal(str(max(0.0, seconds))) / Decimal("3600")) * Decimal(str(max(0.0, rate)))
    except (InvalidOperation, ValueError):
        value = Decimal("0")
    return value.quantize(Decimal("0.01"), rounding=ROUND_HALF_UP)


def issue_payment(
    issue_counts: dict[str, object], issue_rates: dict[str, object],
) -> tuple[Decimal, list[dict[str, object]]]:
    """Calculate a stable per-issue total and a serializable breakdown."""
    total = Decimal("0")
    breakdown: list[dict[str, object]] = []
    for issue in sorted(issue_counts):
        try:
            count = max(0, int(issue_counts.get(issue, 0) or 0))
            rate = Decimal(str(max(0.0, float(issue_rates.get(issue, 0) or 0))))
        except (InvalidOperation, TypeError, ValueError):
            continue
        if count <= 0:
            continue
        line_total = (Decimal(count) * rate).quantize(
            Decimal("0.01"), rounding=ROUND_HALF_UP,
        )
        total += line_total
        breakdown.append({
            "issue": issue,
            "count": count,
            "rate": float(rate),
            "amount": float(line_total),
        })
    return total.quantize(Decimal("0.01"), rounding=ROUND_HALF_UP), breakdown


def alert_payment(
    alert_items: list[dict[str, object]],
) -> tuple[Decimal, list[dict[str, object]]]:
    """Calculate per-alert prices and also return a compact per-issue summary."""
    grouped: dict[str, dict[str, object]] = {}
    total = Decimal("0")
    for item in alert_items:
        issue = clean_hebrew_text(str(item.get("issue", ""))).strip()
        try:
            rate = Decimal(str(max(0.0, float(item.get("rate", 0) or 0))))
        except (InvalidOperation, TypeError, ValueError):
            continue
        if not issue or rate <= 0:
            continue
        rate = rate.quantize(Decimal("0.01"), rounding=ROUND_HALF_UP)
        total += rate
        record = grouped.setdefault(issue, {
            "issue": issue, "count": 0, "amount": Decimal("0"), "rates": set(),
        })
        record["count"] = int(record["count"]) + 1
        record["amount"] = Decimal(str(record["amount"])) + rate
        rates = record["rates"]
        if isinstance(rates, set):
            rates.add(rate)
    breakdown: list[dict[str, object]] = []
    for issue in sorted(grouped):
        record = grouped[issue]
        rates = record.pop("rates")
        common_rate = next(iter(rates)) if isinstance(rates, set) and len(rates) == 1 else None
        breakdown.append({
            "issue": issue,
            "count": int(record["count"]),
            "rate": float(common_rate) if common_rate is not None else None,
            "amount": float(Decimal(str(record["amount"])).quantize(
                Decimal("0.01"), rounding=ROUND_HALF_UP,
            )),
        })
    return total.quantize(Decimal("0.01"), rounding=ROUND_HALF_UP), breakdown


def build_customer_work_report_html(summary: dict) -> str:
    started = datetime.fromisoformat(str(summary["start"]))
    ended = datetime.fromisoformat(str(summary["end"]))
    seconds = max(0.0, float(summary["seconds"]))
    rate = max(0.0, float(summary.get("rate", 0) or 0))
    payment_mode = str(summary.get("payment_mode", PAYMENT_MODE_HOURLY))
    alert_items = summary.get("alert_items", [])
    if not isinstance(alert_items, list):
        alert_items = []
    if payment_mode == PAYMENT_MODE_ISSUE:
        if alert_items:
            payment, breakdown = alert_payment(alert_items)
        else:
            payment, breakdown = issue_payment(
                summary.get("issue_counts", {}) if isinstance(summary.get("issue_counts"), dict) else {},
                summary.get("issue_rates", {}) if isinstance(summary.get("issue_rates"), dict) else {},
            )
    else:
        payment = timer_payment(seconds, rate)
        breakdown = []
    rounded_seconds = max(0, int(round(seconds)))
    hours, remainder = divmod(rounded_seconds, 3600)
    minutes, display_seconds = divmod(remainder, 60)
    duration = f"{hours:02}:{minutes:02}:{display_seconds:02}"
    decimal_hours = seconds / 3600.0
    client = html.escape(str(summary.get("client", "")).strip() or "לא צוין")
    report_name = html.escape(str(summary.get("report_name", "")).strip() or "לא צוין")
    generated = datetime.now()
    report_title = (
        "דוח עבודה לפי סוג בעיה"
        if payment_mode == PAYMENT_MODE_ISSUE else "דוח שעות עבודה"
    )
    if payment_mode == PAYMENT_MODE_ISSUE:
        billing_rows = "".join(
            "<tr>"
            f"<td>{html.escape(str(item['issue']))}</td>"
            f"<td>{int(item['count'])}</td>"
            f"<td>{('מחירים שונים' if item.get('rate') is None else '₪{:,.2f}'.format(float(item['rate'])))}</td>"
            f"<td>₪{float(item['amount']):,.2f}</td>"
            "</tr>"
            for item in breakdown
        )
        alert_rows = "".join(
            "<tr>"
            f"<td>{html.escape(str(item.get('issue', '')))}</td>"
            f"<td>{html.escape(str(item.get('page', '')))}</td>"
            f"<td>{html.escape(str(item.get('line', '')))}</td>"
            f"<td>{html.escape(str(item.get('word', '')))}</td>"
            f"<td>{html.escape(str(item.get('message', '')))}</td>"
            f"<td>₪{float(item.get('rate', 0) or 0):,.2f}</td>"
            "</tr>"
            for item in alert_items
        )
        alert_section = (
            '<section class="billing"><h2>פירוט כל ההתראות מהדוח</h2>'
            '<table><thead><tr><th>סוג</th><th>עמוד</th><th>שורה</th>'
            '<th>מילה</th><th>הודעה בדוח</th><th>מחיר</th></tr></thead>'
            f'<tbody>{alert_rows}</tbody></table></section>'
            if alert_rows else ""
        )
        billing_section = f"""
      <section class="billing">
        <h2>פירוט לפי סוג בעיה</h2>
        <table><thead><tr><th>סוג הבעיה</th><th>כמות</th><th>מחיר ליחידה</th><th>סה״כ</th></tr></thead>
        <tbody>{billing_rows}</tbody></table>
      </section>{alert_section}"""
        rate_item = (
            '<div class="item"><div class="label">שיטת תשלום</div>'
            '<div class="value">לפי סוג הבעיה</div></div>'
        )
    else:
        billing_section = ""
        rate_item = (
            '<div class="item"><div class="label">מחיר לשעה</div>'
            f'<div class="value">₪{rate:,.2f}</div></div>'
        )
    return f"""<!doctype html>
<html lang="he" dir="rtl">
<head>
  <meta charset="utf-8">
  <meta name="viewport" content="width=device-width, initial-scale=1">
  <title>{report_title} - {client}</title>
  <style>
    :root {{ --brown:#5a3518; --gold:#b87516; --cream:#fff9ec; --line:#dec9a2; --ink:#332315; }}
    * {{ box-sizing:border-box; }}
    body {{ margin:0; background:#eee5d4; color:var(--ink); font-family:"Segoe UI",Arial,sans-serif; }}
    .page {{ width:min(900px,calc(100% - 32px)); margin:32px auto; background:white; box-shadow:0 12px 35px #5a351830; }}
    header {{ padding:34px 42px 28px; color:white; background:linear-gradient(135deg,var(--brown),#7b4b22); }}
    h1 {{ margin:0 0 8px; font-size:32px; }}
    header p {{ margin:0; color:#f6dfb8; font-size:16px; }}
    main {{ padding:34px 42px 42px; }}
    .client {{ font-size:24px; font-weight:800; margin-bottom:24px; color:var(--brown); }}
    .grid {{ display:grid; grid-template-columns:repeat(2,minmax(0,1fr)); gap:14px; }}
    .item {{ padding:16px 18px; background:var(--cream); border:1px solid var(--line); border-radius:10px; }}
    .label {{ color:#876b4b; font-size:13px; font-weight:700; margin-bottom:5px; }}
    .value {{ font-size:18px; font-weight:750; overflow-wrap:anywhere; }}
    .billing {{ margin-top:24px; }}
    .billing h2 {{ color:var(--brown); font-size:20px; }}
    table {{ width:100%; border-collapse:collapse; }}
    th,td {{ padding:11px 12px; text-align:right; border-bottom:1px solid var(--line); }}
    th {{ background:var(--cream); color:var(--brown); }}
    .total {{ margin-top:24px; display:flex; justify-content:space-between; align-items:center; padding:22px 26px; border-radius:12px; background:#f6d878; color:var(--brown); }}
    .total strong {{ font-size:30px; }}
    footer {{ padding:18px 42px; border-top:1px solid var(--line); color:#876b4b; font-size:12px; }}
    @media (max-width:620px) {{ .grid{{grid-template-columns:1fr}} main,header,footer{{padding-right:22px;padding-left:22px}} }}
    @media print {{ body{{background:white}} .page{{width:100%;margin:0;box-shadow:none}} @page{{size:A4;margin:14mm}} }}
  </style>
</head>
<body>
  <article class="page">
    <header><h1>{report_title}</h1><p>סיכום עבודת בדיקת ותיקון דוח</p></header>
    <main>
      <div class="client">לקוח: {client}</div>
      <section class="grid">
        <div class="item"><div class="label">תאריך העבודה</div><div class="value">{started:%d/%m/%Y}</div></div>
        <div class="item"><div class="label">דוח מקור</div><div class="value">{report_name}</div></div>
        <div class="item"><div class="label">שעת התחלה</div><div class="value">{started:%H:%M:%S}</div></div>
        <div class="item"><div class="label">שעת סיום</div><div class="value">{ended:%H:%M:%S}</div></div>
        <div class="item"><div class="label">משך עבודה</div><div class="value">{duration}</div></div>
        <div class="item"><div class="label">שעות לחיוב</div><div class="value">{decimal_hours:.2f} שעות</div></div>
        {rate_item}
        <div class="item"><div class="label">תקופת העבודה</div><div class="value">{started:%d/%m/%Y %H:%M} – {ended:%d/%m/%Y %H:%M}</div></div>
      </section>
      {billing_section}
      <section class="total"><span>סה״כ לתשלום</span><strong>₪{payment:,.2f}</strong></section>
    </main>
    <footer>הופק באמצעות קורא דוחות ללקוחות · {generated:%d/%m/%Y %H:%M}</footer>
  </article>
</body>
</html>"""


def _resolved_pdf_path(pdf_path: Path) -> str:
    return os.path.normcase(str(pdf_path.resolve()))


def cache_path_for_pdf(pdf_path: Path) -> Path:
    key = hashlib.sha256(_resolved_pdf_path(pdf_path).encode("utf-8")).hexdigest()
    return app_data_dir() / f"ocr-file-{key}.json"


def _pdf_fingerprint(pdf_path: Path) -> dict[str, int | str]:
    stat = pdf_path.stat()
    return {
        "source_path": _resolved_pdf_path(pdf_path),
        "size": stat.st_size,
        "mtime_ns": stat.st_mtime_ns,
        "app_version": OCR_CACHE_VERSION,
    }


def load_ocr_cache(pdf_path: Path) -> list[ReportRow] | None:
    cache = cache_path_for_pdf(pdf_path)
    if not cache.exists():
        return None
    try:
        payload = json.loads(cache.read_text(encoding="utf-8"))
        if not isinstance(payload, dict) or payload.get("meta") != _pdf_fingerprint(pdf_path):
            return None
        rows = payload.get("rows")
        if not isinstance(rows, list):
            return None
        cached_rows = [ReportRow(**item) for item in rows]
        changed = False
        for row in cached_rows:
            before = (
                row.ocr_start, row.ocr_first_word, row.ocr_problem_word,
                row.ocr_problem_type, row.ocr_description,
            )
            ensure_ocr_baseline(row)
            row.ocr_problem_type = normalize_problem_type(row.ocr_problem_type)
            row.ocr_description = normalize_report_description(
                row.ocr_description, row.report_kind,
            )
            if before != (
                row.ocr_start, row.ocr_first_word, row.ocr_problem_word,
                row.ocr_problem_type, row.ocr_description,
            ):
                changed = True
        corrected = apply_learned_rules_to_rows(cached_rows)
        if changed or corrected:
            try:
                # Save both the untouched ocr_* baseline and the corrected
                # display values so reopening this report needs no rescan.
                write_ocr_cache(pdf_path, cached_rows)
            except OSError:
                pass
        return cached_rows
    except (OSError, ValueError, TypeError):
        return None


def write_ocr_cache(pdf_path: Path, rows: list[ReportRow]) -> None:
    cache = cache_path_for_pdf(pdf_path)
    temporary = cache.with_suffix(".tmp")
    payload = {
        "meta": _pdf_fingerprint(pdf_path),
        "rows": [asdict(row) for row in rows],
    }
    temporary.write_text(json.dumps(payload, ensure_ascii=False, indent=2), encoding="utf-8")
    temporary.replace(cache)


def delete_cache_for_pdf(pdf_path: Path) -> int:
    candidates = {cache_path_for_pdf(pdf_path)}
    try:
        stat = pdf_path.stat()
        for version in {"1.0.0", "1.1.0", OCR_CACHE_VERSION, APP_VERSION}:
            legacy_key = hashlib.sha256(
                f"{pdf_path.resolve()}|{stat.st_size}|{stat.st_mtime_ns}|{version}".encode()
            ).hexdigest()
            candidates.add(app_data_dir() / f"ocr-{legacy_key}.json")
    except OSError:
        pass
    removed = 0
    for cache in candidates:
        try:
            cache.unlink()
            removed += 1
        except FileNotFoundError:
            pass
    return removed


def delete_all_ocr_caches() -> int:
    removed = 0
    for cache in app_data_dir().glob("ocr-*.json"):
        try:
            cache.unlink()
            removed += 1
        except FileNotFoundError:
            pass
    return removed


def clean_hebrew_text(text: str) -> str:
    text = text.replace("\u200f", "").replace("\u200e", "")
    text = re.sub(r"[|]", " ", text)
    text = re.sub(r"\s+", " ", text).strip(" .,:;-_")
    return text


HEBREW_DIACRITICS = "\u0591-\u05bd\u05bf-\u05c7"
DIVINE_NAME_SPEECH_PATTERN = re.compile(
    rf"י[{HEBREW_DIACRITICS}]*ה[{HEBREW_DIACRITICS}]*ו[{HEBREW_DIACRITICS}]*ה"
    rf"|י[{HEBREW_DIACRITICS}]*ק[{HEBREW_DIACRITICS}]*ו[{HEBREW_DIACRITICS}]*ק"
)
EYETECH_DIVINE_NAME_PATTERN = re.compile(
    rf"י[{HEBREW_DIACRITICS}]*ד[{HEBREW_DIACRITICS}]*ו[{HEBREW_DIACRITICS}]*ד"
)
EYETECH_SACRED_SPELLINGS = (
    ("אלהיהם", "אלדיהם"),
    ("אלהיכם", "אלדיכם"),
    ("אלהינו", "אלדינו"),
    ("אלהיך", "אלדיך"),
    ("אלהיו", "אלדיו"),
    ("אלהים", "אלדים"),
    ("אלהי", "אלדי"),
    ("אלוה", "אלוד"),
    ("אהיה", "אדיד"),
    ("יהוה", "ידוד"),
    ("יה", "יד"),
)


def _marked_word_pattern(word: str) -> re.Pattern[str]:
    body = "".join(re.escape(letter) + f"[{HEBREW_DIACRITICS}]*" for letter in word)
    return re.compile(body + r"(?=$|[^\u05d0-\u05ea])")


EYETECH_SACRED_DISPLAY_PATTERNS = tuple(
    (_marked_word_pattern(canonical), display)
    for canonical, display in EYETECH_SACRED_SPELLINGS
)
EYETECH_SACRED_SPEECH_PATTERNS = tuple(
    (_marked_word_pattern(display), canonical)
    for canonical, display in EYETECH_SACRED_SPELLINGS
)


def normalize_divine_names_for_speech(text: str) -> str:
    """Apply the traditional qere according to the vocalized divine name."""
    def replacement(match: re.Match[str]) -> str:
        name = unicodedata.normalize("NFD", match.group(0))
        vav = name.find("ו")
        final_he = name.rfind("ה")
        vav_marks = name[vav + 1:final_he] if 0 <= vav < final_he else ""
        if "\u05b4" in vav_marks:  # hiriq under the vav: Elohim qere
            return "אֱלֹהִים"
        return "אֲדֹנָי"

    return DIVINE_NAME_SPEECH_PATTERN.sub(replacement, str(text or ""))


def normalize_divine_names_for_display(text: str) -> str:
    """Show sacred names with qof while retaining the source form elsewhere."""
    return DIVINE_NAME_SPEECH_PATTERN.sub("יקוק", str(text or ""))


def normalize_eyetech_divine_names_for_speech(text: str) -> str:
    """EyeTech prints the tetragrammaton with dalet; restore it for qere only."""
    restored = restore_eyetech_sacred_names(text)
    return normalize_divine_names_for_speech(restored)


def restore_eyetech_sacred_names(text: str) -> str:
    restored = str(text or "")
    restored = re.sub(
        r"(?<=[\u05d0-\u05ea])\s*[-–—]{1,4}\s*(?=[\u05d0-\u05ea])",
        "", restored,
    )
    for pattern, canonical in EYETECH_SACRED_SPEECH_PATTERNS:
        restored = pattern.sub(canonical, restored)
    return restored


def display_report_text(row: ReportRow, text: str) -> str:
    if row.report_kind.startswith("eyetech"):
        # EyeTech's chosen display spelling is ידוד.  Keep it on screen even
        # when a corpus match supplied the canonical spelling internally.
        displayed = str(text or "")
        for pattern, hidden in EYETECH_SACRED_DISPLAY_PATTERNS:
            displayed = pattern.sub(hidden, displayed)
        return displayed
    return normalize_divine_names_for_display(text)


DISPLAY_DIVINE_NAME_PATTERN = re.compile(
    rf"י[{HEBREW_DIACRITICS}]*ק[{HEBREW_DIACRITICS}]*ו[{HEBREW_DIACRITICS}]*ק"
)


def restore_divine_names_from_display(text: str) -> str:
    """Convert the display-only spelling back before saving or matching."""
    return DISPLAY_DIVINE_NAME_PATTERN.sub("יהוה", str(text or ""))


_NIKUD_CORPUS: dict[str, dict[str, str]] | None = None
_HEBREW_SPEECH_TOKEN = re.compile(
    r"[\u05d0-\u05ea\u0591-\u05bd\u05bf\u05c1\u05c2\u05c4\u05c5\u05c7]+"
)


def _load_nikud_corpus() -> dict[str, dict[str, str]]:
    global _NIKUD_CORPUS
    if _NIKUD_CORPUS is not None:
        return _NIKUD_CORPUS
    try:
        payload = json.loads(resource_path("torah_nikud.json").read_text(encoding="utf-8"))
        pages = payload.get("pages", {}) if isinstance(payload, dict) else {}
        if not isinstance(pages, dict):
            pages = {}
        _NIKUD_CORPUS = {
            str(page): {str(line): str(text) for line, text in lines.items()}
            for page, lines in pages.items()
            if isinstance(lines, dict)
        }
    except (OSError, ValueError, TypeError):
        _NIKUD_CORPUS = {}
    return _NIKUD_CORPUS


def _speech_word_key(text: str) -> str:
    decomposed = unicodedata.normalize("NFD", str(text or ""))
    consonants = "".join(character for character in decomposed if "א" <= character <= "ת")
    return consonants.replace("יקוק", "יהוה")


def _remove_cantillation(text: str) -> str:
    # Cantillation marks can confuse speech engines; vowel points, dagesh and
    # shin/sin dots are intentionally retained for pronunciation.
    return "".join(
        character for character in str(text or "")
        if not "\u0591" <= character <= "\u05af"
    )


def _speech_units(text: str) -> list[str]:
    return [unit for unit in _HEBREW_SPEECH_TOKEN.findall(str(text or "")) if _speech_word_key(unit)]


def _find_vocalized_phrase(source: str, query: str, prefer_start: bool = False) -> str:
    source_units = _speech_units(source)
    source_keys = [_speech_word_key(unit) for unit in source_units]
    query_keys = [_speech_word_key(unit) for unit in _speech_units(query)]
    query_keys = [key for key in query_keys if key]
    if not source_units or not query_keys:
        return str(query or "")

    width = len(query_keys)
    matches: list[list[str]] = []
    for start in range(0, len(source_keys) - width + 1):
        if source_keys[start:start + width] == query_keys:
            matches.append(source_units[start:start + width])
            if prefer_start and start == 0:
                matches = [matches[-1]]
                break

    if not matches and width == 1:
        query_key = query_keys[0]
        scored = sorted(
            (
                (difflib.SequenceMatcher(None, query_key, key).ratio(), index)
                for index, key in enumerate(source_keys)
            ),
            reverse=True,
        )
        if scored:
            best_key = source_keys[scored[0][1]]
            distance = _letter_edit_distance(query_key, best_key)
            safe_typo = (
                (distance == 1 and min(len(query_key), len(best_key)) >= 2)
                or (
                    distance <= 2
                    and max(len(query_key), len(best_key)) >= 6
                    and scored[0][0] >= 0.76
                )
            )
            runner_up = scored[1][0] if len(scored) > 1 else 0.0
            if safe_typo and scored[0][0] - runner_up >= 0.12:
                matches = [[source_units[scored[0][1]]]]

    if not matches and width > 1:
        # OCR occasionally joins neighbouring words or confuses one or two
        # letters. Compare compact consonant strings over a few nearby window
        # sizes, but accept only a strong, unambiguous match. This lets the
        # known vocalized Torah text correct OCR without making unsafe guesses.
        query_compact = "".join(query_keys)
        candidates: list[tuple[float, int, int]] = []
        minimum_window = max(1, width - 1)
        maximum_window = min(len(source_units), width + 2)
        for candidate_width in range(minimum_window, maximum_window + 1):
            for start in range(0, len(source_keys) - candidate_width + 1):
                source_compact = "".join(source_keys[start:start + candidate_width])
                score = difflib.SequenceMatcher(None, query_compact, source_compact).ratio()
                candidates.append((score, start, candidate_width))
        candidates.sort(reverse=True)
        if candidates and candidates[0][0] >= 0.88:
            best_score, best_start, best_width = candidates[0]
            runner_up = next(
                (
                    score for score, start, candidate_width in candidates[1:]
                    if (start, candidate_width) != (best_start, best_width)
                ),
                0.0,
            )
            if best_score - runner_up >= 0.03:
                matches = [source_units[best_start:best_start + best_width]]

    if not matches:
        return str(query or "")
    rendered = {
        " ".join(_remove_cantillation(unit) for unit in match)
        for match in matches
    }
    if len(rendered) != 1:
        return str(query or "")
    return next(iter(rendered))


def vocalize_report_text(
    page: str, line: str, text: str, *, line_start: bool = False, whole_page: bool = False,
) -> str:
    """Return a safely matched vocalized reading without changing displayed OCR text."""
    if not str(text or "").strip():
        return str(text or "")
    try:
        page_key = str(int(re.search(r"\d+", str(page)).group()))
    except (AttributeError, TypeError, ValueError):
        return str(text)
    page_lines = _load_nikud_corpus().get(page_key)
    if not page_lines:
        return str(text)
    if whole_page:
        source = " ".join(page_lines.get(str(number), "") for number in range(1, 43))
        return _find_vocalized_phrase(source, text, prefer_start=False)
    try:
        line_key = str(int(re.search(r"\d+", str(line)).group()))
    except (AttributeError, TypeError, ValueError):
        return str(text)
    source = page_lines.get(line_key, "")
    if not source:
        return str(text)
    return _find_vocalized_phrase(source, text, prefer_start=line_start)


def _letter_edit_distance(first: str, second: str) -> int:
    if first == second:
        return 0
    previous = list(range(len(second) + 1))
    for first_index, first_character in enumerate(first, start=1):
        current = [first_index]
        for second_index, second_character in enumerate(second, start=1):
            current.append(min(
                current[-1] + 1,
                previous[second_index] + 1,
                previous[second_index - 1] + (first_character != second_character),
            ))
        previous = current
    return previous[-1]


def safely_correct_first_word_from_corpus(page: str, line: str, raw_text: str) -> str:
    """Fix a likely OCR typo without replacing a visually different word."""
    raw_key = _speech_word_key(raw_text)
    if not raw_key:
        return raw_text
    try:
        page_key = str(int(re.search(r"\d+", str(page)).group()))
        line_key = str(int(re.search(r"\d+", str(line)).group()))
    except (AttributeError, TypeError, ValueError):
        return raw_text
    source = _load_nikud_corpus().get(page_key, {}).get(line_key, "")
    source_units = _speech_units(source)
    if not source_units:
        return raw_text
    known_unit = source_units[0]
    known_key = _speech_word_key(known_unit)
    distance = _letter_edit_distance(raw_key, known_key)
    similarity = difflib.SequenceMatcher(None, raw_key, known_key).ratio()
    safe_typo = (
        distance == 0
        or (distance == 1 and min(len(raw_key), len(known_key)) >= 2)
        or (distance <= 2 and max(len(raw_key), len(known_key)) >= 6 and similarity >= 0.76)
    )
    if not safe_typo:
        return raw_text
    return _remove_cantillation(known_unit)


def corpus_corrected_ocr_values(row: ReportRow) -> tuple[str, str, str]:
    """Correct OCR text contextually from the known page and Torah line.

    The raw OCR fields remain untouched so user-created learning rules can
    still refer to the actual recognition error. Returned values contain no
    niqqud because these values are shown in the editor and rows table; speech
    receives the vocalized form separately.
    """
    raw_start = row.ocr_start or row.start
    raw_first = row.ocr_first_word or row.first_word
    raw_problem = row.ocr_problem_word or row.problem_word
    corrected_start = _correction_key(vocalize_report_text(
        row.page, row.line, raw_start, whole_page=True,
    )) or raw_start
    corrected_first = _correction_key(safely_correct_first_word_from_corpus(
        row.page, row.line, raw_first,
    )) or raw_first
    corrected_problem = _correction_key(vocalize_report_text(
        row.page, row.line, raw_problem,
    )) or raw_problem
    if _correction_key(raw_first) == _correction_key(raw_problem):
        # When OCR found only one bold token, keep both fields together after
        # correcting the authoritative first word for this numbered line.
        corrected_problem = corrected_first
    return corrected_start, corrected_first, corrected_problem


def hebrew_word(text: str) -> str:
    return "".join(re.findall(r"[\u0590-\u05ff]+", text))


def normalize_description(text: str) -> str:
    value = clean_hebrew_text(text)
    compact = re.sub(r"[\"'׳״/\\-]", " ", value)
    compact = re.sub(r"\s+", " ", compact)
    if (
        "אותיות מחוברות" in compact
        or "חשש נגיעה בין האות" in compact
        or ("נגיעה" in compact and "אות" in compact)
        or ("דביק" in compact and "אות" in compact)
    ):
        return "דיבוק"
    if "חשש אות שבורה" in compact or "אות שבורה" in compact:
        return "נתק"
    if (
        "בעיה בצורת האות" in compact
        or "צורת האות" in compact
        or "אות מוחלפת" in compact
        or "אותיות מוחלפות" in compact
    ):
        return "בעיה"
    tag_variants = ("בעית תגים", "בעיית תגים", "בעית הגים", "בעיית הגים", "תגים", "הגים")
    tag_similarity = max(
        (difflib.SequenceMatcher(None, compact, variant).ratio() for variant in tag_variants),
        default=0.0,
    )
    if any(variant in compact for variant in tag_variants) or tag_similarity >= 0.76:
        return "תגים"
    known = [
        "אות חסרה", "אות מיותרת", "אות מוחלפת", "אותיות חסרות", "אותיות מוחלפות",
        "מילה חסרה", "מילה מיותרת", "מילים חסרות", "חשש אברים נוגעים",
        "מומלץ לתקן", "כתם", "צורה לא תקינה", "מילה חסרה שורה מעל",
    ]
    if value:
        best = max(known, key=lambda item: difflib.SequenceMatcher(None, value, item).ratio())
        if difflib.SequenceMatcher(None, value, best).ratio() >= 0.64:
            return best
    return value


def normalize_report_description(text: str, report_kind: str = "classic") -> str:
    """Keep EyeTech's full description; classic reports use spoken shorthand."""
    if report_kind.startswith("eyetech"):
        return clean_hebrew_text(text)
    return normalize_description(text)


KNOWN_PROBLEM_TYPES = {"תגים", "בעיה", "דיבוק", "נתק", "חסרות", "יתירות"}


def normalize_problem_type(value: str) -> str:
    normalized = normalize_description(value)
    compact = clean_hebrew_text(normalized)
    if "מוחל" in compact or "צורת" in compact:
        return "בעיה"
    if "חסר" in compact:
        return "חסרות"
    if "יתר" in compact or "יתיר" in compact:
        return "יתירות"
    return normalized


def problem_type_needs_refinement(value: str) -> bool:
    normalized = normalize_problem_type(value)
    return not normalized or normalized not in KNOWN_PROBLEM_TYPES


LEARNED_RULE_SCOPES = {
    "first_word": "word",
    "problem_word": "word",
    "start": "start",
    "problem_type": "description",
    "description": "description",
}
DEFAULT_LEARNED_RULES = [
    {"scope": "word", "wrong": "פל", "correct": "פי", "created": "תיקון ראשוני"},
    {"scope": "word", "wrong": "לשראל", "correct": "ישראל", "created": "תיקון ראשוני"},
]


def learned_corrections_path() -> Path:
    return app_data_dir() / "learned-corrections.json"


def server_learned_corrections_path() -> Path:
    return app_data_dir() / "server-learned-corrections.json"


def rule_sync_pending_path() -> Path:
    return app_data_dir() / "rule-sync-pending.json"


def rule_sync_secret_path() -> Path:
    return app_data_dir() / "rule-sync.json"


def _correction_key(text: str) -> str:
    value = unicodedata.normalize("NFKC", clean_hebrew_text(text))
    value = re.sub(r"[\u0591-\u05c7]", "", value)
    value = re.sub(r"\s+", " ", value).strip()
    return value.replace("יקוק", "יהוה")


def _load_learned_rules_file(
    path: Path, *, source_override: str = "",
) -> list[dict[str, object]]:
    if not path.exists():
        return []
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
        raw_rules = payload.get("rules", []) if isinstance(payload, dict) else []
    except (OSError, ValueError, TypeError):
        return []
    rules: list[dict[str, object]] = []
    seen: set[tuple[str, str, str]] = set()
    for item in raw_rules:
        if not isinstance(item, dict):
            continue
        scope = str(item.get("scope", ""))
        wrong = clean_hebrew_text(str(item.get("wrong", "")))
        correct = clean_hebrew_text(str(item.get("correct", "")))
        key = _correction_key(wrong)
        if scope not in {"word", "start", "description"} or not key or not correct:
            continue
        identity = (scope, key, str(item.get("report_kind", "")))
        if identity in seen:
            continue
        seen.add(identity)
        rule: dict[str, object] = {
            "scope": scope,
            "wrong": wrong,
            "correct": correct,
            "created": str(item.get("created", "")),
        }
        for metadata_name in (
            "field", "report_kind", "source", "ai_reason", "ai_error_type",
            "ai_apply_mode", "ai_image", "ai_analyzed",
        ):
            metadata_value = item.get(metadata_name)
            if metadata_value not in (None, ""):
                rule[metadata_name] = str(metadata_value)
        for numeric_name in ("ai_confidence", "minimum_similarity", "example_count"):
            try:
                rule[numeric_name] = float(item.get(numeric_name, 0) or 0)
            except (TypeError, ValueError):
                pass
        if source_override:
            rule["source"] = source_override
        rules.append(rule)
    return rules


def load_local_learned_rules() -> list[dict[str, object]]:
    rules = _load_learned_rules_file(learned_corrections_path())
    return rules if learned_corrections_path().exists() else [dict(rule) for rule in DEFAULT_LEARNED_RULES]


def load_server_learned_rules() -> list[dict[str, object]]:
    return _load_learned_rules_file(
        server_learned_corrections_path(), source_override="server-approved",
    )


def load_learned_rules() -> list[dict[str, object]]:
    # Server rules are loaded first. A local rule with the same identity always
    # wins, so a customer's own correction is never overwritten by a sync.
    merged: dict[tuple[str, str, str], dict[str, object]] = {}
    for rule in load_server_learned_rules() + load_local_learned_rules():
        identity = (
            str(rule.get("scope", "")),
            _correction_key(str(rule.get("wrong", ""))),
            str(rule.get("report_kind", "")),
        )
        if identity[0] and identity[1]:
            merged[identity] = rule
    return list(merged.values())


def save_learned_rules(rules: list[dict[str, object]]) -> None:
    path = learned_corrections_path()
    temporary = path.with_suffix(".tmp")
    # Synchronized server rules are read-only. Never copy them into the local
    # editable file, otherwise deleting or replacing a remote rule would be
    # impossible to manage safely on the server.
    local_rules = [
        rule for rule in rules if str(rule.get("source", "")) != "server-approved"
    ]
    payload = {"version": 2, "rules": local_rules}
    temporary.write_text(json.dumps(payload, ensure_ascii=False, indent=2), encoding="utf-8")
    temporary.replace(path)


def add_learned_rule(
    scope: str, wrong: str, correct: str, metadata: dict[str, object] | None = None,
) -> bool:
    wrong = clean_hebrew_text(wrong)
    correct = clean_hebrew_text(correct)
    wrong_key = _correction_key(wrong)
    if scope not in {"word", "start", "description"} or not wrong_key or not correct:
        return False
    if wrong_key == _correction_key(correct):
        return False
    rules = load_learned_rules()
    metadata = dict(metadata or {})
    changed = False
    updated = False
    for rule in rules:
        if str(rule["scope"]) == scope and _correction_key(str(rule["wrong"])) == wrong_key:
            if str(rule["correct"]) != correct or str(rule["wrong"]) != wrong:
                rule["wrong"] = wrong
                rule["correct"] = correct
                rule["created"] = datetime.now().isoformat(timespec="seconds")
                changed = True
            old_count = int(float(rule.get("example_count", 0) or 0))
            rule["example_count"] = old_count + 1
            for key, value in metadata.items():
                if value not in (None, "") and rule.get(key) != value:
                    rule[key] = value
                    changed = True
            updated = True
            break
    if not updated:
        new_rule: dict[str, object] = {
            "scope": scope, "wrong": wrong, "correct": correct,
            "created": datetime.now().isoformat(timespec="seconds"),
            "example_count": 1,
        }
        new_rule.update({key: value for key, value in metadata.items() if value not in (None, "")})
        rules.append(new_rule)
        changed = True
    if changed:
        save_learned_rules(rules)
    return changed


def annotate_learned_rule(
    scope: str, wrong: str, correct: str, metadata: dict[str, object],
) -> bool:
    rules = load_learned_rules()
    identity = _correction_key(wrong)
    changed = False
    for rule in rules:
        if (
            str(rule.get("scope", "")) == scope
            and _correction_key(str(rule.get("wrong", ""))) == identity
            and _correction_key(str(rule.get("correct", ""))) == _correction_key(correct)
        ):
            for key, value in metadata.items():
                if value not in (None, "") and rule.get(key) != value:
                    rule[key] = value
                    changed = True
            break
    if changed:
        save_learned_rules(rules)
    return changed


def ensure_ocr_baseline(row: ReportRow) -> None:
    if not row.ocr_start and row.start:
        row.ocr_start = row.start
    if not row.ocr_first_word and row.first_word:
        row.ocr_first_word = row.first_word
    if not row.ocr_problem_word and row.problem_word:
        row.ocr_problem_word = row.problem_word
    if not row.ocr_problem_type and row.problem_type:
        row.ocr_problem_type = normalize_problem_type(row.problem_type)
    if not row.ocr_description and row.description:
        row.ocr_description = normalize_report_description(row.description, row.report_kind)


def apply_learned_rules_to_rows(
    rows: list[ReportRow], rules: list[dict[str, object]] | None = None,
) -> int:
    if rules is None:
        rules = load_learned_rules()
    lookup: dict[tuple[str, str, str], str] = {}
    similar_rules: dict[tuple[str, str], list[dict[str, object]]] = {}
    for rule in rules:
        scope = str(rule.get("scope", ""))
        wrong = _correction_key(str(rule.get("wrong", "")))
        correct = str(rule.get("correct", ""))
        report_kind = str(rule.get("report_kind", ""))
        if scope and wrong and correct:
            lookup[(scope, wrong, report_kind)] = correct
            try:
                confidence = float(rule.get("ai_confidence", 0) or 0)
                minimum = float(rule.get("minimum_similarity", 0.92) or 0.92)
            except (TypeError, ValueError):
                confidence, minimum = 0.0, 0.92
            if (
                str(rule.get("ai_apply_mode", "")) == "similar"
                and confidence >= 0.90 and scope == "word"
            ):
                copied = dict(rule)
                copied["minimum_similarity"] = max(0.90, min(0.99, minimum))
                similar_rules.setdefault((scope, report_kind), []).append(copied)
    changed = 0
    for row in rows:
        ensure_ocr_baseline(row)
        original = (
            row.start, row.first_word, row.problem_word,
            row.problem_type, row.description,
        )
        # OCR always starts with the report image. The corpus may repair only
        # a close spelling error; it can no longer replace a different word by
        # position alone. User-learned rules retain the highest priority.
        corpus_start, corpus_first, corpus_problem = corpus_corrected_ocr_values(row)

        def learned_value(scope: str, value: str, fallback: str) -> str:
            key = _correction_key(value)
            exact = lookup.get(
                (scope, key, row.report_kind),
                lookup.get((scope, key, "")),
            )
            if exact is not None:
                return exact
            # Similar matching is deliberately narrow: only single words,
            # only AI-reviewed user examples, and only with a clear winner.
            if scope != "word" or not key or " " in key:
                return fallback
            candidates: list[tuple[float, dict[str, object]]] = []
            for report_kind in (row.report_kind, ""):
                for rule in similar_rules.get((scope, report_kind), []):
                    wrong_key = _correction_key(str(rule.get("wrong", "")))
                    if abs(len(key) - len(wrong_key)) > 1:
                        continue
                    score = difflib.SequenceMatcher(None, key, wrong_key).ratio()
                    if score >= float(rule.get("minimum_similarity", 0.92)):
                        candidates.append((score, rule))
            candidates.sort(key=lambda item: item[0], reverse=True)
            if not candidates:
                return fallback
            if len(candidates) > 1 and candidates[0][0] - candidates[1][0] < 0.06:
                return fallback
            return str(candidates[0][1].get("correct", fallback))

        def corrected_value(
            scope: str, raw_value: str, corpus_value: str, ai_value: str | None = None,
        ) -> str:
            baseline = clean_hebrew_text(str(ai_value or "")) or corpus_value
            baseline = learned_value(scope, corpus_value, baseline)
            return learned_value(scope, raw_value, baseline)

        row.start = corrected_value("start", row.ocr_start, corpus_start, row.ai_start)
        row.first_word = corrected_value(
            "word", row.ocr_first_word, corpus_first, row.ai_first_word,
        )
        row.problem_word = corrected_value(
            "word", row.ocr_problem_word, corpus_problem, row.ai_problem_word,
        )
        baseline_problem_type = normalize_problem_type(row.ocr_problem_type)
        ai_problem_type = normalize_problem_type(str(row.ai_problem_type or ""))
        row.problem_type = learned_value(
            "description", baseline_problem_type, ai_problem_type or baseline_problem_type,
        )
        baseline_description = normalize_report_description(
            row.ocr_description, row.report_kind,
        )
        ai_description = normalize_report_description(
            str(row.ai_description or ""), row.report_kind,
        )
        row.description = learned_value(
            "description", baseline_description, ai_description or baseline_description,
        )
        if row.manual_start is not None:
            row.start = row.manual_start
        if row.manual_first_word is not None:
            row.first_word = row.manual_first_word
        if row.manual_problem_word is not None:
            row.problem_word = row.manual_problem_word
        if row.manual_problem_type is not None:
            row.problem_type = normalize_problem_type(row.manual_problem_type)
        if row.manual_description is not None:
            row.description = normalize_report_description(
                row.manual_description, row.report_kind,
            )
        if original != (
            row.start, row.first_word, row.problem_word,
            row.problem_type, row.description,
        ):
            changed += 1
    return changed


def locate_tesseract() -> Path:
    candidates = [
        Path(os.environ.get("ProgramFiles", r"C:\Program Files")) / "Tesseract-OCR" / "tesseract.exe",
        Path(os.environ.get("ProgramFiles(x86)", r"C:\Program Files (x86)")) / "Tesseract-OCR" / "tesseract.exe",
    ]
    found = shutil.which("tesseract")
    if found:
        candidates.insert(0, Path(found))
    for candidate in candidates:
        if candidate.exists():
            return candidate
    raise RuntimeError("Tesseract OCR לא נמצא. יש להתקין אותו ולסמן את השפה Hebrew.")


def validate_tesseract(tesseract: Path) -> None:
    result = subprocess.run(
        [str(tesseract), "--list-langs"], capture_output=True, text=True,
        encoding="utf-8", errors="replace", creationflags=subprocess.CREATE_NO_WINDOW,
    )
    languages = result.stdout + result.stderr
    if "heb" not in languages.split():
        raise RuntimeError("חבילת השפה heb אינה מותקנת בתיקיית tessdata של Tesseract.")


def cluster_positions(values: np.ndarray, gap: int = 2) -> list[int]:
    if values.size == 0:
        return []
    clusters: list[list[int]] = [[int(values[0])]]
    for value in values[1:]:
        ivalue = int(value)
        if ivalue > clusters[-1][-1] + gap:
            clusters.append([ivalue])
        else:
            clusters[-1].append(ivalue)
    return [int(round(sum(cluster) / len(cluster))) for cluster in clusters]


TABLE_PROFILES: dict[str, tuple[float, ...]] = {
    "classic": (0.030, 0.280, 0.430, 0.750, 0.800, 0.920, 0.970),
    "classic_no_found": (0.030, 0.280, 0.750, 0.800, 0.920, 0.970),
    "eyetech": (0.018, 0.152, 0.286, 0.462, 0.781, 0.832, 0.932, 0.983),
    "eyetech_regular": (0.017, 0.153, 0.330, 0.546, 0.972, 0.991),
}


def _profile_verticals(gray: np.ndarray, report_kind: str) -> tuple[list[int], list[int]]:
    ratios = TABLE_PROFILES[report_kind]
    ink = gray < 160
    height, width = ink.shape
    score = ink.sum(axis=0)
    xs: list[int] = []
    values: list[int] = []
    for index, ratio in enumerate(ratios):
        center = int(round(width * ratio))
        fixed_eyetech_edge = (
            report_kind.startswith("eyetech")
            and index in {0, len(ratios) - 1}
        ) or (report_kind == "eyetech_regular" and index == 4)
        if fixed_eyetech_edge:
            x = max(0, min(width - 1, center))
        else:
            radius_ratio = 0.012 if report_kind == "eyetech" else 0.010
            radius = max(7, int(round(width * radius_ratio)))
            left, right = max(0, center - radius), min(width, center + radius + 1)
            x = left + int(np.argmax(score[left:right]))
        xs.append(x)
        values.append(int(score[x]))
    return xs, values


def detect_report_kind(gray: np.ndarray) -> str:
    height = gray.shape[0]
    scores: dict[str, float] = {}
    profile_values: dict[str, list[int]] = {}
    for kind in TABLE_PROFILES:
        _xs, values = _profile_verticals(gray, kind)
        profile_values[kind] = values
        core = values[1:-1]
        scores[kind] = (sum(core) / max(1, len(core))) / max(1, height)

    if scores["eyetech"] >= 0.48:
        return "eyetech"
    classic_values = profile_values["classic"]
    classic_reference = float(np.median([
        classic_values[1], classic_values[3], classic_values[4], classic_values[5],
    ]))
    has_found_separator = classic_values[2] >= classic_reference * 0.62
    if max(scores["classic"], scores["classic_no_found"]) >= 0.28:
        return "classic" if has_found_separator else "classic_no_found"
    return "eyetech_regular"


def table_column_bounds(xs: list[int], report_kind: str) -> dict[str, tuple[int, int]]:
    if report_kind == "classic":
        return {
            "description": (xs[0], xs[1]), "need": (xs[2], xs[3]),
            "line": (xs[3], xs[4]), "start": (xs[4], xs[5]),
            "page": (xs[5], xs[6]),
        }
    if report_kind == "classic_no_found":
        return {
            "description": (xs[0], xs[1]), "need": (xs[1], xs[2]),
            "line": (xs[2], xs[3]), "start": (xs[3], xs[4]),
            "page": (xs[4], xs[5]),
        }
    if report_kind == "eyetech":
        return {
            "description": (xs[0], xs[1]),
            "problem_type": (xs[1], xs[2]),
            "need": (xs[3], xs[4]),
            "line": (xs[4], xs[5]), "start": (xs[5], xs[6]),
            "page": (xs[6], xs[7]),
        }
    need_left, need_right = xs[3], xs[4]
    # EyeTech's regular layout has no visible divider between the first two
    # textual columns.  ``xs[1]`` is a text-density anchor rather than the
    # actual edge: the description continues to its right (for example the
    # word "נתק"), while the issue type begins farther right.  Keep the split
    # in the whitespace between those two centered labels.
    description_type_split = int(round(xs[1] + (xs[2] - xs[1]) * 0.27))
    # In this layout the line number sits at the extreme right of the wide
    # "צריך להיות" cell.  A tighter crop avoids reading the final letters of
    # the adjacent text as extra digits (for example 6 becoming 610).
    line_left = int(round(need_left + (need_right - need_left) * 0.88))
    return {
        "description": (xs[0], description_type_split),
        "problem_type": (description_type_split, xs[2]),
        "need": (need_left, need_right),
        "line": (line_left, need_right), "start": (0, 0), "page": (0, 0),
    }


def locate_table(gray: np.ndarray, report_kind: str = "") -> tuple[list[int], list[int]]:
    kind = report_kind if report_kind in TABLE_PROFILES else detect_report_kind(gray)
    xs, _values = _profile_verticals(gray, kind)
    height, width = gray.shape
    minimum_gap_ratio = 0.005 if kind == "eyetech_regular" else 0.018
    if any(b - a < width * minimum_gap_ratio for a, b in zip(xs, xs[1:])):
        raise RuntimeError("לא הצלחתי לזהות את עמודות הטבלה.")

    if kind in {"classic", "classic_no_found"}:
        ink = gray < 115
        required_ratio = 0.72
    else:
        ink = gray < 190
        required_ratio = 0.58 if kind == "eyetech_regular" else 0.62
    span = ink[:, xs[0] : xs[-1] + 1].sum(axis=1)
    required = (xs[-1] - xs[0]) * required_ratio
    raw_lines = np.where(span >= required)[0]
    ys = cluster_positions(raw_lines)
    ys = [y for y in ys if width * 0.02 < y < height * 0.99]
    ys = [y for index, y in enumerate(ys) if index == 0 or y - ys[index - 1] >= 18]
    if kind == "eyetech" and len(ys) >= 3:
        large_gap = max(180, int(round(height * 0.12)))
        for index in range(len(ys) - 1, 0, -1):
            if ys[index] - ys[index - 1] >= large_gap:
                ys = ys[index:]
                break
    minimum_lines = 2 if kind.startswith("eyetech") else 3
    if len(ys) < minimum_lines:
        raise RuntimeError("לא הצלחתי לזהות את שורות הטבלה.")
    return xs, ys


IMAGE_TRAINING_WIDTH = 96
IMAGE_TRAINING_HEIGHT = 48
IMAGE_TRAINING_LIMIT = 500
_IMAGE_TRAINING_CACHE: tuple[int, list[dict]] | None = None
_IMAGE_TRAINING_LOCK = threading.RLock()


def image_training_path() -> Path:
    return app_data_dir() / "image-ocr-training.json"


def _normalized_ink_signature(image: Image.Image) -> tuple[np.ndarray, float, str] | None:
    gray = np.asarray(image.convert("L"), dtype=np.uint8)
    if gray.size < 16:
        return None
    low = float(np.percentile(gray, 5))
    high = float(np.percentile(gray, 95))
    if high - low < 18:
        return None
    threshold = min(225.0, low + (high - low) * 0.58)
    ink = gray < threshold
    ys, xs = np.where(ink)
    if not len(xs) or len(xs) < 8:
        return None
    left, right = int(xs.min()), int(xs.max()) + 1
    top, bottom = int(ys.min()), int(ys.max()) + 1
    cropped = ink[top:bottom, left:right]
    source_height, source_width = cropped.shape
    if source_width < 2 or source_height < 2:
        return None
    aspect = source_width / source_height
    maximum_width = IMAGE_TRAINING_WIDTH - 6
    maximum_height = IMAGE_TRAINING_HEIGHT - 6
    scale = min(maximum_width / source_width, maximum_height / source_height)
    target_width = max(1, int(round(source_width * scale)))
    target_height = max(1, int(round(source_height * scale)))
    resized = Image.fromarray((cropped.astype(np.uint8) * 255), mode="L").resize(
        (target_width, target_height), Image.Resampling.BILINEAR,
    )
    normalized = np.zeros((IMAGE_TRAINING_HEIGHT, IMAGE_TRAINING_WIDTH), dtype=bool)
    x = (IMAGE_TRAINING_WIDTH - target_width) // 2
    y = (IMAGE_TRAINING_HEIGHT - target_height) // 2
    normalized[y:y + target_height, x:x + target_width] = np.asarray(resized) >= 110
    packed = np.packbits(normalized.reshape(-1))
    return normalized, aspect, base64.b64encode(packed.tobytes()).decode("ascii")


def _decode_ink_signature(encoded: str) -> np.ndarray | None:
    try:
        packed = np.frombuffer(base64.b64decode(encoded, validate=True), dtype=np.uint8)
        unpacked = np.unpackbits(packed)[:IMAGE_TRAINING_WIDTH * IMAGE_TRAINING_HEIGHT]
        if unpacked.size != IMAGE_TRAINING_WIDTH * IMAGE_TRAINING_HEIGHT:
            return None
        return unpacked.reshape((IMAGE_TRAINING_HEIGHT, IMAGE_TRAINING_WIDTH)).astype(bool)
    except (ValueError, TypeError):
        return None


def load_image_training_records() -> list[dict]:
    path = image_training_path()
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
        raw_samples = payload.get("samples", []) if isinstance(payload, dict) else []
    except (OSError, ValueError, TypeError):
        return []
    records: list[dict] = []
    for item in raw_samples:
        if not isinstance(item, dict):
            continue
        scope = str(item.get("scope", ""))
        correct = clean_hebrew_text(str(item.get("correct", "")))
        signature = str(item.get("signature", ""))
        if scope not in {"word", "start", "description"} or not correct or not signature:
            continue
        try:
            aspect = float(item.get("aspect", 1.0))
        except (TypeError, ValueError):
            continue
        records.append({
            "id": str(item.get("id", "")) or uuid.uuid4().hex,
            "scope": scope,
            "recognized": clean_hebrew_text(str(item.get("recognized", ""))),
            "correct": correct,
            "signature": signature,
            "aspect": max(0.05, min(20.0, aspect)),
            "source": str(item.get("source", "")),
            "created": str(item.get("created", "")),
        })
    return records[-IMAGE_TRAINING_LIMIT:]


def save_image_training_records(records: list[dict]) -> None:
    global _IMAGE_TRAINING_CACHE
    path = image_training_path()
    temporary = path.with_suffix(".tmp")
    payload = {"version": 1, "samples": records[-IMAGE_TRAINING_LIMIT:]}
    temporary.write_text(json.dumps(payload, ensure_ascii=False, indent=2), encoding="utf-8")
    temporary.replace(path)
    with _IMAGE_TRAINING_LOCK:
        _IMAGE_TRAINING_CACHE = None


def add_image_training_sample(
    image: Image.Image, scope: str, recognized: str, correct: str, source: str = "",
) -> dict:
    signature = _normalized_ink_signature(image)
    if signature is None:
        raise ValueError("לא נמצאו בתמונה אותיות ברורות.")
    _mask, aspect, encoded = signature
    record = {
        "id": uuid.uuid4().hex,
        "scope": scope,
        "recognized": clean_hebrew_text(recognized),
        "correct": clean_hebrew_text(correct),
        "signature": encoded,
        "aspect": round(aspect, 5),
        "source": source,
        "created": datetime.now().isoformat(timespec="seconds"),
    }
    records = load_image_training_records()
    records.append(record)
    save_image_training_records(records)
    return record


def _loaded_image_training_samples() -> list[dict]:
    global _IMAGE_TRAINING_CACHE
    path = image_training_path()
    try:
        modified = path.stat().st_mtime_ns
    except OSError:
        return []
    with _IMAGE_TRAINING_LOCK:
        if _IMAGE_TRAINING_CACHE is not None and _IMAGE_TRAINING_CACHE[0] == modified:
            return _IMAGE_TRAINING_CACHE[1]
        loaded: list[dict] = []
        for record in load_image_training_records():
            mask = _decode_ink_signature(record["signature"])
            if mask is not None:
                loaded.append({**record, "mask": mask})
        _IMAGE_TRAINING_CACHE = (modified, loaded)
        return loaded


def _ink_similarity(first: np.ndarray, second: np.ndarray, aspect_ratio: float) -> float:
    best = 0.0
    for y_shift in range(-2, 3):
        for x_shift in range(-2, 3):
            shifted = np.zeros_like(second)
            source_y1 = max(0, -y_shift)
            source_y2 = min(second.shape[0], second.shape[0] - y_shift)
            source_x1 = max(0, -x_shift)
            source_x2 = min(second.shape[1], second.shape[1] - x_shift)
            target_y1, target_y2 = source_y1 + y_shift, source_y2 + y_shift
            target_x1, target_x2 = source_x1 + x_shift, source_x2 + x_shift
            shifted[target_y1:target_y2, target_x1:target_x2] = second[
                source_y1:source_y2, source_x1:source_x2
            ]
            total = int(first.sum()) + int(shifted.sum())
            if total:
                dice = (2.0 * float(np.logical_and(first, shifted).sum())) / total
                best = max(best, dice)
    return best * (0.82 + 0.18 * max(0.0, min(1.0, aspect_ratio)))


def apply_image_training_to_crop(
    image: Image.Image, scope: str, recognized: str,
) -> str:
    if scope not in {"word", "start", "description"}:
        return recognized
    signature = _normalized_ink_signature(image)
    if signature is None:
        return recognized
    mask, aspect, _encoded = signature
    scored_by_label: dict[str, tuple[float, dict]] = {}
    for sample in _loaded_image_training_samples():
        if sample["scope"] != scope:
            continue
        sample_aspect = float(sample["aspect"])
        aspect_ratio = min(aspect, sample_aspect) / max(aspect, sample_aspect)
        score = _ink_similarity(mask, sample["mask"], aspect_ratio)
        previous = scored_by_label.get(sample["correct"])
        if previous is None or score > previous[0]:
            scored_by_label[sample["correct"]] = (score, sample)
    scored = sorted(scored_by_label.values(), key=lambda item: item[0], reverse=True)
    if not scored:
        return recognized
    best_score, best_sample = scored[0]
    same_text_error = (
        _correction_key(recognized)
        and _correction_key(recognized) == _correction_key(best_sample["recognized"])
    )
    required = 0.86 if same_text_error else 0.92
    runner_up = scored[1][0] if len(scored) > 1 else 0.0
    if best_score >= required and best_score - runner_up >= 0.025:
        return str(best_sample["correct"])
    return recognized


class GigaPdfHebrewRecognizer:
    """Run the GigaPDF Hebrew CRNN on an already-detected word crop."""

    def __init__(self) -> None:
        import onnxruntime as ort

        model_dir = resource_path("gigapdf_ocr_model")
        model_path = model_dir / "model.onnx"
        dictionary_path = model_dir / "dict.txt"
        if not model_path.is_file() or not dictionary_path.is_file():
            raise FileNotFoundError("קובצי מודל GigaPDF Hebrew OCR אינם נמצאים")
        dictionary = dictionary_path.read_text(encoding="utf-8-sig").splitlines()
        self.characters = [character for character in dictionary if character]
        if len(self.characters) != 107:
            raise ValueError("מילון התווים של GigaPDF Hebrew OCR אינו תקין")
        self.session = ort.InferenceSession(
            str(model_path), providers=["CPUExecutionProvider"],
        )
        self.input_name = self.session.get_inputs()[0].name
        self.output_name = self.session.get_outputs()[0].name
        self.lock = threading.RLock()

    @staticmethod
    def _prepare(image: Image.Image) -> np.ndarray:
        rgb = image.convert("RGB")
        width, height = rgb.size
        if width < 2 or height < 2:
            raise ValueError("תמונת המילה קטנה מדי")
        padding = max(3, int(round(height * 0.22)))
        padded = Image.new("RGB", (width + padding * 2, height + padding * 2), "white")
        padded.paste(rgb, (padding, padding))
        target_width = max(8, min(2048, int(round(padded.width * 48 / padded.height))))
        resized = padded.resize((target_width, 48), Image.Resampling.BILINEAR)
        pixels = np.asarray(resized, dtype=np.float32) / 127.5 - 1.0
        return np.transpose(pixels, (2, 0, 1))[None, ...]

    def recognize(self, image: Image.Image) -> tuple[str, float]:
        tensor = self._prepare(image)
        with self.lock:
            logits = self.session.run(
                [self.output_name], {self.input_name: tensor},
            )[0][0]
        token_ids = np.argmax(logits, axis=1)
        shifted = logits - np.max(logits, axis=1, keepdims=True)
        probabilities = np.exp(shifted)
        probabilities /= np.sum(probabilities, axis=1, keepdims=True)
        selected = np.max(probabilities, axis=1) * 100.0
        tokens: list[str] = []
        token_scores: list[float] = []
        previous = -1
        for position, raw_token in enumerate(token_ids):
            token = int(raw_token)
            if token != previous and token != 0:
                if 1 <= token <= len(self.characters):
                    tokens.append(self.characters[token - 1])
                    token_scores.append(float(selected[position]))
                elif token == len(self.characters) + 1:
                    tokens.append(" ")
                    token_scores.append(float(selected[position]))
            previous = token
        # The standalone ONNX checkpoint returns a single detected word in
        # logical Hebrew order.  The GigaPDF page runtime reverses a complete
        # visual-order line, but doing that again for our per-word crops would
        # spell every word backwards.
        text = clean_hebrew_text("".join(tokens)).strip()
        score = float(np.mean(token_scores)) if token_scores else 0.0
        return text, score


_GIGAPDF_RECOGNIZER: GigaPdfHebrewRecognizer | None = None
_GIGAPDF_RECOGNIZER_LOCK = threading.RLock()


def giga_recognize_hebrew_crop(image: Image.Image) -> tuple[str, float]:
    global _GIGAPDF_RECOGNIZER
    with _GIGAPDF_RECOGNIZER_LOCK:
        if _GIGAPDF_RECOGNIZER is None:
            _GIGAPDF_RECOGNIZER = GigaPdfHebrewRecognizer()
        recognizer = _GIGAPDF_RECOGNIZER
    return recognizer.recognize(image)


def run_tesseract_tsv(
    tesseract: Path, image_path: Path, language: str = "heb", whitelist: str = "",
    offset_x: int = 0, offset_y: int = 0, psm: int = 6,
    training_scope: str = "", apply_visual_training: bool = False,
    tessdata_dir: Path | None = None,
) -> list[OcrWord]:
    command = [str(tesseract), str(image_path), "stdout", "-l", language, "--psm", str(psm)]
    if tessdata_dir is not None:
        command.extend(["--tessdata-dir", str(tessdata_dir)])
    if whitelist:
        command.extend(["-c", f"tessedit_char_whitelist={whitelist}"])
    # Enable TSV directly instead of loading the bundled ``configs/tsv`` file.
    # A report-specific OCR model can live in a small private tessdata folder
    # that intentionally contains only its traineddata file.
    command.extend(["-c", "tessedit_create_tsv=1"])
    result = subprocess.run(
        command, capture_output=True, text=True, encoding="utf-8", errors="replace",
        creationflags=subprocess.CREATE_NO_WINDOW,
        env={**os.environ, "OMP_THREAD_LIMIT": "1"},
    )
    if result.returncode:
        raise RuntimeError("Tesseract נכשל: " + (result.stderr.strip() or str(result.returncode)))
    words: list[OcrWord] = []
    use_gigapdf = GIGAPDF_OCR_EDITION and language.startswith("heb") and not whitelist
    source_image: Image.Image | None = None
    if use_gigapdf or (
        apply_visual_training and training_scope and _loaded_image_training_samples()
    ):
        try:
            source_image = Image.open(image_path).convert("L")
        except OSError:
            source_image = None
    # Tesseract's TSV text may legitimately start with a quotation mark.  The
    # default CSV quote handling then swallows following TSV rows into that
    # word, so quoting must be disabled for this tab-separated format.
    reader = csv.DictReader(io.StringIO(result.stdout), delimiter="\t", quoting=csv.QUOTE_NONE)
    for record in reader:
        text = clean_hebrew_text(record.get("text", ""))
        if not text:
            continue
        try:
            local_x = int(record["left"])
            local_y = int(record["top"])
            width = int(record["width"])
            height = int(record["height"])
            if use_gigapdf and source_image is not None and width > 1 and height > 1:
                padding = max(2, int(round(height * 0.12)))
                crop = source_image.crop((
                    max(0, local_x - padding), max(0, local_y - padding),
                    min(source_image.width, local_x + width + padding),
                    min(source_image.height, local_y + height + padding),
                ))
                giga_text, giga_confidence = giga_recognize_hebrew_crop(crop)
                original_has_hebrew = bool(re.search(r"[\u0590-\u05ff]", text))
                giga_has_hebrew = bool(re.search(r"[\u0590-\u05ff]", giga_text))
                if giga_text and (giga_has_hebrew or not original_has_hebrew):
                    text = giga_text
                    if giga_confidence:
                        record["conf"] = str(giga_confidence)
            if source_image is not None and width > 1 and height > 1:
                crop = source_image.crop((local_x, local_y, local_x + width, local_y + height))
                text = apply_image_training_to_crop(crop, training_scope, text)
            words.append(OcrWord(
                text=text,
                x=local_x + offset_x, y=local_y + offset_y,
                w=width, h=height,
                conf=float(record.get("conf", -1)),
            ))
        except (ValueError, KeyError):
            continue
    return words


def report_column_ocr_model(report_kind: str, column_name: str) -> tuple[str, Path | None]:
    """Use the Guttman Keren model only for EyeTech/Le'einei start text."""
    tessdata_dir = resource_path("tessdata")
    if (
        report_kind.startswith("eyetech")
        and column_name == "start"
        and (tessdata_dir / "heb_keren.traineddata").is_file()
    ):
        return "heb_keren", tessdata_dir
    return "heb", None


def words_in_cell(words: list[OcrWord], left: int, right: int, top: int, bottom: int) -> list[OcrWord]:
    return [word for word in words if left < word.cx < right and top < word.cy < bottom]


def group_visual_lines(words: list[OcrWord]) -> list[list[OcrWord]]:
    groups: list[list[OcrWord]] = []
    for word in sorted(words, key=lambda item: (item.cy, -item.x)):
        target = None
        for group in groups:
            baseline = sum(item.cy for item in group) / len(group)
            if abs(word.cy - baseline) <= max(9, word.h * 0.45):
                target = group
                break
        if target is None:
            groups.append([word])
        else:
            target.append(word)
    groups.sort(key=lambda group: sum(item.cy for item in group) / len(group))
    for group in groups:
        group.sort(key=lambda item: item.x, reverse=True)
    return groups


def join_rtl(words: list[OcrWord]) -> str:
    return clean_hebrew_text(" ".join(word.text for word in sorted(words, key=lambda item: item.x, reverse=True)))


def join_rtl_visual_lines(words: list[OcrWord]) -> str:
    """Read a multiline Hebrew cell top-to-bottom and each line right-to-left."""
    return clean_hebrew_text(" ".join(join_rtl(line) for line in group_visual_lines(words)))


def embedded_pdf_words(page: object, dpi: int = OCR_DPI) -> list[OcrWord]:
    """Read exact positioned words from a PDF text layer in image coordinates.

    EyeTech regular reports contain two different embedded fonts.  OCRing both
    fonts as pixels loses letters even though the PDF already carries the exact
    Unicode text.  PDFium returns the words in visual left-to-right order; the
    existing ``join_rtl`` helper restores their logical Hebrew order later.
    """
    try:
        text_page = page.get_textpage()
        _page_width, page_height = page.get_size()
    except Exception:
        return []
    scale = dpi / 72.0
    words: list[OcrWord] = []
    token_chars: list[str] = []
    token_boxes: list[tuple[float, float, float, float]] = []

    def flush() -> None:
        if not token_chars or not token_boxes:
            token_chars.clear()
            token_boxes.clear()
            return
        text = clean_hebrew_text("".join(token_chars))
        left = min(box[0] for box in token_boxes) * scale
        right = max(box[2] for box in token_boxes) * scale
        top = (page_height - max(box[3] for box in token_boxes)) * scale
        bottom = (page_height - min(box[1] for box in token_boxes)) * scale
        if text and right > left and bottom > top:
            words.append(OcrWord(
                text=text,
                x=int(round(left)), y=int(round(top)),
                w=max(1, int(round(right - left))),
                h=max(1, int(round(bottom - top))),
                conf=100.0,
            ))
        token_chars.clear()
        token_boxes.clear()

    try:
        for index in range(text_page.count_chars()):
            character = text_page.get_text_range(index, 1)
            if not character or character.isspace():
                flush()
                continue
            try:
                box = tuple(float(value) for value in text_page.get_charbox(index))
            except Exception:
                flush()
                continue
            if len(box) != 4 or box[2] <= box[0] or box[3] <= box[1]:
                flush()
                continue
            token_chars.append(character)
            token_boxes.append(box)
        flush()
    except Exception:
        return []
    finally:
        try:
            text_page.close()
        except Exception:
            pass
    return words


def usable_embedded_hebrew(words: list[OcrWord]) -> bool:
    """Reject image-only or broken text layers and fall back to OCR."""
    return sum(len(hebrew_word(word.text)) for word in words) >= 20


def stroke_thickness(gray: np.ndarray, word: OcrWord) -> float:
    pad = 1
    y1, y2 = max(0, word.y - pad), min(gray.shape[0], word.y + word.h + pad)
    x1, x2 = max(0, word.x - pad), min(gray.shape[1], word.x + word.w + pad)
    binary = gray[y1:y2, x1:x2] < 175
    if binary.size == 0 or binary.sum() == 0:
        return 0.0
    core = binary.copy()
    core[1:-1, 1:-1] &= binary[1:-1, :-2]
    core[1:-1, 1:-1] &= binary[1:-1, 2:]
    core[1:-1, 1:-1] &= binary[:-2, 1:-1]
    core[1:-1, 1:-1] &= binary[2:, 1:-1]
    area = float(binary.sum())
    perimeter = area - float(core.sum())
    return area / max(1.0, perimeter)


def merge_close_words(words: list[OcrWord]) -> list[OcrWord]:
    ordered = sorted(words, key=lambda item: item.x, reverse=True)
    merged: list[OcrWord] = []
    standalone_words = {"אל", "את", "לו", "כל", "כי", "כן", "על", "עם", "מן", "משה", "אני", "אשר", "דבר"}
    for word in ordered:
        if not merged:
            merged.append(word)
            continue
        previous = merged[-1]
        gap = previous.x - (word.x + word.w)
        previous_text = hebrew_word(previous.text)
        word_text = hebrew_word(word.text)
        protected_space = previous_text in standalone_words or word_text in standalone_words
        if not protected_space and gap <= max(5, int(min(previous.h, word.h) * 0.18)):
            text = hebrew_word(previous.text) + hebrew_word(word.text)
            left = min(previous.x, word.x)
            right = max(previous.x + previous.w, word.x + word.w)
            top = min(previous.y, word.y)
            bottom = max(previous.y + previous.h, word.y + word.h)
            merged[-1] = OcrWord(text, left, top, right - left, bottom - top, min(previous.conf, word.conf))
        else:
            merged.append(word)
    return merged


def eyetech_underline_score(
    gray: np.ndarray, word: OcrWord, median_height: float,
) -> float:
    """Score the short underline that EyeTech places below one letter.

    The marked word is also slightly larger, but letter shapes make height
    alone unreliable in Hebrew.  We therefore look near the bottom of the
    word for a horizontal ink run with mostly white space immediately above
    it, then use the larger bounding box only as supporting evidence.
    """
    x0 = max(0, word.x - 3)
    x1 = min(gray.shape[1], word.x + word.w + 3)
    y0 = max(0, word.y - 1)
    y1 = min(gray.shape[0], word.y + word.h + 5)
    mask = gray[y0:y1, x0:x1] < 175
    if mask.size == 0:
        return 0.0
    minimum_run = max(9, int(round(median_height * 0.38)))
    best = 0.0
    lower_start = max(0, int(round(word.h * 0.62)))
    for y in range(lower_start, mask.shape[0]):
        line = mask[y]
        start: int | None = None
        for x in range(mask.shape[1] + 1):
            black = x < mask.shape[1] and bool(line[x])
            if black and start is None:
                start = x
            if not black and start is not None:
                run = x - start
                if run >= minimum_run:
                    above_top = max(0, y - 5)
                    above_bottom = max(0, y - 1)
                    blank_ratio = 0.0
                    if above_bottom > above_top:
                        blank_ratio = 1.0 - float(np.mean(
                            mask[above_top:above_bottom, start:x],
                        ))
                    vertical_ratio = y / max(1.0, float(word.h))
                    height_ratio = word.h / max(1.0, median_height)
                    if blank_ratio >= 0.58 and vertical_ratio >= 0.68:
                        score = (
                            run / minimum_run
                            + blank_ratio * 1.6
                            + vertical_ratio
                            + max(0.0, height_ratio - 1.0) * 2.0
                        )
                        best = max(best, score)
                start = None
    if word.h < median_height * 1.07:
        best *= 0.55
    return best


def cell_reading_words(
    cell_words: list[OcrWord], row_top: int, row_bottom: int,
) -> list[OcrWord]:
    """Return the main Hebrew words of a report cell in reading order."""
    lines = group_visual_lines(cell_words)
    main_lines: list[list[OcrWord]] = []
    for line in lines:
        text = join_rtl(line)
        center_y = sum(word.cy for word in line) / len(line)
        if text.startswith("פ'") or center_y > row_top + (row_bottom - row_top) * 0.72:
            continue
        main_lines.append(line)
    reading_words: list[OcrWord] = []
    for line in main_lines:
        reading_words.extend(merge_close_words([word for word in line if hebrew_word(word.text)]))
    return reading_words


def extract_bold_words(
    gray: np.ndarray, cell_words: list[OcrWord], row_top: int, row_bottom: int,
    *, prefer_underline: bool = False,
) -> tuple[str, str, float]:
    reading_words = cell_reading_words(cell_words, row_top, row_bottom)
    if not reading_words:
        return "", "", 0.0

    first = reading_words[0]
    first_text = hebrew_word(first.text)
    if prefer_underline:
        heights = [word.h for word in reading_words if hebrew_word(word.text)]
        median_height = float(np.median(heights)) if heights else 0.0
        underlined = sorted(
            (
                (eyetech_underline_score(gray, word, median_height), word)
                for word in reading_words
            ),
            key=lambda item: item[0], reverse=True,
        )
        if underlined and underlined[0][0] >= 4.0:
            problem_text = hebrew_word(underlined[0][1].text) or first_text
            confs = [word.conf for word in reading_words if word.conf >= 0]
            confidence = sum(confs) / len(confs) if confs else 0.0
            return first_text, problem_text, confidence

    thicknesses = [(word, stroke_thickness(gray, word)) for word in reading_words]
    regular_values = [value for word, value in thicknesses if value > 0 and hebrew_word(word.text)]
    median = float(np.median(regular_values)) if regular_values else 0.0
    bold_threshold = max(median * 1.15, 2.25)
    heights = [word.h for word in reading_words if hebrew_word(word.text)]
    median_height = float(np.median(heights)) if heights else 0.0
    tall_threshold = max(median_height * 1.28, median_height + 7.0)
    bold = [
        (word, value) for word, value in thicknesses
        if hebrew_word(word.text) and (
            value >= bold_threshold
            or (word.h >= tall_threshold and value >= median * 1.02)
        )
    ]

    problem = first
    for candidate, _value in bold:
        if candidate is first:
            continue
        candidate_text = hebrew_word(candidate.text)
        if candidate_text and candidate_text != first_text:
            problem = candidate
            break
    problem_text = hebrew_word(problem.text) or first_text
    confs = [word.conf for word in reading_words if word.conf >= 0]
    confidence = sum(confs) / len(confs) if confs else 0.0
    return first_text, problem_text, confidence


def exact_problem_word_from_marker(
    gray: np.ndarray, exact_words: list[OcrWord], marker_words: list[OcrWord],
    row_top: int, row_bottom: int,
) -> str:
    """Map a pixel-detected EyeTech mark back to the exact embedded word."""
    marker_first, marker_problem, _confidence = extract_bold_words(
        gray, marker_words, row_top, row_bottom, prefer_underline=True,
    )
    if not marker_problem or marker_problem == marker_first:
        return ""
    marker_reading = cell_reading_words(marker_words, row_top, row_bottom)
    target = next(
        (word for word in marker_reading if hebrew_word(word.text) == marker_problem),
        None,
    )
    exact_reading = cell_reading_words(exact_words, row_top, row_bottom)
    if target is None or not exact_reading:
        return ""

    def geometry_score(word: OcrWord) -> float:
        overlap = max(0.0, min(word.x + word.w, target.x + target.w) - max(word.x, target.x))
        overlap_ratio = overlap / max(1.0, min(float(word.w), float(target.w)))
        center_distance = abs(word.cx - target.cx) / max(20.0, float(max(word.w, target.w)))
        text_similarity = difflib.SequenceMatcher(
            None, hebrew_word(target.text), hebrew_word(word.text),
        ).ratio()
        # Text identity is the strongest signal when Tesseract correctly read
        # the marked word but attached an imprecise rectangle to it.  Geometry
        # remains decisive when OCR made a spelling mistake.
        return overlap_ratio * 2.0 + text_similarity * 4.0 - center_distance

    best = max(exact_reading, key=geometry_score)
    return hebrew_word(best.text)


def digits_from_cell(words: list[OcrWord]) -> str:
    text = " ".join(word.text for word in sorted(words, key=lambda item: item.x, reverse=True))
    matches = re.findall(r"\d+", text)
    return matches[0] if matches else ""


def extract_rows_from_page(
    gray: np.ndarray, words: list[OcrWord], pdf_page: int,
    line_ocr_words: list[OcrWord] | None = None,
    page_ocr_words: list[OcrWord] | None = None,
    start_ocr_words: list[OcrWord] | None = None,
    problem_marker_words: list[OcrWord] | None = None,
    report_kind: str = "classic",
) -> list[ReportRow]:
    xs, ys = locate_table(gray, report_kind)
    bounds = table_column_bounds(xs, report_kind)
    rows: list[ReportRow] = []
    pairs = zip(ys[1:], ys[2:]) if report_kind in {"classic", "classic_no_found"} else zip(ys, ys[1:])
    for top, bottom in pairs:
        if bottom - top < 20:
            continue
        if report_kind == "eyetech_regular":
            # Decorative page headings use a long horizontal arrow that can
            # look like a table row.  A real finding has the rounded table's
            # left border running through most of the interval; a heading
            # does not.  Filtering by that border also keeps the row count
            # equal to the report's own finding count.
            inner_top = min(bottom, top + 4)
            inner_bottom = max(inner_top, bottom - 4)
            border = gray[
                inner_top:inner_bottom,
                max(0, xs[0] - 2):min(gray.shape[1], xs[0] + 3),
            ]
            if border.size == 0 or float(np.mean(border < 190)) < 0.30:
                continue
        desc_words = words_in_cell(words, *bounds["description"], top, bottom)
        problem_type_words = (
            words_in_cell(words, *bounds["problem_type"], top, bottom)
            if "problem_type" in bounds else []
        )
        need_words = words_in_cell(words, *bounds["need"], top, bottom)
        line_words = words_in_cell(line_ocr_words or words, *bounds["line"], top, bottom)
        start_words = words_in_cell(start_ocr_words or [], *bounds["start"], top, bottom)
        page_words = words_in_cell(page_ocr_words or [], *bounds["page"], top, bottom)
        line_number = digits_from_cell(line_words)
        if not line_number:
            continue
        first, problem, confidence = extract_bold_words(
            gray, need_words, top, bottom,
            prefer_underline=report_kind.startswith("eyetech"),
        )
        exact_reading = cell_reading_words(need_words, top, bottom)
        exact_heights = [word.h for word in exact_reading if hebrew_word(word.text)]
        exact_median_height = float(np.median(exact_heights)) if exact_heights else 0.0
        reliable_exact_underline = bool(
            exact_median_height
            and max(
                (eyetech_underline_score(gray, word, exact_median_height) for word in exact_reading),
                default=0.0,
            ) >= 4.0
        )
        if (
            report_kind.startswith("eyetech")
            and problem_marker_words
            and not reliable_exact_underline
        ):
            marker_cell_words = words_in_cell(
                problem_marker_words, *bounds["need"], top, bottom,
            )
            marked_exact = exact_problem_word_from_marker(
                gray, need_words, marker_cell_words, top, bottom,
            )
            if marked_exact:
                problem = marked_exact
        description_raw = join_rtl(desc_words)
        problem_type_raw = join_rtl(problem_type_words)
        start_text = join_rtl_visual_lines(start_words)
        start_text = re.sub(r"[^\u0590-\u05ff\s'׳״\"]", "", start_text).strip()
        rows.append(ReportRow(
            page=digits_from_cell(page_words),
            start=start_text,
            line=line_number,
            first_word=first,
            problem_word=problem or first,
            problem_type=normalize_problem_type(problem_type_raw),
            description=normalize_report_description(description_raw, report_kind),
            source_pdf_page=pdf_page,
            confidence=round(confidence, 1),
            row_left=xs[0] / gray.shape[1],
            row_top=top / gray.shape[0],
            row_right=xs[-1] / gray.shape[1],
            row_bottom=bottom / gray.shape[0],
            report_kind=report_kind,
        ))
    return rows


def parse_regular_header(text: str) -> tuple[str, str]:
    normalized = clean_hebrew_text(text)
    page_match = re.search(r"עמוד\D{0,12}(\d{1,3})", normalized)
    if page_match is None:
        page_match = re.search(r"מס[׳']?\D{0,5}(\d{1,3})", normalized)
    page = page_match.group(1) if page_match else ""
    start = ""
    start_match = re.search(r"המתחיל\s+(.+)", normalized)
    if start_match:
        start = re.sub(r"[^\u0590-\u05ff\s'׳״\"]", " ", start_match.group(1))
        start = clean_hebrew_text(start).strip(" '׳״\"")
    elif page_match:
        # On the large decorative heading Tesseract occasionally recognizes
        # the actual opening words but drops only the label "המתחיל".
        remainder = normalized[page_match.end():]
        start = re.sub(r"[^\u0590-\u05ff\s'׳״\"]", " ", remainder)
        start = clean_hebrew_text(start).strip(" '׳״\"")
        tokens = start.split()
        if tokens and difflib.SequenceMatcher(None, tokens[0], "המתחיל").ratio() >= 0.68:
            start = " ".join(tokens[1:])
    # Decorative quotation marks are drawn at the visual ends of this RTL
    # heading and can otherwise remain attached to the last opening word.
    start = re.sub(r"['׳״\"]", "", start).strip()
    return page, start


def rerecognize_report_row(
    pdf_path: Path, row: ReportRow,
) -> tuple[dict[str, str | float], dict[str, list[tuple[str, Image.Image]]]]:
    """Run OCR again on one report row and return visual word candidates."""
    if row.source_pdf_page <= 0:
        raise ValueError("לשורה הזאת אין מספר דף PDF תקין.")
    tesseract = locate_tesseract()
    validate_tesseract(tesseract)
    document = pdfium.PdfDocument(str(pdf_path))
    try:
        page = document[row.source_pdf_page - 1]
        try:
            bitmap = page.render(scale=OCR_DPI / 72.0)
            image = bitmap.to_pil().convert("L")
        finally:
            page.close()
    finally:
        document.close()
    gray = np.asarray(image)
    report_kind = row.report_kind if row.report_kind in TABLE_PROFILES else detect_report_kind(gray)
    xs, ys = locate_table(gray, report_kind)
    bounds = table_column_bounds(xs, report_kind)
    cleaned = np.array(gray)
    for x in xs:
        cleaned[:, max(0, x - 2):x + 3] = 255
    for y in ys:
        cleaned[max(0, y - 2):y + 3, :] = 255
    top = max(0, int(round(row.row_top * gray.shape[0])) + 3)
    bottom = min(gray.shape[0], int(round(row.row_bottom * gray.shape[0])) - 3)
    if bottom - top < 10:
        raise ValueError("לא ניתן לאתר את גבולות השורה בתמונה.")
    specs = {
        "description": (bounds["description"][0] + 3, bounds["description"][1] - 2, "description"),
        "need": (bounds["need"][0] + 3, bounds["need"][1] - 2, "word"),
    }
    if report_kind.startswith("eyetech"):
        specs["problem_type"] = (
            bounds["problem_type"][0] + 3,
            bounds["problem_type"][1] - 2,
            "description",
        )
    if report_kind != "eyetech_regular":
        specs["start"] = (bounds["start"][0] + 3, bounds["start"][1] - 2, "start")
    column_words: dict[str, list[OcrWord]] = {}
    visual_candidates: dict[str, list[tuple[str, Image.Image]]] = {
        "word": [], "start": [], "description": [],
    }
    temp_dir = Path(tempfile.mkdtemp(prefix="duk-reread-row-"))
    try:
        for name, (left, right, training_scope) in specs.items():
            crop_path = temp_dir / f"{name}.png"
            Image.fromarray(cleaned[top:bottom, left:right]).save(crop_path, "PNG")
            language, tessdata_dir = report_column_ocr_model(report_kind, name)
            words = run_tesseract_tsv(
                tesseract, crop_path, language=language, psm=6,
                offset_x=left, offset_y=top, training_scope=training_scope,
                tessdata_dir=tessdata_dir,
            )
            column_words[name] = words
            for word in words:
                padding = max(2, int(round(word.h * 0.10)))
                word_crop = image.crop((
                    max(0, word.x - padding), max(0, word.y - padding),
                    min(image.width, word.x + word.w + padding),
                    min(image.height, word.y + word.h + padding),
                ))
                visual_candidates[training_scope].append((word.text, word_crop))
    finally:
        shutil.rmtree(temp_dir, ignore_errors=True)

    first, problem, confidence = extract_bold_words(
        gray, column_words.get("need", []), top, bottom,
        prefer_underline=report_kind.startswith("eyetech"),
    )
    start = join_rtl_visual_lines(column_words.get("start", [])) or row.ocr_start or row.start
    start = re.sub(r"[^\u0590-\u05ff\s'׳״\"]", "", start).strip()
    description = normalize_report_description(
        join_rtl(column_words.get("description", [])), report_kind,
    )
    problem_type = normalize_problem_type(join_rtl(column_words.get("problem_type", [])))
    values: dict[str, str | float] = {
        "start": start,
        "first_word": first,
        "problem_word": problem or first,
        "problem_type": problem_type,
        "description": description,
        "confidence": round(confidence, 1),
    }
    return values, visual_candidates


def render_report_row_crop(pdf_path: Path, row: ReportRow, dpi: int = OCR_DPI) -> Image.Image:
    """Render the complete original report row for correction dialogs."""
    if row.source_pdf_page <= 0:
        raise ValueError("לשורה הזאת אין מספר דף PDF תקין.")
    document = pdfium.PdfDocument(str(pdf_path))
    try:
        page = document[row.source_pdf_page - 1]
        try:
            bitmap = page.render(scale=dpi / 72.0)
            page_image = bitmap.to_pil().convert("RGB")
        finally:
            page.close()
    finally:
        document.close()
    left = max(0, int(round(row.row_left * page_image.width)))
    right = min(page_image.width, int(round(row.row_right * page_image.width)))
    top = max(0, int(round(row.row_top * page_image.height)))
    bottom = min(page_image.height, int(round(row.row_bottom * page_image.height)))
    if right - left < 20 or bottom - top < 10:
        raise ValueError("לא ניתן לאתר את תמונת השורה בדוח.")
    return page_image.crop((left, top, right, bottom))


def best_visual_candidate(
    candidates: list[tuple[str, Image.Image]], wrong_text: str,
) -> tuple[str, Image.Image] | None:
    wrong_key = _correction_key(wrong_text)
    if not candidates or not wrong_key:
        return None
    scored = sorted(
        (
            (difflib.SequenceMatcher(None, wrong_key, _correction_key(text)).ratio(), text, image)
            for text, image in candidates if _correction_key(text)
        ),
        key=lambda item: item[0], reverse=True,
    )
    if not scored or scored[0][0] < 0.60:
        return None
    return scored[0][1], scored[0][2]


def single_word_correction_pairs(wrong_text: str, correct_text: str) -> list[tuple[str, str]]:
    wrong_units = _speech_units(wrong_text)
    correct_units = _speech_units(correct_text)
    if len(wrong_units) == 1 and len(correct_units) == 1:
        return [(wrong_units[0], correct_units[0])]
    wrong_keys = [_speech_word_key(unit) for unit in wrong_units]
    correct_keys = [_speech_word_key(unit) for unit in correct_units]
    matcher = difflib.SequenceMatcher(None, wrong_keys, correct_keys)
    pairs: list[tuple[str, str]] = []
    for operation, wrong_start, wrong_end, correct_start, correct_end in matcher.get_opcodes():
        if operation == "replace" and wrong_end - wrong_start == 1 and correct_end - correct_start == 1:
            pairs.append((wrong_units[wrong_start], correct_units[correct_start]))
    return pairs


class ReportOcr:
    def __init__(self, progress: Callable[[str, int, int], None]):
        self.progress = progress
        self.tesseract = locate_tesseract()
        validate_tesseract(self.tesseract)

    def cache_path(self, pdf_path: Path) -> Path:
        return cache_path_for_pdf(pdf_path)

    def _prepare_pdf_page(
        self, document: pdfium.PdfDocument, pdf_page: int, temp_dir: Path,
        report_kind: str,
    ) -> tuple[Path, Path, list[int], list[int], list[OcrWord]]:
        page = document[pdf_page - 1]
        try:
            bitmap = page.render(scale=OCR_DPI / 72.0)
            image = bitmap.to_pil().convert("L")
            exact_words = (
                embedded_pdf_words(page, OCR_DPI)
                if report_kind.startswith("eyetech") else []
            )
        finally:
            page.close()
        gray = np.asarray(image)
        xs, ys = locate_table(gray, report_kind)
        cleaned = np.array(gray)
        for x in xs:
            cleaned[:, max(0, x - 2) : x + 3] = 255
        for y in ys:
            cleaned[max(0, y - 2) : y + 3, :] = 255

        gray_path = temp_dir / f"page-{pdf_page:03}-gray.bmp"
        clean_path = temp_dir / f"page-{pdf_page:03}-clean.bmp"
        Image.fromarray(gray).save(gray_path, "BMP")
        Image.fromarray(cleaned).save(clean_path, "BMP")
        return gray_path, clean_path, xs, ys, exact_words

    def _ocr_prepared_page(
        self, pdf_page: int, gray_path: Path, clean_path: Path,
        xs: list[int], ys: list[int], temp_dir: Path, report_kind: str,
        exact_words: list[OcrWord] | None = None,
    ) -> list[ReportRow]:
        gray = np.asarray(Image.open(gray_path).convert("L"))
        cleaned = np.asarray(Image.open(clean_path).convert("L"))
        exact_words = list(exact_words or [])
        use_exact_text = report_kind.startswith("eyetech") and usable_embedded_hebrew(exact_words)

        top, bottom = ys[0] + 3, ys[-1] - 2
        bounds = table_column_bounds(xs, report_kind)
        column_specs = {
            "description": (*bounds["description"], "heb", "", "description"),
            "need": (*bounds["need"], "heb", "", "word"),
        }
        if report_kind.startswith("eyetech"):
            column_specs["problem_type"] = (
                *bounds["problem_type"], "heb", "", "description",
            )
        if report_kind == "eyetech_regular":
            pass
        else:
            column_specs["line"] = (*bounds["line"], "eng", "0123456789", "")
            column_specs["start"] = (*bounds["start"], "heb", "", "start")
            column_specs["page"] = (*bounds["page"], "eng", "0123456789", "")
        column_words: dict[str, list[OcrWord]] = {}
        problem_marker_words: list[OcrWord] = []
        if use_exact_text:
            for name, (left, right, _language, _whitelist, _scope) in column_specs.items():
                column_words[name] = words_in_cell(exact_words, left, right, top, bottom)
            # OCR just the script column for its pixel-aware word rectangles.
            # Spelling still comes from the exact PDF layer; these rectangles
            # are used only to detect the short underline below the bad letter.
            need_left, need_right = bounds["need"]
            need_left += 3
            need_right -= 2
            need_path = temp_dir / f"page-{pdf_page:03}-need-markers.bmp"
            Image.fromarray(cleaned[top:bottom, need_left:need_right]).save(need_path, "BMP")
            problem_marker_words = run_tesseract_tsv(
                self.tesseract, need_path, language="heb",
                offset_x=need_left, offset_y=top, training_scope="word",
            )
            # The precise PDF layer also supplies the row number.  It remains
            # separate from the larger 'צריך להיות' phrase because both share
            # the same broad visual cell in this report layout.
            column_words["line"] = exact_words
        else:
            for name, (left, right, language, whitelist, training_scope) in column_specs.items():
                left += 3
                right -= 2
                crop_path = temp_dir / f"page-{pdf_page:03}-{name}.bmp"
                Image.fromarray(cleaned[top:bottom, left:right]).save(crop_path, "BMP")
                tessdata_dir = None
                if language == "heb":
                    language, tessdata_dir = report_column_ocr_model(report_kind, name)
                column_words[name] = run_tesseract_tsv(
                    self.tesseract, crop_path, language=language, whitelist=whitelist,
                    offset_x=left, offset_y=top, training_scope=training_scope,
                    tessdata_dir=tessdata_dir,
                )

        if report_kind == "eyetech_regular" and not use_exact_text:
            line_left, line_right = bounds["line"]
            line_words: list[OcrWord] = []
            for row_number, (row_top, row_bottom) in enumerate(zip(ys, ys[1:])):
                if row_bottom - row_top < 20:
                    continue
                border = gray[
                    row_top + 4:max(row_top + 4, row_bottom - 4),
                    max(0, xs[0] - 2):min(gray.shape[1], xs[0] + 3),
                ]
                if border.size == 0 or float(np.mean(border < 190)) < 0.30:
                    continue
                crop_top = row_top + 3
                crop_bottom = row_bottom - 2
                crop_left = line_left + 2
                crop_right = line_right - 2
                if crop_bottom - crop_top < 8 or crop_right - crop_left < 8:
                    continue
                line_path = temp_dir / f"page-{pdf_page:03}-line-{row_number:03}.png"
                Image.fromarray(cleaned[crop_top:crop_bottom, crop_left:crop_right]).save(
                    line_path, "PNG",
                )
                line_words.extend(run_tesseract_tsv(
                    self.tesseract, line_path, language="eng", whitelist="0123456789",
                    psm=7, offset_x=crop_left, offset_y=crop_top,
                    apply_visual_training=False,
                ))
            column_words["line"] = line_words

        words = (
            column_words["description"]
            + column_words.get("problem_type", [])
            + column_words["need"]
        )
        rows = extract_rows_from_page(
            gray, words, pdf_page,
            line_ocr_words=column_words["line"],
            page_ocr_words=column_words.get("page", []),
            start_ocr_words=column_words.get("start", []),
            problem_marker_words=problem_marker_words,
            report_kind=report_kind,
        )
        if report_kind.startswith("eyetech") and rows:
            type_left, type_right = bounds["problem_type"]
            for row_index, row in enumerate(rows):
                if not problem_type_needs_refinement(row.problem_type):
                    continue
                cell_top = max(0, int(round(row.row_top * gray.shape[0])) + 3)
                cell_bottom = min(
                    gray.shape[0], int(round(row.row_bottom * gray.shape[0])) - 2,
                )
                cell_left = type_left + 3
                cell_right = type_right - 2
                if cell_bottom - cell_top < 8 or cell_right - cell_left < 8:
                    continue
                type_path = temp_dir / f"page-{pdf_page:03}-type-{row_index:03}.png"
                Image.fromarray(
                    cleaned[cell_top:cell_bottom, cell_left:cell_right],
                ).save(type_path, "PNG")
                precise_words = run_tesseract_tsv(
                    self.tesseract, type_path, language="heb", psm=6,
                    offset_x=cell_left, offset_y=cell_top,
                    training_scope="description",
                )
                precise_type = normalize_problem_type(join_rtl(precise_words))
                if precise_type:
                    row.problem_type = precise_type
        if report_kind == "eyetech_regular" and rows:
            current_page = ""
            current_start = ""
            previous_bottom = 0
            page_height, page_width = gray.shape
            for row_index, row in enumerate(rows):
                row_top = int(round(row.row_top * page_height))
                gap = row_top - previous_bottom
                if row_index == 0 or gap >= max(28, int(round(page_height * 0.012))):
                    # The first finding is close to the report's column-title
                    # band.  A compact heading crop keeps those labels out of
                    # the RTL reconstruction while still covering both lines
                    # of a decorative opening heading.
                    header_top = max(previous_bottom, row_top - int(round(page_height * 0.040)))
                    header_left = int(round(page_width * 0.18))
                    header_right = int(round(page_width * 0.96))
                    if row_top - header_top >= 25:
                        header_words = (
                            words_in_cell(
                                exact_words, header_left, header_right,
                                header_top, row_top,
                            )
                            if use_exact_text else []
                        )
                        if not header_words:
                            header_path = temp_dir / f"page-{pdf_page:03}-header-{row_index:03}.png"
                            Image.fromarray(cleaned[header_top:row_top, header_left:header_right]).save(
                                header_path, "PNG",
                            )
                            header_words = run_tesseract_tsv(
                                self.tesseract, header_path, language="heb", psm=7,
                                offset_x=header_left, offset_y=header_top,
                                apply_visual_training=False,
                            )
                        page_value, start_value = parse_regular_header(join_rtl(header_words))
                        if page_value:
                            current_page = page_value
                        if start_value:
                            current_start = start_value
                row.page = current_page
                row.start = current_start
                previous_bottom = int(round(row.row_bottom * page_height))
        return rows

    def read(self, pdf_path: Path, use_cache: bool = True) -> list[ReportRow]:
        if use_cache:
            cached_rows = load_ocr_cache(pdf_path)
            if cached_rows is not None:
                return cached_rows

        all_rows: list[ReportRow] = []
        previous_page = ""
        previous_start = ""
        temp_dir = Path(tempfile.mkdtemp(prefix="duk-reader-"))
        document: pdfium.PdfDocument | None = None
        try:
            document = pdfium.PdfDocument(str(pdf_path))
            page_count = len(document)
            first_page = document[0]
            try:
                first_image = first_page.render(scale=OCR_DPI / 72.0).to_pil().convert("L")
            finally:
                first_page.close()
            report_kind = detect_report_kind(np.asarray(first_image))
            worker_count = min(8, max(2, os.cpu_count() or 4), page_count)
            page_results: dict[int, list[ReportRow]] = {}
            with ThreadPoolExecutor(max_workers=worker_count, thread_name_prefix="duk-ocr") as executor:
                futures = {}
                for page_number in range(1, page_count + 1):
                    gray_path, clean_path, xs, ys, exact_words = self._prepare_pdf_page(
                        document, page_number, temp_dir, report_kind,
                    )
                    future = executor.submit(
                        self._ocr_prepared_page, page_number, gray_path, clean_path,
                        xs, ys, temp_dir, report_kind, exact_words,
                    )
                    futures[future] = page_number
                document.close()
                document = None
                completed = 0
                for future in as_completed(futures):
                    page_number = futures[future]
                    page_results[page_number] = future.result()
                    completed += 1
                    self.progress(
                        f"מזהה עמודים - הושלמו {completed} מתוך {page_count}",
                        completed, page_count,
                    )

            for page_number in range(1, page_count + 1):
                page_rows = page_results.get(page_number, [])
                for row in page_rows:
                    if row.page:
                        previous_page = row.page
                    else:
                        row.page = previous_page
                    if row.start:
                        previous_start = row.start
                    else:
                        row.start = previous_start
                    all_rows.append(row)
            if not all_rows:
                raise RuntimeError("לא נמצאו שורות בדוח. ודא שזהו דוח של תוכנת דיוקי סופרים.")
            for row in all_rows:
                ensure_ocr_baseline(row)
            apply_learned_rules_to_rows(all_rows)
            # Cache the contextual corrections immediately. The ocr_* fields
            # keep the raw recognition result for later user learning.
            write_ocr_cache(pdf_path, all_rows)
            return all_rows
        finally:
            if document is not None:
                document.close()
            shutil.rmtree(temp_dir, ignore_errors=True)


class SpeechWorker:
    def __init__(self, on_status: Callable[[str], None]):
        self.on_status = on_status
        self.commands: queue.Queue[tuple[list[str], int, str, float, int] | None] = queue.Queue()
        self.process: subprocess.Popen[str] | None = None
        self.state_lock = threading.Lock()
        self.generation = 0
        self.current_alias: str | None = None
        self.local_voice_lock = threading.RLock()
        self.cache_prepare_lock = threading.RLock()
        self.local_g2p = None
        self.local_voices: dict[str, object] = {}
        self.prefetch_commands: queue.Queue[tuple[list[str], int, str, str] | None] = queue.Queue()
        self.prefetch_lock = threading.Lock()
        self.prefetching: set[str] = set()
        self.prefetch_closed = False
        self.prefetch_threads = [
            threading.Thread(target=self._run_prefetch, daemon=True)
            for _index in range(2)
        ]
        for prefetch_thread in self.prefetch_threads:
            prefetch_thread.start()
        self.thread = threading.Thread(target=self._run, daemon=True)
        self.thread.start()

    def _start_process(self) -> None:
        if self.process and self.process.poll() is None:
            return
        script = resource_path("tts_worker.ps1")
        self.process = subprocess.Popen(
            ["powershell.exe", "-NoProfile", "-ExecutionPolicy", "Bypass", "-File", str(script)],
            stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            text=True, encoding="ascii", errors="replace", bufsize=1,
            creationflags=subprocess.CREATE_NO_WINDOW,
        )
        ready = self.process.stdout.readline().strip() if self.process.stdout else ""
        if not ready.startswith("READY|"):
            raise RuntimeError("הקול העברי של Windows אינו זמין.")

    def _play_media(
        self, path: Path, generation: int, media_type: str, playback_rate: int = 0,
    ) -> None:
        alias = f"dukreader{os.getpid()}{threading.get_ident()}"
        winmm = ctypes.windll.winmm

        def send(command: str) -> None:
            error = winmm.mciSendStringW(command, None, 0, None)
            if error:
                message = ctypes.create_unicode_buffer(256)
                winmm.mciGetErrorStringW(error, message, 256)
                raise RuntimeError(message.value or f"MCI error {error}")

        with self.state_lock:
            if generation != self.generation:
                return
        send(f'open "{path}" type {media_type} alias {alias}')
        if playback_rate:
            speed = max(500, min(1500, 1000 + int(playback_rate) * 10))
            try:
                send(f"set {alias} speed {speed}")
            except RuntimeError:
                # Some Windows media codecs do not expose speed control.  The
                # clip is still usable at its original recording speed.
                pass
        with self.state_lock:
            if generation != self.generation:
                winmm.mciSendStringW(f"close {alias}", None, 0, None)
                return
            self.current_alias = alias
        try:
            send(f"play {alias} wait")
        finally:
            winmm.mciSendStringW(f"close {alias}", None, 0, None)
            with self.state_lock:
                if self.current_alias == alias:
                    self.current_alias = None

    @staticmethod
    def _neural_cache_path(part: str, rate: int, voice: str) -> Path:
        cache_dir = app_data_dir() / "speech-cache"
        cache_dir.mkdir(parents=True, exist_ok=True)
        cache_key = hashlib.sha256(
            f"{voice}\0{rate}\0{part}".encode("utf-8")
        ).hexdigest()
        return cache_dir / f"{cache_key}.mp3"

    @staticmethod
    def _local_voice_cache_path(part: str, rate: int, voice: str) -> Path:
        cache_dir = app_data_dir() / "speech-cache"
        cache_dir.mkdir(parents=True, exist_ok=True)
        cache_key = hashlib.sha256(
            f"local-v1\0{voice}\0{rate}\0{part}".encode("utf-8")
        ).hexdigest()
        return cache_dir / f"{cache_key}.wav"

    @staticmethod
    def _recorded_avri_root() -> Path:
        root = app_data_dir() / "ספריית הקלטות אברי"
        root.mkdir(parents=True, exist_ok=True)
        return root

    @classmethod
    def _recorded_avri_cache_path(cls, part: str, _rate: int = 0, _voice: str = "") -> Path:
        cache_dir = cls._recorded_avri_root() / "קטעי קול לפי טקסט"
        cache_dir.mkdir(parents=True, exist_ok=True)
        digest = hashlib.sha256(part.encode("utf-8")).hexdigest()[:16]
        readable = unicodedata.normalize("NFC", part).strip()
        readable = re.sub(r'[<>:"/\\|?*\x00-\x1f]', " ", readable)
        readable = re.sub(r"\s+", " ", readable).strip(" .")[:54]
        if not readable:
            readable = "קטע"
        return cache_dir / f"{readable}--{digest}.mp3"

    @staticmethod
    def _valid_cached_clip(path: Path) -> bool:
        try:
            return path.is_file() and path.stat().st_size > 100
        except OSError:
            return False

    @staticmethod
    def _trim_neural_cache() -> None:
        cache_dir = app_data_dir() / "speech-cache"
        pinned: set[str] = set()
        packs_dir = app_data_dir() / "speech-packs"
        try:
            manifests = list(packs_dir.glob("*.json"))
        except OSError:
            manifests = []
        for manifest in manifests:
            try:
                value = json.loads(manifest.read_text(encoding="utf-8"))
                files = value.get("files", []) if isinstance(value, dict) else []
            except (OSError, ValueError, TypeError):
                continue
            if isinstance(files, list):
                pinned.update(str(name) for name in files if isinstance(name, str))
        try:
            clips = sorted(
                list(cache_dir.glob("*.mp3")) + list(cache_dir.glob("*.wav")),
                key=lambda path: path.stat().st_mtime,
                reverse=True,
            )
        except OSError:
            return
        unpinned = [path for path in clips if path.name not in pinned]
        for path in unpinned[NEURAL_SPEECH_CACHE_LIMIT:]:
            try:
                path.unlink(missing_ok=True)
            except OSError:
                pass

    def quality_cache_path(self, part: str, rate: int, voice: str) -> Path:
        if voice == RECORDED_AVRI_VOICE:
            return self._recorded_avri_cache_path(part)
        if voice.startswith("local-"):
            return self._local_voice_cache_path(part, rate, voice)
        return self._neural_cache_path(part, rate, voice)

    @staticmethod
    def estimated_clip_size(part: str, voice: str) -> int:
        meaningful_length = max(1, len(re.sub(r"\s+", "", part)))
        if voice.startswith("local-"):
            return max(18_000, meaningful_length * 4_600)
        if voice == RECORDED_AVRI_VOICE:
            return max(3_000, meaningful_length * 700)
        return max(3_000, meaningful_length * 700)

    def pin_report_clips(
        self, pdf_path: Path, parts: list[str], rate: int, voice: str,
    ) -> Path:
        try:
            stat = pdf_path.stat()
            identity = f"{pdf_path.resolve()}\0{stat.st_size}\0{stat.st_mtime_ns}\0{voice}\0{rate}"
        except OSError:
            identity = f"{pdf_path}\0{voice}\0{rate}"
        pack_id = hashlib.sha256(identity.encode("utf-8")).hexdigest()
        packs_dir = app_data_dir() / "speech-packs"
        packs_dir.mkdir(parents=True, exist_ok=True)
        manifest = packs_dir / f"{pack_id}.json"
        file_names = sorted({
            self.quality_cache_path(part, rate, voice).name
            for part in parts if part and part != RECORDED_AVRI_GAP_MARKER
        })
        value = {
            "version": 1,
            "pdf": str(pdf_path),
            "voice": voice,
            "rate": rate,
            "updated_at": datetime.now().isoformat(timespec="seconds"),
            "files": file_names,
        }
        temporary = manifest.with_suffix(".tmp")
        temporary.write_text(json.dumps(value, ensure_ascii=False, indent=2), encoding="utf-8")
        temporary.replace(manifest)
        return manifest

    def prepare_quality_clips(self, parts: list[str], rate: int, voice: str) -> list[Path]:
        if not parts or voice == "offline":
            return []
        with self.cache_prepare_lock:
            if voice == RECORDED_AVRI_VOICE:
                return asyncio.run(self._create_recorded_avri_clips(parts))
            if voice.startswith("local-"):
                return self._create_local_voice_clips(parts, rate, voice)
            return asyncio.run(self._create_neural_clips(parts, rate, voice))

    def prepare_export_clip(
        self, text: str, rate: int, voice: str, target: Path, force: bool = False,
    ) -> Path:
        """Create one complete, user-visible recording for a report row."""
        if not force and self._valid_cached_clip(target):
            return target
        target.parent.mkdir(parents=True, exist_ok=True)
        with self.cache_prepare_lock:
            if not force and self._valid_cached_clip(target):
                return target
            if voice.startswith("local-"):
                source = self._create_local_voice_clips([text], rate, voice)[0]
            else:
                neural_voice = (
                    RECORDED_AVRI_EDGE_VOICE
                    if voice == RECORDED_AVRI_VOICE else voice
                )
                source = asyncio.run(
                    self._create_neural_clips([text], rate, neural_voice)
                )[0]
            temporary = target.with_name(f".{target.name}.{uuid.uuid4().hex}.tmp")
            try:
                shutil.copy2(source, temporary)
                os.replace(temporary, target)
            finally:
                temporary.unlink(missing_ok=True)
        return target

    async def _create_recorded_avri_clips(self, parts: list[str]) -> list[Path]:
        """Create reusable Avri clips whose cache identity is text only."""
        truststore.inject_into_ssl()
        unique_parts = list(dict.fromkeys(
            part for part in parts if part and part != RECORDED_AVRI_GAP_MARKER
        ))
        paths = [self._recorded_avri_cache_path(part) for part in unique_parts]
        pending: list[tuple[Path, Path, object]] = []
        for part, path in zip(unique_parts, paths):
            if self._valid_cached_clip(path):
                continue
            descriptor, filename = tempfile.mkstemp(
                prefix="duk-avri-", suffix=".mp3", dir=str(path.parent),
            )
            os.close(descriptor)
            temporary_path = Path(filename)
            communicate = edge_tts.Communicate(
                part, RECORDED_AVRI_EDGE_VOICE, rate="+0%",
            )
            pending.append((temporary_path, path, communicate.save(str(temporary_path))))
        try:
            if pending:
                await asyncio.gather(*(task for _temporary, _target, task in pending))
                for temporary_path, target_path, _task in pending:
                    os.replace(temporary_path, target_path)
            return paths
        except Exception:
            for temporary_path, _target_path, _task in pending:
                temporary_path.unlink(missing_ok=True)
            raise

    async def _create_neural_clips(self, parts: list[str], rate: int, voice: str) -> list[Path]:
        truststore.inject_into_ssl()
        paths = [self._neural_cache_path(part, rate, voice) for part in parts]
        pending: list[tuple[Path, Path, object]] = []
        for part in parts:
            path = self._neural_cache_path(part, rate, voice)
            if self._valid_cached_clip(path):
                try:
                    os.utime(path, None)
                except OSError:
                    pass
                continue
            descriptor, filename = tempfile.mkstemp(
                prefix="duk-neural-", suffix=".mp3", dir=str(path.parent),
            )
            os.close(descriptor)
            temporary_path = Path(filename)
            communicate = edge_tts.Communicate(part, voice, rate=f"{rate:+d}%")
            pending.append((temporary_path, path, communicate.save(str(temporary_path))))
        try:
            if pending:
                await asyncio.gather(*(task for _temporary, _target, task in pending))
                for temporary_path, target_path, _task in pending:
                    os.replace(temporary_path, target_path)
                self._trim_neural_cache()
            return paths
        except Exception:
            for temporary_path, _target_path, _task in pending:
                temporary_path.unlink(missing_ok=True)
            raise

    def _load_local_voice(self, voice: str):
        voice_files = LOCAL_VOICE_MODELS.get(voice)
        if not voice_files:
            raise RuntimeError("הקול המקומי שנבחר אינו מוכר")
        model_name, config_name = voice_files
        with self.local_voice_lock:
            if self.local_g2p is None:
                from renikud_onnx import G2P
                self.local_g2p = G2P(str(resource_path("offline_voice_models/renikud.onnx")))
            if voice not in self.local_voices:
                from piper_onnx import Piper
                self.local_voices[voice] = Piper(
                    str(resource_path(model_name)),
                    str(resource_path(config_name)),
                )
            return self.local_g2p, self.local_voices[voice]

    def _create_local_voice_clips(self, parts: list[str], rate: int, voice: str) -> list[Path]:
        paths = [self._local_voice_cache_path(part, rate, voice) for part in parts]
        pending = [(part, path) for part, path in zip(parts, paths) if not self._valid_cached_clip(path)]
        if not pending:
            for path in paths:
                try:
                    os.utime(path, None)
                except OSError:
                    pass
            return paths
        g2p, piper = self._load_local_voice(voice)
        length_scale = max(0.52, min(2.0, 100.0 / max(50.0, 100.0 + float(rate))))
        with self.local_voice_lock:
            for part, target_path in pending:
                phonemes = g2p.phonemize(str(part))
                samples, sample_rate = piper.create(
                    phonemes, is_phonemes=True, length_scale=length_scale,
                )
                audio = np.asarray(samples, dtype=np.float32)
                if not audio.size:
                    raise RuntimeError("מנוע הקול המקומי לא החזיר שמע")
                peak = float(np.max(np.abs(audio)))
                if not np.isfinite(peak) or peak < 1e-6:
                    raise RuntimeError("מנוע הקול המקומי החזיר שמע שקט")
                # Piper voices differ substantially in output level.  Normalize
                # every local clip so SASpeech is as audible as the other voices.
                pcm = np.clip(audio / peak * 30100.0, -32768, 32767).astype("<i2")
                descriptor, filename = tempfile.mkstemp(
                    prefix="duk-local-", suffix=".wav", dir=str(target_path.parent),
                )
                os.close(descriptor)
                temporary_path = Path(filename)
                try:
                    with wave.open(str(temporary_path), "wb") as wav_file:
                        wav_file.setnchannels(1)
                        wav_file.setsampwidth(2)
                        wav_file.setframerate(int(sample_rate))
                        wav_file.writeframes(pcm.tobytes())
                    os.replace(temporary_path, target_path)
                finally:
                    temporary_path.unlink(missing_ok=True)
        self._trim_neural_cache()
        return paths

    def _prefetch_neural(self, parts: list[str], rate: int, voice: str, signature: str) -> None:
        try:
            if voice == RECORDED_AVRI_VOICE:
                with self.cache_prepare_lock:
                    asyncio.run(self._create_recorded_avri_clips(parts))
            elif voice.startswith("local-"):
                self._create_local_voice_clips(parts, rate, voice)
            else:
                asyncio.run(self._create_neural_clips(parts, rate, voice))
        except Exception:
            # Prefetch is an optimization only. Normal speech still has its
            # online-to-offline fallback and will report a useful error.
            pass
        finally:
            with self.prefetch_lock:
                self.prefetching.discard(signature)

    def _run_prefetch(self) -> None:
        while True:
            command = self.prefetch_commands.get()
            if command is None:
                break
            self._prefetch_neural(*command)

    def prefetch(self, parts: list[str], rate: int, voice: str) -> None:
        self.prefetch_many([(parts, rate, voice)])

    def prefetch_many(self, requests: list[tuple[list[str], int, str]]) -> None:
        prepared: list[tuple[list[str], int, str, str]] = []
        for parts, rate, voice in requests:
            if not parts or voice == "offline":
                continue
            signature = hashlib.sha256(
                (f"{voice}\0{rate}\0" + "\0".join(parts)).encode("utf-8")
            ).hexdigest()
            if voice == RECORDED_AVRI_VOICE:
                cache_path = self._recorded_avri_cache_path
            elif voice.startswith("local-"):
                cache_path = self._local_voice_cache_path
            else:
                cache_path = self._neural_cache_path
            cache_parts = [part for part in parts if part != RECORDED_AVRI_GAP_MARKER]
            if all(self._valid_cached_clip(cache_path(part, rate, voice)) for part in cache_parts):
                continue
            prepared.append((list(parts), rate, voice, signature))

        with self.prefetch_lock:
            if self.prefetch_closed:
                return
            # Keep only the current two-row look-ahead. Old queued rows are no
            # longer useful after the user jumps elsewhere in the report.
            while True:
                try:
                    stale = self.prefetch_commands.get_nowait()
                except queue.Empty:
                    break
                if stale is not None:
                    self.prefetching.discard(stale[3])
            for command in prepared:
                signature = command[3]
                if signature in self.prefetching:
                    continue
                self.prefetching.add(signature)
                self.prefetch_commands.put(command)

    def _speak_neural(
        self, parts: list[str], rate: int, voice: str, gap_seconds: float, generation: int,
    ) -> None:
        paths = asyncio.run(self._create_neural_clips(parts, rate, voice))
        for index, path in enumerate(paths):
            with self.state_lock:
                if generation != self.generation:
                    break
            self._play_media(path, generation, "mpegvideo")
            if index < len(paths) - 1:
                deadline = time.monotonic() + gap_seconds
                while time.monotonic() < deadline:
                    with self.state_lock:
                        if generation != self.generation:
                            break
                    time.sleep(0.05)

    def _speak_local_neural(
        self, parts: list[str], rate: int, voice: str, gap_seconds: float, generation: int,
    ) -> None:
        paths = self._create_local_voice_clips(parts, rate, voice)
        for index, path in enumerate(paths):
            with self.state_lock:
                if generation != self.generation:
                    break
            self._play_media(path, generation, "waveaudio")
            if index < len(paths) - 1:
                deadline = time.monotonic() + gap_seconds
                while time.monotonic() < deadline:
                    with self.state_lock:
                        if generation != self.generation:
                            break
                    time.sleep(0.05)

    def _speak_recorded_avri(
        self, parts: list[str], rate: int, gap_seconds: float, generation: int,
    ) -> None:
        """Play pre-recorded Avri pieces; synthesize only a missing piece."""
        for part in parts:
            with self.state_lock:
                if generation != self.generation:
                    return
            if part == RECORDED_AVRI_GAP_MARKER:
                deadline = time.monotonic() + gap_seconds
                while time.monotonic() < deadline:
                    with self.state_lock:
                        if generation != self.generation:
                            return
                    time.sleep(0.03)
                continue
            path = self._recorded_avri_cache_path(part)
            if not self._valid_cached_clip(path):
                try:
                    with self.cache_prepare_lock:
                        asyncio.run(self._create_recorded_avri_clips([part]))
                except Exception:
                    # A previously unseen problem word may be requested while
                    # fully offline.  Only that word falls back to the local
                    # Michael model; the saved Avri pieces remain unchanged.
                    fallback = self._create_local_voice_clips([part], rate, "local-michael")[0]
                    self._play_media(fallback, generation, "waveaudio")
                    continue
            self._play_media(path, generation, "mpegvideo", playback_rate=rate)

    def _speak_offline(
        self, parts: list[str], rate: int, gap_seconds: float, generation: int,
    ) -> None:
        with self.state_lock:
            if generation != self.generation:
                return
        self._start_process()
        if not self.process or not self.process.stdin or not self.process.stdout:
            raise RuntimeError("הקול המקומי אינו זמין")
        gap_milliseconds = int(round(gap_seconds * 1000))
        body = f'<break time="{gap_milliseconds}ms"/>'.join(html.escape(part) for part in parts)
        ssml = (
            '<speak version="1.0" xmlns="http://www.w3.org/2001/10/synthesis" xml:lang="he-IL">'
            f'<prosody rate="{rate:+d}%">{body}</prosody></speak>'
        )
        encoded = base64.b64encode(ssml.encode("utf-8")).decode("ascii")
        self.process.stdin.write("SPEAK|" + encoded + "\n")
        self.process.stdin.flush()
        response = self.process.stdout.readline().strip()
        if response.startswith("ERROR|"):
            raise RuntimeError("שגיאה בקול המקומי")

    def _run(self) -> None:
        while True:
            command = self.commands.get()
            if command is None:
                break
            parts, rate, voice, gap_seconds, generation = command
            with self.state_lock:
                if generation != self.generation:
                    continue
            try:
                if voice == "offline":
                    self._speak_offline(parts, rate, gap_seconds, generation)
                    with self.state_lock:
                        current = generation == self.generation
                    if current:
                        self.on_status("מוכן - קול מקומי")
                elif voice == "export-file":
                    export_path = Path(parts[0]) if parts else Path()
                    media_type = "waveaudio" if export_path.suffix.lower() == ".wav" else "mpegvideo"
                    self._play_media(export_path, generation, media_type)
                    with self.state_lock:
                        current = generation == self.generation
                    if current:
                        self.on_status("מוכן - הקלטה מקומית מתיקיית הדוח")
                elif voice == RECORDED_AVRI_VOICE:
                    self._speak_recorded_avri(parts, rate, gap_seconds, generation)
                    with self.state_lock:
                        current = generation == self.generation
                    if current:
                        self.on_status("מוכן - אברי מוקלט אופליין")
                elif voice.startswith("local-"):
                    try:
                        self._speak_local_neural(parts, rate, voice, gap_seconds, generation)
                        with self.state_lock:
                            current = generation == self.generation
                        if current:
                            self.on_status("מוכן - קול איכותי אופליין")
                    except Exception as exc:
                        try:
                            (app_data_dir() / "voice-error.log").write_text(
                                traceback.format_exc(), encoding="utf-8",
                            )
                        except OSError:
                            pass
                        with self.state_lock:
                            current = generation == self.generation
                        if current:
                            self.on_status(
                                f"הקול האיכותי המקומי נכשל ({exc}) - עובר לאסף"
                            )
                            self._speak_offline(parts, rate, gap_seconds, generation)
                            self.on_status("מוכן - קול מקומי")
                else:
                    try:
                        self._speak_neural(parts, rate, voice, gap_seconds, generation)
                        with self.state_lock:
                            current = generation == self.generation
                        if current:
                            self.on_status("מוכן - קול איכותי")
                    except Exception:
                        with self.state_lock:
                            current = generation == self.generation
                        if current:
                            self.on_status("הקול המקוון לא זמין - עובר לקול המקומי")
                            self._speak_offline(parts, rate, gap_seconds, generation)
                            self.on_status("מוכן - קול מקומי")
            except Exception as exc:
                with self.state_lock:
                    current = generation == self.generation
                if current:
                    self.on_status(f"שגיאת קול: {exc}")

    def cancel(self) -> None:
        with self.state_lock:
            self.generation += 1
            alias = self.current_alias
            process = self.process
            self.process = None
        while True:
            try:
                self.commands.get_nowait()
            except queue.Empty:
                break
        if alias:
            ctypes.windll.winmm.mciSendStringW(f"stop {alias}", None, 0, None)
        if process and process.poll() is None:
            try:
                process.terminate()
            except OSError:
                pass

    def speak(self, parts: list[str], rate: int, voice: str, gap_seconds: float = 1.0) -> None:
        self.cancel()
        gap_seconds = max(0.0, min(5.0, float(gap_seconds)))
        with self.state_lock:
            generation = self.generation
        self.commands.put((parts, rate, voice, gap_seconds, generation))

    def speak_export(self, path: Path) -> None:
        self.cancel()
        with self.state_lock:
            generation = self.generation
        self.commands.put(([str(path)], 0, "export-file", 0.0, generation))

    def close(self) -> None:
        self.cancel()
        self.commands.put(None)
        with self.prefetch_lock:
            self.prefetch_closed = True
            while True:
                try:
                    stale = self.prefetch_commands.get_nowait()
                except queue.Empty:
                    break
                if stale is not None:
                    self.prefetching.discard(stale[3])
            for _thread in self.prefetch_threads:
                self.prefetch_commands.put(None)


class ReportReaderApp:
    def __init__(self, root: tk.Tk):
        self.root = root
        self.root.title(f"{APP_NAME} {APP_VERSION}")
        try:
            self.root.iconbitmap(default=str(resource_path("app.ico")))
        except Exception:
            pass
        # The timer controls deliberately stay on one line.  Keep the desktop
        # window wide enough that resizing cannot hide part of that row.
        fit_window_to_work_area(self.root, 1480, 920, 1360, 620)
        self.rows: list[ReportRow] = []
        self.current_index = -1
        self.pdf_path: Path | None = None
        self.reading_started_monotonic: float | None = None
        self.reading_visited_indices: set[int] = set()
        self.reading_summary: dict | None = None
        self.reading_pdf_path = ""
        saved_settings = self._load_settings()
        try:
            saved_speed = max(-50, min(50, int(round(float(saved_settings.get("speech_speed", 0))))))
        except (TypeError, ValueError):
            saved_speed = 0
        saved_voice = str(saved_settings.get("voice_choice", "מיכאל - איכותי אופליין"))
        saved_voice = {
            "הילה - איכותי": "הילה - איכותי אונליין",
            "אברי - איכותי": "אברי - איכותי אונליין",
            "אסף - לא מקוון": "אסף - אופליין בסיסי",
        }.get(saved_voice, saved_voice)
        if saved_voice not in VOICE_CHOICES:
            saved_voice = "מיכאל - איכותי אופליין"
        try:
            self.default_zoom_factor = max(
                0.60, min(4.0, float(saved_settings.get("default_zoom_factor", 1.0)))
            )
        except (TypeError, ValueError):
            self.default_zoom_factor = 1.0
        self.speed = tk.IntVar(value=saved_speed)
        self.speed_text = tk.StringVar(value=self._speed_label(saved_speed))
        self.voice_choice = tk.StringVar(value=saved_voice)
        try:
            saved_gap = max(0.0, min(5.0, float(saved_settings.get("speech_gap_seconds", 1.0))))
        except (TypeError, ValueError):
            saved_gap = 1.0
        self.speech_gap = tk.StringVar(value=f"{saved_gap:g}")
        self.hourly_rate = tk.StringVar(value=str(saved_settings.get("hourly_rate", "")))
        self.timer_client = tk.StringVar(value=str(saved_settings.get("timer_client", "")))
        saved_payment_mode = str(saved_settings.get("payment_mode", PAYMENT_MODE_HOURLY))
        if saved_payment_mode not in PAYMENT_MODE_LABELS:
            saved_payment_mode = PAYMENT_MODE_HOURLY
        self.payment_mode = tk.StringVar(value=PAYMENT_MODE_LABELS[saved_payment_mode])
        self.issue_filter = tk.StringVar(value="הכול")
        self.issue_sort = tk.StringVar(value="סדר הדוח")
        raw_issue_rates = saved_settings.get(
            "default_issue_rates", saved_settings.get("issue_rates", {}),
        )
        self.issue_rates: dict[str, float] = {}
        if isinstance(raw_issue_rates, dict):
            for issue, value in raw_issue_rates.items():
                clean_issue = clean_hebrew_text(str(issue))
                try:
                    clean_rate = max(0.0, float(value))
                except (TypeError, ValueError):
                    continue
                if clean_issue:
                    self.issue_rates[clean_issue] = clean_rate
        self.default_issue_rates = dict(self.issue_rates)
        self.client_issue_rates: dict[str, dict[str, float]] = {}
        raw_client_issue_rates = saved_settings.get("client_issue_rates", {})
        if isinstance(raw_client_issue_rates, dict):
            for client_key, values in raw_client_issue_rates.items():
                if not isinstance(values, dict):
                    continue
                cleaned: dict[str, float] = {}
                for issue, value in values.items():
                    clean_issue = clean_hebrew_text(str(issue)).strip()
                    try:
                        clean_rate = max(0.0, float(value))
                    except (TypeError, ValueError):
                        continue
                    if clean_issue and clean_rate > 0:
                        cleaned[clean_issue] = clean_rate
                if cleaned:
                    self.client_issue_rates[str(client_key).casefold()] = cleaned
        self.client_alert_rates: dict[str, dict[str, dict[str, float]]] = {}
        raw_client_alert_rates = saved_settings.get("client_alert_rates", {})
        if isinstance(raw_client_alert_rates, dict):
            for client_key, reports in raw_client_alert_rates.items():
                if not isinstance(reports, dict):
                    continue
                clean_reports: dict[str, dict[str, float]] = {}
                for report_key, values in reports.items():
                    if not isinstance(values, dict):
                        continue
                    clean_values: dict[str, float] = {}
                    for alert_key, value in values.items():
                        try:
                            clean_rate = max(0.0, float(value))
                        except (TypeError, ValueError):
                            continue
                        if clean_rate > 0:
                            clean_values[str(alert_key)] = clean_rate
                    if clean_values:
                        clean_reports[str(report_key)] = clean_values
                if clean_reports:
                    self.client_alert_rates[str(client_key).casefold()] = clean_reports
        self.finance_link_text = tk.StringVar(value=(
            "לקוחות ודוחות שעות נשמרים במחשב"
            if CUSTOMER_EDITION else "בודק חיבור לתוכנת הכספים..."
        ))
        self.finance_clients: list[dict] = []
        self.finance_client_rates: dict[str, float] = {}
        raw_local_clients = saved_settings.get("local_clients", [])
        self.local_clients: list[dict] = []
        if isinstance(raw_local_clients, list):
            seen_local_clients: set[str] = set()
            for item in raw_local_clients:
                if isinstance(item, str):
                    item = {"name": item, "hourly_rate": 0}
                if not isinstance(item, dict):
                    continue
                name = str(item.get("name", "")).strip()
                key = name.casefold()
                if not name or key in seen_local_clients:
                    continue
                try:
                    local_rate = max(0.0, float(item.get("hourly_rate", 0) or 0))
                except (TypeError, ValueError):
                    local_rate = 0.0
                seen_local_clients.add(key)
                self.local_clients.append({"name": name, "hourly_rate": local_rate})
        raw_work_history = saved_settings.get("work_history", [])
        self.work_history: list[dict] = (
            [item for item in raw_work_history if isinstance(item, dict)][-500:]
            if isinstance(raw_work_history, list) else []
        )
        self.finance_username = ""
        self.finance_clients_mtime_ns: int | None = None
        self.finance_poll_job: str | None = None
        self.timer_elapsed_text = tk.StringVar(value="00:00:00")
        self.timer_summary_text = tk.StringVar(value="טרם נמדד זמן עבודה")
        self.timer_start: datetime | None = None
        self.timer_run_started: datetime | None = None
        self.timer_accumulated_seconds = 0.0
        self.timer_rate_value = 0.0
        self.timer_client_value = ""
        self.timer_payment_mode_value = PAYMENT_MODE_HOURLY
        self.timer_issue_counts_value: dict[str, int] = {}
        self.timer_issue_rates_value: dict[str, float] = {}
        self.timer_alert_items_value: list[dict[str, object]] = []
        self.timer_session_id: str | None = None
        self.timer_pdf_path = ""
        self.timer_finance_username = ""
        self.timer_after_job: str | None = None
        saved_summary = saved_settings.get("last_timer_summary")
        self.last_timer_summary: dict | None = saved_summary if isinstance(saved_summary, dict) else None
        saved_recent = saved_settings.get("recent_files", [])
        self.recent_files: list[str] = []
        if isinstance(saved_recent, list):
            for item in saved_recent:
                if isinstance(item, str) and item and item not in self.recent_files:
                    self.recent_files.append(item)
        known_recent = {os.path.normcase(item) for item in self.recent_files}
        for cache in sorted(
            app_data_dir().glob("ocr-file-*.json"), key=lambda item: item.stat().st_mtime, reverse=True,
        ):
            try:
                payload = json.loads(cache.read_text(encoding="utf-8"))
                source_path = str(payload.get("meta", {}).get("source_path", ""))
            except (OSError, ValueError, TypeError):
                continue
            if source_path and os.path.normcase(source_path) not in known_recent:
                self.recent_files.append(source_path)
                known_recent.add(os.path.normcase(source_path))
        self.key_bindings: dict[str, str] = saved_settings.get(
            "keys", {"next": "Return", "previous": "minus", "repeat": "plus"}
        )
        defaults = {"next": "Return", "previous": "minus", "repeat": "plus"}
        for action, default in defaults.items():
            if not isinstance(self.key_bindings.get(action), str):
                self.key_bindings[action] = default
        saved_column_widths = saved_settings.get("result_column_widths", {})
        self.result_column_widths: dict[str, int] = {}
        if isinstance(saved_column_widths, dict):
            for name, value in saved_column_widths.items():
                try:
                    self.result_column_widths[str(name)] = max(42, min(700, int(value)))
                except (TypeError, ValueError):
                    pass
        self.shortcut_vars = {
            action: tk.StringVar(value=self._display_key(key))
            for action, key in self.key_bindings.items()
        }
        self.footer_text = tk.StringVar()
        self.update_status_text = tk.StringVar(value=f"גרסה {APP_VERSION}")
        self.update_in_progress = False
        self.update_retry_job: str | None = None
        self.customer_auth = load_customer_auth() if CUSTOMER_EDITION else {}
        self.auth_heartbeat_job: str | None = None
        self.auth_heartbeat_running = False
        self.ocr_rule_sync_job: str | None = None
        self.ocr_rule_sync_running = False
        self._update_shortcut_text()
        self.status = tk.StringVar(value="בחר קובץ PDF כדי להתחיל")
        self.progress_value = tk.DoubleVar(value=0)
        self.preview_photo: ImageTk.PhotoImage | None = None
        self.preview_base_image: Image.Image | None = None
        self.preview_cache: dict[int, Image.Image] = {}
        self.zoom_factor = 1.0
        self.zoom_text = tk.StringVar(value="100%")
        self.preview_focus_y = 0.5
        self.preview_resize_job: str | None = None
        self.preview_page_number = 0
        self.preview_image_bounds: tuple[float, float, float, float] | None = None
        self.preview_pan_origin: tuple[int, int] | None = None
        self.preview_was_dragged = False
        self.key_settings_open = False
        self.cache_manager_open = False
        self.learning_manager_open = False
        self.image_training_open = False
        self.default_settings_open = False
        self.offline_ai_dialog: tk.Toplevel | None = None
        self.offline_ai_cancel = threading.Event()
        self.offline_ai_thread: threading.Thread | None = None
        self.offline_ai_review_generation = 0
        self.ai_enabled = bool(saved_settings.get("offline_ai_enabled", False))
        self.ai_auto_review = bool(saved_settings.get("offline_ai_auto_review", True))
        self.ai_vision_fallback = bool(saved_settings.get("offline_ai_vision_fallback", True))
        try:
            self.ai_confidence_threshold = max(
                35.0, min(95.0, float(saved_settings.get("offline_ai_threshold", 72.0)))
            )
        except (TypeError, ValueError):
            self.ai_confidence_threshold = 72.0
        self.offline_ai: OfflineAiManager | None = (
            OfflineAiManager(app_data_dir() / "offline-ai")
            if not CUSTOMER_EDITION and not GIGAPDF_OCR_EDITION else None
        )
        self.bulk_download_dialog: tk.Toplevel | None = None
        self.bulk_download_thread: threading.Thread | None = None
        self.bulk_download_cancel = threading.Event()
        self.bulk_download_state: dict[str, object] = {}
        self.avri_library_thread: threading.Thread | None = None
        self.avri_library_cancel = threading.Event()
        self.avri_library_generation = 0
        self.avri_library_enabled = bool(saved_settings.get("avri_library_enabled", False))
        self.ocr_generation = 0
        restore_state = saved_settings.get("last_report_state")
        self.startup_restore_state: dict | None = restore_state if isinstance(restore_state, dict) else None
        self.pending_report_restore: dict | None = None
        self.bound_action_sequences: list[str] = []
        self._drop_hwnd = 0
        self._drop_old_wndproc = 0
        self._drop_wndproc_callback = None
        self.editor_vars = {
            name: tk.StringVar() for name in (
                "page", "start", "line", "first_word", "problem_word",
                "problem_type", "description",
            )
        }
        self.speech = SpeechWorker(lambda value: self.root.after(0, self.status.set, value))
        self._build_ui()
        self.root.bind("<Configure>", self._window_resized, add="+")
        self._enable_pdf_drop()
        if CUSTOMER_EDITION:
            self._refresh_local_clients()
        else:
            self._refresh_finance_clients(force=True)
        self._load_client_pricing(self.timer_client.get().strip())
        self._restore_timer(saved_settings)
        if not CUSTOMER_EDITION:
            self._schedule_finance_client_refresh()
        self._show_home_screen()
        self._bind_keys()
        self.root.protocol("WM_DELETE_WINDOW", self.close)
        if not GIGAPDF_OCR_EDITION:
            self._schedule_update_check(2200)
        if CUSTOMER_EDITION:
            self.auth_heartbeat_job = self.root.after(60_000, self._customer_auth_heartbeat)
        if not GIGAPDF_OCR_EDITION:
            self._schedule_ocr_rule_sync(3500)

    @staticmethod
    def _settings_path() -> Path:
        return app_data_dir() / "settings.json"

    def _load_settings(self) -> dict:
        try:
            return json.loads(self._settings_path().read_text(encoding="utf-8"))
        except (OSError, ValueError, TypeError):
            return {}

    def _save_settings(self) -> None:
        settings = self._load_settings()
        settings["keys"] = self.key_bindings
        settings["recent_files"] = self.recent_files
        settings["hourly_rate"] = self.hourly_rate.get().strip()
        settings["timer_client"] = self.timer_client.get().strip()
        settings["payment_mode"] = self.selected_payment_mode()
        settings["issue_rates"] = self.default_issue_rates
        settings["default_issue_rates"] = self.default_issue_rates
        settings["client_issue_rates"] = self.client_issue_rates
        settings["client_alert_rates"] = self.client_alert_rates
        settings["speech_gap_seconds"] = self.speech_gap_seconds()
        settings["speech_speed"] = int(round(self.speed.get()))
        settings["voice_choice"] = self.voice_choice.get()
        settings["default_zoom_factor"] = self.default_zoom_factor
        settings["last_timer_summary"] = self.last_timer_summary
        settings["result_column_widths"] = self.result_column_widths
        settings["avri_library_enabled"] = self.avri_library_enabled
        if not CUSTOMER_EDITION and not GIGAPDF_OCR_EDITION:
            settings["offline_ai_enabled"] = self.ai_enabled
            settings["offline_ai_auto_review"] = self.ai_auto_review
            settings["offline_ai_vision_fallback"] = self.ai_vision_fallback
            settings["offline_ai_threshold"] = self.ai_confidence_threshold
        if CUSTOMER_EDITION:
            settings["local_clients"] = self.local_clients
            settings["work_history"] = self.work_history[-500:]
        if self.pdf_path is not None and self.current_index < 0 and self.pending_report_restore:
            # Opening a saved report briefly has no selected row while OCR/cache
            # loading is in progress. Preserve the previous good state instead
            # of replacing it with the temporary index -1.
            pass
        elif self.pdf_path is not None:
            row_identity: dict[str, object] = {}
            if 0 <= self.current_index < len(self.rows):
                row = self.rows[self.current_index]
                row_identity = {
                    "page": row.page,
                    "start": row.start,
                    "line": row.line,
                    "first_word": row.first_word,
                    "source_pdf_page": row.source_pdf_page,
                }
            try:
                preview_x = float(self.preview_canvas.xview()[0])
                preview_y = float(self.preview_canvas.yview()[0])
            except (AttributeError, IndexError, tk.TclError, TypeError, ValueError):
                preview_x = 0.0
                preview_y = 0.0
            settings["last_report_state"] = {
                "pdf_path": str(self.pdf_path.resolve()),
                "current_index": self.current_index,
                "row": row_identity,
                "zoom_factor": self.zoom_factor,
                "preview_x": preview_x,
                "preview_y": preview_y,
            }
        else:
            settings.pop("last_report_state", None)
        if self.timer_start is not None:
            settings["active_timer"] = {
                "start": self.timer_start.isoformat(),
                "run_started": self.timer_run_started.isoformat() if self.timer_run_started else None,
                "accumulated_seconds": self.timer_accumulated_seconds,
                "rate": self.timer_rate_value,
                "payment_mode": self.timer_payment_mode_value,
                "issue_counts": self.timer_issue_counts_value,
                "issue_rates": self.timer_issue_rates_value,
                "alert_items": self.timer_alert_items_value,
                "client": self.timer_client_value or self.timer_client.get().strip(),
                "session_id": self.timer_session_id,
                "pdf_path": self.timer_pdf_path,
                "finance_username": self.timer_finance_username,
            }
        else:
            settings.pop("active_timer", None)
        settings_path = self._settings_path()
        temporary = settings_path.with_suffix(".tmp")
        temporary.write_text(json.dumps(settings, ensure_ascii=False, indent=2), encoding="utf-8")
        temporary.replace(settings_path)

    def _refresh_finance_clients(self, force: bool = False) -> None:
        snapshot_path = finance_bridge_dir() / FINANCE_CLIENTS_FILE
        try:
            mtime_ns = snapshot_path.stat().st_mtime_ns
        except OSError:
            mtime_ns = None
        if not force and mtime_ns == self.finance_clients_mtime_ns:
            return
        self.finance_clients_mtime_ns = mtime_ns
        context = load_finance_context()
        self.finance_username = str(context.get("username", "")).strip()
        self.finance_clients = list(context.get("clients", []))
        self.finance_client_rates = {
            item["name"].casefold(): float(item.get("repairRate", 0) or 0)
            for item in self.finance_clients
        }
        names = tuple(item["name"] for item in self.finance_clients)
        if hasattr(self, "timer_client_combo"):
            self.timer_client_combo.configure(values=names)
        if self.finance_username:
            self.finance_link_text.set(
                f"מחובר לכספים: {self.finance_username} · {len(names)} לקוחות"
            )
        else:
            self.finance_link_text.set("כדי לקשר הכנסה, פתח פעם אחת את תוכנת הכספים המעודכנת")

    def _refresh_local_clients(self) -> None:
        self.local_clients.sort(key=lambda item: str(item.get("name", "")).casefold())
        self.finance_clients = [
            {"name": str(item.get("name", "")).strip(), "repairRate": item.get("hourly_rate", 0)}
            for item in self.local_clients if str(item.get("name", "")).strip()
        ]
        self.finance_client_rates = {
            item["name"].casefold(): float(item.get("repairRate", 0) or 0)
            for item in self.finance_clients
        }
        names = tuple(item["name"] for item in self.finance_clients)
        if hasattr(self, "timer_client_combo"):
            self.timer_client_combo.configure(values=names)
        self.finance_link_text.set(
            f"שמירה מקומית בלבד · {len(names)} לקוחות שמורים"
        )

    def _remember_local_client(self, name: str, rate: float | None = None) -> None:
        if not CUSTOMER_EDITION:
            return
        clean_name = name.strip()
        if not clean_name:
            return
        for item in self.local_clients:
            if str(item.get("name", "")).casefold() == clean_name.casefold():
                item["name"] = clean_name
                if rate is not None and rate > 0:
                    item["hourly_rate"] = rate
                self._refresh_local_clients()
                return
        self.local_clients.append({
            "name": clean_name,
            "hourly_rate": rate if rate is not None and rate > 0 else 0,
        })
        self._refresh_local_clients()

    def _schedule_finance_client_refresh(self) -> None:
        if self.finance_poll_job:
            try:
                self.root.after_cancel(self.finance_poll_job)
            except tk.TclError:
                pass
        self.finance_poll_job = self.root.after(3000, self._finance_client_refresh_tick)

    def _finance_client_refresh_tick(self) -> None:
        self.finance_poll_job = None
        self._refresh_finance_clients()
        self._schedule_finance_client_refresh()

    def _timer_client_changed(self, _event=None) -> None:
        if self.timer_start is not None:
            return
        client = self.timer_client.get().strip()
        if CUSTOMER_EDITION and client:
            self._remember_local_client(client)
        loaded_issue_prices = self._load_client_pricing(client)
        rate = self.finance_client_rates.get(client.casefold())
        if rate is not None and rate > 0:
            self.hourly_rate.set(f"{rate:g}")
            self.status.set(f"נטען מחיר התיקונים של {client}: ₪{rate:g} לשעה")
        elif loaded_issue_prices:
            self.status.set(
                f"נטענו המחירים האחרונים של {client}: {loaded_issue_prices} סוגי בעיה"
            )
        if hasattr(self, "tree") and self.rows:
            self._refresh_result_rows()
        self._save_settings()

    def _record_recent_file(self, pdf_path: Path) -> None:
        resolved = str(pdf_path.resolve())
        lowered = os.path.normcase(resolved)
        self.recent_files = [
            item for item in self.recent_files
            if os.path.normcase(str(Path(item))) != lowered
        ]
        self.recent_files.insert(0, resolved)
        self._save_settings()
        self._refresh_recent_files()

    def _refresh_recent_files(self) -> None:
        if not hasattr(self, "recent_tree"):
            return
        self.recent_tree.delete(*self.recent_tree.get_children())
        for index, item in enumerate(self.recent_files):
            path = Path(item)
            name = path.name if path.exists() else f"{path.name} (הקובץ לא נמצא)"
            self.recent_tree.insert("", "end", iid=str(index), values=(name, str(path.parent)))
        count = len(self.recent_files)
        if count:
            self.recent_summary.set(f"{count} קבצים שנפתחו לאחרונה - לחץ פעמיים כדי לפתוח")
        else:
            self.recent_summary.set("עדיין לא נפתחו דוחות בתוכנה")

    @staticmethod
    def _format_duration(total_seconds: float) -> str:
        seconds = max(0, int(round(total_seconds)))
        hours, remainder = divmod(seconds, 3600)
        minutes, seconds = divmod(remainder, 60)
        return f"{hours:02}:{minutes:02}:{seconds:02}"

    def selected_payment_mode(self) -> str:
        selected = self.payment_mode.get().strip()
        for mode, label in PAYMENT_MODE_LABELS.items():
            if selected == label:
                return mode
        return PAYMENT_MODE_HOURLY

    @staticmethod
    def _billing_issue_for_row(row: ReportRow) -> str:
        raw_issue = (
            row.problem_type if row.report_kind.startswith("eyetech") else row.description
        )
        return normalize_problem_type(raw_issue).strip()

    @staticmethod
    def _pricing_client_key(client: str) -> str:
        return client.strip().casefold() or "__default__"

    def _report_pricing_key(self) -> str:
        if self.pdf_path is None:
            return ""
        try:
            source = _resolved_pdf_path(self.pdf_path)
        except OSError:
            source = os.path.normcase(str(self.pdf_path))
        return hashlib.sha256(source.encode("utf-8")).hexdigest()[:24]

    @staticmethod
    def _alert_pricing_key(row: ReportRow) -> str:
        identity = "\u001f".join((
            str(row.source_pdf_page), row.page.strip(), row.line.strip(),
            row.start.strip(), row.first_word.strip(), row.problem_word.strip(),
            row.problem_type.strip(), row.description.strip(), f"{row.row_top:.6f}",
        ))
        return hashlib.sha256(identity.encode("utf-8")).hexdigest()[:24]

    @staticmethod
    def _alert_message_for_row(row: ReportRow) -> str:
        if row.report_kind.startswith("eyetech"):
            return clean_hebrew_text(row.description or row.problem_type).strip()
        return clean_hebrew_text(row.description).strip()

    def _found_cell_crop(
        self, row: ReportRow, page_cache: dict[int, Image.Image],
    ) -> Image.Image | None:
        """Return the original image from the report's 'נמצא' cell."""
        if self.pdf_path is None or row.source_pdf_page <= 0:
            return None
        kind = row.report_kind if row.report_kind in TABLE_PROFILES else "classic"
        if kind == "classic_no_found":
            return None
        ratios = TABLE_PROFILES[kind]
        if kind == "classic":
            left_ratio, right_ratio = ratios[1], ratios[2]
        else:
            left_ratio, right_ratio = ratios[2], ratios[3]
        page_number = row.source_pdf_page
        page_image = page_cache.get(page_number)
        if page_image is None:
            document = pdfium.PdfDocument(str(self.pdf_path))
            try:
                page = document[page_number - 1]
                bitmap = page.render(scale=220 / 72.0)
                page_image = bitmap.to_pil().convert("RGB")
                page.close()
            finally:
                document.close()
            page_cache[page_number] = page_image
        pad_x = max(2, int(round(page_image.width * 0.003)))
        pad_y = max(2, int(round(page_image.height * 0.002)))
        left = max(0, int(round(left_ratio * page_image.width)) + pad_x)
        right = min(page_image.width, int(round(right_ratio * page_image.width)) - pad_x)
        top = max(0, int(round(row.row_top * page_image.height)) + pad_y)
        bottom = min(page_image.height, int(round(row.row_bottom * page_image.height)) - pad_y)
        if right <= left or bottom <= top:
            return None
        return page_image.crop((left, top, right, bottom))

    def _load_client_pricing(self, client: str) -> int:
        profile = self.client_issue_rates.get(self._pricing_client_key(client))
        self.issue_rates = dict(profile if profile is not None else self.default_issue_rates)
        return len(profile or {})

    def _current_alert_overrides(self, client: str | None = None) -> dict[str, float]:
        client_name = self.timer_client.get().strip() if client is None else client
        report_key = self._report_pricing_key()
        if not report_key:
            return {}
        return dict(
            self.client_alert_rates
            .get(self._pricing_client_key(client_name), {})
            .get(report_key, {})
        )

    def _current_alert_items(
        self,
        rates: dict[str, float] | None = None,
        overrides: dict[str, float] | None = None,
    ) -> list[dict[str, object]]:
        active_rates = self.issue_rates if rates is None else rates
        active_overrides = self._current_alert_overrides() if overrides is None else overrides
        items: list[dict[str, object]] = []
        for index, row in enumerate(self.rows):
            issue = self._billing_issue_for_row(row)
            if not issue:
                continue
            key = self._alert_pricing_key(row)
            rate = float(active_overrides.get(key, active_rates.get(issue, 0)) or 0)
            items.append({
                "key": key,
                "row_index": index,
                "issue": issue,
                "page": row.page,
                "line": row.line,
                "start": display_report_text(row, row.start),
                "word": display_report_text(row, row.problem_word),
                "message": self._alert_message_for_row(row),
                "rate": max(0.0, rate),
                "custom_rate": key in active_overrides,
            })
        return items

    def _current_issue_counts(self) -> dict[str, int]:
        counts: dict[str, int] = {}
        for row in self.rows:
            issue = self._billing_issue_for_row(row)
            if issue:
                counts[issue] = counts.get(issue, 0) + 1
        return counts

    @staticmethod
    def _format_issue_breakdown(breakdown: list[dict[str, object]]) -> str:
        return "  |  ".join(
            (
                f"{item['issue']}: {int(item['count'])} התראות, ₪{float(item['amount']):,.2f}"
                if item.get("rate") is None
                else f"{item['issue']}: {int(item['count'])} × ₪{float(item['rate']):g}"
            )
            for item in breakdown
        )

    def _payment_mode_changed(self, _event=None) -> None:
        mode = self.selected_payment_mode()
        self._set_timer_controls()
        self._save_settings()
        if mode == PAYMENT_MODE_ISSUE:
            count = sum(self._current_issue_counts().values())
            self.status.set(
                f"התשלום יחושב לפי סוגי הבעיה בדוח ({count} תיקונים מזוהים)"
            )
        else:
            self.status.set("התשלום יחושב לפי זמן העבודה והמחיר לשעה")

    def open_issue_pricing(self) -> None:
        if self.timer_start is not None:
            messagebox.showinfo(APP_NAME, "אי אפשר לשנות מחירים באמצע עבודה פעילה.")
            return
        client = self.timer_client.get().strip()
        self._load_client_pricing(client)
        counts = self._current_issue_counts()
        issues = sorted(set(DEFAULT_BILLING_ISSUES) | set(self.issue_rates) | set(counts))
        pending_overrides = self._current_alert_overrides(client)
        dialog = tk.Toplevel(self.root)
        dialog.title("מחירים לפי סוג בעיה")
        fit_window_to_work_area(dialog, 760, 680, 570, 460)
        dialog.transient(self.root)
        dialog.grab_set()
        dialog.configure(bg="#E7D4AB")
        try:
            dialog.iconbitmap(default=str(resource_path("app.ico")))
        except Exception:
            pass

        tk.Label(
            dialog,
            text=(f"מחירים עבור הלקוח: {client}" if client else "מחירי ברירת מחדל"),
            bg="#5A3518", fg="white",
            font=("Segoe UI", 17, "bold"), pady=13,
        ).pack(fill="x")
        tk.Label(
            dialog,
            text=(
                "המחיר הוא לכל התראה מסוג זה. לחץ על שם סוג הבעיה כדי לראות את כל "
                "ההתראות מהדוח ולתת מחיר שונה להתראה מסוימת.\n"
                "המחירים יישמרו ללקוח וייטענו אוטומטית בפעם הבאה."
            ),
            bg="#FFF9EC", fg="#74471F", font=("Segoe UI", 10),
            justify="right", anchor="e", padx=16, pady=10,
        ).pack(fill="x", padx=14, pady=(14, 8))

        table_shell = tk.Frame(dialog, bg="#FFF9EC")
        table_shell.pack(fill="both", expand=True, padx=14)
        table_canvas = tk.Canvas(table_shell, bg="#FFF9EC", highlightthickness=0)
        table_scroll = ttk.Scrollbar(table_shell, orient="vertical", command=table_canvas.yview)
        table = tk.Frame(table_canvas, bg="#FFF9EC", padx=14, pady=10)
        table_window = table_canvas.create_window((0, 0), window=table, anchor="nw")
        table_canvas.configure(yscrollcommand=table_scroll.set)
        table_scroll.pack(side="left", fill="y")
        table_canvas.pack(side="right", fill="both", expand=True)
        table.bind(
            "<Configure>",
            lambda _event: table_canvas.configure(scrollregion=table_canvas.bbox("all")),
        )
        table_canvas.bind(
            "<Configure>",
            lambda event: table_canvas.itemconfigure(table_window, width=event.width),
        )
        tk.Label(table, text="סוג הבעיה", bg="#FFF9EC", fg="#5A3518",
                 font=("Segoe UI", 10, "bold")).grid(row=0, column=2, padx=8, pady=5)
        tk.Label(table, text="כמות בדוח", bg="#FFF9EC", fg="#5A3518",
                 font=("Segoe UI", 10, "bold")).grid(row=0, column=1, padx=8, pady=5)
        tk.Label(table, text="מחיר ליחידה ₪", bg="#FFF9EC", fg="#5A3518",
                 font=("Segoe UI", 10, "bold")).grid(row=0, column=0, padx=8, pady=5)
        rate_vars: dict[str, tk.StringVar] = {}

        def current_rates() -> dict[str, float]:
            result: dict[str, float] = {}
            for issue_name, variable in rate_vars.items():
                raw = variable.get().strip().replace(",", ".").replace("₪", "")
                try:
                    value = max(0.0, float(raw)) if raw else 0.0
                except ValueError:
                    value = 0.0
                if value > 0:
                    result[issue_name] = value
            return result

        def open_alerts(issue: str) -> None:
            matches = [
                item for item in self._current_alert_items(current_rates(), pending_overrides)
                if item.get("issue") == issue
            ]
            alerts = tk.Toplevel(dialog)
            alerts.title(f"התראות בדוח — {issue}")
            fit_window_to_work_area(alerts, 1030, 610, 720, 440)
            alerts.transient(dialog)
            alerts.grab_set()
            alerts.configure(bg="#E7D4AB")
            tk.Label(
                alerts, text=f"{issue} — {len(matches)} התראות בדוח",
                bg="#5A3518", fg="white", font=("Segoe UI", 16, "bold"), pady=12,
            ).pack(fill="x")
            tk.Label(
                alerts,
                text="בחר התראה, כתוב מחיר אחר ושמור. 'מחיר סוג' מחזיר אותה למחיר הכללי.",
                bg="#FFF9EC", fg="#74471F", font=("Segoe UI", 10),
                anchor="e", justify="right", padx=14, pady=9,
            ).pack(fill="x", padx=12, pady=(12, 6))
            tree_box = tk.Frame(alerts, bg="#FFF9EC")
            tree_box.pack(fill="both", expand=True, padx=12)
            alert_tree = ttk.Treeview(
                tree_box,
                columns=("message", "word", "line", "page", "price"),
                show="headings", selectmode="browse",
            )
            for column, title, width in (
                ("message", "ההודעה מהדוח", 390), ("word", "מילה בעייתית", 150),
                ("line", "שורה", 65), ("page", "עמוד", 65), ("price", "מחיר ₪", 90),
            ):
                alert_tree.heading(column, text=title)
                alert_tree.column(column, width=width, minwidth=55, anchor="e")
            alert_scroll = ttk.Scrollbar(tree_box, orient="vertical", command=alert_tree.yview)
            alert_tree.configure(yscrollcommand=alert_scroll.set)
            alert_scroll.pack(side="left", fill="y")
            alert_tree.pack(fill="both", expand=True)
            item_by_iid: dict[str, dict[str, object]] = {}
            for position, item in enumerate(matches):
                iid = str(position)
                item_by_iid[iid] = item
                alert_tree.insert("", "end", iid=iid, values=(
                    item.get("message", ""), item.get("word", ""), item.get("line", ""),
                    item.get("page", ""), f"{float(item.get('rate', 0) or 0):g}",
                ))
            found_preview_box = tk.Frame(
                alerts, bg="#FFF9EC", highlightthickness=1, highlightbackground="#CDB68E",
                height=155,
            )
            found_preview_box.pack(fill="x", padx=12, pady=(8, 0))
            found_preview_box.pack_propagate(False)
            tk.Label(
                found_preview_box, text="צילום תא „נמצא” מהדוח",
                bg="#FFF9EC", fg="#5A3518", font=("Segoe UI", 10, "bold"),
                anchor="e", padx=10, pady=4,
            ).pack(side="right", fill="y")
            found_preview_label = tk.Label(
                found_preview_box, text="בחר התראה כדי להציג את התמונה",
                bg="white", fg="#866A49", font=("Segoe UI", 10),
                anchor="center", justify="center", padx=8, pady=5,
            )
            found_preview_label.pack(side="left", fill="both", expand=True, padx=7, pady=7)
            found_page_cache: dict[int, Image.Image] = {}
            found_preview_photo: list[ImageTk.PhotoImage | None] = [None]
            edit = tk.Frame(alerts, bg="#E7D4AB", padx=12, pady=12)
            edit.pack(fill="x")
            selected_text = tk.StringVar(value="בחר התראה מהרשימה")
            price_var = tk.StringVar()
            tk.Label(
                edit, textvariable=selected_text, bg="#E7D4AB", fg="#5A3518",
                font=("Segoe UI", 10, "bold"), anchor="e",
            ).pack(side="right", fill="x", expand=True, padx=(8, 0))
            ttk.Entry(
                edit, textvariable=price_var, width=11, justify="center",
                style="Editor.TEntry", font=("Segoe UI", 10),
            ).pack(side="right", padx=5)
            tk.Label(edit, text="מחיר ₪", bg="#E7D4AB", fg="#5A3518").pack(side="right")

            def selected_alert() -> tuple[str, dict[str, object]] | None:
                selection = alert_tree.selection()
                if not selection:
                    messagebox.showinfo(APP_NAME, "יש לבחור התראה מהרשימה.", parent=alerts)
                    return None
                iid = selection[0]
                return iid, item_by_iid[iid]

            def alert_selected(_event=None) -> None:
                selection = alert_tree.selection()
                if not selection:
                    return
                item = item_by_iid[selection[0]]
                price_var.set(f"{float(item.get('rate', 0) or 0):g}")
                selected_text.set(
                    f"עמוד {item.get('page', '')} · שורה {item.get('line', '')} · "
                    f"{item.get('word', '')}"
                )
                try:
                    row_index = int(item.get("row_index", -1))
                    row = self.rows[row_index]
                    crop = self._found_cell_crop(row, found_page_cache)
                    if crop is None:
                        found_preview_photo[0] = None
                        found_preview_label.configure(
                            image="", text="בדוח הזה אין תא „נמצא” נפרד",
                        )
                    else:
                        scale = min(3.5, 820 / max(1, crop.width), 132 / max(1, crop.height))
                        shown = crop.resize(
                            (max(1, int(round(crop.width * scale))),
                             max(1, int(round(crop.height * scale)))),
                            Image.Resampling.LANCZOS,
                        )
                        found_preview_photo[0] = ImageTk.PhotoImage(shown)
                        found_preview_label.configure(
                            image=found_preview_photo[0], text="",
                        )
                except Exception:
                    found_preview_photo[0] = None
                    found_preview_label.configure(
                        image="", text="לא ניתן להציג את תא „נמצא” של השורה",
                    )

            def save_alert_price() -> None:
                selected = selected_alert()
                if selected is None:
                    return
                iid, item = selected
                raw = price_var.get().strip().replace(",", ".").replace("₪", "")
                try:
                    value = float(raw)
                    if value <= 0:
                        raise ValueError
                except ValueError:
                    messagebox.showerror(APP_NAME, "יש להזין מחיר גדול מאפס.", parent=alerts)
                    return
                key = str(item["key"])
                pending_overrides[key] = value
                item["rate"] = value
                item["custom_rate"] = True
                alert_tree.set(iid, "price", f"{value:g}")
                selected_text.set(selected_text.get() + " · מחיר אישי נשמר")

            def reset_alert_price() -> None:
                selected = selected_alert()
                if selected is None:
                    return
                iid, item = selected
                pending_overrides.pop(str(item["key"]), None)
                base = float(current_rates().get(issue, 0) or 0)
                item["rate"] = base
                item["custom_rate"] = False
                alert_tree.set(iid, "price", f"{base:g}" if base else "")
                price_var.set(f"{base:g}" if base else "")

            alert_tree.bind("<<TreeviewSelect>>", alert_selected)
            tk.Button(
                edit, text="שמירת מחיר להתראה", command=save_alert_price,
                bg="#A66A16", fg="white", relief="flat", padx=12, pady=7,
                font=("Segoe UI", 9, "bold"),
            ).pack(side="left", padx=4)
            tk.Button(
                edit, text="חזרה למחיר הסוג", command=reset_alert_price,
                bg="#F1E2C4", fg="#5A3518", relief="flat", padx=12, pady=7,
                font=("Segoe UI", 9, "bold"),
            ).pack(side="left", padx=4)
            if matches:
                alert_tree.selection_set("0")
                alert_tree.focus("0")
                alert_selected()

        for row_number, issue in enumerate(issues, start=1):
            variable = tk.StringVar(value=(
                f"{self.issue_rates[issue]:g}" if self.issue_rates.get(issue, 0) > 0 else ""
            ))
            rate_vars[issue] = variable
            issue_button = tk.Button(
                table, text=f"{issue}  ← הצגת ההתראות", bg="#FFF4D8", fg="#5A3518",
                activebackground="#F6D878", relief="flat", cursor="hand2",
                font=("Segoe UI", 10, "bold"), anchor="e",
                command=lambda selected_issue=issue: open_alerts(selected_issue),
            )
            issue_button.grid(row=row_number, column=2, sticky="ew", padx=8, pady=4)
            tk.Label(
                table, text=str(counts.get(issue, 0)), bg="#FFF9EC", fg="#866A49",
                font=("Segoe UI", 10),
            ).grid(row=row_number, column=1, padx=8, pady=4)
            ttk.Entry(
                table, textvariable=variable, width=12, justify="center",
                style="Editor.TEntry", font=("Segoe UI", 10),
            ).grid(row=row_number, column=0, padx=8, pady=4)
        table.columnconfigure(2, weight=1)

        def save_prices() -> None:
            updated: dict[str, float] = {}
            invalid: list[str] = []
            for issue, variable in rate_vars.items():
                raw = variable.get().strip().replace(",", ".").replace("₪", "")
                if not raw:
                    continue
                try:
                    value = float(raw)
                    if value < 0:
                        raise ValueError
                except ValueError:
                    invalid.append(issue)
                    continue
                if value > 0:
                    updated[issue] = value
            if invalid:
                messagebox.showerror(
                    APP_NAME,
                    "מחיר לא תקין עבור: " + ", ".join(invalid),
                    parent=dialog,
                )
                return
            self.issue_rates = updated
            client_key = self._pricing_client_key(client)
            if client:
                self.client_issue_rates[client_key] = dict(updated)
            else:
                self.default_issue_rates = dict(updated)
            report_key = self._report_pricing_key()
            if report_key:
                reports = self.client_alert_rates.setdefault(client_key, {})
                if pending_overrides:
                    reports[report_key] = dict(pending_overrides)
                else:
                    reports.pop(report_key, None)
                if not reports:
                    self.client_alert_rates.pop(client_key, None)
            self._save_settings()
            self._refresh_result_rows()
            self.status.set(
                f"נשמרו ל{client or 'ברירת המחדל'} {len(updated)} סוגי מחיר "
                f"ו־{len(pending_overrides)} מחירים להתראות מסוימות"
            )
            dialog.grab_release()
            dialog.destroy()

        buttons = tk.Frame(dialog, bg="#E7D4AB", padx=14, pady=12)
        buttons.pack(fill="x")
        tk.Button(
            buttons, text="שמירת המחירים", command=save_prices,
            bg="#A66A16", fg="white", activebackground="#8C5410",
            activeforeground="white", relief="flat", padx=18, pady=8,
            font=("Segoe UI", 10, "bold"),
        ).pack(side="right", padx=4)
        tk.Button(
            buttons, text="ביטול", command=dialog.destroy,
            bg="#F1E2C4", fg="#5A3518", relief="flat", padx=18, pady=8,
            font=("Segoe UI", 10, "bold"),
        ).pack(side="right", padx=4)

    def _format_timer_summary(self, summary: dict | None) -> str:
        if not summary:
            return "טרם נמדד זמן עבודה"
        try:
            started = datetime.fromisoformat(str(summary["start"]))
            ended = datetime.fromisoformat(str(summary["end"]))
            seconds = max(0.0, float(summary["seconds"]))
            rate = max(0.0, float(summary.get("rate", 0) or 0))
        except (KeyError, TypeError, ValueError):
            return "טרם נמדד זמן עבודה"
        hours_decimal = seconds / 3600
        payment_mode = str(summary.get("payment_mode", PAYMENT_MODE_HOURLY))
        if payment_mode == PAYMENT_MODE_ISSUE:
            alert_items = summary.get("alert_items", [])
            if isinstance(alert_items, list) and alert_items:
                payment, breakdown = alert_payment(alert_items)
            else:
                payment, breakdown = issue_payment(
                    summary.get("issue_counts", {})
                    if isinstance(summary.get("issue_counts"), dict) else {},
                    summary.get("issue_rates", {})
                    if isinstance(summary.get("issue_rates"), dict) else {},
                )
        else:
            payment = timer_payment(seconds, rate)
            breakdown = []
        client = str(summary.get("client", "")).strip()
        finance_status = str(summary.get("finance_status", "")).strip()
        client_part = f"לקוח {client}  |  " if client else ""
        finance_part = "  |  נשלח אוטומטית לכספים" if finance_status == "queued" else ""
        base = (
            f"{client_part}מ־{started:%d/%m/%Y %H:%M} עד {ended:%d/%m/%Y %H:%M}  |  "
            f"סה״כ {self._format_duration(seconds)} ({hours_decimal:.2f} שעות)"
        )
        if payment_mode == PAYMENT_MODE_ISSUE:
            issue_count = sum(int(item["count"]) for item in breakdown)
            details = self._format_issue_breakdown(breakdown)
            return (
                f"{base}  |  לפי סוג בעיה: {issue_count} תיקונים  |  "
                f"לתשלום ₪{payment:,.2f}{finance_part}"
                + (f"  |  {details}" if details else "")
            )
        return f"{base}  |  לתשלום ₪{payment:,.2f}{finance_part}"

    def save_customer_work_report(self, summary: dict | None = None) -> Path | None:
        if not CUSTOMER_EDITION:
            return None
        selected = summary if isinstance(summary, dict) else self.last_timer_summary
        if not isinstance(selected, dict):
            messagebox.showinfo(APP_NAME, "עדיין אין עבודה שהסתיימה ואפשר להפיק ממנה דוח.")
            return None
        try:
            started = datetime.fromisoformat(str(selected["start"]))
            document = build_customer_work_report_html(selected)
        except (KeyError, TypeError, ValueError) as exc:
            messagebox.showerror(APP_NAME, f"לא ניתן להפיק דוח מהסיכום השמור.\n\n{exc}")
            return None
        client = str(selected.get("client", "")).strip() or "לקוח"
        safe_client = re.sub(r'[<>:"/\\|?*]+', "-", client).strip(" .") or "לקוח"
        report_kind = (
            "דוח תיקונים" if selected.get("payment_mode") == PAYMENT_MODE_ISSUE
            else "דוח שעות"
        )
        initial_name = f"{report_kind} - {safe_client} - {started:%Y-%m-%d}.html"
        destination = filedialog.asksaveasfilename(
            parent=self.root,
            title="שמירת דוח עבודה",
            defaultextension=".html",
            filetypes=(("דוח עבודה שניתן להדפיס ל-PDF", "*.html"), ("כל הקבצים", "*.*")),
            initialfile=initial_name,
        )
        if not destination:
            return None
        report_path = Path(destination)
        try:
            report_path.parent.mkdir(parents=True, exist_ok=True)
            temporary = report_path.with_suffix(report_path.suffix + ".tmp")
            temporary.write_text(document, encoding="utf-8")
            temporary.replace(report_path)
        except OSError as exc:
            messagebox.showerror(APP_NAME, f"לא הצלחתי לשמור את דוח העבודה.\n\n{exc}")
            return None
        self.status.set(f"דוח העבודה נשמר: {report_path.name}")
        if messagebox.askyesno(
            APP_NAME,
            "דוח העבודה נשמר בהצלחה.\n\n"
            "לפתוח אותו עכשיו? בחלון שייפתח אפשר לבחור הדפסה ולשמור כ־PDF.",
        ):
            try:
                os.startfile(str(report_path))
            except OSError as exc:
                messagebox.showerror(APP_NAME, f"הדוח נשמר, אך לא הצלחתי לפתוח אותו.\n\n{exc}")
        return report_path

    def _complete_customer_timer(self, summary: dict, seconds: float, payment: Decimal) -> None:
        client = str(summary.get("client", "")).strip()
        self.last_timer_summary = summary
        self.work_history.append(dict(summary))
        self.work_history = self.work_history[-500:]
        self.timer_start = None
        self.timer_run_started = None
        self.timer_accumulated_seconds = 0.0
        self.timer_session_id = None
        self.timer_pdf_path = ""
        self.timer_client_value = ""
        self.timer_finance_username = ""
        self.timer_payment_mode_value = PAYMENT_MODE_HOURLY
        self.timer_issue_counts_value = {}
        self.timer_issue_rates_value = {}
        self.timer_alert_items_value = []
        if self.timer_after_job:
            self.root.after_cancel(self.timer_after_job)
            self.timer_after_job = None
        self.timer_elapsed_text.set(self._format_duration(seconds))
        self.timer_summary_text.set(self._format_timer_summary(summary))
        self._set_timer_controls()
        self._save_settings()
        self.status.set(f"העבודה של {client} הסתיימה · לתשלום ₪{payment:,.2f}")
        if messagebox.askyesno(
            APP_NAME,
            f"העבודה הסתיימה.\n\n"
            f"זמן: {self._format_duration(seconds)}\n"
            f"לתשלום: ₪{payment:,.2f}\n\n"
            "להפיק עכשיו דוח עבודה ללקוח?",
        ):
            self.save_customer_work_report(summary)

    def _restore_timer(self, settings: dict) -> None:
        self.timer_summary_text.set(self._format_timer_summary(self.last_timer_summary))
        active = settings.get("active_timer")
        if isinstance(active, dict):
            try:
                started = datetime.fromisoformat(str(active["start"]))
                rate = max(0.0, float(active["rate"]))
                if started <= datetime.now():
                    self.timer_start = started
                    run_started_value = active.get("run_started", active["start"])
                    self.timer_run_started = (
                        datetime.fromisoformat(str(run_started_value)) if run_started_value else None
                    )
                    self.timer_accumulated_seconds = max(
                        0.0, float(active.get("accumulated_seconds", 0.0))
                    )
                    self.timer_rate_value = rate
                    active_mode = str(active.get("payment_mode", PAYMENT_MODE_HOURLY))
                    if active_mode not in PAYMENT_MODE_LABELS:
                        active_mode = PAYMENT_MODE_HOURLY
                    self.timer_payment_mode_value = active_mode
                    self.payment_mode.set(PAYMENT_MODE_LABELS[active_mode])
                    raw_counts = active.get("issue_counts", {})
                    raw_rates = active.get("issue_rates", {})
                    self.timer_issue_counts_value = {
                        str(issue): max(0, int(value))
                        for issue, value in raw_counts.items()
                        if isinstance(raw_counts, dict) and str(issue).strip()
                    } if isinstance(raw_counts, dict) else {}
                    self.timer_issue_rates_value = {
                        str(issue): max(0.0, float(value))
                        for issue, value in raw_rates.items()
                        if isinstance(raw_rates, dict) and str(issue).strip()
                    } if isinstance(raw_rates, dict) else {}
                    raw_alert_items = active.get("alert_items", [])
                    self.timer_alert_items_value = (
                        [dict(item) for item in raw_alert_items if isinstance(item, dict)]
                        if isinstance(raw_alert_items, list) else []
                    )
                    self.timer_client_value = str(active.get("client", "")).strip()
                    self.timer_client.set(self.timer_client_value or self.timer_client.get().strip())
                    self.timer_session_id = str(active.get("session_id", "")).strip() or uuid.uuid4().hex
                    self.timer_pdf_path = str(active.get("pdf_path", "")).strip()
                    self.timer_finance_username = str(active.get("finance_username", "")).strip()
                    self.hourly_rate.set(f"{rate:g}")
            except (KeyError, TypeError, ValueError):
                self.timer_start = None
        self._set_timer_controls()
        self._timer_tick()

    def _set_timer_controls(self) -> None:
        if not hasattr(self, "timer_start_button"):
            return
        if self.timer_start is None:
            self.timer_start_button.state(["!disabled"])
            self.timer_pause_button.state(["disabled"])
            self.timer_finish_button.state(["disabled"])
            self.timer_cancel_button.state(["disabled"])
            self.timer_pause_text.set("הפסקה")
            if self.selected_payment_mode() == PAYMENT_MODE_HOURLY:
                self.timer_rate_entry.state(["!disabled"])
            else:
                self.timer_rate_entry.state(["disabled"])
            self.timer_client_combo.state(["!disabled"])
            self.payment_mode_combo.state(["readonly"])
            self.timer_issue_price_button.state(["!disabled"])
        else:
            self.timer_start_button.state(["disabled"])
            self.timer_pause_button.state(["!disabled"])
            self.timer_finish_button.state(["!disabled"])
            self.timer_cancel_button.state(["!disabled"])
            self.timer_pause_text.set("הפסקה" if self.timer_run_started else "המשך")
            self.timer_rate_entry.state(["disabled"])
            self.timer_client_combo.state(["disabled"])
            self.payment_mode_combo.state(["disabled"])
            self.timer_issue_price_button.state(["disabled"])
        if CUSTOMER_EDITION and hasattr(self, "timer_report_button"):
            self.timer_report_button.state(
                ["!disabled"] if isinstance(self.last_timer_summary, dict) else ["disabled"]
            )

    def _timer_tick(self) -> None:
        if self.timer_after_job:
            try:
                self.root.after_cancel(self.timer_after_job)
            except tk.TclError:
                pass
            self.timer_after_job = None
        if self.timer_start is None:
            return
        elapsed = self.timer_accumulated_seconds
        if self.timer_run_started is not None:
            elapsed += (datetime.now() - self.timer_run_started).total_seconds()
        self.timer_elapsed_text.set(self._format_duration(elapsed))
        if self.timer_run_started is not None:
            self.timer_after_job = self.root.after(500, self._timer_tick)

    def start_timer(self) -> None:
        if self.timer_start is not None:
            return
        if not CUSTOMER_EDITION:
            self._refresh_finance_clients(force=True)
            if not self.finance_username:
                messagebox.showerror(
                    APP_NAME,
                    "עדיין אין חיבור למשתמש בתוכנת הכספים.\n\n"
                    "התקן/פתח פעם אחת את תוכנת הכספים המעודכנת, התחבר למשתמש שלך, "
                    "וחזור לכאן. רשימת הלקוחות והמחירים תופיע אוטומטית.",
                )
                return
        client = self.timer_client.get().strip()
        if not client:
            messagebox.showerror(APP_NAME, "יש לבחור או לכתוב לקוח לפני התחלת הטיימר")
            try:
                self.timer_client_combo.focus_set()
            except tk.TclError:
                pass
            return
        payment_mode = self.selected_payment_mode()
        issue_counts: dict[str, int] = {}
        issue_rates: dict[str, float] = {}
        alert_items: list[dict[str, object]] = []
        if payment_mode == PAYMENT_MODE_ISSUE:
            self._load_client_pricing(client)
            if not self.rows or self.pdf_path is None:
                messagebox.showerror(
                    APP_NAME,
                    "כדי לחשב תשלום לפי סוג בעיה יש לפתוח תחילה דוח ולהמתין לסיום הזיהוי.",
                )
                return
            issue_counts = self._current_issue_counts()
            if not issue_counts:
                messagebox.showerror(APP_NAME, "לא נמצאו בדוח סוגי בעיה שאפשר לחייב לפיהם.")
                return
            missing_prices = [
                issue for issue in sorted(issue_counts)
                if float(self.issue_rates.get(issue, 0) or 0) <= 0
            ]
            if missing_prices:
                messagebox.showerror(
                    APP_NAME,
                    "יש להגדיר מחיר גדול מאפס לכל סוג שמופיע בדוח:\n\n"
                    + ", ".join(missing_prices),
                )
                self.open_issue_pricing()
                return
            issue_rates = {
                issue: float(self.issue_rates[issue]) for issue in issue_counts
            }
            alert_items = self._current_alert_items(issue_rates)
            missing_alert_prices = [
                item for item in alert_items if float(item.get("rate", 0) or 0) <= 0
            ]
            if missing_alert_prices:
                messagebox.showerror(
                    APP_NAME,
                    "יש התראות ללא מחיר. פתח 'מחירים לפי סוג' והשלם מחיר לכל סוג.",
                )
                self.open_issue_pricing()
                return
            rate = 0.0
        else:
            raw_rate = self.hourly_rate.get().strip().replace(",", ".").replace("₪", "")
            try:
                rate = float(raw_rate)
                if rate <= 0:
                    raise ValueError
            except ValueError:
                messagebox.showerror(
                    APP_NAME,
                    "יש להזין מחיר גדול מאפס לשעה, לדוגמה 75 או 75.50",
                )
                return
        started = datetime.now()
        self.timer_start = started
        self.timer_run_started = started
        self.timer_accumulated_seconds = 0.0
        self.timer_rate_value = rate
        self.timer_client_value = client
        self.timer_payment_mode_value = payment_mode
        self.timer_issue_counts_value = issue_counts
        self.timer_issue_rates_value = issue_rates
        self.timer_alert_items_value = alert_items
        self.timer_session_id = uuid.uuid4().hex
        self.timer_pdf_path = str(self.pdf_path.resolve()) if self.pdf_path else ""
        self.timer_finance_username = "" if CUSTOMER_EDITION else self.finance_username
        if CUSTOMER_EDITION:
            self._remember_local_client(
                client, rate if payment_mode == PAYMENT_MODE_HOURLY else None,
            )
        self.timer_client.set(client)
        if payment_mode == PAYMENT_MODE_HOURLY:
            self.hourly_rate.set(f"{rate:g}")
        self.timer_elapsed_text.set("00:00:00")
        self._set_timer_controls()
        self._save_settings()
        self._timer_tick()
        if payment_mode == PAYMENT_MODE_ISSUE:
            issue_total = sum(issue_counts.values())
            self.status.set(
                f"העבודה של {client} התחילה · החיוב לפי {issue_total} תיקונים בדוח"
            )
        else:
            self.status.set(f"טיימר התיקונים של {client} התחיל")

    def toggle_timer_pause(self) -> None:
        if self.timer_start is None:
            return
        now = datetime.now()
        if self.timer_run_started is not None:
            self.timer_accumulated_seconds += max(
                0.0, (now - self.timer_run_started).total_seconds()
            )
            self.timer_run_started = None
            if self.timer_after_job:
                self.root.after_cancel(self.timer_after_job)
                self.timer_after_job = None
            self.timer_elapsed_text.set(self._format_duration(self.timer_accumulated_seconds))
            self.status.set("הטיימר בהפסקה - זמן ההפסקה אינו מחושב")
        else:
            self.timer_run_started = now
            self.status.set("הטיימר ממשיך")
            self._timer_tick()
        self._set_timer_controls()
        self._save_settings()

    def cancel_timer(self) -> None:
        if self.timer_start is None:
            return
        seconds = self.timer_accumulated_seconds
        if self.timer_run_started is not None:
            seconds += max(0.0, (datetime.now() - self.timer_run_started).total_seconds())
        client = self.timer_client_value or self.timer_client.get().strip()
        cancel_explanation = (
            "יימחק ולא יישמר בדוח השעות"
            if CUSTOMER_EDITION else "יימחק ולא יישלח לתוכנת הכספים"
        )
        if not messagebox.askyesno(
            APP_NAME,
            f"לבטל את הטיימר של {client or 'העבודה הנוכחית'}?\n\n"
            f"הזמן שנמדד ({self._format_duration(seconds)}) {cancel_explanation}.",
        ):
            return
        if self.timer_after_job:
            try:
                self.root.after_cancel(self.timer_after_job)
            except tk.TclError:
                pass
            self.timer_after_job = None
        self.timer_start = None
        self.timer_run_started = None
        self.timer_accumulated_seconds = 0.0
        self.timer_rate_value = 0.0
        self.timer_client_value = ""
        self.timer_payment_mode_value = PAYMENT_MODE_HOURLY
        self.timer_issue_counts_value = {}
        self.timer_issue_rates_value = {}
        self.timer_alert_items_value = []
        self.timer_session_id = None
        self.timer_pdf_path = ""
        self.timer_finance_username = ""
        self.timer_elapsed_text.set("00:00:00")
        self.timer_summary_text.set(
            "הטיימר בוטל - הזמן לא נשמר"
            if CUSTOMER_EDITION else "הטיימר בוטל - לא נשלח דבר לתוכנת הכספים"
        )
        self._set_timer_controls()
        self._save_settings()
        self.status.set("הטיימר בוטל")

    def finish_timer(self) -> None:
        if self.timer_start is None:
            return
        ended = datetime.now()
        seconds = self.timer_accumulated_seconds
        if self.timer_run_started is not None:
            seconds += max(0.0, (ended - self.timer_run_started).total_seconds())
        client = self.timer_client_value or self.timer_client.get().strip()
        session_id = self.timer_session_id or uuid.uuid4().hex
        payment_mode = self.timer_payment_mode_value
        if payment_mode == PAYMENT_MODE_ISSUE:
            if self.timer_alert_items_value:
                payment, issue_breakdown = alert_payment(self.timer_alert_items_value)
            else:
                payment, issue_breakdown = issue_payment(
                    self.timer_issue_counts_value, self.timer_issue_rates_value,
                )
        else:
            payment = timer_payment(seconds, self.timer_rate_value)
            issue_breakdown = []
        hours_decimal = Decimal(str(max(0.0, seconds))) / Decimal("3600")
        report_path = self.timer_pdf_path or (str(self.pdf_path.resolve()) if self.pdf_path else "")
        report_name = Path(report_path).name if report_path else ""
        summary = {
            "start": self.timer_start.isoformat(),
            "end": ended.isoformat(),
            "seconds": seconds,
            "rate": self.timer_rate_value,
            "payment_mode": payment_mode,
            "issue_counts": dict(self.timer_issue_counts_value),
            "issue_rates": dict(self.timer_issue_rates_value),
            "issue_breakdown": issue_breakdown,
            "alert_items": [dict(item) for item in self.timer_alert_items_value],
            "client": client,
            "session_id": session_id,
            "finance_status": "queued" if not CUSTOMER_EDITION else "local",
            "report_path": report_path,
            "report_name": report_name,
            "amount": float(payment),
        }
        if CUSTOMER_EDITION:
            self._complete_customer_timer(summary, seconds, payment)
            return
        job = {
            "schemaVersion": 1,
            "source": "DukReportReader",
            "externalId": f"duk-report-timer:{session_id}",
            "sessionId": session_id,
            "targetUsername": self.timer_finance_username or self.finance_username,
            "type": "income",
            "category": "תיקונים",
            "client": client,
            "amount": float(payment),
            "date": ended.strftime("%Y-%m-%d"),
            "start": self.timer_start.isoformat(),
            "end": ended.isoformat(),
            "workSeconds": round(seconds, 3),
            "hours": str(hours_decimal.quantize(Decimal("0.000001"), rounding=ROUND_HALF_UP)),
            "hourlyRate": self.timer_rate_value,
            "billingMode": payment_mode,
            "issueCounts": dict(self.timer_issue_counts_value),
            "issueRates": dict(self.timer_issue_rates_value),
            "issueBreakdown": issue_breakdown,
            "reportPath": report_path,
            "reportName": report_name,
            "note": " | ".join(filter(None, (
                f"מ־{self.timer_start:%d/%m/%Y %H:%M} עד {ended:%d/%m/%Y %H:%M}",
                f"{self._format_duration(seconds)} זמן עבודה",
                (
                    "חיוב לפי סוג בעיה: " + self._format_issue_breakdown(issue_breakdown)
                    if payment_mode == PAYMENT_MODE_ISSUE
                    else f"₪{self.timer_rate_value:g} לשעה"
                ),
                f"דוח: {report_name}" if report_name else "",
            ))),
            "createdAt": int(ended.timestamp() * 1000),
        }
        try:
            queue_finance_repair_job(job)
        except (OSError, ValueError) as exc:
            self.timer_accumulated_seconds = seconds
            self.timer_run_started = None
            if self.timer_after_job:
                self.root.after_cancel(self.timer_after_job)
                self.timer_after_job = None
            self._set_timer_controls()
            self._save_settings()
            messagebox.showerror(
                APP_NAME,
                "לא הצלחתי לשמור את העבודה להעברה לתוכנת הכספים. "
                "הטיימר נשמר בהפסקה; לחץ שוב על סיום כדי לנסות מחדש.\n\n"
                f"{exc}",
            )
            self.status.set("העבודה טרם הועברה לכספים; הטיימר נשמר בהפסקה")
            return
        self.last_timer_summary = summary
        self.timer_start = None
        self.timer_run_started = None
        self.timer_accumulated_seconds = 0.0
        self.timer_session_id = None
        self.timer_pdf_path = ""
        self.timer_client_value = ""
        self.timer_finance_username = ""
        self.timer_payment_mode_value = PAYMENT_MODE_HOURLY
        self.timer_issue_counts_value = {}
        self.timer_issue_rates_value = {}
        self.timer_alert_items_value = []
        if self.timer_after_job:
            self.root.after_cancel(self.timer_after_job)
            self.timer_after_job = None
        self.timer_elapsed_text.set(self._format_duration(seconds))
        self.timer_summary_text.set(self._format_timer_summary(self.last_timer_summary))
        self._set_timer_controls()
        self._save_settings()
        billing_label = "לפי סוג בעיה" if payment_mode == PAYMENT_MODE_ISSUE else "לפי זמן"
        self.status.set(
            f"העבודה של {client} הסתיימה ({billing_label}) - "
            f"₪{payment:,.2f} נשלחו אוטומטית לכספים בקטגוריית תיקונים"
        )

    @staticmethod
    def _display_key(keysym: str) -> str:
        names = {
            "Return": "Enter", "minus": "−", "plus": "+", "space": "רווח",
            "Left": "חץ שמאלה", "Right": "חץ ימינה", "Up": "חץ למעלה", "Down": "חץ למטה",
            "Prior": "Page Up", "Next": "Page Down", "BackSpace": "Backspace", "Escape": "Esc",
        }
        return names.get(keysym, keysym)

    def _update_shortcut_text(self) -> None:
        if hasattr(self, "shortcut_vars"):
            for action, variable in self.shortcut_vars.items():
                variable.set(self._display_key(self.key_bindings[action]))
        if hasattr(self, "footer_text"):
            self.footer_text.set(
                "מקשי קיצור: הבא - " + self._display_key(self.key_bindings["next"])
                + "   |   הקודם - " + self._display_key(self.key_bindings["previous"])
                + "   |   חזרה - " + self._display_key(self.key_bindings["repeat"])
            )

    def open_key_settings(self) -> None:
        if self.key_settings_open:
            return
        self.key_settings_open = True
        dialog = tk.Toplevel(self.root)
        dialog.title("הגדרת מקשים")
        dialog.geometry("500x360")
        dialog.resizable(False, False)
        dialog.transient(self.root)
        dialog.grab_set()
        dialog.configure(bg="#E7D4AB")
        try:
            dialog.iconbitmap(default=str(resource_path("app.ico")))
        except Exception:
            pass

        temporary = dict(self.key_bindings)
        labels = {
            action: tk.StringVar(value=self._display_key(key))
            for action, key in temporary.items()
        }
        capture_action: list[str | None] = [None]
        instruction = tk.StringVar(value="בחר פעולה ולאחר מכן לחץ על המקש הרצוי")

        tk.Label(
            dialog, text="הגדרת מקשי פעולה", bg="#5A3518", fg="white",
            font=("Segoe UI", 17, "bold"), pady=14,
        ).pack(fill="x")
        tk.Label(
            dialog, textvariable=instruction, bg="#FFF9EC", fg="#74471F",
            font=("Segoe UI", 10, "bold"), pady=10,
        ).pack(fill="x", padx=18, pady=(16, 8))

        rows_frame = tk.Frame(dialog, bg="#FFF9EC", padx=16, pady=12)
        rows_frame.pack(fill="x", padx=18)
        action_names = {"next": "מעבר לשורה הבאה", "previous": "חזרה לשורה הקודמת", "repeat": "הקראה חוזרת"}

        def begin_capture(action: str) -> None:
            capture_action[0] = action
            instruction.set(f"לחץ עכשיו על המקש עבור: {action_names[action]}")
            dialog.focus_force()

        for row_index, action in enumerate(("next", "previous", "repeat")):
            tk.Label(
                rows_frame, text=action_names[action], bg="#FFF9EC", fg="#332315",
                font=("Segoe UI", 11, "bold"), anchor="e",
            ).grid(row=row_index, column=2, sticky="e", padx=8, pady=7)
            tk.Label(
                rows_frame, textvariable=labels[action], bg="#F6D878", fg="#332315",
                font=("Segoe UI", 11, "bold"), width=12, pady=7,
            ).grid(row=row_index, column=1, padx=8, pady=7)
            tk.Button(
                rows_frame, text="שנה", command=lambda selected=action: begin_capture(selected),
                bg="#A66A16", fg="white", activebackground="#8C5410", activeforeground="white",
                relief="flat", font=("Segoe UI", 10, "bold"), width=8, pady=6,
            ).grid(row=row_index, column=0, padx=8, pady=7)
        rows_frame.columnconfigure(2, weight=1)

        def capture(event) -> str:
            action = capture_action[0]
            if not action:
                return "break"
            if event.keysym in {"Shift_L", "Shift_R", "Control_L", "Control_R", "Alt_L", "Alt_R", "Caps_Lock"}:
                return "break"
            temporary[action] = event.keysym
            labels[action].set(self._display_key(event.keysym))
            capture_action[0] = None
            instruction.set("המקש נקלט. אפשר לשנות פעולה נוספת או לשמור")
            return "break"

        dialog.bind("<KeyPress>", capture)

        def close_dialog() -> None:
            self.key_settings_open = False
            dialog.grab_release()
            dialog.destroy()

        def save_keys() -> None:
            if len(set(temporary.values())) != 3:
                messagebox.showerror(APP_NAME, "יש לבחור מקש שונה לכל פעולה.", parent=dialog)
                return
            self.key_bindings = temporary
            self._save_settings()
            self._update_shortcut_text()
            self._bind_keys()
            close_dialog()
            self.status.set("הגדרות המקשים נשמרו")

        buttons = tk.Frame(dialog, bg="#E7D4AB")
        buttons.pack(fill="x", padx=18, pady=14)
        tk.Button(
            buttons, text="שמירה", command=save_keys, bg="#5A3518", fg="white",
            activebackground="#74471F", activeforeground="white", relief="flat",
            font=("Segoe UI", 10, "bold"), padx=22, pady=8,
        ).pack(side="right", padx=5)
        tk.Button(
            buttons, text="ביטול", command=close_dialog, bg="#F1E2C4", fg="#5A3518",
            activebackground="#E5CF9F", relief="flat", font=("Segoe UI", 10, "bold"), padx=22, pady=8,
        ).pack(side="right", padx=5)
        dialog.protocol("WM_DELETE_WINDOW", close_dialog)

    def open_default_settings(self) -> None:
        if self.default_settings_open:
            return
        self.default_settings_open = True
        dialog = tk.Toplevel(self.root)
        dialog.title("הגדרות ברירת מחדל")
        fit_window_to_work_area(dialog, 720, 710, 620, 600)
        dialog.resizable(True, True)
        dialog.transient(self.root)
        dialog.grab_set()
        dialog.configure(bg="#E7D4AB")
        try:
            dialog.iconbitmap(default=str(resource_path("app.ico")))
        except Exception:
            pass

        voice_var = tk.StringVar(value=self.voice_choice.get())
        speed_var = tk.StringVar(value=str(int(round(self.speed.get()))))
        gap_var = tk.StringVar(value=f"{self.speech_gap_seconds():g}")
        zoom_var = tk.StringVar(value=str(int(round(self.default_zoom_factor * 100))))
        rate_var = tk.StringVar(value=self.hourly_rate.get().strip())
        client_var = tk.StringVar(value=self.timer_client.get().strip())

        tk.Label(
            dialog, text="הגדרות ברירת מחדל", bg="#5A3518", fg="white",
            font=("Segoe UI", 18, "bold"), pady=14,
        ).pack(fill="x")
        tk.Label(
            dialog, text="הערכים האלה ייטענו אוטומטית בכל הפעלה ובכל דוח חדש",
            bg="#FFF9EC", fg="#74471F", font=("Segoe UI", 10, "bold"), pady=10,
        ).pack(fill="x", padx=18, pady=(16, 8))

        form = tk.Frame(dialog, bg="#FFF9EC", padx=22, pady=16)
        form.pack(fill="x", padx=18)

        def add_row(row: int, label: str, widget: tk.Widget, explanation: str = "") -> None:
            tk.Label(
                form, text=label, bg="#FFF9EC", fg="#332315",
                font=("Segoe UI", 11, "bold"), anchor="e",
            ).grid(row=row, column=2, sticky="e", padx=(10, 4), pady=8)
            widget.grid(row=row, column=1, sticky="ew", padx=8, pady=8)
            if explanation:
                tk.Label(
                    form, text=explanation, bg="#FFF9EC", fg="#866A49",
                    font=("Segoe UI", 9), anchor="e",
                ).grid(row=row, column=0, sticky="e", padx=(4, 8), pady=8)

        voice_box = ttk.Combobox(
            form, textvariable=voice_var, state="readonly", width=20,
            values=VOICE_CHOICES, justify="right",
        )
        add_row(0, "קול", voice_box)

        def test_selected_voice() -> None:
            try:
                rate = max(-50, min(50, int(round(float(speed_var.get())))))
            except (TypeError, ValueError):
                rate = 0
            voice = self._voice_id_for_choice(voice_var.get())
            self.status.set(f"בודק את הקול: {voice_var.get()}")
            self.speech.speak(
                ["זוהי בדיקה של הקול שנבחר"], rate, voice, 0.0,
            )

        tk.Button(
            form, text="בדיקת קול", command=test_selected_voice,
            bg="#F6D878", fg="#5A3518", activebackground="#E8C65B",
            relief="flat", font=("Segoe UI", 9, "bold"), padx=8, pady=4,
        ).grid(row=0, column=0, sticky="w", padx=(4, 8), pady=8)
        speed_box = ttk.Combobox(
            form, textvariable=speed_var, width=20, justify="center",
            values=tuple(str(value) for value in range(-50, 51, 10)),
        )
        add_row(1, "מהירות דיבור", speed_box, "מ־50− עד 50+")
        gap_box = ttk.Combobox(
            form, textvariable=gap_var, state="readonly", width=20, justify="center",
            values=("0", "0.25", "0.5", "0.75", "1", "1.5", "2", "3", "4", "5"),
        )
        add_row(2, "השהיה בין המילים", gap_box, "בשניות")
        zoom_box = ttk.Combobox(
            form, textvariable=zoom_var, width=20, justify="center",
            values=("60", "80", "100", "120", "150", "200", "250", "300", "350", "400"),
        )
        add_row(3, "הגדלת העמוד", zoom_box, "באחוזים")
        rate_entry = ttk.Entry(form, textvariable=rate_var, width=22, justify="center")
        add_row(4, "מחיר לשעה", rate_entry, "אפשר להשאיר ריק")
        client_box = ttk.Combobox(
            form, textvariable=client_var, width=20, justify="right",
            values=tuple(client.get("name", "") for client in self.finance_clients if client.get("name")),
        )
        add_row(5, "לקוח ברירת מחדל", client_box, "לטיימר תיקונים")
        form.columnconfigure(1, weight=1)

        key_frame = tk.Frame(dialog, bg="#FFF9EC", padx=18, pady=10)
        key_frame.pack(fill="x", padx=18, pady=(8, 0))
        tk.Label(
            key_frame,
            text=(
                "מקשים: הבא " + self._display_key(self.key_bindings["next"])
                + "  |  הקודם " + self._display_key(self.key_bindings["previous"])
                + "  |  חזרה " + self._display_key(self.key_bindings["repeat"])
            ),
            bg="#FFF9EC", fg="#332315", font=("Segoe UI", 10, "bold"), anchor="e",
        ).pack(side="right", fill="x", expand=True)

        def close_dialog() -> None:
            self.default_settings_open = False
            try:
                dialog.grab_release()
            except tk.TclError:
                pass
            dialog.destroy()

        def open_keys() -> None:
            close_dialog()
            self.root.after(50, self.open_key_settings)

        tk.Button(
            key_frame, text="שינוי מקשים", command=open_keys, bg="#F1E2C4", fg="#5A3518",
            activebackground="#E5CF9F", relief="flat", font=("Segoe UI", 10, "bold"),
            padx=15, pady=7,
        ).pack(side="left", padx=(8, 0))

        def check_update_from_settings() -> None:
            close_dialog()
            self.root.after(50, lambda: self.check_for_updates(silent=False))

        if not GIGAPDF_OCR_EDITION:
            tk.Button(
                key_frame, text=f"בדיקת עדכון · {APP_VERSION}", command=check_update_from_settings,
                bg="#F6D878", fg="#5A3518", activebackground="#E8C65B", relief="flat",
                font=("Segoe UI", 10, "bold"), padx=15, pady=7,
            ).pack(side="left", padx=(8, 0))

        def open_ai_settings() -> None:
            close_dialog()
            self.root.after(50, self.open_offline_ai_manager)

        if not CUSTOMER_EDITION and not GIGAPDF_OCR_EDITION:
            ai_frame = tk.Frame(dialog, bg="#FFF9EC", padx=18, pady=10)
            ai_frame.pack(fill="x", padx=18, pady=(8, 0))
            tk.Button(
                ai_frame, text="AI אופליין — התקנה וניהול מודלים", command=open_ai_settings,
                bg="#278552", fg="white", activebackground="#1F6B42",
                activeforeground="white", relief="flat", font=("Segoe UI", 10, "bold"),
                padx=15, pady=7,
            ).pack(fill="x")

        def reset_fields() -> None:
            voice_var.set("מיכאל - איכותי אופליין")
            speed_var.set("0")
            gap_var.set("1")
            zoom_var.set("100")
            rate_var.set("")
            client_var.set("")

        def save_defaults() -> None:
            try:
                speed = int(round(float(speed_var.get())))
                gap = float(gap_var.get())
                zoom_percent = float(zoom_var.get())
                if not -50 <= speed <= 50 or not 0 <= gap <= 5 or not 60 <= zoom_percent <= 400:
                    raise ValueError
                raw_rate = rate_var.get().strip().replace(",", ".").replace("₪", "")
                if raw_rate and float(raw_rate) <= 0:
                    raise ValueError
            except ValueError:
                messagebox.showerror(
                    APP_NAME,
                    "בדוק את הערכים: מהירות 50− עד 50+, השהיה 0 עד 5, הגדלה 60% עד 400%, ומחיר חיובי.",
                    parent=dialog,
                )
                return
            self.voice_choice.set(voice_var.get())
            self.speed.set(speed)
            self.speed_text.set(self._speed_label(speed))
            self.speech_gap.set(f"{gap:g}")
            self.default_zoom_factor = zoom_percent / 100.0
            self.hourly_rate.set(rate_var.get().strip())
            self.timer_client.set(client_var.get().strip())
            if CUSTOMER_EDITION and client_var.get().strip():
                try:
                    saved_rate = float(raw_rate) if raw_rate else None
                except ValueError:
                    saved_rate = None
                self._remember_local_client(client_var.get().strip(), saved_rate)
            if self.pdf_path is not None:
                self._set_zoom(self.default_zoom_factor)
            self._save_settings()
            close_dialog()
            self.status.set("הגדרות ברירת המחדל נשמרו")

        buttons = tk.Frame(dialog, bg="#E7D4AB")
        buttons.pack(fill="x", padx=18, pady=14)
        tk.Button(
            buttons, text="שמירה", command=save_defaults, bg="#5A3518", fg="white",
            activebackground="#74471F", activeforeground="white", relief="flat",
            font=("Segoe UI", 10, "bold"), padx=24, pady=9,
        ).pack(side="right", padx=5)
        tk.Button(
            buttons, text="איפוס ערכים", command=reset_fields, bg="#F6D878", fg="#5A3518",
            activebackground="#E8C65B", relief="flat", font=("Segoe UI", 10, "bold"),
            padx=20, pady=9,
        ).pack(side="right", padx=5)
        tk.Button(
            buttons, text="ביטול", command=close_dialog, bg="#F1E2C4", fg="#5A3518",
            activebackground="#E5CF9F", relief="flat", font=("Segoe UI", 10, "bold"),
            padx=20, pady=9,
        ).pack(side="left", padx=5)
        dialog.protocol("WM_DELETE_WINDOW", close_dialog)

    def open_offline_ai_manager(self) -> None:
        if self.offline_ai is None:
            messagebox.showinfo(APP_NAME, "AI אופליין זמין רק בגרסה הפרטית.")
            return
        if self.offline_ai_dialog is not None:
            try:
                if self.offline_ai_dialog.winfo_exists():
                    self.offline_ai_dialog.lift()
                    return
            except tk.TclError:
                pass
        dialog = tk.Toplevel(self.root)
        self.offline_ai_dialog = dialog
        dialog.title("AI אופליין — למידת OCR")
        fit_window_to_work_area(dialog, 760, 650, 680, 560)
        dialog.transient(self.root)
        dialog.configure(bg="#E7D4AB")
        try:
            dialog.iconbitmap(default=str(resource_path("app.ico")))
        except Exception:
            pass
        tk.Label(
            dialog, text="AI אופליין ללמידת תיקוני OCR", bg="#5A3518", fg="white",
            font=("Segoe UI", 18, "bold"), pady=14,
        ).pack(fill="x")
        tk.Label(
            dialog,
            text=(
                "אתה מתקן זיהוי שגוי — ה-AI משווה לתמונת השורה, מסביר את הטעות "
                "ושומר כלל בטוח לפעמים הבאות.\n"
                "העיבוד נעשה במחשב; תמונות הדוח אינן נשלחות לשירות AI חיצוני."
            ),
            bg="#FFF9EC", fg="#74471F", font=("Segoe UI", 10),
            justify="right", anchor="e", padx=18, pady=12,
        ).pack(fill="x", padx=18, pady=(16, 8))

        enabled_var = tk.BooleanVar(value=self.ai_enabled)
        auto_var = tk.BooleanVar(value=self.ai_auto_review)
        vision_var = tk.BooleanVar(value=self.ai_vision_fallback)
        threshold_var = tk.StringVar(value=f"{self.ai_confidence_threshold:g}")
        options = tk.Frame(dialog, bg="#FFF9EC", padx=16, pady=10)
        options.pack(fill="x", padx=18)
        for label, variable in (
            ("הפעלת AI אופליין", enabled_var),
            ("בדיקה אוטומטית של זיהויים לא בטוחים", auto_var),
            ("בדיקת תמונת השורה כשהטקסט אינו מספיק", vision_var),
        ):
            tk.Checkbutton(
                options, text=label, variable=variable, bg="#FFF9EC", fg="#332315",
                activebackground="#FFF9EC", selectcolor="#F6D878", anchor="e",
                font=("Segoe UI", 10, "bold"),
            ).pack(fill="x", pady=2)
        threshold_row = tk.Frame(options, bg="#FFF9EC")
        threshold_row.pack(fill="x", pady=(6, 0))
        tk.Label(
            threshold_row, text="בדיקה מתחת לביטחון", bg="#FFF9EC", fg="#5A3518",
            font=("Segoe UI", 10, "bold"),
        ).pack(side="right", padx=(8, 0))
        ttk.Combobox(
            threshold_row, textvariable=threshold_var, state="readonly", width=7,
            values=("50", "60", "65", "70", "72", "75", "80", "85"), justify="center",
        ).pack(side="right")

        state_text = tk.StringVar()
        progress_text = tk.StringVar(value="מוכן")
        progress_value = tk.DoubleVar(value=0)
        tk.Label(
            dialog, textvariable=state_text, bg="#FFF9EC", fg="#278552",
            font=("Segoe UI", 11, "bold"), justify="right", anchor="e", padx=16, pady=10,
        ).pack(fill="x", padx=18, pady=(8, 0))
        ttk.Progressbar(dialog, variable=progress_value, maximum=100).pack(
            fill="x", padx=22, pady=(12, 3),
        )
        tk.Label(
            dialog, textvariable=progress_text, bg="#E7D4AB", fg="#5A3518",
            font=("Segoe UI", 10, "bold"), anchor="e",
        ).pack(fill="x", padx=22)

        def dialog_exists() -> bool:
            try:
                return bool(dialog.winfo_exists())
            except tk.TclError:
                return False

        def refresh_status() -> None:
            if not dialog_exists():
                return
            state = self.offline_ai.status()
            text_size = float(state["text_bytes"]) / (1024 ** 3)
            vision_size = float(state["vision_bytes"]) / (1024 ** 3)
            state_text.set(
                f"מנוע: {'מותקן' if state['runtime'] else 'חסר'}   |   "
                f"טקסט: {'מותקן' if state['text'] else 'חסר'} {text_size:.2f}GB   |   "
                f"תמונה: {'מותקן' if state['vision'] else 'חסר'} {vision_size:.2f}GB"
            )

        def update_progress(label: str, completed: int, total: int) -> None:
            def update() -> None:
                if not dialog_exists():
                    return
                progress_value.set(completed / total * 100 if total else 0)
                suffix = f" מתוך {total / (1024 ** 2):,.0f} MB" if total else ""
                progress_text.set(f"{label}: {completed / (1024 ** 2):,.0f} MB{suffix}")
            self.root.after(0, update)

        def install(package: str) -> None:
            if self.offline_ai_thread and self.offline_ai_thread.is_alive():
                messagebox.showinfo(APP_NAME, "כבר מתבצעת פעולת AI.", parent=dialog)
                return
            self.offline_ai_cancel.clear()
            progress_text.set("מתחיל הורדה...")
            progress_value.set(0)

            def worker() -> None:
                try:
                    if package == "text":
                        self.offline_ai.install_text_package(self.offline_ai_cancel, update_progress)
                    else:
                        self.offline_ai.install_vision_package(self.offline_ai_cancel, update_progress)
                    self.ai_enabled = True
                    self.root.after(0, enabled_var.set, True)
                    self.root.after(0, progress_value.set, 100)
                    self.root.after(0, progress_text.set, "ההתקנה הושלמה")
                    self.root.after(0, refresh_status)
                    self.root.after(0, self._save_settings)
                except OfflineAiCancelled:
                    self.root.after(0, progress_text.set, "ההורדה נעצרה; אפשר להמשיך מאותה נקודה.")
                except Exception as exc:
                    try:
                        (app_data_dir() / "offline-ai-error.log").write_text(
                            traceback.format_exc(), encoding="utf-8",
                        )
                    except OSError:
                        pass
                    self.root.after(0, progress_text.set, f"הפעולה נכשלה: {exc}")

            self.offline_ai_thread = threading.Thread(
                target=worker, name=f"duk-ai-install-{package}", daemon=True,
            )
            self.offline_ai_thread.start()

        def cancel_install() -> None:
            self.offline_ai_cancel.set()
            progress_text.set("עוצר...")

        def delete_models() -> None:
            if not messagebox.askyesno(
                APP_NAME,
                "למחוק את מנוע ה-AI ואת המודלים?\nכללי OCR שכבר נלמדו יישארו.",
                parent=dialog, icon="warning",
            ):
                return
            self.offline_ai_cancel.set()
            self.offline_ai.delete_component("all")
            self.ai_enabled = False
            enabled_var.set(False)
            progress_value.set(0)
            progress_text.set("המודלים נמחקו")
            refresh_status()

        actions = tk.Frame(dialog, bg="#E7D4AB")
        actions.pack(fill="x", padx=18, pady=12)
        for label, command, color in (
            ("התקנת תיקון טקסט", lambda: install("text"), "#278552"),
            ("התקנת קריאת תמונה", lambda: install("vision"), "#5A3518"),
            ("עצירת הורדה", cancel_install, "#A66A16"),
            ("מחיקת מודלים", delete_models, "#8A3B2C"),
        ):
            tk.Button(
                actions, text=label, command=command, bg=color, fg="white",
                relief="flat", font=("Segoe UI", 10, "bold"), padx=14, pady=8,
            ).pack(side="right", padx=4)

        def close_dialog(save: bool = False) -> None:
            if save:
                self.ai_enabled = bool(enabled_var.get())
                self.ai_auto_review = bool(auto_var.get())
                self.ai_vision_fallback = bool(vision_var.get())
                try:
                    self.ai_confidence_threshold = max(
                        35.0, min(95.0, float(threshold_var.get()))
                    )
                except (TypeError, ValueError):
                    self.ai_confidence_threshold = 72.0
                self._save_settings()
            self.offline_ai_dialog = None
            dialog.destroy()
            if save and self.pdf_path and self.rows:
                self._start_offline_ai_review(self.pdf_path, self.rows)

        footer = tk.Frame(dialog, bg="#E7D4AB")
        footer.pack(fill="x", padx=18, pady=(0, 12))
        tk.Button(
            footer, text="שמירה וסגירה", command=lambda: close_dialog(True),
            bg="#5A3518", fg="white", relief="flat", font=("Segoe UI", 10, "bold"),
            padx=22, pady=9,
        ).pack(side="right")
        tk.Button(
            footer, text="סגירה", command=close_dialog, bg="#F1E2C4", fg="#5A3518",
            relief="flat", font=("Segoe UI", 10, "bold"), padx=18, pady=9,
        ).pack(side="left")
        dialog.protocol("WM_DELETE_WINDOW", close_dialog)
        refresh_status()

    def _refresh_rows_after_learning_change(self) -> None:
        if not self.rows:
            return
        apply_learned_rules_to_rows(self.rows)
        self._update_issue_filter_options()
        self._refresh_result_rows()
        selection = self.tree.selection()
        if selection:
            self.load_selected()

    def _queue_ai_correction_analysis(
        self,
        row: ReportRow,
        items: list[tuple[str, str, str, str]],
        image_bytes: bytes,
    ) -> None:
        if not items:
            return
        image_path = ""
        if image_bytes:
            try:
                image_dir = app_data_dir() / "offline-ai" / "learning-images"
                image_dir.mkdir(parents=True, exist_ok=True)
                digest = hashlib.sha256(
                    image_bytes + "|".join("\0".join(item) for item in items).encode("utf-8")
                ).hexdigest()[:20]
                target = image_dir / f"correction-{digest}.jpg"
                if not target.exists():
                    target.write_bytes(image_bytes)
                image_path = str(target)
            except OSError:
                image_path = ""
        for _field, scope, wrong, correct in items:
            annotate_learned_rule(
                scope, wrong, correct,
                {"ai_image": image_path, "ai_analyzed": "false"},
            )
            self._enqueue_approved_rule_for_sync(
                scope, wrong, correct, row.report_kind, _field,
            )

        manager = self.offline_ai
        if (
            manager is None or not self.ai_enabled or not manager.runtime_ready()
            or (not manager.text_ready() and not manager.vision_ready())
        ):
            self.status.set(
                "התיקון נשמר ויחול להבא. לאחר התקנת AI אופליין הוא גם ינתח את סוג הטעות."
            )
            return
        row_context = self._offline_ai_row_payload(row)

        def worker() -> None:
            analyzed = 0
            for field, scope, wrong, correct in items:
                try:
                    result = manager.analyze_correction(
                        field=field,
                        scope=scope,
                        wrong=wrong,
                        correct=correct,
                        report_kind=row.report_kind,
                        row_context=row_context,
                        image_bytes=image_bytes or None,
                    )
                    try:
                        confidence = max(
                            0.0, min(1.0, float(result.get("confidence", 0) or 0))
                        )
                    except (TypeError, ValueError):
                        confidence = 0.0
                    apply_mode = str(result.get("apply_mode", "exact")).strip().lower()
                    if apply_mode != "similar" or confidence < 0.90:
                        apply_mode = "exact"
                    try:
                        minimum_similarity = max(
                            0.86,
                            min(0.99, float(result.get("minimum_similarity", 0.92) or 0.92)),
                        )
                    except (TypeError, ValueError):
                        minimum_similarity = 0.92
                    annotate_learned_rule(
                        scope, wrong, correct,
                        {
                            "ai_analyzed": "true",
                            "ai_reason": clean_hebrew_text(str(result.get("reason", ""))),
                            "ai_error_type": clean_hebrew_text(
                                str(result.get("error_type", ""))
                            ),
                            "ai_apply_mode": apply_mode,
                            "ai_confidence": confidence,
                            "minimum_similarity": minimum_similarity,
                            "ai_image": image_path,
                        },
                    )
                    analyzed += 1
                except Exception:
                    try:
                        (app_data_dir() / "offline-ai-learning-error.log").write_text(
                            traceback.format_exc(), encoding="utf-8",
                        )
                    except OSError:
                        pass
            if analyzed:
                self.root.after(
                    0, self.status.set,
                    f"ה-AI ניתח {analyzed} תיקוני OCR ושמר אותם לפעמים הבאות",
                )

        threading.Thread(target=worker, name="duk-ai-learn-correction", daemon=True).start()

    @staticmethod
    def _rule_sync_key() -> str:
        try:
            payload = json.loads(rule_sync_secret_path().read_text(encoding="utf-8"))
        except (OSError, ValueError, TypeError):
            return ""
        key = str(payload.get("sync_key", "")) if isinstance(payload, dict) else ""
        return key if 32 <= len(key) <= 256 else ""

    def _enqueue_approved_rule_for_sync(
        self, scope: str, wrong: str, correct: str, report_kind: str, field: str,
    ) -> None:
        if CUSTOMER_EDITION or GIGAPDF_OCR_EDITION:
            return
        clean_rule = {
            "scope": scope,
            "wrong": clean_hebrew_text(wrong)[:180],
            "correct": clean_hebrew_text(correct)[:180],
            "report_kind": clean_hebrew_text(report_kind)[:80],
            "field": clean_hebrew_text(field)[:40],
            "approved_at": datetime.now().isoformat(timespec="seconds"),
            "source_version": APP_VERSION,
        }
        if (
            clean_rule["scope"] not in {"word", "start", "description"}
            or not clean_rule["wrong"] or not clean_rule["correct"]
        ):
            return
        identity = hashlib.sha256(
            "\0".join(
                str(clean_rule[name])
                for name in ("scope", "wrong", "correct", "report_kind")
            ).encode("utf-8")
        ).hexdigest()
        clean_rule["id"] = identity
        with RULE_SYNC_FILE_LOCK:
            try:
                payload = json.loads(rule_sync_pending_path().read_text(encoding="utf-8"))
                pending = payload.get("rules", []) if isinstance(payload, dict) else []
            except (OSError, ValueError, TypeError):
                pending = []
            values = {
                str(item.get("id", "")): item
                for item in pending if isinstance(item, dict) and item.get("id")
            }
            values[identity] = clean_rule
            temporary = rule_sync_pending_path().with_suffix(".tmp")
            temporary.write_text(
                json.dumps({"version": 1, "rules": list(values.values())}, ensure_ascii=False, indent=2),
                encoding="utf-8",
            )
            temporary.replace(rule_sync_pending_path())
        self._schedule_ocr_rule_sync(800)

    def _schedule_ocr_rule_sync(self, delay_ms: int = 6 * 60 * 60 * 1000) -> None:
        if GIGAPDF_OCR_EDITION:
            return
        if self.ocr_rule_sync_job:
            try:
                self.root.after_cancel(self.ocr_rule_sync_job)
            except tk.TclError:
                pass
        self.ocr_rule_sync_job = self.root.after(max(250, delay_ms), self._ocr_rule_sync_tick)

    def _ocr_rule_sync_tick(self) -> None:
        self.ocr_rule_sync_job = None
        if self.ocr_rule_sync_running:
            self._schedule_ocr_rule_sync(60_000)
            return
        self.ocr_rule_sync_running = True

        def worker() -> None:
            try:
                if CUSTOMER_EDITION:
                    self._download_approved_ocr_rules()
                else:
                    self._submit_approved_ocr_rules()
            finally:
                self.ocr_rule_sync_running = False
                try:
                    self.root.after(0, self._schedule_ocr_rule_sync)
                except (RuntimeError, tk.TclError):
                    pass

        threading.Thread(target=worker, name="duk-ocr-rule-sync", daemon=True).start()

    def _submit_approved_ocr_rules(self) -> None:
        sync_key = self._rule_sync_key()
        if not sync_key:
            return
        with RULE_SYNC_FILE_LOCK:
            try:
                payload = json.loads(rule_sync_pending_path().read_text(encoding="utf-8"))
                pending = payload.get("rules", []) if isinstance(payload, dict) else []
            except (OSError, ValueError, TypeError):
                pending = []
        pending = [item for item in pending if isinstance(item, dict)][:500]
        if not pending:
            return
        request_object = urllib.request.Request(
            OCR_RULES_SUBMIT_URL,
            data=json.dumps({"rules": pending}, ensure_ascii=False).encode("utf-8"),
            headers={
                "Accept": "application/json",
                "Content-Type": "application/json; charset=utf-8",
                "User-Agent": f"DukReportReaderPrivate/{APP_VERSION}",
                "X-ReportReader-Rule-Key": sync_key,
            },
            method="POST",
        )
        try:
            with urllib.request.urlopen(request_object, timeout=25) as response:
                accepted = response.status == 200
        except (OSError, urllib.error.URLError):
            accepted = False
        if not accepted:
            return
        sent_ids = {str(item.get("id", "")) for item in pending}
        with RULE_SYNC_FILE_LOCK:
            try:
                latest = json.loads(rule_sync_pending_path().read_text(encoding="utf-8"))
                remaining = latest.get("rules", []) if isinstance(latest, dict) else []
            except (OSError, ValueError, TypeError):
                remaining = []
            remaining = [
                item for item in remaining
                if isinstance(item, dict) and str(item.get("id", "")) not in sent_ids
            ]
            temporary = rule_sync_pending_path().with_suffix(".tmp")
            temporary.write_text(
                json.dumps({"version": 1, "rules": remaining}, ensure_ascii=False, indent=2),
                encoding="utf-8",
            )
            temporary.replace(rule_sync_pending_path())

    def _download_approved_ocr_rules(self) -> None:
        target = server_learned_corrections_path()
        if target.exists() and time.time() - target.stat().st_mtime < OCR_RULES_SYNC_INTERVAL_SECONDS:
            return
        headers = {
            "Accept": "application/json",
            "User-Agent": f"DukReportReaderClients/{APP_VERSION}",
        }
        token = str(self.customer_auth.get("token", ""))
        if token:
            headers["Authorization"] = "Bearer " + token
        request_object = urllib.request.Request(OCR_RULES_PUBLIC_URL, headers=headers, method="GET")
        try:
            with urllib.request.urlopen(request_object, timeout=25) as response:
                raw = response.read(2 * 1024 * 1024)
            payload = json.loads(raw.decode("utf-8"))
        except (OSError, UnicodeError, ValueError, urllib.error.URLError):
            return
        rules = payload.get("rules", []) if isinstance(payload, dict) else []
        if not isinstance(rules, list) or len(rules) > 5000:
            return
        sanitized: list[dict[str, object]] = []
        for item in rules:
            if not isinstance(item, dict):
                continue
            scope = str(item.get("scope", ""))
            wrong = clean_hebrew_text(str(item.get("wrong", "")))[:180]
            correct = clean_hebrew_text(str(item.get("correct", "")))[:180]
            if scope not in {"word", "start", "description"} or not wrong or not correct:
                continue
            sanitized.append({
                "scope": scope, "wrong": wrong, "correct": correct,
                "report_kind": clean_hebrew_text(str(item.get("report_kind", "")))[:80],
                "field": clean_hebrew_text(str(item.get("field", "")))[:40],
                "created": str(item.get("published_at", ""))[:50],
                "source": "server-approved",
            })
        temporary = target.with_suffix(".tmp")
        temporary.write_text(
            json.dumps({"version": int(payload.get("version", 1) or 1), "rules": sanitized}, ensure_ascii=False, indent=2),
            encoding="utf-8",
        )
        temporary.replace(target)
        if self.rows:
            try:
                self.root.after(0, self._refresh_rows_after_learning_change)
            except (RuntimeError, tk.TclError):
                pass

    def open_row_ocr_correction(self, index: int) -> None:
        if not self.pdf_path or not (0 <= index < len(self.rows)):
            return
        row = self.rows[index]
        ensure_ocr_baseline(row)
        dialog = tk.Toplevel(self.root)
        dialog.title("תיקון OCR וזיהוי מחדש")
        fit_window_to_work_area(dialog, 940, 740, 720, 540)
        dialog.transient(self.root)
        dialog.grab_set()
        dialog.configure(bg="#E7D4AB")
        tk.Label(
            dialog, text="תיקון OCR וזיהוי מחדש", bg="#5A3518", fg="white",
            font=("Segoe UI", 17, "bold"), pady=14,
        ).pack(fill="x")
        tk.Label(
            dialog,
            text=f"עמוד {row.page}  |  שורה {row.line}\n"
                 "בעמודה האמצעית מופיע הזיהוי הגולמי. שנה רק את הטעות בעמודת התיקון.",
            bg="#FFF9EC", fg="#74471F", font=("Segoe UI", 10),
            justify="right", anchor="e", padx=16, pady=11,
        ).pack(fill="x", padx=18, pady=(14, 8))

        preview_card = tk.Frame(dialog, bg="#FFF9EC", padx=10, pady=8)
        preview_card.pack(fill="x", padx=18, pady=(0, 8))
        tk.Label(
            preview_card, text="תמונת השורה המקורית — גלול לצדדים כדי לראות את כולה",
            bg="#FFF9EC", fg="#5A3518", font=("Segoe UI", 10, "bold"), anchor="e",
        ).pack(fill="x", pady=(0, 5))
        preview_canvas = tk.Canvas(
            preview_card, width=875, height=145, bg="white",
            highlightthickness=1, highlightbackground="#CDB68E",
        )
        preview_scroll = ttk.Scrollbar(
            preview_card, orient="horizontal", command=preview_canvas.xview,
        )
        preview_canvas.configure(xscrollcommand=preview_scroll.set)
        preview_canvas.pack(fill="x")
        preview_scroll.pack(fill="x", pady=(4, 0))
        row_ai_image_bytes = b""
        try:
            row_image = render_report_row_crop(self.pdf_path, row)
            ai_buffer = io.BytesIO()
            row_image.save(ai_buffer, "JPEG", quality=90, optimize=True)
            row_ai_image_bytes = ai_buffer.getvalue()
            if row_image.height > 135:
                scale = 135 / row_image.height
                row_image = row_image.resize(
                    (max(1, int(round(row_image.width * scale))), 135),
                    Image.Resampling.LANCZOS,
                )
            row_preview_photo = ImageTk.PhotoImage(row_image)
            preview_canvas.create_image(4, 4, image=row_preview_photo, anchor="nw")
            preview_canvas.image = row_preview_photo
            preview_canvas.configure(
                scrollregion=(0, 0, row_image.width + 8, max(145, row_image.height + 8))
            )
            # Start at the right side, where page/start/line columns are located.
            preview_canvas.xview_moveto(1.0)
        except Exception as exc:
            preview_canvas.create_text(
                860, 70, text=f"לא ניתן להציג את תמונת השורה: {exc}",
                anchor="e", fill="#8A3B2C", font=("Segoe UI", 10),
            )

        field_specs = [
            ("start", "המתחיל", "start"),
            ("first_word", "תחילת השורה", "word"),
            ("problem_word", "מילה בעייתית", "word"),
            ("problem_type", "סוג הבעיה", "description"),
            ("description", "תיאור הבעיה", "description"),
        ]
        raw_values = {
            "start": row.ocr_start,
            "first_word": row.ocr_first_word,
            "problem_word": row.ocr_problem_word,
            "problem_type": row.ocr_problem_type,
            "description": row.ocr_description,
        }
        correction_vars: dict[str, tk.StringVar] = {}
        correction_entries: dict[str, NativeRtlEntry] = {}
        table = tk.Frame(dialog, bg="#FFF9EC", padx=14, pady=12)
        table.pack(fill="both", expand=True, padx=18)
        for column, heading in enumerate(("שדה", "מה ה־OCR זיהה", "התיקון שלך")):
            tk.Label(
                table, text=heading, bg="#F1E2C4", fg="#5A3518",
                font=("Segoe UI", 10, "bold"), pady=7,
            ).grid(row=0, column=column, sticky="ew", padx=3, pady=(0, 5))
            table.columnconfigure(column, weight=(2 if column else 1))
        for grid_row, (name, label, _scope) in enumerate(field_specs, start=1):
            raw = raw_values[name]
            current = getattr(row, name)
            if name in {"start", "first_word", "problem_word"}:
                raw = normalize_divine_names_for_display(raw)
                current = normalize_divine_names_for_display(current)
            correction_vars[name] = tk.StringVar(value=current)
            tk.Label(
                table, text=label, bg="#FFF9EC", fg="#5A3518",
                font=("Segoe UI", 10, "bold"), anchor="e", padx=7,
            ).grid(row=grid_row, column=0, sticky="ew", padx=3, pady=5)
            tk.Label(
                table, text=raw or "—", bg="#FFFDF7", fg="#866A49",
                font=("Segoe UI", 10), anchor="e", padx=8, relief="solid", bd=1,
            ).grid(row=grid_row, column=1, sticky="nsew", padx=3, pady=5)
            correction_entry = NativeRtlEntry(
                table, textvariable=correction_vars[name],
            )
            correction_entry.grid(
                row=grid_row, column=2, sticky="nsew", padx=3, pady=5,
            )
            correction_entries[name] = correction_entry

        def close_dialog() -> None:
            try:
                dialog.grab_release()
            except tk.TclError:
                pass
            dialog.destroy()

        def save_and_rerecognize() -> None:
            corrected: dict[str, str] = {}
            for name, _label, _scope in field_specs:
                value = clean_hebrew_text(correction_entries[name].get())
                if name in {"start", "first_word", "problem_word"}:
                    value = restore_divine_names_from_display(value)
                if name == "problem_type":
                    value = normalize_problem_type(value)
                elif name == "description":
                    value = normalize_report_description(value, row.report_kind)
                corrected[name] = value
            changed = {
                name for name, _label, _scope in field_specs
                if _correction_key(raw_values[name]) != _correction_key(corrected[name])
            }
            dialog.configure(cursor="wait")
            self.status.set("מריץ זיהוי מחדש על השורה...")
            self.root.update_idletasks()
            try:
                reread, visual_candidates = rerecognize_report_row(self.pdf_path, row)
                learned_examples: list[str] = []
                analysis_items: list[tuple[str, str, str, str]] = []
                for name, _label, scope in field_specs:
                    new_raw = clean_hebrew_text(str(reread.get(name, "")))
                    old_raw = raw_values[name]
                    if name in changed and corrected[name]:
                        for wrong in {old_raw, new_raw}:
                            if wrong and _correction_key(wrong) != _correction_key(corrected[name]):
                                add_learned_rule(
                                    scope, wrong, corrected[name],
                                    {
                                        "field": name,
                                        "report_kind": row.report_kind,
                                        "source": "user-approved",
                                        "ai_analyzed": "false",
                                    },
                                )
                                analysis_items.append((name, scope, wrong, corrected[name]))
                        manual_name = f"manual_{name}"
                        setattr(row, manual_name, corrected[name])
                        learned_examples.append(f"{old_raw} ← {corrected[name]}")
                    baseline_name = f"ocr_{name}"
                    if new_raw:
                        setattr(row, baseline_name, new_raw)
                try:
                    row.confidence = float(reread.get("confidence", row.confidence))
                except (TypeError, ValueError):
                    pass
                apply_learned_rules_to_rows([row])
                write_ocr_cache(self.pdf_path, self.rows)
                self._refresh_rows_after_learning_change()
                close_dialog()
                if learned_examples:
                    self.status.set(
                        "השורה זוהתה מחדש וה־OCR למד: " + ", ".join(learned_examples)
                    )
                    self._queue_ai_correction_analysis(
                        row, analysis_items, row_ai_image_bytes,
                    )
                else:
                    self.status.set("השורה זוהתה מחדש; לא הוזן שינוי ללימוד")
            except Exception as exc:
                dialog.configure(cursor="")
                messagebox.showerror(APP_NAME, f"הזיהוי מחדש נכשל:\n{exc}", parent=dialog)

        actions = tk.Frame(dialog, bg="#E7D4AB")
        actions.pack(fill="x", padx=18, pady=14)
        tk.Button(
            actions, text="שמירה, לימוד וזיהוי מחדש", command=save_and_rerecognize,
            bg="#278552", fg="white", activebackground="#1F6B42", activeforeground="white",
            relief="flat", font=("Segoe UI", 11, "bold"), padx=24, pady=9,
        ).pack(side="right", padx=5)
        tk.Button(
            actions, text="ביטול", command=close_dialog,
            bg="#F1E2C4", fg="#5A3518", relief="flat", font=("Segoe UI", 10, "bold"),
            padx=20, pady=9,
        ).pack(side="left", padx=5)
        dialog.protocol("WM_DELETE_WINDOW", close_dialog)
        if correction_entries:
            dialog.after(100, correction_entries[field_specs[0][0]].focus_set)

    def open_image_training(self, row_index: int | None = None) -> None:
        if self.image_training_open:
            return
        self.image_training_open = True
        dialog = tk.Toplevel(self.root)
        dialog.title("אימון OCR מתמונה")
        dialog.geometry("920x800")
        dialog.minsize(840, 740)
        dialog.transient(self.root)
        dialog.grab_set()
        dialog.configure(bg="#E7D4AB")
        try:
            dialog.iconbitmap(default=str(resource_path("app.ico")))
        except Exception:
            pass

        tk.Label(
            dialog, text="אימון זיהוי מתמונה", bg="#5A3518", fg="white",
            font=("Segoe UI", 17, "bold"), pady=14,
        ).pack(fill="x")
        tk.Label(
            dialog,
            text="בחר תמונה חתוכה שמכילה מילה אחת בלבד. התוכנה תשמור את צורת האותיות\n"
                 "ותשתמש בתיקון רק כאשר תמונה עתידית דומה מספיק לדוגמה.",
            bg="#FFF9EC", fg="#74471F", font=("Segoe UI", 10),
            justify="right", anchor="e", padx=16, pady=10,
        ).pack(fill="x", padx=18, pady=(14, 8))

        scope_labels = {
            "מילה ראשונה / בעייתית": "word",
            "המתחיל": "start",
            "תיאור הבעיה": "description",
        }
        scope_var = tk.StringVar(value="מילה ראשונה / בעייתית")
        recognized_var = tk.StringVar()
        correct_var = tk.StringVar()
        file_var = tk.StringVar(value="לא נבחרה תמונה")
        sample_count_var = tk.StringVar()
        selected_image: Image.Image | None = None
        selected_source = ""
        detected_word_count = 0
        preview_photo: ImageTk.PhotoImage | None = None

        selection_frame = tk.Frame(dialog, bg="#FFF9EC", padx=12, pady=10)
        selection_frame.pack(fill="x", padx=18)
        tk.Label(
            selection_frame, text="סוג השדה", bg="#FFF9EC", fg="#5A3518",
            font=("Segoe UI", 10, "bold"),
        ).pack(side="right", padx=(8, 4))
        ttk.Combobox(
            selection_frame, textvariable=scope_var, values=list(scope_labels),
            state="readonly", width=23, justify="right",
        ).pack(side="right", padx=4)
        tk.Label(
            selection_frame, textvariable=file_var, bg="#FFF9EC", fg="#866A49",
            font=("Segoe UI", 9), anchor="e",
        ).pack(side="right", fill="x", expand=True, padx=12)

        preview_label = tk.Label(
            dialog, text="בחר תמונת PNG, JPG, BMP או TIFF", bg="white", fg="#866A49",
            font=("Segoe UI", 11), height=7, relief="solid", bd=1,
        )
        preview_label.pack(fill="x", padx=18, pady=8)

        fields = tk.Frame(dialog, bg="#FFF9EC", padx=12, pady=10)
        fields.pack(fill="x", padx=18)
        for title, variable in (("הזיהוי הנוכחי", recognized_var), ("המילה הנכונה", correct_var)):
            field = tk.Frame(fields, bg="#FFF9EC")
            field.pack(side="right", fill="x", expand=True, padx=7)
            tk.Label(
                field, text=title, bg="#FFF9EC", fg="#5A3518",
                font=("Segoe UI", 10, "bold"), anchor="e",
            ).pack(fill="x")
            ttk.Entry(field, textvariable=variable, justify="right").pack(fill="x", pady=(4, 0))

        def process_image(original: Image.Image, source_name: str, ocr_path: Path | None = None) -> None:
            nonlocal selected_image, selected_source, detected_word_count, preview_photo
            temporary_path: Path | None = None
            try:
                original = original.convert("RGB")
                if ocr_path is None:
                    descriptor, raw_path = tempfile.mkstemp(prefix="duk-ocr-clipboard-", suffix=".png")
                    os.close(descriptor)
                    temporary_path = Path(raw_path)
                    original.save(temporary_path, "PNG")
                    ocr_path = temporary_path
                shown = original.copy()
                shown.thumbnail((710, 125), Image.Resampling.LANCZOS)
                preview_photo = ImageTk.PhotoImage(shown)
                preview_label.configure(image=preview_photo, text="", height=125)
                tesseract = locate_tesseract()
                validate_tesseract(tesseract)
                words = run_tesseract_tsv(
                    tesseract, ocr_path, language="heb", psm=8,
                    apply_visual_training=False,
                )
                detected_word_count = len(words)
                recognized = join_rtl(words)
                recognized_var.set(normalize_divine_names_for_display(recognized))
                correct_var.set(normalize_divine_names_for_display(recognized))
                if len(words) == 1:
                    word = words[0]
                    padding = max(2, int(round(word.h * 0.10)))
                    selected_image = original.crop((
                        max(0, word.x - padding), max(0, word.y - padding),
                        min(original.width, word.x + word.w + padding),
                        min(original.height, word.y + word.h + padding),
                    ))
                else:
                    selected_image = None
                selected_source = source_name
                file_var.set(
                    f"{selected_source} — זוהו {detected_word_count} מילים"
                    if detected_word_count != 1 else f"{selected_source} — מילה אחת, מוכן לשמירה"
                )
            except Exception as exc:
                selected_image = None
                detected_word_count = 0
                messagebox.showerror(APP_NAME, f"לא ניתן לקרוא את התמונה:\n{exc}", parent=dialog)
            finally:
                if temporary_path is not None:
                    try:
                        temporary_path.unlink()
                    except OSError:
                        pass

        def choose_image() -> None:
            path_value = filedialog.askopenfilename(
                title="בחירת תמונה לאימון OCR",
                filetypes=[
                    ("קבצי תמונה", "*.png *.jpg *.jpeg *.bmp *.tif *.tiff"),
                    ("כל הקבצים", "*.*"),
                ],
                parent=dialog,
            )
            if not path_value:
                return
            try:
                original = Image.open(path_value).convert("RGB")
                process_image(original, Path(path_value).name, Path(path_value))
            except Exception as exc:
                messagebox.showerror(APP_NAME, f"לא ניתן לקרוא את התמונה:\n{exc}", parent=dialog)

        def paste_image() -> None:
            try:
                clipboard = ImageGrab.grabclipboard()
                if isinstance(clipboard, Image.Image):
                    process_image(clipboard, "תמונה מלוח ההעתקה")
                    return
                if isinstance(clipboard, list):
                    for candidate in clipboard:
                        path = Path(str(candidate))
                        if path.is_file() and path.suffix.lower() in {
                            ".png", ".jpg", ".jpeg", ".bmp", ".tif", ".tiff",
                        }:
                            with Image.open(path) as copied_file:
                                process_image(copied_file.copy(), path.name, path)
                            return
                messagebox.showinfo(
                    APP_NAME, "לא נמצאה תמונה בלוח ההעתקה. העתק תמונה או צילום מסך ונסה שוב.",
                    parent=dialog,
                )
            except Exception as exc:
                messagebox.showerror(APP_NAME, f"לא ניתן להדביק את התמונה:\n{exc}", parent=dialog)

        def choose_from_report_row() -> None:
            selection = self.tree.selection()
            if row_index is not None:
                selected_index = row_index
            elif selection:
                selected_index = int(selection[0])
            else:
                messagebox.showinfo(APP_NAME, "בחר תחילה שורה מהדוח.", parent=dialog)
                return
            if not self.pdf_path or not (0 <= selected_index < len(self.rows)):
                messagebox.showinfo(APP_NAME, "אין כרגע שורת דוח זמינה לאימון.", parent=dialog)
                return
            row = self.rows[selected_index]
            try:
                document = pdfium.PdfDocument(str(self.pdf_path))
                try:
                    page = document[row.source_pdf_page - 1]
                    try:
                        bitmap = page.render(scale=OCR_DPI / 72.0)
                        page_image = bitmap.to_pil().convert("RGB")
                    finally:
                        page.close()
                finally:
                    document.close()
                report_kind = row.report_kind if row.report_kind in TABLE_PROFILES else ""
                gray_page = np.asarray(page_image.convert("L"))
                if not report_kind:
                    report_kind = detect_report_kind(gray_page)
                xs, _ys = locate_table(gray_page, report_kind)
                bounds = table_column_bounds(xs, report_kind)
                scope = scope_labels[scope_var.get()]
                column_bounds = {
                    "description": (bounds["description"][0] + 4, bounds["description"][1] - 4),
                    "word": (bounds["need"][0] + 4, bounds["need"][1] - 4),
                    "start": (
                        bounds["start"][0] + 4,
                        bounds["start"][1] - 4,
                    ),
                }
                if scope == "start" and report_kind == "eyetech_regular":
                    raise ValueError("בדוח הזה המתחיל נמצא בכותרת. תקן אותו בחלון תיקון השורה.")
                left, right = column_bounds[scope]
                top = max(0, int(round(row.row_top * page_image.height)) + 3)
                bottom = min(page_image.height, int(round(row.row_bottom * page_image.height)) - 3)
                if right - left < 10 or bottom - top < 10:
                    raise ValueError("לא ניתן לאתר את התא של השורה המסומנת.")
                cell_image = page_image.crop((left, top, right, bottom))
            except Exception as exc:
                messagebox.showerror(APP_NAME, f"לא ניתן לקחת את התמונה מהדוח:\n{exc}", parent=dialog)
                return

            crop_dialog = tk.Toplevel(dialog)
            crop_dialog.title("סימון המילה מתוך שורת הדוח")
            crop_dialog.transient(dialog)
            crop_dialog.grab_set()
            crop_dialog.configure(bg="#E7D4AB")
            tk.Label(
                crop_dialog, text="גרור מלבן סביב מילה אחת ולחץ אישור",
                bg="#5A3518", fg="white", font=("Segoe UI", 13, "bold"), pady=11,
            ).pack(fill="x")
            maximum_width = 1050
            maximum_height = 360
            scale = min(maximum_width / cell_image.width, maximum_height / cell_image.height, 2.5)
            display_size = (
                max(1, int(round(cell_image.width * scale))),
                max(1, int(round(cell_image.height * scale))),
            )
            displayed = cell_image.resize(display_size, Image.Resampling.LANCZOS)
            crop_photo = ImageTk.PhotoImage(displayed)
            crop_canvas = tk.Canvas(
                crop_dialog, width=display_size[0], height=display_size[1],
                bg="white", highlightthickness=1, highlightbackground="#CDB68E",
                cursor="crosshair",
            )
            crop_canvas.pack(padx=14, pady=14)
            crop_canvas.create_image(0, 0, image=crop_photo, anchor="nw")
            crop_start: tuple[int, int] | None = None
            crop_bounds: tuple[int, int, int, int] | None = None
            crop_rectangle: int | None = None

            def crop_press(event) -> None:
                nonlocal crop_start, crop_bounds, crop_rectangle
                crop_start = (max(0, min(display_size[0], event.x)), max(0, min(display_size[1], event.y)))
                crop_bounds = None
                if crop_rectangle is not None:
                    crop_canvas.delete(crop_rectangle)
                crop_rectangle = crop_canvas.create_rectangle(
                    crop_start[0], crop_start[1], crop_start[0], crop_start[1],
                    outline="#E3A600", width=3,
                )

            def crop_drag(event) -> None:
                nonlocal crop_bounds
                if crop_start is None or crop_rectangle is None:
                    return
                x = max(0, min(display_size[0], event.x))
                y = max(0, min(display_size[1], event.y))
                crop_canvas.coords(crop_rectangle, crop_start[0], crop_start[1], x, y)
                crop_bounds = (
                    min(crop_start[0], x), min(crop_start[1], y),
                    max(crop_start[0], x), max(crop_start[1], y),
                )

            def close_crop() -> None:
                try:
                    crop_dialog.grab_release()
                except tk.TclError:
                    pass
                crop_dialog.destroy()
                dialog.grab_set()

            def accept_crop() -> None:
                if crop_bounds is None or crop_bounds[2] - crop_bounds[0] < 6 or crop_bounds[3] - crop_bounds[1] < 6:
                    messagebox.showinfo(APP_NAME, "סמן מלבן ברור סביב מילה אחת.", parent=crop_dialog)
                    return
                original_bounds = tuple(int(round(value / scale)) for value in crop_bounds)
                word_image = cell_image.crop(original_bounds)
                close_crop()
                process_image(
                    word_image,
                    f"עמוד {row.page}, שורה {row.line}, {scope_var.get()}",
                )

            crop_canvas.bind("<ButtonPress-1>", crop_press)
            crop_canvas.bind("<B1-Motion>", crop_drag)
            crop_canvas.bind("<ButtonRelease-1>", crop_drag)
            crop_buttons = tk.Frame(crop_dialog, bg="#E7D4AB")
            crop_buttons.pack(fill="x", padx=14, pady=(0, 12))
            tk.Button(
                crop_buttons, text="אישור", command=accept_crop,
                bg="#278552", fg="white", relief="flat", font=("Segoe UI", 10, "bold"),
                padx=22, pady=8,
            ).pack(side="right", padx=4)
            tk.Button(
                crop_buttons, text="ביטול", command=close_crop,
                bg="#F1E2C4", fg="#5A3518", relief="flat", font=("Segoe UI", 10, "bold"),
                padx=22, pady=8,
            ).pack(side="left", padx=4)
            crop_dialog.protocol("WM_DELETE_WINDOW", close_crop)

        tk.Button(
            selection_frame, text="בחירת תמונה", command=choose_image,
            bg="#A66A16", fg="white", activebackground="#8C5410",
            activeforeground="white", relief="flat", font=("Segoe UI", 10, "bold"),
            padx=16, pady=7,
        ).pack(side="left", padx=4)
        tk.Button(
            selection_frame, text="הדבקה מהלוח", command=paste_image,
            bg="#F1E2C4", fg="#5A3518", activebackground="#E5CF9F",
            relief="flat", font=("Segoe UI", 10, "bold"), padx=16, pady=7,
        ).pack(side="left", padx=4)
        tk.Button(
            selection_frame, text="מהשורה בדוח", command=choose_from_report_row,
            bg="#F1E2C4", fg="#5A3518", activebackground="#E5CF9F",
            relief="flat", font=("Segoe UI", 10, "bold"), padx=14, pady=7,
        ).pack(side="left", padx=4)

        samples_frame = tk.Frame(dialog, bg="#FFF9EC", padx=10, pady=8)
        samples_frame.pack(fill="both", expand=True, padx=18, pady=(10, 0))
        tk.Label(
            samples_frame, textvariable=sample_count_var, bg="#FFF9EC", fg="#5A3518",
            font=("Segoe UI", 10, "bold"), anchor="e",
        ).pack(fill="x", pady=(0, 5))
        samples_tree = ttk.Treeview(
            samples_frame, columns=("scope", "recognized", "correct", "created"),
            show="headings", selectmode="browse", height=5,
        )
        for column, heading, width in (
            ("scope", "חל על", 170), ("recognized", "זוהה", 145),
            ("correct", "תיקון", 145), ("created", "נשמר", 165),
        ):
            samples_tree.heading(column, text=heading)
            samples_tree.column(column, width=width, anchor="e")
        samples_tree.pack(fill="both", expand=True)

        def refresh_samples() -> None:
            samples_tree.delete(*samples_tree.get_children())
            records = load_image_training_records()
            reverse_labels = {value: key for key, value in scope_labels.items()}
            for record in reversed(records):
                samples_tree.insert("", "end", iid=record["id"], values=(
                    reverse_labels.get(record["scope"], record["scope"]),
                    normalize_divine_names_for_display(record["recognized"]),
                    normalize_divine_names_for_display(record["correct"]),
                    record.get("created", "").replace("T", " "),
                ))
            sample_count_var.set(f"דוגמאות תמונה שנשמרו: {len(records)}")

        def save_sample() -> None:
            if selected_image is None or detected_word_count != 1:
                messagebox.showwarning(
                    APP_NAME, "יש לבחור תמונה חתוכה שבה ה־OCR מזהה מילה אחת בלבד.", parent=dialog,
                )
                return
            recognized = restore_divine_names_from_display(clean_hebrew_text(recognized_var.get()))
            correct = restore_divine_names_from_display(clean_hebrew_text(correct_var.get()))
            if len(_speech_units(correct)) != 1 or " " in correct.strip():
                messagebox.showwarning(APP_NAME, "בתיקון יש להזין מילה אחת בלבד.", parent=dialog)
                return
            scope = scope_labels[scope_var.get()]
            try:
                add_image_training_sample(selected_image, scope, recognized, correct, selected_source)
                if recognized and _correction_key(recognized) != _correction_key(correct):
                    add_learned_rule(scope, recognized, correct)
                self._refresh_rows_after_learning_change()
                refresh_samples()
                self.status.set(f"ה־OCR למד מהתמונה: {recognized} ← {correct}")
                messagebox.showinfo(APP_NAME, "דוגמת התמונה נשמרה ונוספה לאימון.", parent=dialog)
            except (OSError, ValueError) as exc:
                messagebox.showerror(APP_NAME, str(exc), parent=dialog)

        def delete_selected_sample() -> None:
            selection = samples_tree.selection()
            if not selection:
                messagebox.showinfo(APP_NAME, "בחר דוגמה למחיקה.", parent=dialog)
                return
            sample_id = selection[0]
            records = [record for record in load_image_training_records() if record["id"] != sample_id]
            save_image_training_records(records)
            refresh_samples()
            self.status.set("דוגמת אימון התמונה נמחקה")

        def edit_selected_sample(_event=None) -> None:
            selection = samples_tree.selection()
            if not selection:
                messagebox.showinfo(APP_NAME, "בחר דוגמה לעריכה.", parent=dialog)
                return
            sample_id = selection[0]
            records = load_image_training_records()
            record = next((item for item in records if item["id"] == sample_id), None)
            if record is None:
                refresh_samples()
                return
            editor = tk.Toplevel(dialog)
            editor.title("עריכת דוגמת תמונה")
            editor.geometry("520x330")
            editor.resizable(False, False)
            editor.transient(dialog)
            editor.grab_set()
            editor.configure(bg="#E7D4AB")
            tk.Label(
                editor, text="עריכת דוגמה שנלמדה מתמונה", bg="#5A3518", fg="white",
                font=("Segoe UI", 15, "bold"), pady=12,
            ).pack(fill="x")
            reverse_scopes = {value: key for key, value in scope_labels.items()}
            edit_scope = tk.StringVar(value=reverse_scopes.get(record["scope"], record["scope"]))
            edit_recognized = tk.StringVar(
                value=normalize_divine_names_for_display(record["recognized"])
            )
            edit_correct = tk.StringVar(value=normalize_divine_names_for_display(record["correct"]))
            form = tk.Frame(editor, bg="#FFF9EC", padx=18, pady=14)
            form.pack(fill="both", expand=True, padx=16, pady=12)
            for label, variable, is_scope in (
                ("סוג השדה", edit_scope, True),
                ("הזיהוי הנוכחי", edit_recognized, False),
                ("התיקון", edit_correct, False),
            ):
                row_frame = tk.Frame(form, bg="#FFF9EC")
                row_frame.pack(fill="x", pady=5)
                tk.Label(
                    row_frame, text=label, bg="#FFF9EC", fg="#5A3518",
                    font=("Segoe UI", 10, "bold"), width=16, anchor="e",
                ).pack(side="right", padx=(8, 0))
                if is_scope:
                    widget = ttk.Combobox(
                        row_frame, textvariable=variable, values=list(scope_labels),
                        state="readonly", justify="right",
                    )
                else:
                    widget = ttk.Entry(row_frame, textvariable=variable, justify="right")
                widget.pack(side="right", fill="x", expand=True)

            def close_sample_editor() -> None:
                try:
                    editor.grab_release()
                except tk.TclError:
                    pass
                editor.destroy()
                dialog.grab_set()

            def save_sample_edit() -> None:
                new_scope = scope_labels.get(edit_scope.get(), "")
                new_recognized = restore_divine_names_from_display(
                    clean_hebrew_text(edit_recognized.get())
                )
                new_correct = restore_divine_names_from_display(clean_hebrew_text(edit_correct.get()))
                if new_scope not in {"word", "start", "description"} or not new_correct:
                    messagebox.showwarning(APP_NAME, "יש למלא סוג שדה ותיקון.", parent=editor)
                    return
                if len(_speech_units(new_correct)) != 1 or " " in new_correct.strip():
                    messagebox.showwarning(APP_NAME, "בתיקון יש להזין מילה אחת בלבד.", parent=editor)
                    return
                old_scope = record["scope"]
                old_recognized = record["recognized"]
                record["scope"] = new_scope
                record["recognized"] = new_recognized
                record["correct"] = new_correct
                record["created"] = datetime.now().isoformat(timespec="seconds")
                save_image_training_records(records)
                learned_rules = load_learned_rules()
                matching_rule = next((
                    rule for rule in learned_rules
                    if rule["scope"] == old_scope
                    and _correction_key(rule["wrong"]) == _correction_key(old_recognized)
                ), None)
                if matching_rule is not None:
                    matching_rule.update({
                        "scope": new_scope, "wrong": new_recognized, "correct": new_correct,
                        "created": datetime.now().isoformat(timespec="seconds"),
                    })
                    save_learned_rules(learned_rules)
                elif new_recognized and _correction_key(new_recognized) != _correction_key(new_correct):
                    add_learned_rule(new_scope, new_recognized, new_correct)
                self._refresh_rows_after_learning_change()
                close_sample_editor()
                refresh_samples()
                self.status.set("דוגמת אימון התמונה נערכה ונשמרה")

            action_row = tk.Frame(editor, bg="#E7D4AB")
            action_row.pack(fill="x", padx=16, pady=(0, 12))
            tk.Button(
                action_row, text="שמירת השינויים", command=save_sample_edit,
                bg="#278552", fg="white", relief="flat", font=("Segoe UI", 10, "bold"),
                padx=18, pady=8,
            ).pack(side="right", padx=4)
            tk.Button(
                action_row, text="ביטול", command=close_sample_editor,
                bg="#F1E2C4", fg="#5A3518", relief="flat", font=("Segoe UI", 10, "bold"),
                padx=18, pady=8,
            ).pack(side="left", padx=4)
            editor.protocol("WM_DELETE_WINDOW", close_sample_editor)

        def delete_all_samples() -> None:
            records = load_image_training_records()
            if not records or not messagebox.askyesno(
                APP_NAME, "למחוק את כל דוגמאות האימון מתמונות?", icon="warning", parent=dialog,
            ):
                return
            save_image_training_records([])
            refresh_samples()
            self.status.set("כל דוגמאות אימון התמונה נמחקו")

        def close_dialog() -> None:
            self.image_training_open = False
            try:
                dialog.grab_release()
            except tk.TclError:
                pass
            dialog.destroy()

        buttons = tk.Frame(dialog, bg="#E7D4AB")
        buttons.pack(fill="x", padx=18, pady=12)
        for text, command, background in (
            ("שמירת האימון", save_sample, "#278552"),
            ("עריכת המסומנת", edit_selected_sample, "#278552"),
            ("מחיקת הדוגמה המסומנת", delete_selected_sample, "#A66A16"),
            ("מחיקת כולן", delete_all_samples, "#8A3B2C"),
        ):
            tk.Button(
                buttons, text=text, command=command, bg=background, fg="white",
                activebackground=background, activeforeground="white", relief="flat",
                font=("Segoe UI", 10, "bold"), padx=14, pady=8,
            ).pack(side="right", padx=4)
        tk.Button(
            buttons, text="סגירה", command=close_dialog,
            bg="#F1E2C4", fg="#5A3518", activebackground="#E5CF9F",
            relief="flat", font=("Segoe UI", 10, "bold"), padx=18, pady=8,
        ).pack(side="left", padx=4)
        dialog.protocol("WM_DELETE_WINDOW", close_dialog)
        samples_tree.bind("<Double-1>", edit_selected_sample)
        refresh_samples()
        if row_index is not None:
            dialog.after(150, choose_from_report_row)

    def open_learning_manager(self) -> None:
        if self.learning_manager_open:
            return
        self.learning_manager_open = True
        dialog = tk.Toplevel(self.root)
        dialog.title("למידת OCR")
        dialog.geometry("800x610")
        dialog.resizable(False, False)
        dialog.transient(self.root)
        dialog.grab_set()
        dialog.configure(bg="#E7D4AB")
        try:
            dialog.iconbitmap(default=str(resource_path("app.ico")))
        except Exception:
            pass

        tk.Label(
            dialog, text="כללי תיקון שה-OCR למד", bg="#5A3518", fg="white",
            font=("Segoe UI", 17, "bold"), pady=14,
        ).pack(fill="x")
        tk.Label(
            dialog,
            text="הכללים חלים רק על מילה או שדה שלם, ולא משנים חלק מתוך מילה ארוכה.\n"
                 "כדי ללמד כלל חדש: תקן שורה ולחץ 'שמירה ולימוד OCR'.",
            bg="#FFF9EC", fg="#74471F", font=("Segoe UI", 10),
            justify="right", anchor="e", padx=16, pady=12,
        ).pack(fill="x", padx=18, pady=(16, 8))

        table_frame = tk.Frame(dialog, bg="#FFF9EC", padx=10, pady=10)
        table_frame.pack(fill="both", expand=True, padx=18)
        rules_tree = ttk.Treeview(
            table_frame, columns=("scope", "wrong", "correct"),
            show="headings", selectmode="browse", height=9,
        )
        rules_tree.heading("scope", text="חל על")
        rules_tree.heading("wrong", text="זיהוי שגוי")
        rules_tree.heading("correct", text="תיקון")
        rules_tree.column("scope", width=180, anchor="e")
        rules_tree.column("wrong", width=190, anchor="e")
        rules_tree.column("correct", width=190, anchor="e")
        rules_scroll = ttk.Scrollbar(table_frame, orient="vertical", command=rules_tree.yview)
        rules_tree.configure(yscrollcommand=rules_scroll.set)
        rules_scroll.pack(side="left", fill="y")
        rules_tree.pack(fill="both", expand=True)
        scope_labels = {
            "word": "מילה ראשונה / בעייתית",
            "start": "המתחיל",
            "description": "תיאור הבעיה",
        }

        current_rules: list[dict[str, str]] = []
        selected_rule_index: int | None = None
        inline_scope = tk.StringVar(value="מילה ראשונה / בעייתית")
        inline_wrong = tk.StringVar()
        inline_correct = tk.StringVar()
        reverse_scope_labels = {label: scope for scope, label in scope_labels.items()}
        edit_panel = tk.Frame(dialog, bg="#FFF9EC", padx=10, pady=9)
        edit_panel.pack(fill="x", padx=18, pady=(8, 0))
        for label, variable, is_scope in (
            ("סוג השדה", inline_scope, True),
            ("זיהוי שגוי", inline_wrong, False),
            ("תיקון", inline_correct, False),
        ):
            field = tk.Frame(edit_panel, bg="#FFF9EC")
            field.pack(side="right", fill="x", expand=True, padx=5)
            tk.Label(
                field, text=label, bg="#FFF9EC", fg="#5A3518",
                font=("Segoe UI", 9, "bold"), anchor="e",
            ).pack(fill="x")
            if is_scope:
                control = ttk.Combobox(
                    field, textvariable=variable, values=list(reverse_scope_labels),
                    state="readonly", justify="right",
                )
            else:
                control = ttk.Entry(field, textvariable=variable, justify="right")
            control.pack(fill="x", pady=(3, 0))

        def refresh() -> None:
            nonlocal current_rules, selected_rule_index
            current_rules = load_learned_rules()
            selected_rule_index = None
            inline_wrong.set("")
            inline_correct.set("")
            rules_tree.delete(*rules_tree.get_children())
            for index, rule in enumerate(current_rules):
                scope_text = scope_labels.get(rule["scope"], rule["scope"])
                if str(rule.get("source", "")) == "server-approved":
                    scope_text += " · מהשרת"
                rules_tree.insert("", "end", iid=str(index), values=(
                    scope_text,
                    normalize_divine_names_for_display(rule["wrong"]),
                    normalize_divine_names_for_display(rule["correct"]),
                ))

        def load_inline_rule(_event=None) -> None:
            nonlocal selected_rule_index
            selection = rules_tree.selection()
            if not selection:
                return
            selected_rule_index = int(selection[0])
            rule = current_rules[selected_rule_index]
            inline_scope.set(scope_labels.get(rule["scope"], rule["scope"]))
            inline_wrong.set(normalize_divine_names_for_display(rule["wrong"]))
            inline_correct.set(normalize_divine_names_for_display(rule["correct"]))

        def save_inline_rule() -> None:
            nonlocal selected_rule_index
            if selected_rule_index is None or not (0 <= selected_rule_index < len(current_rules)):
                messagebox.showinfo(APP_NAME, "בחר כלל לעריכה.", parent=dialog)
                return
            if str(current_rules[selected_rule_index].get("source", "")) == "server-approved":
                messagebox.showinfo(
                    APP_NAME, "כלל מאושר שהתקבל מהשרת הוא לקריאה בלבד.", parent=dialog,
                )
                return
            scope = reverse_scope_labels.get(inline_scope.get(), "")
            wrong = restore_divine_names_from_display(clean_hebrew_text(inline_wrong.get()))
            correct = restore_divine_names_from_display(clean_hebrew_text(inline_correct.get()))
            if scope not in {"word", "start", "description"} or not wrong or not correct:
                messagebox.showwarning(APP_NAME, "יש למלא את כל שדות העריכה.", parent=dialog)
                return
            if _correction_key(wrong) == _correction_key(correct):
                messagebox.showwarning(APP_NAME, "הזיהוי והתיקון חייבים להיות שונים.", parent=dialog)
                return
            edited = {
                "scope": scope, "wrong": wrong, "correct": correct,
                "created": datetime.now().isoformat(timespec="seconds"),
            }
            updated: list[dict[str, str]] = []
            for index, rule in enumerate(current_rules):
                if index == selected_rule_index:
                    updated.append(edited)
                elif not (
                    rule["scope"] == scope
                    and _correction_key(rule["wrong"]) == _correction_key(wrong)
                ):
                    updated.append(rule)
            save_learned_rules(updated)
            self._refresh_rows_after_learning_change()
            refresh()
            self.status.set("כלל הלימוד נערך ונשמר")

        def edit_selected(_event=None) -> None:
            selection = rules_tree.selection()
            if not selection:
                messagebox.showinfo(APP_NAME, "בחר כלל לעריכה.", parent=dialog)
                return
            index = int(selection[0])
            rule = current_rules[index]
            if str(rule.get("source", "")) == "server-approved":
                messagebox.showinfo(
                    APP_NAME, "כלל מאושר שהתקבל מהשרת הוא לקריאה בלבד.", parent=dialog,
                )
                return
            editor = tk.Toplevel(dialog)
            editor.title("עריכת כלל OCR")
            editor.geometry("520x330")
            editor.resizable(False, False)
            editor.transient(dialog)
            editor.grab_set()
            editor.configure(bg="#E7D4AB")
            tk.Label(
                editor, text="עריכת כלל שנלמד", bg="#5A3518", fg="white",
                font=("Segoe UI", 15, "bold"), pady=12,
            ).pack(fill="x")
            reverse_scopes = {label: scope for scope, label in scope_labels.items()}
            scope_var = tk.StringVar(value=scope_labels.get(rule["scope"], rule["scope"]))
            wrong_var = tk.StringVar(value=normalize_divine_names_for_display(rule["wrong"]))
            correct_var = tk.StringVar(value=normalize_divine_names_for_display(rule["correct"]))
            form = tk.Frame(editor, bg="#FFF9EC", padx=18, pady=14)
            form.pack(fill="both", expand=True, padx=16, pady=12)
            for label, variable, is_scope in (
                ("סוג השדה", scope_var, True),
                ("הזיהוי השגוי", wrong_var, False),
                ("התיקון", correct_var, False),
            ):
                row_frame = tk.Frame(form, bg="#FFF9EC")
                row_frame.pack(fill="x", pady=5)
                tk.Label(
                    row_frame, text=label, bg="#FFF9EC", fg="#5A3518",
                    font=("Segoe UI", 10, "bold"), width=16, anchor="e",
                ).pack(side="right", padx=(8, 0))
                if is_scope:
                    widget = ttk.Combobox(
                        row_frame, textvariable=variable, values=list(reverse_scopes),
                        state="readonly", justify="right",
                    )
                else:
                    widget = ttk.Entry(row_frame, textvariable=variable, justify="right")
                widget.pack(side="right", fill="x", expand=True)

            def close_editor() -> None:
                try:
                    editor.grab_release()
                except tk.TclError:
                    pass
                editor.destroy()
                dialog.grab_set()

            def save_rule_edit() -> None:
                scope = reverse_scopes.get(scope_var.get(), "")
                wrong = restore_divine_names_from_display(clean_hebrew_text(wrong_var.get()))
                correct = restore_divine_names_from_display(clean_hebrew_text(correct_var.get()))
                if scope not in {"word", "start", "description"} or not wrong or not correct:
                    messagebox.showwarning(APP_NAME, "יש למלא את כל השדות.", parent=editor)
                    return
                if _correction_key(wrong) == _correction_key(correct):
                    messagebox.showwarning(APP_NAME, "הזיהוי והתיקון חייבים להיות שונים.", parent=editor)
                    return
                updated_rule = {
                    "scope": scope, "wrong": wrong, "correct": correct,
                    "created": datetime.now().isoformat(timespec="seconds"),
                }
                updated_rules = [
                    item for item_index, item in enumerate(current_rules)
                    if item_index == index or not (
                        item["scope"] == scope
                        and _correction_key(item["wrong"]) == _correction_key(wrong)
                    )
                ]
                updated_index = next(
                    item_index for item_index, item in enumerate(updated_rules)
                    if item is current_rules[index]
                )
                updated_rules[updated_index] = updated_rule
                save_learned_rules(updated_rules)
                self._refresh_rows_after_learning_change()
                close_editor()
                refresh()
                self.status.set("כלל הלימוד נערך ונשמר")

            action_row = tk.Frame(editor, bg="#E7D4AB")
            action_row.pack(fill="x", padx=16, pady=(0, 12))
            tk.Button(
                action_row, text="שמירת השינויים", command=save_rule_edit,
                bg="#278552", fg="white", relief="flat", font=("Segoe UI", 10, "bold"),
                padx=18, pady=8,
            ).pack(side="right", padx=4)
            tk.Button(
                action_row, text="ביטול", command=close_editor,
                bg="#F1E2C4", fg="#5A3518", relief="flat", font=("Segoe UI", 10, "bold"),
                padx=18, pady=8,
            ).pack(side="left", padx=4)
            editor.protocol("WM_DELETE_WINDOW", close_editor)

        def delete_selected() -> None:
            selection = rules_tree.selection()
            if not selection:
                messagebox.showinfo(APP_NAME, "בחר כלל למחיקה.", parent=dialog)
                return
            index = int(selection[0])
            rule = current_rules[index]
            if str(rule.get("source", "")) == "server-approved":
                messagebox.showinfo(
                    APP_NAME, "כלל מאושר שהתקבל מהשרת מנוהל בגרסה הפרטית.", parent=dialog,
                )
                return
            if not messagebox.askyesno(
                APP_NAME, f"למחוק את הכלל {rule['wrong']} ← {rule['correct']}?",
                parent=dialog,
            ):
                return
            del current_rules[index]
            save_learned_rules(current_rules)
            self._refresh_rows_after_learning_change()
            refresh()
            self.status.set("כלל הלימוד נמחק")

        def delete_all() -> None:
            if not current_rules:
                return
            if not messagebox.askyesno(
                APP_NAME, "למחוק את כל כללי הלימוד של ה-OCR?",
                icon="warning", parent=dialog,
            ):
                return
            save_learned_rules([])
            self._refresh_rows_after_learning_change()
            refresh()
            self.status.set("כל כללי הלימוד נמחקו")

        def rule_context_menu(event) -> str:
            item = rules_tree.identify_row(event.y)
            if not item:
                return "break"
            rules_tree.selection_set(item)
            rules_tree.focus(item)
            load_inline_rule()
            menu = tk.Menu(dialog, tearoff=False, font=("Segoe UI", 10))
            menu.add_command(label="עריכת הכלל", command=edit_selected)
            menu.add_command(label="מחיקת הכלל", command=delete_selected)
            try:
                menu.tk_popup(event.x_root, event.y_root)
            finally:
                menu.grab_release()
            return "break"

        buttons = tk.Frame(dialog, bg="#E7D4AB")
        buttons.pack(fill="x", padx=18, pady=14)
        tk.Button(
            buttons, text="שמירת העריכה", command=save_inline_rule,
            bg="#278552", fg="white", activebackground="#1F6B42",
            activeforeground="white", relief="flat", font=("Segoe UI", 10, "bold"),
            padx=18, pady=8,
        ).pack(side="right", padx=5)
        tk.Button(
            buttons, text="מחיקת הכלל המסומן", command=delete_selected,
            bg="#A66A16", fg="white", activebackground="#8C5410",
            activeforeground="white", relief="flat", font=("Segoe UI", 10, "bold"),
            padx=18, pady=8,
        ).pack(side="right", padx=5)
        tk.Button(
            buttons, text="מחיקת כל הכללים", command=delete_all,
            bg="#8A3B2C", fg="white", activebackground="#6F2D22",
            activeforeground="white", relief="flat", font=("Segoe UI", 10, "bold"),
            padx=18, pady=8,
        ).pack(side="right", padx=5)

        def close_dialog() -> None:
            self.learning_manager_open = False
            dialog.grab_release()
            dialog.destroy()

        tk.Button(
            buttons, text="סגירה", command=close_dialog, bg="#F1E2C4", fg="#5A3518",
            activebackground="#E5CF9F", relief="flat", font=("Segoe UI", 10, "bold"),
            padx=18, pady=8,
        ).pack(side="left", padx=5)
        dialog.protocol("WM_DELETE_WINDOW", close_dialog)
        rules_tree.bind("<<TreeviewSelect>>", load_inline_rule)
        rules_tree.bind("<Double-1>", edit_selected)
        rules_tree.bind("<Button-3>", rule_context_menu)
        rules_tree.bind("<Delete>", lambda _event: delete_selected())
        refresh()

    def open_cache_manager(self) -> None:
        if self.cache_manager_open:
            return
        self.cache_manager_open = True
        dialog = tk.Toplevel(self.root)
        dialog.title("ניהול מטמון")
        dialog.geometry("540x420")
        dialog.resizable(False, False)
        dialog.transient(self.root)
        dialog.grab_set()
        dialog.configure(bg="#E7D4AB")
        try:
            dialog.iconbitmap(default=str(resource_path("app.ico")))
        except Exception:
            pass

        tk.Label(
            dialog, text="ניהול מטמון OCR", bg="#5A3518", fg="white",
            font=("Segoe UI", 17, "bold"), pady=14,
        ).pack(fill="x")
        tk.Label(
            dialog,
            text="המחיקה אינה מוחקת את קובץ ה-PDF.\nבפתיחה הבאה של הקובץ תתבצע סריקה חדשה.",
            bg="#FFF9EC", fg="#74471F", font=("Segoe UI", 11),
            justify="right", anchor="e", padx=18, pady=14,
        ).pack(fill="x", padx=18, pady=(16, 8))

        actions = tk.Frame(dialog, bg="#FFF9EC", padx=20, pady=14)
        actions.pack(fill="both", expand=True, padx=18)

        def report_result(pdf_path: Path, removed: int) -> None:
            if removed:
                messagebox.showinfo(
                    APP_NAME,
                    f"המטמון של '{pdf_path.name}' נמחק.\nבפתיחה הבאה תתבצע סריקה מחדש.",
                    parent=dialog,
                )
                self.status.set(f"המטמון של {pdf_path.name} נמחק")
            else:
                messagebox.showinfo(APP_NAME, "לא נמצא מטמון שמור עבור הקובץ הזה.", parent=dialog)

        def delete_selected_pdf() -> None:
            selected = filedialog.askopenfilename(
                title="בחר PDF שאת המטמון שלו יש למחוק",
                filetypes=[("PDF", "*.pdf")], parent=dialog,
            )
            if not selected:
                return
            pdf_path = Path(selected)
            if not messagebox.askyesno(
                APP_NAME, f"למחוק רק את המטמון של '{pdf_path.name}'?",
                parent=dialog,
            ):
                return
            report_result(pdf_path, delete_cache_for_pdf(pdf_path))

        def delete_current_pdf() -> None:
            if self.pdf_path is None:
                messagebox.showinfo(APP_NAME, "לא פתוח כרגע קובץ PDF.", parent=dialog)
                return
            if not messagebox.askyesno(
                APP_NAME, f"למחוק רק את המטמון של '{self.pdf_path.name}'?",
                parent=dialog,
            ):
                return
            report_result(self.pdf_path, delete_cache_for_pdf(self.pdf_path))

        def delete_everything() -> None:
            if not messagebox.askyesno(
                APP_NAME,
                "למחוק את כל מטמוני ה-OCR?\nקובצי ה-PDF והגדרות התוכנה לא יימחקו.",
                icon="warning", parent=dialog,
            ):
                return
            removed = delete_all_ocr_caches()
            messagebox.showinfo(APP_NAME, f"נמחקו {removed} קובצי מטמון.", parent=dialog)
            self.status.set(f"נמחקו {removed} קובצי מטמון")

        button_style = {
            "bg": "#A66A16", "fg": "white", "activebackground": "#8C5410",
            "activeforeground": "white", "relief": "flat",
            "font": ("Segoe UI", 11, "bold"), "pady": 9,
        }
        tk.Button(
            actions, text="בחירת PDF ומחיקת המטמון שלו בלבד",
            command=delete_selected_pdf, **button_style,
        ).pack(fill="x", pady=5)
        tk.Button(
            actions, text="מחיקת המטמון של ה-PDF הפתוח",
            command=delete_current_pdf, **button_style,
        ).pack(fill="x", pady=5)
        tk.Button(
            actions, text="מחיקת כל המטמון", command=delete_everything,
            bg="#8A3B2C", fg="white", activebackground="#6F2D22",
            activeforeground="white", relief="flat", font=("Segoe UI", 11, "bold"), pady=9,
        ).pack(fill="x", pady=(16, 5))

        def close_dialog() -> None:
            self.cache_manager_open = False
            dialog.grab_release()
            dialog.destroy()

        tk.Button(
            dialog, text="סגירה", command=close_dialog, bg="#F1E2C4", fg="#5A3518",
            activebackground="#E5CF9F", relief="flat", font=("Segoe UI", 10, "bold"),
            padx=24, pady=8,
        ).pack(pady=(0, 14))
        dialog.protocol("WM_DELETE_WINDOW", close_dialog)

    def _build_ui(self) -> None:
        palette = {
            "navy": "#5A3518", "navy_light": "#74471F", "blue": "#A66A16",
            "yellow": "#F6D878", "page": "#E7D4AB", "card": "#FFF9EC",
            "text": "#332315", "muted": "#866A49", "line": "#CDB68E", "green": "#278552",
        }
        self.root.configure(bg=palette["page"])
        style = ttk.Style()
        style.theme_use("clam")
        style.configure("Page.TFrame", background=palette["page"])
        style.configure("Header.TFrame", background=palette["navy"])
        style.configure("HeaderTitle.TLabel", background=palette["navy"], foreground="white", font=("Segoe UI", 22, "bold"))
        style.configure("HeaderSub.TLabel", background=palette["navy"], foreground="#F2DFC0", font=("Segoe UI", 10))
        style.configure("Card.TFrame", background=palette["card"], relief="flat")
        style.configure("CardTitle.TLabel", background=palette["card"], foreground=palette["text"], font=("Segoe UI", 12, "bold"))
        style.configure("Muted.TLabel", background=palette["page"], foreground=palette["muted"], font=("Segoe UI", 10))
        style.configure("Status.TLabel", background=palette["card"], foreground=palette["green"], font=("Segoe UI", 10, "bold"))
        style.configure("Accent.TButton", background=palette["blue"], foreground="white", borderwidth=0, padding=(18, 10), font=("Segoe UI", 10, "bold"))
        style.map("Accent.TButton", background=[("active", "#8C5410"), ("pressed", "#6D3E0B")])
        style.configure("Secondary.TButton", background="#F1E2C4", foreground=palette["navy"], borderwidth=0, padding=(15, 9), font=("Segoe UI", 10, "bold"))
        style.map("Secondary.TButton", background=[("active", "#E5CF9F")])
        style.configure("Timer.TButton", background="#F1E2C4", foreground=palette["navy"], borderwidth=0, padding=(10, 8), font=("Segoe UI", 9, "bold"))
        style.map("Timer.TButton", background=[("active", "#E5CF9F")])
        style.configure("TimerAccent.TButton", background=palette["blue"], foreground="white", borderwidth=0, padding=(12, 8), font=("Segoe UI", 9, "bold"))
        style.map("TimerAccent.TButton", background=[("active", "#8C5410"), ("pressed", "#6D3E0B")])
        style.configure("Reader.Horizontal.TProgressbar", troughcolor="#E8D9BC", background=palette["blue"], borderwidth=0, thickness=7)
        style.configure("Reader.Horizontal.TScale", background=palette["card"], troughcolor="#DDC8A1")
        style.configure("Treeview", background="white", fieldbackground="white", foreground=palette["text"], rowheight=34, borderwidth=0, font=("Segoe UI", 10))
        style.configure("Treeview.Heading", background=palette["navy_light"], foreground="white", relief="flat", padding=(8, 10), font=("Segoe UI", 10, "bold"))
        style.map("Treeview", background=[("selected", palette["yellow"])], foreground=[("selected", palette["text"])])
        style.map("Treeview.Heading", background=[("active", palette["navy_light"])])
        style.configure("Editor.TEntry", fieldbackground="#FFFDF7", foreground=palette["text"], bordercolor=palette["line"], padding=7)
        style.configure("Editor.TCombobox", fieldbackground="#FFFDF7", foreground=palette["text"], bordercolor=palette["line"], padding=6)

        header = ttk.Frame(self.root, style="Header.TFrame", padding=(24, 16))
        header.pack(fill="x")
        title_box = ttk.Frame(header, style="Header.TFrame")
        title_box.pack(side="right")
        ttk.Label(title_box, text=APP_NAME, style="HeaderTitle.TLabel", anchor="e").pack(fill="x")
        self.header_subtitle = ttk.Label(
            title_box,
            text=(
                "OCR עברי, הקראה חכמה ודוחות שעות ללקוחות"
                if CUSTOMER_EDITION else "OCR עברי והקראה חכמה לדוחות דיוקי סופרים"
            ),
            style="HeaderSub.TLabel", anchor="e",
        )
        self.header_subtitle.pack(fill="x")
        shortcut_box = ttk.Frame(header, style="Header.TFrame")
        self.shortcut_box = shortcut_box
        shortcut_box.pack(side="left", padx=(0, 4))
        for action, label in (("next", "הבא"), ("previous", "הקודם"), ("repeat", "חזרה")):
            tk.Label(
                shortcut_box, textvariable=self.shortcut_vars[action], justify="center",
                bg=palette["navy_light"], fg="#F8E8CC", font=("Segoe UI", 9, "bold"),
                width=8, padx=4, pady=4,
            ).pack(side="left", padx=2)
            tk.Label(
                shortcut_box, text=label, bg=palette["navy_light"], fg="#F8E8CC",
                font=("Segoe UI", 8), padx=3, pady=4,
            ).pack(side="left", padx=(0, 3))

        body = ttk.Frame(self.root, style="Page.TFrame", padding=(18, 14, 18, 10))
        self.body_frame = body
        body.pack(fill="both", expand=True)

        toolbar = ttk.Frame(body, style="Card.TFrame", padding=(14, 11))
        toolbar.pack(fill="x", pady=(0, 10))
        toolbar_actions = ttk.Frame(toolbar, style="Card.TFrame")
        toolbar_actions.pack(fill="x")
        toolbar_settings = ttk.Frame(toolbar, style="Card.TFrame")
        toolbar_settings.pack(fill="x", pady=(8, 0))
        ttk.Button(toolbar_actions, text="פתיחת דוח PDF", style="Accent.TButton", command=self.choose_pdf).pack(side="right", padx=(6, 0))
        self.close_report_button = ttk.Button(
            toolbar_actions, text="סגירת דוח", style="Secondary.TButton", command=self.close_pdf,
        )
        self.close_report_button.pack(side="right", padx=6)
        ttk.Button(toolbar_actions, text="התחלת הקראה", style="Secondary.TButton", command=self.start_reading).pack(side="right", padx=6)
        ttk.Button(toolbar_actions, text="הגדרות", style="Secondary.TButton", command=self.open_default_settings).pack(side="right", padx=6)
        ttk.Button(toolbar_actions, text="ניהול מטמון", style="Secondary.TButton", command=self.open_cache_manager).pack(side="right", padx=6)
        if not CUSTOMER_EDITION:
            ttk.Button(
                toolbar_actions, text="הורדת כל ההקראות", style="Secondary.TButton",
                command=self.open_bulk_speech_download,
            ).pack(side="right", padx=6)
        if not GIGAPDF_OCR_EDITION:
            ttk.Button(
                toolbar_actions, text="בדיקת עדכון", style="Secondary.TButton",
                command=lambda: self.check_for_updates(silent=False),
            ).pack(side="right", padx=6)
        ttk.Label(
            toolbar_actions, textvariable=self.update_status_text, style="CardTitle.TLabel",
            font=("Segoe UI", 8, "bold"),
        ).pack(side="left", padx=(10, 4))
        ttk.Label(toolbar_settings, text="מהירות דיבור", style="CardTitle.TLabel").pack(side="right", padx=(0, 8))
        ttk.Scale(
            toolbar_settings, from_=-50, to=50, variable=self.speed, orient="horizontal", length=210,
            style="Reader.Horizontal.TScale", command=self._speed_changed,
        ).pack(side="right", padx=5)
        speed_badge = tk.Label(
            toolbar_settings, textvariable=self.speed_text, bg="#F4E5C7", fg=palette["blue"],
            font=("Segoe UI", 9, "bold"), width=8, padx=6, pady=6,
        )
        speed_badge.pack(side="right", padx=(0, 8))
        ttk.Label(toolbar_settings, text="קול", style="CardTitle.TLabel").pack(side="right", padx=(20, 7))
        voice_picker = ttk.Combobox(
            toolbar_settings, textvariable=self.voice_choice, state="readonly", width=22,
            values=VOICE_CHOICES, justify="right",
            font=("Segoe UI", 10),
        )
        voice_picker.pack(side="right", padx=(0, 5))
        ttk.Label(toolbar_settings, text="השהיה", style="CardTitle.TLabel").pack(side="right", padx=(14, 5))
        gap_picker = ttk.Combobox(
            toolbar_settings, textvariable=self.speech_gap, state="readonly", width=5,
            values=("0", "0.25", "0.5", "0.75", "1", "1.5", "2", "3", "4", "5"),
            justify="center", font=("Segoe UI", 10),
        )
        gap_picker.pack(side="right", padx=(0, 3))
        gap_picker.bind("<<ComboboxSelected>>", self._speech_gap_changed)
        ttk.Label(toolbar_settings, text="שניות", style="CardTitle.TLabel").pack(side="right", padx=(0, 4))

        timer_card = ttk.Frame(body, style="Card.TFrame", padding=(14, 9))
        timer_card.pack(fill="x", pady=(0, 10))
        timer_controls = ttk.Frame(timer_card, style="Card.TFrame")
        self.timer_controls_frame = timer_controls
        timer_controls.pack(fill="x")
        timer_identity = ttk.Frame(timer_controls, style="Card.TFrame")
        self.timer_identity_frame = timer_identity
        timer_identity.pack(side="right", fill="x", expand=True)
        timer_actions = ttk.Frame(timer_controls, style="Card.TFrame")
        self.timer_actions_frame = timer_actions
        timer_actions.pack(side="left", padx=(0, 8))
        ttk.Label(timer_identity, text="מעקב ותשלום", style="CardTitle.TLabel").pack(side="right", padx=(0, 10))
        ttk.Label(
            timer_identity, text="שיטת תשלום", style="CardTitle.TLabel",
            font=("Segoe UI", 9, "bold"),
        ).pack(side="right", padx=(5, 3))
        self.payment_mode_combo = ttk.Combobox(
            timer_identity, textvariable=self.payment_mode, state="readonly", width=19,
            values=tuple(PAYMENT_MODE_LABELS.values()), justify="right",
            style="Editor.TCombobox", font=("Segoe UI", 9),
        )
        self.payment_mode_combo.pack(side="right", padx=4)
        self.payment_mode_combo.bind("<<ComboboxSelected>>", self._payment_mode_changed)
        self.timer_issue_price_button = ttk.Button(
            timer_identity, text="מחירים לפי סוג", style="Timer.TButton",
            command=self.open_issue_pricing,
        )
        self.timer_issue_price_button.pack(side="right", padx=4)
        ttk.Label(timer_identity, text="לקוח", style="CardTitle.TLabel", font=("Segoe UI", 9, "bold")).pack(side="right", padx=(5, 3))
        self.timer_client_combo = ttk.Combobox(
            timer_identity, textvariable=self.timer_client, width=18, justify="right",
            style="Editor.TCombobox", font=("Segoe UI", 10),
        )
        self.timer_client_combo.pack(side="right", padx=4)
        self.timer_client_combo.bind("<<ComboboxSelected>>", self._timer_client_changed)
        self.timer_client_combo.bind("<FocusOut>", self._timer_client_changed)
        ttk.Label(timer_identity, text="₪ לשעה", style="CardTitle.TLabel", font=("Segoe UI", 9, "bold")).pack(side="right", padx=(5, 3))
        self.timer_rate_entry = ttk.Entry(
            timer_identity, textvariable=self.hourly_rate, width=8, justify="center",
            style="Editor.TEntry", font=("Segoe UI", 10, "bold"),
        )
        self.timer_rate_entry.pack(side="right", padx=4)
        self.timer_start_button = ttk.Button(
            timer_actions, text="התחלה", style="TimerAccent.TButton", command=self.start_timer,
        )
        self.timer_start_button.pack(side="right", padx=4)
        self.timer_pause_text = tk.StringVar(value="הפסקה")
        self.timer_pause_button = ttk.Button(
            timer_actions, textvariable=self.timer_pause_text, style="Timer.TButton",
            command=self.toggle_timer_pause,
        )
        self.timer_pause_button.pack(side="right", padx=4)
        self.timer_finish_button = ttk.Button(
            timer_actions,
            text="סיום וחישוב" if CUSTOMER_EDITION else "סיום והעברה לכספים",
            style="Timer.TButton", command=self.finish_timer,
        )
        self.timer_finish_button.pack(side="right", padx=4)
        self.timer_cancel_button = ttk.Button(
            timer_actions, text="ביטול טיימר", style="Timer.TButton", command=self.cancel_timer,
        )
        self.timer_cancel_button.pack(side="right", padx=4)
        self.timer_report_button = ttk.Button(
            timer_actions, text="דוח עבודה", style="Timer.TButton",
            command=self.save_customer_work_report,
        )
        if CUSTOMER_EDITION:
            self.timer_report_button.pack(side="right", padx=4)

        timer_result = ttk.Frame(timer_card, style="Card.TFrame")
        timer_result.pack(fill="x", pady=(8, 0))
        tk.Label(
            timer_result, textvariable=self.timer_elapsed_text, bg="#F6D878", fg=palette["text"],
            font=("Segoe UI", 14, "bold"), width=9, padx=8, pady=5,
        ).pack(side="left", padx=(0, 10))
        self.timer_summary_label = tk.Label(
            timer_result, textvariable=self.timer_summary_text, bg=palette["card"], fg=palette["navy"],
            font=("Segoe UI", 9, "bold"), anchor="w", justify="left", wraplength=560,
        )
        self.timer_summary_label.pack(side="left", fill="x", expand=True)
        tk.Label(
            timer_result, textvariable=self.finance_link_text, bg=palette["card"], fg="#2D7A4B",
            font=("Segoe UI", 8, "bold"), anchor="w", justify="left",
        ).pack(side="left", padx=(8, 0))

        status_card = ttk.Frame(body, style="Card.TFrame", padding=(12, 8))
        status_card.pack(fill="x", pady=(0, 10))
        ttk.Label(status_card, textvariable=self.status, style="Status.TLabel", anchor="e").pack(side="right")
        progress = ttk.Progressbar(status_card, variable=self.progress_value, maximum=100, style="Reader.Horizontal.TProgressbar")
        progress.pack(side="left", fill="x", expand=True, padx=(0, 18))

        self.recent_frame = ttk.Frame(body, style="Card.TFrame", padding=(28, 24))
        recent_header = ttk.Frame(self.recent_frame, style="Card.TFrame")
        recent_header.pack(fill="x", pady=(0, 16))
        ttk.Label(
            recent_header, text="קבצים שנפתחו לאחרונה", style="CardTitle.TLabel",
            anchor="e", font=("Segoe UI", 18, "bold"),
        ).pack(side="right")
        self.recent_summary = tk.StringVar()
        ttk.Label(
            recent_header, textvariable=self.recent_summary, style="Muted.TLabel", anchor="w",
        ).pack(side="left")
        tk.Label(
            self.recent_frame,
            text="אפשר לגרור לכאן קובץ PDF ולשחרר כדי לפתוח אותו",
            bg="#F6D878", fg=palette["text"], font=("Segoe UI", 12, "bold"),
            padx=14, pady=10,
        ).pack(fill="x", pady=(0, 14))

        recent_table = ttk.Frame(self.recent_frame, style="Card.TFrame")
        recent_table.pack(fill="both", expand=True)
        self.recent_tree = ttk.Treeview(
            recent_table, columns=("name", "folder"), show="headings", selectmode="browse",
        )
        self.recent_tree.heading("name", text="שם הקובץ")
        self.recent_tree.heading("folder", text="תיקייה")
        self.recent_tree.column("name", width=330, anchor="e")
        self.recent_tree.column("folder", width=760, anchor="e")
        recent_scroll = ttk.Scrollbar(recent_table, orient="vertical", command=self.recent_tree.yview)
        self.recent_tree.configure(yscrollcommand=recent_scroll.set)
        recent_scroll.pack(side="left", fill="y")
        self.recent_tree.pack(fill="both", expand=True)
        self.recent_tree.bind("<Double-1>", self._open_recent_selected)

        recent_buttons = ttk.Frame(self.recent_frame, style="Card.TFrame")
        recent_buttons.pack(fill="x", pady=(14, 0))
        ttk.Button(
            recent_buttons, text="פתיחת הקובץ המסומן", style="Accent.TButton",
            command=self._open_recent_selected,
        ).pack(side="right", padx=(0, 6))
        ttk.Button(
            recent_buttons, text="הסרה מהרשימה", style="Secondary.TButton",
            command=self._remove_recent_selected,
        ).pack(side="right", padx=6)

        content = ttk.Panedwindow(body, orient="horizontal")
        self.content = content

        preview_frame = ttk.Frame(content, style="Card.TFrame", padding=10)
        preview_header = ttk.Frame(preview_frame, style="Card.TFrame")
        preview_header.pack(fill="x", pady=(0, 5))
        ttk.Label(preview_header, text="תצוגת העמוד", style="CardTitle.TLabel", anchor="e").pack(side="right")
        preview_tools = ttk.Frame(preview_frame, style="Card.TFrame")
        preview_tools.pack(fill="x", pady=(0, 7))
        zoom_box = ttk.Frame(preview_tools, style="Card.TFrame")
        zoom_box.pack(fill="x")
        ttk.Button(zoom_box, text="+", style="Secondary.TButton", width=3, command=self.zoom_in).pack(side="right", padx=2)
        ttk.Button(zoom_box, text="−", style="Secondary.TButton", width=3, command=self.zoom_out).pack(side="right", padx=2)
        ttk.Button(zoom_box, text="התאם", style="Secondary.TButton", width=7, command=self.zoom_fit).pack(side="right", padx=2)
        tk.Label(
            zoom_box, textvariable=self.zoom_text, bg="#F4E5C7", fg=palette["navy"],
            font=("Segoe UI", 9, "bold"), width=6, padx=3, pady=6,
        ).pack(side="right", padx=(5, 2))
        page_box = ttk.Frame(preview_tools, style="Card.TFrame")
        page_box.pack(fill="x", pady=(5, 0))
        self.previous_page_button = ttk.Button(
            page_box, text="עמוד קודם", style="Secondary.TButton", width=12,
            command=lambda: self.navigate_report_page(-1),
        )
        self.previous_page_button.pack(side="right", fill="x", expand=True, padx=(0, 3))
        self.next_page_button = ttk.Button(
            page_box, text="עמוד הבא", style="Secondary.TButton", width=12,
            command=lambda: self.navigate_report_page(1),
        )
        self.next_page_button.pack(side="right", fill="x", expand=True, padx=(3, 0))
        self.previous_page_button.state(["disabled"])
        self.next_page_button.state(["disabled"])
        self.current_banner = tk.StringVar(value="לא נבחרה שורה")
        self.remaining_rows_text = tk.StringVar(value="הקראות שנותרו: —")
        self.remaining_pages_text = tk.StringVar(value="עמודי תוכן שנותרו: —")
        self.remaining_sheets_text = tk.StringVar(value="דפי דוח שנותרו: —")
        current_label = tk.Label(
            preview_frame, textvariable=self.current_banner, anchor="center", justify="center",
            bg=palette["yellow"], fg=palette["text"], font=("Segoe UI", 13, "bold"),
            padx=10, pady=8, wraplength=650,
        )
        self.current_label_widget = current_label
        current_label.pack(fill="x")
        counters = tk.Frame(preview_frame, bg="#F4E5C7", padx=4, pady=5)
        counters.pack(fill="x", pady=(2, 8))
        for variable in (
            self.remaining_rows_text, self.remaining_pages_text, self.remaining_sheets_text,
        ):
            tk.Label(
                counters, textvariable=variable, bg="#F4E5C7", fg=palette["navy"],
                font=("Segoe UI", 10, "bold"), anchor="center", padx=5, pady=3,
            ).pack(side="right", fill="x", expand=True, padx=2)
        canvas_box = ttk.Frame(preview_frame, style="Card.TFrame")
        canvas_box.pack(fill="both", expand=True)
        self.preview_canvas = tk.Canvas(
            canvas_box, width=450, height=400, bg="#D8C39E",
            highlightbackground=palette["line"], highlightthickness=1,
        )
        preview_vbar = ttk.Scrollbar(canvas_box, orient="vertical", command=self.preview_canvas.yview)
        preview_hbar = ttk.Scrollbar(canvas_box, orient="horizontal", command=self.preview_canvas.xview)
        self.preview_canvas.configure(yscrollcommand=preview_vbar.set, xscrollcommand=preview_hbar.set)
        self.preview_canvas.grid(row=0, column=0, sticky="nsew")
        preview_vbar.grid(row=0, column=1, sticky="ns")
        preview_hbar.grid(row=1, column=0, sticky="ew")
        canvas_box.rowconfigure(0, weight=1)
        canvas_box.columnconfigure(0, weight=1)
        self.preview_canvas.bind("<Configure>", self._preview_resized)
        self.preview_canvas.bind("<MouseWheel>", self._preview_mousewheel)
        self.preview_canvas.bind("<Shift-MouseWheel>", self._preview_mousewheel)
        self.preview_canvas.bind("<ButtonPress-1>", self._preview_pan_start)
        self.preview_canvas.bind("<B1-Motion>", self._preview_pan_move)
        self.preview_canvas.bind("<ButtonRelease-1>", self._preview_pan_end)

        table_card = ttk.Frame(content, style="Card.TFrame", padding=10)
        table_header = ttk.Frame(table_card, style="Card.TFrame")
        table_header.pack(fill="x", pady=(0, 8))
        ttk.Label(table_header, text="השורות שזוהו", style="CardTitle.TLabel", anchor="e").pack(side="right")
        ttk.Button(
            table_header, text="כללים שנלמדו", style="Secondary.TButton",
            command=self.open_learning_manager,
        ).pack(side="right", padx=8)
        ttk.Button(
            table_header, text="איפוס רוחב", style="Secondary.TButton",
            command=self._reset_result_column_widths,
        ).pack(side="left", padx=(0, 8))
        self.table_hint_label = ttk.Label(
            table_header,
            text="קליק ימני על שורה לתיקון OCR · אפשר לגרור גבול בין כותרות",
            style="Muted.TLabel", anchor="w",
        )
        self.table_hint_label.pack(side="left")
        filter_bar = ttk.Frame(table_card, style="Card.TFrame")
        filter_bar.pack(fill="x", pady=(0, 8))
        ttk.Label(filter_bar, text="סינון לפי סוג בעיה", style="CardTitle.TLabel").pack(
            side="right", padx=(4, 6),
        )
        self.issue_filter_combo = ttk.Combobox(
            filter_bar, textvariable=self.issue_filter, state="readonly", width=23,
            values=("הכול",), justify="right", style="Editor.TCombobox",
            font=("Segoe UI", 9),
        )
        self.issue_filter_combo.pack(side="right", padx=4)
        self.issue_filter_combo.bind("<<ComboboxSelected>>", self._result_view_changed)
        ttk.Label(filter_bar, text="מיון", style="CardTitle.TLabel").pack(
            side="right", padx=(14, 4),
        )
        self.issue_sort_combo = ttk.Combobox(
            filter_bar, textvariable=self.issue_sort, state="readonly", width=18,
            values=("סדר הדוח", "לפי סוג הבעיה", "לפי עמוד ושורה"),
            justify="right", style="Editor.TCombobox", font=("Segoe UI", 9),
        )
        self.issue_sort_combo.pack(side="right", padx=4)
        self.issue_sort_combo.bind("<<ComboboxSelected>>", self._result_view_changed)
        self.result_view_count = ttk.Label(
            filter_bar, text="", style="Muted.TLabel", anchor="w",
        )
        self.result_view_count.pack(side="left", padx=5)
        table_frame = ttk.Frame(table_card, style="Card.TFrame")
        table_frame.pack(fill="both", expand=True)
        content.add(preview_frame, weight=2)
        content.add(table_card, weight=3)

        columns = (
            "price", "description", "problem_type", "problem_word",
            "first_word", "line", "start", "page",
        )
        self.tree = ttk.Treeview(table_frame, columns=columns, show="headings", selectmode="browse", height=12)
        headings = {
            "price": "מחיר ₪", "description": "תיאור", "problem_type": "סוג הבעיה",
            "problem_word": "מילה בעייתית",
            "first_word": "תחילת השורה", "line": "שורה", "start": "המתחיל", "page": "עמוד",
        }
        widths = {
            "price": 78, "description": 145, "problem_type": 130, "problem_word": 140,
            "first_word": 140, "line": 60, "start": 190, "page": 58,
        }
        self.default_result_column_widths = dict(widths)
        for column in columns:
            self.tree.heading(column, text=headings[column])
            self.tree.column(
                column, width=self.result_column_widths.get(column, widths[column]),
                minwidth=42, stretch=True, anchor="e",
            )
        scrollbar = ttk.Scrollbar(table_frame, orient="vertical", command=self.tree.yview)
        self.tree.configure(yscrollcommand=scrollbar.set)
        scrollbar.pack(side="left", fill="y")
        self.tree.pack(fill="both", expand=True)
        self.tree.bind("<<TreeviewSelect>>", self.load_selected)
        self.tree.bind("<Double-1>", self.start_from_double_click)
        self.tree.bind("<Button-3>", self.open_row_context_menu)
        self.tree.bind("<ButtonRelease-1>", self._result_tree_mouse_released, add="+")
        self.result_price_summary_text = tk.StringVar(
            value="סה״כ מחיר לדוח: ₪0.00   |   נעשה עד עכשיו: ₪0.00",
        )
        tk.Label(
            table_card, textvariable=self.result_price_summary_text,
            bg="#F6D878", fg=palette["navy"], font=("Segoe UI", 11, "bold"),
            anchor="center", justify="center", padx=12, pady=7,
        ).pack(fill="x", pady=(7, 0))

        footer = tk.Label(
            self.root, textvariable=self.footer_text,
            bg=palette["navy"], fg="#F8E8CC", font=("Segoe UI", 10, "bold"), pady=8,
        )
        footer.pack(fill="x")

    def _window_resized(self, event) -> None:
        if event.widget is not self.root:
            return
        width = max(1, int(event.width))
        height = max(1, int(event.height))
        compact_width = width < 1120
        compact_height = height < 700
        if compact_width:
            if self.shortcut_box.winfo_manager():
                self.shortcut_box.pack_forget()
            if self.table_hint_label.winfo_manager():
                self.table_hint_label.pack_forget()
            self.body_frame.configure(padding=(8, 8, 8, 6))
        else:
            if not self.shortcut_box.winfo_manager():
                self.shortcut_box.pack(side="left", padx=(0, 4))
            if not self.table_hint_label.winfo_manager():
                self.table_hint_label.pack(side="left")
            self.body_frame.configure(padding=(18, 14, 18, 10))
        if compact_height:
            if self.header_subtitle.winfo_manager():
                self.header_subtitle.pack_forget()
        elif not self.header_subtitle.winfo_manager():
            self.header_subtitle.pack(fill="x")
        self.timer_summary_label.configure(wraplength=max(180, width - 410))
        try:
            preview_width = self.current_label_widget.master.winfo_width()
            self.current_label_widget.configure(wraplength=max(220, preview_width - 28))
        except tk.TclError:
            pass

    def _speed_changed(self, value: str) -> None:
        amount = int(round(float(value)))
        self.speed.set(amount)
        self.speed_text.set(self._speed_label(amount))

    @staticmethod
    def _speed_label(amount: int) -> str:
        if amount <= -30:
            return "איטית מאוד"
        elif amount < -8:
            return "איטית"
        elif amount <= 8:
            return "רגילה"
        elif amount < 30:
            return "מהירה"
        return "מהירה מאוד"

    def speech_gap_seconds(self) -> float:
        try:
            return max(0.0, min(5.0, float(self.speech_gap.get())))
        except (TypeError, ValueError):
            return 1.0

    def _speech_gap_changed(self, _event=None) -> None:
        gap = self.speech_gap_seconds()
        self.speech_gap.set(f"{gap:g}")
        self._save_settings()
        self.status.set(f"ההשהיה בין המילים נקבעה ל־{gap:g} שניות")

    def _bind_keys(self) -> None:
        for sequence in self.bound_action_sequences:
            self.root.unbind_all(sequence)
        self.bound_action_sequences.clear()

        callbacks = {"next": self.next_row, "previous": self.previous_row, "repeat": self.repeat_row}
        aliases = {"Return": "KP_Enter", "minus": "KP_Subtract", "plus": "KP_Add"}

        for action, keysym in self.key_bindings.items():
            def dispatch(_event, callback=callbacks[action]):
                if (
                    self.key_settings_open or self.cache_manager_open
                    or self.learning_manager_open or self.image_training_open
                ):
                    return "break"
                return callback()

            sequences = [f"<KeyPress-{keysym}>"]
            if keysym in aliases:
                sequences.append(f"<KeyPress-{aliases[keysym]}>")
            for sequence in sequences:
                self.root.bind_all(sequence, dispatch)
                self.bound_action_sequences.append(sequence)
        self.root.bind_all("<Control-MouseWheel>", self._ctrl_mousewheel)

    def _show_home_screen(self) -> None:
        if hasattr(self, "content"):
            self.content.pack_forget()
        if hasattr(self, "editor_frame"):
            self.editor_frame.pack_forget()
        if hasattr(self, "recent_frame") and not self.recent_frame.winfo_manager():
            self.recent_frame.pack(fill="both", expand=True)
        if hasattr(self, "close_report_button"):
            self.close_report_button.state(["disabled"])
        self._refresh_recent_files()

    def _show_report_screen(self) -> None:
        self.recent_frame.pack_forget()
        if not self.content.winfo_manager():
            self.content.pack(fill="both", expand=True)
        self.close_report_button.state(["!disabled"])

    def _open_recent_selected(self, _event=None) -> str:
        selection = self.recent_tree.selection()
        if not selection:
            return "break"
        index = int(selection[0])
        if index < 0 or index >= len(self.recent_files):
            return "break"
        pdf_path = Path(self.recent_files[index])
        if not pdf_path.exists():
            messagebox.showerror(
                APP_NAME,
                "הקובץ אינו נמצא במיקום שבו נפתח לאחרונה.\nאפשר להסיר אותו מהרשימה.",
            )
            return "break"
        self.open_pdf(pdf_path)
        return "break"

    def _remove_recent_selected(self) -> None:
        selection = self.recent_tree.selection()
        if not selection:
            return
        index = int(selection[0])
        if 0 <= index < len(self.recent_files):
            removed = Path(self.recent_files.pop(index)).name
            self._save_settings()
            self._refresh_recent_files()
            self.status.set(f"{removed} הוסר מרשימת הקבצים האחרונים")

    def _enable_pdf_drop(self) -> None:
        if os.name != "nt":
            return
        try:
            self.root.update_idletasks()
            hwnd = int(self.root.winfo_id())
            user32 = ctypes.windll.user32
            shell32 = ctypes.windll.shell32
            wndproc_type = ctypes.WINFUNCTYPE(
                ctypes.c_ssize_t, ctypes.c_void_p, ctypes.c_uint,
                ctypes.c_size_t, ctypes.c_ssize_t,
            )
            user32.SetWindowLongPtrW.argtypes = [ctypes.c_void_p, ctypes.c_int, ctypes.c_void_p]
            user32.SetWindowLongPtrW.restype = ctypes.c_void_p
            user32.CallWindowProcW.argtypes = [
                ctypes.c_void_p, ctypes.c_void_p, ctypes.c_uint,
                ctypes.c_size_t, ctypes.c_ssize_t,
            ]
            user32.CallWindowProcW.restype = ctypes.c_ssize_t
            shell32.DragAcceptFiles.argtypes = [ctypes.c_void_p, ctypes.c_bool]
            shell32.DragQueryFileW.argtypes = [
                ctypes.c_void_p, ctypes.c_uint, ctypes.c_wchar_p, ctypes.c_uint,
            ]
            shell32.DragQueryFileW.restype = ctypes.c_uint
            shell32.DragFinish.argtypes = [ctypes.c_void_p]
            old_proc_holder = {"value": 0}

            def wndproc(window, message, wparam, lparam):
                if message == 0x0233:  # WM_DROPFILES
                    paths: list[str] = []
                    try:
                        count = int(shell32.DragQueryFileW(wparam, 0xFFFFFFFF, None, 0))
                        for index in range(count):
                            length = int(shell32.DragQueryFileW(wparam, index, None, 0))
                            buffer = ctypes.create_unicode_buffer(length + 1)
                            shell32.DragQueryFileW(wparam, index, buffer, length + 1)
                            paths.append(buffer.value)
                    finally:
                        shell32.DragFinish(wparam)
                    self.root.after(0, self._open_dropped_files, paths)
                    return 0
                return user32.CallWindowProcW(
                    old_proc_holder["value"], window, message, wparam, lparam,
                )

            callback = wndproc_type(wndproc)
            old_proc = user32.SetWindowLongPtrW(hwnd, -4, callback)
            if not old_proc:
                return
            old_proc_holder["value"] = old_proc
            shell32.DragAcceptFiles(hwnd, True)
            self._drop_hwnd = hwnd
            self._drop_old_wndproc = old_proc
            self._drop_wndproc_callback = callback
        except Exception:
            self._drop_hwnd = 0
            self._drop_old_wndproc = 0
            self._drop_wndproc_callback = None

    def _open_dropped_files(self, paths: list[str]) -> None:
        pdfs = [Path(path) for path in paths if Path(path).suffix.lower() == ".pdf"]
        if not pdfs:
            messagebox.showinfo(APP_NAME, "יש לגרור קובץ PDF.")
            return
        self.open_pdf(pdfs[0])
        if len(pdfs) > 1:
            self.status.set(f"נפתח {pdfs[0].name}; אפשר לפתוח דוח אחד בכל פעם")

    def choose_pdf(self) -> None:
        selected = filedialog.askopenfilename(title="בחר דוח PDF", filetypes=[("PDF", "*.pdf")])
        if not selected:
            return
        self.open_pdf(Path(selected))

    def restore_last_report(self) -> None:
        state = self.startup_restore_state
        self.startup_restore_state = None
        if not isinstance(state, dict):
            return
        pdf_path = Path(str(state.get("pdf_path", "")))
        if not pdf_path.exists() or pdf_path.suffix.lower() != ".pdf":
            return
        self.open_pdf(pdf_path, restore_state=state)

    def open_pdf(self, pdf_path: Path, restore_state: dict | None = None) -> None:
        if not pdf_path.exists() or pdf_path.suffix.lower() != ".pdf":
            messagebox.showerror(APP_NAME, "קובץ ה-PDF אינו נמצא.")
            return
        self.speech.cancel()
        self.ocr_generation += 1
        generation = self.ocr_generation
        self.pending_report_restore = restore_state if isinstance(restore_state, dict) else None
        self.pdf_path = pdf_path
        self._record_recent_file(pdf_path)
        self._show_report_screen()
        self.status.set("מתחיל OCR...")
        self.progress_value.set(0)
        self.rows.clear()
        self.current_index = -1
        self.issue_filter.set("הכול")
        self.issue_sort.set("סדר הדוח")
        self._reset_reading_stats()
        self.preview_cache.clear()
        self.preview_base_image = None
        self.preview_page_number = 0
        self.preview_image_bounds = None
        self.zoom_factor = self.default_zoom_factor
        self.zoom_text.set(f"{int(round(self.zoom_factor * 100))}%")
        self.preview_canvas.delete("all")
        self._update_page_navigation_buttons()
        self.current_banner.set("מזהה את הדוח...")
        self._set_remaining_banner(None, None, None)
        self.tree.delete(*self.tree.get_children())
        for variable in self.editor_vars.values():
            variable.set("")
        threading.Thread(
            target=self._ocr_background, args=(pdf_path, generation), daemon=True,
        ).start()

    def _ocr_background(self, pdf_path: Path, generation: int) -> None:
        try:
            def progress(message: str, current: int, total: int) -> None:
                self.root.after(0, self._ocr_progress, generation, message, current, total)
            rows = ReportOcr(progress).read(pdf_path)
            self.root.after(0, self._ocr_finished, generation, pdf_path, rows)
        except Exception as exc:
            details = traceback.format_exc()
            log = app_data_dir() / "error.log"
            log.write_text(details, encoding="utf-8")
            self.root.after(0, self._show_error, generation, str(exc))

    def _ocr_progress(self, generation: int, message: str, current: int, total: int) -> None:
        if generation != self.ocr_generation:
            return
        self.status.set(message)
        self.progress_value.set(current / total * 100)

    @staticmethod
    def _offline_ai_row_payload(row: ReportRow) -> dict[str, object]:
        return {
            "page": row.page,
            "line": row.line,
            "start": row.ocr_start or row.start,
            "first_word": row.ocr_first_word or row.first_word,
            "problem_word": row.ocr_problem_word or row.problem_word,
            "problem_type": row.ocr_problem_type or row.problem_type,
            "description": row.ocr_description or row.description,
            "report_kind": row.report_kind,
            "ocr_confidence": row.confidence,
        }

    def _row_needs_offline_ai(self, row: ReportRow) -> bool:
        if row.ai_reviewed:
            return False
        if float(row.confidence or 0) < self.ai_confidence_threshold:
            return True
        values = (row.ocr_first_word or row.first_word, row.ocr_problem_word or row.problem_word)
        if not values[0] or not values[1]:
            return True
        suspicious = re.compile(r"[^\u0590-\u05ff\s'׳״\"-]")
        return any(bool(suspicious.search(str(value))) for value in values if value)

    @staticmethod
    def _ai_reference_for_row(row: ReportRow) -> tuple[str, str]:
        try:
            page_key = str(int(re.search(r"\d+", row.page).group()))
        except (AttributeError, TypeError, ValueError):
            return "", ""
        page_lines = _load_nikud_corpus().get(page_key, {})
        try:
            line_key = str(int(re.search(r"\d+", row.line).group()))
        except (AttributeError, TypeError, ValueError):
            line_key = ""
        corpus_line = str(page_lines.get(line_key, ""))
        page_head = " ".join(str(page_lines.get(str(number), "")) for number in range(1, 5))
        return corpus_line, page_head

    @staticmethod
    def _safe_ai_candidate(
        field: str, original: str, proposed: object, reference: str, confidence: float,
    ) -> str | None:
        candidate = clean_hebrew_text(str(proposed or ""))
        original = clean_hebrew_text(str(original or ""))
        if not candidate or _correction_key(candidate) == _correction_key(original):
            return None
        if confidence < 0.84:
            return None
        if field == "problem_type":
            normalized = normalize_problem_type(candidate)
            return normalized if normalized in KNOWN_PROBLEM_TYPES else None
        if field == "description":
            ratio = difflib.SequenceMatcher(
                None, _correction_key(original), _correction_key(candidate),
            ).ratio()
            return candidate if ratio >= 0.72 else None
        if re.search(r"[^\u0590-\u05ff\s'׳״\"-]", candidate):
            return None
        original_key = _correction_key(original)
        candidate_key = _correction_key(candidate)
        reference_key = _correction_key(reference)
        ratio = difflib.SequenceMatcher(None, original_key, candidate_key).ratio()
        appears_in_reference = bool(candidate_key and candidate_key in reference_key)
        if ratio >= 0.74 or (appears_in_reference and (not original_key or ratio >= 0.45)):
            return candidate
        return None

    def _apply_offline_ai_result(
        self, generation: int, pdf_path: Path, index: int, result: dict,
        source: str = "text",
    ) -> None:
        if (
            generation != self.offline_ai_review_generation
            or self.pdf_path != pdf_path
            or not (0 <= index < len(self.rows))
        ):
            return
        row = self.rows[index]
        try:
            confidence = max(0.0, min(1.0, float(result.get("confidence", 0) or 0)))
        except (TypeError, ValueError):
            confidence = 0.0
        corpus_line, page_head = self._ai_reference_for_row(row)
        references = {
            "start": page_head,
            "first_word": corpus_line,
            "problem_word": corpus_line,
            "problem_type": " ".join(sorted(KNOWN_PROBLEM_TYPES)),
            "description": row.ocr_description or row.description,
        }
        changed = False
        for field in ("start", "first_word", "problem_word", "problem_type", "description"):
            original = str(getattr(row, f"ocr_{field}") or getattr(row, field) or "")
            accepted = self._safe_ai_candidate(
                field, original, result.get(field, ""), references[field], confidence,
            )
            if accepted:
                setattr(row, f"ai_{field}", accepted)
                changed = True
        row.ai_confidence = max(row.ai_confidence, confidence)
        row.ai_reason = clean_hebrew_text(str(result.get("reason", "")))
        if source == "vision" or not self.ai_vision_fallback or confidence >= 0.88:
            row.ai_reviewed = True
        apply_learned_rules_to_rows([row])
        try:
            write_ocr_cache(pdf_path, self.rows)
        except OSError:
            pass
        self._refresh_result_rows()
        if self.current_index == index:
            self.load_selected()
        if changed:
            self.status.set(
                f"AI אופליין תיקן שורה {row.line or index + 1} "
                f"({int(round(confidence * 100))}% ביטחון)"
            )

    def _start_offline_ai_review(self, pdf_path: Path, rows: list[ReportRow]) -> None:
        manager = self.offline_ai
        if (
            manager is None or not self.ai_enabled or not self.ai_auto_review
            or not manager.runtime_ready() or not manager.text_ready()
        ):
            return
        self.offline_ai_review_generation += 1
        generation = self.offline_ai_review_generation
        candidates = [index for index, row in enumerate(rows) if self._row_needs_offline_ai(row)]
        if not candidates:
            return
        learned = load_learned_rules()

        def examples_for(row: ReportRow) -> list[dict[str, object]]:
            examples: list[dict[str, object]] = []
            for rule in learned:
                report_kind = str(rule.get("report_kind", ""))
                if report_kind and report_kind != row.report_kind:
                    continue
                examples.append({
                    "scope": rule.get("scope", ""),
                    "wrong": rule.get("wrong", ""),
                    "correct": rule.get("correct", ""),
                    "reason": rule.get("ai_reason", ""),
                    "apply_mode": rule.get("ai_apply_mode", "exact"),
                })
            return examples[-24:]

        def worker() -> None:
            vision_candidates: list[int] = []
            for position, index in enumerate(candidates, start=1):
                if generation != self.offline_ai_review_generation or self.pdf_path != pdf_path:
                    return
                row = rows[index]
                try:
                    corpus_line, page_head = self._ai_reference_for_row(row)
                    result = manager.review_text(
                        self._offline_ai_row_payload(row), corpus_line, page_head,
                        examples_for(row),
                    )
                    try:
                        confidence = float(result.get("confidence", 0) or 0)
                    except (TypeError, ValueError):
                        confidence = 0.0
                    if confidence < 0.88 or not row.ocr_first_word or not row.ocr_problem_word:
                        vision_candidates.append(index)
                    self.root.after(
                        0, self._apply_offline_ai_result,
                        generation, pdf_path, index, result, "text",
                    )
                    self.root.after(
                        0, self.status.set,
                        f"AI אופליין בדק {position} מתוך {len(candidates)} שורות חשודות",
                    )
                except Exception:
                    try:
                        (app_data_dir() / "offline-ai-review-error.log").write_text(
                            traceback.format_exc(), encoding="utf-8",
                        )
                    except OSError:
                        pass
            if self.ai_vision_fallback and manager.vision_ready():
                for index in vision_candidates[:30]:
                    if generation != self.offline_ai_review_generation or self.pdf_path != pdf_path:
                        return
                    row = rows[index]
                    try:
                        image = render_report_row_crop(pdf_path, row, dpi=220)
                        buffer = io.BytesIO()
                        image.save(buffer, "JPEG", quality=88, optimize=True)
                        result = manager.review_image(
                            buffer.getvalue(), self._offline_ai_row_payload(row),
                        )
                        self.root.after(
                            0, self._apply_offline_ai_result,
                            generation, pdf_path, index, result, "vision",
                        )
                    except Exception:
                        continue
            self.root.after(0, self.status.set, "בדיקת AI אופליין הסתיימה")

        threading.Thread(target=worker, name="duk-offline-ai-review", daemon=True).start()

    def _show_error(self, generation: int, message: str) -> None:
        if generation != self.ocr_generation:
            return
        self.status.set("הזיהוי נכשל")
        messagebox.showerror(APP_NAME, message)

    def _ocr_finished(self, generation: int, pdf_path: Path, rows: list[ReportRow]) -> None:
        if generation != self.ocr_generation or self.pdf_path != pdf_path:
            return
        self.rows = rows
        self._update_issue_filter_options()
        self._refresh_result_rows()
        self.status.set(f"נמצאו {len(rows)} שורות. אפשר לתקן או להתחיל בהקראה.")
        self.progress_value.set(100)
        self._start_private_avri_library_preparation(pdf_path, rows)
        self._start_offline_ai_review(pdf_path, rows)
        if rows:
            restore = self.pending_report_restore
            self.pending_report_restore = None
            restore_index = 0
            if isinstance(restore, dict):
                try:
                    restore_index = max(0, min(int(restore.get("current_index", 0)), len(rows) - 1))
                except (TypeError, ValueError):
                    restore_index = 0
                identity = restore.get("row")
                if isinstance(identity, dict) and identity:
                    try:
                        wanted_source_page = int(identity.get("source_pdf_page", 0) or 0)
                    except (TypeError, ValueError):
                        wanted_source_page = 0
                    wanted = (
                        str(identity.get("page", "")),
                        str(identity.get("start", "")),
                        str(identity.get("line", "")),
                        str(identity.get("first_word", "")),
                        wanted_source_page,
                    )
                    for index, row in enumerate(rows):
                        candidate = (row.page, row.start, row.line, row.first_word, row.source_pdf_page)
                        if candidate == wanted:
                            restore_index = index
                            break
                try:
                    self.zoom_factor = max(0.60, min(4.0, float(restore.get("zoom_factor", 1.0))))
                except (TypeError, ValueError):
                    self.zoom_factor = self.default_zoom_factor
                self.zoom_text.set(f"{int(round(self.zoom_factor * 100))}%")
            self.select_index(restore_index)
            self._prefetch_rows(restore_index, count=2)
            if isinstance(restore, dict) and (
                "preview_x" in restore or "preview_y" in restore
            ):
                try:
                    preview_x = max(0.0, min(1.0, float(restore.get("preview_x", 0.0))))
                    preview_y = max(0.0, min(1.0, float(restore.get("preview_y", 0.0))))
                except (TypeError, ValueError):
                    preview_x = preview_y = 0.0
                self.root.after(250, self._restore_preview_scroll, preview_x, preview_y)
                self.status.set(
                    f"הדוח נפתח מחדש במקום שנשמר - שורה {restore_index + 1} מתוך {len(rows)}"
                )
                self._save_settings()

    def _restore_preview_scroll(self, preview_x: float, preview_y: float) -> None:
        try:
            self.preview_canvas.xview_moveto(preview_x)
            self.preview_canvas.yview_moveto(preview_y)
        except tk.TclError:
            pass

    def close_pdf(self) -> None:
        if self.pdf_path is None:
            self._show_home_screen()
            return
        closed_name = self.pdf_path.name
        self.speech.cancel()
        self.ocr_generation += 1
        self.offline_ai_review_generation += 1
        self.pending_report_restore = None
        self.pdf_path = None
        self.rows.clear()
        self.current_index = -1
        self.issue_filter.set("הכול")
        self.issue_sort.set("סדר הדוח")
        self._reset_reading_stats()
        self.tree.delete(*self.tree.get_children())
        self._update_issue_filter_options()
        if hasattr(self, "result_view_count"):
            self.result_view_count.configure(text="")
        self.preview_cache.clear()
        self.preview_base_image = None
        self.preview_photo = None
        self.preview_page_number = 0
        self.preview_image_bounds = None
        self.preview_canvas.delete("all")
        self._update_page_navigation_buttons()
        self.current_banner.set("לא נבחרה שורה")
        self._set_remaining_banner(None, None, None)
        self.progress_value.set(0)
        for variable in self.editor_vars.values():
            variable.set("")
        self.status.set(f"{closed_name} נסגר - אפשר לבחור דוח אחר")
        self._save_settings()
        self._show_home_screen()

    def load_selected(self, _event=None) -> None:
        selection = self.tree.selection()
        if not selection:
            return
        index = int(selection[0])
        row = self.rows[index]
        for name, variable in self.editor_vars.items():
            value = getattr(row, name)
            if name in {"start", "first_word", "problem_word"}:
                value = display_report_text(row, value)
            variable.set(value)
        self.show_row_preview(row, index)

    def _capture_result_column_widths(self) -> None:
        if not hasattr(self, "tree"):
            return
        for column in self.tree.cget("columns"):
            try:
                self.result_column_widths[str(column)] = int(self.tree.column(column, "width"))
            except (tk.TclError, TypeError, ValueError):
                pass
        self._save_settings()

    @staticmethod
    def _result_numeric_value(value: object) -> tuple[int, str]:
        text_value = str(value or "").strip()
        match = re.search(r"\d+", text_value)
        return (int(match.group()) if match else 10**9, text_value)

    def _update_issue_filter_options(self) -> None:
        if not hasattr(self, "issue_filter_combo"):
            return
        issues = sorted({
            issue for issue in (self._billing_issue_for_row(row) for row in self.rows)
            if issue
        })
        values = ("הכול", *issues)
        self.issue_filter_combo.configure(values=values)
        if self.issue_filter.get() not in values:
            self.issue_filter.set("הכול")

    def _visible_result_indices(self) -> list[int]:
        selected_issue = self.issue_filter.get().strip()
        indices = [
            index for index, row in enumerate(self.rows)
            if selected_issue in {"", "הכול"}
            or self._billing_issue_for_row(row) == selected_issue
        ]
        sorting = self.issue_sort.get().strip()
        if sorting == "לפי סוג הבעיה":
            indices.sort(key=lambda index: (
                self._billing_issue_for_row(self.rows[index]),
                self._result_numeric_value(self.rows[index].page),
                self._result_numeric_value(self.rows[index].line),
                index,
            ))
        elif sorting == "לפי עמוד ושורה":
            indices.sort(key=lambda index: (
                self._result_numeric_value(self.rows[index].page),
                self._result_numeric_value(self.rows[index].line),
                self._billing_issue_for_row(self.rows[index]),
                index,
            ))
        return indices

    def _result_row_prices(self) -> dict[int, float]:
        prices: dict[int, float] = {}
        for item in self._current_alert_items():
            try:
                index = int(item.get("row_index", -1))
                price = max(0.0, float(item.get("rate", 0) or 0))
            except (TypeError, ValueError):
                continue
            if 0 <= index < len(self.rows):
                prices[index] = price
        return prices

    def _update_result_price_summary(self, prices: dict[int, float] | None = None) -> None:
        if not hasattr(self, "result_price_summary_text"):
            return
        active_prices = self._result_row_prices() if prices is None else prices
        total = sum((Decimal(str(value)) for value in active_prices.values()), Decimal("0"))
        completed_indices = {
            index for index in self.reading_visited_indices if index in active_prices
        }
        completed = sum(
            (Decimal(str(active_prices[index])) for index in completed_indices), Decimal("0"),
        )
        missing = sum(1 for value in active_prices.values() if value <= 0)
        text_value = (
            f"סה״כ מחיר לדוח: ₪{total:,.2f}   |   "
            f"נעשה עד עכשיו: ₪{completed:,.2f} "
            f"({len(completed_indices)} מתוך {len(active_prices)} התראות)"
        )
        if missing:
            text_value += f"   |   {missing} התראות ללא מחיר"
        self.result_price_summary_text.set(text_value)

    def _refresh_result_rows(self) -> None:
        if not hasattr(self, "tree"):
            return
        selected_iid = str(self.current_index) if self.current_index >= 0 else ""
        self.tree.delete(*self.tree.get_children())
        indices = self._visible_result_indices()
        prices = self._result_row_prices()
        for index in indices:
            row = self.rows[index]
            self.tree.insert("", "end", iid=str(index), values=(
                f"₪{prices[index]:g}" if prices.get(index, 0) > 0 else "",
                row.description,
                row.problem_type,
                display_report_text(row, row.problem_word),
                display_report_text(row, row.first_word),
                row.line, display_report_text(row, row.start), row.page,
            ))
        if hasattr(self, "result_view_count"):
            self.result_view_count.configure(
                text=f"מוצגות {len(indices)} מתוך {len(self.rows)} התראות"
            )
        if selected_iid and self.tree.exists(selected_iid):
            self.tree.selection_set(selected_iid)
            self.tree.focus(selected_iid)
            self.tree.see(selected_iid)
        self._update_result_price_summary(prices)

    def _result_view_changed(self, _event=None) -> None:
        self._refresh_result_rows()
        count = len(self._visible_result_indices())
        self.status.set(
            f"תצוגת ההתראות עודכנה · מוצגות {count} מתוך {len(self.rows)} · "
            "סדר ההקראה המקורי לא השתנה"
        )

    def _result_tree_mouse_released(self, event) -> None:
        if self.tree.identify_region(event.x, event.y) in {"heading", "separator"}:
            self.root.after(30, self._capture_result_column_widths)

    def _reset_result_column_widths(self) -> None:
        if not hasattr(self, "tree"):
            return
        for column, width in self.default_result_column_widths.items():
            self.tree.column(column, width=width)
        self._capture_result_column_widths()
        self.status.set("רוחב עמודות הטבלה הוחזר לברירת המחדל")

    def start_from_double_click(self, event) -> str:
        if self.tree.identify_region(event.x, event.y) != "cell":
            return "break"
        item = self.tree.identify_row(event.y)
        if not item:
            return "break"
        self.select_index(int(item))
        self.speak_current(include_header=True, repeat=False)
        return "break"

    def open_row_context_menu(self, event) -> str:
        item = self.tree.identify_row(event.y)
        if not item:
            return "break"
        index = int(item)
        self.tree.selection_set(item)
        self.tree.focus(item)
        self.load_selected()
        self.root.after(10, lambda: self.open_row_ocr_correction(index))
        return "break"

    def _remaining_reading_counts(self, index: int) -> tuple[int, int, int]:
        if not (0 <= index < len(self.rows)):
            return 0, 0, 0
        remaining_rows = len(self.rows) - index
        content_page_keys: set[str] = set()
        report_sheet_keys: set[int] = set()
        for remaining_row in self.rows[index:]:
            page_key = remaining_row.page.strip()
            if page_key:
                content_page_keys.add(page_key)
            if remaining_row.source_pdf_page > 0:
                report_sheet_keys.add(remaining_row.source_pdf_page)
        return (
            remaining_rows,
            max(1, len(content_page_keys)),
            max(1, len(report_sheet_keys)),
        )

    def _set_remaining_banner(
        self, rows: int | None, pages: int | None, sheets: int | None,
    ) -> None:
        self.remaining_rows_text.set(
            "הקראות שנותרו: —" if rows is None else f"הקראות שנותרו: {rows}"
        )
        self.remaining_pages_text.set(
            "עמודי תוכן שנותרו: —" if pages is None else f"עמודי תוכן שנותרו: {pages}"
        )
        self.remaining_sheets_text.set(
            "דפי דוח שנותרו: —" if sheets is None else f"דפי דוח שנותרו: {sheets}"
        )

    def show_row_preview(self, row: ReportRow, index: int) -> None:
        if not self.pdf_path or row.source_pdf_page <= 0:
            return
        remaining_rows, remaining_pages, remaining_report_sheets = self._remaining_reading_counts(index)
        detail_line = f"עמוד: {row.page}     שורה: {row.line}"
        shown_first = display_report_text(row, row.first_word)
        shown_problem = display_report_text(row, row.problem_word)
        word_line = f"תחילת השורה: {shown_first}"
        if row.problem_word and row.problem_word != row.first_word:
            word_line += f"     מילה בעייתית: {shown_problem}"
        if row.problem_type:
            word_line += f"     סוג הבעיה: {row.problem_type}"
        if row.description:
            word_line += f"     תיאור: {row.description}"
        self.current_banner.set(f"{detail_line}\n{word_line}")
        self._set_remaining_banner(remaining_rows, remaining_pages, remaining_report_sheets)
        try:
            page_number = row.source_pdf_page
            self.preview_page_number = page_number
            self._update_page_navigation_buttons()
            original = self.preview_cache.get(page_number)
            if original is None:
                document = pdfium.PdfDocument(str(self.pdf_path))
                try:
                    page = document[page_number - 1]
                    bitmap = page.render(scale=120 / 72.0)
                    original = bitmap.to_pil().convert("RGB")
                    page.close()
                finally:
                    document.close()
                self.preview_cache[page_number] = original
                if len(self.preview_cache) > 4:
                    oldest = next(iter(self.preview_cache))
                    if oldest != page_number:
                        self.preview_cache.pop(oldest, None)

            dimmed = Image.blend(original, Image.new("RGB", original.size, "#CBB994"), 0.60)
            left = max(0, int(row.row_left * original.width))
            top = max(0, int(row.row_top * original.height))
            right = min(original.width, int(row.row_right * original.width))
            bottom = min(original.height, int(row.row_bottom * original.height))
            if right > left and bottom > top:
                clear_row = original.crop((left, top, right, bottom))
                marker = Image.blend(clear_row, Image.new("RGB", clear_row.size, "#FFD84D"), 0.34)
                dimmed.paste(marker, (left, top, right, bottom))

            self.preview_base_image = dimmed
            self.preview_focus_y = ((top + bottom) / 2) / max(1, original.height)
            self._render_preview()
        except Exception:
            self.preview_canvas.delete("all")
            self.preview_canvas.create_text(
                220, 280, text="לא ניתן להציג את העמוד", fill="white", font=("Arial", 13)
            )

    def _render_preview(self) -> None:
        if self.preview_base_image is None:
            self.preview_image_bounds = None
            return
        canvas_width = max(120, self.preview_canvas.winfo_width())
        canvas_height = max(120, self.preview_canvas.winfo_height())
        source = self.preview_base_image
        fit_scale = min((canvas_width - 10) / source.width, (canvas_height - 10) / source.height)
        scale = max(0.05, fit_scale * self.zoom_factor)
        image_width = max(1, int(source.width * scale))
        image_height = max(1, int(source.height * scale))
        display = source.resize((image_width, image_height), Image.Resampling.LANCZOS)
        self.preview_photo = ImageTk.PhotoImage(display)

        scroll_width = max(canvas_width, image_width)
        scroll_height = max(canvas_height, image_height)
        image_x = max(0, (canvas_width - image_width) // 2)
        image_y = max(0, (canvas_height - image_height) // 2)
        self.preview_image_bounds = (image_x, image_y, image_width, image_height)
        self.preview_canvas.delete("all")
        self.preview_canvas.create_image(image_x, image_y, image=self.preview_photo, anchor="nw")
        self.preview_canvas.configure(scrollregion=(0, 0, scroll_width, scroll_height))
        self.preview_canvas.configure(cursor="hand2")

        if scroll_width > canvas_width:
            self.preview_canvas.xview_moveto((scroll_width - canvas_width) / (2 * scroll_width))
        else:
            self.preview_canvas.xview_moveto(0)
        if scroll_height > canvas_height:
            focus_pixel = image_y + self.preview_focus_y * image_height
            fraction = (focus_pixel - canvas_height / 2) / max(1, scroll_height)
            maximum = max(0.0, 1.0 - canvas_height / scroll_height)
            self.preview_canvas.yview_moveto(max(0.0, min(maximum, fraction)))
        else:
            self.preview_canvas.yview_moveto(0)

    def _set_zoom(self, value: float) -> None:
        self.zoom_factor = max(0.60, min(4.0, value))
        self.zoom_text.set(f"{int(round(self.zoom_factor * 100))}%")
        self._render_preview()

    def zoom_in(self) -> None:
        self._set_zoom(self.zoom_factor + 0.20)

    def zoom_out(self) -> None:
        self._set_zoom(self.zoom_factor - 0.20)

    def zoom_fit(self) -> None:
        self._set_zoom(1.0)

    def _ctrl_mousewheel(self, event) -> str:
        if event.delta > 0:
            self.zoom_in()
        elif event.delta < 0:
            self.zoom_out()
        return "break"

    def _preview_mousewheel(self, event) -> str:
        if event.state & 0x0004:
            return self._ctrl_mousewheel(event)
        direction = -1 if event.delta > 0 else 1
        if event.state & 0x0001:
            self.preview_canvas.xview_scroll(direction, "units")
        else:
            self.preview_canvas.yview_scroll(direction, "units")
        return "break"

    def _preview_pan_start(self, event) -> None:
        self.preview_pan_origin = (event.x, event.y)
        self.preview_was_dragged = False
        self.preview_canvas.scan_mark(event.x, event.y)
        self.preview_canvas.configure(cursor="fleur")

    def _preview_pan_move(self, event) -> None:
        if self.preview_pan_origin is None:
            return
        distance = abs(event.x - self.preview_pan_origin[0]) + abs(event.y - self.preview_pan_origin[1])
        if distance < 6 and not self.preview_was_dragged:
            return
        self.preview_was_dragged = True
        self.preview_canvas.scan_dragto(event.x, event.y, gain=1)

    def _preview_pan_end(self, event=None) -> None:
        was_dragged = self.preview_was_dragged
        self.preview_pan_origin = None
        self.preview_was_dragged = False
        self.preview_canvas.configure(cursor="hand2" if self.preview_base_image is not None else "")
        if not was_dragged and event is not None:
            self._select_row_from_preview(event)

    def _row_index_at_preview_position(self, normalized_x: float, normalized_y: float) -> int | None:
        candidates: list[tuple[float, int]] = []
        for index, row in enumerate(self.rows):
            if row.source_pdf_page != self.preview_page_number:
                continue
            if not (row.row_left <= normalized_x <= row.row_right):
                continue
            if row.row_top <= normalized_y <= row.row_bottom:
                center = (row.row_top + row.row_bottom) / 2
                candidates.append((abs(normalized_y - center), index))
        if not candidates:
            return None
        return min(candidates)[1]

    def _select_row_from_preview(self, event) -> None:
        if not self.rows or self.preview_image_bounds is None:
            return
        image_x, image_y, image_width, image_height = self.preview_image_bounds
        canvas_x = self.preview_canvas.canvasx(event.x)
        canvas_y = self.preview_canvas.canvasy(event.y)
        if image_width <= 0 or image_height <= 0:
            return
        normalized_x = (canvas_x - image_x) / image_width
        normalized_y = (canvas_y - image_y) / image_height
        if not (0.0 <= normalized_x <= 1.0 and 0.0 <= normalized_y <= 1.0):
            return
        index = self._row_index_at_preview_position(normalized_x, normalized_y)
        if index is None:
            self.status.set("לא נמצאה שורה במקום שנלחץ")
            return
        self.select_index(index)
        self.speak_current(include_header=True, repeat=False)

    def _preview_resized(self, _event=None) -> None:
        if self.preview_resize_job:
            self.root.after_cancel(self.preview_resize_job)
        self.preview_resize_job = self.root.after(100, self._render_preview)

    def save_edit(self, learn: bool = False) -> None:
        selection = self.tree.selection()
        if not selection:
            return
        index = int(selection[0])
        row = self.rows[index]
        ensure_ocr_baseline(row)
        old_values = {
            name: getattr(row, name) for name in self.editor_vars
        }
        new_values = {
            name: clean_hebrew_text(variable.get())
            for name, variable in self.editor_vars.items()
        }
        for name in ("start", "first_word", "problem_word"):
            new_values[name] = restore_divine_names_from_display(new_values[name])
        new_values["problem_type"] = normalize_problem_type(new_values["problem_type"])
        new_values["description"] = normalize_report_description(
            new_values["description"], row.report_kind,
        )

        if old_values["first_word"] == old_values["problem_word"]:
            first_changed = new_values["first_word"] != old_values["first_word"]
            problem_changed = new_values["problem_word"] != old_values["problem_word"]
            if first_changed and not problem_changed:
                new_values["problem_word"] = new_values["first_word"]
                self.editor_vars["problem_word"].set(new_values["problem_word"])
            elif problem_changed and not first_changed:
                new_values["first_word"] = new_values["problem_word"]
                self.editor_vars["first_word"].set(new_values["first_word"])

        baseline_names = {
            "start": "ocr_start",
            "first_word": "ocr_first_word",
            "problem_word": "ocr_problem_word",
            "problem_type": "ocr_problem_type",
            "description": "ocr_description",
        }
        manual_names = {
            "start": "manual_start",
            "first_word": "manual_first_word",
            "problem_word": "manual_problem_word",
            "problem_type": "manual_problem_type",
            "description": "manual_description",
        }
        learned_pairs: set[tuple[str, str, str]] = set()
        for name, value in new_values.items():
            setattr(row, name, value)
            if name in manual_names and value != old_values[name]:
                setattr(row, manual_names[name], value)
            if learn and name in LEARNED_RULE_SCOPES:
                wrong = getattr(row, baseline_names[name])
                if _correction_key(wrong) != _correction_key(value) and wrong and value:
                    learned_pairs.add((LEARNED_RULE_SCOPES[name], wrong, value))

        learned_count = 0
        if learn:
            for scope, wrong, correct in sorted(learned_pairs):
                if add_learned_rule(scope, wrong, correct):
                    learned_count += 1

        self._refresh_rows_after_learning_change()
        if self.pdf_path:
            try:
                write_ocr_cache(self.pdf_path, self.rows)
            except Exception:
                pass
            self._start_private_avri_library_preparation(self.pdf_path, self.rows)
        if learn and learned_pairs:
            if learned_count:
                examples = ", ".join(f"{wrong} ← {correct}" for _scope, wrong, correct in sorted(learned_pairs))
                self.status.set(f"התיקון נשמר וה-OCR למד: {examples}")
            else:
                self.status.set("התיקון נשמר - כלל הלימוד כבר היה קיים")
        elif learn:
            self.status.set("התיקון נשמר, אך לא נמצא שינוי מתאים ללימוד")
        else:
            self.status.set("התיקון נשמר לשורה הזאת")

    def select_index(self, index: int) -> None:
        if not self.rows:
            return
        self.current_index = max(0, min(index, len(self.rows) - 1))
        iid = str(self.current_index)
        if not self.tree.exists(iid):
            # Keyboard/reading navigation always follows the original report order.
            # Reveal the target if a table-only filter currently hides it.
            self.issue_filter.set("הכול")
            self._refresh_result_rows()
        self.tree.selection_set(iid)
        self.tree.focus(iid)
        self.tree.see(iid)
        self.load_selected()

    def _report_pdf_pages(self) -> list[int]:
        return sorted({row.source_pdf_page for row in self.rows if row.source_pdf_page > 0})

    def _update_page_navigation_buttons(self) -> None:
        if not hasattr(self, "previous_page_button"):
            return
        pages = self._report_pdf_pages()
        if not pages:
            self.previous_page_button.state(["disabled"])
            self.next_page_button.state(["disabled"])
            return
        current_page = self.preview_page_number
        if 0 <= self.current_index < len(self.rows):
            current_page = self.rows[self.current_index].source_pdf_page or current_page
        try:
            page_position = pages.index(current_page)
        except ValueError:
            page_position = 0
        self.previous_page_button.state(
            ["!disabled"] if page_position > 0 else ["disabled"],
        )
        self.next_page_button.state(
            ["!disabled"] if page_position < len(pages) - 1 else ["disabled"],
        )

    def navigate_report_page(self, direction: int) -> None:
        pages = self._report_pdf_pages()
        if not pages:
            return
        current_page = self.preview_page_number
        if 0 <= self.current_index < len(self.rows):
            current_page = self.rows[self.current_index].source_pdf_page or current_page
        try:
            page_position = pages.index(current_page)
        except ValueError:
            page_position = 0
        target_position = max(0, min(len(pages) - 1, page_position + (1 if direction > 0 else -1)))
        target_page = pages[target_position]
        for index, row in enumerate(self.rows):
            if row.source_pdf_page == target_page:
                self.select_index(index)
                self.status.set(
                    f"עבר לעמוד {row.page or target_page} — שורה {row.line or index + 1}"
                )
                break
        self._update_page_navigation_buttons()

    @staticmethod
    def _format_storage_size(byte_count: int) -> str:
        amount = max(0.0, float(byte_count))
        for unit in ("בתים", "KB", "MB", "GB"):
            if amount < 1024.0 or unit == "GB":
                return f"{amount:.0f} {unit}" if unit in {"בתים", "KB"} else f"{amount:.1f} {unit}"
            amount /= 1024.0
        return f"{amount:.1f} GB"

    @staticmethod
    def _safe_folder_component(value: str, fallback: str = "ללא שם") -> str:
        cleaned = unicodedata.normalize("NFC", str(value)).strip()
        cleaned = re.sub(r'[<>:"/\\|?*\x00-\x1f]', " ", cleaned)
        cleaned = re.sub(r"\s+", " ", cleaned).strip(" .")
        return (cleaned or fallback)[:90]

    @staticmethod
    def _link_recorded_clip(source: Path, target: Path) -> None:
        if not SpeechWorker._valid_cached_clip(source):
            return
        target.parent.mkdir(parents=True, exist_ok=True)
        try:
            if target.exists() and os.path.samefile(source, target):
                return
        except OSError:
            pass
        temporary = target.with_name(f".{target.name}.{uuid.uuid4().hex}.tmp")
        try:
            try:
                os.link(source, temporary)
            except OSError:
                shutil.copy2(source, temporary)
            os.replace(temporary, target)
        finally:
            temporary.unlink(missing_ok=True)

    def open_private_avri_library_folder(self) -> None:
        if CUSTOMER_EDITION:
            return
        folder = self.speech._recorded_avri_root()
        try:
            os.startfile(str(folder))  # type: ignore[attr-defined]
        except OSError as error:
            messagebox.showerror(APP_NAME, f"לא ניתן לפתוח את התיקייה:\n{error}")

    def _start_private_avri_library_preparation(
        self, pdf_path: Path, rows: list[ReportRow], force: bool = False,
    ) -> None:
        """Prepare all reusable Avri parts without delaying OCR or the UI."""
        if (
            CUSTOMER_EDITION or not rows
            or (not force and not self.avri_library_enabled)
        ):
            return
        self.avri_library_cancel.set()
        self.avri_library_generation += 1
        generation = self.avri_library_generation
        cancel = threading.Event()
        self.avri_library_cancel = cancel
        row_plan = [
            {
                "index": index,
                "page_label": row.page.strip() or str(row.source_pdf_page or index + 1),
                "line_label": row.line.strip() or str(index + 1),
                "data": self.recorded_avri_row_data(row),
            }
            for index, row in enumerate(rows)
        ]

        def worker() -> None:
            root = self.speech._recorded_avri_root()
            try:
                pdf_identity = hashlib.sha256(str(pdf_path.resolve()).encode("utf-8")).hexdigest()[:10]
            except OSError:
                pdf_identity = hashlib.sha256(str(pdf_path).encode("utf-8")).hexdigest()[:10]
            report_name = self._safe_folder_component(pdf_path.stem, "דוח")
            report_root = root / "דוחות" / f"{report_name}--{pdf_identity}"

            report_parts: list[str] = []
            for item in row_plan:
                data = item["data"]
                if isinstance(data, dict):
                    report_parts.extend(str(data.get(key, "")) for key in (
                        "page", "start", "line", "first_word", "issue",
                    ))
            all_parts = list(dict.fromkeys(
                part for part in (
                    report_parts
                    + ["שורה", "סוף", "סיום דוח"]
                    + [str(number) for number in range(1, 246)]
                )
                if part
            ))
            total = len(all_parts)
            existing = sum(
                1 for part in all_parts
                if self.speech._valid_cached_clip(self.speech._recorded_avri_cache_path(part))
            )
            completed = existing
            self.root.after(
                0, self._avri_library_progress, generation, completed, total,
                "מכין את ספריית אברי ברקע",
            )
            pending = [
                part for part in all_parts
                if not self.speech._valid_cached_clip(self.speech._recorded_avri_cache_path(part))
            ]
            for offset in range(0, len(pending), 8):
                if cancel.is_set():
                    return
                batch = pending[offset:offset + 8]
                self.speech.prepare_quality_clips(batch, 0, RECORDED_AVRI_VOICE)
                completed += sum(
                    1 for part in batch
                    if self.speech._valid_cached_clip(self.speech._recorded_avri_cache_path(part))
                )
                self.root.after(
                    0, self._avri_library_progress, generation, completed, total,
                    "מוריד הקלטות אברי",
                )
            if cancel.is_set():
                return

            # A readable fixed library, in addition to the content-addressed
            # cache used by the player.
            for number in range(1, 246):
                source = self.speech._recorded_avri_cache_path(str(number))
                self._link_recorded_clip(
                    source, root / "קבוע" / "מספרי עמודים" / f"{number:03d}.mp3",
                )
                self._link_recorded_clip(
                    source, root / "קבוע" / "מספרי שורות" / f"{number:03d}.mp3",
                )
            for constant in ("שורה", "סוף", "סיום דוח"):
                self._link_recorded_clip(
                    self.speech._recorded_avri_cache_path(constant),
                    root / "קבוע" / "מילים קבועות" /
                    f"{self._safe_folder_component(constant)}.mp3",
                )

            issue_texts = sorted({
                str(item["data"].get("issue", ""))
                for item in row_plan if isinstance(item.get("data"), dict)
                and str(item["data"].get("issue", ""))
            })
            for issue in issue_texts:
                self._link_recorded_clip(
                    self.speech._recorded_avri_cache_path(issue),
                    root / "קבוע" / "תיאורי בעיה" /
                    f"{self._safe_folder_component(issue, 'תיאור')}.mp3",
                )

            manifest_rows: list[dict[str, object]] = []
            page_starts: dict[str, list[str]] = {}
            line_occurrences: dict[tuple[str, str], int] = {}
            for item in row_plan:
                page_label = str(item["page_label"])
                line_label = str(item["line_label"])
                data = item["data"]
                if not isinstance(data, dict):
                    continue
                page_dir = report_root / self._safe_folder_component(f"עמוד {page_label}")
                start = str(data.get("start", ""))
                starts = page_starts.setdefault(page_label, [])
                if start and start not in starts:
                    starts.append(start)
                    suffix = "" if len(starts) == 1 else f" {len(starts):02d}"
                    self._link_recorded_clip(
                        self.speech._recorded_avri_cache_path(start),
                        page_dir / f"תחילת עמוד{suffix}.mp3",
                    )
                key = (page_label, line_label)
                line_occurrences[key] = line_occurrences.get(key, 0) + 1
                duplicate = line_occurrences[key]
                line_name = f"שורה {line_label}" + (f" - {duplicate:02d}" if duplicate > 1 else "")
                line_dir = page_dir / self._safe_folder_component(line_name)
                targets = {
                    "מספר שורה.mp3": str(data.get("line", "")),
                    "תחילת שורה.mp3": str(data.get("first_word", "")),
                    "תיאור הבעיה.mp3": str(data.get("issue", "")),
                }
                for file_name, text_value in targets.items():
                    if text_value:
                        self._link_recorded_clip(
                            self.speech._recorded_avri_cache_path(text_value),
                            line_dir / file_name,
                        )
                manifest_rows.append({
                    "index": int(item["index"]), "page": page_label,
                    "line": line_label, "folder": str(line_dir.relative_to(report_root)),
                    "start": start, "first_word": str(data.get("first_word", "")),
                    "issue": str(data.get("issue", "")),
                })
            manifest = {
                "version": 1,
                "source_pdf": str(pdf_path),
                "created_at": datetime.now().isoformat(timespec="seconds"),
                "voice": RECORDED_AVRI_EDGE_VOICE,
                "note": "המילה הבעייתית נוצרת לפי הצורך ואינה חלק מההכנה האוטומטית",
                "rows": manifest_rows,
            }
            report_root.mkdir(parents=True, exist_ok=True)
            manifest_path = report_root / "תוכן הספרייה.json"
            temporary = manifest_path.with_suffix(".json.tmp")
            temporary.write_text(
                json.dumps(manifest, ensure_ascii=False, indent=2), encoding="utf-8",
            )
            temporary.replace(manifest_path)
            self.root.after(0, self._avri_library_finished, generation, report_root, total, "")
        
        def guarded_worker() -> None:
            try:
                worker()
            except Exception as error:
                if not cancel.is_set():
                    self.root.after(
                        0, self._avri_library_finished, generation,
                        self.speech._recorded_avri_root(), 0, str(error),
                    )

        self.avri_library_thread = threading.Thread(
            target=guarded_worker, name="duk-avri-library", daemon=True,
        )
        self.avri_library_thread.start()

    def _avri_library_progress(
        self, generation: int, completed: int, total: int, label: str,
    ) -> None:
        if generation != self.avri_library_generation:
            return
        percentage = completed / max(1, total) * 100
        self.progress_value.set(percentage)
        self.status.set(f"{label}: {completed} מתוך {total} — הדוח כבר זמין לעבודה")

    def _avri_library_finished(
        self, generation: int, folder: Path, total: int, error: str,
    ) -> None:
        if generation != self.avri_library_generation:
            return
        if error:
            self.status.set(
                "הדוח מוכן. ספריית אברי תמשיך בפעם הבאה כשיהיה חיבור לאינטרנט"
            )
            return
        self.progress_value.set(100)
        self.status.set(
            f"ספריית אברי מוכנה — {total} קטעים נשמרו בתיקייה {folder.name}"
        )

    @staticmethod
    def _voice_id_for_choice(choice: str) -> str:
        choice = str(choice)
        if choice.startswith("Piper עברי SASpeech"):
            return "local-saspeech"
        if choice.startswith("מיכאל"):
            return "local-michael"
        if choice.startswith("שאול"):
            return "local-shaul"
        if choice.startswith("אברי מוקלט"):
            return RECORDED_AVRI_VOICE
        if choice.startswith("אברי"):
            return "he-IL-AvriNeural"
        if choice.startswith("אסף"):
            return "offline"
        return "he-IL-HilaNeural"

    def _bulk_page_options(self) -> list[tuple[str, int]]:
        options: list[tuple[str, int]] = []
        seen: set[str] = set()
        for index, row in enumerate(self.rows):
            label = row.page.strip() or (
                f"עמוד PDF {row.source_pdf_page}" if row.source_pdf_page > 0 else f"שורה {index + 1}"
            )
            if label in seen:
                continue
            seen.add(label)
            options.append((label, index))
        return options

    def _bulk_export_folder(self, pdf_path: Path | None = None) -> Path | None:
        source = pdf_path or self.pdf_path
        if source is None:
            return None
        report_name = self._safe_folder_component(source.stem, "דוח")
        return source.parent / "הקלטות דוחות" / report_name

    @staticmethod
    def _bulk_export_manifest_path(folder: Path) -> Path:
        return folder / "פרטי ההקלטות.json"

    def _load_bulk_export_manifest(self, folder: Path) -> dict:
        try:
            value = json.loads(
                self._bulk_export_manifest_path(folder).read_text(encoding="utf-8")
            )
        except (OSError, ValueError, TypeError):
            value = {}
        if not isinstance(value, dict):
            value = {}
        entries = value.get("entries")
        if not isinstance(entries, dict):
            value["entries"] = {}
        return value

    def _save_bulk_export_manifest(
        self, folder: Path, manifest: dict, source_pdf: Path | None = None,
    ) -> None:
        folder.mkdir(parents=True, exist_ok=True)
        manifest["version"] = 1
        manifest["updated_at"] = datetime.now().isoformat(timespec="seconds")
        report_source = source_pdf or self.pdf_path
        if report_source is not None:
            manifest["source_pdf"] = str(report_source)
        target = self._bulk_export_manifest_path(folder)
        temporary = target.with_suffix(".json.tmp")
        temporary.write_text(
            json.dumps(manifest, ensure_ascii=False, indent=2), encoding="utf-8",
        )
        temporary.replace(target)

    def _bulk_export_items(
        self, start_index: int, voice: str, rate: int,
        pdf_path: Path | None = None,
    ) -> list[dict[str, object]]:
        folder = self._bulk_export_folder(pdf_path)
        if folder is None:
            return []
        manifest = self._load_bulk_export_manifest(folder)
        manifest_entries = manifest.get("entries", {})
        if not isinstance(manifest_entries, dict):
            manifest_entries = {}
        occurrences: dict[str, int] = {}
        items: list[dict[str, object]] = []
        extension = ".wav" if voice.startswith("local-") else ".mp3"
        for index in range(start_index, len(self.rows)):
            row = self.rows[index]
            page_label = row.page.strip()
            if page_label.isdigit():
                page_label = f"{int(page_label):03d}"
            elif not page_label:
                page_label = f"{max(1, row.source_pdf_page or index + 1):03d}"
            problem_label = display_report_text(
                row, row.problem_word or row.first_word or "ללא מילה",
            )
            base_name = self._safe_folder_component(
                f"{page_label} - {problem_label}", f"{page_label} - הקלטה",
            )
            occurrences[base_name] = occurrences.get(base_name, 0) + 1
            duplicate = occurrences[base_name]
            file_stem = base_name + (f" - {duplicate:02d}" if duplicate > 1 else "")
            target = folder / f"{file_stem}{extension}"
            include_header = self.is_group_start(index)
            speech_parts = self.build_row_speech_parts(
                index, include_header=include_header, repeat=False, voice=None,
            )
            full_text = ". ".join(
                part.strip(" .,;") for part in speech_parts if part.strip(" .,;")
            )
            signature = hashlib.sha256(
                f"export-v1\0{voice}\0{rate}\0{full_text}".encode("utf-8")
            ).hexdigest()
            entry = manifest_entries.get(str(index), {})
            valid = bool(
                isinstance(entry, dict)
                and entry.get("file") == target.name
                and entry.get("signature") == signature
                and self.speech._valid_cached_clip(target)
            )
            items.append({
                "index": index, "page": page_label, "problem_word": problem_label,
                "text": full_text, "path": target, "signature": signature,
                "voice": voice, "rate": rate, "include_header": include_header,
                "valid": valid,
            })
        return items

    def open_bulk_export_folder(self) -> None:
        folder = self._bulk_export_folder()
        if folder is None:
            return
        folder.mkdir(parents=True, exist_ok=True)
        try:
            os.startfile(str(folder))  # type: ignore[attr-defined]
        except OSError as error:
            messagebox.showerror(APP_NAME, f"לא ניתן לפתוח את התיקייה:\n{error}")

    def _saved_export_for_row(
        self, index: int, include_header: bool, repeat: bool,
        voice: str, rate: int,
    ) -> Path | None:
        if repeat or not (0 <= index < len(self.rows)):
            return None
        for item in self._bulk_export_items(0, voice, rate):
            if int(item["index"]) != index:
                continue
            if bool(item["include_header"]) != bool(include_header):
                return None
            path = item["path"]
            if bool(item["valid"]) and isinstance(path, Path):
                return path
            return None
        return None

    def _bulk_speech_inventory(
        self, start_index: int, voice: str,
    ) -> list[tuple[str, str]]:
        candidates: list[tuple[str, str]] = []
        if voice == RECORDED_AVRI_VOICE:
            candidates.extend(
                ("מספרים לעמודים ולשורות", str(number))
                for number in range(1, 246)
            )
            candidates.extend(("מילים קבועות", value) for value in (
                "שורה", "סוף", "סיום דוח",
            ))
            for index in range(start_index, len(self.rows)):
                row = self.rows[index]
                data = self.recorded_avri_row_data(row)
                candidates.extend(("מספרים נוספים", value) for value in (
                    data["page"], data["line"],
                ) if value and not (value.isdigit() and 1 <= int(value) <= 245))
                if self.is_group_start(index) and data["start"]:
                    candidates.append(("תחילות עמוד", data["start"]))
                if data["first_word"]:
                    candidates.append(("תחילות שורה", data["first_word"]))
                if data["issue"]:
                    candidates.append(("תיאורי בעיה", data["issue"]))
                if (
                    row.problem_word and row.problem_word != row.first_word
                    and data["problem_word"]
                ):
                    candidates.append(("מילים בעייתיות", data["problem_word"]))
        else:
            for index in range(start_index, len(self.rows)):
                for part in self.build_row_speech_parts(
                    index, include_header=self.is_group_start(index),
                    repeat=False, voice=voice,
                ):
                    candidates.append(("הקראות מלאות", part))

        inventory: list[tuple[str, str]] = []
        seen_paths: set[str] = set()
        rate = int(round(self.speed.get()))
        for category, part in candidates:
            if not part or part == RECORDED_AVRI_GAP_MARKER:
                continue
            path = self.speech.quality_cache_path(part, rate, voice)
            path_key = os.path.normcase(str(path))
            if path_key in seen_paths:
                continue
            seen_paths.add(path_key)
            inventory.append((category, part))
        return inventory

    def _bulk_speech_parts(self, start_index: int) -> list[str]:
        voice = self._voice_id_for_choice(str(
            self.bulk_download_state.get("voice_choice", self.voice_choice.get())
        ))
        return [
            part for _category, part
            in self._bulk_speech_inventory(start_index, voice)
        ]

    def open_bulk_speech_download(self) -> None:
        if CUSTOMER_EDITION:
            return
        if not self.rows or self.pdf_path is None:
            messagebox.showinfo(APP_NAME, "תחילה יש לפתוח דוח ולהמתין לסיום הזיהוי.")
            return
        if self.bulk_download_dialog is not None:
            try:
                if self.bulk_download_dialog.winfo_exists():
                    self.bulk_download_dialog.deiconify()
                    self.bulk_download_dialog.lift()
                    return
            except tk.TclError:
                pass
            self.bulk_download_dialog = None

        dialog = tk.Toplevel(self.root)
        self.bulk_download_dialog = dialog
        dialog.title("הורדת כל ההקראות של הדוח")
        fit_window_to_work_area(dialog, 780, 900, 640, 700)
        dialog.transient(self.root)
        dialog.configure(bg="#E7D4AB")
        try:
            dialog.iconbitmap(default=str(resource_path("app.ico")))
        except Exception:
            pass

        tk.Label(
            dialog, text="הורדת כל ההקראות למחשב", bg="#5A3518", fg="white",
            font=("Segoe UI", 17, "bold"), pady=14,
        ).pack(fill="x")
        tk.Label(
            dialog,
            text="התוכנה מכינה את כל שורות הדוח ושומרת גם קובץ מלא לכל שורה בתיקייה על שם הדוח.\n"
                 "לאחר ההורדה התוכנה תעדיף את הקבצים המקומיים גם כשיש אינטרנט.",
            bg="#FFF9EC", fg="#74471F", font=("Segoe UI", 10),
            justify="right", anchor="e", padx=16, pady=11,
        ).pack(fill="x", padx=18, pady=(14, 8))

        page_options = self._bulk_page_options()
        page_to_index = dict(page_options)
        default_page = page_options[0][0]
        if 0 <= self.current_index < len(self.rows):
            current = self.rows[self.current_index]
            current_label = current.page.strip() or (
                f"עמוד PDF {current.source_pdf_page}" if current.source_pdf_page > 0 else default_page
            )
            if current_label in page_to_index:
                default_page = current_label
        quality_choices = tuple(
            choice for choice in VOICE_CHOICES if not choice.startswith("אסף")
        )
        selected_quality = self.voice_choice.get()
        if selected_quality not in quality_choices:
            selected_quality = "הילה - איכותי אונליין"
        start_page_var = tk.StringVar(value=default_page)
        voice_var = tk.StringVar(value=selected_quality)
        estimate_var = tk.StringVar()
        export_folder = self._bulk_export_folder()
        export_folder_var = tk.StringVar(value=(
            f"תיקיית הקבצים: {export_folder}" if export_folder is not None else ""
        ))
        progress_text = tk.StringVar(value="מוכן לחישוב ולהורדה")
        progress_var = tk.DoubleVar(value=0)

        selectors = tk.Frame(dialog, bg="#FFF9EC", padx=15, pady=12)
        selectors.pack(fill="x", padx=18)
        tk.Label(
            selectors, text="התחלה מעמוד", bg="#FFF9EC", fg="#332315",
            font=("Segoe UI", 10, "bold"), anchor="e",
        ).grid(row=0, column=2, sticky="e", padx=7, pady=7)
        page_picker = ttk.Combobox(
            selectors, textvariable=start_page_var,
            values=tuple(label for label, _index in page_options),
            state="readonly", justify="right", width=24,
        )
        page_picker.grid(row=0, column=1, sticky="ew", padx=7, pady=7)
        tk.Label(
            selectors, text="קול איכותי", bg="#FFF9EC", fg="#332315",
            font=("Segoe UI", 10, "bold"), anchor="e",
        ).grid(row=1, column=2, sticky="e", padx=7, pady=7)
        voice_picker = ttk.Combobox(
            selectors, textvariable=voice_var, values=quality_choices,
            state="readonly", justify="right", width=24,
        )
        voice_picker.grid(row=1, column=1, sticky="ew", padx=7, pady=7)
        selectors.columnconfigure(1, weight=1)

        tk.Label(
            dialog, textvariable=export_folder_var, bg="#FFF9EC", fg="#74471F",
            font=("Segoe UI", 9, "bold"), justify="right", anchor="e",
            padx=14, pady=8, wraplength=700,
        ).pack(fill="x", padx=18, pady=(8, 0))

        estimate_label = tk.Label(
            dialog, textvariable=estimate_var, bg="#F6D878", fg="#332315",
            font=("Segoe UI", 10, "bold"), justify="right", anchor="e",
            padx=14, pady=12, wraplength=610,
        )
        estimate_label.pack(fill="x", padx=18, pady=(9, 8))
        statistics_card = tk.Frame(dialog, bg="#FFF9EC", padx=12, pady=10)
        statistics_card.pack(fill="both", expand=True, padx=18, pady=(0, 8))
        tk.Label(
            statistics_card, text="מה כבר קיים ומה עדיין חסר", bg="#FFF9EC",
            fg="#5A3518", font=("Segoe UI", 11, "bold"), anchor="e",
        ).pack(fill="x", pady=(0, 7))
        statistics_tree = ttk.Treeview(
            statistics_card,
            columns=("category", "total", "existing", "missing", "remaining"),
            show="headings", height=5, selectmode="none",
        )
        for column, title, width, anchor in (
            ("category", "סוג הקלטה", 225, "e"),
            ("total", "סה״כ", 70, "center"),
            ("existing", "קיים", 70, "center"),
            ("missing", "חסר", 70, "center"),
            ("remaining", "נפח חסר", 105, "center"),
        ):
            statistics_tree.heading(column, text=title)
            statistics_tree.column(column, width=width, minwidth=55, anchor=anchor, stretch=True)
        statistics_scroll = ttk.Scrollbar(
            statistics_card, orient="vertical", command=statistics_tree.yview,
        )
        statistics_tree.configure(yscrollcommand=statistics_scroll.set)
        statistics_scroll.pack(side="left", fill="y")
        statistics_tree.pack(fill="both", expand=True)
        progress_card = tk.Frame(dialog, bg="#FFF9EC", padx=14, pady=12)
        progress_card.pack(fill="x", padx=18)
        ttk.Progressbar(
            progress_card, variable=progress_var, maximum=100,
            style="Reader.Horizontal.TProgressbar",
        ).pack(fill="x", pady=(0, 9))
        tk.Label(
            progress_card, textvariable=progress_text, bg="#FFF9EC", fg="#5A3518",
            font=("Segoe UI", 10, "bold"), anchor="e", justify="right",
        ).pack(fill="x")

        buttons = tk.Frame(dialog, bg="#E7D4AB")
        buttons.pack(fill="x", padx=18, pady=14)
        start_button = tk.Button(
            buttons, text="התחלת הורדה", bg="#278552", fg="white",
            activebackground="#1F6B42", activeforeground="white", relief="flat",
            font=("Segoe UI", 11, "bold"), padx=24, pady=9,
        )
        start_button.pack(side="right", padx=5)
        cancel_button = tk.Button(
            buttons, text="ביטול הורדה", bg="#F6D878", fg="#5A3518",
            activebackground="#E8C65B", relief="flat", font=("Segoe UI", 10, "bold"),
            padx=18, pady=9, state="disabled",
        )
        cancel_button.pack(side="right", padx=5)
        close_button = tk.Button(
            buttons, text="סגירת החלון", bg="#F1E2C4", fg="#5A3518",
            activebackground="#E5CF9F", relief="flat", font=("Segoe UI", 10, "bold"),
            padx=18, pady=9,
        )
        close_button.pack(side="left", padx=5)
        library_button = tk.Button(
            buttons, text="פתיחת תיקיית אברי", bg="#F1E2C4", fg="#5A3518",
            activebackground="#E5CF9F", relief="flat", font=("Segoe UI", 10, "bold"),
            padx=14, pady=9, command=self.open_private_avri_library_folder,
        )
        library_button.pack(side="left", padx=5)
        report_folder_button = tk.Button(
            buttons, text="תיקיית הדוח", bg="#F1E2C4", fg="#5A3518",
            activebackground="#E5CF9F", relief="flat", font=("Segoe UI", 10, "bold"),
            padx=12, pady=9, command=self.open_bulk_export_folder,
        )
        report_folder_button.pack(side="left", padx=5)

        ui = {
            "dialog": dialog, "progress": progress_var, "progress_text": progress_text,
            "estimate": estimate_var, "start_button": start_button,
            "cancel_button": cancel_button, "page_picker": page_picker,
            "voice_picker": voice_picker,
        }
        self.bulk_download_state["ui"] = ui

        def calculate_estimate(*_args) -> dict[str, object]:
            start_index = page_to_index.get(start_page_var.get(), 0)
            voice_choice = voice_var.get()
            voice = self._voice_id_for_choice(voice_choice)
            rate = int(round(self.speed.get()))
            self.bulk_download_state["voice_choice"] = voice_choice
            inventory = self._bulk_speech_inventory(start_index, voice)
            parts = [part for _category, part in inventory]
            internal_paths = [
                self.speech.quality_cache_path(part, rate, voice) for part in parts
            ]
            export_items = self._bulk_export_items(start_index, voice, rate)
            export_paths = [
                item["path"] for item in export_items if isinstance(item.get("path"), Path)
            ]
            cached_bytes = 0
            remaining_bytes = 0
            cached_count = 0
            category_stats: dict[str, dict[str, int]] = {}
            for (category, part), path in zip(inventory, internal_paths):
                values = category_stats.setdefault(
                    category, {"total": 0, "existing": 0, "missing": 0, "remaining": 0},
                )
                values["total"] += 1
                if self.speech._valid_cached_clip(path):
                    cached_count += 1
                    values["existing"] += 1
                    try:
                        cached_bytes += path.stat().st_size
                    except OSError:
                        pass
                else:
                    estimated = self.speech.estimated_clip_size(part, voice)
                    remaining_bytes += estimated
                    values["missing"] += 1
                    values["remaining"] += estimated
            export_values = category_stats.setdefault(
                "קבצי הקראה בתיקיית הדוח",
                {"total": 0, "existing": 0, "missing": 0, "remaining": 0},
            )
            for item in export_items:
                export_values["total"] += 1
                path = item.get("path")
                if bool(item.get("valid")) and isinstance(path, Path):
                    cached_count += 1
                    export_values["existing"] += 1
                    try:
                        cached_bytes += path.stat().st_size
                    except OSError:
                        pass
                else:
                    estimated = self.speech.estimated_clip_size(
                        str(item.get("text", "")), voice,
                    )
                    remaining_bytes += estimated
                    export_values["missing"] += 1
                    export_values["remaining"] += estimated
            row_count = max(0, len(self.rows) - start_index)
            total_size = cached_bytes + remaining_bytes
            statistics_tree.delete(*statistics_tree.get_children())
            category_order = (
                "מספרים לעמודים ולשורות", "מילים קבועות", "תחילות עמוד",
                "מספרים נוספים", "תחילות שורה", "תיאורי בעיה",
                "מילים בעייתיות", "הקראות מלאות", "קבצי הקראה בתיקיית הדוח",
            )
            for category in category_order:
                values = category_stats.get(category)
                if not values:
                    continue
                statistics_tree.insert("", "end", values=(
                    category, values["total"], values["existing"], values["missing"],
                    self._format_storage_size(values["remaining"]),
                ))
            estimate_var.set(
                f"{row_count} הקראות · {len(parts)} קטעי מטמון · "
                f"{len(export_items)} קבצים בתיקיית הדוח\n"
                f"גודל כולל משוער: {self._format_storage_size(total_size)}  |  "
                f"כבר במחשב: {self._format_storage_size(cached_bytes)}  |  "
                f"נותר להכין: {self._format_storage_size(remaining_bytes)}"
            )
            return {
                "start_index": start_index, "voice_choice": voice_choice,
                "voice": voice, "rate": rate, "parts": parts,
                "paths": internal_paths, "export_items": export_items,
                "all_paths": internal_paths + export_paths,
                "total_count": len(parts) + len(export_items),
                "cached_count": cached_count, "cached_bytes": cached_bytes,
                "estimated_total": total_size, "row_count": row_count,
                "pdf_path": self.pdf_path, "rows_snapshot": list(self.rows),
            }

        ui["calculate"] = calculate_estimate

        def close_dialog() -> None:
            if bool(self.bulk_download_state.get("active")):
                self.status.set("הורדת ההקראות ממשיכה ברקע")
            self.bulk_download_state.pop("ui", None)
            self.bulk_download_dialog = None
            dialog.destroy()

        def cancel_download() -> None:
            self.bulk_download_cancel.set()
            progress_text.set("מסיים את הקטע הנוכחי ואז עוצר…")
            cancel_button.configure(state="disabled")

        def start_download() -> None:
            if bool(self.bulk_download_state.get("active")):
                return
            plan = calculate_estimate()
            parts = list(plan["parts"])
            total_count = int(plan.get("total_count", len(parts)) or 0)
            if total_count <= 0:
                progress_text.set("לא נמצאו הקראות להכנה מהעמוד שנבחר")
                return
            if not messagebox.askyesno(
                APP_NAME,
                f"להכין {plan['row_count']} הקראות?\n"
                f"הגודל הכולל המשוער הוא {self._format_storage_size(int(plan['estimated_total']))}.",
                parent=dialog,
            ):
                return
            self.bulk_download_cancel.clear()
            if str(plan["voice"]) == RECORDED_AVRI_VOICE:
                self.avri_library_enabled = True
                self._save_settings()
            self.bulk_download_state.update(plan)
            self.bulk_download_state.update(active=True, completed=int(plan["cached_count"]), error="")
            self.speech.pin_report_clips(
                self.pdf_path, parts, int(plan["rate"]), str(plan["voice"]),
            )
            total = max(1, total_count)
            progress_var.set(int(plan["cached_count"]) / total * 100)
            progress_text.set(
                f"מתחיל — {int(plan['cached_count'])} מתוך {total_count} כבר נשמרו במחשב"
            )
            start_button.configure(state="disabled")
            cancel_button.configure(state="normal")
            page_picker.configure(state="disabled")
            voice_picker.configure(state="disabled")
            pdf_for_pack = self.pdf_path

            def worker() -> None:
                all_parts = list(plan["parts"])
                internal_paths = list(plan["paths"])
                all_paths = list(plan["all_paths"])
                export_items = [
                    dict(item) for item in list(plan["export_items"])
                    if isinstance(item, dict)
                ]
                work_total = int(plan["total_count"])
                pending = [
                    (part, path) for part, path in zip(all_parts, internal_paths)
                    if not self.speech._valid_cached_clip(path)
                ]
                completed = int(plan["cached_count"])
                try:
                    batch_size = 3 if str(plan["voice"]).startswith("local-") else 8
                    for offset in range(0, len(pending), batch_size):
                        if self.bulk_download_cancel.is_set():
                            break
                        batch = pending[offset:offset + batch_size]
                        self.speech.prepare_quality_clips(
                            [part for part, _path in batch],
                            int(plan["rate"]), str(plan["voice"]),
                        )
                        completed += sum(
                            1 for _part, path in batch if self.speech._valid_cached_clip(path)
                        )
                        self.root.after(
                            0, self._bulk_download_progress,
                            completed, work_total, all_paths,
                        )
                    export_folder_value = self._bulk_export_folder(pdf_for_pack)
                    export_manifest = (
                        self._load_bulk_export_manifest(export_folder_value)
                        if export_folder_value is not None else {"entries": {}}
                    )
                    export_entries = export_manifest.setdefault("entries", {})
                    if not isinstance(export_entries, dict):
                        export_entries = {}
                        export_manifest["entries"] = export_entries
                    for item in export_items:
                        if self.bulk_download_cancel.is_set():
                            break
                        if bool(item.get("valid")):
                            continue
                        target = item.get("path")
                        if not isinstance(target, Path):
                            continue
                        self.speech.prepare_export_clip(
                            str(item.get("text", "")), int(plan["rate"]),
                            str(plan["voice"]), target, force=True,
                        )
                        if self.speech._valid_cached_clip(target):
                            completed += 1
                            export_entries[str(item.get("index", ""))] = {
                                "file": target.name,
                                "signature": str(item.get("signature", "")),
                                "page": str(item.get("page", "")),
                                "problem_word": str(item.get("problem_word", "")),
                                "voice": str(plan["voice"]),
                                "rate": int(plan["rate"]),
                            }
                            if export_folder_value is not None:
                                self._save_bulk_export_manifest(
                                    export_folder_value, export_manifest, pdf_for_pack,
                                )
                        self.root.after(
                            0, self._bulk_download_progress,
                            completed, work_total, all_paths,
                        )
                    existing_parts = [
                        part for part, path in zip(all_parts, internal_paths)
                        if self.speech._valid_cached_clip(path)
                    ]
                    if pdf_for_pack is not None:
                        self.speech.pin_report_clips(
                            pdf_for_pack, existing_parts, int(plan["rate"]), str(plan["voice"]),
                        )
                    cancelled = self.bulk_download_cancel.is_set()
                    self.root.after(
                        0, self._bulk_download_finished,
                        completed, work_total, all_paths, cancelled, "",
                    )
                except Exception as exc:
                    self.root.after(
                        0, self._bulk_download_finished,
                        completed, work_total, all_paths, False, str(exc),
                    )

            self.bulk_download_thread = threading.Thread(
                target=worker, name="duk-bulk-speech", daemon=True,
            )
            self.bulk_download_thread.start()

        start_button.configure(command=start_download)
        cancel_button.configure(command=cancel_download)
        close_button.configure(command=close_dialog)
        page_picker.bind("<<ComboboxSelected>>", calculate_estimate)
        voice_picker.bind("<<ComboboxSelected>>", calculate_estimate)
        dialog.protocol("WM_DELETE_WINDOW", close_dialog)
        calculate_estimate()

        if bool(self.bulk_download_state.get("active")):
            start_button.configure(state="disabled")
            cancel_button.configure(state="normal")
            page_picker.configure(state="disabled")
            voice_picker.configure(state="disabled")
            completed = int(self.bulk_download_state.get("completed", 0) or 0)
            total = max(1, int(self.bulk_download_state.get("total", 1) or 1))
            progress_var.set(completed / total * 100)
            progress_text.set(f"ההורדה ממשיכה — {completed} מתוך {total}")

    def _bulk_download_progress(self, completed: int, total: int, paths: list[Path]) -> None:
        self.bulk_download_state["completed"] = completed
        self.bulk_download_state["total"] = total
        percentage = completed / max(1, total) * 100
        actual_bytes = 0
        for path in paths:
            try:
                if path.is_file():
                    actual_bytes += path.stat().st_size
            except OSError:
                pass
        message = (
            f"מוריד הקראות: {completed} מתוך {total}  ·  "
            f"נשמרו {self._format_storage_size(actual_bytes)}"
        )
        self.status.set(message)
        self.progress_value.set(percentage)
        ui = self.bulk_download_state.get("ui")
        if isinstance(ui, dict):
            try:
                ui["progress"].set(percentage)
                ui["progress_text"].set(message)
            except tk.TclError:
                pass

    def _bulk_download_finished(
        self, completed: int, total: int, paths: list[Path], cancelled: bool, error: str,
    ) -> None:
        self.bulk_download_state.update(active=False, completed=completed, total=total, error=error)
        actual_bytes = 0
        for path in paths:
            try:
                if path.is_file():
                    actual_bytes += path.stat().st_size
            except OSError:
                pass
        if error:
            message = f"הורדת ההקראות נעצרה: {error}"
        elif cancelled:
            message = (
                f"ההורדה בוטלה — {completed} מתוך {total} קטעים נשמרו "
                f"({self._format_storage_size(actual_bytes)})"
            )
        else:
            export_folder = self._bulk_export_folder(
                self.bulk_download_state.get("pdf_path")
                if isinstance(self.bulk_download_state.get("pdf_path"), Path) else None
            )
            message = (
                f"כל ההקראות מוכנות — {completed} קטעים, "
                f"{self._format_storage_size(actual_bytes)} נשמרו במחשב"
                + (f" · תיקייה: {export_folder}" if export_folder is not None else "")
            )
            self.progress_value.set(100)
            if self.bulk_download_state.get("voice") == RECORDED_AVRI_VOICE:
                library_pdf = self.bulk_download_state.get("pdf_path")
                library_rows = self.bulk_download_state.get("rows_snapshot")
                if isinstance(library_pdf, Path) and isinstance(library_rows, list):
                    self._start_private_avri_library_preparation(
                        library_pdf,
                        [row for row in library_rows if isinstance(row, ReportRow)],
                        force=True,
                    )
        self.status.set(message)
        ui = self.bulk_download_state.get("ui")
        if isinstance(ui, dict):
            try:
                ui["progress"].set(completed / max(1, total) * 100)
                ui["progress_text"].set(message)
                ui["cancel_button"].configure(state="disabled")
                ui["start_button"].configure(state="normal")
                ui["page_picker"].configure(state="readonly")
                ui["voice_picker"].configure(state="readonly")
                recalculate = ui.get("calculate")
                original_pdf = self.bulk_download_state.get("pdf_path")
                if callable(recalculate) and original_pdf == self.pdf_path:
                    recalculate()
            except tk.TclError:
                pass

    def start_reading(self) -> None:
        if not self.rows:
            messagebox.showinfo(APP_NAME, "תחילה יש לפתוח דוח PDF ולהמתין לסיום הזיהוי.")
            return
        if self.current_index < 0:
            self.select_index(0)
        self._begin_reading_stats(reset=True)
        self.speak_current(include_header=True, repeat=False)

    def next_row(self) -> str:
        if not self.rows:
            return "break"
        if self.current_index < len(self.rows) - 1:
            self.select_index(self.current_index + 1)
            self.speak_current(include_header=self.is_group_start(self.current_index), repeat=False)
        else:
            display_summary, spoken_summary = self._finish_reading_stats()
            self.status.set(display_summary)
            self.current_banner.set(display_summary)
            self._set_remaining_banner(0, 0, 0)
            self.speech.speak(
                [spoken_summary], int(round(self.speed.get())), self.selected_voice(),
            )
        return "break"

    def previous_row(self) -> str:
        if not self.rows:
            return "break"
        if self.current_index > 0:
            self.select_index(self.current_index - 1)
            self.speak_current(include_header=self.is_group_start(self.current_index), repeat=False)
        return "break"

    def repeat_row(self) -> str:
        if self.rows and self.current_index >= 0:
            self.speak_current(include_header=False, repeat=True)
        return "break"

    def is_group_start(self, index: int) -> bool:
        if index <= 0:
            return True
        current = self.rows[index]
        previous = self.rows[index - 1]
        return (current.page, current.start) != (previous.page, previous.start)

    def is_page_end(self, index: int) -> bool:
        if not (0 <= index < len(self.rows)):
            return False
        if index >= len(self.rows) - 1:
            return True
        current = self.rows[index]
        following = self.rows[index + 1]
        current_page = current.page.strip()
        following_page = following.page.strip()
        if current_page or following_page:
            return current_page != following_page
        return current.source_pdf_page != following.source_pdf_page

    def build_speech_parts(self, row: ReportRow, include_header: bool, repeat: bool) -> list[str]:
        source_start = row.start
        source_first_word = row.first_word
        source_problem_word = row.problem_word
        if row.report_kind.startswith("eyetech"):
            source_start = restore_eyetech_sacred_names(source_start)
            source_first_word = restore_eyetech_sacred_names(source_first_word)
            source_problem_word = restore_eyetech_sacred_names(source_problem_word)
        vocalized_start = vocalize_report_text(
            row.page, row.line, source_start, whole_page=True,
        )
        vocalized_first_word = vocalize_report_text(
            row.page, row.line, source_first_word, line_start=True,
        )
        vocalized_problem_word = vocalize_report_text(
            row.page, row.line, source_problem_word,
        )
        if include_header:
            first_part = f"{row.page}, {vocalized_start}. שורה {row.line}, {vocalized_first_word}"
        else:
            first_part = f"{row.line}, {vocalized_first_word}"
        parts = [first_part]
        spoken_issue = (
            row.problem_type
            if row.report_kind.startswith("eyetech")
            else row.description
        )
        if row.problem_word and row.problem_word != row.first_word:
            second_part = vocalized_problem_word
            if not repeat and spoken_issue:
                second_part += f", {spoken_issue}"
            parts.append(second_part)
        elif not repeat and spoken_issue:
            parts[0] += f", {spoken_issue}"
        normalizer = (
            normalize_eyetech_divine_names_for_speech
            if row.report_kind.startswith("eyetech")
            else normalize_divine_names_for_speech
        )
        return [normalizer(part) for part in parts]

    @staticmethod
    def _spoken_number(value: str) -> str:
        stripped = str(value).strip()
        if re.fullmatch(r"\d+", stripped):
            return str(int(stripped or "0"))
        return stripped

    def recorded_avri_row_data(self, row: ReportRow) -> dict[str, str]:
        source_start = row.start
        source_first_word = row.first_word
        source_problem_word = row.problem_word
        if row.report_kind.startswith("eyetech"):
            source_start = restore_eyetech_sacred_names(source_start)
            source_first_word = restore_eyetech_sacred_names(source_first_word)
            source_problem_word = restore_eyetech_sacred_names(source_problem_word)
        normalizer = (
            normalize_eyetech_divine_names_for_speech
            if row.report_kind.startswith("eyetech")
            else normalize_divine_names_for_speech
        )
        return {
            "page": self._spoken_number(row.page),
            "line": self._spoken_number(row.line),
            "start": normalizer(vocalize_report_text(
                row.page, row.line, source_start, whole_page=True,
            )),
            "first_word": normalizer(vocalize_report_text(
                row.page, row.line, source_first_word, line_start=True,
            )),
            "problem_word": normalizer(vocalize_report_text(
                row.page, row.line, source_problem_word,
            )),
            "issue": normalizer(
                row.problem_type if row.report_kind.startswith("eyetech") else row.description
            ),
        }

    def build_recorded_avri_parts(
        self, row: ReportRow, include_header: bool, repeat: bool,
    ) -> list[str]:
        """Build small reusable clips for the private offline Avri library."""
        data = self.recorded_avri_row_data(row)
        parts: list[str] = []
        if include_header:
            parts.extend(part for part in (
                data["page"], data["start"], "שורה", data["line"], data["first_word"],
            ) if part)
        else:
            parts.extend(part for part in (data["line"], data["first_word"]) if part)
        if row.problem_word and row.problem_word != row.first_word:
            parts.extend((RECORDED_AVRI_GAP_MARKER, data["problem_word"]))
            if not repeat and data["issue"]:
                parts.append(data["issue"])
        elif not repeat and data["issue"]:
            parts.append(data["issue"])
        return parts

    def build_row_speech_parts(
        self, index: int, include_header: bool, repeat: bool, voice: str | None = None,
    ) -> list[str]:
        if voice == RECORDED_AVRI_VOICE:
            parts = self.build_recorded_avri_parts(self.rows[index], include_header, repeat)
        else:
            parts = self.build_speech_parts(self.rows[index], include_header, repeat)
        if not repeat and self.is_page_end(index):
            parts.append("סוף")
        return parts

    def selected_voice(self) -> str:
        return self._voice_id_for_choice(self.voice_choice.get())

    def _reset_reading_stats(self) -> None:
        self.reading_started_monotonic = None
        self.reading_visited_indices = set()
        self.reading_summary = None
        self.reading_pdf_path = ""
        self._update_result_price_summary()

    def _begin_reading_stats(self, reset: bool = False) -> None:
        pdf_path = str(self.pdf_path.resolve()) if self.pdf_path else ""
        if (
            reset
            or self.reading_started_monotonic is None
            or self.reading_pdf_path != pdf_path
        ):
            self.reading_started_monotonic = time.monotonic()
            self.reading_visited_indices = set()
            self.reading_summary = None
            self.reading_pdf_path = pdf_path

    @staticmethod
    def _duration_for_speech(total_seconds: float) -> str:
        seconds = max(0, int(round(total_seconds)))
        if seconds < 1:
            return "פחות משנייה"
        hours, remainder = divmod(seconds, 3600)
        minutes, seconds = divmod(remainder, 60)
        parts: list[str] = []
        if hours:
            parts.append("שעה אחת" if hours == 1 else f"{hours} שעות")
        if minutes:
            parts.append("דקה אחת" if minutes == 1 else f"{minutes} דקות")
        if seconds:
            parts.append("שנייה אחת" if seconds == 1 else f"{seconds} שניות")
        return " ו ".join(parts)

    def _finish_reading_stats(self) -> tuple[str, str]:
        if self.reading_summary is None:
            self._begin_reading_stats()
            if not self.reading_visited_indices and 0 <= self.current_index < len(self.rows):
                self.reading_visited_indices.add(self.current_index)
            elapsed = max(0.0, time.monotonic() - (self.reading_started_monotonic or time.monotonic()))
            page_keys: set[str] = set()
            for index in self.reading_visited_indices:
                if not (0 <= index < len(self.rows)):
                    continue
                row = self.rows[index]
                page_key = row.page.strip()
                if not page_key and row.source_pdf_page > 0:
                    page_key = f"pdf:{row.source_pdf_page}"
                if page_key:
                    page_keys.add(page_key)
            line_count = max(1, len(self.reading_visited_indices))
            page_count = max(1, len(page_keys))
            self.reading_summary = {
                "elapsed": elapsed,
                "average_page": elapsed / page_count,
                "average_line": elapsed / line_count,
                "pages": page_count,
                "lines": line_count,
            }

        summary = self.reading_summary
        elapsed = float(summary["elapsed"])
        average_page = float(summary["average_page"])
        average_line = float(summary["average_line"])
        display = (
            f"סיום הדוח  |  זמן כולל {self._format_duration(elapsed)}  |  "
            f"ממוצע לעמוד {self._format_duration(average_page)}  |  "
            f"ממוצע לשורה {self._format_duration(average_line)}"
        )
        spoken = (
            f"סיום דוח. זמן כולל, {self._duration_for_speech(elapsed)}. "
            f"ממוצע לעמוד, {self._duration_for_speech(average_page)}. "
            f"ממוצע לשורה, {self._duration_for_speech(average_line)}."
        )
        return display, spoken

    def speak_current(self, include_header: bool, repeat: bool) -> None:
        if not repeat:
            self._begin_reading_stats()
            self.reading_visited_indices.add(self.current_index)
            self.reading_summary = None
            self._update_result_price_summary()
        rate = int(round(self.speed.get()))
        voice = self.selected_voice()
        saved_recording = self._saved_export_for_row(
            self.current_index, include_header, repeat, voice, rate,
        )
        if saved_recording is not None:
            self.status.set(
                f"מקריא מהתיקייה המקומית — {saved_recording.name}"
            )
            self.speech.speak_export(saved_recording)
            return
        parts = self.build_row_speech_parts(
            self.current_index, include_header, repeat, voice=voice,
        )
        self.status.set(f"מכין הקראה איכותית {self.current_index + 1} מתוך {len(self.rows)}")
        self.speech.speak(parts, rate, voice, self.speech_gap_seconds())
        next_index = self.current_index + 1
        if next_index < len(self.rows):
            self._prefetch_rows(next_index, count=2)
        else:
            self.speech.prefetch(["סיום דוח"], rate, voice)

    def _prefetch_rows(self, start_index: int, count: int = 2) -> None:
        rate = int(round(self.speed.get()))
        voice = self.selected_voice()
        requests: list[tuple[list[str], int, str]] = []
        for index in range(start_index, min(start_index + count, len(self.rows))):
            parts = self.build_row_speech_parts(
                index, include_header=self.is_group_start(index), repeat=False, voice=voice,
            )
            requests.append((parts, rate, voice))
        self.speech.prefetch_many(requests)

    def _customer_auth_heartbeat(self) -> None:
        self.auth_heartbeat_job = None
        if not CUSTOMER_EDITION or self.auth_heartbeat_running:
            return
        token = str(self.customer_auth.get("token", ""))
        if not token:
            self._customer_access_revoked("נדרשת כניסה מחדש.")
            return
        self.auth_heartbeat_running = True

        def worker() -> None:
            try:
                status, payload = api_json_request(AUTH_STATUS_URL, {}, token=token, timeout=20)
                if status == 200 and payload.get("ok"):
                    self.root.after(0, self._customer_auth_verified, payload)
                elif status in {401, 403}:
                    self.root.after(
                        0, self._customer_access_revoked,
                        str(payload.get("error", "הגישה לתוכנה נותקה.")),
                    )
                else:
                    self.root.after(0, self._customer_auth_retry)
            except Exception:
                self.root.after(0, self._customer_auth_retry)

        threading.Thread(target=worker, name="duk-auth-heartbeat", daemon=True).start()

    def _customer_auth_verified(self, payload: dict) -> None:
        self.auth_heartbeat_running = False
        self.customer_auth["last_verified"] = int(time.time())
        user = payload.get("user")
        if isinstance(user, dict):
            self.customer_auth["user"] = user
        try:
            save_customer_auth(self.customer_auth)
        except OSError:
            pass
        self.auth_heartbeat_job = self.root.after(60_000, self._customer_auth_heartbeat)

    def _customer_auth_retry(self) -> None:
        self.auth_heartbeat_running = False
        self.auth_heartbeat_job = self.root.after(60_000, self._customer_auth_heartbeat)

    def _customer_access_revoked(self, reason: str) -> None:
        self.auth_heartbeat_running = False
        clear_customer_auth()
        messagebox.showerror("הגישה נותקה", reason + "\n\nהתוכנה תחזור למסך הכניסה.")
        restart = [sys.executable] if getattr(sys, "frozen", False) else [sys.executable, sys.argv[0]]
        self.close()
        try:
            subprocess.Popen(restart, close_fds=True)
        except OSError:
            pass

    def check_for_updates(self, silent: bool = False) -> None:
        if GIGAPDF_OCR_EDITION:
            self.update_status_text.set("גרסת ניסוי מקומית · ללא עדכונים")
            if not silent:
                messagebox.showinfo(
                    APP_NAME,
                    "זוהי גרסת ניסוי חד־פעמית. היא אינה מחוברת לעדכונים האוטומטיים.",
                )
            return
        if self.update_in_progress:
            return
        self.update_retry_job = None
        self.update_in_progress = True
        self.update_status_text.set("בודק עדכון...")
        manifest_url = (
            CUSTOMER_UPDATE_MANIFEST_URL if CUSTOMER_EDITION else PRIVATE_UPDATE_MANIFEST_URL
        )
        user_agent = (
            f"DukReportReaderClients/{APP_VERSION}"
            if CUSTOMER_EDITION else f"DukReportReaderPrivate/{APP_VERSION}"
        )

        def worker() -> None:
            last_error: Exception | None = None
            truststore.inject_into_ssl()
            for attempt in range(1, 6):
                try:
                    request = urllib.request.Request(
                        manifest_url,
                        headers={
                            "Accept": "application/json",
                            "User-Agent": user_agent,
                            "X-Duk-Update-Format": "installer-v1",
                        },
                    )
                    with urllib.request.urlopen(request, timeout=25) as response:
                        payload = json.loads(response.read(256 * 1024).decode("utf-8"))
                    if not isinstance(payload, dict):
                        raise ValueError("השרת החזיר תשובה לא תקינה")
                    self.root.after(0, self._handle_update_manifest, payload, silent)
                    return
                except Exception as error:
                    last_error = error
                    if attempt < 5:
                        self.root.after(
                            0, self.update_status_text.set,
                            f"החיבור נותק · ניסיון נוסף {attempt + 1}/5...",
                        )
                        time.sleep(min(8, attempt * 2))
            self.root.after(
                0, self._update_check_failed,
                str(last_error or "לא ניתן להתחבר לשרת"), silent,
            )

        threading.Thread(target=worker, name="duk-update-check", daemon=True).start()

    def _handle_update_manifest(self, payload: dict, silent: bool) -> None:
        self.update_in_progress = False
        latest = str(payload.get("version", "")).strip()
        download_url = str(payload.get("url", "")).strip()
        digest = str(payload.get("sha256", "")).strip().lower()
        package_format = str(payload.get("format", "zip")).strip().lower()
        try:
            size = int(payload.get("size", 0))
        except (TypeError, ValueError):
            size = 0
        if (
            not latest or not download_url.startswith("https://yaakovserver.com/")
            or not re.fullmatch(r"[0-9a-f]{64}", digest) or size <= 0
            or package_format not in {"zip", "installer"}
        ):
            self._update_check_failed("פרטי העדכון בשרת אינם תקינים", silent)
            return
        if version_key(latest) <= version_key(APP_VERSION):
            self.update_status_text.set(f"גרסה {APP_VERSION} · מעודכנת")
            self._schedule_update_check(6 * 60 * 60 * 1000)
            if not silent:
                messagebox.showinfo("עדכוני תוכנה", f"מותקנת הגרסה העדכנית: {APP_VERSION}")
            return
        notes = str(payload.get("notes", "")).strip()
        message = (
            f"גרסה חדשה {latest} מוכנה להתקנה.\n\n"
            f"{notes + chr(10) + chr(10) if notes else ''}"
            "התוכנה תשמור את הדוח והמיקום הנוכחי, תיסגר ותיפתח שוב באותו מקום.\n"
            "להוריד ולהתקין עכשיו?"
        )
        self.update_status_text.set(f"עדכון {latest} זמין")
        if not CUSTOMER_EDITION and silent:
            self.update_status_text.set(f"מוריד אוטומטית עדכון {latest}...")
            self._download_update(payload)
            return
        if messagebox.askyesno("עדכון קורא דוחות", message, icon="info"):
            self._download_update(payload)

    def _update_check_failed(self, detail: str, silent: bool) -> None:
        self.update_in_progress = False
        self.update_status_text.set(f"גרסה {APP_VERSION}")
        self._schedule_update_check(2 * 60 * 1000)
        if not silent:
            messagebox.showerror("עדכוני תוכנה", f"לא ניתן לבדוק עדכונים כרגע.\n\n{detail}")

    def _schedule_update_check(self, delay_ms: int) -> None:
        if self.update_retry_job:
            try:
                self.root.after_cancel(self.update_retry_job)
            except tk.TclError:
                pass
        self.update_retry_job = self.root.after(
            max(1000, int(delay_ms)), lambda: self.check_for_updates(silent=True),
        )

    def _download_update(self, payload: dict) -> None:
        if self.update_in_progress:
            return
        self.update_in_progress = True
        latest = str(payload["version"])
        package_format = str(payload.get("format", "zip")).strip().lower()
        package_suffix = ".exe" if package_format == "installer" else ".zip"
        archive = app_data_dir() / f"update-{latest}{package_suffix}"
        self.update_status_text.set(f"מוריד עדכון {latest}...")
        user_agent = (
            f"DukReportReaderClients/{APP_VERSION}"
            if CUSTOMER_EDITION else f"DukReportReaderPrivate/{APP_VERSION}"
        )
        expected_executable = (
            "dukreportreaderclients.exe" if CUSTOMER_EDITION else "dukreportreader.exe"
        )

        def worker() -> None:
            temporary = archive.with_suffix(archive.suffix + ".part")
            try:
                expected_size = int(payload["size"])
                truststore.inject_into_ssl()
                last_error: Exception | None = None
                for attempt in range(1, 13):
                    received = temporary.stat().st_size if temporary.is_file() else 0
                    if received < 0 or received > expected_size:
                        temporary.unlink(missing_ok=True)
                        received = 0
                    digest = hashlib.sha256()
                    if received:
                        with temporary.open("rb") as existing:
                            while chunk := existing.read(1024 * 1024):
                                digest.update(chunk)
                    headers = {
                        "Accept": (
                            "application/vnd.microsoft.portable-executable"
                            if package_format == "installer" else "application/zip"
                        ),
                        "User-Agent": user_agent,
                        "X-Duk-Update-Format": "installer-v1",
                    }
                    if received:
                        headers["Range"] = f"bytes={received}-"
                    try:
                        request = urllib.request.Request(str(payload["url"]), headers=headers)
                        with urllib.request.urlopen(request, timeout=90) as response:
                            response_status = int(getattr(response, "status", response.getcode()))
                            if received and response_status != 206:
                                received = 0
                                digest = hashlib.sha256()
                                mode = "wb"
                            else:
                                mode = "ab" if received else "wb"
                            with temporary.open(mode) as output:
                                while True:
                                    chunk = response.read(1024 * 1024)
                                    if not chunk:
                                        break
                                    output.write(chunk)
                                    digest.update(chunk)
                                    received += len(chunk)
                                    percent = min(100, int(received * 100 / max(1, expected_size)))
                                    self.root.after(
                                        0, self.update_status_text.set,
                                        f"מוריד עדכון {latest}... {percent}%",
                                    )
                        if received == expected_size:
                            break
                        raise ValueError(
                            f"גודל ההורדה שונה מהצפוי ({received} במקום {expected_size})"
                        )
                    except Exception as error:
                        last_error = error
                        if attempt == 12:
                            raise
                        self.root.after(
                            0, self.update_status_text.set,
                            f"ההורדה נותקה · מתחבר וממשיך ({attempt + 1}/12)...",
                        )
                        time.sleep(min(15, attempt * 2))
                if received != expected_size:
                    raise ValueError(
                        f"גודל ההורדה שונה מהצפוי ({received} במקום {expected_size}): {last_error}"
                    )
                if digest.hexdigest().lower() != str(payload["sha256"]).lower():
                    temporary.unlink(missing_ok=True)
                    raise ValueError("חתימת קובץ העדכון אינה תואמת")
                temporary.replace(archive)
                if package_format == "installer":
                    with archive.open("rb") as executable:
                        if executable.read(2) != b"MZ":
                            archive.unlink(missing_ok=True)
                            raise ValueError("קובץ המתקין שהתקבל אינו תקין")
                    self.root.after(0, self._install_downloaded_installer, archive, latest)
                    return
                with zipfile.ZipFile(archive, "r") as package:
                    bad_member = package.testzip()
                    if bad_member:
                        raise ValueError(f"קובץ פגום בתוך העדכון: {bad_member}")
                    members = [
                        item.filename for item in package.infolist()
                        if not item.is_dir()
                        and Path(item.filename).name.casefold() == expected_executable
                    ]
                    if len(members) != 1:
                        raise ValueError("חבילת העדכון אינה מכילה קובץ תוכנה יחיד")
                self.root.after(0, self._install_downloaded_update, archive, members[0], latest)
            except Exception as error:
                self.root.after(0, self._update_download_failed, str(error))

        threading.Thread(target=worker, name="duk-update-download", daemon=True).start()

    def _update_download_failed(self, detail: str) -> None:
        self.update_in_progress = False
        self.update_status_text.set("העדכון נכשל")
        self._schedule_update_check(2 * 60 * 1000)
        messagebox.showerror("עדכון קורא דוחות", f"הורדת העדכון נכשלה.\n\n{detail}")

    def _install_downloaded_installer(self, installer: Path, latest: str) -> None:
        if not getattr(sys, "frozen", False):
            self.update_in_progress = False
            self.update_status_text.set(f"מתקין {latest} הורד")
            messagebox.showinfo(
                "עדכון קורא דוחות",
                f"המתקין הורד אל:\n{installer}\n\nבהרצת פיתוח לא מפעילים את המתקין.",
            )
            return
        installed_target = Path(os.environ.get("LOCALAPPDATA", tempfile.gettempdir())) / "Programs"
        installed_target /= "DukReportReaderClients" if CUSTOMER_EDITION else "DukReportReader"
        installed_target /= "DukReportReaderClients.exe" if CUSTOMER_EDITION else "DukReportReader.exe"
        updater_script = app_data_dir() / f"install-setup-update-{latest}.ps1"
        updater_script.write_text(
            r'''param(
    [int]$ProcessToWait,
    [string]$Installer,
    [string]$InstalledTarget
)
$ErrorActionPreference = "Stop"
try {
    Wait-Process -Id $ProcessToWait -Timeout 180 -ErrorAction SilentlyContinue
    $arguments = @(
        "/VERYSILENT", "/SUPPRESSMSGBOXES", "/NORESTART",
        "/CLOSEAPPLICATIONS", "/RESTARTAPPLICATIONS=0"
    )
    $setup = Start-Process -FilePath $Installer -ArgumentList $arguments -Wait -PassThru
    if ($setup.ExitCode -ne 0) { throw "Installer exit code: $($setup.ExitCode)" }
    if (-not (Test-Path -LiteralPath $InstalledTarget -PathType Leaf)) {
        throw "Installed application was not found"
    }
    Start-Process -FilePath $InstalledTarget
} catch {
    try {
        $log = Join-Path ([IO.Path]::GetDirectoryName($Installer)) "update-error.txt"
        $_ | Out-String | Set-Content -LiteralPath $log -Encoding UTF8
    } catch {}
    if (Test-Path -LiteralPath $InstalledTarget -PathType Leaf) {
        Start-Process -FilePath $InstalledTarget
    }
} finally {
    Remove-Item -LiteralPath $Installer -Force -ErrorAction SilentlyContinue
}
''',
            encoding="utf-8-sig",
        )
        self.update_status_text.set("סוגר, מתקין ופותח מחדש...")
        self._save_settings()
        flags = (
            getattr(subprocess, "CREATE_NO_WINDOW", 0)
            | getattr(subprocess, "DETACHED_PROCESS", 0)
            | getattr(subprocess, "CREATE_NEW_PROCESS_GROUP", 0)
        )
        try:
            subprocess.Popen(
                [
                    "powershell.exe", "-NoProfile", "-ExecutionPolicy", "Bypass",
                    "-File", str(updater_script),
                    "-ProcessToWait", str(os.getpid()),
                    "-Installer", str(installer),
                    "-InstalledTarget", str(installed_target),
                ],
                close_fds=True,
                creationflags=flags,
            )
        except OSError as error:
            self.update_in_progress = False
            self.update_status_text.set("הפעלת המתקין נכשלה")
            messagebox.showerror("עדכון קורא דוחות", str(error))
            return
        self.close()

    def _install_downloaded_update(self, archive: Path, member: str, latest: str) -> None:
        if not getattr(sys, "frozen", False):
            self.update_in_progress = False
            self.update_status_text.set(f"עדכון {latest} הורד")
            messagebox.showinfo(
                "עדכון קורא דוחות",
                f"העדכון הורד אל:\n{archive}\n\nבהרצת פיתוח לא מחליפים את קובץ התוכנה.",
            )
            return
        target = Path(sys.executable).resolve()
        permission_probe = target.parent / f".duk-update-test-{uuid.uuid4().hex}"
        try:
            permission_probe.write_bytes(b"ok")
            permission_probe.unlink()
        except OSError as error:
            self.update_in_progress = False
            self.update_status_text.set("נדרשת הרשאת כתיבה")
            messagebox.showerror(
                "עדכון קורא דוחות",
                "לא ניתן לעדכן מתוך התיקייה הנוכחית. העבירו את התוכנה לתיקייה רגילה של המשתמש ונסו שוב.\n\n"
                + str(error),
            )
            return
        updater_script = app_data_dir() / f"install-update-{latest}.ps1"
        updater_script.write_text(
            r'''param(
    [int]$ProcessToWait,
    [string]$Archive,
    [string]$Target,
    [string]$Entry
)
$ErrorActionPreference = "Stop"
$stage = Join-Path ([IO.Path]::GetTempPath()) ("duk-report-reader-update-" + [guid]::NewGuid().ToString("N"))
$pending = "$Target.new"
$backup = "$Target.previous"
try {
    Wait-Process -Id $ProcessToWait -Timeout 180 -ErrorAction SilentlyContinue
    $resolvedTarget = [IO.Path]::GetFullPath($Target)
    for ($attempt = 0; $attempt -lt 180; $attempt++) {
        $stillRunning = Get-CimInstance Win32_Process -ErrorAction SilentlyContinue | Where-Object {
            $_.ExecutablePath -and [IO.Path]::GetFullPath($_.ExecutablePath) -eq $resolvedTarget
        }
        if (-not $stillRunning) { break }
        Start-Sleep -Seconds 1
    }
    Add-Type -AssemblyName System.IO.Compression.FileSystem
    [IO.Directory]::CreateDirectory($stage) | Out-Null
    [IO.Compression.ZipFile]::ExtractToDirectory($Archive, $stage)
    $source = Join-Path $stage ($Entry.Replace('/', [IO.Path]::DirectorySeparatorChar))
    if (-not (Test-Path -LiteralPath $source -PathType Leaf)) { throw "Missing executable in update package" }
    Copy-Item -LiteralPath $source -Destination $pending -Force
    if (Test-Path -LiteralPath $backup) { Remove-Item -LiteralPath $backup -Force }
    $movedOld = $false
    for ($attempt = 0; $attempt -lt 60 -and -not $movedOld; $attempt++) {
        try {
            if (Test-Path -LiteralPath $Target) {
                Move-Item -LiteralPath $Target -Destination $backup -Force
            }
            $movedOld = $true
        } catch {
            Start-Sleep -Seconds 1
        }
    }
    if (-not $movedOld) { throw "The installed application is still in use" }
    try {
        Move-Item -LiteralPath $pending -Destination $Target -Force
    } catch {
        if (Test-Path -LiteralPath $backup) { Move-Item -LiteralPath $backup -Destination $Target -Force }
        throw
    }
    Start-Process -FilePath $Target
    Start-Sleep -Milliseconds 800
    if (Test-Path -LiteralPath $backup) { Remove-Item -LiteralPath $backup -Force }
} catch {
    try {
        $log = Join-Path ([IO.Path]::GetDirectoryName($Archive)) "update-error.txt"
        $_ | Out-String | Set-Content -LiteralPath $log -Encoding UTF8
    } catch {}
    if (-not (Test-Path -LiteralPath $Target) -and (Test-Path -LiteralPath $backup)) {
        Move-Item -LiteralPath $backup -Destination $Target -Force
    }
    if (Test-Path -LiteralPath $Target) { Start-Process -FilePath $Target }
} finally {
    Remove-Item -LiteralPath $pending -Force -ErrorAction SilentlyContinue
    Remove-Item -LiteralPath $stage -Recurse -Force -ErrorAction SilentlyContinue
    Remove-Item -LiteralPath $Archive -Force -ErrorAction SilentlyContinue
}
''',
            encoding="utf-8-sig",
        )
        self.update_status_text.set("מתקין עדכון ופותח מחדש...")
        self._save_settings()
        flags = (
            getattr(subprocess, "CREATE_NO_WINDOW", 0)
            | getattr(subprocess, "DETACHED_PROCESS", 0)
            | getattr(subprocess, "CREATE_NEW_PROCESS_GROUP", 0)
        )
        try:
            subprocess.Popen(
                [
                    "powershell.exe", "-NoProfile", "-ExecutionPolicy", "Bypass",
                    "-File", str(updater_script),
                    "-ProcessToWait", str(os.getpid()),
                    "-Archive", str(archive),
                    "-Target", str(target),
                    "-Entry", member,
                ],
                close_fds=True,
                creationflags=flags,
            )
        except OSError as error:
            self.update_in_progress = False
            self.update_status_text.set("הפעלת העדכון נכשלה")
            messagebox.showerror("עדכון קורא דוחות", str(error))
            return
        self.close()

    def close(self) -> None:
        self._save_settings()
        self.bulk_download_cancel.set()
        self.avri_library_cancel.set()
        self.offline_ai_cancel.set()
        self.offline_ai_review_generation += 1
        if self.offline_ai is not None:
            self.offline_ai.stop()
        if self.auth_heartbeat_job:
            try:
                self.root.after_cancel(self.auth_heartbeat_job)
            except tk.TclError:
                pass
            self.auth_heartbeat_job = None
        if self.ocr_rule_sync_job:
            try:
                self.root.after_cancel(self.ocr_rule_sync_job)
            except tk.TclError:
                pass
            self.ocr_rule_sync_job = None
        if self.update_retry_job:
            try:
                self.root.after_cancel(self.update_retry_job)
            except tk.TclError:
                pass
            self.update_retry_job = None
        if self.finance_poll_job:
            try:
                self.root.after_cancel(self.finance_poll_job)
            except tk.TclError:
                pass
            self.finance_poll_job = None
        if self.timer_after_job:
            try:
                self.root.after_cancel(self.timer_after_job)
            except tk.TclError:
                pass
            self.timer_after_job = None
        if self._drop_hwnd and self._drop_old_wndproc:
            try:
                ctypes.windll.shell32.DragAcceptFiles(self._drop_hwnd, False)
                ctypes.windll.user32.SetWindowLongPtrW(
                    self._drop_hwnd, -4, self._drop_old_wndproc,
                )
            except Exception:
                pass
            self._drop_hwnd = 0
            self._drop_old_wndproc = 0
            self._drop_wndproc_callback = None
        self.speech.close()
        self.root.destroy()
class CustomerLoginGate:
    def __init__(self, root: tk.Tk, on_success: Callable[[], None]):
        self.root = root
        self.on_success = on_success
        saved = load_customer_auth()
        self.saved = saved
        self.name = tk.StringVar(value=str(saved.get("name", "")))
        self.phone = tk.StringVar(value=str(saved.get("phone", "")))
        self.status = tk.StringVar(value="בודק הרשאה...")
        self.busy = False
        self.login_button: ttk.Button | None = None
        self.root.title(f"{APP_NAME} {APP_VERSION} · כניסה")
        try:
            self.root.iconbitmap(default=str(resource_path("app.ico")))
        except Exception:
            pass
        fit_window_to_work_area(root, 560, 430, 460, 380)
        self._build()
        if str(saved.get("token", "")):
            self._validate_saved_session()
        else:
            self.status.set("היכנסו עם אותם פרטים שמסרתם באתר ההורדה")

    def _build(self) -> None:
        background = "#FFF8E9"
        navy = "#4A2D17"
        gold = "#D9B75D"
        self.root.configure(bg=background)
        header = tk.Frame(self.root, bg=navy, height=96)
        header.pack(fill="x")
        header.pack_propagate(False)
        tk.Label(
            header, text="קורא דוחות ללקוחות", bg=navy, fg="white",
            font=("Segoe UI", 20, "bold"), anchor="e", padx=28,
        ).pack(fill="both", expand=True)
        card = tk.Frame(self.root, bg="white", padx=38, pady=26, highlightbackground="#E4D3B0", highlightthickness=1)
        card.pack(fill="both", expand=True, padx=42, pady=28)
        tk.Label(
            card, text="כניסה לגרסת הלקוחות", bg="white", fg=navy,
            font=("Segoe UI", 16, "bold"), anchor="e",
        ).pack(fill="x", pady=(0, 14))
        tk.Label(card, text="שם מלא", bg="white", fg="#6E604F", font=("Segoe UI", 9, "bold"), anchor="e").pack(fill="x")
        name_entry = ttk.Entry(card, textvariable=self.name, justify="right", font=("Segoe UI", 12))
        name_entry.pack(fill="x", ipady=6, pady=(4, 10))
        tk.Label(card, text="מספר טלפון", bg="white", fg="#6E604F", font=("Segoe UI", 9, "bold"), anchor="e").pack(fill="x")
        phone_entry = ttk.Entry(card, textvariable=self.phone, justify="right", font=("Segoe UI", 12))
        phone_entry.pack(fill="x", ipady=6, pady=(4, 14))
        self.login_button = ttk.Button(card, text="כניסה לתוכנה", command=self._login)
        self.login_button.pack(fill="x", ipady=6)
        tk.Label(
            card, textvariable=self.status, bg="white", fg="#2D7A4B",
            font=("Segoe UI", 9, "bold"), anchor="e", justify="right", wraplength=430,
        ).pack(fill="x", pady=(12, 0))
        name_entry.focus_set()
        phone_entry.bind("<Return>", lambda _event: self._login())

    def _set_busy(self, value: bool, message: str) -> None:
        self.busy = value
        self.status.set(message)
        if self.login_button is not None:
            self.login_button.configure(state="disabled" if value else "normal")

    def _validate_saved_session(self) -> None:
        self._set_busy(True, "בודק הרשאה מול השרת...")
        token = str(self.saved.get("token", ""))

        def worker() -> None:
            try:
                status, payload = api_json_request(AUTH_STATUS_URL, {}, token=token, timeout=20)
            except Exception:
                last_verified = int(self.saved.get("last_verified", 0) or 0)
                if last_verified >= int(time.time()) - 86400:
                    self.root.after(0, self._complete, self.saved)
                else:
                    self.root.after(0, self._session_failed, "אין חיבור לשרת. נדרש חיבור לאינטרנט לצורך אימות הכניסה.")
                return
            if status == 200 and payload.get("ok"):
                self.saved["last_verified"] = int(time.time())
                if isinstance(payload.get("user"), dict):
                    self.saved["user"] = payload["user"]
                self.root.after(0, self._complete, self.saved)
            else:
                clear_customer_auth()
                self.root.after(0, self._session_failed, str(payload.get("error", "נדרשת כניסה מחדש.")))

        threading.Thread(target=worker, name="duk-login-check", daemon=True).start()

    def _session_failed(self, message: str) -> None:
        self._set_busy(False, message)

    def _login(self) -> None:
        if self.busy:
            return
        name = self.name.get().strip()
        phone = self.phone.get().strip()
        if len(name) < 2 or len(re.sub(r"\D", "", phone)) < 8:
            self.status.set("יש להזין את השם והטלפון כפי שנמסרו באתר")
            return
        device_id = customer_device_id()
        self._set_busy(True, "מתחבר לשרת...")

        def worker() -> None:
            try:
                status, payload = api_json_request(
                    AUTH_LOGIN_URL,
                    {
                        "name": name, "phone": phone, "device_id": device_id,
                        "app_version": APP_VERSION, "platform": "windows",
                    },
                    timeout=25,
                )
            except Exception as error:
                self.root.after(0, self._session_failed, f"לא ניתן להתחבר לשרת: {error}")
                return
            if status != 200 or not payload.get("token"):
                self.root.after(0, self._session_failed, str(payload.get("error", "פרטי הכניסה אינם תואמים.")))
                return
            auth = {
                "token": str(payload["token"]), "name": name, "phone": phone,
                "device_id": device_id, "user": payload.get("user", {}),
                "last_verified": int(time.time()),
            }
            self.root.after(0, self._complete, auth)

        threading.Thread(target=worker, name="duk-login", daemon=True).start()

    def _complete(self, auth: dict) -> None:
        try:
            save_customer_auth(auth)
        except OSError as error:
            self._session_failed(f"לא ניתן לשמור את הכניסה במחשב: {error}")
            return
        for child in self.root.winfo_children():
            child.destroy()
        self.root.resizable(True, True)
        self.on_success()


def run_local_voice_self_test(result_path: Path) -> None:
    """Exercise the bundled private Piper voice before showing the UI."""
    result_path.parent.mkdir(parents=True, exist_ok=True)
    wav_path = result_path.with_suffix(".wav")
    worker = SpeechWorker(lambda _value: None)
    payload: dict[str, object]
    try:
        source = worker._create_local_voice_clips(
            ["זוהי בדיקה של קול פייפר החדש"], 0, "local-saspeech",
        )[0]
        shutil.copy2(source, wav_path)
        with wave.open(str(wav_path), "rb") as wav_file:
            frame_count = wav_file.getnframes()
            sample_rate = wav_file.getframerate()
        payload = {
            "ok": True,
            "wav": str(wav_path),
            "bytes": wav_path.stat().st_size,
            "sample_rate": sample_rate,
            "duration_seconds": frame_count / max(1, sample_rate),
        }
    except Exception as exc:
        payload = {
            "ok": False,
            "error": str(exc),
            "traceback": traceback.format_exc(),
        }
    finally:
        worker.close()
    result_path.write_text(
        json.dumps(payload, ensure_ascii=False, indent=2), encoding="utf-8",
    )


def main() -> None:
    self_test_prefix = "--voice-self-test="
    for argument in sys.argv[1:]:
        if argument.startswith(self_test_prefix):
            run_local_voice_self_test(Path(argument[len(self_test_prefix):]))
            return
    enable_windows_dpi_awareness()
    root = tk.Tk()

    def launch_reader() -> None:
        app = ReportReaderApp(root)
        root._duk_reader_app = app  # type: ignore[attr-defined]
        if len(sys.argv) > 1:
            candidate = Path(sys.argv[1])
            if candidate.exists() and candidate.suffix.lower() == ".pdf":
                root.after(250, app.open_pdf, candidate)
        else:
            root.after(250, app.restore_last_report)

    if CUSTOMER_EDITION:
        CustomerLoginGate(root, launch_reader)
    else:
        launch_reader()
    root.mainloop()


if __name__ == "__main__":
    main()
