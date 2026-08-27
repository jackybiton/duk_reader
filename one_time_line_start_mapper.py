from __future__ import annotations

import csv
import json
import os
import re
import shutil
import sys
import threading
import unicodedata
import uuid
from collections import Counter, defaultdict
from dataclasses import dataclass, field
from datetime import datetime
from pathlib import Path

import tkinter as tk
from tkinter import filedialog, messagebox, ttk

from duk_reader import (
    APP_NAME,
    RECORDED_AVRI_VOICE,
    ReportOcr,
    ReportRow,
    SpeechWorker,
    _load_nikud_corpus,
    _remove_cantillation,
    _speech_word_key,
    _speech_units,
    app_data_dir,
    display_report_text,
    enable_windows_dpi_awareness,
    fit_window_to_work_area,
    normalize_divine_names_for_speech,
    normalize_divine_names_for_display,
    normalize_eyetech_divine_names_for_speech,
    resource_path,
    restore_eyetech_sacred_names,
    vocalize_report_text,
)


TOOL_NAME = "מיפוי חד־פעמי של תחילות שורה"
STATISTICS_FILE = "סטטיסטיקה - תחילות שורה.csv"
PAGE_SUMMARY_FILE = "סיכום לפי עמוד.csv"
MANIFEST_FILE = "מיפוי תחילות שורה.json"
FORCE_CORPUS_PAGES = {78, 242, 243}


def normalized_number(value: object) -> str:
    text = str(value or "").strip()
    if re.fullmatch(r"\d+", text):
        return str(int(text))
    return text


def safe_component(value: object, fallback: str) -> str:
    text = unicodedata.normalize("NFC", str(value or "")).strip()
    text = re.sub(r'[<>:"/\\|?*\x00-\x1f]', " ", text)
    text = re.sub(r"\s+", " ", text).strip(" .")[:90]
    return text or fallback


def spoken_line_start(row: ReportRow) -> str:
    source = row.first_word.strip()
    if row.report_kind.startswith("eyetech"):
        source = restore_eyetech_sacred_names(source)
        normalizer = normalize_eyetech_divine_names_for_speech
    else:
        normalizer = normalize_divine_names_for_speech
    # The report is authoritative. Use the corpus only to add nikud when its
    # consonants are exactly the same; never let fuzzy corpus correction swap
    # the word that was actually recognized in the report.
    corpus_word = ""
    try:
        page = int(normalized_number(row.page))
        line = int(normalized_number(row.line))
        corpus_source = _load_nikud_corpus().get(str(page), {}).get(str(line), "")
        corpus_units = _speech_units(corpus_source)
        corpus_word = _remove_cantillation(corpus_units[0]) if corpus_units else ""
    except (TypeError, ValueError):
        corpus_word = ""
    reading = (
        corpus_word
        if corpus_word and _speech_word_key(corpus_word) == _speech_word_key(source)
        else source
    )
    return normalizer(reading).strip()


def plain_display_word(value: str) -> str:
    letters = "".join(
        character for character in unicodedata.normalize("NFD", str(value or ""))
        if "א" <= character <= "ת"
    )
    return normalize_divine_names_for_display(letters)


def corpus_line_start(page: int, line: int) -> tuple[str, str]:
    source = _load_nikud_corpus().get(str(page), {}).get(str(line), "")
    units = _speech_units(source)
    if not units:
        return "", ""
    vocalized = _remove_cantillation(units[0])
    spoken = normalize_divine_names_for_speech(vocalized).strip()
    return plain_display_word(vocalized), spoken


@dataclass
class Candidate:
    report: str
    page: str
    line: str
    display_text: str
    spoken_text: str
    confidence: float
    source_pdf_page: int


@dataclass
class MappedLine:
    page: str
    line: str
    display_text: str
    spoken_text: str
    reports: list[str]
    target: Path | None
    cache_path: Path | None
    status: str
    variants: list[str] = field(default_factory=list)
    source_count: int = 1
    error: str = ""
    selected: bool = True
    download_allowed: bool = True
    corpus_only: bool = False
    report_spoken_text: str = ""
    report_display_text: str = ""
    corpus_spoken_text: str = ""
    corpus_display_text: str = ""
    decision: str = ""
    force_corpus: bool = False

    @property
    def key(self) -> str:
        return f"{self.page}\u0000{self.line}"


class LineStartMapper:
    def __init__(self, root: tk.Tk):
        self.root = root
        self.root.title(TOOL_NAME)
        self.root.configure(bg="#E7D4AB")
        fit_window_to_work_area(root, 1240, 820, 880, 620)
        try:
            self.root.iconbitmap(default=str(resource_path("app.ico")))
        except Exception:
            pass

        self.pdf_paths: list[Path] = []
        self.mapped: list[MappedLine] = []
        self.output_root = SpeechWorker._recorded_avri_root()
        self.cancel_event = threading.Event()
        self.worker: threading.Thread | None = None
        self.operation_kind = ""
        self.review_dialog: tk.Toplevel | None = None
        self.speech = SpeechWorker(lambda message: self._ui(self.status.set, message))

        self.status = tk.StringVar(value="בחר כמה דוחות PDF ולחץ על מיפוי הדוחות")
        self.summary = tk.StringVar(value="עדיין לא בוצע מיפוי")
        self.output_text = tk.StringVar(value=str(self.output_root))
        self.progress = tk.DoubleVar(value=0)
        self.include_page_numbers = tk.BooleanVar(value=True)
        self.include_line_numbers = tk.BooleanVar(value=True)
        self.include_line_starts = tk.BooleanVar(value=True)
        self.allow_corpus_download = tk.BooleanVar(value=False)
        self.allow_corpus_download_value = False
        self._build_ui()
        self.root.protocol("WM_DELETE_WINDOW", self.close)

    def _build_ui(self) -> None:
        header = tk.Frame(self.root, bg="#5A3518", padx=18, pady=14)
        header.pack(fill="x")
        tk.Label(
            header, text=TOOL_NAME, bg="#5A3518", fg="white",
            font=("Segoe UI", 18, "bold"), anchor="e",
        ).pack(fill="x")
        tk.Label(
            header,
            text="כלי נפרד שאינו משנה את תוכנת קורא הדוחות",
            bg="#5A3518", fg="#F6D878", font=("Segoe UI", 10), anchor="e",
        ).pack(fill="x", pady=(3, 0))

        actions = tk.Frame(self.root, bg="#FFF9EC", padx=14, pady=12)
        actions.pack(fill="x", padx=14, pady=(14, 8))
        self.choose_button = tk.Button(
            actions, text="בחירת דוחות PDF", command=self.choose_reports,
            bg="#A7650B", fg="white", activebackground="#8F5508",
            activeforeground="white", relief="flat", padx=18, pady=9,
            font=("Segoe UI", 10, "bold"),
        )
        self.choose_button.pack(side="right", padx=4)
        self.map_button = tk.Button(
            actions, text="מיפוי הדוחות", command=self.start_mapping,
            bg="#74471F", fg="white", activebackground="#5A3518",
            activeforeground="white", relief="flat", padx=18, pady=9,
            font=("Segoe UI", 10, "bold"),
        )
        self.map_button.pack(side="right", padx=4)
        self.download_button = tk.Button(
            actions, text="הורדת ההקלטות החסרות", command=self.start_download,
            bg="#278552", fg="white", activebackground="#1F6B42",
            activeforeground="white", relief="flat", padx=18, pady=9,
            font=("Segoe UI", 10, "bold"), state="disabled",
        )
        self.download_button.pack(side="right", padx=4)
        self.organize_button = tk.Button(
            actions, text="סידור הקיים בלבד",
            command=lambda: self.start_download(organize_only=True),
            bg="#356B91", fg="white", activebackground="#295572",
            activeforeground="white", relief="flat", padx=14, pady=9,
            font=("Segoe UI", 10, "bold"), state="disabled",
        )
        self.organize_button.pack(side="right", padx=4)
        self.cancel_button = tk.Button(
            actions, text="עצירת ההורדה", command=self.cancel, bg="#C94A3A",
            activebackground="#A93C30", activeforeground="white",
            fg="white", relief="flat", padx=14, pady=9,
            font=("Segoe UI", 10, "bold"), state="disabled",
        )
        self.cancel_button.pack(side="right", padx=4)
        tk.Button(
            actions, text="פתיחת תיקיית היעד", command=self.open_output_folder,
            bg="#F1E2C4", fg="#5A3518", relief="flat", padx=14, pady=9,
            font=("Segoe UI", 10, "bold"),
        ).pack(side="left", padx=4)
        tk.Button(
            actions, text="מזער והמשך ברקע", command=self.continue_in_background,
            bg="#D7C08E", fg="#5A3518", activebackground="#C9AE72",
            relief="flat", padx=13, pady=9, font=("Segoe UI", 9, "bold"),
        ).pack(side="left", padx=4)

        selection = tk.Frame(self.root, bg="#FFF9EC", padx=14, pady=9)
        selection.pack(fill="x", padx=14, pady=(0, 8))
        tk.Label(
            selection, text="מה להוריד:", bg="#FFF9EC", fg="#5A3518",
            font=("Segoe UI", 10, "bold"),
        ).pack(side="right", padx=(8, 2))
        for text, variable in (
            ("מספרי עמודים 1–245", self.include_page_numbers),
            ("מספרי שורות 1–42", self.include_line_numbers),
            ("תחילות שורה", self.include_line_starts),
        ):
            tk.Checkbutton(
                selection, text=text, variable=variable, bg="#FFF9EC",
                activebackground="#FFF9EC", fg="#5A3518",
                selectcolor="#F6D878", font=("Segoe UI", 10),
            ).pack(side="right", padx=8)
        tk.Checkbutton(
            selection, text="לאפשר גם מתיקון קוראים",
            variable=self.allow_corpus_download,
            command=self.apply_corpus_download_choice,
            bg="#FFF9EC", activebackground="#FFF9EC", fg="#A13A2C",
            selectcolor="#F6D878", font=("Segoe UI", 10, "bold"),
        ).pack(side="right", padx=8)
        tk.Button(
            selection, text="סימון כל השורות", command=lambda: self.mark_rows("all"),
            bg="#F1E2C4", fg="#5A3518", relief="flat", padx=10, pady=5,
        ).pack(side="left", padx=3)
        tk.Button(
            selection, text="רק החסרות", command=lambda: self.mark_rows("missing"),
            bg="#F1E2C4", fg="#5A3518", relief="flat", padx=10, pady=5,
        ).pack(side="left", padx=3)
        tk.Button(
            selection, text="ביטול סימון שורות", command=lambda: self.mark_rows("none"),
            bg="#F1E2C4", fg="#5A3518", relief="flat", padx=10, pady=5,
        ).pack(side="left", padx=3)
        self.review_button = tk.Button(
            selection, text="הכרעה בהבדלים", command=self.open_conflict_review,
            bg="#F6D878", fg="#5A3518", relief="flat", padx=10, pady=5,
            font=("Segoe UI", 9, "bold"), state="disabled",
        )
        self.review_button.pack(side="left", padx=3)
        tk.Button(
            actions, text="בחירת תיקיית יעד", command=self.choose_output_folder,
            bg="#F1E2C4", fg="#5A3518", relief="flat", padx=14, pady=9,
            font=("Segoe UI", 10, "bold"),
        ).pack(side="left", padx=4)

        files_card = tk.Frame(self.root, bg="#FFF9EC", padx=12, pady=10)
        files_card.pack(fill="x", padx=14, pady=8)
        tk.Label(
            files_card, text="הדוחות שנבחרו", bg="#FFF9EC", fg="#5A3518",
            font=("Segoe UI", 11, "bold"), anchor="e",
        ).pack(fill="x")
        self.files_label = tk.Label(
            files_card, text="לא נבחרו דוחות", bg="#FFF9EC", fg="#74471F",
            font=("Segoe UI", 9), anchor="e", justify="right", wraplength=1120,
        )
        self.files_label.pack(fill="x", pady=(5, 0))
        tk.Label(
            files_card, textvariable=self.output_text, bg="#FFF9EC", fg="#86633D",
            font=("Segoe UI", 9), anchor="e", justify="right", wraplength=1120,
        ).pack(fill="x", pady=(6, 0))

        summary_card = tk.Frame(self.root, bg="#F6D878", padx=14, pady=10)
        summary_card.pack(fill="x", padx=14, pady=(0, 8))
        tk.Label(
            summary_card, textvariable=self.summary, bg="#F6D878", fg="#332315",
            font=("Segoe UI", 11, "bold"), anchor="e", justify="right",
        ).pack(fill="x")

        table_card = tk.Frame(self.root, bg="#FFF9EC", padx=10, pady=10)
        table_card.pack(fill="both", expand=True, padx=14, pady=(0, 8))
        columns = ("selected", "page", "line", "text", "status", "reports", "variants")
        self.tree = ttk.Treeview(
            table_card, columns=columns, show="headings", selectmode="extended",
        )
        for column, title, width, anchor in (
            ("selected", "להוריד", 65, "center"),
            ("page", "עמוד", 70, "center"),
            ("line", "שורה", 70, "center"),
            ("text", "תחילת השורה", 190, "e"),
            ("status", "מצב ההקלטה", 170, "e"),
            ("reports", "דוחות מקור", 270, "e"),
            ("variants", "זיהויים נוספים", 230, "e"),
        ):
            self.tree.heading(column, text=title)
            self.tree.column(column, width=width, minwidth=55, anchor=anchor, stretch=True)
        yscroll = ttk.Scrollbar(table_card, orient="vertical", command=self.tree.yview)
        xscroll = ttk.Scrollbar(table_card, orient="horizontal", command=self.tree.xview)
        self.tree.configure(yscrollcommand=yscroll.set, xscrollcommand=xscroll.set)
        self.tree.bind("<Double-1>", self.toggle_row_selection)
        self.tree.bind("<space>", self.toggle_selected_rows)
        yscroll.pack(side="left", fill="y")
        xscroll.pack(side="bottom", fill="x")
        self.tree.pack(fill="both", expand=True)

        footer = tk.Frame(self.root, bg="#E7D4AB", padx=14, pady=10)
        footer.pack(fill="x")
        ttk.Progressbar(
            footer, variable=self.progress, maximum=100,
        ).pack(fill="x", pady=(0, 7))
        tk.Label(
            footer, textvariable=self.status, bg="#E7D4AB", fg="#5A3518",
            font=("Segoe UI", 10, "bold"), anchor="e", justify="right",
        ).pack(fill="x")

    def _ui(self, callback, *args) -> None:
        try:
            self.root.after(0, callback, *args)
        except tk.TclError:
            pass

    def choose_reports(self) -> None:
        selected = filedialog.askopenfilenames(
            title="בחר דוחות PDF למיפוי",
            filetypes=[("PDF", "*.pdf")],
        )
        if not selected:
            return
        seen: set[str] = set()
        self.pdf_paths = []
        for value in selected:
            path = Path(value)
            key = os.path.normcase(str(path.resolve()))
            if key not in seen:
                seen.add(key)
                self.pdf_paths.append(path)
        self.files_label.configure(text="  |  ".join(path.name for path in self.pdf_paths))
        self.status.set(f"נבחרו {len(self.pdf_paths)} דוחות. לחץ על מיפוי הדוחות.")
        self.mapped.clear()
        self._refresh_table()
        self._set_busy(False)

    def choose_output_folder(self) -> None:
        selected = filedialog.askdirectory(
            title="בחר תיקייה לשמירת תחילות השורה",
            initialdir=str(self.output_root.parent),
        )
        if selected:
            self.output_root = Path(selected)
            self.output_text.set(f"תיקיית יעד: {self.output_root}")
            try:
                self._ensure_output_structure(self.output_root)
            except OSError as error:
                messagebox.showerror(
                    TOOL_NAME, f"לא ניתן ליצור את תיקיית השמירה:\n{error}",
                )
                return
            if self.mapped:
                self.status.set("תיקיית היעד השתנתה; יש לבצע מיפוי מחדש.")
                self.mapped.clear()
                self._refresh_table()
                self._set_busy(False)

    def _set_busy(self, busy: bool) -> None:
        state = "disabled" if busy else "normal"
        self.choose_button.configure(state=state)
        self.map_button.configure(state=state)
        self.cancel_button.configure(state="normal" if busy else "disabled")
        if busy:
            labels = {
                "download": "עצירת ההורדה",
                "organize": "עצירת הסידור",
                "mapping": "עצירת המיפוי",
            }
            self.cancel_button.configure(
                text=labels.get(self.operation_kind, "עצירת הפעולה")
            )
        else:
            self.cancel_button.configure(text="עצירת ההורדה")
        self.download_button.configure(
            state="disabled" if busy or not self.mapped else "normal"
        )
        self.organize_button.configure(
            state="disabled" if busy or not self.mapped else "normal"
        )

    def cancel(self) -> None:
        self.cancel_event.set()
        if self.operation_kind == "download":
            self.status.set(
                "עוצר את ההורדה אחרי הקבוצה הנוכחית… כל מה שכבר הושלם יישמר"
            )
        elif self.operation_kind == "organize":
            self.status.set(
                "עוצר את הסידור… כל מה שכבר סודר יישאר בתיקיית היעד"
            )
        else:
            self.status.set("עוצר את המיפוי אחרי הדוח הנוכחי…")
        self.cancel_button.configure(state="disabled")

    def continue_in_background(self) -> None:
        if self.worker and self.worker.is_alive():
            self.status.set(
                "הפעולה ממשיכה ברקע. אפשר להמשיך לעבוד בקורא הדוחות."
            )
        self.root.iconify()

    def _manifest_entries(self) -> dict[str, dict]:
        path = self.output_root / MANIFEST_FILE
        try:
            value = json.loads(path.read_text(encoding="utf-8"))
            entries = value.get("entries", {}) if isinstance(value, dict) else {}
            return entries if isinstance(entries, dict) else {}
        except (OSError, ValueError, TypeError):
            return {}

    @staticmethod
    def _target_for(
        output_root: Path, page: str, line: str, display_text: str = "תחילת שורה",
    ) -> Path:
        page_label = f"{int(page):03d}" if page.isdigit() else safe_component(page, "לא מזוהה")
        line_label = f"{int(line):03d}" if line.isdigit() else safe_component(line, "לא מזוהה")
        word = safe_component(plain_display_word(display_text), "ללא מילה")
        return (
            output_root / "תחילות שורה" / f"עמוד {page_label}"
            / f"שורה {line_label} - {word}.mp3"
        )

    @staticmethod
    def _ensure_output_structure(output_root: Path) -> None:
        output_root.mkdir(parents=True, exist_ok=True)
        (output_root / "קבוע" / "מספרי עמודים").mkdir(parents=True, exist_ok=True)
        (output_root / "קבוע" / "מספרי שורות").mkdir(parents=True, exist_ok=True)
        line_starts = output_root / "תחילות שורה"
        line_starts.mkdir(parents=True, exist_ok=True)
        for page in range(1, 246):
            (line_starts / f"עמוד {page:03d}").mkdir(parents=True, exist_ok=True)

    def start_mapping(self) -> None:
        if self.worker and self.worker.is_alive():
            return
        try:
            self._ensure_output_structure(self.output_root)
        except OSError as error:
            messagebox.showerror(
                TOOL_NAME, f"לא ניתן ליצור את תיקיית השמירה:\n{error}",
            )
            return
        self.cancel_event.clear()
        self.progress.set(0)
        self.operation_kind = "mapping"
        self.status.set("בונה מיפוי של 245 עמודים × 42 שורות…")
        self._set_busy(True)
        pdfs = list(self.pdf_paths)
        output_root = self.output_root

        def worker() -> None:
            candidates: list[Candidate] = []
            errors: list[str] = []
            total = len(pdfs)
            for pdf_index, pdf_path in enumerate(pdfs, start=1):
                if self.cancel_event.is_set():
                    break

                def ocr_progress(message: str, _current: int, _total: int) -> None:
                    self._ui(
                        self.status.set,
                        f"{pdf_path.name} · {message} · דוח {pdf_index} מתוך {total}",
                    )

                try:
                    rows = ReportOcr(ocr_progress).read(pdf_path, use_cache=True)
                    for row in rows:
                        page = normalized_number(row.page)
                        line = normalized_number(row.line)
                        display_text = display_report_text(row, row.first_word).strip()
                        spoken_text = spoken_line_start(row) if row.first_word.strip() else ""
                        candidates.append(Candidate(
                            report=pdf_path.name, page=page, line=line,
                            display_text=display_text, spoken_text=spoken_text,
                            confidence=float(row.confidence or 0),
                            source_pdf_page=int(row.source_pdf_page or 0),
                        ))
                except Exception as error:
                    errors.append(f"{pdf_path.name}: {error}")
                self._ui(self.progress.set, pdf_index / max(1, total) * 75)
            if self.cancel_event.is_set():
                self._ui(self._mapping_finished, [], ["המיפוי בוטל"])
                return
            mapped = self._combine_candidates(candidates, output_root)
            try:
                self._write_statistics(mapped, output_root, pdfs)
            except OSError as error:
                errors.append(f"שמירת הסטטיסטיקה נכשלה: {error}")
            self._ui(self.progress.set, 100)
            self._ui(self._mapping_finished, mapped, errors)

        self.worker = threading.Thread(target=worker, name="one-time-line-map", daemon=True)
        self.worker.start()

    def _combine_candidates(
        self, candidates: list[Candidate], output_root: Path,
    ) -> list[MappedLine]:
        manifest_entries = self._manifest_entries()
        groups: dict[tuple[str, str], list[Candidate]] = defaultdict(list)
        unidentified: list[MappedLine] = []
        for candidate in candidates:
            missing = []
            if not candidate.page:
                missing.append("עמוד")
            if not candidate.line:
                missing.append("שורה")
            if not candidate.spoken_text:
                missing.append("תחילת שורה")
            if missing:
                unidentified.append(MappedLine(
                    page=candidate.page or "?", line=candidate.line or "?",
                    display_text=candidate.display_text or "?", spoken_text="",
                    reports=[candidate.report], target=None, cache_path=None,
                    status="חסר בזיהוי: " + ", ".join(missing),
                    variants=[], source_count=1,
                ))
                continue
            if not (
                candidate.page.isdigit() and 1 <= int(candidate.page) <= 245
                and candidate.line.isdigit() and 1 <= int(candidate.line) <= 42
            ):
                unidentified.append(MappedLine(
                    page=candidate.page or "?", line=candidate.line or "?",
                    display_text=candidate.display_text or "?", spoken_text="",
                    reports=[candidate.report], target=None, cache_path=None,
                    status="מחוץ לטווח 245×42", selected=False,
                ))
                continue
            groups[(candidate.page, candidate.line)].append(candidate)

        mapped: list[MappedLine] = []
        for page_number in range(1, 246):
            for line_number in range(1, 43):
                page = str(page_number)
                line = str(line_number)
                values = groups.get((page, line), [])
                corpus_display, corpus_spoken = corpus_line_start(page_number, line_number)
                counts = Counter(value.spoken_text for value in values if value.spoken_text)
                confidence: dict[str, float] = defaultdict(float)
                display_by_spoken: dict[str, str] = {}
                for value in values:
                    confidence[value.spoken_text] += value.confidence
                    display_by_spoken.setdefault(value.spoken_text, value.display_text)
                report_chosen = ""
                report_display = ""
                if counts:
                    report_chosen = max(
                        counts,
                        key=lambda text: (counts[text], confidence[text], len(text)),
                    )
                    report_display = display_by_spoken.get(
                        report_chosen, plain_display_word(report_chosen),
                    )
                force_corpus = page_number in FORCE_CORPUS_PAGES
                if force_corpus and corpus_spoken:
                    chosen = corpus_spoken
                    display_text = corpus_display
                elif force_corpus:
                    mapped.append(MappedLine(
                        page=page, line=line, display_text="—", spoken_text="",
                        reports=sorted({value.report for value in values}) or ["תיקון קוראים"],
                        target=None, cache_path=None,
                        status=(
                            "שורה ריקה בתיקון קוראים — אין מה להקליט · "
                            "עמוד מוגדר תמיד לפי תיקון קוראים"
                        ),
                        variants=[value.spoken_text for value in values if value.spoken_text],
                        source_count=len(values), selected=False,
                        download_allowed=False, corpus_only=not bool(values),
                        force_corpus=True, decision="corpus_forced",
                    ))
                    continue
                elif report_chosen:
                    chosen = report_chosen
                    display_text = report_display
                elif corpus_spoken:
                    chosen = corpus_spoken
                    display_text = corpus_display
                else:
                    mapped.append(MappedLine(
                        page=page, line=line, display_text="—", spoken_text="",
                        reports=sorted({value.report for value in values}),
                        target=None, cache_path=None,
                        status="שורה ריקה במאגר — אין מה להקליט",
                        variants=[], source_count=len(values), selected=False,
                        download_allowed=False,
                    ))
                    continue
                variants = [
                    text for text, _count in counts.most_common()
                    if text and text != chosen
                ]
                corpus_differs = bool(
                    report_chosen and corpus_spoken and report_chosen != corpus_spoken
                )
                if corpus_differs and not force_corpus and corpus_spoken not in variants:
                    variants.append(f"תיקון קוראים: {corpus_spoken}")
                target = self._target_for(output_root, page, line, display_text)
                cache_path = SpeechWorker._recorded_avri_cache_path(chosen)
                entry = manifest_entries.get(f"{page}\u0000{line}", {})
                target_valid = bool(
                    isinstance(entry, dict)
                    and entry.get("spoken_text") == chosen
                    and entry.get("file") == str(target.relative_to(output_root))
                    and SpeechWorker._valid_cached_clip(target)
                )
                cache_valid = SpeechWorker._valid_cached_clip(cache_path)
                if target_valid:
                    status = "קיים בתיקייה"
                elif cache_valid:
                    status = "קיים במטמון — נדרש רק לסדר בתיקייה"
                else:
                    status = "חסרה הקלטה"
                if variants:
                    status += " · נמצאו זיהויים שונים"
                if force_corpus:
                    status += " · עמוד מוגדר תמיד לפי תיקון קוראים"
                from_report = bool(values)
                corpus_allowed = self.allow_corpus_download_value
                if not from_report:
                    status += (
                        " · תיקון קוראים בלבד — ניתן להורדה"
                        if corpus_allowed
                        else " · תיקון קוראים בלבד — לא יורד כרגע"
                    )
                mapped.append(MappedLine(
                    page=page, line=line, display_text=display_text,
                    spoken_text=chosen,
                    reports=sorted({value.report for value in values}) or ["תיקון קוראים"],
                    target=target, cache_path=cache_path, status=status,
                    variants=variants, source_count=len(values),
                    selected=from_report or corpus_allowed,
                    download_allowed=from_report or corpus_allowed,
                    corpus_only=not from_report,
                    report_spoken_text=report_chosen,
                    report_display_text=report_display,
                    corpus_spoken_text=corpus_spoken,
                    corpus_display_text=corpus_display,
                    decision=(
                        "corpus_forced" if force_corpus
                        else ("report" if report_chosen else "corpus")
                    ),
                    force_corpus=force_corpus,
                ))

        def sort_key(item: MappedLine):
            page_key = (0, int(item.page)) if item.page.isdigit() else (1, item.page)
            line_key = (0, int(item.line)) if item.line.isdigit() else (1, item.line)
            return page_key, line_key, item.display_text

        return sorted(mapped, key=sort_key) + unidentified

    def _mapping_finished(self, mapped: list[MappedLine], errors: list[str]) -> None:
        self.operation_kind = ""
        self.mapped = mapped
        self._set_busy(False)
        self._refresh_table()
        conflicts = self._decision_conflicts()
        self.review_button.configure(state="normal" if conflicts else "disabled")
        if not mapped:
            self.status.set(errors[0] if errors else "לא נמצאו שורות למיפוי")
            if errors and errors != ["המיפוי בוטל"]:
                messagebox.showerror(TOOL_NAME, "\n".join(errors[:8]))
            return
        self.status.set(
            f"המיפוי הושלם. הסטטיסטיקה נשמרה בתיקיית היעד"
            + (f" · {len(errors)} דוחות נכשלו" if errors else "")
        )
        if errors:
            messagebox.showwarning(TOOL_NAME, "\n".join(errors[:8]))
        if conflicts:
            self.root.after(150, self.open_conflict_review)

    def _decision_conflicts(self) -> list[MappedLine]:
        return [
            item for item in self.mapped
            if not item.force_corpus
            and item.report_spoken_text and item.corpus_spoken_text
            and item.report_spoken_text != item.corpus_spoken_text
        ]

    def _set_conflict_choice(
        self, item: MappedLine, choice: str,
        manifest_entries: dict[str, dict] | None = None,
    ) -> None:
        if choice == "corpus":
            spoken = item.corpus_spoken_text
            display = item.corpus_display_text or plain_display_word(spoken)
            choice_label = "תיקון קוראים"
        else:
            spoken = item.report_spoken_text
            display = item.report_display_text or plain_display_word(spoken)
            choice = "report"
            choice_label = "הדוח"
        if not spoken:
            return
        item.spoken_text = spoken
        item.display_text = display
        item.decision = choice
        item.target = self._target_for(self.output_root, item.page, item.line, display)
        item.cache_path = SpeechWorker._recorded_avri_cache_path(spoken)
        if manifest_entries is None:
            manifest_entries = self._manifest_entries()
        manifest_entry = manifest_entries.get(item.key, {})
        target_valid = bool(
            isinstance(manifest_entry, dict)
            and manifest_entry.get("spoken_text") == spoken
            and manifest_entry.get("file") == str(item.target.relative_to(self.output_root))
            and SpeechWorker._valid_cached_clip(item.target)
        )
        if target_valid:
            item.status = "קיים בתיקייה"
        elif SpeechWorker._valid_cached_clip(item.cache_path):
            item.status = "קיים במטמון — נדרש רק לסדר בתיקייה"
        else:
            item.status = "חסרה הקלטה"
        item.status += f" · הוכרע לפי {choice_label}"
        item.download_allowed = True
        item.selected = True

    def open_conflict_review(self) -> None:
        conflicts = self._decision_conflicts()
        if not conflicts:
            messagebox.showinfo(TOOL_NAME, "לא נמצאו הבדלים בין הדוחות לתיקון קוראים.")
            return
        if self.review_dialog is not None:
            try:
                if self.review_dialog.winfo_exists():
                    self.review_dialog.lift()
                    return
            except tk.TclError:
                pass
        dialog = tk.Toplevel(self.root)
        self.review_dialog = dialog
        dialog.title("הכרעה בין הדוח לתיקון קוראים")
        dialog.configure(bg="#E7D4AB")
        fit_window_to_work_area(dialog, 1040, 690, 760, 520)
        dialog.transient(self.root)
        tk.Label(
            dialog, text="הכרעה בהבדלי זיהוי", bg="#5A3518", fg="white",
            font=("Segoe UI", 16, "bold"), pady=12,
        ).pack(fill="x")
        tk.Label(
            dialog,
            text=(
                f"נמצאו {len(conflicts)} שורות שבהן המילה בדוח שונה מתיקון קוראים. "
                "בחר שורות וקבע לפי איזה מקור להכין את ההקלטה."
            ),
            bg="#FFF9EC", fg="#5A3518", font=("Segoe UI", 10),
            anchor="e", justify="right", wraplength=950, padx=14, pady=10,
        ).pack(fill="x", padx=14, pady=(12, 8))

        table = tk.Frame(dialog, bg="#FFF9EC", padx=9, pady=9)
        table.pack(fill="both", expand=True, padx=14, pady=(0, 8))
        tree = ttk.Treeview(
            table,
            columns=("page", "line", "report", "corpus", "choice", "sources"),
            show="headings", selectmode="extended",
        )
        for column, title, width, anchor in (
            ("page", "עמוד", 60, "center"),
            ("line", "שורה", 60, "center"),
            ("report", "לפי הדוח", 190, "e"),
            ("corpus", "לפי תיקון קוראים", 210, "e"),
            ("choice", "הבחירה", 120, "center"),
            ("sources", "דוחות", 250, "e"),
        ):
            tree.heading(column, text=title)
            tree.column(column, width=width, minwidth=50, anchor=anchor, stretch=True)
        scroll = ttk.Scrollbar(table, orient="vertical", command=tree.yview)
        tree.configure(yscrollcommand=scroll.set)
        scroll.pack(side="left", fill="y")
        tree.pack(fill="both", expand=True)

        for index, item in enumerate(conflicts):
            tree.insert("", "end", iid=str(index), values=(
                item.page, item.line,
                item.report_display_text or item.report_spoken_text,
                item.corpus_display_text or item.corpus_spoken_text,
                "הדוח" if item.decision == "report" else "תיקון קוראים",
                " | ".join(item.reports),
            ))

        def apply_choice(choice: str, apply_all: bool = False) -> None:
            if apply_all:
                indexes = list(range(len(conflicts)))
            else:
                indexes = []
                for item_id in tree.selection():
                    try:
                        indexes.append(int(item_id))
                    except ValueError:
                        pass
                if not indexes:
                    messagebox.showinfo(
                        TOOL_NAME, "בחר שורה אחת או יותר בטבלה.", parent=dialog,
                    )
                    return
            manifest_entries = self._manifest_entries()
            for index in indexes:
                item = conflicts[index]
                self._set_conflict_choice(item, choice, manifest_entries)
                tree.set(
                    str(index), "choice",
                    "הדוח" if item.decision == "report" else "תיקון קוראים",
                )

        def save_and_close() -> None:
            try:
                self._write_statistics(self.mapped, self.output_root, list(self.pdf_paths))
            except OSError as error:
                messagebox.showerror(
                    TOOL_NAME, f"שמירת ההכרעות נכשלה:\n{error}", parent=dialog,
                )
                return
            self._refresh_table()
            self.review_dialog = None
            dialog.destroy()

        buttons = tk.Frame(dialog, bg="#E7D4AB", padx=12, pady=10)
        buttons.pack(fill="x")
        tk.Button(
            buttons, text="לפי הדוח — למסומנות",
            command=lambda: apply_choice("report"), bg="#74471F", fg="white",
            relief="flat", padx=13, pady=8, font=("Segoe UI", 9, "bold"),
        ).pack(side="right", padx=3)
        tk.Button(
            buttons, text="לפי תיקון קוראים — למסומנות",
            command=lambda: apply_choice("corpus"), bg="#A7650B", fg="white",
            relief="flat", padx=13, pady=8, font=("Segoe UI", 9, "bold"),
        ).pack(side="right", padx=3)
        tk.Button(
            buttons, text="הכול לפי הדוח",
            command=lambda: apply_choice("report", True), bg="#F1E2C4",
            fg="#5A3518", relief="flat", padx=11, pady=8,
        ).pack(side="right", padx=3)
        tk.Button(
            buttons, text="הכול לפי תיקון קוראים",
            command=lambda: apply_choice("corpus", True), bg="#F1E2C4",
            fg="#5A3518", relief="flat", padx=11, pady=8,
        ).pack(side="right", padx=3)
        tk.Button(
            buttons, text="שמירת ההכרעות וסגירה",
            command=save_and_close, bg="#278552", fg="white", relief="flat",
            padx=16, pady=8, font=("Segoe UI", 9, "bold"),
        ).pack(side="left", padx=3)
        dialog.protocol("WM_DELETE_WINDOW", save_and_close)

    def _refresh_table(self) -> None:
        self.tree.delete(*self.tree.get_children())
        for index, item in enumerate(self.mapped):
            self.tree.insert("", "end", iid=str(index), values=(
                (
                    "✓" if item.selected and item.target is not None
                    else ("×" if item.target is not None and not item.download_allowed else "—")
                ),
                item.page, item.line, item.display_text, item.status,
                " | ".join(item.reports), " | ".join(item.variants),
            ))
        mapped = [item for item in self.mapped if item.target is not None]
        unidentified = len(self.mapped) - len(mapped)
        selected = sum(1 for item in mapped if item.selected and item.download_allowed)
        report_lines = sum(1 for item in mapped if item.download_allowed)
        existing = sum(
            1 for item in mapped
            if item.status.startswith("קיים") or item.status.startswith("נשמר")
        )
        missing = sum(1 for item in mapped if "חסרה הקלטה" in item.status)
        conflicts = sum(1 for item in mapped if item.variants)
        pages = len({item.page for item in mapped})
        page_numbers_existing = sum(
            1 for number in range(1, 246)
            if SpeechWorker._valid_cached_clip(
                self.output_root / "קבוע" / "מספרי עמודים" / f"{number:03d}.mp3"
            ) or SpeechWorker._valid_cached_clip(
                SpeechWorker._recorded_avri_cache_path(str(number))
            )
        )
        line_numbers_existing = sum(
            1 for number in range(1, 43)
            if SpeechWorker._valid_cached_clip(
                self.output_root / "קבוע" / "מספרי שורות" / f"{number:03d}.mp3"
            ) or SpeechWorker._valid_cached_clip(
                SpeechWorker._recorded_avri_cache_path(str(number))
            )
        )
        self.summary.set(
            f"עמודים: {pages}  |  שורות עם טקסט: {len(mapped)}  |  "
            f"נמצאו בדוחות: {report_lines}  |  מסומנות: {selected}  |  "
            f"הקלטות קיימות: {existing}  |  חסרות: {missing}  |  "
            f"שורות ריקות/לא מזוהות: {unidentified}  |  זיהויים שונים: {conflicts}\n"
            f"מספרי עמודים קיימים: {page_numbers_existing}/245  |  "
            f"מספרי שורות קיימים: {line_numbers_existing}/42"
        )

    def mark_rows(self, mode: str) -> None:
        for item in self.mapped:
            if item.target is None or not item.download_allowed:
                item.selected = False
            elif mode == "all":
                item.selected = True
            elif mode == "none":
                item.selected = False
            elif mode == "missing":
                item.selected = "חסרה הקלטה" in item.status
        self._refresh_table()

    def apply_corpus_download_choice(self) -> None:
        allowed = bool(self.allow_corpus_download.get())
        self.allow_corpus_download_value = allowed
        for item in self.mapped:
            if not item.corpus_only or item.target is None:
                continue
            item.download_allowed = allowed
            item.selected = allowed
            item.status = re.sub(
                r" · תיקון קוראים בלבד — (?:לא יורד כרגע|ניתן להורדה)$",
                "",
                item.status,
            )
            item.status += (
                " · תיקון קוראים בלבד — ניתן להורדה"
                if allowed else " · תיקון קוראים בלבד — לא יורד כרגע"
            )
        self._refresh_table()

    def toggle_row_selection(self, event) -> None:
        item_id = self.tree.identify_row(event.y)
        if not item_id:
            return
        try:
            item = self.mapped[int(item_id)]
        except (ValueError, IndexError):
            return
        if item.target is not None and item.download_allowed:
            item.selected = not item.selected
            self._refresh_table()

    def toggle_selected_rows(self, _event=None) -> str:
        indexes: list[int] = []
        for item_id in self.tree.selection():
            try:
                indexes.append(int(item_id))
            except ValueError:
                pass
        eligible = [
            self.mapped[index] for index in indexes
            if self.mapped[index].target is not None
            and self.mapped[index].download_allowed
        ]
        select = not all(item.selected for item in eligible) if eligible else False
        for item in eligible:
            item.selected = select
        self._refresh_table()
        return "break"

    def start_download(self, organize_only: bool = False) -> None:
        if not self.mapped or (self.worker and self.worker.is_alive()):
            return
        try:
            self._ensure_output_structure(self.output_root)
        except OSError as error:
            messagebox.showerror(
                TOOL_NAME, f"לא ניתן ליצור את תיקיית השמירה:\n{error}",
            )
            return
        tasks: list[dict[str, object]] = []
        if self.include_page_numbers.get():
            for number in range(1, 246):
                text = str(number)
                target = self.output_root / "קבוע" / "מספרי עמודים" / f"{number:03d}.mp3"
                tasks.append({
                    "text": text, "target": target,
                    "cache": SpeechWorker._recorded_avri_cache_path(text),
                    "mapped": None, "kind": "מספרי עמודים",
                    "target_valid": SpeechWorker._valid_cached_clip(target),
                })
        if self.include_line_numbers.get():
            for number in range(1, 43):
                text = str(number)
                target = self.output_root / "קבוע" / "מספרי שורות" / f"{number:03d}.mp3"
                tasks.append({
                    "text": text, "target": target,
                    "cache": SpeechWorker._recorded_avri_cache_path(text),
                    "mapped": None, "kind": "מספרי שורות",
                    "target_valid": SpeechWorker._valid_cached_clip(target),
                })
        if self.include_line_starts.get():
            for item in self.mapped:
                if (
                    item.selected and item.download_allowed
                    and item.target is not None and item.cache_path is not None
                ):
                    tasks.append({
                        "text": item.spoken_text, "target": item.target,
                        "cache": item.cache_path, "mapped": item,
                        "kind": "תחילות שורה",
                        "target_valid": item.status.startswith("קיים בתיקייה"),
                    })
        if not tasks:
            messagebox.showinfo(TOOL_NAME, "לא סומן דבר להורדה או לסידור.")
            return
        if organize_only:
            tasks = [
                task for task in tasks
                if SpeechWorker._valid_cached_clip(task["cache"])
                or (
                    bool(task["target_valid"])
                    and SpeechWorker._valid_cached_clip(task["target"])
                )
            ]
            if not tasks:
                messagebox.showinfo(
                    TOOL_NAME,
                    "לא נמצאו הקלטות קיימות לסידור בקטגוריות שסומנו.\n"
                    "לא בוצעה שום הורדה מהאינטרנט.",
                )
                return
        missing_network = [
            task for task in tasks
            if not SpeechWorker._valid_cached_clip(task["cache"])
            and not bool(task["target_valid"])
        ]
        selected_line_starts = sum(1 for task in tasks if task["kind"] == "תחילות שורה")
        if organize_only:
            confirmation = (
                f"לסדר {len(tasks)} הקלטות שכבר קיימות במחשב?\n"
                f"תחילות שורה קיימות: {selected_line_starts}\n\n"
                "במצב זה לא תתבצע הורדה מהאינטרנט ולא ייווצרו הקלטות חדשות."
            )
        else:
            confirmation = (
                f"להכין {len(tasks)} קבצים שסומנו?\n"
                f"תחילות שורה מסומנות: {selected_line_starts}\n"
                f"מתוכן {len(missing_network)} הקלטות דורשות הורדה מהאינטרנט."
            )
        if not messagebox.askyesno(
            TOOL_NAME,
            confirmation,
        ):
            return
        self.cancel_event.clear()
        self.progress.set(0)
        self.operation_kind = "organize" if organize_only else "download"
        if organize_only:
            self.root.title(f"{TOOL_NAME} — מסדר הקלטות קיימות")
            self.status.set(
                "מסדר רק הקלטות קיימות. לא מתבצעת שום הורדה מהאינטרנט."
            )
        else:
            self.root.title(f"{TOOL_NAME} — ההורדה ממשיכה ברקע")
            self.status.set(
                "ההורדה התחילה ברקע. אפשר ללחוץ „מזער והמשך ברקע” ולעבוד כרגיל."
            )
        self._set_busy(True)
        output_root = self.output_root
        pdfs = list(self.pdf_paths)

        def worker() -> None:
            errors: list[str] = []
            # If a verified organized file exists but the shared application
            # cache was cleared, restore it without any network request.
            for task in tasks:
                cache = task["cache"]
                target = task["target"]
                if (
                    isinstance(cache, Path) and isinstance(target, Path)
                    and bool(task["target_valid"])
                    and SpeechWorker._valid_cached_clip(target)
                    and not SpeechWorker._valid_cached_clip(cache)
                ):
                    try:
                        self._link_clip(target, cache)
                    except OSError as error:
                        errors.append(str(error))
            # Organize-only is deliberately kept network-free. Even if a file
            # disappears between task discovery and this worker, it remains
            # missing and is never passed to the quality speech provider.
            unique_missing = [] if organize_only else list(dict.fromkeys(
                str(task["text"]) for task in tasks
                if str(task["text"])
                and not SpeechWorker._valid_cached_clip(task["cache"])
            ))
            downloaded_texts: set[str] = set()
            total_work = max(1, len(unique_missing) + len(tasks))
            completed = 0
            # Small batches make the stop button react quickly while keeping
            # network preparation efficient.
            for offset in range(0, len(unique_missing), 4):
                if self.cancel_event.is_set():
                    break
                batch = unique_missing[offset:offset + 4]
                try:
                    self.speech.prepare_quality_clips(batch, 0, RECORDED_AVRI_VOICE)
                    downloaded_texts.update(batch)
                except Exception as error:
                    errors.append(str(error))
                completed += len(batch)
                self._ui(self.progress.set, completed / total_work * 100)
                self._ui(
                    self.status.set,
                    f"מוריד קטעי קול: {min(offset + len(batch), len(unique_missing))} "
                    f"מתוך {len(unique_missing)}",
                )

            if not self.cancel_event.is_set():
                for task in tasks:
                    if self.cancel_event.is_set():
                        break
                    try:
                        target = task["target"]
                        cache = task["cache"]
                        assert isinstance(target, Path) and isinstance(cache, Path)
                        mapped_item = task.get("mapped")
                        if not SpeechWorker._valid_cached_clip(cache):
                            if isinstance(mapped_item, MappedLine):
                                mapped_item.status = "ההורדה נכשלה"
                                mapped_item.error = "קובץ הקול לא נוצר"
                        else:
                            self._link_clip(cache, target)
                            if isinstance(mapped_item, MappedLine):
                                if organize_only:
                                    mapped_item.status = "סודר בתיקייה מהקיים"
                                else:
                                    mapped_item.status = (
                                        "הורד ונשמר בתיקייה"
                                        if mapped_item.spoken_text in downloaded_texts
                                        else "נשמר בתיקייה מהמטמון"
                                    )
                    except Exception as error:
                        mapped_item = task.get("mapped")
                        if isinstance(mapped_item, MappedLine):
                            mapped_item.status = "שמירת הקובץ נכשלה"
                            mapped_item.error = str(error)
                            label = f"עמוד {mapped_item.page}, שורה {mapped_item.line}"
                        else:
                            label = str(task.get("kind", "קובץ"))
                        errors.append(f"{label}: {error}")
                    completed += 1
                    self._ui(self.progress.set, completed / total_work * 100)
            try:
                self._write_statistics(self.mapped, output_root, pdfs)
            except OSError as error:
                errors.append(f"שמירת הסטטיסטיקה נכשלה: {error}")
            self._ui(
                self._download_finished,
                errors,
                self.cancel_event.is_set(),
                organize_only,
            )

        self.worker = threading.Thread(target=worker, name="one-time-line-download", daemon=True)
        self.worker.start()

    @staticmethod
    def _link_clip(source: Path, target: Path) -> None:
        target.parent.mkdir(parents=True, exist_ok=True)
        temporary = target.with_name(f".{target.name}.{uuid.uuid4().hex}.tmp")
        try:
            try:
                os.link(source, temporary)
            except OSError:
                shutil.copy2(source, temporary)
            os.replace(temporary, target)
        finally:
            temporary.unlink(missing_ok=True)

    def _download_finished(
        self, errors: list[str], cancelled: bool, organize_only: bool = False,
    ) -> None:
        self.operation_kind = ""
        self.root.title(TOOL_NAME)
        self._set_busy(False)
        self._refresh_table()
        if cancelled:
            if organize_only:
                self.status.set(
                    "הסידור נעצר. הקבצים שכבר סודרו נשארו בתיקיית היעד."
                )
            else:
                self.status.set(
                    "ההורדה נעצרה. הקבצים שכבר הושלמו נשמרו; "
                    "בלחיצה הבאה יורדו רק החסרים."
                )
        elif errors:
            self.status.set(f"הפעולה הסתיימה עם {len(errors)} שגיאות")
            messagebox.showwarning(TOOL_NAME, "\n".join(errors[:8]))
        else:
            self.progress.set(100)
            self.status.set(
                "כל ההקלטות הקיימות סודרו; לא בוצעה הורדה מהאינטרנט"
                if organize_only
                else "כל תחילות השורה הורדו וסודרו לפי עמוד ומספר שורה"
            )
        try:
            self.root.bell()
        except tk.TclError:
            pass

    def _write_statistics(
        self, mapped: list[MappedLine], output_root: Path, pdfs: list[Path],
    ) -> None:
        self._ensure_output_structure(output_root)
        rows: list[dict[str, object]] = []
        manifest_entries: dict[str, dict[str, object]] = {}
        for item in mapped:
            row = {
                "עמוד": item.page,
                "שורה": item.line,
                "תחילת השורה": item.display_text,
                "טקסט להקראה": item.spoken_text,
                "מצב": item.status,
                "דוחות מקור": " | ".join(item.reports),
                "מספר מופעים": item.source_count,
                "זיהויים נוספים": " | ".join(item.variants),
                "זיהוי מהדוח": item.report_display_text,
                "זיהוי מתיקון קוראים": item.corpus_display_text,
                "הכרעה": (
                    "לפי הדוח" if item.decision == "report"
                    else (
                        "תמיד לפי תיקון קוראים"
                        if item.decision == "corpus_forced"
                        else ("לפי תיקון קוראים" if item.decision == "corpus" else "")
                    )
                ),
                "מסומן להורדה": "כן" if item.selected else "לא",
                "קובץ": str(item.target or ""),
                "שגיאה": item.error,
            }
            rows.append(row)
            if item.target is not None:
                manifest_entries[item.key] = {
                    "page": item.page, "line": item.line,
                    "display_text": item.display_text,
                    "spoken_text": item.spoken_text,
                    "file": str(item.target.relative_to(output_root)),
                    "status": item.status, "reports": item.reports,
                    "variants": item.variants, "selected": item.selected,
                    "report_text": item.report_spoken_text,
                    "corpus_text": item.corpus_spoken_text,
                    "decision": item.decision,
                    "force_corpus": item.force_corpus,
                }
        fieldnames = list(rows[0].keys()) if rows else [
            "עמוד", "שורה", "תחילת השורה", "טקסט להקראה", "מצב",
            "דוחות מקור", "מספר מופעים", "זיהויים נוספים", "זיהוי מהדוח",
            "זיהוי מתיקון קוראים", "הכרעה", "מסומן להורדה",
            "קובץ", "שגיאה",
        ]
        stats_path = output_root / STATISTICS_FILE
        temporary_stats = stats_path.with_suffix(".csv.tmp")
        with temporary_stats.open("w", encoding="utf-8-sig", newline="") as handle:
            writer = csv.DictWriter(handle, fieldnames=fieldnames)
            writer.writeheader()
            writer.writerows(rows)
        os.replace(temporary_stats, stats_path)

        page_values: dict[str, dict[str, int]] = defaultdict(
            lambda: {"mapped": 0, "existing": 0, "missing": 0, "unidentified": 0, "conflicts": 0}
        )
        for item in mapped:
            values = page_values[item.page]
            if item.target is None:
                values["unidentified"] += 1
                continue
            values["mapped"] += 1
            if item.status.startswith("קיים") or item.status.startswith("נשמר") or item.status.startswith("הורד"):
                values["existing"] += 1
            else:
                values["missing"] += 1
            if item.variants:
                values["conflicts"] += 1
        page_path = output_root / PAGE_SUMMARY_FILE
        temporary_page = page_path.with_suffix(".csv.tmp")
        with temporary_page.open("w", encoding="utf-8-sig", newline="") as handle:
            writer = csv.writer(handle)
            writer.writerow(("עמוד", "שורות ממופות", "קיים", "חסר", "חסר בזיהוי", "זיהויים שונים"))
            for page, values in sorted(
                page_values.items(),
                key=lambda pair: (0, int(pair[0])) if pair[0].isdigit() else (1, pair[0]),
            ):
                writer.writerow((
                    page, values["mapped"], values["existing"], values["missing"],
                    values["unidentified"], values["conflicts"],
                ))
        os.replace(temporary_page, page_path)

        manifest = {
            "version": 1,
            "updated_at": datetime.now().isoformat(timespec="seconds"),
            "voice": "he-IL-AvriNeural",
            "reports": [str(path) for path in pdfs],
            "entries": manifest_entries,
        }
        manifest_path = output_root / MANIFEST_FILE
        temporary_manifest = manifest_path.with_suffix(".json.tmp")
        temporary_manifest.write_text(
            json.dumps(manifest, ensure_ascii=False, indent=2), encoding="utf-8",
        )
        os.replace(temporary_manifest, manifest_path)

    def open_output_folder(self) -> None:
        try:
            self._ensure_output_structure(self.output_root)
        except OSError as error:
            messagebox.showerror(TOOL_NAME, f"לא ניתן ליצור את התיקייה:\n{error}")
            return
        try:
            os.startfile(str(self.output_root))  # type: ignore[attr-defined]
        except OSError as error:
            messagebox.showerror(TOOL_NAME, f"לא ניתן לפתוח את התיקייה:\n{error}")

    def close(self) -> None:
        if self.worker and self.worker.is_alive():
            if not messagebox.askyesno(TOOL_NAME, "פעולה עדיין מתבצעת. לעצור ולסגור?"):
                return
            self.cancel_event.set()
        self.speech.close()
        self.root.destroy()


def self_test() -> None:
    classic = ReportRow(
        page="64", line="4", first_word="ישראל", confidence=91,
        report_kind="classic",
    )
    duplicate = ReportRow(
        page="064", line="04", first_word="ישראל", confidence=88,
        report_kind="classic",
    )
    assert normalized_number(classic.page) == normalized_number(duplicate.page) == "64"
    assert normalized_number(classic.line) == normalized_number(duplicate.line) == "4"
    assert spoken_line_start(classic)
    report_override = ReportRow(
        page="1", line="1", first_word="שונה", confidence=99,
        report_kind="classic",
    )
    assert _speech_word_key(spoken_line_start(report_override)) == "שונה"
    matching_report = ReportRow(
        page="1", line="1", first_word="בראשית", confidence=99,
        report_kind="classic",
    )
    assert _speech_word_key(spoken_line_start(matching_report)) == "בראשית"
    assert spoken_line_start(matching_report) != "בראשית"
    target = LineStartMapper._target_for(Path("X"), "64", "4", "ישראל")
    assert target == (
        Path("X") / "תחילות שורה" / "עמוד 064" / "שורה 004 - ישראל.mp3"
    )
    nonempty = sum(
        1 for page in range(1, 246) for line in range(1, 43)
        if corpus_line_start(page, line)[1]
    )
    assert nonempty == 10_270
    print("SELF_TEST_OK")


def main() -> None:
    if "--self-test" in sys.argv:
        self_test()
        return
    enable_windows_dpi_awareness()
    root = tk.Tk()
    LineStartMapper(root)
    root.mainloop()


if __name__ == "__main__":
    main()
