from __future__ import annotations

import base64
import json
import os
import re
import shutil
import socket
import subprocess
import tempfile
import threading
import time
import urllib.error
import urllib.request
import zipfile
from dataclasses import dataclass
from pathlib import Path
from typing import Callable


AI_USER_AGENT = "DukReportReader-OfflineAI/1.0"
LLAMA_RELEASE_API = "https://api.github.com/repos/ggml-org/llama.cpp/releases/latest"


@dataclass(frozen=True)
class AiArtifact:
    key: str
    label: str
    filename: str
    url: str
    approximate_bytes: int


AI_ARTIFACTS = {
    "text": AiArtifact(
        key="text",
        label="AI טקסט — Qwen3 4B",
        filename="Qwen3-4B-Q4_K_M.gguf",
        url=(
            "https://huggingface.co/Qwen/Qwen3-4B-GGUF/resolve/main/"
            "Qwen3-4B-Q4_K_M.gguf?download=true"
        ),
        approximate_bytes=2_500_000_000,
    ),
    "vision": AiArtifact(
        key="vision",
        label="AI ראייה — Qwen3-VL 4B",
        filename="Qwen3VL-4B-Instruct-Q4_K_M.gguf",
        url=(
            "https://huggingface.co/Qwen/Qwen3-VL-4B-Instruct-GGUF/resolve/main/"
            "Qwen3VL-4B-Instruct-Q4_K_M.gguf?download=true"
        ),
        approximate_bytes=2_500_000_000,
    ),
    "vision_projector": AiArtifact(
        key="vision_projector",
        label="מפענח תמונה — Qwen3-VL",
        filename="mmproj-Qwen3VL-4B-Instruct-Q8_0.gguf",
        url=(
            "https://huggingface.co/Qwen/Qwen3-VL-4B-Instruct-GGUF/resolve/main/"
            "mmproj-Qwen3VL-4B-Instruct-Q8_0.gguf?download=true"
        ),
        approximate_bytes=500_000_000,
    ),
}


class OfflineAiCancelled(RuntimeError):
    pass


class OfflineAiManager:
    """Download and run private, local-only language and vision models."""

    def __init__(self, root: Path):
        self.root = Path(root)
        self.models_dir = self.root / "models"
        self.runtime_dir = self.root / "llama-runtime"
        self.downloads_dir = self.root / "downloads"
        self.logs_dir = self.root / "logs"
        for directory in (self.models_dir, self.runtime_dir, self.downloads_dir, self.logs_dir):
            directory.mkdir(parents=True, exist_ok=True)
        self._server_lock = threading.RLock()
        self._request_lock = threading.Lock()
        self._server: subprocess.Popen | None = None
        self._server_kind = ""
        self._server_port = 0
        self._server_log = None

    @property
    def server_executable(self) -> Path:
        direct = self.runtime_dir / "llama-server.exe"
        if direct.is_file():
            return direct
        matches = list(self.runtime_dir.rglob("llama-server.exe"))
        return matches[0] if matches else direct

    def artifact_path(self, key: str) -> Path:
        return self.models_dir / AI_ARTIFACTS[key].filename

    @staticmethod
    def _valid_large_file(path: Path, expected: int) -> bool:
        try:
            return path.is_file() and path.stat().st_size >= max(1_000_000, int(expected * 0.72))
        except OSError:
            return False

    def runtime_ready(self) -> bool:
        return self.server_executable.is_file()

    def text_ready(self) -> bool:
        spec = AI_ARTIFACTS["text"]
        return self._valid_large_file(self.artifact_path("text"), spec.approximate_bytes)

    def vision_ready(self) -> bool:
        model = AI_ARTIFACTS["vision"]
        projector = AI_ARTIFACTS["vision_projector"]
        return (
            self._valid_large_file(self.artifact_path("vision"), model.approximate_bytes)
            and self._valid_large_file(
                self.artifact_path("vision_projector"), projector.approximate_bytes,
            )
        )

    def status(self) -> dict[str, object]:
        def size(path: Path) -> int:
            try:
                return path.stat().st_size
            except OSError:
                return 0

        return {
            "runtime": self.runtime_ready(),
            "text": self.text_ready(),
            "vision": self.vision_ready(),
            "text_bytes": size(self.artifact_path("text")),
            "vision_bytes": size(self.artifact_path("vision")) + size(
                self.artifact_path("vision_projector")
            ),
            "running": bool(self._server and self._server.poll() is None),
            "running_kind": self._server_kind,
        }

    @staticmethod
    def _request_json(url: str, timeout: float = 30.0) -> dict:
        request = urllib.request.Request(
            url, headers={"User-Agent": AI_USER_AGENT, "Accept": "application/json"},
        )
        with urllib.request.urlopen(request, timeout=timeout) as response:
            payload = json.loads(response.read().decode("utf-8"))
        if not isinstance(payload, dict):
            raise RuntimeError("השרת החזיר תשובה לא תקינה")
        return payload

    @staticmethod
    def _download(
        url: str,
        target: Path,
        cancel: threading.Event,
        progress: Callable[[str, int, int], None] | None,
        label: str,
    ) -> Path:
        target.parent.mkdir(parents=True, exist_ok=True)
        temporary = target.with_suffix(target.suffix + ".part")
        existing = temporary.stat().st_size if temporary.exists() else 0
        headers = {"User-Agent": AI_USER_AGENT}
        if existing:
            headers["Range"] = f"bytes={existing}-"
        request = urllib.request.Request(url, headers=headers)
        try:
            response = urllib.request.urlopen(request, timeout=60)
        except urllib.error.HTTPError as error:
            if existing and error.code == 416:
                temporary.replace(target)
                return target
            if existing and error.code in {400, 404}:
                temporary.unlink(missing_ok=True)
                existing = 0
                request = urllib.request.Request(url, headers={"User-Agent": AI_USER_AGENT})
                response = urllib.request.urlopen(request, timeout=60)
            else:
                raise
        with response:
            if existing and getattr(response, "status", 200) != 206:
                temporary.unlink(missing_ok=True)
                existing = 0
            remaining = int(response.headers.get("Content-Length", "0") or 0)
            total = existing + remaining if remaining else 0
            mode = "ab" if existing else "wb"
            completed = existing
            with temporary.open(mode) as output:
                while True:
                    if cancel.is_set():
                        raise OfflineAiCancelled("ההורדה נעצרה")
                    block = response.read(1024 * 1024)
                    if not block:
                        break
                    output.write(block)
                    completed += len(block)
                    if progress:
                        progress(label, completed, total)
        if cancel.is_set():
            raise OfflineAiCancelled("ההורדה נעצרה")
        temporary.replace(target)
        return target

    def install_runtime(
        self,
        cancel: threading.Event,
        progress: Callable[[str, int, int], None] | None = None,
    ) -> Path:
        if self.runtime_ready():
            return self.server_executable
        release = self._request_json(LLAMA_RELEASE_API)
        assets = release.get("assets") if isinstance(release.get("assets"), list) else []
        if not any("bin-win-cpu-x64.zip" in str(item.get("name", "")) for item in assets):
            nightly_match = re.search(r"releases/tag/(b\d+)", str(release.get("body", "")))
            if not nightly_match:
                raise RuntimeError("לא נמצאה גרסת Windows של מנוע ה-AI")
            release = self._request_json(
                "https://api.github.com/repos/ggml-org/llama.cpp/releases/tags/"
                + nightly_match.group(1)
            )
            assets = release.get("assets") if isinstance(release.get("assets"), list) else []
        asset = next(
            (
                item for item in assets
                if str(item.get("name", "")).endswith("bin-win-cpu-x64.zip")
            ),
            None,
        )
        if not isinstance(asset, dict) or not str(asset.get("browser_download_url", "")):
            raise RuntimeError("לא נמצאה חבילת llama.cpp המתאימה ל-Windows")
        archive = self.downloads_dir / str(asset.get("name", "llama-win-cpu.zip"))
        self._download(
            str(asset["browser_download_url"]), archive, cancel, progress, "מנוע AI",
        )
        staging = Path(tempfile.mkdtemp(prefix="duk-ai-runtime-", dir=str(self.root)))
        try:
            with zipfile.ZipFile(archive) as zipped:
                zipped.extractall(staging)
            servers = list(staging.rglob("llama-server.exe"))
            if not servers:
                raise RuntimeError("קובץ llama-server.exe לא נמצא בחבילה")
            self.stop()
            if self.runtime_dir.exists():
                shutil.rmtree(self.runtime_dir)
            self.runtime_dir.mkdir(parents=True, exist_ok=True)
            shutil.copytree(servers[0].parent, self.runtime_dir, dirs_exist_ok=True)
            (self.runtime_dir / "runtime.json").write_text(
                json.dumps({"asset": asset.get("name"), "installed": time.time()}, indent=2),
                encoding="utf-8",
            )
        finally:
            shutil.rmtree(staging, ignore_errors=True)
            archive.unlink(missing_ok=True)
        if not self.runtime_ready():
            raise RuntimeError("התקנת מנוע ה-AI לא הושלמה")
        return self.server_executable

    def install_artifact(
        self,
        key: str,
        cancel: threading.Event,
        progress: Callable[[str, int, int], None] | None = None,
    ) -> Path:
        spec = AI_ARTIFACTS[key]
        target = self.artifact_path(key)
        if self._valid_large_file(target, spec.approximate_bytes):
            return target
        downloaded = self._download(spec.url, target, cancel, progress, spec.label)
        if not self._valid_large_file(downloaded, spec.approximate_bytes):
            downloaded.unlink(missing_ok=True)
            raise RuntimeError(f"הקובץ של {spec.label} לא ירד במלואו")
        return downloaded

    def install_text_package(
        self, cancel: threading.Event,
        progress: Callable[[str, int, int], None] | None = None,
    ) -> None:
        self.install_runtime(cancel, progress)
        self.install_artifact("text", cancel, progress)

    def install_vision_package(
        self, cancel: threading.Event,
        progress: Callable[[str, int, int], None] | None = None,
    ) -> None:
        self.install_runtime(cancel, progress)
        self.install_artifact("vision", cancel, progress)
        self.install_artifact("vision_projector", cancel, progress)

    def delete_component(self, component: str) -> None:
        self.stop()
        targets: list[Path]
        if component == "text":
            targets = [self.artifact_path("text")]
        elif component == "vision":
            targets = [self.artifact_path("vision"), self.artifact_path("vision_projector")]
        elif component == "all":
            targets = [self.models_dir, self.runtime_dir, self.downloads_dir]
        else:
            raise ValueError(component)
        resolved_root = self.root.resolve()
        for target in targets:
            try:
                resolved = target.resolve()
            except OSError:
                resolved = target.absolute()
            if resolved_root not in resolved.parents and resolved != resolved_root:
                raise RuntimeError("סירוב למחוק נתיב מחוץ לתיקיית ה-AI")
            if target.is_dir():
                shutil.rmtree(target, ignore_errors=True)
            else:
                target.unlink(missing_ok=True)
        self.models_dir.mkdir(parents=True, exist_ok=True)
        self.runtime_dir.mkdir(parents=True, exist_ok=True)
        self.downloads_dir.mkdir(parents=True, exist_ok=True)

    @staticmethod
    def _free_port() -> int:
        with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as sock:
            sock.bind(("127.0.0.1", 0))
            return int(sock.getsockname()[1])

    def stop(self) -> None:
        with self._server_lock:
            process = self._server
            self._server = None
            self._server_kind = ""
            self._server_port = 0
            if process and process.poll() is None:
                process.terminate()
                try:
                    process.wait(timeout=8)
                except subprocess.TimeoutExpired:
                    process.kill()
            if self._server_log is not None:
                try:
                    self._server_log.close()
                except Exception:
                    pass
                self._server_log = None

    def _start_server(self, kind: str) -> int:
        with self._server_lock:
            if self._server and self._server.poll() is None and self._server_kind == kind:
                return self._server_port
            self.stop()
            if not self.runtime_ready():
                raise RuntimeError("מנוע ה-AI אינו מותקן")
            if kind == "text":
                if not self.text_ready():
                    raise RuntimeError("מודל הטקסט אינו מותקן")
                model = self.artifact_path("text")
                projector = None
            elif kind == "vision":
                if not self.vision_ready():
                    raise RuntimeError("מודל הראייה אינו מותקן")
                model = self.artifact_path("vision")
                projector = self.artifact_path("vision_projector")
            else:
                raise ValueError(kind)
            port = self._free_port()
            command = [
                str(self.server_executable), "-m", str(model),
                "--host", "127.0.0.1", "--port", str(port),
                "-c", "3072", "-t", str(max(2, min(6, os.cpu_count() or 4))),
                "--parallel", "1", "--jinja",
            ]
            if projector is not None:
                command.extend(("--mmproj", str(projector)))
            log_path = self.logs_dir / f"llama-{kind}.log"
            self._server_log = log_path.open("w", encoding="utf-8", errors="replace")
            startupinfo = None
            creationflags = 0
            if os.name == "nt":
                startupinfo = subprocess.STARTUPINFO()
                startupinfo.dwFlags |= subprocess.STARTF_USESHOWWINDOW
                creationflags = getattr(subprocess, "CREATE_NO_WINDOW", 0)
            self._server = subprocess.Popen(
                command,
                stdin=subprocess.DEVNULL,
                stdout=self._server_log,
                stderr=subprocess.STDOUT,
                startupinfo=startupinfo,
                creationflags=creationflags,
            )
            self._server_kind = kind
            self._server_port = port
        deadline = time.monotonic() + 150
        last_error = ""
        while time.monotonic() < deadline:
            if self._server is None or self._server.poll() is not None:
                try:
                    last_error = log_path.read_text(encoding="utf-8", errors="replace")[-1200:]
                except OSError:
                    pass
                self.stop()
                raise RuntimeError("מנוע ה-AI לא הצליח לעלות. " + last_error.strip())
            try:
                request = urllib.request.Request(f"http://127.0.0.1:{port}/health")
                with urllib.request.urlopen(request, timeout=2) as response:
                    if response.status == 200:
                        return port
            except (OSError, urllib.error.URLError):
                time.sleep(0.35)
        self.stop()
        raise TimeoutError("טעינת מודל ה-AI ארכה יותר מדי זמן")

    @staticmethod
    def _extract_json(text: str) -> dict:
        value = re.sub(r"<think>.*?</think>", "", str(text or ""), flags=re.S).strip()
        value = re.sub(r"^```(?:json)?\s*|\s*```$", "", value, flags=re.I | re.S).strip()
        try:
            parsed = json.loads(value)
        except json.JSONDecodeError:
            match = re.search(r"\{.*\}", value, flags=re.S)
            if not match:
                raise RuntimeError("ה-AI לא החזיר תשובת JSON תקינה")
            parsed = json.loads(match.group(0))
        if not isinstance(parsed, dict):
            raise RuntimeError("ה-AI החזיר תשובה לא תקינה")
        return parsed

    def _chat(self, kind: str, messages: list[dict], timeout: float = 180.0) -> dict:
        with self._request_lock:
            port = self._start_server(kind)
            payload = {
                "model": "local",
                "messages": messages,
                "temperature": 0.0,
                "top_p": 0.1,
                "max_tokens": 420,
                "response_format": {"type": "json_object"},
            }
            request = urllib.request.Request(
                f"http://127.0.0.1:{port}/v1/chat/completions",
                data=json.dumps(payload, ensure_ascii=False).encode("utf-8"),
                headers={"Content-Type": "application/json", "User-Agent": AI_USER_AGENT},
            )
            with urllib.request.urlopen(request, timeout=timeout) as response:
                result = json.loads(response.read().decode("utf-8"))
            try:
                content = result["choices"][0]["message"]["content"]
            except (KeyError, IndexError, TypeError) as error:
                raise RuntimeError("מנוע ה-AI החזיר תשובה חסרה") from error
            return self._extract_json(content)

    def review_text(
        self, row: dict[str, object], corpus_line: str, page_head: str,
        learned_examples: list[dict[str, object]] | None = None,
    ) -> dict:
        prompt = {
            "task": "בדיקת OCR בדוח הגהת סת״ם בעברית",
            "rules": [
                "אל תשנה טקסט תקין",
                "הדוח המצולם הוא המקור; טקסט התורה הוא רק עזר לתיקון שגיאת כתיב קרובה",
                "אל תמציא מילים שאינן נראות בנתוני ה-OCR",
                "החזר confidence בין 0 ל-1",
                "החזר JSON בלבד",
            ],
            "output": {
                "start": "מחרוזת",
                "first_word": "מחרוזת",
                "problem_word": "מחרוזת",
                "problem_type": "מחרוזת",
                "description": "מחרוזת",
                "confidence": 0.0,
                "reason": "משפט קצר",
            },
            "ocr": row,
            "torah_line_reference": corpus_line,
            "page_opening_reference": page_head,
            "corrections_learned_from_user": list(learned_examples or [])[:24],
        }
        return self._chat(
            "text",
            [
                {"role": "system", "content": "אתה בודק OCR שמרני ומדויק בעברית."},
                {"role": "user", "content": json.dumps(prompt, ensure_ascii=False)},
            ],
        )

    def analyze_correction(
        self,
        *,
        field: str,
        scope: str,
        wrong: str,
        correct: str,
        report_kind: str,
        row_context: dict[str, object],
        image_bytes: bytes | None = None,
    ) -> dict:
        instructions = {
            "task": "למד מתיקון OCR שהמשתמש אישר",
            "field": field,
            "scope": scope,
            "ocr_wrong": wrong,
            "user_correct": correct,
            "report_kind": report_kind,
            "row_context": row_context,
            "rules": [
                "הטקסט שהמשתמש הזין הוא התשובה הנכונה",
                "הסבר בקצרה איזו טעות חזותית או לשונית עשה ה-OCR",
                "קבע אם בטוח להחיל את התיקון רק על התאמה זהה או גם על זיהוי דומה",
                "אל תציע החלפה כללית שעלולה לשנות מילה תקינה",
                "החזר JSON בלבד",
            ],
            "output": {
                "error_type": "בלבול אותיות/חיבור/פיצול/חסר/יתר/אחר",
                "reason": "הסבר קצר בעברית",
                "apply_mode": "exact או similar",
                "minimum_similarity": 0.9,
                "confidence": 0.0,
            },
        }
        if image_bytes and self.vision_ready():
            encoded = base64.b64encode(image_bytes).decode("ascii")
            return self._chat(
                "vision",
                [
                    {
                        "role": "system",
                        "content": "אתה מנתח טעות OCR עברית מתיקון משתמש מאושר.",
                    },
                    {
                        "role": "user",
                        "content": [
                            {
                                "type": "text",
                                "text": json.dumps(instructions, ensure_ascii=False),
                            },
                            {
                                "type": "image_url",
                                "image_url": {"url": "data:image/jpeg;base64," + encoded},
                            },
                        ],
                    },
                ],
                timeout=240.0,
            )
        return self._chat(
            "text",
            [
                {
                    "role": "system",
                    "content": "אתה מנתח טעות OCR עברית מתיקון משתמש מאושר.",
                },
                {"role": "user", "content": json.dumps(instructions, ensure_ascii=False)},
            ],
        )

    def review_image(self, image_bytes: bytes, row: dict[str, object]) -> dict:
        encoded = base64.b64encode(image_bytes).decode("ascii")
        instructions = {
            "task": "קרא את שורת דוח הסת״ם שבתמונה ובדוק את זיהוי ה-OCR",
            "rules": [
                "קרא רק טקסט שנראה בתמונה",
                "בתא צריך להיות: החזר את תחילת השורה ואת המילה שבה אות מסומנת או מודגשת",
                "בדוחות EyeTech אות עם קו תחתון מסמנת את המילה הבעייתית",
                "החזר JSON בלבד ו-confidence בין 0 ל-1",
            ],
            "current_ocr": row,
            "output": {
                "start": "מחרוזת",
                "first_word": "מחרוזת",
                "problem_word": "מחרוזת",
                "problem_type": "מחרוזת",
                "description": "מחרוזת",
                "confidence": 0.0,
                "reason": "משפט קצר",
            },
        }
        return self._chat(
            "vision",
            [
                {"role": "system", "content": "אתה מפענח תמונות OCR עבריות באופן שמרני."},
                {
                    "role": "user",
                    "content": [
                        {"type": "text", "text": json.dumps(instructions, ensure_ascii=False)},
                        {
                            "type": "image_url",
                            "image_url": {"url": "data:image/jpeg;base64," + encoded},
                        },
                    ],
                },
            ],
            timeout=240.0,
        )
