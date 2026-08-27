"""Build representative, unvocalized Hebrew OCR training lines for Guttman Keren."""

from __future__ import annotations

import json
import re
import sys
import unicodedata
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
TORAH = ROOT / "torah_nikud.json"


def plain_hebrew(text: str) -> str:
    text = unicodedata.normalize("NFD", text)
    text = "".join(char for char in text if unicodedata.category(char) != "Mn")
    text = text.replace("־", " ").replace("׃", "").replace("♢", "")
    text = re.sub(r"\[[^]]*]", "", text)
    text = re.sub(r"\s+", " ", text).strip()
    return text


def main() -> None:
    if len(sys.argv) != 2:
        raise SystemExit("usage: build_keren_training_text.py OUTPUT")
    output = Path(sys.argv[1])
    payload = json.loads(TORAH.read_text(encoding="utf-8"))
    verses: list[str] = []
    for page in payload["pages"].values():
        for line in page.values():
            cleaned = plain_hebrew(line)
            if cleaned:
                verses.append(cleaned)

    lines = [
        "עמוד מס' 13, המתחיל \"ויסר המלך את טבעתו\"",
        "עמוד מס 13 המתחיל ויסר המלך את טבעתו",
        "עמוד מס' 1, המתחיל בראשית ברא אלהים",
        "עמוד מס' 78, המתחיל הבאים אחריהם",
        "עמוד מס' 242, המתחיל ויתקדש עד שאול",
        "עמוד מס' 245, המתחיל ויהי נעם",
        "חשש אותיות מחוברות אות חסרה אות שבורה בעיה בצורת האות",
        "בעיית תגים דיבוק נתק בעיה צורה לא תקינה",
    ]
    for number, verse in enumerate(verses[:650], start=1):
        words = verse.split()
        if not words:
            continue
        start = " ".join(words[: min(8, len(words))])
        lines.append(f"עמוד מס' {(number - 1) % 245 + 1}, המתחיל {start}")
        lines.append(verse[:100])

    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text("\n".join(lines) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
