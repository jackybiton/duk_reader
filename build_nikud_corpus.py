from __future__ import annotations

import json
import re
from pathlib import Path

from torah_audio_index import build_audio_index


HERE = Path(__file__).resolve().parent
SOURCE = HERE / "tikun-korim-pages-nikud"
TARGET = HERE / "torah_nikud.json"
AUDIO_INDEX_TARGET = HERE / "torah_audio_index.json"


def main() -> None:
    pages: dict[str, dict[str, str]] = {}
    for path in sorted(SOURCE.glob("*/*.txt")):
        match = re.fullmatch(r"עמוד-(\d{3})\.txt", path.name)
        if not match:
            continue
        page_number = str(int(match.group(1)))
        lines: dict[str, str] = {}
        for raw_line in path.read_text(encoding="utf-8").splitlines():
            line_match = re.match(r"^\s*(\d{1,2})(?:\s+(.*))?$", raw_line)
            if line_match:
                lines[str(int(line_match.group(1)))] = (line_match.group(2) or "").strip()
        if set(lines) != {str(number) for number in range(1, 43)}:
            raise RuntimeError(f"{path} does not contain exactly lines 1-42")
        pages[page_number] = lines

    if set(pages) != {str(number) for number in range(1, 246)}:
        raise RuntimeError("The corpus does not contain exactly pages 1-245")
    payload = {
        "schemaVersion": 1,
        "source": "tikunkorim.co.il",
        "pages": pages,
    }
    TARGET.write_text(
        json.dumps(payload, ensure_ascii=False, separators=(",", ":")),
        encoding="utf-8",
    )

    audio_index = build_audio_index(payload)
    AUDIO_INDEX_TARGET.write_text(
        json.dumps(audio_index, ensure_ascii=False, separators=(",", ":")),
        encoding="utf-8",
    )

    print(f"Wrote {TARGET} ({TARGET.stat().st_size:,} bytes, {len(pages)} pages)")
    print(
        f"Wrote {AUDIO_INDEX_TARGET} "
        f"({audio_index['uniqueVocalizedWords']:,} vocalized word forms, "
        f"{audio_index['uniquePlainWords']:,} plain forms, "
        f"{audio_index['ambiguousPlainWords']:,} ambiguous plain forms, "
        f"{audio_index['totalTokens']:,} total tokens)"
    )


if __name__ == "__main__":
    main()
