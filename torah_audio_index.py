from __future__ import annotations

import argparse
import hashlib
import json
import unicodedata
from collections import Counter, defaultdict
from pathlib import Path


HERE = Path(__file__).resolve().parent
DEFAULT_CORPUS = HERE / "torah_nikud.json"
DEFAULT_INDEX = HERE / "torah_audio_index.json"

# Hebrew cantillation marks (te'amim). Keep vowel points and shin/sin dots,
# because they affect pronunciation. Meteg is removed because it is not needed
# for the recording lookup key and varies between editions.
CANTILLATION_RANGES = ((0x0591, 0x05AF),)
REMOVE_CODEPOINTS = {0x05BD, 0x05BE, 0x05C0, 0x05C3, 0x05C6}


def _is_cantillation(char: str) -> bool:
    value = ord(char)
    return any(start <= value <= end for start, end in CANTILLATION_RANGES)


def normalize_recording_word(value: str) -> str:
    """Return a stable vocalized Hebrew word suitable for an audio lookup key."""
    value = unicodedata.normalize("NFD", value)
    cleaned: list[str] = []
    for char in value:
        codepoint = ord(char)
        if _is_cantillation(char) or codepoint in REMOVE_CODEPOINTS:
            continue
        category = unicodedata.category(char)
        if "\u05d0" <= char <= "\u05ea" or category == "Mn":
            cleaned.append(char)
    return unicodedata.normalize("NFC", "".join(cleaned)).strip()


def plain_hebrew(value: str) -> str:
    """Return only Hebrew letters, without niqqud/cantillation."""
    decomposed = unicodedata.normalize("NFD", value)
    return "".join(char for char in decomposed if "\u05d0" <= char <= "\u05ea")


def tokenize_hebrew(text: str) -> list[str]:
    """Split a vocalized Torah line into Hebrew word forms.

    Maqaf and punctuation are treated as separators, while Hebrew combining
    marks remain attached to their letter sequence.
    """
    words: list[str] = []
    current: list[str] = []

    def flush() -> None:
        if not current:
            return
        normalized = normalize_recording_word("".join(current))
        current.clear()
        if normalized and plain_hebrew(normalized):
            words.append(normalized)

    for char in unicodedata.normalize("NFD", text):
        if "\u05d0" <= char <= "\u05ea" or unicodedata.category(char) == "Mn":
            current.append(char)
        else:
            flush()
    flush()
    return words


def audio_id(word: str) -> str:
    normalized = normalize_recording_word(word)
    return hashlib.sha256(normalized.encode("utf-8")).hexdigest()[:16]


def build_audio_index(corpus: dict) -> dict:
    pages = corpus.get("pages") if isinstance(corpus, dict) else None
    if not isinstance(pages, dict) or not pages:
        raise ValueError("torah_nikud.json does not contain a non-empty 'pages' object")

    counts: Counter[str] = Counter()
    first_location: dict[str, dict[str, int]] = {}
    plain_forms: dict[str, set[str]] = defaultdict(set)
    total_tokens = 0

    def numeric_key(value: str) -> tuple[int, str]:
        try:
            return int(value), value
        except (TypeError, ValueError):
            return 10**9, str(value)

    for page_key in sorted(pages, key=numeric_key):
        lines = pages[page_key]
        if not isinstance(lines, dict):
            continue
        for line_key in sorted(lines, key=numeric_key):
            text = lines[line_key]
            if not isinstance(text, str):
                continue
            for word in tokenize_hebrew(text):
                total_tokens += 1
                counts[word] += 1
                plain = plain_hebrew(word)
                plain_forms[plain].add(word)
                first_location.setdefault(
                    word,
                    {"page": int(page_key), "line": int(line_key)},
                )

    records = []
    for word in sorted(counts, key=lambda item: (plain_hebrew(item), item)):
        identifier = audio_id(word)
        records.append(
            {
                "id": identifier,
                "word": word,
                "plain": plain_hebrew(word),
                "audio": f"words/{identifier}.wav",
                "count": counts[word],
                "first": first_location[word],
            }
        )

    ambiguous_plain = {
        plain: sorted(forms)
        for plain, forms in plain_forms.items()
        if len(forms) > 1
    }

    return {
        "schemaVersion": 1,
        "sourceSchemaVersion": corpus.get("schemaVersion"),
        "totalTokens": total_tokens,
        "uniqueVocalizedWords": len(records),
        "uniquePlainWords": len(plain_forms),
        "ambiguousPlainWords": len(ambiguous_plain),
        "words": records,
        "plainForms": {
            plain: [audio_id(form) for form in sorted(forms)]
            for plain, forms in sorted(plain_forms.items())
        },
    }


def write_audio_index(corpus_path: Path, target_path: Path) -> dict:
    corpus = json.loads(corpus_path.read_text(encoding="utf-8"))
    index = build_audio_index(corpus)
    target_path.write_text(
        json.dumps(index, ensure_ascii=False, separators=(",", ":")),
        encoding="utf-8",
    )
    return index


def main() -> None:
    parser = argparse.ArgumentParser(description="Build the Torah word/audio index")
    parser.add_argument("--corpus", type=Path, default=DEFAULT_CORPUS)
    parser.add_argument("--output", type=Path, default=DEFAULT_INDEX)
    args = parser.parse_args()

    index = write_audio_index(args.corpus, args.output)
    print(
        f"Wrote {args.output}: {index['totalTokens']:,} tokens, "
        f"{index['uniqueVocalizedWords']:,} vocalized forms, "
        f"{index['uniquePlainWords']:,} plain words"
    )


if __name__ == "__main__":
    main()
