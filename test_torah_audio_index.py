import unittest

from torah_audio_index import (
    audio_id,
    build_audio_index,
    normalize_recording_word,
    plain_hebrew,
    tokenize_hebrew,
)


class TorahAudioIndexTests(unittest.TestCase):
    def test_removes_cantillation_but_keeps_niqqud(self):
        self.assertEqual(
            normalize_recording_word("בְּרֵאשִׁ֖ית"),
            "בְּרֵאשִׁית",
        )
        self.assertEqual(plain_hebrew("בְּרֵאשִׁית"), "בראשית")

    def test_maqaf_and_punctuation_split_words(self):
        self.assertEqual(
            tokenize_hebrew("בְּרֵאשִׁ֖ית בָּרָ֣א־אֱלֹהִ֑ים׃"),
            ["בְּרֵאשִׁית", "בָּרָא", "אֱלֹהִים"],
        )

    def test_index_deduplicates_vocalized_forms(self):
        corpus = {
            "schemaVersion": 1,
            "pages": {
                "1": {
                    "1": "בְּרֵאשִׁית בָּרָא אֱלֹהִים",
                    "2": "בָּרָא אֵת",
                }
            },
        }
        result = build_audio_index(corpus)
        self.assertEqual(result["totalTokens"], 5)
        self.assertEqual(result["uniqueVocalizedWords"], 4)
        record = next(item for item in result["words"] if item["word"] == "בָּרָא")
        self.assertEqual(record["count"], 2)
        self.assertEqual(record["first"], {"page": 1, "line": 1})
        self.assertEqual(record["audio"], f"words/{audio_id('בָּרָא')}.wav")

    def test_related_words_with_different_letters_are_not_grouped(self):
        corpus = {
            "schemaVersion": 1,
            "pages": {"1": {"1": "מֶלֶךְ מָלַךְ"}},
        }
        result = build_audio_index(corpus)
        self.assertIn("מלך", result["plainForms"])
        self.assertIn("מלכ", result["plainForms"])
        self.assertEqual(len(result["plainForms"]["מלך"]), 1)
        self.assertEqual(len(result["plainForms"]["מלכ"]), 1)

    def test_same_plain_letters_keep_separate_vocalized_forms(self):
        corpus = {
            "schemaVersion": 1,
            "pages": {"1": {"1": "שָׁב שֵׁב"}},
        }
        result = build_audio_index(corpus)
        self.assertEqual(result["uniquePlainWords"], 1)
        self.assertEqual(len(result["plainForms"]["שב"]), 2)
        self.assertEqual(result["ambiguousPlainWords"], 1)

    def test_empty_corpus_is_rejected(self):
        with self.assertRaises(ValueError):
            build_audio_index({"schemaVersion": 1, "pages": {}})


if __name__ == "__main__":
    unittest.main()
