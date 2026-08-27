import json
import os
import tempfile
import unittest
from pathlib import Path
from unittest import mock

from duk_reader import ReportRow, apply_learned_rules_to_rows, load_learned_rules


class LearnedOcrRulesTest(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.environment = mock.patch.dict(os.environ, {"LOCALAPPDATA": self.temporary.name})
        self.environment.start()
        self.data = Path(self.temporary.name) / "DukReportReader"
        self.data.mkdir(parents=True, exist_ok=True)

    def tearDown(self) -> None:
        self.environment.stop()
        self.temporary.cleanup()

    def _write(self, filename: str, rules: list[dict]) -> None:
        (self.data / filename).write_text(
            json.dumps({"version": 2, "rules": rules}, ensure_ascii=False),
            encoding="utf-8",
        )

    def test_local_rule_overrides_same_server_rule(self) -> None:
        self._write("server-learned-corrections.json", [{
            "scope": "word", "wrong": "פל", "correct": "פו",
            "report_kind": "classic", "source": "server-approved",
        }])
        self._write("learned-corrections.json", [{
            "scope": "word", "wrong": "פל", "correct": "פי",
            "report_kind": "classic", "source": "user-approved",
        }])
        rules = load_learned_rules()
        matching = [item for item in rules if item["wrong"] == "פל"]
        self.assertEqual(len(matching), 1)
        self.assertEqual(matching[0]["correct"], "פי")

    def test_exact_rule_is_reused_only_for_the_matching_report_kind(self) -> None:
        rule = {
            "scope": "word", "wrong": "פל", "correct": "פי",
            "report_kind": "classic", "source": "user-approved",
        }
        classic = ReportRow(ocr_problem_word="פל", report_kind="classic")
        eyetech = ReportRow(ocr_problem_word="פל", report_kind="eyetech")
        apply_learned_rules_to_rows([classic, eyetech], [rule])
        self.assertEqual(classic.problem_word, "פי")
        self.assertEqual(eyetech.problem_word, "פל")

    def test_similar_rule_requires_ai_approval_and_high_unique_match(self) -> None:
        rules = [{
            "scope": "word",
            "wrong": "אבגדהוזחטיכ",
            "correct": "אבגדהוזחטיך",
            "report_kind": "classic",
            "source": "user-approved",
            "ai_apply_mode": "similar",
            "ai_confidence": 0.96,
            "minimum_similarity": 0.90,
        }]
        row = ReportRow(ocr_problem_word="אבגדהוזחטיק", report_kind="classic")
        apply_learned_rules_to_rows([row], rules)
        self.assertEqual(row.problem_word, "אבגדהוזחטיך")


if __name__ == "__main__":
    unittest.main()
