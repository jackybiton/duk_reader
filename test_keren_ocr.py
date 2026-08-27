import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

import duk_reader


class KerenOcrModelTests(unittest.TestCase):
    def test_eyetech_start_uses_keren_model_when_bundled(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "tessdata").mkdir()
            (root / "tessdata" / "heb_keren.traineddata").touch()
            with patch.object(duk_reader, "resource_path", side_effect=lambda name: root / name):
                self.assertEqual(
                    duk_reader.report_column_ocr_model("eyetech", "start"),
                    ("heb_keren", root / "tessdata"),
                )

    def test_other_columns_and_reports_keep_standard_hebrew(self):
        self.assertEqual(duk_reader.report_column_ocr_model("eyetech", "need"), ("heb", None))
        self.assertEqual(duk_reader.report_column_ocr_model("classic", "start"), ("heb", None))


if __name__ == "__main__":
    unittest.main()
