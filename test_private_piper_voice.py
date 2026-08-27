import unittest
from pathlib import Path

import duk_reader


class PrivatePiperVoiceTests(unittest.TestCase):
    def test_private_voice_is_available_and_mapped(self):
        self.assertFalse(duk_reader.CUSTOMER_EDITION)
        self.assertIn(duk_reader.PRIVATE_PIPER_VOICE_CHOICE, duk_reader.VOICE_CHOICES)
        self.assertEqual(
            duk_reader.ReportReaderApp._voice_id_for_choice(
                duk_reader.PRIVATE_PIPER_VOICE_CHOICE,
            ),
            "local-saspeech",
        )

    def test_private_voice_assets_exist(self):
        model_name, config_name = duk_reader.LOCAL_VOICE_MODELS["local-saspeech"]
        root = Path(duk_reader.__file__).resolve().parent
        self.assertTrue((root / model_name).is_file())
        self.assertTrue((root / config_name).is_file())


if __name__ == "__main__":
    unittest.main()
