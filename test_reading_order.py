import unittest

from duk_reader import OcrWord, join_rtl, join_rtl_visual_lines


class MultilineStartReadingOrderTest(unittest.TestCase):
    def test_reads_each_visual_line_before_moving_down(self) -> None:
        words = [
            OcrWord("ויהי", 90, 10, 34, 18, 95),
            OcrWord("בימי", 35, 10, 34, 18, 95),
            OcrWord("אחשורוש", 62, 38, 70, 18, 95),
        ]

        self.assertEqual(join_rtl(words), "ויהי אחשורוש בימי")
        self.assertEqual(join_rtl_visual_lines(words), "ויהי בימי אחשורוש")

    def test_preserves_rtl_order_inside_both_lines(self) -> None:
        words = [
            OcrWord("בהבל", 92, 8, 38, 18, 94),
            OcrWord("בוץ", 38, 8, 30, 18, 94),
            OcrWord("וארגמן", 58, 36, 66, 18, 94),
        ]

        self.assertEqual(join_rtl_visual_lines(words), "בהבל בוץ וארגמן")


if __name__ == "__main__":
    unittest.main()
