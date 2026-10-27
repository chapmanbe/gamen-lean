"""Tests for tools/docs/notebook.py (notebook parsing and page assembly).

Pure functions only; the Lean runs are exercised by render.py on the real
notebooks (plan Task 5, Step 6).

Run: python3 -m unittest discover -s tools/docs -v
"""
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from notebook import (  # noqa: E402
    MissingOutput, generated_file, html_head, nested_widget, parse_expected,
    place_messages, render_page, split_blocks, split_commands,
    unexpected_placeholders)

SOURCE = """import Gamen.Teaching

/-!
# A notebook

Some prose.
-/

open Gamen

def x : Nat := 1

/-!
## More prose
-/
"""

HINTS = """#html hints [
  ("1. Reveal", "a"),
  ("2. Reveal", "b"),
  ("3. Reveal", "c"),
  ("4. Reveal", "d"),
  ("5. Reveal", "e"),
  ("6. Reveal", "f") ]

def after : Nat := 2
"""

PRIMER = """import Gamen.Teaching

namespace Primer

open Gamen

def rule : Nat := 1

#html truthTableHtml classical [rule]

end Primer
"""

FOUR = """/-!
# Four cells
-/

#eval 1

#eval 2

#html hint "a" "b"

#html kripkeExplorer figure11
"""


def code_commands(source):
    return [c for b in split_blocks(source) if b.kind == "code"
            for c in split_commands(b)]


class SplitTests(unittest.TestCase):
    def test_split_blocks_prose_and_code(self):
        blocks = split_blocks(SOURCE)
        kinds = [b.kind for b in blocks if b.text.strip()]
        self.assertEqual(kinds, ["code", "prose", "code", "prose"])
        prose = [b for b in blocks if b.kind == "prose"]
        self.assertEqual((prose[0].start, prose[0].end), (3, 7))
        self.assertIn("# A notebook", prose[0].text)
        self.assertNotIn("/-!", prose[0].text)

    def test_multiline_html_cell(self):
        cmds = code_commands(HINTS)
        self.assertEqual(cmds[0].kind, "html")
        self.assertEqual(cmds[0].end - cmds[0].start, 6)
        self.assertEqual(cmds[1].kind, "other")

    def test_check_is_an_output_command(self):
        self.assertEqual(code_commands("#check x\n")[0].kind, "eval")


class GeneratedFileTests(unittest.TestCase):
    def test_generated_file_reopens_namespace(self):
        cells = [c for c in code_commands(PRIMER) if c.kind == "html"]
        text, line_map = generated_file("Notebooks.PropLogicPrimer", PRIMER, cells)
        order = [text.index(s) for s in
                 ["import Notebooks.PropLogicPrimer", "import Widgets.StaticHtml",
                  "namespace Primer", "open Gamen", "#eval", "end Primer"]]
        self.assertEqual(order, sorted(order))
        eval_line = text.splitlines().index(
            next(l for l in text.splitlines() if l.startswith("#eval"))) + 1
        self.assertEqual(line_map[eval_line], cells[0].start)

    def test_kripke_rewrite(self):
        src = "#html kripkeExplorer figure11\n"
        cells = code_commands(src)
        text, _ = generated_file("Notebooks.X", src, cells)
        self.assertIn("Gamen.Widgets.kripkeStatic figure11", text)
        self.assertNotIn("kripkeExplorer", text)

    def test_countermodel_rewrite(self):
        src = "#html countermodelHtml systemK [] ml[ □p ]\n"
        text, _ = generated_file("Notebooks.X", src, code_commands(src))
        self.assertIn("Gamen.Widgets.countermodelStatic systemK [] ml[ □p ]", text)


class OpenInTests(unittest.TestCase):
    SRC = "open Gamen.Widgets in\n#html kripkeExplorer figure11\n"

    def test_open_in_prefix_joins_the_cell(self):
        cmds = code_commands(self.SRC)
        self.assertEqual(len(cmds), 1)
        self.assertEqual(cmds[0].kind, "html")
        self.assertEqual(html_head(cmds[0]), "kripkeExplorer")

    def test_open_in_prefix_kept_in_generated_file(self):
        text, _ = generated_file("Notebooks.X", self.SRC, code_commands(self.SRC))
        lines = text.splitlines()
        i = lines.index("open Gamen.Widgets in")
        self.assertTrue(lines[i + 1].startswith("#eval"))
        self.assertIn("Gamen.Widgets.kripkeStatic figure11", text)


class PlaceholderTests(unittest.TestCase):
    def test_nested_widget_found(self):
        html = '<div><p>x</p><div class="widget-placeholder" data-export="default"></div></div>'
        self.assertEqual(nested_widget(html), "default")
        self.assertIsNone(nested_widget('<div class="kripke-static"><svg></svg></div>'))

    def test_unexpected_placeholders(self):
        found = ["Notebooks/A.lean:12: foo", "Notebooks/B.lean:3: bar"]
        self.assertEqual(unexpected_placeholders(found, {"Notebooks/A.lean:12: foo"}),
                         ["Notebooks/B.lean:3: bar"])
        self.assertEqual(unexpected_placeholders(found, set(found)), [])

    def test_expected_placeholders_file_parsing(self):
        text = "# comment\n\nNotebooks/A.lean:12: foo\n"
        self.assertEqual(parse_expected(text), {"Notebooks/A.lean:12: foo"})


class PlacementTests(unittest.TestCase):
    def test_place_messages(self):
        src = "#eval\n  1 +\n  2\n\ndef y := 3\n"
        cmds = code_commands(src)
        placed = place_messages(cmds, [(3, "3")])
        self.assertEqual(placed, {1: ["3"]})


class PageTests(unittest.TestCase):
    def test_eval_output_escaped(self):
        html = render_page("X", "#eval foo\n", {1: ["a < b\n& c"]}, {})
        self.assertIn('<pre class="eval-output">a &lt; b\n&amp; c</pre>', html)

    def test_every_cell_has_output(self):
        cmds = code_commands(FOUR)
        evals = [c.start for c in cmds if c.kind == "eval"]
        htmls = [c.start for c in cmds if c.kind == "html"]
        messages = {evals[0]: ["1"], evals[1]: ["2"]}
        widgets = {htmls[0]: None, htmls[1]: '<div class="kripke-static"><svg></svg></div>'}
        html = render_page("Four", FOUR, messages, widgets)
        self.assertEqual(html.count('class="eval-output"'), 2)
        self.assertEqual(html.count('class="widget-static"'), 1)
        self.assertEqual(html.count('class="widget-placeholder"'), 1)
        self.assertIn("Widget <code>hint</code>", html)
        self.assertEqual(html.count("This diagram is interactive in the notebook"), 1)
        with self.assertRaises(MissingOutput) as ctx:
            render_page("Four", FOUR, {evals[0]: ["1"]}, widgets)
        self.assertIn(str(evals[1]), str(ctx.exception))

    def test_note_only_under_explorer_picture(self):
        src = "#html countermodelHtml systemK [] ml[ □p ]\n"
        text_only = render_page("X", src, {}, {1: "<p>Valid in K</p>"})
        self.assertNotIn("interactive in the notebook", text_only)
        picture = render_page("X", src, {}, {1: '<div class="kripke-static"><svg></svg></div>'})
        self.assertIn("interactive in the notebook", picture)

    def test_prose_rendered_as_markdown(self):
        html = render_page("X", SOURCE, {}, {})
        self.assertIn("<h1>A notebook</h1>", html)
        self.assertIn("Read-only copy of <code>Notebooks/X.lean</code>", html)


if __name__ == "__main__":
    unittest.main()
