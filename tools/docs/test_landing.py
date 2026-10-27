"""Tests for tools/docs/landing.py (the site's landing page from README.md).

Run: python3 -m unittest discover -s tools/docs -v
"""
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from landing import render_readme  # noqa: E402

FIXTURE = """# gamen-lean

Intro text with [porting notes](PORTING.md), [an outside link](https://example.org)
and [a section link](#build).

![A picture](docs/images/pic.gif)

## Build

    lake build
"""


class LandingTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        root = Path(self.tmp.name)
        self.repo = root / "repo"
        (self.repo / "docs" / "images").mkdir(parents=True)
        (self.repo / "docs" / "images" / "pic.gif").write_bytes(b"GIF89a")
        (self.repo / "README.md").write_text(FIXTURE, encoding="utf-8")
        self.out = root / "site"
        render_readme(self.repo / "README.md", self.out)
        self.html = (self.out / "index.html").read_text(encoding="utf-8")

    def tearDown(self):
        self.tmp.cleanup()

    def test_index_written(self):
        self.assertIn("<h1", self.html)
        self.assertIn("gamen-lean</h1>", self.html)
        self.assertIn('href="site.css"', self.html)
        self.assertTrue((self.out / "site.css").is_file())

    def test_relative_links_rewritten(self):
        self.assertIn(
            'href="https://github.com/chapmanbe/gamen-lean/blob/main/PORTING.md"',
            self.html)
        self.assertIn('href="https://example.org"', self.html)
        self.assertIn('href="#build"', self.html)

    def test_images_copied(self):
        self.assertIn('src="docs/images/pic.gif"', self.html)
        self.assertTrue((self.out / "docs" / "images" / "pic.gif").is_file())

    def test_site_links_in_header(self):
        self.assertIn('href="api/index.html"', self.html)
        self.assertIn('href="notebooks/index.html"', self.html)


if __name__ == "__main__":
    unittest.main()
