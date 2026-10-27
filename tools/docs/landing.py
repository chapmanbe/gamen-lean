#!/usr/bin/env python3
"""The documentation site's landing page, generated from README.md.

One source: the README is the landing page, so the two cannot drift apart.
Relative links to repository files point at GitHub (the site does not serve
them); local images are copied next to the page.

Usage:  python3 tools/docs/landing.py README.md _site
Needs:  tools/docs/requirements.txt
"""
import re
import shutil
import sys
from pathlib import Path

import markdown

sys.path.insert(0, str(Path(__file__).resolve().parent))
from page import page  # noqa: E402

HERE = Path(__file__).resolve().parent
REPO_BLOB = "https://github.com/chapmanbe/gamen-lean/blob/main/"

_HREF = re.compile(r'href="([^"]*)"')
_SRC = re.compile(r'src="([^"]*)"')


def _is_relative(url: str) -> bool:
    return not (url.startswith("#") or re.match(r"^[a-zA-Z][a-zA-Z0-9+.-]*:", url)
                or url.startswith("/"))


def render_readme(readme: Path, out_dir: Path) -> None:
    source = readme.read_text(encoding="utf-8")
    body = markdown.markdown(source, extensions=["tables", "fenced_code"])

    def rewrite_href(m: "re.Match[str]") -> str:
        url = m.group(1)
        return f'href="{REPO_BLOB + url if _is_relative(url) else url}"'

    body = _HREF.sub(rewrite_href, body)

    out_dir.mkdir(parents=True, exist_ok=True)
    for url in _SRC.findall(body):
        if _is_relative(url):
            src = readme.parent / url
            if not src.is_file():
                raise FileNotFoundError(f"README image not found: {url}")
            dest = out_dir / url
            dest.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(src, dest)

    title_match = re.search(r"^# (.+)$", source, re.MULTILINE)
    title = title_match.group(1).strip() if title_match else "gamen-lean"
    (out_dir / "index.html").write_text(page(title, body, 0), encoding="utf-8")
    shutil.copyfile(HERE / "site.css", out_dir / "site.css")


if __name__ == "__main__":
    if len(sys.argv) != 3:
        sys.exit("usage: landing.py README.md OUT_DIR")
    render_readme(Path(sys.argv[1]), Path(sys.argv[2]))
