#!/usr/bin/env python3
"""Render the teaching notebooks as read-only web pages.

For each notebook: run `lake env lean --json` on it to collect every
`#eval`/`#check` output, then evaluate its `#html` cells through a generated
Lean file (see `notebook.generated_file`) to get static HTML. Outputs come
from Lean in this run, never from a stored copy.

A `#html` cell that cannot be evaluated outside the notebook (for example,
one that uses a `private` definition) becomes a named placeholder and is
listed as `placeholder: FILE:LINE: HEAD`. Any other Lean error, or a cell
left without output, fails the run (exit 1).

Usage:  lake build && python3 tools/docs/render.py --out _site/notebooks Notebooks/*.lean
Needs:  tools/docs/requirements.txt
"""
from __future__ import annotations

import argparse
import json
import re
import shutil
import subprocess
import sys
import tempfile
from html import escape
from pathlib import Path
from typing import Dict, List, Optional, Tuple

sys.path.insert(0, str(Path(__file__).resolve().parent))
from notebook import (  # noqa: E402
    MissingOutput, generated_file, html_head, nested_widget, parse_expected,
    place_messages, render_page, split_blocks, split_commands,
    unexpected_placeholders)
from page import page  # noqa: E402

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent  # the gamen-lean repository


class RenderError(Exception):
    pass


def lean_messages(path: Path) -> List[dict]:
    """Messages from `lake env lean --json PATH`, run at the repository root."""
    proc = subprocess.run(["lake", "env", "lean", "--json", str(path)], cwd=ROOT,
                          capture_output=True, text=True)
    messages = []
    for line in proc.stdout.splitlines():
        line = line.strip()
        if line.startswith("{"):
            messages.append(json.loads(line))
    if proc.returncode != 0 and not any(m.get("severity") == "error" for m in messages):
        raise RenderError(f"lean failed on {path} (exit {proc.returncode}): "
                          f"{(proc.stderr or proc.stdout).strip()[:500]}")
    return messages


def _text(m: dict) -> str:
    return m.get("data", "").rstrip("\n")


def render_notebook(path: Path, placeholders: List[str]) -> Tuple[str, str]:
    """(page HTML, title) for one notebook."""
    source = path.read_text(encoding="utf-8")
    rel = path.resolve().relative_to(ROOT)
    commands = [c for b in split_blocks(source) if b.kind == "code" for c in split_commands(b)]

    notebook_msgs = lean_messages(rel)
    errors = [m for m in notebook_msgs if m.get("severity") == "error"]
    if errors:
        raise RenderError("\n".join(f"{rel}:{m['pos']['line']}: {_text(m)}" for m in errors))
    outputs = place_messages(
        commands, [(m["pos"]["line"], _text(m)) for m in notebook_msgs
                   if m.get("severity") == "information"])

    cells = [c for c in commands if c.kind == "html"]
    widgets: Dict[int, Optional[str]] = {}
    if cells:
        module = "Notebooks." + path.stem
        text, line_map = generated_file(module, source, cells)
        with tempfile.TemporaryDirectory() as tmp:
            gen = Path(tmp) / f"Static{path.stem}.lean"
            gen.write_text(text, encoding="utf-8")
            gen_msgs = lean_messages(gen)
        failed = set()
        for m in gen_msgs:
            cell = line_map.get(m["pos"]["line"])
            if m.get("severity") == "error":
                if cell is None:
                    raise RenderError(f"generated file for {rel}: line {m['pos']['line']}: {_text(m)}")
                failed.add(cell)
            elif m.get("severity") == "information" and cell is not None:
                widgets[cell] = widgets.get(cell, "") + _text(m)
        for c in cells:
            nested = nested_widget(widgets.get(c.start) or "")
            if c.start in failed or c.start not in widgets or nested is not None:
                widgets[c.start] = None
                placeholders.append(f"{rel}:{c.start}: {html_head(c)}")

    html = render_page(path.stem, source, outputs, widgets)
    m = re.search(r"<title>(.*?) · gamen-lean</title>", html)
    return html, (m.group(1) if m else path.stem)


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--out", required=True, type=Path)
    ap.add_argument("notebooks", nargs="+", type=Path)
    args = ap.parse_args()

    args.out.mkdir(parents=True, exist_ok=True)
    css = args.out.parent / "site.css"
    if not css.exists():
        shutil.copyfile(HERE / "site.css", css)

    placeholders: List[str] = []
    failures: List[str] = []
    index: List[Tuple[str, str]] = []
    for nb in sorted(args.notebooks):
        print(f"→ {nb}", flush=True)
        try:
            html, title = render_notebook(nb, placeholders)
        except (RenderError, MissingOutput, ValueError) as e:
            failures.append(str(e))
            continue
        (args.out / f"{nb.stem}.html").write_text(html, encoding="utf-8")
        index.append((nb.stem, title))

    items = "\n".join(f'<li><a href="{escape(stem)}.html">{escape(title)}</a> '
                      f'<span class="notebook-source">(<code>Notebooks/{escape(stem)}.lean</code>)</span></li>'
                      for stem, title in index)
    body = ("<h1>Notebooks</h1>\n<p>Read-only copies of the teaching notebooks, with every "
            "result computed by Lean when this site was built. Interactive widgets appear "
            "as their starting picture; to use them, open the notebook in VS Code with "
            "the Lean 4 extension (see the <a href=\"../index.html#notebooks\">README</a>).</p>\n"
            f"<ul>\n{items}\n</ul>")
    (args.out / "index.html").write_text(page("Notebooks · gamen-lean", body, 1), encoding="utf-8")

    # A placeholder is a picture missing from the site: allowed only when
    # listed in expected-placeholders.txt, so a renamed rewrite target or a
    # nested widget fails the build instead of going quietly blank.
    expected = parse_expected((HERE / "expected-placeholders.txt").read_text(encoding="utf-8"))
    for p in placeholders:
        print(f"placeholder: {p}")
    for p in unexpected_placeholders(placeholders, expected):
        failures.append(f"{p}: widget not rendered and not listed in "
                        "tools/docs/expected-placeholders.txt")
    for f in failures:
        print(f"::error::{f}")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
