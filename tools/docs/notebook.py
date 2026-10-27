"""Parse a Lean teaching notebook and assemble its read-only web page.

Pure functions; `render.py` runs Lean and calls these. A notebook is prose
in `/-! … -/` blocks and Lean code between them. Code is split into
commands: a command starts at a non-blank line in column 0 and runs to the
last non-blank line before the next one. `#eval` and `#check` commands get
their Lean output under them; `#html` commands get a static rendering of
their widget (see `Widgets/StaticHtml.lean`).
"""
from __future__ import annotations

import re
from dataclasses import dataclass
from html import escape
from typing import Dict, List, Optional, Sequence, Tuple

import markdown
from pygments import highlight
from pygments.formatters import HtmlFormatter
from pygments.lexers import get_lexer_by_name
from pygments.util import ClassNotFound

from page import page

# `#html` heads whose interactive widget has a static stand-in.
REWRITES = {"kripkeExplorer": "Gamen.Widgets.kripkeStatic",
            "countermodelHtml": "Gamen.Widgets.countermodelStatic"}

INTERACTIVE_NOTE = (
    "This diagram is interactive in the notebook: open <code>Notebooks/{file}.lean</code> "
    "in VS Code with the Lean 4 extension and put the cursor on the <code>#html</code> line.")

OUTPUT_COMMANDS = ("#eval", "#check")


class MissingOutput(Exception):
    """An `#eval`/`#check` without Lean output, or an `#html` without a rendering."""


@dataclass
class Block:
    kind: str  # "prose" or "code"
    text: str
    start: int  # 1-based, inclusive
    end: int


@dataclass
class Command:
    text: str
    start: int
    end: int
    kind: str  # "eval", "html" or "other"


def split_blocks(source: str) -> List[Block]:
    lines = source.splitlines()
    blocks: List[Block] = []
    code: List[str] = []
    code_start = 1
    i = 0
    while i < len(lines):
        if lines[i].startswith("/-!"):
            if code:
                blocks.append(Block("code", "\n".join(code), code_start, i))
            start = i
            inner = [lines[i][3:]]
            while "-/" not in lines[i]:
                i += 1
                if i == len(lines):
                    raise ValueError(f"unterminated /-! block at line {start + 1}")
                inner.append(lines[i])
            inner[-1] = inner[-1][: inner[-1].rindex("-/")]
            if start == i:  # one-line block: /-! text -/
                inner = [lines[i][3: lines[i].rindex("-/")]]
            blocks.append(Block("prose", "\n".join(inner).strip("\n"), start + 1, i + 1))
            code, code_start = [], i + 2
        else:
            code.append(lines[i])
        i += 1
    if code:
        blocks.append(Block("code", "\n".join(code), code_start, len(lines)))
    return blocks


def _kind(text: str) -> str:
    if text.startswith(OUTPUT_COMMANDS):
        return "eval"
    if text.startswith("#html"):
        return "html"
    return "other"


def split_commands(block: Block) -> List[Command]:
    lines = block.text.split("\n")
    starts = [n for n, l in enumerate(lines) if l.strip() and not l[0].isspace()]
    commands = []
    for k, s in enumerate(starts):
        stop = starts[k + 1] if k + 1 < len(starts) else len(lines)
        last = max(n for n in range(s, stop) if lines[n].strip())
        text = "\n".join(lines[s: last + 1])
        commands.append(Command(text, block.start + s, block.start + last, _kind(text)))
    return commands


def html_head(cell: Command) -> str:
    m = re.match(r"#html\s+([^\s(\[]+)", cell.text)
    return m.group(1) if m else "#html"


def _rewritten_expr(cell: Command) -> str:
    expr = cell.text[len("#html"):].strip()
    head = html_head(cell)
    if head in REWRITES:
        expr = REWRITES[head] + expr[len(head):]
    return expr


_SCOPE = re.compile(r"^(open|namespace|end|section)\b")


def generated_file(module: str, source: str,
                   cells: Sequence[Command]) -> Tuple[str, Dict[int, int]]:
    """Lean source that evaluates each `#html` cell's expression to an HTML
    string, under the same `namespace`/`open` lines it had in the notebook.
    Returns the source and a map from its lines to the cell's start line."""
    out = [f"import {module}", "import Widgets.StaticHtml", ""]
    line_map: Dict[int, int] = {}
    by_start = {c.start: c for c in cells}
    code_lines = set()
    for b in split_blocks(source):
        if b.kind == "code":
            code_lines.update(range(b.start, b.end + 1))
    for n, line in enumerate(source.splitlines(), start=1):
        if n in by_start:
            cell = by_start[n]
            first = len(out) + 1
            out.append("#eval IO.println (Gamen.Widgets.htmlToString (")
            out.extend(_rewritten_expr(cell).split("\n"))
            out.append("))")
            for g in range(first, len(out) + 1):
                line_map[g] = cell.start
        elif n in code_lines and _SCOPE.match(line) and not line.rstrip().endswith(" in"):
            out.append(line)
    return "\n".join(out) + "\n", line_map


def place_messages(commands: Sequence[Command],
                   messages: Sequence[Tuple[int, str]]) -> Dict[int, List[str]]:
    placed: Dict[int, List[str]] = {}
    for line, text in messages:
        for c in commands:
            if c.start <= line <= c.end:
                placed.setdefault(c.start, []).append(text)
                break
    return placed


def _lexer():
    try:
        return get_lexer_by_name("lean4")
    except ClassNotFound:
        return None


def _code_html(code: str) -> str:
    lexer = _lexer()
    if lexer is None:
        return f"<pre><code>{escape(code)}</code></pre>"
    return highlight(code, lexer, HtmlFormatter())


def render_page(name: str, source: str, messages: Dict[int, List[str]],
                widgets: Dict[int, Optional[str]]) -> str:
    """The page for `Notebooks/<name>.lean`. `messages` maps an output
    command's start line to its Lean output; `widgets` maps an `#html`
    cell's start line to its HTML, or None for a named placeholder."""
    parts = [f'<p class="notebook-source">Read-only copy of <code>Notebooks/{escape(name)}.lean</code>. '
             'To run it, see the <a href="../index.html#notebooks">README\'s Notebooks section</a>.</p>']
    title = name
    for block in split_blocks(source):
        if block.kind == "prose":
            m = re.search(r"^# (.+)$", block.text, re.MULTILINE)
            if m and title == name:
                title = m.group(1).strip()
            parts.append(markdown.markdown(block.text, extensions=["tables", "fenced_code"]))
            continue
        pending: List[str] = []

        def flush():
            text = "\n".join(pending).strip("\n")
            if text.strip():
                parts.append(_code_html(text))
            pending.clear()

        for cmd in split_commands(block):
            pending.append(cmd.text)
            pending.append("")
            if cmd.kind == "eval":
                if cmd.start not in messages:
                    raise MissingOutput(f"{name}: line {cmd.start}: no Lean output for "
                                        f"{cmd.text.splitlines()[0]}")
                flush()
                for text in messages[cmd.start]:
                    parts.append(f'<pre class="eval-output">{escape(text.rstrip(chr(10)), quote=False)}</pre>')
            elif cmd.kind == "html":
                if cmd.start not in widgets:
                    raise MissingOutput(f"{name}: line {cmd.start}: no rendering for "
                                        f"{cmd.text.splitlines()[0]}")
                flush()
                head = html_head(cmd)
                rendered = widgets[cmd.start]
                if rendered is None:
                    parts.append(f'<div class="widget-placeholder">Widget <code>{escape(head)}</code>: '
                                 'shown only in the notebook.</div>')
                else:
                    parts.append(f'<div class="widget-static">{rendered}</div>')
                    if 'class="kripke-static"' in rendered:
                        parts.append('<p class="widget-note">'
                                     + INTERACTIVE_NOTE.format(file=escape(name)) + "</p>")
        flush()
    return page(f"{title} · gamen-lean", "\n".join(parts), 1)
