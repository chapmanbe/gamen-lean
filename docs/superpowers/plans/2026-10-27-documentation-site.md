# Documentation Site Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Publish chapmanbe.github.io/gamen-lean: a landing page made from the README, a doc-gen4 API reference, and a read-only HTML page for every notebook, rebuilt by GitHub Actions on every push to `main`.

**Architecture:** doc-gen4 runs from a separate `docbuild/` Lake package, so the main `lakefile.toml` gains no dependency. A Python renderer (`tools/docs/`) splits each notebook into prose and commands. It runs `lake env lean --json` to get every `#eval` output, and it evaluates each `#html` cell through a generated Lean file that calls a new Lean serializer (`Html → String`). One workflow builds everything into `_site/`. It deploys on push to `main`, and it only builds on pull requests.

**Tech Stack:** Lean 4.34.0, Lake, doc-gen4 `v4.34.0`, ProofWidgets v0.0.111 (already pinned), Python 3 with `markdown` and `pygments` (pinned in `tools/docs/requirements.txt`), GitHub Actions (`actions/upload-pages-artifact@v3`, `actions/deploy-pages@v4`).

**Spec:** `docs/superpowers/specs/2026-10-22-documentation-site-design.md`

## Global Constraints

- The main `lakefile.toml` gains no `[[require]]`. You may add one `[[lean_lib]]` or `globs` entry, but only if a task says so. ProofWidgets stays at `v0.0.111`, Plausible at `v4.34.0`, and the toolchain at `leanprover/lean4:v4.34.0`.
- Pin doc-gen4 at `rev = "v4.34.0"` in `docbuild/lakefile.toml`.
- The API reference covers the `Gamen` and `Widgets` libraries only.
- Site layout: landing page at `/` (`_site/index.html`), API at `/api/`, notebooks at `/notebooks/`.
- The notebooks under `Notebooks/` are not edited.
- Every `#eval` output on a page comes from Lean in the same build, never typed in by hand.
- Hints render as closed `<details>`, so nothing reveals an answer without a click.
- A notebook whose rendering fails fails the workflow. The one exception: an `#html` cell that can't be evaluated becomes a named placeholder, listed in the build log.
- The interactive-widget note under each explorer picture has this exact text: "This diagram is interactive in the notebook: open `Notebooks/<File>.lean` in VS Code with the Lean 4 extension and put the cursor on the `#html` line."
- Python scripts are standard library plus `markdown` and `pygments` only, at the versions in `tools/docs/requirements.txt`.
- American English in all prose, comments and page text.
- Lean conventions from `CLAUDE.md`: no `sorry`, no `partial def`, `Except` instead of `panic!`. Commit messages end with `Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>`.
- Workflow: triggers on `push` to `main`, `pull_request` to `main`, and `workflow_dispatch`. Deploy steps are guarded with `if: github.event_name != 'pull_request'`. Job timeout is 60 minutes. Cache `.lake` and `docbuild/.lake`, keyed on `lake-manifest.json`, `docbuild/lake-manifest.json` and `lean-toolchain`. The workflow does not run `lake test`.

## Environment notes for implementers

- This worktree has no `.lake/`. Before the first `lake build`, symlink the main checkout's packages so they aren't downloaded again: `mkdir -p .lake && ln -s /Users/brainchapman/Projects/Logic/gamen-lean/.lake/packages .lake/packages`. `lake build` then builds gamen-lean itself, which takes several minutes.
- Use `/usr/bin/git`, one command per Bash call. The rtk hook breaks plain `git` in worktrees.
- Run `gh` only as a standalone command, with no pipes or `&&`.
- `lake` is at `~/.elan/bin/lake`.

## Review Focus

1. **A `#html` cell that spans several lines** (`#html hints [ … ]` in `Ch1SyntaxSemantics.lean`). Expect the whole expression to be evaluated and a closed `<details>` per hint, not a parse error or only the first line. Test: Task 4, `test_multiline_html_cell`.
2. **A cell whose expression uses a name from the notebook's own namespace** (`Primer`, `ThreeValued`). Expect the generated file to reopen that namespace so `rule`, `argument1` and so on resolve. Test: Task 4, `test_generated_file_reopens_namespace`.
3. **An `#eval` whose output contains `<`, `&` or a multi-line string.** Expect escaped, verbatim, line-preserving output in a `<pre>`. Test: Task 4, `test_eval_output_escaped`.
4. **Relative links and images in `README.md`.** Expect `PORTING.md`-style links to point at GitHub, and `docs/images/*.gif` to be copied and shown. Test: Task 2, `test_relative_links_rewritten` and `test_images_copied`.
5. **An SVG attribute ProofWidgets emits in React camelCase** (`strokeWidth`), or a `data` attribute. Expect `stroke-width` in the output and no `data=` attribute, so the browser draws the stroke and the page doesn't carry click payloads. Test: Task 3, case "svg attrs: strokeWidth becomes stroke-width, data is dropped".

---

### Task 1: doc-gen4 API reference

**Files:**
- Create: `docbuild/lakefile.toml`
- Create: `docbuild/lake-manifest.json` (generated by `lake update`, committed)
- Create: `tools/docs/build-api.sh`
- Modify: `.gitignore` (add `docbuild/.lake/` and `_site/`)

**Interfaces:**
- Produces: `tools/docs/build-api.sh OUT_DIR`. It builds the docs and copies doc-gen4's output directory (`docbuild/.lake/build/doc/`) to `OUT_DIR`. It exits non-zero if `OUT_DIR/index.html`, `OUT_DIR/Gamen.html` or `OUT_DIR/Widgets.html` is missing.

- [ ] **Step 1: Write `docbuild/lakefile.toml`.** Package `name = "docbuild"`, `reservoir = false`. Add `[[require]] name = "gamen", path = "../"`, and `[[require]] name = "doc-gen4", git = "https://github.com/leanprover/doc-gen4", rev = "v4.34.0"`. Its `lean-toolchain` must match, so copy `../lean-toolchain` into `docbuild/lean-toolchain`.
- [ ] **Step 2: Resolve dependencies.** Run: `cd docbuild && ~/.elan/bin/lake update doc-gen4`. Expected: `lake-manifest.json` lists doc-gen4 at the `v4.34.0` commit, and lists gamen's own dependencies at the same revisions as `../lake-manifest.json`. If the ProofWidgets or Plausible revisions differ from the main manifest, stop and report. Don't change the main manifest.
- [ ] **Step 3: Write `tools/docs/build-api.sh`.** Use `set -euo pipefail`. Run `cd docbuild && lake build Gamen:docs Widgets:docs`, copy `.lake/build/doc/` to the output directory, then run the three `test -f` checks. Each failed check prints `::error::` plus the missing file.
- [ ] **Step 4: Run it.** Run: `bash tools/docs/build-api.sh $TMPDIR/api`. Expected: exit 0, and `$TMPDIR/api/Gamen/Kripke.html` exists. Also run `grep -c "Definition 1.7" $TMPDIR/api/Gamen/Semantics.html` (or whichever module holds the truth-at-a-world docstring). Expected: ≥ 1, which shows docstrings are rendered.
- [ ] **Step 5: Plant a failure.** Temporarily change the script's check to `Missing.html`. Expected: exit 1 with `::error::`. Revert.
- [ ] **Step 6: Commit** `docbuild/lakefile.toml docbuild/lake-manifest.json docbuild/lean-toolchain tools/docs/build-api.sh .gitignore` with the message "Add a doc-gen4 build for the Gamen and Widgets API reference".

### Task 2: Landing page from the README, plus CITATION.cff

**Files:**
- Modify: `README.md` (add sections: "Statement of need", "How to cite", "Contributing"; add a "Documentation" line linking to the site)
- Create: `CITATION.cff`
- Create: `tools/docs/requirements.txt`, `tools/docs/site.css`, `tools/docs/page.py`, `tools/docs/landing.py`
- Test: `tools/docs/test_landing.py`

**Interfaces:**
- Produces in `tools/docs/page.py`: `page(title: str, body_html: str, depth: int) -> str`. It returns a full HTML document with the site header (links: Home, API reference, Notebooks, GitHub) and the stylesheet link `"../" * depth + "site.css"`. Tasks 5 and 6 use it.
- Produces in `tools/docs/landing.py`: `render_readme(readme: Path, out_dir: Path) -> None`. It writes `out_dir/index.html`, copies each referenced local image to `out_dir/<same relative path>`, and copies `site.css` to `out_dir/site.css`. CLI: `python3 tools/docs/landing.py README.md _site`.
- Constant: `REPO_BLOB = "https://github.com/chapmanbe/gamen-lean/blob/main/"`.

- [ ] **Step 1: Write `tools/docs/requirements.txt`** with `markdown==3.7` and `pygments==2.19.1`. Run: `python3 -c "import pygments.lexers as l; print(l.get_lexer_by_name('lean4'))"` after `pip install -r`. Expected: a Lean 4 lexer. If none, report it; Task 5 will then fall back to unhighlighted `<pre>`.
- [ ] **Step 2: Write the failing tests** in `tools/docs/test_landing.py` (`unittest`, using a temporary directory and a small fixture README written by the test):
  - `test_index_written`: `index.html` exists, contains `<h1>` with the README's first heading, and links `site.css`.
  - `test_relative_links_rewritten`: `[x](PORTING.md)` becomes `href="https://github.com/chapmanbe/gamen-lean/blob/main/PORTING.md"`. `[y](https://example.org)` is unchanged. `[z](#build)` is unchanged.
  - `test_images_copied`: `![a](docs/images/pic.gif)` stays `src="docs/images/pic.gif"`, and the file exists under `out_dir/docs/images/`.
  - `test_site_links_in_header`: the page contains `href="api/index.html"` and `href="notebooks/index.html"`.
- [ ] **Step 3: Run them.** Run: `python3 -m unittest tools/docs/test_landing.py -v`. Expected: FAIL (import error).
- [ ] **Step 4: Implement `page.py`, `landing.py` and `site.css`.** Use `markdown` with the `tables` and `fenced_code` extensions. Rewrite links by post-processing `href="…"` values that are relative and don't start with `#`. `site.css` is one readable, single-column stylesheet (max width about 48rem, system fonts, code in monospace, `details` styled as a box). It defines its colors as variables with a `prefers-color-scheme: dark` variant.
- [ ] **Step 5: Run the tests.** Expected: PASS.
- [ ] **Step 6: Edit `README.md`.** Add the three sections before "License" and change "Status: early port" to match `CLAUDE.md` (gamen-lean is the primary implementation; every gamen-hs library module is ported).
  - **"Statement of need":** gamen-lean is executable modal, temporal, epistemic, deontic, STIT, ATL and dynamic logics in one Lean 4 library, with teaching notebooks for health informatics students that follow *Boxes and Diamonds*, and a JSON Lines service used for clinical guideline validation. Its predecessors are gamen-hs and Gamen.jl.
  - **"How to cite":** points to `CITATION.cff`.
  - **"Contributing":** issues and pull requests on GitHub, `lake build` and `lake test` must pass, and see `CLAUDE.md` for conventions.
  - **"Documentation":** a line linking https://chapmanbe.github.io/gamen-lean.

  Keep each section to three to six sentences, using only facts already stated in `README.md`, `CLAUDE.md` or `PORTING.md`. Mark the commit message "draft for Brian's edit".
- [ ] **Step 7: Write `CITATION.cff`** (cff-version 1.2.0): title "gamen-lean", authors Brian Chapman and Jeremiah Chapman (no ORCIDs), license MIT, repository-code `https://github.com/chapmanbe/gamen-lean`, version `0.1.0` (from `lakefile.toml`), no DOI.
- [ ] **Step 8: Render the real README.** Run: `python3 tools/docs/landing.py README.md $TMPDIR/site`. Expected: exit 0, and `$TMPDIR/site/docs/images/gamen-lean-widget-click-test.gif` exists.
- [ ] **Step 9: Commit** with the message "Generate the documentation landing page from the README; add statement of need, citation and contributing sections (draft for Brian's edit)".

### Task 3: Workflow for the landing page and API reference (site goes live)

**Files:**
- Create: `.github/workflows/docs.yml`
- Create: `tools/docs/build-site.sh`

**Interfaces:**
- Consumes: `tools/docs/build-api.sh OUT_DIR` (Task 1) and `tools/docs/landing.py README OUT` (Task 2).
- Produces: `tools/docs/build-site.sh` (no arguments). It builds `_site/` from scratch: landing page, `_site/api/`, and a placeholder `_site/notebooks/index.html` saying "Notebook pages are coming." Task 6 replaces the placeholder. It exits non-zero if any part fails.

- [ ] **Step 1: Write `tools/docs/build-site.sh`.** Use `set -euo pipefail`. Run `rm -rf _site`, then `lake build`, the landing page, the API reference into `_site/api`, and the notebook placeholder. End with `test -f` on `_site/index.html`, `_site/api/index.html` and `_site/notebooks/index.html`.
- [ ] **Step 2: Run it locally.** Run: `bash tools/docs/build-site.sh`. Expected: exit 0 and the three files present. Open `_site/index.html` in a browser by hand. The sandbox blocks `open`, so ask Brian to run `! open _site/index.html` and confirm the header links work.
- [ ] **Step 3: Write `.github/workflows/docs.yml`.** Follow the shape of gamen-hs's `docs.yml`, as summarized in Global Constraints:
  - Permissions: `contents: read`, `pages: write`, `id-token: write`.
  - Concurrency group `pages`.
  - Environment `github-pages` only when not a pull request.
  - Steps: checkout, then install elan (`curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain none` and add `~/.elan/bin` to `$GITHUB_PATH`), then `actions/setup-python@v5` (3.12) and `pip install -r tools/docs/requirements.txt`, then `actions/cache@v4` for `.lake` and `docbuild/.lake`, then `bash tools/docs/build-site.sh`, then upload and deploy (guarded).
  - Add a comment block at the top explaining the pull-request guard, as gamen-hs does.
- [ ] **Step 4: Lint it.** Run: `python3 -c "import yaml,sys; yaml.safe_load(open('.github/workflows/docs.yml'))"` (if PyYAML is available; otherwise skip this step and note that). Expected: no error.
- [ ] **Step 5: Commit** with the message "Add the documentation workflow: landing page and API reference, deployed on push to main".
- [ ] **Step 6: Outward-facing (controller asks Brian first):** push the `docs-site` branch and open a pull request into `main`. The pull-request run must build green before Brian merges. Merging is what puts the site live.

### Task 4: Lean serializer for `#html` cells

**Files:**
- Create: `Widgets/StaticHtml.lean`
- Create: `Tests/StaticHtml.lean`
- Modify: `Tests/Main.lean` (import `Tests.StaticHtml`; add `StaticHtmlTests.cases` to the two lists at about lines 6137 and 6164, as `ManyValuedNotebookTests.cases` is added)

**Interfaces:**
- Produces, in namespace `Gamen.Widgets`:
  - `htmlToString : Html → String`. `.text` is HTML-escaped (`&`, `<`, `>`). `.element` writes the tag and its attributes, and children recurse. `.component _ exp _ _` becomes `<div class="widget-placeholder" data-export="EXP"></div>`, where EXP is the export name. The Python renderer replaces this with a named placeholder.
  - Attribute rules:
    - Drop `data`, `key`, and any name matching `on[A-Z].*`.
    - `className` becomes `class`.
    - A `style` JSON object becomes a CSS string (`fontSize` → `font-size: …;`).
    - Other camelCase names become kebab-case, except `viewBox` and `preserveAspectRatio`.
    - JSON strings are written as-is (attribute-escaped). Numbers are written in their JSON form. Booleans: `true` writes the bare attribute, `false` drops it.
    - A void element (`br`, `hr`, `img`, `input`, `meta`, `link`) is written without a closing tag.
  - `kripkeStatic (sc : Scenario) : Html := (initialResult sc).html`, wrapped in `<div class="kripke-static">…</div>`.
- Termination: `htmlToString` recurses through `Array Html` children. Use structural recursion via a mutual helper over `Array`/`List`, or `Array.attach` with `sizeOf`. Don't use `partial def` (CLAUDE.md).

- [ ] **Step 1: Write the failing test cases** in `Tests/StaticHtml.lean`, as `StaticHtmlTests.cases : List (String × Bool)` in the style of `Tests/ManyValuedNotebooks.lean`:
  - "text is escaped": `htmlToString (.text "a < b & c") == "a &lt; b &amp; c"`.
  - "hint is a closed details element": `htmlToString (hint "S" "A") == "<details><summary>S</summary><p>A</p></details>"`. Note `hint` comes from `Widgets/Hint.lean`.
  - "svg attrs: strokeWidth becomes stroke-width, data is dropped": the output for `.element "line" #[("strokeWidth", 2), ("data", "w1"), ("stroke", "rgb(0,0,0)")] #[]` contains `stroke-width="2"`, contains `stroke="rgb(0,0,0)"`, and doesn't contain `data=`.
  - "viewBox keeps its case": contains `viewBox="0 0 10 10"`.
  - "className becomes class, style object becomes CSS": `<div class="x" style="font-size: 12px;"></div>` from the corresponding element.
  - "component becomes a placeholder": `htmlToString (kripkeExplorer figure11-like)` contains `class="widget-placeholder"`. Build a two-world scenario in the test.
  - "kripkeStatic draws an svg": `htmlToString (kripkeStatic sc)` starts with `<div class="kripke-static">`, contains `<svg`, and contains each world name of `sc`.
- [ ] **Step 2: Run them.** Run: `lake build Tests && lake test 2>&1 | grep -E "StaticHtml|passed|failed"`. Expected: build fails (unknown identifiers).
- [ ] **Step 3: Implement `Widgets/StaticHtml.lean`.** Import `Widgets.KripkeExplorer` and `Widgets.Hint`.
- [ ] **Step 4: Run them again.** Expected: all pass, and the total count rises by the number of new cases.
- [ ] **Step 5: Plant a bug.** Make `className` stay `className`. Expected: one case fails. Revert.
- [ ] **Step 6: Commit** with the message "Add a static Html-to-string serializer for rendering notebook widgets".

### Task 5: Notebook renderer

**Files:**
- Create: `tools/docs/notebook.py` (parsing and generation; pure functions)
- Create: `tools/docs/render.py` (CLI; runs Lean and writes pages)
- Test: `tools/docs/test_notebook.py`

**Interfaces:**
- Consumes: `page()` (Task 2), `Gamen.Widgets.htmlToString` and `kripkeStatic` (Task 4).
- Produces in `notebook.py`:
  - `@dataclass Block(kind: str, text: str, start: int, end: int)`. `kind` is `"prose"` (the inside of a `/-! … -/` block) or `"code"`. Lines are 1-based and inclusive.
  - `split_blocks(source: str) -> list[Block]`.
  - `@dataclass Command(text: str, start: int, end: int, kind: str)`. `kind` is `"eval"`, `"html"` or `"other"`. A command starts at a non-blank line in column 0 and runs to the last non-blank line before the next column-0 non-blank line, or to the end of its code block.
  - `split_commands(block: Block) -> list[Command]`.
  - `REWRITES = {"kripkeExplorer": "Gamen.Widgets.kripkeStatic"}`, applied to the head identifier of an `#html` expression.
  - `generated_file(module: str, source: str, cells: list[Command]) -> tuple[str, dict[int, int]]`. It returns Lean source that imports `module` and `Widgets.StaticHtml`. Then, in source order, it carries every column-0 `open …`, `namespace X` and `end X` line from the notebook, interleaved so each cell sits under the same opens and namespace it had in the notebook. Each cell becomes `#eval IO.println (Gamen.Widgets.htmlToString (<rewritten expression>))`. The returned map goes from generated-file line to the cell's `start` line.
  - `place_messages(commands, messages) -> dict[int, list[str]]`: from command start line to output texts, matching a message to the command whose `[start, end]` contains its line.
- Produces in `render.py`: CLI `python3 tools/docs/render.py --out DIR Notebooks/*.lean`. It writes `DIR/<Stem>.html` per notebook, `DIR/index.html` (each notebook's first `# ` heading, linked), and copies `site.css` to `DIR/../site.css` if absent. It prints `placeholder: <file>:<line>: <head identifier>` for each placeholder. It exits 1 on any Lean error message in a notebook run, or in a generated-file run other than at a cell that becomes a placeholder.
- Page layout per notebook:
  - Prose goes through `markdown`.
  - Code blocks are highlighted with pygments `lean4` (plain `<pre>` if unavailable).
  - Under each `#eval`, the output goes in `<pre class="eval-output">` (escaped).
  - Under each `#html`, the serialized HTML goes in `<div class="widget-static">`.
  - Under each `kripkeExplorer` cell, the interactive-widget note.
  - Placeholders become `<div class="widget-placeholder">Widget <code>HEAD</code>: shown only in the notebook.</div>`.
  - At the top of the page: "Read-only copy of `Notebooks/<File>.lean`. To run it, see the README's Notebooks section."

- [ ] **Step 1: Write the failing tests** in `tools/docs/test_notebook.py` (`unittest`, pure functions only, with fixture strings):
  - `test_split_blocks_prose_and_code`: a source with a header, two `/-! -/` blocks and code between them gives the kinds `["code", "prose", "code", "prose"]`, with correct line ranges.
  - `test_multiline_html_cell`: the `#html hints [` cell (6 lines, closing `]` indented) is one `Command` of kind `"html"` with `end - start == 6`.
  - `test_generated_file_reopens_namespace`: for a source with `namespace Primer` / `open Gamen` / `#html truthTableHtml classical [rule]` / `end Primer`, the generated text contains `namespace Primer`, then `open Gamen`, then the `#eval` line, then `end Primer`, in that order.
  - `test_kripke_rewrite`: `#html kripkeExplorer figure11` generates `Gamen.Widgets.kripkeStatic figure11`.
  - `test_eval_output_escaped`: rendering an eval command with the message `"a < b\n& c"` produces `<pre class="eval-output">a &lt; b\n&amp; c</pre>`.
  - `test_place_messages`: a message on line `start + 2` of a three-line `#eval` lands under that command.
  - `test_every_cell_has_output` (the spec's check): for a fixture with two `#eval` and two `#html` commands and fake messages for all four, the rendered page has two `eval-output` blocks and two `widget-static`/`widget-placeholder` blocks. With one `#eval` message missing, `render_page` raises `MissingOutput` naming the line.
- [ ] **Step 2: Run them.** Run: `python3 -m unittest tools/docs/test_notebook.py -v`. Expected: FAIL (import error).
- [ ] **Step 3: Implement `notebook.py`** and the page assembly in `render.py` (`render_page(path, source, messages, widget_html) -> str`, raising `MissingOutput`).
- [ ] **Step 4: Run them.** Expected: PASS.
- [ ] **Step 5: Implement the Lean runs in `render.py`.** Run `lake env lean --json <notebook>`, where each stdout line is a JSON message with `pos.line`, `severity` and `data`. Write the generated file to a temporary directory, not inside `Notebooks/`, and run `lake env lean --json` on it. When a generated-file error lands in a cell, that cell becomes a placeholder, and the rest of the cells still render.
- [ ] **Step 6: Run on all five notebooks.** Run: `lake build && python3 tools/docs/render.py --out $TMPDIR/nb Notebooks/*.lean`. Expected: exit 0, and five pages plus the index. Then run `grep -c "eval-output" $TMPDIR/nb/Ch1SyntaxSemantics.html`. Expected: 16, one per `#eval` (the count from `grep -c "^#eval"`). Also run `grep -c "<details" $TMPDIR/nb/Ch1SyntaxSemantics.html`. Expected: ≥ 12 (two `hints` panels of six), and none has an `open` attribute. Report every `placeholder:` line.
- [ ] **Step 7: Plant a failure.** Copy a notebook to `$TMPDIR`, add `#eval (1 : Nat) + "x"`, and render it. Expected: exit 1 with the file and line.
- [ ] **Step 8: Commit** with the message "Add the notebook renderer: prose, highlighted code, real #eval output, static widgets".

### Task 6: Notebook pages in the site and the workflow

**Files:**
- Modify: `tools/docs/build-site.sh` (replace the notebook placeholder with `render.py --out _site/notebooks Notebooks/*.lean`)
- Modify: `README.md` (Notebooks section: one sentence linking the web copies)

- [ ] **Step 1: Edit `build-site.sh`.**
- [ ] **Step 2: Run** `bash tools/docs/build-site.sh`. Expected: exit 0, and `_site/notebooks/PropLogicPrimer.html` exists. Ask Brian to run `! open _site/notebooks/Ch1SyntaxSemantics.html` and check three things: the Figure 1.1 picture, the interactive note under it, and closed hints.
- [ ] **Step 3: Commit** with the message "Publish the notebooks as read-only pages". Push the branch; the pull-request run must pass.

### Task 7 (only after PR #6, the dynamic explorer, is merged into `main`): dynamic explorer pictures

The dynamic explorer draws in JavaScript, so its `#html` cells are placeholders until this task. Rebase `docs-site` on `main` first.

**Files:**
- Modify: `Widgets/StaticHtml.lean`: add `dynamicStaticJson (sc) : String`, the JSON of `view (ExplorerState.init sc)` from `Widgets/Dynamic/Explorer.lean`, the same data `Widgets/js/dynamicExplorer.js` receives.
- Modify: `tools/docs/notebook.py`: in `REWRITES`, `dynamicExplorerOr` maps to a JSON-producing call, and a cell flag tells `render.py` to draw it.
- Create: `tools/docs/dynamic_svg.py`: `draw(view_json: dict) -> str`, an SVG of the before and after models with the same node positions, labels and dashed default loops as the JS. It has no controls, just the starting picture and the first question's text.
- Test: `tools/docs/test_dynamic_svg.py` (one fixture view: every world name and every edge label appears, and a dashed loop has `stroke-dasharray`). In `Tests/StaticHtml.lean`, add a case that `dynamicStaticJson` of the handoff scenario parses as JSON with a `before` field.

- [ ] Steps follow Task 5's pattern: failing tests, implementation, run on `Notebooks/Dynamic*.lean`, check that no placeholders remain, commit as "Draw static pictures of the dynamic explorer for the notebook pages".
