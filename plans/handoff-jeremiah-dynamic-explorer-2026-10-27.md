# Handoff to Jeremiah: the dynamic-scenarios explorer

*2026-10-27. Written for Jeremiah, who is taking over this branch from Brian.
Everything you need is in the repo; this file is the starting point.*

## 1. What this is

A new teaching widget for gamen-lean, plus three notebooks that use it. A
student loads a small clinical model, applies an update (an action model, or
an ATL-D grant or revoke), sees the model before and after, and answers
graded questions of three kinds: click the worlds where a formula holds,
change the update so a goal holds, and write a formula true exactly at given
worlds. Wrong answers get a reason.

It covers four scenarios:

| # | Scenario | Logic | Notebook |
|---|---|---|---|
| 1 | Handoff: a page about high potassium may or may not reach the day clinician | Action models (Lorini, Perrotin & Schwarzentruber, KR 2022) | `Notebooks/DynamicEpistemic.lean` |
| 2 | "I would if I could": a patient lacks the referral action | ATL-D (Galimullin, Grosinger & Mittelmann, KR 2026) | `Notebooks/DynamicAbility.lean` |
| 3 | Safety versus access: a revoke and the reasonableness rule | ATL-D | `Notebooks/DynamicAbility.lean` |
| 5 | Shift change: ordering authority changes hands; the pharmacist isn't told | ATEL-D | `Notebooks/DynamicCapstone.lean` |

Scenario 4 (pancreatic cancer, angels and demons) is deliberately not built
yet; see section 9.

Read these for the why and the how, in this order:

1. `docs/superpowers/specs/2026-10-21-dynamic-scenarios-explorer-design.md`:
   the design and Brian's decisions.
2. `docs/superpowers/plans/2026-10-22-dynamic-scenarios-explorer.md`: the
   implementation plan (9 tasks). The code follows it, with the deviations
   listed in section 7 below.
3. `CLAUDE.md`: project rules (Except not panic!, no partial def, American
   English, B&D citations checked against the PDF).

## 2. Get the branch

The work is on the branch `dynamic-explorer` on GitHub; `main` does not
have it yet. The branch also carries three commits that were never on
GitHub's `main` (an EvidenceTrust docstring fix, the design, and the plan).
If `git` is not installed yet, do section 3.1 first.

If you don't have the repo yet:

```sh
git clone git@github.com:chapmanbe/gamen-lean.git
cd gamen-lean
git switch dynamic-explorer
```

(Use `https://github.com/chapmanbe/gamen-lean.git` if you have no SSH key
on GitHub.)

If you already have a clone:

```sh
cd gamen-lean
git fetch origin
git switch dynamic-explorer
```

Commit or set aside any local changes first, or `git switch` refuses.
`git branch --show-current` should print `dynamic-explorer`. From then on,
`git pull` on this branch picks up anything Brian pushes. To push your own
work you need collaborator access on `chapmanbe/gamen-lean`; ask Brian if
`git push` is refused.

## 3. Setting up Lean and VS Code on macOS

Do these once, in order. Commands go in Terminal (or VS Code's terminal,
**⌃`**). macOS's default shell is zsh, so the shell config file is
`~/.zshrc`.

### 3.1 Command-line developer tools (git)

Lake fetches the project's dependencies with git.

```sh
git --version
```

If that prints a version, skip ahead. If macOS offers to install the
"command line developer tools", accept; or run `xcode-select --install`.

### 3.2 VS Code

1. Download VS Code from <https://code.visualstudio.com>, unzip it, and drag
   **Visual Studio Code.app** into **/Applications**. Run it from there, not
   from Downloads: macOS runs apps outside /Applications from a temporary
   location, which breaks the `code` command below.
2. Install the `code` command: in VS Code press **⇧⌘P** (Command Palette),
   run **Shell Command: Install 'code' command in PATH**, and enter your
   password if asked. This makes `/usr/local/bin/code`, a link to a small
   script inside the app. Check in a *new* terminal:
   ```sh
   which code        # /usr/local/bin/code
   ```

### 3.3 elan (Lean's version manager), lake and lean

You never install a Lean version by hand: elan reads each project's
`lean-toolchain` file (here 4.34.0) and downloads that version the first time
it's needed.

```sh
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
```

Accept the default installation. It puts `elan`, `lake` and `lean` in
`~/.elan/bin`.

### 3.4 Put `~/.elan/bin` on your PATH

The installer may write a PATH line into a profile file that your terminal
doesn't read, so add it to `~/.zshrc` yourself:

```sh
echo 'export PATH="$HOME/.elan/bin:$PATH"' >> ~/.zshrc
source ~/.zshrc
```

Check, in a **new** terminal window:

```sh
which elan lake lean   # all three under /Users/<you>/.elan/bin
elan --version
```

If `which` finds nothing, open `~/.zshrc` (`code ~/.zshrc`) and confirm the
line is there exactly once, then open another new terminal. A line with a
typo, such as a stray character after the closing quote, can stop the rest
of the file from being read.

### 3.5 The Lean 4 extension

1. In VS Code, open Extensions (**⇧⌘X**), search **Lean 4**, and install the
   one published by **leanprover** (id `leanprover.lean4`).
2. **Quit VS Code completely (⌘Q) and reopen it.** VS Code reads PATH when it
   starts; a window opened before step 3.4 won't find `lake`.

### 3.6 Open the project the right way

Always open the **folder** that contains `lakefile.toml`, not a single file:

```sh
cd gamen-lean            # your clone, on the branch from section 2
code .
```

or **File → Open Folder…**. Opened as a single file, the extension can't find
the project and every import fails.

Then build once from VS Code's terminal (**⌃`**), which starts in the
project folder:

```sh
lake --version           # first run in the folder downloads Lean 4.34.0
lake build               # downloads ProofWidgets and Plausible, then builds; several minutes
```

### 3.7 Check that everything works

1. Open `Notebooks/Ch1SyntaxSemantics.lean`. A thin orange bar in the left
   margin shows Lean processing the file; wait for it to disappear.
2. The **infoview** panel opens on the right. If it doesn't: press **⇧⌘P**, type
   `infoview`, and pick the Lean 4 command that toggles it.
3. Put the cursor on a `#eval` line: its result appears in the infoview. Put
   it on an `#html kripkeExplorer …` line: a clickable diagram appears.

If that works, the setup is complete.

### 3.8 Typing logic symbols

- **In a `.lean` file**, the extension turns backslash abbreviations into
  symbols as you type: `\and` → ∧, `\or` → ∨, `\not` → ¬, `\to` → →,
  `\iff` → ↔, `\<` → ⟨, `\>` → ⟩, `\top` → ⊤, `\bot` → ⊥. Hover over a
  symbol to see how to type it.
- **In the explorer's formula box**, abbreviations don't work, because it's
  a web text field, not the Lean editor. Use the ASCII forms the parser
  accepts: `~` (¬), `&` (∧), `|` (∨), `->` (→), `<->` (↔), `<<a>>` (⟨⟨a⟩⟩),
  `true`/`false`, `[]`/`<>` (□/◇). For example, `K[D]p & ~K[N]K[D]p`.

### 3.9 Optional: the GitHub CLI

For filing issues from the terminal (section 10), install Homebrew
(<https://brew.sh>), then:

```sh
brew install gh
gh auth login
```

### 3.10 Troubleshooting

| Symptom | Fix |
|---|---|
| `zsh: command not found: lake` | Step 3.4; then open a new terminal. |
| The extension says it can't find Lean or `lake` | Quit VS Code with ⌘Q and reopen it (step 3.5). |
| Every `import` is red | You opened a file, not the folder; reopen the folder (step 3.6). |
| The orange bar never finishes on a notebook | Run `lake build` in the terminal and read the first error. |
| Your edit to a `data/scenarios/*.json` file or the widget JS has no effect | Lake doesn't track those files; see the "Lake gotcha" in section 4. |
| The infoview is stuck or stale after a rebuild | ⇧⌘P, type `restart`, and run the Lean 4 command that restarts the server (or restarts the file). |

## 4. Build and test

```sh
lake build        # library, widgets, notebooks, gamen-validate (a few minutes the first time)
lake test         # expect: 1759/1759 passed
```

The new tests are in `Tests/DynamicInput.lean` (parsers),
`Tests/DynamicExplorer.lean` (grader, state machine, widget RPC) and
`Tests/DynamicScenarios.lean` (every scenario's answer key, hints, and
library-level claims checked directly against `productUpdate`/`dsat`).

**Lake gotcha.** The scenario files and the widget's JavaScript are pulled in
with `include_str`, which Lake does not track. After editing
`data/scenarios/*.json`, make any real change to `Widgets/Dynamic/Library.lean`
so it rebuilds (the disk-staleness test in `lake test` fails if you forget).
After editing `Widgets/js/dynamicExplorer.js`, do the same to
`Widgets/Dynamic/Widget.lean`; nothing catches stale JS.

## 5. Where things are

| Path | What |
|---|---|
| `Gamen/Input.lean` | Tokenizer and parser for epistemic formulas (`K[a]p`, `¬`, `∧`, `[p]q`, ASCII too) |
| `Gamen/Atl/DynamicInput.lean` | Parser and round-trip printer for ATL-D formulas (`⟨⟨a⟩⟩F p`, `has(a,α)`, `[φ:α→{A},{B}]+ψ`) |
| `Widgets/Dynamic/Scenario.lean` | Scenario format, JSON decoding, before/after models per logic, unknown-atom check |
| `Widgets/Dynamic/Grade.lean` | Grading, hints, minimality check, required-selection check |
| `Widgets/Dynamic/Explorer.lean` | Pure state machine: `step`, `view` (all logic is in Lean) |
| `Widgets/Dynamic/Widget.lean` | Root RPC method `dynamicExplorerStep`, the ProofWidgets component |
| `Widgets/js/dynamicExplorer.js` | Hand-written renderer (no bundler); draws `view`'s JSON, sends events |
| `Widgets/Dynamic/Library.lean` | Loads `data/scenarios/*.json`; `dynamicExplorerOr` |
| `data/scenarios/*.json` | The four scenarios: models, controls, layout, questions, answers, hints |
| `Notebooks/Dynamic*.lean` | The three notebooks |

The existing `Widgets/KripkeExplorer.lean` is untouched; ProofWidgets' root
`updateSvg` method belongs to it, which is why the new widget has its own JS
and RPC method.

## 6. What to check first (by eye; nobody has yet)

The code was reviewed task by task and as a whole branch, but the widget has
never been looked at in a real infoview. Please do these, in order.

### 6a. A known rendering bug: self-loops hidden behind stacked worlds

Brian found it: in `DynamicEpistemic.lean`, tick **N** only, press Apply, and
w1×sent shows no loop labeled N. The model is right: with only N observing
the after-model has the edge (N, w1×sent → w1×sent) (checked by evaluating
`Library.handoff`'s `after ["N"]`). Two rendering choices hide it:

- `edgeGroups` in `Widgets/js/dynamicExplorer.js` merges all edges on the same
  pair, so D's and N's loops become one loop labeled `D,N`.
- Self-loops are drawn *above* the node, and the layout stacks product worlds
  (w1×lost, w1×sent) only 0.12 apart (`siblingGap` in `Explorer.lean`, about
  43 px). The lower world's loop and label fall behind the upper world's
  circle, which is drawn on top.

Options (Brian hadn't decided):

1. Draw self-loops to the side of the node; give `handoff.json` explicit
   `layout` entries for the product worlds (an exact name beats the
   stacking); keep merged labels in a fixed order.
2. Don't draw reflexive loops at all (every relation in these epistemic
   models is reflexive) and say so once in the notebook. Check B&D's own
   figure convention in the PDF first (`notes/bd-screen.pdf`, edition pinned
   in `notes/bd-edition.md`); don't cite it from memory.

Either way, look at all four scenarios after the change: the same overlap
can happen wherever worlds stack.

### 6b. The widget click-through

`NEXT.md` (the "Before merge" item) has a scratch file and nine numbered
steps that exercise every control: Apply, clicking worlds, Check, typing a
formula, a parse error, question navigation, persistence when the cursor
moves, Reset, the dashed "otherwise: stay" loops, and the notes box for a
revoke the reasonableness rule blocks. Follow them as written.

### 6c. The three notebooks

Also in `NEXT.md`, step by step. Read each notebook as a student would:

- Does the prose match what the diagram shows?
- Can every question be answered from the screen?
- Does every wrong answer get a reason that's true?
- Do the prompts say exactly what to tick and press? (Questions about a
  particular model now *refuse* to grade under a different selection and say
  what to tick; check that the refusal reads well.)

Every logical claim in the prose is supposed to have a test behind it in
`Tests/DynamicScenarios.lean`. If you find a claim without one, that's a bug.

## 7. Decisions made during the build that you should review

These were made on Brian's behalf while he was away; he hasn't reviewed them
all. The ones most worth your judgment as a logician come first.

1. **The capstone story changed.** The plan had the shift-change grant
   conditioned on ⊤. In ATEL-D a ⊤-conditioned grant holds at every state, so
   every agent knows it, informed or not; the pharmacist can't be left
   ignorant that way. The grant and revoke are now conditioned on an atom
   `handoff` (the shift has changed), and the pharmacist starts out unable to
   tell handoff from non-handoff states. A fourth state, `new-shift-present`,
   blocks atom shortcuts in the formula question. The ⊤ point became a
   question of its own. Check that this is the right way to tell the story,
   and the wording of the premise ("the pharmacist does not know whether the
   shift change has happened yet").
2. **Subjective mode for ATEL-D.** The capstone uses the subjective reading of
   ⟨⟨A⟩⟩; in this model subjective and objective give the same answers, so a
   student never sees the reading matter. Worth a question that separates
   them, if you want one.
3. **Unknown atoms are errors.** A formula naming an atom the model doesn't
   have (a typo, or a state name like `crisis`) is reported as an error that
   lists the model's atoms and, in ATL-D, suggests `has(agent,action)`. The
   library's own semantics treats unknown atoms as false; the explorer checks
   before evaluating.
4. **Minimal answers.** Reach-the-goal questions can ask for the fewest
   choices (`"minimal": true`): a selection that works is still marked wrong
   if a strict subset also works, with a message naming what isn't needed.
5. **Required selections.** Click and formula questions name the selection
   they're about (`"selection"` in the data) and refuse to grade under any
   other.
6. **Default moves drawn dashed.** Joint moves an ATL-D model leaves to
   `default_next` are drawn as one dashed "otherwise: stay" loop per state, so
   they're visible but distinct from listed moves.
7. **Update notes.** Notes such as a revoke blocked by the reasonableness rule
   have their own box and stay visible until the update is undone.
8. **Formula syntax.** Students type what the parsers read: `K[a]φ` for both
   logics (the library's `DFormula.toString` prints `K_aφ`, which is ambiguous
   for multi-letter agents, so the explorer uses its own printer).

## 8. Known small issues (deferred; none blocks merge)

From the reviews, triaged as "can wait":

- Parser error messages: `K[a p` says "expected an agent name" rather than
  "missing ]"; `K[true]` gives a confusing message; an empty update list
  `[]+ψ` can't be parsed (`[]` reads as □).
- `toggleable` agent names in a scenario aren't checked against the model's
  agents (a wrong name is silently inert).
- Single-direction arrows are drawn 4 px off-axis; long joint-move labels on
  one edge can get very long (e.g. old-shift → ordered after the grant).
- Errors and prompts share one box in the widget; an `isError` flag in `view`
  would let the renderer color errors.
- Scenario 3 has no write-a-formula question (the spec asks for a mix of all
  three kinds).
- In ATL-D, a reach-goal question whose `atWorld` names a nonexistent state
  grades false instead of erroring (authoring typo; no shipped scenario hits
  it).
- Formula hints match on trimmed text, so `~K[D]p` misses a hint written for
  `¬K[D]p` (it still gets a generated explanation).
- The notebooks lack an "objectives" list like `Ch1HealthObligations.lean`.
- `PORTING.md`'s ATL-D row says "behavioural" (pre-existing).

## 9. What comes after

- **Scenario 4 (pancreatic cancer, angels and demons).** Waiting for its
  sources: PDFs to download by hand (the list and citations are in Brian's
  `~/Downloads/pancreatic-lit/lit-search.md`; ask him for it). It needs its
  own plan: a parser for `AngelsDemons.SFormula`, and strategy extraction so
  a student can play the health system step by step. The design's
  "system-design reading" section explains why the student plays the
  modifier, not the patient.
- **Documentation site.** Design at
  `docs/superpowers/specs/2026-10-22-documentation-site-design.md`, awaiting
  Brian's approval: doc-gen4 API docs plus read-only notebook pages on GitHub
  Pages.

## 10. Reporting

File problems on gamen-lean (`gh issue create -R chapmanbe/gamen-lean`), one
issue per problem, with the scenario, the selection, and what you saw. When
the checks in section 6 pass and the rendering bug is fixed, the branch is
ready to merge into `main`.
