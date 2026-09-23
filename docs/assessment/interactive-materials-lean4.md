# Interactive teaching materials in Lean 4: review and conclusions

Date: 2026-09-23. Written by Claude (Opus 5.5) for Brian and Jeremiah Chapman.
Input reviewed: `/private/tmp/interlean.txt`, a transcript of a conversation
with another AI assistant comparing interactive-materials tooling for Lean 4
and Haskell. Its load-bearing claims were checked against primary sources
(GitHub repositories and commit history, official docs, Lean release notes)
on 2026-09-23. Companion to `feasibility-assessment.md` and
`haskell-vs-lean4.md`.

## Bottom line

Lean 4 is a better home for gamen's teaching materials than Haskell, but not
for the reason the transcript gives, and not without work. Moving to Lean
does **not** by itself restore what Pluto provides. What it does is:

1. **End the split.** The logic engine and the teaching materials can live in
   one language. The Gamen.jl/Pluto vs. gamen-hs division was a two-codebase
   problem; Lean removes it.
2. **Give students a live environment Haskell never had.** Edit a model in
   a Lean file and every result below it is recomputed. The infoview shows
   types and values at the cursor. There is no hidden state. The gamen-hs
   notebooks, by contrast, are static Markdown with output spliced in at
   build time.
3. **Add a capability Pluto lacks.** Exercise answers can be machine-checked
   (`example : … := by native_decide`) rather than read off by eye.

Getting Pluto-style widgets (checkboxes, dropdowns, drawn Kripke models)
means building them, once, with ProofWidgets. Getting zero-install access
for students means hosting a server. Both are feasible; neither comes for
free.

## The claims, checked

| Claim in the transcript | Verdict | What is actually true |
|---|---|---|
| `lean4_jupyter` is a working Jupyter kernel | **Partly** | It exists (utensil/lean4_jupyter) and is built on Lean's REPL, but the last commit was Nov 2024, targeting Lean 4.8–4.11. It is unmaintained for current Lean. |
| `lean-to` is a Jupyter kernel wrapper for Lean 4 | **False in effect** | bollu/lean-to exists but was abandoned in April 2022 (54 commits, last one "add hello world"). |
| Verso produces interactive course materials | **Partly** | Verso is the Lean FRO's publishing tool (used for the Lean reference manual and *Functional Programming in Lean*). Its HTML is **static**: elaborated code with hovers, go-to-definition, and proof states baked in, but no code runs in the reader's browser, and widgets do not carry over (open RFC, verso#311). |
| The Lean editor works "like a Pluto notebook" with zero hidden state | **Partly** | Zero hidden state: true. Pluto-style reactivity: **false**. Lean re-checks the file top-down from the point of an edit; it has no dependency graph. For a notebook written top to bottom, the experience is close; for anything else it differs. |
| Lean Playground runs a full compiler in the browser via WASM, no server | **False** | lean4web and live.lean-lang.org run Lean **server-side** (Express + WebSocket proxy to a sandboxed Lean process). In-browser WASM was explored by Lean developers and not pursued. |
| Lean Game Server gives gamified browser exercises | **True** | It is a server application (self-hostable, or published at adam.math.hhu.de). Every existing game is proof/tactic based, not programming. |
| Native widgets (UserWidget) render interactive React components from Lean files | **True** | ProofWidgets4 offers JSX-like syntax in Lean, interactive SVG/HTML, Recharts and Penrose diagrams, and RPC back to Lean for click/drag interaction. It works **only in a live editor** connected to a Lean server. |
| Haskell web deployment needs "heavy backend servers or GHCJS" | **Outdated** | GHC has had official WebAssembly and JavaScript backends since 9.6. Both are still "technology preview," but GHCJS is being superseded. |
| Haskell is limited to GHCi for interaction | **Overstated** | IHaskell is actively maintained (2026), and the HLS eval plugin evaluates `-- >>>` comments in the editor. Haskell's interactive story is weaker than Lean's, not absent. |
| Haskell's advantage is its data-science ecosystem | **Irrelevant here** | For plotting and statistics, the real alternatives are Julia and Python, not Haskell. gamen needs model diagrams, not large-scale data science. |
| (implied) A Pluto-like reactive notebook exists for Lean | **None found** | No dependency-graph notebook with bound sliders exists for Lean 4. |

Overall, the transcript gets the direction right (Lean's in-editor
interactivity is richer than Haskell's) but overstates maturity in four
places: stale Jupyter kernels presented as working, in-browser execution
that doesn't exist, Pluto-equivalence that is only partial, and widgets in
exported pages that aren't supported yet. It also understates Haskell's
current tooling.

## What the Pluto notebooks actually do, and the Lean equivalent

Counted across the 20 Gamen.jl notebooks (theory and health tracks):

| Pluto feature | Use in Gamen.jl | Lean equivalent | Status |
|---|---|---|---|
| Reactivity (change a cell, dependents rerun) | throughout | Top-down re-elaboration in the editor | **Available.** Same experience if notebooks are written top to bottom, which they already are. |
| `@bind` widgets (43): `Select` to build formulas from operators and atoms, to choose the logic/system; `CheckBox` to toggle clinical facts (e.g., "cultures drawn," "antibiotics started") | 43 bindings | ProofWidgets HTML components with RPC to Lean | **Must be built.** A lower-fidelity fallback that works today: students edit a literal (`def culturesDrawn := true`) and watch the results below update. |
| `visualize_model` (Makie Kripke graphs) | 55 calls | ProofWidgets SVG or Penrose diagram in the infoview | **Must be built**, once, as a reusable `#kripke m` widget. |
| Markdown prose between cells | throughout | Module docstrings and `/-! … -/` blocks in the editor; Verso for a published book | **Available.** |
| Static HTML export for reading | Pluto HTML export | Verso (hovers, types, proof states; no execution, no widgets yet) | **Available**, with that limit. |
| Student access | Local Julia + Pluto install | (a) Local VS Code + elan; (b) self-hosted lean4web with gamen as a dependency; (c) Lean Game Server for guided exercises | **Available**, but (b) and (c) need a server we run. |

**New with Lean, not possible in Pluto:** exercise answers checked by
Lean itself. Tested against the slice code (`sketches/lean`):

```lean
-- Exercise 1.4: is □p → p true at every world of this model?
def answer : Bool :=
  match isTrueIn exerciseModel (.implies (.box p) p) with
  | .ok b => b | .error _ => true
example : answer = false := by native_decide   -- accepted
example : answer = true  := by native_decide   -- rejected: "evaluated that the proposition … is false"
```

The student changes `false` to `true`, and Lean says they're wrong, with no
instructor involved.

**Checked honestly, this uses `native_decide`, not `decide`.** Plain
`by decide` (checking in Lean's trusted kernel) fails on the current code:
the kernel cannot unfold `satisfies`, which uses well-founded recursion,
or the `Std.TreeSet` internals. `native_decide` runs the compiled code
instead, so the guarantee is "the compiled evaluator agrees," not "the
kernel proved it." For a teaching exercise that is enough. For claims made
in a paper, it is not, and Mathlib discourages it for proofs. If
kernel-checked exercises matter, the teaching layer needs structurally
recursive semantics over simple data (lists, not tree sets), which is a
design choice to make early.

## Principles behind these conclusions

1. **Judge by what the students do, not by the feature list.** The bar is set
   by the existing Pluto notebooks: select and toggle, watch results and
   diagrams update, read the prose around them. Anything Lean offers that
   those notebooks don't use (proof-state panes, games) is a bonus, not a
   reason.
2. **Count only what exists and is maintained today.** Two of the transcript's
   four headline tools (both Jupyter kernels) are abandoned, and one
   (in-browser Lean) doesn't exist. Plans should rest on Verso, ProofWidgets,
   lean4web, and lean4game, all of which are active.
3. **Keep authoring and delivery separate.** Lean's live experience belongs to
   whoever is running a Lean server, local or hosted. Static export (Verso)
   keeps the hovers and loses the execution. Any plan has to say which of
   the two a given student gets.
4. **One language beats two.** Keeping Gamen.jl and gamen-hs in sync is the
   cost that prompted this project. A Lean library plus Lean teaching
   materials removes that cost regardless of how the widget work goes.
5. **Mind the audience.** The primary audience is health informatics graduate
   students with no logic background. The Lean infoview is built for proofs
   and can overwhelm them. The materials should lean on `#eval` output and
   custom widgets, and introduce the goal view deliberately, not by accident.

## Recommended next step

Before retiring any Pluto notebook, prototype one pair of chapters in Lean:
B&D Chapter 1 (Kripke models) and its health counterpart (the sepsis
timing scenario that uses the checkbox toggles). The prototype needs:

1. A reusable Kripke-model widget (ProofWidgets SVG) with click-to-toggle
   valuations, which covers the `visualize_model` + `CheckBox` pattern.
2. A formula-builder widget (operator/atom dropdowns), covering the
   `Select` pattern.
3. Three machine-checked exercises (`by native_decide`), plus one attempt at
   a kernel-checked (`by decide`) variant over list-based models, to size the
   cost of the stronger guarantee.
4. Delivery through a self-hosted lean4web instance with the gamen Lean
   package preinstalled, tried by a couple of students who haven't seen Lean.

Success criterion: a student with no Lean experience can do everything the
Pluto version lets them do, in a browser, without installing anything.

**Caveat on my own literacy:** I have not built a ProofWidgets widget in
this session. Its API has changed across Lean releases, so widget code
should be written against the current ProofWidgets4 examples and
compile-checked. The same discipline applied to Plausible in the slice
test.

## Prototype results (2026-09-23, Opus 5.5)

The recommended next step was carried out: both Chapter 1 notebooks were
ported to Lean, with widgets, and served from a local lean4web. Code:
`sketches/lean/` (notebooks, widgets, tests) and `sketches/web-projects/`
(the lean4web course project and a loopback-only launcher). Screenshots:
`sketches/lean/docs/`.

**Pairing correction.** The plan named "Chapter 1 and its sepsis
scenario." The sepsis checkboxes are actually in the Chapter 14 temporal
notebook. The real Chapter 1 pair is `ch1_syntax_and_semantics.jl` and
`ch1_health_clinical_obligations.jl`, and that pair was ported.

### What was built

| Piece | Replaces in Pluto | Notes |
|---|---|---|
| `ml[ … ]` notation | `Box(Implies(p, q))` | Textbook symbols in their own syntax category; `{t}` splices named formulas. Four `#guard` checks. |
| `KripkeExplorer` widget | `visualize_model` + `@bind … CheckBox` + live results table | Written in Lean on ProofWidgets `InteractiveSvg`: click a fact chip, then click a world to toggle it; every check formula is re-evaluated by `satisfies` on each click. Static mode draws Figure 1.1 and the ED model. |
| `hint` / `hints` | "Reveal answer" admonitions | `<details>` HTML in the infoview. |
| Guideline cards | `@bind selected_guideline Select(...)` | Five collapsible cards shown together, not a dropdown. |
| Prediction exercises | "predict, then reveal" | `some true`/`some false` answers graded by `#eval`; `native_decide` examples show statements Lean checks. |
| `Ch1SyntaxSemantics.lean`, `Ch1HealthObligations.lean` | the two Pluto notebooks | All sections ported except the long history passage (condensed) and the Knowledge Representation Lens asides. |
| `GamenCourse` + `run-local.sh` | running Pluto locally | lean4web with the notebooks under *Examples*; bound to 127.0.0.1. |

### How it was verified

1. **Answer keys.** The test suite checks every answer the Pluto notebooks
   state against the Lean models: Problem 1.1 (F T T F T T T F F), the
   four practice items, the challenge, G1–G5 at w1 (T F F T F), and the
   prover verdicts for G5/G6, G4/G7, and G8/G9. All match.
2. **Widget interaction.** Six tests replay clicks through the widget's
   `update` exactly as ProofWidgets' server loop does. A mutation check
   confirmed the tests catch the real bug described below.
3. **Rendering.** The widget's SVG was rendered offline and inspected, and
   the notebooks were then driven in Chrome through lean4web. Clicking
   `blood_cultures` and then w3 turned G2 and "All obligations met" green;
   hints expanded on click. (`docs/widget-before-click.png`,
   `docs/widget-after-click.png`, `docs/ed-diagram-in-browser.png`.)
4. `lake test`: **36/36** pass.

### Problems found and fixed along the way

- **Every click would have been ignored.** ProofWidgets records which
  element was pressed only *after* processing the mousedown event, so a
  handler that acts on mousedown never sees the clicked element. The
  handler now acts on mouseup. Unit tests that called the click handler
  directly passed anyway; only the protocol-faithful replay caught it.
- **Clicks on labels didn't reach the shape.** World names and chip labels
  now carry the same data as the shape underneath.
- **Layout:** chip labels sat outside their rectangles (SVG rectangles hang
  down from their corner, and the y-axis points up); facts collided with
  the instructions; the 600 px canvas overflowed a normal-width infoview.
  The canvas is now 480 × 432 and fits.
- **Server load:** the stock component polls the server every 33 ms.
  Polling is off; the widget talks to Lean only on a click. This matters
  when many students share one server.
- **Debug text:** the stock component prints its internal state under
  every widget. A vendored copy strips that line (`Widgets/js/make-quiet.sh`,
  Apache-2.0, modification noted).
- **Citations:** my Lean slice mis-cited B&D (frame/model as 1.6/1.7,
  truth at a world as 1.9, truth in a model as 1.11). Checked against the
  PDF: model = 1.6, truth at a world = 1.7, truth in a model = 1.9,
  validity = 1.11. Fixed. gamen-hs was already correct.
- **Network exposure:** lean4web's `npm start` serves the editor on every
  network interface, and on macOS Lean runs unsandboxed. The first run did
  exactly that; it was stopped as soon as it was noticed. `run-local.sh`
  and two small local edits to the lean4web clone now bind everything to
  127.0.0.1. A port conflict with an unrelated local `python3 -m
  http.server 8080` was avoided by moving lean4web's server to 8090.

### Open problems

1. **First load in lean4web can leave the infoview stuck** on "No info
   found" (server log: "Outdated RPC session"). It reproduced twice when
   an example was loaded into a fresh page; a page reload fixed it both
   times. It would confuse students, and the cause (lean4web vs. our setup)
   is not yet isolated.
2. **Classroom hosting is undecided.** A real deployment needs a Linux
   server with bubblewrap and lean4web's production mode, plus a decision
   about who runs it (UTSW infrastructure or a cloud host). That's your
   call, not a technical blocker.
3. **Not yet tried by students.** The success criterion (a Lean novice can
   do everything the Pluto version allows, in a browser, without
   installing anything) is testable now but has not been tested.
4. **Parity gaps.** No dropdown widget: the guideline selector became
   cards, and the extension notebook's operator/atom formula builder was
   not ported. SVG text doesn't wrap, so long check labels need short
   names. Exercise checks use `native_decide`, which trusts the compiler
   rather than the kernel (see above).
5. **Reliance on an unstable interface.** The RPC name `updateSvg` is fixed
   by ProofWidgets' JavaScript, and the mouseup behavior depends on its
   server loop. Both are pinned at v0.0.111; a ProofWidgets upgrade should
   rerun the widget tests (they will catch a change in event order).

### Effort

About one working session of model time for both notebooks, the widgets,
the notation, the tests, and the web setup. Most of the debugging went to
ProofWidgets' interaction details and lean4web's network defaults, not to
the logic. The remaining Pluto notebooks would reuse all of this, so each
further chapter is mostly prose and scenario definitions.
