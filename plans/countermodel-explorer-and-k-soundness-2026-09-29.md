# Plan: tableau countermodel explorer, a machine-checked soundness proof for K, and edition-proof B&D citations

*Written 2026-09-29. Read this once; implement against it. Three independent
parts. Part A is a teaching feature (one or two sessions). Part B is a
research milestone (several sessions, merged one milestone at a time).
Part C is tooling that keeps B&D citations correct across editions (one
session; added the same day). No part waits on anything outside the repo. In particular, no step
waits on student testing: none is available, so every check below is
automated or done by an agent.*

## Objective

- **Part A.** From a formula, run the tableau, and if the formula is not
  valid, show the extracted countermodel in the existing Kripke explorer,
  where the student can click through it. Valid formulas and unknown
  verdicts are reported plainly. An unverified model is never shown.
- **Part B.** Prove in Lean, with no `sorry` and no `native_decide`, that
  the *executable* tableau prover (`Gamen.Tableau.buildTableau` as it
  runs) is sound for K. A closed tableau means the assumptions are
  unsatisfiable (B&D Theorem 6.6). That makes "the tableau says valid" a
  checked theorem, not a tested hope.
- **Part C.** Give every B&D citation an anchor in the Open Logic sources
  that survives renumbering, and a checked index, so that wrong citations
  fail a test today, and moving to a new edition is a reviewed report
  rather than a hunt. The evidence is in
  `docs/assessment/bd-source-anchors-2026-09-29.md`.

## Where things stand (2026-09-29; verify with `git log`)

- `main` at `ea2e0fe`, pushed. The port is nearly done: Atl.ImperfectInfo
  is in progress, and Dcleg remains. `Gamen/Tableau.lean` is fully ported
  and stable.
- The pieces Part A joins already exist:
  - `buildTableau sys maxSteps assumptions : TableauOutcome` (`.closed`,
    `.stillOpen branches`, `.exhausted n`), in `Gamen/Tableau.lean`.
  - `extractCountermodel sys b : Except String Model`, in the same file.
    It **re-checks** the model against every signed formula on the branch
    before returning it, and throws otherwise (budget-truncated branches,
    and blocked branches in KTB and S5).
  - `Widgets/KripkeExplorer.lean`:
    - `Scenario` holds worlds with (x, y) positions, edges, atoms,
      editable worlds, `evalAt`, `checks` and a valuation;
    - `kripkeExplorer : Scenario → Html`;
    - `Scenario.toModel`.
- The executable semantics is `Gamen.Semantics.satisfies : Model → World →
  Formula → Except String Bool`. It is built on `Std.TreeSet`/`TreeMap` and
  uses well-founded recursion, which is why the notebooks use
  `native_decide`, not `decide` (see CLAUDE.md).
- The B&D citations below were checked against `notes/bd-screen.pdf`
  (SHA-256 `3c50d5da…bc453`, the Fall 2025 edition pinned in
  `notes/bd-edition.md`).

## Part A: tableau → countermodel → explorer

### Design

1. **A new module, `Widgets/Countermodel.lean`,** imported by the widget
   library. It has no gamen-hs counterpart, so list it in `PORTING.md` as a
   Lean-only addition.
2. **One result type:**
   ```lean
   inductive CountermodelView where
     | valid                                  -- closed tableau
     | countermodel (sc : Scenario) (branch : Nat)
     | unknown (why : String)                 -- budget exhausted, or no open
                                              -- branch gave a verified model
   def countermodelView (sys : System) (premises : List Formula)
       (conclusion : Formula) (maxSteps := defaultMaxSteps) : CountermodelView
   ```
   - Build the assumptions exactly as `tableauProves` does. Factor out a
     shared `proofAssumptions` helper in `Tableau.lean` so the two cannot
     drift apart. This is a pure refactor; keep `compare.py` at zero
     disagreements.
   - On `.stillOpen bs`, try `extractCountermodel` on each open branch in
     order and use the first that succeeds.
   - If every branch fails, return `.unknown` with the first error. Never
     fall back to an unchecked model.
3. **Reuse the existing widget.** `ProofWidgets` requires the RPC name
   `updateSvg` and allows one explorer state type (CLAUDE.md), so the
   countermodel view only has to *produce a `Scenario`*. No new widget
   state and no new JavaScript are needed.
4. **Layout from the prefix tree.** Worlds are prefixes (`"1"`, `"1.1"`,
   `"1.2.1"`), so depth gives the row and the leaves are spread across the
   columns. Respect the `Scenario` docstring's constraint: y ≥ 4.9 + 0.3 ×
   (facts shown), inside the 10 × 9 canvas.
   - Draw every edge of the closed relation, since the checks evaluate on
     `Scenario.toModel`, which must equal the extracted model. Reflexive
     edges use the existing `selfLoop`.
   - If a model doesn't fit (too many worlds, depth or atoms), render a
     static, still verified, text view instead: worlds, R and V as HTML
     lists.
   - The first task is to measure the limits. Expect about 3 atoms and
     depth ≤ 2. Record them in the docstring.
5. **Checks and editing.**
   - `evalAt := "1"`, the root.
   - The checks are the conclusion (expected false) and each premise
     (expected true). Label them `conclusion` and `premise 1`, … and put
     the formulas in the surrounding HTML prose, because SVG text doesn't
     wrap.
   - Make every world editable, so a student can toggle facts and watch
     the conclusion's check change. That is the teaching point: the
     countermodel is a witness, not magic.
6. **The notebook entry point is a function, not a new command:**
   `#html countermodelHtml systemK [] ml[□(p ∨ q) → □p ∨ □q]`. It wraps
   the verdict in a sentence ("valid in K", "not valid in K; here is a
   countermodel read off open branch 2", "unknown: …") and embeds
   `kripkeExplorer` for the countermodel case.
7. **Notebook section.** B&D §6.9 "Countermodels from Tableaux" (p. 110)
   and Example 6.22 (pp. 111–113).
   - Add it to the ported tableau notebook if one exists by then.
     Otherwise create `Notebooks/Ch6Countermodels.lean` with Example 6.22
     plus two exercises: the S4-valid, K-invalid `□p → □□p`, and one that
     is K-valid.
   - Every stated answer goes into the answer-key tests (CLAUDE.md).

### Verification (all automated; nothing waits on students)

1. **Answer key from B&D Example 6.22** (pp. 112–113, Figure 6.1). For
   `□(p ∨ q) → (□p ∨ □q)` in K, the view is a countermodel with:
   - W = {1, 1.1, 1.2};
   - R = {⟨1, 1.1⟩, ⟨1, 1.2⟩};
   - V(p) = {1.2} and V(q) = {1.1}.

   Assert this exactly.
2. **Unit cases:**
   - the K axiom `□(p → q) → (□p → □q)` gives `.valid`;
   - `□p → □□p` gives a countermodel in K and `.valid` in S4;
   - `□p → p` gives a countermodel in K whose model has no ⟨1,1⟩ edge,
     and `.valid` in KT;
   - a formula outside the Kripke fragment gives `.unknown`, not an error.
3. **Property test** (Plausible, capped formula size, systems K, KT, S4):
   - whenever the view is `.countermodel sc`, `satisfies sc.toModel "1"
     conclusion = .ok false`, each premise is `.ok true`, and every world's
     position is inside the canvas and meets the y constraint;
   - whenever it is `.valid`, `tableauProves` says `.definitely true`.
4. **Widget event tests:** replay a toggle on the Example 6.22 scenario
   with the existing harness (mouseup order, CLAUDE.md) and check that the
   conclusion's check flips when V(q) gains world 1.2.
5. **Planted bugs**, each of which must turn a test red:
   - evaluate the checks at a leaf instead of the root;
   - drop the closure edges in S4;
   - skip the `extractCountermodel` re-check (return a model from a
     budget-truncated branch).
6. **Agent walkthrough, as a substitute for students; informative, not
   blocking.**
   - A fresh-context reviewer (Fable) reads only the notebook section and
     follows its instructions as a Lean novice would.
   - An optional browser smoke test runs through `web/run-local.sh`
     (127.0.0.1 only, per CLAUDE.md) with a screenshot.
   - The known lean4web first-load bug (the infoview stuck on "No info
     found"; a reload fixes it) is noted, not fixed here.
   - Findings go into `docs/assessment/` as a dated record.

### Done when
All of the verification above passes, `lake build` and `lake test` pass,
`compare.py` shows 0 disagreements, the reviewer's findings are settled,
and the user approves the merge.

## Part B: soundness of the executable tableau for K

### The theorem (target statement)

```lean
-- Prop-level semantics, B&D Def. 1.6 (model) and 1.7 (truth at a world),
-- over an arbitrary world type: no finiteness, no TreeSet.
structure KModel (W : Type) where
  R : W → W → Prop
  V : Atom → W → Prop
def Sat {W} (M : KModel W) : W → Formula → Prop     -- K fragment

theorem buildTableau_sound {n : Nat} {Γ : List PrefixedFormula}
    (hK : ∀ pf ∈ Γ, pf.formula.IsBasicModal)
    (h : buildTableau systemK n Γ = .closed) : ¬ Satisfiable Γ
                                                  -- B&D Def. 6.4, Thm 6.6

theorem tableauProves_sound (h : tableauProves systemK n Γ A = .definitely true)
    (hK : …) : ∀ {W} (M : KModel W) (w : W), (∀ φ ∈ Γ, Sat M w φ) → Sat M w A
                                                  -- B&D Cor. 6.7
```

- `IsBasicModal` is the K fragment: ⊥, atoms, ¬, ∧, ∨, →, ↔, □, ◇. It is
  closed under the rules' subformulas, so the temporal rules in
  `tryPriority1` never fire.
- `Satisfiable` follows B&D Defs. 6.3–6.4 (pp. 98–99): an interpretation
  f of the prefixes, with R f(σ) f(σ.n) whenever both σ and σ.n are used.
- **Why prove it about `buildTableau` itself:** the payoff is that the
  program students and `gamen-validate` run is the one proved sound, not
  an idealized copy.

### Milestones (each merges only when it is `sorry`-free)

- **B0. Spike on the order instances. Do this first; it decides the cost
  of everything else.**
  - `Branch.isClosed` and `contains` go through `Std.TreeSet`, whose
    membership lemmas (`contains_insert`, `mem_ofList`, …) need lawful
    comparison (`Std.TransCmp`, `LawfulEqCmp`) for the *derived* `Ord` on
    `Formula` (30 constructors), `Prefix` and `PrefixedFormula`.
  - Find out what Lean 4.34 gives for derived `Ord` instances. If the
    proofs are cheap (a derive handler, or a generic tactic), take them.
  - **Fallback:** don't change the order. Prove one direction only,
    `members.contains pf → pf ∈ formulas.toList`, from a branch invariant.
  - **Last resort, which needs the user's approval:** replace the derived
    `Ord` with a proved-lawful one. This changes `TreeSet` iteration
    order, so it risks wire output; it must pass `compare.py` byte for
    byte and the slow property tests.
- **B1. Semantics and adequacy.**
  - Define `KModel`, `Sat`, `IsBasicModal` and `Satisfiable` in a new
    `Gamen/Proofs/` directory, which has no gamen-hs counterpart.
  - Optionally prove adequacy: for a finite `Model` and a world in it,
    `satisfies m w φ = .ok b ↔ (Sat (toKModel m) w φ ↔ b = true)` on the
    K fragment. That links the notebooks' `native_decide` answers to the
    Prop semantics. Worth doing, but it isn't on the critical path.
- **B2. Branch invariants.**
  - `members` and `prefixes` agree with `formulas`, and every
    constructor/`append`/`addUnique` preserves that.
  - `freshPrefix` really is fresh. The `find?` case is direct. The `getD`
    fallback case needs a pigeonhole lemma (`prefixes.size + 1` distinct
    candidates), or a rewrite that makes the bound structural, with
    identical results and a property test.
- **B3. Closure.** B&D Prop. 6.5 (p. 99) is the `σ T A ∧ σ F A` case. The
  `σ T ⊥` case follows from `Sat` (the code's extra condition, which
  gamen-hs has and B&D does not).
- **B4. Rule soundness.** This is the case analysis in B&D Thm. 6.6's
  proof (pp. 99–102):
  - for every `RuleResult` from `propositionalRule`, `boxTrueRule`,
    `boxFalseRule`, `diamondTrueRule` and `diamondFalseRule`, if the branch
    is satisfiable then so is `stack` (all additions), or so is one side
    of `split`;
  - □F and ◇T extend f to the fresh prefix, using B2.
- **B5. Passes and the driver.**
  - `applyAllRules sys b` returns branches each of which is `b` extended
    by one justified rule application, or `[b]`.
  - `buildTableau.go` keeps the invariant "if Γ is satisfiable, some branch
    in the list is satisfiable". A `.closed` result therefore contradicts B3.
  - The passes are `Id.run do` loops with `continue` and early `return`,
    and `formulas[i]!`. If reasoning about them directly is too costly,
    rewrite them as structurally recursive functions *with identical
    results*. This is CLAUDE.md's termination rule applied to proofs: add
    a property test that the old and new passes agree, then run
    `compare.py` (0 disagreements) and `lake exe slowtests`.
  - The `expanded`/`scanStart` fields only affect which rule fires next,
    so soundness should not depend on them. Keep them abstract.
- **B6. Corollaries and the axiom audit.**
  - Prove `tableauProves_sound` (B&D Cor. 6.7, and Cor. 6.8 for the
    premise-free case).
  - Add a test that fails if `#print axioms tableauProves_sound` mentions
    anything beyond `propext`, `Classical.choice` and `Quot.sound`. In
    particular this rejects `sorryAx` and `native_decide`. (At Lean 4.34,
    `native_decide` adds a per-theorem axiom named
    `<thm>._native.native_decide.ax_…`, not `Lean.ofReduceBool`, so the
    check must be an allowlist; a blocklist on `ofReduceBool` misses it.
    Checked 2026-09-29.)
- **B7. Later, not part of this plan's "done":**
  - Extend to KT, KD, KB, K4, S4 and S5 by frame class: B&D Props.
    6.10–6.14 (pp. 103–105) and Cor. 6.15 (p. 106). S5 in the code adds B□
    and B◇ beyond Table 6.4; they are sound for symmetric frames (Prop.
    6.12), which S5 frames are.
  - Soundness of `extractCountermodel`, the completeness direction (Thm.
    6.19), is a separate project.

### Verification of the proofs

- **Planted bugs:** each must make the proof fail to compile, not just a
  test.
  - make `boxFalseRule` reuse an existing child instead of a fresh prefix;
  - make `isClosed` accept `σ T A` with `σ' F A` for σ ≠ σ';
  - drop the ⊥ from `IsBasicModal`'s closure argument.
- The `#print axioms` test from B6 runs in `lake test`.
- Proofs live in their own module, built by `lake build`, so that a
  broken proof breaks the build. If proof checking makes builds too slow,
  move them to a separate `lean_lib` that is still in the default targets.
- An independent reviewer (Opus, plus Fable for the milestones with the
  most proof in them) reads the theorem *statements* against B&D. The
  most likely serious error is proving the wrong statement: an
  interpretation condition that is too weak, or a `Sat` clause that
  disagrees with Def. 1.7.

### Done when
B0–B6 are merged `sorry`-free, the axiom audit passes, `compare.py` still
shows 0 disagreements, and `docs/assessment/` has a dated note with what
was proved, what was refactored (with the equivalence tests), and B0's
outcome.

## Part C: B&D citations that survive new editions

Background and evidence: `docs/assessment/bd-source-anchors-2026-09-29.md`.
In short:
- OpenLogic labels, written without the part tag, survived 2019 → 2026
  unchanged: 89 of 89 in normal modal logic.
- Only 106 of 226 numbered statements are labeled, and only 20 of 85
  definitions.
- Printed numbers depend on B&D's build tags, so they can't be computed
  from the source.

### Design

1. **Citation syntax.** Write the number, then an anchor in brackets:
   - labeled statements: `B&D Thm. 6.6 [tab:sou:thm:tableau-soundness]`,
     the label without its part tag;
   - unlabeled statements: `B&D Def. 6.3 [tab:sou, defn 1]`, the section
     plus the statement's position among statements of that kind in the
     section;
   - tables, figures and pages keep plain numbers, since OpenLogic doesn't
     label them consistently.
2. **Index: `notes/bd-citations.tsv`,** committed. It has one row per
   anchor we cite: anchor, kind, number and page in the pinned PDF, the
   first words of the statement, and the file:line locations that cite it.
3. **Tool: `tools/bd/citations.py`,** in Python like `compare.py`.
   - **`index`:** regenerates the TSV. It sparse-clones OpenLogic at the
     revision in `notes/bd-edition.md`, pulls each anchored statement's
     text, and finds it in `pdftotext -layout notes/bd-screen.pdf` by
     normalized text. Anything it can't match with confidence is printed
     for a human, never guessed.
   - **`check`:** every anchored citation in `Gamen/`, `Notebooks/`,
     `Tests/`, `Widgets/` and CLAUDE.md must have an index row whose kind
     and number agree. Any "B&D" line with a Def/Prop/Thm/… number but no
     anchor is reported. It exits nonzero on errors.
   - **`migrate NEW.pdf [--olp REV]`:** for each index row, finds the
     statement in the new edition, by label where there is one and by text
     otherwise. It reports moved, reworded and missing statements, and
     edits nothing.
4. **One-pass migration of existing citations.** Add anchors to the B&D
   citations already in the code (80-plus in 20 files). Where the number
   in the code is wrong, fix it against the PDF and list each fix in the
   commit message, as the porter does.
5. **Wire it in.** Add `python3 tools/bd/citations.py check` to CLAUDE.md's
   Build list, and to the module-porter's and module-reviewer's citation
   steps, next to the `pdftotext` instruction.

### Verification

- **Planted citations, each of which `check` must reject:**
  - a Def. 6.4 anchor labeled as 6.3;
  - "B&D Definition 2.1", which doesn't exist; gamen-hs's `FrameProperties.hs`
    had exactly this, per the stale-citation list in gamen-hs's
    `notes/bd-edition.md`;
  - a B&D number with no anchor.
- **`index` must reproduce known rows exactly:**
  - Thm. 6.6 on p. 99 (`tab:sou:thm:tableau-soundness`);
  - Defs. 6.3 and 6.4 on pp. 98–99;
  - Example 6.22 on p. 111;
  - Def. 1.6 and Def. 1.7, per CLAUDE.md.
- **`migrate` dry run:** run it with the pinned PDF as the "new" edition.
  Every row must come back unchanged. A real old edition isn't available
  locally, so this only tests the harness.

### Offer the labels upstream (ask the user first)

Once the index exists, it lists the unlabeled statements we cite. Draft a
pull request to `OpenLogicProject/OpenLogic` adding `\ollabel` to them,
following the existing naming (`defn:…`, `ex:…`). Opening it is
outward-facing, so the user decides.

### Watch for new editions (optional; the user decides)

A monthly scheduled check fetches the B&D PDF from bd.openlogicproject.org
and compares its SHA-256 with the pin. If it differs, it notifies the user
and runs nothing else. Move the pin only on purpose, before a teaching
term, in gamen-hs and gamen-lean together, using `migrate`'s report.

### Done when
`check` passes on `main`, every existing B&D citation has an anchor, the
planted citations are rejected, the known rows reproduce, and CLAUDE.md and
the agents run `check`.

## Order and models

- **Part C can go first, or at any time.** It is small and independent.
  Doing it before Part B means B's new citations are anchored from the
  start. Sonnet can build it; Opus reviews it.
- **Part A next.** It is short and stands on its own. Opus writes it,
  because the widget constraints are unforgiving; Opus reviews it, and the
  Fable agent walkthrough follows.
- **Part B can run alongside the Dcleg port**, since they share no files.
  The exception is a B5 rewrite of the passes in `Tableau.lean`: land that
  alone, and rerun `slowtests` afterward.
- Use Opus or Fable for Part B, one milestone per session. The next session
  starts from the last merged milestone and this plan.
- **Stop and ask the user** before:
  - B0's last resort (changing the `Ord` instances);
  - any change to `gamen-validate` output;
  - enlarging the widget canvas, which affects every existing notebook
    scenario.
