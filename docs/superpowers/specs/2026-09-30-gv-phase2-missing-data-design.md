# Design: guideline-validation Phase 2, applicability under missing data

Date: 2026-09-30. Status: approved in conversation; awaiting spec review.
Parent plan: `plans/logic-for-guideline-validation-2026-09-29.md`, Phase 2.
Spans two repos: gamen-lean (theory) and `~/Projects/Logic/Lean/guideline-validation`
(the Lean port; clinical layer).

## Goal

For a patient whose data is incomplete, say whether each paper-mode conflict
is **definite**, **possible** or **absent**, by evaluating the conflict's
conditions in strong Kleene logic (K3), the logic CQL uses for `null`. Back
the K3 verdict with proofs of what it guarantees, and with an exact check
that measures how often "possible" over-warns.

## Decisions (Brian, 2026-09-30)

1. **Hand-written patient fixtures** for the first version, not simulation or
   C-CDA data.
2. **K3 verdict plus an exact check** (option A). K3 is reported because it
   matches CQL; the exact status comes from enumerating completions.
3. **Condition definitions drafted by Claude, approved by Brian.** Each
   carries its sources and `status: draft` until Brian approves it.
4. **Placement:** general theory in gamen-lean; clinical data and the
   consumer in the Lean port. No `gamen-validate` protocol change.

## Correction to the parent plan

The plan's third theorem, "possible ⇔ conflict in some completions but not
all," is false. K3 is sound but not complete: `p ∧ ¬p` with `p` unknown is
`u` (possible) but true in no completion. The same happens through fact
constraints (two CKD stages at once). What holds: definite ⇒ every
completion; absent ⇒ no completion; some-but-not-all ⇒ possible. A dated
note in the plan records this.

## Findings that shaped the design

- A `conditional` is an opaque slug (547 distinct in the canonical data,
  e.g. `ckd_g1_g4_a3_without_diabetes`). The port encodes it as a single atom
  (canonical mode) or ignores it (paper mode). K3 over opaque atoms is a
  lookup, so Phase 2 needs a **condition vocabulary**: each slug defined as a
  formula over patient facts.
- The 20 paper-mode conflicts (`test/golden/conflicts_stripped.json`) pair 4
  AHA recs from `blumenthal-2026_extracted.json` with 3 KDIGO restrictions.
  (Corrected 2026-09-30: an earlier survey looked the rec ids up in the KDIGO
  files, where the same ids name different recs.)
  - Only R18 has a `conditional`: `moderate_hypertriglyceridemia` ("In
    adults with fasting TG levels of 150 to 499 mg/dL …"). R16, R17 and
    R138 are unconditional.
  - Restrictions: `CKD G3-G5 (universal in this stage range)`,
    `hyperkalemia on renin-angiotensin system inhibitor therapy`,
    `hyperphosphatemia`.
  - So the vocabulary needs 4 definitions. KDIGO Rec 4.1.8 reads "In
    patients with CKD G3a–G5D … in the treatment of hyperphosphatemia," so
    the draft follows the cited source text, not the `applies_when`
    paraphrase, and notes the difference for Brian's review.
- With these definitions no real conflict pair can over-warn (no pair joins
  contradictory conditions). Over-warning is tested with synthetic formulas.

## Part 1: gamen-lean, `Gamen/ManyValued/Completion.lean`

Lean-only, no clinical content, built for `decide` like `Gamen.ManyValued`.
Uses `TV3`, `strongKleene`, `eval`, `isCore`, `strongKleene_agrees_classical`.

**Definitions**
- Partial valuation `p : Atom → TV3` (`u` = unknown).
- `c : Atom → Bool` *completes* `p` when for every atom
  `p a = .u ∨ p a = TV3.ofBool (c a)`.
- Constraint `exactlyOne : List Atom`. A completion is *admissible* when it
  satisfies every constraint.
- `k3Status f p : K3Status` (`definite | possible | absent`) from K3 `eval`
  giving `t | u | f`. Errors (non-core formula) stay `Except`.
- `exactStatus f p cs : ExactStatus` (`always | sometimes | never |
  noAdmissibleCompletion`) by enumerating admissible completions over the
  atoms of `f` and of the constraints. `noAdmissibleCompletion` (the known
  facts already violate a constraint) is a fixture error, never a verdict.

**Theorems** (kernel-checked, `isCore` formulas, allowlist axiom audit)
1. Monotonicity: refining unknowns never changes a `t` or `f` value.
2. `definite` ⇒ `f` true in every completion (hence every admissible one).
3. `absent` ⇒ `f` false in every completion.
4. True in some admissible completion and false in another ⇒ `possible`.
5. Converse fails: `by decide` witnesses `p ∧ ¬p`, and an `exactlyOne`
   witness, are `possible` and `never`.
6. `exactStatus` agrees with the quantified definitions over admissible
   completions.

**Tests:** `decide` checks on small cases; a Plausible property test that
`k3Status`/`exactStatus` never contradict theorems 2–4 on random formulas;
planted bug (flip one K3 table entry) caught.

**Out of scope:** partially known facts ("stage G3 or G4").

## Part 2: port data, `data/applicability/`

**`facts.json`**, the fact vocabulary:
- enumerated: `ckd_status ∈ {none, G1, G2, G3a, G3b, G4, G5}`,
  `fasting_tg ∈ {below_150, 150_to_499, 500_or_more}` (mg/dL),
  `age_group ∈ {child, adult}`. Each value is an atom (`ckd_status=G3a`);
  each enumerated fact yields an `exactlyOne` constraint. "Has CKD" is
  `ckd_status ≠ none`;
- boolean: `hyperkalemia`, `on_rasi`, `hyperphosphatemia`;
- each category system cites the KDIGO section defining it, checked against
  the KDIGO text, not memory.

**`conditions.json`**, keyed by the exact data string:
- `definition`: tree of `and`, `or`, `not`, `fact`, `in` (`in` compiles to a
  disjunction of value atoms);
- `sources`: the rec's verbatim text from the extracted data, and the KDIGO
  section;
- `status`: `draft | approved`, `approved_by`, `approved_on`. Only Brian sets
  `approved`.

**`patients.json`**, about 8 fixtures: `id`, `description`, `exercises` (the
case it tests), `facts` (known facts only; an absent fact is unknown). Every
conflict gets at least one definite, one absent and one possible result.

**Rules:** a rec with no `conditional` is `true`. A condition string missing
from `conditions.json` is quarantined as an undefined condition (listed, no
verdict). A fact value outside the vocabulary is a load-time `Except` error.

## Part 3: port code, CLI, output

**`GuidelineValidation/Applicability.lean`:** load and validate the data;
compile definitions to `Formula` and collect constraints; build a patient's
partial valuation (unlisted atoms `u`); for each (patient, conflict) evaluate
`recCondition ∧ restrictionCondition`, giving `k3Status`, `exactStatus` and
`disagree` (by theorems 2–3, only possible/never can disagree). Domain axioms
and bridge chains carry no condition.

**CLI:** new subcommand
`validate-guidelines applicability <recs.json> <axioms.json> [--patients <file>] [--mode …] [--agent-aware] [--json]`.
It runs conflict detection unchanged, then the new layer. `conflicts` is
untouched, so `test/golden/` parity stays byte-identical. `--patients`
defaults to `data/applicability/patients.json`.

**Output (text or JSON):** a banner with draft/approved definition counts
(any draft ⇒ "not for paper use"); per patient, each conflict with its
condition formula, K3 status and exact status; totals of definite, possible,
absent and disagreements; the undefined-condition list; provenance as in the
existing runs.

## Verification

- `GVTests/Applicability.lean`: an answer key of expected K3 and exact status
  for every patient × conflict, worked out by hand from the definitions
  before the code runs; loading errors (bad fact value, constraint-violating
  fixture, undefined condition); existing golden tests still pass.
- Planted bugs caught: `and`→`or` in the definition compiler; unlisted facts
  treated as false instead of `u`.
- gamen-lean: `lake test`. `slowtests` and `compare.py` not needed (no
  Tableau, Semantics or protocol changes).

## Process and gates

- Worktree branch per repo. gamen-lean Part 1 first, reviewed and merged,
  then the port.
- Opus implements; Fable reviews.
- No result goes into the paper until Brian approves the definitions and a
  clinician reads a sample (parent plan's gate). Nothing is written to the
  canonical repo.
