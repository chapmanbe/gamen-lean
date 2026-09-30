# Novice walkthrough of the three-valued notebooks, 2026-09-30

A dated record. No students were available, so, as the plan requires
(`plans/three-valued-logic-2026-09-29.md`, "Verification"), a fresh Fable
agent stood in. It was told it had no formal logic background (a health
informatics graduate student who knows HbA1c and quality measures, a little
SQL, and no Lean), and it worked through both notebooks in order on
branch `three-valued-notebooks` at `ed9ffc6`. It filled in the exercises
on scratch copies and ran them with `lake env lean`, starting with its
first honest attempt. The findings inform revisions; they don't block the
merge. What changed in response is listed at the end.

## Notebook 1: `PropLogicPrimer.lean`

**Where it got lost**
- **Cy, in "which records comply?":** it wanted a third answer, "the rule
  doesn't apply". The grader's hint got it to T, but it accepted that only
  after the "surprises of →" section, which comes after the exercise.
- **`gradeColumn`'s hint** says "apply the table for the main
  connective", and "main connective" is defined nowhere.
- **`atomList f == [⟨"diabetic"⟩]`** in the `gradeFind` call: the
  brackets are unexplained noise.
- **"Use the `#html` line to draw a table":** nobody said the student may
  copy and edit such a line. Only 2 of the 4 entailment tables are
  provided.

**Terms used before they were defined:** "premises" (plain English carried
it), and "main connective" (in the grader only).

**Exercises:** all could be started, and every wrong first answer was fixed
by its hint.

**Lean syntax**
- `->` and `\/` are rejected inside `ml[ ]`.
- Nothing says that the editor turns `\and` into ∧.
- `some`, `none`, `Option` and `def … :=` are never explained.
- `#eval rule` adds parentheses, which looked like a mistake.
- `[true, false, …]` without `some` is accepted, by coercion, which trained
  the habit that fails in notebook 2.

**Clinical examples:** these landed: the screening rule, Dee, affirming the
consequent, and explosion as contradictory data. Answering the three "Why
bother" questions one by one was "the best part".

## Notebook 2: `ThreeValued.lean`

**Where it got lost**
- **`def bea : Atom → TV3 := …`:** the → in the type reads as the
  "if…then" just learned, and `Atom` and `TV3` are not introduced.
- **The `#check` theorem statements** (`isCore`, `Except.map`, `fun a =>`)
  were unreadable.
- **`classify strongKleene ml[ diabetic ∨ ¬diabetic ]` prints
  "contingent"**, although the column is t/u/t and never f. The primer
  defined contingent as "true in some rows and false in others". A real
  inconsistency: the helper means "satisfiable, not a tautology".
- **`keptBy`** is raw Lean, and the `{poorControl}` splice in `ml[ ]` is
  never explained.
- **The FHIRPath hint** says "both say the same thing" right after "two
  things that don't agree". It meant that the release and the CI build
  agree with each other, but it reads as a contradiction. The `#eval`
  after the hint has no caption.
- **follows2's hint**, "Which of the three are designated": the three
  what?
- **"Which logic?" tested reading, not understanding:** the answers are
  stated verbatim in the paragraphs just above.

**Terms used before they were defined:** `xor`; "designates" as a verb;
"induction on formulas" (defined inline, but dense).

**Lean syntax**
- `some u` → "Unknown identifier `u`".
- `some .U` is rejected.
- `some "u"` → a type mismatch.
- `[.t, .u, …]` without `some` → nine "Unknown constant `Option.t`"
  errors.
- `record .u [("diabetic", true)]` → the error points at `.u`.

**Clinical examples:** Bea's missing HbA1c and the "neither list" ledger
argument were "excellent", and CMS122 made the design choice real. The
four-logics section felt abstract. LP's screening reading helped; weak
Kleene's "error" reading did not connect to any record the student knew.

## Its top five changes, ranked

1. Define "main connective" in the primer, and point the column hint at
   it.
2. Add a "Lean you need" box at the top of the primer: `def`,
   `some`/`none`, the dot in `.t`, `some` on every list item, and `\and`
   becoming ∧.
3. Caption or hide the `#check` theorems.
4. Fix "contingent" for three values.
5. Explain `{…}` splicing and the `Atom → TV3` annotation where they first
   appear; rewrite the FHIRPath hint and caption its `#eval`.

## What changed in response

In the fix round, together with the blind code review's findings:

1. The primer now defines "main connective", right after formulas are
   built, and the column grader's hint refers to it.
2. The primer has a "Lean you need" box covering `def`, `Option`,
   `some`/`none`, `some` on every list item, backslash input, "`->` does
   not work", and "copy any `#html` line". The three-valued notebook
   explains the `Atom → TV3` annotation, the dot in `.u`, and the
   `{…}` splice.
3. Each `#check` has a plain-English caption that says the student need
   not read the statement, and glosses `isCore` and `ofBool`.
4. "Contingent" in three values is explained where `classify` first
   prints it: "designated in some rows but not all".
5. The FHIRPath hint was rewritten ("both … still contain this
   disagreement"), and its `#eval` is captioned. follows2's hint names the
   three formulas; `xor` is glossed; "designates" is defined.
6. "Which logic?" now asks about formulas that the prose does not answer:
   `¬(p ∧ ¬p)` in K3, `(p ∧ q) → p` in Ł3, `p ∨ ¬p` in weak Kleene, and
   `p → p` in LP.
7. Every exercise's formula is a named `def` next to its answer, and every
   entailment exercise has its table.

**Not changed:** in the primer, `[true, false]` still coerces to `Option`
without `some`. The box tells students to write `some`.
