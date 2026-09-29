# Plan: logic for health informatics students, from truth tables to CQL's three-valued logic

*Written 2026-09-29. Read this once; implement against it. Nothing here
waits on student testing: none is available, so an agent does the
walkthrough. Most health informatics students have seen no formal logic, so
the module begins at truth tables.*

## Objective

Two notebooks, and a small library module behind them.

1. **A primer on classical propositional logic,** built on clinical rules:
   truth tables, validity and entailment, with no background assumed.
2. **Three-valued logic and missing data.** Strong Kleene logic is the
   logic of CQL and FHIRPath. The notebook contrasts it with weak Kleene,
   Łukasiewicz and designated-value (LP-style) logics, and shows where the
   "unknown" in clinical data changes answers students take for granted.

The payoff for the students: they'll understand why a quality-measure
criterion can evaluate to null, and what their query engine does with that.

## Verified facts this plan rests on (checked 2026-09-29)

- **CQL 2.0.0** (<https://cql.hl7.org/09-b-cqlreference.html>, "Logical
  Operators"):
  - `and` (Table 9‑A), `or`, `not`, `xor` and `implies` (Table 9‑A1) are
    strong Kleene, with `null` as the third value;
  - `implies`: "Otherwise, this operator returns true if the right operand
    evaluates to true, and null otherwise";
  - the spec doesn't name the logic.
- **FHIRPath 3.0.0** (<https://hl7.org/fhirpath/en/>, "Boolean logic"):
  - "The operators then use three-valued logic to propagate empty
    operands";
  - the tables for `and`, `or`, `not()`, `xor` and `implies` are strong
    Kleene, with the empty collection `{ }` as the third value;
  - implementations must not rely on short-circuit evaluation.
  - **An apparent inconsistency inside the spec:** the note under
    `implies` says "if the left side of an implies evaluates to empty, the
    result of the operation is the right side", but the table gives
    `{ } implies false = { }`, not `false`. Check whether HL7 errata or
    Jira already cover it before citing it anywhere. It makes a good
    exercise either way.
- **The OpenLogic Text at the pinned revision `0a18d37`,**
  `content/many-valued-logic/`:
  - `syntax-and-semantics` (`mvl:syn`): connectives, formulas, matrices,
    valuations, semantic notions, and many-valued logics as sublogics of
    classical logic;
  - `three-valued-logics` (`mvl:thr`): introduction; Kleene logics (`skl`,
    strong and weak/Bochvar); Łukasiewicz (`luk`); Gödel (`god`);
    "Designating not just T" (`mul`, e.g. LP);
  - `infinite-valued-logics` is out of scope.
- **B&D's appendix** (our pinned `notes/bd-screen.pdf`) imports OpenLogic's
  `propositional-logic/syntax-and-semantics`, so the primer can cite the
  PDF we already keep. Look up the appendix's letter and numbers when
  writing; don't guess them.
- **Not yet verified; check before stating it in a notebook:** how CQL
  treats a `null` condition at a query boundary (a `where` clause or a
  population criterion). The expectation is that only `true` is kept, so
  `null` behaves like `false` there, as SQL's `WHERE` treats UNKNOWN.
  Quote the spec section when you confirm it.

## Design

### Library: `Gamen/ManyValued.lean` (Lean-only; no gamen-hs counterpart)

- **Built for `decide` from the start.**
  - Truth values are small inductive types with `DecidableEq`: `TV3 | t |
    u | f`, plus `Bool` for classical logic.
  - Valuations are functions on a finite list of atoms.
  - Evaluation is plain structural recursion, with no `TreeSet`.

  So notebook claims can be checked by the kernel's `decide` rather than
  `native_decide`. That's a first for the project, and it is in line with
  Part B of `plans/countermodel-explorer-and-k-soundness-2026-09-29.md`.
- **Matrices, as in the OLT (`mvl:syn:mat`).** A logic is a matrix: truth
  values, designated values, and truth functions for ¬, ∧, ∨, → and ↔.
  Define `classical`, `strongKleene` (K3), `weakKleene` (Bochvar),
  `lukasiewicz3` (Ł3), `logicOfParadox` (LP: K3's tables with u
  designated) and `goedel3`. Take each table from the OLT section it cites
  and put an anchor in its docstring (Part C form, e.g.
  `[thr:skl, defn 1]`).
- **Formulas:** reuse `Gamen.Formula`'s propositional fragment.
  `eval (m : Matrix V) (v : Atom → V) : Formula → Except String V`
  throws on modal and other non-propositional operators, as elsewhere in
  the library.
- **Semantic notions (OLT `mvl:syn:sem`):** tautology (designated under
  every valuation) and entailment. Both are decidable by enumerating the
  3ⁿ valuations of the formula's atoms.

### Spec correspondence, as data (Buchanan's separation principle)

- `data/specs/cql-2.0.0-logical.json` and
  `data/specs/fhirpath-3.0.0-boolean.json` hold each operator's table
  transcribed from the spec, with its URL, version, section and table ID.
  They are authoritative sources, never LLM-derived.
- A test checks that each spec table equals the `strongKleene` matrix,
  mapping null or `{ }` to `u`.
- This makes "CQL's `and`, `or`, `not` and `implies` are strong Kleene" a
  checked claim, not a remark in prose. If a future spec version changes a
  table, the test fails.

### Notebook 1: `Notebooks/PropLogicPrimer.lean`

- **Audience:** no logic background.
- **Motivation first:** an eligibility rule ("age ≥ 65 ∧ diabetic →
  offer screening"), then the symbols.
- **Topics:**
  - atoms and connectives;
  - truth tables, as rendered HTML tables with `#eval` grading of filled-in
    rows;
  - tautology, contradiction and contingency;
  - validity and entailment, shown by exhaustive truth tables;
  - the material conditional's surprises, using clinical examples.
- **Citations:** B&D appendix numbers, anchored.
- **Every stated answer** goes into the answer-key tests (CLAUDE.md).

### Notebook 2: `Notebooks/ThreeValued.lean`

- **Missing data first:** a patient with no HbA1c on file, then
  "diabetic ∧ HbA1c > 9".
- **Topics:**
  - strong Kleene tables, and the fact that they agree with classical logic
    on {t, f};
  - **the key result:** every formula takes the value u when all its atoms
    are u, so K3 has *no* tautologies. `p ∨ ¬p` is not guaranteed true when
    data is missing. The clinical reading: "has the condition or doesn't"
    fails for a patient whose status is unknown;
  - weak Kleene: u is infectious, like an error;
  - Łukasiewicz: `u → u` is true, which restores `p → p`;
  - LP: designating u changes which inferences hold;
  - the correspondence with CQL and FHIRPath, checked against the spec
    tables;
  - where null collapses to false (only after the query-boundary fact
    above is verified);
  - the FHIRPath `implies` exercise (only after checking errata).
- **Exercises:** predict the value, then check it with `#eval`. Each
  exercise is "find a formula that…" or "which logic makes this
  entailment hold?".

### Interactivity

- Start with rendered HTML tables and `#eval` grading. Both work with the
  existing machinery, so no new widget is needed.
- A clickable truth-table widget is a later option. The KripkeExplorer
  constraint (the root RPC must be named `updateSvg`, so there is one
  explorer state type; CLAUDE.md) means it would have to extend
  `ExplorerState` into a sum type and rerun the widget tests. **Ask the
  user before doing that.**

## Theorems to prove (kernel-checked; small and teachable)

1. `strongKleene` agrees with `classical` on valuations into {t, f}: the
   classical fragment is preserved.
2. **No K3 tautologies:** for every formula, the all-u valuation evaluates
   it to u. The proof is induction on formulas, and it is simple enough to
   show students as an example of a proof about *all* formulas.
3. **Ł3 and K3 differ only in →:** the two matrices agree on ¬, ∧ and ∨,
   which `decide` checks over the tables.
4. **Optional:** LP's tautologies are exactly the classical ones.
   Property-test it first; prove it only if cheap.

`#print axioms` for each must be free of `Lean.ofReduceBool` (the Part B
audit, reused).

## Verification (automated; nothing waits on students)

- Answer-key tests for every stated answer in both notebooks.
- Spec-table tests, as above.
- Property tests (Plausible) over random propositional formulas:
  - K3 on classical valuations equals classical evaluation;
  - `eval` never throws on the propositional fragment;
  - entailment by enumeration matches a brute-force oracle.
- **Planted bugs, each of which must fail a test:**
  - make strong Kleene's `u ∧ f = u`;
  - swap Łukasiewicz's `u → u` to u;
  - designate only t in LP.
- **Novice walkthrough in place of students.** A fresh Fable agent is told
  it has no formal logic background and works through both notebooks in
  order. It reports every place it got lost, every undefined term and every
  exercise it couldn't start. Its findings go into `docs/assessment/` as a
  dated record. They inform revisions, but don't block the merge.
- Optional browser smoke test through `web/run-local.sh` (127.0.0.1 only).

## Order and models

- Start after the Atl.ImperfectInfo merge. This work can run alongside the
  Dcleg port and the countermodel plan's Parts A to C, since they share no
  files.
- Build the library and spec tests first, then Notebook 1, then Notebook 2.
- Opus writes it, because the pedagogy for true novices is the hard part.
  Opus reviews the code; the Fable novice walkthrough reviews the
  notebooks.
- **Stop and ask the user** before:
  - adding an interactive widget (the `ExplorerState` change);
  - raising the FHIRPath `implies` inconsistency with HL7 (outward-facing);
  - pinning a built OpenLogic Text PDF in `notes/`, which would be a second
    pinned book alongside B&D.

## Done when

- Both notebooks build.
- Every stated answer is in the answer-key tests.
- The spec-table tests pass.
- Theorems 1–3 are proved with a clean axiom audit.
- The planted bugs are caught.
- The novice walkthrough is recorded.
- The user approves the merge.
