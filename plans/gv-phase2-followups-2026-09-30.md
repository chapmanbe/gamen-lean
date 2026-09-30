# Implementation Plan: GV Phase 2 follow-ups
*Written 2026-09-30 at the close of the Phase 2 session. Read this once; implement against it.*

## Objective
Phase 2 (applicability under missing data) is **merged**: gamen-lean
`3f1127d` (`Gamen.ManyValued.Completion`, theorems 1–6) and the Lean
guideline-validation port `c6c0a54` (`validate-guidelines applicability`).
This plan covers what's left: (A) acting on Brian's review of the four
draft definitions, when he gives it, and (B) the deferred minor findings
from the reviews. Done when A is applied (if Brian has reviewed) and each B
item is fixed or explicitly dropped by Brian.

Background, read only if needed: spec
`docs/superpowers/specs/2026-09-30-gv-phase2-missing-data-design.md`;
executed plan `docs/superpowers/plans/2026-09-30-gv-phase2-missing-data.md`.

## Decisions (do not relitigate)
- K3 is the reported verdict, backed by an exact completion check — K3 matches CQL's null handling; the exact check measures over-warning.
- The parent plan's "possible ⇔ some but not all completions" is false; only one direction holds — K3 is sound, not complete (`p ∧ ¬p`).
- Hand-written patient fixtures, not simulation or C-CDA data — Brian, 2026-09-30.
- Definitions follow the cited source text, not the pipeline's `applies_when` paraphrase; differences are noted — domain knowledge from authoritative sources.
- Only Brian sets `"status": "approved"` — approval gate for paper use.
- Output is paper-ready only if every definition is approved **and** no condition in the data is undefined.
- The RASi conjunct of the potassium definition stays unless Brian drops it — the restriction's own text names RASi.
- Commit trailers name the model that actually wrote the commit.
- No `gamen-validate` protocol change for Phase 2 — the port calls gamen-lean as a library.

## Architecture
- gamen-lean `Gamen/ManyValued/Completion.lean` (+ `Tests/Completion.lean`): clinic-free theory.
- Port `data/applicability/{facts,conditions,patients}.json`: vocabulary, 4 draft definitions, 7 patients.
- Port `GuidelineValidation/Applicability.lean`: loading, `compileCond`, `assessAll`, `runApplicability`.
- Port `GVTests/Applicability.lean`: loading cases, hand answer key (`expectedStatus`; totals 36/64/40), CLI cases.
- Port `docs/applicability-definitions-review.md`: Brian's readable review sheet, with a sign-off table.

## Interfaces / contracts
Unchanged from the merged code. Approval edits one entry in `conditions.json`:
```json
"status": "approved", "approved_by": "<name>", "approved_on": "YYYY-MM-DD"
```

## Constraints
gamen-lean `CLAUDE.md` and the port's `CLAUDE.md` apply (no `sorry`, no
`partial def`, `Except` not `panic!`, allowlist axiom audits, never write
to the canonical repo, American English). `lake` is `~/.elan/bin/lake`.
The port depends on gamen-lean by path (`../../gamen-lean`), so it builds
against gamen-lean's **main checkout**: merge gamen-lean changes before
building the port.

## Non-goals / rejected alternatives
- Partially known facts ("stage G3 or G4") — out of scope for Phase 2.
- Defining the other ~540 condition slugs in the data — not needed for the 20 paper-mode conflicts; they would be quarantined as undefined.
- Editing the answer key to match code output — rework by hand from the definitions instead.
- Protocol extension for `gamen-validate` — Phase 6's decision.

## Open questions for the implementer
- [ ] Has Brian filled in the sign-off table in the port's `docs/applicability-definitions-review.md`? If not, skip Part A; don't approve anything yourself.
- [ ] Does Brian want the B items done now, or left until later? Ask if unclear.

## Task list (ordered)

### A. After Brian's review (only if he has reviewed)
1. For each definition he **approves**: set `status`, `approved_by`, `approved_on` in `data/applicability/conditions.json`.
2. For each he **changes**: edit the `definition` and `note`, rework `expectedStatus` and the totals in `GVTests/Applicability.lean` **by hand** first, then run `lake test`.
3. Record his decisions in the review sheet's sign-off table; commit.
4. If all four are approved, confirm that the real run prints no "not for paper use" banner, and that JSON `for_paper_use` is true. The clinician-sample gate still applies before any paper claim.

### B. Deferred minor findings (small; group into one or two commits per repo)
gamen-lean:
1. Move the generic helpers out of `Completion.lean`: `mapM_ok` to a shared util, and `mem_dedup` next to `dedup` in `ManyValued.lean`.
2. Add `LawfulBEq Atom` in `Formula.lean` (then retire `atom_eq_of_beq`). This touches a module everything imports: run `lake test`, `lake exe slowtests`, and `tools/compare/compare.py`.

Port:

3. Undefined-condition test: also assert that every remaining assessment's `appliesWhen != pKey`, and that the 16 remaining statuses equal the full run's.
4. Main answer-key run: assert `ar.undefined.isEmpty && ar.skipped == 0`.
5. Docstring on `assess`: pruning by `relevantConstraints` assumes `Patient.known` came from `knownAtoms`.
6. Doc comment: `Json.parse` keeps the last value when a patient's facts object repeats a key.
7. Test harness: catch exceptions per test group in `GVTests/Main.lean`, so one throwing group doesn't abort the rest.
8. Add a test that rec decode errors appear in the `applicability` output's skipped count (a recs fixture with one bad record).
9. Leave shared `parseFlags` as it is (other subcommands silently accept `--patients`, as with `--mode` before). Just note it.

## Suggested implementer model
Part A: Sonnet. It's data edits plus a hand re-derivation, and the hand
derivation is where silent errors hide, so don't drop to Haiku. Part B:
Sonnet for the port items. Use Opus for B2 (`LawfulBEq Atom`), which
touches the core `Formula` module, and have a separate reviewer check it.
