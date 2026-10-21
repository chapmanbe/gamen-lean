# Knowledge Digest: gamen-lean, 2026-10-13 digest threads 5 through the paper proofs
*Written 2026-10-21 at the close of the session that worked through the 10-13 digest's open threads. Read this once; it is the state of that work. It is a handoff for choosing the next thread, not a draft brief.*

> **Kickoff:** Read `NEXT.md`, then this digest, then ask Brian which open thread to take. Do not re-open the settled decisions below. Do not cite Perrotin et al. (venue/year) until it is checked against the paper.

## Objective
Record the state after the issue #3 close-out and the verification and proof-running threads. Nothing is to be drafted.

## State in one paragraph
Everything is committed and pushed (`main` at `b61f572`). `lake test` passes 1579/1579. `tools/compare/compare.py` is unchanged at 103 DISAGREE (46 agree-with-notes, 0 new; deontic-STIT, documented). `gamen-validate` protocol is at 9. Issue #3 (items 1-4) is closed out; follow-up issue #4 (evidence-trust design) is open and linked from the #3 comment.

## What was done, in order
1. **DL-BET (issue #3 item 4):** merged `evidence-trust` into `main`, opened #4, committed the 10-13 digest, deleted the branch.
2. **[ASSERTED] sources verified** (`docs/assessment/source-verification-2026-10-15.md`). Unverifiable citations were softened in `Gamen/EvidenceTrust.lean` and `Gamen/ActionModel.lean`. Figure 1 edge costs were checked against the paper (addendum in the same record).
3. **Competitive SUL (Def 10):** the three coalitions `⟨[demon d]⟩^a`, `⟨[angel a]⟩^d`, `⟨[∅]⟩^{a,d}` implemented in `Gamen/AngelsDemons.lean` (protocol 9; wire types `update_demon`, `update_angel`, `update_none`).
4. **DL-BET Theorems 1-2:** proofs are in an IRIT technical report that is not local, so every reduction axiom of Def 8 was tested as a validity instead (`Tests/EvidenceTrust.lean`, `reductionCases`).
5. **Angels-and-demons proofs** (`docs/assessment/angels-demons-proofs-2026-10-20.md`): the Figure 3 and 4 separating models and the Theorem 5 QBF reduction, as tests.
6. **ATL-D proofs** (`docs/assessment/atl-d-proofs-2026-10-20.md`): Theorems 1-2 separating CGSs (`Tests/AtlDynamic.lean`) and the Theorem 6 3SAT reduction (`Tests/UpdateSearch.lean`).

## Decisions and framing (do not relitigate)
- **Reading A for competitive SUL:** each side's own move must be legal on its own, so every joint result is serial. The paper does not state this; Brian decided it on 2026-10-15. It is documented in the `Gamen/AngelsDemons.lean` module docstring. Evidence it matches the paper: Example 3's competitive claims hold under it.
- **Competitive coalitions are implemented by grouping** the existential side's choices, each with the set of universal-side replies. `pre` is ∃ group ∀ reply ∀ successor. Duals use the `negated` flag with `¬ψ` pushed through the temporal operators.
- **Lean-only extensions bump the protocol version.** Protocol 9 is current.
- **`docs/assessment/` entries are dated records:** add, don't rewrite.

## Findings about the papers
- **DL-BET Def 8:** the printed reduction axiom uses `∨`/`∧` where only the other connective is valid. A test shows the printed form is invalid. The Theorem 1-2 proofs themselves are unavailable.
- **Angels-and-demons Theorem 5 (QBF):** the paper's φ_n indexing has a slip; the construction works once corrected.
- **ATL-D Theorem 6 (3SAT):** the goal formula works as printed. No slip.
- ATL-D Theorems 1-2 separating CGSs behave as claimed.

## Test-quality lessons (reuse the method)
- Turn a paper's separating models and reductions into tests, plant a mutation, and confirm the test fails.
- Check instance nonvacuity. The Theorem 6 test first let a planted bug survive because every instance was satisfiable by a uniform assignment; `mixedOnly`/`mixedUnsat` instances plus a nonvacuity assertion fixed that.
- A wire test that only checks `isSome` cannot tell two request types apart; add a hand-derived discriminator.
- Random inclusion tests on arenas over 3 states only: larger arenas exceed the 20000 cap.

## Not run, and why
- The "no formula can distinguish" halves of both papers' separation theorems (bisimulation arguments).
- Theorems 5 and 7 of ATL-D and the complexity results of both papers (algorithm plus bound).
- SCL hardness (Theorem 6 of the angels-and-demons paper): sketch only, in an unavailable technical report.
- Obstruction Logic comparisons: OL is not implemented.
- The ATL-D⁻ hardness variant (one sentence in the paper).

## Open threads
- [ ] Read Perrotin et al. and Hunter for issue #4 (venue and year of Perrotin are marked unverified there).
- [ ] A notebook or widget for the action-model and angels-and-demons work. Needs a design conversation first (audience, which logics, notebook versus infoview widget, what gets graded).
- [ ] Obstruction Logic, which would allow the OL halves of Theorems 3-4 to be tested.

## Pitfalls hit this session
- macOS `sed -i` needs `''`, and `\b` is unsupported; use Python regex.
- `at` and `axiom` are Lean keywords; don't use them as identifiers.
- `S.and`/`S.top` don't resolve through the abbrev `S`; use `SFormula.and` etc.
- Wait loops using `pgrep -f "compare.py|lake build"` match the shell command text itself; read the task output file instead.
- `git push` over SSH fails inside the sandbox; Brian pushes with `! git push origin main`.

## Suggested next-session model
Sonnet is fine for the Perrotin/Hunter reading; the notebook design wants a design conversation with Brian first.
