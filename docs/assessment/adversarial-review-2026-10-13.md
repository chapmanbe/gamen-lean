# Adversarial review of the issue #3 work, 2026-10-13

Scope: commits `58aa079..8cec465` (atl_model_check and the Cgs codec, ATL-D/ATEL-D,
update search, social laws, DEL action models and `epistemic_check`, SDL/SCL/SUL).
Reviewers: four Fable agents (one per chunk) and Gemini through Antigravity (`agy -p`, four
chunks). Both worked from a scrubbed copy of the repository (no plans, no `PORTING.md`, no
CLAUDE.md) plus plain-text extracts of the source papers, and were told the author wrote
both the code and its tests. Gemini's headless mode auto-denies shell commands, so its prompts
inlined every file. Every finding was checked against the code (and, where it turned on the
paper, the paper) before acting; the ones I could reproduce were reproduced first.

## Real defects, now fixed (each has a regression test)

| Area | Finding | Found by |
|---|---|---|
| SUL | The demon's removal must leave a serial model on its own (paper fn. 2, Def 2); the code checked only the combined (removal ∪ addition) result, so `⟨[angel 1, demon 2]⟩X¬admin` held at s3 of 𝔐2 | Fable |
| SDL/SCL/SUL | A large budget enumerated every edge subset before the arena cap could fire (a hang, not an error) | Fable |
| SDL/SCL/SUL | `holdsAt` on a nonexistent state returned `false`; duplicate state names accepted; `index.getD x 0` silent default in arena construction | Fable, Gemini |
| ATL-D | Unknown agent in a coalition operator silently gave ∅ | Fable, Gemini |
| ATL-D | `semantics: perfect` on a model with indistinguishable states read `K_a` by them and `⟨⟨A⟩⟩` without them (a logic in neither paper); now `semantics_mismatch` | Fable |
| Protocol | `"dynamic": "true"` silently selected the static reader; empty update list accepted; `default_next` with both `stay` and `state` accepted | Fable |
| Codec | `[[s0,s0]]` passed the overlap check; empty indistinguishability class `[[]]` ignored; partial `indistinguishable` (epistemic) left worlds with no successors, so `K_b ⊥` held | Fable, Gemini |
| Action models | Name collision check covered only surviving pairs; a dead pair's name could resurrect an edge to a live world | Fable, Gemini |
| Action models | A builder's `group` was not checked against the agents (typo = nobody learns); `mkActionModel` itself gave a forgotten agent an empty relation | Fable, Gemini |
| Action models | Builder mixed with explicit fields silently ignored the explicit part; unknown agent in relations had the wrong error code; `holds` was `false` (now `null`) where an update could not run; ambiguity was reported for worlds the caller did not ask about | Fable, Gemini |
| Social laws | The `state:v` atoms of G⁺ were not checked for freshness | Fable, Gemini |
| Update search | Unknown state/pool action/agent reported as `search_failed`; unbounded `bound` allocated an array of that size; stale nodes re-expanded and overcounted | Fable, Gemini |

## Test weaknesses fixed

Duality tests that ran the same code on both sides now also check hand-derived values; the
random CTL cross-check now covers a budget-100 demon (EX/EF/EG) as well as budget 0 and was
restricted to 3-4 states for the big-angel case (5 states exceeds the arena cap, an error);
the semi-private cross-check against ATEL-D now has an outside agent; the public-announcement
product test checks relations and valuation; error-code tests check which error; every
`DFormula` constructor round-trips through the encoder/decoder; nested strategic operators
with non-zero budgets are tested with hand-derived expectations.

## Considered and not changed

* Repeated JSON object keys keep the last (Lean's parser). Protocol-wide and already
  documented (`tools/compare/intentional-divergences.md`, D5).
* A model without `default_next` is checked for completeness over the *available* joint moves
  only; a move enabled later by a grant is an error at that point (`checkSpecified`), not
  at load time. A deliberate choice, documented in `Validate.lean`.
* `trans` falls back to staying put for an unlisted joint move, but every evaluation path
  checks `specified` first, so the fallback is not reachable through `dsat`.
* Update search measures clauses, not the paper's number of updates (Def 7); documented.
* `implementConstraint` is the perfect-information definition and leaves `∼` alone; its
  docstring now says so.
* `{"type":"top"}` is not accepted by the dynamic decoder, as in the static one.
* The three competitive SUL coalitions are not implemented. The paper does not say what a
  joint move leaving a non-serial model means against a universal opponent, and Example 3
  uses them (`⟨[demon 2]⟩²`, `⟨[demon 2]⟩¹`). Gemini rated this high; it is a known, documented
  gap, and it needs a decision on that convention before it can be closed.

## Notes on the reviewers

Both reviewers independently found the chunk-B name collision, the unchecked group, and the
unknown coalition agent. Fable found the SUL legality defect and the hang, which Gemini missed;
Gemini found the `mkActionModel` gap, the empty class and the weak tests, which Fable missed.
Gemini's chunk A output opened with a long stream of leaked reasoning before the report.
