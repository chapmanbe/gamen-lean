# Adversarial review of `angels_demons_check`, 2026-10-14

Scope: `Validate/AngelsDemons.lean`, `Tests/ValidateAngelsDemons.lean`, the dispatch in
`Validate/Core.lean`. Reviewers: one Fable agent and Gemini (`agy -p`), both on a scrubbed copy
(no plans, `PORTING.md`, CLAUDE.md, digests) plus a text extract of the paper, told the author
wrote code and tests. Gemini's first run was auto-denied (it asked for a shell command); the
retry said to use no tools. Each finding was reproduced against the built binary before acting.

## Real, fixed (each has a test)

| Finding | Found by |
|---|---|
| The `until`/`release` test compared `⟨⟨2⟩⟩(¬admin R ¬admin)` with `⟨⟨2⟩⟩G¬admin`; `p R p ≡ p` (Def 5, k = 0), so the sets agree by accident and the test passed with `until`/`release` swapped. Replaced by a budget-0 pair with different hand-derived sets ({s0,s2,s3} vs {s3}); verified it fails when swapped | both |
| Misspelled keys (`valuations`, `cost`, a stray `angel_bound`) were read as absent: every atom false, every cost 1. Unknown keys in a model, formula or path are now `malformed_spec` | Fable |
| A pair named twice in `costs` silently took the last entry (and could shadow a zero cost); a state listed twice in `states` was reported twice. Both now `malformed_spec` | both |
| `max_models` was unbounded, and `0` broke even bound-0 formulas with a misleading `check_failed`. Now 1..1000000 else `bad_max_models` | both |
| Docs cited Defs 2, 3 and 6 for the operators (they are Defs 4-5 SDL, 7-8 SCL, 10-11 SUL); the request description wrote `top`/`bot` as if bare strings | both |

## Not reproduced or not changed

- Both reviewers called unbounded `max_models` a memory/time blowup. It was not: 20000 returns in
  0 s, and 200000 and 1000000 on 5-6 state complete graphs return the cap error in under 1 s.
  Bounded anyway, as above.
- A non-numeric `max_models` (and similar wire-type errors in `parseRequest`) give a whole-request
  error without `error_code`, like every existing request; left as is.
- Duplicate edges are accepted; edges are a set, so this changes nothing.
- Each formula rebuilds its arena, so cost scales with the formula count; unchanged.
