# Intentional divergences from gamen-hs's `gamen-validate`

gamen-lean has been the primary implementation since 2026-09-29, and fixes
bugs rather than copying them (CLAUDE.md, "Fix bugs here, don't copy them").
Existing request types must still match gamen-hs byte for byte, except for
the divergences listed here. `compare.py` disagreements that aren't listed
are regressions.

Each entry records:
- what differs, and for which requests;
- why Lean is right, citing a test or proof;
- the gamen-hs build compared against (branch and commit), since the answer
  depends on it;
- the `compare.py` count it explains.

## 1. Certified refutations in the deontic-STIT prover (gamen-hs#41)

- **What differs:** some deontic-STIT consistency requests. Lean answers
  `unknown` with reason `uncertified_refutation` where gamen-hs `main`
  answers `consistent`.
- **Why:** a G3DS refutation read off a saturated sequent is evidence of
  consistency only if its countermodel passes a re-check. Without that
  certificate, "consistent" can be wrong (gamen-hs#41). Lean follows the fix
  on gamen-hs branch `fix/41-certified-refutation` (commit `483c463`, PR
  #44). See `proveCases` in `Tests/Main.lean`, the "Issue #41" block.
- **Against which build:**
  - gamen-hs `fix/41-certified-refutation`: 0 disagreements. Every port
    before 2026-09-29 evening was compared against this build. *Historical:*
    that branch lacks gamen-hs `2fba336` (#60), so since gamen-lean#1 the
    flat-format requests with an unknown `op` or `temporal_op` (section C)
    disagree against it too. Compare against gamen-hs `main`.
  - gamen-hs `fix/53-dcleg-counterfactual-validities`, which lacks `483c463`
    and was built 2026-09-29 18:27: **103 DISAGREE**, all of them this case.
    (`compare.py` seed 20260923; 4731 requests: 4614 identical, 14
    equivalent, 0 scope gaps, 103 disagreements.)
  - gamen-hs `main` at `fd8b269`, compared 2026-09-30: **103 DISAGREE**,
    all of them this case. (4731 requests: 4582 identical, 46 equivalent, 0
    scope gaps, 103 disagreements.) See "Comparison log" below.
- **Status:** intentional. PR #44 is still open on gamen-hs. If it merges,
  this divergence disappears against gamen-hs `main`.

## Comparison log

Notable `compare.py` runs that are not divergences, kept so a later count
can be explained.

- **2026-09-30, gamen-hs `main` at `fd8b269`** (after gamen-hs merged #57,
  #58, #61 and #63 on 2026-09-29 evening). Before gamen-lean#1, section C
  (flat format) had 64 disagreements: gamen-hs#60 had made unknown flat
  `op`/`temporal_op` values parse errors, and gamen-lean still guessed.
  That was a gamen-lean bug. After gamen-lean#1 ported the fix, section C
  has 0, and the only disagreements left are divergence #1's 103.

## Adding an entry

Add one when a Lean bug fix changes `gamen-validate` output for an existing
request type. Include the `compare.py` counts before and after, and say which
gamen-hs build they were measured against.
