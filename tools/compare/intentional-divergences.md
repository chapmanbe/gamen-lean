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

## dcleg-service (`compare_dcleg.py`)

The Lean `dcleg-service` (`DclegService.lean`, `Gamen/Service/*`) is
compared against gamen-hs's by `tools/compare/compare_dcleg.py`, which
labels each of these divergences itself (`div:<name>`) and counts anything
else as DISAGREE. Against gamen-hs `main` at `fd8b269` (its `dcleg-service`
binary built 2026-09-29 19:06), seed 20261006, 2026-10-06: 299 sessions,
3272 requests: 3109 identical, 5 equivalent (malformed-JSON messages), 22
`crash`, 125 `premises`, 2 `build-premises`, 8 `max_violations`, 1
`duplicate-key`, **0 DISAGREE**.

- **D1 `crash`: library errors are replies, not a dead process.** Where
  gamen-hs's evaluator calls `error` (`B_i` for an agent with no doxastic
  map, in a `sat`/`true_in`/`counterfactual` formula, or in the
  `self_awareness`/`intentional_awareness` checks for a turn-taker with no
  doxastic map), the Haskell process dies with no reply and the session is
  lost. Lean answers `{"code": "internal_error", "message": <the library's
  message>}` (the protocol note's code for a server-side failure) and keeps
  serving. Test: `extensionCases` in `Tests/DclegService.lean`.
- **D2 `premises`: the default premise function.** `build` applies
  `Gamen.Dcleg.withMovePremises`, which gamen-lean fixed on 2026-09-30
  (singleton premise at single-move vertices; premises at outcome vertices;
  `docs/dcleg-outcome-node-premises-2026-09-30.md`). Answers that depend on
  F differ: `counterfactual` at an outcome vertex or a single-move vertex
  reached by more than one world (gamen-hs answers every counterfactual at an
  outcome vertex vacuously true), `sat`/`true_in` formulas containing a
  counterfactual, and the `centering`, `contemporary_universality` and
  `minimal_revision` axiom checks. The harness counts a `counterfactual`
  disagreement anywhere else as DISAGREE.
- **D3 `build-premises`: premise admissibility at `build`.** gamen-hs runs
  `validateDclegModel` before premises are applied; Lean's
  `validateDclegModel` also checks Centering and Contemporary Universality
  of F, so it runs after `withMovePremises`. A model whose histories
  disagree with the strategic structure (a world plays a move `moves` does
  not list, or stops at a non-end vertex) is now `model_invalid` with those
  violations; gamen-hs builds it. Test: `extensionCases`.
- **D4 `max_violations`: a cap ≤ 0 no longer reads as satisfied.**
  gamen-hs's `take maxV` leaves no violations, so it answers
  `"satisfied": true` for any model. Lean decides `satisfied` from whether a
  violation exists and caps only the list: `{"satisfied": false,
  "violations": []}`. Test: `extensionCases`.
- **D5 `duplicate-key`: repeated JSON keys.** aeson keeps the first of two
  equal keys, Lean's `Json.parse` the last (`{"id":"a","id":"b",…}` echoes
  `a` in gamen-hs, `b` here). Not fixed: it would take a JSON parser of our
  own; no caller sends duplicate keys.

Malformed JSON gets `parse_error` from both, with each JSON library's own
message; the harness counts these as equivalent, as `compare.py` does.
One known, unlisted edge: numbers are echoed only in a rejected `premises`
value (`details.received`), and Lean.Json does not keep how a number was
written, so an integer literal written out with more than 1024 trailing
zeros is echoed in exponent form (`1.0e1025`), where aeson writes the digits
(`Gamen.Service.encodeNumber`). Not in the harness corpus.

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
