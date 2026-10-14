# Adversarial review of DL-BET and `evidence_trust_check`, 2026-10-14

Scope: `Gamen/EvidenceTrust.lean`, `Validate/EvidenceTrust.lean`, the `Core.lean` dispatch and both test
files. Reviewers: one Fable agent (given page images of the paper, because `pdftotext` drops overlines and
slashes) and Gemini through `agy -p` (extract only; told the extract drops overlines and slashes). Both
worked from a scrubbed copy (no plans, spec, `PORTING.md`, CLAUDE.md) and were told the author wrote code
and tests. Every finding was reproduced against the built binary before acting.

## What both reviewers confirmed independently

Defs 2-6, `R_i`, `E_i^{≥x}`, the validities and the §2.4 example agree with the PDF (both re-derived the
two example claims and the Moore counterexample by hand); C8 is `∅ ∉ C` and Def 5's guard is `K̂_iφ`
(both saw the extract is wrong there); C1-C10 are checked in the right direction.

## Real, fixed (each has a test that failed first)

| Finding | Found by |
|---|---|
| A typo in the request envelope (`world` for `worlds`) was ignored and reported every world; envelope keys are now checked | Fable |
| A missing `knowledge` entry made an agent omniscient (singleton classes); `knowledge` is now required for every agent | Fable, Gemini |
| A `type` formula outside the language (`x` above the agent count, quota outside [1/2, 1]) returned false; now `bad_type` | Fable |
| The random corpus might never exercise `R_i` or Def 6, making validities (3), (4), (8)-(11) and Proposition 1 vacuous; now counts (≥ 20 of 120 seeds each) and a hand-derived revision case (`R_i p ∧ B_i ¬p`) | Fable |
| `valid? == some false` passed if the formula failed at one world; now `sat? == some 0` | Fable |
| Quadratic normalization of a long `sets` list (22.7 s for 16000 sets, 1.4 MB); now `Sets.ofList` (3.0 s) and a cap of 2000 sets per entry (`bad_size`), because `validate` is quadratic in the sets | Fable |
| The `worlds` test claimed `true_in_model` was per world; it is one flag for the whole model; title fixed | Gemini |

## Not reproduced

Unbounded recursion or memory on deeply nested formulas: 20,000-deep `not` and 3,000-deep chains of
`announce`, `assess` and `lose_trust` on a 20-world, 8-agent model all answer normally (the existing
`check_consistency` is the one that hangs on deep `not`, which predates this work).

## Considered and not changed (rulings)

- `types` is per agent, not per class, on the wire (both reviewers): the spec's documented JSON
  restriction; the library supports `T` per class, so the `type` formula and `R_i` cannot distinguish
  classes over the wire. Extend `types` to per-class entries when a use needs it.
- An empty knowledge class `[]` is ignored, and a world named in no class is its own class (documented);
  harmless.
- C7 is checked within the world (`X ∈ C(i,j,w) → X ⊆ E_i(w)`); the printed condition has free `w, v` and
  read literally would force `C = ∅`. Now stated in the module docstring.
- `ESM.validate` compares `Sets` lists as given; a hand-built model with equal sets in a different order
  fails C5 (wire inputs are normalized, so unaffected).
- `holds` keys come out sorted, not in `worlds` order; an unknown formula type with extra keys reports the
  unknown key; duplicate JSON object keys are last-wins (a property of Lean's `Json`).
