# DL-BET: belief, evidence and trust (issue #3, item 4, first component)

*2026-10-14. Design for a faithful port of one component; the combination across
components is out of scope (see "Follow-up").*

## Goal

Port the logic **DL-BET** of Liu & Lorini, *Reasoning About Belief, Evidence and Trust in
a Multi-agent Setting*, PRIMA 2017 (local copy `~/Projects/Logic/Bergen/Bergen/lit/pdfs/liu2017belief.pdf`),
as a Lean library module and a Lean-only `gamen-validate` request. It models agents who
receive evidence from sources they trust, judge whether they have sufficient reason to
believe a claim, and revise beliefs accordingly. Conflicting sources (the paper's
Amazon-vs-RT example) leave the agent suspending judgment. That is the "discordance"
case of issue #3 item 4; combining this with Perrotin et al. (LORI 2019) and Hunter's
papers is research and is not attempted here.

Success: the paper's §2.4 example is reproduced exactly; Proposition 1 (updates preserve
the model class) and validities (1)-(11) hold as property tests; every definition number
cited is checked against the PDF; `lake build`, `lake test` pass; `compare.py` unchanged.

## Source corrections (read off the PDF page, not the text extract)

`pdftotext` drops overlines and slashes in this paper. Two definitions read differently from
the extract and **the PDF governs**:

- **C8** is `∅ ∉ C(i,j,v)` (extract: `∈`). It is what makes `¬T_{i,j}⊥` valid (footnote 1).
- **Def 5**'s guard is `M,w ⊨ K̂_i φ` ("φ is consistent with i's information"), not `K_i φ`.
  Validity (7) is `K̂_iφ → [+_{i,j}φ]T_{i,j}φ`.

Other definitions used (all read off the PDF): `E_i^{≥x}φ := ⋁_{|J|=x} ⋀_{j∈J} E_{i,j}φ`
(`J ⊆ Agt`, so it counts *source agents*, `i` included; `E_i^{≥0} := ⊤`, `E_i^{≥|Agt|+1} := ⊥`),
`E_i^xφ := E_i^{≥x}φ ∧ ¬E_i^{≥x+1}φ`, and
`R_iφ := ⋁_{x,x',x''∈Evd, y∈Qt, x>x', x/(x+x')≥y, x≥x''} (E_i^xφ ∧ E_i^{x'}¬φ ∧ type(i,x'',y))`.

## Approach

A self-contained module with its own formula type, as `DFormula` (ATL-D) and `SFormula`
(angels and demons) did. The 30-constructor `Formula` is not touched; no change to
tableau, fragment checks, printer or `Epistemic.lean`. Rejected: extending `Formula`
(every match changes, gamen-hs parity lost); encoding in `ActionModel` (the `E` and `T`
operators are neighbourhood modalities and the updates edit the neighbourhoods).

## Module `Gamen/EvidenceTrust.lean`

**Model (Def 1).** `n` worlds `0..n-1`; a set of worlds is a bitmask `Nat` (as in
`AngelsDemons`). Agents are indexed. Per agent `i`: `E i : Array Nat` (information set of each
world, as a mask), `D i : Array Nat` (belief set of each world), `T i : Array (Nat × Rat)`
(cautiousness `x`, quota `y`). Per ordered pair `(i,j)`: `S i j`, `C i j : Array (List Nat)` (the
sets of worlds, as masks, per world). Atoms: valuation `Array (List String)`. Equality of
evidence is equality of masks, so `‖φ‖_{i,w}` is `⟦φ⟧ &&& E i w`.

`mkESM` checks C1-C10 and returns `Except ESMError`, with the constraint's name in the
message: C1 equivalence (reflexive, symmetric, transitive), C2 `D i w ≠ 0`, C3 `D i w ⊆ E i w`,
C4 `D` constant on `E`-classes, C5/C6/C10 `S`, `C`, `T` constant on classes, C7 every
set in `C i j w` is `⊆ E i w`, C8 no set in `C i j w` is `0`, C9 `S i j w ⊆ C i j w`. Also:
quotas in `[1/2, 1]`, cautiousness in `0..|Agt|`.

**Formulas (`EFormula`).** `atom`, `bot`, `not`, `and`, `type i x y`, `knows i φ`, `believes i φ`,
`evidence i j φ`, `trust i j φ`, and four update forms that carry their continuation so the type
stays a plain inductive (no mutual): `announce i φ ψ` = `[!_iφ]ψ`, `loseTrust i j φ ψ` =
`[−_{i,j}φ]ψ`, `relyOn i j φ ψ` = `[+_{i,j}φ]ψ`, `assess i φ ψ` = `[?_iφ]ψ`. Derived: `or`, `implies`, `top`,
`hatK`, `hatB`, `atLeast i x φ` (`E_i^{≥x}`), `reason i φ` (`R_i`).

**Satisfaction (Def 2).** `sat : ESM → EFormula → Except String Nat` returns the mask of worlds
satisfying the formula. Updates build the new model from the old: `‖φ‖` is always taken in the
pre-update model (Defs 3-6), and `[α]ψ` is `sat (update M α) ψ`. Recursion is structural on the
formula (the model argument changes), so no fuel.

`R_iφ` is evaluated directly, not by expanding the disjunction: at `w`, with `T i w = (x'', y)`, let `x` =
number of agents `j` with `E_{i,j}φ`, `x'` = number with `E_{i,j}¬φ`; then `R_iφ` iff `x > x'`,
`x/(x+x') ≥ y`, `x ≥ x''`. A test checks this against the literal disjunction on small cases.

**Updates (Defs 3-6), exactly as printed.**
- `!_iφ`: for every `j`, `S(j,i,w) ∪= {‖φ‖_{j,w}}` where `M,w ⊨ T_{j,i}φ`. No truth precondition, unlike public
  announcement: `i` may announce a falsehood.
- `−_{i,j}φ`: remove `‖φ‖_{i,w}` from `S(i,j,w)` and from `C(i,j,w)`.
- `+_{i,j}φ`: add `‖φ‖_{i,w}` to `C(i,j,w)` where `M,w ⊨ K̂_iφ`.
- `?_iφ`: four cases on `R_iφ`/`R_i¬φ` and `B_i¬φ`/`B_iφ` (expansion keeps `D ∩ ‖·‖`; revision
  replaces `D` by `‖·‖`; else unchanged).

## Request `evidence_trust_check` (Lean-only, protocol 8)

```
{"action":"evidence_trust_check","model":{...},"formulas":[...],"worlds":[...]}
```
Model (class-based so C1, C4-C6, C10 hold by construction; the rest are checked):
`worlds`, `agents`, `valuation` (world → atoms); `knowledge` (agent → list of classes, each a list of
worlds; a world in no class is alone); `belief` (agent → list of `{"class": world, "worlds": [...]}`;
**required for every class** (no default), C2/C3 checked); `evidence` and `trust`
(agent → source → list of `{"class": world, "sets": [[worlds],...]}`; a class not listed has none);
`types` (agent → `[x, "y"]`, one type per agent; `"y"` an exact rational such as `"3/4"`).
`types` per agent rather than per class is a restriction of the JSON layer only; the library
supports a type per class. Unknown keys in a model, formula or object are `malformed_spec`
(the lesson of the `angels_demons_check` review).

Formulas (tree format): `atom`, `bot`, `top`, `not`, `and`, `or`, `implies`, `type` (`agent`, `x`, `y`),
`knowledge`/`belief` (`agent`, `operand`), `evidence`/`trust` (`agent`, `source`, `operand`),
`reason` (`agent`, `operand`), `announce` (`agent`, `operand`, `then`), `lose_trust`/`rely_on`
(`agent`, `source`, `operand`, `then`), `assess` (`agent`, `operand`, `then`).

Reply, as `epistemic_check`: `{"worlds","results":[{"index","formula","satisfying","holds",
"true_in_model"} | {"index","error","error_code"}]}`. Request errors carry `error_code`:
`malformed_spec`, `unknown_world`, `unknown_agent`, `duplicate_world`, `duplicate_agent`,
`overlapping_classes`, `bad_rational`, and `violates_C2` / `C3` / `C7` / `C8` / `C9` plus
`bad_type` for the semantic constraints. Resource use is bounded: worlds ≤ 20 (masks over
`2^n` subsets are enumerated only through the formula's own sets), agents ≤ 8, `bad_size` otherwise.
Documented in `Validate.lean`; `Gamen/Protocol.lean` protocol 7 → 8.

## Testing

Every expected value comes from the paper or a hand derivation, not from the code under test.

1. **§2.4 example**, built by hand (worlds over `p`, `q`; four sources; chatbot type `(2, 1)`;
   `Hyp1 ∧ Hyp2 ∧ Hyp3`): `[!Amazon q][!RT ¬q][?chatbot q]` leaves `¬B q ∧ ¬B ¬q`;
   `[!Wikipedia p][!IMDb p][?chatbot p]B q` holds. Negative controls: one announcement fewer and the
   second claim fails; type `(1, 1)` and one source suffices.
2. **Validities (1)-(11)** on many small random ESMs (propositional φ, ψ), and the paper's stated
   counterexample `R_i(p ∧ ¬B_i p) → [?_i(p ∧ ¬B_i p)]B_i(p ∧ ¬B_i p)` as an invalid case.
3. **Proposition 1** as a property: for random ESMs and all four updates the result satisfies C1-C10.
4. `R_i` direct versus literal disjunction; `E_i^{≥x}` counts agents (a source counts once).
5. **Constructor**: one violating model per constraint, rejected with that constraint's name.
6. **Definition probes**: `!_iφ` with a false φ still adds evidence for a trusting listener;
   `+_{i,j}φ` is a no-op where `K̂_iφ` fails (the corrected guard); `−_{i,j}φ` removes from both `S` and `C`.
7. **Mutation checks**, planted one at a time, each must fail a test: `∪`↔`\` in Def 4; `K̂`→`K` in Def 5;
   expand/revise branches swapped in Def 6; `x ≥ x''` dropped from `R_i`; C8 as `∈`.
8. **Wire**: request round-trips, error codes, unknown keys, a bad rational, size limits.
9. Not tested and not claimed: soundness and completeness (Theorems 1-2); proofs not read.

After implementation: a fresh adversarial pass on a scrubbed copy (Fable + `agy`), recorded in
`docs/assessment/`.

## Out of scope

Perrotin, Lorini et al. group announcements and trust (LORI 2019); Hunter's trust-based belief
revision; any decision procedure or tableau for DL-BET; a notebook or widget. Not mirrored to gamen-hs;
papers are never committed.

## Follow-up

Draft a separate design issue on gamen-lean: how these components combine for "trust in a source's
classification, and discordance across sources" (the clinical use case), listing what is a plain port
and what is research.

## Sources

| Source | Status |
|---|---|
| Liu & Lorini, PRIMA 2017 (local PDF) | [VERIFIED] syntax and abbreviations (pp. 4-6), Defs 1-6 (pp. 6-9) read off the PDF page; §2.3 properties and §2.4 example read from the text extract (to be re-read from the PDF when tests are written); axiomatization and proofs **not read** |
| Perrotin et al. 2019, Hunter 2022-2026 | [ASSERTED] local PDFs, not read; out of scope |
