# DL-BET Theorems 1-2: what could be checked (2026-10-15)

Source: Liu & Lorini, PRIMA 2017 (`liu2017belief.pdf`), Defs 7-8 and Theorems 1-2 on pp. 13-16.

**The proofs are not in this paper.** Theorem 1 (L-BET sound and complete for ESMs) is stated with
"the proof can be found in the extended version of this paper [28]", an IRIT technical report
(Liu & Lorini, 2017) that is not local. Theorem 2 (DL-BET) is argued only in one sentence:
the reduction axioms and the rule RRE give, for any DL-BET formula, a provably equivalent
L-BET formula, so completeness follows from Theorem 1. Neither proof was read.

**What was checked instead:** the soundness half of Theorem 2. Every reduction axiom of Def 8
(announce, lose trust, rely on, assess; read off the page images, pp. 15-16) is a validity of
the implemented semantics on 120 random ESMs, for 3 agents, 3 antecedents φ and 8 consequents
ψ (atoms, negation, K, B, E, T, nested), including the α₁-α₅ case split for `[?_iφ]B_iψ`.
Tests: `reductionCases` in `Tests/EvidenceTrust.lean`.

**Finding: the paper's Red−E_{i,j} and Red−T_{i,j} are misprinted.** Page 15 prints
`[−_{i,j}φ]E_{i,j}ψ ↔ (E_{i,j}[−_{i,j}φ]ψ ∨ ¬K_i(φ ↔ [−_{i,j}φ]ψ))` (and the same for T).
With `∨` this is not valid: take ψ = φ propositional, so `[−]φ ≡ φ` and `¬K_i(φ ↔ φ)` is false;
the right side collapses to `E_{i,j}φ`, which can hold before the update, while the paper's own
validity (6) says `[−_{i,j}φ]¬E_{i,j}φ`. With `∧` it is valid, and it matches Def 4 (the
evidence set is removed exactly when ‖ψ‖ and ‖φ‖ coincide for `i`). The `∨` form fails on some
random ESM (tested), the `∧` form on none. Confidence: high that `∨` is a misprint; the cost
if wrong is none for the code, which implements Def 4, not the axiom.

**Also noted:** the reduction list for `[?_iφ]` prints the `E_{j,k}` axiom twice (a typo; the
second is presumably `K`/`T`, both tested), and the `T_{j,k}` axiom for `[!_iφ]` has no side
condition and holds for every `k`, including `k = i`.

**Not checked:** completeness (neither theorem), the L-BET axioms of Def 7 as validities (most are
covered by validities (1)-(11) and the frame conditions), and the extended report.
