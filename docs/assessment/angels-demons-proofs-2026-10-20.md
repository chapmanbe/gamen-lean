# Angels and Demons §3-4: the proofs that can be run (2026-10-20)

Source: Catta, Galimullin & Mittelmann, AAMAS 2026, pp. 5-7 (Theorems 1-7), figures read from
rendered page images. Tests: `expressivityCases` and `qbfCases` in `Tests/AngelsDemons.lean`.

**Run against the checker (all pass):**
- Theorems 1-2 separating pairs. SDL ⋠ SCL: `⟨⟨1⟩⟩Xp` holds at s of 𝔐1 and fails at s of 𝔐2
  (Fig. 3, costs 1 vs 2). SCL ⋠ SDL and CTL ≺ SCL/SUL: `⟨⟨angel 1⟩⟩X[angel 0]X¬p`, and the
  competitive SUL formula `⟨[angel 1]⟩^0 X [⟨angel 0, demon 0⟩] X¬p`, hold at s of 𝔐3 and fail
  at 𝔐4. The translations SDL ≼ SUL, SCL ≼ SUL and Theorem 1's CTL embedding
  (`⟨[0,n]⟩ ≡ ⟨⟨n⟩⟩`, `⟨[n,0]⟩ ≡ angelic ⟨⟨n⟩⟩`, `⟨[0,0]⟩ ≡ ⟨⟨0⟩⟩`) hold on six models.
- Theorem 4 (SDL ⋠ OL): `⟨⟨1⟩⟩Fp` holds at s1 of 𝔐_{n+2} and fails at s1 of 𝔐_{n+3} (Fig. 4),
  for n = 1, 2, 3.
- Theorem 5's lower bound: the QBF-to-SDL reduction (p. 6) agrees with brute-force QBF truth on
  all 24 two-variable instances (both true and false ones) and 12 three-variable ones.

**Finding: the reduction's formula is mis-indexed as printed.** `φ := φ_n` with
`φ_k := [1]X(chosen_k → φ_{k-1})` (or `⟨1⟩X(chosen_k ∧ φ_{k-1})`) puts `Q_n` and `chosen_n`
outermost, so the demon's first move faces `chosen_n`, which cannot hold after one removal
(only one atom is decided). The reduction works with `Q_1`, `chosen_1` outermost and
`chosen_n` innermost; the printed order gives a definite wrong answer on some instance (tested).
Confidence: high that this is an indexing slip in the paper, since the corrected form agrees with
brute force on 36 instances and the printed one does not. Cost if wrong: none for the code.

**Not run, and why:** the "no formula of the other logic can distinguish them" halves of
Theorems 1-4 (bisimulation-style arguments, not computation); Theorem 6 (SCL PSPACE-hardness,
the proof is "omitted for brevity", sketch in the technical report [27], not local); Theorem 7
(SUL in EXPSPACE) and the algorithm's complexity bound (no computational content to test). The
Theorem 3/4 OL results need Obstruction Logic, which is not implemented here.
