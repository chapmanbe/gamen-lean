# ATL-D (KR 2026, extended version): the proofs that can be run (2026-10-20)

Source: Galimullin, Grosinger & Mittelmann, *I Would If I Could*, extended version
(`galimullin2026iwiic-extended.pdf`): Theorems 1, 2, 5, 6, 7 and the appendix; figures read from
rendered page images. Tests: `separationCases` in `Tests/AtlDynamic.lean`, `reductionCases` in
`Tests/UpdateSearch.lean`. Theorems 3 and 4 were already differential tests.

**Run against the checker (all pass, no slip found):**
- Theorems 1-2 separating CGSs (Fig. 3). `[⊤ : β → {a}]⁺⟨⟨a⟩⟩X¬p` fails at v of 𝒢1 and holds at
  v of 𝒢2; `[⊤ : β → {a}]⁻⟨⟨a⟩⟩X¬p` fails at v of 𝒢3 and holds at v of 𝒢4 (α and β swapped);
  plain `⟨⟨a⟩⟩X¬p` has the same value in 𝒢3 and 𝒢4.
- Theorem 6's NP-hardness reduction (3SAT → bounded update existence, Fig. 6): the paper's
  example Ψ = (p1∨p2∨p3)∧(¬p1∨¬p3∨p4) with its update `[p2 : α → a, p4 : α → a]⁺`, and 20
  further instances (the unsatisfiable 8-clause one, an unsatisfiable one whose clauses are each
  satisfiable by a uniform assignment, three satisfiable only by a mixed true/false assignment,
  14 random), all agree with brute-force satisfiability. The search runs over the pool
  `p_l : α → a`, `p_l : β → a` (`notFound` is relative to the pool, so this tests the direction the
  proof relies on). The goal formula `φ_Ψ` works exactly as printed.

**Test-quality note:** a first version of the reduction test used only instances that an
all-true or all-false assignment satisfies, and a planted bug (a grant ignoring its condition,
which treats every atom alike) survived it. Instances needing a mixed assignment were added; the
bug is now caught.

**Not run:** the "no formula of the other logic can distinguish them" halves (bisimulation
arguments); Theorem 5 (P-completeness, an algorithm and a bound); Theorem 7 (ΔP₂ for ATEL-D);
the NP-hardness variant for ATL-D⁻ ("a modification of the proof", stated in one sentence).
