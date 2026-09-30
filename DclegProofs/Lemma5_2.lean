import DclegProofs.Theorem5_1

/-!
# Lemma 5.2: (deep(z) ∧ F^zᵢ ∧ Bᵢ AX FutRat^zᵢ ∧ Ratᵢ) □→ CondRat^zᵢ is valid

**The result in plain words.** Section 5.5.2 considers replacing V^{y,z}ᵢ's
references to *past* rationality by a condition F^zᵢ about future
rationality only: for every move i could rationally make, i believes that
making it would leave every other player believing i will be rational from
then on. Lemma 5.2 says that, with this, rationality again forces
conditioned rationality:

> **Lemma 5.2** (p. 43). For any depth z ∈ ℕ, the following conditional
> is a validity of DCLEG: (deep(z) ∧ F^zᵢ ∧ Bᵢ AX FutRat^zᵢ ∧ Ratᵢ) □→ CondRat^zᵢ.
>
> The proof of this conditional's validity is similar to the proof
> presented for (V^{y,z}ᵢ ∧ Ratᵢ) □→ CondRat^zᵢ, but more streamlined …

**Status: partly formalized.** The claim is `claim_lemma5_2`. What the
Theorem 5.1 argument establishes when replayed here, the (m, k) disjunct
of CondRat^zᵢ for the move m actually made, is proved as
`lemma5_2_actual_move`. The ⋀_{m′} part, for moves other than m, is where
the argument stops, for the reasons given in `Theorem5_1.lean` and
repeated at the end of this file.
-/

namespace DclegProofs

open Formula
open Classical

noncomputable section

variable {Agent Move PVar : Type}

/-! ## F^zᵢ (p. 43)

> F^zᵢ := turnᵢ ∧ ⋀_{m′∈M} ( ¬◇(m ∧ Ratᵢ) ∨ Bᵢ(m′ □→ X ⋀_{j∈A∖i} Bⱼ FutRat^zᵢ) )

**QUESTION FOR JEREMIAH (Q18).** The bound variable is m′ but the ◇ disjunct
is printed with m. The Lean reads both as m′. -/

/-- F^zᵢ (p. 43). -/
def Fcond (sig : Signature Agent Move) (i : Agent) (z : Nat) : Formula Agent Move PVar :=
  turn i ∧'
  bigAnd (sig.moves.map fun m' =>
    ¬' (◇ (move m' ∧' Rat sig i)) ∨'
    bel i (move m' □→ next (bigAnd ((others sig i).map fun j => bel j (FutRat sig i z)))))

/-- Lemma 5.2, as a claim. -/
def claim_lemma5_2 (sig : Signature Agent Move) (PVar : Type) : Prop :=
  ∀ (i : Agent) (z : Nat),
    Valid sig ((deep z ∧' Fcond (PVar := PVar) sig i z ∧' bel i (AX sig (FutRat sig i z)) ∧' Rat sig i)
      □→ CondRat sig i z)

/-! ## The part that goes through: the actual move

Fix a pointed model (γ, w) on i's turn where i makes move m, and suppose
F^zᵢ, Bᵢ AX FutRat^zᵢ, Ratᵢ, and (from Ratᵢ, for some k)
Bᵢ(m □→ ⋁_{h≥k} hᵢ). Then the second conjunct of CondRat's (m, k) disjunct
holds: Bᵢ((m ∧ X B^E FutRat^zᵢ) □→ ⋁_{h≥k} hᵢ). The steps, each mapped to
the hand proof of Theorem 5.1 as adapted on p. 43:

1. Take μ ∈ ⊒ʷᵢ(γ). By Self-Awareness μ plays m. (Not in the hand proof;
   it is what makes the counterfactuals at μ collapse.)
2. "Bᵢ AX FutRat … gives us M, μ, w ⊩ m □→ X Bᵢ FutRat" (p. 41):
   `bel_next_of_bel_AX`, giving Bᵢ FutRat^zᵢ at (μ, w′).
3. F^zᵢ at m: ◇(m ∧ Ratᵢ) holds at γ (γ itself is a witness), so
   Bᵢ(m □→ X ⋀_{j≠i} Bⱼ FutRat^zᵢ); at μ the antecedent m is true, so
   ⋀_{j≠i} Bⱼ FutRat^zᵢ at (μ, w′). This is (5.1)–(5.3) with future in
   place of past rationality.
4. Together, B^E FutRat^zᵢ at (μ, w′), i.e. X B^E FutRat^zᵢ at (μ, w).
5. So the antecedent m ∧ X B^E FutRat^zᵢ is true at μ and the
   counterfactual collapses (`sat_cf_of_sat`) to ⋁_{h≥k} hᵢ at μ, which
   Bᵢ(m □→ ⋁_{h≥k} hᵢ) at γ supplies, again by collapse. The hand proof
   reaches (5.6) by cautious monotonicity instead; here it is not needed.

**Lean, as it comes up.** `rcases h with h₁ | h₂` splits a disjunction
into two cases. `by_cases h : P` splits on whether `P` holds. `absurd a b`
closes a goal from `a : P` and `b : ¬P`. -/

variable {Node World : Type} {sig : Signature Agent Move} {M : GameModel Agent Move Node World PVar sig}

/-- j ∈ A ∖ {i} exactly when j ≠ i. -/
theorem mem_others {i j : Agent} : j ∈ others sig i ↔ j ≠ i := by
  simp only [others, List.mem_filter, decide_eq_true_eq]
  exact ⟨fun h => h.2, fun h => ⟨sig.agents_complete j, h⟩⟩

theorem lemma5_2_actual_move {γ : World} {w w' : Node} {i : Agent} {m : Move} {k : Int} {z : Nat}
    (hγ : M.Reaches γ w) (hi : M.T.Q w = some i)
    (hm : M.MoveAt γ w m) (hnext : M.T.next w m = some w')
    (hF : sat M γ w (Fcond sig i z))
    (hAX : sat M γ w (bel i (AX sig (FutRat sig i z))))
    (hRat : sat M γ w (Rat sig i))
    (hRatk : sat M γ w (bel i (move m □→ payoffAtLeast sig k i))) :
    sat M γ w (bel i ((move m ∧' next (belE sig (FutRat sig i z))) □→ payoffAtLeast sig k i)) := by
  refine ⟨hγ, fun μ hμ => ?_⟩
  have hμr := dox_reaches hμ
  -- 1. μ plays m
  have hμm : M.MoveAt μ w m := (M.self_awareness i w γ hi μ hμ m).mpr hm
  -- 2. Bᵢ FutRat at (μ, w′)
  have hBi : sat M μ w' (bel i (FutRat sig i z)) := bel_next_of_bel_AX hi hm hnext hAX hμ
  -- 3. Bⱼ FutRat at (μ, w′) for j ≠ i, from F^zᵢ
  simp only [Fcond, sat_and, sat_bigAnd_map] at hF
  have hdia : sat M γ w (◇ (move m ∧' Rat sig i)) :=
    (sat_dia hγ).mpr ⟨γ, hγ, sat_and.mpr ⟨sat_move.mpr hm, hRat⟩⟩
  have hbel : sat M γ w (bel i (move m □→
      next (bigAnd ((others sig i).map fun j => bel j (FutRat sig i z))))) := by
    rcases hF.2 m (sig.moves_complete m) with hno | hbel
    · exact absurd hdia (sat_neg.mp hno)
    · exact hbel
  have hothers : ∀ j, j ≠ i → sat M μ w' (bel j (FutRat sig i z)) := by
    intro j hj
    have hcf := hbel.2 μ hμ
    have hX := (sat_cf_of_sat hμr (sat_move.mpr hμm)).mp hcf
    have hall := (sat_next_iff hμm hnext).mp hX
    exact sat_bigAnd_map.mp hall j (mem_others.mpr hj)
  -- 4. B^E FutRat at (μ, w′)
  have hBE : sat M μ w' (belE sig (FutRat sig i z)) := by
    rw [sat_belE]
    intro j
    by_cases hj : j = i
    · subst hj; exact hBi
    · exact hothers j hj
  -- 5. the antecedent is true at μ, so both counterfactuals collapse
  have hante : sat M μ w (move m ∧' next (belE sig (FutRat sig i z))) :=
    sat_and.mpr ⟨sat_move.mpr hμm, (sat_next_iff hμm hnext).mpr hBE⟩
  rw [sat_cf_of_sat hμr hante]
  exact (sat_cf_of_sat hμr (sat_move.mpr hμm)).mp (hRatk.2 μ hμ)

/-! ## What the formalization found

**Status.** The (m, k) part for the actual move is proved; the ⋀_{m′}
part is open, and with it the lemma.

1. **What the proof does not say.** `lemma5_2_actual_move` uses
   Self-Awareness (three times), Expectational Continuity, Transitivity,
   Euclideanness and Centering. The proof on p. 41, which p. 43 says to
   adapt, cites none of them; the sentence "This gives us
   M, μ, w ⊩ m □→ X Bᵢ FutRat^zᵢ" is where they are all needed.

2. **Where the argument stops.** For an available m′ ≠ m, CondRat's
   ⋀_{m′} conjunct needs one of: □¬m′ (false, m′ is available and by
   `H_covers` some world plays it); B̂ᵢ((m′ ∧ X B^E FutRat^zᵢ) □→
   ⋁_{h≤k} hᵢ); or ¬◇(m′ ∧ X B^E FutRat^zᵢ) ∧ B̂ᵢ(m′ □→ ⋁_{h≤k} hᵢ). Ratᵢ
   supplies B̂ᵢ(m′ □→ ⋁_{h≤k} hᵢ): some ν ∈ ⊒ʷᵢ(γ) with every world
   maximally m′-consistent with ν having payoff ≤ k. To get the middle
   disjunct from this one needs, at ν, m′ □→ X B^E FutRat^zᵢ (then cautious
   monotonicity, `maxConsistent_of_and_of_local`). F^zᵢ gives
   m′ □→ X ⋀_{j≠i} Bⱼ FutRat^zᵢ at ν when ◇(m′ ∧ Ratᵢ); the j = i
   component, m′ □→ X Bᵢ FutRat^zᵢ, is the step that `bel_next_of_bel_AX`
   provides only for m′ = m (see `Theorem5_1.lean`, item 2). And when
   ¬◇(m′ ∧ Ratᵢ), F^zᵢ gives nothing, and the third disjunct's
   ¬◇(m′ ∧ X B^E FutRat^zᵢ) has no visible source (item 1 there).

3. **Ratᵢ is transparent to i.** On i's turn Ratᵢ ↔ BᵢRatᵢ
   (`rat_imp_bel_rat`, `bel_rat_imp_rat`). This is what the future
   rationality needed in item 2 would have to be built from, one node at
   a time; it is not enough by itself, because FutRat^zᵢ at later nodes
   depends on i's beliefs there, which Minimal Revision ties to the
   beliefs of the *counterfactual* world's plausible set, not γ's.

So Lemma 5.2 stands or falls with the same inference as Theorem 5.1. If
that inference can be justified (perhaps by a strengthened F^zᵢ that
speaks of Bᵢ FutRat as well as Bⱼ for j ≠ i, or by an extra frame
condition), the rest of the proof is routine and the pieces here would
carry over. -/

end

end DclegProofs
