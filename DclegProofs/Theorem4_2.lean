import DclegProofs.Lemma4_1

/-!
# Theorem 4.2: R^z □→ BI_z is valid

**The result in plain words.** Chapter 4 looks for a belief condition
that guarantees backward induction. `Ratᵢ` (p. 29) says player i's current
move is not irrational given i's beliefs, and R^z (p. 31) says, roughly,
that everyone believes everyone is rational now, that this will keep
holding after any move, and that backward-induction continuations are
considered plausible. Theorem 4.2 says the condition works:

> **Theorem 4.2** (p. 31). For any depth z ∈ ℕ, the following is a
> validity of DCLEG: R^z □→ BI_z.

**Status: partly formalized.** Definitions complete; the base case z = 0
is proved (`theorem4_2_zero`); the full claim is `claim_theorem4_2`; the
inductive step is open. Several facts the inductive step relies on are
proved here as tools, and the closing section lists what the step needs
beyond them, including two places where the hand proof's justification is
not the one that works.

By `valid_cf_iff` (`Basics.lean`), "R^z □→ BI_z is valid" is the same as
"at every pointed model, R^z implies BI_z." The closing paragraph of the
hand proof (p. 33: "Suppose M, γ, w ⊮ R^{n+1} …") is that equivalence,
argued by hand; it is not needed separately.
-/

namespace DclegProofs

open Formula

variable {Agent Move PVar : Type}

/-! ## Ratᵢ (p. 29)

> Ratᵢ := ¬turnᵢ ∨ ⋁_{m∈M} ⋁_{k∈N} ( m ∧ Bᵢ(m □→ ⋁_{h∈N:h≥k} hᵢ)
>          ∧ ⋀_{m′∈M} ( □¬m′ ∨ B̂ᵢ(m′ □→ ⋁_{h∈N:h≤k} hᵢ) ) )

The grouping follows (4.15) on p. 33 and (5.4) on p. 41, where the same
formula is written out: Bᵢ applies to the whole counterfactual
m □→ ⋁ hᵢ, and the conjunct m stands outside it. -/

/-- Ratᵢ (p. 29). -/
def Rat (sig : Signature Agent Move) (i : Agent) : Formula Agent Move PVar :=
  ¬' (turn i) ∨'
  bigOr (sig.moves.map fun m => bigOr (sig.payoffs.map fun k =>
    move m ∧'
    bel i (move m □→ payoffAtLeast sig k i) ∧'
    bigAnd (sig.moves.map fun m' =>
      □ (¬' (move m')) ∨' dbel i (move m' □→ payoffAtMost sig k i))))

/-! ## R^z (p. 31)

> R⁰ := end
>
> R^{z+1} := B^E ( ⋀_{a∈A} Rat_a ∧ AX ⋁_{0≤z′≤z} R^{z′}
>                ∧ ⋁_{m∈M} (◇m ∧ (m □→ X R^z))
>                ∧ ⋀_{a∈A} ⋀_{m∈M} ⋀_{k∈N} ( ¬◇(m ∧ X ⋁_{0≤z′≤z} BI_{z′} ∧ k_a)
>                                            ∨ B̂_a(m □→ k_a) ) )

As with BI_z, the pair (R^z, ⋁_{z′≤z} R^{z′}) is computed together. -/

/-- The body of R^{z+1}, given `r` = R^z, `u` = ⋁_{z′≤z} R^{z′}, and z. -/
def Rbody (sig : Signature Agent Move) (z : Nat) (r u : Formula Agent Move PVar) :
    Formula Agent Move PVar :=
  belE sig (
    bigAnd (sig.agents.map fun a => Rat sig a) ∧'
    AX sig u ∧'
    bigOr (sig.moves.map fun m => ◇ (move m) ∧' (move m □→ next r)) ∧'
    bigAnd (sig.agents.map fun a => bigAnd (sig.moves.map fun m => bigAnd (sig.payoffs.map fun k =>
      ¬' (◇ (move m ∧' next (BIupto sig z) ∧' payoff k a)) ∨' dbel a (move m □→ payoff k a)))))

/-- (R^z, ⋁_{0≤z′≤z} R^{z′}). -/
def Rpair (sig : Signature Agent Move) : Nat → Formula Agent Move PVar × Formula Agent Move PVar
  | 0 => («end», «end»)
  | z + 1 =>
      let r := Rbody sig z (Rpair sig z).1 (Rpair sig z).2
      (r, (Rpair sig z).2 ∨' r)

/-- R^z (p. 31). -/
def R (sig : Signature Agent Move) (z : Nat) : Formula Agent Move PVar := (Rpair sig z).1

/-- ⋁_{0≤z′≤z} R^{z′}. -/
def Rupto (sig : Signature Agent Move) (z : Nat) : Formula Agent Move PVar := (Rpair sig z).2

/-! ## The statement -/

/-- Theorem 4.2, as a claim: for every depth z, R^z □→ BI_z is valid. -/
def claim_theorem4_2 (sig : Signature Agent Move) (PVar : Type) : Prop :=
  ∀ z : Nat, Valid sig (R (PVar := PVar) sig z □→ BI sig z)

/-! ## The base case, proved

> *Base Case: z = 0.* This is trivial, as the definitions of R⁰ and BI₀
> are the same. Clearly, if M, γ, w ⊩ R⁰, we must also have M, γ, w ⊩ BI₀.
> If M, γ, w ⊮ end, then we know that w ∉ EndV, and so the counterfactual
> will be satisfied vacuously. Hence, R⁰ □→ BI₀ is valid. (p. 32)

In Lean: R⁰ and BI₀ are both `end` *by definition*, so "R⁰ implies BI₀ at
every pointed model" is `fun … h => h`, and `valid_cf_of_imp` turns that
into validity of the counterfactual. The hand proof's second sentence (the
vacuous case) is the part `valid_cf_of_imp` absorbs: it is not needed,
because every maximally R⁰-consistent world satisfies R⁰. -/

variable {Node World : Type} {sig : Signature Agent Move} {M : GameModel Agent Move Node World PVar sig}

/-- Theorem 4.2 for z = 0. -/
theorem theorem4_2_zero : Valid sig (R (PVar := PVar) sig 0 □→ BI sig 0) :=
  valid_cf_of_imp (fun _ _ _ _ _ _ h => h)

/-! ## Tools the inductive step uses

The inductive step (pp. 32–33) is a chain of about fifteen inferences.
Those that are general facts about DCLEG are proved here, each named after
the phrase in the hand proof that invokes it. -/

/-- "Because BᵢBᵢφ □→ Bᵢφ is valid for every player i and formula φ"
(p. 32): B^E B^E ψ gives B^E ψ. Uses C4 for each agent. -/
theorem belE_belE_imp_belE {γ : World} {w : Node} {ψ : Formula Agent Move PVar}
    (h : sat M γ w (belE sig (belE sig ψ))) : sat M γ w (belE sig ψ) := by
  rw [sat_belE] at h ⊢
  intro i
  have hi := h i
  refine bel_C4 ⟨hi.1, fun μ hμ => ?_⟩
  exact (sat_belE.mp (hi.2 μ hμ)) i

/-- "By perfect information, we therefore know that M, γ, w ⊩ ◇X BIₙ"
(p. 32), from B^E ◇X BIₙ: `bel_dia_imp_dia` for any one agent. Needs at
least one agent in A. -/
theorem belE_dia_imp_dia {γ : World} {w : Node} {φ : Formula Agent Move PVar}
    (hγ : M.Reaches γ w) (i : Agent) (h : sat M γ w (belE sig (◇ φ))) : sat M γ w (◇ φ) :=
  bel_dia_imp_dia hγ (sat_belE.mp h i)

/-- On i's turn, Ratᵢ has the same value at γ and at every world i
considers plausible there. Every ingredient of Ratᵢ is invariant across
the cluster: the move (Self-Awareness), Bᵢ and B̂ᵢ (Transitivity and
Euclideanness), and □ (world-independence). This is what makes the last
inference of the inductive step ("This means that M, μ, w ⊮ Ratᵢ, and so
M, γ, w ⊮ BᵢRatᵢ," p. 33) go through: Ratᵢ fails at μ because its value
there is fixed by data μ shares with γ. -/
theorem sat_rat_of_dox {γ μ : World} {w : Node} {i : Agent}
    (hγ : M.Reaches γ w) (hi : M.T.Q w = some i) (hμ : M.dox i w γ μ) :
    sat M μ w (Rat sig i) ↔ sat M γ w (Rat sig i) := by
  have hμr := dox_reaches hμ
  simp only [Rat, sat_or, sat_neg, sat_turn, sat_move, sat_and, sat_bigOr_map, sat_bigAnd_map,
    sat_bel_of_dox hγ hμ, sat_dbel_of_dox hγ hμ, box_world_indep hμr hγ,
    M.self_awareness i w γ hi μ hμ]

/-- Ratᵢ → BᵢRatᵢ, at reached nodes. Off i's turn Ratᵢ is trivially
true everywhere; on i's turn use `sat_rat_of_dox`. -/
theorem rat_imp_bel_rat {γ : World} {w : Node} {i : Agent}
    (hγ : M.Reaches γ w) (h : sat M γ w (Rat sig i)) : sat M γ w (bel i (Rat sig i)) := by
  refine ⟨hγ, fun μ hμ => ?_⟩
  by_cases hi : M.T.Q w = some i
  · exact (sat_rat_of_dox hγ hi hμ).mpr h
  · exact Or.inl hi

/-- BᵢRatᵢ → Ratᵢ, at reached nodes (Present Seriality). -/
theorem bel_rat_imp_rat {γ : World} {w : Node} {i : Agent}
    (hγ : M.Reaches γ w) (h : sat M γ w (bel i (Rat sig i))) : sat M γ w (Rat sig i) := by
  by_cases hi : M.T.Q w = some i
  · obtain ⟨μ, hμ⟩ := M.present_seriality i w γ hγ
    exact (sat_rat_of_dox hγ hi hμ).mp (h.2 μ hμ)
  · exact Or.inl hi

/-! ## What the formalization found

**Status.** Base case proved; inductive step open. Reading pp. 32–33
against the definitions:

1. **"Note that, regardless of the value of z, R^z = B^E ψ for some
   formula ψ" (p. 32) is false for z = 0**, where R⁰ = end. The step it
   supports, from X ⋁_{z≤n} B^E R^z to X ⋁_{z≤n} R^z, still holds for the
   z = 0 disjunct, but by a different route: B^E end → end needs Present
   Seriality, the fact that `end` depends only on the node (`sat_end_iff`
   with `dox_reaches`), and A ≠ ∅ (B^E over an empty set of agents is ⊤,
   see `belE`), not C4. For z ≥ 1 the C4 route is `belE_belE_imp_belE`.

2. **"By perfect information, we have to have M, γ, w ⊩ X ⋁ B^E R^z"
   (p. 32)**, from X B^E ⋁ R^z. Moving a disjunction out of B^E is not a
   modal validity; it is justified here because R^z, for each z, can only
   hold at nodes of depth z (so at the fixed next node w′, only one
   disjunct is live in any world). That fact — *M, γ, w ⊩ R^z implies
   depth(w) = z* — is not stated in the thesis. It would be proved by
   induction: Present Seriality to get out from under B^E, then the
   conjunct AX ⋁_{z′≤z} R^{z′} to bound every successor's depth and the
   conjunct ⋁_m (◇m ∧ (m □→ X R^z)) to find a successor of depth exactly
   z. Both of those steps read a counterfactual m □→ X(…) at worlds that
   are maximally m-consistent, so they need such worlds to *exist* for
   each available m: that is the p. 22 argument, which under the literal
   definition of maximal consistency holds only for node-local premises
   (Q12; `exists_maxConsistent_of_dia`). So this lemma is missing from the
   thesis, and its proof depends on how Q12 is resolved. It is also the
   lemma that Lemma 4.1's inductive case needs (item 1 there).

3. **"Then clearly M, γ, w ⊩ B^E ◇X R^n" (p. 32)**, from
   B^E ⋁_m (◇m ∧ (m □→ X R^n)). This needs, at each plausible world μ,
   a world in max^m_{F(μ,w)}(Γ): that is the p. 22 argument from
   contemporary universality, which under the literal definition of
   maximal consistency requires premises to be node-local (Q12) and
   F(μ,w) finite (Q6); `exists_maxConsistent_of_dia` gives it under those
   assumptions.

4. **(4.16) → (4.17).** "M, μ, w ⊮ ¬◇(m ∧ kᵢ ∧ X ⋁BI)" uses that ◇ is
   world-independent (`box_world_indep`), since (4.11) established ◇(…) at
   γ, not μ; and moving B̂ᵢ(m □→ ⋁ hᵢ) from μ back to γ uses
   `sat_dbel_of_dox`. Both are fine.

5. **Typos, not gaps.** The sentence just before (4.18) writes
   "Bᵢ(m′ □→ ⋁_{0≤z≤n} R^z)"; from the AX conjunct of R^{n+1} what one has
   is Bᵢ(m′ □→ X ⋁ R^z), with an X, and (4.18) itself has the X. In (4.12)
   the displayed formula has "□¬m ∨ ◇(m ∧ …)" where the text around it
   (and (4.13)) has m′. On p. 33, "Take m′ ∈ PMoves(w) \ w" should read
   PMoves(w) \ {m}.

6. **(4.19) → "M, ν, w ⊩ ¬(m′ □→ ⋁_{h≤k} hᵢ)".** The proof takes η
   maximally m′-consistent with F(ν,w), notes η ⊩ X ⋁BI, and applies
   (4.19), a counterfactual with the *stronger* antecedent m′ ∧ X ⋁BI, to
   η. That is legitimate: a maximally m′-consistent world that also
   satisfies χ is maximally (m′ ∧ χ)-consistent, `maxConsistent_and_of_sat`
   in `Basics.lean`. It needs no extra assumption. (The text says
   "M, ν, w ⊩ X ⋁BI"; η is meant.)

7. **From (4.20) to "M, μ, w ⊮ Ratᵢ".** (4.20) lists the conjuncts for the
   specific k of (4.11), but Ratᵢ at μ is a disjunction over *all* k′ ∈ N.
   To refute it one needs: for every k′ for which Bᵢ(m □→ ⋁_{h≥k′} hᵢ)
   holds at μ, k′ ≤ k, and then B̂ᵢ(m′ □→ ⋁_{h≤k′} hᵢ) fails because
   ⋁_{h≤k′} entails ⋁_{h≤k}. The bound k′ ≤ k follows from
   B̂ᵢ(m □→ ⋁_{h≤k} hᵢ) via centering and Self-Awareness (all plausible
   worlds play m, so the counterfactuals collapse to payoff facts about
   them, `sat_cf_of_sat`). This is a real step, not written out.

8. **The closing paragraph** (case split on □¬R^{n+1}, contemporary
   universality) is unnecessary: `valid_cf_of_imp`.

Items 2 and 3 are the substantive ones. Item 2 needs a lemma the thesis
lacks, and both it and item 3 depend on how Q12 is resolved: under
node-local premises, `exists_maxConsistent_of_dia` supplies what they
need, and what remains is to write the lemma of item 2 down. -/

end DclegProofs
