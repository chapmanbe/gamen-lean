import DclegProofs.Theorem4_2

/-!
# Theorem 5.1: (V^{y,z}ᵢ ∧ Ratᵢ) □→ CondRat^zᵢ is valid

**The result in plain words.** Chapter 5 adapts Gustafsson and
Rabinowicz's "conditioned dominance" as `CondRat^zᵢ` (p. 39): i's move is
rational on the supposition that, after it, everyone keeps believing i will
be rational in the future. Theorem 5.1 gives a belief condition V^{y,z}ᵢ
(p. 40) under which ordinary rationality forces conditioned rationality:

> **Theorem 5.1** (p. 40). For any height y ∈ ℕ and depth z ∈ ℕ, the
> following conditional is a validity of DCLEG: (V^{y,z}ᵢ ∧ Ratᵢ) □→ CondRat^zᵢ.

**Status: open.** All definitions are formalized and the claim is stated
(`claim_theorem5_1`). One step of the hand proof that is asserted without
justification is proved here as a tool, for the move actually made
(`bel_next_of_bel_AX`); the closing section explains why the same step is
not available for the other moves, and where that leaves the proof.

**Lean, as it comes up.** `noncomputable section` tells Lean that the
definitions below may use classical reasoning (here, to filter the agent
list by `j ≠ i` for an arbitrary type of agents) and need not be
executable. `open Classical` makes every proposition decidable for that
purpose.
-/

namespace DclegProofs

open Formula
open Classical

noncomputable section

variable {Agent Move PVar : Type}

/-! ## Height, depth, since, until (p. 38)

> high(0) := start          deep(0) := end
> high(n+1) := Y high(n)    deep(n+1) := ◇X deep(n)
>
> φ S₀ ψ := ψ                       φ U₀ ψ := ψ
> φ S_{n+1} ψ := ψ ∨ Y(φ ∧ φ Sₙ ψ)   φ U_{n+1} ψ := ψ ∨ (φ ∧ X φ U ψ)

**QUESTION FOR JEREMIAH (Q14).** In the printed U_{n+1} clause the index
on the inner U is missing ("X φUψ"). The Lean reads it as Uₙ, by symmetry
with S_{n+1}. -/

/-- high(y): the current node is at height y. -/
def high : Nat → Formula Agent Move PVar
  | 0 => start
  | n + 1 => prev (high n)

/-- deep(z): the current node is at depth z. -/
def deep : Nat → Formula Agent Move PVar
  | 0 => «end»
  | n + 1 => ◇ (next (deep n))

/-- φ Sₙ ψ, bounded since (`since` is not a legal Lean name, hence `bSince`). -/
def bSince (φ ψ : Formula Agent Move PVar) : Nat → Formula Agent Move PVar
  | 0 => ψ
  | n + 1 => ψ ∨' prev (φ ∧' bSince φ ψ n)

/-- φ Uₙ ψ, bounded until (Q14; `until` is a reserved word, hence `bUntil`). -/
def bUntil (φ ψ : Formula Agent Move PVar) : Nat → Formula Agent Move PVar
  | 0 => ψ
  | n + 1 => ψ ∨' (φ ∧' next (bUntil φ ψ n))

/-! ## Past and future rationality, conditioned rationality (p. 39)

> PastRat^yᵢ := Ratᵢ S_y start        FutRat^zᵢ := Ratᵢ U_z end
>
> CondRat^zᵢ := ¬turnᵢ ∨ ⋁_{m∈M} ⋁_{k∈N} ( mᵢ
>   ∧ Bᵢ((m ∧ X B^E FutRat^zᵢ) □→ ⋁_{h∈N:h≥k} hᵢ)
>   ∧ ⋀_{m′∈M} ( □¬m′ ∨ B̂ᵢ((m′ ∧ X B^E FutRat^zᵢ) □→ ⋁_{h∈N:h≤k} hᵢ)
>                ∨ (¬◇(m′ ∧ X B^E FutRat^zᵢ) ∧ B̂ᵢ(m′ □→ ⋁_{h∈N:h≤k} hᵢ)) ) )

**QUESTION FOR JEREMIAH (Q15).** The first disjunct under ⋀_{m′} is printed
"□¬m" (no prime); the Lean reads it as □¬m′, as in Ratᵢ. -/

/-- PastRat^yᵢ (p. 39). -/
def PastRat (sig : Signature Agent Move) (i : Agent) (y : Nat) : Formula Agent Move PVar :=
  bSince (Rat sig i) start y

/-- FutRat^zᵢ (p. 39). -/
def FutRat (sig : Signature Agent Move) (i : Agent) (z : Nat) : Formula Agent Move PVar :=
  bUntil (Rat sig i) «end» z

/-- CondRat^zᵢ (p. 39). -/
def CondRat (sig : Signature Agent Move) (i : Agent) (z : Nat) : Formula Agent Move PVar :=
  ¬' (turn i) ∨'
  bigOr (sig.moves.map fun m => bigOr (sig.payoffs.map fun k =>
    movei m i ∧'
    bel i ((move m ∧' next (belE sig (FutRat sig i z))) □→ payoffAtLeast sig k i) ∧'
    bigAnd (sig.moves.map fun m' =>
      □ (¬' (move m')) ∨'
      dbel i ((move m' ∧' next (belE sig (FutRat sig i z))) □→ payoffAtMost sig k i) ∨'
      (¬' (◇ (move m' ∧' next (belE sig (FutRat sig i z)))) ∧'
        dbel i (move m' □→ payoffAtMost sig k i)))))

/-! ## The condition V^{y,z}ᵢ (pp. 39–40)

> PF^{y,z}_{i,j} := (deep(z) ∧ Bⱼ PastRat^yᵢ) □→ FutRat^zᵢ
>
> P^{y,0}_{i,j} := Bⱼ PF^{y,0}_{i,j}
> P^{y,n+1}_{i,j} := Bⱼ PF^{y,n+1}_{i,j} ∧ AX ⋁_{0≤z≤n} (deep(z) ∧ P^{y+1,z}_{i,j})
>
> P^{y,z}ᵢ := ⋀_{j∈A} P^{y,z}_{i,j}
>
> H^yᵢ := turnᵢ ∧ ⋀_{m∈M} ( ¬◇(m ∧ Ratᵢ) ∨ Bᵢ(m □→ X ⋀_{j∈A∖{i}} Bⱼ PastRat^{y+1}ᵢ) )
>
> V^{y,z}ᵢ := high(y) ∧ deep(z) ∧ Bᵢ P^{y,z}ᵢ ∧ H^yᵢ ∧ Bᵢ AX FutRat^zᵢ

**QUESTION FOR JEREMIAH (Q16).** PF^{y,z}_{i,j} is printed with consequent
FutRat^zᵢ, but its use at (5.2) on p. 40 has consequent Bⱼ FutRat^{z′}ᵢ,
and the prose on p. 40 ("then j believes that i will not make any
irrational moves") matches the latter. The Lean follows the printed
definition. Which is intended? (With the printed form, Bⱼ PF and
Bⱼ(deep ∧ Bⱼ PastRat) give Bⱼ FutRat through Counterfactual K′ rather than
directly, so the difference is a step in the proof, not the truth of the
theorem.)

**QUESTION FOR JEREMIAH (Q17).** P^{y,z}ᵢ is printed as ⋀_{j∈A}, including
j = i, while the surrounding prose says "for every player other than i."
The Lean follows the formula. -/

/-- PF^{y,z}_{i,j} (p. 39), as printed (Q16). -/
def PF (sig : Signature Agent Move) (i j : Agent) (y z : Nat) : Formula Agent Move PVar :=
  (deep z ∧' bel j (PastRat sig i y)) □→ FutRat sig i z

/-- (P^{y,z}_{i,j}, ⋁_{0≤z′≤z} (deep(z′) ∧ P^{y,z′}_{i,j})), computed together.
Recursion is on z; the height y changes to y+1 in the AX conjunct. -/
def Ppair (sig : Signature Agent Move) (i j : Agent) :
    Nat → Nat → Formula Agent Move PVar × Formula Agent Move PVar
  | y, 0 =>
      let p := bel j (PF sig i j y 0)
      (p, deep 0 ∧' p)
  | y, n + 1 =>
      let p := bel j (PF sig i j y (n + 1)) ∧' AX sig (Ppair sig i j (y + 1) n).2
      (p, (Ppair sig i j y n).2 ∨' (deep (n + 1) ∧' p))

/-- P^{y,z}_{i,j} (p. 40). -/
def Pij (sig : Signature Agent Move) (i j : Agent) (y z : Nat) : Formula Agent Move PVar :=
  (Ppair sig i j y z).1

/-- P^{y,z}ᵢ := ⋀_{j∈A} P^{y,z}_{i,j} (Q17). -/
def Pall (sig : Signature Agent Move) (i : Agent) (y z : Nat) : Formula Agent Move PVar :=
  bigAnd (sig.agents.map fun j => Pij sig i j y z)

/-- A ∖ {i}, as a list. -/
def others (sig : Signature Agent Move) (i : Agent) : List Agent :=
  sig.agents.filter fun j => decide (j ≠ i)

/-- H^yᵢ (p. 40). -/
def Hcond (sig : Signature Agent Move) (i : Agent) (y : Nat) : Formula Agent Move PVar :=
  turn i ∧'
  bigAnd (sig.moves.map fun m =>
    ¬' (◇ (move m ∧' Rat sig i)) ∨'
    bel i (move m □→ next (bigAnd ((others sig i).map fun j => bel j (PastRat sig i (y + 1))))))

/-- V^{y,z}ᵢ (p. 40). -/
def Vcond (sig : Signature Agent Move) (i : Agent) (y z : Nat) : Formula Agent Move PVar :=
  high y ∧' deep z ∧' bel i (Pall sig i y z) ∧' Hcond sig i y ∧' bel i (AX sig (FutRat sig i z))

/-! ## The statement -/

/-- Theorem 5.1, as a claim. -/
def claim_theorem5_1 (sig : Signature Agent Move) (PVar : Type) : Prop :=
  ∀ (i : Agent) (y z : Nat),
    Valid sig ((Vcond (PVar := PVar) sig i y z ∧' Rat sig i) □→ CondRat sig i z)

/-! ## A tool: the step "this gives us M, μ, w ⊩ m □→ X Bᵢ FutRat^zᵢ"

Page 41: "We also know that M, γ, w ⊩ Bᵢ AX FutRat^zᵢ. This gives us
M, μ, w ⊩ m □→ X Bᵢ FutRat^zᵢ." No justification is offered. For the move
i actually makes, it holds, and the argument is worth writing out because
it uses three frame conditions the hand proof never names:

* Self-Awareness: every μ ∈ ⊒ʷᵢ(γ) makes the same move m as γ, so at μ the
  antecedent m is *true* and m □→ … collapses to … (centering,
  `sat_cf_of_sat`).
* Expectational Continuity: since all of ⊒ʷᵢ(μ) play m, i's plausible
  worlds at w′ = next(w, m) are the same as at w.
* Transitivity and Euclideanness: ⊒ʷᵢ(μ) = ⊒ʷᵢ(γ), so each δ ∈ ⊒ʷ′ᵢ(μ)
  satisfies AX FutRat at w, hence (playing m, by Self-Awareness again)
  FutRat at w′.

`bel_next_of_bel_AX` states this for an arbitrary φ in place of FutRat. -/

variable {Node World : Type} {sig : Signature Agent Move} {M : GameModel Agent Move Node World PVar sig}

/-- X φ holds at (γ, w) iff φ holds at the next node, which is unique. -/
theorem sat_next_iff {γ : World} {w w' : Node} {m : Move} {φ : Formula Agent Move PVar}
    (hm : M.MoveAt γ w m) (hnext : M.T.next w m = some w') :
    sat M γ w (next φ) ↔ sat M γ w' φ := by
  rw [sat_next]
  constructor
  · rintro ⟨m₁, w₁, hm₁, hn₁, h⟩
    have hm' := moveAt_unique hm hm₁
    subst hm'
    have hw' : w' = w₁ := Option.some.inj (hnext.symm.trans hn₁)
    subst hw'
    exact h
  · intro h
    exact ⟨m, w', hm, hnext, h⟩

/-- On i's turn, if i believes AX φ, then at every world i considers
plausible, i will believe φ after the move actually made. -/
theorem bel_next_of_bel_AX {γ μ : World} {w w' : Node} {m : Move} {i : Agent}
    {φ : Formula Agent Move PVar}
    (hi : M.T.Q w = some i) (hm : M.MoveAt γ w m) (hnext : M.T.next w m = some w')
    (h : sat M γ w (bel i (AX sig φ))) (hμ : M.dox i w γ μ) :
    sat M μ w' (bel i φ) := by
  have hμr := dox_reaches hμ
  have hμm : M.MoveAt μ w m := (M.self_awareness i w γ hi μ hμ m).mpr hm
  have hμw' : M.Reaches μ w' := reaches_next hμm hnext
  -- every world plausible for i at (μ, w) plays m, and only m
  have hall : ∀ δ, M.dox i w μ δ → ∀ m', M.MoveAt δ w m' ↔ m' = m := by
    intro δ hδ m'
    exact (M.self_awareness i w μ hi δ hδ m').trans
      ⟨fun h' => moveAt_unique h' hμm, fun h' => h' ▸ hμm⟩
  have hEC := M.expectational_continuity i w μ m w' hμm hnext
    (M.present_seriality i w μ hμr) hall
  refine ⟨hμw', fun δ hδ => ?_⟩
  have hδγ : M.dox i w γ δ := (dox_cluster hμ).mp ((hEC δ).mp hδ)
  have hAX := h.2 δ hδγ
  simp only [AX, sat_and, sat_bigAnd_map] at hAX
  have hcf : sat M δ w (move m □→ next φ) := hAX.2 m (sig.moves_complete m)
  have hδm : M.MoveAt δ w m := (M.self_awareness i w γ hi δ hδγ m).mpr hm
  have hX := (sat_cf_of_sat (dox_reaches hδγ) (sat_move.mpr hδm)).mp hcf
  exact (sat_next_iff hδm hnext).mp hX

/-! ## What the formalization found

**Status.** Open. Definitions complete; the proof on pp. 40–41 was read
against them and could not be replayed, for the following reasons.

1. **A case is dropped.** The proof begins: "Take any move m ∈ M. If
   M, γ, w ⊩ ¬◇(m ∧ Ratᵢ), then clearly M, γ, w ⊩ ¬m. Otherwise, we know
   … Bᵢ(m □→ X ⋀_{j≠i} Bⱼ PastRat^{y+1}ᵢ)." Nothing further is said about
   the first case, but the conclusion drawn at the end of the paragraph,
   "M, μ, w ⊩ m □→ X B^E FutRat^zᵢ for every m ∈ PMoves(w)," is then used
   at (5.5) for *every* available m′, including those with ¬◇(m′ ∧ Ratᵢ).
   For such m′, H^yᵢ gives nothing, and (5.5)'s middle disjunct is not
   established. CondRat's third disjunct, ¬◇(m′ ∧ X B^E FutRat^zᵢ) ∧
   B̂ᵢ(m′ □→ ⋁_{h≤k} hᵢ), was added for exactly this situation (p. 39,
   "the third condition is necessary since …"), but the proof does not
   argue that ¬◇(m′ ∧ Ratᵢ) implies ¬◇(m′ ∧ X B^E FutRat^zᵢ), and it is
   not clear that it does.

2. **"This gives us M, μ, w ⊩ m □→ X Bᵢ FutRat^zᵢ" (p. 41).** For the move
   m actually made at (γ, w) this is `bel_next_of_bel_AX`, via
   Self-Awareness, Expectational Continuity, Transitivity and
   Euclideanness, none of which the proof cites. For a move m′ ≠ m it does
   not follow from Bᵢ AX FutRat^zᵢ at γ: a world β maximally m′-consistent
   with μ at w plays m′, so Self-Awareness puts β outside ⊒ʷᵢ(γ), and
   β's beliefs at next(w, m′) are constrained (by Minimal Revision) only
   through β's *own* plausible worlds at w, about which Bᵢ AX FutRat^zᵢ
   at γ says nothing. So (5.3)'s j = i component, hence "m′ □→ X B^E
   FutRat^zᵢ at ν" as used before (5.5), is unsupported for m′ ≠ m.
   Whether the *theorem* survives is a separate question; a countermodel
   would have to defeat CondRat's second and third disjuncts at once, and
   this formalization did not construct one.

3. **The (5.6) inference** "Bᵢ(m □→ ⋁ hᵢ) and Bᵢ(m □→ X B^E FutRat) give
   Bᵢ((m ∧ X B^E FutRat) □→ ⋁ hᵢ)" is cautious monotonicity,
   `maxConsistent_of_and_of_local`; in general it needs node-local premises
   (Q12) and finiteness (Q6). For the actual move it is not needed at all,
   since the antecedent is true at every μ ∈ ⊒ʷᵢ(γ) and `sat_cf_of_sat`
   applies.

4. **From PF to (5.2).** See Q16: the printed PF has consequent FutRat^zᵢ,
   and (5.2) uses Bⱼ FutRat^{z′}ᵢ. Either way, (5.2) needs the step from
   Bⱼ PF^{y+1,z′} at the next node to the displayed counterfactual, which
   is Counterfactual K′ inside X and inside m □→; fine, but several
   inferences compressed into one line.

5. **The closing case split** ("Now we consider the cases where
   M, γ, w ⊮ V^{y,z}ᵢ ∧ Ratᵢ …") is unnecessary: `valid_cf_of_imp`.

Item 1 and item 2 together are why this result is marked open rather than
partly proved: the proof establishes the m-part of CondRat for the actual
move (that much is `bel_next_of_bel_AX` plus `sat_rat_of_dox`), but the
⋀_{m′} part rests on an inference that the frame conditions do not seem
to supply. -/

end

end DclegProofs
