import DclegProofs.Basics

/-!
# Lemma 4.1: BI_z characterizes the backward-induction paths

**The result in plain words.** Chapter 4 defines, for each depth z, a
formula BI_z (p. 27) meant to say "from here on, the play in this world
follows a backward-induction path." Lemma 4.1 says the formula does its
job:

> **Lemma 4.1** (p. 27). Where node w is at depth z in the game tree,
> M, γ, w ⊩ BI_z if and only if the path dictated by H(γ) starting from w
> is a backward induction path.

**Status: partly formalized.** The definitions are complete, the base case
(z = 0) is proved (`lemma4_1_zero`), and the full claim is stated as
`claim_lemma4_1`. The inductive case is not proved here; the closing
section says exactly what it needs and what the formalization found about
the hand proof along the way.

**Lean, as it comes up.** `def name (args) : Type := body` defines a
function. Recursion on a natural number `z` is written by cases `| 0 => …`
and `| z + 1 => …`. A `def … : Prop` whose body is a statement is a
*claim*: writing it down does not assert it; only a `theorem` with a proof
does. The word `sat M γ w φ` is "M, γ, w ⊩ φ" from `Semantics.lean`.
-/

namespace DclegProofs

open Formula

variable {Agent Move PVar : Type}

/-! ## The payoff disjunctions

BI_z uses ⋁_{h∈N : h ≥ k} hᵢ and ⋁_{h∈N : h ≤ k} hᵢ. Because N is the list
`sig.payoffs`, these are `bigOr` over the list filtered by the condition.
`List.filter` wants a Boolean test, hence `decide (k ≤ h)`. -/

/-- ⋁_{h ∈ N : h ≥ k} hᵢ -/
def payoffAtLeast (sig : Signature Agent Move) (k : Int) (i : Agent) : Formula Agent Move PVar :=
  bigOr ((sig.payoffs.filter fun h => decide (k ≤ h)).map fun h => payoff h i)

/-- ⋁_{h ∈ N : h ≤ k} hᵢ -/
def payoffAtMost (sig : Signature Agent Move) (k : Int) (i : Agent) : Formula Agent Move PVar :=
  bigOr ((sig.payoffs.filter fun h => decide (h ≤ k)).map fun h => payoff h i)

variable {Node World : Type} {sig : Signature Agent Move} {M : GameModel Agent Move Node World PVar sig}

/-- ⋁_{h ≥ k} hᵢ holds exactly when i's payoff in γ's outcome is at least k.
Uses `P_range` (payoffs lie in N) for the ← direction. -/
theorem sat_payoffAtLeast {γ : World} {w : Node} {k : Int} {i : Agent} :
    sat M γ w (payoffAtLeast sig k i) ↔ k ≤ M.P i (M.H γ).outcome := by
  simp only [payoffAtLeast, sat_bigOr, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨φ, ⟨h, ⟨_, hk⟩, rfl⟩, hsat⟩
    simp only [sat] at hsat
    rw [hsat]; exact hk
  · intro hk
    exact ⟨payoff (M.P i (M.H γ).outcome) i,
      ⟨M.P i (M.H γ).outcome, ⟨M.P_range i _ (M.H_wf γ).outcome_end, hk⟩, rfl⟩, rfl⟩

theorem sat_payoffAtMost {γ : World} {w : Node} {k : Int} {i : Agent} :
    sat M γ w (payoffAtMost sig k i) ↔ M.P i (M.H γ).outcome ≤ k := by
  simp only [payoffAtMost, sat_bigOr, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨φ, ⟨h, ⟨_, hk⟩, rfl⟩, hsat⟩
    simp only [sat] at hsat
    rw [hsat]; exact hk
  · intro hk
    exact ⟨payoff (M.P i (M.H γ).outcome) i,
      ⟨M.P i (M.H γ).outcome, ⟨M.P_range i _ (M.H_wf γ).outcome_end, hk⟩, rfl⟩, rfl⟩

/-! ## The formula BI_z (p. 27)

> BI₀ := end
>
> BI_{z+1} := X(⋁_{0≤z′≤z} BI_{z′}) ∧ ◇X BI_z ∧
>   ⋁_{i∈A} ⋁_{k∈N} ⋁_{m∈M} ( mᵢ ∧ □((m ∧ X ⋁_{0≤z′≤z} BI_{z′}) □→ ⋁_{h∈N:h≥k} hᵢ)
>     ∧ ⋀_{m′∈M} ( □¬m′ ∨ ◇(m′ ∧ X ⋁_{0≤z′≤z} BI_{z′} ∧ ⋁_{h∈N:h≤k} hᵢ) ) )

The recursion refers to *all* earlier BI_{z′}, through ⋁_{z′≤z} BI_{z′}.
Lean's structural recursion wants each recursive call on `z`, not on an
arbitrary smaller number, so `BIpair z` computes the pair
(BI_z, ⋁_{z′≤z} BI_{z′}) in one go, and `BI z` is its first component.
`BIbody z b u` is the displayed BI_{z+1} with `b` standing for BI_z and `u`
for ⋁_{z′≤z} BI_{z′}. -/

/-- The body of BI_{z+1}, given `b` = BI_z and `u` = ⋁_{0≤z′≤z} BI_{z′}. -/
def BIbody (sig : Signature Agent Move) (b u : Formula Agent Move PVar) : Formula Agent Move PVar :=
  next u ∧' ◇ (next b) ∧'
  bigOr (sig.agents.map fun i => bigOr (sig.payoffs.map fun k => bigOr (sig.moves.map fun m =>
    movei m i ∧'
    □ ((move m ∧' next u) □→ payoffAtLeast sig k i) ∧'
    bigAnd (sig.moves.map fun m' =>
      □ (¬' (move m')) ∨' ◇ (move m' ∧' next u ∧' payoffAtMost sig k i)))))

/-- (BI_z, ⋁_{0≤z′≤z} BI_{z′}). -/
def BIpair (sig : Signature Agent Move) : Nat → Formula Agent Move PVar × Formula Agent Move PVar
  | 0 => («end», «end»)
  | z + 1 =>
      let b := BIbody sig (BIpair sig z).1 (BIpair sig z).2
      (b, (BIpair sig z).2 ∨' b)

/-- BI_z (p. 27). -/
def BI (sig : Signature Agent Move) (z : Nat) : Formula Agent Move PVar := (BIpair sig z).1

/-- ⋁_{0≤z′≤z} BI_{z′}. -/
def BIupto (sig : Signature Agent Move) (z : Nat) : Formula Agent Move PVar := (BIpair sig z).2

/-- `BIupto` really is the disjunction of the earlier BI's. -/
theorem sat_BIupto {γ : World} {w : Node} {z : Nat} :
    sat M γ w (BIupto sig z) ↔ ∃ z' ≤ z, sat M γ w (BI sig z') := by
  induction z with
  | zero =>
    constructor
    · intro h; exact ⟨0, Nat.le_refl 0, h⟩
    · rintro ⟨z', hz', h⟩
      have : z' = 0 := Nat.le_zero.mp hz'
      subst this; exact h
  | succ n ih =>
    show sat M γ w ((BIpair sig n).2 ∨' _) ↔ _
    simp only [sat]
    constructor
    · rintro (h | h)
      · obtain ⟨z', hz', h⟩ := ih.mp h
        exact ⟨z', Nat.le_succ_of_le hz', h⟩
      · exact ⟨n + 1, Nat.le_refl _, h⟩
    · rintro ⟨z', hz', h⟩
      rcases Nat.lt_or_eq_of_le hz' with hlt | rfl
      · exact Or.inl (ih.mpr ⟨z', Nat.le_of_lt_succ hlt, h⟩)
      · exact Or.inr h

/-! ## Depth

The thesis uses "the depth z of the current node" (p. 26) and, on p. 38,
"the maximal distance from the current node to an outcome node." The Lean
relation `Depth T w z` says exactly that: outcome nodes have depth 0, and a
node whose successors all have depth ≤ z, one of them exactly z, has depth
z + 1. In the `node` rule the successors' depths are given by a function
`d`, and the successor of depth exactly z is named (`m₀`, `w₀`) rather than
asserted to exist: Lean does not allow "there exists … `Depth` …" inside
the rules that define `Depth` itself, and naming the witnesses says the
same thing. (Nodes on a cycle unreachable from the root, see the note in
`Semantics.lean`, have no depth; every node on a history does, since the
tree is finite. That is left as a hypothesis of the results.) -/

/-- Depth of a node: maximal distance to an outcome node. -/
inductive Depth (T : StrategicStructure Agent Move Node) : Node → Nat → Prop
  | leaf {w : Node} : T.EndV w → Depth T w 0
  | node {w : Node} {z : Nat} (d : Move → Nat) (m₀ : Move) (w₀ : Node) :
      (∀ m w', T.next w m = some w' → d m ≤ z) →
      (∀ m w', T.next w m = some w' → Depth T w' (d m)) →
      T.next w m₀ = some w₀ → Depth T w₀ z →
      Depth T w (z + 1)

theorem depth_zero_iff {T : StrategicStructure Agent Move Node} {w : Node} :
    Depth T w 0 ↔ T.EndV w := by
  constructor
  · intro h; cases h; assumption
  · exact Depth.leaf

/-! ## Backward induction (§2.2.1, p. 7; §4.1, pp. 26–27)

Page 7 defines backward induction by pruning: at each final decision node
keep the branches leading to the current player's maximal payoff (for
degenerate games, "pruned using the maximin principle"), then treat the
node as an outcome and repeat. The *proof* of Lemma 4.1 (p. 27) works with
an equivalent recursive description, which is what the Lean defines:

> For each successor w′ of w, let o₁,…,oₐ be the outcome nodes reachable
> by a backward induction path from w′. Set k_{w′} = min{Pᵢ(o_b)}.
> Backward induction instructs player i to choose a move m such that for
> every m′, k_{next(w,m′)} ≤ k_{next(w,m)}. Let BI(w) ⊆ PMoves(w) denote
> the set of moves permitted by backward induction.

`BIOutcomes T P w S` says "S is the set of outcome nodes reachable from w
by a backward-induction path." `BIMove T P w i S m` is "m ∈ BI(w)," given
the sets `S m′` for the successors. The comparison of minima
k_{next(w,m′)} ≤ k_{next(w,m)} is written without computing a minimum:
"for every outcome o under m there is an outcome o′ under m′ with
Pᵢ(o′) ≤ Pᵢ(o)," which for finite non-empty sets is the same thing.

**QUESTION FOR JEREMIAH (Q13).** Is this recursive description the
intended definition of "backward induction path" (the one Lemma 4.1 is
about), with ties broken by the maximin rule as p. 7 says for degenerate
games? The Lean defines it directly and does not relate it to pruning. -/

/-- m ∈ BI(w): m is available, and for every available m′, the minimum
payoff for i under m′ is at most the minimum under m. -/
def BIMove (T : StrategicStructure Agent Move Node) (P : Agent → Node → Int)
    (w : Node) (i : Agent) (S : Move → Node → Prop) (m : Move) : Prop :=
  (∃ w', T.next w m = some w') ∧
  ∀ m' w'', T.next w m' = some w'' → ∀ o, S m o → ∃ o', S m' o' ∧ P i o' ≤ P i o

/-- `BIOutcomes T P w S`: S is the set of outcomes reachable from w along
backward-induction paths. -/
inductive BIOutcomes (T : StrategicStructure Agent Move Node) (P : Agent → Node → Int) :
    Node → (Node → Prop) → Prop
  | leaf {w : Node} : T.EndV w → BIOutcomes T P w (fun o => o = w)
  | node {w : Node} {i : Agent} (S : Move → Node → Prop) :
      T.Q w = some i →
      (∀ m w', T.next w m = some w' → BIOutcomes T P w' (S m)) →
      BIOutcomes T P w (fun o => ∃ m, BIMove T P w i S m ∧ S m o)

/-- "The path dictated by H(γ) starting from w is a backward induction
path": either w is an outcome node (the path ⟨w⟩), or the move γ makes at
w is in BI(w) and the same holds from the next node. -/
inductive FollowsBI (M : GameModel Agent Move Node World PVar sig) : World → Node → Prop
  | leaf {γ : World} {w : Node} : M.T.EndV w → FollowsBI M γ w
  | step {γ : World} {w : Node} {i : Agent} {m : Move} {w' : Node} (S : Move → Node → Prop) :
      M.T.Q w = some i → M.MoveAt γ w m → M.T.next w m = some w' →
      (∀ m'' w'', M.T.next w m'' = some w'' → BIOutcomes M.T M.P w'' (S m'')) →
      BIMove M.T M.P w i S m →
      FollowsBI M γ w' → FollowsBI M γ w

/-! ## The statement

Line by line: for any types of nodes and worlds and any game model over
the signature; for any world γ, node w and depth z; if w has depth z and
w is reached in γ (the pointed model is legitimate), then BI_z holds at
(γ, w) exactly when γ follows a backward-induction path from w. -/

/-- Lemma 4.1, as a claim. -/
def claim_lemma4_1 (sig : Signature Agent Move) (PVar : Type) : Prop :=
  ∀ (Node World : Type) (M : GameModel Agent Move Node World PVar sig) (γ : World) (w : Node) (z : Nat),
    Depth M.T w z → M.Reaches γ w →
      (sat M γ w (BI (PVar := PVar) sig z) ↔ FollowsBI M γ w)

/-! ## The base case, proved

The hand proof's base cases (pp. 27–28):

> *BI Path ⇒ Satisfaction.* Suppose that w ∈ EndV. … Then we know that
> w ∈ V_γ, and since w ∈ EndV, we get M, γ, w ⊩ end. Therefore
> M, γ, w ⊩ BI₀.
>
> *Satisfaction ⇒ BI Path.* Take any w ∈ V and a world γ where
> M, γ, w ⊩ BI₀. Then … w ∈ EndV. … this path has to be ⟨w⟩, i.e. exactly
> the backward induction path.

Both directions go through `sat_end_iff` from `Basics.lean`, which is the
p. 21 claim that `end` holds exactly at outcome nodes. Note the second
direction does not use the depth hypothesis at all, exactly as in the
hand proof. -/

/-- BI₀ holds at a reached node exactly when it is an outcome node. -/
theorem sat_BI_zero_iff {γ : World} {w : Node} (hγ : M.Reaches γ w) :
    sat M γ w (BI sig 0) ↔ M.T.EndV w :=
  sat_end_iff hγ

/-- Lemma 4.1 for z = 0. -/
theorem lemma4_1_zero {γ : World} {w : Node} (hd : Depth M.T w 0) (hγ : M.Reaches γ w) :
    sat M γ w (BI sig 0) ↔ FollowsBI M γ w := by
  have hend := depth_zero_iff.mp hd
  constructor
  · intro _
    exact FollowsBI.leaf hend
  · intro _
    exact (sat_BI_zero_iff hγ).mpr hend

/-- The "Satisfaction ⇒ BI path" base case, with no depth hypothesis, as
the hand proof states it. -/
theorem followsBI_of_sat_BI_zero {γ : World} {w : Node} (hγ : M.Reaches γ w)
    (h : sat M γ w (BI sig 0)) : FollowsBI M γ w :=
  FollowsBI.leaf ((sat_BI_zero_iff hγ).mp h)

/-! ## What the formalization found

**Status.** Base case proved. Inductive case open. Writing the definitions
and reading the inductive case against them turned up the following.

1. **The induction hypothesis does not match the statement.** Lemma 4.1
   is stated for "w at depth z." In *Satisfaction ⇒ BI path* (p. 29) the
   hypothesis for w at depth n+1 gives X ⋁_{0≤z≤n} BI_z, so at
   w′ = next(w, m_γ) some BI_{z′} holds with z′ ≤ n, and the proof says
   "so the path dictated by H(γ) starting from w′ is a backward induction
   path by the inductive hypothesis." But the inductive hypothesis, as an
   instance of the lemma, applies to BI_{z′} at w′ only if depth(w′) = z′,
   and nothing so far says which z′ the disjunction supplies. The gap can
   be closed by a separate fact, *M, γ, w ⊩ BI_z implies depth(w) = z*
   (plausible: the ⋀_{m′} conjunct together with the requirement that
   every outcome is reached in some world forces every successor to have
   depth ≤ z, and ◇X BI_z forces one of depth z), which the thesis does not
   state or prove; or by restating the lemma without the depth hypothesis
   as "M, γ, w ⊩ BI_z iff depth(w) = z and the path from w is a BI path."
   The same issue does not arise in *BI path ⇒ Satisfaction*, where the
   depth of w′ is known.

2. **"Every possible path has to be represented in a model" (p. 27).**
   The model only requires every *outcome node* to be reached in some
   world (`H_covers`). The step from an outcome o reachable from w″ to a
   world η whose history follows the path from w″ to o also uses that
   paths to o are unique (condition 5) and that every history starts at
   the root, so η's history must pass through w″ along that path. This is
   true but is a lemma about `PathFrom` and `Reach` that the formal proof
   would need, and the hand proof does not mention it.

3. **Choosing k_BI ∈ N.** BI_{z+1} quantifies k over N, so the proof's
   k_BI = min{Pᵢ(o)} must lie in N. It does, because Pᵢ maps outcome nodes
   into N (`P_range`) and the minimum of a finite non-empty set of payoffs
   is one of them; but the formal proof must construct that minimum from
   the finiteness of V, which is bookkeeping the hand proof does not need.

4. **□¬m′ for unavailable moves** (p. 28, "there are no possible worlds
   which take this move") follows from history condition 2
   (`moveAt_pmoves`). **¬□¬m′ for available moves** needs, again, a world
   playing m′ at w, i.e. item 2.

5. **Two readings of "backward induction path"** (Q13): pruning (p. 7)
   versus the recursive description used in the proof (p. 27). The Lean
   commits to the latter.

None of these affects the base case. Items 1 and 2 are what the inductive
case would need before the reasoning on pp. 27–29 can be replayed step by
step; item 1 is the one that changes what has to be proved. -/

end DclegProofs
