import DclegProofs.Basics

/-!
# Q12, checked on a concrete model

`Basics.lean` (Q12) claims that under the literal reading of "maximally
φ-consistent" (p. 19), where clause 2(b) quantifies ⟦φ⟧ over pairs at
*every* node, the p. 22 statement "◇m′ gives a maximally m′-consistent
world" can fail. This file builds the smallest game model that shows it
and has Lean check every condition of `GameModel` on it, so the claim does
not rest on a prose argument.

**The game.** Five nodes: a root `r` where player `i` chooses `m` (to the
outcome `w1`) or `m'` (to `v`); at `v`, again `i`'s turn, `m'` leads to the
outcome `o1` and `m` to `o2`.

**The worlds.** `γ` plays m at r. `β` plays m′ at r and m at v. `δ` plays
m′ at r and m′ at v. So every outcome is reached, and ⟦m′⟧, the pairs where
m′ is played, is {(β,r), (δ,r), (δ,v)}.

**The premises at (γ, r).**
  Y₁ = {(γ,r), (β,r), (δ,r), (δ,v)},  Y₂ = {(γ,r), (δ,v)},  Y₃ = {(γ,r)}.
⋂{Y₁,Y₂,Y₃} = {(γ,r)}, so Centering holds; Y₁ contains every world at r, so
Contemporary Universality holds. Everywhere else, F(x,u) consists of the
singleton {(x,u)} and the set of all reached pairs at u, which satisfy
both conditions trivially.

**Why max^{m′}_{F(γ,r)}(Γ) is empty.** A world β′ in it needs a non-empty
G ⊆ {Y₁,Y₂,Y₃} with (β′,r) ∈ ⋂G and β′ playing m′ at r, so β′ ∈ {β,δ}. Only
Y₁ contains (β,r) or (δ,r), so G = {Y₁}. But G′ = {Y₁,Y₂} is a strict
superset inside F(γ,r) whose intersection {(γ,r),(δ,v)} contains the
m′-pair (δ,v), at the *other* node v. So clause 2(b) fails for G, and no
β′ qualifies. Meanwhile ◇m′ holds at (γ,r), witnessed by β. Hence
m′ □→ ⊥ is true at (γ,r): the counterfactual is vacuous although the
antecedent is possible.

**Beliefs.** Each world considers only itself plausible, at every node it
reaches (`exDox`). All eight doxastic conditions then hold, most of them
trivially; Minimal Revision needs that a world is maximally m-consistent
with itself when it plays m, which Centering provides.

**Lean, as it comes up.** `inductive … deriving DecidableEq` defines a
finite type with the listed elements and lets `decide` settle equalities
on it. `decide` proves a closed statement by computing it; here it does
the bookkeeping on the five nodes and three worlds. `cases x <;> decide`
does a case split on a variable and then `decide` in every case.
-/

namespace DclegProofs.Q12Example

open Formula

inductive ExNode | r | w1 | v | o1 | o2
  deriving DecidableEq, Repr
inductive ExWorld | γ | β | δ
  deriving DecidableEq, Repr
inductive ExAgent | i
  deriving DecidableEq, Repr
inductive ExMove | m | m'
  deriving DecidableEq, Repr

open ExNode ExWorld ExAgent ExMove

/-! ### Making `decide` work

Lean's core library can decide equalities on these types but not
statements "for all nodes …" or "for some move …", since it has no
built-in notion of a finite type. The instances below say how: check each
element. With them, `decide` settles every closed statement in this file
that quantifies over nodes, worlds or moves. -/

instance {P : ExMove → Prop} [DecidablePred P] : Decidable (∀ x, P x) :=
  decidable_of_iff (P m ∧ P m')
    ⟨fun h x => by cases x <;> simp_all, fun h => ⟨h m, h m'⟩⟩
instance {P : ExMove → Prop} [DecidablePred P] : Decidable (∃ x, P x) :=
  decidable_of_iff (P m ∨ P m')
    ⟨fun h => h.elim (⟨m, ·⟩) (⟨m', ·⟩), fun ⟨x, hx⟩ => by cases x <;> simp_all⟩
instance {P : ExNode → Prop} [DecidablePred P] : Decidable (∀ x, P x) :=
  decidable_of_iff (P r ∧ P w1 ∧ P v ∧ P o1 ∧ P o2)
    ⟨fun h x => by cases x <;> simp_all, fun h => ⟨h r, h w1, h v, h o1, h o2⟩⟩
instance {P : ExNode → Prop} [DecidablePred P] : Decidable (∃ x, P x) :=
  decidable_of_iff (P r ∨ P w1 ∨ P v ∨ P o1 ∨ P o2)
    ⟨fun h => by rcases h with h | h | h | h | h <;> exact ⟨_, h⟩,
     fun ⟨x, hx⟩ => by cases x <;> simp_all⟩
instance {P : ExWorld → Prop} [DecidablePred P] : Decidable (∀ x, P x) :=
  decidable_of_iff (P γ ∧ P β ∧ P δ)
    ⟨fun h x => by cases x <;> simp_all, fun h => ⟨h γ, h β, h δ⟩⟩
instance {P : ExWorld → Prop} [DecidablePred P] : Decidable (∃ x, P x) :=
  decidable_of_iff (P γ ∨ P β ∨ P δ)
    ⟨fun h => by rcases h with h | h | h <;> exact ⟨_, h⟩,
     fun ⟨x, hx⟩ => by cases x <;> simp_all⟩

/-! ## The signature and the strategic structure -/

def exSig : Signature ExAgent ExMove where
  agents := [i]
  moves := [m, m']
  payoffs := [0]
  agents_complete := fun a => by cases a; simp
  moves_complete := fun x => by cases x <;> simp

def isEnd : ExNode → Bool
  | w1 | o1 | o2 => true
  | r | v => false

def exQ : ExNode → Option ExAgent
  | r | v => some i
  | w1 | o1 | o2 => none

def exNext : ExNode → ExMove → Option ExNode
  | r, m => some w1
  | r, m' => some v
  | v, m' => some o1
  | v, m => some o2
  | _, _ => none

def pm (n : ExNode) (x : ExMove) : Bool := (exNext n x).isSome

def exT : StrategicStructure ExAgent ExMove ExNode where
  EndV n := isEnd n = true
  Q := exQ
  PMoves n x := pm n x = true
  next := exNext
  nodes_finite := ⟨[r, w1, v, o1, o2], by decide⟩
  endV_proper := by decide
  cond1 := by decide
  cond2 := by decide
  cond3 := by decide
  cond4 := by decide
  cond5 := by decide
  cond6 := by decide
  cond7 := by decide

instance (n : ExNode) : Decidable (exT.EndV n) := inferInstanceAs (Decidable (isEnd n = true))
instance (n : ExNode) (x : ExMove) : Decidable (exT.PMoves n x) :=
  inferInstanceAs (Decidable (pm n x = true))

/-! ## Histories -/

def exH : ExWorld → History ExMove ExNode
  | γ => ⟨[(r, m)], w1⟩
  | β => ⟨[(r, m'), (v, m)], o2⟩
  | δ => ⟨[(r, m'), (v, m')], o1⟩

instance (x : ExWorld) (u : ExNode) : Decidable (Reaches exH x u) :=
  inferInstanceAs (Decidable (u ∈ (exH x).nodes))
instance (x : ExWorld) (u : ExNode) (y : ExMove) : Decidable (MoveAt exH x u y) :=
  inferInstanceAs (Decidable ((u, y) ∈ (exH x).steps))

theorem exRoot : exT.IsRoot r := by unfold StrategicStructure.IsRoot; decide

theorem exH_wf : ∀ x, (exH x).WellFormed exT := by
  intro x
  cases x
  · exact ⟨by decide, ⟨r, exRoot, .cons (by decide) (.nil _)⟩, by decide, by decide⟩
  · exact ⟨by decide, ⟨r, exRoot, .cons (by decide) (.cons (by decide) (.nil _))⟩,
      by decide, by decide⟩
  · exact ⟨by decide, ⟨r, exRoot, .cons (by decide) (.cons (by decide) (.nil _))⟩,
      by decide, by decide⟩

/-- A move made at u leads to a node that is also reached: a fact about the
three histories that `decide` settles once the variables are fixed. -/
theorem reach_step {x : ExWorld} {u u' : ExNode} {y : ExMove}
    (hm : MoveAt exH x u y) (hn : exNext u y = some u') :
    Reaches exH x u ∧ Reaches exH x u' := by
  revert hm hn
  cases x <;> cases u <;> cases y <;> cases u' <;> decide

/-! ## Premises -/

def Y1 : ExWorld × ExNode → Prop := fun p => p = (γ, r) ∨ p = (β, r) ∨ p = (δ, r) ∨ p = (δ, v)
def Y2 : ExWorld × ExNode → Prop := fun p => p = (γ, r) ∨ p = (δ, v)
/-- {(x,u)}, when reached (so that premises are subsets of I). -/
def singleP (x : ExWorld) (u : ExNode) : ExWorld × ExNode → Prop :=
  fun p => p = (x, u) ∧ Reaches exH x u
/-- All reached pairs at u. -/
def sliceP (u : ExNode) : ExWorld × ExNode → Prop := fun p => p.2 = u ∧ Reaches exH p.1 u

/-- F(x, u): at (γ, r) the three premises Y₁, Y₂, Y₃ = {(γ,r)}; elsewhere
the singleton and the slice. -/
def exF (x : ExWorld) (u : ExNode) (Y : ExWorld × ExNode → Prop) : Prop :=
  (Y = Y1 ∧ x = γ ∧ u = r) ∨ (Y = Y2 ∧ x = γ ∧ u = r) ∨
  Y = singleP x u ∨ (Y = sliceP u ∧ ¬ (x = γ ∧ u = r))

theorem exF_self {x : ExWorld} {u : ExNode} (hx : Reaches exH x u) {Y} (hY : exF x u Y) :
    Y (x, u) := by
  rcases hY with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | rfl | ⟨rfl, _⟩
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact ⟨rfl, hx⟩
  · exact ⟨rfl, hx⟩

/-! ## Beliefs: each world considers exactly itself plausible -/

def exDox (_ : ExAgent) (u : ExNode) (x y : ExWorld) : Prop := Reaches exH x u ∧ x = y

/-- A world that plays y at u is maximally ⟦y⟧-consistent with itself:
take G = F(x, u). -/
theorem maxConsistent_self {x : ExWorld} {u : ExNode} {y : ExMove}
    (hm : MoveAt exH x u y) (hx : Reaches exH x u) :
    MaxConsistent exF x u (fun p => Reaches exH p.1 p.2 ∧ MoveAt exH p.1 p.2 y) x := by
  refine ⟨⟨hx, hm⟩, exF x u, ⟨singleP x u, Or.inr (Or.inr (Or.inl rfl))⟩, fun _ h => h,
    fun _ hY => exF_self hx hY, ?_⟩
  intro G' _ ⟨Y, hY, hYn⟩ hsub _ _ _
  exact hYn (hsub Y hY)

/-! ## The model -/

def exM : GameModel ExAgent ExMove ExNode ExWorld Empty exSig where
  T := exT
  worlds_finite := ⟨[γ, β, δ], fun x => by cases x <;> decide⟩
  H := exH
  H_wf := exH_wf
  H_covers := fun u hu => by
    cases u
    · exact absurd hu (by decide)
    · exact ⟨γ, by decide⟩
    · exact absurd hu (by decide)
    · exact ⟨δ, by decide⟩
    · exact ⟨β, by decide⟩
  π := fun p => p.elim
  π_sub := fun p => p.elim
  P := fun _ _ => 0
  P_range := fun _ _ _ => by simp [exSig]
  F := exF
  F_sub := by
    intro x u Y hY p hp
    rcases hY with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | rfl | ⟨rfl, _⟩
    · rcases hp with rfl | rfl | rfl | rfl <;> decide
    · rcases hp with rfl | rfl <;> decide
    · obtain ⟨rfl, h⟩ := hp; exact h
    · obtain ⟨h1, h2⟩ := hp; rw [h1]; exact h2
  F_finite := fun x u => ⟨[Y1, Y2, singleP x u, sliceP u], fun Y hY => by
    rcases hY with ⟨rfl, _, _⟩ | ⟨rfl, _, _⟩ | rfl | ⟨rfl, _⟩ <;> simp⟩
  centering := by
    intro x u hx p hp
    constructor
    · intro h
      exact (h (singleP x u) (Or.inr (Or.inr (Or.inl rfl)))).1
    · rintro rfl Y hY
      exact exF_self hx hY
  contemporary_universality := by
    intro b x u hb
    by_cases h : x = γ ∧ u = r
    · obtain ⟨rfl, rfl⟩ := h
      refine ⟨Y1, Or.inl ⟨rfl, rfl, rfl⟩, ?_⟩
      cases b
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
    · exact ⟨sliceP u, Or.inr (Or.inr (Or.inr ⟨rfl, h⟩)), rfl, hb⟩
  dox := exDox
  presence := fun _ u y hy b ⟨hb, hby⟩ => hy (hby ▸ hb)
  present_seriality := fun _ u x hx => ⟨x, hx, rfl⟩
  transitivity := fun _ u a b c h1 h2 => ⟨h1.1, h1.2.trans h2.2⟩
  euclidean := fun _ u a b c h1 h2 => by
    obtain ⟨ha, rfl⟩ := h1; obtain ⟨_, rfl⟩ := h2; exact ⟨ha, rfl⟩
  self_awareness := fun _ u x _ d hd y => by obtain ⟨_, rfl⟩ := hd; exact Iff.rfl
  minimal_revision := fun _ u x y u' hm hn d hd => by
    obtain ⟨_, rfl⟩ := hd
    exact ⟨x, ⟨(reach_step hm hn).1, rfl⟩, maxConsistent_self hm (reach_step hm hn).1⟩
  expectational_continuity := fun _ u x y u' hm hn _ _ d => by
    obtain ⟨h1, h2⟩ := reach_step hm hn
    exact ⟨fun ⟨_, e⟩ => ⟨h1, e⟩, fun ⟨_, e⟩ => ⟨h2, e⟩⟩
  recall := fun _ u x y u' hm hn e => by
    obtain ⟨h1, h2⟩ := reach_step hm hn
    constructor
    · rintro ⟨_, rfl⟩; exact ⟨x, ⟨h2, rfl⟩, h1, rfl⟩
    · rintro ⟨d, ⟨_, rfl⟩, _, rfl⟩; exact ⟨h1, rfl⟩

instance (x : ExWorld) (u : ExNode) : Decidable (exM.Reaches x u) :=
  inferInstanceAs (Decidable (Reaches exH x u))
instance (x : ExWorld) (u : ExNode) (y : ExMove) : Decidable (exM.MoveAt x u y) :=
  inferInstanceAs (Decidable (MoveAt exH x u y))

/-! ## The two facts -/

/-- ◇m′ holds at (γ, r): β reaches r and plays m′ there. -/
theorem dia_move' : sat exM γ r (◇ (move m')) := by
  rw [sat_dia (by decide)]
  exact ⟨β, by decide, sat_move.mpr (by decide)⟩

/-- Y₁ ≠ Y₂ as sets: they differ at (β, r). -/
theorem Y1_ne_Y2 : Y1 ≠ Y2 := by
  intro h
  have : Y2 (β, r) := h ▸ (Or.inr (Or.inl rfl) : Y1 (β, r))
  rcases this with h' | h' <;> cases h'

/-- No world is maximally m′-consistent with γ at r. -/
theorem no_maxConsistent : ¬ ∃ b, exM.MaxConsistent γ r (extension exM (move m')) b := by
  rintro ⟨b, ⟨_, hbm⟩, G, ⟨Y0, hY0⟩, hGF, hbG, hmax⟩
  -- b plays m′ at r, so b is β or δ
  have hb : b = β ∨ b = δ := by
    have hbm' : MoveAt exH b r m' := sat_move.mp hbm
    revert hbm'; cases b <;> decide
  -- every member of G contains (b, r); of Y₁, Y₂, {(γ,r)}, only Y₁ does
  have hG1 : ∀ Y, G Y → Y = Y1 := by
    intro Y hY
    have hmem := hbG Y hY
    rcases hGF Y hY with ⟨rfl, _, _⟩ | ⟨rfl, _, _⟩ | rfl | ⟨rfl, hne⟩
    · rfl
    · exfalso; rcases hb with rfl | rfl <;> rcases hmem with h | h <;> cases h
    · exfalso; rcases hb with rfl | rfl <;> cases hmem.1
    · exact absurd ⟨rfl, rfl⟩ hne
  have hGY1 : G Y1 := (hG1 Y0 hY0) ▸ hY0
  -- G′ = {Y₁, Y₂} is a strict superset inside F(γ, r) whose intersection
  -- holds the m′-pair (δ, v)
  refine hmax (fun Y => Y = Y1 ∨ Y = Y2) (fun Y hY => Or.inl (hG1 Y hY))
    ⟨Y2, Or.inr rfl, fun h => Y1_ne_Y2 (hG1 Y2 h).symm⟩ ?_ (δ, v) ?_ ?_
  · rintro Y (rfl | rfl)
    · exact Or.inl ⟨rfl, rfl, rfl⟩
    · exact Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)
  · rintro Y (rfl | rfl)
    · exact Or.inr (Or.inr (Or.inr rfl))
    · exact Or.inr rfl
  · exact ⟨by decide, sat_move.mpr (by decide)⟩

/-- So m′ □→ ⊥ holds at (γ, r) although ◇m′ does: under the literal
reading of maximal consistency, the p. 22 claim fails on this model. -/
theorem cf_bot : sat exM γ r (move m' □→ bot) := by
  intro b hb
  exact no_maxConsistent ⟨b, hb⟩

/-- And the premises at (γ, r) are not node-local: Y₁ contains (δ, v). -/
theorem not_local : ¬ LocalPremises exM γ r := by
  intro h
  have := h Y1 (Or.inl ⟨rfl, rfl, rfl⟩) (δ, v) (Or.inr (Or.inr (Or.inr rfl)))
  cases this

end DclegProofs.Q12Example
