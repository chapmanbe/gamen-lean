import DclegProofs.Semantics

/-!
# Consequences of Chapter 3 that the proofs rely on

The hand proofs in Chapters 4 and 5 use a number of facts about DCLEG that
Chapter 3 states in prose (pp. 19, 21–23) rather than proving: that `end`
is true exactly at outcome nodes, that □φ does not depend on the world,
that centering makes a true antecedent's own world the only maximally
consistent one, that Bᵢ satisfies D, 4, 5 and C4, and so on. This file
proves them, so that the proof files can cite them by name. Everything here
is checked by Lean's kernel; the axiom audit in `Tests/DclegProofs.lean`
confirms that nothing beyond the three standard axioms is used.

**Lean, as it comes up.** A `theorem` has a statement (after the colon) and
a proof (after `:=`). Proofs are written with *tactics* inside `by …`; each
tactic transforms the current goal, and the infoview in VS Code shows the
goal after every step. The tactics used here, explained the first time
each appears:

* `intro x` — for a goal `∀ x, …` or `A → …`, name the thing being assumed.
* `exact e` — close the goal with the term `e`.
* `constructor` — for a goal `A ∧ B` (or `A ↔ B`), split into two goals.
* `obtain ⟨a, b⟩ := h` — take apart a hypothesis `h : A ∧ B` or `∃ a, B`.
* `cases h` / `rcases` — case analysis on a hypothesis.
* `refine ⟨_, _⟩` — like `exact`, but with holes that become new goals.
* `simp only [defs]` — rewrite with the listed definitions and lemmas.
* `by_contra h` — to prove `P`, assume `¬P` as `h` and derive `False`.
* `induction l with …` — structural induction on a list or a derivation.
-/

namespace DclegProofs

open Formula

variable {Agent Move Node World PVar : Type} {sig : Signature Agent Move}
variable {M : GameModel Agent Move Node World PVar sig}

/-! ## Unfolding the abbreviations

These say what satisfaction of each §3.1.2 abbreviation amounts to, which
is what p. 21 asserts in prose ("⊤ is always satisfied, φ ∧ ψ is satisfied
when both …"). Each is a one-line consequence of the definitions. -/

/-- The primitive clauses, restated as rewrite rules (each is true by
definition, `Iff.rfl`), so that proofs can unfold exactly the connective
they mean to. -/
theorem sat_neg {γ : World} {w : Node} {φ : Formula Agent Move PVar} :
    sat M γ w (¬' φ) ↔ ¬ sat M γ w φ := Iff.rfl
theorem sat_or {γ : World} {w : Node} {φ ψ : Formula Agent Move PVar} :
    sat M γ w (φ ∨' ψ) ↔ sat M γ w φ ∨ sat M γ w ψ := Iff.rfl
theorem sat_turn {γ : World} {w : Node} {i : Agent} :
    sat M γ w (turn i) ↔ M.T.Q w = some i := Iff.rfl
theorem sat_move {γ : World} {w : Node} {m : Move} :
    sat M γ w (move m) ↔ M.MoveAt γ w m := Iff.rfl
theorem sat_bel {γ : World} {w : Node} {i : Agent} {φ : Formula Agent Move PVar} :
    sat M γ w (bel i φ) ↔ M.Reaches γ w ∧ ∀ μ, M.dox i w γ μ → sat M μ w φ := Iff.rfl
theorem sat_next {γ : World} {w : Node} {φ : Formula Agent Move PVar} :
    sat M γ w (next φ) ↔ ∃ m w', M.MoveAt γ w m ∧ M.T.next w m = some w' ∧ sat M γ w' φ := Iff.rfl
theorem sat_cf {γ : World} {w : Node} {φ ψ : Formula Agent Move PVar} :
    sat M γ w (φ □→ ψ) ↔ ∀ β, M.MaxConsistent γ w (extension M φ) β → sat M β w ψ := Iff.rfl

theorem sat_top (γ : World) (w : Node) : sat M γ w top := by
  simp only [top, sat, not_false_eq_true]

theorem sat_and {γ : World} {w : Node} {φ ψ : Formula Agent Move PVar} :
    sat M γ w (φ ∧' ψ) ↔ sat M γ w φ ∧ sat M γ w ψ := by
  simp only [Formula.and, sat, not_or, Classical.not_not]

theorem sat_bigAnd {γ : World} {w : Node} {l : List (Formula Agent Move PVar)} :
    sat M γ w (bigAnd l) ↔ ∀ φ ∈ l, sat M γ w φ := by
  induction l with
  | nil => simp [bigAnd, sat_top]
  | cons φ rest ih => simp [bigAnd, sat_and, ih]

theorem sat_bigOr {γ : World} {w : Node} {l : List (Formula Agent Move PVar)} :
    sat M γ w (bigOr l) ↔ ∃ φ ∈ l, sat M γ w φ := by
  induction l with
  | nil => simp [bigOr, sat]
  | cons φ rest ih => simp [bigOr, sat, ih]

/-- The forms actually used: ⋁ and ⋀ over a list transformed by `f`
(e.g. ⋁_{m∈M} φ(m) is `bigOr (sig.moves.map φ)`). -/
theorem sat_bigOr_map {α : Type} {γ : World} {w : Node} {l : List α}
    {f : α → Formula Agent Move PVar} :
    sat M γ w (bigOr (l.map f)) ↔ ∃ x ∈ l, sat M γ w (f x) := by
  rw [sat_bigOr]
  constructor
  · rintro ⟨φ, hφ, h⟩
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hφ
    exact ⟨x, hx, h⟩
  · rintro ⟨x, hx, h⟩
    exact ⟨f x, List.mem_map.mpr ⟨x, hx, rfl⟩, h⟩

theorem sat_bigAnd_map {α : Type} {γ : World} {w : Node} {l : List α}
    {f : α → Formula Agent Move PVar} :
    sat M γ w (bigAnd (l.map f)) ↔ ∀ x ∈ l, sat M γ w (f x) := by
  rw [sat_bigAnd]
  constructor
  · intro h x hx
    exact h (f x) (List.mem_map.mpr ⟨x, hx, rfl⟩)
  · intro h φ hφ
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hφ
    exact h x hx

theorem sat_dia {γ : World} {w : Node} {φ : Formula Agent Move PVar} (hγ : M.Reaches γ w) :
    sat M γ w (◇ φ) ↔ ∃ β, M.Reaches β w ∧ sat M β w φ := by
  simp only [dia, sat, Classical.not_forall, Classical.not_not]
  constructor
  · intro ⟨β, ⟨_, hβ⟩, h⟩; exact ⟨β, hβ, h⟩
  · intro ⟨β, hβ, h⟩; exact ⟨β, ⟨hγ, hβ⟩, h⟩

theorem sat_dbel {γ : World} {w : Node} {i : Agent} {φ : Formula Agent Move PVar}
    (hγ : M.Reaches γ w) :
    sat M γ w (dbel i φ) ↔ ∃ μ, M.dox i w γ μ ∧ sat M μ w φ := by
  simp only [dbel, sat]
  constructor
  · intro h
    apply Classical.byContradiction
    intro hno
    exact h ⟨hγ, fun μ hμ hφ => hno ⟨μ, hμ, hφ⟩⟩
  · intro ⟨μ, hμ, hφ⟩ h
    exact h.2 μ hμ hφ

theorem sat_belE {γ : World} {w : Node} {φ : Formula Agent Move PVar} :
    sat M γ w (belE sig φ) ↔ ∀ i, sat M γ w (bel i φ) := by
  rw [belE, sat_bigAnd_map]
  exact ⟨fun h i => h i (sig.agents_complete i), fun h i _ => h i⟩

/-! ## Histories: reached nodes and moves

Small facts about `Reaches` and `MoveAt` that every later proof uses. -/

/-- If Move(γ, w) = m then w ∈ V_γ. -/
theorem moveAt_reaches {γ : World} {w : Node} {m : Move} (h : M.MoveAt γ w m) : M.Reaches γ w := by
  unfold GameModel.Reaches DclegProofs.Reaches History.nodes
  unfold GameModel.MoveAt DclegProofs.MoveAt at h
  exact List.mem_append_left _ (List.mem_map.mpr ⟨(w, m), h, rfl⟩)

/-- History condition 2: the move made at w is available at w. -/
theorem moveAt_pmoves {γ : World} {w : Node} {m : Move} (h : M.MoveAt γ w m) : M.T.PMoves w m :=
  (M.H_wf γ).moves_possible (w, m) h

/-- So next(w, Move(γ,w)) is defined (condition 3). -/
theorem moveAt_next_defined {γ : World} {w : Node} {m : Move} (h : M.MoveAt γ w m) :
    ∃ w', M.T.next w m = some w' :=
  (M.T.cond3 w m).mpr (moveAt_pmoves h)

/-- A node at which a move is made is not an outcome node (condition 2). -/
theorem moveAt_not_end {γ : World} {w : Node} {m : Move} (h : M.MoveAt γ w m) : ¬ M.T.EndV w := by
  intro hend
  exact ((M.T.cond2 w).mpr hend) m (moveAt_pmoves h)

/-- At a reached node that is not the outcome, the history makes a move. -/
theorem reaches_move_of_not_end {γ : World} {w : Node} (hr : M.Reaches γ w) (hne : ¬ M.T.EndV w) :
    ∃ m, M.MoveAt γ w m := by
  unfold GameModel.Reaches DclegProofs.Reaches History.nodes at hr
  rcases List.mem_append.mp hr with h | h
  · obtain ⟨⟨v, m⟩, hvm, rfl⟩ := List.mem_map.mp h
    exact ⟨m, hvm⟩
  · have : w = (M.H γ).outcome := by simpa using h
    exact absurd (this ▸ (M.H_wf γ).outcome_end) hne

/-- The node after a move on a path is on the path (or is its endpoint). -/
theorem PathFrom.next_mem {T : StrategicStructure Agent Move Node} {a e : Node}
    {steps : List (Node × Move)} (h : PathFrom T a steps e) {w w' : Node} {m : Move}
    (hw : (w, m) ∈ steps) (hnext : T.next w m = some w') :
    w' ∈ steps.map Prod.fst ++ [e] := by
  induction h with
  | nil => simp at hw
  | @cons v mv v' rest e' hv hrest ih =>
    rcases List.mem_cons.mp hw with heq | hmem
    · cases heq
      have : w' = v' := Option.some.inj (hnext.symm.trans hv)
      subst this
      cases hrest with
      | nil => simp
      | cons _ _ => simp
    · exact List.mem_cons_of_mem _ (ih hmem)

/-- If Move(γ, w) = m and next(w, m) = w′ then w′ ∈ V_γ. -/
theorem reaches_next {γ : World} {w w' : Node} {m : Move}
    (hm : M.MoveAt γ w m) (hnext : M.T.next w m = some w') : M.Reaches γ w' := by
  obtain ⟨_, _, hpath⟩ := (M.H_wf γ).root_path
  exact hpath.next_mem hm hnext

/-- The outcome node of H(γ) is reached in γ. -/
theorem outcome_reaches (γ : World) : M.Reaches γ (M.H γ).outcome := by
  unfold GameModel.Reaches DclegProofs.Reaches History.nodes
  exact List.mem_append_right _ (List.mem_singleton.mpr rfl)

/-- A non-empty path ends with a move into its endpoint. -/
theorem PathFrom.last_step {T : StrategicStructure Agent Move Node} {w e : Node}
    {steps : List (Node × Move)} (h : PathFrom T w steps e) (hne : steps ≠ []) :
    ∃ v m, T.next v m = some e := by
  induction h with
  | nil => exact absurd rfl hne
  | @cons w m w' rest e hnext hrest ih =>
    cases rest with
    | nil => cases hrest; exact ⟨w, m, hnext⟩
    | cons p rest' => exact ih (List.cons_ne_nil _ _)

/-- The first node of a non-empty path is the path's start. -/
theorem PathFrom.head_mem {T : StrategicStructure Agent Move Node} {w e : Node}
    {steps : List (Node × Move)} (h : PathFrom T w steps e) (hne : steps ≠ []) :
    w ∈ steps.map Prod.fst := by
  cases h with
  | nil => exact absurd rfl hne
  | cons _ _ => simp

/-- The root of H(γ) is reached in γ, and it is not the outcome: histories
have at least one move (a history's sequence is non-empty), and the root has
no predecessor while the outcome has one. -/
theorem root_reaches_ne_outcome (γ : World) :
    ∃ r, M.Reaches γ r ∧ r ≠ (M.H γ).outcome := by
  obtain ⟨r, hroot, hpath⟩ := (M.H_wf γ).root_path
  refine ⟨r, ?_, ?_⟩
  · unfold GameModel.Reaches DclegProofs.Reaches History.nodes
    exact List.mem_append_left _ (hpath.head_mem (M.H_wf γ).nonempty)
  · intro heq
    obtain ⟨v, m, hvm⟩ := hpath.last_step (M.H_wf γ).nonempty
    exact hroot v m (heq ▸ hvm)

/-! ## `end` and `X⊤` (p. 21)

> If w ∈ EndV, then we will have M, γ, w ⊩ □¬X⊤, as no world which reaches
> w reaches any point after w. If w ∉ EndV, we know that the world must
> progress past w, and so we will have M, γ, w ⊩ X⊤. Thus, the abbreviation
> end captures, as desired, exactly the outcome nodes. -/

/-- X⊤ holds at a reached node exactly when it is not an outcome node. -/
theorem sat_nextTop_iff {γ : World} {w : Node} (hγ : M.Reaches γ w) :
    sat M γ w (next top) ↔ ¬ M.T.EndV w := by
  constructor
  · intro ⟨m, _, hm, _, _⟩
    exact moveAt_not_end hm
  · intro hne
    obtain ⟨m, hm⟩ := reaches_move_of_not_end hγ hne
    obtain ⟨w', hw'⟩ := moveAt_next_defined hm
    exact ⟨m, w', hm, hw', sat_top _ _⟩

/-- `end` holds at a reached node exactly when it is an outcome node. -/
theorem sat_end_iff {γ : World} {w : Node} (hγ : M.Reaches γ w) :
    sat M γ w «end» ↔ M.T.EndV w := by
  constructor
  · intro h
    have := h γ ⟨hγ, hγ⟩
    simp only [sat] at this
    exact Classical.not_not.mp (fun hne => this ((sat_nextTop_iff hγ).mpr hne))
  · intro hend β ⟨_, hβ⟩ hX
    exact (sat_nextTop_iff hβ).mp hX hend

/-! ## □ does not depend on the world (p. 23)

> Suppose M, γ, w ⊩ □φ. This means that at every world β ∈ Γ with w ∈ V_β,
> we have M, β, w ⊩ φ. Therefore, M, α, w ⊩ □φ for every α ∈ Γ. -/

theorem sat_box_iff {γ : World} {w : Node} {φ : Formula Agent Move PVar} (hγ : M.Reaches γ w) :
    sat M γ w (□ φ) ↔ ∀ β, M.Reaches β w → sat M β w φ := by
  simp only [sat]
  exact ⟨fun h β hβ => h β ⟨hγ, hβ⟩, fun h β ⟨_, hβ⟩ => h β hβ⟩

theorem box_world_indep {γ α : World} {w : Node} {φ : Formula Agent Move PVar}
    (hγ : M.Reaches γ w) (hα : M.Reaches α w) :
    sat M γ w (□ φ) ↔ sat M α w (□ φ) := by
  rw [sat_box_iff hγ, sat_box_iff hα]

/-- □φ → φ at reached nodes (the T axiom, p. 23). -/
theorem box_elim {γ : World} {w : Node} {φ : Formula Agent Move PVar} (hγ : M.Reaches γ w)
    (h : sat M γ w (□ φ)) : sat M γ w φ :=
  (sat_box_iff hγ).mp h γ hγ

/-! ## The counterfactual and validity

The four results of the thesis all have the form "φ □→ ψ is valid." Two
facts about the counterfactual clause reduce that to something simpler.

**Fact 1.** Every world in max^φ_{F(γ,w)}(Γ) satisfies φ (that is clause 1
of the definition on p. 19). So to show φ □→ ψ holds at *every* pointed
model, it is enough to show that φ → ψ holds at every pointed model.
This is `valid_cf_of_imp`. The hand proofs of Theorem 4.2 (p. 33) and
Theorem 5.1 (p. 41) end by splitting into "□¬φ, so vacuous" and
"◇φ, so by contemporary universality there are maximally φ-consistent
worlds, and the argument applies to them"; Fact 1 shows neither the case
split nor contemporary universality is needed for that final step.

**Fact 2** (p. 19: "centering guarantees that if (γ,w) ∈ ⟦φ⟧, then
max^φ_{F(γ,w)}(Γ) = {(γ,w)}"). Proved as `maxConsistent_of_sat` (γ is in
the set) and `maxConsistent_eq_of_sat` (nothing else is). Its consequence
`valid_cf_iff`: a counterfactual φ □→ ψ is valid *if and only if* the
material conditional φ → ψ is. For validity, then, □→ and → are
interchangeable; they differ only pointwise. -/

/-- Every maximally φ-consistent world satisfies φ. -/
theorem maxConsistent_sat {γ β : World} {w : Node} {φ : Formula Agent Move PVar}
    (h : M.MaxConsistent γ w (extension M φ) β) : M.Reaches β w ∧ sat M β w φ :=
  h.1

/-- Fact 1: if φ → ψ holds at every pointed model, φ □→ ψ is valid. -/
theorem valid_cf_of_imp {φ ψ : Formula Agent Move PVar}
    (h : ∀ (Node World : Type) (M : GameModel Agent Move Node World PVar sig) (γ : World) (w : Node),
      M.Reaches γ w → sat M γ w φ → sat M γ w ψ) :
    Valid sig (φ □→ ψ) := by
  intro Node World M γ w _ β hβ
  exact h Node World M β w hβ.1.1 hβ.1.2

/-- Centering forces F(γ, w) to be non-empty at reached pairs (Q4, Q7):
otherwise ⋂F(γ,w) would contain every reached pair, and there are at least
two of them in γ (the root and the outcome). -/
theorem F_nonempty {γ : World} {w : Node} (hγ : M.Reaches γ w) : ∃ Y, M.F γ w Y := by
  apply Classical.byContradiction
  intro hno
  have vac : ∀ p : World × Node, M.Reaches p.1 p.2 → p = (γ, w) := fun p hp =>
    (M.centering γ w hγ p hp).mp (fun Y hY => absurd ⟨Y, hY⟩ hno)
  obtain ⟨r, hr, hne⟩ := root_reaches_ne_outcome (M := M) γ
  have h1 := vac (γ, r) hr
  have h2 := vac (γ, (M.H γ).outcome) (outcome_reaches γ)
  exact hne (by cases h1; cases h2; rfl)

/-- Fact 2, half one: if M, γ, w ⊩ φ then γ ∈ max^φ_{F(γ,w)}(Γ).
The witness G is F(γ,w) itself: non-empty by `F_nonempty`, ⋂F(γ,w) ∋ (γ,w)
by centering, and no strict superset of F(γ,w) lies inside F(γ,w). -/
theorem maxConsistent_of_sat {γ : World} {w : Node} {φ : Formula Agent Move PVar}
    (hγ : M.Reaches γ w) (hφ : sat M γ w φ) : M.MaxConsistent γ w (extension M φ) γ := by
  refine ⟨⟨hγ, hφ⟩, M.F γ w, F_nonempty hγ, fun _ h => h, ?_, ?_⟩
  · exact (M.centering γ w hγ (γ, w) hγ).mpr rfl
  · intro G' _ ⟨Y, hY, hYF⟩ hsub _ _ _
    exact hYF (hsub Y hY)

/-- Fact 2, half two: if M, γ, w ⊩ φ then γ is the *only* maximally
φ-consistent world. Either the witness G is all of F(γ,w), and then
β ∈ ⋂F(γ,w) = {(γ,w)}; or it is not, and then F(γ,w) itself is a strict
superset of G inside F(γ,w) whose intersection contains the φ-world (γ,w),
contradicting maximality. -/
theorem maxConsistent_eq_of_sat {γ β : World} {w : Node} {φ : Formula Agent Move PVar}
    (hγ : M.Reaches γ w) (hφ : sat M γ w φ)
    (hβ : M.MaxConsistent γ w (extension M φ) β) : β = γ := by
  obtain ⟨⟨hβr, _⟩, G, _, hGF, hβG, hmax⟩ := hβ
  by_cases hall : ∀ Y, M.F γ w Y → G Y
  · have : (β, w) = (γ, w) :=
      (M.centering γ w hγ (β, w) hβr).mp (fun Y hY => hβG Y (hall Y hY))
    cases this; rfl
  · obtain ⟨Y, hYF, hYG⟩ := Classical.not_forall.mp hall |>.imp fun _ h => Classical.not_imp.mp h
    exact (hmax (M.F γ w) hGF ⟨Y, hYF, hYG⟩ (fun _ h => h) (γ, w)
      ((M.centering γ w hγ (γ, w) hγ).mpr rfl) ⟨hγ, hφ⟩).elim

/-- φ □→ ψ at a world where φ holds is just ψ there (p. 21: "In this case,
M, γ, w ⊩ φ □→ ψ when M, γ, w ⊩ ψ"). -/
theorem sat_cf_of_sat {γ : World} {w : Node} {φ ψ : Formula Agent Move PVar}
    (hγ : M.Reaches γ w) (hφ : sat M γ w φ) :
    sat M γ w (φ □→ ψ) ↔ sat M γ w ψ := by
  constructor
  · intro h; exact h γ (maxConsistent_of_sat hγ hφ)
  · intro h β hβ
    have := maxConsistent_eq_of_sat hγ hφ hβ
    subst this; exact h

/-- φ □→ ψ is valid iff φ → ψ holds at every pointed model. -/
theorem valid_cf_iff {φ ψ : Formula Agent Move PVar} :
    Valid sig (φ □→ ψ) ↔
      ∀ (Node World : Type) (M : GameModel Agent Move Node World PVar sig) (γ : World) (w : Node),
        M.Reaches γ w → sat M γ w φ → sat M γ w ψ := by
  constructor
  · intro h Node World M γ w hγ hφ
    exact h Node World M γ w hγ γ (maxConsistent_of_sat hγ hφ)
  · exact valid_cf_of_imp

/-! ## Maximal premise sets exist (p. 22), and cautious monotonicity

Page 22 argues: "Contemporary universality says that every such β is
m′-consistent with a non-empty subset of F(γ,w), so there will be at least
one world which is maximally m′-consistent with F(γ,w)." The step from
"consistent with some G" to "consistent with a *maximal* G" needs F(γ,w)
finite (Q6), and it needs one more thing.

**QUESTION FOR JEREMIAH (Q12, maximality across nodes).** Clause 2(b) on
p. 19 says every strict superset G′ has (⋂G′) ∩ ⟦φ⟧ = ∅, where ⟦φ⟧ ranges
over pairs at *every* node. Premises are arbitrary subsets of I, so a
premise may contain pairs at other nodes. Then a G whose intersection
contains an m′-world at w can have a superset whose intersection contains
an m′-pair at some other node v, and no G is maximal. Concretely, with
Y₁ = {(γ,w),(β,w),(δ,w),(δ,v)}, Y₂ = {(γ,w),(δ,v)}, Y₃ = {(γ,w)} as
F(γ,w), where β and δ play m′ at w and δ plays m′ again at v: centering
and contemporary universality hold, the only G with an m′-world at w in
⋂G is {Y₁}, and {Y₁,Y₂} ⊋ {Y₁} has (δ,v) ∈ ⋂{Y₁,Y₂} ∩ ⟦m′⟧. So
max^{m′}_{F(γ,w)}(Γ) = ∅ although ◇m′ holds, and m′ □→ ⊥ is true at
(γ,w). This is not only argued in prose: `Q12Example.lean` builds this
model (five nodes, three worlds), has Lean check every `GameModel`
condition on it, and proves `dia_move'`, `no_maxConsistent` and `cf_bot`
about it. The p. 22 claim therefore fails under the literal reading. It
holds if premises are *node-local*, i.e. every
premise in F(γ,w) contains only pairs at w (`LocalPremises` below), or
equivalently if 2(b) reads (⋂G′) ∩ ⟦φ⟧ ∩ (Γ × {w}) = ∅. Which is intended?
The proof of Theorem 4.2 uses the p. 22 claim (p. 32, "Then clearly
M, γ, w ⊩ B^E ◇X R^n"), so the answer matters there. -/

/-- Every premise in F(γ, w) contains only pairs at w. -/
def LocalPremises (M : GameModel Agent Move Node World PVar sig) (γ : World) (w : Node) : Prop :=
  ∀ Y, M.F γ w Y → ∀ p, Y p → p.2 = w

/-- Any G ⊆ F(γ,w) whose intersection meets X extends to a G'' ⊆ F(γ,w)
whose intersection still meets X and to which no further premise can be
added without losing that. By induction on the finite list of premises. -/
theorem exists_maximal_extension {γ : World} {w : Node} (X : World × Node → Prop)
    (G : (World × Node → Prop) → Prop) (hGF : ∀ Y, G Y → M.F γ w Y)
    (hwit : ∃ p, (∀ Y, G Y → Y p) ∧ X p) :
    ∃ G'' : (World × Node → Prop) → Prop,
      (∀ Y, G Y → G'' Y) ∧ (∀ Y, G'' Y → M.F γ w Y) ∧ (∃ p, (∀ Y, G'' Y → Y p) ∧ X p) ∧
      ∀ Y, M.F γ w Y → ¬ G'' Y → ¬ ∃ p, (∀ Z, (G'' Z ∨ Z = Y) → Z p) ∧ X p := by
  obtain ⟨l, hl⟩ := M.F_finite γ w
  suffices key : ∀ (l' : List (World × Node → Prop)) (G : (World × Node → Prop) → Prop),
      (∀ Y, G Y → M.F γ w Y) → (∃ p, (∀ Y, G Y → Y p) ∧ X p) →
      ∃ G'' : (World × Node → Prop) → Prop,
        (∀ Y, G Y → G'' Y) ∧ (∀ Y, G'' Y → M.F γ w Y) ∧ (∃ p, (∀ Y, G'' Y → Y p) ∧ X p) ∧
        ∀ Y ∈ l', M.F γ w Y → ¬ G'' Y → ¬ ∃ p, (∀ Z, (G'' Z ∨ Z = Y) → Z p) ∧ X p by
    obtain ⟨G'', h1, h2, h3, h4⟩ := key l G hGF hwit
    exact ⟨G'', h1, h2, h3, fun Y hY => h4 Y (hl Y hY) hY⟩
  intro l'
  induction l' with
  | nil =>
    intro G hGF hwit
    exact ⟨G, fun _ h => h, hGF, hwit, fun Y hY => absurd hY (by simp)⟩
  | cons Y rest ih =>
    intro G hGF hwit
    obtain ⟨G₁, h1, h2, h3, h4⟩ := ih G hGF hwit
    by_cases hstop : ¬ M.F γ w Y ∨ G₁ Y ∨ ¬ ∃ p, (∀ Z, (G₁ Z ∨ Z = Y) → Z p) ∧ X p
    · refine ⟨G₁, h1, h2, h3, ?_⟩
      intro Z hZ hZF hZG
      rcases List.mem_cons.mp hZ with rfl | hZr
      · rcases hstop with h | h | h
        · exact absurd hZF h
        · exact absurd h hZG
        · exact h
      · exact h4 Z hZr hZF hZG
    · have hYF : M.F γ w Y := Classical.byContradiction fun h => hstop (Or.inl h)
      have hwit2 : ∃ p, (∀ Z, (G₁ Z ∨ Z = Y) → Z p) ∧ X p :=
        Classical.byContradiction fun h => hstop (Or.inr (Or.inr h))
      refine ⟨fun Z => G₁ Z ∨ Z = Y, fun Z hZ => Or.inl (h1 Z hZ), ?_, hwit2, ?_⟩
      · intro Z hZ
        rcases hZ with hZ | rfl
        · exact h2 Z hZ
        · exact hYF
      · intro Z hZ hZF hZG
        rcases List.mem_cons.mp hZ with rfl | hZr
        · exact absurd (Or.inr rfl) hZG
        · have hZG₁ : ¬ G₁ Z := fun h => hZG (Or.inl h)
          intro ⟨p, hp, hX⟩
          refine h4 Z hZr hZF hZG₁ ⟨p, fun W hW => hp W ?_, hX⟩
          rcases hW with hW | hW
          · exact Or.inl (Or.inl hW)
          · exact Or.inr hW

/-- The p. 22 claim, under node-local premises: a world β that reaches w,
satisfies X at w, and lies in some premise of F(γ,w), guarantees a world
maximally X-consistent with γ at w. -/
theorem exists_maxConsistent_of_local {γ β : World} {w : Node} (X : World × Node → Prop)
    (hloc : LocalPremises M γ w) {Y : World × Node → Prop} (hYF : M.F γ w Y)
    (hβY : Y (β, w)) (hβX : X (β, w)) :
    ∃ β', M.MaxConsistent γ w X β' := by
  obtain ⟨G'', hsub, hGF, ⟨p, hp, hpX⟩, hmax⟩ :=
    exists_maximal_extension (M := M) X (fun Z => Z = Y) (fun Z hZ => hZ ▸ hYF)
      ⟨(β, w), fun Z hZ => hZ ▸ hβY, hβX⟩
  obtain ⟨β', v⟩ := p
  have hv : v = w := hloc Y (hGF Y (hsub Y rfl)) (β', v) (hp Y (hsub Y rfl))
  subst v
  refine ⟨β', hpX, G'', ⟨Y, hsub Y rfl⟩, hGF, hp, ?_⟩
  intro G' hG'sup ⟨Z, hZ, hZn⟩ hG'F q hq hqX
  refine hmax Z (hG'F Z hZ) hZn ⟨q, fun W hW => hq W ?_, hqX⟩
  rcases hW with hW | rfl
  · exact hG'sup W hW
  · exact hZ

/-- ◇φ gives a maximally φ-consistent world (p. 22), under node-local
premises, via contemporary universality. -/
theorem exists_maxConsistent_of_dia {γ : World} {w : Node} {φ : Formula Agent Move PVar}
    (hloc : LocalPremises M γ w) (hγ : M.Reaches γ w) (h : sat M γ w (◇ φ)) :
    ∃ β', M.MaxConsistent γ w (extension M φ) β' := by
  obtain ⟨β, hβ, hφ⟩ := (sat_dia hγ).mp h
  obtain ⟨Y, hYF, hβY⟩ := M.contemporary_universality β γ w hβ
  exact exists_maxConsistent_of_local (extension M φ) hloc hYF hβY ⟨hβ, hφ⟩

/-- Strengthening by something true throughout max^φ: a world maximally
φ-consistent that also satisfies χ is maximally (φ ∧ χ)-consistent. No
side conditions; this is the direction used at (4.19)–(4.20) on p. 33. -/
theorem maxConsistent_and_of_sat {γ β : World} {w : Node} {φ χ : Formula Agent Move PVar}
    (hβ : M.MaxConsistent γ w (extension M φ) β) (hχ : sat M β w χ) :
    M.MaxConsistent γ w (extension M (φ ∧' χ)) β := by
  obtain ⟨⟨hβr, hβφ⟩, G, hGne, hGF, hβG, hmax⟩ := hβ
  refine ⟨⟨hβr, sat_and.mpr ⟨hβφ, hχ⟩⟩, G, hGne, hGF, hβG, ?_⟩
  intro G' hsup hstrict hG'F p hp hpX
  exact hmax G' hsup hstrict hG'F p hp ⟨hpX.1, (sat_and.mp hpX.2).1⟩

/-- Cautious monotonicity: if every maximally φ-consistent world satisfies
χ (φ □→ χ), then every maximally (φ ∧ χ)-consistent world is maximally
φ-consistent; so (φ □→ ψ) ∧ (φ □→ χ) gives (φ ∧ χ) □→ ψ. This is the
inference at (5.6) on p. 41. It needs node-local premises (Q12) and
finiteness (Q6), to extend a competing G′ to a maximal one. -/
theorem maxConsistent_of_and_of_local {γ β : World} {w : Node} {φ χ : Formula Agent Move PVar}
    (hloc : LocalPremises M γ w)
    (hχ : ∀ β', M.MaxConsistent γ w (extension M φ) β' → sat M β' w χ)
    (hβ : M.MaxConsistent γ w (extension M (φ ∧' χ)) β) :
    M.MaxConsistent γ w (extension M φ) β := by
  obtain ⟨⟨hβr, hβφχ⟩, G, ⟨Y, hY⟩, hGF, hβG, hmax⟩ := hβ
  refine ⟨⟨hβr, (sat_and.mp hβφχ).1⟩, G, ⟨Y, hY⟩, hGF, hβG, ?_⟩
  intro G' hsup hstrict hG'F p hp hpX
  obtain ⟨G'', hsub, hG''F, ⟨q, hq, hqX⟩, hmax''⟩ :=
    exists_maximal_extension (M := M) (extension M φ) G' hG'F ⟨p, hp, hpX⟩
  obtain ⟨β'', v⟩ := q
  have hYG'' : G'' Y := hsub Y (hsup Y hY)
  have hv : v = w := hloc Y (hG''F Y hYG'') (β'', v) (hq Y hYG'')
  subst v
  have hβ''max : M.MaxConsistent γ w (extension M φ) β'' := by
    refine ⟨hqX, G'', ⟨Y, hYG''⟩, hG''F, hq, ?_⟩
    intro G₃ hsup3 ⟨Z3, hZ3, hZ3n⟩ hG3F r hr hrX
    refine hmax'' Z3 (hG3F Z3 hZ3) hZ3n ⟨r, fun W hW => hr W ?_, hrX⟩
    rcases hW with hW | rfl
    · exact hsup3 W hW
    · exact hZ3
  obtain ⟨Z, hZ, hZn⟩ := hstrict
  exact hmax G'' (fun W hW => hsub W (hsup W hW)) ⟨Z, hsub Z hZ, hZn⟩ hG''F (β'', w) hq
    ⟨hqX.1, sat_and.mpr ⟨hqX.2, hχ β'' hβ''max⟩⟩

/-! ## Belief (§3.2.4, p. 22): D, 4, 5, C4, and the □ interactions (p. 23)

The thesis lists these as counterfactual validities. By `valid_cf_iff`
each is equivalent to the material form proved here. Each proof names the
frame condition it uses, which is what one expects from the KD45 analogy:
Present Seriality for D, Transitivity for 4, Euclideanness for 5 and C4. -/

/-- Presence, read forward: every world i considers plausible at w reaches w. -/
theorem dox_reaches {i : Agent} {w : Node} {γ μ : World} (h : M.dox i w γ μ) : M.Reaches μ w :=
  Classical.not_not.mp (fun hn => M.presence i w μ hn γ h)

/-- Transitivity and Euclideanness together: the plausible worlds of a
plausible world are exactly one's own. -/
theorem dox_cluster {i : Agent} {w : Node} {γ μ ν : World} (h : M.dox i w γ μ) :
    M.dox i w μ ν ↔ M.dox i w γ ν :=
  ⟨fun h' => M.transitivity i w γ μ ν h h', fun h' => M.euclidean i w γ μ ν h h'⟩

/-- Bᵢφ has the same value at γ and at any world i considers plausible at
w: both quantify over the same cluster (`dox_cluster`). -/
theorem sat_bel_of_dox {γ μ : World} {w : Node} {i : Agent} {φ : Formula Agent Move PVar}
    (hγ : M.Reaches γ w) (hμ : M.dox i w γ μ) :
    sat M μ w (bel i φ) ↔ sat M γ w (bel i φ) := by
  simp only [sat_bel, dox_cluster hμ, hγ, dox_reaches hμ, true_and]

/-- Likewise for B̂ᵢφ. -/
theorem sat_dbel_of_dox {γ μ : World} {w : Node} {i : Agent} {φ : Formula Agent Move PVar}
    (hγ : M.Reaches γ w) (hμ : M.dox i w γ μ) :
    sat M μ w (dbel i φ) ↔ sat M γ w (dbel i φ) := by
  simp only [dbel, sat_neg, sat_bel_of_dox hγ hμ]

/-- Counterfactual D, material form: Bᵢφ → B̂ᵢφ. Uses Present Seriality. -/
theorem bel_D {γ : World} {w : Node} {i : Agent} {φ : Formula Agent Move PVar}
    (hγ : M.Reaches γ w) (h : sat M γ w (bel i φ)) : sat M γ w (dbel i φ) := by
  rw [sat_dbel hγ]
  obtain ⟨μ, hμ⟩ := M.present_seriality i w γ hγ
  exact ⟨μ, hμ, h.2 μ hμ⟩

/-- Counterfactual 4, material form: Bᵢφ → BᵢBᵢφ. Uses Transitivity. -/
theorem bel_4 {γ : World} {w : Node} {i : Agent} {φ : Formula Agent Move PVar}
    (h : sat M γ w (bel i φ)) : sat M γ w (bel i (bel i φ)) := by
  refine ⟨h.1, fun μ hμ => ⟨dox_reaches hμ, fun ν hν => ?_⟩⟩
  exact h.2 ν (M.transitivity i w γ μ ν hμ hν)

/-- Counterfactual 5, material form: B̂ᵢφ → BᵢB̂ᵢφ. Uses Euclideanness. -/
theorem bel_5 {γ : World} {w : Node} {i : Agent} {φ : Formula Agent Move PVar}
    (hγ : M.Reaches γ w) (h : sat M γ w (dbel i φ)) : sat M γ w (bel i (dbel i φ)) := by
  obtain ⟨μ, hμ, hφ⟩ := (sat_dbel hγ).mp h
  refine ⟨hγ, fun ν hν => ?_⟩
  rw [sat_dbel (dox_reaches hν)]
  exact ⟨μ, M.euclidean i w γ ν μ hν hμ, hφ⟩

/-- Counterfactual C4, material form: BᵢBᵢφ → Bᵢφ. Uses Euclideanness
(every plausible world considers itself plausible). -/
theorem bel_C4 {γ : World} {w : Node} {i : Agent} {φ : Formula Agent Move PVar}
    (h : sat M γ w (bel i (bel i φ))) : sat M γ w (bel i φ) :=
  ⟨h.1, fun μ hμ => (h.2 μ hμ).2 μ (M.euclidean i w γ μ μ hμ hμ)⟩

/-- ¬Bᵢ□φ ∨ □φ (p. 23): belief in a necessity is correct. Uses Present
Seriality and Presence, plus the world-independence of □. -/
theorem bel_box_imp_box {γ : World} {w : Node} {i : Agent} {φ : Formula Agent Move PVar}
    (hγ : M.Reaches γ w) (h : sat M γ w (bel i (□ φ))) : sat M γ w (□ φ) := by
  obtain ⟨μ, hμ⟩ := M.present_seriality i w γ hγ
  exact (box_world_indep hγ (dox_reaches hμ)).mpr (h.2 μ hμ)

/-- ¬□φ ∨ Bᵢ□φ (p. 23). -/
theorem box_imp_bel_box {γ : World} {w : Node} {i : Agent} {φ : Formula Agent Move PVar}
    (hγ : M.Reaches γ w) (h : sat M γ w (□ φ)) : sat M γ w (bel i (□ φ)) :=
  ⟨hγ, fun _ hμ => (box_world_indep hγ (dox_reaches hμ)).mp h⟩

/-- ¬□φ ∨ Bᵢφ (p. 23). -/
theorem box_imp_bel {γ : World} {w : Node} {i : Agent} {φ : Formula Agent Move PVar}
    (hγ : M.Reaches γ w) (h : sat M γ w (□ φ)) : sat M γ w (bel i φ) :=
  ⟨hγ, fun μ hμ => (sat_box_iff hγ).mp h μ (dox_reaches hμ)⟩

/-- Bᵢ◇φ → ◇φ, the form of "by perfect information" used on p. 32:
◇ is world-independent, and some plausible world exists. -/
theorem bel_dia_imp_dia {γ : World} {w : Node} {i : Agent} {φ : Formula Agent Move PVar}
    (hγ : M.Reaches γ w) (h : sat M γ w (bel i (◇ φ))) : sat M γ w (◇ φ) := by
  obtain ⟨μ, hμ⟩ := M.present_seriality i w γ hγ
  have hμd := h.2 μ hμ
  rw [sat_dia (dox_reaches hμ)] at hμd
  rw [sat_dia hγ]
  exact hμd

/-! ## Histories are simple paths; `Move` is a function (Q3)

Page 17 argues that the tree conditions rule out loops, so a history never
visits a node twice, and `Move(γ, w)` is well defined. The Lean has `MoveAt`
as a relation (Q3); here we prove the relation is functional, so the
∃-readings of the X clause and the frame conditions agree with the
thesis's functional ones. The argument: a node on a path from the root
that is visited twice would lie on a cycle; but no node reachable from the
root lies on a cycle, because following the cycle backwards (condition 5,
no merging) would give the root a predecessor. -/

/-- `Reach T a b`: b is reachable from a by zero or more moves. Built from
the *end*: a step is appended after a reachability derivation. -/
inductive Reach {Agent Move Node : Type} (T : StrategicStructure Agent Move Node) (a : Node) : Node → Prop
  | refl : Reach T a a
  | snoc {b c : Node} {m : Move} : Reach T a b → T.next b m = some c → Reach T a c

theorem Reach.trans {T : StrategicStructure Agent Move Node} {a b c : Node}
    (h1 : Reach T a b) (h2 : Reach T b c) : Reach T a c := by
  induction h2 with
  | refl => exact h1
  | snoc _ hstep ih => exact Reach.snoc ih hstep

/-- Every node listed on a path is reachable from the path's start. -/
theorem PathFrom.reach_of_mem {T : StrategicStructure Agent Move Node} {a e : Node}
    {steps : List (Node × Move)} (h : PathFrom T a steps e) {v : Node} {m : Move}
    (hv : (v, m) ∈ steps) : Reach T a v := by
  induction h with
  | nil => simp at hv
  | @cons w m' w' rest e' hnext _ ih =>
    rcases List.mem_cons.mp hv with heq | hmem
    · cases heq; exact Reach.refl
    · exact Reach.trans (Reach.snoc Reach.refl hnext) (ih hmem)

/-- No node reachable from the root lies on a cycle. -/
theorem no_cycle_from_root {T : StrategicStructure Agent Move Node} {r v : Node}
    (hroot : T.IsRoot r) (hr : Reach T r v) :
    ¬ ∃ (m : Move) (v' : Node), T.next v m = some v' ∧ Reach T v' v := by
  induction hr with
  | refl =>
    rintro ⟨m, v', hnext, hback⟩
    cases hback with
    | refl => exact T.cond4 _ _ hnext
    | snoc _ hstep => exact hroot _ _ hstep
  | @snoc u v m hru hstep ih =>
    rintro ⟨m1, v1, hnext1, hback⟩
    cases hback with
    | refl => exact T.cond4 _ _ hnext1
    | @snoc b _ m' hv1b hbv =>
      obtain ⟨rfl, _⟩ := T.cond5 _ _ _ _ _ hstep hbv
      exact ih ⟨m, v, hstep, Reach.trans (Reach.snoc Reach.refl hnext1) hv1b⟩

/-- Two different moves at the same node on one path would put the node
on a cycle. -/
theorem PathFrom.cycle_of_two_moves {T : StrategicStructure Agent Move Node} {a e : Node}
    {steps : List (Node × Move)} (h : PathFrom T a steps e) {v : Node} {m m' : Move}
    (h1 : (v, m) ∈ steps) (h2 : (v, m') ∈ steps) (hne : m ≠ m') :
    ∃ (m₀ : Move) (v' : Node), T.next v m₀ = some v' ∧ Reach T v' v := by
  induction h with
  | nil => simp at h1
  | @cons w mw w' rest e' hnext hrest ih =>
    rcases List.mem_cons.mp h1 with e1 | r1 <;> rcases List.mem_cons.mp h2 with e2 | r2
    · cases e1; cases e2; exact absurd rfl hne
    · cases e1; exact ⟨_, w', hnext, hrest.reach_of_mem r2⟩
    · cases e2; exact ⟨_, w', hnext, hrest.reach_of_mem r1⟩
    · exact ih r1 r2

/-- Move(γ, w) is a function: at most one move is made at w in H(γ). -/
theorem moveAt_unique {γ : World} {w : Node} {m m' : Move}
    (h1 : M.MoveAt γ w m) (h2 : M.MoveAt γ w m') : m = m' := by
  apply Classical.byContradiction
  intro hne
  obtain ⟨r, hroot, hpath⟩ := (M.H_wf γ).root_path
  exact no_cycle_from_root hroot (hpath.reach_of_mem h1) (hpath.cycle_of_two_moves h1 h2 hne)

end DclegProofs
