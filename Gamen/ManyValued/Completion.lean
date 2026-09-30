import Gamen.ManyValued

/-!
# Completions of partial valuations (Lean-only)

Spec: `docs/superpowers/specs/2026-09-30-gv-phase2-missing-data-design.md`.
A partial valuation gives each atom t, f or u (unknown). A completion fills
in every u classically. Strong Kleene (K3) `[thr:skl, defn 1]` is sound for
completions but not complete:

- a K3 value of t (f) means true (false) in *every* completion
  (`definite_sound`, `absent_sound`), so a formula true in some completion
  and false in another is u (`mixed_possible`);
- the converse fails: `p ∧ ¬p` is u with `p` unknown, yet false in every
  completion (`Tests/Completion.lean`, theorem 5).

`exactStatus` measures the gap by enumerating completions, optionally under
`exactlyOne` constraints (one value per enumerated fact). The soundness
theorems quantify over all completions, so they hold a fortiori for the
admissible ones.

Built for `decide`, like `Gamen.ManyValued`: no `TreeSet`, structural
recursion only.
-/

open Gamen

namespace Gamen.ManyValued

/-- `c` completes `p`: it keeps every known value and fills in each `u`. -/
def Completes (p : Atom → TV3) (c : Atom → Bool) : Prop :=
  ∀ a, p a = .u ∨ p a = TV3.ofBool (c a)

/-- The information order: `u` below everything, `t` and `f` incomparable. -/
def TV3.le : TV3 → TV3 → Bool
  | .u, _ => true
  | .t, .t => true
  | .f, .f => true
  | _, _ => false

/-- The K3 tables are monotone in the information order (checked by `decide`). -/
theorem strongKleene_tables_monotone :
    (∀ a c, TV3.le a c = true → TV3.le (negK a) (negK c) = true) ∧
    (∀ a b c d, TV3.le a c = true → TV3.le b d = true → TV3.le (conjK3 a b) (conjK3 c d) = true) ∧
    (∀ a b c d, TV3.le a c = true → TV3.le b d = true → TV3.le (disjK3 a b) (disjK3 c d) = true) ∧
    (∀ a b c d, TV3.le a c = true → TV3.le b d = true → TV3.le (implK3 a b) (implK3 c d) = true) := by
  decide

/-- **Theorem 1 (monotonicity).** Refining unknowns never changes a t or f. -/
theorem strongKleene_monotone {p q : Atom → TV3} (hpq : ∀ a, TV3.le (p a) (q a) = true) :
    ∀ f, isCore f = true → ∃ x y, eval strongKleene p f = .ok x ∧
      eval strongKleene q f = .ok y ∧ TV3.le x y = true := by
  intro f hf
  obtain ⟨m1, m2, m3, m4⟩ := strongKleene_tables_monotone
  induction f with
  | atomF a => exact ⟨p a, q a, rfl, rfl, hpq a⟩
  | not a ih =>
    obtain ⟨x, y, hx, hy, hle⟩ := ih hf
    exact ⟨_, _, eval_not_ok hx, eval_not_ok hy, m1 x y hle⟩
  | and a b iha ihb =>
    simp only [isCore, Bool.and_eq_true] at hf
    obtain ⟨x, y, hx, hy, h1⟩ := iha hf.1
    obtain ⟨x', y', hx', hy', h2⟩ := ihb hf.2
    exact ⟨_, _, eval_and_ok hx hx', eval_and_ok hy hy', m2 x x' y y' h1 h2⟩
  | or a b iha ihb =>
    simp only [isCore, Bool.and_eq_true] at hf
    obtain ⟨x, y, hx, hy, h1⟩ := iha hf.1
    obtain ⟨x', y', hx', hy', h2⟩ := ihb hf.2
    exact ⟨_, _, eval_or_ok hx hx', eval_or_ok hy hy', m3 x x' y y' h1 h2⟩
  | implies a b iha ihb =>
    simp only [isCore, Bool.and_eq_true] at hf
    obtain ⟨x, y, hx, hy, h1⟩ := iha hf.1
    obtain ⟨x', y', hx', hy', h2⟩ := ihb hf.2
    exact ⟨_, _, eval_implies_ok hx hx', eval_implies_ok hy hy', m4 x x' y y' h1 h2⟩
  | _ => simp [isCore] at hf

theorem completes_le {p : Atom → TV3} {c : Atom → Bool} (hc : Completes p c) :
    ∀ a, TV3.le (p a) (TV3.ofBool (c a)) = true := by
  intro a
  rcases hc a with h | h <;> rw [h] <;> cases c a <;> rfl

/-- A completion's classical value lies above the K3 value. -/
theorem completion_value {p : Atom → TV3} {c : Atom → Bool} {f : Formula} {x : TV3}
    (hf : isCore f = true) (hc : Completes p c) (hx : eval strongKleene p f = .ok x) :
    ∃ b, eval classical c f = .ok b ∧ TV3.le x (TV3.ofBool b) = true := by
  obtain ⟨x', y, hx', hy, hle⟩ := strongKleene_monotone (completes_le hc) f hf
  obtain ⟨b, hb⟩ := eval_core_ok classical c f hf
  have hagree := strongKleene_agrees_classical c f hf
  rw [hy, hb] at hagree
  have hy' : y = TV3.ofBool b := by cases hagree; rfl
  rw [hx] at hx'
  cases hx'
  exact ⟨b, hb, hy' ▸ hle⟩

/-- **Theorem 2.** K3 value t ⇒ true in every completion. -/
theorem definite_sound {p : Atom → TV3} {c : Atom → Bool} {f : Formula}
    (hf : isCore f = true) (h : eval strongKleene p f = .ok .t) (hc : Completes p c) :
    eval classical c f = .ok true := by
  obtain ⟨b, hb, hle⟩ := completion_value hf hc h
  cases b <;> simp_all [TV3.le, TV3.ofBool]

/-- **Theorem 3.** K3 value f ⇒ false in every completion. -/
theorem absent_sound {p : Atom → TV3} {c : Atom → Bool} {f : Formula}
    (hf : isCore f = true) (h : eval strongKleene p f = .ok .f) (hc : Completes p c) :
    eval classical c f = .ok false := by
  obtain ⟨b, hb, hle⟩ := completion_value hf hc h
  cases b <;> simp_all [TV3.le, TV3.ofBool]

/-- **Theorem 4.** True in one completion and false in another ⇒ K3 value u.
(The parent plan's "possible ⇔ some but not all" is false; see the module
docstring.) -/
theorem mixed_possible {p : Atom → TV3} {c₁ c₂ : Atom → Bool} {f : Formula}
    (hf : isCore f = true) (h₁ : Completes p c₁) (h₂ : Completes p c₂)
    (e₁ : eval classical c₁ f = .ok true) (e₂ : eval classical c₂ f = .ok false) :
    eval strongKleene p f = .ok .u := by
  obtain ⟨x, hx⟩ := eval_core_ok strongKleene p f hf
  cases x with
  | t => rw [definite_sound hf hx h₂] at e₂; cases e₂
  | f => rw [absent_sound hf hx h₁] at e₁; cases e₁
  | u => exact hx

/-! ## Statuses -/

/-- The K3 verdict: t, u, f. -/
inductive K3Status where
  | definite | possible | absent
  deriving DecidableEq, Repr

/-- The verdict over admissible completions. `noAdmissibleCompletion`
means the known facts already break a constraint: a data error, never a
verdict. -/
inductive ExactStatus where
  | always | sometimes | never | noAdmissibleCompletion
  deriving DecidableEq, Repr

/-- The K3 verdict: t ↦ `definite`, u ↦ `possible`, f ↦ `absent`; errors on
a non-core formula, like `eval`. -/
def k3Status (f : Formula) (p : Atom → TV3) : Except String K3Status := do
  match ← eval strongKleene p f with
  | .t => pure .definite
  | .u => pure .possible
  | .f => pure .absent

/-- `c` makes exactly one atom of each group true. Groups should not
repeat an atom. An empty group is unsatisfiable (no completion makes
exactly one of zero atoms true), so a `cs` containing `[]` makes
`exactStatus` return `noAdmissibleCompletion`. -/
def admissible (cs : List (List Atom)) (c : Atom → Bool) : Bool :=
  cs.all fun g => (g.filter c).length == 1

/-- Every classical assignment to `atoms` that keeps `p`'s known values:
`2ᵏ` of them for `k` unknown atoms. -/
def completionsOn (p : Atom → TV3) : List Atom → List (List (Atom × Bool))
  | [] => [[]]
  | a :: as =>
    let rest := completionsOn p as
    let choices := match p a with
      | .t => [true]
      | .f => [false]
      | .u => [true, false]
    choices.flatMap fun b => rest.map fun r => (a, b) :: r

/-- The exact status of `f` over the completions of `p` that satisfy `cs`,
by enumeration over the atoms of `f` and `cs`. Errors if `f` is not
propositional. -/
def exactStatus (f : Formula) (p : Atom → TV3) (cs : List (List Atom)) :
    Except String ExactStatus := do
  unless isCore f do throw s!"ManyValued.exactStatus: {f} is not a propositional formula"
  let atoms := dedup (atomList f ++ cs.flatten)
  let asgs := (completionsOn p atoms).filter fun asg => admissible cs (lookup asg)
  let vals ← asgs.mapM fun asg => eval classical (lookup asg) f
  if vals.isEmpty then return .noAdmissibleCompletion
  if vals.all id then return .always
  if vals.all (! ·) then return .never
  return .sometimes

/-! ## Theorem 6: the enumerator is correct -/

/-- `Atom`'s derived `==` is equality (it has no `LawfulBEq` instance). -/
theorem atom_eq_of_beq {a b : Atom} (h : (a == b) = true) : a = b := by
  cases a; cases b
  revert h
  simp [BEq.beq, instBEqAtom.beq]

/-- `dedup`'s fold keeps the accumulator and adds the list. -/
theorem mem_dedup_foldl {l acc : List Atom} {a : Atom} :
    a ∈ List.foldl (fun acc a => if acc.contains a then acc else acc ++ [a]) acc l ↔
      a ∈ acc ∨ a ∈ l := by
  induction l generalizing acc with
  | nil => simp
  | cons b l ih =>
    rw [List.foldl_cons, ih]
    split <;> rename_i h
    · have hb : b ∈ acc := by
        obtain ⟨x, hx, hbx⟩ := List.contains_iff_exists_mem_beq.mp h
        exact atom_eq_of_beq hbx ▸ hx
      constructor
      · rintro (h | h)
        · exact .inl h
        · exact .inr (List.mem_cons_of_mem _ h)
      · rintro (h | h)
        · exact .inl h
        · rcases List.mem_cons.mp h with rfl | h
          · exact .inl hb
          · exact .inr h
    · simp [or_assoc]

/-- `dedup` keeps exactly the members of its input. -/
theorem mem_dedup {l : List Atom} {a : Atom} : a ∈ dedup l ↔ a ∈ l := by
  simp [dedup, mem_dedup_foldl]

/-- `eval` depends only on the valuation of the formula's atoms. -/
theorem eval_congr {V : Type} {m : Matrix V} {v w : Atom → V} (f : Formula)
    (h : ∀ a ∈ atomList.go f, v a = w a) : eval m v f = eval m w f := by
  induction f with
  | atomF a => simp [eval, h a (by simp [atomList.go])]
  | not a ih => simp only [eval]; rw [ih h]
  | and a b iha ihb | or a b iha ihb | implies a b iha ihb =>
    simp only [eval]
    rw [iha (fun x hx => h x (by simp [atomList.go, hx])),
      ihb (fun x hx => h x (by simp [atomList.go, hx]))]
  | _ => rfl

/-- An enumerated assignment keeps every known value of `p` on `as`. -/
theorem completionsOn_sound {p : Atom → TV3} {as : List Atom} {asg : List (Atom × Bool)}
    (h : asg ∈ completionsOn p as) : ∀ a ∈ as, p a = .u ∨ p a = TV3.ofBool (lookup asg a) := by
  induction as generalizing asg with
  | nil => simp
  | cons a0 as ih =>
    intro a ha
    simp only [completionsOn, List.mem_flatMap, List.mem_map] at h
    obtain ⟨b, hb, r, hr, rfl⟩ := h
    have hb' : p a0 = .u ∨ p a0 = TV3.ofBool b := by
      cases hpa : p a0 <;> rw [hpa] at hb <;> cases b <;> simp_all [TV3.ofBool]
    simp only [lookup]
    by_cases hab : a = a0
    · subst hab; simpa using hb'
    · simp only [hab, ↓reduceIte]
      exact ih hr a (by simpa [hab] using ha)

/-- A completion restricted to `as` is enumerated by `completionsOn`. -/
theorem restrict_mem {p : Atom → TV3} {c : Atom → Bool} (hc : Completes p c) (as : List Atom) :
    as.map (fun a => (a, c a)) ∈ completionsOn p as := by
  induction as with
  | nil => simp [completionsOn]
  | cons a0 as ih =>
    simp only [completionsOn, List.mem_flatMap, List.mem_map, List.map_cons]
    refine ⟨c a0, ?_, _, ih, rfl⟩
    rcases hc a0 with h | h <;> rw [h] <;> cases c a0 <;> simp [TV3.ofBool]

/-- Looking up a restriction gives back the completion on `as`. -/
theorem lookup_restrict {c : Atom → Bool} {as : List Atom} {a : Atom} (ha : a ∈ as) :
    lookup (as.map fun a => (a, c a)) a = c a := by
  induction as with
  | nil => simp at ha
  | cons a0 as ih =>
    simp only [List.map_cons, lookup]
    by_cases hab : a = a0
    · subst hab; simp
    · simp only [hab, ↓reduceIte]
      exact ih (by simpa [hab] using ha)

/-- `admissible` depends only on the atoms in the groups. -/
theorem admissible_congr {cs : List (List Atom)} {c d : Atom → Bool}
    (h : ∀ g ∈ cs, ∀ a ∈ g, c a = d a) : admissible cs c = admissible cs d := by
  induction cs with
  | nil => rfl
  | cons g cs ih =>
    have e1 := List.filter_congr (h g (by simp))
    have e2 := ih (fun g' hg' => h g' (by simp [hg']))
    simp only [admissible, List.all_cons] at e2 ⊢
    rw [e1, e2]

/-- `mapM` of a function that never errors is `.ok` of `map`. -/
theorem mapM_ok {α β ε : Type} {l : List α} {g : α → Except ε β} {k : α → β}
    (H : ∀ x ∈ l, g x = .ok (k x)) : l.mapM g = .ok (l.map k) := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    rw [List.mapM_cons, H x (by simp), ih (fun y hy => H y (by simp [hy]))]
    rfl

/-- `c` is a completion of `p` that satisfies every constraint. -/
def AdmissibleCompletion (p : Atom → TV3) (cs : List (List Atom)) (c : Atom → Bool) : Prop :=
  Completes p c ∧ admissible cs c = true

/-- **Theorem 6.** `exactStatus` says what it enumerates. Each enumerated
assignment extends to an admissible completion with the same value of `f`
(atoms outside the enumeration take their known value, or true), and each
admissible completion restricts to an enumerated assignment with the same
value, because `f` and the constraints mention only enumerated atoms. -/
theorem exactStatus_spec {f : Formula} {p : Atom → TV3} {cs : List (List Atom)}
    (hf : isCore f = true) :
    match exactStatus f p cs with
    | .ok .noAdmissibleCompletion => ¬ ∃ c, AdmissibleCompletion p cs c
    | .ok .always => (∃ c, AdmissibleCompletion p cs c) ∧
        ∀ c, AdmissibleCompletion p cs c → eval classical c f = .ok true
    | .ok .never => (∃ c, AdmissibleCompletion p cs c) ∧
        ∀ c, AdmissibleCompletion p cs c → eval classical c f = .ok false
    | .ok .sometimes => (∃ c, AdmissibleCompletion p cs c ∧ eval classical c f = .ok true) ∧
        (∃ c, AdmissibleCompletion p cs c ∧ eval classical c f = .ok false)
    | .error _ => False := by
  have hev : ∀ c, eval classical c f = .ok ((eval classical c f).toOption.getD false) := by
    intro c
    obtain ⟨b, hb⟩ := eval_core_ok classical c f hf
    rw [hb]; rfl
  simp only [exactStatus, hf, ite_true]
  rw [mapM_ok (k := fun asg => (eval classical (lookup asg) f).toOption.getD false)
    (fun asg _ => hev _)]
  generalize hS : List.filter (fun asg => admissible cs (lookup asg))
    (completionsOn p (dedup (atomList f ++ cs.flatten))) = S
  generalize hk : (fun asg => (eval classical (lookup asg) f).toOption.getD false) = k
  have hinf : ∀ {a}, a ∈ atomList.go f → a ∈ dedup (atomList f ++ cs.flatten) := fun ha =>
    mem_dedup.mpr (List.mem_append_left _ (mem_dedup.mpr ha))
  have hincs : ∀ {g a}, g ∈ cs → a ∈ g → a ∈ dedup (atomList f ++ cs.flatten) := fun hg ha =>
    mem_dedup.mpr (List.mem_append_right _ (List.mem_flatten.mpr ⟨_, hg, ha⟩))
  -- every enumerated assignment extends to an admissible completion
  have h2 : ∀ asg ∈ S, ∃ c, AdmissibleCompletion p cs c ∧ eval classical c f = .ok (k asg) := by
    classical
    intro asg hm
    rw [← hS, List.mem_filter] at hm
    obtain ⟨hmc, hadm⟩ := hm
    refine ⟨fun a => if a ∈ dedup (atomList f ++ cs.flatten) then lookup asg a else decide (p a = .t),
      ⟨?_, ?_⟩, ?_⟩
    · intro a
      by_cases ha : a ∈ dedup (atomList f ++ cs.flatten)
      · simp only [ha, ↓reduceIte]
        exact completionsOn_sound hmc a ha
      · simp only [ha, ↓reduceIte]
        cases p a <;> simp [TV3.ofBool]
    · rw [admissible_congr (d := lookup asg) (fun g hg a ha => by simp [hincs hg ha])]
      exact hadm
    · rw [← hk, eval_congr (w := lookup asg) f (fun a ha => by simp [hinf ha])]
      exact hev _
  -- every admissible completion restricts to an enumerated assignment
  have h3 : ∀ c, AdmissibleCompletion p cs c → ∃ asg ∈ S, eval classical c f = .ok (k asg) := by
    rintro c ⟨hc, hadm⟩
    refine ⟨(dedup (atomList f ++ cs.flatten)).map (fun a => (a, c a)), ?_, ?_⟩
    · rw [← hS, List.mem_filter]
      refine ⟨restrict_mem hc _, ?_⟩
      rw [admissible_congr (d := c) (fun g hg a ha => lookup_restrict (hincs hg ha))]
      exact hadm
    · rw [← hk]
      dsimp only
      rw [eval_congr (w := c) f (fun a ha => lookup_restrict (hinf ha))]
      exact hev c
  dsimp only [bind, Except.bind]
  by_cases e1 : (S.map k).isEmpty = true
  · simp only [e1, ↓reduceIte]
    show ¬ _
    rintro ⟨c, hc⟩
    obtain ⟨asg, hm, _⟩ := h3 c hc
    have : S = [] := by simpa using e1
    rw [this] at hm
    simp at hm
  obtain ⟨asg0, hasg0⟩ : ∃ asg0, asg0 ∈ S := by
    cases S with
    | nil => simp at e1
    | cons x _ => exact ⟨x, List.mem_cons_self⟩
  obtain ⟨c0, hc0, _⟩ := h2 asg0 hasg0
  simp only [e1, ↓reduceIte, Bool.false_eq_true]
  by_cases e2 : (S.map k).all id = true
  · simp only [e2, ↓reduceIte]
    show _ ∧ _
    refine ⟨⟨c0, hc0⟩, fun c hc => ?_⟩
    obtain ⟨asg, hm, he⟩ := h3 c hc
    rw [he]
    have := List.all_eq_true.mp e2 (k asg) (List.mem_map_of_mem hm)
    simp only [id] at this
    rw [this]
  simp only [e2, ↓reduceIte, Bool.false_eq_true]
  by_cases e3 : ((S.map k).all fun x => !x) = true
  · simp only [e3, ↓reduceIte]
    show _ ∧ _
    refine ⟨⟨c0, hc0⟩, fun c hc => ?_⟩
    obtain ⟨asg, hm, he⟩ := h3 c hc
    rw [he]
    have := List.all_eq_true.mp e3 (k asg) (List.mem_map_of_mem hm)
    simp only [Bool.not_eq_true'] at this
    rw [this]
  simp only [e3, ↓reduceIte, Bool.false_eq_true]
  show _ ∧ _
  have hfalse : ∃ asg ∈ S, k asg = false := by
    refine Classical.byContradiction fun hne => e2 (List.all_eq_true.mpr ?_)
    intro x hx
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
    cases hka : k a
    · exact absurd ⟨a, ha, hka⟩ hne
    · rfl
  have htrue : ∃ asg ∈ S, k asg = true := by
    refine Classical.byContradiction fun hne => e3 (List.all_eq_true.mpr ?_)
    intro x hx
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
    cases hka : k a
    · rfl
    · exact absurd ⟨a, ha, hka⟩ hne
  obtain ⟨a1, ha1, hk1⟩ := htrue
  obtain ⟨a2, ha2, hk2⟩ := hfalse
  obtain ⟨c1, hc1, he1⟩ := h2 a1 ha1
  obtain ⟨c2, hc2, he2⟩ := h2 a2 ha2
  exact ⟨⟨c1, hc1, hk1 ▸ he1⟩, ⟨c2, hc2, hk2 ▸ he2⟩⟩
end Gamen.ManyValued
