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

end Gamen.ManyValued
