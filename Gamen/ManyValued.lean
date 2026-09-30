import Gamen.Formula

/-!
# Many-valued propositional logics

Lean-only (no gamen-hs counterpart); plan:
`plans/three-valued-logic-2026-09-29.md`.

Every matrix here is taken from the Open Logic Text (OLT), chapter
`many-valued-logic`, pinned at OpenLogic revision `0a18d37`. Anchors in
brackets follow the Part C citation form: `[thr:skl, defn 1]` is the first
`defn` in the section with file id `mvl:thr:skl`; `[thr:luk:def:lukasiewicz]`
is the `\ollabel` `def:lukasiewicz` in `mvl:thr:luk`. Sources:

- `syntax-and-semantics/matrices.tex` (`mvl:syn:mat`): matrices, classical logic;
- `syntax-and-semantics/semantic-notions.tex` (`mvl:syn:sem`): tautology, entailment;
- `three-valued-logics/kleene.tex` (`mvl:thr:skl`): strong and weak Kleene;
- `three-valued-logics/lukasiewicz.tex` (`mvl:thr:luk`): Łukasiewicz;
- `three-valued-logics/goedel.tex` (`mvl:thr:god`): Gödel;
- `three-valued-logics/multiple-designation.tex` (`mvl:thr:mul`): LP.

**Built for `decide`.** Truth values are small inductive types, truth
functions are pattern-matching tables, and `eval` is structural recursion
with no `TreeSet`, so claims about particular formulas can be checked by
the kernel (`by decide`) rather than trusted to the compiler
(`native_decide`).

**Language.** The OLT gives the three-valued Kleene, Łukasiewicz and LP
matrices the language ¬, ∧, ∨, → *without* ⊥ (unlike `L₀` in
`[syn:con, ex 1]`), and Gödel logic and classical logic the language with ⊥.
No matrix here has ↔: the OLT defines none (Łukasiewicz ↔ appears only as
an exercise, `mvl:thr:luk:prob:luk-iff`). So `eval` errors on ⊥ in a matrix
without it, on ↔, and on every modal or other non-propositional operator.
The theorems below are stated for `isCore` formulas (atoms, ¬, ∧, ∨, →),
which every matrix evaluates. Without ⊥ excluded, "no K3 tautologies"
would be false: K3 with ⊥ = f makes ¬⊥ a tautology.
-/

namespace Gamen.ManyValued

open Gamen

/-- The three truth values of `mvl:thr` (OLT `\True`, `\Undef`, `\False`).
Constructor order matches the OLT tables' row order: t, u, f. -/
inductive TV3 where
  | t
  | u
  | f
  deriving DecidableEq, Repr, Inhabited

instance : ToString TV3 where
  toString | .t => "t" | .u => "u" | .f => "f"

/-- `∀ a : TV3, P a` is decided by checking t, u and f, so `decide` can
check claims about whole tables. -/
instance TV3.decForall (P : TV3 → Prop) [DecidablePred P] : Decidable (∀ a, P a) :=
  if h : P .t ∧ P .u ∧ P .f then
    isTrue (fun a => by cases a <;> simp_all)
  else
    isFalse (fun h' => h ⟨h' _, h' _, h' _⟩)

/-- Embed a classical truth value. -/
def TV3.ofBool : Bool → TV3
  | true => .t
  | false => .f

/-- A matrix `[syn:mat:defn:matrix]`: truth values, designated values,
and a truth function per connective. `falsum` is `none` when ⊥ is not in
the logic's language. -/
structure Matrix (V : Type) where
  name : String
  /-- The truth values `V`, in the OLT's table order; valuations are
  enumerated over this list. -/
  values : List V
  /-- Membership in the designated values `V⁺`. -/
  designated : V → Bool
  neg : V → V
  conj : V → V → V
  disj : V → V → V
  impl : V → V → V
  falsum : Option V

/-! ## Classical logic -/

/-- Classical logic `[syn:mat, ex 1]`, tables from `[syn:mat:fig:tf-CL]`:
`V = {T, F}` as `Bool`, `V⁺ = {T}`, `tf(⊥) = F`. -/
def classical : Matrix Bool where
  name := "classical"
  values := [true, false]
  designated := fun x => x
  neg | true => false | false => true
  conj
    | true, true => true
    | _, _ => false
  disj
    | false, false => false
    | _, _ => true
  impl
    | true, false => false
    | _, _ => true
  falsum := some false

/-! ## Kleene logics `[thr:skl]` -/

/-- Negation shared by strong and weak Kleene, Łukasiewicz and LP
(`[thr:skl, defn 1]`, `[thr:skl, defn 2]`, `[thr:luk:def:lukasiewicz]`). -/
def negK : TV3 → TV3
  | .t => .f
  | .u => .u
  | .f => .t

/-- Strong Kleene ∧ `[thr:skl, defn 1]`. Rows are the left operand. -/
def conjK3 : TV3 → TV3 → TV3
  | .t, .t => .t | .t, .u => .u | .t, .f => .f
  | .u, .t => .u | .u, .u => .u | .u, .f => .f
  | .f, .t => .f | .f, .u => .f | .f, .f => .f

/-- Strong Kleene ∨ `[thr:skl, defn 1]`. -/
def disjK3 : TV3 → TV3 → TV3
  | .t, .t => .t | .t, .u => .t | .t, .f => .t
  | .u, .t => .t | .u, .u => .u | .u, .f => .u
  | .f, .t => .t | .f, .u => .u | .f, .f => .f

/-- Strong Kleene → `[thr:skl, defn 1]`. -/
def implK3 : TV3 → TV3 → TV3
  | .t, .t => .t | .t, .u => .u | .t, .f => .f
  | .u, .t => .t | .u, .u => .u | .u, .f => .u
  | .f, .t => .t | .f, .u => .t | .f, .f => .t

/-- Strong Kleene logic K3 `[thr:skl, defn 1]`: `V⁺ = {t}`, no ⊥. -/
def strongKleene : Matrix TV3 where
  name := "strong Kleene"
  values := [.t, .u, .f]
  designated | .t => true | _ => false
  neg := negK
  conj := conjK3
  disj := disjK3
  impl := implK3
  falsum := none

/-- Weak Kleene ∧ `[thr:skl, defn 2]`. -/
def conjKw : TV3 → TV3 → TV3
  | .t, .t => .t | .t, .u => .u | .t, .f => .f
  | .u, .t => .u | .u, .u => .u | .u, .f => .u
  | .f, .t => .f | .f, .u => .u | .f, .f => .f

/-- Weak Kleene ∨ `[thr:skl, defn 2]`. -/
def disjKw : TV3 → TV3 → TV3
  | .t, .t => .t | .t, .u => .u | .t, .f => .t
  | .u, .t => .u | .u, .u => .u | .u, .f => .u
  | .f, .t => .t | .f, .u => .u | .f, .f => .f

/-- Weak Kleene → `[thr:skl, defn 2]`. -/
def implKw : TV3 → TV3 → TV3
  | .t, .t => .t | .t, .u => .u | .t, .f => .f
  | .u, .t => .u | .u, .u => .u | .u, .f => .u
  | .f, .t => .t | .f, .u => .u | .f, .f => .t

/-- Weak Kleene (Bochvar) logic `[thr:skl, defn 2]`: `V⁺ = {t}`, no ⊥.
Bochvar's extra connectives (external negation, "is undefined") are not
in the matrix and are not modeled. -/
def weakKleene : Matrix TV3 where
  name := "weak Kleene"
  values := [.t, .u, .f]
  designated | .t => true | _ => false
  neg := negK
  conj := conjKw
  disj := disjKw
  impl := implKw
  falsum := none

/-! ## Łukasiewicz `[thr:luk]` -/

/-- Łukasiewicz → `[thr:luk:def:lukasiewicz]`: strong Kleene's except
`u → u = t`. -/
def implL3 : TV3 → TV3 → TV3
  | .t, .t => .t | .t, .u => .u | .t, .f => .f
  | .u, .t => .t | .u, .u => .t | .u, .f => .u
  | .f, .t => .t | .f, .u => .t | .f, .f => .t

/-- Łukasiewicz ∧ `[thr:luk:def:lukasiewicz]`. The OLT prints its own
table; `lukasiewicz3_agrees_strongKleene` proves it equals `conjK3`. -/
def conjL3 : TV3 → TV3 → TV3
  | .t, .t => .t | .t, .u => .u | .t, .f => .f
  | .u, .t => .u | .u, .u => .u | .u, .f => .f
  | .f, .t => .f | .f, .u => .f | .f, .f => .f

/-- Łukasiewicz ∨ `[thr:luk:def:lukasiewicz]`. -/
def disjL3 : TV3 → TV3 → TV3
  | .t, .t => .t | .t, .u => .t | .t, .f => .t
  | .u, .t => .t | .u, .u => .u | .u, .f => .u
  | .f, .t => .t | .f, .u => .u | .f, .f => .f

/-- Three-valued Łukasiewicz logic Ł3 `[thr:luk:def:lukasiewicz]`:
`V⁺ = {t}`, no ⊥. -/
def lukasiewicz3 : Matrix TV3 where
  name := "Łukasiewicz"
  values := [.t, .u, .f]
  designated | .t => true | _ => false
  neg := negK
  conj := conjL3
  disj := disjL3
  impl := implL3
  falsum := none

/-! ## Gödel `[thr:god]` -/

/-- Gödel ¬ `[thr:god:defn:goedel]`: `¬u = f`. -/
def negG3 : TV3 → TV3
  | .t => .f
  | .u => .f
  | .f => .t

/-- Gödel ∧ `[thr:god:defn:goedel]`. -/
def conjG3 : TV3 → TV3 → TV3
  | .t, .t => .t | .t, .u => .u | .t, .f => .f
  | .u, .t => .u | .u, .u => .u | .u, .f => .f
  | .f, .t => .f | .f, .u => .f | .f, .f => .f

/-- Gödel ∨ `[thr:god:defn:goedel]`. -/
def disjG3 : TV3 → TV3 → TV3
  | .t, .t => .t | .t, .u => .t | .t, .f => .t
  | .u, .t => .t | .u, .u => .u | .u, .f => .u
  | .f, .t => .t | .f, .u => .u | .f, .f => .f

/-- Gödel → `[thr:god:defn:goedel]`: `u → f = f`. -/
def implG3 : TV3 → TV3 → TV3
  | .t, .t => .t | .t, .u => .u | .t, .f => .f
  | .u, .t => .t | .u, .u => .t | .u, .f => .f
  | .f, .t => .t | .f, .u => .t | .f, .f => .t

/-- Three-valued Gödel logic G `[thr:god:defn:goedel]`: `V⁺ = {t}`,
`tf(⊥) = f`. -/
def goedel3 : Matrix TV3 where
  name := "Gödel"
  values := [.t, .u, .f]
  designated | .t => true | _ => false
  neg := negG3
  conj := conjG3
  disj := disjG3
  impl := implG3
  falsum := some .f

/-! ## Logic of paradox `[thr:mul]` -/

/-- Priest's logic of paradox LP `[thr:mul, defn 1]`: strong Kleene's
truth functions with `V⁺ = {t, u}`, no ⊥. -/
def logicOfParadox : Matrix TV3 where
  name := "LP"
  values := [.t, .u, .f]
  designated | .t => true | .u => true | .f => false
  neg := negK
  conj := conjK3
  disj := disjK3
  impl := implK3
  falsum := none

/-! ## Evaluation -/

/-- The connectives every matrix here interprets: atoms, ¬, ∧, ∨, →. -/
def isCore : Formula → Bool
  | .atomF _ => true
  | .not a => isCore a
  | .and a b => isCore a && isCore b
  | .or a b => isCore a && isCore b
  | .implies a b => isCore a && isCore b
  | _ => false

/-- The value of a formula under valuation `v` (OLT `mvl:syn:val`: the
truth function of the main connective applied to the values of its
arguments). Errors, rather than defaulting, on ⊥ when the matrix has no
⊥, on ↔, and on every non-propositional operator. Operands are evaluated
left to right, so the leftmost error is the one reported. -/
def eval {V : Type} (m : Matrix V) (v : Atom → V) : Formula → Except String V
  | .bot =>
    match m.falsum with
    | some x => .ok x
    | none => .error s!"ManyValued.eval: ⊥ is not in the language of {m.name} logic"
  | .atomF a => .ok (v a)
  | .not a => do return m.neg (← eval m v a)
  | .and a b => do return m.conj (← eval m v a) (← eval m v b)
  | .or a b => do return m.disj (← eval m v a) (← eval m v b)
  | .implies a b => do return m.impl (← eval m v a) (← eval m v b)
  | .iff _ _ => .error s!"ManyValued.eval: ↔ is not in the language of {m.name} logic"
  | g => .error s!"ManyValued.eval: {g} is not a propositional formula"

/-- Lean core has no `DecidableEq (Except ε α)`; this one lets `decide`
check claims such as `isTautology lukasiewicz3 (p → p) = .ok true`. It
compares error messages only when both sides are errors. -/
instance instDecidableEqExcept {ε α : Type} [DecidableEq ε] [DecidableEq α] :
    DecidableEq (Except ε α)
  | .ok a, .ok b =>
    if h : a = b then isTrue (h ▸ rfl) else isFalse (fun e => h (by cases e; rfl))
  | .error a, .error b =>
    if h : a = b then isTrue (h ▸ rfl) else isFalse (fun e => h (by cases e; rfl))
  | .ok _, .error _ => isFalse (fun e => by cases e)
  | .error _, .ok _ => isFalse (fun e => by cases e)

/-- `v` satisfies `A` (`v ⊨ A`, value designated). An evaluation error
counts as not satisfied; use `eval` to tell the two apart. -/
def sat {V : Type} (m : Matrix V) (v : Atom → V) (f : Formula) : Bool :=
  match eval m v f with
  | .ok x => m.designated x
  | .error _ => false

/-! ## Valuations by enumeration -/

/-- Remove repeats, keeping first occurrences. -/
def dedup : List Atom → List Atom :=
  List.foldl (fun acc a => if acc.contains a then acc else acc ++ [a]) []

/-- The distinct atoms of a formula, in first-occurrence order. Atoms
under a non-propositional operator are not collected; `eval` rejects such
a formula anyway. -/
def atomList (f : Formula) : List Atom := dedup (go f)
where
  go : Formula → List Atom
    | .atomF a => [a]
    | .not a => go a
    | .and a b | .or a b | .implies a b | .iff a b => go a ++ go b
    | _ => []

/-- Every assignment of `vals` to `atoms`, as association lists: `|vals|ⁿ`
of them for `n` atoms. -/
def assignments {V : Type} (vals : List V) : List Atom → List (List (Atom × V))
  | [] => [[]]
  | a :: as =>
    let rest := assignments vals as
    vals.flatMap fun x => rest.map fun r => (a, x) :: r

/-- The valuation given by an assignment; atoms it doesn't list get
`default` (they don't occur in the formulas being evaluated). -/
def lookup {V : Type} [Inhabited V] : List (Atom × V) → Atom → V
  | [], _ => default
  | (b, x) :: rest, a => if a = b then x else lookup rest a

/-- The atoms of several formulas, without repeats. -/
def atomsOf (fs : List Formula) : List Atom := dedup (fs.flatMap atomList)

/-- Γ ⊨ A `[syn:sem, defn 1]`: every valuation that designates all of Γ
designates A. Decided by enumerating the `|V|ⁿ` valuations of the atoms
of Γ and A. Errors if any formula is outside the matrix's language. -/
def entails {V : Type} [Inhabited V] (m : Matrix V) (premises : List Formula)
    (conclusion : Formula) : Except String Bool :=
  go (assignments m.values (atomsOf (conclusion :: premises)))
where
  go : List (List (Atom × V)) → Except String Bool
    | [] => .ok true
    | asg :: rest => do
      let v := lookup asg
      let c ← eval m v conclusion
      let ps ← premises.mapM (eval m v)
      if ps.all m.designated && !m.designated c then return false
      go rest

/-- A is a tautology `[syn:sem, defn 1]`: designated under every
valuation, i.e. `∅ ⊨ A` (`[syn:sem:prop:semanticalfacts]`, item 1). -/
def isTautology {V : Type} [Inhabited V] (m : Matrix V) (f : Formula) : Except String Bool :=
  entails m [] f

/-! ## Theorems (kernel-checked)

Axiom audit: `Tests/ManyValued.lean` (`#assert_kernel_only`) fails the
build if any of these depends on an axiom beyond `propext`, `Quot.sound`
and `Classical.choice`: `sorryAx`, `Lean.ofReduceBool`, or the axiom
`native_decide` generates. Tactics used: `decide` for every claim about
the tables; structural induction with `rw` for the claims about all
formulas. -/

section evalLemmas
variable {V : Type} {m : Matrix V} {v : Atom → V} {a b : Formula} {x y : V}

theorem eval_not_ok (hx : eval m v a = .ok x) : eval m v (.not a) = .ok (m.neg x) := by
  simp only [eval, hx]; rfl
theorem eval_and_ok (hx : eval m v a = .ok x) (hy : eval m v b = .ok y) :
    eval m v (.and a b) = .ok (m.conj x y) := by
  simp only [eval, hx, hy]; rfl
theorem eval_or_ok (hx : eval m v a = .ok x) (hy : eval m v b = .ok y) :
    eval m v (.or a b) = .ok (m.disj x y) := by
  simp only [eval, hx, hy]; rfl
theorem eval_implies_ok (hx : eval m v a = .ok x) (hy : eval m v b = .ok y) :
    eval m v (.implies a b) = .ok (m.impl x y) := by
  simp only [eval, hx, hy]; rfl

end evalLemmas

/-- Every matrix evaluates every `isCore` formula without error. -/
theorem eval_core_ok {V : Type} (m : Matrix V) (v : Atom → V) :
    ∀ f, isCore f = true → ∃ x, eval m v f = .ok x := by
  intro f hf
  induction f with
  | atomF a => exact ⟨v a, rfl⟩
  | not a ih =>
    obtain ⟨x, hx⟩ := ih hf
    exact ⟨_, eval_not_ok hx⟩
  | and a b iha ihb | or a b iha ihb | implies a b iha ihb =>
    simp only [isCore, Bool.and_eq_true] at hf
    obtain ⟨x, hx⟩ := iha hf.1
    obtain ⟨y, hy⟩ := ihb hf.2
    first
      | exact ⟨_, eval_and_ok hx hy⟩
      | exact ⟨_, eval_or_ok hx hy⟩
      | exact ⟨_, eval_implies_ok hx hy⟩
  | _ => simp [isCore] at hf

/-- The strong Kleene tables restricted to {t, f} are the classical ones
(checked by `decide` over all inputs). -/
theorem strongKleene_tables_classical :
    (∀ a, negK (.ofBool a) = .ofBool (classical.neg a)) ∧
    (∀ a b, conjK3 (.ofBool a) (.ofBool b) = .ofBool (classical.conj a b)) ∧
    (∀ a b, disjK3 (.ofBool a) (.ofBool b) = .ofBool (classical.disj a b)) ∧
    (∀ a b, implK3 (.ofBool a) (.ofBool b) = .ofBool (classical.impl a b)) := by
  decide

/-- **Theorem (i).** On valuations into {t, f}, strong Kleene evaluation
agrees with classical evaluation (the Łukasiewicz analog is
`[thr:luk, prop 1]`). -/
theorem strongKleene_agrees_classical (v : Atom → Bool) :
    ∀ f, isCore f = true →
      eval strongKleene (fun a => .ofBool (v a)) f = (eval classical v f).map .ofBool := by
  intro f hf
  obtain ⟨t1, t2, t3, t4⟩ := strongKleene_tables_classical
  -- The induction hypothesis in the form `K3 value = ofBool (classical value)`.
  have step : ∀ g, isCore g = true →
      (eval strongKleene (fun a => .ofBool (v a)) g = (eval classical v g).map .ofBool) →
      ∃ x, eval classical v g = .ok x ∧
        eval strongKleene (fun a => .ofBool (v a)) g = .ok (.ofBool x) := by
    intro g hg ih
    obtain ⟨x, hx⟩ := eval_core_ok classical v g hg
    exact ⟨x, hx, by rw [ih, hx]; rfl⟩
  induction f with
  | atomF a => rfl
  | not a ih =>
    obtain ⟨x, hx, ha⟩ := step a hf (ih hf)
    rw [eval_not_ok ha, eval_not_ok hx]
    exact congrArg Except.ok (t1 x)
  | and a b iha ihb =>
    simp only [isCore, Bool.and_eq_true] at hf
    obtain ⟨x, hx, ha⟩ := step a hf.1 (iha hf.1)
    obtain ⟨y, hy, hb⟩ := step b hf.2 (ihb hf.2)
    rw [eval_and_ok ha hb, eval_and_ok hx hy]
    exact congrArg Except.ok (t2 x y)
  | or a b iha ihb =>
    simp only [isCore, Bool.and_eq_true] at hf
    obtain ⟨x, hx, ha⟩ := step a hf.1 (iha hf.1)
    obtain ⟨y, hy, hb⟩ := step b hf.2 (ihb hf.2)
    rw [eval_or_ok ha hb, eval_or_ok hx hy]
    exact congrArg Except.ok (t3 x y)
  | implies a b iha ihb =>
    simp only [isCore, Bool.and_eq_true] at hf
    obtain ⟨x, hx, ha⟩ := step a hf.1 (iha hf.1)
    obtain ⟨y, hy, hb⟩ := step b hf.2 (ihb hf.2)
    rw [eval_implies_ok ha hb, eval_implies_ok hx hy]
    exact congrArg Except.ok (t4 x y)
  | _ => simp [isCore] at hf

/-- The all-`u` valuation sends every `isCore` formula to `u`, for any
matrix whose truth functions fix `u` (`[thr:skl, prop 1]`'s proof). -/
theorem eval_allU {m : Matrix TV3}
    (hneg : m.neg .u = .u) (hconj : m.conj .u .u = .u)
    (hdisj : m.disj .u .u = .u) (himpl : m.impl .u .u = .u) :
    ∀ f, isCore f = true → eval m (fun _ => .u) f = .ok .u := by
  intro f hf
  induction f with
  | atomF a => rfl
  | not a ih => rw [eval_not_ok (ih hf), hneg]
  | and a b iha ihb =>
    simp only [isCore, Bool.and_eq_true] at hf
    rw [eval_and_ok (iha hf.1) (ihb hf.2), hconj]
  | or a b iha ihb =>
    simp only [isCore, Bool.and_eq_true] at hf
    rw [eval_or_ok (iha hf.1) (ihb hf.2), hdisj]
  | implies a b iha ihb =>
    simp only [isCore, Bool.and_eq_true] at hf
    rw [eval_implies_ok (iha hf.1) (ihb hf.2), himpl]
  | _ => simp [isCore] at hf

/-- **Theorem (ii).** Under the all-`u` valuation every `isCore` formula
is `u` in strong Kleene logic. -/
theorem strongKleene_allU : ∀ f, isCore f = true →
    eval strongKleene (fun _ => .u) f = .ok .u :=
  eval_allU (by decide) (by decide) (by decide) (by decide)

/-- **No K3 tautologies** `[thr:skl, prop 1]`: every `isCore` formula is
undesignated under some valuation (the all-`u` one). -/
theorem strongKleene_no_tautologies :
    ∀ f, isCore f = true → ∃ v, sat strongKleene v f = false := by
  intro f hf
  refine ⟨fun _ => .u, ?_⟩
  simp [sat, strongKleene_allU f hf]
  rfl

/-- The same for weak Kleene, which `[thr:skl, prop 1]` also states. -/
theorem weakKleene_no_tautologies :
    ∀ f, isCore f = true → ∃ v, sat weakKleene v f = false := by
  intro f hf
  refine ⟨fun _ => .u, ?_⟩
  simp [sat, eval_allU (m := weakKleene) (by decide) (by decide) (by decide) (by decide) f hf]
  rfl

/-- **Theorem (iii), first half.** Ł3 and K3 have the same ¬, ∧ and ∨
(`decide` over the tables). -/
theorem lukasiewicz3_agrees_strongKleene :
    (∀ a, lukasiewicz3.neg a = strongKleene.neg a) ∧
    (∀ a b, lukasiewicz3.conj a b = strongKleene.conj a b) ∧
    (∀ a b, lukasiewicz3.disj a b = strongKleene.disj a b) := by
  decide

/-- **Theorem (iii), second half.** Their → tables differ, and only at
`u → u` (`t` in Ł3, `u` in K3). -/
theorem lukasiewicz3_impl_differs :
    lukasiewicz3.impl .u .u = .t ∧ strongKleene.impl .u .u = .u ∧
    (∀ a b, (a, b) ≠ (.u, .u) → lukasiewicz3.impl a b = strongKleene.impl a b) := by
  decide

end Gamen.ManyValued
