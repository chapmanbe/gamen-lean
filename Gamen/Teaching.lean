import Gamen.Semantics
import Gamen.Notation
import Gamen.Tableau

/-!
# Gamen.Teaching

Small helpers for the teaching notebooks.
-/
namespace Gamen

/-- `M, w ⊩ φ` as a plain `Bool`, for `#eval` and `native_decide`. Operators
that need a richer model (Knowledge, Stit, …) count as `false`; the teaching
notebooks for Chapter 1 use only propositional operators, □ and ◇. -/
def holdsAt (m : Model) (w : World) (φ : Formula) : Bool :=
  match satisfies m w φ with
  | .ok b => b
  | .error _ => false

/-- True at every world: M ⊩ A (B&D Definition 1.9). -/
def trueIn (m : Model) (φ : Formula) : Bool :=
  match isTrueIn m φ with
  | .ok b => b
  | .error _ => false

/-- Feedback for a prediction exercise. Students write `some true` or
`some false`; `none` means "not answered yet". -/
def grade (prediction : Option Bool) (actual : Bool) : String :=
  match prediction with
  | none => "Not answered yet: replace `none` with `some true` or `some false`."
  | some p => if p == actual then "✓ Correct." else "✗ Not quite. Look at every accessible world again."

/-- Feedback for a "write the formula" exercise. -/
def gradeFormula (answer : Option Formula) (expected : Formula) : String :=
  match answer with
  | none => "Not answered yet: replace `none` with `some ml[ … ]`."
  | some f => if f == expected then s!"✓ Correct: {f}"
              else s!"✗ You wrote {f}. Compare it with the sentence again."

/-- In notebooks, `#eval` shows formulas in textbook notation rather than as
constructor trees. -/
instance (priority := high) : Repr Formula := ⟨fun f _ => f.toString⟩

/-- Is the set satisfiable by some model in which every world has an
acceptable successor (system KD, as in `gamen-validate`)? -/
def consistency (fs : List Formula) : String :=
  match tableauConsistent systemKDt defaultMaxSteps fs with
  | .definitely true => "consistent: some model satisfies all of them"
  | .definitely false => "inconsistent: no model satisfies all of them"
  | .unknown r => s!"undecided ({r.code})"

end Gamen
