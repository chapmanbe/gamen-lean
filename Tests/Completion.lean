import Gamen.ManyValued.Completion
import Tests.ManyValued

/-!
# Tests for `Gamen.ManyValued.Completion` (Lean-only)

Spec: `docs/superpowers/specs/2026-09-30-gv-phase2-missing-data-design.md`.
Kernel-checked witnesses (theorem 5), the axiom audit, unit `cases`, and
the predicate for the Plausible property in `Tests/Main.lean`.
-/

namespace CompletionTests

open Gamen Gamen.ManyValued

def p : Formula := .atom "p"
def q : Formula := .atom "q"
def allU : Atom → TV3 := fun _ => .u

/-! ## Theorem 5: the converse of `mixed_possible` fails (`decide`) -/

/-- `p ∧ ¬p` with `p` unknown: K3 says possible, yet no completion makes it true. -/
theorem contradiction_possible : k3Status (.and p (.not p)) allU = .ok .possible := by decide
theorem contradiction_never : exactStatus (.and p (.not p)) allU [] = .ok .never := by decide
/-- The same through a constraint: exactly one of p, q. -/
theorem exclusive_possible : k3Status (.and p q) allU = .ok .possible := by decide
theorem exclusive_never : exactStatus (.and p q) allU [[⟨"p"⟩, ⟨"q"⟩]] = .ok .never := by decide
/-- K3 has no tautologies, but the exact check sees `p ∨ ¬p` hold everywhere. -/
theorem lem_always : exactStatus (.or p (.not p)) allU [] = .ok .always := by decide
/-- Known facts that break a constraint admit no completion. -/
theorem violated :
    exactStatus p (fun _ => .t) [[⟨"p"⟩, ⟨"q"⟩]] = .ok .noAdmissibleCompletion := by decide

#assert_kernel_only
  strongKleene_tables_monotone strongKleene_monotone completes_le completion_value
  definite_sound absent_sound mixed_possible
  contradiction_possible contradiction_never exclusive_possible exclusive_never lem_always violated

/-! ## Unit cases -/

def cases : List (String × Bool) := [
  ("Completion: all known, p ∧ q true → definite, always",
    k3Status (.and p q) (fun _ => .t) == .ok .definite
      && exactStatus (.and p q) (fun _ => .t) [] == .ok .always),
  ("Completion: q known false → p ∧ q absent, never",
    let v : Atom → TV3 := fun a => if a.name == "q" then .f else .u
    k3Status (.and p q) v == .ok .absent && exactStatus (.and p q) v [] == .ok .never),
  ("Completion: p unknown → p possible, sometimes",
    k3Status p allU == .ok .possible && exactStatus p allU [] == .ok .sometimes),
  ("Completion: completionsOn fixes known atoms (p=t, q=u gives 2)",
    (completionsOn (fun a => if a.name == "p" then .t else .u) [⟨"p"⟩, ⟨"q"⟩]).length == 2),
  ("Completion: k3Status errors on a non-core formula (□p)",
    ManyValuedTests.isErr (k3Status (.box p) allU)),
  ("Completion: exactStatus errors on a non-core formula (□p)",
    ManyValuedTests.isErr (exactStatus (.box p) allU [])),
  ("Completion: exactStatus errors on a non-core formula even with no admissible completion",
    ManyValuedTests.isErr (exactStatus (.box p) (fun _ => .t) [[⟨"p"⟩, ⟨"q"⟩]]))
]

/-! ## Plausible support -/

/-- A partial valuation of p, q, r: `k` says known, `b` is the value. -/
def partialVal (kp bp kq bq kr br : Bool) (a : Atom) : TV3 :=
  let val (k b : Bool) : TV3 := if k then TV3.ofBool b else .u
  if a.name == "p" then val kp bp else if a.name == "q" then val kq bq
  else if a.name == "r" then val kr br else .u

/-- Theorems 2–4 at run time: definite ⇒ always, absent ⇒ never (or no
admissible completion under the p/q constraint), so sometimes ⇒ possible. -/
def k3ExactConsistent (f : Formula) (kp bp kq bq kr br constrain : Bool) : Bool :=
  let v := partialVal kp bp kq bq kr br
  let cs := if constrain then [[⟨"p"⟩, ⟨"q"⟩]] else []
  match k3Status f v, exactStatus f v cs with
  | .ok .definite, .ok e => e == .always || e == .noAdmissibleCompletion
  | .ok .absent, .ok e => e == .never || e == .noAdmissibleCompletion
  | .ok .possible, .ok _ => true
  | _, _ => false

end CompletionTests
