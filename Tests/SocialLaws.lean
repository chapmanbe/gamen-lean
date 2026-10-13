import Gamen.Atl.SocialLaws
import Tests.AtlDynamic

/-!
# Theorem 3 of the ATL-D paper: behavioural constraints as ATL-D updates

`G † η, v ⊨ ⟨⟨∅⟩⟩Gφ` iff `G⁺, v ⊨ [π_η]− ⟨⟨∅⟩⟩Gφ`, on the oxygen-tank model, for several
constraints and objectives. `G † η` is built from van der Hoek, Roberts & Wooldridge's
definition (`implementConstraint`) and checked with the static `Gamen.Atl.sat`; the other side
goes through ATL-D updates. Also pinned: the unreasonable case, where the two are *not* the same.
-/

namespace SocialLawTests

open Gamen Gamen.Atl.Dynamic AtlDynamicTests

def tank : Option DynModel := (load modelDefault).toOption

/-- Objectives φ ∈ ATL, as `Formula` (static checker) and `DFormula` (updates). -/
def objectives : List (Formula × DFormula) :=
  [(.not (.atom "warm"), .not warmP),
   (.or (.not (.atom "warm")) (.atom "atBob"), .or (.not warmP) atBob),
   (.atom "atBob", atBob),
   (.not (.atom "atBob"), .not atBob)]

def constraints : List (String × Constraint) :=
  [("none", []),
   ("r1 may not go left outside Bob's room", [("left", "r1", ["q0", "q2"])]),
   ("r1 may not go right at Bob's room and may not go left at the balcony",
    [("right", "r1", ["q1"]), ("left", "r1", ["q2"])]),
   ("r1 may not go right anywhere", [("right", "r1", ["q0", "q1", "q2"])])]

/-- Effective iff `G † η, v ⊨ ⟨⟨∅⟩⟩Gφ` (static ATL on the restricted model). -/
def effective (m : DynModel) (η : Constraint) (φ : Formula) (v : String) : Option Bool := do
  let g ← (implementConstraint m η).toOption
  let s ← (sat g.cgs (.canAlways [] φ)).toOption
  pure (s.contains v)

/-- `G⁺, v ⊨ [π_η]− ⟨⟨∅⟩⟩Gφ`. -/
def viaUpdate (m : DynModel) (η : Constraint) (φ : DFormula) (v : String) : Option Bool := do
  let s ← (dsat m.withStateAtoms .perfect (.revoke (behaviouralUpdate η) (.canAlways [] φ))).toOption
  pure (s.contains v)

def cases : List (String × Bool) :=
  (constraints.map fun (name, η) =>
    (s!"Thm 3: ({name}) effective ⇔ [π_η]−⟨⟨∅⟩⟩Gφ, 4 objectives × 3 states",
     match tank with
     | some m => objectives.all fun (φ, d) => ["q0", "q1", "q2"].all fun v =>
         (effective m η φ v).isSome && effective m η φ v == viaUpdate m η d v
     | none => false)) ++ [
  ("Thm 3: the constraints are not all equivalent to doing nothing (the check is not vacuous)",
    match tank with
    | some m => objectives.any fun (φ, _) => ["q0", "q1", "q2"].any fun v =>
        effective m (constraints[1]!.2) φ v != effective m [] φ v
    | none => false),
  ("implementConstraint: r2's only action forbidden is not reasonable, and is an error",
    match tank with
    | some m => (implementConstraint m [("left", "r2", ["q1"])]).isOk == false
    | none => false),
  ("unreasonable η: ATL-D's revoke keeps the agent's actions instead (the documented divergence)",
    match tank with
    | some m =>
      let bad : Constraint := [("left", "r1", ["q0"]), ("right", "r1", ["q0"])]
      (implementConstraint m bad).isOk == false
        && (match dsat m.withStateAtoms .perfect
              (.revoke (behaviouralUpdate bad) (.and (.has "r1" "left") (.has "r1" "right"))) with
            | .ok s => s.contains "q0"
            | .error _ => false)
    | none => false),
  ("implementConstraint: unknown action, agent or state is an error",
    match tank with
    | some m =>
      (implementConstraint m [("fly", "r1", ["q0"])]).isOk == false
        && (implementConstraint m [("left", "r9", ["q0"])]).isOk == false
        && (implementConstraint m [("left", "r1", ["q9"])]).isOk == false
    | none => false),
  ("G⁺: every state satisfies exactly its own state atom",
    match tank with
    | some m => (dsat m.withStateAtoms .perfect (.atom (stateAtom "q1"))).toOption.map (·.toList)
        == some ["q1"]
    | none => false)
]

end SocialLawTests
