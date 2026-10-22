import Widgets.Dynamic.Scenario

/-!
# Dynamic-scenarios explorer: the grader

`gradeAnswer` checks a student's answer semantically, on the model after the
update:

* `clickWorlds`: the clicked set against the formula's truth set;
* `writeFormula`: the student formula's truth set against the target, so any
  equivalent formula passes;
* `reachGoal`: the model after the *student's* selection, with the goal true at
  the named world (or at every world).

A parse or evaluation error is an `Except` error, never `correct := false`.
The message is the question's `Hint` for the normalized answer when there is
one, otherwise generated from the worlds where the answer and the truth differ.
-/

namespace Gamen.Widgets.Dynamic

open Lean (ToJson FromJson)

inductive Answer
  | worlds (ws : List String)
  | formula (text : String)
  | controls (selected : List String)
  deriving ToJson, FromJson, Inhabited

structure Feedback where
  correct : Bool
  message : String
  deriving ToJson, FromJson, Inhabited

/-- Sorted, without duplicates (the order of the evaluators' truth sets). -/
private def sortedSet (xs : List String) : List String := (Std.TreeSet.ofList xs).toList

private def showSet (xs : List String) : String :=
  if xs.isEmpty then "no world" else ", ".intercalate xs

/-- The normalized form `Hint.answer` is written in. -/
def Answer.normalize : Answer → String
  | .worlds ws => ",".intercalate (sortedSet ws)
  | .formula t => t.trim
  | .controls s => ",".intercalate (sortedSet s)

/-- `K[a]φ` (epistemic) or `knows a φ` (ATL-D) at the top: the agent and `φ`'s text. -/
private def knowsParts (mode : Mode) (text : String) : Option (String × String) :=
  match mode with
  | .epistemic =>
    match parseFormula text with
    | .ok (.knowledge a φ) => some (a, φ.toString)
    | _ => none
  | .atlD =>
    match Atl.Dynamic.parseDFormula text with
    | .ok (.knows a φ) => some (a, φ.toInput)
    | _ => none

/-- For a wrongly clicked world `w` where `K[a]φ` fails: a world `a` cannot rule
out at which `φ` is false. -/
private def knowsWitness (mode : Mode) (ev : Evaluable) (formula : String) (w : String) :
    Except String (Option String) := do
  match knowsParts mode formula with
  | none => pure none
  | some (a, φ) =>
    let tφ ← ev.truthSet φ
    pure <| ((ev.access a w).find? (!tφ.contains ·)).map fun w' =>
      s!"At {w}, {a} cannot rule out {w'}, where {φ} is false."

private def clickMessage (mode : Mode) (ev : Evaluable) (f : String)
    (truth clicked : List String) : Except String String := do
  let extra := clicked.filter (!truth.contains ·)
  let missing := truth.filter (!clicked.contains ·)
  let mut parts : List String := []
  unless extra.isEmpty do
    parts := parts ++ [s!"{f} is true at {showSet truth} but not at {showSet extra}."]
    for w in extra do
      if let some s ← knowsWitness mode ev f w then parts := parts ++ [s]
  unless missing.isEmpty do
    parts := parts ++ [s!"{f} is also true at {showSet missing}, which you did not select."]
  pure (" ".intercalate parts)

/-- Grade answer `a` to question `q`; `selected` is the scenario's current
controls (used by `clickWorlds` and `writeFormula`; `reachGoal` uses the
student's own selection). -/
def gradeAnswer (sc : Scenario) (selected : List String) (q : Question) (a : Answer) :
    Except String Feedback := do
  let (correct, generated) ← match q.kind, a with
    | .clickWorlds f, .worlds ws => do
      let ev ← sc.after selected
      let clicked := sortedSet ws
      if let some w := clicked.find? (!ev.worlds.contains ·) then
        throw s!"unknown world \"{w}\""
      let truth ← ev.truthSet f
      if clicked == truth then pure (true, "Correct.")
      else pure (false, ← clickMessage sc.mode ev f truth clicked)
    | .writeFormula target, .formula text => do
      let ev ← sc.after selected
      let target := sortedSet target
      let mine ← ev.truthSet text
      if mine == target then pure (true, "Correct.")
      else
        let extra := mine.filter (!target.contains ·)
        let missing := target.filter (!mine.contains ·)
        let parts :=
          (if extra.isEmpty then [] else [s!"Your formula is true at {showSet extra} but should not be."]) ++
          (if missing.isEmpty then [] else [s!"Your formula is not true at {showSet missing} but should be."])
        pure (false, " ".intercalate parts)
    | .reachGoal goal atWorld, .controls sel => do
      let ev ← sc.after sel
      let truth ← ev.truthSet goal
      match atWorld with
      | some w =>
        if !ev.worlds.contains w then
          pure (false, s!"With that choice there is no world {w}.")
        else if truth.contains w then pure (true, "Correct.")
        else pure (false, s!"With that choice, {goal} is not true at {w}.")
      | none =>
        let failing := ev.worlds.filter (!truth.contains ·)
        if failing.isEmpty then pure (true, "Correct.")
        else pure (false, s!"With that choice, {goal} is true at {showSet truth} but not at {showSet failing}.")
    | .clickWorlds _, _ => throw "this question expects a set of worlds"
    | .writeFormula _, _ => throw "this question expects a formula"
    | .reachGoal _ _, _ => throw "this question expects a choice of controls"
  let norm := a.normalize
  let message := match q.hints.find? (·.answer == norm) with
    | some h => h.text
    | none => generated
  pure { correct, message }

end Gamen.Widgets.Dynamic
