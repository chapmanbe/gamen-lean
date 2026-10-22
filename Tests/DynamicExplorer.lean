import Widgets.Dynamic.Grade

/-!
# The dynamic-scenarios explorer: scenario format and grader

A two-world epistemic scenario (agents N and D; events `sent` and `lost`, with
`pre(sent) = p`) and a one-agent ATL-D model whose revocation would empty
`d(nurse, s0)` and so is skipped there by the reasonableness rule.
-/

namespace DynamicExplorerTests

open Lean (Json ToJson toJson)
open Gamen.Widgets.Dynamic

/-- `Except` has no `BEq` in core; compare successes by value and failures by message. -/
local instance {ε α : Type} [BEq ε] [BEq α] : BEq (Except ε α) where
  beq
    | .ok a, .ok b => a == b
    | .error a, .error b => a == b
    | _, _ => false

def isError {α : Type} (r : Except String α) : Bool :=
  match r with | .error _ => true | .ok _ => false

def parsed (s : String) : Json := (Json.parse s).toOption.getD Json.null

/-- Neither agent can tell `w1` (where `p`) from `w2`. -/
def epiModel : Json := parsed
  "{\"worlds\":[\"w1\",\"w2\"],\"agents\":[\"N\",\"D\"],
    \"indistinguishable\":{\"N\":[[\"w1\",\"w2\"]],\"D\":[[\"w1\",\"w2\"]]},
    \"valuation\":{\"w1\":[\"p\"]}}"

def epiControls : Json := parsed
  "{\"events\":[\"sent\",\"lost\"],\"pre\":{\"sent\":\"p\"},\"post\":{},
    \"toggleable\":[\"D\"],\"observers\":[]}"

def q1 : Question :=
  { id := "q1", prompt := "Where does D know p while N does not know that?"
    kind := .clickWorlds "K[D]p ∧ ¬K[N]K[D]p", answer := "w1×sent"
    hints := [{ answer := "", text := "Select at least one world." }] }

def q2 : Question :=
  { id := "q2", prompt := "Write a formula true exactly where D knows p."
    kind := .writeFormula ["w1×sent"], answer := "K[D]p" }

def q3 : Question :=
  { id := "q3", prompt := "Who must observe for D to know p after a send?"
    kind := .reachGoal "K[D]p" (some "w1×sent"), answer := "D" }

def q4 : Question :=
  { id := "q4", prompt := "Where does D know p?", kind := .clickWorlds "K[D]p", answer := "w1×sent" }

def sc : Scenario :=
  { id := "lab", title := "Lab result", setup := "A result is sent or lost."
    mode := .epistemic, model := epiModel, controls := epiControls
    layout := [⟨"w1", 0, 0⟩, ⟨"w2", 1, 0⟩], questions := [q1, q2, q3] }

def grade (q : Question) (a : Answer) : Except String Bool :=
  (gradeAnswer sc ["D"] q a).map (·.correct)

def gradeMsg (q : Question) (a : Answer) : String :=
  match gradeAnswer sc ["D"] q a with
  | .ok f => f.message
  | .error e => e

/-- One agent, two states; `x` is the nurse's only action at `s0`. -/
def dynModel : Json := parsed
  "{\"states\":[\"s0\",\"s1\"],\"agents\":[\"nurse\"],\"actions\":[\"x\",\"y\"],
    \"moves\":{\"s0\":{\"nurse\":[\"x\"]},\"s1\":{\"nurse\":[\"x\",\"y\"]}},
    \"default_next\":{\"stay\":true},\"transitions\":[],
    \"valuation\":{\"s1\":[\"q\"]}}"

def dynControls : Json := parsed
  "{\"mode\":\"perfect\",\"clauses\":[
    {\"label\":\"noX\",\"kind\":\"revoke\",\"cond\":\"⊤\",\"action\":\"x\",
     \"agents\":[\"nurse\"],\"informed\":[]}]}"

def dsc : Scenario :=
  { id := "dyn", title := "Revoke", setup := "", mode := .atlD
    model := dynModel, controls := dynControls, layout := [], questions := [] }

def dynNotes : List String := ((dsc.after ["noX"]).map (·.notes)).toOption.getD []

def cases : List (String × Bool) := [
  ("before has 2 worlds", ((sc.before).map (·.worlds.length)) == .ok 2),
  ("after, D observes: 3 worlds",
    ((sc.after ["D"]).map (·.worlds)) == .ok ["w1×lost", "w1×sent", "w2×lost"]),
  ("K[D]p ∧ ¬K[N]K[D]p exactly at w1×sent",
    ((sc.after ["D"]).bind (·.truthSet "K[D]p ∧ ¬K[N]K[D]p")) == .ok ["w1×sent"]),
  ("clickWorlds correct", grade q1 (.worlds ["w1×sent"]) == .ok true),
  ("clickWorlds wrong", grade q1 (.worlds ["w1×sent", "w1×lost"]) == .ok false),
  ("clickWorlds wrong names the witness",
    (gradeMsg q1 (.worlds ["w1×sent", "w1×lost"])).contains "w1×lost"),
  ("clickWorlds on K[D]p names a world D cannot rule out",
    (gradeMsg q4 (.worlds ["w1×lost"])).contains "D cannot rule out w2×lost"),
  ("writeFormula equivalent passes", grade q2 (.formula "¬¬K[D]p") == grade q2 (.formula "K[D]p")),
  ("writeFormula K[D]p passes", grade q2 (.formula "K[D]p") == .ok true),
  ("writeFormula p fails", grade q2 (.formula "p") == .ok false),
  ("unknown agent is an error, not false",
    isError (sc.after ["D"] |>.bind (·.truthSet "K[X]p"))),
  ("parse error is an error, not wrong", isError (gradeAnswer sc ["D"] q2 (.formula "K[D"))),
  ("hint matched before generated", gradeMsg q1 (.worlds []) == "Select at least one world."),
  ("reachGoal: D observing reaches the goal", grade q3 (.controls ["D"]) == .ok true),
  ("reachGoal: nobody observing misses it", grade q3 (.controls []) == .ok false),
  ("reachGoal: unknown control is an error", isError (gradeAnswer sc ["D"] q3 (.controls ["Z"]))),
  ("answer of the wrong shape is an error", isError (gradeAnswer sc ["D"] q1 (.formula "p"))),
  ("scenario JSON round-trips",
    ((Scenario.ofJson (toJson sc)).map toJson) == .ok (toJson sc)),
  ("ofJson fills omitted hints and checks",
    ((Scenario.ofJson (parsed
      "{\"id\":\"s\",\"title\":\"t\",\"setup\":\"\",\"mode\":\"epistemic\",
        \"model\":{},\"controls\":{},\"layout\":[],
        \"questions\":[{\"id\":\"q\",\"prompt\":\"\",\"answer\":\"\",
          \"kind\":{\"clickWorlds\":{\"formula\":\"p\"}}}]}")).map
      (fun s => s.checks.length + (s.questions.map (·.hints.length)).sum)) == .ok 0),
  ("ofJson: a non-object question is an error, not a panic",
    isError (Scenario.ofJson (Json.mkObj [("questions", Json.arr #[Json.str "x"])]))),
  ("ofJson: a non-object scenario is an error", isError (Scenario.ofJson (Json.str "x"))),
  ("ATL-D: a skipped revoke leaves a note naming the agent and state",
    dynNotes.any (fun n => n.contains "nurse" && n.contains "s0")),
  ("ATL-D: no note where the revoke applied", !dynNotes.any (·.contains "s1")),
  ("ATL-D: revoke applied at s1", ((dsc.after ["noX"]).bind (·.truthSet "has(nurse,x)")) == .ok ["s0"]),
  ("ATL-D: before, x everywhere", ((dsc.before).bind (·.truthSet "has(nurse,x)")) == .ok ["s0", "s1"]),
  ("ATL-D: unknown clause label is an error", isError (dsc.after ["nope"]))
]

end DynamicExplorerTests
