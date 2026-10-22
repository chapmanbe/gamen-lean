import Widgets.Dynamic.Explorer

/-!
# The dynamic-scenarios explorer: scenario format and grader

A two-world epistemic scenario (agents N and D; events `sent` and `lost`, with
`pre(sent) = p`) and a one-agent ATL-D model whose revocation would empty
`d(nurse, s0)` and so is skipped there by the reasonableness rule.
-/

namespace DynamicExplorerTests

open Lean (Json ToJson toJson fromJson?)
open Gamen.Widgets.Dynamic

/-- `Except` has no `BEq` in core; compare successes by value and failures by message. -/
local instance {ε α : Type} [BEq ε] [BEq α] : BEq (Except ε α) where
  beq
    | .ok a, .ok b => a == b
    | .error a, .error b => a == b
    | _, _ => false

def isOk {α : Type} (r : Except String α) : Bool :=
  match r with | .ok _ => true | .error _ => false

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

def replayOn (s : Scenario) (es : List Event) : ExplorerState :=
  es.foldl step (ExplorerState.init s)

def replay (es : List Event) : ExplorerState := replayOn sc es

/-- Every event is ruled out by `pre`, so no world survives the product. -/
def noSurvivorControls : Json := parsed
  "{\"events\":[\"sent\"],\"pre\":{\"sent\":\"⊥\"},\"post\":{},
    \"toggleable\":[],\"observers\":[]}"

def noSurvivor : Scenario := { sc with controls := noSurvivorControls }

def viewField (s : ExplorerState) (k : String) : Json := (view s).getObjValD k

def viewWorlds (s : ExplorerState) : Nat :=
  (((viewField s "model").getObjValD "worlds").getArr?.toOption.map (·.size)).getD 99

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
  ("ATL-D: unknown clause label is an error", isError (dsc.after ["nope"])),
  ("submit before apply asks to apply",
    (replay [.submit]).message == some "Apply the update first."),
  ("apply then correct click grades true",
    (replay [.toggleControl "D", .apply, .clickWorld "w1×sent", .submit]).feedback.map (·.correct)
      == some true),
  ("apply then wrong click grades false",
    (replay [.toggleControl "D", .apply, .clickWorld "w1×lost", .submit]).feedback.map (·.correct)
      == some false),
  ("toggle after apply un-applies",
    (replay [.toggleControl "D", .apply, .toggleControl "N"]).applied == false),
  ("toggle after apply clears clicks and feedback",
    let s := replay [.toggleControl "D", .apply, .clickWorld "w1×sent", .submit, .toggleControl "N"]
    s.clicked.isEmpty && s.feedback.isNone),
  ("apply shows the after model", (replay [.toggleControl "D", .apply]).applied == true),
  ("click toggles membership",
    (replay [.toggleControl "D", .apply, .clickWorld "w1×sent", .clickWorld "w1×sent"]).clicked == []),
  ("click unknown world is a message",
    (replay [.toggleControl "D", .apply, .clickWorld "w9"]).message.isSome),
  ("click on a before-model world after apply is a message",
    (replay [.toggleControl "D", .apply, .clickWorld "w1"]).message.isSome),
  ("next past last clamps",
    (replay (List.replicate 20 .nextQuestion)).question == sc.questions.length - 1),
  ("prev before first clamps", (replay [.prevQuestion, .prevQuestion]).question == 0),
  ("next clears clicks, formula and feedback",
    let s := replay [.toggleControl "D", .apply, .clickWorld "w1×sent", .setFormula "p", .submit, .nextQuestion]
    s.clicked.isEmpty && s.formulaText == "" && s.feedback.isNone),
  ("empty update keeps before", (replayOn noSurvivor [.apply]).applied == false),
  ("empty update says so",
    (replayOn noSurvivor [.apply]).message == some "No world survives this update."),
  ("writeFormula question submits the formula",
    (replay [.toggleControl "D", .apply, .nextQuestion, .setFormula "K[D]p", .submit]).feedback.map
      (·.correct) == some true),
  ("writeFormula parse error lands in message",
    let s := replay [.toggleControl "D", .apply, .nextQuestion, .setFormula "K[D", .submit]
    s.message.isSome && s.feedback.isNone),
  ("reachGoal grades the selection without apply",
    (replay [.toggleControl "D", .nextQuestion, .nextQuestion, .submit]).feedback.map (·.correct)
      == some true),
  ("unknown control at apply is a message", (replay [.toggleControl "Z", .apply]).message.isSome),
  ("reset clears selection and application",
    let s := replay [.toggleControl "D", .apply, .reset]
    s.selected.isEmpty && !s.applied),
  ("state round-trips JSON",
    isOk (fromJson? (toJson (replay [.toggleControl "D", .apply])) : Except String ExplorerState)),
  ("event round-trips JSON",
    isOk (fromJson? (toJson (Event.clickWorld "w")) : Except String Event)),
  ("view before apply shows the before worlds", viewWorlds (replay []) == 2),
  ("view after apply shows the after worlds", viewWorlds (replay [.toggleControl "D", .apply]) == 3),
  ("view marks clicked worlds",
    (toJson (view (replay [.toggleControl "D", .apply, .clickWorld "w1×sent"]))).compress.contains
      "\"clicked\":true"),
  ("view of a world missing from layout notes it",
    let s := replayOn { sc with layout := [] } []
    ((viewField s "message").getStr?.toOption.getD "").contains "w1")
]

end DynamicExplorerTests
