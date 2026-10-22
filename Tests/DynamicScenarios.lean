import Widgets.Dynamic.Library

/-!
# The dynamic-explorer scenario library

Every shipped scenario decodes, and its answer key checks out: each question's
stored `answer` grades correct, and each hint's `answer` grades incorrect with
exactly that hint's text.

`clickWorlds` and `writeFormula` are graded on the model after the update the
student has applied, so the key needs that selection. `intendedSelection`
records it per question id; `reachGoal` questions are graded on the answer
itself, which is the selection.
-/

namespace DynamicScenariosTests

open Gamen Gamen.Widgets.Dynamic Gamen.Widgets.Dynamic.Library

/-- `Except` has no `BEq` in core; compare successes by value and failures by message. -/
local instance {ε α : Type} [BEq ε] [BEq α] : BEq (Except ε α) where
  beq
    | .ok a, .ok b => a == b
    | .error a, .error b => a == b
    | _, _ => false

def isOk {α : Type} (r : Except String α) : Bool :=
  match r with | .ok _ => true | .error _ => false

/-- The controls applied before a click or formula question is answered. -/
def intendedSelection : String → List String
  | "click-handoff" => ["D"]
  | "write-lost-high" => ["D"]
  | "click-nurse-knows" => ["D", "N"]
  | _ => []

/-- An answer in normalized form, as the question's kind expects it. -/
def answerOf (q : Question) (s : String) : Answer :=
  match q.kind with
  | .clickWorlds _ => .worlds (if s.isEmpty then [] else s.splitOn ",")
  | .writeFormula _ => .formula s
  | .reachGoal _ _ => .controls (if s.isEmpty then [] else s.splitOn ",")

def selectionFor (q : Question) : List String :=
  match q.kind with
  | .reachGoal _ _ => []
  | _ => intendedSelection q.id

/-- Grade `s` as an answer to `q` in `sc`. -/
def feedbackOf (sc : Scenario) (q : Question) (s : String) : Except String Feedback :=
  gradeAnswer sc (selectionFor q) q (answerOf q s)

def keyOk (sc : Scenario) (q : Question) : Bool :=
  ((feedbackOf sc q q.answer).map (·.correct)) == .ok true

def hintsOk (sc : Scenario) (q : Question) : Bool :=
  q.hints.all fun h =>
    ((feedbackOf sc q h.answer).map fun f => (f.correct, f.message)) == .ok (false, h.text)

def scenarios : List Scenario := allScenarios.filterMap fun (_, r) => r.toOption

def allQuestions : List (Scenario × Question) :=
  scenarios.flatMap fun sc => sc.questions.map (sc, ·)

/-- The handoff story built without the grader or the controls format. -/
def handoffClaim : Except String Bool := do
  let sc ← handoff
  let m ← (Gamen.EpistemicJson.decodeModel sc.model).mapError (·.message)
  let p ← parseFormula "p"
  let am ← mkActionModel ["sent", "lost"] ["N", "D"]
    [("N", [("sent", "sent"), ("sent", "lost"), ("lost", "sent"), ("lost", "lost")]),
     ("D", [("sent", "sent"), ("lost", "lost")])]
    [("sent", p)]
  let m' ← productUpdate m am
  let f ← parseFormula "K[D]p ∧ ¬K[N]K[D]p"
  eSatisfies m' "w1×sent" f

def cases : List (String × Bool) := [
  ("every library scenario decodes",
    allScenarios.all (fun (_, r) => isOk r) && !allScenarios.isEmpty),
  ("handoff has 4-5 questions of mixed kinds",
    match handoff with
    | .ok sc => sc.questions.length ≥ 4 && sc.questions.length ≤ 5
    | .error _ => false),
  ("every question has at least one hint",
    allQuestions.all fun (_, q) => !q.hints.isEmpty),
  ("every stored answer grades correct",
    allQuestions.all fun (sc, q) => keyOk sc q),
  ("every hint grades incorrect with exactly its text",
    allQuestions.all fun (sc, q) => hintsOk sc q),
  ("library claim: K[D]p ∧ ¬K[N]K[D]p at w1×sent, built directly",
    handoffClaim == .ok true),
  ("a load error names the data file",
    match load "x.json" "{" with
    | .error e => e.startsWith "x.json: "
    | .ok _ => false),
  ("dynamicExplorerOr on an error renders a paragraph with the message",
    match Gamen.Widgets.dynamicExplorerOr (.error "x.json: boom") with
    | ProofWidgets.Html.element "p" _ cs => cs.size == 1
    | _ => false)
]

/-- `include_str` data is not tracked by Lake, so a stale build would grade the
old JSON. Re-read each scenario file at run time (relative to the repository
root, where `lake test` runs, like `data/specs/`) and compare with the embedded
scenario. -/
def diskCases : IO (List (String × Bool)) := do
  let mut out := []
  for (file, embedded) in allScenarios do
    let text ← try IO.FS.readFile file catch e => pure s!"<unreadable: {e}>"
    let fresh := load file text
    let same := match fresh, embedded with
      | .ok a, .ok b => Lean.toJson a == Lean.toJson b
      | _, _ => false
    out := out ++ [(s!"{file}: embedded scenario matches the file on disk (rebuild if not)", same)]
  return out

end DynamicScenariosTests
