import Widgets.Dynamic.Library
import Gamen.Atl.UpdateSearch

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

/-- Clause labels, as in the scenario files. -/
def referPatient : String := "grant primary : refer → {patient}"
def referStaff : String := "grant primary : refer → {staff}"
def revokeAll : String := "revoke ⊤ : override → {team}"
def revokeRoutine : String := "revoke routine : override → {team}"

/-- The controls applied before a click or formula question is answered. -/
def intendedSelection : String → List String
  | "click-handoff" => ["D"]
  | "write-lost-high" => ["D"]
  | "click-nurse-knows" => ["D", "N"]
  | "click-would-before" => []
  | "click-would-after" => [referPatient]
  | "write-has-refer" => [referPatient]
  | "click-staff-refer" => [referStaff]
  | "click-harm-before" => []
  | "click-given-revoked" => [revokeAll]
  | "click-has-override" => [revokeAll]
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

/-- `dsat` of a formula on a scenario's ATL-D model, built without the grader or
the controls format: updates are written in the formula itself. -/
def dTruth (sc : Except String Scenario) (f : String) : Except String (List String) := do
  let sc ← sc
  let m ← (Gamen.CgsJson.decodeDyn sc.model).mapError (·.message)
  pure (← Atl.Dynamic.dsat m .perfect (← Atl.Dynamic.parseDFormula f)).toList

/-- A scenario's clauses as an update-search pool, with their labels. -/
def poolOf (sc : Scenario) : Except String (List (String × Atl.Dynamic.Candidate)) := do
  let cs ← (sc.controls.getObjValD "clauses").getArr?
  cs.toList.mapM fun c => do
    let label ← (c.getObjValD "label").getStr?
    let kind ← (c.getObjValD "kind").getStr?
    let cond ← Atl.Dynamic.parseDFormula (← (c.getObjValD "cond").getStr?)
    let action ← (c.getObjValD "action").getStr?
    let agents ← (Lean.fromJson? (c.getObjValD "agents") : Except String (List String))
    pure (label, { grant := kind == "grant", cond, action, agents })

/-- `boundedUpdate` over the scenario's own clauses finds no grant with fewer
clauses than the stored answer to `reach-would`, and finds one of that size made
of exactly the stored answer's clauses. -/
def smallestGrantClaim : Except String Bool := do
  let sc ← wouldIfCould
  let q ← match sc.questions.find? (·.id == "reach-would") with
    | some q => pure q
    | none => throw "no question reach-would"
  let labels := q.answer.splitOn ","
  let pool ← poolOf sc
  let m ← (Gamen.CgsJson.decodeDyn sc.model).mapError (·.message)
  let goal ← Atl.Dynamic.parseDFormula "⟨⟨patient⟩⟩F treated"
  let n := labels.length
  let below ← Atl.Dynamic.boundedUpdate m .perfect "home" goal (n - 1) (pool.map (·.2)) 100000
  let at_ ← Atl.Dynamic.boundedUpdate m .perfect "home" goal n (pool.map (·.2)) 100000
  let noneSmaller := match below.outcome with | .notFound => true | .found .. => false
  let sameClauses := match at_.outcome with
    | .found steps size =>
      let found := steps.flatMap (·.clauses)
      let stored := pool.filter (labels.contains ·.1) |>.map (·.2)
      size == n && found.length == stored.length &&
        (found.zip stored).all fun (a, b) =>
          a.grant == b.grant && a.cond == b.cond && a.action == b.action && a.agents == b.agents
    | .notFound => false
  pure (noneSmaller && sameClauses)

/-- The reasonableness notes after revoking override everywhere. -/
def revokeAllNotes : Except String (List String) := do
  pure (← (← safetyAccess).after [revokeAll]).notes

def contains (s sub : String) : Bool := (s.splitOn sub).length > 1

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
  ("would-if-could and safety-access have 3-6 questions each",
    [wouldIfCould, safetyAccess].all fun r => match r with
      | .ok sc => sc.questions.length ≥ 3 && sc.questions.length ≤ 6
      | .error _ => false),
  ("library claim: before any grant, ⟨⟨patient⟩⟩F treated holds at specialist and treated only",
    dTruth wouldIfCould "⟨⟨patient⟩⟩F treated" == .ok ["specialist", "treated"]),
  ("library claim: granting refer to the patient at primary makes ⟨⟨patient⟩⟩F treated true everywhere",
    dTruth wouldIfCould "[primary:refer→{patient}]+⟨⟨patient⟩⟩F treated"
      == .ok ["home", "primary", "specialist", "treated"]),
  ("library claim: granting refer to the staff instead leaves the patient alone unable",
    dTruth wouldIfCould "[primary:refer→{staff}]+⟨⟨patient⟩⟩F treated" == .ok ["specialist", "treated"]),
  ("library claim: after the staff grant, patient and staff together can reach treated from anywhere",
    dTruth wouldIfCould "[primary:refer→{staff}]+⟨⟨patient,staff⟩⟩F treated"
      == .ok ["home", "primary", "specialist", "treated"]),
  ("library claim: a grant conditioned on ⟨⟨patient⟩⟩F treated lands only where it is already true",
    dTruth wouldIfCould "[⟨⟨patient⟩⟩F treated:refer→{patient}]+has(patient,refer)"
      == .ok ["specialist", "treated"]),
  ("library claim: at home the patient can force primary next, and can avoid treatment forever",
    (dTruth wouldIfCould "⟨⟨patient⟩⟩X primary").map (·.contains "home") == .ok true
      && (dTruth wouldIfCould "⟨⟨patient⟩⟩G ¬treated").map (·.contains "home") == .ok true),
  ("library claim: boundedUpdate finds no grant smaller than the stored answer",
    smallestGrantClaim == .ok true),
  ("library claim: before any revoke, ⟨⟨team⟩⟩F harm holds at routine and error",
    dTruth safetyAccess "⟨⟨team⟩⟩F harm" == .ok ["error", "routine"]),
  ("library claim: revoking override everywhere removes emergency access but not at crisis",
    dTruth safetyAccess "[⊤:override→{team}]-⟨⟨team⟩⟩F given" == .ok ["crisis", "given", "routine"]
      && dTruth safetyAccess "[⊤:override→{team}]-has(team,override)" == .ok ["crisis"]
      && dTruth safetyAccess "[⊤:override→{team}]-⟨⟨team⟩⟩F harm" == .ok ["error"]),
  ("library claim: revoking override at routine only keeps the team safe and able everywhere",
    dTruth safetyAccess
      "[routine:override→{team}]-((routine → ¬⟨⟨team⟩⟩F harm) ∧ (emergency → ⟨⟨team⟩⟩F given))"
      == .ok ["crisis", "emergency", "error", "given", "routine"]),
  ("the safety scenario's one reasonableness note names team at crisis",
    match revokeAllNotes with
    | .ok [n] => contains n "from team at crisis"
    | _ => false),
  ("revoking override in emergencies also keeps it at crisis only, with a note",
    match ((do pure (← (← safetyAccess).after ["revoke emergency : override → {team}"]).notes)
        : Except String _) with
    | .ok [n] => contains n "from team at crisis"
    | _ => false),
  ("the targeted revoke triggers no reasonableness note",
    ((do pure (← (← safetyAccess).after [revokeRoutine]).notes) : Except String _) == .ok []),
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
