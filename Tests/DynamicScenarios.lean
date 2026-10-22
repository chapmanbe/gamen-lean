import Widgets.Dynamic.Library
import Gamen.Atl.UpdateSearch

/-!
# The dynamic-explorer scenario library

Every shipped scenario decodes, and its answer key checks out: each question's
stored `answer` grades correct, and each hint's `answer` grades incorrect with
exactly that hint's text.

`clickWorlds` and `writeFormula` are graded on the model after the update the
student has applied, so the key needs that selection: each such question names
it in the data (`selection`), and any other selection is refused. `reachGoal`
questions are graded on the answer itself, which is the selection.
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
def referWhereTreatable : String := "grant ⟨⟨patient⟩⟩F treated : refer → {patient}"
def revokeAll : String := "revoke ⊤ : override → {team}"
def revokeRoutine : String := "revoke routine : override → {team}"
def grantHandoff : String := "grant handoff : order → {incoming}"
def grantHandoffInform : String := "grant handoff : order → {incoming} and inform {pharmacist}"
def grantEverywhere : String := "grant ⊤ : order → {incoming}"
def revokeOutgoing : String := "revoke handoff : order → {outgoing}"

/-- An answer in normalized form, as the question's kind expects it. -/
def answerOf (q : Question) (s : String) : Answer :=
  match q.kind with
  | .clickWorlds _ => .worlds (if s.isEmpty then [] else s.splitOn ",")
  | .writeFormula _ => .formula s
  | .reachGoal _ _ => .controls (if s.isEmpty then [] else s.splitOn ",")

/-- The selection a click or formula question is graded under: its own
`selection` from the data (every shipped one has it; see the case below). -/
def selectionFor (q : Question) : List String :=
  match q.kind with
  | .reachGoal _ _ => []
  | _ => q.selection.getD []

/-- Click and formula questions name their selection; `reachGoal` grades the
selection itself, so it names none. -/
def selectionNamed (q : Question) : Bool :=
  match q.kind with
  | .reachGoal _ _ => q.selection.isNone
  | _ => q.selection.isSome

/-- Grade `ans` to question `id` of `sc` under the controls `sel`. -/
def gradeUnder (sc : Except String Scenario) (id : String) (sel : List String) (ans : Answer) :
    Except String Feedback := do
  let sc ← sc
  let q ← (sc.questions.find? (·.id == id)).elim (throw s!"no question {id}") pure
  gradeAnswer sc sel q ans

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

/-- `dTruth` under a given `IrMode` (the shift-change scenario is ATEL-D, subjective). -/
def dTruthIn (mode : Atl.Dynamic.IrMode) (sc : Except String Scenario) (f : String) :
    Except String (List String) := do
  let sc ← sc
  let m ← (Gamen.CgsJson.decodeDyn sc.model).mapError (·.message)
  pure (← Atl.Dynamic.dsat m mode (← Atl.Dynamic.parseDFormula f)).toList

/-- Grade a question of the shift-change scenario: (correct, message). -/
def gradeShift (id : String) (ans : String) : Except String (Bool × String) := do
  let sc ← shiftChange
  let q ← (sc.questions.find? (·.id == id)).elim (throw s!"no question {id}") pure
  let f ← feedbackOf sc q ans
  pure (f.correct, f.message)

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

/-- Grade a selection for `reach-would`: (correct, message). -/
def reachWould (sel : List String) : Except String (Bool × String) := do
  let sc ← wouldIfCould
  let q ← (sc.questions.find? (·.id == "reach-would")).elim (throw "no question reach-would") pure
  let f ← gradeAnswer sc [] q (.controls sel)
  pure (f.correct, f.message)

/-- Whether `text` grades correct for `write-has-refer`. -/
def writeHasRefer (text : String) : Except String Bool := do
  let sc ← wouldIfCould
  let q ← (sc.questions.find? (·.id == "write-has-refer")).elim (throw "no question write-has-refer") pure
  pure (← feedbackOf sc q text).correct

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
  ("every click and formula question names its selection; no reachGoal does",
    allQuestions.all fun (_, q) => selectionNamed q),
  ("a stored answer grades with \"Correct.\", never a hint's text",
    allQuestions.all fun (sc, q) => ((feedbackOf sc q q.answer).map (·.message)) == .ok "Correct."),
  ("click-handoff: nobody observing and nothing clicked is refused, naming D",
    (gradeUnder handoff "click-handoff" [] (.worlds [])).map (·.correct) == .error
      "This question is about the model after selecting D only: tick D, press Apply, then answer."),
  ("click-nurse-knows: nothing clicked under no selection is refused",
    isOk (gradeUnder handoff "click-nurse-knows" [] (.worlds [])) == false),
  ("click-nurse-knows: nothing clicked under its own selection grades incorrect",
    ((gradeUnder handoff "click-nurse-knows" ["N", "D"] (.worlds [])).map (·.correct)) == .ok false),
  ("click-harm-before: after the ⊤ revoke, clicking only error is refused, asking for no update",
    (gradeUnder safetyAccess "click-harm-before" [revokeAll] (.worlds ["error"])).map (·.correct) == .error
      "This question is about the model before any update: untick every control, press Apply, then answer."),
  ("notebook claim (DynamicEpistemic): handoff's questions are click, formula, reach, click; \
      the first, second and fourth name a selection, the third does not",
    match handoff with
    | .ok sc =>
      (sc.questions.map fun q => match q.kind with
        | .clickWorlds _ => "click" | .writeFormula _ => "formula" | .reachGoal .. => "reach")
        == ["click", "formula", "reach", "click"]
      && sc.questions.map (·.selection.isSome) == [true, true, false, true]
    | .error _ => false),
  ("an unknown atom is an error: crisis (a state name) on safety-access",
    ((do (← safetyAccess).before >>= (·.truthSet "⟨⟨team⟩⟩F crisis")) : Except String _) == .error
      "crisis is not an atom of this model (atoms: emergency, given, harm, routine). \
        For an action, write has(agent,action)."),
  ("an unknown atom is an error: K[D]q on handoff, before and after",
    ((do (← handoff).before >>= (·.truthSet "K[D]q")) : Except String _) == .error
      "q is not an atom of this model (atoms: p)."
    && isOk ((do (← handoff).after ["D"] >>= (·.truthSet "K[D]q")) : Except String _) == false),
  ("an action written as an atom, or has without arguments, reaches the has(agent,action) advice",
    ["refer", "has"].all fun f =>
      match ((do (← wouldIfCould).after [referPatient] >>= (·.truthSet f)) : Except String _) with
      | .error e => contains e s!"{f} is not an atom" && contains e "write has(agent,action)"
      | .ok _ => false),
  ("an unknown atom inside an update condition is an error",
    isOk ((do (← wouldIfCould).before >>= (·.truthSet "[home:refer→{patient}]+⊤")) : Except String _)
      == false),
  ("a scenario's own atoms still work",
    ((do (← wouldIfCould).before >>= (·.truthSet "primary ∨ treated")) : Except String _)
      == .ok ["primary", "treated"]
    && ((do (← handoff).after ["D"] >>= (·.truthSet "p")) : Except String _) == .ok ["w1×lost", "w1×sent"]),
  ("every scenario's checks evaluate without error, before and under every named selection",
    scenarios.all fun sc =>
      let sels := [] :: sc.questions.filterMap (·.selection)
      sels.all fun sel => sc.checks.all fun c => isOk ((sc.after sel).bind (·.truthSet c))),
  ("a refusal quotes clause labels and joins them with and",
    (gradeUnder shiftChange "click-unaware" [] (.worlds [])).map (·.correct) == .error
      s!"This question is about the model after selecting \"{grantHandoff}\" and \"{revokeOutgoing}\" only: \
        tick \"{grantHandoff}\" and \"{revokeOutgoing}\", press Apply, then answer."),
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
  ("reach-would asks for a minimal selection; handoff's reachGoal (no minimal field) decodes as not minimal",
    (wouldIfCould.toOption.bind (·.questions.find? (·.id == "reach-would"))).map (·.minimal) == some true
      && (handoff.toOption.bind (·.questions.find? (·.id == "reach-handoff"))).map (·.minimal)
        == some false),
  ("reach-would: every grant ticked works but grades incorrect, naming unneeded grants",
    reachWould [referPatient, referStaff, referWhereTreatable] == .ok (false,
      s!"That works, but {referStaff}, {referWhereTreatable} are not needed: the goal is reached without them.")),
  ("reach-would: the right grant plus the staff grant grades incorrect, naming the staff grant",
    reachWould [referPatient, referStaff] == .ok (false,
      s!"That works, but {referStaff} is not needed: the goal is reached without it.")),
  ("reach-would: the right grant alone grades correct",
    reachWould [referPatient] == .ok (true, "Correct.")),
  ("write-has-refer: the atom primary no longer picks out the target",
    writeHasRefer "primary" == .ok false),
  ("shift-change has 4-6 questions and is ATEL-D in subjective mode",
    match shiftChange with
    | .ok sc => sc.questions.length ≥ 4 && sc.questions.length ≤ 6
        && (sc.controls.getObjValD "mode").getStr? == .ok "subjective"
    | .error _ => false),
  ("library claim: before any update, the pharmacist cannot tell new-shift from old-shift",
    dTruthIn .subjective shiftChange "handoff ∧ ¬K[pharmacist]handoff" == .ok ["new-shift"]
      && dTruthIn .subjective shiftChange "K[pharmacist]handoff" == .ok ["new-shift-present"]),
  ("library claim: both clinicians know whether the shift has changed, not whether the pharmacist was there",
    ["incoming", "outgoing"].all fun a =>
      dTruthIn .subjective shiftChange s!"K[{a}]handoff ∨ K[{a}]¬handoff"
        == .ok ["new-shift", "new-shift-present", "old-shift", "ordered"]
      && dTruthIn .subjective shiftChange s!"K[{a}]K[pharmacist]handoff" == .ok []),
  ("library claim: the uninformed ⊤ grant teaches the pharmacist nothing about handoff",
    (["K[pharmacist]handoff", "K[pharmacist]¬handoff"].all fun f =>
      dTruthIn .subjective shiftChange s!"[⊤:order→\{incoming}]+{f}" == dTruthIn .subjective shiftChange f)
      &&dTruthIn .subjective shiftChange "[⊤:order→{incoming}]+K[pharmacist]handoff"
        == .ok ["new-shift-present"]),
  ("library claim: the ⊤ grant lets the incoming clinician order before the shift change",
    (dTruthIn .subjective shiftChange "[⊤:order→{incoming}]+has(incoming,order)").map (·.contains "old-shift")
      == .ok true),
  ("library claim: after the handoff grant and revoke, incoming can order and knows it, the pharmacist does not know it",
    dTruthIn .subjective shiftChange
      "[handoff:order→{incoming},{incoming}]+([handoff:order→{outgoing}]-(has(incoming,order) ∧ K[incoming]has(incoming,order) ∧ ¬K[pharmacist]has(incoming,order)))"
      == .ok ["new-shift"]),
  ("library claim: with the pharmacist informed, the pharmacist knows incoming can order",
    dTruthIn .subjective shiftChange
      "[handoff:order→{incoming},{pharmacist}]+([handoff:order→{outgoing}]-K[pharmacist]has(incoming,order))"
      == .ok ["new-shift", "new-shift-present"]),
  ("library claim: a grant whose condition is ⊤ is known to the pharmacist everywhere, informed or not",
    dTruthIn .subjective shiftChange "[⊤:order→{incoming}]+K[pharmacist]has(incoming,order)"
      == .ok ["new-shift", "new-shift-present", "old-shift", "ordered"]
      && dTruthIn .subjective shiftChange "[⊤:order→{incoming},{pharmacist}]+K[pharmacist]has(incoming,order)"
        == .ok ["new-shift", "new-shift-present", "old-shift", "ordered"]),
  ("library claim (subjective): the ability to have an order placed moves from outgoing to incoming at the new-shift states",
    dTruthIn .subjective shiftChange "⟨⟨incoming⟩⟩X ordered" == .ok ["ordered"]
      && dTruthIn .subjective shiftChange "⟨⟨outgoing⟩⟩X ordered"
        == .ok ["new-shift", "new-shift-present", "old-shift", "ordered"]
      && dTruthIn .subjective shiftChange
        "[handoff:order→{incoming}]+([handoff:order→{outgoing}]-⟨⟨incoming⟩⟩X ordered)"
        == .ok ["new-shift", "new-shift-present", "ordered"]
      && dTruthIn .subjective shiftChange
        "[handoff:order→{incoming}]+([handoff:order→{outgoing}]-⟨⟨outgoing⟩⟩X ordered)"
        == .ok ["old-shift", "ordered"]),
  ("the shift-change revoke triggers no reasonableness note",
    ((do pure (← (← shiftChange).after [grantHandoff, revokeOutgoing]).notes) : Except String _) == .ok []),
  ("reach-informed is minimal; the handoff grant without informing grades incorrect",
    (shiftChange.toOption.bind (·.questions.find? (·.id == "reach-informed"))).map (·.minimal) == some true
      && (gradeShift "reach-informed" s!"{grantHandoff},{revokeOutgoing}").map (·.1) == .ok false),
  ("reach-informed: both handoff grants plus the revoke works but names the uninformed grant as not needed",
    gradeShift "reach-informed" s!"{grantHandoff},{grantHandoffInform},{revokeOutgoing}" == .ok (false,
      s!"That works, but {grantHandoff} is not needed: the goal is reached without it.")),
  ("reach-informed: the ⊤ grant plus the revoke grades incorrect (incoming could order before the handoff)",
    (gradeShift "reach-informed" s!"{grantEverywhere},{revokeOutgoing}").map (·.1) == .ok false),
  ("write-knows-whether: the atoms handoff and ordered do not pick out the target",
    (gradeShift "write-knows-whether" "handoff ∨ ordered").map (·.1) == .ok false
      && (gradeShift "write-knows-whether" "handoff").map (·.1) == .ok false),
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
