import Widgets.Dynamic.Grade

/-!
# Dynamic-scenarios explorer: the state machine

Pure logic for the widget: `step` folds an `Event` into an `ExplorerState`, and
`view` renders a state as the JSON the widget draws. `step` is total: every
`Except` error from the scenario or the grader lands in `message`, shown to the
student verbatim.

The student toggles controls, applies the update to see the model after it, then
answers the current question. `clickWorlds` and `writeFormula` questions are about
the model *after* the update, so they need `apply` first (and, when the question
names its `selection`, exactly those controls); `reachGoal` grades the selected
controls themselves.
-/

namespace Gamen.Widgets.Dynamic

open Lean (Json ToJson FromJson toJson)

structure ExplorerState where
  scenario : Scenario
  /-- Current control keys. -/
  selected : List String
  /-- Showing the model after the update. -/
  applied : Bool := false
  question : Nat := 0
  clicked : List String := []
  formulaText : String := ""
  feedback : Option Feedback := none
  /-- Errors and prompts, shown verbatim; replaced by the next event. -/
  message : Option String := none
  /-- What the update did (e.g. a skipped revoke); kept while the after model is shown. -/
  notes : List String := []
  deriving ToJson, FromJson, Inhabited

inductive Event
  | toggleControl (key : String)
  | apply
  | reset
  | clickWorld (w : String)
  | setFormula (text : String)
  | submit
  | nextQuestion
  | prevQuestion
  deriving ToJson, FromJson, Inhabited

def ExplorerState.init (sc : Scenario) : ExplorerState :=
  { scenario := sc, selected := [] }

/-- The model the student currently sees. -/
private def ExplorerState.shown (s : ExplorerState) : Except String Evaluable :=
  if s.applied then s.scenario.after s.selected else s.scenario.before

private def toggle (x : String) (xs : List String) : List String :=
  if xs.contains x then xs.filter (· != x) else xs ++ [x]

private def ExplorerState.currentQuestion (s : ExplorerState) : Option Question :=
  s.scenario.questions[s.question]?

private def ExplorerState.moveTo (s : ExplorerState) (i : Nat) : ExplorerState :=
  { s with question := i, clicked := [], formulaText := "", feedback := none, message := none }

private def ExplorerState.doApply (s : ExplorerState) : ExplorerState :=
  match s.scenario.after s.selected with
  | .error e => { s with message := some e }
  | .ok ev =>
    if ev.worlds.isEmpty then
      { s with applied := false, clicked := [], feedback := none, notes := [],
               message := some "No world survives this update." }
    else
      { s with applied := true, clicked := [], feedback := none,
               message := none, notes := ev.notes }

private def ExplorerState.doClick (s : ExplorerState) (w : String) : ExplorerState :=
  match s.shown with
  | .error e => { s with message := some e }
  | .ok ev =>
    if ev.worlds.contains w then
      { s with clicked := toggle w s.clicked, feedback := none, message := none }
    else
      { s with message := some s!"There is no world \"{w}\" in the model shown." }

private def ExplorerState.doSubmit (s : ExplorerState) : ExplorerState :=
  match s.currentQuestion with
  | none => { s with message := some "There is no question to answer." }
  | some q =>
    -- a wrong selection says what to tick before "Apply the update first."
    let answer : Except String Answer := checkSelection q s.selected *>
      match q.kind with
      | .reachGoal .. => pure (.controls s.selected)
      | .clickWorlds _ =>
        if s.applied then pure (.worlds s.clicked) else throw "Apply the update first."
      | .writeFormula _ =>
        if s.applied then pure (.formula s.formulaText) else throw "Apply the update first."
    match answer >>= gradeAnswer s.scenario s.selected q with
    | .ok f => { s with feedback := some f, message := none }
    | .error e => { s with feedback := none, message := some e }

/-- One transition. Total: errors become `message`. -/
def step (s : ExplorerState) (e : Event) : ExplorerState :=
  match e with
  | .toggleControl k =>
    { s with selected := toggle k s.selected, applied := false, clicked := [],
             feedback := none, message := none, notes := [] }
  | .apply => s.doApply
  | .reset => { ExplorerState.init s.scenario with question := s.question }
  | .clickWorld w => s.doClick w
  | .setFormula t => { s with formulaText := t, feedback := none }
  | .submit => s.doSubmit
  | .nextQuestion =>
    s.moveTo (min (s.question + 1) (s.scenario.questions.length - 1))
  | .prevQuestion => s.moveTo (s.question - 1)

/-! ## View -/

/-- Vertical gap between product worlds sharing a layout entry. Assumes layout
coordinates in [0, 1] and nodes drawn at most 0.1 across. -/
private def siblingGap : Float := 0.12

/-- A world's drawing position: from the layout (a product world `w×e` takes `w`'s
position, stacked vertically by `siblingGap` by its index among the worlds sharing
it, toward the middle of [0, 1] and clamped into it), else on a circle. -/
private def position (layout : List WorldPos) (worlds : List String) (w : String) :
    Option (Float × Float) :=
  let base (v : String) := (v.splitOn "×").headD v
  match layout.find? (·.name == w) with
  | some p => some (p.x, p.y)
  | none =>
    (layout.find? (·.name == base w)).map fun p =>
      let siblings := worlds.filter (base · == base w)
      let k := (siblings.findIdx? (· == w)).getD 0
      let dir := if p.y + siblingGap * (siblings.length - 1).toFloat ≤ 1 then 1.0 else -1.0
      (min 1 (max 0 p.x), min 1 (max 0 (p.y + dir * siblingGap * k.toFloat)))

private def circle (n i : Nat) : Float × Float :=
  let a := 2 * 3.141592653589793 * i.toFloat / (max n 1).toFloat
  (0.5 + 0.4 * Float.cos a, 0.5 + 0.4 * Float.sin a)

private def evaluableView (s : ExplorerState) (ev : Evaluable) : Json × List String :=
  let n := ev.worlds.length
  let placed := ev.worlds.zipIdx.map fun (w, i) =>
    (w, i, position s.scenario.layout ev.worlds w)
  let unplaced := placed.filterMap fun (w, _, p) => if p.isNone then some w else none
  let worlds := placed.map fun (w, i, p) =>
    let (x, y) := p.getD (circle n i)
    Json.mkObj [("name", toJson w), ("x", toJson x), ("y", toJson y),
      ("facts", toJson ((ev.facts.find? (·.1 == w)).map (·.2) |>.getD [])),
      ("clicked", toJson (s.clicked.contains w))]
  let edges := ev.edges.map fun e =>
    Json.mkObj [("label", toJson e.label), ("from", toJson e.src), ("to", toJson e.dst),
      ("dashed", toJson e.dflt)]
  (Json.mkObj [("worlds", Json.arr worlds.toArray), ("edges", Json.arr edges.toArray)], unplaced)

private def checkView (ev : Evaluable) (f : String) : Json :=
  match ev.truthSet f with
  | .ok ws => Json.mkObj [("formula", toJson f), ("worlds", toJson ws)]
  | .error e => Json.mkObj [("formula", toJson f), ("error", toJson e)]

/-- The JSON the widget draws. -/
def view (s : ExplorerState) : Json :=
  let sc := s.scenario
  let (model, checks, notes) :=
    match s.shown with
    | .error _ => (Json.mkObj [("worlds", Json.arr #[]), ("edges", Json.arr #[])], [], [])
    | .ok ev =>
      let (m, unplaced) := evaluableView s ev
      (m, sc.checks.map (checkView ev),
       if unplaced.isEmpty then []
       else [s!"Data error: no layout position for {", ".intercalate unplaced}."])
  let parts := (s.message.toList ++ (match s.shown with | .error e => [e] | .ok _ => []) ++ notes)
  let message := if parts.isEmpty then Json.null else toJson (" ".intercalate parts.eraseDups)
  let controls : List String :=
    match sc.mode with
    | .epistemic => ((sc.controls.getObjValD "toggleable").getArr?.toOption.getD #[]).toList.filterMap
        (·.getStr?.toOption)
    | .atlD => ((sc.controls.getObjValD "clauses").getArr?.toOption.getD #[]).toList.filterMap
        fun c => (c.getObjValD "label").getStr?.toOption
  let question :=
    match s.currentQuestion with
    | none => Json.null
    | some q => Json.mkObj [("index", toJson s.question), ("count", toJson sc.questions.length),
        ("id", toJson q.id), ("prompt", toJson q.prompt),
        ("kind", toJson (match q.kind with
          | .clickWorlds _ => "clickWorlds" | .reachGoal .. => "reachGoal"
          | .writeFormula _ => "writeFormula" : String))]
  Json.mkObj [
    ("title", toJson sc.title), ("setup", toJson sc.setup),
    ("controls", Json.arr (controls.map fun k =>
      Json.mkObj [("key", toJson k), ("label", toJson k), ("on", toJson (s.selected.contains k))]).toArray),
    ("model", model), ("checks", Json.arr checks.toArray),
    ("question", question), ("formulaText", toJson s.formulaText),
    ("feedback", toJson s.feedback), ("message", message), ("notes", toJson s.notes), ("applied", toJson s.applied)]

end Gamen.Widgets.Dynamic
