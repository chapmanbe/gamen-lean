import Gamen.ActionModel
import Gamen.EpistemicJson
import Gamen.CgsJson
import Gamen.Input
import Gamen.Atl.DynamicInput

/-!
# Dynamic-scenarios explorer: scenario format and models per mode

A `Scenario` is data (JSON): a model, the update controls a student toggles, a
layout for drawing, and graded questions. `Scenario.before` and `Scenario.after`
turn it into an `Evaluable`, a mode-independent view the widget draws and the
grader evaluates on.

Controls, per mode (`selected` holds control keys):

* `epistemic`: `{"events": [...], "pre": {"e": "φ"}, "post": {"e": {"p": "φ"}},
  "toggleable": ["N", "D"], "observers": ["D"]}`. The key is an agent name. A
  selected agent *observes* the event (identity relation over events); an
  unselected one considers every event possible (full relation). Agents not in
  `toggleable` take their fixed role from `observers`. The update is the product
  `M × A` (`mkActionModel`, `productUpdate`); worlds are named `w×e`.
* `atlD`: `{"mode": "perfect" | "subjective" | "objective", "clauses":
  [{"label", "kind": "grant" | "revoke", "cond", "action", "agents",
  "informed"}]}`. The key is a clause label. Selected clauses apply in listed
  order, consecutive clauses of the same kind as one simultaneous update
  (`dclauses`, then `updateModel`). Where the reasonableness rule skips a revoke
  (it would leave an agent no action at a state), the `Evaluable` carries a note.

Every failure (decoding, parsing, evaluation) is an `Except` error, never a
default value.
-/

namespace Gamen.Widgets.Dynamic

open Lean (Json ToJson FromJson toJson fromJson?)
open Gamen.Atl.Dynamic

/-- Which logic a scenario's model and controls are in. -/
inductive Mode
  | epistemic
  | atlD
  deriving ToJson, FromJson, Inhabited, BEq, Repr

/-- Where to draw a world. -/
structure WorldPos where
  name : String
  x : Float
  y : Float
  deriving ToJson, FromJson, Inhabited

inductive QuestionKind
  /-- Click the worlds where `formula` holds after the update. -/
  | clickWorlds (formula : String)
  /-- Choose controls so that `goal` holds at `atWorld` (`none`: at every world). -/
  | reachGoal (goal : String) (atWorld : Option String)
  /-- Write any formula true exactly at `target` after the update. -/
  | writeFormula (target : List String)
  deriving ToJson, FromJson, Inhabited

/-- Feedback for one specific answer; `answer` is in normalized form (worlds or
controls sorted and comma-joined, formulas as their text). -/
structure Hint where
  answer : String
  text : String
  deriving ToJson, FromJson, Inhabited

structure Question where
  id : String
  prompt : String
  kind : QuestionKind
  /-- The reference answer, normalized. -/
  answer : String
  hints : List Hint := []
  deriving ToJson, FromJson, Inhabited

structure Scenario where
  id : String
  title : String
  setup : String
  mode : Mode
  model : Json
  controls : Json
  layout : List WorldPos
  /-- Formulas whose truth sets are always shown. -/
  checks : List String := []
  questions : List Question
  deriving ToJson, FromJson, Inhabited

/-- A model the explorer can evaluate on, whatever the logic. -/
structure Evaluable where
  worlds : List String
  /-- (agent or action label, from, to), for drawing. -/
  edges : List (String × String × String)
  /-- world ↦ true atoms. -/
  facts : List (String × List String)
  /-- Parse and evaluate a formula; the worlds where it holds, sorted. -/
  truthSet : String → Except String (List String)
  /-- agent, world ↦ the worlds the agent cannot tell from it. -/
  access : String → String → List String
  /-- E.g. reasonableness-rule messages. -/
  notes : List String := []

/-! ## JSON helpers -/

private def field (j : Json) (k ctx : String) : Except String Json :=
  match j.getObjVal? k with
  | .ok v => pure v
  | .error _ => throw s!"{ctx}: key \"{k}\" not found"

private def strList (ctx : String) (j : Json) : Except String (List String) :=
  (fromJson? j : Except String (List String)).mapError fun e => s!"{ctx}: {e}"

private def str (ctx : String) (j : Json) : Except String String :=
  j.getStr?.mapError fun e => s!"{ctx}: {e}"

/-- An optional object field as its entries (absent or `null`: none). -/
private def entries (j : Json) (k ctx : String) : Except String (List (String × Json)) :=
  match j.getObjVal? k with
  | .error _ | .ok .null => pure []
  | .ok v => do
    let o ← v.getObj?.mapError fun e => s!"{ctx}.{k}: {e}"
    pure o.toList

/-- Decode a scenario. `hints` and `checks` may be omitted (empty). -/
def Scenario.ofJson (j : Json) : Except String Scenario := do
  let withDefault (o : Json) (k : String) : Json :=
    match o.getObjVal? k with
    | .ok _ => o
    | .error _ => o.setObjVal! k (Json.arr #[])
  let qs ← (j.getObjValD "questions").getArr?.mapError fun e => s!"scenario.questions: {e}"
  let j := (withDefault j "checks").setObjVal! "questions"
    (Json.arr (qs.map fun q => withDefault q "hints"))
  (fromJson? j : Except String Scenario).mapError fun e => s!"scenario: {e}"

/-- A key `selected` that names no control is an error, not ignored. -/
private def checkKeys (keys selected : List String) : Except String Unit :=
  match selected.find? (!keys.contains ·) with
  | some k => throw s!"unknown control \"{k}\""
  | none => pure ()

/-! ## Epistemic mode -/

private def epiEvaluable (m : EpistemicModel) : Evaluable :=
  let ws := m.eFrame.eWorlds.toList
  { worlds := ws
    edges := m.eFrame.eRelations.toList.flatMap fun (a, r) =>
      ws.flatMap fun w => (r.getD w ∅).toList.map fun w' => (a, w, w')
    facts := ws.map fun w =>
      (w, m.eValuation.toList.filterMap fun (p, s) => if s.contains w then some p.name else none)
    truthSet := fun s => do
      let f ← parseFormula s
      ws.filterM fun w => eSatisfies m w f
    access := fun a w =>
      match eAccessible m.eFrame a w with
      | .ok s => s.toList
      | .error _ => [] }

private def epiModel (sc : Scenario) : Except String EpistemicModel :=
  (EpistemicJson.decodeModel sc.model).mapError (·.message)

/-- The action model the selection describes. -/
private def epiActionModel (agents : List String) (c : Json) (selected : List String) :
    Except String ActionModel := do
  let events ← strList "controls.events" (← field c "events" "controls")
  let toggleable ← strList "controls.toggleable" ((c.getObjVal? "toggleable").toOption.getD (.arr #[]))
  let observers ← strList "controls.observers" ((c.getObjVal? "observers").toOption.getD (.arr #[]))
  checkKeys toggleable selected
  let pre ← (← entries c "pre" "controls").mapM fun (e, f) => do
    pure (e, ← parseFormula (← str s!"controls.pre.{e}" f))
  let post ← (← entries c "post" "controls").mapM fun (e, ps) => do
    let o ← ps.getObj?.mapError fun err => s!"controls.post.{e}: {err}"
    let ps ← o.toList.mapM fun (p, f) => do
      pure (p, ← parseFormula (← str s!"controls.post.{e}.{p}" f))
    pure (e, ps)
  let rels := agents.map fun a =>
    let observes := if toggleable.contains a then selected.contains a else observers.contains a
    (a, if observes then events.map fun e => (e, e)
        else events.flatMap fun e => events.map fun e' => (e, e'))
  mkActionModel events agents rels pre post

/-! ## ATL-D mode -/

private structure DClause where
  label : String
  grant : Bool
  cond : DFormula
  action : String
  agents : List String
  informed : List String

private def dClause (j : Json) : Except String DClause := do
  let label ← str "clause.label" (← field j "label" "clause")
  let ctx := s!"clause \"{label}\""
  let grant ← match ← str s!"{ctx}.kind" (← field j "kind" ctx) with
    | "grant" => pure true
    | "revoke" => pure false
    | k => throw s!"{ctx}: kind must be \"grant\" or \"revoke\", not \"{k}\""
  let cond ← parseDFormula (← str s!"{ctx}.cond" (← field j "cond" ctx))
  let action ← str s!"{ctx}.action" (← field j "action" ctx)
  let agents ← strList s!"{ctx}.agents" (← field j "agents" ctx)
  let informed ← strList s!"{ctx}.informed" ((j.getObjVal? "informed").toOption.getD (.arr #[]))
  pure { label, grant, cond, action, agents, informed }

private def dControls (c : Json) : Except String (IrMode × List DClause) := do
  let mode ← match ← str "controls.mode" (← field c "mode" "controls") with
    | "perfect" => pure IrMode.perfect
    | "subjective" => pure .subjective
    | "objective" => pure .objective
    | k => throw s!"controls.mode: expected perfect, subjective or objective, not \"{k}\""
  let cs ← (← field c "clauses" "controls").getArr?.mapError fun e => s!"controls.clauses: {e}"
  pure (mode, ← cs.toList.mapM dClause)

private def jointLabel (jm : Std.TreeMap String String) : String :=
  ", ".intercalate (jm.toList.map fun (a, α) => s!"{a}={α}")

private def dynEvaluable (m : DynModel) (mode : IrMode) (notes : List String) : Evaluable :=
  let cgs := m.cgs
  let ws := cgs.cgsStates.toList
  { worlds := ws
    edges := ws.flatMap fun v =>
      (jointMoves cgs cgs.cgsAgents v).filterMap fun jm =>
        if m.specified v jm then some (jointLabel jm, v, cgs.cgsTransition v jm) else none
    facts := ws.map fun v => (v, (cgs.cgsLabeling v).toList)
    truthSet := fun s => do
      let f ← parseDFormula s
      pure (← dsat m mode f).toList
    access := fun a v => (m.epistemic a v).toList
    notes }

private def dynModel (sc : Scenario) : Except String DynModel :=
  (CgsJson.decodeDyn sc.model).mapError (·.message)

/-- Consecutive clauses of the same kind, in order. -/
private def runs : List DClause → List (List DClause)
  | [] => []
  | c :: cs =>
    match runs cs with
    | (d :: ds) :: rest => if d.grant == c.grant then (c :: d :: ds) :: rest else [c] :: (d :: ds) :: rest
    | rest => [c] :: rest

private def toUpdateList : List DClause → UpdateList
  | [] => .nil
  | c :: cs => .cons c.cond c.action c.agents c.informed (toUpdateList cs)

/-- Apply one simultaneous update, as `dsat` does for `[…]+` / `[…]-`, and note
every (agent, state) where a revoke was skipped by the reasonableness rule. -/
private def applyRun (m : DynModel) (mode : IrMode) (grant : Bool) (cs : List DClause) :
    Except String (DynModel × List String) := do
  let clauses ← dclauses m mode (toUpdateList cs)
  let m' := updateModel m grant clauses
  if grant then checkSpecified m'
  checkEpistemic m'
  if grant then return (m', [])
  let notes := m.cgs.cgsStates.toList.flatMap fun v =>
    m.cgs.cgsAgents.toList.filterMap fun a =>
      let x := clauses.filterMap fun (sv, α, as, _) =>
        if sv.contains v && as.contains a then some α else none
      let d := m.cgs.cgsMoves v a
      let d' := m'.cgs.cgsMoves v a
      if x.any d.contains && d'.toList == d.toList then
        some s!"Revoking {", ".intercalate x.eraseDups} from {a} at {v} would leave {a} \
          no action there, so {a} keeps {", ".intercalate d.toList} (reasonableness)."
      else none
  return (m', notes)

/-! ## Before and after -/

/-- The scenario's model, before any update. -/
def Scenario.before (sc : Scenario) : Except String Evaluable := do
  match sc.mode with
  | .epistemic => pure (epiEvaluable (← epiModel sc))
  | .atlD =>
    let (mode, _) ← dControls sc.controls
    pure (dynEvaluable (← dynModel sc) mode [])

/-- The model after the update that the `selected` controls describe. -/
def Scenario.after (sc : Scenario) (selected : List String) : Except String Evaluable := do
  match sc.mode with
  | .epistemic =>
    let m ← epiModel sc
    let am ← epiActionModel (m.eFrame.eRelations.toList.map (·.1)) sc.controls selected
    pure (epiEvaluable (← productUpdate m am))
  | .atlD =>
    let (mode, clauses) ← dControls sc.controls
    checkKeys (clauses.map (·.label)) selected
    let chosen := clauses.filter (selected.contains ·.label)
    let mut m ← dynModel sc
    let mut notes : List String := []
    for run in runs chosen do
      match run with
      | [] => pure ()
      | c :: _ =>
        let (m', ns) ← applyRun m mode c.grant run
        m := m'
        notes := notes ++ ns
    pure (dynEvaluable m mode notes)

end Gamen.Widgets.Dynamic
