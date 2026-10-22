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
default value. That includes a formula (or clause condition, `pre` or `post`)
naming an atom the model does not have, which the evaluators alone would read
as false everywhere.
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
  /-- For `reachGoal` only: also require the selection to be minimal. A selection
  that reaches the goal grades incorrect when a strict subset of it also does
  (`gradeAnswer`). Optional in the JSON (absent: `false`). -/
  minimal : Bool := false
  /-- For `clickWorlds` and `writeFormula`: the controls the question is about.
  These are graded on the model after the student's current selection, so a
  different selection is refused with a message saying what to tick
  (`gradeAnswer`), rather than graded on a model the question does not mean.
  `some []` is the model before any update. Optional in the JSON (absent:
  `none`, any selection). -/
  selection : Option (List String) := none
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

/-- Decode a scenario. `hints` and `checks` may be omitted (empty), a
question's `minimal` (`false`) and its `selection` (`none`). -/
def Scenario.ofJson (j : Json) : Except String Scenario := do
  -- no `setObjVal!`: on a non-object it panics and continues with a default
  let obj (ctx : String) (o : Json) := o.getObj?.mapError fun e => s!"{ctx}: {e}"
  let withDefault (ctx : String) (o : Json) (k : String) (d : Json := Json.arr #[]) :
      Except String Json := do
    let m ← obj ctx o
    pure (if m.contains k then o else Json.obj (m.insert k d))
  let m ← obj "scenario" (← withDefault "scenario" j "checks")
  let qs ← (j.getObjValD "questions").getArr?.mapError fun e => s!"scenario.questions: {e}"
  let qs ← qs.mapM fun q => do
    let q ← withDefault "scenario.questions[]" q "hints"
    let q ← withDefault "scenario.questions[]" q "minimal" (Json.bool false)
    withDefault "scenario.questions[]" q "selection" Json.null
  let j := Json.obj (m.insert "questions" (Json.arr qs))
  (fromJson? j : Except String Scenario).mapError fun e => s!"scenario: {e}"

/-- A key `selected` that names no control is an error, not ignored. -/
private def checkKeys (keys selected : List String) : Except String Unit :=
  match selected.find? (!keys.contains ·) with
  | some k => throw s!"unknown control \"{k}\""
  | none => pure ()

/-! ## Atoms

The evaluators read an atom the model does not have as false everywhere, so a
typo, or an action or state name written as an atom, would grade as "true
nowhere". Every formula is checked against the model's atoms first. -/

/-- An error naming each atom of `used` not in `known`. `atl` adds the advice
for actions, which only ATL-D formulas have. -/
private def checkAtoms (atl : Bool) (known used : List String) : Except String Unit :=
  let unknown := (used.filter (!known.contains ·)).eraseDups
  if unknown.isEmpty then pure () else
  let names := ", ".intercalate unknown
  let what := if unknown.length == 1 then s!"{names} is not an atom" else s!"{names} are not atoms"
  let atoms := if known.isEmpty then "none" else ", ".intercalate known
  throw s!"{what} of this model (atoms: {atoms}).\
    {if atl then " For an action, write has(agent,action)." else ""}"

private def epiAtoms (m : EpistemicModel) : List String :=
  (Std.TreeSet.ofList (m.eValuation.toList.map (·.1.name))).toList

/-- Parse an epistemic formula and check its atoms (including inside
announcements) against `known`. -/
private def parseEpi (known : List String) (s : String) : Except String Formula := do
  let f ← parseFormula s
  checkAtoms false known (f.atoms.toList.map (·.name))
  pure f

/-! ## Epistemic mode -/

/-- `known`: the atoms formulas may use (the model's, before and after). -/
private def epiEvaluable (m : EpistemicModel) (known : List String) : Evaluable :=
  let ws := m.eFrame.eWorlds.toList
  { worlds := ws
    edges := m.eFrame.eRelations.toList.flatMap fun (a, r) =>
      ws.flatMap fun w => (r.getD w ∅).toList.map fun w' => (a, w, w')
    facts := ws.map fun w =>
      (w, m.eValuation.toList.filterMap fun (p, s) => if s.contains w then some p.name else none)
    truthSet := fun s => do
      let f ← parseEpi known s
      ws.filterM fun w => eSatisfies m w f
    access := fun a w =>
      match eAccessible m.eFrame a w with
      | .ok s => s.toList
      | .error _ => [] }

private def epiModel (sc : Scenario) : Except String EpistemicModel :=
  (EpistemicJson.decodeModel sc.model).mapError (·.message)

/-- The action model the selection describes. -/
private def epiActionModel (known agents : List String) (c : Json) (selected : List String) :
    Except String ActionModel := do
  let events ← strList "controls.events" (← field c "events" "controls")
  let toggleable ← strList "controls.toggleable" ((c.getObjVal? "toggleable").toOption.getD (.arr #[]))
  let observers ← strList "controls.observers" ((c.getObjVal? "observers").toOption.getD (.arr #[]))
  checkKeys toggleable selected
  let pre ← (← entries c "pre" "controls").mapM fun (e, f) => do
    pure (e, ← (parseEpi known (← str s!"controls.pre.{e}" f)).mapError (s!"controls.pre.{e}: " ++ ·))
  let post ← (← entries c "post" "controls").mapM fun (e, ps) => do
    let o ← ps.getObj?.mapError fun err => s!"controls.post.{e}: {err}"
    let ps ← o.toList.mapM fun (p, f) => do
      pure (p, ← (parseEpi known (← str s!"controls.post.{e}.{p}" f)).mapError
        (s!"controls.post.{e}.{p}: " ++ ·))
    pure (e, ps)
  let rels := agents.map fun a =>
    let observes := if toggleable.contains a then selected.contains a else observers.contains a
    (a, if observes then events.map fun e => (e, e)
        else events.flatMap fun e => events.map fun e' => (e, e'))
  mkActionModel events agents rels pre post

/-! ## ATL-D mode -/

mutual
/-- The atoms of an ATL-D formula, including inside update conditions. -/
private def dAtoms : DFormula → List String
  | .bot | .has .. => []
  | .atom n => [n]
  | .not f | .knows _ f | .canNext _ f | .canAlways _ f | .canEventually _ f => dAtoms f
  | .and l r | .or l r | .implies l r | .iff l r | .canUntil _ l r | .canRelease _ l r =>
    dAtoms l ++ dAtoms r
  | .grant us f | .revoke us f => uAtoms us ++ dAtoms f

private def uAtoms : UpdateList → List String
  | .nil => []
  | .cons c _ _ _ rest => dAtoms c ++ uAtoms rest
end

private def dynAtoms (m : DynModel) : List String :=
  (Std.TreeSet.ofList (m.cgs.cgsStates.toList.flatMap fun v => (m.cgs.cgsLabeling v).toList)).toList

/-- Parse an ATL-D formula and check its atoms against `known`. -/
private def parseDyn (known : List String) (s : String) : Except String DFormula := do
  let f ← parseDFormula s
  checkAtoms true known (dAtoms f)
  pure f

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
      let f ← parseDyn (dynAtoms m) s
      pure (← dsat m mode f).toList
    access := fun a v => (m.epistemic a v).toList
    notes }

/-- The scenario's model, its `IrMode` and its clauses, every clause condition
checked against the model's atoms. -/
private def dynSetup (sc : Scenario) : Except String (DynModel × IrMode × List DClause) := do
  let m ← (CgsJson.decodeDyn sc.model).mapError (·.message)
  let (mode, clauses) ← dControls sc.controls
  for c in clauses do
    (checkAtoms true (dynAtoms m) (dAtoms c.cond)).mapError (s!"clause \"{c.label}\".cond: " ++ ·)
  pure (m, mode, clauses)

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
  | .epistemic => let m ← epiModel sc; pure (epiEvaluable m (epiAtoms m))
  | .atlD =>
    let (m, mode, _) ← dynSetup sc
    pure (dynEvaluable m mode [])

/-- The model after the update that the `selected` controls describe. -/
def Scenario.after (sc : Scenario) (selected : List String) : Except String Evaluable := do
  match sc.mode with
  | .epistemic =>
    let m ← epiModel sc
    let am ← epiActionModel (epiAtoms m) (m.eFrame.eRelations.toList.map (·.1)) sc.controls selected
    let m' ← productUpdate m am
    pure (epiEvaluable m' ((Std.TreeSet.ofList (epiAtoms m ++ epiAtoms m')).toList))
  | .atlD =>
    let (m, mode, clauses) ← dynSetup sc
    checkKeys (clauses.map (·.label)) selected
    let chosen := clauses.filter (selected.contains ·.label)
    let mut m := m
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
