import Gamen.Atel
import Gamen.Atl.Dynamic
import Lean.Data.Json
import Std.Data.HashMap

/-!
# Gamen.CgsJson

A JSON codec for `Gamen.Cgs` models, so a concurrent game structure given as
data (rather than built from Lean code) can be loaded by any caller. Lean-only:
gamen-hs has no counterpart. Used by the `atl_model_check` request of
`gamen-validate` (`Validate/Atl.lean`), but independent of the wire protocol.

States, agents and actions are all `String`s (`Cgs String String`).

## Spec format

    { "states": ["s0", "s1"],
      "agents": ["a", "b"],
      "moves": { "s0": { "a": ["x", "y"], "b": ["z"] }, ... },
      "transitions": [ { "state": "s0", "moves": { "a": "x", "b": "z" }, "next": "s1" }, ... ],
      "valuation": { "s0": ["p"], ... },                       -- optional; absent state = no atoms
      "indistinguishable": { "a": [["s0", "s1"], ["s2"]] } }   -- optional, imperfect information

`transitions` must be a *complete* joint-move table: exactly one entry for every
joint move (one action per agent, each available at `state`) at every state.
Optional, for ATL-D updates (`Gamen.Atl.Dynamic`): `"actions": [...]` declares
the whole action universe (so `transitions` may mention actions no agent has yet),
and `"default_next": {"stay": true}` or `{"state": "s"}` gives the successor of
every joint move the table does not list (then the table need not be complete).
Without `default_next`, an update that enables an unlisted joint move is an error.

`indistinguishable` gives, per agent, the classes of the epistemic relation; a
state in no class of an agent is alone in its class, and an agent not mentioned
cannot distinguish nothing (all its classes are singletons).

Every failure is a `CgsSpecError`: a stable machine-readable `code` plus a
message. Bad data is never a crash and never a default.
-/
namespace Gamen

open Lean (Json)

/-- A spec failure: `code` is stable and machine-readable, `message` is for people. -/
structure CgsSpecError where
  code : String
  message : String
  deriving Repr

namespace CgsJson

private def err {α : Type} (code msg : String) : Except CgsSpecError α :=
  .error ⟨code, msg⟩

/-- Lift a `Json` accessor's `String` error into a `malformed_spec` error. -/
private def lift {α : Type} (ctx : String) (r : Except String α) : Except CgsSpecError α :=
  r.mapError fun e => ⟨"malformed_spec", s!"{ctx}: {e}"⟩

private def getField (o : Json) (k ctx : String) : Except CgsSpecError Json :=
  match o.getObjVal? k with
  | .ok v => .ok v
  | .error _ => err "malformed_spec" s!"{ctx}: key \"{k}\" not found"

private def strList (ctx : String) (j : Json) : Except CgsSpecError (List String) := do
  let arr ← lift ctx j.getArr?
  arr.toList.mapM fun x => lift ctx x.getStr?

private def objEntries (ctx : String) (j : Json) : Except CgsSpecError (List (String × Json)) := do
  let o ← lift ctx j.getObj?
  return o.toList

private def noDuplicates (code what : String) (xs : List String) : Except CgsSpecError Unit :=
  match xs.find? (fun x => xs.count x > 1) with
  | some x => err code s!"duplicate {what} \"{x}\""
  | none => pure ()

/-- A decoded spec: the CGS, and (when given) each agent's epistemic classes
as an `AtelModel`. -/
structure Decoded where
  cgs : Cgs String String
  /-- The imperfect-information model; all-singleton classes when the spec has
  no `indistinguishable` field. -/
  atel : AtelModel String String

private abbrev JointKey := String × List (String × String)

/-- Decode the CGS part of a spec (everything but `indistinguishable`), with
the data ATL-D updates need: the action universe and which joint moves have a
stated successor. See the module docstring for `actions` and `default_next`. -/
def decodeDynBase (j : Json) : Except CgsSpecError Atl.Dynamic.DynModel := do
  let _ ← lift "model" j.getObj?
  let statesL ← strList "states" (← getField j "states" "model")
  let agentsL ← strList "agents" (← getField j "agents" "model")
  noDuplicates "duplicate_state" "state" statesL
  noDuplicates "duplicate_agent" "agent" agentsL
  let states : Std.TreeSet String := Std.TreeSet.ofList statesL
  let agents : Std.TreeSet String := Std.TreeSet.ofList agentsL
  let knownState (ctx st : String) : Except CgsSpecError Unit :=
    if states.contains st then pure () else err "unknown_state" s!"{ctx}: unknown state \"{st}\""
  let knownAgent (ctx ag : String) : Except CgsSpecError Unit :=
    if agents.contains ag then pure () else err "unknown_agent" s!"{ctx}: unknown agent \"{ag}\""
  -- moves : state → agent → actions
  let movesJ ← getField j "moves" "model"
  let mut movesTbl : Std.HashMap (String × String) (Std.TreeSet String) := {}
  for (st, perAgent) in ← objEntries "moves" movesJ do
    knownState "moves" st
    for (ag, acts) in ← objEntries s!"moves[{st}]" perAgent do
      knownAgent s!"moves[{st}]" ag
      let actL ← strList s!"moves[{st}][{ag}]" acts
      if actL.isEmpty then
        throw ⟨"empty_moves", s!"agent \"{ag}\" has no moves at state \"{st}\""⟩
      movesTbl := movesTbl.insert (st, ag) (Std.TreeSet.ofList actL)
  for st in statesL do
    for ag in agentsL do
      unless movesTbl.contains (st, ag) do
        throw ⟨"missing_moves", s!"no moves given for agent \"{ag}\" at state \"{st}\""⟩
  let moves : String → String → Std.TreeSet String := fun st ag =>
    (movesTbl.get? (st, ag)).getD ∅
  -- action universe: declared by `actions`, else the actions in use
  let used : Std.TreeSet String := movesTbl.fold (fun acc _ v => acc ∪ v) ∅
  let declared := (j.getObjVal? "actions").toOption.filter (· != Json.null)
  let actionSet : Std.TreeSet String ← match declared with
    | none => pure used
    | some v => do
      let u := Std.TreeSet.ofList (← strList "actions" v)
      match used.toList.find? (!u.contains ·) with
      | some α => throw ⟨"unknown_action", s!"actions: \"{α}\" is available in moves but not declared"⟩
      | none => pure u
  -- successor of a joint move no transition mentions
  let dfltJ := (j.getObjVal? "default_next").toOption.filter (· != Json.null)
  let dflt : Option (Option String) ← match dfltJ with
    | none => pure none
    | some d => do
      if (d.getObjVal? "stay").toOption == some (Json.bool true) then pure (some none)
      else
        let st ← lift "default_next" (← getField d "state" "default_next").getStr?
        knownState "default_next" st
        pure (some (some st))
  -- transitions : complete joint-move table
  let transJ ← getField j "transitions" "model"
  let mut transTbl : Std.HashMap JointKey String := {}
  for (t, i) in (← lift "transitions" transJ.getArr?).toList.zipIdx do
    let ctx := s!"transitions[{i}]"
    let st ← lift ctx (← getField t "state" ctx).getStr?
    knownState ctx st
    let next ← lift ctx (← getField t "next" ctx).getStr?
    knownState ctx next
    let mv ← objEntries ctx (← getField t "moves" ctx)
    let mvTree ← mv.foldlM (init := (∅ : Std.TreeMap String String)) fun acc (ag, a) => do
      knownAgent ctx ag
      let act ← lift ctx a.getStr?
      if declared.isSome then
        unless actionSet.contains act do
          throw ⟨"unknown_action", s!"{ctx}: action \"{act}\" is not in actions"⟩
      else
        unless (moves st ag).contains act do
          throw ⟨"unknown_move", s!"{ctx}: action \"{act}\" is not available to agent \"{ag}\" at state \"{st}\""⟩
      pure (acc.insert ag act)
    for ag in agentsL do
      unless mvTree.contains ag do
        throw ⟨"incomplete_joint_move", s!"{ctx}: no action given for agent \"{ag}\""⟩
    let key : JointKey := (st, mvTree.toList)
    if transTbl.contains key then
      throw ⟨"duplicate_transition", s!"{ctx}: a transition for this joint move at state \"{st}\" is already given"⟩
    transTbl := transTbl.insert key next
  let trans : String → Std.TreeMap String String → String := fun st jm =>
    (transTbl.get? (st, jm.toList)).getD (match dflt with | some (some d) => d | _ => st)
  -- valuation
  let mut valTbl : Std.HashMap String (Std.TreeSet String) := {}
  if let some v := (j.getObjVal? "valuation").toOption then
    unless v == Json.null do
      for (st, atoms) in ← objEntries "valuation" v do
        knownState "valuation" st
        valTbl := valTbl.insert st (Std.TreeSet.ofList (← strList s!"valuation[{st}]" atoms))
  let label : String → Std.TreeSet String := fun st => (valTbl.get? st).getD ∅
  -- the joint-move table must cover every joint move at every state
  let provisional : Cgs String String :=
    { cgsStates := states, cgsAgents := agents, cgsMoves := moves,
      cgsTransition := trans, cgsLabeling := label }
  if dflt.isNone then
   for st in statesL do
    for jm in jointMoves provisional agents st do
      unless transTbl.contains (st, jm.toList) do
        let shown := ", ".intercalate (jm.toList.map fun (ag, a) => s!"{ag}={a}")
        throw ⟨"missing_transition", s!"no transition for joint move ({shown}) at state \"{st}\""⟩
  match mkCgs states agents moves trans label with
  | .ok cgs =>
    pure { cgs, actions := actionSet,
           specified := fun v jm => dflt.isSome || transTbl.contains (v, jm.toList),
           epistemic := fun _ st => Std.TreeSet.ofList [st] }
  | .error msg => err "invalid_cgs" msg

/-- Decode the CGS part of a spec. -/
def decodeCgs (j : Json) : Except CgsSpecError (Cgs String String) :=
  (·.cgs) <$> decodeDynBase j

/-- Decode the optional `indistinguishable` field into an epistemic relation
over `cgs`'s states: agent → state → class. -/
def decodeEpistemic (cgs : Cgs String String) (j : Json) :
    Except CgsSpecError (String → String → Std.TreeSet String) := do
  let mut tbl : Std.HashMap (String × String) (Std.TreeSet String) := {}
  match (j.getObjVal? "indistinguishable").toOption with
  | none => pure ()
  | some .null => pure ()
  | some v =>
    for (ag, classes) in ← objEntries "indistinguishable" v do
      unless cgs.cgsAgents.contains ag do
        throw ⟨"unknown_agent", s!"indistinguishable: unknown agent \"{ag}\""⟩
      for cls in (← lift s!"indistinguishable[{ag}]" classes.getArr?).toList do
        let members ← strList s!"indistinguishable[{ag}]" cls
        for st in members do
          unless cgs.cgsStates.contains st do
            throw ⟨"unknown_state", s!"indistinguishable[{ag}]: unknown state \"{st}\""⟩
          if tbl.contains (ag, st) then
            throw ⟨"overlapping_classes", s!"indistinguishable[{ag}]: state \"{st}\" is in more than one class"⟩
        let clsSet := Std.TreeSet.ofList members
        for st in members do
          tbl := tbl.insert (ag, st) clsSet
  pure fun ag st => (tbl.get? (ag, st)).getD (Std.TreeSet.ofList [st])

/-- Decode a spec for ATL-D/ATEL-D: the dynamic model with its `indistinguishable`
relation (singletons when absent). -/
def decodeDyn (j : Json) : Except CgsSpecError Atl.Dynamic.DynModel := do
  let base ← decodeDynBase j
  let epi ← decodeEpistemic base.cgs j
  match mkAtelModel base.cgs epi with
  | .ok _ => pure { base with epistemic := epi }
  | .error msg => err "invalid_indistinguishability" msg

/-- Decode a whole spec: the CGS and its imperfect-information model. -/
def decode (j : Json) : Except CgsSpecError Decoded := do
  let cgs ← decodeCgs j
  let epi ← decodeEpistemic cgs j
  match mkAtelModel cgs epi with
  | .ok atel => pure { cgs, atel }
  | .error msg => err "invalid_indistinguishability" msg

end CgsJson
end Gamen
