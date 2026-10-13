import Gamen.Protocol
import Gamen.CgsJson
import Gamen.Atl
import Gamen.Atl.ImperfectInfo
import Gamen.Atl.Dynamic

/-!
# Validate.Atl

The Lean-only `atl_model_check` request of `gamen-validate` (protocol 2):
model-check ATL formulas on a concrete concurrent game structure given as JSON.
See `Validate.lean` for the wire format and `Gamen.CgsJson` for the model spec.

gamen-hs has no such request; it is outside `tools/compare`'s scope.
-/
open Lean (Json toJson)
open Gamen Gamen.Protocol Gamen.Atl.Dynamic

/-- Which satisfaction relation `atl_model_check` evaluates. -/
inductive AtlSemantics where
  /-- `Gamen.Atl.sat`: perfect information (AHK 2002). -/
  | perfect
  /-- `Gamen.atlirSat`: ATLir, subjective. -/
  | subjective
  /-- `Gamen.atlirSatObjective`: ATLir, objective. -/
  | objective

def AtlSemantics.name : AtlSemantics → String
  | .perfect => "perfect"
  | .subjective => "imperfect_subjective"
  | .objective => "imperfect_objective"

def AtlSemantics.parse : String → Except String AtlSemantics
  | "perfect" => .ok .perfect
  | "imperfect_subjective" => .ok .subjective
  | "imperfect_objective" => .ok .objective
  | other => .error s!"Unknown semantics: {other} \
      (expected perfect, imperfect_subjective or imperfect_objective)"

/-- The formulas of an `atl_model_check` request: plain ATL/Coalition formulas
(`Gamen.Formula`), or, when the request has `"dynamic": true`, ATL-D formulas. -/
inductive AtlFormulas where
  | static (fs : List Formula)
  | dynamic (fs : List DFormula)

open Lean in
/-- Decode an ATL-D formula (tree format). The `ATL` operators use the same
keys as `decodeFormula`; the additions are

    {"type":"has","agent":"a","action":"x"}
    {"type":"grant" | "revoke",
     "updates":[{"condition":F,"action":"x","agents":["a"]}, ...], "operand":F}
    {"type":"can_release","agents":[...],"left":F,"right":F}

`partial` for the reason `decodeFormula` is: recursion goes through field
lookups on the (finite) JSON value, which Lean cannot see as structural. -/
partial def decodeDFormula (j : Json) : Except String DFormula := do
  let sub (k : String) : Except String DFormula := do decodeDFormula (← field j k)
  let agents := strListField j "agents"
  match ← strField j "type" with
  | "bot" => return .bot
  | "atom" => return .atom (← strField j "name")
  | "not" => return .not (← sub "operand")
  | "and" => return .and (← sub "left") (← sub "right")
  | "or" => return .or (← sub "left") (← sub "right")
  | "implies" => return .implies (← sub "left") (← sub "right")
  | "iff" => return .iff (← sub "left") (← sub "right")
  | "has" => return .has (← strField j "agent") (← strField j "action")
  | "can_next" | "coalition" => return .canNext (← agents) (← sub "operand")
  | "can_always" => return .canAlways (← agents) (← sub "operand")
  | "can_eventually" => return .canEventually (← agents) (← sub "operand")
  | "can_until" => return .canUntil (← agents) (← sub "left") (← sub "right")
  | "can_release" => return .canRelease (← agents) (← sub "left") (← sub "right")
  | "grant" => return .grant (← updates) (← sub "operand")
  | "revoke" => return .revoke (← updates) (← sub "operand")
  | other => throw s!"Unknown formula type: {other}"
where
  updates : Except String UpdateList := do
    let items := (← (← field j "updates").getArr?).toList
    items.foldrM (init := UpdateList.nil) fun u rest => do
      return .cons (← decodeDFormula (← field u "condition")) (← strField u "action")
        (← strListField u "agents") rest

/-- An `atl_model_check` error carries a stable `error_code` beside the message. -/
def atlErr (code msg : String) : Json :=
  Json.mkObj [("ok", false), ("error", toJson msg), ("error_code", toJson code)]

/-- Per-formula result: its satisfying states among `check`, or its error. -/
def atlItem (all check : List String) (i : Nat) (display : String)
    (r : Except String (Std.TreeSet String)) : Json :=
  let base := [("index", toJson i), ("formula", toJson display)]
  match r with
  | .error msg => Json.mkObj (base ++ [("error", toJson msg)])
  | .ok s =>
    Json.mkObj (base ++ [
      ("satisfying", toJson (check.filter s.contains)),
      ("holds", Json.mkObj (check.map fun st => (st, toJson (s.contains st)))),
      ("true_in_model", toJson (all.all s.contains))])

def atlReply (sem : String) (check : List String) (results : List Json) : Json :=
  Json.mkObj [("ok", true), ("result", Json.mkObj [
    ("semantics", toJson sem), ("states", toJson check),
    ("results", Json.arr results.toArray)])]

/-- Answer an `atl_model_check` request. `states = none` checks every state. -/
def atlModelCheck (model : Json) (fs : AtlFormulas) (states : Option (List String))
    (sem : AtlSemantics) : Json :=
  match fs with
  | .static formulas =>
    match CgsJson.decode model with
    | .error e => atlErr e.code e.message
    | .ok d =>
      let all := d.cgs.cgsStates.toList
      let check := states.getD all
      match check.find? (fun st => !d.cgs.cgsStates.contains st) with
      | some st => atlErr "unknown_state" s!"states: unknown state \"{st}\""
      | none =>
        let satSet (f : Formula) : Except String (Std.TreeSet String) :=
          match sem with
          | .perfect => sat d.cgs f
          | .subjective => atlirSat d.atel f
          | .objective => atlirSatObjective d.atel f
        atlReply sem.name check <| formulas.zipIdx.map fun (f, i) =>
          atlItem all check i (toString f) (satSet f)
  | .dynamic formulas =>
    match sem with
    | .perfect =>
      match CgsJson.decodeDyn model with
      | .error e => atlErr e.code e.message
      | .ok m =>
        let all := m.cgs.cgsStates.toList
        let check := states.getD all
        match check.find? (fun st => !m.cgs.cgsStates.contains st) with
        | some st => atlErr "unknown_state" s!"states: unknown state \"{st}\""
        | none =>
          atlReply "perfect_dynamic" check <| formulas.zipIdx.map fun (f, i) =>
            atlItem all check i (toString f) (dsat m f)
    | _ => atlErr "unsupported_semantics" "dynamic formulas support only perfect information"
