import Gamen.Protocol
import Gamen.CgsJson
import Gamen.Atl
import Gamen.Atl.ImperfectInfo

/-!
# Validate.Atl

The Lean-only `atl_model_check` request of `gamen-validate` (protocol 2):
model-check ATL formulas on a concrete concurrent game structure given as JSON.
See `Validate.lean` for the wire format and `Gamen.CgsJson` for the model spec.

gamen-hs has no such request; it is outside `tools/compare`'s scope.
-/
open Lean (Json toJson)
open Gamen Gamen.Protocol

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

/-- An `atl_model_check` error carries a stable `error_code` beside the message. -/
def atlErr (code msg : String) : Json :=
  Json.mkObj [("ok", false), ("error", toJson msg), ("error_code", toJson code)]

/-- Answer an `atl_model_check` request. `states = none` checks every state. -/
def atlModelCheck (model : Json) (formulas : List Formula) (states : Option (List String))
    (sem : AtlSemantics) : Json :=
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
      let results := formulas.zipIdx.map fun (f, i) =>
        let base := [("index", toJson i), ("formula", toString f |> toJson)]
        match satSet f with
        | .error msg => Json.mkObj (base ++ [("error", toJson msg)])
        | .ok s =>
          let holds := check.map fun st => (st, toJson (s.contains st))
          Json.mkObj (base ++ [
            ("satisfying", toJson (check.filter s.contains)),
            ("holds", Json.mkObj holds),
            ("true_in_model", toJson (s == d.cgs.cgsStates))])
      Json.mkObj [("ok", true), ("result", Json.mkObj [
        ("semantics", toJson sem.name), ("states", toJson check),
        ("results", Json.arr results.toArray)])]
