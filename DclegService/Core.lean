import Gamen.Service.Protocol
import Gamen.Service.Formula
import Gamen.Service.Model
import Gamen.Service.Axioms

/-!
# DclegService.Core

The non-`IO` part of `dcleg-service` (`gamen-hs/service/Main.hs`): the
handle registry, the dispatcher and the operation handlers. The main loop
(`DclegService.lean`) keeps a `ServiceState` in an `IO.Ref` and feeds it one
line at a time; `runSession` does the same purely, for the tests.

Operations, as in gamen-hs v0.1: `ping`, `build`, `sat`, `true_in`,
`counterfactual`, `axiom_check`, `drop`, `list`. The protocol note
(`notes/dcleg-service-protocol.md` in gamen-hs) also describes
`enumerate_counterfactuals` and `info`; gamen-hs never implemented them, and
both answer `unknown_op` here too.

**Lean-only `version` op (dcleg protocol 1).** Answers
`{"commit": …, "implementation": "gamen-lean", "protocol": 1}`, so a caller
can tell which binary answered; gamen-hs answers `unknown_op`. `ping` is
unchanged, and does not list `version` among its capabilities, so that
existing requests stay byte-identical.

**Errors.** Where gamen-hs's evaluator calls `error` (a `B_i` for an agent
with no doxastic map, in a formula or in the Self-Awareness and Intentional
Awareness checks), the Haskell process dies with no reply, ending the
session. Here the request gets an `internal_error` reply (§6's code for a
server-side failure) carrying the library's message, and the service goes
on. Recorded in `tools/compare/intentional-divergences.md`.
-/

namespace DclegService
open Lean (Json toJson)
open Gamen Gamen.Service

/-- The protocol version the Lean-only `version` op reports. Protocol 1 is
gamen-hs's v0.1 operations, byte-compatible except for the listed
divergences, plus `version`. Bump it when a Lean-only extension changes what
a caller can send or receive. -/
def dclegProtocolVersion : Nat := 1

/-- The registry (Haskell `IORef (Map Handle DclegModel)`) and the counter
behind generated handles (`h-0`, `h-1`, …). -/
structure ServiceState where
  registry : Std.TreeMap String DclegModel := ∅
  counter : Nat := 0

/-- `missing_field` error naming the field. -/
def missingField (rid field : String) : Json :=
  mkErr rid "missing_field" s!"Required field missing: {field}"
    (some (Json.mkObj [("field", Json.str field)]))

/-- A library error during evaluation (gamen-hs crashes here; see the
module docstring). -/
def internalError (rid msg : String) : Json :=
  mkErr rid "internal_error" msg none

/-- Require `handle`, look it up, run the continuation. -/
def withHandle (st : ServiceState) (rid : String) (o : Json) (f : DclegModel → Json) : Json :=
  match maybeField o "handle" parseString with
  | none => missingField rid "handle"
  | some h =>
    match st.registry.get? h with
    | none => mkErr rid "handle_unknown" s!"Unknown handle: {h}" none
    | some m => f m

def handlePing (rid : String) : Json :=
  mkOk rid (Json.mkObj [
    ("service", "dcleg-service"), ("version", "0.1.0"),
    ("capabilities", toJson ["build", "sat", "true_in", "counterfactual", "axiom_check",
      "drop", "list"])])

def handleVersion (commit rid : String) : Json :=
  mkOk rid (Json.mkObj [("implementation", "gamen-lean"), ("commit", Json.str commit),
    ("protocol", toJson dclegProtocolVersion)])

def handleBuild (st : ServiceState) (rid : String) (o : Json) : ServiceState × Json :=
  let strict := (maybeField o "strict" parseBool).getD false
  match maybeField o "model" pure with
  | none => (st, missingField rid "model")
  | some modelV =>
    match parseAndBuildModel modelV strict with
    | .error (.buildUnsupported feature details) =>
      (st, mkErr rid "unsupported" s!"Unsupported feature: {feature}" (some details))
    | .error (.buildInvalid violations) =>
      (st, mkErr rid "model_invalid" "Model validation failed"
        (some (Json.mkObj [("violations", toJson violations)])))
    | .ok m =>
      -- As in Haskell, a generated handle uses up a counter value even when
      -- it turns out to be in use.
      let (h, st) := match maybeField o "handle" parseString with
        | some h => (h, st)
        | none => (s!"h-{st.counter}", { st with counter := st.counter + 1 })
      if st.registry.contains h then
        (st, mkErr rid "handle_in_use" s!"Handle already in use: {h}" none)
      else
        ({ st with registry := st.registry.insert h m },
          mkOk rid (Json.mkObj [("handle", Json.str h), ("warnings", Json.arr #[])]))

/-- `formula_invalid` for a decode failure, with an optional message prefix. -/
def decodeOr (rid : String) (prefix_ : String) (v : Json) (k : DclegFormula → Json) : Json :=
  match decodeDclegFormula v with
  | .error msg => mkErr rid "formula_invalid" (prefix_ ++ msg) none
  | .ok phi => k phi

def vertexNotInWorld (rid vertex gamma : String) : Json :=
  mkErr rid "vertex_not_in_world" s!"Vertex {vertex} not reached in world {gamma}" none

def handleSat (st : ServiceState) (rid : String) (o : Json) : Json :=
  withHandle st rid o fun m =>
    match maybeField o "world" parseString, maybeField o "vertex" parseString,
        maybeField o "formula" pure with
    | none, _, _ => missingField rid "world"
    | _, none, _ => missingField rid "vertex"
    | _, _, none => missingField rid "formula"
    | some gamma, some vertex, some fv =>
      decodeOr rid "" fv fun phi =>
        if !(worldVertices m gamma).contains vertex then vertexNotInWorld rid vertex gamma
        else match dclegSatisfies m gamma vertex phi with
          | .ok b => mkOk rid (Json.mkObj [("satisfied", toJson b)])
          | .error e => internalError rid e

def handleTrueIn (st : ServiceState) (rid : String) (o : Json) : Json :=
  withHandle st rid o fun m =>
    match maybeField o "formula" pure with
    | none => missingField rid "formula"
    | some fv =>
      decodeOr rid "" fv fun phi =>
        match dclegTrueIn m phi with
        | .ok b => mkOk rid (Json.mkObj [("true_in_model", toJson b)])
        | .error e => internalError rid e

/-- φ □→ ψ at (γ,w), optionally with the witness worlds:
witnesses = max^φ_{F(γ,w)}(Γ); vacuous = no witnesses; satisfied = ψ holds
at w in every witness world. -/
def handleCounterfactual (st : ServiceState) (rid : String) (o : Json) : Json :=
  withHandle st rid o fun m =>
    let retWit := (maybeField o "return_witnesses" parseBool).getD false
    match maybeField o "world" parseString, maybeField o "vertex" parseString,
        maybeField o "antecedent" pure, maybeField o "consequent" pure with
    | none, _, _, _ => missingField rid "world"
    | _, none, _, _ => missingField rid "vertex"
    | _, _, none, _ => missingField rid "antecedent"
    | _, _, _, none => missingField rid "consequent"
    | some gamma, some vertex, some antV, some consV =>
      decodeOr rid "antecedent: " antV fun phi =>
      decodeOr rid "consequent: " consV fun psi =>
        if !(worldVertices m gamma).contains vertex then vertexNotInWorld rid vertex gamma
        else
          let r : Except String Json := do
            let witnesses ← maxPhiConsistent m gamma vertex phi
            let satisfied ← witnesses.allM fun beta => dclegSatisfies m beta vertex psi
            return Json.mkObj ([("satisfied", toJson satisfied),
                ("vacuous", toJson witnesses.isEmpty)] ++
              if retWit then [("witnesses", toJson witnesses)] else [])
          match r with
          | .ok v => mkOk rid v
          | .error e => internalError rid e

/-- Check the requested belief-revision axioms (all by default), capping
each violation list at `max_violations` (default 10). Unknown axiom names
are rejected outright (gamen-hs#18 task 18). -/
def handleAxiomCheck (st : ServiceState) (rid : String) (o : Json) : Json :=
  withHandle st rid o fun m =>
    let requested := (maybeField o "axioms" (parseList parseText)).getD allAxiomNames
    let maxV := (maybeField o "max_violations" parseInt).getD 10
    let unknown := requested.filter (!allAxiomNames.contains ·)
    if !unknown.isEmpty then
      mkErr rid "unknown_axiom" s!"Unknown axiom(s): {", ".intercalate unknown}"
        (some (Json.mkObj [("unknown", toJson unknown), ("known", toJson allAxiomNames)]))
    else
      -- Haskell's `Map.fromList`: one entry per name, in key order.
      let names := (Std.TreeSet.ofList requested : Std.TreeSet String).toList
      match names.mapM (fun ax => do return (ax, ← checkAxiom ax maxV m)) with
      | .ok kvs => mkOk rid (Json.mkObj kvs)
      | .error e => internalError rid e

def handleDrop (st : ServiceState) (rid : String) (o : Json) : ServiceState × Json :=
  match maybeField o "handle" parseString with
  | none => (st, missingField rid "handle")
  | some h =>
    let dropped := st.registry.contains h
    ({ st with registry := st.registry.erase h },
      mkOk rid (Json.mkObj [("dropped", toJson dropped)]))

def handleList (st : ServiceState) (rid : String) : Json :=
  mkOk rid (Json.mkObj [("handles",
    Json.arr (st.registry.toList.map fun (h, m) => modelSummary h m).toArray)])

/-- Dispatch one parsed request. `commit` is used only by `version`. -/
def dispatch (commit : String) (st : ServiceState) (req : Request) : ServiceState × Json :=
  let rid := req.reqId
  let o := req.reqRaw
  match req.reqOp with
  | "ping" => (st, handlePing rid)
  | "version" => (st, handleVersion commit rid)
  | "build" => handleBuild st rid o
  | "sat" => (st, handleSat st rid o)
  | "true_in" => (st, handleTrueIn st rid o)
  | "counterfactual" => (st, handleCounterfactual st rid o)
  | "axiom_check" => (st, handleAxiomCheck st rid o)
  | "drop" => handleDrop st rid o
  | "list" => (st, handleList st rid)
  | op => (st, mkErr rid "unknown_op" s!"Unknown operation: {op}" none)

/-- One input line (without its newline): `none` for an empty line, which
gets no reply (Haskell's `BL.null` check), else the reply. -/
def processLine (commit : String) (st : ServiceState) (line : String) :
    ServiceState × Option Json :=
  if line.isEmpty then (st, none) else
  match Json.parse line with
  | .error e => (st, some (mkParseError e))
  | .ok j =>
    match parseRequest j with
    | .error e => (st, some (mkParseError e))
    | .ok req =>
      let (st, out) := dispatch commit st req
      (st, some out)

/-- Run a whole session from a fresh registry; the encoded reply lines, as
the binary prints them. -/
def runSession (lines : List String) (commit : String := "unknown") : List String :=
  let step := fun (acc : ServiceState × Array String) line =>
    let (st, out) := processLine commit acc.1 line
    (st, match out with
      | some j => acc.2.push (encode j)
      | none => acc.2)
  (lines.foldl step ({}, #[])).2.toList

end DclegService
