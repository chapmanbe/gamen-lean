import Gamen.Protocol
import Gamen.Tableau
import Gamen.Fragment

/-!
# gamen-validate (Lean port)

Port of `gamen-hs/validate/Main.hs`: a JSON Lines service on stdin/stdout.

    {"action": "ping"}
    {"action": "check_consistency", "formulas": [...]}
    {"action": "validate_formula", "formula": {...}}
    {"action": "validate_agent", "formula": {...}, "agent": "clinician"}
    {"action": "check_pairwise", "formulas": [...]}

Responses are `{"ok": true, "result": ...}` or `{"ok": false, "error": "..."}`.

**Slice limitation.** gamen-hs dispatches consistency checks to three
backends: the KDt tableau, its doxastic-D and ranking-theory rules (for
`belief`/`ranked_belief`), and the deontic-STIT prover (for agent
operators). Only the first is ported. Inputs that would reach the other
two get `{"ok": false, "error": "not ported in Lean slice: …"}`, so the
side-by-side comparison can separate scope gaps from disagreements.
Fragment rejections ("unsupported operator …") happen before dispatch
and are fully ported.

There is no `deepseq` crash guard: the Lean code has no `error` calls to
guard against, and evaluation is strict.
-/
open Lean (Json toJson)
open Gamen Gamen.Protocol

inductive Request where
  | ping
  | checkConsistency (formulas : List Formula)
  | validateFormula (raw : Json)
  | validateAgent (raw : Json) (agent : String)
  | checkPairwise (formulas : List Formula)

def parseRequest (j : Json) : Except String Request := do
  let .obj _ := j | throw "expected Object"
  match ← (← field j "action").getStr? with
  | "ping" => return .ping
  | "check_consistency" => return .checkConsistency (← formulas)
  | "validate_formula" => return .validateFormula (← field j "formula")
  | "validate_agent" => return .validateAgent (← field j "formula") (← strField j "agent")
  | "check_pairwise" => return .checkPairwise (← formulas)
  | other => throw s!"Unknown action: {other}"
where
  formulas : Except String (List Formula) := do
    (← (← field j "formulas").getArr?).toList.mapM decodeFormula

/-- Outcome of choosing and running a consistency backend. -/
inductive Classified where
  | unsupported (op prover : String)   -- rejected by the fragment gate
  | verdict (v : Verdict) (prover : String)
  | notPorted (what : String)          -- needs a backend this slice lacks

def tableauMaxSteps : Nat := 5000

/-- Port of `firstUnsupported` in `validate/Main.hs`: the first constructor
across a formula list rejected by a fragment check (`checkTableauFragment`
or `checkDSFragment`), or `none` if all are in fragment. Any reason other
than `unsupportedOperator` should not arise from a fragment check. -/
def firstUnsupported (chk : Formula → Except UnknownReason Unit) (fs : List Formula) :
    Option String :=
  fs.findSome? fun f => match chk f with
    | .ok () => none
    | .error (.unsupportedOperator name) => some name
    | .error _ => none

/-- A fragment-agnostic scan for operators outside this Lean slice's own
scope (not a Haskell concept: gamen-hs's doxastic/ranking tableau rules
are fully implemented, so it never needs this). -/
def firstOutOfScope (ok : Formula → Bool) (fs : List Formula) : Option String :=
  fs.findSome? (·.firstOffender ok)

/-- Port of `classifyConsistency`: any agent operator sends the whole set to
the deontic-STIT prover; otherwise the KDt tableau (plus doxastic and
ranking rules) handles it. Each backend gates its fragment first with
`Gamen.Fragment.checkDSFragment` / `checkTableauFragment`. -/
def classifyConsistency (fs : List Formula) : Classified :=
  if fs.any (·.hasAgentOperator) then
    match firstUnsupported checkDSFragment fs with
    | some op => .unsupported op "deontic-stit"
    | none => .notPorted "deontic-STIT prover (G3DS)"
  else
    match firstUnsupported (checkTableauFragment systemKDt) fs with
    | some op => .unsupported op "kdt+doxasticD"
    | none =>
      match firstOutOfScope (fun f => !(f matches .belief .. | .rankedBelief ..)) fs with
      | some op => .notPorted s!"doxastic/ranking tableau rules ({op})"
      | none => .verdict (tableauConsistent systemKDt tableauMaxSteps fs) "kdt+doxasticD"

def statusPairs : Verdict → List (String × Json)
  | .definitely true => [("status", "consistent"), ("consistent", true)]
  | .definitely false => [("status", "inconsistent"), ("consistent", false)]
  | .unknown r => [("status", "unknown"), ("reason", r.code)]

def okResult (v : Json) : Json := Json.mkObj [("ok", true), ("result", v)]
def errResult (e : String) : Json := Json.mkObj [("ok", false), ("error", e)]

def patientAtoms : List String :=
  ["take_statin", "take_medication", "exercise_regular", "diet_adherent",
   "healthy_weight_maintained", "tobacco_avoided", "followup_attended",
   "statin_taken_daily", "ezetimibe_taken_daily", "injection_administered", "fill_rx"]

def handleRequest : Request → Json
  | .ping => okResult "pong"
  | .checkConsistency fs =>
    match classifyConsistency fs with
    | .unsupported op prover =>
      errResult s!"unsupported operator: {op} (not in the {prover} fragment)"
    | .notPorted what => errResult s!"not ported in Lean slice: {what}"
    | .verdict v prover =>
      okResult (Json.mkObj (statusPairs v ++
        [("formula_count", toJson fs.length), ("prover", toJson prover)]))
  | .validateFormula raw =>
    match decodeFormula raw with
    | .ok f => okResult (Json.mkObj [
        ("valid", true), ("formula", toJson f),
        ("atoms", toJson (f.atoms.toList.map (·.name))), ("display", toString f)])
    | .error msg => okResult (Json.mkObj [("valid", false), ("parse_error", msg)])
  | .validateAgent raw agent =>
    match decodeFormula raw with
    | .ok f =>
      let names := f.atoms.toList.map (·.name)
      let concern := agent == "clinician" && names.any patientAtoms.contains
      okResult (Json.mkObj [
        ("valid", !concern), ("formula", toJson f), ("claimed_agent", agent),
        ("atoms", toJson names),
        ("concern", if concern then
          "Formula contains patient-controlled atoms but is attributed to clinician. \
           Consider 'joint' or 'patient'." else Json.null)])
    | .error msg => okResult (Json.mkObj [("valid", false), ("parse_error", msg)])
  | .checkPairwise fs =>
    let indexed := (List.range fs.length).zip fs
    let pairs := indexed.flatMap fun (i, fi) =>
      indexed.filterMap fun (j, fj) => if i < j then some (i, fi, j, fj) else none
    let classified := pairs.map fun (i, fi, j, fj) => (i, fi, j, fj, classifyConsistency [fi, fj])
    match classified.findSome? (fun | (_, _, _, _, .notPorted w) => some w | _ => none) with
    | some what => errResult s!"not ported in Lean slice: {what}"
    | none =>
      let conflicts := classified.filterMap fun
        | (i, fi, j, fj, .verdict (.definitely false) _) =>
          some (Json.mkObj [("i", toJson i), ("j", toJson j), ("formula_i", toJson fi), ("formula_j", toJson fj)])
        | _ => none
      let indeterminate := classified.filterMap fun
        | (i, _, j, _, .unsupported op _) =>
          some (Json.mkObj [("i", toJson i), ("j", toJson j), ("reason", "unsupported_operator"), ("operator", toJson op)])
        | (i, _, j, _, .verdict (.unknown r) _) =>
          some (Json.mkObj [("i", toJson i), ("j", toJson j), ("reason", toJson r.code)])
        | _ => none
      okResult (Json.mkObj [
        ("total_pairs", toJson pairs.length), ("conflicts", Json.arr conflicts.toArray),
        ("conflict_count", toJson conflicts.length),
        ("indeterminate", Json.arr indeterminate.toArray),
        ("indeterminate_count", toJson indeterminate.length)])

def processLine (line : String) : Json :=
  match Json.parse line with
  | .error e => errResult e
  | .ok j =>
    match parseRequest j with
    | .error e => errResult e
    | .ok req => handleRequest req

/-- Read JSON Lines until EOF; skip empty lines, as `BL.null` does in Haskell. -/
partial def main : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  let rec loop : IO Unit := do
    let line ← stdin.getLine
    if line.isEmpty then return  -- EOF
    let body := if line.endsWith "\n" then line.dropEnd 1 |>.toString else line
    unless body.isEmpty do
      stdout.putStrLn (processLine body).compress
      stdout.flush
    loop
  loop
