import Gamen.Protocol
import Gamen.Tableau
import Gamen.Temporal
import Gamen.Fragment
import Gamen.Doxastic
import Gamen.RankingTheory
import Gamen.DeonticStit.Prove
import Validate.Atl

/-!
# Validate.Core

The non-`IO` core of `gamen-validate` (`gamen-hs/validate/Main.hs`),
factored out of `Validate.lean` so it can be `import`ed from `Tests.Main`
without the two executables' `main` declarations colliding. See
`Validate.lean` for the wire-protocol documentation.
-/
open Lean (Json toJson)
open Gamen Gamen.Protocol

inductive Request where
  | ping
  | version
  | checkConsistency (formulas : List Formula)
  | validateFormula (raw : Json)
  | validateAgent (raw : Json) (agent : String)
  | checkPairwise (formulas : List Formula)
  | atlModelCheck (model : Json) (formulas : List Formula) (states : Option (List String))
      (sem : AtlSemantics)

def parseRequest (j : Json) : Except String Request := do
  let .obj _ := j | throw "expected Object"
  match ← (← field j "action").getStr? with
  | "ping" => return .ping
  | "version" => return .version
  | "check_consistency" => return .checkConsistency (← formulas)
  | "validate_formula" => return .validateFormula (← field j "formula")
  | "validate_agent" => return .validateAgent (← field j "formula") (← strField j "agent")
  | "check_pairwise" => return .checkPairwise (← formulas)
  | "atl_model_check" =>
    let states ← match ← optField j "states" with
      | none => pure none
      | some v => pure (some (← (← v.getArr?).toList.mapM (·.getStr?)))
    let sem ← match ← optStr j "semantics" with
      | none => pure AtlSemantics.perfect
      | some s => AtlSemantics.parse s
    return .atlModelCheck (← field j "model") (← formulas) states sem
  | other => throw s!"Unknown action: {other}"
where
  formulas : Except String (List Formula) := do
    (← (← field j "formulas").getArr?).toList.mapM decodeFormula

/-- Outcome of choosing and running a consistency backend. -/
inductive Classified where
  | unsupported (op prover : String)   -- rejected by the fragment gate
  | verdict (v : Verdict) (prover : String)
  | proverError (msg : String)         -- the prover returned `Except.error`

def tableauMaxSteps : Nat := 5000

/-- DS^k_n parameters (`validate/Main.hs` `dsK`, `dsMaxSteps`). k = 0 means
unlimited choice. -/
def dsK : Int := 0
def dsMaxSteps : Nat := 5000

/-- Haskell-`show`-style quoting for a `String`, sufficient for
`ProverStuck`'s diagnostic messages (plain ASCII text without control
characters in practice, as gamen-hs's own `ProverStuck` call sites use).
Escapes backslash and double-quote as GHC's derived `Show String` does;
does not attempt GHC's full escape table (named escapes for control
characters, decimal escapes for non-ASCII such as `¬` → `\172`, the `\&` disambiguator after a numeric escape), since a
`ProverStuck`/`BudgetExhausted`/`UncertifiedRefutation` reason reaching `reasonOperator` is
already a "should not occur" case (see its docstring). -/
def quoteHaskellString (s : String) : String :=
  "\"" ++ String.ofList (s.toList.flatMap fun c =>
    if c == '\\' then ['\\', '\\']
    else if c == '"' then ['\\', '"']
    else [c]) ++ "\""

/-- Port of `reasonOperator` (`validate/Main.hs`): the operator name an
`UnsupportedOperator` carried, or Haskell's derived `Show UnknownReason`
rendering of any other reason. The Haskell comment on this function says
"any other reason should not arise from a fragment check" — `firstUnsupported`
still has to render *something* for it rather than silently treat it as
in-fragment (gamen-hs `Left reason -> Just (reasonOperator reason)` covers
every `Left`, not just `UnsupportedOperator`). -/
def reasonOperator : UnknownReason → String
  | .unsupportedOperator name => name
  | .budgetExhausted n => s!"BudgetExhausted {n}"
  | .proverStuck s => s!"ProverStuck {quoteHaskellString s}"
  | .uncertifiedRefutation s => s!"UncertifiedRefutation {quoteHaskellString s}"

/-- Port of `firstUnsupported` in `validate/Main.hs`: the first constructor
across a formula list rejected by a fragment check (`checkTableauFragment`
or `checkDSFragment`), rendered by `reasonOperator`, or `none` if all are
in fragment. -/
def firstUnsupported (chk : Formula → Except UnknownReason Unit) (fs : List Formula) :
    Option String :=
  fs.findSome? fun f => match chk f with
    | .ok () => none
    | .error reason => some (reasonOperator reason)

/-- Port of `consistencySystem` (`validate/Main.hs`): KDt plus the doxastic
D rule and the two ranking-theory closure rules (`rankingRules`). The name
is gamen-hs's, in case it reaches any error text. -/
def consistencySystem : System :=
  { systemKDt with
    name := "KDt+doxasticD+rankingOCF"
    usedPrefixRules := systemKDt.usedPrefixRules ++ doxasticRules ++ rankingRules }

/-- Port of `classifyConsistency`: any agent operator sends the whole set to
the deontic-STIT prover; otherwise the KDt tableau (plus doxastic and
ranking rules) handles it. Each backend gates its fragment first with
`Gamen.Fragment.checkDSFragment` / `checkTableauFragment`.

`proverError` has no gamen-hs counterpart. The Lean G3DS prover returns
`Except` only because `ancestors` takes fuel (see
`Gamen.DeonticStit.Saturation`); that fuel can run out only on a cyclic
generation tree, and `Prove` parents only fresh labels, so the branch is
unreachable. It is reported as an error, never as a verdict. -/
def classifyConsistency (fs : List Formula) : Classified :=
  if fs.any (·.hasAgentOperator) then
    match firstUnsupported checkDSFragment fs with
    | some op => .unsupported op "deontic-stit"
    | none =>
      match isFormulaSetConsistent dsK dsMaxSteps fs with
      | .ok v => .verdict v "deontic-stit"
      | .error msg => .proverError msg
  else
    match firstUnsupported (checkTableauFragment systemKDt) fs with
    | some op => .unsupported op "kdt+doxasticD"
    | none => .verdict (tableauConsistent consistencySystem tableauMaxSteps fs) "kdt+doxasticD"

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

/-- The Lean-only `version` reply: `implementation` tells callers which
binary answered (gamen-hs has no `version` action; it answers
`{"error":"Error in $: Unknown action: version","ok":false}`), `commit` which build, `protocol` which
protocol. -/
def versionResult (commit : String) : Json :=
  okResult (Json.mkObj [("implementation", "gamen-lean"), ("commit", toJson commit),
    ("protocol", toJson protocolVersion)])

/-- Answer one request. `commit` is the build's git commit, used only by
`version`. -/
def handleRequest (commit : String) : Request → Json
  | .ping => okResult "pong"
  | .version => versionResult commit
  | .checkConsistency fs =>
    match classifyConsistency fs with
    | .unsupported op prover =>
      errResult s!"unsupported operator: {op} (not in the {prover} fragment)"
    | .proverError msg => errResult s!"prover error: {msg}"
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
  | .atlModelCheck model fs states sem => atlModelCheck model fs states sem
  | .checkPairwise fs =>
    let indexed := (List.range fs.length).zip fs
    let pairs := indexed.flatMap fun (i, fi) =>
      indexed.filterMap fun (j, fj) => if i < j then some (i, fi, j, fj) else none
    let classified := pairs.map fun (i, fi, j, fj) => (i, fi, j, fj, classifyConsistency [fi, fj])
    match classified.findSome? (fun | (_, _, _, _, .proverError m) => some m | _ => none) with
    | some msg => errResult s!"prover error: {msg}"
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

def processLine (line : String) (commit : String := "unknown") : Json :=
  match Json.parse line with
  | .error e => errResult e
  | .ok j =>
    match parseRequest j with
    | .error e => errResult e
    | .ok req => handleRequest commit req
