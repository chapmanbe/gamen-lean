import Gamen.Protocol
import Gamen.CgsJson
import Gamen.Atl
import Gamen.Atl.ImperfectInfo
import Gamen.Atl.Dynamic
import Gamen.Atl.UpdateSearch

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

def AtlSemantics.mode : AtlSemantics → IrMode
  | .perfect => .perfect
  | .subjective => .subjective
  | .objective => .objective

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
    {"type":"knowledge","agent":"a","operand":F}
    {"type":"grant" | "revoke",
     "updates":[{"condition":F,"action":"x","agents":["a"],"informed":["b"]}, ...],
     "operand":F}                       -- "informed" is optional (ATEL-D)
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
  | "knowledge" => return .knows (← strField j "agent") (← sub "operand")
  | "can_next" | "coalition" => return .canNext (← agents) (← sub "operand")
  | "can_always" => return .canAlways (← agents) (← sub "operand")
  | "can_eventually" => return .canEventually (← agents) (← sub "operand")
  | "can_until" => return .canUntil (← agents) (← sub "left") (← sub "right")
  | "can_release" => return .canRelease (← agents) (← sub "left") (← sub "right")
  | "grant" => return .grant (← updates) (← sub "operand")
  | "revoke" => return .revoke (← updates) (← sub "operand")
  | other => throw s!"Unknown formula type: {other}"
where
  informed (u : Json) : Except String (List String) := do
    match ← optField u "informed" with
    | none => pure []
    | some v => (← v.getArr?).toList.mapM (·.getStr?)
  updates : Except String UpdateList := do
    let items := (← (← field j "updates").getArr?).toList
    items.foldrM (init := UpdateList.nil) fun u rest => do
      return .cons (← decodeDFormula (← field u "condition")) (← strField u "action")
        (← strListField u "agents")
        (← informed u) rest

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
    match CgsJson.decodeDyn model with
    | .error e => atlErr e.code e.message
    | .ok m =>
      let all := m.cgs.cgsStates.toList
      let check := states.getD all
      match check.find? (fun st => !m.cgs.cgsStates.contains st) with
      | some st => atlErr "unknown_state" s!"states: unknown state \"{st}\""
      | none =>
        atlReply (sem.name ++ "_dynamic") check <| formulas.zipIdx.map fun (f, i) =>
          atlItem all check i (toString f) (dsat m sem.mode f)

-- ── atl_update_search (bounded update existence) ─────────────────────────

mutual
/-- The inverse of `decodeDFormula`. -/
def encodeDFormula : DFormula → Json
  | .bot => Json.mkObj [("type", "bot")]
  | .atom n => Json.mkObj [("type", "atom"), ("name", toJson n)]
  | .not f => Json.mkObj [("type", "not"), ("operand", encodeDFormula f)]
  | .and l r => Json.mkObj [("type", "and"), ("left", encodeDFormula l), ("right", encodeDFormula r)]
  | .or l r => Json.mkObj [("type", "or"), ("left", encodeDFormula l), ("right", encodeDFormula r)]
  | .implies l r =>
      Json.mkObj [("type", "implies"), ("left", encodeDFormula l), ("right", encodeDFormula r)]
  | .iff l r => Json.mkObj [("type", "iff"), ("left", encodeDFormula l), ("right", encodeDFormula r)]
  | .has a x => Json.mkObj [("type", "has"), ("agent", toJson a), ("action", toJson x)]
  | .knows a f => Json.mkObj [("type", "knowledge"), ("agent", toJson a), ("operand", encodeDFormula f)]
  | .canNext as f => Json.mkObj [("type", "can_next"), ("agents", toJson as), ("operand", encodeDFormula f)]
  | .canAlways as f =>
      Json.mkObj [("type", "can_always"), ("agents", toJson as), ("operand", encodeDFormula f)]
  | .canEventually as f =>
      Json.mkObj [("type", "can_eventually"), ("agents", toJson as), ("operand", encodeDFormula f)]
  | .canUntil as l r =>
      Json.mkObj [("type", "can_until"), ("agents", toJson as),
        ("left", encodeDFormula l), ("right", encodeDFormula r)]
  | .canRelease as l r =>
      Json.mkObj [("type", "can_release"), ("agents", toJson as),
        ("left", encodeDFormula l), ("right", encodeDFormula r)]
  | .grant us f => Json.mkObj [("type", "grant"), ("updates", encodeUpdates us), ("operand", encodeDFormula f)]
  | .revoke us f => Json.mkObj [("type", "revoke"), ("updates", encodeUpdates us), ("operand", encodeDFormula f)]

def encodeUpdates : UpdateList → Json
  | .nil => Json.arr #[]
  | .cons c a as bs rest =>
      Json.arr (#[Json.mkObj [("condition", encodeDFormula c), ("action", toJson a),
        ("agents", toJson as), ("informed", toJson bs)]]
        ++ (match encodeUpdates rest with | .arr xs => xs | _ => #[]))
end

/-- Decode `"pool"`: `[{"kind":"grant"|"revoke","condition":F,"action","agents","informed"?}]`. -/
def decodePool (j : Json) : Except String (List Candidate) := do
  (← j.getArr?).toList.mapM fun c => do
    let grant ← match ← strField c "kind" with
      | "grant" => pure true
      | "revoke" => pure false
      | other => throw s!"pool: unknown kind {other} (expected grant or revoke)"
    let informed ← match ← optField c "informed" with
      | none => pure []
      | some v => (← v.getArr?).toList.mapM (·.getStr?)
    return { grant, cond := ← decodeDFormula (← field c "condition"),
             action := ← strField c "action", agents := ← strListField c "agents", informed }

def encodeStep (st : Step) : Json :=
  Json.mkObj [("kind", if st.grant then "grant" else "revoke"),
    ("clauses", Json.arr (st.clauses.map fun c =>
      Json.mkObj [("condition", encodeDFormula c.cond), ("action", toJson c.action),
        ("agents", toJson c.agents), ("informed", toJson c.informed)]).toArray)]

/-- Answer an `atl_update_search` request: is there a sequence of at most `bound`
clauses (over `pool`, default `defaultPool`) after which `goal` holds at `state`? -/
def atlUpdateSearch (model : Json) (state : String) (goal : DFormula) (bound : Nat)
    (pool : Option (List Candidate)) (fuel : Nat) (sem : AtlSemantics) : Json :=
  match CgsJson.decodeDyn model with
  | .error e => atlErr e.code e.message
  | .ok m =>
    match boundedUpdate m sem.mode state goal bound (pool.getD (defaultPool m)) fuel with
    | .error msg => atlErr "search_failed" msg
    | .ok r =>
      let common := [("explored", toJson r.explored), ("illegal", toJson r.illegal),
        ("semantics", toJson (sem.name ++ "_dynamic")),
        ("complete_for", toJson "the candidate pool within the clause bound")]
      match r.outcome with
      | .notFound => Json.mkObj [("ok", true), ("result", Json.mkObj (("found", toJson false) :: common))]
      | .found steps k =>
        let w := stepsFormula steps goal
        Json.mkObj [("ok", true), ("result", Json.mkObj (
          [("found", toJson true), ("size", toJson k),
           ("updates", Json.arr (steps.map encodeStep).toArray),
           ("formula", toJson (toString w)), ("witness", encodeDFormula w)] ++ common))]
