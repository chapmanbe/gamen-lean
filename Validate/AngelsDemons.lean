import Gamen.Protocol
import Gamen.AngelsDemons

/-!
# Validate.AngelsDemons

The Lean-only `angels_demons_check` request of `gamen-validate` (protocol 7): model-check
SDL/SCL/SUL formulas (`Gamen.AngelsDemons`; Catta, Galimullin & Mittelmann, AAMAS 2026) on
a weighted graph given as JSON. See `Validate.lean` for the wire format. gamen-hs has no
such request; it is outside `tools/compare`'s scope.
-/
open Lean (Json toJson)
open Gamen Gamen.Protocol Gamen.AngelsDemons

/-- A decoding error with a stable `error_code`. -/
structure AdError where
  code : String
  message : String

instance : Inhabited AdError := ⟨⟨"", ""⟩⟩

private def malformed (msg : String) : AdError := ⟨"malformed_spec", msg⟩

private def lift {α} (r : Except String α) : Except AdError α := r.mapError malformed

def adErr (e : AdError) : Json :=
  Json.mkObj [("ok", false), ("error", toJson e.message), ("error_code", toJson e.code)]

/-- Reject a key the request does not define: a misspelled `valuation` or `costs` would
otherwise be read as absent, and silently change every answer. -/
private def onlyKeys (j : Json) (allowed : List String) (what : String) : Except AdError Unit :=
  match j with
  | .obj kvs =>
    match kvs.toList.find? (fun (k, _) => !allowed.contains k) with
    | some (k, _) => throw (malformed s!"{what}: unknown key \"{k}\" (expected one of {allowed})")
    | none => pure ()
  | _ => throw (malformed s!"{what} must be an object")

private def stateIdx (names : Array String) (n : String) : Except AdError Nat :=
  match names.findIdx? (· == n) with
  | some i => pure i
  | none => throw ⟨"unknown_state", s!"unknown state \"{n}\""⟩

private def nat (j : Json) (what : String) : Except AdError Nat :=
  match j.getNat? with
  | .ok n => pure n
  | .error _ => throw (malformed s!"{what} must be a non-negative integer")

/-- Decode a model:
`{"states":[..],"edges":[[from,to],..],"costs":[[from,to,n],..],"default_cost":1,
"valuation":{"s":[atoms]}}`. `costs` overrides `default_cost` (default 1) pairwise (naming a pair twice is an error); every
ordered pair needs a positive cost (Def 1), and the graph must be serial. -/
def decodeWModel (j : Json) : Except AdError WModel := do
  onlyKeys j ["states", "edges", "costs", "default_cost", "valuation"] "model"
  let names ← lift ((← lift (field j "states")).getArr? >>= fun a => a.toList.mapM (·.getStr?))
  if let some n := names.find? (fun n => names.count n > 1) then
    throw ⟨"duplicate_state", s!"duplicate state name \"{n}\""⟩
  let arr := names.toArray
  let edges ← match ← lift (optField j "edges") with
    | none => pure []
    | some v => (← lift v.getArr?).toList.mapM fun e => do
        let p ← lift e.getArr?
        match p.toList with
        | [a, b] => pure (← stateIdx arr (← lift a.getStr?), ← stateIdx arr (← lift b.getStr?))
        | _ => throw (malformed "an edge is a pair [from, to]")
  let dflt ← match ← lift (optField j "default_cost") with
    | none => pure 1
    | some v => nat v "default_cost"
  let costs ← match ← lift (optField j "costs") with
    | none => pure []
    | some v => (← lift v.getArr?).toList.mapM fun e => do
        match (← lift e.getArr?).toList with
        | [a, b, c] => pure (← stateIdx arr (← lift a.getStr?), ← stateIdx arr (← lift b.getStr?),
            ← nat c "a cost")
        | _ => throw (malformed "a cost entry is [from, to, n]")
  for (i, k, _) in costs do
    if (costs.filter fun (a, b, _) => a == i && b == k).length > 1 then
      throw (malformed s!"costs: the pair \"{names[i]!}\" → \"{names[k]!}\" is given more than once")
  let cost (i k : Nat) : Nat :=
    match costs.find? (fun (a, b, _) => a == i && b == k) with
    | some (_, _, c) => c
    | none => dflt
  let labels ← match ← lift (optField j "valuation") with
    | none => pure ([] : List (Nat × List String))
    | some (.obj kvs) => kvs.toList.mapM fun (s, v) => do
        pure (← stateIdx arr s, ← lift (v.getArr? >>= fun a => a.toList.mapM (·.getStr?)))
    | some _ => throw (malformed "valuation must be an object")
  let lab (i : Nat) : List String := (labels.filter (·.1 == i)).flatMap (·.2)
  (mkWModel names edges cost lab).mapError fun msg => ⟨"invalid_model", msg⟩

/- Formulas:

    {"type":"atom","name":"p"}  "top"  "bot"  "not"(operand)  "and"/"or"/"implies"(left,right)
    {"type":"demon"|"demon_box"|"angel"|"angel_box","bound":n,"path":P}
    {"type":"update"|"update_box"|"update_demon"|"update_demon_box"|"update_angel"
            |"update_angel_box"|"update_none"|"update_none_box","angel_bound":a,"demon_bound":d,"path":P}

with path `P` one of `{"type":"next","operand":F}`, `{"type":"until"|"release","left":F,
"right":F}`, `{"type":"eventually"|"always","operand":F}`. `demon` is `⟨⟨n⟩⟩`
of SDL (Defs 4-5), `angel` that of SCL (Defs 7-8), the `_box` forms are their duals `[n]`, and
`update` is the cooperative `⟨[angel a, demon d]⟩` (Defs 10-11); `update_demon` is `⟨[demon d]⟩^a`
(the demon has a strategy against every angelic `a`-strategy), `update_angel` is `⟨[angel a]⟩^d`,
`update_none` is `⟨[∅]⟩^{a,d}`, and each `_box` is the dual. All take both bounds. Against a
universal opponent each side's own move must be legal (reading A, `Gamen.AngelsDemons.movesFrom`).

`partial` as `decodeDFormula` is: recursion goes through JSON field lookups. -/
mutual
partial def decodeSFormula (j : Json) : Except AdError SFormula := do
  let sub (k : String) : Except AdError SFormula := do decodeSFormula (← lift (field j k))
  let path : Except AdError PFormula := do decodePFormula (← lift (field j "path"))
  let bound (k : String := "bound") : Except AdError Nat := do nat (← lift (field j k)) k
  let ty ← lift (strField j "type")
  onlyKeys j (["type"] ++ match ty with
    | "atom" => ["name"]
    | "not" => ["operand"]
    | "and" | "or" | "implies" => ["left", "right"]
    | "update" | "update_box" | "update_demon" | "update_demon_box" | "update_angel"
    | "update_angel_box" | "update_none" | "update_none_box" => ["angel_bound", "demon_bound", "path"]
    | "demon" | "demon_box" | "angel" | "angel_box" => ["bound", "path"]
    | _ => []) s!"formula \"{ty}\""
  match ty with
  | "atom" => return .atom (← lift (strField j "name"))
  | "top" => return SFormula.top
  | "bot" => return .not SFormula.top
  | "not" => return .not (← sub "operand")
  | "and" => return .and (← sub "left") (← sub "right")
  | "or" => return .or (← sub "left") (← sub "right")
  | "implies" => return .or (.not (← sub "left")) (← sub "right")
  | "demon" => return .demon (← bound) (← path)
  | "demon_box" => return .demonBox (← bound) (← path)
  | "angel" => return .angel (← bound) (← path)
  | "angel_box" => return .angelBox (← bound) (← path)
  | "update" => return .update (← bound "angel_bound") (← bound "demon_bound") (← path)
  | "update_box" => return .updateBox (← bound "angel_bound") (← bound "demon_bound") (← path)
  | "update_demon" => return .updateDemon (← bound "demon_bound") (← bound "angel_bound") (← path)
  | "update_demon_box" =>
    return .updateDemonBox (← bound "demon_bound") (← bound "angel_bound") (← path)
  | "update_angel" => return .updateAngel (← bound "angel_bound") (← bound "demon_bound") (← path)
  | "update_angel_box" =>
    return .updateAngelBox (← bound "angel_bound") (← bound "demon_bound") (← path)
  | "update_none" => return .updateNone (← bound "angel_bound") (← bound "demon_bound") (← path)
  | "update_none_box" =>
    return .updateNoneBox (← bound "angel_bound") (← bound "demon_bound") (← path)
  | other => throw (malformed s!"Unknown formula type: {other}")

partial def decodePFormula (j : Json) : Except AdError PFormula := do
  let sub (k : String) : Except AdError SFormula := do decodeSFormula (← lift (field j k))
  let ty ← lift (strField j "type")
  onlyKeys j (["type"] ++ match ty with
    | "next" | "eventually" | "always" => ["operand"]
    | _ => ["left", "right"]) s!"path \"{ty}\""
  match ty with
  | "next" => return .next (← sub "operand")
  | "until" => return .until (← sub "left") (← sub "right")
  | "release" => return .release (← sub "left") (← sub "right")
  | "eventually" => return PFormula.eventually (← sub "operand")
  | "always" => return PFormula.always (← sub "operand")
  | other => throw (malformed s!"Unknown path type: {other}")
end

/-- The largest `max_models` a request may ask for: the arena is built in memory. -/
def maxModelsLimit : Nat := 1000000

/-- Answer an `angels_demons_check` request. `states = none` reports every state;
`maxModels` caps the arena of pointed models. -/
def angelsDemonsCheck (model : Json) (formulas : List Json) (states : Option (List String))
    (maxModels : Nat) : Json :=
  if maxModels == 0 || maxModels > maxModelsLimit then
    adErr ⟨"bad_max_models", s!"max_models must be between 1 and {maxModelsLimit}"⟩
  else
  match decodeWModel model with
  | .error e => adErr e
  | .ok m =>
    let all := m.states.toList
    let report := states.getD all
    match report.find? (fun s => !m.states.contains s) with
    | some s => adErr ⟨"unknown_state", s!"states: unknown state \"{s}\""⟩
    | none =>
    match report.find? (fun s => report.count s > 1) with
    | some s => adErr (malformed s!"states: \"{s}\" is listed more than once")
    | none =>
      let item (fj : Json) (i : Nat) : Json :=
        let base := [("index", toJson i)]
        match decodeSFormula fj with
        | .error e => Json.mkObj (base ++ [("error", toJson e.message), ("error_code", toJson e.code)])
        | .ok f =>
          match satStates m f maxModels with
          | .error msg =>
            Json.mkObj (base ++ [("error", toJson msg), ("error_code", "check_failed")])
          | .ok sat =>
            Json.mkObj (base ++ [
              ("satisfying", toJson (report.filter sat.contains)),
              ("holds", Json.mkObj (report.map fun s => (s, toJson (sat.contains s)))),
              ("true_in_model", toJson (all.all sat.contains))])
      Json.mkObj [("ok", true), ("result", Json.mkObj [
        ("states", toJson report),
        ("results", Json.arr (formulas.zipIdx.map fun (f, i) => item f i).toArray)])]
