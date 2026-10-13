import Lean.Data.Json
import Gamen.Formula
import Gamen.Verdict

/-!
# Gamen.Protocol

Port of `gamen-hs/protocol/Gamen/Protocol/Formula.hs`: the JSON codec for
`Formula`. Fragment gating (`gamen-hs/src/Gamen/Fragment.hs`) lives in
`Gamen.Fragment`; `hasAgentOperator` lives in `Gamen.Formula`, as in the
Haskell.

Two decoding formats, as in Haskell:

1. **Tree format**, keyed by `"type"`, round-trips with `toJson`:
   `{"type": "box", "operand": {"type": "atom", "name": "p"}}`
2. **Flat extraction format**, keyed by `"op"`, from LLM extraction:
   `{"op": "box", "atom": "statin", "conditional": "ascvd",
     "temporal_op": "future_box", "agent": "clinician"}`

Like the Haskell codec, this lives outside the core library files so that
`Gamen.Formula` stays free of JSON dependencies.
-/
namespace Gamen
open Lean (Json ToJson FromJson toJson fromJson?)

namespace Protocol

/-- The wire-protocol version that the Lean-only `{"action":"version"}`
request reports (plans/downstream-migration-2026-09-29.md, Phase 0a).
Protocol 1 is gamen-hs's five actions, byte-compatible except for
`tools/compare/intentional-divergences.md`, plus `version` itself. Bump it
whenever a Lean-only extension changes what a caller can send or receive. -/
def protocolVersion : Nat := 4

/-- Optional field: missing or `null` both mean `none` (aeson's `.:?`). -/
def optField (o : Json) (k : String) : Except String (Option Json) :=
  match o.getObjVal? k with
  | .ok .null => .ok none
  | .ok v => .ok (some v)
  | .error _ => .ok none

def field (o : Json) (k : String) : Except String Json :=
  match o.getObjVal? k with
  | .ok v => .ok v
  | .error _ => .error s!"key \"{k}\" not found"

def strField (o : Json) (k : String) : Except String String := do
  (← field o k).getStr?

def optStr (o : Json) (k : String) : Except String (Option String) := do
  match ← optField o k with
  | none => return none
  | some v => return some (← v.getStr?)

def strListField (o : Json) (k : String) : Except String (List String) := do
  let arr ← (← field o k).getArr?
  arr.toList.mapM (·.getStr?)

end Protocol

open Protocol in
/-- Decode a formula. A `"type"` key selects tree format; an `"op"` key
selects flat format.

`partial` because the recursion goes through field lookups (`sub`
fetches a child by key from the object's field map), which Lean can't see
as structural descent into `Json`. It terminates: every recursive call
decodes a value nested strictly inside `j`, and parsed JSON is finite. -/
partial def decodeFormula (j : Json) : Except String Formula := do
  let .obj _ := j | throw "Formula JSON must be an object"
  match ← optStr j "type", ← optStr j "op" with
  | some typ, _ => tree typ
  | none, some op => flat op
  | none, none =>
    throw "Formula JSON must have either 'type' (tree format) or 'op' (extraction format)"
where
  sub (k : String) : Except String Formula := do decodeFormula (← field j k)
  tree (typ : String) : Except String Formula := do
    match typ with
    | "bot" => return .bot
    | "atom" => return .atom (← strField j "name")
    | "not" => return .not (← sub "operand")
    | "and" => return .and (← sub "left") (← sub "right")
    | "or" => return .or (← sub "left") (← sub "right")
    | "implies" => return .implies (← sub "left") (← sub "right")
    | "iff" => return .iff (← sub "left") (← sub "right")
    | "box" => return .box (← sub "operand")
    | "diamond" => return .diamond (← sub "operand")
    | "future_box" => return .futureBox (← sub "operand")
    | "future_diamond" => return .futureDiamond (← sub "operand")
    | "past_box" => return .pastBox (← sub "operand")
    | "past_diamond" => return .pastDiamond (← sub "operand")
    | "since" => return .since (← sub "left") (← sub "right")
    | "until" => return .until (← sub "left") (← sub "right")
    | "knowledge" => return .knowledge (← strField j "agent") (← sub "operand")
    | "belief" => return .belief (← strField j "agent") (← sub "operand")
    | "ranked_belief" =>
      return .rankedBelief (← strField j "agent") (← (← field j "rank").getInt?) (← sub "operand")
    | "announce" => return .announce (← sub "left") (← sub "right")
    | "stit" => return .stit (← strField j "agent") (← sub "operand")
    | "choice_diamond" => return .choiceDiamond (← strField j "agent") (← sub "operand")
    | "group_stit" => return .groupStit (← sub "operand")
    | "next" => return .next (← sub "operand")
    | "ought" => return .ought (← strField j "agent") (← sub "operand")
    | "permitted" => return .permitted (← strField j "agent") (← sub "operand")
    | "coalition" => return .coalition (← strListField j "agents") (← sub "operand")
    | "can_next" => return .canNext (← strListField j "agents") (← sub "operand")
    | "can_always" => return .canAlways (← strListField j "agents") (← sub "operand")
    | "can_eventually" => return .canEventually (← strListField j "agents") (← sub "operand")
    | "can_until" => return .canUntil (← strListField j "agents") (← sub "left") (← sub "right")
    | other => throw s!"Unknown formula type: {other}"
  /-- Flat format: `box`/`diamond`/`box_not`, with an agent becoming
  Ought/Permitted; an optional temporal wrapper and conditional antecedent.

  Any other `op`, or a `temporal_op` other than the three below (or an
  absent/null one), is an error, as in gamen-hs since gamen-hs#60 (commit
  `2fba336`); gamen-lean#1. The flat format is fed by LLM extraction
  output, and the old fallbacks (an unknown `op` became □, an unknown
  `temporal_op` was dropped) silently turned a misspelled prohibition into
  its opposite. `temporal_op` is checked before `op`, as in gamen-hs. -/
  flat (op : String) : Except String Formula := do
    let core : Formula := .atom (← strField j "atom")
    let cond ← optStr j "conditional"
    let temp ← optStr j "temporal_op"
    let agent ← optStr j "agent"
    let temporalCore : Formula ← match temp with
      | none => pure core
      | some "future_box" => pure (.futureBox core)
      | some "future_diamond" => pure (.futureDiamond core)
      | some "periodic" => pure (.futureBox (.futureDiamond core))
      | some t => throw s!"unknown flat temporal_op: {t}"
    let deontic : Formula ← match op, agent with
      | "box", some ag => pure (.ought ag temporalCore)
      | "box", none => pure (.box temporalCore)
      | "diamond", some ag => pure (.permitted ag temporalCore)
      | "diamond", none => pure (.diamond temporalCore)
      | "box_not", some ag => pure (.ought ag (.not temporalCore))
      | "box_not", none => pure (.box (.not temporalCore))
      | _, _ => throw s!"unknown flat op: {op}"
    return match cond with
      | some c => .implies (.atom c) deontic
      | none => deontic

/-- Encode to tree format. Round-trips with `decodeFormula` for all 30
constructors. -/
def encodeFormula : Formula → Json
  | .bot => ty "bot" []
  | .atomF a => ty "atom" [("name", a.name)]
  | .not f => ty "not" [("operand", encodeFormula f)]
  | .and l r => ty "and" [("left", encodeFormula l), ("right", encodeFormula r)]
  | .or l r => ty "or" [("left", encodeFormula l), ("right", encodeFormula r)]
  | .implies l r => ty "implies" [("left", encodeFormula l), ("right", encodeFormula r)]
  | .iff l r => ty "iff" [("left", encodeFormula l), ("right", encodeFormula r)]
  | .box f => ty "box" [("operand", encodeFormula f)]
  | .diamond f => ty "diamond" [("operand", encodeFormula f)]
  | .futureBox f => ty "future_box" [("operand", encodeFormula f)]
  | .futureDiamond f => ty "future_diamond" [("operand", encodeFormula f)]
  | .pastBox f => ty "past_box" [("operand", encodeFormula f)]
  | .pastDiamond f => ty "past_diamond" [("operand", encodeFormula f)]
  | .since l r => ty "since" [("left", encodeFormula l), ("right", encodeFormula r)]
  | .until l r => ty "until" [("left", encodeFormula l), ("right", encodeFormula r)]
  | .knowledge a f => ty "knowledge" [("agent", a), ("operand", encodeFormula f)]
  | .belief a f => ty "belief" [("agent", a), ("operand", encodeFormula f)]
  | .rankedBelief a n f =>
    ty "ranked_belief" [("agent", a), ("rank", toJson n), ("operand", encodeFormula f)]
  | .announce b c => ty "announce" [("left", encodeFormula b), ("right", encodeFormula c)]
  | .stit a f => ty "stit" [("agent", a), ("operand", encodeFormula f)]
  | .choiceDiamond a f => ty "choice_diamond" [("agent", a), ("operand", encodeFormula f)]
  | .groupStit f => ty "group_stit" [("operand", encodeFormula f)]
  | .next f => ty "next" [("operand", encodeFormula f)]
  | .ought a f => ty "ought" [("agent", a), ("operand", encodeFormula f)]
  | .permitted a f => ty "permitted" [("agent", a), ("operand", encodeFormula f)]
  | .coalition as f => ty "coalition" [("agents", toJson as), ("operand", encodeFormula f)]
  | .canNext as f => ty "can_next" [("agents", toJson as), ("operand", encodeFormula f)]
  | .canAlways as f => ty "can_always" [("agents", toJson as), ("operand", encodeFormula f)]
  | .canEventually as f => ty "can_eventually" [("agents", toJson as), ("operand", encodeFormula f)]
  | .canUntil as l r =>
    ty "can_until" [("agents", toJson as), ("left", encodeFormula l), ("right", encodeFormula r)]
where
  ty (t : String) (fields : List (String × Json)) : Json :=
    Json.mkObj (("type", Json.str t) :: fields)

instance : ToJson Formula := ⟨encodeFormula⟩
instance : FromJson Formula := ⟨decodeFormula⟩

end Gamen
