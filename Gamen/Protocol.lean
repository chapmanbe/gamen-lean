import Lean.Data.Json
import Gamen.Formula
import Gamen.Verdict

/-!
# Gamen.Protocol

Port of `gamen-hs/protocol/Gamen/Protocol/Formula.hs` (the JSON codec for
`Formula`) and `gamen-hs/src/Gamen/Fragment.hs` (per-prover fragment
gating), plus `hasAgentOperator` from `Gamen.Formula`.

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
selects flat format. -/
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
  Ought/Permitted; an optional temporal wrapper and conditional antecedent. -/
  flat (op : String) : Except String Formula := do
    let core : Formula := .atom (← strField j "atom")
    let cond ← optStr j "conditional"
    let temp ← optStr j "temporal_op"
    let agent ← optStr j "agent"
    let temporalCore : Formula := match temp with
      | some "future_box" => .futureBox core
      | some "future_diamond" => .futureDiamond core
      | some "periodic" => .futureBox (.futureDiamond core)
      | _ => core
    let deontic : Formula := match op, agent with
      | "box", some ag => .ought ag temporalCore
      | "box", none => .box temporalCore
      | "diamond", some ag => .permitted ag temporalCore
      | "diamond", none => .diamond temporalCore
      | "box_not", some ag => .ought ag (.not temporalCore)
      | "box_not", none => .box (.not temporalCore)
      | _, _ => .box temporalCore  -- fallback, as in Haskell
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

/-! ## Fragment gating (port of `Gamen.Fragment`) -/

namespace Formula

/-- Haskell constructor name, used verbatim in wire-protocol errors. -/
def constructorName : Formula → String
  | .bot => "Bot" | .atomF _ => "Atom" | .not _ => "Not" | .and .. => "And"
  | .or .. => "Or" | .implies .. => "Implies" | .iff .. => "Iff" | .box _ => "Box"
  | .diamond _ => "Diamond" | .futureBox _ => "FutureBox"
  | .futureDiamond _ => "FutureDiamond" | .pastBox _ => "PastBox"
  | .pastDiamond _ => "PastDiamond" | .since .. => "Since" | .until .. => "Until"
  | .knowledge .. => "Knowledge" | .belief .. => "Belief"
  | .rankedBelief .. => "RankedBelief" | .announce .. => "Announce"
  | .stit .. => "Stit" | .choiceDiamond .. => "ChoiceDiamond"
  | .groupStit _ => "GroupStit" | .next _ => "Next" | .ought .. => "Ought"
  | .permitted .. => "Permitted" | .coalition .. => "Coalition"
  | .canNext .. => "CanNext" | .canAlways .. => "CanAlways"
  | .canEventually .. => "CanEventually" | .canUntil .. => "CanUntil"

def immediateSubformulas : Formula → List Formula
  | .bot | .atomF _ => []
  | .not g | .box g | .diamond g | .futureBox g | .futureDiamond g | .pastBox g
  | .pastDiamond g | .knowledge _ g | .belief _ g | .rankedBelief _ _ g
  | .stit _ g | .choiceDiamond _ g | .groupStit g | .next g | .ought _ g
  | .permitted _ g | .coalition _ g | .canNext _ g | .canAlways _ g
  | .canEventually _ g => [g]
  | .and l r | .or l r | .implies l r | .iff l r | .since l r | .until l r
  | .announce l r | .canUntil _ l r => [l, r]

/-- Every immediate subformula is structurally smaller. This one lemma lets
`hasAgentOperator` and `firstOffender` recurse through
`immediateSubformulas`, as the Haskell does, and still be total. -/
theorem sizeOf_lt_of_mem_immediate {f g : Formula} (h : g ∈ f.immediateSubformulas) :
    sizeOf g < sizeOf f := by
  cases f <;> simp [immediateSubformulas] at h <;>
    (try rcases h with rfl | rfl) <;> (try subst h) <;> simp <;> omega

/-- Is the top-level constructor an agent operator? -/
def isAgentOperator : Formula → Bool
  | .stit .. | .choiceDiamond .. | .ought .. | .permitted .. | .coalition ..
  | .canNext .. | .canAlways .. | .canEventually .. | .canUntil .. => true
  | _ => false

/-- Does the formula contain an agent operator anywhere (which dispatches
consistency checking to the deontic-STIT prover)? -/
def hasAgentOperator (f : Formula) : Bool :=
  f.isAgentOperator || f.immediateSubformulas.attach.any fun ⟨g, _⟩ => g.hasAgentOperator
termination_by f
decreasing_by exact sizeOf_lt_of_mem_immediate ‹_›

/-- The first constructor (pre-order) that `ok` rejects. -/
def firstOffender (ok : Formula → Bool) (f : Formula) : Option String :=
  if !ok f then some f.constructorName
  else f.immediateSubformulas.attach.findSome? fun ⟨g, _⟩ => g.firstOffender ok
termination_by f
decreasing_by exact sizeOf_lt_of_mem_immediate ‹_›

/-- Operators the consistency tableau (KDt + doxastic D + ranking) accepts. -/
def allowedInTableau : Formula → Bool
  | .bot | .atomF _ | .not _ | .and .. | .or .. | .implies .. | .iff .. | .box _
  | .diamond _ | .belief .. | .rankedBelief .. => true
  | _ => false

/-- Operators the deontic-STIT prover (G3DS) accepts. -/
def allowedInDS : Formula → Bool
  | .bot | .atomF _ | .not _ | .and .. | .or .. | .implies .. | .iff .. | .box _
  | .diamond _ | .stit .. | .choiceDiamond .. | .ought .. | .permitted .. => true
  | _ => false

end Formula
end Gamen
