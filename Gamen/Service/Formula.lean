import Gamen.Dcleg
import Gamen.Service.Protocol

/-!
# Gamen.Service.Formula

Port of `gamen-hs/protocol/Service/Formula.hs`: decode a `DclegFormula`
from the tree-format JSON of `notes/dcleg-service-protocol.md` §4 (in
gamen-hs). All twelve constructors plus the five convenience aliases
`and`, `implies`, `diamond`, `plausible`, `top`.

Haskell's orphan `FromJSON DclegFormula` instance becomes a function. Its
error messages are aeson's (`key "name" not found`,
`parsing DclegFormula failed, expected Object, but encountered Number`, …),
since the service returns them as `formula_invalid` messages.
-/

namespace Gamen.Service
open Lean (Json)

/-- Decode with explicit fuel, one unit per level of nesting. Running out is
an error, never a formula; `decodeDclegFormula` passes the value's own
nesting depth plus one, which is always enough. -/
def decodeDclegFormulaFuel : Nat → Json → Except String DclegFormula
  | 0, _ => throw "decodeDclegFormula: out of fuel (nesting deeper than the value)"
  | fuel + 1, j =>
    withObject "DclegFormula" j fun o => do
      let sub (k : String) : Except String DclegFormula :=
        reqField o k (decodeDclegFormulaFuel fuel)
      let typ ← reqField o "type" parseText
      match typ with
      | "bot" => pure .dfBot
      | "top" => pure dfTop
      | "prop" => return .dfProp (← reqField o "name" parseString)
      | "turn" => return .dfTurn (← reqField o "agent" parseString)
      | "move" => return .dfMove (← reqField o "move" parseString)
      | "payoff" => do
        let k ← reqField o "value" parseInt
        return .dfPayoff k (← reqField o "agent" parseString)
      | "neg" => return .dfNeg (← sub "operand")
      | "or" => do let l ← sub "left"; return .dfOr l (← sub "right")
      | "conditional" => do
        let a ← sub "antecedent"; return .dfConditional a (← sub "consequent")
      | "belief" => do
        let i ← reqField o "agent" parseString; return .dfBelief i (← sub "operand")
      | "next" => return .dfNext (← sub "operand")
      | "yesterday" => return .dfYesterday (← sub "operand")
      | "box" => return .dfBox (← sub "operand")
      -- convenience aliases
      | "and" => do let l ← sub "left"; return dfAnd l (← sub "right")
      | "implies" => do let l ← sub "left"; return dfImplies l (← sub "right")
      | "diamond" => return dfDiamond (← sub "operand")
      | "plausible" => do
        let i ← reqField o "agent" parseString; return dfPlausible i (← sub "operand")
      | other => throw s!"Unknown DclegFormula type: {other}"

/-- Haskell's `fromJSON :: Value -> Result DclegFormula`. -/
def decodeDclegFormula (j : Json) : Except String DclegFormula :=
  decodeDclegFormulaFuel (depth j + 1) j

end Gamen.Service
