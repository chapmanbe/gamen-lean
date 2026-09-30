import Validate.Core

/-!
# The flat extraction format (`Gamen/Protocol.lean`, `decodeFormula`)

gamen-lean#1, the port of gamen-hs#60: an unknown `op` or `temporal_op` is
a parse error, never a guess. The flat format is fed by LLM extraction
output, and the old fallbacks (an unknown `op` became □, an unknown
`temporal_op` was dropped) turned a misspelled prohibition into its
opposite. Byte-level agreement with gamen-hs is `compare.py`'s job
(section C); these cases pin the contract where `lake test` sees it.
-/

namespace ProtocolFlatTests

open Gamen Gamen.Protocol

/-- Decode a flat formula given as JSON text. -/
def flat (s : String) : Except String Formula := do
  decodeFormula (← Lean.Json.parse s)

/-- Lean core has no `BEq (Except ε α)`. -/
instance : BEq (Except String Formula) where
  beq
    | .ok a, .ok b => a == b
    | .error a, .error b => a == b
    | _, _ => false

def isErr (e : Except String Formula) (msg : String) : Bool :=
  match e with | .error m => m == msg | .ok _ => false

def cases : List (String × Bool) := [
  ("flat: box/diamond/box_not, with and without an agent",
    flat "{\"op\":\"box\",\"atom\":\"x\"}" == .ok (.box (.atom "x"))
      && flat "{\"op\":\"box\",\"atom\":\"x\",\"agent\":\"c\"}" == .ok (.ought "c" (.atom "x"))
      && flat "{\"op\":\"diamond\",\"atom\":\"x\"}" == .ok (.diamond (.atom "x"))
      && flat "{\"op\":\"diamond\",\"atom\":\"x\",\"agent\":\"c\"}" == .ok (.permitted "c" (.atom "x"))
      && flat "{\"op\":\"box_not\",\"atom\":\"x\"}" == .ok (.box (.not (.atom "x")))
      && flat "{\"op\":\"box_not\",\"atom\":\"x\",\"agent\":\"c\"}"
        == .ok (.ought "c" (.not (.atom "x")))),
  ("flat: the three temporal_ops, and an absent or null one",
    flat "{\"op\":\"box\",\"atom\":\"x\",\"temporal_op\":\"future_box\"}" == .ok (.box (.futureBox (.atom "x")))
      && flat "{\"op\":\"box\",\"atom\":\"x\",\"temporal_op\":\"future_diamond\"}"
        == .ok (.box (.futureDiamond (.atom "x")))
      && flat "{\"op\":\"box\",\"atom\":\"x\",\"temporal_op\":\"periodic\"}"
        == .ok (.box (.futureBox (.futureDiamond (.atom "x"))))
      && flat "{\"op\":\"box\",\"atom\":\"x\",\"temporal_op\":null}" == .ok (.box (.atom "x"))),
  ("flat: a conditional becomes an implication",
    flat "{\"op\":\"box\",\"atom\":\"x\",\"conditional\":\"c\"}" == .ok (.implies (.atom "c") (.box (.atom "x")))),
  ("gamen-lean#1: an unknown op is an error, not □ (a misspelled prohibition)",
    isErr (flat "{\"op\":\"must\",\"atom\":\"x\"}") "unknown flat op: must"
      && isErr (flat "{\"op\":\"box-not\",\"atom\":\"x\"}") "unknown flat op: box-not"
      && isErr (flat "{\"op\":\"prohibition\",\"atom\":\"x\",\"agent\":\"c\"}") "unknown flat op: prohibition"),
  ("gamen-lean#1: an unknown temporal_op is an error, not dropped",
    isErr (flat "{\"op\":\"box\",\"atom\":\"x\",\"temporal_op\":\"sometimes\"}")
      "unknown flat temporal_op: sometimes"),
  ("gamen-lean#1: temporal_op is checked before op, as in gamen-hs",
    isErr (flat "{\"op\":\"must\",\"atom\":\"x\",\"temporal_op\":\"weird\"}")
      "unknown flat temporal_op: weird"),
  ("gamen-lean#1: validate_formula reports it as a parse_error (gamen-hs's exact bytes)",
    (processLine "{\"action\":\"validate_formula\",\"formula\":{\"op\":\"box\",\"atom\":\"statin\",\"temporal_op\":\"sometimes\"}}").compress
      == "{\"ok\":true,\"result\":{\"parse_error\":\"unknown flat temporal_op: sometimes\",\"valid\":false}}") ]

end ProtocolFlatTests
