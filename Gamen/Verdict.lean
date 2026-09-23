/-!
# Gamen.Verdict

Port of `gamen-hs/src/Gamen/Verdict.hs`: a three-valued prover answer.
-/
namespace Gamen

inductive UnknownReason where
  | budgetExhausted (steps : Nat)
  | unsupportedOperator (op : String)
  | proverStuck (why : String)
  deriving BEq, Repr

inductive Verdict where
  | definitely (b : Bool)
  | unknown (reason : UnknownReason)
  deriving BEq, Repr

def Verdict.negate : Verdict → Verdict
  | .definitely b => .definitely !b
  | u@(.unknown _) => u

def Verdict.isDefinitelyTrue : Verdict → Bool
  | .definitely b => b
  | .unknown _ => false

def UnknownReason.code : UnknownReason → String
  | .budgetExhausted _ => "budget_exhausted"
  | .unsupportedOperator _ => "unsupported_operator"
  | .proverStuck _ => "prover_stuck"

end Gamen
