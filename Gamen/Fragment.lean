import Gamen.Formula
import Gamen.Tableau
import Gamen.Verdict

/-!
# Gamen.Fragment

Port of `gamen-hs/src/Gamen/Fragment.hs`: fragment membership checks for
the two prover backends (adversarial-review refactor, issue #18).

Both provers silently mis-answer formulas built from constructors they do
not decompose: the prefixed tableau treats an unknown operator as an
opaque atom (so `tableauConsistent systemK [Knowledge "a" (p ∧ ¬p)]` would
be reported satisfiable), and a G3DS^k_n saturation predicate is vacuously
true on operators outside `L_n` (so an out-of-fragment formula would
saturate to "refuted"). Both are silent false answers on the clinical
validation path.

The fix is a gate at the service boundary: reject out-of-fragment input
with a structured `UnknownReason.unsupportedOperator` *before* dispatching
to a backend (see `Validate.lean`'s `classifyConsistency`), so the
library's satisfaction functions keep their exhaustive `match`es (which
preserve the exhaustiveness guarantee) yet can never be reached by a bad
request.

**Note on the allowlists**, from the Haskell: the tableau fragment is not
derived from the rules a `System` installs — the rules are opaque
`PrefixedFormula → Branch → RuleResult` functions with no introspectable
domain, and probing them is unreliable. So `allowedInTableau` below is
maintained by hand to match what the Lean engine actually decomposes
(`systemK`/`systemKDt`: base propositional + K modal + belief/ranked-belief
rules — see `Gamen.Tableau`'s "Missing" note in `PORTING.md` for the
K-family systems not yet ported). The G3DS fragment is the fixed `L_n` set
from Lyon & van Berkel 2024, Definition 3 (an external citation, not a B&D
one; not applicable to `bd-screen.pdf`).

No B&D citations appear in this module.
-/
namespace Gamen

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

/-- The immediate subformulas of a node (one level down). -/
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
`firstOffender` recurse through `immediateSubformulas`, as the Haskell
does (`firstOffender ok f = ... mapMaybe (firstOffender ok) (immediateSubformulas f)`),
and still be total. -/
theorem sizeOf_lt_of_mem_immediate {f g : Formula} (h : g ∈ f.immediateSubformulas) :
    sizeOf g < sizeOf f := by
  cases f <;> simp [immediateSubformulas] at h <;>
    (try rcases h with rfl | rfl) <;> (try subst h) <;> simp <;> omega

/-- The name of the first constructor (in top-down, left-to-right order)
that fails the predicate, or `none` if the whole formula is in fragment. -/
def firstOffender (ok : Formula → Bool) (f : Formula) : Option String :=
  if !ok f then some f.constructorName
  else f.immediateSubformulas.attach.findSome? fun ⟨g, _⟩ => g.firstOffender ok
termination_by f
decreasing_by exact sizeOf_lt_of_mem_immediate ‹_›

/-- Is this node's /top/ constructor decomposable by the tableau engine
(base propositional + K modal + belief/ranked-belief rules)? Judges only
the outermost constructor; `firstOffender` recurses into the children.

Temporal operators (G, F, H, P, Since, Until) are *not* in the fragment —
the whole temporal tableau layer is quarantined (gamen-hs issue #25;
Jeremiah's adjudication 2026-09-05): H/P have no core tableau rules at
all, and G/F were built by analogy to □/◇ with no completeness proof.
Knowledge and Announce have no tableau rules either (opaque if they slip
through). Every STIT/deontic/ATL operator routes to the deontic-STIT
prover instead. -/
def allowedInTableau : Formula → Bool
  | .bot | .atomF _ | .not _ | .and .. | .or .. | .implies .. | .iff .. | .box _
  | .diamond _ | .belief .. | .rankedBelief .. => true
  | .knowledge .. | .announce .. => false
  | .futureBox _ | .futureDiamond _ | .pastBox _ | .pastDiamond _
  | .since .. | .until .. => false
  | .stit .. | .choiceDiamond .. | .groupStit _ | .next _ | .ought ..
  | .permitted .. | .coalition .. | .canNext .. | .canAlways ..
  | .canEventually .. | .canUntil .. => false

/-- Is this node's top constructor in the G3DS^k_n language `L_n`
(Lyon & van Berkel 2024, Definition 3):
`⊥, atoms, ¬, ∧, ∨, →, ↔, □, ◇, [i], ⟨i⟩, ⊗_i, ⊖_i`? -/
def allowedInDS : Formula → Bool
  | .bot | .atomF _ | .not _ | .and .. | .or .. | .implies .. | .iff .. | .box _
  | .diamond _ | .stit .. | .choiceDiamond .. | .ought .. | .permitted .. => true
  | .futureBox _ | .futureDiamond _ | .pastBox _ | .pastDiamond _
  | .since .. | .until .. | .knowledge .. | .belief .. | .rankedBelief ..
  | .announce .. | .groupStit _ | .next _ | .coalition .. | .canNext ..
  | .canAlways .. | .canEventually .. | .canUntil .. => false

end Formula

/-- Reject a formula the prefixed-tableau backend cannot decompose.

The `System` argument is accepted for interface symmetry with the backend
and for future per-system refinement; the current allowlist is fixed to
the `gamen-validate` consistency system, as in the Haskell. -/
def checkTableauFragment (_sys : System) (f : Formula) : Except UnknownReason Unit :=
  match f.firstOffender Formula.allowedInTableau with
  | none => .ok ()
  | some name => .error (.unsupportedOperator name)

/-- Reject a formula outside the G3DS^k_n language `L_n`. -/
def checkDSFragment (f : Formula) : Except UnknownReason Unit :=
  match f.firstOffender Formula.allowedInDS with
  | none => .ok ()
  | some name => .error (.unsupportedOperator name)

end Gamen
