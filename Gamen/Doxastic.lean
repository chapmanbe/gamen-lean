import Gamen.Formula
import Gamen.Tableau

/-!
# Gamen.Doxastic

Port of `gamen-hs/src/Gamen/Doxastic.hs`: non-factive belief operator `B_a`.

Standard axiomatization is KD45:

* **K**: `B_a(p → q) → (B_a p → B_a q)` (distribution; free in normal modal logic)
* **D**: `B_a p → ¬B_a(¬p)` (consistency: agents do not believe contradictions)
* **4**: `B_a p → B_a(B_a p)` (positive introspection)
* **5**: `¬B_a p → B_a(¬B_a p)` (negative introspection)

B is non-factive: `B_a p ↛ p`. An agent can believe false things. This
distinguishes belief from knowledge (`Gamen.Epistemic.Knowledge`), which
includes the T axiom `K_a p → p`.

## Tableau coverage

This module currently provides the **D** axiom rule, which catches
single-agent contradictory beliefs:

> `B_radA(PE) ∧ B_radA(¬PE) ⊢ ⊥`

Multi-agent disagreement remains consistent (different agents → opaque
formulas in the prefixed tableau):

> `B_radA(PE) ∧ B_radB(¬PE)` is satisfiable

The 4 and 5 axioms (introspection) require agent-labelled prefixes, which
the current single-relation prefix infrastructure does not support. They
are not implemented here.

The Haskell docstring cites no B&D definition or table number for this
module (KD45 belief is not itself a Boxes & Diamonds topic); none is
carried over here either.
-/
namespace Gamen

/-- **D** axiom for belief: an agent does not believe both `p` and `¬p`.

Rule: `σ T B_a p → σ F B_a(¬p)`.

Closes a branch where both `σ T B_a p` and `σ T B_a(¬p)` have been
asserted (the second triggers `σ F B_a(¬p)` which contradicts the explicit
`σ T B_a(¬p)`). -/
def applyDoxasticDRule : Rule
  | ⟨σ, .T, .belief a p⟩, b =>
    let new := pfFalse σ (.belief a (.not p))
    if b.contains new then .noRule else .stack [new]
  | _, _ => .noRule

/-- Used-prefix rules for KD belief (currently just D).
Add to the `usedPrefixRules` list of a `System`. -/
def doxasticRules : List Rule := [applyDoxasticDRule]

end Gamen
