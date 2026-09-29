import Gamen.Atl.ModelCheck
import Gamen.Atl.Strategy
import Gamen.Cgs
import Gamen.Formula

/-!
# Gamen.Atl

Port of `gamen-hs/src/Gamen/Atl.hs`: Alternating-time Temporal Logic (ATL)
over Concurrent Game Structures.

ATL extends Coalition Logic with temporal fixpoint operators, allowing
reasoning about strategic ability across infinite plays:

* `⟨⟨C⟩⟩Xφ` — C can force φ at the next step
* `⟨⟨C⟩⟩Gφ` — C has a strategy to maintain φ forever
* `⟨⟨C⟩⟩Fφ` — C has a strategy to eventually reach φ
* `⟨⟨C⟩⟩(φ U ψ)` — C can maintain φ until ψ is reached

Model checking is global: `atlSatisfies` first computes the full
satisfaction set via `Gamen.Atl.ModelCheck.sat` then checks membership.
Complexity: O(|CGS| × |φ|) for memoryless perfect-info strategies
(Alur, Henzinger & Kupferman 2002, §4).

References:
  Alur, Henzinger & Kupferman (2002), *Alternating-time Temporal Logic*,
  JACM 49(5): 672–713. Not among the PDFs in `gamen-hs/notes/` (per
  `Gamen.Cgs`/`Gamen.Atl.ModelCheck`'s docstrings, which make the same
  point about their own §2/§4 citations); kept exactly as the Haskell
  gives it, unverified against a primary source.

Both `error` calls in the Haskell (`atlSatisfies`'s world guard; `sat`'s
own eighteen unsupported-operator errors, propagated) become `Except`,
matching `Gamen.Atl.ModelCheck`'s precedent — never a `panic!`/default. -/
namespace Gamen

/-- M, s ⊩ φ — ATL satisfaction at state `s`, checked via global model
checking.

Errors if `s` is not in `cgsStates`, or if `sat` itself errors (an
unsupported operator outside the ATL/Coalition/propositional fragment, or
`lfp`/`gfp` fuel exhaustion — see `Gamen.Atl.ModelCheck`). -/
def atlSatisfies {s a : Type} [Ord s] [Ord a] [BEq s] (cgs : Cgs s a) (st : s) (f : Formula) :
    Except String Bool :=
  if !cgs.cgsStates.contains st then
    throw "atlSatisfies: state is not in cgsStates"
  else do
    let satSet ← sat cgs f
    pure (satSet.contains st)

/-- A formula is true in a CGS if it holds at every state. -/
def atlIsTrueIn {s a : Type} [Ord s] [Ord a] [BEq s] (cgs : Cgs s a) (f : Formula) :
    Except String Bool := do
  let satSet ← sat cgs f
  pure (satSet == cgs.cgsStates)

end Gamen
