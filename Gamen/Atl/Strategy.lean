/-!
# Gamen.Atl.Strategy

Port of `gamen-hs/src/Gamen/Atl/Strategy.hs`: strategy parameterisation for
ATL model checking (Bulling & Jamroga 2014).

ATL admits four distinct logics depending on two independent axes:

* __Memory__: does an agent's strategy depend only on the current state
  (memoryless/positional) or on the full history of play (perfect recall)?

* __Information__: does the agent observe the true state (perfect info) or
  only an equivalence class of states (imperfect info)?

The interaction of these axes gives genuinely different logics — in
particular, the standard fixpoint algorithm is unsound for imperfect-info
strategies (Jamroga & van der Hoek 2004).

References:
* Bulling & Jamroga (2014), *Comparing Variants of Strategic Ability*,
  JAAMAS 28(3): 474–514
* Jamroga & van der Hoek (2004), *Agents That Know How to Play*,
  Fundamenta Informaticae 63(2–3): 185–219

Neither PDF is among `gamen-hs/notes/`, so these citations are kept exactly
as the Haskell gives them, unverified against a primary source.
-/

namespace Gamen.Atl.Strategy

/-- The four cells of the (memory × information) strategy grid.

Phase 2 (gamen-hs ATL) implements `memorylessPI` only. The other three
constructors are present so that function signatures and data types can
accommodate them from day one; gamen-hs's own comment says model-checking
functions would throw `error "not yet supported"` for any other
constructor, but that is a planned check, not an existing one — no
function in gamen-hs's `src/` currently takes a `StrategyClass` at all
(`Atl.hs` re-exports the type but calls no function on it), so there is no
call site to port as `Except` yet. -/
inductive StrategyClass
  | memorylessPI    -- Positional + perfect info — standard ATL (AHK 2002)
  | perfectRecallPI -- History + perfect info — ATL with memory
  | memorylessIR    -- Positional + imperfect info — ATLir
  | perfectRecallIR -- History + imperfect info — ATLiR
  deriving BEq, Ord, Repr, DecidableEq

end Gamen.Atl.Strategy
