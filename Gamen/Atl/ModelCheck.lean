import Gamen.Cgs
import Gamen.Formula
import Gamen.Kripke

/-!
# Gamen.Atl.ModelCheck

Port of `gamen-hs/src/Gamen/Atl/ModelCheck.hs`: ATL model checking via the
AHK fixpoint algorithm.

The central operation is `sat`: given a CGS and a formula, compute the set
of all states at which the formula holds. For ATL temporal operators this
requires global (whole-model) computation via fixpoints; local per-state
evaluation is not feasible.

Complexity: O(|CGS| × |φ|) for memoryless perfect-info strategies, matching
the bound in Alur, Henzinger & Kupferman (2002) §4.

References:
  Alur, Henzinger & Kupferman (2002), *Alternating-time Temporal Logic*,
  JACM 49(5): 672–713. Not among the PDFs in `gamen-hs/notes/` (per
  `Gamen.Cgs`'s docstring, which makes the same point about the §2/§4
  citations it needs); the page numbers below (pp. 683–684 for Definition 3,
  §4 for the complexity bound) are kept exactly as the Haskell gives them,
  unverified against a primary source.

`sat _ Bot`, `sat cgs (Atom _)`, …, `sat cgs (Coalition c phi)` /
`sat cgs (CanNext c phi)` / `sat cgs (CanAlways c phi)` /
`sat cgs (CanEventually c phi)` / `sat cgs (CanUntil c phi psi)` are total;
the eighteen remaining constructors (temporal, epistemic, doxastic, STIT,
deontic-STIT, LACA — everything outside the ATL/Coalition/propositional
fragment) each `error` in the Haskell. Ported as `Except`, with the
Haskell's wording kept verbatim (matching `Gamen.Laca`'s precedent for the
identical pattern), never a `panic!`/default.

`lfp`/`gfp` iterate "until nothing changes" with no bound in the Haskell;
per the project's one shared fixpoint helper (`Kripke.iterateToFixpoint`),
both are ported to take an explicit `fuel` argument and return `Except`,
unlike their Haskell signatures. `sat` is `lfp`/`gfp`'s only caller here,
and always passes `cgs.cgsStates.size + 1`: `lfp`/`gfp` iterate over subsets
of `s`, but every set built along the way — `∅`, `cgsStates` itself, and
every `preC`/union/intersection of the two — is a subset of `cgsStates`
(`preC` filters `cgs.cgsStates`; the temporal operators' step functions only
intersect/union sets already known to be subsets of it), so the walk is
really through the subset lattice of a universe of size `cgs.cgsStates.size`,
monotone lfp/gfp iteration over which stabilizes within that many rounds by
the usual pigeonhole argument (each non-final round changes the set's size
by at least one, in a fixed direction). Running out of fuel is an error
naming `lfp`/`gfp`, never a default. -/
namespace Gamen

-- ── Fixpoint utilities ──────────────────────────────────────────────────

/-- Least fixpoint of a monotone function over sets of states, starting
from `∅`. See the module docstring for the fuel bound and the deviation
from the Haskell's unbounded `lfp`. -/
def lfp {s : Type} [Ord s] [BEq s] (step : Std.TreeSet s → Std.TreeSet s) (fuel : Nat) :
    Except String (Std.TreeSet s) :=
  iterateToFixpoint "lfp" step fuel ∅

/-- Greatest fixpoint of a monotone function over sets of states, starting
from `initial` (typically `cgsStates`) and iterating downward. Fuel as
`lfp`. -/
def gfp {s : Type} [Ord s] [BEq s] (initial : Std.TreeSet s)
    (step : Std.TreeSet s → Std.TreeSet s) (fuel : Nat) :
    Except String (Std.TreeSet s) :=
  iterateToFixpoint "gfp" step fuel initial

-- ── Satisfaction set ─────────────────────────────────────────────────────

/-- Compute the set of all states satisfying `φ` in a CGS.

Propositional operators are interpreted pointwise via `cgsLabeling`.
Coalition Logic `[C]φ` and ATL `⟨⟨C⟩⟩Xφ` are both one-step preimages
(identical semantics). The three temporal operators use fixpoints:

> sat(⟨⟨C⟩⟩Gφ) = ν X. sat(φ) ∩ preC(C, X)
> sat(⟨⟨C⟩⟩Fφ) = μ X. sat(φ) ∪ preC(C, X)
> sat(⟨⟨C⟩⟩(φ U ψ)) = μ X. sat(ψ) ∪ (sat(φ) ∩ preC(C, X))

(AHK 2002, §4, Definitions 3–5) -/
def sat {s a : Type} [Ord s] [Ord a] [BEq s] (cgs : Cgs s a) (f : Formula) :
    Except String (Std.TreeSet s) := do
  match f with
  | .bot => pure ∅
  | .atomF atm =>
      pure (cgs.cgsStates.filter fun st => (cgs.cgsLabeling st).contains atm.name)
  | .not f' => do
      let sf ← sat cgs f'
      pure (cgs.cgsStates \ sf)
  | .and l r => do
      let sl ← sat cgs l
      let sr ← sat cgs r
      pure (sl ∩ sr)
  | .or l r => do
      let sl ← sat cgs l
      let sr ← sat cgs r
      pure (sl ∪ sr)
  | .implies l r => do
      let sl ← sat cgs l
      let sr ← sat cgs r
      pure ((cgs.cgsStates \ sl) ∪ sr)
  | .iff l r => do
      let sl ← sat cgs l
      let sr ← sat cgs r
      pure ((sl ∩ sr) ∪ (cgs.cgsStates \ (sl ∪ sr)))

  -- [C]φ ≡ ⟨⟨C⟩⟩Xφ — one-step coalition preimage
  | .coalition c f' => do
      let sf ← sat cgs f'
      pure (preC cgs (Std.TreeSet.ofList c) sf)

  -- ⟨⟨C⟩⟩Xφ — same preimage (AHK 2002, Def. 3(1))
  | .canNext c f' => do
      let sf ← sat cgs f'
      pure (preC cgs (Std.TreeSet.ofList c) sf)

  -- ⟨⟨C⟩⟩Gφ — greatest fixpoint (AHK 2002, Def. 3(2))
  | .canAlways c f' => do
      let satPhi ← sat cgs f'
      let coalition := Std.TreeSet.ofList c
      gfp cgs.cgsStates (fun x => satPhi ∩ preC cgs coalition x) (cgs.cgsStates.size + 1)

  -- ⟨⟨C⟩⟩Fφ — least fixpoint (AHK 2002, Def. 3(3))
  | .canEventually c f' => do
      let satPhi ← sat cgs f'
      let coalition := Std.TreeSet.ofList c
      lfp (fun x => satPhi ∪ preC cgs coalition x) (cgs.cgsStates.size + 1)

  -- ⟨⟨C⟩⟩(φ U ψ) — until as least fixpoint (AHK 2002, Def. 3(4))
  | .canUntil c l r => do
      let satPhi ← sat cgs l
      let satPsi ← sat cgs r
      let coalition := Std.TreeSet.ofList c
      lfp (fun x => satPsi ∪ (satPhi ∩ preC cgs coalition x)) (cgs.cgsStates.size + 1)

  -- Operators not supported in CGS model checking
  | .box _ => throw "Box not supported in ATL; use ⟨⟨Ag⟩⟩G for grand-coalition invariance"
  | .diamond _ => throw "Diamond not supported in ATL"
  | .futureBox _ => throw "FutureBox not supported in ATL; use CanAlways"
  | .futureDiamond _ => throw "FutureDiamond not supported in ATL; use CanEventually"
  | .pastBox _ => throw "Past operators not supported in ATL model checking"
  | .pastDiamond _ => throw "Past operators not supported in ATL model checking"
  | .since _ _ => throw "Since not supported in ATL model checking"
  | .until _ _ => throw "Until not supported in ATL model checking"
  | .knowledge _ _ => throw "Knowledge requires an epistemic model (use Gamen.Atel)"
  | .belief _ _ => throw "Belief not supported in ATL model checking"
  | .rankedBelief _ _ _ => throw "RankedBelief not supported in ATL model checking"
  | .announce _ _ => throw "Announce not supported in ATL model checking"
  | .stit _ _ => throw "Stit requires a STIT model (use Gamen.Stit)"
  | .choiceDiamond _ _ => throw "ChoiceDiamond requires a STIT model"
  | .groupStit _ => throw "GroupStit requires a STIT model"
  | .next _ => throw "Next requires a Laca model (use Gamen.Laca)"
  | .ought _ _ => throw "Ought requires a deontic model (use Gamen.DeonticStit)"
  | .permitted _ _ => throw "Permitted requires a deontic model (use Gamen.DeonticStit)"

end Gamen
