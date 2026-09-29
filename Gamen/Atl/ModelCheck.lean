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
naming `lfp`/`gfp`, never a default.

**Laziness.** `sat`'s Haskell body is pure (no `Except`; `error` is a bare
partial-function call), so `Data.Set`'s own laziness decides, for the
propositional connectives, whether an illegal sub-formula on one side of
`And`/`Or`/`Implies`/`Iff` is ever forced — and a strict left-then-right
`Except` translation can throw where the Haskell, having never forced the
illegal side, returns a definite answer. Confirmed directly against GHC's
`containers` (`cabal repl`, `Data.Set.intersection`/`union`/`difference`,
forcing an `error` thunk on one side under `seq`): `intersection ∅ e = ∅`
and `difference ∅ e = ∅` *without evaluating* `e`; `intersection a e`
(`a` nonempty) and `difference a e` (`a` nonempty) force `e`; `union`
forces its second argument unconditionally, and — since every caller here
(including every test in `Tests/Main.lean`) eventually forces the union's
*result* to compare it — its first argument too, so `union` itself adds no
observable short-circuit under full demand. Working through `sat`'s five
propositional clauses under these rules (confirmed against gamen-hs
directly for every case below, via `cabal repl`):
- `Not f'`: `Set.difference states (go f')` skips `f'` exactly when
  `states` (`cgs.cgsStates`, plain data, never itself throws) is empty —
  relevant on a CGS with no states, which `mkCgs` does not reject.
- `And l r`: `go l` is always forced (it is `intersection`'s first
  argument); `go r` is skipped exactly when `go l`'s result is empty (e.g.
  `sat cgs (And Bot (Box p)) = ∅`, confirmed, never touching `Box`'s error).
- `Or l r`: both sides always forced (per `union`'s rule above), no
  shortcut to replicate; but `union` forces its *second* argument first,
  so `r` is evaluated before `l` (see "Error order" below).
- `Implies l r`: the antecedent `Set.difference states (go l)` follows
  `Not`'s rule (`go l` skipped iff `states` is empty); the consequent
  `go r` is `union`'s second argument, so it is *always* forced regardless
  of `states`/`l` — confirmed asymmetric: on a zero-state CGS,
  `sat cgs (Implies (Box p) q) = ∅` (antecedent's `Box` never reached) but
  `sat cgs (Implies p (Box q))` errors (consequent's `Box` always reached).
- `Iff l r`: `go l` is always forced, in every case (it is the shared
  `intersection sl sr`'s first argument, and that `intersection` is itself
  always eventually forced, directly or via `union`'s pass-through under
  full demand). `go r` is skipped only when `states` is *also* empty and
  `go l`'s result is empty — when `states` is nonempty, the antecedent's
  own `Set.union sl sr` unconditionally forces `sr` regardless of `sl`, so
  there is no shortcut to replicate in that case (confirmed:
  `sat loop (Iff Bot (Box p))` errors, on a *nonempty*-state model, even
  though the left side is `Bot`).

Every one of these eight shapes (each connective's short-circuit and
non-short-circuit side) was checked against gamen-hs's actual `sat`, not
derived from the Haskell source alone; see `atlModelCheckCases`'s "Not in
gamen-hs: laziness" cases. The ATL temporal operators (`CanAlways`,
`CanEventually`, `CanUntil`) were audited the same way and need no such
handling: `satPhi`/`satPsi` are each an unconditionally-forced first
argument to their step function's own `intersection`/`union` (as above),
and `lfp`/`gfp` always invoke the step function at least once (to test the
initial iterate), so they are always forced regardless of `preC`'s
value — confirmed directly (`sat loop (CanAlways ["alice"] (Box p))` and
its `CanEventually`/`CanUntil` siblings, phi or psi illegal, all error).
`Gamen.Atel.atelSat`'s `Knowledge` clause (`Set.isSubsetOf`) was audited
too and also needs no handling: unlike `intersection`/`difference`,
`Data.Set.isSubsetOf`'s *left* argument being empty does not skip forcing
the right (confirmed: `Set.isSubsetOf Set.empty (error …)` still throws
under `seq`). But that `isSubsetOf` sits inside a `Set.filter` over
`states`, so on a zero-state model `go phi` is never forced at all
(GHCi, 2026-09-29: `atelSat zeroModel (Knowledge "alice" (Box p))` = ∅):
`atelSat` now skips it when `states` is empty (correction, 2026-09-29).

**Error order** (added 2026-09-29, checked in GHCi). When *both* operands
of a connective error, which error GHC reports is also decided by
`Data.Set`'s forcing order: `union` forces its second argument first, so
`Or l r` and `Implies l r` report `r`'s error, and so does `Iff l r` when
`states` is nonempty (its outer `union`'s second argument contains
`Set.union sl sr`); `And` reports `l`'s (`intersection`'s first argument);
`CanUntil` reports `φ`'s before `ψ`'s (the step function
`union satPsi (intersection satPhi …)` forces the `intersection`, hence
`satPhi`, first). The earlier port evaluated `l` first everywhere, which
gave the left error for `Or`/`Implies`/`Iff`; fixed, with a "Not in
gamen-hs: error order" case for each.

**One-step coalition operators** (correction, 2026-09-29). `Coalition`
and `CanNext` are `preC cgs c (go φ)`, and `preC` forces its target set
only when it reaches a membership test: never on a zero-state CGS, never
at a state where some coalition member has no moves, and never where
some opponent has none. GHCi: `sat zeroCgs (CanNext ["alice"] (Box p))` =
∅. The earlier port evaluated `go φ` first and threw; both clauses now go
through `Gamen.Cgs.preCLazy`. -/
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
  | .not f' =>
      -- `Set.difference states (go f')`: `Data.Set.difference ∅ e = ∅`
      -- *without evaluating* `e` (checked against GHC's `containers`, see the
      -- module docstring's "Laziness" note). `cgs.cgsStates` is plain data
      -- (never itself throws), so this is the one place its emptiness alone
      -- decides whether `f'` is evaluated at all — relevant on a CGS with no
      -- states, which `mkCgs` does not reject.
      if cgs.cgsStates.isEmpty then pure ∅
      else do
        let sf ← sat cgs f'
        pure (cgs.cgsStates \ sf)
  | .and l r => do
      -- `Set.intersection (go l) (go r)`: `Data.Set.intersection ∅ e = ∅`
      -- without evaluating `e`; `go l` (the first/left argument) is always
      -- evaluated first regardless. So `r` is skipped exactly when `l`'s
      -- satisfaction set is empty — e.g. `And Bot (Box p)` = ∅, never
      -- reaching `Box`'s error, even though `Box` is unsupported.
      let sl ← sat cgs l
      if sl.isEmpty then pure ∅
      else do
        let sr ← sat cgs r
        pure (sl ∩ sr)
  | .or l r => do
      -- `Set.union (go l) (go r)`: `Data.Set.union` forces both arguments,
      -- its *second* first (`union t1 Tip = t1` is its first equation), so
      -- there is no short-circuit, but when both sides error GHC reports
      -- `r`'s error (GHCi, 2026-09-29: `sat c (Or (Box p) (Diamond p))` →
      -- the Diamond error).
      let sr ← sat cgs r
      let sl ← sat cgs l
      pure (sl ∪ sr)
  | .implies l r => do
      -- `Set.union (Set.difference states (go l)) (go r)`: `go r` (union's
      -- second argument) is forced first, unconditionally. The antecedent
      -- `Set.difference states (go l)` follows `Not`'s rule: `go l` is
      -- skipped exactly when `states` is empty. Both sides erroring: `r`'s
      -- error (GHCi, 2026-09-29, on a nonempty and a zero-state CGS).
      let sr ← sat cgs r
      let diffPart ← do
        if cgs.cgsStates.isEmpty then pure (∅ : Std.TreeSet s)
        else do
          let sl ← sat cgs l
          pure (cgs.cgsStates \ sl)
      pure (diffPart ∪ sr)
  | .iff l r => do
      -- `Set.union (Set.intersection sl sr) (Set.difference states (Set.union sl sr))`
      -- (`sl`/`sr` shared thunks for `go l`/`go r`). `sl` is always forced
      -- (it is `intersection`'s first argument, and that
      -- `intersection` is itself always eventually forced — either directly,
      -- when the difference/`states` part is empty and `union` returns it
      -- unevaluated to a caller that then demands it, or as part of the
      -- general merge otherwise). When `states` is nonempty, `sr` is *also*
      -- always forced regardless of `sl`, via the difference part's own
      -- `Set.union sl sr` (whose second argument, `sr`, is unconditionally
      -- forced) — so there is no shortcut to replicate in that case. Only
      -- when `states` is empty does `sl`'s emptiness decide whether `sr` is
      -- ever touched, matching `Not`/`Implies`'s antecedent above. All four
      -- shapes (`states` empty or not, crossed with which of `l`/`r` is the
      -- illegal operand) were checked against GHC's `containers` directly.
      -- Order when both sides error (GHCi, 2026-09-29): with `states`
      -- nonempty the outer `union` forces its second argument first, whose
      -- `Set.union sl sr` forces `sr` before `sl`, so `r`'s error wins
      -- (`sat c (Iff (Box p) (Diamond p))` → Diamond); with `states` empty
      -- only `sl` is forced, so `l`'s error.
      if cgs.cgsStates.isEmpty then
        let sl ← sat cgs l
        if sl.isEmpty then pure ∅
        else do
          let sr ← sat cgs r
          pure (sl ∩ sr)
      else do
        let sr ← sat cgs r
        let sl ← sat cgs l
        pure ((sl ∩ sr) ∪ (cgs.cgsStates \ (sl ∪ sr)))

  -- [C]φ ≡ ⟨⟨C⟩⟩Xφ — one-step coalition preimage
  -- (`preCLazy`: `sat cgs f'` is forced only where the lazy `preC`
  -- would force it; see the module docstring.)
  | .coalition c f' => preCLazy cgs (Std.TreeSet.ofList c) (sat cgs f')

  -- ⟨⟨C⟩⟩Xφ — same preimage (AHK 2002, Def. 3(1))
  | .canNext c f' => preCLazy cgs (Std.TreeSet.ofList c) (sat cgs f')

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
