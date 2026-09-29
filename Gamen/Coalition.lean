import Std.Data.TreeMap
import Std.Data.TreeSet
import Gamen.Cgs
import Gamen.Formula

/-!
# Gamen.Coalition

Port of `gamen-hs/src/Gamen/Coalition.hs`: Coalition Logic (Pauly 2002)
over Concurrent Game Structures.

The core modality is `[C]φ`: coalition `C` has a joint action that
guarantees `φ` holds at the next state, regardless of what the opposing
agents do. This is the one-step fragment of ATL (no temporal fixpoints);
`Gamen.Atl`/`Gamen.Atl.ModelCheck` add the temporal operators.

References:
  Pauly (2001), *Logic for Social Software*, ILLC DS-2001-10.
  Pauly (2002), *A Modal Logic for Coalitional Power in Games*, Journal of
  Logic and Computation 12(1): 149–166.
Neither paper is among the PDFs in `gamen-hs/notes/` (only a correspondence
note, `notes/pauly2002-correspondence.md`, which is itself derived from the
Haskell, not the paper); page numbers below are kept exactly as the
Haskell gives them, unverified against a primary source (`Gamen.Cgs`'s
docstring makes the same point about its own AHK 2002 citations).

Both `error` sites in the Haskell (`coalSatisfies`'s world-existence guard,
mirroring `Gamen.Atl`/`Gamen.Laca`'s gamen-hs#7-style guard; and its
seventeen unsupported-operator `error` calls, everything outside the
Coalition Logic/propositional fragment) become `Except`, Haskell wording
kept verbatim, never a `panic!`/default — matching `Gamen.Laca`'s and
`Gamen.Atl.ModelCheck`'s precedent for the identical pattern. `coalIsTrueIn`
and the frame-axiom checks call `coalSatisfies`/`preC` and so also return
`Except`/stay pure as their Haskell signatures require. -/
namespace Gamen

/-- `M, s ⊩ φ` — Coalition Logic satisfaction at state `s` (Pauly 2002,
Definition 3.1).

Errors if `s` is not in `cgsStates` — without this guard, unseen states
silently satisfy all negative formulas (the same gamen-hs#7-style guard as
`Gamen.Laca.lSatisfies`/`Gamen.Stit.sSatisfies`/`Gamen.Atl.atlSatisfies`).

The propositional valuation is drawn from `cgsLabeling`: an atom `p` holds
at `s` iff `p ∈ cgsLabeling cgs s`.

The key case:

> M, s ⊩ [C]φ  iff  ∃ joint move m_C for C at s.
> >               ∀ completions m_(Ag∖C) by opposing agents.
> >               M, transition(s, m_C ∪ m_(Ag∖C)) ⊩ φ

This is equivalent to `s ∈ preC cgs C (sat cgs φ)` (`Gamen.Atl.ModelCheck`)
but avoids materialising the full satisfaction set, exactly as the
Haskell. `any`/`all` become `anyM`/`allM` so that an error from a
recursive `coalSatisfies` call propagates instead of being silently
skipped by a short-circuiting `any`/`all` that never forces it — matching
the Haskell's behavior under laziness (a `True` found before a would-error
branch is reached never forces that branch either). -/
def coalSatisfies {s a : Type} [Ord s] [Ord a] (cgs : Cgs s a) (st : s) :
    Formula → Except String Bool := fun f => do
  unless cgs.cgsStates.contains st do
    throw "coalSatisfies: state is not in cgsStates"
  match f with
  -- Propositional.
  | .bot => return false
  | .atomF atm => return (cgs.cgsLabeling st).contains atm.name
  | .not f' => return !(← coalSatisfies cgs st f')
  | .and l r => if !(← coalSatisfies cgs st l) then return false else coalSatisfies cgs st r
  | .or l r => if (← coalSatisfies cgs st l) then return true else coalSatisfies cgs st r
  | .implies l r =>
      if !(← coalSatisfies cgs st l) then return true else coalSatisfies cgs st r
  | .iff l r => return (← coalSatisfies cgs st l) == (← coalSatisfies cgs st r)
  -- [C]φ — coalition C can force φ in one step (Pauly 2002, Definition 3.1).
  -- `oppMove.union coMove` is the asymmetric union `Gamen.Cgs.preC` uses
  -- internally (its `leftBiasedUnion`, private to that module): on a
  -- shared key `coMove`'s entry wins, matching Haskell's
  -- `Map.union coMove oppMove` (`Data.Map.union` keeps its first
  -- argument's entry). In the one call here, `coMove`/`oppMove` are moves
  -- for a coalition and its complement, so domains never actually overlap.
  | .coalition agents phi =>
      let coalition := Std.TreeSet.ofList agents
      let opponents := cgs.cgsAgents \ coalition
      (jointMoves cgs coalition st).anyM fun coMove =>
        (jointMoves cgs opponents st).allM fun oppMove =>
          coalSatisfies cgs (cgs.cgsTransition st (oppMove.union coMove)) phi
  -- Operators not supported in Coalition Logic.
  | .box _ => throw "Box not supported in Coalition Logic; [Ag]φ encodes universal effectivity"
  | .diamond _ => throw "Diamond not supported in Coalition Logic"
  | .futureBox _ => throw "Temporal operators require ATL (use Gamen.Atl)"
  | .futureDiamond _ => throw "Temporal operators require ATL (use Gamen.Atl)"
  | .pastBox _ => throw "Past operators not supported in Coalition Logic"
  | .pastDiamond _ => throw "Past operators not supported in Coalition Logic"
  | .since _ _ => throw "Since not supported in Coalition Logic"
  | .until _ _ => throw "Until not supported in Coalition Logic"
  | .knowledge _ _ => throw "Knowledge requires an epistemic model (use Gamen.Atel)"
  | .belief _ _ => throw "Belief not supported in Coalition Logic"
  | .rankedBelief _ _ _ => throw "RankedBelief not supported in Coalition Logic"
  | .announce _ _ => throw "Announce not supported in Coalition Logic"
  | .stit _ _ => throw "Stit requires a STIT model (use Gamen.Stit or Gamen.Laca)"
  | .choiceDiamond _ _ => throw "ChoiceDiamond requires a STIT model"
  | .groupStit _ => throw "GroupStit requires a STIT model"
  | .next _ => throw "Next requires a Laca model (use Gamen.Laca)"
  | .ought _ _ => throw "Ought requires a deontic model (use Gamen.DeonticStit)"
  | .permitted _ _ => throw "Permitted requires a deontic model (use Gamen.DeonticStit)"
  | .canNext _ _ => throw "CanNext requires ATL model checking (use Gamen.Atl)"
  | .canAlways _ _ => throw "CanAlways requires ATL model checking (use Gamen.Atl)"
  | .canEventually _ _ => throw "CanEventually requires ATL model checking (use Gamen.Atl)"
  | .canUntil _ _ _ => throw "CanUntil requires ATL model checking (use Gamen.Atl)"

/-- A formula is true in a CGS if it holds at every state. -/
def coalIsTrueIn {s a : Type} [Ord s] [Ord a] (cgs : Cgs s a) (f : Formula) :
    Except String Bool :=
  cgs.cgsStates.toList.allM fun st => coalSatisfies cgs st f

-- ── Frame axiom checks (Pauly 2002, Theorem 3.2) ─────────────────────────

/-- N — ⊤-effectivity: the grand coalition can always force ⊤.

`preC cgs Ag S = S` for any non-empty model. Equivalently, `[Ag]⊤` holds
at every state. -/
def checkTopEffectivity {s a : Type} [Ord s] [Ord a] [BEq s] (cgs : Cgs s a) : Bool :=
  preC cgs cgs.cgsAgents cgs.cgsStates == cgs.cgsStates

/-- ⊥-monotonicity: the empty coalition cannot force ⊥.

`preC cgs ∅ ∅ = ∅`: since every state has at least one joint move
(guaranteed by `mkCgs`), no state can ensure that all successors land in
the empty set. -/
def checkBotMonotonicity {s a : Type} [Ord s] [Ord a] (cgs : Cgs s a) : Bool :=
  (preC cgs ∅ ∅).isEmpty

/-- Monotonicity: if `C` can force `x`, it can force any superset.

`preC cgs c x ⊆ preC cgs c (x ∪ y)` for all `x, y ⊆ cgsStates`. -/
def checkMonotonicity {s a : Type} [Ord s] [Ord a]
    (cgs : Cgs s a) (coalition : Std.TreeSet String) (x y : Std.TreeSet s) : Bool :=
  let lhs := preC cgs coalition x
  let rhs := preC cgs coalition (x ∪ y)
  lhs.all fun st => rhs.contains st

/-- Superadditivity: disjoint coalitions can combine their guarantees.

If `C ∩ D = ∅`, then `preC C x ∩ preC D y ⊆ preC (C ∪ D) (x ∩ y)`. This is
the key structural property distinguishing Coalition Logic from plain
modal logic (Pauly 2002, Theorem 3.2 item 4). -/
def checkSuperadditivity {s a : Type} [Ord s] [Ord a]
    (cgs : Cgs s a) (c d : Std.TreeSet String) (x y : Std.TreeSet s) : Bool :=
  if !(c ∩ d).isEmpty then
    true  -- vacuously true when C∩D≠∅
  else
    let combined := preC cgs c x ∩ preC cgs d y
    let target := preC cgs (c ∪ d) (x ∩ y)
    combined.all fun st => target.contains st

end Gamen
