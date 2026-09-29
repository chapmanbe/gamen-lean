import Std.Data.TreeMap
import Std.Data.TreeSet

/-!
# Gamen.Cgs

Port of `gamen-hs/src/Gamen/Cgs.hs`: Concurrent Game Structures (Alur,
Henzinger & Kupferman, "Alternating-Time Temporal Logic", *Journal of the
ACM* 49(5), 2002, §2). A CGS is the semantic foundation for ATL and
Coalition Logic: a multi-player, multi-state transition system where
agents choose actions simultaneously and independently, and the joint
choice determines the successor state.

This module is formula-agnostic — it defines only the model layer.
Satisfaction relations live in `Gamen.Coalition` (Pauly 2002) and
`Gamen.Atl` (AHK 2002), neither ported yet, so this module has no direct
Lean test-suite counterpart in gamen-hs (there is no `test/CgsSpec.hs`);
see `Tests/Main.lean`'s `cgsCases` docstring for how it is tested here.

The AHK 2002 paper is not among the PDFs in `gamen-hs/notes/`, so its
`§2`/`§4` section citations are kept exactly as the Haskell gives them,
unverified against a primary source.

`Agent` is written as `String` directly, not as a fresh `abbrev Agent`:
`Gamen.Agent` already exists (`RankingTheory.lean`), a module this one's
Haskell import list does not depend on — the same choice `DeonticStit.lean`
and `DeonticStit/Sequent.lean` make, and for the same reason (both are in
the shared `Gamen` namespace, so a second `abbrev Agent` would collide).
-/
namespace Gamen

/-- A Concurrent Game Structure (Alur, Henzinger & Kupferman 2002, §2).

`Cgs s a` is parameterised by state type `s` and action type `a`. At each
state every agent independently picks an action from its available move
set; the resulting joint move determines the successor state via
`cgsTransition`.

Informal invariants (not enforced by the type, matching the Haskell):
- `cgsMoves` returns a non-empty set for every (state, agent) pair in the
  domain of `cgsStates × cgsAgents`.
- `cgsTransition` is total on the cross-product of available moves.

Use `mkCgs` to get a check on both invariants. `[Ord s] [Ord a]` replace
the Haskell smart constructor's `(Ord s, Ord a)` constraint: unlike
Haskell's `Data.Set`/`Data.Map`, `Std.TreeSet`/`Std.TreeMap` carry their
comparator as part of the type, so the plain `Cgs` record itself (not just
`mkCgs`) needs the instances wherever its fields mention `Std.TreeSet a`
or `Std.TreeMap String a`. -/
structure Cgs (s a : Type) [Ord s] [Ord a] where
  /-- All states. -/
  cgsStates : Std.TreeSet s
  /-- All agents. -/
  cgsAgents : Std.TreeSet String
  /-- Available moves per (state, agent). -/
  cgsMoves : s → String → Std.TreeSet a
  /-- Joint move → successor state. -/
  cgsTransition : s → Std.TreeMap String a → s
  /-- True propositions at a state. -/
  cgsLabeling : s → Std.TreeSet String

/-- All joint moves of a group of agents at a state: the Cartesian product
of their per-agent move sets, as a list of `Std.TreeMap String a` values,
one assigning an action to each agent in `ags`. Shared by `mkCgs` (closure
check, over the full agent set) and `jointMoves` (over a coalition).

Matches the Haskell fold's list-comprehension order exactly: `mv` (the
newly-chosen agent's action) is the outer loop, `m` (the partial map built
so far) the inner one. -/
private def jointMovesOver {s a : Type} [Ord a]
    (moves : s → String → Std.TreeSet a) (ags : List String) (st : s) :
    List (Std.TreeMap String a) :=
  ags.foldr
    (fun ag acc => (moves st ag).toList.flatMap fun mv => acc.map fun m => m.insert ag mv)
    [(∅ : Std.TreeMap String a)]

/-- Union of two joint moves, biased toward `m1` on a conflicting key —
matching Haskell's `Data.Map.union` (`Map.union m1 m2` keeps `m1`'s entry
on a shared key). `Std.TreeMap.union` is biased the other way (its
*second* argument wins), so this flips the argument order. In the one call
site (`preC`), `m1`/`m2` are moves for a coalition and its complement, so
domains never actually overlap; the bias is kept exact anyway. -/
private def leftBiasedUnion {a : Type} [Ord a]
    (m1 m2 : Std.TreeMap String a) : Std.TreeMap String a :=
  m2.union m1

/-- Construct a `Cgs`, checking two invariants and returning the first
violation as an error, or the `Cgs` itself:

1. no agent has an empty move set at any state; and
2. `cgsTransition` is *closed* — every joint move over all agents at every
   state lands back in `states`.

The closure check matters because the satisfaction relations
(`Gamen.Coalition`, `Gamen.Atl`, `Gamen.Atel`, none ported yet) read an
escaping successor (one outside `states`) as failing every proposition —
i.e. silently as `¬φ` — rather than erroring, so an unchecked CGS with a
dangling transition quietly corrupts model checking (adversarial review
B7, the same review that motivated `Kripke.mkFrame`'s edge check).
Rejecting such structures at construction keeps the successor total on the
reachable state set.

Note: the bare `Cgs` constructor remains available for internal builders
that produce a CGS by transformation (e.g.
`Gamen.Atl.ImperfectInfo.residualCgs`) rather than from
raw data; prefer `mkCgs` for models built from user input, as in the
Haskell. -/
def mkCgs {s a : Type} [Ord s] [Ord a]
    (states : Std.TreeSet s) (agents : Std.TreeSet String)
    (moves : s → String → Std.TreeSet a)
    (trans : s → Std.TreeMap String a → s)
    (label : s → Std.TreeSet String) :
    Except String (Cgs s a) := do
  let emptyMoveViolations :=
    states.toList.flatMap fun st =>
      agents.toList.filterMap fun ag =>
        if (moves st ag).isEmpty then some (st, ag) else none
  match emptyMoveViolations with
  | (st, ag) :: _ =>
      throw ("mkCgs: agent " ++ ag ++ " has no moves at state {"
        ++ String.intercalate " " (label st).toList ++ "}")
  | [] =>
      let escapingTransitions :=
        states.toList.filter fun st =>
          (jointMovesOver moves agents.toList st).any fun jm =>
            !states.contains (trans st jm)
      match escapingTransitions with
      | st :: _ =>
          throw ("mkCgs: a joint move at state {"
            ++ String.intercalate " " (label st).toList
            ++ "} leads to a successor outside the state set "
            ++ "(cgsTransition is not closed)")
      | [] =>
          return { cgsStates := states, cgsAgents := agents, cgsMoves := moves,
                    cgsTransition := trans, cgsLabeling := label }

/-- Available actions for `ag` at `st`. -/
def availableMoves {s a : Type} [Ord s] [Ord a] (cgs : Cgs s a) :
    s → String → Std.TreeSet a :=
  cgs.cgsMoves

/-- All joint moves available to a set of agents (a coalition) at `st`.

Returns the Cartesian product of per-agent move sets as a list of
`Std.TreeMap String a` values — each map assigns one action to each agent
in the coalition. -/
def jointMoves {s a : Type} [Ord s] [Ord a]
    (cgs : Cgs s a) (coalition : Std.TreeSet String) (st : s) :
    List (Std.TreeMap String a) :=
  jointMovesOver cgs.cgsMoves coalition.toList st

/-- Apply a full joint move at `st`. The caller must supply an entry for
every agent in `cgsAgents`. -/
def applyJointMove {s a : Type} [Ord s] [Ord a] (cgs : Cgs s a) :
    s → Std.TreeMap String a → s :=
  cgs.cgsTransition

/-- Pre-image of `x` under coalition `c` (AHK 2002, §4).

`preC cgs c x` is the set of states from which `c` can force the next
state into `x` regardless of what the opposing agents do:

`preC c x = { s | ∃ joint move m_c for c. ∀ completions m_(Ag∖c) by
non-c agents. transition(s, m_c ∪ m_(Ag∖c)) ∈ x }`

This is the fundamental operation used by both Coalition Logic
satisfaction and the ATL fixpoint algorithm. -/
def preC {s a : Type} [Ord s] [Ord a]
    (cgs : Cgs s a) (coalition : Std.TreeSet String) (x : Std.TreeSet s) :
    Std.TreeSet s :=
  let opponents := cgs.cgsAgents \ coalition
  cgs.cgsStates.filter fun st =>
    (jointMoves cgs coalition st).any fun coMove =>
      (jointMoves cgs opponents st).all fun oppMove =>
        x.contains (cgs.cgsTransition st (leftBiasedUnion coMove oppMove))

/-- `preC` with a target set that is not yet evaluated and may be an error.
Not in gamen-hs as a separate function: it reproduces the lazy Haskell
`preC`, which forces `x` only on reaching a membership test. So `x`'s error
is raised only if some state has a coalition joint move and, for it, an
opponent joint move. It is never raised on a zero-state CGS, nor when a
coalition member (or an opponent) has no moves anywhere. On `.ok x` it
equals `preC cgs coalition x`. Used by `Gamen.Atl.ModelCheck.sat`,
`Gamen.Atel.atelSat`, and `Gamen.Atl.ImperfectInfo`. -/
def preCLazy {s a : Type} [Ord s] [Ord a]
    (cgs : Cgs s a) (coalition : Std.TreeSet String) (x : Except String (Std.TreeSet s)) :
    Except String (Std.TreeSet s) := do
  let opponents := cgs.cgsAgents \ coalition
  let kept ← cgs.cgsStates.toList.filterM fun st =>
    (jointMoves cgs coalition st).anyM fun coMove =>
      (jointMoves cgs opponents st).allM fun oppMove => do
        let xs ← x
        pure (xs.contains (cgs.cgsTransition st (leftBiasedUnion coMove oppMove)))
  pure (Std.TreeSet.ofList kept)

end Gamen
