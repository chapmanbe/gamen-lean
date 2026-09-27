import Std.Data.TreeMap
import Gamen.Formula

/-!
# Gamen.Kripke

Port of `gamen-hs/src/Gamen/Kripke.hs` (B&D Definition 1.6):
Kripke frames and models over string-named worlds.
-/
namespace Gamen

abbrev World := String

/-- The ⟨W, R⟩ part of a model (B&D Definition 1.6; frames proper are
Chapter 2): a set of worlds plus an accessibility relation, stored as a
successor map. -/
structure Frame where
  worlds : Std.TreeSet World
  relation : Std.TreeMap World (Std.TreeSet World)
  deriving Inhabited

/-- B&D Definition 1.6: a model ⟨W, R, V⟩ is a frame plus a valuation. -/
structure Model where
  frame : Frame
  valuation : Std.TreeMap Atom (Std.TreeSet World)
  deriving Inhabited

/-- As Haskell's `deriving Show` on `Frame`/`Model` (`Gamen/Kripke.hs`
~30–44): printed as the underlying association lists, for Plausible
counterexamples (`Tests/Main.lean`'s `Properties (Plausible)` block). -/
instance : Repr Frame where
  reprPrec fr n := reprPrec
    (fr.worlds.toList, fr.relation.toList.map fun (w, vs) => (w, vs.toList)) n

instance : Repr Model where
  reprPrec m n := reprPrec
    (m.frame, m.valuation.toList.map fun (a, vs) => (a, vs.toList)) n

/-- Worlds accessible from `w`. -/
def Frame.accessible (fr : Frame) (w : World) : Std.TreeSet World :=
  fr.relation.getD w ∅

/-- Build a frame from world names and edges. Haskell calls `error` on an
edge whose endpoint is outside the world set; here that is an `Except`. -/
def mkFrame (ws : List World) (rels : List (World × World)) : Except String Frame := do
  let worldSet := Std.TreeSet.ofList ws
  for (src, dst) in rels do
    unless worldSet.contains src && worldSet.contains dst do
      throw s!"mkFrame: edge ({src} -> {dst}) has an endpoint outside the world set"
  let relation := rels.foldl
    (fun m (src, dst) => m.insert src ((m.getD src ∅).insert dst)) ∅
  return { worlds := worldSet, relation }

/-- Build a model from a frame and `(atomName, worlds)` pairs. -/
def mkModel (fr : Frame) (vals : List (String × List World)) : Model :=
  { frame := fr
    valuation := Std.TreeMap.ofList
      (vals.map fun (n, ws) => ((⟨n⟩ : Atom), Std.TreeSet.ofList ws)) }

-- --------------------------------------------------------------------
-- Relation utilities (shared across STIT modules)
-- --------------------------------------------------------------------
--
-- Ported per `docs/assessment/lean-library-reuse-2026-09-23.md` §2:
-- gamen-hs writes the reflexive/symmetric/transitive checks four times
-- (`FrameProperties.hs`, `Kripke.hs`'s `isEquivalenceOn`,
-- `Stit.hs:335`'s `isTransitiveOn`, `Temporal.hs:165`'s
-- `isTransitiveFrame`). Here there is one copy of each, on the raw
-- `(worlds, successor map)` pair that both `Frame` and those other
-- modules' frame-like records carry; `FrameProperties.isReflexive` and
-- friends are one-line wrappers over `fr.worlds`/`fr.relation`, and the
-- other modules' functions will wrap these the same way when ported.

/-- `s` is a subset of `t`. `Std.TreeSet` has no `isSubsetOf`; this is
Haskell's `Set.isSubsetOf` written out by hand. Shared by `Kripke` and
`FrameProperties` (moved here per the assessment note above). -/
def subsetOf (s t : Std.TreeSet World) : Bool :=
  s.all fun w => t.contains w

/-- The relation `rel` is reflexive on `ws`: every `w ∈ ws` accesses
itself. The `Frame`-level version is `FrameProperties.isReflexive`. -/
def reflexiveOn (ws : Std.TreeSet World) (rel : Std.TreeMap World (Std.TreeSet World)) : Bool :=
  ws.all fun w => (rel.getD w ∅).contains w

/-- The relation `rel` is symmetric on `ws`. The `Frame`-level version is
`FrameProperties.isSymmetric`. -/
def symmetricOn (ws : Std.TreeSet World) (rel : Std.TreeMap World (Std.TreeSet World)) : Bool :=
  ws.all fun w => (rel.getD w ∅).all fun v => (rel.getD v ∅).contains w

/-- The relation `rel` is transitive on `ws`. The `Frame`-level version
is `FrameProperties.isTransitive`. -/
def transitiveOn (ws : Std.TreeSet World) (rel : Std.TreeMap World (Std.TreeSet World)) : Bool :=
  ws.all fun w => (rel.getD w ∅).all fun v => subsetOf (rel.getD v ∅) (rel.getD w ∅)

/-- Check whether a relation is an equivalence relation over a set of
worlds (reflexive, symmetric, transitive).

Used by Stit, DeonticStit, and Xstit frame condition checkers. -/
def isEquivalenceOn (ws : Std.TreeSet World) (rel : Std.TreeMap World (Std.TreeSet World)) : Bool :=
  reflexiveOn ws rel && symmetricOn ws rel && transitiveOn ws rel

/-- Compute equivalence classes from a relation.

Each world is placed in the class `{w} ∪ R(w)`. Forcing `w` into its own
class fixes two bugs on relations that are not perfectly reflexive
(adversarial review B7, gamen-hs issue #18): a world with `w ∉ R(w)` was
dropped from its own class, and a world with `R(w) = ∅` produced a
spurious empty class. For a genuine equivalence relation `R(w)` already
contains `w`, so this is a no-op and the partition is unchanged.

Not equivalence closure: on a relation that is not itself an equivalence
relation, the classes `{w} ∪ R(w)` can overlap (`RegressionIssue18.hs:337`
pins this as the intended B7 behavior). The result is in reverse
discovery order (Haskell builds it as `cls : acc` while discovering
worlds in ascending order); callers that iterate over the classes
(`Stit.hs:247`, `Xstit.hs:308`) can have that order leak through, so it
is preserved here rather than sorted. -/
def equivalenceClasses (ws : Std.TreeSet World) (rel : Std.TreeMap World (Std.TreeSet World)) :
    List (Std.TreeSet World) :=
  go ws.toList ∅ []
where
  go : List World → Std.TreeSet World → List (Std.TreeSet World) → List (Std.TreeSet World)
    | [], _, acc => acc
    | w :: rest, seen, acc =>
        if seen.contains w then
          go rest seen acc
        else
          let cls := (rel.getD w ∅).insert w
          go rest (seen.union cls) (cls :: acc)

/-- All ways of choosing one element from each list in order, matching
Haskell's `sequence :: [[a]] -> [[a]]` for the list monad exactly
(the *last* list varies fastest): `sections [[1,2],[3,4]] =
[[1,3],[1,4],[2,3],[2,4]]`. Batteries' `List.sections` enumerates in a
different order (assessment §2); this 4-line local definition keeps the
Haskell order instead of adding the dependency. Shared with
`Tests/PropertyHelpers.lean`'s `genDSModel`; `checkIndependence` below
used to build its search space this way but now searches depth-first
instead (see its docstring). -/
def sections {α : Type} : List (List α) → List (List α)
  | [] => [[]]
  | xs :: rest =>
      let tails := sections rest
      xs.flatMap fun x => tails.map fun t => x :: t

/-- Check independence of agents within a single moment.

For any selection of one choice cell per agent, the intersection must be
non-empty. The first argument is a function returning an agent's choice
cell at a given world.

Haskell's `all` walks a lazily-built `sequence` and stops at the first
combination whose intersection is empty, but never prunes *within* a
combination: each one it does look at still folds all of its cells before
`all` can move on. An earlier Lean version built the entire `sections`
list before checking any combination — the exact laziness this module's
`sections` was written to avoid, since `sections` itself is strict. This
version instead searches depth-first, one agent at a time, carrying the
intersection of the cells chosen so far: once that running intersection is
empty, no cell chosen for a later agent can grow it back, so the whole
branch is pruned without visiting the remaining agents at all. Same
Boolean result on every input as the `sections`-based version (checked by
the "checkIndependence agrees with the sections-based search" property in
`Tests/Main.lean`), not necessarily the same combination Haskell's laziness
would have stopped on. -/
def checkIndependence {agent : Type} (choiceCell : agent → World → Std.TreeSet World)
    (agents : List agent) (mom : Std.TreeSet World) : Bool :=
  go agents none
where
  cellsFor (a : agent) : List (Std.TreeSet World) :=
    (mom.toList.map (choiceCell a)).eraseDupsBy (fun s t => s.toList == t.toList)
  go : List agent → Option (Std.TreeSet World) → Bool
    | [], _ => true
    | a :: rest, acc =>
        (cellsFor a).all fun cell =>
          let acc' : Std.TreeSet World := acc.elim cell (· ∩ cell)
          !acc'.isEmpty && go rest (some acc')

-- --------------------------------------------------------------------
-- Shared fixpoint iteration, with fuel
-- --------------------------------------------------------------------
-- gamen-hs iterates "until nothing changes" in six places (`lfp`, `gfp`,
-- `transitiveClose`, `euclideanClose`, `largestBisimulation`,
-- `Laca.trajectory`), none of them bounded. The Lean ports go through
-- this one helper instead.

/-- Iterate `step` from `x` until `step y == y`, returning that `y`: the
Haskell `go r = let r' = step r in if r' == r then r else go r'` loop.
`fuel` counts calls to `step`; each caller documents why its fuel suffices
(`|U| + 1` for monotone iteration in a finite universe `U`, `|W|² + 1` for
relation closures over `W`). Running out of fuel is an error naming
`what`, never a default answer. -/
def iterateToFixpoint {α : Type} [BEq α] (what : String) (step : α → α) :
    Nat → α → Except String α
  | 0, _ => throw s!"{what}: no fixpoint within the fuel bound"
  | fuel + 1, x =>
    let x' := step x
    if x' == x then pure x else iterateToFixpoint what step fuel x'

end Gamen
