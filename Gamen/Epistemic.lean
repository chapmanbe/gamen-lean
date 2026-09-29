import Std.Data.TreeMap
import Gamen.Formula
import Gamen.Kripke

/-!
# Gamen.Epistemic

Port of `gamen-hs/src/Gamen/Epistemic.hs`: multi-agent epistemic models
with per-agent accessibility relations, public announcement semantics,
group/common knowledge, and bisimulation. B&D Chapter 15, "Epistemic
Logics" (`notes/bd-screen.pdf`, Fall 2025 edition, pp. 190–203).

The Haskell cites "Chapter 13, B&D Fall 2019" and Definitions 13.3, 13.4,
13.5, 13.7, and 13.11. In the PDF in `notes/` Chapter 13 is conditional
logic (sphere models); the epistemic definitions are Chapter 15, and
every number below is checked against it: language and formulas are
Definitions 15.1–15.2 (p. 191), group knowledge E and common knowledge C
are Definition 15.3 (p. 192), models are Definition 15.4 (p. 193), truth
is Definition 15.5 (p. 194), common knowledge's semantics is Definition
15.6 (p. 196, with R_G defined as the transitive closure just above it),
bisimulation is Definition 15.7 and Theorem 15.8 (p. 198), and public
announcement truth and the restricted model M|B are Definition 15.11
(p. 201). The Haskell's "BdRV §1.4" (Blackburn, de Rijke & Venema) is not
in `notes/` and is left unverified. `Agent` is written as `String`
directly, as in `Gamen.Stit`/`Gamen.Xstit` (`Gamen.Agent` already exists
in `RankingTheory.lean`).

Every Haskell `error` becomes an `Except`: `eAccessible`'s and
`eDoxasticAccessible`'s unknown agent, and `eSatisfies`'s world guard and
its twenty unsupported operators (the Haskell wording is kept verbatim).
Everything built on them (`eIsTrueIn`, `restrictModel`, `groupKnows`,
`commonKnowledge`, `isBisimulation`, `largestBisimulation`,
`bisimilarWorlds`) returns `Except` in turn.

Laziness (CLAUDE.md, "Laziness"): the Haskell `eSatisfies` builds a
per-announcement-body table of restricted models (`restrictions`,
`Epistemic.hs` ~148–158) whose entries are thunks, so a restriction runs
only when its `[B]C` is actually reached. This port does not build the
table: it restricts the model on demand when `[B]C` is reached and `B`
holds at `w`, which gives the same results and the same errors (`p ∧ [B]C`
with `p` false never evaluates `B` anywhere). The Haskell's
`announcementBodies` helper exists only to key that table and has no
counterpart here. No cache is added; none of the tests need one.

Not reachable from `gamen-validate` (gamen-hs's `validate/Main.hs` does
not import `Gamen.Epistemic`), so `tools/compare/compare.py` cannot check
this port; it rests on `Tests/Main.lean`'s `epistemicCases`,
`epistemicPaperCorrespondenceCases`, `epistemicRegressionCases`, the two
`Gamen.Epistemic` properties, and the Doxastic PaperCorrespondence cases.
-/
namespace Gamen

-- Bisimulations are sets of world pairs (`Set (World, World)` in the
-- Haskell); see the same note in `Tableau.lean`.
attribute [local instance] lexOrd

-- --------------------------------------------------------------------
-- Epistemic frames and models (B&D Definition 15.4, p. 193)
-- --------------------------------------------------------------------

/-- A multi-agent epistemic frame with per-agent accessibility relations
(the ⟨W, {R_a}⟩ part of B&D Definition 15.4, p. 193).

`eRelations` are the epistemic (knowledge) relations, conventionally S5
equivalence relations (reflexive, symmetric, transitive — making knowledge
factive).

`eDoxastic` are the doxastic (belief) relations, conventionally KD45
(serial, transitive, euclidean — non-factive). Belief is non-factive so
the relations are typically *not* reflexive: an agent can believe
something false. Empty by default; populate only if `belief` operators
are in use. -/
structure EpistemicFrame where
  eWorlds : Std.TreeSet World
  eRelations : Std.TreeMap String (Std.TreeMap World (Std.TreeSet World))
  eDoxastic : Std.TreeMap String (Std.TreeMap World (Std.TreeSet World))
  deriving Inhabited

/-- A multi-agent epistemic model M = ⟨W, {R_a}, V⟩ (B&D Definition 15.4,
p. 193). -/
structure EpistemicModel where
  eFrame : EpistemicFrame
  eValuation : Std.TreeMap Atom (Std.TreeSet World)
  deriving Inhabited

private def reprRels (rels : Std.TreeMap String (Std.TreeMap World (Std.TreeSet World))) :
    List (String × List (World × List World)) :=
  rels.toList.map fun (a, rel) => (a, rel.toList.map fun (w, vs) => (w, vs.toList))

/-- As Haskell's `deriving Show`: printed as the underlying association
lists, for Plausible counterexamples (`Tests/Main.lean`'s `Gamen.Epistemic`
properties). -/
instance : Repr EpistemicFrame where
  reprPrec fr n := reprPrec
    (fr.eWorlds.toList, reprRels fr.eRelations, reprRels fr.eDoxastic) n

instance : Repr EpistemicModel where
  reprPrec m n := reprPrec
    (m.eFrame, m.eValuation.toList.map fun (a, vs) => (a, vs.toList)) n

/-- Haskell's `relMap`: `(agent, edges)` pairs into per-agent successor
maps (`Map.fromListWith Set.union`, so repeated sources merge). -/
private def relMap (rels : List (String × List (World × World))) :
    Std.TreeMap String (Std.TreeMap World (Std.TreeSet World)) :=
  Std.TreeMap.ofList (rels.map fun (agent, pairs) => (agent, buildRel pairs))
where
  buildRel (pairs : List (World × World)) : Std.TreeMap World (Std.TreeSet World) :=
    pairs.foldl (fun m (src, dst) => m.insert src ((m.getD src ∅).insert dst)) ∅

/-- Construct an epistemic frame with both knowledge and belief relations.
Belief relations are conventionally KD45 (serial, transitive, euclidean —
*not* reflexive, since belief is non-factive). Like the Haskell, no check
that edge endpoints lie in `ws` (compare `mkFrame`). -/
def mkEpistemicFrameWithBelief (ws : List World)
    (agentRels : List (String × List (World × World)))   -- knowledge (S5)
    (doxRels : List (String × List (World × World)))     -- belief (KD45)
    : EpistemicFrame :=
  { eWorlds := Std.TreeSet.ofList ws
    eRelations := relMap agentRels
    eDoxastic := relMap doxRels }

/-- Construct an epistemic frame from worlds and per-agent knowledge
relation pairs. Doxastic (belief) relations are empty; use
`mkEpistemicFrameWithBelief` if you need `belief` operators. -/
def mkEpistemicFrame (ws : List World) (agentRels : List (String × List (World × World))) :
    EpistemicFrame :=
  mkEpistemicFrameWithBelief ws agentRels []

/-- Construct an epistemic model from a frame and valuation pairs. Takes
`String`-keyed input for ergonomic call sites; internally wraps each name
as an `Atom`. -/
def mkEpistemicModel (fr : EpistemicFrame) (vals : List (String × List World)) : EpistemicModel :=
  { eFrame := fr
    eValuation := Std.TreeMap.ofList
      (vals.map fun (n, ws) => ((⟨n⟩ : Atom), Std.TreeSet.ofList ws)) }

/-- The set of agents in a frame (the keys of its knowledge relations). -/
def agents (fr : EpistemicFrame) : Std.TreeSet String :=
  Std.TreeSet.ofList fr.eRelations.keys

/-- Worlds knowledge-accessible by agent from world.

Errors on an agent with no knowledge relation in the frame rather than
returning the empty set: an unknown agent must not make `K_a φ`
vacuously true (adversarial review B1, same failure mode the world
guard already closed — gamen-hs#7). -/
def eAccessible (fr : EpistemicFrame) (agent : String) (w : World) :
    Except String (Std.TreeSet World) :=
  match fr.eRelations.get? agent with
  | none => throw s!"eAccessible: agent {repr agent} is not in model"
  | some rel => pure (rel.getD w ∅)

/-- Worlds doxastically (belief-)accessible by agent from world.

Errors on an agent with no doxastic relation rather than returning the
empty set (which would make `B_a φ` vacuously true, review B1). Note
this means evaluating `belief` on a knowledge-only frame (built by
`mkEpistemicFrame`, whose doxastic map is empty) errors — use
`mkEpistemicFrameWithBelief` to supply belief relations. -/
def eDoxasticAccessible (fr : EpistemicFrame) (agent : String) (w : World) :
    Except String (Std.TreeSet World) :=
  match fr.eDoxastic.get? agent with
  | none => throw s!"eDoxasticAccessible: agent {repr agent} has no belief relation in model"
  | some rel => pure (rel.getD w ∅)

-- --------------------------------------------------------------------
-- Model restriction (B&D Definition 15.11, p. 201)
-- --------------------------------------------------------------------

/-- `R'_a = R_a ∩ (W' × W')`, written as the Haskell's `Map.mapWithKey`:
a source outside `W'` keeps its key but loses all its successors. -/
private def restrictRels (wPrime : Std.TreeSet World)
    (rels : Std.TreeMap String (Std.TreeMap World (Std.TreeSet World))) :
    Std.TreeMap String (Std.TreeMap World (Std.TreeSet World)) :=
  Std.TreeMap.ofList (rels.toList.map fun (agent, rel) =>
    (agent, Std.TreeMap.ofList (rel.toList.map fun (u, succs) =>
      (u, if wPrime.contains u then succs.filter wPrime.contains else ∅))))

/-- The body of `restrictModel` once the surviving worlds `W'` are known:
`R'_a = R_a ∩ (W' × W')` for every knowledge and belief relation, and
`V'(p) = V(p) ∩ W'`. Shared by `restrictModel` and `eSatisfies`'s
announcement clause (the latter cannot call the former, which is
defined in terms of it). -/
def restrictWorlds (m : EpistemicModel) (wPrime : Std.TreeSet World) : EpistemicModel :=
  { eFrame :=
      { eWorlds := wPrime
        eRelations := restrictRels wPrime m.eFrame.eRelations
        eDoxastic := restrictRels wPrime m.eFrame.eDoxastic }
    eValuation := Std.TreeMap.ofList
      (m.eValuation.toList.map fun (a, ws) => (a, ws.filter wPrime.contains)) }

-- --------------------------------------------------------------------
-- Semantics (B&D Definitions 15.5, p. 194, and 15.11, p. 201)
-- --------------------------------------------------------------------

/-- M, w ⊩ A for epistemic models (B&D Definition 15.5, p. 194, extended
by Definition 15.11, p. 201, for `[B]C`). Gives meaning to the
propositional connectives, `knowledge`, `belief`, and `announce`; every
other operator is an error with the Haskell's wording, never a default
truth value — plain `box`/`diamond` because a multi-agent model has no
single accessibility relation, the rest because the model has nothing to
evaluate them against.

Errors if `w` is not in `eWorlds (eFrame m)` — without this guard,
non-existent worlds yield vacuously-true results for negative, universal,
and modal formulas (gamen-hs#7, mirroring gamen-hs#3). The guard applies
at every recursive call, so a relation edge leading outside the model
errors when `K_a`/`B_a` follows it, as in the Haskell.

`[B]C` is true at `w` iff (M, w ⊩ B) implies (M|B, w ⊩ C). The restricted
model is built here, on demand, only when `B` holds at `w` (see the module
docstring on the Haskell's lazy table); building it evaluates `B` at every
world of `M` in ascending order and raises the first error met. Haskell's
`restrictModel` errors in exactly the same situations, but its `Set.filter`
does not fix which world is evaluated first, so when two worlds error with
different messages the message raised may differ. -/
def eSatisfies (m : EpistemicModel) (w : World) (f : Formula) : Except String Bool := do
  unless m.eFrame.eWorlds.contains w do
    throw s!"eSatisfies: world {repr w} is not in model"
  match f with
  | .bot => return false
  | .atomF a => return (m.eValuation.getD a ∅).contains w
  | .not g => return !(← eSatisfies m w g)
  -- Short-circuiting, matching Haskell's lazy `&&`/`||`: the right side
  -- is only evaluated (and so can only error) when the left side's value
  -- doesn't already settle the result.
  | .and l r => if !(← eSatisfies m w l) then return false else eSatisfies m w r
  | .or l r => if (← eSatisfies m w l) then return true else eSatisfies m w r
  | .implies l r => if !(← eSatisfies m w l) then return true else eSatisfies m w r
  | .iff l r => return (← eSatisfies m w l) == (← eSatisfies m w r)
  -- □A: not meaningful in multi-agent epistemic models. Error for clarity.
  | .box _ => throw "Box operator not supported in epistemic models; use Knowledge"
  | .diamond _ => throw "Diamond operator not supported in epistemic models; use Knowledge"
  -- Temporal operators: not applicable to epistemic models
  | .futureBox _ => throw "FutureBox not supported in epistemic models"
  | .futureDiamond _ => throw "FutureDiamond not supported in epistemic models"
  | .pastBox _ => throw "PastBox not supported in epistemic models"
  | .pastDiamond _ => throw "PastDiamond not supported in epistemic models"
  | .since _ _ => throw "Since not supported in epistemic models"
  | .until _ _ => throw "Until not supported in epistemic models"
  | .stit _ _ => throw "Stit not supported in epistemic models; use Gamen.Stit"
  | .choiceDiamond _ _ =>
      throw "ChoiceDiamond not supported in epistemic models; use Gamen.Stit or Gamen.DeonticStit"
  | .groupStit _ => throw "GroupStit not supported in epistemic models; use Gamen.Stit"
  | .next _ => throw "Next not supported in epistemic models; use Gamen.Laca"
  | .ought _ _ => throw "Ought not supported in epistemic models; use Gamen.DeonticStit"
  | .permitted _ _ => throw "Permitted not supported in epistemic models; use Gamen.DeonticStit"
  | .rankedBelief _ _ _ =>
      throw "RankedBelief not supported in epistemic models; use Gamen.RankingTheory"
  | .coalition _ _ =>
      throw "Coalition not supported in epistemic models; use Gamen.Cgs/Gamen.Coalition"
  | .canNext _ _ => throw "CanNext not supported in epistemic models; use Gamen.Atl"
  | .canAlways _ _ => throw "CanAlways not supported in epistemic models; use Gamen.Atl"
  | .canEventually _ _ => throw "CanEventually not supported in epistemic models; use Gamen.Atl"
  | .canUntil _ _ _ => throw "CanUntil not supported in epistemic models; use Gamen.Atl"
  -- K_a B: true at w iff B holds at all R_a-successors of w
  | .knowledge agent g => do
      let succs ← eAccessible m.eFrame agent w
      succs.toList.allM (eSatisfies m · g)
  -- B_a B: true at w iff B holds at all doxastic-R_a-successors of w
  -- (KD45 — non-factive; uses the doxastic accessibility relation)
  | .belief agent g => do
      let succs ← eDoxasticAccessible m.eFrame agent w
      succs.toList.allM (eSatisfies m · g)
  -- [B]C: true at w iff (M,w ⊩ B) implies (M|B, w ⊩ C).
  | .announce b c => do
      if !(← eSatisfies m w b) then return true  -- vacuously true
      let wPrime ← m.eFrame.eWorlds.toList.filterM (eSatisfies m · b)
      eSatisfies (restrictWorlds m (Std.TreeSet.ofList wPrime)) w c

/-- A formula is true in an epistemic model if it holds at every world. -/
def eIsTrueIn (m : EpistemicModel) (f : Formula) : Except String Bool :=
  m.eFrame.eWorlds.toList.allM (eSatisfies m · f)

/-- Construct the restricted model M|B (B&D Definition 15.11, p. 201) where:
  W' = {w ∈ W : M, w ⊩ B}
  R'_a = R_a ∩ (W' × W')
  V'(p) = V(p) ∩ W'
Evaluating `B` at a world can error (`eSatisfies`), so this is an `Except`. -/
def restrictModel (m : EpistemicModel) (announcement : Formula) : Except String EpistemicModel := do
  let wPrime ← m.eFrame.eWorlds.toList.filterM (eSatisfies m · announcement)
  return restrictWorlds m (Std.TreeSet.ofList wPrime)

-- --------------------------------------------------------------------
-- Group and common knowledge (B&D Definitions 15.3, p. 192, and 15.6, p. 196)
-- --------------------------------------------------------------------

/-- Everybody-knows operator: E_{G'} A = ∧_{b∈G'} K_b A (B&D Definition
15.3, p. 192). -/
def groupKnows (m : EpistemicModel) (w : World) (agentList : List String) (f : Formula) :
    Except String Bool :=
  agentList.allM fun a => eSatisfies m w (.knowledge a f)

/-- Common knowledge: C_{G'} A holds at w iff A holds at every world w'
with R_{G'} w w', where R_{G'} is the *transitive closure* (R⁺) of
∪_{b∈G'} R_b (B&D Definition 15.6, p. 196, and Definition B.40, p. 231:
R⁺ = ⋃_{0<n} Rⁿ).

The closure is transitive, NOT reflexive-transitive: w' ranges over
worlds reachable from w in *one or more* steps, so w itself is
included only when it lies on a ≥1-step cycle. The previous code
seeded the reachable set with `{w}` (i.e. used R∗), which coincides
with R⁺ on reflexive S5 relations but over-restricts C_G on
non-reflexive relations (adversarial review B8).

Haskell computes the reachable set by breadth-first search, calling
`eAccessible` for every agent at every visited world; here the agents are
checked once up front (`eAccessible` at `w`, in list order, so the same
unknown-agent error surfaces first) and the closure runs through the
shared `iterateToFixpoint`. Each round adds the successors of every world
reached so far; every reachable world is in `U = W ∪ {targets of the
listed agents' edges}` (edges are not checked against `W` when the frame
is built), so each non-final round adds at least one of at most `|U|`
worlds and `|U| + 1` rounds suffice. The fuel below is an upper bound on
that. -/
def commonKnowledge (m : EpistemicModel) (w : World) (agentList : List String) (f : Formula) :
    Except String Bool := do
  agentList.forM fun a => discard <| eAccessible m.eFrame a w
  let rels := agentList.map fun a => m.eFrame.eRelations.getD a ∅
  let step (u : World) : Std.TreeSet World :=
    rels.foldl (fun acc rel => acc.insertMany (rel.getD u ∅)) ∅
  let expand (visited : Std.TreeSet World) : Std.TreeSet World :=
    visited.foldl (fun acc u => acc.insertMany (step u)) visited
  let bound := m.eFrame.eWorlds.size
    + rels.foldl (fun n rel => rel.foldl (fun n _ succs => n + succs.size) n) 0
  let reachable ← iterateToFixpoint "commonKnowledge" expand (bound + 1) (step w)
  reachable.toList.allM (eSatisfies m · f)

-- --------------------------------------------------------------------
-- Bisimulation (B&D Definition 15.7, p. 198)
-- --------------------------------------------------------------------

/-- Doxastic (belief) accessibility with an empty default — unlike
`eDoxasticAccessible` it does not error on an agent absent from the
doxastic map, so a bisimulation check can compare a belief-carrying
model against a knowledge-only one (their belief edges then differ
and the back/forth clauses correctly reject the relation). -/
private def doxAccess (m : EpistemicModel) (a : String) (w : World) : Std.TreeSet World :=
  (m.eFrame.eDoxastic.getD a ∅).getD w ∅

/-- The propositional variables and the knowledge/doxastic agents that
a bisimulation between `m1` and `m2` must respect. -/
private def bisimSignature (m1 m2 : EpistemicModel) :
    Std.TreeSet Atom × Std.TreeSet String × Std.TreeSet String :=
  ( Std.TreeSet.ofList (m1.eValuation.keys ++ m2.eValuation.keys)
  , (agents m1.eFrame).insertMany (agents m2.eFrame)
  , Std.TreeSet.ofList (m1.eFrame.eDoxastic.keys ++ m2.eFrame.eDoxastic.keys) )

/-- Do worlds `w1` and `w2` satisfy the local bisimulation conditions
(atom agreement + forth/back for every knowledge *and* doxastic
relation) with respect to the pair-set `relSet`? Covering the
doxastic relations is what makes a certified bisimulation preserve
`belief` formulas, not just `knowledge` (adversarial review B8).

An agent in `kAgents` that one of the models lacks is an `eAccessible`
error, as in the Haskell (whose `forthBack` forces both accessibility
sets, `m1`'s first, whenever it is reached). -/
private def bisimLocal (m1 m2 : EpistemicModel) (allAtoms : Std.TreeSet Atom)
    (kAgents dAgents : Std.TreeSet String) (relSet : Std.TreeSet (World × World))
    (w1 w2 : World) : Except String Bool := do
  let atomAgrees (p : Atom) : Bool :=
    (m1.eValuation.getD p ∅).contains w1 == (m2.eValuation.getD p ∅).contains w2
  let forthBack (s1 s2 : Std.TreeSet World) : Bool :=
    s1.all (fun v1 => s2.any fun v2 => relSet.contains (v1, v2))
    && s2.all (fun v2 => s1.any fun v1 => relSet.contains (v1, v2))
  -- Clause 1: propositional agreement
  if !allAtoms.all atomAgrees then return false
  -- Clauses 2/3: forth/back over knowledge relations
  let kOk ← kAgents.toList.allM fun a => do
    let s1 ← eAccessible m1.eFrame a w1
    let s2 ← eAccessible m2.eFrame a w2
    pure (forthBack s1 s2)
  if !kOk then return false
  -- Clauses 4/5: forth/back over doxastic relations
  return dAgents.all fun a => forthBack (doxAccess m1 a w1) (doxAccess m2 a w2)

/-- Check whether a relation is a bisimulation between two models
(B&D Definition 15.7, p. 198), covering both knowledge and belief
relations. -/
def isBisimulation (m1 m2 : EpistemicModel) (rel : List (World × World)) : Except String Bool :=
  let relSet := Std.TreeSet.ofList rel
  let (allAtoms, kAgents, dAgents) := bisimSignature m1 m2
  rel.allM fun (w1, w2) => bisimLocal m1 m2 allAtoms kAgents dAgents relSet w1 w2

/-- Strict equality on `Except` results, so `largestBisimulation`'s
refinement can run through `iterateToFixpoint`: an error state is its own
fixpoint (`step (error e) = error e`), and is returned as the error. -/
private local instance [BEq ε] [BEq α] : BEq (Except ε α) where
  beq
    | .ok a, .ok b => a == b
    | .error x, .error y => x == y
    | _, _ => false

/-- The largest bisimulation between two models, computed by partition
refinement (Kanellakis–Smolka): start from every world pair that
agrees on all atoms, then repeatedly drop any pair that fails a
forth/back clause (for a knowledge or doxastic relation) against the
current relation, until a fixed point. The result is the greatest
bisimulation — any two worlds it relates are modally equivalent for
knowledge *and* belief.

The refinement loop (Haskell `refine`) runs through the shared
`iterateToFixpoint`, over `Except` so that a `bisimLocal` error stops it
with that error. Each non-final round drops at least one of the `initial`
pairs, so `|initial| + 1` rounds suffice. -/
def largestBisimulation (m1 m2 : EpistemicModel) : Except String (List (World × World)) := do
  let (allAtoms, kAgents, dAgents) := bisimSignature m1 m2
  let ws1 := m1.eFrame.eWorlds.toList
  let ws2 := m2.eFrame.eWorlds.toList
  let val (m : EpistemicModel) (p : Atom) : Std.TreeSet World := m.eValuation.getD p ∅
  -- Seed: all atom-agreeing pairs (clause 1 is refinement-stable).
  let initial : Std.TreeSet (World × World) := Std.TreeSet.ofList <|
    ws1.flatMap fun w1 => ws2.filterMap fun w2 =>
      if allAtoms.all (fun p => (val m1 p).contains w1 == (val m2 p).contains w2)
        then some (w1, w2) else none
  let refineOnce (r : Std.TreeSet (World × World)) : Except String (Std.TreeSet (World × World)) :=
    (fun l => (Std.TreeSet.ofList l : Std.TreeSet (World × World))) <$>
      r.toList.filterM fun (w1, w2) => bisimLocal m1 m2 allAtoms kAgents dAgents r w1 w2
  let result ← iterateToFixpoint "largestBisimulation" (· >>= refineOnce) (initial.size + 1)
    (pure initial)
  let r ← result
  return r.toList

/-- Check bisimilarity of specific worlds via a given relation. Haskell's
`&&` is lazy: when `(w1, w2)` is not in `rel`, `isBisimulation` is not
evaluated and cannot error. -/
def bisimilarWorlds (m1 m2 : EpistemicModel) (w1 w2 : World) (rel : List (World × World)) :
    Except String Bool :=
  if rel.contains (w1, w2) then isBisimulation m1 m2 rel else pure false

-- --------------------------------------------------------------------
-- Conversion from single-agent KripkeModel
-- --------------------------------------------------------------------

/-- Wrap a `Model` as a single-agent `EpistemicModel`. -/
def fromKripkeModel (m : Model) (agent : String) : EpistemicModel :=
  { eFrame :=
      { eWorlds := m.frame.worlds
        eRelations := Std.TreeMap.ofList [(agent, m.frame.relation)]
        eDoxastic := ∅ }
    eValuation := m.valuation }

end Gamen
