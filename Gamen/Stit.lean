import Std.Data.TreeMap
import Gamen.Formula
import Gamen.Kripke

/-!
# Gamen.Stit

Port of `gamen-hs/src/Gamen/Stit.hs`: Temporal STIT logic (T-STIT), Lorini,
E. (2013). "Temporal STIT logic and its application to normative
reasoning." *Journal of Applied Non-Classical Logics*, 23(4), pp. 372–399.
Local copy `notes/Lorini_12691.pdf`, checked with `pdftotext` (title,
venue, volume, and page range confirmed against the PDF's own citation
block; the in-body definition/example page numbers below are carried over
from the Haskell unchanged).

Multi-relational Kripke models for reasoning about agency, choice, and
obligation with temporal operators. Agents' choices partition possible
worlds at each moment; the grand coalition's choice is the intersection
of individual choices.

`Agent` is written as `String` directly, matching `Gamen.Cgs`/
`Gamen.DeonticStit`'s choice: `Gamen.Agent` already exists
(`RankingTheory.lean`), a module this one's Haskell import list (Formula,
Kripke) does not depend on.

`sSatisfies` returns `Except String Bool`: the world-existence guard and
the unsupported-operator branches that are Haskell `error` calls become
`throw`, as does `agentAccessible`'s unknown-agent guard (the Haskell's own
comment cites adversarial review B1 / gamen-hs#7: an unknown agent must not
make `[i]φ` vacuously true).
-/
namespace Gamen

-- --------------------------------------------------------------------
-- T-STIT frames and models (Lorini 2013, Definition 1, pp. 373–374)
-- --------------------------------------------------------------------

/-- A temporal Kripke STIT frame.

`M = (W, R_□, {R_i | i ∈ Agt}, R_Agt, R_G, R_H, V)` where R_□, each R_i,
and R_Agt are equivalence relations, R_G is serial and transitive (strict
future), and R_H = R_G⁻¹. -/
structure StitFrame where
  sWorlds : Std.TreeSet World
  /-- R_□: historical necessity (equivalence). -/
  rSettled : Std.TreeMap World (Std.TreeSet World)
  /-- {R_i}: per-agent choice (equivalence). -/
  rAgents : Std.TreeMap String (Std.TreeMap World (Std.TreeSet World))
  /-- R_Agt: grand coalition (intersection of R_i). -/
  rGrandCoal : Std.TreeMap World (Std.TreeSet World)
  /-- R_G: strict future (serial + transitive). -/
  rFuture : Std.TreeMap World (Std.TreeSet World)
  /-- R_H = R_G⁻¹. -/
  rPast : Std.TreeMap World (Std.TreeSet World)
  deriving BEq, Repr

/-- A T-STIT model: frame + valuation. -/
structure StitModel where
  sFrame : StitFrame
  sValuation : Std.TreeMap Atom (Std.TreeSet World)
  deriving BEq, Repr

/-- Invert a relation: R_H = R_G⁻¹. -/
def invertRelation (ws : Std.TreeSet World) (rel : Std.TreeMap World (Std.TreeSet World)) :
    Std.TreeMap World (Std.TreeSet World) :=
  ws.toList.foldl
    (fun acc src =>
      (rel.getD src ∅).toList.foldl
        (fun acc' dst => acc'.insert dst ((acc'.getD dst ∅).insert src))
        acc)
    ∅

/-- Compute the grand coalition relation as the pointwise intersection of
all agent relations: R_Agt(w) = ⋂_i R_i(w). -/
def computeGrandCoalition (ws : Std.TreeSet World)
    (agentRels : Std.TreeMap String (Std.TreeMap World (Std.TreeSet World))) :
    Std.TreeMap World (Std.TreeSet World) :=
  if agentRels.isEmpty then
    Std.TreeMap.ofList (ws.toList.map fun w => (w, ws))
  else
    Std.TreeMap.ofList (ws.toList.map fun w =>
      match agentRels.values.map (fun rel => rel.getD w ∅) with
      | [] => (w, ws)  -- unreachable: `agentRels` is non-empty on this branch
      | c :: cs => (w, cs.foldl (· ∩ ·) c))

/-- Construct a T-STIT frame.

Auto-computes R_H as the inverse of R_G, and R_Agt as the pointwise
intersection of all R_i. No `error` in the Haskell (unlike `Kripke.mkFrame`,
edges are not checked against the world set); ported as-is. -/
def mkStitFrame (ws : List World) (settledPairs : List (World × World))
    (agentPairs : List (String × List (World × World)))
    (futurePairs : List (World × World)) : StitFrame :=
  let worldSet := Std.TreeSet.ofList ws
  let buildRel (pairs : List (World × World)) : Std.TreeMap World (Std.TreeSet World) :=
    pairs.foldl (fun m (src, dst) => m.insert src ((m.getD src ∅).insert dst)) ∅
  let agentRels := Std.TreeMap.ofList (agentPairs.map fun (agent, rels) => (agent, buildRel rels))
  let future := buildRel futurePairs
  { sWorlds := worldSet
    rSettled := buildRel settledPairs
    rAgents := agentRels
    rGrandCoal := computeGrandCoalition worldSet agentRels
    rFuture := future
    rPast := invertRelation worldSet future }

/-- Construct a T-STIT model. -/
def mkStitModel (fr : StitFrame) (vals : List (String × List World)) : StitModel :=
  { sFrame := fr
    sValuation := Std.TreeMap.ofList
      (vals.map fun (n, ws) => ((⟨n⟩ : Atom), Std.TreeSet.ofList ws)) }

-- --------------------------------------------------------------------
-- Accessors
-- --------------------------------------------------------------------

/-- Worlds accessible via a named relation. -/
def sAccessible (rel : Std.TreeMap World (Std.TreeSet World)) (w : World) : Std.TreeSet World :=
  rel.getD w ∅

/-- Agent's accessible worlds from a given world.

Errors on an unknown agent rather than returning ∅: without this guard,
`[i]φ` would be vacuously true for any agent name, known or not
(adversarial review B1, cf. the world guard, gamen-hs#7). -/
def agentAccessible (fr : StitFrame) (agent : String) (w : World) :
    Except String (Std.TreeSet World) :=
  match fr.rAgents.get? agent with
  | none => throw s!"agentAccessible: agent {agent} is not in model"
  | some rel => pure (sAccessible rel w)

/-- The set of agents in the frame. -/
def sAgents (fr : StitFrame) : Std.TreeSet String :=
  Std.TreeSet.ofList fr.rAgents.keys

/-- Agent i's choice cell at world w: the R_i equivalence class of w. -/
def choiceCell (fr : StitFrame) (agent : String) (w : World) :
    Except String (Std.TreeSet World) :=
  agentAccessible fr agent w

/-- The moment containing w: the R_□ equivalence class of w. -/
def moment (fr : StitFrame) (w : World) : Std.TreeSet World :=
  sAccessible fr.rSettled w

-- --------------------------------------------------------------------
-- Semantics (Lorini 2013, Section 2.2)
-- --------------------------------------------------------------------

/-- `M, w ⊩ φ` for T-STIT models.

Errors if `w` is not in `m.sFrame.sWorlds` — without this guard,
non-existent worlds yield vacuously-true results for negative, universal,
and modal formulas (gamen-hs#7, mirroring gamen-hs#3). Fourteen operators
have no T-STIT semantics and `throw`, matching the Haskell's `error`
calls. -/
def sSatisfies (m : StitModel) (w : World) (f : Formula) : Except String Bool := do
  unless m.sFrame.sWorlds.contains w do
    throw s!"sSatisfies: world {w} is not in model"
  match f with
  | .bot => return false
  | .atomF a => return (m.sValuation.getD a ∅).contains w
  | .not g => return !(← sSatisfies m w g)
  -- Short-circuiting, matching Haskell's lazy `&&`/`||`: the right side
  -- is only evaluated (and so can only error) when the left side's value
  -- doesn't already settle the result.
  | .and l r => if !(← sSatisfies m w l) then return false else sSatisfies m w r
  | .or l r => if (← sSatisfies m w l) then return true else sSatisfies m w r
  | .implies l r => if !(← sSatisfies m w l) then return true else sSatisfies m w r
  | .iff l r => return (← sSatisfies m w l) == (← sSatisfies m w r)
  -- [i]φ: agent i sees to it that φ (universal over R_i)
  | .stit agent g => do
      let acc ← agentAccessible m.sFrame agent w
      acc.toList.allM (sSatisfies m · g)
  -- ⟨i⟩φ: agent i has a choice that allows φ (existential dual of [i])
  | .choiceDiamond agent g => do
      let acc ← agentAccessible m.sFrame agent w
      acc.toList.anyM (sSatisfies m · g)
  -- [Agt]φ: grand coalition sees to it (universal over R_Agt)
  | .groupStit g => (sAccessible m.sFrame.rGrandCoal w).toList.allM (sSatisfies m · g)
  -- □φ: historically necessary / settled (universal over R_□)
  | .box g => (sAccessible m.sFrame.rSettled w).toList.allM (sSatisfies m · g)
  -- ◇φ: historically possible (existential dual of □)
  | .diamond g => (sAccessible m.sFrame.rSettled w).toList.anyM (sSatisfies m · g)
  -- Temporal operators (over R_G and R_H)
  | .futureBox g => (sAccessible m.sFrame.rFuture w).toList.allM (sSatisfies m · g)
  | .futureDiamond g => (sAccessible m.sFrame.rFuture w).toList.anyM (sSatisfies m · g)
  | .pastBox g => (sAccessible m.sFrame.rPast w).toList.allM (sSatisfies m · g)
  | .pastDiamond g => (sAccessible m.sFrame.rPast w).toList.anyM (sSatisfies m · g)
  -- Operators not supported in STIT models
  | .since _ _ => throw "Since not yet supported in STIT models"
  | .until _ _ => throw "Until not yet supported in STIT models"
  | .knowledge _ _ => throw "Knowledge not supported in STIT models; use Gamen.Epistemic"
  | .belief _ _ => throw "Belief not supported in STIT models; use Gamen.Epistemic"
  | .rankedBelief _ _ _ =>
      throw "RankedBelief not supported in STIT models; use Gamen.RankingTheory"
  | .announce _ _ => throw "Announce not supported in STIT models; use Gamen.Epistemic"
  | .next _ => throw "Next not supported in STIT models; use Gamen.Laca"
  | .ought _ _ => throw "Ought not supported in T-STIT; use Gamen.DeonticStit"
  | .permitted _ _ => throw "Permitted not supported in T-STIT; use Gamen.DeonticStit"
  | .coalition _ _ => throw "Coalition not supported in T-STIT; use Gamen.Cgs/Gamen.Coalition"
  | .canNext _ _ => throw "CanNext not supported in T-STIT; use Gamen.Atl"
  | .canAlways _ _ => throw "CanAlways not supported in T-STIT; use Gamen.Atl"
  | .canEventually _ _ => throw "CanEventually not supported in T-STIT; use Gamen.Atl"
  | .canUntil _ _ _ => throw "CanUntil not supported in T-STIT; use Gamen.Atl"
termination_by f

/-- A formula is true in a STIT model if it holds at every world. -/
def sIsTrueIn (m : StitModel) (f : Formula) : Except String Bool :=
  m.sFrame.sWorlds.toList.allM (sSatisfies m · f)

-- --------------------------------------------------------------------
-- Constraint checking (Lorini 2013, Definition 1, pp. 373–374, C1-C7)
-- --------------------------------------------------------------------

/-- C1: R_i ⊆ R_□ for all agents i.
Each agent's choice refines the moment partition. -/
def checkC1 (fr : StitFrame) : Bool :=
  fr.rAgents.toList.all fun (_, agentRel) =>
    fr.sWorlds.all fun w =>
      subsetOf (sAccessible agentRel w) (sAccessible fr.rSettled w)

/-- C2: Independence of agents.
For any selection of one choice cell per agent (at the same moment), the
intersection is non-empty.

For efficiency, this checks only within each R_□ equivalence class. -/
def checkC2 (fr : StitFrame) : Bool :=
  let moments := equivalenceClasses fr.sWorlds fr.rSettled
  let agentList := fr.rAgents.keys
  -- `agentList` is always drawn from `fr.rAgents`'s own keys, so this
  -- total accessor never actually falls into a missing-agent default —
  -- it exists only so `checkIndependence`'s accessor parameter stays a
  -- pure function, matching `Kripke.checkIndependence`'s signature and
  -- `DeonticStit.checkDS_C2`'s `dsAccessible` (unlike the exported,
  -- `Except`-returning `agentAccessible` above, which must error on a
  -- genuinely unknown agent).
  let accessible (agent : String) (w : World) : Std.TreeSet World :=
    sAccessible (fr.rAgents.getD agent ∅) w
  moments.all fun mom => checkIndependence accessible agentList mom

/-- C3: R_Agt(w) = intersection of R_i(w) for all i.
The grand coalition's choice is the pointwise intersection of individual
choices. -/
def checkC3 (fr : StitFrame) : Bool :=
  fr.sWorlds.all fun w =>
    let expected := match fr.rAgents.values with
      | [] => fr.sWorlds  -- no agents: grand coalition is everything
      | rels =>
          -- `rels` is non-empty here, so `rels.map _` is too; the `[]`
          -- arm below is unreachable, matching `computeGrandCoalition`'s
          -- Haskell-mirroring `foldl1` above.
          match rels.map (fun rel => sAccessible rel w) with
          | [] => fr.sWorlds
          | c :: cs => cs.foldl (· ∩ ·) c
    sAccessible fr.rGrandCoal w == expected

/-- C4: Connectedness of R_G within moments.
For all w, v, u in W: if v, u in R_G(w) then u in R_G(v) or v in R_G(u) or
u = v. -/
def checkC4 (fr : StitFrame) : Bool :=
  fr.sWorlds.all fun w =>
    let succs := (sAccessible fr.rFuture w).toList
    succs.all fun v => succs.all fun u =>
      u == v
      || (sAccessible fr.rFuture v).contains u
      || (sAccessible fr.rFuture u).contains v

/-- C5: Connectedness of R_H within moments (symmetric to C4).
For all w, v, u in W: if v, u in R_H(w) then u in R_H(v) or v in R_H(u) or
u = v. -/
def checkC5 (fr : StitFrame) : Bool :=
  fr.sWorlds.all fun w =>
    let preds := (sAccessible fr.rPast w).toList
    preds.all fun v => preds.all fun u =>
      u == v
      || (sAccessible fr.rPast v).contains u
      || (sAccessible fr.rPast u).contains v

/-- C6: No choice between undivided histories.
R_G ∘ R_□ ⊆ R_Agt ∘ R_G. If v is in the future of w, and u is in the same
moment as v, then there exists z in R_Agt(w) such that u is in R_G(z). -/
def checkC6 (fr : StitFrame) : Bool :=
  fr.sWorlds.all fun w =>
    (sAccessible fr.rFuture w).all fun v =>
      (sAccessible fr.rSettled v).all fun u =>
        (sAccessible fr.rGrandCoal w).any fun z => (sAccessible fr.rFuture z).contains u

/-- C7: Irreflexivity of R_G within R_□ classes.
If v in R_□(w), then v not in R_G(w). (Worlds at the same moment cannot be
in each other's strict future.) -/
def checkC7 (fr : StitFrame) : Bool :=
  fr.sWorlds.all fun w =>
    (sAccessible fr.rSettled w).all fun v => !(sAccessible fr.rFuture w).contains v

/-- Transitivity of a relation over a world set. One-line wrapper over the
shared `Kripke.transitiveOn` (CLAUDE.md "Shared relation checks"). -/
def isTransitiveOn (ws : Std.TreeSet World) (rel : Std.TreeMap World (Std.TreeSet World)) :
    Bool :=
  transitiveOn ws rel

/-- Def. 1 /typing/ requirements (Lorini 2013): R_□, each R_i, and R_Agt
are equivalence relations; R_G is transitive; R_H = R_G⁻¹. C1–C7 constrain
how these relations interlock but /presuppose/ the typing — a frame with,
say, a non-transitive R_i satisfies C1–C7 yet is not a T-STIT frame, and
the earlier validator (C1–C7 only) accepted it (adversarial review B7).
`isEquivalenceOn` was imported for exactly this and left unused.

/Seriality of R_G/ (Lorini's "time has no end") is deliberately /not/
required here: this module model-checks finite grounded frames, and C7
(R_G irreflexive within a moment) makes a serial R_G impossible in a
single-moment finite frame. Finite frames therefore carry a truncated
future, matching the finite-model simplification used throughout
(cf. `Gamen.Laca`). -/
def checkTyping (fr : StitFrame) : Bool :=
  isEquivalenceOn fr.sWorlds fr.rSettled
  && fr.rAgents.values.all (isEquivalenceOn fr.sWorlds)
  && isEquivalenceOn fr.sWorlds fr.rGrandCoal
  && isTransitiveOn fr.sWorlds fr.rFuture
  && fr.rPast == invertRelation fr.sWorlds fr.rFuture

/-- Check all T-STIT frame constraints: Def. 1 typing (`checkTyping`) and
the interaction constraints C1–C7. -/
def isValidStitFrame (fr : StitFrame) : Bool :=
  checkTyping fr &&
  checkC1 fr && checkC2 fr && checkC3 fr &&
  checkC4 fr && checkC5 fr && checkC6 fr && checkC7 fr

end Gamen
