import Std.Data.TreeMap
import Gamen.Formula
import Gamen.Kripke

/-!
# Gamen.Xstit

Port of `gamen-hs/src/Gamen/Xstit.hs`: epistemic deontic XSTIT logic,
Broersen, J. (2011). "Deontic epistemic stit logic distinguishing modes of
mens rea." *Journal of Applied Logic* 9, 137–152. Local copy
`gamen-hs/notes/Broersen2011.pdf`; title, venue, volume, and page range
taken from its `pdftotext` output, and every definition and page number
below checked against it.

XSTIT combines agency (`[a xstit]`), temporal next-state (X), epistemic
knowledge (K_a), and deontic obligation (via violation constants) to
formalize modes of mens rea (Broersen 2011, §5, "Deontic modalities and
modes of mens rea", pp. 147–149).

The automatic classifier `mensReaCheck` (and the `MensRea` type)
distinguishes *three* modes — knowingly, recklessly, and strict liability.
A `negligently` formula is also provided, but it takes an explicit
standard-of-care premise and so is a standalone constructor rather than
part of the classification; "purposefully" is not modeled (adversarial
review B8).

Two-dimensional semantics: each world encodes a (dynamic state, history)
pair. The frame's relations capture the branching-time structure.

`Agent` is written as `String` directly, as in `Gamen.Stit`/`Gamen.Cgs`
(`Gamen.Agent` already exists in `RankingTheory.lean`).

Every Haskell `error` becomes an `Except`: `mkXstitFrame`'s non-functional
R_X, `xChoiceCell`/`xEpistemicCell`'s unknown agent, `nextOf`'s missing
successor, and `xSatisfies`'s world guard and unsupported operators. The
functions built on `xSatisfies` (`xIsTrueIn`, `mensReaCheck`, the three
application checks) return `Except` in turn.

Citation fixes against the PDF (the Haskell's are wrong): frames are
Definitions 2.2 (p. 140) and 3.2 (p. 144), not "Definition 3.1" (that is
the language); models are Definition 2.3 (p. 142); truth is Definitions 2.4
(p. 142) and 3.3 (p. 145), not "Definition 3.2"; "knowingly doing"
K_a[a xstit]φ is introduced right after Definition 3.3 (p. 145), not in
"Definition 5.2" (that is the weaker strict-liability obligation
□([a xstit]¬φ → [a xstit]V)). `obligatedKnowingly` and `recklessly` are
gamen-hs's own combinations motivated by Definition 5.3 (p. 148); they are
not that definition's operators, which are obligations with a knowledge
formula in the antecedent.
-/
namespace Gamen

-- --------------------------------------------------------------------
-- XSTIT frames and models (Broersen 2011, Definitions 2.2, 2.3, 3.2)
-- --------------------------------------------------------------------

/-- An XSTIT frame (Broersen 2011, Definition 2.2, p. 140, extended with
epistemic relations by Definition 3.2, p. 144).

F = (W, R_X, R_□, {R_[A] | A ∈ Agt}, {R_{K_a} | a ∈ Agt})

Each world w ∈ W represents a (dynamic state, history) pair.
- R_X: next-state (serial, deterministic — a function)
- R_□: historical necessity / settledness (equivalence)
- R_[A]: per-agent choice effectivity (equivalence, refines R_□)
- R_{K_a}: per-agent epistemic indistinguishability (equivalence) -/
structure XstitFrame where
  xWorlds : Std.TreeSet World
  /-- R_X: deterministic next-state. -/
  rNext : Std.TreeMap World World
  /-- R_□: historical necessity (equivalence). -/
  rSettledX : Std.TreeMap World (Std.TreeSet World)
  /-- R_[A]: per-agent choice (equivalence). -/
  rChoice : Std.TreeMap String (Std.TreeMap World (Std.TreeSet World))
  /-- R_{K_a}: per-agent knowledge (equivalence). -/
  rEpistemic : Std.TreeMap String (Std.TreeMap World (Std.TreeSet World))
  deriving BEq, Repr

/-- An XSTIT model: frame + valuation (Broersen 2011, Definition 2.3,
p. 142). Violation atoms `"v_a"` are ordinary atoms in the valuation. -/
structure XstitModel where
  xFrame : XstitFrame
  xValuation : Std.TreeMap Atom (Std.TreeSet World)
  deriving BEq, Repr

/-- Build a relation map from pairs (Haskell's `Map.fromListWith Set.union`). -/
private def xBuildRel (pairs : List (World × World)) : Std.TreeMap World (Std.TreeSet World) :=
  pairs.foldl (fun m (src, dst) => m.insert src ((m.getD src ∅).insert dst)) ∅

/-- Construct an XSTIT frame.

Errors if R_X is not functional: a world given more than one distinct
next-state. Haskell's `Map.fromList` used to keep the last binding
silently, corrupting the next-state function (adversarial review B7). The
first such world in ascending order is reported, as in the Haskell. -/
def mkXstitFrame (ws : List World)
    (nextPairs : List (World × World))
    (settledPairs : List (World × World))
    (choicePairs : List (String × List (World × World)))
    (epistemicPairs : List (String × List (World × World))) : Except String XstitFrame :=
  let nonFunctional :=
    (xBuildRel nextPairs).toList.filterMap fun (src, tos) =>
      if tos.size > 1 then some src else none
  match nonFunctional with
  | w :: _ => throw s!"mkXstitFrame: R_X is not functional — world {repr w} is given \
      multiple next-states. R_X must be a deterministic function (Broersen 2011, Def. 2.2)."
  | [] => pure
      { xWorlds := Std.TreeSet.ofList ws
        rNext := Std.TreeMap.ofList nextPairs
        rSettledX := xBuildRel settledPairs
        rChoice := Std.TreeMap.ofList (choicePairs.map fun (agent, rels) => (agent, xBuildRel rels))
        rEpistemic :=
          Std.TreeMap.ofList (epistemicPairs.map fun (agent, rels) => (agent, xBuildRel rels)) }

/-- Construct an XSTIT model. -/
def mkXstitModel (fr : XstitFrame) (vals : List (String × List World)) : XstitModel :=
  { xFrame := fr
    xValuation := Std.TreeMap.ofList
      (vals.map fun (n, ws) => ((⟨n⟩ : Atom), Std.TreeSet.ofList ws)) }

-- --------------------------------------------------------------------
-- Accessors
-- --------------------------------------------------------------------

/-- The set of agents in the frame (from choice relations). -/
def xAgents (fr : XstitFrame) : Std.TreeSet String :=
  Std.TreeSet.ofList fr.rChoice.keys

/-- Agent's choice cell at world w: R_[A](w).

Errors rather than returning ∅ for an unknown agent: otherwise `[A xstit]φ`
and (via obligation) `⊗_A φ` are vacuously true for every φ (adversarial
review B1; cf. gamen-hs#7). -/
def xChoiceCell (fr : XstitFrame) (agent : String) (w : World) :
    Except String (Std.TreeSet World) :=
  match fr.rChoice.get? agent with
  | none => throw s!"xChoiceCell: agent {repr agent} is not in model"
  | some rel => pure (rel.getD w ∅)

/-- Agent's epistemic cell at world w: R_{K_a}(w). Errors on an unknown
agent, as `xChoiceCell`. -/
def xEpistemicCell (fr : XstitFrame) (agent : String) (w : World) :
    Except String (Std.TreeSet World) :=
  match fr.rEpistemic.get? agent with
  | none => throw s!"xEpistemicCell: agent {repr agent} is not in model"
  | some rel => pure (rel.getD w ∅)

/-- Settled cell at world w: R_□(w). -/
def xSettledCell (fr : XstitFrame) (w : World) : Std.TreeSet World :=
  fr.rSettledX.getD w ∅

/-- Next world on this history: R_X(w). Errors if R_X has no successor
for `w` (R_X not serial). -/
def nextOf (fr : XstitFrame) (w : World) : Except String World :=
  match fr.rNext.get? w with
  | some w' => pure w'
  | none => throw s!"R_X is not serial: no successor for world {repr w}"

-- --------------------------------------------------------------------
-- Derived operators (Broersen 2011, Section 5)
-- --------------------------------------------------------------------
-- `violationAtom` and `obligation` come before `xSatisfies` (the Haskell
-- defines them after) because `xSatisfies` evaluates `Ought` by
-- rewriting to `obligation`.

/-- Violation atom for agent a: Anderson-style violation constant V
(Broersen 2011, §5, p. 147), one per agent. -/
def violationAtom (a : String) : Formula := .atom ("v_" ++ a)

/-- Obligation: O[a xstit]φ (Broersen 2011, Definition 5.1, p. 147).
□(¬[a xstit]φ → [a xstit]V_a) -/
def obligation (a : String) (phi : Formula) : Formula :=
  .box (.implies (.not (.stit a phi)) (.stit a (violationAtom a)))

/-- Termination measure for `xSatisfies`. `ought`/`permitted` are weighted
so that their rewrites (to `obligation a φ` and to `¬ought a (¬φ)`) are
strictly lighter than the formula they came from; every other constructor
weighs one more than its subformulas. Used only in `termination_by`: the
recursion itself is the Haskell's, unchanged. -/
def xstitWeight : Formula → Nat
  | .bot => 1
  | .atomF _ => 1
  | .not f => xstitWeight f + 1
  | .and l r => xstitWeight l + xstitWeight r + 1
  | .or l r => xstitWeight l + xstitWeight r + 1
  | .implies l r => xstitWeight l + xstitWeight r + 1
  | .iff l r => xstitWeight l + xstitWeight r + 1
  | .box f => xstitWeight f + 1
  | .diamond f => xstitWeight f + 1
  | .futureBox f => xstitWeight f + 1
  | .futureDiamond f => xstitWeight f + 1
  | .pastBox f => xstitWeight f + 1
  | .pastDiamond f => xstitWeight f + 1
  | .since l r => xstitWeight l + xstitWeight r + 1
  | .until l r => xstitWeight l + xstitWeight r + 1
  | .knowledge _ f => xstitWeight f + 1
  | .belief _ f => xstitWeight f + 1
  | .rankedBelief _ _ f => xstitWeight f + 1
  | .announce b c => xstitWeight b + xstitWeight c + 1
  | .stit _ f => xstitWeight f + 1
  | .choiceDiamond _ f => xstitWeight f + 1
  | .groupStit f => xstitWeight f + 1
  | .next f => xstitWeight f + 1
  | .ought _ f => xstitWeight f + 10
  | .permitted _ f => xstitWeight f + 20
  | .coalition _ f => xstitWeight f + 1
  | .canNext _ f => xstitWeight f + 1
  | .canAlways _ f => xstitWeight f + 1
  | .canEventually _ f => xstitWeight f + 1
  | .canUntil _ l r => xstitWeight l + xstitWeight r + 1

-- --------------------------------------------------------------------
-- Semantics (Broersen 2011, Definitions 2.4 and 3.3)
-- --------------------------------------------------------------------

/-- `M, w ⊩ φ` for XSTIT models (Broersen 2011, Definition 2.4, p. 142,
and Definition 3.3, p. 145, for K_a).

Key difference from T-STIT: `[a xstit]φ` means agent a's choice
guarantees φ *at the next state*. The "X" in XSTIT refers to this
next-state composition.

Errors if `w` is not in `m.xFrame.xWorlds` — without this guard,
non-existent worlds yield vacuously-true results for negative, universal,
and modal formulas (gamen-hs#7, mirroring gamen-hs#3). `Ought` is
evaluated by rewriting to `obligation`, and `Permitted a φ` as
`¬Ought a (¬φ)`, as in the Haskell; neither rewrite is structural, so
termination is by `xstitWeight`. -/
def xSatisfies (m : XstitModel) (w : World) (f : Formula) : Except String Bool := do
  unless m.xFrame.xWorlds.contains w do
    throw s!"xSatisfies: world {repr w} is not in model"
  match f with
  -- Propositional
  | .bot => return false
  | .atomF a => return (m.xValuation.getD a ∅).contains w
  | .not g => return !(← xSatisfies m w g)
  -- Short-circuiting, matching Haskell's lazy `&&`/`||`: the right side
  -- is only evaluated (and so can only error) when the left side's value
  -- doesn't already settle the result.
  | .and l r => if !(← xSatisfies m w l) then return false else xSatisfies m w r
  | .or l r => if (← xSatisfies m w l) then return true else xSatisfies m w r
  | .implies l r => if !(← xSatisfies m w l) then return true else xSatisfies m w r
  | .iff l r => return (← xSatisfies m w l) == (← xSatisfies m w r)
  -- Xφ: φ holds at R_X(w) (Definition 2.4, X clause)
  | .next g => do
      let w' ← nextOf m.xFrame w
      xSatisfies m w' g
  -- □φ: φ holds at all R_□-accessible worlds (historical necessity / settled)
  | .box g => (xSettledCell m.xFrame w).toList.allM (xSatisfies m · g)
  -- ◇φ: φ holds at some R_□-accessible world (dual of □)
  | .diamond g => (xSettledCell m.xFrame w).toList.anyM (xSatisfies m · g)
  -- [a xstit]φ: agent a's choice guarantees φ at the next state:
  -- for all w' ∈ R_[A](w), M, R_X(w') ⊩ φ
  | .stit agent g => do
      let cell ← xChoiceCell m.xFrame agent w
      cell.toList.allM fun w' => do
        let n ← nextOf m.xFrame w'
        xSatisfies m n g
  -- K_a φ: agent a knows φ (S5 — universal over R_{K_a})
  | .knowledge agent g => do
      let cell ← xEpistemicCell m.xFrame agent w
      cell.toList.allM (xSatisfies m · g)
  -- Ought_a φ: obligation via violation constants (Definition 5.1)
  | .ought agent g => xSatisfies m w (obligation agent g)
  -- Permitted_a φ: not obligated to ¬φ
  | .permitted agent g => return !(← xSatisfies m w (.ought agent (.not g)))
  -- Operators not supported in XSTIT models
  | .futureBox _ => throw "FutureBox not supported in XSTIT; only Next is available"
  | .futureDiamond _ => throw "FutureDiamond not supported in XSTIT; only Next is available"
  | .pastBox _ => throw "PastBox not supported in XSTIT"
  | .pastDiamond _ => throw "PastDiamond not supported in XSTIT"
  | .since _ _ => throw "Since not supported in XSTIT"
  | .until _ _ => throw "Until not supported in XSTIT"
  | .belief _ _ => throw "Belief not supported in XSTIT; use Gamen.Epistemic"
  | .rankedBelief _ _ _ => throw "RankedBelief not supported in XSTIT; use Gamen.RankingTheory"
  | .announce _ _ => throw "Announce not supported in XSTIT"
  | .groupStit _ => throw "GroupStit not supported in XSTIT; use Stit for individual agents"
  | .choiceDiamond _ _ => throw "ChoiceDiamond not yet supported in XSTIT"
  | .coalition _ _ => throw "Coalition not supported in XSTIT; use Gamen.Cgs/Gamen.Coalition"
  | .canNext _ _ => throw "CanNext not supported in XSTIT; use Gamen.Atl"
  | .canAlways _ _ => throw "CanAlways not supported in XSTIT; use Gamen.Atl"
  | .canEventually _ _ => throw "CanEventually not supported in XSTIT; use Gamen.Atl"
  | .canUntil _ _ _ => throw "CanUntil not supported in XSTIT; use Gamen.Atl"
termination_by xstitWeight f
decreasing_by all_goals (simp_wf; simp [xstitWeight, obligation, violationAtom]; try omega)

/-- A formula is true in an XSTIT model if it holds at every world. -/
def xIsTrueIn (m : XstitModel) (f : Formula) : Except String Bool :=
  m.xFrame.xWorlds.toList.allM (xSatisfies m · f)

-- --------------------------------------------------------------------
-- Frame conditions (Broersen 2011, Definitions 2.2 + 3.2)
-- XC1–XC5 correspond to the base XSTIT frame (Definition 2.2, p. 140).
-- XC6 (epistemic equivalence) corresponds to the epistemic extension
-- (Definition 3.2, p. 144).
-- --------------------------------------------------------------------

/-- XC1: R_X is serial — every world has a successor. -/
def checkXC1 (fr : XstitFrame) : Bool :=
  fr.xWorlds.all fun w => fr.rNext.contains w

/-- XC2: R_□ is an equivalence relation. -/
def checkXC2 (fr : XstitFrame) : Bool :=
  isEquivalenceOn fr.xWorlds fr.rSettledX

/-- XC3: Each R_[A] is an equivalence relation. -/
def checkXC3 (fr : XstitFrame) : Bool :=
  fr.rChoice.toList.all fun (_, rel) => isEquivalenceOn fr.xWorlds rel

/-- XC4: R_[A] refines R_□ — each choice cell is within a single moment:
R_[A](w) ⊆ R_□(w) for all w and all agents. -/
def checkXC4 (fr : XstitFrame) : Bool :=
  fr.rChoice.toList.all fun (_, rel) =>
    fr.xWorlds.all fun w => subsetOf (rel.getD w ∅) (xSettledCell fr w)

/-- XC5: Independence of agents. For any selection of one choice cell per
agent (within the same moment), the intersection is non-empty.

The Haskell passes `xChoiceCell fr`, which errors on an unknown agent; the
agents here are `fr.rChoice`'s own keys, so that error is unreachable and
a total accessor is used instead (as `Stit.checkC2` does), keeping
`checkIndependence`'s pure accessor parameter. -/
def checkXC5 (fr : XstitFrame) : Bool :=
  let agentList := fr.rChoice.keys
  let moments := equivalenceClasses fr.xWorlds fr.rSettledX
  let cell (agent : String) (w : World) : Std.TreeSet World :=
    (fr.rChoice.getD agent ∅).getD w ∅
  moments.all fun mom => checkIndependence cell agentList mom

/-- XC6: Each R_{K_a} is an equivalence relation. -/
def checkXC6 (fr : XstitFrame) : Bool :=
  fr.rEpistemic.toList.all fun (_, rel) => isEquivalenceOn fr.xWorlds rel

/-- Check all XSTIT frame conditions. -/
def isValidXstitFrame (fr : XstitFrame) : Bool :=
  checkXC1 fr && checkXC2 fr && checkXC3 fr
  && checkXC4 fr && checkXC5 fr && checkXC6 fr

-- --------------------------------------------------------------------
-- Derived mens rea operators (Broersen 2011, Sections 3 and 5)
-- --------------------------------------------------------------------

/-- Knowingly doing: agent knows they see to it, K_a[a xstit]φ
(Broersen 2011, p. 145, just after Definition 3.3). -/
def knowingly (a : String) (phi : Formula) : Formula :=
  .knowledge a (.stit a phi)

/-- Obligated and knowingly acting: O[a xstit]φ ∧ K_a[a xstit]φ.
gamen-hs's own combination, motivated by Definition 5.3's "acting
knowingly" mode (p. 148); not that definition's operator. -/
def obligatedKnowingly (a : String) (phi : Formula) : Formula :=
  .and (obligation a phi) (knowingly a phi)

/-- Recklessly acting: obligated to avoid φ, does not knowingly see to
avoidance, but also does not know that they don't bring about φ.
gamen-hs's own combination, motivated by Definition 5.3's "acting
recklessly" mode (p. 148); not that definition's operator. -/
def recklessly (a : String) (phi : Formula) : Formula :=
  .and (obligation a (.not phi))
    (.and (.not (knowingly a (.not phi)))
      (.not (.knowledge a (.not (.stit a phi)))))

/-- Negligently acting: obligated, does not know they see to it, but a
reasonable agent (captured by the standard-of-care formula) would know. -/
def negligently (a : String) (phi standardOfCare : Formula) : Formula :=
  .and (obligation a phi)
    (.and (.not (.knowledge a (.stit a phi))) standardOfCare)

/-- Strict liability: obligation violated, regardless of knowledge.
O[a xstit]φ ∧ ¬[a xstit]φ (Definition 5.1 is the strict-liability
obligation, p. 147). -/
def strictLiability (a : String) (phi : Formula) : Formula :=
  .and (obligation a phi) (.not (.stit a phi))

-- --------------------------------------------------------------------
-- Mens rea classification
-- --------------------------------------------------------------------

/-- Modes of mens rea (Broersen 2011, Section 5). -/
inductive MensRea where
  /-- Obligation violated, knowledge irrelevant. -/
  | mrStrictLiability
  /-- Knows risk but disregards. -/
  | mrReckless
  /-- Knows they see to the outcome. -/
  | mrKnowing
  deriving BEq, Ord, Repr, DecidableEq

/-- Classify the mens rea level of agent a with respect to outcome φ.
Returns all applicable classifications at the given world, in the
Haskell's order (strict liability, knowing, reckless). -/
def mensReaCheck (m : XstitModel) (w : World) (a : String) (phi : Formula) :
    Except String (List MensRea) := do
  let sl ← xSatisfies m w (strictLiability a phi)
  let kn ← xSatisfies m w (obligatedKnowingly a phi)
  let rk ← xSatisfies m w (recklessly a phi)
  return (if sl then [.mrStrictLiability] else [])
    ++ (if kn then [.mrKnowing] else [])
    ++ (if rk then [.mrReckless] else [])

-- --------------------------------------------------------------------
-- Application functions
-- --------------------------------------------------------------------

/-- Duty check: which candidate formulas is agent a obligated to see to at
world w? -/
def xDutyCheck (m : XstitModel) (w : World) (agent : String) (candidates : List Formula) :
    Except String (List Formula) :=
  candidates.filterM fun f => xSatisfies m w (.ought agent f)

/-- Knowledge check: which candidate formulas does agent a know at world
w? -/
def xKnowledgeCheck (m : XstitModel) (w : World) (agent : String) (candidates : List Formula) :
    Except String (List Formula) :=
  candidates.filterM fun f => xSatisfies m w (.knowledge agent f)

/-- Epistemic duty check: for each obligation, does agent a know it?
Returns pairs of (obligation, whether agent knows the obligation).

Strict where the Haskell is lazy: the knowledge flag is computed as soon
as the obligation holds, so an error in it surfaces even if a caller
would only have looked at the formulas. -/
def xEpistemicDutyCheck (m : XstitModel) (w : World) (agent : String)
    (candidates : List Formula) : Except String (List (Formula × Bool)) :=
  candidates.filterMapM fun f => do
    if ← xSatisfies m w (.ought agent f) then
      let k ← xSatisfies m w (.knowledge agent (.ought agent f))
      return some (f, k)
    else
      return none

end Gamen
