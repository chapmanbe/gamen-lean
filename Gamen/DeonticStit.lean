import Gamen.Formula
import Gamen.Kripke

/-!
# Gamen.DeonticStit

Port of `gamen-hs/src/Gamen/DeonticStit.hs`: DS^k_n frames and models
(Lyon & van Berkel, "Proof Theory and Decision Procedures for Deontic
STIT Logics", *Journal of Artificial Intelligence Research* 81 (2024),
pp. 837–876; local copy `notes/LyonBerkel2024.pdf`, checked with
`pdftotext`), for reasoning about agents' choices, obligations, and
permissions. Supports duty checking, compliance checking, and joint
fulfillment checking (Section 5, p. 867).

`Agent` is written as `String` directly, matching
`Gamen.DeonticStit.Sequent`'s choice: `Gamen.Agent` already exists
(`RankingTheory.lean`), a module this one's Haskell import list does not
depend on.

`dsSatisfies` returns `Except String Bool`: the world-existence guard and
the sixteen unsupported-operator branches that are Haskell `error` calls
here become `throw`. `dutyCheck` and `jointFulfillment` call `dsSatisfies`
and so also return `Except`, unlike their Haskell counterparts;
`complianceCheck` doesn't call it and stays `Bool`.
-/
namespace Gamen

-- --------------------------------------------------------------------
-- DS^k_n frames and models (Definition 2, p. 843; Lyon & van Berkel 2024)
-- --------------------------------------------------------------------

/-- A DS^k_n frame: F = ⟨W, {R_[i] | i ∈ Ag}, {I_⊗_i | i ∈ Ag}⟩
(Definition 2, p. 843). `dsRelations` holds each agent's choice relation
R_[i] (an equivalence relation, condition C1); `dsIdeals` holds each
agent's ideal-world set I_⊗_i (conditions D1–D3). -/
structure DSFrame where
  dsWorlds : Std.TreeSet World
  dsRelations : Std.TreeMap String (Std.TreeMap World (Std.TreeSet World))
  dsIdeals : Std.TreeMap String (Std.TreeSet World)
  deriving BEq, Repr

/-- A DS^k_n model: a frame plus a valuation. -/
structure DSModel where
  dsFrame : DSFrame
  dsValuation : Std.TreeMap Atom (Std.TreeSet World)
  deriving BEq, Repr

/-- Build a DS frame from world names, per-agent choice-relation edges,
and per-agent ideal-world lists. No `error` in the Haskell (unlike
`Kripke.mkFrame`, edges are not checked against the world set); ported
as-is. -/
def mkDSFrame (ws : List World) (agentPairs : List (String × List (World × World)))
    (idealPairs : List (String × List World)) : DSFrame :=
  let buildRel (rels : List (World × World)) : Std.TreeMap World (Std.TreeSet World) :=
    rels.foldl (fun m (from_, to_) => m.insert from_ ((m.getD from_ ∅).insert to_)) ∅
  { dsWorlds := Std.TreeSet.ofList ws
    dsRelations := Std.TreeMap.ofList (agentPairs.map fun (agent, rels) => (agent, buildRel rels))
    dsIdeals := Std.TreeMap.ofList (idealPairs.map fun (agent, iws) =>
      (agent, Std.TreeSet.ofList iws)) }

/-- Build a DS model from a frame and `(atomName, worlds)` pairs. -/
def mkDSModel (fr : DSFrame) (vals : List (String × List World)) : DSModel :=
  { dsFrame := fr
    dsValuation := Std.TreeMap.ofList
      (vals.map fun (n, ws) => ((⟨n⟩ : Atom), Std.TreeSet.ofList ws)) }

-- --------------------------------------------------------------------
-- Accessors
-- --------------------------------------------------------------------

/-- Agent `agent`'s accessible worlds from `w` (R_[i](w)). -/
def dsAccessible (fr : DSFrame) (agent : String) (w : World) : Std.TreeSet World :=
  match fr.dsRelations.get? agent with
  | none => ∅
  | some rel => rel.getD w ∅

/-- The set of agents in the frame. -/
def dsAgents (fr : DSFrame) : Std.TreeSet String :=
  Std.TreeSet.ofList fr.dsRelations.keys

/-- Agent `agent`'s choice cell at world `w`. -/
def dsChoiceCell (fr : DSFrame) (agent : String) (w : World) : Std.TreeSet World :=
  dsAccessible fr agent w

/-- Agent `agent`'s ideal worlds. Not exported from the Haskell module. -/
private def dsIdealSet (fr : DSFrame) (agent : String) : Std.TreeSet World :=
  fr.dsIdeals.getD agent ∅

-- --------------------------------------------------------------------
-- Semantics (Definition 3, pp. 844–845; Lyon & van Berkel 2024)
-- --------------------------------------------------------------------

/-- `M, w ⊩ φ` for DS models (Definition 3).

Errors if `w` is not in `m.dsFrame.dsWorlds` — without this guard,
non-existent worlds yield vacuously-true results for negative,
universal, and modal formulas (gamen-hs#7, mirroring gamen-hs#3).
Sixteen operators have no DS semantics and `throw`, matching the
Haskell's `error` calls; `groupStit` throws because Lyon & van Berkel's
DS language has no group operator — group obligation needs a different
logic. -/
def dsSatisfies (m : DSModel) (w : World) (f : Formula) : Except String Bool := do
  unless m.dsFrame.dsWorlds.contains w do
    throw s!"dsSatisfies: world {w} is not in model"
  match f with
  | .bot => return false
  | .atomF a => return (m.dsValuation.getD a ∅).contains w
  | .not g => return !(← dsSatisfies m w g)
  -- Short-circuiting, matching Haskell's lazy `&&`/`||`: the right side
  -- is only evaluated (and so can only error) when the left side's value
  -- doesn't already settle the result. `do`'s `←` is strict, so writing
  -- `(← dsSatisfies m w l) && (← dsSatisfies m w r)` would evaluate both
  -- sides unconditionally and surface a right-side error the Haskell
  -- never reaches (e.g. `And Bot (FutureBox p)`).
  | .and l r => if !(← dsSatisfies m w l) then return false else dsSatisfies m w r
  | .or l r => if (← dsSatisfies m w l) then return true else dsSatisfies m w r
  | .implies l r => if !(← dsSatisfies m w l) then return true else dsSatisfies m w r
  -- `==` on `Bool` is strict in both arguments in Haskell too; no
  -- short-circuiting to preserve here.
  | .iff l r => return (← dsSatisfies m w l) == (← dsSatisfies m w r)
  -- □φ: settled/necessary — true at all worlds (Def 3, item 5)
  | .box g => m.dsFrame.dsWorlds.toList.allM (dsSatisfies m · g)
  -- ◇φ: possible — true at some world (Def 3, item 6)
  | .diamond g => m.dsFrame.dsWorlds.toList.anyM (dsSatisfies m · g)
  -- [i]φ: agent i's choice guarantees φ (Def 3, item 7)
  | .stit agent g => (dsAccessible m.dsFrame agent w).toList.allM (dsSatisfies m · g)
  -- ⟨i⟩φ: i has a choice that allows φ (Def 3, item 8)
  | .choiceDiamond agent g => (dsAccessible m.dsFrame agent w).toList.anyM (dsSatisfies m · g)
  | .groupStit _ =>
      throw "GroupStit not supported in DS models; Lyon-Berkel have no group operator"
  -- ⊗_i φ: agent i ought to see to it that φ — true iff φ holds at all of
  -- i's ideal worlds (Def 3, item 9)
  | .ought agent g => (dsIdealSet m.dsFrame agent).toList.allM (dsSatisfies m · g)
  -- ⊖_i φ: agent i is permitted to see to it — true iff φ holds at some of
  -- i's ideal worlds (Def 3, item 10)
  | .permitted agent g => (dsIdealSet m.dsFrame agent).toList.anyM (dsSatisfies m · g)
  | .futureBox _ => throw "FutureBox not supported in DS models"
  | .futureDiamond _ => throw "FutureDiamond not supported in DS models"
  | .pastBox _ => throw "PastBox not supported in DS models"
  | .pastDiamond _ => throw "PastDiamond not supported in DS models"
  | .since _ _ => throw "Since not supported in DS models"
  | .until _ _ => throw "Until not supported in DS models"
  | .knowledge _ _ => throw "Knowledge not supported in DS models"
  | .belief _ _ => throw "Belief not supported in DS models"
  | .rankedBelief _ _ _ =>
      throw "RankedBelief not supported in DS models; use Gamen.RankingTheory"
  | .announce _ _ => throw "Announce not supported in DS models"
  | .next _ => throw "Next not supported in DS models"
  | .coalition _ _ =>
      throw "Coalition not supported in DS models; use Gamen.Cgs/Gamen.Coalition"
  | .canNext _ _ => throw "CanNext not supported in DS models; use Gamen.Atl"
  | .canAlways _ _ => throw "CanAlways not supported in DS models; use Gamen.Atl"
  | .canEventually _ _ => throw "CanEventually not supported in DS models; use Gamen.Atl"
  | .canUntil _ _ _ => throw "CanUntil not supported in DS models; use Gamen.Atl"
termination_by f

/-- A formula is true in a DS model if it holds at every world. -/
def dsIsTrueIn (m : DSModel) (f : Formula) : Except String Bool :=
  m.dsFrame.dsWorlds.toList.allM (dsSatisfies m · f)

/-- A formula is DS^k_n-valid if true in every model of the given list.
(For testing small hand-built models, not for general validity.) -/
def dsIsValid (models : List DSModel) (f : Formula) : Except String Bool :=
  models.allM (dsIsTrueIn · f)

-- --------------------------------------------------------------------
-- Frame conditions (Definition 2, p. 843; Lyon & van Berkel 2024)
-- --------------------------------------------------------------------

/-- C1: R_[i] is an equivalence relation for all i. -/
def checkDS_C1 (fr : DSFrame) : Bool :=
  fr.dsRelations.toList.all fun (_, rel) => isEquivalenceOn fr.dsWorlds rel

/-- C2: independence of agents — for any selection of one choice cell
per agent, the intersection is non-empty. -/
def checkDS_C2 (fr : DSFrame) : Bool :=
  checkIndependence (dsAccessible fr) fr.dsRelations.keys fr.dsWorlds

/-- C3: limited choice — each agent has at most `k` choice cells;
`k = 0` means unlimited. -/
def checkDS_C3 (k : Int) (fr : DSFrame) : Bool :=
  if k == 0 then true
  else
    fr.dsRelations.toList.all fun (_, rel) =>
      let cells := (fr.dsWorlds.toList.map fun w => rel.getD w ∅).eraseDupsBy
        (fun s t => s.toList == t.toList)
      (cells.length : Int) ≤ k

/-- D1: ideal worlds are a subset of W. -/
def checkDS_D1 (fr : DSFrame) : Bool :=
  fr.dsIdeals.toList.all fun (_, ideal) => subsetOf ideal fr.dsWorlds

/-- D2: every agent has at least one ideal world. -/
def checkDS_D2 (fr : DSFrame) : Bool :=
  fr.dsIdeals.toList.all fun (_, ideal) => !ideal.isEmpty

/-- D3: ideal worlds fill entire choice cells — if `w` is ideal for
agent `i` and `v ∈ R_[i](w)`, then `v` is also ideal for `i`. -/
def checkDS_D3 (fr : DSFrame) : Bool :=
  fr.dsIdeals.toList.all fun (agent, ideal) =>
    ideal.toList.all fun w => (dsAccessible fr agent w).toList.all fun v => ideal.contains v

/-- All DS frame conditions, with unlimited choice (`checkDS_C3 0`). -/
def isValidDSFrame (fr : DSFrame) : Bool :=
  checkDS_C1 fr && checkDS_C2 fr && checkDS_C3 0 fr
    && checkDS_D1 fr && checkDS_D2 fr && checkDS_D3 fr

-- --------------------------------------------------------------------
-- Normative reasoning applications (Section 5, p. 867; Lyon & van Berkel 2024)
-- --------------------------------------------------------------------

/-- Duty checking: the formulas from `candidates` that are obligatory
for `agent` at `w`, i.e. those `f` with `⊗_agent f` true. -/
def dutyCheck (m : DSModel) (w : World) (agent : String) (candidates : List Formula) :
    Except String (List Formula) :=
  candidates.filterM fun f => dsSatisfies m w (.ought agent f)

/-- Compliance checking: does a proposed choice (the set of worlds
`agent` would select) comply with `agent`'s obligations? A choice is
compliant if it intersects the ideal set. -/
def complianceCheck (m : DSModel) (agent : String) (chosenCell : Std.TreeSet World) : Bool :=
  !(chosenCell ∩ dsIdealSet m.dsFrame agent).isEmpty

/-- Joint fulfillment checking: can `agent` jointly fulfill all `duties`
simultaneously — do they all hold at some single ideal world? -/
def jointFulfillment (m : DSModel) (agent : String) (duties : List Formula) :
    Except String Bool :=
  (dsIdealSet m.dsFrame agent).toList.anyM fun w => duties.allM (dsSatisfies m w ·)

end Gamen
