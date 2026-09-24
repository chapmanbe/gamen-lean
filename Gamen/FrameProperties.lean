import Gamen.Formula
import Gamen.Kripke
import Gamen.Semantics

/-!
# Gamen.FrameProperties

Port of `gamen-hs/src/Gamen/FrameProperties.hs`: predicates on Kripke
frames and brute-force frame validity checking.

The B&D numbers cited below were checked against `notes/bd-screen.pdf`
directly (`pdftotext`), not copied from the Haskell docstrings. Two of
the Haskell citations turned out to be wrong for this PDF and are
corrected here (see `PORTING.md` / the porting report for detail):
the basic properties (reflexive, symmetric, ...) live in B&D Table 2.1,
not "Definition 2.3" (which is the frame ⟨W,R⟩ itself), and frame
validity is B&D Definition 2.4, not "Definition 2.1" (there is no
Definition 2.1 in Chapter 2). gamen-hs's own "frd.N" tags for Definition
2.11, Proposition 2.9, Proposition 2.12, and Proposition 2.14 all check
out against the real chapter-2 numbering, so those are spelled out
directly here instead of kept as an internal alias.
-/
namespace Gamen

-- --------------------------------------------------------------------
-- Basic frame properties (B&D Table 2.1, §2.2)
-- --------------------------------------------------------------------

/-- A frame is reflexive if every world accesses itself: ∀w, Rww
(B&D Table 2.1). Thin wrapper over `Kripke.reflexiveOn`, the shared
copy used by `Kripke.isEquivalenceOn` and (when ported) `Stit`'s and
`Temporal`'s transitivity checks — see `docs/assessment/lean-library-
reuse-2026-09-23.md` §2. -/
def isReflexive (fr : Frame) : Bool :=
  reflexiveOn fr.worlds fr.relation

/-- A frame is symmetric if ∀w w', Rww' → Rw'w (B&D Table 2.1). Thin
wrapper over `Kripke.symmetricOn` (see `isReflexive`). -/
def isSymmetric (fr : Frame) : Bool :=
  symmetricOn fr.worlds fr.relation

/-- A frame is transitive if ∀w w' w'', (Rww' ∧ Rw'w'') → Rww''
(B&D Table 2.1). Thin wrapper over `Kripke.transitiveOn` (see
`isReflexive`). -/
def isTransitive (fr : Frame) : Bool :=
  transitiveOn fr.worlds fr.relation

/-- A frame is serial if every world has at least one successor
(B&D Table 2.1). -/
def isSerial (fr : Frame) : Bool :=
  fr.worlds.all fun w => !(fr.accessible w).isEmpty

/-- A frame is euclidean if ∀w w' w'', (Rww' ∧ Rww'') → Rw'w''
(B&D Table 2.1). -/
def isEuclidean (fr : Frame) : Bool :=
  fr.worlds.all fun w =>
    let succs := fr.accessible w
    succs.all fun v => subsetOf succs (fr.accessible v)

-- --------------------------------------------------------------------
-- Additional frame properties (B&D Table 2.2, §2.4)
-- --------------------------------------------------------------------

/-- Partially functional: every world has at most one successor
(B&D Table 2.2). -/
def isPartiallyFunctional (fr : Frame) : Bool :=
  fr.worlds.all fun w => (fr.accessible w).size <= 1

/-- Functional: every world has exactly one successor, and that
successor is a world of the frame (B&D Table 2.2). Checking membership
in `worlds` (not just the count) mirrors gamen-hs's adversarial-review
fix B7: a dangling edge to a non-world can't masquerade as the single
successor. -/
def isFunctional (fr : Frame) : Bool :=
  fr.worlds.all fun w =>
    let succs := fr.accessible w
    succs.size == 1 && subsetOf succs fr.worlds

/-- Weakly dense: every step decomposes into two steps —
∀u v, Ruv → ∃w, (Ruw ∧ Rwv) (B&D Table 2.2). -/
def isWeaklyDense (fr : Frame) : Bool :=
  fr.worlds.all fun u =>
    (fr.accessible u).all fun v =>
      fr.worlds.any fun w => (fr.accessible u).contains w && (fr.accessible w).contains v

/-- Weakly connected: any two successors are related or identical —
∀w u v, (Rwu ∧ Rwv) → (Ruv ∨ u=v ∨ Rvu) (B&D Table 2.2). -/
def isWeaklyConnected (fr : Frame) : Bool :=
  fr.worlds.all fun w =>
    let succs := fr.accessible w
    succs.all fun u =>
      succs.all fun v =>
        (fr.accessible u).contains v || u == v || (fr.accessible v).contains u

/-- Weakly directed (confluence): any two successors have a common
successor — ∀w u v, (Rwu ∧ Rwv) → ∃t, (Rut ∧ Rvt) (B&D Table 2.2). -/
def isWeaklyDirected (fr : Frame) : Bool :=
  fr.worlds.all fun w =>
    let succs := fr.accessible w
    succs.all fun u =>
      succs.all fun v =>
        fr.worlds.any fun t => (fr.accessible u).contains t && (fr.accessible v).contains t

-- --------------------------------------------------------------------
-- Equivalence and universality (B&D Definition 2.11)
-- --------------------------------------------------------------------

/-- The accessibility relation is an equivalence relation iff it is
reflexive, symmetric, and transitive (B&D Definition 2.11). -/
def isEquivalenceRelation (fr : Frame) : Bool :=
  isReflexive fr && isSymmetric fr && isTransitive fr

/-- A frame is universal if every world accesses every world
(B&D Definition 2.11). This checks *coverage* (`worlds ⊆ R(w)`) rather
than comparing successor counts, mirroring gamen-hs's adversarial-review
fix B7: a successor set with the right cardinality but a dangling edge
and a missing world can no longer masquerade as universal. -/
def isUniversal (fr : Frame) : Bool :=
  fr.worlds.all fun w => subsetOf fr.worlds (fr.accessible w)

-- --------------------------------------------------------------------
-- Frame validity (B&D Definition 2.4)
-- --------------------------------------------------------------------

/-- Decode the `i`-th valuation of `vs` over `nWorlds` worlds, low bits
first per variable (a mixed-radix encoding of `i` in base `2 ^ nWorlds`).
Port of the `where`-bound `buildValuation` in the Haskell source. -/
private def buildValuation (worldList : List World) (nWorlds : Nat) :
    Nat → List String → List (String × List World)
  | _, [] => []
  | remaining, v :: vs =>
      let mask := (1 <<< nWorlds) - 1
      let bits := remaining &&& mask
      let rest := remaining >>> nWorlds
      let ws := (List.range nWorlds).filterMap fun j =>
        if bits &&& (1 <<< j) != 0 then worldList[j]? else none
      (v, ws) :: buildValuation worldList nWorlds rest vs

/-- A formula is valid on a frame if it is true in every model based on
that frame (B&D Definition 2.4: `F ⊨ A` iff `M ⊩ A` for every model `M`
based on `F`). Enumerates all valuations of the formula's atoms over the
frame's worlds, so only tractable for small frames and formulas. -/
def isValidOnFrame (fr : Frame) (formula : Formula) : Except String Bool :=
  let vars := formula.atoms
  if vars.isEmpty then
    -- No propositional variables — just check with the empty valuation.
    isTrueIn (mkModel fr []) formula
  else
    let varList := vars.toList.map Atom.name
    let worldList := fr.worlds.toList
    let nWorlds := worldList.length
    let nValuations : Nat := (2 ^ nWorlds) ^ varList.length
    (List.range nValuations).allM fun i =>
      isTrueIn (mkModel fr (buildValuation worldList nWorlds i varList)) formula

end Gamen
