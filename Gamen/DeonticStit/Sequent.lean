import Gamen.Formula
import Std.Data.TreeSet

/-!
# Gamen.DeonticStit.Sequent

Port of `gamen-hs/src/Gamen/DeonticStit/Sequent.hs`: labeled sequent data
types for the deontic STIT calculus G3DS^k_n (Lyon & van Berkel, "Proof
Theory and Decision Procedures for Deontic STIT Logics", *Journal of
Artificial Intelligence Research* 81 (2024), pp. 837–876; local copy
`notes/LyonBerkel2024.pdf`, checked with `pdftotext -l 1`).

A sequent has the form

> ℛ ⇒ Γ

where ℛ is a set of *relational atoms* — either choice relations `R_[i] w u`
(`RelAtom.choice`) or ideal-set predicates `I_⊗_i w` (`RelAtom.ideal`) — and
Γ is a set of *labeled formulas* `w : φ` (`LabFormula`). This is Definition 4
(p. 846 of the paper; checked against `pdftotext notes/LyonBerkel2024.pdf -`).

*Invariant.* Every formula attached to a label inside a `Sequent` is in
Negation Normal Form (see `Gamen.Formula.toNNF`, `isNNF`). The smart
constructor `mkLabFormula` enforces this; client code that builds
`LabFormula` values directly is responsible for upholding the invariant.

No B&D citations in this module — the only citations are to Lyon & van
Berkel (2024), external to `bd-screen.pdf`, and are checked here against
`notes/LyonBerkel2024.pdf` rather than taken from the Haskell's docstrings
verbatim.
-/
namespace Gamen

-- ====================================================================
-- Labels
-- ====================================================================

/-- A label denotes a world in the model. Labels are drawn from a
denumerable set; we use `Nat` under the hood (Haskell uses `Int`, but no
label is ever negative: `label0 = 0`, `nextLabel` only increments, and
`freshLabel` only ever returns a non-negative candidate) and provide
`ToString` so `⟨0⟩` prints as `w0`, matching the `w₀, w₁, …` convention of
Lyon & van Berkel. -/
structure Label where
  unLabel : Nat
  deriving BEq, Ord, Hashable, Repr, DecidableEq, Inhabited

instance : ToString Label := ⟨fun l => s!"w{l.unLabel}"⟩

/-- The initial label `w₀`, used as the root of proof search. -/
def label0 : Label := ⟨0⟩

/-- Successor label, useful when introducing fresh labels by hand. -/
def nextLabel (l : Label) : Label := ⟨l.unLabel + 1⟩

-- ====================================================================
-- Agents and relational atoms
-- ====================================================================

-- Haskell declares `type Agent = String` locally ("so this module can
-- stand alone"); Lean writes `String` directly instead of a new top-level
-- `Agent` alias, since `Gamen.Agent` already exists (`RankingTheory.lean`,
-- a different subsystem this module does not depend on per its Haskell
-- import list, which is `Gamen.Formula` only) and declaring a second
-- `Gamen.Agent` would collide with it wherever both modules are imported
-- together (as `Tests/Main.lean` does).

/-- A relational atom in a sequent's antecedent.

Two shapes, mirroring Lyon-Berkel Definition 4:

* `choice i w u` encodes `R_[i] w u` — agent `i`'s choice relation relates
  labels `w` and `u`.
* `ideal i w` encodes `I_⊗_i w` — label `w` is in agent `i`'s deontically
  optimal set. -/
inductive RelAtom where
  | choice (i : String) (w u : Label)
  | ideal (i : String) (w : Label)
  deriving BEq, Ord, Hashable, Repr, DecidableEq, Inhabited

instance : ToString RelAtom where
  toString
    | .choice i w u => s!"R_[{i}]{w}{u}"
    | .ideal i w => s!"I_⊗_{i} {w}"

-- ====================================================================
-- Labeled formulas
-- ====================================================================

/-- A formula prefixed with a label, written `w : φ`.

`lfFormula` is required to be in NNF — see `Gamen.Formula.toNNF`. Use
`mkLabFormula` to enforce this when constructing values from arbitrary
input. -/
structure LabFormula where
  lfLabel : Label
  lfFormula : Formula
  deriving BEq, Ord, Hashable, Repr, DecidableEq, Inhabited

instance : ToString LabFormula := ⟨fun lf => s!"{lf.lfLabel}:{lf.lfFormula}"⟩

/-- Smart constructor: normalise the formula to NNF before pairing with the
label, so the sequent invariant is upheld even if the caller hands in
`implies`/`iff`/non-NNF negations. -/
def mkLabFormula (w : Label) (f : Formula) : LabFormula := ⟨w, f.toNNF⟩

-- ====================================================================
-- Sequents
-- ====================================================================

/-- A labeled sequent: relational atoms (the antecedent ℛ) on the left of
`⇒`, labeled formulas (the consequent Γ) on the right.

Both sides are `Std.TreeSet`s to avoid duplicates and give `O(log n)`
membership tests, as Haskell's `Data.Set`. `Sequent` derives `BEq`/`Repr`
(both available for `Std.TreeSet`, unlike `Ord`/`Hashable`/`DecidableEq`,
which `Std.TreeSet` does not provide); the Haskell also derives `Ord`, not
needed by anything in this module. -/
structure Sequent where
  rels : Std.TreeSet RelAtom
  gamma : Std.TreeSet LabFormula
  deriving BEq, Repr

instance : ToString Sequent where
  toString s :=
    let rPart := if s.rels.isEmpty then "" else
      String.intercalate " " (s.rels.toList.map toString) ++ " "
    let gPart := String.intercalate " " (s.gamma.toList.map toString)
    rPart ++ "⇒ " ++ gPart

/-- The empty sequent: no relational atoms, no labeled formulas. -/
def emptySequent : Sequent := { rels := ∅, gamma := ∅ }

/-- Sequent containing exactly one labeled formula and nothing else. Used
to seed proof search from an input formula φ as `∅ ⇒ w₀:φ`. The formula is
normalised to NNF. -/
def singletonSequent (w : Label) (f : Formula) : Sequent :=
  { rels := ∅, gamma := (∅ : Std.TreeSet LabFormula).insert (mkLabFormula w f) }

/-- Add a relational atom to the antecedent. Set-based: idempotent. -/
def addRel (r : RelAtom) (s : Sequent) : Sequent := { s with rels := s.rels.insert r }

/-- Add a labeled formula to the consequent. Set-based: idempotent. The
caller is expected to have NNF'd the formula already (use `mkLabFormula` if
unsure). -/
def addFormula (lf : LabFormula) (s : Sequent) : Sequent := { s with gamma := s.gamma.insert lf }

/-- `O(log n)` membership in the antecedent. -/
def hasRel (r : RelAtom) (s : Sequent) : Bool := s.rels.contains r

/-- `O(log n)` membership in the consequent. -/
def hasFormula (lf : LabFormula) (s : Sequent) : Bool := s.gamma.contains lf

private def relLabels (rs : Std.TreeSet RelAtom) : Std.TreeSet Label :=
  rs.foldl (fun acc r => match r with
    | .choice _ w u => (acc.insert w).insert u
    | .ideal _ w => acc.insert w) ∅

private def formulaLabels (gs : Std.TreeSet LabFormula) : Std.TreeSet Label :=
  Std.TreeSet.ofList (gs.toList.map (·.lfLabel))

/-- All labels mentioned anywhere in the sequent — both endpoints of
relational atoms and the prefixes of labeled formulas. -/
def labels (s : Sequent) : Std.TreeSet Label :=
  (relLabels s.rels).union (formulaLabels s.gamma)

/-- A label not currently appearing in the sequent. Picks the smallest
non-negative `Label n` unused on either side.

At most `(labels s).size` labels can be in use, so one of the first
`(labels s).size + 1` candidates `w0, w1, …` is fresh — this bound replaces
Haskell's unbounded `go (n + 1)` and makes the search visibly terminating
(the same pigeonhole argument as `Tableau.freshPrefix`). The `getD`
fallback is unreachable by that argument, exactly as in `freshPrefix`. -/
def freshLabel (s : Sequent) : Label :=
  let used := labels s
  let candidates := (List.range (used.size + 1)).map (Label.mk ·)
  (candidates.find? (fun l => !used.contains l)).getD ⟨used.size + 1⟩

/-- Replace every occurrence of label `u` with label `w` throughout the
sequent. Mirrors the Λ(w/u) substitution used by Lyon-Berkel in
admissibility lemmas (the `(Sub)` structural rule, Section 3, p. 849 —
checked against `pdftotext notes/LyonBerkel2024.pdf -`). -/
def substLabel (u w : Label) (s : Sequent) : Sequent :=
  let sub (x : Label) : Label := if x == u then w else x
  { rels := Std.TreeSet.ofList (s.rels.toList.map fun
      | .choice i a b => RelAtom.choice i (sub a) (sub b)
      | .ideal i a => RelAtom.ideal i (sub a))
    gamma := Std.TreeSet.ofList (s.gamma.toList.map fun lf => { lf with lfLabel := sub lf.lfLabel }) }

end Gamen
