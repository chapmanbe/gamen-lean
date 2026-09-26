import Gamen.Formula
import Gamen.Kripke
import Gamen.Tableau

/-!
# Gamen.Temporal

Port of `gamen-hs/src/Gamen/Temporal.hs`: temporal frame-condition tableau
rules, the combined deontic-temporal system KDt, and temporal frame
properties.

Temporal logic is B&D (F25) Chapter 14: the language is Definition 14.2
(p. 184), truth at a point Definition 14.4 (p. 185), and the frame
properties below are the ones in Table 14.1 (p. 186). The semantics
itself lives in `Gamen.Semantics`. B&D gives no temporal tableau; the
rules below follow gamen-hs, which cites BdRV §1.3 for the frame
conditions and builds the rules by analogy to B&D Table 6.3. (gamen-hs's
header says B&D has no temporal chapter; that is true of the Fall 2019
edition, not of the F25 edition this project cites.)

As in gamen-hs, the temporal tableau is quarantined at the
`gamen-validate` fragment boundary (gamen-hs issue #25): `Gamen.Fragment`
rejects every temporal operator, and there are still no core rules for
PastBox/PastDiamond, so the raw prover reports `{HA, P¬A}` satisfiable.
-/
namespace Gamen

/-! ## Temporal tableau rules (analogous to B&D Table 6.3) -/

/-- Used parents of σ on the branch (Haskell's
`Set.filter (isChildOf σ) (usedPrefixes branch)`). -/
private def usedParentsOf (b : Branch) (σ : Prefix) : List Prefix :=
  b.prefixes.toList.filter (σ.isChildOf ·)

/-- Add `mk τ f` for every τ in `targets` not already on the branch. -/
private def propagate (b : Branch) (targets : List Prefix)
    (mk : Prefix → Formula → PrefixedFormula) (f : Formula) : RuleResult :=
  let adds := targets.filterMap fun τ =>
    let pf := mk τ f
    if b.contains pf then none else some pf
  if adds.isEmpty then .noRule else .stack adds

/-- TG rule (reflexive temporal frames): σ T GA → σ T A. -/
def applyTemporalTFutureBoxRule : Rule
  | ⟨σ, .T, .futureBox a⟩, b =>
    let new := pfTrue σ a
    if b.contains new then .noRule else .stack [new]
  | _, _ => .noRule

/-- TF rule (reflexive temporal frames): σ F FA → σ F A. -/
def applyTemporalTFutureDiamondRule : Rule
  | ⟨σ, .F, .futureDiamond a⟩, b =>
    let new := pfFalse σ a
    if b.contains new then .noRule else .stack [new]
  | _, _ => .noRule

/-- 4G rule (transitive temporal frames): σ T GA → σ.n T GA for each used
child σ.n. -/
def applyTemporal4FutureBoxRule : Rule
  | ⟨σ, .T, f@(.futureBox _)⟩, b => propagate b (b.childrenOf σ) pfTrue f
  | _, _ => .noRule

/-- 4F rule (transitive temporal frames): σ F FA → σ.n F FA for each used
child σ.n. -/
def applyTemporal4FutureDiamondRule : Rule
  | ⟨σ, .F, f@(.futureDiamond _)⟩, b => propagate b (b.childrenOf σ) pfFalse f
  | _, _ => .noRule

/-- TH rule (reflexive temporal frames): σ T HA → σ T A. -/
def applyTemporalTPastBoxRule : Rule
  | ⟨σ, .T, .pastBox a⟩, b =>
    let new := pfTrue σ a
    if b.contains new then .noRule else .stack [new]
  | _, _ => .noRule

/-- TP rule (reflexive temporal frames): σ F PA → σ F A. -/
def applyTemporalTPastDiamondRule : Rule
  | ⟨σ, .F, .pastDiamond a⟩, b =>
    let new := pfFalse σ a
    if b.contains new then .noRule else .stack [new]
  | _, _ => .noRule

/-- 4H rule (transitive temporal frames): σ T HA → τ T HA for each used
parent τ of σ. -/
def applyTemporal4PastBoxRule : Rule
  | ⟨σ, .T, f@(.pastBox _)⟩, b => propagate b (usedParentsOf b σ) pfTrue f
  | _, _ => .noRule

/-- 4P rule (transitive temporal frames): σ F PA → τ F PA for each used
parent τ of σ. -/
def applyTemporal4PastDiamondRule : Rule
  | ⟨σ, .F, f@(.pastDiamond _)⟩, b => propagate b (usedParentsOf b σ) pfFalse f
  | _, _ => .noRule

/-! ## Combined deontic-temporal tableau system -/

/-- KDt: combined deontic-temporal logic.

Deontic operators (□/◇) have serial frames (D axiom): the D□/D◇ rules
(B&D Table 6.3) as witness rules. Temporal operators have reflexive and
transitive frames: the T and 4 rules above, for G/F and H/P.

As in gamen-hs, deontic and temporal accessibility share a single
relation (its "Phase 1"). gamen-hs inlines copies of the D rules because
`Tableau.hs` does not export them; `Gamen.Tableau` does, and its
`dBoxRule`/`dDiamondRule` are the same rules. -/
def systemKDt : System :=
  ⟨"KDt",
   [ -- Temporal reflexivity (T axiom): GA → A, HA → A
     applyTemporalTFutureBoxRule, applyTemporalTFutureDiamondRule,
     applyTemporalTPastBoxRule, applyTemporalTPastDiamondRule,
     -- Temporal transitivity (4 axiom): GA → GGA, HA → HHA
     applyTemporal4FutureBoxRule, applyTemporal4FutureDiamondRule,
     applyTemporal4PastBoxRule, applyTemporal4PastDiamondRule ],
   [dBoxRule, dDiamondRule]⟩

/-! ## Temporal frame properties (B&D Table 14.1, p. 186) -/

/-- Is the frame's relation transitive? ∀u v w, (u ≺ v ∧ v ≺ w) → u ≺ w.
Corresponds to FFp → Fp (B&D Table 14.1). Thin wrapper over
`Kripke.transitiveOn`, the shared copy. -/
def isTransitiveFrame (fr : Frame) : Bool :=
  transitiveOn fr.worlds fr.relation

/-- Is the frame's relation linear? ∀w v, w ≺ v ∨ w = v ∨ v ≺ w.
Corresponds to (FPp ∨ PFp) → (Pp ∨ p ∨ Fp) (B&D Table 14.1). -/
def isLinearFrame (fr : Frame) : Bool :=
  let ws := fr.worlds.toList
  ws.all fun w => ws.all fun v =>
    w == v || (fr.accessible w).contains v || (fr.accessible v).contains w

/-- Is the frame dense? ∀w v, w ≺ v → ∃u (w ≺ u ∧ u ≺ v).
Corresponds to Fp → FFp (B&D Table 14.1). -/
def isDenseFrame (fr : Frame) : Bool :=
  fr.worlds.all fun w =>
    (fr.accessible w).all fun v =>
      fr.worlds.any fun u => (fr.accessible w).contains u && (fr.accessible u).contains v

/-- Does the frame have an unbounded past? ∀w ∃v, v ≺ w.
Corresponds to Hp → Pp (B&D Table 14.1). -/
def isUnboundedPast (fr : Frame) : Bool :=
  fr.worlds.all fun w => fr.worlds.any fun v => (fr.accessible v).contains w

/-- Does the frame have an unbounded future? ∀w ∃v, w ≺ v.
Corresponds to Gp → Fp (B&D Table 14.1). -/
def isUnboundedFuture (fr : Frame) : Bool :=
  fr.worlds.all fun w => !(fr.accessible w).isEmpty

end Gamen
