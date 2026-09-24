import Std.Data.TreeMap
import Gamen.Formula
import Gamen.Kripke
import Gamen.Tableau

/-!
# Gamen.RankingTheory

Port of `gamen-hs/src/Gamen/RankingTheory.hs`: Spohn's ordinal conditional
functions (OCFs) for graded doxastic reasoning.

## Background

An OCF is a function κ : W → ℕ assigning each world a *degree of
disbelief*, with κ⁻¹(0) ≠ ∅ (Spohn 1988, Definition 4, p. 115). The agent's
"actual" beliefs are the worlds at rank 0; higher ranks are progressively
more disbelieved. See Spohn (1988), "Ordinal Conditional Functions: A
Dynamic Theory of Epistemic States," in Harper & Skyrms (eds.), *Causation
in Decision, Belief Change, and Statistics II*, pp. 105–134.

For a proposition A ⊆ W, κ(A) = min { κ(w) | w ∈ A }. By Spohn's Theorem
2(a) (p. 115), for every contingent A: κ(A) = 0 ∨ κ(¬A) = 0. The
*two-sided rank* τ(A) = κ(¬A) − κ(A) (Spohn's "firmness," p. 116)
collapses both halves into a single signed integer:

* τ(A) > 0: A is believed with firmness τ(A)
* τ(A) = 0: A is epistemically open (neither A nor ¬A is committed)
* τ(A) < 0: A is disbelieved with firmness |τ(A)|

`Formula.rankedBelief a n φ` asserts the agent's two-sided rank of φ is
*exactly* `n`.

## Module scope (v1)

The static side of ranking theory plus conditionalization (the dynamic
update rule), and two tableau closure rules. Not provided: transfinite
ranks, and any aggregation policy (`combineIndependent` is a documented
primitive; applications must verify its independence precondition, see
Heckerman 1986).

## Differences from the Haskell

* Every `error` is an `Except String` with the Haskell message. Where
  Haskell's laziness or `&&`/`||`/`any`/`all` short-circuiting skips a
  computation that could error, the Lean code skips it too, so the same
  inputs error.
* `Rank` is Lean's unbounded `Int`, not Haskell's 64-bit `Int`. The two
  sentinels Haskell uses (`maxBound`/`minBound` for κ(∅) and for τ of a
  model-valid/model-unsatisfiable formula) are kept with the same values as
  `rankMaxBound`/`rankMinBound`, so outputs are identical.

No B&D definition applies (ranking theory is not a Boxes & Diamonds
topic). Spohn citations were checked against
`gamen-hs/notes/spohn1988-ordinal-conditional-functions.pdf`; the Haskell's
"p. 117" for the "additional reason … strengthened" passage is p. 118 there,
corrected below.
-/
namespace Gamen

/-- A two-sided rank (Spohn's "firmness"). Positive: belief; negative:
disbelief; zero: explicit neutrality. -/
abbrev Rank := Int

/-- Agent identifier: the same string namespace `belief` uses. -/
abbrev Agent := String

/-- Haskell's `maxBound :: Int` (64-bit GHC), the sentinel for κ(∅) = +∞
and τ = +∞. -/
def rankMaxBound : Rank := 9223372036854775807

/-- Haskell's `minBound :: Int` (64-bit GHC), the sentinel for τ = −∞. -/
def rankMinBound : Rank := -9223372036854775808

/-- A ranking-theoretic model: per-agent κ-functions over a shared set of
worlds, plus a propositional valuation.

*Invariant (well-formedness):* for each agent a, the κ-function is defined
on every world in `kWorlds`, takes only non-negative values, and at least
one world has κ_a(w) = 0. See `wellFormed`. -/
structure KappaModel where
  kWorlds : Std.TreeSet World
  /-- κ_a(w) for each agent a, as raw non-negative ranks; τ is derived in `tau`. -/
  kKappa : Std.TreeMap Agent (Std.TreeMap World Int)
  kValuation : Std.TreeMap Atom (Std.TreeSet World)
  deriving Inhabited

/-- Structural equality, as Haskell's derived `Eq`. -/
instance : BEq KappaModel where
  beq m n :=
    m.kWorlds.toList == n.kWorlds.toList
      && m.kKappa.toList.map (fun (a, kw) => (a, kw.toList))
          == n.kKappa.toList.map (fun (a, kw) => (a, kw.toList))
      && m.kValuation.toList.map (fun (a, ws) => (a, ws.toList))
          == n.kValuation.toList.map (fun (a, ws) => (a, ws.toList))

/-- Construct a `KappaModel` from worlds, per-agent κ-tables, and a
propositional valuation. Duplicate keys: the last wins, as with Haskell's
`Map.fromList`. -/
def mkKappaModel (ws : List World) (kappas : List (Agent × List (World × Int)))
    (vals : List (String × List World)) : KappaModel :=
  { kWorlds := Std.TreeSet.ofList ws
    kKappa := Std.TreeMap.ofList (kappas.map fun (a, kvs) => (a, Std.TreeMap.ofList kvs))
    kValuation := Std.TreeMap.ofList
      (vals.map fun (n, wss) => ((⟨n⟩ : Atom), Std.TreeSet.ofList wss)) }

/-- Check the model invariants:

* every agent's κ is total over `kWorlds`
* every κ-value is non-negative
* every agent has at least one world with κ_a(w) = 0 (Spohn Def. 4, p. 115)

Theorem 2(a) (κ(A) = 0 ∨ κ(¬A) = 0) is automatic from the definition
κ(A) = min over A and the existence of a κ_a = 0 world. -/
def wellFormed (m : KappaModel) : Bool :=
  m.kKappa.toList.all fun (_, kw) =>
    kw.keys == m.kWorlds.toList          -- total over kWorlds
      && kw.values.all (· ≥ 0)           -- non-negative
      && kw.values.contains 0            -- at least one zero

/-- κ_a(w): the agent's degree of disbelief in the singleton {w}. Errors if
the agent is unknown or the world isn't in the agent's κ-table. -/
def kappaWorld (m : KappaModel) (a : Agent) (w : World) : Except String Int :=
  match m.kKappa.get? a with
  | none => throw s!"kappaWorld: unknown agent {repr a}"
  | some kw =>
    match kw.get? w with
    | none => throw s!"kappaWorld: world {repr w} not in agent {repr a}'s κ-table"
    | some k => pure k

/-- κ_a(A) = min { κ_a(w) | w ∈ A } (Spohn Def. 4, p. 115). By convention
κ_a(∅) = +∞, reported as the `rankMaxBound` sentinel. Callers must not do
arithmetic on the sentinel; `tau` handles the empty-side cases explicitly. -/
def kappaProp (m : KappaModel) (a : Agent) (as : Std.TreeSet World) : Except String Int := do
  match as.toList with
  | [] => pure rankMaxBound
  | w :: rest =>
    let k0 ← kappaWorld m a w
    rest.foldlM (fun acc w' => return min acc (← kappaWorld m a w')) k0

mutual

/-- The propositional truth set ⟦φ⟧ ⊆ W. Defined for the propositional
fragment plus `rankedBelief` (global per agent). Every world is evaluated,
in ascending order, as Haskell's `Set.filter` does. -/
def truthSet (m : KappaModel) (phi : Formula) : Except String (Std.TreeSet World) := do
  let ws ← m.kWorlds.toList.filterM fun w => propSat m w phi
  return Std.TreeSet.ofList ws

/-- τ_a(φ) = κ_a(¬⟦φ⟧) − κ_a(⟦φ⟧): the agent's two-sided rank (Spohn's
firmness, p. 116). By Theorem 2(a) (p. 115) one of the two is zero, so τ is
well-defined and signed.

The empty-side cases are handled explicitly rather than by subtracting the
κ(∅) sentinel: if φ is valid in the model (⟦¬φ⟧ = ∅) τ is +∞, reported as
`rankMaxBound`; if φ is unsatisfiable in the model (⟦φ⟧ = ∅) it is −∞,
reported as `rankMinBound`. A model with no worlds is an error. -/
def tau (m : KappaModel) (a : Agent) (phi : Formula) : Except String Rank := do
  let truePhi ← truthSet m phi
  let falsePhi := m.kWorlds.filter (!truePhi.contains ·)
  if truePhi.isEmpty && falsePhi.isEmpty then
    throw "tau: model has no worlds"
  else if falsePhi.isEmpty then pure rankMaxBound  -- φ valid in model: τ = +∞
  else if truePhi.isEmpty then pure rankMinBound   -- φ unsatisfiable: τ = −∞
  else
    let kf ← kappaProp m a falsePhi
    let kt ← kappaProp m a truePhi
    pure (kf - kt)

/-- Local satisfaction in the propositional fragment, used by `truthSet`.
`rankedBelief` assertions are global, evaluated via `tau` (same answer at
every world). `∧`/`∨`/`→` short-circuit as Haskell's `&&`/`||` do. -/
def propSat (m : KappaModel) (w : World) : Formula → Except String Bool
  | .bot => pure false
  | .atomF a => pure ((m.kValuation.getD a ∅).contains w)
  | .not f => return !(← propSat m w f)
  | .and l r => do if ← propSat m w l then propSat m w r else pure false
  | .or l r => do if ← propSat m w l then pure true else propSat m w r
  | .implies l r => do if ← propSat m w l then propSat m w r else pure true
  | .iff l r => return (← propSat m w l) == (← propSat m w r)
  | .rankedBelief a n f => return (← tau m a f) == n
  | f => throw s!"Gamen.RankingTheory.propSat: unsupported operator in operand: {f} (the operand of RankedBelief must be propositional)"

end

/-- Satisfaction at a world for ranking-theoretic models. Most cases are
local; `rankedBelief` is global to the agent's κ-function and so does not
depend on `w` beyond the world-existence guard. -/
def kappaSat (m : KappaModel) (w : World) (f : Formula) : Except String Bool :=
  if !m.kWorlds.contains w then
    throw s!"kappaSat: world {repr w} is not in model"
  else propSat m w f

/-- Is the formula set jointly satisfiable in *this* model? True iff some
world satisfies every formula. Short-circuits like Haskell's `any`/`all`. -/
def kappaConsistent (m : KappaModel) (fs : List Formula) : Except String Bool :=
  m.kWorlds.toList.anyM fun w => fs.allM (kappaSat m w)

/-! ## Conditionalization (Spohn Def. 6, p. 117) -/

/-- The guards of `conditionalize`, in Haskell's order, returning
(⟦φ⟧, W ∖ ⟦φ⟧). Split out so `applyEvidence` checks them before computing
τ, as Haskell's lazy `conditionalize m a φ (tau m a φ + δ)` does. -/
private def conditionalizeGuards (m : KappaModel) (a : Agent) (phi : Formula) :
    Except String (Std.TreeSet World × Std.TreeSet World) := do
  if !m.kKappa.contains a then
    throw s!"conditionalize: unknown agent {repr a}"
  let truePhi ← truthSet m phi
  let falsePhi := m.kWorlds.filter (!truePhi.contains ·)
  if truePhi.isEmpty then
    throw "conditionalize: cannot condition on a model-contradiction (⟦φ⟧ = ∅)"
  if falsePhi.isEmpty then
    throw "conditionalize: cannot condition on a model-tautology (⟦φ⟧ = W)"
  return (truePhi, falsePhi)

/-- The update of agent `a`'s κ-table, given the guards' output. -/
private def conditionalizeUpdate (m : KappaModel) (a : Agent)
    (truePhi falsePhi : Std.TreeSet World) (n : Rank) : KappaModel :=
  -- Which side is shifted up by |n|, and which is the new κ = 0 anchor.
  let (raised, anchored, shift) :=
    if n ≥ 0 then (falsePhi, truePhi, n) else (truePhi, falsePhi, -n)
  let minOver (s : Std.TreeSet World) (kw : Std.TreeMap World Int) : Int :=
    match s.toList.map (kw.getD · 0) with
    | [] => 0
    | k :: ks => ks.foldl min k
  let update (kw : Std.TreeMap World Int) : Std.TreeMap World Int :=
    let kAnchor := minOver anchored kw
    let kRaised := minOver raised kw
    kw.map fun w k => if anchored.contains w then k - kAnchor else (k - kRaised) + shift
  { m with kKappa := m.kKappa.modify a update }

/-- A,α-conditionalization (Spohn 1988, Def. 6, p. 117). Updates agent `a`'s
κ-function so that:

* the A-part keeps its internal grading but is shifted to start at 0
* the ¬A-part keeps its internal grading but is shifted to start at α

where A = ⟦φ⟧ and α = |n|; the sign of `n` chooses which side is raised:
positive `n` makes φ believed with firmness `n`, negative `n` makes φ
disbelieved with firmness `|n|`.

*This is overwrite semantics, faithful to Spohn.* `conditionalize m a φ 2`
then `conditionalize _ a φ 1` leaves τ(φ) = 1, not 3. Spohn (1988, p. 118;
the Haskell says p. 117): "if α > β, then one has got additional reason for
A whereby the belief in A is strengthened": α is the *resulting* firmness,
not an increment. For additive aggregation use `applyEvidence`.

Def. 6 requires A ∉ {∅, W}: conditioning on a model-contradiction or a
model-tautology is an error (it would leave no κ = 0 world). -/
def conditionalize (m : KappaModel) (a : Agent) (phi : Formula) (n : Rank) :
    Except String KappaModel := do
  let (truePhi, falsePhi) ← conditionalizeGuards m a phi
  return conditionalizeUpdate m a truePhi falsePhi n

/-- Apply a piece of evidence *additively* to the current firmness:
`applyEvidence m a φ δ` reads τ_a(φ), adds δ, and conditionalizes to the
result.

*Independence caveat.* Successive calls implicitly assume the evidence
pieces are independent (cf. `combineIndependent`); a domain judgement, not
enforced by the API.

Haskell passes τ + δ to `conditionalize` as a lazy thunk, and only the
`Map.mapWithKey` over the agent's κ-table forces it. So `conditionalize`'s
guards run first, and τ is computed exactly when the agent's κ-table is
non-empty; with an empty table the model comes back unchanged (what
`Map.adjust` over an empty table yields), even where τ would error. -/
def applyEvidence (m : KappaModel) (a : Agent) (phi : Formula) (delta : Rank) :
    Except String KappaModel := do
  let (truePhi, falsePhi) ← conditionalizeGuards m a phi
  if (m.kKappa.getD a ∅).isEmpty then return m
  let t ← tau m a phi
  return conditionalizeUpdate m a truePhi falsePhi (t + delta)

/-! ## Evidence combination -/

/-- Combine two two-sided ranks under the *independence* assumption
(Spohn 1988, Theorem 7, p. 121: κ(B ∩ C) = κ(B) + κ(C)).

*Warning.* This is integer addition, sound only when the two evidence
sources are stipulated independent; on dependent evidence it is the same
error as combining MYCIN certainty factors that silently assume conditional
independence (Heckerman 1986). This function does not check the
precondition. -/
def combineIndependent (x y : Rank) : Rank := x + y

/-! ## Belief ↔ RankedBelief translation -/

/-- Convert binary `belief` to `rankedBelief` at a fixed firmness, recursing
through every constructor. Existing `rankedBelief`s keep their rank. -/
def beliefToRanked (n : Rank) : Formula → Formula
  | .bot => .bot
  | .atomF a => .atomF a
  | .not f => .not (beliefToRanked n f)
  | .and l r => .and (beliefToRanked n l) (beliefToRanked n r)
  | .or l r => .or (beliefToRanked n l) (beliefToRanked n r)
  | .implies l r => .implies (beliefToRanked n l) (beliefToRanked n r)
  | .iff l r => .iff (beliefToRanked n l) (beliefToRanked n r)
  | .box f => .box (beliefToRanked n f)
  | .diamond f => .diamond (beliefToRanked n f)
  | .futureBox f => .futureBox (beliefToRanked n f)
  | .futureDiamond f => .futureDiamond (beliefToRanked n f)
  | .pastBox f => .pastBox (beliefToRanked n f)
  | .pastDiamond f => .pastDiamond (beliefToRanked n f)
  | .since l r => .since (beliefToRanked n l) (beliefToRanked n r)
  | .until l r => .until (beliefToRanked n l) (beliefToRanked n r)
  | .knowledge a f => .knowledge a (beliefToRanked n f)
  | .belief a f => .rankedBelief a n (beliefToRanked n f)
  | .rankedBelief a m f => .rankedBelief a m (beliefToRanked n f)
  | .announce b c => .announce (beliefToRanked n b) (beliefToRanked n c)
  | .stit a f => .stit a (beliefToRanked n f)
  | .choiceDiamond a f => .choiceDiamond a (beliefToRanked n f)
  | .groupStit f => .groupStit (beliefToRanked n f)
  | .next f => .next (beliefToRanked n f)
  | .ought a f => .ought a (beliefToRanked n f)
  | .permitted a f => .permitted a (beliefToRanked n f)
  | .coalition c f => .coalition c (beliefToRanked n f)
  | .canNext c f => .canNext c (beliefToRanked n f)
  | .canAlways c f => .canAlways c (beliefToRanked n f)
  | .canEventually c f => .canEventually c (beliefToRanked n f)
  | .canUntil c l r => .canUntil c (beliefToRanked n l) (beliefToRanked n r)

/-- Convert `rankedBelief` assertions of nonzero firmness back to binary
`belief` (negative rank: belief in the negated operand). `none` if any
rank-0 (neutral) assertion occurs, which has no binary-belief equivalent.
Other constructors pass through. -/
def rankedToBelief : Formula → Option Formula
  | .rankedBelief a n f =>
    if n > 0 then .belief a <$> rankedToBelief f
    else if n < 0 then (.belief a ∘ .not) <$> rankedToBelief f
    else none
  | .bot => some .bot
  | .atomF a => some (.atomF a)
  | .not f => .not <$> rankedToBelief f
  | .and l r => .and <$> rankedToBelief l <*> rankedToBelief r
  | .or l r => .or <$> rankedToBelief l <*> rankedToBelief r
  | .implies l r => .implies <$> rankedToBelief l <*> rankedToBelief r
  | .iff l r => .iff <$> rankedToBelief l <*> rankedToBelief r
  | .box f => .box <$> rankedToBelief f
  | .diamond f => .diamond <$> rankedToBelief f
  | .futureBox f => .futureBox <$> rankedToBelief f
  | .futureDiamond f => .futureDiamond <$> rankedToBelief f
  | .pastBox f => .pastBox <$> rankedToBelief f
  | .pastDiamond f => .pastDiamond <$> rankedToBelief f
  | .since l r => .since <$> rankedToBelief l <*> rankedToBelief r
  | .until l r => .until <$> rankedToBelief l <*> rankedToBelief r
  | .knowledge a f => .knowledge a <$> rankedToBelief f
  | .belief a f => .belief a <$> rankedToBelief f
  | .announce b c => .announce <$> rankedToBelief b <*> rankedToBelief c
  | .stit a f => .stit a <$> rankedToBelief f
  | .choiceDiamond a f => .choiceDiamond a <$> rankedToBelief f
  | .groupStit f => .groupStit <$> rankedToBelief f
  | .next f => .next <$> rankedToBelief f
  | .ought a f => .ought a <$> rankedToBelief f
  | .permitted a f => .permitted a <$> rankedToBelief f
  | .coalition c f => .coalition c <$> rankedToBelief f
  | .canNext c f => .canNext c <$> rankedToBelief f
  | .canAlways c f => .canAlways c <$> rankedToBelief f
  | .canEventually c f => .canEventually c <$> rankedToBelief f
  | .canUntil c l r => .canUntil c <$> rankedToBelief l <*> rankedToBelief r

/-! ## Tableau closure rules

Two structural laws fall out of the signed reading of
`rankedBelief a n φ` ≡ τ_a(φ) = n:

1. *Functionality.* τ_a(φ) is a function of the agent's state, so
   `σ T rankedBelief a n φ` and `σ T rankedBelief a m φ` with n ≠ m jointly
   contradict.
2. *Negation symmetry.* τ_a(¬φ) = −τ_a(φ), so `σ T rankedBelief a n φ` and
   `σ T rankedBelief a m (¬φ)` jointly contradict whenever m ≠ −n.

On a violation each rule stacks `σ F rankedBelief a n φ`, closing the
branch by the standard T/F closure. -/

/-- Functionality closure: if the branch already asserts the same
ranked-belief operand at a different rank for the same agent and prefix,
derive `F` of the current assertion. -/
def applyRankedFunctionalityRule : Rule
  | ⟨σ, .T, .rankedBelief a n phi⟩, b =>
    let conflict (pf : PrefixedFormula) : Bool :=
      pf.pfx == σ && pf.sign == .T &&
        match pf.formula with
        | .rankedBelief a' m psi => a' == a && psi == phi && m != n
        | _ => false
    if b.formulas.any conflict then
      let new := pfFalse σ (.rankedBelief a n phi)
      if b.contains new then .noRule else .stack [new]
    else .noRule
  | _, _ => .noRule

/-- Negation-symmetry closure: τ_a(¬φ) = −τ_a(φ), so paired assertions of
`rankedBelief a n φ` and `rankedBelief a m (¬φ)` with m ≠ −n close the
branch. The second alternative handles the current assertion being itself
the negated form (φ = ¬φ'). As in Haskell, an other-formula whose operand
is a negation is matched only by the first alternative. -/
def applyRankedNegationSymmetryRule : Rule
  | ⟨σ, .T, .rankedBelief a n phi⟩, b =>
    let conflict (pf : PrefixedFormula) : Bool :=
      pf.pfx == σ && pf.sign == .T &&
        match pf.formula with
        | .rankedBelief a' m (.not psi) => a' == a && psi == phi && m != -n
        | .rankedBelief a' m psi =>
          match phi with
          | .not phi' => a' == a && psi == phi' && m != -n
          | _ => false
        | _ => false
    if b.formulas.any conflict then
      let new := pfFalse σ (.rankedBelief a n phi)
      if b.contains new then .noRule else .stack [new]
    else .noRule
  | _, _ => .noRule

/-- Both ranking-theory closure rules. Add to the `usedPrefixRules` of a
`System` to enable consistency checking over `rankedBelief` assertions. -/
def rankingRules : List Rule := [applyRankedFunctionalityRule, applyRankedNegationSymmetryRule]

end Gamen
