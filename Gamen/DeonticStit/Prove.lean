import Gamen.Formula
import Gamen.Verdict
import Gamen.DeonticStit.Sequent
import Gamen.DeonticStit.Rules
import Gamen.DeonticStit.Saturation

/-!
# Gamen.DeonticStit.Prove

Port of `gamen-hs/src/Gamen/DeonticStit/Prove.hs`: the proof-search driver
for the deontic STIT calculus G3DS^k_n (Lyon & van Berkel, "Proof Theory and
Decision Procedures for Deontic STIT Logics", *JAIR* 81 (2024), Algorithm 1,
p. 856, listing pp. 858–860; checked against
`pdftotext gamen-hs/notes/LyonBerkel2024.pdf -`).

Bottom-up rule application in three phases:

1. Relational, non-generating: `applyRef`, `applyEuc`, `applyD3`,
   `applyAPC k`.
2. Logical, non-generating: `applyOr`, `applyAnd`, `applyDiamond`,
   `applyChoiceDiamond`, `applyPermitted`.
3. Generating (blocking-aware): `applyBoxB`, `applyStitB`, `applyOughtB`,
   `applyD2B`.

Closure (the (id) rule) is checked before each scheduling attempt; if
`isStable` holds the search stops and returns `refuted` with the current
generation tree and sequent. The driver's `maxSteps` budget is its fuel:
running out is `maxStepsExceeded`, surfaced as `Verdict.unknown`, never as a
definite answer.

The IoaOp operation (Definition 11, p. 851) is *not yet* scheduled by this
driver, as in the Haskell (gamen-hs issue #8 step F): sequents that genuinely
need IOA introductions saturate before the IOA tuples are produced.

*Errors.* The Haskell has no `error` calls, but the blocking predicates
consult `Saturation.ancestors`, which in Lean returns `Except` (a cyclic
parent map is an error there, where the Haskell diverges). So every function
here that reaches a blocking check returns `Except String _`; an error is
propagated, never turned into a verdict. The generation trees built by this
driver never contain a cycle (every child is a fresh label), so the error
path is defensive.

*Deviation.* `maxSteps` is a `Nat` (the Haskell's `Int`): the fuel of a
structural recursion, as in `Tableau.buildTableau`. A negative Haskell
budget behaves like `0` (`steps <= 0` is `maxStepsExceeded`), so only the
`budgetExhausted` payload of a negative budget is lost. `k` stays an `Int`,
matching `applyAPC`/`satAPC`.
-/

namespace Gamen

/-- The outcome of a proof-search attempt.

* `proved`: every branch closed via (id); the input formula is valid in
  DS^k_n (or, when starting from a sequent with extra formulas, the input is
  jointly inconsistent).
* `refuted`: proof search reached a stable sequent; the `GenTree` and
  `Sequent` carry what counter-model extraction needs.
* `maxStepsExceeded`: the `maxSteps` budget ran out before closure or
  stability. Surfaced as `Verdict.unknown`, never as a definite refutation.
* `stuck`: no rule applies *and* the sequent is not stable, a disagreement
  between the schedule and the saturation predicates. Reported as
  `Verdict.unknown`, not as `refuted`. -/
inductive ProveResult where
  | proved
  | refuted (gt : GenTree) (s : Sequent)
  | maxStepsExceeded (gt : GenTree) (s : Sequent)
  | stuck (gt : GenTree) (s : Sequent)
  deriving Repr

-- ====================================================================
-- Blocking-aware generating rules
-- ====================================================================

/-- (□) with the strict saturation condition (C_□) (Definition 18, p. 856):
a witness counts only if it is *unblocked* in the generation tree. -/
def applyBoxB (gt : GenTree) (s : Sequent) : Except String (Option RuleApp) := do
  let ls := (labels s).toList
  let cand ← s.gamma.toList.findSomeM? fun
    | ⟨w, .box phi⟩ => do
      let witnessed ← ls.anyM fun u => do
        return (← isUnblocked u gt s) && hasFormula ⟨u, phi⟩ s
      return if witnessed then none else some (w, phi)
    | _ => pure none
  match cand with
  | none => return none
  | some (w, phi) =>
    let fresh := freshLabel s
    let s' := addFormula ⟨fresh, phi⟩ s
    return some (freshApp [s'] w fresh)

/-- ([i]) with the strict saturation condition (C_[i]) (Definition 18,
p. 856): only *unblocked* principal labels matter, and only a witness
related by `R_[i]` counts. -/
def applyStitB (gt : GenTree) (s : Sequent) : Except String (Option RuleApp) := do
  let ls := (labels s).toList
  let cand ← s.gamma.toList.findSomeM? fun
    | ⟨w, .stit agent phi⟩ => do
      if !(← isUnblocked w gt s) then return none
      let witnessed := ls.any fun u =>
        hasRel (.choice agent w u) s && hasFormula ⟨u, phi⟩ s
      return if witnessed then none else some (w, agent, phi)
    | _ => pure none
  match cand with
  | none => return none
  | some (w, agent, phi) =>
    let fresh := freshLabel s
    let s' := addRel (.choice agent w fresh) (addFormula ⟨fresh, phi⟩ s)
    return some (freshApp [s'] w fresh)

/-- (⊗_i) with the strict saturation condition (C_⊗_i) (Definition 18,
p. 856): a witness counts only if it is *unblocked*. -/
def applyOughtB (gt : GenTree) (s : Sequent) : Except String (Option RuleApp) := do
  let ls := (labels s).toList
  let cand ← s.gamma.toList.findSomeM? fun
    | ⟨w, .ought agent phi⟩ => do
      let witnessed ← ls.anyM fun u => do
        return (← isUnblocked u gt s) && hasRel (.ideal agent u) s
          && hasFormula ⟨u, phi⟩ s
      return if witnessed then none else some (w, agent, phi)
    | _ => pure none
  match cand with
  | none => return none
  | some (w, agent, phi) =>
    let fresh := freshLabel s
    let s' := addRel (.ideal agent fresh) (addFormula ⟨fresh, phi⟩ s)
    return some (freshApp [s'] w fresh)

/-- (D2_i) with the strict saturation condition (C_D2) (Definition 18,
p. 856): an agent counts as having an ideal world only if some *unblocked*
label carries `I_⊗_i`. Fresh labels are parented at `rootLabel`, per the
(D2_i) bullet of Definition 14 (p. 854), which adds the edge `(w, u)` from
the root `w`. (The Haskell cites "Definition 14 Note 4"; footnote 4 of the
paper concerns the ([i]*) clause.) -/
def applyD2B (rootLabel : Label) (gt : GenTree) (s : Sequent) :
    Except String (Option RuleApp) := do
  let ls := (labels s).toList
  let needy ← (sequentAgents s).toList.findSomeM? fun a => do
    let has ← ls.anyM fun u => do
      return (← isUnblocked u gt s) && hasRel (.ideal a u) s
    return if has then none else some a
  match needy with
  | none => return none
  | some a =>
    let fresh := freshLabel s
    let s' := addRel (.ideal a fresh) s
    return some (freshApp [s'] rootLabel fresh)

-- ====================================================================
-- The driver
-- ====================================================================

/-- The phase-ordered rule schedule. Returns `some (gt', premises)` for the
first applicable rule, with the generation tree updated with an edge per
fresh label. Unexported in the Haskell. -/
private def scheduleRule (k : Int) (gt : GenTree) (s : Sequent) :
    Except String (Option (GenTree × List Sequent)) := do
  let applyEdges (app : RuleApp) : GenTree :=
    (app.raParents.zip app.raFreshLabels).foldr (fun (p, c) acc => addGenChild p c acc) gt
  let pureRules : List DeonticStit.Rule :=
    [applyRef, applyEuc, applyD3, applyAPC k,
     applyOr, applyAnd, applyDiamond, applyChoiceDiamond, applyPermitted]
  let treeRules : List (Sequent → Except String (Option RuleApp)) :=
    [applyBoxB gt, applyStitB gt, applyOughtB gt, applyD2B gt.gtRoot gt]
  let rules := pureRules.map (fun r t => pure (r t)) ++ treeRules
  let app? ← rules.findSomeM? (· s)
  return app?.map fun app => (applyEdges app, app.raPremises)

/-- Recursive proof search. `steps` is the fuel: every rule application
spends one step, and each premise is searched with the remaining budget
(as in the Haskell, where `recurseAll` hands `steps - 1` to every premise).
A premise that does not close stops the search with its result. -/
def prove (k : Int) : Nat → GenTree → Sequent → Except String ProveResult
  | 0, gt, s => pure (.maxStepsExceeded gt s)
  | steps + 1, gt, s => do
    if isClosedSequent s then return .proved
    if ← isStable k gt s then return .refuted gt s
    match ← scheduleRule k gt s with
    -- No rule fired, yet the sequent is not stable: a prover defect, not a
    -- refutation.
    | none => return .stuck gt s
    | some (gt', premises) =>
      for prem in premises do
        match ← prove k steps gt' prem with
        | .proved => pure ()
        | r => return r
      return .proved

/-- Try to derive `∅ ⇒ w₀:φ` in G3DS^k_n. The formula is normalized to NNF
before search starts; `maxSteps` caps the recursion depth. -/
def proveFormula (k : Int) (maxSteps : Nat) (phi : Formula) : Except String ProveResult :=
  prove k maxSteps (emptyGenTree label0) (singletonSequent label0 phi.toNNF)

/-- Is `φ` *valid* in DS^k_n? Three-valued: `proved` is definitely true,
`refuted` definitely false; budget exhaustion or a stuck sequent is
`unknown`, never a definite answer. -/
def isFormulaValid (k : Int) (maxSteps : Nat) (phi : Formula) : Except String Verdict := do
  match ← proveFormula k maxSteps phi with
  | .proved => return .definitely true
  | .refuted _ _ => return .definitely false
  | .maxStepsExceeded _ _ => return .unknown (.budgetExhausted maxSteps)
  | .stuck _ _ =>
    return .unknown (.proverStuck "G3DS proof search reached a non-stable dead end")

/-- Is `φ` *satisfiable*? `φ` is satisfiable iff `¬φ` is not valid; negating
the verdict keeps `unknown` unknown. -/
def isFormulaSatisfiable (k : Int) (maxSteps : Nat) (phi : Formula) : Except String Verdict :=
  Verdict.negate <$> isFormulaValid k maxSteps (.not phi)

/-- Is the finite set `{φ₁, …, φₙ}` *jointly consistent*, i.e. is
`φ₁ ∧ … ∧ φₙ` satisfiable? The empty set is vacuously consistent. The
conjunction is built as the Haskell's `foldr And f fs`. -/
def isFormulaSetConsistent (k : Int) (maxSteps : Nat) : List Formula → Except String Verdict
  | [] => pure (.definitely true)
  | f :: fs => isFormulaSatisfiable k maxSteps (fs.foldr .and f)

end Gamen
