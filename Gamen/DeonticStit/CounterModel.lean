import Gamen.Formula
import Gamen.Kripke
import Gamen.DeonticStit
import Gamen.DeonticStit.Sequent
import Gamen.DeonticStit.Rules
import Gamen.DeonticStit.Saturation
import Std.Data.TreeMap
import Std.Data.TreeSet

/-!
# Gamen.DeonticStit.CounterModel

Port of `gamen-hs/src/Gamen/DeonticStit/CounterModel.hs`: counter-model
extraction from a stable sequent (Lyon & van Berkel, *JAIR* 2024,
Definition 20, pp. 858–859; checked against
`pdftotext gamen-hs/notes/LyonBerkel2024.pdf -`).

When the proof-search driver returns `.refuted gt s`, the sequent `s` is
stable under the generation tree `gt`. `extractDSModel` builds the
corresponding *stability model*, which falsifies the input formula at `w₀`
(the root label) and serves as the counter-model witness.

## Construction (Definition 20)

* `W^Λ` — the unblocked labels in `Λ`.
* `R_[i]^Λ` — the Euclidean closure of `S_[i]^Λ`, where `(w, u) ∈ S_[i]^Λ`
  iff (i) `R_[i]wu ∈ ℛ` with both endpoints unblocked, or (ii) `R_[i]wv ∈ ℛ`
  with `w` unblocked and `v` directly blocked by `u`, where `u` is a
  *proper ancestor* of `v` (the loop-node redirection). Blocking is
  ancestor-relative (Definition 16, p. 855), so the redirection target must
  be an ancestor of `v`, not any unblocked label with matching content
  (adversarial review B6).
* `I_⊗_i^Λ` — labels `w` with `I_⊗_i w ∈ ℛ` that are unblocked.
* `V^Λ(p)` — labels `w` with `w:¬p ∈ Γ` that are unblocked. Note the
  polarity flip: a literal `w:¬p` in the consequent of a stable sequent says
  "we have failed to derive `w:p`", so the counter-model makes `p` false
  at `w`.

Deviations from the Haskell: `euclideanClose` returns `Except` (it runs
through the shared fuelled `iterateToFixpoint`), and `extractDSModel`
propagates the `Except` errors of `unblockedLabels`, `ancestors`, and
`dsSatisfies` instead of crashing or diverging. Formulas in error
messages are printed with Lean's `toString`, not Haskell's `show`.

Issue #8 step G.
-/
namespace Gamen

attribute [local instance] lexOrd

-- ====================================================================
-- Euclidean closure
-- ====================================================================

/-- Euclidean closure of a binary relation: extend with `(u, v)` whenever
`(w, u)` and `(w, v)` are both present, iterating to a fixed point. The
`universe` argument is unused at present but is kept in the signature so
future variants can intersect with it (as in the Haskell).

Fuel: `n² + 1`, where `n` is the number of labels occurring in `r`. Every
added pair `(u, v)` has both components already in `r`'s field, so the
field never grows and the relation has at most `n²` pairs; each round
before the last adds at least one. -/
def euclideanClose (_universe : Std.TreeSet Label) (r : Std.TreeSet (Label × Label)) :
    Except String (Std.TreeSet (Label × Label)) :=
  let field : Std.TreeSet Label :=
    r.foldl (fun acc (w, u) => (acc.insert w).insert u) ∅
  let step (r : Std.TreeSet (Label × Label)) : Std.TreeSet (Label × Label) :=
    let pairs := r.toList
    r.insertMany (pairs.flatMap fun (w1, u) =>
      pairs.filterMap fun (w2, v) => if w1 == w2 then some (u, v) else none)
  iterateToFixpoint "euclideanClose" step (field.size * field.size + 1) r

-- ====================================================================
-- Public API
-- ====================================================================

/-- Construct and *verify* a `DSModel` from a stable sequent and its
generation tree, following Definition 20 (Lyon & van Berkel 2024,
pp. 858–859).

Labels become `World` values via `toString`: `⟨0⟩` becomes `"w0"`. The
valuation flips polarity: `V^Λ(p)` contains exactly the labels at which
`w:¬p ∈ Γ`.

The result is *re-checked* rather than trusted (the B6 hazard is a
trusted-but-wrong counter-model): extraction fails unless (1) the extracted
frame is a valid DS frame (`isValidDSFrame`) and (2) every root-labelled
formula `w₀:φ ∈ Γ` is actually falsified at `w₀` (`dsSatisfies m w₀ φ`
is `.ok false`). A stable refuted sequent reads Γ disjunctively, so a
genuine counter-model must falsify each of its root disjuncts. (A C2
failure inside `isValidDSFrame` is the documented IoaOp scheduling
deferral — such a frame is reported as unverifiable here rather than
emitted as a bogus counter-model.) -/
def extractDSModel (gt : GenTree) (s : Sequent) : Except String DSModel := do
  let unblockedSet ← unblockedLabels gt s
  let labelToWorld : Label → World := toString
  let worlds : Std.TreeSet World :=
    unblockedSet.foldl (fun acc w => acc.insert (labelToWorld w)) ∅
  let agentSet := sequentAgents s
  let choicePairsInRels (a : String) : List (Label × Label) :=
    s.rels.toList.filterMap fun
      | .choice b w u => if b == a then some (w, u) else none
      | .ideal _ _ => none
  -- S_[i]^Λ: clause (i), both endpoints unblocked ...
  let sBaseRelation (a : String) : Except String (Std.TreeSet (Label × Label)) := do
    let clauseI := (choicePairsInRels a).filter fun (w, u) =>
      unblockedSet.contains w && unblockedSet.contains u
    -- ... or clause (ii), v directly blocked by a proper ancestor u. The
    -- redirection target must be an ancestor of v (Definition 16 blocking
    -- is ancestor-relative), not any unblocked label with matching content
    -- (adversarial review B6).
    let clauseII ← (choicePairsInRels a).flatMapM fun (w, v) => do
      if !unblockedSet.contains w then return []
      let anc ← ancestors v gt
      return anc.filterMap fun u =>
        if unblockedSet.contains u && isDirectlyBlockedBy v u gt s then some (w, u) else none
    return Std.TreeSet.ofList clauseI ∪ Std.TreeSet.ofList clauseII
  let choiceRelation (a : String) : Except String (Std.TreeMap World (Std.TreeSet World)) := do
    let pairs ← euclideanClose unblockedSet (← sBaseRelation a)
    let startKeys : Std.TreeMap World (Std.TreeSet World) :=
      unblockedSet.foldl (fun acc w => acc.insert (labelToWorld w) ∅) ∅
    return pairs.foldl (fun acc (w, u) =>
      acc.alter (labelToWorld w) fun
        | none => some {labelToWorld u}
        | some us => some (us.insert (labelToWorld u))) startKeys
  let relations ← agentSet.toList.foldlM (fun acc a => do
    return acc.insert a (← choiceRelation a)) (∅ : Std.TreeMap String (Std.TreeMap World (Std.TreeSet World)))
  let ideals : Std.TreeMap String (Std.TreeSet World) :=
    agentSet.foldl (fun acc a =>
      acc.insert a (unblockedSet.foldl (fun ws w =>
        if hasRel (.ideal a w) s then ws.insert (labelToWorld w) else ws) ∅)) ∅
  let valuation : Std.TreeMap Atom (Std.TreeSet World) :=
    s.gamma.foldl (fun acc lf =>
      match lf.lfFormula with
      | .not (.atomF a) =>
        if unblockedSet.contains lf.lfLabel then
          acc.alter a fun
            | none => some {labelToWorld lf.lfLabel}
            | some ws => some (ws.insert (labelToWorld lf.lfLabel))
        else acc
      | _ => acc) ∅
  let model : DSModel :=
    { dsFrame := { dsWorlds := worlds, dsRelations := relations, dsIdeals := ideals }
      dsValuation := valuation }
  if !isValidDSFrame model.dsFrame then
    throw "extractDSModel: extracted frame is not a valid DS frame \
      (C1-C3/D1-D3; a C2 failure is the documented IoaOp deferral)"
  -- Root-labelled Γ formulas the counter-model must falsify. The root is
  -- always unblocked, hence present in the model.
  let rootGamma := s.gamma.toList.filter fun lf =>
    lf.lfLabel == gt.gtRoot && unblockedSet.contains lf.lfLabel
  let notFalsified ← rootGamma.findM? fun lf =>
    dsSatisfies model (labelToWorld lf.lfLabel) lf.lfFormula
  match notFalsified with
  | some lf =>
    throw s!"extractDSModel: model fails to falsify root formula {lf.lfFormula} \
      at {labelToWorld lf.lfLabel}"
  | none => return model

end Gamen
