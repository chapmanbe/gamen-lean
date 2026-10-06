import Gamen.Dcleg
import Gamen.Service.Protocol

/-!
# Gamen.Service.Axioms

Port of `gamen-hs/protocol/Service/Axioms.hs`: the belief-revision axiom
checks behind `dcleg-service`'s `axiom_check`. Each check enumerates the
model's finite components (no prover), and reports up to `max_violations`
violations.

Citations are to the final DCLEG thesis (Chapman 2026, pinned in
`notes/dcleg-edition.md`, printed pages): the eight doxastic conditions
(1 Presence … 8 Recall) are §3.2.2, p. 20; Centering and Contemporary
Universality, the conditions on F, §3.2.2, p. 19; Intentional Awareness
§3.2.4, p. 23. The Haskell cites the April 2026 draft's numbering
("§2.2", "§2.4", i.e. DCLEG v5.0 §2.2 and §2.4).

Two differences from the Haskell, both so that no error and no truncation
turns into an answer:

* **Errors.** A check can hit a library error: Self-Awareness and
  Intentional Awareness evaluate the turn-taker's beliefs, and
  `doxasticSuccessors` errors for an agent with no doxastic map. In gamen-hs
  that `error` kills the whole service process. Here `checkAxiom` returns
  it, and the service answers `internal_error`.
* **`max_violations` ≤ 0.** gamen-hs's `take maxV` leaves no violations to
  report, so it answers `"satisfied": true` for any model. Here
  `satisfied` is decided by whether there is at least one violation, and
  only the *listed* violations are capped (an empty list for a cap ≤ 0).

Otherwise the enumeration order, the stopping point and the violation
objects are the Haskell's: the loops below nest in the order of its list
comprehensions and stop as soon as the cap is reached, so an error past the
cap is not raised (Haskell's `take` never forces it).
-/

namespace Gamen.Service
open Lean (Json toJson)
open Dcleg

-- Pairs as keys: Lean core has no global `Ord (α × β)` (see `Tableau.lean`).
attribute [local instance] lexOrd

/-- The axiom names `axiom_check` accepts, in the Haskell's order. -/
def allAxiomNames : List String :=
  [ "presence", "present_seriality", "transitivity", "euclideanness"
  , "self_awareness", "intentional_awareness"
  , "centering", "contemporary_universality"
  , "minimal_revision", "expectational_continuity", "recall" ]

/-- How a check stops early: the cap was reached, or a library error. -/
inductive Halt where
  | full
  | err (msg : String)

/-- A check: collects violations in the state, and stops with `Halt`. -/
abbrev CheckM := ExceptT Halt (StateM (Array Json))

/-- Record a violation; stop once `limit` have been found. -/
def emitV (limit : Nat) (v : Json) : CheckM Unit := do
  modify (·.push v)
  if (← get).size ≥ limit then throw .full

/-- Lift a library result, turning its error into a halt. -/
def liftE {α : Type} : Except String α → CheckM α
  | .ok a => pure a
  | .error e => throw (.err e)

/-- Run a check body with cap `maxV`. The search runs to `max maxV 1`
violations, so `satisfied` is right for every cap; the reply lists the
first `maxV` (none for `maxV ≤ 0`). -/
def runCheck (maxV : Int) (body : Nat → CheckM Unit) : Except String Json :=
  let limit := max maxV.toNat 1
  let (r, vs) := (body limit).run.run #[]
  match r with
  | .error (.err e) => .error e
  | _ =>
    if vs.isEmpty then .ok (Json.mkObj [("satisfied", true)])
    else .ok (Json.mkObj [("satisfied", false),
      ("violations", Json.arr (vs.toList.take maxV.toNat).toArray)])

private def agentList (m : DclegModel) : List Agent := m.dmDoxastic.keys
private def worldList (m : DclegModel) : List World := m.dmWorlds.toList
private def vertexList (m : DclegModel) : List Vertex := m.dmStructure.ssNodes.toList

private def obj (kvs : List (String × Json)) : Json := Json.mkObj kvs

/-! ## Standard doxastic conditions (§3.2.2, p. 20) -/

/-- Presence: if w ∉ V_γ then R_i^w(γ) = ∅. -/
def presence (m : DclegModel) (limit : Nat) : CheckM Unit := do
  for i in agentList m do
    for w in vertexList m do
      for gamma in worldList m do
        if !(worldVertices m gamma).contains w then
          if !(← liftE (doxasticSuccessors m i w gamma)).isEmpty then
            emitV limit (obj [("agent", i), ("world", gamma), ("vertex", w),
              ("detail", "non-empty doxastic successors when w ∉ V_γ")])

/-- Present Seriality: if w ∈ V_γ then R_i^w(γ) ≠ ∅. -/
def presentSeriality (m : DclegModel) (limit : Nat) : CheckM Unit := do
  for i in agentList m do
    for w in vertexList m do
      for gamma in worldList m do
        if (worldVertices m gamma).contains w then
          if (← liftE (doxasticSuccessors m i w gamma)).isEmpty then
            emitV limit (obj [("agent", i), ("world", gamma), ("vertex", w),
              ("detail", "empty doxastic successors when w ∈ V_γ")])

/-- Transitivity: γ' ∈ R_i^w(γ) and γ'' ∈ R_i^w(γ') imply γ'' ∈ R_i^w(γ). -/
def transitivity (m : DclegModel) (limit : Nat) : CheckM Unit := do
  for i in agentList m do
    for w in vertexList m do
      for gamma in worldList m do
        let succGamma ← liftE (doxasticSuccessors m i w gamma)
        for gamma' in succGamma do
          for gamma'' in ← liftE (doxasticSuccessors m i w gamma') do
            if !succGamma.contains gamma'' then
              emitV limit (obj [("agent", i), ("vertex", w), ("world", gamma),
                ("successor", gamma'), ("transitive_successor", gamma''),
                ("detail", "γ'∈R(γ), γ''∈R(γ') but γ''∉R(γ)")])

/-- Euclideanness: γ', γ'' ∈ R_i^w(γ) imply γ'' ∈ R_i^w(γ'). -/
def euclideanness (m : DclegModel) (limit : Nat) : CheckM Unit := do
  for i in agentList m do
    for w in vertexList m do
      for gamma in worldList m do
        let succs ← liftE (doxasticSuccessors m i w gamma)
        for gamma' in succs do
          for gamma'' in succs do
            if !(← liftE (doxasticSuccessors m i w gamma')).contains gamma'' then
              emitV limit (obj [("agent", i), ("vertex", w), ("world", gamma),
                ("successor1", gamma'), ("successor2", gamma''),
                ("detail", "γ',γ''∈R(γ) but γ''∉R(γ')")])

/-! ## Self-Awareness (§3.2.2, p. 20) and Intentional Awareness (§3.2.4, p. 23) -/

/-- Self-Awareness: if Q(w) = i then {Mv(δ,w) | δ ∈ R_i^w(γ)} = {Mv(γ,w)}. -/
def selfAwareness (m : DclegModel) (limit : Nat) : CheckM Unit := do
  for w in vertexList m do
    let some i := m.dmStructure.ssPlayer.get? w | continue
    for gamma in worldList m do
      if !(worldVertices m gamma).contains w then continue
      let some mv := moveAt m gamma w | continue
      for gamma' in ← liftE (doxasticSuccessors m i w gamma) do
        let some mv' := moveAt m gamma' w | continue
        if mv' != mv then
          emitV limit (obj [("agent", i), ("vertex", w), ("world", gamma),
            ("actual_move", mv), ("believed_move", mv'),
            ("detail", "successor world plays different move than actual")])

/-- Intentional Awareness (§3.2.4, p. 23): B_i(m_i) ↔ m_i with m_i = (m ∧ turn_i),
checked as a material biconditional at each reached (γ,w). -/
def intentionalAwareness (m : DclegModel) (limit : Nat) : CheckM Unit := do
  for w in vertexList m do
    let some i := m.dmStructure.ssPlayer.get? w | continue
    for gamma in worldList m do
      if !(worldVertices m gamma).contains w then continue
      for mv in (m.dmStructure.ssMoves.getD w ∅).toList do
        let mi := dfAnd (.dfMove mv) (.dfTurn i)
        let lhs ← liftE (dclegSatisfies m gamma w (.dfBelief i mi))
        let rhs ← liftE (dclegSatisfies m gamma w mi)
        if lhs != rhs then
          emitV limit (obj [("agent", i), ("vertex", w), ("world", gamma), ("move", mv),
            ("detail", "B_i(m_i) ≠ m_i: agent's self-belief about move is inaccurate")])

/-! ## Conditions on the premise function F (§3.2.2, p. 19) -/

/-- Centering: ∩F(γ,w) = {(γ,w)}, wherever F(γ,w) has an entry. -/
def centering (m : DclegModel) (limit : Nat) : CheckM Unit := do
  for ((gamma, w), fgw) in m.dmPremises.toList do
    match fgw.toList with
    | [] => pure ()
    | p :: ps =>
      -- Haskell `foldr1 Set.intersection` (intersection is associative)
      let itsct := ps.foldl (fun a b => a ∩ b) p
      if itsct.toList != [(gamma, w)] then
        emitV limit (obj [("world", gamma), ("vertex", w),
          ("intersection", toJson (itsct.toList.map fun (a, b) => [a, b])),
          ("detail", "∩F(γ,w) ≠ {(γ,w)}")])

/-- Contemporary Universality: w ∈ V_β implies (β,w) ∈ ∪F(γ,w). -/
def contemporaryUniversality (m : DclegModel) (limit : Nat) : CheckM Unit := do
  for ((gamma, w), fgw) in m.dmPremises.toList do
    if fgw.isEmpty then continue
    for beta in worldList m do
      if (worldVertices m beta).contains w && !fgw.toList.any (·.contains (beta, w)) then
        emitV limit (obj [("world", gamma), ("vertex", w), ("missing_world", beta),
          ("detail", "w∈V_β but (β,w)∉∪F(γ,w)")])

/-! ## Belief-revision conditions (§3.2.2, p. 20) -/

/-- Minimal Revision: R_i^{w'}(γ) ⊆ ∪{ max_{F(δ,w)}^m(Γ) | δ ∈ R_i^w(γ) },
with m = Mv(γ,w) and w' = next(w,m). -/
def minimalRevision (m : DclegModel) (limit : Nat) : CheckM Unit := do
  for i in agentList m do
    for w in vertexList m do
      for gamma in worldList m do
        if !(worldVertices m gamma).contains w then continue
        let some mv := moveAt m gamma w | continue
        let some w' := m.dmStructure.ssNext.get? (w, mv) | continue
        let succAtW ← liftE (doxasticSuccessors m i w gamma)
        let atW' ← liftE (doxasticSuccessors m i w' gamma)
        -- Haskell builds `candidates` lazily, so only when there is a γ'.
        if atW'.isEmpty then continue
        let mut candidates : List World := []
        for delta in succAtW do
          candidates := candidates ++ (← liftE (maxPhiConsistent m delta w (.dfMove mv)))
        for gamma' in atW' do
          if !candidates.contains gamma' then
            emitV limit (obj [("agent", i), ("vertex", w), ("world", gamma),
              ("next_vertex", w'), ("violating_successor", gamma'),
              ("detail", "γ'∈R_i(w',γ) but γ'∉∪max_m over R_i(w,γ)")])

/-- Expectational Continuity: if {Mv(δ,w) | δ ∈ R_i^w(γ)} = {m} then
R_i^w(γ) = R_i^{w'}(γ), with w' = next(w,m). -/
def expectationalContinuity (m : DclegModel) (limit : Nat) : CheckM Unit := do
  for i in agentList m do
    for w in vertexList m do
      for gamma in worldList m do
        if !(worldVertices m gamma).contains w then continue
        let succs ← liftE (doxasticSuccessors m i w gamma)
        let succMoves : Std.TreeSet Move := Std.TreeSet.ofList (succs.filterMap (moveAt m · w))
        if succMoves.size != 1 then continue
        let some mv := succMoves.min? | continue
        let some w' := m.dmStructure.ssNext.get? (w, mv) | continue
        let atW' ← liftE (doxasticSuccessors m i w' gamma)
        if (Std.TreeSet.ofList succs : Std.TreeSet World).toList
            != (Std.TreeSet.ofList atW' : Std.TreeSet World).toList then
          emitV limit (obj [("agent", i), ("vertex", w), ("world", gamma), ("move", mv),
            ("next_vertex", w'),
            ("detail", "beliefs changed at w' despite all successors playing m")])

/-- Recall: R_i^w(γ) = ∪{ R_i^w(δ) | δ ∈ R_i^{w'}(γ) }, with w' = next(w, Mv(γ,w)). -/
def recall (m : DclegModel) (limit : Nat) : CheckM Unit := do
  for i in agentList m do
    for w in vertexList m do
      for gamma in worldList m do
        if !(worldVertices m gamma).contains w then continue
        let some mv := moveAt m gamma w | continue
        let some w' := m.dmStructure.ssNext.get? (w, mv) | continue
        let atW : Std.TreeSet World := Std.TreeSet.ofList (← liftE (doxasticSuccessors m i w gamma))
        let mut union : List World := []
        for d in ← liftE (doxasticSuccessors m i w' gamma) do
          union := union ++ (← liftE (doxasticSuccessors m i w d))
        if atW.toList != (Std.TreeSet.ofList union : Std.TreeSet World).toList then
          emitV limit (obj [("agent", i), ("vertex", w), ("world", gamma), ("next_vertex", w'),
            ("detail", "R_i(w,γ) ≠ ∪{R_i(w,δ) | δ∈R_i(w',γ)}")])

/-- Dispatch by axiom name: `{"satisfied": true}` or
`{"satisfied": false, "violations": [...]}`, or the library error the check
hit. An unknown name is an error here; the service rejects unknown names
before calling this (gamen-hs#18 task 18), where gamen-hs returned an
`{"error": …}` object. -/
def checkAxiom (ax : String) (maxV : Int) (m : DclegModel) : Except String Json :=
  let body : Option (Nat → CheckM Unit) := match ax with
    | "presence" => some (presence m)
    | "present_seriality" => some (presentSeriality m)
    | "transitivity" => some (transitivity m)
    | "euclideanness" => some (euclideanness m)
    | "self_awareness" => some (selfAwareness m)
    | "intentional_awareness" => some (intentionalAwareness m)
    | "centering" => some (centering m)
    | "contemporary_universality" => some (contemporaryUniversality m)
    | "minimal_revision" => some (minimalRevision m)
    | "expectational_continuity" => some (expectationalContinuity m)
    | "recall" => some (recall m)
    | _ => none
  match body with
  | some b => runCheck maxV b
  | none => .error s!"unknown axiom: {ax}"

end Gamen.Service
