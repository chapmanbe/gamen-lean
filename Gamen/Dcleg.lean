import Std.Data.TreeMap
import Std.Data.TreeSet

/-!
# Gamen.Dcleg

Port of `gamen-hs/src/Gamen/Dcleg.hs`: the Doxastic Conditional Logic of
Extensive Games (DCLEG). Jeremiah Chapman, *Doxastic Conditional Logic,
Rationality, and Backward Induction: Formalizing Belief and Counterfactual
Reasoning in Games*, Master's thesis in Logic, University of Gothenburg,
June 4th 2026, supervised by Martin Kaså; DCLEG is its Chapter 3.
Unqualified section numbers below mean that final thesis, with its printed
page numbers; both it and the April 2026 v5.0 draft this module was first
ported against are pinned by hash in `notes/dcleg-edition.md`. The v5.0
sections map as §1.x → §3.1.x and §2.1–2.6 → §3.2.1–3.2.6, and the
semantics did not change between them.

Formulas are evaluated at pointed models (M, γ, w), where γ is a possible
world and w a game vertex actually reached in γ. The language combines the
propositional operators (¬, ∨), a counterfactual conditional (φ □→ ψ),
belief operators B_i, the temporal operators X (next) and Y (yesterday), and
a necessity operator □ (true at every world reaching the current vertex).
Syntax is §3.1.1 (pp. 15–16), abbreviations §3.1.2 (p. 16), strategic
structures §3.2.1 (pp. 16–18), game models and the premise function §3.2.2
(pp. 18–20), satisfaction §3.2.3 (pp. 20–22).

## Deviations from the Haskell

* **Errors.** Both Haskell `error`s become `Except`: `dclegSatisfies`'s
  "vertex not reached in world" guard and `doxasticSuccessors`'s unknown
  agent. So `doxasticSuccessors`, `extension`, `maxPhiConsistent`,
  `dclegSatisfies`, and `dclegTrueIn` return `Except`. `validateDclegModel`
  calls `doxasticSuccessors` only for agents taken from the doxastic map's
  own keys, so its error is unreachable there; it uses the total lookup
  (`doxSuccs`) and stays a pure `List String`. Messages use `repr` for
  Haskell's `show`, as `Gamen.Epistemic` does; the two agree on ASCII names
  (GHC escapes non-ASCII characters such as `γ`, Lean does not).
* **`Prop` is `DclegProp`.** Haskell's `type Prop = Set (World, Vertex)`
  would shadow Lean's `Prop` inside `namespace Gamen`.
* **No antecedent cache.** gamen-hs threads a lazy map from each
  counterfactual antecedent to its extension `[[φ]]` (issue #18, task 19.2),
  computed at most once and only when that counterfactual is reached.
  `[[φ]]` depends only on the model and φ, so the cache changes speed, not
  results; this port recomputes `[[φ]]` each time the counterfactual is
  reached (never before), which matches both the results and which error
  is raised. Add a cache, with a property test against this version, only
  if speed demands it (CLAUDE.md, "Laziness").
* **Laziness.** The Haskell's `||` and `all` short-circuit, so an erroring
  right disjunct, or a later belief/□/counterfactual witness, is never
  forced once the answer is settled; `dclegSatisfies` does the same
  (`if … then … else`, `List.allM`). In a counterfactual, gamen-hs forces
  `[[φ]]` at its first `Set.member` test, before any ψ, whenever the model
  has at least one world, even at an outcome vertex with no premises; the
  port always computes `[[φ]]` first, which differs only when there are no
  worlds, and then `[[φ]]` is empty and cannot error.
* **Centering fixed (gamen-hs TODO(#18)).** `withMovePremises` adds the
  singleton premise {(γ,w)} to every F(γ,w), so Centering holds at
  single-move vertices too. gamen-hs leaves this as a TODO, and there
  ∩F(γ,w) is all of R^w at a single-move vertex. This is a deliberate
  divergence: gamen-lean is primary. It changes results only at
  single-move vertices reached by more than one world (see
  `withMovePremises`); Dcleg is not part of `gamen-validate`.
* `DclegModel` derives no `BEq`/`Repr` (the Haskell derives `Eq, Show`;
  nothing here or in the tests compares models).
-/
namespace Gamen

-- Pairs as keys: Lean core has no global `Ord (α × β)` (see `Tableau.lean`).
attribute [local instance] lexOrd

namespace Dcleg

abbrev World := String
abbrev Vertex := String
abbrev Move := String
abbrev Agent := String

end Dcleg

open Dcleg

/-! ## Syntax (§3.1.1, pp. 15–16) -/

/-- Formulas of DCLEG (§3.1.1, pp. 15–16). Atoms: ⊥, propositions p, turn_i, moves m,
payoffs k_i. Operators: ¬, ∨, □→ (counterfactual), B_i, X, Y, □. -/
inductive DclegFormula where
  /-- ⊥ (falsity) -/
  | dfBot
  /-- p ∈ Prop -/
  | dfProp (p : String)
  /-- turn_i: it is i's turn -/
  | dfTurn (i : Agent)
  /-- m: move m is played this turn -/
  | dfMove (m : Move)
  /-- k_i: i ultimately gets payoff k -/
  | dfPayoff (k : Int) (i : Agent)
  /-- ¬φ -/
  | dfNeg (φ : DclegFormula)
  /-- φ ∨ ψ -/
  | dfOr (φ ψ : DclegFormula)
  /-- φ □→ ψ (counterfactual) -/
  | dfConditional (φ ψ : DclegFormula)
  /-- B_i φ -/
  | dfBelief (i : Agent) (φ : DclegFormula)
  /-- X φ -/
  | dfNext (φ : DclegFormula)
  /-- Y φ -/
  | dfYesterday (φ : DclegFormula)
  /-- □ φ -/
  | dfBox (φ : DclegFormula)
  deriving BEq, Ord, Repr, Inhabited

/-! ### Abbreviation helpers (§3.1.2, p. 16) -/

/-- ⊤ = ¬⊥ -/
def dfTop : DclegFormula := .dfNeg .dfBot

/-- φ ∧ ψ = ¬(¬φ ∨ ¬ψ) -/
def dfAnd (p q : DclegFormula) : DclegFormula := .dfNeg (.dfOr (.dfNeg p) (.dfNeg q))

/-- φ → ψ = ¬φ ∨ ψ (material conditional) -/
def dfImplies (p q : DclegFormula) : DclegFormula := .dfOr (.dfNeg p) q

/-- ◇φ = ¬□¬φ -/
def dfDiamond (p : DclegFormula) : DclegFormula := .dfNeg (.dfBox (.dfNeg p))

/-- B̂_i φ = ¬B_i¬φ (agent i considers φ plausible) -/
def dfPlausible (i : Agent) (p : DclegFormula) : DclegFormula :=
  .dfNeg (.dfBelief i (.dfNeg p))

/-! ## Strategic structure (§3.2.1, pp. 16–18) -/

/-- T = ⟨V, EndV, Q, PMoves, next⟩ (§3.2.1, pp. 16–17). Conditions 1–7
(§3.2.1, p. 17) are
documented but not enforced here. -/
structure StrategicStructure where
  /-- V: all nodes -/
  ssNodes : Std.TreeSet Vertex
  /-- EndV ⊂ V: outcome nodes -/
  ssEndNodes : Std.TreeSet Vertex
  /-- Q: V \ EndV → Agt (partial) -/
  ssPlayer : Std.TreeMap Vertex Agent
  /-- PMoves: V → P(Act) -/
  ssMoves : Std.TreeMap Vertex (Std.TreeSet Move)
  /-- next: V × Act ⇀ V -/
  ssNext : Std.TreeMap (Vertex × Move) Vertex

/-- Construct a strategic structure from all nodes, the end (outcome)
nodes, the player at each decision node, the possible moves at each node,
and the transitions (node, move, successor). A repeated key keeps its last
value, as Haskell's `Map.fromList` does. -/
def mkStrategicStructure (ns ends : List Vertex) (player : List (Vertex × Agent))
    (moves : List (Vertex × List Move)) (trans : List (Vertex × Move × Vertex)) :
    StrategicStructure where
  ssNodes := Std.TreeSet.ofList ns
  ssEndNodes := Std.TreeSet.ofList ends
  ssPlayer := Std.TreeMap.ofList player
  ssMoves := Std.TreeMap.ofList (moves.map fun (v, ms) => (v, Std.TreeSet.ofList ms))
  ssNext := Std.TreeMap.ofList (trans.map fun (v, m, v') => ((v, m), v'))

/-! ## History (§3.2.2, pp. 18–19) -/

/-- A complete play: H(γ) = ⟨(v₀,m₀),…,(vₑ,mₑ)⟩, v_{e+1} (§3.2.2, pp. 18–19).
Conditions: v₀ is the unique root; m_j ∈ PMoves(v_j); next(v_j,m_j) = v_{j+1}. -/
structure History where
  /-- (v₀,m₀), …, (vₑ,mₑ) -/
  histMoves : List (Vertex × Move)
  /-- outcome node v_{e+1} -/
  histEnd : Vertex
  deriving BEq, Repr

def mkHistory (moves : List (Vertex × Move)) (e : Vertex) : History := ⟨moves, e⟩

/-- V_γ: all vertices visited in history h. -/
def histVertices (h : History) : Std.TreeSet Vertex :=
  Std.TreeSet.ofList (h.histMoves.map Prod.fst ++ [h.histEnd])

/-! ## Propositions -/

/-- A proposition is a subset of I = {(γ,w) | w ∈ V_γ} (§3.2.2, p. 19). Haskell's
`Prop`, renamed so as not to shadow Lean's `Prop`. -/
abbrev DclegProp := Std.TreeSet (World × Vertex)

/-- Haskell's `Ord (Set a)`: compare the ascending element lists. Needed
for sets of propositions (`dmPremises`); Std gives `TreeSet` no `Ord`. -/
instance : Ord DclegProp where
  compare a b := compare a.toList b.toList

/-- Haskell's `Eq (Set a)`: equal element lists. -/
instance : BEq DclegProp where
  beq a b := a.toList == b.toList

/-! ## Game model (§3.2.2, pp. 18–20) -/

/-- M = ⟨T, Γ, H, F, π, {R^w}, {N^w_i}, {P_i}⟩ (§3.2.2, p. 18).

R^w is derived from H at evaluation time (§3.2.2, p. 19):
R^w = {(β,γ) ∈ Γ² | w ∈ V_γ ∩ V_β}, so it is not stored. -/
structure DclegModel where
  dmStructure : StrategicStructure
  dmWorlds : Std.TreeSet World
  dmHistory : Std.TreeMap World History
  /-- F(γ,w) ∈ P(P(I)): premise function for counterfactuals (§3.2.2, p. 19).
  Constraints: Centering (∩F(γ,w) = {(γ,w)}) and Contemporary Universality
  (∀β: w ∈ V_β → (β,w) ∈ ∪F(γ,w)). Populate with `withMovePremises` or
  supply explicitly. -/
  dmPremises : Std.TreeMap (World × Vertex) (Std.TreeSet DclegProp)
  /-- π(p) ⊆ I: valuation for propositional variables. -/
  dmValuation : Std.TreeMap String (Std.TreeSet (World × Vertex))
  /-- N^w_i ⊆ Γ²: doxastic accessibility for agent i at vertex w, stored as
  agent → vertex → world → set of accessible worlds. -/
  dmDoxastic : Std.TreeMap Agent (Std.TreeMap Vertex (Std.TreeMap World (Std.TreeSet World)))
  /-- P_i: EndV → N: payoff for agent i at each outcome node. -/
  dmPayoff : Std.TreeMap Agent (Std.TreeMap Vertex Int)

/-- Construct a model. Premises start empty; call `withMovePremises` or
populate `dmPremises` directly before evaluating counterfactuals. -/
def mkDclegModel (ss : StrategicStructure) (ws : List World)
    (hs : List (World × History))
    (val : List (String × List (World × Vertex)))
    (dox : List (Agent × List (Vertex × List (World × List World))))
    (pay : List (Agent × List (Vertex × Int))) : DclegModel where
  dmStructure := ss
  dmWorlds := Std.TreeSet.ofList ws
  dmHistory := Std.TreeMap.ofList hs
  dmPremises := ∅
  dmValuation := Std.TreeMap.ofList (val.map fun (p, pairs) => (p, Std.TreeSet.ofList pairs))
  dmDoxastic := Std.TreeMap.ofList <| dox.map fun (ag, vgsucs) =>
    (ag, Std.TreeMap.ofList <| vgsucs.map fun (v, gsucs) =>
      (v, Std.TreeMap.ofList <| gsucs.map fun (g, succs) => (g, Std.TreeSet.ofList succs)))
  dmPayoff := Std.TreeMap.ofList (pay.map fun (ag, entries) => (ag, Std.TreeMap.ofList entries))

/-! ## Model inspection -/

/-- V_γ: vertices reached in world γ (empty if γ has no history). -/
def worldVertices (m : DclegModel) (gamma : World) : Std.TreeSet Vertex :=
  match m.dmHistory.get? gamma with
  | some h => histVertices h
  | none => ∅

/-- Move(γ,w): move made at vertex w in world γ (§3.2.3, p. 20; v5.0's
Mv). The first matching pair in the history, as Haskell's `lookup`. -/
def moveAt (m : DclegModel) (gamma : World) (w : Vertex) : Option Move := do
  let h ← m.dmHistory.get? gamma
  (h.histMoves.find? (·.1 == w)).map (·.2)

/-- Predecessor of w in world γ: the unique v with next(v, Move(γ,v)) = w. -/
def predecessorVertex (m : DclegModel) (gamma : World) (w : Vertex) : Option Vertex :=
  match m.dmHistory.get? gamma with
  | none => none
  | some h => go h (h.histMoves)
where
  go (h : History) : List (Vertex × Move) → Option Vertex
    | [] => none
    | (v, _) :: rest =>
      let w' := match rest with
        | (v', _) :: _ => v'
        | [] => h.histEnd
      if w' == w then some v else go h rest

/-- R^w: worlds β with w ∈ V_β (derived from H, §3.2.2, p. 19). -/
def settledAccessible (m : DclegModel) (w : Vertex) : List World :=
  m.dmWorlds.toList.filter fun beta => (worldVertices m beta).contains w

/-- N^w_i(γ) for an agent whose per-vertex map is already in hand. -/
private def doxSuccs (perAgt : Std.TreeMap Vertex (Std.TreeMap World (Std.TreeSet World)))
    (w : Vertex) (gamma : World) : List World :=
  ((perAgt.getD w ∅).getD gamma ∅).toList

/-- N^w_i(γ): worlds doxastically accessible from γ for agent i at vertex w
(ᚣ^w_i(γ), §3.2.2, pp. 19–20).

Errors on an agent with no doxastic map rather than returning ∅: an unknown
agent must not make `B_i φ` vacuously true (adversarial review B1;
cf. gamen-hs#7). An empty successor set for a *known* agent at a particular
(world, vertex) is a KD-seriality matter left to `validateDclegModel`. -/
def doxasticSuccessors (m : DclegModel) (i : Agent) (w : Vertex) (gamma : World) :
    Except String (List World) :=
  match m.dmDoxastic.get? i with
  | none => throw s!"doxasticSuccessors: agent {repr i} is not in model"
  | some perAgt => pure (doxSuccs perAgt w gamma)

/-- Basic well-formedness checks for a DCLEG model (adversarial review B7).
Returns the violation messages; `[]` means the model passes:

* *referential integrity*: every vertex visited by a history is a node of
  the strategic structure, and every world named in the doxastic map (key
  or successor) is a world of the model;
* *N^w_i ⊆ R^w*: each doxastic successor β of γ at vertex w has w ∈ V_β;
* *doxastic seriality (KD)*: wherever agent i has a doxastic map at vertex
  w, N^w_i(γ) is non-empty for every γ ∈ R^w;
* *admissible premises* (§3.2.2, p. 19), at every reached pair (γ,w),
  w ∈ V_γ, decision and outcome vertices alike: Centering,
  ⋂F(γ,w) = {(γ,w)}, and Contemporary Universality, (β,w) ∈ ⋃F(γ,w) for
  every β with w ∈ V_β. A missing F(γ,w) is ∅, as the evaluator reads it,
  and ∅ violates Centering (its intersection is not {(γ,w)}). Not in
  gamen-hs; see `docs/dcleg-outcome-node-premises-2026-09-30.md`.

These are the referential, seriality and premise guarantees the evaluator
relies on (Present Seriality is condition 2 of §3.2.2's doxastic conditions,
p. 20), not the full Conditions 1–7 of §3.2.1 (p. 17). -/
def validateDclegModel (m : DclegModel) : List String :=
  historyIntegrity ++ doxasticWorldIntegrity ++ nSubsetR ++ doxSeriality ++ premiseAdmissibility
where
  nodes := m.dmStructure.ssNodes
  ws := m.dmWorlds
  historyIntegrity : List String := Id.run do
    let mut out := []
    for (g, h) in m.dmHistory.toList do
      for v in (histVertices h).toList do
        if !nodes.contains v then
          out := out ++ [s!"validateDclegModel: world {repr g} visits vertex {repr v} \
            which is not a node of the strategic structure"]
    return out
  doxasticWorldIntegrity : List String := Id.run do
    let mut out := []
    for (i, perVtx) in m.dmDoxastic.toList do
      for perWorld in perVtx.values do
        for (g, succs) in perWorld.toList do
          for g' in g :: succs.toList do
            if !ws.contains g' then
              out := out ++ [s!"validateDclegModel: agent {repr i} doxastic map \
                references world {repr g'} not in the model"]
    return out
  nSubsetR : List String := Id.run do
    let mut out := []
    for (i, perVtx) in m.dmDoxastic.toList do
      for (w, perWorld) in perVtx.toList do
        for (g, succs) in perWorld.toList do
          for delta in succs.toList do
            if ws.contains delta && !(worldVertices m delta).contains w then
              out := out ++ [s!"validateDclegModel: agent {repr i} at vertex {repr w}: \
                doxastic successor {repr delta} of world {repr g} does not visit vertex \
                {repr w} (N^w_i ⊄ R^w)"]
    return out
  doxSeriality : List String := Id.run do
    let mut out := []
    for (i, perVtx) in m.dmDoxastic.toList do
      for w in perVtx.keys do
        for g in settledAccessible m w do
          if (doxSuccs perVtx w g).isEmpty then
            out := out ++ [s!"validateDclegModel: agent {repr i} at vertex {repr w} \
              has no doxastic successors for world {repr g} ∈ R^w (violates KD seriality)"]
    return out
  premiseAdmissibility : List String := Id.run do
    let mut out := []
    for g in ws.toList do
      for w in (worldVertices m g).toList do
        let fgw := (m.dmPremises.getD (g, w) ∅).toList
        match fgw with
        | [] =>
          out := out ++ [s!"validateDclegModel: F({repr g},{repr w}) is empty \
            (violates Centering: ⋂F(γ,w) must be \{(γ,w)}, §3.2.2, p. 19)"]
        | p :: ps =>
          let cap := ps.foldl (fun a b => a ∩ b) p
          if cap.toList != [(g, w)] then
            out := out ++ [s!"validateDclegModel: ⋂F({repr g},{repr w}) = {repr cap.toList}, \
              not \{({repr g},{repr w})} (violates Centering, §3.2.2, p. 19)"]
        for beta in settledAccessible m w do
          unless fgw.any (·.contains (beta, w)) do
            out := out ++ [s!"validateDclegModel: world {repr beta} reaches vertex {repr w} \
              but ({repr beta},{repr w}) ∉ ⋃F({repr g},{repr w}) (violates Contemporary \
              Universality, §3.2.2, p. 19)"]
    return out

/-! ## Counterfactual selection (§3.2.2, p. 19) -/

/-- Haskell's `Data.List.subsequences`, same order:
`subsequences [1,2,3] = [[],[1],[2],[1,2],[3],[1,3],[2,3],[1,2,3]]`. -/
def subsequences {α : Type} (xs : List α) : List (List α) :=
  [] :: nonEmpty xs
where
  nonEmpty : List α → List (List α)
    | [] => []
    | x :: rest => [x] :: (nonEmpty rest).foldr (fun ys r => ys :: (x :: ys) :: r) []

/-- max_{F(γ,w)}^φ(Γ), given `ext` = [[φ]] (§3.2.2, p. 19): the worlds γ' with
(γ',w) ∈ [[φ]] and a non-empty G ⊆ F(γ,w) such that (γ',w) ∈ ∩G and every
G' ⊋ G within F(γ,w) is φ-inconsistent. Haskell's `maxPhiConsistentWith`;
pure, since the only thing that can error, [[φ]], is the caller's.
Maximality is checked against one-premise extensions of G, as in the
Haskell (sufficient, since adding premises only shrinks ∩G'). -/
def maxPhiConsistentWith (m : DclegModel) (ext : Std.TreeSet (World × Vertex))
    (gamma : World) (w : Vertex) : List World :=
  let fgw := m.dmPremises.getD (gamma, w) ∅
  let fList := fgw.toList
  let bigCap : List DclegProp → DclegProp
    | [] => ∅
    | [p] => p
    | p :: ps => ps.foldr (fun a b => a ∩ b) p
  let phiCons (gs : List DclegProp) : Bool := !(bigCap gs ∩ ext).isEmpty
  let isMaximal (g : List DclegProp) : Bool :=
    phiCons g && (fList.filter (fun p => !g.contains p)).all (fun p => !phiCons (p :: g))
  let maxGs := (subsequences fList).filter (fun g => !g.isEmpty) |>.filter isMaximal
  (m.dmWorlds.toList.filter fun gamma' =>
    ext.contains (gamma', w) && maxGs.any (fun g => (bigCap g).contains (gamma', w))).eraseDups

/-- The pairs (γ, w) with w ∈ V_γ at which `sat` holds, in world then
vertex order; the first error is raised, as the Haskell list comprehension
forces them in that order. -/
private def extensionBy (m : DclegModel) (sat : World → Vertex → Except String Bool) :
    Except String (Std.TreeSet (World × Vertex)) := do
  let mut out : Std.TreeSet (World × Vertex) := ∅
  for gamma in m.dmWorlds.toList do
    for w in (worldVertices m gamma).toList do
      if ← sat gamma w then out := out.insert (gamma, w)
  return out

/-! ## Satisfaction (§3.2.3, pp. 20–22) -/

/-- M, γ, w ⊩ φ (§3.2.3, p. 21). Requires w ∈ V_γ, and errors otherwise, at every
recursive call, as the Haskell's first equation does. -/
def dclegSatisfies (m : DclegModel) : World → Vertex → DclegFormula → Except String Bool
  | gamma, w, phi => do
    unless (worldVertices m gamma).contains w do
      throw s!"dclegSatisfies: vertex {repr w} not reached in world {repr gamma}"
    match phi with
    -- ⊥ is never satisfied.
    | .dfBot => pure false
    -- p: (γ,w) ∈ π(p)
    | .dfProp p => pure ((m.dmValuation.getD p ∅).contains (gamma, w))
    -- turn_i: Q(w) = i
    | .dfTurn i => pure (m.dmStructure.ssPlayer.get? w == some i)
    -- m: Move(γ,w) = m
    | .dfMove mv => pure (moveAt m gamma w == some mv)
    -- k_i: P_i(w_{e+1}) = k, where w_{e+1} = histEnd(H(γ))
    | .dfPayoff k i =>
      match m.dmHistory.get? gamma with
      | none => pure false
      | some h =>
        match (m.dmPayoff.get? i).bind (·.get? h.histEnd) with
        | some k' => pure (k' == k)
        | none => pure false
    | .dfNeg f => return !(← dclegSatisfies m gamma w f)
    | .dfOr f g => do
      if ← dclegSatisfies m gamma w f then pure true else dclegSatisfies m gamma w g
    -- B_i φ: φ holds at w in every N^w_i(γ)-world.
    | .dfBelief i f => do
      let succs ← doxasticSuccessors m i w gamma
      succs.allM fun delta => dclegSatisfies m delta w f
    -- X φ: φ holds at next(w, Move(γ,w)); false at outcome nodes.
    | .dfNext f =>
      match moveAt m gamma w with
      | none => pure false
      | some mv =>
        match m.dmStructure.ssNext.get? (w, mv) with
        | none => pure false
        | some w' => dclegSatisfies m gamma w' f
    -- Y φ: φ holds at the predecessor of w in γ; false at the root.
    | .dfYesterday f =>
      match predecessorVertex m gamma w with
      | none => pure false
      | some w' => dclegSatisfies m gamma w' f
    -- □ φ: φ holds at w in every world β with w ∈ V_β; uniform across γ (§3.2.5, p. 23).
    | .dfBox f => (settledAccessible m w).allM fun beta => dclegSatisfies m beta w f
    -- φ □→ ψ: ψ holds at w in every maximally φ-consistent world
    -- (§3.2.2, p. 19; §3.2.3, pp. 21–22).
    | .dfConditional f g => do
      let ext ← extensionBy m fun beta v => dclegSatisfies m beta v f
      (maxPhiConsistentWith m ext gamma w).allM fun beta => dclegSatisfies m beta w g

/-- [[φ]]: the set of (world, vertex) pairs satisfying φ (§3.2.2, p. 19). -/
def extension (m : DclegModel) (phi : DclegFormula) :
    Except String (Std.TreeSet (World × Vertex)) :=
  extensionBy m fun gamma w => dclegSatisfies m gamma w phi

/-- max_{F(γ,w)}^φ(Γ): the worlds maximally φ-consistent with γ at w (§3.2.2, p. 19). -/
def maxPhiConsistent (m : DclegModel) (gamma : World) (w : Vertex) (phi : DclegFormula) :
    Except String (List World) := do
  return maxPhiConsistentWith m (← extension m phi) gamma w

/-- φ is true in M if it holds at every (γ,w) with w ∈ V_γ. Stops at the
first pair where it fails, as Haskell's `all`. -/
def dclegTrueIn (m : DclegModel) (phi : DclegFormula) : Except String Bool :=
  let pairs := m.dmWorlds.toList.flatMap fun gamma =>
    (worldVertices m gamma).toList.map fun w => (gamma, w)
  pairs.allM fun (gamma, w) => dclegSatisfies m gamma w phi

/-! ## Default move-based premise function -/

/-- F(γ,w) under the default, for each vertex w reached in γ. At a decision
vertex: one premise per move mv ∈ PMoves(w), the pairs (β,w) of the worlds β
that play mv at w, with (γ,w) added to every *non-actual* move's premise,
plus the singleton premise {(γ,w)} (Centering; gamen-hs TODO(#18)). At an
outcome vertex: {(γ,w)} and {(β,w) | w ∈ V_β} (see `withMovePremises`). -/
private def buildPremises (m : DclegModel) :
    Std.TreeMap (World × Vertex) (Std.TreeSet DclegProp) :=
  Std.TreeMap.ofList <| m.dmWorlds.toList.flatMap fun gamma =>
    (worldVertices m gamma).toList.map fun w =>
      ((gamma, w),
        if m.dmStructure.ssEndNodes.contains w then outcomePremisesAt gamma w
        else premisesAt gamma w)
where
  allWorlds := m.dmWorlds.toList
  /-- {(γ,w)} ⊂ {(β,w) | w ∈ V_β}: one arbitrary admissible choice. -/
  outcomePremisesAt (gamma : World) (w : Vertex) : Std.TreeSet DclegProp :=
    Std.TreeSet.ofList [Std.TreeSet.ofList [(gamma, w)],
      Std.TreeSet.ofList ((settledAccessible m w).map fun beta => (beta, w))]
  worldsWithMoveAt (w : Vertex) (mv : Move) : List World :=
    allWorlds.filter fun beta => (worldVertices m beta).contains w && moveAt m beta w == some mv
  mkPremise (gamma : World) (w : Vertex) (mv : Move) (actual : Option Move) : DclegProp :=
    let base : DclegProp := Std.TreeSet.ofList ((worldsWithMoveAt w mv).map fun beta => (beta, w))
    if some mv == actual then base else base.insert (gamma, w)
  premisesAt (gamma : World) (w : Vertex) : Std.TreeSet DclegProp :=
    let actual := moveAt m gamma w
    let allMvs := (m.dmStructure.ssMoves.getD w ∅).toList
    (Std.TreeSet.ofList (allMvs.map fun mv => mkPremise gamma w mv actual)).insert
      (Std.TreeSet.ofList [(gamma, w)])

/-- Populate F(γ,w) at every reached pair: from the moves actually played at
decision vertices (gamen-hs's own construction), and with a fixed nested pair
at outcome vertices (below). F's constraints are Centering and Contemporary
Universality (§3.2.2, p. 19). At a decision vertex w: for each available
move mv at w, the premise
{(β,w) | β plays mv at w}, with (γ,w) added to every *non-actual* move's
premise; and the singleton premise {(γ,w)}.

Contemporary Universality holds at a decision vertex because every world
reaching w plays some move there. Centering (∩F(γ,w) = {(γ,w)}) holds at every decision vertex
because of the singleton premise. Without it, Centering holds only where at
least two moves are available: at a *single-move* vertex the lone premise
is the whole R^w, so ∩F(γ,w) = R^w ⊋ {(γ,w)} whenever more than one world
reaches w (adversarial review B8).

**Deliberate divergence from gamen-hs** (its TODO(#18), not done there).
The singleton changes max^φ_{F(γ,w)}(Γ) only at single-move vertices that
more than one world reaches, and there only when (γ,w) ∈ [[φ]]: the answer
is then {γ} (Centering, §3.2.2, p. 19) instead of every world at w
satisfying φ. Elsewhere it is redundant. Where two or more moves are
available the other premises already intersect to {(γ,w)}; and if
(γ,w) ∉ [[φ]], no premise set containing the singleton is φ-consistent,
so the maximal sets are the same as before. At a vertex where only γ plays
its move the singleton equals that move's premise and F is unchanged.

**Outcome nodes** (deliberate divergence from gamen-hs, which gives them no
entry: fixed in gamen-lean; `docs/dcleg-outcome-node-premises-2026-09-30.md`).
With no premises, Centering and Contemporary Universality fail there, and
every φ □→ ψ is vacuously true (so ⊤ □→ ⊥ held at every outcome node). Each
reached outcome pair (γ,w) now gets two nested premises,

  F(γ,w) = { {(γ,w)}, {(β,w) | w ∈ V_β} },

"the actual world, inside all worlds that reach this outcome". Centering and
Contemporary Universality then hold at every reached pair; they are what
§3.2.2 (p. 19) requires of F, and `validateDclegModel` checks them.

This is **one arbitrary admissible choice**, not something the thesis
requires. The thesis leaves F unspecified, a parameter of the model subject
only to those two conditions, and other admissible systems give some
counterfactuals other truth values. A validity must hold for *every*
admissible F, so property tests draw random admissible premise systems
rather than rely on this default. -/
def withMovePremises (m : DclegModel) : DclegModel :=
  { m with dmPremises := buildPremises m }

end Gamen
