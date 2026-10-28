import Gamen.Atl.ModelCheck
import Gamen.Atel
import Gamen.Cgs
import Gamen.Formula

/-!
# Gamen.Atl.ImperfectInfo

Port of `gamen-hs/src/Gamen/Atl/ImperfectInfo.hs`: ATLir, Alternating-time
Temporal Logic with imperfect information and memoryless uniform strategies.

ATLir is ATL restricted to strategies where an agent must choose the same
action in all states it cannot distinguish (the uniformity constraint), as
studied in Jamroga & van der Hoek (2004), *Agents That Know How to Play*,
Fundamenta Informaticae 63(2–3): 185–219, and implemented by the STV tool
(Kurpiewski et al. 2019).

## Semantics

Two standard readings of `⟨⟨A⟩⟩ir`, both requiring a *uniform* joint
strategy `σ_A` (constant on `~_a` classes for each `a ∈ A`) (Schobbens
2004; Bulling & Jamroga 2014):

* *Subjective* (`atlirSat`, the default): `s ⊩ ⟨⟨A⟩⟩ir φ` iff some uniform
  `σ_A` witnesses `φ` from *every* state in `⋃_{a∈A} [s]_{~_a}`.
* *Objective* (`atlirSatObjective`): some uniform `σ_A` witnesses `φ` from
  the actual state `s` only.

Hence `sat(subjective) ⊆ sat(objective) ⊆ sat_ATL` (Jamroga & van der Hoek
2004, §4; Schobbens 2004).

## Implementation

The ATL fixpoint algorithm is incorrect for ATLir (Jamroga & van der Hoek
2004, §3). Instead: enumerate all uniform joint strategy profiles; for
each, build the *residual CGS* with the coalition's actions committed, and
apply ATL semantics (against the empty coalition) there. Exponential in
(epistemic classes × actions per class).

Not in gamen-hs (gamen-lean#8): `allUniformProfiles` prunes by default, so
each class offers only one of each group of actions that have the same
effect throughout it (`distinctUniformActions`). An uninformed agent's no-op
moves and the moves at sink states no longer multiply the profile count,
here and in ATL-D (`Gamen.Atl.Dynamic.uniformSat`). The answers and errors
are unchanged (`Tests/AtlirPruning.lean` checks this against
`prune := false`, gamen-hs's full enumeration).

None of the cited papers (Jamroga & van der Hoek 2004; Schobbens 2004,
ENTCS 85(2): 82–93; Bulling & Jamroga 2014; Kurpiewski, Jamroga & Knapik
2019) is among the PDFs in `gamen-hs/notes/`, so their volume/page and
section numbers are kept exactly as the Haskell gives them, unverified
against a primary source. No B&D citations.

## Deviations

* `atlirSat`/`atlirSatObjective` return `Except`: the seventeen
  unsupported-operator `error` calls become `throw`, wording verbatim.
  `atlirSatisfies`/`atlirSatisfiesObjective` (world guard) and
  `atlirIsTrueIn`/`atlirIsTrueInObjective` return `Except Bool`.
* `allUniformStrategies`/`allUniformProfiles` return `Except`: the
  Haskell's `Set.findMin cls` is partial and errors on an empty epistemic
  class (possible only for a model built without `mkAtelModel`, whose
  reflexivity check rules it out). It becomes `throw` with GHC's own
  message, raised exactly when Haskell's list-monad `sequence` would force
  that class (classes left to right, stopping at the first class with no
  uniform action). `atlirSat`'s coalition operators propagate it. One
  residual divergence: in Haskell the `findMin` thunk is forced only if
  the epistemic function is strict in its state argument. For one that
  ignores it (`\_ _ -> Set.empty`), GHCi gives `allUniformStrategies` = `[]`
  and `atlirSat (CanNext al p)` = ∅ with no error; for one that inspects
  it, the `findMin` error. Lean cannot observe that strictness, so it
  always throws. That is the conservative choice: a malformed model never
  yields a definite answer.
* `lfp`/`gfp` take fuel `cgsStates.size + 1`, as in `Gamen.Atl.ModelCheck.sat`
  (every set built is a subset of `cgsStates`).
* `epistemicClasses` returns the classes in `Data.Set`'s order on sets
  (lexicographic on the ascending element lists), deduplicated, as
  `Set.toList . Set.fromList` does; `Std.TreeSet` has no `Ord`, so the sort
  is written out (`compareLex`).

## Laziness

The Haskell `atlirSatWith` is pure, so `Data.Set`'s strictness decides
which subformula's `error` fires, and whether one fires at all. This port
reproduces it clause by clause (derived from `containers`' definitions and
checked against GHCi on `atlirSat`; see `atlirCases`' laziness cases):

* `Set.union a b` forces `b`, then `a`: `Or l r` evaluates `r` first;
  `Implies l r` evaluates `r`, then `l` (only when `states ≠ ∅`).
  (`Gamen.Atl.ModelCheck.sat` and `Gamen.Atel.atelSat` now do the same;
  they evaluated `l` first until 2026-09-29.)
* `Set.intersection a b`/`Set.difference a b` force `a`, and `b` only if
  `a ≠ ∅`: `And l r` skips `r` when `l` is empty; `Not f` skips `f` when
  `states = ∅`.
* `Iff l r` is `union (sl ∩ sr) (states \ (sl ∪ sr))`: when `states ≠ ∅`,
  `r` then `l`; when `states = ∅`, `l` only.
* `Knowledge`, and every coalition operator, are `Set.filter`s over
  `states`: nothing inside is forced when `states = ∅`.
* A coalition operator forces the profile list, then the first witness
  set, if `states ≠ ∅` (and further witness sets only while earlier ones
  fail to cover a state's requirement set). With no uniform profile at
  all, `φ` is never forced. `⟨⟨C⟩⟩X φ`'s witness is `preC res ∅ (sat φ)`,
  which forces `sat φ` only on reaching a membership test, i.e. only if
  some state has a nonempty joint move for the opponents (`Gamen.Cgs.preCLazy`).
  The fixpoint witnesses force `sat φ` (and then `sat ψ`, for `U`) on
  their first step. -/
namespace Gamen

-- ── Epistemic utilities ─────────────────────────────────────────────────

/-- Lexicographic comparison of lists: `Data.Set`'s `Ord (Set s)` compares
the ascending element lists this way. -/
private def compareLex {α : Type} [Ord α] : List α → List α → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | x :: xs, y :: ys =>
      match compare x y with
      | .eq => compareLex xs ys
      | o => o

/-- Insert into a list sorted by `compareLex`, dropping duplicates. -/
private def insertSortedLex {α : Type} [Ord α] (x : List α) :
    List (List α) → List (List α)
  | [] => [x]
  | y :: ys =>
      match compareLex x y with
      | .lt => x :: y :: ys
      | .eq => y :: ys
      | .gt => y :: insertSortedLex x ys

/-- All distinct epistemic equivalence classes for agent `ag`, in
`Data.Set`'s order on sets. -/
def epistemicClasses {s a : Type} [Ord s] [Ord a] (m : AtelModel s a) (ag : String) :
    List (Std.TreeSet s) :=
  let lists := m.atelCgs.cgsStates.toList.foldl
    (fun acc st => insertSortedLex (m.atelEpistemic ag st).toList acc) []
  lists.map fun l => Std.TreeSet.ofList l

/-- Subjective epistemic neighbourhood of `s` under `coalition`: the union
of the individual `~_a` classes for all `a ∈ coalition`, plus `s` itself
(so an empty coalition gives `{s}`, the objective reading) (Schobbens 2004;
Bulling & Jamroga 2014). -/
def subjectiveClass {s a : Type} [Ord s] [Ord a] (m : AtelModel s a)
    (coalition : Std.TreeSet String) (st : s) : Std.TreeSet s :=
  (coalition.toList.foldl (fun acc ag => acc ∪ m.atelEpistemic ag st) ∅).insert st

/-- Actions available to agent `ag` at *all* states in the equivalence
class of `s`. Empty if the class is empty or the move sets share no
action. -/
def uniformActions {s a : Type} [Ord s] [Ord a] (m : AtelModel s a) (ag : String)
    (st : s) : Std.TreeSet a :=
  let cgs := m.atelCgs
  match (m.atelEpistemic ag st).toList with
  | [] => ∅
  | t :: ts => ts.foldr (fun t' acc => acc ∩ cgs.cgsMoves t' ag) (cgs.cgsMoves t ag)

-- ── Uniform strategy enumeration ────────────────────────────────────────

/-- A uniform memoryless strategy for one agent: maps every state to an
action, constant on `~_ag` classes. -/
abbrev UniformStrategy (s a : Type) [Ord s] := Std.TreeMap s a

/-- Haskell's list-monad `sequence` (Cartesian product, first list
outermost), in the same order. -/
private def sequenceList {α : Type} : List (List α) → List (List α)
  | [] => [[]]
  | xs :: rest =>
      let tails := sequenceList rest
      xs.flatMap fun x => tails.map (x :: ·)

/-- Left-biased union of a list of maps (`Data.Map.unions`). -/
private def unionsLeft {k v : Type} [Ord k] (ms : List (Std.TreeMap k v)) :
    Std.TreeMap k v :=
  ms.foldl (fun acc m => m.union acc) ∅

/-- `sequence` over lists whose elements are computed in `Except`, raising
an error exactly where Haskell's lazy `sequence` would force it: the lists
are forced left to right, and once one is empty the rest are never forced
(the product is empty). -/
private def sequenceExcept {α : Type} :
    List (Except String (List α)) → Except String (List (List α))
  | [] => pure [[]]
  | e :: rest => do
      let xs ← e
      if xs.isEmpty then pure []
      else do
        let tails ← sequenceExcept rest
        pure (xs.flatMap fun x => tails.map (x :: ·))

/-- Not in gamen-hs as a separate function: `allUniformStrategies`'s
enumeration, with the actions tried on each class supplied by `choices`
(given the class and its least state). Shared with the pruned enumeration in
`allUniformProfiles`. -/
def uniformStrategiesWith {s a : Type} [Ord s] [Ord a] (m : AtelModel s a) (ag : String)
    (choices : Std.TreeSet s → s → List a) : Except String (List (UniformStrategy s a)) := do
  let classChoices : List (Except String (List (Std.TreeMap s a))) :=
    (epistemicClasses m ag).map fun cls =>
      match cls.min? with
      | none => throw "Set.findMin: empty set has no minimal element"
      | some rep =>
          pure ((choices cls rep).map fun act =>
            Std.TreeMap.ofList (cls.toList.map fun st => (st, act)))
  let combos ← sequenceExcept classChoices
  pure (combos.map unionsLeft)

/-- All uniform memoryless strategies for agent `ag`: the Cartesian product
of action choices over `epistemicClasses`, each class contributing one
action from `uniformActions`, assigned to every state in that class.

`Except`: an empty class makes the Haskell's `Set.findMin` error (see the
module docstring). -/
def allUniformStrategies {s a : Type} [Ord s] [Ord a] (m : AtelModel s a) (ag : String) :
    Except String (List (UniformStrategy s a)) :=
  uniformStrategiesWith m ag fun _ rep => (uniformActions m ag rep).toList

/-- Not in gamen-hs (gamen-lean#8). `acts` with each action dropped that has
the same effect as an earlier one at every state of `cls`. Two actions of `ag`
have the same effect at `t` when they give the same successor under every
joint move of `others`, the other agents who may move. Swapping one for the
other in a uniform strategy leaves the residual CGS's transition the same at
every state, so no witnessing set changes. A class of sink states keeps one
action. -/
def distinctUniformActions {s a : Type} [Ord s] [Ord a] (m : AtelModel s a) (ag : String)
    (others : Std.TreeSet String) (cls : Std.TreeSet s) (acts : List a) : List a :=
  let cgs := m.atelCgs
  let sameEffect (x y : a) : Bool :=
    cls.toList.all fun t =>
      (jointMoves cgs others t).all fun jm =>
        compare (cgs.cgsTransition t (jm.insert ag x)) (cgs.cgsTransition t (jm.insert ag y))
          == .eq
  (acts.foldl (fun kept x => if kept.any (sameEffect · x) then kept else x :: kept) []).reverse

/-- All uniform joint strategy profiles for `coalition`: the Cartesian
product of `allUniformStrategies` over the coalition's agents (ascending).

Differs from gamen-hs (gamen-lean#8): by default (`prune := true`) each class
offers only `distinctUniformActions`, where `others` is everyone in the model
or the coalition but the agent. The pruned list is a sublist of the full one,
in the same order, with the same first profile, and every profile left out has
a residual CGS identical to that of an earlier one kept. So a checker that
looks for a covering witness set (`atlirSatWith`), or computes them all in
order (`Gamen.Atl.Dynamic.uniformSat`), gives the same answer and raises the
same first error either way. `prune := false` is gamen-hs's full list, kept as
the baseline that `Tests/AtlirPruning.lean` checks against. -/
def allUniformProfiles {s a : Type} [Ord s] [Ord a] (m : AtelModel s a)
    (coalition : Std.TreeSet String) (prune : Bool := true) :
    Except String (List (Std.TreeMap String (UniformStrategy s a))) := do
  let agentList := coalition.toList
  let strategies (ag : String) : Except String (List (UniformStrategy s a)) :=
    if prune then
      let others := (m.atelCgs.cgsAgents ∪ coalition).erase ag
      uniformStrategiesWith m ag fun cls rep =>
        distinctUniformActions m ag others cls (uniformActions m ag rep).toList
    else allUniformStrategies m ag
  let stratCombs ← sequenceExcept (agentList.map strategies)
  pure (stratCombs.map fun strats => Std.TreeMap.ofList (agentList.zip strats))

-- ── Residual CGS ────────────────────────────────────────────────────────

/-- Commit the coalition's uniform profile and return the residual CGS
(only opponent agents remain active). Built with the bare `Cgs`
constructor, as in the Haskell (`Gamen.Cgs.mkCgs`'s docstring).

`oppJm.union coalJm` is the Haskell's `Map.union coal_jm opp_jm`
(`Std.TreeMap.union` keeps its second argument's entry on a shared key,
`Data.Map.union` its first). -/
def residualCgs {s a : Type} [Ord s] [Ord a] (m : AtelModel s a)
    (profile : Std.TreeMap String (UniformStrategy s a))
    (coalition : Std.TreeSet String) : Cgs s a :=
  let cgs := m.atelCgs
  { cgsStates := cgs.cgsStates
    cgsAgents := cgs.cgsAgents \ coalition
    cgsMoves := cgs.cgsMoves
    cgsTransition := fun st oppJm =>
      let coalJm := profile.filterMap fun _ strat => strat.get? st
      cgs.cgsTransition st (oppJm.union coalJm)
    cgsLabeling := cgs.cgsLabeling }

-- ── Satisfaction set ────────────────────────────────────────────────────

/-- Shared ATLir satisfaction, parameterised by the requirement set
(`subjectiveClass` for the subjective reading, `{s}` for the objective):

> s ∈ sat(⟨⟨A⟩⟩ir φ) iff ∃ uniform profile σ_A. req(A, s) ⊆ witnessing(σ_A, φ)

where `witnessing(σ_A, φ)` is where `σ_A` guarantees `φ` in the residual
CGS. Propositional and `Knowledge` clauses are as in `Gamen.Atel.atelSat`
(up to evaluation order; see the module docstring's "Laziness"). -/
def atlirSatWith {s a : Type} [Ord s] [Ord a] [BEq s]
    (req : AtelModel s a → Std.TreeSet String → s → Std.TreeSet s)
    (m : AtelModel s a) (f : Formula) (prune : Bool := true) : Except String (Std.TreeSet s) :=
  go f
where
  cgs := m.atelCgs
  states := m.atelCgs.cgsStates
  fuel := m.atelCgs.cgsStates.size + 1
  /-- A state satisfies the coalition operator iff some profile's
  witnessing set covers its requirement set. Profiles come from
  `allUniformProfiles … (prune := prune)`, which gives the same answer
  either way. Every witness set is computed up front (Lean is strict), but an
  error inside one is raised only when `anyM` reaches it, in profile order,
  as Haskell's `any` does. -/
  objSat (coalition : Std.TreeSet String)
      (w : Cgs s a → Except String (Std.TreeSet s)) : Except String (Std.TreeSet s) :=
    if states.isEmpty then pure ∅
    else do
      let profiles ← allUniformProfiles m coalition (prune := prune)
      let witnessSets := profiles.map fun prof => w (residualCgs m prof coalition)
      let kept ← states.toList.filterM fun st =>
        let need := req m coalition st
        witnessSets.anyM fun wE => do
          let ws ← wE
          pure (need.all fun t => ws.contains t)
      pure (Std.TreeSet.ofList kept)
  canNextClause (c : List String) (satPhi : Except String (Std.TreeSet s)) :
      Except String (Std.TreeSet s) :=
    objSat (Std.TreeSet.ofList c) fun res => preCLazy res ∅ satPhi
  go : Formula → Except String (Std.TreeSet s)
  | .bot => pure ∅
  | .atomF atm =>
      pure (states.filter fun st => (cgs.cgsLabeling st).contains atm.name)
  | .not f' =>
      if states.isEmpty then pure ∅
      else do
        let sf ← go f'
        pure (states \ sf)
  | .and l r => do
      let sl ← go l
      if sl.isEmpty then pure ∅
      else do
        let sr ← go r
        pure (sl ∩ sr)
  | .or l r => do
      -- `Set.union` forces its second argument first.
      let sr ← go r
      let sl ← go l
      pure (sl ∪ sr)
  | .implies l r => do
      let sr ← go r
      let diffPart ← do
        if states.isEmpty then pure (∅ : Std.TreeSet s)
        else do
          let sl ← go l
          pure (states \ sl)
      pure (diffPart ∪ sr)
  | .iff l r => do
      if states.isEmpty then
        -- `difference ∅ _` is ∅ unforced; then `intersection sl sr` forces
        -- `sl`, which is ∅ (a subset of `states`), so `sr` is skipped.
        let _ ← go l
        pure ∅
      else do
        let sr ← go r
        let sl ← go l
        pure ((sl ∩ sr) ∪ (states \ (sl ∪ sr)))
  -- K_a φ — as in ATEL (Gamen.Atel).
  | .knowledge agent phi =>
      if states.isEmpty then pure ∅
      else do
        let sphi ← go phi
        pure (states.filter fun st => (m.atelEpistemic agent st).all fun t => sphi.contains t)
  -- [C]φ — Coalition Logic one-step; treated as CanNext under ATLir.
  | .coalition c phi => canNextClause c (go phi)
  -- ⟨⟨C⟩⟩ir Xφ
  | .canNext c phi => canNextClause c (go phi)
  -- ⟨⟨C⟩⟩ir Gφ — greatest fixpoint in the residual, empty coalition.
  | .canAlways c phi =>
      let satPhi := go phi
      objSat (Std.TreeSet.ofList c) fun res => do
        let sp ← satPhi
        gfp states (fun x => sp ∩ preC res ∅ x) fuel
  -- ⟨⟨C⟩⟩ir Fφ — least fixpoint in the residual.
  | .canEventually c phi =>
      let satPhi := go phi
      objSat (Std.TreeSet.ofList c) fun res => do
        let sp ← satPhi
        lfp (fun x => sp ∪ preC res ∅ x) fuel
  -- ⟨⟨C⟩⟩ir (φ U ψ) — until as least fixpoint in the residual.
  | .canUntil c phi psi =>
      let satPhi := go phi
      let satPsi := go psi
      objSat (Std.TreeSet.ofList c) fun res => do
        let sp ← satPhi
        let sq ← satPsi
        lfp (fun x => sq ∪ (sp ∩ preC res ∅ x)) fuel
  -- Operators not supported in ATLir.
  | .box _ => throw "Box not supported in ATLir; use ⟨⟨Ag⟩⟩G"
  | .diamond _ => throw "Diamond not supported in ATLir"
  | .futureBox _ => throw "FutureBox not supported in ATLir; use CanAlways"
  | .futureDiamond _ => throw "FutureDiamond not supported in ATLir; use CanEventually"
  | .pastBox _ => throw "Past operators not supported in ATLir"
  | .pastDiamond _ => throw "Past operators not supported in ATLir"
  | .since _ _ => throw "Since not supported in ATLir"
  | .until _ _ => throw "Until not supported in ATLir"
  | .belief _ _ => throw "Belief not supported in ATLir; use Gamen.Epistemic"
  | .rankedBelief _ _ _ => throw "RankedBelief not supported in ATLir"
  | .announce _ _ => throw "Announce not supported in ATLir"
  | .stit _ _ => throw "Stit requires a STIT model"
  | .choiceDiamond _ _ => throw "ChoiceDiamond requires a STIT model"
  | .groupStit _ => throw "GroupStit requires a STIT model"
  | .next _ => throw "Next requires a Laca model"
  | .ought _ _ => throw "Ought requires a deontic model"
  | .permitted _ _ => throw "Permitted requires a deontic model"

/-- The set of states satisfying `φ` under the ATLir *subjective*
semantics (the default). -/
def atlirSat {s a : Type} [Ord s] [Ord a] [BEq s] (m : AtelModel s a) (f : Formula) :
    Except String (Std.TreeSet s) :=
  atlirSatWith subjectiveClass m f

/-- The set of states satisfying `φ` under the ATLir *objective* semantics
(the witnessing set need only contain the actual state). -/
def atlirSatObjective {s a : Type} [Ord s] [Ord a] [BEq s] (m : AtelModel s a)
    (f : Formula) : Except String (Std.TreeSet s) :=
  atlirSatWith (fun _ _ st => Std.TreeSet.ofList [st]) m f

-- ── Convenience wrappers ────────────────────────────────────────────────

/-- M, s ⊩_ir φ — ATLir satisfaction at a single state (subjective). -/
def atlirSatisfies {s a : Type} [Ord s] [Ord a] [BEq s] (m : AtelModel s a) (st : s)
    (f : Formula) : Except String Bool :=
  if !m.atelCgs.cgsStates.contains st then
    throw "atlirSatisfies: state not in cgsStates"
  else do
    let satSet ← atlirSat m f
    pure (satSet.contains st)

/-- A formula is true in an ATLir model (subjective) if it holds at every
state. -/
def atlirIsTrueIn {s a : Type} [Ord s] [Ord a] [BEq s] (m : AtelModel s a)
    (f : Formula) : Except String Bool := do
  let satSet ← atlirSat m f
  pure (satSet == m.atelCgs.cgsStates)

/-- M, s ⊩_ir φ — ATLir satisfaction at a single state (objective). -/
def atlirSatisfiesObjective {s a : Type} [Ord s] [Ord a] [BEq s] (m : AtelModel s a)
    (st : s) (f : Formula) : Except String Bool :=
  if !m.atelCgs.cgsStates.contains st then
    throw "atlirSatisfiesObjective: state not in cgsStates"
  else do
    let satSet ← atlirSatObjective m f
    pure (satSet.contains st)

/-- A formula is true in an ATLir model (objective) if it holds at every
state. -/
def atlirIsTrueInObjective {s a : Type} [Ord s] [Ord a] [BEq s] (m : AtelModel s a)
    (f : Formula) : Except String Bool := do
  let satSet ← atlirSatObjective m f
  pure (satSet == m.atelCgs.cgsStates)

end Gamen
