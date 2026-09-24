import Gamen.Kripke

/-!
# Gamen.Semantics

Port of `gamen-hs/src/Gamen/Semantics.hs`: the satisfaction relation
(B&D Definition 1.7) plus the temporal clauses (Lorini 2013).

Haskell's `satisfies` returns `Bool` and calls `error` for operators that
need a richer model (Knowledge, Stit, ...). Lean has no exception-throwing
`error` in pure code — `panic!` logs and then returns a default value — so
this port returns `Except String Bool` and the unsupported-operator case is
an ordinary value callers must handle.
-/
namespace Gamen

open Formula in
/-- `satisfies m w f` — B&D Definition 1.7, M, w ⊩ f. -/
def satisfies (m : Model) (w : World) (f : Formula) : Except String Bool := do
  unless m.frame.worlds.contains w do
    throw s!"satisfies: world {w} is not in model"
  let acc := m.frame.accessible
  let ws := m.frame.worlds.toList
  match f with
  | .bot => return false
  | .atomF a => return (m.valuation.getD a ∅).contains w
  | .not g => return !(← satisfies m w g)
  | .and l r => return (← satisfies m w l) && (← satisfies m w r)
  | .or l r => return (← satisfies m w l) || (← satisfies m w r)
  | .implies l r => return !(← satisfies m w l) || (← satisfies m w r)
  | .iff l r => return (← satisfies m w l) == (← satisfies m w r)
  | .box g | .futureBox g => (acc w).toList.allM (satisfies m · g)
  | .diamond g | .futureDiamond g => (acc w).toList.anyM (satisfies m · g)
  | .pastBox g =>
      ws.allM fun t' => do return !(acc t').contains w || (← satisfies m t' g)
  | .pastDiamond g =>
      ws.anyM fun t' => do return (acc t').contains w && (← satisfies m t' g)
  | .since b c =>
      ws.anyM fun t' => do
        if !(acc t').contains w then return false
        if !(← satisfies m t' c) then return false
        ws.allM fun s => do
          if s == t' || s == w || !((acc t').contains s && (acc s).contains w) then
            return true
          satisfies m s b
  | .until b c =>
      (acc w).toList.anyM fun t' => do
        if !(← satisfies m t' c) then return false
        ws.allM fun s => do
          if s == w || s == t' || !((acc w).contains s && (acc s).contains t') then
            return true
          satisfies m s b
  | .knowledge .. => throw "Knowledge operator requires an EpistemicModel (use Gamen.Epistemic)"
  | .belief .. => throw "Belief operator requires an EpistemicModel (use Gamen.Epistemic)"
  | .rankedBelief .. => throw "RankedBelief operator requires a KappaModel (use Gamen.RankingTheory)"
  | .announce .. => throw "Announce operator requires an EpistemicModel (use Gamen.Epistemic)"
  | .stit .. => throw "Stit operator requires a StitModel (use Gamen.Stit)"
  | .choiceDiamond .. =>
      throw "ChoiceDiamond operator requires a StitModel or DSModel (use Gamen.Stit or Gamen.DeonticStit)"
  | .groupStit .. => throw "GroupStit operator requires a StitModel (use Gamen.Stit)"
  | .next .. => throw "Next operator requires a LacaModel (use Gamen.Laca)"
  | .ought .. => throw "Ought operator requires a DSModel (use Gamen.DeonticStit)"
  | .permitted .. => throw "Permitted operator requires a DSModel (use Gamen.DeonticStit)"
  | .coalition .. => throw "Coalition operator requires a Cgs model (use Gamen.Coalition)"
  | .canNext .. => throw "CanNext requires a Cgs model (use Gamen.Atl)"
  | .canAlways .. => throw "CanAlways requires a Cgs model (use Gamen.Atl)"
  | .canEventually .. => throw "CanEventually requires a Cgs model (use Gamen.Atl)"
  | .canUntil .. => throw "CanUntil requires a Cgs model (use Gamen.Atl)"
termination_by f

/-- B&D Definition 1.9: true in a model, i.e., at every world. -/
def isTrueIn (m : Model) (f : Formula) : Except String Bool :=
  m.frame.worlds.toList.allM (satisfies m · f)

/-- A formula is valid in a class of models if true in every model
(B&D Definition 1.11). -/
def isValid (models : List Model) (f : Formula) : Except String Bool :=
  models.allM (isTrueIn · f)

open Formula in
/-- The maximal non-propositional subformulas of a formula: the `opaque`
helper inside gamen-hs's `abstractModal`. -/
def opaqueSubformulas : Formula → Std.TreeSet Formula
  | .bot => ∅
  | .atomF _ => ∅
  | .not a => opaqueSubformulas a
  | .and l r | .or l r | .implies l r | .iff l r =>
    (opaqueSubformulas l).insertMany (opaqueSubformulas r).toList
  | f => (∅ : Std.TreeSet Formula).insert f

/-- The prefix for `abstractModal`'s generated atoms: the shortest
`"__modal:"`, `"___modal:"`, … that no atom name in `names` starts with.
gamen-hs gets it with `until`, adding one `_` at a time; here it is
computed directly. A name blocks exactly one candidate (its leading
underscores, when at least two are followed by `"modal:"`), so the
answer is the smallest count ≥ 2 not blocked. -/
def modalPrefix (names : List String) : String :=
  let blocked := names.filterMap fun n =>
    let k := (n.toList.takeWhile (· == '_')).length
    if k ≥ 2 && (String.ofList (n.toList.drop k)).startsWith "modal:" then some k else none
  let sorted := (blocked.mergeSort (· ≤ ·)).eraseDups
  let k := sorted.foldl (fun k b => if b == k then k + 1 else k) 2
  String.ofList (List.replicate k '_') ++ "modal:"

open Formula in
/-- Replace every maximal non-propositional subformula with a fresh atom.
Identical subformulas map to the same atom (both occurrences of `□p` in
`□p ∨ ¬□p` become one variable, keeping it a tautology); distinct
subformulas get distinct atoms. Port of gamen-hs's `abstractModal` after
the fix for chapmanbe/gamen-hs#31: the key is the `Formula` itself, not
its printed form, which is not injective (`Stit "a" p` and
`Announce (Atom "a") p` both print as `[a]p`). Subformulas are numbered in
`Ord` order; `Formula`'s constructors are declared in the same order as the
Haskell's, so the derived orders agree and the generated names match
gamen-hs's. The prefix comes from `modalPrefix`, so a generated atom cannot
collide with a user-written one.

Returns `Except` because the table lookup cannot fail for a subformula of
the input, but Lean does not know that; an error here is a bug, not a
`false`. -/
def abstractModal (f0 : Formula) : Except String Formula :=
  let table : Std.TreeMap Formula Nat :=
    (opaqueSubformulas f0).toList.zipIdx.foldl (fun m (f, i) => m.insert f i) ∅
  go table (modalPrefix ((atoms f0).toList.map (·.name))) f0
where
  go (table : Std.TreeMap Formula Nat) (pre : String) : Formula → Except String Formula
    | .bot => pure .bot
    | .atomF a => pure (.atomF a)
    | .not a => return .not (← go table pre a)
    | .and l r => return .and (← go table pre l) (← go table pre r)
    | .or l r => return .or (← go table pre l) (← go table pre r)
    | .implies l r => return .implies (← go table pre l) (← go table pre r)
    | .iff l r => return .iff (← go table pre l) (← go table pre r)
    -- Any non-propositional constructor is opaque at the propositional
    -- level: abstract the whole subformula to one variable.
    | f => match table.get? f with
      | some i => pure (.atomF ⟨pre ++ toString i⟩)
      | none => throw s!"abstractModal: {f} missing from its own subformula table"

/-- Is the formula a propositional tautology — a substitution instance
of a tautology of classical propositional logic (B&D Definition 1.14;
Proposition 1.16 is that every tautological instance is valid)?

Each *maximal* non-propositional subformula (any `box`, `diamond`,
temporal, epistemic, deontic, STIT, or ATL node) is first abstracted to
a fresh propositional atom via `abstractModal`, then all `2^n` truth
assignments to the resulting atoms are enumerated. Abstraction is
essential: evaluating a modal subformula at a dead-end world (the
previous gamen-hs approach) made `□⊥` vacuously true and reported it —
and `¬◇p` — as tautologies (adversarial review B5). For modal-validity
questions, build explicit Kripke models and use `isValid`. -/
def isTautology (phi0 : Formula) : Except String Bool := do
  let phi ← abstractModal phi0
  let atomList := phi.atoms.toList
  let n := atomList.length
  let cases := 2 ^ n
  let indexed := atomList.zip (List.range n)
  (List.range cases).allM fun k => do
    let trueAtoms := indexed.filterMap fun (a, i) =>
      if k.testBit i then some (a.name, ["w"]) else none
    let fr ← mkFrame ["w"] []
    isTrueIn (mkModel fr trueAtoms) phi

/-- Γ entails A in model M if: for every world w, if all premises
hold at w then the conclusion holds at w (B&D Definition 1.23). -/
def entails (m : Model) (premises : List Formula) (conclusion : Formula) :
    Except String Bool :=
  m.frame.worlds.toList.allM fun w => do
    if (← premises.allM (satisfies m w ·)) then
      satisfies m w conclusion
    else
      return true

end Gamen
