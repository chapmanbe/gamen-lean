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

end Gamen
