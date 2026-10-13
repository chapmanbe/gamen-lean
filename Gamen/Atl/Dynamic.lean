import Gamen.Atl.ModelCheck
import Gamen.Cgs
import Std.Data.HashMap

/-!
# Gamen.Atl.Dynamic

ATL-D: ATL with dynamic actions (perfect information). Lean-only; gamen-hs
has no counterpart. Source: Galimullin, Grosinger & Mittelmann, *I Would If
I Could: Reasoning about Dynamics of Actions in Multi-Agent Systems*, KR 2026,
doi:10.24963/kr.2026/31 (Defs 1-4 and Algorithm 1). Plan:
`plans/atl-d-2026-10-13.md`. ATEL-D (informed agents, `K_a`) is a later phase.

## What it adds to ATL

* `has a α`: agent `a` currently has action `α` (Def 4).
* `grant`/`revoke` updates `[φ1:α1→A1, …, φk:αk→Ak]±ψ`. Every `φi` is
  evaluated in the *current* model, at every state, simultaneously (an update
  is not a chain of updates). Granting adds `αi` to `d(a, v)` for `a ∈ Ai`,
  `v ⊨ φi`. Revoking removes them, except that an agent never loses its last
  action at a state ("reasonableness"): if the removal would empty `d(a, v)`,
  `a` keeps all of `d(a, v)` there. The transition function is unchanged.
  `ψ` is then checked in the updated model (Algorithm 1).
* The release operator `⟨⟨A⟩⟩φRψ` (Def 4); `⟨⟨A⟩⟩Gφ = ⟨⟨A⟩⟩⊥Rφ`.

## Disabled transitions

The paper's transition function is total on *all* joint actions, including
ones no agent currently has available. A `DynModel` carries the action
universe and a `specified` predicate saying which joint moves have a stated
successor. After a grant, every joint move that is now available must be
`specified`; otherwise `dsat` returns an error rather than inventing a
successor. A model with a default successor (`CgsJson`'s `default_next`)
specifies everything.

States, agents and actions are `String`s, as in `Gamen.CgsJson`.

Strict evaluation: unlike `Gamen.Atl.sat`, there is no gamen-hs behavior to
match, so an error in any subformula is an error.
-/
namespace Gamen
namespace Atl.Dynamic

/-- A CGS plus the data an update needs. -/
structure DynModel where
  cgs : Cgs String String
  /-- All actions that exist; `has`, `grant` and `revoke` may only name these. -/
  actions : Std.TreeSet String
  /-- Whether the joint move at the state has a stated successor. -/
  specified : String → Std.TreeMap String String → Bool

mutual
/-- ATL-D formulas (Def 1). `UpdateList` is a separate inductive so that the
conditions inside an update are ordinary structural subterms. -/
inductive DFormula where
  | bot
  | atom (name : String)
  | not (f : DFormula)
  | and (l r : DFormula)
  | or (l r : DFormula)
  | implies (l r : DFormula)
  | iff (l r : DFormula)
  | has (agent action : String)
  | canNext (agents : List String) (f : DFormula)
  | canAlways (agents : List String) (f : DFormula)
  | canEventually (agents : List String) (f : DFormula)
  | canUntil (agents : List String) (l r : DFormula)
  | canRelease (agents : List String) (l r : DFormula)
  | grant (updates : UpdateList) (f : DFormula)
  | revoke (updates : UpdateList) (f : DFormula)

/-- `φ1 : α1 → A1, …, φk : αk → Ak`. -/
inductive UpdateList where
  | nil
  | cons (cond : DFormula) (action : String) (agents : List String) (rest : UpdateList)
end

namespace DFormula

mutual
protected def toString : DFormula → String
  | .bot => "⊥"
  | .atom n => n
  | .not f => "¬" ++ f.toString
  | .and l r => "(" ++ l.toString ++ " ∧ " ++ r.toString ++ ")"
  | .or l r => "(" ++ l.toString ++ " ∨ " ++ r.toString ++ ")"
  | .implies l r => "(" ++ l.toString ++ " → " ++ r.toString ++ ")"
  | .iff l r => "(" ++ l.toString ++ " ↔ " ++ r.toString ++ ")"
  | .has a α => s!"has({a},{α})"
  | .canNext as f => s!"⟨⟨{",".intercalate as}⟩⟩X" ++ f.toString
  | .canAlways as f => s!"⟨⟨{",".intercalate as}⟩⟩G" ++ f.toString
  | .canEventually as f => s!"⟨⟨{",".intercalate as}⟩⟩F" ++ f.toString
  | .canUntil as l r => s!"⟨⟨{",".intercalate as}⟩⟩(" ++ l.toString ++ " U " ++ r.toString ++ ")"
  | .canRelease as l r => s!"⟨⟨{",".intercalate as}⟩⟩(" ++ l.toString ++ " R " ++ r.toString ++ ")"
  | .grant us f => "[" ++ DFormula.updatesToString us ++ "]+" ++ f.toString
  | .revoke us f => "[" ++ DFormula.updatesToString us ++ "]-" ++ f.toString

protected def updatesToString : UpdateList → String
  | .nil => ""
  | .cons c α as .nil => c.toString ++ ":" ++ α ++ "→{" ++ ",".intercalate as ++ "}"
  | .cons c α as rest =>
      c.toString ++ ":" ++ α ++ "→{" ++ ",".intercalate as ++ "}, " ++ DFormula.updatesToString rest
end

instance : ToString DFormula := ⟨DFormula.toString⟩

end DFormula

/-- A resolved update clause: the states where its condition holds, the action,
the agents. -/
abbrev Clause := Std.TreeSet String × String × List String

/-- The model after granting (`grant = true`) or revoking the clauses' actions.
`d'(a, v) = d(a, v) ∪ X(a, v)` or, for revocation, `d(a, v) \ X(a, v)` unless
that leaves `a` with nothing at `v` (Def 4, Algorithm 1 lines 13-21). -/
def updateModel (m : DynModel) (grant : Bool) (clauses : List Clause) : DynModel :=
  let cgs := m.cgs
  let newMoves : Std.HashMap (String × String) (Std.TreeSet String) :=
    cgs.cgsStates.toList.foldl (init := {}) fun acc v =>
      cgs.cgsAgents.toList.foldl (init := acc) fun acc a =>
        let x : Std.TreeSet String := Std.TreeSet.ofList
          (clauses.filterMap fun (sv, α, as) => if sv.contains v && as.contains a then some α else none)
        let d := cgs.cgsMoves v a
        let d' :=
          if grant then d ∪ x
          else
            let rest := d \ x
            if rest.isEmpty then d else rest
        acc.insert (v, a) d'
  { m with cgs := { cgs with cgsMoves := fun v a => (newMoves.get? (v, a)).getD (cgs.cgsMoves v a) } }

/-- Every joint move available in `m` has a stated successor. -/
def checkSpecified (m : DynModel) : Except String Unit :=
  match m.cgs.cgsStates.toList.findSome? fun v =>
      (jointMoves m.cgs m.cgs.cgsAgents v).findSome? fun jm =>
        if m.specified v jm then none else some (v, jm) with
  | none => pure ()
  | some (v, jm) =>
    throw s!"an update enables a joint move with no stated successor (state \"{v}\", \
      {", ".intercalate (jm.toList.map fun (a, α) => s!"{a}={α}")}); \
      give the model a default_next"

/-- Fuel for the fixpoints, as in `Gamen.Atl.sat`: `|states| + 1`. -/
private def fuelOf (m : DynModel) : Nat := m.cgs.cgsStates.size + 1

mutual
/-- `{v | M, v ⊨ f}` (Def 4, Algorithm 1). -/
def dsat (m : DynModel) : DFormula → Except String (Std.TreeSet String)
  | .bot => pure ∅
  | .atom n => pure (m.cgs.cgsStates.filter fun v => (m.cgs.cgsLabeling v).contains n)
  | .not f => do pure (m.cgs.cgsStates \ (← dsat m f))
  | .and l r => do pure ((← dsat m l) ∩ (← dsat m r))
  | .or l r => do pure ((← dsat m l) ∪ (← dsat m r))
  | .implies l r => do pure ((m.cgs.cgsStates \ (← dsat m l)) ∪ (← dsat m r))
  | .iff l r => do
      let sl ← dsat m l
      let sr ← dsat m r
      pure ((sl ∩ sr) ∪ (m.cgs.cgsStates \ (sl ∪ sr)))
  | .has a α => do
      unless m.cgs.cgsAgents.contains a do throw s!"has: unknown agent \"{a}\""
      unless m.actions.contains α do throw s!"has: unknown action \"{α}\""
      pure (m.cgs.cgsStates.filter fun v => (m.cgs.cgsMoves v a).contains α)
  | .canNext as f => do
      pure (preC m.cgs (Std.TreeSet.ofList as) (← dsat m f))
  | .canAlways as f => do
      let sf ← dsat m f
      gfp m.cgs.cgsStates (fun x => sf ∩ preC m.cgs (Std.TreeSet.ofList as) x) (fuelOf m)
  | .canEventually as f => do
      let sf ← dsat m f
      lfp (fun x => sf ∪ preC m.cgs (Std.TreeSet.ofList as) x) (fuelOf m)
  | .canUntil as l r => do
      let sl ← dsat m l
      let sr ← dsat m r
      lfp (fun x => sr ∪ (sl ∩ preC m.cgs (Std.TreeSet.ofList as) x)) (fuelOf m)
  | .canRelease as l r => do
      -- νX. ψ ∩ (φ ∪ preC(X)); `⟨⟨A⟩⟩Gφ = ⟨⟨A⟩⟩⊥Rφ` (Def 4).
      let sl ← dsat m l
      let sr ← dsat m r
      gfp m.cgs.cgsStates
        (fun x => sr ∩ (sl ∪ preC m.cgs (Std.TreeSet.ofList as) x)) (fuelOf m)
  | .grant us f => do
      let clauses ← dclauses m us
      let m' := updateModel m true clauses
      checkSpecified m'
      dsat m' f
  | .revoke us f => do
      let clauses ← dclauses m us
      dsat (updateModel m false clauses) f

/-- Evaluate every condition in the *current* model `m` (simultaneity), and
check the named agents and actions exist. -/
def dclauses (m : DynModel) : UpdateList → Except String (List Clause)
  | .nil => pure []
  | .cons c α as rest => do
      unless m.actions.contains α do throw s!"update: unknown action \"{α}\""
      if let some a := as.find? (fun a => !m.cgs.cgsAgents.contains a) then
        throw s!"update: unknown agent \"{a}\""
      let sc ← dsat m c
      pure ((sc, α, as) :: (← dclauses m rest))
end

/-- Is `f` true at every state? -/
def dIsTrueIn (m : DynModel) (f : DFormula) : Except String Bool := do
  pure ((← dsat m f) == m.cgs.cgsStates)

end Atl.Dynamic
end Gamen
