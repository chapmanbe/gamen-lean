import Gamen.Atl.Dynamic

/-!
# Gamen.Atl.SocialLaws

Behavioural constraints and social laws in ATL, and their translation into ATL-D
updates (the ATL-D paper's Theorem 3; Galimullin, Grosinger & Mittelmann, KR 2026).
Lean-only.

Source of the definitions: van der Hoek, Roberts & Wooldridge, *Social laws in
alternating time: effectiveness, feasibility, and synthesis*, Synthese 156(1):1-19, 2007,
doi:10.1007/s11229-006-9072-6, §4 (pp. 9-11), checked against the PDF:

* a **behavioural constraint** `β : Ac_Ag → 2^Q`; `q ∈ β(α)` means `α` is forbidden at `q`;
* it must be **reasonable**: at every state every agent keeps an allowed action;
* **implementation** `S † β` removes the transitions that use a forbidden action;
* a **social law** `(φ, β)` with `φ` an ATL objective is **effective** if `S † β ⊨ φ`.

Differences from the paper, forced by `Gamen.Cgs`: there each action belongs to one agent,
so `β` is indexed by the action alone; here actions can be shared, so a `Constraint` lists
`(action, agent, forbidden states)`. In vdHRW an unreasonable `β` is simply not a
constraint; `implementConstraint` reports it as an error. ATL-D's revoke update instead
keeps an agent's actions when a removal would empty them, so the two agree on reasonable
constraints, and only on those.

## Translation (ATL-D paper, before Theorem 3)

Targeting a single state needs a formula true only there, so `G⁺` labels every state `v`
with a fresh atom `state:v`. For `v ∈ η(α, a)` the update has the clause
`state:v : α → {a}`; `[π_η]−` is then a revoke. Theorem 3: for `φ ∈ ATL` and finite `G`,
`G † η, v ⊨ ⟨⟨∅⟩⟩Gφ` iff `G⁺, v ⊨ [π_η]− ⟨⟨∅⟩⟩Gφ`. `Tests/SocialLaws.lean` checks it.
-/
namespace Gamen
namespace Atl.Dynamic

/-- `(action, agent, states where that agent may not perform the action)`. -/
abbrev Constraint := List (String × String × List String)

/-- The atom naming state `v` in `G⁺`. It must not occur in the objective. -/
def stateAtom (v : String) : String := "state:" ++ v

/-- `G⁺`: every state `v` also satisfies its own atom `state:v`. -/
def DynModel.withStateAtoms (m : DynModel) : DynModel :=
  { m with cgs := { m.cgs with
      cgsLabeling := fun v => (m.cgs.cgsLabeling v).insert (stateAtom v) } }

/-- `π_η`: one revoke clause `state:v : α → {a}` per forbidden `(α, a, v)`. -/
def behaviouralUpdate (η : Constraint) : UpdateList :=
  η.foldr (fun (α, a, vs) rest =>
    vs.foldr (fun v r => .cons (.atom (stateAtom v)) α [a] [] r) rest) .nil

/-- `G † η` (vdHRW §4): remove every action `η` forbids. Errors if a name is unknown, or if
`η` is not reasonable (some agent left with no action at some state). -/
def implementConstraint (m : DynModel) (η : Constraint) : Except String DynModel := do
  for (α, a, vs) in η do
    unless m.actions.contains α do throw s!"constraint: unknown action \"{α}\""
    unless m.cgs.cgsAgents.contains a do throw s!"constraint: unknown agent \"{a}\""
    if let some v := vs.find? (fun v => !m.cgs.cgsStates.contains v) then
      throw s!"constraint: unknown state \"{v}\""
  let allowed (v a : String) : Std.TreeSet String :=
    (m.cgs.cgsMoves v a).filter fun α =>
      !η.any fun (α', a', vs) => α' == α && a' == a && vs.contains v
  for v in m.cgs.cgsStates.toList do
    for a in m.cgs.cgsAgents.toList do
      if (allowed v a).isEmpty then
        throw s!"behavioural constraint is not reasonable: agent \"{a}\" has no allowed action at state \"{v}\""
  pure { m with cgs := { m.cgs with cgsMoves := allowed } }

end Atl.Dynamic
end Gamen
