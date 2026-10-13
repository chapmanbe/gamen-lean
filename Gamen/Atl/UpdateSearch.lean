import Gamen.Atl.Dynamic
import Std.Data.HashMap

/-!
# Gamen.Atl.UpdateSearch

The bounded update existence problem for ATL-D / ATEL-D (Galimullin, Grosinger &
Mittelmann, KR 2026, Def 7, Theorem 6): given a model, a state `v`, a goal `φ` and a
bound `n`, is there a sequence of updates `[π⃗]` of size at most `n` with
`M, v ⊨ [π⃗]φ`? Lean-only. Plan: `plans/atl-d-2026-10-13.md`.

## What is searched, exactly

The paper's updates may use any ATL-D formula as a condition, so the unrestricted search
space is infinite and its size measure (symbols of `[π⃗]φ`) is not what a caller
usually wants to bound. This module therefore solves a *finite, explicit* version:

* the candidate **pool** is a finite list of clauses `(grant | revoke, condition,
  action, agents, informed)`; `defaultPool` is every `⊤`/atom/`¬atom` condition with
  every action, every single agent, grant and revoke;
* the **size** of a sequence is its total number of clauses (not symbols);
* a sequence is a list of *brackets*, each a nonempty set of clauses of one kind applied
  simultaneously (as `[π]+`/`[π]-`); brackets run in order.

`notFound` therefore means "no sequence over this pool within the bound", never "no
update exists". Updates that would be errors when evaluated (a grant enabling a joint
move with no stated successor, an update that breaks `∼`) are not legal moves; they are
counted in `illegal`, not silently dropped.

## Search

Breadth first by cost over *distinct models* (the action table and `∼`), so the many
clause sets with the same effect are explored once. All nodes of cost `s` exist before
layer `s` is examined, so the first hit is minimal. A fuel on candidate clause sets
tried turns exhaustion into an error, never a default answer.
-/
namespace Gamen
namespace Atl.Dynamic

/-- One clause of an update, with its kind. -/
structure Candidate where
  grant : Bool
  cond : DFormula
  action : String
  agents : List String
  informed : List String := []

/-- A bracket: clauses of one kind applied simultaneously. -/
structure Step where
  grant : Bool
  clauses : List Candidate

def Step.updates (st : Step) : UpdateList :=
  st.clauses.foldr (fun c rest => .cons c.cond c.action c.agents c.informed rest) .nil

/-- `[π1]±[π2]±…φ`. -/
def stepsFormula (steps : List Step) (goal : DFormula) : DFormula :=
  steps.foldr (fun st f => if st.grant then .grant st.updates f else .revoke st.updates f) goal

inductive SearchOutcome where
  | found (steps : List Step) (size : Nat)
  | notFound

structure SearchReport where
  outcome : SearchOutcome
  /-- Candidate clause sets tried. -/
  explored : Nat
  /-- Of those, how many were not legal moves (see the module docstring). -/
  illegal : Nat

/-- Every atom/negated-atom/`⊤` condition × action × single agent × grant/revoke. -/
def defaultPool (m : DynModel) : List Candidate :=
  let atoms := m.cgs.cgsStates.toList.flatMap (fun v => (m.cgs.cgsLabeling v).toList) |>.eraseDups
  let conds : List DFormula :=
    .not .bot :: (atoms.flatMap fun p => [DFormula.atom p, .not (.atom p)])
  [true, false].flatMap fun g =>
    conds.flatMap fun c =>
      m.actions.toList.flatMap fun a =>
        m.cgs.cgsAgents.toList.map fun ag => { grant := g, cond := c, action := a, agents := [ag] }

/-- The `k`-element sublists, in order. -/
def combos {α : Type} : List α → Nat → List (List α)
  | _, 0 => [[]]
  | [], _ + 1 => []
  | x :: xs, k + 1 => (combos xs k).map (x :: ·) ++ combos xs (k + 1)

/-- Identifies a model by what updates can change: actions and `∼`. -/
def modelKey (m : DynModel) : String :=
  let moves := m.cgs.cgsStates.toList.flatMap fun v =>
    m.cgs.cgsAgents.toList.map fun a => (m.cgs.cgsMoves v a).toList
  let epi := m.cgs.cgsStates.toList.flatMap fun v =>
    m.cgs.cgsAgents.toList.map fun a => (m.epistemic a v).toList
  toString (repr (moves, epi))

private structure Node where
  model : DynModel
  /-- Steps taken, most recent first. -/
  steps : List Step

/-- Bounded update existence (Def 7) over `pool`; see the module docstring. -/
def boundedUpdate (m : DynModel) (mode : IrMode) (v : String) (goal : DFormula) (n : Nat)
    (pool : List Candidate) (fuel : Nat) : Except String SearchReport := do
  unless m.cgs.cgsStates.contains v do throw s!"boundedUpdate: unknown state \"{v}\""
  for c in pool do
    unless m.actions.contains c.action do throw s!"pool: unknown action \"{c.action}\""
    if let some a := (c.agents ++ c.informed).find? (fun a => !m.cgs.cgsAgents.contains a) then
      throw s!"pool: unknown agent \"{a}\""
  let mut layers : Array (List Node) := Array.replicate (n + 1) []
  let mut seen : Std.HashMap String Nat := {}
  layers := layers.set! 0 [{ model := m, steps := [] }]
  seen := seen.insert (modelKey m) 0
  let mut explored := 0
  let mut illegal := 0
  for s in [0:n + 1] do
    for node in layers[s]! do
      if (← dsat node.model mode goal).contains v then
        return { outcome := .found node.steps.reverse s, explored, illegal }
    if s < n then
      for node in layers[s]! do
        for grant in [true, false] do
          let cands := pool.filter (·.grant == grant)
          let sets ← cands.mapM fun c => dsat node.model mode c.cond
          let indexed := cands.zip sets
          for k in [1:n - s + 1] do
            for combo in combos indexed k do
              explored := explored + 1
              if explored > fuel then
                throw s!"update search budget exhausted after {fuel} candidate clause sets"
              let clauses : List Clause := combo.map fun (c, sv) => (sv, c.action, c.agents, c.informed)
              let m' := updateModel node.model grant clauses
              let ok := (if grant then (checkSpecified m').isOk else true) && (checkEpistemic m').isOk
              if !ok then
                illegal := illegal + 1
              else
                let key := modelKey m'
                let cost := s + k
                if let some old := seen.get? key then
                  if old ≤ cost then continue
                seen := seen.insert key cost
                layers := layers.modify cost fun l =>
                  { model := m', steps := { grant, clauses := combo.map (·.1) } :: node.steps } :: l
  return { outcome := .notFound, explored, illegal }

end Atl.Dynamic
end Gamen
