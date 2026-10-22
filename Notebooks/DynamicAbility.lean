import Widgets.Dynamic.Library

/-!
# I Would If I Could: Granting and Revoking Actions

*A companion on strategic ability that changes. The logic is ATL-D, from
Galimullin, Grosinger & Mittelmann, "I Would If I Could: Reasoning about
Dynamics of Actions in Multi-Agent Systems," KR 2026 (Def 1 for the formulas,
Def 4 for `has`, grant and revoke, Algorithm 1 for model checking), as
implemented in `Gamen/Atl/Dynamic.lean`.*

**How to use this file.** Open it in VS Code (with the Lean 4 extension) or in
the course's Lean web editor, and put your cursor on one of the `#html` lines
below. The explorer appears in the panel on the right. Tick update clauses,
press *Apply*, click states or type formulas, and press *Check* to get graded
feedback (*Reset* clears the boxes and starts over). Nothing in this file needs
editing.

## Agents, actions, and states

A model here is a *concurrent game structure*: a set of **states**, a set of
**agents**, and, at every state, the **actions** each agent has available. At
each step every agent picks one of its actions at once; the resulting *joint
action* decides the next state. In the explorer, an arrow is labeled with the
joint action that takes it, e.g. `patient=visit, staff=wait`. A model need not
list every joint action: in the referral scenario below, any joint action it
leaves out keeps the state where it is. Those are drawn as one dashed loop per
state, labeled `otherwise: stay`; at `primary`, before any grant, it is the
only arrow, since waiting is all anyone can do there.

## Saying what a group can do

`⟨⟨A⟩⟩` reads "the agents in `A`, acting together, have a strategy such that,
whatever the other agents do, ...". It is followed by a temporal operator:

| Formula | The group `A` can make sure that ... |
|---|---|
| `⟨⟨A⟩⟩X φ` | `φ` holds at the next state |
| `⟨⟨A⟩⟩G φ` | `φ` holds now and at every state from here on |
| `⟨⟨A⟩⟩F φ` | `φ` holds now or at some later state |
| `⟨⟨A⟩⟩(φ U ψ)` | `ψ` eventually holds, and `φ` holds at every state before that |

Two details matter in the questions. First, `F` and `G` include the present
state: `⟨⟨A⟩⟩F φ` is true wherever `φ` already is. Second, the other agents are
opponents: a strategy for `A` must work whatever they choose, so an action held
by someone outside `A` does not help `A`. For example, in the referral scenario
below, at `home` the patient can make sure the next state is `primary`
(`⟨⟨patient⟩⟩X primary`, by visiting), and can also keep away from treatment
forever (`⟨⟨patient⟩⟩G ¬treated`, by waiting).

## Having an action, and changing who has it

ATL-D adds `has(a,α)`: agent `a` has action `α` available at the current state
(Def 4). An action's name on its own is not a formula: write `refer` and the
explorer tells you it is not an atom of the model. And it adds **updates** that change who has what. An update is a list
of clauses `φ : α → {A}`, each read "at every state where `φ` holds, the agents
in `A` get (or lose) `α`":

- **Grant** `[φ : α → {A}]+ψ`: add `α` to each agent in `A` at every state where
  `φ` holds, then check `ψ` in the new model.
- **Revoke** `[φ : α → {A}]-ψ`: remove `α` from them there, then check `ψ`.

Every condition `φ` is evaluated in the model *before* the update, at every
state at once; the clauses of one update are applied simultaneously, not one
after another. An update changes only who has which action: the arrows a joint
action takes stay the same.

Revoking has one exception, the paper's **reasonableness** rule (Def 4,
Algorithm 1): an agent never loses its last action at a state. If removing the
actions would leave an agent with nothing to do at a state, the agent keeps all
of its actions there. The explorer reports each place where this happens in
its notes box.

In the explorer, each update clause is a checkbox, labeled with its kind and
the clause, e.g. `grant primary : refer → {patient}`. Ticked clauses are
applied in the order listed; consecutive clauses of the same kind form one
simultaneous update. You do not type updates yourself: you tick them, and your
formulas are evaluated in the model the explorer shows. A question about a
particular update is graded only with exactly its clauses ticked and applied;
otherwise the explorer tells you which to tick.

## Scenario 2: the missing referral

A patient wants specialist treatment. The patient can get as far as primary
care, but going on to the specialist needs a referral, and nobody has that
action yet. This is the paper's title in miniature: the patient would if the
patient could. Which grant fixes it, and which grants only look as if they do?
-/

open Gamen.Widgets Gamen.Widgets.Dynamic ProofWidgets
open scoped ProofWidgets.Jsx

#html dynamicExplorerOr Library.wouldIfCould

/-!
## Scenario 3: safety versus access

Taking an action away to prevent harm can take it away where it is needed.
Here a care team can override a pharmacy check. In routine care the override
lets an error through; in an emergency it is the only way the medication gets
given, since waiting for verification stays in the emergency. Watch the notes box: one revoke is not applied everywhere you
might expect, because of the reasonableness rule.
-/

#html dynamicExplorerOr Library.safetyAccess

/-!
## Summary

| Concept | In the explorer |
|---|---|
| `⟨⟨A⟩⟩X/G/F/U` | what the group `A` can make sure of, whatever the others do |
| `has(a,α)` | agent `a` has action `α` at this state |
| Grant `[φ : α → {A}]+` | add `α` for `A` wherever `φ` held before the update |
| Revoke `[φ : α → {A}]-` | remove `α` for `A` wherever `φ` held before the update |
| Reasonableness | a revoke never leaves an agent with no action at a state |

**What the examples show.** An ability can be missing because the action is
missing, and granting it to the wrong agent, or under a condition judged in the
wrong model, does not help. Taking an action away is just as blunt: a revoke
written for one situation reaches every state its condition covers.

## Coming next: scenario 4

A scenario on the path to first treatment for pancreatic cancer will follow,
built on a different logic (angels and demons), once its sources have been
read.
-/
