import Widgets.Dynamic.Library

/-!
# Who Can Order Now? Abilities That Change Hands Unseen

*The capstone of the dynamic-explorer notebooks. It joins the two earlier ones:
knowledge, from `DynamicEpistemic.lean`, and abilities that are granted and
revoked, from `DynamicAbility.lean`. The logic is ATEL-D, the epistemic
version of ATL-D from Galimullin, Grosinger & Mittelmann, "I Would If I Could:
Reasoning about Dynamics of Actions in Multi-Agent Systems," KR 2026 (Defs 8-11,
Algorithm 2), as implemented in `Gamen/Atl/Dynamic.lean`.*

**How to use this file.** Open it in VS Code (with the Lean 4 extension) or in
the course's Lean web editor, and put your cursor on the `#html` line below.
The explorer appears in the panel on the right. Tick update clauses, press
*Apply*, click states or type formulas, and press *Check* to get graded
feedback (*Reset* clears the boxes and starts over). Nothing in this file needs
editing.

## From a fact to an ability

In scenario 1 a *fact* reached only some people: the page told the doctor the
potassium was high, and the nurse was left not knowing that the doctor knew.
Here an *ability* changes hands, and not everyone finds out. At shift change,
the authority to order passes from the outgoing clinician to the incoming one.
The pharmacist, who has to act on orders, does not know whether the shift change
has happened yet, and so does not know who can order.

## The model

There are four states:

- `old-shift`: the shift has not changed;
- `new-shift`: it has (the atom `handoff` holds), but the pharmacist cannot tell
  this state from `old-shift`;
- `new-shift-present`: it has, and the pharmacist was there for it, so can tell;
- `ordered`: someone has placed an order.

At first only the outgoing clinician has the action `order`, which leads to
`ordered`; the incoming clinician and the pharmacist can only wait. The two
clinicians know whether the shift has changed, but not whether the pharmacist
was there.

## Updates that inform

ATEL-D keeps ATL-D's grant and revoke, and adds knowledge `K[a]φ`. An update
clause can name a second set of agents, written `[φ : α → {A}, {B}]`: the agents
in `B` gain or lose nothing, they are only *informed*. Every agent in `A` or `B`
learns whether the condition `φ` held (judged before the update): each such
agent can now tell a state where `φ` held from one where it did not. No one else
learns anything. In the explorer the clause
`grant handoff : order → {incoming} and inform {pharmacist}` is
`[handoff : order → {incoming}, {pharmacist}]+`.

So after `grant handoff : order → {incoming}` and
`revoke handoff : order → {outgoing}`, at `new-shift` the incoming clinician can
order and knows it, but the pharmacist does not know it: the pharmacist still
cannot rule out `old-shift`, where the incoming clinician cannot order. Inform
the pharmacist as well, and at `new-shift` the pharmacist knows the incoming
clinician can order. The pharmacist's ignorance of the ability is ignorance of
the condition: who can order depends on whether the shift has changed.

**A grant everywhere is a grant everyone knows about.** Give the grant the
condition `⊤` instead, informing no one, and the pharmacist knows the incoming
clinician can order at every state. The pharmacist has learned nothing; but
since the incoming clinician can now order at every state, every state the
pharmacist cannot rule out is one where it can. To change an ability without
everyone knowing, the change has to depend on something not everyone knows.
(The ⊤ grant is also the wrong update for this story: it lets the incoming
clinician order before the shift has changed.)

## Ability under uncertainty

`⟨⟨A⟩⟩` keeps its meaning from the ability notebook, with one change. An agent
who cannot tell two states apart cannot choose a different action in each, so
a strategy picks one action for all the states an agent cannot tell apart, and
must work from every one of them. This is the *subjective* reading, the one
`Gamen/Atl/Dynamic.lean` adopts for ATEL-D (following the paper's extended
version, Example 2), and the explorer uses it in this scenario. Here the
incoming clinician can make sure an order is placed next at `new-shift` and
`new-shift-present` after the update, and the outgoing clinician no longer can
there.

## The explorer

Work through the questions in order. Each tells you which clauses to tick, or
asks you to choose them.
-/

open Gamen.Widgets Gamen.Widgets.Dynamic ProofWidgets
open scoped ProofWidgets.Jsx

#html dynamicExplorerOr Library.shiftChange

/-!
## Summary

| Concept | In the explorer |
|---|---|
| `K[a]φ` | `φ` holds at every state `a` cannot rule out |
| `has(a,α)` | agent `a` has action `α` at this state |
| `[φ : α → {A}, {B}]+` | grant `α` to `A` where `φ` held; `A` and `B` learn whether `φ` held |
| `[φ : α → {A}, {B}]-` | the same, revoking |
| `⟨⟨A⟩⟩` (subjective) | one action per set of states an agent cannot tell apart, working from each |
| Condition `⊤` | changes the ability everywhere, so everyone knows the result |

**What the examples show.** Handing over authority is two changes, a grant and
a revoke, and a third question: who is told. A handoff that reaches the
incoming clinician but not the pharmacist leaves the pharmacist unable to say
who can order, even though nothing about the pharmacist's own actions changed.
Scenario 1 made the same point about a fact; this one makes it about an
ability.
-/
