import Widgets.Dynamic.Library

/-!
# Who Knows What After the Page? Action Models in Epistemic Logic

*An epistemic-logic companion to B&D (knowledge `K[a]φ`). The update itself follows Lorini, Perrotin & Schwarzentruber,
"Epistemic Actions: Comparing Multi-agent Belief Bases with Action Models,"
KR 2022 (Defs 7-9), as implemented in `Gamen/ActionModel.lean`.*

**How to use this file.** Open it in VS Code (with the Lean 4 extension) or in
the course's Lean web editor, and put your cursor on the `#html` line below.
The explorer appears in the panel on the right. You work entirely inside it:
tick the observers, press *Apply*, click worlds or type formulas, and
press *Check* to get graded feedback (*Reset* starts over). Nothing in this file needs editing.

## A page that may be lost

A lab system pages the covering team about a potassium result. In the world
`w1` the potassium is high (the atom `p`); in `w2` it is not. Before anything
happens, neither the nurse **N** nor the doctor **D** can tell `w1` from `w2`.

Then one of two **events** occurs:

- `sent`: the page is delivered. It can only happen where `p` is true (its
  *precondition* is `p`);
- `lost`: the page never arrives. It can happen anywhere (precondition `⊤`).

Whoever is paying attention (an **observer**) sees which event occurred.
Everyone else cannot tell the events apart.

## The idea: an action model

An *action model* lists the events, says what must hold for each to occur
(`pre`), and says, for each agent, which events that agent cannot tell apart.
The **product update** `M × A` builds a new model whose worlds are pairs
`world×event`, keeping a pair only when the world satisfies the event's
precondition. Agent `a` cannot tell `w×e` from `w'×e'` exactly when `a` could
not tell `w` from `w'` before **and** cannot tell `e` from `e'`.

An observer distinguishes every event from every other; a non-observer
distinguishes none. So ticking *D* in the explorer makes D an observer, and
the new worlds are `w1×sent`, `w1×lost`, and `w2×lost` (the pair `w2×sent` is
dropped, since `sent` requires `p`).

Two things to watch for as you work:

- **Higher-order knowledge.** `K[D]p` says D knows the potassium is high.
  `K[N]K[D]p` says N knows that D knows. A single page can give D knowledge
  without giving N knowledge *about* D's knowledge.
- **Why `K` fails.** `K[a]φ` holds at a world when `φ` holds at every world
  `a` cannot rule out. When you click a world where `K` fails, the feedback
  names a world `a` cannot rule out where `φ` is false.

## The explorer

Work through the four questions in order. The first, third and fourth tell you
what to select; the second asks for a formula.
-/

open Gamen.Widgets Gamen.Widgets.Dynamic ProofWidgets
open scoped ProofWidgets.Jsx

#html dynamicExplorerOr Library.handoff

/-!
## Summary

| Concept | In the explorer |
|---|---|
| Event | `sent`, `lost` |
| Precondition | `sent` requires `p`; `lost` requires nothing |
| Observer | an agent who can tell the events apart |
| Product world | `w×e`: world `w` after event `e` |
| `K[a]φ` | `φ` holds at every world `a` cannot rule out |
| `K[N]K[D]p` | N knows that D knows `p` |

**What the example shows.** One event can give one agent knowledge while
leaving everyone else ignorant of that fact. Making the handoff reliable
means making sure the right people observe the right events, not only that
the message is sent.
-/
