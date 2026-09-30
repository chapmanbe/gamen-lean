# Counterfactuals at outcome nodes: an implementation defect and a proposed fix

*gamen-lean, 2026-09-30. For Jeremiah and Brian. Section numbers and pages
refer to the final thesis (June 4, 2026), pinned in `notes/dcleg-edition.md`.*

## Summary

At outcome nodes, gamen-lean's executable DCLEG model builds an **empty**
premise function F. The thesis never asks for that. It leaves F
*unspecified*, a parameter subject only to Centering and Contemporary
Universality. "No premises" breaks both conditions, and it makes **every**
counterfactual true at every outcome node. So the defect is in our code,
not in the thesis. As Jeremiah pointed out, not specifying the premises is
different from giving no premises.

The proposed fix follows his suggestion: use *any* premise set that
satisfies the thesis's conditions. Concretely:
1. the default construction always produces an admissible F;
2. the model validator rejects any F that isn't admissible;
3. anything that tests a validity varies F over admissible choices, rather
   than trusting one default.

## What the thesis says

§3.2.2 (p. 19) defines the set of indices, the pairs where a node is
actually reached:

> I := {(γ, w) | w ∈ V_γ}, …

The premise function assigns each world–node pair a set of propositions
(subsets of I):

> F : (Γ × V) → P(P(I)) … We require the following restrictions on F:
> 1. ∀γ ∈ Γ. ∀w ∈ V. ⋂F(γ, w) = {(γ, w)} (Centering)
> 2. ∀β, γ ∈ Γ. (w ∈ V_β) → ((β, w) ∈ ⋃F(γ, w)) (Contemporary Universality)

Nothing more is said about F. It is part of the model, like the valuation.
Truth of a counterfactual at a point depends on it, and **validity**
quantifies over every model, hence over every admissible F.

(A related detail in the same definition: since each premise is a subset of
I, Centering can only hold at reached pairs, w ∈ V_γ. The formalization
reads it that way; see Q7 in `DclegProofs/Semantics.lean`.)

## What our code does

- **Where F comes from.** `Gamen.Dcleg.withMovePremises` builds F. It is
  gamen-hs's construction, ported unchanged, **not** Jeremiah's. For each
  decision node w reached in γ, it creates one premise per available move
  (the worlds that play that move at w). The branch
  `worktree-agent-a9d2aa02e455338d0` now also adds {(γ,w)}, to fix
  Centering at single-move nodes.
- **Outcome nodes get no entry at all.**
- **How the evaluator reads that.** It treats a missing F(γ,w) as the empty
  set. With no non-empty premise sets, there are no "maximally
  φ-consistent" worlds, and the counterfactual clause "ψ holds at every
  maximally φ-consistent world" is then true **vacuously**, for any φ and ψ.
- **Nothing catches it.** `validateDclegModel` checks referential integrity
  and doxastic seriality only. It never checks Centering or Contemporary
  Universality, so an inadmissible F passes silently.

**Demonstration.** Take the two-world test model `dclegPropGame` (worlds
γL, γR; root v0; outcome nodes v1, v2), with `withMovePremises` applied:

| Formula | at decision node v0 | at outcome node v1 |
|---|---|---|
| ⊤ □→ ⊥ | false | **true** |

Centering requires that when φ holds at the actual world, φ □→ ψ reduces
to ψ there. Here φ = ⊤ holds, so ⊤ □→ ⊥ should be false everywhere. At
outcome nodes the code says true.

**Why it matters:**
- Consequences of Centering fail at outcome nodes, e.g. counterfactual
  modus ponens: φ ∧ (φ □→ ψ) → ψ.
- The backward-induction results (Ch. 4–5) are anchored at outcome nodes
  (R⁰ = end, the payoff atoms kᵢ). Any executable check of them there
  would get wrong truth values.
- The planned check of the thesis's validities on generated models would
  report **spurious counterexamples**, e.g. to ¬(⊤ □→ ⊥), and could also
  **hide real ones**.
- **The formal proofs are not affected.** In `DclegProofs/Semantics.lean`,
  F is a field of the model, and Centering is a condition every model must
  meet, so every theorem there already holds for *every* admissible F. The
  defect concerns only the executable model checker in `Gamen/Dcleg.lean`.

## Proposed fix

### 1. Admissible by default

The code needs *some* concrete F so that a model can be evaluated without
the user writing one. The simplest admissible choice at an outcome node w,
for each γ reaching it, is two nested premises:

  **F(γ, w) = { {(γ, w)},  {(β, w) | w ∈ V_β} }**

- **Centering:** the intersection is {(γ, w)}.
- **Contemporary Universality:** the outer premise contains every world
  that reaches w.
- **Meaning:** "the actual world, inside all worlds that reach this
  outcome."
  - If φ holds at γ, φ □→ ψ reduces to ψ at γ.
  - Otherwise, φ □→ ψ looks at the other worlds reaching the same outcome
    where φ holds.
  - If none do, it is vacuously true. That's the legitimate vacuous case,
    an antecedent impossible at this node.

This is **one arbitrary admissible choice**, as Jeremiah suggested. The
thesis doesn't prefer it over any other. Other admissible systems (finer
nested spheres, or ones inherited from the parent node's move premises)
would give some counterfactuals different truth values, and that's
correct: counterfactual truth at a point depends on F. The default should
say so in its docstring.

### 2. Reject inadmissible F

Extend `validateDclegModel` to check Centering and Contemporary
Universality at every reached pair (γ, w) with w ∈ V_γ, including outcome
nodes. Then an F that a user supplies, or a future construction produces,
can't silently violate the thesis. The current `withMovePremises` would
fail this check at outcome nodes, which is what the fix addresses.

### 3. Don't trust one default when testing validities

Since validity ranges over all admissible F, anything that checks a
claimed validity on concrete models should **generate random admissible
premise systems**, not rely on the default alone. This applies to stage 3
of `plans/dcleg-thesis-verification-2026-09-29.md` and to property tests.
Every generated F must pass the check in step 2. A formula that fails for
some admissible F is not valid, even if it holds under the default.

### Tests to add

- Centering and Contemporary Universality hold at every reached pair,
  outcome nodes included, for every test model under the default.
- ⊤ □→ ⊥ is false at every reached pair; counterfactual modus ponens holds
  at outcome nodes.
- The validator rejects a model whose F is empty at an outcome node, and
  one that violates Centering at a decision node.
- Planted checks: reverting each part of the fix must fail a test.

### Effect on existing tests

At least one expected result in the tests ported from gamen-hs will change,
because it currently relies on vacuous counterfactuals at an outcome node.
Under gamen-lean's policy (it is now the primary implementation), such tests
are updated and marked as deliberate divergences from gamen-hs, with the
reason. Dcleg isn't part of `gamen-validate`, so no downstream protocol
output changes.

## Questions for Jeremiah

1. Do the examples or arguments in Chapters 4–5 assume a *particular* F
   at outcome nodes, or is every admissible F intended? If a particular one,
   which?
2. Is there a reason to prefer a specific default: the two-premise system
   above, or something finer, e.g. derived from the path into the outcome
   node?
3. Confirm the domain of Centering: "∀γ ∀w ∈ V_γ" (only reached pairs), as
   the definition of I implies (Q7 in the formalization).
