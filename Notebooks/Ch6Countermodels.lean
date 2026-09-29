import Gamen.Teaching
import Widgets.Countermodel
import Widgets.Hint

/-!
# Chapter 6: Countermodels from tableaux

*Lean-only notebook (Gamen.jl has no Pluto counterpart), following §6.9
"Countermodels from Tableaux" of [Boxes and Diamonds](https://bd.openlogicproject.org)
(B&D, Fall 2025 edition, pp. 110–113).*

**How to use this file.** Put your cursor on an `#eval` or `#html` line to see
its result in the panel on the right. Change anything and every result below
updates. Exercises tell you what to edit.

**Learning outcomes.** After this notebook you will be able to:

1. say what an open, complete tableau branch tells you about a formula;
2. read a Kripke countermodel off an open branch, as B&D does in
   Example 6.22;
3. check a countermodel yourself, by changing its valuation and watching
   the formula's truth value change.

## A tableau that stays open

A prefixed tableau for A starts from the assumption 1 F A ("A is false at
world 1") and applies the rules until every branch closes or no rule adds
anything new. If every branch closes, A is valid (B&D Theorem 6.6). If a
branch stays open and complete, the proof of the completeness theorem
(Theorem 6.19) does more than tell you A is not valid: it *builds a model*
in which A is false. For K this is a decision procedure (B&D §6.9, p. 110).

The recipe, from the open branch:

- **W**: the prefixes on the branch (1, 1.1, 1.2, …);
- **R**: each prefix σ sees its children σ.n;
- **V(p)**: the prefixes σ with σ T p on the branch.

`countermodelView sys premises conclusion` runs the tableau and reads the
model off the first open branch. It shows a model only after checking that
it really satisfies every line of the branch; otherwise it says "unknown".

## Example 6.22

B&D shows that □(p ∨ q) → (□p ∨ □q) is not valid in K. The □F rule creates
world 1.1 (where p is false) and world 1.2 (where q is false); □(p ∨ q) then
forces p ∨ q at both, and the only open branch makes q true at 1.1 and p
true at 1.2.
-/
open Gamen Gamen.Widgets ProofWidgets

def example622 : Formula := ml[ □(p ∨ q) → □p ∨ □q ]

#eval (countermodelView systemK [] example622).summary

/-!
Compare with B&D (pp. 112–113): W = {1, 1.1, 1.2}, R = {⟨1, 1.1⟩, ⟨1, 1.2⟩},
V(p) = {1.2} and V(q) = {1.1} (Figure 6.1).

Now look at it. The checks under the diagram are evaluated at world 1:
the conclusion is false there (✗), which is what makes this a countermodel.
-/

#html countermodelHtml systemK [] example622

/-!
**A countermodel is a witness, not magic.** In the panel, click the fact
`q`, then click world 1.2. Now q holds at both 1.1 and 1.2, so □q is true
at 1, and the conclusion's check turns to ✓: this model is no longer a
countermodel. Click 1.2 again to undo.

**Statements Lean checks.** The `example` lines assert answers, and Lean
rejects the file if one is false.
-/

example : (countermodelView systemK [] example622).isValid = false := by native_decide
example : (countermodelView systemK [] ml[ □(p → q) → (□p → □q) ]).isValid = true := by
  native_decide

/-!
## Exercises

For each formula, predict whether it is valid in the given system. Replace
`none` with `some true` (valid) or `some false` (not valid), then look at the
`#html` line below the predictions.

1. □p → □□p in K.
2. □p → □□p in S4, where the accessibility relation is reflexive and
   transitive.
3. (□p ∨ □q) → □(p ∨ q) in K (B&D Problem 6.1, item 2).
-/

def exercise1 : Formula := ml[ □p → □□p ]
def exercise3 : Formula := ml[ □p ∨ □q → □(p ∨ q) ]

def predict1 : Option Bool := none
def predict2 : Option Bool := none
def predict3 : Option Bool := none

#eval [grade predict1 (countermodelView systemK [] exercise1).isValid,
       grade predict2 (countermodelView systemS4 [] exercise1).isValid,
       grade predict3 (countermodelView systemK [] exercise3).isValid]

#html countermodelHtml systemK [] exercise1
#html countermodelHtml systemS4 [] exercise1
#html countermodelHtml systemK [] exercise3

#html hints [
  ("Explain 1", "Not valid in K. The countermodel is a chain 1 → 1.1 → 1.1.1 with p \
     true only at 1.1: □p holds at 1, but □□p fails, because p fails at 1.1.1, two \
     steps away. Nothing in K makes R transitive."),
  ("Explain 2", "Valid in S4. With a transitive relation, every world two steps from \
     1 is also one step from 1, so if p holds at every world 1 sees, □p holds at \
     every world 1 sees too. The S4 tableau closes."),
  ("Explain 3", "Valid in K. Suppose □p holds at 1 (the case □q is the same): then p \
     holds at every accessible world, so p ∨ q does too. Every branch of the tableau \
     closes.") ]

example : (countermodelView systemK [] exercise1).isValid = false := by native_decide
example : (countermodelView systemS4 [] exercise1).isValid = true := by native_decide
example : (countermodelView systemK [] exercise3).isValid = true := by native_decide
