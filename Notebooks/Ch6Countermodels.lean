import Gamen.Teaching
import Widgets.Countermodel
import Widgets.Hint

/-!
# Chapter 6: Countermodels from tableaux

*Follows §6.9 "Countermodels from Tableaux" of
[Boxes and Diamonds](https://bd.openlogicproject.org) (B&D, Fall 2025
edition, pp. 110–113).*

## How to use this file

Open it in VS Code with the Lean 4 extension (or in the course's Lean web
editor). Results appear in the **infoview**, the panel on the right: put
your cursor on an `#eval` or `#html` line to see what it shows there. When
you change anything, every result below the change updates.

- Formulas go between `ml[` and `]`, in the book's notation. Type `\box`
  for □, `\diamond` for ◇, `\not` for ¬, `\and` for ∧, `\or` for ∨, `\to`
  for →. As in the book, ∨ and ∧ bind tighter than →, so `□p ∨ □q → r`
  means `(□p ∨ □q) → r`. This file writes the parentheses anyway.
- `def name : Formula := ml[ … ]` gives a formula a name.
- `#eval` and `#html` show a result in the infoview.
- `example : … := by native_decide` states a fact. Ignore the
  `by native_decide` part: it tells Lean to check the fact by computing
  it, and Lean rejects the file if the fact is false.

**Learning outcomes.** After this notebook you will be able to:

1. read a prefixed tableau branch, line by line;
2. say what an open, complete branch tells you about a formula;
3. read a Kripke countermodel off an open branch, as B&D does in
   Example 6.22;
4. check a countermodel yourself, by changing it and watching the
   formula's truth value change.

## Tableaux in four sentences

A tableau tries to build a model in which the formula is false, one
*signed formula* at a time. `σ T A` says "A is true at world σ" and `σ F A`
says "A is false at world σ"; the *prefix* σ names a world, and σ.n names a
world that σ can see (B&D §6.1, pp. 93–94). The rules (B&D Tables 6.1 and
6.2, pp. 95–96) break formulas into smaller ones, and some rules split the
list into two *branches*, one per way the formula could be true or false. A
branch is *closed* when it contains both σ T A and σ F A, a contradiction
(B&D §6.2, p. 94); it is *open* otherwise, and *complete* when every rule
that applies has been applied (B&D Definition 6.17, pp. 107–108).

To test whether A is valid, the tableau starts from the assumption
`1 F A`. If every branch closes, no model makes A false, so A is valid
(B&D Theorem 6.6). If a branch stays open and complete, the proof of
completeness (Theorem 6.19) turns it into a model in which A is false. For
K this is a decision procedure (B&D §6.9, p. 110).

## Example 6.22: the branch

B&D shows that □(p ∨ q) → (□p ∨ □q) is not valid in K. Here is the open
branch the tableau finds, computed, not typed in. Each line says which rule
produced it from which earlier line; "assumption" marks the starting
point. It is a single branch: where a rule splits (the ∨T lines 10 and 11),
only the side that stays open is printed. The side that closes belongs to
another branch and is not shown; the note on the split line names it.
-/
open Gamen Gamen.Widgets ProofWidgets

def example622 : Formula := ml[ □(p ∨ q) → (□p ∨ □q) ]

#html openBranchHtml systemK [] example622

/-!
Read it from the top. The →F rule turns line 1 into lines 2 and 3; ∨F
splits line 3 into 4 and 5. □F makes a new world for each false box: 1.1,
where p is false (line 6), and 1.2, where q is false (line 8). □T copies
p ∨ q into every world that 1 sees (lines 7 and 9).

Lines 10 and 11 are splits. At 1.1, p ∨ q can be true because p is or
because q is. The p side contradicts line 6 (1.1 F p), so that branch
closes; the q side stays open. At 1.2 the q side closes against line 8, and
the p side stays open. Only the open sides, 1.1 T q and 1.2 T p, appear in
the printout; the closed sides 1.1 T p and 1.2 T q are named only in the
notes. Nothing else applies, so this branch is open and complete.

## Example 6.22: the model

Read the model off the open branch (the proof of B&D Theorem 6.19, p. 109):

- **W**, the worlds: the prefixes on the branch;
- **R**, which world sees which: each σ sees its children σ.n;
- **V(p)**, where p is true: the prefixes σ with σ T p on the branch.

`countermodelView system premises conclusion` runs the tableau and reads
the model off the open branch. The *premises* are formulas you assume true
at world 1; the list `[]` means there are none, so the question is simply
whether the conclusion is valid. The model is shown only after Lean checks
that it satisfies every line of the branch.
-/

#eval (countermodelView systemK [] example622).summary

/-!
`.summary` is the verdict as one line of text (`#eval countermodelView …`
without it shows the same line). The branch and the diagram need `#html`.
"Open branch 1" means the first open branch in the order the tableau lists
them; here there is only one.

Compare with B&D (pp. 112–113): W = {1, 1.1, 1.2},
R = {⟨1, 1.1⟩, ⟨1, 1.2⟩}, V(p) = {1.2} and V(q) = {1.1} (Figure 6.1).

There are three possible verdicts: *valid*, a *countermodel*, or
*unknown*, when the tableau runs out of steps before it finishes. Here is an
unknown, from giving the tableau only 3 steps:
-/

#eval (countermodelView systemK [] example622 (maxSteps := 3)).summary

/-!
## Example 6.22: explore the model

`countermodelHtml` draws the countermodel. The panel has four parts:

- **the diagram**: each circle is a world, labeled by its prefix, with
  arrows for R;
- **the facts** listed under each world: the atoms true there, or
  "(nothing)";
- **the row of fact buttons** below the diagram, one per atom: click one to
  select it, then click a world to switch that fact on or off there;
- **the checks** at the bottom, evaluated at world 1: ✗ means false there,
  ✓ means true. For a countermodel the conclusion's check is ✗.

For a valid formula there is no model to draw, and you get one sentence
saying so. For an unknown verdict, you get the reason.
-/

#html countermodelHtml systemK [] example622

/-!
**A countermodel is a witness, not magic.** In the panel, click the fact
`q` (in the row of fact buttons), then click world 1.2. Now q holds at both
1.1 and 1.2, so □q is true at 1, and the conclusion's check turns to ✓:
this model is no longer a countermodel. Click 1.2 again to undo.

## Other systems

The functions take a system: `systemK`, `systemKT`, `systemKD`,
`systemKB` (B&D's KTB), `systemK4`, `systemS4` and `systemS5`. Each adds
rules to K's for its frame condition (B&D Table 6.4, p. 104). S4, for
reflexive and transitive frames, adds T□ and T◇ (what is necessary at σ is
true at σ) and 4□ and 4◇ (a □ formula true at σ is also true at every
world σ sees; B&D Table 6.3, p. 103). Its countermodels draw every arrow of
the reflexive, transitive relation, including the loops.

## Exercises

For each formula, predict whether it is valid in the given system. Replace
`none` with `some true` (valid) or `some false` (not valid), and read the
numbered feedback. Then look at the `#html` lines below it.

1. □p → □□p in K.
2. □p → □□p in S4.
3. (□p ∨ □q) → □(p ∨ q) in K (B&D Problem 6.1, item 2).
-/

def exercise1 : Formula := ml[ □p → □□p ]
/-- The same formula as exercise 1; exercise 2 asks about it in S4. -/
def exercise2 : Formula := exercise1
def exercise3 : Formula := ml[ (□p ∨ □q) → □(p ∨ q) ]

def predict1 : Option Bool := none
def predict2 : Option Bool := none
def predict3 : Option Bool := none

#eval [
  gradeValidity 1 predict1 (countermodelView systemK [] exercise1)
    "In K, nothing makes R transitive: a world two steps from 1 need not be one \
     step from 1.",
  gradeValidity 2 predict2 (countermodelView systemS4 [] exercise2)
    "S4's frames are transitive: every world two steps from 1 is also one step \
     from 1.",
  gradeValidity 3 predict3 (countermodelView systemK [] exercise3)
    "Suppose □p is true at 1. What does that say about p ∨ q at the worlds 1 \
     sees?"]

#html countermodelHtml systemK [] exercise1
#html countermodelHtml systemS4 [] exercise2
#html countermodelHtml systemK [] exercise3

#html hints [
  ("Explain 1", "Not valid in K. The countermodel is a chain 1 → 1.1 → 1.1.1 with p \
     true only at 1.1: □p holds at 1, but □□p fails, because p fails at 1.1.1, two \
     steps away."),
  ("Explain 2", "Valid in S4. The 4□ rule copies □p from 1 to every world 1 sees, \
     so the world two steps away must have p, and every branch closes."),
  ("Explain 3", "Valid in K. If □p holds at 1 (the case □q is the same), p holds at \
     every world 1 sees, so p ∨ q does too. Every branch of the tableau closes.") ]

/-!
## Solutions (checked by Lean)

Read these after you have tried the exercises. Each line states an answer,
and Lean rejects the file if it is wrong.
-/

example : (countermodelView systemK [] example622).isCountermodel = true := by native_decide
-- Not an exercise: the K axiom, for comparison. It is valid.
example : (countermodelView systemK [] ml[ □(p → q) → (□p → □q) ]).isValid = true := by
  native_decide
example : (countermodelView systemK [] exercise1).isCountermodel = true := by native_decide
example : (countermodelView systemS4 [] exercise2).isValid = true := by native_decide
example : (countermodelView systemK [] exercise3).isValid = true := by native_decide
