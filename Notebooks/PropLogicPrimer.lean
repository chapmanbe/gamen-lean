import Gamen.Teaching
import Widgets.TruthTable
import Widgets.Hint

/-!
# A primer on propositional logic, with clinical rules

*The first of two notebooks on logic for health informatics. No logic
background is assumed. The second notebook, `ThreeValued.lean`, asks what
happens when a fact is missing from the record. This one follows Appendix C
of [Boxes and Diamonds](https://bd.openlogicproject.org) (B&D, Fall 2025
edition), "Syntax and Semantics".*

**How to use this file.** Put your cursor on a line that starts with
`#eval` or `#html`, and its result appears in the panel on the right (the
"infoview"). Change anything, and every result below it updates. Exercises
tell you what to edit: usually you replace a `none` with an answer, and
the line below it tells you whether you are right.

**Learning outcomes.** After this notebook you will be able to:

1. write a clinical rule as a formula, with atoms and the connectives
   ¬, ∧, ∨, →;
2. read and fill in a truth table;
3. decide whether a patient's record complies with a rule;
4. tell a tautology from a contingent or unsatisfiable formula;
5. check whether a conclusion follows from premises, and find a
   counterexample when it doesn't.

## Why bother with logic?

Here is a screening rule of the kind found in clinical guidelines:

> If a patient is 65 or older and has diabetes, offer screening.

Some questions about it sound easy but trip people up:

- A 40-year-old with diabetes was not offered screening. Was the rule broken?
- A patient was offered screening. Does that tell you they are 65 or older?
- A patient is under 65. Does the rule say *not* to offer screening?

You will be able to answer all three by the end of the notebook, and to
check your answers with a computer. That is the point of logic here: it
makes "does this follow?" a question with a checkable answer, instead of a
matter of how the sentence sounds.

## Atoms

An **atom** (B&D calls it a *propositional variable*, Definition C.1) is
a statement that is either true or false for a given patient. We give each
one a short name:

| atom | meaning |
|---|---|
| `age65` | the patient is 65 or older |
| `diabetic` | the patient has diabetes |
| `offer` | the patient is offered screening |

An atom has no inner structure as far as logic is concerned: logic doesn't
know what "diabetes" means, only that `diabetic` is true or false.

## Connectives

Formulas are built from atoms with **connectives** (B&D Definition C.1):

| symbol | read as | type it as |
|---|---|---|
| ¬A | not A | `\not` |
| A ∧ B | A and B | `\and` |
| A ∨ B | A or B (or both) | `\or` |
| A → B | if A then B | `\to` |

In this file you write formulas between `ml[` and `]`. The screening rule
becomes:
-/

namespace Primer   -- keeps this notebook's names apart from other notebooks'

open Gamen Gamen.ManyValued Gamen.Widgets

def rule : Formula := ml[ (age65 ∧ diabetic) → offer ]

#eval rule

/-!
The parentheses say that `age65 ∧ diabetic` together is the "if" part.
Formulas can be as long as you like: every atom is a formula, and if A and
B are formulas, so are ¬A, (A ∧ B), (A ∨ B) and (A → B). B&D also uses ⊥
("falsum", a formula that is always false), and defines A ↔ B ("A if and
only if B") as (A → B) ∧ (B → A) (Definition C.2). We won't need either.

## Truth tables

Each connective is defined by a **truth table**. It lists every way its
parts can be true (T) or false (F), and gives the value of the whole in
each case. Here are the tables for ¬ and ∧:
-/

#html truthTableHtml classical [ml[ ¬p ]]
#html truthTableHtml classical [ml[ p ∧ q ]]

/-!
(Ignore "designated" in the note under each table for now; it matters in
the second notebook. In this notebook the designated value is just T.)

**¬** flips the value. **∧** is true only when both sides are true.

Now ∨ and →:
-/

#html truthTableHtml classical [ml[ p ∨ q ], ml[ p → q ]]

/-!
**∨** is *inclusive*: `p ∨ q` is true when either side is true, including
when both are. ("Diabetic or hypertensive" includes patients who are both.)

**→** is false in exactly one row: `p` true and `q` false. That is the
only way to break a promise of the form "if p then q". In the other three
rows the promise is kept, including the two rows where `p` is false. We
come back to those rows below, because they surprise most people.

A formula with more atoms has more rows: each atom doubles the number, so
three atoms give 2 × 2 × 2 = 8 rows. The rows are always listed in the same
order: the first atom changes slowest, T before F. Here is the screening
rule, built up in two steps:
-/

#html truthTableHtml classical [ml[ age65 ∧ diabetic ], rule]

/-!
### Practice: fill in a column

Fill in the column for `p ∧ ¬q`, top row first. The rows are in the order
above: (p, q) = (T, T), (T, F), (F, T), (F, F). Write `some true` for T and
`some false` for F. (Tip: work out the ¬q column in your head first.)
-/

def column1 : List (Option Bool) := [none, none, none, none]

#eval gradeColumn classical ml[ p ∧ ¬q ] column1

/-!
Now fill in the column for `¬p ∨ q`:
-/

def column2 : List (Option Bool) := [none, none, none, none]

#eval gradeColumn classical ml[ ¬p ∨ q ] column2

#html hint "Compare your answer to column2 with the table for p → q"
  "They are the same column: ¬p ∨ q and p → q have the same value in every row. \
  \"If p then q\" says the same thing as \"not p, or q\"."

/-!
## Patients are valuations

A truth table lists every possible combination of values. A single patient
is *one* row. In B&D's terms a patient's record is a **valuation**
(Definition C.14): it gives each atom the value T or F.

We build one with `record`. The first argument says what an atom the list
doesn't mention should be; `false` means "not recorded, so false". Here we
list every atom anyway.
-/

def ana := record false [("age65", true),  ("diabetic", true),  ("offer", true)]
def ben := record false [("age65", true),  ("diabetic", true),  ("offer", false)]
def cy  := record false [("age65", false), ("diabetic", true),  ("offer", false)]
def dee := record false [("age65", false), ("diabetic", false), ("offer", true)]

/-!
The value of a whole formula for a patient is worked out from the inside
out, one connective at a time, using the tables (B&D Definition C.15).
For Ana, `age65 ∧ diabetic` is T ∧ T = T, and then T → T = T:
-/

#eval truthValue classical ana rule

/-!
When the rule is true for a patient, we say the record **complies** with
the rule; when it is false, the record **violates** it.

### Practice: which records comply?

Predict whether each record complies with the rule (`some true`) or
violates it (`some false`). Work it out with the table before you check.
-/

def complies1 : Option Bool := none   -- Ben: 65+, diabetic, not offered
def complies2 : Option Bool := none   -- Cy: under 65, diabetic, not offered
def complies3 : Option Bool := none   -- Dee: under 65, not diabetic, offered

#eval [gradeValue 1 complies1 (eval classical ben rule)
        "Ben is 65+ and diabetic, so the \"if\" part is true. Was he offered screening?",
       gradeValue 2 complies2 (eval classical cy rule)
        "Cy is under 65, so the \"if\" part age65 ∧ diabetic is false. \
        Look at the → table's rows where the left side is F.",
       gradeValue 3 complies3 (eval classical dee rule)
        "Dee's \"if\" part is false. Does the rule forbid offering screening?"]

/-!
### The surprises of →

Cy's and Dee's answers are worth a second look.

- **Cy** complies. The rule only talks about patients who are 65 or older
  *and* diabetic; about everyone else it says nothing, so it can't be
  broken by them. This is called **vacuous truth**: a rule whose "if" part
  is false is true, because it makes no demand. It is the answer to the
  first question at the top of this notebook.
- **Dee** complies too, even though she was offered screening without
  meeting the criteria. The rule says when screening *must* be offered, not
  when it *may*. It is not a rule that screening is offered *only* to
  diabetics over 65. That rule would be `offer → (age65 ∧ diabetic)`, a
  different formula: the arrow points the other way.

The → of logic is called the **material conditional**. It is the everyday
"if" with everything but the truth values stripped away: no causation, no
timing, no "and otherwise don't". That is exactly what makes it checkable,
and exactly why it surprises people.

## Tautologies, contingent and unsatisfiable formulas

Some formulas are true for every patient, whatever the record says. B&D
Definition C.19 sorts formulas into three kinds:

- a **tautology** is true in every row of its truth table;
- an **unsatisfiable** formula is false in every row;
- a **contingent** formula is true in some rows and false in others
  (B&D: "satisfiable but not a tautology").

"The patient has diabetes or doesn't" is a tautology, and "the patient has
diabetes and doesn't" is unsatisfiable:
-/

#html truthTableHtml classical [ml[ diabetic ∨ ¬diabetic ], ml[ diabetic ∧ ¬diabetic ]]

#eval classify classical ml[ diabetic ∨ ¬diabetic ]
#eval classify classical ml[ diabetic ∧ ¬diabetic ]

/-!
Remember `diabetic ∨ ¬diabetic`. It looks too obvious to be worth saying,
but the second notebook shows that it stops being true once a record can
leave `diabetic` unknown.

### Practice: classify

Write `some "tautology"`, `some "contingent"` or `some "unsatisfiable"`.
Use the `#html` line to draw a table if you need one.
-/

def kind1 : Option String := none   -- the screening rule
def kind2 : Option String := none   -- (p → q) ∨ (q → p)
def kind3 : Option String := none   -- ¬(p → p)
def kind4 : Option String := none   -- p → (q → p)

#eval [gradeClassify 1 classical rule kind1
        "Ben's row makes the rule false, and Ana's makes it true.",
       gradeClassify 2 classical ml[ (p → q) ∨ (q → p) ] kind2
        "Draw the table. For (p → q) ∨ (q → p) to be false, both sides must be false.",
       gradeClassify 3 classical ml[ ¬(p → p) ] kind3
        "What is p → p when p is T? When p is F?",
       gradeClassify 4 classical ml[ p → (q → p) ] kind4
        "The only way to make it false is p true and q → p false. Can q → p be false when p is true?"]

#html truthTableHtml classical [ml[ (p → q) ∨ (q → p) ]]

/-!
Number 2 is another surprise of the material conditional: of any two
statements, one "implies" the other. Pick any two facts about a patient,
say "has a fever" and "is left-handed", and `(fever → lefthanded) ∨
(lefthanded → fever)` is true. The formula is about truth values only, not
about any connection between the two facts.

### Practice: find a tautology

Find a tautology other than `diabetic ∨ ¬diabetic` whose only atom is
`diabetic`.
-/

def myTautology : Option Formula := none

#eval gradeFind 1 myTautology
  (fun f => classify classical f == "tautology" && atomList f == [⟨"diabetic"⟩]
    && f != ml[ diabetic ∨ ¬diabetic ])
  "is a tautology, other than diabetic ∨ ¬diabetic, with diabetic as its only atom"

#html hint "Stuck?"
  "Try ml[ diabetic → diabetic ]: \"if the patient is diabetic, the patient is diabetic\". \
  It is false only if the left side is T and the right side is F, which can't happen."

/-!
## Entailment: what follows from what

Now the main event. A set of premises Γ **entails** a conclusion A,
written Γ ⊨ A, if A is true in every row where all the premises are true
(B&D Definition C.19(4)). To check it, look *only* at the rows where every
premise is true, and see whether the conclusion is true there too. A row
where the premises are all true and the conclusion is false is a
**counterexample**: one is enough to show that A does not follow.

The table below does this for us. Its last column marks the rows where all
the premises are true: ✓ if the conclusion is true as well, ✗ (and red) if
the row is a counterexample.

**Modus ponens.** From the rule, and the facts that a patient is 65 or
older and diabetic, it follows that the patient is offered screening:
-/

#html entailmentHtml classical [rule, ml[ age65 ], ml[ diabetic ]] ml[ offer ]

/-!
Only one row has all three premises true, and `offer` is true in it.

**Affirming the consequent.** A patient was offered screening. Does the
rule let us conclude they are 65 or older and diabetic? That is the second
question from the top.
-/

#html entailmentHtml classical [rule, ml[ offer ]] ml[ age65 ∧ diabetic ]

/-!
No: the red rows are patients like Dee, who were offered screening without
meeting the criteria. They comply with the rule, so the rule can't rule
them out.

### Practice: does it follow?

Predict whether each entailment holds (`some true`) or not (`some false`),
then draw its table with `entailmentHtml` to see why.

1. The rule and `¬age65` entail `¬offer`. (Under 65, so no screening?)
2. The rule and `¬offer` entail `¬(age65 ∧ diabetic)`. (Not offered, so not
   a 65+ diabetic?)
3. The rule and `¬diabetic` entail `¬offer`.
4. `diabetic` and `¬diabetic` entail `offer`.
-/

def follows1 : Option Bool := none
def follows2 : Option Bool := none
def follows3 : Option Bool := none
def follows4 : Option Bool := none

#eval [gradeYesNo 1 follows1 (entails classical [rule, ml[ ¬age65 ]] ml[ ¬offer ])
        "Think of Dee: under 65, and offered screening. Does she comply with the rule?",
       gradeYesNo 2 follows2 (entails classical [rule, ml[ ¬offer ]] ml[ ¬(age65 ∧ diabetic) ])
        "Suppose the patient were a 65+ diabetic. Then the rule says offer. But offer is false.",
       gradeYesNo 3 follows3 (entails classical [rule, ml[ ¬diabetic ]] ml[ ¬offer ])
        "The rule says nothing about patients without diabetes.",
       gradeYesNo 4 follows4 (entails classical [ml[ diabetic ], ml[ ¬diabetic ]] ml[ offer ])
        "Look for a row where both premises are true. Is there one?"]

#html entailmentHtml classical [rule, ml[ ¬age65 ]] ml[ ¬offer ]
#html entailmentHtml classical [ml[ diabetic ], ml[ ¬diabetic ]] ml[ offer ]

/-!
Number 1 has a name, **denying the antecedent**, and it is the third
question from the top: the rule does not say to withhold screening from
anyone. Number 2 is **modus tollens**, and it is valid.

Number 4 deserves a comment. No row makes both `diabetic` and `¬diabetic`
true, so there is no row to be a counterexample, and the entailment holds.
Contradictory premises entail *anything*. Logicians call this
**explosion** (*ex falso quodlibet*). In a record system it means a
contradiction in the data can "prove" whatever you like, so it is worth
catching early. B&D Proposition C.21 turns this around into a test: Γ ⊨ A
exactly when Γ together with ¬A is unsatisfiable. Tools that check clinical
guidelines for conflicts use that test, asking whether a set of rules and
facts can all be true at once.

## Summary

- A formula is built from atoms with ¬, ∧, ∨, →. Truth tables define the
  connectives.
- A patient's record is a valuation, one row of the table. A record
  complies with a rule when the rule is true in that row.
- → is false only when the left side is true and the right side false.
  Rules are vacuously true for patients they don't apply to, and "if A then
  B" is not "if B then A".
- Tautology: true in every row. Unsatisfiable: in none. Contingent: in some.
- Γ ⊨ A when every row that makes all of Γ true makes A true. One
  counterexample row refutes it.

Everything here assumed that every atom is either true or false for every
patient. Real records are incomplete: a lab test that was never ordered is
neither "high" nor "not high" in the record. The next notebook,
`ThreeValued.lean`, adds a third value for "unknown", the one clinical
query languages use, and shows which of the facts above survive.
-/

end Primer
