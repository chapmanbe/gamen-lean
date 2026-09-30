import Gamen.Teaching
import Widgets.TruthTable
import Widgets.Hint

/-!
# Three-valued logic and missing data

*The second of two notebooks on logic for health informatics. Start with
`PropLogicPrimer.lean` if truth tables, tautologies and entailment (⊨) are
new to you. The logics here follow the Open Logic Text's chapter on
three-valued logics (<https://openlogicproject.org>), and the CQL and
FHIRPath facts are quoted from the HL7 specifications, checked 2026-09-30.*

**How to use this file.** As before: put your cursor on an `#eval` or
`#html` line to see its result in the infoview, and replace each `none` in
an exercise with your answer.

**Learning outcomes.** After this notebook you will be able to:

1. evaluate a formula when some facts are unknown, using the strong Kleene
   tables;
2. explain why "the patient has diabetes or doesn't" is not guaranteed true
   when diabetes status is missing;
3. compare four three-valued logics and say what each one's "unknown" means;
4. predict what a CQL or FHIRPath expression returns when data is missing,
   and what a query does with that result.

## A patient with a missing lab

A quality measure looks for diabetic patients whose diabetes is poorly
controlled:

> The patient has diabetes, and their most recent HbA1c is above 9%.

With two atoms, `diabetic` and `hba1c_high` ("the most recent HbA1c is
above 9%"), the criterion is:
-/

namespace ThreeValued   -- keeps this notebook's names apart from other notebooks'

open Gamen Gamen.ManyValued Gamen.Widgets

def poorControl : Formula := ml[ diabetic ∧ hba1c_high ]

/-!
Bea has diabetes, but no HbA1c on file. In the primer, `record false`
filled in every unmentioned atom as false. For Bea that gives:
-/

def beaClosedWorld := record false [("diabetic", true)]

#eval truthValue classical beaClosedWorld poorControl

/-!
F: "Bea's diabetes is not poorly controlled." But nothing in her record
says that. Her HbA1c might be 12%; nobody has measured it. Treating "not
recorded" as "false" is called the **closed-world assumption**. It is right
for some facts (a pharmacy's list of dispensed drugs is complete) and wrong
for most clinical ones.

The alternative is a third truth value. We write the three values t, u and
f, as the Open Logic Text does: t for true, f for false, and u for
**unknown**. You type them in Lean as `.t`, `.u` and `.f`. Now `record .u`
fills in every unmentioned atom as unknown:
-/

def bea : Atom → TV3 := record .u [("diabetic", .t)]                      -- no HbA1c on file
def cal : Atom → TV3 := record .u [("diabetic", .f)]                      -- no diabetes, no HbA1c
def dot : Atom → TV3 := record .u []                                      -- nothing recorded
def eve : Atom → TV3 := record .u [("diabetic", .t), ("hba1c_high", .f)]  -- HbA1c 7%

/-!
## Strong Kleene logic

To evaluate `t ∧ u` we need tables with a row for u. Here is a way to find
them. Read u as "t or f, we don't know which". For each connective, ask:
*would the answer be the same whichever it turns out to be?* If so, that is
the answer; if not, the answer is u.

- `t ∧ u`: if the unknown is t, we get t; if f, we get f. It depends, so
  `t ∧ u = u`.
- `f ∧ u`: one side is already false, so the whole is false either way:
  `f ∧ u = f`.
- `t ∨ u = t`, for the same reason: one side is already true.

These are the tables of **strong Kleene logic**, called K3 (after Stephen
Kleene). Designated values are the ones that count as true when we ask
whether a formula is a tautology, or whether it follows from premises. In
K3 only t is designated.
-/

#html truthTableHtml strongKleene [ml[ ¬p ]]
#html truthTableHtml strongKleene [ml[ p ∧ q ], ml[ p ∨ q ], ml[ p → q ]]

/-!
With three values and two atoms there are 3 × 3 = 9 rows, in the order t,
u, f. Now Bea's criterion is unknown, which is the honest answer:
-/

#eval truthValue strongKleene bea poorControl

/-!
### Practice: predict the value

Write `some .t`, `some .u` or `some .f`.

1. `poorControl` for Cal (not diabetic, no HbA1c).
2. `diabetic ∨ hba1c_high` for Bea.
3. `hba1c_high → diabetic` for Cal.
4. `poorControl` for Eve (diabetic, HbA1c 7%).
-/

def value1 : Option TV3 := none
def value2 : Option TV3 := none
def value3 : Option TV3 := none
def value4 : Option TV3 := none

#eval [gradeValue 1 value1 (eval strongKleene cal poorControl)
        "Cal's diabetic is f. What is f ∧ (anything)?",
       gradeValue 2 value2 (eval strongKleene bea ml[ diabetic ∨ hba1c_high ])
        "Bea's diabetic is t. What is t ∨ (anything)?",
       gradeValue 3 value3 (eval strongKleene cal ml[ hba1c_high → diabetic ])
        "That is u → f. Would the answer be the same if the u were t? If it were f?",
       gradeValue 4 value4 (eval strongKleene eve poorControl)
        "Nothing about Eve is unknown. What is t ∧ f?"]

/-!
Number 1 is the good news of three-valued logic: Cal's result is a
definite f even though his HbA1c is missing, because it can't matter.
Number 4 is a reminder that nothing changes when nothing is missing.

In fact, K3 agrees with classical logic on every formula whenever no atom
is u. Look at the tables: the rows without a u are exactly the classical
truth tables. That is a theorem, checked by Lean for *every* formula built
from ¬, ∧, ∨ and → (`ofBool` turns true and false into t and f):
-/

#check @strongKleene_agrees_classical

/-!
### Practice: fill in a column

In the primer, `¬p ∨ q` had the same column as `p → q`. Is that still so in
K3? Fill in the column for `¬p ∨ q`, nine rows, in the table's order:
(p, q) = (t, t), (t, u), (t, f), (u, t), (u, u), (u, f), (f, t), (f, u),
(f, f). Then compare it with the → column above.
-/

def column1 : List (Option TV3) := [none, none, none, none, none, none, none, none, none]

#eval gradeColumn strongKleene ml[ ¬p ∨ q ] column1

/-!
## The key result: no tautologies

Here is the tautology from the primer, "the patient has diabetes or
doesn't", in K3:
-/

#html truthTableHtml strongKleene [ml[ diabetic ∨ ¬diabetic ], ml[ diabetic → diabetic ]]

#eval classify strongKleene ml[ diabetic ∨ ¬diabetic ]
#eval truthValue strongKleene dot ml[ diabetic ∨ ¬diabetic ]

/-!
In the row where `diabetic` is u, `¬diabetic` is u too, and `u ∨ u = u`.
So for Dot, whose record says nothing, "has diabetes or doesn't" is
unknown. The same happens to "if diabetic, then diabetic".

This isn't an accident of these two formulas. **K3 has no tautologies at
all.** Give every atom the value u, and every formula comes out u, because
every K3 table sends u (and u, u) to u:
-/

#check @strongKleene_no_tautologies

/-!
The proof is a proof about *all* formulas, and it goes by **induction on
formulas** (B&D Theorem C.4): show the claim for atoms, then show that if
it holds for A and B, it holds for ¬A, A ∧ B, A ∨ B and A → B. Atoms are u
by assumption. If A and B are both u, then ¬A is `¬u = u`, A ∧ B is
`u ∧ u = u`, and so on, one table cell per connective. Lean checks that
proof (`eval_allU` in `Gamen/ManyValued.lean`), so the claim holds for
every formula, not only the ones we've tried.

Which raises an odd point about Dot. However her diabetes status turns out,
`diabetic ∨ ¬diabetic` will be true: t ∨ f = t, and f ∨ t = t. Every way of
filling in the unknown gives t, yet K3 says u. K3 works one connective at a
time, and by the time it reaches ∨ it has two u's and has forgotten that
they are the same unknown. So when K3 says t or f, you can trust it (that
answer holds however the unknowns turn out). When it says u, the true
answer may still be settled. (`Gamen.ManyValued.Completion` proves the
first half, and its `exactStatus` checks every way of filling in the
unknowns when you need the exact answer.)

### A trick question

Try to find a formula whose only atom is `diabetic` and which K3 makes t
for Dot, whose `diabetic` is u. Try two or three, then read the hint.
-/

def trick : Option Formula := none

#eval gradeFind 1 trick
  (fun f => atomList f == [⟨"diabetic"⟩] && eval strongKleene dot f == .ok .t)
  "is t for Dot in K3"

#html hint "Why none of your attempts worked"
  "There is no such formula. Dot's only atom is u, so by the theorem above every \
  formula built from ¬, ∧, ∨ and → is u for her. That is what \"no tautologies\" means."

/-!
## Three other logics

K3 is one answer to "what should u do?". Changing a table, or changing
which values are designated, gives other logics, each with its own reading
of u.

### Weak Kleene: u as an error

In **weak Kleene logic** (also called Bochvar's logic), u is infectious:
any u in, u out. Even `f ∧ u` is u.
-/

#html truthTableHtml weakKleene [ml[ p ∧ q ], ml[ p ∨ q ]]
#eval truthValue weakKleene cal poorControl

/-!
Cal's definite f is gone. This fits a u that means "the computation
failed" or "this question makes no sense here", like an error that
propagates through everything it touches, rather than "we haven't measured
it". Weak Kleene has no tautologies either (`weakKleene_no_tautologies`).

### Łukasiewicz: one cell changes

Jan Łukasiewicz's three-valued logic Ł3 has K3's tables for ¬, ∧ and ∨.
Only → is different, and only in one cell: `u → u = t`.
-/

#html truthTableHtml lukasiewicz3 [ml[ p → q ]]
#check @lukasiewicz3_agrees_strongKleene
#check @lukasiewicz3_impl_differs

/-!
Read u → u = t as: "if diabetic, then diabetic" is true even when we don't
know whether the patient is diabetic. That brings back `p → p` as a
tautology. `p ∨ ¬p` stays lost, because ∨ didn't change.

### LP: designating u

The **logic of paradox**, LP (Graham Priest), keeps K3's tables and
changes which values count as true: both t and u are designated. Read a
designated u as "not ruled out", the reading of a screening test, where
anything not known to be negative stays in.

Now `p ∨ ¬p` is designated in every row, since its only non-t value is u.
In fact, LP has exactly the same tautologies as classical logic (the Open
Logic Text proves it; this project checks it on random formulas). What LP
changes is entailment.

### Practice: which logic?

Predict: is each formula a tautology in the logic named? `some true` or
`some false`.

1. `p → p` in K3.
2. `p → p` in Ł3.
3. `p ∨ ¬p` in Ł3.
4. `p ∨ ¬p` in LP.
-/

def taut1 : Option Bool := none
def taut2 : Option Bool := none
def taut3 : Option Bool := none
def taut4 : Option Bool := none

#eval [gradeYesNo 1 taut1 (isTautology strongKleene ml[ p → p ])
        "Remember the key result: what does every formula become when every atom is u?",
       gradeYesNo 2 taut2 (isTautology lukasiewicz3 ml[ p → p ])
        "Look at the one cell where Ł3 differs from K3.",
       gradeYesNo 3 taut3 (isTautology lukasiewicz3 ml[ p ∨ ¬p ])
        "Ł3's ∨ and ¬ are K3's. What is u ∨ ¬u?",
       gradeYesNo 4 taut4 (isTautology logicOfParadox ml[ p ∨ ¬p ])
        "In LP, u is designated. What values can p ∨ ¬p take?"]

/-!
### Entailment in three values

Entailment works as in the primer: Γ ⊨ A if every row that designates all
the premises designates A. Only "designated" has replaced "true". The
entailment tables mark counterexamples in red, as before.

**Explosion** ({p, ¬p} ⊨ q) holds in K3, as in classical logic: no row makes
both p and ¬p equal t. In LP it fails, since p = u makes both p and ¬p
designated:
-/

#html entailmentHtml strongKleene [ml[ p ], ml[ ¬p ]] ml[ q ]
#html entailmentHtml logicOfParadox [ml[ p ], ml[ ¬p ]] ml[ q ]

/-!
That is LP's selling point: a contradiction in the data (one source says
diabetic, another says not) doesn't let you conclude anything you like.

### Practice: does it follow?

`some true` if the entailment holds, `some false` if not. Draw the table
with `entailmentHtml` to see the counterexample when there is one.

1. Modus ponens, {p, p → q} ⊨ q, in K3.
2. Modus ponens in LP.
3. {p} ⊨ p ∨ q in K3. ("Diabetic, so diabetic or hypertensive.")
4. {p} ⊨ p ∨ q in weak Kleene.
-/

def follows1 : Option Bool := none
def follows2 : Option Bool := none
def follows3 : Option Bool := none
def follows4 : Option Bool := none

#eval [gradeYesNo 1 follows1 (entails strongKleene [ml[ p ], ml[ p → q ]] ml[ q ])
        "Designated means t in K3. If p is t and p → q is t, what can q be?",
       gradeYesNo 2 follows2 (entails logicOfParadox [ml[ p ], ml[ p → q ]] ml[ q ])
        "Try p = u and q = f. Which of the three are designated in LP?",
       gradeYesNo 3 follows3 (entails strongKleene [ml[ p ]] ml[ p ∨ q ])
        "If p is t, what is p ∨ q, whatever q is?",
       gradeYesNo 4 follows4 (entails weakKleene [ml[ p ]] ml[ p ∨ q ])
        "Try p = t and q = u in weak Kleene's ∨ table."]

#html entailmentHtml logicOfParadox [ml[ p ], ml[ p → q ]] ml[ q ]

/-!
Each logic gives something up. K3 loses every tautology, Ł3 keeps `p → p`
but not `p ∨ ¬p`, LP keeps the tautologies but loses modus ponens, and weak
Kleene loses even "p, so p or q". There is no three-valued logic that keeps
everything; which one fits depends on what u means in your data.

## CQL and FHIRPath are strong Kleene

Clinical Quality Language (CQL) is the HL7 language that electronic quality
measures are written in, and FHIRPath is the expression language used
throughout FHIR. Neither specification names its logic, but both publish
truth tables:

- **CQL 2.0.0** (Reference, "Logical Operators", Tables 9-A and 9-A1) gives
  `and`, `or`, `not`, `xor` and `implies` tables with `null` as the third
  value.
- **FHIRPath 3.0.0** ("Boolean logic") says its operators "use three-valued
  logic to propagate empty operands", with the empty collection `{ }` as
  the third value.

Both are the strong Kleene tables, with `null` or `{ }` for u. This project
keeps the tables, transcribed from the specifications, in
`data/specs/cql-2.0.0-logical.json` and `data/specs/fhirpath-3.0.0-boolean.json`,
and its tests check every row against `strongKleene`. If a future version
of either specification changes a table, the tests fail.

So Bea's criterion, written in CQL, is null:

```
define "Poor Control":
  "Has Diabetes" and "Most Recent HbA1c Percent" > 9
```

"Most Recent HbA1c Percent" is null because there is no result, and CQL's
comparison operators return null when an argument is null ("If either
argument is null, the result is null"). So the criterion is `true and null`,
which is null: `t ∧ u = u`.

### Where null becomes false

A query has to decide, in the end, whether to keep a patient or not, and
there are only two options. CQL's rule is in the Author's Guide
("Filtering"): "only elements where the condition evaluates to true are
included in the result, effectively ignoring the entries for which the
logical expression evaluates to null." The Quality Measure IG says the same
for population criteria (Conformance Requirement 3.11): "If population
criteria evaluate to null for a patient-based measure it is interpreted as
false."

So at the boundary of a query, u is treated like f. Put the strong Kleene
table for ¬ next to that rule, and something surprising happens to Bea:

- `where "Poor Control"` drops her, because `u` is not `true`;
- `where not "Poor Control"` also drops her, because `¬u = u`, which is not
  `true` either.

Bea is in neither list. A report that counts "poor control" and "not poor
control" separately and adds them up will not reach the number of diabetic
patients. CQL has operators to make the choice explicit: `X is null`,
`X is true` and `X is false` always return true or false (`null is true` is
false).

Measure writers do make that choice on purpose. CMS122v13, "Diabetes:
Glycemic Status Assessment Greater Than 9%", puts patients in the numerator
whose most recent result "is >9.0% or is missing, or was not performed
during the measurement period". Bea counts as poorly controlled there. The
measure is scored so that a lower rate is better, and counting a missing
test as poor control means a clinic can't improve its score by not
testing.

### Practice: what does the query do?

Predict whether Bea is kept (`some true`) or dropped (`some false`) by each
filter. A filter keeps a patient only when the condition is t.

1. `where "Poor Control"`
2. `where not "Poor Control"`
3. `where "Has Diabetes" or "Poor Control"`
-/

/-- A CQL `where` clause keeps a patient only when the condition is t. -/
def keptBy (condition : Formula) (patient : Atom → TV3) : Except String Bool :=
  (eval strongKleene patient condition).map (· == .t)

def kept1 : Option Bool := none
def kept2 : Option Bool := none
def kept3 : Option Bool := none

#eval [gradeYesNo 1 kept1 (keptBy poorControl bea)
        "Bea's criterion is u, and a filter keeps only t.",
       gradeYesNo 2 kept2 (keptBy ml[ ¬{poorControl} ] bea)
        "What is ¬u?",
       gradeYesNo 3 kept3 (keptBy ml[ diabetic ∨ {poorControl} ] bea)
        "Bea's diabetic is t. What is t ∨ u?"]

/-!
### A puzzle from the FHIRPath specification

FHIRPath 3.0.0's section on `implies` says two things that don't agree.
The table gives, for an empty left side:

| left | right | left implies right |
|---|---|---|
| `{ }` | `true` | `true` |
| `{ }` | `false` | `{ }` |
| `{ }` | `{ }` | `{ }` |

and a note under the table says: "Note carefully that if the left side of an
implies evaluates to empty, the result of the operation is the right side."

1. According to the note, what is `{ } implies false`?
2. According to the table?
3. Which one is strong Kleene's `u → f`?
-/

#html hint "Answers"
  "1. The note gives false: the right side. 2. The table gives { }. 3. The table: \
  in K3, u → f = u, which is { } in FHIRPath. The note is right in two of the three rows \
  (true and { }) and disagrees in the false row. As of the 3.0.0 release and the \
  continuous build checked on 2026-09-30, both say the same thing, and we found no \
  published erratum. The operator's definition in words agrees with the table."

#eval truthValue strongKleene (record .u [("q", .f)]) ml[ p → q ]

/-!
## Summary

- A third value, u for unknown, lets a record say "not measured" instead of
  "false". Strong Kleene logic (K3) evaluates with it: if the unknown
  couldn't change the answer, the answer is definite; otherwise it's u.
- On records with nothing unknown, K3 agrees with classical logic.
- K3 has no tautologies: with every atom unknown, every formula is u. Even
  "has diabetes or doesn't" is unknown for a patient with no record. A K3
  answer of t or f can be trusted; an answer of u may be too cautious.
- Weak Kleene makes u infectious, Łukasiewicz makes u → u true, and LP
  counts u as designated. Each keeps some inferences and loses others.
- CQL and FHIRPath use strong Kleene tables. At a query boundary, CQL keeps
  only true, so a null criterion is dropped, and so is its negation.
  Measures that care about missing data say what to do with it, as CMS122
  does.
-/

end ThreeValued
