import Notebooks.PropLogicPrimer
import Notebooks.ThreeValued
import Widgets.TruthTable

/-!
# Answer keys for the many-valued notebooks, and `Widgets/TruthTable.lean`

Every answer the two notebooks state, in prose, in a hint or in a grader's
expected value, checked against the library (CLAUDE.md: "Every stated
answer in a ported notebook goes into the answer-key tests"). Plan:
`plans/three-valued-logic-2026-09-29.md`.

- `Notebooks/PropLogicPrimer.lean` (namespace `Primer`)
- `Notebooks/ThreeValued.lean` (namespace `ThreeValued`)

A graded exercise is checked by feeding its grader the stated answer and
requiring a ✓. The exercise's formulas, arguments, records and checks are
the notebook's own `def`s, not copies, and the grader computes the real
value, so a drifting formula, record, check or table fails the case.
-/

namespace ManyValuedNotebookTests

open Gamen Gamen.ManyValued Gamen.Widgets

private def ok (s : String) : Bool := (s.splitOn "✓").length > 1

/-! ## `Widgets/TruthTable.lean` -/

def widgetCases : List (String × Bool) := [
  ("truth table: p → q, classical, rows TT TF FT FF (B&D order)",
    tableGrid classical [ml[ p → q ]] ==
      [["p", "q", "(p → q)"], ["T", "T", "T"], ["T", "F", "F"], ["F", "T", "T"], ["F", "F", "T"]]),
  ("truth table: K3 p ∧ q has 9 rows in the order t, u, f",
    (tableGrid strongKleene [ml[ p ∧ q ]]).tail.map (·.take 2) ==
      [["t", "t"], ["t", "u"], ["t", "f"], ["u", "t"], ["u", "u"], ["u", "f"],
       ["f", "t"], ["f", "u"], ["f", "f"]]),
  ("truth table: a formula outside the language shows `error`",
    tableGrid strongKleene [ml[ p ↔ q ]] |>.tail |>.all (·.getLast? == some "error")),
  ("record: listed facts, the first entry wins, the rest get `missing`",
    record TV3.u [("p", .t), ("p", .f)] ⟨"p"⟩ == .t && record TV3.u [] ⟨"q"⟩ == .u
      && record false [("p", true)] ⟨"q"⟩ == false),
  ("classify: tautology / contingent / unsatisfiable / error",
    classify classical ml[ p ∨ ¬p ] == "tautology"
      && classify classical ml[ p ] == "contingent"
      && classify classical ml[ p ∧ ¬p ] == "unsatisfiable"
      && (classify strongKleene ml[ ⊥ ]).startsWith "error"),
  ("counterexamples: p → q, q ⊭ p has exactly the row p = F, q = T",
    counterexamples classical [ml[ p → q ], ml[ q ]] ml[ p ] == [[(⟨"p"⟩, false), (⟨"q"⟩, true)]]),
  ("counterexamples agree with entails (valid ⇔ none), classical and LP",
    [(classical.name, (counterexamples classical [ml[ p ], ml[ p → q ]] ml[ q ]).isEmpty,
        entails classical [ml[ p ], ml[ p → q ]] ml[ q ] == .ok true),
     (logicOfParadox.name, (counterexamples logicOfParadox [ml[ p ], ml[ p → q ]] ml[ q ]).isEmpty,
        entails logicOfParadox [ml[ p ], ml[ p → q ]] ml[ q ] == .ok true)].all
      fun (_, a, b) => a == b),
  ("gradeColumn: right, wrong row, unanswered, wrong length",
    gradeColumn classical ml[ p → q ] [some true, some false, some true, some true]
        == "✓ Correct: that is the column for (p → q)."
      && (gradeColumn classical ml[ p → q ] [some true, some true, some true, some true]).startsWith
        "✗ Row 2 is not right"
      && (gradeColumn classical ml[ p → q ] [none, none, none, none]).startsWith "Not answered yet"
      && (gradeColumn classical ml[ p → q ] [some true, none, some true, some true])
        == "Row 2 is still `none`."
      && (gradeColumn classical ml[ p → q ] [some true]).startsWith "The table for"),
  ("gradeValue / gradeYesNo / gradeClassify / gradeFind: none, right, wrong",
    (gradeValue 1 (none : Option TV3) (.ok .u) "H").startsWith "1. Not answered yet"
      && gradeValue 1 (some TV3.u) (.ok .u) "H" == "1. ✓ Correct: u."
      && gradeValue 1 (some TV3.t) (.ok .u) "H" == "1. ✗ Not quite. H"
      && gradeYesNo 2 (some false) (.ok false) "H" == "2. ✓ Correct: no."
      && gradeYesNo 2 (some true) (.ok false) "H" == "2. ✗ Not quite. H"
      && gradeClassify 3 classical ml[ p ∨ ¬p ] (some "tautology") "H" == "3. ✓ Correct: tautology."
      && gradeClassify 3 classical ml[ p ∨ ¬p ] (some "contingent") "H" == "3. ✗ Not quite. H"
      && (gradeClassify 3 classical ml[ p ∨ ¬p ] (some "valid") "H").startsWith "3. \"valid\" is not"
      && ok (gradeFind 4 (some ml[ p ]) (fun _ => .ok true) "g")
      && !ok (gradeFind 4 (some ml[ p ]) (fun _ => .ok false) "g")),
  ("graders report a formula outside the language instead of marking it wrong",
    (gradeClassify 1 classical ml[ p ↔ p ] (some "tautology") "H").startsWith "1. (p ↔ p) has no value"
      && (gradeColumn strongKleene ml[ p ↔ q ] [some .t]).startsWith "(p ↔ q) has no truth table"
      && (gradeFind 1 (some ml[ diabetic ↔ diabetic ]) Primer.tautologyCheck "g").startsWith
        "1. (diabetic ↔ diabetic) has no value"),
  ("entailmentVerdict with no premises prints ∅",
    (entailmentVerdict classical [] ml[ p ∨ ¬p ]).startsWith "∅ ⊨ (p ∨ ¬p)"),
  ("truthValue shows T/F classically, t/u/f in three values, and errors",
    truthValue classical (record false []) ml[ p → q ] == "T"
      && truthValue strongKleene (record TV3.u []) ml[ p ] == "u"
      && (truthValue strongKleene (record TV3.u []) ml[ ⊥ ]).startsWith "error:") ]

/-! ## `Notebooks/PropLogicPrimer.lean` -/

open Primer in
def primerCases : List (String × Bool) := [
  ("primer: the rule is ((age65 ∧ diabetic) → offer); 3 atoms give 8 rows",
    toString rule == "((age65 ∧ diabetic) → offer)"
      && (tableGrid classical [ml[ age65 ∧ diabetic ], rule]).length == 9),
  ("primer column exercises: p ∧ ¬q = F T F F; ¬p ∨ q = T F T T",
    ok (gradeColumn classical columnFormula1 [some false, some true, some false, some false])
      && ok (gradeColumn classical columnFormula2 [some true, some false, some true, some true])),
  ("primer hint: ¬p ∨ q and p → q have the same column",
    column classical columnFormula2 == column classical ml[ p → q ]),
  ("primer: the main connective of p ∧ ¬q is ∧",
    match columnFormula1 with | .and _ _ => true | _ => false),
  ("primer: Ana complies (T → T via T ∧ T)",
    truthValue classical ana rule == "T"
      && truthValue classical ana ml[ age65 ∧ diabetic ] == "T"),
  ("primer compliance exercise: Ben F, Cy T, Dee T",
    ok (gradeValue 1 (some false) (eval classical ben rule) "")
      && ok (gradeValue 2 (some true) (eval classical cy rule) "")
      && ok (gradeValue 3 (some true) (eval classical dee rule) "")),
  ("primer: diabetic ∨ ¬diabetic tautology, diabetic ∧ ¬diabetic unsatisfiable",
    classify classical ml[ diabetic ∨ ¬diabetic ] == "tautology"
      && classify classical ml[ diabetic ∧ ¬diabetic ] == "unsatisfiable"),
  ("primer classify exercise: rule contingent; (p → q) ∨ (q → p) tautology; \
    ¬(p → p) unsatisfiable; p → (q → p) tautology",
    ok (gradeClassify 1 classical kindFormula1 (some "contingent") "")
      && ok (gradeClassify 2 classical kindFormula2 (some "tautology") "")
      && ok (gradeClassify 3 classical kindFormula3 (some "unsatisfiable") "")
      && ok (gradeClassify 4 classical kindFormula4 (some "tautology") "")
      && kindFormula1 == rule),
  ("primer classify hint 1: Ben's row makes the rule false, Ana's true",
    truthValue classical ben rule == "F" && truthValue classical ana rule == "T"),
  ("primer find-a-tautology hint: diabetic → diabetic passes the grader",
    ok (gradeFind 1 (some ml[ diabetic → diabetic ]) tautologyCheck "")
      && !ok (gradeFind 1 (some ml[ diabetic ∨ ¬diabetic ]) tautologyCheck "")
      && !ok (gradeFind 1 (some ml[ p → p ]) tautologyCheck "")
      && !ok (gradeFind 1 (some ml[ diabetic ]) tautologyCheck "")),
  ("primer modus ponens: holds, and exactly one row has all premises true",
    entails classical [rule, ml[ age65 ], ml[ diabetic ]] ml[ offer ] == .ok true
      && ((tableRows classical [rule, ml[ age65 ], ml[ diabetic ], ml[ offer ]]).filter
        fun (_, vs) => (vs.take 3).all (· == .ok true)).length == 1),
  ("primer question 2: offer and the rule don't give age65 either",
    entails classical [rule, ml[ offer ]] ml[ age65 ] == .ok false),
  ("primer affirming the consequent: fails; Dee's record is a counterexample",
    entails classical [rule, ml[ offer ]] ml[ age65 ∧ diabetic ] == .ok false
      && (counterexamples classical [rule, ml[ offer ]] ml[ age65 ∧ diabetic ]).any
        fun asg => asg.all fun (a, x) => dee a == x),
  ("primer entailment exercise: 1 no, 2 yes (modus tollens), 3 no, 4 yes (explosion)",
    ok (gradeYesNo 1 (some false) (argument1.follows classical) "")
      && ok (gradeYesNo 2 (some true) (argument2.follows classical) "")
      && ok (gradeYesNo 3 (some false) (argument3.follows classical) "")
      && ok (gradeYesNo 4 (some true) (argument4.follows classical) "")),
  ("primer Prop C.21: Γ ⊨ A iff Γ ∪ {¬A} is unsatisfiable, on all four exercises",
    [argument1, argument2, argument3, argument4].all fun a =>
      let conj := (a.premises ++ [Formula.not a.conclusion]).foldr (fun f acc => Formula.and f acc) ml[ p ∨ ¬p ]
      (a.follows classical).map (!·) == satisfiable classical conj),
  ("primer: Dee (under 65, offered) complies, so denying the antecedent fails on her",
    argument1.premises.all (fun f => truthValue classical dee f == "T")
      && truthValue classical dee argument1.conclusion == "F"),
  ("primer explosion: no row makes diabetic and ¬diabetic both true",
    (counterexamples classical argument4.premises argument4.conclusion).isEmpty
      && classify classical ml[ diabetic ∧ ¬diabetic ] == "unsatisfiable") ]

/-! ## `Notebooks/ThreeValued.lean` -/

open ThreeValued in
def threeValuedCases : List (String × Bool) := [
  ("3v: closed world makes Bea's criterion F; K3 makes it u",
    truthValue classical beaClosedWorld poorControl == "F"
      && truthValue strongKleene bea poorControl == "u"),
  ("3v: t ∧ u = u, f ∧ u = f, t ∨ u = t (K3)",
    strongKleene.conj .t .u == .u && strongKleene.conj .f .u == .f
      && strongKleene.disj .t .u == .t),
  ("3v value exercise: Cal f, Bea t, Cal u, Eve f",
    ok (gradeValue 1 (some TV3.f) (eval strongKleene cal poorControl) "")
      && ok (gradeValue 2 (some TV3.t) (eval strongKleene bea valueFormula2) "")
      && ok (gradeValue 3 (some TV3.u) (eval strongKleene cal valueFormula3) "")
      && ok (gradeValue 4 (some TV3.f) (eval strongKleene eve poorControl) "")),
  ("3v: the K3 rows without u are the classical tables",
    ((tableGrid strongKleene [ml[ p ∧ q ], ml[ p ∨ q ], ml[ p → q ]]).tail.filter
        (fun r => !(r.take 2).contains "u")).map (·.map String.toUpper)
      == (tableGrid classical [ml[ p ∧ q ], ml[ p ∨ q ], ml[ p → q ]]).tail),
  ("3v column exercise: K3 ¬p ∨ q = p → q column (t u f t u u t t t)",
    column strongKleene columnFormula == column strongKleene ml[ p → q ]
      && ok (gradeColumn strongKleene columnFormula
        [some .t, some .u, some .f, some .t, some .u, some .u, some .t, some .t, some .t])),
  ("3v: diabetic ∨ ¬diabetic is not a K3 tautology; u for Dot, and so is diabetic → diabetic",
    isTautology strongKleene ml[ diabetic ∨ ¬diabetic ] == .ok false
      && classify strongKleene ml[ diabetic ∨ ¬diabetic ] == "contingent"
      && column strongKleene ml[ diabetic ∨ ¬diabetic ] == [.ok .t, .ok .u, .ok .t]
      && truthValue strongKleene dot ml[ diabetic ∨ ¬diabetic ] == "u"
      && truthValue strongKleene dot ml[ diabetic → diabetic ] == "u"),
  ("3v: every classical filling-in of Dot's diabetic gives t for diabetic ∨ ¬diabetic",
    [true, false].all fun b =>
      truthValue classical (record false [("diabetic", b)]) ml[ diabetic ∨ ¬diabetic ] == "T"),
  ("3v trick question: the natural attempts all fail the grader",
    [ml[ diabetic ∨ ¬diabetic ], ml[ diabetic → diabetic ], ml[ ¬(diabetic ∧ ¬diabetic) ],
     ml[ diabetic ], ml[ ¬diabetic ]].all fun f =>
      !ok (gradeFind 1 (some f) trickCheck "")),
  ("3v weak Kleene: f ∧ u = u, so Cal's criterion is u",
    weakKleene.conj .f .u == .u && truthValue weakKleene cal poorControl == "u"),
  ("3v Łukasiewicz: u → u = t; p → p tautology; p ∨ ¬p not",
    lukasiewicz3.impl .u .u == .t
      && isTautology lukasiewicz3 ml[ p → p ] == .ok true
      && isTautology lukasiewicz3 ml[ p ∨ ¬p ] == .ok false),
  ("3v LP: p ∨ ¬p is a tautology; t and u designated",
    isTautology logicOfParadox ml[ p ∨ ¬p ] == .ok true
      && logicOfParadox.designated .u && logicOfParadox.designated .t
      && !logicOfParadox.designated .f),
  ("3v prose: K3 p → p is not a tautology",
    isTautology strongKleene ml[ p → p ] == .ok false),
  ("3v tautology exercise: K3 ¬(p ∧ ¬p) no, Ł3 (p ∧ q) → p yes, Kw p ∨ ¬p no, LP p → p yes",
    ok (gradeYesNo 1 (some false) (isTautology strongKleene tautFormula1) "")
      && ok (gradeYesNo 2 (some true) (isTautology lukasiewicz3 tautFormula2) "")
      && ok (gradeYesNo 3 (some false) (isTautology weakKleene tautFormula3) "")
      && ok (gradeYesNo 4 (some true) (isTautology logicOfParadox tautFormula4) "")
      && isTautology classical tautFormula1 == .ok true),
  ("3v tautology hints: Ł3 u → u = t, u → t = t; LP u → u = u, designated",
    lukasiewicz3.impl .u .u == .t && lukasiewicz3.impl .u .t == .t
      && logicOfParadox.impl .u .u == .u && logicOfParadox.designated .u),
  ("3v explosion: holds in K3, fails in LP at p = u",
    entails strongKleene [ml[ p ], ml[ ¬p ]] ml[ q ] == .ok true
      && entails logicOfParadox [ml[ p ], ml[ ¬p ]] ml[ q ] == .ok false
      && (counterexamples logicOfParadox [ml[ p ], ml[ ¬p ]] ml[ q ]).all
        fun asg => asg.contains (⟨"p"⟩, .u)),
  ("3v entailment exercise: MP in K3 yes, MP in LP no (p = u, q = f), \
    p ⊨ p ∨ q in K3 yes, in weak Kleene no (p = t, q = u)",
    ok (gradeYesNo 1 (some true) (modusPonens.follows strongKleene) "")
      && ok (gradeYesNo 2 (some false) (modusPonens.follows logicOfParadox) "")
      && ok (gradeYesNo 3 (some true) (addition.follows strongKleene) "")
      && ok (gradeYesNo 4 (some false) (addition.follows weakKleene) "")
      && (counterexamples logicOfParadox modusPonens.premises modusPonens.conclusion).contains
        [(⟨"p"⟩, .u), (⟨"q"⟩, .f)]
      && (counterexamples weakKleene addition.premises addition.conclusion).contains
        [(⟨"p"⟩, .t), (⟨"q"⟩, .u)]),
  ("3v: ¬u = u", strongKleene.neg .u == .u),
  ("3v query exercise: Bea dropped by \"Poor Control\" and by its negation, \
    kept by \"Has Diabetes\" or \"Poor Control\"",
    ok (gradeYesNo 1 (some false) (keptBy query1 bea) "")
      && ok (gradeYesNo 2 (some false) (keptBy query2 bea) "")
      && ok (gradeYesNo 3 (some true) (keptBy query3 bea) "")
      && query1 == poorControl && query2 == .not poorControl),
  ("3v: the four logics' summary (K3 loses p → p, Ł3 keeps it but not p ∨ ¬p, \
    LP keeps p ∨ ¬p but loses modus ponens, Kw loses addition)",
    isTautology strongKleene ml[ p → p ] == .ok false
      && isTautology lukasiewicz3 ml[ p → p ] == .ok true
      && isTautology lukasiewicz3 ml[ p ∨ ¬p ] == .ok false
      && isTautology logicOfParadox ml[ p ∨ ¬p ] == .ok true
      && modusPonens.follows logicOfParadox == .ok false
      && addition.follows weakKleene == .ok false),
  ("3v FHIRPath puzzle: K3 u → t = t, u → f = u, u → u = u (the table); \
    the note (result = right side) matches in two of three rows",
    strongKleene.impl .u .t == .t && strongKleene.impl .u .f == .u
      && strongKleene.impl .u .u == .u
      && ([TV3.t, .f, .u].filter fun r => strongKleene.impl .u r == r).length == 2
      && truthValue strongKleene (record TV3.u [("q", .f)]) ml[ p → q ] == "u") ]

def cases : List (String × Bool) := widgetCases ++ primerCases ++ threeValuedCases

end ManyValuedNotebookTests
