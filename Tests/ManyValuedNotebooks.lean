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
requiring a ✓; the grader computes the real value, so a drifting formula,
record or table fails the case.
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
      && ok (gradeFind 4 (some ml[ p ]) (fun _ => true) "g")
      && !ok (gradeFind 4 (some ml[ p ]) (fun _ => false) "g")),
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
    ok (gradeColumn classical ml[ p ∧ ¬q ] [some false, some true, some false, some false])
      && ok (gradeColumn classical ml[ ¬p ∨ q ] [some true, some false, some true, some true])),
  ("primer hint: ¬p ∨ q and p → q have the same column",
    column classical ml[ ¬p ∨ q ] == column classical ml[ p → q ]),
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
    ok (gradeClassify 1 classical rule (some "contingent") "")
      && ok (gradeClassify 2 classical ml[ (p → q) ∨ (q → p) ] (some "tautology") "")
      && ok (gradeClassify 3 classical ml[ ¬(p → p) ] (some "unsatisfiable") "")
      && ok (gradeClassify 4 classical ml[ p → (q → p) ] (some "tautology") "")),
  ("primer classify hint 1: Ben's row makes the rule false, Ana's true",
    truthValue classical ben rule == "F" && truthValue classical ana rule == "T"),
  ("primer find-a-tautology hint: diabetic → diabetic passes the grader",
    ok (gradeFind 1 (some ml[ diabetic → diabetic ])
      (fun f => classify classical f == "tautology" && atomList f == [⟨"diabetic"⟩]
        && f != ml[ diabetic ∨ ¬diabetic ]) "")),
  ("primer modus ponens: holds, and exactly one row has all premises true",
    entails classical [rule, ml[ age65 ], ml[ diabetic ]] ml[ offer ] == .ok true
      && ((tableRows classical [rule, ml[ age65 ], ml[ diabetic ], ml[ offer ]]).filter
        fun (_, vs) => (vs.take 3).all (· == .ok true)).length == 1),
  ("primer affirming the consequent: fails; Dee's record is a counterexample",
    entails classical [rule, ml[ offer ]] ml[ age65 ∧ diabetic ] == .ok false
      && (counterexamples classical [rule, ml[ offer ]] ml[ age65 ∧ diabetic ]).any
        fun asg => asg.all fun (a, x) => dee a == x),
  ("primer entailment exercise: 1 no, 2 yes (modus tollens), 3 no, 4 yes (explosion)",
    ok (gradeYesNo 1 (some false) (entails classical [rule, ml[ ¬age65 ]] ml[ ¬offer ]) "")
      && ok (gradeYesNo 2 (some true)
        (entails classical [rule, ml[ ¬offer ]] ml[ ¬(age65 ∧ diabetic) ]) "")
      && ok (gradeYesNo 3 (some false) (entails classical [rule, ml[ ¬diabetic ]] ml[ ¬offer ]) "")
      && ok (gradeYesNo 4 (some true)
        (entails classical [ml[ diabetic ], ml[ ¬diabetic ]] ml[ offer ]) "")),
  ("primer: Dee (under 65, offered) complies, so denying the antecedent fails on her",
    truthValue classical dee rule == "T" && truthValue classical dee ml[ ¬age65 ] == "T"
      && truthValue classical dee ml[ ¬offer ] == "F"),
  ("primer explosion: no row makes diabetic and ¬diabetic both true",
    (counterexamples classical [ml[ diabetic ], ml[ ¬diabetic ]] ml[ offer ]).isEmpty
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
      && ok (gradeValue 2 (some TV3.t) (eval strongKleene bea ml[ diabetic ∨ hba1c_high ]) "")
      && ok (gradeValue 3 (some TV3.u) (eval strongKleene cal ml[ hba1c_high → diabetic ]) "")
      && ok (gradeValue 4 (some TV3.f) (eval strongKleene eve poorControl) "")),
  ("3v: the K3 rows without u are the classical tables",
    ((tableGrid strongKleene [ml[ p ∧ q ], ml[ p ∨ q ], ml[ p → q ]]).tail.filter
        (fun r => !(r.take 2).contains "u")).map (·.map String.toUpper)
      == (tableGrid classical [ml[ p ∧ q ], ml[ p ∨ q ], ml[ p → q ]]).tail),
  ("3v column exercise: K3 ¬p ∨ q = p → q column (t t t t u u t u f)",
    column strongKleene ml[ ¬p ∨ q ] == column strongKleene ml[ p → q ]
      && ok (gradeColumn strongKleene ml[ ¬p ∨ q ]
        [some .t, some .u, some .f, some .t, some .u, some .u, some .t, some .t, some .t])),
  ("3v: diabetic ∨ ¬diabetic is not a K3 tautology; u for Dot, and so is diabetic → diabetic",
    isTautology strongKleene ml[ diabetic ∨ ¬diabetic ] == .ok false
      && truthValue strongKleene dot ml[ diabetic ∨ ¬diabetic ] == "u"
      && truthValue strongKleene dot ml[ diabetic → diabetic ] == "u"),
  ("3v: every classical filling-in of Dot's diabetic gives t for diabetic ∨ ¬diabetic",
    [true, false].all fun b =>
      truthValue classical (record false [("diabetic", b)]) ml[ diabetic ∨ ¬diabetic ] == "T"),
  ("3v trick question: the natural attempts all fail the grader",
    [ml[ diabetic ∨ ¬diabetic ], ml[ diabetic → diabetic ], ml[ ¬(diabetic ∧ ¬diabetic) ],
     ml[ diabetic ], ml[ ¬diabetic ]].all fun f =>
      !ok (gradeFind 1 (some f)
        (fun f => atomList f == [⟨"diabetic"⟩] && eval strongKleene dot f == .ok .t) "")),
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
  ("3v tautology exercise: K3 p → p no, Ł3 p → p yes, Ł3 p ∨ ¬p no, LP p ∨ ¬p yes",
    ok (gradeYesNo 1 (some false) (isTautology strongKleene ml[ p → p ]) "")
      && ok (gradeYesNo 2 (some true) (isTautology lukasiewicz3 ml[ p → p ]) "")
      && ok (gradeYesNo 3 (some false) (isTautology lukasiewicz3 ml[ p ∨ ¬p ]) "")
      && ok (gradeYesNo 4 (some true) (isTautology logicOfParadox ml[ p ∨ ¬p ]) "")),
  ("3v explosion: holds in K3, fails in LP at p = u",
    entails strongKleene [ml[ p ], ml[ ¬p ]] ml[ q ] == .ok true
      && entails logicOfParadox [ml[ p ], ml[ ¬p ]] ml[ q ] == .ok false
      && (counterexamples logicOfParadox [ml[ p ], ml[ ¬p ]] ml[ q ]).all
        fun asg => asg.contains (⟨"p"⟩, .u)),
  ("3v entailment exercise: MP in K3 yes, MP in LP no (p = u, q = f), \
    p ⊨ p ∨ q in K3 yes, in weak Kleene no (p = t, q = u)",
    ok (gradeYesNo 1 (some true) (entails strongKleene [ml[ p ], ml[ p → q ]] ml[ q ]) "")
      && ok (gradeYesNo 2 (some false) (entails logicOfParadox [ml[ p ], ml[ p → q ]] ml[ q ]) "")
      && ok (gradeYesNo 3 (some true) (entails strongKleene [ml[ p ]] ml[ p ∨ q ]) "")
      && ok (gradeYesNo 4 (some false) (entails weakKleene [ml[ p ]] ml[ p ∨ q ]) "")
      && (counterexamples logicOfParadox [ml[ p ], ml[ p → q ]] ml[ q ]).contains
        [(⟨"p"⟩, .u), (⟨"q"⟩, .f)]
      && (counterexamples weakKleene [ml[ p ]] ml[ p ∨ q ]).contains
        [(⟨"p"⟩, .t), (⟨"q"⟩, .u)]),
  ("3v: ¬u = u", strongKleene.neg .u == .u),
  ("3v query exercise: Bea dropped by \"Poor Control\" and by its negation, \
    kept by \"Has Diabetes\" or \"Poor Control\"",
    ok (gradeYesNo 1 (some false) (keptBy poorControl bea) "")
      && ok (gradeYesNo 2 (some false) (keptBy ml[ ¬{poorControl} ] bea) "")
      && ok (gradeYesNo 3 (some true) (keptBy ml[ diabetic ∨ {poorControl} ] bea) "")),
  ("3v FHIRPath puzzle: K3 u → t = t, u → f = u, u → u = u (the table); \
    the note (result = right side) matches in two of three rows",
    strongKleene.impl .u .t == .t && strongKleene.impl .u .f == .u
      && strongKleene.impl .u .u == .u
      && ([TV3.t, .f, .u].filter fun r => strongKleene.impl .u r == r).length == 2
      && truthValue strongKleene (record TV3.u [("q", .f)]) ml[ p → q ] == "u") ]

def cases : List (String × Bool) := widgetCases ++ primerCases ++ threeValuedCases

end ManyValuedNotebookTests
