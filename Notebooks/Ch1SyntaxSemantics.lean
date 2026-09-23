import Gamen.Teaching
import Widgets.KripkeExplorer
import Widgets.Hint

/-!
# Chapter 1: Syntax and Semantics

*Lean port of Gamen.jl `notebooks/theory/pluto/ch1_syntax_and_semantics.jl`,
following Chapter 1 of [Boxes and Diamonds](https://bd.openlogicproject.org)
(B&D). Clinical companion: `Ch1HealthObligations.lean`.*

**How to use this file.** Put your cursor on an `#eval` or `#html` line to see
its result in the panel on the right. Change anything and every result below
updates. Exercises tell you what to edit.

**Learning outcomes.** After this notebook you will be able to:

1. construct modal formulas (atoms, connectives, □, ◇);
2. build a Kripke model and evaluate any formula at a world;
3. explain □ (true at *all* accessible worlds) vs. ◇ (true at *some*),
   including vacuous truth at dead-end worlds;
4. decide whether an English sentence needs modal logic, and translate it;
5. verify the duality □A ≡ ¬◇¬A on a concrete model.

## Why modal logic?

> *"Can't an LLM just do all the reasoning for me?"*

An LLM can generate plausible text about reasoning, but it cannot
*guarantee* that its conclusions follow from its premises. Modal logic exists
because "true or false" is not expressive enough for how we reason:

- **"It is raining"** is propositional: true or false.
- **"It might rain tomorrow"** is modal: *possibility* across situations.
- **"You must file your taxes"** is modal: *obligation* across acceptable outcomes.
- **"She knows the password"** is modal: true *in every situation consistent
  with her information*.

C. I. Lewis introduced modal operators in 1918; Saul Kripke's possible-worlds
semantics (late 1950s) made them rigorous and, eventually, computable. Today
modal logic underpins software verification, multi-agent AI, legal and
ethical reasoning, and clinical decision support.

## The language of basic modal logic

B&D Definition 1.1: the language has ⊥, propositional variables, the
connectives ¬, ∧, ∨, →, and two modal operators, □ ("necessarily," "in all
accessible situations") and ◇ ("possibly," "in some accessible situation").
□ and ◇ are *quantifiers over situations*: to evaluate them we need a space
of situations, a **Kripke model**.

### Building formulas (B&D Definition 1.2)

Every atom is a formula; if A and B are formulas, so are ¬A, (A ∧ B),
(A ∨ B), (A → B), □A, and ◇A. ⊤ abbreviates ¬⊥ and A ↔ B abbreviates
(A → B) ∧ (B → A) (Definition 1.3).

In this file you write formulas between `ml[` and `]`, in the same notation
as the book. Type `\box` for □, `\diamond` for ◇, `\not` for ¬, `\and` for ∧,
`\or` for ∨, `\to` for →, `\bot` for ⊥.
-/
open Gamen Gamen.Widgets

#eval ml[ ⊥ ]
#eval ml[ ⊤ ]
#eval [ml[ ¬p ], ml[ p ∧ q ], ml[ p ∨ q ], ml[ p → q ], ml[ p ↔ q ]]
#eval ml[ □p → p ]
#eval ml[ □(p → q) → (□p → □q) ]    -- Schema K

/-! Formulas are data: named formulas can be reused inside `ml[ … ]` with `{…}`. -/

def schemaK : Formula := ml[ □(p → q) → (□p → □q) ]
#eval ml[ {schemaK} ∧ ◇r ]

/-!
### Practice: translate English into formulas

Let `p` = "it is raining" and `q` = "I have an umbrella." Replace each `none`
with `some ml[ … ]`; the line below it tells you whether you are right.
-/

def t1 : Option Formula := none   -- "It is not raining."
def t2 : Option Formula := none   -- "If it is raining, then I have an umbrella."
def t3 : Option Formula := none   -- "It is necessarily raining."
def t4 : Option Formula := none   -- "It is possible that I have an umbrella."
def t5 : Option Formula := none   -- "If it is necessarily raining, then it is raining."
def t6 : Option Formula := none   -- "It is possible that it is raining and I don't have an umbrella."
def t7 : Option Formula := none   -- Schema K: "If necessarily rain implies umbrellas, then
                                  --  if it necessarily rains, I necessarily have an umbrella."

#eval [gradeFormula t1 ml[ ¬p ], gradeFormula t2 ml[ p → q ], gradeFormula t3 ml[ □p ],
       gradeFormula t4 ml[ ◇q ], gradeFormula t5 ml[ □p → p ],
       gradeFormula t6 ml[ ◇(p ∧ ¬q) ], gradeFormula t7 ml[ □(p → q) → (□p → □q) ]]

/-!
Two of these deserve a second look once you have them. □p → p (the T axiom)
holds on *reflexive* frames (Chapter 2) but not in general. Schema K holds on
*every* frame: it is the defining axiom of the weakest normal modal logic, K.

### Modal-free formulas

A formula is *modal-free* if it contains no □ or ◇:
-/

#eval (ml[ p ∧ ¬q ]).isModalFree
#eval (ml[ p → □q ]).isModalFree

/-!
### Practice: modal or not?

Decide whether each sentence needs modal logic, then open the hint.

1. "The patient has a fever and a cough."
2. "The bridge might collapse under heavy load."
3. "If the test is positive, the patient is infected."
4. "Every employee must complete safety training."
5. "Alice knows that the server is down."
6. "It is raining or it is not raining."
-/

#html hints [
  ("1. Reveal", "Propositional: fever ∧ cough. No modality needed."),
  ("2. Reveal", "Modal: 'might' is possibility, some situation where it collapses (◇)."),
  ("3. Reveal", "Propositional: positive → infected, a material implication."),
  ("4. Reveal", "Modal: 'must' is obligation, in all acceptable scenarios (deontic □)."),
  ("5. Reveal", "Modal: 'knows' means true in every situation consistent with Alice's information (epistemic □)."),
  ("6. Reveal", "Propositional: p ∨ ¬p, a tautology.") ]

/-!
## Relational models

B&D Definition 1.6: a model M = ⟨W, R, V⟩ has a nonempty set of worlds W,
an accessibility relation R ⊆ W × W, and a valuation V assigning each atom
the set of worlds where it is true.

What are "worlds"? Anything whose alternatives matter: board positions in a
game, treatment pathways for a patient, states of a program.

### Figure 1.1 from Boxes and Diamonds

- W = {w1, w2, w3}
- R = {w1Rw2, w1Rw3}: w1 accesses w2 and w3; w2 and w3 are dead ends.
- V(p) = {w1, w2}, V(q) = {w2}
-/

def figure11 : Scenario where
  title := "Figure 1.1: a simple model"
  worlds := [("w1", 1.2, 6.8), ("w2", 5.0, 8.0), ("w3", 5.0, 5.6)]
  edges := [("w1", "w2"), ("w1", "w3")]
  atoms := ["p", "q"]
  evalAt := "w1"
  valuation := [("p", ["w1", "w2"]), ("q", ["w2"])]

def M : Model := figure11.toModel

#html kripkeExplorer figure11

/-!
## Truth at a world (B&D Definition 1.7)

M, w ⊩ A ("A is true at w in M") is defined by cases:

- M, w ⊮ ⊥;
- M, w ⊩ p iff w ∈ V(p);
- ¬, ∧, ∨, → as in propositional logic, *at w*;
- M, w ⊩ □A iff M, w' ⊩ A for **every** w' with Rww';
- M, w ⊩ ◇A iff M, w' ⊩ A for **some** w' with Rww'.

`holdsAt M "w1" φ` computes M, w1 ⊩ φ.
-/

#eval holdsAt M "w1" ml[ ◇q ]

/-!
### Problem 1.1: which of the following hold?

Predict each answer from the diagram, then replace `none` with `some true`
or `some false`.

1. M, w1 ⊩ q            2. M, w3 ⊩ ¬q           3. M, w1 ⊩ p ∨ q
4. M, w1 ⊩ □(p ∨ q)     5. M, w3 ⊩ □q           6. M, w3 ⊩ □⊥
7. M, w1 ⊩ ◇q           8. M, w1 ⊩ □q           9. M, w1 ⊩ ¬□□¬q
-/

def problem11 : List (String × Formula) :=
  [("w1", ml[ q ]), ("w3", ml[ ¬q ]), ("w1", ml[ p ∨ q ]), ("w1", ml[ □(p ∨ q) ]),
   ("w3", ml[ □q ]), ("w3", ml[ □⊥ ]), ("w1", ml[ ◇q ]), ("w1", ml[ □q ]),
   ("w1", ml[ ¬□□¬q ])]

def predictions11 : List (Option Bool) :=
  [none, none, none, none, none, none, none, none, none]

#eval (problem11.zip predictions11).zipIdx.map fun (((w, φ), guess), i) =>
  s!"{i + 1}. M, {w} ⊩ {φ}: {grade guess (holdsAt M w φ)}"

#html hints [
  ("Explain 5 and 6", "w3 has no accessible worlds. □A requires A at *all* successors; \
     with none to check, □q and even □⊥ are vacuously true there."),
  ("Explain 9", "□□¬q is true at w1: w2 and w3 are dead ends, so □¬q is vacuously \
     true at both. Hence ¬□□¬q is false.") ]

/-!
**Statements Lean checks.** A `#eval` shows a value. The `example` lines
below *assert* answers, and Lean rejects the file if one is false. Change
a `true` to `false` to see what happens.
-/

example : holdsAt M "w3" ml[ □⊥ ] = true := by native_decide
example : holdsAt M "w1" ml[ □(p ∨ q) ] = false := by native_decide

/-!
### Practice: evaluate formulas on Figure 1.1

1. Does M, w2 ⊩ □p hold?
2. Does M, w1 ⊩ ◇(p ∧ q) hold?
3. Does M, w1 ⊩ □p hold?
4. Does M, w1 ⊩ ◇q ∧ ◇¬q hold?
-/

def practice : List (String × Formula) :=
  [("w2", ml[ □p ]), ("w1", ml[ ◇(p ∧ q) ]), ("w1", ml[ □p ]), ("w1", ml[ ◇q ∧ ◇¬q ])]

def practiceAnswers : List (Option Bool) := [none, none, none, none]

#eval (practice.zip practiceAnswers).zipIdx.map fun (((w, φ), guess), i) =>
  s!"{i + 1}. M, {w} ⊩ {φ}: {grade guess (holdsAt M w φ)}"

/-!
**5. Challenge.** Write a formula that is true at w3 but false at w1 and w2.
-/

def challenge : Formula := ml[ ⊥ ]   -- replace ⊥ with your formula

#eval
  let truth := ["w1", "w2", "w3"].map (holdsAt M · challenge)
  if truth == [false, false, true] then s!"✓ {challenge} is true only at w3."
  else s!"Not yet: {challenge} at w1, w2, w3 is {truth}."

/-!
## Duality of □ and ◇ (B&D Proposition 1.8)

□A is equivalent to ¬◇¬A, and ◇A to ¬□¬A, just as ∀ and ∃ are duals.
Check both at every world of M:
-/

#eval ["w1", "w2", "w3"].map fun w =>
  (w, holdsAt M w ml[ □p ] == holdsAt M w ml[ ¬◇¬p ],
      holdsAt M w ml[ ◇p ] == holdsAt M w ml[ ¬□¬p ])

/-!
## Truth in a model (B&D Definition 1.9)

A is *true in* M (M ⊩ A) if it is true at every world of M.
-/

#eval (trueIn M ml[ p ], trueIn M ml[ ⊤ ], trueIn M ml[ □⊥ ])

/-!
- p is not true in M: it fails at w3.
- ⊤ is true in every model.
- □⊥ is not true in M: it fails at w1, which has successors.

## Entailment (B&D Definition 1.23)

Γ entails A in M if A is true at every world where all of Γ is true. For
example, in M, {p, ◇q} entails ◇(p ∨ q) and {p} does not entail □p:
-/

def entailsIn (m : Model) (Γ : List Formula) (A : Formula) : Bool :=
  ["w1", "w2", "w3"].all fun w => !(Γ.all (holdsAt m w ·)) || holdsAt m w A

#eval (entailsIn M [ml[ p ], ml[ ◇q ]] ml[ ◇(p ∨ q) ], entailsIn M [ml[ p ]] ml[ □p ])

/-!
**What's next.** Chapter 2 asks which formulas are true on *every* model
with a given frame property (reflexive, serial, transitive …). That is where
□p → p and the D axiom □p → ◇p get their meaning.
-/
