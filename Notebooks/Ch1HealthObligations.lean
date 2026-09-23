import Gamen.Teaching
import Gamen.Tableau
import Widgets.KripkeExplorer

/-!
# Clinical Obligations and Modal Logic

*Lean port of Gamen.jl `notebooks/applications/health/ch1_health_clinical_obligations.jl`.
Companion to B&D Chapter 1 (`Ch1SyntaxSemantics.lean`).*

**How to use this file.** Open it in VS Code (with the Lean 4 extension) or
in the course's Lean web editor. Put your cursor on any `#eval` line to see
its result in the panel on the right; diagrams appear there too. When you
change anything, every result below the change updates automatically.

You are an emergency physician. Your hospital's CDS fires: *"This patient
**should** receive aspirin."* A colleague at another institution describes the
same guideline as: *"Patients with chest pain **must** receive aspirin within
10 minutes."* Your EHR treats "should" as a hard stop; theirs uses it as a
dismissible reminder.

**Same guideline. Two institutions. Two different clinical behaviors.**

Lomotan et al. (2010) documented this systematically: when guidelines use
deontic terms (*must*, *should*, *may*, *must not*), clinicians and EHR
developers interpret them with widely varying obligation levels.

**Modal logic** gives these terms a precise definition. By the end of this
notebook, you will be able to:

- translate clinical guideline statements ("must," "may," "must not if…")
  into formulas;
- build a Kripke model of a clinical scenario and its acceptable pathways;
- check whether a set of guidelines is satisfied in that model;
- detect when two guidelines conflict, even *conditionally*.

**Two terms used throughout.** *Modal*: about modes of truth (necessary,
possible, obligatory, permitted). *Deontic*: about obligation and permission
(Greek *deon*, duty).

## From clinical language to modal logic

"Must obtain consent" means that in **every** acceptable clinical scenario,
consent is obtained. "May use clinical judgment" means that **some**
acceptable pathway permits it. *Every* vs. *some* is exactly what the two
modal operators capture:

| Clinical term | Deontic meaning | Formula |
|---|---|---|
| "must," "is required" | obligation | `□p`: in all acceptable scenarios, p |
| "may," "is acceptable" | permission | `◇p`: in some acceptable scenario, p |
| "must not," "is contraindicated" | prohibition | `□¬p`: in all acceptable scenarios, not p |

In this file, formulas are written between `ml[` and `]` in textbook
notation: `ml[ □consent ]`, `ml[ active_bleeding → □¬thrombolytic ]`.
-/
open Gamen Gamen.Widgets ProofWidgets
open scoped ProofWidgets.Jsx

#eval ml[ active_bleeding → □¬thrombolytic ]

/-!
### Exercise 1: classify clinical statements

Write each statement as a formula. Replace `none` with `some ml[ … ]` and
put your cursor on the `#eval` line to check.

a. "Patients admitted with community-acquired pneumonia *must* receive
   antibiotics within 4 hours." (atom: `antibiotics_4hr`)
b. "Clinicians *may* substitute a generic statin for a brand-name
   equivalent." (atom: `substitute_generic`)
c. "Thrombolytics *must not* be administered to patients with recent
   intracranial surgery." (atom: `thrombolytic`)
-/

def answer1a : Option Formula := none
def answer1b : Option Formula := none
def answer1c : Option Formula := none

#eval gradeFormula answer1a ml[ □antibiotics_4hr ]
#eval gradeFormula answer1b ml[ ◇substitute_generic ]
#eval gradeFormula answer1c ml[ □¬thrombolytic ]

/-!
## Formalizing guidelines as formulas

Five clinical guidelines and their formalizations. Click a guideline in the
panel to expand it. (The Pluto version used a dropdown; this list shows all
five at once so you can compare them.)
-/

structure Guideline where
  id : String
  text : String
  term : String
  kind : String
  formula : Formula
  explanation : String

def guidelines : List Guideline := [
  { id := "G1", text := "Informed consent must be obtained before any procedure",
    term := "must", kind := "obligation", formula := ml[ □consent ],
    explanation := "In all deontically acceptable scenarios, informed consent is obtained. \
      There is no acceptable world where consent is absent." },
  { id := "G2", text := "Patients with bacteremia should receive blood cultures before antibiotics",
    term := "should", kind := "obligation", formula := ml[ □blood_cultures ],
    explanation := "\"Should\" is weaker than \"must\" in clinical language, but both map to \
      obligation (□) in standard deontic logic. Graded modalities could capture the \
      difference; basic modal logic cannot." },
  { id := "G3", text := "Clinicians may use clinical judgment to adjust antibiotic duration",
    term := "may", kind := "permission", formula := ml[ ◇adjust_duration ],
    explanation := "Adjusting is permitted: at least one acceptable world has it. It is \
      neither required nor prohibited." },
  { id := "G4", text := "Thrombolytics must not be given if the patient has active bleeding",
    term := "must not … if", kind := "conditional prohibition",
    formula := ml[ active_bleeding → □¬thrombolytic ],
    explanation := "IF active bleeding THEN it is obligatory that thrombolytics are not \
      given. The condition sits outside the modal operator." },
  { id := "G5", text := "Discharge planning should begin within 24 hours of admission",
    term := "should", kind := "obligation", formula := ml[ □discharge_plan ],
    explanation := "\"Within 24 hours\" needs temporal operators (Chapter 14). For now, \
      only the deontic content is formalized." } ]

def guidelineCard (g : Guideline) : Html :=
  <details>
    <summary>{.text s!"{g.id}: {g.text}"}</summary>
    <p>{.text s!"\"{g.term}\" → {g.kind} → {g.formula}"}</p>
    <p>{.text g.explanation}</p>
  </details>

#html <div>{... (guidelines.map guidelineCard).toArray}</div>

/-!
Notice the pattern: G1, G2, and G5 ("must"/"should") all become □, while G3
("may") becomes ◇. What does that tell you about how obligation *strength*
is represented in basic modal logic?

## A clinical Kripke model

**Scenario: an emergency department patient with chest pain.**

- **w1**: current state, patient presenting
- **w2**: acceptable pathway: consent obtained, blood cultures drawn, discharge planned
- **w3**: acceptable pathway: consent obtained, thrombolytics given (no active bleeding)
- **w4**: unacceptable state: thrombolytics given despite active bleeding

Accessibility w1 → w2 and w1 → w3 marks which next states are *acceptable*.
w4 is not accessible: it is not an acceptable scenario.
-/

def edScenario : Scenario where
  title := "Clinical scenario: ED patient with chest pain"
  worlds := [("w1", 1.0, 6.6), ("w2", 4.6, 7.9), ("w3", 4.6, 5.4), ("w4", 8.2, 6.6)]
  edges := [("w1", "w2"), ("w1", "w3")]
  atoms := ["consent", "blood_cultures", "thrombolytic", "active_bleeding", "discharge_plan"]
  evalAt := "w1"
  checks := guidelines.map fun g => { label := g.id, formula := g.formula }
  valuation := [("consent", ["w2", "w3"]), ("blood_cultures", ["w2"]),
                ("thrombolytic", ["w3", "w4"]), ("active_bleeding", ["w4"]),
                ("discharge_plan", ["w2"])]

def edModel : Model := edScenario.toModel

/-!
### Exercise 2: predict before you look

Before putting your cursor on the diagram below, predict which guidelines
hold at w1. Replace each `none` with `some true` or `some false`.
-/

def predictG1 : Option Bool := none
def predictG2 : Option Bool := none
def predictG3 : Option Bool := none
def predictG4 : Option Bool := none
def predictG5 : Option Bool := none

#eval (guidelines.zip [predictG1, predictG2, predictG3, predictG4, predictG5]).map
  fun (g, p) => s!"{g.id}: {grade p (holdsAt edModel "w1" g.formula)}"

/-! Now look. The diagram shows the model; the checks below it are
evaluated at w1. -/

#html kripkeExplorer edScenario

/-!
### Interpreting the results

- **G1 (consent) holds**: consent is obtained in both accessible worlds.
- **G2 (blood cultures) fails**: cultures are drawn in w2 but not w3, and
  □ requires truth in *all* accessible worlds.
- **G3 (adjust duration) fails**: no accessible world adjusts duration, and ◇
  requires *at least one*.
- **G4 (conditional prohibition) holds**: there is no active bleeding at w1,
  so the implication holds trivially.
- **G5 (discharge plan) fails**: planned in w2 but not w3.

A model satisfying every guideline needs *every* acceptable pathway to comply
with *every* obligation.

**Results you can rely on.** A `#eval` shows a value; the lines below
*state* two of these results, and Lean refuses to accept the file if a
statement is false. Try changing a `true` to `false`.
-/

example : holdsAt edModel "w1" ml[ □consent ] = true := by native_decide
example : holdsAt edModel "w1" ml[ □blood_cultures ] = false := by native_decide

/-!
## Exploring deontic concepts

### Obligation vs. permission: □ and ◇ are duals

"It is obligatory to obtain consent" = "it is not permitted to skip
consent": `□consent` ≡ `¬◇¬consent`. Check it at every world:
-/

#eval ["w1", "w2", "w3", "w4"].map fun w =>
  (w, holdsAt edModel w ml[ □consent ], holdsAt edModel w ml[ ¬◇¬consent ])

/-!
### Vacuous truth and dead-end worlds

At worlds with no accessible successors (w2, w3, w4), **every obligation is
vacuously true**, even a contradictory one:
-/

#eval ["w1", "w2", "w3"].map fun w => (w, holdsAt edModel w ml[ □(consent ∧ ¬consent) ])

/-!
In standard deontic logic, at a world with no acceptable alternatives,
*everything* is obligatory. Think of a patient with a contraindication to
every available treatment. This is why the **D axiom**, □p → ◇p ("if
something is obligatory, it must at least be permitted"), matters for
clinical reasoning: it rules out dead ends. Chapter 3 returns to it.

## Interactive exploration: build your own scenario

Choose which clinical facts hold at each acceptable pathway. In the panel:
click a fact at the bottom to select it, then click w2 or w3 to switch that
fact on or off there. The guideline checks at w1 update on every click.

(The Pluto version used six checkboxes; here you toggle facts directly on
the diagram.)
-/

def buildYourOwn : Scenario where
  title := "Build your own scenario (click to edit w2 and w3)"
  worlds := [("w1", 1.2, 7.0), ("w2", 5.5, 8.0), ("w3", 5.5, 6.0)]
  edges := [("w1", "w2"), ("w1", "w3")]
  atoms := ["consent", "blood_cultures", "thrombolytic"]
  editable := ["w2", "w3"]
  evalAt := "w1"
  checks := [
    { label := "G1: must obtain consent", formula := ml[ □consent ] },
    { label := "G2: should draw cultures", formula := ml[ □blood_cultures ] },
    { label := "G3': may give thrombolytics", formula := ml[ ◇thrombolytic ] },
    { label := "All obligations met", formula := ml[ □consent ∧ □blood_cultures ] } ]
  valuation := [("consent", ["w2", "w3"]), ("blood_cultures", ["w2"]),
                ("thrombolytic", ["w3"])]

#html kripkeExplorer buildYourOwn

/-!
Notice:

- **Obligations (□)** need the fact in *both* w2 and w3.
- **Permissions (◇)** need it in *at least one*.
- To meet every obligation, every acceptable pathway must comply.

## Guideline conflicts

- **G5**: "Discharge planning should begin within 24 hours" → `□discharge_plan`
- **G6**: "Discharge planning must not begin until cultures are finalized" →
  `□¬discharge_plan`

With one acceptable next state, try both valuations of `discharge_plan`:
-/

def g5 : Formula := ml[ □discharge_plan ]
def g6 : Formula := ml[ □¬discharge_plan ]

def twoWorlds (dischargePlanned : Bool) : Model :=
  { worlds := [("w1", 0, 0), ("w2", 0, 0)], edges := [("w1", "w2")],
    atoms := ["discharge_plan"], evalAt := "w1", title := "",
    valuation := [("discharge_plan", if dischargePlanned then ["w2"] else [])] :
    Scenario }.toModel

#eval [true, false].map fun planned =>
  (s!"discharge_plan at w2 = {planned}",
   s!"G5 = {holdsAt (twoWorlds planned) "w1" g5}",
   s!"G6 = {holdsAt (twoWorlds planned) "w1" g6}")

/-!
Either way, one guideline is violated: a **genuine conflict**.

### Conditional conflicts are subtler

- **G4**: `active_bleeding → □¬thrombolytic`
- **G7**: "Patients with STEMI must receive thrombolytics" → `□thrombolytic`
-/

def g4 : Formula := ml[ active_bleeding → □¬thrombolytic ]
def g7 : Formula := ml[ □thrombolytic ]

def stemiPatient (bleeding : Bool) : Model :=
  { worlds := [("w1", 0, 0), ("w2", 0, 0)], edges := [("w1", "w2")],
    atoms := ["thrombolytic", "active_bleeding"], evalAt := "w1", title := "",
    valuation := [("thrombolytic", ["w2"]),
                  ("active_bleeding", if bleeding then ["w1"] else [])] :
    Scenario }.toModel

#eval [false, true].map fun bleeding =>
  (s!"active_bleeding at w1 = {bleeding}",
   s!"G4 = {holdsAt (stemiPatient bleeding) "w1" g4}",
   s!"G7 = {holdsAt (stemiPatient bleeding) "w1" g7}")

/-!
Without bleeding, both hold: the guidelines are **consistent**. With
bleeding, G4 fails. They conflict only for patients with *both* STEMI and
active bleeding: exactly the edge case informal review misses.

### A preview of Chapter 6: let the prover decide

The model checks above test *one* model at a time. The tableau prover asks
whether *any* model can satisfy a set of formulas. With the D axiom
(every state has an acceptable successor):
-/

#eval consistency [g5, g6]
#eval consistency [g4, g7]
#eval consistency [g4, g7, ml[ active_bleeding ]]

/-!
### Exercise 3: conditional vs. unconditional conflicts

- **G8**: "Patients with sepsis *must* receive IV fluids within 1 hour" →
  `sepsis → □iv_fluids`
- **G9**: "Patients with fluid overload *must not* receive IV fluids" →
  `fluid_overload → □¬iv_fluids`

Are G8 and G9 unconditionally conflicting (like G5/G6) or conditionally
conflicting (like G4/G7)? For which patients? Predict, then ask the prover
by editing the formula lists below.
-/

def g8 : Formula := ml[ sepsis → □iv_fluids ]
def g9 : Formula := ml[ fluid_overload → □¬iv_fluids ]

#eval consistency [g8, g9]
#eval consistency [g8, g9, ml[ sepsis ]]

/-!
## Summary

| B&D concept | Clinical interpretation |
|---|---|
| Formula | a clinical recommendation or condition |
| □A | "A is obligatory" / "must" / "is required" |
| ◇A | "A is permitted" / "may" / "is acceptable" |
| □¬A | "A is prohibited" / "must not" |
| A → □B | "if condition A, then B is obligatory" |
| Kripke world | a possible clinical scenario |
| Accessibility | "deontically acceptable" transitions |
| M, w ⊩ A | guideline A is satisfied in scenario w |
| M ⊩ A | guideline A is satisfied in all scenarios |

**What's next.** Chapter 2: why seriality (the D axiom) makes obligations
achievable. Chapter 3: KD as the logic of clinical guidelines. Chapter 6:
automated conflict detection. Chapter 14: "before," "after," "within 7 days."
-/
