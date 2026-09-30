import Gamen.ManyValued
import ProofWidgets.Component.HtmlDisplay

/-!
# Truth tables, patient records and graders for the many-valued notebooks

Lean-only; plan: `plans/three-valued-logic-2026-09-29.md`, "Interactivity".
Static HTML tables shown with `#html`, plus the plain-`String` helpers the
notebooks `#eval` (`Notebooks/PropLogicPrimer.lean`,
`Notebooks/ThreeValued.lean`). Nothing here is clickable, so the
KripkeExplorer's single-state-type constraint does not apply.

Usage in a notebook file:

    #html truthTableHtml classical [ml[ p ∧ q ], ml[ p → q ]]
    #html entailmentHtml strongKleene [ml[ p ], ml[ p → q ]] ml[ q ]

Rows are listed in `ManyValued.assignments` order: the first atom varies
slowest, values in the matrix's order (T before F, as in B&D's tables; t,
u, f as in the OLT's).
-/
open Lean ProofWidgets

namespace Gamen.Widgets

open Gamen Gamen.ManyValued

/-! ## Writing truth values -/

/-- How a truth value is written in the tables: B&D writes `T` and `F`
(Definition C.14); the OLT's three-valued chapter writes t, u, f, which
is also how students type them in Lean (`.t`, `.u`, `.f`). -/
class TVLabel (V : Type) where
  label : V → String

instance : TVLabel Bool := ⟨fun b => if b then "T" else "F"⟩
instance : TVLabel TV3 := ⟨toString⟩

/-- A formula's value under a valuation, written as in the tables, or
`error: …` when the formula is outside the matrix's language. -/
def truthValue {V : Type} [TVLabel V] (m : Matrix V) (v : Atom → V) (f : Formula) : String :=
  match eval m v f with
  | .ok x => TVLabel.label x
  | .error e => s!"error: {e}"

/-! ## Patient records -/

/-- A valuation built from a list of recorded facts. Atoms the list doesn't
mention get `missing`: `record false …` is the closed-world reading ("not
recorded" means "false"), `record .u …` the three-valued one ("not
recorded" means "unknown"). If an atom is listed twice, the first entry
counts. -/
def record {V : Type} (missing : V) (facts : List (String × V)) : Atom → V :=
  fun a => match facts.find? (·.1 == a.name) with
    | some (_, x) => x
    | none => missing

/-! ## Truth tables as data -/

/-- One row per valuation of the atoms of `fs`: the valuation, then each
formula's value. -/
def tableRows {V : Type} [Inhabited V] (m : Matrix V) (fs : List Formula) :
    List (List (Atom × V) × List (Except String V)) :=
  (assignments m.values (atomsOf fs)).map fun asg => (asg, fs.map (eval m (lookup asg)))

/-- The table as strings: a header row (atoms, then formulas), then one
row per valuation. The tests compare against this. -/
def tableGrid {V : Type} [Inhabited V] [TVLabel V] (m : Matrix V) (fs : List Formula) :
    List (List String) :=
  let header := (atomsOf fs).map toString ++ fs.map toString
  header :: (tableRows m fs).map fun (asg, vals) =>
    asg.map (fun (_, x) => TVLabel.label x) ++ vals.map fun
      | .ok x => TVLabel.label x
      | .error _ => "error"

/-- The column of one formula, top to bottom, as in `tableGrid`. -/
def column {V : Type} [Inhabited V] (m : Matrix V) (f : Formula) : List (Except String V) :=
  (tableRows m [f]).map fun (_, vals) => vals.headD (.error "no value")

/-- The valuations that designate every premise but not the conclusion:
the counterexamples to `premises ⊨ conclusion` (B&D Definition C.19(4)).
A row where some formula errors is not a counterexample; `entails`
reports the error instead. -/
def counterexamples {V : Type} [Inhabited V] (m : Matrix V) (premises : List Formula)
    (conclusion : Formula) : List (List (Atom × V)) :=
  (tableRows m (premises ++ [conclusion])).filterMap fun (asg, vals) =>
    match vals.mapM id with
    | .ok xs =>
      if (xs.take premises.length).all m.designated && !m.designated (xs.getLastD default)
      then some asg else none
    | .error _ => none

/-- Some valuation designates `f` (B&D Definition C.19(1)). -/
def satisfiable {V : Type} [Inhabited V] (m : Matrix V) (f : Formula) : Except String Bool := do
  let vals ← (column m f).mapM id
  return vals.any m.designated

/-- B&D Definition C.19: a tautology, satisfiable but not a tautology
("contingent"), or unsatisfiable. -/
def classify {V : Type} [Inhabited V] (m : Matrix V) (f : Formula) : String :=
  match isTautology m f, satisfiable m f with
  | .ok true, _ => "tautology"
  | .ok false, .ok true => "contingent"
  | .ok false, .ok false => "unsatisfiable"
  | .error e, _ | _, .error e => s!"error: {e}"

/-- `premises ⊨ conclusion` as a sentence. -/
def entailmentVerdict {V : Type} [Inhabited V] (m : Matrix V) (premises : List Formula)
    (conclusion : Formula) : String :=
  let lhs := ", ".intercalate (premises.map toString)
  match entails m premises conclusion with
  | .ok true => s!"{lhs} ⊨ {conclusion} in {m.name} logic: no counterexample."
  | .ok false => s!"{lhs} ⊭ {conclusion} in {m.name} logic: see the marked rows."
  | .error e => s!"error: {e}"

/-! ## Graders

Numbered feedback, in the style of `gradeValidity` (`Countermodel.lean`):
`none` means "not answered yet", and the hint appears only after a wrong
answer. -/

/-- Grade a predicted truth value. -/
def gradeValue {V : Type} [DecidableEq V] [TVLabel V] (n : Nat) (prediction : Option V)
    (actual : Except String V) (hint : String) : String :=
  match prediction, actual with
  | none, _ => s!"{n}. Not answered yet: replace `none` with your prediction."
  | some _, .error e => s!"{n}. This formula has no value here ({e})."
  | some p, .ok a =>
    if p = a then s!"{n}. ✓ Correct: {TVLabel.label a}."
    else s!"{n}. ✗ Not quite. {hint}"

/-- Grade a yes/no prediction (a tautology? an entailment?). -/
def gradeYesNo (n : Nat) (prediction : Option Bool) (actual : Except String Bool)
    (hint : String) : String :=
  match prediction, actual with
  | none, _ => s!"{n}. Not answered yet: replace `none` with `some true` or `some false`."
  | some _, .error e => s!"{n}. {e}"
  | some p, .ok a =>
    if p == a then s!"{n}. ✓ Correct: {if a then "yes" else "no"}."
    else s!"{n}. ✗ Not quite. {hint}"

/-- Grade a classification (B&D Definition C.19): the student writes
`some "tautology"`, `some "contingent"` or `some "unsatisfiable"`. -/
def gradeClassify {V : Type} [Inhabited V] (n : Nat) (m : Matrix V) (f : Formula)
    (answer : Option String) (hint : String) : String :=
  match answer with
  | none => s!"{n}. Not answered yet: replace `none` with `some \"tautology\"`, \
      `some \"contingent\"` or `some \"unsatisfiable\"`."
  | some a =>
    let c := classify m f
    if a == c then s!"{n}. ✓ Correct: {c}."
    else if !["tautology", "contingent", "unsatisfiable"].contains a then
      s!"{n}. \"{a}\" is not one of the three words: tautology, contingent, unsatisfiable."
    else s!"{n}. ✗ Not quite. {hint}"

/-- Grade a hand-filled column of a truth table, top row first. Reports the
first wrong row (1-based) rather than the right answer. -/
def gradeColumn {V : Type} [Inhabited V] [DecidableEq V] [TVLabel V] (m : Matrix V)
    (f : Formula) (answer : List (Option V)) : String :=
  let expected := column m f
  if answer.length != expected.length then
    s!"The table for {f} has {expected.length} rows; your list has {answer.length}."
  else if answer.all (·.isNone) then
    "Not answered yet: replace each `none` with `some …`."
  else
    let rows := (answer.zip expected).zipIdx
    match rows.find? (fun ((a, e), _) => match a, e with
        | some x, .ok y => x ≠ y
        | none, _ => true
        | some _, .error _ => true) with
    | none => s!"✓ Correct: that is the column for {f}."
    | some ((none, _), i) => s!"Row {i + 1} is still `none`."
    | some (_, i) => s!"✗ Row {i + 1} is not right. Find that row's values for the atoms \
        and apply the table for the main connective."

/-- Grade a "find a formula that …" exercise: `check` says whether the
student's formula does the job, and `goal` restates the job. -/
def gradeFind (n : Nat) (answer : Option Formula) (check : Formula → Bool) (goal : String) :
    String :=
  match answer with
  | none => s!"{n}. Not answered yet: replace `none` with `some ml[ … ]`."
  | some f =>
    if check f then s!"{n}. ✓ Correct: {f} {goal}."
    else s!"{n}. ✗ {f} does not do it: it should be a formula that {goal}."

/-! ## HTML -/

private def cell (tag : String) (s : String) (bold : Bool := false) : Html :=
  let pad := [("padding", Json.str "2px 10px"), ("textAlign", Json.str "center"),
    ("borderBottom", Json.str "1px solid rgba(127,127,127,0.4)")]
  let style := if bold then pad ++ [("fontWeight", Json.str "bold")] else pad
  Html.element tag #[("style", Json.mkObj style)] #[.text s]

private def tableEl (header : List String) (rows : List Html) : Html :=
  Html.element "table" #[("style", Json.mkObj [("borderCollapse", Json.str "collapse")])]
    #[Html.element "thead" #[] #[Html.element "tr" #[] (header.map (cell "th" ·)).toArray],
      Html.element "tbody" #[] rows.toArray]

private def valueCell {V : Type} [TVLabel V] (m : Matrix V) : Except String V → Html
  | .ok x => cell "td" (TVLabel.label x) (bold := m.designated x)
  | .error _ => cell "td" "error"

private def note (s : String) : Html :=
  Html.element "p" #[("style", Json.mkObj [("fontSize", Json.str "90%")])] #[.text s]

/-- A truth table for several formulas over the same atoms. Designated
values (T; t, and u in LP) are in bold. -/
def truthTableHtml {V : Type} [Inhabited V] [TVLabel V] (m : Matrix V) (fs : List Formula) :
    Html :=
  let header := (atomsOf fs).map toString ++ fs.map toString
  let rows := (tableRows m fs).map fun (asg, vals) =>
    Html.element "tr" #[] (asg.map (fun (p : Atom × V) => cell "td" (TVLabel.label p.2)) ++
      vals.map (valueCell m)).toArray
  Html.element "div" #[] #[tableEl header rows,
    note s!"{m.name} logic. Bold values are designated (they count as \"true\")."]

/-- The table for `premises ⊨ conclusion`: the last column says, for each
row where every premise is designated, whether the conclusion is too.
Those rows are the only ones that matter (B&D Definition C.19(4)); a ✗
is a counterexample. -/
def entailmentHtml {V : Type} [Inhabited V] [TVLabel V] (m : Matrix V)
    (premises : List Formula) (conclusion : Formula) : Html :=
  let fs := premises ++ [conclusion]
  let header := (atomsOf fs).map toString ++ fs.map toString ++ ["premises all designated?"]
  let rows := (tableRows m fs).map fun (asg, vals) =>
    let verdict := match vals.mapM id with
      | .ok xs =>
        if (xs.take premises.length).all m.designated then
          if m.designated (xs.getLastD default) then "✓ conclusion too" else "✗ counterexample"
        else ""
      | .error _ => "error"
    let bg := if verdict == "✗ counterexample" then
      #[("style", Json.mkObj [("background", Json.str "rgba(220,50,50,0.18)")])] else #[]
    Html.element "tr" bg (asg.map (fun (p : Atom × V) => cell "td" (TVLabel.label p.2)) ++
      vals.map (valueCell m) ++ [cell "td" verdict]).toArray
  Html.element "div" #[] #[tableEl header rows, note (entailmentVerdict m premises conclusion)]

end Gamen.Widgets
