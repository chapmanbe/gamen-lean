import Gamen.Tableau
import Widgets.KripkeExplorer

/-!
# Countermodels from tableaux, in the Kripke explorer

Lean-only (no gamen-hs counterpart). From premises and a conclusion, run the
prefixed tableau (B&D Chapter 6). If it closes, the conclusion follows. If a
branch stays open, read a countermodel off it, as in B&D §6.9 "Countermodels
from Tableaux" (p. 110) and Example 6.22 (pp. 111–113), and show it in the
existing Kripke explorer (`Widgets/KripkeExplorer.lean`), where the student
can toggle facts and watch the checks change.

Only a model that `extractCountermodel` returned is ever shown. That
function re-checks the model against every signed formula on the branch, so
an unfinished (budget-truncated) or otherwise unsound branch yields
`.unknown`, never a picture.

Usage in a notebook file:

    #html countermodelHtml systemK [] ml[ □(p ∨ q) → □p ∨ □q ]
-/
open Lean ProofWidgets

namespace Gamen.Widgets

/-- What the tableau says about `premises ⊢ conclusion`. -/
inductive CountermodelView where
  /-- Every branch closed: the conclusion follows (B&D Theorem 6.6). -/
  | valid
  /-- A verified countermodel, read off open branch `branch` (1-based, in the
  order `buildTableau` returns the open branches). -/
  | countermodel (sc : Scenario) (branch : Nat)
  /-- The step budget ran out, or no open branch gave a verified model. -/
  | unknown (why : String)
  deriving Inhabited

/-! ## Layout

Worlds are prefixes (`"1"`, `"1.1"`, `"1.2.1"`). Depth (the number of dots)
gives the row. Every world gets its own column, in prefix order (parents
before children, `1.2 < 1.10`), so each child sits down and to the right of
its parent. Giving only the leaves columns and centering each parent above
its leaves puts a middle or only child directly under its parent's fact
list, which overlaps whenever there are three or more atoms.

Rows run from `topRow` down to `4.9 + 0.3 × k`, the lowest height the
`Scenario` docstring allows for `k` facts shown under a world. Every world is
editable, so a student can make every atom true at one world: `k` is the
number of atoms (at least 1, for the "(nothing)" line). So, for up to 9
atoms, every position is inside the 10 × 9 canvas and meets that constraint
by construction; what can fail is overlap, which `fitsCanvas` checks.

Measured limits (`fitsCanvas` on this geometry, 2026-09-29; the layout
tests in `Tests/Main.lean` pin them):

* every prefix tree with at most 4 worlds fits; with 5 worlds, every tree of
  depth at most 2 fits; with 6 worlds, a root with 5 children fits but many
  depth-2 shapes do not (columns 1.52 apart, rows as little as 0.75 apart);
  7 or more worlds never fit (columns 1.27 apart, closer than a fact list
  is wide);
* depth at most 3 (a fifth level's name, `1.1.1.1.1`, runs off the right
  edge);
* at most 4 atoms (the fact chips are 2.4 apart on a 10-wide canvas), with
  short names: one 15-character atom name already limits the model to
  3 worlds;
* at most 5 premises (6 check rows between y = 2.2 and y = 0.3).

A model that does not fit is shown as a static, still verified, text view
(`countermodelText`). -/

/-- The row of the root world. Its self-loop (if any) tops out at
`topRow + 0.87`, below the title's baseline at 8.7. -/
def topRow : Float := 7.6

/-- Facts drawn under each world when every atom holds there (at least one
line, for "(nothing)"). -/
def factLines (atoms : List String) : Nat := max 1 atoms.length

/-- The lowest row allowed by the `Scenario` docstring: y ≥ 4.9 + 0.3 × facts. -/
def bottomRow (atoms : List String) : Float := 4.9 + 0.3 * (factLines atoms).toFloat

/-- A prefix name as its path of numbers (`"1.2.1"` ↦ `[1, 2, 1]`). -/
def prefixPath (w : String) : List Nat := (w.splitOn ".").map (·.toNat?.getD 0)

/-- Lexicographic order on prefix paths, so `1.2 < 1.10` and parents come
before their children. -/
def pathLt : List Nat → List Nat → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => a < b || (a == b && pathLt as bs)

def depth (w : String) : Nat := (prefixPath w).length - 1

/-- Positions for the worlds, as described above. -/
def layout (worlds : List String) (atoms : List String) : List (String × Float × Float) :=
  let ws := worlds.mergeSort fun a b => pathLt (prefixPath a) (prefixPath b)
  let n := ws.length
  let spacing : Float := if n ≤ 1 then 0 else min 3.0 (7.6 / (n - 1).toFloat)
  let x0 : Float := 5.0 - spacing * (n - 1).toFloat / 2
  let maxDepth := (ws.map depth).foldl max 0
  let rowGap : Float :=
    if maxDepth == 0 then 0 else (topRow - bottomRow atoms) / maxDepth.toFloat
  ws.zipIdx.map fun (w, i) => (w, x0 + spacing * i.toFloat, topRow - rowGap * (depth w).toFloat)

/-- An axis-aligned box `(x₀, y₀, x₁, y₁)`. -/
abbrev Box := Float × Float × Float × Float

def Box.overlaps (a b : Box) : Bool :=
  let (ax0, ay0, ax1, ay1) := a
  let (bx0, by0, bx1, by1) := b
  ax0 < bx1 && bx0 < ax1 && ay0 < by1 && by0 < ay1

def Box.inside (a : Box) (x0 y0 x1 y1 : Float) : Bool :=
  let (ax0, ay0, ax1, ay1) := a
  x0 ≤ ax0 && y0 ≤ ay0 && ax1 ≤ x1 && ay1 ≤ y1

/-- The world's circle and name, plus its self-loop if it has one, following
`render` (radius 0.42, loop 0.45 above the circle, name at 15px ≈ 0.18 per
character from x − 0.22). -/
def worldBox (sc : Scenario) (w : String) (x y : Float) : Box :=
  let loop := if sc.edges.contains (w, w) then 0.45 else 0
  (x - 0.42, y - 0.42, max (x + 0.42) (x - 0.22 + 0.18 * w.length.toFloat), y + 0.42 + loop)

/-- The fact list under a world when every atom holds there, following
`render` (12px ≈ 0.15 per character from x − 0.9; lines 0.3 apart, the first
0.77 below the center). -/
def factBox (sc : Scenario) (x y : Float) : Box :=
  let widest := (sc.atoms.map String.length).foldl max "(nothing)".length
  let k := (factLines sc.atoms).toFloat
  (x - 0.9, y - 0.77 - 0.3 * (k - 1) - 0.1, x - 0.9 + 0.15 * widest.toFloat, y - 0.77 + 0.25)

/-- Does the scenario draw legibly: at most 4 atoms (the chip row), at most
6 checks (the results rows), every world and fact list inside the canvas
(below the title), and no two of them overlapping? -/
def fitsCanvas (sc : Scenario) : Bool :=
  let boxes := sc.worlds.map fun (w, x, y) => (w, [worldBox sc w x y, factBox sc x y])
  sc.atoms.length ≤ 4 && sc.checks.length ≤ 6
    && sc.worlds.all (fun (_, _, y) => y ≥ bottomRow sc.atoms - 1e-9)
    && boxes.all (fun (_, bs) => bs.all (·.inside 0 4.1 10 8.5))
    && boxes.all fun (w, bs) => boxes.all fun (v, cs) =>
        w == v || bs.all fun b => cs.all fun c => !b.overlaps c

/-! ## From a verified model to a scenario -/

def modelEdges (m : Model) : List (String × String) :=
  m.frame.relation.toList.flatMap fun (w, vs) => vs.toList.map (w, ·)

def modelValuation (m : Model) : List (String × List String) :=
  m.valuation.toList.map fun (a, ws) => (a.name, ws.toList)

/-- The checks: the conclusion (expected false at the root) and each premise
(expected true). The formulas themselves go in the surrounding prose. -/
def countermodelChecks (premises : List Formula) (conclusion : Formula) : List Check :=
  { label := "conclusion", formula := conclusion }
    :: premises.zipIdx.map fun (φ, i) => { label := s!"premise {i + 1}", formula := φ }

/-- The explorer scenario for a verified countermodel: every edge of the
(closed) relation, every atom, every world editable, checks at the root. -/
def countermodelScenario (sys : System) (premises : List Formula) (conclusion : Formula)
    (m : Model) (branch : Nat) : Scenario :=
  let atoms := modelValuation m |>.map (·.1)
  { title := s!"{sys.name} countermodel (open branch {branch})"
    worlds := layout m.frame.worlds.toList atoms
    edges := modelEdges m
    atoms
    editable := m.frame.worlds.toList
    evalAt := toString Prefix.root
    checks := countermodelChecks premises conclusion
    valuation := modelValuation m }

/-- Try `extractCountermodel` on each open branch in order and keep the first
model it returns (with its 1-based branch number), or the first error. -/
def firstVerified (sys : System) (bs : List Branch) : Except String (Model × Nat) :=
  go bs 1 none
where
  go : List Branch → Nat → Option String → Except String (Model × Nat)
    | [], _, firstErr => .error (firstErr.getD "the tableau has no open branch")
    | b :: rest, i, firstErr =>
      match extractCountermodel sys b with
      | .ok m => .ok (m, i)
      | .error e => go rest (i + 1) (firstErr <|> some e)

/-- Run the tableau for `premises ⊢ conclusion` in `sys` (with the same
assumptions as `tableauProves`, via `proofAssumptions`) and report the
verdict, with a verified countermodel when there is one. -/
def countermodelView (sys : System) (premises : List Formula) (conclusion : Formula)
    (maxSteps := defaultMaxSteps) : CountermodelView :=
  match buildTableau sys maxSteps (proofAssumptions premises conclusion) with
  | .closed => .valid
  | .exhausted n => .unknown s!"the tableau ran out of its step budget ({n} steps)"
  | .stillOpen bs =>
    match firstVerified sys bs with
    | .ok (m, i) => .countermodel (countermodelScenario sys premises conclusion m i) i
    | .error e => .unknown e

/-- Did every branch close? -/
def CountermodelView.isValid : CountermodelView → Bool
  | .valid => true
  | _ => false

private def setOf (xs : List String) : String := "{" ++ ", ".intercalate xs ++ "}"

/-- W, R and V of the countermodel in B&D's notation, e.g.
`W = {1, 1.1}; R = {⟨1, 1.1⟩}; V(p) = {1.1}`. -/
def Scenario.modelLines (sc : Scenario) : List String :=
  [s!"W = {setOf (sc.worlds.map (·.1))}",
   s!"R = {setOf (sc.edges.map fun (a, b) => s!"⟨{a}, {b}⟩")}"]
  ++ sc.valuation.map fun (a, ws) => s!"V({a}) = {setOf ws}"

/-- A one-line verdict, for `#eval` in the notebooks. -/
def CountermodelView.summary : CountermodelView → String
  | .valid => "valid: every branch closes"
  | .unknown why => s!"unknown: {why}"
  | .countermodel sc i => s!"countermodel (open branch {i}): {"; ".intercalate sc.modelLines}"

/-! ## HTML -/

private def para (s : String) : Html := Html.element "p" #[] #[.text s]

private def bulletList (items : List String) : Html :=
  Html.element "ul" #[] (items.map fun s => Html.element "li" #[] #[.text s]).toArray

/-- A static text view of a verified countermodel: W, R and V as lists. Used
when the model is too large to draw (`fitsCanvas`). -/
def countermodelText (sc : Scenario) : Html :=
  Html.element "div" #[] #[
    para "The model is too large to draw here, so it is listed instead.",
    bulletList sc.modelLines]

private def checksProse (premises : List Formula) (conclusion : Formula) : Html :=
  bulletList (s!"conclusion: {conclusion} (false at 1 in this model)"
    :: premises.zipIdx.map fun (φ, i) => s!"premise {i + 1}: {φ} (true at 1)")

/-- The notebook entry point: `#html countermodelHtml systemK [] ml[ … ]`. -/
def countermodelHtml (sys : System) (premises : List Formula) (conclusion : Formula)
    (maxSteps := defaultMaxSteps) : Html :=
  let what := if premises.isEmpty then s!"{conclusion}"
    else s!"{conclusion} (from {premises.length} premise{if premises.length == 1 then "" else "s"})"
  match countermodelView sys premises conclusion maxSteps with
  | .valid => para s!"Valid in {sys.name}: {what}. Every branch of the tableau closes."
  | .unknown why => para s!"Unknown in {sys.name}: {what}. {why}"
  | .countermodel sc i =>
    Html.element "div" #[] #[
      para s!"Not valid in {sys.name}: {what}. Here is a countermodel read off \
        open branch {i}. The checks are evaluated at world 1:",
      checksProse premises conclusion,
      if fitsCanvas sc then kripkeExplorer sc else countermodelText sc]

end Gamen.Widgets
