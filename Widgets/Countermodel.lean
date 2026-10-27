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
gives the row, and every world gets its own column. `arrange` tries column
orders and shifts (`layoutShifts`) and keeps the first that `fitsCanvas`:

* in-order first: half of a world's children to its left, half to its
  right, so a parent sits between its children. (Centering a parent over
  its leaves instead puts a middle or only child directly under the
  parent's fact list; putting the root in the first column makes its
  arrows to far children graze the children in between.)
* then prefix order (each parent left of its subtree);
* each unshifted, then with every other column lifted or dropped. A chain
  1 → 1.1 → 1.1.1 lies on one straight line otherwise, and in S4 the
  closure edge ⟨1, 1.1.1⟩ would run under world 1.1.

Rows run from `topRow` down to `4.9 + 0.3 × k`, the lowest height the
`Scenario` docstring allows for `k` facts shown under a world. Every world is
editable, so a student can make every atom true at one world: `k` is the
number of atoms (at least 1, for the "(nothing)" line). Shifts are clamped
to those rows, so, for up to 9 atoms, every position is inside the 10 × 9
canvas and meets that constraint. What can fail is legibility, which
`fitsCanvas` checks: overlapping worlds or fact lists, an arrow through a
world it does not end at, or text too wide for its place.

Measured limits (`fitsCanvas`, 2026-09-29; the layout tests in
`Tests/Main.lean` pin them), with one-letter atoms:

* K and KT (tree edges, with or without self-loops): every prefix tree with
  at most 4 worlds fits, and with 5 worlds every tree of depth at most 2; a
  root with 5 children fits; with 4 atoms, no 7-world tree fits;
* S4 (the reflexive, transitive closure): every tree with at most 3 worlds,
  and every 4-world tree of depth at most 2;
* depth at most 3 (a fifth level's name, `1.1.1.1.1`, runs off the right
  edge);
* at most 4 atoms (the fact chips are 2.4 apart), each at most 12 ASCII
  characters (the chip is 2.2 wide);
* at most 5 premises (6 check rows between y = 2.2 and y = 0.3), and each
  check row, which draws its formula, within the canvas width: a
  conclusion of 6 conjoined atoms fits, 7 do not. The full formulas are
  also in the HTML prose.

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

/-- `c` is a child `w.n` of `w`. -/
def isChildName (c w : String) : Bool :=
  let pc := prefixPath c
  let pw := prefixPath w
  pc.length == pw.length + 1 && pw.isPrefixOf pc

/-- In-order column order: the first half of a world's children (with their
subtrees) to its left, the rest to its right, so a parent sits between its
children rather than above one of them. The fuel is the number of worlds,
which bounds the depth. -/
def inorderFrom (ws : List String) : Nat → String → List String
  | 0, _ => []
  | fuel + 1, w =>
    let cs := ws.filter (isChildName · w)
    let k := cs.length / 2
    (cs.take k).flatMap (inorderFrom ws fuel) ++ [w] ++ (cs.drop k).flatMap (inorderFrom ws fuel)

/-- Column orders: `0` is prefix order (each parent left of its subtree),
`1` is in-order from the root (worlds it misses keep prefix order, at the
end). -/
def columnOrder (order : Nat) (worlds : List String) : List String :=
  let ws := worlds.mergeSort fun a b => pathLt (prefixPath a) (prefixPath b)
  if order == 0 then ws else
    match ws with
    | [] => []
    | root :: _ =>
      let io := inorderFrom ws (ws.length + 1) root
      io ++ ws.filter (!io.contains ·)

/-- Positions with every world in its own column (in `columnOrder order`)
and rows by depth; then the worlds in every other column (`parity`) move by
`bump`, clamped to the rows allowed (`bottomRow`..`topRow`). The result
lists the worlds in prefix order, whatever their columns. -/
def layoutWith (order : Nat) (bump : Float) (parity : Nat) (worlds atoms : List String) :
    List (String × Float × Float) :=
  let ws := columnOrder order worlds
  let n := ws.length
  let spacing : Float := if n ≤ 1 then 0 else min 3.0 (7.6 / (n - 1).toFloat)
  let x0 : Float := 5.0 - spacing * (n - 1).toFloat / 2
  let maxDepth := (ws.map depth).foldl max 0
  let lo := bottomRow atoms
  let rowGap : Float := if maxDepth == 0 then 0 else (topRow - lo) / maxDepth.toFloat
  let placed := ws.zipIdx.map fun (w, i) =>
    let y := topRow - rowGap * (depth w).toFloat
    let y' := if i % 2 == parity then max lo (min topRow (y + bump)) else y
    (w, x0 + spacing * i.toFloat, y')
  placed.mergeSort fun a b => pathLt (prefixPath a.1) (prefixPath b.1)

/-- The unshifted in-order layout. -/
def layout (worlds atoms : List String) : List (String × Float × Float) :=
  layoutWith 1 0 0 worlds atoms

/-- The layouts `arrange` tries, in order: (column order, bump, parity).
A straight chain 1 → 1.1 → 1.1.1 lies on one line when unshifted, so the
closure edge ⟨1, 1.1.1⟩ would run under world 1.1; lifting or dropping every
other column bends it. -/
def layoutShifts : List (Nat × Float × Nat) :=
  [1, 0].flatMap fun o => (o, 0, 0) ::
    ([0.5, 0.9, 1.3].flatMap fun b => [(o, b, 1), (o, -b, 1), (o, b, 0), (o, -b, 0)])

/-- An axis-aligned box `(x₀, y₀, x₁, y₁)`. -/
abbrev Box := Float × Float × Float × Float

def Box.overlaps (a b : Box) : Bool :=
  let (ax0, ay0, ax1, ay1) := a
  let (bx0, by0, bx1, by1) := b
  ax0 < bx1 && bx0 < ax1 && ay0 < by1 && by0 < ay1

def Box.inside (a : Box) (x0 y0 x1 y1 : Float) : Bool :=
  let (ax0, ay0, ax1, ay1) := a
  x0 ≤ ax0 && y0 ≤ ay0 && ax1 ≤ x1 && ay1 ≤ y1

/-- Approximate width of `s` in canvas units at `px` pixels (the canvas is
480 px for 10 units): 0.6 em per ASCII character and a full em for anything
else (□, ◇, →, …), which is on the wide side for both. -/
def textWidth (s : String) (px : Float) : Float :=
  s.toList.foldl (fun acc c => acc + (if c.toNat < 128 then 0.6 else 1.0) * px / 48) 0

/-- The world's circle and name, plus its self-loop if it has one, following
`render` (radius 0.42, loop 0.45 above the circle, name at 15px from
x − 0.22). -/
def worldBox (sc : Scenario) (w : String) (x y : Float) : Box :=
  let loop := if sc.edges.contains (w, w) then 0.45 else 0
  (x - 0.42, y - 0.42, max (x + 0.42) (x - 0.22 + textWidth w 15), y + 0.42 + loop)

/-- The fact list under a world when every atom holds there, following
`render` (12px from x − 0.9; lines 0.3 apart, the first 0.77 below the
center). -/
def factBox (sc : Scenario) (x y : Float) : Box :=
  let widest := ("(nothing)" :: sc.atoms).foldl (fun m a => max m (textWidth a 12)) 0
  let k := (factLines sc.atoms).toFloat
  (x - 0.9, y - 0.77 - 0.3 * (k - 1) - 0.1, x - 0.9 + widest, y - 0.77 + 0.25)

/-- Distance from point `c` to the segment `a`–`b`. -/
def segmentDistance (a b c : Float × Float) : Float :=
  let (ax, ay) := a
  let (bx, by_) := b
  let (cx, cy) := c
  let dx := bx - ax
  let dy := by_ - ay
  let len2 := dx * dx + dy * dy
  let t := if len2 < 1e-12 then 0 else max 0 (min 1 (((cx - ax) * dx + (cy - ay) * dy) / len2))
  let px := ax + t * dx - cx
  let py := ay + t * dy - cy
  Float.sqrt (px * px + py * py)

/-- No arrow passes through (or grazes, within 0.1) the circle of a world it
does not start or end at, so every edge of the relation is visible.
Self-loops are drawn above their own world and are not arrows. -/
def edgesClear (sc : Scenario) : Bool :=
  sc.edges.all fun (a, b) =>
    a == b ||
      match sc.worlds.lookup a, sc.worlds.lookup b with
      | some pa, some pb => sc.worlds.all fun (w, x, y) =>
          w == a || w == b || segmentDistance pa pb (x, y) > 0.42 + 0.1
      | _, _ => false

/-- The atom names fit in their chips (2.2 wide, label from 0.12, 13px). -/
def chipsFit (sc : Scenario) : Bool :=
  sc.atoms.length ≤ 4 && sc.atoms.all fun a => 0.12 + textWidth a 13 ≤ 2.2

/-- At most 6 check rows (y = 2.2 down to 0.3), each `✓  label   formula`
at 14px from x = 0.2 inside the 10-wide canvas. `render` draws the formula
too, so a long conclusion does not fit. -/
def checksFit (sc : Scenario) : Bool :=
  sc.checks.length ≤ 6 && sc.checks.all fun c =>
    0.2 + textWidth s!"✓  {c.label}   {c.formula}" 14 ≤ 10

/-- Does the scenario draw legibly: the chips and check rows fit, every
world at y ≥ 4.9 + 0.3 × facts, every world and fact list inside the canvas
(below the title), no two of them overlapping, and no arrow through a world
it does not end at? -/
def fitsCanvas (sc : Scenario) : Bool :=
  let boxes := sc.worlds.map fun (w, x, y) => (w, [worldBox sc w x y, factBox sc x y])
  chipsFit sc && checksFit sc
    && sc.worlds.all (fun (_, _, y) => y ≥ bottomRow sc.atoms - 1e-9)
    && boxes.all (fun (_, bs) => bs.all (·.inside 0 4.1 10 8.5))
    && (boxes.all fun (w, bs) => boxes.all fun (v, cs) =>
        w == v || bs.all fun b => cs.all fun c => !b.overlaps c)
    && edgesClear sc

/-- Place the scenario's worlds: the first of `layoutShifts` that
`fitsCanvas`, or the unshifted layout if none does (the model is then shown
as text). -/
def arrange (sc : Scenario) : Scenario :=
  let names := sc.worlds.map (·.1)
  let tries := layoutShifts.map fun (o, b, par) =>
    { sc with worlds := layoutWith o b par names sc.atoms }
  (tries.find? fitsCanvas).getD { sc with worlds := layout names sc.atoms }

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
  arrange
  { title := s!"{sys.name} countermodel (open branch {branch})"
    worlds := m.frame.worlds.toList.map (·, 0, 0)
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

/-! ## The open branch, line by line -/

/-- The K rule (B&D Table 6.1, p. 95, and Table 6.2, p. 96) that adds `pf`
when applied to `src`, if one does: its name, and for a branching rule the
signed formula on the other side of the split. -/
def ruleFor (src pf : PrefixedFormula) : Option (String × Option PrefixedFormula) :=
  let σ := src.pfx
  let here (s : Sign) (a : Formula) : Bool := pf.pfx == σ && pf.sign == s && pf.formula == a
  let child (s : Sign) (a : Formula) : Bool :=
    pf.pfx.isChildOf σ && pf.sign == s && pf.formula == a
  let stack (name : String) (ok : Bool) := if ok then some (name, none) else none
  let split (name : String) (l r : PrefixedFormula) : Option (String × Option PrefixedFormula) :=
    if pf == l then some (name, some r) else if pf == r then some (name, some l) else none
  match src.sign, src.formula with
  | .T, .not a => stack "¬T" (here .F a)
  | .F, .not a => stack "¬F" (here .T a)
  | .T, .and a b => stack "∧T" (here .T a || here .T b)
  | .F, .and a b => split "∧F" ⟨σ, .F, a⟩ ⟨σ, .F, b⟩
  | .T, .or a b => split "∨T" ⟨σ, .T, a⟩ ⟨σ, .T, b⟩
  | .F, .or a b => stack "∨F" (here .F a || here .F b)
  | .T, .implies a b => split "→T" ⟨σ, .F, a⟩ ⟨σ, .T, b⟩
  | .F, .implies a b => stack "→F" (here .T a || here .F b)
  | .T, .box a => stack "□T" (child .T a)
  | .F, .box a => stack "□F" (child .F a)
  | .T, .diamond a => stack "◇T" (child .T a)
  | .F, .diamond a => stack "◇F" (child .F a)
  | _, _ => none

/-- The branch as numbered lines in B&D's style: each signed formula with
the rule and line that produced it. For a split (∧F, ∨T, →T), say what the
other side added, and, when that contradicts an earlier line, that the
other side closes there. Rules outside Tables 6.1–6.2 (the extra rules of
KT, S4, …) show as "rule of {system}". -/
def branchLines (nAssumptions : Nat) (sysName : String) (b : Branch) : List String :=
  let fs := b.formulas.toList
  let flip : Sign → Sign := fun | .T => .F | .F => .T
  fs.zipIdx.map fun (pf, i) =>
    let why :=
      if i < nAssumptions then "assumption" else
      match (fs.take i).zipIdx.findSome? fun (src, j) => (ruleFor src pf).map (·, j) with
      | none => s!"rule of {sysName}"
      | some ((r, none), j) => s!"{r} {j + 1}"
      | some ((r, some alt), j) =>
        let clash := (fs.take i).zipIdx.find? fun (g, _) =>
          g.pfx == alt.pfx && g.formula == alt.formula && g.sign == flip alt.sign
        match clash with
        | some (_, k) => s!"{r} {j + 1}; the other side, {alt}, closes against line {k + 1}"
        | none => s!"{r} {j + 1}; the other side is {alt}"
    s!"{i + 1}. {pf}    ({why})"

/-- The lines of the open branch that `countermodelView` reads its model
off, or `[]` when there is none (valid, or unknown). -/
def openBranchLines (sys : System) (premises : List Formula) (conclusion : Formula)
    (maxSteps := defaultMaxSteps) : List String :=
  match buildTableau sys maxSteps (proofAssumptions premises conclusion) with
  | .stillOpen bs =>
    match firstVerified sys bs with
    | .ok (_, i) => match bs[i - 1]? with
      | some b => branchLines (premises.length + 1) sys.name b
      | none => []
    | .error _ => []
  | _ => []

/-- Did every branch close? -/
def CountermodelView.isValid : CountermodelView → Bool
  | .valid => true
  | _ => false

/-- Was a verified countermodel found? (Not the same as `!isValid`: an
`.unknown` verdict is neither.) -/
def CountermodelView.isCountermodel : CountermodelView → Bool
  | .countermodel .. => true
  | _ => false

/-- The verdict as a prediction answer: `some true` for valid, `some false`
for a verified countermodel, `none` for unknown. -/
def CountermodelView.verdict : CountermodelView → Option Bool
  | .valid => some true
  | .countermodel .. => some false
  | .unknown _ => none

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

/-- `#eval countermodelView …` shows the one-line summary. -/
instance : ToString CountermodelView := ⟨CountermodelView.summary⟩
instance : Repr CountermodelView := ⟨fun v _ => v.summary⟩

/-- Feedback for "is it valid?": `n` numbers the line, `hint` is shown only
after a wrong answer. -/
def gradeValidity (n : Nat) (prediction : Option Bool) (v : CountermodelView)
    (hint : String) : String :=
  match prediction, v.verdict with
  | none, _ => s!"{n}. Not answered yet: replace `none` with `some true` (valid) or \
      `some false` (not valid)."
  | some _, none => s!"{n}. The tableau could not decide ({v.summary})."
  | some p, some a =>
    if p == a then s!"{n}. ✓ Correct: {if a then "valid" else "not valid"}."
    else s!"{n}. ✗ Not quite. {hint}"

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

/-- `countermodelHtml` with the diagram drawn by `diagram`: the interactive
`kripkeExplorer` in notebooks, a static picture on the documentation site
(`kripkeStatic`, in `Widgets/StaticHtml.lean`). -/
def countermodelHtmlWith (diagram : Scenario → Html) (sys : System) (premises : List Formula)
    (conclusion : Formula) (maxSteps := defaultMaxSteps) : Html :=
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
      if fitsCanvas sc then diagram sc else countermodelText sc]

/-- The notebook entry point: `#html countermodelHtml systemK [] ml[ … ]`. -/
def countermodelHtml (sys : System) (premises : List Formula) (conclusion : Formula)
    (maxSteps := defaultMaxSteps) : Html :=
  countermodelHtmlWith kripkeExplorer sys premises conclusion maxSteps

/-- The open branch that the countermodel is read off, as a preformatted
block for `#html` (`openBranchLines`). -/
def openBranchHtml (sys : System) (premises : List Formula) (conclusion : Formula)
    (maxSteps := defaultMaxSteps) : Html :=
  match openBranchLines sys premises conclusion maxSteps with
  | [] => para "There is no open branch with a verified countermodel to show."
  | ls => Html.element "pre" #[] #[.text ("\n".intercalate ls)]

end Gamen.Widgets
