import ProofWidgets.Component.InteractiveSvg
import ProofWidgets.Component.HtmlDisplay
import Gamen.Protocol
import Gamen.Semantics

/-!
# Kripke explorer widget

A reusable, clickable Kripke-model diagram for the Lean teaching notebooks.
It replaces three Pluto patterns from the Gamen.jl notebooks:

* `visualize_model(model, positions = …)`: the diagram itself;
* `@bind x CheckBox()` per clinical fact per world: click an atom chip to
  select a fact, then click a world to toggle whether it holds there;
* a results table that recomputes on every change: each "check" formula is
  evaluated at `evalAt` by `Gamen.satisfies` on every click.

Everything is written in Lean on top of ProofWidgets' `InteractiveSvg`; the
only JavaScript is ProofWidgets' prebuilt component, vendored with its debug
line removed (`Widgets/js/make-quiet.sh`).

Usage in a notebook file:

    #html kripkeExplorer myScenario
-/
open Lean ProofWidgets Svg

namespace Gamen.Widgets

/-- A formula to evaluate and display, with a short label. -/
structure Check where
  label : String
  formula : Formula
  deriving ToJson, FromJson, Inhabited

/-- Everything the widget needs to draw and evaluate a model. Coordinates are
in a 10 × 9 drawing area (y points up). Each world's fact list hangs below
it, 0.3 per fact, starting 0.77 below the center; the fact chips occupy
y ≈ 3.1–4.1 and the check results y ≈ 0.3–2.6. So keep every world at
y ≥ 4.9 + 0.3 × (facts shown), e.g. y ≥ 5.8 for three facts. -/
structure Scenario where
  title : String
  /-- World name with its (x, y) position. -/
  worlds : List (String × Float × Float)
  edges : List (String × String)
  /-- Atoms whose valuation is shown (and, for editable worlds, toggled). -/
  atoms : List String
  /-- Worlds whose facts the student may toggle; `[]` makes a static diagram. -/
  editable : List String := []
  /-- The world at which the checks are evaluated. -/
  evalAt : String
  checks : List Check := []
  /-- Initial valuation: atom ↦ worlds where it holds. -/
  valuation : List (String × List String)
  deriving ToJson, FromJson, Inhabited

structure ExplorerState where
  scenario : Scenario
  valuation : List (String × List String)
  selectedAtom : Nat := 0
  deriving ToJson, FromJson, Inhabited

/-- The model currently shown (the scenario's frame plus the edited valuation). -/
def ExplorerState.model (s : ExplorerState) : Except String Model := do
  let fr ← mkFrame (s.scenario.worlds.map (·.1)) s.scenario.edges
  return mkModel fr s.valuation

def ExplorerState.holds (s : ExplorerState) (atom world : String) : Bool :=
  ((s.valuation.lookup atom).getD []).contains world

/-- Toggle `atom` at `world`, keeping every atom in the valuation list. -/
def ExplorerState.toggle (s : ExplorerState) (atom world : String) : ExplorerState :=
  let ws := (s.valuation.lookup atom).getD []
  let ws' := if ws.contains world then ws.erase world else ws ++ [world]
  let rest := s.valuation.filter (·.1 != atom)
  { s with valuation := rest ++ [(atom, ws')] }

/-! ## Drawing -/

def canvas : Svg.Frame := { xmin := 0, ymin := 0, xSize := 10, width := 480, height := 432 }

private def gray : Color := (0.55, 0.55, 0.55)
private def ink : Color := (0.12, 0.12, 0.12)
private def blue : Color := (0.20, 0.40, 0.75)
private def paleBlue : Color := (0.86, 0.91, 0.98)
private def paleGray : Color := (0.94, 0.94, 0.94)
private def green : Color := (0.10, 0.50, 0.20)
private def red : Color := (0.75, 0.15, 0.15)

private def worldRadius : Float := 0.42

/-- An arrow from `a` to `b`, trimmed to the circle edges, with a filled head. -/
def arrow (a b : Float × Float) : Array (Element canvas) :=
  let (x1, y1) := a
  let (x2, y2) := b
  let dx := x2 - x1
  let dy := y2 - y1
  let len := Float.sqrt (dx * dx + dy * dy)
  if len < 1e-6 then #[] else
  let ux := dx / len
  let uy := dy / len
  let sx := x1 + ux * worldRadius
  let sy := y1 + uy * worldRadius
  let ex := x2 - ux * worldRadius
  let ey := y2 - uy * worldRadius
  let head := 0.22
  let bx := ex - ux * head
  let byy := ey - uy * head
  let px := -uy * head * 0.5
  let py := ux * head * 0.5
  #[ Svg.line (.abs sx sy) (.abs bx byy) |>.setStroke gray (.px 2),
     Svg.polygon #[.abs ex ey, .abs (bx + px) (byy + py), .abs (bx - px) (byy - py)]
       |>.setFill gray ]

/-- A self-loop drawn as a small triangle path above the world. -/
def selfLoop (a : Float × Float) : Array (Element canvas) :=
  let (x, y) := a
  let top := y + worldRadius + 0.45
  #[ Svg.polyline #[.abs (x - 0.2) (y + worldRadius - 0.05), .abs (x - 0.25) top,
                    .abs (x + 0.25) top, .abs (x + 0.2) (y + worldRadius - 0.05)]
       |>.setStroke gray (.px 2) ]

def txt (x y : Float) (s : String) (size : Nat := 15) (c : Color := ink) : Element canvas :=
  Svg.text (.abs x y) s (.px size) |>.setFill c

def render (s : ExplorerState) : Svg canvas :=
  let sc := s.scenario
  let pos (w : String) : Float × Float := ((sc.worlds.lookup w).getD (0, 0))
  let edges := sc.edges.foldl (init := #[]) fun acc (a, b) =>
    acc ++ (if a == b then selfLoop (pos a) else arrow (pos a) (pos b))
  let worlds := sc.worlds.foldl (init := #[]) fun acc (w, x, y) =>
    let editable := sc.editable.contains w
    let facts := sc.atoms.filter (s.holds · w)
    let factLines := (if facts.isEmpty then ["(nothing)"] else facts).zipIdx.map
      fun (f, i) => txt (x - 0.9) (y - worldRadius - 0.35 - 0.3 * i.toFloat) f 12
        (if facts.isEmpty then gray else ink)
    acc.push (Svg.circle (.abs x y) (.abs worldRadius)
        |>.setFill (if editable then paleBlue else paleGray)
        |>.setStroke (if editable then blue else gray) (.px 2)
        |>.setId s!"world-{w}" |>.setData s!"w:{w}")
      |>.push (txt (x - 0.22) (y - 0.08) w 15 |>.setId s!"world-{w}-label" |>.setData s!"w:{w}")
      |>.append factLines.toArray
  let header := #[txt 0.2 8.7 sc.title 17]
  let chips := if sc.editable.isEmpty then #[] else
    let label := txt 0.2 3.95 "Select a fact, then click a blue world to toggle it:" 13 gray
    sc.atoms.zipIdx.foldl (init := #[label]) fun acc (a, i) =>
      let x := 0.2 + 2.4 * i.toFloat
      let sel := i == s.selectedAtom
      acc.push (Svg.rect (.abs x 3.6) (.abs 2.2) (.abs 0.5)
          |>.setFill (if sel then blue else paleGray)
          |>.setStroke blue (.px 1) |>.setId s!"atom-{i}" |>.setData s!"a:{i}")
        |>.push (txt (x + 0.12) 3.25 a 13 (if sel then (1.0, 1.0, 1.0) else ink)
          |>.setId s!"atom-{i}-label" |>.setData s!"a:{i}")
  let results := match s.model with
    | .error e => #[txt 0.2 2.2 s!"model error: {e}" 13 red]
    | .ok m =>
      let rows := sc.checks.zipIdx.map fun (c, i) =>
        let y := 2.2 - 0.38 * i.toFloat
        match satisfies m sc.evalAt c.formula with
        | .ok true => txt 0.2 y s!"✓  {c.label}   {c.formula}" 14 green
        | .ok false => txt 0.2 y s!"✗  {c.label}   {c.formula}" 14 red
        | .error e => txt 0.2 y s!"?  {c.label}: {e}" 14 red
      (if sc.checks.isEmpty then #[] else
        #[txt 0.2 2.6 s!"At {sc.evalAt}:" 14 gray]) ++ rows.toArray
  { elements := header ++ edges ++ worlds ++ chips ++ results }

/-- Click handling: `a:i` selects fact `i`; `w:name` toggles the selected
fact at an editable world. Every other event leaves the state unchanged.
Labels drawn on top of a shape carry the shape's data, so clicking the text
works too. -/
def handleClick (s : ExplorerState) (data : String) : ExplorerState :=
  match data.splitOn ":" with
  | ["a", i] => { s with selectedAtom := i.toNat?.getD s.selectedAtom }
  | ["w", w] =>
    if s.scenario.editable.contains w then
      match s.scenario.atoms[s.selectedAtom]? with
      | some a => s.toggle a w
      | none => s
    else s
  | _ => s

def explorer : InteractiveSvg ExplorerState where
  init := default
  frame := canvas
  -- React on mouse *up*: ProofWidgets records the pressed element as
  -- `selected` only after processing the mousedown event, so `getData` sees
  -- the clicked element at mouseup, not at mousedown.
  update _time _Δt action _mouseStart _mouseEnd _selected getData state :=
    match action.kind, getData String with
    | .mouseup, some d => handleClick state d
    | _, _ => state
  render _time _mouseStart _mouseEnd state := render state

end Gamen.Widgets

open Server RequestM Gamen.Widgets in
/-- The RPC method name is fixed by ProofWidgets' `interactiveSvg.js`, so it
must be exactly `updateSvg` at the root. Polling is switched off
(`callbackTime := none`): the widget only talks to the server on a click,
which matters when many students share one server. -/
@[server_rpc_method]
def updateSvg (params : UpdateParams ExplorerState) :
    RequestM (RequestTask (UpdateResult ExplorerState)) := do
  let task ← explorer.serverRpcMethod params
  return task.mapCheap (·.map fun r => { r with callbackTime := none })

namespace Gamen.Widgets

@[widget_module]
def KripkeExplorerWidget : Component (UpdateResult ExplorerState) where
  javascript := include_str "js" / "interactiveSvgQuiet.js"

/-- Initial widget contents for a scenario. -/
def initialResult (sc : Scenario) : UpdateResult ExplorerState :=
  let st : ExplorerState := { scenario := sc, valuation := sc.valuation }
  let svg := render st
  { html := svg.toHtml
    state := { state := st, time := 0, selected := none, mousePos := none
               idToData := svg.idToDataList }
    callbackTime := none }

/-- The HTML to pass to `#html`. -/
def kripkeExplorer (sc : Scenario) : Html :=
  let r := initialResult sc
  Html.ofComponent KripkeExplorerWidget r #[]

end Gamen.Widgets

namespace Gamen.Widgets

/-- The scenario's model as initially defined, so notebook `#eval` cells and
the diagram are built from one definition. A malformed scenario (an edge to
an unknown world) yields the empty model. -/
def Scenario.toModel (sc : Scenario) : Model :=
  match mkFrame (sc.worlds.map (·.1)) sc.edges with
  | .ok fr => mkModel fr sc.valuation
  | .error _ => default

end Gamen.Widgets
