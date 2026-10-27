import Widgets.KripkeExplorer
import Widgets.Hint

/-!
# Static HTML for the documentation site

The documentation site (`tools/docs/render.py`) shows each notebook's `#html`
cells as plain HTML, since GitHub Pages cannot run the Lean server the
widgets talk to. `htmlToString` serializes a ProofWidgets `Html` value:

- elements and text directly, translating React attribute conventions to
  HTML (`className` → `class`, a `style` object → CSS, camelCase SVG
  attributes such as `strokeWidth` → `stroke-width`), and dropping event
  handlers and the explorer's `data` click payloads;
- a component node (an interactive widget) as a placeholder `div` naming
  its export, which the renderer replaces with a named note.

`kripkeStatic` is the Kripke explorer's starting picture as plain `Html`,
which the renderer substitutes for `kripkeExplorer` cells.
-/

open Lean ProofWidgets

namespace Gamen.Widgets

private def escapeText (s : String) : String :=
  s.foldl (init := "") fun acc c =>
    match c with
    | '&' => acc ++ "&amp;"
    | '<' => acc ++ "&lt;"
    | '>' => acc ++ "&gt;"
    | c => acc.push c

private def escapeAttr (s : String) : String :=
  (escapeText s).replace "\"" "&quot;"

/-- `strokeWidth` ↦ `stroke-width`. -/
private def kebab (s : String) : String :=
  s.foldl (init := "") fun acc c =>
    if c.isUpper then (acc.push '-').push c.toLower else acc.push c

/-- Attribute names SVG keeps in camelCase. -/
private def keepsCase (name : String) : Bool :=
  name == "viewBox" || name == "preserveAspectRatio"

private def htmlAttrName (name : String) : String :=
  if name == "className" then "class"
  else if keepsCase name then name
  else kebab name

/-- A JSON attribute value as attribute text: strings as-is, anything else
in its compact JSON form. -/
private def jsonText : Json → String
  | .str s => s
  | j => j.compress

/-- A React `style` object as a CSS declaration list. -/
private def styleText (j : Json) : String :=
  match j with
  | .obj kvs =>
    " ".intercalate <| kvs.foldl (init := []) fun acc k v =>
      acc ++ [s!"{kebab k}: {jsonText v};"]
  | j => jsonText j

private def dropped (name : String) : Bool :=
  name == "data" || name == "key" ||
    (name.startsWith "on" && (name.get? ⟨2⟩).any Char.isUpper)

private def attrText (name : String) (v : Json) : String :=
  if dropped name then ""
  else match v with
    | .bool true => s!" {htmlAttrName name}"
    | .bool false | .null => ""
    | v =>
      let text := if name == "style" then styleText v else jsonText v
      s!" {htmlAttrName name}=\"{escapeAttr text}\""

private def voidElements : List String := ["br", "hr", "img", "input", "meta", "link"]

/-- Serialize ProofWidgets `Html` to an HTML string (module docstring). -/
def htmlToString : Html → String
  | .text s => escapeText s
  | .element tag attrs children =>
    let open_ := "<" ++ tag ++ String.join (attrs.toList.map fun (k, v) => attrText k v) ++ ">"
    if voidElements.contains tag then open_
    else
      open_ ++ String.join (children.attach.toList.map fun ⟨c, _⟩ => htmlToString c)
        ++ "</" ++ tag ++ ">"
  | .component _ exp _ _ =>
    s!"<div class=\"widget-placeholder\" data-export=\"{escapeAttr exp}\"></div>"
termination_by h => sizeOf h
decreasing_by
  have := Array.sizeOf_lt_of_mem ‹_ ∈ children›
  simp_wf
  omega

/-- The Kripke explorer's starting picture, as plain `Html`, for the
documentation site's read-only notebook pages. -/
def kripkeStatic (sc : Scenario) : Html :=
  .element "div" #[("className", "kripke-static")] #[(initialResult sc).html]

end Gamen.Widgets
