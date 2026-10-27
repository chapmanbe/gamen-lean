import Gamen.Teaching
import Widgets.StaticHtml
import Widgets.Countermodel

/-!
# Tests for `Widgets/StaticHtml.lean`

The serializer that turns a notebook's `#html` value into plain HTML for the
documentation site (`tools/docs/render.py`). Plan:
`docs/superpowers/plans/2026-10-27-documentation-site.md`, Task 4.
-/

namespace StaticHtmlTests

open Lean ProofWidgets Gamen Gamen.Widgets

private def has (s sub : String) : Bool := (s.splitOn sub).length > 1

private def twoWorlds : Scenario where
  title := "two worlds"
  worlds := [("u1", 1.0, 5.0), ("u2", 5.0, 5.0)]
  edges := [("u1", "u2")]
  atoms := ["p"]
  evalAt := "u1"
  valuation := [("p", ["u2"])]

def cases : List (String × Bool) := [
  ("static html: text is escaped",
    htmlToString (.text "a < b & c") == "a &lt; b &amp; c"),
  ("static html: hint is a closed details element",
    htmlToString (hint "S" "A") == "<details><summary>S</summary><p>A</p></details>"),
  ("static html: svg attrs: strokeWidth becomes stroke-width, data is dropped",
    let s := htmlToString (.element "line"
      #[("strokeWidth", (2 : Nat)), ("data", "w1"), ("stroke", "rgb(0,0,0)")] #[])
    has s "stroke-width=\"2\"" && has s "stroke=\"rgb(0,0,0)\"" && !has s "data="),
  ("static html: viewBox keeps its case",
    has (htmlToString (.element "svg" #[("viewBox", "0 0 10 10")] #[])) "viewBox=\"0 0 10 10\""),
  ("static html: className becomes class, style object becomes CSS",
    htmlToString (.element "div"
      #[("className", "x"), ("style", Json.mkObj [("fontSize", "12px")])] #[])
      == "<div class=\"x\" style=\"font-size: 12px;\"></div>"),
  ("static html: event handlers and false booleans are dropped, true is bare",
    htmlToString (.element "input"
      #[("onClick", "f"), ("disabled", true), ("hidden", false)] #[])
      == "<input disabled>"),
  ("static html: attribute values are escaped",
    has (htmlToString (.element "a" #[("title", "say \"hi\" & <go>")] #[]))
      "title=\"say &quot;hi&quot; &amp; &lt;go&gt;\""),
  ("static html: component becomes a placeholder",
    has (htmlToString (kripkeExplorer twoWorlds)) "class=\"widget-placeholder\""),
  ("static html: kripkeStatic draws an svg with every world",
    let s := htmlToString (kripkeStatic twoWorlds)
    s.startsWith "<div class=\"kripke-static\">" && has s "<svg" && has s "u1" && has s "u2"),
  ("static html: countermodelStatic draws the embedded explorer, no placeholder",
    let s := htmlToString (countermodelStatic systemK [] ml[ □p → p ])
    has s "kripke-static" && has s "<svg" && !has s "widget-placeholder"),
  ("static html: countermodelStatic agrees with countermodelHtml outside the diagram",
    let a := htmlToString (countermodelStatic systemK [] ml[ □p → □□p ])
    let b := htmlToString (countermodelHtml systemK [] ml[ □p → □□p ])
    (a.splitOn "<div class=\"kripke-static\">").head! == (b.splitOn "<div class=\"widget-placeholder\"").head!)
]

end StaticHtmlTests
