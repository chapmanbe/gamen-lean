import ProofWidgets.Component.HtmlDisplay

/-!
# Collapsible hints

The Pluto notebooks' "Reveal answer" admonitions:

    #html hint "Reveal answer" "¬p: simply the negation of p."
-/
open ProofWidgets
open scoped ProofWidgets.Jsx

namespace Gamen.Widgets

def hint (summary answer : String) : Html :=
  <details>
    <summary>{.text summary}</summary>
    <p>{.text answer}</p>
  </details>

/-- Several hints in one panel, e.g. for a numbered practice list. -/
def hints (items : List (String × String)) : Html :=
  <div>{... (items.map fun (s, a) => hint s a).toArray}</div>

end Gamen.Widgets
