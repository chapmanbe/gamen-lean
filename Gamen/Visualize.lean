import Gamen.Formula
import Gamen.Kripke

/-!
# Gamen.Visualize

Port of `gamen-hs/src/Gamen/Visualize.hs`: render Kripke frames and models
as Graphviz `dot` source.

The notebook build pipeline pipes the output through `dot -Tsvg` to produce
a figure that gets embedded in the rendered Markdown. The functions here
are pure: they take a `Frame` or `Model` and return a `String` of `dot`
source. Any I/O (writing the file, calling `dot`) is the caller's job.

Conventions:

* Worlds are circular nodes labeled with the world name.
* Names are written unquoted and unescaped, as in gamen-hs. A world or atom
  name that isn't a bare DOT identifier gives invalid DOT, and a tableau
  prefix such as `1.2.1` is silently misread by Graphviz as `1.2`. This is
  filed as gamen-hs#55 and copied until it is fixed there.
* For `Model`, each node label also lists the atoms holding at that world,
  on a second line.
* Edges are directed (the accessibility relation is binary, not necessarily
  symmetric).
* Default layout is left-to-right (`rankdir=LR`); override by editing the
  produced source.

gamen-hs has no tests for this module (`grep -rlw toGraphviz test/*.hs`
and the same for `toGraphvizModel` both return nothing, and it is absent
from `test/PaperCorrespondence.hs`). `visualizeCases` in `Tests/Main.lean`
is therefore checked against `cabal repl`'s output directly rather than a
ported spec; see that section's docstring for the transcript.
-/
namespace Gamen

/-- Common `dot` scaffolding shared by `toGraphviz` and `toGraphvizModel`.
Caller supplies the (already-sorted, per `Std.TreeSet`/`Std.TreeMap`
iteration order) node list, the edge list, and a function that produces
the `dot` statement for each node. -/
private def render (nodes : List World) (edges : List (World × World))
    (nodeStmt : World → String) : String :=
  let lines :=
    [ "digraph K {"
    , "  rankdir=LR;"
    , "  bgcolor=\"transparent\";"
    , "  node [shape=circle, fontname=\"et-book, Palatino, serif\","
        ++ " fontsize=12, color=\"#111\", fontcolor=\"#111\"];"
    , "  edge [color=\"#555\", arrowsize=0.7];"
    ]
    ++ nodes.map (fun w => "  " ++ nodeStmt w)
    ++ edges.map (fun (src, dst) => "  " ++ src ++ " -> " ++ dst ++ ";")
    ++ ["}"]
  -- Haskell's `unlines` appends a trailing `\n` after every line, including
  -- the last.
  String.join (lines.map (· ++ "\n"))

/-- Render a `Frame` (just structure, no valuation) as `dot` source. -/
def toGraphviz (fr : Frame) : String :=
  let edges := fr.relation.toList.flatMap fun (w, us) => us.toList.map fun u => (w, u)
  render fr.worlds.toList edges (fun w => w ++ " [label=\"" ++ w ++ "\"];")

/-- Render a `Model` as `dot` source. Each world's label includes the
atoms holding there, separated from the world name by a literal `\n`
(rendered as a line break by Graphviz, not a Lean/Haskell newline). -/
def toGraphvizModel (m : Model) : String :=
  let edges :=
    m.frame.relation.toList.flatMap fun (w, us) => us.toList.map fun u => (w, u)
  let atomsAt (w : World) : List String :=
    (m.valuation.toList.filterMap fun (a, ws) => if ws.contains w then some a.name else none)
      |>.mergeSort (· ≤ ·)
  let modelNode (w : World) : String :=
    let as := atomsAt w
    let atomLine := if as.isEmpty then "" else "\\n" ++ ", ".intercalate as
    w ++ " [label=\"" ++ w ++ atomLine ++ "\"];"
  render m.frame.worlds.toList edges modelNode

end Gamen
