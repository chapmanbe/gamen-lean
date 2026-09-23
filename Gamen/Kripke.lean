import Std.Data.TreeMap
import Gamen.Formula

/-!
# Gamen.Kripke

Port of `gamen-hs/src/Gamen/Kripke.hs` (B&D Definition 1.6):
Kripke frames and models over string-named worlds.
-/
namespace Gamen

abbrev World := String

/-- The ⟨W, R⟩ part of a model (B&D Definition 1.6; frames proper are
Chapter 2): a set of worlds plus an accessibility relation, stored as a
successor map. -/
structure Frame where
  worlds : Std.TreeSet World
  relation : Std.TreeMap World (Std.TreeSet World)
  deriving Inhabited

/-- B&D Definition 1.6: a model ⟨W, R, V⟩ is a frame plus a valuation. -/
structure Model where
  frame : Frame
  valuation : Std.TreeMap Atom (Std.TreeSet World)
  deriving Inhabited

/-- Worlds accessible from `w`. -/
def Frame.accessible (fr : Frame) (w : World) : Std.TreeSet World :=
  fr.relation.getD w ∅

/-- Build a frame from world names and edges. Haskell calls `error` on an
edge whose endpoint is outside the world set; here that is an `Except`. -/
def mkFrame (ws : List World) (rels : List (World × World)) : Except String Frame := do
  let worldSet := Std.TreeSet.ofList ws
  for (src, dst) in rels do
    unless worldSet.contains src && worldSet.contains dst do
      throw s!"mkFrame: edge ({src} -> {dst}) has an endpoint outside the world set"
  let relation := rels.foldl
    (fun m (src, dst) => m.insert src ((m.getD src ∅).insert dst)) ∅
  return { worlds := worldSet, relation }

/-- Build a model from a frame and `(atomName, worlds)` pairs. -/
def mkModel (fr : Frame) (vals : List (String × List World)) : Model :=
  { frame := fr
    valuation := Std.TreeMap.ofList
      (vals.map fun (n, ws) => ((⟨n⟩ : Atom), Std.TreeSet.ofList ws)) }

end Gamen
