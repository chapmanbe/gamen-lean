import Gamen.ActionModel
import Gamen.Protocol

/-!
# Gamen.EpistemicJson

JSON codecs for `Gamen.Epistemic` models and `Gamen.ActionModel` action models,
used by the `epistemic_check` request of `gamen-validate` (`Validate/Epistemic.lean`).
Lean-only. Every failure is an `EpiSpecError`: a stable `code` and a message.

## Model

    { "worlds": ["w1", "w2"], "agents": ["a", "b"],
      "relations": { "a": [["w1","w2"], ["w2","w1"], ...] },   -- edges, any frame
      "indistinguishable": { "b": [["w1","w2"], ["w3"]] },     -- S5 classes (sugar)
      "valuation": { "w1": ["p"] } }                           -- world → true atoms

An agent may use `relations`, `indistinguishable`, or both (edges are united); an
agent in neither has no accessible worlds. In `indistinguishable`, a world in no class is
alone in its class, and a world in two classes is an `overlapping_classes` error. Every agent must be listed in `agents`.

## Action model

Either explicit

    { "events": ["a","a0"],
      "relations": { "i": [["a","a"],["a0","a0"]], ... },
      "pre": { "a": F }, "post": { "a": { "p": F } } }

Every agent of the model must appear in `relations` (with `[]` if it sees no event):
an omitted agent would silently know everything. Or a builder: `{"public_announcement": F}`,
`{"semi_private_whether": {"group": [...], "formula": F}}`,
`{"private_announcement": {"group": [...], "formula": F}}`. `F` are tree-format
formulas (`Gamen.Protocol.decodeFormula`).
-/
namespace Gamen

open Lean (Json)

structure EpiSpecError where
  code : String
  message : String

namespace EpistemicJson

private def err {α : Type} (code msg : String) : Except EpiSpecError α := .error ⟨code, msg⟩

private def lift {α : Type} (ctx : String) (r : Except String α) : Except EpiSpecError α :=
  r.mapError fun e => ⟨"malformed_spec", s!"{ctx}: {e}"⟩

private def getField (o : Json) (k ctx : String) : Except EpiSpecError Json :=
  match o.getObjVal? k with
  | .ok v => .ok v
  | .error _ => err "malformed_spec" s!"{ctx}: key \"{k}\" not found"

private def optObj (o : Json) (k : String) : Option Json :=
  (o.getObjVal? k).toOption.filter (· != Json.null)

private def strList (ctx : String) (j : Json) : Except EpiSpecError (List String) := do
  (← lift ctx j.getArr?).toList.mapM fun x => lift ctx x.getStr?

private def entries (ctx : String) (j : Json) : Except EpiSpecError (List (String × Json)) := do
  pure (← lift ctx j.getObj?).toList

private def pairs (ctx : String) (j : Json) : Except EpiSpecError (List (String × String)) := do
  (← lift ctx j.getArr?).toList.mapM fun e => do
    match ← strList ctx e with
    | [x, y] => pure (x, y)
    | _ => err "malformed_spec" s!"{ctx}: an edge must be a pair of two names"

private def formula (ctx : String) (j : Json) : Except EpiSpecError Formula :=
  (decodeFormula j).mapError fun e => ⟨"invalid_formula", s!"{ctx}: {e}"⟩

/-- Decode an epistemic model. -/
def decodeModel (j : Json) : Except EpiSpecError EpistemicModel := do
  let _ ← lift "model" j.getObj?
  let worlds ← strList "worlds" (← getField j "worlds" "model")
  let agents ← strList "agents" (← getField j "agents" "model")
  if let some w := worlds.find? (fun w => worlds.count w > 1) then
    throw ⟨"duplicate_world", s!"duplicate world \"{w}\""⟩
  if let some a := agents.find? (fun a => agents.count a > 1) then
    throw ⟨"duplicate_agent", s!"duplicate agent \"{a}\""⟩
  let knownW (ctx w : String) : Except EpiSpecError Unit :=
    if worlds.contains w then pure () else err "unknown_world" s!"{ctx}: unknown world \"{w}\""
  let knownA (ctx a : String) : Except EpiSpecError Unit :=
    if agents.contains a then pure () else err "unknown_agent" s!"{ctx}: unknown agent \"{a}\""
  let mut edges : List (String × List (World × World)) := agents.map (·, [])
  let addEdges (acc : List (String × List (World × World))) (a : String) (es : List (String × String)) :=
    acc.map fun (b, old) => if b == a then (b, old ++ es) else (b, old)
  if let some r := optObj j "relations" then
    for (a, es) in ← entries "relations" r do
      knownA "relations" a
      let ps ← pairs s!"relations[{a}]" es
      for (x, y) in ps do knownW s!"relations[{a}]" x; knownW s!"relations[{a}]" y
      edges := addEdges edges a ps
  if let some r := optObj j "indistinguishable" then
    for (a, cls) in ← entries "indistinguishable" r do
      knownA "indistinguishable" a
      let mut covered : List String := []
      for c in (← lift s!"indistinguishable[{a}]" cls.getArr?).toList do
        let ws ← strList s!"indistinguishable[{a}]" c
        if ws.isEmpty then
          throw ⟨"malformed_spec", s!"indistinguishable[{a}]: a class cannot be empty"⟩
        for w in ws do
          knownW s!"indistinguishable[{a}]" w
          if covered.contains w then
            throw ⟨"overlapping_classes", s!"indistinguishable[{a}]: world \"{w}\" is in more than one class"⟩
          covered := covered ++ [w]
        edges := addEdges edges a (ws.flatMap fun x => ws.map fun y => (x, y))
      -- a world in no class is alone in its class (as in the CGS spec), not unreachable
      edges := addEdges edges a ((worlds.filter (!covered.contains ·)).map fun w => (w, w))
  let mut vals : List (String × List World) := []
  if let some v := optObj j "valuation" then
    for (w, atoms) in ← entries "valuation" v do
      knownW "valuation" w
      for p in ← strList s!"valuation[{w}]" atoms do
        vals := match vals.find? (·.1 == p) with
          | some _ => vals.map fun (q, ws) => if q == p then (q, ws ++ [w]) else (q, ws)
          | none => vals ++ [(p, [w])]
  pure (mkEpistemicModel (mkEpistemicFrame worlds edges) vals)

/-- Decode an action model for `agents`; returns it with the default actual event
(`none` = choose the unique executable event at each world). -/
def decodeActionModel (agents : List String) (j : Json) :
    Except EpiSpecError (ActionModel × Option String) := do
  let wrap {α : Type} (r : Except String α) : Except EpiSpecError α :=
    r.mapError fun e => ⟨"invalid_action_model", e⟩
  let builders := ["public_announcement", "semi_private_whether", "private_announcement"].filter
    fun k => (optObj j k).isSome
  let explicit := ["events", "relations", "pre", "post"].filter fun k => (optObj j k).isSome
  if builders.length > 1 || (builders.length == 1 && !explicit.isEmpty) then
    throw ⟨"malformed_spec",
      s!"an action model is either one builder or explicit events/relations/pre/post, not a mix (got {builders ++ explicit})"⟩
  if let some f := optObj j "public_announcement" then
    return (← wrap (publicAnnouncement agents (← formula "public_announcement" f)), some "!")
  if let some b := optObj j "semi_private_whether" then
    let g ← strList "semi_private_whether.group" (← getField b "group" "semi_private_whether")
    let f ← formula "semi_private_whether" (← getField b "formula" "semi_private_whether")
    return (← wrap (semiPrivateWhether agents g f), none)
  if let some b := optObj j "private_announcement" then
    let g ← strList "private_announcement.group" (← getField b "group" "private_announcement")
    let f ← formula "private_announcement" (← getField b "formula" "private_announcement")
    return (← wrap (privateAnnouncement agents g f), some "!")
  let events ← strList "events" (← getField j "events" "action model")
  let mut rels : List (String × List (String × String)) := []
  if let some r := optObj j "relations" then
    for (a, es) in ← entries "relations" r do
      unless agents.contains a do
        throw ⟨"unknown_agent", s!"relations: unknown agent \"{a}\""⟩
      rels := rels ++ [(a, ← pairs s!"relations[{a}]" es)]
  -- an agent left out would silently see no events and so "know" everything
  if let some ag := agents.find? (fun ag => !rels.any (·.1 == ag)) then
    throw ⟨"invalid_action_model",
      s!"agent \"{ag}\" has no entry in relations (use [] if it sees nothing)"⟩
  let mut pre : List (String × Formula) := []
  if let some r := optObj j "pre" then
    for (e, f) in ← entries "pre" r do pre := pre ++ [(e, ← formula s!"pre[{e}]" f)]
  let mut post : List (String × List (String × Formula)) := []
  if let some r := optObj j "post" then
    for (e, ps) in ← entries "post" r do
      let mut row : List (String × Formula) := []
      for (p, f) in ← entries s!"post[{e}]" ps do row := row ++ [(p, ← formula s!"post[{e}][{p}]" f)]
      post := post ++ [(e, row)]
  pure (← wrap (mkActionModel events agents rels pre post), none)

end EpistemicJson
end Gamen
