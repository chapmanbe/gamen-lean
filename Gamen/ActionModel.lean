import Gamen.Epistemic

/-!
# Gamen.ActionModel

DEL action models and product update over `Gamen.Epistemic` models. Lean-only;
gamen-hs has no counterpart. Issue #3, item 3: with only public announcement
(`[B]C`, B&D Def 15.11) an announcement cannot be visible to a subset of the
agents; an action model can.

Sources: Lorini, Perrotin & Schwarzentruber, *Epistemic Actions: Comparing
Multi-agent Belief Bases with Action Models*, KR 2022, doi:10.24963/kr.2022/24:
epistemic model Def 6, action model Def 7 (events, per-agent relations,
preconditions `pre`, postconditions `post`), product `M × A` Def 8, truth of
`⟨A, a⟩φ` Def 9. Checked against the PDF in
`~/Projects/Logic/logic-notes/reference/dynamic-strategic-logics/pdfs/`. The
original is Baltag, Moss & Solecki 1998, not local, so not verified against it.
The belief-base half of that paper (ruby action models, Defs 10-11) is not ported.

## Design

* `ActionModel` is plain data; preconditions and postconditions are `Formula`s
  that `eSatisfies` can evaluate (propositional, `knowledge`, even `announce`).
  There is no `⟨A, a⟩` constructor in `Formula`: that would make `Formula` a
  nested inductive. `eSatisfiesAfter` (and `eSatisfiesBoxAfter`) is the
  function form; chain calls for nested dynamics.
* A missing precondition is `⊤`; a missing postcondition for an atom leaves the
  atom unchanged (identity, `post(e, p) = p`).
* Product worlds are named `w×e`. Two distinct world × event pairs with the same
  name are an error, never a silent merge (checked over all pairs, dead ones included).
* Errors, not defaults: an agent of the model with no relation in the action
  model, and a model with doxastic (`eDoxastic`) relations, are errors. The
  product updates the knowledge relations only, and silently dropping belief
  relations would turn a crash into a wrong answer.
* Agents are `String`s; events are `String`s.
-/
namespace Gamen

/-- An action model (Lorini et al. Def 7): events, per-agent relations over
events, preconditions, postconditions. -/
structure ActionModel where
  events : Std.TreeSet String
  /-- `agent → event → events the agent considers possible instead`. -/
  rel : Std.TreeMap String (Std.TreeMap String (Std.TreeSet String))
  /-- Missing event = `⊤`. -/
  pre : Std.TreeMap String Formula
  /-- `event → atom → new value`; a missing entry leaves the atom unchanged. -/
  post : Std.TreeMap String (Std.TreeMap String Formula)

/-- Build an action model, checking that it has an event and that every
relation edge, precondition and postcondition names a known event. Every agent
in `agents` must appear in `rels` (with `[]` if it sees no event): a forgotten agent
is an error, so that "sees nothing" is never confused with "forgotten". -/
def mkActionModel (events : List String) (agents : List String)
    (rels : List (String × List (String × String)))
    (pre : List (String × Formula) := [])
    (post : List (String × List (String × Formula)) := []) :
    Except String ActionModel := do
  if events.isEmpty then throw "mkActionModel: an action model needs at least one event"
  let evs := Std.TreeSet.ofList events
  let known (ctx e : String) : Except String Unit :=
    if evs.contains e then pure () else throw s!"mkActionModel: {ctx}: unknown event \"{e}\""
  for (ag, edges) in rels do
    unless agents.contains ag do throw s!"mkActionModel: relation for unknown agent \"{ag}\""
    for (e, e') in edges do known s!"relation of {ag}" e; known s!"relation of {ag}" e'
  -- an agent left out of `rels` would silently see no events and so "know" everything;
  -- one that sees nothing must say so with an empty edge list
  if let some ag := agents.find? (fun ag => !rels.any (·.1 == ag)) then
    throw s!"mkActionModel: agent \"{ag}\" has no relation (give [] if it sees no event)"
  for (e, _) in pre do known "precondition" e
  for (e, _) in post do known "postcondition" e
  let relMap := agents.foldl (init := (∅ : Std.TreeMap String (Std.TreeMap String (Std.TreeSet String))))
    fun acc ag =>
      let edges : List (String × String) := (rels.filter (·.1 == ag)).flatMap (·.2)
      acc.insert ag (edges.foldl (init := (∅ : Std.TreeMap String (Std.TreeSet String)))
        fun m p => m.insert p.1 ((m.getD p.1 ∅).insert p.2))
  pure { events := evs, rel := relMap
         pre := Std.TreeMap.ofList pre
         post := Std.TreeMap.ofList (post.map fun (e, ps) => (e, Std.TreeMap.ofList ps)) }

/-- `M, w ⊨ pre(e)`. -/
def ActionModel.executable (am : ActionModel) (m : EpistemicModel) (w : World) (e : String) :
    Except String Bool :=
  match am.pre.get? e with
  | none => pure true
  | some p => eSatisfies m w p

/-- The product `M × A` (Lorini et al. Def 8):
1. worlds `(w, e)` with `M, w ⊨ pre(e)`;
2. `(w, e) R'_a (w', e')` iff `w R_a w'` and `e R^A_a e'`;
3. `V'((w, e)) = {p | M, w ⊨ post(e, p)}`, with `post(e, p) = p` by default.

Worlds are named `w×e`. Errors: a model with doxastic relations, an agent with no
relation in `am`, a name collision between distinct pairs, or an error raised by a
pre/postcondition. -/
def productUpdate (m : EpistemicModel) (am : ActionModel) : Except String EpistemicModel := do
  unless m.eFrame.eDoxastic.isEmpty do
    throw "productUpdate: the model has doxastic relations, which the product does not update"
  for (ag, _) in m.eFrame.eRelations.toList do
    unless am.rel.contains ag do
      throw s!"productUpdate: agent \"{ag}\" has no relation in the action model"
  let name (w e : String) : String := w ++ "×" ++ e
  -- surviving pairs, in (world, event) order
  let mut pairs : List (World × String) := []
  for w in m.eFrame.eWorlds.toList do
    for e in am.events.toList do
      if ← am.executable m w e then pairs := pairs ++ [(w, e)]
  -- Distinct pairs must get distinct names, over *all* world × event pairs, not only the
  -- survivors: a pair that failed its precondition would otherwise still match a live name
  -- in the relation step below.
  let everyName := m.eFrame.eWorlds.toList.flatMap fun w => am.events.toList.map fun e => name w e
  if let some n := everyName.find? (fun n => everyName.count n > 1) then
    throw s!"productUpdate: two different (world, event) pairs are both named \"{n}\""
  let names := pairs.map fun (w, e) => name w e
  let alive := Std.TreeSet.ofList names
  -- relations
  let mut rels : Std.TreeMap String (Std.TreeMap World (Std.TreeSet World)) := ∅
  for (ag, wrel) in m.eFrame.eRelations.toList do
    let erel := am.rel.getD ag ∅
    let mut r : Std.TreeMap World (Std.TreeSet World) := ∅
    for (w, e) in pairs do
      let ws := wrel.getD w ∅
      let es := erel.getD e ∅
      let succs := ws.toList.flatMap fun w' => es.toList.filterMap fun e' =>
        if alive.contains (name w' e') then some (name w' e') else none
      r := r.insert (name w e) (Std.TreeSet.ofList succs)
    rels := rels.insert ag r
  -- valuation: every atom of the model, plus any a postcondition sets
  let postAtoms := am.post.toList.flatMap fun (_, ps) => ps.toList.map (·.1)
  let atoms := (m.eValuation.toList.map (·.1.name) ++ postAtoms).eraseDups
  let mut val : Std.TreeMap Atom (Std.TreeSet World) := ∅
  for p in atoms do
    let mut ws : List World := []
    for (w, e) in pairs do
      let holds ← match (am.post.getD e ∅).get? p with
        | some f => eSatisfies m w f
        | none => pure ((m.eValuation.getD ⟨p⟩ ∅).contains w)
      if holds then ws := name w e :: ws
    val := val.insert ⟨p⟩ (Std.TreeSet.ofList ws)
  pure { eFrame := { eWorlds := alive, eRelations := rels, eDoxastic := ∅ }
         eValuation := val }

/-- `M, w ⊨ ⟨A, e⟩φ` (Lorini et al. Def 9): `e` is executable at `w`, and `φ`
holds at `(w, e)` in `M × A`. -/
def eSatisfiesAfter (m : EpistemicModel) (w : World) (am : ActionModel) (e : String)
    (φ : Formula) : Except String Bool := do
  unless m.eFrame.eWorlds.contains w do
    throw s!"eSatisfiesAfter: world {repr w} is not in model"
  unless am.events.contains e do throw s!"eSatisfiesAfter: unknown event \"{e}\""
  if !(← am.executable m w e) then return false
  eSatisfies (← productUpdate m am) (w ++ "×" ++ e) φ

/-- `M, w ⊨ [A, e]φ`: if `e` is executable at `w`, `φ` holds after it. -/
def eSatisfiesBoxAfter (m : EpistemicModel) (w : World) (am : ActionModel) (e : String)
    (φ : Formula) : Except String Bool := do
  unless m.eFrame.eWorlds.contains w do
    throw s!"eSatisfiesBoxAfter: world {repr w} is not in model"
  unless am.events.contains e do throw s!"eSatisfiesBoxAfter: unknown event \"{e}\""
  if !(← am.executable m w e) then return true
  eSatisfies (← productUpdate m am) (w ++ "×" ++ e) φ

-- ── Common action models ─────────────────────────────────────────────────

/-- Public announcement of `φ` (event `"!"`): everyone sees it. The product is
`M|φ` with worlds renamed `w×!` (B&D Def 15.11). -/
def publicAnnouncement (agents : List String) (φ : Formula) : Except String ActionModel :=
  mkActionModel ["!"] agents (agents.map fun a => (a, [("!", "!")])) [("!", φ)]

/-- Semi-private announcement of whether `φ` to `group`: events `"φ"` (pre `φ`)
and `"¬φ"` (pre `¬φ`). Agents in `group` tell them apart; the others cannot, so
they learn nothing, but they know the group learned whether `φ`. -/
def semiPrivateWhether (agents group : List String) (φ : Formula) :
    Except String ActionModel := do
  if let some g := group.find? (!agents.contains ·) then
    throw s!"semiPrivateWhether: group member \"{g}\" is not an agent"
  let all := [("φ", "φ"), ("φ", "¬φ"), ("¬φ", "φ"), ("¬φ", "¬φ")]
  mkActionModel ["φ", "¬φ"] agents
    (agents.map fun a =>
      (a, if group.contains a then [("φ", "φ"), ("¬φ", "¬φ")] else all))
    [("φ", φ), ("¬φ", .not φ)]

/-- Private announcement of `φ` to `group` (event `"!"`, pre `φ`): the group sees
the announcement; every other agent believes nothing happened (event `"skip"`,
pre `⊤`). The actual event is `"!"`. -/
def privateAnnouncement (agents group : List String) (φ : Formula) :
    Except String ActionModel := do
  if let some g := group.find? (!agents.contains ·) then
    throw s!"privateAnnouncement: group member \"{g}\" is not an agent"
  mkActionModel ["!", "skip"] agents
    (agents.map fun a =>
      (a, if group.contains a then [("!", "!"), ("skip", "skip")]
          else [("!", "skip"), ("skip", "skip")]))
    [("!", φ)]

end Gamen
