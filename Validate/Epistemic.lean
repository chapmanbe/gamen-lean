import Gamen.EpistemicJson

/-!
# Validate.Epistemic

The Lean-only `epistemic_check` request of `gamen-validate` (protocol 5): evaluate
epistemic formulas on a model given as JSON, optionally after a sequence of DEL
action-model updates (`Gamen.ActionModel`). See `Validate.lean` for the wire format and
`Gamen.EpistemicJson` for the model and action-model specs. Outside `tools/compare`'s
scope: gamen-hs has no epistemic request.
-/
open Lean (Json toJson)
open Gamen

def epiErr (code msg : String) : Json :=
  Json.mkObj [("ok", false), ("error", toJson msg), ("error_code", toJson code)]

/-- Where an original world has got to after the updates so far: its name in the
current model, or `none` once some update was not executable there. -/
abbrev Track := List (String × Option String)

/-- The unique event executable at `w`, if any. More than one is an error: the
request must say which event happens. -/
private def autoEvent (m : EpistemicModel) (am : ActionModel) (w : String) :
    Except EpiSpecError (Option String) := do
  let runnable ← am.events.toList.filterM fun e =>
    (am.executable m w e).mapError fun msg => ⟨"update_failed", msg⟩
  match runnable with
  | [] => pure none
  | [e] => pure (some e)
  | es => throw ⟨"ambiguous_event",
      s!"world \"{w}\": events {es} are all executable; give the update an \"event\""⟩

/-- Apply one update (an action model, plus an optional `"event"`) to the model and
to every tracked world. -/
private def applyUpdate (m : EpistemicModel) (tr : Track) (u : Json) :
    Except EpiSpecError (EpistemicModel × Track) := do
  let agents := m.eFrame.eRelations.toList.map (·.1)
  let (am, dflt) ← EpistemicJson.decodeActionModel agents u
  let ev ← match (u.getObjVal? "event").toOption.filter (· != Json.null) with
    | none => pure dflt
    | some e => match e.getStr? with
      | .ok s => pure (some s)
      | .error msg => throw ⟨"malformed_spec", s!"event: {msg}"⟩
  if let some e := ev then
    unless am.events.contains e do throw ⟨"unknown_event", s!"unknown event \"{e}\""⟩
  let tr' ← tr.mapM fun (w, cur) => do
    match cur with
    | none => pure (w, none)
    | some cw =>
      let e? ← match ev with
        | some e => do
          let ok ← (am.executable m cw e).mapError fun msg => ⟨"update_failed", msg⟩
          pure (if ok then some e else none)
        | none => autoEvent m am cw
      pure (w, e?.map fun e => cw ++ "×" ++ e)
  let m' ← (productUpdate m am).mapError fun msg => ⟨"update_failed", msg⟩
  pure (m', tr')

/-- Answer an `epistemic_check` request. `worlds = none` reports every world. -/
def epistemicCheck (model : Json) (updates : List Json) (formulas : List Formula)
    (worlds : Option (List String)) : Json :=
  match EpistemicJson.decodeModel model with
  | .error e => epiErr e.code e.message
  | .ok m0 =>
    let all := m0.eFrame.eWorlds.toList
    let report := worlds.getD all
    match report.find? (fun w => !m0.eFrame.eWorlds.contains w) with
    | some w => epiErr "unknown_world" s!"worlds: unknown world \"{w}\""
    | none =>
      let run : Except EpiSpecError (EpistemicModel × Track) :=
        updates.foldlM (fun (m, tr) u => applyUpdate m tr u) (m0, report.map fun w => (w, some w))
      match run with
      | .error e => epiErr e.code e.message
      | .ok (m, tr) =>
        let cur (w : String) : Option String := (tr.find? (·.1 == w)).bind (·.2)
        let item (f : Formula) (i : Nat) : Json :=
          let base := [("index", toJson i), ("formula", toJson (toString f))]
          let rows : Except String (List (String × Bool × Bool)) := report.mapM fun w =>
            match cur w with
            | none => pure (w, false, false)            -- not executable
            | some cw => do pure (w, true, ← eSatisfies m cw f)
          match rows with
          | .error msg => Json.mkObj (base ++ [("error", toJson msg)])
          | .ok rs =>
            Json.mkObj (base ++ [
              ("satisfying", toJson (rs.filter (fun (_, _, h) => h) |>.map (·.1))),
              -- null where the update could not run: not "φ is false there"
              ("holds", Json.mkObj (rs.map fun (w, ex, h) => (w, if ex then toJson h else Json.null))),
              ("not_executable", toJson (rs.filter (fun (_, ex, _) => !ex) |>.map (·.1)))])
        Json.mkObj [("ok", true), ("result", Json.mkObj [
          ("worlds", toJson report), ("updates", toJson updates.length),
          ("results", Json.arr (formulas.zipIdx.map fun (f, i) => item f i).toArray)])]
