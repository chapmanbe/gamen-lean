import Gamen.Protocol
import Gamen.EvidenceTrust

/-!
# Validate.EvidenceTrust

The Lean-only `evidence_trust_check` request of `gamen-validate` (protocol 8): model-check
DL-BET formulas (`Gamen.EvidenceTrust`; Liu & Lorini, PRIMA 2017) on an evidence source model
given as JSON. See `Validate.lean` for the wire format. gamen-hs has no such request.
-/
open Lean (Json toJson)
open Gamen Gamen.Protocol Gamen.EvidenceTrust

structure EtError where
  code : String
  message : String

instance : Inhabited EtError := ⟨⟨"", ""⟩⟩

namespace EtJson

def err (code msg : String) : EtError := ⟨code, msg⟩
private def malformed (msg : String) : EtError := err "malformed_spec" msg
private def lift {α} (r : Except String α) : Except EtError α := r.mapError malformed

def maxWorlds : Nat := 20
def maxAgents : Nat := 8
/-- Validation compares every evidence set with every trusted set, so the sets per entry are capped. -/
def maxSetsPerEntry : Nat := 2000

/-- Reject a key the request does not define (a misspelling would otherwise read as absent). -/
def onlyKeys (j : Json) (allowed : List String) (what : String) : Except EtError Unit :=
  match j with
  | .obj kvs =>
    match kvs.toList.find? (fun (k, _) => !allowed.contains k) with
    | some (k, _) => throw (malformed s!"{what}: unknown key \"{k}\" (expected one of {allowed})")
    | none => pure ()
  | _ => throw (malformed s!"{what} must be an object")

/-- An exact rational: `"1"`, `"3/4"`. -/
def parseRat (s : String) : Except EtError Rat :=
  match s.splitOn "/" with
  | [a] => match a.toNat? with
    | some n => pure (n : Rat)
    | none => throw (err "bad_rational" s!"\"{s}\" is not a rational (expected \"n\" or \"n/d\")")
  | [a, b] => match a.toNat?, b.toNat? with
    | some n, some d => if d == 0 then throw (err "bad_rational" s!"\"{s}\" has a zero denominator")
                        else pure ((n : Rat) / (d : Rat))
    | _, _ => throw (err "bad_rational" s!"\"{s}\" is not a rational (expected \"n\" or \"n/d\")")
  | _ => throw (err "bad_rational" s!"\"{s}\" is not a rational (expected \"n\" or \"n/d\")")

private def worldIdx (ws : Array String) (w : String) : Except EtError Nat :=
  match ws.findIdx? (· == w) with
  | some i => pure i
  | none => throw (err "unknown_world" s!"unknown world \"{w}\"")

private def agentIdx (ags : Array String) (a : String) : Except EtError Nat :=
  match ags.findIdx? (· == a) with
  | some i => pure i
  | none => throw (err "unknown_agent" s!"unknown agent \"{a}\"")

private def strList (j : Json) (what : String) : Except EtError (List String) :=
  lift (j.getArr? >>= fun a => a.toList.mapM (·.getStr?)) |>.mapError fun e => malformed s!"{what}: {e.message}"

private def maskOfNames (ws : Array String) (names : List String) : Except EtError Mask :=
  names.foldlM (fun acc n => do pure (acc ||| (1 <<< (← worldIdx ws n)))) 0

/-- `{agent: <value>}` entries, each key checked against the agents. -/
private def agentEntries (ags : Array String) (j : Json) (what : String) :
    Except EtError (List (Nat × Json)) := do
  match j with
  | .obj kvs => kvs.toList.mapM fun (k, v) => do pure (← agentIdx ags k, v)
  | _ => throw (malformed s!"{what} must be an object keyed by agent")

/-- Decode a model. Classes make C1, C4-C6 and C10 hold by construction; `validate` still runs. -/
def decodeModel (j : Json) : Except EtError (ESM × List String) := do
  onlyKeys j ["worlds", "agents", "valuation", "knowledge", "belief", "evidence", "trust", "types"] "model"
  let ws ← strList (← lift (field j "worlds")) "worlds"
  let ags ← strList (← lift (field j "agents")) "agents"
  if ws.length > maxWorlds then throw (err "bad_size" s!"at most {maxWorlds} worlds")
  if ags.length > maxAgents then throw (err "bad_size" s!"at most {maxAgents} agents")
  if ws.isEmpty || ags.isEmpty then throw (malformed "a model needs a world and an agent")
  if let some w := ws.find? (fun w => ws.count w > 1) then throw (err "duplicate_world" s!"duplicate world \"{w}\"")
  if let some a := ags.find? (fun a => ags.count a > 1) then throw (err "duplicate_agent" s!"duplicate agent \"{a}\"")
  let wa := ws.toArray
  let aa := ags.toArray
  let n := ws.length
  let na := ags.length
  -- valuation
  let valuation ← match ← lift (optField j "valuation") with
    | none => pure (Array.replicate n ([] : List String))
    | some (.obj kvs) =>
      let mut v := Array.replicate n ([] : List String)
      for (w, atoms) in kvs.toList do
        v := v.set! (← worldIdx wa w) (← strList atoms s!"valuation of {w}")
      pure v
    | some _ => throw (malformed "valuation must be an object")
  -- knowledge classes: E i w
  let mut E : Array (Array Mask) := Array.replicate na (Array.ofFn (n := n) fun w => (1 <<< w.val))
  -- knowledge is required for every agent: an agent with no entry would silently know everything
  let kj ← lift (field j "knowledge")
  let mut kSeen : List Nat := []
  for (i, cj) in ← agentEntries aa kj "knowledge" do
    kSeen := i :: kSeen
    let mut row := Array.ofFn (n := n) fun w => (1 <<< w.val)
    let mut seen : Mask := 0
    for cls in (← lift cj.getArr?).toList do
      let mask ← maskOfNames wa (← strList cls "a knowledge class")
      if seen &&& mask != 0 then throw (err "overlapping_classes" s!"agent {aa[i]!}: classes overlap")
      seen := seen ||| mask
      for w in List.range n do
        if mask.testBit w then row := row.set! w mask
    E := E.set! i row
  for i in List.range na do
    unless kSeen.contains i do
      throw (malformed s!"knowledge: no entry for agent {aa[i]!} (give [] for an agent who knows the actual world)")
  let classMask (i : Nat) (w : Nat) : Mask := E[i]![w]!
  -- belief: required for every class of every agent
  let mut D : Array (Array Mask) := Array.replicate na (Array.replicate n 0)
  let beliefJ ← lift (field j "belief")
  let mut beliefSeen : List (Nat × Mask) := []
  for (i, bj) in ← agentEntries aa beliefJ "belief" do
    for entry in (← lift bj.getArr?).toList do
      onlyKeys entry ["class", "worlds"] "a belief entry"
      let c ← worldIdx wa (← lift (strField entry "class"))
      let b ← maskOfNames wa (← strList (← lift (field entry "worlds")) "belief worlds")
      let k := classMask i c
      if beliefSeen.contains (i, k) then throw (malformed s!"belief: agent {aa[i]!} has two entries for one class")
      beliefSeen := (i, k) :: beliefSeen
      for w in List.range n do
        if k.testBit w then D := D.modify i (·.set! w b)
  for i in List.range na do
    for w in List.range n do
      unless beliefSeen.contains (i, classMask i w) do
        throw (malformed s!"belief: no entry for agent {aa[i]!} at the class of world {wa[w]!}")
  -- evidence and trust: agent → source → [{class, sets}]
  let decodeSets (field : String) : Except EtError (Array (Array (Array Sets))) := do
    let mut tab : Array (Array (Array Sets)) := Array.replicate na (Array.replicate na (Array.replicate n []))
    match ← lift (optField j field) with
    | none => pure tab
    | some tj =>
      for (i, srcs) in ← agentEntries aa tj field do
        for (k, entries) in ← agentEntries aa srcs field do
          let mut done : List Mask := []
          for entry in (← lift entries.getArr?).toList do
            onlyKeys entry ["class", "sets"] s!"a {field} entry"
            let c ← worldIdx wa (← lift (strField entry "class"))
            let setsJ ← lift (← lift (Gamen.Protocol.field entry "sets")).getArr?
            if setsJ.size > maxSetsPerEntry then
              throw (err "bad_size" s!"{field}: at most {maxSetsPerEntry} sets per entry")
            let sets ← setsJ.toList.mapM fun sj => do
              maskOfNames wa (← strList sj s!"a {field} set")
            let km := classMask i c
            if done.contains km then throw (malformed s!"{field}: two entries for one class")
            done := km :: done
            let norm := Sets.ofList sets
            for w in List.range n do
              if km.testBit w then tab := tab.modify i (·.modify k (·.set! w norm))
      pure tab
  let S ← decodeSets "evidence"
  let C ← decodeSets "trust"
  -- types
  let typesJ ← lift (field j "types")
  let mut T : Array (Array (Nat × Rat)) := Array.replicate na (Array.replicate n (0, 1))
  let mut typed : List Nat := []
  for (i, tj) in ← agentEntries aa typesJ "types" do
    match (← lift tj.getArr?).toList with
    | [xj, yj] =>
      let x ← match xj.getNat? with
        | .ok x => pure x
        | .error _ => throw (malformed s!"types: cautiousness of {aa[i]!} must be a non-negative integer")
      let y ← parseRat (← lift yj.getStr?)
      T := T.set! i (Array.replicate n (x, y))
      typed := i :: typed
    | _ => throw (malformed s!"types: {aa[i]!} must be [cautiousness, \"quota\"]")
  for i in List.range na do
    unless typed.contains i do throw (malformed s!"types: no type for agent {aa[i]!}")
  let m : ESM := { n, agents := aa, valuation, E, D, S, C, T }
  match m.validate with
  | .ok () => pure (m, ws)
  | .error msg =>
    let code := if msg.startsWith "bad_type" then "bad_type"
      else if msg.startsWith "C" then s!"violates_{(msg.takeWhile (· != ':')).toString}"
      else "malformed_spec"
    throw (err code msg)

/-- Formulas, as tree-format JSON; agents by name. -/
partial def decodeFormula (ags : Array String) (j : Json) : Except EtError EFormula := do
  let ty ← lift (strField j "type")
  let allowed := match ty with
    | "atom" => ["name"]
    | "not" | "knowledge" | "belief" | "reason" => ["operand"] ++ (if ty == "not" then [] else ["agent"])
    | "and" | "or" | "implies" => ["left", "right"]
    | "type" => ["agent", "x", "y"]
    | "evidence" | "trust" => ["agent", "source", "operand"]
    | "announce" | "assess" => ["agent", "operand", "then"]
    | "lose_trust" | "rely_on" => ["agent", "source", "operand", "then"]
    | _ => []
  onlyKeys j (["type"] ++ allowed) s!"formula \"{ty}\""
  let sub (k : String) : Except EtError EFormula := do decodeFormula ags (← lift (field j k))
  let ag (k : String := "agent") : Except EtError Nat := do agentIdx ags (← lift (strField j k))
  match ty with
  | "atom" => return .atom (← lift (strField j "name"))
  | "bot" => return .bot
  | "top" => return EFormula.top
  | "not" => return .not (← sub "operand")
  | "and" => return .and (← sub "left") (← sub "right")
  | "or" => return EFormula.or (← sub "left") (← sub "right")
  | "implies" => return EFormula.implies (← sub "left") (← sub "right")
  | "type" =>
    let x ← match (← lift (field j "x")).getNat? with
      | .ok x => pure x
      | .error _ => throw (malformed "type: x must be a non-negative integer")
    let y ← parseRat (← lift (strField j "y"))
    if x > ags.size then throw (err "bad_type" s!"type: cautiousness {x} exceeds the number of agents")
    if y < (1 : Rat) / 2 || y > 1 then throw (err "bad_type" s!"type: quota {y} is outside [1/2, 1]")
    return .type (← ag) x y
  | "knowledge" => return .knows (← ag) (← sub "operand")
  | "belief" => return .believes (← ag) (← sub "operand")
  | "reason" => return .reason (← ag) (← sub "operand")
  | "evidence" => return .evidence (← ag) (← ag "source") (← sub "operand")
  | "trust" => return .trust (← ag) (← ag "source") (← sub "operand")
  | "announce" => return .announce (← ag) (← sub "operand") (← sub "then")
  | "assess" => return .assess (← ag) (← sub "operand") (← sub "then")
  | "lose_trust" => return .loseTrust (← ag) (← ag "source") (← sub "operand") (← sub "then")
  | "rely_on" => return .relyOn (← ag) (← ag "source") (← sub "operand") (← sub "then")
  | other => throw (malformed s!"Unknown formula type: {other}")

end EtJson

def etErr (e : EtError) : Json :=
  Json.mkObj [("ok", false), ("error", toJson e.message), ("error_code", toJson e.code)]

/-- Answer an `evidence_trust_check` request. `worlds = none` reports every world. -/
def evidenceTrustCheck (model : Json) (formulas : List Json) (worlds : Option (List String)) : Json :=
  match EtJson.decodeModel model with
  | .error e => etErr e
  | .ok (m, names) =>
    let report := worlds.getD names
    match report.find? (fun w => !names.contains w) with
    | some w => etErr ⟨"unknown_world", s!"worlds: unknown world \"{w}\""⟩
    | none =>
    match report.find? (fun w => report.count w > 1) with
    | some w => etErr ⟨"malformed_spec", s!"worlds: \"{w}\" is listed more than once"⟩
    | none =>
      let idx (w : String) : Nat := (names.findIdx? (· == w)).getD 0
      let item (fj : Json) (i : Nat) : Json :=
        let base := [("index", toJson i)]
        match EtJson.decodeFormula m.agents fj with
        | .error e => Json.mkObj (base ++ [("error", toJson e.message), ("error_code", toJson e.code)])
        | .ok f =>
          match sat m f with
          | .error msg => Json.mkObj (base ++ [("error", toJson msg), ("error_code", "check_failed")])
          | .ok mask =>
            let holds (w : String) := mask.testBit (idx w)
            Json.mkObj (base ++ [
              ("satisfying", toJson (report.filter holds)),
              ("holds", Json.mkObj (report.map fun w => (w, toJson (holds w)))),
              ("true_in_model", toJson (mask == Mask.full m.n))])
      Json.mkObj [("ok", true), ("result", Json.mkObj [
        ("worlds", toJson report),
        ("results", Json.arr (formulas.zipIdx.map fun (f, i) => item f i).toArray)])]
