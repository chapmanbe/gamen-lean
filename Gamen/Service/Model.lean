import Gamen.Dcleg
import Gamen.Service.Protocol

/-!
# Gamen.Service.Model

Port of `gamen-hs/protocol/Service/Model.hs`: decode a DCLEG model from the
JSON of `notes/dcleg-service-protocol.md` §3 (in gamen-hs), validate it, and
apply the default premise function. Only the §3 `"auto"` premises form is
supported, as in gamen-hs v0.1.

**One deliberate divergence from gamen-hs**, in what `build` accepts. The
Haskell runs the library's `validateDclegModel` on the model *before*
premises are added. Lean's `validateDclegModel` also checks that the premise
function is admissible (Centering and Contemporary Universality, DCLEG
§3.2.2, p. 19), which no premise-free model passes, so here it runs on the
model *after* `withMovePremises`. Its other checks don't look at premises,
so their messages are unchanged. The premise checks fail only when a
history disagrees with the strategic structure (a world plays a move that
`moves` doesn't list, or stops at a vertex that is neither an end node nor
followed by a move); gamen-hs builds such models, and then answers
counterfactuals over a premise function the thesis does not allow.
Recorded in `tools/compare/intentional-divergences.md` (dcleg-service D3).
-/

namespace Gamen.Service
open Lean (Json toJson)
open Dcleg

-- Pairs as keys: Lean core has no global `Ord (α × β)` (see `Tableau.lean`).
attribute [local instance] lexOrd

/-! ## JSON helper types (mirror the §3 wire format) -/

structure StrucJSON where
  sjNodes : List String
  sjEndNodes : List String
  sjPlayer : List (String × String)
  sjMoves : List (String × List String)
  sjNext : List (String × String × String)

structure HistJSON where
  hjWorld : String
  /-- (vertex, move) pairs -/
  hjMoves : List (String × String)
  hjEnd : String

structure ValJSON where
  vjProp : String
  /-- (world, vertex) pairs -/
  vjPairs : List (String × String)

structure WorldSuccJSON where
  wsWorld : String
  wsSuccessors : List String

structure DoxVertexJSON where
  dvVertex : String
  dvWorlds : List WorldSuccJSON

structure DoxAgentJSON where
  daAgent : String
  daEntries : List DoxVertexJSON

structure PayoffJSON where
  payAgent : String
  /-- (vertex, payoff) pairs -/
  payEntries : List (String × Int)

structure ModelJSON where
  mjStructure : StrucJSON
  mjWorlds : List String
  mjHistories : List HistJSON
  mjValuation : List ValJSON
  mjDoxastic : List DoxAgentJSON
  mjPayoff : List PayoffJSON
  mjPremises : Json

/-- The `FromJSON` instances of `Service/Model.hs`, fields in the order the
Haskell parses them, so the first failure reported is the same one. -/
def parseStruc (j : Json) : Except String StrucJSON :=
  withObject "strategic_structure" j fun o => do
    let ns ← reqField o "nodes" (parseList parseString)
    let ends ← reqField o "end_nodes" (parseList parseString)
    let pl ← reqField o "player" (parseList (parsePair parseString parseString))
    let mv ← reqField o "moves" (parseList (parsePair parseString (parseList parseString)))
    let nx ← reqField o "next" (parseList (parseTriple parseString parseString parseString))
    return ⟨ns, ends, pl, mv, nx⟩

def parseHist (j : Json) : Except String HistJSON :=
  withObject "history" j fun o => do
    let w ← reqField o "world" parseString
    let ms ← reqField o "moves" (parseList (parsePair parseString parseString))
    let e ← reqField o "end" parseString
    return ⟨w, ms, e⟩

def parseVal (j : Json) : Except String ValJSON :=
  withObject "valuation_entry" j fun o => do
    let p ← reqField o "prop" parseString
    return ⟨p, ← reqField o "pairs" (parseList (parsePair parseString parseString))⟩

def parseWorldSucc (j : Json) : Except String WorldSuccJSON :=
  withObject "world_succ_entry" j fun o => do
    let w ← reqField o "world" parseString
    return ⟨w, ← reqField o "successors" (parseList parseString)⟩

def parseDoxVertex (j : Json) : Except String DoxVertexJSON :=
  withObject "dox_vertex_entry" j fun o => do
    let v ← reqField o "vertex" parseString
    return ⟨v, ← reqField o "worlds" (parseList parseWorldSucc)⟩

def parseDoxAgent (j : Json) : Except String DoxAgentJSON :=
  withObject "dox_agent_entry" j fun o => do
    let a ← reqField o "agent" parseString
    return ⟨a, ← reqField o "entries" (parseList parseDoxVertex)⟩

def parsePayoff (j : Json) : Except String PayoffJSON :=
  withObject "payoff_entry" j fun o => do
    let a ← reqField o "agent" parseString
    return ⟨a, ← reqField o "entries" (parseList (parsePair parseString parseInt))⟩

def parseModelJSON (j : Json) : Except String ModelJSON :=
  withObject "model" j fun o => do
    let s ← reqField o "strategic_structure" parseStruc
    let ws ← reqField o "worlds" (parseList parseString)
    let hs ← reqField o "histories" (parseList parseHist)
    let val ← optField o "valuation" (parseList parseVal) []
    let dox ← optField o "doxastic" (parseList parseDoxAgent) []
    let pay ← optField o "payoff" (parseList parsePayoff) []
    let prem ← optField o "premises" pure (Json.str "auto")
    return ⟨s, ws, hs, val, dox, pay, prem⟩

/-! ## Entry point -/

/-- Why a build request could not be turned into a model: a feature the
service does not implement (`unsupported`, with a label and machine-readable
details), or a model that fails validation. -/
inductive BuildError where
  /-- feature label + machine-readable details -/
  | buildUnsupported (feature : String) (details : Json)
  /-- structural / referential validation violations -/
  | buildInvalid (violations : List String)

/-! ## Structural validation (§3 "Validation on build") -/

def checkEndNodesSubset (m : DclegModel) : List String :=
  let ss := m.dmStructure
  ss.ssEndNodes.toList.filter (!ss.ssNodes.contains ·) |>.map ("end_node not in nodes: " ++ ·)

def checkPlayerDefined (m : DclegModel) : List String :=
  let ss := m.dmStructure
  let nonEnds := ss.ssNodes.toList.filter (!ss.ssEndNodes.contains ·)
  (nonEnds.filter (!ss.ssPlayer.contains ·) |>.map ("player undefined at non-end node: " ++ ·))
  ++ (ss.ssEndNodes.toList.filter (ss.ssPlayer.contains ·)
      |>.map ("player defined at end node: " ++ ·))

def checkNoMovesAtEnd (m : DclegModel) : List String :=
  let ss := m.dmStructure
  ss.ssEndNodes.toList.filter (fun v => match ss.ssMoves.get? v with
      | some ms => !ms.isEmpty
      | none => false)
    |>.map ("non-empty move set at end node: " ++ ·)

def checkNoSelfLoops (m : DclegModel) : List String :=
  m.dmStructure.ssNext.toList.filterMap fun ((v, mv), v') =>
    if v == v' then some s!"self-loop at ({v}, {mv})" else none

def checkPayoffComplete (m : DclegModel) : List String :=
  let ends := m.dmStructure.ssEndNodes.toList
  m.dmPayoff.toList.flatMap fun (ag, perV) =>
    ends.filter (!perV.contains ·) |>.map fun v =>
      s!"payoff missing for agent {ag} at end node {v}"

/-- Every `next` transition must land on a declared node (gamen-hs#18 task 18). -/
def checkNextTargets (m : DclegModel) : List String :=
  let nodes := m.dmStructure.ssNodes
  m.dmStructure.ssNext.toList.filterMap fun ((v, mv), v') =>
    if nodes.contains v' then none else some s!"next target not a node: ({v}, {mv}) -> {v'}"

/-- Every history must be attached to a declared world (gamen-hs#18 task 18). -/
def checkHistoryWorlds (m : DclegModel) : List String :=
  m.dmHistory.keys.filter (!m.dmWorlds.contains ·)
    |>.map ("history attached to world not in model: " ++ ·)

def validateModel (m : DclegModel) : List String :=
  checkEndNodesSubset m ++ checkPlayerDefined m ++ checkNoMovesAtEnd m ++ checkNoSelfLoops m
    ++ checkPayoffComplete m ++ checkNextTargets m ++ checkHistoryWorlds m

/-- Assemble, validate, and apply premises (Haskell `assembleModel`). -/
def assembleModel (mj : ModelJSON) (strict : Bool) : Except BuildError DclegModel :=
  if strict then
    throw (.buildUnsupported "strict"
      (Json.mkObj [("note", "strict-mode validation is not implemented in v0.1")]))
  else if mj.mjPremises != Json.str "auto" then
    throw (.buildUnsupported "premises" (Json.mkObj
      [("note", "only the \"auto\" premises form is supported in v0.1; explicit premises \
          are deferred to v0.2"),
       ("received", mj.mjPremises)]))
  else
    let sj := mj.mjStructure
    let ss := mkStrategicStructure sj.sjNodes sj.sjEndNodes sj.sjPlayer sj.sjMoves sj.sjNext
    let hs := mj.mjHistories.map fun h => (h.hjWorld, mkHistory h.hjMoves h.hjEnd)
    let val := mj.mjValuation.map fun v => (v.vjProp, v.vjPairs)
    let dox := mj.mjDoxastic.map fun da =>
      (da.daAgent, da.daEntries.map fun dv =>
        (dv.dvVertex, dv.dvWorlds.map fun we => (we.wsWorld, we.wsSuccessors)))
    let pay := mj.mjPayoff.map fun p => (p.payAgent, p.payEntries)
    let m0 := mkDclegModel ss mj.mjWorlds hs val dox pay
    let m1 := withMovePremises m0
    -- §3 structural checks + referential integrity, then the library's
    -- `validateDclegModel` on the model with its premises (module docstring).
    let violations := validateModel m0 ++ validateDclegModel m1
    if violations.isEmpty then pure m1 else throw (.buildInvalid violations)

/-- Parse a model from JSON, validate it, and apply premises. `strict:true`
or an explicit `premises` value is rejected as unsupported, not ignored
(gamen-hs#18 task 18). -/
def parseAndBuildModel (v : Json) (strict : Bool) : Except BuildError DclegModel :=
  match parseModelJSON v with
  | .error msg => throw (.buildInvalid ["JSON parse error: " ++ msg])
  | .ok mj => assembleModel mj strict

/-! ## Summary for `list` -/

/-- Compact shape summary used by the `list` operation. -/
def modelSummary (h : String) (m : DclegModel) : Json :=
  Json.mkObj [("handle", Json.str h), ("vertices", toJson m.dmStructure.ssNodes.size),
    ("worlds", toJson m.dmWorlds.size)]

end Gamen.Service
