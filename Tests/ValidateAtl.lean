import Validate.Core

/-!
# The Lean-only `atl_model_check` action (`Validate/Atl.lean`, `Gamen/CgsJson.lean`)

Issue #2. Protocol extension outside `compare.py`'s scope, so its contract is
pinned here: a two-state, two-agent spec agrees with `sat` called directly,
the flat formula format works, the imperfect-information semantics are
reachable, and malformed specs return stable `error_code`s, never crashes.
-/

namespace ValidateAtlTests

open Lean (Json)
open Gamen

/-- Agent `a` picks `x` (go to `s1`) or `y` (go to `s0`); `b` has the single
move `z`. `goal` holds at `s1`. -/
def model : String :=
  "{\"states\":[\"s0\",\"s1\"],\"agents\":[\"a\",\"b\"],\
    \"moves\":{\"s0\":{\"a\":[\"x\",\"y\"],\"b\":[\"z\"]},\"s1\":{\"a\":[\"x\",\"y\"],\"b\":[\"z\"]}},\
    \"transitions\":[\
      {\"state\":\"s0\",\"moves\":{\"a\":\"x\",\"b\":\"z\"},\"next\":\"s1\"},\
      {\"state\":\"s0\",\"moves\":{\"a\":\"y\",\"b\":\"z\"},\"next\":\"s0\"},\
      {\"state\":\"s1\",\"moves\":{\"a\":\"x\",\"b\":\"z\"},\"next\":\"s1\"},\
      {\"state\":\"s1\",\"moves\":{\"a\":\"y\",\"b\":\"z\"},\"next\":\"s0\"}],\
    \"valuation\":{\"s1\":[\"goal\"]}"

def goal : String := "{\"type\":\"atom\",\"name\":\"goal\"}"
def canNextA : String :=
  "{\"type\":\"can_next\",\"agents\":[\"a\"],\"operand\":" ++ goal ++ "}"
def canNextB : String :=
  "{\"type\":\"can_next\",\"agents\":[\"b\"],\"operand\":" ++ goal ++ "}"

def boxGoal : String := "{\"type\":\"box\",\"operand\":" ++ goal ++ "}"

/-- `model` is an unclosed object (so tests can append fields); this closes it. -/
def req (m : String) (rest : String) : String :=
  "{\"action\":\"atl_model_check\",\"model\":" ++ m ++ "}," ++ rest ++ "}"

def run (line : String) : Json := processLine line "t"

def satOf (r : Json) (i : Nat) : Option (List String) := do
  let res ← (← r.getObjVal? "result" |>.toOption).getObjVal? "results" |>.toOption
  let e ← res.getArrVal? i |>.toOption
  let arr ← (← e.getObjVal? "satisfying" |>.toOption).getArr? |>.toOption
  pure (arr.toList.filterMap (·.getStr?.toOption))

def code (r : Json) : Option String :=
  (r.getObjVal? "error_code").toOption >>= (·.getStr?.toOption)

/-- Direct model check of the same CGS, built from Lean values. -/
def direct : Except String (Std.TreeSet String) := do
  let states := Std.TreeSet.ofList ["s0", "s1"]
  let cgs ← mkCgs states (Std.TreeSet.ofList ["a", "b"])
    (fun _ ag => if ag == "a" then Std.TreeSet.ofList ["x", "y"] else Std.TreeSet.ofList ["z"])
    (fun st jm => match jm.get? "a" with
      | some "x" => "s1"
      | _ => if st == "s1" then "s0" else "s0")
    (fun st => if st == "s1" then Std.TreeSet.ofList ["goal"] else ∅)
  sat cgs (.canNext ["a"] (.atom "goal"))

def cases : List (String × Bool) := [
  ("atl_model_check: <<a>>X goal holds at s0 and s1 (a picks x)",
    satOf (run (req model s!"\"formulas\":[{canNextA}]")) 0 == some ["s0", "s1"]),
  ("atl_model_check: <<b>>X goal holds nowhere (b cannot force it)",
    satOf (run (req model s!"\"formulas\":[{canNextB}]")) 0 == some []),
  ("atl_model_check: agrees with Gamen.Atl.sat called directly",
    (match direct with | .ok s => s.toList | .error _ => ["error"])
      == (satOf (run (req model s!"\"formulas\":[{canNextA}]")) 0).getD ["none"]),
  ("atl_model_check: several formulas answered in order",
    satOf (run (req model s!"\"formulas\":[{canNextB},{canNextA}]")) 1 == some ["s0", "s1"]),
  ("atl_model_check: optional states restricts the answer",
    satOf (run (req model s!"\"formulas\":[{canNextA}],\"states\":[\"s1\"]")) 0 == some ["s1"]),
  ("atl_model_check: an unsupported operator is a per-formula error, the other formulas still answered",
    (let r := run (req model s!"\"formulas\":[{boxGoal},{canNextA}]")
     ((r.compress.splitOn "\"ok\":true").length == 2)
       && satOf r 1 == some ["s0", "s1"] && (satOf r 0).isNone
       && (r.compress.splitOn "\"error\":").length == 2)),
  ("atl_model_check: imperfect semantics reachable, default classes are singletons",
    satOf (run (req model s!"\"semantics\":\"imperfect_subjective\",\"formulas\":[{canNextA}]")) 0
      == some ["s0", "s1"]),
  ("atl_model_check: unknown semantics is an error",
    ((run (req model s!"\"semantics\":\"nope\",\"formulas\":[{canNextA}]")).compress.splitOn "\"ok\":false").length == 2),
  ("atl_model_check: unknown state in states -> unknown_state",
    code (run (req model s!"\"formulas\":[{canNextA}],\"states\":[\"s9\"]")) == some "unknown_state"),
  ("malformed: unknown agent in moves -> unknown_agent",
    code (run (req (model.replace "\"b\":[\"z\"]},\"s1\"" "\"b\":[\"z\"],\"q\":[\"z\"]},\"s1\"")
      s!"\"formulas\":[{canNextA}]")) == some "unknown_agent"),
  ("malformed: repeated joint move -> duplicate_transition",
    code (run (req (model.replace "{\"state\":\"s1\",\"moves\":{\"a\":\"y\",\"b\":\"z\"},\"next\":\"s0\"}" "{\"state\":\"s1\",\"moves\":{\"a\":\"x\",\"b\":\"z\"},\"next\":\"s0\"}")
      s!"\"formulas\":[{canNextA}]")) == some "duplicate_transition"),
  ("malformed: incomplete joint-move table -> missing_transition",
    code (run (req (model.replace ",\
      {\"state\":\"s1\",\"moves\":{\"a\":\"y\",\"b\":\"z\"},\"next\":\"s0\"}" "")
      s!"\"formulas\":[{canNextA}]")) == some "missing_transition"),
  ("malformed: transition to an unknown state -> unknown_state",
    code (run (req (model.replace "\"next\":\"s0\"}]" "\"next\":\"s7\"}]")
      s!"\"formulas\":[{canNextA}]")) == some "unknown_state"),
  ("malformed: action not available -> unknown_move",
    code (run (req (model.replace "\"a\":\"y\",\"b\":\"z\"},\"next\":\"s0\"},\
      {\"state\":\"s1\"" "\"a\":\"w\",\"b\":\"z\"},\"next\":\"s0\"},\
      {\"state\":\"s1\"") s!"\"formulas\":[{canNextA}]")) == some "unknown_move"),
  ("malformed: missing key -> malformed_spec, not a crash",
    code (run "{\"action\":\"atl_model_check\",\"model\":{\"states\":[\"s0\"]},\"formulas\":[]}")
      == some "malformed_spec"),
  ("malformed: model absent is a plain protocol error",
    (run "{\"action\":\"atl_model_check\",\"formulas\":[]}").compress
      == "{\"error\":\"key \\\"model\\\" not found\",\"ok\":false}"),
  ("indistinguishable: non-reflexive-free overlap -> overlapping_classes",
    code (run (req (model ++ ",\"indistinguishable\":{\"a\":[[\"s0\",\"s1\"],[\"s1\"]]}")
      s!"\"semantics\":\"imperfect_subjective\",\"formulas\":[{canNextA}]")) == some "overlapping_classes")
]

end ValidateAtlTests
