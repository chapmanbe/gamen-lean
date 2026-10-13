import Gamen.Atl.UpdateSearch
import Tests.AtlDynamic
import Tests.ValidateAtl

/-!
# Bounded update existence (`Gamen.Atl.UpdateSearch`; ATL-D paper Def 7, Theorem 6)

On the oxygen-tank model (Example 1): one revocation keeps the robots out of the warm
area; reaching Bob in one step needs a grant; both together need two clauses, and one is
not enough. Every `found` answer is re-checked by evaluating `[π⃗]φ` with `dsat`.
-/

namespace UpdateSearchTests

open Gamen Gamen.Atl.Dynamic AtlDynamicTests

def safe : DFormula := .canRelease [] atBob (.not (.atom "warm"))
def reach : DFormula := .canNext team atBob

def tank : Option DynModel := (load modelDefault).toOption

def search (m : DynModel) (mode : IrMode) (v : String) (goal : DFormula) (n : Nat)
    (fuel : Nat := 200000) : Except String SearchReport :=
  boundedUpdate m mode v goal n (defaultPool m) fuel

def sizeOf? (r : Except String SearchReport) : Option (Option Nat) :=
  match r with
  | .ok { outcome := .found _ k, .. } => some (some k)
  | .ok { outcome := .notFound, .. } => some none
  | .error _ => none

/-- A `found` answer really satisfies `[π⃗]φ` at `v`, and has the size it claims. -/
def verified (m : DynModel) (mode : IrMode) (v : String) (goal : DFormula)
    (r : Except String SearchReport) : Bool :=
  match r with
  | .ok { outcome := .found steps k, .. } =>
    (steps.foldl (fun acc st => acc + st.clauses.length) 0) == k
      && (match dsat m mode (stepsFormula steps goal) with
          | .ok s => s.contains v
          | .error _ => false)
  | _ => false

def code (r : Lean.Json) : Option String :=
  (r.getObjVal? "error_code").toOption >>= (·.getStr?.toOption)

def reachJ : String :=
  "{\"type\":\"can_next\",\"agents\":[\"r1\",\"r2\"],\"operand\":{\"type\":\"atom\",\"name\":\"atBob\"}}"

def wireWith (goal : String) (bound : Nat) (extra : String) : Lean.Json :=
  processLine ("{\"action\":\"atl_update_search\",\"model\":" ++ modelDefault ++ ",\"state\":\"q0\",\"goal\":"
    ++ goal ++ ",\"bound\":" ++ toString bound ++ extra ++ "}") "t"

def wire (goal : String) (bound : Nat) : Lean.Json := wireWith goal bound ""

def cases : List (String × Bool) := [
  ("search: a goal that already holds needs the empty sequence (size 0)",
    match tank with
    | some m => sizeOf? (search m .perfect "q0" (.canEventually team atBob) 2) == some (some 0)
    | none => false),
  ("search: ⟨⟨∅⟩⟩(atBob R ¬warm) at q0 fails now and one revocation fixes it (size 1)",
    match tank with
    | some m =>
      sizeOf? (search m .perfect "q0" safe 0) == some none
        && sizeOf? (search m .perfect "q0" safe 1) == some (some 1)
        && verified m .perfect "q0" safe (search m .perfect "q0" safe 1)
    | none => false),
  ("search: ⟨⟨r1,r2⟩⟩X atBob at q0 needs one grant (size 1), and no 0-clause sequence works",
    match tank with
    | some m =>
      sizeOf? (search m .perfect "q0" reach 0) == some none
        && sizeOf? (search m .perfect "q0" reach 1) == some (some 1)
        && verified m .perfect "q0" reach (search m .perfect "q0" reach 1)
    | none => false),
  ("search: both goals together need exactly two clauses; one is not enough",
    match tank with
    | some m =>
      let goal := DFormula.and reach safe
      sizeOf? (search m .perfect "q0" goal 1) == some none
        && sizeOf? (search m .perfect "q0" goal 2) == some (some 2)
        && verified m .perfect "q0" goal (search m .perfect "q0" goal 3)
    | none => false),
  ("search: a larger bound never makes the answer smaller than the minimum",
    match tank with
    | some m => sizeOf? (search m .perfect "q0" (.and reach safe) 3) == some (some 2)
    | none => false),
  ("search: ATEL-D — informing a at the p-state lets a reach the goal subjectively (size 1)",
    match load epiModel with
    | .ok m =>
      let goal := DFormula.canNext ["a"] (.atom "goal")
      sizeOf? (search m .subjective "s0" goal 0) == some none
        && sizeOf? (search m .subjective "s0" goal 1) == some (some 1)
        && verified m .subjective "s0" goal (search m .subjective "s0" goal 1)
    | .error _ => false),
  ("search: a tiny budget is an error, never a silent 'not found'",
    match tank with
    | some m => (search m .perfect "q0" (.and reach safe) 2 (fuel := 3)).isOk == false
    | none => false),
  ("search: unknown state and unknown pool action are errors",
    match tank with
    | some m =>
      (search m .perfect "zz" reach 1).isOk == false
        && (boundedUpdate m .perfect "q0" reach 1
              [{ grant := true, cond := .not .bot, action := "fly", agents := ["r2"] }] 100).isOk == false
    | none => false),
  ("search: an explicit pool restricts the answer (no grant in the pool, so reach is not found)",
    match tank with
    | some m =>
      sizeOf? (boundedUpdate m .perfect "q0" reach 2
        ((defaultPool m).filter (!·.grant)) 200000) == some none
    | none => false),
  ("search: grants that enable a joint move with no stated successor are not legal moves (counted, not silently dropped)",
    match (load modelNoDefault).toOption with
    | some m =>
      match search m .perfect "q0" reach 1 with
      | .ok { outcome := .notFound, illegal, .. } => illegal > 0
      | _ => false
    | none => false),
  ("atl_update_search over the wire: reach needs one grant; the reply says what the search is complete for",
    let r := wire reachJ 1
    (r.compress.splitOn "\"found\":true").length == 2 && (r.compress.splitOn "\"size\":1").length == 2
      && (r.compress.splitOn "complete_for").length == 2),
  ("atl_update_search: the returned witness, fed back to atl_model_check, holds at q0",
    match (do
        let res ← (wire reachJ 1).getObjVal? "result" |>.toOption
        res.getObjVal? "witness" |>.toOption : Option Lean.Json) with
    | some w =>
      let back := processLine ("{\"action\":\"atl_model_check\",\"dynamic\":true,\"model\":" ++ modelDefault
        ++ ",\"formulas\":[" ++ w.compress ++ "]}") "t"
      (ValidateAtlTests.satOf back 0).map (·.contains "q0") == some true
    | none => false),
  ("atl_update_search: bound 0 finds nothing; a one-clause bound with revokes only cannot reach",
    ((wire reachJ 0).compress.splitOn "\"found\":false").length == 2
      && ((wireWith reachJ 1 ",\"pool\":[{\"kind\":\"revoke\",\"condition\":{\"type\":\"not\",\"operand\":{\"type\":\"bot\"}},\"action\":\"left\",\"agents\":[\"r1\"]}]").compress.splitOn "\"found\":false").length == 2),
  ("atl_update_search: a tiny fuel is a search_failed error",
    code (wireWith reachJ 1 ",\"fuel\":1") == some "search_failed"),
  ("atl_update_search: a missing bound is a plain protocol error",
    (processLine ("{\"action\":\"atl_update_search\",\"model\":" ++ modelDefault ++ ",\"state\":\"q0\",\"goal\":" ++ reachJ ++ "}") "t").compress
      == "{\"error\":\"key \\\"bound\\\" not found\",\"ok\":false}"),
  ("combos: the 2-element sublists of [1,2,3]",
    combos [1, 2, 3] 2 == [[1, 2], [1, 3], [2, 3]] && combos [1, 2] 0 == [[]] && combos [1] 2 == []),
  ("review: atl_update_search error codes — unknown_state, unknown_action, bound_too_large, search_failed only for the search itself",
    code (wireWith reachJ 1 ",\"state\":\"zz\"") == some "unknown_state"
      && code (wireWith reachJ 1 ",\"pool\":[{\"kind\":\"grant\",\"condition\":{\"type\":\"bot\"},\"action\":\"fly\",\"agents\":[\"r2\"]}]") == some "unknown_action"
      && code (wire reachJ 5000) == some "bound_too_large"
      && code (wireWith reachJ 1 ",\"fuel\":1") == some "search_failed"),
  ("review: encodeDFormula and decodeDFormula round-trip on every constructor",
    let fs : List DFormula :=
      [.bot, .atom "p", .not (.atom "p"), .and (.atom "p") (.atom "q"), .or (.atom "p") (.atom "q"),
       .implies (.atom "p") (.atom "q"), .iff (.atom "p") (.atom "q"), .has "r1" "left",
       .knows "r1" (.atom "p"), .canNext ["r1"] (.atom "p"), .canAlways ["r1"] (.atom "p"),
       .canEventually ["r1", "r2"] (.atom "p"), .canUntil ["r1"] (.atom "p") (.atom "q"),
       .canRelease ["r1"] (.atom "p") (.atom "q"),
       .grant (.cons (.atom "p") "x" ["r1"] ["r2"] (.cons (.not .bot) "y" ["r2"] [] .nil)) (.atom "q"),
       .revoke (.cons (.atom "p") "x" ["r1"] [] .nil) (.has "r1" "x")]
    fs.all fun f =>
      match decodeDFormula (encodeDFormula f) with
      | .ok g => encodeDFormula g == encodeDFormula f
      | .error _ => false),
  ("review: an unknown agent (in agents or in informed) in the pool is an error",
    match tank with
    | some m =>
      (boundedUpdate m .perfect "q0" reach 1
        [{ grant := true, cond := .not .bot, action := "right", agents := ["r9"] }] 100).isOk == false
        && (boundedUpdate m .perfect "q0" reach 1
          [{ grant := true, cond := .not .bot, action := "right", agents := ["r2"], informed := ["r9"] }] 100).isOk == false
    | none => false)
]

end UpdateSearchTests
