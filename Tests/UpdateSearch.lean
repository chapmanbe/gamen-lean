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

def coreCases : List (String × Bool) := [
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

/-! ## Theorem 6's NP-hardness reduction (extended version, appendix), run end to end

3SAT `Ψ = ⋀ X_i` becomes a one-agent CGS `G_Ψ` (states `X_i`, `x_i^j`, `u_l`, `t1`, `t2`; atoms
`p`, `p⊤`, `p⊥`, `p_l`) and a goal `φ_Ψ`; `Ψ` is satisfiable iff some update `[π]` makes
`G_Ψ, X_1 ⊨ [π]φ_Ψ`. An update enables `α` (true) or `β` (false) at `u_l` via `p_l : α → a`.
The pool is the `2k` clauses `p_l : α → a` and `p_l : β → a`, bound `k`; the answer must equal
brute-force satisfiability. `notFound` is relative to that pool, so this checks the reduction in
the direction the proof sketch relies on: a satisfying assignment yields such an update, and when
no update exists in the pool, `Ψ` is unsatisfiable. -/

/-- A 3SAT instance: clauses of three literals `±l`, atoms `1..k`. -/
abbrev Cnf := List (List Int)

def Cnf.atoms (c : Cnf) : Nat := c.foldl (fun m cl => cl.foldl (fun m l => max m l.natAbs) m) 0

/-- Brute-force satisfiability. -/
def Cnf.sat (c : Cnf) : Bool :=
  (List.range (2 ^ c.atoms)).any fun bits =>
    c.all fun cl => cl.any fun l =>
      let v := (bits / 2 ^ (l.natAbs - 1)) % 2 == 1
      if l > 0 then v else !v

def jstr (xs : List String) : String := "[" ++ ",".intercalate xs ++ "]"
def q (s : String) : String := "\"" ++ s ++ "\""

/-- `G_Ψ` as an `atl_model_check` model. -/
def gPsi (c : Cnf) : String :=
  let m := c.length
  let k := c.atoms
  let acts := ["alpha", "beta", "beta1", "beta2", "beta3", "gamma"]
  let xs : List String := (List.range m).map fun i => s!"X{i + 1}"
  let lits : List (String × Int) := (List.range m).flatMap fun i =>
    (List.range 3).map fun j => (s!"x{i + 1}_{j + 1}", (c[i]!)[j]!)
  let us : List String := (List.range k).map fun l => s!"u{l + 1}"
  let states := xs ++ lits.map (·.1) ++ us ++ ["t1", "t2"]
  let avail (st : String) : List String :=
    if st.startsWith "X" then ["alpha", "beta1", "beta2", "beta3"]
    else if st.startsWith "x" then ["alpha"]
    else if st.startsWith "u" then ["gamma"] else ["alpha"]
  let next (st act : String) : String :=
    if st.startsWith "X" then
      let i := (st.drop 1).toNat!
      if act == "alpha" then (if i < m then s!"X{i + 1}" else st)
      else if act == "beta1" then s!"x{i}_1" else if act == "beta2" then s!"x{i}_2"
      else if act == "beta3" then s!"x{i}_3" else st
    else if st.startsWith "x" then
      if act == "alpha" then
        match lits.find? (·.1 == st) with
        | some (_, l) => s!"u{l.natAbs}"
        | none => st
      else st
    else if st.startsWith "u" then
      if act == "alpha" then "t1" else if act == "beta" then "t2" else st
    else st
  let val (st : String) : List String :=
    if st.startsWith "X" then ["p"]
    else if st.startsWith "x" then
      (match lits.find? (·.1 == st) with | some (_, l) => if l > 0 then ["pT"] else ["pF"] | none => [])
    else if st.startsWith "u" then [s!"p{st.drop 1}"]
    else if st == "t1" then ["pT"] else ["pF"]
  "{" ++ s!"\"states\":{jstr (states.map q)},\"agents\":[\"a\"],\"actions\":{jstr (acts.map q)},"
    ++ "\"moves\":{" ++ ",".intercalate (states.map fun st => s!"{q st}:\{\"a\":{jstr ((avail st).map q)}}") ++ "},"
    ++ "\"valuation\":{" ++ ",".intercalate ((states.filter fun st => !(val st).isEmpty).map fun st =>
        s!"{q st}:{jstr ((val st).map q)}") ++ "},"
    ++ "\"transitions\":[" ++ ",".intercalate (states.flatMap fun st => acts.map fun a =>
        s!"\{\"state\":{q st},\"moves\":\{\"a\":{q a}},\"next\":{q (next st a)}}") ++ "]}"

def dx (f : DFormula) : DFormula := .canNext ["a"] f
def pT : DFormula := .atom "pT"
def pF : DFormula := .atom "pF"
def pAt : DFormula := .atom "p"

/-- `φ_Ψ = ⟨⟨a⟩⟩G(p ∧ ⟨⟨a⟩⟩X(¬p ∧ φtrue ∧ φfalse))`. -/
def phiPsi : DFormula :=
  let ph (t f : DFormula) : DFormula :=
    .implies t (.and (dx (.and (.not t) (dx t))) (.not (dx (dx f))))
  .canAlways ["a"] (.and pAt (dx (.and (.not pAt) (.and (ph pT pF) (ph pF pT)))))

def psiPool (k : Nat) : List Candidate :=
  (List.range k).flatMap fun l =>
    ["alpha", "beta"].map fun a =>
      { grant := true, cond := .atom s!"p{l + 1}", action := a, agents := ["a"] }

/-- `some true` iff an update over the pool, of size at most `k`, makes `φ_Ψ` hold at `X1`. -/
def reductionSays (c : Cnf) : Option Bool :=
  match AtlDynamicTests.load (gPsi c) with
  | .error _ => none
  | .ok m =>
    match boundedUpdate m .perfect "X1" phiPsi c.atoms (psiPool c.atoms) 200000 with
    | .ok { outcome := .found steps _, .. } =>
      -- re-check the witness by evaluating [π]φ_Ψ
      match dsat m .perfect (stepsFormula steps phiPsi) with
      | .ok r => some (r.contains "X1")
      | .error _ => none
    | .ok { outcome := .notFound, .. } => some false
    | .error _ => none

def paperEx : Cnf := [[1, 2, 3], [-1, -3, 4]]
def unsat3 : Cnf := [[1, 2, 3], [1, 2, -3], [1, -2, 3], [1, -2, -3], [-1, 2, 3], [-1, 2, -3], [-1, -2, 3], [-1, -2, -3]]
def lcgN (x : Nat) : Nat := (x * 1103515245 + 12345) % 2147483648
/-- A random 3-literal-per-clause instance over `k` atoms. -/
def randCnf (k m seed : Nat) : Cnf :=
  let rec go (i x : Nat) (acc : Cnf) : Cnf :=
    match i with
    | 0 => acc
    | i + 1 =>
      let (cl, x') := (List.range 3).foldl (fun (cl, x) _ =>
        let x := lcgN x
        let atom := (x / 65536) % k + 1
        let sign := (x / 1048576) % 2 == 0
        (cl ++ [if sign then (atom : Int) else -(atom : Int)], x)) ([], x)
      go i x' (acc ++ [cl])
  go m seed []

/-- Satisfiable only by assignments that set some atom true and some false, so an update that
treats every atom alike (ignores the condition `p_l`) cannot find them. -/
def mixedOnly : List Cnf :=
  [[[1, 1, 1], [-2, -2, -2]], [[1, 1, 1], [-2, -2, -2], [-1, 2, 3]],
   [[-1, -1, -1], [2, 2, 2], [1, -2, 3]]]
/-- Unsatisfiable, but each clause is satisfied by some uniform assignment. -/
def mixedUnsat : Cnf := [[1, 1, 1], [-1, 2, 2], [-2, -2, -2]]

def reductionInstances : List Cnf :=
  [paperEx, unsat3, mixedUnsat] ++ mixedOnly ++ (List.range 14).map fun i => randCnf (3 + i % 2) (3 + (i * 5) % 9) (7 + 977 * i)

def reductionCases : List (String × Bool) := [
  ("Thm 6 hardness (Fig. 6): the paper's example Ψ = (p1∨p2∨p3)∧(¬p1∨¬p3∨p4) is satisfiable, and its update [p2 : α → a, p4 : α → a]⁺ makes φ_Ψ hold at X1",
    (match AtlDynamicTests.load (gPsi paperEx) with
     | .ok m =>
       (dsat m .perfect (.grant (.cons (.atom "p2") "alpha" ["a"] [] (.cons (.atom "p4") "alpha" ["a"] [] .nil)) phiPsi)).toOption.map
         (·.contains "X1") == some true
         && (dsat m .perfect phiPsi).toOption.map (·.contains "X1") == some false
     | .error _ => false)),
  ("Thm 6 hardness: the reduction agrees with brute-force 3SAT on the paper's example, the 8-clause unsatisfiable instance, and 14 random ones (both satisfiable and unsatisfiable occur), including instances only a mixed true/false assignment satisfies",
    reductionInstances.all (fun c => reductionSays c == some c.sat)
      && reductionInstances.any (·.sat) && reductionInstances.any (!·.sat)
      && mixedOnly.all fun c => c.sat
        && !(c.all fun cl => cl.any fun l => l > 0) && !(c.all fun cl => cl.any fun l => l < 0))
]

def cases : List (String × Bool) := coreCases ++ reductionCases

end UpdateSearchTests
