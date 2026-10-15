import Validate.Core

/-!
# The Lean-only `angels_demons_check` action (`Validate/AngelsDemons.lean`)

Issue #3 item 2, protocol 7. The wire contract over the access-control models of Catta,
Galimullin & Mittelmann (AAMAS 2026), Examples 1-3 (Figure 1's costs were checked against the figure;
see `Tests/AngelsDemons.lean`). Every expected set repeats a value `Tests/AngelsDemons.lean`
checks through the Lean API, so the JSON layer is tested against the checker, not itself.
-/

namespace ValidateAngelsDemonsTests

open Lean (Json)

def atomF (n : String) : String := "{\"type\":\"atom\",\"name\":\"" ++ n ++ "\"}"
def notF (f : String) : String := "{\"type\":\"not\",\"operand\":" ++ f ++ "}"
def nextP (f : String) : String := "{\"type\":\"next\",\"operand\":" ++ f ++ "}"
def alwaysP (f : String) : String := "{\"type\":\"always\",\"operand\":" ++ f ++ "}"
def eventuallyP (f : String) : String := "{\"type\":\"eventually\",\"operand\":" ++ f ++ "}"
def strat (ty : String) (n : Nat) (p : String) : String :=
  "{\"type\":\"" ++ ty ++ "\",\"bound\":" ++ toString n ++ ",\"path\":" ++ p ++ "}"
def upd (ty : String) (a d : Nat) (p : String) : String :=
  "{\"type\":\"" ++ ty ++ "\",\"angel_bound\":" ++ toString a ++ ",\"demon_bound\":" ++ toString d
    ++ ",\"path\":" ++ p ++ "}"

def costs : String :=
  "[[\"s0\",\"s0\",3],[\"s1\",\"s1\",3],[\"s2\",\"s2\",2],[\"s3\",\"s3\",2],[\"s0\",\"s1\",3],\
    [\"s1\",\"s0\",1],[\"s0\",\"s2\",2],[\"s2\",\"s0\",1],[\"s0\",\"s3\",2],[\"s2\",\"s3\",1],\
    [\"s3\",\"s2\",1]]"

def e1 : String :=
  "[[\"s0\",\"s0\"],[\"s1\",\"s1\"],[\"s2\",\"s2\"],[\"s3\",\"s3\"],[\"s0\",\"s1\"],[\"s0\",\"s2\"],\
    [\"s0\",\"s3\"],[\"s2\",\"s0\"],[\"s2\",\"s3\"]]"

def e2 : String :=
  "[[\"s0\",\"s0\"],[\"s1\",\"s1\"],[\"s2\",\"s2\"],[\"s3\",\"s3\"],[\"s0\",\"s1\"],[\"s0\",\"s2\"],\
    [\"s2\",\"s0\"]]"

def model (edges : String) : String :=
  "{\"states\":[\"s0\",\"s1\",\"s2\",\"s3\"],\"edges\":" ++ edges ++ ",\"costs\":" ++ costs
    ++ ",\"default_cost\":9,\"valuation\":{\"s1\":[\"error\"],\"s2\":[\"server\"],\
      \"s3\":[\"server\",\"admin\"]}}"

def req (m : String) (fs : List String) (extra : String := "") : String :=
  "{\"action\":\"angels_demons_check\",\"model\":" ++ m ++ ",\"formulas\":["
    ++ ",".intercalate fs ++ "]" ++ extra ++ "}"

def run (line : String) : Json := processLine line "t"

def item (r : Json) (i : Nat) : Option Json := do
  let rs ← (← (r.getObjVal? "result").toOption).getObjVal? "results" |>.toOption
  rs.getArrVal? i |>.toOption

def sat (r : Json) (i : Nat := 0) : Option (List String) := do
  let arr ← (← (← item r i).getObjVal? "satisfying" |>.toOption).getArr? |>.toOption
  pure (arr.toList.filterMap (·.getStr?.toOption))

def strKey (j : Option Json) (k : String) : Option String :=
  j.bind fun j => (j.getObjVal? k).toOption >>= (·.getStr?.toOption)

def code (r : Json) : Option String := strKey (some r) "error_code"

def admin := atomF "admin"
def err := atomF "error"

def cases : List (String × Bool) := [
  ("Example 1 over JSON: ⟨⟨demon 2⟩⟩G¬admin holds at s0, s1, s2, and not at s3",
    sat (run (req (model e1) [strat "demon" 2 (alwaysP (notF admin))])) == some ["s0", "s1", "s2"]),
  ("Example 1 with budget 1 (the demon cannot afford s0→s3): only s1",
    sat (run (req (model e1) [strat "demon" 1 (alwaysP (notF admin))])) == some ["s1"]),
  ("Example 3: ⟨[angel 2, demon 2]⟩F¬admin holds at s3 of 𝔐2; with either budget 0 it does not",
    (sat (run (req (model e2) [upd "update" 2 2 (eventuallyP (notF admin))]))).map (·.contains "s3")
        == some true
      && (sat (run (req (model e2) [upd "update" 0 2 (eventuallyP (notF admin))]))).map (·.contains "s3")
        == some false
      && (sat (run (req (model e2) [upd "update" 2 0 (eventuallyP (notF admin))]))).map (·.contains "s3")
        == some false),
  ("competitive coalitions over the wire (Example 3): update_demon (demon_bound 2, angel_bound 2) F¬admin fails at s3; (demon 2, angel 1) G¬admin holds at s1 and (2, 2) fails; the angel and ∅ forms are distinct request types",
    (sat (run (req (model e2) [upd "update_demon" 2 2 (eventuallyP (notF admin))]))).map (·.contains "s3")
        == some false
      && (sat (run (req (model e2) [upd "update_demon" 1 2 (alwaysP (notF admin))]))).map (·.contains "s1")
        == some true
      && (sat (run (req (model e2) [upd "update_demon" 2 2 (alwaysP (notF admin))]))).map (·.contains "s1")
        == some false
      && (sat (run (req (model e2) [upd "update_demon_box" 2 2 (eventuallyP admin)]))).isSome
      && (sat (run (req (model e2) [upd "update_angel" 2 2 (eventuallyP (notF admin))]))).isSome
      && (sat (run (req (model e2) [upd "update_none" 2 2 (eventuallyP (notF admin))]))).isSome),
  ("update_angel is not the cooperative form: at s3 of 𝔐2 only the demon can remove s3's self-loop, so ⟨[angel 2]⟩^2 F¬admin fails (the universal demon passes) while ⟨[angel 2, demon 2]⟩F¬admin holds",
    (sat (run (req (model e2) [upd "update_angel" 2 2 (eventuallyP (notF admin))]))).map (·.contains "s3")
        == some false
      && (sat (run (req (model e2) [upd "update" 2 2 (eventuallyP (notF admin))]))).map (·.contains "s3")
        == some true),
  ("update_none is universal over the angel too: on 𝔐2 at s0, G¬admin holds for ⟨[angel 1]⟩^0 (the angel adds nothing, and s3 is unreachable from s0 in 𝔐2) but fails for ⟨[∅]⟩^{1,0} (an angel adding s0→s3 or s2→s3 reaches it)",
    (sat (run (req (model e2) [upd "update_angel" 1 0 (alwaysP (notF admin))]))).map (·.contains "s0")
        == some true
      && (sat (run (req (model e2) [upd "update_none" 1 0 (alwaysP (notF admin))]))).map (·.contains "s0")
        == some false),
  ("the new types are strict about keys: a `bound` on update_none, and a missing demon_bound on update_angel, are malformed_spec",
    strKey (item (run (req (model e2) [strat "update_none" 1 (nextP admin)])) 0) "error_code"
        == some "malformed_spec"
      && strKey (item (run (req (model e2)
        ["{\"type\":\"update_angel\",\"angel_bound\":1,\"path\":" ++ nextP admin ++ "}"])) 0)
        "error_code" == some "malformed_spec"),
  ("SUL legality survives the wire: ⟨[angel 1, demon 2]⟩X¬admin fails at s3 of 𝔐2",
    (sat (run (req (model e2) [upd "update" 1 2 (nextP (notF admin))]))).map (·.contains "s3")
      == some false),
  ("duality by name: [2]F admin (demon_box) = {s3}, hand-derived in Tests/AngelsDemons",
    sat (run (req (model e1) [strat "demon_box" 2 (eventuallyP admin)])) == some ["s3"]),
  ("nested strategic operators: ⟨⟨1⟩⟩X⟨⟨1⟩⟩X¬admin holds only at s1",
    sat (run (req (model e1)
      [strat "demon" 1 (nextP (strat "demon" 1 (nextP (notF admin))))])) == some ["s1"]),
  ("until and release are not interchangeable: with budget 0 (plain CTL on 𝔐1), ⟨⟨0⟩⟩(admin U ¬error) = {s0,s2,s3} and ⟨⟨0⟩⟩(admin R ¬error) = {s3}, hand-derived",
    sat (run (req (model e1) [strat "demon" 0
        ("{\"type\":\"until\",\"left\":" ++ admin ++ ",\"right\":" ++ notF err ++ "}")]))
        == some ["s0", "s2", "s3"]
      && sat (run (req (model e1) [strat "demon" 0
        ("{\"type\":\"release\",\"left\":" ++ admin ++ ",\"right\":" ++ notF err ++ "}")]))
        == some ["s3"]),
  ("connectives: error ∨ admin, implies and top/bot",
    sat (run (req (model e1) ["{\"type\":\"or\",\"left\":" ++ err ++ ",\"right\":" ++ admin ++ "}"]))
        == some ["s1", "s3"]
      && sat (run (req (model e1)
        ["{\"type\":\"implies\",\"left\":" ++ err ++ ",\"right\":{\"type\":\"bot\"}}"]))
        == some ["s0", "s2", "s3"]
      && sat (run (req (model e1) ["{\"type\":\"top\"}"])) == some ["s0", "s1", "s2", "s3"]),
  ("`states` restricts the report, and `holds` and `true_in_model` are per state",
    (let r := run (req (model e1) [strat "demon" 2 (alwaysP (notF admin))]
        ",\"states\":[\"s3\",\"s1\"]")
     sat r == some ["s1"]
       && ((item r 0).bind fun i => (i.getObjVal? "true_in_model").toOption) == some (Json.bool false)
       && ((item r 0).bind fun i => (i.getObjVal? "holds").toOption
            >>= fun h => (h.getObjVal? "s3").toOption) == some (Json.bool false))),
  ("an unknown state in `states` is a request error",
    code (run (req (model e1) [admin] ",\"states\":[\"s9\"]")) == some "unknown_state"),
  ("a non-serial graph, a zero cost and a duplicate state are request errors with codes",
    code (run (req "{\"states\":[\"a\",\"b\"],\"edges\":[[\"a\",\"b\"]]}" [admin])) == some "invalid_model"
      && code (run (req "{\"states\":[\"a\"],\"edges\":[[\"a\",\"a\"]],\"default_cost\":0}" [admin]))
        == some "invalid_model"
      && code (run (req "{\"states\":[\"a\",\"a\"],\"edges\":[[\"a\",\"a\"]]}" [admin]))
        == some "duplicate_state"
      && code (run (req "{\"states\":[\"a\"],\"edges\":[[\"a\",\"z\"]]}" [admin])) == some "unknown_state"),
  ("a bad formula is a per-formula error and does not sink its neighbors",
    (let r := run (req (model e1) ["{\"type\":\"nope\"}", admin])
     strKey (item r 0) "error_code" == some "malformed_spec" && sat r 1 == some ["s3"])),
  ("a misspelled key is an error, not an absent field: `valuations`, `cost`, an `angel_bound` on a demon, a stray path key",
    code (run (req ((model e1).replace "valuation" "valuations") [admin])) == some "malformed_spec"
      && code (run (req ((model e1).replace "\"costs\"" "\"cost\"") [admin])) == some "malformed_spec"
      && strKey (item (run (req (model e1)
        ["{\"type\":\"demon\",\"bound\":1,\"angel_bound\":1,\"path\":" ++ nextP admin ++ "}"])) 0)
        "error_code" == some "malformed_spec"
      && strKey (item (run (req (model e1)
        [strat "demon" 1 ("{\"type\":\"next\",\"operand\":" ++ admin ++ ",\"left\":" ++ admin ++ "}")])) 0)
        "error_code" == some "malformed_spec"),
  ("a pair costed twice and a state listed twice are errors",
    code (run (req ((model e1).replace "\"costs\":[" "\"costs\":[[\"s0\",\"s0\",5],") [admin]))
        == some "malformed_spec"
      && code (run (req (model e1) [admin] ",\"states\":[\"s1\",\"s1\"]")) == some "malformed_spec"),
  ("max_models must be between 1 and 1000000; max_models 1 still answers ⟨⟨0⟩⟩X admin = □admin = {s3}",
    code (run (req (model e1) [admin] ",\"max_models\":0")) == some "bad_max_models"
      && code (run (req (model e1) [admin] ",\"max_models\":1000001")) == some "bad_max_models"
      && sat (run (req (model e1) [strat "demon" 0 (nextP admin)] ",\"max_models\":1")) == some ["s3"]),
  ("the arena cap is a per-formula error, never a partial answer",
    strKey (item (run (req (model e1) [strat "demon" 9 (nextP admin)] ",\"max_models\":1")) 0)
      "error_code" == some "check_failed")
]

end ValidateAngelsDemonsTests
