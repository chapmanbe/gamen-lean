import Validate.Core

/-!
# The Lean-only `epistemic_check` action (`Validate/Epistemic.lean`, `Gamen/EpistemicJson.lean`)

Issue #3 item 3, protocol 5. Pins the wire contract: Lorini et al. Examples 1-3 over
JSON, the builders against the existing `[B]C`, event selection, sequential updates, and
the stable error codes.
-/

namespace ValidateEpistemicTests

open Lean (Json)

def pA : String := "{\"type\":\"atom\",\"name\":\"p\"}"
def qA : String := "{\"type\":\"atom\",\"name\":\"q\"}"
def neg (f : String) : String := "{\"type\":\"not\",\"operand\":" ++ f ++ "}"
def conj (l r : String) : String := "{\"type\":\"and\",\"left\":" ++ l ++ ",\"right\":" ++ r ++ "}"
def knows (a f : String) : String :=
  "{\"type\":\"knowledge\",\"agent\":\"" ++ a ++ "\",\"operand\":" ++ f ++ "}"
def announce (b c : String) : String :=
  "{\"type\":\"announce\",\"left\":" ++ b ++ ",\"right\":" ++ c ++ "}"

/-- Worlds `w` (with `p`) and `u`, indistinguishable for `i` and `j`. -/
def lorini : String :=
  "{\"worlds\":[\"w\",\"u\"],\"agents\":[\"i\",\"j\"],\
    \"indistinguishable\":{\"i\":[[\"w\",\"u\"]],\"j\":[[\"w\",\"u\"]]},\"valuation\":{\"w\":[\"p\"]}}"

/-- The same worlds with agents `a` and `b`. -/
def loriniAB : String := (lorini.replace "\"j\"" "\"b\"").replace "\"i\"" "\"a\""

/-- Lorini et al. Fig. 1's action model; `event` selects `a`. -/
def loriniA : String :=
  "{\"events\":[\"a\",\"a0\"],\
    \"relations\":{\"i\":[[\"a\",\"a\"],[\"a0\",\"a0\"]],\"j\":[[\"a\",\"a0\"],[\"a0\",\"a0\"]]},\
    \"pre\":{\"a\":" ++ pA ++ "},\"post\":{\"a\":{\"p\":{\"type\":\"bot\"}}},\"event\":\"a\"}"

/-- Three worlds, two agents; `p` on w1,w2 and `q` on w2,w3. -/
def m2 : String :=
  "{\"worlds\":[\"w1\",\"w2\",\"w3\"],\"agents\":[\"a\",\"b\"],\
    \"relations\":{\"a\":[[\"w1\",\"w2\"],[\"w2\",\"w1\"],[\"w1\",\"w1\"],[\"w2\",\"w2\"],[\"w3\",\"w3\"]]},\
    \"indistinguishable\":{\"b\":[[\"w2\",\"w3\"],[\"w1\"]]},\
    \"valuation\":{\"w1\":[\"p\"],\"w2\":[\"p\",\"q\"],\"w3\":[\"q\"]}}"

def req (model : String) (updates formulas : String) (extra : String := "") : String :=
  "{\"action\":\"epistemic_check\",\"model\":" ++ model ++ ",\"updates\":[" ++ updates
    ++ "],\"formulas\":[" ++ formulas ++ "]" ++ extra ++ "}"

def run (line : String) : Json := processLine line "t"

def result (r : Json) (i : Nat) (key : String) : Option (List String) := do
  let rs ← (← (r.getObjVal? "result").toOption).getObjVal? "results" |>.toOption
  let e ← rs.getArrVal? i |>.toOption
  let arr ← (← (e.getObjVal? key).toOption).getArr? |>.toOption
  pure (arr.toList.filterMap (·.getStr?.toOption))

def code (r : Json) : Option String :=
  (r.getObjVal? "error_code").toOption >>= (·.getStr?.toOption)

def sat (r : Json) (i : Nat := 0) := result r i "satisfying"

def cases : List (String × Bool) := [
  ("epistemic_check: no updates, atoms and knowledge",
    sat (run (req lorini "" (pA ++ "," ++ knows "i" pA ++ "," ++ neg (knows "i" pA)))) 0 == some ["w"]
      && sat (run (req lorini "" (pA ++ "," ++ knows "i" pA ++ "," ++ neg (knows "i" pA)))) 1 == some []
      && sat (run (req lorini "" (pA ++ "," ++ knows "i" pA ++ "," ++ neg (knows "i" pA)))) 2 == some ["u", "w"]),
  ("Lorini Ex. 2 over the wire: after a, i knows ¬p and j knows neither; u is not executable",
    let r := run (req lorini loriniA
      (conj (knows "i" (neg pA)) (conj (neg (knows "j" pA)) (neg (knows "j" (neg pA))))))
    sat r == some ["w"] && result r 0 "not_executable" == some ["u"]),
  ("public_announcement builder agrees with [B]C: updates [!p] then ψ vs formula [p]ψ",
    let ψ := conj (knows "a" qA) (neg (knows "b" pA))
    let direct := run (req m2 "" (announce pA ψ))
    let viaUpdate := run (req m2 ("{\"public_announcement\":" ++ pA ++ "}") ψ)
    -- [p]ψ is vacuously true where p is false; the update form reports those as not executable
    (sat direct).map (·.filter fun w => w == "w1" || w == "w2")
      == (sat viaUpdate)
      && result viaUpdate 0 "not_executable" == some ["w3"]),
  ("two sequential public announcements: only worlds with p and q survive",
    let r := run (req m2 ("{\"public_announcement\":" ++ pA ++ "},{\"public_announcement\":" ++ qA ++ "}")
      "{\"type\":\"not\",\"operand\":{\"type\":\"bot\"}}")
    sat r == some ["w2"]),
  ("semi_private_whether: the actual event is chosen by the truth of p; a learns, b does not",
    let upd := "{\"semi_private_whether\":{\"group\":[\"a\"],\"formula\":" ++ pA ++ "}}"
    let r := run (req loriniAB upd
      (knows "a" pA ++ "," ++ knows "b" pA ++ "," ++ knows "b" ("{\"type\":\"or\",\"left\":" ++ knows "a" pA
        ++ ",\"right\":" ++ knows "a" (neg pA) ++ "}")))
    sat r 0 == some ["w"] && sat r 1 == some [] && sat r 2 == some ["u", "w"]),
  ("private_announcement: default event is !; a knows p, b believes a does not",
    let upd := "{\"private_announcement\":{\"group\":[\"a\"],\"formula\":" ++ pA ++ "}}"
    let r := run (req loriniAB upd
      (knows "a" pA ++ "," ++ knows "b" (neg (knows "a" pA))))
    sat r 0 == some ["w"] && sat r 1 == some ["w"] && result r 0 "not_executable" == some ["u"]),
  ("an update with two executable events and no \"event\" is an ambiguous_event error",
    code (run (req lorini "{\"events\":[\"e\",\"f\"],\"relations\":{\"i\":[[\"e\",\"e\"],[\"f\",\"f\"]],\"j\":[[\"e\",\"e\"],[\"f\",\"f\"]]}}" pA))
      == some "ambiguous_event"),
  ("worlds restricts the report; an unknown world is unknown_world",
    sat (run (req m2 "" pA ",\"worlds\":[\"w1\",\"w3\"]")) == some ["w1"]
      && code (run (req m2 "" pA ",\"worlds\":[\"zz\"]")) == some "unknown_world"),
  ("error codes: unknown_agent, unknown_world in a relation, duplicate_world",
    code (run (req (m2.replace "\"relations\":{\"a\"" "\"relations\":{\"zz\"") "" pA)) == some "unknown_agent"
      && code (run (req (m2.replace "[\"w3\",\"w3\"]" "[\"w3\",\"w9\"]") "" pA)) == some "unknown_world"
      && code (run (req (m2.replace "\"w2\",\"w3\"],\"agents\"" "\"w2\",\"w2\"],\"agents\"") "" pA)) == some "duplicate_world"),
  ("error codes: unknown_event, and invalid_action_model when an agent has no relation entry (it would know everything)",
    code (run (req lorini (loriniA.replace "\"event\":\"a\"" "\"event\":\"zz\"") pA)) == some "unknown_event"
      && code (run (req lorini "{\"events\":[\"e\"],\"event\":\"e\"}" pA)) == some "invalid_action_model"),
  ("error codes: invalid_formula in an update, malformed_spec when a key is missing",
    code (run (req lorini
      "{\"public_announcement\":{\"type\":\"nonsense\"}}" pA)) == some "invalid_formula"
      && code (run "{\"action\":\"epistemic_check\",\"model\":{\"worlds\":[\"w\"]},\"formulas\":[]}")
        == some "malformed_spec"),
  ("an unsupported operator is a per-formula error; the other formulas are still answered",
    let r := run (req m2 "" ("{\"type\":\"box\",\"operand\":" ++ pA ++ "}," ++ pA))
    sat r 1 == some ["w1", "w2"] && sat r 0 == none
      && ((r.compress.splitOn "\"error\":").length == 2)),
  ("a model without `model` is a plain protocol error, as for atl_model_check",
    (run "{\"action\":\"epistemic_check\",\"formulas\":[]}").compress
      == "{\"error\":\"key \\\"model\\\" not found\",\"ok\":false}")
]

end ValidateEpistemicTests
