import Validate.Core

/-!
# The Lean-only `evidence_trust_check` action (`Validate/EvidenceTrust.lean`)

Issue #3 item 4, protocol 8. Pins the wire contract: the paper's §2.4 example over JSON, the
stable error codes, strict keys, and size limits.
-/

namespace ValidateEvidenceTrustTests

open Lean (Json)

def movieJson : String :=
  "{\"worlds\":[\"w0\",\"w1\",\"w2\"],\"agents\":[\"chatbot\",\"wikipedia\",\"imdb\",\"amazon\",\"rt\"],\
    \"valuation\":{\"w0\":[\"p\",\"q\"],\"w1\":[\"q\"]},\
    \"knowledge\":{\"chatbot\":[[\"w0\",\"w1\",\"w2\"]],\"wikipedia\":[[\"w0\",\"w1\",\"w2\"]],\"imdb\":[[\"w0\",\"w1\",\"w2\"]],\"amazon\":[[\"w0\",\"w1\",\"w2\"]],\"rt\":[[\"w0\",\"w1\",\"w2\"]]},\
    \"belief\":{\"chatbot\":[{\"class\":\"w0\",\"worlds\":[\"w0\",\"w1\",\"w2\"]}],\"wikipedia\":[{\"class\":\"w0\",\"worlds\":[\"w0\"]}],\"imdb\":[{\"class\":\"w0\",\"worlds\":[\"w0\"]}],\"amazon\":[{\"class\":\"w0\",\"worlds\":[\"w0\"]}],\"rt\":[{\"class\":\"w0\",\"worlds\":[\"w0\"]}]},\
    \"trust\":{\"chatbot\":{\"wikipedia\":[{\"class\":\"w0\",\"sets\":[[\"w0\"],[\"w1\",\"w2\"]]}],\"imdb\":[{\"class\":\"w0\",\"sets\":[[\"w0\"],[\"w1\",\"w2\"]]}],\
      \"amazon\":[{\"class\":\"w0\",\"sets\":[[\"w0\",\"w1\"],[\"w2\"]]}],\"rt\":[{\"class\":\"w0\",\"sets\":[[\"w0\",\"w1\"],[\"w2\"]]}]}},\
    \"types\":{\"chatbot\":[2,\"1\"],\"wikipedia\":[1,\"1\"],\"imdb\":[1,\"1\"],\"amazon\":[1,\"1\"],\"rt\":[1,\"1\"]}}"

/-- Two worlds, two agents, no evidence or trust. -/
def tiny : String :=
  "{\"worlds\":[\"a\",\"b\"],\"agents\":[\"i\",\"j\"],\"valuation\":{\"a\":[\"p\"]},\
    \"belief\":{\"i\":[{\"class\":\"a\",\"worlds\":[\"a\"]}],\"j\":[{\"class\":\"a\",\"worlds\":[\"a\"]}]},\
    \"knowledge\":{\"i\":[[\"a\",\"b\"]],\"j\":[[\"a\",\"b\"]]},\
    \"types\":{\"i\":[0,\"1\"],\"j\":[0,\"1\"]}}"

def atomJ (n : String) : String := "{\"type\":\"atom\",\"name\":\"" ++ n ++ "\"}"
def notJ (f : String) : String := "{\"type\":\"not\",\"operand\":" ++ f ++ "}"
def andJ (a b : String) : String := "{\"type\":\"and\",\"left\":" ++ a ++ ",\"right\":" ++ b ++ "}"
def beliefJ (a f : String) : String := "{\"type\":\"belief\",\"agent\":\"" ++ a ++ "\",\"operand\":" ++ f ++ "}"
def announceJ (a f g : String) : String :=
  "{\"type\":\"announce\",\"agent\":\"" ++ a ++ "\",\"operand\":" ++ f ++ ",\"then\":" ++ g ++ "}"
def assessJ (a f g : String) : String :=
  "{\"type\":\"assess\",\"agent\":\"" ++ a ++ "\",\"operand\":" ++ f ++ ",\"then\":" ++ g ++ "}"

def req (model : String) (fs : List String) (extra : String := "") : String :=
  "{\"action\":\"evidence_trust_check\",\"model\":" ++ model ++ ",\"formulas\":["
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
def itemCode (r : Json) (i : Nat) : Option String := strKey (item r i) "error_code"

/-- `k` distinct nonempty subsets of 20 worlds `w0..w19`, as JSON. -/
def manySets (k : Nat) : String :=
  "[" ++ ",".intercalate ((List.range k).map fun m =>
    "[" ++ ",".intercalate (((List.range 20).filter fun b => (m + 1).testBit b).map fun b =>
      "\"w" ++ toString b ++ "\"") ++ "]") ++ "]"

def bigModel (k : Nat) : String :=
  let ws := "[" ++ ",".intercalate ((List.range 20).map fun i => "\"w" ++ toString i ++ "\"") ++ "]"
  "{\"worlds\":" ++ ws ++ ",\"agents\":[\"i\",\"j\"],\"knowledge\":{\"i\":[" ++ ws ++ "],\"j\":[" ++ ws
    ++ "]},\"belief\":{\"i\":[{\"class\":\"w0\",\"worlds\":[\"w0\"]}],\"j\":[{\"class\":\"w0\",\"worlds\":[\"w0\"]}]},\
    \"trust\":{\"i\":{\"j\":[{\"class\":\"w0\",\"sets\":" ++ manySets k ++ "}]}},\
    \"types\":{\"i\":[0,\"1\"],\"j\":[0,\"1\"]}}"

def p := atomJ "p"
def q := atomJ "q"
def all3 : List String := ["w0", "w1", "w2"]

def cases : List (String × Bool) := [
  ("§2.4 over JSON: Wikipedia and IMDb both announcing p, then ?chatbot p, gives B q in every world",
    sat (run (req movieJson [announceJ "wikipedia" p (announceJ "imdb" p (assessJ "chatbot" p (beliefJ "chatbot" q)))]))
      == some all3),
  ("§2.4 over JSON: Amazon q then RT ¬q then ?chatbot q leaves the chatbot undecided about q everywhere",
    sat (run (req movieJson [announceJ "amazon" q (announceJ "rt" (notJ q) (assessJ "chatbot" q
      (andJ (notJ (beliefJ "chatbot" q)) (notJ (beliefJ "chatbot" (notJ q))))))])) == some all3),
  ("control: Wikipedia alone does not make a cautiousness-2 chatbot believe q (no world)",
    sat (run (req movieJson [announceJ "wikipedia" p (assessJ "chatbot" p (beliefJ "chatbot" q))])) == some []),
  ("`worlds` restricts the report; `holds` is per reported world; `true_in_model` is one flag for the whole model, not the restricted report",
    (let r := run (req movieJson [p] ",\"worlds\":[\"w2\",\"w0\"]")
     sat r == some ["w0"]
       && ((item r 0).bind fun i => (i.getObjVal? "true_in_model").toOption) == some (Json.bool false))),
  ("an unknown world in `worlds` is a request error",
    code (run (req movieJson [p] ",\"worlds\":[\"w9\"]")) == some "unknown_world"),
  ("a world listed twice in `worlds` is an error",
    code (run (req movieJson [p] ",\"worlds\":[\"w0\",\"w0\"]")) == some "malformed_spec"),
  ("belief is required for every class: dropping the chatbot's entry is malformed_spec, not a default",
    code (run (req (movieJson.replace "\"chatbot\":[{\"class\":\"w0\",\"worlds\":[\"w0\",\"w1\",\"w2\"]}]," "") [p]))
      == some "malformed_spec"),
  ("a misspelled model key is an error, not an absent field (`trusts`)",
    code (run (req (movieJson.replace "\"trust\":" "\"trusts\":") [p])) == some "malformed_spec"),
  ("a stray key on a formula is an error",
    itemCode (run (req movieJson ["{\"type\":\"atom\",\"name\":\"p\",\"agent\":\"chatbot\"}"])) 0
      == some "malformed_spec"),
  ("an update without `then` is malformed_spec, not a silent ⊤",
    itemCode (run (req movieJson
      ["{\"type\":\"announce\",\"agent\":\"wikipedia\",\"operand\":" ++ p ++ "}"])) 0 == some "malformed_spec"),
  ("an unknown agent in a formula is a per-formula unknown_agent, and does not sink its neighbor",
    (let r := run (req movieJson [beliefJ "nobody" p, p])
     itemCode r 0 == some "unknown_agent" && sat r 1 == some ["w0"])),
  ("a quota as a decimal string is bad_rational, and as a JSON number is malformed_spec",
    code (run (req (tiny.replace "[0,\"1\"]" "[0,\"0.75\"]") [p])) == some "bad_rational"
      && code (run (req (tiny.replace "[0,\"1\"]" "[0,0.75]") [p])) == some "malformed_spec"),
  ("a zero denominator is bad_rational",
    code (run (req (tiny.replace "[0,\"1\"]" "[0,\"3/0\"]") [p])) == some "bad_rational"),
  ("a quota below 1/2 is bad_type; a cautiousness above the number of agents is bad_type",
    code (run (req (tiny.replace "[0,\"1\"]" "[0,\"1/4\"]") [p])) == some "bad_type"
      && code (run (req (tiny.replace "[0,\"1\"]" "[3,\"1\"]") [p])) == some "bad_type"),
  ("C9 over the wire: evidence from a source one does not trust is violates_C9",
    code (run (req (tiny.replace "\"types\"" "\"evidence\":{\"i\":{\"j\":[{\"class\":\"a\",\"sets\":[[\"a\"]]}]}},\"types\"") [p]))
      == some "violates_C9"),
  ("C8 over the wire: trust about the empty set is violates_C8",
    code (run (req (tiny.replace "\"types\"" "\"trust\":{\"i\":{\"j\":[{\"class\":\"a\",\"sets\":[[]]}]}},\"types\"") [p]))
      == some "violates_C8"),
  ("C3 over the wire: a belief set reaching outside its class is violates_C3, not a missing-entry error",
    (let m := (tiny.replace "\"belief\":{\"i\":[{\"class\":\"a\",\"worlds\":[\"a\"]}]"
        "\"belief\":{\"i\":[{\"class\":\"a\",\"worlds\":[\"a\",\"b\"]},{\"class\":\"b\",\"worlds\":[\"b\"]}]").replace
        "\"knowledge\":{\"i\":[[\"a\",\"b\"]]" "\"knowledge\":{\"i\":[[\"a\"],[\"b\"]]"
     code (run (req m [p])) == some "violates_C3")),
  ("overlapping knowledge classes, duplicate worlds and duplicate agents have their own codes",
    code (run (req (tiny.replace "[[\"a\",\"b\"]],\"j\"" "[[\"a\",\"b\"],[\"b\"]],\"j\"") [p])) == some "overlapping_classes"
      && code (run (req (tiny.replace "[\"a\",\"b\"],\"agents\"" "[\"a\",\"a\"],\"agents\"") [p])) == some "duplicate_world"
      && code (run (req (tiny.replace "[\"i\",\"j\"],\"valuation\"" "[\"i\",\"i\"],\"valuation\"") [p])) == some "duplicate_agent"),
  ("an entry naming a class twice is malformed_spec (belief)",
    code (run (req (tiny.replace "\"belief\":{\"i\":[{\"class\":\"a\",\"worlds\":[\"a\"]}]"
      "\"belief\":{\"i\":[{\"class\":\"a\",\"worlds\":[\"a\"]},{\"class\":\"b\",\"worlds\":[\"b\"]}]") [p]))
      == some "malformed_spec"),
  ("21 worlds is bad_size",
    code (run (req ("{\"worlds\":[" ++ ",".intercalate ((List.range 21).map fun i => "\"w" ++ toString i ++ "\"")
      ++ "],\"agents\":[\"i\"],\"belief\":{},\"types\":{}}") [p])) == some "bad_size"),
  ("9 agents is bad_size",
    code (run (req ("{\"worlds\":[\"w\"],\"agents\":[" ++ ",".intercalate ((List.range 9).map fun i => "\"a" ++ toString i ++ "\"")
      ++ "],\"belief\":{},\"types\":{}}") [p])) == some "bad_size"),
  ("a typo in the request envelope is an error, not an ignored field (`world` for `worlds`)",
    (let r := run (req movieJson [p] ",\"world\":[\"w9\"]")
     (r.getObjVal? "ok").toOption == some (Json.bool false)
       && ((r.getObjVal? "error").toOption.bind (·.getStr?.toOption)).any (·.contains "unknown key"))),
  ("knowledge is required for every agent: omitting it, or omitting one agent, is malformed_spec, not omniscience",
    code (run (req (tiny.replace "\"knowledge\":{\"i\":[[\"a\",\"b\"]],\"j\":[[\"a\",\"b\"]]}," "") [p])) == some "malformed_spec"
      && code (run (req (tiny.replace "\"knowledge\":{\"i\":[[\"a\",\"b\"]],\"j\":[[\"a\",\"b\"]]}"
        "\"knowledge\":{\"i\":[[\"a\",\"b\"]]}") [p])) == some "malformed_spec"),
  ("a `type` formula outside the language (cautiousness above the agent count, quota below 1/2) is bad_type, not false",
    itemCode (run (req tiny ["{\"type\":\"type\",\"agent\":\"i\",\"x\":9,\"y\":\"1\"}"])) 0 == some "bad_type"
      && itemCode (run (req tiny ["{\"type\":\"type\",\"agent\":\"i\",\"x\":0,\"y\":\"1/4\"}"])) 0 == some "bad_type"),
  ("more than 2000 sets in one evidence or trust entry is bad_size (validation is quadratic in the sets)",
    code (run (req (bigModel 2001) [p])) == some "bad_size"),
  ("the protocol version is at least 8 (this request's) and the version request reports it",
    Gamen.Protocol.protocolVersion ≥ 8
      && (run "{\"action\":\"version\"}").compress.contains
        s!"\"protocol\":{Gamen.Protocol.protocolVersion}")]

end ValidateEvidenceTrustTests
