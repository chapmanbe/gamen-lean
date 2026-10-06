import DclegService.BuildInfo

/-!
# `dcleg-service` tests

Port of the gamen-hs tests that exercise the service itself (`Gamen.Dcleg`,
which it calls, is tested by `dclegCases` in `Tests/Main.lean`):

* `test/RegressionIssue18.hs`, "task 18: dcleg-service build hardening
  (issue #18)": all 5 `it`s (`task18Cases`), against `parseAndBuildModel`.
* `test/ProtocolSpec.hs`, "dcleg-service survives bad input and stays
  live": all 3 `it`s (`protocolSpecCases`). gamen-hs runs the binary as a
  subprocess; here they run through `runSession`, the same code the
  binary's loop calls, line by line.

Then, Lean-side:

* `goldenCases`: three recorded sessions (`data/dcleg-service/session-*.jsonl`)
  whose replies must match gamen-hs's, recorded from its `dcleg-service`
  binary (`session-*.gamen-hs.jsonl`), byte for byte, line by line. They
  cover every operation, true and false answers, and the error replies
  (envelope, missing fields, handles, formula and model JSON errors, model
  validation). Requests whose replies differ on purpose are left out (see
  `tools/compare/intentional-divergences.md`); `extensionCases` pins those.
* `extensionCases`: the Lean-only `version` op, and the intentional
  divergences: `internal_error` where gamen-hs crashes, `max_violations`
  ≤ 0, and premise admissibility at `build`.
-/

namespace DclegServiceTests

open Lean (Json)
open Gamen Gamen.Service DclegService

/-! ## RegressionIssue18, "task 18: dcleg-service build hardening" -/

def validJson : String :=
  "{\"strategic_structure\":{\"nodes\":[\"v0\",\"v1\",\"v2\"]," ++
  "\"end_nodes\":[\"v1\",\"v2\"],\"player\":[[\"v0\",\"p1\"]]," ++
  "\"moves\":[[\"v0\",[\"L\",\"R\"]]]," ++
  "\"next\":[[\"v0\",\"L\",\"v1\"],[\"v0\",\"R\",\"v2\"]]}," ++
  "\"worlds\":[\"gL\",\"gR\"]," ++
  "\"histories\":[{\"world\":\"gL\",\"moves\":[[\"v0\",\"L\"]],\"end\":\"v1\"}," ++
  "{\"world\":\"gR\",\"moves\":[[\"v0\",\"R\"]],\"end\":\"v2\"}]," ++
  "\"valuation\":[{\"prop\":\"p\",\"pairs\":[[\"gL\",\"v1\"]]}]," ++
  "\"doxastic\":[{\"agent\":\"p1\",\"entries\":[{\"vertex\":\"v0\"," ++
  "\"worlds\":[{\"world\":\"gL\",\"successors\":[\"gL\"]}," ++
  "{\"world\":\"gR\",\"successors\":[\"gR\"]}]}]}]," ++
  "\"payoff\":[{\"agent\":\"p1\",\"entries\":[[\"v1\",1],[\"v2\",0]]}]," ++
  "\"premises\":\"auto\"}"

/-- The test JSON, or `none` if it does not parse (which fails the case). -/
def decodeV (t : String) : Option Json := (Json.parse t).toOption

def validModel : Option Json := decodeV validJson
def badNextModel : Option Json := decodeV (validJson.replace "\"R\",\"v2\"" "\"R\",\"v9\"")
def danglingDox : Option Json :=
  decodeV (validJson.replace "{\"world\":\"gR\",\"successors\":[\"gR\"]}"
    "{\"world\":\"gZ\",\"successors\":[\"gZ\"]}")
def explicitPrem : Option Json := decodeV (validJson.replace "\"auto\"" "[\"explicit\"]")

def tagOf : Except BuildError DclegModel → String
  | .error (.buildUnsupported feat _) => "unsupported:" ++ feat
  | .error (.buildInvalid _) => "invalid"
  | .ok _ => "ok"

/-- The build's tag, or `none` if the test JSON did not parse. -/
def buildTag (v : Option Json) (strict : Bool) : Option String :=
  v.map fun j => tagOf (parseAndBuildModel j strict)

/-- The violations of an invalid build; `none` for any other outcome. -/
def buildViolations (v : Option Json) : Option (List String) :=
  v.bind fun j => match parseAndBuildModel j false with
    | .error (.buildInvalid vs) => some vs
    | _ => none

def task18Cases : List (String × Bool) := [
  ("RegressionIssue18 task 18: a well-formed model builds (Right)",
    buildTag validModel false == some "ok"),
  ("RegressionIssue18 task 18: strict:true is rejected as unsupported, not silently ignored",
    buildTag validModel true == some "unsupported:strict"),
  ("RegressionIssue18 task 18: explicit (non-auto) premises are rejected as unsupported",
    buildTag explicitPrem false == some "unsupported:premises"),
  ("RegressionIssue18 task 18: a dangling next target is rejected via structural validation",
    buildTag badNextModel false == some "invalid"
      && (buildViolations badNextModel).any (·.any (·.contains "next target not a node"))),
  ("RegressionIssue18 task 18: a dangling doxastic world is caught by wired-in validateDclegModel",
    buildTag danglingDox false == some "invalid"
      && (buildViolations danglingDox).any (·.any (·.contains "validateDclegModel"))) ]

/-! ## ProtocolSpec, "dcleg-service survives bad input and stays live" -/

def contains (s sub : String) : Bool := (s.splitOn sub).length > 1

def protocolSpecCases : List (String × Bool) :=
  let outs1 := runSession ["not json at all", "{\"id\": \"1\", \"op\": \"ping\"}"]
  let outs2 := runSession ["{\"id\": \"1\", \"op\": \"frobnicate\"}", "{\"id\": \"2\", \"op\": \"ping\"}"]
  let outs3 := runSession [
    "{\"id\":\"1\",\"op\":\"build\",\"model\":" ++ validJson ++ "}",
    "{\"id\":\"2\",\"op\":\"build\",\"strict\":true,\"model\":" ++ validJson ++ "}",
    "{\"id\":\"3\",\"op\":\"axiom_check\",\"handle\":\"h-0\",\"axioms\":[\"bogus_axiom\"]}",
    "{\"id\":\"4\",\"op\":\"ping\"}"]
  let nth (outs : List String) (i : Nat) := outs.getD i ""
  [ ("ProtocolSpec dcleg-service: malformed JSON → ok:false parse_error, then still answers a ping",
      outs1.length == 2 && contains (nth outs1 0) "\"ok\":false"
        && contains (nth outs1 0) "parse_error" && contains (nth outs1 1) "dcleg-service"),
    ("ProtocolSpec dcleg-service: unknown op → ok:false unknown_op, then live",
      outs2.length == 2 && contains (nth outs2 0) "\"ok\":false"
        && contains (nth outs2 0) "unknown_op" && contains (nth outs2 1) "dcleg-service"),
    ("ProtocolSpec dcleg-service: build ok, strict rejected, unknown axiom rejected — all in one session",
      outs3.length == 4 && contains (nth outs3 0) "\"ok\":true"
        && contains (nth outs3 1) "unsupported" && contains (nth outs3 2) "unknown_axiom"
        && contains (nth outs3 3) "dcleg-service") ]

/-! ## Recorded sessions, byte for byte against gamen-hs -/

/-- Lines of a file, without the final empty one; an unreadable file gives
`none`, which fails every case built on it. -/
def readLines (path : String) : IO (Option (List String)) := do
  try
    let t ← IO.FS.readFile path
    return some ((t.splitOn "\n").filter (!·.isEmpty))
  catch _ => return none

/-- One case per recorded gamen-hs reply, plus one that the reply counts
agree. The input file may contain empty lines (no reply), so replies are
paired by position in the output, as the binary prints them. -/
def goldenCases : IO (List (String × Bool)) := do
  let mut out := []
  for s in ["ops", "errors", "build-errors"] do
    let inp ← readLines s!"data/dcleg-service/session-{s}.jsonl"
    let exp ← readLines s!"data/dcleg-service/session-{s}.gamen-hs.jsonl"
    match inp, exp with
    | some inp, some exp =>
      let got := runSession inp
      out := out ++ [(s!"golden session {s}: {exp.length} replies, as gamen-hs",
        got.length == exp.length)]
      for (e, i) in exp.zipIdx do
        out := out ++ [(s!"golden session {s}, reply {i}: {e.take 60}…",
          got[i]? == some e)]
    | _, _ => out := out ++ [(s!"golden session {s}: data files readable", false)]
  return out

/-! ## Lean-only `version`, and the intentional divergences -/

def selfAwareBad : String :=
  validJson.replace "{\"world\":\"gL\",\"successors\":[\"gL\"]}"
    "{\"world\":\"gL\",\"successors\":[\"gR\"]}"

/-- A history plays a move (`X`) that `moves` does not list at v0: gamen-hs
builds it; here the premise function fails Contemporary Universality. -/
def offMoveModel : String :=
  validJson.replace "{\"world\":\"gR\",\"moves\":[[\"v0\",\"R\"]]" "{\"world\":\"gR\",\"moves\":[[\"v0\",\"X\"]]"

/-- The task-18 model without a doxastic map, so the player p1 has none. -/
def noDoxModel : String :=
  validJson.replace ("\"doxastic\":[{\"agent\":\"p1\",\"entries\":[{\"vertex\":\"v0\"," ++
    "\"worlds\":[{\"world\":\"gL\",\"successors\":[\"gL\"]}," ++
    "{\"world\":\"gR\",\"successors\":[\"gR\"]}]}]}],") ""

def build (h model : String) : String :=
  s!"\{\"id\":\"b\",\"op\":\"build\",\"handle\":\"{h}\",\"model\":{model}}"

def extensionCases : List (String × Bool) := [
  ("version: reply names gamen-lean, the commit, and dcleg protocol 1 (exact bytes)",
    runSession ["{\"id\":\"v\",\"op\":\"version\"}"] "abc123"
      == ["{\"id\":\"v\",\"ok\":true,\"result\":{\"commit\":\"abc123\",\
           \"implementation\":\"gamen-lean\",\"protocol\":1}}"]),
  ("version: the served commit is the build stamp",
    runSession ["{\"id\":\"v\",\"op\":\"version\"}"] dclegBuildCommit
      == [s!"\{\"id\":\"v\",\"ok\":true,\"result\":\{\"commit\":\"{dclegBuildCommit}\",\
           \"implementation\":\"gamen-lean\",\"protocol\":1}}"]
      && dclegBuildCommit != "unknown"),
  ("ping does not list version (byte-identical to gamen-hs)",
    runSession ["{\"id\":\"1\",\"op\":\"ping\"}"]
      == ["{\"id\":\"1\",\"ok\":true,\"result\":{\"capabilities\":[\"build\",\"sat\",\"true_in\",\
           \"counterfactual\",\"axiom_check\",\"drop\",\"list\"],\"service\":\"dcleg-service\",\
           \"version\":\"0.1.0\"}}"]),
  ("sat with B_i for an unknown agent: internal_error, and the service stays live \
    (gamen-hs crashes)",
    runSession [build "m" validJson,
      "{\"id\":\"2\",\"op\":\"sat\",\"handle\":\"m\",\"world\":\"gL\",\"vertex\":\"v0\",\
        \"formula\":{\"type\":\"belief\",\"agent\":\"zz\",\"operand\":{\"type\":\"bot\"}}}",
      "{\"id\":\"3\",\"op\":\"true_in\",\"handle\":\"m\",\"formula\":{\"type\":\"bot\"}}"]
      == ["{\"id\":\"b\",\"ok\":true,\"result\":{\"handle\":\"m\",\"warnings\":[]}}",
          "{\"error\":{\"code\":\"internal_error\",\"message\":\"doxasticSuccessors: agent \
            \\\"zz\\\" is not in model\"},\"id\":\"2\",\"ok\":false}",
          "{\"id\":\"3\",\"ok\":true,\"result\":{\"true_in_model\":false}}"]),
  ("axiom_check self_awareness for a player with no doxastic map: internal_error \
    (gamen-hs crashes)",
    (runSession [build "m" noDoxModel,
      "{\"id\":\"2\",\"op\":\"axiom_check\",\"handle\":\"m\",\"axioms\":[\"self_awareness\"]}"]).getD 1 ""
      == "{\"error\":{\"code\":\"internal_error\",\"message\":\"doxasticSuccessors: agent \
            \\\"p1\\\" is not in model\"},\"id\":\"2\",\"ok\":false}"),
  ("axiom_check with max_violations 0 on a violated axiom: satisfied false, no list \
    (gamen-hs: satisfied true)",
    (runSession [build "m" selfAwareBad,
      "{\"id\":\"2\",\"op\":\"axiom_check\",\"handle\":\"m\",\"axioms\":[\"self_awareness\"],\
        \"max_violations\":0}"]).getD 1 ""
      == "{\"id\":\"2\",\"ok\":true,\"result\":{\"self_awareness\":{\"satisfied\":false,\
           \"violations\":[]}}}"),
  ("axiom_check with max_violations -1 on a violated axiom: satisfied false",
    (runSession [build "m" selfAwareBad,
      "{\"id\":\"2\",\"op\":\"axiom_check\",\"handle\":\"m\",\"axioms\":[\"self_awareness\"],\
        \"max_violations\":-1}"]).getD 1 ""
      == "{\"id\":\"2\",\"ok\":true,\"result\":{\"self_awareness\":{\"satisfied\":false,\
           \"violations\":[]}}}"),
  ("axiom_check with max_violations 0 on a satisfied axiom: satisfied true",
    (runSession [build "m" validJson,
      "{\"id\":\"2\",\"op\":\"axiom_check\",\"handle\":\"m\",\"axioms\":[\"self_awareness\"],\
        \"max_violations\":0}"]).getD 1 ""
      == "{\"id\":\"2\",\"ok\":true,\"result\":{\"self_awareness\":{\"satisfied\":true}}}"),
  ("build rejects a history playing an unlisted move: premises fail Contemporary \
    Universality (gamen-hs builds it)",
    match decodeV offMoveModel with
    | some j => match parseAndBuildModel j false with
      | .error (.buildInvalid vs) => vs.any (·.contains "Contemporary Universality")
      | _ => false
    | none => false),
  ("encode: numbers as Data.Scientific prints them (aeson)",
    (decodeV "[1.5,1e10,0.01,12345678.9,1e-2,-3,0.1,1.0,100,-0.5e-3,0.0,1234567.5]").map encode
      == some "[1.5,10000000000,1.0e-2,1.23456789e7,1.0e-2,-3,0.1,1.0,100,-5.0e-4,0.0,1234567.5]"),
  ("encode: string escapes as aeson's",
    (decodeV "\"\\b\\f\\n\\r\\t\\u001f\\\"\\\\é/\"").map encode
      == some "\"\\u0008\\u000c\\n\\r\\t\\u001f\\\"\\\\é/\""),
  ("parseInt: aeson's messages for a float, an overflow, and a string; 2^63-1 accepted",
    ((decodeV "1.5").map parseInt |>.map (·.toOption)) == some none
      && (match (decodeV "1.5").map parseInt with
          | some (.error e) => e == "parsing Int failed, value is either floating or will \
              cause over or underflow 1.5"
          | _ => false)
      && (match (decodeV "9223372036854775808").map parseInt with
          | some (.error e) => e == "parsing Int failed, value is either floating or will \
              cause over or underflow 9.223372036854775808e18"
          | _ => false)
      && (match (decodeV "\"1\"").map parseInt with
          | some (.error e) => e == "parsing Int failed, expected Number, but encountered String"
          | _ => false)
      && (match (decodeV "9223372036854775807").map parseInt with
          | some (.ok v) => v == 9223372036854775807
          | _ => false)
      && (match (decodeV "1e2").map parseInt with
          | some (.ok v) => v == 100
          | _ => false)) ]

def cases : IO (List (String × Bool)) := do
  return task18Cases ++ protocolSpecCases ++ (← goldenCases) ++ extensionCases

end DclegServiceTests
