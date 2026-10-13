import Validate.Core

/-!
# ATL-D (`Gamen.Atl.Dynamic`, the `"dynamic": true` form of `atl_model_check`)

Source: Galimullin, Grosinger & Mittelmann, KR 2026 (doi:10.24963/kr.2026/31).
Example 1 (the oxygen tank, Figures 1-2) is rebuilt from the figures, not from
extracted text. Plan: `plans/atl-d-2026-10-13.md`.

Model: states q0 (salon, start), q1 (Bob's room, `atBob`), q2 (balcony, `warm`).
Both robots moving left goes q0→q2→q1→q0, both right the other way; mixed
moves stay put. r1 has left and right, r2 only left, so the two "both right"
transitions are the paper's dotted (disabled) ones.
-/

namespace AtlDynamicTests

open Lean (Json)
open Gamen Gamen.Atl.Dynamic

def edge (st nx a b : String) : String :=
  s!"\{\"state\":\"{st}\",\"moves\":\{\"r1\":\"{a}\",\"r2\":\"{b}\"},\"next\":\"{nx}\"}"

/-- Transitions for the two "both same direction" joint moves; mixed moves are
covered by `default_next` (stay) or, in `modelNoDefault`, by an explicit stay. -/
def cycle : List String :=
  [edge "q0" "q2" "left" "left", edge "q2" "q1" "left" "left", edge "q1" "q0" "left" "left",
   edge "q0" "q1" "right" "right", edge "q1" "q2" "right" "right", edge "q2" "q0" "right" "right"]

def movesJ : String :=
  "{\"q0\":{\"r1\":[\"left\",\"right\"],\"r2\":[\"left\"]},\
    \"q1\":{\"r1\":[\"left\",\"right\"],\"r2\":[\"left\"]},\
    \"q2\":{\"r1\":[\"left\",\"right\"],\"r2\":[\"left\"]}}"

def header : String :=
  "{\"states\":[\"q0\",\"q1\",\"q2\"],\"agents\":[\"r1\",\"r2\"],\"actions\":[\"left\",\"right\"],\
    \"moves\":" ++ movesJ ++ ",\"valuation\":{\"q1\":[\"atBob\"],\"q2\":[\"warm\"]},"

/-- With `default_next: stay`, the unlisted mixed moves stay put. -/
def modelDefault : String :=
  header ++ "\"default_next\":{\"stay\":true},\"transitions\":[" ++ ",".intercalate cycle ++ "]}"

/-- Without a default: only the available joint moves are listed, so granting
`right` to r2 enables moves with no stated successor. -/
def modelNoDefault : String :=
  header ++ "\"transitions\":[" ++
    ",".intercalate ([edge "q0" "q2" "left" "left", edge "q2" "q1" "left" "left",
      edge "q1" "q0" "left" "left", edge "q0" "q0" "right" "left",
      edge "q1" "q1" "right" "left", edge "q2" "q2" "right" "left"]) ++ "]}"

def load (s : String) : Except String DynModel :=
  match Json.parse s with
  | .error e => .error e
  | .ok j => (CgsJson.decodeDyn j).mapError (·.message)

open DFormula in
def atBob : DFormula := .atom "atBob"
def team : List String := ["r1", "r2"]
def grantRight : UpdateList := .cons (.not .bot) "right" ["r2"] .nil
def revokeLeftR1 : UpdateList := .cons (.not (.atom "atBob")) "left" ["r1"] .nil

def sats (s : String) (f : DFormula) : Option (List String) :=
  match load s with
  | .ok m => match dsat m f with | .ok r => some r.toList | .error _ => none
  | .error _ => none

def errs (s : String) (f : DFormula) : Bool :=
  match load s with
  | .ok m => match dsat m f with | .error _ => true | .ok _ => false
  | .error _ => false

/-- The paper's first formula. -/
def f1 : DFormula :=
  .and (.not (.has "r2" "right"))
    (.grant grantRight (.and (.has "r2" "right") (.canNext team atBob)))

/-- The paper's second formula: after granting `right` to r2 and revoking `left`
from r1 at non-`atBob` states, always `atBob R ¬warm`. -/
def f2 : DFormula :=
  .grant grantRight (.revoke revokeLeftR1 (.canRelease [] atBob (.not (.atom "warm"))))

/-- The same without the revocation: the balcony is reachable first. -/
def f2NoRevoke : DFormula :=
  .grant grantRight (.canRelease [] atBob (.not (.atom "warm")))

def all3 : List String := ["q0", "q1", "q2"]

def req (formula : String) (model : String := modelDefault) : String :=
  "{\"action\":\"atl_model_check\",\"dynamic\":true,\"model\":" ++ model
    ++ ",\"formulas\":[" ++ formula ++ "]}"

def code (r : Json) : Option String :=
  (r.getObjVal? "error_code").toOption >>= (·.getStr?.toOption)

def cases : List (String × Bool) := [
  ("ATL-D Example 1: ⟨⟨r1,r2⟩⟩F atBob holds at q0 (left twice)",
    (sats modelDefault (.canEventually team atBob)).map (·.contains "q0") == some true),
  ("ATL-D Example 1: ⟨⟨r1,r2⟩⟩X atBob fails at q0 before the grant (right,right is disabled)",
    (sats modelDefault (.canNext team atBob)).map (·.contains "q0") == some false),
  ("ATL-D Example 1: ¬has(r2,right) ∧ [⊤:right→{r2}]+(has ∧ ⟨⟨r1,r2⟩⟩X atBob) holds at every state",
    sats modelDefault f1 == some all3),
  ("ATL-D Example 1: [grant][revoke] ⟨⟨∅⟩⟩ atBob R ¬warm holds at q0",
    (sats modelDefault f2).map (·.contains "q0") == some true),
  ("ATL-D Example 1: without the revocation the same formula fails at q0 (balcony first)",
    (sats modelDefault f2NoRevoke).map (·.contains "q0") == some false),
  ("ATL-D: has(r1,left) holds everywhere; after revoking left from r1 at ¬atBob, only at q1",
    sats modelDefault (.has "r1" "left") == some all3
      && sats modelDefault (.revoke revokeLeftR1 (.has "r1" "left")) == some ["q1"]),
  ("ATL-D: reasonableness — revoking r2's only action leaves r2 with it",
    sats modelDefault (.revoke (.cons (.not .bot) "left" ["r2"] .nil) (.has "r2" "left")) == some all3),
  ("ATL-D: revoking everything r1 has leaves r1 with left and right (reasonableness)",
    sats modelDefault
      (.revoke (.cons (.not .bot) "left" ["r1"] (.cons (.not .bot) "right" ["r1"] .nil))
        (.and (.has "r1" "left") (.has "r1" "right"))) == some all3),
  ("ATL-D: an update is simultaneous — the second condition is read before the first clause applies",
    -- `jump` exists but nobody has it. Clause 1 grants r2 `right`; clause 2 grants r1 `jump`
    -- where r2 has `right`. Read in the *current* model r2 lacks `right` everywhere, so r1 gets
    -- nothing; a chained update would grant `jump` everywhere.
    let withJump := modelDefault.replace "\"actions\":[\"left\",\"right\"]" "\"actions\":[\"left\",\"right\",\"jump\"]"
    let simult := UpdateList.cons (.not .bot) "right" ["r2"] (.cons (.has "r2" "right") "jump" ["r1"] .nil)
    let chained := (UpdateList.cons (.not .bot) "right" ["r2"] .nil)
    sats withJump (.grant simult (.has "r1" "jump")) == some []
      && sats withJump (.grant chained (.grant (.cons (.has "r2" "right") "jump" ["r1"] .nil) (.has "r1" "jump")))
        == some all3),
  ("ATL-D: grant is idempotent",
    sats modelDefault (.grant grantRight (.grant grantRight (.has "r2" "right")))
      == sats modelDefault (.grant grantRight (.has "r2" "right"))),
  ("ATL-D: ⟨⟨A⟩⟩Gφ equals ⟨⟨A⟩⟩(⊥ R φ)",
    sats modelDefault (.grant grantRight (.canAlways team (.not (.atom "warm"))))
      == sats modelDefault (.grant grantRight (.canRelease team .bot (.not (.atom "warm"))))),
  ("ATL-D: update-free formulas agree with Gamen.Atl.sat",
    match load modelDefault with
    | .ok m =>
      [(DFormula.canEventually team atBob, Formula.canEventually team (.atom "atBob")),
       (.canNext team atBob, .canNext team (.atom "atBob")),
       (.canAlways ["r1"] (.not (.atom "warm")), .canAlways ["r1"] (.not (.atom "warm"))),
       (.canUntil team (.not (.atom "warm")) atBob, .canUntil team (.not (.atom "warm")) (.atom "atBob")),
       (.canNext [] (.or atBob (.atom "warm")), .canNext [] (.or (.atom "atBob") (.atom "warm"))),
       (.implies atBob (.atom "warm"), .implies (.atom "atBob") (.atom "warm"))].all fun (d, f) =>
        match dsat m d, sat m.cgs f with
        | .ok a, .ok b => a == b
        | _, _ => false
    | .error _ => false),
  ("ATL-D: an update enabling a joint move with no stated successor is an error, never a default",
    errs modelNoDefault (.grant grantRight (.has "r2" "right"))),
  ("ATL-D: the same model without updates is fine",
    (sats modelNoDefault (.canEventually team atBob)).isSome),
  ("ATL-D: unknown action in has is an error",
    errs modelDefault (.has "r2" "fly")),
  ("ATL-D: unknown agent in an update is an error",
    errs modelDefault (.grant (.cons (.not .bot) "right" ["r9"] .nil) .bot)),
  ("ATL-D: unknown action in an update is an error",
    errs modelDefault (.grant (.cons (.not .bot) "fly" ["r2"] .nil) .bot)),
  ("atl_model_check dynamic: Example 1's first formula over the wire",
    let r := processLine (req
      ("{\"type\":\"and\",\"left\":{\"type\":\"not\",\"operand\":{\"type\":\"has\",\"agent\":\"r2\",\"action\":\"right\"}},\
        \"right\":{\"type\":\"grant\",\"updates\":[{\"condition\":{\"type\":\"not\",\"operand\":{\"type\":\"bot\"}},\
        \"action\":\"right\",\"agents\":[\"r2\"]}],\"operand\":{\"type\":\"and\",\
        \"left\":{\"type\":\"has\",\"agent\":\"r2\",\"action\":\"right\"},\
        \"right\":{\"type\":\"can_next\",\"agents\":[\"r1\",\"r2\"],\"operand\":{\"type\":\"atom\",\"name\":\"atBob\"}}}}}")) "t"
    (r.compress.splitOn "\"satisfying\":[\"q0\",\"q1\",\"q2\"]").length == 2),
  ("atl_model_check dynamic: imperfect semantics are rejected with a code",
    code (processLine
      ("{\"action\":\"atl_model_check\",\"dynamic\":true,\"semantics\":\"imperfect_subjective\",\"model\":"
        ++ modelDefault ++ ",\"formulas\":[]}") "t") == some "unsupported_semantics"),
  ("atl_model_check dynamic: an undeclared available action is an unknown_action error",
    code (processLine (req "{\"type\":\"bot\"}"
      ((modelDefault.replace "\"actions\":[\"left\",\"right\"]" "\"actions\":[\"left\"]"))) "t")
      == some "unknown_action"),
  ("atl_model_check: a transition using a granted action is accepted only with `actions`",
    code (processLine (req "{\"type\":\"bot\"}"
      (modelDefault.replace "\"actions\":[\"left\",\"right\"]," "")) "t") == some "unknown_move")
]

end AtlDynamicTests
