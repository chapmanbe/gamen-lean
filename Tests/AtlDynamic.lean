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
def grantRight : UpdateList := .cons (.not .bot) "right" ["r2"] [] .nil
def revokeLeftR1 : UpdateList := .cons (.not (.atom "atBob")) "left" ["r1"] [] .nil

def sats (s : String) (f : DFormula) : Option (List String) :=
  match load s with
  | .ok m => match dsat m .perfect f with | .ok r => some r.toList | .error _ => none
  | .error _ => none

def errs (s : String) (f : DFormula) : Bool :=
  match load s with
  | .ok m => match dsat m .perfect f with | .error _ => true | .ok _ => false
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

/-! ## ATEL-D

`a` cannot tell s0 (`p`) from s1. At s0 action `x` reaches the goal `g`, at s1 action
`y` does; `w` exists but nobody has it. -/

def epiModel : String :=
  "{\"states\":[\"s0\",\"s1\",\"g\"],\"agents\":[\"a\"],\"actions\":[\"x\",\"y\",\"w\"],\
    \"moves\":{\"s0\":{\"a\":[\"x\",\"y\"]},\"s1\":{\"a\":[\"x\",\"y\"]},\"g\":{\"a\":[\"x\",\"y\"]}},\
    \"valuation\":{\"s0\":[\"p\"],\"g\":[\"goal\"]},\"default_next\":{\"stay\":true},\
    \"transitions\":[\
      {\"state\":\"s0\",\"moves\":{\"a\":\"x\"},\"next\":\"g\"},\
      {\"state\":\"s1\",\"moves\":{\"a\":\"y\"},\"next\":\"g\"},\
      {\"state\":\"g\",\"moves\":{\"a\":\"x\"},\"next\":\"g\"},\
      {\"state\":\"g\",\"moves\":{\"a\":\"y\"},\"next\":\"g\"}],\
    \"indistinguishable\":{\"a\":[[\"s0\",\"s1\"]]}}"

def satMode (mode : IrMode) (f : DFormula) : Option (List String) :=
  match load epiModel with
  | .ok m => match dsat m mode f with | .ok r => some r.toList | .error _ => none
  | .error _ => none

def goalNext : DFormula := .canNext ["a"] (.atom "goal")
def p : DFormula := .atom "p"
/-- `[p : w → A, B]+`. -/
def informP (granted informed : List String) : UpdateList := .cons p "w" granted informed .nil

/-! ## ATEL-D Example 2 (extended version, Fig. 5)

The oxygen-tank model with partial observation: r2 tells the balcony (q2) from the
inside rooms, r1 tells Bob's room (q1) from the rest. The extended version's text
states "no uniform strategy … from all states the robots consider indistinguishable",
which is the subjective reading. -/

def modelImp : String :=
  (modelDefault.dropEnd 1).toString
    ++ ",\"indistinguishable\":{\"r1\":[[\"q0\",\"q2\"],[\"q1\"]],\"r2\":[[\"q0\",\"q1\"],[\"q2\"]]}}"

def satImp (f : DFormula) : Option (List String) :=
  match load modelImp with
  | .ok m => match dsat m .subjective f with | .ok r => some r.toList | .error _ => none
  | .error _ => none

def holdsQ0 (f : DFormula) : Option Bool := (satImp f).map (·.contains "q0")

def xAtBob : DFormula := .canNext team atBob
def warmP : DFormula := .atom "warm"
/-- `[¬atBob ∧ ¬warm : right → {r2}, {r1}]+`. -/
def sharpUpd : UpdateList :=
  .cons (.and (.not atBob) (.not warmP)) "right" ["r2"] ["r1"] .nil

/-! ## Social laws (Galimullin & Kuijer 2024, SLAM; ATL-D paper Theorem 4)

An atomic law `ζ(α, a) = φ` allows `a` to take `α` exactly where `φ` holds in the
current model; if that would forbid everything an agent has at a state, the law does
not apply there. Theorem 4: `[ζ]ψ` is `[¬φ1 : α1 → {a1}, …]− ψ`. The law-restricted
model below is built straight from the SLAM definition, not from `updateModel`. -/

abbrev Law := String × String × Formula × DFormula   -- action, agent, condition (both forms)

def lawModel (m : DynModel) (laws : List Law) : Except String (Cgs String String) := do
  let mut allowed : List (String × String × Std.TreeSet String) := []
  for (α, a, c, _) in laws do
    allowed := (α, a, ← sat m.cgs c) :: allowed
  let moves : String → String → Std.TreeSet String := fun v a =>
    let d := m.cgs.cgsMoves v a
    let ok := d.filter fun α =>
      allowed.all fun (α', a', s) => !(α' == α && a' == a) || s.contains v
    if ok.isEmpty then d else ok
  pure { m.cgs with cgsMoves := moves }

def lawUpdate (laws : List Law) : UpdateList :=
  laws.foldr (fun (α, a, _, d) rest => .cons (.not d) α [a] [] rest) .nil

/-- `[ζ]ψ` (restricted model) and `[π_ζ]−ψ` agree, for ψ given in both forms. -/
def theorem4 (modelJson : String) (laws : List Law) (ψ : Formula × DFormula) : Bool :=
  match load modelJson with
  | .ok m =>
    match lawModel m laws, sat (match lawModel m laws with | .ok c => c | .error _ => m.cgs) ψ.1,
        dsat m .perfect (.revoke (lawUpdate laws) ψ.2) with
    | .ok _, .ok a, .ok b => a == b
    | _, _, _ => false
  | .error _ => false

def atomF (n : String) : Formula × DFormula := (.atom n, .atom n)
def fEv : Formula × DFormula :=
  (.canEventually ["r1", "r2"] (.atom "atBob"), .canEventually team atBob)
def fSafe : Formula × DFormula :=
  (.canAlways [] (.not (.atom "warm")), .canAlways [] (.not warmP))
def fNext : Formula × DFormula :=
  (.canNext ["r1"] (.atom "atBob"), .canNext ["r1"] atBob)
def fUntil : Formula × DFormula :=
  (.canUntil ["r1", "r2"] (.not (.atom "warm")) (.atom "atBob"), .canUntil team (.not warmP) atBob)

def lawsA : List Law := [("left", "r1", .atom "atBob", atBob)]
def lawsB : List Law := [("right", "r1", .not (.atom "warm"), .not warmP),
                         ("left", "r1", .atom "atBob", atBob)]
/-- An ATL condition, and a law forbidding all of r2's actions at the non-`atBob` states. -/
def lawsC : List Law := [("left", "r1", .canNext ["r1", "r2"] (.atom "atBob"), xAtBob),
                         ("left", "r2", .atom "atBob", atBob)]

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
    sats modelDefault (.revoke (.cons (.not .bot) "left" ["r2"] [] .nil) (.has "r2" "left")) == some all3),
  ("ATL-D: revoking everything r1 has leaves r1 with left and right (reasonableness)",
    sats modelDefault
      (.revoke (.cons (.not .bot) "left" ["r1"] [] (.cons (.not .bot) "right" ["r1"] [] .nil))
        (.and (.has "r1" "left") (.has "r1" "right"))) == some all3),
  ("ATL-D: an update is simultaneous — the second condition is read before the first clause applies",
    -- `jump` exists but nobody has it. Clause 1 grants r2 `right`; clause 2 grants r1 `jump`
    -- where r2 has `right`. Read in the *current* model r2 lacks `right` everywhere, so r1 gets
    -- nothing; a chained update would grant `jump` everywhere.
    let withJump := modelDefault.replace "\"actions\":[\"left\",\"right\"]" "\"actions\":[\"left\",\"right\",\"jump\"]"
    let simult := UpdateList.cons (.not .bot) "right" ["r2"] [] (.cons (.has "r2" "right") "jump" ["r1"] [] .nil)
    let chained := (UpdateList.cons (.not .bot) "right" ["r2"] [] .nil)
    sats withJump (.grant simult (.has "r1" "jump")) == some []
      && sats withJump (.grant chained (.grant (.cons (.has "r2" "right") "jump" ["r1"] [] .nil) (.has "r1" "jump")))
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
        match dsat m .perfect d, sat m.cgs f with
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
    errs modelDefault (.grant (.cons (.not .bot) "right" ["r9"] [] .nil) .bot)),
  ("ATL-D: unknown action in an update is an error",
    errs modelDefault (.grant (.cons (.not .bot) "fly" ["r2"] [] .nil) .bot)),
  ("atl_model_check dynamic: Example 1's first formula over the wire",
    let r := processLine (req
      ("{\"type\":\"and\",\"left\":{\"type\":\"not\",\"operand\":{\"type\":\"has\",\"agent\":\"r2\",\"action\":\"right\"}},\
        \"right\":{\"type\":\"grant\",\"updates\":[{\"condition\":{\"type\":\"not\",\"operand\":{\"type\":\"bot\"}},\
        \"action\":\"right\",\"agents\":[\"r2\"]}],\"operand\":{\"type\":\"and\",\
        \"left\":{\"type\":\"has\",\"agent\":\"r2\",\"action\":\"right\"},\
        \"right\":{\"type\":\"can_next\",\"agents\":[\"r1\",\"r2\"],\"operand\":{\"type\":\"atom\",\"name\":\"atBob\"}}}}}")) "t"
    (r.compress.splitOn "\"satisfying\":[\"q0\",\"q1\",\"q2\"]").length == 2),
  ("atl_model_check dynamic: an undeclared available action is an unknown_action error",
    code (processLine (req "{\"type\":\"bot\"}"
      ((modelDefault.replace "\"actions\":[\"left\",\"right\"]" "\"actions\":[\"left\"]"))) "t")
      == some "unknown_action"),
  ("atl_model_check: a transition using a granted action is accepted only with `actions`",
    code (processLine (req "{\"type\":\"bot\"}"
      (modelDefault.replace "\"actions\":[\"left\",\"right\"]," "")) "t") == some "unknown_move"),
  ("ATEL-D: ⟨⟨a⟩⟩X goal under perfect information holds everywhere",
    satMode .perfect goalNext == some ["g", "s0", "s1"]),
  ("ATEL-D: subjectively a cannot (it must choose one action for s0 and s1)",
    satMode .subjective goalNext == some ["g"]),
  ("ATEL-D: objectively a can at s0 and s1 (a different uniform strategy for each)",
    satMode .objective goalNext == some ["g", "s0", "s1"]),
  ("ATEL-D: K_a p fails where a cannot tell p from ¬p; K_a ¬p holds only at g",
    satMode .subjective (.knows "a" p) == some []
      && satMode .subjective (.knows "a" (.not p)) == some ["g"]),
  ("ATEL-D: informing a of p (B = {a}) lets a tell s0 from s1: K_a p ∨ K_a ¬p everywhere",
    satMode .subjective (.grant (informP [] ["a"]) (.or (.knows "a" p) (.knows "a" (.not p))))
      == some ["g", "s0", "s1"]),
  ("ATEL-D: an update that informs nobody leaves a's knowledge alone",
    satMode .subjective (.grant (informP [] []) (.or (.knows "a" p) (.knows "a" (.not p))))
      == some ["g"]),
  ("ATEL-D: granting w to a at p-states informs a too (a ∈ A), and K_a p then holds at s0",
    satMode .subjective (.grant (informP ["a"] []) (.knows "a" p)) == some ["s0"]),
  ("ATEL-D: after the informing update a can subjectively reach the goal everywhere",
    satMode .subjective (.grant (informP [] ["a"]) goalNext) == some ["g", "s0", "s1"]),
  ("ATEL-D: the same update without informing does not help",
    satMode .subjective (.grant (informP [] []) goalNext) == some ["g"]),
  ("ATEL-D: a revoke that informs also refines (revoke y from a at p-states, a informed)",
    satMode .subjective
      (.revoke (.cons p "y" [] ["a"] .nil) (.or (.knows "a" p) (.knows "a" (.not p))))
      == some ["g", "s0", "s1"]),
  ("ATEL-D: refinement keeps ∼ an equivalence with uniform moves (mkAtelModel accepts it)",
    match load epiModel with
    | .ok m =>
      match (dclauses m .subjective (informP ["a"] [])) with
      | .ok cl => (mkAtelModel (updateModel m true cl).cgs (updateModel m true cl).epistemic).isOk
      | .error _ => false
    | .error _ => false),
  ("ATEL-D: unknown agent in `informed` is an error",
    (match load epiModel with
     | .ok m => (dsat m .subjective (.grant (informP [] ["z"]) .bot)).isOk == false
     | .error _ => false)),
  ("atl_model_check dynamic: subjective semantics over the wire, with informed",
    let r := processLine ("{\"action\":\"atl_model_check\",\"dynamic\":true,\"semantics\":\"imperfect_subjective\",\"model\":"
      ++ epiModel ++ ",\"formulas\":[{\"type\":\"grant\",\"updates\":[{\"condition\":{\"type\":\"atom\",\"name\":\"p\"},\
        \"action\":\"w\",\"agents\":[],\"informed\":[\"a\"]}],\"operand\":{\"type\":\"can_next\",\"agents\":[\"a\"],\
        \"operand\":{\"type\":\"atom\",\"name\":\"goal\"}}}]}") "t"
    (r.compress.splitOn "\"satisfying\":[\"g\",\"s0\",\"s1\"]").length == 2
      && (r.compress.splitOn "imperfect_subjective_dynamic").length == 2),
  ("ATEL-D Example 2: at q0 the robots cannot reach Bob in one step, and both know it",
    holdsQ0 (.and (.not xAtBob) (.and (.knows "r1" (.not xAtBob)) (.knows "r2" (.not xAtBob)))) == some true),
  ("ATEL-D Example 2: granting right to r2 everywhere and informing everyone does not help",
    holdsQ0 (.grant (.cons (.not .bot) "right" ["r2"] ["r1", "r2"] .nil) xAtBob) == some false),
  ("ATEL-D Example 2: granting right to r2 outside Bob's room, informing only r2, does not help (r1 is unsure)",
    holdsQ0 (.grant (.cons (.not atBob) "right" ["r2"] [] .nil) xAtBob) == some false),
  ("ATEL-D Example 2: [¬atBob ∧ ¬warm : right → {r2}, {r1}]+ ⟨⟨r1,r2⟩⟩X atBob holds at every state",
    satImp (.grant sharpUpd xAtBob) == some all3),
  ("ATEL-D Example 2: each robot knows it cannot reach Bob now but could after that update",
    ["r1", "r2"].all fun r =>
      holdsQ0 (.and (.knows r (.not xAtBob)) (.knows r (.grant sharpUpd xAtBob))) == some true),
  ("ATEL-D: [φ : α → ∅, Ag]+ is a public announcement of φ (everyone then knows φ's truth value)",
    satImp (.grant (.cons atBob "left" [] ["r1", "r2"] .nil) (.or (.knows "r2" atBob) (.knows "r2" (.not atBob))))
      == some all3),
  ("SLAM/Thm 4: [ζ]ψ agrees with [π_ζ]−ψ (one law, four formulas)",
    [fEv, fSafe, fNext, fUntil].all (theorem4 modelDefault lawsA)),
  ("SLAM/Thm 4: two laws on one agent",
    [fEv, fSafe, fNext, fUntil].all (theorem4 modelDefault lawsB)),
  ("SLAM/Thm 4: an ATL condition, and a law that forbids all of r2's actions (reasonableness)",
    [fEv, fSafe, fNext, fUntil].all (theorem4 modelDefault lawsC)),
  ("SLAM/Thm 4: the laws actually change something (so the agreement is not vacuous)",
    match load modelDefault with
    | .ok m =>
      match lawModel m lawsB with
      | .ok c => (sat c fEv.1).toOption != (sat m.cgs fEv.1).toOption
          || (sat c fSafe.1).toOption != (sat m.cgs fSafe.1).toOption
      | .error _ => false
    | .error _ => false),
  ("review: an unknown agent in a coalition operator is an error, not a silent empty set",
    errs modelDefault (.canNext ["r9"] atBob) && errs modelDefault (.canNext ["r1", "r9"] atBob)),
  ("review: perfect semantics on a model with indistinguishable states is refused (semantics_mismatch); imperfect_subjective is accepted",
    let f := "{\"type\":\"knowledge\",\"agent\":\"a\",\"operand\":{\"type\":\"atom\",\"name\":\"p\"}}"
    let q (sem : String) := processLine ("{\"action\":\"atl_model_check\",\"dynamic\":true" ++ sem ++ ",\"model\":"
      ++ epiModel ++ ",\"formulas\":[" ++ f ++ "]}") "t"
    code (q "") == some "semantics_mismatch"
      && code (q ",\"semantics\":\"imperfect_subjective\"") == none),
  ("review: \"dynamic\" must be a boolean — \"true\" does not silently select the static reader",
    ((processLine ("{\"action\":\"atl_model_check\",\"dynamic\":\"true\",\"model\":" ++ modelDefault
      ++ ",\"formulas\":[]}") "t").compress.splitOn "must be true or false").length == 2),
  ("review: an empty update list is rejected (Def 1: at least one clause)",
    ((processLine ("{\"action\":\"atl_model_check\",\"dynamic\":true,\"model\":" ++ modelDefault
      ++ ",\"formulas\":[{\"type\":\"grant\",\"updates\":[],\"operand\":{\"type\":\"bot\"}}]}") "t").compress.splitOn "at least one clause").length == 2),
  ("review: default_next with both stay and state is malformed_spec; [[s0,s0]] is overlapping_classes",
    code (processLine ("{\"action\":\"atl_model_check\",\"dynamic\":true,\"model\":"
      ++ modelDefault.replace "\"default_next\":{\"stay\":true}" "\"default_next\":{\"stay\":true,\"state\":\"q0\"}"
      ++ ",\"formulas\":[]}") "t") == some "malformed_spec"
      && code (processLine ("{\"action\":\"atl_model_check\",\"dynamic\":true,\"semantics\":\"imperfect_subjective\",\"model\":"
        ++ epiModel.replace "[[\"s0\",\"s1\"]]" "[[\"s0\",\"s0\"]]" ++ ",\"formulas\":[]}") "t") == some "overlapping_classes"),
  ("review: the no-stated-successor failure is that error, not some other (message checked)",
    match load modelNoDefault with
    | .ok m => match dsat m .perfect (.grant grantRight (.has "r2" "right")) with
      | .error msg => (msg.splitOn "no stated successor").length == 2
      | .ok _ => false
    | .error _ => false),
  ("review: revoke, knowledge, can_release and a default_next state travel over the wire",
    let model := epiModel.replace "\"default_next\":{\"stay\":true}" "\"default_next\":{\"state\":\"g\"}"
    let fs := "{\"type\":\"revoke\",\"updates\":[{\"condition\":{\"type\":\"atom\",\"name\":\"p\"},\"action\":\"x\",\"agents\":[\"a\"],\"informed\":null}],\
      \"operand\":{\"type\":\"can_release\",\"agents\":[],\"left\":{\"type\":\"atom\",\"name\":\"goal\"},\"right\":{\"type\":\"not\",\"operand\":{\"type\":\"bot\"}}}}"
    let r := processLine ("{\"action\":\"atl_model_check\",\"dynamic\":true,\"semantics\":\"imperfect_subjective\",\"model\":"
      ++ model ++ ",\"formulas\":[" ++ fs ++ "]}") "t"
    (r.compress.splitOn "\"ok\":true").length == 2),
  ("review: an empty indistinguishability class [[]] is malformed_spec in the CGS codec",
    code (processLine ("{\"action\":\"atl_model_check\",\"dynamic\":true,\"semantics\":\"imperfect_subjective\",\"model\":"
      ++ epiModel.replace "[[\"s0\",\"s1\"]]" "[[]]" ++ ",\"formulas\":[]}") "t") == some "malformed_spec")
]

end AtlDynamicTests
