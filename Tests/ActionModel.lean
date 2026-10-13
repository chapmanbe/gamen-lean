import Gamen.ActionModel
import Tests.AtlDynamic

/-!
# `Gamen.ActionModel` (DEL action models, product update; issue #3 item 3)

Answer keys: Lorini, Perrotin & Schwarzentruber, KR 2022, Examples 1-3 (Fig. 1).
Cross-checks: a public-announcement action model against the existing `[B]C`
(B&D Def 15.11); a semi-private "whether" announcement against ATEL-D's informing
update (`Gamen.Atl.Dynamic`), which should agree on knowledge.
-/

namespace ActionModelTests

open Gamen

def holds (r : Except String Bool) (b : Bool) : Bool :=
  match r with | .ok x => x == b | .error _ => false
def fails {α : Type} (r : Except String α) : Bool :=
  match r with | .error _ => true | .ok _ => false

def p : Formula := .atom "p"
def q : Formula := .atom "q"
def kn (a : String) (f : Formula) : Formula := .knowledge a f

def full (ws : List String) : List (String × String) := ws.flatMap fun a => ws.map fun b => (a, b)

/-! ## Lorini et al., Figure 1 -/

/-- Worlds `w` (where `p` holds) and `u`, indistinguishable for `i` and `j`. -/
def loriniM : EpistemicModel :=
  mkEpistemicModel
    (mkEpistemicFrame ["w", "u"] [("i", full ["w", "u"]), ("j", full ["w", "u"])])
    [("p", ["w"])]

/-- Event `a` (pre `p`, post `p ← ⊥`) is the only one `i` considers; `j` thinks `a0`
(nothing) happened. -/
def loriniA : Except String ActionModel :=
  mkActionModel ["a", "a0"] ["i", "j"]
    [("i", [("a", "a"), ("a0", "a0")]), ("j", [("a", "a0"), ("a0", "a0")])]
    [("a", p)] [("a", [("p", .bot)])]

def withA (f : ActionModel → Bool) : Bool :=
  match loriniA with | .ok am => f am | .error _ => false

/-! ## A small two-agent model for the cross-checks -/

def m2 : EpistemicModel :=
  mkEpistemicModel
    (mkEpistemicFrame ["w1", "w2", "w3"]
      [("a", full ["w1", "w2"] ++ [("w3", "w3")]),
       ("b", full ["w2", "w3"] ++ [("w1", "w1")])])
    [("p", ["w1", "w2"]), ("q", ["w2", "w3"])]

def probes : List Formula :=
  [kn "a" q, kn "b" p, .not (kn "a" (kn "b" q)), .or q (kn "b" (.not p)),
   kn "a" (.implies p q), .and p (.not (kn "a" p))]

/-- Two worlds, `p` on `s0`; both agents unsure. -/
def m3 : EpistemicModel :=
  mkEpistemicModel
    (mkEpistemicFrame ["s0", "s1"] [("a", full ["s0", "s1"]), ("b", full ["s0", "s1"])])
    [("p", ["s0"])]

def cases : List (String × Bool) := [
  ("Lorini Ex. 3: M × A has worlds (w,a), (w,a0), (u,a0) — (u,a) fails the precondition p",
    withA fun am => match productUpdate loriniM am with
      | .ok n => n.eFrame.eWorlds.toList == ["u×a0", "w×a", "w×a0"]
      | .error _ => false),
  ("Lorini Ex. 3: p holds only at (w,a0) — the assignment of a makes it false at (w,a)",
    withA fun am => match productUpdate loriniM am with
      | .ok n => (n.eValuation.getD ⟨"p"⟩ ∅).toList == ["w×a0"]
      | .error _ => false),
  ("Lorini Ex. 2: after a, i knows ¬p; j neither knows p nor ¬p (private announcement + assignment)",
    withA fun am =>
      holds (eSatisfiesAfter loriniM "w" am "a"
        (.and (kn "i" (.not p)) (.and (.not (kn "j" p)) (.not (kn "j" (.not p)))))) true),
  ("Lorini: a is not executable at u (p is false there); the box form is vacuously true",
    withA fun am => holds (eSatisfiesAfter loriniM "u" am "a" .top) false
      && holds (eSatisfiesBoxAfter loriniM "u" am "a" .bot) true),
  ("public announcement action model agrees with [B]C at every world, for six formulas",
    match publicAnnouncement ["a", "b"] p with
    | .ok am => ["w1", "w2", "w3"].all fun w => probes.all fun ψ =>
        match eSatisfies m2 w (.announce p ψ), eSatisfiesBoxAfter m2 w am "!" ψ with
        | .ok x, .ok y => x == y
        | _, _ => false
    | .error _ => false),
  ("public announcement: the product is M|p, i.e. exactly the p-worlds, renamed",
    match publicAnnouncement ["a", "b"] p with
    | .ok am => match productUpdate m2 am with
      | .ok n => n.eFrame.eWorlds.toList == ["w1×!", "w2×!"]
      | .error _ => false
    | .error _ => false),
  ("identity action model leaves every formula's truth unchanged",
    match mkActionModel ["e"] ["a", "b"] [("a", [("e", "e")]), ("b", [("e", "e")])] with
    | .ok am => ["w1", "w2", "w3"].all fun w => probes.all fun ψ =>
        match eSatisfies m2 w ψ, eSatisfiesAfter m2 w am "e" ψ with
        | .ok x, .ok y => x == y
        | _, _ => false
    | .error _ => false),
  ("assignment p ← ¬p flips p at every world; the old truth value is read before the update",
    match mkActionModel ["e"] ["a", "b"] [("a", [("e", "e")]), ("b", [("e", "e")])]
        [] [("e", [("p", .not p)])] with
    | .ok am => match productUpdate m2 am with
      | .ok n => (n.eValuation.getD ⟨"p"⟩ ∅).toList == ["w3×e"]
      | .error _ => false
    | .error _ => false),
  ("semi-private whether: the group learns whether p, the other agent does not",
    match semiPrivateWhether ["a", "b"] ["a"] p with
    | .ok am =>
      holds (eSatisfiesAfter m3 "s0" am "φ" (kn "a" p)) true
        && holds (eSatisfiesAfter m3 "s0" am "φ" (kn "b" p)) false
        && holds (eSatisfiesAfter m3 "s1" am "¬φ" (kn "a" (.not p))) true
    | .error _ => false),
  ("semi-private whether: b knows that a learned whether p",
    match semiPrivateWhether ["a", "b"] ["a"] p with
    | .ok am => holds (eSatisfiesAfter m3 "s0" am "φ" (kn "b" (.or (kn "a" p) (kn "a" (.not p))))) true
    | .error _ => false),
  ("private announcement: a knows p, b still does not and believes a does not know it",
    match privateAnnouncement ["a", "b"] ["a"] p with
    | .ok am =>
      holds (eSatisfiesAfter m3 "s0" am "!" (kn "a" p)) true
        && holds (eSatisfiesAfter m3 "s0" am "!" (kn "b" p)) false
        && holds (eSatisfiesAfter m3 "s0" am "!" (kn "b" (.not (kn "a" p)))) true
    | .error _ => false),
  ("private announcement is not executable where φ is false",
    match privateAnnouncement ["a", "b"] ["a"] p with
    | .ok am => holds (eSatisfiesAfter m3 "s1" am "!" .top) false
    | .error _ => false),
  ("cross-check: semi-private whether (group {a}) agrees with ATEL-D's informing update on a's knowledge",
    -- ATEL-D: model `AtlDynamicTests.epiModel` (s0 has p; a cannot tell s0 from s1; g alone).
    let epi := mkEpistemicModel
      (mkEpistemicFrame ["s0", "s1", "g"] [("a", full ["s0", "s1"] ++ [("g", "g")])])
      [("p", ["s0"]), ("goal", ["g"])]
    let probesA : List (Formula × Gamen.Atl.Dynamic.DFormula) :=
      [(kn "a" p, .knows "a" AtlDynamicTests.p),
       (kn "a" (.not p), .knows "a" (.not AtlDynamicTests.p)),
       (.or (kn "a" p) (kn "a" (.not p)),
        .or (.knows "a" AtlDynamicTests.p) (.knows "a" (.not AtlDynamicTests.p)))]
    match semiPrivateWhether ["a"] ["a"] p, AtlDynamicTests.load AtlDynamicTests.epiModel with
    | .ok am, .ok dm =>
      probesA.all fun (f, d) =>
        match Gamen.Atl.Dynamic.dsat dm .subjective
            (.grant (AtlDynamicTests.informP [] ["a"]) d) with
        | .ok set => ["s0", "s1", "g"].all fun s =>
            let ev := match eSatisfies epi s p with | .ok true => "φ" | _ => "¬φ"
            holds (eSatisfiesBoxAfter epi s am ev f) (set.contains s)
        | .error _ => false
    | _, _ => false),
  ("error: a model with doxastic relations is refused, not silently updated",
    match publicAnnouncement ["a"] p with
    | .ok am => fails (productUpdate
        { m3 with eFrame := { m3.eFrame with eDoxastic := m3.eFrame.eRelations } } am)
    | .error _ => false),
  ("error: an agent of the model with no relation in the action model",
    match publicAnnouncement ["a"] p with
    | .ok am => fails (productUpdate m3 am)
    | .error _ => false),
  ("error: two different (world, event) pairs with the same name",
    match mkActionModel ["b×c", "c"] ["a"] [("a", [("b×c", "b×c"), ("c", "c")])] with
    | .ok am =>
      fails (productUpdate
        (mkEpistemicModel (mkEpistemicFrame ["a", "a×b"] [("a", [("a", "a"), ("a×b", "a×b")])]) []) am)
    | .error _ => false),
  ("error: a precondition that cannot be evaluated is reported",
    match mkActionModel ["e"] ["a", "b"] [("a", [("e", "e")]), ("b", [("e", "e")])]
        [("e", .box p)] with
    | .ok am => fails (productUpdate m3 am)
    | .error _ => false),
  ("mkActionModel: no events, an edge to an unknown event, an unknown agent, a precondition on an unknown event",
    fails (mkActionModel [] ["a"] [])
      && fails (mkActionModel ["e"] ["a"] [("a", [("e", "x")])])
      && fails (mkActionModel ["e"] ["a"] [("z", [("e", "e")])])
      && fails (mkActionModel ["e"] ["a"] [] [("x", p)])),
  ("eSatisfiesAfter: an unknown event or world is an error",
    match publicAnnouncement ["a", "b"] p with
    | .ok am => fails (eSatisfiesAfter m3 "s0" am "nope" p) && fails (eSatisfiesAfter m3 "zz" am "!" p)
    | .error _ => false),
  ("review: a name collision involving a pair that FAILED its precondition is still an error (it would otherwise add a spurious edge)",
    match mkActionModel ["b×c", "c"] ["i"] [("i", [("b×c", "c"), ("c", "c")])] [("c", p)] with
    | .ok am =>
      fails (productUpdate
        (mkEpistemicModel
          (mkEpistemicFrame ["a", "a×b"] [("i", full ["a", "a×b"])]) [("p", ["a"])]) am)
    | .error _ => false),
  ("review: a group member that is not an agent is an error in both builders (it would silently make nobody learn)",
    fails (semiPrivateWhether ["a", "b"] ["z"] p) && fails (privateAnnouncement ["a", "b"] ["z"] p)),
  ("an epistemic postcondition is read in the model before the update (p ← ¬K_i p)",
    match mkActionModel ["a"] ["i"] [("i", [("a", "a")])] [] [("a", [("p", .not (kn "i" p))])] with
    | .ok am =>
      let m := mkEpistemicModel (mkEpistemicFrame ["w", "u"] [("i", [("w", "w"), ("u", "u")])]) [("p", ["w"])]
      match productUpdate m am with
      | .ok n => (n.eValuation.getD ⟨"p"⟩ ∅).toList == ["u×a"]
      | .error _ => false
    | .error _ => false),
  ("review: mkActionModel refuses an agent with no relation entry, and accepts one that explicitly sees nothing",
    fails (mkActionModel ["e"] ["a", "b"] [("a", [("e", "e")])])
      && (mkActionModel ["e"] ["a", "b"] [("a", [("e", "e")]), ("b", [])]).isOk),
  ("review: the public-announcement product keeps the restricted relations and the valuation, not just the worlds",
    match publicAnnouncement ["a", "b"] p with
    | .ok am => match productUpdate m2 am with
      | .ok n =>
        let rel (ag w : String) : List String := ((n.eFrame.eRelations.getD ag ∅).getD w ∅).toList
        rel "a" "w1×!" == ["w1×!", "w2×!"] && rel "a" "w2×!" == ["w1×!", "w2×!"]
          && rel "b" "w2×!" == ["w2×!"] && rel "b" "w1×!" == ["w1×!"]
          && (n.eValuation.getD ⟨"p"⟩ ∅).toList == ["w1×!", "w2×!"]
          && (n.eValuation.getD ⟨"q"⟩ ∅).toList == ["w2×!"]
      | .error _ => false
    | .error _ => false),
  ("review: two-agent cross-check — informing only a (ATEL-D) agrees with a semi-private announcement to {a} on what a AND b know",
    -- b is outside the group: b learns nothing about p but knows a learned whether p.
    let json := "{\"states\":[\"s0\",\"s1\"],\"agents\":[\"a\",\"b\"],\"actions\":[\"x\",\"w\"],\
      \"moves\":{\"s0\":{\"a\":[\"x\"],\"b\":[\"x\"]},\"s1\":{\"a\":[\"x\"],\"b\":[\"x\"]}},\
      \"valuation\":{\"s0\":[\"p\"]},\"default_next\":{\"stay\":true},\"transitions\":[],\
      \"indistinguishable\":{\"a\":[[\"s0\",\"s1\"]],\"b\":[[\"s0\",\"s1\"]]}}"
    let epi := mkEpistemicModel
      (mkEpistemicFrame ["s0", "s1"] [("a", full ["s0", "s1"]), ("b", full ["s0", "s1"])]) [("p", ["s0"])]
    let aware : Formula := .or (kn "a" p) (kn "a" (.not p))
    let probes : List (Formula × Gamen.Atl.Dynamic.DFormula) :=
      [(kn "a" p, .knows "a" AtlDynamicTests.p), (kn "b" p, .knows "b" AtlDynamicTests.p),
       (kn "b" (.not p), .knows "b" (.not AtlDynamicTests.p)),
       (kn "b" aware, .knows "b" (.or (.knows "a" AtlDynamicTests.p) (.knows "a" (.not AtlDynamicTests.p))))]
    match semiPrivateWhether ["a", "b"] ["a"] p, AtlDynamicTests.load json with
    | .ok am, .ok dm =>
      probes.all fun (f, d) =>
        match Gamen.Atl.Dynamic.dsat dm .subjective
            (.grant (AtlDynamicTests.informP [] ["a"]) d) with
        | .ok set => ["s0", "s1"].all fun s =>
            let ev := match eSatisfies epi s p with | .ok true => "φ" | _ => "¬φ"
            holds (eSatisfiesBoxAfter epi s am ev f) (set.contains s)
        | .error _ => false
    | _, _ => false)
]

end ActionModelTests
