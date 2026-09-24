import Gamen.Tableau
import Gamen.Fragment
import Gamen.FrameProperties
import Plausible
import Notebooks.Ch1HealthObligations
import Notebooks.Ch1SyntaxSemantics
import Validate.Core

/-!
# Tests

Ports of `test/TableauSpec.hs` (system K cases and countermodel extraction),
`test/FormulaSpec.hs` in full (`formulaCases`; `unitCases` keeps two extra
printing spot-checks that predate `formulaCases` and aren't literal ports
of a Haskell `it`), `test/FramePropertiesSpec.hs`, `test/KripkeSemanticsSpec.hs`,
the "Boxes & Diamonds Ch. 1 (Zach 2019)" block of `test/PaperCorrespondence.hs`
(split between `framePropertiesCases`, for the `isValidOnFrame`-exercising
"Definition 1.11" slice, and `semanticsCases`, for the rest — see
`semanticsCases` for the full list; no `PaperCorrespondence.hs` section
exercises `dstit`/`commitment` yet — those are only reached through
`Gamen.Stit`/`Gamen.Laca`, both not yet ported), the `toNNF` properties from
`test/Properties.hs`, run with Plausible instead of QuickCheck, `Gamen.Fragment`
(`test/RegressionIssue18.hs`'s "A2" describe block, plus the fragment-boundary
assertions from `test/Properties.hs`'s "issue #25" `it` — see `fragmentCases`
for what of that `it` is and is not ported), and `Gamen.Kripke`'s "B7: Kripke /
FrameProperties dangling-edge and class fixes" describe block from the
same file (see `kripkeCases`).
-/
open Gamen Plausible

/-! ## A tiny hspec-like harness -/

structure Case where
  name : String
  ok : Bool

def p : Formula := .atom "p"
def q : Formula := .atom "q"

def proves (prem : List Formula) (c : Formula) : Bool :=
  tableauProves systemK defaultMaxSteps prem c == .definitely true
def refutes (prem : List Formula) (c : Formula) : Bool :=
  tableauProves systemK defaultMaxSteps prem c == .definitely false
def consistent (fs : List Formula) : Verdict := tableauConsistent systemK defaultMaxSteps fs

/-- Countermodel for □p → p: build, take the first open branch, extract,
and confirm the formula is false in the extracted model. -/
def countermodelCase : Bool :=
  match buildTableau systemK 1000 [pfFalse .root (.implies (.box p) p)] with
  | .stillOpen (b :: _) =>
    match extractCountermodel systemK b >>= (isTrueIn · (.implies (.box p) p)) with
    | .ok truth => !truth
    | .error _ => false
  | _ => false

def unitCases : List Case := [
  -- Prefixes and closure
  ⟨"prefix printing", toString (Prefix.root.extend 2 |>.extend 3) == "1.2.3"⟩,
  ⟨"detects open branch", !(Branch.ofList [pfTrue .root p, pfTrue .root q]).isClosed⟩,
  ⟨"detects closed branch", (Branch.ofList [pfTrue .root p, pfFalse .root p]).isClosed⟩,
  ⟨"closure needs matching prefixes",
    !(Branch.ofList [pfTrue .root p, pfFalse (Prefix.root.extend 1) p]).isClosed⟩,
  -- System K validities (B&D Table 6.2)
  ⟨"proves (□p ∧ □q) → □(p ∧ q)", proves [] (.implies (.and (.box p) (.box q)) (.box (.and p q)))⟩,
  ⟨"proves ◇(p ∨ q) → (◇p ∨ ◇q)",
    proves [] (.implies (.diamond (.or p q)) (.or (.diamond p) (.diamond q)))⟩,
  ⟨"proves Schema K", proves [] (.implies (.box (.implies p q)) (.implies (.box p) (.box q)))⟩,
  ⟨"does not prove T: □p → p", refutes [] (.implies (.box p) p)⟩,
  ⟨"does not prove 4: □p → □□p", refutes [] (.implies (.box p) (.box (.box p)))⟩,
  ⟨"□p does not entail ◇p", refutes [.box p] (.diamond p)⟩,
  ⟨"◇p does not entail □p", refutes [] (.implies (.diamond p) (.box p))⟩,
  ⟨"proves dual ¬◇¬p → □p", proves [] (.implies (.not (.diamond (.not p))) (.box p))⟩,
  ⟨"K does not prove D: □p → ◇p", refutes [] (.implies (.box p) (.diamond p))⟩,
  -- Consistency
  ⟨"{□p, ◇q} satisfiable", consistent [.box p, .diamond q] == .definitely true⟩,
  ⟨"{p, ¬p} unsatisfiable", consistent [p, .not p] == .definitely false⟩,
  ⟨"{p → q, ¬q} satisfiable", consistent [.implies p q, .not q] == .definitely true⟩,
  ⟨"{p ∨ q, ¬p} satisfiable", consistent [.or p q, .not p] == .definitely true⟩,
  ⟨"{p, p ∨ q, ¬q} satisfiable", consistent [p, .or p q, .not q] == .definitely true⟩,
  -- Countermodels (B&D Theorem 6.19)
  ⟨"extracts countermodel for □p → p", countermodelCase⟩,
  -- Pretty-printing matches Haskell `show`
  ⟨"show □(p → ◇q)", toString (Formula.box (.implies p (.diamond q))) == "□(p → ◇q)"⟩,
  ⟨"show agents", toString (Formula.canUntil ["a", "b"] p q) == "⟨⟨a,b⟩⟩(p U q)"⟩
]

/-! ## Formula

Port of `test/FormulaSpec.hs` in full (B&D Definition 1.2, p. 5 — see the
citation note in `Gamen/Formula.lean`). Two describe blocks: "Formula
(Definition 1.2)" and "Negation Normal Form (toNNF, isNNF)". -/

def np : Formula := .not p
def nq : Formula := .not q

def formulaCases : List Case := [
  -- describe "Formula (Definition 1.2)"
  ⟨"shows formulas with standard notation",
    toString p == "p"
    && toString (.bot : Formula) == "⊥"
    && toString np == "¬p"
    && toString (Formula.box p) == "□p"
    && toString (Formula.diamond p) == "◇p"
    && toString (Formula.implies p q) == "(p → q)"⟩,
  ⟨"derives structural equality",
    p == p && p != q
    && Formula.box p == Formula.box p && Formula.box p != Formula.diamond p⟩,
  ⟨"detects modal-free formulas",
    p.isModalFree && (Formula.implies p q).isModalFree
    && !(Formula.box p).isModalFree
    && !(Formula.and p (Formula.diamond q)).isModalFree⟩,
  ⟨"collects atoms",
    (Formula.implies (Formula.box p) (Formula.diamond q)).atoms.toList
      == [(⟨"p"⟩ : Atom), ⟨"q"⟩]
    && (Formula.bot : Formula).atoms.toList == []⟩,
  ⟨"atoms returns properly typed Atom values",
    (Formula.and p (Formula.box q)).atoms.toList.map Atom.name == ["p", "q"]
    && toString (⟨"p"⟩ : Atom) == "p"
    && (match p with | .atom n => n == "p" | _ => false)⟩,
  -- describe "Negation Normal Form (toNNF, isNNF)"
  ⟨"leaves atoms and Bot unchanged", p.toNNF == p && (Formula.bot : Formula).toNNF == .bot⟩,
  ⟨"preserves a literal (Not Atom)", np.toNNF == np⟩,
  ⟨"eliminates double negation", (Formula.not np).toNNF == p⟩,
  ⟨"eliminates Implies", (Formula.implies p q).toNNF == Formula.or np q⟩,
  ⟨"eliminates Iff",
    (Formula.iff p q).toNNF == Formula.and (Formula.or np q) (Formula.or nq p)⟩,
  ⟨"applies de Morgan over And/Or",
    (Formula.not (Formula.and p q)).toNNF == Formula.or np nq
    && (Formula.not (Formula.or p q)).toNNF == Formula.and np nq⟩,
  ⟨"negates Box/Diamond as duals",
    (Formula.not (Formula.box p)).toNNF == Formula.diamond np
    && (Formula.not (Formula.diamond p)).toNNF == Formula.box np⟩,
  ⟨"negates FutureBox/FutureDiamond as duals",
    (Formula.not (Formula.futureBox p)).toNNF == Formula.futureDiamond np
    && (Formula.not (Formula.futureDiamond p)).toNNF == Formula.futureBox np⟩,
  ⟨"negates PastBox/PastDiamond as duals",
    (Formula.not (Formula.pastBox p)).toNNF == Formula.pastDiamond np
    && (Formula.not (Formula.pastDiamond p)).toNNF == Formula.pastBox np⟩,
  ⟨"negates Stit and ChoiceDiamond as duals (Lyon-Berkel)",
    (Formula.not (Formula.stit "i" p)).toNNF == Formula.choiceDiamond "i" np
    && (Formula.not (Formula.choiceDiamond "i" p)).toNNF == Formula.stit "i" np⟩,
  ⟨"negates Ought and Permitted as duals (Lyon-Berkel)",
    (Formula.not (Formula.ought "i" p)).toNNF == Formula.permitted "i" np
    && (Formula.not (Formula.permitted "i" p)).toNNF == Formula.ought "i" np⟩,
  ⟨"leaves negations of non-dualizable operators in place",
    (Formula.not (Formula.knowledge "a" p)).toNNF == Formula.not (Formula.knowledge "a" p)
    && (Formula.not (Formula.knowledge "a" np)).toNNF == Formula.not (Formula.knowledge "a" np)
    && (Formula.not (Formula.groupStit p)).toNNF == Formula.not (Formula.groupStit p)
    && (Formula.not (Formula.next p)).toNNF == Formula.not (Formula.next p)⟩,
  ⟨"recurses through nested modalities",
    (Formula.not (Formula.box (Formula.implies (Formula.stit "i" p) (Formula.diamond q)))).toNNF
      == Formula.diamond (Formula.and (Formula.stit "i" p) (Formula.box nq))⟩,
  ⟨"isNNF accepts the L_n fragment",
    p.isNNF && np.isNNF && (Formula.and p np).isNNF
    && (Formula.or (Formula.box p) (Formula.diamond np)).isNNF
    && (Formula.stit "i" (Formula.or p np)).isNNF
    && (Formula.ought "i" np).isNNF
    && (Formula.choiceDiamond "i" p).isNNF⟩,
  ⟨"isNNF rejects Implies, Iff, and Not on non-literal modal",
    !(Formula.implies p q).isNNF && !(Formula.iff p q).isNNF
    && !(Formula.not (Formula.and p q)).isNNF && !(Formula.not (Formula.box p)).isNNF
    && !(Formula.not (Formula.stit "i" p)).isNNF && !(Formula.not (Formula.ought "i" p)).isNNF⟩,
  ⟨"toNNF produces an NNF result on L_n inputs",
    [ Formula.implies p q
    , Formula.iff p q
    , Formula.not (Formula.and p (Formula.or q (Formula.box (Formula.stit "i" p))))
    , Formula.not (Formula.ought "i" (Formula.implies p q))
    , Formula.iff (Formula.stit "i" p) (Formula.box (Formula.permitted "i" q))
    ].all (fun f => f.toNNF.isNNF)⟩,
  ⟨"toNNF is idempotent",
    [ Formula.implies p q
    , Formula.not (Formula.iff p q)
    , Formula.not (Formula.not (Formula.and (Formula.box p) (Formula.stit "i" (Formula.diamond np))))
    , Formula.iff (Formula.ought "i" p) (Formula.permitted "i" (Formula.not q))
    ].all (fun f => f.toNNF.toNNF == f.toNNF)⟩,
  ⟨"hasAgentOperator detects Stit/Ought/Permitted/ChoiceDiamond",
    !p.hasAgentOperator && !(Formula.box p).hasAgentOperator
    && !(Formula.belief "a" p).hasAgentOperator
    && (Formula.stit "i" p).hasAgentOperator
    && (Formula.ought "i" p).hasAgentOperator
    && (Formula.permitted "i" p).hasAgentOperator
    && (Formula.choiceDiamond "i" p).hasAgentOperator
    && (Formula.futureBox (Formula.ought "c" (.atom "statin"))).hasAgentOperator
    && (Formula.implies (.atom "ascvd") (Formula.ought "c" (.atom "statin"))).hasAgentOperator
    && !(Formula.groupStit p).hasAgentOperator⟩,
  -- describe "Derived STIT operators" (Formula.hs:429-446). Only the
  -- structural shape of `dstit`/`commitment` themselves is FormulaSpec's
  -- business; `dstit`'s satisfaction behavior ("dstit smart constructor
  -- uses Box for settledness", StitSpec.hs:30-31, and the model-level
  -- checks at StitSpec.hs:113-116) comes with `Gamen.Stit`.
  ⟨"dstit smart constructor uses Box for settledness (StitSpec.hs:30)",
    Formula.dstit "i" p == .and (.stit "i" p) (.not (.box p))⟩,
  ⟨"commitment builds □(¬F*[i]A → G*v_{i,j}) ∧ ¬[i]A (Formula.hs:440-446)",
    Formula.commitment "a" "b" p
      == .and (.box (.implies
            (.not (.or (.stit "a" p) (.futureDiamond (.stit "a" p))))
            (.and (.atom "v_a_b") (.futureBox (.atom "v_a_b")))))
          (.not (.stit "a" p))⟩,
  ⟨"commitment's agent order is pinned (i is the committed agent, not j)",
    Formula.commitment "a" "b" p != Formula.commitment "b" "a" p⟩
]

/-! ## Widget interaction

`simulateClicks` replays browser events through `explorer.update` the way
ProofWidgets v0.0.111's `InteractiveSvg.serverRpcMethod` does: `getData`
reads the element recorded as `selected`, and `selected` is set *after* a
mousedown is processed and cleared after a mouseup. (Calling `handleClick`
directly would skip exactly the ordering that broke clicks the first time.) -/

open ProofWidgets.Svg in
def simulateClicks (st : Gamen.Widgets.ExplorerState) (ids : List String) :
    Gamen.Widgets.ExplorerState := Id.run do
  let mut state := st
  for id in ids do
    let mut selected : Option String := none
    for kind in [ActionKind.mousedown, ActionKind.mouseup] do
      let idToData := Std.HashMap.ofList (Gamen.Widgets.render state).idToDataList
      let getData := fun (α : Type) [Lean.FromJson α] => do
        let d ← idToData[(← selected)]?
        (Lean.fromJson? (α := α) d).toOption
      state := Gamen.Widgets.explorer.update 0 0 { kind, id := some id, data := none }
        none none selected getData state
      if kind == .mousedown then selected := some id
  return state

def byo0 : Gamen.Widgets.ExplorerState :=
  { scenario := buildYourOwn, valuation := buildYourOwn.valuation }

def g2At (st : Gamen.Widgets.ExplorerState) : Bool :=
  match st.model with
  | .ok m => holdsAt m "w1" ml[ □blood_cultures ]
  | .error _ => false

def widgetCases : List Case := [
  ⟨"widget: G2 initially fails at w1", !g2At byo0⟩,
  ⟨"widget: select blood_cultures, click w3 → G2 holds",
    g2At (simulateClicks byo0 ["atom-1", "world-w3"])⟩,
  ⟨"widget: clicking the world's label works too",
    g2At (simulateClicks byo0 ["atom-1-label", "world-w3-label"])⟩,
  ⟨"widget: clicking twice toggles back",
    !g2At (simulateClicks byo0 ["atom-1", "world-w3", "world-w3"])⟩,
  ⟨"widget: non-editable world w1 ignores clicks",
    (simulateClicks byo0 ["atom-0", "world-w1"]).valuation == byo0.valuation⟩,
  ⟨"widget: a click on empty space changes nothing",
    (simulateClicks byo0 ["nothing-here"]).valuation == byo0.valuation⟩ ]

/-! ## Notebook answer keys

The answers stated in the Gamen.jl Pluto notebooks (and B&D Problem 1.1),
checked against the Lean models. If a notebook's model or a formula drifts,
these fail. -/

def answerKeyCases : List Case := [
  ⟨"ch1 Problem 1.1 matches the Pluto answers (F T T F T T T F F)",
    problem11.map (fun (w, φ) => holdsAt M w φ)
      == [false, true, true, false, true, true, true, false, false]⟩,
  ⟨"ch1 practice matches (T T F T)",
    practice.map (fun (w, φ) => holdsAt M w φ) == [true, true, false, true]⟩,
  ⟨"ch1 challenge: ¬p ∧ ¬q is true only at w3",
    ["w1", "w2", "w3"].map (holdsAt M · ml[ ¬p ∧ ¬q ]) == [false, false, true]⟩,
  ⟨"health G1–G5 at w1 match the Pluto answers (T F F T F)",
    guidelines.map (fun g => holdsAt edModel "w1" g.formula)
      == [true, false, false, true, false]⟩,
  ⟨"health: G5/G6 conflict, G4/G7 conflict only with bleeding, G8/G9 only with both",
    consistency [g5, g6] == "inconsistent: no model satisfies all of them"
    && consistency [g4, g7] == "consistent: some model satisfies all of them"
    && consistency [g4, g7, ml[ active_bleeding ]] == "inconsistent: no model satisfies all of them"
    && consistency [g8, g9, ml[ sepsis ]] == "consistent: some model satisfies all of them"
    && consistency [g8, g9, ml[ sepsis ], ml[ fluid_overload ]]
         == "inconsistent: no model satisfies all of them"⟩ ]

/-! ## Frame properties

Port of `test/FramePropertiesSpec.hs`, plus the slice of
`test/PaperCorrespondence.hs` ("Definition 1.11 (p. 11): validity in a
class of models") that exercises `isValidOnFrame`. B&D numbers were
checked against `notes/bd-screen.pdf` (see `Gamen/FrameProperties.lean`
for the two spots where the Haskell citations were wrong). -/

/-- `none` when `mkFrame` rejects the fixture, so a malformed test frame
fails its case instead of `get!` panicking and continuing with a default. -/
private def frame (ws : List String) (rels : List (String × String)) : Option Frame :=
  (mkFrame ws rels).toOption

/-- A frame predicate on a fixture frame; `none` if the frame is malformed.
Compare against `some true` / `some false`, as with `validOn`. -/
private def holds (prop : Frame → Bool) (fr : Option Frame) : Option Bool :=
  fr.map prop

/-- `Except`-safe: an evaluation error (`none`) matches neither `some true`
nor `some false`, so a call site comparing against either one fails the
test on error, whichever polarity it expected. A plain `Bool`-returning
helper with a fixed default (e.g. `.getD false`) would let an error
masquerade as a definite answer for whichever polarity matches the
default — that is exactly the bug this shape avoids. -/
private def validOn (fr : Option Frame) (f : Formula) : Option Bool :=
  fr.bind fun fr => (isValidOnFrame fr f).toOption

def framePropertiesCases : List Case := [
  -- Frame property predicates (B&D Table 2.1)
  ⟨"detects reflexive frames",
    holds isReflexive (frame ["w1", "w2"] [("w1","w1"), ("w1","w2"), ("w2","w2")]) == some true
    && holds isSerial (frame ["w1", "w2"] [("w1","w1"), ("w1","w2"), ("w2","w2")]) == some true
    && holds isReflexive (frame ["w1", "w2"] [("w1","w1"), ("w1","w2")]) == some false⟩,
  ⟨"detects symmetric frames",
    holds isSymmetric (frame ["w1", "w2"] [("w1","w2"), ("w2","w1")]) == some true
    && holds isSymmetric (frame ["w1", "w2"] [("w1","w2")]) == some false⟩,
  ⟨"detects transitive frames",
    holds isTransitive (frame ["w1", "w2", "w3"] [("w1","w2"), ("w2","w3"), ("w1","w3")]) == some true
    && holds isTransitive (frame ["w1", "w2", "w3"] [("w1","w2"), ("w2","w3")]) == some false⟩,
  ⟨"detects serial frames",
    holds isSerial (frame ["w1", "w2"] [("w1","w2"), ("w2","w1")]) == some true
    && holds isSerial (frame ["w1", "w2", "w3"] [("w1","w2")]) == some false⟩,
  ⟨"detects euclidean frames",
    holds isEuclidean (frame ["w1", "w2", "w3"]
      [("w1","w2"), ("w1","w3"), ("w2","w2"), ("w2","w3"), ("w3","w2"), ("w3","w3")]) == some true
    && holds isEuclidean (frame ["w1", "w2", "w3"] [("w1","w2"), ("w1","w3")]) == some false⟩,
  -- Frame validity (B&D Definition 2.4)
  ⟨"validates Box Top on any frame",
    validOn (frame ["w1", "w2"] [("w1","w2")]) (.box .top) == some true⟩,
  ⟨"rejects Bot on any frame",
    validOn (frame ["w1", "w2"] [("w1","w2")]) .bot == some false⟩,
  -- Schema T: □p → p corresponds to reflexivity (B&D Table 2.1; Corollary 2.8)
  ⟨"schema T is valid on reflexive frames",
    validOn (frame ["w1", "w2"] [("w1","w1"), ("w1","w2"), ("w2","w2")])
      (.implies (.box p) p) == some true⟩,
  ⟨"schema T is not valid on non-reflexive frames",
    validOn (frame ["w1", "w2"] [("w1","w2")]) (.implies (.box p) p) == some false⟩,
  -- Schema D: □p → ◇p corresponds to seriality (B&D Table 2.1; Corollary 2.8)
  ⟨"schema D is valid on serial frames",
    validOn (frame ["w1", "w2"] [("w1","w2"), ("w2","w1")])
      (.implies (.box p) (.diamond p)) == some true⟩,
  ⟨"schema D is not valid on non-serial frames",
    validOn (frame ["w1", "w2"] [("w1","w2")]) (.implies (.box p) (.diamond p)) == some false⟩,
  -- Schema B: p → □◇p corresponds to symmetry (B&D Table 2.1; Corollary 2.8)
  ⟨"schema B is valid on symmetric frames",
    validOn (frame ["w1", "w2"] [("w1","w2"), ("w2","w1"), ("w1","w1"), ("w2","w2")])
      (.implies p (.box (.diamond p))) == some true⟩,
  ⟨"schema B is not valid on non-symmetric frames",
    validOn (frame ["w1", "w2"] [("w1","w2"), ("w2","w2")])
      (.implies p (.box (.diamond p))) == some false⟩,
  -- Schema 4: □p → □□p corresponds to transitivity (B&D Table 2.1; Corollary 2.8)
  ⟨"schema 4 is valid on transitive frames",
    validOn (frame ["w1", "w2", "w3"] [("w1","w2"), ("w2","w3"), ("w1","w3")])
      (.implies (.box p) (.box (.box p))) == some true⟩,
  ⟨"schema 4 is not valid on non-transitive frames",
    validOn (frame ["w1", "w2", "w3"] [("w1","w2"), ("w2","w3")])
      (.implies (.box p) (.box (.box p))) == some false⟩,
  -- Schema 5: ◇p → □◇p corresponds to euclideanness (B&D Table 2.1; Corollary 2.8)
  ⟨"schema 5 is valid on euclidean frames",
    validOn (frame ["w1", "w2", "w3"]
      [("w1","w2"), ("w1","w3"), ("w2","w2"), ("w2","w3"), ("w3","w2"), ("w3","w3")])
      (.implies (.diamond p) (.box (.diamond p))) == some true⟩,
  ⟨"schema 5 is not valid on non-euclidean frames",
    validOn (frame ["w1", "w2", "w3"] [("w1","w2"), ("w1","w3")])
      (.implies (.diamond p) (.box (.diamond p))) == some false⟩,
  -- Schema K: □(p→q) → (□p→□q) valid on all frames (B&D Proposition 1.19)
  ⟨"schema K is valid on any frame",
    validOn (frame ["w1", "w2"] [("w1","w2")])
      (.implies (.box (.implies p q)) (.implies (.box p) (.box q))) == some true
    && validOn (frame ["w1", "w2", "w3"] [("w1","w2"), ("w2","w3")])
      (.implies (.box (.implies p q)) (.implies (.box p) (.box q))) == some true
    && validOn (frame ["w1"] [("w1","w1")])
      (.implies (.box (.implies p q)) (.implies (.box p) (.box q))) == some true⟩,
  -- Additional frame properties (B&D Table 2.2)
  ⟨"detects partially functional frames",
    holds isPartiallyFunctional (frame ["w1", "w2", "w3"] [("w1","w2"), ("w2","w3")]) == some true
    && holds isPartiallyFunctional (frame ["w1", "w2", "w3"] [("w1","w2"), ("w1","w3")]) == some false⟩,
  ⟨"detects functional frames",
    holds isFunctional (frame ["w1", "w2"] [("w1","w2"), ("w2","w1")]) == some true
    && holds isFunctional (frame ["w1", "w2"] [("w1","w2")]) == some false
    && holds isFunctional (frame ["w1", "w2", "w3"]
      [("w1","w2"), ("w1","w3"), ("w2","w3"), ("w3","w1")]) == some false⟩,
  ⟨"detects weakly dense frames",
    holds isWeaklyDense (frame ["w1", "w2"] [("w1","w1"), ("w1","w2"), ("w2","w2")]) == some true
    && holds isWeaklyDense (frame ["w1", "w2"] [("w1","w2")]) == some false⟩,
  ⟨"detects weakly connected frames",
    holds isWeaklyConnected (frame ["w1", "w2", "w3"] [("w1","w2"), ("w1","w3"), ("w2","w3")]) == some true
    && holds isWeaklyConnected (frame ["w1", "w2", "w3"] [("w1","w2"), ("w1","w3")]) == some false⟩,
  ⟨"detects weakly directed frames",
    holds isWeaklyDirected (frame ["w1", "w2", "w3", "w4"]
      [("w1","w2"), ("w1","w3"), ("w2","w4"), ("w3","w4"), ("w4","w4")]) == some true
    && holds isWeaklyDirected (frame ["w1", "w2", "w3"] [("w1","w2"), ("w1","w3")]) == some false⟩,
  -- Equivalence relation and universal (B&D Definition 2.11)
  ⟨"detects equivalence relations",
    holds isEquivalenceRelation (frame ["w1", "w2"]
      [("w1","w1"), ("w2","w2"), ("w1","w2"), ("w2","w1")]) == some true
    && holds isEquivalenceRelation (frame ["w1", "w2"] [("w1","w2"), ("w2","w1")]) == some false⟩,
  ⟨"detects universal frames",
    holds isUniversal (frame ["w1", "w2"]
      [("w1","w1"), ("w1","w2"), ("w2","w1"), ("w2","w2")]) == some true
    && holds isUniversal (frame ["w1", "w2"] [("w1","w1"), ("w1","w2"), ("w2","w2")]) == some false⟩,
  -- B&D Table 2.2 correspondence results (cf. Problems 2.3–2.4). Names below
  -- keep the Haskell spec's literal wording ("Diamond"/"Box"/"->"/"<->"
  -- instead of ◇/□/→/↔) so each `it` in test/FramePropertiesSpec.hs has an
  -- exact-string match here.
  ⟨"◇p → □p corresponds to partially functional",
    validOn (frame ["w1", "w2", "w3"] [("w1","w2"), ("w2","w3")])
      (.implies (.diamond p) (.box p)) == some true
    && validOn (frame ["w1", "w2", "w3"] [("w1","w2"), ("w1","w3")])
      (.implies (.diamond p) (.box p)) == some false⟩,
  ⟨"◇p ↔ □p corresponds to functional",
    validOn (frame ["w1", "w2"] [("w1","w2"), ("w2","w1")]) (.iff (.diamond p) (.box p))
      == some true
    && validOn (frame ["w1", "w2"] [("w1","w2")]) (.iff (.diamond p) (.box p))
      == some false⟩,
  ⟨"□□p → □p corresponds to weakly dense",
    validOn (frame ["w1", "w2"] [("w1","w1"), ("w1","w2"), ("w2","w2")])
      (.implies (.box (.box p)) (.box p)) == some true
    && validOn (frame ["w1", "w2"] [("w1","w2")]) (.implies (.box (.box p)) (.box p))
      == some false⟩,
  ⟨"schema L corresponds to weakly connected",
    validOn (frame ["w1", "w2", "w3"] [("w1","w2"), ("w1","w3"), ("w2","w3")])
      (.or (.box (.implies (.and p (.box p)) q)) (.box (.implies (.and q (.box q)) p)))
      == some true
    && validOn (frame ["w1", "w2", "w3"] [("w1","w2"), ("w1","w3")])
      (.or (.box (.implies (.and p (.box p)) q)) (.box (.implies (.and q (.box q)) p)))
      == some false⟩,
  ⟨"schema G: ◇□p → □◇p corresponds to weakly directed",
    validOn (frame ["w1", "w2", "w3", "w4"]
      [("w1","w2"), ("w1","w3"), ("w2","w4"), ("w3","w4"), ("w4","w4")])
      (.implies (.diamond (.box p)) (.box (.diamond p))) == some true
    && validOn (frame ["w1", "w2", "w3"] [("w1","w2"), ("w1","w3")])
      (.implies (.diamond (.box p)) (.box (.diamond p))) == some false⟩,
  -- Relationships between properties (B&D Proposition 2.9)
  ⟨"reflexive implies serial",
    holds isReflexive (frame ["w1", "w2"] [("w1","w1"), ("w2","w2")]) == some true
    && holds isSerial (frame ["w1", "w2"] [("w1","w1"), ("w2","w2")]) == some true⟩,
  ⟨"symmetric + transitive implies euclidean",
    holds isSymmetric (frame ["w1", "w2"] [("w1","w2"), ("w2","w1"), ("w1","w1"), ("w2","w2")]) == some true
    && holds isTransitive (frame ["w1", "w2"] [("w1","w2"), ("w2","w1"), ("w1","w1"), ("w2","w2")]) == some true
    && holds isEuclidean (frame ["w1", "w2"] [("w1","w2"), ("w2","w1"), ("w1","w1"), ("w2","w2")]) == some true⟩,
  ⟨"symmetric or euclidean implies weakly directed",
    holds isSymmetric (frame ["w1", "w2"] [("w1","w2"), ("w2","w1")]) == some true
    && holds isWeaklyDirected (frame ["w1", "w2"] [("w1","w2"), ("w2","w1")]) == some true
    && holds isEuclidean (frame ["w1", "w2", "w3"]
      [("w1","w2"), ("w1","w3"), ("w2","w2"), ("w2","w3"), ("w3","w2"), ("w3","w3")]) == some true
    && holds isWeaklyDirected (frame ["w1", "w2", "w3"]
      [("w1","w2"), ("w1","w3"), ("w2","w2"), ("w2","w3"), ("w3","w2"), ("w3","w3")]) == some true⟩,
  ⟨"euclidean implies weakly connected",
    holds isEuclidean (frame ["w1", "w2", "w3"]
      [("w1","w2"), ("w1","w3"), ("w2","w2"), ("w2","w3"), ("w3","w2"), ("w3","w3")]) == some true
    && holds isWeaklyConnected (frame ["w1", "w2", "w3"]
      [("w1","w2"), ("w1","w3"), ("w2","w2"), ("w2","w3"), ("w3","w2"), ("w3","w3")]) == some true⟩,
  ⟨"functional implies serial",
    holds isFunctional (frame ["w1", "w2"] [("w1","w2"), ("w2","w1")]) == some true
    && holds isSerial (frame ["w1", "w2"] [("w1","w2"), ("w2","w1")]) == some true⟩,
  -- Equivalence relation characterizations (B&D Proposition 2.12)
  ⟨"equivalence relation satisfies all equivalent conditions",
    let equiv3 := frame ["w1", "w2", "w3"]
      [ ("w1","w1"), ("w1","w2"), ("w1","w3")
      , ("w2","w1"), ("w2","w2"), ("w2","w3")
      , ("w3","w1"), ("w3","w2"), ("w3","w3") ]
    holds isEquivalenceRelation equiv3 == some true && holds isReflexive equiv3 == some true && holds isEuclidean equiv3 == some true
    && holds isSerial equiv3 == some true && holds isSymmetric equiv3 == some true && holds isTransitive equiv3 == some true && holds isUniversal equiv3 == some true⟩,
  ⟨"non-universal equivalence relation",
    let equivTwoClasses := frame ["w1", "w2", "w3"]
      [("w1","w1"), ("w2","w2"), ("w2","w3"), ("w3","w2"), ("w3","w3")]
    holds isEquivalenceRelation equivTwoClasses == some true && holds isUniversal equivTwoClasses == some false⟩,
  -- S5 on equivalence and universal frames (B&D Proposition 2.14)
  ⟨"all S5 schemas valid on equivalence frames",
    let equiv := frame ["w1", "w2", "w3"]
      [ ("w1","w1"), ("w1","w2"), ("w1","w3")
      , ("w2","w1"), ("w2","w2"), ("w2","w3")
      , ("w3","w1"), ("w3","w2"), ("w3","w3") ]
    validOn equiv (.implies (.box p) p) == some true
    && validOn equiv (.implies p (.box (.diamond p))) == some true
    && validOn equiv (.implies (.box p) (.box (.box p))) == some true
    && validOn equiv (.implies (.diamond p) (.box (.diamond p))) == some true⟩,
  ⟨"S5 schemas also valid on non-universal equivalence relations",
    let equiv2 := frame ["w1", "w2", "w3"]
      [("w1","w1"), ("w2","w2"), ("w2","w3"), ("w3","w2"), ("w3","w3")]
    holds isEquivalenceRelation equiv2 == some true
    && validOn equiv2 (.implies (.box p) p) == some true
    && validOn equiv2 (.implies p (.box (.diamond p))) == some true
    && validOn equiv2 (.implies (.box p) (.box (.box p))) == some true
    && validOn equiv2 (.implies (.diamond p) (.box (.diamond p))) == some true⟩,
  -- PaperCorrespondence: Definition 1.11 (p. 11), validity in a class of
  -- models — the isValidOnFrame-exercising `it`s only (the "entailment"
  -- describe block in that file is ported in `semanticsCases` instead,
  -- alongside the rest of "Boxes & Diamonds Ch. 1").
  ⟨"Def 1.11: □p is true at an isolated world (no successors, vacuously)",
    if let some fr := frame ["w"] [] then
    let m := mkModel fr []
    (satisfies m "w" (.box p)).toOption == some true
    else false⟩,
  ⟨"Def 1.11: p is false at an isolated world (V(p) = ∅)",
    if let some fr := frame ["w"] [] then
    let m := mkModel fr []
    (satisfies m "w" p).toOption == some false
    else false⟩,
  ⟨"Def 1.11: □p→p is false at an isolated world (witnesses T failing off reflexivity)",
    if let some fr := frame ["w"] [] then
    let m := mkModel fr []
    (satisfies m "w" (.implies (.box p) p)).toOption == some false
    else false⟩,
  ⟨"Prop 1.19: K axiom valid on 2-world chain frame {w1→w2}",
    validOn (frame ["w1","w2"] [("w1","w2")])
      (.implies (.box (.implies p q)) (.implies (.box p) (.box q))) == some true⟩,
  ⟨"Prop 1.19: K axiom valid on 3-world chain frame {w1→w2→w3}",
    validOn (frame ["w1","w2","w3"] [("w1","w2"), ("w2","w3")])
      (.implies (.box (.implies p q)) (.implies (.box p) (.box q))) == some true⟩,
  ⟨"Prop 1.19: K axiom valid on reflexive singleton frame {w1→w1}",
    validOn (frame ["w1"] [("w1","w1")])
      (.implies (.box (.implies p q)) (.implies (.box p) (.box q))) == some true⟩
]

/-! ## Kripke (`Gamen.Kripke`)

Port of `test/RegressionIssue18.hs`'s "B7: Kripke / FrameProperties
dangling-edge and class fixes" describe block (all 4 `it`s) — the rest of
that file needs modules not yet ported (`PORTING.md`). `mkFrame`,
`accessible`, and `mkModel` are otherwise exercised throughout
`framePropertiesCases`/`semanticsCases`; `isEquivalenceOn` and
`checkIndependence` have no Haskell spec of their own (only
`RegressionIssue18.hs` exercises `equivalenceClasses` directly — the
callers that would exercise the other two, `Stit`/`Xstit`/`DeonticStit`,
are not yet ported), so the extra cases below are not-in-spec sanity
checks, each flagged as such. -/

def kripkeCases : List Case := [
  -- RegressionIssue18.hs: "B7: Kripke / FrameProperties dangling-edge
  -- and class fixes"
  ⟨"mkFrame errors on an edge whose endpoint is not a world",
    match mkFrame ["w1"] [("w1", "ghost")] with
    | .error _ => true
    | .ok _ => false⟩,
  ⟨"equivalenceClasses puts each world in its own class (no drops, no ∅)",
    -- Non-reflexive rel: w1↦{w2}, w2↦{w1}. The old code dropped w1 (it
    -- took R(w1)={w2} as w1's class) and could emit empty classes.
    let rel : Std.TreeMap World (Std.TreeSet World) := Std.TreeMap.ofList
      [("w1", Std.TreeSet.ofList ["w2"]), ("w2", Std.TreeSet.ofList ["w1"])]
    let cls := equivalenceClasses (Std.TreeSet.ofList ["w1", "w2"]) rel
    cls.all (fun c => !c.isEmpty)
    && cls.foldl (· ∪ ·) ∅ == Std.TreeSet.ofList ["w1", "w2"]⟩,
  -- Not in any Haskell spec, but pins the *order* of `equivalenceClasses`'s
  -- output, which the case above does not check (it only checks the
  -- classes as a set of sets). `equivalenceClasses`'s docstring and
  -- `Kripke.hs`/`RegressionIssue18.hs:337` both describe the algorithm as
  -- reverse discovery order over `ws` in ascending order; this fixture
  -- (worlds {a,b,c,d,e}, rel = {a↦{b}, c↦{c,d}, d↦{a}, e↦∅}, b keyless)
  -- exercises all three B7 cases at once (a non-reflexive pair a/b, a
  -- self-looping pair c/d, and a keyless/empty-image world e) so the
  -- order is not incidentally symmetric. Expected value obtained by
  -- running gamen-hs's `equivalenceClasses` on this fixture in `cabal
  -- repl` (not derived from the Lean code under test).
  ⟨"equivalenceClasses returns classes in reverse discovery order",
    let rel : Std.TreeMap World (Std.TreeSet World) := Std.TreeMap.ofList
      [ ("a", Std.TreeSet.ofList ["b"])
      , ("c", Std.TreeSet.ofList ["c", "d"])
      , ("d", Std.TreeSet.ofList ["a"])
      , ("e", (∅ : Std.TreeSet World)) ]
    let cls := equivalenceClasses (Std.TreeSet.ofList ["a", "b", "c", "d", "e"]) rel
    cls.map (·.toList) == [["e"], ["c", "d"], ["a", "b"]]⟩,
  ⟨"isUniversal checks coverage, not successor count (dangling edge)",
    -- w1 reaches {w1, ghost}: count 2 = |worlds| but w2 is uncovered.
    -- Built with the raw `Frame` constructor (as the Haskell does), since
    -- `mkFrame` would itself reject the dangling edge.
    let fr : Frame :=
      { worlds := Std.TreeSet.ofList ["w1", "w2"]
        relation := Std.TreeMap.ofList
          [ ("w1", Std.TreeSet.ofList ["w1", "ghost"])
          , ("w2", Std.TreeSet.ofList ["w1", "w2"]) ] }
    isUniversal fr == false⟩,
  ⟨"isFunctional rejects a lone dangling successor",
    -- w1's single successor is a non-world.
    let fr : Frame :=
      { worlds := Std.TreeSet.ofList ["w1"]
        relation := Std.TreeMap.ofList [("w1", Std.TreeSet.ofList ["ghost"])] }
    isFunctional fr == false⟩,
  -- Not in any Haskell spec: `isEquivalenceOn` is `FrameProperties.
  -- isEquivalenceRelation` applied to a bare `(worlds, relation)` pair
  -- rather than a `Frame`; check it agrees, on both a genuine
  -- equivalence relation and a non-equivalence one.
  ⟨"isEquivalenceOn agrees with isEquivalenceRelation on a Frame",
    let ws := Std.TreeSet.ofList ["w1", "w2", "w3"]
    let equivRel : Std.TreeMap World (Std.TreeSet World) := Std.TreeMap.ofList
      [ ("w1", Std.TreeSet.ofList ["w1", "w2", "w3"])
      , ("w2", Std.TreeSet.ofList ["w1", "w2", "w3"])
      , ("w3", Std.TreeSet.ofList ["w1", "w2", "w3"]) ]
    let nonEquivRel : Std.TreeMap World (Std.TreeSet World) := Std.TreeMap.ofList
      [("w1", Std.TreeSet.ofList ["w2"]), ("w2", Std.TreeSet.ofList ["w1"])]
    isEquivalenceOn ws equivRel == true
    && isEquivalenceRelation { worlds := ws, relation := equivRel } == true
    && isEquivalenceOn ws nonEquivRel == false
    && isEquivalenceRelation { worlds := ws, relation := nonEquivRel } == false⟩,
  -- Not in any Haskell spec: two agents with independent choice cells at
  -- every world of the moment (any pairing has a non-empty joint
  -- outcome) versus two agents whose choices can conflict.
  ⟨"checkIndependence accepts independent choice cells, rejects conflicting ones",
    let mom := Std.TreeSet.ofList ["w1", "w2", "w3", "w4"]
    -- Agent a's cells: {w1,w2} or {w3,w4}; agent b's cells: {w1,w3} or
    -- {w2,w4}. Every pairing of one a-cell and one b-cell meets in
    -- exactly one world.
    let independentCell (agent : String) (w : String) : Std.TreeSet World :=
      if agent == "a" then
        if w == "w1" || w == "w2" then Std.TreeSet.ofList ["w1", "w2"]
        else Std.TreeSet.ofList ["w3", "w4"]
      else
        if w == "w1" || w == "w3" then Std.TreeSet.ofList ["w1", "w3"]
        else Std.TreeSet.ofList ["w2", "w4"]
    -- Agent a's cells: {w1,w2} or {w3,w4}; agent b's cells: {w1,w2} or
    -- {w3,w4} too — picking a's {w1,w2} and b's {w3,w4} meets in ∅.
    let conflictingCell (agent : String) (w : String) : Std.TreeSet World :=
      if w == "w1" || w == "w2" then Std.TreeSet.ofList ["w1", "w2"]
      else Std.TreeSet.ofList ["w3", "w4"]
    checkIndependence independentCell ["a", "b"] mom == true
    && checkIndependence conflictingCell ["a", "b"] mom == false
    -- No agents: vacuously independent (Haskell's explicit `[] -> True`
    -- case, guarding the otherwise-partial `foldl1`).
    && checkIndependence independentCell ([] : List String) mom == true
    -- Empty moment: `sequence` over empty cell lists is `[]`, so `all`
    -- is vacuously true (Haskell behavior, not a special case).
    && checkIndependence independentCell ["a", "b"] ∅ == true⟩
]

/-! ## Semantics (`Gamen.Semantics`)

Port of `test/KripkeSemanticsSpec.hs` (all 9 `it`s), the rest of
`test/PaperCorrespondence.hs`'s "Boxes & Diamonds Ch. 1 (Zach 2019)" block
that was not already covered by `framePropertiesCases`'s "Definition 1.11"
slice: Definition 1.6 (model as a triple), Definition 1.7 (all 8 truth
clauses), Proposition 1.8 (□/◇ duality), Definition 1.9 (truth in a
model), Proposition 1.19 (K is K-provable, via the already-ported
`systemK` tableau), and Definition 1.23 + Example 1.24 (entailment); plus
`test/RegressionIssue18.hs`'s "B5: isTautology abstracts modal
subformulas" block (all 4 `it`s) and two `isValid` cases (not in any
Haskell spec — `isValid` is exercised only indirectly there, via
`isValidOnFrame`/`isValidDSFrame`/`isValidStitFrame`/`isValidXstitFrame`
in other modules), one with an expected-`false` result so a planted
`throw` cannot slip past under either polarity. Every B&D citation in
this block was checked against `notes/bd-screen.pdf` (`Definition 1.6`
p.7, `Definition 1.7`/`Proposition 1.8` p.9, `Definition 1.9` p.10,
`Proposition 1.19` p.15, `Definition 1.23` p.16, `Example 1.24` p.17,
`Definition 1.14`/`Proposition 1.16` p.12–14) — one fix: `Semantics.hs`
cites "Definition 1.16" for `isTautology`, but the PDF's Definition 1.16
is `Proposition 1.16` ("All tautological instances are valid"); the
"tautological instance" it actually defines is *Definition 1.14*. Fixed
in `Gamen/Semantics.lean`'s docstring. The three Proposition 1.8 cases
compare each side against an explicit `some true`/`some false` rather
than against each other, so a planted error on both sides (`none ==
none`) cannot pass. -/

def r : Formula := .atom "r"

/-- Figure 1.1 (B&D p. 8): W={w1,w2,w3}, R={(w1,w2),(w1,w3)}, V(p)={w1,w2},
V(q)={w2}. Shared by both `KripkeSemanticsSpec.hs`'s `frame11`/`model11`
and `PaperCorrespondence.hs`'s `fig11frame`/`fig11model` — identical
constructions in both Haskell files. -/
private def fig11frame : Option Frame := frame ["w1", "w2", "w3"] [("w1", "w2"), ("w1", "w3")]
private def fig11model : Option Model := fig11frame.map (mkModel · [("p", ["w1", "w2"]), ("q", ["w2"])])

/-- Figure 1.2 (B&D p. 17): same frame as Figure 1.1, V(p)={w2,w3}.
Counterexample to `p → ◇p ⊨ □p → p`. -/
private def fig12model : Option Model := fig11frame.map (mkModel · [("p", ["w2", "w3"])])

/-- `Except`-safe: `none` (from either a malformed fixture or a genuine
`satisfies` error) matches neither `some true` nor `some false`. -/
private def sat (m : Option Model) (w : String) (f : Formula) : Option Bool :=
  m.bind fun m => (satisfies m w f).toOption

/-- `true` only when `satisfies` actually throws (not when the fixture
itself is malformed) — used for the gamen-hs#3 regression, where the
Haskell test asserts `evaluate (satisfies m "c" f) \`shouldThrow\` anyErrorCall`. -/
private def satErrs (m : Option Model) (w : String) (f : Formula) : Bool :=
  match m with
  | none => false
  | some m => (satisfies m w f).toOption == none

private def trueIn (m : Option Model) (f : Formula) : Option Bool :=
  m.bind fun m => (isTrueIn m f).toOption

private def ent (m : Option Model) (prem : List Formula) (concl : Formula) : Option Bool :=
  m.bind fun m => (entails m prem concl).toOption

/-- `Except`-safe `isValid` over a list of possibly-malformed fixtures:
`none` if any model in `ms` is malformed or if `isValid` itself errors. -/
private def valid (ms : List (Option Model)) (f : Formula) : Option Bool :=
  (ms.mapM id).bind fun ms => (isValid ms f).toOption

private def tautology (f : Formula) : Option Bool := (isTautology f).toOption

def semanticsCases : List Case := [
  -- KripkeSemanticsSpec.hs: "Kripke structures (Definition 1.6)"
  ⟨"constructs frames",
    (fig11frame.map (·.worlds.size) == some 3)
    && (fig11frame.map (·.accessible "w1") == fig11frame.map (fun _ => Std.TreeSet.ofList ["w2", "w3"]))
    && (fig11frame.map (·.accessible "w2") == fig11frame.map (fun _ => (∅ : Std.TreeSet World)))⟩,
  -- KripkeSemanticsSpec.hs: "Semantics (Definition 1.7)"
  ⟨"evaluates atoms",
    sat fig11model "w1" p == some true && sat fig11model "w3" p == some false
    && sat fig11model "w2" q == some true && sat fig11model "w1" q == some false⟩,
  ⟨"evaluates negation",
    sat fig11model "w3" (.not p) == some true && sat fig11model "w1" (.not p) == some false⟩,
  ⟨"evaluates Box",
    sat fig11model "w1" (.box p) == some false && sat fig11model "w2" (.box p) == some true⟩,
  ⟨"evaluates Diamond",
    sat fig11model "w1" (.diamond q) == some true && sat fig11model "w3" (.diamond q) == some false⟩,
  ⟨"evaluates complex formulas",
    sat fig11model "w1" (.implies (.box p) p) == some true
    && sat fig11model "w1" (.and (.diamond p) (.diamond q)) == some true⟩,
  ⟨"errors on world not in model (gamen-hs#3)",
    let fr := frame ["a", "b"] [("a", "a"), ("a", "b"), ("b", "b")]
    let m := fr.map (mkModel · [("p", ["a", "b"]), ("q", ["b"]), ("r", ["a"])])
    let f := Formula.implies (.or (.atom "p") (.atom "q")) (.and (.not (.atom "q")) (.atom "r"))
    sat m "a" f == some true && sat m "b" f == some false && satErrs m "c" f⟩,
  -- KripkeSemanticsSpec.hs: "Truth in models (Definition 1.9)"
  ⟨"checks truth in a model",
    trueIn fig11model p == some false && trueIn fig11model (.implies .bot p) == some true⟩,
  -- KripkeSemanticsSpec.hs: "Entailment (Definition 1.23)"
  ⟨"checks entailment",
    ent fig11model [p] (.or p q) == some true && ent fig11model [p] q == some false⟩,
  -- PaperCorrespondence.hs: "Definition 1.6 (p. 7): model as triple ⟨W,R,V⟩"
  ⟨"Figure 1.1 (p. 8): |W| = 3", fig11frame.map (·.worlds.size) == some 3⟩,
  ⟨"Figure 1.1 (p. 8): R(w1) = {w2,w3} — w1 sees w2 and w3",
    fig11frame.map (·.accessible "w1") == fig11frame.map (fun _ => Std.TreeSet.ofList ["w2", "w3"])⟩,
  ⟨"Figure 1.1 (p. 8): R(w2) = ∅ — w2 is a dead end",
    fig11frame.map (·.accessible "w2") == fig11frame.map (fun _ => (∅ : Std.TreeSet World))⟩,
  ⟨"Figure 1.1 (p. 8): R(w3) = ∅ — w3 is a dead end",
    fig11frame.map (·.accessible "w3") == fig11frame.map (fun _ => (∅ : Std.TreeSet World))⟩,
  -- PaperCorrespondence.hs: "Definition 1.7 (p. 9): truth of a formula at a world"
  ⟨"clause 2 (atom): p = True at w1 (w1 ∈ V(p))", sat fig11model "w1" p == some true⟩,
  ⟨"clause 2 (atom): p = True at w2 (w2 ∈ V(p))", sat fig11model "w2" p == some true⟩,
  ⟨"clause 2 (atom): p = False at w3 (w3 ∉ V(p))", sat fig11model "w3" p == some false⟩,
  ⟨"clause 1 (⊥): ⊥ = False at w1 (⊥ is false everywhere)", sat fig11model "w1" .bot == some false⟩,
  ⟨"clause 1 (⊥): ⊥ = False at w3 (⊥ is false everywhere)", sat fig11model "w3" .bot == some false⟩,
  ⟨"clause 3 (¬): ¬p = True at w3 (w3 ∉ V(p))", sat fig11model "w3" (.not p) == some true⟩,
  ⟨"clause 3 (¬): ¬p = False at w1 (w1 ∈ V(p))", sat fig11model "w1" (.not p) == some false⟩,
  ⟨"clause 4 (∧): p∧q = True at w2 (w2 ∈ V(p) and w2 ∈ V(q))", sat fig11model "w2" (.and p q) == some true⟩,
  ⟨"clause 4 (∧): p∧q = False at w1 (w1 ∈ V(p) but w1 ∉ V(q))", sat fig11model "w1" (.and p q) == some false⟩,
  ⟨"clause 5 (∨): p∨q = False at w3 (w3 ∉ V(p) and w3 ∉ V(q))", sat fig11model "w3" (.or p q) == some false⟩,
  ⟨"clause 5 (∨): p∨q = True at w1 (w1 ∈ V(p))", sat fig11model "w1" (.or p q) == some true⟩,
  ⟨"clause 6 (→): p→q = False at w1 (p true, q false)", sat fig11model "w1" (.implies p q) == some false⟩,
  ⟨"clause 6 (→): p→q = True at w3 (p false, so implication holds)", sat fig11model "w3" (.implies p q) == some true⟩,
  ⟨"clause 7 (□): □p = False at w1 (w3 accessible but w3 ∉ V(p))", sat fig11model "w1" (.box p) == some false⟩,
  ⟨"clause 7 (□): □p = True at w2 (dead end — vacuously true, B&D p. 9)", sat fig11model "w2" (.box p) == some true⟩,
  ⟨"clause 8 (◇): ◇q = True at w1 (w2 accessible and w2 ∈ V(q))", sat fig11model "w1" (.diamond q) == some true⟩,
  ⟨"clause 8 (◇): ◇q = False at w3 (dead end, no successors)", sat fig11model "w3" (.diamond q) == some false⟩,
  -- PaperCorrespondence.hs: "Proposition 1.8 (p. 9): □/◇ duality  □A ↔ ¬◇¬A"
  ⟨"Prop 1.8: □p = False and ¬◇¬p = False at w1 (w3 accessible lacks p)",
    sat fig11model "w1" (.box p) == some false
    && sat fig11model "w1" (.not (.diamond (.not p))) == some false⟩,
  ⟨"Prop 1.8: □p = True and ¬◇¬p = True at w2 (dead end — both vacuously true)",
    sat fig11model "w2" (.box p) == some true
    && sat fig11model "w2" (.not (.diamond (.not p))) == some true⟩,
  ⟨"Prop 1.8: □p = True and ¬◇¬p = True at w3 (dead end — both vacuously true)",
    sat fig11model "w3" (.box p) == some true
    && sat fig11model "w3" (.not (.diamond (.not p))) == some true⟩,
  -- PaperCorrespondence.hs: "Definition 1.9 (p. 10): truth in a model  M ⊩ A"
  ⟨"⊥→p is true in Figure 1.1 (ex falso, true at all worlds)",
    trueIn fig11model (.implies .bot p) == some true⟩,
  ⟨"p is NOT true in Figure 1.1 (false at w3 ∉ V(p))", trueIn fig11model p == some false⟩,
  -- PaperCorrespondence.hs: "Proposition 1.19 (p. 15): K axiom is K-provable"
  ⟨"¬K is K-inconsistent (negation of K has a closed tableau)",
    consistent [.not (.implies (.box (.implies p q)) (.implies (.box p) (.box q)))] == .definitely false⟩,
  -- PaperCorrespondence.hs: "Definition 1.23 (p. 16) + Example 1.24 (p. 17): entailment"
  ⟨"Example 1.24: p→◇p = True at w1 in Figure 1.2 (p false, so implication holds)",
    sat fig12model "w1" (.implies p (.diamond p)) == some true⟩,
  ⟨"Example 1.24: □p→p = False at w1 in Figure 1.2 (□p true but p false)",
    sat fig12model "w1" (.implies (.box p) p) == some false⟩,
  ⟨"Example 1.24: {p→◇p} ⊭ □p→p — w1 witnesses the failure of entailment",
    ent fig12model [.implies p (.diamond p)] (.implies (.box p) p) == some false⟩,
  -- RegressionIssue18.hs: "B5: isTautology abstracts modal subformulas" (all 8 `it`s,
  -- including the 4 added with the gamen-hs#31 fix)
  ⟨"□⊥ is not a tautology", tautology (.box .bot) == some false⟩,
  ⟨"¬◇p is not a tautology", tautology (.not (.diamond p)) == some false⟩,
  ⟨"p ∨ ¬p is a tautology", tautology (.or p (.not p)) == some true⟩,
  ⟨"□p ∨ ¬□p is a tautology (same modal subformula abstracts alike)",
    tautology (.or (.box p) (.not (.box p))) == some true⟩,
  -- gamen-hs#31: distinct subformulas that print alike must not share a variable.
  ⟨"[a]p ∨ ¬[a!]p is not a tautology (Stit vs Announce print alike)",
    tautology (.or (.stit "a" p) (.not (.announce (.atomF ⟨"a"⟩) p))) == some false⟩,
  ⟨"[Agt]p ∨ ¬[Agt!]p is not a tautology (GroupStit vs Announce print alike)",
    tautology (.or (.groupStit p) (.not (.announce (.atomF ⟨"Agt"⟩) p))) == some false⟩,
  ⟨"[a]p ∨ ¬[a]p is a tautology (control)",
    tautology (.or (.stit "a" p) (.not (.stit "a" p))) == some true⟩,
  ⟨"a generated atom cannot collide with a user atom of the same name",
    tautology (.or (.box p) (.not (.atomF ⟨s!"__modal:{(Formula.box p).toString}"⟩))) == some false⟩,
  -- Not in gamen-hs: its collision test above uses an old-scheme name, which
  -- the fixed naming (`__modal:0`, …) can never produce, so it passes even
  -- without `modalPrefix`. A user atom named like a new-scheme atom does
  -- exercise the prefix. gamen-hs answers False here too (checked in GHCi).
  ⟨"a user atom named like a generated one (__modal:0) is not merged with it",
    tautology (.or (.box p) (.not (.atomF ⟨"__modal:0"⟩))) == some false⟩,
  -- isValid (B&D Definition 1.11), not covered by any Haskell spec. Both
  -- cases use a genuine two-model class where the models disagree on the
  -- test formula, so `isValid` really exercises "true in *every* model
  -- in the class" (Definition 1.11) rather than degenerating to a single
  -- model's `isTrueIn` — a single-model class would not catch, e.g.,
  -- `allM` mistakenly swapped for `anyM`.
  ⟨"isValid: schema K holds in the class {Figure 1.1, Figure 1.2} \
    (frame-valid by Prop 1.19, so true regardless of valuation)",
    valid [fig11model, fig12model]
      (.implies (.box (.implies p q)) (.implies (.box p) (.box q))) == some true⟩,
  ⟨"isValid: ¬q fails in the class {Figure 1.1, Figure 1.2} — fig11model's \
    w2 (q true) witnesses invalidity even though fig12model (q unvalued, \
    so false everywhere) satisfies ¬q vacuously",
    valid [fig11model, fig12model] (.not q) == some false⟩
]

/-! ## Fragment gating (`Gamen.Fragment`) -/

/-- `Except`-safe comparison for fragment checks: matches the constructor
and payload of both sides directly, so an unexpected `Except` variant
(e.g. `.error (.budgetExhausted _)` where `.ok ()` was expected) fails the
case instead of being coerced to a default `Bool`. -/
def fragOk (r expected : Except UnknownReason Unit) : Bool :=
  match r, expected with
  | .ok (), .ok () => true
  | .error e1, .error e2 => e1 == e2
  | _, _ => false

/-- Port of `test/RegressionIssue18.hs`'s "A2: fragment gating rejects
out-of-fragment operators" (all 6 `it`s), plus the fragment-boundary
assertions from `test/Properties.hs`'s "issue #25: all temporal operators
are quarantined at the fragment boundary" `it`.

That Properties.hs `it` has four numbered steps; only steps 2 and 3 belong
to `Gamen.Fragment` (`checkTableauFragment` itself). Step 1 (an exhaustive
semantic-oracle search over ≤3-world models, confirming `{HA, P¬A}` is
really unsatisfiable) belongs with `Gamen.Semantics`/model enumeration and
step 4 (`tableauConsistent systemKDt … unsat`, confirming the *raw* prover
is still wrong on the past) needs the full temporal tableau — both
`Gamen.Temporal` dependents not yet ported (see `PORTING.md`). Porting
those two steps is deferred to `Gamen.Temporal`; this file ports only the
gate. -/
def fragmentCases : List Case := [
  ⟨"G3DS fragment accepts ⊗_i p",
    fragOk (checkDSFragment (.ought "i" p)) (.ok ())⟩,
  ⟨"G3DS fragment rejects K_b q (epistemic is outside L_n)",
    fragOk (checkDSFragment (.knowledge "b" q)) (.error (.unsupportedOperator "Knowledge"))⟩,
  ⟨"G3DS fragment rejects a mixed set's epistemic member",
    fragOk (checkDSFragment (.not (.knowledge "b" q))) (.error (.unsupportedOperator "Knowledge"))⟩,
  ⟨"tableau fragment accepts □p",
    fragOk (checkTableauFragment systemK (.box p)) (.ok ())⟩,
  ⟨"tableau fragment rejects Knowledge",
    fragOk (checkTableauFragment systemK (.knowledge "a" (.and p (.not p))))
      (.error (.unsupportedOperator "Knowledge"))⟩,
  ⟨"tableau fragment rejects GroupStit (the A4 crash trigger)",
    fragOk (checkTableauFragment systemK (.groupStit p))
      (.error (.unsupportedOperator "GroupStit"))⟩,
  ⟨"issue #25 (step 2): every temporal operator is rejected, past and \
    future, including nested under another modality",
    fragOk (checkTableauFragment systemKDt (.pastBox p))
        (.error (.unsupportedOperator "PastBox"))
    && fragOk (checkTableauFragment systemKDt (.pastDiamond p))
        (.error (.unsupportedOperator "PastDiamond"))
    && fragOk (checkTableauFragment systemKDt (.futureBox p))
        (.error (.unsupportedOperator "FutureBox"))
    && fragOk (checkTableauFragment systemKDt (.futureDiamond p))
        (.error (.unsupportedOperator "FutureDiamond"))
    && fragOk (checkTableauFragment systemKDt (.box (.pastDiamond p)))
        (.error (.unsupportedOperator "PastDiamond"))
    && fragOk (checkTableauFragment systemKDt (.box (.futureBox p)))
        (.error (.unsupportedOperator "FutureBox"))⟩,
  ⟨"issue #25 (step 3): the quarantine must not over-reach — the \
    non-temporal operators the service relies on stay in fragment",
    fragOk (checkTableauFragment systemKDt (.box p)) (.ok ())
    && fragOk (checkTableauFragment systemKDt (.diamond p)) (.ok ())
    && fragOk (checkTableauFragment systemKDt (.belief "a" p)) (.ok ())
    && fragOk (checkTableauFragment systemKDt (.implies p (.not p))) (.ok ())⟩,
  -- Review fix: `firstUnsupported` (validate/Main.hs:262-269) must route
  -- *every* `Left` through `reasonOperator` (validate/Main.hs:271-276),
  -- not just `UnsupportedOperator` — `reasonOperator other = show other`
  -- for any other reason. A fragment check "should not" produce
  -- `ProverStuck`/`BudgetExhausted`, but if one ever did, treating it as
  -- in-fragment (routing the formula on to the prover) would be exactly
  -- the silent-wrong-answer bug this module exists to prevent. Verified
  -- against GHC's actual derived `Show UnknownReason`
  -- (`runghc` on the three-constructor type: `show (ProverStuck "x") ==
  -- "ProverStuck \"x\""`), not from memory or from Lean's `reprStr`.
  ⟨"firstUnsupported renders a non-UnsupportedOperator reason via \
    Haskell's derived Show, not Lean's Repr, and does not let it through \
    as in-fragment",
    firstUnsupported (fun _ => .error (.proverStuck "x")) [p] == some "ProverStuck \"x\""
    && firstUnsupported (fun _ => .error (.budgetExhausted 5)) [p] == some "BudgetExhausted 5"⟩,
  -- Review fix: pin `hasAgentOperator (GroupStit _) = False`
  -- (Formula.hs:230) even when the operand itself has an agent operator —
  -- `GroupStit` does not recurse into its operand (it is excluded outright,
  -- not merely "no agent operator at top level"), unlike the previous Lean
  -- version routed through `immediateSubformulas`.
  ⟨"hasAgentOperator (GroupStit (Stit a p)) = false (Formula.hs:230)",
    !(Formula.groupStit (Formula.stit "a" p)).hasAgentOperator⟩
]

/-! ## Property tests (Plausible) -/

/-- Kripke-fragment formulas over atoms p, q, r. Mirrors `genFormula` in
`test/Properties.hs`, plus `iff`, which the Lean `toNNF` rewrites
differently from the Haskell text and so deserves random coverage. -/
partial def genFormula : Nat → Gen Formula
  | 0 => Gen.frequency (pure .bot) [(1, pure .bot), (4, genAtom)]
  | n + 1 =>
    let h := (n + 1) / 2
    Gen.frequency (pure .bot) [
      (1, pure .bot), (4, genAtom),
      (3, .not <$> genFormula n),
      (3, .and <$> genFormula h <*> genFormula h),
      (2, .or <$> genFormula h <*> genFormula h),
      (2, .implies <$> genFormula h <*> genFormula h),
      (1, .iff <$> genFormula h <*> genFormula h),
      (2, .box <$> genFormula n),
      (2, .diamond <$> genFormula n)]
where
  genAtom : Gen Formula := do
    let ⟨i, _⟩ ← Gen.choose Nat 0 2 (by omega)
    return .atom (["p", "q", "r"].getD i "p")

instance : Arbitrary Formula := ⟨Gen.sized fun n => genFormula (min n 12)⟩

instance : Shrinkable Formula where
  shrink
    | .not g | .box g | .diamond g => [g]
    | .and l r | .or l r | .implies l r | .iff l r => [l, r]
    | _ => []

/-- A fixed 3-world model with a reflexive point, a dead end, and a cycle,
used to check that `toNNF` preserves truth everywhere. `none` if `mkFrame`
rejects it (not `get!`, whose panic would continue with an empty model and
make the properties below pass vacuously). -/
def testModel : Option Model :=
  (mkFrame ["w1", "w2", "w3"] [("w1", "w1"), ("w1", "w2"), ("w2", "w3"), ("w3", "w1")]).toOption.map
    (mkModel · [("p", ["w1", "w3"]), ("q", ["w2"]), ("r", [])])

def truthsIn (m : Option Model) (f : Formula) : Option (List Bool) :=
  m.bind fun m => (m.frame.worlds.toList.mapM (satisfies m · f)).toOption

def properties : List (String × IO Bool) :=
  let run (p : Prop) [Testable p] : IO Bool := do
    match ← Testable.checkIO p { numInst := 300, quiet := true } with
    | .failure _ xs _ => IO.println s!"    counterexample: {xs}"; return false
    | _ => return true
  -- Plausible's `Testable` instances match `NamedBinder name (∀ x, …)`; the
  -- `plausible` tactic inserts the binder names itself, but `checkIO` from
  -- plain `IO` needs them spelled out.
  [ ("toNNF idempotent",
      run (NamedBinder "f" <| ∀ f : Formula, toNNF (toNNF f) = toNNF f)),
    ("toNNF output is in NNF",
      run (NamedBinder "f" <| ∀ f : Formula, isNNF (toNNF f) = true)),
    ("toNNF preserves truth at every world",
      run (NamedBinder "f" <| ∀ f : Formula,
        ((truthsIn testModel f).isSome
          && truthsIn testModel (toNNF f) == truthsIn testModel f) = true)),
    ("tableau-valid formulas are true in the test model (soundness spot-check)",
      run (NamedBinder "f" <| ∀ f : Formula,
        (!proves [] f || truthsIn testModel f == some [true, true, true]) = true)) ]
where
  toNNF := Formula.toNNF
  isNNF := Formula.isNNF

def main : IO UInt32 := do
  let mut failures := 0
  IO.println "Unit cases"
  for c in unitCases ++ formulaCases ++ widgetCases ++ answerKeyCases ++ framePropertiesCases
      ++ kripkeCases ++ semanticsCases ++ fragmentCases do
    IO.println s!"  {if c.ok then "✓" else "✗"} {c.name}"
    unless c.ok do failures := failures + 1
  IO.println "Properties (300 random formulas each)"
  for (name, prop) in properties do
    let ok ← prop
    IO.println s!"  {if ok then "✓" else "✗"} {name}"
    unless ok do failures := failures + 1
  let total := unitCases.length + formulaCases.length + widgetCases.length + answerKeyCases.length
    + framePropertiesCases.length + kripkeCases.length + semanticsCases.length
    + fragmentCases.length + properties.length
  IO.println s!"{total - failures}/{total} passed"
  return if failures == 0 then 0 else 1
