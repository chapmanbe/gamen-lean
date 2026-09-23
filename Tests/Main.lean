import Gamen.Tableau
import Gamen.Fragment
import Gamen.FrameProperties
import Plausible
import Notebooks.Ch1HealthObligations
import Notebooks.Ch1SyntaxSemantics

/-!
# Tests

Ports of `test/TableauSpec.hs` (system K cases and countermodel extraction),
`test/FormulaSpec.hs`-style printing checks, `test/FramePropertiesSpec.hs`,
the `Definition 1.11` / `Proposition 1.19` slice of `test/PaperCorrespondence.hs`
that exercises `isValidOnFrame`, the `toNNF` properties from
`test/Properties.hs`, run with Plausible instead of QuickCheck, and
`Gamen.Fragment` (`test/RegressionIssue18.hs`'s "A2" describe block, plus
the fragment-boundary assertions from `test/Properties.hs`'s "issue #25"
`it` — see `fragmentCases` for what of that `it` is and is not ported).
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
  -- describe block in that file needs `entails`, not yet ported).
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
    && fragOk (checkTableauFragment systemKDt (.implies p (.not p))) (.ok ())⟩
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
  for c in unitCases ++ widgetCases ++ answerKeyCases ++ framePropertiesCases ++ fragmentCases do
    IO.println s!"  {if c.ok then "✓" else "✗"} {c.name}"
    unless c.ok do failures := failures + 1
  IO.println "Properties (300 random formulas each)"
  for (name, prop) in properties do
    let ok ← prop
    IO.println s!"  {if ok then "✓" else "✗"} {name}"
    unless ok do failures := failures + 1
  let total := unitCases.length + widgetCases.length + answerKeyCases.length
    + framePropertiesCases.length + fragmentCases.length + properties.length
  IO.println s!"{total - failures}/{total} passed"
  return if failures == 0 then 0 else 1
