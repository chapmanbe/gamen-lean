import Gamen.Tableau
import Plausible
import Notebooks.Ch1HealthObligations
import Notebooks.Ch1SyntaxSemantics

/-!
# Tests

Ports of `test/TableauSpec.hs` (system K cases and countermodel extraction),
`test/FormulaSpec.hs`-style printing checks, and the `toNNF` properties from
`test/Properties.hs`, run with Plausible instead of QuickCheck.
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
used to check that `toNNF` preserves truth everywhere. -/
def testModel : Model :=
  let fr := (mkFrame ["w1", "w2", "w3"] [("w1", "w1"), ("w1", "w2"), ("w2", "w3"), ("w3", "w1")]).toOption.get!
  mkModel fr [("p", ["w1", "w3"]), ("q", ["w2"]), ("r", [])]

def truthsIn (m : Model) (f : Formula) : Option (List Bool) :=
  (m.frame.worlds.toList.mapM (satisfies m · f)).toOption

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
        truthsIn testModel (toNNF f) = truthsIn testModel f)),
    ("tableau-valid formulas are true in the test model (soundness spot-check)",
      run (NamedBinder "f" <| ∀ f : Formula,
        (!proves [] f || truthsIn testModel f == some [true, true, true]) = true)) ]
where
  toNNF := Formula.toNNF
  isNNF := Formula.isNNF

def main : IO UInt32 := do
  let mut failures := 0
  IO.println "Unit cases"
  for c in unitCases ++ widgetCases ++ answerKeyCases do
    IO.println s!"  {if c.ok then "✓" else "✗"} {c.name}"
    unless c.ok do failures := failures + 1
  IO.println "Properties (300 random formulas each)"
  for (name, prop) in properties do
    let ok ← prop
    IO.println s!"  {if ok then "✓" else "✗"} {name}"
    unless ok do failures := failures + 1
  let total := unitCases.length + widgetCases.length + answerKeyCases.length + properties.length
  IO.println s!"{total - failures}/{total} passed"
  return if failures == 0 then 0 else 1
