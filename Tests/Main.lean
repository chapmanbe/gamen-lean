import Gamen.Tableau
import Gamen.Temporal
import Gamen.Doxastic
import Gamen.RankingTheory
import Gamen.Plausibility
import Gamen.Fragment
import Gamen.FrameProperties
import Gamen.DeonticStit
import Gamen.DeonticStit.Sequent
import Gamen.DeonticStit.Rules
import Gamen.DeonticStit.Saturation
import Gamen.DeonticStit.Prove
import Gamen.DeonticStit.CounterModel
import Gamen.Cgs
import Plausible
import Notebooks.Ch1HealthObligations
import Notebooks.Ch1SyntaxSemantics
import Validate.Core
import Tests.PropertyHelpers

/-!
# Tests

Ports of `test/TableauSpec.hs` in full (`tableauCases`),
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
assertions from `test/Properties.hs`'s "issue #25" `it`, all five steps — see
`fragmentCases`), `test/TemporalSpec.hs` in full plus the `Gamen.Temporal`
blocks of `test/PaperCorrespondence.hs` (`temporalCases`), and `Gamen.Kripke`'s "B7: Kripke /
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
  -- Pretty-printing matches Haskell `show`
  ⟨"show □(p → ◇q)", toString (Formula.box (.implies p (.diamond q))) == "□(p → ◇q)"⟩,
  ⟨"show agents", toString (Formula.canUntil ["a", "b"] p q) == "⟨⟨a,b⟩⟩(p U q)"⟩
]

/-! ## Tableau

Port of `test/TableauSpec.hs` in full, one case per `it`, in file order.
Verdicts are compared against `.definitely true`/`.definitely false`, so a
budget-exhausted `.unknown` fails the case whichever answer was expected
(stricter than Haskell's `TestShims`, which maps `Unknown` to `False`).
The "Chapter 14: Temporal Logics" banner at the end of the spec has no
`it`s. -/

/-- Both sides succeeded with equal values; any error fails. -/
def okEq [BEq α] : Except String α → Except String α → Bool
  | .ok a, .ok b => a == b
  | _, _ => false

def provesIn (sys : System) (prem : List Formula) (c : Formula) : Verdict :=
  tableauProves sys defaultMaxSteps prem c
def consistentIn (sys : System) (fs : List Formula) : Verdict :=
  tableauConsistent sys defaultMaxSteps fs

/-- Open branches of the tableau for F φ at the root (a countermodel search;
Haskell `openFor`). -/
def openFor (sys : System) (phi : Formula) : List Branch :=
  match buildTableau sys 1000 [pfFalse .root phi] with
  | .stillOpen bs => bs
  | _ => []

/-- Every open branch extracts a model that falsifies φ at the root
(Haskell `allExtract`). -/
def allExtract (sys : System) (phi : Formula) : Bool :=
  let bs := openFor sys phi
  !bs.isEmpty && bs.all fun b =>
    okEq (extractCountermodel sys b >>= fun m => satisfies m "1" phi) (.ok false)

def tableauCases : List Case :=
  let yes : Verdict := .definitely true
  let no : Verdict := .definitely false
  let schemaK : Formula := .implies (.box (.implies p q)) (.implies (.box p) (.box q))
  let axT : Formula := .implies (.box p) p
  let ax4 : Formula := .implies (.box p) (.box (.box p))
  let axD : Formula := .implies (.box p) (.diamond p)
  let bpDbp : Formula := .implies (.box p) (.diamond (.box p))
  let ax5 : Formula := .implies (.diamond p) (.box (.diamond p))
  let σ1 := mkPrefix [1]
  let σ12 := mkPrefix [1, 2]
  let pf1 := pfTrue .root p
  let pf2 := pfFalse .root p
  let pf3 := pfTrue .root q
  [
  -- describe "Prefix (Definition 6.1)" [B&D §6.1: no numbered definition]
  ⟨"constructs and extends prefixes",
    okEq (σ1 >>= (extendPrefix · 2)) σ12
    && okEq (σ12 >>= parentPrefix) σ1
    && okEq (toString <$> mkPrefix [1, 2, 3]) (.ok "1.2.3")⟩,
  -- describe "PrefixedFormula and branch closure (Definition 6.2)" [B&D §6.1 prefixed
  -- formulas, §6.2 closure; no numbered definitions]
  ⟨"detects open branches", !(Branch.ofList [pf1, pf3]).isClosed⟩,
  ⟨"detects closed branches", (Branch.ofList [pf1, pf2]).isClosed⟩,
  ⟨"requires matching prefixes for closure",
    match mkPrefix [1, 1] with
    | .ok σ2 => !(Branch.ofList [pf1, pfFalse σ2 p]).isClosed
    | .error _ => false⟩,
  -- describe "K rules: Examples 6.1 and 6.2 (B&D)"
  ⟨"proves (□p ∧ □q) → □(p ∧ q)",
    provesIn systemK [] (.implies (.and (.box p) (.box q)) (.box (.and p q))) == yes⟩,
  ⟨"proves ◇(p ∨ q) → (◇p ∨ ◇q)",
    provesIn systemK [] (.implies (.diamond (.or p q)) (.or (.diamond p) (.diamond q))) == yes⟩,
  ⟨"proves Schema K: □(p→q) → (□p→□q)", provesIn systemK [] schemaK == yes⟩,
  ⟨"does not prove T: □p → p", provesIn systemK [] axT == no⟩,
  ⟨"does not prove 4: □p → □□p", provesIn systemK [] ax4 == no⟩,
  -- describe "Soundness: non-theorems in K (Theorem 6.6)"
  ⟨"□p does not entail ◇p (seriality not assumed)", provesIn systemK [.box p] (.diamond p) == no⟩,
  ⟨"◇p does not entail □p", provesIn systemK [] (.implies (.diamond p) (.box p)) == no⟩,
  ⟨"proves dual: ¬◇¬p → □p",
    provesIn systemK [] (.implies (.not (.diamond (.not p))) (.box p)) == yes⟩,
  -- describe "Consistency in K"
  ⟨"{□p, ◇q} is satisfiable in K", consistentIn systemK [.box p, .diamond q] == yes⟩,
  ⟨"{p, ¬p} is unsatisfiable", consistentIn systemK [p, .not p] == no⟩,
  ⟨"{p → q, ¬q} is satisfiable", consistentIn systemK [.implies p q, .not q] == yes⟩,
  ⟨"{p → q, p} is satisfiable", consistentIn systemK [.implies p q, p] == yes⟩,
  ⟨"{p ∨ q, ¬q} is satisfiable", consistentIn systemK [.or p q, .not q] == yes⟩,
  ⟨"{p ∨ q, ¬p} is satisfiable", consistentIn systemK [.or p q, .not p] == yes⟩,
  ⟨"{p, p ∨ q, ¬q} is satisfiable", consistentIn systemK [p, .or p q, .not q] == yes⟩,
  -- describe "Countermodel extraction (Theorem 6.19)"
  ⟨"extracts a countermodel for □p → p", countermodelCase⟩,
  -- Issue #38: the D rules fire only at prefixes with a modal formula, so a
  -- modal-free prefix had no successor and the KD model was not serial.
  ⟨"KD countermodel is serial even at modal-free worlds (#38)",
    (openFor systemKD p).all fun b =>
      match extractCountermodel systemKD b with
      | .ok m => isSerial m.frame
      | .error _ => false⟩,
  -- Issue #39: a branch open only because a prefix is blocked failed the
  -- extraction's own re-check; the blocked prefix had no witnesses.
  ⟨"extracts from every open branch with a blocked prefix: K, □□p ↔ ¬□p (#39)",
    allExtract systemK (.iff (.box (.box p)) (.not (.box p)))⟩,
  -- Faithful port of the gamen-hs case, but it does not pin the #39 fix for
  -- KD: it still passes with KD's borrowing disabled, because
  -- `serialClose`'s self-loop at the blocked prefix already satisfies it.
  -- The Not-in-gamen-hs KD case in `crossCheckCases` does need borrowing.
  ⟨"extracts from every open branch with a blocked prefix: KD, □□p ↔ ¬□p (#39)",
    allExtract systemKD (.iff (.box (.box p)) (.not (.box p)))⟩,
  ⟨"extracts from every open branch with a blocked prefix: K4, ◇□p ∧ □⊥ (#39)",
    allExtract systemK4 (.and (.diamond (.box p)) (.box .bot))⟩,
  -- describe "KT rules: T axiom (Table 6.4)"
  ⟨"KT proves T: □p → p", provesIn systemKT [] axT == yes⟩,
  ⟨"KT proves Schema K", provesIn systemKT [] schemaK == yes⟩,
  ⟨"KT does not prove 4: □p → □□p", provesIn systemKT [] ax4 == no⟩,
  -- describe "KD rules: D axiom (Table 6.4)"
  ⟨"KD proves D: □p → ◇p", provesIn systemKD [] axD == yes⟩,
  ⟨"K does not prove D: □p → ◇p", provesIn systemK [] axD == no⟩,
  -- describe "KB rules: B axiom (Table 6.4)". gamen-hs names □p → ◇□p
  -- "B"; B&D's B is A → □◇A (Table 2.1), while □A → ◇□A already holds
  -- on every reflexive frame. Formula kept, label corrected.
  ⟨"KB proves □p → ◇□p (gamen-hs: \"B\")", provesIn systemKB [] bpDbp == yes⟩,
  ⟨"K does not prove □p → ◇□p (gamen-hs: \"B\")", provesIn systemK [] bpDbp == no⟩,
  -- describe "K4 rules: 4 axiom (Table 6.4)"
  ⟨"K4 proves 4: □p → □□p", provesIn systemK4 [] ax4 == yes⟩,
  ⟨"K does not prove 4", provesIn systemK [] ax4 == no⟩,
  -- describe "S4 rules: T + 4 (Table 6.4)"
  ⟨"S4 proves T: □p → p", provesIn systemS4 [] axT == yes⟩,
  ⟨"S4 proves 4: □p → □□p", provesIn systemS4 [] ax4 == yes⟩,
  ⟨"S4 does not prove 5: ◇p → □◇p", provesIn systemS4 [] ax5 == no⟩,
  -- describe "S5 rules: T + B + 4 + 4r (Table 6.4)"
  ⟨"S5 proves T: □p → p", provesIn systemS5 [] axT == yes⟩,
  ⟨"S5 proves 4: □p → □□p", provesIn systemS5 [] ax4 == yes⟩,
  ⟨"S5 proves 5: ◇p → □◇p", provesIn systemS5 [] ax5 == yes⟩,
  -- gamen-hs cites Example 6.9 here, but Example 6.9 proves
  -- S5 ⊢ □A → □◇A, not □A → ◇□A.
  ⟨"S5 proves □p → ◇□p (gamen-hs: \"B\", \"Example 6.9\")", provesIn systemS5 [] bpDbp == yes⟩,
  ⟨"S5 proves Schema K", provesIn systemS5 [] schemaK == yes⟩,
  -- describe "Consistency in extended systems"
  ⟨"{□p, ¬p} is unsatisfiable in KT", consistentIn systemKT [.box p, .not p] == no⟩,
  ⟨"{□p, ¬p} is satisfiable in K (no reflexivity)", consistentIn systemK [.box p, .not p] == yes⟩,
  ⟨"KD: {p → □(¬q), □q} is satisfiable",
    consistentIn systemKD [.implies p (.box (.not q)), .box q] == yes⟩,
  ⟨"KD: {p → □q, ¬p} is satisfiable", consistentIn systemKD [.implies p (.box q), .not p] == yes⟩,
  ⟨"KD: {□p, □¬p} is unsatisfiable (seriality forces a clashing successor)",
    consistentIn systemKD [.box p, .box (.not p)] == no⟩,
  ⟨"KD: a modal conflict is not masked by a noisy implication bundle",
    let noise := (List.range 10).map fun i =>
      Formula.implies (.atom s!"a{i + 1}") (.atom s!"b{i + 1}")
    consistentIn systemKD (noise ++ [.box p, .box (.not p)]) == no⟩,
  -- Not in TableauSpec.hs: without these, removing B□/B◇ from systemKB and
  -- systemS5 left every case green. Verdicts confirmed in gamen-hs
  -- (cabal repl). B is A → □◇A (B&D Table 2.1).
  ⟨"KTB proves B: p → □◇p", provesIn systemKB [] (.implies p (.box (.diamond p))) == yes⟩,
  ⟨"KTB does not prove 4: □p → □□p", provesIn systemKB [] ax4 == no⟩
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
  ⟨"a user atom named by the old printed-form scheme (__modal:□p) is not merged",
    tautology (.or (.box p) (.not (.atomF ⟨s!"__modal:{(Formula.box p).toString}"⟩))) == some false⟩,
  -- The old-scheme name above can never be generated by the fixed naming
  -- (`__modal:0`, …), so only this case exercises `modalPrefix`
  -- (gamen-hs#33).
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
    valid [fig11model, fig12model] (.not q) == some false⟩,
  -- Not in gamen-hs. `And`/`Or` must short-circuit like Haskell's lazy
  -- `&&`/`||`: the right side (an operator `satisfies` has no semantics
  -- for) must never be evaluated once the left side already settles the
  -- result. Expected values from gamen-hs GHCi on `fig11model`-equivalent
  -- fixture (p true at w1): `satisfies m "w1" (And Bot (Stit "i" p))` ⇒
  -- `False`; `satisfies m "w1" (Or p (Knowledge "i" p))` ⇒ `True`.
  ⟨"And Bot _ short-circuits to False without evaluating an erroring right side",
    sat fig11model "w1" (.and .bot (.stit "i" p)) == some false⟩,
  ⟨"Or p _ short-circuits to True without evaluating an erroring right side",
    sat fig11model "w1" (.or p (.knowledge "i" p)) == some true⟩
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

/-- All subsets of a list (Haskell `subsequencesOf` in `Properties.hs`). -/
private def subsequencesOf {α : Type} : List α → List (List α)
  | [] => [[]]
  | x :: xs => let r := subsequencesOf xs; r ++ r.map (x :: ·)

/-- Issue #25 step 1: does any model on 1–3 worlds (every frame, every
valuation of `p`) satisfy all of `fs` at some world? `Except`, so a
malformed fixture or a `satisfies` error cannot read as "no". -/
private def anyModelSatisfiesAll (fs : List Formula) : Except String Bool := do
  let ws3 := ["w1", "w2", "w3"]
  let models ← ([1, 2, 3].flatMap fun n =>
      let ws := ws3.take n
      (subsequencesOf (ws.flatMap fun a => ws.map fun b => (a, b))).flatMap fun es =>
        (subsequencesOf ws).map fun vs => (ws, es, vs)).mapM
    fun (ws, es, vs) => do return mkModel (← mkFrame ws es) [("p", vs)]
  models.anyM fun m => m.frame.worlds.toList.anyM fun w => fs.allM (satisfies m w)

/-- Port of `test/RegressionIssue18.hs`'s "A2: fragment gating rejects
out-of-fragment operators" (all 6 `it`s), plus the fragment-boundary
assertions from `test/Properties.hs`'s "issue #25: all temporal operators
are quarantined at the fragment boundary" `it`.

That Properties.hs `it` has five numbered steps, ported as one case each.
Steps 2 and 3 exercise `Gamen.Fragment` (`checkTableauFragment` itself);
step 1 (an exhaustive semantic-oracle search over ≤3-world models,
confirming `{HA, P¬A}` is really unsatisfiable), step 4 (the *raw*
`tableauConsistent systemKDt` still calls that set satisfiable), and step
5 (the semantics of the temporal operators is untouched by the quarantine)
were deferred until `Gamen.Temporal` was ported. -/
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
  ⟨"issue #25 (step 1): the semantic oracle confirms {HA, P¬A} is \
    unsatisfiable — no model on up to 3 worlds satisfies it anywhere",
    okEq (anyModelSatisfiesAll [.pastBox p, .pastDiamond (.not p)]) (.ok false)⟩,
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
  ⟨"issue #25 (step 4): the raw prover is unchanged and still wrong on \
    the past — tableauConsistent systemKDt 4000 {HA, P¬A} is Definitely True",
    tableauConsistent systemKDt 4000 [.pastBox p, .pastDiamond (.not p)]
      == .definitely true⟩,
  ⟨"issue #25 (step 5): the semantic layer is untouched — satisfies still \
    evaluates temporal operators",
    let m2 := (frame ["w1", "w2"] [("w1", "w2")]).map (mkModel · [("p", ["w1"])])
    sat m2 "w1" (.futureBox p) == some false
    && sat m2 "w1" (.futureDiamond p) == some false
    && sat m2 "w2" (.pastDiamond p) == some true⟩,
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

/-! ## Temporal logic (`Gamen.Temporal`)

Port of `test/TemporalSpec.hs` in full (all 19 `it`s), then the three
`Gamen.Temporal` describe blocks of `test/PaperCorrespondence.hs` ("frame
conditions", 6 `it`s; "G/F/H/P semantics (over tmLinear …)", 4; "systemKDt
tableau …", 3). B&D citations checked against `bd-screen.pdf` (F25):
Definition 14.2 (p. 184), Definition 14.4 (p. 185), Table 14.1 (p. 186).
The spec's "Until and Since" block said "no B&D chapter"; F25 has them as
Definition 14.5 (p. 187), with the arguments the other way round (B&D's
S B C has witness B; gamen-hs's `Since a b` has witness `b`).

Verdicts are compared against `.definitely true`/`.definitely false` with
the Haskell shim's budget (1000 = `defaultMaxSteps`), so a budget-exhausted
`.unknown` fails the case whichever answer was expected. -/

/-- `tmLinear` (`PaperCorrespondence.hs`): past → present → future,
V(p) = {past, present}, V(q) = {future}. -/
private def tmLinear : Option Model :=
  (frame ["past", "present", "future"] [("past", "present"), ("present", "future")]).map
    (mkModel · [("p", ["past", "present"]), ("q", ["future"])])

def temporalCases : List Case :=
  let yes : Verdict := .definitely true
  let no : Verdict := .definitely false
  -- "Temporal model semantics": t1 ≺ t2 ≺ t3, p at t1 and t2, q at t3
  let m := (frame ["t1", "t2", "t3"] [("t1", "t2"), ("t2", "t3")]).map
    (mkModel · [("p", ["t1", "t2"]), ("q", ["t3"])])
  -- "Until and Since": the frame carries the transitive closure
  let mDirect := (frame ["t1", "t2", "t3"] [("t1", "t2"), ("t1", "t3"), ("t2", "t3")]).map
    (mkModel · [("p", ["t1", "t2"]), ("q", ["t3"])])
  [
  -- TemporalSpec.hs: "Temporal formula construction (Definition 14.2)"
  ⟨"displays temporal formulas",
    toString (Formula.futureDiamond p) == "Fp" && toString (Formula.futureBox p) == "Gp"
    && toString (Formula.pastDiamond p) == "Pp" && toString (Formula.pastBox p) == "Hp"⟩,
  ⟨"temporal formulas are not modal-free",
    !(Formula.futureDiamond p).isModalFree && !(Formula.since p q).isModalFree⟩,
  -- TemporalSpec.hs: "Temporal model semantics (Definition 14.4)"
  ⟨"evaluates FutureDiamond (F)",
    sat m "t1" (.futureDiamond p) == some true && sat m "t1" (.futureDiamond q) == some false
    && sat m "t2" (.futureDiamond q) == some true⟩,
  ⟨"evaluates FutureBox (G)",
    sat m "t1" (.futureBox q) == some false && sat m "t2" (.futureBox q) == some true
    && sat m "t3" (.futureBox p) == some true⟩,
  ⟨"evaluates PastDiamond (P)",
    sat m "t1" (.pastDiamond p) == some false && sat m "t2" (.pastDiamond p) == some true
    && sat m "t3" (.pastDiamond p) == some true⟩,
  ⟨"evaluates PastBox (H)",
    sat m "t1" (.pastBox q) == some true && sat m "t2" (.pastBox q) == some false
    && sat m "t3" (.pastBox q) == some false⟩,
  -- TemporalSpec.hs: "Until and Since operators (B&D Definition 14.5, p. 187;
  -- frame must carry transitive closure)"
  ⟨"evaluates Until",
    sat mDirect "t1" (.until p q) == some true && sat mDirect "t1" (.until q q) == some false⟩,
  ⟨"evaluates Since", sat mDirect "t3" (.since q p) == some true⟩,
  -- TemporalSpec.hs: "Temporal frame properties (Table 14.1)"
  ⟨"detects transitive frames",
    holds isTransitiveFrame (frame ["t1", "t2", "t3"] [("t1", "t2"), ("t2", "t3")]) == some false
    && holds isTransitiveFrame
      (frame ["t1", "t2", "t3"] [("t1", "t2"), ("t2", "t3"), ("t1", "t3")]) == some true⟩,
  ⟨"detects linear frames",
    holds isLinearFrame
      (frame ["t1", "t2", "t3"] [("t1", "t2"), ("t2", "t3"), ("t1", "t3")]) == some true
    && holds isLinearFrame (frame ["t1", "t2", "t3"] [("t1", "t2"), ("t1", "t3")]) == some false⟩,
  ⟨"detects dense frames",
    holds isDenseFrame (frame ["t1", "t2"] [("t1", "t2")]) == some false
    && holds isDenseFrame (frame ["t1", "t2"] [("t1", "t2"), ("t2", "t2")]) == some true⟩,
  ⟨"detects unbounded past/future",
    let bounded := frame ["t1", "t2"] [("t1", "t2")]
    let cyclic := frame ["t1", "t2"] [("t1", "t2"), ("t2", "t1")]
    holds isUnboundedPast bounded == some false && holds isUnboundedFuture bounded == some false
    && holds isUnboundedPast cyclic == some true && holds isUnboundedFuture cyclic == some true⟩,
  -- TemporalSpec.hs: "Combined deontic-temporal (KDt)"
  ⟨"proves Gp → p (temporal reflexivity)",
    provesIn systemKDt [] (.implies (.futureBox p) p) == yes⟩,
  ⟨"proves Gp → Fp (box implies diamond via reflexivity)",
    provesIn systemKDt [] (.implies (.futureBox p) (.futureDiamond p)) == yes⟩,
  ⟨"O(Fp) ∧ O(G¬p) is inconsistent",
    consistentIn systemKDt [.box (.futureDiamond p), .box (.futureBox (.not p))] == no⟩,
  ⟨"proves G(□p) → □p (temporal reflexivity through deontic)",
    provesIn systemKDt [] (.implies (.futureBox (.box p)) (.box p)) == yes⟩,
  ⟨"proves □(Fp) → ◇(Fp) (D axiom through temporal)",
    provesIn systemKDt [] (.implies (.box (.futureDiamond p)) (.diamond (.futureDiamond p))) == yes⟩,
  ⟨"{p → □(G¬q), □(Fq)} is satisfiable (set p=false)",
    consistentIn systemKDt [.implies p (.box (.futureBox (.not q))), .box (.futureDiamond q)] == yes⟩,
  ⟨"{Gp, F¬p} is unsatisfiable (reflexivity + propagation)",
    consistentIn systemKDt [.futureBox p, .futureDiamond (.not p)] == no⟩,
  -- PaperCorrespondence.hs: "Gamen.Temporal: frame conditions"
  ⟨"isTransitiveFrame = True: {t1→t2→t3, t1→t3} is transitively closed",
    holds isTransitiveFrame
      (frame ["t1", "t2", "t3"] [("t1", "t2"), ("t2", "t3"), ("t1", "t3")]) == some true⟩,
  ⟨"isTransitiveFrame = False: {t1→t2→t3} without t1→t3 is not transitively closed",
    holds isTransitiveFrame (frame ["t1", "t2", "t3"] [("t1", "t2"), ("t2", "t3")]) == some false⟩,
  ⟨"isLinearFrame = True: total order {t1→t2→t3} is linear",
    holds isLinearFrame
      (frame ["t1", "t2", "t3"] [("t1", "t2"), ("t2", "t3"), ("t1", "t3")]) == some true⟩,
  ⟨"isLinearFrame = False: branching frame {t1→t2, t1→t3} is not linear",
    holds isLinearFrame (frame ["t1", "t2", "t3"] [("t1", "t2"), ("t1", "t3")]) == some false⟩,
  ⟨"isUnboundedFuture = True: cycle {t1→t2→t1} gives every world a successor",
    holds isUnboundedFuture (frame ["t1", "t2"] [("t1", "t2"), ("t2", "t1")]) == some true⟩,
  ⟨"isUnboundedFuture = False: t2 has no successor in {t1→t2}",
    holds isUnboundedFuture (frame ["t1", "t2"] [("t1", "t2")]) == some false⟩,
  -- PaperCorrespondence.hs: "Gamen.Temporal: G/F/H/P semantics (over tmLinear)"
  ⟨"G (FutureBox): Gp false at 'present' — only successor 'future' lacks p",
    sat tmLinear "present" (.futureBox p) == some false⟩,
  ⟨"F (FutureDiamond): Fq true at 'present' — successor 'future' has q",
    sat tmLinear "present" (.futureDiamond q) == some true⟩,
  ⟨"H (PastBox): Hp true at 'present' — only predecessor 'past' has p",
    sat tmLinear "present" (.pastBox p) == some true⟩,
  ⟨"P (PastDiamond): Pq false at 'present' — predecessor 'past' lacks q",
    sat tmLinear "present" (.pastDiamond q) == some false⟩,
  -- PaperCorrespondence.hs: "Gamen.Temporal: systemKDt tableau (reflexive+transitive+serial)"
  ⟨"Gp ∧ ¬p is KDt-inconsistent (T rule derives p from Gp, closing with ¬p)",
    consistentIn systemKDt [.futureBox p, .not p] == no⟩,
  ⟨"Hp ∧ ¬p is KDt-inconsistent (past T rule derives p from Hp)",
    consistentIn systemKDt [.pastBox p, .not p] == no⟩,
  ⟨"Gp alone is KDt-consistent",
    consistentIn systemKDt [.futureBox p] == yes⟩,
  -- Not in gamen-hs: one case per temporal rule that no case above needs
  -- (gamen-hs's temporal property is disabled for #25, so nothing there
  -- exercises them). Verdicts checked against gamen-hs with runghc
  -- (`tableauProves`/`tableauConsistent`, budget 1000).
  ⟨"Not in gamen-hs: KDt proves Gp → GGp (needs 4G)",
    provesIn systemKDt [] (.implies (.futureBox p) (.futureBox (.futureBox p))) == yes⟩,
  ⟨"Not in gamen-hs: KDt proves FFp → Fp (needs 4F)",
    provesIn systemKDt [] (.implies (.futureDiamond (.futureDiamond p)) (.futureDiamond p)) == yes⟩,
  ⟨"Not in gamen-hs: {Gp, FF¬p} is KDt-inconsistent (needs 4G)",
    consistentIn systemKDt [.futureBox p, .futureDiamond (.futureDiamond (.not p))] == no⟩,
  ⟨"Not in gamen-hs: {F(Hp), ¬p} is KDt-inconsistent (needs 4H: the child's \
    Hp reaches the root)",
    consistentIn systemKDt [.futureDiamond (.pastBox p), .not p] == no⟩,
  ⟨"Not in gamen-hs: {F(¬Pp), p} is KDt-inconsistent (needs 4P: the child's \
    F Pp reaches the root)",
    consistentIn systemKDt [.futureDiamond (.not (.pastDiamond p)), p] == no⟩,
  ⟨"Not in gamen-hs: {Gp, F¬p} is K-inconsistent (base GT rule, no T/4 to mask it)",
    consistentIn systemK [.futureBox p, .futureDiamond (.not p)] == no⟩,
  ⟨"Not in gamen-hs: {¬Fp, F(p ∧ q)} is K-inconsistent (base FF rule)",
    consistentIn systemK [.not (.futureDiamond p), .futureDiamond (.and p q)] == no⟩
  ]

/-! ## Doxastic belief (`Gamen.Doxastic`)

`test/DoxasticSpec.hs` does not exist in gamen-hs, so there are no spec
`it`s to port. Port of the "applyDoxasticDRule: tableau closure for
contradictory beliefs" describe block under "Gamen.Doxastic — KD45 belief
(non-factive)" in `test/PaperCorrespondence.hs` (all 3 `it`s).

The sibling describe blocks in that section, "Non-factiveness: B_a φ at w
does not entail φ at w" and "D axiom: B_a φ → ¬B_a(¬φ) (doxastic
seriality)" (3 `it`s each), exercise `eSatisfies`/`mkEpistemicModel`/
`mkEpistemicFrameWithBelief`/`Knowledge`, all from `Gamen.Epistemic`, which
is not ported (see `PORTING.md`) — skipped until that module lands. -/

/-- `KD-belief` system used by the PaperCorrespondence tableau block:
`doxasticRules` as used-prefix rules, no witness rules. -/
def doxBeliefSystem : System := ⟨"KD-belief", doxasticRules, []⟩

def doxasticCases : List Case := [
  ⟨"B_a p is satisfiable on its own",
    tableauConsistent doxBeliefSystem defaultMaxSteps [.belief "a" p]
      == .definitely true⟩,
  ⟨"B_a p ∧ B_a(¬p) is unsatisfiable — D rule closes the branch",
    tableauConsistent doxBeliefSystem defaultMaxSteps
      [.belief "a" p, .belief "a" (.not p)] == .definitely false⟩,
  ⟨"B_a p ∧ B_b(¬p) is satisfiable — D rule is per-agent; agents may disagree",
    tableauConsistent doxBeliefSystem defaultMaxSteps
      [.belief "a" p, .belief "b" (.not p)] == .definitely true⟩
]

/-! ## Ranking theory (`Gamen.RankingTheory`)

Port of `test/RankingTheorySpec.hs` in full (40 `it`s, in file order), then
the "Spohn (1988) — ranking theory" section of `test/PaperCorrespondence.hs`
in full (15 `it`s), then "B4: ranking theory κ=∞ no longer leaks into
arithmetic" from `test/RegressionIssue18.hs` (5 `it`s). An `it` with several
`shouldBe`s is one case joining them with `&&`.

Every `Except` result is compared against `.ok v` (`okIs`), so an error
fails the case whichever answer was expected; the Haskell `shouldThrow`
cases check for `.error` (`isErr`). Tableau verdicts are compared against
`.definitely true`/`.definitely false`, so budget exhaustion fails too.

One case name differs from the Haskell: "conditionalize is overwrite, not
additive (Spohn p.117)" cites p.118 here, where the quoted passage is in
`notes/spohn1988-ordinal-conditional-functions.pdf`. -/

/-- `e` succeeded with value `v`; an error fails. -/
def okIs [BEq α] (e : Except String α) (v : α) : Bool :=
  match e with
  | .ok a => a == v
  | .error _ => false

/-- `e` is an error (Haskell `shouldThrow anyErrorCall`). -/
def isErr (e : Except String α) : Bool :=
  match e with
  | .ok _ => false
  | .error _ => true

def rkX : Formula := .atom "X"

/-- Two worlds, w1 ⊨ X, w2 ⊨ ¬X; κ_c(w1) = 0, κ_c(w2) = 2. -/
def rkM2 : KappaModel :=
  mkKappaModel ["w1", "w2"] [("c", [("w1", 0), ("w2", 2)])] [("X", ["w1"])]

/-- The same two worlds with c neutral about X. -/
def rkNeutral : KappaModel :=
  mkKappaModel ["w1", "w2"] [("c", [("w1", 0), ("w2", 0)])] [("X", ["w1"])]

/-- PaperCorrespondence reference model: κ_c(w1) = 0, κ_c(w2) = 3. -/
def rkM0 : KappaModel :=
  mkKappaModel ["w1", "w2"] [("c", [("w1", 0), ("w2", 3)])] [("X", ["w1"])]

def rkSys : System := { systemK with usedPrefixRules := rankingRules }

def rkCheck (fs : List Formula) : Verdict := consistentIn rkSys fs

/-- The cwyde 5-row assertion-category mapping. -/
def cwydeAssertion : String → Option Formula
  | "DEFINITE_EXISTENCE" => some (.rankedBelief "c" 2 rkX)
  | "PROBABLE_EXISTENCE" => some (.rankedBelief "c" 1 rkX)
  | "AMBIVALENT_EXISTENCE" => some (.rankedBelief "c" 0 rkX)
  | "PROBABLE_NEGATED_EXISTENCE" => some (.rankedBelief "c" (-1) rkX)
  | "DEFINITE_NEGATED_EXISTENCE" => some (.rankedBelief "c" (-2) rkX)
  | _ => none

/-- Consistency verdict of the named cwyde categories; `none` on an unknown
category name (Haskell's `error "unknown cwyde category"`). -/
def cwydeCheck (cats : List String) : Option Verdict :=
  (cats.mapM cwydeAssertion).map rkCheck

def rankingTheoryCases : List Case := [
  -- RankingTheory: Formula constructor and Show
  ⟨"RankedBelief shows with κ-notation and signed rank",
    toString (Formula.rankedBelief "c" 2 rkX) == "κ[c,2]X"
      && toString (Formula.rankedBelief "c" (-2) rkX) == "κ[c,-2]X"
      && toString (Formula.rankedBelief "c" 0 rkX) == "κ[c,0]X"⟩,
  ⟨"rank-0 is a meaningful (non-vacuous) assertion under signed semantics",
    Formula.rankedBelief "c" 0 rkX != .rankedBelief "c" 1 rkX⟩,
  ⟨"atoms recurses under RankedBelief",
    (Formula.rankedBelief "c" 2 (.and p q)).atoms.toList == [⟨"p"⟩, ⟨"q"⟩]⟩,
  ⟨"toNNF preserves RankedBelief structure",
    (Formula.rankedBelief "c" 2 (.implies p q)).toNNF == .rankedBelief "c" 2 (.or (.not p) q)⟩,
  ⟨"isNNF accepts RankedBelief over an NNF body",
    (Formula.rankedBelief "c" 2 p).isNNF == true
      && (Formula.rankedBelief "c" 2 (.implies p q)).isNNF == false⟩,
  -- RankingTheory: KappaModel semantics
  ⟨"wellFormed accepts a properly constructed model", wellFormed rkM2 == true⟩,
  ⟨"wellFormed rejects a model with no κ=0 world",
    wellFormed (mkKappaModel ["w1"] [("c", [("w1", 1)])] []) == false⟩,
  ⟨"kappaProp computes min over a proposition",
    okIs (kappaProp rkM2 "c" (.ofList ["w1"])) 0
      && okIs (kappaProp rkM2 "c" (.ofList ["w2"])) 2
      && okIs (kappaProp rkM2 "c" (.ofList ["w1", "w2"])) 0⟩,
  ⟨"tau gives a positive firmness for a believed proposition", okIs (tau rkM2 "c" rkX) 2⟩,
  ⟨"tau gives a negative firmness for a disbelieved proposition",
    okIs (tau rkM2 "c" (.not rkX)) (-2)⟩,
  ⟨"kappaSat: RankedBelief holds at the asserted exact rank",
    okIs (kappaSat rkM2 "w1" (.rankedBelief "c" 2 rkX)) true
      && okIs (kappaSat rkM2 "w1" (.rankedBelief "c" 1 rkX)) false
      && okIs (kappaSat rkM2 "w1" (.rankedBelief "c" (-2) rkX)) false⟩,
  ⟨"kappaSat: RankedBelief is global (same answer at every world)",
    okEq (kappaSat rkM2 "w1" (.rankedBelief "c" 2 rkX))
      (kappaSat rkM2 "w2" (.rankedBelief "c" 2 rkX))⟩,
  ⟨"kappaSat: rank-0 (neutrality) holds when both halves are at κ=0",
    okIs (kappaSat rkNeutral "w1" (.rankedBelief "c" 0 rkX)) true⟩,
  ⟨"kappaSat negation symmetry: τ(¬φ) = -τ(φ)",
    okIs (kappaSat rkM2 "w1" (.rankedBelief "c" (-2) (.not rkX))) true⟩,
  ⟨"kappaSat errors on a world not in the model", isErr (kappaSat rkM2 "wstray" rkX)⟩,
  -- RankingTheory: Conditionalization (Spohn Def. 6)
  ⟨"conditionalize +n shifts ¬φ-worlds up by n (overwrite)",
    okIs (do tau (← conditionalize rkNeutral "c" rkX 2) "c" rkX) 2⟩,
  ⟨"conditionalize -n shifts φ-worlds up by n (evidence against)",
    okIs (do tau (← conditionalize rkNeutral "c" rkX (-3)) "c" rkX) (-3)⟩,
  ⟨"conditionalize is overwrite, not additive (Spohn p.118)",
    okIs (do
      let m1 ← conditionalize rkNeutral "c" rkX 2
      let m2' ← conditionalize m1 "c" rkX 1
      tau m2' "c" rkX) 1⟩,
  ⟨"conditionalization preserves well-formedness",
    okIs (wellFormed <$> conditionalize rkNeutral "c" rkX 2) true⟩,
  -- RankingTheory: applyEvidence (additive aggregation)
  ⟨"two +evidence applications stack additively",
    okIs (do
      let m1 ← applyEvidence rkNeutral "c" rkX 2
      let m2' ← applyEvidence m1 "c" rkX 1
      tau m2' "c" rkX) 3⟩,
  ⟨"+ evidence followed by - evidence partially cancels",
    okIs (do
      let m1 ← applyEvidence rkNeutral "c" rkX 2
      let m2' ← applyEvidence m1 "c" rkX (-1)
      tau m2' "c" rkX) 1⟩,
  ⟨"+ and - of equal magnitude returns to neutrality",
    okIs (do
      let m1 ← applyEvidence rkNeutral "c" rkX 2
      let m2' ← applyEvidence m1 "c" rkX (-2)
      tau m2' "c" rkX) 0⟩,
  ⟨"applyEvidence preserves well-formedness",
    okIs (wellFormed <$> applyEvidence rkNeutral "c" rkX 2) true⟩,
  -- RankingTheory: combineIndependent (use under independence only)
  ⟨"is integer addition",
    combineIndependent 2 3 == 5 && combineIndependent 2 (-3) == -1
      && combineIndependent (-2) (-3) == -5 && combineIndependent 0 0 == 0⟩,
  -- RankingTheory: Belief ↔ RankedBelief translation
  ⟨"beliefToRanked promotes Belief to RankedBelief at given rank",
    beliefToRanked 2 (.belief "c" rkX) == .rankedBelief "c" 2 rkX⟩,
  ⟨"beliefToRanked recurses under modal operators",
    beliefToRanked 1 (.and (.belief "c" rkX) (.box (.belief "d" (.atom "Y"))))
      == .and (.rankedBelief "c" 1 rkX) (.box (.rankedBelief "d" 1 (.atom "Y")))⟩,
  ⟨"rankedToBelief: positive rank → Belief over the operand",
    rankedToBelief (.rankedBelief "c" 2 rkX) == some (.belief "c" rkX)⟩,
  ⟨"rankedToBelief: negative rank → Belief over the negated operand",
    rankedToBelief (.rankedBelief "c" (-2) rkX) == some (.belief "c" (.not rkX))⟩,
  ⟨"rankedToBelief: rank-0 has no binary equivalent",
    rankedToBelief (.rankedBelief "c" 0 rkX) == none⟩,
  -- RankingTheory: Tableau closure rules (Spohn Theorem 2(a))
  ⟨"single ranked-belief assertion is consistent",
    rkCheck [.rankedBelief "c" 2 rkX] == .definitely true⟩,
  ⟨"rank-0 (neutrality) alone is consistent",
    rkCheck [.rankedBelief "c" 0 rkX] == .definitely true⟩,
  ⟨"functionality: same agent + operand at different ranks closes",
    rkCheck [.rankedBelief "c" 2 rkX, .rankedBelief "c" 3 rkX] == .definitely false⟩,
  ⟨"negation symmetry: positive φ + positive ¬φ closes",
    rkCheck [.rankedBelief "c" 2 rkX, .rankedBelief "c" 1 (.not rkX)] == .definitely false⟩,
  ⟨"negation symmetry holds when m = -n: consistent",
    rkCheck [.rankedBelief "c" 2 rkX, .rankedBelief "c" (-2) (.not rkX)] == .definitely true⟩,
  ⟨"different agents are independent",
    rkCheck [.rankedBelief "radA" 2 rkX, .rankedBelief "radB" (-3) rkX] == .definitely true⟩,
  ⟨"cwyde mapping: DEFINITE + AMBIVALENT-of-other-finding is consistent",
    rkCheck [.rankedBelief "c" 2 (.atom "PE"), .rankedBelief "c" 0 (.atom "Pneumonia")]
      == .definitely true⟩,
  ⟨"cwyde mapping: DEFINITE_EXISTENCE + DEFINITE_NEGATED on same finding closes",
    rkCheck [.rankedBelief "c" 2 (.atom "PE"), .rankedBelief "c" (-2) (.atom "PE")]
      == .definitely false⟩,
  -- RankingTheory: cwyde 5-row assertion-category mapping
  ⟨"each cwyde category alone is consistent",
    ["DEFINITE_EXISTENCE", "PROBABLE_EXISTENCE", "AMBIVALENT_EXISTENCE",
     "PROBABLE_NEGATED_EXISTENCE", "DEFINITE_NEGATED_EXISTENCE"].all fun cat =>
      cwydeCheck [cat] == some (.definitely true)⟩,
  ⟨"DEFINITE + DEFINITE_NEGATED on same finding is inconsistent",
    cwydeCheck ["DEFINITE_EXISTENCE", "DEFINITE_NEGATED_EXISTENCE"] == some (.definitely false)⟩,
  ⟨"DEFINITE + PROBABLE_NEGATED on same finding is inconsistent",
    cwydeCheck ["DEFINITE_EXISTENCE", "PROBABLE_NEGATED_EXISTENCE"] == some (.definitely false)⟩,
  -- PaperCorrespondence: Spohn (1988), Definition 4 (p. 115)
  ⟨"reference model satisfies well-formedness (κ_c(w1) = 0)", wellFormed rkM0 == true⟩,
  ⟨"model with no κ = 0 world is ill-formed",
    wellFormed (mkKappaModel ["w1"] [("c", [("w1", 2)])] []) == false⟩,
  -- Theorem 2(b) (p. 115)
  ⟨"kappaProp({w1}) = 0 — w1 is the minimum-ranked world (w1 ∈ V(X))",
    okIs (kappaProp rkM0 "c" (.ofList ["w1"])) 0⟩,
  ⟨"kappaProp({w2}) = 3 — w2 is disbelieved with firmness 3 (w2 ∉ V(X))",
    okIs (kappaProp rkM0 "c" (.ofList ["w2"])) 3⟩,
  ⟨"kappaProp({w1,w2}) = 0 — min{0,3} = 0 (Theorem 2(b): κ(A∪B) = min{κ(A),κ(B)})",
    okIs (kappaProp rkM0 "c" (.ofList ["w1", "w2"])) 0⟩,
  ⟨"κ(A∪B) = min{κ(A),κ(B)}: computed values confirm Theorem 2(b)",
    okIs (do
      let kA ← kappaProp rkM0 "c" (.ofList ["w1"])
      let kB ← kappaProp rkM0 "c" (.ofList ["w2"])
      let kAB ← kappaProp rkM0 "c" (.ofList ["w1", "w2"])
      return kAB == min kA kB) true⟩,
  -- Definition 6 (p. 117)
  ⟨"τ(X) = 2 after conditionalize to α=2 (overwrites prior firmness 3)",
    okIs (do tau (← conditionalize rkM0 "c" rkX 2) "c" rkX) 2⟩,
  ⟨"τ(X) = 1 after second conditionalize to α=1 (overwrites previous α=2)",
    okIs (do
      let m1 ← conditionalize rkM0 "c" rkX 2
      tau (← conditionalize m1 "c" rkX 1) "c" rkX) 1⟩,
  -- Theorem 3 (p. 118)
  ⟨"τ(X) = 3 after round-trip α=2 then α=3 (original firmness restored)",
    okIs (do
      let m1 ← conditionalize rkM0 "c" rkX 2
      tau (← conditionalize m1 "c" rkX 3) "c" rkX) 3⟩,
  ⟨"κ_c(w1) = 0 after round-trip (minimum-ranked world unchanged)",
    okIs (do
      let m1 ← conditionalize rkM0 "c" rkX 2
      kappaWorld (← conditionalize m1 "c" rkX 3) "c" "w1") 0⟩,
  ⟨"κ_c(w2) = 3 after round-trip (original rank restored)",
    okIs (do
      let m1 ← conditionalize rkM0 "c" rkX 2
      kappaWorld (← conditionalize m1 "c" rkX 3) "c" "w2") 3⟩,
  -- Theorem 7 (p. 121)
  ⟨"combineIndependent 2 3 = 5  (κ(B∩C) = κ(B) + κ(C))", combineIndependent 2 3 == 5⟩,
  ⟨"combineIndependent 0 3 = 3  (rank-0 component leaves sum = other rank)",
    combineIndependent 0 3 == 3⟩,
  ⟨"combineIndependent 2 0 = 2  (symmetric: rank-0 on either side)",
    combineIndependent 2 0 == 2⟩,
  ⟨"combineIndependent 2 2 = 4  (equal ranks add)", combineIndependent 2 2 == 4⟩,
  -- RegressionIssue18 B4: ranking theory κ=∞ no longer leaks into arithmetic
  ⟨"τ of a normal proposition is finite", okIs (tau rkM2 "c" rkX) 2⟩,
  ⟨"τ of a model-tautology is +∞ (maxBound), not wrapped garbage",
    okIs (tau rkM2 "c" (.or rkX (.not rkX))) rankMaxBound⟩,
  ⟨"τ of a model-contradiction is −∞ (minBound), not wrapped garbage",
    okIs (tau rkM2 "c" (.and rkX (.not rkX))) rankMinBound⟩,
  ⟨"conditionalizing on a contradiction errors (would break wellFormed)",
    isErr (conditionalize rkM2 "c" (.and rkX (.not rkX)) 2)⟩,
  ⟨"conditionalizing on a satisfiable proposition preserves wellFormed",
    okIs (wellFormed <$> conditionalize rkM2 "c" rkX 3) true⟩,
  -- Not in gamen-hs: with the agent's κ-table empty, Haskell's lazy rank
  -- argument to `conditionalize` is never forced (`Map.mapWithKey` over an
  -- empty map), so τ is not evaluated and `applyEvidence` returns the model
  -- unchanged (checked in GHCi). The Lean must not compute τ, which errors.
  ⟨"applyEvidence with an empty κ-table returns the model unchanged",
    let m := mkKappaModel ["w1", "w2"] [("a", [])] [("p", ["w1"])]
    okIs (applyEvidence m "a" p 1) m⟩
]

/-! ## Plausibility (`Gamen.Plausibility`)

Port of `test/PlausibilitySpec.hs` in full (`carrierLaws` is a shared
helper `it`-ed 3 times in the Haskell, once per carrier; here it is
`carrierLawCases`, called once per carrier below, for 24 of the 57
examples `cabal test --test-options="--match Plausibility"` reports).
Every `Option` result is compared against `some v` (`someIs`) or by
`match … | none => false`, so a failed `conditionOn` fails the case
whichever answer was expected, matching `okIs`/`isErr` for `Except`. -/

/-- `o` succeeded with value `v`; `none` (an error) fails the case,
matching `okIs` for `Except`. -/
def someIs [BEq α] (o : Option α) (v : α) : Bool :=
  match o with
  | some a => a == v
  | none => false

/-- Test convenience: build a `ProbabilityPlausibility`/`PossibilityPlausibility`
directly from a literal already known to be in [0,1], bypassing the
`Except`-returning smart constructor (which `plausibilityConstructorCases`
tests on its own) — mirrors Haskell calling the (non-`Except`)
`mkProbability`/`mkPossibility` directly on a literal it knows is valid. -/
def prob (r : Rat) : ProbabilityPlausibility := ⟨r⟩
def poss (r : Rat) : PossibilityPlausibility := ⟨r⟩

/-- The carrier laws every `Plausibility` instance commits to (module
header of `Gamen.Plausibility`), checked over a finite sample. Ports the
`carrierLaws` helper from `test/PlausibilitySpec.hs`. -/
def carrierLawCases {p : Type} [BEq p] [Plausibility p] (carrier : String) (samples : List p) :
    List Case :=
  [ ⟨carrier ++ ": plBot ⊑ x ⊑ plTop for all sample values",
      samples.all (plLeq plBot) && samples.all (plLeq · plTop)⟩,
    ⟨carrier ++ ": plJoin is commutative",
      samples.all fun x => samples.all fun y => plJoin x y == plJoin y x⟩,
    ⟨carrier ++ ": plJoin is associative",
      samples.all fun x => samples.all fun y => samples.all fun z =>
        plJoin x (plJoin y z) == plJoin (plJoin x y) z⟩,
    ⟨carrier ++ ": plBot is the identity of plJoin",
      samples.all fun x => plJoin x plBot == x && plJoin plBot x == x⟩,
    ⟨carrier ++ ": plTop is the identity of plTimes",
      samples.all fun x => plTimes x plTop == x && plTimes plTop x == x⟩,
    ⟨carrier ++ ": plBot annihilates plTimes",
      samples.all fun x => plTimes x plBot == plBot && plTimes plBot x == plBot⟩,
    ⟨carrier ++ ": plCondition _ plBot is Nothing; defined otherwise",
      samples.all (fun x => plCondition x plBot == none)
        && samples.all fun x => samples.all fun b =>
             b == plBot || !(plLeq x b) || plCondition x b != none⟩,
    ⟨carrier ++ ": coherence: plTimes (plCondition x b) b == x when x ⊑ b, b ≠ plBot",
      samples.all fun x => samples.all fun b =>
        if b == plBot || !(plLeq x b) then true
        else match plCondition x b with
          | some c => plTimes c b == x
          | none => true⟩ ]

def plausibilityConstructorCases : List Case := [
  ⟨"Plausibility: smart constructors: mkRank rejects negative ranks", isErr (mkRank (-1))⟩,
  ⟨"Plausibility: smart constructors: mkProbability rejects values outside [0,1]",
    isErr (mkProbability (3/2)) && isErr (mkProbability (-1/2))⟩,
  ⟨"Plausibility: smart constructors: mkPossibility rejects values outside [0,1]",
    isErr (mkPossibility (3/2))⟩,
  ⟨"Plausibility: order: ranks: lower κ is MORE plausible (order reverses the numbers)",
    plLeq (RankedPlausibility.finiteRank 3) (.finiteRank 1) == true
      && plLeq (RankedPlausibility.finiteRank 1) (.finiteRank 3) == false
      && plLt RankedPlausibility.infiniteRank (.finiteRank 0) == true⟩,
  ⟨"Plausibility: order: probability and possibility: numeric order",
    plLeq (prob (1/4)) (prob (1/2)) == true && plLeq (poss (3/10)) (poss (1/2)) == true⟩
]

-- κ: w1 = 1, w2 = 0, w3 = 3 — the agent believes ¬{w1,w3}-ish content;
-- w2 is the κ = 0 core.
def rkPlM1 : PlausibilityMeasure RankedPlausibility :=
  mkMeasure [("w1", .finiteRank 1), ("w2", .finiteRank 0), ("w3", .finiteRank 3)]
def rkPlE : Std.TreeSet World := Std.TreeSet.ofList ["w1", "w3"]

def rankedConditioningCases : List Case := [
  ⟨"RankedPlausibility: plOf is the min rank over the event (OCF law)",
    plOf rkPlM1 rkPlE == .finiteRank 1
      && plOf rkPlM1 (plDomain rkPlM1) == .finiteRank 0
      && plOf rkPlM1 (∅ : Std.TreeSet World) == .infiniteRank⟩,
  ⟨"RankedPlausibility: conditionOn shifts the event to κ = 0 and kills the rest (Spohn Def. 5)",
    match conditionOn rkPlM1 rkPlE with
    | some m' => plPoint m' "w1" == .finiteRank 0
        && plPoint m' "w3" == .finiteRank 2
        && plPoint m' "w2" == .infiniteRank
        && isNormalized m'
    | none => false⟩,
  ⟨"RankedPlausibility: round-trip: conditioning a normalized measure on its domain is identity",
    someIs (conditionOn rkPlM1 (plDomain rkPlM1)) rkPlM1⟩,
  ⟨"RankedPlausibility: round-trip: joint = conditional ⊗ marginal (κ(A∩E) = κ(A|E) + κ(E))",
    match conditionOn rkPlM1 rkPlE with
    | some m' =>
      let a := Std.TreeSet.ofList ["w3"]
      plTimes (plOf m' a) (plOf rkPlM1 rkPlE) == plOf rkPlM1 (a.filter fun w => rkPlE.contains w)
    | none => false⟩,
  ⟨"RankedPlausibility: conditioning on an impossible event is Nothing",
    conditionOn rkPlM1 (∅ : Std.TreeSet World) == none
      && conditionOn rkPlM1 (Std.TreeSet.ofList ["nowhere"]) == none⟩,
  ⟨"RankedPlausibility: iterated conditioning = conditioning on the intersection",
    let e2 := Std.TreeSet.ofList ["w3"]
    match conditionOn rkPlM1 rkPlE with
    | none => false
    | some step1 =>
      conditionOn step1 e2 == conditionOn rkPlM1 (rkPlE.filter fun w => e2.contains w)⟩
]

-- An unfair 4-sided die: P(w1)=1/2, P(w2)=1/4, P(w3)=1/8, P(w4)=1/8.
def probPlM1 : PlausibilityMeasure ProbabilityPlausibility :=
  mkMeasure [("w1", prob (1/2)), ("w2", prob (1/4)), ("w3", prob (1/8)), ("w4", prob (1/8))]
def probPlE : Std.TreeSet World := Std.TreeSet.ofList ["w2", "w3", "w4"]

def probabilityConditioningCases : List Case := [
  ⟨"ProbabilityPlausibility: plOf is finite additivity",
    plOf probPlM1 probPlE == prob (1/2) && isNormalized probPlM1⟩,
  ⟨"ProbabilityPlausibility: conditionOn is Bayes conditioning (P(w|E) = P(w)/P(E))",
    match conditionOn probPlM1 probPlE with
    | some m' => plPoint m' "w2" == prob (1/2)
        && plPoint m' "w3" == prob (1/4)
        && plPoint m' "w1" == prob 0
        && isNormalized m'
    | none => false⟩,
  ⟨"ProbabilityPlausibility: round-trip: conditioning a normalized measure on its domain is identity",
    someIs (conditionOn probPlM1 (plDomain probPlM1)) probPlM1⟩,
  ⟨"ProbabilityPlausibility: round-trip: chain rule P(A∩E) = P(A|E) · P(E)",
    match conditionOn probPlM1 probPlE with
    | some m' =>
      let a := Std.TreeSet.ofList ["w1", "w2"]
      plTimes (plOf m' a) (plOf probPlM1 probPlE)
        == plOf probPlM1 (a.filter fun w => probPlE.contains w)
    | none => false⟩,
  ⟨"ProbabilityPlausibility: conditioning on a probability-0 event is Nothing",
    conditionOn probPlM1 (∅ : Std.TreeSet World) == none⟩,
  ⟨"ProbabilityPlausibility: iterated conditioning = conditioning on the intersection",
    let e2 := Std.TreeSet.ofList ["w3", "w4"]
    match conditionOn probPlM1 probPlE with
    | none => false
    | some step1 =>
      conditionOn step1 e2 == conditionOn probPlM1 (probPlE.filter fun w => e2.contains w)⟩
]

-- π: w1 = 1, w2 = 1/2, w3 = 3/10.
def possPlM1 : PlausibilityMeasure PossibilityPlausibility :=
  mkMeasure [("w1", poss 1), ("w2", poss (1/2)), ("w3", poss (3/10))]
def possPlE : Std.TreeSet World := Std.TreeSet.ofList ["w2", "w3"]

def possibilityConditioningCases : List Case := [
  ⟨"PossibilityPlausibility: plOf is maxitivity (Π(A∪B) = max)",
    plOf possPlM1 possPlE == poss (1/2) && plOf possPlM1 (plDomain possPlM1) == plTop⟩,
  ⟨"PossibilityPlausibility: conditionOn is min-based conditioning (Dubois-Prade)",
    match conditionOn possPlM1 possPlE with
    | some m' => plPoint m' "w2" == poss 1
        && plPoint m' "w3" == poss (3/10)
        && plPoint m' "w1" == poss 0
        && isNormalized m'
    | none => false⟩,
  ⟨"PossibilityPlausibility: round-trip: conditioning a normalized measure on its domain is identity",
    someIs (conditionOn possPlM1 (plDomain possPlM1)) possPlM1⟩,
  ⟨"PossibilityPlausibility: round-trip: Π(A∩E) = min(Π(A|E), Π(E))",
    match conditionOn possPlM1 possPlE with
    | some m' =>
      let a := Std.TreeSet.ofList ["w3"]
      plTimes (plOf m' a) (plOf possPlM1 possPlE)
        == plOf possPlM1 (a.filter fun w => possPlE.contains w)
    | none => false⟩,
  ⟨"PossibilityPlausibility: conditioning on a possibility-0 event is Nothing",
    conditionOn possPlM1 (∅ : Std.TreeSet World) == none⟩,
  ⟨"PossibilityPlausibility: iterated conditioning = conditioning on the intersection",
    let e2 := Std.TreeSet.ofList ["w3"]
    match conditionOn possPlM1 possPlE with
    | none => false
    | some step1 =>
      conditionOn step1 e2 == conditionOn possPlM1 (possPlE.filter fun w => e2.contains w)⟩
]

/-- `Pl(A | E)` computed two ways: (1) condition the whole measure, then
measure `A`; (2) `plCondition (Pl(A∩E)) (Pl(E))` directly. `false` if either
side's `Option` fails — not exercised by the ported cases below, all of
which are set up to succeed, matching the Haskell's `fromJust`-based
`agreesOn`. -/
def plAgrees {p : Type} [BEq p] [Plausibility p]
    (m : PlausibilityMeasure p) (a e : Std.TreeSet World) : Bool :=
  match conditionOn m e with
  | none => false
  | some m' =>
    match plCondition (plOf m (a.filter fun w => e.contains w)) (plOf m e) with
    | none => false
    | some c => plOf m' a == c

def plAgreementCases : List Case :=
  let rkM : PlausibilityMeasure RankedPlausibility :=
    mkMeasure [("w1", .finiteRank 1), ("w2", .finiteRank 0), ("w3", .finiteRank 3)]
  let probM : PlausibilityMeasure ProbabilityPlausibility :=
    mkMeasure [("w1", prob (1/2)), ("w2", prob (1/4)), ("w3", prob (1/4))]
  let possM : PlausibilityMeasure PossibilityPlausibility :=
    mkMeasure [("w1", poss 1), ("w2", poss (1/2)), ("w3", poss (3/10))]
  [ ⟨"conditionOn agrees with event-level plCondition: for ranks",
      plAgrees rkM (Std.TreeSet.ofList ["w1"]) (Std.TreeSet.ofList ["w1", "w3"])
        && plAgrees rkM (Std.TreeSet.ofList ["w1", "w2"]) (Std.TreeSet.ofList ["w1", "w3"])⟩,
    ⟨"conditionOn agrees with event-level plCondition: for probability",
      plAgrees probM (Std.TreeSet.ofList ["w2"]) (Std.TreeSet.ofList ["w2", "w3"])
        && plAgrees probM (Std.TreeSet.ofList ["w1", "w2"]) (Std.TreeSet.ofList ["w2", "w3"])⟩,
    ⟨"conditionOn agrees with event-level plCondition: for possibility (including the boundary case Π(A∩E) = Π(E))",
      plAgrees possM (Std.TreeSet.ofList ["w2"]) (Std.TreeSet.ofList ["w2", "w3"])
        && plAgrees possM (Std.TreeSet.ofList ["w3"]) (Std.TreeSet.ofList ["w2", "w3"])⟩ ]

def mostPlausibleCases : List Case :=
  let m1 : PlausibilityMeasure RankedPlausibility :=
    mkMeasure [("w1", .finiteRank 1), ("w2", .finiteRank 0), ("w3", .finiteRank 0)]
  let m2 : PlausibilityMeasure ProbabilityPlausibility :=
    mkMeasure [("w1", prob (1/2)), ("w2", prob (1/4)), ("w3", prob (1/4))]
  let m3 : PlausibilityMeasure RankedPlausibility :=
    mkMeasure [("w1", .finiteRank 0), ("w2", .finiteRank 1), ("w3", .finiteRank 2)]
  let e3 : Std.TreeSet World := Std.TreeSet.ofList ["w2", "w3"]
  [ ⟨"mostPlausible: ranks: the κ = 0 core",
      mostPlausible m1 == Std.TreeSet.ofList ["w2", "w3"]⟩,
    ⟨"mostPlausible: probability: the highest-mass worlds",
      mostPlausible m2 == Std.TreeSet.ofList ["w1"]⟩,
    ⟨"mostPlausible: after conditioning, the core lies inside the evidence",
      match conditionOn m3 e3 with
      | some m' => mostPlausible m' == Std.TreeSet.ofList ["w2"] && subsetOf (mostPlausible m') e3
      | none => false⟩ ]

-- Agent c: κ(w1) = 0, κ(w2) = 1, κ(w3) = 2; X true at w2, w3.
def plKm : KappaModel :=
  mkKappaModel ["w1", "w2", "w3"] [("c", [("w1", 0), ("w2", 1), ("w3", 2)])] [("X", ["w2", "w3"])]
def plPhi : Formula := .atom "X"

def agentMeasureCases : List Case := [
  ⟨"agentMeasure: projects the κ-table as point plausibilities",
    okIs ((agentMeasure plKm "c").map fun m =>
      plPoint m "w1" == .finiteRank 0 && plPoint m "w3" == .finiteRank 2 && isNormalized m) true⟩,
  ⟨"agentMeasure: errors on an unknown agent", isErr (agentMeasure plKm "nobody")⟩,
  ⟨"agentMeasure: conditionOn on ⟦φ⟧ agrees with Spohn conditionalize on the φ-side",
    okIs (do
      let ePhi ← truthSet plKm plPhi
      let am ← agentMeasure plKm "c"
      let km' ← conditionalize plKm "c" plPhi 5
      match conditionOn am ePhi with
      | none => throw "conditionOn failed"
      | some m' =>
        ePhi.toList.allM fun w => do
          let kv ← kappaWorld km' "c" w
          pure (plPoint m' w == RankedPlausibility.finiteRank kv)) true⟩,
  ⟨"agentMeasure: the conditioned core is the most plausible φ-worlds",
    okIs (do
      let ePhi ← truthSet plKm plPhi
      let am ← agentMeasure plKm "c"
      match conditionOn am ePhi with
      | none => throw "conditionOn failed"
      | some m' => pure (mostPlausible m' == Std.TreeSet.ofList ["w2"])) true⟩
]

def plausibilityCases : List Case :=
  carrierLawCases "RankedPlausibility"
    ([RankedPlausibility.finiteRank 0, .finiteRank 1, .finiteRank 2, .finiteRank 3, .finiteRank 4,
      .infiniteRank])
  ++ carrierLawCases "ProbabilityPlausibility" [prob 0, prob (1/4), prob (1/3), prob (1/2), prob 1]
  ++ carrierLawCases "PossibilityPlausibility" [poss 0, poss (3/10), poss (1/2), poss (7/10), poss 1]
  ++ plausibilityConstructorCases
  ++ rankedConditioningCases
  ++ probabilityConditioningCases
  ++ possibilityConditioningCases
  ++ plAgreementCases
  ++ mostPlausibleCases
  ++ agentMeasureCases

/-! ## Deontic-STIT sequents (`Gamen.DeonticStit.Sequent`)

Port of the "Sequent (Gamen.DeonticStit.Sequent)" `describe` block of
`test/DeonticStitSpec.hs` in full (9 `it`s, in file order). The rest of
`DeonticStitSpec.hs` (beyond the `.Rules` blocks in `rulesCases`, the
`.Saturation` blocks in `saturationCases`, the `.Prove` and clinical
blocks in `proveCases`, and the base-module blocks in `deonticStitCases`
below) exercises `.CounterModel`, in `counterModelCases`. -/

def dsW0 : Label := label0
def dsW1 : Label := nextLabel dsW0
def dsW2 : Label := nextLabel dsW1

def sequentCases : List Case := [
  ⟨"Label shows as wN",
    toString dsW0 == "w0" && toString dsW2 == "w2"⟩,
  ⟨"mkLabFormula normalises to NNF",
    (mkLabFormula dsW0 (.implies p q)).lfFormula == .or (.not p) q
      && (mkLabFormula dsW0 (.not (.box p))).lfFormula == .diamond (.not p)⟩,
  ⟨"singletonSequent seeds proof search at w₀",
    let s := singletonSequent dsW0 (.implies p q)
    s.gamma.size == 1 && s.rels.isEmpty
      && hasFormula (mkLabFormula dsW0 (.implies p q)) s⟩,
  ⟨"addRel and addFormula are idempotent (set-based)",
    let r := RelAtom.choice "i" dsW0 dsW1
    let lf := mkLabFormula dsW0 p
    let s0 := emptySequent
    let s1 := addRel r (addRel r s0)
    let s2 := addFormula lf (addFormula lf s0)
    s1.rels.size == 1 && s2.gamma.size == 1⟩,
  ⟨"labels collects every label appearing on either side",
    let s := addRel (RelAtom.choice "i" dsW0 dsW1)
      (addRel (RelAtom.ideal "i" dsW2) (singletonSequent dsW0 p))
    labels s == Std.TreeSet.ofList [dsW0, dsW1, dsW2]⟩,
  ⟨"freshLabel returns a label not in the sequent",
    let s := addRel (RelAtom.choice "i" dsW0 dsW1)
      (addRel (RelAtom.ideal "i" dsW2) (singletonSequent dsW0 p))
    let fresh := freshLabel s
    !(labels s).contains fresh⟩,
  ⟨"freshLabel on the empty sequent is w0",
    freshLabel emptySequent == dsW0⟩,
  ⟨"substLabel rewrites labels everywhere they appear",
    let s := addRel (RelAtom.choice "i" dsW1 dsW2)
      (addFormula (mkLabFormula dsW1 p) (singletonSequent dsW0 q))
    let renamed := substLabel dsW1 dsW0 s
    hasRel (RelAtom.choice "i" dsW0 dsW2) renamed
      && !hasRel (RelAtom.choice "i" dsW1 dsW2) renamed
      && hasFormula (mkLabFormula dsW0 p) renamed
      && !hasFormula (mkLabFormula dsW1 p) renamed⟩,
  ⟨"RelAtom Show matches the paper's notation shape",
    toString (RelAtom.choice "i" dsW0 dsW1) == "R_[i]w0w1"
      && toString (RelAtom.ideal "i" dsW2) == "I_⊗_i w2"⟩
]

/-! ## Deontic-STIT rules (`Gamen.DeonticStit.Rules`)

Port of the two `describe` blocks "DeonticStit.Rules: closure and
non-generating logical rules" and "DeonticStit.Rules: generating and frame
rules" of `test/DeonticStitSpec.hs` (31 `it`s, in file order). A Haskell
`case … of Just RuleApp{…} -> …; _ -> expectationFailure` becomes a `match`
whose fallback arm is `false`; `shouldBe Nothing` becomes `.isNone`. No
`PaperCorrespondence.hs` section calls this module directly. -/

def rulesCases : List Case :=
  let np : Formula := .not p
  [
  -- isClosedSequent (id rule)
  ⟨"isClosedSequent: closes when w:p and w:¬p both appear",
    isClosedSequent (addFormula (mkLabFormula dsW0 p) (singletonSequent dsW0 np)) == true⟩,
  ⟨"isClosedSequent: does not close on different labels",
    isClosedSequent (addFormula (mkLabFormula dsW1 np) (singletonSequent dsW0 p)) == false⟩,
  ⟨"isClosedSequent: does not close on different atoms",
    isClosedSequent (addFormula (mkLabFormula dsW0 (.not q)) (singletonSequent dsW0 p)) == false⟩,
  ⟨"isClosedSequent: does not close the empty sequent",
    isClosedSequent emptySequent == false⟩,
  -- applyAnd (∧ rule)
  ⟨"applyAnd: branches w:(p∧q) into [w:p,…] and [w:q,…] premises",
    match applyAnd (singletonSequent dsW0 (.and p q)) with
    | some ⟨[ls, rs], fs, _, _⟩ =>
      fs == [] && hasFormula (mkLabFormula dsW0 p) ls && hasFormula (mkLabFormula dsW0 q) rs
        && hasFormula (mkLabFormula dsW0 (.and p q)) ls
        && hasFormula (mkLabFormula dsW0 (.and p q)) rs
    | _ => false⟩,
  ⟨"applyAnd: is Nothing when the sequent has no conjunctions",
    (applyAnd (singletonSequent dsW0 p)).isNone⟩,
  ⟨"applyAnd: is Nothing when both conjuncts are already on Γ",
    (applyAnd (addFormula (mkLabFormula dsW0 p)
      (addFormula (mkLabFormula dsW0 q) (singletonSequent dsW0 (.and p q))))).isNone⟩,
  -- applyOr (∨ rule)
  ⟨"applyOr: produces one premise with both disjuncts added",
    match applyOr (singletonSequent dsW0 (.or p q)) with
    | some ⟨[s'], [], _, _⟩ =>
      hasFormula (mkLabFormula dsW0 p) s' && hasFormula (mkLabFormula dsW0 q) s'
    | _ => false⟩,
  ⟨"applyOr: is Nothing when both disjuncts already present",
    (applyOr (addFormula (mkLabFormula dsW0 p)
      (addFormula (mkLabFormula dsW0 q) (singletonSequent dsW0 (.or p q))))).isNone⟩,
  -- applyDiamond (◇ rule)
  ⟨"applyDiamond: adds u:φ for an existing label u when w:◇φ ∈ Γ",
    match applyDiamond (singletonSequent dsW0 (.diamond p)) with
    | some ⟨[s'], [], _, _⟩ =>
      hasFormula (mkLabFormula dsW0 p) s' && hasFormula (mkLabFormula dsW0 (.diamond p)) s'
    | _ => false⟩,
  ⟨"applyDiamond: is Nothing when φ already at every label",
    (applyDiamond (addFormula (mkLabFormula dsW0 p) (singletonSequent dsW0 (.diamond p)))).isNone⟩,
  -- applyChoiceDiamond (⟨i⟩ rule)
  ⟨"applyChoiceDiamond: adds u:φ and u:⟨i⟩φ when R_[i]wu ∈ ℛ and w:⟨i⟩φ ∈ Γ",
    match applyChoiceDiamond (addRel (.choice "i" dsW0 dsW1)
        (singletonSequent dsW0 (.choiceDiamond "i" p))) with
    | some ⟨[s'], [], _, _⟩ =>
      hasFormula (mkLabFormula dsW1 p) s'
        && hasFormula (mkLabFormula dsW1 (.choiceDiamond "i" p)) s'
    | _ => false⟩,
  ⟨"applyChoiceDiamond: is Nothing without a matching R_[i] relation",
    (applyChoiceDiamond (singletonSequent dsW0 (.choiceDiamond "i" p))).isNone⟩,
  -- applyPermitted (⊖_i rule)
  ⟨"applyPermitted: adds u:φ when I_⊗_i u ∈ ℛ and w:⊖_i φ ∈ Γ",
    match applyPermitted (addRel (.ideal "i" dsW1) (singletonSequent dsW0 (.permitted "i" p))) with
    | some ⟨[s'], [], _, _⟩ => hasFormula (mkLabFormula dsW1 p) s'
    | _ => false⟩,
  ⟨"applyPermitted: is Nothing without an Ideal relation",
    (applyPermitted (singletonSequent dsW0 (.permitted "i" p))).isNone⟩,
  -- applyBox (□ rule)
  ⟨"applyBox: introduces a fresh label witnessing the body",
    match applyBox (singletonSequent dsW0 (.box p)) with
    | some ⟨[s'], [v], _, _⟩ =>
      hasFormula (mkLabFormula v p) s' && hasFormula (mkLabFormula dsW0 (.box p)) s'
    | _ => false⟩,
  ⟨"applyBox: is Nothing when some label already has the body",
    (applyBox (addFormula (mkLabFormula dsW0 p) (singletonSequent dsW0 (.box p)))).isNone⟩,
  -- applyStit ([i] rule)
  ⟨"applyStit: adds R_[i]w_v and v:φ for fresh v",
    match applyStit (singletonSequent dsW0 (.stit "i" p)) with
    | some ⟨[s'], [v], _, _⟩ =>
      hasRel (.choice "i" dsW0 v) s' && hasFormula (mkLabFormula v p) s'
    | _ => false⟩,
  ⟨"applyStit: is Nothing when some R_[i]wu has u:φ",
    (applyStit (addFormula (mkLabFormula dsW0 p)
      (addRel (.choice "i" dsW0 dsW0) (singletonSequent dsW0 (.stit "i" p))))).isNone⟩,
  -- applyOught (⊗_i rule)
  ⟨"applyOught: adds I_⊗_i v and v:φ for fresh v",
    match applyOught (singletonSequent dsW0 (.ought "i" p)) with
    | some ⟨[s'], [v], _, _⟩ =>
      hasRel (.ideal "i" v) s' && hasFormula (mkLabFormula v p) s'
    | _ => false⟩,
  ⟨"applyOught: is Nothing when some I_⊗_i u has u:φ",
    (applyOught (addFormula (mkLabFormula dsW0 p)
      (addRel (.ideal "i" dsW0) (singletonSequent dsW0 (.ought "i" p))))).isNone⟩,
  -- applyRef (Ref_i rule)
  ⟨"applyRef: adds R_[i]ww when missing",
    match applyRef (singletonSequent dsW0 (.stit "i" p)) with
    | some ⟨[s'], [], _, _⟩ => hasRel (.choice "i" dsW0 dsW0) s'
    | _ => false⟩,
  ⟨"applyRef: is Nothing when every (i, w) is already reflexive",
    (applyRef (addRel (.choice "i" dsW0 dsW0) (singletonSequent dsW0 (.stit "i" p)))).isNone⟩,
  -- applyEuc (Euc_i rule)
  ⟨"applyEuc: with R_[i]wu and R_[i]wv adds R_[i]uv",
    match applyEuc (addRel (.choice "i" dsW0 dsW1)
        (addRel (.choice "i" dsW0 dsW2) (singletonSequent dsW0 (.stit "i" p)))) with
    | some ⟨[s'], [], _, _⟩ =>
      hasRel (.choice "i" dsW1 dsW2) s' || hasRel (.choice "i" dsW2 dsW1) s'
        || hasRel (.choice "i" dsW1 dsW1) s' || hasRel (.choice "i" dsW2 dsW2) s'
    | _ => false⟩,
  -- applyD3 (D3_i rule)
  ⟨"applyD3: with I_⊗_i w and R_[i]wu adds I_⊗_i u",
    match applyD3 (addRel (.ideal "i" dsW0)
        (addRel (.choice "i" dsW0 dsW1) (singletonSequent dsW0 (.permitted "i" p)))) with
    | some ⟨[s'], [], _, _⟩ => hasRel (.ideal "i" dsW1) s'
    | _ => false⟩,
  ⟨"applyD3: is Nothing when ideal set is already closed under R_[i]",
    (applyD3 (addRel (.ideal "i" dsW0) (addRel (.ideal "i" dsW1)
      (addRel (.choice "i" dsW0 dsW1) (singletonSequent dsW0 (.permitted "i" p)))))).isNone⟩,
  -- applyD2 (D2_i rule)
  ⟨"applyD2: introduces a fresh I_⊗_i v when no ideal exists for agent i",
    match applyD2 dsW0 (singletonSequent dsW0 (.ought "i" p)) with
    | some ⟨[s'], [v], [pa], _⟩ => hasRel (.ideal "i" v) s' && pa == dsW0
    | _ => false⟩,
  ⟨"applyD2: is Nothing when every agent already has an ideal world",
    (applyD2 dsW0 (addRel (.ideal "i" dsW0) (singletonSequent dsW0 (.ought "i" p)))).isNone⟩,
  -- applyAPC (APC^k_i, limited choice)
  ⟨"applyAPC: k=0 disables the rule",
    (applyAPC 0 (addRel (.choice "i" dsW0 dsW0) (singletonSequent dsW0 (.stit "i" p)))).isNone⟩,
  ⟨"applyAPC: k=1 with 2 labels and no R_[i] yields 1 premise",
    match applyAPC 1 (addFormula (mkLabFormula dsW1 p) (singletonSequent dsW0 (.stit "i" p))) with
    | some ⟨[s'], [], _, _⟩ => hasRel (.choice "i" dsW0 dsW1) s'
    | _ => false⟩,
  ⟨"applyAPC: k=2 with 3 labels and no R_[i] yields 3 premises",
    match applyAPC 2 (addFormula (mkLabFormula dsW1 p)
        (addFormula (mkLabFormula dsW2 p) (singletonSequent dsW0 (.stit "i" p)))) with
    | some ⟨ps, [], _, _⟩ => ps.length == 3
    | _ => false⟩
  ]

/-! ## Deontic-STIT saturation (`Gamen.DeonticStit.Saturation`)

Port of the four "DeonticStit.Saturation: …" `describe` blocks of
`test/DeonticStitSpec.hs` (GenTree, blocking, saturation predicates,
isStable) in full (26 `it`s, in file order). Predicates that consult the
generation tree return `Except` in Lean (see the module docstring), so those
are compared with `okIs`: an error fails the case whichever answer was
expected. -/

def saturationCases : List Case :=
  let np : Formula := .not p
  let gt0 := emptyGenTree dsW0
  [
  -- GenTree
  ⟨"emptyGenTree has just the root",
    gt0.gtRoot == dsW0 && okIs (ancestors dsW0 gt0) []⟩,
  ⟨"addGenChild records the parent edge",
    let gt := addGenChild dsW1 dsW2 (addGenChild dsW0 dsW1 gt0)
    okIs (ancestors dsW2 gt) [dsW1, dsW0] && okIs (ancestors dsW1 gt) [dsW0]⟩,
  ⟨"addGenIoaLabel marks but does not parent",
    let gt := addGenIoaLabel dsW1 gt0
    isIoaLabel dsW1 gt == true && okIs (ancestors dsW1 gt) []⟩,
  -- blocking
  ⟨"directly blocks a child whose Γ↾u and ideals match the parent",
    -- Same formula content {p} at both labels, same (empty) ideals, but
    -- Definition 16 (i) excludes the root as blocker: w1 is NOT blocked.
    let gt := addGenChild dsW0 dsW1 gt0
    let s := addFormula (mkLabFormula dsW0 p) (addFormula (mkLabFormula dsW1 p) emptySequent)
    isDirectlyBlockedBy dsW1 dsW0 gt s == false && okIs (isBlocked dsW1 gt s) false⟩,
  ⟨"directly blocks when the ancestor is not the root",
    let gt := addGenChild dsW1 dsW2 (addGenChild dsW0 dsW1 gt0)
    let s := addFormula (mkLabFormula dsW1 p) (addFormula (mkLabFormula dsW2 p) emptySequent)
    isDirectlyBlockedBy dsW2 dsW1 gt s == true && okIs (isBlocked dsW2 gt s) true⟩,
  ⟨"differing formula content prevents blocking",
    let gt := addGenChild dsW1 dsW2 (addGenChild dsW0 dsW1 gt0)
    let s := addFormula (mkLabFormula dsW1 p) (addFormula (mkLabFormula dsW2 np) emptySequent)
    isDirectlyBlockedBy dsW2 dsW1 gt s == false⟩,
  ⟨"IOA labels are never blocked",
    okIs (isBlocked dsW1 (addGenIoaLabel dsW1 gt0) emptySequent) false⟩,
  -- saturation predicates
  ⟨"satId fails on a closed sequent",
    satId (addFormula (mkLabFormula dsW0 p) (singletonSequent dsW0 np)) == false⟩,
  ⟨"satOr fails when a disjunct is missing",
    satOr (singletonSequent dsW0 (.or p q)) == false⟩,
  ⟨"satOr holds when both disjuncts are present",
    satOr (addFormula (mkLabFormula dsW0 p)
      (addFormula (mkLabFormula dsW0 q) (singletonSequent dsW0 (.or p q)))) == true⟩,
  ⟨"satAnd fails when both conjuncts are missing",
    satAnd (singletonSequent dsW0 (.and p q)) == false⟩,
  ⟨"satAnd holds with one conjunct present (saturation, not the rule)",
    satAnd (addFormula (mkLabFormula dsW0 p) (singletonSequent dsW0 (.and p q))) == true⟩,
  ⟨"satDiamond requires some witness label",
    satDiamond (singletonSequent dsW0 (.diamond p)) == false
      && satDiamond (addFormula (mkLabFormula dsW0 p) (singletonSequent dsW0 (.diamond p))) == true⟩,
  ⟨"satBox requires an unblocked witness",
    okIs (satBox gt0 (singletonSequent dsW0 (.box p))) false
      && okIs (satBox gt0 (addFormula (mkLabFormula dsW0 p) (singletonSequent dsW0 (.box p)))) true⟩,
  ⟨"satChoiceDiamond demands u:φ AND u:⟨i⟩φ when R_[i]wu present",
    let s0 := addRel (.choice "i" dsW0 dsW1) (singletonSequent dsW0 (.choiceDiamond "i" p))
    let s1 := addFormula (mkLabFormula dsW1 p)
      (addFormula (mkLabFormula dsW1 (.choiceDiamond "i" p)) s0)
    satChoiceDiamond s0 == false && satChoiceDiamond s1 == true⟩,
  ⟨"satStit demands an R_[i]wu and u:φ for unblocked w",
    okIs (satStit gt0 (singletonSequent dsW0 (.stit "i" p))) false⟩,
  ⟨"satRef demands R_[i]ww at every (i, w)",
    satRef (singletonSequent dsW0 (.stit "i" p)) == false
      && satRef (addRel (.choice "i" dsW0 dsW0) (singletonSequent dsW0 (.stit "i" p))) == true⟩,
  ⟨"satEuc fails without Euclidean closure of R_[i]wu, R_[i]wv → R_[i]uv",
    -- R_[i]w0w0 and R_[i]w0w1 both present; Euclidean demands
    -- R_[i]w0w1 (already there), R_[i]w1w0, and R_[i]w1w1.
    let s := addRel (.choice "i" dsW0 dsW0)
      (addRel (.choice "i" dsW0 dsW1) (singletonSequent dsW0 (.stit "i" p)))
    let sClosed := addRel (.choice "i" dsW1 dsW0) (addRel (.choice "i" dsW1 dsW1) s)
    satEuc s == false && satEuc sClosed == true⟩,
  ⟨"satPermitted demands u:φ at every Ideal-witness",
    satPermitted (addRel (.ideal "i" dsW1) (singletonSequent dsW0 (.permitted "i" p))) == false⟩,
  ⟨"satOught requires unblocked I_⊗_i u with u:φ",
    okIs (satOught gt0 (singletonSequent dsW0 (.ought "i" p))) false
      && okIs (satOught gt0 (addRel (.ideal "i" dsW0)
          (addFormula (mkLabFormula dsW0 p) (singletonSequent dsW0 (.ought "i" p))))) true⟩,
  ⟨"satD2 demands every agent to have an unblocked ideal",
    okIs (satD2 gt0 (singletonSequent dsW0 (.ought "i" p))) false
      && okIs (satD2 gt0 (addRel (.ideal "i" dsW0) (singletonSequent dsW0 (.ought "i" p)))) true⟩,
  ⟨"satD3 demands ideal-set closure under R_[i]",
    let s0 := addRel (.ideal "i" dsW0)
      (addRel (.choice "i" dsW0 dsW1) (singletonSequent dsW0 (.permitted "i" p)))
    satD3 s0 == false && satD3 (addRel (.ideal "i" dsW1) s0) == true⟩,
  ⟨"satAPC k=0 always holds",
    satAPC 0 (singletonSequent dsW0 (.stit "i" p)) == true⟩,
  ⟨"satAPC k=1 fails when 2 labels exist with no R_[i] pair",
    satAPC 1 (addFormula (mkLabFormula dsW1 p) (singletonSequent dsW0 (.stit "i" p))) == false⟩,
  -- isStable
  ⟨"isStable: is False on any non-trivial sequent missing R_[i]ww",
    -- (Stit "i" p) at w0 needs Ref (R_[i]w0w0) plus a witness u with
    -- R_[i]w0u and u:p — none of which we have.
    okIs (isStable 0 gt0 (singletonSequent dsW0 (.stit "i" (.atom "p")))) false⟩,
  ⟨"isStable: is True on the empty sequent",
    okIs (isStable 0 gt0 emptySequent) true⟩
  ]

/-! ## Deontic-STIT proof search (`Gamen.DeonticStit.Prove`)

Ports, in file order:

* `test/DeonticStitSpec.hs`, "DeonticStit.Prove: proveFormula" (all 14
  `it`s), "Clinical scenario: AHA + KDIGO + USDA potassium (issue #8
  step I)" (all 3 `it`s), and "Issue #41: refutations need a certified
  countermodel (IoaOp not scheduled)" (all 5 `it`s; gamen-hs 483c463). The spec's `TestShims` map `Unknown` to `False`;
  here every verdict is compared against `.ok (.definitely b)`, so an error
  or an `unknown` fails the case whichever answer was expected.
* `test/PaperCorrespondence.hs`, "Lyon & van Berkel (2024) — G3DS^k_n
  prover": the "Definition 3", "Example 5", and "Algorithm 1 + Figure 5"
  blocks (4 `it`s). Its "Definition 20" block (3 `it`s) is in
  `counterModelCases`. Citations fixed against
  the PDF: Definition 3 is pp. 844–845 (the Haskell says 843–844);
  Algorithm 1's listing is pp. 858–860 (the Haskell says 859–860); the §4.1
  counterexample is stated on p. 864 (the spec says p. 865, Figure 5's page).
* `test/RegressionIssue18.hs`, "A1: budget exhaustion is Unknown, never a
  definite answer" (3 `it`s), "A3: ⊥ / ⊤ handled by both provers" (6), and
  "consistency: inconsistent deontic sets still close" (1), in full,
  including their tableau `it`s. -/

/-- Strict equality on `Except` results, so a case can compare against
`.ok v`: an `.error` never equals an `.ok`, whichever answer was expected. -/
local instance [BEq ε] [BEq α] : BEq (Except ε α) where
  beq
    | .ok a, .ok b => a == b
    | .error x, .error y => x == y
    | _, _ => false

/-- The spec's `isUncertified`: the verdict is `unknown` because the G3DS
refutation could not be certified by a re-checked countermodel
(gamen-hs#41). An error or any other verdict is `false`. -/
def isUncertified : Except String Verdict → Bool
  | .ok (.unknown (.uncertifiedRefutation _)) => true
  | _ => false

/-- `proveFormula` ended in `refuted`, compared on the result shape. -/
def isRefuted : Except String ProveResult → Bool
  | .ok (.refuted _ _) => true
  | _ => false

/-- The spec's `stripAgents`: the old agent-stripping reduction to KD,
used only to reconstruct the pre-issue-#8 verdict. -/
def stripAgents : Formula → Formula
  | .ought _ f => .box (stripAgents f)
  | .permitted _ f => .diamond (stripAgents f)
  | .stit _ f => .box (stripAgents f)
  | .choiceDiamond _ f => .diamond (stripAgents f)
  | .groupStit f => .box (stripAgents f)
  | .not f => .not (stripAgents f)
  | .and l r => .and (stripAgents l) (stripAgents r)
  | .or l r => .or (stripAgents l) (stripAgents r)
  | .implies l r => .implies (stripAgents l) (stripAgents r)
  | .iff l r => .iff (stripAgents l) (stripAgents r)
  | .box f => .box (stripAgents f)
  | .diamond f => .diamond (stripAgents f)
  | .futureBox f => .futureBox (stripAgents f)
  | .futureDiamond f => .futureDiamond (stripAgents f)
  | .pastBox f => .pastBox (stripAgents f)
  | .pastDiamond f => .pastDiamond (stripAgents f)
  | .belief a f => .belief a (stripAgents f)
  | f => f

def proveCases : List Case :=
  let dsProves (f : Formula) (b : Bool) : Bool :=
    isFormulaValid 0 1000 f == .ok (.definitely b)
  let dsSat (f : Formula) (b : Bool) : Bool :=
    isFormulaSatisfiable 0 1000 f == .ok (.definitely b)
  let hhDiet : Formula := .atom "hh_diet"
  let highK : Formula := .atom "high_K"
  let kdConsistent (fs : List Formula) (b : Bool) : Bool :=
    tableauConsistent systemKD 1000 (fs.map stripAgents) == .definitely b
  let oic : Formula :=
    .implies (.ought "i" p) (.or (.diamond (.stit "i" p)) (.permitted "i" (.not p)))
  let x41 : Formula := .atom "x"
  let y41 : Formula := .atom "y"
  let neitherBoth : Formula := .box (.not (.and x41 y41))
  [
  -- DeonticStitSpec: "DeonticStit.Prove: proveFormula"
  ⟨"proves the propositional tautology p ∨ ¬p", dsProves (.or p (.not p)) true⟩,
  ⟨"proves p → p", dsProves (.implies p p) true⟩,
  ⟨"refutes the propositional non-tautology p ∧ ¬p", dsProves (.and p (.not p)) false⟩,
  ⟨"p ∧ ¬p is unsatisfiable", dsSat (.and p (.not p)) false⟩,
  ⟨"p ∧ q is satisfiable", dsSat (.and p q) true⟩,
  ⟨"isFormulaSetConsistent rejects {p, ¬p}",
    isFormulaSetConsistent 0 1000 [p, .not p] == .ok (.definitely false)⟩,
  ⟨"isFormulaSetConsistent accepts {p, q}",
    isFormulaSetConsistent 0 1000 [p, q] == .ok (.definitely true)⟩,
  ⟨"proves Box (p ∨ ¬p)", dsProves (.box (.or p (.not p))) true⟩,
  ⟨"proves Box p → Box p", dsProves (.implies (.box p) (.box p)) true⟩,
  ⟨"proves ◇p ∨ □¬p", dsProves (.or (.diamond p) (.box (.not p))) true⟩,
  ⟨"proves □(p ∧ q) → □p", dsProves (.implies (.box (.and p q)) (.box p)) true⟩,
  ⟨"proves the K axiom □(p → q) → (□p → □q)",
    dsProves (.implies (.box (.implies p q)) (.implies (.box p) (.box q))) true⟩,
  ⟨"proves Lyon-Berkel Example 5: ⊗_i p → ◇[i]p ∨ ⊖_i ¬p", dsProves oic true⟩,
  ⟨"terminates on the §4.1 counterexample ◇[1]p ∨ ◇[2]q",
    isRefuted (proveFormula 0 5000 (.or (.choiceDiamond "1" p) (.choiceDiamond "2" q)))⟩,
  -- DeonticStitSpec: "Clinical scenario: AHA + KDIGO + USDA potassium"
  ⟨"cross-agent same-atom: ⊗_p X ∧ ⊗_c ¬X is inconsistent in DS too; prover says Unknown (#41)",
    -- C2 (independence of agents) makes this inconsistent; the prover
    -- cannot reach that without IoaOp, and its C2-violating refutation is
    -- now reported as uncertified.
    let phis := [Formula.ought "patient" hhDiet, .ought "clinician" (.not hhDiet)]
    isUncertified (isFormulaSetConsistent 0 5000 phis) && kdConsistent phis false⟩,
  ⟨"intra-agent action conflict via USDA bridge — both reject",
    let phis := [Formula.ought "patient" hhDiet, .ought "patient" (.not highK),
                 .box (.implies hhDiet highK)]
    isFormulaSetConsistent 0 5000 phis == .ok (.definitely false) && kdConsistent phis false⟩,
  ⟨"advice-level + KDIGO + bridge — consistent (no adherence axiom); DS prover can't certify it (#41)",
    let phis := [Formula.ought "clinician" (.stit "clinician" (.atom "advise_hh_diet")),
                 .ought "patient" (.not highK), .box (.implies hhDiet highK)]
    -- A one-world DS model certifies consistency without the prover.
    let witness := mkDSModel
      (mkDSFrame ["w"] [("clinician", [("w", "w")]), ("patient", [("w", "w")])]
                       [("clinician", ["w"]), ("patient", ["w"])])
      [("advise_hh_diet", ["w"]), ("hh_diet", []), ("high_K", [])]
    isValidDSFrame witness.dsFrame
      && phis.all (fun φ => dsSatisfies witness "w" φ == .ok true)
      && kdConsistent phis true
      && isUncertified (isFormulaSetConsistent 0 5000 phis)⟩,
  -- DeonticStitSpec: "Issue #41: refutations need a certified countermodel
  -- (IoaOp not scheduled)"
  ⟨"#41: the IOA axiom is not reported invalid",
    isUncertified (isFormulaValid 0 2000
      (.implies (.and (.diamond (.stit "1" x41)) (.diamond (.stit "2" y41)))
                (.diamond (.and (.stit "1" x41) (.stit "2" y41)))))⟩,
  ⟨"#41: two agents' obligations that cannot both hold are not reported consistent",
    isUncertified (isFormulaSetConsistent 0 5000
      [.ought "physician" x41, .ought "nurse" y41, neitherBoth])⟩,
  ⟨"#41: the single-agent version is still definitely inconsistent",
    isFormulaSetConsistent 0 5000 [.ought "physician" x41, .ought "physician" y41, neitherBoth]
      == .ok (.definitely false)⟩,
  ⟨"#41: a single-agent refutation still certifies (◇[1]x ∧ ◇[1]y ⊬ ◇([1]x ∧ [1]y))",
    isFormulaValid 0 2000
      (.implies (.and (.diamond (.stit "1" x41)) (.diamond (.stit "1" y41)))
                (.diamond (.and (.stit "1" x41) (.stit "1" y41))))
      == .ok (.definitely false)⟩,
  ⟨"#41: Proved answers are unaffected (Ought implies Can)",
    isFormulaValid 0 2000 (.implies (.ought "physician" x41) (.diamond (.stit "physician" x41)))
      == .ok (.definitely true)⟩,
  -- PaperCorrespondence: Lyon & van Berkel (2024), Definition 3 (pp. 844–845)
  ⟨"L&vB Def 3: K axiom □(p→q)→(□p→□q) is DS-valid",
    isFormulaValid 0 5000 (.implies (.box (.implies p q)) (.implies (.box p) (.box q)))
      == .ok (.definitely true)⟩,
  ⟨"L&vB Def 3: ⊗_i p and ⊗_i ¬p are jointly inconsistent",
    isFormulaSetConsistent 0 5000 [.ought "i" p, .ought "i" (.not p)] == .ok (.definitely false)⟩,
  -- Example 5 (p. 847)
  ⟨"L&vB Example 5: ⊗_i p → ◇[i]p ∨ ⊖_i ¬p is DS-valid",
    isFormulaValid 0 5000 oic == .ok (.definitely true)⟩,
  -- Algorithm 1 (p. 856, listing pp. 858–860) + Figure 5 (p. 865)
  ⟨"L&vB §4.1 counterexample ◇[1]p ∨ ◇[2]q: refutes without MaxStepsExceeded",
    isRefuted (proveFormula 0 5000 (.or (.choiceDiamond "1" p) (.choiceDiamond "2" q)))⟩,
  -- RegressionIssue18: A1
  ⟨"A1 tableau: a 0-step budget yields Unknown, not 'consistent'",
    tableauConsistent systemK 0 [p] == .unknown (.budgetExhausted 0)⟩,
  ⟨"A1 tableau: with budget the same set is Definitely satisfiable",
    tableauConsistent systemK 1000 [p] == .definitely true⟩,
  ⟨"A1 G3DS: satisfiability of ⊗_i p ∧ ⊗_i ¬p at budget 1 is Unknown",
    isFormulaSatisfiable 0 1 (.and (.ought "i" p) (.ought "i" (.not p)))
      == .ok (.unknown (.budgetExhausted 1))⟩,
  -- RegressionIssue18: A3
  ⟨"A3 tableau: {⊥} is inconsistent", tableauConsistent systemK 1000 [.bot] == .definitely false⟩,
  ⟨"A3 tableau: {p, p → ⊥} is inconsistent (negation as →⊥)",
    tableauConsistent systemK 1000 [p, .implies p .bot] == .definitely false⟩,
  ⟨"A3 tableau: ⊢ ⊤ is provable", tableauProves systemK 1000 [] Formula.top == .definitely true⟩,
  ⟨"A3 G3DS: ¬⊥ is valid", isFormulaValid 0 5000 (.not .bot) == .ok (.definitely true)⟩,
  ⟨"A3 G3DS: ⊥ → p is valid", isFormulaValid 0 5000 (.implies .bot p) == .ok (.definitely true)⟩,
  ⟨"A3 G3DS: □⊥ is NOT valid (positive ⊥ must stay inert, not close)",
    isFormulaValid 0 5000 (.box .bot) == .ok (.definitely false)⟩,
  -- RegressionIssue18: consistency
  ⟨"G3DS: {⊗_i p, ⊗_i ¬p} is inconsistent",
    isFormulaSetConsistent 0 5000 [.ought "i" p, .ought "i" (.not p)] == .ok (.definitely false)⟩,
  -- Not in gamen-hs. Guards applyOughtB's (C_⊗_i) witness condition that
  -- the witness `u` carry `I_⊗_i u`: here w₀ carries `p` but is not ideal,
  -- so it must not count as a witness for `⊗_i p`. Without the check the
  -- rule never fires, satOught fails, and the search ends `stuck`
  -- (unknown). Expected verdict from gamen-hs GHCi:
  -- `isFormulaValid 0 1000 (Or (Atom "p") (Ought "i" (Atom "p")))` ⇒
  -- `Definitely False` (proveFormula ⇒ Refuted).
  ⟨"Not in gamen-hs: p ∨ ⊗_i p is not valid (⊗_i witness must be ideal)",
    isFormulaValid 0 1000 (.or p (.ought "i" p)) == .ok (.definitely false)
      && isRefuted (proveFormula 0 1000 (.or p (.ought "i" p)))⟩
  ]

/-! ## Deontic-STIT base module (`Gamen.DeonticStit`)

Port of the last five `describe` blocks of `test/DeonticStitSpec.hs`
("Deontic STIT formula construction", "DS model construction and frame
conditions", "DS satisfaction (Definition 3)", "toNNF preserves DS
satisfaction (issue #8 step B)", "Normative reasoning applications
(Section 5)"), all 17 `it`s, in file order. `test/DeonticStitSpec.hs`'s
"DeonticStit.CounterModel: extractDSModel" block and
`PaperCorrespondence.hs`'s "Definition 20" block are in
`counterModelCases`. `dsSatisfies` returns `Except`,
so its results are compared with `okIs` or with `==` against another
`dsSatisfies` call (both sides `Except`), never unwrapped to `Bool`. -/

/-- The cycling example from Lyon & van Berkel (2024), Figure 1 (p. 846):
Jade (j) and Kai (k) cycling on a two-lane road. -/
def dsFrame' : DSFrame :=
  mkDSFrame ["w1", "w2", "w3", "w4"]
    -- Jade's choice relation (equivalence classes: {w1,w3}, {w2,w4})
    [ ("j", [ ("w1", "w1"), ("w1", "w3"), ("w3", "w1"), ("w3", "w3")
            , ("w2", "w2"), ("w2", "w4"), ("w4", "w2"), ("w4", "w4") ])
    -- Kai's choice relation (equivalence classes: {w1,w2}, {w3,w4})
    , ("k", [ ("w1", "w1"), ("w1", "w2"), ("w2", "w1"), ("w2", "w2")
            , ("w3", "w3"), ("w3", "w4"), ("w4", "w3"), ("w4", "w4") ]) ]
    -- Ideal sets: Jade obligated to {w1,w3}, Kai to {w1,w2}
    [("j", ["w1", "w3"]), ("k", ["w1", "w2"])]

def dsModel' : DSModel :=
  mkDSModel dsFrame'
    [ ("left_jade",  ["w1", "w3"])
    , ("right_jade", ["w2", "w4"])
    , ("left_kai",   ["w1", "w2"])
    , ("right_kai",  ["w3", "w4"])
    , ("coll",       ["w2", "w3"]) ]

def deonticStitCases : List Case :=
  let lj : Formula := .atom "left_jade"
  let rj : Formula := .atom "right_jade"
  let lk : Formula := .atom "left_kai"
  let rk : Formula := .atom "right_kai"
  let coll : Formula := .atom "coll"
  [
  -- Deontic STIT formula construction
  ⟨"displays Ought and Permitted",
    toString (Formula.ought "j" lj) == "O[j]left_jade"
      && toString (Formula.permitted "j" lj) == "P[j]left_jade"⟩,
  ⟨"Ought/Permitted are not modal-free",
    (Formula.ought "j" lj).isModalFree == false
      && (Formula.permitted "j" lj).isModalFree == false⟩,
  -- DS model construction and frame conditions
  ⟨"valid frame passes all conditions", isValidDSFrame dsFrame' == true⟩,
  ⟨"C1: R_[i] are equivalence relations", checkDS_C1 dsFrame' == true⟩,
  ⟨"C2: independence of agents", checkDS_C2 dsFrame' == true⟩,
  ⟨"D1: ideal worlds subset of W", checkDS_D1 dsFrame' == true⟩,
  ⟨"D2: every agent has ideal worlds", checkDS_D2 dsFrame' == true⟩,
  ⟨"D3: ideal worlds fill choice cells", checkDS_D3 dsFrame' == true⟩,
  -- DS satisfaction (Definition 3)
  ⟨"evaluates [i]phi (agent choice)",
    okIs (dsSatisfies dsModel' "w1" (.stit "j" lj)) true
      && okIs (dsSatisfies dsModel' "w2" (.stit "j" lj)) false⟩,
  ⟨"evaluates □phi (settled)",
    okIs (dsSatisfies dsModel' "w1" (.box lj)) false
      && okIs (dsSatisfies dsModel' "w1" (.box (.or lj rj))) true⟩,
  ⟨"evaluates ⊗_i phi (ought)",
    okIs (dsSatisfies dsModel' "w1" (.ought "j" lj)) true
      && okIs (dsSatisfies dsModel' "w1" (.ought "j" rj)) false
      && okIs (dsSatisfies dsModel' "w1" (.ought "k" lk)) true⟩,
  ⟨"evaluates ⊖_i phi (permitted)",
    okIs (dsSatisfies dsModel' "w1" (.permitted "j" lj)) true
      && okIs (dsSatisfies dsModel' "w1" (.permitted "j" coll)) true
      && okIs (dsSatisfies dsModel' "w1" (.permitted "j" rj)) false⟩,
  ⟨"collision avoidance is settled if both comply",
    let noColl := Formula.implies (.not coll) (.or (.and rj rk) (.and lj lk))
    okIs (dsSatisfies dsModel' "w1" (.box noColl)) true⟩,
  -- Not in gamen-hs. `And`/`Or` must short-circuit like Haskell's lazy
  -- `&&`/`||`: the right side (an operator `dsSatisfies` has no DS
  -- semantics for) must never be evaluated once the left side already
  -- settles the result. Expected values from gamen-hs GHCi (single-world
  -- model, `p` true at `w1`): `dsSatisfies m "w1" (And Bot (FutureBox p))`
  -- ⇒ `False`; `dsSatisfies m "w1" (Or p (Next p))` ⇒ `True`.
  ⟨"And Bot _ short-circuits to False without evaluating an erroring right side",
    okIs (dsSatisfies dsModel' "w1" (.and .bot (.futureBox lj))) false⟩,
  ⟨"Or left_jade _ short-circuits to True without evaluating an erroring right side",
    okIs (dsSatisfies dsModel' "w1" (.or lj (.next lj))) true⟩,
  -- toNNF preserves DS satisfaction (issue #8 step B)
  ⟨"every L_n test formula is satisfaction-equivalent to its NNF",
    let phis : List Formula :=
      [ .implies (.stit "j" lj) (.permitted "j" lj)
      , .iff (.ought "k" lk) (.not (.permitted "k" (.not lk)))
      , .not (.and (.ought "j" lj) (.permitted "j" rj))
      , .not (.implies (.box (.or lj rj)) (.stit "j" lj))
      , .not (.choiceDiamond "k" coll) ]
    let worlds_ := ["w1", "w2", "w3", "w4"]
    -- Comparing the two `Except` results directly would let a planted
    -- `dsSatisfies` that always throws pass vacuously (`error == error`);
    -- requiring the left side to be `.ok` rules that out.
    phis.all fun phi =>
      worlds_.all fun w =>
        match dsSatisfies dsModel' w phi with
        | .ok v => dsSatisfies dsModel' w phi.toNNF == .ok v
        | .error _ => false⟩,
  -- Normative reasoning applications (Section 5)
  ⟨"duty checking: identifies Jade's obligations",
    okIs (dutyCheck dsModel' "w1" "j" [lj, rj, lk, rk]) [lj]⟩,
  ⟨"compliance checking: Jade's left choice complies",
    complianceCheck dsModel' "j" (Std.TreeSet.ofList ["w1", "w3"]) == true
      && complianceCheck dsModel' "j" (Std.TreeSet.ofList ["w2", "w4"]) == false⟩,
  ⟨"joint fulfillment: can Jade fulfill all duties?",
    okIs (jointFulfillment dsModel' "j" [lj]) true
      && okIs (jointFulfillment dsModel' "j" [lj, .not coll]) true
      && okIs (jointFulfillment dsModel' "j" [rj]) false⟩,
  -- WorldGuardsSpec.hs:36, "dsSatisfies errors on world not in DSModel"
  -- (gamen-hs#7). The Haskell's sibling `it`s in the same describe block
  -- (`eSatisfies`/`sSatisfies`/`xSatisfies`/`lSatisfies`) need
  -- `Gamen.Epistemic`/`.Stit`/`.Xstit`/`.Laca`, not yet ported.
  ⟨"dsSatisfies errors on world not in DSModel",
    let dfr := mkDSFrame ["a", "b"] [("ag", [("a", "a"), ("b", "b")])] [("ag", ["a"])]
    let dm := mkDSModel dfr [("p", ["a", "b"]), ("q", ["b"]), ("r", ["a"])]
    let probeFormula : Formula :=
      .implies (.or (.atom "p") (.atom "q")) (.and (.not (.atom "q")) (.atom "r"))
    okIs (dsSatisfies dm "a" probeFormula) true
      && isErr (dsSatisfies dm "c" probeFormula)⟩
  ]

/-! ## Property tests (Plausible) -/

def properties : List (String × IO Bool) :=
  -- `.gaveUp` (Plausible could not draw enough well-formed examples — the
  -- same outcome a thrown `GenError` produces) must fail here too: it used
  -- to fall through the catch-all `| _ => return true` and read as a pass,
  -- which is exactly how properties with an inner `m : Model` binder
  -- stayed green when `genKripkeModel` was made to always throw. A
  -- `GenError` at an *inner* binder (`NamedBinder "f" <| ∀ f : Formula,
  -- NamedBinder "m" <| ∀ m : Model, …`) is caught by Plausible's own
  -- `runPropE` and turned into `.gaveUp` before it ever reaches here —
  -- but at the outermost binder (a property with no other variable ahead
  -- of the one whose generator throws, e.g. "□(p→q)→(□p→□q) …"'s
  -- `∀ m : Model`), `Testable.checkIO`'s own top-level call to
  -- `Testable.runProp` has no such wrapper, and the exception reaches
  -- `IO` uncaught, aborting the whole test binary rather than failing
  -- just this one property. `run` must catch it itself.
  let run (p : Prop) (numInst : Nat := 300) [Testable p] : IO Bool := do
    match ← (try some <$> Testable.checkIO p { numInst := numInst, quiet := true }
              catch e => do
                IO.println s!"    generator errored: {e}"
                pure none) with
    | none => return false
    | some (.failure _ xs _) => IO.println s!"    counterexample: {xs}"; return false
    | some (.gaveUp n) => do
        IO.println s!"    gave up: {n} well-formed example(s) could not be drawn"
        return false
    | some (.success _) => return true
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
        (!proves [] f || truthsIn testModel f == some [true, true, true]) = true)),
    -- Gamen.Tableau: K satisfiability — internal soundness invariant
    -- (issue #18): a formula and its negation can never both close.
    ("no formula and its negation are both provably unsatisfiable",
      run (NamedBinder "f" <| ∀ f : Formula,
        !(tableauConsistent systemK defaultMaxSteps [f] == .definitely false
            && tableauConsistent systemK defaultMaxSteps [.not f] == .definitely false)) 200),
    -- Gamen.Tableau: soundness vs. Kripke semantics (K, KT, K4, S4, S5) —
    -- mirrors the "Gamen.Tableau: soundness vs. Kripke semantics" describe
    -- block of `test/Properties.hs`, minus the seven `==>`-shaped
    -- properties: "unsatisfiable ⇒ …", "provable entailment ⇒ …",
    -- "satisfied in some model ⇒ …", "S5 unsatisfiable ⇒ …", and
    -- "extracted countermodel …" now live in `Tests/SlowMain.lean`
    -- (`lake exe slowtests`) — running them at Haskell's real
    -- `numInst`/discard-cap/size takes on the order of Haskell's own
    -- ~460s for this same set, which would make `lake test` itself that
    -- slow. The disabled/quarantined temporal property and its "issue
    -- #25" `it` are still not ported (both need `Gamen.Temporal`).
    ("axiom-scheme instances: prover proves them and they hold in every model (K)",
      run (NamedBinder "f" <| ∀ f : ValidFormula, NamedBinder "m" <| ∀ m : Model,
        (match allSatisfies m f.getFormula with
          | .ok true => !(tableauProves systemK defaultMaxSteps [] f.getFormula
                            == .definitely false)
          | _ => false) = true) 300),
    ("K-valid instances and the T axiom hold in every reflexive model (KT)",
      run (NamedBinder "f" <| ∀ f : ValidFormula, NamedBinder "g" <| ∀ g : Formula,
        NamedBinder "m" <| ∀ m0 : Model,
          (match allSatisfies (reflexiveClosureModel m0) f.getFormula,
                 allSatisfies (reflexiveClosureModel m0) (.implies (.box g) g) with
            | .ok true, .ok true =>
                !(tableauProves systemKT defaultMaxSteps [] (.implies (.box g) g)
                    == .definitely false)
            | _, _ => false) = true) 200),
    ("axiom 4 instances: proved by K4 and true on transitive frames",
      run (NamedBinder "f" <| ∀ f : FourFormula, NamedBinder "m" <| ∀ m0 : Model,
        (match transitiveClosureModel m0 with
          | .error _ => false
          | .ok m =>
            match allSatisfies m f.getFormula with
            | .ok true =>
                isTransitive m.frame
                  && !(tableauProves systemK4 2000 [] f.getFormula == .definitely false)
            | _ => false) = true) 200),
    ("S4 instances: proved by S4 and true on reflexive-transitive frames",
      run (NamedBinder "f" <| ∀ f : S4Formula, NamedBinder "m" <| ∀ m0 : Model,
        (match s4ClosureModel m0 with
          | .error _ => false
          | .ok m =>
            match allSatisfies m f.getFormula with
            | .ok true =>
                isReflexive m.frame && isTransitive m.frame
                  && !(tableauProves systemS4 2000 [] f.getFormula == .definitely false)
            | _ => false) = true) 200),
    ("S5 instances: proved by S5 and true on equivalence frames",
      run (NamedBinder "f" <| ∀ f : S5Formula, NamedBinder "m" <| ∀ m0 : Model,
        (match s5ClosureModel m0 with
          | .error _ => false
          | .ok m =>
            match allSatisfies m f.getFormula with
            | .ok true =>
                isReflexive m.frame && isTransitive m.frame && isEuclidean m.frame
                  && !(tableauProves systemS5 2000 [] f.getFormula == .definitely false)
            | _ => false) = true) 200),
    -- Gamen.Semantics: K distribution axiom.
    ("□(p→q)→(□p→□q) holds at every world of every random model",
      run (NamedBinder "m" <| ∀ m : Model,
        isOkTrue (allSatisfies m
          (.implies (.box (.implies (.atomF ⟨"p"⟩) (.atomF ⟨"q"⟩)))
                    (.implies (.box (.atomF ⟨"p"⟩)) (.box (.atomF ⟨"q"⟩))))) = true) 100),
    -- Gamen.RankingTheory: structural invariants — the two `isContingent
    -- ⇒ …` properties now live in `Tests/SlowMain.lean` alongside the
    -- other five `==>`-shaped properties (see the comment above).
    ]
where
  toNNF := Formula.toNNF
  isNNF := Formula.isNNF

/-! ## Deontic-STIT counter-model extraction (`Gamen.DeonticStit.CounterModel`)

Ports, in file order:

* `test/DeonticStitSpec.hs`, "DeonticStit.CounterModel: extractDSModel"
  (all 3 `it`s).
* `test/PaperCorrespondence.hs`, "Lyon & van Berkel (2024) — G3DS^k_n
  prover", its "Definition 20" block (all 3 `it`s). Citation fixed against
  the PDF: Definition 20 runs pp. 858–859 (the Haskell says p. 858).
* `test/RegressionIssue18.hs`, "B6: counter-models are verified, not
  trusted": its two G3DS `it`s. The block's three tableau `it`s exercise
  `Gamen.Tableau`'s `extractCountermodel`, not this module.
* One case not in gamen-hs, for `euclideanClose` on its own.

`refutedModel` returns `Except`: a proof, a budget overrun, a prover error,
or an extraction error all land in `.error`, and every case below fails on
`.error` whichever answer it expects. `dsSatisfies` results are compared
against `.ok false`, never unwrapped. -/

/-- Run `proveFormula 0 1000 phi`; on `.refuted gt s`, extract the
counter-model. Anything but a refutation is an error. -/
def refutedModel (phi : Formula) : Except String DSModel := do
  match ← proveFormula 0 1000 phi with
  | .refuted gt s => extractDSModel gt s
  | _ => throw s!"{phi} should be refuted"

def counterModelCases : List Case :=
  let rootW : World := toString label0
  let withModel (phi : Formula) (check : DSModel → Bool) : Bool :=
    match refutedModel phi with
    | .ok m => check m
    | .error _ => false
  let l (n : Nat) : Label := ⟨n⟩
  [
  -- DeonticStitSpec: "DeonticStit.CounterModel: extractDSModel"
  ⟨"Box p is refuted; extracted model falsifies Box p at w0",
    withModel (.box p) fun m =>
      m.dsFrame.dsWorlds.contains rootW && dsSatisfies m rootW (.box p) == .ok false⟩,
  ⟨"Stit i p is refuted; extracted model falsifies it at w0",
    withModel (.stit "i" p) fun m =>
      m.dsFrame.dsWorlds.contains rootW && dsSatisfies m rootW (.stit "i" p) == .ok false⟩,
  ⟨"Ought i p is refuted; extracted model has nonempty ideal",
    withModel (.ought "i" p) fun m =>
      dsSatisfies m rootW (.ought "i" p) == .ok false && isValidDSFrame m.dsFrame⟩,
  -- PaperCorrespondence: Lyon & van Berkel (2024), Definition 20 (pp. 858–859)
  ⟨"Box p is refuted; root world label0 ∈ worlds of extracted model (= True)",
    withModel (.box p) fun m => m.dsFrame.dsWorlds.contains rootW⟩,
  ⟨"Box p is refuted; extracted model falsifies □p at root (= False)",
    withModel (.box p) fun m => dsSatisfies m rootW (.box p) == .ok false⟩,
  ⟨"Ought i p is refuted; extracted model satisfies D2 (non-empty ideal)",
    withModel (.ought "i" p) fun _ => true⟩,
  -- RegressionIssue18: "B6: counter-models are verified, not trusted"
  ⟨"G3DS: extraction returns a verified Right model for □p",
    withModel (.box p) fun m =>
      isValidDSFrame m.dsFrame && m.dsFrame.dsWorlds.contains rootW
        && dsSatisfies m rootW (.box p) == .ok false⟩,
  ⟨"G3DS: ⊗_i p extracts a verified counter-model with a valid frame",
    withModel (.ought "i" p) fun m => dsSatisfies m rootW (.ought "i" p) == .ok false⟩,
  -- Not in gamen-hs: euclideanClose on its own. From {(0,1), (0,2)}
  -- Euclideanness adds (1,1), (1,2), (2,1), (2,2); nothing else follows.
  ⟨"euclideanClose {(w0,w1),(w0,w2)} adds exactly the four (u,v) pairs over {w1,w2}",
    (euclideanClose ∅ (Std.TreeSet.ofList [(l 0, l 1), (l 0, l 2)] lexOrd.compare)).map
        (·.toList) ==
      .ok [(l 0, l 1), (l 0, l 2), (l 1, l 1), (l 1, l 2), (l 2, l 1), (l 2, l 2)]⟩
  ]

/-! ## Tableau countermodel closure

* `test/RegressionIssue18.hs`, "B6: counter-models are verified, not
  trusted": its three tableau `it`s (the two G3DS `it`s are in
  `counterModelCases`).
* Not in gamen-hs: `Tableau.transitiveClose` now goes through the shared
  `iterateToFixpoint`. One case checks it against a reference closure on all
  512 relations over three worlds; another checks that running out of fuel
  is an error, where the old loop returned a partly closed relation. -/

/-- B6's `openBranchesOf`, keeping only the first open branch. -/
def firstOpenBranch (sys : System) (steps : Nat) (as : List PrefixedFormula) : Option Branch :=
  match buildTableau sys steps as with
  | .stillOpen (b :: _) => some b
  | _ => none

/-- Reference transitive closure (Warshall) over a fixed world list. -/
def warshall (ws : List World) (r : List (World × World)) : List (World × World) := Id.run do
  let mut reach := r
  for k in ws do
    for i in ws do
      for j in ws do
        if !reach.contains (i, j) && reach.contains (i, k) && reach.contains (k, j) then
          reach := reach ++ [(i, j)]
  return reach

/-- Every relation over `{a, b, c}`, as a list of pairs (512 of them). -/
def allRelations3 : List (List (World × World)) :=
  let ws := ["a", "b", "c"]
  let pairs := ws.flatMap fun x => ws.map fun y => (x, y)
  (List.range (2 ^ pairs.length)).map fun mask =>
    (pairs.zipIdx.filter fun (_, i) => mask.testBit i).map (·.1)

def closureCases : List Case :=
  let ws := ["a", "b", "c"]
  let rel (ps : List (World × World)) : Rel := Std.TreeSet.ofList ps lexOrd.compare
  [ ⟨"tableau: open branch yields a Right model that falsifies the goal",
      match firstOpenBranch systemK 1000 [pfFalse .root (.implies (.box p) p)] with
      | some b => (extractCountermodel systemK b >>= (isTrueIn · (.implies (.box p) p))) == .ok false
      | none => false⟩,
    ⟨"tableau: a closed branch has no counter-model (Left)",
      match extractCountermodel systemK (Branch.ofList [pfTrue .root p, pfFalse .root p]) with
      | .error _ => true
      | .ok _ => false⟩,
    ⟨"tableau: per-system closure makes the KT model reflexive",
      match firstOpenBranch systemKT 1000 [pfFalse .root (.implies p (.box p))] with
      | some b =>
        match extractCountermodel systemKT b with
        | .ok cm => cm.frame.worlds.toList.all fun w => (cm.frame.accessible w).contains w
        | .error _ => false
      | none => false⟩,
    ⟨"Not in gamen-hs: transitiveClose matches Warshall on all 512 relations over 3 worlds",
      allRelations3.all fun ps =>
        (transitiveClose ws (rel ps)).map (·.toList) == .ok (rel (warshall ws ps)).toList⟩,
    ⟨"Not in gamen-hs: transitiveClose errors when fuel runs out (no partial relation)",
      -- `ws = []` gives fuel 1: one composition adds (a, c), so no fixpoint
      -- is confirmed within the bound.
      match transitiveClose [] (rel [("a", "b"), ("b", "c")]) with
      | .error _ => true
      | .ok _ => false⟩
  ]

/-! ## Cross-checks of the decision procedures (Not in gamen-hs)

Lean-only (Gamen.jl issue #20). The random checks and their bounds are
documented in `Tests/PropertyHelpers.lean` ("Cross-checks of the decision
procedures"). Here: 40 draws per system from seed `crossSeed`, frames of
at most 3 worlds, plus 60 T/D/B/4/5 schema instances per system (seed
`crossSeed + 2`, `genSchemaSample`), which catch an unsound rule added to
a system; G3DS 40 draws for 1 and for 2 agents against 20 random
DS models. `lake exe slowtests` runs 1000 draws per system (and 4-world
frames for KT, KTB, S4, S5) and 500 G3DS draws per agent set.

gamen-hs#38 (KD countermodels not serial) and #39 (K/KD/K4 extraction
failing on a branch left open only by blocking) were fixed upstream in
08a52d4 (`serialClose`, `blockerOf`/`borrowsBlockerWitnesses`); the three
regression cases below now pin the fixed behavior (every open branch
extracts a verified model) instead of the bug. Two more regressions
remain unfixed and still pin the bug, identical in gamen-hs (checked in
GHCi): one documented G3DS deferral (IoaOp/C2, gamen-hs#41, open; since
483c463 `isFormulaValid` reports such a refutation as uncertified instead of
invalid, and the pinned case checks that too) and one
budget-exhaustion note (KT/KTB/S4/S5 on a small formula, gamen-hs#40);
each still flips when fixed there. KTB and S5 do not borrow their blocker's
witnesses (see `borrowsBlockerWitnesses`), so their blocked branches can
still fail extraction; tracked separately as gamen-hs#42, open (known
failures are KTB-only). This fix does not touch them and the random
samples here have not hit one, so `crossExtractOne` still treats any KTB
or S5 extraction failure as a hard error rather than excusing it. The
#42 example is pinned below (KTB fails, flips when fixed; S5 extracts),
with a KTB formula that breaks if KTB is added to the borrowing list and
a KD formula that needs KD's borrowed edges. -/

def crossSeed : Nat := 20260925

def crossCase (name : String) (r : Bool × String) (seed : Nat := crossSeed) : Case :=
  ⟨s!"Not in gamen-hs: {name} (seed {seed}): {r.2}", r.1⟩

/-- The G3DS formula whose stability frame fails only C2. -/
def c2Formula : Formula :=
  .implies (.box (.iff (.stit "1" p) (.box .bot))) (.ought "2" (.choiceDiamond "2" (.implies q p)))

/-- (C1, C2, C3 (k = 0), D1, D2, D3) of `c2Formula`'s stability frame,
and whether `extractDSModel` rejects it as "not a valid DS frame". -/
def c2Shape : Except String (List Bool × Bool) := do
  match ← proveFormula 0 5000 c2Formula with
  | .refuted gt s =>
    let fr := (← dsStabilityModel gt s).dsFrame
    let rejected := match extractDSModel gt s with
      | .error e => (e.splitOn "not a valid DS frame").length > 1
      | .ok _ => false
    return ([checkDS_C1 fr, checkDS_C2 fr, checkDS_C3 0 fr, checkDS_D1 fr, checkDS_D2 fr,
      checkDS_D3 fr], rejected)
  | _ => throw "c2Formula: not refuted"

def crossCheckCases : List Case :=
  let kd : XSystem := ⟨systemKD, isSerial, "serial"⟩
  let k : XSystem := ⟨systemK, fun _ => true, "any"⟩
  let k4 : XSystem := ⟨systemK4, isTransitive, "transitive"⟩
  let ktb : XSystem := ⟨systemKB, fun f => isReflexive f && isSymmetric f, "reflexive+symmetric"⟩
  let s5 : XSystem := ⟨systemS5, isEquivalenceRelation, "equivalence"⟩
  let tFormula : Formula := .diamond (.or (.and (.box q) (.box .bot)) (.and p .bot))
  (xSystems.flatMap fun xs =>
    [ crossCase s!"{xs.sys.name} verdicts vs. ≤3-world {xs.condName} frames"
        (crossCheckVerdict (crossCheckSystem xs crossSeed 40 3 defaultMaxSteps)),
      crossCase s!"{xs.sys.name} extracted countermodels re-checked"
        (crossExtractVerdict (crossExtractSystem xs crossSeed 40 3 defaultMaxSteps)) ])
  ++ (xSystems.flatMap fun xs =>
    let fs := schemaSamples (crossSeed + 2) 60
    [ crossCase s!"{xs.sys.name} verdicts on 60 T/D/B/4/5 schema instances vs. ≤3-world \
        {xs.condName} frames" (crossCheckVerdict (fs >>= (crossCheckOn xs · 3 defaultMaxSteps))) (crossSeed + 2),
      crossCase s!"{xs.sys.name} extracted countermodels of 60 schema instances re-checked"
        (crossExtractVerdict (fs >>= (crossExtractOn xs · 3 defaultMaxSteps))) (crossSeed + 2) ])
  ++ ([["1"], ["1", "2"]].flatMap fun ag =>
    [ crossCase s!"G3DS {ag.length}-agent: proved ⇒ true in 20 random DS models"
        (dsCrossCheckVerdict (dsCrossCheck ag crossSeed 40 20 5000)),
      crossCase s!"G3DS {ag.length}-agent: extracted models re-checked"
        (dsExtractVerdict (dsExtractCheck ag crossSeed 40 5000)) ])
  ++ [
  ⟨"Not in gamen-hs: KD: refuting p extracts a serial model (gamen-hs#38, fixed upstream)",
    extractionShapes kd p == some ["verified"]⟩,
  ⟨"Not in gamen-hs: K: □□p ↔ ¬□p, every open branch extracts, including the blocked one \
    (gamen-hs#39, fixed upstream)",
    extractionShapes k (.iff (.box (.box p)) (.not (.box p))) == some ["verified", "verified"]⟩,
  ⟨"Not in gamen-hs: K4: ◇□p ∧ □⊥, every open branch extracts, including the blocked one \
    (gamen-hs#39, fixed upstream)",
    extractionShapes k4 (.and (.diamond (.box p)) (.box .bot))
      == some ["verified", "verified", "verified"]⟩,
  -- Needs KD's borrowed edges: with "KD" removed from
  -- `borrowsBlockerWitnesses`, the blocked branch fails its re-check
  -- (the #39 KD case above does not, see its comment).
  ⟨"Not in gamen-hs: KD: ¬(◇p ∧ ◇◇p), every open branch extracts, including the blocked one \
    (needs KD's borrowed edges; gamen-hs#39, fixed upstream; proposed for gamen-hs in #45)",
    extractionShapes kd (.not (.and (.diamond p) (.diamond (.diamond p)))) == some ["verified"]⟩,
  -- Why KTB is not in `borrowsBlockerWitnesses`: this branch extracts
  -- without borrowed edges, and adding "KTB" to the list makes it fail
  -- (symmetric closure turns a borrowed edge σ → τ′ into τ′ → σ; see
  -- gamen-hs#42). Found by exhaustive search up to size 7 (none) and
  -- random depth-8 formulas (seed 2502, then shrunk by hand).
  ⟨"Not in gamen-hs: KTB: ⊥ ∨ □◇(□⊥ ∨ ¬p) extracts a reflexive+symmetric countermodel \
    without borrowing its blocker's witnesses (fails if KTB borrows; gamen-hs#42; proposed in #45)",
    extractionShapes ktb (.or .bot (.box (.diamond (.or (.box .bot) (.not p)))))
      == some ["verified"]⟩,
  -- gamen-hs#42, open: KTB's only open branch for F ◇□□¬p is blocked and
  -- fails the re-check (`F □¬p at 1.1.2`). Pins the bug; flips when fixed.
  ⟨"Not in gamen-hs: KTB: ◇□□¬p's only open branch fails extraction \
    (gamen-hs#42, open; flips when fixed)",
    match extractionShapes ktb (.diamond (.box (.box (.not p)))) with
    | some [s] => s.startsWith "error: extractCountermodel: extracted model fails to satisfy"
    | _ => false⟩,
  -- S5 does not borrow either, but the blocked branch for the same
  -- formula extracts, as gamen-hs#42 reports. Pinned so a fix to #42
  -- cannot break S5. There is no S5 counterpart of the KTB case above:
  -- the prefix tree is connected, so S5's equivalence closure is already
  -- all of W × W with or without borrowed edges, and adding "S5" to
  -- `borrowsBlockerWitnesses` changes nothing.
  ⟨"Not in gamen-hs: S5: ◇□□¬p extracts an equivalence-frame countermodel \
    without borrowing (gamen-hs#42 reports S5 unaffected here)",
    extractionShapes s5 (.diamond (.box (.box (.not p)))) == some ["verified"]⟩,
  ⟨"Not in gamen-hs: G3DS: □([1]p ↔ □⊥) → ⊗₂⟨2⟩(q → p) is refuted, extraction rejects \
    a stability frame that fails only C2 (IoaOp deferral, gamen-hs#41), and isFormulaValid \
    reports it uncertified, not invalid (flips when IoaOp is scheduled)",
    c2Shape == .ok ([true, false, true, true, true, true], true)
      && isUncertified (isFormulaValid 0 5000 c2Formula)⟩,
  ⟨"Not in gamen-hs: KT: ◇((□q ∧ □⊥) ∨ (p ∧ ⊥)) exhausts the default budget (unknown, \
    never a wrong answer; same in gamen-hs; flips when fixed)",
    tableauProves systemKT defaultMaxSteps [] tFormula == .unknown (.budgetExhausted defaultMaxSteps)⟩
  ]

/-! ## Cgs (`Gamen.Cgs`)

There is no `test/CgsSpec.hs` in gamen-hs, and the `Cgs`-exercising
`PaperCorrespondence.hs` sections all reach it only through `Coalition`,
`Atl`/`Atl.ModelCheck`, `Atel`, or `Laca`'s `lacaToCgs`, none ported yet
(`PORTING.md`):

- "Pauly (2002) — Coalition Logic" (`coalSatisfies`, `checkTopEffectivity`,
  `checkBotMonotonicity`, `checkMonotonicity`, `checkSuperadditivity`: all
  `Gamen.Coalition`);
- "Alur, Henzinger & Kupferman (2002) — ATL" (`sat`, `atlSatisfies`,
  `CanNext`/`CanAlways`/`CanEventually`/`CanUntil`: `Gamen.Atl`/
  `Gamen.Atl.ModelCheck`);
- "van der Hoek & Wooldridge (2003) — ATEL" (adds `AtelModel`,
  `mkAtelModel`, `atelSat`: `Gamen.Atel`);
- the imperfect-information ATEL section right after it (adds
  `Gamen.Atl.ImperfectInfo`);
- the "Herzig, Lorini & Perrotin (2022) — LACA" section's `lacaToCgs`
  coercion sub-block (needs `Gamen.Laca`, and then `Gamen.Atl` again for
  `atlSatisfies`/`sat`/`CanNext`/`CanEventually`).

So every case below is a not-in-spec sanity check on the raw `Cgs`
primitives themselves (`mkCgs`, `availableMoves`, `jointMoves`,
`applyJointMove`, `preC`), each flagged as such. The two fixtures are the
`Cgs` values `PaperCorrespondence.hs` builds for the sections above —
the "control game" (Pauly 2002, `Int` states/`String` actions, agents
`alice`/`bob`) and the "loop" model (AHK 2002) — and the expected `preC`
values are computed by hand from the Haskell file's own inline comments
(cited below), not from the Lean code under test. Coverage of `mkCgs`'s
two error branches (an agent with no moves at some state; a joint move
escaping the state set) has no Haskell counterpart at all: `CgsSpec.hs`
doesn't exist, so gamen-hs itself never exercises them; they matter for
the same reason `Kripke.mkFrame`'s dangling-edge check does (adversarial
review B7, cited in `Gamen.Cgs`'s `mkCgs` docstring). -/

/-- Pauly (2002) control game: `PaperCorrespondence.hs` ~1241–1262. Agent
`alice` controls `p` (plays `"p"`/`"not-p"`), agent `bob` controls `q`
(plays `"q"`/`"not-q"`); the transition ignores the source state. -/
private def controlMoves (_ : Nat) (ag : String) : Std.TreeSet String :=
  if ag == "alice" then Std.TreeSet.ofList ["p", "not-p"]
  else if ag == "bob" then Std.TreeSet.ofList ["q", "not-q"]
  else ∅

private def controlTrans (_ : Nat) (jm : Std.TreeMap String String) : Nat :=
  match jm.get? "alice" == some "p", jm.get? "bob" == some "q" with
  | true, true => 0
  | true, false => 1
  | false, true => 2
  | false, false => 3

private def controlLabel : Nat → Std.TreeSet String
  | 0 => Std.TreeSet.ofList ["p", "q"]
  | 1 => Std.TreeSet.ofList ["p"]
  | 2 => Std.TreeSet.ofList ["q"]
  | _ => ∅

private def controlCgs : Except String (Cgs Nat String) :=
  mkCgs (Std.TreeSet.ofList [0, 1, 2, 3]) (Std.TreeSet.ofList ["alice", "bob"])
    controlMoves controlTrans controlLabel

/-- AHK (2002) loop model: `PaperCorrespondence.hs` ~1387–1401. Single
agent `alice`; `"next"` advances `(s + 1) mod 3`, `"stay"` is a self-loop. -/
private def loopMoves (_ : Nat) (_ : String) : Std.TreeSet String :=
  Std.TreeSet.ofList ["next", "stay"]

private def loopTrans (s : Nat) (jm : Std.TreeMap String String) : Nat :=
  match jm.get? "alice" with
  | some "next" => (s + 1) % 3
  | _ => s

private def loopLabel : Nat → Std.TreeSet String
  | 0 => Std.TreeSet.ofList ["p"]
  | 1 => Std.TreeSet.ofList ["q"]
  | _ => ∅

private def loopCgs : Except String (Cgs Nat String) :=
  mkCgs (Std.TreeSet.ofList [0, 1, 2]) (Std.TreeSet.ofList ["alice"]) loopMoves loopTrans loopLabel

def cgsCases : List Case := [
  ⟨"Not in gamen-hs (no CgsSpec.hs): mkCgs accepts the Pauly (2002) control game \
    (non-empty moves for alice and bob at every state)",
    match controlCgs with
    | .ok _ => true
    | .error _ => false⟩,
  ⟨"Not in gamen-hs: mkCgs accepts the AHK (2002) loop model",
    match loopCgs with
    | .ok _ => true
    | .error _ => false⟩,
  ⟨"Not in gamen-hs: mkCgs rejects an agent with no moves at any state",
    match mkCgs (Std.TreeSet.ofList [0, 1]) (Std.TreeSet.ofList ["alice", "carol"])
        controlMoves controlTrans controlLabel with
    | .error _ => true
    | .ok _ => false⟩,
  ⟨"Not in gamen-hs: mkCgs rejects a joint move that escapes the state set",
    let escapingTrans (s : Nat) (jm : Std.TreeMap String String) : Nat :=
      if jm.get? "alice" == some "p" && jm.get? "bob" == some "q" then 99
      else controlTrans s jm
    match mkCgs (Std.TreeSet.ofList [0, 1, 2, 3]) (Std.TreeSet.ofList ["alice", "bob"])
        controlMoves escapingTrans controlLabel with
    | .error _ => true
    | .ok _ => false⟩,
  ⟨"Not in gamen-hs: availableMoves cgs 0 \"alice\" = {\"not-p\",\"p\"}",
    match controlCgs with
    | .ok cgs => availableMoves cgs 0 "alice" == Std.TreeSet.ofList ["not-p", "p"]
    | .error _ => false⟩,
  ⟨"Not in gamen-hs: jointMoves over {alice} at any state has the 2 alice-only moves",
    match controlCgs with
    | .ok cgs =>
      let jms := jointMoves cgs (Std.TreeSet.ofList ["alice"]) 0
      jms.length == 2
      && jms.any (fun m => m.get? "alice" == some "p" && m.get? "bob" == none)
      && jms.any (fun m => m.get? "alice" == some "not-p" && m.get? "bob" == none)
    | .error _ => false⟩,
  ⟨"Not in gamen-hs: jointMoves over the grand coalition has all 4 (alice, bob) combinations",
    match controlCgs with
    | .ok cgs =>
      let jms := jointMoves cgs (Std.TreeSet.ofList ["alice", "bob"]) 0
      jms.length == 4
      && jms.any (fun m => m.get? "alice" == some "p" && m.get? "bob" == some "q")
      && jms.any (fun m => m.get? "alice" == some "p" && m.get? "bob" == some "not-q")
      && jms.any (fun m => m.get? "alice" == some "not-p" && m.get? "bob" == some "q")
      && jms.any (fun m => m.get? "alice" == some "not-p" && m.get? "bob" == some "not-q")
    | .error _ => false⟩,
  ⟨"Not in gamen-hs: applyJointMove matches the control game's transition table",
    match controlCgs with
    | .ok cgs =>
      applyJointMove cgs 0 (Std.TreeMap.ofList [("alice", "p"), ("bob", "q")]) == 0
      && applyJointMove cgs 0 (Std.TreeMap.ofList [("alice", "p"), ("bob", "not-q")]) == 1
      && applyJointMove cgs 0 (Std.TreeMap.ofList [("alice", "not-p"), ("bob", "q")]) == 2
      && applyJointMove cgs 0 (Std.TreeMap.ofList [("alice", "not-p"), ("bob", "not-q")]) == 3
    | .error _ => false⟩,
  ⟨"Not in gamen-hs, but PaperCorrespondence.hs ~1292–1299 (\"[{alice}]p holds at ALL \
    states\"): preC(control, {alice}, {0,1}) = all four states — alice's move \"p\" \
    lands in {0,1} regardless of bob",
    match controlCgs with
    | .ok cgs => preC cgs (Std.TreeSet.ofList ["alice"]) (Std.TreeSet.ofList [0, 1]) == cgs.cgsStates
    | .error _ => false⟩,
  ⟨"Not in gamen-hs, but PaperCorrespondence.hs ~1301–1304 (\"[{alice}]q at state 0 is \
    FALSE\"): preC(control, {alice}, {0,2}) = ∅ — alice cannot force q against bob",
    match controlCgs with
    | .ok cgs => preC cgs (Std.TreeSet.ofList ["alice"]) (Std.TreeSet.ofList [0, 2]) == ∅
    | .error _ => false⟩,
  ⟨"Not in gamen-hs, but PaperCorrespondence.hs ~1306–1307 (\"[{bob}]q at state 0\"): \
    preC(control, {bob}, {0,2}) = all four states — bob's move \"q\" lands in {0,2} \
    regardless of alice",
    match controlCgs with
    | .ok cgs => preC cgs (Std.TreeSet.ofList ["bob"]) (Std.TreeSet.ofList [0, 2]) == cgs.cgsStates
    | .error _ => false⟩,
  ⟨"Not in gamen-hs, but PaperCorrespondence.hs ~1319–1322 (\"[{}](p ∧ q) is FALSE\"): \
    preC(control, ∅, {0}) = ∅ — the empty coalition can't out-force two adversaries",
    match controlCgs with
    | .ok cgs => preC cgs ∅ (Std.TreeSet.ofList [0]) == ∅
    | .error _ => false⟩,
  ⟨"Not in gamen-hs, but PaperCorrespondence.hs ~1312–1314 (\"[{alice,bob}](p ∧ q)\"): \
    preC(control, {alice,bob}, {0}) = all four states — the grand coalition has no \
    opponents and can just pick (p, q)",
    match controlCgs with
    | .ok cgs =>
      preC cgs (Std.TreeSet.ofList ["alice", "bob"]) (Std.TreeSet.ofList [0]) == cgs.cgsStates
    | .error _ => false⟩,
  ⟨"Not in gamen-hs: preC(control, {alice}, {1,3}) = ∅ — alice's move alone doesn't decide \
    membership in {1,3} (that also depends on bob's move, which alice doesn't control), \
    unlike {0,1}/{0,2} where one of alice's two moves happens to decide it either way \
    (this fixture is chosen to fail if opponents are computed as the coalition itself \
    instead of its complement, since that bug still gets {0,1}/{0,2} right by accident)",
    match controlCgs with
    | .ok cgs => preC cgs (Std.TreeSet.ofList ["alice"]) (Std.TreeSet.ofList [1, 3]) == ∅
    | .error _ => false⟩,
  ⟨"Not in gamen-hs, but PaperCorrespondence.hs ~1425–1431 (\"sat(⟨⟨alice⟩⟩Xq) = {0,1}\"): \
    preC(loop, {alice}, {1}) = {0,1} — state 0 plays \"next\" into 1, state 1 plays \
    \"stay\" and stays at 1, state 2 has no move into 1",
    match loopCgs with
    | .ok cgs => preC cgs (Std.TreeSet.ofList ["alice"]) (Std.TreeSet.ofList [1]) == Std.TreeSet.ofList [0, 1]
    | .error _ => false⟩,
  ⟨"Not in gamen-hs, but PaperCorrespondence.hs ~1443–1448 (\"sat(⟨⟨alice⟩⟩Xp) = {1,2}\", \
    i.e. preC(loop,{alice},{0}) = {0,2}): state 0 stays at 0, state 2 plays \"next\" into \
    0, state 1 has no move into 0",
    match loopCgs with
    | .ok cgs => preC cgs (Std.TreeSet.ofList ["alice"]) (Std.TreeSet.ofList [0]) == Std.TreeSet.ofList [0, 2]
    | .error _ => false⟩
]

def main : IO UInt32 := do
  let mut failures := 0
  IO.println "Unit cases"
  for c in unitCases ++ tableauCases ++ formulaCases ++ widgetCases ++ answerKeyCases ++ framePropertiesCases
      ++ kripkeCases ++ semanticsCases ++ fragmentCases ++ temporalCases ++ doxasticCases ++ rankingTheoryCases
      ++ plausibilityCases ++ sequentCases ++ rulesCases ++ saturationCases ++ proveCases
      ++ deonticStitCases ++ counterModelCases ++ closureCases ++ crossCheckCases ++ cgsCases do
    IO.println s!"  {if c.ok then "✓" else "✗"} {c.name}"
    unless c.ok do failures := failures + 1
  IO.println "Properties (Plausible; sample size varies by property, see Tests/Main.lean)"
  for (name, prop) in properties do
    let ok ← prop
    IO.println s!"  {if ok then "✓" else "✗"} {name}"
    unless ok do failures := failures + 1
  let total := unitCases.length + tableauCases.length + formulaCases.length + widgetCases.length + answerKeyCases.length
    + framePropertiesCases.length + kripkeCases.length + semanticsCases.length
    + fragmentCases.length + temporalCases.length + doxasticCases.length + rankingTheoryCases.length + plausibilityCases.length
    + sequentCases.length + rulesCases.length + saturationCases.length + proveCases.length
    + deonticStitCases.length + counterModelCases.length + closureCases.length
    + crossCheckCases.length + cgsCases.length + properties.length
  IO.println s!"{total - failures}/{total} passed"
  return if failures == 0 then 0 else 1
