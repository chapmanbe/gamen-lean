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
import Gamen.Coalition
import Gamen.Atl.ModelCheck
import Gamen.Atl
import Gamen.Atel
import Gamen.Atl.ImperfectInfo
import Gamen.Laca
import Gamen.Stit
import Gamen.Xstit
import Gamen.Epistemic
import Gamen.Dcleg
import Gamen.Visualize
import Plausible
import Notebooks.Ch1HealthObligations
import Notebooks.Ch1SyntaxSemantics
import Notebooks.Ch6Countermodels
import Validate.Core
import Tests.PropertyHelpers
import Tests.ManyValued
import Tests.Completion
import Tests.ManyValuedNotebooks
import Tests.ValidateVersion
import Tests.ValidateAtl
import Tests.AtlDynamic
import Tests.ActionModel
import Tests.ValidateEpistemic
import Tests.UpdateSearch
import Tests.SocialLaws
import Tests.ProtocolFlat
import Tests.DclegProofs
import Tests.DclegService

/-!
# Tests

Ports of `test/TableauSpec.hs` in full (`tableauCases`),
`test/FormulaSpec.hs` in full (`formulaCases`; `unitCases` keeps two extra
printing spot-checks that predate `formulaCases` and aren't literal ports
of a Haskell `it`), `test/FramePropertiesSpec.hs`, `test/KripkeSemanticsSpec.hs`,
the "Boxes & Diamonds Ch. 1 (Zach 2019)" block of `test/PaperCorrespondence.hs`
(split between `framePropertiesCases`, for the `isValidOnFrame`-exercising
"Definition 1.11" slice, and `semanticsCases`, for the rest — see
`semanticsCases` for the full list), the `toNNF` properties from
`test/Properties.hs`, run with Plausible instead of QuickCheck, `Gamen.Fragment`
(`test/RegressionIssue18.hs`'s "A2" describe block, plus the fragment-boundary
assertions from `test/Properties.hs`'s "issue #25" `it`, all five steps — see
`fragmentCases`), `test/TemporalSpec.hs` in full plus the `Gamen.Temporal`
blocks of `test/PaperCorrespondence.hs` (`temporalCases`), `Gamen.Kripke`'s "B7: Kripke /
FrameProperties dangling-edge and class fixes" describe block from the
same file (see `kripkeCases`), and `test/StitSpec.hs` in full plus the
"Lorini (2013) — Temporal STIT logic" block of `test/PaperCorrespondence.hs`,
one `test/WorldGuardsSpec.hs` `it`, and the Stit-side `it`s of
`test/RegressionIssue18.hs`'s "B1: unknown agent errors, never vacuous
truth" and "B7: isValidStitFrame enforces Lorini Def. 1 typing" blocks
(`stitCases`/`stitPaperCorrespondenceCases`/`stitRegressionCases`;
`dstit`/`commitment` themselves live in `Gamen.Formula`, already exercised
by `formulaCases`, so this is `Gamen.Stit`'s own model/semantics/
frame-condition coverage), and `test/EpistemicSpec.hs` in full plus the
"B&D Chapter 15 — Epistemic Logics (Zach 2025)" section of
`test/PaperCorrespondence.hs`, its two Doxastic `eSatisfies` blocks, one
`test/WorldGuardsSpec.hs` `it`, the Epistemic-side `it`s of
`test/RegressionIssue18.hs`'s "B1" block, and the two `Gamen.Epistemic`
properties (`epistemicCases`/`epistemicPaperCorrespondenceCases`/
`epistemicRegressionCases`/`doxasticCases`/`properties`). -/
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

/-- `e` succeeded with value `v`; an error fails. Used throughout to
compare `Except`-returning satisfaction functions (`sSatisfies`,
`dsSatisfies`, …) against `.ok v`, so an error fails the case whichever
answer was expected — see the `rankingTheoryCases` docstring below for the
convention this and `isErr` follow. -/
def okIs [BEq α] (e : Except String α) (v : α) : Bool :=
  match e with
  | .ok a => a == v
  | .error _ => false

/-- `e` is an error (Haskell `shouldThrow anyErrorCall`). -/
def isErr (e : Except String α) : Bool :=
  match e with
  | .ok _ => false
  | .error _ => true

/-- The computation errors with exactly `msg`. -/
def errIs {α : Type} (e : Except String α) (msg : String) : Bool :=
  match e with
  | .error m => m == msg
  | .ok _ => false

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

/-- The countermodel view for B&D Example 6.22 (`Notebooks/Ch6Countermodels.lean`). -/
def ex622View : Gamen.Widgets.CountermodelView := Gamen.Widgets.countermodelView systemK [] example622

def ex622Scenario : Gamen.Widgets.Scenario :=
  match ex622View with
  | .countermodel sc _ => sc
  | _ => default

def ex622State : Gamen.Widgets.ExplorerState :=
  { scenario := ex622Scenario, valuation := ex622Scenario.valuation }

/-- Each check evaluated where the widget evaluates it (`evalAt`), on the
widget's current model, as `render` does. -/
def checkResults (st : Gamen.Widgets.ExplorerState) : List (Option Bool) :=
  match st.model with
  | .ok m => st.scenario.checks.map fun c => (satisfies m st.scenario.evalAt c.formula).toOption
  | .error _ => []

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
    (simulateClicks byo0 ["nothing-here"]).valuation == byo0.valuation⟩,
  ⟨"widget: Example 6.22 countermodel: the conclusion's check is ✗ at the root",
    checkResults ex622State == [some false]⟩,
  ⟨"widget: Example 6.22: select q, click 1.2 → the conclusion's check flips to ✓",
    checkResults (simulateClicks ex622State ["atom-1", "world-1.2"]) == [some true]⟩,
  ⟨"widget: Example 6.22: clicking 1.2 twice restores the countermodel",
    checkResults (simulateClicks ex622State ["atom-1", "world-1.2", "world-1.2-label"])
      == [some false]⟩ ]

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
         == "inconsistent: no model satisfies all of them"⟩,
  -- B&D Example 6.22, pp. 111–113 (Figure 6.1), Fall 2025 edition.
  ⟨"ch6 Example 6.22: W = {1, 1.1, 1.2}, R = {⟨1,1.1⟩, ⟨1,1.2⟩}, V(p) = {1.2}, V(q) = {1.1}",
    ex622Scenario.worlds.map (·.1) == ["1", "1.1", "1.2"]
    && ex622Scenario.edges == [("1", "1.1"), ("1", "1.2")]
    && ex622Scenario.valuation == [("p", ["1.2"]), ("q", ["1.1"])]
    && ex622View.summary == "countermodel (open branch 1): W = {1, 1.1, 1.2}; \
         R = {⟨1, 1.1⟩, ⟨1, 1.2⟩}; V(p) = {1.2}; V(q) = {1.1}"⟩,
  ⟨"ch6 exercises: □p → □□p invalid in K (a countermodel), valid in S4; \
    (□p ∨ □q) → □(p ∨ q) valid in K",
    [(Gamen.Widgets.countermodelView systemK [] exercise1).verdict,
     (Gamen.Widgets.countermodelView systemS4 [] exercise2).verdict,
     (Gamen.Widgets.countermodelView systemK [] exercise3).verdict]
      == [some false, some true, some true]
    && exercise2 == ml[ □p → □□p ]⟩,
  ⟨"ch6 exercise 1 hint: the K countermodel is the chain 1 → 1.1 → 1.1.1 with V(p) = {1.1}",
    match Gamen.Widgets.countermodelView systemK [] exercise1 with
    | .countermodel sc _ => sc.edges == [("1", "1.1"), ("1.1", "1.1.1")]
        && sc.valuation == [("p", ["1.1"])]
    | _ => false⟩,
  -- The notebook's reading of the branch: lines 2–11 and the two ∨T splits,
  -- whose other sides close against lines 6 and 8 (B&D pp. 111–112).
  ⟨"ch6 Example 6.22 open branch, line by line",
    Gamen.Widgets.openBranchLines systemK [] example622 == [
      "1. 1 F (□(p ∨ q) → (□p ∨ □q))    (assumption)",
      "2. 1 T □(p ∨ q)    (→F 1)",
      "3. 1 F (□p ∨ □q)    (→F 1)",
      "4. 1 F □p    (∨F 3)",
      "5. 1 F □q    (∨F 3)",
      "6. 1.1 F p    (□F 4)",
      "7. 1.1 T (p ∨ q)    (□T 2)",
      "8. 1.2 F q    (□F 5)",
      "9. 1.2 T (p ∨ q)    (□T 2)",
      "10. 1.1 T q    (∨T 7; the other side, 1.1 T p, closes against line 6)",
      "11. 1.2 T p    (∨T 9; the other side, 1.2 T q, closes against line 8)"]⟩,
  ⟨"ch6 #eval of a verdict shows its summary",
    toString ex622View == ex622View.summary
      && (repr ex622View).pretty == ex622View.summary⟩,
  ⟨"ch6 the unknown verdict with a 3-step budget",
    (Gamen.Widgets.countermodelView systemK [] example622 (maxSteps := 3)).summary
      == "unknown: the tableau ran out of its step budget (3 steps)"⟩,
  ⟨"ch6 exercise feedback: numbered, the hint only after a wrong answer",
    let v := Gamen.Widgets.countermodelView systemK [] exercise1
    Gamen.Widgets.gradeValidity 1 (some false) v "H" == "1. ✓ Correct: not valid."
    && Gamen.Widgets.gradeValidity 1 (some true) v "H" == "1. ✗ Not quite. H"
    && (Gamen.Widgets.gradeValidity 2 none v "H").startsWith "2. Not answered yet"⟩ ]

/-! ## Countermodel view (`Widgets/Countermodel.lean`)

Lean-only (plans/countermodel-explorer-and-k-soundness-2026-09-29.md,
Part A). -/

namespace CountermodelViewTests
open Gamen.Widgets

def view (sys : System) (prem : List Formula) (c : Formula) : CountermodelView :=
  countermodelView sys prem c

def scenarioOf : CountermodelView → Option Scenario
  | .countermodel sc _ => some sc
  | _ => none

def unknownWhy : CountermodelView → String
  | .unknown w => w
  | _ => ""

/-- The scenario's model is the extracted model: same worlds, relation and
valuation. -/
def sameModel (a b : Model) : Bool :=
  a.frame.worlds.toList == b.frame.worlds.toList
    && modelEdges a == modelEdges b && modelValuation a == modelValuation b

def firstExtracted (sys : System) (prem : List Formula) (c : Formula) : Option Model :=
  match buildTableau sys defaultMaxSteps (proofAssumptions prem c) with
  | .stillOpen bs => (firstVerified sys bs).toOption.map (·.1)
  | _ => none

/-- Independent of `edgesClear`: no arrow of a drawn scenario comes within
the world radius (0.42) of the center of a world it does not end at. The
arrow is sampled at 200 points rather than solved in closed form, so a
mistake in `segmentDistance` does not carry over. -/
def noEdgeThroughWorld (sc : Scenario) : Bool :=
  sc.edges.all fun (a, b) => a == b ||
    match sc.worlds.lookup a, sc.worlds.lookup b with
    | some (ax, ay), some (bx, by_) =>
      (List.range 201).all fun k =>
        let t := k.toFloat / 200
        let px := ax + t * (bx - ax)
        let py := ay + t * (by_ - ay)
        sc.worlds.all fun (w, x, y) =>
          w == a || w == b || (px - x) * (px - x) + (py - y) * (py - y) > 0.42 * 0.42
    | _, _ => false

/-- A scenario is acceptable to draw: if `countermodelHtml` would draw it
(`fitsCanvas`), no arrow runs through a world it does not end at. -/
def drawnOK (sc : Scenario) : Bool := !fitsCanvas sc || noEdgeThroughWorld sc

def isChildW (c p : String) : Bool :=
  (prefixPath c).length == (prefixPath p).length + 1 && (prefixPath p).isPrefixOf (prefixPath c)

def isDescW (c p : String) : Bool :=
  (prefixPath c).length > (prefixPath p).length && (prefixPath p).isPrefixOf (prefixPath c)

/-- A synthetic scenario placed by `arrange`, for the canvas limits. Edges:
`mode` 0 is the prefix tree (K), 1 adds self-loops (KT), 2 is the
reflexive, transitive closure (S4). -/
def synth (worlds atoms : List String) (mode : Nat := 1) (checks : List Check := []) :
    Scenario :=
  let es := worlds.flatMap fun a => worlds.filterMap fun b =>
    if (mode == 2 && (isDescW b a || a == b)) || (mode < 2 && isChildW b a)
        || (mode == 1 && a == b) then some (a, b) else none
  arrange
  { title := "", worlds := worlds.map (·, 0, 0), edges := es
    atoms, editable := worlds, evalAt := "1", checks, valuation := atoms.map (·, []) }

/-- Every prefix tree with `n` worlds: world i + 1 picks a parent among the
first i worlds (with repeats up to sibling order). -/
def trees : Nat → List (List String)
  | 0 => [[]]
  | 1 => [["1"]]
  | n + 1 => (trees n).flatMap fun ws => ws.map fun parent =>
      let k := (ws.filter fun w => w.startsWith (parent ++ ".") &&
        !((w.drop (parent.length + 1)).toString.contains '.')).length
      ws ++ [s!"{parent}.{k + 1}"]

def depthAtMost (d : Nat) (ws : List String) : Bool := ws.all fun w => depth w ≤ d

def chain (d : Nat) : List String :=
  (List.range (d + 1)).map fun i => ".".intercalate (List.replicate (i + 1) "1")

def star (n : Nat) : List String := "1" :: (List.range n).map fun i => s!"1.{i + 1}"

def atoms4 : List String := ["p", "q", "r", "s"]

/-- `p ∧ (p ∧ (… ∧ p))` with `n + 1` atoms. -/
def conj : Nat → Formula
  | 0 => p
  | n + 1 => .and p (conj n)

/-- Every countermodel scenario the unit tests draw. -/
def drawnScenarios : List Scenario :=
  [ex622Scenario] ++ ([(systemK, [], ml[ □p → □□p ]), (systemK, [], ml[ □p → p ]),
    (systemS4, [], ml[ ◇p → □◇p ]), (systemS4, [], ml[ □(q → □(q ∨ ¬p)) ]),
    (systemK, [ml[ □p ], ml[ q ]], ml[ □□p ]), (systemKT, [], ml[ ◇p → □◇p ]),
    (systemS4, [], ml[ □(p ∨ q) → (□p ∨ □q) ])].filterMap fun (sys, ps, c) =>
      scenarioOf (view sys ps c))

def cases : List Case := [
  ⟨"countermodelView: the K axiom □(p → q) → (□p → □q) is valid",
    (view systemK [] ml[ □(p → q) → (□p → □q) ]).isValid⟩,
  ⟨"countermodelView: □p → □□p has a countermodel in K and is valid in S4",
    (view systemK [] ml[ □p → □□p ]).isCountermodel
      && (view systemS4 [] ml[ □p → □□p ]).isValid⟩,
  ⟨"countermodelView: □p → p has a countermodel in K with no ⟨1, 1⟩ edge, and is valid in KT",
    (match scenarioOf (view systemK [] ml[ □p → p ]) with
      | some sc => !sc.edges.contains ("1", "1")
      | none => false)
      && (view systemKT [] ml[ □p → p ]).isValid⟩,
  ⟨"countermodelView: a formula outside the Kripke fragment gives .unknown, not an error",
    unknownWhy (view systemK [] (.knowledge "a" p))
      == "extractCountermodel: formula outside the Kripke fragment: K[a]p"⟩,
  ⟨"countermodelView: an exhausted step budget gives .unknown, which is neither valid \
    nor a countermodel",
    let v := countermodelView systemK [] ml[ □(p ∨ q) → □p ∨ □q ] (maxSteps := 2)
    unknownWhy v == "the tableau ran out of its step budget (2 steps)"
      && !v.isValid && !v.isCountermodel && v.verdict == none⟩,
  -- gamen-hs#42 (open): KTB's only open branch for ◇□□¬p fails the
  -- re-check, so there is no verified model to show.
  ⟨"countermodelView: KTB ◇□□¬p: the only open branch fails its re-check → .unknown, no picture",
    (unknownWhy (view systemKB [] ml[ ◇□□¬p ])).startsWith
      "extractCountermodel: extracted model fails to satisfy"
      && openBranchLines systemKB [] ml[ ◇□□¬p ] == []⟩,
  ⟨"firstVerified: an unexpanded (truncated) branch is rejected, not drawn",
    isErr (firstVerified systemK [Branch.ofList [pfFalse .root ml[ p → p ]]])⟩,
  ⟨"firstVerified: skips a failing branch and numbers the one it uses",
    match firstVerified systemK [Branch.ofList [pfFalse .root ml[ p → p ]],
        Branch.ofList [pfFalse .root ml[ p ]]] with
    | .ok (_, i) => i == 2
    | .error _ => false⟩,
  ⟨"countermodelView: the scenario's model is exactly the extracted model \
    (Example 6.22; S4 ◇p → □◇p)",
    [(systemK, ml[ □(p ∨ q) → □p ∨ □q ]), (systemS4, ml[ ◇p → □◇p ])].all fun (sys, c) =>
      match scenarioOf (view sys [] c), firstExtracted sys [] c with
      | some sc, some m => sameModel sc.toModel m
      | _, _ => false⟩,
  ⟨"countermodelView: an S4 countermodel draws the closed relation (reflexive and transitive)",
    match scenarioOf (view systemS4 [] ml[ ◇p → □◇p ]) with
    | some sc => isReflexive sc.toModel.frame && isTransitive sc.toModel.frame
        && sc.edges.contains ("1", "1")
    | none => false⟩,
  ⟨"countermodelView: checks at the root, every world editable, labeled conclusion then premises",
    match scenarioOf (view systemK [ml[ □p ], ml[ q ]] ml[ □□p ]) with
    | some sc => sc.evalAt == "1" && sc.editable == sc.worlds.map (·.1)
        && sc.checks.map (·.label) == ["conclusion", "premise 1", "premise 2"]
        && checkResults { scenario := sc, valuation := sc.valuation }
             == [some false, some true, some true]
    | none => false⟩,
  ⟨"countermodelView: premises that entail the conclusion give .valid",
    (view systemK [ml[ □p ], ml[ □(p → q) ]] ml[ □q ]).isValid⟩,
  ⟨"countermodelView: Example 6.22 fits the canvas",
    fitsCanvas ex622Scenario⟩,
  -- The review's reproduction: unshifted, 1, 1.1, 1.1.1 lie on one line and
  -- the closure edge ⟨1, 1.1.1⟩ runs under world 1.1.
  ⟨"layout: S4 □(q → □(q ∨ ¬p)): the chain is drawn with ⟨1, 1.1.1⟩ clear of world 1.1",
    match scenarioOf (view systemS4 [] ml[ □(q → □(q ∨ ¬p)) ]) with
    | some sc => sc.edges.contains ("1", "1.1.1") && fitsCanvas sc && noEdgeThroughWorld sc
        && !noEdgeThroughWorld { sc with worlds := layout (sc.worlds.map (·.1)) sc.atoms }
    | none => false⟩,
  ⟨"layout: every drawn scenario in these tests has no arrow through another world",
    drawnScenarios.length == 8 && drawnScenarios.all drawnOK⟩,
  ⟨"layout: every prefix tree with ≤ 4 worlds fits with tree edges and loops (K, KT), \
    4 one-letter atoms, and no arrow through a world",
    (List.range 4).all fun n => (trees (n + 1)).all fun ws =>
      let sc := synth ws atoms4
      fitsCanvas sc && noEdgeThroughWorld sc⟩,
  ⟨"layout: every 5-world prefix tree of depth ≤ 2 fits (K, KT), and a root with 5 children",
    (trees 5).all (fun ws => !depthAtMost 2 ws || fitsCanvas (synth ws atoms4))
      && fitsCanvas (synth (star 5) atoms4)⟩,
  ⟨"layout: with the S4 closure, every tree with ≤ 3 worlds and every 4-world tree of \
    depth ≤ 2 fits",
    (List.range 4).all fun n => (trees (n + 1)).all fun ws =>
      (n == 3 && !depthAtMost 2 ws) || fitsCanvas (synth ws atoms4 2)⟩,
  ⟨"layout: no 7-world prefix tree fits with 4 atoms",
    (trees 7).all fun ws => !fitsCanvas (synth ws atoms4)⟩,
  ⟨"layout: depth 4 does not fit (1.1.1.1.1 runs off the canvas)",
    !fitsCanvas (synth (chain 4) ["p"]) && fitsCanvas (synth (chain 3) atoms4)⟩,
  ⟨"layout: 5 atoms do not fit (fact chips); 4 do",
    !fitsCanvas (synth (star 1) (atoms4 ++ ["t"])) && fitsCanvas (synth (star 1) atoms4)⟩,
  ⟨"layout: an atom name of 12 characters fits its chip, 13 do not",
    fitsCanvas (synth (star 1) ["abcdefghijkl"])
      && !fitsCanvas (synth (star 1) ["abcdefghijklm"])⟩,
  ⟨"layout: a check row fits a conclusion of 6 conjoined atoms, not 7 (the SVG draws it)",
    fitsCanvas (synth (star 1) ["p"] 1 [{ label := "conclusion", formula := conj 5 }])
      && !fitsCanvas (synth (star 1) ["p"] 1 [{ label := "conclusion", formula := conj 6 }])⟩,
  ⟨"layout: 6 checks fit (5 premises), 7 do not",
    let c : Check := { label := "c", formula := .bot }
    fitsCanvas (synth (star 2) ["p"] 1 (List.replicate 6 c))
      && !fitsCanvas (synth (star 2) ["p"] 1 (List.replicate 7 c))⟩,
  ⟨"layout: positions stay inside the canvas and at y ≥ 4.9 + 0.3 × atoms, in every \
    layout arrange tries",
    (List.range 6).all fun n => (trees (n + 1)).all fun ws =>
      layoutShifts.all fun (o, b, par) => (layoutWith o b par ws atoms4).all fun (_, x, y) =>
        0 ≤ x && x ≤ 10 && y ≤ 9 && y ≥ bottomRow atoms4 - 1e-9⟩ ]

/-- The property-test invariant for one system, premise and conclusion: a
countermodel refutes the conclusion where the widget evaluates it (the
root), satisfies the premise there, lies inside the canvas at
y ≥ 4.9 + 0.3 × atoms, and, if drawn, has no arrow through a world it does
not end at; `.valid` means `tableauProves` proved it. -/
def viewOK (sys : System) (prem conc : Formula) : Bool :=
  match countermodelView sys [prem] conc with
  | .valid => tableauProves sys defaultMaxSteps [prem] conc == .definitely true
  | .unknown _ => true
  | .countermodel sc _ =>
    sc.evalAt == "1"
      && okIs (satisfies sc.toModel sc.evalAt conc) false
      && okIs (satisfies sc.toModel "1" prem) true
      && (sc.worlds.all fun (_, x, y) =>
           0 ≤ x && x ≤ 10 && y ≤ 9 && y ≥ bottomRow sc.atoms - 1e-9)
      && drawnOK sc

end CountermodelViewTests

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

/-! ## Stit (`Gamen.Stit`)

Port of `test/StitSpec.hs` in full (all 21 `it`s), the "Lorini (2013) —
Temporal STIT logic" describe block of `test/PaperCorrespondence.hs` (all
15 `it`s — the only such block Stit unblocks; every other block mentioning
`Stit`/`ChoiceDiamond`/`GroupStit` is inside a DeonticStit fixture and
already ported in `deonticStitCases`/`counterModelCases`), and one `it`
from `test/WorldGuardsSpec.hs`'s "World-existence guards (gamen-hs#7)"
block ("sSatisfies errors on world not in StitModel") that this port
unblocks — its siblings (`eSatisfies`/`xSatisfies`/`lSatisfies`) still need
`Gamen.Epistemic`/`.Xstit`/`.Laca`.

`agentAccessible`/`choiceCell` and `sSatisfies`/`sIsTrueIn` return
`Except`; results are compared with `okIs`/`isErr` or, for `Except (Std.
TreeSet World)`, `okIs` again (it needs only `BEq`), never unwrapped. -/

/-- StitSpec.hs's shared fixture: a single moment `{w1, w2}`. Agent "a"
distinguishes w1 from w2 (choice cells `{w1}`, `{w2}`); agent "b" is
trivial (one cell `{w1, w2}`). No future (R_G = ∅). -/
def stitFrame : StitFrame :=
  mkStitFrame ["w1", "w2"]
    [("w1", "w1"), ("w1", "w2"), ("w2", "w1"), ("w2", "w2")]
    [ ("a", [("w1", "w1"), ("w2", "w2")])
    , ("b", [("w1", "w1"), ("w1", "w2"), ("w2", "w1"), ("w2", "w2")]) ]
    []

def stitModel : StitModel :=
  mkStitModel stitFrame [("p", ["w1"]), ("q", ["w2"])]

def stitCases : List Case := [
  -- describe "STIT formula construction"
  ⟨"displays Stit, ChoiceDiamond, GroupStit",
    toString (Formula.stit "i" p) == "[i]p"
    && toString (Formula.choiceDiamond "i" p) == "<i>p"
    && toString (Formula.groupStit p) == "[Agt]p"⟩,
  ⟨"STIT formulas are not modal-free",
    !(Formula.stit "i" p).isModalFree
    && !(Formula.choiceDiamond "i" p).isModalFree
    && !(Formula.groupStit p).isModalFree⟩,
  ⟨"collects atoms from STIT formulas",
    (Formula.stit "i" (.implies p q)).atoms.toList == [(⟨"p"⟩ : Atom), ⟨"q"⟩]
    && (Formula.choiceDiamond "i" p).atoms.toList == [(⟨"p"⟩ : Atom)]
    && (Formula.groupStit p).atoms.toList == [(⟨"p"⟩ : Atom)]⟩,
  ⟨"dstit smart constructor uses Box for settledness",
    Formula.dstit "i" p == .and (.stit "i" p) (.not (.box p))⟩,
  -- describe "STIT model construction"
  ⟨"builds frame with correct worlds", stitFrame.sWorlds.size == 2⟩,
  ⟨"auto-computes R_Agt as intersection of R_i",
    sAccessible stitFrame.rGrandCoal "w1" == Std.TreeSet.ofList ["w1"]
    && sAccessible stitFrame.rGrandCoal "w2" == Std.TreeSet.ofList ["w2"]⟩,
  ⟨"moment returns R_□ equivalence class",
    moment stitFrame "w1" == Std.TreeSet.ofList ["w1", "w2"]⟩,
  ⟨"choiceCell returns R_i equivalence class",
    okIs (choiceCell stitFrame "a" "w1") (Std.TreeSet.ofList ["w1"])
    && okIs (choiceCell stitFrame "a" "w2") (Std.TreeSet.ofList ["w2"])
    && okIs (choiceCell stitFrame "b" "w1") (Std.TreeSet.ofList ["w1", "w2"])⟩,
  -- describe "STIT satisfaction"
  ⟨"evaluates [i]phi (agent stit)",
    okIs (sSatisfies stitModel "w1" (.stit "a" p)) true
    && okIs (sSatisfies stitModel "w2" (.stit "a" p)) false
    && okIs (sSatisfies stitModel "w1" (.stit "b" p)) false⟩,
  ⟨"evaluates [Agt]phi (grand coalition stit)",
    okIs (sSatisfies stitModel "w1" (.groupStit p)) true
    && okIs (sSatisfies stitModel "w2" (.groupStit p)) false⟩,
  ⟨"evaluates □phi (historical necessity, was Settled)",
    okIs (sSatisfies stitModel "w1" (.box p)) false
    && okIs (sSatisfies stitModel "w1" (.box (.or p q))) true⟩,
  ⟨"evaluates ◇phi (historical possibility)",
    okIs (sSatisfies stitModel "w1" (.diamond p)) true⟩,
  ⟨"evaluates <i>phi (choice diamond, dual of [i])",
    okIs (sSatisfies stitModel "w1" (.choiceDiamond "a" p)) true
    && okIs (sSatisfies stitModel "w2" (.choiceDiamond "a" p)) false
    && okIs (sSatisfies stitModel "w1" (.choiceDiamond "b" p)) true⟩,
  ⟨"evaluates deliberative stit",
    okIs (sSatisfies stitModel "w1" (Formula.dstit "a" p)) true
    && okIs (sSatisfies stitModel "w1" (Formula.dstit "a" (.or p q))) false⟩,
  ⟨"evaluates temporal operators (vacuous with no future)",
    okIs (sSatisfies stitModel "w1" (.futureBox p)) true
    && okIs (sSatisfies stitModel "w1" (.futureDiamond p)) false⟩,
  -- describe "STIT frame constraint checking"
  ⟨"valid frame passes all constraints", isValidStitFrame stitFrame == true⟩,
  ⟨"C1: R_i must be subset of R_□",
    checkC1 stitFrame == true
    -- A frame where agent sees across moments fails C1
    && checkC1 (mkStitFrame ["w1", "w2"]
          [("w1", "w1"), ("w2", "w2")]
          [("a", [("w1", "w1"), ("w1", "w2"), ("w2", "w1"), ("w2", "w2")])]
          []) == false⟩,
  ⟨"C2: independence of agents", checkC2 stitFrame == true⟩,
  ⟨"C3: R_Agt is intersection of R_i", checkC3 stitFrame == true⟩,
  ⟨"C7: R_G irreflexive within R_□ classes",
    checkC7 stitFrame == true
    -- A frame with future within the same moment would fail
    && checkC7 (mkStitFrame ["w1", "w2"]
          [("w1", "w1"), ("w1", "w2"), ("w2", "w1"), ("w2", "w2")]
          []
          [("w1", "w2")]) == false⟩,
  ⟨"sIsTrueIn checks all worlds",
    okIs (sIsTrueIn stitModel (.or p q)) true
    && okIs (sIsTrueIn stitModel p) false⟩,
  -- WorldGuardsSpec.hs:29, "sSatisfies errors on world not in StitModel"
  -- (gamen-hs#7).
  ⟨"sSatisfies errors on world not in StitModel",
    let sfr := mkStitFrame ["a", "b"] [("a", "a"), ("a", "b"), ("b", "b")]
      [("ag", [("a", "a"), ("b", "b")])] []
    let sm := mkStitModel sfr [("p", ["a", "b"]), ("q", ["b"]), ("r", ["a"])]
    let probeFormula : Formula :=
      .implies (.or (.atom "p") (.atom "q")) (.and (.not (.atom "q")) (.atom "r"))
    okIs (sSatisfies sm "a" probeFormula) true
      && isErr (sSatisfies sm "c" probeFormula)⟩
]

/-! ### Lorini (2013) — Temporal STIT logic (`test/PaperCorrespondence.hs`)

The only `PaperCorrespondence.hs` describe block Stit unblocks: "Lorini
(2013) — Temporal STIT logic", Definition 1 (pp. 373–374) and Example 5
(p. 376), all 15 `it`s. -/

/-- Definition 1 (Lorini 2013, pp. 373–374): minimal two-world T-STIT
frame. W = {w1,w2}, one moment {w1,w2}. Agent "a": one big choice {w1,w2}.
Agent "b": two singleton choices. R_G = ∅ (no temporal structure needed for
C1–C7 / semantic tests). -/
def miniStitFrame : StitFrame :=
  mkStitFrame ["w1", "w2"]
    [("w1", "w1"), ("w1", "w2"), ("w2", "w1"), ("w2", "w2")]
    [ ("a", [("w1", "w1"), ("w1", "w2"), ("w2", "w1"), ("w2", "w2")])
    , ("b", [("w1", "w1"), ("w2", "w2")]) ]
    []

def miniStitModel : StitModel :=
  mkStitModel miniStitFrame [("p", ["w1"])]

/-- Frame violating C1: agent "a"'s choice spans two singleton moments. -/
def c1ViolFrame : StitFrame :=
  mkStitFrame ["w1", "w2"]
    [("w1", "w1"), ("w2", "w2")]
    [("a", [("w1", "w1"), ("w1", "w2"), ("w2", "w1"), ("w2", "w2")])]
    []

/-- Frame violating C7: w2 is in the same moment as w1 yet also in
R_G(w1). -/
def c7ViolFrame : StitFrame :=
  mkStitFrame ["w1", "w2"]
    [("w1", "w1"), ("w1", "w2"), ("w2", "w1"), ("w2", "w2")]
    [("a", [("w1", "w1"), ("w1", "w2"), ("w2", "w1"), ("w2", "w2")])]
    [("w1", "w2")]

def stitPaperCorrespondenceCases : List Case := [
  -- describe "Definition 1 (pp. 373–374): T-STIT frame constraints C1–C7"
  ⟨"C1 (p. 373): checkC1 miniStitFrame = True — every R_i is a subset of R_□",
    checkC1 miniStitFrame == true⟩,
  ⟨"C1 violated: checkC1 c1ViolFrame = False — agent choice spans two singleton moments",
    checkC1 c1ViolFrame == false⟩,
  ⟨"C2 (p. 374): checkC2 miniStitFrame = True — cross-agent choice selections have nonempty intersection",
    checkC2 miniStitFrame == true⟩,
  ⟨"C3 (p. 374): checkC3 miniStitFrame = True — R_Agt equals pointwise intersection of R_i",
    checkC3 miniStitFrame == true⟩,
  ⟨"C7 (p. 374): checkC7 miniStitFrame = True — no world in the moment is in its R_G future",
    checkC7 miniStitFrame == true⟩,
  ⟨"C7 violated: checkC7 c7ViolFrame = False — w2 ∈ R_□(w1) yet w2 ∈ R_G(w1)",
    checkC7 c7ViolFrame == false⟩,
  ⟨"isValidStitFrame miniStitFrame = True — satisfies all C1–C7",
    isValidStitFrame miniStitFrame == true⟩,
  ⟨"isValidStitFrame c1ViolFrame = False — fails C1",
    isValidStitFrame c1ViolFrame == false⟩,
  -- describe "Definition 1 (p. 373): moment and choice-cell accessors"
  ⟨"moment w1 = {w1,w2}: both worlds share the same R_□ equivalence class",
    moment miniStitFrame "w1" == Std.TreeSet.ofList ["w1", "w2"]⟩,
  ⟨"choiceCell b w1 = {w1}: agent b has a singleton choice at w1",
    okIs (choiceCell miniStitFrame "b" "w1") (Std.TreeSet.ofList ["w1"])⟩,
  -- describe "Example 5 (p. 376): semantics of [i]φ, □φ, ⟨Agt⟩φ, ⟨i⟩φ"
  ⟨"[b stit]p = True at w1: b's choice cell {w1} ⊆ V(p)",
    okIs (sSatisfies miniStitModel "w1" (.stit "b" p)) true⟩,
  ⟨"[a stit]p = False at w1: a's choice {w1,w2} includes w2 ∉ V(p)",
    okIs (sSatisfies miniStitModel "w1" (.stit "a" p)) false⟩,
  ⟨"□p = False at w1: moment {w1,w2} includes w2 ∉ V(p)",
    okIs (sSatisfies miniStitModel "w1" (.box p)) false⟩,
  ⟨"[Agt stit]p = True at w1: grand coalition cell {w1} ⊆ V(p)",
    okIs (sSatisfies miniStitModel "w1" (.groupStit p)) true⟩,
  ⟨"⟨a⟩p = True at w1: a's choice {w1,w2} contains w1 ∈ V(p)",
    okIs (sSatisfies miniStitModel "w1" (.choiceDiamond "a" p)) true⟩
]

/-! ### RegressionIssue18.hs: Stit-side "B1" and "B7" blocks

Both unblocked by this port:

* "B1: unknown agent errors, never vacuous truth" — the two `Stit: …` `it`s
  (the two `Epistemic: …` sibling `it`s need `Gamen.Epistemic`, not yet
  ported).
* "B7: isValidStitFrame enforces Lorini Def. 1 typing" — all 3 `it`s.
  `checkTyping` presupposes typing (R_□, each R_i, and R_Agt are
  equivalence relations; R_G is transitive) that C1–C7 alone don't enforce;
  before `checkTyping` existed, the C1–C7-only validator wrongly accepted a
  frame with a non-transitive R_G. -/

def stitRegressionCases : List Case :=
  -- B1 fixture: a single reflexive world, one agent "a" whose relation is
  -- the identity.
  let b1Model := mkStitModel (mkStitFrame ["w"] [("w", "w")] [("a", [("w", "w")])] [])
    [("p", ["w"])]
  -- B7 fixture: three singleton moments with a non-transitive R_G
  -- (w1→w2, w2→w3, but NOT w1→w3). This satisfies every interaction
  -- constraint C1–C7, yet R_G is not transitive, so the frame is not a
  -- T-STIT frame.
  let ntFrame := mkStitFrame ["w1", "w2", "w3"]
    [("w1", "w1"), ("w2", "w2"), ("w3", "w3")]
    [("a", [("w1", "w1"), ("w2", "w2"), ("w3", "w3")])]
    [("w1", "w2"), ("w2", "w3")]
  [ ⟨"Stit: a known agent evaluates normally", okIs (sSatisfies b1Model "w" (.stit "a" p)) true⟩,
    ⟨"Stit: [typo]⊥ errors (not vacuously true)", isErr (sSatisfies b1Model "w" (.stit "typo" .bot))⟩,
    ⟨"the frame still satisfies C1 and C7", checkC1 ntFrame == true && checkC7 ntFrame == true⟩,
    ⟨"checkTyping rejects the non-transitive R_G", checkTyping ntFrame == false⟩,
    ⟨"isValidStitFrame now rejects it (was accepted under C1–C7 only)",
      isValidStitFrame ntFrame == false⟩ ]

/-! ## Xstit (`Gamen.Xstit`)

Port of `test/XstitSpec.hs` in full (all 19 `it`s) plus `test/WorldGuardsSpec.hs`'s
"xSatisfies errors on world not in XstitModel" `it` (`xstitCases`); the
"Broersen (2011) — Epistemic deontic XSTIT" block of
`test/PaperCorrespondence.hs` (all 34 `it`s, `xstitPaperCorrespondenceCases`);
and `test/RegressionIssue18.hs`'s "B7: mkXstitFrame rejects a non-functional
R_X" block (both `it`s, `xstitRegressionCases`).

`mkXstitFrame` returns `Except`, so every fixture is an `Except String
XstitFrame`/`XstitModel`; `xSat`/`xFr` bind through it, so an error in the
fixture or in the check fails the case whichever answer was expected. -/

/-- `xSatisfies` through an `Except` model. -/
def xSat (em : Except String XstitModel) (w : World) (f : Formula) : Except String Bool :=
  em >>= fun m => xSatisfies m w f

/-- A pure frame check through an `Except` frame. -/
def xFr (ef : Except String XstitFrame) (check : XstitFrame → Bool) : Except String Bool :=
  check <$> ef

/-- XstitSpec.hs's clinical prescribing scenario: 4 worlds, 2 moments × 2
histories. The clinician "c" chooses between safe (h1) and unsafe (h2)
medication but cannot tell the histories apart at moment 0. -/
def xFrame' : Except String XstitFrame :=
  mkXstitFrame
    ["s0_h1", "s0_h2", "s1_h1", "s1_h2"]
    -- R_X: deterministic next-state
    [ ("s0_h1", "s1_h1"), ("s0_h2", "s1_h2")
    , ("s1_h1", "s1_h1"), ("s1_h2", "s1_h2") ]  -- terminal loops
    -- R_□: settledness (equivalence classes = moments)
    [ ("s0_h1", "s0_h1"), ("s0_h1", "s0_h2")
    , ("s0_h2", "s0_h1"), ("s0_h2", "s0_h2")
    , ("s1_h1", "s1_h1"), ("s1_h1", "s1_h2")
    , ("s1_h2", "s1_h1"), ("s1_h2", "s1_h2") ]
    -- R_[c]: each world is its own cell at both moments
    [ ("c", [ ("s0_h1", "s0_h1"), ("s0_h2", "s0_h2")
            , ("s1_h1", "s1_h1"), ("s1_h2", "s1_h2") ]) ]
    -- R_{K_c}: can't distinguish at moment 0
    [ ("c", [ ("s0_h1", "s0_h1"), ("s0_h1", "s0_h2")
            , ("s0_h2", "s0_h1"), ("s0_h2", "s0_h2")
            , ("s1_h1", "s1_h1"), ("s1_h2", "s1_h2") ]) ]

def xModel' : Except String XstitModel :=
  xFrame'.map fun fr => mkXstitModel fr
    [ ("safe_med", ["s1_h1"])
    , ("unsafe_med", ["s1_h2"])
    , ("allergy_known", ["s0_h1"])
    , ("v_c", ["s1_h2"]) ]  -- violation when unsafe med prescribed

def safeMed : Formula := .atom "safe_med"
def unsafeMed : Formula := .atom "unsafe_med"

def xstitCases : List Case := [
  -- describe "XSTIT frame conditions (Broersen 2011, Definition 3.1)"
  -- (sic: frames are Definitions 2.2 + 3.2; 3.1 is the language)
  ⟨"valid frame passes all conditions", okIs (xFr xFrame' isValidXstitFrame) true⟩,
  ⟨"XC1: R_X is serial", okIs (xFr xFrame' checkXC1) true⟩,
  ⟨"XC2: R_□ is an equivalence relation", okIs (xFr xFrame' checkXC2) true⟩,
  ⟨"XC3: R_[A] are equivalence relations", okIs (xFr xFrame' checkXC3) true⟩,
  ⟨"XC4: R_[A] refines R_□", okIs (xFr xFrame' checkXC4) true⟩,
  ⟨"XC5: independence of agents", okIs (xFr xFrame' checkXC5) true⟩,
  ⟨"XC6: R_{K_a} are equivalence relations", okIs (xFr xFrame' checkXC6) true⟩,
  -- describe "XSTIT satisfaction (Broersen 2011, Definition 3.2)"
  -- (sic: truth is Definitions 2.4 + 3.3)
  ⟨"evaluates Next (next-state)",
    okIs (xSat xModel' "s0_h1" (.next safeMed)) true
    && okIs (xSat xModel' "s0_h2" (.next unsafeMed)) true
    && okIs (xSat xModel' "s0_h2" (.next safeMed)) false⟩,
  ⟨"evaluates □ (historical necessity, was Settled)",
    okIs (xSat xModel' "s1_h1" (.box safeMed)) false
    && okIs (xSat xModel' "s1_h1" (.box (.or safeMed unsafeMed))) true⟩,
  ⟨"evaluates [a xstit]phi (choice guarantees at next state)",
    okIs (xSat xModel' "s0_h1" (.stit "c" safeMed)) true
    && okIs (xSat xModel' "s0_h2" (.stit "c" safeMed)) false
    && okIs (xSat xModel' "s0_h2" (.stit "c" unsafeMed)) true⟩,
  ⟨"evaluates K_a phi (epistemic knowledge)",
    okIs (xSat xModel' "s0_h1" (.knowledge "c" (.atom "allergy_known"))) false
    && okIs (xSat xModel' "s1_h1" (.knowledge "c" safeMed)) true⟩,
  ⟨"clinician does NOT know they see to safe_med (epistemic uncertainty)",
    okIs (xSat xModel' "s0_h1" (knowingly "c" safeMed)) false⟩,
  -- describe "XSTIT obligation and mens rea (Broersen 2011, Section 5)"
  ⟨"evaluates Ought via violation constants",
    okIs (xSat xModel' "s0_h1" (.ought "c" safeMed)) true⟩,
  ⟨"evaluates Permitted",
    okIs (xSat xModel' "s0_h1" (.permitted "c" safeMed)) true⟩,
  ⟨"strict liability at s0_h2",
    okIs (xSat xModel' "s0_h2" (strictLiability "c" safeMed)) true
    && okIs (xSat xModel' "s0_h1" (strictLiability "c" safeMed)) false⟩,
  ⟨"mens rea classification",
    okIs ((xModel' >>= fun m => mensReaCheck m "s0_h2" "c" safeMed).map
      (·.contains .mrStrictLiability)) true
    && okIs (xModel' >>= fun m => mensReaCheck m "s0_h1" "c" safeMed) []⟩,
  -- describe "XSTIT application functions"
  ⟨"duty check identifies obligations",
    okIs (xModel' >>= fun m => xDutyCheck m "s0_h1" "c" [safeMed, unsafeMed]) [safeMed]⟩,
  ⟨"knowledge check identifies known facts",
    okIs (xModel' >>= fun m => xKnowledgeCheck m "s1_h1" "c" [safeMed, unsafeMed]) [safeMed]⟩,
  ⟨"epistemic duty check: clinician knows obligation but not compliance",
    okIs (xModel' >>= fun m => xEpistemicDutyCheck m "s0_h1" "c" [safeMed, unsafeMed])
      [(safeMed, true)]⟩,
  -- WorldGuardsSpec.hs:43, "xSatisfies errors on world not in XstitModel"
  -- (gamen-hs#7).
  ⟨"xSatisfies errors on world not in XstitModel",
    let xm := (mkXstitFrame ["a", "b"] [("a", "b"), ("b", "b")]
      [("a", "a"), ("b", "b")]
      [("ag", [("a", "a"), ("b", "b")])]
      [("ag", [("a", "a"), ("b", "b")])]).map fun xfr =>
        mkXstitModel xfr [("p", ["a", "b"]), ("q", ["b"]), ("r", ["a"])]
    let probeFormula : Formula :=
      .implies (.or (.atom "p") (.atom "q")) (.and (.not (.atom "q")) (.atom "r"))
    okIs (xSat xm "a" probeFormula) true
      && isErr (xSat xm "c" probeFormula)⟩
]

/-! ### Broersen (2011) — Epistemic deontic XSTIT (`test/PaperCorrespondence.hs`)

All 34 `it`s. Two citations in the describe titles are corrected here
against `notes/Broersen2011.pdf`: Definition 3.3 is on p. 145 (the Haskell
says 144), and "Knowingly (Def. 3.3/5.2)" is introduced after Definition
3.3 on p. 145 — Definition 5.2 is a weaker obligation. -/

/-- 4-world fixture: moment 1 = {w0,w1}, where agent "a" chooses w0 (next
w2, p true) or w1 (next w3, v_a true); moment 2 = {w2,w3}, terminal. Unit
epistemic cells: the agent knows the actual world. -/
def xstitFr : Except String XstitFrame :=
  mkXstitFrame
    ["w0", "w1", "w2", "w3"]
    -- R_X: serial, deterministic next-state
    [("w0", "w2"), ("w1", "w3"), ("w2", "w2"), ("w3", "w3")]
    -- R_□: two moments {w0,w1} and {w2,w3}
    [ ("w0", "w0"), ("w0", "w1"), ("w1", "w0"), ("w1", "w1")
    , ("w2", "w2"), ("w2", "w3"), ("w3", "w2"), ("w3", "w3") ]
    -- R_[a]: fine choices in moment 1 (singletons); whole moment in moment 2
    [("a", [ ("w0", "w0"), ("w1", "w1")
           , ("w2", "w2"), ("w2", "w3"), ("w3", "w2"), ("w3", "w3") ])]
    -- R_{K_a}: unit equivalence classes
    [("a", [("w0", "w0"), ("w1", "w1"), ("w2", "w2"), ("w3", "w3")])]

def xstitM : Except String XstitModel :=
  xstitFr.map fun fr => mkXstitModel fr [("p", ["w2"]), ("v_a", ["w3"])]

/-- `mensReaCheck xstitM w "a" p` contains `mr`. -/
def xMensReaHas (w : World) (mr : MensRea) : Except String Bool :=
  (xstitM >>= fun m => mensReaCheck m w "a" p).map (·.contains mr)

def xstitPaperCorrespondenceCases : List Case := [
  -- describe "Definitions 2.2 (p. 140) + 3.2 (p. 144): frame conditions XC1–XC6"
  ⟨"isValidXstitFrame xstitFr — all XC1–XC6 hold", okIs (xFr xstitFr isValidXstitFrame) true⟩,
  ⟨"XC1 (Def. 2.2, p. 140): R_X is serial — every world has a next state",
    okIs (xFr xstitFr checkXC1) true⟩,
  ⟨"XC2 (Def. 2.2, p. 140): R_□ is an equivalence relation (historical necessity)",
    okIs (xFr xstitFr checkXC2) true⟩,
  ⟨"XC3 (Def. 2.2, p. 140): each R_[A] is an equivalence relation (choice effectivity)",
    okIs (xFr xstitFr checkXC3) true⟩,
  ⟨"XC4 (Def. 2.2, p. 140): R_[A](w) ⊆ R_□(w) — choice cells refine historical necessity",
    okIs (xFr xstitFr checkXC4) true⟩,
  ⟨"XC5 (Def. 2.2, p. 140): Indep-G — joint choices of disjoint groups always intersect",
    okIs (xFr xstitFr checkXC5) true⟩,
  ⟨"XC6 (Def. 3.2, p. 144): each R_{K_a} is an equivalence relation (epistemic)",
    okIs (xFr xstitFr checkXC6) true⟩,
  ⟨"frame with no R_X entries violates XC1 (not serial)",
    okIs (xFr (mkXstitFrame ["w0", "w1"] [] [] [] []) checkXC1) false⟩,
  -- describe "Definitions 2.4 + 3.3 (pp. 142, 145): truth conditions — X, □, [a xstit], K_a"
  -- (Haskell: "pp. 142, 144"; Definition 3.3 is on p. 145)
  ⟨"p = False at w0 (pre-action moment; V(p) = {w2})", okIs (xSat xstitM "w0" p) false⟩,
  ⟨"p = True at w2 (good-outcome world; w2 ∈ V(p))", okIs (xSat xstitM "w2" p) true⟩,
  ⟨"Xp true at w0: R_X(w0)=w2, p holds at w2  (Definition 2.4, Xφ clause)",
    okIs (xSat xstitM "w0" (.next p)) true⟩,
  ⟨"Xp false at w1: R_X(w1)=w3, p does not hold at w3", okIs (xSat xstitM "w1" (.next p)) false⟩,
  ⟨"[a xstit]p true at w0: R_[a](w0)={w0}, next(w0)=w2, p at w2  (Definition 2.4, [A xstit] clause)",
    okIs (xSat xstitM "w0" (.stit "a" p)) true⟩,
  ⟨"[a xstit]p false at w1: R_[a](w1)={w1}, next(w1)=w3, p not at w3",
    okIs (xSat xstitM "w1" (.stit "a" p)) false⟩,
  ⟨"K_a p false at w0: R_{K_a}(w0)={w0}, p not at w0  (Definition 3.3, K_a clause)",
    okIs (xSat xstitM "w0" (.knowledge "a" p)) false⟩,
  ⟨"K_a p true at w2: R_{K_a}(w2)={w2}, p at w2", okIs (xSat xstitM "w2" (.knowledge "a" p)) true⟩,
  ⟨"K_a[a xstit]p true at w0: agent knows they see to p (unit epistemic cell, correct choice)",
    okIs (xSat xstitM "w0" (.knowledge "a" (.stit "a" p))) true⟩,
  ⟨"K_a[a xstit]p false at w1: agent knows they do NOT see to p",
    okIs (xSat xstitM "w1" (.knowledge "a" (.stit "a" p))) false⟩,
  -- describe "Definition 5.1 (p. 147): O[a xstit]φ = □(¬[a xstit]φ → [a xstit]V)"
  ⟨"violationAtom 'a' = Atom 'v_a'  (Anderson-style, p. 147)", violationAtom "a" == .atom "v_a"⟩,
  ⟨"O[a xstit]p holds at w0: settled cell {w0,w1} — w1 branch fails p → triggers v_a",
    okIs (xSat xstitM "w0" (.ought "a" p)) true⟩,
  ⟨"O[a xstit]p also holds at w1 (same settled cell, same obligation)",
    okIs (xSat xstitM "w1" (.ought "a" p)) true⟩,
  ⟨"O[a xstit](¬p) is false at w0: w0 branch fails ¬p but v_a not triggered at w2",
    okIs (xSat xstitM "w0" (.ought "a" (.not p))) false⟩,
  -- describe "Definitions 5.1-5.3 (pp. 147–148): derived mens rea operators"
  ⟨"strictLiability a p false at w0: agent IS seeing to p (obligation but no breach)",
    okIs (xSat xstitM "w0" (strictLiability "a" p)) false⟩,
  ⟨"strictLiability a p true at w1: obligated, agent does NOT see to p",
    okIs (xSat xstitM "w1" (strictLiability "a" p)) true⟩,
  ⟨"knowingly a p true at w0: K_a([a xstit]p) — agent knows they see to p",
    okIs (xSat xstitM "w0" (knowingly "a" p)) true⟩,
  ⟨"knowingly a p false at w1: agent knows they do not see to p",
    okIs (xSat xstitM "w1" (knowingly "a" p)) false⟩,
  ⟨"obligatedKnowingly a p true at w0: obligated AND K_a[a xstit]p",
    okIs (xSat xstitM "w0" (obligatedKnowingly "a" p)) true⟩,
  ⟨"obligatedKnowingly a p false at w1: obligated but agent does not knowingly see to p",
    okIs (xSat xstitM "w1" (obligatedKnowingly "a" p)) false⟩,
  ⟨"mensReaCheck at w0: MRKnowing applies — agent knowingly fulfils obligation",
    okIs (xMensReaHas "w0" .mrKnowing) true⟩,
  ⟨"mensReaCheck at w0: MRStrictLiability does not apply — agent sees to p",
    okIs (xMensReaHas "w0" .mrStrictLiability) false⟩,
  ⟨"mensReaCheck at w1: MRStrictLiability applies — obligated but fails to see to p",
    okIs (xMensReaHas "w1" .mrStrictLiability) true⟩,
  ⟨"mensReaCheck at w1: MRKnowing does not apply — agent doesn't see to p",
    okIs (xMensReaHas "w1" .mrKnowing) false⟩,
  -- describe "Application functions (Gamen.Xstit module): duty and epistemic duty checks"
  ⟨"xDutyCheck at w0: agent is obligated to see to p but not ¬p",
    okIs (xstitM >>= fun m => xDutyCheck m "w0" "a" [p, .not p]) [p]⟩,
  ⟨"xEpistemicDutyCheck at w0: agent knows their obligation to see to p",
    okIs ((xstitM >>= fun m => xEpistemicDutyCheck m "w0" "a" [p]).map (·.map (·.2))) [true]⟩
]

/-! ### RegressionIssue18.hs: "B7: mkXstitFrame rejects a non-functional R_X" -/

def xstitRegressionCases : List Case := [
  ⟨"a world with two next-states errors (was silently repaired)",
    isErr (mkXstitFrame ["w0", "w1", "w2"] [("w0", "w1"), ("w0", "w2")] [] [] [])⟩,
  ⟨"a functional R_X builds normally",
    match mkXstitFrame ["w0", "w1"] [("w0", "w1"), ("w1", "w1")] [] [] [] with
    | .ok _ => true
    | .error _ => false⟩
]

/-! ## Epistemic (`Gamen.Epistemic`)

Port of `test/EpistemicSpec.hs` in full (all 23 `it`s) plus
`test/WorldGuardsSpec.hs`'s "eSatisfies errors on world not in
EpistemicModel" `it` (`epistemicCases`); the "B&D Chapter 15 — Epistemic
Logics (Zach 2025)" section of `test/PaperCorrespondence.hs` (all 15 `it`s,
`epistemicPaperCorrespondenceCases`); and the two `Epistemic: …` `it`s of
`test/RegressionIssue18.hs`'s "B1: unknown agent errors, never vacuous
truth" block (`epistemicRegressionCases`). The two Doxastic
PaperCorrespondence blocks that exercise `eSatisfies` live in
`doxasticCases`, next to their sibling tableau block. The two
`Gamen.Epistemic` properties of `test/Properties.hs` are in `properties`.

Every B&D number in the Haskell test titles (Definitions 15.2–15.7,
Theorem 15.8, Definition 15.11, Table 15.1, Figures 15.2–15.3, and their
pages) was checked against `notes/bd-screen.pdf` and is correct.

`eSatisfies`, `eAccessible`, `restrictModel`, and the bisimulation
functions return `Except`; every case compares against `.ok v` (`okIs`),
so an error fails the case whichever answer was expected. -/

/-- `Set.member v (eAccessible fr a w)`, through the `Except`. -/
def accHas (fr : EpistemicFrame) (a : String) (w v : World) : Except String Bool :=
  (eAccessible fr a w).map (·.contains v)

-- EpistemicSpec.hs "EpistemicFrame construction and accessible (Definition 15.4)"
def eSpecFr1 : EpistemicFrame := mkEpistemicFrame ["w1", "w2", "w3"]
  [ ("a", [("w1", "w2"), ("w2", "w2")])
  , ("b", [("w1", "w1"), ("w1", "w3"), ("w3", "w3")]) ]

-- "Epistemic truth conditions (Definition 15.5)"
def eSpecM2 : EpistemicModel :=
  mkEpistemicModel
    (mkEpistemicFrame ["w1", "w2", "w3"]
      [ ("a", [("w1", "w2"), ("w2", "w2"), ("w3", "w3")])
      , ("b", [("w1", "w3"), ("w2", "w2"), ("w3", "w3")]) ])
    [("p", ["w1", "w2"]), ("q", ["w2"])]

-- "Group and common knowledge (Definition 15.3, 15.6)"
def eSpecM3 : EpistemicModel :=
  mkEpistemicModel
    (mkEpistemicFrame ["w1", "w2", "w3"]
      [ ("a", [("w1", "w2"), ("w2", "w2"), ("w3", "w3")])
      , ("b", [("w1", "w2"), ("w2", "w2"), ("w3", "w3")]) ])
    [("p", ["w1", "w2"])]

-- "Veridicality: K[a]p → p (reflexive R_a)"
def eSpecMV : EpistemicModel :=
  mkEpistemicModel
    (mkEpistemicFrame ["w1", "w2"] [("a", [("w1", "w1"), ("w2", "w2")])])
    [("p", ["w1"])]

-- "Doxastic logic: Belief operator (Gamen.Doxastic, KD45)": knowledge
-- reflexive at w1 (T axiom holds); belief sees w2 from w1 but not w1
-- (non-factive, D axiom only).
def eSpecMB : EpistemicModel :=
  mkEpistemicModel
    (mkEpistemicFrameWithBelief ["w1", "w2"]
      [("a", [("w1", "w1"), ("w2", "w2")])]   -- knowledge: reflexive
      [("a", [("w1", "w2"), ("w2", "w2")])])  -- belief: serial, not reflexive
    [("p", ["w1"])]                           -- p is true only at w1

-- Two clinicians can disagree without contradicting the model.
def eSpecMD : EpistemicModel :=
  mkEpistemicModel
    (mkEpistemicFrameWithBelief ["w1", "w2", "w3"] []
      [ ("radA", [("w1", "w2")])    -- radA's belief world: w2 (PE holds)
      , ("radB", [("w1", "w3")]) ]) -- radB's belief world: w3 (PE absent)
    [("PE", ["w2"])]

/-- "Doxastic D-axiom rule (consistency tableau)": the same combined
system `gamen-validate`'s `check_consistency` uses. -/
def consistencySys : System :=
  { systemKDt with
    name := "KDt+doxasticD"
    usedPrefixRules := systemKDt.usedPrefixRules ++ doxasticRules }

-- "Public announcement (Definition 15.11)"
def eSpecMPA : EpistemicModel :=
  mkEpistemicModel
    (mkEpistemicFrame ["w1", "w2", "w3"]
      [ ("a", [("w1", "w2"), ("w2", "w2"), ("w3", "w3")])
      , ("b", [("w1", "w1"), ("w1", "w3"), ("w3", "w3")]) ])
    [("p", ["w1", "w2"]), ("q", ["w2"])]

def eSpecMPA2 : EpistemicModel :=
  mkEpistemicModel
    (mkEpistemicFrame ["w1", "w2", "w3"]
      [("a", [("w1", "w1"), ("w1", "w2"), ("w2", "w2"), ("w3", "w3")])])
    [("p", ["w1", "w2"])]

-- "Bisimulation (Definition 15.7)"
def eSpecBisM1 : EpistemicModel :=
  mkEpistemicModel
    (mkEpistemicFrame ["w1", "w2", "w3"]
      [("a", [("w1", "w2"), ("w1", "w3"), ("w2", "w2"), ("w3", "w3")])])
    [("p", ["w2", "w3"])]

def eSpecBisM2 : EpistemicModel :=
  mkEpistemicModel
    (mkEpistemicFrame ["v1", "v2"] [("a", [("v1", "v2"), ("v2", "v2")])])
    [("p", ["v2"])]

def eSpecBis : List (World × World) := [("w1", "v1"), ("w2", "v2"), ("w3", "v2")]

-- "EpistemicModel from KripkeModel": `mkFrame` is an `Except`, so the
-- fixture is too, and the case fails if it errors.
def eSpecFromKripke : Except String EpistemicModel :=
  (mkFrame ["w1", "w2"] [("w1", "w2")]).map fun fr =>
    fromKripkeModel (mkModel fr [("p", ["w2"])]) "a"

-- WorldGuardsSpec.hs:22, "eSatisfies errors on world not in EpistemicModel"
-- (gamen-hs#7).
def eGuardModel : EpistemicModel :=
  mkEpistemicModel
    (mkEpistemicFrame ["a", "b"] [("ag", [("a", "a"), ("a", "b"), ("b", "b")])])
    [("p", ["a", "b"]), ("q", ["b"]), ("r", ["a"])]

def eGuardProbe : Formula :=
  .implies (.or (.atom "p") (.atom "q")) (.and (.not (.atom "q")) (.atom "r"))

def epistemicCases : List Case := [
  -- "Epistemic formula construction (Definition 15.2)"
  ⟨"displays Knowledge and Announce",
    toString (Formula.knowledge "a" p) == "K[a]p" && toString (Formula.announce p q) == "[p]q"⟩,
  ⟨"Knowledge equality",
    Formula.knowledge "a" p == .knowledge "a" p && Formula.knowledge "a" p != .knowledge "b" p⟩,
  ⟨"epistemic formulas are not modal-free",
    (Formula.knowledge "a" p).isModalFree == false && (Formula.announce p q).isModalFree == false⟩,
  -- "EpistemicFrame construction and accessible (Definition 15.4)"
  ⟨"constructs frames with agent relations",
    eSpecFr1.eWorlds.contains "w1"
      && okIs (accHas eSpecFr1 "a" "w1" "w2") true
      && okIs (accHas eSpecFr1 "a" "w1" "w3") false
      && okIs (accHas eSpecFr1 "b" "w1" "w1") true
      && okIs (accHas eSpecFr1 "b" "w1" "w3") true⟩,
  ⟨"tracks agents", (agents eSpecFr1).contains "a" && (agents eSpecFr1).contains "b"⟩,
  -- "Epistemic truth conditions (Definition 15.5)"
  ⟨"evaluates Knowledge",
    okIs (eSatisfies eSpecM2 "w1" (.knowledge "a" p)) true    -- w2 has p
      && okIs (eSatisfies eSpecM2 "w1" (.knowledge "b" p)) false  -- w3 has no p
      && okIs (eSatisfies eSpecM2 "w1" (.knowledge "a" q)) true   -- w2 has q
      && okIs (eSatisfies eSpecM2 "w1" (.knowledge "b" q)) false⟩, -- w3 has no q
  -- "Group and common knowledge (Definition 15.3, 15.6)"
  ⟨"evaluates group knowledge",
    okIs (groupKnows eSpecM3 "w1" ["a", "b"] p) true
      && okIs (groupKnows eSpecM3 "w3" ["a", "b"] p) false⟩,
  ⟨"evaluates common knowledge", okIs (commonKnowledge eSpecM3 "w1" ["a", "b"] p) true⟩,
  -- "Veridicality: K[a]p → p (reflexive R_a)"
  ⟨"K[a]p → p holds on reflexive frames",
    okIs (eSatisfies eSpecMV "w1" (.implies (.knowledge "a" p) p)) true
      && okIs (eSatisfies eSpecMV "w2" (.implies (.knowledge "a" p) p)) true⟩,
  -- "Doxastic logic: Belief operator (Gamen.Doxastic, KD45)"
  ⟨"displays Belief", toString (Formula.belief "a" p) == "B[a]p"⟩,
  ⟨"Belief equality and modal status",
    Formula.belief "a" p == .belief "a" p
      && Formula.belief "a" p != .belief "b" p
      && Formula.belief "a" p != .knowledge "a" p
      && (Formula.belief "a" p).isModalFree == false⟩,
  ⟨"atoms recurses into Belief",
    (Formula.belief "a" (.and p q)).atoms.toList == [⟨"p"⟩, ⟨"q"⟩]⟩,
  ⟨"Belief is non-factive: B_a p can be true while p is false",
    -- At w1: p holds, but agent's belief reaches only w2 (where p is false)
    okIs (eSatisfies eSpecMB "w1" (.atom "p")) true
      && okIs (eSatisfies eSpecMB "w1" (.belief "a" p)) false
      -- At w1: agent believes ¬p (since the only doxastic successor w2 has ¬p)
      && okIs (eSatisfies eSpecMB "w1" (.belief "a" (.not p))) true
      -- Knowledge of p coincides with p at w1 (reflexive)
      && okIs (eSatisfies eSpecMB "w1" (.knowledge "a" p)) true⟩,
  ⟨"Knowledge and Belief use independent relations",
    okIs (eSatisfies eSpecMD "w1" (.belief "radA" (.atom "PE"))) true
      && okIs (eSatisfies eSpecMD "w1" (.belief "radB" (.not (.atom "PE")))) true⟩,
  -- "Doxastic D-axiom rule (consistency tableau)"
  ⟨"two clinicians disagreeing is consistent (cwyde core case)",
    tableauConsistent consistencySys defaultMaxSteps
      [.belief "radA" (.atom "PE"), .belief "radB" (.not (.atom "PE"))] == .definitely true⟩,
  ⟨"single agent's contradictory beliefs is inconsistent (D axiom)",
    tableauConsistent consistencySys defaultMaxSteps
      [.belief "radA" (.atom "PE"), .belief "radA" (.not (.atom "PE"))] == .definitely false⟩,
  ⟨"B_a p ∧ ¬p is consistent (belief is non-factive)",
    tableauConsistent consistencySys defaultMaxSteps
      [.belief "radA" (.atom "PE"), .not (.atom "PE")] == .definitely true⟩,
  ⟨"B_a p ∧ ¬B_a p is propositionally inconsistent",
    tableauConsistent consistencySys defaultMaxSteps
      [.belief "radA" (.atom "PE"), .not (.belief "radA" (.atom "PE"))] == .definitely false⟩,
  -- "Public announcement (Definition 15.11)"
  ⟨"restricts model correctly",
    match restrictModel eSpecMPA p with
    | .ok mP =>
        mP.eFrame.eWorlds.contains "w1"
          && mP.eFrame.eWorlds.contains "w2"
          && !mP.eFrame.eWorlds.contains "w3"
          && okIs (accHas mP.eFrame "b" "w1" "w3") false
    | .error _ => false⟩,
  ⟨"[p]K[a]p: after announcing p, a knows p",
    okIs (eSatisfies eSpecMPA2 "w1" (.announce p (.knowledge "a" p))) true
      && okIs (eSatisfies eSpecMPA2 "w3" (.announce p (.knowledge "a" p))) true⟩,
  -- "Bisimulation (Definition 15.7)"
  ⟨"validates bisimulation",
    okIs (isBisimulation eSpecBisM1 eSpecBisM2 eSpecBis) true
      && okIs (bisimilarWorlds eSpecBisM1 eSpecBisM2 "w1" "v1" eSpecBis) true⟩,
  ⟨"bisimilar worlds satisfy same formulas (Theorem 15.8)",
    okIs (eSatisfies eSpecBisM1 "w1" (.knowledge "a" p)) true
      && okIs (eSatisfies eSpecBisM2 "v1" (.knowledge "a" p)) true⟩,
  -- "EpistemicModel from KripkeModel"
  ⟨"wraps KripkeModel as single-agent epistemic model",
    okIs (eSpecFromKripke >>= fun em => accHas em.eFrame "a" "w1" "w2") true
      && okIs (eSpecFromKripke >>= fun em => eSatisfies em "w1" (.knowledge "a" p)) true⟩,
  -- WorldGuardsSpec.hs:22 (gamen-hs#7)
  ⟨"eSatisfies errors on world not in EpistemicModel",
    okIs (eSatisfies eGuardModel "a" eGuardProbe) true
      && isErr (eSatisfies eGuardModel "c" eGuardProbe)⟩,
  -- Not in gamen-hs: the two halves of the laziness contract (CLAUDE.md,
  -- "Laziness"; `Epistemic.hs` ~148–158). Haskell's per-announcement table
  -- of restricted models is lazy, so `⊥ ∧ [□p]p` is simply false: `[□p]p`
  -- is never reached and `□p` (an error in epistemic models) is never
  -- evaluated. A port that built the table up front would error here.
  ⟨"Not in gamen-hs: ⊥ ∧ [□p]p is false — an unreached announcement body is never evaluated",
    okIs (eSatisfies eSpecMPA "w1" (.and .bot (.announce (.box p) p))) false⟩,
  -- …and once `[B]C` *is* reached with `B` true at `w`, the restriction
  -- evaluates `B` at every world: `p ∨ □q` is true at w1 by short-circuit
  -- but reaches `□q` at w3 (where p is false), so the whole thing errors,
  -- as Haskell's `restrictModel` would.
  ⟨"Not in gamen-hs: [p ∨ □q]p at w1 errors — the restriction evaluates the body at every world",
    isErr (eSatisfies eSpecMPA "w1" (.announce (.or p (.box q)) p))⟩,
  -- Not in gamen-hs (which has the same gap: every `commonKnowledge` case
  -- there is settled by one step). R_G⁺ must reach w3 from w1 in two steps
  -- (a: w1→w2, b: w2→w3), where p fails; a one-step "closure" sees only
  -- w2 and answers true.
  ⟨"Not in gamen-hs: common knowledge follows the transitive closure past one step",
    let m := mkEpistemicModel
      (mkEpistemicFrame ["w1", "w2", "w3"] [("a", [("w1", "w2")]), ("b", [("w2", "w3")])])
      [("p", ["w1", "w2"])]
    okIs (commonKnowledge m "w1" ["a", "b"] p) false⟩
]

/-! ### PaperCorrespondence.hs: "B&D Chapter 15 — Epistemic Logics (Zach 2025)" -/

-- Figure 15.2 (B&D p. 199): two bisimilar models.
-- M1: w1→{w2,w3}, self-loops at w2/w3. V(p)={w2,w3}.
-- M2: v1→v2, self-loop at v2. V(p)={v2}.
-- Bisimulation: Z={(w1,v1),(w2,v2),(w3,v2)}.
def fig132m1 : EpistemicModel :=
  mkEpistemicModel
    (mkEpistemicFrame ["w1", "w2", "w3"]
      [("a", [("w1", "w2"), ("w1", "w3"), ("w2", "w2"), ("w3", "w3")])])
    [("p", ["w2", "w3"])]

def fig132m2 : EpistemicModel :=
  mkEpistemicModel
    (mkEpistemicFrame ["v1", "v2"] [("a", [("v1", "v2"), ("v2", "v2")])])
    [("p", ["v2"])]

-- Figure 15.3 (B&D p. 202): before and after public announcement of p.
-- W={w1,w2,w3}; V(p)={w1,w3}, V(q)={w3}.
-- Agent a: w1↔w3 plus self-loops; agent b: full clique.
def fig133model : EpistemicModel :=
  mkEpistemicModel
    (mkEpistemicFrame ["w1", "w2", "w3"]
      [ ("a", [("w1", "w1"), ("w1", "w3"), ("w3", "w1"), ("w3", "w3"), ("w2", "w2")])
      , ("b", [ ("w1", "w1"), ("w1", "w2"), ("w1", "w3")
              , ("w2", "w1"), ("w2", "w2"), ("w2", "w3")
              , ("w3", "w1"), ("w3", "w2"), ("w3", "w3")]) ])
    [("p", ["w1", "w3"]), ("q", ["w3"])]

def epistemicPaperCorrespondenceCases : List Case := [
  -- "Definition 15.4 (p. 193): multi-agent epistemic model M = ⟨W,{R_a},V⟩"
  ⟨"Figure 15.2 (p. 199): |W_M1| = 3", fig132m1.eFrame.eWorlds.size == 3⟩,
  ⟨"Figure 15.2 (p. 199): |W_M2| = 2", fig132m2.eFrame.eWorlds.size == 2⟩,
  ⟨"Figure 15.2 (p. 199): M1 has exactly one agent {a}",
    (agents fig132m1.eFrame).toList == ["a"]⟩,
  -- "Definition 15.5 (p. 194): K_a B true at w iff B holds at all R_a-successors"
  ⟨"K_a p at w1 in fig132m1: R_a(w1)={w2,w3}, both have p → K_a p True",
    okIs (eSatisfies fig132m1 "w1" (.knowledge "a" p)) true⟩,
  ⟨"K_a p at v1 in fig132m2: R_a(v1)={v2}, v2 has p → K_a p True",
    okIs (eSatisfies fig132m2 "v1" (.knowledge "a" p)) true⟩,
  ⟨"K_b p at w1 in fig133model: R_b(w1) includes w2 which lacks p → K_b p False",
    okIs (eSatisfies fig133model "w1" (.knowledge "b" p)) false⟩,
  -- "Table 15.1 (p. 196): Veridicality — reflexive R_a implies K_a B → B"
  ⟨"K_a p = True at w2 in fig132m1 (self-loop at w2, w2 ∈ V(p))",
    okIs (eSatisfies fig132m1 "w2" (.knowledge "a" p)) true⟩,
  ⟨"p = True at w2 in fig132m1 — veridicality: K_a p → p holds here",
    okIs (eSatisfies fig132m1 "w2" p) true⟩,
  -- "Definition 15.6 (p. 196): common knowledge — A at every R_G*-reachable world"
  ⟨"p is NOT common knowledge from w3 in fig133model: b can reach w2 which lacks p",
    okIs (commonKnowledge fig133model "w3" ["a", "b"] p) false⟩,
  ⟨"p is common knowledge in a model where p holds everywhere",
    let m := mkEpistemicModel
      (mkEpistemicFrame ["u", "v"] [("a", [("u", "v"), ("v", "u"), ("u", "u"), ("v", "v")])])
      [("p", ["u", "v"])]
    okIs (commonKnowledge m "u" ["a"] p) true⟩,
  -- "Definition 15.7 + Theorem 15.8 (p. 198): bisimulation preserves modal truth"
  ⟨"Figure 15.2 (p. 199): Z={(w1,v1),(w2,v2),(w3,v2)} is a bisimulation",
    okIs (isBisimulation fig132m1 fig132m2 [("w1", "v1"), ("w2", "v2"), ("w3", "v2")]) true⟩,
  ⟨"Theorem 15.8: bisimilar worlds w1/v1 agree on K_a p",
    match eSatisfies fig132m1 "w1" (.knowledge "a" p), eSatisfies fig132m2 "v1" (.knowledge "a" p) with
    | .ok b1, .ok b2 => b1 == b2
    | _, _ => false⟩,
  ⟨"worlds with different valuations are not bisimilar: {(w1,w2)} fails clause 1",
    -- w1 lacks p, w2 has p — propositional agreement fails
    okIs (isBisimulation fig132m1 fig132m1 [("w1", "w2")]) false⟩,
  -- "Definition 15.11 (p. 201): PAL semantics — [B]C restricts model to B-worlds"
  ⟨"Figure 15.3 (p. 202): before announcement, K_b p is false at w1",
    okIs (eSatisfies fig133model "w1" (.knowledge "b" p)) false⟩,
  ⟨"Figure 15.3 (p. 202): M, w1 ⊩ [p]K_b p — after announcing p, b knows p",
    okIs (eSatisfies fig133model "w1" (.announce p (.knowledge "b" p))) true⟩
]

/-! ### RegressionIssue18.hs: "B1: unknown agent errors, never vacuous truth" (Epistemic `it`s) -/

def epistemicRegressionCases : List Case :=
  let eModel := mkEpistemicModel
    (mkEpistemicFrame ["w"] [("a", [("w", "w")])])
    [("p", ["w"])]
  [ ⟨"Epistemic: a known agent evaluates normally",
      okIs (eSatisfies eModel "w" (.knowledge "a" p)) true⟩,
    ⟨"Epistemic: K_typo ⊥ errors (not vacuously true)",
      isErr (eSatisfies eModel "w" (.knowledge "typo" .bot))⟩ ] ++
  -- `RegressionIssue18.hs` "B8: Epistemic common knowledge and
  -- bisimulation" (all 4 `it`s; missed by the original port, added after
  -- merge).
  let ckM := mkEpistemicModel
    (mkEpistemicFrame ["cw", "cu"] [("a", [("cw", "cu")])])
    [("p", ["cu"])]
  let bm1 := mkEpistemicModel
    (mkEpistemicFrameWithBelief ["x"] [("a", [("x", "x")])] [("a", [("x", "x")])]) []
  let bm2 := mkEpistemicModel
    (mkEpistemicFrameWithBelief ["y"] [("a", [("y", "y")])] [("a", [])]) []
  let lm := mkEpistemicModel
    (mkEpistemicFrame ["s1", "s2"] [("a", [("s1", "s1"), ("s2", "s2")])])
    [("p", ["s1"])]
  [ ⟨"B8: commonKnowledge uses the transitive closure R⁺, not R∗",
      okIs (commonKnowledge ckM "cw" ["a"] (.atomF ⟨"p"⟩)) true⟩,
    ⟨"B8: isBisimulation now also requires doxastic-relation agreement",
      okIs (isBisimulation bm1 bm2 [("x", "y")]) false⟩,
    ⟨"B8: isBisimulation accepts a doxastic-respecting relation",
      okIs (isBisimulation bm1 bm1 [("x", "x")]) true⟩,
    ⟨"B8: largestBisimulation contains the identity and separates non-equivalent worlds",
      match largestBisimulation lm lm with
      | .ok lb => ["s1", "s2"].all (fun w => lb.contains (w, w)) && !lb.contains ("s1", "s2")
      | .error _ => false⟩,
    -- The B8 fixture's worlds already differ on `p`, so the seed alone
    -- separates them; here `u` and `v` agree on every atom and only a
    -- refinement round (u's successor has p, v's does not) splits them.
    ⟨"Not in gamen-hs: largestBisimulation refines atom-agreeing pairs by their successors",
      let rm := mkEpistemicModel
        (mkEpistemicFrame ["t", "u", "v"] [("a", [("u", "t"), ("v", "v"), ("t", "t")])])
        [("p", ["t"])]
      match largestBisimulation rm rm with
      | .ok lb => lb.contains ("u", "u") && !lb.contains ("u", "v") && !lb.contains ("v", "u")
      | .error _ => false⟩ ]

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
`mkEpistemicFrameWithBelief`/`Knowledge` from `Gamen.Epistemic`; they are
ported here too, after the tableau block, over the `doxM` fixture. -/

-- KD45 doxastic fixture (PaperCorrespondence.hs `doxFr`/`doxM`): non-factive
-- belief. Agent "a" epistemically sees only w0 (self-loop), so K_a p is
-- false at w0 (p is not in w0). Doxastically, a sees only w1 (where p is
-- true), so B_a p is true at w0 — even though p is false there.
def doxM : EpistemicModel :=
  mkEpistemicModel
    (mkEpistemicFrameWithBelief ["w0", "w1"]
      [("a", [("w0", "w0"), ("w1", "w1")])]   -- epistemic: reflexive (self-loops)
      [("a", [("w0", "w1"), ("w1", "w1")])])  -- doxastic: serial (w0→w1, w1→w1)
    [("p", ["w1"])]                           -- p true only at w1

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
      [.belief "a" p, .belief "b" (.not p)] == .definitely true⟩,
  -- "Non-factiveness: B_a φ at w does not entail φ at w"
  ⟨"B_a p true at w0 — all doxastic successors (w1) satisfy p",
    okIs (eSatisfies doxM "w0" (.belief "a" p)) true⟩,
  ⟨"p false at w0 — demonstrating non-factiveness of belief",
    okIs (eSatisfies doxM "w0" p) false⟩,
  ⟨"K_a p false at w0 — epistemic self-loop at w0 fails p; knowledge is factive",
    okIs (eSatisfies doxM "w0" (.knowledge "a" p)) false⟩,
  -- "D axiom: B_a φ → ¬B_a(¬φ)  (doxastic seriality)"
  ⟨"B_a p holds at w0", okIs (eSatisfies doxM "w0" (.belief "a" p)) true⟩,
  ⟨"B_a(¬p) false at w0 — D axiom holds: agent does not believe contradiction",
    okIs (eSatisfies doxM "w0" (.belief "a" (.not p))) false⟩,
  ⟨"D axiom formula B_a p → ¬B_a(¬p) satisfied at every world in doxM",
    okIs (["w0", "w1"].allM fun w =>
      eSatisfies doxM w (.implies (.belief "a" p) (.not (.belief "a" (.not p))))) true⟩
]

/-! ## Ranking theory (`Gamen.RankingTheory`)

Port of `test/RankingTheorySpec.hs` in full (40 `it`s, in file order), then
the "Spohn (1988) — ranking theory" section of `test/PaperCorrespondence.hs`
in full (15 `it`s), then "B4: ranking theory κ=∞ no longer leaks into
arithmetic" from `test/RegressionIssue18.hs` (5 `it`s). An `it` with several
`shouldBe`s is one case joining them with `&&`.

Every `Except` result is compared against `.ok v` (`okIs`, defined near
the top of this file alongside `Case`/`p`/`q`), so an error fails the case
whichever answer was expected; the Haskell `shouldThrow` cases check for
`.error` (`isErr`). Tableau verdicts are compared against `.definitely
true`/`.definitely false`, so budget exhaustion fails too.

One case name differs from the Haskell: "conditionalize is overwrite, not
additive (Spohn p.117)" cites p.118 here, where the quoted passage is in
`notes/spohn1988-ordinal-conditional-functions.pdf`. -/

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
  -- live in `epistemicCases` (`eSatisfies`), `stitCases` (`sSatisfies`),
  -- `xstitCases` (`xSatisfies`), and `lacaCases` (`lSatisfies`).
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
  [ -- Gamen.ManyValued (Lean-only; plans/three-valued-logic-2026-09-29.md).
    ("ManyValued: K3 on {t,f}-valuations equals Semantics.satisfies (one-world model)",
      run (NamedBinder "f" <| ∀ f : ManyValuedTests.CoreFormula,
        NamedBinder "bp" <| ∀ bp : Bool, NamedBinder "bq" <| ∀ bq : Bool,
        NamedBinder "br" <| ∀ br : Bool,
        ManyValuedTests.k3MatchesSemantics f.getFormula bp bq br = true)),
    ("ManyValued: eval never errors on ¬ ∧ ∨ → formulas (all six matrices)",
      run (NamedBinder "f" <| ∀ f : ManyValuedTests.CoreFormula,
        ManyValuedTests.evalNeverErrorsCore f.getFormula = true)),
    ("ManyValued: eval never errors on formulas with ⊥ (classical, Gödel)",
      run (NamedBinder "f" <| ∀ f : PropFormula,
        ManyValuedTests.evalNeverErrorsWithBot f.getFormula = true)),
    ("ManyValued: LP tautologies are the classical ones [thr:mul:prop:LP-taut-CL]",
      run (NamedBinder "f" <| ∀ f : ManyValuedTests.CoreFormula,
        ManyValuedTests.lpTautologiesClassical f.getFormula = true) 200),
    ("ManyValued: classical isTautology by enumeration equals Semantics.isTautology",
      run (NamedBinder "f" <| ∀ f : PropFormula,
        ManyValuedTests.classicalTautologyMatchesSemantics f.getFormula = true) 200),
    ("ManyValued: entails (0, 1, 2 premises) equals a brute-force oracle (all six matrices)",
      run (NamedBinder "g" <| ∀ g : ManyValuedTests.CoreFormula,
        NamedBinder "h" <| ∀ h : ManyValuedTests.CoreFormula,
        NamedBinder "c" <| ∀ c : ManyValuedTests.CoreFormula,
        ManyValuedTests.entailsMatchesOracle g.getFormula h.getFormula c.getFormula = true) 200),
    ("Completion: K3 status never contradicts the exact check (theorems 2–4)",
      run (NamedBinder "f" <| ∀ f : ManyValuedTests.CoreFormula,
        NamedBinder "kp" <| ∀ kp : Bool, NamedBinder "bp" <| ∀ bp : Bool,
        NamedBinder "kq" <| ∀ kq : Bool, NamedBinder "bq" <| ∀ bq : Bool,
        NamedBinder "kr" <| ∀ kr : Bool, NamedBinder "br" <| ∀ br : Bool,
        NamedBinder "c" <| ∀ c : Bool,
        CompletionTests.k3ExactConsistent f.getFormula kp bp kq bq kr br c = true) 200),
    ("toNNF idempotent",
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
    -- Widgets/Countermodel.lean (Lean-only; plan Part A): K, KT, S4, one
    -- premise, formulas capped at size 12 by the `Arbitrary Formula` instance.
    ("countermodel view: every countermodel refutes the conclusion at the root and \
      satisfies the premise, lies inside the canvas bounds, and, when drawn, has no arrow \
      through another world; .valid agrees with tableauProves (K, KT, S4)",
      run (NamedBinder "f" <| ∀ f : Formula, NamedBinder "g" <| ∀ g : Formula,
        ([systemK, systemKT, systemS4].all fun sys => CountermodelViewTests.viewOK sys g f)
          = true) 100),
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
    -- Gamen.Epistemic: public announcement semantics (the "Gamen.Epistemic:
    -- public announcement semantics" describe block of `test/Properties.hs`,
    -- both `prop`s, 100 instances each as hspec's default). The Haskell
    -- title says "Def. 13.11"; in `notes/bd-screen.pdf` the restricted
    -- model M|B is Definition 15.11 (p. 201). An error from `restrictModel`
    -- or `eSatisfies` is a failure, never a pass.
    ("restrictModel (Def. 15.11): every world in M|B satisfies B",
      run (NamedBinder "m" <| ∀ m : EpistemicModel, NamedBinder "f" <| ∀ f : PropFormula,
        isOkTrue (restrictModel m f.getFormula >>= (eIsTrueIn · f.getFormula)) = true) 100),
    ("K_a distribution axiom: K_a(φ→ψ) → (K_a φ → K_a ψ) at every world",
      run (NamedBinder "m" <| ∀ m : EpistemicModel, NamedBinder "f" <| ∀ f : PropFormula,
        NamedBinder "g" <| ∀ g : PropFormula,
        isOkTrue (eIsTrueIn m
          (.implies (.knowledge "a" (.implies f.getFormula g.getFormula))
                    (.implies (.knowledge "a" f.getFormula) (.knowledge "a" g.getFormula)))) = true) 100),
    -- Gamen.RankingTheory: structural invariants — the two `isContingent
    -- ⇒ …` properties now live in `Tests/SlowMain.lean` alongside the
    -- other five `==>`-shaped properties (see the comment above).
    --
    -- Gamen.Kripke: not in gamen-hs. `checkIndependence` was reworked from
    -- building every combination via `sections` to an early-exit,
    -- depth-first search (`PORTING.md`'s Stit row); this checks the two
    -- implementations agree on every instance, not just the fixed cases in
    -- `kripkeCases`.
    ("checkIndependence agrees with the sections-based search it replaced",
      run (NamedBinder "inst" <| ∀ inst : IndependenceInstance,
        (let mom := Std.TreeSet.ofList inst.worlds
         checkIndependence inst.choiceCell inst.agents mom
           == legacyCheckIndependence inst.choiceCell inst.agents mom) = true) 300),
    -- Gamen.Epistemic: not in gamen-hs. `commonKnowledge`'s closure was
    -- rewritten from Haskell's BFS to `iterateToFixpoint`; this checks the
    -- two agree (value or error alike) on random one-agent models, whose
    -- random edge sets include multi-step chains, from the world "w1"
    -- every generated model has.
    ("commonKnowledge agrees with the breadth-first search it replaced",
      run (NamedBinder "m" <| ∀ m : EpistemicModel, NamedBinder "f" <| ∀ f : PropFormula,
        (match commonKnowledge m "w1" ["a"] f.getFormula,
               bfsCommonKnowledge m "w1" ["a"] f.getFormula with
         | .ok a, .ok b => a == b
         | .error x, .error y => x == y
         | _, _ => false) = true) 200),
    -- Gamen.Laca: succState algebraic properties (test/Properties.hs's
    -- "Gamen.Laca: succState algebraic properties" describe block, all
    -- three `prop`s, 100 instances each as hspec's default — no
    -- `modifyMaxSuccess` override near them in the Haskell).
    ("succState with empty attempt is identity",
      run (NamedBinder "s" <| ∀ s : LacaState, succState s ∅ == s) 100),
    ("succState is self-inverse: applying the same attempt twice returns original",
      run (NamedBinder "s" <| ∀ s : LacaState, NamedBinder "atts" <| ∀ atts : AttemptSet,
        succState (succState s atts.getAttemptSet) atts.getAttemptSet == s) 100),
    ("succState flips each attempted atom and leaves others unchanged",
      run (NamedBinder "s" <| ∀ s : LacaState, NamedBinder "atts" <| ∀ atts : AttemptSet,
        (let s' := succState s atts.getAttemptSet
         atts.getAttemptSet.toList.all (fun a => stateValue s' a == !(stateValue s a))
           && (["p", "q", "r"].filter (!atts.getAttemptSet.contains ·)).all
                (fun a => stateValue s' a == stateValue s a)) = true) 100),
    -- Gamen.Dcleg: the "Gamen.Dcleg: propositional invariants over a fixed
    -- 2-world FPIE game" describe block of `test/Properties.hs` (all four
    -- `prop`s, 100 instances each as hspec's default). An error at any point
    -- fails the property; `||` short-circuits as in the Haskell.
    ("Dcleg double negation: ¬¬φ ↔ φ at every (world, vertex) pair",
      run (NamedBinder "f" <| ∀ f : DclegPropFormula,
        isOkTrue (dclegPropPoints.allM fun (g, w) => do
          let a ← dclegSatisfies dclegPropGame g w (.dfNeg (.dfNeg f.getFormula))
          let b ← dclegSatisfies dclegPropGame g w f.getFormula
          return a == b) = true) 100),
    ("Dcleg DFOr with DFBot is identity: φ ∨ ⊥ ↔ φ at every point",
      run (NamedBinder "f" <| ∀ f : DclegPropFormula,
        isOkTrue (dclegPropPoints.allM fun (g, w) => do
          let a ← dclegSatisfies dclegPropGame g w (.dfOr f.getFormula .dfBot)
          let b ← dclegSatisfies dclegPropGame g w f.getFormula
          return a == b) = true) 100),
    ("Dcleg □ T-axiom (§3.2.5 S5, p. 23): □φ → φ at every point",
      run (NamedBinder "f" <| ∀ f : DclegPropFormula,
        isOkTrue (dclegPropPoints.allM fun (g, w) => do
          if !(← dclegSatisfies dclegPropGame g w (.dfBox f.getFormula)) then return true
          dclegSatisfies dclegPropGame g w f.getFormula) = true) 100),
    ("Dcleg centering (§3.2.2, p. 19): if φ holds at (γ,w) then φ □→ ψ ↔ ψ at decision nodes",
      run (NamedBinder "f" <| ∀ f : DclegPropFormula, NamedBinder "g" <| ∀ g : DclegPropFormula,
        isOkTrue (dclegDecisionPoints.allM fun (γ, w) => do
          if !(← dclegSatisfies dclegPropGame γ w f.getFormula) then return true
          let c ← dclegSatisfies dclegPropGame γ w (.dfConditional f.getFormula g.getFormula)
          let d ← dclegSatisfies dclegPropGame γ w g.getFormula
          return c == d) = true) 100),
    -- Not in gamen-hs: validities checked over random *admissible* premise
    -- systems, not only the default (F is a model parameter subject to
    -- Centering and Contemporary Universality, §3.2.2, p. 19;
    -- docs/dcleg-outcome-node-premises-2026-09-30.md, "Proposed fix" 3).
    ("Dcleg random admissible F passes validateDclegModel (Centering and Contemporary \
      Universality at every reached pair, §3.2.2, p. 19)",
      run (NamedBinder "a" <| ∀ a : AdmissibleDcleg,
        (validateDclegModel a.model).isEmpty = true) 100),
    ("Dcleg counterfactual modus ponens φ ∧ (φ □→ ψ) → ψ at every reached pair, random \
      admissible F (Centering, §3.2.2, p. 19)",
      run (NamedBinder "a" <| ∀ a : AdmissibleDcleg, NamedBinder "f" <| ∀ f : DclegPropFormula,
        NamedBinder "g" <| ∀ g : DclegPropFormula,
        (let m := a.model
         isOkTrue ((dclegPointsOf m).allM fun (γ, w) =>
          dclegSatisfies m γ w (dfImplies (dfAnd f.getFormula
            (.dfConditional f.getFormula g.getFormula)) g.getFormula))) = true) 100),
    ("Dcleg ¬(⊤ □→ ⊥) at every reached pair, outcome nodes included, random admissible F \
      (Centering, §3.2.2, p. 19)",
      run (NamedBinder "a" <| ∀ a : AdmissibleDcleg,
        (let m := a.model
         isOkTrue ((dclegPointsOf m).allM fun (γ, w) =>
          dclegSatisfies m γ w (.dfNeg (.dfConditional dfTop .dfBot)))) = true) 100),
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

There is no `test/CgsSpec.hs` in gamen-hs, but `test/RegressionIssue18.hs`
has a "B7: mkCgs rejects transitions that escape the state set" describe
block (2 `it`s, lines 319–331), ported verbatim as `cgsCases`'s first two
entries below (the same file's "B7: Kripke / FrameProperties dangling-edge
and class fixes" block is `kripkeCases`, near `Tests/Main.lean:646`). Every
other `Cgs`-exercising `PaperCorrespondence.hs` section reaches it only
through `Coalition`, `Atl`/`Atl.ModelCheck`, or `Atel`; `Gamen.Atl` and
`Gamen.Atl.ModelCheck` are now ported (see below and `PORTING.md`), the
the ATEL one is not; `Gamen.Coalition` is now ported too (see
`coalitionCases`, right after this list):

- "Pauly (2002) — Coalition Logic" (`coalSatisfies`, `checkTopEffectivity`,
  `checkBotMonotonicity`, `checkMonotonicity`, `checkSuperadditivity`: all
  `Gamen.Coalition`; ported in full as `coalitionCases`, reusing this
  section's "control game" `Cgs` fixture, `controlCgs`, below);
- "Alur, Henzinger & Kupferman (2002) — ATL" (`sat`: `atlModelCheckCases`
  below; `atlSatisfies`, `CanNext`/`CanAlways`/`CanEventually`/`CanUntil`:
  `atlCases`, `Gamen.Atl`'s section);
- "van der Hoek & Wooldridge (2003) — ATEL" (adds `AtelModel`,
  `mkAtelModel`, `atelSat`: `Gamen.Atel`, ported as `atelCases`);
- the imperfect-information ATEL section right after it (adds
  `Gamen.Atl.ImperfectInfo`, ported as `atlirCases`).

`Gamen.Laca` is now ported (`Gamen/Laca.lean`); its `lacaToCgs` coercion
sub-block of the "Herzig, Lorini & Perrotin (2022) — LACA" section is split
across three case lists: the four `it`s that only exercise `Cgs` primitives
(`cgsStates`, `cgsAgents`, two `cgsLabeling`) are ported in
`lacaPaperCorrespondenceCases`; its other three `it`s (`atlSatisfies` × 2,
`sat`) are ported in `atlCases` (`Gamen.Atl`'s section).

So apart from the two `RegressionIssue18.hs` cases, every other case below
is a not-in-spec sanity check on the raw `Cgs` primitives themselves
(`mkCgs`, `availableMoves`, `jointMoves`, `applyJointMove`, `preC`), each
flagged as such. The two fixtures used for those are the `Cgs` values
`PaperCorrespondence.hs` builds for the sections above — the "control
game" (Pauly 2002, `Int` states/`String` actions, agents `alice`/`bob`)
and the "loop" model (AHK 2002) — and the expected `preC` values are
computed by hand from the Haskell file's own inline comments (cited
below), not from the Lean code under test. Coverage of `mkCgs`'s other
error branch (an agent with no moves at some state) has no Haskell
counterpart at all, not even in `RegressionIssue18.hs`; it matters for the
same reason `Kripke.mkFrame`'s dangling-edge check does (adversarial
review B7, cited in `Gamen.Cgs`'s `mkCgs` docstring). -/

/-- `test/RegressionIssue18.hs:319–330`'s fixture, verbatim: states `{0,1}`,
agents `{"a"}`, `mvs _ _ = {"go"}`, `lbl _ = ∅`. -/
private def b7Moves (_ : Nat) (_ : String) : Std.TreeSet String := Std.TreeSet.ofList ["go"]

private def b7Label (_ : Nat) : Std.TreeSet String := ∅

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
  -- RegressionIssue18.hs: "B7: mkCgs rejects transitions that escape the
  -- state set" (lines 319–331).
  ⟨"RegressionIssue18 B7: an escaping successor (→ state 9 ∉ states) is rejected",
    match mkCgs (Std.TreeSet.ofList [0, 1]) (Std.TreeSet.ofList ["a"]) b7Moves
        (fun _ _ => 9) b7Label with
    | .error _ => true
    | .ok _ => false⟩,
  ⟨"RegressionIssue18 B7: a closed transition builds normally",
    match mkCgs (Std.TreeSet.ofList [0, 1]) (Std.TreeSet.ofList ["a"]) b7Moves
        (fun s _ => s) b7Label with
    | .ok _ => true
    | .error _ => false⟩,
  ⟨"PaperCorrespondence.hs:1273 mkCgs accepts the control game (non-empty moves for all \
    agents at all states) — the only `it` of the \"Pauly (2002) — Coalition Logic\" \
    section's \"Definition 1\" block that exercises Cgs, not Coalition; its siblings are \
    in coalitionCases",
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
  ⟨"Not in gamen-hs: preC(control, {bob}, {2}) = ∅ — bob alone can't force landing in \
    exactly {2}: playing \"q\" also allows alice to steer to 0 (not 2), and playing \
    \"not-q\" also allows alice to steer to 1 or 3 (not 2); the true opponent is alice, \
    not bob himself (this is the {bob} mirror of the {alice} case above: emptying the \
    opponents set, or setting it to the coalition, would wrongly make \"q\" sufficient, \
    since q alone forces landing in {0,2} and this fixture's target set only contains \
    one of the two)",
    match controlCgs with
    | .ok cgs => preC cgs (Std.TreeSet.ofList ["bob"]) (Std.TreeSet.ofList [2]) == ∅
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

/-! ## Coalition (`Gamen.Coalition`)

There is no `test/CoalitionSpec.hs` in gamen-hs (`for f in coalSatisfies
coalIsTrueIn checkTopEffectivity checkBotMonotonicity checkMonotonicity
checkSuperadditivity; do grep -lw "$f" test/*.hs; done` finds hits only in
`test/PaperCorrespondence.hs`). `coalIsTrueIn` is not called by any `it`
either. Ported below (`coalitionCases`): every `it` of `PaperCorrespondence.hs`'s
"Pauly (2002) — Coalition Logic" section (lines 1227–1361, three `describe`
blocks: "Definition 1 (p. 152)", "Definition 3 (p. 153)", "Theorem 3.2
(p. 155)"), reusing that section's own "control game" `Cgs` fixture
(`controlCgs`, `cgsCases`'s docstring above), except the one `it` that
exercises only `mkCgs` ("mkCgs accepts the control game", line 1273):
that assertion is already covered by `cgsCases`'s "Not in gamen-hs (no
CgsSpec.hs): mkCgs accepts the Pauly (2002) control game" case, which
turns out to be this very `it` under a "not in gamen-hs" label written
before `Gamen.Coalition` was ported — corrected in place, since porting a
second copy of the same assertion would be porting from scratch code that
already exists.

Pauly (2001), *Logic for Social Software* (ILLC DS-2001-10), and Pauly
(2002), *A Modal Logic for Coalitional Power in Games* (J. Log. Comp.
12(1): 149–166) — the Haskell module's two citations — are not among the
PDFs in `gamen-hs/notes/` (only a correspondence note derived from the
Haskell itself, `notes/pauly2002-correspondence.md`); the page numbers in
the Haskell's `describe` titles below are kept exactly as given, unverified
against a primary source (`Gamen.Cgs`/`Gamen.Atl.ModelCheck`'s docstrings
make the same point about their own AHK 2002 citations). -/

def coalitionCases : List Case :=
  let p_ : Formula := .atom "p"
  let q_ : Formula := .atom "q"
  let cAlice : List String := ["alice"]
  let cBob : List String := ["bob"]
  let cAll : List String := ["alice", "bob"]
  let cEmpty : List String := []
  match controlCgs with
  | .error _ => [⟨"Gamen.Coalition: controlCgs fixture failed to build", false⟩]
  | .ok cgs =>
  [ -- Definition 1 (p. 152): Concurrent Game Structure. The "mkCgs accepts
    -- the control game" `it` (line 1273) is ported in `cgsCases`, above.
    ⟨"PaperCorrespondence.hs:1280 propositional: p holds at state 0 (labeling)",
      okIs (coalSatisfies cgs 0 p_) true⟩,
    ⟨"PaperCorrespondence.hs:1283 propositional: p does not hold at state 2 (labeling)",
      okIs (coalSatisfies cgs 2 p_) false⟩,
    ⟨"PaperCorrespondence.hs:1286-1288 propositional: q holds at state 0 and 2, not at 1 and 3",
      okIs (coalSatisfies cgs 0 q_) true && okIs (coalSatisfies cgs 1 q_) false
        && okIs (coalSatisfies cgs 2 q_) true && okIs (coalSatisfies cgs 3 q_) false⟩,

    -- Definition 3 (p. 153): [C]φ — one-step coalition effectivity.
    ⟨"PaperCorrespondence.hs:1292 [{alice}]p at state 0: alice plays 'p'; whatever bob \
      does, p holds next",
      okIs (coalSatisfies cgs 0 (.coalition cAlice p_)) true⟩,
    ⟨"PaperCorrespondence.hs:1297 [{alice}]p holds at ALL states (transition is \
      state-independent)",
      okIs (coalSatisfies cgs 0 (.coalition cAlice p_)) true
        && okIs (coalSatisfies cgs 1 (.coalition cAlice p_)) true
        && okIs (coalSatisfies cgs 2 (.coalition cAlice p_)) true
        && okIs (coalSatisfies cgs 3 (.coalition cAlice p_)) true⟩,
    ⟨"PaperCorrespondence.hs:1301 [{alice}]q at state 0 is FALSE: alice cannot control \
      bob's choice",
      okIs (coalSatisfies cgs 0 (.coalition cAlice q_)) false⟩,
    ⟨"PaperCorrespondence.hs:1306 [{bob}]q at state 0: bob plays 'q'; whatever alice \
      does, q holds next",
      okIs (coalSatisfies cgs 0 (.coalition cBob q_)) true⟩,
    ⟨"PaperCorrespondence.hs:1309 [{bob}]p at state 0 is FALSE: bob cannot control \
      alice's choice",
      okIs (coalSatisfies cgs 0 (.coalition cBob p_)) false⟩,
    ⟨"PaperCorrespondence.hs:1312 [{alice,bob}](p ∧ q): grand coalition plays (p, q) → state 0",
      okIs (coalSatisfies cgs 0 (.coalition cAll (.and p_ q_))) true⟩,
    ⟨"PaperCorrespondence.hs:1316 [{alice,bob}](p ∧ ¬q): grand coalition plays \
      (p, not-q) → state 1",
      okIs (coalSatisfies cgs 0 (.coalition cAll (.and p_ (.not q_)))) true⟩,
    ⟨"PaperCorrespondence.hs:1319 [{}](p ∧ q) is FALSE: bob can play 'not-q' so not all \
      successors have q",
      okIs (coalSatisfies cgs 0 (.coalition cEmpty (.and p_ q_))) false⟩,
    ⟨"PaperCorrespondence.hs:1324 ¬[{alice}]q holds at state 0 (negation of a false \
      coalition formula)",
      okIs (coalSatisfies cgs 0 (.not (.coalition cAlice q_))) true⟩,
    ⟨"PaperCorrespondence.hs:1327 [{alice}](p ∨ q) is TRUE: alice forces p, and p → p∨q",
      okIs (coalSatisfies cgs 0 (.coalition cAlice (.or p_ q_))) true⟩,
    ⟨"Not in gamen-hs: [{alice}]¬q at state 0 is FALSE — alice's own two moves alone \
      can't decide it (bob's \"q\" beats alice's \"p\", bob's \"q\" also beats alice's \
      \"not-p\"), unlike [{alice}]p/[{alice}]q above, where one of alice's two moves \
      happens to decide the target either way; this is the coalSatisfies analogue of \
      cgsCases' \"opponents-computed-wrong\" fixture note, and catches a coalSatisfies \
      [C]φ clause that quantifies the ∀ over the coalition's own moves instead of the \
      opponents' (that bug still gets every ported PaperCorrespondence.hs case above \
      right, by the same accident: none of their target propositions is controlled \
      solely by the opponent; filed as gamen-hs#52)",
      okIs (coalSatisfies cgs 0 (.coalition cAlice (.not q_))) false⟩,
    ⟨"Not in gamen-hs (no WorldGuardsSpec.hs coverage for Coalition, and \
      `grep -n coalSatisfies test/WorldGuardsSpec.hs test/RegressionIssue18.hs` finds \
      nothing): coalSatisfies errors on a state not in cgsStates (gamen-hs#7-style \
      guard, mirroring Gamen.Laca/Gamen.Stit/Gamen.Atl's world-existence guards) — \
      without it, an unseen state would silently satisfy every negative formula",
      isErr (coalSatisfies cgs 99 p_)⟩,

    -- Theorem 3.2 (p. 155): frame axioms N, ⊥, Mon, Super.
    ⟨"PaperCorrespondence.hs:1333 N — ⊤-effectivity: checkTopEffectivity returns True",
      checkTopEffectivity cgs⟩,
    ⟨"PaperCorrespondence.hs:1338 ⊥ — ⊥-monotonicity: checkBotMonotonicity returns True",
      checkBotMonotonicity cgs⟩,
    ⟨"PaperCorrespondence.hs:1343 Mon — monotonicity: preC({alice}, {0,1}) ⊆ \
      preC({alice}, {0,1,2})",
      checkMonotonicity cgs (Std.TreeSet.ofList ["alice"]) (Std.TreeSet.ofList [0, 1])
        (Std.TreeSet.ofList [2])⟩,
    ⟨"PaperCorrespondence.hs:1352 Super — superadditivity: disjoint {alice},{bob} \
      combine guarantees",
      checkSuperadditivity cgs (Std.TreeSet.ofList ["alice"]) (Std.TreeSet.ofList ["bob"])
        (Std.TreeSet.ofList [0, 1]) (Std.TreeSet.ofList [0, 2])⟩
  ]

/-! ## Atl.ModelCheck (`Gamen.Atl.ModelCheck`)

There is no `test/Atl*.hs` spec in gamen-hs — `find test -iname '*atl*'`
returns nothing. Ported here: from `test/PaperCorrespondence.hs`'s "Alur,
Henzinger & Kupferman (2002) — ATL" section, every `it` that calls only
`sat` (16 of the section's 25 `it`s, across the "Definition 3 (pp.
683–684): sat — global satisfaction sets", "Definition 3(1)"–"(4)", and
"AHK 2002 §3.2: ATL axioms" `describe` blocks); and, from the "Jamroga &
van der Hoek (2004) — ATLir" section, the two `sat`-only `it`s under "§4
Theorem: sat_ATL ≥ sat_ATLir" (the perfect-info half of each
strict-containment pair, reusing that section's `irCgs` fixture, which
needs only `Cgs`/`Formula`). Every sibling `it` in both sections also
calls `atlSatisfies` (`Gamen.Atl`), and the ATLir section's other `it`s
also call `atlirSat`/`atlirSatObjective`/`epistemicClasses`/
`uniformActions`/`subjectiveClass`/`allUniformStrategies`
(`Gamen.Atl.ImperfectInfo`) or `mkAtelModel` (`Gamen.Atel`); none of those
three modules was ported at the time (all three now are: `atlCases`,
`atelCases`, `atlirCases`), nor was the whole "van der Hoek & Wooldridge (2003) — ATEL" section and its
"Healthcare application" sub-block (every `it` there needs `Gamen.Atel`).

Two title/value mismatches found while porting, both kept as the Haskell
has them (filed as gamen-hs#51):
`test/PaperCorrespondence.hs`'s `it "sat(⟨⟨alice⟩⟩Xq) = {0}: …"` (line
1425) actually asserts `sat loop (CanNext al q_) \`shouldBe\` Set.fromList
[0, 1 :: Int]` — the title says `{0}`, the value checked is `{0,1}`; the
Haskell's own inline comments work through the arithmetic and arrive at
`{0,1}`, flagging the title as wrong themselves ("Hmm — so sat(⟨⟨alice⟩⟩Xq)
= {0,1}, not {0}"), but the title was never fixed.
`test/PaperCorrespondence.hs`'s `it "sat(⟨⟨alice⟩⟩Xp) = {1,2}: …"` (line
1443) actually asserts `sat loop (CanNext al p_) \`shouldBe\` Set.fromList
[0, 2 :: Int]` — the title says `{1,2}`, the value checked is `{0,2}`.
Both ported cases below check the value the Haskell test actually runs,
per "port every `it`", and each one's own comment flags its mismatch
instead of silently fixing the Haskell's title.

AHK 2002 is not among the PDFs in `gamen-hs/notes/` (`Gamen.Cgs`'s
docstring makes the same point about its own §2/§4 citations), so the page
numbers below are kept exactly as the Haskell's comments give them,
unverified against a primary source. -/

/-- Jamroga & van der Hoek (2004) imperfect-info example (Schobbens 2004,
§3), `PaperCorrespondence.hs` ~1725–1739: single agent `alice`, states
`{0,1,2}`, `p` only at state 2, moves `{"left","right"}` everywhere,
`(0,left)→2`, `(0,right)→0`, `(1,left)→1`, `(1,right)→2`, `2` absorbing. -/
private def irMoves (_ : Nat) (ag : String) : Std.TreeSet String :=
  if ag == "alice" then Std.TreeSet.ofList ["left", "right"] else ∅

private def irTrans : Nat → Std.TreeMap String String → Nat
  | 0, jm => if jm.get? "alice" == some "left" then 2 else 0
  | 1, jm => if jm.get? "alice" == some "right" then 2 else 1
  | _, _ => 2

private def irLabel : Nat → Std.TreeSet String
  | 2 => Std.TreeSet.ofList ["p"]
  | _ => ∅

private def irCgs : Cgs Nat String :=
  { cgsStates := Std.TreeSet.ofList [0, 1, 2]
    cgsAgents := Std.TreeSet.ofList ["alice"]
    cgsMoves := irMoves
    cgsTransition := irTrans
    cgsLabeling := irLabel }

/-- A zero-state CGS: `mkCgs` does not reject an empty state set (both of
its checks — no agent has an empty move set at any state; every joint
move is closed — are vacuously true when `states = ∅`), used by
`atlModelCheckCases`'s laziness cases below. Confirmed to build
successfully against gamen-hs directly (`cabal repl`,
`mkCgs Set.empty Set.empty (const (const Set.empty)) const (const Set.empty)`
→ `Right`, not an `error`). -/
private def zeroCgs : Except String (Cgs Nat String) :=
  mkCgs ∅ ∅ (fun _ _ => (∅ : Std.TreeSet String)) (fun s _ => s) (fun _ => (∅ : Std.TreeSet String))

def atlModelCheckCases : List Case :=
  let al : List String := ["alice"]
  let p_ : Formula := .atom "p"
  let q_ : Formula := .atom "q"
  [ -- Definition 3 (pp. 683–684): sat — global satisfaction sets.
    ⟨"sat(p) = {0}: only state 0 has 'p' in its labeling",
      match loopCgs with
      | .ok cgs => okIs (sat cgs p_) (Std.TreeSet.ofList [0])
      | .error _ => false⟩,
    ⟨"sat(q) = {1}: only state 1 has 'q' in its labeling",
      match loopCgs with
      | .ok cgs => okIs (sat cgs q_) (Std.TreeSet.ofList [1])
      | .error _ => false⟩,
    ⟨"sat(¬p) = {1,2}: complement of {0}",
      match loopCgs with
      | .ok cgs => okIs (sat cgs (.not p_)) (Std.TreeSet.ofList [1, 2])
      | .error _ => false⟩,
    ⟨"sat(p ∧ q) = ∅: p and q never hold simultaneously",
      match loopCgs with
      | .ok cgs => okIs (sat cgs (.and p_ q_)) ∅
      | .error _ => false⟩,
    ⟨"sat(p ∨ q) = {0,1}: union of the two singleton sets",
      match loopCgs with
      | .ok cgs => okIs (sat cgs (.or p_ q_)) (Std.TreeSet.ofList [0, 1])
      | .error _ => false⟩,
    -- Definition 3(1) (p. 684): ⟨⟨C⟩⟩Xφ = preC(C, sat(φ)).
    ⟨"sat(⟨⟨alice⟩⟩Xq) = {0,1}: title in PaperCorrespondence.hs says {0} (line 1425), but \
      its own inline comments work out {0,1} and the value it actually checks is {0,1} — \
      ported as run, not as titled (gamen-hs#51)",
      match loopCgs with
      | .ok cgs => okIs (sat cgs (.canNext al q_)) (Std.TreeSet.ofList [0, 1])
      | .error _ => false⟩,
    ⟨"sat(⟨⟨alice⟩⟩Xp) = {0,2}: title in PaperCorrespondence.hs says {1,2}, \
      but the value it actually checks is {0,2} — ported as run, not as titled (gamen-hs#51)",
      match loopCgs with
      | .ok cgs => okIs (sat cgs (.canNext al p_)) (Std.TreeSet.ofList [0, 2])
      | .error _ => false⟩,
    -- Definition 3(2) (p. 684): ⟨⟨C⟩⟩Gφ = ν X. sat(φ) ∩ preC(C, X).
    ⟨"sat(⟨⟨alice⟩⟩Gp) = {0}: alice can maintain p forever only from state 0",
      match loopCgs with
      | .ok cgs => okIs (sat cgs (.canAlways al p_)) (Std.TreeSet.ofList [0])
      | .error _ => false⟩,
    ⟨"sat(⟨⟨alice⟩⟩Gq) = {1}: alice can maintain q only from state 1",
      match loopCgs with
      | .ok cgs => okIs (sat cgs (.canAlways al q_)) (Std.TreeSet.ofList [1])
      | .error _ => false⟩,
    -- Definition 3(3) (p. 684): ⟨⟨C⟩⟩Fφ = μ X. sat(φ) ∪ preC(C, X).
    ⟨"sat(⟨⟨alice⟩⟩Fq) = {0,1,2}: alice can reach q from any state",
      match loopCgs with
      | .ok cgs => okIs (sat cgs (.canEventually al q_)) (Std.TreeSet.ofList [0, 1, 2])
      | .error _ => false⟩,
    ⟨"sat(⟨⟨alice⟩⟩Fp) = {0,1,2}: alice can also reach p from any state",
      match loopCgs with
      | .ok cgs => okIs (sat cgs (.canEventually al p_)) (Std.TreeSet.ofList [0, 1, 2])
      | .error _ => false⟩,
    -- Definition 3(4) (p. 684): ⟨⟨C⟩⟩(φ U ψ) = μ X. sat(ψ) ∪ (sat(φ) ∩ preC(C, X)).
    ⟨"sat(⟨⟨alice⟩⟩(p U q)) = {0,1}: alice can maintain p until q from states 0 and 1",
      match loopCgs with
      | .ok cgs => okIs (sat cgs (.canUntil al p_ q_)) (Std.TreeSet.ofList [0, 1])
      | .error _ => false⟩,
    -- AHK 2002 §3.2: ATL axioms (S, Mono, ⊤, ⊥).
    ⟨"S — ⟨⟨C⟩⟩Fφ ↔ φ ∨ ⟨⟨C⟩⟩X(⟨⟨C⟩⟩Fφ): unrolling of least fixpoint",
      match loopCgs with
      | .ok cgs =>
        okIs (sat cgs (.or p_ (.canNext al (.canEventually al p_))))
          (match sat cgs (.canEventually al p_) with | .ok s => s | .error _ => ∅)
      | .error _ => false⟩,
    ⟨"⊤-effectivity: ⟨⟨alice⟩⟩X⊤ holds everywhere (sat = all states)",
      match loopCgs with
      | .ok cgs => okIs (sat cgs (.canNext al (.not .bot))) cgs.cgsStates
      | .error _ => false⟩,
    ⟨"⊥-witness: ⟨⟨alice⟩⟩X⊥ = ∅ (no move forces ⊥)",
      match loopCgs with
      | .ok cgs => okIs (sat cgs (.canNext al .bot)) ∅
      | .error _ => false⟩,
    ⟨"Mono — sat monotone: sat(φ) ⊆ sat(φ ∨ ψ)",
      match loopCgs with
      | .ok cgs =>
        match sat cgs p_, sat cgs (.or p_ q_) with
        | .ok sp, .ok spq => sp.all fun w => spq.contains w
        | _, _ => false
      | .error _ => false⟩,
    -- Jamroga & van der Hoek (2004) — ATLir, §4 Theorem: sat_ATL ≥ sat_ATLir
    -- (the perfect-info `sat` half of each strict-containment pair; the
    -- `atlirSat` half is in `atlirCases`).
    ⟨"sat_ATL (⟨⟨alice⟩⟩ X p) = {0,1,2} — perfect info: each state picks the right action",
      okIs (sat irCgs (.canNext al p_)) (Std.TreeSet.ofList [0, 1, 2])⟩,
    ⟨"sat_ATL (⟨⟨alice⟩⟩ F p) = {0,1,2} — perfect info: alice picks optimally at each visit",
      okIs (sat irCgs (.canEventually al p_)) (Std.TreeSet.ofList [0, 1, 2])⟩,
    -- Not in gamen-hs: `lfp`/`gfp` have no fuel bound in the Haskell (there
    -- is nothing there to run out); this pins the Lean-only deviation
    -- (module docstring) that turns "iterate until stable" into
    -- `Except`-with-fuel, the same shape as `Tableau.transitiveClose`'s
    -- "errors when fuel runs out" case.
    ⟨"Not in gamen-hs: lfp errors when fuel runs out (no partial fixpoint)",
      isErr (lfp (fun x => x ∪ (Std.TreeSet.ofList [(0 : Nat)])) 0)⟩,
    ⟨"Not in gamen-hs: gfp errors when fuel runs out (no partial fixpoint)",
      isErr (gfp (Std.TreeSet.ofList [(0 : Nat), 1]) (fun x => x.filter (· == 0)) 0)⟩,
    -- Not in gamen-hs: `sat`'s eighteen unsupported-operator branches are
    -- `Except`, never a `panic!`/default (a representative sample; every
    -- branch's message is checked to match the Haskell verbatim in
    -- `Gamen.Atl.ModelCheck`'s own source comments).
    ⟨"Not in gamen-hs: sat errors on Box (not supported in ATL)",
      match loopCgs with
      | .ok cgs => isErr (sat cgs (.box p_))
      | .error _ => false⟩,
    ⟨"Not in gamen-hs: sat errors on Knowledge (needs Gamen.Atel)",
      match loopCgs with
      | .ok cgs => isErr (sat cgs (.knowledge "alice" p_))
      | .error _ => false⟩,
    ⟨"Not in gamen-hs: sat errors on Next (needs Gamen.Laca)",
      match loopCgs with
      | .ok cgs => isErr (sat cgs (.next p_))
      | .error _ => false⟩,
    ⟨"Not in gamen-hs: sat errors on Ought (needs Gamen.DeonticStit)",
      match loopCgs with
      | .ok cgs => isErr (sat cgs (.ought "alice" p_))
      | .error _ => false⟩,
    -- Not in gamen-hs: laziness. Each expected value/error below was
    -- checked directly against gamen-hs's `sat`, not derived from its
    -- source alone (`cabal repl`, `Gamen.Atl.ModelCheck`; see the module
    -- docstring's "Laziness" note for the full derivation).
    ⟨"Not in gamen-hs: laziness — sat(And Bot (Box p)) = ∅ on a nonempty-state \
      CGS: And's left conjunct (Bot) is empty, so Data.Set.intersection never \
      forces the right (Box, unsupported) — confirmed against gamen-hs \
      (`sat loop (And Bot (Box p_))` → `Right (fromList [])`)",
      match loopCgs with
      | .ok cgs => okIs (sat cgs (.and .bot (.box p_))) ∅
      | .error _ => false⟩,
    ⟨"Not in gamen-hs: laziness — sat(And p (Box p)) errors when p is nonempty \
      (sat(p) = {0}): the left conjunct being *nonempty* forces the right, \
      unlike the Bot case above — confirmed against gamen-hs",
      match loopCgs with
      | .ok cgs => isErr (sat cgs (.and p_ (.box p_)))
      | .error _ => false⟩,
    ⟨"Not in gamen-hs: laziness — sat(Not (Box p)) = ∅ on a zero-state CGS \
      (mkCgs does not reject cgsStates = ∅): Data.Set.difference ∅ e = ∅ \
      without forcing e, so Box's error is never reached — confirmed against \
      gamen-hs (`sat zeroCgs (Not (Box p_))` → `Right (fromList [])`)",
      match zeroCgs with
      | .ok cgs => okIs (sat cgs (.not (.box p_))) ∅
      | .error _ => false⟩,
    ⟨"Not in gamen-hs: laziness — sat(Implies (Box p) q) = ∅ on a zero-state \
      CGS: the antecedent's Box is inside a Set.difference states (...) with \
      states = ∅, so it is never forced — confirmed against gamen-hs",
      match zeroCgs with
      | .ok cgs => okIs (sat cgs (.implies (.box p_) q_)) ∅
      | .error _ => false⟩,
    ⟨"Not in gamen-hs: laziness — sat(Implies p (Box q)) errors on the SAME \
      zero-state CGS: the consequent is union's second argument, always \
      forced regardless of states/antecedent — confirmed against gamen-hs, \
      pinning the antecedent/consequent asymmetry above",
      match zeroCgs with
      | .ok cgs => isErr (sat cgs (.implies p_ (.box q_)))
      | .error _ => false⟩,
    ⟨"Not in gamen-hs: laziness — sat(Iff Bot (Box p)) errors on a \
      NONEMPTY-state CGS even though the left side is Bot: Iff's own \
      Set.union sl sr unconditionally forces sr once states is nonempty, \
      unlike And — confirmed against gamen-hs (`sat loop (Iff Bot (Box p_))`)",
      match loopCgs with
      | .ok cgs => isErr (sat cgs (.iff .bot (.box p_)))
      | .error _ => false⟩,
    ⟨"Not in gamen-hs: laziness — sat(Iff p (Box q)) = ∅ on a zero-state CGS: \
      sl (=sat(p) = ∅, states empty) forces first and is empty, so — with \
      states also empty — sr (Box q) is skipped, unlike the nonempty-state \
      case above — confirmed against gamen-hs",
      match zeroCgs with
      | .ok cgs => okIs (sat cgs (.iff p_ (.box q_))) ∅
      | .error _ => false⟩,
    ⟨"Not in gamen-hs: laziness — sat(Iff (Box p) q) errors on a zero-state \
      CGS: Iff's left side (sl) is always forced, in every case — confirmed \
      against gamen-hs",
      match zeroCgs with
      | .ok cgs => isErr (sat cgs (.iff (.box p_) q_))
      | .error _ => false⟩,
    -- Not in gamen-hs: error order when both operands error, and preC's
    -- laziness. Expected values and error texts from gamen-hs's own `sat`
    -- in GHCi (`cabal repl lib:gamen`, 2026-09-29), on `irCgs`, `zeroCgs`,
    -- and `irCgs` with a moveless second agent `bob`.
    ⟨"Not in gamen-hs: error order — sat(Or (Box p) (Diamond p)) raises the \
      Diamond error (Set.union forces its second argument first; GHCi)",
      errIs (sat irCgs (.or (.box p_) (.diamond p_))) "Diamond not supported in ATL"⟩,
    ⟨"Not in gamen-hs: error order — sat(Implies (Box p) (Diamond p)) raises \
      the Diamond error, on irCgs and on a zero-state CGS (GHCi)",
      errIs (sat irCgs (.implies (.box p_) (.diamond p_))) "Diamond not supported in ATL"
        && (match zeroCgs with
            | .ok cgs =>
                errIs (sat cgs (.implies (.box p_) (.diamond p_))) "Diamond not supported in ATL"
            | .error _ => false)⟩,
    ⟨"Not in gamen-hs: error order — sat(Iff (Box p) (Diamond p)) raises the \
      Diamond error on irCgs, the Box error on a zero-state CGS (GHCi)",
      errIs (sat irCgs (.iff (.box p_) (.diamond p_))) "Diamond not supported in ATL"
        && (match zeroCgs with
            | .ok cgs =>
                errIs (sat cgs (.iff (.box p_) (.diamond p_)))
                  "Box not supported in ATL; use ⟨⟨Ag⟩⟩G for grand-coalition invariance"
            | .error _ => false)⟩,
    ⟨"Not in gamen-hs: laziness — preC forces its target only at a membership \
      test: sat(⟨⟨alice⟩⟩X Box p) = ∅ on a zero-state CGS and {0,1,2} with a \
      moveless opponent; sat([bob] Box p) = ∅ (bob has no moves); GHCi",
      (match zeroCgs with
       | .ok cgs => okIs (sat cgs (.canNext al (.box p_))) ∅
       | .error _ => false)
        && okIs (sat { irCgs with cgsAgents := Std.TreeSet.ofList ["alice", "bob"] }
              (.canNext al (.box p_))) (Std.TreeSet.ofList [0, 1, 2])
        && okIs (sat irCgs (.coalition ["bob"] (.box p_))) ∅
        && errIs (sat irCgs (.canNext al (.box p_)))
              "Box not supported in ATL; use ⟨⟨Ag⟩⟩G for grand-coalition invariance"⟩
  ]

/-! ## Atl (`Gamen.Atl`)

There is no `test/Atl*.hs` spec in gamen-hs (`find test -iname '*atl*'`
returns nothing, per `Gamen.Atl.ModelCheck`'s row above). Ported here,
from `test/PaperCorrespondence.hs`: every `it` in the "Alur, Henzinger &
Kupferman (2002) — ATL" section that calls `atlSatisfies` (the other 10
of that section's 26 `it`s, complementing `atlModelCheckCases`'s 16
`sat`-only ones — the "Definition 3(1)"/"(2)"/"(4)" and "sat(⟨⟨alice⟩⟩Fq)"
`describe` blocks), plus the "Herzig, Lorini & Perrotin (2022) — LACA"
section's "lacaToCgs coercion" sub-block's last three `it`s (`atlSatisfies`
× 2, `sat` × 1 — held back together in `Gamen.Laca`'s and `Gamen.Cgs`'s
rows pending this module, and ported together here). Every other
`atlSatisfies`/`atlIsTrueIn`-calling `it` in gamen-hs's `test/` (checked:
`grep -n atlSatisfies test/*.hs`, `grep -n atlIsTrueIn test/*.hs` — the
latter has zero hits anywhere in gamen-hs) is one of these 12. `atlIsTrueIn`
itself is exercised by no gamen-hs test at all; the two cases below marked
"Not in gamen-hs" cover it directly. AHK 2002 page numbers kept exactly as
the Haskell's comments give them (see `atlModelCheckCases`'s docstring),
unverified against a primary source. -/

def atlCases : List Case :=
  let al : List String := ["alice"]
  let p_ : Formula := .atom "p"
  let q_ : Formula := .atom "q"
  let h_ : Formula := .atom "h"
  -- `test/PaperCorrespondence.hs`'s LACA fixture (Example 1, p. 2649):
  -- agent "1" controls h, "2" controls w; both false initially. Same
  -- fixture as `Gamen.Laca`'s `lacaModelHW`/`lacaS0`, defined locally here
  -- since this section runs before those `private def`s below.
  let lacaModelHW' : LacaModel := mkLacaModel [("h", "1"), ("w", "2")]
  let lacaS0' : LacaState := Std.TreeMap.ofList [("h", false), ("w", false)]
  let cgs' := lacaToCgs lacaModelHW'
  [ -- Definition 3(1) (p. 684): ⟨⟨C⟩⟩Xφ = preC(C, sat(φ)).
    ⟨"⟨⟨alice⟩⟩Xq holds at state 0: alice plays 'next', landing at 1 (q)",
      match loopCgs with
      | .ok cgs => okIs (atlSatisfies cgs 0 (.canNext al q_)) true
      | .error _ => false⟩,
    ⟨"⟨⟨alice⟩⟩Xq holds at state 1: alice plays 'stay', staying at 1 (q)",
      match loopCgs with
      | .ok cgs => okIs (atlSatisfies cgs 1 (.canNext al q_)) true
      | .error _ => false⟩,
    ⟨"⟨⟨alice⟩⟩Xq is FALSE at state 2: no move leads to a state with q",
      match loopCgs with
      | .ok cgs => okIs (atlSatisfies cgs 2 (.canNext al q_)) false
      | .error _ => false⟩,
    -- Definition 3(2) (p. 684): ⟨⟨C⟩⟩Gφ = ν X. sat(φ) ∩ preC(C, X).
    ⟨"⟨⟨alice⟩⟩Gp holds at state 0 (play 'stay' forever)",
      match loopCgs with
      | .ok cgs => okIs (atlSatisfies cgs 0 (.canAlways al p_)) true
      | .error _ => false⟩,
    ⟨"⟨⟨alice⟩⟩Gp is FALSE at state 1: p does not hold at 1",
      match loopCgs with
      | .ok cgs => okIs (atlSatisfies cgs 1 (.canAlways al p_)) false
      | .error _ => false⟩,
    ⟨"⟨⟨alice⟩⟩Gp is FALSE at state 2: p does not hold at 2",
      match loopCgs with
      | .ok cgs => okIs (atlSatisfies cgs 2 (.canAlways al p_)) false
      | .error _ => false⟩,
    -- Definition 3(3) (p. 684): ⟨⟨C⟩⟩Fφ = μ X. sat(φ) ∪ preC(C, X).
    ⟨"⟨⟨alice⟩⟩Fq holds at all states: alice can always reach q",
      match loopCgs with
      | .ok cgs =>
        [0, 1, 2].all fun s => okIs (atlSatisfies cgs s (.canEventually al q_)) true
      | .error _ => false⟩,
    -- Definition 3(4) (p. 684): ⟨⟨C⟩⟩(φ U ψ) = μ X. sat(ψ) ∪ (sat(φ) ∩ preC(C, X)).
    ⟨"⟨⟨alice⟩⟩(p U q) holds at state 0: play 'next' (p holds now, q holds at state 1)",
      match loopCgs with
      | .ok cgs => okIs (atlSatisfies cgs 0 (.canUntil al p_ q_)) true
      | .error _ => false⟩,
    ⟨"⟨⟨alice⟩⟩(p U q) holds at state 1: q already holds (until satisfied immediately)",
      match loopCgs with
      | .ok cgs => okIs (atlSatisfies cgs 1 (.canUntil al p_ q_)) true
      | .error _ => false⟩,
    ⟨"⟨⟨alice⟩⟩(p U q) is FALSE at state 2: p does not hold here, q not yet reached",
      match loopCgs with
      | .ok cgs => okIs (atlSatisfies cgs 2 (.canUntil al p_ q_)) false
      | .error _ => false⟩,
    -- "lacaToCgs coercion" sub-block, Gamen.Laca §3.1 (the three `it`s
    -- held back from `lacaPaperCorrespondenceCases`/`cgsCases`).
    ⟨"atlSatisfies cgs' s0 (⟨⟨1⟩⟩ X h) = True — agent 1 attempts h, flips it \
      regardless of agent 2",
      okIs (atlSatisfies cgs' lacaS0' (.canNext ["1"] h_)) true⟩,
    ⟨"atlSatisfies cgs' s0 (⟨⟨2⟩⟩ X h) = False — agent 2 controls w, cannot guarantee h",
      okIs (atlSatisfies cgs' lacaS0' (.canNext ["2"] h_)) false⟩,
    ⟨"sat cgs' (⟨⟨1⟩⟩ F h) = all states — agent 1 can always flip h in one step",
      okIs (sat cgs' (.canEventually ["1"] h_)) cgs'.cgsStates⟩,
    -- Not in gamen-hs (no `atlIsTrueIn` call anywhere in gamen-hs's
    -- `test/`): sanity checks on the raw function, mirroring `sat`'s own
    -- fixtures.
    ⟨"Not in gamen-hs: atlIsTrueIn loop p is False — p only holds at state 0, not 1 or 2",
      match loopCgs with
      | .ok cgs => okIs (atlIsTrueIn cgs p_) false
      | .error _ => false⟩,
    ⟨"Not in gamen-hs: atlIsTrueIn loop (⟨⟨alice⟩⟩Fq) is True — alice can reach q \
      from every state",
      match loopCgs with
      | .ok cgs => okIs (atlIsTrueIn cgs (.canEventually al q_)) true
      | .error _ => false⟩,
    -- Not in gamen-hs: `atlSatisfies`'s world-existence guard (gamen-hs#7
    -- pattern, matching every other module's `s*Satisfies`/`x*Satisfies`).
    ⟨"Not in gamen-hs: atlSatisfies errors on a state not in cgsStates",
      match loopCgs with
      | .ok cgs => isErr (atlSatisfies cgs 99 p_)
      | .error _ => false⟩
  ]

/-! ## Laca (`Gamen.Laca`)

Port of `test/LacaSpec.hs` in full (11 `it`s across its three describe
blocks: "LACA formula construction" — 2, on plain `Formula` behavior
(`Next`'s `show`/`isModalFree`), already covered generically by
`Gamen.Formula`'s own tests but ported here too since they live in
`LacaSpec.hs`; "LACA state operations" — 2; "LACA satisfaction" — 7),
plus `test/WorldGuardsSpec.hs`:55–65's two `lSatisfies` `it`s (the last
of the "World-existence guards (gamen-hs#7)" describe block to be
ported — see the comment on `proveCases`'s `dsSatisfies` case above for
where its `eSatisfies`/`sSatisfies`/`xSatisfies` siblings live). -/

/-- `test/LacaSpec.hs`/`herzig2022-correspondence.md`'s shared fixture:
Example 1 (p. 2649) — agent "1" controls `h` (heating), "2" controls `w`
(window); both false initially. -/
private def lacaModelHW : LacaModel := mkLacaModel [("h", "1"), ("w", "2")]

private def lacaS0 : LacaState := Std.TreeMap.ofList [("h", false), ("w", false)]

def lacaCases : List Case := [
  -- "LACA formula construction"
  ⟨"displays Next", toString (Formula.next (.atom "p")) == "Xp"⟩,
  ⟨"Next is not modal-free", (Formula.next (.atom "p")).isModalFree == false⟩,
  -- "LACA state operations"
  ⟨"computes successor state",
    let s1 := succState lacaS0 (Std.TreeSet.ofList ["h"])
    stateValue s1 "h" == true && stateValue s1 "w" == false⟩,
  ⟨"generates trajectories",
    -- With attempt {h}, trajectory: h=F -> h=T -> h=F (cycle detected).
    let traj := trajectory lacaS0 (Std.TreeSet.ofList ["h"]) 10
    traj.length == 3
      && stateValue (traj.getD 0 ∅) "h" == false
      && stateValue (traj.getD 1 ∅) "h" == true⟩,
  -- "LACA satisfaction"
  ⟨"evaluates atoms at current state",
    okIs (lSatisfies lacaModelHW lacaS0 ∅ (.atom "h")) false
      && okIs (lSatisfies lacaModelHW lacaS0 ∅ (.atom "w")) false⟩,
  ⟨"evaluates Next (X operator)",
    okIs (lSatisfies lacaModelHW lacaS0 (Std.TreeSet.ofList ["h"]) (.next (.atom "h"))) true
      && okIs (lSatisfies lacaModelHW lacaS0 (Std.TreeSet.ofList ["h"]) (.next (.atom "w"))) false⟩,
  ⟨"evaluates G (always future)",
    okIs (lSatisfies lacaModelHW lacaS0 ∅ (.futureBox (.not (.atom "h")))) true
      && okIs (lSatisfies lacaModelHW lacaS0 (Std.TreeSet.ofList ["h"]) (.futureBox (.atom "h"))) false⟩,
  ⟨"evaluates F (eventually)",
    okIs (lSatisfies lacaModelHW lacaS0 (Std.TreeSet.ofList ["h"]) (.futureDiamond (.atom "h"))) true
      && okIs (lSatisfies lacaModelHW lacaS0 ∅ (.futureDiamond (.atom "h"))) false⟩,
  ⟨"evaluates [i cstit] (Chellas stit)",
    okIs (lSatisfies lacaModelHW lacaS0 (Std.TreeSet.ofList ["h"]) (.stit "1" (.next (.atom "h")))) true
      && okIs (lSatisfies lacaModelHW lacaS0 ∅ (.stit "2" (.next (.atom "h")))) false⟩,
  ⟨"evaluates □ (historical necessity, was Settled)",
    okIs (lSatisfies lacaModelHW lacaS0 ∅ (.box (.next (.atom "h")))) false⟩,
  ⟨"evaluates deliberative stit",
    okIs (lSatisfies lacaModelHW lacaS0 (Std.TreeSet.ofList ["h"])
      (Formula.dstit "1" (.next (.atom "h")))) true⟩,
  -- test/WorldGuardsSpec.hs:55–65.
  ⟨"lSatisfies errors on state with stray atom",
    let lm := mkLacaModel [("p", "ag"), ("q", "ag")]
    let stray : LacaState := Std.TreeMap.ofList [("p", true), ("q", false), ("zzz", true)]
    isErr (lSatisfies lm stray ∅ (.atom "p"))⟩,
  ⟨"lSatisfies errors on state missing an atom",
    let lm := mkLacaModel [("p", "ag"), ("q", "ag")]
    let partialState : LacaState := Std.TreeMap.ofList [("p", true)]
    isErr (lSatisfies lm partialState ∅ (.atom "p"))⟩
]

/-! ## Laca (`test/PaperCorrespondence.hs`)

The "Herzig, Lorini & Perrotin (2022) — LACA" section: "Section 2.2 (p.
2649): succState" (4 `it`s) and "Section 3.2 (p. 2650): truth conditions"
(8 `it`s) in full, plus the four `Cgs`-primitive `it`s of the
"lacaToCgs coercion" sub-block (`cgsStates`, `cgsAgents`, two
`cgsLabeling`). Page numbers checked against `notes/Lorini2022.pdf`
(Herzig, Lorini & Perrotin, *IJCAI 2022*, pp. 2648–2654) and are correct.

The sub-block's other three `it`s (`atlSatisfies cgs' s0
(CanNext ["1"] h_)`, `atlSatisfies cgs' s0 (CanNext ["2"] h_)`, and
`sat cgs' (CanEventually ["1"] h_)`) are ported in `atlCases`, above,
`Gamen.Atl`'s section. -/

def lacaPaperCorrespondenceCases : List Case := [
  -- Section 2.2 (p. 2649): succState — attempt flips the controlled atom.
  ⟨"succState s0 {h} = {h=True, w=False}: h flips, w unchanged",
    succState lacaS0 (Std.TreeSet.ofList ["h"]) ==
      Std.TreeMap.ofList [("h", true), ("w", false)]⟩,
  ⟨"succState s0 {w} = {h=False, w=True}: w flips, h unchanged",
    succState lacaS0 (Std.TreeSet.ofList ["w"]) ==
      Std.TreeMap.ofList [("h", false), ("w", true)]⟩,
  ⟨"succState s0 {h,w} = {h=True, w=True}: both atoms flip",
    succState lacaS0 (Std.TreeSet.ofList ["h", "w"]) ==
      Std.TreeMap.ofList [("h", true), ("w", true)]⟩,
  ⟨"succState s0 ∅ = s0: empty attempt leaves state unchanged",
    succState lacaS0 ∅ == lacaS0⟩,
  -- Section 3.2 (p. 2650): truth conditions — X, G, □, ◇, [J cstit].
  ⟨"¬h ∧ ¬w = True at (s0, ∅): both atoms false initially",
    okIs (lSatisfies lacaModelHW lacaS0 ∅ (.and (.not (.atom "h")) (.not (.atom "w")))) true⟩,
  ⟨"X h = True at (s0, {h}): next state has h=True",
    okIs (lSatisfies lacaModelHW lacaS0 (Std.TreeSet.ofList ["h"]) (.next (.atom "h"))) true⟩,
  ⟨"X(¬h) = True at (s0, ∅): h stays False with empty attempt",
    okIs (lSatisfies lacaModelHW lacaS0 ∅ (.next (.not (.atom "h")))) true⟩,
  ⟨"G(¬h) = True at (s0, ∅): h remains False throughout trajectory",
    okIs (lSatisfies lacaModelHW lacaS0 ∅ (.futureBox (.not (.atom "h")))) true⟩,
  ⟨"◇(X h) = True at (s0, ∅): attempt {h} achieves h at next step",
    okIs (lSatisfies lacaModelHW lacaS0 ∅ (.diamond (.next (.atom "h")))) true⟩,
  ⟨"□(X h) = False at (s0, ∅): empty attempt leaves h False",
    okIs (lSatisfies lacaModelHW lacaS0 ∅ (.box (.next (.atom "h")))) false⟩,
  ⟨"[1 cstit](X h) = True at (s0, {h}): agent 1 guarantees h flips regardless of agent 2",
    okIs (lSatisfies lacaModelHW lacaS0 (Std.TreeSet.ofList ["h"])
      (.stit "1" (.next (.atom "h")))) true⟩,
  ⟨"[2 cstit](X h) = False at (s0, ∅): agent 2 controls w, cannot guarantee h flips",
    okIs (lSatisfies lacaModelHW lacaS0 ∅ (.stit "2" (.next (.atom "h")))) false⟩,
  -- lacaToCgs coercion: LACA model as a restricted CGS (Gamen.Laca §3.1) —
  -- `Cgs`-only slice of the sub-block.
  ⟨"cgsStates has 2^2 = 4 states (all valuations over {h,w})",
    (lacaToCgs lacaModelHW).cgsStates.size == 4⟩,
  ⟨"cgsAgents = {1, 2}",
    (lacaToCgs lacaModelHW).cgsAgents == Std.TreeSet.ofList ["1", "2"]⟩,
  ⟨"cgsLabeling s0 = ∅ (both atoms false)",
    (lacaToCgs lacaModelHW).cgsLabeling lacaS0 == ∅⟩,
  ⟨"cgsLabeling sH = {h} (only h is true)",
    (lacaToCgs lacaModelHW).cgsLabeling (Std.TreeMap.ofList [("h", true), ("w", false)])
      == Std.TreeSet.ofList ["h"]⟩
]

/-! ## Atel (`Gamen.Atel`)

There is no `test/AtelSpec.hs` in gamen-hs (`for f in AtelModel mkAtelModel
atelSat atelSatisfies atelIsTrueIn; do grep -lw "$f" test/*.hs; done` hits
only `PaperCorrespondence.hs` and `RegressionIssue18.hs`). Ported here:

- the full "van der Hoek & Wooldridge (2003) — ATEL" section of
  `test/PaperCorrespondence.hs` (19 `it`s: its "Definition 3(i)" block over
  the loop+epistemic model — the same AHK loop CGS as `cgsCases`/`atlCases`'
  `loopCgs`, reused here — its "Definition 3(ii)" block, and its
  "Healthcare application: surgical-team coordination" block over the
  surgical-safety model);
- `test/RegressionIssue18.hs`'s "B2/B7: ATLir semantics and iCGS
  validation" describe block's two `mkAtelModel`-only `it`s ("B7:
  mkAtelModel rejects a non-symmetric epistemic relation", "B7: mkAtelModel
  rejects differing move sets across indistinguishable states"). The same
  block's other three `it`s (`atlirSat`, `atlirSatObjective`,
  `subjectiveClass`) are in `atlirRegressionCases`
  (`Gamen.Atl.ImperfectInfo`).

The "Jamroga & van der Hoek (2004) — ATLir" section's `epistemicClasses`
`it` (`test/PaperCorrespondence.hs` ~1753–1758) is ported in `atlirCases`
(`Gamen.Atl.ImperfectInfo`).

van der Hoek & Wooldridge (2003), *Cooperation, Knowledge, and Time:
Alternating-time Temporal Epistemic Logic*, Studia Logica 75(1): 125–157 —
matches `Gamen.Atel`'s module docstring, unverified against a primary
source (not among the PDFs in `gamen-hs/notes/`, same as AHK 2002). -/

/-- The loop model's epistemic relation (`PaperCorrespondence.hs` ~1580–1582):
alice's class at state 0 is `{0}`; at 1 and 2 it is `{1,2}`. -/
private def loopEpistemic (_ : String) : Nat → Std.TreeSet Nat
  | 0 => Std.TreeSet.ofList [0]
  | _ => Std.TreeSet.ofList [1, 2]

/-- Surgical-safety CGS (`PaperCorrespondence.hs` ~1630–1647). States:
0 = allergy-unknown/pre-op, 1 = allergy-known/pre-op, 2 = safe-completion.
Agents "anes" (anesthesiologist), "surg" (surgeon). -/
private def surgMoves : Nat → String → Std.TreeSet String
  | _, "anes" => Std.TreeSet.ofList ["alert", "proceed"]
  | _, "surg" => Std.TreeSet.ofList ["operate", "wait"]
  | _, _ => ∅

private def surgTrans : Nat → Std.TreeMap String String → Nat
  | 0, jm => if jm.get? "anes" == some "alert" then 1 else 0
  | 1, jm => if jm.get? "surg" == some "operate" then 2 else 1
  | _, _ => 2

private def surgLabel : Nat → Std.TreeSet String
  | 0 => ∅
  | 1 => Std.TreeSet.ofList ["safe"]
  | _ => Std.TreeSet.ofList ["safe", "complete"]

private def surgCgs : Except String (Cgs Nat String) :=
  mkCgs (Std.TreeSet.ofList [0, 1, 2]) (Std.TreeSet.ofList ["anes", "surg"])
    surgMoves surgTrans surgLabel

/-- Surgical model's epistemic relation (`PaperCorrespondence.hs` ~1648–1652):
"anes" has complete information; "surg" can't distinguish 0 from 1. -/
private def surgEpistemic : String → Nat → Std.TreeSet Nat
  | "anes", s => Std.TreeSet.ofList [s]
  | "surg", 2 => Std.TreeSet.ofList [2]
  | "surg", _ => Std.TreeSet.ofList [0, 1]
  | _, s => Std.TreeSet.ofList [s]

private def atelLoopModel : Except String (AtelModel Nat String) := do
  let cgs ← loopCgs
  mkAtelModel cgs loopEpistemic

private def atelSurgModel : Except String (AtelModel Nat String) := do
  let cgs ← surgCgs
  mkAtelModel cgs surgEpistemic

/-- Alice's epistemic relation for the ATLir section
(`PaperCorrespondence.hs` ~1741–1745): `{0,1}` and `{2}`. -/
private def irEpistemic : String → Nat → Std.TreeSet Nat
  | "alice", 0 => Std.TreeSet.ofList [0, 1]
  | "alice", 1 => Std.TreeSet.ofList [0, 1]
  | "alice", _ => Std.TreeSet.ofList [2]
  | _, s => Std.TreeSet.ofList [s]

private def irModel : Except String (AtelModel Nat String) :=
  mkAtelModel irCgs irEpistemic

private def withIr (k : AtelModel Nat String → Bool) : Bool :=
  match irModel with
  | .ok m => k m
  | .error _ => false

/-- `irCgs` with a second agent `bob` who has no moves anywhere
(`irMoves` gives non-`alice` agents `∅`). Built without `mkCgs`, which
would reject it; `mkAtelModel` accepts it. With coalition `{alice}`, the
opponents' joint-move list is empty at every state, so `preC` never tests
membership. -/
private def irBobModel : Except String (AtelModel Nat String) :=
  mkAtelModel { irCgs with cgsAgents := Std.TreeSet.ofList ["alice", "bob"] } irEpistemic

/-- A zero-state ATEL model (over `zeroCgs`, `Gamen.Atl.ModelCheck`'s row):
the epistemic relation is trivially reflexive/symmetric/transitive/uniform
when there are no states to check, so `mkAtelModel` accepts it. Used by
`atelCases`'s laziness cases below, mirroring `atlModelCheckCases`'s. -/
private def zeroAtelModel : Except String (AtelModel Nat String) := do
  let cgs ← zeroCgs
  mkAtelModel cgs (fun _ _ => (∅ : Std.TreeSet Nat))

def atelCases : List Case :=
  let al : List String := ["alice"]
  let p_ : Formula := .atom "p"
  let q_ : Formula := .atom "q"
  let team : List String := ["anes", "surg"]
  let surgOnly : List String := ["surg"]
  let safe_ : Formula := .atom "safe"
  let complete_ : Formula := .atom "complete"
  [ -- Definition 3(i) (p. 134): K_a φ = { s | class_a(s) ⊆ sat(φ) }.
    ⟨"mkAtelModel accepts the loop+epistemic model (reflexivity satisfied)",
      match loopCgs with
      | .ok cgs => match mkAtelModel cgs loopEpistemic with
        | .ok _ => true
        | .error _ => false
      | .error _ => false⟩,
    ⟨"K_alice p at state 0 is TRUE: class({0}) = {0} ⊆ sat(p)={0}",
      match atelLoopModel with
      | .ok m => okIs (atelSatisfies m 0 (.knowledge "alice" p_)) true
      | .error _ => false⟩,
    ⟨"K_alice p at state 1 is FALSE: class({1}) = {1,2} ⊄ sat(p)={0}",
      match atelLoopModel with
      | .ok m => okIs (atelSatisfies m 1 (.knowledge "alice" p_)) false
      | .error _ => false⟩,
    ⟨"K_alice ¬p at state 1 is TRUE: {1,2} ⊆ sat(¬p)={1,2}",
      match atelLoopModel with
      | .ok m => okIs (atelSatisfies m 1 (.knowledge "alice" (.not p_))) true
      | .error _ => false⟩,
    ⟨"K_alice q at state 1 is FALSE: {1,2} ⊄ sat(q)={1}",
      match atelLoopModel with
      | .ok m => okIs (atelSatisfies m 1 (.knowledge "alice" q_)) false
      | .error _ => false⟩,
    ⟨"K_alice q at state 2 is FALSE: same class {1,2} ⊄ {1}",
      match atelLoopModel with
      | .ok m => okIs (atelSatisfies m 2 (.knowledge "alice" q_)) false
      | .error _ => false⟩,
    ⟨"K_alice ¬q at state 0 is TRUE: class {0} ⊆ sat(¬q)={0,2}",
      match atelLoopModel with
      | .ok m => okIs (atelSatisfies m 0 (.knowledge "alice" (.not q_))) true
      | .error _ => false⟩,
    -- Definition 3(ii) (p. 134): K_a(⟨⟨C⟩⟩φ) — knowing strategic ability.
    ⟨"K_alice(⟨⟨alice⟩⟩Fq) holds everywhere: alice knows she can always reach q",
      match atelLoopModel with
      | .ok m => [0, 1, 2].all fun s =>
          okIs (atelSatisfies m s (.knowledge "alice" (.canEventually al q_))) true
      | .error _ => false⟩,
    ⟨"K_alice(⟨⟨alice⟩⟩Gq) at state 1 is FALSE: {1,2} ⊄ sat(⟨⟨alice⟩⟩Gq)={1}",
      match atelLoopModel with
      | .ok m => okIs (atelSatisfies m 1 (.knowledge "alice" (.canAlways al q_))) false
      | .error _ => false⟩,
    ⟨"K_alice(⟨⟨alice⟩⟩Gq) at state 0 is FALSE: class {0} ⊄ {1}",
      match atelLoopModel with
      | .ok m => okIs (atelSatisfies m 0 (.knowledge "alice" (.canAlways al q_))) false
      | .error _ => false⟩,
    -- Healthcare application: surgical-team coordination.
    ⟨"⟨⟨team⟩⟩F complete = {0,1,2}: team can ensure completion from any state",
      match atelSurgModel with
      | .ok m => okIs (atelSat m (.canEventually team complete_)) (Std.TreeSet.ofList [0, 1, 2])
      | .error _ => false⟩,
    ⟨"⟨⟨surg⟩⟩F complete = {1,2}: surgeon alone cannot force it from state 0",
      match atelSurgModel with
      | .ok m => okIs (atelSat m (.canEventually surgOnly complete_)) (Std.TreeSet.ofList [1, 2])
      | .error _ => false⟩,
    ⟨"K_surg(⟨⟨team⟩⟩F complete) at state 0: surgeon knows team can succeed",
      match atelSurgModel with
      | .ok m => okIs (atelSatisfies m 0 (.knowledge "surg" (.canEventually team complete_))) true
      | .error _ => false⟩,
    ⟨"K_surg(⟨⟨surg⟩⟩F complete) at state 0: FALSE — surg doesn't know if alone is enough",
      match atelSurgModel with
      | .ok m => okIs (atelSatisfies m 0 (.knowledge "surg" (.canEventually surgOnly complete_))) false
      | .error _ => false⟩,
    ⟨"K_anes safe at state 1: TRUE — anes has complete info, knows allergy is handled",
      match atelSurgModel with
      | .ok m => okIs (atelSatisfies m 1 (.knowledge "anes" safe_)) true
      | .error _ => false⟩,
    ⟨"K_anes safe at state 0: FALSE — anes knows allergy is NOT handled (complete info)",
      match atelSurgModel with
      | .ok m => okIs (atelSatisfies m 0 (.knowledge "anes" safe_)) false
      | .error _ => false⟩,
    ⟨"K_surg safe at state 1: FALSE — surg can't distinguish safe state 1 from unsafe 0",
      match atelSurgModel with
      | .ok m => okIs (atelSatisfies m 1 (.knowledge "surg" safe_)) false
      | .error _ => false⟩,
    ⟨"K_anes(⟨⟨team⟩⟩F complete) holds everywhere: anes with complete info knows team \
      can always succeed",
      match atelSurgModel with
      | .ok m => [0, 1, 2].all fun s =>
          okIs (atelSatisfies m s (.knowledge "anes" (.canEventually team complete_))) true
      | .error _ => false⟩,
    ⟨"atelSat of tautology (¬⊥) = all states",
      match atelSurgModel, surgCgs with
      | .ok m, .ok cgs => okIs (atelSat m (.not .bot)) cgs.cgsStates
      | _, _ => false⟩,
    -- Not in gamen-hs: laziness. `atelSat`'s propositional connectives
    -- follow `Gamen.Atl.ModelCheck.sat`'s laziness fix exactly (same
    -- fixtures/values as `atlModelCheckCases`'s laziness cases, confirmed
    -- against gamen-hs the same way — see `Gamen.Atl.ModelCheck`'s
    -- docstring for the full derivation).
    ⟨"Not in gamen-hs: laziness — atelSat(And Bot (Box p)) = ∅ on a \
      nonempty-state model: the left conjunct (Bot) is empty, so Box \
      (unsupported) is never forced",
      match atelLoopModel with
      | .ok m => okIs (atelSat m (.and .bot (.box p_))) ∅
      | .error _ => false⟩,
    ⟨"Not in gamen-hs: laziness — atelSat(And p (Box p)) errors when p is \
      nonempty (sat(p) = {0} on the loop model)",
      match atelLoopModel with
      | .ok m => isErr (atelSat m (.and p_ (.box p_)))
      | .error _ => false⟩,
    ⟨"Not in gamen-hs: laziness — atelSat(Not (Box p)) = ∅ on a zero-state \
      ATEL model (mkAtelModel accepts cgsStates = ∅)",
      match zeroAtelModel with
      | .ok m => okIs (atelSat m (.not (.box p_))) ∅
      | .error _ => false⟩,
    ⟨"Not in gamen-hs: laziness — atelSat(Implies (Box p) q) = ∅ on the SAME \
      zero-state model: antecedent's Box never forced when states = ∅",
      match zeroAtelModel with
      | .ok m => okIs (atelSat m (.implies (.box p_) q_)) ∅
      | .error _ => false⟩,
    ⟨"Not in gamen-hs: laziness — atelSat(Implies p (Box q)) errors on the \
      SAME zero-state model: consequent always forced, pinning the \
      antecedent/consequent asymmetry",
      match zeroAtelModel with
      | .ok m => isErr (atelSat m (.implies p_ (.box q_)))
      | .error _ => false⟩,
    ⟨"Not in gamen-hs: laziness — atelSat(Iff Bot (Box p)) errors on a \
      NONEMPTY-state model even though the left side is Bot",
      match atelLoopModel with
      | .ok m => isErr (atelSat m (.iff .bot (.box p_)))
      | .error _ => false⟩,
    ⟨"Not in gamen-hs: laziness — atelSat(Iff p (Box q)) = ∅ on a zero-state \
      model: sl (=∅, states empty) forces first and is empty, so sr is \
      skipped",
      match zeroAtelModel with
      | .ok m => okIs (atelSat m (.iff p_ (.box q_))) ∅
      | .error _ => false⟩,
    ⟨"Not in gamen-hs: laziness — atelSat(Iff (Box p) q) errors on a \
      zero-state model: Iff's left side is always forced, in every case",
      match zeroAtelModel with
      | .ok m => isErr (atelSat m (.iff (.box p_) q_))
      | .error _ => false⟩,
    -- Not in gamen-hs: error order when both operands error, and the
    -- Knowledge/preC laziness. Expected values and error texts from
    -- gamen-hs's own `atelSat` in GHCi (`cabal repl lib:gamen`, 2026-09-29),
    -- on `irModel`, `zeroAtelModel`, and `irBobModel`.
    ⟨"Not in gamen-hs: error order — atelSat(Or (Box p) (Diamond p)) raises the \
      Diamond error (GHCi)",
      withIr fun m => errIs (atelSat m (.or (.box p_) (.diamond p_))) "Diamond not supported in ATEL"⟩,
    ⟨"Not in gamen-hs: error order — atelSat(Implies (Box p) (Diamond p)) raises \
      the Diamond error, on irModel and on a zero-state model (GHCi)",
      withIr (fun m =>
        errIs (atelSat m (.implies (.box p_) (.diamond p_))) "Diamond not supported in ATEL")
        && (match zeroAtelModel with
            | .ok m =>
                errIs (atelSat m (.implies (.box p_) (.diamond p_))) "Diamond not supported in ATEL"
            | .error _ => false)⟩,
    ⟨"Not in gamen-hs: error order — atelSat(Iff (Box p) (Diamond p)) raises the \
      Diamond error on irModel, the Box error on a zero-state model (GHCi)",
      withIr (fun m =>
        errIs (atelSat m (.iff (.box p_) (.diamond p_))) "Diamond not supported in ATEL")
        && (match zeroAtelModel with
            | .ok m =>
                errIs (atelSat m (.iff (.box p_) (.diamond p_))) "Box not supported in ATEL; use ⟨⟨Ag⟩⟩G"
            | .error _ => false)⟩,
    ⟨"Not in gamen-hs: laziness — on a zero-state model, atelSat(K_alice Box p) \
      and atelSat(⟨⟨alice⟩⟩X Box p) are ∅ (GHCi)",
      match zeroAtelModel with
      | .ok m =>
          okIs (atelSat m (.knowledge "alice" (.box p_))) ∅
            && okIs (atelSat m (.canNext al (.box p_))) ∅
      | .error _ => false⟩,
    ⟨"Not in gamen-hs: laziness — atelSat(⟨⟨alice⟩⟩X Box p) = {0,1,2} with a \
      moveless opponent, atelSat([bob] Box p) = ∅, but ⟨⟨alice⟩⟩X Box p errors \
      on irModel (GHCi)",
      (match irBobModel with
       | .ok m => okIs (atelSat m (.canNext al (.box p_))) (Std.TreeSet.ofList [0, 1, 2])
       | .error _ => false)
        && withIr (fun m =>
          okIs (atelSat m (.coalition ["bob"] (.box p_))) ∅
            && errIs (atelSat m (.canNext al (.box p_))) "Box not supported in ATEL; use ⟨⟨Ag⟩⟩G")⟩
  ]

/-! ## Atel (`test/RegressionIssue18.hs`)

The "B2/B7: ATLir semantics and iCGS validation" describe block's two
`mkAtelModel`-only `it`s (lines ~271–286); see `atelCases`'s docstring for
the block's other three `it`s, which stay unported. -/

private def atelB7Moves : Nat → String → Std.TreeSet String
  | _, "alice" => Std.TreeSet.ofList ["left", "right"]
  | _, _ => ∅

private def atelB7Trans : Nat → Std.TreeMap String String → Nat
  | 0, jm => if jm.get? "alice" == some "left" then 2 else 0
  | 1, jm => if jm.get? "alice" == some "right" then 2 else 1
  | _, _ => 2

private def atelB7Label : Nat → Std.TreeSet String
  | 2 => Std.TreeSet.ofList ["p"]
  | _ => ∅

private def atelB7Cgs : Cgs Nat String :=
  { cgsStates := Std.TreeSet.ofList [0, 1, 2]
    cgsAgents := Std.TreeSet.ofList ["alice"]
    cgsMoves := atelB7Moves
    cgsTransition := atelB7Trans
    cgsLabeling := atelB7Label }

/-- The good epistemic relation (`epi` in the Haskell): alice can't tell 0
from 1; state 2 is its own class. -/
private def atelB7Epi : String → Nat → Std.TreeSet Nat
  | "alice", 0 => Std.TreeSet.ofList [0, 1]
  | "alice", 1 => Std.TreeSet.ofList [0, 1]
  | _, s => Std.TreeSet.ofList [s]

def atelRegressionCases : List Case :=
  [ ⟨"RegressionIssue18 B7: mkAtelModel rejects a non-symmetric epistemic relation",
      -- alice sees 1 from 0 but not 0 from 1: asymmetric.
      let epiBad : String → Nat → Std.TreeSet Nat
        | "alice", 0 => Std.TreeSet.ofList [0, 1]
        | _, s => Std.TreeSet.ofList [s]
      isErr (mkAtelModel atelB7Cgs epiBad)⟩,
    ⟨"RegressionIssue18 B7: mkAtelModel rejects differing move sets across \
      indistinguishable states",
      -- alice's moves differ between the indistinguishable 0 and 1.
      let movesBad : Nat → String → Std.TreeSet String
        | 1, "alice" => Std.TreeSet.ofList ["left"]
        | s, ag => atelB7Moves s ag
      let cgsBad : Cgs Nat String := { atelB7Cgs with cgsMoves := movesBad }
      isErr (mkAtelModel cgsBad atelB7Epi)⟩,
    -- Not in gamen-hs: the two cases above (ported from RegressionIssue18,
    -- whose own `it`s only check `Left _`, not exact text) do not isolate
    -- the reflexivity/transitivity checks — each fixture that violates
    -- symmetry/move-uniformity there happens to be caught regardless of
    -- whether the reflexivity/transitivity checks are even present, so
    -- disabling either silently would still pass every existing case. These
    -- two fixtures are constructed to violate *only* reflexivity/*only*
    -- transitivity (worked out by hand, cross-checked against gamen-hs's
    -- actual `mkAtelModel` via `cabal repl` — confirmed both report the
    -- checks below, not a different one, i.e. every other check silently
    -- passes on each fixture), and the expected error text is gamen-hs's
    -- own (`src/Gamen/Atel.hs`'s `reflexivity`/`transitivity` messages,
    -- confirmed verbatim against the `cabal repl` output), compared exactly
    -- rather than via `isErr`, so a disabled/broken check (which would
    -- either accept the model or report a *different* violation's message)
    -- fails this case.
    ⟨"Not in gamen-hs: mkAtelModel rejects a reflexivity-only violation \
      (loop model, alice's class at 0 is ∅ instead of {0}; classes at 1 and \
      2 are the unmodified {1,2} each, so symmetry/transitivity/move-\
      uniformity all still hold)",
      let reflOnlyBadEpi : String → Nat → Std.TreeSet Nat
        | _, 0 => ∅
        | _, _ => Std.TreeSet.ofList [1, 2]
      match loopCgs with
      | .ok cgs =>
          match mkAtelModel cgs reflOnlyBadEpi with
          | .error msg => msg == "mkAtelModel: agent alice has a non-reflexive epistemic \
              relation (state not in own class)"
          | .ok _ => false
      | .error _ => false⟩,
    ⟨"Not in gamen-hs: mkAtelModel rejects a transitivity-only violation \
      (loop model, classes {0,1}/{0,1,2}/{1,2} at states 0/1/2: reflexive \
      and symmetric, but 0~1 and 1~2 without 0~2)",
      let transOnlyBadEpi : String → Nat → Std.TreeSet Nat
        | _, 0 => Std.TreeSet.ofList [0, 1]
        | _, 1 => Std.TreeSet.ofList [0, 1, 2]
        | _, _ => Std.TreeSet.ofList [1, 2]
      match loopCgs with
      | .ok cgs =>
          match mkAtelModel cgs transOnlyBadEpi with
          | .error msg => msg == "mkAtelModel: agent alice has a non-transitive epistemic relation"
          | .ok _ => false
      | .error _ => false⟩
  ]

/-! ## Atl.ImperfectInfo (`Gamen.Atl.ImperfectInfo`)

No `test/*ImperfectInfo*Spec.hs` in gamen-hs. The export search (`grep -lw`
over `test/*.hs` for every export) hits only `PaperCorrespondence.hs` and
`RegressionIssue18.hs`. Ported: every `it` of `PaperCorrespondence.hs`'s
"Jamroga & van der Hoek (2004) — ATLir" section except the two `sat`-only
ones already in `atlModelCheckCases` (15 of 17, `atlirCases`), and the
three `atlirSat`/`atlirSatObjective`/`subjectiveClass` `it`s of
`RegressionIssue18.hs`'s "B2/B7: ATLir semantics and iCGS validation"
block (`atlirRegressionCases`; its other two are in `atelRegressionCases`).

The "Not in gamen-hs" cases pin the module docstring's "Laziness" notes.
Each expected value, error text included, was checked against gamen-hs's
own `atlirSat` in GHCi (`cabal repl lib:gamen`, 2026-09-29). -/

def atlirCases : List Case :=
  let al : List String := ["alice"]
  let p_ : Formula := .atom "p"
  let boxErr := "Box not supported in ATLir; use ⟨⟨Ag⟩⟩G"
  let diaErr := "Diamond not supported in ATLir"
  [ -- §3 utility functions: epistemic classes and uniform actions
    ⟨"epistemicClasses alice = [{0,1},{2}]",
      withIr fun m => (epistemicClasses m "alice").map (·.toList) == [[0, 1], [2]]⟩,
    ⟨"uniformActions alice 0 = {left,right} (both moves available in class {0,1})",
      withIr fun m => uniformActions m "alice" 0 == Std.TreeSet.ofList ["left", "right"]⟩,
    ⟨"Not in gamen-hs: uniformActions intersects move sets across the class: \
      alice has {left,right} at 0 but only {left} at 1 (hand-built model, \
      bypassing mkAtelModel's uniformity check) → {left} (GHCi; gamen-hs#54)",
      -- GHCi, 2026-09-29: `uniformActions (AtelModel (irCgs { cgsMoves =
      -- mixMoves }) irEpi) "alice" 0` → `fromList ["left"]`.
      let mixMoves : Nat → String → Std.TreeSet String
        | 1, "alice" => Std.TreeSet.ofList ["left"]
        | s, ag => irMoves s ag
      let mixed : AtelModel Nat String :=
        { atelCgs := { irCgs with cgsMoves := mixMoves }, atelEpistemic := irEpistemic }
      uniformActions mixed "alice" 0 == Std.TreeSet.ofList ["left"]⟩,
    ⟨"subjectiveClass {alice} 0 = {0,1}",
      withIr fun m =>
        subjectiveClass m (Std.TreeSet.ofList ["alice"]) 0 == Std.TreeSet.ofList [0, 1]⟩,
    ⟨"allUniformStrategies alice has 4 strategies (2 classes × 2 moves)",
      withIr fun m => okIs ((allUniformStrategies m "alice").map List.length) 4⟩,
    -- §4 Theorem: sat_ATL ≥ sat_ATLir (strict containment for X p)
    ⟨"sat_ATLir(⟨⟨alice⟩⟩ir X p) = {2} — no uniform strategy works for class {0,1}",
      withIr fun m => okIs (atlirSat m (.canNext al p_)) (Std.TreeSet.ofList [2])⟩,
    ⟨"sat_ATLir strictly ⊊ sat_ATL for CanNext p",
      withIr fun m =>
        match atlirSat m (.canNext al p_), sat irCgs (.canNext al p_) with
        | .ok a, .ok b => a.all fun w => b.contains w
        | _, _ => false⟩,
    -- §4 Theorem: sat_ATL ≥ sat_ATLir (strict containment for F p)
    ⟨"sat_ATLir(⟨⟨alice⟩⟩ir F p) = {2} — uniform strategies cannot escape class {0,1}",
      withIr fun m => okIs (atlirSat m (.canEventually al p_)) (Std.TreeSet.ofList [2])⟩,
    ⟨"sat_ATLir strictly ⊊ sat_ATL for CanEventually p",
      withIr fun m =>
        match atlirSat m (.canEventually al p_), sat irCgs (.canEventually al p_) with
        | .ok a, .ok b => a.all fun w => b.contains w
        | _, _ => false⟩,
    -- §4 ATLir semantics: always (G) and until
    ⟨"sat_ATLir(⟨⟨alice⟩⟩ir G p) = {2} — only absorbing p-state can maintain p forever",
      withIr fun m => okIs (atlirSat m (.canAlways al p_)) (Std.TreeSet.ofList [2])⟩,
    ⟨"sat_ATLir(⟨⟨alice⟩⟩ir (p U p)) = {2} — trivial until (p until p = p)",
      withIr fun m => okIs (atlirSat m (.canUntil al p_ p_)) (Std.TreeSet.ofList [2])⟩,
    ⟨"sat_ATLir(⟨⟨alice⟩⟩ir F ¬p) = {0,1} — uniform 'right' loops 0 in ¬p; state 2 \
      absorbs under p",
      withIr fun m => okIs (atlirSat m (.canEventually al (.not p_))) (Std.TreeSet.ofList [0, 1])⟩,
    -- B2: objective semantics (actual state only) vs subjective
    ⟨"sat_ATLir^obj(⟨⟨alice⟩⟩ir X p) = {0,1,2} — success required at s only",
      withIr fun m => okIs (atlirSatObjective m (.canNext al p_)) (Std.TreeSet.ofList [0, 1, 2])⟩,
    ⟨"objective X p coincides with perfect-info sat_ATL here",
      withIr fun m =>
        match atlirSatObjective m (.canNext al p_), sat irCgs (.canNext al p_) with
        | .ok a, .ok b => a == b
        | _, _ => false⟩,
    ⟨"subjective ⊊ objective for X p (uniformity bites across the class)",
      withIr fun m =>
        match atlirSat m (.canNext al p_), atlirSatObjective m (.canNext al p_) with
        | .ok subj, .ok obj => subj.all (fun w => obj.contains w) && !(subj == obj)
        | _, _ => false⟩,
    ⟨"sat_ATLir^obj(⟨⟨alice⟩⟩ir F p) = {0,1,2}",
      withIr fun m =>
        okIs (atlirSatObjective m (.canEventually al p_)) (Std.TreeSet.ofList [0, 1, 2])⟩,
    -- Not in gamen-hs: the wrappers (no gamen-hs test calls them).
    ⟨"Not in gamen-hs: atlirSatisfies 2 / 0 (⟨⟨alice⟩⟩ir X p) = true / false; \
      objective at 0 = true",
      withIr fun m =>
        okIs (atlirSatisfies m 2 (.canNext al p_)) true
          && okIs (atlirSatisfies m 0 (.canNext al p_)) false
          && okIs (atlirSatisfiesObjective m 0 (.canNext al p_)) true⟩,
    ⟨"Not in gamen-hs: atlirIsTrueIn (⟨⟨alice⟩⟩ir X p) = false; objective = true",
      withIr fun m =>
        okIs (atlirIsTrueIn m (.canNext al p_)) false
          && okIs (atlirIsTrueInObjective m (.canNext al p_)) true⟩,
    ⟨"Not in gamen-hs: atlirSatisfies / atlirSatisfiesObjective error on a state \
      not in cgsStates",
      withIr fun m =>
        errIs (atlirSatisfies m 7 p_) "atlirSatisfies: state not in cgsStates"
          && errIs (atlirSatisfiesObjective m 7 p_)
            "atlirSatisfiesObjective: state not in cgsStates"⟩,
    ⟨"Not in gamen-hs: [alice]p is treated as ⟨⟨alice⟩⟩ir X p = {2}; \
      ⟨⟨∅⟩⟩ir X p = {2}",
      withIr fun m =>
        okIs (atlirSat m (.coalition al p_)) (Std.TreeSet.ofList [2])
          && okIs (atlirSat m (.canNext [] p_)) (Std.TreeSet.ofList [2])⟩,
    ⟨"Not in gamen-hs: sat_ATLir^obj(⟨⟨alice⟩⟩ir G ¬p) = {0,1} (uniform 'right' \
      keeps 0 at 0; uniform 'left' keeps 1 at 1)",
      withIr fun m =>
        okIs (atlirSatObjective m (.canAlways al (.not p_))) (Std.TreeSet.ofList [0, 1])⟩,
    -- Not in gamen-hs: laziness (GHCi-checked, see the list's docstring).
    ⟨"Not in gamen-hs: laziness — Or (Box p) (Diamond p) raises the Diamond error \
      (Set.union forces its second argument first)",
      withIr fun m => errIs (atlirSat m (.or (.box p_) (.diamond p_))) diaErr⟩,
    ⟨"Not in gamen-hs: laziness — Implies (Box p) (Diamond p) raises the Diamond error",
      withIr fun m => errIs (atlirSat m (.implies (.box p_) (.diamond p_))) diaErr⟩,
    ⟨"Not in gamen-hs: laziness — Iff (Box p) (Diamond p) raises the Diamond error \
      on a nonempty-state model",
      withIr fun m => errIs (atlirSat m (.iff (.box p_) (.diamond p_))) diaErr⟩,
    ⟨"Not in gamen-hs: laziness — And Bot (Box p) = ∅; And (Box p) (Diamond p) \
      raises the Box error",
      withIr fun m =>
        okIs (atlirSat m (.and .bot (.box p_))) ∅
          && errIs (atlirSat m (.and (.box p_) (.diamond p_))) boxErr⟩,
    ⟨"Not in gamen-hs: laziness — ⟨⟨alice⟩⟩ir (Box p U Diamond p) raises the Box \
      error (φ before ψ)",
      withIr fun m => errIs (atlirSat m (.canUntil al (.box p_) (.diamond p_))) boxErr⟩,
    ⟨"Not in gamen-hs: laziness — K_alice (Box p) and Not (Box p) raise the Box \
      error on a nonempty-state model",
      withIr fun m =>
        errIs (atlirSat m (.knowledge "alice" (.box p_))) boxErr
          && errIs (atlirSat m (.not (.box p_))) boxErr⟩,
    ⟨"Not in gamen-hs: laziness — on a zero-state model, K_alice (Box p), \
      ⟨⟨alice⟩⟩ir X (Box p) and Not (Box p) are ∅",
      match zeroAtelModel with
      | .ok m =>
          okIs (atlirSat m (.knowledge "alice" (.box p_))) ∅
            && okIs (atlirSat m (.canNext al (.box p_))) ∅
            && okIs (atlirSat m (.not (.box p_))) ∅
      | .error _ => false⟩,
    ⟨"Not in gamen-hs: laziness — on a zero-state model, Iff (Box p) (Diamond p) \
      raises Box, Implies (Box p) (Diamond p) raises Diamond",
      match zeroAtelModel with
      | .ok m =>
          errIs (atlirSat m (.iff (.box p_) (.diamond p_))) boxErr
            && errIs (atlirSat m (.implies (.box p_) (.diamond p_))) diaErr
      | .error _ => false⟩,
    ⟨"Not in gamen-hs: laziness — ⟨⟨bob⟩⟩ir X (Box p) and [bob](Box p) = ∅: bob \
      has no moves, so no uniform profile, so Box p is never evaluated",
      withIr fun m =>
        okIs (atlirSat m (.canNext ["bob"] (.box p_))) ∅
          && okIs (atlirSat m (.coalition ["bob"] (.box p_))) ∅⟩,
    ⟨"Not in gamen-hs: laziness — with a moveless opponent bob, ⟨⟨alice⟩⟩ir X (Box p) \
      = {0,1,2} (preC never tests membership), but F and G raise the Box error",
      match irBobModel with
      | .ok m =>
          okIs (atlirSat m (.canNext al (.box p_))) (Std.TreeSet.ofList [0, 1, 2])
            && errIs (atlirSat m (.canEventually al (.box p_))) boxErr
            && errIs (atlirSat m (.canAlways al (.box p_))) boxErr
      | .error _ => false⟩,
    ⟨"Not in gamen-hs: an empty epistemic class (model built without mkAtelModel, \
      epistemic function strict in the state) raises Set.findMin's error",
      -- GHCi, epistemic `\_ s -> if s == 99 then {s} else ∅`: both calls
      -- give `Left Set.findMin: empty set has no minimal element`. (For an
      -- epistemic function that ignores its state, GHC never forces
      -- `findMin` and returns `[]`/∅; Lean cannot see that strictness and
      -- always throws. See the module docstring.)
      let bad : AtelModel Nat String :=
        { atelCgs := irCgs, atelEpistemic := fun _ s => if s == 99 then {s} else ∅ }
      let findMinErr := "Set.findMin: empty set has no minimal element"
      errIs (atlirSat bad (.canNext al p_)) findMinErr
        && errIs (allUniformStrategies bad "alice") findMinErr⟩
  ]

/-! ## Atl.ImperfectInfo (`test/RegressionIssue18.hs`)

"B2/B7: ATLir semantics and iCGS validation"'s three ATLir `it`s, over the
block's own model (`atelB7Cgs`/`atelB7Epi`). -/

def atlirRegressionCases : List Case :=
  let al : List String := ["alice"]
  let withB7 (k : AtelModel Nat String → Bool) : Bool :=
    match mkAtelModel atelB7Cgs atelB7Epi with
    | .ok m => k m
    | .error _ => false
  [ ⟨"RegressionIssue18 B2: subjective ⟨⟨alice⟩⟩ir X p = {2} (union-of-classes, \
      not intersection)",
      withB7 fun m => okIs (atlirSat m (.canNext al (.atom "p"))) (Std.TreeSet.ofList [2])⟩,
    ⟨"RegressionIssue18 B2: objective ⟨⟨alice⟩⟩ir X p = {0,1,2} (actual state only)",
      withB7 fun m =>
        okIs (atlirSatObjective m (.canNext al (.atom "p"))) (Std.TreeSet.ofList [0, 1, 2])⟩,
    ⟨"RegressionIssue18 B2: subjectiveClass is the union of ~_a classes (= {0,1} for \
      alice at 0)",
      withB7 fun m =>
        subjectiveClass m (Std.TreeSet.ofList ["alice"]) 0 == Std.TreeSet.ofList [0, 1]⟩
  ]

/-! ## DCLEG (`Gamen.Dcleg`)

Ports, in file order:

* `test/DclegServiceSpec.hs` in full (59 `it`s, `dclegCases`). Despite its
  name it imports only `Gamen.Dcleg` and exercises the library functions
  the dcleg service delegates to, so it is this module's spec.
* `test/PaperCorrespondence.hs`, "Chapman (2026) — Doxastic Conditional
  Logic of Extensive Games (DCLEG v5.0)" in full (35 `it`s,
  `dclegPaperCorrespondenceCases`).
* `test/RegressionIssue18.hs`, "B7: validateDclegModel catches
  referential/seriality faults" (3 `it`s, `dclegRegressionCases`).
* The four `test/Properties.hs` properties (`properties`).
* Not in gamen-hs (end of `dclegCases`): errors, short-circuiting, and a
  three-move and a one-move vertex, every value and error text from GHCi.

Citations are to the final thesis (Chapter 3), with printed pages
(`notes/dcleg-edition.md`); "DCLEG v5.0" names the April 2026 draft, and
gamen-hs's quoted describe titles keep its v5.0 numbering, each followed by
the final section. v5.0's Table 1 ("Some Validities") is its §2.7, not §2.5
or §1.2, and the final thesis dropped it: the ten tests that cite it are
labeled "DCLEG v5.0 Table 1 (not in the final thesis)" and kept. □'s
uniformity is §3.2.5's text (p. 23), not Table 1; Presence and
Self-Awareness are §3.2.2's doxastic conditions 1 and 5 (p. 20), not §2.4.
v5.0's Table 1 states PerfectInfo, TurnStr, and SinglePref with the
counterfactual □→ (gamen-hs#53); the Haskell tests check the material → at
one point, and are ported as they are.

`withMovePremises` adds the singleton premise {(γ,w)} (gamen-hs TODO(#18),
fixed in gamen-lean), so Centering holds at single-move vertices; the
tests that depend on it are marked "fixed in gamen-lean; gamen-hs
TODO(#18)".

Every satisfaction result is compared with `okIs`/`bothOkEq`, so an error
fails the case whichever answer was expected. -/
section DclegTests

attribute [local instance] lexOrd

/-- Both succeed with the same value. Haskell's `a `shouldBe` b` between two
`dclegSatisfies` calls; an error on either side fails. -/
def bothOkEq [BEq α] (a b : Except String α) : Bool :=
  match a, b with
  | .ok x, .ok y => x == y
  | _, _ => false

/-- `DclegServiceSpec.hs`'s `svcModel`. -/
def svcModel : DclegModel := withMovePremises <| mkDclegModel
  (mkStrategicStructure ["v0", "v1", "v2"] ["v1", "v2"] [("v0", "p1")]
    [("v0", ["L", "R"])] [("v0", "L", "v1"), ("v0", "R", "v2")])
  ["gL", "gR"]
  [("gL", mkHistory [("v0", "L")] "v1"), ("gR", mkHistory [("v0", "R")] "v2")]
  [("alive", [("gL", "v0")])]
  [("p1", [("v0", [("gL", ["gL"]), ("gR", ["gR"])])])]
  [("p1", [("v1", 1), ("v2", 0)])]

def svcSat (g w : String) (f : DclegFormula) : Except String Bool := dclegSatisfies svcModel g w f

def svcDox (w g : String) : Except String (List String) := doxasticSuccessors svcModel "p1" w g

def sortedStrings (xs : List String) : List String := (Std.TreeSet.ofList xs : Std.TreeSet String).toList

/-- `∩F(γ,v0)` (Haskell `foldr1 Set.intersection`); `none` if F is empty,
where `foldr1` would error. -/
def svcPremiseCap (g : String) : Option (List (String × String)) :=
  match (svcModel.dmPremises.getD (g, "v0") ∅).toList with
  | [] => none
  | p :: ps => some (ps.foldr (fun a b => a ∩ b) p).toList

def svcPremiseUnion (g : String) : Std.TreeSet (String × String) :=
  (svcModel.dmPremises.getD (g, "v0") ∅).toList.foldl (fun acc s => s.foldl (·.insert ·) acc) ∅

/-- Witness set, whether ψ holds at every witness, and whether it is empty. -/
def svcWitnesses (g : String) (phi psi : DclegFormula) :
    Except String (List String × Bool × Bool) := do
  let ws ← maxPhiConsistent svcModel g "v0" phi
  let sat ← ws.allM fun b => dclegSatisfies svcModel b "v0" psi
  return (sortedStrings ws, sat, ws.isEmpty)

/-- Not in gamen-hs: one decision vertex with three moves, one world each. -/
def dclegThreeMove : DclegModel := withMovePremises <| mkDclegModel
  (mkStrategicStructure ["v0", "v1", "v2", "v3"] ["v1", "v2", "v3"] [("v0", "p1")]
    [("v0", ["L", "M", "R"])] [("v0", "L", "v1"), ("v0", "M", "v2"), ("v0", "R", "v3")])
  ["gL", "gM", "gR"]
  [("gL", mkHistory [("v0", "L")] "v1"), ("gM", mkHistory [("v0", "M")] "v2"),
   ("gR", mkHistory [("v0", "R")] "v3")]
  []
  [("p1", [("v0", [("gL", ["gL"]), ("gM", ["gM"]), ("gR", ["gR"])])])]
  [("p1", [("v1", 2), ("v2", 1), ("v3", 0)])]

/-- Not in gamen-hs: a single-move vertex reached by two worlds. gamen-hs's
`withMovePremises` does not give Centering here (adversarial review B8);
gamen-lean's does (fixed in gamen-lean; gamen-hs TODO(#18)). -/
def dclegOneMove : DclegModel := withMovePremises <| mkDclegModel
  (mkStrategicStructure ["v0", "v1"] ["v1"] [("v0", "p1")] [("v0", ["L"])] [("v0", "L", "v1")])
  ["gA", "gB"]
  [("gA", mkHistory [("v0", "L")] "v1"), ("gB", mkHistory [("v0", "L")] "v1")]
  [("p", [("gB", "v0")])] [] []

/-- Not in gamen-hs: p1 chooses L or R at v0; after L, p2 has the single
move C at v1, which two worlds (gA, gB) reach. p is true at (gB,v1) and
(gC,v0), so p varies between the two worlds at the single-move vertex. -/
def dclegOneMoveDeep : DclegModel := withMovePremises <| mkDclegModel
  (mkStrategicStructure ["v0", "v1", "v2", "v3"] ["v2", "v3"] [("v0", "p1"), ("v1", "p2")]
    [("v0", ["L", "R"]), ("v1", ["C"])] [("v0", "L", "v1"), ("v0", "R", "v2"), ("v1", "C", "v3")])
  ["gA", "gB", "gC"]
  [("gA", mkHistory [("v0", "L"), ("v1", "C")] "v3"),
   ("gB", mkHistory [("v0", "L"), ("v1", "C")] "v3"),
   ("gC", mkHistory [("v0", "R")] "v2")]
  [("p", [("gB", "v1"), ("gC", "v0")])] [] []

/-- Every (γ,w) with w a decision vertex reached in γ. -/
def dclegDecisionPointsOf (m : DclegModel) : List (String × String) :=
  m.dmWorlds.toList.flatMap fun g =>
    ((worldVertices m g).toList.filter (!m.dmStructure.ssEndNodes.contains ·)).map (g, ·)

/-- Centering (§3.2.2, p. 19) at every decision vertex: ∩F(γ,w) = {(γ,w)}. -/
def dclegCenteringAtDecisionPoints (m : DclegModel) : Bool :=
  (dclegDecisionPointsOf m).all fun (g, w) =>
    match (m.dmPremises.getD (g, w) ∅).toList with
    | [] => false
    | p :: ps => (ps.foldr (fun a b => a ∩ b) p).toList == [(g, w)]

/-- §3.2.5 (p. 23): "if the main connective of φ is □, the counterfactual
conditional φ □→ ψ always collapses to a material conditional". Checks
(□χ □→ ψ) ↔ (□χ → ψ) at every decision point, for each χ and ψ given. -/
def dclegBoxCollapseAtDecisionPoints (m : DclegModel) (chis psis : List DclegFormula) : Bool :=
  isOkTrue <| (dclegDecisionPointsOf m).allM fun (g, w) =>
    chis.allM fun chi => psis.allM fun psi => do
      let c ← dclegSatisfies m g w (.dfConditional (.dfBox chi) psi)
      let d ← dclegSatisfies m g w (dfImplies (.dfBox chi) psi)
      return c == d

def dclegCases : List Case :=
  let mi (mv : String) : DclegFormula := dfAnd (.dfMove mv) (.dfTurn "p1")
  [ -- "model construction"
    ⟨"DclegServiceSpec: both worlds are present in the model",
      svcModel.dmWorlds.toList == ["gL", "gR"]⟩,
    ⟨"DclegServiceSpec: strategic structure has three vertices",
      svcModel.dmStructure.ssNodes.size == 3⟩,
    ⟨"DclegServiceSpec: withMovePremises populates dmPremises at decision vertex",
      svcModel.dmPremises.contains ("gL", "v0")⟩,
    -- Deliberate divergence from gamen-hs: fixed in gamen-lean (outcome-node
    -- premises; docs/dcleg-outcome-node-premises-2026-09-30.md). gamen-hs's
    -- `it` is "withMovePremises leaves end nodes out of dmPremises"; an
    -- outcome node with no premises violates Centering and Contemporary
    -- Universality (§3.2.2, p. 19) and makes every φ □→ ψ vacuously true
    -- there. Now every reached outcome pair gets an entry; (gL,v2) is not
    -- reached, so it still has none.
    ⟨"DclegServiceSpec: withMovePremises gives reached end nodes premises, and unreached ones \
      none (deliberate divergence from gamen-hs: fixed in gamen-lean (outcome-node premises; \
      docs/dcleg-outcome-node-premises-2026-09-30.md))",
      svcModel.dmPremises.contains ("gL", "v1") && svcModel.dmPremises.contains ("gR", "v2")
        && !svcModel.dmPremises.contains ("gL", "v2")⟩,
    -- "sat — atomic formulas (§2.3 Chapman 2026)"; final §3.2.3, p. 21
    ⟨"DclegServiceSpec: ⊥ is never satisfied (§3.2.3, p. 21, DFBot)", okIs (svcSat "gL" "v0" .dfBot) false⟩,
    ⟨"DclegServiceSpec: prop 'alive' true at (gL,v0) — in valuation extension (§3.2.3, p. 21, DFProp)",
      okIs (svcSat "gL" "v0" (.dfProp "alive")) true⟩,
    ⟨"DclegServiceSpec: prop 'alive' false at (gR,v0) — not in extension (§3.2.3, p. 21, DFProp)",
      okIs (svcSat "gR" "v0" (.dfProp "alive")) false⟩,
    ⟨"DclegServiceSpec: turn_p1 true at v0 — Q(v0)=p1 (§3.2.3, p. 21, DFTurn)",
      okIs (svcSat "gL" "v0" (.dfTurn "p1")) true⟩,
    ⟨"DclegServiceSpec: turn_p1 false at outcome v1 — Q undefined at end nodes (§3.2.3, p. 21, DFTurn)",
      okIs (svcSat "gL" "v1" (.dfTurn "p1")) false⟩,
    ⟨"DclegServiceSpec: DFMove L true at (gL,v0) — Move(gL,v0)=L (§3.2.3, p. 21, DFMove)",
      okIs (svcSat "gL" "v0" (.dfMove "L")) true⟩,
    ⟨"DclegServiceSpec: DFMove R false at (gL,v0) — Move(gL,v0)=L not R (§3.2.3, p. 21, DFMove)",
      okIs (svcSat "gL" "v0" (.dfMove "R")) false⟩,
    ⟨"DclegServiceSpec: DFPayoff 1 p1 true at (gL,v0) — P_p1(v1)=1 (§3.2.3, p. 21, DFPayoff)",
      okIs (svcSat "gL" "v0" (.dfPayoff 1 "p1")) true⟩,
    ⟨"DclegServiceSpec: DFPayoff 0 p1 true at (gR,v0) — P_p1(v2)=0 (§3.2.3, p. 21, DFPayoff)",
      okIs (svcSat "gR" "v0" (.dfPayoff 0 "p1")) true⟩,
    ⟨"DclegServiceSpec: DFPayoff 0 p1 false at (gL,v0) — P_p1(v1)=1 not 0 (§3.2.3, p. 21, DFPayoff)",
      okIs (svcSat "gL" "v0" (.dfPayoff 0 "p1")) false⟩,
    -- "sat — temporal operators X and Y (§2.3 Chapman 2026)"; final §3.2.3, p. 21
    ⟨"DclegServiceSpec: X(payoff 1) true at (gL,v0): next(v0,L)=v1, P_p1(v1)=1 (§3.2.3, p. 21, DFNext)",
      okIs (svcSat "gL" "v0" (.dfNext (.dfPayoff 1 "p1"))) true⟩,
    ⟨"DclegServiceSpec: X(payoff 1) false at (gR,v0): next(v0,R)=v2, P_p1(v2)=0 (§3.2.3, p. 21, DFNext)",
      okIs (svcSat "gR" "v0" (.dfNext (.dfPayoff 1 "p1"))) false⟩,
    ⟨"DclegServiceSpec: X⊤ false at outcome v1 — no successor move exists (§3.2.3, p. 21, DFNext)",
      okIs (svcSat "gL" "v1" (.dfNext dfTop)) false⟩,
    ⟨"DclegServiceSpec: Y⊤ false at root v0 — no predecessor exists (§3.2.3, p. 21, DFYesterday)",
      okIs (svcSat "gL" "v0" (.dfYesterday dfTop)) false⟩,
    ⟨"DclegServiceSpec: Y⊤ true at (gL,v1): predecessor of v1 is v0 (§3.2.3, p. 21, DFYesterday)",
      okIs (svcSat "gL" "v1" (.dfYesterday dfTop)) true⟩,
    -- "sat — necessity □ and belief B_i (§2.3–2.4 Chapman 2026)"; final §3.2.3, p. 21
    ⟨"DclegServiceSpec: □(turn_p1) true at v0: both worlds reach v0 with Q(v0)=p1 (§3.2.3, p. 21, DFBox)",
      okIs (svcSat "gL" "v0" (.dfBox (.dfTurn "p1"))) true⟩,
    ⟨"DclegServiceSpec: □(DFMove L) false at v0: gR reaches v0 but plays R (§3.2.3, p. 21, DFBox)",
      okIs (svcSat "gL" "v0" (.dfBox (.dfMove "L"))) false⟩,
    -- Haskell cites "§2.5 Table 1"; uniformity is v5.0 §2.5's text (final §3.2.5), not Table 1.
    ⟨"DclegServiceSpec: □ uniformity: □(turn_p1) same truth at v0 regardless of world (§3.2.5, p. 23)",
      bothOkEq (svcSat "gL" "v0" (.dfBox (.dfTurn "p1"))) (svcSat "gR" "v0" (.dfBox (.dfTurn "p1")))⟩,
    ⟨"DclegServiceSpec: B_p1(DFMove L) true at (gL,v0): p1 considers only gL at v0 (§3.2.3, p. 21, DFBelief)",
      okIs (svcSat "gL" "v0" (.dfBelief "p1" (.dfMove "L"))) true⟩,
    ⟨"DclegServiceSpec: B_p1(DFMove L) false at (gR,v0): gR-successor plays R not L (§3.2.3, p. 21, DFBelief)",
      okIs (svcSat "gR" "v0" (.dfBelief "p1" (.dfMove "L"))) false⟩,
    ⟨"DclegServiceSpec: B_p1(DFMove R) true at (gR,v0): p1 in gR considers only gR (§3.2.3, p. 21, DFBelief)",
      okIs (svcSat "gR" "v0" (.dfBelief "p1" (.dfMove "R"))) true⟩,
    -- Haskell cites "(§2.4)"; PerfectInfo is DCLEG v5.0 Table 1 (v5.0 §2.7; not
    -- in the final thesis). Presence is §3.2.2, p. 20.
    ⟨"DclegServiceSpec: PerfectInfo (DCLEG v5.0 Table 1, not in the final thesis): □φ → B_p1 φ at \
      (gL,v0) — Presence (§3.2.2, p. 20) \
      entails inclusion",
      okIs (svcSat "gL" "v0" (dfImplies (.dfBox (.dfTurn "p1")) (.dfBelief "p1" (.dfTurn "p1"))))
        true⟩,
    -- "true_in — global satisfaction"
    ⟨"DclegServiceSpec: ⊤ (=¬⊥) is true in every model (dclegTrueIn)",
      okIs (dclegTrueIn svcModel dfTop) true⟩,
    ⟨"DclegServiceSpec: ⊥ is false in every model (dclegTrueIn)",
      okIs (dclegTrueIn svcModel .dfBot) false⟩,
    ⟨"DclegServiceSpec: □⊤ is true in model: ⊤ at all worlds reaching any vertex (dclegTrueIn)",
      okIs (dclegTrueIn svcModel (.dfBox dfTop)) true⟩,
    ⟨"DclegServiceSpec: DFMove L is NOT globally true: false at (gR,v0) (dclegTrueIn)",
      okIs (dclegTrueIn svcModel (.dfMove "L")) false⟩,
    -- "counterfactual — maxPhiConsistent witnesses (§2.2 Chapman 2026)"; final §3.2.2, p. 19
    ⟨"DclegServiceSpec: L □→ payoff_1 at (gL,v0): witnesses = {gL}, satisfied, not vacuous \
      (§3.2.2 Centering, p. 19)",
      okIs (svcWitnesses "gL" (.dfMove "L") (.dfPayoff 1 "p1")) (["gL"], true, false)⟩,
    ⟨"DclegServiceSpec: R □→ payoff_0 at (gL,v0): witnesses = {gR}, satisfied, not vacuous (§3.2.3, p. 21)",
      okIs (svcWitnesses "gL" (.dfMove "R") (.dfPayoff 0 "p1")) (["gR"], true, false)⟩,
    ⟨"DclegServiceSpec: R □→ payoff_1 at (gL,v0): witnesses = {gR}, NOT satisfied (§3.2.3, p. 21)",
      okIs ((·.2.1) <$> svcWitnesses "gL" (.dfMove "R") (.dfPayoff 1 "p1")) false⟩,
    ⟨"DclegServiceSpec: ⊥ □→ anything at (gL,v0): vacuous — no φ-consistent worlds (§3.2.2, p. 19; §3.2.3, p. 22)",
      okIs (maxPhiConsistent svcModel "gL" "v0" .dfBot) []⟩,
    ⟨"DclegServiceSpec: dclegSatisfies handles vacuous counterfactual as True (§3.2.3, p. 21, DFConditional)",
      okIs (svcSat "gL" "v0" (.dfConditional .dfBot .dfBot)) true⟩,
    ⟨"DclegServiceSpec: counterfactual witness set is symmetric by world: gR witnesses R □→ \
      payoff_0 from gR (§3.2.3, p. 21)",
      okIs (sortedStrings <$> maxPhiConsistent svcModel "gR" "v0" (.dfMove "R")) ["gR"]⟩,
    -- "axiom_check — standard doxastic axioms (§2.2 Chapman 2026)"; final §3.2.2, p. 20
    ⟨"DclegServiceSpec: presence satisfied: gR does not reach v1, successors at v1 for gR are \
      empty (§3.2.2, p. 20)",
      okIs (svcDox "v1" "gR") []⟩,
    ⟨"DclegServiceSpec: presence satisfied: gL does not reach v2, successors at v2 for gL are \
      empty (§3.2.2, p. 20)",
      okIs (svcDox "v2" "gL") []⟩,
    ⟨"DclegServiceSpec: present_seriality satisfied at decision vertex: R_p1^{v0}(gL) non-empty \
      (§3.2.2, p. 20)",
      okIs ((!·.isEmpty) <$> svcDox "v0" "gL") true⟩,
    ⟨"DclegServiceSpec: present_seriality VIOLATED at end node v1: model defines no beliefs \
      there (§3.2.2, p. 20)",
      okIs (svcDox "v1" "gL") []⟩,
    ⟨"DclegServiceSpec: transitivity satisfied: {gL} is a singleton so transitivity holds \
      trivially (§3.2.2, p. 20)",
      okIs (do
        let succs ← svcDox "v0" "gL"
        let trans ← succs.mapM (svcDox "v0")
        return trans.flatten.all (succs.contains ·)) true⟩,
    ⟨"DclegServiceSpec: euclideanness satisfied: singleton successors are trivially euclidean \
      (§3.2.2, p. 20)",
      okIs (do
        let succs ← svcDox "v0" "gL"
        let pairs := succs.flatMap fun a => succs.map fun b => (a, b)
        pairs.allM fun (a, b) => return (← svcDox "v0" a).contains b) true⟩,
    -- "axiom_check — self-awareness and intentional-awareness (§2.2–2.4 Chapman 2026)"; final
    -- §3.2.2, p. 20, and §3.2.4, p. 23
    ⟨"DclegServiceSpec: self_awareness: all gL-successors at v0 play L — matches actual move (§3.2.2, p. 20)",
      okIs ((·.map fun d => moveAt svcModel d "v0") <$> svcDox "v0" "gL") [some "L"]⟩,
    ⟨"DclegServiceSpec: self_awareness: all gR-successors at v0 play R — matches actual move (§3.2.2, p. 20)",
      okIs ((·.map fun d => moveAt svcModel d "v0") <$> svcDox "v0" "gR") [some "R"]⟩,
    ⟨"DclegServiceSpec: intentional_awareness: B_p1(L ∧ turn_p1) ↔ (L ∧ turn_p1) at (gL,v0) (§3.2.4, p. 23)",
      bothOkEq (svcSat "gL" "v0" (.dfBelief "p1" (mi "L"))) (svcSat "gL" "v0" (mi "L"))⟩,
    ⟨"DclegServiceSpec: intentional_awareness: B_p1(R ∧ turn_p1) ↔ (R ∧ turn_p1) at (gL,v0) (§3.2.4, p. 23)",
      bothOkEq (svcSat "gL" "v0" (.dfBelief "p1" (mi "R"))) (svcSat "gL" "v0" (mi "R"))⟩,
    ⟨"DclegServiceSpec: intentional_awareness: B_p1(R ∧ turn_p1) ↔ (R ∧ turn_p1) at (gR,v0) (§3.2.4, p. 23)",
      bothOkEq (svcSat "gR" "v0" (.dfBelief "p1" (mi "R"))) (svcSat "gR" "v0" (mi "R"))⟩,
    -- "axiom_check — premise function axioms (§2.2 Chapman 2026)"; final §3.2.2, p. 19
    ⟨"DclegServiceSpec: centering: ∩F(gL,v0) = {(gL,v0)} (§3.2.2, p. 19)",
      svcPremiseCap "gL" == some [("gL", "v0")]⟩,
    ⟨"DclegServiceSpec: centering: ∩F(gR,v0) = {(gR,v0)} (§3.2.2, p. 19)",
      svcPremiseCap "gR" == some [("gR", "v0")]⟩,
    ⟨"DclegServiceSpec: contemporary_universality: gL ∈ ∪F(gL,v0) at v0 — centering places it in \
      premise (§3.2.2, p. 19)",
      (svcPremiseUnion "gL").contains ("gL", "v0")⟩,
    ⟨"DclegServiceSpec: contemporary_universality: gR ∈ ∪F(gL,v0) — all worlds reaching v0 \
      covered (§3.2.2, p. 19)",
      (svcPremiseUnion "gL").contains ("gR", "v0")⟩,
    -- Haskell cites "(withMovePremises §2.3)"; the move-based F is gamen-hs's
    -- own construction, and F's constraints are §3.2.2 (p. 19).
    ⟨"DclegServiceSpec: F(gL,v0) has exactly two premises — one per move (withMovePremises; F: §3.2.2, p. 19)",
      (svcModel.dmPremises.getD ("gL", "v0") ∅).size == 2⟩,
    -- "axiom_check — belief-revision dynamics (§2.2 Chapman 2026)"; final §3.2.2, p. 20
    ⟨"DclegServiceSpec: minimal_revision satisfied: no worlds at v1 to check — vacuously true (§3.2.2, p. 20)",
      okIs (svcDox "v1" "gL") []⟩,
    ⟨"DclegServiceSpec: minimal_revision: witness pool for move L includes gL (§3.2.2, p. 20)",
      okIs (maxPhiConsistent svcModel "gL" "v0" (.dfMove "L")) ["gL"]⟩,
    ⟨"DclegServiceSpec: minimal_revision: witness pool for move R includes gR (§3.2.2, p. 20)",
      okIs (sortedStrings <$> maxPhiConsistent svcModel "gL" "v0" (.dfMove "R")) ["gR"]⟩,
    ⟨"DclegServiceSpec: expectational_continuity VIOLATED at (gL,v0): successors play L but \
      beliefs change at v1 (§3.2.2, p. 20)",
      okIs (do return sortedStrings (← svcDox "v0" "gL") != sortedStrings (← svcDox "v1" "gL"))
        true⟩,
    ⟨"DclegServiceSpec: expectational_continuity VIOLATED at (gR,v0): same pattern for move R (§3.2.2, p. 20)",
      okIs (do return sortedStrings (← svcDox "v0" "gR") != sortedStrings (← svcDox "v2" "gR"))
        true⟩,
    ⟨"DclegServiceSpec: recall VIOLATED at (gL,v0): R_p1(v0,gL) ≠ ∪{R_p1(v0,δ) | δ∈R_p1(v1,gL)} \
      (§3.2.2, p. 20)",
      okIs (do
        let atV0 ← svcDox "v0" "gL"
        let atV1 ← svcDox "v1" "gL"
        let u ← atV1.mapM (svcDox "v0")
        return sortedStrings atV0 != sortedStrings u.flatten) true⟩,
    ⟨"DclegServiceSpec: recall VIOLATED at (gR,v0): symmetric case for world gR (§3.2.2, p. 20)",
      okIs (do
        let atV0 ← svcDox "v0" "gR"
        let atV2 ← svcDox "v2" "gR"
        let u ← atV2.mapM (svcDox "v0")
        return sortedStrings atV0 != sortedStrings u.flatten) true⟩,
    -- Not in gamen-hs: errors and short-circuiting. Values and error texts
    -- from gamen-hs's `dclegSatisfies`/`dclegTrueIn` in GHCi.
    ⟨"Not in gamen-hs: a vertex not reached in the world is an error, never false",
      errIs (svcSat "gL" "v2" .dfBot) "dclegSatisfies: vertex \"v2\" not reached in world \"gL\""⟩,
    ⟨"Not in gamen-hs: B_i for an unknown agent is an error, never vacuously true",
      errIs (svcSat "gL" "v0" (.dfBelief "p9" dfTop))
        "doxasticSuccessors: agent \"p9\" is not in model"⟩,
    ⟨"Not in gamen-hs: ⊤ ∨ B_p9 ⊤ is true: ∨ never reaches the erroring right side",
      okIs (svcSat "gL" "v0" (.dfOr dfTop (.dfBelief "p9" dfTop))) true⟩,
    ⟨"Not in gamen-hs: (B_p9 ⊤) □→ ⊥ at outcome v1 errors: [[φ]] is computed before the premises are used",
      errIs (svcSat "gL" "v1" (.dfConditional (.dfBelief "p9" dfTop) .dfBot))
        "doxasticSuccessors: agent \"p9\" is not in model"⟩,
    ⟨"Not in gamen-hs: ⊥ □→ B_p9 ⊤ is vacuously true: ψ is never evaluated without witnesses",
      okIs (svcSat "gL" "v0" (.dfConditional .dfBot (.dfBelief "p9" dfTop))) true⟩,
    ⟨"Not in gamen-hs: dclegTrueIn (L ∨ B_p9 ⊤) errors at the first pair where L is false",
      errIs (dclegTrueIn svcModel (.dfOr (.dfMove "L") (.dfBelief "p9" dfTop)))
        "doxasticSuccessors: agent \"p9\" is not in model"⟩,
    ⟨"Not in gamen-hs: □B_p1(L) false at v0: gR's belief is R",
      okIs (svcSat "gL" "v0" (.dfBox (.dfBelief "p1" (.dfMove "L")))) false⟩,
    -- G = {premise_R} = {(gL,v0),(gR,v0)} is ⊤-consistent but not maximal:
    -- adding premise_L keeps it consistent. Every case above passes even
    -- if the maximality check is dropped; this one does not.
    ⟨"Not in gamen-hs: Centering: max^⊤_{F(gL,v0)} = [gL], so ⊤ □→ payoff_1 holds at (gL,v0)",
      okIs (maxPhiConsistent svcModel "gL" "v0" dfTop) ["gL"]
        && okIs (svcSat "gL" "v0" (.dfConditional dfTop (.dfPayoff 1 "p1"))) true⟩,
    ⟨"Not in gamen-hs: three moves: max^{M∨R}_{F(gL,v0)} = [gM, gR] (two maximal premise sets)",
      okIs (maxPhiConsistent dclegThreeMove "gL" "v0" (.dfOr (.dfMove "M") (.dfMove "R")))
        ["gM", "gR"]⟩,
    ⟨"Not in gamen-hs: three moves: max^{L∨R}_{F(gM,v0)} = [gL, gR]",
      okIs (maxPhiConsistent dclegThreeMove "gM" "v0" (.dfOr (.dfMove "L") (.dfMove "R")))
        ["gL", "gR"]⟩,
    ⟨"Not in gamen-hs: three moves: (M ∨ R) □→ payoff_1 false at (gL,v0) (gR gets 0)",
      okIs (dclegSatisfies dclegThreeMove "gL" "v0"
        (.dfConditional (.dfOr (.dfMove "M") (.dfMove "R")) (.dfPayoff 1 "p1"))) false⟩,
    -- Fixed in gamen-lean; gamen-hs TODO(#18). Deliberate divergence from
    -- gamen-hs, whose F(gA,v0) is the lone premise {gA,gB}, so max^⊤ there
    -- is [gA, gB] (review B8). With the singleton premise {(gA,v0)},
    -- Centering (§3.2.2, p. 19) gives max^⊤ = {gA}, as the thesis says it
    -- must whenever (γ,w) ∈ [[φ]].
    ⟨"Not in gamen-hs: single-move vertex: max^⊤_{F(gA,v0)} = [gA] by Centering \
      (fixed in gamen-lean; gamen-hs TODO(#18))",
      okIs (maxPhiConsistent dclegOneMove "gA" "v0" dfTop) ["gA"]⟩,
    ⟨"Not in gamen-hs: single-move vertex: a φ false at γ still selects every φ-world \
      (p □→ ⊥ false at (gA,v0): max^p = [gB])",
      okIs (maxPhiConsistent dclegOneMove "gA" "v0" (.dfProp "p")) ["gB"]
        && okIs (dclegSatisfies dclegOneMove "gA" "v0" (.dfConditional (.dfProp "p") .dfBot))
          false⟩,
    ⟨"Not in gamen-hs: Centering ∩F(γ,w) = {(γ,w)} at every decision vertex, single-move \
      ones included (§3.2.2, p. 19; fixed in gamen-lean; gamen-hs TODO(#18))",
      [dclegOneMove, dclegOneMoveDeep, svcModel, dclegThreeMove, dclegPropGame].all
        dclegCenteringAtDecisionPoints⟩,
    ⟨"Not in gamen-hs: □⊤ □→ p ↔ □⊤ → p at single-move (gB,v0): true (fixed in gamen-lean; \
      gamen-hs TODO(#18) gives false)",
      okIs (dclegSatisfies dclegOneMove "gB" "v0" (.dfConditional (.dfBox dfTop) (.dfProp "p")))
        true⟩,
    ⟨"Not in gamen-hs: §3.2.5 (p. 23): φ □→ ψ collapses to φ → ψ when φ's main connective \
      is □, at every decision vertex, single-move ones included (fixed in gamen-lean; \
      gamen-hs TODO(#18))",
      let chis : List DclegFormula := [dfTop, .dfBot, .dfProp "p", .dfNeg (.dfProp "p"),
        .dfMove "L", .dfMove "C", .dfNext dfTop, .dfYesterday dfTop, dfDiamond (.dfProp "p")]
      let psis : List DclegFormula := [.dfBot, dfTop, .dfProp "p", .dfNeg (.dfProp "p"),
        .dfMove "L", .dfNext (.dfProp "p"), .dfYesterday (.dfProp "p")]
      [dclegOneMove, dclegOneMoveDeep, svcModel, dclegThreeMove].all fun m =>
        dclegBoxCollapseAtDecisionPoints m chis psis⟩,
    -- Input now passed through withMovePremises (fixed in gamen-lean: outcome-
    -- node premises; docs/dcleg-outcome-node-premises-2026-09-30.md): the
    -- validator now also checks F, and without premises it would add Centering
    -- and Contemporary Universality messages to the two this test is about.
    ⟨"Not in gamen-hs: validateDclegModel reports a stray vertex and a stray doxastic world",
      validateDclegModel (withMovePremises <| mkDclegModel
          (mkStrategicStructure ["v0", "v1", "v2"] ["v1", "v2"] [("v0", "p1")]
            [("v0", ["L", "R"])] [("v0", "L", "v1"), ("v0", "R", "v2")])
          ["gL"] [("gL", mkHistory [("v0", "L")] "v9")] []
          [("p1", [("v0", [("gL", ["gZ"])])])] [])
        == ["validateDclegModel: world \"gL\" visits vertex \"v9\" which is not a node of the \
            strategic structure",
            "validateDclegModel: agent \"p1\" doxastic map references world \"gZ\" not in the \
            model"]⟩,
    -- Not in gamen-hs: admissible premises at every reached pair, outcome
    -- nodes included (fixed in gamen-lean; outcome-node premises;
    -- docs/dcleg-outcome-node-premises-2026-09-30.md). Centering and
    -- Contemporary Universality are §3.2.2's conditions on F (p. 19).
    ⟨"Not in gamen-hs: validateDclegModel returns [] for every test model under withMovePremises \
      (Centering and Contemporary Universality at every reached pair, outcome nodes included; \
      §3.2.2, p. 19)",
      [svcModel, dclegThreeMove, dclegOneMove, dclegOneMoveDeep, dclegPropGame,
        dclegSharedGame].all (validateDclegModel · == [])⟩,
    ⟨"Not in gamen-hs: ⊤ □→ ⊥ is false at every reached pair of dclegPropGame, outcome nodes \
      v1 and v2 included (Centering, §3.2.2, p. 19; vacuously true at v1, v2 before the fix)",
      dclegPropPoints == [("γL", "v0"), ("γL", "v1"), ("γR", "v0"), ("γR", "v2")]
        && dclegPropPoints.all fun (g, w) =>
          okIs (dclegSatisfies dclegPropGame g w (.dfConditional dfTop .dfBot)) false⟩,
    ⟨"Not in gamen-hs: default F at the shared outcome (gA,v1) of dclegOneMove is \
      {{(gA,v1)}, {(gA,v1),(gB,v1)}}",
      (dclegOneMove.dmPremises.getD ("gA", "v1") ∅).toList.map (·.toList)
        == [[("gA", "v1")], [("gA", "v1"), ("gB", "v1")]]⟩,
    ⟨"Not in gamen-hs: at the shared outcome (gA,v1) of dclegOneMove, max^⊤ = [gA] \
      (Centering, §3.2.2, p. 19) and max^{Y p} = [gB]: the outer premise selects the other \
      world reaching the outcome, so Y p □→ ⊥ is false there",
      okIs (maxPhiConsistent dclegOneMove "gA" "v1" dfTop) ["gA"]
        && okIs (maxPhiConsistent dclegOneMove "gA" "v1" (.dfYesterday (.dfProp "p"))) ["gB"]
        && okIs (dclegSatisfies dclegOneMove "gA" "v1"
          (.dfConditional (.dfYesterday (.dfProp "p")) .dfBot)) false⟩,
    ⟨"Not in gamen-hs: counterfactual modus ponens φ ∧ (φ □→ ψ) → ψ at every outcome pair of \
      every test model under withMovePremises (Centering, §3.2.2, p. 19)",
      let fs : List DclegFormula := [dfTop, .dfBot, .dfProp "p", .dfProp "alive",
        .dfYesterday (.dfProp "p"), .dfYesterday (.dfMove "L"), .dfPayoff 1 "p1", .dfPayoff 0 "p1"]
      [svcModel, dclegThreeMove, dclegOneMove, dclegOneMoveDeep, dclegPropGame,
        dclegSharedGame].all fun m =>
        isOkTrue <| ((dclegPointsOf m).filter (m.dmStructure.ssEndNodes.contains ·.2)).allM
          fun (g, w) => fs.allM fun f => fs.allM fun h =>
            dclegSatisfies m g w (dfImplies (dfAnd f (.dfConditional f h)) h)⟩,
    ⟨"Not in gamen-hs: validateDclegModel rejects F = ∅ at outcome node (γL,v1)",
      validateDclegModel { dclegPropGame with
          dmPremises := dclegPropGame.dmPremises.erase ("γL", "v1") }
        == ["validateDclegModel: F(\"γL\",\"v1\") is empty (violates Centering: ⋂F(γ,w) must \
            be {(γ,w)}, §3.2.2, p. 19)",
            "validateDclegModel: world \"γL\" reaches vertex \"v1\" but (\"γL\",\"v1\") ∉ \
            ⋃F(\"γL\",\"v1\") (violates Contemporary Universality, §3.2.2, p. 19)"]⟩,
    ⟨"Not in gamen-hs: validateDclegModel rejects a Centering violation at decision node \
      (γL,v0): F = {{(γL,v0),(γR,v0)}}",
      validateDclegModel { dclegPropGame with
          dmPremises := dclegPropGame.dmPremises.insert ("γL", "v0")
            (Std.TreeSet.ofList [Std.TreeSet.ofList [("γL", "v0"), ("γR", "v0")]]) }
        == ["validateDclegModel: ⋂F(\"γL\",\"v0\") = [(\"γL\", \"v0\"), (\"γR\", \"v0\")], \
            not {(\"γL\",\"v0\")} (violates Centering, §3.2.2, p. 19)"]⟩,
    ⟨"Not in gamen-hs: validateDclegModel rejects a Contemporary Universality violation at \
      decision node (γL,v0): F = {{(γL,v0)}} misses γR",
      validateDclegModel { dclegPropGame with
          dmPremises := dclegPropGame.dmPremises.insert ("γL", "v0")
            (Std.TreeSet.ofList [Std.TreeSet.ofList [("γL", "v0")]]) }
        == ["validateDclegModel: world \"γR\" reaches vertex \"v0\" but (\"γR\",\"v0\") ∉ \
            ⋃F(\"γL\",\"v0\") (violates Contemporary Universality, §3.2.2, p. 19)"]⟩
  ]

/-- `PaperCorrespondence.hs`'s `dclegM` (the same game as `dclegPropGame`). -/
def dclegM : DclegModel := dclegPropGame

/-- end = □¬X⊤ (§3.1.2, p. 16; v5.0's `fin`): true exactly at outcome nodes
(§3.2.3, p. 21). -/
def dclegEnd : DclegFormula := .dfBox (.dfNeg (.dfNext dfTop))

/-- start = □¬Y⊤ (§3.1.2, p. 16; v5.0's `beg`): true exactly at the unique
root (§3.2.3, p. 21). -/
def dclegStart : DclegFormula := .dfBox (.dfNeg (.dfYesterday dfTop))

def dclegPaperCorrespondenceCases : List Case :=
  let sat (g w : String) (f : DclegFormula) : Except String Bool := dclegSatisfies dclegM g w f
  let t := "Chapman (2026) — DCLEG: "
  let v5 := "DCLEG v5.0 Table 1 (not in the final thesis): "
  [ -- "§2.3 Satisfaction: atomic clauses"; final §3.2.3, p. 21
    ⟨t ++ "⊥ is never satisfied (§3.2.3, p. 21)", okIs (sat "γL" "v0" .dfBot) false⟩,
    ⟨t ++ "prop 'alive' true at (γL,v0) — only world+vertex in its extension (§3.2.3, p. 21)",
      okIs (sat "γL" "v0" (.dfProp "alive")) true⟩,
    ⟨t ++ "prop 'alive' false at (γR,v0) — not in extension (§3.2.3, p. 21)",
      okIs (sat "γR" "v0" (.dfProp "alive")) false⟩,
    ⟨t ++ "turn_p1 true at v0 — Q(v0) = p1 (§3.2.3, p. 21)", okIs (sat "γL" "v0" (.dfTurn "p1")) true⟩,
    ⟨t ++ "turn_p1 false at outcome v1 — Q undefined at end nodes (§3.2.3, p. 21)",
      okIs (sat "γL" "v1" (.dfTurn "p1")) false⟩,
    ⟨t ++ "DFMove L true at (γL,v0) — Move(γL,v0) = L (§3.2.3, p. 21)", okIs (sat "γL" "v0" (.dfMove "L")) true⟩,
    ⟨t ++ "DFMove R false at (γL,v0) — Move(γL,v0) = L, not R (§3.2.3, p. 21)",
      okIs (sat "γL" "v0" (.dfMove "R")) false⟩,
    ⟨t ++ "DFPayoff 1 p1 true at (γL,v0) — P_p1(v1) = 1 (§3.2.3, p. 21)",
      okIs (sat "γL" "v0" (.dfPayoff 1 "p1")) true⟩,
    ⟨t ++ "DFPayoff 0 p1 false at (γL,v0) — P_p1(v1) = 1, not 0 (§3.2.3, p. 21)",
      okIs (sat "γL" "v0" (.dfPayoff 0 "p1")) false⟩,
    ⟨t ++ "DFPayoff 0 p1 true at (γR,v0) — P_p1(v2) = 0 (§3.2.3, p. 21)",
      okIs (sat "γR" "v0" (.dfPayoff 0 "p1")) true⟩,
    -- "§2.3 Satisfaction: temporal operators (X and Y)"; final §3.2.3, p. 21
    ⟨t ++ "X(payoff 1) true at (γL,v0): next(v0,L)=v1, P_p1(v1)=1 (§3.2.3, p. 21)",
      okIs (sat "γL" "v0" (.dfNext (.dfPayoff 1 "p1"))) true⟩,
    ⟨t ++ "X(payoff 1) false at (γR,v0): next(v0,R)=v2, P_p1(v2)=0 (§3.2.3, p. 21)",
      okIs (sat "γR" "v0" (.dfNext (.dfPayoff 1 "p1"))) false⟩,
    ⟨t ++ "X⊤ false at outcome v1 — no move at outcome nodes (§3.2.3, p. 21, end = □¬X⊤)",
      okIs (sat "γL" "v1" (.dfNext dfTop)) false⟩,
    ⟨t ++ "Y⊤ false at root v0 — no predecessor (§3.2.3, p. 21, start = □¬Y⊤)",
      okIs (sat "γL" "v0" (.dfYesterday dfTop)) false⟩,
    ⟨t ++ "Y⊤ true at (γL,v1): predecessor is v0 (§3.2.3, p. 21)",
      okIs (sat "γL" "v1" (.dfYesterday dfTop)) true⟩,
    -- "§2.3 Satisfaction: necessity operator □"; final §3.2.3, p. 21
    ⟨t ++ "□(turn_p1) true at v0: both γL and γR reach v0 with Q(v0)=p1 (§3.2.3, p. 21)",
      okIs (sat "γL" "v0" (.dfBox (.dfTurn "p1"))) true⟩,
    ⟨t ++ "□(DFMove L) false at v0: γR reaches v0 but plays R (§3.2.3, p. 21)",
      okIs (sat "γL" "v0" (.dfBox (.dfMove "L"))) false⟩,
    ⟨t ++ "□ uniformity: □(turn_p1) has the same truth at v0 regardless of γ (§3.2.5, p. 23)",
      bothOkEq (sat "γL" "v0" (.dfBox (.dfTurn "p1"))) (sat "γR" "v0" (.dfBox (.dfTurn "p1")))⟩,
    -- "§2.3 Satisfaction: counterfactual conditional □→"; final §3.2.3, pp. 21–22
    ⟨t ++ "L □→ (payoff 1): actual-move conditional collapses to ψ at (γL,v0) — Centering (§3.2.2, p. 19)",
      okIs (sat "γL" "v0" (.dfConditional (.dfMove "L") (.dfPayoff 1 "p1"))) true⟩,
    ⟨t ++ "R □→ (payoff 0) at (γL,v0): counter-to-fact conditional selects γR (§3.2.3, p. 21)",
      okIs (sat "γL" "v0" (.dfConditional (.dfMove "R") (.dfPayoff 0 "p1"))) true⟩,
    ⟨t ++ "R □→ (payoff 1) at (γL,v0): false — γR gets payoff 0, not 1 (§3.2.3, p. 21)",
      okIs (sat "γL" "v0" (.dfConditional (.dfMove "R") (.dfPayoff 1 "p1"))) false⟩,
    ⟨t ++ "vacuous conditional (L∧R) □→ ⊥ is true at (γL,v0): no world plays both L and R (§3.2.3, p. 22)",
      okIs (sat "γL" "v0" (.dfConditional (dfAnd (.dfMove "L") (.dfMove "R")) .dfBot)) true⟩,
    -- "§2.3 Satisfaction: belief operator B_i"; final §3.2.3, p. 21.
    -- Self-Awareness is §3.2.2's doxastic condition 5 (p. 20; v5.0 §2.2's);
    -- the Haskell cites "§2.4" here and "§2.4 Cond. 5" in the fixture comment.
    ⟨t ++ "B_p1(DFMove L) true at (γL,v0): p1 considers only γL at v0 (§3.2.3, p. 21; §3.2.2 Self-Awareness, p. 20)",
      okIs (sat "γL" "v0" (.dfBelief "p1" (.dfMove "L"))) true⟩,
    ⟨t ++ "B_p1(DFMove L) false at (γR,v0): p1 in γR considers only γR where R is played (§3.2.3, p. 21)",
      okIs (sat "γR" "v0" (.dfBelief "p1" (.dfMove "L"))) false⟩,
    ⟨t ++ "B_p1(DFMove R) true at (γR,v0): p1 believes R is played — only γR considered (§3.2.3, p. 21)",
      okIs (sat "γR" "v0" (.dfBelief "p1" (.dfMove "R"))) true⟩,
    -- "§2.4 Intentional Awareness: B_i(m_i) ↔ m_i"; final §3.2.4, p. 23
    ⟨t ++ "§3.2.4 Intentional Awareness (p. 23): B_p1(L ∧ turn_p1) ↔ (L ∧ turn_p1) at (γL,v0): agent \
      correctly believes own move",
      bothOkEq (sat "γL" "v0" (.dfBelief "p1" (dfAnd (.dfMove "L") (.dfTurn "p1"))))
        (sat "γL" "v0" (dfAnd (.dfMove "L") (.dfTurn "p1")))⟩,
    -- "§2.5 / Table 1 (Some Validities): structural game laws". Table 1 is
    -- DCLEG v5.0's §2.7 ("Some Validities"), not §2.5, and the final thesis
    -- dropped it: these ten tests (with PerfectInfo in `dclegCases`) check
    -- claims only v5.0 makes, and are kept as v5.0 tests. v5.0's Table 1
    -- writes TurnStr, PerfectInfo, and SinglePref with □→; these check the
    -- material → (gamen-hs#53, fixed there by PR #61, not followed here).
    -- The end/start cases rest on definitions the final thesis keeps
    -- (§3.1.2, p. 16) and on §3.2.3's account of them (p. 21).
    ⟨t ++ v5 ++ "TurnStr: turn_p1 → □(turn_p1) at (γL,v0)",
      okIs (sat "γL" "v0" (dfImplies (.dfTurn "p1") (.dfBox (.dfTurn "p1")))) true⟩,
    ⟨t ++ v5 ++ "PerfectInfo: □(turn_p1) → B_p1(turn_p1) at (γL,v0)",
      okIs (sat "γL" "v0" (dfImplies (.dfBox (.dfTurn "p1")) (.dfBelief "p1" (.dfTurn "p1")))) true⟩,
    ⟨t ++ v5 ++ "end = □¬X⊤ (v5.0's fin) false at decision node v0: p1 still has a move \
      (§3.1.2, p. 16)",
      okIs (sat "γL" "v0" dclegEnd) false⟩,
    ⟨t ++ v5 ++ "end = □¬X⊤ (v5.0's fin) true at outcome node v1: no move remains \
      (§3.1.2, p. 16)",
      okIs (sat "γL" "v1" dclegEnd) true⟩,
    ⟨t ++ v5 ++ "start = □¬Y⊤ (v5.0's beg) true at root v0: v0 has no predecessor in \
      any world (§3.1.2, p. 16)",
      okIs (sat "γL" "v0" dclegStart) true⟩,
    ⟨t ++ v5 ++ "start = □¬Y⊤ (v5.0's beg) false at non-root v1 \
      (§3.1.2, p. 16)",
      okIs (sat "γL" "v1" dclegStart) false⟩,
    ⟨t ++ v5 ++ "OneAct: ¬end → (L ∨ R) at (γL,v0) — exactly one move is played",
      okIs (sat "γL" "v0" (dfImplies (.dfNeg dclegEnd) (.dfOr (.dfMove "L") (.dfMove "R")))) true⟩,
    ⟨t ++ v5 ++ "SinglePref: (payoff 1) → ¬(payoff 0) at (γL,v0), distinct payoffs k ≠ h",
      okIs (sat "γL" "v0" (dfImplies (.dfPayoff 1 "p1") (.dfNeg (.dfPayoff 0 "p1")))) true⟩,
    -- Haskell's title ends "(§1.2)"; CompletePref is v5.0 Table 1 (v5.0 §2.7).
    ⟨t ++ v5 ++ "CompletePref: (payoff 1) ∨ (payoff 0) holds in every world",
      okIs (["γL", "γR"].allM fun g =>
        sat g "v0" (.dfOr (.dfPayoff 1 "p1") (.dfPayoff 0 "p1"))) true⟩
  ]

/-- `RegressionIssue18.hs`, "B7: validateDclegModel catches
referential/seriality faults" (all 3 `it`s). -/
def dclegRegressionCases : List Case :=
  let ss := mkStrategicStructure ["v0", "v1", "v2"] ["v1", "v2"] [("v0", "p1")]
    [("v0", ["L", "R"]), ("v1", []), ("v2", [])] [("v0", "L", "v1"), ("v0", "R", "v2")]
  -- Deliberate divergence from gamen-hs: fixed in gamen-lean (outcome-node
  -- premises; docs/dcleg-outcome-node-premises-2026-09-30.md). The model is
  -- passed through withMovePremises: validateDclegModel now also checks
  -- Centering and Contemporary Universality (§3.2.2, p. 19), which a model
  -- with no premises fails, so without F the first `it` would report
  -- violations and the other two would pass for the wrong reason.
  let mkModelDox (dox : List (String × List (String × List (String × List String)))) :=
    withMovePremises <| mkDclegModel ss ["wL", "wR"]
      [("wL", mkHistory [("v0", "L")] "v1"), ("wR", mkHistory [("v0", "R")] "v2")]
      [] dox [("p1", [("v1", 1), ("v2", 0)])]
  [ ⟨"RegressionIssue18 B7: a well-formed model passes (no violations) (deliberate divergence \
      from gamen-hs: fixed in gamen-lean (outcome-node premises; \
      docs/dcleg-outcome-node-premises-2026-09-30.md))",
      validateDclegModel (mkModelDox [("p1", [("v0", [("wL", ["wL"]), ("wR", ["wR"])])])]) == []⟩,
    ⟨"RegressionIssue18 B7: flags N^w_i ⊄ R^w (successor does not visit the vertex)",
      validateDclegModel (mkModelDox [("p1", [("v1", [("wL", ["wR"])])])]) != []⟩,
    ⟨"RegressionIssue18 B7: flags a doxastic-seriality (KD) violation (empty successors)",
      validateDclegModel (mkModelDox [("p1", [("v0", [("wL", []), ("wR", ["wR"])])])]) != []⟩
  ]

end DclegTests

/-! ## Visualize (`Gamen.Visualize`)

gamen-hs has no spec for `Gamen.Visualize` and no `test/PaperCorrespondence.hs`
section exercises it (`grep -rlw toGraphviz test/*.hs` and the same for
`toGraphvizModel` both return nothing, `grep -n Visualize test/*.hs` is
empty). `visualizeCases` is therefore checked directly against `cabal repl
gamen:lib:gamen`'s output on the same inputs, not a ported `it`. Transcript
(gamen-hs at the commit this section was written against):

```
ghci> putStrLn (toGraphviz (mkFrame ["w1","w2","w3"]
        [("w1","w2"),("w2","w3"),("w1","w1")]))
digraph K {
  rankdir=LR;
  bgcolor="transparent";
  node [shape=circle, fontname="et-book, Palatino, serif", fontsize=12, color="#111", fontcolor="#111"];
  edge [color="#555", arrowsize=0.7];
  w1 [label="w1"];
  w2 [label="w2"];
  w3 [label="w3"];
  w1 -> w1;
  w1 -> w2;
  w2 -> w3;
}
```

and the same frame's model with `("p", ["w1","w2"])`, `("q", ["w2"])`
added (`toGraphvizModel`), plus the empty frame/model and a single world
with an atom that holds nowhere. -/
section VisualizeTests

/-- The GHCi transcript's worked frame: `w1 -> w1`, `w1 -> w2`, `w2 -> w3`. -/
def visFrame : Except String Frame :=
  mkFrame ["w1", "w2", "w3"] [("w1", "w2"), ("w2", "w3"), ("w1", "w1")]

/-- Same frame with `p` at `w1,w2` and `q` at `w2`. -/
def visModel : Except String Model :=
  visFrame.map fun fr => mkModel fr [("p", ["w1", "w2"]), ("q", ["w2"])]

def visEmptyFrame : Except String Frame := mkFrame [] []

def visEmptyModel : Except String Model := visEmptyFrame.map fun fr => mkModel fr []

/-- One world, one atom that holds nowhere: exercises the "no atoms at
this world" branch of `toGraphvizModel`'s node label. -/
def visNoAtomsModel : Except String Model :=
  (mkFrame ["w1"] []).map fun fr => mkModel fr [("p", [])]

def visualizeCases : List Case :=
  [ ⟨"Visualize toGraphviz: three worlds, a loop and a chain (GHCi transcript)",
      okIs (visFrame.map toGraphviz)
        ("digraph K {\n" ++
         "  rankdir=LR;\n" ++
         "  bgcolor=\"transparent\";\n" ++
         "  node [shape=circle, fontname=\"et-book, Palatino, serif\", fontsize=12, \
           color=\"#111\", fontcolor=\"#111\"];\n" ++
         "  edge [color=\"#555\", arrowsize=0.7];\n" ++
         "  w1 [label=\"w1\"];\n" ++
         "  w2 [label=\"w2\"];\n" ++
         "  w3 [label=\"w3\"];\n" ++
         "  w1 -> w1;\n" ++
         "  w1 -> w2;\n" ++
         "  w2 -> w3;\n" ++
         "}\n")⟩,
    ⟨"Visualize toGraphvizModel: node labels carry the atoms holding there, \
      sorted, comma-separated (GHCi transcript)",
      okIs (visModel.map toGraphvizModel)
        ("digraph K {\n" ++
         "  rankdir=LR;\n" ++
         "  bgcolor=\"transparent\";\n" ++
         "  node [shape=circle, fontname=\"et-book, Palatino, serif\", fontsize=12, \
           color=\"#111\", fontcolor=\"#111\"];\n" ++
         "  edge [color=\"#555\", arrowsize=0.7];\n" ++
         "  w1 [label=\"w1\\np\"];\n" ++
         "  w2 [label=\"w2\\np, q\"];\n" ++
         "  w3 [label=\"w3\"];\n" ++
         "  w1 -> w1;\n" ++
         "  w1 -> w2;\n" ++
         "  w2 -> w3;\n" ++
         "}\n")⟩,
    ⟨"Visualize toGraphviz: empty frame is just the scaffolding, no nodes or edges \
      (GHCi transcript)",
      okIs (visEmptyFrame.map toGraphviz)
        ("digraph K {\n" ++
         "  rankdir=LR;\n" ++
         "  bgcolor=\"transparent\";\n" ++
         "  node [shape=circle, fontname=\"et-book, Palatino, serif\", fontsize=12, \
           color=\"#111\", fontcolor=\"#111\"];\n" ++
         "  edge [color=\"#555\", arrowsize=0.7];\n" ++
         "}\n")⟩,
    ⟨"Visualize toGraphvizModel: empty model matches empty frame (GHCi transcript)",
      okIs (visEmptyModel.map toGraphvizModel)
        ("digraph K {\n" ++
         "  rankdir=LR;\n" ++
         "  bgcolor=\"transparent\";\n" ++
         "  node [shape=circle, fontname=\"et-book, Palatino, serif\", fontsize=12, \
           color=\"#111\", fontcolor=\"#111\"];\n" ++
         "  edge [color=\"#555\", arrowsize=0.7];\n" ++
         "}\n")⟩,
    ⟨"Visualize toGraphvizModel: an atom with no worlds in its extension leaves the \
      node's second label line off (GHCi transcript)",
      okIs (visNoAtomsModel.map toGraphvizModel)
        ("digraph K {\n" ++
         "  rankdir=LR;\n" ++
         "  bgcolor=\"transparent\";\n" ++
         "  node [shape=circle, fontname=\"et-book, Palatino, serif\", fontsize=12, \
           color=\"#111\", fontcolor=\"#111\"];\n" ++
         "  edge [color=\"#555\", arrowsize=0.7];\n" ++
         "  w1 [label=\"w1\"];\n" ++
         "}\n")⟩
  ]

end VisualizeTests

def main : IO UInt32 := do
  let mut failures := 0
  IO.println "Unit cases"
  for c in unitCases ++ tableauCases ++ formulaCases ++ widgetCases ++ answerKeyCases ++ CountermodelViewTests.cases ++ framePropertiesCases
      ++ kripkeCases ++ stitCases ++ stitPaperCorrespondenceCases ++ stitRegressionCases
      ++ xstitCases ++ xstitPaperCorrespondenceCases ++ xstitRegressionCases
      ++ epistemicCases ++ epistemicPaperCorrespondenceCases ++ epistemicRegressionCases
      ++ semanticsCases ++ fragmentCases ++ temporalCases ++ doxasticCases ++ rankingTheoryCases
      ++ plausibilityCases ++ sequentCases ++ rulesCases ++ saturationCases ++ proveCases
      ++ deonticStitCases ++ counterModelCases ++ closureCases ++ crossCheckCases ++ cgsCases
      ++ coalitionCases
      ++ atlModelCheckCases ++ atlCases ++ lacaCases ++ lacaPaperCorrespondenceCases
      ++ atelCases ++ atelRegressionCases ++ atlirCases ++ atlirRegressionCases
      ++ dclegCases ++ dclegPaperCorrespondenceCases ++ dclegRegressionCases
      ++ visualizeCases do
    IO.println s!"  {if c.ok then "✓" else "✗"} {c.name}"
    unless c.ok do failures := failures + 1
  -- Gamen.ManyValued (Lean-only): unit cases, then the CQL/FHIRPath spec
  -- tables in `data/specs/` checked against strong Kleene.
  let specCases ← ManyValuedTests.specTableCases
  let dclegServiceCases ← DclegServiceTests.cases
  for (name, ok) in ManyValuedTests.cases ++ specCases ++ CompletionTests.cases
      ++ ManyValuedNotebookTests.cases ++ ValidateVersionTests.cases ++ ValidateAtlTests.cases ++ AtlDynamicTests.cases ++ ActionModelTests.cases ++ ValidateEpistemicTests.cases ++ UpdateSearchTests.cases ++ SocialLawTests.cases
      ++ ProtocolFlatTests.cases ++ dclegServiceCases do
    IO.println s!"  {if ok then "✓" else "✗"} {name}"
    unless ok do failures := failures + 1
  IO.println "Properties (Plausible; sample size varies by property, see Tests/Main.lean)"
  for (name, prop) in properties do
    let ok ← prop
    IO.println s!"  {if ok then "✓" else "✗"} {name}"
    unless ok do failures := failures + 1
  let total := unitCases.length + tableauCases.length + formulaCases.length + widgetCases.length + answerKeyCases.length
    + CountermodelViewTests.cases.length
    + framePropertiesCases.length + kripkeCases.length
    + stitCases.length + stitPaperCorrespondenceCases.length + stitRegressionCases.length
    + xstitCases.length + xstitPaperCorrespondenceCases.length + xstitRegressionCases.length
    + epistemicCases.length + epistemicPaperCorrespondenceCases.length + epistemicRegressionCases.length
    + semanticsCases.length
    + fragmentCases.length + temporalCases.length + doxasticCases.length + rankingTheoryCases.length + plausibilityCases.length
    + sequentCases.length + rulesCases.length + saturationCases.length + proveCases.length
    + deonticStitCases.length + counterModelCases.length + closureCases.length
    + crossCheckCases.length + cgsCases.length + coalitionCases.length
    + atlModelCheckCases.length + atlCases.length
    + lacaCases.length + lacaPaperCorrespondenceCases.length
    + atelCases.length + atelRegressionCases.length
    + atlirCases.length + atlirRegressionCases.length
    + dclegCases.length + dclegPaperCorrespondenceCases.length + dclegRegressionCases.length
    + visualizeCases.length
    + ManyValuedTests.cases.length + specCases.length + CompletionTests.cases.length
    + ManyValuedNotebookTests.cases.length + ValidateVersionTests.cases.length + ValidateAtlTests.cases.length + AtlDynamicTests.cases.length + ActionModelTests.cases.length + ValidateEpistemicTests.cases.length + UpdateSearchTests.cases.length + SocialLawTests.cases.length
    + ProtocolFlatTests.cases.length + dclegServiceCases.length
    + properties.length
  IO.println s!"{total - failures}/{total} passed"
  return if failures == 0 then 0 else 1
