# Porting gamen-hs to Lean 4

Source of truth: [gamen-hs](https://github.com/chapmanbe/gamen-hs), local
checkout `~/Projects/Logic/Haskell/gamen-hs`, at `e218749` (2026-09-23) when
this plan was written. Background and evidence for choosing Lean:
`docs/assessment/`.

## Status by module

Lines are gamen-hs source lines. "Depends on" lists gamen-hs imports. "Porter" is the
model `/port-module` runs the `module-porter` agent on (the review is always
Opus). `opus` or `fable` marks the risky ports: termination rewrites, search
loops needing fuel, laziness, the deontic-STIT saturation loop. It is a first
cut; change it when a port proves easier or harder than expected. `—` means
nothing left to port.

### Core (`src/Gamen/`)

| Module | Lines | Depends on | Porter | Lean status |
|---|---:|---|---|---|
| Formula | 446 | — | sonnet | **Done** (`Gamen/Formula.lean`): all 30 constructors, printing, `atoms`, `toNNF`, `isNNF`, `isModalFree`, `hasAgentOperator`, `dstit`, `commitment`. B&D citation fixed: the module docstring cited "Definition 1.1", which in `notes/bd-screen.pdf` is the *language* (symbol inventory); the formula ADT itself is *Definition 1.2* (p. 5), which is what the Haskell's own module haddock already cites correctly. `dstit`/`commitment` cite Lorini (2013), external to B&D — not checked against the PDF. |
| Verdict | 68 | — | — | **Done** |
| Kripke | 147 | Formula | sonnet | **Done** (`Gamen/Kripke.lean`): `Frame`, `Model`, `mkFrame`, `mkModel`, plus the shared relation utilities `subsetOf`, `reflexiveOn`, `symmetricOn`, `transitiveOn`, `isEquivalenceOn`, `equivalenceClasses`, `sections` (the `List` cartesian-product helper, matching Haskell's `sequence` order), and `checkIndependence`, per `docs/assessment/lean-library-reuse-2026-09-23.md` §2: `subsetOf`/`reflexiveOn`/`symmetricOn`/`transitiveOn` now live in `Kripke.lean` (moved from `FrameProperties.lean`), and `FrameProperties.isReflexive`/`isSymmetric`/`isTransitive` are one-line wrappers over them (results unchanged). `equivalenceClasses` keeps the exact Haskell algorithm and output order. No B&D citations to check in this module (the utilities are uncited in the Haskell). |
| Semantics | 212 | Formula, Kripke | sonnet | **Done** (`Gamen/Semantics.lean`): `satisfies`, `isTrueIn`, `isValid`, `isTautology` (via `abstractModal`), `entails`. B&D citations (Definition 1.7/1.9/1.11/1.23) checked against `notes/bd-screen.pdf`; correct as written in the Haskell. One fix: `Semantics.hs`'s `isTautology` cites "Definition 1.16", but p. 12–13 of the PDF has "tautological instance" as *Definition 1.14*; 1.16 is *Proposition 1.16* ("All tautological instances are valid"), a different claim. The Lean docstring cites both correctly. `abstractModal` includes the fix for chapmanbe/gamen-hs#31 (gamen-hs `1f9edb2`): subformulas are keyed on the formula, not its printed form, with the 4 new B5 tests plus one stronger prefix test. |
| Tableau | 1067 | Formula, Kripke, Semantics, Verdict | opus | **Done** (`Gamen/Tableau.lean`): engine, blocking, all passes, driver, countermodels, closures; `mkPrefix`/`extendPrefix`/`parentPrefix` (as `Except`); the Table 6.3 rules (T, D, B, 4, 4r; Haskell's `apply…Rule` names without the `apply` prefix, matching the already-ported rules) and systems K, KT, KD, KB (= KTB), K4, S4, S5 (Table 6.4), plus KDt's D rules for `gamen-validate`. FutureBox/FutureDiamond rules stay quarantined (gamen-hs issue #25). Citations fixed: prefixes and prefixed formulas are prose in B&D §6.1 and closure in §6.2, not Definitions 6.1–6.3 (Def 6.3 is interpretation of prefixes); the D rules are Table 6.3, not 6.4. |
| Fragment | 242 | Formula, Tableau, Verdict | — | **Done** (`Gamen/Fragment.lean`): `constructorName`, `immediateSubformulas`, `firstOffender`, `allowedInTableau`, `allowedInDS`, `checkTableauFragment`, `checkDSFragment`, split out of `Gamen/Protocol.lean` into its own module. `Validate.lean`'s `classifyConsistency` gates through `checkTableauFragment`/`checkDSFragment` directly, as `validate/Main.hs` does. No B&D citations in this module (the only citation, "Lyon & van Berkel 2024, Definition 3", is external to `bd-screen.pdf`). |
| FrameProperties | 172 | Formula, Kripke, Semantics | — | **Done** (`Gamen/FrameProperties.lean`): all predicates and `isValidOnFrame`. Two of the Haskell docstring's B&D citations were wrong for `notes/bd-screen.pdf` and were corrected in the port (basic properties are Table 2.1, not "Definition 2.3"; frame validity is Definition 2.4, not "Definition 2.1"); gamen-hs's internal "frd.N" tags for Definition 2.11 / Proposition 2.9 / 2.12 / 2.14 all checked out and are spelled out as real chapter-2 numbers. |
| Temporal | 210 | Formula, Kripke, Tableau | opus | Not started (semantics already in `Semantics.lean`; `systemKDt`'s D rules in `Tableau.lean`) |
| Doxastic | 56 | Formula, Tableau | sonnet | **Done** (`Gamen/Doxastic.lean`): `applyDoxasticDRule`, `doxasticRules`. No B&D citation in the Haskell docstring to check (KD45 belief axioms K/D/4/5 are named, not numbered against `bd-screen.pdf`). Wired into `gamen-validate`: `Validate/Core.lean`'s `consistencySystem` is KDt + `doxasticRules` + `rankingRules`, as in `validate/Main.hs` (`rankingRules` added with RankingTheory). compare.py section H covers plain belief. |
| RankingTheory | 454 | Formula, Kripke, Tableau | opus | **Done** (`Gamen/RankingTheory.lean`): every exported function, same names. Every `error` is an `Except` with the Haskell message; where Haskell's laziness or `&&`/`\|\|`/`any`/`all` short-circuiting skips a call that could error, the Lean skips it too (`applyEvidence` runs `conditionalize`'s guards before computing τ, as the lazy rank thunk does). Haskell's 64-bit `maxBound`/`minBound` sentinels (κ(∅), τ = ±∞) are kept as `rankMaxBound`/`rankMinBound` with the same values, since `Rank` is Lean's unbounded `Int`. No B&D citations apply; the Spohn (1988) citations were checked against `gamen-hs/notes/spohn1988-ordinal-conditional-functions.pdf`, and the "p. 117" for the "additional reason … strengthened" quote is fixed to p. 118. Wired into `gamen-validate`: `consistencySystem` now appends `rankingRules`, so `rankedBelief` requests are answered (compare.py section I). |
| Plausibility | 340 | Kripke, RankingTheory | sonnet | **Done** (`Gamen/Plausibility.lean`): the Haskell typeclass `class Eq p => Plausibility p` is a Lean `class Plausibility (p : Type) [BEq p]`, with `plBot`/`plTop`/`plLeq`/`plJoin`/`plTimes`/`plCondition` exported so call sites write the bare Haskell names; `[BEq p]` is written out at every call site since Lean does not project a class's own instance-implicit parameters the way Haskell projects a superclass. All three carriers (`RankedPlausibility`, `ProbabilityPlausibility`, `PossibilityPlausibility`, the last two over Lean's exact `Rat`) and the abstract measure layer (`PlausibilityMeasure`, `mkMeasure`, `plPoint`, `plDomain`, `plOf`, `isNormalized`, `conditionOn`, `mostPlausible`) and the `Gamen.RankingTheory` bridge (`agentMeasure`) are ported, same names. `mkRank`/`mkProbability`/`mkPossibility`/`agentMeasure`'s unknown-agent case are `Except`, not `error`. Haskell's `agentMeasure` is not itself wrapped in `Except` — it calls the pure smart constructor `mkRank` per κ-value via `Map.map` from the module's `Data.Map.Strict` import, which forces every value to WHNF at construction, so Haskell already crashes immediately on an out-of-invariant negative rank, not lazily. The Lean port makes that eager check explicit as an `Except`, inside the one `agentMeasure` already returns for the unknown-agent case, rather than an uncatchable `error`; not a behavior deviation. Not exercised by any ported test (every `KappaModel` in scope is well-formed). No B&D citations apply (Halpern/Spohn are external to `bd-screen.pdf`, already checked in `Gamen.RankingTheory`). Not wired into `gamen-validate`: `validate/Main.hs` never imports `Gamen.Plausibility` (only present in gamen-hs's export list and test suite), so there is nothing for `compare.py` to gain here. |
| Epistemic | 411 | Formula, Kripke | fable | Not started; see the laziness note under Conventions |
| DeonticStit | 277 | Formula, Kripke | sonnet | Not started |
| DeonticStit.Sequent | 209 | Formula | sonnet | Not started |
| DeonticStit.Rules | 515 | Sequent, Formula | opus | Not started |
| DeonticStit.Saturation | 341 | Rules, Sequent, Formula | fable | Not started |
| DeonticStit.Prove | 250 | Rules, Saturation, Sequent, Formula, Verdict | opus | Not started (needed by `gamen-validate`) |
| DeonticStit.CounterModel | 199 | DeonticStit, Rules, Saturation, Sequent, Formula, Kripke | opus | Not started |
| Stit | 348 | Formula, Kripke | sonnet | Not started |
| Xstit | 417 | Formula, Kripke | opus | Not started |
| Laca | 274 | Cgs, Formula | sonnet | Not started |
| Cgs | 164 | — | sonnet | Not started |
| Coalition | 142 | Cgs, Formula | sonnet | Not started |
| Atl.Strategy | 35 | — | sonnet | Not started |
| Atl.ModelCheck | 116 | Cgs, Formula | sonnet | Not started |
| Atl | 47 | Atl.ModelCheck, Atl.Strategy, Cgs, Formula | sonnet | Not started |
| Atel | 184 | Atl.ModelCheck, Cgs, Formula | sonnet | Not started |
| Atl.ImperfectInfo | 335 | Atel, Atl.ModelCheck, Cgs, Formula | opus | Not started |
| Dcleg | 528 | — | opus | Not started |
| Visualize | 83 | Formula, Kripke | — | Superseded by `Widgets/KripkeExplorer.lean` for teaching; port only if a text/DOT export is needed |

### Protocol and executables

| Component | Lines | Lean status |
|---|---:|---|
| `protocol/Gamen/Protocol/Formula.hs` | 167 | **Done** (`Gamen/Protocol.lean`): tree and flat formats, all 30 constructors. Fragment gating that used to live here moved to `Gamen/Fragment.lean`. |
| `validate/Main.hs` (`gamen-validate`) | 329 | **Done for the tableau backend.** The non-`IO` request/response logic lives in `Validate/Core.lean` (split out of `Validate.lean`, which now only wraps it with `main`, so `Tests.Main` can `import Validate.Core` for direct unit tests without the two executables' `main` colliding). Ranked-belief requests are answered since the RankingTheory port. Requests needing the deontic-STIT prover answer `"not ported in Lean slice: …"` until those modules land. `reasonOperator` (validate/Main.hs:271-276) is ported faithfully: a non-`UnsupportedOperator` reason renders as GHC's derived `Show UnknownReason` would, not Lean's `reprStr` — verified against `runghc` output, not from memory. |
| `protocol/Service/*` + `service/Main.hs` (dcleg service) | 893 | Not started |
| `app/Main.hs` (`gamen-repl` demo) | 43 | Not started |

### Tests

| gamen-hs test | Lines | Lean status |
|---|---:|---|
| TableauSpec | 229 | **Done**: all 43 `it`s in `tableauCases` (`Tests/Main.lean`), plus two KTB cases (B, and not 4) that exercise the B rules, which no spec `it` does. Two case names corrected: gamen-hs labels □p → ◇□p as axiom "B" (B&D's B is A → □◇A, Table 2.1) and cites Example 6.9 for it (Example 6.9 proves S5 ⊢ □A → □◇A). No `PaperCorrespondence.hs` block beyond the already-ported Prop. 1.19 `it` exercises the non-temporal, non-doxastic tableau; the `systemKDt` block waits on `Gamen.Temporal`; the `applyDoxasticDRule` block is now ported (`doxasticCases`, see PaperCorrespondence row). |
| Properties | 910 | NNF properties ported (Plausible). The fragment-boundary half of the "issue #25" `it` (steps 2–3: `checkTableauFragment systemKDt` rejects every temporal operator, nested or not, and does not over-reach on the non-temporal operators) is ported in `fragmentCases`; steps 1 (exhaustive semantic-oracle search) and 4 (raw `tableauConsistent systemKDt` on the unsatisfiable past-operator set) are deferred to `Gamen.Temporal`. The two "Gamen.RankingTheory: structural invariants" properties (τ(¬φ) = −τ(φ); `conditionalize` preserves `wellFormed`) are not yet ported: they need a random `KappaModel` generator. Rest not started. |
| ProtocolSpec, DclegServiceSpec | 565 | Covered for `gamen-validate` by the side-by-side harness (`tools/compare/`); unit specs not ported |
| FramePropertiesSpec | 356 | **Done** (`Tests/Main.lean`, `framePropertiesCases`) |
| KripkeSemanticsSpec | 88 | **Done** (`Tests/Main.lean`, `semanticsCases`): all 9 `it`s, including the gamen-hs#3 world-existence-guard regression (checked as a genuine `Except` error, not coerced to a default). |
| FormulaSpec | 171 | **Done** (`Tests/Main.lean`, `formulaCases`): all 23 `it`s, both describe blocks ("Formula (Definition 1.2)" and "Negation Normal Form"). The `dstit`/`commitment` `it`s live in `StitSpec`/`LacaSpec`, not `FormulaSpec` — ported with those modules. |
| RankingTheorySpec | 256 | **Done** (`Tests/Main.lean`, `rankingTheoryCases`): all 40 `it`s. One case name cites Spohn p. 118 instead of the Haskell's p. 117 (see the RankingTheory row). |
| PlausibilitySpec | 264 | **Done** (`Tests/Main.lean`, `carrierLawCases`×3 + `plausibilityConstructorCases` + `rankedConditioningCases` + `probabilityConditioningCases` + `possibilityConditioningCases` + `plAgreementCases` + `mostPlausibleCases` + `agentMeasureCases`): all 57 examples (`cabal test --test-options="--match Plausibility"` → `57 examples, 0 failures`), including the shared `carrierLaws` helper run once per carrier. No `PaperCorrespondence.hs` section exercises `Gamen.Plausibility` (checked by grep; none found). |
| TemporalSpec, EpistemicSpec, StitSpec, XstitSpec, LacaSpec, DeonticStitSpec, WorldGuardsSpec | ~1,786 | Not started: port with each module |
| PaperCorrespondence | 1,848 | The "Boxes & Diamonds Ch. 1 (Zach 2019)" section is **done**: the `isValidOnFrame`-exercising "Definition 1.11" slice was already in `framePropertiesCases`; `semanticsCases` now adds Definition 1.6 (model as triple), Definition 1.7 (all 8 truth clauses), Proposition 1.8 (□/◇ duality), Definition 1.9 (truth in a model), Proposition 1.19 (K is K-provable, via `systemK`), and Definition 1.23 + Example 1.24 (entailment) — 39 cases total. All of that section's B&D page/definition numbers were checked against `notes/bd-screen.pdf` and were already correct in the Haskell. "Gamen.Doxastic — KD45 belief (non-factive)": the "applyDoxasticDRule: tableau closure for contradictory beliefs" describe block is **done** (3 `it`s, `doxasticCases` in `Tests/Main.lean`); its two sibling describe blocks ("Non-factiveness…", "D axiom: B_a φ → ¬B_a(¬φ)…", 3 `it`s each) exercise `Gamen.Epistemic` (`eSatisfies`, `mkEpistemicModel`, `mkEpistemicFrameWithBelief`, `Knowledge`), not yet ported — port with `Gamen.Epistemic`. "Spohn (1988) — ranking theory" is **done** (all 15 `it`s, at the end of `rankingTheoryCases`); its Spohn page and definition numbers were checked against the PDF and are correct. The rest of the file (Lyon & van Berkel deontic-STIT, Stit/Xstit/Dcleg/ATL sections) needs modules not yet ported; port the remaining sections with each module |
| RegressionIssue18 | 481 | "A2: fragment gating rejects out-of-fragment operators" ported in full (6 `it`s, `fragmentCases` in `Tests/Main.lean`); "B7: Kripke / FrameProperties dangling-edge and class fixes" ported in full (4 `it`s, `kripkeCases`); "B4: ranking theory κ=∞ no longer leaks into arithmetic" ported in full (5 `it`s, end of `rankingTheoryCases`); the rest needs modules not yet ported (deontic-STIT, ATLir, Epistemic, Stit, Xstit, Cgs, Dcleg) |

## Proposed order

Each wave ends with its tests ported and `tools/compare/compare.py` green.

1. **Finish the core. Done.** `Formula` (including `dstit`/`commitment`),
   `Kripke`, `Semantics`, `Fragment` (split out of `Protocol.lean`),
   `FrameProperties`, and `Tableau` (K, KT, KD, KTB, K4, S4, S5), with
   `FormulaSpec`, `KripkeSemanticsSpec`, `FramePropertiesSpec` and
   `TableauSpec`.
2. **Complete the `gamen-validate` tableau backend. Done.** `Doxastic`
   (plain belief; compare.py section H) and `RankingTheory` (ranked belief;
   section I) are ported and wired. `Plausibility` is ported but not wired,
   because gamen-hs's own `validate/Main.hs` never imports it. The
   remaining 26 scope gaps are all deontic STIT.
3. **Deontic STIT (G3DS^k_n, Lyon & van Berkel 2024).** `Sequent` →
   `Rules` → `Saturation` → `Prove` → `CounterModel`, with
   `DeonticStitSpec`. The largest remaining risk: expect termination-checker
   work in the saturation loop. After this, `gamen-validate` is complete and
   the comparison should show no scope gaps.
4. **Remaining logics.** `Temporal`, `Epistemic`, `Stit`, `Xstit`, `Cgs`,
   `Laca`, `Coalition`, `Atl.*`, `Atel`.
5. **dcleg service and extras.** `Dcleg`, `protocol/Service/*`,
   `service/Main.hs`, `app/Main.hs`; extend the comparison harness to the
   dcleg service's protocol.

In parallel: teaching notebooks, one Gamen.jl Pluto chapter at a time
(`Notebooks/`), reusing `Widgets/`.

## Verification

- `lake test`: unit cases, widget-interaction tests, notebook answer keys,
  Plausible properties.
- `tools/compare/compare.py`: sends the same JSON Lines requests to the
  gamen-hs and Lean `gamen-validate` binaries and classifies every response
  (identical / equivalent / scope gap / DISAGREE). Needs gamen-hs built.
  The 2026-09-23 baseline was 3,653 requests, 0 disagreements
  (`docs/assessment/compare-summary-2026-09-23.txt`).
- Before trusting a new green run, plant a bug and confirm the tests catch
  it (done for NNF, the D rules, and the widget event order).
