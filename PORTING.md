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
| Formula | 446 | — | sonnet | **Mostly done** (`Gamen/Formula.lean`): all 30 constructors, printing, `atoms`, `toNNF`, `isNNF`, `isModalFree`, `hasAgentOperator`. Missing: `dstit`, `commitment`. |
| Verdict | 68 | — | — | **Done** |
| Kripke | 147 | Formula | sonnet | **Partial**: `Frame`, `Model`, `mkFrame`, `mkModel`. Missing: `isEquivalenceOn`, `equivalenceClasses`, `checkIndependence`. Port per `docs/assessment/lean-library-reuse-2026-09-23.md` §2: put shared reflexive/symmetric/transitive/`subsetOf` checks in `Kripke.lean`, build `isEquivalenceOn` on them, and make FrameProperties' `isReflexive`/`isSymmetric`/`isTransitive` one-line wrappers (results unchanged; its tests must stay green). Keep `equivalenceClasses` as written (order matters). |
| Semantics | 212 | Formula, Kripke | sonnet | **Done** (`Gamen/Semantics.lean`): `satisfies`, `isTrueIn`, `isValid`, `isTautology` (via `abstractModal`), `entails`. B&D citations (Definition 1.7/1.9/1.11/1.23) checked against `notes/bd-screen.pdf`; correct as written in the Haskell. One fix: `Semantics.hs`'s `isTautology` cites "Definition 1.16", but p. 12–13 of the PDF has "tautological instance" as *Definition 1.14*; 1.16 is *Proposition 1.16* ("All tautological instances are valid"), a different claim. The Lean docstring cites both correctly. `abstractModal` includes the fix for chapmanbe/gamen-hs#31 (gamen-hs `1f9edb2`): subformulas are keyed on the formula, not its printed form, with the 4 new B5 tests plus one stronger prefix test. |
| Tableau | 1067 | Formula, Kripke, Semantics, Verdict | opus | **Partial**: engine, blocking, all passes, driver, countermodels, closures; systems K and KDt (D rules). Missing: KT, KD, KB, K4, S4, S5 rule sets (Table 6.4). Temporal rules stay quarantined (gamen-hs issue #25). |
| Fragment | 242 | Formula, Tableau, Verdict | — | **Done** (`Gamen/Fragment.lean`): `constructorName`, `immediateSubformulas`, `firstOffender`, `allowedInTableau`, `allowedInDS`, `checkTableauFragment`, `checkDSFragment`, split out of `Gamen/Protocol.lean` into its own module. `Validate.lean`'s `classifyConsistency` gates through `checkTableauFragment`/`checkDSFragment` directly, as `validate/Main.hs` does. No B&D citations in this module (the only citation, "Lyon & van Berkel 2024, Definition 3", is external to `bd-screen.pdf`). |
| FrameProperties | 172 | Formula, Kripke, Semantics | — | **Done** (`Gamen/FrameProperties.lean`): all predicates and `isValidOnFrame`. Two of the Haskell docstring's B&D citations were wrong for `notes/bd-screen.pdf` and were corrected in the port (basic properties are Table 2.1, not "Definition 2.3"; frame validity is Definition 2.4, not "Definition 2.1"); gamen-hs's internal "frd.N" tags for Definition 2.11 / Proposition 2.9 / 2.12 / 2.14 all checked out and are spelled out as real chapter-2 numbers. |
| Temporal | 210 | Formula, Kripke, Tableau | opus | Not started (semantics already in `Semantics.lean`; `systemKDt`'s D rules in `Tableau.lean`) |
| Doxastic | 56 | Formula, Tableau | sonnet | Not started (needed by `gamen-validate`) |
| RankingTheory | 454 | Formula, Kripke, Tableau | opus | Not started (needed by `gamen-validate`) |
| Plausibility | 340 | Kripke, RankingTheory | sonnet | Not started; the one Haskell typeclass (`class Plausibility`) maps to a Lean `class` directly |
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
| `validate/Main.hs` (`gamen-validate`) | 329 | **Done for the tableau backend.** The non-`IO` request/response logic lives in `Validate/Core.lean` (split out of `Validate.lean`, which now only wraps it with `main`, so `Tests.Main` can `import Validate.Core` for direct unit tests without the two executables' `main` colliding). Requests needing the doxastic/ranking rules or the deontic-STIT prover answer `"not ported in Lean slice: …"` until those modules land. `reasonOperator` (validate/Main.hs:271-276) is ported faithfully: a non-`UnsupportedOperator` reason renders as GHC's derived `Show UnknownReason` would, not Lean's `reprStr` — verified against `runghc` output, not from memory. |
| `protocol/Service/*` + `service/Main.hs` (dcleg service) | 893 | Not started |
| `app/Main.hs` (`gamen-repl` demo) | 43 | Not started |

### Tests

| gamen-hs test | Lines | Lean status |
|---|---:|---|
| TableauSpec | 229 | K-system cases ported (`Tests/Main.lean`) |
| Properties | 910 | NNF properties ported (Plausible). The fragment-boundary half of the "issue #25" `it` (steps 2–3: `checkTableauFragment systemKDt` rejects every temporal operator, nested or not, and does not over-reach on the non-temporal operators) is ported in `fragmentCases`; steps 1 (exhaustive semantic-oracle search) and 4 (raw `tableauConsistent systemKDt` on the unsatisfiable past-operator set) are deferred to `Gamen.Temporal`. Rest not started. |
| ProtocolSpec, DclegServiceSpec | 565 | Covered for `gamen-validate` by the side-by-side harness (`tools/compare/`); unit specs not ported |
| FramePropertiesSpec | 356 | **Done** (`Tests/Main.lean`, `framePropertiesCases`) |
| KripkeSemanticsSpec | 88 | **Done** (`Tests/Main.lean`, `semanticsCases`): all 9 `it`s, including the gamen-hs#3 world-existence-guard regression (checked as a genuine `Except` error, not coerced to a default). |
| FormulaSpec, TemporalSpec, EpistemicSpec, StitSpec, XstitSpec, LacaSpec, DeonticStitSpec, RankingTheorySpec, PlausibilitySpec, WorldGuardsSpec | ~2,500 | Not started: port with each module |
| PaperCorrespondence | 1,848 | The "Boxes & Diamonds Ch. 1 (Zach 2019)" section is **done**: the `isValidOnFrame`-exercising "Definition 1.11" slice was already in `framePropertiesCases`; `semanticsCases` now adds Definition 1.6 (model as triple), Definition 1.7 (all 8 truth clauses), Proposition 1.8 (□/◇ duality), Definition 1.9 (truth in a model), Proposition 1.19 (K is K-provable, via `systemK`), and Definition 1.23 + Example 1.24 (entailment) — 39 cases total. All of that section's B&D page/definition numbers were checked against `notes/bd-screen.pdf` and were already correct in the Haskell. The rest of the file (Lyon & van Berkel deontic-STIT, Stit/Xstit/Dcleg/ATL sections) needs modules not yet ported; port the remaining sections with each module |
| RegressionIssue18 | 481 | "A2: fragment gating rejects out-of-fragment operators" ported in full (6 `it`s, `fragmentCases` in `Tests/Main.lean`); the rest needs modules not yet ported (doxastic/ranking, deontic-STIT, ATLir, Epistemic, Stit, Xstit, Cgs, Dcleg, Kripke/FrameProperties dangling-edge cases beyond what `FramePropertiesSpec` already covers) |

## Proposed order

Each wave ends with its tests ported and `tools/compare/compare.py` green.

1. **Finish the core.** Add `dstit`/`commitment`, the rest of `Kripke` and
   `Semantics`, the KT–S5 rule sets. Port `FormulaSpec`,
   `KripkeSemanticsSpec`, the rest of `TableauSpec`. (`FrameProperties` and
   `FramePropertiesSpec` are done; `Fragment` is split out of
   `Protocol.lean` into its own module and done.)
2. **Complete the `gamen-validate` tableau backend.** `Doxastic`,
   `RankingTheory` (+ `Plausibility`). After this, belief/ranked-belief
   requests stop being scope gaps in the comparison.
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
