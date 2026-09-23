# Porting gamen-hs to Lean 4

Source of truth: [gamen-hs](https://github.com/chapmanbe/gamen-hs), local
checkout `~/Projects/Logic/Haskell/gamen-hs`, at `e218749` (2026-09-23) when
this plan was written. Background and evidence for choosing Lean:
`docs/assessment/`.

## Status by module

Lines are gamen-hs source lines. "Depends on" lists gamen-hs imports.

### Core (`src/Gamen/`)

| Module | Lines | Depends on | Lean status |
|---|---:|---|---|
| Formula | 446 | — | **Mostly done** (`Gamen/Formula.lean`): all 30 constructors, printing, `atoms`, `toNNF`, `isNNF`, `isModalFree`. `hasAgentOperator` lives in `Gamen/Protocol.lean`. Missing: `dstit`, `commitment`. |
| Verdict | 68 | — | **Done** |
| Kripke | 147 | Formula | **Partial**: `Frame`, `Model`, `mkFrame`, `mkModel`. Missing: `isEquivalenceOn`, `equivalenceClasses`, `checkIndependence`. |
| Semantics | 212 | Formula, Kripke | **Done** (`satisfies`, `isTrueIn`). Missing: `isValid`, `isTautology`, `entails`. |
| Tableau | 1067 | Formula, Kripke, Semantics, Verdict | **Partial**: engine, blocking, all passes, driver, countermodels, closures; systems K and KDt (D rules). Missing: KT, KD, KB, K4, S4, S5 rule sets (Table 6.4). Temporal rules stay quarantined (gamen-hs issue #25). |
| Fragment | 242 | Formula, Tableau, Verdict | **Done**, but lives in `Gamen/Protocol.lean`; split out to `Gamen/Fragment.lean` to keep the one-to-one module mapping. |
| FrameProperties | 172 | Formula, Kripke, Semantics | **Done** (`Gamen/FrameProperties.lean`): all predicates and `isValidOnFrame`. Two of the Haskell docstring's B&D citations were wrong for `notes/bd-screen.pdf` and were corrected in the port (basic properties are Table 2.1, not "Definition 2.3"; frame validity is Definition 2.4, not "Definition 2.1"); gamen-hs's internal "frd.N" tags for Definition 2.11 / Proposition 2.9 / 2.12 / 2.14 all checked out and are spelled out as real chapter-2 numbers. |
| Temporal | 210 | Formula, Kripke, Tableau | Not started (semantics already in `Semantics.lean`; `systemKDt`'s D rules in `Tableau.lean`) |
| Doxastic | 56 | Formula, Tableau | Not started (needed by `gamen-validate`) |
| RankingTheory | 454 | Formula, Kripke, Tableau | Not started (needed by `gamen-validate`) |
| Plausibility | 340 | Kripke, RankingTheory | Not started; the one Haskell typeclass (`class Plausibility`) maps to a Lean `class` directly |
| Epistemic | 411 | Formula, Kripke | Not started; see the laziness note under Conventions |
| DeonticStit | 277 | Formula, Kripke | Not started |
| DeonticStit.Sequent | 209 | Formula | Not started |
| DeonticStit.Rules | 515 | Sequent, Formula | Not started |
| DeonticStit.Saturation | 341 | Rules, Sequent, Formula | Not started |
| DeonticStit.Prove | 250 | Rules, Saturation, Sequent, Formula, Verdict | Not started (needed by `gamen-validate`) |
| DeonticStit.CounterModel | 199 | DeonticStit, Rules, Saturation, Sequent, Formula, Kripke | Not started |
| Stit | 348 | Formula, Kripke | Not started |
| Xstit | 417 | Formula, Kripke | Not started |
| Laca | 274 | Cgs, Formula | Not started |
| Cgs | 164 | — | Not started |
| Coalition | 142 | Cgs, Formula | Not started |
| Atl.Strategy | 35 | — | Not started |
| Atl.ModelCheck | 116 | Cgs, Formula | Not started |
| Atl | 47 | Atl.ModelCheck, Atl.Strategy, Cgs, Formula | Not started |
| Atel | 184 | Atl.ModelCheck, Cgs, Formula | Not started |
| Atl.ImperfectInfo | 335 | Atel, Atl.ModelCheck, Cgs, Formula | Not started |
| Dcleg | 528 | — | Not started |
| Visualize | 83 | Formula, Kripke | Superseded by `Widgets/KripkeExplorer.lean` for teaching; port only if a text/DOT export is needed |

### Protocol and executables

| Component | Lines | Lean status |
|---|---:|---|
| `protocol/Gamen/Protocol/Formula.hs` | 167 | **Done** (`Gamen/Protocol.lean`): tree and flat formats, all 30 constructors |
| `validate/Main.hs` (`gamen-validate`) | 329 | **Done for the tableau backend** (`Validate.lean`). Requests needing the doxastic/ranking rules or the deontic-STIT prover answer `"not ported in Lean slice: …"` until those modules land. |
| `protocol/Service/*` + `service/Main.hs` (dcleg service) | 893 | Not started |
| `app/Main.hs` (`gamen-repl` demo) | 43 | Not started |

### Tests

| gamen-hs test | Lines | Lean status |
|---|---:|---|
| TableauSpec | 229 | K-system cases ported (`Tests/Main.lean`) |
| Properties | 910 | NNF properties ported (Plausible); rest not started |
| ProtocolSpec, DclegServiceSpec | 565 | Covered for `gamen-validate` by the side-by-side harness (`tools/compare/`); unit specs not ported |
| FramePropertiesSpec | 356 | **Done** (`Tests/Main.lean`, `framePropertiesCases`) |
| FormulaSpec, KripkeSemanticsSpec, TemporalSpec, EpistemicSpec, StitSpec, XstitSpec, LacaSpec, DeonticStitSpec, RankingTheorySpec, PlausibilitySpec, WorldGuardsSpec | ~2,600 | Not started: port with each module |
| PaperCorrespondence | 1,848 | Not started, except the `isValidOnFrame`-exercising slice of the "Definition 1.11 (p. 11): validity in a class of models" section (6 cases, in `framePropertiesCases`); the rest of that section ("entailment") needs `entails`, not yet ported. Port the remaining sections one by one with each module; these pin the code to the papers |
| RegressionIssue18 | 481 | Not started |

## Proposed order

Each wave ends with its tests ported and `tools/compare/compare.py` green.

1. **Finish the core.** Split `Fragment` out of `Protocol.lean`; add
   `dstit`/`commitment`, the rest of `Kripke` and `Semantics`, the KT–S5
   rule sets. Port `FormulaSpec`, `KripkeSemanticsSpec`, the rest of
   `TableauSpec`. (`FrameProperties` and `FramePropertiesSpec` are done.)
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
