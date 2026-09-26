# Where the bugs came from: one porting session (2026-09-24 to 2026-09-26)

A dated record, written at the user's request after they asked whether the
multi-language setup (Gamen.jl, gamen-hs, gamen-lean) finds different bugs
because each language exposes different misconceptions, or because the models
doing the work have improved. The session covered wave 2 (RankingTheory,
Plausibility), wave 3 (all of `DeonticStit`), wiring G3DS into
`gamen-validate`, the `test/Properties.hs` port, and a Lean-only cross-check
against independent semantics (prompted by Gamen.jl#20). Commits run from
`881cf63` to `8af16b2`, and gamen-hs issues from #35 to #41.

## Findings, by what exposed them

"Found by" names the step that surfaced the finding, not who fixed it.

### 1. Lean forced a decision Haskell left implicit

| Finding | Found by | Record |
|---|---|---|
| `Tableau.transitiveClose` returned a partly closed relation when its fuel ran out (merged in wave 1) | CounterModel porter; confirmed by both reviewers and the coordinator | `ac73c49` |
| `ancestors` diverges on a cyclic parent map in Haskell; Lean needs fuel and `Except` | Saturation porter | `b7b7595` |
| `applyEvidence` on an empty κ-table: Haskell never forces τ (lazy), Lean threw | Opus reviewer (Fable reviewer missed it) | `9afdfa2` |
| "Deferred error in an unforced thunk" was wrong: `Data.Map.Strict` forces values | Opus reviewer | `21c77a4` |

These come from totality and the lack of exceptions in pure code: every
"iterate until nothing changes" and every "this error is never reached"
became an explicit claim with a bound or an `Except`.

### 2. Bugs the port introduced, caught by review or planted checks

| Finding | Found by | Record |
|---|---|---|
| `(← a) && (← b)` in `do` runs both sides, unlike Haskell's lazy `&&`/`||`; also present in `Semantics.lean` since wave 1 | Opus reviewer, confirmed in GHCi | `8c72cbc`, `68b6240` |
| Iterated-conditioning tests compared `Option`s, so `none == none` passed where Haskell's `fromJust` would crash | Opus reviewer's plant | `21c77a4`; reviewer check added in `f405e23` |
| An NNF test compared two `Except`s, so `error == error` passed | Opus reviewer's plant | `fb8b54f` |
| Plausible's `gaveUp` counted as a pass; guard-false draws counted as passes (Haskell's `==>` discards them), so 3 to 10 times fewer real checks | Opus reviewer | `ea8df19` |
| Helper checks collapsed an error to `false`, so ranking properties passed with nothing tested | Properties porter's own plant | `ea8df19` |
| An invented journal, title, and page range for Lyon & van Berkel 2024 | Opus reviewer, checked against the PDF | `2cea97d`; porter rule added in `eb7985c` |
| Wrong page numbers the porter added (Saturation) | Both reviewers | `4cd1faa` |

These come from mismatches between Lean and Haskell semantics (strict `do`,
`Option` or `Except` in place of a crash, Plausible in place of QuickCheck),
plus one model confabulation.

### 3. Mechanical discipline that would work in any language

| Finding | Found by | Record |
|---|---|---|
| Spohn quote on p. 118, not p. 117 | Porter, `pdftotext` | gamen-hs#35 |
| `applyD2` cites "Note 4 of Definition 14"; it is the (D2_i) bullet | Porter, `pdftotext` | gamen-hs#36 |
| Prove citations (Definition 3, Algorithm 1, §4.1 pages) | Porter, `pdftotext` | gamen-hs#37 |
| `applyOughtB`'s ideal-world check untested in both gamen-hs and Lean | Prove porter's own plant; **both reviewers missed it** | `a61c0c9`, gamen-hs#37 |
| World-existence guard in `dsSatisfies` untested | Opus reviewer's plant | `487db12` |
| RegressionIssue18 B6 tableau tests never ported in wave 1 | Opus reviewer (CounterModel review) | `ac73c49` |
| The paper itself misprints (C_⊗_i) with ⊖ | Saturation porter, `pdftotext` | noted in `Saturation.lean` |

### 4. An independent oracle, the semantics (bugs in the algorithm itself)

| Finding | Found by | Record |
|---|---|---|
| KD countermodels are not serial: the D rules never fire at modal-free prefixes | Cross-check (frame-class check on extracted models) | gamen-hs#38 |
| Extraction fails on branches left open by blocking: no edge back to the blocker (K, KD, K4) | Cross-check | gamen-hs#39 |
| `tableauProves` exhausts its budget in KT, KTB, S4, S5 on a small formula | Cross-check | gamen-hs#40 |
| About 20% of two-agent G3DS refutations have frames that fail only C2; IoaOp is unscheduled and tracked only in code comments | Cross-check | gamen-hs#41 |
| Random formulas rarely hit schema-shaped cases, so an unsound extra rule in KT passed `lake test` | Opus reviewer's plant, on the cross-check itself | `8af16b2` |

None of these is a wrong verdict. Across all seven systems the tableau's
answers agreed with enumeration up to three worlds. They are gaps in the
design of countermodel extraction and scheduling, present in gamen-hs and
copied into Lean by the faithful-port rule.

## Observations

1. **Translation friction finds one class of bug: unexamined assumptions.**
   Section 1 shows what Lean adds: a claim that a loop terminates or an
   error is unreachable has to be written down, and it can then be checked.
   These findings are specific to the language pair.

2. **A faithful port finds almost none of the algorithm's bugs, by design.**
   We copy gamen-hs's bugs on purpose, and `compare.py` reports only
   differences. Two implementations of one algorithm share its
   misconceptions, a known weakness of redundant independent
   implementations. The Section 4 findings appeared only when outputs were
   checked against the semantics, which no prover depends on. The idea for
   that check came from the Julia side (Gamen.jl#20). The cross-language
   benefit was an oracle, not the code.

3. **Mechanical checks beat judgment, including the models'.** Planted bugs,
   `pdftotext`, `compare.py`, and enumeration produced most findings.
   Several cases show a mechanical step finding what model judgment missed:
   - both reviewers missed the `applyOughtB` gap that a plant found;
   - one reviewer missed the empty-table case that the other caught;
   - a porter invented a citation and claimed to have checked it;
   - the coordinator nearly lost uncommitted work reverting a plant with
     `git checkout`, and trusted a wrapped `diff` that misreported two
     differing files as identical.

   The models' contribution was running this discipline thoroughly and at
   scale, not replacing it.

4. **Model capability versus process: not separable from this record.** The
   process tightened during the session:
   - new reviewer and porter rules (`f405e23`, `eb7985c`);
   - the three-way oracle;
   - independent reproduction of every finding.

   The models ran the whole session. There is no control run, so "the models
   improved" and "the checks improved" are confounded. What the record does
   show: many confirmed findings came with a planted-bug or GHCi
   reproduction, and every finding was independently reproduced by the
   coordinator before it was acted on.

## Limits of this record

One session, one coordinator, and porter and reviewer models from one
vendor. Coordinator errors are included where they happened, but the
coordinator also wrote this record. Counts come from session reports and
commit messages, not a separate audit. The unported modules (Temporal,
Epistemic, Stit, Xstit, Laca, Cgs, ATL, Dcleg) may show a different mix.
