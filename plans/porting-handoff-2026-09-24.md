# Implementation Plan: continue the gamen-hs → Lean port (wave 2 onward)
*Written 2026-09-24 at the close of a porting/design session. Read this once; continue against it.*

## Objective
Keep porting gamen-hs modules to Lean in `PORTING.md` order, one module per
`/port-module` run, merged only on the user's word. **Waves 1–3 are
done. Next: property tests (Properties.hs generators), then wave 4** . A module is done when its tests are ported, `lake test`
is green on `main`, and `tools/compare/compare.py` shows 0 DISAGREE.

## Where things stand (updated 2026-09-25, after wave 3)
- **Waves 1–3 done.** All of `DeonticStit` (base, Sequent, Rules,
  Saturation, Prove, CounterModel) is ported; Prove is wired into
  `gamen-validate`, which is complete.
- `lake test`: 455/455. compare.py: 4,470 requests, 4,456 identical, 14
  equivalent, **0 scope_gap, 0 DISAGREE**.
- Shared fixpoint helper `iterateToFixpoint` now exists (`Kripke.lean`);
  `DeonticStit.euclideanClose` and `Tableau.transitiveClose` use it.
  Remaining unbounded loops to route through it as their modules land:
  `lfp`, `gfp`, `largestBisimulation`, `Laca.trajectory`.
- `Semantics.satisfies` and `DeonticStit.dsSatisfies` now short-circuit
  `And`/`Or`/`Implies` like Haskell's lazy `&&`/`||` (found in review; any
  future `satisfies`-style evaluator must do the same).
- Upstream issues filed: gamen-hs#35, #36, #37.
- Push only when the user asks.

## Decisions (do not relitigate)
- **The workflow is `/port-module <Module>`** (`.claude/skills/port-module/`).
  The porter model comes from `PORTING.md`'s Porter column. Every port gets
  an Opus `module-reviewer`; `opus`/`fable` modules also get a second
  `module-reviewer` with `model: fable`, in parallel and blind to the first.
  — Four Sonnet ports each needed exactly one review round. That process
  works.
- **The coordinator reproduces every reviewer finding before acting on it**,
  and drops the ones it can't reproduce. — Both reviewers and the
  coordinator have each been wrong at least once (string-matched test names,
  a sed plant that didn't apply).
- **The reviewer never sees the porter's report.** — Sonnet porters
  over-reported their work twice, while their code was correct.
- **No outside models.** `mmreview` can't run here (see memory
  `outside-model-reviews-unavailable`). Don't retry Codex, Gemini, or
  Antigravity without asking the user; check UTSW policy first.
- **Keep bugs faithful, file them upstream.** A gamen-hs bug is filed on
  gamen-hs and copied into Lean until it's fixed there, then the fix is
  ported (precedent: #31 → `12828e5`). The user decides; file issues only
  when asked.
- **Library reuse:** see `docs/assessment/lean-library-reuse-2026-09-23.md`
  and the conventions it added to `CLAUDE.md` (shared relation checks in
  `Kripke.lean`, one fixpoint helper with fuel). Add no dependencies.
- **Rule names drop Haskell's `apply` prefix** (`tBoxRule`), following
  existing precedent; `apply4BoxRule` can't keep its digit-led name anyway.
  Leave it.
- **New compare.py sections go at the END of `build_corpus`**, so earlier
  sections' random draws, and so the baseline, stay unchanged.

## RankingTheory: done (record)
- Opus porter, one review round (Opus + Fable). Porter also did the
  `Validate/Core.lean` wiring and compare.py **section I** (409 ranked-belief
  requests). Planting the ranking rules out gave 49 DISAGREE, all in
  section I: ranked belief in the older random sections never reaches these
  rules, so section I is the only coverage.
- Review fix: `applyEvidence` returns the model unchanged when the agent's
  κ-table is empty (Haskell never forces τ there). Only the Opus reviewer
  caught it.
- Not ported: the two ranking `prop`s in `Properties.hs` (need a random
  `KappaModel` generator); recorded in `PORTING.md`.
- Spohn "additional reason … strengthened" is p. 118, not 117: fixed in
  Lean, filed upstream as gamen-hs#35 (open).
- κ = ∞ kept as gamen-hs's 64-bit sentinels (`rankMaxBound`/`rankMinBound`);
  Lean `Int` is unbounded, so `combineIndependent` doesn't wrap near them
  (documented, out of wire scope).

## Plausibility: done (record)
- Sonnet porter, one review round (Opus). Review fix: three
  iterated-conditioning tests used `Option.bind`, so they passed when
  `conditionOn` always returned `none` (Haskell's `fromJust` crashes). They
  now fail on `none`; planting `conditionOn := none` fails 18 cases.
- Watch for this pattern in later ports: a Haskell `fromJust`/partial match
  ported as `Option` comparison can make `none == none` pass.
- `Data.Map.Strict` forces values at construction: check the import before
  calling any Haskell evaluation "lazy".

## Wave 3: record
- Porter ratings held: Sonnet modules needed one review round; the two
  `opus` modules Rules and CounterModel needed none, Prove one; `fable`
  Saturation one (doc-only). Consider `sonnet` for similar `opus` modules
  if a third passes clean.
- G3DS wiring plants: "always consistent" → 8 DISAGREE; "D2 dropped" → 15.
  Only 26 corpus requests reach G3DS (optional compare.py section, task 3).
- Lean-only reply `"prover error: …"` is unreachable via Prove.
- Review lessons: porters invent or mis-page paper citations (now forbidden
  in `module-porter.md`); a porter's own plant found the `applyOughtB` gap
  both reviewers missed; `(← a) && (← b)` in `do` is strict (both sides run).
- Coordinator gotchas: never revert a plant with `git checkout <file>` when
  the file holds uncommitted work; copy a clean file aside and restore it.
  The RTK `diff` wrapper once misreported differing files as identical; use
  `/usr/bin/diff`.

## Process gotchas (already in the agent files; watch the coordinator side too)
- Worktrees branch from `origin/main`. The porter fast-forwards to local
  `main` first. Review with a three-dot diff (`main...branch`).
- Use `/usr/bin/git` in worktrees: the RTK hook rewrites plain `git`, and the
  worktree safety check blocks the rewrite.
- Never use `git stash`: it's shared across worktrees.
- Test with `lake test`, never the prebuilt `.lake/build/bin/tests`, which
  can be stale.
- Before planting in a worktree, check that no background `compare.py` or
  `lake` is running (`pgrep -f compare.py`). A full compare run takes
  several minutes; run long checks in the background.
- `lake`/`lean` live in `~/.elan/bin`, which is not on the shell PATH:
  `export PATH="$HOME/.elan/bin:$PATH"`.
- The gamen-hs binary: `cd ~/Projects/Logic/Haskell/gamen-hs && cabal list-bin exe:gamen-validate`.
  GHCi for spot checks: `cabal repl gamen:lib:gamen`, with `:m + *Gamen.X`
  for unexported functions.
- Commit trailer: `Co-Authored-By: Claude Opus 5.5 (1M context) <noreply@anthropic.com>`.

## Non-goals / rejected alternatives
- `mmreview`/Codex/Gemini: not available (see above).
- Mathlib, Batteries, Foundation as dependencies: rejected for now. Proofs
  would later go in a separate Lake package.
- A union-find `equivalenceClasses` or a SAT-solver `isTautology`: rejected,
  because output order and executability must match gamen-hs.

## Open questions / loose ends (raise with the user; don't act unasked)
- [x] (done 2026-09-24, waves 1–2 rewritten) `PORTING.md` wave 1 entry reads awkwardly after several porters edited
      it; offer a clean rewrite.
- [ ] gamen-hs#33 (weak prefix test) is **closed** upstream. The Lean test
      comment "Not in gamen-hs: its collision test above…" in `Tests/Main.lean`
      (B5 block) may now be stale; check what gamen-hs changed and update the
      comment or port the new test.
- [ ] `Kripke.checkIndependence` builds every combination eagerly, where
      Haskell stops early. Rework it as an early-exit search, with the same
      results and a property test, during the **Stit** port.
- [ ] `~/Projects/Logic/CLAUDE.md` Publication Plan still says JOSE =
      "Gamen.jl + Pluto notebooks". The user must decide whether the Lean
      notebooks replace them. `gamen-roc` is not listed there either.
- [ ] Wave 3 (DeonticStit) and Epistemic are the riskiest modules
      (saturation loop fuel; the explicit lazy memo, `Epistemic.hs` ~148–158).

## Task list (ordered)
1. Port `test/Properties.hs`'s model generators (`ArbModel`, and
   `ArbKappaModel` now that RankingTheory is ported; `ArbEpistemicModel`
   waits for Epistemic) and its tableau-vs-Kripke-semantics properties
   (K, KT, K4) to Plausible. Unblocks the two deferred RankingTheory
   properties. Not a `/port-module` module: run a porter in a worktree,
   Opus review.
2. **Done 2026-09-25; #38/#39 fixed upstream 2026-09-26.** Lean-only,
   prompted by Gamen.jl#20: every tableau system cross-checked against
   frame enumeration (≤3 worlds up to isomorphism; ≤4 for KT/KTB/S4/S5 in
   slowtests; 4 worlds × 3 atoms for K is out of reach), with extracted
   countermodels re-checked for all seven systems, and G3DS the same way.
   Seeded draws. It found gamen-hs#38 (KD countermodels not serial),
   gamen-hs#39 (K/KD/K4 extraction fails at blocked prefixes), gamen-hs#40
   (KT/KTB/S4/S5 exhaust the budget on `◇((□q ∧ □⊥) ∨ (p ∧ ⊥))`, same in
   gamen-hs, still pinned), and gamen-hs#41 (documented G3DS IoaOp/C2
   deferral, still the only G3DS extraction exclusion). #38 and #39 were
   fixed upstream in gamen-hs `08a52d4` (`serialClose`,
   `blockerOf`/`borrowsBlockerWitnesses`) and ported into
   `Gamen/Tableau.lean`; `crossExtractOne`'s exclusions for both are
   dropped and the three regression pins that used to check the bug
   (`Tests/Main.lean`'s `crossCheckCases`) now check the fixed behavior.
   KTB and S5 do not borrow (by design), so their blocked branches can
   still fail extraction; tracked separately as gamen-hs#42, open. Known
   failures are KTB-only (e.g. `◇□□¬p`); none found for S5. Our random
   samples have not hit one, so `crossExtractOne` still treats any KTB or
   S5 failure as a hard error rather than excusing it; `crossCheckCases`
   pins the #42 example. Still open: offer to file the
   stronger check on gamen-hs (ask first).
3. Optional: a compare.py G3DS section (coverage is 26 requests).
4. Deferred (Gamen.jl#19): runtime string → `Formula` parser, when a widget
   or the web editor needs it; extend `ml[…]` as operators land.
5. Wave 4: Temporal, Epistemic (`fable`, explicit lazy memo), Stit,
   Xstit, Cgs, Laca, Coalition, Atl.*, Atel.

## Suggested implementer model
Coordinator session: **Opus**. It reviews, reproduces findings, and edits the
wire-contract code in `Validate/Core.lean` and `compare.py`. Porters follow
the Porter column (Sonnet for routine modules, Opus for RankingTheory, Fable
for Epistemic and DeonticStit.Saturation).
