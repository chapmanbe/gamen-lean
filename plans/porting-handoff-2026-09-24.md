# Implementation Plan: continue the gamen-hs → Lean port (wave 2 onward)
*Written 2026-09-24 at the close of a porting/design session. Read this once; continue against it.*

## Objective
Keep porting gamen-hs modules to Lean in `PORTING.md` order, one module per
`/port-module` run, merged only on the user's word. **Waves 1 and 2 are
done. Next: wave 3, deontic STIT, starting with `Sequent`** . A module is done when its tests are ported, `lake test`
is green on `main`, and `tools/compare/compare.py` shows 0 DISAGREE.

## Where things stand (as of `1335727`, updated 2026-09-24)
- **Wave 1 done:** Formula, Kripke, Semantics, Fragment, FrameProperties,
  Tableau (K, KT, KD, KTB, K4, S4, S5).
- **Wave 2 done:** Doxastic and RankingTheory ported and wired;
  Plausibility ported, not wired (gamen-hs's `validate/Main.hs` never
  imports it).
- `lake test`: 321/321. compare.py: 4,470 requests, 4,430 identical, 14
  equivalent, 26 scope_gap, **0 DISAGREE**. The 26 scope gaps are all
  deontic-STIT; wave 3 should clear them.
- `main` is pushed to `origin`. Push only when the user asks.

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

## Wave 3: specifics for the next run
- Order: `Sequent` → `Rules` → `Saturation` → `Prove` → `CounterModel`, with
  `DeonticStitSpec`. Check each module's Porter column (`Saturation` is
  `fable`).
- `CounterModel` also depends on the base `DeonticStit` module (277 lines,
  `sonnet`, not started), which the wave 3 order in `PORTING.md` omits.
  Port it before `CounterModel`; it needs only Formula and Kripke.
- The saturation loop needs fuel (gamen-hs's step budget), returning
  `Except` on exhaustion, via the shared fixpoint helper where it fits.
- After `Prove` lands, wire it into `Validate/Core.lean`, remove the
  deontic-STIT scope gate, and do the plant-out check; the 26 scope gaps
  should go to 0.

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
1. ~~RankingTheory~~ (`a9d735d`), ~~Plausibility~~ (`1335727`); wave 2 done.
2. `/port-module Sequent`, then Rules, Saturation, Prove, CounterModel.
3. Wire the deontic-STIT prover into `gamen-validate`; compare.py to 0
   scope gaps.

## Suggested implementer model
Coordinator session: **Opus**. It reviews, reproduces findings, and edits the
wire-contract code in `Validate/Core.lean` and `compare.py`. Porters follow
the Porter column (Sonnet for routine modules, Opus for RankingTheory, Fable
for Epistemic and DeonticStit.Saturation).
