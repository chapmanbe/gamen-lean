# Implementation Plan: continue the gamen-hs → Lean port (wave 2 onward)
*Written 2026-09-24 at the close of a porting/design session. Read this once; continue against it.*

## Objective
Keep porting gamen-hs modules to Lean in `PORTING.md` order, one module per
`/port-module` run, merged only on the user's word. **Waves 1 and 2 are
done; wave 3 is down to the base `DeonticStit` module and `CounterModel`** . A module is done when its tests are ported, `lake test`
is green on `main`, and `tools/compare/compare.py` shows 0 DISAGREE.

## Where things stand (updated 2026-09-24, after wiring G3DS)
- **Waves 1–2 done.** Wave 3: `DeonticStit.Sequent`, `.Rules`,
  `.Saturation`, `.Prove` done; Prove is wired into `gamen-validate`,
  which is now complete.
- `lake test`: 419/419. compare.py: 4,470 requests, 4,456 identical, 14
  equivalent, **0 scope_gap, 0 DISAGREE**.
- Upstream issues filed this session: gamen-hs#35 (Spohn page), #36
  (`applyD2` "Note 4"), #37 (Prove page citations + untested `applyOughtB`
  ideal check). Lean already has the fixes and a "Not in gamen-hs" test.
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

## Wave 3: specifics for the next run
- Next: the base `DeonticStit` module (277 lines, `sonnet`, needs only
  Formula and Kripke; the `PORTING.md` order omitted it), then
  `DeonticStit.CounterModel` (`opus`). CounterModel unblocks
  PaperCorrespondence's L&vB "Definition 20" block (3 cases), skipped in
  the Prove port.
- G3DS wiring record: plant "always consistent" → 8 DISAGREE (section D);
  plant "D2 rule dropped" → 15 (sections C, D). Only 26 corpus requests
  reach G3DS, so a dedicated compare.py section (at the END of
  `build_corpus`) would strengthen coverage; not done yet.
- Lean-only reply `"prover error: …"` (from `ancestors` fuel) is
  unreachable via Prove; documented in `Validate/Core.lean`.
- Lessons from wave 3 reviews: porters invent or mis-page paper citations
  (now forbidden in `module-porter.md`); a porter's own plant found the
  `applyOughtB` gap both reviewers missed, so keep asking porters for
  per-rule plants.
- Coordinator gotcha: never revert a plant with `git checkout <file>` when
  that file also holds uncommitted work; copy a clean file aside and
  restore it. The RTK `diff` wrapper once misreported two differing files
  as identical; use `/usr/bin/diff`.

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
1. `/port-module DeonticStit` (base module).
2. `/port-module DeonticStit.CounterModel`; port the L&vB Definition 20
   block with it.
3. Optional: a compare.py G3DS section to raise coverage above 26 requests.
4. Wave 4: Temporal, Epistemic (`fable`, explicit lazy memo), Stit,
   Xstit, Cgs, Laca, Coalition, Atl.*, Atel.

## Suggested implementer model
Coordinator session: **Opus**. It reviews, reproduces findings, and edits the
wire-contract code in `Validate/Core.lean` and `compare.py`. Porters follow
the Porter column (Sonnet for routine modules, Opus for RankingTheory, Fable
for Epistemic and DeonticStit.Saturation).
