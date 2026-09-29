# Implementation Plan: continue the gamen-hs → Lean port (wave 4, second half)
*Written 2026-09-28 at the close of a porting session. Read this once; implement against it.
Supersedes `plans/porting-handoff-2026-09-26.md` (kept as a dated record; its
Epistemic strategy notes are now history).*

## Objective
Port the remaining gamen-hs logics (the ATL/game-structure chain, then wave
5), one module per run, each with its tests, and keep the Lean port in step
with upstream gamen-hs fixes. A module is done when its `PORTING.md` row
says **Done**, every Haskell `it` that exercises it (found by export search,
see Decisions) has a Lean case, the reviewers' findings are settled, and the
user has approved the merge.

## Where things stand (snapshot, 2026-09-28; verify with `git log`)
- `main` at `1848468` plus this plan's commit, **pushed** to `origin`.
  `lake test` 730/730 on `main`. `lake exe slowtests` 36/36 (on the Stit
  branch, the last one to touch a prover-adjacent module: `Kripke`).
  compare.py: 4,731 requests, 4,717 identical, 14 equivalent, 0 scope gap,
  0 DISAGREE (the "14" is the *equivalent* column; one porter misread it as
  disagreements).
- Wave 4 done this session, each via `/port-module`, one review round or
  none:
  - **Cgs** (sonnet): 19 cases; gamen-hs has no CgsSpec. One round (a false
    "gamen-hs never tests `mkCgs`'s error branches" claim; RegressionIssue18
    B7 does).
  - **Stit** (sonnet): 43 cases, plus `Kripke.checkIndependence` reworked as
    an early-exit search with a property test against the old version. No
    fixes needed.
  - **Xstit** (opus, two reviewers): 56 cases; Broersen citations corrected
    (filed as gamen-hs#46). No fixes needed.
  - **Epistemic** (fable, two reviewers): 53 cases plus 5 "Not in gamen-hs"
    cases. No lazy table: restrict on demand (CLAUDE.md, Laziness). One
    round: a multi-step common-knowledge case and a BFS-agreement property
    (the closure was untested past one step, in gamen-hs too: #48). **After
    merge**, RegressionIssue18's "B8: Epistemic common knowledge and
    bisimulation" (4 `it`s) turned out to be missed by the porter and both
    reviewers; ported in `2ddf63a` with one extra case, since B8's fixture
    never needs a `largestBisimulation` refinement round.
- Filed this session on gamen-hs: #46 (Xstit Broersen citations), #47
  (Epistemic cites B&D Fall 2019 Ch. 13), #48 (no multi-step
  common-knowledge test), #49 (stale B&D citations in Semantics,
  FrameProperties, Tableau). **PR #50** (branch `docs/pin-bd-edition`, open):
  adds `notes/bd-edition.md`, pinning the B&D edition. gamen-lean's
  CLAUDE.md already points to that file; it won't exist in the local
  gamen-hs checkout until #50 merges.
- gamen-hs local checkout is on `fix/41-certified-refutation` at `423f685`
  (compare.py builds against that). `origin/main` is at `f27399d`. A second
  gamen-hs worktree, `~/Projects/Logic/Haskell/gamen-hs-bd-edition`, holds
  the PR #50 branch; remove it once #50 merges.
- Still open upstream from before: #25, #40, #41 (IoaOp), #42, #45.

## Decisions (do not relitigate)
- **Workflow is `/port-module <Module>`**, which only the *user* can invoke.
  Porter model from `PORTING.md`'s Porter column. Opus `module-reviewer`
  always; `opus`/`fable` modules also get a blind parallel reviewer with
  `model: fable`. Every port this session needed at most one review round.
- **Each reviewer gets its own detached checkout** of the porter's branch
  (`.claude/worktrees/review-<module>-<model>`, with the porter's `.lake`
  copied in), never the porter's worktree. Two reviewers sharing one saw
  each other's planted bugs (Xstit). Now in the `/port-module` skill.
- **Find a module's tests by export search, not by section name.**
  `for f in <exports>; do grep -lw "$f" test/*.hs; done` over gamen-hs's
  `test/`. Shared files (`RegressionIssue18.hs`, `WorldGuardsSpec.hs`,
  `Properties.hs`) test many modules under unrelated headings; that is how
  B8 slipped past three agents. Now in both agent files; the coordinator
  should run the same search before reporting a port as complete.
- **Laziness: match outputs and errors, not evaluation order** (CLAUDE.md).
- **B&D citations mean the pinned edition** (Fall 2025; revisions and
  SHA-256 in `gamen-hs/notes/bd-edition.md`, via PR #50). Check the PDF's
  hash before checking citations; name any other edition explicitly.
- **Upstream fixes to already-ported modules** are direct `module-porter`
  runs with the commit hash and scope, reviewed the same way.
- **Reproduce every reviewer finding before acting**; send confirmed ones
  back to the same porter in one round. **The reviewer never sees the
  porter's report.**
- **Keep gamen-hs bugs faithful and file them upstream**, with the user's
  say-so. Citation errors are fixed in Lean *and* filed (#46, #47, #49).
- **No outside models** (memory `outside-model-reviews-unavailable`).
- **Library reuse / no new dependencies:** see
  `docs/assessment/lean-library-reuse-2026-09-23.md`.
- **New compare.py requests go at the END of `build_corpus`.**
- **Merge only when the user says so**, `--no-ff`, then `lake build` +
  `lake test` on `main`, remove the worktrees (porter's and reviewers'),
  delete the branch. **Push only when asked** (the user asked after every
  merge this session).

## Architecture (remaining order and dependencies)
One Lean module per gamen-hs module, same name. Remaining, in dependency
order (Porter column in parentheses):

1. **Laca** (sonnet) — Cgs, Formula; `Laca.trajectory` goes through the
   shared fuel-checked fixpoint helper. Unblocks the `lSatisfies` guard test
   and PaperCorrespondence's LACA block (its `lacaToCgs` sub-block also
   needs Atl).
2. **Coalition** (sonnet) — Cgs, Formula. Unblocks Pauly (2002) block.
3. **Atl.Strategy** (sonnet) — no dependencies.
4. **Atl.ModelCheck** (sonnet) — Cgs, Formula.
5. **Atl** (sonnet) — Atl.ModelCheck, Atl.Strategy, Cgs, Formula. Unblocks
   the AHK (2002) block and the rest of LACA's.
6. **Atel** (sonnet) — Atl.ModelCheck, Cgs, Formula.
7. **Atl.ImperfectInfo** (opus) — Atel, Atl.ModelCheck, Cgs, Formula.

Laca, Coalition, Atl.Strategy and Atl.ModelCheck are mutually independent;
they could run in parallel, at the cost of `PORTING.md` merge conflicts (see
gotchas). One at a time has been the norm.

Then wave 5: Dcleg (opus), `protocol/Service/*`, the dcleg service,
`app/Main.hs`.

## Interfaces / contracts
- `gamen-validate` output stays byte-identical to gamen-hs for requests in
  scope; run compare.py after touching `Protocol.lean`, `Validate/*.lean`,
  or any prover. Cgs, Stit, Xstit and Epistemic are not reachable from
  `gamen-validate`; check each new module's reachability (grep gamen-hs's
  `validate/Main.hs` imports) before relying on compare.py.
- Everything else: CLAUDE.md "Porting conventions".

## Constraints / process gotchas
- **Check upstream first each session:** `git -C ~/Projects/Logic/Haskell/gamen-hs log --oneline -10`,
  and check whether PR #50 has merged.
- `lake` is in `~/.elan/bin`, not on PATH. The RTK hook can't find it via
  `rtk proxy`; call `~/.elan/bin/lake` directly.
- RTK rewrites `grep` output into a summarized form that can hide lines;
  for exact matching over long lines (e.g. `PORTING.md` rows) use Python.
- Worktrees branch from `origin/main`; porter fast-forwards to local `main`
  first; review with `main...branch`.
- Never `git stash` (shared across worktrees).
- Test with `lake test`, never the prebuilt `.lake/build/bin/tests`.
- Plants: back up the file to the scratchpad, plant with `sed`, confirm
  `git diff --stat` shows the change, run, restore from the backup. A plant
  that isn't caught may mean the fixture is too weak, not that the plant
  missed: check (Cgs `preC`, Epistemic `largestBisimulation`).
- `cmd | tail` hides a failing exit status; don't chain merges through
  pipes.
- **Parallel branches both edit `PORTING.md` table rows** → conflicts;
  resolve with a word-level three-way merge.
- `lake exe slowtests` ~15 min under load; run it in the background after
  touching Tableau, Semantics, RankingTheory, Kripke, or the DeonticStit
  prover.
- Commit trailer: `Co-Authored-By: Claude Opus 5.5 (1M context) <noreply@anthropic.com>`.

## Non-goals / rejected alternatives
- `mmreview`/Codex/Gemini — not available here.
- Mathlib/Batteries/Foundation dependencies — rejected for now.
- Mimicking Haskell laziness (explicit lazy memos) — rejected 2026-09-28.
- Committing the B&D PDF — rejected: cover art is CC BY-NC; the hash pin
  suffices.
- Porting `Visualize` — superseded by `Widgets/KripkeExplorer.lean`.

## Open questions for the implementer (raise with the user; don't act unasked)
- [ ] When PR #50 merges, remove `~/Projects/Logic/Haskell/gamen-hs-bd-edition`.
- [ ] When #46/#47/#49 land upstream, check the Lean citations still agree.
- [ ] When gamen-hs#45 lands, drop "Not in gamen-hs" from the two witness
      cases; when #42 lands, flip the KTB `◇□□¬p` pin.
- [ ] The B&D audit checked only that each cited number exists in the
      pinned edition, not that it's the right definition for the claim.
- [ ] `~/Projects/Logic/CLAUDE.md` Publication Plan still says JOSE =
      "Gamen.jl + Pluto notebooks"; the user decides whether the Lean
      notebooks replace them.
- [ ] Re-time `lake exe slowtests` on an idle machine.

## Task list (ordered)
1. Check gamen-hs for new commits and PR #50's status; port any fixes to
   ported modules first (direct `module-porter`).
2. `/port-module Laca`.
3. `/port-module Coalition`, `Atl.Strategy`, `Atl.ModelCheck`, `Atl`,
   `Atel`, `Atl.ImperfectInfo`, in that order.
4. For each: before reporting, run the export search over gamen-hs's
   `test/` yourself and confirm every hit is ported or listed as skipped.
5. After each merge: `lake test`; compare.py if the module or anything it
   touched is reachable from `gamen-validate`; slowtests when a prover or
   `Kripke` was touched. Update this plan's "Where things stand" if it
   drifts far.
6. Then plan wave 5 (Dcleg and the service) with the user.

## Suggested implementer model
Coordinator: Opus. Porters: the Porter column (sonnet for Laca, Coalition,
Atl.*, Atel; opus for Atl.ImperfectInfo and Dcleg). This session's ports
needed zero or one review round each, so the column looks right.
