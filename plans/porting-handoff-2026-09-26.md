# Implementation Plan: continue the gamen-hs → Lean port (wave 4)
*Written 2026-09-26 at the close of a porting session. Read this once; implement against it.
Supersedes `plans/porting-handoff-2026-09-24.md` (kept as a dated record).*

## Objective
Port the remaining gamen-hs logics (wave 4 in `PORTING.md`), one module per
run, each with its tests and a green `tools/compare/compare.py`, and keep
the Lean port in step with upstream gamen-hs fixes as they land. A module is
done when its `PORTING.md` row says **Done**, every Haskell `it` for it has a
Lean case, the reviewers' findings are settled, and the user has approved the
merge.

## Where things stand (snapshot, 2026-09-26; verify with `git log`)
- `main` at `e05dd83`, not pushed. `lake test` 554/554, `lake exe slowtests`
  36/36 (on each merged branch; not rerun on merged `main`), compare.py
  4,731 requests: 4,717 identical, 14 equivalent, 0 scope gap, 0 DISAGREE,
  against gamen-hs `423f685`.
- Waves 1–3 done. Wave 4: **Temporal done** (`Gamen/Temporal.lean`;
  `systemKDt` moved there from `Tableau.lean` with all 8 temporal rules; the
  four core G/F tableau rules were missing and are now in `Tableau.lean`).
- Upstream fixes ported today: gamen-hs#38/#39 (countermodel extraction:
  `serialClose`, `blockerOf`, `borrowsBlockerWitnesses`) and gamen-hs#41
  (`483c463`: G3DS answers Definitely False only with a re-checked
  countermodel; new reason `uncertifiedRefutation`, wire code
  `uncertified_refutation`). The Lean-only cross-checks now hard-fail on
  every extraction error; the only exclusion left is the G3DS uncertified
  refutation whose frame fails C2 alone and whose model still falsifies φ.
- compare.py section J (G3DS on its own language, 261 requests) is new; it
  caught upstream #41 the day it landed.
- Filed today: gamen-hs#45 (the KD #39 spec case passes without borrowing;
  nothing pins the borrowing list against KTB). Lean carries both witnesses
  as "Not in gamen-hs" cases pointing at #45.
- Open upstream issues the Lean pins or mirrors: #25 (past operators never
  decomposed; e.g. `Hp → HHp` is wrongly "Definitely False" in both), #40
  (KT/KTB/S4/S5 budget exhaustion on `◇((□q ∧ □⊥) ∨ (p ∧ ⊥))`), #41 (IoaOp
  still unscheduled), #42 (KTB extraction on blocked branches).

## Decisions (do not relitigate)
- **Workflow is `/port-module <Module>`**, which only the *user* can invoke
  (`disable-model-invocation`). The coordinator asks the user to run it; it
  must not replicate the skill by hand. Porter model from `PORTING.md`'s
  Porter column. Opus `module-reviewer` always; `opus`/`fable` modules also
  get a blind parallel `module-reviewer` with `model: fable`. — Worked for
  every port so far, one review round each.
- **Upstream fixes to already-ported modules** are *not* `/port-module`
  runs: launch `module-porter` directly in a worktree with the commit hash
  and scope, then review the same way (two reviewers if a prover's soundness
  is involved). — Done this way for #38/#39 and #41.
- **Reproduce every reviewer finding before acting** (rerun the plant or
  read the cited lines); drop what doesn't reproduce. Send confirmed
  findings back to the same porter via `SendMessage`, all in one round.
- **The reviewer never sees the porter's report.**
- **Keep gamen-hs bugs faithful and file them upstream**; port the fix when
  it lands. Filing an issue needs the user's say-so; reproduce in gamen-hs
  first (use a separate `git worktree` of gamen-hs in the scratchpad so a
  concurrent porter's gamen-hs build isn't disturbed).
- **No outside models** (memory `outside-model-reviews-unavailable`).
- **Library reuse / no new dependencies:** see
  `docs/assessment/lean-library-reuse-2026-09-23.md`.
- **Rule names drop Haskell's `apply` prefix** where precedent exists.
- **New compare.py requests go at the END of `build_corpus`** (or appended
  to a section's fixed list), so earlier random draws stay unchanged.
- **Merge only when the user says so**, `--no-ff`, then `lake build` +
  `lake test` on `main`, remove the worktree, delete the branch. Don't push.

## Architecture (wave 4 order and dependencies)
One Lean module per gamen-hs module, same name (`Gamen/<M>.lean` ↔
`src/Gamen/<M>.hs`). Remaining, in dependency order (Porter column in
parentheses):

1. **Cgs** (sonnet) — no dependencies; unblocks Laca, Coalition, Atl.*.
2. **Stit** (sonnet) — Formula, Kripke. During this port, rework
   `Kripke.checkIndependence` as an early-exit search (Haskell stops early;
   Lean builds every combination), same results, plus a property test.
3. **Xstit** (opus).
4. **Epistemic** (fable) — riskiest part is `Epistemic.hs` ~148–158's
   announcement-restriction table. Decided 2026-09-28: do not mimic the
   laziness (CLAUDE.md, Laziness). Keep the Haskell names and structure,
   restrict the model when `[B]C` is reached (same results and errors as
   gamen-hs), and add a fill-on-first-use cache only if speed demands it,
   with a property test against the uncached version. Planted check: a
   build-everything-up-front version must fail a test (e.g. `p ∧ [B]C`,
   `p` false, `B` erroring). Unblocks: `WorldGuardsSpec` `eSatisfies` case,
   two Doxastic PaperCorrespondence blocks, `ArbEpistemicModel` generator.
   **Before starting:** brainstorm the remaining strategy with the user
   (`superpowers:brainstorming`): whether Epistemic reaches
   `gamen-validate` (compare.py), how unsupported operators fail, and
   whether an evaluation-state design also suits common knowledge. Agree
   on it before launching the porter.
5. **Laca** (sonnet) — Cgs, Formula; `Laca.trajectory` goes through the
   shared fuel-checked fixpoint helper. Unblocks `lSatisfies` guard test.
6. **Coalition** (sonnet), **Atl.Strategy**, **Atl.ModelCheck**, **Atl**
   (sonnet), **Atel** (sonnet), **Atl.ImperfectInfo** (opus).

Then wave 5 (Dcleg, `protocol/Service/*`, service, `app/Main.hs`).

## Interfaces / contracts
- `gamen-validate` output stays byte-identical to gamen-hs for requests in
  scope; run compare.py after touching `Protocol.lean`, `Validate/*.lean`,
  or any prover.
- Everything else: CLAUDE.md "Porting conventions" (Except not `panic!`,
  no `partial def`, fuel, `lexOrd` for pair keys, shared relation checks in
  `Kripke.lean`, one fixpoint helper).

## Constraints / process gotchas
- **Check upstream first each session:** `git -C ~/Projects/Logic/Haskell/gamen-hs log --oneline -10`.
  gamen-hs changed twice on 2026-09-26 mid-session; a moved gamen-hs shows
  up as compare.py DISAGREE that "also happens on main".
- `lake` is in `~/.elan/bin`, not on PATH: `export PATH="$HOME/.elan/bin:$PATH"`.
- Worktrees branch from `origin/main`; porter fast-forwards to local `main`
  first; review with `main...branch`.
- Use `/usr/bin/git` inside worktrees (the RTK hook rewrite trips the
  worktree safety check). Never `git stash` (shared across worktrees).
- Test with `lake test`, never the prebuilt `.lake/build/bin/tests`.
- Plants: don't plant in a worktree another agent (or a reviewer) is using;
  reviewers should plant in a `git archive` copy. A Lean `match` plant that
  adds an arm fails as "redundant alternative"; plant inside the body
  instead (e.g. `.take 0`).
- `cmd | tail` hides a failing exit status: a failed `git merge` piped to
  `tail` let `lake build` run on a conflicted tree. Don't chain merges
  through pipes.
- **Parallel branches both edit `PORTING.md` table rows** (one long line
  per module) → conflicts on every concurrent merge. Resolve with a
  word-level three-way merge (split each row on spaces, `git merge-file`
  against the merge base), then confirm each side's new phrases are present.
- `lake exe slowtests` took 15.5 min on 2026-09-26 under load (CLAUDE.md
  says ~10); run it in the background after touching Tableau, Semantics,
  RankingTheory, or the DeonticStit prover.
- Agent worktrees can stay "locked" by this Claude process after the agent
  finishes; if the branch is merged and `git status` is clean, `git worktree
  unlock` then remove.
- Commit trailer: `Co-Authored-By: Claude Opus 5.5 (1M context) <noreply@anthropic.com>`.

## Non-goals / rejected alternatives
- `mmreview`/Codex/Gemini — not available here.
- Mathlib/Batteries/Foundation dependencies — rejected for now.
- Union-find `equivalenceClasses`, SAT-solver `isTautology` — output order
  and executability must match gamen-hs.
- Porting `Visualize` — superseded by `Widgets/KripkeExplorer.lean`.

## Open questions for the implementer (raise with the user; don't act unasked)
- [ ] `~/Projects/Logic/CLAUDE.md` Publication Plan still says JOSE =
      "Gamen.jl + Pluto notebooks"; the user decides whether the Lean
      notebooks replace them.
- [ ] Re-time `lake exe slowtests` on an idle machine; update CLAUDE.md's
      "~10 min" if it's really longer (7 extraction properties were added).
- [ ] When gamen-hs#45 lands, drop "Not in gamen-hs" from the two witness
      cases; when #42 lands, flip the KTB `◇□□¬p` pin.
- [ ] Optional: runtime string → `Formula` parser (Gamen.jl#19), only when
      a widget or the web editor needs it.

## Task list (ordered)
1. Check gamen-hs for new commits; port any fixes to ported modules first
   (direct `module-porter`, see Decisions).
2. Ask the user to run `/port-module Cgs`; review, settle, report, merge on
   approval.
3. `/port-module Stit` (include the `checkIndependence` early-exit rework).
4. `/port-module Xstit`.
5. Brainstorm the Epistemic porting strategy with the user first, then
   `/port-module Epistemic` (restrict on demand, no lazy memo; then port the unblocked
   WorldGuards/Doxastic tests and `ArbEpistemicModel`).
6. `/port-module Laca`, then Coalition, Atl.Strategy, Atl.ModelCheck, Atl,
   Atel, Atl.ImperfectInfo.
7. After each merge: `lake test`, compare.py; slowtests when a prover was
   touched. Update this plan's "Where things stand" if it drifts far.

## Suggested implementer model
Coordinator: Opus (it settles reviewer disputes and plants checks; Lean fails
loudly at compile time but semantic drift from gamen-hs is silent, caught
only by compare.py and planted checks). Porters: the Porter column
(sonnet for Cgs/Stit/Laca/Coalition/Atl/Atel, opus for Xstit and
Atl.ImperfectInfo, fable for Epistemic).
