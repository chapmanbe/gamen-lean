# Implementation Plan: continue gamen-lean (session handoff)
*Written 2026-10-06 at the close of a session that merged the DCLEG proofs,
prepared the guideline-validation and cwyde migration patches, and ported
`dcleg-service`. Read this once; it indexes the detailed plans, which you read
only for the thread you pick up. Supersedes `plans/session-handoff-2026-10-01.md`
for **state and the task list**. That file's Decisions, Interfaces, Constraints
and Non-goals sections are still in force and are not repeated here; read them
if you need them. Everything else in it is history.*

## Objective

Pick up **one** open thread below, implement it against its own plan, and get
Brian's approval before merging. Done for a thread means:
- its plan's "Done when" is met;
- it was reviewed independently (a blind reviewer, planted checks);
- `lake build` and `lake test` pass on `main`;
- Brian approved the merge.

## Where things stand (2026-10-06; verify with `git log`)

**gamen-lean:** `main` is at the commit that adds this file, pushed.
`lake test` passes 1303/1303. Every gamen-hs library module is ported, and now
the dcleg service too. Not ported: the `gamen-repl` demo. `PORTING.md` has the
rest.

**Done this session, all on `main`:**
- **DCLEG proofs merged** (`5c94daf`, from `dcleg-proofs-draft`) as a library
  illustration: `DclegProofs/`, `Tests/DclegProofs.lean`. Q1–Q18 for Jeremiah
  are still open, and the README and `FINDINGS.md` say so. The branch and its
  worktree `~/Projects/Logic/gamen-lean-dcleg-proofs/` still exist and can be
  deleted; the backup bundle is `~/Backups/dcleg-proofs-draft-2026-09-30.bundle`.
- **guideline-validation migration, Phase 1.1: patch prepared, not applied.**
  - Record: `docs/assessment/guideline-validation-migration-2026-10-05.md`.
  - Patch: `docs/assessment/patches/guideline-validation-lean-discovery-2026-10-05.patch`.
  - `detect_conflicts.py` on the canonical data gives byte-identical JSON on
    the Haskell and Lean binaries, in both modes (20 and 5 triples).
- **cwyde migration, Phase 1.2: patch prepared, not applied.**
  - Record: `docs/assessment/cwyde-migration-2026-10-05.md`.
  - Patch: `docs/assessment/patches/cwyde-lean-discovery-2026-10-05.patch`.
  - The old cabal fallback never fired (wrong path), so cwyde's gamen tests
    were skipping in a plain run.
  - One test fails identically on both binaries, so it predates the migration:
    `test_gamen_bridge.py::test_consistency_indication_with_existence`
    (`unsupported operator: Knowledge`). Not investigated.
- **`dcleg-service` port, Phase 0c: merged** (`212bc9d`).
  - Plan: `plans/dcleg-service-port-2026-10-05.md`.
  - New executable `dcleg-service` (`DclegService.lean`, `DclegService/*`),
    `Gamen/Service/{Protocol,Formula,Model,Axioms}.lean`,
    `Tests/DclegService.lean`, `data/dcleg-service/` (golden sessions),
    `tools/compare/compare_dcleg.py`.
  - Blind-reviewed (Opus); review fixes applied (premises classification
    narrowed, divergence D6 listed). `compare_dcleg.py`: 0 DISAGREE over 3272
    requests. `compare.py`: unchanged (4582 / 46 / 0 / 103).
  - Divergences D1–D6 are in `tools/compare/intentional-divergences.md`.
  - `tools/install.sh` was edited to install it but has **not been run**
    for `dcleg-service`.
- **Installed, off `PATH`:** `~/.local/share/gamen-lean/gamen-validate`, built
  from `5c94daf`. It is older than `main` now (it lacks the `Validate/Stamp.lean`
  move). Reinstall with `tools/install.sh` before relying on it.
- **Untracked, deliberately:** `notes/dcleg-thesis-final.pdf`. Don't commit it.

## Open threads

| Thread | Plan | State | Next step |
|---|---|---|---|
| Downstream migration | `plans/downstream-migration-2026-09-29.md` | 0a/0b/0c done; Phase 1.1 and 1.2 patches ready | Brian applies the two patches (or lifts the read-only rule). Then **1.3 gamen-simulations** (below), then Phase 2 |
| Guideline-validation logic | `plans/logic-for-guideline-validation-2026-09-29.md`; `plans/gv-phase2-followups-2026-09-30.md` | Phase 2 merged | Brian approves the 4 draft definitions; then a clinician sample |
| K tableau soundness | `plans/countermodel-explorer-and-k-soundness-2026-09-29.md`, Part B | Part A merged | B0 spike on derived `Ord` lawfulness |
| Edition-proof citations | same plan, Part C | not started | `tools/bd/citations.py`: index, check, migrate. Covers DCLEG citations too |
| DCLEG thesis verification | `plans/dcleg-thesis-verification-2026-09-29.md` | proofs merged; Q1–Q18 open | Wait for Brian's talk with Jeremiah (especially Q12 and Q13) |
| Three-valued teaching | `plans/three-valued-logic-2026-09-29.md` | Done | Optional: look at the tables in the VS Code infoview |

### The default next thread: gamen-simulations onto the Lean `dcleg-service` (Phase 1.3)

`~/Projects/Logic/Julia/gamen-simulations`; its README says it is "built on
gamen-hs via JSON Lines services". It needs Brian's OK for any edit there (its
own session). Before editing anything:
1. **Check its models against divergence D3:** `build` now rejects a model
   whose histories play a move that `moves` doesn't list (`model_invalid`).
   gamen-hs accepted these.
2. **Check whether it uses `enumerate_counterfactuals` or `info`.** The spec
   lists them, but gamen-hs never implemented them, so both Haskell and Lean
   answer `unknown_op`.
3. **Check the Monte Carlo runs are seeded**, or a before/after over fixed seeds
   means nothing (plan, Phase 1.3).
4. Capture a before run (Haskell `dcleg-service`), switch, capture an after
   run, and classify every difference against D1–D6.
Then correct `~/Projects/Logic/CLAUDE.md` (gamen-simulations missing from the
project table; the stale `guideline-cds-simulation` and `patient-agent-assistant`
lines).

## Open questions for Brian

- [ ] **Apply the two migration patches?** Or lift the read-only rule on
  guideline-validation and cwyde for an agent to apply them. Either needs
  `GAMEN_VALIDATE_BIN` (or `CWYDE_GAMEN_BIN`) set where the tool runs, or
  `tools/install.sh --link`, which switches every caller at once.
- [ ] **Rename `cwyde-haskell-bridge`?** Nothing outside cwyde imports it. Its
  file list is in the cwyde record.
- [ ] **The failing cwyde test** (`Knowledge` outside the prover's fragment): a
  cwyde encoding problem or a prover gap? Needs its own look.
- [ ] **When to make gamen-lean public**, and gamen-hs's fate (archive it; its
  PRs #44, #56–#58).
- [ ] **Share `FINDINGS.md` and the outcome-node write-up with Jeremiah?** Note
  `FINDINGS.md` is now on `main`.
- [ ] **The 4 GV draft definitions**, and the draft timing-limitation paragraph in
  the Lean GV port.
- [ ] **Delete the worktree and branch** `worktree-agent-aed8ec54ad95ac08b`
  (merged) and `dcleg-proofs-draft` (merged)?
- [ ] **Stale Lake cache entries** from a reviewer, under
  `~/.elan/toolchains/leanprover--lean4---v4.34.0/lake/cache/`: see the
  2026-10-01 handoff for the file list.
- [ ] **A leaked API key.** `~/Projects/Logic/Julia/guideline-validation/.env`
  holds an Anthropic API key; an agent printed it into a session transcript on
  2026-10-05. The file is gitignored. Rotate the key if that transcript is
  stored or shared.

**For Jeremiah:** Q1–Q18 in `DclegProofs/Semantics.lean` (`grep -n "QUESTION FOR
JEREMIAH" DclegProofs/*.lean`), and the three questions at the end of
`docs/dcleg-outcome-node-premises-2026-09-30.md`. If he doesn't understand a
question, re-ask it against the thesis page, in plain logic terms with an
example; offer "as written / other reading / thesis doesn't settle it"; don't
record a guess as an answer.

## Task list (ordered by what's unblocked now)

1. **Ask Brian which thread to pick up.** If it's the migration, first ask
   whether the two patches are applied.
2. **Default:** gamen-simulations (Phase 1.3, above), once Brian OKs edits there.
3. **Part C, citation tooling.**
4. **Part B0,** the soundness spike.
5. **Phase 2 of the migration** (retire gamen-hs as a runtime dependency) once
   every project is verified on Lean. Archiving gamen-hs is Brian's decision.

## Things learned this session

- **The porter agent is pinned to Sonnet** in `.claude/agents/module-porter.md`;
  pass `model: "opus"` on the Agent call for Opus work. It is written for one
  `src/Gamen/<Module>.hs` module, so a different-shaped port needs the prompt
  to say what differs (see `plans/dcleg-service-port-2026-10-05.md`).
- **`lake` is not on the shell's PATH:** use `export PATH="$HOME/.elan/bin:$PATH"`.
- **Shell traps:** the shell is zsh, so an unquoted `$VAR` holding several words
  is not split; `sed -i` needs `-i ''` on macOS; `| head -1` can kill a process
  with SIGPIPE and leave its output file unwritten.
- Downstream repos carry uncommitted work (guideline-validation, cwyde); patches
  were written against `HEAD` and touch none of it. Never run `pixi run` in
  guideline-validation: use `.pixi/envs/default/bin/python` with `PYTHONPATH`.

## Suggested implementer model

- **Migration plumbing** (Python, env config, before/after diffs): **Sonnet**,
  with an **Opus** blind reviewer.
- **Lean library and proof work** (Part B, the DCLEG proofs): **Opus or Fable.**
  A wrong definition type-checks fine.
- **Citation tooling** (Python): **Sonnet**, with an Opus reviewer.
