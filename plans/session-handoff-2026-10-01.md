# Implementation Plan: continue gamen-lean (session handoff)
*Written 2026-10-01 at the close of a session that finished the three-valued
notebooks, migration Phase 0a/0b, and gamen-lean#1. Read this once; it
indexes the detailed plans, which you read only for the thread you pick up.
Supersedes `plans/session-handoff-2026-09-30.md`, which is now history.*

## Objective

Pick up **one** open thread below, implement it against its own plan, and
get Brian's approval before merging. Done for a thread means:
- its plan's "Done when" is met;
- it was reviewed independently (a blind reviewer, planted checks);
- `lake build` and `lake test` pass on `main`;
- Brian approved the merge.

## Where things stand (2026-10-01; verify with `git log`)

**gamen-lean:**
- `main` is at `4597b44`, pushed. `lake test` passes 1188/1188.
- Every gamen-hs library module is ported. Not yet ported: the dcleg
  service and the `gamen-repl` demo. `PORTING.md` has the rest.
- **Done this session, all merged and pushed:**
  - **The three-valued notebooks** (`820fc3a`):
    - `Notebooks/PropLogicPrimer.lean` and `Notebooks/ThreeValued.lean`;
    - static truth and entailment tables plus graders in
      `Widgets/TruthTable.lean`;
    - answer keys in `Tests/ManyValuedNotebooks.lean`;
    - records in `docs/assessment/three-valued-*-2026-09-30.md` (the
      verified spec facts, and the Fable novice walkthrough).
  - **Migration Phase 0a/0b:**
    - the Lean-only `{"action":"version"}`, with its commit stamp in
      `Validate/BuildInfo.lean`;
    - `tools/install.sh`;
    - tests in `Tests/ValidateVersion.lean`.
  - **gamen-lean#1, closed:** the flat decoder had guessed on an unknown
    `op` or `temporal_op`. This was the port of gamen-hs#60, found by
    `compare.py`. Tests are in `Tests/ProtocolFlat.lean`.
- **Untracked, deliberately:** `notes/dcleg-thesis-final.pdf`. Don't commit
  it.

**Kept on purpose; don't merge or delete:**
- Branch `dcleg-proofs-draft` (`1db8e7e`), in the worktree
  `~/Projects/Logic/gamen-lean-dcleg-proofs/`.
  - It holds the Lean formalization of Jeremiah's thesis proofs.
  - Brian merges it only after talking with Jeremiah.
  - Backup: `~/Backups/dcleg-proofs-draft-2026-09-30.bundle`. Make a fresh
    bundle after any new commits.

**Lean guideline-validation port**
(`~/Projects/Logic/Lean/guideline-validation`, remote
`chapmanbe/guideline-validation-lean`): Phase 2 is merged. Its 4 draft
condition definitions await Brian's approval
(`docs/applicability-definitions-review.md` there).

## Decisions (do not relitigate)

**Carried over from 2026-09-30:**
- **gamen-lean is primary, and gamen-hs is frozen.**
  - New logics, features and fixes happen here; file issues on gamen-lean.
  - All downstream projects migrate to gamen-lean.
  - JOSS targets gamen-lean.
- **`compare.py` is a compatibility check, not the contract.**
  - Every disagreement must be listed in
    `tools/compare/intentional-divergences.md`.
  - Existing requests stay byte-compatible.
  - New capabilities are Lean-only extensions, with a version field.
- **Pins:**
  - B&D (Fall 2025) is in `notes/` with its SHA, in `notes/bd-edition.md`.
  - DCLEG citations mean the final thesis.
  - Axiom audits are allowlists: `native_decide` shows up as a per-theorem
    axiom.
- **DCLEG outcome-node premises** are merged as `f6ce8b3`. Revert with
  `git revert -m 1 f6ce8b3` if Jeremiah prefers a different F.
- **Process.** Every change gets:
  - an implementer on a branch;
  - a blind reviewer (Opus) with its own scratch area;
  - planted checks;
  - a fix round;
  - a merge only with Brian's approval.

  Nothing waits on students: an agent walkthrough stands in, recorded in
  `docs/assessment/`.

**New on 2026-09-30/10-01:**
- **The commit stamp is taken at compile time**, by `build_commit%` in
  `Validate/BuildInfo.lean`.
  - git runs in gamen-lean's own directory.
  - `-dirty` counts only source files, tracked or untracked: `*.lean`,
    `lakefile.toml`, `lean-toolchain` and `lake-manifest.json`.
  - Why: the binary can't find its source at run time, and a run-time
    `git` call would describe the checkout rather than the build.
- **`enableArtifactCache = false` in `lakefile.toml`.**
  - Lake's shared cache is keyed on source hashes only, so it could
    restore a binary stamped with another commit.
  - The package setting overrides `LAKE_ARTIFACT_CACHE`.
  - Don't remove it.
- **`tools/install.sh` copies the binary to
  `~/.local/share/gamen-lean/gamen-validate`, and links it onto PATH only
  with `--link`.**
  - `~/.local/bin` is already on PATH, so a link switches every remaining
    caller at once.
  - Callers migrate one at a time, through their environment variable.
  - The copy keeps later `lake build`s from changing what callers run.
  - The script refuses a stamp that isn't `HEAD`. A `-dirty` stamp needs
    `--allow-dirty`.
- **The compare baseline is gamen-hs `main` at `fd8b269`.**
  - Expected: 103 disagreements, all of them divergence #1 (gamen-hs#41,
    PR #44 still open).
  - Every other section has 0 disagreements. The "equivalent" ones differ
    only by aeson's `Error in $…: ` prefix, which is known and accepted.
  - The `fix/41` branch baseline is historical.
- **A bug found by `compare.py` is fixed in Lean** (gamen-lean#1 is the
  model): file the issue, write a fix with tests, and run planted checks.
  Matching gamen-hs's newer behavior is not a new divergence.
- **Teaching notebooks for novices:**
  - a "Lean you need" box;
  - every exercise's formula is a named `def` that the answer-key tests
    share;
  - each `#check` gets a plain-English caption;
  - static `#html` tables only. A clickable truth table needs Brian's OK
    first: it would change the KripkeExplorer's `ExplorerState`.

## Architecture: the open threads and their plans

| Thread | Plan (read only if you pick it) | State | Next step |
|---|---|---|---|
| Downstream migration | `plans/downstream-migration-2026-09-29.md`, Phase 1 | 0a/0b done | **guideline-validation** (see "The default next thread" below), then cwyde. Blocked beyond that: gamen-simulations needs the `dcleg-service` port (0c) |
| `dcleg-service` port (migration 0c) | same plan, 0c; `PORTING.md` row "protocol/Service/* + service/Main.hs" (893 lines) | not started | A `/port-module`-style run (Brian invokes it), plus a side-by-side check on the service protocol and the 5 skipped `RegressionIssue18` tests |
| Guideline-validation logic | `plans/logic-for-guideline-validation-2026-09-29.md`; follow-ups in `plans/gv-phase2-followups-2026-09-30.md` | Phase 2 merged | Brian approves the 4 draft definitions; then a clinician sample before any paper claim |
| Three-valued teaching | `plans/three-valued-logic-2026-09-29.md` | **Done** | Optional: check how the tables look in the VS Code infoview. Ask Brian before raising the FHIRPath `implies` note/table conflict with HL7 (Jira not searched) |
| K tableau soundness | `plans/countermodel-explorer-and-k-soundness-2026-09-29.md`, Part B | Part A merged | B0 spike on derived `Ord` lawfulness |
| Edition-proof citations | same plan, Part C | not started | `tools/bd/citations.py`: index, check, migrate. Covers DCLEG citations too |
| DCLEG thesis verification | `plans/dcleg-thesis-verification-2026-09-29.md` | proofs draft on `dcleg-proofs-draft` | Wait for Brian's talk with Jeremiah (Q1–Q18, especially Q12 and Q13) |

### The default next thread: guideline-validation onto the Lean binary

From the migration plan's Phase 1.1. In short:
1. In this repo, run `tools/install.sh`, without `--link`.
2. In the canonical guideline-validation repository
   (`~/Projects/Logic/Julia/guideline-validation`), set
   `GAMEN_VALIDATE_BIN=~/.local/share/gamen-lean/gamen-validate`: in its
   pixi or env configuration, and in the Snakemake rules that call the
   tools.
3. Capture a **before** run (Haskell binary) and an **after** run (Lean):
   - its tests;
   - `detect_conflicts.py` on the canonical data, in paper mode and in
     agent-aware mode;
   - the Lean port's parity checks.

   Expected: identical, except for gamen-hs#41 rows (divergence #1).
4. Then remove the gamen-hs `dist-newstyle` fallback from
   `find_gamen_validate()` (`extraction/src/guideline_extraction/detect_conflicts.py`),
   and update its docstring and error message.

**Blocked on Brian first** (see Open questions): the canonical repository
is read-only for agents.

## Interfaces / contracts

- **`version`** (`Validate/Core.lean`, `versionResult`):
  `{"ok":true,"result":{"commit":"<12-hex>[-dirty]|unknown","implementation":"gamen-lean","protocol":1}}`.
  - Keys are alphabetical, as `Json.compress` writes them.
  - `Gamen.Protocol.protocolVersion` is `1`. Bump it when a Lean-only
    extension changes what callers send or receive.
  - gamen-hs answers `{"error":"Error in $: Unknown action: version","ok":false}`.
- **`serveLine` (`Validate/BuildInfo.lean`) is what `main` calls;**
  `processLine line commit` is the pure core.
- **Flat format:**
  - `op` ∈ {box, diamond, box_not};
  - `temporal_op` ∈ {absent/null, future_box, future_diamond, periodic};
  - anything else is an error: `unknown flat op: …` or
    `unknown flat temporal_op: …`;
  - a missing `atom` is reported first, then a bad `temporal_op`, then a
    bad `op`;
  - a `"type"` key selects tree format, even when `"op"` is present.
- **`tools/install.sh`:**
  - options: `[--link] [--bin-dir DIR] [--share-dir DIR] [--allow-dirty]`;
  - every refusal (a bad argument or stamp, or a non-symlink at the
    `--link` target) exits 1.
- **Callers' variables:** `GAMEN_VALIDATE_BIN` for guideline-validation,
  `CWYDE_GAMEN_BIN` for cwyde. Each checks its variable, then PATH, then a
  Haskell fallback.

## Constraints

- All of CLAUDE.md applies. In particular:
  - no `sorry`;
  - no `partial def` without a stated reason;
  - `Except`, not `panic!`;
  - run `compare.py` after touching `Protocol.lean`, `Validate*.lean` or a
    prover;
  - American English.
- **Downstream repositories:** each change is its own session, with
  Brian's approval. The canonical guideline-validation repository is
  **read-only for agents** until Brian says otherwise.
- **Reviewer agents** must not:
  - write to `~/.local/bin`;
  - set `LAKE_ARTIFACT_CACHE`;
  - write outside their own scratch directory.

  Tell them so in the prompt. A reviewer polluted Lake's shared cache on
  2026-09-30.
- **The thesis:** don't commit the PDF, and don't quote large passages
  from it.

## Non-goals / rejected alternatives

- **Updating gamen-hs:** it's frozen.
- **A run-time `git` lookup for the commit stamp:** it would describe the
  checkout, not the build.
- **Symlinking onto PATH by default in `install.sh`:** it would switch
  every caller at once.
- **Pointing callers at `.lake/build/bin`:** any `lake build` would change
  what they run.
- **Listing gamen-lean#1 as a divergence:** it was a Lean bug, now fixed.
  It's recorded in the "Comparison log" of `intentional-divergences.md`.
- **Mathlib in gamen-lean,** a blocklist axiom audit, and one big logic
  for guideline validation: all rejected earlier, for the reasons in their
  plans.

## Open questions for the implementer

**For Brian:**
- [ ] **The guideline-validation migration** needs edits in the canonical
  repository, which is read-only for agents. Does Brian lift that for this
  migration, do the edits himself, or have an agent prepare a patch for
  him?
- [ ] **Delete the stale Lake cache entries** a reviewer wrote, under
  `~/.elan/toolchains/leanprover--lean4---v4.34.0/lake/cache/`:
  - `artifacts/{20f4a01cacdbb3c6.olean,327f6e9ba58ade39.c,5516e1a25897b132.o,acee21cabbec8663}`;
  - `outputs/gamen/{6c5edf91c6782ab3,059682ff6733f6dd,bb9345f3b77a0a02}.json`.

  gamen-lean no longer reads the cache; other projects might.
- [ ] **Still open from before:**
  - when to make gamen-lean public;
  - gamen-hs's fate (archive it; its PRs #44, #56–#58);
  - whether to share `FINDINGS.md` and the outcome-node write-up with
    Jeremiah;
  - the 4 GV draft definitions;
  - the draft timing-limitation paragraph in the Lean GV port;
  - the stale lean4web `nodemon` (pid 10887).
- [ ] **Stale claims in `~/Projects/Logic/CLAUDE.md`:**
  - it says guideline-cds-simulation and patient-agent-assistant call
    `gamen-validate`, but none was found;
  - gamen-simulations is missing from its project table.

**For Jeremiah:** Q1–Q18 in `DclegProofs/Semantics.lean`, and the three
questions at the end of the outcome-node write-up.

## Task list (ordered by what's unblocked now)

1. **Ask Brian which thread to pick up,** and settle the first open
   question if it's the migration.
2. **Default:** guideline-validation onto the Lean binary (above). Then
   cwyde (Phase 1.2: `CWYDE_GAMEN_BIN`, `pytest --require-gamen`, rename
   the bridge package only with Brian's OK).
3. **Part C, citation tooling:** it catches wrong B&D and DCLEG citations
   at test time.
4. **Part B0,** the soundness spike.
5. **The `dcleg-service` port** (0c), which unblocks gamen-simulations.
6. **Optional:** check the three-valued notebooks in the VS Code infoview,
   or in `web/run-local.sh`, which binds to 127.0.0.1 only.

## Suggested implementer model

- **Migration plumbing** (guideline-validation, cwyde; Python, env config,
  before/after diffs): **Sonnet**, with an **Opus** blind reviewer. The
  diffs make failures loud.
- **Lean library and proof work** (Part B, the DCLEG proofs): **Opus or
  Fable.** A wrong definition type-checks fine.
- **The `dcleg-service` port:** **Opus.** It has a JSON protocol and must
  be byte-compatible.
- **Citation tooling** (Python): **Sonnet**, with an Opus reviewer.
