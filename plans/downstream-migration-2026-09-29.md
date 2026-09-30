# Plan: migrating every downstream project from gamen-hs to gamen-lean

*Written 2026-09-29. Read this once; implement against it.*

*Brian decided on 2026-09-29 that gamen-lean is the primary implementation,
that gamen-hs is frozen, and that **all downstream applications migrate to
gamen-lean**. This plan says how.*

*Work in each downstream repository happens in a session in that repository,
with Brian's approval. This plan only sets the order and how each migration
is verified.*

## Principle

The Lean `gamen-validate` answers the existing request types byte for byte
like gamen-hs, except for the divergences listed in
`tools/compare/intentional-divergences.md`. So each migration is:
1. point the caller at the Lean binary;
2. rerun the caller's own tests and a before/after comparison on real
   inputs;
3. check that every difference is a listed divergence.

An unexplained difference is a bug in gamen-lean. Fix it there, with a test.

## Inventory (checked 2026-09-29)

| Project | What it calls | How it finds it | Migration |
|---|---|---|---|
| **guideline-validation** (canonical, `~/Projects/Logic/Julia/guideline-validation`) | `gamen-validate` | `find_gamen_validate()` in `extraction/src/guideline_extraction/detect_conflicts.py`: `$GAMEN_VALIDATE_BIN`, then `PATH`, then a gamen-hs `dist-newstyle` glob | Point it at the Lean binary. Conflict detection already runs on the Lean port (ADR-0002) |
| **cwyde** (`~/Code/Python/cwyde`) | `gamen-validate` | `packages/cwyde-haskell-bridge/.../discovery.py`: `$CWYDE_GAMEN_BIN`, `$GAMEN_VALIDATE_BIN`, `PATH`, then a cabal glob. Its tests skip without a binary unless `--require-gamen` is given | Point it at the Lean binary, then rename the bridge package |
| **gamen-simulations** (`~/Projects/Logic/Julia/gamen-simulations`; not in the project-family table) | **`dcleg-service`**, per its README ("built on gamen-hs via JSON Lines services") | to check | **Blocked: `dcleg-service` isn't ported.** See Phase 0c |
| **guideline-cds-simulation** (`~/Projects/Logic/Julia/guideline-cds-simulation`) | depends on `GamenSimulations` (`../gamen-simulations`). **No `gamen-validate` call found in `src/`**, although the family CLAUDE.md says it has one | via gamen-simulations | Follows gamen-simulations. Check the CLAUDE.md claim |
| **patient-agent-assistant** (`~/Code/Python/patient-agent-assistant`) | **no reference to gamen found** in its `.py`, `.md` or `.toml` files, although the family CLAUDE.md says it calls `gamen-validate` | — | Probably only a documentation fix. Confirm with Brian |

**The two stale claims** in `~/Projects/Logic/CLAUDE.md` (guideline-cds-simulation
and patient-agent-assistant calling `gamen-validate`) should be confirmed and
corrected. The same file should add gamen-simulations to the project table.

## Phase 0: prerequisites in gamen-lean

### 0a. Let callers tell which implementation answered

Today both binaries answer `{"action":"ping"}` with the identical
`{"ok":true,"result":"pong"}`, so a caller can't check that it switched.
- **Add a Lean-only action** `{"action":"version"}`, returning
  `{"ok":true,"result":{"implementation":"gamen-lean","commit":"<git rev>","protocol":1}}`,
  and leave `ping` unchanged.
- **Check `compare.py`'s corpus** for a `version` action. gamen-hs answers
  unknown actions with an error, so if the corpus sends one, record it as
  intentional divergence #2.
- Put the protocol number in `Protocol.lean`, and document the new action.
  This is the "version field" that CLAUDE.md asks new capabilities to carry.

### 0b. A stable, installed binary

- **Add `tools/install.sh`:** run `lake build gamen-validate` (and later
  `dcleg-service`), then symlink `~/.local/bin/gamen-validate` to
  `gamen-lean/.lake/build/bin/gamen-validate`. Print the `version`
  response, so the install can be checked.
- **Migrate each caller with its environment variable first**
  (`GAMEN_VALIDATE_BIN` / `CWYDE_GAMEN_BIN`), so the others aren't
  affected. Only when every `gamen-validate` caller is verified, install on
  `PATH`. Every lookup checks the environment variable and then `PATH`
  before its Haskell fallback, so the `PATH` install switches whatever is
  left.

### 0c. Port `dcleg-service` (blocks gamen-simulations)

- It's the "`protocol/Service/*` + `service/Main.hs` (dcleg service), 893
  lines" row in `PORTING.md`, not started. `Gamen.Dcleg` is already
  ported, so this is the protocol, the model building and the service
  loop.
- **Port it the usual way,** through `/port-module`-style runs: a porter, a
  blind reviewer, planted checks. Also add a `compare.py`-style side-by-side
  check for the service protocol, using the gamen-hs `dcleg-service`
  binary, and port the 5 `RegressionIssue18` "task 18: dcleg-service build
  hardening" tests that were skipped with Dcleg.
- Model: Opus (JSON protocol plus byte compatibility). Set the `PORTING.md`
  Porter column when starting.

## Phase 1: one project at a time

In each project, capture a **before** run on the Haskell binary, switch,
capture an **after** run, and compare the two.

1. **guideline-validation** (first: smallest, and already mostly on Lean)
   - Set `GAMEN_VALIDATE_BIN` for the project, e.g. in its pixi or env
     configuration, and in the Snakemake rules that call the tools.
   - Verify:
     - its tests;
     - `detect_conflicts.py` before vs after on the canonical data (paper
       mode and agent-aware mode);
     - the Lean port's parity checks.

     Expected: identical except for gamen-hs#41 rows (divergence #1).
   - Then remove the gamen-hs `dist-newstyle` fallback from
     `find_gamen_validate()` and update the docstring and error message.
2. **cwyde**
   - Set `CWYDE_GAMEN_BIN`, then run `pytest --require-gamen` (unit and
     integration).
   - Rename `cwyde-haskell-bridge` to something implementation-neutral
     (e.g. `cwyde-gamen-bridge`). Keep a compatibility import for one
     release if anything outside cwyde imports it.
   - Update `src/cwyde/formal/modal.py`'s reference to gamen-hs's
     `validate/Main.hs` to point at gamen-lean's `Gamen/Protocol.lean`.
   - Remove the cabal-glob fallback from `discovery.py`.
3. **gamen-simulations** (after 0c)
   - Point its `dcleg-service` path at the Lean build.
   - Verify with its tests and notebooks, and a before/after comparison of
     the service output over fixed seeds. The Monte Carlo runs must be
     seeded for this to mean anything; check that first.
   - Update its README ("built on gamen-hs") and add it to the
     project-family table.
4. **guideline-cds-simulation**
   - Nothing to do beyond gamen-simulations, unless a direct call turns up.
   - Correct the family CLAUDE.md line about it.
5. **patient-agent-assistant**
   - Confirm that nothing calls gamen, then correct the family CLAUDE.md
     line.

## Phase 2: retire gamen-hs as a runtime dependency

- Once every project is verified on Lean:
  - install on `PATH` (0b);
  - remove the remaining Haskell fallbacks;
  - update the family CLAUDE.md dependency lines.
- `compare.py` still needs a gamen-hs build, for as long as byte
  compatibility is kept. Decide later whether to keep it (a frozen,
  reference build) or retire it once no caller needs byte compatibility.
- **Archiving gamen-hs on GitHub is a separate decision for Brian.** So is
  what happens to its open PRs (#44, #56–#58) and the in-progress #53
  branch, which another session was working on on 2026-09-29.

## Order

1. 0a and 0b (small; one session).
2. guideline-validation, then cwyde.
3. 0c, the `dcleg-service` port (the largest item).
4. gamen-simulations, then guideline-cds-simulation and
   patient-agent-assistant (documentation).
5. Phase 2.

## Stop and ask Brian before

- any change in a downstream repository (each is its own session);
- installing on `PATH`, which switches every caller at once;
- archiving gamen-hs, or closing its open PRs;
- renaming the cwyde bridge package, if anything outside cwyde imports it.
