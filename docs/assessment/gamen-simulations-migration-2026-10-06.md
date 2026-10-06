# gamen-simulations onto the Lean `dcleg-service`: before/after and patch (2026-10-06)

Plan: `plans/downstream-migration-2026-09-29.md`, Phase 1.3. A dated record;
add to it, don't rewrite it. Nothing in gamen-simulations
(`~/Projects/Logic/Julia/gamen-simulations`, HEAD `c328fdf`) was changed. The
runs used a scratch copy of its working tree; the change is a patch.
Helpers: `tools/migration/`.

## Pre-checks

- **Operations used:** the three notebooks call only `ping`, `build`, `sat`,
  `counterfactual`, `axiom_check` and `drop` (through `DclegClient`). Nothing
  calls `enumerate_counterfactuals` or `info`, which neither binary implements.
- **Seeds:** no `rand`, `seed` or RNG call in `notebooks/`, `src/`; the
  notebooks only `using Random`. The requests were identical across the two
  runs of each notebook, so the comparison is reproducible.
- **Divergence D3** (`build` rejects a model whose histories play a move that
  `moves` does not list): no notebook model hits it. Every `build` succeeded,
  with an identical response, on both binaries.
- **Binary discovery:** there is none. The notebooks read `DCLEG_SERVICE`, with
  a hardcoded gamen-hs path as the default; `DclegClient(binary)` takes a path.
- `test/` holds only `Project.toml` and `Manifest.toml`: no tests exist.

## Before/after

Each notebook was run headlessly with Pluto (`run_pluto_notebook.jl`) twice,
through `jsonl_tee_shim.py`, once with the gamen-hs `dcleg-service` and once with
gamen-lean's (`5d9df0f`).

| Notebook | Requests | Responses identical, Haskell vs Lean |
|---|---|---|
| `mm-counterfactual` | 28 | 28 |
| `suicide-disclosure` | 33 | 33 |
| `vus-counseling` | 81 | 81 |

So 142 of 142 responses are byte-identical, and no notebook reaches any of
D1–D6 (D2, the premise function, would show at an outcome vertex or a
single-move vertex reached by more than one world; none occurs here).

Pluto reports the same cell errors on both: `mm-counterfactual` has 2 errored
cells (an invalid string escape, `\_`, in a markdown-table cell, and the cell
that depends on it); the other two have 0. The escape defect is in `HEAD`
already (3 occurrences), so it predates the migration.

## The patch

`patches/gamen-simulations-lean-service-2026-10-06.patch`, made against the
**working tree** (not `HEAD`), because the repository has uncommitted edits to
the same lines (they already move `~/Code/Haskell` to `~/Projects/Logic/Haskell`).
Apply with `patch -p1` from the repository root; a dry run applied cleanly.
It changes:
- the default `DCLEG_SERVICE` in the three notebooks, to
  `~/.local/share/gamen-lean/dcleg-service`;
- `README.md` and `CLAUDE.md`: install steps (`tools/install.sh`), the project
  table (gamen-lean added; gamen-hs marked frozen), the architecture box, the
  build/run section, and a one-paragraph migration note;
- one comment in `src/GamenSimulations.jl`; one stale comment in two notebooks.

Applied to a fresh copy, with `DCLEG_SERVICE` unset, the three notebooks run
on the Lean binary with the same cell errors as before (2, 0, 0).

## Not in the patch (for Brian)

- `tools/install.sh` has now been run, so `~/.local/share/gamen-lean/` holds
  `gamen-validate` and `dcleg-service`, both stamped `5d9df0f`. Not on `PATH`.
- `CLAUDE.md` still says "build a Haskell-side model" (line ~30) and that "the
  Haskell side expects arrays of tuples only" (line ~180): background prose.
- Other notes and plans in the repo mention gamen-hs (`plans/`, `notes/`);
  left alone.
- The `mm-counterfactual` escape defect is not fixed here: it is not a
  migration matter.
- Phase 1.4 and 1.5 remain: `guideline-cds-simulation` (it depends on
  gamen-simulations; no direct call found) and `patient-agent-assistant`
  (no gamen reference found), plus correcting `~/Projects/Logic/CLAUDE.md`.
