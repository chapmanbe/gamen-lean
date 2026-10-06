# guideline-validation onto the Lean `gamen-validate`: before/after and patch (2026-10-05)

Plan: `plans/downstream-migration-2026-09-29.md`, Phase 1.1. A dated record;
add to it, don't rewrite it. Nothing in the canonical repository
(`~/Projects/Logic/Julia/guideline-validation`, HEAD `899b67f`) was changed:
it is read-only for agents, so the change is a patch for Brian to apply.

## Before/after

`detect_conflicts.py` on `data/derived/blumenthal-2026_extracted.json` and
`dietary_domain_axioms.json`, once with the gamen-hs binary and once with the
Lean binary installed by `tools/install.sh` (gamen-lean `5c94daf`, not on
`PATH`), in both modes:

| Mode | Inconsistent triples | Raw output JSON, Haskell vs Lean |
|---|---|---|
| paper (stripped) | 20 (12 unique rec-target pairs) | byte-identical |
| agent-aware | 5 (3 unique pairs) | byte-identical |

So there are no divergence rows to explain here, including none from
gamen-hs#41. The project's own tests pass with `GAMEN_VALIDATE_BIN` set to
the Lean binary (extraction: 76 passed). The patched file also reproduces
the Haskell output byte for byte when it finds the Lean binary through
`$GAMEN_VALIDATE_BIN`.

Not rerun: `lean/tools/parity.py`. It already passes the Lean binary to
`detect_conflicts.py` through `--binary`, and the Snakemake `detect_conflicts`
rule already runs the Lean port (ADR-0002), so neither is affected.

## The patch

`patches/guideline-validation-lean-discovery-2026-10-05.patch`
(`git apply` from the canonical repository's root; checked against HEAD):

1. `find_gamen_validate()`: drops the gamen-hs `dist-newstyle` glob. It now
   checks `$GAMEN_VALIDATE_BIN`, then `PATH`; the error points at
   `tools/install.sh`.
2. `prover_provenance()`: asks the binary for `{"action": "version"}` and
   records its own commit stamp. Without this, an installed Lean binary
   (no checkout beside it) would record "gamen-hs repo  HEAD unknown" in the
   sidecar note. A binary without `version` is recorded as unknown.
3. `extraction/tests/test_find_gamen_validate.py`: five tests for both.

## Not in the patch (for Brian)

- `GAMEN_VALIDATE_BIN` still has to be set where the Python tool runs
  (shell, or pixi/env configuration), or the binary put on `PATH` with
  `tools/install.sh --link`, which switches every caller at once.
- Stale text in the canonical repository: `README.md` line 87 (`cabal run
  gamen-validate`) and line 210 (gamen-hs provides the service); `AGENTS.md`;
  `analysis/crest/scripts/run_conflict_detection.py` (defaults to
  `/tmp/gamen-validate`); `lean/tools/parity.py` (builds gamen-lean in place
  rather than using the installed copy).
- The working tree of the canonical repository has uncommitted changes
  (`.gitignore`, `AGENTS.md`, `NEXT.md`, `pixi.toml`, and others). The patch
  touches none of them.
