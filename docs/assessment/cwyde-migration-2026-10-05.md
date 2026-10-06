# cwyde onto the Lean `gamen-validate`: before/after and patch (2026-10-05)

Plan: `plans/downstream-migration-2026-09-29.md`, Phase 1.2. A dated record;
add to it, don't rewrite it. Nothing in cwyde (`~/Code/Python/cwyde`, HEAD
`66199c2`) was changed: changes to a downstream repository wait for Brian, so
the change is a patch. Companion record for the first migration:
`guideline-validation-migration-2026-10-05.md`.

## Before/after

`pytest --require-gamen` over the whole suite, in cwyde's `.venv`, with caching
and bytecode off (cwyde tracks `.pyc` files in git; the runs left its working
tree unchanged). Lean binary: gamen-lean `5c94daf`, installed by
`tools/install.sh`, not on `PATH`.

| Run | Result |
|---|---|
| Current discovery, nothing set | 183 passed, **22 errors** (no binary found) |
| gamen-hs binary via `CWYDE_GAMEN_BIN` | 204 passed, 1 failed |
| Lean binary via `CWYDE_GAMEN_BIN` | 204 passed, 1 failed (same test, same error) |
| Patched copy, Lean via `CWYDE_GAMEN_BIN` | 209 passed, 1 failed (same test) |
| Patched copy, Lean on `PATH` only | 209 passed, 1 failed (same test) |

- **Same failure on both binaries, so it predates the migration:**
  `tests/integration/test_gamen_bridge.py::test_consistency_indication_with_existence`
  fails with `unsupported operator: Knowledge (not in the kdt+doxasticD
  fragment)`. Not investigated here; it needs its own look (cwyde's
  `Knowledge`/`Indication` encoding against the prover's fragment).
- **The cabal fallback never fired.** Its glob looked under
  `~/Code/Haskell/gamen-hs`, but gamen-hs lives at
  `~/Projects/Logic/Haskell/gamen-hs`. With nothing set, the gamen tests
  could not find a binary at all, so they skipped in a plain run.
- The patched copy was a scratch copy of the tree with the patched files
  overlaid, checked to be the modules actually imported. The five new tests
  and a sixth were run against the original `discovery.py` too: two fail
  there, as intended.

## The patch

`patches/cwyde-lean-discovery-2026-10-05.patch` (`git apply` from the cwyde
root; checked against HEAD):

1. `discovery.py`: removes the cabal glob and the now-unused `glob` import;
   rewrites the docstring; gives `GamenBinaryNotFound` a real list of what
   was searched, with the `tools/install.sh` hint. Also removes a dead
   `from cwyde_haskell_bridge.schema import searched_paths` (no such name),
   which made `require_gamen_validate()` raise `ImportError` instead of
   `GamenBinaryNotFound`.
2. `src/cwyde/formal/modal.py`: the tree-format reference points at
   gamen-lean's `Gamen/Protocol.lean`.
3. `README.md`: the install section builds gamen-lean with `tools/install.sh`
   instead of building gamen-hs with cabal.
4. `tests/unit/test_gamen_discovery.py`: six tests for the search order and
   for the absence of any cabal fallback.

## Not in the patch (for Brian)

- **Renaming `cwyde-haskell-bridge`** (plan: only with Brian's OK). Nothing
  outside cwyde imports it (searched `~/Projects/Logic` and `~/Code/Python`),
  so no compatibility import is needed. It would touch the package, the root
  `pyproject.toml` extras, `tests/conftest.py`,
  `tests/integration/test_gamen_bridge.py`, `README.md`, three `docs/`
  files, `scripts/spike_gamen_roundtrip.py` and two example notebooks.
- Env setup: `CWYDE_GAMEN_BIN` must be exported where cwyde runs, or the
  binary put on `PATH` with `tools/install.sh --link` (switches every
  caller).
- Prose in `docs/` that still describes gamen-hs and `~/Code/Haskell/gamen-hs`
  (`doxastic-semantics.md`, `modal-semantics.md` "Connection to gamen-hs",
  `architecture.md`): left alone; it is background, not instructions.
- Hygiene: cwyde tracks `__pycache__/*.pyc` (11 modified files in its tree) and
  has `.claude/worktrees/agent-*` with a stale copy of the tree.
