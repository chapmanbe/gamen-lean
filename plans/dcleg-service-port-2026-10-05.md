# Plan: port `dcleg-service` to Lean (migration Phase 0c)
*Written 2026-10-05. Sets up the run; nothing is ported yet. Parent plan:
`plans/downstream-migration-2026-09-29.md`, Phase 0c. This blocks
gamen-simulations (and, through it, guideline-cds-simulation).*

## Objective

A Lean `dcleg-service` executable that answers the same JSON Lines protocol as
gamen-hs's `dcleg-service`, byte for byte on the existing operations, so
gamen-simulations can be pointed at it. Done when:
- `lake build` builds a `dcleg-service` executable, and `lake test` passes;
- a side-by-side harness (`tools/compare/compare_dcleg.py`) runs the same
  request sessions through both binaries and every difference is a listed
  intentional divergence (`tools/compare/intentional-divergences.md`);
- the 5 skipped `RegressionIssue18` tests ("task 18: dcleg-service build
  hardening", `test/RegressionIssue18.hs` ~422-) are ported and pass;
- the `PORTING.md` rows are updated and a blind reviewer has signed off;
- Brian approved the merge.

## What is being ported (gamen-hs, ~893 lines of Haskell)

| Haskell | Lines | Lean target |
|---|---|---|
| `protocol/Service/Protocol.hs` | 55 | envelope, error codes (`Service/Protocol.lean`) |
| `protocol/Service/Formula.hs` | 38 | `DclegFormula` ↔ JSON |
| `protocol/Service/Model.hs` | 263 | model ↔ JSON, validation on `build` |
| `protocol/Service/Axioms.hs` | 284 | belief-revision axiom checks |
| `service/Main.hs` | 253 | registry, dispatcher, main loop |

Spec: `~/Projects/Logic/Haskell/gamen-hs/notes/dcleg-service-protocol.md`
(475 lines; ops: `ping`, `build`, `sat`, `true_in`, `counterfactual`,
`axiom_check`, `enumerate_counterfactuals`, `drop`, `list`, `info`). Where the
spec and the Haskell disagree, the Haskell is the behavior to match; list each
disagreement in the report.

Already done and not to be redone: `Gamen/Dcleg.lean` (528 lines;
`DclegFormula`, `StrategicStructure`, `mkStrategicStructure`, …) and
`dclegCases` (DclegServiceSpec, which tests `Gamen.Dcleg` directly).

## Layout

- Modules mirror the Haskell, as in `CLAUDE.md`: `Gamen/Service/{Protocol,
  Formula,Model,Axioms}.lean` (add to `Gamen.lean`), and an executable root
  `DclegService.lean` (name it to match `Validate.lean`'s convention) with a
  `[[lean_exe]] name = "dcleg-service"` entry in `lakefile.toml`.
- Follow how `Validate.lean` / `Validate/Core.lean` and `Gamen/Protocol.lean`
  already solve JSON Lines I/O and byte-identical output (key order, number
  formatting, escaping). Reuse; don't reinvent.
- Stamp the build like `gamen-validate` (`Validate/BuildInfo.lean`, the
  `version` action) so `tools/install.sh` can install it too; extend
  `install.sh` and its printed hints (a `dcleg-service` line for
  gamen-simulations). A Lean-only `version` op is a protocol extension, so
  give it a version field and keep it out of the comparison.

## Things that will go wrong if not said

- **State.** The service is stateful: a registry `IORef (Map Handle
  DclegModel)`, single-threaded. Model it with `IO.Ref`. `build` hardening
  (task 18) is about what `build` rejects; those errors and their codes must
  match.
- **Errors stay errors**, per `CLAUDE.md`: no `panic!`, no `.getD` to reach an
  answer, in the library or the tests. `error` → `Except`.
- **Laziness: match outputs, not evaluation order** (`CLAUDE.md`), but note
  which request errors surface when several would.
- **Byte compatibility** includes error message text and error codes, not just
  successful results. Check `enumerate_counterfactuals` output order.
- **Seeds / nondeterminism:** if any op depends on a random choice, find it
  before comparing; the comparison must be reproducible.
- **Cite** thesis/B&D definition numbers only after checking the PDF
  (`notes/dcleg-edition.md` pins the DCLEG edition).

## Verification

1. `lake build`, `lake test` green; `lake exe slowtests` if a prover was
   touched (it should not be).
2. Plant a logic bug in the service; confirm a test fails; revert. Plant an
   `Except` that throws; confirm the expected-false cases fail too; revert.
3. `tools/compare/compare_dcleg.py` (new; modeled on `compare.py`): session
   scripts of requests, so that registry state is exercised (`build`, then
   `sat`/`true_in`/`counterfactual`, `drop`, `list`, `info`), plus error
   cases (malformed JSON, unknown op, invalid models). Needs the gamen-hs
   `dcleg-service` binary; it is already built (checked 2026-10-05) under
   `~/Projects/Logic/Haskell/gamen-hs/dist-newstyle/build/*/ghc-*/gamen-*/x/dcleg-service/build/dcleg-service/dcleg-service`
   (rebuild with `cabal build dcleg-service` in gamen-hs if it goes stale). Report the
   disagreement count and classify each.
4. A before/after on gamen-simulations is *not* part of this port; it is Phase
   1.3 of the migration plan (its own session, Brian's OK first).

## Who and how

- **Porter: Opus.** The agent file `.claude/agents/module-porter.md` says
  `model: sonnet`; override it with `model: "opus"` on the Agent call. That
  agent is written for one `src/Gamen/<Module>.hs` module at a time, so the
  prompt below tells it which parts differ.
- **Reviewer: `module-reviewer`, blind** (give it the branch and module name,
  not the porter's report).
- Run the porter in a worktree (`isolation: "worktree"`). It must start with
  `git merge --ff-only main`; `main` now includes the DclegProofs merge.
- When the run starts, set the `PORTING.md` Porter column on the
  `protocol/Service/*` row to `opus`.

### Porter prompt

> Port gamen-hs's dcleg service to Lean per `plans/dcleg-service-port-2026-10-05.md`
> (read it first, then `CLAUDE.md`). This is not a `src/Gamen/<Module>.hs`
> module: the sources are `protocol/Service/{Protocol,Formula,Model,Axioms}.hs`
> and `service/Main.hs` in `~/Projects/Logic/Haskell/gamen-hs`, and the
> spec is `notes/dcleg-service-protocol.md`. Deliver the `dcleg-service`
> executable, `Gamen/Service/*`, the port of the 5 skipped "task 18"
> `RegressionIssue18` tests, `tools/compare/compare_dcleg.py`, and the
> `PORTING.md` updates. Use your standard report block; for "Haskell its,
> spec" use `test/DclegServiceSpec.hs` and `test/RegressionIssue18.hs`.

### Reviewer prompt

> Review branch `<branch>`, module "dcleg service (`Gamen.Service.*`,
> `service/Main.hs`)", against gamen-hs. Check byte compatibility of
> responses and error text, the registry semantics, and that every skipped
> test is accounted for.

## Stop and ask Brian before

- merging;
- installing `dcleg-service` on `PATH`;
- touching gamen-simulations or any other downstream repository;
- changing an existing `gamen-validate` response.
