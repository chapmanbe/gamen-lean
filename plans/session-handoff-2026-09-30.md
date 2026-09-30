# Implementation Plan: continue gamen-lean after the port (session handoff)
*Written 2026-09-30 at the close of a long design and implementation session.
Read this once; it indexes the detailed plans, which you read only for the
thread you pick up. Supersedes `plans/porting-handoff-2026-09-28.md`, which
is now history.*

## Objective

The gamen-hs → Lean library port is complete. gamen-lean is now the primary
implementation. Pick up **one** of the open threads below, implement it
against its own plan, and get Brian's approval before merging. Done for a
thread means: its plan's "Done when" is met; it was reviewed independently
(a blind reviewer, planted checks); `lake build` and `lake test` pass on
`main`; and Brian approved the merge.

## Where things stand (snapshot, 2026-09-30; verify with `git log`)

**gamen-lean:**
- `main` is at `e2a3749`, **pushed**. `lake test` passes 1188/1188.
- Every gamen-hs library module is ported, including Visualize. See
  PORTING.md for the rest.
- Untracked, deliberately: `notes/dcleg-thesis-final.pdf`, Jeremiah's final
  thesis, which isn't added to git yet by Brian's instruction.

**Lean guideline-validation port** (`~/Projects/Logic/Lean/guideline-validation`,
remote `chapmanbe/guideline-validation-lean`): `main` is at `22cadaf`,
pushed, with Phase 1 (honest timing reporting) merged. Its untracked
`.claude/` directory isn't ours.

**Kept on purpose; don't merge or delete:**
- **Branch `dcleg-proofs-draft`** (`1db8e7e`), checked out as a git worktree
  at **`~/Projects/Logic/gamen-lean-dcleg-proofs/`**.
  - It holds `DclegProofs/`, the Lean formalization of the thesis proofs
    written for Jeremiah: `README.md`, `FINDINGS.md`, `Semantics.lean`,
    `Basics.lean`, `Q12Example.lean`, and one file per result
    (`Lemma4_1`, `Theorem4_2`, `Theorem5_1`, `Lemma5_2`).
  - It's reviewed and correct, but **Brian will merge it only after
    talking with Jeremiah.**
  - Backup: `~/Backups/dcleg-proofs-draft-2026-09-30.bundle`, verified by
    a test restore. Make a fresh bundle after any new commits.

## Decisions (do not relitigate)

**Direction:**
- **gamen-lean is primary; gamen-hs is frozen** (2026-09-29): Lean has
  implemented every logic. New logics, features and fixes happen here only.
  See CLAUDE.md.
- **Fix inherited bugs here, don't copy them.** File issues on gamen-lean.
  Mark every changed gamen-hs expectation in a test as "deliberate
  divergence from gamen-hs". CLAUDE.md "Conventions".
- **`compare.py` is a compatibility check, not the contract.**
  Disagreements must be listed in
  `tools/compare/intentional-divergences.md` (#1 is gamen-hs#41).
  Existing requests stay byte-compatible so the binary can replace
  gamen-hs's.
- **New capabilities are Lean-only protocol extensions,** with a version
  field. Don't mirror them to gamen-hs (D2, resolved).
- **All downstream projects migrate to gamen-lean,** following
  `plans/downstream-migration-2026-09-29.md`.
- **JOSS targets gamen-lean.** Its 6-month public-history clock starts when
  gamen-lean goes public; see `~/Code/notes/publication-plan.md`.

**Sources and pins:**
- **References that drive the implementation live in gamen-lean,** in
  `references/` (D1).
- **The B&D PDF is committed** in `notes/`, pinned (Fall 2025, SHA in
  `notes/bd-edition.md`); its license is recorded there.
- **DCLEG citations mean the final thesis,** with printed pages; v5.0 is
  cited as "DCLEG v5.0". The map is in
  `docs/assessment/dcleg-final-vs-implementation-2026-09-30.md`.

**Lean discipline:**
- **Axiom audits are allowlists** (`propext`, `Classical.choice`,
  `Quot.sound`). At Lean 4.34, `native_decide` appears as
  `<thm>._native.native_decide.ax_…`, not `Lean.ofReduceBool`.
- **Design new modules for `decide`** (structural recursion, no `TreeSet`)
  when you can; `Gamen.ManyValued` is the model.

**DCLEG:**
- **Outcome-node premises** (merged `f6ce8b3`; roll back with
  `git revert -m 1 f6ce8b3` if Jeremiah prefers a different F):
  - the default F at an outcome node is one *arbitrary admissible* choice,
    {{(γ,w)}, all worlds reaching w};
  - the validator checks Centering and Contemporary Universality at every
    reached pair;
  - validities are tested over random admissible F.

  Rationale: `docs/dcleg-outcome-node-premises-2026-09-30.md`. Jeremiah's
  point, adopted: "unspecified" ≠ "no premises".
- **Findings about the thesis are neutral and classified,** each as a
  typo, reading-dependent (Q#), missing step, or proof gap. Nothing goes to
  Jeremiah without Brian. `FINDINGS.md` separates "safe to raise now" from
  "waits on his answers".

**Process:**
- **Nothing waits on students;** an agent walkthrough stands in. Record it
  in `docs/assessment/`.
- **Every change gets:** a porter in a worktree, a blind reviewer in its
  own checkout (Opus, plus Fable for the hard ones), planted checks, a fix
  round, and then a merge only with Brian's approval.

## Architecture: the open threads and their plans

| Thread | Plan (read only if you pick it) | State | Next step |
|---|---|---|---|
| Guideline-validation logic | `plans/logic-for-guideline-validation-2026-09-29.md`; Phase 2 spec/plan in `docs/superpowers/` (2026-09-30) | Phase 1 merged. **Phase 2 merged 2026-09-30**: `Gamen.ManyValued.Completion` (theorems 1–6, gamen-lean `3f1127d`) and the port's `validate-guidelines applicability` (port `c6c0a54`); 7 hand-written patients × 20 conflicts: 36 definite, 64 possible, 40 absent, 0 over-warnings | **Brian approves the 4 draft definitions**: read the port's `docs/applicability-definitions-review.md` (R18 and Rec 3.3.1.1 add "adults"; potassium limited to CKD, RASi part from PP 3.6.3; phosphate limited to G3a–G5; G5D counted as G5). Then a clinician sample before any paper claim |
| Three-valued teaching | `plans/three-valued-logic-2026-09-29.md` | **Done 2026-09-30** (merged `820fc3a`): `Notebooks/PropLogicPrimer.lean`, `Notebooks/ThreeValued.lean`, `Widgets/TruthTable.lean`, answer keys in `Tests/ManyValuedNotebooks.lean`. Blind review and Fable novice walkthrough done, with one fix round (`docs/assessment/three-valued-*-2026-09-30.md`) | Optional: check the tables render in the VS Code infoview; ask Brian before raising the FHIRPath `implies` note/table conflict with HL7 (Jira not searched) |
| K tableau soundness | `plans/countermodel-explorer-and-k-soundness-2026-09-29.md` Part B | Part A (countermodel explorer) merged | B0 spike on derived `Ord` lawfulness |
| Edition-proof citations | same plan, Part C | not started | `tools/bd/citations.py` index/check/migrate. Now also covers DCLEG citations |
| DCLEG thesis verification | `plans/dcleg-thesis-verification-2026-09-29.md` | Proofs draft on `dcleg-proofs-draft` (see above). An F-condition validator and a random admissible-F generator exist in `Gamen/Dcleg.lean` and the tests | **Wait for Brian's talk with Jeremiah.** Then: his answers to Q1–Q18 (especially Q12 and Q13), then finish Lemma 4.1, Theorem 4.2, Lemma 5.2 and Theorem 5.1 |
| Downstream migration | `plans/downstream-migration-2026-09-29.md` | **Phase 0a/0b done 2026-09-30** (merged): the Lean-only `version` action (commit stamped at compile time in `Validate/BuildInfo.lean`; `enableArtifactCache = false` in `lakefile.toml` keeps Lake's shared cache from restoring another commit's stamp) and `tools/install.sh`, which copies the binary to `~/.local/share/gamen-lean/` and puts it on PATH only with `--link` (`~/.local/bin` is already on PATH, so linking switches every caller at once). Also fixed gamen-lean#1 (flat decoder guessed on unknown `op`/`temporal_op`; port of gamen-hs#60), found by `compare.py` | Migrate guideline-validation (set `GAMEN_VALIDATE_BIN` to the installed copy; a session in that repo, with Brian's approval), then cwyde (`CWYDE_GAMEN_BIN`). `tools/install.sh --link` only after both are verified. Blocked beyond that: gamen-simulations needs the `dcleg-service` port (0c) |

## Interfaces / contracts

- **`gamen-validate`:** existing request types are byte-compatible with
  gamen-hs, except for the listed divergences. Compare against gamen-hs
  `main` (`fd8b269`): the only disagreements are divergence #1's 103. The
  Lean-only `version` action answers
  `{"ok":true,"result":{"commit":…,"implementation":"gamen-lean","protocol":1}}`
  (keys alphabetical, as Lean's `Json.compress` writes them).
- **The DCLEG premise function:** `withMovePremises` gives decision nodes
  one premise per move plus {(γ,w)}, and outcome nodes the two-premise
  system above. `validateDclegModel` returns `[]` iff the model is
  admissible, among other checks.
- **The formal DCLEG semantics** (in `DclegProofs`) is separate from the
  executable one. There, F is an arbitrary admissible parameter.

## Constraints

- All of CLAUDE.md applies. In particular: no `sorry`; no `partial def`
  without a stated reason; `Except`, not `panic!`; cite B&D and DCLEG
  against the pinned PDFs; American English.
- **The canonical guideline-validation repository is read-only** for agents
  (`~/Projects/Logic/Julia/guideline-validation`). Changes in downstream
  repositories need Brian's approval, one session per repository.
- **Don't commit the thesis PDF.** Don't quote large passages of the thesis
  (it's unpublished).

## Non-goals / rejected alternatives

- **Updating gamen-hs** (new logics, fixes, PRs): rejected, since gamen-hs
  is frozen.
- **One big logic for guideline validation:** rejected in favor of
  decidable layers, each proved sound in Lean (literature report
  `references/logic-for-guideline-validation-2026-09-29.md`).
- **Metric temporal logic, UPPAAL:** a poorer fit, because they model
  processes, not obligation sets.
- **Mathlib in gamen-lean:** not added. The proofs so far don't need it. If
  they ever do, use a separate package.
- **A blocklist-style axiom audit:** rejected, because it misses
  `native_decide`.

## Open questions for the implementer

- [ ] **Brian's decisions:**
  - when to make gamen-lean public;
  - what to do with gamen-hs (archive it, and its open PRs #44, #56–#58);
  - whether and how to share `FINDINGS.md` and
    `docs/dcleg-outcome-node-premises-2026-09-30.md` with Jeremiah;
  - Phase 2's patient-fact source (fixtures proposed).
- [ ] **Jeremiah's answers:**
  - Q1–Q18 in `DclegProofs/Semantics.lean`;
  - the three questions at the end of the outcome-node write-up.
- [ ] **Stale claims:** `~/Projects/Logic/CLAUDE.md` says
  guideline-cds-simulation and patient-agent-assistant call
  `gamen-validate`. Neither was found to (see the migration plan's
  inventory). gamen-simulations is missing from its project table.
- [ ] **Housekeeping:** a stale lean4web `nodemon` process (pid 10887,
  from `gamen-roc/sketches`, started Sept 23) serves nothing. Brian may
  kill it.
- [ ] **Lake's shared artifact cache** holds entries a reviewer agent
  wrote from a scratch copy, stamped with a commit that exists nowhere
  else. gamen-lean no longer reads the cache, but other projects might.
  Brian to delete, under
  `~/.elan/toolchains/leanprover--lean4---v4.34.0/lake/cache/`:
  `artifacts/{20f4a01cacdbb3c6.olean,327f6e9ba58ade39.c,5516e1a25897b132.o,acee21cabbec8663}`
  and `outputs/gamen/{6c5edf91c6782ab3,059682ff6733f6dd,bb9345f3b77a0a02}.json`.
- [ ] **The draft limitation paragraph** in the Lean GV port,
  `docs/notes/timing-limitation-draft.md`, awaits Brian's review before
  any manuscript use.

## Task list (ordered by what's unblocked now)

1. **Ask Brian which thread to pick up.** Only the DCLEG proofs are waiting
   on him and Jeremiah; everything else is unblocked.
2. **Migration Phase 0a/0b: done 2026-09-30.** If he doesn't say: migrate
   guideline-validation to the installed Lean binary (its own session, in
   that repository, with Brian's approval).
3. **Guideline-validation Phase 2: done 2026-09-30.** Waiting on Brian's
   approval of the draft definitions (see the table above). Follow-ups:
   `plans/gv-phase2-followups-2026-09-30.md`.
4. **The three-valued notebooks: done 2026-09-30** (`820fc3a`).
5. **Part C, citation tooling:** it catches wrong B&D and DCLEG citations
   at test time.
6. **Part B0,** the soundness spike.
7. **The `dcleg-service` port** (migration 0c), as a `/port-module`-style
   run with Opus.

## Suggested implementer model

- **Lean library and proof work** (Part B, the DCLEG proofs, Phase 2's
  proofs): **Opus or Fable.** Lean fails loudly, but a wrong definition
  type-checks fine, so faithfulness is where silent errors hide.
- **Plumbing and data** (migration 0a/0b, Phase 3's FHIR mapping,
  citation tooling): **Sonnet**, with an Opus reviewer.
- **Notebooks for novices:** **Opus** to write, then a **Fable** novice
  walkthrough.
