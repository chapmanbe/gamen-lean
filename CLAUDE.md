# gamen-lean — Claude Code instructions

The Gamen modal logics in Lean 4, plus teaching notebooks that replace the
Gamen.jl Pluto notebooks. Brian Chapman and Jeremiah Chapman.

**gamen-lean is the primary implementation** (decided 2026-09-29). It began
as a port of [gamen-hs](https://github.com/chapmanbe/gamen-hs)
(`~/Projects/Logic/Haskell/gamen-hs`), and every library module was ported
by 2026-09-29. gamen-hs is now frozen: new logics, features and bug fixes
happen here, and are not mirrored back to Haskell. Port history and status
by module: `PORTING.md`. Why Lean, and the evidence: `docs/assessment/`.
Forward plans: `plans/*-2026-09-29.md`.

**"What's next?"**: read `NEXT.md` and answer from it. If it has a
"Start here" section, give that section's steps in order, with the exact
commands and file paths, and check the first one (the current branch)
before going further. Don't summarize the open-threads list unless asked.

## Build

- `lake build`: library, widgets, notebooks, `gamen-validate`
- `lake test`: unit, widget, answer-key, and property tests
- `lake exe slowtests`: slow property cross-checks (~10 min); run after
  touching Tableau, Semantics, RankingTheory, or the DeonticStit prover
- `python3 tools/compare/compare.py`: compatibility check against gamen-hs's
  `gamen-validate` for the existing request types (build both first). Any
  disagreement must be a known, intentional divergence listed in
  `tools/compare/intentional-divergences.md`; anything else is a
  regression.
- Toolchain pinned in `lean-toolchain` (4.34.0); Plausible and ProofWidgets
  pinned to the matching tags in `lakefile.toml`. Upgrade all three together.

## Conventions

- **Fix bugs here, don't copy them.** Until 2026-09-29, bugs found while
  porting were filed on gamen-hs and copied faithfully until fixed there.
  Now a bug inherited from gamen-hs is fixed in Lean directly, with a test.
  If the fix changes `gamen-validate` output for an existing request, add it
  to `tools/compare/intentional-divergences.md`. File issues on gamen-lean
  (`gh issue create -R chapmanbe/gamen-lean`), not gamen-hs.
- **One Lean module per gamen-hs module**, same name (`Gamen.Tableau` ↔
  `src/Gamen/Tableau.hs`), so the two can be read side by side. Keep the
  Haskell function names in lowerCamelCase; constructors are lowerCamelCase
  (`.box`, `.stit`).
- **Cite B&D definition numbers** in docstrings, and check them against the
  PDF (`notes/bd-screen.pdf`, `pdftotext`), never from memory.
  B&D is revised continually: unqualified citations mean the edition pinned
  in `notes/bd-edition.md` (Fall 2025, the same as gamen-hs). Check the
  PDF's SHA-256 against that file first, and name any other edition explicitly. Ch. 1:
  model = Def 1.6, truth at a world = 1.7, truth in a model = 1.9,
  validity = 1.11, entailment = 1.23.
- **`error` becomes `Except`, not `panic!`.** Lean's `panic!` logs and then
  *continues with a default value*, turning a crash into a silent wrong
  answer. gamen-hs has ~185 `error` calls; convert each to `Except` (or
  prove it unreachable).
- **No `partial def` in the library** unless unavoidable; say why in the
  docstring when it is. Recursion on subterms is automatic. Search loops get
  explicit fuel (gamen-hs's step budgets become the fuel). Recursion through
  `immediateSubformulas` uses `Formula.sizeOf_lt_of_mem_immediate`.
- **When termination forces a rewrite, keep the results identical** and add
  a property test that checks it (see the `toNNF` note in `Formula.lean`).
- **No `sorry`** in committed code.
- **Laziness: match outputs, not evaluation order.** Don't mimic Haskell's
  laziness; match its results *and errors*. It matters in two places.
  First, `Epistemic.hs` ~148–158: the per-announcement table of restricted models
  is built lazily, so a restriction (which evaluates the announcement body
  at every world, and can error) runs only when `[B]C` is reached. A literal
  strict translation that builds the table up front would raise errors
  gamen-hs never raises (e.g. `p ∧ [B]C` with `p` false). Restrict on
  demand instead; add a cache filled on first use only if speed demands
  it, with a property test against the uncached version. Second, set-valued
  model checkers (`Atl.ModelCheck.sat`, `Atel.atelSat`): `Data.Set`'s
  `intersection ∅ x` and `difference ∅ x` return ∅ without evaluating `x`,
  so `sat (⊥ ∧ □p)` is ∅ in gamen-hs, not an unsupported-operator error.
  Evaluate the second operand only when Haskell would; `union` forces both,
  its *second* argument first, so when both sides error gamen-hs reports
  the right one (`Or`, `Implies`, `Iff`). Match which error surfaces, not
  just whether one does. Check any new set-algebra port against GHC. Everywhere else, strict
  evaluation is safe.
- **Pairs as keys**: Lean core has no `Ord (α × β)` instance; use
  `attribute [local instance] lexOrd` (see `Tableau.lean`).
- **Shared relation checks live in `Kripke.lean`.** gamen-hs writes
  reflexive/symmetric/transitive checks four times (FrameProperties,
  `Kripke.isEquivalenceOn`, `Stit.isTransitiveOn`,
  `Temporal.isTransitiveFrame`). Lean has one copy, on (worlds, successor
  map), in `Kripke.lean`; each module keeps its Haskell-named function as a
  one-line wrapper so the side-by-side reading still works.
- **One fixpoint helper, with fuel.** gamen-hs iterates "until nothing
  changes" in six places (`lfp`, `gfp`, `transitiveClose`, `euclideanClose`,
  `largestBisimulation`, `Laca.trajectory`), none bounded. Port them all
  through one shared helper that takes fuel and returns `Except`: running out
  of fuel is an error, never a default. Document the bound (`|U| + 1` for
  monotone iteration in a finite universe `U`, `|W|² + 1` for relation
  closures). `partial_fixpoint` counts as `partial def`.
- Before porting a general-purpose helper, check
  `docs/assessment/lean-library-reuse-2026-09-23.md`: most of Lean's
  library versions are proof-only definitions, and the few executable ones
  must keep gamen-hs's order and output.
- **Keep existing requests compatible.** Downstream projects (cwyde,
  patient-agent-assistant, guideline-cds-simulation) may still call a
  `gamen-validate` binary. For the existing request types, output stays
  byte-identical to gamen-hs except for listed intentional divergences. Run
  `tools/compare/compare.py` after touching `Protocol.lean`, `Validate.lean`
  or any prover. New capabilities are Lean-only protocol extensions (new
  fields or actions, with a version field), out of scope for `compare.py`.
- Domain knowledge lives in data, not code (Buchanan's separation
  principle); domain axioms come from authoritative sources, never LLMs.

## Verification discipline

- Port a module's tests with the module, including the relevant
  `PaperCorrespondence` sections.
- Before trusting a green run, plant a bug and confirm a test catches it.
- Everything in `docs/assessment/` is a dated record; add to it, don't
  rewrite it.

## Widgets and notebooks

- `Widgets/KripkeExplorer.lean` is built on ProofWidgets `InteractiveSvg`.
  Two non-obvious constraints, both pinned at ProofWidgets v0.0.111:
  - the RPC method must be named exactly `updateSvg` at the root (the
    prebuilt JS calls it by name), so there is one explorer state type;
  - handle clicks on **mouseup**: the server records the pressed element
    only after processing mousedown. The widget tests replay the real event
    order; rerun them after any ProofWidgets upgrade.
- `Widgets/js/interactiveSvgQuiet.js` is generated by `make-quiet.sh` from
  the pinned ProofWidgets release (Apache-2.0; debug line removed).
- Notebooks: prose in `/-! … -/`, formulas in `ml[ … ]`, answers graded by
  `#eval` (`grade`, `gradeFormula`), and machine-checked claims via
  `native_decide`. `decide` does not work on the Kripke semantics
  (well-founded recursion, `TreeSet`). `Gamen.ManyValued` is the
  exception: it was built for `decide` (structural recursion, no `TreeSet`),
  so its claims are kernel-checked. Design new modules that way when you
  can. Axiom audits must be allowlists (`propext`, `Classical.choice`,
  `Quot.sound`): at Lean 4.34, `native_decide` shows up as
  `<thm>._native.native_decide.ax_…`, not `Lean.ofReduceBool`.
- Every stated answer in a ported notebook goes into the answer-key tests.

## Web editor (`web/`)

Local prototype only. On macOS Lean runs unsandboxed, and lean4web's stock
`npm start` serves to the whole network: always use `web/run-local.sh`,
which binds to 127.0.0.1. Never start lean4web any other way on a laptop.
