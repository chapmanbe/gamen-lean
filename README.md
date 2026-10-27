# gamen-lean

A Lean 4 port of [gamen-hs](https://github.com/chapmanbe/gamen-hs), a
framework for modal, temporal, epistemic, deontic, and STIT logic with
applications to clinical guideline validation, together with interactive
teaching notebooks that follow *Boxes and Diamonds*
([bd.openlogicproject.org](https://bd.openlogicproject.org)).

Named from Old English *gamen* (game, sport, joy).

**Status.** gamen-lean is the primary implementation of the Gamen logics
(since 2026-09-29). Every gamen-hs library module is ported, gamen-hs is
frozen, and new logics are added here. For the request types gamen-hs
supports, `gamen-validate` answers identically to gamen-hs, apart from the
divergences listed in `tools/compare/intentional-divergences.md`. See
[`PORTING.md`](PORTING.md) for the module-by-module record.

**Documentation:** [chapmanbe.github.io/gamen-lean](https://chapmanbe.github.io/gamen-lean)
has the API reference and read-only copies of the notebooks.

## Statement of need

Modal logics for knowledge, obligation, time, agency and strategic ability
are usually taught on paper and studied in separate tools, one logic at a
time. gamen-lean puts them in one executable Lean 4 library: Kripke
semantics and tableau provers for the *Boxes and Diamonds* systems, and
temporal, epistemic, doxastic, deontic, STIT, ATL and dynamic logics, each
checked by tests against its source paper. It serves two groups. Students,
especially in health informatics, work through notebooks where a clinical
rule becomes a formula they can evaluate, a model they can click, and an
answer the notebook grades. Researchers and applications call
`gamen-validate`, a JSON Lines service that clinical guideline validation
uses to detect conflicting obligations. gamen-lean succeeds gamen-hs
(Haskell) and Gamen.jl (Julia).

## Build

Install [elan](https://lean-lang.org/install), then:

```sh
lake build     # library, widgets, notebooks, gamen-validate
lake test      # unit, widget, notebook answer-key, and property tests
```

## Layout

| Path | Contents |
|---|---|
| `Gamen/` | The library: one module per gamen-hs module |
| `Validate.lean` | `gamen-validate`, the JSON Lines service used by guideline-validation, guideline-cds-simulation, patient-agent-assistant, and cwyde |
| `Widgets/` | Infoview widgets for the notebooks (clickable Kripke models, hints) |
| `Notebooks/` | Teaching notebooks ported from the Gamen.jl Pluto notebooks |
| `DclegProofs/` | Machine-checked proofs from the DCLEG thesis (Chapter 3 semantics, Lemma 4.1, Theorem 4.2, Theorem 5.1, Lemma 5.2); Prop-level, no Mathlib. Start at its `README.md` |
| `Tests/` | The test suite |
| `tools/compare/` | Side-by-side comparison of the gamen-hs and Lean `gamen-validate` |
| `web/` | Local web editor (lean4web) for the notebooks |
| `docs/assessment/` | The 2026-09-23 feasibility study that chose Lean |

## Notebooks

Open a file in `Notebooks/` in VS Code with the Lean 4 extension and put the
cursor on an `#eval` or `#html` line; results and diagrams appear in the
infoview. Or run them in a browser: `web/setup.sh` once, then
`web/run-local.sh` (localhost only; see `web/README.md`). To read them
without installing anything, see the
[read-only copies](https://chapmanbe.github.io/gamen-lean/notebooks/) on the
documentation site, with every result computed by Lean.

For health informatics students with no logic background, two notebooks
start from clinical rules: `PropLogicPrimer.lean` (truth tables, validity,
entailment) and then `ThreeValued.lean` (missing data, strong Kleene logic,
and why a CQL criterion can be null).

![Clicking a fact onto a world updates the guideline checks](docs/images/gamen-lean-widget-click-test.gif)

## How to cite

If you use gamen-lean, please cite it using the metadata in
[`CITATION.cff`](CITATION.cff). GitHub's "Cite this repository" button
produces APA and BibTeX from that file.

## Contributing

Bug reports, questions and pull requests are welcome on
[GitHub](https://github.com/chapmanbe/gamen-lean/issues). Before opening a
pull request, run `lake build` and `lake test`; both must pass. A bug fix
comes with a test that fails without it. The project's conventions (no
`sorry`, errors as `Except` rather than `panic!`, *Boxes and Diamonds*
definition numbers in docstrings checked against the text) are in
[`CLAUDE.md`](CLAUDE.md).

## License

MIT. `Widgets/js/interactiveSvgQuiet.js` is derived from ProofWidgets4
(Apache-2.0); see `Widgets/js/make-quiet.sh`.
