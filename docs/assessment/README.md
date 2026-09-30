# Feasibility assessment (2026-09-23)

The study that led to this repository, written in the exploratory
`gamen-roc` directory and copied here as a dated record. Paths such as
`sketches/lean/…` in these files refer to that directory; the code they
describe now lives at this repository's root (`sketches/lean/Gamen/` →
`Gamen/`, `sketches/compare/` → `tools/compare/`, `sketches/web-projects/`
→ `web/projects/`).

| File | Contents |
|---|---|
| `feasibility-assessment.md` | Feature inventory of gamen-hs; Roc, Gleam, Lean 4, OCaml, F#, Rust, and others compared; Lean slice test (Part 4); protocol port and side-by-side comparison (Part 5) |
| `haskell-vs-lean4.md` | Which is easier to learn, for this project and these two people |
| `interactive-materials-lean4.md` | Lean vs. Pluto for teaching; review of an external comparison; prototype results |
| `compare-summary-2026-09-23.txt` | Side-by-side baseline: 3,653 requests, 0 disagreements |
| `compare-mutation-no-D-rules-2026-09-23.txt` | Same run with the D rules removed: 88 disagreements (the harness works) |

Later records, written in this repository:

| File | Contents |
|---|---|
| `lean-library-reuse-2026-09-23.md` | Which Lean library definitions the port can reuse, and why most cannot |
| `bug-provenance-2026-09-26.md` | Where the bugs found during waves 2–3 and the cross-checks came from: the language, the port, mechanical checks, or an independent oracle |
| `bd-source-anchors-2026-09-29.md` | Whether the Open Logic sources give B&D citations anchors that survive renumbering: label coverage, 2019→2026 stability, why numbers can't be computed from source |
| `novice-walkthrough-ch6-countermodels-2026-09-29.md` | An agent standing in for a novice student works through the Ch. 6 countermodels notebook (no students available) |
| `dcleg-final-vs-implementation-2026-09-30.md` | DCLEG v5.0 draft vs. the final thesis (Ch. 3), item by item; which meaning `Gamen.Dcleg` implements; a citation map to the final thesis; Ch. 4–5 gaps; gamen-hs#53 under the final thesis |
