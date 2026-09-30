# Pinned versions of DCLEG

`Gamen.Dcleg` ports gamen-hs's `src/Gamen/Dcleg.hs`, which implements
Jeremiah Chapman, *Doxastic Conditional Logic of Extensive Games* (v5.0),
University of Gothenburg, April 2026, supervised by Martin Kaså. DCLEG is
Chapter 3 of his final thesis (June 2026), which the citations now follow.

**Two versions are pinned.** Unqualified "Chapman (2026)" or "DCLEG"
citations in gamen-lean mean the **final thesis** (below), with its
**printed** page numbers. Citations to the April 2026 draft name it
explicitly: "DCLEG v5.0, §2.7". `Gamen.Dcleg` was ported against v5.0;
its citations were migrated on 2026-09-30, following the map in
`docs/assessment/dcleg-final-vs-implementation-2026-09-30.md` §3:

* v5.0 §1.x → final §3.1.x; v5.0 §2.1–2.6 → final §3.2.1–3.2.6. Conditions
  keep their numbers and names.
* v5.0's `beg`, `fin`, `Mv` are the final thesis's `start`, `end`,
  `Move` (same definitions). Lean identifiers keep their names, except the
  test-local `dclegEnd`/`dclegStart`.
* v5.0's §2.7 (Table 1, "Some Validities") and §2.7.1 have no counterpart
  in the final thesis. The tests that check Table 1 are kept, labeled
  "DCLEG v5.0 Table 1 (not in the final thesis)".
* Counterfactual K′ (final §3.2.4, p. 22) is
  (B_i(φ □→ ψ) ∧ B_i φ) □→ B_i ψ. v5.0 had ψ as the consequent, which is
  not valid (the 2026-09-30 report gives a countermodel). The semantics are
  otherwise unchanged.

## Final thesis (2026-06-04)

| | |
|---|---|
| Title | *Doxastic Conditional Logic, Rationality, and Backward Induction: Formalizing Belief and Counterfactual Reasoning in Games* |
| Degree | Thesis for the Master's degree in Logic (30 credits), University of Gothenburg; supervisor Martin Kaså |
| Date | June 4th 2026 (title page); PDF created 2026-06-15; 64 pages |
| File | `notes/dcleg-thesis-final.pdf`, **untracked**: not added to git yet, by Brian's instruction (2026-09-30); GUPEA publication pending |
| SHA-256 | `e4828132a4333cf6d629ba327c460714bd6a577362db6dbce0d4fa713fe86c88` |
| DCLEG | Chapter 3 (§3.1 syntax, §3.2 semantics; v5.0's §1–2) |
| Proved results | Lemma 4.1, Theorem 4.2 (Ch. 4, backward induction); Theorem 5.1, Lemma 5.2 (Ch. 5, conditioned dominance) |

PDF page indices (e.g. Lemma 4.1 on PDF p. 35) differ from the printed page
numbers. Cite the printed ones.

## v5.0 draft (April 2026)

| | |
|---|---|
| Version | v5.0 (April 2026), 13 pages |
| Source | `gamen-hs/notes/DCLEGv5.tex` (tracked in gamen-hs, which is private) |
| PDF | `gamen-hs/notes/DCLEGv5.pdf` (gitignored in gamen-hs) |
| SHA-256 (tex) | `73fa60abc9b644c8618debc7b8e9072d019ad031cadf926927a66ccb38cff480` |
| SHA-256 (pdf) | `4eab3e10df7abf503a99594e554537e2d6fca20f679e40926ca9d5b96059239b` |

The draft isn't copied here because it is unpublished work. Pin it by hash;
copy it only when the final version is public, or with Jeremiah's agreement.

## Checking your copy

```sh
shasum -a 256 ~/Projects/Logic/Haskell/gamen-hs/notes/DCLEGv5.{tex,pdf}
```

The draft has 13 pages and states its validities with short justifications.
The hand proofs are in the full thesis, which isn't in either repository.
