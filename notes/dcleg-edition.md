# Pinned version of the DCLEG draft

`Gamen.Dcleg` ports gamen-hs's `src/Gamen/Dcleg.hs`, which implements
Jeremiah Chapman, *Doxastic Conditional Logic of Extensive Games* (v5.0),
University of Gothenburg, April 2026, supervised by Martin Kaså.

**Two versions are pinned.** Until the citation migration is done, every
unqualified "Chapman (2026)" or "DCLEG" citation in gamen-lean still means
the **v5.0 draft**, because that is what `Gamen.Dcleg` was ported against.
The **final thesis** (below) supersedes it. A consistency check (2026-09-30)
compares the two and the implementation. Once it maps the citations,
unqualified citations will mean the final thesis, and v5.0 citations will
be named explicitly ("DCLEG v5.0, §2.7").

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
