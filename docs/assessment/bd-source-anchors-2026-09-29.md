# Stable anchors for B&D citations in the Open Logic sources (2026-09-29)

**Question.** *Boxes and Diamonds* (B&D) renumbers its definitions and
theorems between editions. Epistemic logic was Chapter 13 in Fall 2019 and
is Chapter 15 in Fall 2025. Do the LaTeX sources carry identifiers that
survive renumbering, so that our citations can follow the book from one
edition to the next?

**Answer.** Partly.
- The labels that exist are very stable. None of the modal-logic labels
  changed between 2019 and our pin, apart from one rename of the part tag.
- Fewer than half of the numbered statements have a label, and definitions
  (what we cite most) mostly don't.
- The printed numbers can't be recomputed from the source alone.

## Where B&D comes from

- **The build repository is `rzach/boxes-and-diamonds`.** Its `bd.tex`
  imports OpenLogic content (`OpenLogicProject/OpenLogic`):
  - whole parts: `normal-modal-logic`, `counterfactuals` and
    `applied-modal-logic`;
  - four `intuitionistic-logic` chapters: introduction, semantics,
    soundness-completeness and tableaux;
  - appendix material from the sets, propositional-logic and
    first-order-logic parts.
- **Both revisions printed on our pinned PDF's copyright page exist
  upstream** (`notes/bd-edition.md`):
  - B&D `f3673b5`, dated 2025-07-01;
  - OpenLogic `0a18d37`, committed 2026-02-17T04:04Z (2026-02-16 in
    local time, as printed).
- **Every section file declares an ID,** `\olfileid{part}{chapter}{section}`,
  e.g. `\olfileid{nml}{tab}{sou}` for normal modal logic → tableaux →
  soundness. Some statements carry `\ollabel{kind:name}` inside that
  scope, so B&D Theorem 6.6 is `nml:tab:sou:thm:tableau-soundness`.

## Findings

All counts are over the OpenLogic content B&D imports (the four parts
above), at the pinned revision `0a18d37`, unless stated otherwise.

1. **Label coverage** counts a label anywhere inside the statement, and
   excludes Problems, which have their own counter.

   | Kind | Labeled |
   |---|---|
   | Theorem | 19 / 23 |
   | Lemma | 7 / 8 |
   | Corollary | 11 / 14 |
   | Proposition | 42 / 69 |
   | Definition | 20 / 85 |
   | Example | 7 / 27 |
   | All | 106 / 226 |

   Unlabeled examples we already cite or plan to:
   - Definitions 6.3 and 6.4 (interpretation of prefixes; satisfiable
     sets of prefixed formulas), both in `nml:tab:sou`;
   - Proposition 6.5, in the same section.
2. **Stability, 2019 → pin, for the `normal-modal-logic` part.** This
   compares OpenLogic `3162240` (2019-08-29, the last commit to that part
   before 2019-09-15) with `0a18d37`.
   - Written in full (`part:chapter:section:label`), every label changed,
     because the part tag was renamed from `mod` to `nml`.
   - Written without the part tag (`chapter:section:label`), **89 of 89
     labels survived**, and 95 exist now.
   - 64 of 65 `chapter:section` IDs survived.
   - Over the same period the printed numbers moved a lot.
3. **Numbers can't be computed from the source.**
   - Walking the sources in `bd.tex`'s import order gives 213 numbered
     statements in 15 chapters. The PDF has 208.
   - The two sequences agree for the first 91 items, then diverge in
     Chapter 4 (completeness).
   - The cause: the source contains alternative versions selected by build
     tags. `nml:com:mod` has two `prop:diamond` statements, one under
     `\iftag{prvBox}{…}{…}`, and B&D's build keeps only one.
   - Extra examples (6.23, 7.6–7.8) appear in the source walk but not in
     the PDF, which fits the same explanation, but I didn't check each one.
   - So which statements exist, and their numbers, depend on the book's tag
     configuration.

## Recommendation

1. **Cite a number plus an anchor.**
   - Labeled statements get the label without the part tag, since that's
     what changed: "B&D Thm. 6.6 [tab:sou:thm:tableau-soundness]".
   - Unlabeled statements get their section plus their position among that
     kind in that section: "B&D Def. 6.3 [tab:sou, defn 1]". Positions
     survive renumbering elsewhere in the book, but not edits to that
     section.
2. **Keep a citation index** (`notes/bd-citations.tsv`): one row per
   anchor, with the number, the page and the first words of the
   statement in the pinned PDF.
   - When the pin moves, labeled anchors map to their new numbers exactly.
   - Positional anchors are checked by matching the statement's text in the
     new PDF. The migration report lists what moved, what changed wording
     and what disappeared.
   - The index also catches wrong citations today, of the kind found
     repeatedly in gamen-hs.
3. **Offer the labels upstream.** A pull request to OpenLogic adding
   `\ollabel` to the few dozen unlabeled definitions and examples we cite
   would make them as stable as the theorems, for everyone who uses the
   book.
4. **Exact alternative, not needed yet:** build B&D ourselves at the pinned
   revisions, with a LaTeX hook that writes each statement's number, file
   ID and label to a file. That gives exact numbers under the real tag
   configuration, but needs a TeX installation and more machinery.

## How this was checked

- The work was done in a sparse, shallow clone of `OpenLogicProject/OpenLogic`
  at `0a18d37` and `3162240`, fetched by SHA, plus `gh api` reads of
  `rzach/boxes-and-diamonds` at `f3673b5`.
- **Label and ID extraction:** regexes over `\olfileid`, `\ollabel` and the
  six numbered theorem environments, with TeX comments stripped.
- **Numbering walk:** `\olimport` was followed recursively in `bd.tex`'s
  order, and the six environments share one counter per chapter. This is
  B&D's own scheme: Example 6.1, 6.2, then Definition 6.3.
- **PDF side:** `pdftotext -layout notes/bd-screen.pdf`, keeping lines
  that begin with "Definition/Theorem/… N.M", first occurrence only.
- The scripts were throwaway, and the method is described here in enough
  detail to redo. If the citation index gets built, its tool replaces
  them.
