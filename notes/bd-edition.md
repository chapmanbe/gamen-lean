# Pinned edition of Boxes and Diamonds

*Boxes and Diamonds* (B&D) is an open-access book that Richard Zach keeps
revising. Definition, theorem and page numbers move between editions: the
Fall 2019 edition had epistemic logic in Chapter 13, and Fall 2025 has it in
Chapter 15 (Chapter 13 is now minimal change semantics). A citation that
doesn't say which edition it means can go stale without anyone noticing.

**Every unqualified "B&D" citation in gamen-lean refers to the edition
below**, the same edition gamen-hs pins. To cite any other edition, name it
explicitly (e.g. "B&D Fall 2019, Def. 13.5").

| | |
|---|---|
| Edition | Fall 2025 ("F25" on the title page) |
| B&D revision | `f3673b5` (2025-07-01) |
| Open Logic Text revision | `0a18d37` (2026-02-16) |
| File | `notes/bd-screen.pdf` (screen version, 315 pages), committed here |
| SHA-256 | `3c50d5da0ac02791cd7a4df80d7e3921ffed96f2c8d8643b71666ee9d71bc453` |
| Source | <https://bd.openlogicproject.org/> |
| License | Text: CC BY 4.0. Cover illustrations: CC BY-NC 4.0. |

The revisions are printed on the copyright page ("This version of Boxes and
Diamonds is revision …"). The Open Logic Text revision can change within one
named edition, so check the SHA-256 and revisions, not just "F25".

## License and attribution

*Boxes and Diamonds: An Open Introduction to Modal Logic*, by Richard Zach
(Open Logic Project), is licensed under a
[Creative Commons Attribution 4.0 International License](https://creativecommons.org/licenses/by/4.0/).
It is based on *The Open Logic Text* by the Open Logic Project, used under
the same license. The cover illustrations are licensed
[CC BY-NC 4.0](https://creativecommons.org/licenses/by-nc/4.0/).

`notes/bd-screen.pdf` is the unmodified file from
<https://bd.openlogicproject.org/>, kept here so that citations can be
checked against exactly the pinned build. It is not covered by this
repository's `LICENSE`. Because of the cover, don't redistribute the PDF
commercially.

## Checking citations

```sh
shasum -a 256 notes/bd-screen.pdf        # must match the SHA-256 above
pdftotext -layout notes/bd-screen.pdf - | grep -n "Definition 6.3"
```

## Keeping in step with gamen-hs

This file is a copy of gamen-hs's `notes/bd-edition.md` (gamen-hs PR #50),
minus its list of stale citations in the Haskell sources, which live there.
If either repository moves the pin:

1. Replace the PDF in both.
2. Update this table in both.
3. Re-check every B&D citation in both. Search for `Definition`, `Def.`,
   `Proposition`, `Theorem`, `Example`, `Figure` and `Table` near "B&D", and
   fix the ones that moved.
