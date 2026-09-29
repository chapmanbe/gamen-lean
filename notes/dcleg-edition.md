# Pinned version of the DCLEG draft

`Gamen.Dcleg` ports gamen-hs's `src/Gamen/Dcleg.hs`, which implements
Jeremiah Chapman, *Doxastic Conditional Logic of Extensive Games* (v5.0),
University of Gothenburg, April 2026, supervised by Martin Kaså.

**Every unqualified "Chapman (2026)" or "DCLEG" citation in gamen-lean means
the v5.0 draft below.** The final thesis is signed for release but not yet
in GUPEA (checked 2026-09-29). When it appears, compare it with v5.0 and
re-check every Chapman (2026) citation, just as for a new B&D edition
(`notes/bd-edition.md`).

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
