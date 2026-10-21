# Verification of the [ASSERTED] sources from the 2026-10-13 digest (2026-10-15)

Scope: bibliographic facts only, checked against local files. No paper was read for its
results. A line marked verified means the stated fact was seen in the named file.

| Source | Checked against | Result |
|---|---|---|
| Baltag, Moss & Solecki, "The logic of public announcements, common knowledge, and private suspicions", TARK 1998, pp. 43-56 | reference list of Velázquez-Quesada (arXiv:2210.04656v1) | **Reference verified second-hand; the original is not local and was not read.** Velázquez-Quesada also attributes private announcements to Baltag et al. (1998, 1999). `Gamen/ActionModel.lean` docstring updated. |
| Galimullin & Ågotnes, "Dynamic Coalition Logic: Granting and Revoking Dictatorial Powers", LORI 2021, pp. 88-101, doi:10.1007/978-3-030-88708-7_7 | `Bergen/lit/bergen.bib` (`galimullin2021dcl`) | **Bib entry exists; PDF not local, not read.** The DaLí 2022 paper was not found in the bib: still [ASSERTED]. Not cited in code. |
| Velázquez-Quesada, "Communication between agents in dynamic epistemic logic", arXiv:2210.04656v1, 10 Oct 2022 | `~/Downloads/2210.04656v1.pdf` first page | **Title, author and arXiv id verified.** The digest's "topic-based relation updates" description was not re-checked. Not cited in code. |
| Perrotin, Galimullin, Canu & Alechina, "Public Group Announcements and Trust in Doxastic Logic" | `Perrotin-etal-PGAaTiDL.pdf` first page | **Title and authors verified. The PDF text carries no venue or year** (PDF creation date is Oct 2019). "LORI 2019" is therefore unverified. `Gamen/EvidenceTrust.lean` docstring and issue #4 corrected to say so. |
| Hunter: 2017 (with Schwarzentruber & Tsang), 2022, 2023 (x2), 2024 (x2), 2026 (x2) | first pages of the local PDFs | **Titles and authors verified** (`hunter2017manipulation`, `2022dishonest`, `2023joint` with Booth, `2023reports`, `2024combined`, `2024tool` with Iglesias, `2026memory`, `2026twokinds` with Lepke). Years come from file names, not checked; venues not checked; none read for results. |

Still [ASSERTED]: every claim about what these papers prove or how they model trust; the
DaLí 2022 reference; venues and years noted above.

## Addendum: Figure 1 edge costs (Catta, Galimullin & Mittelmann, AAMAS 2026, p. 3)

The digest said the costs in `Tests/AngelsDemons.lean` (`cost1`, `e1`) were a reconstruction
from the text (confidence: medium). Checked by rendering p. 3 of the PDF at 400 dpi and reading
every label of both models. **All match; no change to any cost.**

- Self-loops: s0 3, s1 3, s2 2, s3 2 (identical in 𝔐1 and 𝔐2).
- s0→s2 2, s2→s0 1, s0→s1 3, s0→s3 2, s2→s3 1; dotted s1→s0 1, s3→s2 1.
- 𝔐2: the s0→s3 and s2→s3 edges are dotted (removed), with the same costs.
- Pairs not drawn get cost 9 in the tests; the figure has none, so that is a test convention.

Not checked: that the dotted edges' arrow directions in 𝔐2 (s3→s2 and s2→s3 both drawn) matter
to any claim; the tests use only the 𝔐1 and 𝔐3 constructions from the text.

## Addendum 2026-10-21: Perrotin et al. and Hunter, read

Read from the local PDFs (pdftotext); abstracts, and for Perrotin §§3 and 7, in full.

| Source | What was read | Result |
|---|---|---|
| Perrotin, Galimullin, Canu & Alechina, "Public Group Announcements and Trust in Doxastic Logic" | §3 (semantics), §7 (discussion), headings, references | **Read.** The logic is SDDLT: *syntactic* belief bases (sets of formulas over `B_a`, closed under the trust-chain relation) and a trust *set* per agent, with simultaneous public group announcements. Trust can only be lost; announcements that contradict each other, with neither supported by the receiver's beliefs, cost both announcers their trust. Complete axiomatization by reduction axioms (Theorem 1). It does **not** cite Liu & Lorini (DL-BET), uses no evidence sets or possible worlds, and is a different framework, not an extension of `EvidenceTrust`. Venue and year are still absent from the PDF text: unverified. |
| Hunter 2023 (Booth), "Joint Trust for Belief Revision" | Header, abstract | Venue verified from the PDF header: the 36th Canadian Conference on Artificial Intelligence. |
| Hunter 2023, "Reports, Observations, and Belief Change"; 2024, "Combined Change Operators for Trust and Belief"; 2026 (Lepke), "Belief Revision with Two Kinds of Trust"; 2026, "Belief Change with Full Memory and Trust" | Abstracts only | These are AGM/Darwiche-Pearl-style postulate papers on trust-weighted revision (representation results, trust-change operators, honesty thresholds). They are not modal logics with a semantics to port. Venues and years unchecked; results not read beyond the abstracts. |

Consequence for issue #4: the `EvidenceTrust.lean` docstring claim ("other components") should read as *related work*, not as components of DL-BET. Neither source is a natural next module.
