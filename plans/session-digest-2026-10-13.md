# Knowledge Digest: gamen-lean issue #3 (dynamic strategic logics) and its review
*Written 2026-10-13 at the close of the session that implemented issue #3 and reviewed the result. Read this once; it is the state of that work. It is a handoff for choosing the next thread, not a draft brief.*

> **Kickoff:** Read `plans/session-digest-2026-10-13.md`, then ask Brian which open thread to take (competitive SUL coalitions needs his decision first; item 4 needs a scoping call). Do not re-open the settled decisions below, and do not cite any [ASSERTED] source until it is checked against the paper.

## Objective
Hand off the state after items 1-3 of issue #3 were built, pushed and adversarially reviewed. Nothing is to be drafted. The next session picks one thread from "Open questions".

## State in one paragraph
Everything is committed and pushed (`main` at `62f35aa`); `lake build` is clean, `lake test` passes 1470, and `tools/compare/compare.py` shows only the known 103 DISAGREE (deontic-STIT, documented). Issue #3 is open and carries comments for every step. New Lean-only protocol requests: `atl_model_check` (+ `"dynamic": true`), `epistemic_check`, `atl_update_search`; `gamen-validate` protocol is at 6.

## Decisions and framing (do not relitigate)
- **ATEL-D `⟨⟨A⟩⟩` is subjective** (memoryless uniform strategies over the *updated* relation, as `atlirSat`). The conference paper never states it; the extended version's Example 2 does ("no uniform strategy … from all states the robots consider indistinguishable"), and the objective reading contradicts its text. Objective is kept only for comparison.
- **ATL-D formulas live in a separate `DFormula`**, not in `Formula`: an update holds a list of conditions, which would make the 30-constructor `Formula` a nested inductive (risk to derived instances and termination lemmas).
- **Bounded update existence is a finite-pool search** (clause count, breadth-first over distinct models, fuel). The paper's problem ranges over every condition formula, which is infinite; `notFound` means "none over this pool within the bound".
- **Theorem 3 (behavioural constraints) comes from van der Hoek, Roberts & Wooldridge 2007 §4**, not from Alechina, Logan & Dastani 2018 (an earlier note and a #3 comment named it wrongly; corrected). It agrees with ATL-D's revoke only for *reasonable* constraints.
- **SDL/SCL/SUL's cost bound is a per-step budget on graph change**, and edits persist; it is not a cost on agents' actions. Only the *cooperative* SUL update is implemented.
- **Action models are a library plus `epistemic_check`; `Formula` is unchanged** (no `⟨A,e⟩` constructor). The belief-base half of the Lorini paper is not ported.
- **Reviews use a scrubbed copy** (no plans, `PORTING.md`, CLAUDE.md) so the reviewer is independent. `agy -p` works headless only with a self-contained prompt (inline the files); Brian approved sending code and paper extracts to Antigravity (telemetry off).
- gamen-lean stays Lean-only here: nothing is mirrored to gamen-hs; papers are never committed.

## Structure (what exists)
| Module | Request | Tests |
|---|---|---|
| `Gamen/CgsJson.lean`, `Validate/Atl.lean` | `atl_model_check` (protocol 2) | `Tests/ValidateAtl.lean` |
| `Gamen/Atl/Dynamic.lean` (ATL-D, ATEL-D) | `atl_model_check` + `"dynamic": true` (3, 4) | `Tests/AtlDynamic.lean` |
| `Gamen/ActionModel.lean`, `Gamen/EpistemicJson.lean`, `Validate/Epistemic.lean` | `epistemic_check` (5) | `Tests/ActionModel.lean`, `Tests/ValidateEpistemic.lean` |
| `Gamen/Atl/UpdateSearch.lean` | `atl_update_search` (6) | `Tests/UpdateSearch.lean` |
| `Gamen/Atl/SocialLaws.lean` | (library; Theorem 3) | `Tests/SocialLaws.lean` |
| `Gamen/AngelsDemons.lean` | none yet | `Tests/AngelsDemons.lean` |

Commits: `58aa079` (#2), `081587a` ATL-D, `b11eea4` ATEL-D, `f1b4d2a` Example 2 + Theorem 4 tests, `0dca214` action models + `epistemic_check`, `dc32476` update search + social laws, `8cec465` angels and demons, `62f35aa` review fixes. Record of the review: `docs/assessment/adversarial-review-2026-10-13.md`. Plan: `plans/atl-d-2026-10-13.md`. Protocol docs: `Validate.lean`. Status rows: `PORTING.md` ("Lean-only additions").

## Sources
"Verified" here means read in the local PDF or text extract and the definition numbers checked; PDFs are under `~/Projects/Logic/logic-notes/reference/dynamic-strategic-logics/pdfs/`, `~/Projects/Logic/Bergen/Bergen/lit/pdfs/` or `~/Downloads/`, and are not committed.
| Source | Locator | Status | Supports |
|---|---|---|---|
| Galimullin, Grosinger & Mittelmann, *I Would If I Could*, KR 2026 (conference + extended versions) | doi:10.24963/kr.2026/31 | [VERIFIED] Defs 1-11, Algorithms 1-2, Examples 1-2, Theorems 3-4, Def 7; proofs of Theorems 5-7 and expressivity **not read** | ATL-D, ATEL-D, update search, Theorem 3/4 tests |
| Lorini, Perrotin & Schwarzentruber, KR 2022 | doi:10.24963/kr.2022/24 | [VERIFIED] Defs 6-9, Examples 1-3; Defs 10-11 (ruby actions) not ported | action models |
| van der Hoek, Roberts & Wooldridge, Synthese 156(1):1-19 (2007) | doi:10.1007/s11229-006-9072-6 | [VERIFIED] §4 (pp. 9-11) | behavioural constraints, Theorem 3 |
| Galimullin & Kuijer, AAMAS 2024 (3-page abstract) | AAMAS 2024, pp. 2270-2272 | [VERIFIED] atomic-law semantics | Theorem 4 differential test |
| Catta, Galimullin & Mittelmann, *On Angels and Demons*, AAMAS 2026 | doi:10.65109/xezz1033 | [VERIFIED] Defs 1-11, Examples 1-3, Def 13; proofs not read; Figure 1 costs are a **reconstruction** | SDL/SCL/SUL |
| Alechina, Logan & Dastani, FLAP 5(2):457-490 (2018) | in `~/Downloads/ifcolog00022.pdf` | [VERIFIED] not needed (survey; does not cover vdHRW) | none |
| Baltag, Moss & Solecki 1998 | not local | [ASSERTED] original action-model source; cited via Lorini only | action models |
| Galimullin & Ågotnes, LORI 2021 and DaLí 2022 | dois in `Bergen/lit/bergen.bib` | [ASSERTED] not local; PDFs not found | ATL-D precursor, action models for coalition logic |
| Velázquez-Quesada 2022 (arXiv:2210.04656) | `~/Downloads/2210.04656v1.pdf` | [ASSERTED] only skimmed; different mechanism (topic-based relation updates) | item 3 background |

## Key claims
- Example 2 of the angels-and-demons paper ("holds for any state s") is **false at s1** under its own Defs 5/8; true at s0, s2, s3, and the `X`-shifted form holds everywhere. Confidence: high (hand-derived and tested).
- Figure 1's edge costs were reconstructed so every textual claim about 𝔐1/𝔐2 holds; they were not read off the figure. Confidence: medium.
- The review found a real SUL legality bug (the demon's removal must leave a serial model on its own, footnote 2) that the paper-based tests had missed; reviewers independently agreed on the others. Confidence: high.
- Lean's JSON parser keeps the last duplicate key silently (known divergence D5). Confidence: high (probed).

## Constraints
American English everywhere; B&D numbers checked against the PDF, other papers against the local copies; no `sorry`, no `partial def` in the library except the JSON decoders (documented), `Except` not `panic!`; tests must be mutation-checked ("plant a bug"); keep `compare.py` at the known 103; context-frugal outputs.

## Non-goals / rejected framings
- Implementing the competitive SUL coalitions without Brian's decision on joint-move legality against a universal opponent (the paper is silent; guessing risks a wrong logic).
- Treating `found: false` from the update search as "no update exists".
- Treating the Alechina survey as the source of Theorem 3.
- Mirroring any of this into gamen-hs, or committing the papers.

## Open questions for the next session
- [ ] **Competitive SUL** (Def 10: `⟨[demon n]⟩^m`, `⟨[angel n]⟩^m`, `⟨[∅]⟩`): Brian to decide the legality convention; Example 3's own claims use them.
- [ ] **Item 4** (trust and discordance across sources): scoping call; suggested start is one component (e.g. Liu & Lorini 2017) plus a design issue.
- [ ] A `gamen-validate` request for the angels-and-demons checker; a notebook or widget for the action-model work.
- [ ] The unread proofs (complexity and expressivity of ATL-D and angels-and-demons); fetch Galimullin & Ågotnes 2021/2022 if wanted.
- [ ] Check the Figure 1 reconstruction against a higher-resolution figure or the authors.
- [ ] Any [ASSERTED] source above must be verified before it is cited anywhere.

## Suggested drafting model
Strong model (Sonnet or Fable) for any new logic or semantics decision; Sonnet is fine for mechanical follow-ups with a checkable spec (a protocol request over an existing checker, a notebook port). Run a fresh adversarial pass (scrubbed copy, `agy` + Fable) on anything new before merging.
