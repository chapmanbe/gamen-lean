# Knowledge Digest: gamen-lean cleanup and cwyde follow-up
*Written 2026-10-07 at the close of a cleanup session. Read this once, together with `plans/session-handoff-2026-10-06.md`; the digest updates that handoff's state and open questions.*

> **Kickoff:** Read `plans/session-digest-2026-10-07.md` and `plans/session-handoff-2026-10-06.md`, then ask Brian which open thread to take. Do not edit gamen-simulations, guideline-validation or guideline-cds-simulation without his OK: they hold uncommitted work of his own. Verify every state claim below with `git log` and `git status` before acting.

## Objective
Hand off the state after cleanup. Nothing is to be drafted. The next session picks one thread (cwyde issue #14, gamen-simulations Phase 1.3, citation tooling, or the soundness spike).

## Decisions and framing (do not relitigate)
- The DCLEG proofs stay on `main` as a library illustration; the thesis proofs were not removed. The thesis PDF is gitignored (`notes/dcleg-thesis-final.pdf`), local reference only.
- `dcleg-proofs-draft` branch and its worktree are deleted; the branch tip `1db8e7e` is in `~/Backups/dcleg-proofs-draft-2026-09-30.bundle`, and the worktree's zip is `~/Backups/DclegProofs-2026-09-30.zip`.
- The porter's worktree and branch `worktree-agent-aed8ec54ad95ac08b` are deleted (merged, tip `0072b72`). Only the main checkout remains.
- A bug found in the cwyde test is filed on cwyde (issue #14), not fixed in gamen-lean, because the cwyde-side re-encoding is the preferred fix.
- Brian addresses cwyde #14 from the cwyde project; no PR was opened, as there is no change yet.

## State (verify first)
- gamen-lean `main` at `bc7d20d`, pushed, clean. `lake test` was 1303/1303.
- guideline-validation: migration patch applied and pushed (`f2cb2b2`).
- cwyde: migration patch pushed (`dc6e807`); `CLAUDE.md` pushed (`0992980`); `main` in sync with `origin`. 27 `__pycache__/*.pyc` files are still tracked.
- gamen-simulations: migration patch applied in the working tree, uncommitted and mixed with Brian's own WIP; 4 unpushed commits (it showed `ahead 4`).
- guideline-cds-simulation: no upstream configured; not touched.
- `~/.local/share/gamen-lean/gamen-validate` is older than `main`; `tools/install.sh` has not been run for `dcleg-service`.

## Open threads
| Thread | Next step |
|---|---|
| cwyde #14 (`Indication` uses `Knowledge`) | Brian re-encodes via ranked belief, or files a gamen-lean issue to add `Knowledge` to the fragment; then update the cwyde `CLAUDE.md` line that calls it unresolved |
| cwyde `.pyc` untracking | `git rm -r --cached` the 27 files; add `.DS_Store` and `.ipynb_checkpoints/` ignores. Needs Brian's yes |
| gamen-simulations Phase 1.3 | Check D3, `enumerate_counterfactuals`/`info` use, seeding; before/after run; Brian's OK first |
| Dangling uncommitted files in guideline-validation, gamen-simulations, guideline-cds-simulation | Brian decides per repo |
| Handoff edits | The 10-06 handoff still lists the two deleted worktrees/branches as open and mentions the old worktree path; mark them done |
| Other (from the handoff) | Stale Lake cache entries; share `FINDINGS.md` with Jeremiah; when to make gamen-lean public; gamen-hs's fate; cwyde bridge rename; `~/Projects/Logic/CLAUDE.md` stale lines; rotate the leaked API key in guideline-validation's `.env` |

## Sources
No literature citations were used this session. None are [ASSERTED]. Any B&D or thesis definition numbers in the repo are checked against the pinned PDFs per `CLAUDE.md`, not from this digest.

## Constraints
American English. Brian approves merges. Never run `pixi run` in guideline-validation. `lake` needs `export PATH="$HOME/.elan/bin:$PATH"`. zsh does not split unquoted variables; BSD `sed -i ''`.

## Non-goals
- Do not commit the thesis PDF.
- Do not mirror fixes to gamen-hs (frozen).
- Do not paper over the cwyde failure by weakening the assertion.

## Open questions for the next session
- [ ] Which thread does Brian want?
- [ ] Did Brian push or change anything in the downstream repos since this was written?

## Suggested drafting model
Opus or Fable for Lean and proof work; Sonnet with an Opus blind reviewer for Python migration plumbing.
