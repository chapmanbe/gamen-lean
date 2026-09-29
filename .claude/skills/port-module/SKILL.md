---
name: port-module
description: Use when porting a gamen-hs module to gamen-lean, e.g. "/port-module Doxastic" or "/port-module Epistemic fable".
argument-hint: <Module> [sonnet|opus|fable]
disable-model-invocation: true
---

# Port a module

Arguments: the module name as it appears in `PORTING.md`, and optionally
the porter model.

## 1. Pick the porter model

Use the model argument if one was given. Otherwise use the module's
**Porter** column in `PORTING.md`. Stop and ask if the row says `—` or the
module's dependencies (the **Depends on** column) are not yet ported.

## 2. Port

Launch the `module-porter` agent with `isolation: "worktree"` and `model`
set to the porter model. The prompt names the module and nothing else; the
agent file carries the instructions.

The worktree branches from `origin/main`, not the local `main`. The porter
fast-forwards to local `main` as its first step. If it reports that the
fast-forward failed, stop and tell the user. When reviewing, diff with
`main...<branch>` (three dots) so commits made on `main` since the fork do
not show up as deletions.

## 3. Review

Launch the `module-reviewer` agent (Opus) on the porter's branch. Give it
the branch and module name, **not** the porter's report.

Give each reviewer its own checkout, since reviewers plant bugs and run
tests: `git worktree add --detach .claude/worktrees/review-<module>-<model>
<branch>`, copy the porter worktree's `.lake` into it to skip a full
rebuild, and tell the reviewer to work only there. (Two reviewers sharing
the porter's worktree once saw each other's planted bugs.) Remove these
checkouts after the merge; `--force` is needed because of the copied
`.lake`.

If the Porter column says `opus` or `fable`, also launch a second
`module-reviewer` with `model: fable`, in parallel with the Opus one, with
the same prompt. Neither reviewer sees the other's report. Findings both
report are the strongest signal; settle the rest the same way. (Outside
models via `mmreview` are not available on this machine: Codex has no
paid account, and Gemini's subscription login is refused for this CLI.
Revisit if that changes.)

## 4. Settle the findings

Before acting on a finding, reproduce it yourself: rerun the command, or
read the lines it cites. Drop findings you cannot reproduce, and tell the
user which. Send the confirmed ones back to the porter (`SendMessage`, same
agent) and have it fix them on its branch. Then re-check those findings
yourself. After two rounds that still leave findings, stop and bring them
to the user.

## 5. Report and merge

Tell the user: spec cases vs Lean cases, test totals, planted-check
results, compare.py disagreements, B&D fixes, the model, and anything
fixed after review. **Merge only when the user says so.** Then merge
`--no-ff` into `main`, run `lake build` and `lake test` on `main`, remove
the worktree, and delete the merged branch. Do not push unless asked.

If the port took noticeably more or fewer rounds than its Porter model
suggests, propose a change to that column.
