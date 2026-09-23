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

## 3. Review

Launch the `module-reviewer` agent (Opus) on the porter's branch. Give it
the branch and module name, **not** the porter's report.

If the Porter column says `opus` or `fable`, also run `mmreview` on the
branch diff: the porter and the reviewer are both Claude, and on the risky
modules an outside model is worth the cost.

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
