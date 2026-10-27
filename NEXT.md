# NEXT

## Start here (Jeremiah, from 2026-10-27)

Brian has handed the dynamic-scenarios explorer to Jeremiah. Its work is on
the branch `dynamic-explorer` (not yet merged into `main`). If you are
Jeremiah, or Claude answering "what's next?" for him, do these in order:

1. Make sure you are on the branch: `git branch --show-current` prints
   `dynamic-explorer`. If not, see section 2 of the handoff.
2. Read `plans/handoff-jeremiah-dynamic-explorer-2026-10-27.md` sections 1
   and 2 (what this is, getting the branch).
3. Set up Lean and VS Code on macOS: handoff section 3 (3.1–3.10). Check:
   `which lake` prints a path under `~/.elan/bin`.
4. In the repo folder: `lake build`, then `lake test`. Expect every test to
   pass (1759/1759 at handoff). Handoff section 4.
5. Check the widget and notebooks by eye (nobody has yet): handoff section 6.
   Start with 6a, the known bug (self-loops hidden behind stacked worlds in
   `DynamicEpistemic.lean`, e.g. the N loop at w1×sent); it lists two fixes
   to choose between. Then 6b (click-through, steps in the "Before merge"
   item below) and 6c (the three notebooks).
6. Review the build-time decisions (handoff section 7), then report to
   Brian as handoff section 10 says.

Everything below this section is the project-wide list of open threads.

## Open threads

Open threads (2026-10-20), from plans/session-digest-2026-10-13.md:

- Issue #4: Perrotin and Hunter are read (2026-10-21; addendum in docs/assessment/source-verification-2026-10-15.md, digest plans/session-digest-2026-10-21-sources.md). The issue has a comment recording this, and the `EvidenceTrust.lean` docstring now says related work. Left: the research question (trust in a source's classification, discordance across sources), the per-class `types` wire restriction, and verifying venues/years before citing.
- Dynamic-scenarios explorer (2026-10-22, branch dynamic-explorer): the widget (`Widgets/Dynamic/`, `Widgets/js/dynamicExplorer.js`), the scenario format and grader, and three notebooks (`Notebooks/DynamicEpistemic.lean`, `DynamicAbility.lean`, `DynamicCapstone.lean`) are done for scenarios 1, 2, 3 and 5. Before merge (Brian):
  - Manual infoview check of the widget (steps from the Task 5 widget check). In VS Code, `lake build` once. Create the uncommitted scratch file `Scratch/DynExp.lean`:
    ```lean
    import Tests.DynamicExplorer
    open Gamen.Widgets
    #html dynamicExplorer DynamicExplorerTests.sc
    #html dynamicExplorer DynamicExplorerTests.dscQ  -- ATL-D, reasonableness note
    ```
    (If `#html` is not in scope, add `import ProofWidgets.Component.HtmlDisplay`.) On the first `#html`: (1) see "Lab result" and worlds w1 (p), w2 (∅) joined by an "N,D" line; (2) tick **D**, status still says "before"; (3) **Apply** gives w1×lost, w1×sent (stacked under w1), w2×lost; (4) click w1×sent, it turns amber; (5) **Check** gives a green ✓; (6) ▶ to question 2, type `K[D]p`, Check gives ✓, then `K[D` gives a parse error in the neutral box; (7) ▶ to question 3, Check with D ticked gives ✓; (8) persistence: tick D, Apply, click a world, move the cursor elsewhere on the `#html` line and edit a comment elsewhere in the file, and the box, after model and highlight all stay; (9) **Reset** clears the box and restores the before model. On the second `#html`: s0 and s1 each have a dashed loop below the node labeled "otherwise: stay"; tick **noX**, press Apply, and the notes box shows "Revoking x from nurse at s0 would leave nurse no action there…"; it stays visible after clicking s0 and Check.
  - Lake does not track `include_str` files. After editing `Widgets/js/dynamicExplorer.js`, change `Widgets/Dynamic/Widget.lean` (any real edit) so Lake rebuilds the widget; after editing a `data/scenarios/*.json` file, change `Widgets/Dynamic/Library.lean` the same way (the disk-staleness test in `lake test` catches a stale scenario, nothing catches stale JS).
  - View each of the three notebooks once in an infoview. Until the branch is merged, the notebooks exist only on the `dynamic-explorer` branch, so:
    1. In VS Code, **File → Open Folder…** the checkout that is on `dynamic-explorer` (Jeremiah: your `gamen-lean` clone; Brian: the worktree `~/Projects/Logic/gamen-lean/.claude/worktrees/dynamic-explorer`). Open the repo root, the folder that holds `lakefile.toml`.
    2. In its terminal, run `lake build` once (the first run in a fresh clone downloads dependencies and can take several minutes).
    3. Open each notebook in turn: `Notebooks/DynamicEpistemic.lean` (scenario 1, the page that may not arrive), `Notebooks/DynamicAbility.lean` (scenarios 2 and 3, grants and revokes), `Notebooks/DynamicCapstone.lean` (scenario 5, the shift change). Wait for the orange progress bar in the gutter to finish.
    4. Put the cursor on each `#html dynamicExplorerOr …` line; the explorer appears in the infoview (**View → Command Palette → Lean 4: Infoview: Toggle** if the panel is closed). Read the prose above it and work through the questions with Apply, Check, ◀/▶ and Reset.
    5. Things to look for: the prose matches what the diagram shows; every question can be answered from the screen; wrong answers get a reason. One deliberate check: in `DynamicEpistemic.lean`, press Check on question 1 with nothing ticked, and the neutral box says to tick D, press Apply, then answer.
    If an explorer shows a plain paragraph starting "The scenario did not load." instead, its data file failed to decode: note the message.
- Next planned work after the explorer:
  - Scenario 4 (pancreatic) waits for the sources (PDFs to download manually into `~/Downloads/pancreatic-lit/`) and needs its own plan (SFormula parser, strategy extraction). Follow-up: a parallel ATL/ATL-D pancreatic notebook.
  - The documentation site (`docs/superpowers/specs/2026-10-22-documentation-site-design.md`, awaiting Brian's approval).
- A notebook or widget for the action-model and angels-and-demons work beyond the dynamic explorer (the explorer covers scenarios 1, 2, 3, 5 only).
- Obstruction Logic, which would let us test the OL halves of Theorems 3-4 of the angels-and-demons paper.
- Unrun: Theorem 6 of the angels-and-demons paper (SCL hardness; proof sketch is in a technical report), and the "no formula can distinguish" halves of the expressivity theorems.
