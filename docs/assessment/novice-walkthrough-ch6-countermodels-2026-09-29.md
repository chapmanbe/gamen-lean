# Novice walkthrough: `Notebooks/Ch6Countermodels.lean` (2026-09-29)

**Why an agent, not students.** There are no students to test with, so this
walkthrough stands in for them (see
`plans/countermodel-explorer-and-k-soundness-2026-09-29.md`, Part A). Treat
its findings as informative, not as evidence of how real students do.

**Setup**
- **Who:** a fresh Fable agent with no project context.
- **Role:** a health informatics graduate student who has seen propositional
  logic only briefly, has never used Lean or seen modal tableaux, and has read
  B&D chapters 1–5 casually.
- **What it read:** only the notebook, not the library, tests, plans or
  CLAUDE.md.
- **How it ran it:** `lake env lean Notebooks/Ch6Countermodels.lean`, to see
  what the `#eval` output would show in the infoview. The `#html` widgets were
  judged from the prose around them, because they don't render in a terminal.
- **What it did with the exercises:** tried each one before reading its hint.
- **Version tested:** commit `45855f8` on the countermodel-explorer branch,
  before any revision.

## Findings

Line numbers refer to that version.

**Mathematics.** No errors found. The Example 6.22 summary matches B&D's
countermodel (pp. 112–113). Hint 1's chain model (1 → 1.1 → 1.1.1, with
V(p) = {1.1}) matches the computed countermodel.

**The notebook assumes more than a novice knows:**
1. **Tableau vocabulary used before it's explained** (L26–31): "prefixed
   tableau", signed formulas (`1 F A`), "branch", "closes", "open",
   "complete", and Theorems 6.6 and 6.19. A student who has read chapters
   1–5 hasn't met tableaux.
2. **The tableau itself is never shown** (L45–48). The prose jumps to "the □F
   rule creates 1.1 and 1.2" and skips the →F and ∨F steps and why branch
   1.1 T p closes. So the recipe for reading W, R and V off a branch
   (L33–37) had no branch to apply to.
   *This was the walkthrough's top recommendation:* print Example 6.22's open
   branch line by line before the recipe.
3. **Lean and editor basics are missing** (L12, L50–52, L76–78):
   - how to open the file and find the infoview;
   - what `open …` and `def … : Formula := ml[…]` mean;
   - how to type □, ∨ and → (`\box`, `\or`, `\to`);
   - what `.isValid`, `:=` and `by native_decide` mean.
4. **Parameters left unexplained** (L39–41): the `premises` argument, and the
   `[]` in every call, are never explained. The "unknown" verdict is never
   shown.
5. **Precedence** (L52, L90, L94): the code writes `□p ∨ □q → □(p ∨ q)` and
   the prose `(□p ∨ □q) → …`. The notebook doesn't say that ∨ binds tighter
   than →.
6. **The widget is described only by what to click** (L60–70). There's no
   description of its parts (the diagram, the facts, the checks) before the
   clicking instructions. For valid formulas (L104–106), nothing says what
   the widget shows, so a student can't tell "valid" from "broken".
7. **How S4 changes the tableau** (L88–89, L112–114): the notebook never says
   S4 adds rules, so exercise 2 can only be answered from the frame
   condition. The names of the other systems (`systemKT`, `systemS5`) aren't
   listed either.

**Exercise mechanics:**
- **Exercise 2 is defined as `exercise1` run under `systemS4`** (L93–101), so
  grading `predict2` against `exercise1` looks like a bug.
- **The grade output is an unlabeled list of three strings.** With mixed
  results, the student has to count positions.
- **Wrong answers all get the same generic hint.**
- **The answer key is visible right under the exercises** (L119–121,
  `example … = false / true / true`), which spoils the predictions.
- **A maintainer-only reference** ("Gamen.jl / Pluto counterpart", L8) is
  shown to students.

## What happened next

These findings, together with the Opus code review, went back to the author
in one revision round, which landed as commit `7acde4b`.

**Second walkthrough, on `7acde4b`.** A fresh Fable agent played the same
student role, under the same rules.
- **Example 6.22:** it could follow the tableau from start to finish, and it
  read W = {1, 1.1, 1.2}, R and V off the branch itself. Its reading matched
  the notebook's summary and B&D Figure 6.1.
- **Exercises:** it predicted all three correctly before reading the hints.
  Filling in the answers gave "✓ Correct" on all three. A deliberately wrong
  copy gave "✗ Not quite" plus the numbered hint, so the student can tell
  success from failure.
- **What remained** (sent back as a second, small round):
  - say that the panel shows only the open side of each ∨T split;
  - include the fact-button row in the description of the panel;
  - an opaque error when `#eval`-ing the verdict directly;
  - "open branch 1" is numbered but never explained;
  - an unlabeled K-axiom example in the Solutions.

**What this suggests.** The first version assumed more than a novice knows.
Two things fixed most of it: showing the actual tableau branch, and defining
the vocabulary before using it. These are a stand-in's findings, not
students'.
