# Dynamic-scenarios explorer: action models, ATL-D/ATEL-D, angels and demons

*2026-10-21. Design for the NEXT.md item "a notebook or widget for the
action-model and angels-and-demons work." Brainstormed with Brian; his decisions
are marked as his, mine as "my call."*

## Intent

A student who has worked through the existing Boxes and Diamonds notebooks and
widgets uses a small set of clinical scenarios to build an intuition for three
dynamic logics already in the library, and to see where each is useful in
health care:

- **Action models** (`Gamen/ActionModel.lean`): an event that some agents see
  and others don't, and what each agent then knows about the others.
- **ATL-D / ATEL-D** (`Gamen/Atl/Dynamic.lean`): granting and revoking the
  actions agents have, with and without knowledge of the change.
- **Angels and demons** (`Gamen/AngelsDemons.lean`): a demon removes and an
  angel adds edges of a graph, within a per-step budget, while a traveler moves.

Brian's framing: the student sees **the logic, not only the scenario**. Models,
updates and formulas are on screen at all times; the clinical story motivates
them but never replaces them.

## Decisions (Brian's)

1. **Widget first** (option B of the mockups). The student works by clicking:
   choosing who sees an event, which grant or revoke applies, what the demon
   removes or the angel adds, and sees the model before and after. Little code.
2. **Graded questions inside the widget**, of all three kinds:
   - **click the worlds** (or states) where a formula holds; the widget checks
     the set;
   - **change the scenario to reach a goal**: alter the update (who sees it,
     which grant, which intervention, the budget) so a goal formula holds;
   - **write the formula** that is true exactly at a given set of worlds; the
     widget compares truth sets.
   A wrong answer gets a reason, not just a red mark.
3. **Scenarios**, in this order:
   1. **Handoff** (action models). The night clinician N pages the day
      clinician D that potassium is high (`p`). The page arrives (event `sent`,
      precondition `p`) or is lost (`lost`); D can tell the events apart, N
      can't. The student finds the state where D knows `p` but N doesn't know
      that D knows, then changes the event so both know and each knows the
      other knows.
   2. **"I would if I could"** (ATL-D, grant). A patient (or clinician) wants
      to reach a guideline goal but lacks a prerequisite action (a referral, an
      approval). The student finds which grant makes `⟨⟨a⟩⟩ F goal` true.
   3. **Safety versus access** (ATL-D, revoke). Revoking a permission to
      prevent harm can leave a team unable to act in an emergency. The student
      sees the paper's "reasonableness" rule: a revoke that would leave an
      agent with no action at a state is not applied there.
   4. **Pancreatic cancer: the path to first treatment** (angels and demons;
      Brian's grounding, from colleagues; sourced below). A **system-design**
      reading (agreed 2026-10-21): in this logic the traveler is not a player
      with goals; formulas ask whether the *modifier* has a strategy making ψ
      true on **every** traveler move (`Gamen/AngelsDemons.lean`, `satP`). So
      the traveler is the patient's path through a system they don't control,
      and the student plays the **health system**: the angel adds a route (the
      fast-track pathway), the demon closes one (a detour, or, read as
      disruption, a stalled step). The question: can the care team shape the
      pathway so that no path misses treatment within the window? The
      cooperative SUL form (`update a d`: angel and demon together against the
      traveler) is the central one. The patient as an agent with goals is ATL /
      ATL-D's job; see "Follow-up".
   5. **Shift-change handoff of authority** (ATEL-D, capstone; replaces the
      original "authorization the agent doesn't know about", which ATEL-D
      cannot express: a grantee is always informed, `Gamen/Atl/Dynamic.lean`
      lines 29-35, and moves must be uniform on an agent's indistinguishability
      classes). At shift change, ordering authority is granted to the incoming
      clinician (informed) and revoked from the outgoing one; the pharmacist is
      not in the informed set, so does not know the incoming clinician can now
      order. Pairs with scenario 1: there a *fact* reaches only some people,
      here an *ability* changes hands without everyone knowing.
4. **Survival is presented as unresolved.** Scenario 4 claims, with sources,
   that the pathway has these steps and that the interval is long. Whether
   delay changes survival is stated as contested, not as fact.
5. **Scenario 4 is played, not only checked.** Besides changing budgets and
   which steps can be added or closed and reading the verdict, the student
   plays the health system step by step: choose what to add or close, the
   widget moves the traveler along a path that escapes if one exists, and
   shows where the patient slips through. This needs the winning strategy
   (for the student's opponent and for hints), which the model checker does
   not return today: it computes truth sets only. Extracting it from the same
   fixpoint is an implementation addition, not a change to the logic.
6. **Scenario 4 waits for its sources.** Build scenarios 1, 2, 3 and 5 first;
   scenario 4's model, questions and text are built only after the papers
   below are downloaded (manually) and read.

## Goals

- One explorer, with one mode per logic, hosting the five scenarios.
- Each scenario: a short setup text, the model drawn, the update controls, a
  formula panel showing where formulas hold, and 3-6 graded questions mixing
  the three kinds.
- Every scenario and every answer is data, checked by `lake test`.

## Non-goals

- No new logic, no change to the semantics of the three modules, no
  `gamen-validate` protocol change (so `compare.py` is unaffected).
- Not a replacement for `Widgets/KripkeExplorer.lean`; it must keep working.
- No Obstruction Logic, no belief-base (ruby) action models, no web-editor
  (`web/`) deployment.
- No claim about survival benefit; no clinical numbers in scenarios 1-3 and 5.

## Anti-goals (would be a failure even if it works)

- A widget where the student can answer without looking at the model or the
  formula, i.e. the logic is hidden behind the story.
- Feedback that only says right or wrong.
- A clinical claim in scenario text without a cited source (project rule:
  domain claims come from authoritative sources, never from an LLM).
- A grader that silently returns a default on error (`panic!`, or `holdsAt`'s
  "error counts as false"): an evaluation error must surface as an error.

## Constraints

- Lean 4.34.0, ProofWidgets v0.0.111 (pinned; upgrade together).
- ProofWidgets `InteractiveSvg` constraints from CLAUDE.md: the RPC method must
  be named exactly `updateSvg` at the root, so there is **one** explorer state
  type in the package, and clicks are handled on **mouseup**. The existing
  `KripkeExplorer.ExplorerState` already owns `updateSvg`. Either the new modes
  join that state type (a sum over modes) or the new explorer is built on a
  different ProofWidgets component with its own RPC; builder's choice, but
  `KripkeExplorer` and its widget tests must keep passing.
- Library rules apply to any new library code: `Except`, not `panic!`; no
  `partial def` without a stated reason; search loops get fuel; no `sorry`.
- Keep models small enough to draw legibly: at most about 6 worlds/states
  after an update (action-model products multiply worlds).

## Design (my calls, all overridable)

### Scenario data
Scenarios live in data files (Buchanan's separation), one per scenario, read
by the explorer and by the tests. Each holds: title, setup text with source
keys, the model, the available update controls, display positions, and the
questions with their answers and per-answer hints for common wrong answers.
Format and location (`data/scenarios/*.json` is my suggestion) are the
builder's. The modules' existing JSON codecs (`EpistemicJson`, `CgsJson`) are
the starting point for models.

### Hosting
The explorer renders in the infoview from a notebook file, one per track
(epistemic: scenario 1; ability: 2-4; capstone: 5), with brief `/-! … -/`
prose between widget invocations, consistent with the existing notebooks.

### Grading
- Click the worlds: compare the clicked set with the formula's truth set.
- Reach a goal: apply the student's update with the library's own functions
  (`productUpdate`; `updateModel`; the angels-and-demons model checker) and
  evaluate the goal. For ATL-D, `Atl/UpdateSearch.boundedUpdate` can confirm
  that a goal is reachable at all, and find a smallest grant for the answer key.
- Write the formula: compare truth sets on the current (post-update) model.
  The student does not type update operators; formulas are evaluated after the
  update the widget shows.
- Feedback: first a hand-written hint matched to a known wrong answer, else a
  generated one naming the worlds where the answer and the target differ, and,
  for a `K` formula, the indistinguishable world that breaks it.

### Formula input
There is no runtime text parser for formulas: today they come from the `ml[…]`
macro or from JSON. "Write the formula" needs a parser for the epistemic
`Formula`, for ATL-D's `DFormula`, and for `AngelsDemons.SFormula`, with
syntax matching the notation students already know. It returns `Except` with
a readable error. This is the largest new piece of code.

### Mapping scenario 4 onto angels and demons
In `AngelsDemons`, the cost bounds **graph change per step**, not travel time
(module docstring, "What the cost bounds"). So:
- time is the traveler's number of steps, and the window is a step bound,
  expressed with nested `X` (or a pathway whose waiting states loop);
- the demon's budget is how much disruption can happen per step (removing the
  edge "biopsy → staging" = the biopsy stalls);
- the angel's budget is how much the fast-track intervention can add (an edge
  that skips pre-operative biliary drainage);
- questions ask whether the care team (angel, demon, or both via `update a d`)
  can make every path reach `treatment` within the window, and the smallest
  budget that does;
- encoding (my call): "only the fast-track edge" and "only this step can
  stall" are expressed by giving every other edge a cost above the budget, and
  the widget draws only the clinically meaningful edges, so no meaningless
  edge such as "work-up → treatment" is ever shown. Every intermediate graph
  must stay serial (module docstring; reading A, decided 2026-10-15);
- any reading of the box duals (`[n]ψ`, `…Box`) as "the patient gets through
  whatever happens" is checked against the paper's definitions before it
  appears in a question.

### Scenario 5 and ATEL-D
ATEL-D update clauses `φ : α → A, B` inform `A ∪ B`. Scenario 5 is a grant
(incoming clinician in `A`) and a revoke (outgoing clinician), with the
pharmacist in neither set. The plan file (`plans/atl-d-2026-10-13.md`)
recorded ATEL-D's strategy clause for `⟨⟨A⟩⟩` as unread on 2026-10-13; the
builder confirms from `Gamen/Atl/Dynamic.lean`'s docstring and tests what is
implemented, and writes the scenario's formulas against it, before writing
its questions.

### Formula syntax (my call)
Students type the notation the modules already print (`DFormula.toString` and
the equivalents in `ActionModel`/`Epistemic` and `AngelsDemons`), so what they
type is what the widget shows. The notebook prose introduces each new operator
(`⟨⟨A⟩⟩`, `has`, `X`/`U`/`R`, the update modalities) before a question uses it.

## Sources for scenario 4

Found 2026-10-21 by a literature-search subagent and verified against PubMed
by it; notes, verbatim abstracts and BibTeX in
`~/Downloads/pancreatic-lit/lit-search.md`. **Not yet read by us beyond those
notes:** each claim used in scenario text is checked against the paper before
it is cited (PDFs need manual download; automated fetches were blocked).

- Pathway: Gómez-España et al. 2021, SEOM clinical guideline, *Clin Transl
  Oncol*, PMID 33660222 (open access). Order: work-up; tissue diagnosis by
  EUS-FNA before biliary stent; three-phase CT staging; resectable /
  borderline / locally advanced / metastatic; multidisciplinary decision,
  surgery at high-volume centers; then surgery (resectable) or chemotherapy
  first (borderline, locally advanced). NCCN and ESMO texts could not be read.
- Interval: Sugumar et al. 2023, *Ann Surg Oncol*, PMID 37624518 (median 25
  days tissue diagnosis to treatment, rising 21 → 28); Sanjeevi et al. 2016,
  *Br J Surg*, PMID 26572509 (median 42 days imaging to surgery; no
  unresectable-at-operation cases within 22 days).
- Fast track: de Liguori Carino et al. 2022, *HPB*, PMID 34802941 (CT to
  surgery 8 vs 43 days without pre-operative biliary drainage).
- Survival unresolved: Lukács et al. 2019 systematic review, *Cancer Manag
  Res*, PMID 31819622; Mirkin et al. 2018, *J Gastrointest Surg*, PMID
  29520648 (no survival effect up to 12 weeks).
- Not supported, so not claimed: nurse navigation (no pancreatic study found);
  a multidisciplinary clinic did not shorten time to treatment (PMID
  27229097).

## Testing

- Answer keys: for every question in every scenario file, the stored correct
  answer grades as correct and each stored wrong answer grades as wrong with
  its hint.
- Each scenario's claims (e.g. "after `sent`, `K D p ∧ ¬K N (K D p)` holds at
  (w1, sent)") are also asserted as tests against the library directly, so a
  grader bug cannot hide a library bug or the reverse.
- Parser: round-trip and error-message tests; property test that parsing the
  printed form of a random formula returns the formula.
- Widget tests replay the real event order (mouseup), as for `KripkeExplorer`;
  existing widget tests keep passing.
- Plant a bug (e.g. flip one answer, or make `lost` visible to N) and confirm a
  test catches it.

## Follow-up (not in this build)

A parallel ATL / ATL-D notebook on the same pancreatic pathway, with the
patient (and clinicians) as agents with goals: what can the patient, alone or
with the care team, force? Read beside scenario 4, it contrasts "what agents
can achieve" with "how the system must be shaped so nobody falls through."

## Left to the builder

Drawing layout for product models; the controls for choosing grants, revokes
and edges; the data file format; whether the explorer shares `KripkeExplorer`'s
state type or uses another component; exact question wording; how many
questions per scenario within 3-6.
