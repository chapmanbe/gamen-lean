# Dynamic-Scenarios Explorer Implementation Plan (scenarios 1, 2, 3, 5)

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** An infoview explorer in which a student applies action-model and ATL-D/ATEL-D updates to small clinical models, sees the model before and after, and answers graded questions (click the worlds, reach a goal, write the formula), for scenarios 1 (handoff), 2 ("I would if I could"), 3 (safety versus access) and 5 (shift-change handoff of authority).

**Architecture:** All logic is Lean: a formula parser for the two logics, a scenario format read from JSON data files, a grader, and a pure explorer state machine (`step`, `view`). A thin hand-written JS component (no bundler) draws the `view` JSON and sends events to one root RPC method. Notebooks host the explorer with `#html`.

**Tech Stack:** Lean 4.34.0, ProofWidgets v0.0.111, Plausible v4.34.0, React via `@leanprover/infoview` (as ProofWidgets' prebuilt JS does).

**Spec:** `docs/superpowers/specs/2026-10-21-dynamic-scenarios-explorer-design.md`

**Out of this plan (spec decision 6):** scenario 4 (pancreatic cancer, angels and demons), its `SFormula` parser, and strategy extraction. They get their own plan once the sources are read. Nothing here may block adding an `angelsDemons` mode later: `Mode` is an inductive with room for it, and the grader works through `Evaluable` (Task 3), not through a specific logic.

## Global Constraints

- Lean 4.34.0; ProofWidgets v0.0.111; Plausible v4.34.0. No new dependencies.
- `Except`, never `panic!`; no `partial def` without a stated reason in the docstring; no `sorry`.
- An evaluation or parse error is shown as an error, never graded as "wrong" and never turned into `false` (spec anti-goal; do **not** use `Teaching.holdsAt`, which maps errors to `false`).
- `KripkeExplorer` keeps its root `updateSvg` method and its tests unchanged. The new explorer uses its own root RPC method, `dynamicExplorerStep`.
- No change to `Gamen/ActionModel.lean`, `Gamen/Atl/Dynamic.lean`, `Gamen/Epistemic.lean` semantics, or to `gamen-validate`.
- Scenario text makes no clinical numerical claims (scenarios 1, 2, 3, 5 are generic).
- At most about 6 worlds/states drawn per model, after an update.
- Every question's stored answer is checked by `lake test` (answer-key rule).
- American English in all prose, comments and scenario text.
- Commit messages end with `Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>`.

## Review Focus

1. **Malformed formula text** (empty, unbalanced brackets, `K[]p`, unknown operator such as `G p` in the epistemic mode): the student sees a one-line parse error naming the position; no crash, no "wrong answer". Test in Task 1 and Task 2.
2. **A formula naming an agent or atom the model doesn't have** (`K[X]p`, `has(nurse,order)` when `nurse` is not an agent): the explorer reports the evaluation error rather than treating it as false. Test in Task 3.
3. **An update that leaves no world** (every precondition false) **or a revoke stopped by the reasonableness rule**: the student is told what happened ("no world survives the update"; "revoking `order` from `outgoing` at `s1` was not applied: it would leave no action"). Test in Task 4.
4. **Events out of order**: submitting before applying the update, clicking a world of the *before* model when the question is about the *after* model, `nextQuestion` past the last question, toggling controls after applying. Each yields a defined state and a message, never an exception. Test in Task 4.
5. **A formula equivalent to, but not equal to, the stored answer** (`¬¬p` vs `p`, `q ∧ p` vs `p ∧ q`): "write the formula" grades by truth set, so these are correct. Test in Task 3.

---

## File Structure

| File | Responsibility |
|---|---|
| `Gamen/Input.lean` (new) | Tokenizer shared by both parsers; `parseFormula` for the epistemic `Formula` fragment |
| `Gamen/Atl/DynamicInput.lean` (new) | `parseDFormula`, `DFormula.toInput` (a printer the parser reads back) |
| `Widgets/Dynamic/Scenario.lean` (new) | Scenario types, JSON decoding, `Evaluable`, building the before/after models per mode |
| `Widgets/Dynamic/Grade.lean` (new) | `gradeAnswer`, generated feedback |
| `Widgets/Dynamic/Explorer.lean` (new) | `ExplorerState`, `Event`, `step`, `view` |
| `Widgets/Dynamic/Widget.lean` (new) | root RPC `dynamicExplorerStep`, `DynamicExplorerWidget`, `dynamicExplorer` |
| `Widgets/js/dynamicExplorer.js` (new) | hand-written ESM renderer |
| `Widgets/Dynamic/Library.lean` (new) | `include_str` of each data file, decoded scenarios |
| `data/scenarios/{handoff,would-if-could,safety-access,shift-change}.json` (new) | the four scenarios |
| `Notebooks/DynamicEpistemic.lean`, `Notebooks/DynamicAbility.lean`, `Notebooks/DynamicCapstone.lean` (new) | prose plus `#html dynamicExplorer …` |
| `Tests/DynamicInput.lean`, `Tests/DynamicExplorer.lean`, `Tests/DynamicScenarios.lean` (new) | `cases : List (String × Bool)` each |
| `Tests/Main.lean` (modify ~line 31-42 imports, ~6137 case list, ~6164 count) | register the three test modules |

Test-module pattern (from `Tests/ActionModel.lean`): `namespace XTests`, `def cases : List (String × Bool) := [ ("name", bool), … ]`, imported in `Tests/Main.lean` and appended to the unit-case list and the count.

---

### Task 1: Tokenizer and epistemic formula parser

**Files:**
- Create: `Gamen/Input.lean`
- Test: `Tests/DynamicInput.lean` (create), `Tests/Main.lean` (register)

**Interfaces:**
- Produces:
  - `inductive Gamen.Input.Token` (identifier, symbols, `<<`/`⟨⟨`, `>>`/`⟩⟩`, brackets, comma, colon, `+`, `-`) with a source position
  - `Gamen.Input.tokenize : String → Except String (List (Token × Nat))`
  - `Gamen.parseFormula : String → Except String Formula`

Grammar (Unicode and ASCII both accepted): atoms `[a-z][A-Za-z0-9_]*`; `⊥`/`false`; `⊤`/`true` (read as `¬⊥`, since `Formula` has no top); `¬`/`~`; `∧`/`&`; `∨`/`|`; `→`/`->`; `↔`/`<->`; `□`/`[]`, `◇`/`<>`; `K[a] φ` (agent: identifier, any case); announcement `[φ]ψ`; parentheses. Precedence, tightest first: prefix operators, `∧`, `∨`, `→` (right-associative), `↔`. Any other operator is a parse error ("not available in this explorer"). Errors read `"position N: <what was expected>"`.

The round trip uses the existing `Formula.toString` (it prints `K[a]φ` and `[B]C`, which this grammar reads back); no new printer.

- [ ] **Step 1: Write the failing tests** in `Tests/DynamicInput.lean`, namespace `DynamicInputTests`:

```lean
("parse atom", parseFormula "p" == .ok (.atom "p")),
("parse K", parseFormula "K[D] p" == .ok (.knowledge "D" (.atom "p"))),
("parse nested K", parseFormula "K[N] K[D] p" == .ok (.knowledge "N" (.knowledge "D" (.atom "p")))),
("ascii = unicode", parseFormula "K[D]p & ~K[N]K[D]p" == parseFormula "K[D]p ∧ ¬K[N]K[D]p"),
("∧ binds tighter than ∨", parseFormula "p ∨ q ∧ r" == .ok (.or (.atom "p") (.and (.atom "q") (.atom "r")))),
("→ is right-assoc", parseFormula "p → q → r" == .ok (.implies (.atom "p") (.implies (.atom "q") (.atom "r")))),
("announcement", parseFormula "[p]K[D]p" == .ok (.announce (.atom "p") (.knowledge "D" (.atom "p")))),
("empty is an error", (parseFormula "").isError),          -- define a local isError helper
("unbalanced is an error", (parseFormula "(p ∧ q").isError),
("K without agent is an error", (parseFormula "K[] p").isError),
("temporal rejected", (parseFormula "G p").isError),
("error names a position", match parseFormula "p ∧" with | .error e => e.startsWith "position" | _ => false)
```

Plus a Plausible property `∀ f ∈ supported fragment, parseFormula f.toString = .ok f`, using a generator restricted to the constructors above (follow the generator style in `Tests/PropertyHelpers.lean`).

- [ ] **Step 2: Register** `Tests.DynamicInput` in `Tests/Main.lean` (import, case list, count). Run `lake test`; expected: build fails, `parseFormula` unknown.
- [ ] **Step 3: Implement** `tokenize` and `parseFormula` in `Gamen/Input.lean`: recursive descent over the token list, recursion on the list's length (no `partial def`). Add `import Gamen.Input` to `Gamen.lean` if the library root imports modules explicitly.
- [ ] **Step 4: Run** `lake test`. Expected: all `DynamicInputTests` cases pass, existing cases unchanged.
- [ ] **Step 5: Plant a bug** (swap the `∧`/`∨` precedence), confirm the precedence test fails, revert.
- [ ] **Step 6: Commit** `Add a text parser for epistemic formulas`.

### Task 2: ATL-D formula parser and round-trip printer

**Files:**
- Create: `Gamen/Atl/DynamicInput.lean`
- Test: `Tests/DynamicInput.lean`

**Interfaces:**
- Consumes: `Gamen.Input.tokenize` (Task 1)
- Produces:
  - `Gamen.Atl.Dynamic.parseDFormula : String → Except String DFormula`
  - `Gamen.Atl.Dynamic.DFormula.toInput : DFormula → String`

`DFormula.toString` prints `K_{a}φ`, which is ambiguous for multi-letter agents (`K_Dp`), so it can't be the student syntax. `toInput` prints `K[a]φ` instead and otherwise matches `toString`: `has(a,α)`; `⟨⟨a,b⟩⟩Xφ`, `G`, `F`; `⟨⟨A⟩⟩(φ U ψ)`, `R`; updates `[φ:α→{A},{B}]+ψ` and `]-ψ` (the `,{B}` part omitted when `B` is empty; several clauses separated by `,` as `updatesToString` does). ASCII: `<<A>>`, `->`. `⟨⟨⟩⟩` (empty coalition) is allowed.

- [ ] **Step 1: Write the failing tests:**

```lean
("has", parseDFormula "has(attending,order)" == .ok (.has "attending" "order")),
("coalition F", parseDFormula "⟨⟨patient⟩⟩F treated" == .ok (.canEventually ["patient"] (.atom "treated"))),
("ascii coalition", parseDFormula "<<a,b>>X p" == .ok (.canNext ["a","b"] (.atom "p"))),
("until", parseDFormula "⟨⟨a⟩⟩(p U q)" == .ok (.canUntil ["a"] (.atom "p") (.atom "q"))),
("grant", parseDFormula "[referred:order→{a}]+⟨⟨a⟩⟩F treated"
   == .ok (.grant (.cons (.atom "referred") "order" ["a"] [] .nil) (.canEventually ["a"] (.atom "treated")))),
("grant with informed", parseDFormula "[⊤:order→{incoming},{incoming}]+K[pharmacist]has(incoming,order)" |>.isOk),
("K multi-letter agent", parseDFormula "K[pharmacist]p" == .ok (.knows "pharmacist" (.atom "p"))),
("unknown operator", (parseDFormula "□p").isError)
```

(`⊤` here: if `DFormula` has no `top`, accept `⊤` as `¬⊥` and say so in the docstring; the round-trip generator then never produces `¬⊥` from `⊤`.) Plus the property `parseDFormula (toInput f) = .ok f` over random `DFormula`s, including update lists of length 1-2.

- [ ] **Step 2: Run** `lake test`; expected: build fails, `parseDFormula` unknown.
- [ ] **Step 3: Implement** both functions; the mutual `DFormula`/`UpdateList` printer is structural.
- [ ] **Step 4: Run** `lake test`; expected: pass.
- [ ] **Step 5: Plant a bug** (drop the informed set in `toInput`), confirm the round-trip property fails, revert.
- [ ] **Step 6: Commit** `Add a text parser and round-trip printer for ATL-D formulas`.

### Task 3: Scenario format, models per mode, and the grader

**Files:**
- Create: `Widgets/Dynamic/Scenario.lean`, `Widgets/Dynamic/Grade.lean`
- Test: `Tests/DynamicExplorer.lean` (create, register in `Tests/Main.lean`)

**Interfaces:**
- Consumes: `parseFormula`, `parseDFormula`; `Gamen.EpistemicJson.decodeModel : Json → Except EpiSpecError EpistemicModel`; `Gamen.CgsJson.decodeDyn : Json → Except CgsSpecError DynModel`; `mkActionModel`, `productUpdate`, `eSatisfies`, `eAccessible`; `Atl.Dynamic.dclauses`, `updateModel`, `dsat`.
- Produces (namespace `Gamen.Widgets.Dynamic`):

```lean
inductive Mode | epistemic | atlD            -- room for `angelsDemons` later
structure WorldPos where name : String; x : Float; y : Float
inductive QuestionKind
  | clickWorlds (formula : String)            -- answer: the worlds where it holds, after the update
  | reachGoal (goal : String) (atWorld : Option String)  -- `none`: at every world
  | writeFormula (target : List String)       -- answer: any formula true exactly there
structure Hint where answer : String; text : String   -- `answer` in normalized form (below)
structure Question where id : String; prompt : String; kind : QuestionKind; answer : String; hints : List Hint := []
structure Scenario where
  id : String; title : String; setup : String; mode : Mode
  model : Json; controls : Json; layout : List WorldPos
  checks : List String := []                  -- formulas whose truth sets are always shown
  questions : List Question
/-- A model the explorer can evaluate on, whatever the logic. -/
structure Evaluable where
  worlds : List String
  edges : List (String × String × String)     -- (agent or action label, from, to), for drawing
  facts : List (String × List String)         -- world ↦ true atoms
  truthSet : String → Except String (List String)    -- parse + evaluate, sorted
  access : String → String → List String      -- agent, world ↦ indistinguishable worlds
  notes : List String := []                   -- e.g. reasonableness-rule messages
def Scenario.ofJson : Json → Except String Scenario
def Scenario.before : Scenario → Except String Evaluable
def Scenario.after : Scenario → (selected : List String) → Except String Evaluable
inductive Answer | worlds (ws : List String) | formula (text : String) | controls (selected : List String)
structure Feedback where correct : Bool; message : String
def gradeAnswer (sc : Scenario) (selected : List String) (q : Question) (a : Answer) : Except String Feedback
```

Controls JSON, per mode (the `selected` list holds control keys):
- **epistemic:** `{"events": [...], "pre": {"event": "formula"}, "post": {...}, "toggleable": ["N","D"], "observers": ["D"]}`. Key = agent name; a selected agent *observes* (identity relation over events), an unselected one sees every event as possible (full relation). Agents not in `toggleable` take their fixed role from `observers`. Build with `mkActionModel`, then `productUpdate`.
- **atlD:** `{"mode": "perfect" | "subjective" | "objective", "clauses": [{"label", "kind": "grant" | "revoke", "cond", "action", "agents", "informed"}]}`. Key = clause label. Selected clauses apply in listed order, consecutive same-kind clauses as one update (`dclauses` then `updateModel`). For every (agent, state) where a revoke was skipped by the reasonableness rule, add a note naming them (compare `d` before and after).

Normalized answers: worlds as a sorted comma-joined list; controls likewise; formulas as their text.

Grading:
- `clickWorlds`: clicked set vs `truthSet formula` on `after`.
- `writeFormula`: student's `truthSet` vs `target` (so equivalent formulas pass).
- `reachGoal`: build `after` with the student's selection; goal true at `atWorld` (or every world). A parse or evaluation error is `.error`, never `correct := false`.
- Message: first a `Hint` whose `answer` matches the normalized answer; otherwise generated: "true at X but not at Y" naming the differing worlds; when the formula is `K[a]φ` (or `knows`) and a clicked world w is wrong, also name a world in `access a w` where φ fails.

Test helpers (local to `DynamicExplorerTests`): `grade q a := (gradeAnswer sc ["D"] q a).map (·.correct)` and `gradeMsg q a := match gradeAnswer sc ["D"] q a with | .ok f => f.message | .error e => e`.

- [ ] **Step 1: Write the failing tests**, building a tiny inline scenario (two worlds, agents N and D, events `sent`/`lost` with `pre sent = p`):

```lean
("before has 2 worlds", ((sc.before).map (·.worlds.length)) == .ok 2),
("after, D observes: 3 worlds", ((sc.after ["D"]).map (·.worlds)) == .ok ["w1×lost","w1×sent","w2×lost"]),
("K[D]p ∧ ¬K[N]K[D]p exactly at w1×sent", ((sc.after ["D"]).bind (·.truthSet "K[D]p ∧ ¬K[N]K[D]p")) == .ok ["w1×sent"]),
("clickWorlds correct", grade q1 (.worlds ["w1×sent"]) == .ok true),
("clickWorlds wrong names the witness", (gradeMsg q1 (.worlds ["w1×sent","w1×lost"])).contains "w1×lost"),
("writeFormula equivalent passes", grade q2 (.formula "¬¬K[D]p") == grade q2 (.formula "K[D]p")),
("unknown agent is an error, not false", (sc.after ["D"] |>.bind (·.truthSet "K[X]p")).isError),
("parse error is an error, not wrong", (gradeAnswer sc ["D"] q2 (.formula "K[D")).isError),
("hint matched before generated", gradeMsg q1 (.worlds []) == "<the hint text stored for the empty answer>")
```

and one ATL-D case built from a small `decodeDyn` model: a revoke that would empty `d(a, s)` leaves a note mentioning `a` and `s`.

- [ ] **Step 2: Run** `lake test`; expected: build fails.
- [ ] **Step 3: Implement** `Scenario.lean` then `Grade.lean`.
- [ ] **Step 4: Run** `lake test`; expected: pass.
- [ ] **Step 5: Plant a bug** (grade `writeFormula` by string equality), confirm the "equivalent passes" test fails, revert.
- [ ] **Step 6: Commit** `Add the scenario format and grader for the dynamic explorer`.

### Task 4: Explorer state machine

**Files:**
- Create: `Widgets/Dynamic/Explorer.lean`
- Test: `Tests/DynamicExplorer.lean`

**Interfaces:**
- Consumes: Task 3's `Scenario`, `Evaluable`, `Answer`, `Feedback`, `gradeAnswer`.
- Produces:

```lean
structure ExplorerState where
  scenario : Scenario
  selected : List String            -- current control keys
  applied : Bool := false           -- showing the after model
  question : Nat := 0
  clicked : List String := []
  formulaText : String := ""
  feedback : Option Feedback := none
  message : Option String := none   -- errors and notes, shown verbatim
  deriving ToJson, FromJson
inductive Event
  | toggleControl (key : String) | apply | reset
  | clickWorld (w : String) | setFormula (text : String)
  | submit | nextQuestion | prevQuestion
  deriving ToJson, FromJson
def ExplorerState.init (sc : Scenario) : ExplorerState
def step (s : ExplorerState) (e : Event) : ExplorerState
def view (s : ExplorerState) : Json
```

Rules: `step` is total; every `Except` error lands in `message`. `toggleControl` after `apply` un-applies (back to the before model) and clears `clicked` and `feedback`. `clickWorld` toggles membership, and only for worlds of the model currently shown; a click on an unknown world sets `message`. `submit` for `clickWorlds`/`writeFormula` questions before `apply` sets `message := "Apply the update first."` when the question is about the after model (all `clickWorlds` and `writeFormula` questions are). For `reachGoal`, `submit` grades the current `selected`. `nextQuestion`/`prevQuestion` clamp to range and clear `clicked`, `formulaText`, `feedback`. `apply` copies `after`'s `notes` into `message`; an update with no surviving world sets `message := "No world survives this update."` and stays on the before model.

`view` emits: `title`, `setup`, `controls` (key, label, on/off), `model` (`worlds` with `x`,`y`,`facts`,`clicked`; `edges` with label), `checks` (formula text and truth set), `question` (index, count, prompt, kind), `formulaText`, `feedback`, `message`, `applied`. Positions come from `layout`; a world missing from `layout` gets a fallback position on a circle and a `message` note naming it (a data bug, visible but not fatal).

- [ ] **Step 1: Write the failing tests** (event replays on the Task 3 inline scenario):

```lean
("submit before apply asks to apply", (replay [.submit]).message == some "Apply the update first."),
("apply then correct click grades true", (replay [.toggleControl "D", .apply, .clickWorld "w1×sent", .submit]).feedback.map (·.correct) == some true),
("toggle after apply un-applies", (replay [.toggleControl "D", .apply, .toggleControl "N"]).applied == false),
("click unknown world is a message", (replay [.toggleControl "D", .apply, .clickWorld "w9"]).message.isSome),
("next past last clamps", (replay (List.replicate 20 .nextQuestion)).question == sc.questions.length - 1),
("empty update keeps before", (replayOn noSurvivor [.apply]).applied == false),
("state round-trips JSON", (fromJson? (toJson s) : Except String ExplorerState) |>.isOk)
```

where `replay es := es.foldl step (ExplorerState.init sc)`.

- [ ] **Step 2: Run** `lake test`; expected: build fails.
- [ ] **Step 3: Implement.**
- [ ] **Step 4: Run** `lake test`; expected: pass.
- [ ] **Step 5: Plant a bug** (`toggleControl` keeps `applied`), confirm the un-apply test fails, revert.
- [ ] **Step 6: Commit** `Add the dynamic explorer's state machine`.

### Task 5: Widget, RPC method, and JS renderer

**Files:**
- Create: `Widgets/Dynamic/Widget.lean`, `Widgets/js/dynamicExplorer.js`
- Test: `Tests/DynamicExplorer.lean`

**Interfaces:**
- Consumes: `ExplorerState`, `Event`, `step`, `view`.
- Produces:
  - `structure StepParams where state : ExplorerState; event : Event` and `structure StepResult where state : ExplorerState; view : Json` (both `ToJson`, `FromJson`, `RpcEncodable` by deriving)
  - root `@[server_rpc_method] def dynamicExplorerStep (p : StepParams) : RequestM (RequestTask StepResult)` (pure: `RequestM.pureTask` of `step` then `view`)
  - `@[widget_module] def Gamen.Widgets.DynamicExplorerWidget : Component StepResult` with `javascript := include_str "../js/dynamicExplorer.js"` (adjust the path form to match `KripkeExplorer`'s `include_str "js" / "interactiveSvgQuiet.js"` from this file's directory)
  - `def Gamen.Widgets.dynamicExplorer (sc : Scenario) : Html`, the initial `StepResult` of `ExplorerState.init sc`

The JS imports only `react`, `react/jsx-runtime` (or `React.createElement`) and `useRpcSession`/`EnvPosContext` from `@leanprover/infoview`, as `Widgets/js/interactiveSvgQuiet.js` does. It holds the `StepResult` in React state, draws `view.model` as SVG (worlds as labeled circles, facts beneath, edges labeled by agent; clicked worlds highlighted), renders controls as checkboxes, an "Apply"/"Reset" pair, the question with a text input for `writeFormula` and a "Check" button, feedback in green/red, `message` in a neutral box. Every user action is one `rs.call('dynamicExplorerStep', {state, event})`. No polling.

- [ ] **Step 1: Write the failing test:** `("rpc step = step + view", (rpcPure p).view == view (step p.state p.event))`, where `rpcPure` is the pure function the RPC method wraps (expose it as `stepResult : StepParams → StepResult`).
- [ ] **Step 2: Run** `lake test`; expected: build fails.
- [ ] **Step 3: Implement** the Lean side and the JS.
- [ ] **Step 4: Run** `lake build && lake test`; expected: pass, `KripkeExplorer` widget tests unchanged.
- [ ] **Step 5: Manual infoview check** (Brian, in VS Code, since the infoview can't be driven from the CLI): a scratch file with `#html dynamicExplorer DynamicExplorerTests.sc`; check that a click, a checkbox, Apply, typing a formula and Check each update the display. Record the result in the commit message.
- [ ] **Step 6: Commit** `Add the dynamic explorer widget`.

### Task 6: Scenario 1 (handoff) and the epistemic notebook

**Files:**
- Create: `data/scenarios/handoff.json`, `Widgets/Dynamic/Library.lean`, `Notebooks/DynamicEpistemic.lean`
- Test: `Tests/DynamicScenarios.lean` (create, register)

**Interfaces:**
- Consumes: `Scenario.ofJson`, `dynamicExplorer`, `gradeAnswer`.
- Produces:
  - `Gamen.Widgets.Dynamic.Library.handoff : Except String Scenario` (`Scenario.ofJson` of the `include_str`'d file, parsed with `Json.parse`)
  - `allScenarios : List (String × Except String Scenario)`
  - `Gamen.Widgets.dynamicExplorerOr : Except String Scenario → Html`: the explorer, or a visible error paragraph naming the file (no `panic!`); notebooks call this one

Content (spec decision 3.1): worlds `w1` (`p`: potassium high) and `w2` (`¬p`); N and D can't tell them apart; events `sent` (pre `p`) and `lost` (no precondition, i.e. `⊤`); toggleable observers N and D, initially D. Questions, 4-5 of them, mixing kinds: click where `K[D]p ∧ ¬K[N]K[D]p` holds; write a formula true exactly where the page was lost and potassium is high; reach the goal `K[D]p ∧ K[N]K[D]p` at `w1×sent` by changing observers; one more click question on `K[N]p`. Each with at least one hint for the most likely wrong answer.

The notebook follows `Notebooks/Ch1HealthObligations.lean`: header on how to use the file, prose in `/-! … -/` introducing action models (cite Lorini, Perrotin & Schwarzentruber, KR 2022, Defs 7-9, as `Gamen/ActionModel.lean` does), then `#html dynamicExplorerOr Library.handoff`.

- [ ] **Step 1: Write the failing tests** in `Tests/DynamicScenarios.lean`:
  - every entry of `allScenarios` decodes;
  - for every question, the stored `answer` grades `correct = true`, and every hint's `answer` grades `correct = false` with exactly that hint's text;
  - the library-level claim, independent of the grader: build the product with `mkActionModel`/`productUpdate` directly and assert `eSatisfies m "w1×sent" (K[D]p ∧ ¬K[N]K[D]p) = .ok true`.
- [ ] **Step 2: Run** `lake test`; expected: fails (no data file).
- [ ] **Step 3: Write** the data file, `Library.lean`, and the notebook.
- [ ] **Step 4: Run** `lake build && lake test`; expected: pass.
- [ ] **Step 5: Plant a bug** (make `lost` visible to N in the data), confirm a test fails, revert.
- [ ] **Step 6: Commit** `Add the handoff scenario and the dynamic epistemic notebook`.

### Task 7: Scenarios 2 and 3 and the ability notebook

**Files:**
- Create: `data/scenarios/would-if-could.json`, `data/scenarios/safety-access.json`, `Notebooks/DynamicAbility.lean`
- Modify: `Widgets/Dynamic/Library.lean`, `Tests/DynamicScenarios.lean`

**Interfaces:**
- Produces: `Library.wouldIfCould`, `Library.safetyAccess`, both in `allScenarios`.

Content (spec 3.2, 3.3), ATL-D mode `perfect`, models in `decodeDyn` format, 3-5 states each:
- **Would if could:** the patient lacks a prerequisite action (referral); candidate grant clauses include the right one and at least one distractor; questions: click where `⟨⟨patient⟩⟩F treated` holds before and after; reach the goal by choosing grants (answer: the smallest grant, confirmed in the test with `Atl.UpdateSearch.boundedUpdate`); write a formula for "the patient has the referral action".
- **Safety versus access:** a revoke that prevents a harmful action also removes the emergency action at one state, and at another state the revoke is stopped by the reasonableness rule; questions make the student find both.

Notebook prose introduces `⟨⟨A⟩⟩`, `has`, `X`/`G`/`F`/`U`, grant and revoke before any question uses them, citing Galimullin, Grosinger & Mittelmann, KR 2026, with definition numbers taken from `Gamen/Atl/Dynamic.lean`'s docstring (Defs 1-4, Algorithm 1). A closing placeholder section says scenario 4 (pancreatic cancer) will follow; no clinical claim in it.

- [ ] **Step 1: Extend the tests:** both scenarios decode; answer-key checks as in Task 6; library-level claims via `dsat` directly (goal false before, true after the right grant); `boundedUpdate` finds no grant smaller than the stored answer; the safety scenario's reasonableness note names the right agent and state.
- [ ] **Step 2: Run** `lake test`; expected: fails.
- [ ] **Step 3: Write** the data files, library entries and notebook.
- [ ] **Step 4: Run** `lake build && lake test`; expected: pass.
- [ ] **Step 5: Plant a bug** (drop the reasonableness exception in the data's expectations), confirm a test fails, revert.
- [ ] **Step 6: Commit** `Add the grant and revoke scenarios and the dynamic ability notebook`.

### Task 8: Scenario 5 (shift-change handoff) and the capstone notebook

**Files:**
- Create: `data/scenarios/shift-change.json`, `Notebooks/DynamicCapstone.lean`
- Modify: `Widgets/Dynamic/Library.lean`, `Tests/DynamicScenarios.lean`

**Interfaces:**
- Produces: `Library.shiftChange` in `allScenarios`.

- [ ] **Step 1: Confirm the semantics first.** Read `Gamen/Atl/Dynamic.lean`'s docstring (ATEL-D section, `⟨⟨A⟩⟩` under imperfect information) and `Tests/AtlDynamic.lean`'s ATEL-D cases. Write down, in the notebook prose draft, which `IrMode` the scenario uses and why. If what's implemented can't express "the pharmacist does not know the incoming clinician can order" (`¬K[pharmacist]has(incoming,order)` after a grant whose informed set excludes the pharmacist), stop and report rather than bending the scenario.
- [ ] **Step 2: Write the failing tests:** decodes; answer keys; library-level claims via `dsat` on the decoded model: after `[⊤:order→{incoming},{incoming}]+` then the revoke from `outgoing`, `has(incoming,order) ∧ K[incoming]has(incoming,order) ∧ ¬K[pharmacist]has(incoming,order)` holds at the start state; and with the pharmacist added to the informed set, `K[pharmacist]has(incoming,order)` holds.
- [ ] **Step 3: Run** `lake test`; expected: fails.
- [ ] **Step 4: Write** the data file (controls: the grant clause with an informed set the student can widen, as a separate clause label, and the revoke clause), the library entry and the notebook. The prose pairs this with scenario 1: there a fact reached only some people; here an ability changes hands without everyone knowing.
- [ ] **Step 5: Run** `lake build && lake test`; expected: pass.
- [ ] **Step 6: Commit** `Add the shift-change capstone scenario and notebook`.

### Task 9: Whole-branch checks and records

**Files:**
- Modify: `NEXT.md`, `PORTING.md` only if it lists notebooks/widgets (check first)

- [ ] **Step 1: Run** `lake build && lake test`; expected: all pass. Run `python3 tools/compare/compare.py` only if any file under `Gamen/` that `Validate` imports changed (it should not have); expected: no new disagreement.
- [ ] **Step 2: Axiom audit** is not needed (no `native_decide` claims added); confirm with `grep -rn native_decide Notebooks/Dynamic*.lean` returning nothing.
- [ ] **Step 3: Update `NEXT.md`:** the notebook/widget item is done for scenarios 1, 2, 3, 5; scenario 4 waits for the pancreatic sources (PDFs to download manually into `~/Downloads/pancreatic-lit/`) and needs its own plan (SFormula parser, strategy extraction); follow-up: parallel ATL/ATL-D pancreatic notebook.
- [ ] **Step 4: Commit** `Record the dynamic explorer in NEXT.md`.
