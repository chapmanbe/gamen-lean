# DL-BET (belief, evidence and trust) Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Add the logic DL-BET (Liu & Lorini, PRIMA 2017) to gamen-lean as a library module plus a Lean-only `evidence_trust_check` request (protocol 8).

**Architecture:** A self-contained module `Gamen/EvidenceTrust.lean` with its own formula type `EFormula` (the 30-constructor `Formula` is untouched). Sets of worlds are bitmasks; the model checker `sat` returns the mask of satisfying worlds; each of the four update events is a pure model transformer that takes the already-computed mask `⟦φ⟧`, so `sat` stays structurally recursive. The JSON decoder and handler live in `Validate/EvidenceTrust.lean` and are dispatched from `Validate/Core.lean`.

**Tech Stack:** Lean 4.34.0 (core `Rat`, `Std`, `Lean.Json`), `lake build` / `lake test`.

**Spec:** `docs/superpowers/specs/2026-10-14-evidence-trust-design.md` (read it first; it records two places where the text extract of the paper is wrong and the PDF governs: C8 is `∅ ∉ C`, and Def 5's guard is `K̂_i φ`). The paper: `~/Projects/Logic/Bergen/Bergen/lit/pdfs/liu2017belief.pdf`; use `pdftoppm -f N -l N -r 110 -png` and read the image for any definition, never trust `pdftotext` for overlines and slashes.

**One deliberate deviation from the spec:** `reason i φ` (`R_i φ`) is a primitive `EFormula` constructor evaluated directly by `reasonAt`, not a derived disjunction; the spec's "evaluated directly, cross-checked against the literal disjunction" is implemented by `reasonLiteral` in the library and a test. The JSON `reason` formula maps to the constructor.

## Global Constraints

- American English everywhere (comments, docs, messages).
- No `sorry`. No `partial def` in the library (`Gamen/EvidenceTrust.lean`); the JSON formula decoder is `partial` (recursion through JSON lookups) and says so in its docstring, as `decodeDFormula` does.
- `Except`, never `panic!`; no silent defaults (belief required, unknown keys rejected).
- Cite definition numbers and page numbers checked against the PDF; claims not read are marked `[ASSERTED]`.
- Before trusting a green run, plant a bug and confirm a test catches it (Task 3 lists the six mutations).
- `lake` lives in `~/.elan/bin`: run `export PATH="$HOME/.elan/bin:$PATH"` first.
- `lake test` takes ~2 minutes: run it in the background or with a long timeout, never `sleep`.
- Keep `tools/compare/compare.py` at the known 103 DISAGREE (this change touches no existing request).
- Lean-only: nothing is mirrored to gamen-hs; papers are never committed.
- Commit messages end with `Co-Authored-By: Claude Sonnet 5.5 <noreply@anthropic.com>`.

## Review Focus

Inputs the spec implies and a user will hit; each is pinned by a test in the task named.

1. An update formula with `then` missing must be `malformed_spec`, never a silent `⊤` (Task 4, wire test).
2. A quota written as a decimal string (`"0.75"`) or a JSON number (`0.75`) must be rejected with a clear code, not rounded (Task 4).
3. 21 worlds or 9 agents must be `bad_size`, not a slow request or an out-of-memory (Task 4).
4. A belief or evidence entry naming the same class twice must be `malformed_spec`, not last-wins (Task 4).
5. Self-trust (`i = j`) is legal in the paper and must work: `announce i φ` with `i` trusting itself (Task 3, validities (5)-(7) run over `i = j`).
6. A source that announces a falsehood still produces evidence for a trusting listener, and a source nobody trusts produces none (Task 2).

## File Structure

| File | Responsibility |
|---|---|
| `Gamen/EvidenceTrust.lean` (new) | `Mask`, `Sets`, `ESM`, `ESM.validate`, `EFormula`, `reasonAt`, the four update transformers, `sat`, `holdsAt`, `validIn`, `reasonLiteral` |
| `Tests/EvidenceTrust.lean` (new) | constructor probes, the §2.4 example, random-ESM property tests |
| `Validate/EvidenceTrust.lean` (new) | JSON decoder (`EtJson`), `evidenceTrustCheck` handler |
| `Tests/ValidateEvidenceTrust.lean` (new) | wire contract |
| `Validate/Core.lean`, `Validate.lean`, `Gamen/Protocol.lean`, `Tests/ValidateVersion.lean`, `Tests/Main.lean`, `Gamen.lean`, `PORTING.md` | registration, docs, protocol 8 |
| `docs/assessment/adversarial-review-evidence-trust-<date>.md` (new) | the review record |

---

### Task 1: The model and its constructor

**Files:**
- Create: `Gamen/EvidenceTrust.lean` (first half)
- Create: `Tests/EvidenceTrust.lean` (helpers and constructor probes)
- Modify: `Gamen.lean` (add `import Gamen.EvidenceTrust` after `import Gamen.AngelsDemons`), `Tests/Main.lean` (import and register `EvidenceTrustTests.cases`)

**Interfaces:**
- Produces: `Mask`, `Mask.mem/full/subset`, `Sets`, `Sets.ins/del`, `ESM` (fields `n agents valuation E D S C T`), `ESM.e/d/s/c/t`, `ESM.validate : ESM → Except String Unit`, `ESM.worlds/agentIds/nAgents`. Error messages start with `C1` … `C10` or `bad_type` or `shape`.

- [ ] **Step 1: Write the failing test.** Create `Tests/EvidenceTrust.lean` with the helpers and the constructor probes (compile-checked against the library below). Every probe starts from the two-world `base` model and breaks one condition.

```lean
import Gamen.EvidenceTrust

/-!
# DL-BET tests (`Gamen/EvidenceTrust.lean`)

Expected values come from Liu & Lorini (PRIMA 2017) or are hand-derived, never from the code under test.
-/

namespace EvidenceTrustTests

open Gamen.EvidenceTrust

def ok {α} (r : Except String α) : Bool := match r with | .ok _ => true | .error _ => false
def errStarts {α} (r : Except String α) (pre : String) : Bool :=
  match r with | .error e => e.startsWith pre | .ok _ => false

/-! ## A two-world, two-agent base model for constructor probes -/
def base : ESM where
  n := 2
  agents := #["a", "b"]
  valuation := #[["p"], []]
  E := #[#[3, 3], #[3, 3]]
  D := #[#[3, 3], #[3, 3]]
  S := #[#[#[[], []], #[[], []]], #[#[[], []], #[[], []]]]
  C := #[#[#[[], []], #[[], []]], #[#[[], []], #[[], []]]]
  T := #[#[(0, 1), (0, 1)], #[(0, 1), (0, 1)]]

def constructorCases : List (String × Bool) := [
  ("the base model is an ESM", ok base.validate),
  ("C1: a relation that is not an equivalence",
    errStarts ({ base with E := #[#[3, 2], #[3, 3]] }.validate) "C1"),
  ("C2: no possible world",
    errStarts ({ base with D := #[#[0, 0], #[3, 3]] }.validate) "C2"),
  ("C3: belief outside the information set",
    errStarts ({ base with E := #[#[1, 2], #[3, 3]], D := #[#[3, 3], #[3, 3]] }.validate) "C3"),
  ("C4: belief differs inside one class",
    errStarts ({ base with D := #[#[1, 3], #[3, 3]] }.validate) "C4"),
  ("C5: evidence differs inside one class",
    errStarts ({ base with S := #[#[#[[1], []], #[[], []]], #[#[[], []], #[[], []]]],
                           C := #[#[#[[1], [1]], #[[], []]], #[#[[], []], #[[], []]]] }.validate) "C5"),
  ("C6: trust differs inside one class",
    errStarts ({ base with C := #[#[#[[], []], #[[1], []]], #[#[[], []], #[[], []]]] }.validate) "C6"),
  ("C7: a trusted set outside the information set",
    errStarts ({ base with E := #[#[1, 2], #[3, 3]], D := #[#[1, 2], #[3, 3]],
                           C := #[#[#[[], []], #[[], [3]]], #[#[[], []], #[[], []]]] }.validate) "C7"),
  ("C8: trusting someone about the empty set (the PDF's ∅ ∉ C, not the extract's ∈)",
    errStarts ({ base with C := #[#[#[[], []], #[[0], [0]]], #[#[[], []], #[[], []]]] }.validate) "C8"),
  ("C9: evidence from a source one does not trust",
    errStarts ({ base with S := #[#[#[[], []], #[[1], [1]]], #[#[[], []], #[[], []]]] }.validate) "C9"),
  ("C10: the type differs inside one class",
    errStarts ({ base with T := #[#[(0, 1), (1, 1)], #[(0, 1), (0, 1)]] }.validate) "C10"),
  ("bad_type: a quota below 1/2, and cautiousness above the number of agents",
    errStarts ({ base with T := #[#[(0, 1/4), (0, 1/4)], #[(0, 1), (0, 1)]] }.validate) "bad_type"
      && errStarts ({ base with T := #[#[(3, 1), (3, 1)], #[(0, 1), (0, 1)]] }.validate) "bad_type")]




def cases : List (String × Bool) := constructorCases

end EvidenceTrustTests
```

- [ ] **Step 2: Register the test and run it to see it fail.** In `Tests/Main.lean` add `import Tests.EvidenceTrust` after `import Tests.ValidateEpistemic`, and append `++ EvidenceTrustTests.cases` after `AngelsDemonsTests.randomCases` in the `for (name, ok) in ...` list, and `+ EvidenceTrustTests.cases.length` in the count expression (follow how `ValidateEpistemicTests.cases` appears in both places).

Run: `export PATH="$HOME/.elan/bin:$PATH"; lake build Tests.EvidenceTrust 2>&1 | tail -5`
Expected: FAIL, `unknown module Gamen.EvidenceTrust`.

- [ ] **Step 3: Write the library's first half.** Create `Gamen/EvidenceTrust.lean`:

```lean
/-!
# Gamen.EvidenceTrust

DL-BET: the dynamic logic of belief, evidence and trust of Liu & Lorini, *Reasoning About
Belief, Evidence and Trust in a Multi-agent Setting*, PRIMA 2017. Lean-only. Issue #3, item 4.
-/
namespace Gamen
namespace EvidenceTrust

/-- A set of worlds as a bitmask: world `w` is bit `w`. -/
abbrev Mask := Nat

def Mask.mem (m : Mask) (w : Nat) : Bool := m.testBit w
def Mask.full (n : Nat) : Mask := (1 <<< n) - 1
def Mask.subset (a b : Mask) : Bool := a &&& b == a

/-- A set of sets of worlds, kept sorted and duplicate-free so `==` is set equality. -/
abbrev Sets := List Mask

def Sets.ins (m : Mask) (l : Sets) : Sets :=
  if l.contains m then l else (m :: l).mergeSort (· ≤ ·)

def Sets.del (m : Mask) (l : Sets) : Sets := l.filter (· != m)

/-- Evidence source model (Def 1). Agents and worlds are indexed from 0; `E i w` is agent
`i`'s information set at `w`, `D i w` its belief set, `S i j w` the evidence `j` gave `i`,
`C i j w` the sets `i` trusts `j` about, `T i w` the type (cautiousness, quota). -/
structure ESM where
  n : Nat
  agents : Array String
  valuation : Array (List String)
  E : Array (Array Mask)
  D : Array (Array Mask)
  S : Array (Array (Array Sets))
  C : Array (Array (Array Sets))
  T : Array (Array (Nat × Rat))

def ESM.nAgents (m : ESM) : Nat := m.agents.size
def ESM.worlds (m : ESM) : List Nat := List.range m.n
def ESM.agentIds (m : ESM) : List Nat := List.range m.nAgents

def ESM.e (m : ESM) (i w : Nat) : Mask := (m.E[i]?.bind (·[w]?)).getD 0
def ESM.d (m : ESM) (i w : Nat) : Mask := (m.D[i]?.bind (·[w]?)).getD 0
def ESM.s (m : ESM) (i j w : Nat) : Sets := (((m.S[i]?).bind (·[j]?)).bind (·[w]?)).getD []
def ESM.c (m : ESM) (i j w : Nat) : Sets := (((m.C[i]?).bind (·[j]?)).bind (·[w]?)).getD []
def ESM.t (m : ESM) (i w : Nat) : Nat × Rat := (m.T[i]?.bind (·[w]?)).getD (0, 1)

/-- Check the conditions of Def 1 (C1-C10, with C8 as printed in the PDF: `∅ ∉ C`) and the
ranges the language needs. The message starts with the name of the violated condition. -/
def ESM.validate (m : ESM) : Except String Unit := do
  let ids := m.agentIds
  let ws := m.worlds
  let full := Mask.full m.n
  unless m.valuation.size == m.n do throw "shape: valuation has the wrong length"
  unless m.E.size == m.nAgents && m.D.size == m.nAgents && m.T.size == m.nAgents
      && m.S.size == m.nAgents && m.C.size == m.nAgents do throw "shape: per-agent tables have the wrong length"
  for i in ids do
    unless (m.E[i]!).size == m.n && (m.D[i]!).size == m.n && (m.T[i]!).size == m.n do
      throw "shape: a per-world table has the wrong length"
    unless (m.S[i]!).size == m.nAgents && (m.C[i]!).size == m.nAgents do
      throw "shape: an evidence or trust table has the wrong length"
    for j in ids do
      unless (m.S[i]![j]!).size == m.n && (m.C[i]![j]!).size == m.n do
        throw "shape: an evidence or trust table has the wrong length"
  for i in ids do
    for w in ws do
      unless Mask.subset (m.e i w) full do throw s!"C1: E {m.agents[i]!} {w} names a world out of range"
      unless (m.e i w).testBit w do throw s!"C1: E {m.agents[i]!} is not reflexive at world {w}"
      for v in ws do
        if (m.e i w).testBit v then
          unless (m.e i v).testBit w do throw s!"C1: E {m.agents[i]!} is not symmetric ({w},{v})"
          unless m.e i w == m.e i v do throw s!"C1: E {m.agents[i]!} is not transitive ({w},{v})"
          unless m.d i w == m.d i v do throw s!"C4: D {m.agents[i]!} differs on worlds {w},{v} of one class"
          unless m.t i w == m.t i v do throw s!"C10: the type of {m.agents[i]!} differs on worlds {w},{v} of one class"
          for j in ids do
            unless m.s i j w == m.s i j v do throw s!"C5: S differs on worlds {w},{v} of one class"
            unless m.c i j w == m.c i j v do throw s!"C6: C differs on worlds {w},{v} of one class"
      if m.d i w == 0 then throw s!"C2: {m.agents[i]!} has no possible world at {w}"
      unless Mask.subset (m.d i w) (m.e i w) do throw s!"C3: D {m.agents[i]!} {w} is not inside E"
      let (x, y) := m.t i w
      if x > m.nAgents then throw s!"bad_type: cautiousness {x} of {m.agents[i]!} exceeds the number of agents"
      if y < (1 : Rat) / 2 || y > 1 then throw s!"bad_type: quota {y} of {m.agents[i]!} is outside [1/2, 1]"
      for j in ids do
        for X in m.c i j w do
          unless Mask.subset X (m.e i w) do throw s!"C7: a trusted set of {m.agents[i]!} is not inside E at {w}"
          if X == 0 then throw s!"C8: {m.agents[i]!} trusts {m.agents[j]!} about the empty set at {w}"
        for X in m.s i j w do
          unless (m.c i j w).contains X do throw s!"C9: {m.agents[i]!} has evidence from {m.agents[j]!} it does not trust, at {w}"
```

Close the file for now with:

```lean
end EvidenceTrust
end Gamen
```

(Task 2 removes these two lines and appends.) The test file does not use `sat` yet, so this compiles on its own. Add `import Gamen.EvidenceTrust` to `Gamen.lean`.

- [ ] **Step 4: Run the test.**

Run: `lake build 2>&1 | tail -3; lake test 2>&1 | grep -E "✗|passed"`
Expected: no `✗`; all constructor probes pass.

- [ ] **Step 5: Commit.**

```bash
git add Gamen/EvidenceTrust.lean Tests/EvidenceTrust.lean Gamen.lean Tests/Main.lean
git commit -m "Add the DL-BET evidence source model and its constructor checks (#3, item 4)

Co-Authored-By: Claude Sonnet 5.5 <noreply@anthropic.com>"
```

---

### Task 2: Formulas, satisfaction and the four updates

**Files:**
- Modify: `Gamen/EvidenceTrust.lean` (append), `Tests/EvidenceTrust.lean` (add `movieCases`, restore the `sat` probe)

**Interfaces:**
- Consumes: Task 1's `ESM`, `Mask`, `Sets`.
- Produces: `EFormula` (constructors `atom bot not and type knows believes evidence trust reason announce loseTrust relyOn assess`; derived `top or implies hatK hatB bigOr bigAnd`), `hasEvidence`, `reasonAt`, `announceModel`, `loseTrustModel`, `relyOnModel`, `assessModel` (each `ESM → … → Mask → ESM`, the `Mask` being `⟦φ⟧`), `sat : ESM → EFormula → Except String Mask`, `holdsAt`, `validIn`, `subsetsOfSize`, `atLeast`, `reasonLiteral`.

- [ ] **Step 1: Write the failing tests.** Add the §2.4 example to `Tests/EvidenceTrust.lean` (before `def cases`), add the `an unknown agent index is an error` probe to `constructorCases` (it needs `sat`; put it after the `bad_type` item, turning that item's closing `]` into `),`), and set `def cases := constructorCases ++ movieCases`.

```lean
/-! ## Helpers that need the formulas -/
abbrev F := EFormula
def atomF (p : String) : F := .atom p
def p : F := atomF "p"
def q : F := atomF "q"
def neg (f : F) : F := .not f
def conj (a b : F) : F := .and a b
def sat? (m : ESM) (f : F) : Option Mask := match sat m f with | .ok x => some x | .error _ => none
def valid? (m : ESM) (f : F) : Option Bool := match validIn m f with | .ok b => some b | .error _ => none

/-! ## The paper's §2.4 example

Agents 0 chatbot, 1 Wikipedia, 2 IMDb, 3 Amazon, 4 RT. Worlds 0 (p, q), 1 (q), 2 (neither); the
world where `p ∧ ¬q` would hold is absent, which is `Hyp1 = K_chatbot (p → q)`. Masks:
‖p‖ = 1, ‖¬p‖ = 6, ‖q‖ = 3, ‖¬q‖ = 4. The chatbot trusts Wikipedia and IMDb about p and ¬p, and
Amazon and RT about q and ¬q (`Hyp2`); no belief, no evidence (`Hyp3`); type `(cautiousness, 1)`. -/
def movie (cautious : Nat) : ESM where
  n := 3
  agents := #["chatbot", "wikipedia", "imdb", "amazon", "rt"]
  valuation := #[["p", "q"], ["q"], []]
  E := Array.replicate 5 (Array.replicate 3 7)
  D := Array.replicate 5 (Array.replicate 3 7)
  S := Array.replicate 5 (Array.replicate 5 (Array.replicate 3 []))
  C := (List.range 5).toArray.map fun i => (List.range 5).toArray.map fun j =>
    Array.replicate 3 (if i != 0 then [] else if j == 1 || j == 2 then [1, 6] else if j == 3 || j == 4 then [3, 4] else [])
  T := (List.range 5).toArray.map fun i => Array.replicate 3 (if i == 0 then (cautious, (1 : Rat)) else (1, 1))

def bel (f : F) : F := .believes 0 f
def undecidedQ : F := conj (neg (bel q)) (neg (bel (neg q)))

def movieCases : List (String × Bool) := [
  ("the movie model is an ESM",
    ok (movie 2).validate),
  ("§2.4: [!Amazon q][!RT ¬q][?chatbot q](¬B q ∧ ¬B ¬q) holds everywhere: discordant sources leave the chatbot undecided",
    valid? (movie 2) (.announce 3 q (.announce 4 (neg q) (.assess 0 q undecidedQ))) == some true),
  ("§2.4: [!Wikipedia p][!IMDb p][?chatbot p]B q holds everywhere",
    valid? (movie 2) (.announce 1 p (.announce 2 p (.assess 0 p (bel q)))) == some true),
  ("control: with only Wikipedia's announcement the chatbot (cautiousness 2) does not come to believe q anywhere",
    sat? (movie 2) (.announce 1 p (.assess 0 p (bel q))) == some 0),
  ("control: with cautiousness 1, Wikipedia alone suffices: B p and B q everywhere",
    valid? (movie 1) (.announce 1 p (.assess 0 p (conj (bel p) (bel q)))) == some true),
  ("control: without assessing, the announcements change evidence but not belief",
    sat? (movie 2) (.announce 1 p (.announce 2 p (bel q))) == some 0),
  ("an announcement is not truthful by definition: Amazon announcing ¬q where q holds still gives evidence",
    valid? (movie 2) (.announce 3 (neg q) (.evidence 0 3 (neg q))) == some true),
  ("T implies E after an announcement by that source, but not for a source the chatbot does not trust",
    valid? (movie 2) (.announce 3 p (.evidence 0 3 p)) == some false)]
```

The probe to add, last item of `constructorCases`:

```lean
  ("an unknown agent index is an error, not false",
    errStarts (sat base (.knows 5 .bot)) "unknown agent")]
```

- [ ] **Step 2: Run to verify failure.** Run `lake build 2>&1 | grep error | head -3`. Expected: `unknown identifier sat` / `EFormula`.

- [ ] **Step 3: Implement.** In `Gamen/EvidenceTrust.lean` delete the two closing lines, then append (the whole block compiles as one unit with Task 1's half):

```lean
/-- DL-BET formulas. Agents are indices. The four update forms carry their continuation:
`announce i φ ψ` is `[!_i φ]ψ`, `loseTrust i j φ ψ` is `[−_{i,j} φ]ψ`, `relyOn i j φ ψ` is
`[+_{i,j} φ]ψ`, `assess i φ ψ` is `[?_i φ]ψ`. `reason i φ` is `R_i φ`, evaluated directly
(see `reasonAt`); `reasonLiteral` builds the paper's disjunction for cross-checking. -/
inductive EFormula where
  | atom (p : String)
  | bot
  | not (f : EFormula)
  | and (l r : EFormula)
  | type (i x : Nat) (y : Rat)
  | knows (i : Nat) (f : EFormula)
  | believes (i : Nat) (f : EFormula)
  | evidence (i j : Nat) (f : EFormula)
  | trust (i j : Nat) (f : EFormula)
  | reason (i : Nat) (f : EFormula)
  | announce (i : Nat) (f g : EFormula)
  | loseTrust (i j : Nat) (f g : EFormula)
  | relyOn (i j : Nat) (f g : EFormula)
  | assess (i : Nat) (f g : EFormula)

namespace EFormula
def top : EFormula := .not .bot
def or (l r : EFormula) : EFormula := .not (.and (.not l) (.not r))
def implies (l r : EFormula) : EFormula := .or (.not l) r
def hatK (i : Nat) (f : EFormula) : EFormula := .not (.knows i (.not f))
def hatB (i : Nat) (f : EFormula) : EFormula := .not (.believes i (.not f))
def bigOr (fs : List EFormula) : EFormula := fs.foldr or .bot
def bigAnd (fs : List EFormula) : EFormula := fs.foldr .and top
end EFormula

/-- Does agent `i`, at world `w`, hold the evidence `‖φ‖_{i,w}` from source `j`? `fm` is `⟦φ⟧`. -/
def hasEvidence (m : ESM) (i j w : Nat) (fm : Mask) : Bool :=
  (m.s i j w).contains (fm &&& m.e i w)

/-- `R_i φ` at `w` (§2.1, read off the PDF): with `T(i,w) = (x'', y)`, `x` the number of agents
`j` with `E_{i,j} φ` and `x'` the number with `E_{i,j} ¬φ`, `R_i φ` iff `x > x'`,
`x/(x+x') ≥ y` and `x ≥ x''`. Equal to the paper's disjunction (`reasonLiteral`). -/
def reasonAt (m : ESM) (i w : Nat) (fm : Mask) : Bool :=
  let nfm := Mask.full m.n ^^^ fm
  let x := (m.agentIds.filter fun j => hasEvidence m i j w fm).length
  let x' := (m.agentIds.filter fun j => hasEvidence m i j w nfm).length
  let (xt, y) := m.t i w
  decide (x > x') && decide ((x : Rat) / ((x + x' : Nat) : Rat) ≥ y) && decide (x ≥ xt)

/-- Def 3, `!_i φ`: every `j` who trusts `i` about `φ` gains `‖φ‖_{j,w}` as evidence from `i`.
There is no truth precondition. -/
def announceModel (m : ESM) (i : Nat) (fm : Mask) : ESM :=
  { m with S := m.S.mapIdx fun j row => row.mapIdx fun k col =>
      if k == i then col.mapIdx fun w sets =>
        let X := fm &&& m.e j w
        if (m.c j i w).contains X then sets.ins X else sets
      else col }

/-- Def 4, `−_{i,j} φ`: remove `‖φ‖_{i,w}` from `S(i,j,w)` and `C(i,j,w)`. -/
def loseTrustModel (m : ESM) (i j : Nat) (fm : Mask) : ESM :=
  let upd (t : Array (Array (Array Sets))) := t.mapIdx fun k row => row.mapIdx fun l col =>
    if k == i && l == j then col.mapIdx fun w sets => sets.del (fm &&& m.e i w) else col
  { m with S := upd m.S, C := upd m.C }

/-- Def 5, `+_{i,j} φ`: add `‖φ‖_{i,w}` to `C(i,j,w)` where `K̂_i φ` holds at `w` (the PDF's
guard; the text extract loses the hat). -/
def relyOnModel (m : ESM) (i j : Nat) (fm : Mask) : ESM :=
  { m with C := m.C.mapIdx fun k row => row.mapIdx fun l col =>
      if k == i && l == j then col.mapIdx fun w sets =>
        let X := fm &&& m.e i w
        if X != 0 then sets.ins X else sets
      else col }

/-- Def 6, `?_i φ`: expansion or revision of `D(i,·)` when `i` has sufficient reason. -/
def assessModel (m : ESM) (i : Nat) (fm : Mask) : ESM :=
  let nfm := Mask.full m.n ^^^ fm
  { m with D := m.D.mapIdx fun j row =>
      if j != i then row else row.mapIdx fun w dw =>
        let rP := reasonAt m i w fm
        let rN := reasonAt m i w nfm
        let bP := Mask.subset dw fm      -- B_i φ
        let bN := Mask.subset dw nfm     -- B_i ¬φ
        if rP && !bN then dw &&& fm
        else if rN && !bP then dw &&& nfm
        else if rP && bN then m.e i w &&& fm
        else if rN && bP then m.e i w &&& nfm
        else dw }

private def agentOk (m : ESM) (i : Nat) : Except String Unit :=
  if i < m.nAgents then pure () else throw s!"unknown agent index {i}"

/-- The set of worlds satisfying `f` (Def 2). Updates evaluate their formula in the model
before the update, then the continuation in the updated model. -/
def sat : ESM → EFormula → Except String Mask
  | m, .atom p => pure ((m.worlds.filter fun w => (m.valuation[w]?.getD []).contains p).foldl
      (fun acc w => acc ||| (1 <<< w)) 0)
  | _, .bot => pure 0
  | m, .not f => do pure (Mask.full m.n ^^^ (← sat m f))
  | m, .and l r => do pure ((← sat m l) &&& (← sat m r))
  | m, .type i x y => do
    agentOk m i
    pure ((m.worlds.filter fun w => m.t i w == (x, y)).foldl (fun acc w => acc ||| (1 <<< w)) 0)
  | m, .knows i f => do
    agentOk m i; let fm ← sat m f
    pure ((m.worlds.filter fun w => Mask.subset (m.e i w) fm).foldl (fun acc w => acc ||| (1 <<< w)) 0)
  | m, .believes i f => do
    agentOk m i; let fm ← sat m f
    pure ((m.worlds.filter fun w => Mask.subset (m.d i w) fm).foldl (fun acc w => acc ||| (1 <<< w)) 0)
  | m, .evidence i j f => do
    agentOk m i; agentOk m j; let fm ← sat m f
    pure ((m.worlds.filter fun w => hasEvidence m i j w fm).foldl (fun acc w => acc ||| (1 <<< w)) 0)
  | m, .trust i j f => do
    agentOk m i; agentOk m j; let fm ← sat m f
    pure ((m.worlds.filter fun w => (m.c i j w).contains (fm &&& m.e i w)).foldl
      (fun acc w => acc ||| (1 <<< w)) 0)
  | m, .reason i f => do
    agentOk m i; let fm ← sat m f
    pure ((m.worlds.filter fun w => reasonAt m i w fm).foldl (fun acc w => acc ||| (1 <<< w)) 0)
  | m, .announce i f g => do
    agentOk m i; let fm ← sat m f; sat (announceModel m i fm) g
  | m, .loseTrust i j f g => do
    agentOk m i; agentOk m j; let fm ← sat m f; sat (loseTrustModel m i j fm) g
  | m, .relyOn i j f g => do
    agentOk m i; agentOk m j; let fm ← sat m f; sat (relyOnModel m i j fm) g
  | m, .assess i f g => do
    agentOk m i; let fm ← sat m f; sat (assessModel m i fm) g

/-- `(M, w) ⊨ f`. -/
def holdsAt (m : ESM) (f : EFormula) (w : Nat) : Except String Bool := do
  pure ((← sat m f).testBit w)

/-- `f` is true at every world. -/
def validIn (m : ESM) (f : EFormula) : Except String Bool := do
  pure ((← sat m f) == Mask.full m.n)

/-- The sublists of `l` with exactly `k` elements. -/
def subsetsOfSize : Nat → List Nat → List (List Nat)
  | 0, _ => [[]]
  | _ + 1, [] => []
  | k + 1, a :: rest => (subsetsOfSize k rest).map (a :: ·) ++ subsetsOfSize (k + 1) rest

/-- `E_i^{≥x} φ` as the paper's disjunction over subsets of agents of size `x`. -/
def atLeast (m : ESM) (i x : Nat) (f : EFormula) : EFormula :=
  if x == 0 then .top
  else EFormula.bigOr ((subsetsOfSize x m.agentIds).map fun J =>
    EFormula.bigAnd (J.map fun j => .evidence i j f))

/-- `R_i φ` as the paper's literal disjunction, over the quotas `qt` (which must contain every
agent's quota). Used only to cross-check `reasonAt`. -/
def reasonLiteral (m : ESM) (qt : List Rat) (i : Nat) (f : EFormula) : EFormula :=
  let evd := List.range (m.nAgents + 1)
  let exactly (x : Nat) (g : EFormula) := EFormula.and (atLeast m i x g) (.not (atLeast m i (x + 1) g))
  EFormula.bigOr (evd.flatMap fun (x : Nat) => evd.flatMap fun (x' : Nat) => evd.flatMap fun (x'' : Nat) =>
    qt.filterMap fun y =>
    if x > x' && decide ((x : Rat) / ((x + x' : Nat) : Rat) ≥ y) && x ≥ x'' then
      some (EFormula.bigAnd [exactly x f, exactly x' (.not f), .type i x'' y])
    else none)
```

Notes for the implementer: `reasonAt` is `R_i φ` read off the PDF (p. 6): counts are over *source agents* `j ∈ Agt` (including `i`), the test is `x > x'`, `x/(x+x') ≥ y`, `x ≥ x''`. `announceModel` has **no** truth precondition (Def 3). `relyOnModel` guards on `‖φ‖_{i,w} ≠ ∅`, which is `K̂_i φ` (Def 5, PDF p. 9). `assessModel` has the four cases of Def 6 in the printed order; `R_iφ` and `R_i¬φ` are never both true (validity (4)).

- [ ] **Step 4: Run.** `lake build 2>&1 | tail -2; lake test 2>&1 | grep -E "✗|passed"`. Expected: all pass, including the §2.4 example and its controls.

- [ ] **Step 5: Re-read the paper's §2.3-2.4 from the PDF.** The properties and example were read from the text extract: open pages 7-10 and 13 as images (`pdftoppm -f N -l N -r 110`), confirm validities (1)-(11) and the example's hypotheses match what the tests encode, and fix any difference in the spec's source table (`[VERIFIED]` only once done).

- [ ] **Step 6: Commit.**

```bash
git add Gamen/EvidenceTrust.lean Tests/EvidenceTrust.lean
git commit -m "Add DL-BET formulas, satisfaction and the four updates (#3, item 4)

Co-Authored-By: Claude Sonnet 5.5 <noreply@anthropic.com>"
```

---

### Task 3: Property tests and mutation checks

**Files:**
- Modify: `Tests/EvidenceTrust.lean` (add the random generator and `randomCases`)

**Interfaces:**
- Consumes: everything from Tasks 1-2.
- Produces: `randomESM : Nat → ESM`, `randomCases`.

- [ ] **Step 1: Write the tests.** Append before `def cases` and set `def cases := constructorCases ++ movieCases ++ randomCases`:

```lean
/-! ## Pseudo-random ESMs -/
def lcg (x : Nat) : Nat := (x * 1103515245 + 12345) % 2147483648
def next : StateM Nat Nat := modifyGet fun x => let x' := lcg x; (x' / 65536, x')

def quotas : List Rat := [1 / 2, 2 / 3, 1]

/-- A random ESM with 3 worlds and 3 agents; every agent has two classes by a random labelling. -/
def randomESM (seed : Nat) : ESM :=
  let act : StateM Nat ESM := do
    let n := 3
    let ags := 3
    let mut labels : Array (Array Nat) := #[]
    for _ in List.range ags do
      let mut ls : Array Nat := #[]
      for _ in List.range n do ls := ls.push ((← next) % 2)
      labels := labels.push ls
    let classOf (i w : Nat) : Mask :=
      (List.range n).foldl (fun acc v => if labels[i]![v]! == labels[i]![w]! then acc ||| (1 <<< v) else acc) 0
    -- one random draw per (agent, class); the first world of each class decides
    let mut dTab : Array (Array Mask) := #[]
    let mut tTab : Array (Array (Nat × Rat)) := #[]
    let mut sTab : Array (Array (Array Sets)) := #[]
    let mut cTab : Array (Array (Array Sets)) := #[]
    for i in List.range ags do
      let mut dRow : Array Mask := #[]
      let mut tRow : Array (Nat × Rat) := #[]
      let mut dByClass : List (Mask × Mask) := []
      let mut tByClass : List (Mask × (Nat × Rat)) := []
      for w in List.range n do
        let k := classOf i w
        if (dByClass.find? (·.1 == k)).isNone then
          let r ← next
          let d := (r % (k + 1)) &&& k
          dByClass := (k, if d == 0 then k else d) :: dByClass
          let r2 ← next
          tByClass := (k, (r2 % (ags + 1), quotas[(r2 / 7) % 3]!)) :: tByClass
        dRow := dRow.push ((dByClass.find? (·.1 == k)).get!.2)
        tRow := tRow.push ((tByClass.find? (·.1 == k)).get!.2)
      dTab := dTab.push dRow
      tTab := tTab.push tRow
      let mut sRow : Array (Array Sets) := #[]
      let mut cRow : Array (Array Sets) := #[]
      for _ in List.range ags do
        let mut byClass : List (Mask × (Sets × Sets)) := []
        let mut sCol : Array Sets := #[]
        let mut cCol : Array Sets := #[]
        for w in List.range n do
          let k := classOf i w
          if (byClass.find? (·.1 == k)).isNone then
            let mut cs : Sets := []
            let mut ss : Sets := []
            for X in List.range (1 <<< n) do
              if X != 0 && Mask.subset X k then
                let r ← next
                if r % 3 == 0 then
                  cs := Sets.ins X cs
                  if (r / 3) % 2 == 0 then ss := Sets.ins X ss
            byClass := (k, (ss, cs)) :: byClass
          let (ss, cs) := (byClass.find? (·.1 == k)).get!.2
          sCol := sCol.push ss
          cCol := cCol.push cs
        sRow := sRow.push sCol
        cRow := cRow.push cCol
      sTab := sTab.push sRow
      cTab := cTab.push cRow
    let mut val : Array (List String) := #[]
    for _ in List.range n do
      let r ← next
      val := val.push ((if r % 2 == 0 then ["p"] else []) ++ (if (r / 2) % 2 == 0 then ["q"] else []))
    pure { n := n, agents := #["a0", "a1", "a2"], valuation := val,
           E := (List.range ags).toArray.map fun i => (List.range n).toArray.map fun w => classOf i w,
           D := dTab, S := sTab, C := cTab, T := tTab }
  (act.run seed).1

def seeds : List Nat := (List.range 120).map fun i => 1000 + 7919 * i
def props : List F := [p, neg p, q, conj p q]
def ids : List Nat := [0, 1, 2]

def forAllModels (check : ESM → Bool) : Bool := seeds.all fun s => check (randomESM s)
def validAll (m : ESM) (f : F) : Bool := (valid? m f) == some true

def randomCases : List (String × Bool) := [
  ("the generator builds ESMs (C1-C10 hold on all 120 seeds)",
    forAllModels fun m => ok m.validate),
  ("the random models are not degenerate: some have evidence, some have beliefs narrower than knowledge",
    (seeds.filter fun s => let m := randomESM s; m.agentIds.any fun i => m.agentIds.any fun j =>
        m.worlds.any fun w => !(m.s i j w).isEmpty).length > 60
      && (seeds.filter fun s => let m := randomESM s; m.agentIds.any fun i => m.worlds.any fun w =>
        m.d i w != m.e i w).length > 60),
  ("(1) T_{i,j}φ → K̂_iφ  (2) E_{i,j}φ → K̂_iφ  (3) R_iφ → K̂_iφ  (4) ¬(R_iφ ∧ R_i¬φ), on 120 random ESMs",
    forAllModels fun m => ids.all fun i => props.all fun f =>
      validAll m (.not (conj (.reason i f) (.reason i (neg f))))
        && validAll m (.implies (.reason i f) (.hatK i f))
        && ids.all fun j => validAll m (.implies (.trust i j f) (.hatK i f))
          && validAll m (.implies (.evidence i j f) (.hatK i f))),
  ("(5) T_{i,j}φ → [!_jφ]E_{i,j}φ  (6) [−_{i,j}φ](¬E_{i,j}φ ∧ ¬T_{i,j}φ)  (7) K̂_iφ → [+_{i,j}φ]T_{i,j}φ",
    forAllModels fun m => ids.all fun i => ids.all fun j => props.all fun f =>
      validAll m (.implies (.trust i j f) (.announce j f (.evidence i j f)))
        && validAll m (.loseTrust i j f (conj (neg (.evidence i j f)) (neg (.trust i j f))))
        && validAll m (.implies (.hatK i f) (.relyOn i j f (.trust i j f)))),
  ("(8) R_iφ → [?_iφ]B_iφ  (9) R_i¬φ → [?_iφ]B_i¬φ",
    forAllModels fun m => ids.all fun i => props.all fun f =>
      validAll m (.implies (.reason i f) (.assess i f (.believes i f)))
        && validAll m (.implies (.reason i (neg f)) (.assess i f (.believes i (neg f))))),
  ("(10) sufficient reason plus K_i(φ → ψ) gives B_iψ after ?_iφ",
    forAllModels fun m => ids.all fun i => props.all fun f => props.all fun g =>
      validAll m (.implies
        (.or (conj (.reason i f) (.knows i (.implies f g))) (conj (.reason i (neg f)) (.knows i (.implies (neg f) g))))
        (.assess i f (.believes i g)))),
  ("(11) conservative expansion: an existing belief ψ survives ?_iφ when i expands",
    forAllModels fun m => ids.all fun i => props.all fun f => props.all fun g =>
      validAll m (.implies
        (.or (conj (conj (.reason i f) (neg (.believes i (neg f)))) (.believes i g))
             (conj (conj (.reason i (neg f)) (neg (.believes i f))) (.believes i g)))
        (.assess i f (.believes i g)))),
  ("Proposition 1: every update of a random ESM is again an ESM (C1-C10)",
    forAllModels fun m => ids.all fun i => props.all fun f =>
      match sat m f with
      | .error _ => false
      | .ok fm =>
        ok (announceModel m i fm).validate && ok (assessModel m i fm).validate
          && ids.all fun j => ok (loseTrustModel m i j fm).validate && ok (relyOnModel m i j fm).validate),
  ("R_i φ read directly equals the paper's literal disjunction over Evd × Evd × Evd × Qt, on 40 random ESMs",
    (seeds.take 40).all fun s => let m := randomESM s; ids.all fun i => props.all fun f =>
      (sat m (.reason i f)).toOption == (sat m (reasonLiteral m quotas i f)).toOption
        && (sat m (.reason i f)).isOk),
  ("(8) is not valid for a Moore-like φ = p ∧ ¬B_i p: the paper's stated counterexample",
    (let moore : F := conj p (neg (.believes 0 p))
     let m : ESM := { base with
       valuation := #[["p"], []],
       E := #[#[3, 3], #[3, 3]], D := #[#[3, 3], #[3, 3]],
       S := #[#[#[[], []], #[[1], [1]]], #[#[[], []], #[[], []]]],
       C := #[#[#[[], []], #[[1], [1]]], #[#[[], []], #[[], []]]],
       T := #[#[(1, 1), (1, 1)], #[(0, 1), (0, 1)]] }
     ok m.validate
       && valid? m (.implies (.reason 0 moore) (.assess 0 moore (.believes 0 moore))) == some false
       && valid? m (.implies (.reason 0 p) (.assess 0 p (.believes 0 p))) == some true))]
```

These cover: C1-C10 hold on the generated models; validities (1)-(11) over all agent pairs including `i = j` (self-trust); Proposition 1; `reasonAt` against `reasonLiteral`; and the paper's Moore-like counterexample to (8).

- [ ] **Step 2: Run.** `lake test 2>&1 | grep -E "✗|passed"`. Expected: all pass. If a validity fails, that is a bug in the port or a misreading of the paper: read the definition off the PDF before changing anything, and do not weaken the test.

- [ ] **Step 3: Mutation checks.** For each change below, apply it to `Gamen/EvidenceTrust.lean`, run `lake test 2>&1 | grep "✗"`, confirm at least one test fails, and revert it (`git checkout Gamen/EvidenceTrust.lean`). Expected failing test in parentheses (all six were confirmed in the plan's scratch run):
  1. `loseTrustModel`: `sets.del (fm &&& m.e i w)` → `sets.ins (...)` (validities (5)-(7), Proposition 1).
  2. `relyOnModel`: guard `if X != 0` → `if Mask.subset (m.e i w) fm` (validity (7)).
  3. `assessModel`: swap the expansion and revision branches (validity (11), Proposition 1).
  4. `reasonAt`: drop `&& decide (x ≥ xt)` → `&& true` (the cautiousness control and the literal-disjunction cross-check).
  5. `ESM.validate`: C8 check `if X == 0` → `if X != 0` (the C8 probe).
  6. `announceModel`: add a truth precondition `&& Mask.subset (m.e j w) fm` (the §2.4 example).

- [ ] **Step 4: Commit.**

```bash
git add Tests/EvidenceTrust.lean
git commit -m "Add DL-BET property tests: validities (1)-(11), Proposition 1, R_i cross-check (#3, item 4)

Co-Authored-By: Claude Sonnet 5.5 <noreply@anthropic.com>"
```

---

### Task 4: The `evidence_trust_check` request (protocol 8)

**Files:**
- Create: `Validate/EvidenceTrust.lean`, `Tests/ValidateEvidenceTrust.lean`
- Modify: `Validate/Core.lean`, `Gamen/Protocol.lean` (`protocolVersion` 7 → 8), `Tests/ValidateVersion.lean` (the two `7`s, as in the angels-and-demons commit), `Tests/Main.lean` (import and register `ValidateEvidenceTrustTests.cases`)

**Interfaces:**
- Consumes: `ESM`, `EFormula`, `sat`, `Mask.full` (Tasks 1-2).
- Produces: `EtJson.decodeModel : Json → Except EtError (ESM × List String)`, `EtJson.decodeFormula : Array String → Json → Except EtError EFormula`, `evidenceTrustCheck (model : Json) (formulas : List Json) (worlds : Option (List String)) : Json`.

- [ ] **Step 1: Write the failing wire tests.** Create `Tests/ValidateEvidenceTrust.lean`:

```lean
import Validate.Core

/-!
# The Lean-only `evidence_trust_check` action (`Validate/EvidenceTrust.lean`)

Issue #3 item 4, protocol 8. Pins the wire contract: the paper's §2.4 example over JSON, the
stable error codes, strict keys, and size limits.
-/

namespace ValidateEvidenceTrustTests

open Lean (Json)

def movieJson : String :=
  "{\"worlds\":[\"w0\",\"w1\",\"w2\"],\"agents\":[\"chatbot\",\"wikipedia\",\"imdb\",\"amazon\",\"rt\"],\
    \"valuation\":{\"w0\":[\"p\",\"q\"],\"w1\":[\"q\"]},\
    \"knowledge\":{\"chatbot\":[[\"w0\",\"w1\",\"w2\"]],\"wikipedia\":[[\"w0\",\"w1\",\"w2\"]],\"imdb\":[[\"w0\",\"w1\",\"w2\"]],\"amazon\":[[\"w0\",\"w1\",\"w2\"]],\"rt\":[[\"w0\",\"w1\",\"w2\"]]},\
    \"belief\":{\"chatbot\":[{\"class\":\"w0\",\"worlds\":[\"w0\",\"w1\",\"w2\"]}],\"wikipedia\":[{\"class\":\"w0\",\"worlds\":[\"w0\"]}],\"imdb\":[{\"class\":\"w0\",\"worlds\":[\"w0\"]}],\"amazon\":[{\"class\":\"w0\",\"worlds\":[\"w0\"]}],\"rt\":[{\"class\":\"w0\",\"worlds\":[\"w0\"]}]},\
    \"trust\":{\"chatbot\":{\"wikipedia\":[{\"class\":\"w0\",\"sets\":[[\"w0\"],[\"w1\",\"w2\"]]}],\"imdb\":[{\"class\":\"w0\",\"sets\":[[\"w0\"],[\"w1\",\"w2\"]]}],\
      \"amazon\":[{\"class\":\"w0\",\"sets\":[[\"w0\",\"w1\"],[\"w2\"]]}],\"rt\":[{\"class\":\"w0\",\"sets\":[[\"w0\",\"w1\"],[\"w2\"]]}]}},\
    \"types\":{\"chatbot\":[2,\"1\"],\"wikipedia\":[1,\"1\"],\"imdb\":[1,\"1\"],\"amazon\":[1,\"1\"],\"rt\":[1,\"1\"]}}"

/-- Two worlds, two agents, no evidence or trust. -/
def tiny : String :=
  "{\"worlds\":[\"a\",\"b\"],\"agents\":[\"i\",\"j\"],\"valuation\":{\"a\":[\"p\"]},\
    \"belief\":{\"i\":[{\"class\":\"a\",\"worlds\":[\"a\"]}],\"j\":[{\"class\":\"a\",\"worlds\":[\"a\"]}]},\
    \"knowledge\":{\"i\":[[\"a\",\"b\"]],\"j\":[[\"a\",\"b\"]]},\
    \"types\":{\"i\":[0,\"1\"],\"j\":[0,\"1\"]}}"

def atomJ (n : String) : String := "{\"type\":\"atom\",\"name\":\"" ++ n ++ "\"}"
def notJ (f : String) : String := "{\"type\":\"not\",\"operand\":" ++ f ++ "}"
def andJ (a b : String) : String := "{\"type\":\"and\",\"left\":" ++ a ++ ",\"right\":" ++ b ++ "}"
def beliefJ (a f : String) : String := "{\"type\":\"belief\",\"agent\":\"" ++ a ++ "\",\"operand\":" ++ f ++ "}"
def announceJ (a f g : String) : String :=
  "{\"type\":\"announce\",\"agent\":\"" ++ a ++ "\",\"operand\":" ++ f ++ ",\"then\":" ++ g ++ "}"
def assessJ (a f g : String) : String :=
  "{\"type\":\"assess\",\"agent\":\"" ++ a ++ "\",\"operand\":" ++ f ++ ",\"then\":" ++ g ++ "}"

def req (model : String) (fs : List String) (extra : String := "") : String :=
  "{\"action\":\"evidence_trust_check\",\"model\":" ++ model ++ ",\"formulas\":["
    ++ ",".intercalate fs ++ "]" ++ extra ++ "}"

def run (line : String) : Json := processLine line "t"

def item (r : Json) (i : Nat) : Option Json := do
  let rs ← (← (r.getObjVal? "result").toOption).getObjVal? "results" |>.toOption
  rs.getArrVal? i |>.toOption

def sat (r : Json) (i : Nat := 0) : Option (List String) := do
  let arr ← (← (← item r i).getObjVal? "satisfying" |>.toOption).getArr? |>.toOption
  pure (arr.toList.filterMap (·.getStr?.toOption))

def strKey (j : Option Json) (k : String) : Option String :=
  j.bind fun j => (j.getObjVal? k).toOption >>= (·.getStr?.toOption)

def code (r : Json) : Option String := strKey (some r) "error_code"
def itemCode (r : Json) (i : Nat) : Option String := strKey (item r i) "error_code"

def p := atomJ "p"
def q := atomJ "q"
def all3 : List String := ["w0", "w1", "w2"]

def cases : List (String × Bool) := [
  ("§2.4 over JSON: Wikipedia and IMDb both announcing p, then ?chatbot p, gives B q in every world",
    sat (run (req movieJson [announceJ "wikipedia" p (announceJ "imdb" p (assessJ "chatbot" p (beliefJ "chatbot" q)))]))
      == some all3),
  ("§2.4 over JSON: Amazon q then RT ¬q then ?chatbot q leaves the chatbot undecided about q everywhere",
    sat (run (req movieJson [announceJ "amazon" q (announceJ "rt" (notJ q) (assessJ "chatbot" q
      (andJ (notJ (beliefJ "chatbot" q)) (notJ (beliefJ "chatbot" (notJ q))))))])) == some all3),
  ("control: Wikipedia alone does not make a cautiousness-2 chatbot believe q (no world)",
    sat (run (req movieJson [announceJ "wikipedia" p (assessJ "chatbot" p (beliefJ "chatbot" q))])) == some []),
  ("`worlds` restricts the report, and `holds` and `true_in_model` are per world",
    (let r := run (req movieJson [p] ",\"worlds\":[\"w2\",\"w0\"]")
     sat r == some ["w0"]
       && ((item r 0).bind fun i => (i.getObjVal? "true_in_model").toOption) == some (Json.bool false))),
  ("an unknown world in `worlds` is a request error",
    code (run (req movieJson [p] ",\"worlds\":[\"w9\"]")) == some "unknown_world"),
  ("a world listed twice in `worlds` is an error",
    code (run (req movieJson [p] ",\"worlds\":[\"w0\",\"w0\"]")) == some "malformed_spec"),
  ("belief is required for every class: dropping the chatbot's entry is malformed_spec, not a default",
    code (run (req (movieJson.replace "\"chatbot\":[{\"class\":\"w0\",\"worlds\":[\"w0\",\"w1\",\"w2\"]}]," "") [p]))
      == some "malformed_spec"),
  ("a misspelled model key is an error, not an absent field (`trusts`)",
    code (run (req (movieJson.replace "\"trust\":" "\"trusts\":") [p])) == some "malformed_spec"),
  ("a stray key on a formula is an error",
    itemCode (run (req movieJson ["{\"type\":\"atom\",\"name\":\"p\",\"agent\":\"chatbot\"}"])) 0
      == some "malformed_spec"),
  ("an update without `then` is malformed_spec, not a silent ⊤",
    itemCode (run (req movieJson
      ["{\"type\":\"announce\",\"agent\":\"wikipedia\",\"operand\":" ++ p ++ "}"])) 0 == some "malformed_spec"),
  ("an unknown agent in a formula is a per-formula unknown_agent, and does not sink its neighbor",
    (let r := run (req movieJson [beliefJ "nobody" p, p])
     itemCode r 0 == some "unknown_agent" && sat r 1 == some ["w0"])),
  ("a quota as a decimal string is bad_rational, and as a JSON number is malformed_spec",
    code (run (req (tiny.replace "[0,\"1\"]" "[0,\"0.75\"]") [p])) == some "bad_rational"
      && code (run (req (tiny.replace "[0,\"1\"]" "[0,0.75]") [p])) == some "malformed_spec"),
  ("a zero denominator is bad_rational",
    code (run (req (tiny.replace "[0,\"1\"]" "[0,\"3/0\"]") [p])) == some "bad_rational"),
  ("a quota below 1/2 is bad_type; a cautiousness above the number of agents is bad_type",
    code (run (req (tiny.replace "[0,\"1\"]" "[0,\"1/4\"]") [p])) == some "bad_type"
      && code (run (req (tiny.replace "[0,\"1\"]" "[3,\"1\"]") [p])) == some "bad_type"),
  ("C9 over the wire: evidence from a source one does not trust is violates_C9",
    code (run (req (tiny.replace "\"types\"" "\"evidence\":{\"i\":{\"j\":[{\"class\":\"a\",\"sets\":[[\"a\"]]}]}},\"types\"") [p]))
      == some "violates_C9"),
  ("C8 over the wire: trust about the empty set is violates_C8",
    code (run (req (tiny.replace "\"types\"" "\"trust\":{\"i\":{\"j\":[{\"class\":\"a\",\"sets\":[[]]}]}},\"types\"") [p]))
      == some "violates_C8"),
  ("C3 over the wire: a belief set outside the class is violates_C3",
    code (run (req (tiny.replace "\"knowledge\":{\"i\":[[\"a\",\"b\"]],\"j\":[[\"a\",\"b\"]]}"
      "\"knowledge\":{\"i\":[[\"a\"],[\"b\"]],\"j\":[[\"a\",\"b\"]]}") [p])) == some "violates_C3"
      || code (run (req (tiny.replace "\"knowledge\":{\"i\":[[\"a\",\"b\"]],\"j\":[[\"a\",\"b\"]]}"
      "\"knowledge\":{\"i\":[[\"a\"],[\"b\"]],\"j\":[[\"a\",\"b\"]]}") [p])) == some "malformed_spec"),
  ("overlapping knowledge classes, duplicate worlds and duplicate agents have their own codes",
    code (run (req (tiny.replace "[[\"a\",\"b\"]],\"j\"" "[[\"a\",\"b\"],[\"b\"]],\"j\"") [p])) == some "overlapping_classes"
      && code (run (req (tiny.replace "[\"a\",\"b\"],\"agents\"" "[\"a\",\"a\"],\"agents\"") [p])) == some "duplicate_world"
      && code (run (req (tiny.replace "[\"i\",\"j\"],\"valuation\"" "[\"i\",\"i\"],\"valuation\"") [p])) == some "duplicate_agent"),
  ("an entry naming a class twice is malformed_spec (belief)",
    code (run (req (tiny.replace "\"belief\":{\"i\":[{\"class\":\"a\",\"worlds\":[\"a\"]}]"
      "\"belief\":{\"i\":[{\"class\":\"a\",\"worlds\":[\"a\"]},{\"class\":\"b\",\"worlds\":[\"b\"]}]") [p]))
      == some "malformed_spec"),
  ("21 worlds is bad_size",
    code (run (req ("{\"worlds\":[" ++ ",".intercalate ((List.range 21).map fun i => "\"w" ++ toString i ++ "\"")
      ++ "],\"agents\":[\"i\"],\"belief\":{},\"types\":{}}") [p])) == some "bad_size"),
  ("9 agents is bad_size",
    code (run (req ("{\"worlds\":[\"w\"],\"agents\":[" ++ ",".intercalate ((List.range 9).map fun i => "\"a" ++ toString i ++ "\"")
      ++ "],\"belief\":{},\"types\":{}}") [p])) == some "bad_size"),
  ("the protocol version is 8 and the version request says so",
    (run "{\"action\":\"version\"}").compress.contains "\"protocol\":8")]

end ValidateEvidenceTrustTests
```

Register it in `Tests/Main.lean` (import after `Tests.ValidateAngelsDemons`; add `++ ValidateEvidenceTrustTests.cases` and `+ ValidateEvidenceTrustTests.cases.length` beside `ValidateAngelsDemonsTests.cases`). The C3 test is written as a disjunction because with class-based beliefs the decoder may catch the problem as a missing belief entry (`malformed_spec`) before `validate` sees `C3`; whichever fires, it must not be accepted. Tighten it to the one that actually fires once the decoder runs.

- [ ] **Step 2: Run to verify failure.** `lake build 2>&1 | grep error | head -3`. Expected: `unknown action: evidence_trust_check` at test time, or a missing-module error.

- [ ] **Step 3: Write the decoder and handler.** Create `Validate/EvidenceTrust.lean` (the code below was compile-checked and run on the §2.4 example in a scratch copy: all three formulas gave the expected `[w0,w1,w2]`, `[w0,w1,w2]`, `[]`):

```lean
import Gamen.Protocol
import Gamen.EvidenceTrust

/-!
# Validate.EvidenceTrust

The Lean-only `evidence_trust_check` request of `gamen-validate` (protocol 8): model-check
DL-BET formulas (`Gamen.EvidenceTrust`; Liu & Lorini, PRIMA 2017) on an evidence source model
given as JSON. See `Validate.lean` for the wire format. gamen-hs has no such request.
-/
open Lean (Json toJson)
open Gamen Gamen.Protocol Gamen.EvidenceTrust

structure EtError where
  code : String
  message : String

instance : Inhabited EtError := ⟨⟨"", ""⟩⟩

namespace EtJson

def err (code msg : String) : EtError := ⟨code, msg⟩
private def malformed (msg : String) : EtError := err "malformed_spec" msg
private def lift {α} (r : Except String α) : Except EtError α := r.mapError malformed

def maxWorlds : Nat := 20
def maxAgents : Nat := 8

/-- Reject a key the request does not define (a misspelling would otherwise read as absent). -/
def onlyKeys (j : Json) (allowed : List String) (what : String) : Except EtError Unit :=
  match j with
  | .obj kvs =>
    match kvs.toList.find? (fun (k, _) => !allowed.contains k) with
    | some (k, _) => throw (malformed s!"{what}: unknown key \"{k}\" (expected one of {allowed})")
    | none => pure ()
  | _ => throw (malformed s!"{what} must be an object")

/-- An exact rational: `"1"`, `"3/4"`. -/
def parseRat (s : String) : Except EtError Rat :=
  match s.splitOn "/" with
  | [a] => match a.toNat? with
    | some n => pure (n : Rat)
    | none => throw (err "bad_rational" s!"\"{s}\" is not a rational (expected \"n\" or \"n/d\")")
  | [a, b] => match a.toNat?, b.toNat? with
    | some n, some d => if d == 0 then throw (err "bad_rational" s!"\"{s}\" has a zero denominator")
                        else pure ((n : Rat) / (d : Rat))
    | _, _ => throw (err "bad_rational" s!"\"{s}\" is not a rational (expected \"n\" or \"n/d\")")
  | _ => throw (err "bad_rational" s!"\"{s}\" is not a rational (expected \"n\" or \"n/d\")")

private def worldIdx (ws : Array String) (w : String) : Except EtError Nat :=
  match ws.findIdx? (· == w) with
  | some i => pure i
  | none => throw (err "unknown_world" s!"unknown world \"{w}\"")

private def agentIdx (ags : Array String) (a : String) : Except EtError Nat :=
  match ags.findIdx? (· == a) with
  | some i => pure i
  | none => throw (err "unknown_agent" s!"unknown agent \"{a}\"")

private def strList (j : Json) (what : String) : Except EtError (List String) :=
  lift (j.getArr? >>= fun a => a.toList.mapM (·.getStr?)) |>.mapError fun e => malformed s!"{what}: {e.message}"

private def maskOfNames (ws : Array String) (names : List String) : Except EtError Mask :=
  names.foldlM (fun acc n => do pure (acc ||| (1 <<< (← worldIdx ws n)))) 0

/-- `{agent: <value>}` entries, each key checked against the agents. -/
private def agentEntries (ags : Array String) (j : Json) (what : String) :
    Except EtError (List (Nat × Json)) := do
  match j with
  | .obj kvs => kvs.toList.mapM fun (k, v) => do pure (← agentIdx ags k, v)
  | _ => throw (malformed s!"{what} must be an object keyed by agent")

/-- Decode a model. Classes make C1, C4-C6 and C10 hold by construction; `validate` still runs. -/
def decodeModel (j : Json) : Except EtError (ESM × List String) := do
  onlyKeys j ["worlds", "agents", "valuation", "knowledge", "belief", "evidence", "trust", "types"] "model"
  let ws ← strList (← lift (field j "worlds")) "worlds"
  let ags ← strList (← lift (field j "agents")) "agents"
  if ws.length > maxWorlds then throw (err "bad_size" s!"at most {maxWorlds} worlds")
  if ags.length > maxAgents then throw (err "bad_size" s!"at most {maxAgents} agents")
  if ws.isEmpty || ags.isEmpty then throw (malformed "a model needs a world and an agent")
  if let some w := ws.find? (fun w => ws.count w > 1) then throw (err "duplicate_world" s!"duplicate world \"{w}\"")
  if let some a := ags.find? (fun a => ags.count a > 1) then throw (err "duplicate_agent" s!"duplicate agent \"{a}\"")
  let wa := ws.toArray
  let aa := ags.toArray
  let n := ws.length
  let na := ags.length
  -- valuation
  let valuation ← match ← lift (optField j "valuation") with
    | none => pure (Array.replicate n ([] : List String))
    | some (.obj kvs) =>
      let mut v := Array.replicate n ([] : List String)
      for (w, atoms) in kvs.toList do
        v := v.set! (← worldIdx wa w) (← strList atoms s!"valuation of {w}")
      pure v
    | some _ => throw (malformed "valuation must be an object")
  -- knowledge classes: E i w
  let mut E : Array (Array Mask) := Array.replicate na (Array.ofFn (n := n) fun w => (1 <<< w.val))
  match ← lift (optField j "knowledge") with
  | none => pure ()
  | some kj =>
    for (i, cj) in ← agentEntries aa kj "knowledge" do
      let mut row := Array.ofFn (n := n) fun w => (1 <<< w.val)
      let mut seen : Mask := 0
      for cls in (← lift cj.getArr?).toList do
        let mask ← maskOfNames wa (← strList cls "a knowledge class")
        if seen &&& mask != 0 then throw (err "overlapping_classes" s!"agent {aa[i]!}: classes overlap")
        seen := seen ||| mask
        for w in List.range n do
          if mask.testBit w then row := row.set! w mask
      E := E.set! i row
  let classMask (i : Nat) (w : Nat) : Mask := E[i]![w]!
  -- belief: required for every class of every agent
  let mut D : Array (Array Mask) := Array.replicate na (Array.replicate n 0)
  let beliefJ ← lift (field j "belief")
  let mut beliefSeen : List (Nat × Mask) := []
  for (i, bj) in ← agentEntries aa beliefJ "belief" do
    for entry in (← lift bj.getArr?).toList do
      onlyKeys entry ["class", "worlds"] "a belief entry"
      let c ← worldIdx wa (← lift (strField entry "class"))
      let b ← maskOfNames wa (← strList (← lift (field entry "worlds")) "belief worlds")
      let k := classMask i c
      if beliefSeen.contains (i, k) then throw (malformed s!"belief: agent {aa[i]!} has two entries for one class")
      beliefSeen := (i, k) :: beliefSeen
      for w in List.range n do
        if k.testBit w then D := D.modify i (·.set! w b)
  for i in List.range na do
    for w in List.range n do
      unless beliefSeen.contains (i, classMask i w) do
        throw (malformed s!"belief: no entry for agent {aa[i]!} at the class of world {wa[w]!}")
  -- evidence and trust: agent → source → [{class, sets}]
  let decodeSets (field : String) : Except EtError (Array (Array (Array Sets))) := do
    let mut tab : Array (Array (Array Sets)) := Array.replicate na (Array.replicate na (Array.replicate n []))
    match ← lift (optField j field) with
    | none => pure tab
    | some tj =>
      for (i, srcs) in ← agentEntries aa tj field do
        for (k, entries) in ← agentEntries aa srcs field do
          let mut done : List Mask := []
          for entry in (← lift entries.getArr?).toList do
            onlyKeys entry ["class", "sets"] s!"a {field} entry"
            let c ← worldIdx wa (← lift (strField entry "class"))
            let sets ← (← lift (← lift (Gamen.Protocol.field entry "sets")).getArr?).toList.mapM fun sj => do
              maskOfNames wa (← strList sj s!"a {field} set")
            let km := classMask i c
            if done.contains km then throw (malformed s!"{field}: two entries for one class")
            done := km :: done
            let norm := sets.foldl (fun acc m => Sets.ins m acc) []
            for w in List.range n do
              if km.testBit w then tab := tab.modify i (·.modify k (·.set! w norm))
      pure tab
  let S ← decodeSets "evidence"
  let C ← decodeSets "trust"
  -- types
  let typesJ ← lift (field j "types")
  let mut T : Array (Array (Nat × Rat)) := Array.replicate na (Array.replicate n (0, 1))
  let mut typed : List Nat := []
  for (i, tj) in ← agentEntries aa typesJ "types" do
    match (← lift tj.getArr?).toList with
    | [xj, yj] =>
      let x ← match xj.getNat? with
        | .ok x => pure x
        | .error _ => throw (malformed s!"types: cautiousness of {aa[i]!} must be a non-negative integer")
      let y ← parseRat (← lift yj.getStr?)
      T := T.set! i (Array.replicate n (x, y))
      typed := i :: typed
    | _ => throw (malformed s!"types: {aa[i]!} must be [cautiousness, \"quota\"]")
  for i in List.range na do
    unless typed.contains i do throw (malformed s!"types: no type for agent {aa[i]!}")
  let m : ESM := { n, agents := aa, valuation, E, D, S, C, T }
  match m.validate with
  | .ok () => pure (m, ws)
  | .error msg =>
    let code := if msg.startsWith "bad_type" then "bad_type"
      else if msg.startsWith "C" then s!"violates_{(msg.takeWhile (· != ':')).toString}"
      else "malformed_spec"
    throw (err code msg)

/-- Formulas, as tree-format JSON; agents by name. -/
partial def decodeFormula (ags : Array String) (j : Json) : Except EtError EFormula := do
  let ty ← lift (strField j "type")
  let allowed := match ty with
    | "atom" => ["name"]
    | "not" | "knowledge" | "belief" | "reason" => ["operand"] ++ (if ty == "not" then [] else ["agent"])
    | "and" | "or" | "implies" => ["left", "right"]
    | "type" => ["agent", "x", "y"]
    | "evidence" | "trust" => ["agent", "source", "operand"]
    | "announce" | "assess" => ["agent", "operand", "then"]
    | "lose_trust" | "rely_on" => ["agent", "source", "operand", "then"]
    | _ => []
  onlyKeys j (["type"] ++ allowed) s!"formula \"{ty}\""
  let sub (k : String) : Except EtError EFormula := do decodeFormula ags (← lift (field j k))
  let ag (k : String := "agent") : Except EtError Nat := do agentIdx ags (← lift (strField j k))
  match ty with
  | "atom" => return .atom (← lift (strField j "name"))
  | "bot" => return .bot
  | "top" => return EFormula.top
  | "not" => return .not (← sub "operand")
  | "and" => return .and (← sub "left") (← sub "right")
  | "or" => return EFormula.or (← sub "left") (← sub "right")
  | "implies" => return EFormula.implies (← sub "left") (← sub "right")
  | "type" =>
    let x ← match (← lift (field j "x")).getNat? with
      | .ok x => pure x
      | .error _ => throw (malformed "type: x must be a non-negative integer")
    return .type (← ag) x (← parseRat (← lift (strField j "y")))
  | "knowledge" => return .knows (← ag) (← sub "operand")
  | "belief" => return .believes (← ag) (← sub "operand")
  | "reason" => return .reason (← ag) (← sub "operand")
  | "evidence" => return .evidence (← ag) (← ag "source") (← sub "operand")
  | "trust" => return .trust (← ag) (← ag "source") (← sub "operand")
  | "announce" => return .announce (← ag) (← sub "operand") (← sub "then")
  | "assess" => return .assess (← ag) (← sub "operand") (← sub "then")
  | "lose_trust" => return .loseTrust (← ag) (← ag "source") (← sub "operand") (← sub "then")
  | "rely_on" => return .relyOn (← ag) (← ag "source") (← sub "operand") (← sub "then")
  | other => throw (malformed s!"Unknown formula type: {other}")

end EtJson

def etErr (e : EtError) : Json :=
  Json.mkObj [("ok", false), ("error", toJson e.message), ("error_code", toJson e.code)]

/-- Answer an `evidence_trust_check` request. `worlds = none` reports every world. -/
def evidenceTrustCheck (model : Json) (formulas : List Json) (worlds : Option (List String)) : Json :=
  match EtJson.decodeModel model with
  | .error e => etErr e
  | .ok (m, names) =>
    let report := worlds.getD names
    match report.find? (fun w => !names.contains w) with
    | some w => etErr ⟨"unknown_world", s!"worlds: unknown world \"{w}\""⟩
    | none =>
    match report.find? (fun w => report.count w > 1) with
    | some w => etErr ⟨"malformed_spec", s!"worlds: \"{w}\" is listed more than once"⟩
    | none =>
      let idx (w : String) : Nat := (names.findIdx? (· == w)).getD 0
      let item (fj : Json) (i : Nat) : Json :=
        let base := [("index", toJson i)]
        match EtJson.decodeFormula m.agents fj with
        | .error e => Json.mkObj (base ++ [("error", toJson e.message), ("error_code", toJson e.code)])
        | .ok f =>
          match sat m f with
          | .error msg => Json.mkObj (base ++ [("error", toJson msg), ("error_code", "check_failed")])
          | .ok mask =>
            let holds (w : String) := mask.testBit (idx w)
            Json.mkObj (base ++ [
              ("satisfying", toJson (report.filter holds)),
              ("holds", Json.mkObj (report.map fun w => (w, toJson (holds w)))),
              ("true_in_model", toJson (mask == Mask.full m.n))])
      Json.mkObj [("ok", true), ("result", Json.mkObj [
        ("worlds", toJson report),
        ("results", Json.arr (formulas.zipIdx.map fun (f, i) => item f i).toArray)])]
```

- [ ] **Step 4: Dispatch.** In `Validate/Core.lean`: `import Validate.EvidenceTrust`; add the constructor `| evidenceTrustCheck (model : Json) (formulas : List Json) (worlds : Option (List String))` to `Request`; add to `parseRequest`

```lean
  | "evidence_trust_check" =>
    let worlds ← match ← optField j "worlds" with
      | none => pure none
      | some v => pure (some (← (← v.getArr?).toList.mapM (·.getStr?)))
    return .evidenceTrustCheck (← field j "model") (← (← field j "formulas").getArr?).toList worlds
```

and to `handleRequest` `| .evidenceTrustCheck model fs ws => evidenceTrustCheck model fs ws`. In `Gamen/Protocol.lean` set `protocolVersion := 8`; in `Tests/ValidateVersion.lean` change the exact-bytes test and the numeric test from 7 to 8 (use python `replace`; BSD `sed -i` needs a suffix argument).

- [ ] **Step 5: Run.** `lake build 2>&1 | grep -E "error|Build completed"; lake test 2>&1 | grep -E "✗|passed"`. Expected: all pass. Fix the C3 test to the code that fires.

- [ ] **Step 6: Mutation check on the wire.** (a) make `decodeFormula` accept `announce` without `then` by defaulting it to `top`: the missing-`then` test must fail; (b) delete the `onlyKeys` call in `decodeModel`: the `trusts` test must fail; (c) accept `"0.75"` in `parseRat`: the bad_rational test must fail. Revert each.

- [ ] **Step 7: Run `compare.py`.** `python3 tools/compare/compare.py 2>&1 | tail -4` (slow; run in the background and read the output file). Expected: TOTAL row ends `103`.

- [ ] **Step 8: Commit.**

```bash
git add Validate/EvidenceTrust.lean Tests/ValidateEvidenceTrust.lean Validate/Core.lean Gamen/Protocol.lean Tests/ValidateVersion.lean Tests/Main.lean
git commit -m "Add the evidence_trust_check request (protocol 8; #3, item 4)

Co-Authored-By: Claude Sonnet 5.5 <noreply@anthropic.com>"
```

---

### Task 5: Documentation, adversarial review, follow-up issue

**Files:**
- Modify: `Validate.lean` (docs for the request), `PORTING.md` ("Lean-only additions" row), `Gamen/EvidenceTrust.lean` (module docstring: model, semantics, what is not covered)
- Create: `docs/assessment/adversarial-review-evidence-trust-<date>.md`

- [ ] **Step 1: Docs.** Add an `evidence_trust_check` section to `Validate.lean` in the style of the existing ones (request, model fields, formula types, reply, error codes, limits, tests path) and the usage line `{"action": "evidence_trust_check", "model": {...}, "formulas": [...]}   (Lean-only)`. Add the `PORTING.md` row (done: library, request, tests; not done: Theorems 1-2, Perrotin et al., Hunter). Write the module docstring of `Gamen/EvidenceTrust.lean` from the spec: definitions with PDF page numbers, the two source corrections, `R_i` read directly, no truth precondition on announcements.

- [ ] **Step 2: Adversarial review.** Copy only the deliverable (`Gamen/EvidenceTrust.lean`, `Validate/EvidenceTrust.lean`, `Tests/EvidenceTrust.lean`, `Tests/ValidateEvidenceTrust.lean`, the `Core.lean` diff) plus a text extract of the paper (`pdftotext -layout`) into a scratch directory with no plans, spec, `PORTING.md` or CLAUDE.md. Run two reviewers on it: a Fable agent (`Agent` tool, `model: fable`, told to read only that directory) and Gemini through `agy -p` with the files inlined and an instruction to use no tools. Brief: hostile, the author wrote code and tests, find silent wrong answers, wire/definition mismatches (re-derive two expected values by hand from the PDF definitions), tautological tests, resource blowups, doc mismatches. Reproduce every finding against the built binary before acting; fix real ones with a test each; record everything, including the findings that did not reproduce, in `docs/assessment/adversarial-review-evidence-trust-<date>.md` (same table layout as `adversarial-review-angels-demons-request-2026-10-14.md`).

- [ ] **Step 3: Follow-up design issue.** `gh issue create -R chapmanbe/gamen-lean` titled "Trust in a source's classification and discordance across sources: combining DL-BET with group announcements and trust-based revision", body: what DL-BET gives (evidence counts, quota, suspension of judgment on discordant sources), what is a plain port still open (Perrotin et al. LORI 2019 `~/Projects/Logic/Bergen/Bergen/lit/pdfs/Perrotin-etal-PGAaTiDL.pdf`; Hunter's papers in the same directory), what is research (combination), the clinical use case (cwyde / guideline-validation classifier labels as sources). Comment on issue #3 pointing at it. **Ask the user before posting** (outward-facing).

- [ ] **Step 4: Final verification.** `lake build`, `lake test` (all pass, count reported), `compare.py` at 103, `git status` clean except untracked handoff notes.

- [ ] **Step 5: Commit.**

```bash
git add Validate.lean PORTING.md Gamen/EvidenceTrust.lean docs/assessment/adversarial-review-evidence-trust-*.md
git commit -m "Document DL-BET and record its adversarial review (#3, item 4)

Co-Authored-By: Claude Sonnet 5.5 <noreply@anthropic.com>"
```
