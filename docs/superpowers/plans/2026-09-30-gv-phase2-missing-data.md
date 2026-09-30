# GV Phase 2 (Applicability Under Missing Data) Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** For each hand-written patient with incomplete data, label every paper-mode conflict definite, possible or absent by strong Kleene (K3), backed by kernel-checked soundness theorems and an exact completion-enumeration check.

**Architecture:** Part A adds a Lean-only, clinic-free module `Gamen.ManyValued.Completion` to gamen-lean: partial valuations, completions, `k3Status`, `exactStatus` and six theorems. Part B adds `GuidelineValidation.Applicability` to the Lean guideline-validation port: three data files (facts, draft condition definitions, patients), a condition compiler, and a new `validate-guidelines applicability` subcommand that runs existing conflict detection unchanged and assesses each conflict per patient.

**Tech Stack:** Lean 4.34.0 (`~/.elan/bin/lake`; `lake` may not be on `PATH`), Plausible v4.34.0, JSON data files.

**Spec:** `docs/superpowers/specs/2026-09-30-gv-phase2-missing-data-design.md` (gamen-lean). Parent plan: `plans/logic-for-guideline-validation-2026-09-29.md`, Phase 2.

## Global Constraints

- **No `sorry`**, no `native_decide` in Part A theorems; axiom audits are allowlists (`propext`, `Quot.sound`, `Classical.choice`) via `#assert_kernel_only`.
- **No `partial def`** in library code; recursion over JSON uses explicit fuel (`condFuel = 32`), and running out is an `Except` error, never a default.
- **`error` becomes `Except`**, never `panic!`.
- **Domain knowledge in data, not code.** Every condition definition lives in `data/applicability/conditions.json` with verbatim source quotes and `status: "draft"`. Only Brian sets `"approved"`.
- **Never write to the canonical repo** (`~/Projects/Logic/Julia/guideline-validation`); read it by path.
- **`conflicts` output must stay byte-identical**: `test/golden/` parity tests keep passing.
- American English in all prose and comments.
- Cite OLT anchors as `ManyValued.lean` does (`[thr:skl, defn 1]`).
- Commit trailer on every commit:
  ```
  Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>
  Claude-Session: https://claude.ai/code/session_015BTUu2EoNw4LmcNiY5CvzM
  ```

## Repos, branches, order

- **Part A** in gamen-lean (`/Users/brainchapman/Projects/Logic/gamen-lean`), worktree branch `gv-phase2-completion`. Review, then merge to `main` **before Part B builds**: the port's `lakefile.toml` has `path = "../../gamen-lean"`, so it compiles against the gamen-lean *main checkout*.
- **Part B** in `/Users/brainchapman/Projects/Logic/Lean/guideline-validation`, worktree branch `phase2-applicability`. A worktree of the port sits at a different depth, so its `../../gamen-lean` path breaks: **work on a branch in the main checkout of the port** instead of a worktree (`git switch -c phase2-applicability`), or symlink. Its tests read the canonical repo via `GV_CANONICAL_REPO` (default `../../Julia/guideline-validation`).
- Build/test commands: gamen-lean `~/.elan/bin/lake build && ~/.elan/bin/lake test`; port `~/.elan/bin/lake build && ~/.elan/bin/lake test`.

## Review Focus

1. **A patient fixture that sets an enumerated fact to a value not in its list** (typo like `"G3"` for `"G3a"`): must be a load error naming the patient and fact, never a silently unknown fact. Pinned in Task B2.
2. **A condition string in the data that has no definition** (the next extraction adds a new `conditional`): the conflict must be listed as undefined and skipped, never assessed as if unconditional. Pinned in Task B3.
3. **A definition whose conditions contradict through an enumerated fact** (two stages at once): K3 says possible, exact says never, and the row must be flagged `[K3 over-warns]`. Pinned in Task B3.
4. **An `approved` definition missing `approved_by` or `approved_on`**: load error, so nobody can mark a definition approved anonymously. Pinned in Task B2.
5. **Draft definitions in a real run**: the banner must say "DRAFT, not for paper use" and JSON `for_paper_use` must be `false`. Pinned in Task B4.

---

## Part A: gamen-lean, `Gamen.ManyValued.Completion`

### Task A1: Completions, statuses, soundness theorems, witnesses

The code below was prototyped against gamen-lean `main` at `13b2d51` and compiles as written; every theorem's axioms are within the allowlist.

**Files:**
- Create: `Gamen/ManyValued/Completion.lean`
- Modify: `Gamen.lean` (add `import Gamen.ManyValued.Completion` after `import Gamen.ManyValued`, line 34)
- Create: `Tests/Completion.lean`
- Modify: `Tests/Main.lean` (import; unit cases; properties; totals)

**Interfaces:**
- Consumes (from `Gamen.ManyValued`): `TV3` (`.t .u .f`), `TV3.ofBool`, `negK conjK3 disjK3 implK3`, `strongKleene`, `classical`, `eval`, `isCore`, `eval_core_ok`, `eval_not_ok/and_ok/or_ok/implies_ok`, `strongKleene_agrees_classical`, `atomList`, `dedup`, `lookup`.
- Produces (namespace `Gamen.ManyValued`):
  - `def Completes (p : Atom → TV3) (c : Atom → Bool) : Prop`
  - `def TV3.le : TV3 → TV3 → Bool`
  - `inductive K3Status | definite | possible | absent` (`DecidableEq, Repr`)
  - `inductive ExactStatus | always | sometimes | never | noAdmissibleCompletion` (`DecidableEq, Repr`)
  - `def k3Status (f : Formula) (p : Atom → TV3) : Except String K3Status`
  - `def admissible (cs : List (List Atom)) (c : Atom → Bool) : Bool`
  - `def completionsOn (p : Atom → TV3) : List Atom → List (List (Atom × Bool))`
  - `def exactStatus (f : Formula) (p : Atom → TV3) (cs : List (List Atom)) : Except String ExactStatus`
  - theorems `strongKleene_monotone`, `definite_sound`, `absent_sound`, `mixed_possible`

- [ ] **Step 1: Write the failing tests.** Create `Tests/Completion.lean`:

```lean
import Gamen.ManyValued.Completion
import Tests.ManyValued

/-!
# Tests for `Gamen.ManyValued.Completion` (Lean-only)

Spec: `docs/superpowers/specs/2026-09-30-gv-phase2-missing-data-design.md`.
Kernel-checked witnesses (theorem 5), the axiom audit, unit `cases`, and
the predicate for the Plausible property in `Tests/Main.lean`.
-/

namespace CompletionTests

open Gamen Gamen.ManyValued

def p : Formula := .atom "p"
def q : Formula := .atom "q"
def allU : Atom → TV3 := fun _ => .u

/-! ## Theorem 5: the converse of `mixed_possible` fails (`decide`) -/

/-- `p ∧ ¬p` with `p` unknown: K3 says possible, yet no completion makes it true. -/
theorem contradiction_possible : k3Status (.and p (.not p)) allU = .ok .possible := by decide
theorem contradiction_never : exactStatus (.and p (.not p)) allU [] = .ok .never := by decide
/-- The same through a constraint: exactly one of p, q. -/
theorem exclusive_possible : k3Status (.and p q) allU = .ok .possible := by decide
theorem exclusive_never : exactStatus (.and p q) allU [[⟨"p"⟩, ⟨"q"⟩]] = .ok .never := by decide
/-- K3 has no tautologies, but the exact check sees `p ∨ ¬p` hold everywhere. -/
theorem lem_always : exactStatus (.or p (.not p)) allU [] = .ok .always := by decide
/-- Known facts that break a constraint admit no completion. -/
theorem violated :
    exactStatus p (fun _ => .t) [[⟨"p"⟩, ⟨"q"⟩]] = .ok .noAdmissibleCompletion := by decide

#assert_kernel_only
  strongKleene_tables_monotone strongKleene_monotone completes_le completion_value
  definite_sound absent_sound mixed_possible
  contradiction_possible contradiction_never exclusive_possible exclusive_never lem_always violated

/-! ## Unit cases -/

def cases : List (String × Bool) := [
  ("Completion: all known, p ∧ q true → definite, always",
    k3Status (.and p q) (fun _ => .t) == .ok .definite
      && exactStatus (.and p q) (fun _ => .t) [] == .ok .always),
  ("Completion: q known false → p ∧ q absent, never",
    let v : Atom → TV3 := fun a => if a.name == "q" then .f else .u
    k3Status (.and p q) v == .ok .absent && exactStatus (.and p q) v [] == .ok .never),
  ("Completion: p unknown → p possible, sometimes",
    k3Status p allU == .ok .possible && exactStatus p allU [] == .ok .sometimes),
  ("Completion: completionsOn fixes known atoms (p=t, q=u gives 2)",
    (completionsOn (fun a => if a.name == "p" then .t else .u) [⟨"p"⟩, ⟨"q"⟩]).length == 2),
  ("Completion: k3Status errors on a non-core formula (□p)",
    ManyValuedTests.isErr (k3Status (.box p) allU)),
  ("Completion: exactStatus errors on a non-core formula (□p)",
    ManyValuedTests.isErr (exactStatus (.box p) allU []))
]

/-! ## Plausible support -/

/-- A partial valuation of p, q, r: `k` says known, `b` is the value. -/
def partialVal (kp bp kq bq kr br : Bool) (a : Atom) : TV3 :=
  let val (k b : Bool) : TV3 := if k then TV3.ofBool b else .u
  if a.name == "p" then val kp bp else if a.name == "q" then val kq bq
  else if a.name == "r" then val kr br else .u

/-- Theorems 2–4 at run time: definite ⇒ always, absent ⇒ never (or no
admissible completion under the p/q constraint), so sometimes ⇒ possible. -/
def k3ExactConsistent (f : Formula) (kp bp kq bq kr br constrain : Bool) : Bool :=
  let v := partialVal kp bp kq bq kr br
  let cs := if constrain then [[⟨"p"⟩, ⟨"q"⟩]] else []
  match k3Status f v, exactStatus f v cs with
  | .ok .definite, .ok e => e == .always || e == .noAdmissibleCompletion
  | .ok .absent, .ok e => e == .never || e == .noAdmissibleCompletion
  | .ok .possible, .ok _ => true
  | _, _ => false

end CompletionTests
```

  In `Tests/Main.lean`: add `import Tests.Completion` after `import Tests.ManyValued` (line 32). In `main`, change
  `for (name, ok) in ManyValuedTests.cases ++ specCases do` to
  `for (name, ok) in ManyValuedTests.cases ++ specCases ++ CompletionTests.cases do`, and in `total` change
  `+ ManyValuedTests.cases.length + specCases.length` to
  `+ ManyValuedTests.cases.length + specCases.length + CompletionTests.cases.length`.
  In `properties`, after the last `ManyValued:` entry, add:

```lean
    ("Completion: K3 status never contradicts the exact check (theorems 2–4)",
      run (NamedBinder "f" <| ∀ f : ManyValuedTests.CoreFormula,
        NamedBinder "kp" <| ∀ kp : Bool, NamedBinder "bp" <| ∀ bp : Bool,
        NamedBinder "kq" <| ∀ kq : Bool, NamedBinder "bq" <| ∀ bq : Bool,
        NamedBinder "kr" <| ∀ kr : Bool, NamedBinder "br" <| ∀ br : Bool,
        NamedBinder "c" <| ∀ c : Bool,
        CompletionTests.k3ExactConsistent f.getFormula kp bp kq bq kr br c = true) 200),
```

- [ ] **Step 2: Run to confirm failure.** `~/.elan/bin/lake build Tests` → FAIL: `unknown module prefix 'Gamen.ManyValued.Completion'` (or unknown identifiers).

- [ ] **Step 3: Implement.** Create `Gamen/ManyValued/Completion.lean`:

```lean
import Gamen.ManyValued

/-!
# Completions of partial valuations (Lean-only)

Spec: `docs/superpowers/specs/2026-09-30-gv-phase2-missing-data-design.md`.
A partial valuation gives each atom t, f or u (unknown). A completion fills
in every u classically. Strong Kleene (K3) `[thr:skl, defn 1]` is sound for
completions but not complete:

- a K3 value of t (f) means true (false) in *every* completion
  (`definite_sound`, `absent_sound`), so a formula true in some completion
  and false in another is u (`mixed_possible`);
- the converse fails: `p ∧ ¬p` is u with `p` unknown, yet false in every
  completion (`Tests/Completion.lean`, theorem 5).

`exactStatus` measures the gap by enumerating completions, optionally under
`exactlyOne` constraints (one value per enumerated fact). The soundness
theorems quantify over all completions, so they hold a fortiori for the
admissible ones.

Built for `decide`, like `Gamen.ManyValued`: no `TreeSet`, structural
recursion only.
-/

open Gamen

namespace Gamen.ManyValued

/-- `c` completes `p`: it keeps every known value and fills in each `u`. -/
def Completes (p : Atom → TV3) (c : Atom → Bool) : Prop :=
  ∀ a, p a = .u ∨ p a = TV3.ofBool (c a)

/-- The information order: `u` below everything, `t` and `f` incomparable. -/
def TV3.le : TV3 → TV3 → Bool
  | .u, _ => true
  | .t, .t => true
  | .f, .f => true
  | _, _ => false

/-- The K3 tables are monotone in the information order (checked by `decide`). -/
theorem strongKleene_tables_monotone :
    (∀ a c, TV3.le a c = true → TV3.le (negK a) (negK c) = true) ∧
    (∀ a b c d, TV3.le a c = true → TV3.le b d = true → TV3.le (conjK3 a b) (conjK3 c d) = true) ∧
    (∀ a b c d, TV3.le a c = true → TV3.le b d = true → TV3.le (disjK3 a b) (disjK3 c d) = true) ∧
    (∀ a b c d, TV3.le a c = true → TV3.le b d = true → TV3.le (implK3 a b) (implK3 c d) = true) := by
  decide

/-- **Theorem 1 (monotonicity).** Refining unknowns never changes a t or f. -/
theorem strongKleene_monotone {p q : Atom → TV3} (hpq : ∀ a, TV3.le (p a) (q a) = true) :
    ∀ f, isCore f = true → ∃ x y, eval strongKleene p f = .ok x ∧
      eval strongKleene q f = .ok y ∧ TV3.le x y = true := by
  intro f hf
  obtain ⟨m1, m2, m3, m4⟩ := strongKleene_tables_monotone
  induction f with
  | atomF a => exact ⟨p a, q a, rfl, rfl, hpq a⟩
  | not a ih =>
    obtain ⟨x, y, hx, hy, hle⟩ := ih hf
    exact ⟨_, _, eval_not_ok hx, eval_not_ok hy, m1 x y hle⟩
  | and a b iha ihb =>
    simp only [isCore, Bool.and_eq_true] at hf
    obtain ⟨x, y, hx, hy, h1⟩ := iha hf.1
    obtain ⟨x', y', hx', hy', h2⟩ := ihb hf.2
    exact ⟨_, _, eval_and_ok hx hx', eval_and_ok hy hy', m2 x x' y y' h1 h2⟩
  | or a b iha ihb =>
    simp only [isCore, Bool.and_eq_true] at hf
    obtain ⟨x, y, hx, hy, h1⟩ := iha hf.1
    obtain ⟨x', y', hx', hy', h2⟩ := ihb hf.2
    exact ⟨_, _, eval_or_ok hx hx', eval_or_ok hy hy', m3 x x' y y' h1 h2⟩
  | implies a b iha ihb =>
    simp only [isCore, Bool.and_eq_true] at hf
    obtain ⟨x, y, hx, hy, h1⟩ := iha hf.1
    obtain ⟨x', y', hx', hy', h2⟩ := ihb hf.2
    exact ⟨_, _, eval_implies_ok hx hx', eval_implies_ok hy hy', m4 x x' y y' h1 h2⟩
  | _ => simp [isCore] at hf

theorem completes_le {p : Atom → TV3} {c : Atom → Bool} (hc : Completes p c) :
    ∀ a, TV3.le (p a) (TV3.ofBool (c a)) = true := by
  intro a
  rcases hc a with h | h <;> rw [h] <;> cases c a <;> rfl

/-- A completion's classical value lies above the K3 value. -/
theorem completion_value {p : Atom → TV3} {c : Atom → Bool} {f : Formula} {x : TV3}
    (hf : isCore f = true) (hc : Completes p c) (hx : eval strongKleene p f = .ok x) :
    ∃ b, eval classical c f = .ok b ∧ TV3.le x (TV3.ofBool b) = true := by
  obtain ⟨x', y, hx', hy, hle⟩ := strongKleene_monotone (completes_le hc) f hf
  obtain ⟨b, hb⟩ := eval_core_ok classical c f hf
  have hagree := strongKleene_agrees_classical c f hf
  rw [hy, hb] at hagree
  have hy' : y = TV3.ofBool b := by cases hagree; rfl
  rw [hx] at hx'
  cases hx'
  exact ⟨b, hb, hy' ▸ hle⟩

/-- **Theorem 2.** K3 value t ⇒ true in every completion. -/
theorem definite_sound {p : Atom → TV3} {c : Atom → Bool} {f : Formula}
    (hf : isCore f = true) (h : eval strongKleene p f = .ok .t) (hc : Completes p c) :
    eval classical c f = .ok true := by
  obtain ⟨b, hb, hle⟩ := completion_value hf hc h
  cases b <;> simp_all [TV3.le, TV3.ofBool]

/-- **Theorem 3.** K3 value f ⇒ false in every completion. -/
theorem absent_sound {p : Atom → TV3} {c : Atom → Bool} {f : Formula}
    (hf : isCore f = true) (h : eval strongKleene p f = .ok .f) (hc : Completes p c) :
    eval classical c f = .ok false := by
  obtain ⟨b, hb, hle⟩ := completion_value hf hc h
  cases b <;> simp_all [TV3.le, TV3.ofBool]

/-- **Theorem 4.** True in one completion and false in another ⇒ K3 value u.
(The parent plan's "possible ⇔ some but not all" is false; see the module
docstring.) -/
theorem mixed_possible {p : Atom → TV3} {c₁ c₂ : Atom → Bool} {f : Formula}
    (hf : isCore f = true) (h₁ : Completes p c₁) (h₂ : Completes p c₂)
    (e₁ : eval classical c₁ f = .ok true) (e₂ : eval classical c₂ f = .ok false) :
    eval strongKleene p f = .ok .u := by
  obtain ⟨x, hx⟩ := eval_core_ok strongKleene p f hf
  cases x with
  | t => rw [definite_sound hf hx h₂] at e₂; cases e₂
  | f => rw [absent_sound hf hx h₁] at e₁; cases e₁
  | u => exact hx

/-! ## Statuses -/

/-- The K3 verdict: t, u, f. -/
inductive K3Status where
  | definite | possible | absent
  deriving DecidableEq, Repr

/-- The verdict over admissible completions. `noAdmissibleCompletion`
means the known facts already break a constraint: a data error, never a
verdict. -/
inductive ExactStatus where
  | always | sometimes | never | noAdmissibleCompletion
  deriving DecidableEq, Repr

def k3Status (f : Formula) (p : Atom → TV3) : Except String K3Status := do
  match ← eval strongKleene p f with
  | .t => pure .definite
  | .u => pure .possible
  | .f => pure .absent

/-- `c` makes exactly one atom of each group true. Groups should not
repeat an atom. -/
def admissible (cs : List (List Atom)) (c : Atom → Bool) : Bool :=
  cs.all fun g => (g.filter c).length == 1

/-- Every classical assignment to `atoms` that keeps `p`'s known values:
`2ᵏ` of them for `k` unknown atoms. -/
def completionsOn (p : Atom → TV3) : List Atom → List (List (Atom × Bool))
  | [] => [[]]
  | a :: as =>
    let rest := completionsOn p as
    let choices := match p a with
      | .t => [true]
      | .f => [false]
      | .u => [true, false]
    choices.flatMap fun b => rest.map fun r => (a, b) :: r

/-- The exact status of `f` over the completions of `p` that satisfy `cs`,
by enumeration over the atoms of `f` and `cs`. Errors if `f` is not
propositional. -/
def exactStatus (f : Formula) (p : Atom → TV3) (cs : List (List Atom)) :
    Except String ExactStatus := do
  let atoms := dedup (atomList f ++ cs.flatten)
  let asgs := (completionsOn p atoms).filter fun asg => admissible cs (lookup asg)
  let vals ← asgs.mapM fun asg => eval classical (lookup asg) f
  if vals.isEmpty then return .noAdmissibleCompletion
  if vals.all id then return .always
  if vals.all (! ·) then return .never
  return .sometimes

end Gamen.ManyValued
```

  Add `import Gamen.ManyValued.Completion` to `Gamen.lean` after `import Gamen.ManyValued`.

- [ ] **Step 4: Run tests.** `~/.elan/bin/lake build && ~/.elan/bin/lake test 2>&1 | grep -E "Completion|passed|✗"` → all `Completion:` lines ✓, final line `N/N passed`.

- [ ] **Step 5: Plant a bug.** In `Gamen/ManyValued.lean`, change `conjK3`'s `| .u, .f => .f` to `| .u, .f => .u`. Run `~/.elan/bin/lake build Tests 2>&1 | grep -E "error" | head -5`: expect failures (the monotonicity `decide`, or the existing `conjK3`-dependent tests, or the Plausible property). Revert with `git checkout Gamen/ManyValued.lean` and rebuild. Record in the commit message which check caught it.

- [ ] **Step 6: Commit.**

```bash
git add Gamen/ManyValued/Completion.lean Gamen.lean Tests/Completion.lean Tests/Main.lean
git commit -m "ManyValued.Completion: K3 statuses, exact check, soundness theorems

<trailer>"
```

### Task A2: Theorem 6, the enumerator is correct

**Files:**
- Modify: `Gamen/ManyValued/Completion.lean` (append section `## Theorem 6`)
- Modify: `Tests/Completion.lean` (add `exactStatus_spec` and each helper lemma to the `#assert_kernel_only` list)

**Interfaces:**
- Consumes: Task A1's definitions.
- Produces:

```lean
/-- `c` is a completion of `p` that satisfies every constraint. -/
def AdmissibleCompletion (p : Atom → TV3) (cs : List (List Atom)) (c : Atom → Bool) : Prop :=
  Completes p c ∧ admissible cs c = true

/-- **Theorem 6.** `exactStatus` says what it enumerates. -/
theorem exactStatus_spec {f : Formula} {p : Atom → TV3} {cs : List (List Atom)}
    (hf : isCore f = true) :
    match exactStatus f p cs with
    | .ok .noAdmissibleCompletion => ¬ ∃ c, AdmissibleCompletion p cs c
    | .ok .always => (∃ c, AdmissibleCompletion p cs c) ∧
        ∀ c, AdmissibleCompletion p cs c → eval classical c f = .ok true
    | .ok .never => (∃ c, AdmissibleCompletion p cs c) ∧
        ∀ c, AdmissibleCompletion p cs c → eval classical c f = .ok false
    | .ok .sometimes => (∃ c, AdmissibleCompletion p cs c ∧ eval classical c f = .ok true) ∧
        (∃ c, AdmissibleCompletion p cs c ∧ eval classical c f = .ok false)
    | .error _ => False
```

This is the one task whose proof was not prototyped. The statement above is fixed: **do not weaken it** (for example by adding hypotheses beyond `hf`). If the proof stalls after a serious attempt (more than ~400 lines or several hours), stop and report which lemma is stuck.

- [ ] **Step 1: State the theorem with `sorry` locally only** (never committed) and confirm it elaborates: `~/.elan/bin/lake build Gamen.ManyValued.Completion`.

- [ ] **Step 2: Prove the helper lemmas, one at a time, building after each:**
  1. `mem_dedup : a ∈ dedup l ↔ a ∈ l` and `nodup_dedup : (dedup l).Nodup` (induction on the `foldl`; generalize the accumulator).
  2. `eval_congr {m : Matrix V} {v w : Atom → V} (f : Formula) (h : ∀ a ∈ atomList.go f, v a = w a) : eval m v f = eval m w f` (induction on `f`, every constructor).
  3. `mem_completionsOn : asg ∈ completionsOn p as ↔ asg.map Prod.fst = as ∧ ∀ x ∈ asg, p x.1 = .u ∨ p x.1 = TV3.ofBool x.2` (induction on `as`).
  4. `lookup_eq_of_mem : (asg.map Prod.fst).Nodup → (a, b) ∈ asg → lookup asg a = b`.
  5. `admissible_congr : (∀ g ∈ cs, ∀ a ∈ g, c a = d a) → admissible cs c = admissible cs d` (the filter depends only on atoms in the groups).
  6. **Restriction:** for `Completes p c`, `as.map (fun a => (a, c a)) ∈ completionsOn p as`, and its `lookup` agrees with `c` on `as` when `as.Nodup`.
  7. **Extension:** for `asg ∈ completionsOn p as`, `ext a := if a ∈ as then lookup asg a else (p a == .t)` completes `p` and agrees with `lookup asg` on `as`.

- [ ] **Step 3: Prove `exactStatus_spec`.** Unfold `exactStatus`; `eval_core_ok` rules out `.error` for every enumerated valuation (so `mapM` succeeds); split on `vals.isEmpty`, `vals.all id`, `vals.all (! ·)`; use 6 to move from a completion to an enumerated assignment, and 7 back, with 2 and 5 (atoms of `f` and `cs` are in `atoms` by 1).

- [ ] **Step 4: Audit and test.** Add `exactStatus_spec` and every helper to `#assert_kernel_only` in `Tests/Completion.lean`. `~/.elan/bin/lake build && ~/.elan/bin/lake test 2>&1 | tail -1` → `N/N passed`. `grep -n "sorry" Gamen/ManyValued/Completion.lean` → no output.

- [ ] **Step 5: Commit.**

```bash
git add Gamen/ManyValued/Completion.lean Tests/Completion.lean
git commit -m "ManyValued.Completion: prove exactStatus correct (theorem 6)

<trailer>"
```

### Task A3: Review and merge Part A

- [ ] **Step 1:** Dispatch a reviewer (Fable) on branch `gv-phase2-completion` with the spec, not the implementer's report. Ask for: faithfulness of `Completes`/`admissible` to the spec, whether any theorem statement is weaker than the spec's, and the axiom audit.
- [ ] **Step 2:** Fix findings, rerun `~/.elan/bin/lake test`.
- [ ] **Step 3:** Ask Brian to approve the merge. On approval: `git switch main && git merge --no-ff gv-phase2-completion`, then `~/.elan/bin/lake build` in the gamen-lean main checkout (Part B compiles against it).

---

## Part B: guideline-validation port, `GuidelineValidation.Applicability`

All paths relative to `/Users/brainchapman/Projects/Logic/Lean/guideline-validation`.

### Task B1: Data files, with verified source quotes

**Files:**
- Create: `data/applicability/facts.json`
- Create: `data/applicability/conditions.json`
- Create: `data/applicability/patients.json`

**Interfaces:**
- Produces the JSON shapes Task B2 decodes: `facts.json` `{"facts": [{"name", "kind": "bool"|"enum", "values"?, "sources"}]}`; `conditions.json` `{"conditions": [{"key", "definition", "sources", "note", "status", "approved_by", "approved_on"}]}`; `patients.json` `{"patients": [{"id", "description", "exercises", "facts": {name: bool | string}}]}`.

Source files (read-only, canonical repo): `guidelines/KDIGO-2024-CKD-Guideline.txt`, `guidelines/KDIGO-2017-CKD-MBD-Guideline.txt`, and R18's `text` in `data/derived/blumenthal-2026_extracted.json`.

- [ ] **Step 1: Verify every quote below appears verbatim** (modulo line breaks) before writing it. Each command must print a match:

```bash
G=~/Projects/Logic/Julia/guideline-validation/guidelines
grep -n "Table 2| GFR categories in CKD" $G/KDIGO-2024-CKD-Guideline.txt
grep -n "Recommendation 3.3.1.1: We suggest maintaining a protein intake of 0.8 g/kg body weight/d in adults with" $G/KDIGO-2024-CKD-Guideline.txt
grep -n "Actions to manage hyperkalemia (potassium >5.5 mmol/l) in chronic kidney disease" $G/KDIGO-2024-CKD-Guideline.txt
grep -n "4.1.8: In patients with CKD G3a–G5D, we suggest limiting dietary phosphate intake in the treatment of hyper-" $G/KDIGO-2017-CKD-MBD-Guideline.txt
python3 -c "import json; d=json.load(open('$HOME/Projects/Logic/Julia/guideline-validation/data/derived/blumenthal-2026_extracted.json')); print([r['text'] for r in d if r['id']=='R18'])"
```

  If any quote differs, copy the source's exact wording into the JSON instead, and say so in the task report.

- [ ] **Step 2: Write `data/applicability/facts.json`:**

```json
{
  "facts": [
    {"name": "ckd_status", "kind": "enum",
     "values": ["none", "G1", "G2", "G3a", "G3b", "G4", "G5"],
     "sources": [{"source": "KDIGO 2024 CKD", "locator": "Table 2", "quote": "Table 2| GFR categories in CKD"}],
     "note": "G1-G5 are KDIGO's GFR categories; 'none' (no CKD) is ours. G5D (on dialysis) is G5 here."},
    {"name": "age_group", "kind": "enum", "values": ["child", "adult"],
     "sources": [{"source": "KDIGO 2024 CKD", "locator": "Recommendation 3.3.1.1", "quote": "in adults with"},
                 {"source": "ACC/AHA 2026 (Blumenthal et al.)", "locator": "R18", "quote": "In adults with fasting TG levels of 150 to 499 mg/dL"}],
     "note": "Categorical; neither source defines the age boundary. Phase 2 takes the category as given."},
    {"name": "fasting_tg", "kind": "enum", "values": ["below_150", "150_to_499", "500_or_more"],
     "sources": [{"source": "ACC/AHA 2026 (Blumenthal et al.)", "locator": "R18", "quote": "fasting TG levels of 150 to 499 mg/dL"}],
     "note": "Fasting triglycerides, mg/dL."},
    {"name": "hyperkalemia", "kind": "bool",
     "sources": [{"source": "KDIGO 2024 CKD", "locator": "Figure 32", "quote": "Actions to manage hyperkalemia (potassium >5.5 mmol/l) in chronic kidney disease"}],
     "note": "Serum potassium > 5.5 mmol/l."},
    {"name": "on_rasi", "kind": "bool",
     "sources": [{"source": "KDIGO 2024 CKD", "locator": "Ch. 3", "quote": "hyperkalemia on renin-angiotensin system inhibitor therapy"}],
     "note": "Taking a renin-angiotensin system inhibitor (ACEi or ARB). Quote is the restriction's applies_when text (data/conflicts/restrictions.json)."},
    {"name": "hyperphosphatemia", "kind": "bool",
     "sources": [{"source": "KDIGO 2017 CKD-MBD", "locator": "Recommendation 4.1.8", "quote": "in the treatment of hyperphosphatemia"}],
     "note": "Elevated serum phosphate; the source gives no threshold."}
  ]
}
```

- [ ] **Step 3: Write `data/applicability/conditions.json`.** Keys are the exact strings in the data. Definitions follow the cited source text, not the `applies_when` paraphrase; each `note` says where they differ.

```json
{
  "conditions": [
    {"key": "moderate_hypertriglyceridemia",
     "definition": {"and": [{"in": {"fact": "age_group", "values": ["adult"]}},
                            {"in": {"fact": "fasting_tg", "values": ["150_to_499"]}}]},
     "sources": [{"source": "ACC/AHA 2026 (Blumenthal et al.)", "locator": "R18",
                  "quote": "In adults with fasting TG levels of 150 to 499 mg/dL"}],
     "note": "R18's conditional slug. The slug omits 'adults'; the rec text includes it.",
     "status": "draft", "approved_by": null, "approved_on": null},
    {"key": "CKD G3-G5 (universal in this stage range)",
     "definition": {"and": [{"in": {"fact": "age_group", "values": ["adult"]}},
                            {"in": {"fact": "ckd_status", "values": ["G3a", "G3b", "G4", "G5"]}}]},
     "sources": [{"source": "KDIGO 2024 CKD", "locator": "Recommendation 3.3.1.1",
                  "quote": "We suggest maintaining a protein intake of 0.8 g/kg body weight/d in adults with CKD G3–G5 (2C)."}],
     "note": "The applies_when text omits 'adults'; Rec 3.3.1.1 includes it.",
     "status": "draft", "approved_by": null, "approved_on": null},
    {"key": "hyperkalemia on renin-angiotensin system inhibitor therapy",
     "definition": {"and": [{"in": {"fact": "ckd_status", "values": ["G1", "G2", "G3a", "G3b", "G4", "G5"]}},
                            {"fact": "hyperkalemia"}, {"fact": "on_rasi"}]},
     "sources": [{"source": "KDIGO 2024 CKD", "locator": "Figure 32",
                  "quote": "Actions to manage hyperkalemia (potassium >5.5 mmol/l) in chronic kidney disease"}],
     "note": "Figure 32 is scoped to CKD; the applies_when text does not say so.",
     "status": "draft", "approved_by": null, "approved_on": null},
    {"key": "hyperphosphatemia",
     "definition": {"and": [{"in": {"fact": "ckd_status", "values": ["G3a", "G3b", "G4", "G5"]}},
                            {"fact": "hyperphosphatemia"}]},
     "sources": [{"source": "KDIGO 2017 CKD-MBD", "locator": "Recommendation 4.1.8",
                  "quote": "In patients with CKD G3a–G5D, we suggest limiting dietary phosphate intake in the treatment of hyperphosphatemia"}],
     "note": "The applies_when text is only 'hyperphosphatemia'; Rec 4.1.8 limits it to CKD G3a–G5D.",
     "status": "draft", "approved_by": null, "approved_on": null}
  ]
}
```

- [ ] **Step 4: Write `data/applicability/patients.json`** (absent fact = unknown):

```json
{
  "patients": [
    {"id": "P1", "description": "Adult, CKD G4, hyperkalemic on a RASi, hyperphosphatemic, TG 150-499",
     "exercises": "every condition known true: all definite",
     "facts": {"ckd_status": "G4", "hyperkalemia": true, "on_rasi": true, "hyperphosphatemia": true,
               "age_group": "adult", "fasting_tg": "150_to_499"}},
    {"id": "P2", "description": "Adult without CKD, normal labs, not on a RASi",
     "exercises": "every condition known false: all absent",
     "facts": {"ckd_status": "none", "hyperkalemia": false, "on_rasi": false, "hyperphosphatemia": false,
               "age_group": "adult", "fasting_tg": "below_150"}},
    {"id": "P3", "description": "Nothing known",
     "exercises": "all unknown: all possible, exact sometimes",
     "facts": {}},
    {"id": "P4", "description": "Adult, CKD G3b, TG 150-499; potassium, phosphate and RASi use unknown",
     "exercises": "stage known, labs unknown: protein definite, others possible",
     "facts": {"ckd_status": "G3b", "age_group": "adult", "fasting_tg": "150_to_499"}},
    {"id": "P5", "description": "Hyperphosphatemia ruled out; everything else unknown",
     "exercises": "one known false fact makes the phosphate conflicts absent",
     "facts": {"hyperphosphatemia": false}},
    {"id": "P6", "description": "Child, CKD G4, hyperkalemic on a RASi, hyperphosphatemic",
     "exercises": "age rules out R18 and the adult-only protein restriction",
     "facts": {"age_group": "child", "ckd_status": "G4", "hyperkalemia": true, "on_rasi": true,
               "hyperphosphatemia": true}},
    {"id": "P7", "description": "Adult, CKD G2, on a RASi; potassium unknown",
     "exercises": "stage below G3 rules out protein and phosphate; potassium stays possible",
     "facts": {"ckd_status": "G2", "on_rasi": true, "age_group": "adult"}}
  ]
}
```

- [ ] **Step 5: Validate JSON syntax.** `for f in data/applicability/*.json; do python3 -m json.tool $f > /dev/null && echo ok $f; done` → three `ok`.

- [ ] **Step 6: Commit.**

```bash
git add data/applicability
git commit -m "Applicability data: fact vocabulary, draft condition definitions, patient fixtures

Definitions are drafts, quoted from KDIGO 2024, KDIGO 2017 CKD-MBD and the
ACC/AHA 2026 rec text; not approved for paper use.

<trailer>"
```

### Task B2: Vocabulary decoding, condition compiler, patient valuation

The code below was prototyped against the port's `main` at `22cadaf` (with Task A1's module inlined) and compiles.

**Files:**
- Create: `GuidelineValidation/Applicability.lean`
- Modify: `GuidelineValidation.lean` (add `import GuidelineValidation.Applicability`)
- Create: `GVTests/Applicability.lean`
- Modify: `GVTests/Main.lean` (import; group `("Applicability: loading", pure applicabilityLoadCases)`)

**Interfaces:**
- Consumes: `Gamen.ManyValued.Completion` (Task A1); `reqStr`, `optStr` (`Guideline.lean`).
- Produces (namespace `GuidelineValidation`):
  - `inductive FactKind | bool | enum (values : List String)`; `structure Fact { name : String, kind : FactKind }`
  - `def factAtom (name : String) (value : Option String := none) : Atom` (`"hyperkalemia"`, `"ckd_status=G3a"`)
  - `def compileCond (facts : List Fact) : Nat → Json → Except String Formula`
  - `def condFuel : Nat := 32`
  - `def factConstraints (facts : List Fact) : List (List Atom)`
  - `def knownAtoms (facts : List Fact) (known : Json) : Except String (List (Atom × TV3))`
  - `def partialValuation (known : List (Atom × TV3)) (a : Atom) : TV3`
  - `inductive ApprovalStatus | draft | approved`; `structure Condition { key : String, formula : Formula, status : ApprovalStatus }`
  - `structure Vocabulary { facts : List Fact, conditions : List Condition }`
  - `def parseVocabulary (factsContents conditionsContents : String) : Except String Vocabulary`
  - `structure Patient { id : String, description : String, known : List (Atom × TV3) }`
  - `def parsePatients (facts : List Fact) (contents : String) : Except String (Array Patient)`

- [ ] **Step 1: Write the failing tests.** Create `GVTests/Applicability.lean`:

```lean
import GuidelineValidation
import GVTests.Harness

open Lean (Json)
open Gamen Gamen.ManyValued GuidelineValidation

def testFacts : List Fact :=
  [ { name := "ckd_status", kind := .enum ["none", "G3a", "G4"] }
  , { name := "hyperphosphatemia", kind := .bool } ]

def compileStr (s : String) : Except String Formula := do
  compileCond testFacts condFuel (← Json.parse s)

def isErr {α : Type} : Except String α → Bool
  | .ok _ => false
  | .error _ => true

def knownStr (s : String) : Except String (List (Atom × TV3)) := do
  knownAtoms testFacts (← Json.parse s)

def factsJson : String :=
  "{\"facts\":[{\"name\":\"ckd_status\",\"kind\":\"enum\",\"values\":[\"none\",\"G3a\",\"G4\"]}," ++
  "{\"name\":\"hyperphosphatemia\",\"kind\":\"bool\"}]}"

def condJson (key status extra : String) : String :=
  "{\"conditions\":[{\"key\":\"" ++ key ++ "\",\"status\":\"" ++ status ++ "\"" ++ extra ++
  ",\"definition\":{\"fact\":\"hyperphosphatemia\"}}]}"

/-- Nested `not` `n` levels deep around a fact. -/
def deepNot : Nat → String
  | 0 => "{\"fact\":\"hyperphosphatemia\"}"
  | n + 1 => "{\"not\":" ++ deepNot n ++ "}"

def applicabilityLoadCases : List Case :=
  let g34 := "{\"in\":{\"fact\":\"ckd_status\",\"values\":[\"G3a\",\"G4\"]}}"
  [ { name := "compile: in + fact under and"
      ok := (compileStr ("{\"and\":[" ++ g34 ++ ",{\"fact\":\"hyperphosphatemia\"}]}")).map toString
              == .ok "((ckd_status=G3a ∨ ckd_status=G4) ∧ hyperphosphatemia)" }
  , { name := "compile: not", ok := (compileStr "{\"not\":{\"fact\":\"hyperphosphatemia\"}}").map toString == .ok "¬hyperphosphatemia" }
  , { name := "compile: unknown fact is an error", ok := isErr (compileStr "{\"fact\":\"diabetes\"}") }
  , { name := "compile: fact on an enumerated fact is an error", ok := isErr (compileStr "{\"fact\":\"ckd_status\"}") }
  , { name := "compile: in on a boolean fact is an error"
      ok := isErr (compileStr "{\"in\":{\"fact\":\"hyperphosphatemia\",\"values\":[\"x\"]}}") }
  , { name := "compile: in with a value not in the list is an error"
      ok := isErr (compileStr "{\"in\":{\"fact\":\"ckd_status\",\"values\":[\"G3\"]}}") }
  , { name := "compile: empty and is an error", ok := isErr (compileStr "{\"and\":[]}") }
  , { name := "compile: two keys in one node is an error"
      ok := isErr (compileStr "{\"fact\":\"hyperphosphatemia\",\"not\":{\"fact\":\"hyperphosphatemia\"}}") }
  , { name := "compile: nesting past condFuel is an error, not a default", ok := isErr (compileStr (deepNot 40)) }
  , { name := "compile: nesting within condFuel compiles", ok := !isErr (compileStr (deepNot 20)) }
  , { name := "constraints: one exactlyOne group per enumerated fact"
      ok := factConstraints testFacts == [[factAtom "ckd_status" (some "none"), factAtom "ckd_status" (some "G3a"),
                                           factAtom "ckd_status" (some "G4")]] }
  , { name := "patient: known enum value sets it t and the others f"
      ok := knownStr "{\"ckd_status\":\"G4\"}" ==
              .ok [(factAtom "ckd_status" (some "none"), .f), (factAtom "ckd_status" (some "G3a"), .f),
                   (factAtom "ckd_status" (some "G4"), .t)] }
  , { name := "patient: unlisted fact is u"
      ok := match knownStr "{\"hyperphosphatemia\":true}" with
            | .ok k => partialValuation k (factAtom "ckd_status" (some "G4")) == .u
                         && partialValuation k (factAtom "hyperphosphatemia") == .t
            | .error _ => false }
  , { name := "patient: enum value typo (G3 for G3a) is an error", ok := isErr (knownStr "{\"ckd_status\":\"G3\"}") }
  , { name := "patient: boolean given a string is an error", ok := isErr (knownStr "{\"hyperphosphatemia\":\"yes\"}") }
  , { name := "patient: unknown fact is an error", ok := isErr (knownStr "{\"diabetes\":true}") }
  , { name := "patient: parsePatients names the patient in the error"
      ok := match parsePatients testFacts "{\"patients\":[{\"id\":\"PX\",\"description\":\"d\",\"facts\":{\"ckd_status\":\"G3\"}}]}" with
            | .error e => e.startsWith "patient PX:"
            | .ok _ => false }
  , { name := "vocabulary: draft loads", ok := !isErr (parseVocabulary factsJson (condJson "k" "draft" "")) }
  , { name := "vocabulary: approved without approved_by/approved_on is an error"
      ok := isErr (parseVocabulary factsJson (condJson "k" "approved" "")) }
  , { name := "vocabulary: approved with approved_by and approved_on loads"
      ok := !isErr (parseVocabulary factsJson (condJson "k" "approved" ",\"approved_by\":\"Brian Chapman\",\"approved_on\":\"2026-10-01\"")) }
  , { name := "vocabulary: unknown status is an error", ok := isErr (parseVocabulary factsJson (condJson "k" "final" "")) }
  , { name := "vocabulary: duplicate key is an error"
      ok := isErr (parseVocabulary factsJson
              ("{\"conditions\":[{\"key\":\"k\",\"status\":\"draft\",\"definition\":{\"fact\":\"hyperphosphatemia\"}}," ++
               "{\"key\":\"k\",\"status\":\"draft\",\"definition\":{\"fact\":\"hyperphosphatemia\"}}]}")) } ]
```

  In `GVTests/Main.lean`: add `import GVTests.Applicability`, and append `, ("Applicability: loading", pure applicabilityLoadCases)` to `groups`.

  Note: `Except String (List (Atom × TV3))` needs `BEq` for `==`; `Atom` and `TV3` derive `BEq`/`DecidableEq`, and core provides `BEq (Except ε α)` only if you import it. If `==` on `Except` does not resolve, compare with a `match` as in the "unlisted fact is u" case.

- [ ] **Step 2: Run to confirm failure.** `~/.elan/bin/lake build GVTests 2>&1 | grep -m3 error` → unknown identifiers (`compileCond`, …).

- [ ] **Step 3: Implement.** Create `GuidelineValidation/Applicability.lean`:

```lean
import GuidelineValidation.Conflicts
import Gamen.ManyValued.Completion

/-!
# Applicability under missing data (GV Phase 2)

Spec: gamen-lean `docs/superpowers/specs/2026-09-30-gv-phase2-missing-data-design.md`.
Each paper-mode conflict applies when its rec's `conditional` (if any) and
its restriction's `applies_when` both hold. Those strings are defined in
`data/applicability/conditions.json` as formulas over patient facts
(`facts.json`). For a patient with incomplete facts (`patients.json`),
strong Kleene gives definite, possible or absent
(`Gamen.ManyValued.Completion.k3Status`), and an exact enumeration of
completions checks it (`exactStatus`).
-/

open Lean (Json toJson)
open Gamen Gamen.ManyValued

namespace GuidelineValidation

/-- A patient fact: boolean, or one value from a fixed list. -/
inductive FactKind where
  | bool
  | enum (values : List String)
  deriving BEq, Repr

structure Fact where
  name : String
  kind : FactKind
  deriving Repr

/-- The atom for a boolean fact, or for one value of an enumerated fact. -/
def factAtom (name : String) (value : Option String := none) : Atom :=
  match value with
  | none => ⟨name⟩
  | some v => ⟨s!"{name}={v}"⟩

def decodeFact (j : Json) : Except String Fact := do
  let name ← reqStr j "name"
  match ← reqStr j "kind" with
  | "bool" => return { name, kind := .bool }
  | "enum" =>
    let vs ← (← j.getObjVal? "values").getArr?
    let values ← vs.toList.mapM (·.getStr?)
    if values.isEmpty then throw s!"fact {name}: enum with no values"
    return { name, kind := .enum values }
  | k => throw s!"fact {name}: unknown kind {k}"

def findFact (facts : List Fact) (n : String) : Except String Fact :=
  match facts.find? (·.name == n) with
  | some f => .ok f
  | none => .error s!"unknown fact: {n}"

/-- Fold a nonempty list with a binary connective, left to right. -/
def foldConn (op : Formula → Formula → Formula) (what : String) : List Formula → Except String Formula
  | [] => .error s!"empty {what}"
  | f :: fs => .ok (fs.foldl op f)

/-- Compile a condition tree (`fact`, `in`, `and`, `or`, `not`) to a
formula over fact atoms. `fuel` bounds the nesting depth; running out is
an error, never a default. -/
def compileCond (facts : List Fact) : Nat → Json → Except String Formula
  | 0, _ => .error "condition nested too deeply"
  | fuel + 1, j => do
    let obj ← j.getObj?
    match obj.toList with
    | [("fact", n)] =>
      let n ← n.getStr?
      let f ← findFact facts n
      match f.kind with
      | .bool => return .atomF (factAtom n)
      | .enum _ => throw s!"fact {n} is enumerated; use \"in\""
    | [("in", body)] =>
      let n ← reqStr body "fact"
      let f ← findFact facts n
      let vs ← (← (← body.getObjVal? "values").getArr?).toList.mapM (·.getStr?)
      match f.kind with
      | .bool => throw s!"fact {n} is boolean; use \"fact\""
      | .enum allowed =>
        for v in vs do
          unless allowed.contains v do throw s!"fact {n} has no value {v}"
        foldConn .or "in" (vs.map fun v => .atomF (factAtom n (some v)))
    | [("and", xs)] => foldConn .and "and" (← (← xs.getArr?).toList.mapM (compileCond facts fuel))
    | [("or", xs)] => foldConn .or "or" (← (← xs.getArr?).toList.mapM (compileCond facts fuel))
    | [("not", x)] => return .not (← compileCond facts fuel x)
    | _ => throw s!"condition must have exactly one of fact, in, and, or, not: {j.compress}"

/-- Nesting depth allowed in a condition tree. -/
def condFuel : Nat := 32

/-- One `exactlyOne` group per enumerated fact. -/
def factConstraints (facts : List Fact) : List (List Atom) :=
  facts.filterMap fun f => match f.kind with
    | .enum vs => some (vs.map fun v => factAtom f.name (some v))
    | .bool => none

/-- A patient's known facts as atom values. A known enumerated fact sets
its value's atom `t` and the others `f`, so fixtures can't break an
`exactlyOne` constraint. -/
def knownAtoms (facts : List Fact) (known : Json) : Except String (List (Atom × TV3)) := do
  let obj ← known.getObj?
  let mut out := []
  for (n, v) in obj.toList do
    let f ← findFact facts n
    match f.kind, v with
    | .bool, .bool b => out := out ++ [(factAtom n, TV3.ofBool b)]
    | .enum vs, .str s =>
      unless vs.contains s do throw s!"fact {n} has no value {s}"
      out := out ++ vs.map fun w => (factAtom n (some w), if w == s then .t else .f)
    | _, _ => throw s!"fact {n}: value {v.compress} has the wrong type"
  return out

/-- Every atom not set by the patient's known facts is `u`. -/
def partialValuation (known : List (Atom × TV3)) (a : Atom) : TV3 :=
  ((known.find? (·.1 == a)).map (·.2)).getD .u

inductive ApprovalStatus where
  | draft | approved
  deriving BEq, Repr

/-- One entry of `conditions.json`: a data string (a rec `conditional` or
a restriction `applies_when`) and its compiled definition. -/
structure Condition where
  key : String
  formula : Formula
  status : ApprovalStatus
  deriving Repr

structure Vocabulary where
  facts : List Fact
  conditions : List Condition

def decodeCondition (facts : List Fact) (j : Json) : Except String Condition := do
  let key ← reqStr j "key"
  let formula ← (compileCond facts condFuel (← j.getObjVal? "definition")).mapError (s!"condition {key}: " ++ ·)
  let status ← match ← reqStr j "status" with
    | "draft" => pure ApprovalStatus.draft
    | "approved" =>
      if (← optStr j "approved_by").isNone || (← optStr j "approved_on").isNone then
        throw s!"condition {key}: approved without approved_by and approved_on"
      pure .approved
    | s => throw s!"condition {key}: unknown status {s}"
  return { key, formula, status }

def parseVocabulary (factsContents conditionsContents : String) : Except String Vocabulary := do
  let fj ← Json.parse factsContents
  let facts ← ((← (← fj.getObjVal? "facts").getArr?).toList.mapM decodeFact)
  let cj ← Json.parse conditionsContents
  let conditions ← (← (← cj.getObjVal? "conditions").getArr?).toList.mapM (decodeCondition facts)
  let keys := conditions.map (·.key)
  if keys.eraseDups.length != keys.length then throw "conditions.json: duplicate key"
  return { facts, conditions }

structure Patient where
  id : String
  description : String
  known : List (Atom × TV3)

def parsePatients (facts : List Fact) (contents : String) : Except String (Array Patient) := do
  let j ← Json.parse contents
  let arr ← (← j.getObjVal? "patients").getArr?
  arr.mapM fun pj => do
    let id ← reqStr pj "id"
    let known ← (knownAtoms facts (← pj.getObjVal? "facts")).mapError (s!"patient {id}: " ++ ·)
    return { id, description := ← reqStr pj "description", known }

end GuidelineValidation
```

  Add `import GuidelineValidation.Applicability` to `GuidelineValidation.lean`.

  Note: `optStr` (in `Guideline.lean`) returns `none` for JSON `null` and `""`, and for a missing key check its definition; if a missing key is an error rather than `none`, the "approved without approved_by" test still passes, since either way it is an error.

- [ ] **Step 4: Run tests.** `~/.elan/bin/lake build && ~/.elan/bin/lake test 2>&1 | grep -E "Applicability|failure"` → all ✓, `0 failure(s)`.

- [ ] **Step 5: Commit.**

```bash
git add GuidelineValidation/Applicability.lean GuidelineValidation.lean GVTests/Applicability.lean GVTests/Main.lean
git commit -m "Applicability: fact vocabulary, condition compiler, patient valuations

<trailer>"
```

### Task B3: Assessing conflicts per patient, with the answer key

**Files:**
- Modify: `GuidelineValidation/Applicability.lean` (append before `end GuidelineValidation`)
- Modify: `GVTests/Applicability.lean` (add `applicabilityAssessCases : IO (List Case)`)
- Modify: `GVTests/Main.lean` (group `("Applicability: answer key", applicabilityAssessCases)`)

**Interfaces:**
- Consumes: Task B2; `Conflict`, `detectConflicts`, `loadTables`, `loadJsonFile`, `ofExcept`, `parseGuidelines`, `decodeAxioms` (`Conflicts.lean`, `Guideline.lean`).
- Produces:
  - `def Vocabulary.lookup (v : Vocabulary) (key : String) : Option Formula`
  - `def conflictCondition (v : Vocabulary) (c : Conflict) : Except (List String) Formula`
  - `structure Assessment { conflict : Conflict, formula : Formula, k3 : K3Status, exact : ExactStatus }`, `def Assessment.disagree : Assessment → Bool`
  - `def relevantConstraints (cs : List (List Atom)) (f : Formula) : List (List Atom)`
  - `def assess (v : Vocabulary) (p : Patient) (c : Conflict) (f : Formula) : Except String Assessment`
  - `structure ApplicabilityRun { perPatient : Array (Patient × Array Assessment), undefined : List String, skipped : Nat }`
  - `def assessAll (v : Vocabulary) (pats : Array Patient) (conflicts : Array Conflict) : Except String ApplicabilityRun`

- [ ] **Step 1: Write the failing tests.** Append to `GVTests/Applicability.lean`:

```lean
private def canonRepo : IO System.FilePath := do
  return (← IO.getEnv "GV_CANONICAL_REPO").getD "../../Julia/guideline-validation"

def gKey := "CKD G3-G5 (universal in this stage range)"
def kKey := "hyperkalemia on renin-angiotensin system inhibitor therapy"
def pKey := "hyperphosphatemia"

/-- The answer key, worked out by hand from the draft definitions in
`data/applicability/conditions.json` before the code ran. `r18` marks the
only conditional rec (`moderate_hypertriglyceridemia`). -/
def expectedStatus (pid : String) (r18 : Bool) (key : String) : Option (K3Status × ExactStatus) :=
  let d := (K3Status.definite, ExactStatus.always)
  let a := (K3Status.absent, ExactStatus.never)
  let s := (K3Status.possible, ExactStatus.sometimes)
  match pid, r18 with
  | "P1", _ => some d
  | "P2", _ => some a
  | "P3", _ => some s
  | "P4", _ => some (if key == gKey then d else s)
  | "P5", _ => some (if key == pKey then a else s)
  | "P6", true => some a
  | "P6", false => some (if key == gKey then a else d)
  | "P7", _ => some (if key == kKey then s else a)
  | _, _ => none

def realInputs : IO (Vocabulary × Array Patient × Array Conflict) := do
  let t ← loadTables "data/conflicts"
  let canon ← canonRepo
  let recsPath := canon / "data/derived/blumenthal-2026_extracted.json"
  let (recs, _) ← ofExcept recsPath (parseGuidelines (← IO.FS.readFile recsPath))
  let axioms ← ofExcept "axioms" (decodeAxioms (← loadJsonFile (canon / "data/derived/dietary_domain_axioms.json")))
  let run := detectConflicts .paper false .quarantine t recs axioms
  let v ← ofExcept "vocabulary" (parseVocabulary (← IO.FS.readFile "data/applicability/facts.json")
    (← IO.FS.readFile "data/applicability/conditions.json"))
  let pats ← ofExcept "patients" (parsePatients v.facts (← IO.FS.readFile "data/applicability/patients.json"))
  return (v, pats, run.conflicts)

def applicabilityAssessCases : IO (List Case) := do
  let (v, pats, conflicts) ← realInputs
  let ar ← ofExcept "assessAll" (assessAll v pats conflicts)
  let all := ar.perPatient.toList.flatMap fun (p, as) => as.toList.map (p.id, ·)
  let wrong := all.filter fun (pid, a) =>
    expectedStatus pid (a.conflict.guideline.id == "R18") a.conflict.restriction.appliesWhen
      != some (a.k3, a.exact)
  let count (k : K3Status) := (all.filter (·.2.k3 == k)).length
  -- Contradiction through an enumerated fact: two stages at once.
  let bad := "{\"conditions\":[{\"key\":\"" ++ pKey ++ "\",\"status\":\"draft\",\"definition\":{\"and\":[" ++
    "{\"in\":{\"fact\":\"ckd_status\",\"values\":[\"G1\"]}},{\"in\":{\"fact\":\"ckd_status\",\"values\":[\"G4\"]}}]}}," ++
    "{\"key\":\"" ++ gKey ++ "\",\"status\":\"draft\",\"definition\":{\"fact\":\"hyperkalemia\"}}," ++
    "{\"key\":\"" ++ kKey ++ "\",\"status\":\"draft\",\"definition\":{\"fact\":\"hyperkalemia\"}}," ++
    "{\"key\":\"moderate_hypertriglyceridemia\",\"status\":\"draft\",\"definition\":{\"fact\":\"hyperkalemia\"}}]}"
  let vBad ← ofExcept "bad vocabulary" (parseVocabulary (← IO.FS.readFile "data/applicability/facts.json") bad)
  let p3 := pats.filter (·.id == "P3")
  let arBad ← ofExcept "assessAll bad" (assessAll vBad p3 conflicts)
  let badRows := arBad.perPatient.toList.flatMap fun (_, as) => as.toList
  let pRows := badRows.filter (·.conflict.restriction.appliesWhen == pKey)
  -- Undefined condition: drop the phosphate definition.
  let noP := { v with conditions := v.conditions.filter (·.key != pKey) }
  let arNoP ← ofExcept "assessAll noP" (assessAll noP pats conflicts)
  return [
    { name := s!"7 patients × {conflicts.size} conflicts assessed (expect 7 × 20)"
      ok := conflicts.size == 20 && all.length == 140 }
  , { name := s!"every assessment matches the hand answer key ({wrong.length} wrong)", ok := wrong.isEmpty }
  , { name := s!"totals: definite {count .definite}/36, possible {count .possible}/64, absent {count .absent}/40"
      ok := count .definite == 36 && count .possible == 64 && count .absent == 40 }
  , { name := "no disagreements on the real definitions", ok := all.all (!·.2.disagree) }
  , { name := "contradiction via ckd_status (G1 ∧ G4): possible, exact never, flagged"
      ok := !pRows.isEmpty && pRows.all fun a => a.k3 == .possible && a.exact == .never && a.disagree }
  , { name := "undefined condition is listed and its conflicts skipped, not assessed"
      ok := arNoP.undefined == [pKey] && arNoP.skipped == 4
              && arNoP.perPatient.all fun (_, as) => as.size == 16 } ]
```

  In `GVTests/Main.lean` append `, ("Applicability: answer key", applicabilityAssessCases)` to `groups`.

- [ ] **Step 2: Run to confirm failure.** `~/.elan/bin/lake build GVTests 2>&1 | grep -m3 error` → unknown `assessAll`.

- [ ] **Step 3: Implement.** Append to `GuidelineValidation/Applicability.lean`, before `end GuidelineValidation`:

```lean
def Vocabulary.lookup (v : Vocabulary) (key : String) : Option Formula :=
  (v.conditions.find? (·.key == key)).map (·.formula)

/-- The condition under which a conflict applies: the rec's `conditional`
(absent means the rec applies to everyone) and the restriction's
`applies_when`. `.error` lists each string with no definition. -/
def conflictCondition (v : Vocabulary) (c : Conflict) : Except (List String) Formula :=
  let recC := c.guideline.formula.conditional.map fun k => (k, v.lookup k)
  let resC := (c.restriction.appliesWhen, v.lookup c.restriction.appliesWhen)
  let missing := (recC.toList ++ [resC]).filterMap fun (k, f) => if f.isNone then some k else none
  match recC, resC.2 with
  | none, some r => .ok r
  | some (_, some rc), some r => .ok (.and rc r)
  | _, _ => .error missing

structure Assessment where
  conflict : Conflict
  formula : Formula
  k3 : K3Status
  exact : ExactStatus

/-- K3 says `possible` while every admissible completion agrees. By
`definite_sound` and `absent_sound` no other disagreement can occur. -/
def Assessment.disagree (a : Assessment) : Bool :=
  a.k3 == .possible && (a.exact == .always || a.exact == .never)

/-- The constraint groups that mention an atom of `f`. Fixtures can't
break a constraint (`knownAtoms`), so dropping the others loses nothing
and keeps the enumeration small. -/
def relevantConstraints (cs : List (List Atom)) (f : Formula) : List (List Atom) :=
  let as := atomList f
  cs.filter fun g => g.any as.contains

def assess (v : Vocabulary) (p : Patient) (c : Conflict) (f : Formula) : Except String Assessment := do
  let val := partialValuation p.known
  let k3 ← k3Status f val
  match ← exactStatus f val (relevantConstraints (factConstraints v.facts) f) with
  | .noAdmissibleCompletion => throw s!"patient {p.id}: known facts admit no completion"
  | exact => return { conflict := c, formula := f, k3, exact }

structure ApplicabilityRun where
  perPatient : Array (Patient × Array Assessment)
  /-- Distinct condition strings with no definition, in first-seen order. -/
  undefined : List String
  /-- Conflicts left unassessed because a condition is undefined. -/
  skipped : Nat

def assessAll (v : Vocabulary) (pats : Array Patient) (conflicts : Array Conflict) :
    Except String ApplicabilityRun := do
  let mut defined : Array (Conflict × Formula) := #[]
  let mut undefined : List String := []
  let mut skipped := 0
  for c in conflicts do
    match conflictCondition v c with
    | .ok f => defined := defined.push (c, f)
    | .error ms =>
      skipped := skipped + 1
      for m in ms do
        unless undefined.contains m do undefined := undefined ++ [m]
  let perPatient ← pats.mapM fun p => do
    return (p, ← defined.mapM fun (c, f) => assess v p c f)
  return { perPatient, undefined, skipped }
```

- [ ] **Step 4: Run tests.** `~/.elan/bin/lake build && ~/.elan/bin/lake test 2>&1 | grep -E "Applicability|answer key|totals|failure"` → all ✓, `0 failure(s)`. If the answer key disagrees, **do not edit `expectedStatus` to match the code**: rework the case by hand from `conditions.json` first, and report any case where the hand result was wrong.

- [ ] **Step 5: Commit.**

```bash
git add GuidelineValidation/Applicability.lean GVTests/Applicability.lean GVTests/Main.lean
git commit -m "Applicability: assess each conflict per patient (K3 and exact), with a hand answer key

<trailer>"
```

### Task B4: The `applicability` subcommand and its output

**Files:**
- Modify: `GuidelineValidation/Cli.lean` (`Options`, `Command`, `usage`, `parseFlags`, `parseArgs`)
- Modify: `GuidelineValidation/Applicability.lean` (append `k3Label`, `exactLabel`, `assessmentJson`, `ApplicabilityInputs`, `runApplicability`)
- Modify: `ValidateGuidelines.lean` (new `main` branch)
- Modify: `GVTests/Applicability.lean` (add `applicabilityCliCases : IO (List Case)`), `GVTests/Main.lean` (group)
- Modify: `CLAUDE.md`, `README.md` (one line each)

**Interfaces:**
- Consumes: Tasks B2–B3; `Options`, `modeLabel`, `detectConflicts`, `DecodeError`, `provenanceJson`, `packageRoot`, `loadTables`.
- Produces: `Options.patients : Option String`; `Command.applicability (recs axioms : String) (o : Options)`;
  `def runApplicability (o : Options) (recsContents axiomsContents factsContents conditionsContents patientsContents : String) (t : ConflictTables) (prov : Json) : String × UInt32`.

- [ ] **Step 1: Write the failing tests.** Append to `GVTests/Applicability.lean`:

```lean
def applicabilityCliCases : IO (List Case) := do
  let t ← loadTables "data/conflicts"
  let canon ← canonRepo
  let rc ← IO.FS.readFile (canon / "data/derived/blumenthal-2026_extracted.json")
  let ac ← IO.FS.readFile (canon / "data/derived/dietary_domain_axioms.json")
  let fc ← IO.FS.readFile "data/applicability/facts.json"
  let cc ← IO.FS.readFile "data/applicability/conditions.json"
  let pc ← IO.FS.readFile "data/applicability/patients.json"
  let prov := Json.mkObj [("test", Json.bool true)]
  let (txt, code) := runApplicability {} rc ac fc cc pc t prov
  let (js, jcode) := runApplicability { json := true } rc ac fc cc pc t prov
  let (badOut, badCode) := runApplicability {} rc ac fc cc "{\"patients\":[{\"id\":\"PX\",\"description\":\"d\",\"facts\":{\"ckd_status\":\"G3\"}}]}" t prov
  let summary := (Json.parse js >>= (·.getObjValAs? Json "summary")).toOption
  let defs := (Json.parse js >>= (·.getObjValAs? Json "definitions")).toOption
  return [
    { name := "parse: applicability with --patients"
      ok := match parseArgs ["applicability", "r.json", "a.json", "--patients", "p.json"] with
            | .ok (.applicability "r.json" "a.json" o) => o.patients == some "p.json"
            | _ => false }
  , { name := "parse: applicability without --patients defaults to none"
      ok := match parseArgs ["applicability", "r.json", "a.json"] with
            | .ok (.applicability _ _ o) => o.patients.isNone
            | _ => false }
  , { name := "text: exit 0, DRAFT banner, totals line", ok := code == 0 &&
        (txt.splitOn "DRAFT, not for paper use").length > 1 &&
        (txt.splitOn "Totals: definite 36, possible 64, absent 40, disagreements 0").length > 1 }
  , { name := "json: exit 0, summary counts"
      ok := jcode == 0 && summary.any fun s =>
        s.getObjValAs? Nat "definite" == .ok 36 && s.getObjValAs? Nat "possible" == .ok 64 &&
        s.getObjValAs? Nat "absent" == .ok 40 && s.getObjValAs? Nat "disagreements" == .ok 0 }
  , { name := "json: definitions all draft, for_paper_use false"
      ok := defs.any fun d => d.getObjValAs? Nat "draft" == .ok 4 && d.getObjValAs? Bool "for_paper_use" == .ok false }
  , { name := "bad patient file: exit 1, error names the patient"
      ok := badCode == 1 && (badOut.splitOn "patient PX").length > 1 } ]
```

  In `GVTests/Main.lean` append `, ("Applicability: CLI", applicabilityCliCases)` to `groups`. The existing `("Paper mode", paperModeCases)` golden checks must keep passing unchanged: that is the parity check for `conflicts`.

- [ ] **Step 2: Run to confirm failure.** `~/.elan/bin/lake build GVTests 2>&1 | grep -m3 error` → unknown `runApplicability` / `Command.applicability`.

- [ ] **Step 3: Implement the CLI.** In `GuidelineValidation/Cli.lean`:
  - `structure Options`: add field `patients : Option String := none`.
  - `inductive Command`: add `| applicability (recs axioms : String) (o : Options)`.
  - `usage`: append
    `++ "\n       validate-guidelines applicability <recs.json> <axioms.json> [--patients <patients.json>] [--mode paper|canonical] [--agent-aware] [--temporal=...] [--json] [--strict]"`
  - `parseFlags`: before the final catch-all case add
    `| "--patients" :: f :: t, pos, o => parseFlags t pos { o with patients := some f }`
  - `parseArgs`: before `| _ => .error usage` add

```lean
  | "applicability" :: rest => do
    let (pos, o) ← parseFlags rest #[] {}
    match pos.toList with
    | [r, a] => pure (.applicability r a o)
    | _ => throw usage
```

  Append to `GuidelineValidation/Applicability.lean`, before `end GuidelineValidation`:

```lean
def k3Label : K3Status → String
  | .definite => "definite" | .possible => "possible" | .absent => "absent"

def exactLabel : ExactStatus → String
  | .always => "always" | .sometimes => "sometimes" | .never => "never"
  | .noAdmissibleCompletion => "no admissible completion"

def assessmentJson (a : Assessment) : Json :=
  Json.mkObj [
    ("rec_id", Json.str a.conflict.guideline.id), ("axiom_id", Json.str a.conflict.ax.id),
    ("kdigo_source", Json.str a.conflict.restriction.source),
    ("condition", Json.str (toString a.formula)),
    ("k3", Json.str (k3Label a.k3)), ("exact", Json.str (exactLabel a.exact)),
    ("disagree", Json.bool a.disagree)]

structure ApplicabilityInputs where
  errs : Array DecodeError
  vocab : Vocabulary
  conflicts : Nat
  run : ApplicabilityRun

/-- `conflicts` (unchanged), then each conflict assessed for each patient.
While any definition is a draft, the output says it is not for paper use. -/
def runApplicability (o : Options) (recsContents axiomsContents factsContents conditionsContents
    patientsContents : String) (t : ConflictTables) (prov : Json) : String × UInt32 :=
  let parsed : Except String ApplicabilityInputs := do
    let (gs, errs) ← (parseGuidelines recsContents).mapError ("recs: " ++ ·)
    let axioms ← (Json.parse axiomsContents >>= decodeAxioms).mapError ("axioms: " ++ ·)
    let vocab ← (parseVocabulary factsContents conditionsContents).mapError ("vocabulary: " ++ ·)
    let pats ← (parsePatients vocab.facts patientsContents).mapError ("patients: " ++ ·)
    let cr := detectConflicts o.mode o.agentAware o.temporal t gs axioms
    let run ← assessAll vocab pats cr.conflicts
    return { errs, vocab, conflicts := cr.conflicts.size, run }
  match parsed with
  | .error e => (s!"error: {e}", 1)
  | .ok i =>
    let code : UInt32 := if o.strict && !i.errs.isEmpty then 2 else 0
    let drafts := (i.vocab.conditions.filter (·.status == .draft)).length
    let approved := i.vocab.conditions.length - drafts
    let all := i.run.perPatient.toList.flatMap fun (_, as) => as.toList
    let count (k : K3Status) := (all.filter (·.k3 == k)).length
    let disagreements := (all.filter (·.disagree)).length
    if o.json then
      let j := Json.mkObj [
        ("provenance", prov), ("mode", Json.str (modeLabel o.mode)), ("agent_aware", Json.bool o.agentAware),
        ("temporal_policy", Json.str (if o.temporal == .abstract then "abstract" else "quarantine")),
        ("definitions", Json.mkObj [("total", toJson i.vocab.conditions.length),
          ("draft", toJson drafts), ("approved", toJson approved),
          ("for_paper_use", Json.bool (drafts == 0))]),
        ("patients", Json.arr (i.run.perPatient.map fun (p, as) => Json.mkObj [
          ("id", Json.str p.id), ("description", Json.str p.description),
          ("assessments", Json.arr (as.map assessmentJson))])),
        ("undefined_conditions", Json.arr (i.run.undefined.toArray.map Json.str)),
        ("skipped_conflicts", toJson i.run.skipped),
        ("summary", Json.mkObj [("conflicts", toJson i.conflicts),
          ("definite", toJson (count .definite)), ("possible", toJson (count .possible)),
          ("absent", toJson (count .absent)), ("disagreements", toJson disagreements)])]
      (j.pretty, code)
    else
      let line (a : Assessment) : String :=
        s!"    {a.conflict.guideline.id} × {a.conflict.ax.id} × {a.conflict.restriction.source}: " ++
          s!"{k3Label a.k3} (exact: {exactLabel a.exact}){if a.disagree then " [K3 over-warns]" else ""}"
      let lines :=
        [s!"Applicability under missing data (strong Kleene, with an exact check)",
         s!"Definitions: {i.vocab.conditions.length} ({drafts} draft, {approved} approved)" ++
           (if drafts > 0 then ": DRAFT, not for paper use" else ""),
         s!"Mode: {modeLabel o.mode}{if o.agentAware then ", agent-aware" else ""}, conflicts: {i.conflicts}"]
        ++ (i.run.perPatient.toList.flatMap fun (p, as) =>
              s!"  {p.id}: {p.description}" :: as.toList.map line)
        ++ [s!"Totals: definite {count .definite}, possible {count .possible}, absent {count .absent}, disagreements {disagreements}",
            s!"Undefined conditions: {if i.run.undefined.isEmpty then "none" else ", ".intercalate i.run.undefined} ({i.run.skipped} conflicts skipped)",
            s!"Provenance: {prov.compress}"]
      ("\n".intercalate lines, code)
```

  In `ValidateGuidelines.lean`, add a branch to `main`'s `match` (after `.conflicts`):

```lean
  | .ok (.applicability recs axioms o) =>
    let root ← packageRoot
    let dir := root / "data" / "applicability"
    let patients := o.patients.getD (dir / "patients.json").toString
    match ← readFile? recs, ← readFile? axioms, ← readFile? (dir / "facts.json").toString,
        ← readFile? (dir / "conditions.json").toString, ← readFile? patients with
    | .ok rc, .ok ac, .ok fc, .ok cc, .ok pc =>
      let tables ← loadTables (root / "data" / "conflicts")
      let (out, code) := runApplicability o rc ac fc cc pc tables (← provenanceJson)
      if code == 1 then IO.eprintln out else IO.println out
      return code
    | .error e, _, _, _, _ | _, .error e, _, _, _ | _, _, .error e, _, _
    | _, _, _, .error e, _ | _, _, _, _, .error e =>
      IO.eprintln e; return 1
```

- [ ] **Step 4: Run tests.** `~/.elan/bin/lake build && ~/.elan/bin/lake test 2>&1 | grep -E "Paper mode|conflicts match golden|Applicability|failure"` → golden lines ✓, all Applicability ✓, `0 failure(s)`.

- [ ] **Step 5: Run it for real.**

```bash
C=~/Projects/Logic/Julia/guideline-validation/data/derived
~/.elan/bin/lake exe validate-guidelines applicability $C/blumenthal-2026_extracted.json $C/dietary_domain_axioms.json | grep -E "Definitions|Totals|Undefined"
```

  Expected:
  ```
  Definitions: 4 (4 draft, 0 approved): DRAFT, not for paper use
  Totals: definite 36, possible 64, absent 40, disagreements 0
  Undefined conditions: none (0 conflicts skipped)
  ```

- [ ] **Step 6: Docs.** `CLAUDE.md`: add the line `- Phase 2 (applicability under missing data): spec in gamen-lean docs/superpowers/specs/2026-09-30-gv-phase2-missing-data-design.md; data in data/applicability/ (definitions are drafts until Brian approves them).` `README.md`: add the `applicability` usage line.

- [ ] **Step 7: Commit.**

```bash
git add GuidelineValidation/Cli.lean GuidelineValidation/Applicability.lean ValidateGuidelines.lean GVTests/Applicability.lean GVTests/Main.lean CLAUDE.md README.md
git commit -m "validate-guidelines applicability: per-patient conflict status, draft banner

<trailer>"
```

### Task B5: Planted bugs, review, merge

- [ ] **Step 1: Plant bug 1.** In `compileCond`, change `foldConn .and "and"` to `foldConn .or "and"`. `~/.elan/bin/lake test 2>&1 | grep -E "✗" | head -5` → the answer key fails. Revert (`git checkout GuidelineValidation/Applicability.lean`).
- [ ] **Step 2: Plant bug 2.** In `partialValuation`, change `.getD .u` to `.getD .f`. Run tests → answer key and totals fail. Revert.
- [ ] **Step 3:** `~/.elan/bin/lake test 2>&1 | tail -1` → `0 failure(s)`; `git status` clean.
- [ ] **Step 4:** Dispatch a reviewer (Fable) on branch `phase2-applicability` with the spec. Ask for: definitions faithful to their quoted sources; the answer key's hand derivation; any path by which an undefined condition or bad fixture yields a verdict; `conflicts` parity.
- [ ] **Step 5:** Fix findings; rerun tests.
- [ ] **Step 6:** Ask Brian to approve the merge. On approval: `git switch main && git merge --no-ff phase2-applicability`.
- [ ] **Step 7:** Update `plans/session-handoff-2026-09-30.md`'s Guideline-validation row in gamen-lean: Phase 2 merged; the 4 definitions await Brian's approval (list the three source-vs-paraphrase differences: R18 and Rec 3.3.1.1 add "adults"; Figure 32 is scoped to CKD; Rec 4.1.8 adds CKD G3a–G5D). Commit.
