# DclegProofs: machine-checking the DCLEG thesis

For Jeremiah. This directory holds Lean 4 versions of the definitions in
Chapter 3 of your thesis and of the four results it proves (Lemma 4.1,
Theorem 4.2, Theorem 5.1, Lemma 5.2), with as much of each proof as could
be carried through so far. Each file is written to be read on its own, top
to bottom, by someone who knows DCLEG and has never used Lean. This README
says what the exercise is, how to look at the files, and where things
stand.

## What a proof assistant checks, and what it doesn't

Lean is a programming language whose type checker is also a proof checker.
You write a *definition* (a game model, satisfaction, BI_z) in a formal
language; you write a *statement* (a `theorem`); and you write a *proof*,
which is a sequence of steps that Lean checks mechanically. If the file
compiles, the proof is correct relative to the definitions: every step is
an instance of a rule, nothing is skipped, nothing is "clearly." Lean does
not find proofs for you (mostly), and it does not know what DCLEG is.

So a checked proof settles exactly one thing: *these definitions imply this
statement*. Two things it does not settle:

1. **Whether the definitions are the thesis's.** If `sat` in
   `Semantics.lean` reads a clause differently from p. 21, a proof about it
   says nothing about the thesis. This is why the definitions need your
   sign-off before the proofs mean anything, and why every place where the
   Lean had to make a choice is marked `QUESTION FOR JEREMIAH`.
2. **Whether the statement is the one you meant.** Same point, for the
   theorems. Each file quotes the statement briefly and gives a line-by-line
   reading of the Lean version.

What it *does* give you: when a hand proof says "by the inductive
hypothesis" or "by perfect information," the formal version has to say
which hypothesis, and which condition on the model, and for which world.
Where those turned out to be missing, or the hand proof's justification
was not the one that works, that is recorded under "What the formalization
found" in each file. Those sections are the main product.

## How to open a file and read the infoview

Install [VS Code](https://code.visualstudio.com/) and its "Lean 4"
extension. Open the folder `gamen-lean` (the repository root, not this
subdirectory). Open `DclegProofs/Semantics.lean`.

The extension starts Lean on the file and shows, in a side panel called the
**infoview**, the state of whatever your cursor is on:

* On a definition, nothing much: the definition just is.
* On a line inside a proof (`by …`), the infoview shows the **goal**: the
  hypotheses in scope (named, with their types) above a line, and the
  statement still to be proved below it. Move the cursor down one line and
  watch the goal change. That is what each tactic (`intro`, `cases`, …)
  does, and each is explained the first time it is used.
* On a `#print axioms name` line (you can add one anywhere), the infoview
  lists the axioms `name` depends on. See "What 'proved' means."
* Red underlines are errors; the infoview shows the message. A file with no
  red underlines is fully checked.

Prose in `/-! … -/` blocks is documentation; `/-- … -/` is a doc comment
attached to the next definition (hover over the name anywhere to see it);
`-- …` is a line comment.

## How to build

From the repository root:

```sh
lake build DclegProofs     # check every file in this directory
lake build                 # the whole repository (includes DclegProofs)
lake test                  # all tests, including the axiom audit below
```

`lake build DclegProofs` is the one to use while reading; it takes a few
seconds and reports any error with a file and line. This directory imports
nothing from the rest of `gamen-lean` and nothing from Mathlib: only Lean's
own core library.

## The process

For each result:

1. **Formalize the definitions** it needs (`Semantics.lean` for Chapter 3;
   each result file for its own formulas, e.g. `BI z` in `Lemma4_1.lean`).
2. **Get your sign-off** on those definitions, side by side with the
   thesis. Until then the proofs are provisional.
3. **State the result** as a Lean proposition, with a reading guide.
4. **Prove it**, step by step, following the hand proof where one exists,
   with a comment mapping each Lean step to the thesis's step.
5. **Compare with the hand proof**: what the formal proof needed that the
   hand proof does not say, what the hand proof says that turned out to be
   unnecessary, and any step that could not be justified.

Steps 1 and 3 are complete for all four results. Step 4 is complete only
for base cases and sub-lemmas; see the table. Step 5 is written up in each
file's closing section whether or not step 4 finished, because reading
the hand proof against the definitions is where the findings came from.

## What "proved" means here

A `theorem` in these files is proved if the file compiles, with two
qualifications that the test suite enforces:

* **The kernel checked it.** Lean's proof checker is a small program (the
  kernel) that re-verifies every proof term. Tactics are just ways of
  producing terms for it. Nothing in these files is trusted because a
  tactic said so.
* **Only the three standard axioms are used.** `#print axioms name` lists
  what a theorem ultimately rests on. Lean's classical mathematics uses
  `propext` (equivalent propositions are equal), `Quot.sound` (quotients),
  and `Classical.choice` (excluded middle, in effect). Anything else, in
  particular `sorryAx` (a hole left in a proof) or the axiom that
  `native_decide` introduces (trust in the compiler, not the kernel), would
  mean the theorem is not proved in the sense above. The file
  `Tests/DclegProofs.lean` lists every theorem here and fails the build if
  any depends on anything outside that allowlist.

A `def claim_… : Prop` is a **statement without a proof**. It is there so
the exact formal statement is on record and can be checked against the
thesis; it asserts nothing.

## How to review a definition

Take `Semantics.lean` and the thesis open together.

* Each definition's comment names the section, condition number and
  printed page it renders. Check the Lean against that passage, not
  against memory.
* Read `QUESTION FOR JEREMIAH` lines first (there are eighteen, Q1–Q18,
  across the files; `grep -n "QUESTION FOR JEREMIAH" DclegProofs/*.lean`
  lists them). Each is a choice the Lean made where the thesis's wording
  admits more than one reading, or where something had to be added or
  restricted for the definition to make sense. Answer them, in the margin
  or in an issue; a "yes, as written" is as useful as a correction.
* For a `structure` (e.g. `GameModel`), the fields ending in a `Prop` are
  the conditions imposed. Check that the list is the thesis's list, no more
  and no less, and that each says what its number says.
* For `sat`, check clause by clause against the table on p. 21.
* Notation: `¬' φ`, `φ ∨' ψ`, `φ ∧' ψ`, `φ □→ ψ`, `□ φ`, `◇ φ` are the
  object language (primes keep them apart from Lean's own connectives);
  `.next φ`, `.prev φ`, `.bel i φ` are X, Y, Bᵢ.

The order to read the files: `Semantics.lean`, `Basics.lean` (facts about
the semantics the proofs use, most of them things Chapter 3 says in prose),
then `Lemma4_1.lean`, `Theorem4_2.lean`, `Theorem5_1.lean`, `Lemma5_2.lean`.

## Status

| Result | Status | File | Proved so far |
|---|---|---|---|
| Chapter 3 definitions (syntax, strategic structures, histories, game models, satisfaction, validity) | formalized, awaiting sign-off | `Semantics.lean` | (definitions) |
| Chapter 3 prose claims: `end` marks outcome nodes (p. 21), □ is world-independent (p. 23), centering makes a true antecedent's world the only maximally consistent one (p. 19), Bᵢ is D/4/5/C4 (p. 22), Bᵢ–□ interactions (p. 23), `Move` is a function, ◇φ yields a maximally φ-consistent world (p. 22, under Q12), cautious monotonicity | **proved** | `Basics.lean` | all of the above |
| Validity of φ □→ ψ is equivalent to validity of φ → ψ | **proved** | `Basics.lean` | `valid_cf_iff` |
| Q12: a concrete game model (five nodes, three worlds) on which ◇m′ holds but no world is maximally m′-consistent, under the literal reading of p. 19 | **proved** | `Q12Example.lean` | `exM` checked against every `GameModel` condition; `dia_move'`, `no_maxConsistent`, `cf_bot`, `not_local` |
| Lemma 4.1 | partly | `Lemma4_1.lean` | base case z = 0 (`lemma4_1_zero`); definitions of BI_z, depth, BI paths |
| Theorem 4.2 | partly | `Theorem4_2.lean` | base case z = 0 (`theorem4_2_zero`); Ratᵢ ↔ BᵢRatᵢ on i's turn; B^E B^E ψ → B^E ψ |
| Theorem 5.1 | open | `Theorem5_1.lean` | definitions; the step "Bᵢ AX φ gives X Bᵢ φ at plausible worlds" for the actual move (`bel_next_of_bel_AX`) |
| Lemma 5.2 (no written proof in the thesis; p. 43 says "similar to" Theorem 5.1's) | partly | `Lemma5_2.lean` | the Bᵢ conjunct of CondRat's (m, k) disjunct, for the actual move m only, taking Bᵢ(m □→ ⋁_{h≥k} hᵢ) as a hypothesis; the ⋀_{m′} conjunct is not proved (`lemma5_2_actual_move`) |

"Open" means the formalization found a step of the hand proof it could not
justify from the definitions; the file says which. "Partly" means part of
the result is proved and the rest is unfinished for reasons of effort or
of a missing lemma, again spelled out in the file.

Findings that concern the thesis itself, in one line each (details in the
files; `FINDINGS.md` classifies each one and says which depend on the open
questions):

* Centering as printed (p. 19) is unsatisfiable at pairs (γ,w) with
  w ∉ V_γ; the Lean restricts it to reached pairs (Q7).
* Maximal φ-consistency's clause 2(b) quantifies ⟦φ⟧ over all nodes, which
  makes the p. 22 claim ("◇m′ gives a maximally m′-consistent world") false
  unless premises are node-local (Q12); `Q12Example.lean` is a
  machine-checked model where it fails. Theorem 4.2's proof uses that claim.
* Lemma 4.1's two directions each use the other at the successor node
  (the step from (4.7) to "guarantees at least k_BI" needs BI path ⇒
  satisfaction at w′), so they need one joint induction on depth, with a
  lemma "BI_z holds only at depth z" (`Lemma4_1.lean`, item 1).
* Theorem 4.2's "R^z = B^E ψ regardless of z" fails at z = 0; the z = 0
  case needs Present Seriality and A ≠ ∅ instead of C4. Its "by perfect
  information" step needs "R^z holds only at depth z", whose proof in turn
  depends on Q12 (`Theorem4_2.lean`, items 1–2).
* Theorem 5.1 and Lemma 5.2: the step "Bᵢ AX FutRat gives m □→ X Bᵢ FutRat
  at μ" is justified for the actual move (using Self-Awareness,
  Expectational Continuity, Transitivity, Euclideanness, none cited) but
  not established for other moves, and the case ¬◇(m ∧ Ratᵢ) is dropped
  (which p. 41's closing remark partly anticipates). These are gaps in the
  proofs, not counterexamples to the results (`Theorem5_1.lean`, items 1–2).
  Lemma 5.2 has no written proof in the thesis.
* Three typos in the proof of Theorem 4.2: a missing X in the sentence
  before (4.18), m for m′ in (4.12), and "PMoves(w) \ w" for
  PMoves(w) \ {m} on p. 33.
* The closing "vacuous or by contemporary universality" paragraph of each
  validity proof is unnecessary: φ □→ ψ is valid iff φ → ψ is
  (`valid_cf_iff`).
