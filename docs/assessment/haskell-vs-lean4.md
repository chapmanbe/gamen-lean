# Haskell vs. Lean 4 for gamen: which is easier to pick up?

Date: 2026-09-23. Written by Claude (Opus 5.5) for Brian and Jeremiah Chapman.
Companion to `feasibility-assessment.md`. Part 4 of that file has the data
from the Lean 4 slice test cited below.

## Short answer

For a complete novice writing gamen-style code, **Haskell is slightly easier
to start** and **Lean 4 is slightly easier to keep going**. The gap is smaller
than people expect, because gamen uses only the plain functional core the two
languages share: closed sum types, pattern matching, structural equality,
persistent sets and maps, pure recursion.

For the two of you specifically, **Lean is the easier next step**. It
means learning a new syntax, not a new way of thinking.

## Where Haskell is easier

- **Learning material.** Twenty-plus years of books, courses, blog posts, and
  Stack Overflow answers. Almost any beginner question has already been asked.
- **Error messages about ordinary programs.** GHC's messages are cryptic at
  first, but they are well documented and easy to search.
- **Nothing forces advanced ideas on you.** You can write all of gamen without
  meeting a dependent type or a termination proof.

## Where Lean 4 is easier

- **Strict evaluation.** Code runs in the order you read it. Laziness is the
  most common reason Haskell novices get confused (space leaks, `seq`, why a
  program hangs, why an `error` fires late). gamen-hs needs `deepseq` in
  `validate/Main.hs` only because of laziness; the Lean port needs nothing
  like it.
- **Tooling that just works.** `elan` installs Lean, `lake` builds, and the
  VS Code infoview shows the type of anything under the cursor as you type.
  In the slice test, going from install to a green test suite took one
  command each (see Part 4). Haskell's tooling (cabal, GHC versions, HLS)
  causes more setup friction.
- **Batteries in the core.** Ordered maps and sets (`Std.TreeMap`,
  `Std.TreeSet`), hashing, JSON, and `deriving` all ship with Lean. In
  Haskell, a novice quickly runs into `String` vs. `Text`, choosing packages,
  and the list of language extensions.
- **A friendly book.** *Functional Programming in Lean* (David Thrane
  Christiansen) is free and written for programming in Lean, not for
  proving theorems.

## Where Lean 4 is harder

- **Termination checking.** Recursion over formulas is accepted
  automatically. Search loops, like the tableau expansion, need an explicit
  step counter ("fuel") or `partial def`. The slice test hit this twice, in
  the driver loop and in `toNNF`.
- **Less "how do I do X" help.** Most Lean discussion online is about proofs
  (Mathlib, AI theorem proving). Help for everyday programming questions,
  like reading stdin or string handling, is thinner.
- **Error messages that sometimes involve features you haven't learned
  yet**, such as implicit arguments, universes, and auto-parameters.
- **Monthly releases.** Occasionally something small breaks on upgrade; pin
  the version in `lean-toolchain`.

## What the slice test showed

The slice test was a port of `Formula`, `Kripke`, `Semantics`, `Verdict`,
and the system-K tableau (about 800 lines of Lean, plus 144 lines of tests;
see `sketches/lean/`).

| Observation | Novice impact |
|---|---|
| The code reads like the Haskell, constructor for constructor | Low: knowledge of ADTs and pattern matching transfers directly |
| Or-patterns (`\| .box f \| .diamond f => …`) shorten many functions | Helps: fewer repeated lines than Haskell's one-clause-per-constructor style |
| `Ord` for pairs is not on by default (`attribute [local instance] lexOrd`) | Stumbling block: the error message doesn't suggest the fix |
| Loops need visible termination (fuel, bounded search) | Stumbling block at first; later it catches real problems (it flagged a same-size recursion in the Haskell `toNNF`) |
| `error` has no pure equivalent; `panic!` continues with a default value | Design lesson: use `Except`, which is safer but changes signatures |
| Property testing (Plausible) needed `NamedBinder` when called from `IO` | Stumbling block: found only by reading library source |
| Zero doc lookups needed for core Lean or `Std` | Suggests the core library is predictable |

## Side by side

The same function in both languages, from the slice.

Haskell (`gamen-hs/src/Gamen/Semantics.hs`):

```haskell
satisfies m w (Box f) =
  all (\w' -> satisfies m w' f) (accessible (frame m) w)
satisfies _ _ (Stit _ _) =
  error "Stit operator requires a StitModel (use Gamen.Stit)"
```

Lean 4 (`sketches/lean/Gamen/Semantics.lean`):

```lean
  | .box g | .futureBox g => (acc w).toList.allM (satisfies m · g)
  | .stit .. => throw "Stit operator requires a StitModel (use Gamen.Stit)"
```

The logic is the same. The differences are syntax (`.box g` vs. `Box f`;
`·` for the lambda argument), the or-pattern, and `throw` into `Except` in
place of `error`.

## What matters for the two of you

- **Brian** is not starting from zero. He has already invested in Haskell and
  co-owns a 16k-line codebase in it. Switching means learning a second syntax
  and standard library, not a new paradigm. Knowledge of ADTs, pattern
  matching, and typeclasses carries over almost one-to-one.
- **Jeremiah** has an MS in logic. Lean is closer to his world than Haskell
  is, and it's the only candidate language that lets him go on to *prove*
  properties of the prover, such as tableau soundness. His stated goal in
  gamen-hs's CLAUDE.md is Haskell skill for PhD applications; whether Lean
  serves his target programs as well or better is worth checking against
  their listings.

## Bottom line

For a blank-slate novice it's roughly even, with a slight edge to Haskell for
the amount of help available. Given where you both are, Lean 4 is the
easier next step: new syntax, same ideas, better tooling, no laziness. The
best test is to read `sketches/lean/Gamen/Tableau.lean` next to
`gamen-hs/src/Gamen/Tableau.hs` and decide which one you would rather
maintain.
