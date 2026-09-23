# Porting gamen-hs: feasibility assessment

Date: 2026-09-23. Written by Claude (Fable 5.1) for Brian and Jeremiah Chapman.
Question: is it worth porting `gamen-hs` (~/Projects/Logic/Haskell/gamen-hs) to a
more modern functional language, and if so which one?

## Part 1 — What gamen-hs actually is, in language-feature terms

Measured, not guessed (grep over `src/ protocol/ validate/ service/`, GHC 9.8, GHC2021).

| Component | Lines | Files |
|---|---:|---:|
| `src/` core library | 8,289 | 30 |
| `protocol/` JSON codec (internal lib) | 807 | 5 |
| `validate/` gamen-validate CLI | 329 | 1 |
| `service/` dcleg service CLI | 253 | 1 |
| `test/` hspec + QuickCheck | 7,005 | 23 |
| **Total to port** | **~16,700** | **61** |

Test code is 42% of the codebase, and the 1,848-line `PaperCorrespondence.hs`
plus 761 hspec cases are the real asset: they pin the implementation to the
Lorini / Herzig / Lyon–van Berkel / Broersen papers. Any port must carry the
tests, not just the library.

### Features the code depends on, ranked by how hard they are to replace

**Tier 1 — load-bearing; a candidate language must have these or the port is
a rewrite, not a port.**

1. **One closed 30-constructor recursive sum type with compiler-enforced
   exhaustive matching.** `Formula` in `Gamen/Formula.hs`; `-Wall
   -Wincomplete-patterns` is the project's stated bug-catching strategy
   ("every function on Formula must handle all 30 constructors"). The
   `Atom` pattern synonym + `COMPLETE` pragma exists only to keep that
   check intact through a newtype. Target needs: recursive ADTs, exhaustive
   match as a compile error (or a warning the project can promote).
2. **Derived structural `Eq`/`Ord` on recursive ADTs, used as keys in
   persistent ordered `Set`/`Map`.** 48 `data` decls; `Data.Set` at 49 use
   sites, `Data.Map` at 33. Tableau branches are `Set (Sign, Formula)`
   (`branchSet`, O(log n) membership — documented in
   `notes/tableau_optimization.md`); the epistemic memo is `Map Formula
   EpistemicModel`. The order itself is arbitrary, so a *hashed* set would
   do if the language derives `Hash` — but it must be derived, not
   hand-written for a 30-constructor type.
3. **Immutable, recursive, pure style.** 0 uses of mtl/State/Reader/Except in
   the library; 0 GADTs, 0 type families, 0 RankN, 0 Template Haskell, 0
   custom Functor/Monad instances. The library is plain first-order
   functional code: guards (311), `where` (95), `let` (134), list
   comprehensions (82), `Maybe` (52), `Either` (17). This is the single most
   important finding: **the code uses almost none of the Haskell-specific
   machinery that makes Haskell hard to port.**

**Tier 2 — used, but replaceable with a known idiom.**

4. **One typeclass.** `class Eq p => Plausibility p` with three instances
   (`Gamen/Plausibility.hs`). Five methods, no superclass tricks. Trivially
   a record-of-functions (dictionary passing) in a language without
   typeclasses.
5. **Custom `Show` with `showsPrec` precedence** (9 instances) for
   pretty-printing formulas with Unicode operators. Any language: a
   `toString : Int -> Formula -> String` function.
6. **JSON codec** (aeson, 11 use sites; 14 hand-written `FromJSON`/`ToJSON`
   instances in `protocol/`). Hand-written, so no reliance on Generic
   deriving. Needs: a JSON library with a value ADT and stdin/stdout line
   IO. This is the *contract* with guideline-validation,
   guideline-cds-simulation, patient-agent-assistant, and cwyde — the wire
   format must be byte-compatible, but the implementation language is
   invisible to callers.
7. **QuickCheck property tests** (`test/Properties.hs`, 910 lines; sized
   generators over `Formula`, 39 combinator uses). Needs a property-testing
   library with sized recursive generators and shrinking.
8. **hspec-discover** test organization (23 spec files). Any test runner.
9. **`error "..."` calls: 185.** Internal invariant violations
   (`Coalition.hs` 23, `Epistemic.hs` 20, ...). Target needs a crash/panic
   or a discipline to convert these to `Result`. Not hard, but it is 185
   sites and changes signatures if done properly.

**Tier 3 — Haskell-specific, but only at the edges.**

10. **Laziness relied on once, deliberately.** `Gamen/Epistemic.hs:148-158`
    builds `Map Formula EpistemicModel` of announcement restrictions and
    relies on the strict-in-spine / lazy-in-value Map so unreached
    restrictions stay thunks (issue #18 optimization). In a strict language
    this becomes an explicit lazy memo or a `Dict Formula (Lazy Model)` —
    ~10 lines.
11. **`deepseq`/`evaluate`/`try` crash guard** in `validate/Main.hs:318-324`:
    forces the encoded response so a `error` inside the prover becomes an
    error JSON line rather than a crash. Only needed *because* of laziness
    and `error`; strict languages with `Result` get this for free, panic-
    based ones need a top-level catch.
12. **`IORef`** — 13 hits, all in `service/Main.hs` (the dcleg service's
    session state). Any language.
13. **Deriving `Show`/`Ord`** on 31/13 types respectively — see Tier 1 #2.

**Nothing in the code needs:** monad transformers, type-level programming,
lens, STM, concurrency, FFI, laziness for correctness (only for the one
memo), or Cabal-specific packaging beyond internal libraries.

### What this means

gamen-hs is, in practice, written in the "ML core" of Haskell: closed sum
types, exhaustive matching, structural equality, persistent sets/maps, pure
recursion. That subset exists in OCaml, F#, Lean 4, Gleam, Rust, Roc, and
others. So the port is *feasible in principle* into any of them, and the
decision turns on: maturity, community, tooling, the six "Tier 2" items,
and — the question Brian asked — whether I can write the target language
reliably.

### Cost of leaving Haskell that no language choice removes

- **The JOSS plan.** `~/Code/notes/publication-plan.md` targets JOSS for
  gamen-hs in Nov 2026 after a 6-month public history. A port restarts that
  clock for the new codebase unless the paper is about the Haskell version.
- **Two downstream consumers plus cwyde** call `gamen-validate` over JSON
  Lines. Wire compatibility must be regression-tested (`test/ProtocolSpec.hs`
  and `DclegServiceSpec.hs` are the fixtures to port first).
- **Jeremiah's stated goal** (CLAUDE.md goal 4) is building Haskell skill
  for PhD applications. A port does not advance that.
- **761 tests / 16.7k lines** — at a realistic 150–300 lines/day of
  carefully verified port work, this is 2–4 months of effort, most of it in
  the tests.

## Part 2 — Candidate languages

Facts below were gathered 2026-09-23 by web research against primary sources
(release notes, official docs, GitHub). Items the research could not confirm
are marked UNVERIFIED. Nothing here is from model memory except the literacy
self-assessment, which is by definition my own judgment.

### Scorecard against the Tier 1 / Tier 2 requirements

| | Roc | Gleam | Lean 4 | OCaml 5 | F# | Rust† |
|---|---|---|---|---|---|---|
| Version / maturity | no 0.1 yet; nightlies of a brand-new Zig compiler (parity reached ~Sep 2026) | 1.18.1 (Aug 2026), SemVer since 1.0 (2024) | 4.34.0 (Sep 2026), monthly releases | 5.5.0 (Jun 2026), 30 yrs | F# 10 / .NET 10 | 1.93 stable |
| Exhaustive match | **error** | **error** | **error** | warning 8 (dune default profile makes it fatal) | warning FS0025 | **error** |
| Derived structural Eq | Eq derivable | automatic `==` | `deriving BEq, DecidableEq` | polymorphic `=` | automatic | `#[derive]` |
| Derived Ord / Hash for sets | Hash derivable; **no Ord derivation found** (UNVERIFIED) | no Ord; hashed `set`/`dict` accept any type, order "not to be relied on" | `deriving Ord, Hashable` — works on recursive inductives | polymorphic `compare` | automatic structural compare | `#[derive(Ord, Hash)]` |
| Persistent ordered Set/Map | `Dict` insertion-ordered hash map | `gleam/set`, `gleam/dict` (unordered) | `Std.TreeSet/TreeMap` + `HashSet` in core | `Set.Make`/`Map.Make` | `Set`/`Map` ordered | `BTreeSet/BTreeMap` |
| Ad-hoc polymorphism (1 class needed) | abilities → **static dispatch migration in progress** (PRs merging 2026-09-22) | none by design; record-of-functions | typeclasses | functors / modular explicits (new, 5.5) | SRTP/interfaces | traits |
| JSON | `roc-json` (community, tied to Encoding/Decoding abilities) | `gleam_json` + hand decoders (matches current gamen practice) | `Lean.Json`, `deriving ToJson/FromJson`, in core | yojson | System.Text.Json | serde_json |
| Property testing | **none found** (UNVERIFIED) | `qcheck` 1.0 w/ shrinking | Plausible (+ LSpec) | qcheck | FsCheck | proptest |
| Standalone binary for subprocess callers | yes via basic-cli (macOS arm64 built in CI) | **no** — needs BEAM (escript) or Node; third-party bundlers only | yes, Lean→C→native | yes | yes (`PublishAot`) | yes |
| Community | ~6.1k stars, Zulip, no package registry | ~21.9k stars, 308 contributors, ~1.1k hex packages, ~8.4k Discord | ~8.5k stars, 858 Reservoir packages, huge but proof-centric | 6.6k stars, mature | corporate .NET | largest of all |
| Breaking changes, last 12 mo | **whole new syntax + compiler** | none (deprecations only) | 4.29 (reducibility), 4.32 (`Std.Time`, new `do` elaborator) — stdlib, not core syntax | 5.5 modular explicits | none | none |
| Laziness | strict | strict | strict (`Thunk` available) | strict (`Lazy`) | strict (`lazy`) | strict |
| Performance for symbolic work | native (Zig backend) | BEAM; no native-vs-Gleam benchmark exists | native, Perceus RC; PLDI'21 shows ≥ OCaml on allocation-heavy code | native | .NET JIT/AOT | native |

† Rust was not part of today's research; its row is from my own knowledge,
which for Rust is reliable because the language is stable. It is here for
scale, not because it is a functional language.

**Disqualified at Tier 1** (exhaustiveness is a *runtime* error, not compile
time): Unison 1.0, Koka 3.2 ("research language, not production-ready").
**Disqualified on deployment**: PureScript (JS only, native backend stale),
Flix (JVM-only, pre-1.0, no JSON or property-testing library found). Idris 2
passes Tier 1 but is a 3.1k-star community with no property-testing library
found and a Chez Scheme runtime; it offers nothing over Lean 4 for this
project.

### Per-language verdicts

**Roc — not now.** The language is in the middle of the largest change of
its life: a 487-day compiler rewrite that reached parity this month, with a
new syntax (`match`, `|x| ...`, `{ ..rec }`) and an unfinished migration from
abilities to static dispatch. There is no 0.1.0 release, no package
registry, no property-testing library, and no Ord derivation found. Every
one of those is a *today* problem, not a design problem — Roc's design
(closed tag unions, exhaustive `match` as an error, derived `Eq`/`Hash`,
`Dict`/`Set` on any key) fits gamen-hs well. The right move is a small
experiment now (Formula + NNF + one satisfaction function, ~200 lines) to
build a relationship with the language, and a real re-evaluation when 0.1.0
ships (team says "later in 2026," no date). Betting 16k lines on it today
means porting twice.

**Gleam — the maintainability pick.** Everything in Tier 1 and 2 is
available or has a clean idiom: exhaustive `case` is an error, `==` is
structural and free, hashed `set`/`dict` take `Formula` keys with no
boilerplate, the single typeclass becomes a record of five functions,
`gleam_json` decoders are hand-written exactly as the current aeson
instances are, `qcheck` has shrinking. SemVer since 2024 with zero breaking
changes in the last year, the friendliest compiler messages of the group, and
the largest *engaged* community of any candidate that is actually new. Two
real costs: (1) no ordered set — countermodel and branch enumeration order
becomes "whatever the BEAM hash order is," which is deterministic per
Erlang version but unspecified, so any output that downstream tests compare
byte-for-byte needs an explicit sort; (2) **runtime dependency** —
`gamen-validate` is called as a subprocess by three Python/Julia projects,
and a Gleam build of it needs Erlang installed on every caller's machine (or
a third-party bundler), where the Haskell binary is self-contained. Also:
no native performance, no benchmarks for symbolic work; fine for today's
small clinical models, a question mark for 16+-world models (see
`notes/haskell-landscape.md`).

**Lean 4 — the novelty pick, and the closest port.** Of all candidates, Lean
4 is the only one where the port is nearly mechanical: `inductive Formula`
with 30 constructors, `deriving BEq, Ord, Hashable, Repr`, `Std.TreeSet
(Sign × Formula)` for tableau branches, `class Plausibility` verbatim,
`deriving ToJson, FromJson` where hand-written instances are not needed,
Plausible for the 910 lines of QuickCheck, `lake build` to a native binary.
It is *more* Haskell-like than Haskell in the one place that matters here
(typeclasses + deriving + ordered persistent maps all in core). Beyond
parity, it offers something no other candidate can: the tableau soundness
and the Lyon–van Berkel saturation predicates are exactly the kind of thing
one later *proves* in Lean, and a FormalizedFormalLogic project already has
tableau soundness/completeness for K/KT/S4 as a reference (though a
sibling `ModalLogicArchive.Modal.Tableau` is reported broken under 4.33.1 —
small Lean formalizations rot fast). For Jeremiah's PhD applications, Lean
in 2026 is at least as marketable as Haskell for a logic student. Costs:
(1) the termination checker — every recursive function is checked;
structural recursion over `Formula` is free, but the tableau/prover loops
need `partial def` or explicit fuel (gamen already threads `Int` budgets
through `proveFormula`, so fuel is the natural translation); (2) monthly
releases with occasional stdlib breaks — pin the toolchain per project via
`lean-toolchain`, and expect an hour of upgrade work a few times a year;
(3) the community's center of gravity is Mathlib and AI theorem proving,
not application programming, so "how do I read stdin line-by-line" gets
fewer answers than "how do I prove this lemma"; (4) compile times and error
messages are worse than Gleam's, better than they were.

**OCaml 5 / F# — the safe, unexciting ports.** Both satisfy every tier with
polymorphic/structural compare and mature ordered `Set`/`Map`, both have
mature qcheck/FsCheck and JSON, both produce native binaries. OCaml has a
30-year track record and is the language the Haskell code already
resembles; F# adds a corporate ecosystem. Neither scores on novelty or on
"more community engagement" than Haskell; OCaml's community is smaller and
its exhaustiveness check is a warning unless dune makes it fatal. Choose
one of these only if the goal narrows to "lowest-risk migration off GHC."

**Rust — the pragmatic outsider.** Best tooling, community, and deployment
story of any language here, exhaustive `match` error, full `derive`,
`BTreeSet`, serde, proptest. The cost is ownership: tree-rewriting code
over `Box<Formula>` needs `.clone()` or `Rc` discipline, and the code stops
reading like the papers. Not a functional language; listed because it
would be irresponsible to omit the option with the most maintainers on
earth.

### My literacy, honestly

| Language | Self-assessment | Basis |
|---|---|---|
| OCaml, F#, Rust | High. Stable languages, large training corpus. | Can write without docs; would still compile-check. |
| Gleam | High. Small, stable language; syntax unchanged since 1.0. | Need to check current `gleam/dynamic/decode` API (it was reworked in 2024–25). |
| Lean 4 | Medium-high for *programming* Lean. | `Std.TreeMap`/`HashMap` moved into core in 2025 and their APIs are newer than most of my examples; `do`-notation elaborator changed in 4.32. Must verify against docs and compile every snippet. Proof-mode Lean is a different skill and not needed for the port. |
| Roc | **Low.** | My training data is dominated by the *old* syntax (`when … is`, `\x ->`, abilities). The new compiler's syntax postdates it. I would be writing entirely from the mini-tutorial and compiler errors — exactly the situation where confident-but-wrong code is most likely. |
| Unison, Koka, Idris 2, Flix | Medium-low; moot given Tier 1 disqualification. | — |

The only way to turn this table from opinion into evidence is the test in
Part 3.

### Addendum — Rust as a DSL host (added 2026-09-23, Opus 5.5)

Question raised in review: could gamen be written in a domain-specific
language hosted in Rust, inheriting Rust's maintainer base?

**Short answer: Rust hosts DSLs well, but the "most maintainers on earth"
benefit belongs to Rust, not to a DSL built on it.** Rust's tooling is shared;
the DSL's maintainers would be the two of us.

Three ways to build one:

1. **Declarative macros (`macro_rules!`)**: pattern-based syntax rewriting,
   e.g. `formula!( box (p -> diamond q) )`. Cheap and hygienic, but once the
   grammar has precedence and Unicode operators, the error messages turn opaque.
2. **Procedural macros (`syn` + `quote`)**: compile-time Rust programs that
   could turn declarative tableau rules
   (`tableau_rule! { BoxTrue: σ ⊨ □A, σ.n ∈ branch ⟹ σ.n ⊨ A }`) into matching
   code. Powerful, but they need a separate crate, slow down compiles, and
   report errors against generated code. This is the least maintainable Rust
   a newcomer can meet.
3. **External DSL**: a real grammar (`pest`, `lalrpop`, `chumsky`) read at
   runtime from `.gamen` files and interpreted in Rust. This fits the
   Buchanan separation principle best, but it means owning a language:
   grammar, error messages, docs, edge cases.

**Why this cuts against the stated goals.** Contributors would need Rust
*and* the DSL, which shrinks the potential pool. Macro-heavy Rust and a DSL
interpreter are both maintenance burdens on top of the library itself. The
one real argument for a DSL is that it could hide Rust's ownership
boilerplate (`Box`, `.clone()`, `Rc`), which otherwise keeps tree-rewriting
code from reading like B&D.

**Lean 4 already does this natively.** User-extensible syntax (`notation`,
`syntax`, `macro_rules`, custom elaborators) is built into the language; it
is how Mathlib writes its mathematics:

```lean
notation "□" φ => Formula.box φ
example : Formula := □ (p ⟶ ◇ q)
```

That needs no separate parser or macro crate, and the editor supports the
notation. If the appeal is "gamen in notation that reads like the logic,"
Lean provides it as a first-class feature, while Rust makes you build it.

**Where Rust could still fit:**

- *Performance backend*: Lean for the logic, Rust for a fast model checker
  if clinical models grow past ~16 worlds. Speculative; only after a
  benchmark shows the need.
- *Rules as data, no new language*: tableau rules and frame axioms in
  YAML/JSON, read by a plain interpreter. This gets the separation-principle
  benefit without owning a grammar, and it works equally well in Lean.

**Verdict:** Lean 4 stays the lead candidate. Rust is the fallback if Lean's
termination checker or release churn causes trouble in the slice test. A
Rust-hosted DSL is not recommended as the primary route.

## Part 3 — Recommendation

1. **Do not port to Roc now.** Re-evaluate at Roc 0.1.0. Optionally spend an
   afternoon on a 200-line Roc sketch of `Formula` + `toNNF` + `satisfies`
   to learn the language and register interest; keep it in this repo as
   `sketches/roc/`.
2. **Run a literacy-and-fit test before deciding between Gleam and Lean 4.**
   Port the same ~350-line slice to each: `Gamen.Formula` (30 constructors,
   `toNNF`, `atoms`, `Show`), `Gamen.Kripke` + `Gamen.Semantics`
   (`satisfies`), and the tableau for system K only with a dozen
   `TableauSpec` cases and one property from `Properties.hs` (NNF preserves
   satisfaction). Measure: lines, time, number of doc lookups I needed,
   number of compile-fix iterations, and whether the result reads like the
   Haskell. Same slice in Roc as the optional sketch.
3. **If the priority is "someone else can maintain it" → Gleam.** If the
   priority is "novelty and a path to verified provers, on a logic project
   run by a logician" → Lean 4. My recommendation for *this* project is
   **Lean 4**, because the port is closest to mechanical, the dependency
   footprint is core-only (matching gamen's `base + containers` rule), and
   the verification upside is unique; but I would not make that call before
   step 2, and the BEAM-runtime question for the three subprocess callers is
   Gleam's to answer before it could win.
4. **Whatever is chosen, port `protocol/` and `ProtocolSpec`/
   `DclegServiceSpec` first** and run the Python/Julia callers against the
   new binary before touching the logic modules. The wire format is the
   contract; the logic can be ported module by module behind it.
5. **Keep gamen-hs as the reference implementation** through the JOSS
   submission (Nov 2026). Cross-validate the port against it with the
   existing `gamen-validate` protocol — the same trick the project already
   uses between Gamen.jl and gamen-hs.

## Part 4 — Lean 4 slice test (run 2026-09-23, Opus 5.5)

Code: `sketches/lean/` (see its README). Toolchain: Lean 4.34.0 via elan,
Plausible v4.34.0. Run with `lake test`.

### What was ported

| Haskell source | Lean port | Scope |
|---|---|---|
| `Formula.hs` (446 lines) | `Gamen/Formula.lean` (223) | all 30 constructors, `atom` pattern, printing, `isModalFree`, `atoms`, `toNNF`/`pushNeg`, `isNNF`. Not ported: `hasAgentOperator`, `dstit`, `commitment`. |
| `Kripke.hs` (147) | `Gamen/Kripke.lean` (48) | `Frame`, `Model`, `accessible`, `mkFrame`, `mkModel`. Not ported: equivalence/independence helpers. |
| `Semantics.hs` (212) | `Gamen/Semantics.lean` (75) | `satisfies` for all 30 constructors, including Since/Until; `isTrueIn`. |
| `Verdict.hs` (68) | `Gamen/Verdict.lean` (32) | complete |
| `Tableau.hs` (1,067) | `Gamen/Tableau.lean` (426) | prefixes, branches, blocking, Tables 6.1/6.2 rules, all five expansion passes, the driver, `tableauProves`/`tableauConsistent`, countermodel extraction, and closure for every system. Not ported: the KT…S5 rule sets and the quarantined temporal rules. |
| `TableauSpec.hs` + `Properties.hs` (parts) | `Tests/Main.lean` (144) | 21 unit cases + 4 Plausible properties |

The line counts are not a like-for-like comparison, because the Haskell
files contain more features. The fair reading: for the ported functions,
the Lean code is about the same length as the Haskell. Anywhere Lean allows
or-patterns (`| .box f | .diamond f => …`) it is shorter.

### Results

- **25/25 checks pass**: every K-system case from `TableauSpec.hs`,
  countermodel extraction for □p → p, printing matching Haskell `show`, and
  four properties at 300 random formulas each (NNF idempotent, NNF output
  is in NNF, NNF preserves truth at every world of a 3-world model, and a
  soundness spot-check: formulas the tableau calls valid are true in that model).
- **The tests can fail.** Planting a bug (¬□ ↦ □¬ in `pushNeg`) made the
  truth-preservation property fail with a shrunk counterexample. Of the 300
  random formulas, 18 are valid in K, so the soundness check exercises real
  cases, though not many.
- **No logic bugs.** Every build failure was a Lean-mechanics issue; the
  tests passed on the first run.

### The literacy measurements asked for in Part 3

| Measure | Result |
|---|---|
| Wall-clock time, install → green tests | ~7 minutes of tool time. This is model time, not human time: a person porting by hand should budget days for the same slice. |
| Build iterations to green | 9 |
| Distinct compile problems | 8, listed below |
| Doc lookups | 3, all about Plausible (release tag, generator API, `Testable` instances). **Zero** for core Lean or `Std`. |
| `partial def` in library code | **0.** Every function is proven terminating (only the random generator in the tests is `partial`). |

The compile problems, in order: (1) `import` must come before the module
docstring; (2) an anonymous constructor `⟨n⟩` needed a type ascription;
(3) Lean core has no `Ord` instance for pairs (`lexOrd` is only a `def`)
and needed `attribute [local instance] lexOrd`; (4) `attribute` cannot
take a doc comment; (5) `TreeSet`'s default comparator could not be
inferred inside a `where` clause; (6) the tableau driver's termination
proof failed until the step budget became structural fuel; (7) a missing
`Inhabited` for `Frame`; (8) Plausible's `Testable` needs `NamedBinder`
around the quantifier when called from `IO`, not from the tactic. Items 3,
5, 6 and 8 are the ones a novice would get stuck on.

### Where the Lean port deliberately differs from the Haskell

1. **`toNNF`/`pushNeg`**: `iff` and the no-dual cases are inlined, because the
   Haskell recursive calls were on same-size terms (`toNNF (Implies l r)`
   inside `toNNF (Iff l r)`), which Lean will not accept as terminating. The
   results are identical, and property 3 checks that. **This is the
   termination checker catching a real (harmless) non-structural recursion
   in the Haskell.**
2. **`error` → `Except`**: `satisfies` and `mkFrame` return `Except String`.
   Lean's `panic!` logs and then *continues* with a default value, so
   translating `error` calls to `panic!` would turn crashes into silent
   wrong answers. This is the main decision the full port faces across all
   185 `error` sites: most should become `Except`, and that changes their
   signatures.
3. **Bounded loops**: `freshPrefix` searches at most |prefixes|+1
   candidates, the driver's `maxSteps` is structural fuel, and
   `transitiveClose` is bounded by |W|²+1 rounds. These give the same answers
   with termination made explicit.
4. **Readability wins**: the five-level nested `case` in `applyAllRules`
   becomes one `<|>` chain; the duplicated □F/◇T passes share one helper;
   the loops use `for … continue/return` in `Id.run do`.

### Deployment (resolves the UNVERIFIED item in Part 2)

A gamen-only executable is **3.3 MB, self-contained**: `otool -L` shows only
`libc++` and `libSystem`, and no Lean runtime is needed on the caller's
machine. It starts and answers in 0.16 s. The test executable is 105 MB,
because Plausible pulls in Lean's metaprogramming library.

**Correction (Part 5):** the shipped `gamen-validate` is also affected.
JSON support comes from `Lean.Data.Json`, which lives in the `Lean` package,
so the Lean `gamen-validate` is **104 MB** (still self-contained, still only
`libc++`/`libSystem`). For scale, the Haskell `gamen-validate` is 54 MB.
The 3.3 MB figure applies only to a binary without JSON.

### Not verified by this test

- Byte-for-byte agreement with gamen-hs on the same inputs (the protocol
  cross-check recommended in Part 3, step 5).
- Performance against the Haskell prover on larger formulas.
- The hard parts of the codebase: Lyon–van Berkel saturation, XSTIT, and the
  JSON protocol.

### Verdict

The slice supports making Lean 4 the lead candidate. The port was close to
mechanical. Derived `Ord`/`Hashable`/`DecidableEq` on the 30-constructor
type, `Std.TreeSet`/`TreeMap`, and exhaustiveness checking all worked as
predicted. The costs predicted in Part 2 showed up exactly where expected
(termination, the pair-`Ord` gap, and the property-testing ergonomics) and
nowhere else. The termination checker also paid off: it flagged a
same-size recursion in the Haskell `toNNF` that no Haskell tool would
report. Recommended next step: port `protocol/` plus `ProtocolSpec` and run
the gamen-hs and Lean binaries side by side on the same JSON Lines inputs.

## Part 5 — Protocol port and side-by-side comparison (run 2026-09-23, Opus 5.5)

Code: `sketches/lean/Gamen/Protocol.lean`, `sketches/lean/Validate.lean`,
`sketches/compare/compare.py`. Results: `sketches/compare/results/`.

### What was ported

| Haskell source | Lean port | Notes |
|---|---|---|
| `protocol/Gamen/Protocol/Formula.hs` (167 lines) | `Gamen/Protocol.lean` (236, with fragment gating) | Tree-format codec for all 30 constructors and the flat LLM-extraction format, including its fallbacks (unknown `op` becomes □, unknown `temporal_op` is ignored, `null` counts as absent). |
| `src/Gamen/Fragment.hs` (242) | same file | `constructorName`, `immediateSubformulas`, `firstOffender`, both fragment predicates, `hasAgentOperator`. Recursion through the subformula list is total, proved with a one-line `sizeOf` lemma. |
| `validate/Main.hs` (329) | `Validate.lean` (164) | All five actions (`ping`, `check_consistency`, `validate_formula`, `validate_agent`, `check_pairwise`), the three-valued status fields, the 5,000-step budget, and the JSON Lines loop. |
| `Temporal.systemKDt` | `Tableau.lean` | The D□/D◇ witness rules. The temporal T/4 rules are omitted because the fragment gate rejects temporal operators before the tableau can reach them. |

**Scope gap, by design.** gamen-hs sends `belief`/`ranked_belief` to its
doxastic-D and ranking rules, and any agent operator to the deontic-STIT
prover. Neither is ported. When a request needs one of them, the Lean
binary answers `{"ok": false, "error": "not ported in Lean slice: …"}`, so
it never gives a wrong verdict for something it cannot compute. Fragment
*rejections* happen before dispatch and are fully ported.

### Method

`compare.py` (standard-library Python) builds 3,653 requests, sends the
identical stream through one long-running process of each binary (the way
guideline-validation, patient-agent-assistant, and cwyde use it), and
classifies every response pair:

- **identical**: byte-for-byte equal lines.
- **equivalent**: the same JSON, or both are parse errors whose wording
  comes from the JSON library (aeson's `Error in $: …` vs. `Lean.Json`).
- **scope_gap**: Lean said "not ported."
- **DISAGREE**: anything else.

| Section | What it covers |
|---|---|
| A envelope (19) | ping, malformed JSON, non-object requests, unknown action, missing or mistyped fields, whitespace line, trailing `\r` |
| B codec (530) | each of the 30 constructors, plus 500 random trees over all 30 (negative ranks, Unicode atom names, empty agent lists) |
| C flat (166) | every combination of op × agent × temporal_op × conditional (80), plus a missing atom, a null agent, and both `type` and `op` present; each as `validate_formula` and as `check_consistency` |
| D consistency (2,300) | 2,000 random sets of propositional/□/◇ formulas (1–4 formulas, depth ≤ 4), plus 300 sets with one arbitrary-operator formula mixed in |
| E pairwise (320) | 300 random K-fragment lists (0–6 formulas) and 20 with a temporal formula |
| F validate_agent (12) | the patient-atom heuristic for clinician/patient/joint |
| G guideline data (306) | the 141 flat-format formulas extracted from the guidelines in `guideline-validation/data/*.yaml`, checked one at a time, per guideline set, and pairwise |

### Results

| Section | identical | equivalent | scope_gap | DISAGREE |
|---|---:|---:|---:|---:|
| A envelope | 6 | 13 | 0 | 0 |
| B codec-each | 30 | 0 | 0 | 0 |
| B codec-random | 500 | 0 | 0 | 0 |
| C flat | 83 | 0 | 0 | 0 |
| C flat-consistency | 70 | 1 | 12 | 0 |
| D consistency-K | 2,000 | 0 | 0 | 0 |
| D consistency-mixed | 255 | 0 | 45 | 0 |
| E pairwise-K | 300 | 0 | 0 | 0 |
| E pairwise-mixed | 20 | 0 | 0 | 0 |
| F validate_agent | 12 | 0 | 0 | 0 |
| G guideline (4 sections) | 306 | 0 | 0 | 0 |
| **Total (3,653)** | **3,582 (98.1%)** | **14** | **57** | **0** |

- **Zero disagreements.** Every response the Lean binary is able to give
  matches the Haskell response. For 3,582 of 3,596 (all but the 14
  error-wording cases) the match is byte-for-byte, including JSON key order,
  the Unicode in `display` strings, and `null` for an absent `concern`.
- **The verdicts are not trivial.** Among the Haskell responses: 1,758
  consistent, 530 inconsistent, 282 pairwise conflicts, 149 indeterminate
  pairs, and **one budget-exhausted `unknown`, where the Lean prover ran out
  of steps at the same point.** That can only happen if the expansion order
  and step counting match exactly, not just the final answers.
- **The real guideline data matched completely** (306/306 identical). None
  of the 141 extracted formulas carries an `agent`, so none reaches the
  deontic-STIT prover: 133 are propositional/□/◇ and are decided by the
  ported tableau, and 8 carry a `temporal_op`, so both binaries reject them
  with "unsupported operator: FutureBox (not in the kdt+doxasticD
  fragment)" or its FutureDiamond counterpart. Agent-attributed guideline formulas would be scope gaps
  today; this data set simply contains none.
- **The 57 scope gaps** are all belief/ranked-belief sets or agent-operator
  sets that pass the deontic-STIT gate, exactly the two backends not ported.

**The harness can detect disagreements.** Rebuilding the Lean binary
without the D□/D◇ rules (dropping seriality) and rerunning the full corpus
produced **88 disagreements** (64 consistency-K, 21 pairwise-K, 3
mixed-pairwise). A typical one: `{□(⊥ ∧ r)}` is inconsistent in KD
(Haskell) but consistent in K (the mutated Lean build). Everything
unrelated to seriality still matched. The mutated run's summary is kept as
`results/mutation-no-D-rules-summary.txt`. The correct build was restored
and re-verified on that example.

### Performance and size

| | Haskell | Lean |
|---|---:|---:|
| Whole corpus, one process | 215 s | 178 s (−17%) |
| Binary size | 54 MB | 104 MB |
| Runtime dependencies | libc++, libSystem | libc++, libSystem |

Both binaries spend most of the corpus time on a few large random sets,
and the one budget-exhausted request alone runs its full 5,000 steps in
each. Lean's lead is modest and comes from a single run on one machine,
so treat it as "no worse," not as a benchmark. The binary-size gap comes
from `Lean.Data.Json` bringing in the Lean compiler's libraries. A
standalone JSON library would remove most of it, but it doesn't matter for
a subprocess that starts once per session.

### What this establishes, and what it doesn't

Established:
- The wire protocol can be reproduced byte-for-byte in Lean. The three
  downstream projects would not notice the swap for the requests in scope.
- The ported tableau is behaviorally identical to the Haskell tableau on the
  consistency fragment, down to the step budget.
- The slice was ported without behavioral drift. There were no logic bugs
  to fix during the comparison: the Lean binary agreed on its first full
  run.

Not established:
- The doxastic, ranking-theory, and deontic-STIT backends. The G3DS prover
  (Lyon & van Berkel; `DeonticStit/*`, ~1,500 lines) is the hardest remaining
  module and the one most likely to hit termination-checker friction.
- The dcleg service (`service/`), which has its own protocol.
- Performance at scale beyond this corpus.

### Recommended next step

Port the deontic-STIT prover (`DeonticStit.Sequent`, `Rules`, `Saturation`,
`Prove`, `CounterModel`) and extend `compare.py` with its fixtures from
`DeonticStitSpec.hs`. It is the largest risk left in the port. If it goes
as cleanly as the tableau did, a full port is a matter of time rather than
feasibility.
