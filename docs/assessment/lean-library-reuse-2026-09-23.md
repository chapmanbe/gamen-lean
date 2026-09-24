# What gamen-hs builds by hand that Lean already provides

Dated record, 2026-09-23 (Opus 5.5). Question from the project lead: before
porting more modules, find the general-purpose machinery gamen-hs writes from
scratch that Lean's ecosystem already has, so the port calls existing
components instead of duplicating them.

This does not reopen the choice of `Std.TreeMap`/`Std.TreeSet` and `deriving`
(settled in `feasibility-assessment.md`).

**Short answer.** Very little should be swapped in for executable code. gamen-hs's
core library depends only on `base` and `containers` (`gamen.cabal`, lines 59–61),
so it does hand-roll general machinery. But most of it is five-line code whose
iteration order or output text is part of the wire contract, and the library
versions are either Prop-valued (usable only as specifications), ordered
differently, or sit behind a dependency that would cost students gigabytes. The
real gains are: (1) a few small core functions to call directly
(`List.eraseDups`, `Rat`, `Nat.testBit`, `Ord (List α)`); (2) one shared,
fueled fixpoint helper to replace six copies of "iterate until nothing changes";
(3) one shared set of relation helpers instead of four copies of the
transitivity check; and (4) a clear list of core and Mathlib definitions to
prove the executable code against later.

## How this was checked

- Lean core and Std: grepped the pinned toolchain source,
  `~/.elan/toolchains/leanprover--lean4---v4.34.0/src/lean` (cited below as
  `core:`).
- Batteries: shallow clone of tag `v4.34.0`, and a timed full build.
- Mathlib: raw files and `lake-manifest.json` at tag `v4.34.0`, plus a blobless
  clone to count files.
- Foundation and ModalLogic: `lean-toolchain`, `lakefile.toml`, and the file tree
  of `master`/`main` through the GitHub API.
- gamen-hs: targeted greps of `src/Gamen/` at the checkout used by `PORTING.md`.

VERIFIED means I read the definition or file named. UNVERIFIED means it's from
memory or an estimate I did not measure.

## 1. Inventory and verdicts

Verdicts: **USE NOW** (call the library, executable, no new dependency);
**SPEC FOR LATER PROOFS** (Prop-valued or noncomputable, so it can't replace
code, but it's what the code should be proved to agree with); **KEEP OWN** (port
the Haskell as written).

| Concept | gamen-hs location | Lean candidate | Executable? | Verdict | Reason | Verified? |
|---|---|---|---|---|---|---|
| Relation properties: reflexive, symmetric, transitive, serial, euclidean, equivalence | `FrameProperties.hs` (all), `Kripke.hs:101` `isEquivalenceOn`, `Stit.hs:335` `isTransitiveOn`, `Temporal.hs:165` `isTransitiveFrame` | Core: `structure Equivalence` (`core: Init/Core.lean:1325`), `class Std.Refl`/`Std.Symm` (`Init/Core.lean:2522, 2537`), `class Trans` (`Init/Prelude.lean`). Mathlib: `Reflexive`, `Symmetric` (`Mathlib/Order/Defs/Unbundled.lean:183, 187`), `Std.Total`. Euclidean exists nowhere in core or Mathlib; only in FFL's `ModalLogicArchive/Vorspiel/Rel/Euclidean.lean` (`RightEuclidean`). | No: all Prop-valued over `α → α → Prop` | KEEP OWN (Bool over `TreeMap`), SPEC with **core** `Equivalence`/`Std.Refl`/`Std.Symm`/`Trans` | No executable relation-property checker over a finite successor map exists in any of these libraries. The core classes are enough for the specs; Mathlib isn't needed. Separately: gamen-hs has four copies of the transitivity check (see §2). | VERIFIED |
| Subset test on sets | `Set.isSubsetOf` throughout; Lean port has private `subsetOf` in `Gamen/FrameProperties.lean:27` | `Std.TreeSet` has no subset operation. Its API is `insert, contains, erase, filter, partition, all, any, union, inter, diff, merge, foldl, toList, ofList, min?/max?, …`, with no `isSubset` and no `map`. | n/a | KEEP OWN, but make it public and shared | It's needed by FrameProperties, Kripke, Stit, and Epistemic. | VERIFIED (`core: Std/Data/TreeSet/Basic.lean` def list) |
| Equivalence classes / partition | `Kripke.hs:123` `equivalenceClasses`; `Atl/ImperfectInfo.hs:95` `epistemicClasses` | Batteries `UnionFind` (`Batteries/Data/UnionFind/Basic.lean`, indexed by `Fin n`); Mathlib `Setoid.classes`, `Setoid.IsPartition`, `isPartition_classes` (`Mathlib/Data/Setoid/Partition.lean:60, 193, 200`) | UnionFind yes; Mathlib no (`Set (Set α)`) | KEEP OWN; SPEC against `Setoid.IsPartition` (or an equivalent statement written without Mathlib) | gamen-hs's algorithm is deliberately *not* equivalence closure. It puts each world in `{w} ∪ R(w)` (the adversarial-review B7 fix), which differs from union-find's result on relations that aren't equivalences. Its output order is reverse discovery order (`cls : acc`). Union-find would change both, and it needs a string→index map. | VERIFIED |
| Cartesian product of lists (Haskell `sequence` on `[[a]]`) | `Kripke.hs` `checkIndependence`; `ImperfectInfo.hs:147, 162` (strategies, profiles); `Cgs.hs:127` `jointMoves` (hand-written `foldr`) | Batteries `List.sections`, `List.sectionsTR`, `List.product` (`Batteries/Data/List/Basic.lean:450, 455, 506`) | Yes | KEEP OWN (3-line local def) | `List.sections` enumerates in a **different order** from Haskell's `sequence`: the *first* list varies fastest (`[[1,2],[3,4]]` ↦ `[[1,3],[2,3],[1,4],[2,4]]` vs Haskell `[[1,3],[1,4],[2,3],[2,4]]`). That's harmless under `all`/`any` (as in `checkIndependence`), but not where the list itself is returned (`allUniformProfiles`). It isn't worth adding Batteries for this. | VERIFIED (definition read; order derived from the definition, not run) |
| Powerset / subsequences | `Laca.hs:270` `powerSet`; `Dcleg.hs:358` `subsequences` | Batteries `List.sublists` (same order as Haskell `subsequences`, per its docstring `[[], [1], [2], [1,2], [3], …]`) and `List.sublists'` (`[[], [3], [2], [2,3], [1], …]`, the same order as gamen-hs's `Laca.powerSet`) (`Batteries/Data/List/Basic.lean:343, 354`); Mathlib `Finset.powerset` | Yes | KEEP OWN (tiny); cite the Batteries name in the docstring | Both Batteries orders happen to match the Haskell. That's useful to know if Batteries is ever added, but not a reason to add it. `Finset.powerset` has no order. | VERIFIED |
| `nub` (dedup, keep first occurrence) | `Dcleg.hs:360` | core `List.eraseDups` (`Init/Data/List/Basic.lean:2296`; docstring: "keeping the first occurrence") | Yes | **USE NOW** | Same semantics and same O(n²). | VERIFIED |
| Valuation enumeration by bit tricks | `Semantics.hs:181` (`testBit`), `FrameProperties.hs:158–171` (`shiftL`, `.&.`), `Laca.hs:98` | core `Nat.testBit` (`Init/Data/Nat/Bitwise/Basic.lean`), `<<<`, `>>>`, `&&&` | Yes | **USE NOW** (already done in `Semantics.lean:160`, `FrameProperties.lean:153`) | Lean `Nat` is arbitrary precision, so the Haskell `Int` overflow concern disappears. `Laca.hs:98`'s `min 62` cap is then unnecessary for correctness, but keep it for identical results. | VERIFIED |
| Propositional tautology / SAT | `Semantics.hs:174` `isTautology` (2ⁿ truth-table sweep) | core `Std.Sat.CNF` (`Std/Sat/CNF/Basic.lean`: data type, `eval`, `Sat`/`Unsat` as Props; **no solver**); `bv_decide` calls the bundled `cadical` binary through `satQuery` in `CoreM` (`Lean/Meta/Tactic/BVDecide/External.lean:147`) | CNF eval yes; the solver only at elaboration time | KEEP OWN | No runtime SAT solver ships in core. `cadical` is spawned as a subprocess from the meta level, so it isn't callable from the native `gamen-validate` binary without shipping cadical and re-implementing the plumbing. It also can't see the deep-embedded `Formula`. For the small atom counts in play, the truth table is fine and already byte-matched. | VERIFIED |
| Fixpoint iteration ("iterate `f` until `f x == x`") | `Atl/ModelCheck.hs:34, 42` `lfp`/`gfp` (used by `Atl`, `Atel`, `ImperfectInfo`); `Tableau.hs:1058` `transitiveClose`; `DeonticStit/CounterModel.hs:188` `euclideanClose`; `Epistemic.hs:373` `largestBisimulation` (`refine`); `Laca.hs:82` `trajectory` | Core: `partial_fixpoint` definition mode (`Lean/Elab/PreDefinition/PartialFixpoint/`), backed by a **noncomputable** `lfp` (`Init/Internal/Order/Basic.lean:310`). Mathlib: `OrderHom.lfp`/`gfp` (`Mathlib/Order/FixedPoints.lean:49, 54`), `lfp_eq_sSup_iterate`, `gfp_eq_sInf_iterate` (Kleene, lines 272, 282) | Mathlib: no. `partial_fixpoint`: compiles, but proves no termination. | KEEP OWN as **one shared fueled helper**; SPEC against Mathlib `OrderHom.lfp` + `lfp_eq_sSup_iterate` | None of the six Haskell copies has a step bound. CLAUDE.md requires fuel. The fuel has a natural bound: an inflationary (deflationary) iteration inside a finite universe `U` stabilizes within `|U| + 1` steps (`|W|² + 1` for relation closures). Out of fuel → `Except` error, provably unreachable later. `partial_fixpoint` behaves like `partial def` for termination, so it's excluded by the current convention. | VERIFIED |
| Transitive closure / reachability | `Tableau.hs:1058` `transitiveClose`; `Epistemic.hs:297` `commonKnowledge` (BFS from `step w`, i.e. R⁺ not R*) | core `Relation.TransGen` (`Init/Core.lean:1356`); Mathlib `Relation.ReflTransGen`, `ReflGen`, `EqvGen` (`Mathlib/Logic/Relation.lean:388–411`) | No | KEEP OWN, SPEC with **core** `Relation.TransGen` | The `commonKnowledge` docstring stresses R⁺ vs R*: exactly the `TransGen`/`ReflTransGen` distinction, and `TransGen` is in core. | VERIFIED |
| Extended naturals (κ with ∞) | `Plausibility.hs:147` `RankedPlausibility = FiniteRank Int \| InfiniteRank`; `RankingTheory.hs:149, 168` use `maxBound :: Int` as ∞ | Mathlib `ENat := WithTop ℕ` (`Mathlib/Data/ENat/Defs.lean:17`); core `Option Nat` | ENat: probably (it's `Option` underneath); not compiled here | KEEP OWN | A two-constructor inductive mirrors the Haskell and its derived `Show`. `RankingTheory`'s `maxBound` is **reported** as τ = +∞ (`RankingTheory.hs:159`), so if it reaches any output the Lean port needs the literal `9223372036854775807`, not a typed ∞. It isn't worth Mathlib either way. | Definition VERIFIED; ENat computability UNVERIFIED |
| Rationals | `Plausibility.hs:186, 218` (`Rational` carriers) | core `Rat` (`Init/Data/Rat/Basic.lean:33`) | Yes | **USE NOW** | Now in core; no Batteries or Mathlib needed. Printing differs: Lean `toString` gives `1/2` (line 50) where Haskell `show` gives `1 % 2`. That's internal only, since Plausibility isn't on the `gamen-validate` wire. | Lean side VERIFIED; Haskell `show` format UNVERIFIED (from memory) |
| Plausibility order class | `Plausibility.hs:106` `class Plausibility` (`plLeq`, `plJoin`, …) | core `Std.PartialOrderPackage`/`LinearOrderPackage` (`Init/Data/Order/PackageFactories.lean`); Mathlib `Preorder`/`PartialOrder` | Classes yes; laws are Props | KEEP OWN class (verbatim, as PORTING.md says); state the module-header laws as Plausible properties now and as Lean theorems later | The Haskell class isn't an order class (it bundles ⊕, ⊗, conditioning). Reusing an order class for `plLeq` would split one interface in two. | VERIFIED |
| Ordered sets/maps | everywhere | `Std.TreeSet`/`TreeMap` (decided); **`Std.ExtTreeSet`** has `DecidableEq` and extensional equality (`core: Std/Data/ExtTreeSet/Basic.lean:555`); plain `TreeSet` has `BEq` and decidable `~m` equivalence (`Std/Data/TreeSet/DecidableEquiv.lean:22`) | Yes | USE NOW; `ExtTreeSet` is the natural target when *proving* set-valued results equal | Nothing to change in code. For proofs, `ExtTreeSet` avoids the "same elements, different tree" problem. | VERIFIED |
| `Ord` on pairs | `Set (World, World)`, tableau keys | core `lexOrd` (`Init/Data/Ord/Basic.lean:623`) plus lawful `TransOrd`/`LawfulEqOrd` instances for pairs (`Init/Data/Order/Ord.lean:627–641`) | Yes | USE NOW (already, `Tableau.lean:22`) | Core makes `lexOrd` a *local* instance too. The lawful instances exist, so TreeSet lemmas apply. | VERIFIED |
| `Ord` on sets of worlds (Haskell `Set (Set World)`) | `Kripke.hs` `checkIndependence` (`Set.fromList` of choice cells); Stit/Xstit moments | core `Ord (List α)` with lawful instances (`Init/Data/Order/Ord.lean:714–720`), `compareOn` with `TransCmp` (`Ord.lean:622`); `List.compareLex` | Yes | **USE NOW**: `compareOn (·.toList)` | `TreeSet` has no `Ord` instance. Comparing ascending element lists is what Haskell's `Ord (Set a)` does (from memory, but only internal ordering depends on it). | Lean side VERIFIED; Haskell side UNVERIFIED |
| Queue / sequence / int set | `Tableau.hs:53–56` (`Seq`, `IntSet`) | core `Array`, `Std.Queue` (`Init/Data/Queue.lean`), `Std.TreeSet Nat` / `Std.HashSet` | Yes | USE NOW (already `Array` + `TreeSet` in `Tableau.lean`) | — | VERIFIED |
| Union-find, priority queue, graph library | not used anywhere in gamen-hs | Batteries `UnionFind`, `BinaryHeap`, `PairingHeap` | Yes | n/a | Nothing to replace. | VERIFIED (grep of `src/`, `protocol/`, `validate/`, `service/`) |
| JSON | `protocol/`, `validate/Main.hs` (aeson) | core `Lean.Json` (`Lean/Data/Json/Basic.lean`) | Yes | USE NOW (done) | Hand-written encoders stay; `deriving ToJson` would change field order and break byte identity. | VERIFIED |
| Pretty-printing | `Formula.hs` `Show`; `Visualize.hs:72` DOT `render` | core `Std.Format`, `String.intercalate` | Yes | KEEP OWN | Output text is the wire contract. | VERIFIED |
| Property testing | `test/Properties.hs` (QuickCheck) | Plausible (already a dependency) | Yes | USE NOW (done) | — | VERIFIED |
| Modal logic formalization (Kripke semantics, frame correspondence, tableau soundness) | whole library | FFL **Foundation** `master` (Lean v4.34.0, Mathlib v4.34.0) now has only first-order, propositional, and *provability-logic* Kripke models (`Foundation/ProvabilityLogic/Kripke/Basic.lean`: `Rel : World → World → Prop`). The K/KT/S4/S5 material, including `ModalLogicArchive/Modal/Tableau.lean`, lives in **FFL/ModalLogic**, whose `main` pins Lean **v4.31.0** and whose `defaultTargets` are only `Fin74` and `Neighborhood` (the archive isn't built by default). | No (Prop-valued, classical) | Reading reference only; SPEC style to imitate | Can't be a dependency: wrong toolchain, not built by default, no release tags. The feasibility assessment already noted that the archive tableau was reported broken under 4.33.1; whether it builds today is UNVERIFIED. | VERIFIED (toolchains, lakefiles, trees); build status UNVERIFIED |

Module-internal machinery that has no library counterpart and stays hand-written:
the tableau worklist (`Tableau.hs:896` `findExpandableBranch`), prefix trees and
blocking (`Tableau.hs:252–271`), the deontic-STIT generation tree
(`DeonticStit/Saturation.hs:85–162`), and `Cgs.preC`. These are the project's
content, not general-purpose tools.

## 2. Kripke (next module) and FrameProperties (done)

### `isEquivalenceOn`

- **Don't write a fourth transitivity check.** Haskell's `isEquivalenceOn ws rel`
  is, line for line, `isReflexive && isSymmetric && isTransitive` from
  `FrameProperties.hs` applied to `⟨ws, rel⟩`. Both look up successors with
  `findWithDefault ∅` (Lean: `getD w ∅`, which is `Frame.accessible`), and
  `Frame` carries no invariant. The simplest faithful port is:

  ```lean
  def isEquivalenceOn (ws : Std.TreeSet World) (rel : Std.TreeMap World (Std.TreeSet World)) : Bool :=
    isEquivalenceRelation { worlds := ws, relation := rel }
  ```

  But `FrameProperties` imports `Kripke`, not the reverse. So move the three
  predicates (and `subsetOf`) down into `Kripke.lean` as functions on
  `(ws, rel)`, and have `FrameProperties.isReflexive fr := reflexiveOn fr.worlds fr.relation`,
  etc. The same helper then serves `Stit.isTransitiveOn` and
  `Temporal.isTransitiveFrame`, which are two more copies. Keep all gamen-hs
  names as thin wrappers so the side-by-side reading still works.
- **Spec to prove against later:** core `Equivalence` on the relation restricted
  to `ws`: `isEquivalenceOn ws rel = true ↔ Equivalence (fun (a b : {w // w ∈ ws}) => b.1 ∈ rel.getD a.1 ∅)`.
  This needs only core and Std's `TreeSet`/`TreeMap` lemmas, not Mathlib.
  Similarly `isReflexive ↔ Std.Refl`, `isSymmetric ↔ Std.Symm`,
  `isTransitive ↔ IsTrans`-style `∀ a b c`. Euclidean, serial, and the rest are
  stated by hand; nothing to import.

### `equivalenceClasses`

- **Keep the Haskell algorithm.** It isn't equivalence closure: on a relation
  that isn't an equivalence, `{w} ∪ R(w)` classes can overlap, and that's the
  documented B7 behavior pinned by `RegressionIssue18.hs:337`. Union-find
  (Batteries) and `Setoid.classes` (Mathlib) both compute something else there.
- **Preserve the order**: the result is in reverse discovery order (`cls : acc`,
  discovery in ascending world order). Callers (`Stit.hs:247`, `Xstit.hs:308`)
  iterate over moments, so the order can leak into anything that lists moments.
- **Spec for later:** if `isEquivalenceOn ws rel`, the result is a partition of
  `ws` (nonempty, pairwise disjoint, covers `ws`) and each class is `R(w)`. That's
  Mathlib's `Setoid.IsPartition` (`Mathlib/Data/Setoid/Partition.lean:193`),
  but it's short enough to state over lists/`TreeSet` without Mathlib. **Now:**
  add these three as Plausible properties over random equivalence relations
  (generate by random partition), plus the B7 regression case.

### `checkIndependence`

- Needs (a) deduplicated choice cells per agent, i.e. a set of `TreeSet`s, and
  (b) the cartesian product of those lists.
- (a) Either `List.eraseDups` over the cells (uses `TreeSet`'s `BEq`, O(n²),
  fine at these sizes), or a `TreeSet` with `compareOn (·.toList)` via core's
  `Ord (List α)`. `eraseDups` keeps first-occurrence order rather than sorted
  order; the result is consumed by `all`, so either is correct. Prefer
  `compareOn` if you want the intermediate list to match Haskell's sorted order
  for debugging.
- (b) A local 3-line `sections`/`sequence`. Batteries' `List.sections` enumerates
  in a different order; that's harmless here (`all`), but not worth a dependency.
- Haskell's `foldl1 Set.intersection` is partial on an empty list; that's
  unreachable because the empty-agent case returns first. In Lean, fold from the
  first cell (pattern match `c :: cs`) so no `panic!`/default can appear.
- Edge case to test: empty moment with nonempty agents. Haskell `sequence` over
  an empty cell list gives `[]`, so the result is `True`. Match it.

### FrameProperties (already ported)

- Executable code: no change needed, except swapping the private `subsetOf` for
  the shared helper once it moves to `Kripke.lean`.
- `isValidOnFrame`'s valuation enumeration is already core bit ops. There's no
  library enumerator to swap in, and the order is part of the contract (first
  failing valuation).
- **Specs for later proofs**, all core-only: `isReflexive ↔ ∀ w ∈ W, R w w`,
  and so on per B&D Table 2.1. `isValidOnFrame fr φ = .ok true ↔ ∀ V, isTrueIn ⟨fr, V⟩ φ`
  (B&D Definition 2.4), which needs a lemma that the bit enumeration hits every
  valuation over `atoms φ`. The correspondence results (B&D Proposition 2.9 and
  Definition 2.11, e.g. T ↔ reflexive) are the natural first *theorems* of the
  project, and they're exactly what FFL's archive proved in Prop form. Read it
  for proof structure; don't import it.

## 3. Dependencies

Current: `plausible` (`v4.34.0`, 15 MB checked out) and `proofwidgets`
(`v0.0.111`, 25 MB). ProofWidgets v0.0.111 does not pull in Batteries
(`lake-manifest.json` lists only the two).

| Candidate | Release for 4.34.0? | Would it force an upgrade? | Cost | What it buys |
|---|---|---|---|---|
| **Batteries** | Yes, tag `v4.34.0` (`f2effa3`), `lean-toolchain` = `v4.34.0` (VERIFIED) | No | 260 `.lean` files, 2.7 MB source; full build **70 s wall** on an M4 Max, **140 MB** `.lake` (measured) | `sections`, `sublists`, `product`, `UnionFind`, heaps. None of it needed (see table) |
| **Mathlib** | Yes, tag `v4.34.0` (VERIFIED). Its manifest pins `plausible` at `118aa17` and `proofwidgets` at `106ff4f`, the **same commits** as gamen-lean's `v4.34.0` / `v0.0.111` (VERIFIED), plus Batteries `f2effa3`, Aesop, Qq, LeanSearchClient, importGraph, Cli | No | 9,112 `.lean` files (counted). With `lake exe cache get`: a multi-GB download and several GB of `.olean`s on disk. Without the cache: hours of compilation on a laptop (UNVERIFIED estimates, not measured). Linking Mathlib modules into `gamen-validate` could also grow the binary (UNVERIFIED) | Specs: `Setoid.IsPartition`, `OrderHom.lfp` + Kleene lemmas, `Relation.ReflTransGen`, `ENat`. No executable code worth using |
| **Foundation** (FFL) | No tags; `master` is on `v4.34.0` with Mathlib `v4.34.0` (VERIFIED) | No, but tracking `master` is a moving target | All of Mathlib plus Foundation and doc-gen4/Forgive requires | Nothing for modal Kripke semantics any more; that moved to FFL/ModalLogic (on Lean `v4.31.0`, archive not built by default) |

**Recommendation: add nothing now.** Every executable need is covered by core and
Std. Batteries is cheap (about a minute to build), but the only things it would
supply are three-line list functions, and two of them enumerate in a different
order from the Haskell.

When the project starts writing proofs (tableau soundness, frame
correspondence, ATL fixpoints), put them in a **separate Lake package** in the
same repository (for example `proofs/` with its own `lakefile.toml` requiring
`gamen` by path and `mathlib` at `v4.34.0`). Lake fetches every `require` of the
package you build, so a Mathlib require in the root `lakefile.toml` would land
on every student who installs the notebooks. A separate package keeps it off
them. (Standard Lake layout; I didn't test it here, so UNVERIFIED.) Because
Mathlib `v4.34.0` pins exactly our Plausible and ProofWidgets commits, that
package can be added later without moving the toolchain. Upgrading the toolchain
means moving all four pins together, which extends the CLAUDE.md rule "upgrade
all three together" to four.

Most early proofs need only core: `Equivalence`, `Std.Refl`/`Symm`,
`Relation.TransGen`, and Std's `TreeSet`/`TreeMap`/`ExtTreeSet` lemmas. Try
those before reaching for Mathlib.

## 4. Proposed changes to PORTING.md and CLAUDE.md (proposals only)

1. **CLAUDE.md, porting conventions: "Check core before porting a helper."**
   Add a short mapping list: Haskell `nub` → `List.eraseDups`; `Rational` →
   `Rat`; `testBit`/`shiftL`/`.&.` → `Nat.testBit`/`<<<`/`&&&`; `Ord (Set a)` →
   `compareOn (·.toList)`; `Set (a, b)` → `lexOrd` (local instance, as now).
   Note that `Std.TreeSet` has no `isSubset` and no `map`.
2. **CLAUDE.md: one fixpoint helper.** "Iterate until stable" appears six times in
   gamen-hs (`lfp`, `gfp`, `transitiveClose`, `euclideanClose`,
   `largestBisimulation`, `Laca.trajectory`), none with a bound. Port them all
   through one shared helper, for example `iterateUntilStable (fuel : Nat) (f : α → α) (x : α) : Except String α`
   with `[BEq α]`, and a documented fuel bound (`|U| + 1` for monotone iteration
   in a finite universe `U`, `|W|² + 1` for relation closures). Out of fuel is an
   `Except` error, never a default value. State explicitly that `partial_fixpoint`
   counts as `partial def` under the "no `partial def`" rule. It exists in 4.34
   and compiles, but proves no termination.
3. **CLAUDE.md or PORTING.md: shared relation helpers live in `Kripke.lean`.**
   `reflexiveOn`/`symmetricOn`/`transitiveOn`/`subsetOf` on `(worlds, successor map)`,
   with the gamen-hs names (`isEquivalenceOn`, `isTransitiveOn`,
   `isTransitiveFrame`, FrameProperties' `is*`) kept as thin wrappers. This
   bends "one Lean module per gamen-hs module" slightly. The wrappers keep the
   side-by-side reading.
4. **CLAUDE.md: order check when swapping in any library enumerator.** If a
   Haskell list combinator is replaced by a Lean one, confirm the enumeration
   order matches, and say so in the docstring. Example: Batteries `sections` ≠
   Haskell `sequence`, while `sublists` = `subsequences` and `sublists'` =
   `Laca.powerSet`. If the order differs, allow it only when the result is
   consumed by `all`/`any`/set construction.
5. **PORTING.md: add a "Spec for later proofs" note per module.** Kripke/
   FrameProperties → core `Equivalence`, `Std.Refl`/`Symm`, B&D Table 2.1;
   `equivalenceClasses` → partition (Mathlib `Setoid.IsPartition` or local);
   Tableau closures and `commonKnowledge` → core `Relation.TransGen`;
   `Atl.ModelCheck` → Mathlib `OrderHom.lfp`/`gfp` + `lfp_eq_sSup_iterate`;
   Plausibility → its module-header laws.
6. **PORTING.md: dependency policy.** "The `Gamen` library, notebooks, and
   `gamen-validate` use only core, Std, Plausible, and ProofWidgets. Mathlib, if
   it's ever needed, goes in a separate proofs package pinned to the same
   toolchain tag." Also record that FFL Foundation no longer contains modal
   Kripke semantics, so later readers don't go looking for it.
7. **RankingTheory note for its porter:** `maxBound :: Int` is used as the value
   of κ(∅) and τ = +∞ (`RankingTheory.hs:149, 168`). Lean `Int` has no
   `maxBound`. Use the literal `9223372036854775807` wherever the value can
   reach output or tests, and flag every such spot.
