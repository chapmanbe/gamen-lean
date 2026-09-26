import Gamen.Tableau
import Gamen.RankingTheory
import Gamen.FrameProperties
import Gamen.DeonticStit
import Gamen.DeonticStit.Prove
import Gamen.DeonticStit.CounterModel
import Plausible

/-!
# Tests.PropertyHelpers

Generators and checkers shared by `Tests/Main.lean` (`lake test`: the fast
properties, plus everything else) and `Tests/SlowMain.lean` (`lake exe
slowtests`: the seven `==>`-shaped properties ported from
`test/Properties.hs`'s "Gamen.Tableau: soundness vs. Kripke semantics" and
"Gamen.RankingTheory: structural invariants" describe blocks, which need
Haskell's full `numInst`/discard-cap/size to mean anything and so run for
several minutes — see `checkGuarded`'s docstring below and
`PORTING.md`'s `Properties` row).

Moved out of `Tests/Main.lean` into its own module (not duplicated) so
both executables see the identical generators, `Arbitrary`/`Shrinkable`
instances, model-closure helpers, and the `checkGuarded` discard-loop.

Also holds the Lean-only decision-procedure cross-checks (Gamen.jl#20,
not in gamen-hs) used by both executables; see the last section.
-/
open Gamen Plausible

/-- Kripke-fragment formulas over atoms p, q, r. Mirrors `genFormula` in
`test/Properties.hs`, plus `iff`, which the Lean `toNNF` rewrites
differently from the Haskell text and so deserves random coverage. -/
partial def genFormula : Nat → Gen Formula
  | 0 => Gen.frequency (pure .bot) [(1, pure .bot), (4, genAtom)]
  | n + 1 =>
    let h := (n + 1) / 2
    Gen.frequency (pure .bot) [
      (1, pure .bot), (4, genAtom),
      (3, .not <$> genFormula n),
      (3, .and <$> genFormula h <*> genFormula h),
      (2, .or <$> genFormula h <*> genFormula h),
      (2, .implies <$> genFormula h <*> genFormula h),
      (1, .iff <$> genFormula h <*> genFormula h),
      (2, .box <$> genFormula n),
      (2, .diamond <$> genFormula n)]
where
  genAtom : Gen Formula := do
    let ⟨i, _⟩ ← Gen.choose Nat 0 2 (by omega)
    return .atom (["p", "q", "r"].getD i "p")

instance : Arbitrary Formula := ⟨Gen.sized fun n => genFormula (min n 12)⟩

instance : Shrinkable Formula where
  shrink
    | .not g | .box g | .diamond g => [g]
    | .and l r | .or l r | .implies l r | .iff l r => [l, r]
    | _ => []

/-- A fixed 3-world model with a reflexive point, a dead end, and a cycle,
used to check that `toNNF` preserves truth everywhere. `none` if `mkFrame`
rejects it (not `get!`, whose panic would continue with an empty model and
make the properties below pass vacuously). -/
def testModel : Option Model :=
  (mkFrame ["w1", "w2", "w3"] [("w1", "w1"), ("w1", "w2"), ("w2", "w3"), ("w3", "w1")]).toOption.map
    (mkModel · [("p", ["w1", "w3"]), ("q", ["w2"]), ("r", [])])

def truthsIn (m : Option Model) (f : Formula) : Option (List Bool) :=
  m.bind fun m => (m.frame.worlds.toList.mapM (satisfies m · f)).toOption

/-! ### `Model`/`KappaModel` generators (Plausible)

Mirrors `test/Properties.hs`'s `ArbModel`/`ArbKappaModel` newtypes. The
Haskell wrappers exist only to dodge orphan-`Arbitrary`-instance
restrictions; Lean's typeclass resolution has no such restriction, so the
instances below attach directly to `Model` and `KappaModel`.
(`ArbEpistemicModel` is out of scope here: `Gamen.Epistemic` is not
ported.) -/

private def propAtomNames : List String := ["p", "q", "r"]

/-- Haskell's `sublistOf`: a random subset of `xs`, coin-flipping each
element for inclusion. -/
private def genSublist (xs : List α) : Gen (List α) :=
  xs.filterM fun _ => (Arbitrary.arbitrary : Gen Bool)

/-- 1–4 worlds, a random edge subset of `ws ×ˢ ws`, and a random valuation
over {p,q,r}. Mirrors `genKripkeModel`. `mkFrame`'s endpoint check can
never fire here — every edge is drawn from `ws ×ˢ ws` — so a failure
would be a real generator bug: `throw`s a `GenError`, never substitutes a
default model. A thrown `GenError` is *not* automatically a failing test
by itself, though — every caller (`run`, `checkGuarded`) must turn it into
one explicitly, because Plausible's own `.gaveUp` (what a `GenError`
becomes once it reaches `Testable.checkIO`) used to read as a pass here. -/
def genKripkeModel : Gen Model := do
  let ⟨n, _⟩ ← Gen.choose Nat 1 4 (by omega)
  let ws := (List.range n).map fun i => s!"w{i + 1}"
  let allPairs := ws.flatMap fun w1 => ws.map fun w2 => (w1, w2)
  let edges ← genSublist allPairs
  let val ← propAtomNames.mapM fun a => do
    let vs ← genSublist ws
    return (a, vs)
  match mkFrame ws edges with
  | .ok fr => return mkModel fr val
  | .error e => throw (GenError.genError e)

instance : Arbitrary Model := ⟨genKripkeModel⟩

/-- Haskell's `ArbModel` defines no custom `shrink`, so QuickCheck's
default (no shrinking) applies; same here. -/
instance : Shrinkable Model where
  shrink _ := []

/-- 2–4 worlds; agent "c"'s κ is pinned to 0 at the first world (so
`wellFormed` always holds) and drawn from 0–4 at the rest; random
valuation over {p,q,r}. Mirrors `genKappaModel`. -/
def genKappaModel : Gen KappaModel := do
  let ⟨n, _⟩ ← Gen.choose Nat 2 4 (by omega)
  let ws := (List.range n).map fun i => s!"w{i + 1}"
  let rest ← (List.range (n - 1)).mapM fun _ => do
    let ⟨k, _⟩ ← Gen.choose Nat 0 4 (by omega)
    return (k : Int)
  let kappaList := ws.zip ((0 : Int) :: rest)
  let val ← propAtomNames.mapM fun a => do
    let vs ← genSublist ws
    return (a, vs)
  return mkKappaModel ws [("c", kappaList)] val

instance : Arbitrary KappaModel := ⟨genKappaModel⟩

instance : Shrinkable KappaModel where
  shrink _ := []

/-- `∃ w, M,w ⊩ f`, staying in `Except`: an error (unreachable for the
Bot/Atom/Not/And/Or/Implies/Iff/Box/Diamond fragment these generators
produce, over a well-formed `Model`) must propagate as an error, not get
read as "no witness" — that would let a real bug in `satisfies` pass
silently wherever this is used as an implication's conclusion. -/
def anySatisfies (m : Model) (f : Formula) : Except String Bool :=
  m.frame.worlds.toList.anyM fun w => satisfies m w f

/-- `∀ w, M,w ⊩ f`, staying in `Except` for the same reason as
`anySatisfies`. -/
def allSatisfies (m : Model) (f : Formula) : Except String Bool :=
  m.frame.worlds.toList.allM fun w => satisfies m w f

/-- `.ok true`, and nothing else — used where a conjunct must contribute a
definite failure on `.error`, never a silent pass. -/
def isOkTrue : Except String Bool → Bool
  | .ok true => true
  | _ => false

/-- The model's relation as a flat edge set. Mirrors `edgesOf`. -/
def edgesOf (m : Model) : Rel :=
  Std.TreeSet.ofList
    (m.frame.relation.toList.flatMap fun (w, vs) => vs.toList.map fun v => (w, v))
    lexOrd.compare

/-- Rebuild a model with a different accessibility relation, given as an
edge set. Mirrors `withEdges`. -/
def withEdges (m : Model) (es : Rel) : Model :=
  let relation := es.toList.foldl
    (fun acc (w, v) => acc.insert w ((acc.getD w ∅).insert v))
    (∅ : Std.TreeMap World (Std.TreeSet World))
  { m with frame := { m.frame with relation } }

/-- Reflexive closure of `m`'s relation — the KT frame class. Mirrors
`reflexiveClosureModel`. -/
def reflexiveClosureModel (m : Model) : Model :=
  withEdges m (reflexiveClose m.frame.worlds.toList (edgesOf m))

/-- Transitive-only closure of `m`'s relation — the K4 frame class.
Mirrors `transitiveClosureModel`, through the shared, fuel-checked
`Tableau.transitiveClose` (running out of fuel is an `Except`, never a
partly-closed relation, unlike Haskell's unbounded `go`). -/
def transitiveClosureModel (m : Model) : Except String Model :=
  return withEdges m (← transitiveClose m.frame.worlds.toList (edgesOf m))

/-- Reflexive + transitive closure — the S4 frame class. Mirrors
`s4ClosureModel`: transitive-close the raw edges first, then add the
reflexive edges (matching Haskell's `reflClose m (transClose (edgesOf m))`
evaluation order). -/
def s4ClosureModel (m : Model) : Except String Model := do
  let trans ← transitiveClose m.frame.worlds.toList (edgesOf m)
  return withEdges m (reflexiveClose m.frame.worlds.toList trans)

/-- One round of `s5ClosureModel`'s fixpoint: symmetric-close, then
transitive-close, then reflexive-close. -/
private def s5Step (ws : List World) (r : Rel) : Except String Rel := do
  let r' ← transitiveClose ws (symmetricClose r)
  return reflexiveClose ws r'

/-- Iterate `s5Step` to a fixpoint (Haskell's unbounded `go`), through an
explicit fuel bound: each round either reaches the fixpoint or adds at
least one of at most `|ws|²` pairs, so `|ws|² + 1` rounds suffice, as with
`Tableau.transitiveClose`. Running out of fuel is an `Except`, never a
partly-closed relation. -/
private def s5Iterate : Nat → List World → Rel → Except String Rel
  | 0, _, _ => throw "s5ClosureModel: no fixpoint within the fuel bound"
  | fuel + 1, ws, r => do
      let r' ← s5Step ws r
      if r'.toList == r.toList then pure r else s5Iterate fuel ws r'

/-- Reflexive + transitive + symmetric closure = an equivalence relation
— the S5 frame class. Mirrors `s5ClosureModel`. -/
def s5ClosureModel (m : Model) : Except String Model := do
  let ws := m.frame.worlds.toList
  let r ← s5Iterate (ws.length * ws.length + 1) ws (edgesOf m)
  return withEdges m r

/-- A formula that is K-valid BY CONSTRUCTION: axiom schemes instantiated
with random small subformulas. Mirrors `ArbValidFormula`/`genValidFormula`
— see that Haskell docstring for why (valid formulas are too rare in the
raw random stream to reach by filtering). -/
structure ValidFormula where
  getFormula : Formula
  deriving Repr

def genValidFormula : Gen Formula := do
  let a ← Gen.resize (fun _ => 2) (Arbitrary.arbitrary : Gen Formula)
  let b ← Gen.resize (fun _ => 2) (Arbitrary.arbitrary : Gen Formula)
  Gen.elements
    [ .implies a a
    , .or a (.not a)
    , .not (.and a (.not a))
    , .implies (.and a b) a
    , .implies (.and a b) b
    , .implies a (.or a b)
    , .implies b (.or a b)
    , .implies a (.implies b a)
    , .implies .bot a
    , .iff (.not (.not a)) a
    , .iff (.not (.and a b)) (.or (.not a) (.not b))
    , .iff (.not (.or a b)) (.and (.not a) (.not b))
    , .implies (.box (.implies a b)) (.implies (.box a) (.box b))
    , .iff (.diamond a) (.not (.box (.not a)))
    , .iff (.box a) (.not (.diamond (.not a)))
    , .implies (.box (.and a b)) (.box a)
    , .implies (.and (.box a) (.box b)) (.box (.and a b)) ]
    (by simp)

instance : Arbitrary ValidFormula := ⟨ValidFormula.mk <$> genValidFormula⟩
instance : Shrinkable ValidFormula where shrink _ := []

/-- Formulas valid in K4 (transitive frames) but NOT in K: instances of
axiom 4. Mirrors `Arb4Formula`/`gen4Formula`. -/
structure FourFormula where
  getFormula : Formula
  deriving Repr

def gen4Formula : Gen Formula := do
  let a ← Gen.resize (fun _ => 2) (Arbitrary.arbitrary : Gen Formula)
  Gen.elements
    [ .implies (.box a) (.box (.box a))
    , .implies (.diamond (.diamond a)) (.diamond a)
    , .implies (.box a) (.box (.box (.box a)))
    , .implies (.diamond (.diamond (.diamond a))) (.diamond a) ]
    (by simp)

instance : Arbitrary FourFormula := ⟨FourFormula.mk <$> gen4Formula⟩
instance : Shrinkable FourFormula where shrink _ := []

/-- Formulas valid in S4 (reflexive + transitive): T, 4, and the S4
modality-collapse schemes. Mirrors `ArbS4Formula`/`genS4Formula`. -/
structure S4Formula where
  getFormula : Formula
  deriving Repr

def genS4Formula : Gen Formula := do
  let a ← Gen.resize (fun _ => 2) (Arbitrary.arbitrary : Gen Formula)
  Gen.elements
    [ .implies (.box a) a
    , .implies a (.diamond a)
    , .implies (.box a) (.box (.box a))
    , .implies (.diamond (.diamond a)) (.diamond a)
    , .iff (.box (.box a)) (.box a)
    , .iff (.diamond (.diamond a)) (.diamond a)
    , .implies (.box a) (.diamond a)
    , .iff (.box (.diamond (.box (.diamond a)))) (.box (.diamond a)) ]
    (by simp)

instance : Arbitrary S4Formula := ⟨S4Formula.mk <$> genS4Formula⟩
instance : Shrinkable S4Formula where shrink _ := []

/-- Formulas valid in S5 (equivalence frames: reflexive + transitive +
euclidean): axiom 5, T, 4, B, and the S5 modality-collapse schemes.
Mirrors `ArbS5Formula`/`genS5Formula`. -/
structure S5Formula where
  getFormula : Formula
  deriving Repr

def genS5Formula : Gen Formula := do
  let a ← Gen.resize (fun _ => 2) (Arbitrary.arbitrary : Gen Formula)
  Gen.elements
    [ .implies (.diamond a) (.box (.diamond a))
    , .implies (.diamond (.box a)) (.box a)
    , .implies (.box a) a
    , .implies (.box a) (.box (.box a))
    , .implies a (.box (.diamond a))
    , .implies (.diamond (.box a)) a
    , .iff (.box (.diamond a)) (.diamond a)
    , .iff (.diamond (.box a)) (.box a)
    , .iff (.diamond (.diamond a)) (.diamond a)
    , .iff (.box (.box a)) (.box a) ]
    (by simp)

instance : Arbitrary S5Formula := ⟨S5Formula.mk <$> genS5Formula⟩
instance : Shrinkable S5Formula where shrink _ := []

/-- Propositional-fragment-only formulas (no Box/Diamond), safe to use as
the operand of `tau`/`conditionalize`. Mirrors `ArbPropFormula`/
`genPropFormula`. Used directly (not through an `Arbitrary` wrapper): the
`lake exe slowtests` `Gamen.RankingTheory` properties draw it through
`checkGuarded`, sized exactly like Haskell's `sized genPropFormula` (no
cap) rather than the `Arbitrary Formula` instance's `min n 12`. -/
partial def genPropFormula : Nat → Gen Formula
  | 0 => Gen.frequency (pure .bot) [(1, pure .bot), (4, genAtom)]
  | n + 1 =>
    let h := (n + 1) / 2
    Gen.frequency (pure .bot) [
      (1, pure .bot), (4, genAtom),
      (3, .not <$> genPropFormula n),
      (3, .and <$> genPropFormula h <*> genPropFormula h),
      (2, .or <$> genPropFormula h <*> genPropFormula h),
      (2, .implies <$> genPropFormula h <*> genPropFormula h)]
where
  genAtom : Gen Formula := do
    let ⟨i, _⟩ ← Gen.choose Nat 0 2 (by omega)
    return .atom (propAtomNames.getD i "p")

/-- True when φ is neither a tautology nor a contradiction in `m`.
Mirrors `isContingent`, but stays in `Except`: for the propositional
fragment `genPropFormula` generates, `truthSet` can never actually error,
so a `.error` here is a real bug, not a legitimate "not contingent"
reading. Callers must not collapse it to `false` themselves — that would
let an error masquerade as the (equally vacuous-looking) "not contingent"
case and silently pass whichever answer the property expected. -/
def isContingentK (m : KappaModel) (f : Formula) : Except String Bool := do
  let t ← truthSet m f
  return !t.isEmpty && t.toList != m.kWorlds.toList

/-! ### QuickCheck's `==>`, done by hand

`Testable`'s own guard support (`decGuardTestable`, used by the `NamedBinder
∀ h : p, …` shape) does not reproduce QuickCheck's `==>`: it retries a
*single* sample slot up to `Configuration.numRetries` (10) times, and once
`Configuration.numInst` slots have gone by — whether or not any of them
ever satisfied the guard — the run ends, reporting whatever it has (often
`.gaveUp`, occasionally a lone `.success` if one slot got lucky). It never
keeps drawing until it has collected `numInst` *real* (guard-true) checks,
which is what QuickCheck's `maxSuccess` promises and what `run`'s
`numInst` parameter (`Tests/Main.lean`) was actually claiming to deliver.
Concretely: making `genKripkeModel` throw showed every property with an
inner `m : Model` binder going green, because generation failure and
guard failure both collapse to the same `.gaveUp` here — and separately,
even under a correct generator, direct measurement found several of these
properties performing far fewer real checks than their stated count (as
few as 29 of 300) while still reporting a pass.

`checkGuarded` restores both guarantees for the seven properties that use
`==>` (`test/Properties.hs`'s `unsatisfiable ⇒ …`, `satisfied in some
model ⇒ …`, `provable entailment ⇒ …`, `S5 unsatisfiable ⇒ …`, `extracted
countermodel …`'s two discard points, and `Gamen.RankingTheory`'s two
`isContingent ⇒ …` properties — all seven now live in `Tests/SlowMain.lean`,
`lake exe slowtests`, because running them at Haskell's real sizes and
discard caps takes on the order of Haskell's own ~460s for this same set):
draw samples directly through `Gen`, outside the `Testable`/`NamedBinder`
machinery, counting a real check on every guard-true draw and a discard
otherwise. The run ends when it has `target` real checks (pass), when
discards reach `maxDiscardRatio * target` (QuickCheck's own formula; its
default ratio is 10, and `Gamen.RankingTheory`'s two properties use
Haskell's `modifyMaxDiscardRatio 20`), or immediately on a real check that
fails or on any `Except` error from the generator, the guard, or the check
itself — none of those is a discard, all are a definite failure. -/

/-- Grow the sample size with the *real-check* count, capped at
Plausible's own default `Configuration.maxSize` (100) — QuickCheck's own
size formula is `numSuccessTests * maxSize / maxSuccessTests` (real checks
only), which is why a long discard streak in Haskell stays cheap: size
only grows once a check actually counts. Keying this to `checks +
discards` instead (attempts) was tried first and made every discard after
the first ~100 attempts draw a near-maximum-size sample regardless of how
many of those attempts were discards, which is what made the discard-cap
case of these properties (up to `maxDiscardRatio * target` discards)
minutes slower than it needed to be. -/
private def guardedSampleSize (target checks : Nat) : Nat :=
  min 100 (checks * 100 / target + 1)

private def checkGuardedLoop {α : Type} (name : String) (target maxDiscardRatio : Nat)
    (gen : Nat → Gen α) (guard check : α → Except String Bool) :
    Nat → Nat → Nat → IO (Nat × Bool)
  | 0, checks, _ => do
      IO.println s!"    {name}: out of fuel ({checks}/{target} real checks)"
      return (checks, false)
  | fuel + 1, checks, discards => do
      if checks ≥ target then return (checks, true)
      else if discards ≥ maxDiscardRatio * target then
        IO.println s!"    {name}: gave up after {discards} discards ({checks}/{target} real checks)"
        return (checks, false)
      else
        let size := guardedSampleSize target checks
        match ← (try pure (some (← Gen.run (gen size) 0)) catch _ => pure none) with
        | none =>
            IO.println s!"    {name}: generator failed ({checks}/{target} real checks so far)"
            return (checks, false)
        | some x =>
          match guard x with
          | .error e =>
              IO.println s!"    {name}: guard errored: {e} ({checks}/{target} real checks so far)"
              return (checks, false)
          | .ok false => checkGuardedLoop name target maxDiscardRatio gen guard check fuel checks (discards + 1)
          | .ok true =>
            match check x with
            | .ok true => checkGuardedLoop name target maxDiscardRatio gen guard check fuel (checks + 1) discards
            | .ok false =>
                IO.println s!"    {name}: counterexample on real check {checks + 1}"
                return (checks + 1, false)
            | .error e =>
                IO.println s!"    {name}: check errored on real check {checks + 1}: {e}"
                return (checks + 1, false)

/-- Fuel: enough rounds for `target` real checks plus the full discard
budget, so the loop only runs out of fuel if both its own stopping
conditions somehow failed to fire — an internal-consistency backstop, not
a real limit. -/
def checkGuarded {α : Type} (name : String) (target maxDiscardRatio : Nat) (gen : Nat → Gen α)
    (guard check : α → Except String Bool) : IO (Nat × Bool) :=
  checkGuardedLoop name target maxDiscardRatio gen guard check (target + maxDiscardRatio * target + 1) 0 0

/-- The countermodels `extractCountermodel` recovers from every open,
saturated branch of the tableau on `{1 T f}` — `[]` if the tableau closes
or exhausts its budget, matching Haskell's `case … of TOpen branches -> …;
_ -> discard` (a discard, in `checkGuarded`, is exactly the guard `!=
[]` reading `false`). -/
def extractedModelsFor (f : Formula) : List Model :=
  match buildTableau systemK defaultMaxSteps [pfTrue .root f] with
  | .stillOpen branches => branches.filterMap fun b => (extractCountermodel systemK b).toOption
  | _ => []

/-! ## Cross-checks of the decision procedures (Not in gamen-hs)

Lean-only; no gamen-hs counterpart. Prompted by Gamen.jl issue #20: the
prefixed tableau and the G3DS prover are decision procedures, and each
answer they give can be checked against an independent semantics.

* **Tableau vs. enumeration** (`crossCheckSystem`), for K, KT, KD, KTB
  (`systemKB`), K4, S4, S5. Random formulas (atoms drawn from {p, q} or
  {p, q, r}, modal depth ≤ 2, from a printed seed). For each formula:
  - *proved* ⇒ no model on a frame of at most `maxWorlds` worlds that
    satisfies the system's frame condition (`Gamen.FrameProperties`)
    falsifies it at any world (`Gamen.Semantics.satisfies`);
  - *not proved* ⇒ every open branch yields a model from
    `extractCountermodel` whose frame satisfies the condition and which
    falsifies the formula at the root prefix `1`, both re-checked here
    with `FrameProperties`/`satisfies` rather than trusted;
  - if that extracted model has at most `maxWorlds` worlds, the
    enumeration must have found a countermodel too (a check on the
    enumerator itself).

  **What the bound guarantees.** Frames are enumerated up to isomorphism
  (a relation mask is kept only if no permutation of the worlds gives a
  smaller mask), then filtered by the frame condition; valuations range
  over the formula's own atoms only, all `2^(atoms·worlds)` of them, and
  every world is tried. Since truth is invariant under isomorphism, this
  covers *every* model of at most `maxWorlds` worlds on a frame of the
  class. So a wrong "proved" is caught exactly when the formula has a
  countermodel of at most `maxWorlds` worlds in the class; one whose
  smallest countermodel is larger slips through the soundness check.
  Every "not proved" answer, by contrast, is certified outright by its
  re-checked countermodel, whatever its size. Budget exhaustion
  (`exhausted`) is neither a pass nor a fail for a single formula; a run
  tolerates it for at most 5% of its draws, and requires at least one
  proved and one refuted formula so neither direction passes vacuously.

  The verdict check has no exceptions. The extraction check excludes
  exactly two known gamen-hs bugs, each by its precise shape
  (`crossExtractOne`): gamen-hs#38 (KD countermodels are not serial) and
  gamen-hs#39 (K/KD/K4 extraction fails on a branch with a blocked
  prefix). Each excluded refutation must still be certified by the
  enumeration.

* **G3DS** (`dsCrossCheck`): random `L_n` formulas (1 or 2 agents, atoms
  p, q, modal depth ≤ 2, all of ¬ ∧ ∨ → ↔ □ ◇ [i] ⟨i⟩ ⊗ ⊖). *Refuted* ⇒
  `extractDSModel`'s model passes `isValidDSFrame`, has a choice relation
  for every agent of the formula, contains the root `w0`, and falsifies
  the original (not NNF) formula there under `dsSatisfies`. *Proved* ⇒
  the formula holds at every world of every model in a pool of random
  valid DS models (`genDSModel`, valid by construction and re-checked
  with `isValidDSFrame`). The pool is a sample, not an enumeration: it
  can miss a wrong "proved". The extraction check excludes exactly the
  documented IoaOp deferral: a frame that fails C2 and nothing else
  (`isIoaOpDeferral`, on the frame rebuilt by `dsStabilityModel`).
-/

/-- Run a `Gen` deterministically from `seed` at sample size `size`. A
generator failure is an error, never a default. -/
def runGenSeeded {α : Type} (g : Gen α) (seed size : Nat) : Except String α :=
  match (((runRandWith seed g).run ⟨size⟩ : Except GenError α)) with
  | .ok a => .ok a
  | .error (.genError m) => .error s!"generator failed: {m}"

/-- A uniform draw from `0 … k-1` (`k ≥ 1`; `k = 0` behaves as `k = 1`). -/
def pick (k : Nat) : Gen Nat := do
  let ⟨i, _⟩ ← Gen.choose Nat 0 (k - 1) (by omega)
  return i

/-- An atom from `atoms`, or `⊥` with probability `1/(|atoms|+1)`. -/
def genXLeaf (atoms : List String) : Gen Formula := do
  let i ← pick (atoms.length + 1)
  return if i == atoms.length then .bot else .atom (atoms.getD i "p")

/-- Random Kripke-fragment formula over `atoms`, modal depth ≤ `md`,
connective nesting ≤ the last argument. Leaves weigh 3, each unary or
binary connective 1, □ and ◇ 2 each (only while `md > 0`). -/
def genXFormula (atoms : List String) (md : Nat) : Nat → Gen Formula
  | 0 => genXLeaf atoms
  | n + 1 => do
    let c ← pick (if md > 0 then 12 else 8)
    match c with
    | 0 | 1 | 2 => genXLeaf atoms
    | 3 => .not <$> genXFormula atoms md n
    | 4 => .and <$> genXFormula atoms md n <*> genXFormula atoms md n
    | 5 => .or <$> genXFormula atoms md n <*> genXFormula atoms md n
    | 6 => .implies <$> genXFormula atoms md n <*> genXFormula atoms md n
    | 7 => .iff <$> genXFormula atoms md n <*> genXFormula atoms md n
    | 8 | 9 => .box <$> genXFormula atoms (md - 1) n
    | _ => .diamond <$> genXFormula atoms (md - 1) n

/-- One cross-check sample: 2 or 3 atoms, modal depth ≤ 2, nesting ≤ 4. -/
def genXSample : Gen Formula := do
  let k ← pick 2
  genXFormula (if k == 0 then ["p", "q"] else ["p", "q", "r"]) 2 4

/-- The modal depth of a formula (□/◇ and the agent operators count). -/
def modalDepth : Formula → Nat
  | .not f => modalDepth f
  | .and l r | .or l r | .implies l r | .iff l r => max (modalDepth l) (modalDepth r)
  | .box f | .diamond f | .stit _ f | .choiceDiamond _ f | .ought _ f | .permitted _ f =>
      modalDepth f + 1
  | _ => 0

/-- All permutations of a list. -/
def permutationsOf : List Nat → List (List Nat)
  | [] => [[]]
  | x :: xs => (permutationsOf xs).flatMap fun p =>
      (List.range (p.length + 1)).map fun i => p.take i ++ x :: p.drop i

/-- Rename the worlds of an `n`-world relation mask (bit `i*n+j` is the
edge `(wᵢ, wⱼ)`) by the permutation `π`. -/
def permuteMask (n : Nat) (π : List Nat) (mask : Nat) : Nat := Id.run do
  let mut out := 0
  for i in List.range n do
    for j in List.range n do
      if mask.testBit (i * n + j) then
        out := out ||| (1 <<< (π.getD i 0 * n + π.getD j 0))
  return out

/-- One representative per isomorphism class of relations on `n` worlds:
the masks no world permutation makes smaller. -/
def canonicalMasks (n : Nat) : List Nat :=
  let ps := permutationsOf (List.range n)
  (List.range (2 ^ (n * n))).filter fun m => ps.all fun π => permuteMask n π m ≥ m

def xWorldName (i : Nat) : World := s!"w{i}"

def frameOfMask (n mask : Nat) : Except String Frame :=
  let ws := (List.range n).map xWorldName
  let edges := (List.range n).flatMap fun i => (List.range n).filterMap fun j =>
    if mask.testBit (i * n + j) then some (xWorldName i, xWorldName j) else none
  mkFrame ws edges

/-- Every frame of 1 … `maxWorlds` worlds satisfying `cond`, up to
isomorphism. -/
def enumFrames (cond : Frame → Bool) (maxWorlds : Nat) : Except String (List Frame) :=
  (List.range maxWorlds).flatMapM fun k => do
    let n := k + 1
    let frs ← (canonicalMasks n).mapM (frameOfMask n)
    return frs.filter cond

def describeModel (m : Model) : String :=
  let r := (edgesOf m).toList
  let v := m.valuation.toList.map fun (a, ws) => (a.name, ws.toList)
  s!"W={m.frame.worlds.toList} R={r} V={v}"

/-- A model among `frames` × all valuations of `φ`'s atoms, and a world,
where `φ` is false; `none` if there is none. `satisfies` errors
propagate. -/
def smallCountermodel (frames : List Frame) (φ : Formula) :
    Except String (Option (Model × World)) := do
  let as := φ.atoms.toList.map (·.name)
  for fr in frames do
    let ws := fr.worlds.toList
    let n := ws.length
    for v in List.range (2 ^ (as.length * n)) do
      let vals := as.zipIdx.map fun (a, i) =>
        (a, ws.zipIdx.filterMap fun (w, j) => if v.testBit (i * n + j) then some w else none)
      let m := mkModel fr vals
      for w in ws do
        if !(← satisfies m w φ) then return some (m, w)
  return none

/-- A tableau system with its frame condition, checked with
`Gamen.FrameProperties` (B&D Table 6.4 pairs each system with its frame
class). -/
structure XSystem where
  sys : System
  cond : Frame → Bool
  condName : String

def xSystems : List XSystem :=
  [ ⟨systemK, fun _ => true, "any"⟩,
    ⟨systemKT, isReflexive, "reflexive"⟩,
    ⟨systemKD, isSerial, "serial"⟩,
    ⟨systemKB, fun f => isReflexive f && isSymmetric f, "reflexive+symmetric"⟩,
    ⟨systemK4, isTransitive, "transitive"⟩,
    ⟨systemS4, fun f => isReflexive f && isTransitive f, "reflexive+transitive"⟩,
    ⟨systemS5, isEquivalenceRelation, "equivalence"⟩ ]

structure XStats where
  proved : Nat := 0
  refuted : Nat := 0
  unknown : Nat := 0
  /-- Refuted, and the enumeration also found a countermodel. -/
  refutedSmall : Nat := 0
  /-- Extracted countermodels re-checked and verified (one per open branch). -/
  verified : Nat := 0
  /-- Excluded: a KD model that is correct except for seriality (gamen-hs#38). -/
  knownNonSerial : Nat := 0
  /-- Excluded: "branch not saturated" on a branch with a blocked prefix
  (gamen-hs#39). -/
  knownBlocked : Nat := 0

/-- The **verdict** cross-check for one formula, with no exceptions:
*proved* ⇒ no countermodel among `frames`; counts refuted/unknown. -/
def crossVerdictOne (xs : XSystem) (frames : List Frame) (steps : Nat)
    (φ : Formula) (st : XStats) : Except String XStats := do
  let tag := s!"{xs.sys.name}, φ = {φ} ({repr φ})"
  let small ← (smallCountermodel frames φ).mapError (s!"{tag}: satisfies errored: " ++ ·)
  match buildTableau xs.sys steps [pfFalse .root φ] with
  | .closed =>
    if let some (m, w) := small then
      throw s!"{tag}: tableau proves φ, but φ is false at {w} in {describeModel m}"
    return { st with proved := st.proved + 1 }
  | .stillOpen _ =>
    return { st with refuted := st.refuted + 1,
                     refutedSmall := st.refutedSmall + (if small.isSome then 1 else 0) }
  | .exhausted _ => return { st with unknown := st.unknown + 1 }

/-- Is this `extractCountermodel` failure the known gamen-hs#39 class?
Exactly: system K, KD or K4; the error is the verification failure
("branch not saturated"); and the branch has a blocked prefix (its
unwitnessed ◇/□F obligations are what the extracted model then fails). -/
def isKnownBlockedFailure (sys : System) (b : Branch) (e : String) : Bool :=
  ["K", "KD", "K4"].contains sys.name
    && (e.splitOn "branch not saturated").length > 1
    && b.prefixes.toList.any (b.isBlocked ·)

/-- The **extraction** cross-check for one formula (refuted formulas only):
every open branch's `extractCountermodel` model must contain the root,
falsify φ there (`satisfies`), and lie in the frame class
(`FrameProperties`); and if it has at most `maxWorlds` worlds the
enumeration must have found a countermodel too. Two known gamen-hs bugs
are excluded, each by its exact shape, and counted; an excluded
refutation must still be certified by the enumeration:
* KD, a model that passes every check except seriality (gamen-hs#38);
* `isKnownBlockedFailure` (gamen-hs#39).
Anything else fails. -/
def crossExtractOne (xs : XSystem) (frames : List Frame) (maxWorlds steps : Nat)
    (φ : Formula) (st : XStats) : Except String XStats := do
  let tag := s!"{xs.sys.name}, φ = {φ} ({repr φ})"
  match buildTableau xs.sys steps [pfFalse .root φ] with
  | .closed | .exhausted _ => return st
  | .stillOpen bs =>
    if bs.isEmpty then throw s!"{tag}: open tableau with no open branch"
    let small ← (smallCountermodel frames φ).mapError (s!"{tag}: satisfies errored: " ++ ·)
    let certified : Except String Unit :=
      if small.isSome then pure ()
      else throw s!"{tag}: excluded refutation not certified by a ≤ {maxWorlds}-world countermodel"
    let rootW := toString Prefix.root
    let mut st := { st with refuted := st.refuted + 1 }
    for b in bs do
      match extractCountermodel xs.sys b with
      | .error e =>
        if isKnownBlockedFailure xs.sys b e then
          certified
          st := { st with knownBlocked := st.knownBlocked + 1 }
        else throw s!"{tag}: extraction failed: {e}"
      | .ok m =>
        unless m.frame.worlds.contains rootW do
          throw s!"{tag}: extracted model lacks the root world: {describeModel m}"
        match satisfies m rootW φ with
        | .ok false => pure ()
        | .ok true => throw s!"{tag}: extracted model does not falsify φ at root: {describeModel m}"
        | .error e => throw s!"{tag}: satisfies errored on extracted model: {e}"
        if m.frame.worlds.size ≤ maxWorlds && small.isNone then
          throw s!"{tag}: enumeration found no countermodel of ≤ {maxWorlds} worlds, \
            but extraction found {describeModel m}"
        if xs.cond m.frame then
          st := { st with verified := st.verified + 1 }
        else if xs.sys.name == "KD" && !isSerial m.frame then
          certified
          st := { st with knownNonSerial := st.knownNonSerial + 1 }
        else throw s!"{tag}: extracted frame is not {xs.condName}: {describeModel m}"
    return st

/-- `count` random formulas from `seed`, modal depth checked. -/
def crossSamples (seed count : Nat) : Except String (List Formula) := do
  let fs ← runGenSeeded ((List.range count).mapM fun _ => genXSample) seed 0
  if let some φ := fs.find? (modalDepth · > 2) then
    throw s!"generator produced modal depth > 2: {φ}"
  return fs

/-- Verdict cross-check of `count` random formulas from `seed` against
every frame of the class with at most `maxWorlds` worlds. Errors carry
the failing formula (as text and as a `repr` for a regression case). -/
def crossCheckSystem (xs : XSystem) (seed count maxWorlds steps : Nat) :
    Except String XStats := do
  let frames ← enumFrames xs.cond maxWorlds
  (← crossSamples seed count).foldlM (fun st φ => crossVerdictOne xs frames steps φ st) {}

/-- Extraction cross-check of the same draws as `crossCheckSystem`. -/
def crossExtractSystem (xs : XSystem) (seed count maxWorlds steps : Nat) :
    Except String XStats := do
  let frames ← enumFrames xs.cond maxWorlds
  (← crossSamples seed count).foldlM
    (fun st φ => crossExtractOne xs frames maxWorlds steps φ st) {}

/-- A passing verdict run: no error, both directions exercised at least
once, and at most 5% of draws left `unknown` by budget exhaustion.
Exhaustion is never a wrong answer, so it is tolerated and counted rather
than failed; the cap keeps a prover that gives up on everything from
passing. Known exhaustion: `◇((□q ∧ □⊥) ∨ (p ∧ ⊥))` in KT/KTB/S4/S5,
pinned in `Tests/Main.lean`'s `crossCheckCases`. -/
def crossCheckVerdict (r : Except String XStats) : Bool × String :=
  match r with
  | .ok st =>
    (st.unknown * 20 ≤ st.proved + st.refuted + st.unknown && st.proved > 0 && st.refuted > 0,
     s!"proved {st.proved}, refuted {st.refuted} ({st.refutedSmall} with a ≤ N-world \
       countermodel), unknown {st.unknown}")
  | .error e => (false, s!"FAILED: {e}")

/-- A passing extraction run: no error, and at least one model checked
(for KD every model is a #38 exclusion, still checked for everything but
seriality). -/
def crossExtractVerdict (r : Except String XStats) : Bool × String :=
  match r with
  | .ok st =>
    (st.verified + st.knownNonSerial > 0,
     s!"refuted {st.refuted}; extracted models verified {st.verified}, excluded #38 \
       {st.knownNonSerial}, excluded #39 {st.knownBlocked}")
  | .error e => (false, s!"FAILED: {e}")

/-! ### G3DS cross-checks -/

/-- A random `L_n` formula over atoms p, q and `agents`, modal depth ≤
`md`, nesting ≤ the last argument. -/
def genDSXFormula (agents : List String) (md : Nat) : Nat → Gen Formula
  | 0 => genXLeaf ["p", "q"]
  | n + 1 => do
    let c ← pick (if md > 0 then 14 else 8)
    let ag ← pick agents.length
    let a := agents.getD ag "1"
    match c with
    | 0 | 1 | 2 => genXLeaf ["p", "q"]
    | 3 => .not <$> genDSXFormula agents md n
    | 4 => .and <$> genDSXFormula agents md n <*> genDSXFormula agents md n
    | 5 => .or <$> genDSXFormula agents md n <*> genDSXFormula agents md n
    | 6 => .implies <$> genDSXFormula agents md n <*> genDSXFormula agents md n
    | 7 => .iff <$> genDSXFormula agents md n <*> genDSXFormula agents md n
    | 8 => .box <$> genDSXFormula agents (md - 1) n
    | 9 => .diamond <$> genDSXFormula agents (md - 1) n
    | 10 => .stit a <$> genDSXFormula agents (md - 1) n
    | 11 => .choiceDiamond a <$> genDSXFormula agents (md - 1) n
    | 12 => .ought a <$> genDSXFormula agents (md - 1) n
    | _ => .permitted a <$> genDSXFormula agents (md - 1) n

/-- A random DS model over `agents`, valid by construction: each agent
gets 1 or 2 choice cells; every *profile* (one cell per agent) gets 1 or
2 worlds, so any selection of cells intersects (C2); each agent's
relation is "same cell" (C1); each agent's ideal set is a non-empty union
of its cells (D1–D3). Up to 8 worlds for 2 agents. -/
def genDSModel (agents : List String) : Gen DSModel := do
  let cells ← agents.mapM fun _ => (· + 1) <$> pick 2
  let profiles := sections (cells.map List.range)
  let perProfile ← profiles.mapM fun pr => do
    let k ← pick 2
    pure (List.replicate (k + 1) pr)
  let worlds := perProfile.flatten.zipIdx.map fun (pr, i) => (s!"v{i}", pr)
  let rels := agents.zipIdx.map fun (a, ai) =>
    (a, worlds.flatMap fun (w, pw) => worlds.filterMap fun (v, pv) =>
      if pw.getD ai 0 == pv.getD ai 0 then some (w, v) else none)
  let ideals ← agents.zipIdx.mapM fun (a, ai) => do
    let c := cells.getD ai 1
    let mask := (← pick (2 ^ c - 1)) + 1
    pure (a, worlds.filterMap fun (w, pw) =>
      if mask.testBit (pw.getD ai 0) then some w else none)
  let vals ← ["p", "q"].mapM fun at_ => do
    let vs ← worlds.filterM fun _ => (Arbitrary.arbitrary : Gen Bool)
    pure (at_, vs.map (·.1))
  return mkDSModel (mkDSFrame (worlds.map (·.1)) rels ideals) vals

/-- The stability model of Definition 20 (Lyon & van Berkel 2024,
pp. 858–859), built the same way as `extractDSModel` but *without* its
verification, so a test can see the frame `extractDSModel` rejected.
`dsExtractOne` checks that it equals `extractDSModel`'s result whenever
extraction succeeds, so this copy cannot silently drift. -/
def dsStabilityModel (gt : GenTree) (s : Sequent) : Except String DSModel := do
  let unblockedSet ← unblockedLabels gt s
  let lw : Label → World := toString
  let worlds : Std.TreeSet World := unblockedSet.foldl (fun acc w => acc.insert (lw w)) ∅
  let agentSet := sequentAgents s
  let choicePairs (a : String) : List (Label × Label) :=
    s.rels.toList.filterMap fun
      | .choice b w u => if b == a then some (w, u) else none
      | .ideal _ _ => none
  let relations ← agentSet.toList.foldlM (fun acc a => do
    let clauseI := (choicePairs a).filter fun (w, u) =>
      unblockedSet.contains w && unblockedSet.contains u
    let clauseII ← (choicePairs a).flatMapM fun (w, v) => do
      if !unblockedSet.contains w then return []
      let anc ← ancestors v gt
      return anc.filterMap fun u =>
        if unblockedSet.contains u && isDirectlyBlockedBy v u gt s then some (w, u) else none
    let base := Std.TreeSet.ofList clauseI lexOrd.compare ∪ Std.TreeSet.ofList clauseII lexOrd.compare
    let pairs ← euclideanClose unblockedSet base
    let start : Std.TreeMap World (Std.TreeSet World) :=
      unblockedSet.foldl (fun acc w => acc.insert (lw w) ∅) ∅
    let rel : Std.TreeMap World (Std.TreeSet World) := pairs.foldl
      (fun (acc : Std.TreeMap World (Std.TreeSet World)) (w, u) =>
        acc.alter (lw w) fun o => some ((o.getD ∅).insert (lw u))) start
    return acc.insert a rel)
    (∅ : Std.TreeMap String (Std.TreeMap World (Std.TreeSet World)))
  let ideals : Std.TreeMap String (Std.TreeSet World) :=
    agentSet.foldl (fun acc a =>
      acc.insert a (unblockedSet.foldl (fun ws w =>
        if hasRel (.ideal a w) s then ws.insert (lw w) else ws) ∅)) ∅
  let valuation : Std.TreeMap Atom (Std.TreeSet World) :=
    s.gamma.foldl (fun acc lf =>
      match lf.lfFormula with
      | .not (.atomF a) =>
        if unblockedSet.contains lf.lfLabel then
          acc.alter a fun
            | none => some {lw lf.lfLabel}
            | some ws => some (ws.insert (lw lf.lfLabel))
        else acc
      | _ => acc) ∅
  return { dsFrame := { dsWorlds := worlds, dsRelations := relations, dsIdeals := ideals }
           dsValuation := valuation }

/-- The documented IoaOp deferral (`CounterModel.lean`'s `extractDSModel`
docstring; gamen-hs `CounterModel.hs` 66–72, `Prove.hs` 21), exactly: at
least two agents, and the stability frame fails C2 while C1, C3 (k = 0)
and D1–D3 hold. -/
def isIoaOpDeferral (fr : DSFrame) : Bool :=
  fr.dsRelations.size ≥ 2 && checkDS_C1 fr && !checkDS_C2 fr && checkDS_C3 0 fr
    && checkDS_D1 fr && checkDS_D2 fr && checkDS_D3 fr

structure DSXStats where
  proved : Nat := 0
  refuted : Nat := 0
  unknown : Nat := 0
  stuck : Nat := 0
  verified : Nat := 0
  /-- Excluded: extraction rejected a frame failing only C2 (IoaOp deferral). -/
  knownC2 : Nat := 0

/-- **Verdict** check for one `L_n` formula: *proved* ⇒ true at every
world of every pool model. -/
def dsVerdictOne (models : List DSModel) (steps : Nat) (φ : Formula) (st : DSXStats) :
    Except String DSXStats := do
  let tag := s!"φ = {φ} ({repr φ})"
  match ← (proveFormula 0 steps φ).mapError (s!"{tag}: proveFormula errored: " ++ ·) with
  | .proved =>
    for m in models do
      for w in m.dsFrame.dsWorlds.toList do
        match dsSatisfies m w φ with
        | .ok true => pure ()
        | .ok false => throw s!"{tag}: proved, but false at {w} in {repr m}"
        | .error e => throw s!"{tag}: dsSatisfies errored: {e}"
    return { st with proved := st.proved + 1 }
  | .refuted _ _ => return { st with refuted := st.refuted + 1 }
  | .maxStepsExceeded _ _ => return { st with unknown := st.unknown + 1 }
  | .stuck _ _ => return { st with stuck := st.stuck + 1 }

/-- **Extraction** check for one refuted `L_n` formula: `extractDSModel`'s
model equals `dsStabilityModel`, passes `isValidDSFrame`, has a choice
relation for every agent of φ, contains `w0`, and falsifies the original
(not NNF) φ there under `dsSatisfies`. Excluded, exactly: extraction's
"not a valid DS frame" error on a stability frame with `isIoaOpDeferral`.
Anything else fails. -/
def dsExtractOne (steps : Nat) (φ : Formula) (st : DSXStats) : Except String DSXStats := do
  let tag := s!"φ = {φ} ({repr φ})"
  match ← (proveFormula 0 steps φ).mapError (s!"{tag}: proveFormula errored: " ++ ·) with
  | .refuted gt s =>
    let st := { st with refuted := st.refuted + 1 }
    let sm ← (dsStabilityModel gt s).mapError (s!"{tag}: stability model errored: " ++ ·)
    match extractDSModel gt s with
    | .error e =>
      if (e.splitOn "not a valid DS frame").length > 1 && isIoaOpDeferral sm.dsFrame then
        return { st with knownC2 := st.knownC2 + 1 }
      throw s!"{tag}: extraction failed: {e}"
    | .ok m =>
      let rootW := toString label0
      unless m == sm do throw s!"{tag}: extractDSModel differs from dsStabilityModel"
      unless isValidDSFrame m.dsFrame do throw s!"{tag}: extracted frame not a valid DS frame"
      for a in (formulaAgents φ).toList do
        unless m.dsFrame.dsRelations.contains a do
          throw s!"{tag}: extracted frame has no choice relation for agent {a}"
      unless m.dsFrame.dsWorlds.contains rootW do throw s!"{tag}: extracted model lacks {rootW}"
      match dsSatisfies m rootW φ with
      | .ok false => return { st with verified := st.verified + 1 }
      | .ok true => throw s!"{tag}: extracted model does not falsify φ at {rootW}: {repr m}"
      | .error e => throw s!"{tag}: dsSatisfies errored on extracted model: {e}"
  | _ => return st

def dsSamples (agents : List String) (seed count : Nat) : Except String (List Formula) := do
  let fs ← runGenSeeded ((List.range count).mapM fun _ => genDSXFormula agents 2 4) seed 0
  if let some φ := fs.find? (modalDepth · > 2) then
    throw s!"generator produced modal depth > 2: {φ}"
  return fs

/-- Verdict check of `count` random `L_n` formulas over `agents` from
`seed`, against a pool of `nModels` random valid DS models from
`seed + 1`. -/
def dsCrossCheck (agents : List String) (seed count nModels steps : Nat) :
    Except String DSXStats := do
  let fs ← dsSamples agents seed count
  let ms ← runGenSeeded ((List.range nModels).mapM fun _ => genDSModel agents) (seed + 1) 0
  if ms.any (!isValidDSFrame ·.dsFrame) then
    throw "genDSModel produced an invalid DS frame (generator bug)"
  fs.foldlM (fun st φ => dsVerdictOne ms steps φ st) {}

/-- Extraction check of the same draws as `dsCrossCheck`. -/
def dsExtractCheck (agents : List String) (seed count steps : Nat) : Except String DSXStats := do
  (← dsSamples agents seed count).foldlM (fun st φ => dsExtractOne steps φ st) {}

/-- As `crossCheckVerdict`; a `stuck` result (the schedule and the
saturation predicates disagree) always fails. -/
def dsCrossCheckVerdict (r : Except String DSXStats) : Bool × String :=
  match r with
  | .ok st => (st.unknown * 20 ≤ st.proved + st.refuted + st.unknown + st.stuck
      && st.stuck == 0 && st.proved > 0 && st.refuted > 0,
      s!"proved {st.proved}, refuted {st.refuted}, budget {st.unknown}, stuck {st.stuck}")
  | .error e => (false, s!"FAILED: {e}")

def dsExtractVerdict (r : Except String DSXStats) : Bool × String :=
  match r with
  | .ok st => (st.verified > 0,
      s!"refuted {st.refuted}; extracted models verified {st.verified}, excluded C2/IoaOp {st.knownC2}")
  | .error e => (false, s!"FAILED: {e}")

/-- What `extractCountermodel` does on each open branch of `{1 F φ}`, as
a label: `verified`, `non-serial (#38)`, `blocked (#39)`, or a failure
label. `none` if the tableau does not stay open. For pinning the known
gamen-hs bugs in regression cases. -/
def extractionShapes (xs : XSystem) (φ : Formula) : Option (List String) :=
  match buildTableau xs.sys defaultMaxSteps [pfFalse .root φ] with
  | .stillOpen bs => some (bs.map fun b =>
      match extractCountermodel xs.sys b with
      | .ok m =>
        if !(satisfies m (toString Prefix.root) φ matches .ok false) then "not falsified"
        else if xs.cond m.frame then "verified"
        else if xs.sys.name == "KD" && !isSerial m.frame then "non-serial (#38)"
        else "wrong frame class"
      | .error e => if isKnownBlockedFailure xs.sys b e then "blocked (#39)" else s!"error: {e}")
  | _ => none
