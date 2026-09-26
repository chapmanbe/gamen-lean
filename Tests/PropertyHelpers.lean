import Gamen.Tableau
import Gamen.RankingTheory
import Gamen.FrameProperties
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
