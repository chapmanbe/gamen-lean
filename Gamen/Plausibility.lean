import Std.Data.TreeMap
import Gamen.Kripke
import Gamen.RankingTheory

/-!
# Gamen.Plausibility

Port of `gamen-hs/src/Gamen/Plausibility.hs`: a Halpern-style abstraction
over graded uncertainty, with ranking theory, finite discrete probability,
and possibility theory as instances.

## Background

Halpern (*Reasoning About Uncertainty*, MIT Press, 2nd ed. 2017, Ch. 2-3)
observes that probability, Spohn ranking functions, and Dubois-Prade
possibility measures are all *plausibility measures*: maps from events to a
partially ordered carrier `p` with a bottom (impossible) and top (certain)
element. What distinguishes the theories is the pair of combination
operations on the carrier — Halpern's algebraic conditional plausibility
spaces (§3.9) carry

* `⊕` (`plJoin`) — combines the plausibilities of *disjoint* events (sum
  for probability, max for possibility, min for ranks), and
* `⊗` (`plTimes`) — chains a conditional with its condition (product for
  probability, min for possibility, addition for ranks),

linked by the coherence requirement `Pl(A ∩ E) = Pl(A | E) ⊗ Pl(E)`.
Conditioning (`plCondition`) is the (chosen) section of `⊗`: it recovers
`Pl(A | E)` from `Pl(A ∩ E)` and `Pl(E)`. Given those two operations per
instance, the *measure-level* dynamics — computing event plausibilities
(`plOf`) and conditioning a whole measure on an observation (`conditionOn`)
— are defined once here, abstractly.

None of this is a Boxes & Diamonds topic; no B&D citation applies. The
Halpern and Spohn (1988) citations are external and are checked in
`Gamen.RankingTheory`'s docstring, not here.

## Differences from the Haskell

* Every `error` (the three smart constructors `mkRank`/`mkProbability`/
  `mkPossibility`, and `agentMeasure` on an unknown agent) is an
  `Except String`.
* Haskell's `Plausibility` typeclass, `class Eq p => Plausibility p`, is a
  Lean `class Plausibility (p : Type) [BEq p]`; `[BEq p]` stands in for the
  Haskell superclass constraint and is written out at every call site that
  needs it, since Lean does not project instance arguments of a class
  automatically the way Haskell projects superclasses.
* Haskell's `agentMeasure` is *not itself* wrapped in `Except`/`Maybe` — it
  is a bare projection that calls the pure smart constructor `mkRank` on
  each κ-value via `Map.map` from `Data.Map.Strict`, which forces every
  value to WHNF at construction (not the lazy `Data.Map`), so Haskell
  already crashes immediately on an out-of-invariant negative rank, the
  same moment the Lean port's `Except` does. The Lean port just makes that
  eager check explicit as an `Except`, inside the one `agentMeasure`
  already returns for the unknown-agent case, rather than an uncatchable
  `error`. Not exercised by any ported test (every `KappaModel` in scope is
  well-formed).
* `Rational` (Haskell's arbitrary-precision exact fraction, from `base`) is
  Lean's core `Rat`, with the same exactness guarantee (no floating-point
  drift).
-/
namespace Gamen

-- ════════════════════════════════════════════════════════════════════
-- The typeclass
-- ════════════════════════════════════════════════════════════════════

/-- A plausibility carrier in the sense of Halpern's algebraic conditional
plausibility spaces. Minimal complete definition: all six fields. See the
module header for the laws each instance satisfies:

* `plJoin` is commutative and associative with identity `plBot`.
* `plTimes` has identity `plTop` and annihilator `plBot`.
* *Coherence:* whenever `x plLeq b` and `b ≠ plBot`, `plCondition x b =
  some c` with `plTimes c b = x`.
* `plCondition x b = none` iff `b = plBot` (conditioning on an impossible
  event is undefined in all three theories). -/
class Plausibility (p : Type) [BEq p] where
  /-- The plausibility of the impossible event ∅. -/
  plBot : p
  /-- The plausibility of the certain event W. -/
  plTop : p
  /-- The (partial) order on plausibility values: `plLeq x y` means "x is
  at most as plausible as y". All three shipped instances happen to be
  totally ordered; the class only requires a partial order so that
  set-valued carriers (e.g. credal sets) can be added later without an
  interface change. -/
  plLeq : p → p → Bool
  /-- `⊕` — combine the plausibilities of two *disjoint* events into the
  plausibility of their union. The disjointness precondition is the
  caller's obligation (Halpern §3.9); `plOf` discharges it by only ever
  joining singletons. -/
  plJoin : p → p → p
  /-- `⊗` — chain a conditional plausibility with the plausibility of its
  condition: `Pl(A | E) ⊗ Pl(E) = Pl(A ∩ E)`. -/
  plTimes : p → p → p
  /-- Conditioning: `plCondition x b` recovers `Pl(A | E)` from
  `x = Pl(A ∩ E)` and `b = Pl(E)`. Returns `none` iff `b = plBot`
  (conditioning on an impossible event). Callers must ensure `x plLeq b`
  (automatic when `x` measures a subevent of the event `b` measures). -/
  plCondition : p → p → Option p

export Plausibility (plBot plTop plLeq plJoin plTimes plCondition)

/-- Strict version of the plausibility order. -/
def plLt [BEq p] [Plausibility p] (x y : p) : Bool :=
  plLeq x y && x != y

-- ════════════════════════════════════════════════════════════════════
-- Carrier: Spohn ranks (κ with infinity)
-- ════════════════════════════════════════════════════════════════════

/-- A Spohn rank as a plausibility value: lower κ = *more* plausible.
`infiniteRank` (κ = ∞) is the impossible event — it replaces the
`rankMaxBound` sentinel that `Gamen.RankingTheory.kappaProp` uses internally
with an honest extended value, so `⊗` (rank addition) cannot overflow
through it. -/
inductive RankedPlausibility
  | finiteRank (n : Int)  -- ^ κ = n, with n ≥ 0 (see `mkRank`)
  | infiniteRank          -- ^ κ = ∞
  deriving BEq, DecidableEq, Repr

/-- Smart constructor: ranks are non-negative. -/
def mkRank (n : Int) : Except String RankedPlausibility :=
  if n < 0 then throw s!"mkRank: negative rank {n}" else pure (.finiteRank n)

instance : Plausibility RankedPlausibility where
  plBot := .infiniteRank
  plTop := .finiteRank 0
  -- Lower κ is more plausible, so the plausibility order reverses the
  -- numeric order on ranks.
  plLeq x y := match x, y with
    | .infiniteRank, _ => true
    | .finiteRank _, .infiniteRank => false
    | .finiteRank a, .finiteRank b => a ≥ b
  -- κ(A ∪ B) = min(κ(A), κ(B))  (Spohn 1988, the defining law of OCFs)
  plJoin x y := match x, y with
    | .infiniteRank, y => y
    | x, .infiniteRank => x
    | .finiteRank a, .finiteRank b => .finiteRank (min a b)
  -- κ(A ∩ E) = κ(A | E) + κ(E)
  plTimes x y := match x, y with
    | .infiniteRank, _ => .infiniteRank
    | _, .infiniteRank => .infiniteRank
    | .finiteRank a, .finiteRank b => .finiteRank (a + b)
  -- κ(A | E) = κ(A ∩ E) − κ(E)  (Spohn Def. 5)
  plCondition x y := match x, y with
    | _, .infiniteRank => none
    | .infiniteRank, .finiteRank _ => some .infiniteRank
    | .finiteRank a, .finiteRank b => some (.finiteRank (a - b))

-- ════════════════════════════════════════════════════════════════════
-- Carrier: finite discrete probability
-- ════════════════════════════════════════════════════════════════════

/-- A probability as a plausibility value. `Rat` keeps the arithmetic exact
(`BEq` is honest, no floating-point drift), matching Haskell's `Rational`. -/
structure ProbabilityPlausibility where
  val : Rat
  deriving BEq, DecidableEq, Repr

/-- Smart constructor: probabilities live in [0, 1]. -/
def mkProbability (r : Rat) : Except String ProbabilityPlausibility :=
  if r < 0 || r > 1 then throw s!"mkProbability: {r} outside [0,1]"
  else pure ⟨r⟩

instance : Plausibility ProbabilityPlausibility where
  plBot := ⟨0⟩
  plTop := ⟨1⟩
  plLeq x y := x.val ≤ y.val
  -- P(A ∪ B) = P(A) + P(B) for disjoint A, B (finite additivity)
  plJoin x y := ⟨x.val + y.val⟩
  -- P(A ∩ E) = P(A | E) · P(E)  (chain rule)
  plTimes x y := ⟨x.val * y.val⟩
  -- P(A | E) = P(A ∩ E) / P(E)  (Bayes conditioning)
  plCondition x b := if b.val == 0 then none else some ⟨x.val / b.val⟩

-- ════════════════════════════════════════════════════════════════════
-- Carrier: max/min possibility theory
-- ════════════════════════════════════════════════════════════════════

/-- A possibility degree as a plausibility value (Dubois & Prade).
Combination is max/min; conditioning is the *min-based* (qualitative,
ordinal) rule rather than the product-based one — the natural choice when
degrees encode an ordering rather than frequencies. -/
structure PossibilityPlausibility where
  val : Rat
  deriving BEq, DecidableEq, Repr

/-- Smart constructor: possibility degrees live in [0, 1]. -/
def mkPossibility (r : Rat) : Except String PossibilityPlausibility :=
  if r < 0 || r > 1 then throw s!"mkPossibility: {r} outside [0,1]"
  else pure ⟨r⟩

instance : Plausibility PossibilityPlausibility where
  plBot := ⟨0⟩
  plTop := ⟨1⟩
  plLeq x y := x.val ≤ y.val
  -- Π(A ∪ B) = max(Π(A), Π(B)) — maxitivity, the defining possibility law
  plJoin x y := ⟨max x.val y.val⟩
  -- ⊗ = min — Π(A ∩ E) ≤ min(Π(A), Π(E)), with equality the algebraic
  -- chaining law for the min-based conditional
  plTimes x y := ⟨min x.val y.val⟩
  -- Min-based conditioning (Dubois-Prade):
  --   Π(A | E) = 1        if Π(A ∩ E) = Π(E)
  --            = Π(A ∩ E) otherwise
  -- min is not invertible, so the rule picks the MAXIMAL c with
  -- min(c, Π(E)) = Π(A ∩ E) — least-commitment conditioning.
  plCondition x b :=
    if b.val == 0 then none
    else if x.val == b.val then some ⟨1⟩
    else some x

-- ════════════════════════════════════════════════════════════════════
-- Plausibility measures over worlds
-- ════════════════════════════════════════════════════════════════════

/-- A plausibility measure over a finite set of worlds, represented by its
point plausibilities. Event plausibilities are derived via `plOf`; this is
faithful for all shipped instances because each is determined by its values
on singletons (finite additivity, maxitivity, and the OCF min-law
respectively). -/
structure PlausibilityMeasure (p : Type) where
  plmPoints : Std.TreeMap World p

/-- Structural equality, as Haskell's derived `Eq`. -/
instance [BEq p] : BEq (PlausibilityMeasure p) where
  beq m n := m.plmPoints.toList == n.plmPoints.toList

/-- Construct a measure from point plausibilities. -/
def mkMeasure (pts : List (World × p)) : PlausibilityMeasure p :=
  { plmPoints := Std.TreeMap.ofList pts }

/-- The point plausibility of a single world. Worlds outside the measure's
domain are impossible (`plBot`). -/
def plPoint [BEq p] [Plausibility p] (m : PlausibilityMeasure p) (w : World) : p :=
  m.plmPoints.getD w plBot

/-- The measure's domain of worlds. -/
def plDomain (m : PlausibilityMeasure p) : Std.TreeSet World :=
  Std.TreeSet.ofList m.plmPoints.keys

/-- The plausibility of an event A ⊆ W: the ⊕-combination of the point
plausibilities of its worlds. Singletons are pairwise disjoint, so the
disjointness precondition of `plJoin` is met by construction. -/
def plOf [BEq p] [Plausibility p] (m : PlausibilityMeasure p) (a : Std.TreeSet World) : p :=
  a.toList.foldr (fun w acc => plJoin (plPoint m w) acc) plBot

/-- Is the certain event maximally plausible? (Pl(W) = ⊤ — unit total mass,
a κ = 0 world, a fully possible world, respectively.) -/
def isNormalized [BEq p] [Plausibility p] (m : PlausibilityMeasure p) : Bool :=
  plOf m (plDomain m) == plTop

/-- Conditioning, defined ONCE at the abstract level: observe that the
event `e` obtains. Every world outside `e` becomes impossible (`plBot`);
every world inside `e` has its point plausibility renormalized against
`Pl(e)` via `plCondition`. Returns `none` iff `Pl(e) = plBot`.

For each instance this specializes to the textbook rule — `P(w)/P(E)`
(Bayes), `κ(w) − κ(E)` (Spohn Def. 5), and the min-based possibilistic rule
— because each theory's event measure distributes over its point values.
The result is always normalized (`isNormalized`) when `e` meets the
domain. -/
def conditionOn [BEq p] [Plausibility p]
    (m : PlausibilityMeasure p) (e : Std.TreeSet World) :
    Option (PlausibilityMeasure p) :=
  let bE := plOf m (e.filter (plDomain m).contains)
  if bE == plBot then none
  else
    let update (w : World) (x : p) : p :=
      if e.contains w then
        match plCondition x bE with
        | some x' => x'
        | none => plBot  -- unreachable: bE ≠ plBot here
      else plBot
    some { plmPoints := m.plmPoints.map update }

-- ════════════════════════════════════════════════════════════════════
-- Semantics-side hook
-- ════════════════════════════════════════════════════════════════════

/-- The maximally plausible worlds of a measure — the worlds whose point
plausibility is not strictly below any other's. This is the hook for
plausibility-ordered accessibility in Kripke frames: a doxastic agent
believes φ iff φ holds throughout `mostPlausible m` (Halpern Ch. 8; for
ranks this is the κ = 0 core that `Gamen.RankingTheory` calls the agent's
actual beliefs). -/
def mostPlausible [BEq p] [Plausibility p] (m : PlausibilityMeasure p) : Std.TreeSet World :=
  let ws := (plDomain m).toList
  (plDomain m).filter (fun w => !(ws.any (fun w' => plLt (plPoint m w) (plPoint m w'))))

-- ════════════════════════════════════════════════════════════════════
-- Bridge to ranking theory
-- ════════════════════════════════════════════════════════════════════

/-- Project one agent's κ-table out of a `KappaModel` as a plausibility
measure. This is the witness that ranking theory is an instance of the
abstraction: `conditionOn` on the projected measure agrees with Spohn
conditionalization (`Gamen.RankingTheory.conditionalize`) on the evidence
side — see the correspondence tests. Errors on an unknown agent, matching
`Gamen.RankingTheory.kappaWorld`. -/
def agentMeasure (m : KappaModel) (a : Agent) :
    Except String (PlausibilityMeasure RankedPlausibility) := do
  match m.kKappa.get? a with
  | none => throw s!"agentMeasure: unknown agent {repr a}"
  | some kw =>
    let pts ← kw.toList.mapM fun (w, k) => do
      let r ← mkRank k
      pure (w, r)
    return { plmPoints := Std.TreeMap.ofList pts }

end Gamen
