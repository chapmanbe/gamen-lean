import Std.Data.TreeMap
import Std.Data.TreeSet
import Gamen.Cgs
import Gamen.Formula

/-!
# Gamen.Laca

Port of `gamen-hs/src/Gamen/Laca.hs`: LACA, the Logic of Agency based on
Control and Attempt (Herzig, Lorini & Perrotin, "A Computationally Grounded
Logic of 'Seeing-to-it-that'", *IJCAI 2022*, pp. 2648–2654; local PDF
`gamen-hs/notes/Lorini2022.pdf`, page range checked against it). A
computationally grounded encoding of STIT logic where models are finite:
states are propositional valuations, each atom is controlled by exactly one
agent, and the successor state is determined by all agents' attempts.

The Haskell's own docstring simplifies the paper's higher-order atom
valuations (`c_i α`/`t_i α` control-and-attempt atoms in the state) to a
flat `Map String Bool` over base atoms; the semantic clauses for X, G, □,
◇, and `[J cstit]` are still faithful to the paper (§3.2, p. 2650). Ported
here unchanged.

`Agent` is written as `String` directly, as in `Gamen.Cgs`/`Gamen.Stit`/
`Gamen.Xstit`/`Gamen.Epistemic` (`Gamen.Agent` already exists in
`RankingTheory.lean`, a module this one's Haskell import list does not
depend on).

Every Haskell `error` becomes an `Except`: `lSatisfies`'s state/model atom-set
guard (gamen-hs#7, mirroring gamen-hs#3 and the same guard pattern as
`Gamen.Epistemic.eSatisfies`/`Gamen.Stit.sSatisfies`/`Gamen.Xstit.xSatisfies`)
and its fifteen unsupported operators (Haskell wording kept verbatim). The
guard is written once, ahead of the `match`, rather than repeated on every
constructor as in the Haskell's blanket first equation — every recursive
call in this module still re-enters `lSatisfies` and so re-runs the check,
and `succState` never changes a state's key set, so the two are equivalent
for every call this module makes.

`trajectory` already carries explicit fuel from the Haskell (`maxLen`,
always `trajectoryBound s0` at every call site) rather than looping "until
nothing changes" with no bound, so it is ported as ordinary structural
recursion on that fuel, not through `Kripke.iterateToFixpoint`: that
helper's contract (converge to a fixed value, throw on exhaustion) does not
match this loop's shape (accumulate a path with cycle detection along the
way, truncating at the fuel bound). The truncation branch is unreachable in
practice — the state space has `2 ^ |atoms|` valuations, so a repeat is
forced within `trajectoryBound s0` steps by pigeonhole — matching Haskell,
which also just truncates there rather than treating it as an error.

`LacaState` (`Std.TreeMap String Bool`) and the CGS action type used by
`lacaToCgs` (`Std.TreeSet String`, an "attempt set") both need `Ord` for use
as `Std.TreeSet`/`Cgs` type parameters; Std provides neither, so both are
added here as ordinary (non-orphan-restricted) instances, ordered by
`toList` comparison — see `Gamen.Cgs`'s docstring on why Lean needs these
where the Haskell record needs no such constraint.
-/
namespace Gamen

-- `Ord (List (String × Bool))` (used by `Ord LacaState` below) needs
-- `Ord (String × Bool)`; Lean core defines it (`lexOrd`) but does not make
-- it a global instance, so enable it locally here (as `Tableau.lean` and
-- `Epistemic.lean` do).
attribute [local instance] lexOrd

/-- A LACA state: a valuation assigning truth values to atoms. In LACA,
states are complete — every atom has a definite truth value. -/
abbrev LacaState := Std.TreeMap String Bool

/-- Ordered by the state's sorted `(atom, value)` association list; Std
gives `TreeMap` no `Ord` instance. -/
instance : Ord LacaState where
  compare a b := compare a.toList b.toList

/-- An "attempt set": the atoms whose controlling agents are trying to
flip them. Used as `Cgs`'s action type in `lacaToCgs`; Std gives `TreeSet`
no `Ord` instance either. -/
instance : Ord (Std.TreeSet String) where
  compare a b := compare a.toList b.toList

/-- A LACA model.

The model encodes agency via control and successor functions:
- Each propositional atom is controlled by exactly one agent.
- The successor state is determined by the current state plus which agents
  attempt to change which atoms.
- An "attempt" for agent `i` is a set of atoms that `i` tries to flip. -/
structure LacaModel where
  /-- All propositional atoms. -/
  lacaAtoms : Std.TreeSet String
  /-- All agents. -/
  lacaAgents : Std.TreeSet String
  /-- Which agent controls which atom. -/
  lacaControl : Std.TreeMap String String
  deriving Inhabited

/-- Construct a LACA model from atoms and control assignments. -/
def mkLacaModel (controlPairs : List (String × String)) : LacaModel :=
  { lacaAtoms := Std.TreeSet.ofList (controlPairs.map Prod.fst)
    lacaAgents := Std.TreeSet.ofList (controlPairs.map Prod.snd)
    lacaControl := Std.TreeMap.ofList controlPairs }

/-- Get the truth value of an atom in a state. Atoms not in the state are
treated as `False`. -/
def stateValue (s : LacaState) (atom : String) : Bool :=
  s.getD atom false

/-- Compute the successor state given a set of atoms being attempted
(flipped). An attempt is a set of atoms whose controlling agents are trying
to change their values.

For each atom `p`: if `p` is in the attempt set, flip its value; otherwise
keep it. -/
def succState (s : LacaState) (attempts : Std.TreeSet String) : LacaState :=
  Std.TreeMap.ofList (s.toList.map fun (atom, val) =>
    (atom, if attempts.contains atom then !val else val))

/-- `trajectory`'s accumulating loop (Haskell `go`): `fuel` mirrors the
Haskell's decreasing `n`, `seen` the visited-set, `acc` the reversed prefix
built so far. Matches the Haskell equation-by-equation: the `fuel = 0` case
ignores both `s` and `seen` exactly as the Haskell's `go _ 0 _ acc` does. -/
private def trajectoryGo (attempts : Std.TreeSet String) :
    Nat → LacaState → Std.TreeSet LacaState → List LacaState → List LacaState
  | 0, _, _, acc => acc.reverse
  | fuel + 1, s, seen, acc =>
    if seen.contains s then (s :: acc).reverse
    else trajectoryGo attempts fuel (succState s attempts) (seen.insert s) (s :: acc)

/-- Generate a trajectory of states from a starting state, applying a fixed
attempt set repeatedly. Returns states up to a cycle or the given maximum
length. -/
def trajectory (s0 : LacaState) (attempts : Std.TreeSet String) (maxLen : Nat) :
    List LacaState :=
  trajectoryGo attempts maxLen s0 ∅ []

/-- A safe upper bound on the number of distinct states a single
(fixed-attempt) trajectory can visit: the state space has `2 ^ n` valuations
for `n` atoms, so `2 ^ n + 1` steps force a cycle. `trajectory` detects
cycles independently via its visited-set, so this is only a backstop — but
`2 ^ s.size` would silently overflow a fixed-width `Int` (as in the Haskell)
once a state has ≳63 atoms; capped at 62 here too, purely for parity with
the Haskell's reasoning, since Lean's arbitrary-precision `Nat` cannot
itself overflow. -/
def trajectoryBound (s : LacaState) : Nat :=
  2 ^ min 62 s.size + 1

/-- Generate all subsets of a list (powerset), matching the Haskell
`powerSet`'s exact enumeration order: `rest` (all subsets of `xs`) followed
by each of those with `x` inserted. -/
private def powerSet : List String → List (Std.TreeSet String)
  | [] => [∅]
  | x :: xs =>
    let rest := powerSet xs
    rest ++ rest.map (·.insert x)

-- --------------------------------------------------------------------
-- Semantics (Section 3.2, Herzig et al. 2022, p. 2650)
-- --------------------------------------------------------------------

/-- `M, V, n ⊩ φ` — satisfaction at state `V` and time step `n`, for LACA
models.

The key operators:
- `V, n ⊩ α` iff `α ∈ succ^n(V)` (for atoms)
- `V, n ⊩ Xφ` iff `V, n+1 ⊩ φ` (next state)
- `V, n ⊩ Gφ` iff `V, m ⊩ φ` for all `m ≥ n` (always future)
- `V, n ⊩ [J cstit]φ` iff for all alternative attempt profiles by agents
  NOT in `J`, `φ` holds *at the current state* under the combined attempts
  (`J`'s own attempts held fixed). The operator does NOT advance time on
  its own — wrap `φ` in `Next` (X) to talk about the successor.
- `V, n ⊩ [J dstit]φ` iff `[J cstit]φ` and not `□φ`

TODO(gamen-hs#18): confirm the `[J cstit]` evaluation point against Herzig,
Lorini & Perrotin 2022 §3.2. The implementation evaluates at the current
state with the combined attempts (not "at the next state"); `Gamen.Laca`'s
own docstring notes this is unsettled against the paper (`notes/
stit-logics-review.md` does not resolve it either). Ported as-is.

For simplicity, we evaluate at the given state directly (`n = 0`) and use
the successor function to handle `X` and `G`. IMPORTANT: `G`/`F` here follow
a *single trajectory* generated by iterating the FIXED current attempt
profile (period ≤ 2 for a deterministic `succ`), not the paper's
quantification over all plays — a deliberate finite-model simplification
(adversarial review B3, gamen-hs).

Errors if the state's atom set does not match the model's `lacaAtoms` —
without this guard, evaluating an atom not declared in the model silently
defaults to `False`, producing vacuously-true results for negation and
implication (gamen-hs#7, mirroring gamen-hs#3). LACA states are required to
be *complete* propositional valuations over the model's atoms, so this is
the natural domain check. -/
def lSatisfies (m : LacaModel) (s : LacaState) (atts : Std.TreeSet String) :
    Formula → Except String Bool := fun f => do
  unless Std.TreeSet.ofList s.keys == m.lacaAtoms do
    throw s!"lSatisfies: state's atom set {s.keys} \
      does not match model's lacaAtoms {m.lacaAtoms.toList}"
  match f with
  -- Propositional. `and`/`or`/`implies` short-circuit exactly as Haskell's
  -- lazy `&&`/`||`/`not (…) || …` do, so a right side that would error is
  -- never evaluated once the left side already settles the result.
  | .bot => return false
  | .atomF a => return stateValue s a.name
  | .not f' => return !(← lSatisfies m s atts f')
  | .and l r => if !(← lSatisfies m s atts l) then return false else lSatisfies m s atts r
  | .or l r => if (← lSatisfies m s atts l) then return true else lSatisfies m s atts r
  | .implies l r =>
      if !(← lSatisfies m s atts l) then return true else lSatisfies m s atts r
  | .iff l r => return (← lSatisfies m s atts l) == (← lSatisfies m s atts r)
  -- X φ: next state (apply current attempts, then evaluate φ).
  | .next f' => lSatisfies m (succState s atts) atts f'
  -- G φ: φ holds at current state and all future states. We check up to a
  -- cycle (since the state space is finite, trajectories must eventually
  -- cycle).
  | .futureBox f' =>
      (trajectory s atts (trajectoryBound s)).allM fun s' => lSatisfies m s' atts f'
  -- F φ: φ holds at some future state.
  | .futureDiamond f' =>
      (trajectory s atts (trajectoryBound s)).anyM fun s' => lSatisfies m s' atts f'
  -- [J cstit] φ: the Chellas stit for group J. True iff for ALL possible
  -- attempt sets by agents NOT in J, φ holds (evaluated at current state
  -- with the combined attempts). J's current attempts are fixed; we vary
  -- non-J agents' attempts. The stit operator itself does not advance
  -- time — use X inside φ.
  | .stit agent f' =>
      let jAtoms := Std.TreeSet.ofList
        (m.lacaControl.toList.filterMap fun (a, ag) => if ag == agent then some a else none)
      let jAtts := atts ∩ jAtoms
      let nonJAtoms := (m.lacaAtoms \ jAtoms).toList
      (powerSet nonJAtoms).allM fun nonJAtts => lSatisfies m s (jAtts ∪ nonJAtts) f'
  -- [Agt] cstit φ: grand coalition — all agents' attempts are fixed, so φ
  -- is just evaluated at current state (no opponents to vary).
  | .groupStit f' => lSatisfies m s atts f'
  -- □φ: historically necessary / settled — φ holds regardless of ANY
  -- agent's attempts. Quantify over all possible attempt sets.
  | .box f' => (powerSet m.lacaAtoms.toList).allM fun atts' => lSatisfies m s atts' f'
  -- ◇φ: dual of □ — φ holds for some attempt set.
  | .diamond f' => (powerSet m.lacaAtoms.toList).anyM fun atts' => lSatisfies m s atts' f'
  -- Operators not supported in LACA.
  | .choiceDiamond _ _ => throw "ChoiceDiamond not yet supported in LACA"
  | .pastBox _ => throw "PastBox not supported in LACA"
  | .pastDiamond _ => throw "PastDiamond not supported in LACA"
  | .since _ _ => throw "Since not supported in LACA"
  | .until _ _ => throw "Until not supported in LACA"
  | .knowledge _ _ => throw "Knowledge not supported in LACA"
  | .belief _ _ => throw "Belief not supported in LACA"
  | .rankedBelief _ _ _ => throw "RankedBelief not supported in LACA; use Gamen.RankingTheory"
  | .announce _ _ => throw "Announce not supported in LACA"
  | .ought _ _ => throw "Ought not supported in LACA; use Gamen.DeonticStit"
  | .permitted _ _ => throw "Permitted not supported in LACA; use Gamen.DeonticStit"
  | .coalition _ _ => throw "Coalition not supported in LACA; use Gamen.Cgs/Gamen.Coalition"
  | .canNext _ _ => throw "CanNext not supported in LACA; use Gamen.Atl"
  | .canAlways _ _ => throw "CanAlways not supported in LACA; use Gamen.Atl"
  | .canEventually _ _ => throw "CanEventually not supported in LACA; use Gamen.Atl"
  | .canUntil _ _ _ => throw "CanUntil not supported in LACA; use Gamen.Atl"

-- --------------------------------------------------------------------
-- CGS coercion (Herzig et al. 2022, §3.1 — LACA as restricted CGS)
-- --------------------------------------------------------------------

/-- Lift a `LacaModel` into a `Cgs` over `LacaState` with action type
`Std.TreeSet String` (an "attempt set" — the atoms an agent tries to flip).

Correspondence to `Gamen.Cgs`:

- `cgsStates` — all `2 ^ n` complete valuations over `lacaAtoms`
- `cgsAgents` — `lacaAgents`
- `cgsMoves s ag` — all subsets of atoms controlled by `ag`
  (state-independent in LACA; the powerset of the agent's atoms)
- `cgsTransition s jm` — `succState` applied to the union of all agents'
  attempt sets in the joint move `jm`
- `cgsLabeling s` — the set of atoms that are `True` in `s`

This coercion allows ATL and Coalition Logic formulas (from `Gamen.Atl` and
`Gamen.Coalition`, neither ported yet) to be evaluated over LACA models.
Note: the ATL semantics considers all combinations of agents' moves; use
`lSatisfies` for evaluation at a fixed attempt set.

Uses the bare `Cgs` constructor, not `mkCgs`: this builds a `Cgs` by
transformation from an already-validated `LacaModel`, exactly the kind of
internal builder `Cgs.mkCgs`'s docstring carves out (alongside
`Gamen.Atl.ImperfectInfo.residualCgs`, not ported yet), rather than from raw
user data. -/
def lacaToCgs (m : LacaModel) : Cgs LacaState (Std.TreeSet String) :=
  let atomList := m.lacaAtoms.toList
  let allStates : Std.TreeSet LacaState :=
    Std.TreeSet.ofList <| (powerSet atomList).map fun trueSet =>
      Std.TreeMap.ofList (atomList.map fun a => (a, trueSet.contains a))
  { cgsStates := allStates
    cgsAgents := m.lacaAgents
    cgsMoves := fun _ ag =>
      let agAtoms :=
        m.lacaControl.toList.filterMap fun (a, ag') => if ag' == ag then some a else none
      Std.TreeSet.ofList (powerSet agAtoms)
    cgsTransition := fun s jm => succState s (jm.values.foldl (· ∪ ·) ∅)
    cgsLabeling := fun s =>
      Std.TreeSet.ofList (s.toList.filterMap fun (a, v) => if v then some a else none) }

end Gamen
