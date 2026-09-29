import Gamen.Atl.ModelCheck
import Gamen.Cgs
import Gamen.Formula

/-!
# Gamen.Atel

Port of `gamen-hs/src/Gamen/Atel.hs`: Alternating-time Temporal Epistemic
Logic (ATEL) over Concurrent Game Structures with per-agent
indistinguishability relations.

ATEL extends ATL with knowledge operators `K_a`: an agent's knowledge is
determined by which states they cannot distinguish. Strategic operators
`⟨⟨C⟩⟩` are interpreted as in ATL (perfect-info semantics); the epistemic
relations are orthogonal.

References:
  van der Hoek & Wooldridge (2003), *Cooperation, Knowledge, and Time:
  Alternating-time Temporal Epistemic Logic*, Studia Logica 75(1): 125–157.
  The "Definition 3 (p. 134)" citations below and in `Tests/Main.lean`'s
  `atelCases` match `gamen-hs/notes/vanderhoek-wooldridge2003-correspondence.md`
  ("Definition 3 (p. 134): Satisfaction Relation"); the paper itself is not
  among the PDFs in `gamen-hs/notes/`, so the page number is unverified
  against a primary source.

`atelSat`'s eighteen unsupported-operator `error` calls (everything outside
the ATL/Coalition/propositional/knowledge fragment) become `Except`, wording
kept verbatim, matching `Gamen.Atl.ModelCheck`'s precedent. `atelSatisfies`'s
world guard is likewise `Except`, matching `Gamen.Atl.atlSatisfies`.

**Laziness.** `atelSat`'s propositional connectives (`Not`/`And`/`Or`/
`Implies`/`Iff`) follow `Gamen.Atl.ModelCheck.sat`'s laziness fix exactly
(same `Data.Set` combinators, same clauses) — see that module's docstring
for the full derivation and the GHC checks behind it, including its
"Error order" (both operands erroring: `Or`/`Implies`/`Iff` report the
right one) and "One-step coalition operators" (`preCLazy`) notes, which
apply here unchanged. `Knowledge` skips `φ` on a zero-state model (it is a
`Set.filter` over `states`); corrected 2026-09-29 after a GHCi check. The
`CanAlways`/`CanEventually`/`CanUntil` step functions need no handling:
`lfp`/`gfp` always force `satPhi` (then `satPsi`) on their first step. -/
namespace Gamen

-- ── Model ────────────────────────────────────────────────────────────────

/-- An ATEL model: a CGS augmented with per-agent indistinguishability.

`atelEpistemic ag s` returns the set of states that agent `ag` cannot
distinguish from `s` (the equivalence class of `s` under `~_ag`). The class
must include `s` itself (reflexivity). Symmetry and transitivity are not
enforced by the type but are assumed by the semantics — `mkAtelModel`
checks all three, plus move-uniformity, before building one. -/
structure AtelModel (s a : Type) [Ord s] [Ord a] where
  /-- Underlying CGS. -/
  atelCgs : Cgs s a
  /-- Epistemic neighbourhood of `s` for `ag`. -/
  atelEpistemic : String → s → Std.TreeSet s

/-- Construct an `AtelModel`, checking that each agent's epistemic relation
is an equivalence relation (reflexive, symmetric, transitive) and that
indistinguishable states offer the same moves.

The move-uniformity check is what makes uniform strategies well-defined: in
a standard iCGS the actions available to an agent must be identical across
states it cannot distinguish, otherwise a "uniform" choice could be
unavailable at some state in the class (adversarial review B7; Schobbens
2004; Bulling & Jamroga 2014). The checks are needed for correct
`Gamen.Atl.ImperfectInfo` semantics, which quantify over
`~_a` classes and assume they partition the state space.

Returns the first violation found, in the Haskell's order (reflexivity,
then symmetry, then transitivity, then move-uniformity), as an `Except`, or
the `AtelModel` itself. Each category's Haskell list comprehension ranges
over every `(agent, state)` pair and reports a message naming only the
agent, so finding the first agent (in `cgsAgents` order) with *any*
violation in a category yields the identical message to Haskell's "first
element of the concatenated list". -/
def mkAtelModel {s a : Type} [Ord s] [Ord a]
    (cgs : Cgs s a) (epistemic : String → s → Std.TreeSet s) :
    Except String (AtelModel s a) := do
  let ags := cgs.cgsAgents.toList
  let states := cgs.cgsStates.toList
  let reflexivityViolations :=
    ags.filter fun ag => states.any fun st => !(epistemic ag st).contains st
  match reflexivityViolations with
  | ag :: _ =>
      throw ("mkAtelModel: agent " ++ ag
        ++ " has a non-reflexive epistemic relation (state not in own class)")
  | [] =>
  let symmetryViolations :=
    ags.filter fun ag =>
      states.any fun st =>
        (epistemic ag st).toList.any fun t => !(epistemic ag t).contains st
  match symmetryViolations with
  | ag :: _ =>
      throw ("mkAtelModel: agent " ++ ag ++ " has a non-symmetric epistemic relation")
  | [] =>
  let transitivityViolations :=
    ags.filter fun ag =>
      states.any fun st =>
        (epistemic ag st).toList.any fun t =>
          (epistemic ag t).toList.any fun u => !(epistemic ag st).contains u
  match transitivityViolations with
  | ag :: _ =>
      throw ("mkAtelModel: agent " ++ ag ++ " has a non-transitive epistemic relation")
  | [] =>
  let uniformMovesViolations :=
    ags.filter fun ag =>
      states.any fun st =>
        (epistemic ag st).toList.any fun t => cgs.cgsMoves st ag != cgs.cgsMoves t ag
  match uniformMovesViolations with
  | ag :: _ =>
      throw ("mkAtelModel: agent " ++ ag
        ++ " has differing move sets across indistinguishable states")
  | [] =>
      return { atelCgs := cgs, atelEpistemic := epistemic }

-- ── Satisfaction set ────────────────────────────────────────────────────

/-- Compute the set of all states satisfying `φ` in an ATEL model.

`Knowledge` is handled via the epistemic neighbourhood:

> sat(K_a φ) = { s | atelEpistemic a s ⊆ sat(φ) }

All ATL operators delegate to the underlying CGS via `preC`, `lfp`, and
`gfp` (van der Hoek & Wooldridge 2003, Definition 3), as in
`Gamen.Atl.ModelCheck.sat`. `lfp`/`gfp` take the same fuel bound as there
(`cgsStates.size + 1`), for the same reason: every set built along the way
is a subset of `cgsStates`. -/
def atelSat {s a : Type} [Ord s] [Ord a] [BEq s] (m : AtelModel s a) (f : Formula) :
    Except String (Std.TreeSet s) :=
  go f
where
  cgs := m.atelCgs
  states := m.atelCgs.cgsStates
  go : Formula → Except String (Std.TreeSet s)
  | .bot => pure ∅
  | .atomF atm =>
      pure (states.filter fun st => (cgs.cgsLabeling st).contains atm.name)
  | .not f' =>
      -- Laziness (see the module docstring): skip `f'` when `states` is
      -- empty, matching `Data.Set.difference ∅ e = ∅` without forcing `e`.
      if states.isEmpty then pure ∅
      else do
        let sf ← go f'
        pure (states \ sf)
  | .and l r => do
      -- `go l` always forced (`intersection`'s first argument); `go r`
      -- skipped exactly when `go l`'s result is empty.
      let sl ← go l
      if sl.isEmpty then pure ∅
      else do
        let sr ← go r
        pure (sl ∩ sr)
  | .or l r => do
      -- `union` forces both sides, its second argument first: when both
      -- error, `r`'s error (GHCi, 2026-09-29).
      let sr ← go r
      let sl ← go l
      pure (sl ∪ sr)
  | .implies l r => do
      -- Consequent `go r` is `union`'s second argument: forced first,
      -- always. Antecedent follows `Not`'s rule (skip `go l` iff `states`
      -- empty).
      let sr ← go r
      let diffPart ← do
        if states.isEmpty then pure (∅ : Std.TreeSet s)
        else do
          let sl ← go l
          pure (states \ sl)
      pure (diffPart ∪ sr)
  | .iff l r => do
      -- `states` empty: only `go l` is forced (it is ∅, so `go r` is
      -- skipped). `states` nonempty: `Set.union sl sr`, inside the outer
      -- union's second argument, forces `sr` and then `sl`, so when both
      -- error, `r`'s error (GHCi, 2026-09-29).
      if states.isEmpty then
        let sl ← go l
        if sl.isEmpty then pure ∅
        else do
          let sr ← go r
          pure (sl ∩ sr)
      else do
        let sr ← go r
        let sl ← go l
        pure ((sl ∩ sr) ∪ (states \ (sl ∪ sr)))

  -- K_a φ — van der Hoek & Wooldridge (2003), Definition 3(i). A
  -- `Set.filter` over `states`: `go phi` is never forced when `states` is
  -- empty (GHCi, 2026-09-29).
  | .knowledge agent phi =>
      if states.isEmpty then pure ∅
      else do
        let sphi ← go phi
        pure (states.filter fun st => (m.atelEpistemic agent st).all fun t => sphi.contains t)

  -- [C]φ — Coalition Logic (one-step; Pauly 2002). `preCLazy`: `go phi`
  -- is forced only where the lazy `preC` would force it.
  | .coalition c phi => preCLazy cgs (Std.TreeSet.ofList c) (go phi)

  -- ⟨⟨C⟩⟩Xφ — next-step (AHK 2002, Def. 3(1))
  | .canNext c phi => preCLazy cgs (Std.TreeSet.ofList c) (go phi)

  -- ⟨⟨C⟩⟩Gφ — greatest fixpoint (AHK 2002, Def. 3(2))
  | .canAlways c phi => do
      let satPhi ← go phi
      let coalition := Std.TreeSet.ofList c
      gfp states (fun x => satPhi ∩ preC cgs coalition x) (states.size + 1)

  -- ⟨⟨C⟩⟩Fφ — least fixpoint (AHK 2002, Def. 3(3))
  | .canEventually c phi => do
      let satPhi ← go phi
      let coalition := Std.TreeSet.ofList c
      lfp (fun x => satPhi ∪ preC cgs coalition x) (states.size + 1)

  -- ⟨⟨C⟩⟩(φ U ψ) — until (AHK 2002, Def. 3(4))
  | .canUntil c phi psi => do
      let satPhi ← go phi
      let satPsi ← go psi
      let coalition := Std.TreeSet.ofList c
      lfp (fun x => satPsi ∪ (satPhi ∩ preC cgs coalition x)) (states.size + 1)

  -- Operators not supported in ATEL
  | .box _ => throw "Box not supported in ATEL; use ⟨⟨Ag⟩⟩G"
  | .diamond _ => throw "Diamond not supported in ATEL"
  | .futureBox _ => throw "FutureBox not supported in ATEL; use CanAlways"
  | .futureDiamond _ => throw "FutureDiamond not supported in ATEL; use CanEventually"
  | .pastBox _ => throw "Past operators not supported in ATEL"
  | .pastDiamond _ => throw "Past operators not supported in ATEL"
  | .since _ _ => throw "Since not supported in ATEL"
  | .until _ _ => throw "Until not supported in ATEL"
  | .belief _ _ => throw "Belief not supported in ATEL; use Gamen.Epistemic for KD45 belief"
  | .rankedBelief _ _ _ => throw "RankedBelief not supported in ATEL"
  | .announce _ _ => throw "Announce not supported in ATEL; use Gamen.Epistemic for PAL"
  | .stit _ _ => throw "Stit requires a STIT model (use Gamen.Stit)"
  | .choiceDiamond _ _ => throw "ChoiceDiamond requires a STIT model"
  | .groupStit _ => throw "GroupStit requires a STIT model"
  | .next _ => throw "Next requires a Laca model (use Gamen.Laca)"
  | .ought _ _ => throw "Ought requires a deontic model (use Gamen.DeonticStit)"
  | .permitted _ _ => throw "Permitted requires a deontic model (use Gamen.DeonticStit)"

-- ── Convenience wrappers ────────────────────────────────────────────────

/-- M, s ⊩ φ — ATEL satisfaction at a single state.

Errors if `s` is not in `cgsStates` of the underlying CGS, or if `atelSat`
itself errors. -/
def atelSatisfies {s a : Type} [Ord s] [Ord a] [BEq s]
    (m : AtelModel s a) (st : s) (f : Formula) : Except String Bool :=
  if !m.atelCgs.cgsStates.contains st then
    throw "atelSatisfies: state is not in cgsStates"
  else do
    let satSet ← atelSat m f
    pure (satSet.contains st)

/-- A formula is true in an ATEL model if it holds at every state. -/
def atelIsTrueIn {s a : Type} [Ord s] [Ord a] [BEq s]
    (m : AtelModel s a) (f : Formula) : Except String Bool := do
  let satSet ← atelSat m f
  pure (satSet == m.atelCgs.cgsStates)

end Gamen
