import Gamen.Atl.ImperfectInfo

/-!
# ATLir action-equivalence pruning (gamen-lean#8)

`atlirSatWith` enumerates uniform profiles with each agent's effect-equivalent
actions collapsed to one per epistemic class (`distinctUniformActions`). These
cases check that the pruned enumeration is smaller where it should be, and that
`atlirSat`/`atlirSatObjective` give the same answer, error text included, as the
unpruned brute force (`prune := false`) on pseudo-random iCGSs.
-/

namespace AtlirPruningTests

open Gamen

/-- `irCgs` from `Tests/Main.lean` with a third move `noop`, which does exactly
what `right` does: `(0,left)→2`, `(0,right|noop)→0`, `(1,right|noop)→2`,
`(1,left)→1`, and `2` absorbing. Alice cannot tell 0 from 1. -/
def noopModel : Except String (AtelModel Nat String) :=
  let moves : Nat → String → Std.TreeSet String := fun _ ag =>
    if ag == "alice" then Std.TreeSet.ofList ["left", "noop", "right"] else ∅
  let trans : Nat → Std.TreeMap String String → Nat
    | 0, jm => if jm.get? "alice" == some "left" then 2 else 0
    | 1, jm => if jm.get? "alice" == some "left" then 1 else 2
    | _, _ => 2
  let label : Nat → Std.TreeSet String
    | 2 => Std.TreeSet.ofList ["p"]
    | _ => ∅
  let epi : String → Nat → Std.TreeSet Nat
    | "alice", 0 => Std.TreeSet.ofList [0, 1]
    | "alice", 1 => Std.TreeSet.ofList [0, 1]
    | _, s => Std.TreeSet.ofList [s]
  mkAtelModel
    { cgsStates := Std.TreeSet.ofList [0, 1, 2], cgsAgents := Std.TreeSet.ofList ["alice"],
      cgsMoves := moves, cgsTransition := trans, cgsLabeling := label } epi

-- ── Pseudo-random iCGSs ─────────────────────────────────────────────────

private def mix (h x : Nat) : Nat :=
  (h * 6364136223846793005 + x * 1442695040888963407 + 1013904223) % 18446744073709551616

private def hashList (seed : Nat) (xs : List Nat) : Nat :=
  xs.foldl mix (mix seed 7)

private def agentNames : List String := ["a", "b", "c"]

/-- A pseudo-random iCGS with `n` states and three agents. Each agent's
epistemic partition puts state `i` in class `h(i) % 2` or `% 3`; its moves
are `0 … k-1`, with `k ∈ 1..3` fixed per class (so moves are uniform). The
transition depends on each agent's action only through an *effect* in
`0 … 1`, drawn per (agent, state, action), so actions with the same effect
at every state of a class are equivalent and pruning has something to do. -/
def randomModel (seed n : Nat) : Except String (AtelModel Nat Nat) :=
  let states := List.range n
  let agIx (ag : String) : Nat := (agentNames.idxOf ag)
  let nClasses (ag : String) : Nat := 2 + hashList seed [1, agIx ag] % 2
  let cls (ag : String) (st : Nat) : Nat := hashList seed [2, agIx ag, st] % nClasses ag
  let k (ag : String) (c : Nat) : Nat := 1 + hashList seed [3, agIx ag, c] % 3
  let moves : Nat → String → Std.TreeSet Nat := fun st ag =>
    if agentNames.contains ag then Std.TreeSet.ofList (List.range (k ag (cls ag st))) else ∅
  let effect (ag : String) (st act : Nat) : Nat := hashList seed [4, agIx ag, st, act] % 2
  let trans : Nat → Std.TreeMap String Nat → Nat := fun st jm =>
    let effs := agentNames.map fun ag => match jm.get? ag with
      | some act => effect ag st act
      | none => 9
    hashList seed (5 :: st :: effs) % n
  let label : Nat → Std.TreeSet String := fun st =>
    Std.TreeSet.ofList (["p", "q"].filter fun atm =>
      hashList seed [6, st, if atm == "p" then 0 else 1] % 2 == 0)
  let epi : String → Nat → Std.TreeSet Nat := fun ag st =>
    if agentNames.contains ag then
      Std.TreeSet.ofList (states.filter fun t => cls ag t == cls ag st)
    else Std.TreeSet.ofList [st]
  mkAtelModel
    { cgsStates := Std.TreeSet.ofList states, cgsAgents := Std.TreeSet.ofList agentNames,
      cgsMoves := moves, cgsTransition := trans, cgsLabeling := label } epi

private def coalitions : List (List String) :=
  [["a"], ["a", "b"], ["b", "c"], ["a", "b", "c"], []]

/-- Coalition formulas over `p`, `q`, one nesting, and one that raises an
unsupported-operator error inside a coalition operator. -/
private def formulas (c : List String) : List Formula :=
  let p : Formula := .atom "p"
  let q : Formula := .atom "q"
  [ .canNext c p, .canEventually c p, .canAlways c p, .canUntil c p q,
    .canNext c (.canEventually c q), .not (.canAlways c (.or p q)),
    .knowledge "a" (.canEventually c p), .canEventually c (.box p) ]

private def sameResult (x y : Except String (Std.TreeSet Nat)) : Bool :=
  match x, y with
  | .ok a, .ok b => a.toList == b.toList
  | .error e, .error f => e == f
  | _, _ => false

private def subjReq : AtelModel Nat Nat → Std.TreeSet String → Nat → Std.TreeSet Nat :=
  subjectiveClass

private def objReq : AtelModel Nat Nat → Std.TreeSet String → Nat → Std.TreeSet Nat :=
  fun _ _ st => Std.TreeSet.ofList [st]

/-- Pruned and unpruned `atlirSatWith` agree on every coalition and formula,
under both semantics. -/
def agrees (seed n : Nat) : Bool :=
  match randomModel seed n with
  | .error _ => false
  | .ok m => coalitions.all fun c => (formulas c).all fun f =>
      sameResult (atlirSatWith subjReq m f) (atlirSatWith subjReq m f (prune := false))
        && sameResult (atlirSatWith objReq m f) (atlirSatWith objReq m f (prune := false))

private def profileCount (m : AtelModel Nat Nat) (c : List String) (prune : Bool) : Nat :=
  match allUniformProfiles m (Std.TreeSet.ofList c) (prune := prune) with
  | .ok ps => ps.length
  | .error _ => 0

private def seeds : List Nat := (List.range 30).map fun i => 3000 + 7919 * i

def cases : List (String × Bool) :=
  [ ("ATLir pruning: noop ≡ right on {0,1}, and every move at the sink 2 is the same, \
      so alice's 9 uniform strategies collapse to 2 (left/right on {0,1})",
      match noopModel with
      | .ok m =>
          (allUniformProfiles m (Std.TreeSet.ofList ["alice"])).toOption.map List.length == some 9
            && (allUniformProfiles m (Std.TreeSet.ofList ["alice"]) (prune := true)).toOption.map
                List.length == some 2
      | .error _ => false),
    ("ATLir pruning: on the noop model, ⟨⟨alice⟩⟩ir X p = {2}, objective = {0,1,2}, \
      ⟨⟨alice⟩⟩ir F ¬p = {0,1} (as without noop)",
      match noopModel with
      | .ok m =>
          let al := ["alice"]
          let p : Formula := .atom "p"
          (atlirSat m (.canNext al p)).toOption.map (·.toList) == some [2]
            && (atlirSatObjective m (.canNext al p)).toOption.map (·.toList) == some [0, 1, 2]
            && (atlirSat m (.canEventually al (.not p))).toOption.map (·.toList) == some [0, 1]
      | .error _ => false),
    ("ATLir pruning: pruned = unpruned atlirSat and atlirSatObjective (errors included) \
      on 30 pseudo-random 3-agent iCGSs (3–5 states), 5 coalitions × 8 formulas",
      seeds.all fun sd => agrees sd (3 + sd % 3)),
    ("ATLir pruning is not vacuous: the pruned grand-coalition profile list is strictly \
      shorter on at least 20 of those 30 models",
      (seeds.filter fun sd => match randomModel sd (3 + sd % 3) with
        | .ok m => profileCount m agentNames true < profileCount m agentNames false
        | .error _ => false).length ≥ 20),
    ("ATLir pruning keeps the first profile, so a coalition operator forces the same \
      witness set first: pruned and unpruned first profiles agree on those 30 models",
      seeds.all fun sd => match randomModel sd (3 + sd % 3) with
        | .ok m =>
            let c := Std.TreeSet.ofList agentNames
            match allUniformProfiles m c, allUniformProfiles m c (prune := true) with
            | .ok (u :: _), .ok (p :: _) =>
                (u.toList.map fun (ag, st) => (ag, st.toList))
                  == (p.toList.map fun (ag, st) => (ag, st.toList))
            | _, _ => false
        | .error _ => false) ]

end AtlirPruningTests
