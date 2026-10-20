import Gamen.AngelsDemons

/-!
# SDL, SCL and SUL (`Gamen.AngelsDemons`; issue #3 item 2)

Answer keys: Examples 1-3 of Catta, Galimullin & Mittelmann, AAMAS 2026. Figure 1's edge
costs were first reconstructed from the text, then checked against the figure itself (p. 3,
rendered from the PDF, 2026-10-15): every label matches, including the self-loops. The tests
below are the paper's claims plus their obvious contrapositives (nothing here was fitted to a
result the paper does not state). Edges drawn only as dotted
possible additions keep their stated cost; pairs that are neither edges nor drawn get cost 9.

Cross-checks: with budget 0 the modifier cannot change anything, so `⟨⟨0⟩⟩` is the universal
path quantifier and `[0]` the existential one; compared against CTL fixpoints written
separately, on pseudo-random graphs.
-/

namespace AngelsDemonsTests

open Gamen.AngelsDemons

abbrev S := SFormula
abbrev P := PFormula

def atom (n : String) : S := .atom n
def imp (a b : S) : S := .or (.not a) b

/-! ## The access-control models (Figures 1-2) -/

def cost1 (i j : Nat) : Nat :=
  match i, j with
  | 0, 0 => 3 | 1, 1 => 3 | 2, 2 => 2 | 3, 3 => 2
  | 0, 1 => 3 | 1, 0 => 1 | 0, 2 => 2 | 2, 0 => 1
  | 0, 3 => 2 | 2, 3 => 1 | 3, 2 => 1
  | _, _ => 9

/-- Two states, a→a and b→b, cost 1, `b` true at b: the legality discriminator. -/
def tiny : Except String WModel :=
  mkWModel ["a", "b"] [(0, 0), (1, 1)] (fun _ _ => 1) (fun i => if i == 1 then ["b"] else [])

/-- a→b, b→b, cost 1, `b` true at b. -/
def chain : Except String WModel :=
  mkWModel ["a", "b"] [(0, 1), (1, 1)] (fun _ _ => 1) (fun i => if i == 1 then ["b"] else [])

def lab1 (i : Nat) : List String :=
  match i with
  | 1 => ["error"] | 2 => ["server"] | 3 => ["server", "admin"] | _ => []

def e1 : List (Nat × Nat) :=
  [(0, 0), (1, 1), (2, 2), (3, 3), (0, 1), (0, 2), (0, 3), (2, 0), (2, 3)]

def mk (edges : List (Nat × Nat)) : Except String WModel :=
  mkWModel ["s0", "s1", "s2", "s3"] edges cost1 lab1

/-- `𝔐1`; `𝔐2` drops `s2→s3` and `s0→s3`; `𝔐3` adds `s1→s0`. -/
def m1 : Except String WModel := mk e1
def m2 : Except String WModel := mk (e1.filter fun e => e != (2, 3) && e != (0, 3))
def m3 : Except String WModel := mk (e1 ++ [(1, 0)])

def sats (m : Except String WModel) (f : S) (maxModels : Nat := 20000) : Option (List String) :=
  match m with
  | .ok w => (satStates w f maxModels).toOption
  | .error _ => none

def admin : S := atom "admin"
def noAdmin : S := .not admin
def err : S := atom "error"

def coreCases : List (String × Bool) := [
  ("mkWModel: a non-serial graph, a zero cost and an out-of-range edge are errors",
    (mkWModel ["a", "b"] [(0, 1)] (fun _ _ => 1)).isOk == false
      && (mkWModel ["a"] [(0, 0)] (fun _ _ => 0)).isOk == false
      && (mkWModel ["a"] [(0, 0), (0, 3)] (fun _ _ => 1)).isOk == false),
  ("Example 1: ⟨⟨demon 2⟩⟩G¬admin holds at s0, s1, s2 and not at s3 (budget is per step)",
    sats m1 (.demon 2 (.always noAdmin)) == some ["s0", "s1", "s2"]),
  ("Example 1, contrapositive: with budget 1 the demon cannot remove s0→s3 (cost 2), so s0 and s2 fail",
    sats m1 (.demon 1 (.always noAdmin)) == some ["s1"]),
  ("Example 2 as stated, ⟨⟨angel 1⟩⟩G(error → ◇¬error): holds at s0, s2, s3 but NOT at s1 — the paper says \"any state\", yet at step 0 the model is still 𝔐1, where s1 has no exit",
    sats m1 (.angel 1 (.always (imp err (.angelBox 0 (.next (.not err)))))) == some ["s0", "s2", "s3"]),
  ("Example 2, the intended reading — a one-step property, not the paper's G invariance: after the angel's first move the implication holds from every state (⟨⟨angel 1⟩⟩X(error → ◇¬error))",
    sats m1 (.angel 1 (.next (imp err (.angelBox 0 (.next (.not err))))))
      == some ["s0", "s1", "s2", "s3"]),
  ("Example 2: without the angel (budget 0) that goal fails at s1, whose only exit is missing",
    (sats m1 (.angel 0 (.always (imp err (.angelBox 0 (.next (.not err))))))).map (·.contains "s1")
      == some false),
  ("Example 2: in 𝔐3 the angel still cannot force the traveller out of error (⟨⟨angel 1⟩⟩X¬error fails at s1)",
    (sats m3 (.angel 1 (.next (.not err)))).map (·.contains "s1") == some false),
  ("Example 3: ⟨[angel 2, demon 2]⟩F¬admin holds at s3 of 𝔐2 (cooperation empties the admin module)",
    (sats m2 (.update 2 2 (.eventually noAdmin))).map (·.contains "s3") == some true),
  ("Example 3 (cooperative form), contrapositives: with the partner's budget 0, the demon alone or the angel alone cannot (the traveller can stay). The paper's own competitive statement ⟨[demon 2]⟩² is not implemented",
    (sats m2 (.update 0 2 (.eventually noAdmin))).map (·.contains "s3") == some false
      && (sats m2 (.update 2 0 (.eventually noAdmin))).map (·.contains "s3") == some false),
  ("Example 3: one angelic edge (cost 1) and then the demon's self-loop removal (cost 2) suffice, over two steps",
    (sats m2 (.update 1 2 (.eventually noAdmin))).map (·.contains "s3") == some true),
  ("SUL legality (review finding): the demon may not remove s3's last edge in the same step the angel adds a new one; so ⟨[angel 1, demon 2]⟩X¬admin fails at s3, as the paper's Example 3 narrative needs two steps",
    (sats m2 (.update 1 2 (.next noAdmin))).map (·.contains "s3") == some false),
  ("SUL: the same demon removal is fine once the angel's edge exists (𝔐2 plus s3→s2): ⟨[0,2]⟩X¬admin holds at s3",
    (match mk ((e1.filter fun e => e != (2, 3) && e != (0, 3)) ++ [(3, 2)]) with
     | .ok w => (satStates w (.update 0 2 (.next noAdmin))).toOption.map (·.contains "s3") == some true
     | .error _ => false)),
  ("nested strategic operators with non-zero budgets: ⟨⟨1⟩⟩X⟨⟨1⟩⟩X¬admin holds only at s1 (hand-derived from Defs 2, 3, 5)",
    sats m1 (.demon 1 (.next (.demon 1 (.next noAdmin)))) == some ["s1"]),
  ("nested, with different budgets: ⟨⟨2⟩⟩X⟨⟨1⟩⟩X¬admin holds at s0, s1, s2 (hand-derived)",
    sats m1 (.demon 2 (.next (.demon 1 (.next noAdmin)))) == some ["s0", "s1", "s2"]),
  ("holdsAt: an unknown state is an error, not false; duplicate state names are rejected",
    (match m1 with | .ok w => (holdsAt w noAdmin "s9").isOk == false | .error _ => false)
      && (mkWModel ["a", "a"] [(0, 0), (1, 1)] (fun _ _ => 1)).isOk == false),
  ("a huge budget on a dense graph is an error quickly, not a hang (subset enumeration is capped)",
    (match mkWModel ((List.range 10).map toString)
        ((List.range 10).flatMap fun i => (List.range 10).map fun j => (i, j)) (fun _ _ => 1) with
     | .ok w => (satStates w (.demon 20 (.next (.atom "p")))).isOk == false
     | .error _ => false)),
  ("seriality: the demon cannot remove a state's last edge, so ⟨⟨9⟩⟩X¬q is false at a state whose only successor has q",
    (match mkWModel ["a", "b"] [(0, 1), (1, 1)] (fun _ _ => 1) (fun i => if i == 1 then ["q"] else []) with
     | .ok w => (satStates w (.demon 9 (.next (.not (.atom "q"))))).toOption == some []
     | .error _ => false)),
  ("duality against hand-derived values, not against the code's own dual: [1]F admin = {s0,s2,s3}, [2]F admin = {s3}, [1]G¬admin = {s0,s1,s2}",
    sats m1 (.demonBox 1 (.eventually admin)) == some ["s0", "s2", "s3"]
      && sats m1 (.demonBox 2 (.eventually admin)) == some ["s3"]
      && sats m1 (.demonBox 1 (.always noAdmin)) == some ["s0", "s1", "s2"]),
  ("duality: [n]F admin ≡ ¬⟨⟨n⟩⟩G¬admin, for n = 0, 1, 2",
    [0, 1, 2].all fun n =>
      sats m1 (.demonBox n (.eventually admin)) == sats m1 (.not (.demon n (.always noAdmin)))),
  ("duality: [n]G admin ≡ ¬⟨⟨n⟩⟩F¬admin, and angelic, and over U/R",
    [0, 1, 2].all fun n =>
      sats m1 (.demonBox n (.always admin)) == sats m1 (.not (.demon n (.eventually noAdmin)))
        && sats m1 (.angelBox n (.eventually admin)) == sats m1 (.not (.angel n (.always noAdmin)))
        && sats m1 (.demonBox n (.until (atom "server") admin))
          == sats m1 (.not (.demon n (.release (.not (atom "server")) noAdmin)))),
  ("monotone in the budget: the demon with more resources never loses (⟨⟨0⟩⟩ ⊆ ⟨⟨1⟩⟩ ⊆ ⟨⟨2⟩⟩ for G¬admin)",
    match sats m1 (.demon 0 (.always noAdmin)), sats m1 (.demon 1 (.always noAdmin)),
        sats m1 (.demon 2 (.always noAdmin)) with
    | some a, some b, some c => a.all b.contains && b.all c.contains
    | _, _, _ => false),
  ("budget 0 changes nothing, for demon and angel alike",
    sats m1 (.demon 0 (.eventually admin)) == sats m1 (.angel 0 (.eventually admin))
      && sats m1 (.demon 0 (.always noAdmin)) == sats m1 (.angel 0 (.always noAdmin))),
  ("Example 3, competitive: the demon alone cannot clear the admin module, ⟨[demon 2]⟩^2 F¬admin fails at s3 of 𝔐2 (the angel can play the empty move)",
    (sats m2 (.updateDemon 2 2 (.eventually noAdmin))).map (·.contains "s3") == some false),
  ("Example 3, competitive: ⟨[demon 2]⟩^2 G¬admin fails at s1 of 𝔐2 (the angel, aided by a simultaneous bridge, reaches s3)",
    (sats m2 (.updateDemon 2 2 (.always noAdmin))).map (·.contains "s1") == some false),
  ("Example 3, competitive: ⟨[demon 2]⟩^1 G¬admin holds at s1 of 𝔐2 (the angel with one resource cannot restore a path to s3)",
    (sats m2 (.updateDemon 2 1 (.always noAdmin))).map (·.contains "s1") == some true),
  ("SUL reading A (Brian, 2026-10-15), hand-derived on a 2-state model (a→a, b→b, cost 1, `b` at b): at a, X b fails for all four coalitions, since the last edge a→a is not removable even when the angel adds a→b at the same time; under joint-result legality ⟨[demon 1]⟩^1 X b would hold at a. At b only the cooperative and the angelic-choice forms hold (a universal angel can add b→a)",
    (match tiny with
     | .ok w =>
       let atS (f : S) (s : String) := (satStates w f).toOption.map (·.contains s)
       [atS (.update 1 1 (.next (atom "b"))) "a", atS (.updateDemon 1 1 (.next (atom "b"))) "a",
        atS (.updateAngel 1 1 (.next (atom "b"))) "a", atS (.updateNone 1 1 (.next (atom "b"))) "a"]
         == [some false, some false, some false, some false]
       && [atS (.update 1 1 (.next (atom "b"))) "b", atS (.updateDemon 1 1 (.next (atom "b"))) "b",
           atS (.updateAngel 1 1 (.next (atom "b"))) "b", atS (.updateNone 1 1 (.next (atom "b"))) "b"]
         == [some true, some false, some true, some false]
     | .error _ => false)),
  ("⟨[∅]⟩ is universal over both: with a→b, b→b, F b holds at a for budgets (angel 0, demon 1) (no removable edge, no additions) and fails for (angel 1, demon 0) (the angel adds a→a and the traveller loops)",
    (match chain with
     | .ok w =>
       (satStates w (.updateNone 0 1 (.eventually (atom "b")))).toOption == some ["a", "b"]
       && (satStates w (.updateNone 1 0 (.eventually (atom "b")))).toOption == some ["b"]
     | .error _ => false)),
  ("duality of the new modalities against the pushed-through form: [demon d]^a F admin ≡ ¬⟨[demon d]⟩^a G¬admin, and angel, and ∅ (𝔐2)",
    [0, 1, 2].all fun n =>
      sats m2 (.updateDemonBox n 1 (.eventually admin)) == sats m2 (.not (.updateDemon n 1 (.always noAdmin)))
        && sats m2 (.updateAngelBox 1 n (.eventually admin)) == sats m2 (.not (.updateAngel 1 n (.always noAdmin)))
        && sats m2 (.updateNoneBox n 1 (.eventually admin)) == sats m2 (.not (.updateNone n 1 (.always noAdmin)))),
  ("an arena larger than the cap is an error, never a partial answer",
    match m1 with
    | .ok w => (satStates w (.demon 2 (.always noAdmin)) 2).isOk == false
    | .error _ => false)
]

/-! ## `⟨⟨0⟩⟩` and `[0]` against CTL, on pseudo-random graphs -/

/-- A small LCG, so the graphs are reproducible. -/
def lcg (x : Nat) : Nat := (x * 1103515245 + 12345) % 2147483648

/-- A random serial graph on `k` states with atoms `p`, `q`, from `seed`. -/
def randomModel (k seed : Nat) : Except String WModel :=
  let rec go (i j x : Nat) (acc : List (Nat × Nat)) (fuel : Nat) : List (Nat × Nat) × Nat :=
    match fuel with
    | 0 => (acc, x)
    | fuel + 1 =>
      if i ≥ k then (acc, x)
      else
        let x' := lcg x
        let acc' := if x' / 65536 % 3 == 0 then (i, j) :: acc else acc
        if j + 1 ≥ k then go (i + 1) 0 x' acc' fuel else go i (j + 1) x' acc' fuel
  let (es, x) := go 0 0 seed [] (k * k + 1)
  -- make every state serial by giving the ones with no edge a self-loop
  let es := es ++ (List.range k).filterMap fun i =>
    if es.any (·.1 == i) then none else some (i, i)
  let x1 := lcg x
  let x2 := lcg x1
  mkWModel ((List.range k).map toString) es (fun _ _ => 1)
    (fun i => (if (x1 / (i + 1)) % 2 == 0 then ["p"] else []) ++ (if (x2 / (i + 1)) % 2 == 0 then ["q"] else []))

def adj (w : WModel) (i : Nat) : List Nat :=
  (List.range w.k).filter fun j => w.edges.contains (i, j)

def ids (w : WModel) : List Nat := List.range w.k

/-- CTL set `AG p`, `AF p`, `EF p`, `AX p`, `A[p U q]` as lists of states, by naive iteration. -/
def lfpL (w : WModel) (f : List Nat → List Nat) : List Nat :=
  (List.range (w.k + 2)).foldl (fun cur _ => f cur) []
def gfpL (w : WModel) (f : List Nat → List Nat) : List Nat :=
  (List.range (w.k + 2)).foldl (fun cur _ => f cur) (ids w)

def holdsAtom (w : WModel) (a : String) : List Nat := (ids w).filter fun i => (w.labels i).contains a
def ax (w : WModel) (x : List Nat) : List Nat := (ids w).filter fun i => (adj w i).all x.contains
def ex (w : WModel) (x : List Nat) : List Nat := (ids w).filter fun i => (adj w i).any x.contains
def ag (w : WModel) (p : List Nat) : List Nat := gfpL w fun z => (ids w).filter fun i => p.contains i && (adj w i).all z.contains
def af (w : WModel) (p : List Nat) : List Nat := lfpL w fun z => (ids w).filter fun i => p.contains i || (adj w i).all z.contains
def ef (w : WModel) (p : List Nat) : List Nat := lfpL w fun z => (ids w).filter fun i => p.contains i || (adj w i).any z.contains
def au (w : WModel) (p q : List Nat) : List Nat :=
  lfpL w fun z => (ids w).filter fun i => q.contains i || (p.contains i && (adj w i).all z.contains)

def eg (w : WModel) (p : List Nat) : List Nat := gfpL w fun z => (ids w).filter fun i => p.contains i && (adj w i).any z.contains

def named (w : WModel) (x : List Nat) : List String := x.map fun i => w.states[i]!

def agrees (seed k : Nat) : Bool :=
  match randomModel k seed with
  | .error _ => false
  | .ok w =>
    let p := holdsAtom w "p"
    let q := holdsAtom w "q"
    let chk (f : S) (expect : List Nat) : Bool :=
      (satStates w f).toOption == some (named w expect)
    -- with a budget that covers every edge the modifier is unconstrained (up to seriality):
    -- a big demon is the existential path quantifier, a big angel changes nothing for X
    chk (.demon 100 (.next (atom "p"))) (ex w p)
      && chk (.demon 100 (.eventually (atom "p"))) (ef w p)
      && chk (.demon 100 (.always (atom "p"))) (eg w p)
      -- (a big angel on 5 states has ~2^17 edge sets to add: past the arena cap, so an error)
      && (w.k > 4 || chk (.angel 100 (.next (atom "p"))) (ax w p))
      && chk (.demon 0 (.next (atom "p"))) (ax w p)
      && chk (.demon 0 (.always (atom "p"))) (ag w p)
      && chk (.demon 0 (.eventually (atom "p"))) (af w p)
      && chk (.demon 0 (.until (atom "p") (atom "q"))) (au w p q)
      && chk (.demonBox 0 (.eventually (atom "p"))) (ef w p)
      && chk (.demonBox 0 (.next (atom "q"))) (ex w q)
      && chk (.angel 0 (.always (atom "q"))) (ag w q)

/-- The new coalitions against what they must reduce to or be bounded by, on one graph. -/
def updateAgrees (seed k : Nat) : Bool :=
  match randomModel k seed with
  | .error _ => false
  | .ok w =>
    let paths : List P := [.next (atom "p"), .eventually (atom "p"), .always (atom "p"),
      .until (atom "p") (atom "q")]
    let sat' (f : S) := (satStates w f).toOption
    let sub (x y : Option (List String)) : Bool :=
      match x, y with | some a, some b => a.all b.contains | _, _ => false
    paths.all fun ψ =>
      -- a universal side with budget 0 can only play the empty move
      (sat' (.updateDemon 1 0 ψ)).isSome && sat' (.updateDemon 1 0 ψ) == sat' (.demon 1 ψ)
        && sat' (.updateAngel 1 0 ψ) == sat' (.angel 1 ψ)
        && sat' (.updateNone 0 0 ψ) == sat' (.demon 0 ψ)
        -- more universal quantifiers never help the existential side
        && sub (sat' (.updateNone 1 1 ψ)) (sat' (.updateDemon 1 1 ψ))
        && sub (sat' (.updateNone 1 1 ψ)) (sat' (.updateAngel 1 1 ψ))
        && sub (sat' (.updateDemon 1 1 ψ)) (sat' (.update 1 1 ψ))
        && sub (sat' (.updateAngel 1 1 ψ)) (sat' (.update 1 1 ψ))

def randomCases : List (String × Bool) :=
  [("⟨⟨0⟩⟩ and [0] agree with AX/AG/AF/AU/EF/EX, and a budget-100 demon with EX/EF/EG, on 24 pseudo-random graphs (3-5 states)",
    (List.range 24).all fun i => agrees (1000 + 7919 * i) (3 + i % 3)),
   ("⟨[demon n]⟩^0 = ⟨⟨n⟩⟩, ⟨[angel n]⟩^0 = ⟨⟨n⟩⟩ (angelic), ⟨[∅]⟩^{0,0} = ⟨⟨0⟩⟩, and ⟨[∅]⟩ ⊆ ⟨[demon]⟩^m, ⟨[angel]⟩^d ⊆ cooperative ⟨[angel,demon]⟩, on 12 pseudo-random 3-state graphs (budgets ≤ 1; X, F, G, U)",
    (List.range 12).all fun i => updateAgrees (2000 + 104729 * i) 3),
   ("the inclusions are not vacuous: on those graphs ⟨[∅]⟩^{1,1} is strictly smaller than cooperative ⟨[angel 1, demon 1]⟩ for some seed and some path formula",
    (List.range 12).any fun i => match randomModel 3 (2000 + 104729 * i) with
      | .ok w => [PFormula.next (atom "p"), .eventually (atom "p"), .always (atom "p")].any fun ψ =>
          (satStates w (.updateNone 1 1 ψ)).toOption != (satStates w (.update 1 1 ψ)).toOption
      | .error _ => false),
   ("the random graphs are mostly non-trivial (some state satisfies p and some does not, in at least 18 of 24)",
    ((List.range 24).filter fun i => match randomModel (3 + i % 3) (1000 + 7919 * i) with
      | .ok w => let p := holdsAtom w "p"; !p.isEmpty && p.length < w.k
      | .error _ => false).length ≥ 18)]

/-! ## The expressivity proofs of §3 (Theorems 1, 2, 4): the paper's separating models, run

The proofs rest on pairs of models that one logic tells apart and another cannot. The first half
of each argument (a formula *does* hold in one and fail in the other) is a computation, checked
here against the implementation; the second half (no formula of the other logic can tell them
apart) is the paper's argument and is not tested. Figure 3 is read off p. 5 of the PDF, Figure 4
off p. 6. -/

/-- 𝔐1/𝔐2 of Fig. 3: `s : p` and `t`, every edge present, cost `c` on all of them. -/
def fig3Complete (c : Nat) : Except String WModel :=
  mkWModel ["s", "t"] [(0, 0), (0, 1), (1, 0), (1, 1)] (fun _ _ => c)
    (fun i => if i == 0 then ["p"] else [])

/-- 𝔐3 of Fig. 3: `s : p` and `t`, reflexive edges only, cost 1 everywhere. 𝔐4 is `s` alone. -/
def fig3M3 : Except String WModel :=
  mkWModel ["s", "t"] [(0, 0), (1, 1)] (fun _ _ => 1) (fun i => if i == 0 then ["p"] else [])
def fig3M4 : Except String WModel :=
  mkWModel ["s"] [(0, 0)] (fun _ _ => 1) (fun _ => ["p"])

/-- Fig. 4: the chain `s1 → … → s_{n+1}`, then `s_{n+1} → t_i` for `i ≤ k`, `t_i` reflexive,
`p` only at `t1`, all costs 1. States: `s1..s_{n+1}` are 0..n, `t_i` is `n + i`. -/
def fig4 (n k : Nat) : Except String WModel :=
  mkWModel (((List.range (n + 1)).map fun i => s!"s{i + 1}") ++ ((List.range k).map fun i => s!"t{i + 1}"))
    ((List.range n).map (fun i => (i, i + 1)) ++ (List.range k).map (fun i => (n, n + 1 + i))
      ++ (List.range k).map (fun i => (n + 1 + i, n + 1 + i)))
    (fun _ _ => 1) (fun i => if i == n + 1 then ["p"] else [])

def holdsAtName (m : Except String WModel) (f : S) (s : String) : Option Bool :=
  match m with
  | .ok w => (satStates w f).toOption.map (·.contains s)
  | .error _ => none

def pp : S := atom "p"

def expressivityCases : List (String × Bool) := [
  ("Thm 1/2, SDL ⋠ SCL (Fig. 3): ⟨⟨1⟩⟩X p holds at s of 𝔐1 (the demon removes s→t, cost 1) and fails at s of 𝔐2 (every edge costs 2)",
    holdsAtName (fig3Complete 1) (.demon 1 (.next pp)) "s" == some true
      && holdsAtName (fig3Complete 2) (.demon 1 (.next pp)) "s" == some false),
  ("Thm 1/2, SCL ⋠ SDL and CTL ≺ SCL (Fig. 3): ⟨⟨angel 1⟩⟩X[angel 0]X¬p holds at s of 𝔐3 and fails at s of 𝔐4",
    holdsAtName fig3M3 (.angel 1 (.next (.angelBox 0 (.next (.not pp))))) "s" == some true
      && holdsAtName fig3M4 (.angel 1 (.next (.angelBox 0 (.next (.not pp))))) "s" == some false),
  ("Thm 1/2, the SUL formula ⟨[angel 1]⟩^0 X [⟨angel 0, demon 0⟩] X¬p — the competitive form — separates 𝔐3 from 𝔐4 too",
    holdsAtName fig3M3 (.updateAngel 1 0 (.next (.updateBox 0 0 (.next (.not pp))))) "s" == some true
      && holdsAtName fig3M4 (.updateAngel 1 0 (.next (.updateBox 0 0 (.next (.not pp))))) "s" == some false),
  ("Thm 2's translations SDL ≼ SUL and SCL ≼ SUL: ⟨[angel 0, demon n]⟩ ≡ ⟨⟨n⟩⟩ and ⟨[angel n, demon 0]⟩ ≡ the angelic ⟨⟨n⟩⟩ (on 𝔐1 of Fig. 1 and the Fig. 3 models), and Thm 1's ⟨[angel 0, demon 0]⟩ ≡ ⟨⟨0⟩⟩",
    [m1, m2, m3, fig3Complete 1, fig3Complete 2, fig3M3].all fun m =>
      [PFormula.next pp, .eventually pp, .always (.not pp), .until (.not pp) pp].all fun ψ =>
        [0, 1, 2].all fun n =>
          sats m (.update 0 n ψ) == sats m (.demon n ψ) && (sats m (.demon n ψ)).isSome
            && sats m (.update n 0 ψ) == sats m (.angel n ψ) && (sats m (.angel n ψ)).isSome
            && sats m (.update 0 0 ψ) == sats m (.demon 0 ψ)),
  ("Thm 4, SDL ⋠ OL (Fig. 4): ⟨⟨1⟩⟩F p holds at s1 of 𝔐_{n+2} (n+1 non-p t-states, and the demon has n+1 removals along the way) and fails at s1 of 𝔐_{n+3}, for n = 1, 2, 3",
    [1, 2, 3].all fun n =>
      holdsAtName (fig4 n (n + 2)) (.demon 1 (.eventually pp)) "s1" == some true
        && holdsAtName (fig4 n (n + 3)) (.demon 1 (.eventually pp)) "s1" == some false)
]


/-! ## Theorem 5's lower bound: QBF reduces to SDL model checking (p. 6), run end to end

`𝔐^Ψ` has states `s, s_1..s_{2n}`, edges `s→s`, `s→s_i`, `s_i→s`, `p_i^1` at `s_i` and `p_i^0` at
`s_{n+i}`, cost 2 on `s→s` and 1 elsewhere. The demon sets `p_i` true by removing `s → p_i^0`
(`s→s_{n+i}`); `chosen_k` guards that exactly the first `k` atoms are set unambiguously;
`φ_k := [1]X(chosen_k → φ_{k-1})` for `∀`, `⟨1⟩X(chosen_k ∧ φ_{k-1})` for `∃`, `φ_0 := ψ(◇◇p_i^1)`.
As printed, `φ := φ_n` nests `φ_{k-1}` *inside* `φ_k`, so the first demon move would face
`chosen_n`, which cannot hold after one removal; the nesting that works puts `Q_1` outermost
with `chosen_1` (`qbfFormula`). The printed order is `qbfFormulaPrinted`; both are tested. -/

/-- `Ψ = Q_1 p_1 … Q_n p_n ψ`: `true` = ∃. `ψ` is a CNF of literals `±i` (1-based). -/
structure Qbf where
  exists_ : List Bool
  cnf : List (List Int)

def Qbf.n (q : Qbf) : Nat := q.exists_.length

/-- Brute-force truth of the QBF. -/
def Qbf.eval (q : Qbf) : Bool :=
  let rec go (j : Nat) (val : List Bool) (fuel : Nat) : Bool :=
    match fuel with
    | 0 => false
    | fuel + 1 =>
      if j ≥ q.n then
        q.cnf.all fun cl => cl.any fun l =>
          let v := val.getD (l.natAbs - 1) false
          if l > 0 then v else !v
      else if q.exists_.getD j false then go (j + 1) (val ++ [true]) fuel || go (j + 1) (val ++ [false]) fuel
      else go (j + 1) (val ++ [true]) fuel && go (j + 1) (val ++ [false]) fuel
  go 0 [] (q.n + 2)

def qbfModel (n : Nat) : Except String WModel :=
  mkWModel ("s" :: (List.range (2 * n)).map fun i => s!"s{i + 1}")
    ([(0, 0)] ++ (List.range (2 * n)).flatMap fun i => [(0, i + 1), (i + 1, 0)])
    (fun i j => if i == 0 && j == 0 then 2 else 1)
    (fun st => if st == 0 then []
      else if st ≤ n then [s!"p1_{st}"] else [s!"p0_{st - n}"])

def dia (f : S) : S := .demonBox 0 (.next f)
def diaDia (f : S) : S := dia (dia f)
def iffS (a b : S) : S := .and (imp a b) (imp b a)

def chosen (n k : Nat) : S :=
  let first := (List.range k).map fun i =>
    iffS (diaDia (atom s!"p0_{i + 1}")) (.not (diaDia (atom s!"p1_{i + 1}")))
  let rest := ((List.range n).filter (· ≥ k)).map fun i =>
    SFormula.and (diaDia (atom s!"p0_{i + 1}")) (diaDia (atom s!"p1_{i + 1}"))
  first.foldl SFormula.and (rest.foldl SFormula.and SFormula.top)

def matrix (q : Qbf) : S :=
  let lit (l : Int) : S :=
    let a := diaDia (atom s!"p1_{l.natAbs}")
    if l > 0 then a else .not a
  q.cnf.foldl (fun acc cl => SFormula.and acc (cl.foldl (fun d l => SFormula.or d (lit l)) (.not SFormula.top))) SFormula.top

/-- The nesting that works: `Q_1` outermost, guarded by `chosen_1`. -/
def qbfFormula (q : Qbf) : S :=
  let n := q.n
  let rec go (j : Nat) (fuel : Nat) : S :=
    match fuel with
    | 0 => matrix q
    | fuel + 1 =>
      if j > n then matrix q
      else if q.exists_.getD (j - 1) false then
        .demon 1 (.next (.and (chosen n j) (go (j + 1) fuel)))
      else .demonBox 1 (.next (imp (chosen n j) (go (j + 1) fuel)))
  go 1 (n + 1)

/-- As printed: `φ_n` outermost with `Q_n` and `chosen_n`. -/
def qbfFormulaPrinted (q : Qbf) : S :=
  let n := q.n
  let rec go (k : Nat) (fuel : Nat) : S :=
    match fuel with
    | 0 => matrix q
    | fuel + 1 =>
      if k == 0 then matrix q
      else if q.exists_.getD (k - 1) false then
        .demon 1 (.next (.and (chosen n k) (go (k - 1) fuel)))
      else .demonBox 1 (.next (imp (chosen n k) (go (k - 1) fuel)))
  go n (n + 1)

def qbfHolds (q : Qbf) (f : Qbf → S) : Option Bool :=
  holdsAtName (qbfModel q.n) (f q) "s"

def qbfs2 : List Qbf :=
  [[false, false], [false, true], [true, false], [true, true]].flatMap fun pre =>
    [[[1, 2]], [[1], [-2]], [[1, -2], [-1, 2]], [[1], [2]], [[-1, -2]], [[1, 2], [-1, -2]]].map
      fun cnf => { exists_ := pre, cnf := cnf }

def qbfs3 : List Qbf :=
  [[false, true, false], [true, false, true], [true, true, false], [false, false, true]].flatMap fun pre =>
    [[[1, 2], [-2, 3]], [[1, -3], [2, 3], [-1, -2]], [[1, 2, 3]]].map fun cnf => { exists_ := pre, cnf := cnf }

def qbfCases : List (String × Bool) := [
  ("Thm 5 lower bound: the QBF reduction run through the SDL checker agrees with brute-force QBF truth on all 24 two-variable instances (4 prefixes × 6 matrices), with both true and false instances",
    qbfs2.all (fun q => qbfHolds q qbfFormula == some q.eval)
      && qbfs2.any (·.eval) && qbfs2.any (!·.eval)),
  ("…and on 12 three-variable instances",
    qbfs3.all (fun q => qbfHolds q qbfFormula == some q.eval)
      && qbfs3.any (·.eval) && qbfs3.any (!·.eval)),
  ("…but the nesting as printed (φ_n outermost, chosen_n first) does not: it disagrees with brute-force truth on some instance",
    qbfs2.all (fun q => (qbfHolds q qbfFormulaPrinted).isSome)
      && qbfs2.any fun q => qbfHolds q qbfFormulaPrinted != some q.eval)
]

def cases : List (String × Bool) := coreCases ++ expressivityCases ++ qbfCases

end AngelsDemonsTests
