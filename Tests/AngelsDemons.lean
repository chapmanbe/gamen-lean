import Gamen.AngelsDemons

/-!
# SDL, SCL and SUL (`Gamen.AngelsDemons`; issue #3 item 2)

Answer keys: Examples 1-3 of Catta, Galimullin & Mittelmann, AAMAS 2026. Figure 1's edge
costs are small and were reconstructed so that *every claim the paper's text makes about the
two models* holds; the tests below are exactly those claims plus their obvious contrapositives
(nothing here was fitted to a result the paper does not state). Edges drawn only as dotted
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

def cases : List (String × Bool) := [
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
  ("Example 2, the intended reading: after the angel's first move the property holds from every state (⟨⟨angel 1⟩⟩X(error → ◇¬error))",
    sats m1 (.angel 1 (.next (imp err (.angelBox 0 (.next (.not err))))))
      == some ["s0", "s1", "s2", "s3"]),
  ("Example 2: without the angel (budget 0) that goal fails at s1, whose only exit is missing",
    (sats m1 (.angel 0 (.always (imp err (.angelBox 0 (.next (.not err))))))).map (·.contains "s1")
      == some false),
  ("Example 2: in 𝔐3 the angel still cannot force the traveller out of error (⟨⟨angel 1⟩⟩X¬error fails at s1)",
    (sats m3 (.angel 1 (.next (.not err)))).map (·.contains "s1") == some false),
  ("Example 3: ⟨[angel 2, demon 2]⟩F¬admin holds at s3 of 𝔐2 (cooperation empties the admin module)",
    (sats m2 (.update 2 2 (.eventually noAdmin))).map (·.contains "s3") == some true),
  ("Example 3, contrapositives: the demon alone, or the angel alone, cannot (the traveller can stay)",
    (sats m2 (.update 0 2 (.eventually noAdmin))).map (·.contains "s3") == some false
      && (sats m2 (.update 2 0 (.eventually noAdmin))).map (·.contains "s3") == some false),
  ("Example 3: one angelic edge (cost 1) plus the demon's self-loop removal (cost 2) suffice",
    (sats m2 (.update 1 2 (.eventually noAdmin))).map (·.contains "s3") == some true),
  ("seriality: the demon cannot remove a state's last edge, so ⟨⟨9⟩⟩X¬q is false at a state whose only successor has q",
    (match mkWModel ["a", "b"] [(0, 1), (1, 1)] (fun _ _ => 1) (fun i => if i == 1 then ["q"] else []) with
     | .ok w => (satStates w (.demon 9 (.next (.not (.atom "q"))))).toOption == some []
     | .error _ => false)),
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

def named (w : WModel) (x : List Nat) : List String := x.map fun i => w.states[i]!

def agrees (seed k : Nat) : Bool :=
  match randomModel k seed with
  | .error _ => false
  | .ok w =>
    let p := holdsAtom w "p"
    let q := holdsAtom w "q"
    let chk (f : S) (expect : List Nat) : Bool :=
      (satStates w f).toOption == some (named w expect)
    chk (.demon 0 (.next (atom "p"))) (ax w p)
      && chk (.demon 0 (.always (atom "p"))) (ag w p)
      && chk (.demon 0 (.eventually (atom "p"))) (af w p)
      && chk (.demon 0 (.until (atom "p") (atom "q"))) (au w p q)
      && chk (.demonBox 0 (.eventually (atom "p"))) (ef w p)
      && chk (.demonBox 0 (.next (atom "q"))) (ex w q)
      && chk (.angel 0 (.always (atom "q"))) (ag w q)

def randomCases : List (String × Bool) :=
  [("⟨⟨0⟩⟩ and [0] agree with AX/AG/AF/AU/EF/EX on 24 pseudo-random graphs (3-5 states, demon and angel)",
    (List.range 24).all fun i => agrees (1000 + 7919 * i) (3 + i % 3)),
   ("the random graphs are not all trivial (some state satisfies p and some does not)",
    (List.range 24).any fun i => match randomModel (3 + i % 3) (1000 + 7919 * i) with
      | .ok w => let p := holdsAtom w "p"; !p.isEmpty && p.length < w.k
      | .error _ => false)]

end AngelsDemonsTests
