import Gamen.EvidenceTrust

/-!
# DL-BET tests (`Gamen/EvidenceTrust.lean`)

Expected values come from Liu & Lorini (PRIMA 2017) or are hand-derived, never from the code under test.
-/

namespace EvidenceTrustTests

open Gamen.EvidenceTrust

def ok {α} (r : Except String α) : Bool := match r with | .ok _ => true | .error _ => false
def errStarts {α} (r : Except String α) (pre : String) : Bool :=
  match r with | .error e => e.startsWith pre | .ok _ => false

/-! ## A two-world, two-agent base model for constructor probes -/
def base : ESM where
  n := 2
  agents := #["a", "b"]
  valuation := #[["p"], []]
  E := #[#[3, 3], #[3, 3]]
  D := #[#[3, 3], #[3, 3]]
  S := #[#[#[[], []], #[[], []]], #[#[[], []], #[[], []]]]
  C := #[#[#[[], []], #[[], []]], #[#[[], []], #[[], []]]]
  T := #[#[(0, 1), (0, 1)], #[(0, 1), (0, 1)]]

def constructorCases : List (String × Bool) := [
  ("the base model is an ESM", ok base.validate),
  ("C1: a relation that is not an equivalence",
    errStarts ({ base with E := #[#[3, 2], #[3, 3]] }.validate) "C1"),
  ("C2: no possible world",
    errStarts ({ base with D := #[#[0, 0], #[3, 3]] }.validate) "C2"),
  ("C3: belief outside the information set",
    errStarts ({ base with E := #[#[1, 2], #[3, 3]], D := #[#[3, 3], #[3, 3]] }.validate) "C3"),
  ("C4: belief differs inside one class",
    errStarts ({ base with D := #[#[1, 3], #[3, 3]] }.validate) "C4"),
  ("C5: evidence differs inside one class",
    errStarts ({ base with S := #[#[#[[1], []], #[[], []]], #[#[[], []], #[[], []]]],
                           C := #[#[#[[1], [1]], #[[], []]], #[#[[], []], #[[], []]]] }.validate) "C5"),
  ("C6: trust differs inside one class",
    errStarts ({ base with C := #[#[#[[], []], #[[1], []]], #[#[[], []], #[[], []]]] }.validate) "C6"),
  ("C7: a trusted set outside the information set",
    errStarts ({ base with E := #[#[1, 2], #[3, 3]], D := #[#[1, 2], #[3, 3]],
                           C := #[#[#[[], []], #[[], [3]]], #[#[[], []], #[[], []]]] }.validate) "C7"),
  ("C8: trusting someone about the empty set (the PDF's ∅ ∉ C, not the extract's ∈)",
    errStarts ({ base with C := #[#[#[[], []], #[[0], [0]]], #[#[[], []], #[[], []]]] }.validate) "C8"),
  ("C9: evidence from a source one does not trust",
    errStarts ({ base with S := #[#[#[[], []], #[[1], [1]]], #[#[[], []], #[[], []]]] }.validate) "C9"),
  ("C10: the type differs inside one class",
    errStarts ({ base with T := #[#[(0, 1), (1, 1)], #[(0, 1), (0, 1)]] }.validate) "C10"),
  ("bad_type: a quota below 1/2, and cautiousness above the number of agents",
    errStarts ({ base with T := #[#[(0, 1/4), (0, 1/4)], #[(0, 1), (0, 1)]] }.validate) "bad_type"
      && errStarts ({ base with T := #[#[(3, 1), (3, 1)], #[(0, 1), (0, 1)]] }.validate) "bad_type"),
  ("Sets.ofList sorts and removes duplicates, like repeated Sets.ins",
    Sets.ofList [5, 1, 5, 3, 1] == [1, 3, 5]
      && Sets.ofList [] == ([] : Sets)
      && Sets.ofList [5, 1, 5, 3, 1] == [5, 1, 5, 3, 1].foldl (fun acc m => Sets.ins m acc) []),
  ("an unknown agent index is an error, not false",
    errStarts (sat base (.knows 5 .bot)) "unknown agent")]




/-! ## Helpers that need the formulas -/
abbrev F := EFormula
def atomF (p : String) : F := .atom p
def p : F := atomF "p"
def q : F := atomF "q"
def neg (f : F) : F := .not f
def conj (a b : F) : F := .and a b
def sat? (m : ESM) (f : F) : Option Mask := match sat m f with | .ok x => some x | .error _ => none
def valid? (m : ESM) (f : F) : Option Bool := match validIn m f with | .ok b => some b | .error _ => none

/-! ## The paper's §2.4 example

Agents 0 chatbot, 1 Wikipedia, 2 IMDb, 3 Amazon, 4 RT. Worlds 0 (p, q), 1 (q), 2 (neither); the
world where `p ∧ ¬q` would hold is absent, which is `Hyp1 = K_chatbot (p → q)`. Masks:
‖p‖ = 1, ‖¬p‖ = 6, ‖q‖ = 3, ‖¬q‖ = 4. The chatbot trusts Wikipedia and IMDb about p and ¬p, and
Amazon and RT about q and ¬q (`Hyp2`); no belief, no evidence (`Hyp3`); type `(cautiousness, 1)`. -/
def movie (cautious : Nat) : ESM where
  n := 3
  agents := #["chatbot", "wikipedia", "imdb", "amazon", "rt"]
  valuation := #[["p", "q"], ["q"], []]
  E := Array.replicate 5 (Array.replicate 3 7)
  D := Array.replicate 5 (Array.replicate 3 7)
  S := Array.replicate 5 (Array.replicate 5 (Array.replicate 3 []))
  C := (List.range 5).toArray.map fun i => (List.range 5).toArray.map fun j =>
    Array.replicate 3 (if i != 0 then [] else if j == 1 || j == 2 then [1, 6] else if j == 3 || j == 4 then [3, 4] else [])
  T := (List.range 5).toArray.map fun i => Array.replicate 3 (if i == 0 then (cautious, (1 : Rat)) else (1, 1))

def bel (f : F) : F := .believes 0 f
def undecidedQ : F := conj (neg (bel q)) (neg (bel (neg q)))

def movieCases : List (String × Bool) := [
  ("the movie model is an ESM",
    ok (movie 2).validate),
  ("§2.4: [!Amazon q][!RT ¬q][?chatbot q](¬B q ∧ ¬B ¬q) holds everywhere: discordant sources leave the chatbot undecided",
    valid? (movie 2) (.announce 3 q (.announce 4 (neg q) (.assess 0 q undecidedQ))) == some true),
  ("§2.4: [!Wikipedia p][!IMDb p][?chatbot p]B q holds everywhere",
    valid? (movie 2) (.announce 1 p (.announce 2 p (.assess 0 p (bel q)))) == some true),
  ("control: with only Wikipedia's announcement the chatbot (cautiousness 2) does not come to believe q anywhere",
    sat? (movie 2) (.announce 1 p (.assess 0 p (bel q))) == some 0),
  ("control: with cautiousness 1, Wikipedia alone suffices: B p and B q everywhere",
    valid? (movie 1) (.announce 1 p (.assess 0 p (conj (bel p) (bel q)))) == some true),
  ("control: without assessing, the announcements change evidence but not belief",
    sat? (movie 2) (.announce 1 p (.announce 2 p (bel q))) == some 0),
  ("an announcement is not truthful by definition: Amazon announcing ¬q where q holds still gives evidence",
    valid? (movie 2) (.announce 3 (neg q) (.evidence 0 3 (neg q))) == some true),
  ("T implies E after an announcement by that source, but not for a source the chatbot does not trust",
    sat? (movie 2) (.announce 3 p (.evidence 0 3 p)) == some 0),
  ("Def 6 revision: i believes ¬p, has sufficient reason for p (one source, type (1,1)); ?_i p replaces the belief set by ‖p‖ (B p after, ¬B p before)",
    (let m : ESM := { base with
       valuation := #[["p"], []],
       D := #[#[2, 2], #[3, 3]],
       S := #[#[#[[], []], #[[1], [1]]], #[#[[], []], #[[], []]]],
       C := #[#[#[[], []], #[[1], [1]]], #[#[[], []], #[[], []]]],
       T := #[#[(1, 1), (1, 1)], #[(0, 1), (0, 1)]] }
     ok m.validate
       && sat? m (.believes 0 (neg p)) == some 3          -- before: believes ¬p everywhere
       && sat? m (.reason 0 p) == some 3                  -- sufficient reason everywhere
       && sat? m (.assess 0 p (.believes 0 p)) == some 3  -- after: believes p (revision, not expansion)
       && sat? m (.assess 0 p (.believes 0 (neg p))) == some 0))]

/-! ## Pseudo-random ESMs -/
def lcg (x : Nat) : Nat := (x * 1103515245 + 12345) % 2147483648
def next : StateM Nat Nat := modifyGet fun x => let x' := lcg x; (x' / 65536, x')

def quotas : List Rat := [1 / 2, 2 / 3, 1]

/-- A random ESM with 3 worlds and 3 agents; every agent gets a random two-label partition (one class about a quarter of the time). -/
def randomESM (seed : Nat) : ESM :=
  let act : StateM Nat ESM := do
    let n := 3
    let ags := 3
    let mut labels : Array (Array Nat) := #[]
    for _ in List.range ags do
      let mut ls : Array Nat := #[]
      for _ in List.range n do ls := ls.push ((← next) % 2)
      labels := labels.push ls
    let classOf (i w : Nat) : Mask :=
      (List.range n).foldl (fun acc v => if labels[i]![v]! == labels[i]![w]! then acc ||| (1 <<< v) else acc) 0
    -- one random draw per (agent, class); the first world of each class decides
    let mut dTab : Array (Array Mask) := #[]
    let mut tTab : Array (Array (Nat × Rat)) := #[]
    let mut sTab : Array (Array (Array Sets)) := #[]
    let mut cTab : Array (Array (Array Sets)) := #[]
    for i in List.range ags do
      let mut dRow : Array Mask := #[]
      let mut tRow : Array (Nat × Rat) := #[]
      let mut dByClass : List (Mask × Mask) := []
      let mut tByClass : List (Mask × (Nat × Rat)) := []
      for w in List.range n do
        let k := classOf i w
        if (dByClass.find? (·.1 == k)).isNone then
          let r ← next
          let d := (r % (k + 1)) &&& k
          dByClass := (k, if d == 0 then k else d) :: dByClass
          let r2 ← next
          tByClass := (k, (r2 % (ags + 1), quotas[(r2 / 7) % 3]!)) :: tByClass
        dRow := dRow.push ((dByClass.find? (·.1 == k)).get!.2)
        tRow := tRow.push ((tByClass.find? (·.1 == k)).get!.2)
      dTab := dTab.push dRow
      tTab := tTab.push tRow
      let mut sRow : Array (Array Sets) := #[]
      let mut cRow : Array (Array Sets) := #[]
      for _ in List.range ags do
        let mut byClass : List (Mask × (Sets × Sets)) := []
        let mut sCol : Array Sets := #[]
        let mut cCol : Array Sets := #[]
        for w in List.range n do
          let k := classOf i w
          if (byClass.find? (·.1 == k)).isNone then
            let mut cs : Sets := []
            let mut ss : Sets := []
            for X in List.range (1 <<< n) do
              if X != 0 && Mask.subset X k then
                let r ← next
                if r % 3 == 0 then
                  cs := Sets.ins X cs
                  if (r / 3) % 2 == 0 then ss := Sets.ins X ss
            byClass := (k, (ss, cs)) :: byClass
          let (ss, cs) := (byClass.find? (·.1 == k)).get!.2
          sCol := sCol.push ss
          cCol := cCol.push cs
        sRow := sRow.push sCol
        cRow := cRow.push cCol
      sTab := sTab.push sRow
      cTab := cTab.push cRow
    let mut val : Array (List String) := #[]
    for _ in List.range n do
      let r ← next
      val := val.push ((if r % 2 == 0 then ["p"] else []) ++ (if (r / 2) % 2 == 0 then ["q"] else []))
    pure { n := n, agents := #["a0", "a1", "a2"], valuation := val,
           E := (List.range ags).toArray.map fun i => (List.range n).toArray.map fun w => classOf i w,
           D := dTab, S := sTab, C := cTab, T := tTab }
  (act.run seed).1

def seeds : List Nat := (List.range 120).map fun i => 1000 + 7919 * i
def props : List F := [p, neg p, q, conj p q]
def ids : List Nat := [0, 1, 2]

def forAllModels (check : ESM → Bool) : Bool := seeds.all fun s => check (randomESM s)
def validAll (m : ESM) (f : F) : Bool := (valid? m f) == some true

def randomCases : List (String × Bool) := [
  ("the generator builds ESMs (C1-C10 hold on all 120 seeds)",
    forAllModels fun m => ok m.validate),
  ("the random models are not degenerate: some have evidence, some have beliefs narrower than knowledge",
    (seeds.filter fun s => let m := randomESM s; m.agentIds.any fun i => m.agentIds.any fun j =>
        m.worlds.any fun w => !(m.s i j w).isEmpty).length > 60
      && (seeds.filter fun s => let m := randomESM s; m.agentIds.any fun i => m.worlds.any fun w =>
        m.d i w != m.e i w).length > 60),
  ("the corpus exercises R_i: in at least 20 of 120 seeds some agent has sufficient reason for some proposition at some world (so (3), (4), (8)-(11) and Proposition 1 are not vacuous)",
    (seeds.filter fun s => let m := randomESM s; ids.any fun i => props.any fun f =>
      match sat m (.reason i f) with | .ok mask => mask != 0 | .error _ => false).length ≥ 20),
  ("the corpus exercises Def 6: in at least 20 of 120 seeds some ?_i φ changes a belief set",
    (seeds.filter fun s => let m := randomESM s; ids.any fun i => props.any fun f =>
      match sat m f with
      | .ok fm => (assessModel m i fm).D != m.D
      | .error _ => false).length ≥ 20),
  ("(1) T_{i,j}φ → K̂_iφ  (2) E_{i,j}φ → K̂_iφ  (3) R_iφ → K̂_iφ  (4) ¬(R_iφ ∧ R_i¬φ), on 120 random ESMs",
    forAllModels fun m => ids.all fun i => props.all fun f =>
      validAll m (.not (conj (.reason i f) (.reason i (neg f))))
        && validAll m (.implies (.reason i f) (.hatK i f))
        && ids.all fun j => validAll m (.implies (.trust i j f) (.hatK i f))
          && validAll m (.implies (.evidence i j f) (.hatK i f))),
  ("(5) T_{i,j}φ → [!_jφ]E_{i,j}φ  (6) [−_{i,j}φ](¬E_{i,j}φ ∧ ¬T_{i,j}φ)  (7) K̂_iφ → [+_{i,j}φ]T_{i,j}φ",
    forAllModels fun m => ids.all fun i => ids.all fun j => props.all fun f =>
      validAll m (.implies (.trust i j f) (.announce j f (.evidence i j f)))
        && validAll m (.loseTrust i j f (conj (neg (.evidence i j f)) (neg (.trust i j f))))
        && validAll m (.implies (.hatK i f) (.relyOn i j f (.trust i j f)))),
  ("(8) R_iφ → [?_iφ]B_iφ  (9) R_i¬φ → [?_iφ]B_i¬φ",
    forAllModels fun m => ids.all fun i => props.all fun f =>
      validAll m (.implies (.reason i f) (.assess i f (.believes i f)))
        && validAll m (.implies (.reason i (neg f)) (.assess i f (.believes i (neg f))))),
  ("(10) sufficient reason plus K_i(φ → ψ) gives B_iψ after ?_iφ",
    forAllModels fun m => ids.all fun i => props.all fun f => props.all fun g =>
      validAll m (.implies
        (.or (conj (.reason i f) (.knows i (.implies f g))) (conj (.reason i (neg f)) (.knows i (.implies (neg f) g))))
        (.assess i f (.believes i g)))),
  ("(11) conservative expansion: an existing belief ψ survives ?_iφ when i expands",
    forAllModels fun m => ids.all fun i => props.all fun f => props.all fun g =>
      validAll m (.implies
        (.or (conj (conj (.reason i f) (neg (.believes i (neg f)))) (.believes i g))
             (conj (conj (.reason i (neg f)) (neg (.believes i f))) (.believes i g)))
        (.assess i f (.believes i g)))),
  ("Proposition 1: every update of a random ESM is again an ESM (C1-C10)",
    forAllModels fun m => ids.all fun i => props.all fun f =>
      match sat m f with
      | .error _ => false
      | .ok fm =>
        ok (announceModel m i fm).validate && ok (assessModel m i fm).validate
          && ids.all fun j => ok (loseTrustModel m i j fm).validate && ok (relyOnModel m i j fm).validate),
  ("R_i φ read directly equals the paper's literal disjunction over Evd × Evd × Evd × Qt, on 40 random ESMs",
    (seeds.take 40).all fun s => let m := randomESM s; ids.all fun i => props.all fun f =>
      (sat m (.reason i f)).toOption == (sat m (reasonLiteral m quotas i f)).toOption
        && (sat m (.reason i f)).isOk),
  ("(8) is not valid for a Moore-like φ = p ∧ ¬B_i p: the paper's stated counterexample",
    (let moore : F := conj p (neg (.believes 0 p))
     let m : ESM := { base with
       valuation := #[["p"], []],
       E := #[#[3, 3], #[3, 3]], D := #[#[3, 3], #[3, 3]],
       S := #[#[#[[], []], #[[1], [1]]], #[#[[], []], #[[], []]]],
       C := #[#[#[[], []], #[[1], [1]]], #[#[[], []], #[[], []]]],
       T := #[#[(1, 1), (1, 1)], #[(0, 1), (0, 1)]] }
     ok m.validate
       && valid? m (.implies (.reason 0 moore) (.assess 0 moore (.believes 0 moore))) == some false
       && valid? m (.implies (.reason 0 p) (.assess 0 p (.believes 0 p))) == some true))]


/-! ## The reduction axioms of Def 8 (Theorem 2's soundness half)

Each reduction axiom is checked as a validity of the *implemented* semantics on 120 random ESMs.
The proofs of Theorems 1-2 are not in the PRIMA paper (they are in an IRIT technical report that
is not local); this tests the axioms themselves, read off pp. 15-16 of the PDF. -/

def iff' (a b : F) : F := conj (.implies a b) (.implies b a)
/-- Test formulas ψ: atoms, negation, and each modal operator, on different agents. -/
def psis : List F := [p, neg q, .evidence 0 1 p, .trust 1 2 q, .knows 0 q, .believes 1 p,
  .evidence 2 0 (neg p), .trust 0 0 p]
def phis : List F := [p, neg p, q]
def typeFs : List F := [.type 0 0 1, .type 1 1 (1 / 2), .type 2 2 (2 / 3)]

/-- `lhs ↔ rhs` valid on every random ESM, for every `(i, j, φ, ψ)`. -/
def redAll (ax : Nat → Nat → F → F → F × F) : Bool :=
  forAllModels fun m => ids.all fun i => ids.all fun j => phis.all fun f => psis.all fun g =>
    let (l, r) := ax i j f g
    validAll m (iff' l r)

def reductionCases : List (String × Bool) := [
  ("Red for [!_iφ]: p, type, ¬, ∧, K_j, B_j, E_{j,k} (k ≠ i) and T_{j,k} commute with the update",
    redAll (fun i j f g => (.announce i f (.not g), .not (.announce i f g)))
      && redAll (fun i j f g => (.announce i f (conj g p), conj (.announce i f g) (.announce i f p)))
      && redAll (fun i j f g => (.announce i f p, p))
      && typeFs.all (fun t => redAll (fun i j f _ => (.announce i f t, t)))
      && redAll (fun i j f g => (.announce i f (.knows j g), .knows j (.announce i f g)))
      && redAll (fun i j f g => (.announce i f (.believes j g), .believes j (.announce i f g)))
      && redAll (fun i j f g => if i == j then (.top, .top)
          else (.announce i f (.evidence 0 j g), .evidence 0 j (.announce i f g)))
      && redAll (fun i j f g => (.announce i f (.trust 0 j g), .trust 0 j (.announce i f g)))),
  ("Red!E_{j,i}: [!_iφ]E_{j,i}ψ ↔ ((T_{j,i}φ → (E_{j,i}[!_iφ]ψ ∨ K_j(φ ↔ [!_iφ]ψ))) ∧ (¬T_{j,i}φ → E_{j,i}[!_iφ]ψ))",
    redAll (fun i j f g => (.announce i f (.evidence j i g),
      conj (.implies (.trust j i f) (.or (.evidence j i (.announce i f g)) (.knows j (iff' f (.announce i f g)))))
        (.implies (.not (.trust j i f)) (.evidence j i (.announce i f g)))))),
  ("Red for [−_{i,j}φ]: K_k, B_k commute; E_{k,l} and T_{k,l} commute unless (k,l) = (i,j); E_{i,j}ψ ↔ (E_{i,j}[−]ψ ∧ ¬K_i(φ ↔ [−]ψ)), same for T_{i,j} (the paper prints ∨; see the next case)",
    redAll (fun i j f g => (.loseTrust i j f (.knows 1 g), .knows 1 (.loseTrust i j f g)))
      && redAll (fun i j f g => (.loseTrust i j f (.believes 2 g), .believes 2 (.loseTrust i j f g)))
      && redAll (fun i j f g => if i == 0 && j == 1 then (.top, .top)
          else (.loseTrust i j f (.evidence 0 1 g), .evidence 0 1 (.loseTrust i j f g)))
      && redAll (fun i j f g => if i == 1 && j == 2 then (.top, .top)
          else (.loseTrust i j f (.trust 1 2 g), .trust 1 2 (.loseTrust i j f g)))
      && redAll (fun i j f g => (.loseTrust i j f (.evidence i j g),
          conj (.evidence i j (.loseTrust i j f g)) (.not (.knows i (iff' f (.loseTrust i j f g))))))
      && redAll (fun i j f g => (.loseTrust i j f (.trust i j g),
          conj (.trust i j (.loseTrust i j f g)) (.not (.knows i (iff' f (.loseTrust i j f g))))))),
  ("the paper's Red−E_{i,j} and Red−T_{i,j} as printed (p. 15) join the two sides with ∨, which is not valid: it contradicts the paper's own validity (6), [−_{i,j}φ](¬E_{i,j}φ ∧ ¬T_{i,j}φ). With ∧, as tested above, both are valid. The printed ∨ fails on some random ESM",
    !(redAll (fun i j f g => (.loseTrust i j f (.evidence i j g),
          .or (.evidence i j (.loseTrust i j f g)) (.not (.knows i (iff' f (.loseTrust i j f g)))))))
      && !(redAll (fun i j f g => (.loseTrust i j f (.trust i j g),
          .or (.trust i j (.loseTrust i j f g)) (.not (.knows i (iff' f (.loseTrust i j f g)))))))),
  ("Red for [+_{i,j}φ]: K_k, B_k, E_{k,l} commute; T_{k,l} commutes unless (k,l) = (i,j); [+]T_{i,j}ψ ↔ ((K̂_iφ → (T_{i,j}[+]ψ ∨ K_i(φ ↔ [+]ψ))) ∧ (K_i¬φ → T_{i,j}[+]ψ))",
    redAll (fun i j f g => (.relyOn i j f (.knows 1 g), .knows 1 (.relyOn i j f g)))
      && redAll (fun i j f g => (.relyOn i j f (.believes 2 g), .believes 2 (.relyOn i j f g)))
      && redAll (fun i j f g => (.relyOn i j f (.evidence 0 1 g), .evidence 0 1 (.relyOn i j f g)))
      && redAll (fun i j f g => if i == 1 && j == 2 then (.top, .top)
          else (.relyOn i j f (.trust 1 2 g), .trust 1 2 (.relyOn i j f g)))
      && redAll (fun i j f g => (.relyOn i j f (.trust i j g),
          conj (.implies (.hatK i f) (.or (.trust i j (.relyOn i j f g)) (.knows i (iff' f (.relyOn i j f g)))))
            (.implies (.knows i (neg f)) (.trust i j (.relyOn i j f g)))))),
  ("Red for [?_iφ]: K_j commutes; B_j commutes for j ≠ i; E and T commute; [?_iφ]B_iψ ↔ the α₁-α₅ cases",
    redAll (fun i j f g => (.assess i f (.knows j g), .knows j (.assess i f g)))
      && redAll (fun i j f g => if i == j then (.top, .top)
          else (.assess i f (.believes j g), .believes j (.assess i f g)))
      && redAll (fun i j f g => (.assess i f (.evidence 0 j g), .evidence 0 j (.assess i f g)))
      && redAll (fun i j f g => (.assess i f (.trust 0 j g), .trust 0 j (.assess i f g)))
      && redAll (fun i _ f g =>
        let a1 := conj (.reason i f) (neg (.believes i f))
        let a2 := conj (.reason i (neg f)) (neg (.believes i (neg f)))
        let a3 := conj (.reason i f) (.believes i (neg f))
        let a4 := conj (.reason i (neg f)) (.believes i f)
        let a5 := conj (neg a1) (conj (neg a2) (conj (neg a3) (neg a4)))
        (.assess i f (.believes i g),
          conj (.implies a1 (.believes i (.implies f (.assess i f g))))
            (conj (.implies a2 (.believes i (.implies (neg f) (.assess i f g))))
              (conj (.implies a3 (.knows i (.implies f (.assess i f g))))
                (conj (.implies a4 (.knows i (.implies (neg f) (.assess i f g))))
                  (.implies a5 (.believes i (.assess i f g)))))))))]

def cases : List (String × Bool) := constructorCases ++ movieCases ++ randomCases ++ reductionCases

end EvidenceTrustTests
