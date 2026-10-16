/-!
# Gamen.EvidenceTrust

DL-BET: the dynamic logic of belief, evidence and trust of Liu & Lorini, *Reasoning About
Belief, Evidence and Trust in a Multi-agent Setting*, PRIMA 2017 (local copy
`~/Projects/Logic/Bergen/Bergen/lit/pdfs/liu2017belief.pdf`). Lean-only. Issue #3, item 4.

Agents receive evidence from sources they trust (`E_{i,j}φ`, `T_{i,j}φ`), judge whether they have
*sufficient reason* to believe a claim (`R_iφ`: more source agents for `φ` than for `¬φ`, the ratio
at least their quota, and at least their cautiousness many), and revise or expand their beliefs
when they assess it (`?_iφ`). Discordant sources leave the agent suspending judgment: the paper's
Amazon-versus-RT example (§2.4) is a test.

Definitions are checked against the PDF pages, not the text extract, which loses overlines and
slashes: Def 1 (ESM, p. 6; C1-C10, p. 7), Def 2 (truth, p. 8), Defs 3-6 (the four updates, p. 9), the
abbreviations `E_i^{≥x}`, `E_i^x`, `R_i` (p. 6), validities (1)-(11) (p. 11).
Two points where the extract was wrong: **C8 is `∅ ∉ C(i,j,v)`**, and **Def 5's guard is `K̂_iφ`**.

* A set of worlds is a bitmask; `‖φ‖_{i,w} = ⟦φ⟧ ∩ E_i(w)` is how evidence and trust sets are
  identified, so equality of masks is equality of evidence.
* An update evaluates its formula `φ` in the model *before* the update (Defs 3-6), then the
  continuation in the updated model; each update is a pure model transformer given `⟦φ⟧`.
* `R_iφ` is evaluated directly (`reasonAt`), counting source agents `j ∈ Agt`, `i` included;
  `reasonLiteral` builds the paper's disjunction over `Evd × Evd × Evd × Qt` for a cross-check test.
* C7 is printed with free `w, v` (`X ∈ C(i,j,v) → X ⊆ E_i(w)`); read literally with two classes it
  would force `C = ∅` (given C8), so `validate` checks it within the world: `X ∈ C(i,j,w) → X ⊆ E_i(w)`.
* An announcement has no truth precondition, unlike public announcement: `i` may announce a falsehood.

Not covered: the completeness proofs of Theorems 1-2 are not in the PRIMA paper (they are in an IRIT
technical report that is not local), so they are not read; the reduction axioms of Def 8 are tested
as validities of this semantics (`Tests/EvidenceTrust.lean`; the paper prints `∨` in Red−E_{i,j} and
Red−T_{i,j} where `∧` is valid); group
announcements and trust (Perrotin, Galimullin, Canu & Alechina, "Public Group Announcements and Trust in Doxastic Logic"; venue and year unverified) and trust-based belief revision (Hunter) are other
components. Tests: `Tests/EvidenceTrust.lean` (constructor, the §2.4 example, validities (1)-(11),
Proposition 1 on random models).
-/
namespace Gamen
namespace EvidenceTrust

/-- A set of worlds as a bitmask: world `w` is bit `w`. -/
abbrev Mask := Nat

def Mask.mem (m : Mask) (w : Nat) : Bool := m.testBit w
def Mask.full (n : Nat) : Mask := (1 <<< n) - 1
def Mask.subset (a b : Mask) : Bool := a &&& b == a

/-- A set of sets of worlds, kept sorted and duplicate-free so `==` is set equality. -/
abbrev Sets := List Mask

def Sets.ins (m : Mask) (l : Sets) : Sets :=
  if l.contains m then l else (m :: l).mergeSort (· ≤ ·)

def Sets.del (m : Mask) (l : Sets) : Sets := l.filter (· != m)

/-- Sort and drop duplicates in one pass: the same set as folding `Sets.ins` over the list, but
`O(k log k)` rather than `O(k² log k)` (a request may list thousands of sets). -/
def Sets.ofList (l : List Mask) : Sets :=
  let sorted := l.mergeSort (· ≤ ·)
  (sorted.foldl (fun (acc : List Mask) m => match acc with
    | a :: _ => if a == m then acc else m :: acc
    | [] => [m]) []).reverse

/-- Evidence source model (Def 1). Agents and worlds are indexed from 0; `E i w` is agent
`i`'s information set at `w`, `D i w` its belief set, `S i j w` the evidence `j` gave `i`,
`C i j w` the sets `i` trusts `j` about, `T i w` the type (cautiousness, quota). -/
structure ESM where
  n : Nat
  agents : Array String
  valuation : Array (List String)
  E : Array (Array Mask)
  D : Array (Array Mask)
  S : Array (Array (Array Sets))
  C : Array (Array (Array Sets))
  T : Array (Array (Nat × Rat))

def ESM.nAgents (m : ESM) : Nat := m.agents.size
def ESM.worlds (m : ESM) : List Nat := List.range m.n
def ESM.agentIds (m : ESM) : List Nat := List.range m.nAgents

def ESM.e (m : ESM) (i w : Nat) : Mask := (m.E[i]?.bind (·[w]?)).getD 0
def ESM.d (m : ESM) (i w : Nat) : Mask := (m.D[i]?.bind (·[w]?)).getD 0
def ESM.s (m : ESM) (i j w : Nat) : Sets := (((m.S[i]?).bind (·[j]?)).bind (·[w]?)).getD []
def ESM.c (m : ESM) (i j w : Nat) : Sets := (((m.C[i]?).bind (·[j]?)).bind (·[w]?)).getD []
def ESM.t (m : ESM) (i w : Nat) : Nat × Rat := (m.T[i]?.bind (·[w]?)).getD (0, 1)

/-- Check the conditions of Def 1 (C1-C10, with C8 as printed in the PDF: `∅ ∉ C`) and the
ranges the language needs. The message starts with the name of the violated condition. -/
def ESM.validate (m : ESM) : Except String Unit := do
  let ids := m.agentIds
  let ws := m.worlds
  let full := Mask.full m.n
  unless m.valuation.size == m.n do throw "shape: valuation has the wrong length"
  unless m.E.size == m.nAgents && m.D.size == m.nAgents && m.T.size == m.nAgents
      && m.S.size == m.nAgents && m.C.size == m.nAgents do throw "shape: per-agent tables have the wrong length"
  for i in ids do
    unless (m.E[i]!).size == m.n && (m.D[i]!).size == m.n && (m.T[i]!).size == m.n do
      throw "shape: a per-world table has the wrong length"
    unless (m.S[i]!).size == m.nAgents && (m.C[i]!).size == m.nAgents do
      throw "shape: an evidence or trust table has the wrong length"
    for j in ids do
      unless (m.S[i]![j]!).size == m.n && (m.C[i]![j]!).size == m.n do
        throw "shape: an evidence or trust table has the wrong length"
  for i in ids do
    for w in ws do
      unless Mask.subset (m.e i w) full do throw s!"C1: E {m.agents[i]!} {w} names a world out of range"
      unless (m.e i w).testBit w do throw s!"C1: E {m.agents[i]!} is not reflexive at world {w}"
      for v in ws do
        if (m.e i w).testBit v then
          unless (m.e i v).testBit w do throw s!"C1: E {m.agents[i]!} is not symmetric ({w},{v})"
          unless m.e i w == m.e i v do throw s!"C1: E {m.agents[i]!} is not transitive ({w},{v})"
          unless m.d i w == m.d i v do throw s!"C4: D {m.agents[i]!} differs on worlds {w},{v} of one class"
          unless m.t i w == m.t i v do throw s!"C10: the type of {m.agents[i]!} differs on worlds {w},{v} of one class"
          for j in ids do
            unless m.s i j w == m.s i j v do throw s!"C5: S differs on worlds {w},{v} of one class"
            unless m.c i j w == m.c i j v do throw s!"C6: C differs on worlds {w},{v} of one class"
      if m.d i w == 0 then throw s!"C2: {m.agents[i]!} has no possible world at {w}"
      unless Mask.subset (m.d i w) (m.e i w) do throw s!"C3: D {m.agents[i]!} {w} is not inside E"
      let (x, y) := m.t i w
      if x > m.nAgents then throw s!"bad_type: cautiousness {x} of {m.agents[i]!} exceeds the number of agents"
      if y < (1 : Rat) / 2 || y > 1 then throw s!"bad_type: quota {y} of {m.agents[i]!} is outside [1/2, 1]"
      for j in ids do
        for X in m.c i j w do
          unless Mask.subset X (m.e i w) do throw s!"C7: a trusted set of {m.agents[i]!} is not inside E at {w}"
          if X == 0 then throw s!"C8: {m.agents[i]!} trusts {m.agents[j]!} about the empty set at {w}"
        for X in m.s i j w do
          unless (m.c i j w).contains X do throw s!"C9: {m.agents[i]!} has evidence from {m.agents[j]!} it does not trust, at {w}"

/-- DL-BET formulas. Agents are indices. The four update forms carry their continuation:
`announce i φ ψ` is `[!_i φ]ψ`, `loseTrust i j φ ψ` is `[−_{i,j} φ]ψ`, `relyOn i j φ ψ` is
`[+_{i,j} φ]ψ`, `assess i φ ψ` is `[?_i φ]ψ`. `reason i φ` is `R_i φ`, evaluated directly
(see `reasonAt`); `reasonLiteral` builds the paper's disjunction for cross-checking. -/
inductive EFormula where
  | atom (p : String)
  | bot
  | not (f : EFormula)
  | and (l r : EFormula)
  | type (i x : Nat) (y : Rat)
  | knows (i : Nat) (f : EFormula)
  | believes (i : Nat) (f : EFormula)
  | evidence (i j : Nat) (f : EFormula)
  | trust (i j : Nat) (f : EFormula)
  | reason (i : Nat) (f : EFormula)
  | announce (i : Nat) (f g : EFormula)
  | loseTrust (i j : Nat) (f g : EFormula)
  | relyOn (i j : Nat) (f g : EFormula)
  | assess (i : Nat) (f g : EFormula)

namespace EFormula
def top : EFormula := .not .bot
def or (l r : EFormula) : EFormula := .not (.and (.not l) (.not r))
def implies (l r : EFormula) : EFormula := .or (.not l) r
def hatK (i : Nat) (f : EFormula) : EFormula := .not (.knows i (.not f))
def hatB (i : Nat) (f : EFormula) : EFormula := .not (.believes i (.not f))
def bigOr (fs : List EFormula) : EFormula := fs.foldr or .bot
def bigAnd (fs : List EFormula) : EFormula := fs.foldr .and top
end EFormula

/-- Does agent `i`, at world `w`, hold the evidence `‖φ‖_{i,w}` from source `j`? `fm` is `⟦φ⟧`. -/
def hasEvidence (m : ESM) (i j w : Nat) (fm : Mask) : Bool :=
  (m.s i j w).contains (fm &&& m.e i w)

/-- `R_i φ` at `w` (§2.1, read off the PDF): with `T(i,w) = (x'', y)`, `x` the number of agents
`j` with `E_{i,j} φ` and `x'` the number with `E_{i,j} ¬φ`, `R_i φ` iff `x > x'`,
`x/(x+x') ≥ y` and `x ≥ x''`. Equal to the paper's disjunction (`reasonLiteral`). -/
def reasonAt (m : ESM) (i w : Nat) (fm : Mask) : Bool :=
  let nfm := Mask.full m.n ^^^ fm
  let x := (m.agentIds.filter fun j => hasEvidence m i j w fm).length
  let x' := (m.agentIds.filter fun j => hasEvidence m i j w nfm).length
  let (xt, y) := m.t i w
  decide (x > x') && decide ((x : Rat) / ((x + x' : Nat) : Rat) ≥ y) && decide (x ≥ xt)

/-- Def 3, `!_i φ`: every `j` who trusts `i` about `φ` gains `‖φ‖_{j,w}` as evidence from `i`.
There is no truth precondition. -/
def announceModel (m : ESM) (i : Nat) (fm : Mask) : ESM :=
  { m with S := m.S.mapIdx fun j row => row.mapIdx fun k col =>
      if k == i then col.mapIdx fun w sets =>
        let X := fm &&& m.e j w
        if (m.c j i w).contains X then sets.ins X else sets
      else col }

/-- Def 4, `−_{i,j} φ`: remove `‖φ‖_{i,w}` from `S(i,j,w)` and `C(i,j,w)`. -/
def loseTrustModel (m : ESM) (i j : Nat) (fm : Mask) : ESM :=
  let upd (t : Array (Array (Array Sets))) := t.mapIdx fun k row => row.mapIdx fun l col =>
    if k == i && l == j then col.mapIdx fun w sets => sets.del (fm &&& m.e i w) else col
  { m with S := upd m.S, C := upd m.C }

/-- Def 5, `+_{i,j} φ`: add `‖φ‖_{i,w}` to `C(i,j,w)` where `K̂_i φ` holds at `w` (the PDF's
guard; the text extract loses the hat). -/
def relyOnModel (m : ESM) (i j : Nat) (fm : Mask) : ESM :=
  { m with C := m.C.mapIdx fun k row => row.mapIdx fun l col =>
      if k == i && l == j then col.mapIdx fun w sets =>
        let X := fm &&& m.e i w
        if X != 0 then sets.ins X else sets
      else col }

/-- Def 6, `?_i φ`: expansion or revision of `D(i,·)` when `i` has sufficient reason. -/
def assessModel (m : ESM) (i : Nat) (fm : Mask) : ESM :=
  let nfm := Mask.full m.n ^^^ fm
  { m with D := m.D.mapIdx fun j row =>
      if j != i then row else row.mapIdx fun w dw =>
        let rP := reasonAt m i w fm
        let rN := reasonAt m i w nfm
        let bP := Mask.subset dw fm      -- B_i φ
        let bN := Mask.subset dw nfm     -- B_i ¬φ
        if rP && !bN then dw &&& fm
        else if rN && !bP then dw &&& nfm
        else if rP && bN then m.e i w &&& fm
        else if rN && bP then m.e i w &&& nfm
        else dw }

private def agentOk (m : ESM) (i : Nat) : Except String Unit :=
  if i < m.nAgents then pure () else throw s!"unknown agent index {i}"

/-- The set of worlds satisfying `f` (Def 2). Updates evaluate their formula in the model
before the update, then the continuation in the updated model. -/
def sat : ESM → EFormula → Except String Mask
  | m, .atom p => pure ((m.worlds.filter fun w => (m.valuation[w]?.getD []).contains p).foldl
      (fun acc w => acc ||| (1 <<< w)) 0)
  | _, .bot => pure 0
  | m, .not f => do pure (Mask.full m.n ^^^ (← sat m f))
  | m, .and l r => do pure ((← sat m l) &&& (← sat m r))
  | m, .type i x y => do
    agentOk m i
    pure ((m.worlds.filter fun w => m.t i w == (x, y)).foldl (fun acc w => acc ||| (1 <<< w)) 0)
  | m, .knows i f => do
    agentOk m i; let fm ← sat m f
    pure ((m.worlds.filter fun w => Mask.subset (m.e i w) fm).foldl (fun acc w => acc ||| (1 <<< w)) 0)
  | m, .believes i f => do
    agentOk m i; let fm ← sat m f
    pure ((m.worlds.filter fun w => Mask.subset (m.d i w) fm).foldl (fun acc w => acc ||| (1 <<< w)) 0)
  | m, .evidence i j f => do
    agentOk m i; agentOk m j; let fm ← sat m f
    pure ((m.worlds.filter fun w => hasEvidence m i j w fm).foldl (fun acc w => acc ||| (1 <<< w)) 0)
  | m, .trust i j f => do
    agentOk m i; agentOk m j; let fm ← sat m f
    pure ((m.worlds.filter fun w => (m.c i j w).contains (fm &&& m.e i w)).foldl
      (fun acc w => acc ||| (1 <<< w)) 0)
  | m, .reason i f => do
    agentOk m i; let fm ← sat m f
    pure ((m.worlds.filter fun w => reasonAt m i w fm).foldl (fun acc w => acc ||| (1 <<< w)) 0)
  | m, .announce i f g => do
    agentOk m i; let fm ← sat m f; sat (announceModel m i fm) g
  | m, .loseTrust i j f g => do
    agentOk m i; agentOk m j; let fm ← sat m f; sat (loseTrustModel m i j fm) g
  | m, .relyOn i j f g => do
    agentOk m i; agentOk m j; let fm ← sat m f; sat (relyOnModel m i j fm) g
  | m, .assess i f g => do
    agentOk m i; let fm ← sat m f; sat (assessModel m i fm) g

/-- `(M, w) ⊨ f`. -/
def holdsAt (m : ESM) (f : EFormula) (w : Nat) : Except String Bool := do
  pure ((← sat m f).testBit w)

/-- `f` is true at every world. -/
def validIn (m : ESM) (f : EFormula) : Except String Bool := do
  pure ((← sat m f) == Mask.full m.n)

/-- The sublists of `l` with exactly `k` elements. -/
def subsetsOfSize : Nat → List Nat → List (List Nat)
  | 0, _ => [[]]
  | _ + 1, [] => []
  | k + 1, a :: rest => (subsetsOfSize k rest).map (a :: ·) ++ subsetsOfSize (k + 1) rest

/-- `E_i^{≥x} φ` as the paper's disjunction over subsets of agents of size `x`. -/
def atLeast (m : ESM) (i x : Nat) (f : EFormula) : EFormula :=
  if x == 0 then .top
  else EFormula.bigOr ((subsetsOfSize x m.agentIds).map fun J =>
    EFormula.bigAnd (J.map fun j => .evidence i j f))

/-- `R_i φ` as the paper's literal disjunction, over the quotas `qt` (which must contain every
agent's quota). Used only to cross-check `reasonAt`. -/
def reasonLiteral (m : ESM) (qt : List Rat) (i : Nat) (f : EFormula) : EFormula :=
  let evd := List.range (m.nAgents + 1)
  let exactly (x : Nat) (g : EFormula) := EFormula.and (atLeast m i x g) (.not (atLeast m i (x + 1) g))
  EFormula.bigOr (evd.flatMap fun (x : Nat) => evd.flatMap fun (x' : Nat) => evd.flatMap fun (x'' : Nat) =>
    qt.filterMap fun y =>
    if x > x' && decide ((x : Rat) / ((x + x' : Nat) : Rat) ≥ y) && x ≥ x'' then
      some (EFormula.bigAnd [exactly x f, exactly x' (.not f), .type i x'' y])
    else none)

end EvidenceTrust
end Gamen
