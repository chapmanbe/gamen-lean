import Gamen.Formula
import Gamen.DeonticStit.Sequent
import Std.Data.TreeSet

/-!
# Gamen.DeonticStit.Rules

Port of `gamen-hs/src/Gamen/DeonticStit/Rules.hs`: bottom-up inference
rules for the labeled sequent calculus G3DS^k_n (Lyon & van Berkel,
"Proof Theory and Decision Procedures for Deontic STIT Logics", *Journal of
Artificial Intelligence Research* 81 (2024), pp. 837–876, Figure 2). One
function per rule, plus the closure check `isClosedSequent`.

Each rule has type `Rule = Sequent → Option RuleApp` and returns `none` when
the rule's saturation condition is already satisfied (no candidate
principal formula or relational pattern). When applicable it returns
`some` a `RuleApp` carrying the premise sequents and any fresh labels
introduced, so the proof-search driver can record them in the generation
tree.

Coverage, as in the Haskell:

* `isClosedSequent` — encodes (id)
* logical, non-generating: `applyAnd` (∧, two premises), `applyOr` (∨),
  `applyDiamond` (◇), `applyChoiceDiamond` (⟨i⟩), `applyPermitted` (⊖_i)
* logical, generating: `applyBox` (□), `applyStit` ([i]), `applyOught` (⊗_i)
* frame rules, non-generating: `applyRef` (Ref_i), `applyEuc` (Euc_i),
  `applyD3` (D3_i)
* frame rule, generating: `applyD2` (D2_i)
* branching frame rule: `applyAPC` (APC^k_i, only when k > 0)

The (IOA) rule is orchestrated via IoaOp (Definition 11), which needs
generation-tree IOA-label tracking and lives with the saturation driver.

Every "Algorithm 1, lines …", "Figure …", "Definition …", "Remark …", and
"Lemma …" reference below was checked against `pdftotext
notes/LyonBerkel2024.pdf -`. No B&D citations apply to this module. The
Haskell has no `error` calls, so nothing here needs `Except`.

Iteration order matters for which candidate a rule picks: Haskell walks
`Set.toList` in ascending `Ord` order; the Lean walks `Std.TreeSet.toList`
in ascending derived-`Ord` order, which for `Label`, `RelAtom`,
`LabFormula`, and `Formula` compares constructor index first and then
fields left to right, as Haskell's derived `Ord` does.
-/
namespace Gamen

-- ====================================================================
-- Rule type
-- ====================================================================

/-- The result of a successful rule application.

`raPremises` holds one or more sequents whose joint provability entails the
conclusion's provability. A two-element list denotes a branching rule like
(∧), or the branches of (APC).

Generating rules record introduced labels in `raFreshLabels` and, for
tree-node labels, their parent in `raParents` (zipped one-to-one with
`raFreshLabels`). The proof-search driver adds `(parent, child)` edges to
the generation tree from this list.

IoaOp-introduced labels (the (IOA) rule of Definition 11) are recorded
separately in `raIoaLabels`, since per Remark 17 they are *not* tree
nodes. -/
structure RuleApp where
  raPremises : List Sequent
  raFreshLabels : List Label
  raParents : List Label
  raIoaLabels : List Label
  deriving BEq, Repr

/-- A bottom-up rule: scans a sequent for an applicable principal formula or
relational pattern and produces premises. Returns `none` when saturated.

Haskell's `Rule`; namespaced as `DeonticStit.Rule` because `Gamen.Rule` is
already the tableau rule type (`Tableau.lean`), and both modules are
imported together (e.g. by `Tests/Main.lean`). -/
abbrev DeonticStit.Rule := Sequent → Option RuleApp

/-- A non-generating rule application: only premises, no fresh labels and
no generation-tree edges. -/
def nonGenApp (ps : List Sequent) : RuleApp := ⟨ps, [], [], []⟩

/-- A single-fresh-label rule application. The fresh `child` is parented by
`parent` in the generation tree. -/
def freshApp (ps : List Sequent) (parent child : Label) : RuleApp :=
  ⟨ps, [child], [parent], []⟩

-- ====================================================================
-- Search helpers (unexported in the Haskell)
-- ====================================================================

/-- First `some` result over a list (Haskell `lookupOne`). -/
private def lookupOne (f : α → Option β) (xs : List α) : Option β := xs.findSome? f

/-- First `some` result over a `TreeSet`, in ascending order (Haskell
`findFirst`). -/
private def findFirst [Ord α] (f : α → Option β) (s : Std.TreeSet α) : Option β :=
  lookupOne f s.toList

-- ====================================================================
-- (id) — closure
-- ====================================================================

/-- Is the sequent closed under the (id) rule (Lyon & van Berkel,
Figure 2)? Γ is the *succedent* (right of `⇒`), read disjunctively, so the
sequent is provable — "closed" — iff either:

* some label `w` carries both `w:p` and `w:¬p`; or
* some label carries `⊤` (represented in NNF as `¬⊥`). A disjunction with a
  valid disjunct is valid.

Note the polarity: it is positive `⊤` that closes, not positive `⊥`. `⊥`
on the succedent is inert (a false disjunct), so `□⊥` must stay open. -/
def isClosedSequent (s : Sequent) : Bool :=
  s.gamma.toList.any fun
    | ⟨w, .atomF a⟩ => s.gamma.contains ⟨w, .not (.atomF a)⟩
    | ⟨_, .not .bot⟩ => true   -- positive ⊤
    | _ => false

-- ====================================================================
-- (∧) — conjunction (branching)
-- ====================================================================

/-- (∧) rule. From `w:φ∧ψ` in Γ produce two premises: one with `w:φ` added,
one with `w:ψ` added. Per the Algorithm 1 saturation condition (line 24)
the rule fires only when *neither* conjunct is already in Γ; firing when
just one is missing would reproduce the input on that branch and loop the
driver. -/
def applyAnd : DeonticStit.Rule := fun s =>
  let conjCandidate : LabFormula → Option (Label × Formula × Formula)
    | ⟨w, .and l r⟩ =>
      if !s.gamma.contains ⟨w, l⟩ && !s.gamma.contains ⟨w, r⟩ then some (w, l, r) else none
    | _ => none
  match findFirst conjCandidate s.gamma with
  | none => none
  | some (w, l, r) =>
    let leftPremise := addFormula ⟨w, l⟩ s
    let rightPremise := addFormula ⟨w, r⟩ s
    some (nonGenApp [leftPremise, rightPremise])

-- ====================================================================
-- (∨) — disjunction (non-branching)
-- ====================================================================

/-- (∨) rule. From `w:φ∨ψ` in Γ produce one premise with both `w:φ` and
`w:ψ` added (Algorithm 1, lines 21–23). -/
def applyOr : DeonticStit.Rule := fun s =>
  let disjCandidate : LabFormula → Option (Label × Formula × Formula)
    | ⟨w, .or l r⟩ =>
      if !s.gamma.contains ⟨w, l⟩ || !s.gamma.contains ⟨w, r⟩ then some (w, l, r) else none
    | _ => none
  match findFirst disjCandidate s.gamma with
  | none => none
  | some (w, l, r) =>
    some (nonGenApp [addFormula ⟨w, l⟩ (addFormula ⟨w, r⟩ s)])

-- ====================================================================
-- (◇) — modal possibility (non-generating; iterates over labels)
-- ====================================================================

/-- (◇) rule. From `w:◇φ` in Γ, for any existing label `u ∈ Lab(Λ)` such
that `u:φ ∉ Γ`, add `u:φ` (Algorithm 1, lines 32–34). Picks the first such
pair found. -/
def applyDiamond : DeonticStit.Rule := fun s =>
  let allLabels := (labels s).toList
  let candidate : LabFormula → Option (Label × Formula)
    | ⟨_, .diamond phi⟩ =>
      lookupOne (fun u => if !s.gamma.contains ⟨u, phi⟩ then some (u, phi) else none) allLabels
    | _ => none
  match lookupOne candidate s.gamma.toList with
  | none => none
  | some (u, phi) => some (nonGenApp [addFormula ⟨u, phi⟩ s])

-- ====================================================================
-- (⟨i⟩) — choice diamond (non-generating; requires R_[i]wu)
-- ====================================================================

/-- (⟨i⟩) rule. With `R_[i]wu ∈ ℛ` and `w:⟨i⟩φ ∈ Γ`, add `u:φ` and
`u:⟨i⟩φ` (Algorithm 1, lines 35–37). The driver pairs this with the
admissible (⟨i⟩*) variant when `w` is an IOA-label (Figure 4); this basic
rule covers the saturation condition (C_⟨i⟩) for non-IOA labels. -/
def applyChoiceDiamond : DeonticStit.Rule := fun s =>
  let allLabels := (labels s).toList
  let candidate : LabFormula → Option (Label × String × Formula)
    | ⟨w, .choiceDiamond agent phi⟩ =>
      lookupOne
        (fun u =>
          if hasRel (.choice agent w u) s
              && (!s.gamma.contains ⟨u, phi⟩
                  || !s.gamma.contains ⟨u, .choiceDiamond agent phi⟩)
          then some (u, agent, phi) else none)
        allLabels
    | _ => none
  match lookupOne candidate s.gamma.toList with
  | none => none
  | some (u, agent, phi) =>
    some (nonGenApp [addFormula ⟨u, phi⟩ (addFormula ⟨u, .choiceDiamond agent phi⟩ s)])

-- ====================================================================
-- (⊖_i) — permitted (non-generating; requires I_⊗_i u)
-- ====================================================================

/-- (⊖_i) rule. With `I_⊗_i u ∈ ℛ` and `w:⊖_i φ ∈ Γ`, add `u:φ`
(Algorithm 1, lines 38–40). The principal formula is preserved. -/
def applyPermitted : DeonticStit.Rule := fun s =>
  let allLabels := (labels s).toList
  let candidate : LabFormula → Option (Label × Formula)
    | ⟨_, .permitted agent phi⟩ =>
      lookupOne
        (fun u =>
          if hasRel (.ideal agent u) s && !s.gamma.contains ⟨u, phi⟩
          then some (u, phi) else none)
        allLabels
    | _ => none
  match lookupOne candidate s.gamma.toList with
  | none => none
  | some (u, phi) => some (nonGenApp [addFormula ⟨u, phi⟩ s])

-- ====================================================================
-- (□) — necessity (generating)
-- ====================================================================

/-- (□) rule. From `w:□φ` in Γ, when no existing label has `φ` in Γ,
introduce a fresh label `v` and add `v:φ` (Algorithm 1, lines 41–43; the
(□*) relabel optimization is omitted, as in the Haskell). The principal
`w:□φ` is preserved; saturation is reached once some label has `φ`. The
fresh label is parented by the principal label `w`. -/
def applyBox : DeonticStit.Rule := fun s =>
  let allLabels := (labels s).toList
  let candidate : LabFormula → Option (Label × Formula)
    | ⟨w, .box phi⟩ =>
      if !allLabels.any (fun u => s.gamma.contains ⟨u, phi⟩) then some (w, phi) else none
    | _ => none
  match lookupOne candidate s.gamma.toList with
  | none => none
  | some (w, phi) =>
    let fresh := freshLabel s
    some (freshApp [addFormula ⟨fresh, phi⟩ s] w fresh)

-- ====================================================================
-- ([i]) — choice box (generating)
-- ====================================================================

/-- ([i]) rule. From `w:[i]φ` in Γ, when no existing `u` with `R_[i]wu` has
`u:φ` in Γ, introduce a fresh `v`, add the relational atom `R_[i]wv`, and
add `v:φ` (Algorithm 1, lines 51–54, the non-IOA-label case). -/
def applyStit : DeonticStit.Rule := fun s =>
  let allLabels := (labels s).toList
  let candidate : LabFormula → Option (Label × String × Formula)
    | ⟨w, .stit agent phi⟩ =>
      if !allLabels.any (fun u => hasRel (.choice agent w u) s && s.gamma.contains ⟨u, phi⟩)
      then some (w, agent, phi) else none
    | _ => none
  match lookupOne candidate s.gamma.toList with
  | none => none
  | some (w, agent, phi) =>
    let fresh := freshLabel s
    some (freshApp [addRel (.choice agent w fresh) (addFormula ⟨fresh, phi⟩ s)] w fresh)

-- ====================================================================
-- (⊗_i) — ought (generating)
-- ====================================================================

/-- (⊗_i) rule. From `w:⊗_i φ` in Γ, when no existing `u` with `I_⊗_i u`
has `u:φ` in Γ, introduce a fresh `v`, add the deontic predicate `I_⊗_i v`,
and add `v:φ` (Algorithm 1, lines 44–47). -/
def applyOught : DeonticStit.Rule := fun s =>
  let allLabels := (labels s).toList
  let candidate : LabFormula → Option (Label × String × Formula)
    | ⟨w, .ought agent phi⟩ =>
      if !allLabels.any (fun u => hasRel (.ideal agent u) s && s.gamma.contains ⟨u, phi⟩)
      then some (w, agent, phi) else none
    | _ => none
  match lookupOne candidate s.gamma.toList with
  | none => none
  | some (w, agent, phi) =>
    let fresh := freshLabel s
    some (freshApp [addRel (.ideal agent fresh) (addFormula ⟨fresh, phi⟩ s)] w fresh)

-- ====================================================================
-- Helpers: agents
-- ====================================================================

/-- All agent identifiers appearing inside a formula. -/
def formulaAgents : Formula → Std.TreeSet String
  | .bot => ∅
  | .atomF _ => ∅
  | .not f => formulaAgents f
  | .and l r => (formulaAgents l).union (formulaAgents r)
  | .or l r => (formulaAgents l).union (formulaAgents r)
  | .implies l r => (formulaAgents l).union (formulaAgents r)
  | .iff l r => (formulaAgents l).union (formulaAgents r)
  | .box f => formulaAgents f
  | .diamond f => formulaAgents f
  | .futureBox f => formulaAgents f
  | .futureDiamond f => formulaAgents f
  | .pastBox f => formulaAgents f
  | .pastDiamond f => formulaAgents f
  | .since l r => (formulaAgents l).union (formulaAgents r)
  | .until l r => (formulaAgents l).union (formulaAgents r)
  | .knowledge a f => (formulaAgents f).insert a
  | .belief a f => (formulaAgents f).insert a
  | .rankedBelief a _ f => (formulaAgents f).insert a
  | .announce b c => (formulaAgents b).union (formulaAgents c)
  | .stit a f => (formulaAgents f).insert a
  | .choiceDiamond a f => (formulaAgents f).insert a
  | .groupStit f => formulaAgents f
  | .next f => formulaAgents f
  | .ought a f => (formulaAgents f).insert a
  | .permitted a f => (formulaAgents f).insert a
  | .coalition agents f => (Std.TreeSet.ofList agents).union (formulaAgents f)
  | .canNext agents f => (Std.TreeSet.ofList agents).union (formulaAgents f)
  | .canAlways agents f => (Std.TreeSet.ofList agents).union (formulaAgents f)
  | .canEventually agents f => (Std.TreeSet.ofList agents).union (formulaAgents f)
  | .canUntil agents l r =>
    ((Std.TreeSet.ofList agents).union (formulaAgents l)).union (formulaAgents r)

/-- All agent identifiers appearing in a sequent — both in relational atoms
and inside formulas. -/
def sequentAgents (s : Sequent) : Std.TreeSet String :=
  let fromRels := s.rels.foldl (fun (acc : Std.TreeSet String) r => match r with
    | .choice a _ _ => acc.insert a
    | .ideal a _ => acc.insert a) ∅
  let fromForms := s.gamma.foldl (fun (acc : Std.TreeSet String) lf => acc.union (formulaAgents lf.lfFormula)) ∅
  fromRels.union fromForms

-- ====================================================================
-- Frame rules: Ref_i, Euc_i, D3_i (non-generating)
-- ====================================================================

/-- Ref_i rule: each `R_[i]` is reflexive on every label (Algorithm 1,
lines 5–7). Adds `R_[i]ww` for the first `(i, w)` pair lacking it. -/
def applyRef : DeonticStit.Rule := fun s =>
  let lbls := (labels s).toList
  lookupOne
    (fun a => lookupOne
      (fun w =>
        if !hasRel (.choice a w w) s then some (nonGenApp [addRel (.choice a w w) s]) else none)
      lbls)
    (sequentAgents s).toList

/-- Euc_i rule: each `R_[i]` is Euclidean (Algorithm 1, lines 8–10).
Together with Ref_i this makes `R_[i]` an equivalence relation on a stable
sequent (Lemma 21). Given `R_[i]wu` and `R_[i]wv` in ℛ, add `R_[i]uv` if
missing.

The Haskell builds the candidate list `[(a, u, v) | a, w, u, v, …]` lazily
and stops at the first hit; the nested `findSome?` walks the same order and
stops at the same place. -/
def applyEuc : DeonticStit.Rule := fun s =>
  let lbls := (labels s).toList
  lookupOne
    (fun a => lookupOne
      (fun w => lookupOne
        (fun u => lookupOne
          (fun v =>
            if hasRel (.choice a w u) s && hasRel (.choice a w v) s
                && !hasRel (.choice a u v) s
            then some (nonGenApp [addRel (.choice a u v) s]) else none)
          lbls)
        lbls)
      lbls)
    (sequentAgents s).toList

/-- D3_i rule: ideal sets are closed under `R_[i]` (Algorithm 1,
lines 11–13). Given `I_⊗_i w` and `R_[i]wu` in ℛ, add `I_⊗_i u` if
missing. -/
def applyD3 : DeonticStit.Rule := fun s =>
  let lbls := (labels s).toList
  lookupOne
    (fun a => lookupOne
      (fun w => lookupOne
        (fun u =>
          if hasRel (.ideal a w) s && hasRel (.choice a w u) s && !hasRel (.ideal a u) s
          then some (nonGenApp [addRel (.ideal a u) s]) else none)
        lbls)
      lbls)
    (sequentAgents s).toList

-- ====================================================================
-- D2_i — every agent has at least one ideal world (generating)
-- ====================================================================

/-- D2_i rule: for any agent with no `I_⊗_i u` in ℛ, introduce a fresh `v`
with `I_⊗_i v` (Algorithm 1, lines 48–50).

The fresh label is parented under the generation-tree root `rootLabel` (the
input formula's label, conventionally `w₀`), per the (D2_i) clause of
Definition 14. (The Haskell cites "Note 4 of Definition 14"; footnote 4 of
Definition 14 is about the ([i]*) clause, not (D2_i).) -/
def applyD2 (rootLabel : Label) : DeonticStit.Rule := fun s =>
  let lbls := (labels s).toList
  lookupOne
    (fun a =>
      if !lbls.any (fun u => hasRel (.ideal a u) s) then
        let fresh := freshLabel s
        some (freshApp [addRel (.ideal a fresh) s] rootLabel fresh)
      else none)
    (sequentAgents s).toList

-- ====================================================================
-- APC^k_i — limited choice (branching, k > 0 only)
-- ====================================================================

/-- All `n`-element sublists of a list, in the Haskell's `combinations`
order (those containing the head first). Structural on the list. -/
private def combinations : Nat → List α → List (List α)
  | 0, _ => [[]]
  | _ + 1, [] => []
  | n + 1, x :: xs => (combinations n xs).map (x :: ·) ++ combinations (n + 1) xs

/-- All `(k+1)`-tuples of distinct labels drawn from a list (Haskell
`kPlus1Tuples`; `k < 0` gives none). -/
private def kPlus1Tuples (k : Int) (lbls : List Label) : List (List Label) :=
  if k < 0 then [] else combinations (k + 1).toNat lbls

/-- The pairs `(t_m, t_j)` with `m < j`, ordered by `m` then `j` — the
Haskell's `[(tuple !! m, tuple !! j) | m <- [0 .. k-1], j <- [m+1 .. k]]`
for a tuple of length `k + 1`, without partial indexing. -/
private def orderedPairs : List α → List (α × α)
  | [] => []
  | x :: xs => xs.map (x, ·) ++ orderedPairs xs

/-- APC^k_i rule (Lyon & van Berkel, Figure 2; Algorithm 1, lines 14–19).
When `k > 0`, search for a tuple of `k + 1` labels `(w_0, …, w_k)` with *no*
`R_[i]w_j w_m` in ℛ for any `j ≠ m`. If found, branch on the `k(k+1)/2`
ways to pick a single pair `(m, j)` with `0 ≤ m < j ≤ k` and add
`R_[i]w_m w_j`. The rule succeeds iff every branch closes.

`k = 0` disables the rule (no upper bound on choices): `applyAPC 0` is
always `none`. `k` is an `Int`, as in the Haskell; a negative `k` also
yields `none` (no tuples). -/
def applyAPC (k : Int) : DeonticStit.Rule := fun s =>
  if k == 0 then none else
  let labelList := (labels s).toList
  let agents := (sequentAgents s).toList
  -- A tuple is unsaturated iff R_[i]w_j w_m ∉ ℛ for all j ≠ m. The tuple
  -- holds distinct labels, so "j ≠ m" is "different positions".
  let tryBranch (a : String) (tuple : List Label) : Option RuleApp :=
    let idx := tuple.zipIdx
    if idx.all (fun (x, j) => idx.all (fun (y, m) => j == m || !hasRel (.choice a x y) s)) then
      some (nonGenApp ((orderedPairs tuple).map fun (wm, wj) => addRel (.choice a wm wj) s))
    else none
  lookupOne (fun a => lookupOne (tryBranch a) (kPlus1Tuples k labelList)) agents

end Gamen
