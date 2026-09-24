import Gamen.Formula
import Gamen.DeonticStit.Sequent
import Gamen.DeonticStit.Rules
import Std.Data.TreeMap
import Std.Data.TreeSet

/-!
# Gamen.DeonticStit.Saturation

Port of `gamen-hs/src/Gamen/DeonticStit/Saturation.hs`: saturation
conditions, generation tree, and blocking for the deontic STIT proof-search
procedure (Lyon & van Berkel, "Proof Theory and Decision Procedures for
Deontic STIT Logics", *JAIR* 81 (2024), Definitions 14, 16, 18 and
Remark 17, pp. 854–856; all checked against
`pdftotext gamen-hs/notes/LyonBerkel2024.pdf -`).

*Generation tree (Definition 14, p. 854).* A tree of label introductions
recorded as a parent map. Used by the blocking mechanism to detect loop
nodes during proof search. IOA^T-labels are tracked separately (per
Remark 17, p. 855, they never become tree nodes and are always considered
unblocked).

*Blocking (Definition 16, p. 855).* A label `u` is *directly blocked by* a
proper ancestor `v` iff (i) `v` is not the root, (ii) for every agent `i`
the membership `I_⊗_i u ∈ ℛ ⟺ I_⊗_i v ∈ ℛ` holds, and (iii) the formula
content at `u` equals the formula content at `v`. A label is *indirectly
blocked* if some proper ancestor of it is directly blocked. `isBlocked` is
the union of the two.

*Saturation (Definition 18, p. 856).* Fourteen predicates, one per
rule. `isStable` is their conjunction (modulo IOA-tuple-satisfaction, which
lives with the proof-search driver).

*Deviation from the Haskell: `Except`.* Haskell's `ancestors` recurses
through the parent map without a bound, so on a parent map with a cycle
(which `addGenChild` does not prevent) it produces an infinite list. The
lazy `any` in `isDirectlyBlocked`/`isIndirectlyBlocked` then returns `True`
as soon as a matching ancestor appears in that list, and diverges only when
no ancestor matches. The Lean `ancestors` walks with fuel
`gtParent.size + 1` (a cycle-free path visits each of the `size` children
at most once, so the `size + 1`-th step can only be a revisit) and returns
`Except`; it materializes the whole list before any predicate inspects it,
so on a cyclic map Lean always reports an error, including in the cases
where Haskell's lazy search would have returned `True` early. Running out
of fuel is never turned into a truncated list. Cycles cannot arise through
`Gamen.DeonticStit.Prove`: every edge it adds (`Prove.hs`, `applyEdges`,
line 166) parents a fresh label, so the walk is unaffected there. The
blocking predicates and the four saturation predicates that consult the
tree (`satBox`, `satStit`, `satOught`, `satD2`) therefore return
`Except String Bool`, as does `isStable`. The ten predicates that do not
look at the tree stay `Bool`, matching the Haskell.

No B&D citations in this module.
-/
namespace Gamen

-- ====================================================================
-- Generation tree
-- ====================================================================

/-- The generation tree records how labels were introduced during proof
search (Lyon & van Berkel, Definition 14). The root corresponds to the
input formula's label `w₀`; every other label is a child of the label
whose principal formula caused its introduction.

IOA^T-labels — labels introduced by the IOA rule's IoaOp — are *not*
inserted into the tree (Remark 17); they are recorded only in `gtIoaSet`
so that the rest of the procedure can identify them. -/
structure GenTree where
  /-- Root label, conventionally `w₀`. -/
  gtRoot : Label
  /-- child ↦ parent -/
  gtParent : Std.TreeMap Label Label
  /-- Labels introduced by IoaOp. -/
  gtIoaSet : Std.TreeSet Label
  deriving BEq, Repr

/-- A generation tree containing just the root label. -/
def emptyGenTree (root : Label) : GenTree :=
  { gtRoot := root, gtParent := ∅, gtIoaSet := ∅ }

/-- Add a non-IOA child edge: `child` becomes a child of `parent`. -/
def addGenChild (parent child : Label) (gt : GenTree) : GenTree :=
  { gt with gtParent := gt.gtParent.insert child parent }

/-- Mark `child` as an IOA^T-label without inserting it as a tree node
(Remark 17). IOA^T-labels are always unblocked. -/
def addGenIoaLabel (child : Label) (gt : GenTree) : GenTree :=
  { gt with gtIoaSet := gt.gtIoaSet.insert child }

/-- Was the label introduced via IoaOp? -/
def isIoaLabel (w : Label) (gt : GenTree) : Bool := gt.gtIoaSet.contains w

/-- Proper ancestors of a label, parent-first then up to the root. Returns
the empty list for the root and for IOA^T-labels (which have no parent in
the tree).

Fuel: `gt.gtParent.size + 1`. A cycle-free parent chain has at most
`gtParent.size` edges, so needing more steps means the parent map has a
cycle, which is reported as an error (the Haskell diverges there). -/
def ancestors (w : Label) (gt : GenTree) : Except String (List Label) :=
  go (gt.gtParent.size + 1) w
where
  go : Nat → Label → Except String (List Label)
    | 0, _ => throw "ancestors: generation tree parent map has a cycle"
    | fuel + 1, x =>
      match gt.gtParent.get? x with
      | none => pure []
      | some p => do return p :: (← go fuel p)

-- ====================================================================
-- Blocking (Definition 16)
-- ====================================================================

/-- The set of formulas at label `w`: `{φ : w:φ ∈ Γ}` — the
formula-content slice written `Γ↾w` in the paper. -/
private def formulasAt (w : Label) (s : Sequent) : Std.TreeSet Formula :=
  s.gamma.foldl (fun acc lf => if lf.lfLabel == w then acc.insert lf.lfFormula else acc) ∅

/-- Definition 16: `u` is *directly blocked by* `v` iff (i) `v` is not the
root of the generation tree, (ii) for every agent `i`,
`I_⊗_i u ∈ ℛ ⟺ I_⊗_i v ∈ ℛ`, and (iii) `Γ↾u = Γ↾v`.

Does not consult the ancestor chain (the caller does), so it stays `Bool`. -/
def isDirectlyBlockedBy (u v : Label) (gt : GenTree) (s : Sequent) : Bool :=
  let idealAgrees (a : String) : Bool := hasRel (.ideal a u) s == hasRel (.ideal a v) s
  v != gt.gtRoot
    && (sequentAgents s).toList.all idealAgrees
    && formulasAt u s == formulasAt v s

/-- Is the label directly blocked? True iff some *proper ancestor* in the
generation tree directly blocks it. -/
def isDirectlyBlocked (w : Label) (gt : GenTree) (s : Sequent) : Except String Bool := do
  let anc ← ancestors w gt
  return anc.any fun v => isDirectlyBlockedBy w v gt s

/-- Is the label indirectly blocked? True iff some *proper ancestor* of it
is itself directly blocked. -/
def isIndirectlyBlocked (w : Label) (gt : GenTree) (s : Sequent) : Except String Bool := do
  let anc ← ancestors w gt
  anc.anyM fun v => isDirectlyBlocked v gt s

/-- A label is blocked iff it is directly or indirectly blocked. IOA^T-labels
and the root are always unblocked (the former because they have no
ancestors, the latter because clause (i) of `isDirectlyBlockedBy` excludes
them as blockers and they have no ancestors of their own). -/
def isBlocked (w : Label) (gt : GenTree) (s : Sequent) : Except String Bool := do
  if ← isDirectlyBlocked w gt s then return true
  isIndirectlyBlocked w gt s

def isUnblocked (w : Label) (gt : GenTree) (s : Sequent) : Except String Bool :=
  (!·) <$> isBlocked w gt s

/-- All unblocked labels in the sequent under the given generation tree.
Used by saturation conditions and by the proof-search driver when
extracting the stability model. -/
def unblockedLabels (gt : GenTree) (s : Sequent) : Except String (Std.TreeSet Label) := do
  let kept ← (labels s).toList.filterM fun w => isUnblocked w gt s
  return Std.TreeSet.ofList kept

-- ====================================================================
-- Saturation conditions (Definition 18)
-- ====================================================================

/-- (C_id) — no contradicting literals: there is no `w` and atom `p` with
both `w:p ∈ Γ` and `w:¬p ∈ Γ`. -/
def satId (s : Sequent) : Bool := !isClosedSequent s

/-- (C_∨) — every disjunction has both disjuncts. -/
def satOr (s : Sequent) : Bool :=
  s.gamma.toList.all fun
    | ⟨w, .or l r⟩ => hasFormula ⟨w, l⟩ s && hasFormula ⟨w, r⟩ s
    | _ => true

/-- (C_∧) — every conjunction has at least one conjunct. -/
def satAnd (s : Sequent) : Bool :=
  s.gamma.toList.all fun
    | ⟨w, .and l r⟩ => hasFormula ⟨w, l⟩ s || hasFormula ⟨w, r⟩ s
    | _ => true

/-- (C_◇) — every `w:◇φ ∈ Γ` forces `u:φ ∈ Γ` *for every* `u ∈ Lab(Λ)`
(Definition 18). The bound is universal because the calculus's (◇) rule
iterates over labels: saturation means we have exhausted every candidate
witness, not merely produced one. -/
def satDiamond (s : Sequent) : Bool :=
  s.gamma.toList.all fun
    | ⟨_, .diamond phi⟩ => (labels s).toList.all fun u => hasFormula ⟨u, phi⟩ s
    | _ => true

/-- (C_□) — every `w:□φ` has an *unblocked* `u` with `u:φ ∈ Γ`. -/
def satBox (gt : GenTree) (s : Sequent) : Except String Bool :=
  s.gamma.toList.allM fun
    | ⟨_, .box phi⟩ => (labels s).toList.anyM fun u => do
        return (← isUnblocked u gt s) && hasFormula ⟨u, phi⟩ s
    | _ => pure true

/-- (C_⟨i⟩) — for every `w:⟨i⟩φ` and every `u` with `R_[i]wu ∈ ℛ`, both
`u:φ` and `u:⟨i⟩φ` are in Γ. -/
def satChoiceDiamond (s : Sequent) : Bool :=
  s.gamma.toList.all fun
    | ⟨w, .choiceDiamond a phi⟩ => (labels s).toList.all fun u =>
        !hasRel (.choice a w u) s
          || (hasFormula ⟨u, phi⟩ s && hasFormula ⟨u, .choiceDiamond a phi⟩ s)
    | _ => true

/-- (C_[i]) — for every *unblocked* `w` with `w:[i]φ ∈ Γ`, there exists `u`
with `R_[i]wu ∈ ℛ` and `u:φ ∈ Γ`. -/
def satStit (gt : GenTree) (s : Sequent) : Except String Bool :=
  s.gamma.toList.allM fun
    | ⟨w, .stit a phi⟩ => do
        if ← isUnblocked w gt s then
          return (labels s).toList.any fun u => hasRel (.choice a w u) s && hasFormula ⟨u, phi⟩ s
        else
          return true
    | _ => pure true

/-- (C_ref) — every `(i, w)` has `R_[i]ww ∈ ℛ`. -/
def satRef (s : Sequent) : Bool :=
  (sequentAgents s).toList.all fun a =>
    (labels s).toList.all fun w => hasRel (.choice a w w) s

/-- (C_euc) — Euclidean closure: if `R_[i]wu, R_[i]wv ∈ ℛ` then
`R_[i]uv ∈ ℛ`. -/
def satEuc (s : Sequent) : Bool :=
  let ls := (labels s).toList
  (sequentAgents s).toList.all fun a =>
    ls.all fun w => ls.all fun u => ls.all fun v =>
      !(hasRel (.choice a w u) s && hasRel (.choice a w v) s) || hasRel (.choice a u v) s

/-- (C_⊖_i) — for every `w:⊖_i φ ∈ Γ` and every `u` with `I_⊗_i u ∈ ℛ`,
`u:φ ∈ Γ`. -/
def satPermitted (s : Sequent) : Bool :=
  s.gamma.toList.all fun
    | ⟨_, .permitted a phi⟩ => (labels s).toList.all fun u =>
        !hasRel (.ideal a u) s || hasFormula ⟨u, phi⟩ s
    | _ => true

/-- (C_⊗_i) — every `w:⊗_i φ` has an *unblocked* `u` with both
`I_⊗_i u ∈ ℛ` and `u:φ ∈ Γ`. (The paper's statement of (C_⊗_i) on p. 856
misprints the principal formula as `w : ⊖_i φ`; the (⊗_i) rule it
saturates, and the Haskell, take `w : ⊗_i φ`.) -/
def satOught (gt : GenTree) (s : Sequent) : Except String Bool :=
  s.gamma.toList.allM fun
    | ⟨_, .ought a phi⟩ => (labels s).toList.anyM fun u => do
        return (← isUnblocked u gt s) && hasRel (.ideal a u) s && hasFormula ⟨u, phi⟩ s
    | _ => pure true

/-- (C_D2) — every agent `i` has at least one *unblocked* `w` with
`I_⊗_i w ∈ ℛ`. -/
def satD2 (gt : GenTree) (s : Sequent) : Except String Bool :=
  (sequentAgents s).toList.allM fun a =>
    (labels s).toList.anyM fun w => do
      return (← isUnblocked w gt s) && hasRel (.ideal a w) s

/-- (C_D3) — ideal sets are closed under `R_[i]`: if `I_⊗_i w ∈ ℛ` and
`R_[i]wu ∈ ℛ` then `I_⊗_i u ∈ ℛ`. -/
def satD3 (s : Sequent) : Bool :=
  let ls := (labels s).toList
  (sequentAgents s).toList.all fun a =>
    ls.all fun w => ls.all fun u =>
      !(hasRel (.ideal a w) s && hasRel (.choice a w u) s) || hasRel (.ideal a u) s

/-- All `n`-element sublists of a list, in the Haskell's `combinations`
order (those containing the head first). `n` is an `Int` so that the
Haskell's behavior for a negative `k` in `satAPC` is reproduced exactly:
`combinations 0 xs = [[]]`, and a negative `n` bottoms out in
`combinations _ [] = []`. Structural on the list. -/
private def combinations (n : Int) : List α → List (List α)
  | [] => if n == 0 then [[]] else []
  | x :: xs =>
    if n == 0 then [[]]
    else (combinations (n - 1) xs).map (x :: ·) ++ combinations n xs

/-- (C_APC) — for any `(k + 1)`-tuple of labels and any agent, some pair is
related by `R_[i]`. When `k = 0` (no upper bound on choices) the condition
trivially holds.

`k` is an `Int`, as in the Haskell (and as in `applyAPC`). The Haskell
checks position pairs `(j, m)` with `j ≠ m` via `tuple !! j`; since a
combination holds distinct labels, "different positions" is "different
labels", which is what the index-free check below tests. -/
def satAPC (k : Int) (s : Sequent) : Bool :=
  if k == 0 then true else
  let ls := (labels s).toList
  (sequentAgents s).toList.all fun a =>
    (combinations (k + 1) ls).all fun tuple =>
      tuple.any fun x => tuple.any fun y => x != y && hasRel (.choice a x y) s

-- ====================================================================
-- Stability
-- ====================================================================

/-- Is the sequent stable? A sequent is stable iff every saturation
condition holds. The proof-search driver uses `isStable` to decide when no
more rules can fire and a counter-model can be extracted.

*Note:* Definition 18 also requires every IOA^T-tuple to be
IOA^T-satisfied. That check lives with the driver (`Gamen.DeonticStit.Prove`)
since it depends on which labels were introduced by IoaOp; the `GenTree`
carries the necessary `gtIoaSet` bookkeeping.

Short-circuits in the Haskell's `&&` order, so a tree error is only
reported if every earlier `Bool` condition held. -/
def isStable (k : Int) (gt : GenTree) (s : Sequent) : Except String Bool := do
  if !(satId s && satOr s && satAnd s && satDiamond s) then return false
  if !(← satBox gt s) then return false
  if !satChoiceDiamond s then return false
  if !(← satStit gt s) then return false
  if !(satRef s && satEuc s && satPermitted s) then return false
  if !(← satOught gt s) then return false
  if !(← satD2 gt s) then return false
  return satD3 s && satAPC k s

end Gamen
