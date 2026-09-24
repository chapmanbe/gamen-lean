import Std.Data.HashSet
import Gamen.Semantics
import Gamen.Verdict

/-!
# Gamen.Tableau

Port of `gamen-hs/src/Gamen/Tableau.hs`: prefixed signed tableaux (B&D
§6.1 for prefixes and prefixed formulas and §6.2 for branch closure, all in
running prose rather than numbered definitions; rules in Tables 6.1–6.3),
the systems K, KT, KD, KTB, K4, S4, S5 (Table 6.4), ancestor blocking, and
countermodel extraction (B&D Theorem 6.19).

Not ported: the FutureBox/FutureDiamond rules, which gamen-hs has
quarantined (issue #25).
-/
namespace Gamen

-- Lean core defines lexicographic `Ord` on pairs (`lexOrd`) but does not
-- make it an instance; branches key sets on `(Sign × Formula)` and relations
-- on `(World × World)`, so enable it here.
attribute [local instance] lexOrd

/-! ## Prefixes (B&D §6.1) -/

/-- A prefix is a non-empty sequence of positive integers, e.g. `1.2.1`
(B&D §6.1). -/
structure Prefix where
  path : List Nat
  deriving BEq, Ord, Hashable, Repr, DecidableEq, Inhabited

namespace Prefix

instance : ToString Prefix := ⟨fun p => ".".intercalate (p.path.map toString)⟩

def root : Prefix := ⟨[1]⟩
def extend (σ : Prefix) (n : Nat) : Prefix := ⟨σ.path ++ [n]⟩
def length (σ : Prefix) : Nat := σ.path.length

/-- `τ.isChildOf σ`: τ is σ.n for some n. -/
def isChildOf (child parent : Prefix) : Bool :=
  child.length == parent.length + 1 && child.path.dropLast == parent.path

/-- Proper ancestors of σ, root first. -/
def ancestors (σ : Prefix) : List Prefix :=
  (List.range (σ.length - 1)).map fun k => ⟨σ.path.take (k + 1)⟩

end Prefix

/-- Construct a prefix, enforcing non-empty and positive (Haskell `mkPrefix`,
whose `error`s become `Except`). -/
def mkPrefix : List Nat → Except String Prefix
  | [] => throw "Prefix must be non-empty"
  | ns => if ns.all (· > 0) then pure ⟨ns⟩
          else throw "Prefix elements must be positive integers"

/-- Extend a prefix: σ.n (Haskell `extendPrefix`). -/
def extendPrefix (σ : Prefix) (n : Nat) : Except String Prefix :=
  if n > 0 then pure (σ.extend n) else throw "Extension must be a positive integer"

/-- Parent prefix: σ.n → σ. The root has no parent (Haskell `parentPrefix`). -/
def parentPrefix (σ : Prefix) : Except String Prefix :=
  if σ.length > 1 then pure ⟨σ.path.dropLast⟩ else throw "Root prefix has no parent"

/-! ## Signed, prefixed formulas (B&D §6.1) -/

inductive Sign where
  | T
  | F
  deriving BEq, Ord, Hashable, Repr, DecidableEq, Inhabited

instance : ToString Sign := ⟨fun | .T => "T" | .F => "F"⟩

structure PrefixedFormula where
  pfx : Prefix
  sign : Sign
  formula : Formula
  deriving BEq, Ord, Hashable, Repr, DecidableEq, Inhabited

instance : ToString PrefixedFormula := ⟨fun pf => s!"{pf.pfx} {pf.sign} {pf.formula}"⟩

def pfTrue (σ : Prefix) (a : Formula) : PrefixedFormula := ⟨σ, .T, a⟩
def pfFalse (σ : Prefix) (a : Formula) : PrefixedFormula := ⟨σ, .F, a⟩

/-! ## Branches -/

/-- A tableau branch. `formulas` keeps insertion order (rules scan it by
index); `members` and `prefixes` give O(log n) membership. -/
structure Branch where
  formulas : Array PrefixedFormula
  members : Std.TreeSet PrefixedFormula
  prefixes : Std.TreeSet Prefix
  expanded : Std.HashSet Nat := {}   -- indices of fully expanded formulas
  scanStart : Nat := 0

/-- Branch equality is set equality of its formulas, as in Haskell. -/
instance : BEq Branch := ⟨fun a b => a.members.toList == b.members.toList⟩

namespace Branch

def ofList (pfs : List PrefixedFormula) : Branch :=
  { formulas := pfs.toArray
    members := Std.TreeSet.ofList pfs
    prefixes := Std.TreeSet.ofList (pfs.map (·.pfx)) }

/-- Closed iff it contains both σ T A and σ F A (B&D §6.2), or
σ T ⊥ (as in gamen-hs; B&D Ch. 6 states only the first condition). -/
def isClosed (b : Branch) : Bool :=
  b.formulas.any fun pf =>
    pf.sign == .T && (pf.formula == .bot || b.members.contains { pf with sign := .F })

def contains (b : Branch) (pf : PrefixedFormula) : Bool := b.members.contains pf

/-- The least child σ.n not already used on the branch. At most
`prefixes.size` children can be in use, so one of the first
`prefixes.size + 1` candidates is fresh — this bound replaces Haskell's
unbounded `go (n + 1)` and makes the search visibly terminating. -/
def freshPrefix (b : Branch) (σ : Prefix) : Prefix :=
  let candidates := (List.range (b.prefixes.size + 1)).map (σ.extend ·.succ)
  (candidates.find? (!b.prefixes.contains ·)).getD (σ.extend (b.prefixes.size + 1))

/-- Is there already a child τ of σ carrying `s a`? -/
def hasWitness (b : Branch) (σ : Prefix) (s : Sign) (a : Formula) : Bool :=
  b.formulas.any fun pf => pf.pfx.isChildOf σ && pf.sign == s && pf.formula == a

def append (b : Branch) (pf : PrefixedFormula) : Branch :=
  { b with
    formulas := b.formulas.push pf
    members := b.members.insert pf
    prefixes := b.prefixes.insert pf.pfx }

def addUnique (b : Branch) (pfs : List PrefixedFormula) : Branch :=
  pfs.foldl (fun b pf => if b.contains pf then b else b.append pf) b

def childrenOf (b : Branch) (σ : Prefix) : List Prefix :=
  b.prefixes.toList.filter (·.isChildOf σ)

/-- Signed formulas at prefix σ. -/
def prefixContent (b : Branch) (σ : Prefix) : Std.TreeSet (Sign × Formula) :=
  Std.TreeSet.ofList (b.formulas.toList.filterMap fun pf =>
    if pf.pfx == σ then some (pf.sign, pf.formula) else none)

/-- Ancestor blocking: σ is blocked if its content is a subset of some
ancestor's content (prevents infinite expansion). -/
def isBlocked (b : Branch) (σ : Prefix) : Bool :=
  if σ.length ≤ 1 then false
  else
    let content := b.prefixContent σ
    !content.isEmpty && σ.ancestors.any fun anc =>
      let ancContent := b.prefixContent anc
      content.toList.all ancContent.contains

end Branch

def isPropositional : Formula → Bool
  | .not _ | .and _ _ | .or _ _ | .implies _ _ | .iff _ _ => true
  | _ => false

/-! ## Rules (B&D Tables 6.1 and 6.2) -/

inductive RuleResult where
  | noRule
  | stack (additions : List PrefixedFormula)
  | split (left right : List PrefixedFormula)

abbrev Rule := PrefixedFormula → Branch → RuleResult

/-- Table 6.1: propositional rules. -/
def propositionalRule : Rule
  | ⟨σ, s, a⟩, _ =>
    match s, a with
    | .T, .not b => .stack [pfFalse σ b]
    | .F, .not b => .stack [pfTrue σ b]
    | .T, .and l r => .stack [pfTrue σ l, pfTrue σ r]
    | .F, .and l r => .split [pfFalse σ l] [pfFalse σ r]
    | .T, .or l r => .split [pfTrue σ l] [pfTrue σ r]
    | .F, .or l r => .stack [pfFalse σ l, pfFalse σ r]
    | .T, .implies l r => .split [pfFalse σ l] [pfTrue σ r]
    | .F, .implies l r => .stack [pfTrue σ l, pfFalse σ r]
    | .T, .iff l r => .split [pfTrue σ l, pfTrue σ r] [pfFalse σ l, pfFalse σ r]
    | .F, .iff l r => .split [pfTrue σ l, pfFalse σ r] [pfFalse σ l, pfTrue σ r]
    | _, _ => .noRule

/-- Table 6.2, □T: from σ T □A, add τ T A for every used child τ of σ. -/
def boxTrueRule : Rule
  | ⟨σ, .T, .box a⟩, b =>
    let adds := (b.childrenOf σ).filterMap fun τ =>
      let pf := pfTrue τ a
      if b.contains pf then none else some pf
    if adds.isEmpty then .noRule else .stack adds
  | _, _ => .noRule

/-- Table 6.2, □F: from σ F □A, add σ.n F A for a fresh σ.n. -/
def boxFalseRule : Rule
  | ⟨σ, .F, .box a⟩, b =>
    if b.hasWitness σ .F a then .noRule else .stack [pfFalse (b.freshPrefix σ) a]
  | _, _ => .noRule

/-- Table 6.2, ◇T: from σ T ◇A, add σ.n T A for a fresh σ.n. -/
def diamondTrueRule : Rule
  | ⟨σ, .T, .diamond a⟩, b =>
    if b.hasWitness σ .T a then .noRule else .stack [pfTrue (b.freshPrefix σ) a]
  | _, _ => .noRule

/-- Table 6.2, ◇F: from σ F ◇A, add τ F A for every used child τ of σ. -/
def diamondFalseRule : Rule
  | ⟨σ, .F, .diamond a⟩, b =>
    let adds := (b.childrenOf σ).filterMap fun τ =>
      let pf := pfFalse τ a
      if b.contains pf then none else some pf
    if adds.isEmpty then .noRule else .stack adds
  | _, _ => .noRule

/-! ## Systems -/

/-- A modal system: extra rules applied to used prefixes, and witness rules
that may create prefixes (B&D Table 6.4). -/
structure System where
  name : String
  usedPrefixRules : List Rule
  witnessRules : List Rule

def systemK : System := ⟨"K", [], []⟩

/-! ### Additional modal rules (B&D Table 6.3) -/

/-- Table 6.3, T□: σ T □A → σ T A (reflexive). Proposition 6.10. -/
def tBoxRule : Rule
  | ⟨σ, .T, .box a⟩, b =>
    let new := pfTrue σ a
    if b.contains new then .noRule else .stack [new]
  | _, _ => .noRule

/-- Table 6.3, T◇: σ F ◇A → σ F A (reflexive). Proposition 6.10. -/
def tDiamondRule : Rule
  | ⟨σ, .F, .diamond a⟩, b =>
    let new := pfFalse σ a
    if b.contains new then .noRule else .stack [new]
  | _, _ => .noRule

/-- Table 6.3, D□: from σ T □A add σ T ◇A (serial). Proposition 6.11. -/
def dBoxRule : Rule
  | ⟨σ, .T, .box a⟩, b =>
    let new := pfTrue σ (.diamond a)
    if b.contains new then .noRule else .stack [new]
  | _, _ => .noRule

/-- Table 6.3, D◇: from σ F ◇A add σ F □A (serial). Proposition 6.11. -/
def dDiamondRule : Rule
  | ⟨σ, .F, .diamond a⟩, b =>
    let new := pfFalse σ (.box a)
    if b.contains new then .noRule else .stack [new]
  | _, _ => .noRule

/-- The parent σ of σ.n, for the B and 4r rules: the guard is Haskell's
`prefixLength σn < 2 = NoRule`, and the parent is taken straight from the
path. Deliberately not routed through `parentPrefix`'s `Except`, so an
error there can never become "no rule applies". -/
private def parentOf? (σn : Prefix) : Option Prefix :=
  if σn.length < 2 then none else some ⟨σn.path.dropLast⟩

/-- Table 6.3, B□: σ.n T □A → σ T A (symmetric). Proposition 6.12. -/
def bBoxRule : Rule
  | ⟨σn, .T, .box a⟩, b =>
    match parentOf? σn with
    | none => .noRule
    | some σ =>
      let new := pfTrue σ a
      if b.contains new then .noRule else .stack [new]
  | _, _ => .noRule

/-- Table 6.3, B◇: σ.n F ◇A → σ F A (symmetric). Proposition 6.12. -/
def bDiamondRule : Rule
  | ⟨σn, .F, .diamond a⟩, b =>
    match parentOf? σn with
    | none => .noRule
    | some σ =>
      let new := pfFalse σ a
      if b.contains new then .noRule else .stack [new]
  | _, _ => .noRule

/-- Table 6.3, 4□: σ T □A → σ.n T □A for each used child σ.n (transitive).
Proposition 6.13. -/
def fourBoxRule : Rule
  | ⟨σ, .T, f@(.box _)⟩, b =>
    let adds := (b.childrenOf σ).filterMap fun τ =>
      let pf := pfTrue τ f
      if b.contains pf then none else some pf
    if adds.isEmpty then .noRule else .stack adds
  | _, _ => .noRule

/-- Table 6.3, 4◇: σ F ◇A → σ.n F ◇A for each used child σ.n (transitive).
Proposition 6.13. -/
def fourDiamondRule : Rule
  | ⟨σ, .F, f@(.diamond _)⟩, b =>
    let adds := (b.childrenOf σ).filterMap fun τ =>
      let pf := pfFalse τ f
      if b.contains pf then none else some pf
    if adds.isEmpty then .noRule else .stack adds
  | _, _ => .noRule

/-- Table 6.3, 4r□: σ.n T □A → σ T □A (euclidean). Proposition 6.14. -/
def fourRBoxRule : Rule
  | ⟨σn, .T, f@(.box _)⟩, b =>
    match parentOf? σn with
    | none => .noRule
    | some σ =>
      let new := pfTrue σ f
      if b.contains new then .noRule else .stack [new]
  | _, _ => .noRule

/-- Table 6.3, 4r◇: σ.n F ◇A → σ F ◇A (euclidean). Proposition 6.14. -/
def fourRDiamondRule : Rule
  | ⟨σn, .F, f@(.diamond _)⟩, b =>
    match parentOf? σn with
    | none => .noRule
    | some σ =>
      let new := pfFalse σ f
      if b.contains new then .noRule else .stack [new]
  | _, _ => .noRule

/-! ### Systems (B&D Table 6.4) -/

/-- KT: reflexive frames. T□, T◇. -/
def systemKT : System := ⟨"KT", [tBoxRule, tDiamondRule], []⟩

/-- KD: serial frames. D□, D◇ as witness rules. -/
def systemKD : System := ⟨"KD", [], [dBoxRule, dDiamondRule]⟩

/-- B = KTB: reflexive + symmetric. T□, T◇, B□, B◇. Named `systemKB` and
reporting system name "KTB", as in Haskell: this is KTB, not KB (K + B,
symmetric frames only). -/
def systemKB : System :=
  ⟨"KTB", [tBoxRule, tDiamondRule, bBoxRule, bDiamondRule], []⟩

/-- K4: transitive frames. 4□, 4◇. -/
def systemK4 : System := ⟨"K4", [fourBoxRule, fourDiamondRule], []⟩

/-- S4 = KT4: reflexive + transitive. T□, T◇, 4□, 4◇. -/
def systemS4 : System :=
  ⟨"S4", [tBoxRule, tDiamondRule, fourBoxRule, fourDiamondRule], []⟩

/-- S5 = KT4B: Table 6.4 lists T□, T◇, 4□, 4◇, 4r□, 4r◇. B□, B◇ are added
as in Haskell: logically redundant (reflexive + euclidean → symmetric) but
they speed termination. They are not in Table 6.4. -/
def systemS5 : System :=
  ⟨"S5", [tBoxRule, tDiamondRule, bBoxRule, bDiamondRule,
          fourBoxRule, fourDiamondRule, fourRBoxRule, fourRDiamondRule], []⟩

/-- Port of `Gamen.Temporal.systemKDt` as used by `gamen-validate`: the D
rules as witness rules. Its temporal T/4 rules are omitted because the
consistency fragment gate rejects every temporal operator before the
tableau runs, so they can never fire there. -/
def systemKDt : System := ⟨"KDt", [], [dBoxRule, dDiamondRule]⟩

def tryRules : List Rule → Rule
  | [], _, _ => .noRule
  | r :: rs, pf, b =>
    match r pf b with
    | .noRule => tryRules rs pf b
    | res => res

/-- Priority-1 rules: propositional, then rules that only use existing prefixes. -/
def tryPriority1 (sys : System) : Rule :=
  tryRules ([propositionalRule, boxTrueRule, diamondFalseRule] ++ sys.usedPrefixRules)

/-! ## Expansion passes -/

private def isAtomic : Formula → Bool
  | .atomF _ | .bot => true
  | _ => false

/-- Apply the first non-branching priority-1 rule, scanning from `scanStart`. -/
def tryPriority1Pass (sys : System) (b : Branch) : Option (List Branch) := Id.run do
  for i in List.range' b.scanStart (b.formulas.size - b.scanStart) do
    if b.expanded.contains i then continue
    let pf := b.formulas[i]!
    if isAtomic pf.formula then continue
    match tryPriority1 sys pf b with
    | .stack adds =>
      let nb := b.addUnique adds
      if nb == b then continue
      let exp := if isPropositional pf.formula then nb.expanded.insert i else nb.expanded
      return some [{ nb with scanStart := i, expanded := exp }]
    | _ => continue
  return none

/-- Apply a prefix-creating rule (□F or ◇T) to the first unwitnessed,
unblocked candidate. -/
def tryWitnessCreatingPass (isCandidate : PrefixedFormula → Bool) (rule : Rule)
    (b : Branch) : Option (List Branch) := do
  let pf ← b.formulas.find? fun pf =>
    isCandidate pf && !b.hasWitness pf.pfx pf.sign (childFormula pf.formula)
      && !b.isBlocked pf.pfx
  match rule pf b with
  | .stack adds =>
    let nb := b.addUnique adds
    if nb == b then none else some [{ nb with scanStart := 0, expanded := {} }]
  | _ => none
where
  childFormula : Formula → Formula
    | .box a | .diamond a => a
    | f => f

def tryBoxFalsePass : Branch → Option (List Branch) :=
  tryWitnessCreatingPass (fun pf => pf.sign == .F && pf.formula matches .box _) boxFalseRule

def tryDiamondTruePass : Branch → Option (List Branch) :=
  tryWitnessCreatingPass (fun pf => pf.sign == .T && pf.formula matches .diamond _) diamondTrueRule

/-- System-specific witness rules (none for K). -/
def tryWitnessPass (sys : System) (b : Branch) : Option (List Branch) := Id.run do
  if sys.witnessRules.isEmpty then return none
  for pf in b.formulas do
    if b.isBlocked pf.pfx || isAtomic pf.formula then continue
    match tryRules sys.witnessRules pf b with
    | .stack adds =>
      let nb := b.addUnique adds
      if nb == b then continue
      return some [{ nb with scanStart := 0, expanded := {} }]
    | _ => continue
  return none

/-- Apply the first branching rule, forking the branch. -/
def tryBetaPass (sys : System) (b : Branch) : Option (List Branch) := Id.run do
  for i in List.range b.formulas.size do
    if b.expanded.contains i then continue
    let pf := b.formulas[i]!
    if isAtomic pf.formula then continue
    match tryPriority1 sys pf b with
    | .split leftAdds rightAdds =>
      let left := b.addUnique leftAdds
      let right := b.addUnique rightAdds
      let exp := if isPropositional pf.formula then b.expanded.insert i else b.expanded
      let parent := { b with expanded := b.expanded.insert i }
      if left == b && right == b then continue
      else if left == b then
        return some [parent, { right with scanStart := i, expanded := exp }]
      else if right == b then
        return some [{ left with scanStart := i, expanded := exp }, parent]
      else
        return some [{ left with scanStart := i, expanded := exp },
                     { right with scanStart := i, expanded := exp }]
    | _ => continue
  return none

/-- One expansion step on a branch; `[b]` unchanged means saturated. -/
def applyAllRules (sys : System) (b : Branch) : List Branch :=
  if b.isClosed then [b]
  else
    (tryPriority1Pass sys b <|> tryBoxFalsePass b <|> tryDiamondTruePass b
      <|> tryWitnessPass sys b <|> tryBetaPass sys b).getD [b]

/-! ## Driver -/

inductive TableauOutcome where
  | closed
  | stillOpen (branches : List Branch)
  | exhausted (steps : Nat)

def defaultMaxSteps : Nat := 1000

private def findExpandableBranch (branches : List Branch) (saturated : Std.TreeSet Nat) :
    Option (Nat × Branch) :=
  ((List.range branches.length).zip branches).find? fun (i, b) =>
    !b.isClosed && !saturated.contains i

/-- Expand until every branch is closed or saturated, or the step budget
runs out. The budget is the recursion's fuel, so termination is structural. -/
def buildTableau (sys : System) (maxSteps : Nat) (assumptions : List PrefixedFormula) :
    TableauOutcome :=
  go [Branch.ofList assumptions] ∅ maxSteps
where
  finished (branches : List Branch) : TableauOutcome :=
    if branches.all (·.isClosed) then .closed
    else .stillOpen (branches.filter (!·.isClosed))
  go (branches : List Branch) (saturated : Std.TreeSet Nat compare) : Nat → TableauOutcome
    | 0 =>
      match findExpandableBranch branches saturated with
      | none => finished branches
      | some _ => .exhausted maxSteps
    | fuel + 1 =>
      match findExpandableBranch branches saturated with
      | none => finished branches
      | some (idx, b) =>
        match applyAllRules sys b with
        | [b'] =>
          if b' == b then go branches (saturated.insert idx) fuel
          else go (branches.set idx b') saturated fuel
        | nbs =>
          let shift := nbs.length - 1
          let saturated' : Std.TreeSet Nat compare := Std.TreeSet.ofList
            (saturated.toList.map fun s => if s > idx then s + shift else s)
          go (branches.take idx ++ nbs ++ branches.drop (idx + 1)) saturated' fuel

/-- Does `premises ⊢ conclusion` hold in `sys`? Closed tableau for
{1 T pᵢ} ∪ {1 F conclusion} means yes. -/
def tableauProves (sys : System) (maxSteps : Nat) (premises : List Formula)
    (conclusion : Formula) : Verdict :=
  let assumptions := premises.map (pfTrue .root) ++ [pfFalse .root conclusion]
  match buildTableau sys maxSteps assumptions with
  | .closed => .definitely true
  | .stillOpen _ => .definitely false
  | .exhausted n => .unknown (.budgetExhausted n)

/-- Is the set satisfiable in `sys`? -/
def tableauConsistent (sys : System) (maxSteps : Nat) (formulas : List Formula) : Verdict :=
  match buildTableau sys maxSteps (formulas.map (pfTrue .root)) with
  | .closed => .definitely false
  | .stillOpen _ => .definitely true
  | .exhausted n => .unknown (.budgetExhausted n)

/-! ## Countermodels (B&D Theorem 6.19) -/

def kripkeCheckable : Formula → Bool
  | .bot | .atomF _ => true
  | .not a | .box a | .diamond a | .futureBox a | .futureDiamond a
  | .pastBox a | .pastDiamond a => kripkeCheckable a
  | .and a b | .or a b | .implies a b | .iff a b | .since a b | .until a b =>
    kripkeCheckable a && kripkeCheckable b
  | _ => false

abbrev Rel := Std.TreeSet (World × World)

def reflexiveClose (ws : List World) (r : Rel) : Rel := r.insertMany (ws.map fun w => (w, w))
def symmetricClose (r : Rel) : Rel := r.insertMany (r.toList.map fun (w, v) => (v, w))

/-- Transitive closure by iterating composition to a fixpoint. Each round
adds at least one pair or stops, so `|ws|² + 1` rounds suffice. -/
def transitiveClose (ws : List World) (r : Rel) : Rel :=
  go r (ws.length * ws.length + 1)
where
  go (r : Rel) : Nat → Rel
    | 0 => r
    | n + 1 =>
      let pairs := r.toList
      let r' := r.insertMany (pairs.flatMap fun (w, x) =>
        pairs.filterMap fun (y, z) => if x == y then some (w, z) else none)
      if r'.size == r.size then r else go r' n

def closeForSystem (sys : System) (ws : List World) (r : Rel) : Rel :=
  match sys.name with
  | "KT" => reflexiveClose ws r
  | "K4" => transitiveClose ws r
  | "KTB" => symmetricClose (reflexiveClose ws r)
  | "S4" => transitiveClose ws (reflexiveClose ws r)
  | "S5" => transitiveClose ws (symmetricClose (reflexiveClose ws r))
  | _ => r

/-- Build the Kripke model read off an open, saturated branch and check that
it really satisfies every signed formula on the branch. -/
def extractCountermodel (sys : System) (b : Branch) : Except String Model := do
  if b.isClosed then throw "extractCountermodel: branch is closed (no countermodel exists)"
  let pfs := b.formulas.toList
  if let some pf := pfs.find? (!kripkeCheckable ·.formula) then
    throw s!"extractCountermodel: formula outside the Kripke fragment: {pf.formula}"
  let prefixes := b.prefixes.toList
  let ws := prefixes.map toString
  let baseRel : Rel := Std.TreeSet.ofList <| prefixes.flatMap fun σ =>
    prefixes.filterMap fun τ => if τ.isChildOf σ then some (toString σ, toString τ) else none
  let rel := closeForSystem sys ws baseRel
  let allAtoms := pfs.foldl (fun acc pf => acc.insertMany pf.formula.atoms) (∅ : Std.TreeSet Atom)
  let vals := allAtoms.toList.map fun a =>
    (a.name, pfs.filterMap fun pf =>
      if pf.sign == .T && pf.formula == .atomF a then some (toString pf.pfx) else none)
  let model := mkModel (← mkFrame ws rel.toList) vals
  for pf in pfs do
    let holds := (← satisfies model (toString pf.pfx) pf.formula) == (pf.sign == .T)
    unless holds do
      throw s!"extractCountermodel: extracted model fails to satisfy {pf.sign} {pf.formula} \
        at {pf.pfx} (branch not saturated for system {sys.name})"
  return model

end Gamen
