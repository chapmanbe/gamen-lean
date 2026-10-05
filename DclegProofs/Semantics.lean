/-!
# DCLEG, Chapter 3, in Lean

This file writes down the syntax and semantics of DCLEG from Chapter 3 of
Jeremiah Chapman, *Doxastic Conditional Logic, Rationality, and Backward
Induction* (Master's thesis, University of Gothenburg, 2026). Page numbers
are the printed ones. Nothing is proved here: this file is the *definitions*
that the proof files (`Lemma4_1.lean`, `Theorem4_2.lean`, …) build on, and
it is the file that most needs Jeremiah's eyes, because a proof about the
wrong definition proves nothing about the thesis.

**How to read this file.** Each definition comes in three parts:

1. a comment `/-! … -/` in plain language saying which part of the thesis
   it renders and how the Lean reads the thesis's wording;
2. the Lean itself;
3. wherever the thesis's wording admits more than one reading, or where
   the Lean has to add or drop something, a line beginning
   `QUESTION FOR JEREMIAH`. There are eleven of them. Each one is a
   decision that should be his, not ours.

**A few words of Lean, once.**

* `structure … where` bundles named components, like a record or a tuple
  with field names. `M.T` is the field `T` of `M`.
* `inductive` defines a type by listing the ways to build its elements
  (constructors). `Formula` below is an inductive type; so are the
  `Prop`-valued relations like `PathFrom`, which are built by listing the
  rules that derive them.
* `Prop` is the type of propositions. A field of type `Prop` in a structure
  is a *condition* the structure must satisfy; a function returning `Prop`
  is a predicate or relation. Nothing here is executable, and nothing here
  needs to be: these definitions are only used to state and prove theorems.
* A set is a predicate. Where the thesis writes `S ⊆ V` for a set of
  nodes, the Lean has `S : Node → Prop`, and "`w ∈ S`" is `S w`. A set of
  world–node pairs (a proposition, in the thesis's sense) is
  `World × Node → Prop`. A set of such sets is `(World × Node → Prop) → Prop`.
* `Option α` is "an element of α, or nothing": `some x` or `none`. It
  renders the thesis's partial functions `Q` and `next`.
* `∃ x, …`, `∀ x, …`, `∧`, `∨`, `¬`, `→`, `↔` mean what they mean in logic.
  `∃ x ∈ l, …` and `∀ x ∈ l, …` range over the members of a list `l`.
* Types are parameters, not fixed carriers. `Agent`, `Move`, `Node`,
  `World`, `PVar` are arbitrary types, so a theorem proved about
  `GameModel Agent Move Node World PVar sig` holds for every choice of
  them. The thesis's finite sets `A`, `M`, `V`, `Γ` become *lists* that
  enumerate the type, or the assertion that such a list exists (see
  `Signature` and the `_finite` fields).
-/

namespace DclegProofs

/-! ## §3.1.1 Formulae (p. 15)

> Let A be a finite set of agents, M a finite set of moves, N a finite set
> of integers, and P a set of propositional variables.

The Lean keeps `A`, `M`, `N` as *lists*, because Chapter 4's formulas
(`BI_z`, `Rat_i`, …) are finite disjunctions and conjunctions *over* those
sets, and to write down such a formula one needs the elements in some
order. The two `_complete` fields say the lists really enumerate the
types. `N ⊆ ℤ` is a list of `Int` with no completeness condition, since
`N` is a subset of the integers, not all of them. -/

/-- The language's parameters A, M, N (§3.1.1, p. 15). `PVar`, the set P
of propositional variables, is left as a type parameter of `Formula`. -/
structure Signature (Agent Move : Type) where
  /-- A, the finite set of agents, listed. -/
  agents : List Agent
  /-- M, the finite set of moves, listed. -/
  moves : List Move
  /-- N, the finite set of integers that payoffs are drawn from. -/
  payoffs : List Int
  agents_complete : ∀ i : Agent, i ∈ agents
  moves_complete : ∀ m : Move, m ∈ moves

/-! The formulas (p. 15–16). Each constructor is one bullet of the thesis's
inductive definition. The counterfactual φ □→ ψ is `cf`; the thesis's
symbol for it did not survive the PDF text extraction, so `□→` is used in
comments throughout. -/

/-- Formulas of DCLEG (§3.1.1, pp. 15–16). -/
inductive Formula (Agent Move PVar : Type) : Type where
  /-- ⊥ -/
  | bot
  /-- p, for p ∈ P -/
  | pvar (p : PVar)
  /-- turnᵢ -/
  | turn (i : Agent)
  /-- m, for m ∈ M: "move m is played this turn" -/
  | move (m : Move)
  /-- kᵢ, for k ∈ N: "player i ultimately gets payoff k" -/
  | payoff (k : Int) (i : Agent)
  /-- ¬φ -/
  | neg (φ : Formula Agent Move PVar)
  /-- φ ∨ ψ -/
  | or (φ ψ : Formula Agent Move PVar)
  /-- φ □→ ψ, the counterfactual conditional -/
  | cf (φ ψ : Formula Agent Move PVar)
  /-- Bᵢ φ -/
  | bel (i : Agent) (φ : Formula Agent Move PVar)
  /-- X φ, "φ will be true immediately after this move" -/
  | next (φ : Formula Agent Move PVar)
  /-- Y φ, "φ was true immediately before this move" -/
  | prev (φ : Formula Agent Move PVar)
  /-- □ φ -/
  | box (φ : Formula Agent Move PVar)

namespace Formula

variable {Agent Move PVar : Type}

/-! Notation. `¬' φ`, `φ ∨' ψ`, `φ ∧' ψ`, `φ □→ ψ`, `□ φ`, `◇ φ` are the
object-language connectives; the primes keep them apart from Lean's own
`¬`, `∨`, `∧`, which are used in the *meta*-language (in definitions of
satisfaction and in theorem statements). `X` and `Y` are written
`.next φ` and `.prev φ`, and `Bᵢ φ` is `.bel i φ`. -/

scoped prefix:max "¬' " => Formula.neg
scoped infixl:65 " ∨' " => Formula.or
scoped infixr:50 " □→ " => Formula.cf
scoped prefix:max "□ " => Formula.box

/-! ### §3.1.2 Abbreviations (p. 16)
Each is a `def` that unfolds to its official form, exactly as on p. 16. -/

/-- ⊤ := ¬⊥ -/
def top : Formula Agent Move PVar := ¬' bot
/-- φ ∧ ψ := ¬(¬φ ∨ ¬ψ) -/
def and (φ ψ : Formula Agent Move PVar) : Formula Agent Move PVar := ¬' (¬' φ ∨' ¬' ψ)
scoped infixl:70 " ∧' " => Formula.and
/-- mᵢ := m ∧ turnᵢ -/
def movei (m : Move) (i : Agent) : Formula Agent Move PVar := move m ∧' turn i
/-- φ □↔ ψ := (φ □→ ψ) ∧ (ψ □→ φ) -/
def cfIff (φ ψ : Formula Agent Move PVar) : Formula Agent Move PVar := (φ □→ ψ) ∧' (ψ □→ φ)
/-- φ ◇→ ψ := ¬(φ □→ ¬ψ), "if φ were true, ψ might be true" -/
def might (φ ψ : Formula Agent Move PVar) : Formula Agent Move PVar := ¬' (φ □→ ¬' ψ)
/-- B̂ᵢ φ := ¬Bᵢ¬φ, "i considers φ plausible" -/
def dbel (i : Agent) (φ : Formula Agent Move PVar) : Formula Agent Move PVar := ¬' (bel i (¬' φ))
/-- ◇φ := ¬□¬φ -/
def dia (φ : Formula Agent Move PVar) : Formula Agent Move PVar := ¬' □ (¬' φ)
scoped prefix:max "◇ " => Formula.dia
/-- start := □¬Y⊤ -/
def start : Formula Agent Move PVar := □ (¬' (prev top))
/-- end := □¬X⊤ -/
def «end» : Formula Agent Move PVar := □ (¬' (next top))

/-- ⋀ over a list: `bigAnd [φ₁, …, φₙ] = φ₁ ∧ (φ₂ ∧ (… ∧ ⊤))`. The thesis's
big conjunctions ⋀_{i∈A}, ⋀_{m∈M} are `bigAnd` over the `Signature` lists. -/
def bigAnd : List (Formula Agent Move PVar) → Formula Agent Move PVar
  | [] => top
  | φ :: rest => φ ∧' bigAnd rest

/-- ⋁ over a list: `bigOr [φ₁, …, φₙ] = φ₁ ∨ (φ₂ ∨ (… ∨ ⊥))`. -/
def bigOr : List (Formula Agent Move PVar) → Formula Agent Move PVar
  | [] => bot
  | φ :: rest => φ ∨' bigOr rest

/-- B^E φ := ⋀_{i∈A} Bᵢ φ, "everyone believes φ". Needs the agent list. -/
def belE (sig : Signature Agent Move) (φ : Formula Agent Move PVar) : Formula Agent Move PVar :=
  bigAnd (sig.agents.map fun i => bel i φ)

/-- AX φ := ¬end ∧ ⋀_{m∈M} (m □→ X φ), "whatever move is played now, φ next". -/
def AX (sig : Signature Agent Move) (φ : Formula Agent Move PVar) : Formula Agent Move PVar :=
  ¬' «end» ∧' bigAnd (sig.moves.map fun m => move m □→ next φ)

end Formula

/-! ## §3.2.1 Strategic structures (p. 17)

> T = ⟨V, EndV, Q, PMoves, next⟩ where V ≠ ∅ is a finite set of nodes,
> EndV ⊂ V is the set of outcome nodes, Q : V → A is a partial function,
> PMoves : V → P(M) is a total function, and next : V × M → V is a
> [partial] function … We impose the following further requirements …

The type `Node` plays V. `EndV` is a predicate on nodes. `Q w = none` is
"Q(w) undefined". `next w m = none` is "next(w,m) undefined". The seven
numbered conditions are the seven fields `cond1` … `cond7`, in the thesis's
order and with its wording paraphrased in the doc comment.

QUESTION FOR JEREMIAH (Q1, condition 5). The thesis writes
`next(w,m) = next(w′,m′) ↔ (w = w′ ∧ m = m′)`. When both sides are
*undefined*, "equal" has no clear meaning, and the ← direction is trivial,
so the Lean states only the → direction and only when both are defined:
"no node can be reached in more than one way," as p. 17 glosses it. Is
that the intended content?

QUESTION FOR JEREMIAH (Q2, `EndV ⊂ V`). Read as *proper* inclusion, since
p. 18 argues that EndV = V "would not be a game in any meaningful sense."
So `endV_proper` demands a decision node. `V ≠ ∅` then follows.

A NOTE, not a question. Page 17 says conditions 4 and 5 "together mean
that no loops can occur in the game tree." As stated they forbid loops of
length one (4) and merging (5), but not, for instance, two decision nodes
a, b with next(a,m) = b and next(b,m′) = a, provided a and b are unreachable
from the root (conditions 6 and 7 are then still met). Such nodes never lie
on any history, so the semantics never sees them; but "depth" is undefined
for them, which is why the proof files carry an explicit `Depth`
hypothesis rather than assuming every node has one. -/

/-- A strategic structure T (§3.2.1, p. 17). -/
structure StrategicStructure (Agent Move Node : Type) where
  /-- EndV: the outcome nodes. -/
  EndV : Node → Prop
  /-- Q: which player moves at a decision node; `none` at outcome nodes. -/
  Q : Node → Option Agent
  /-- PMoves(w): the moves available at w, as a set. -/
  PMoves : Node → Move → Prop
  /-- next(w, m): the successor node, if any. -/
  next : Node → Move → Option Node
  /-- V is finite: some list contains every node. -/
  nodes_finite : ∃ l : List Node, ∀ w : Node, w ∈ l
  /-- EndV ⊂ V, proper: there is a decision node. (Q2) -/
  endV_proper : ∃ w, ¬ EndV w
  /-- 1. Q(w) is undefined iff w ∈ EndV. -/
  cond1 : ∀ w, Q w = none ↔ EndV w
  /-- 2. PMoves(w) = ∅ iff w ∈ EndV. -/
  cond2 : ∀ w, (∀ m, ¬ PMoves w m) ↔ EndV w
  /-- 3. next(w, m) is defined iff m ∈ PMoves(w). -/
  cond3 : ∀ w m, (∃ v, next w m = some v) ↔ PMoves w m
  /-- 4. next(w, m) ≠ w. -/
  cond4 : ∀ w m, next w m ≠ some w
  /-- 5. No node is reached in more than one way. (Q1) -/
  cond5 : ∀ w m w' m' v, next w m = some v → next w' m' = some v → w = w' ∧ m = m'
  /-- 6. Every outcome node is the result of some move at some node. -/
  cond6 : ∀ w, EndV w → ∃ v m, next v m = some w
  /-- 7. Exactly one node has no predecessor. -/
  cond7 : ∃ r, (∀ v m, next v m ≠ some r) ∧ ∀ r', (∀ v m, next v m ≠ some r') → r' = r

namespace StrategicStructure

variable {Agent Move Node : Type}

/-- "w has no predecessor": the property that condition 7 says exactly one
node has. The thesis calls that node the initial node. -/
def IsRoot (T : StrategicStructure Agent Move Node) (w : Node) : Prop :=
  ∀ v m, T.next v m ≠ some w

end StrategicStructure

/-! ## §3.2.2 Histories (pp. 18–19)

> The history function H : Γ → ((V × M)⁺ × EndV) assigns a "history" to
> each possible world. A history is a (non-empty) finite sequence of
> decision node–move pairs ⟨(w₀,m₀), …, (wₑ,mₑ)⟩ together with an outcome
> node wₑ₊₁ ∈ EndV. A history must meet the following conditions:
> 1. w₀ is the unique initial decision node of the game,
> 2. mⱼ ∈ PMoves(wⱼ) for every j = 0, …, e, and
> 3. next(wⱼ, mⱼ) = wⱼ₊₁ for every j = 0, …, e.

`History` is the pair (sequence, outcome). Condition 3 is rendered by the
relation `PathFrom T w₀ steps e`, "starting at w₀, the steps lead to e":
it is built by two rules, one for the empty sequence and one that peels
off the first pair. Conditions 1–3 and non-emptiness are collected in
`History.WellFormed`. -/

/-- A history ⟨⟨(w₀,m₀), …, (wₑ,mₑ)⟩, wₑ₊₁⟩ (p. 18). -/
structure History (Move Node : Type) where
  /-- ⟨(w₀,m₀), …, (wₑ,mₑ)⟩ -/
  steps : List (Node × Move)
  /-- wₑ₊₁ -/
  outcome : Node

/-- `PathFrom T w steps e`: following `steps` from `w`, each move leads to
the next listed node, and the last move leads to `e` (history condition 3). -/
inductive PathFrom {Agent Move Node : Type} (T : StrategicStructure Agent Move Node) :
    Node → List (Node × Move) → Node → Prop where
  | nil (w : Node) : PathFrom T w [] w
  | cons {w : Node} {m : Move} {w' : Node} {rest : List (Node × Move)} {e : Node} :
      T.next w m = some w' → PathFrom T w' rest e → PathFrom T w ((w, m) :: rest) e

namespace History

variable {Agent Move Node : Type}

/-- The nodes a history passes through, ⟨w₀, …, wₑ, wₑ₊₁⟩. This is V_γ
(p. 19) once the history is H(γ). -/
def nodes (h : History Move Node) : List Node := h.steps.map Prod.fst ++ [h.outcome]

/-- The three conditions on a history (p. 18), plus non-emptiness. -/
structure WellFormed (T : StrategicStructure Agent Move Node) (h : History Move Node) : Prop where
  /-- The sequence is non-empty. -/
  nonempty : h.steps ≠ []
  /-- 1 and 3: the sequence starts at the initial node and each move leads
  to the next node, the last to the outcome. -/
  root_path : ∃ w₀, T.IsRoot w₀ ∧ PathFrom T w₀ h.steps h.outcome
  /-- 2: every listed move is available at its node. -/
  moves_possible : ∀ p ∈ h.steps, T.PMoves p.1 p.2
  /-- wₑ₊₁ ∈ EndV. -/
  outcome_end : T.EndV h.outcome

end History

/-! ## Reached nodes, moves, and maximal consistency (pp. 19–20)

These three notions are defined *before* `GameModel` because the model's
own conditions (Self-Awareness, Minimal Revision, …) refer to them. They
take the history function `H` or the premise function `F` as an explicit
argument; inside a model `M` they are used as `M.Reaches`, `M.MoveAt`,
`M.MaxConsistent` (defined after the structure).

* `Reaches H γ w` is `w ∈ V_γ` (p. 19).
* `MoveAt H γ w m` is `Move(γ, w) = m`, defined on p. 20 as "m such that
  (w, m) ∈ H(γ)"; undefined (no m) when w ∉ V_γ or w is the outcome.

QUESTION FOR JEREMIAH (Q3, Move as a relation). `Move(γ,w)` is a partial
*function* in the thesis. The Lean has the relation "(w, m) ∈ H(γ)"
instead, and every clause that uses it (X, Self-Awareness, …) is written
with "there is an m with (w, m) ∈ H(γ) and …". The two readings agree
exactly when a history never visits the same node twice, which follows
from the tree conditions (`Basics.lean` proves it, `moveAt_unique`, so this
is a presentational choice, not a change in content), but please confirm
this is the intended reading of "Move". -/

/-- V_γ (p. 19): w is reached in world γ according to H(γ). -/
def Reaches {Move Node World : Type} (H : World → History Move Node) (γ : World) (w : Node) : Prop :=
  w ∈ (H γ).nodes

/-- Move(γ, w) = m (p. 20): the pair (w, m) occurs in H(γ). -/
def MoveAt {Move Node World : Type} (H : World → History Move Node) (γ : World) (w : Node) (m : Move) : Prop :=
  (w, m) ∈ (H γ).steps

/-! ### Maximal φ-consistency (p. 19)

> We say that a world γ′ is maximally φ-consistent with world γ at node w if:
> 1. (γ′, w) ∈ ⟦φ⟧ and
> 2. there is a non-empty set G ⊆ F(γ, w) where
>    (a) (γ′, w) ∈ ⋂G and
>    (b) for every set G′ with G ⊂ G′ ⊆ F(γ, w), φ and G′ are inconsistent,
>        i.e. (⋂G′) ∩ ⟦φ⟧ = ∅.

This is rendered *literally*, with ⟦φ⟧ abstracted to an arbitrary
proposition `X : World × Node → Prop` (the satisfaction clause below
plugs in ⟦φ⟧). `G` is a set of propositions, `(World × Node → Prop) → Prop`.
The pieces of the definition, in order: `X (γ', w)` is 1; `∃ G` with
`(∃ Y, G Y)` non-empty and `∀ Y, G Y → F γ w Y` for `G ⊆ F(γ,w)`;
`∀ Y, G Y → Y (γ', w)` is 2(a), membership in ⋂G; the last conjunct is
2(b): for every `G'` that contains `G`, differs from it (some `Y` in `G'`
but not `G`), and lies inside `F(γ,w)`, no pair `p` is both in ⋂G′ and in X.

QUESTION FOR JEREMIAH (Q4, ⋂ of the empty family). Condition 2 demands
G non-empty, so ⋂G is always an intersection of at least one set, and no
convention for ⋂∅ is needed here. But Centering (below) writes ⋂F(γ,w),
and F(γ,w) is not required to be non-empty; the Lean encodes ⋂ as
"belongs to every member", under which ⋂∅ is everything. Under that
reading Centering forces F(γ,w) ≠ ∅ (`Basics.lean`, `F_nonempty`). Is
that the intended consequence? -/

/-- γ' is maximally X-consistent with γ at w, for a proposition X (p. 19). -/
def MaxConsistent {Node World : Type}
    (F : World → Node → (World × Node → Prop) → Prop)
    (γ : World) (w : Node) (X : World × Node → Prop) (γ' : World) : Prop :=
  X (γ', w) ∧
  ∃ G : (World × Node → Prop) → Prop,
    (∃ Y, G Y) ∧
    (∀ Y, G Y → F γ w Y) ∧
    (∀ Y, G Y → Y (γ', w)) ∧
    (∀ G' : (World × Node → Prop) → Prop,
      (∀ Y, G Y → G' Y) → (∃ Y, G' Y ∧ ¬ G Y) → (∀ Y, G' Y → F γ w Y) →
      ∀ p, (∀ Y, G' Y → Y p) → X p → False)

/-! ## §3.2.2 Game models (pp. 18–20)

> M = ⟨T, Γ, H, F, π, {R^w | w ∈ V}, {{⊒ʷᵢ | w ∈ V} | i ∈ A}, {Pᵢ | i ∈ A}⟩

Field by field, with the thesis's requirements as `Prop` fields:

* `T`, the strategic structure; `World` plays Γ, with `worlds_finite`.
* `H` with `H_wf` (each history is well-formed) and `H_covers` (p. 19:
  "for every w ∈ EndV, there is at least one γ ∈ Γ with w ∈ V_γ").
* `π : P → P(I)`; `π_sub` says each π(p) ⊆ I, i.e. consists of reached
  pairs. `I` itself is `Reaches`.
* `P i w` is Pᵢ(w); `P_range` says it lands in N at outcome nodes.
* `R^w` is not a field: p. 19 *defines* it as {(β,γ) | w ∈ V_γ ∩ V_β}, and
  the □ clause of satisfaction uses that definition directly.
* `F` with `F_sub` (premises are subsets of I), `centering` and
  `contemporary_universality` (p. 19), and `F_finite`.
* `dox i w γ δ` is γ ⊒ʷᵢ δ, with the eight conditions of p. 20.

QUESTION FOR JEREMIAH (Q5, |Γ| ≥ |EndV|). This requirement (p. 18) is
omitted as a field: `H_covers` gives a surjection from worlds onto outcome
nodes, so it follows, and cardinalities are awkward without a library.

QUESTION FOR JEREMIAH (Q6, `F_finite`). Γ and V are finite, so I is
finite, so P(P(I)) is finite, so each F(γ,w) is finite. The Lean *assumes*
the last step (`F_finite`) rather than deriving it, since the derivation
is bookkeeping about finiteness that adds nothing about DCLEG. It matters:
two facts the hand proofs use, "◇φ gives a maximally φ-consistent world"
(p. 22) and "(φ □→ ψ) ∧ (φ □→ χ) gives (φ ∧ χ) □→ ψ" (used at (5.6)), need
a *maximal* G to exist, which finiteness of F(γ,w) guarantees.

QUESTION FOR JEREMIAH (Q7, Centering's domain). F is defined on all of
Γ × V, and Centering is stated for all γ, w. But if w ∉ V_γ then
(γ,w) ∉ I, while ⋂F(γ,w) ⊆ I whenever F(γ,w) ≠ ∅, so Centering at such a
pair is unsatisfiable; and if F(γ,w) = ∅ then ⋂F(γ,w) is I (or everything),
which is not {(γ,w)} either. So Centering as printed can only hold if every
world reaches every node. The Lean therefore states Centering only for
reached pairs (γ, w), and only over pairs p ∈ I; that is the reading under
which models exist. Please confirm.

QUESTION FOR JEREMIAH (Q8, Self-Awareness). "{Move(δ,w) | δ ∈ ⊒ʷᵢ(γ)} =
{Move(γ,w)}" as a set equation also says ⊒ʷᵢ(γ) ≠ ∅. The Lean states the
pointwise content: on i's turn, every world i considers plausible makes the
same move as γ (and has a move exactly when γ does). Non-emptiness is
Present Seriality when w ∈ V_γ; when w ∉ V_γ the set equation cannot hold
literally, since Move(γ,w) is undefined. Is the pointwise reading right?

QUESTION FOR JEREMIAH (Q9, Expectational Continuity's antecedent).
"{Move(δ,w) | δ ∈ ⊒ʷᵢ(γ)} = {m}" is read as: ⊒ʷᵢ(γ) ≠ ∅ and every δ in it
has Move(δ,w) = m. -/

/-- A game model (§3.2.2, pp. 18–20). -/
structure GameModel (Agent Move Node World PVar : Type) (sig : Signature Agent Move) where
  /-- T, the strategic structure. -/
  T : StrategicStructure Agent Move Node
  /-- Γ is finite. -/
  worlds_finite : ∃ l : List World, ∀ γ : World, γ ∈ l
  /-- H, the history function. -/
  H : World → History Move Node
  /-- Every H(γ) meets the three history conditions. -/
  H_wf : ∀ γ, (H γ).WellFormed T
  /-- Every outcome node is reached in some world (p. 19). -/
  H_covers : ∀ w, T.EndV w → ∃ γ, Reaches H γ w
  /-- π, the valuation. -/
  π : PVar → World × Node → Prop
  /-- π(p) ⊆ I. -/
  π_sub : ∀ p γ w, π p (γ, w) → Reaches H γ w
  /-- Pᵢ, the payoff functions. -/
  P : Agent → Node → Int
  /-- Pᵢ : EndV → N. -/
  P_range : ∀ i w, T.EndV w → P i w ∈ sig.payoffs
  /-- F, the premise function: `F γ w Y` means Y ∈ F(γ, w). -/
  F : World → Node → (World × Node → Prop) → Prop
  /-- Each premise is a subset of I. -/
  F_sub : ∀ γ w Y, F γ w Y → ∀ p, Y p → Reaches H p.1 p.2
  /-- Each F(γ, w) is finite. (Q6) -/
  F_finite : ∀ γ w, ∃ l : List (World × Node → Prop), ∀ Y, F γ w Y → Y ∈ l
  /-- F1, Centering: ⋂F(γ,w) = {(γ,w)}, for reached (γ,w), over p ∈ I. (Q7) -/
  centering : ∀ γ w, Reaches H γ w →
    ∀ p : World × Node, Reaches H p.1 p.2 → ((∀ Y, F γ w Y → Y p) ↔ p = (γ, w))
  /-- F2, Contemporary Universality: w ∈ V_β → (β,w) ∈ ⋃F(γ,w). -/
  contemporary_universality : ∀ β γ w, Reaches H β w → ∃ Y, F γ w Y ∧ Y (β, w)
  /-- γ ⊒ʷᵢ δ: δ is doxastically accessible from γ for i at w. -/
  dox : Agent → Node → World → World → Prop
  /-- 1, Presence: if w ∉ V_γ then no world accesses γ at w. -/
  presence : ∀ i w γ, ¬ Reaches H γ w → ∀ β, ¬ dox i w β γ
  /-- 2, Present Seriality: if w ∈ V_γ then ⊒ʷᵢ(γ) ≠ ∅. -/
  present_seriality : ∀ i w γ, Reaches H γ w → ∃ δ, dox i w γ δ
  /-- 3, Transitivity. -/
  transitivity : ∀ i w α β γ, dox i w α β → dox i w β γ → dox i w α γ
  /-- 4, Euclideanness. -/
  euclidean : ∀ i w α β γ, dox i w α β → dox i w α γ → dox i w β γ
  /-- 5, Self-Awareness: if Q(w) = i, every δ ∈ ⊒ʷᵢ(γ) has Move(δ,w) = Move(γ,w). (Q8) -/
  self_awareness : ∀ i w γ, T.Q w = some i →
    ∀ δ, dox i w γ δ → ∀ m, (MoveAt H δ w m ↔ MoveAt H γ w m)
  /-- 6, Minimal Revision: if Move(γ,w) = m and w′ = next(w,m), then
  ⊒ʷ′ᵢ(γ) ⊆ ⋃{ max^m_{F(δ,w)}(Γ) | δ ∈ ⊒ʷᵢ(γ) }, where max^m is maximal
  consistency with ⟦m⟧ = {(β,v) ∈ I | Move(β,v) = m}. -/
  minimal_revision : ∀ i w γ m w', MoveAt H γ w m → T.next w m = some w' →
    ∀ δ, dox i w' γ δ →
      ∃ ε, dox i w γ ε ∧
        MaxConsistent F ε w (fun p => Reaches H p.1 p.2 ∧ MoveAt H p.1 p.2 m) δ
  /-- 7, Expectational Continuity: if Move(γ,w) = m, w′ = next(w,m), and
  every world in ⊒ʷᵢ(γ) (non-empty) makes move m at w, then ⊒ʷ′ᵢ(γ) = ⊒ʷᵢ(γ). (Q9) -/
  expectational_continuity : ∀ i w γ m w', MoveAt H γ w m → T.next w m = some w' →
    (∃ δ, dox i w γ δ) → (∀ δ, dox i w γ δ → ∀ m', MoveAt H δ w m' ↔ m' = m) →
    ∀ δ, (dox i w' γ δ ↔ dox i w γ δ)
  /-- 8, Recall: if Move(γ,w) = m and w′ = next(w,m), then
  ⊒ʷᵢ(γ) = ⋃{ ⊒ʷᵢ(δ) | δ ∈ ⊒ʷ′ᵢ(γ) }. -/
  recall : ∀ i w γ m w', MoveAt H γ w m → T.next w m = some w' →
    ∀ ε, (dox i w γ ε ↔ ∃ δ, dox i w' γ δ ∧ dox i w δ ε)

namespace GameModel

variable {Agent Move Node World PVar : Type} {sig : Signature Agent Move}

/-- w ∈ V_γ. -/
abbrev Reaches (M : GameModel Agent Move Node World PVar sig) (γ : World) (w : Node) : Prop :=
  DclegProofs.Reaches M.H γ w

/-- Move(γ, w) = m. -/
abbrev MoveAt (M : GameModel Agent Move Node World PVar sig) (γ : World) (w : Node) (m : Move) : Prop :=
  DclegProofs.MoveAt M.H γ w m

/-- max^X_{F(γ,w)}(Γ) ∋ γ′, for a proposition X. -/
abbrev MaxConsistent (M : GameModel Agent Move Node World PVar sig)
    (γ : World) (w : Node) (X : World × Node → Prop) (γ' : World) : Prop :=
  DclegProofs.MaxConsistent M.F γ w X γ'

end GameModel

/-! ## §3.2.3 Satisfaction (pp. 20–21)

> Take a game model M, a possible world γ, and a node w such that w ∈ V_γ.
> We then define satisfaction on a pointed model M, γ, w as follows: …

`sat M γ w φ` is "M, γ, w ⊩ φ". It is defined by recursion on φ, one case
per line of the table on p. 21, in the table's order. The Lean function is
*total*: it assigns a truth value even when w ∉ V_γ, where the thesis
leaves satisfaction undefined. Every theorem in this package quantifies
only over pointed models with `M.Reaches γ w`, so the extra values are
never used; and the clauses for Bᵢ, X, Y, □, □→ all stay inside I on their
own (Presence keeps Bᵢ inside; R^w, V_γ, and ⟦φ⟧ ⊆ I do the rest).

Clause by clause:

* `kᵢ`: Pᵢ(wₑ₊₁) = k, where wₑ₊₁ is the outcome of H(γ).
* `Bᵢ φ`: "w ∈ V_γ and M, μ, w ⊩ φ for every μ with γ ⊒ʷᵢ μ", conjunct
  included as printed.
* `X φ`: "M, γ, w′ ⊩ φ where w′ = next(w, Move(γ, w))": there is a move m
  with (w, m) ∈ H(γ) and next(w, m) = w′ and φ at w′. False when Move(γ,w)
  is undefined (w an outcome node, or w ∉ V_γ), which is what p. 21's
  "if w ∈ EndV then □¬X⊤" requires. (Q3)
* `Y φ`: "w = next(w′, Move(γ, w′))": there is a pair (w′, m) in H(γ) with
  next(w′, m) = w and φ at w′. Condition 5 makes w′ unique.
* `□ φ`: for every β with γ R^w β, i.e. w ∈ V_γ ∩ V_β.
* `φ □→ ψ`: for every β maximally ⟦φ⟧-consistent with γ at w, ψ at β, where
  ⟦φ⟧ = {(β, v) ∈ I | M, β, v ⊩ φ}: the `Reaches` conjunct keeps ⟦φ⟧ ⊆ I,
  as p. 19 requires of every proposition.

QUESTION FOR JEREMIAH (Q10, the Bᵢ clause's "w ∈ V_γ"). Kept as printed;
it is redundant on pointed models (where w ∈ V_γ is presupposed). Fine? -/

/-- M, γ, w ⊩ φ (p. 21). -/
def sat {Agent Move Node World PVar : Type} {sig : Signature Agent Move}
    (M : GameModel Agent Move Node World PVar sig) :
    World → Node → Formula Agent Move PVar → Prop
  | _, _, .bot => False
  | γ, w, .pvar p => M.π p (γ, w)
  | _, w, .turn i => M.T.Q w = some i
  | γ, w, .move m => M.MoveAt γ w m
  | γ, _, .payoff k i => M.P i (M.H γ).outcome = k
  | γ, w, .neg φ => ¬ sat M γ w φ
  | γ, w, .or φ ψ => sat M γ w φ ∨ sat M γ w ψ
  | γ, w, .bel i φ => M.Reaches γ w ∧ ∀ μ, M.dox i w γ μ → sat M μ w φ
  | γ, w, .next φ => ∃ m w', M.MoveAt γ w m ∧ M.T.next w m = some w' ∧ sat M γ w' φ
  | γ, w, .prev φ => ∃ w' m, M.MoveAt γ w' m ∧ M.T.next w' m = some w ∧ sat M γ w' φ
  | γ, w, .box φ => ∀ β, (M.Reaches γ w ∧ M.Reaches β w) → sat M β w φ
  | γ, w, .cf φ ψ =>
      ∀ β, M.MaxConsistent γ w (fun p => M.Reaches p.1 p.2 ∧ sat M p.1 p.2 φ) β → sat M β w ψ

/-- ⟦φ⟧: the proposition expressed by φ (p. 19), a subset of I. -/
def extension {Agent Move Node World PVar : Type} {sig : Signature Agent Move}
    (M : GameModel Agent Move Node World PVar sig) (φ : Formula Agent Move PVar) :
    World × Node → Prop :=
  fun p => M.Reaches p.1 p.2 ∧ sat M p.1 p.2 φ

/-! ## Validity

The thesis says "φ is a validity of DCLEG" (Theorem 4.2, p. 31; Theorem
5.1, p. 40; Lemma 5.2, p. 43) without a separate definition; the natural
reading, used here, is: satisfied at every pointed model M, γ, w with
w ∈ V_γ, for every game model M over the given signature and over any
choice of the types of nodes and worlds.

QUESTION FOR JEREMIAH (Q11). Validity is relative to the signature
(A, M, N are part of the language, and the formulas BI_z, Rat_i, … depend on
them). Is "for every game model over this signature" the intended
quantification? -/

/-- φ is valid: true at every pointed model over the signature. -/
def Valid {Agent Move PVar : Type} (sig : Signature Agent Move) (φ : Formula Agent Move PVar) : Prop :=
  ∀ (Node World : Type) (M : GameModel Agent Move Node World PVar sig) (γ : World) (w : Node),
    M.Reaches γ w → sat M γ w φ

end DclegProofs
