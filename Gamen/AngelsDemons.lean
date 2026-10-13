import Std.Data.HashMap
import Std.Data.HashSet
import Std.Data.TreeSet

/-!
# Gamen.AngelsDemons

Strategic Deconstruction, Construction and Update Logics (SDL, SCL, SUL) over weighted
graphs: a *demon* removes edges, an *angel* adds edges, up to a cost, and a *traveller*
moves along the edges. Lean-only. Issue #3, item 2.

Source: Catta, Galimullin & Mittelmann, *On Angels and Demons: Strategic (De)Construction
of Dynamic Models*, AAMAS 2026, doi:10.65109/xezz1033 (Defs 1-11; Theorem 5 gives the
complexity, PSPACE for SDL). Checked against the PDF in `~/Downloads/XEZZ1033.pdf`.

## What the cost bounds

The bound `n` of `⟨⟨n⟩⟩ψ` limits how much the modifier changes the graph *at each step*:
a path is a sequence of pointed models, each reached from the last by removing (adding)
edges of total cost at most `n` and then letting the traveller move (Defs 2, 3, 6). The
budget is not spent over the whole play, and edges removed or added stay removed or added.
So the bound is a budget on *graph change*, not a cost on agents' actions; `Gamen.Atl.Dynamic`
changes which actions agents have, this module changes the transition graph.

## Semantics implemented

* a model is a finite serial graph with a positive cost on every ordered pair, and atoms;
* a strategy is a function of the pointed model, so (as for ATL) it is positional on the
  finite *arena* of pointed models `(edge set, state)`; the model checker solves that game
  with the usual fixpoints: `Xφ` one step, `φ U ψ` least, `φ R ψ` greatest;
* every model along a play must be serial (Def 1, preserved by every accessibility
  relation): a removal that leaves a state with no successor is not a legal move;
* `[n]ψ := ¬⟨⟨n⟩⟩¬ψ`; `□φ := ⟨⟨0⟩⟩Xφ` and `◇φ := [0]Xφ` are the usual modalities.

**SUL: only the cooperative update.** SUL has four coalitions (Def 10). `update a d ψ` is
`⟨[angel a, demon d]⟩ψ` (both modifiers cooperate against the traveller) and its dual. The
other three quantify universally over the opponent's strategy while the two modifiers move
at once, and the paper does not say what a joint move that leaves a non-serial model means
under a universal opponent, so they are not implemented rather than guessed.

## Cost of the check

The arena is every model reachable by the formula's moves, built explicitly; `maxModels`
caps it, and exceeding it is an error, never a partial answer. Edge sets are bitmasks over
`k × k` bits, `k` the number of states.
-/
namespace Gamen
namespace AngelsDemons

/-- A weighted model (Def 1). States are indexed `0..k-1`. -/
structure WModel where
  states : Array String
  /-- Edges `(i, j)`: `i → j`. -/
  edges : List (Nat × Nat)
  /-- Cost of adding or removing the edge `i → j`; positive for every ordered pair. -/
  cost : Nat → Nat → Nat
  labels : Nat → Std.TreeSet String

def WModel.k (m : WModel) : Nat := m.states.size

/-- Edge `i → j` is bit `i * k + j`. -/
def bit (k i j : Nat) : Nat := i * k + j

def maskOf (k : Nat) (es : List (Nat × Nat)) : Nat :=
  es.foldl (fun acc (i, j) => acc ||| (1 <<< bit k i j)) 0

def hasEdge (k mask i j : Nat) : Bool := mask.testBit (bit k i j)

def serial (k mask : Nat) : Bool :=
  (List.range k).all fun i => (List.range k).any fun j => hasEdge k mask i j

/-- Build a model, checking that it is non-empty, in range, has positive costs everywhere and
is serial. -/
def mkWModel (states : List String) (edges : List (Nat × Nat)) (cost : Nat → Nat → Nat)
    (labels : Nat → List String := fun _ => []) : Except String WModel := do
  if states.isEmpty then throw "mkWModel: a model needs at least one state"
  let k := states.length
  if let some (i, j) := edges.find? (fun (i, j) => i ≥ k || j ≥ k) then
    throw s!"mkWModel: edge {i} → {j} names a state outside 0..{k - 1}"
  for i in List.range k do
    for j in List.range k do
      if cost i j == 0 then throw s!"mkWModel: the cost of {i} → {j} must be positive"
  unless serial k (maskOf k edges) do throw "mkWModel: the transition relation is not serial"
  pure { states := states.toArray, edges, cost, labels := fun i => Std.TreeSet.ofList (labels i) }

mutual
/-- State formulas of SDL/SCL/SUL. -/
inductive SFormula where
  | atom (name : String)
  | not (f : SFormula)
  | and (l r : SFormula)
  | or (l r : SFormula)
  /-- `⟨⟨n⟩⟩ψ`, demonic. -/
  | demon (n : Nat) (psi : PFormula)
  /-- `[n]ψ := ¬⟨⟨n⟩⟩¬ψ`. -/
  | demonBox (n : Nat) (psi : PFormula)
  /-- `⟨⟨n⟩⟩ψ`, angelic. -/
  | angel (n : Nat) (psi : PFormula)
  | angelBox (n : Nat) (psi : PFormula)
  /-- `⟨[angel a, demon d]⟩ψ`: the cooperative SUL modality. -/
  | update (a d : Nat) (psi : PFormula)
  | updateBox (a d : Nat) (psi : PFormula)

/-- Path formulas. -/
inductive PFormula where
  | next (f : SFormula)
  | until (l r : SFormula)
  | release (l r : SFormula)
end

/-- `¬ψ` pushed through the temporal operators (Def 13). -/
def PFormula.neg : PFormula → PFormula
  | .next f => .next (.not f)
  | .until l r => .release (.not l) (.not r)
  | .release l r => .until (.not l) (.not r)

/-- `Fφ := ⊤ U φ`, `Gφ := ⊥ R φ`. -/
def SFormula.top : SFormula := .not (.and (.atom "") (.not (.atom "")))
def PFormula.eventually (f : SFormula) : PFormula := .until SFormula.top f
def PFormula.always (f : SFormula) : PFormula := .release (.not SFormula.top) f

/-- Who moves. -/
inductive Kind where
  | demon (n : Nat)
  | angel (n : Nat)
  | both (a d : Nat)
  deriving BEq, Hashable

mutual
def kindsS : SFormula → List Kind
  | .atom _ => []
  | .not f => kindsS f
  | .and l r | .or l r => kindsS l ++ kindsS r
  | .demon n p | .demonBox n p => .demon n :: kindsP p
  | .angel n p | .angelBox n p => .angel n :: kindsP p
  | .update a d p | .updateBox a d p => .both a d :: kindsP p
def kindsP : PFormula → List Kind
  | .next f => kindsS f
  | .until l r | .release l r => kindsS l ++ kindsS r
end

/-- Subsets of `items = (bit, cost)` of total cost at most `budget`, as masks (the empty
set included). Costs are positive, so the cost bound prunes the search. -/
def subsetsWithin : List (Nat × Nat) → Nat → List Nat
  | [], _ => [0]
  | (b, c) :: rest, budget =>
    subsetsWithin rest budget
      ++ (if c ≤ budget then (subsetsWithin rest (budget - c)).map (· ||| (1 <<< b)) else [])

/-- Models reachable from edge set `e` in one modifier move of kind `kind`. -/
def movesFrom (m : WModel) (kind : Kind) (e : Nat) : List Nat :=
  let k := m.k
  let pairs := (List.range k).flatMap fun i => (List.range k).map fun j => (i, j)
  let present := pairs.filter fun (i, j) => hasEdge k e i j
  let absent := pairs.filter fun (i, j) => !hasEdge k e i j
  let item (p : Nat × Nat) : Nat × Nat := (bit k p.1 p.2, m.cost p.1 p.2)
  let removals (d : Nat) := subsetsWithin (present.map item) d
  let additions (a : Nat) := subsetsWithin (absent.map item) a
  let raw : List Nat := match kind with
    | .demon n => (removals n).map fun b => e ^^^ b
    | .angel n => (additions n).map fun a => e ||| a
    | .both a d => (removals d).flatMap fun b => (additions a).map fun x => (e ^^^ b) ||| x
  let seen : Std.HashSet Nat := raw.foldl (fun s x => if serial k x then s.insert x else s) {}
  seen.toList

/-- The explicit arena: every model reachable from the initial one by the formula's moves. -/
structure Arena where
  models : Array Nat
  index : Std.HashMap Nat Nat
  /-- `moves kind` : for each model index, the model indices reachable in one move. -/
  moves : Std.HashMap Kind (Array (Array Nat))

def buildArena (m : WModel) (kinds : List Kind) (maxModels : Nat) : Except String Arena := do
  let kinds := kinds.foldl (fun acc k => if acc.contains k then acc else acc ++ [k]) []
  let e0 := maskOf m.k m.edges
  let mut models : Array Nat := #[e0]
  let mut index : Std.HashMap Nat Nat := ({} : Std.HashMap Nat Nat).insert e0 0
  let mut i := 0
  let mut moveLists : Std.HashMap Kind (Array (List Nat)) := {}
  for kd in kinds do moveLists := moveLists.insert kd #[]
  while i < models.size do
    let e := models[i]!
    for kd in kinds do
      let next := movesFrom m kd e
      for x in next do
        unless index.contains x do
          if models.size ≥ maxModels then
            throw s!"arena too large: more than {maxModels} models reachable by the formula's moves"
          index := index.insert x models.size
          models := models.push x
      moveLists := moveLists.insert kd ((moveLists.getD kd #[]).push next)
    i := i + 1
  let moves := moveLists.fold (init := ({} : Std.HashMap Kind (Array (Array Nat))))
    fun acc kd ls => acc.insert kd (ls.map fun l => (l.map fun x => index.getD x 0).toArray)
  pure { models, index, moves }

private def succs (k mask s : Nat) : List Nat :=
  (List.range k).filter fun t => hasEdge k mask s t

/-- One step of the game: the positions from which the modifier can move so that every
traveller reply lands in `x`. -/
def pre (m : WModel) (ar : Arena) (kind : Kind) (x : Array Bool) : Array Bool :=
  let k := m.k
  let mv := ar.moves.getD kind #[]
  (Array.range (ar.models.size * k)).map fun pos =>
    let mi := pos / k
    let s := pos % k
    (mv.getD mi #[]).any fun mj =>
      (succs k (ar.models[mj]!) s).all fun t => x.getD (mj * k + t) false

private def iterate (step : Array Bool → Array Bool) (start : Array Bool) (fuel : Nat) :
    Except String (Array Bool) := do
  let mut cur := start
  for _ in [0:fuel] do
    let nxt := step cur
    if nxt == cur then return cur
    cur := nxt
  throw "fixpoint did not converge within |positions| + 1 steps"

/-- Pointwise combination of two position sets of equal size. -/
def zip2 (f : Bool → Bool → Bool) (a b : Array Bool) : Array Bool :=
  (Array.range a.size).map fun i => f (a.getD i false) (b.getD i false)

mutual
/-- Positions `(model, state)` satisfying a state formula. Index `model * k + state`. -/
def satS (m : WModel) (ar : Arena) : SFormula → Except String (Array Bool)
  | .atom n => pure ((Array.range (ar.models.size * m.k)).map fun pos =>
      (m.labels (pos % m.k)).contains n)
  | .not f => do pure ((← satS m ar f).map (!·))
  | .and l r => do pure (zip2 (· && ·) (← satS m ar l) (← satS m ar r))
  | .or l r => do pure (zip2 (· || ·) (← satS m ar l) (← satS m ar r))
  | .demon n p => satP m ar (.demon n) false p
  | .demonBox n p => do pure ((← satP m ar (.demon n) true p).map (!·))
  | .angel n p => satP m ar (.angel n) false p
  | .angelBox n p => do pure ((← satP m ar (.angel n) true p).map (!·))
  | .update a d p => satP m ar (.both a d) false p
  | .updateBox a d p => do pure ((← satP m ar (.both a d) true p).map (!·))

/-- Positions from which the modifier of kind `kind` has a strategy making `ψ` true on all
traveller replies (Defs 5, 8, 11). With `negated`, the strategy is for `¬ψ` instead, pushed
through the temporal operator (`¬(l U r) = ¬l R ¬r`, ...; Def 13); the box modalities use it,
and it keeps the recursion on subformulas. -/
def satP (m : WModel) (ar : Arena) (kind : Kind) (negated : Bool) :
    PFormula → Except String (Array Bool)
  | .next f => do
      let sf ← satS m ar f
      pure (pre m ar kind (if negated then sf.map (!·) else sf))
  | .until l r => do
      let sl ← satS m ar l
      let sr ← satS m ar r
      if negated then
        let nl := sl.map (!·)
        let nr := sr.map (!·)
        iterate (fun z => zip2 (· && ·) nr (zip2 (· || ·) nl (pre m ar kind z)))
          (Array.replicate sr.size true) (sr.size + 1)
      else
        iterate (fun z => zip2 (· || ·) sr (zip2 (· && ·) sl (pre m ar kind z)))
          (Array.replicate sr.size false) (sr.size + 1)
  | .release l r => do
      let sl ← satS m ar l
      let sr ← satS m ar r
      if negated then
        let nl := sl.map (!·)
        let nr := sr.map (!·)
        iterate (fun z => zip2 (· || ·) nr (zip2 (· && ·) nl (pre m ar kind z)))
          (Array.replicate sr.size false) (sr.size + 1)
      else
        iterate (fun z => zip2 (· && ·) sr (zip2 (· || ·) sl (pre m ar kind z)))
          (Array.replicate sr.size true) (sr.size + 1)
end

/-- The states of the initial model satisfying `f`, by name. `maxModels` caps the arena. -/
def satStates (m : WModel) (f : SFormula) (maxModels : Nat := 20000) :
    Except String (List String) := do
  let ar ← buildArena m (kindsS f) maxModels
  let s ← satS m ar f
  pure ((List.range m.k).filter (fun i => s.getD i false) |>.map fun i => m.states[i]!)

/-- `(M, s) ⊨ f` at the initial model. -/
def holdsAt (m : WModel) (f : SFormula) (s : String) (maxModels : Nat := 20000) :
    Except String Bool := do pure ((← satStates m f maxModels).contains s)

end AngelsDemons
end Gamen
