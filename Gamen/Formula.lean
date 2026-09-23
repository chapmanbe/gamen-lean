import Std.Data.TreeSet

/-!
# Gamen.Formula

Port of `gamen-hs/src/Gamen/Formula.hs`: the 30-constructor formula ADT,
pretty-printing, `atoms`, and negation normal form.

B&D Definition 1.1 (formulas of basic modal logic), extended with the
temporal, epistemic, doxastic, STIT, deontic-STIT, and ATL operators used
elsewhere in gamen.
-/
namespace Gamen

/-- Propositional variable. Haskell: `newtype Atom = MkAtom { atomName :: String }`. -/
structure Atom where
  name : String
  deriving BEq, Ord, Hashable, Repr, DecidableEq, Inhabited

instance : ToString Atom := ⟨Atom.name⟩

/-- The formula ADT. Every function on `Formula` must handle all 30
constructors; Lean rejects a non-exhaustive `match` at compile time. -/
inductive Formula where
  | bot                                     -- ⊥
  | atomF (a : Atom)                        -- propositional variable (use `Formula.atom`)
  | not (f : Formula)                       -- ¬A
  | and (l r : Formula)                     -- A ∧ B
  | or (l r : Formula)                      -- A ∨ B
  | implies (l r : Formula)                 -- A → B
  | iff (l r : Formula)                     -- A ↔ B
  | box (f : Formula)                       -- □A
  | diamond (f : Formula)                   -- ◇A
  | futureBox (f : Formula)                 -- GA
  | futureDiamond (f : Formula)             -- FA
  | pastBox (f : Formula)                   -- HA
  | pastDiamond (f : Formula)               -- PA
  | since (l r : Formula)                   -- B S C
  | until (l r : Formula)                   -- B U C
  | knowledge (agent : String) (f : Formula)  -- K_a A
  | belief (agent : String) (f : Formula)     -- B_a A (KD45)
  | rankedBelief (agent : String) (rank : Int) (f : Formula)  -- Spohn 1988
  | announce (b c : Formula)                -- [B]C
  | stit (agent : String) (f : Formula)     -- [i]A
  | choiceDiamond (agent : String) (f : Formula)  -- ⟨i⟩A
  | groupStit (f : Formula)                 -- [Agt]A
  | next (f : Formula)                      -- XA (LACA)
  | ought (agent : String) (f : Formula)    -- ⊗_i A
  | permitted (agent : String) (f : Formula)  -- ⊖_i A
  | coalition (agents : List String) (f : Formula)  -- [C]φ (Pauly 2002)
  | canNext (agents : List String) (f : Formula)    -- ⟨⟨C⟩⟩Xφ
  | canAlways (agents : List String) (f : Formula)  -- ⟨⟨C⟩⟩Gφ
  | canEventually (agents : List String) (f : Formula)  -- ⟨⟨C⟩⟩Fφ
  | canUntil (agents : List String) (l r : Formula)     -- ⟨⟨C⟩⟩(φ U ψ)
  deriving BEq, Ord, Hashable, Repr, DecidableEq, Inhabited

namespace Formula

/-- `Formula.atom "p"` builds and matches an atom by name. Lean's analog of
the Haskell `pattern Atom` synonym: `@[match_pattern]` lets it appear in
patterns while exhaustiveness checking still sees `atomF`. -/
@[match_pattern] abbrev atom (n : String) : Formula := .atomF ⟨n⟩

def top : Formula := .not .bot

private def agentsStr (as : List String) : String := ",".intercalate as

/-- Haskell `showsPrec`: binary connectives are always parenthesized, unary
prefixes bind tightly. -/
protected def toString : Formula → String
  | .bot => "⊥"
  | .atomF a => a.name
  | .not f => "¬" ++ f.toString
  | .and l r => s!"({l.toString} ∧ {r.toString})"
  | .or l r => s!"({l.toString} ∨ {r.toString})"
  | .implies l r => s!"({l.toString} → {r.toString})"
  | .iff l r => s!"({l.toString} ↔ {r.toString})"
  | .box f => "□" ++ f.toString
  | .diamond f => "◇" ++ f.toString
  | .futureBox f => "G" ++ f.toString
  | .futureDiamond f => "F" ++ f.toString
  | .pastBox f => "H" ++ f.toString
  | .pastDiamond f => "P" ++ f.toString
  | .since l r => s!"({l.toString} S {r.toString})"
  | .until l r => s!"({l.toString} U {r.toString})"
  | .knowledge a f => s!"K[{a}]{f.toString}"
  | .belief a f => s!"B[{a}]{f.toString}"
  | .rankedBelief a n f => s!"κ[{a},{n}]{f.toString}"
  | .announce b c => s!"[{b.toString}]{c.toString}"
  | .stit a f => s!"[{a}]{f.toString}"
  | .choiceDiamond a f => s!"<{a}>{f.toString}"
  | .groupStit f => "[Agt]" ++ f.toString
  | .next f => "X" ++ f.toString
  | .ought a f => s!"O[{a}]{f.toString}"
  | .permitted a f => s!"P[{a}]{f.toString}"
  | .coalition as f => s!"[[{agentsStr as}]]{f.toString}"
  | .canNext as f => s!"⟨⟨{agentsStr as}⟩⟩X{f.toString}"
  | .canAlways as f => s!"⟨⟨{agentsStr as}⟩⟩G{f.toString}"
  | .canEventually as f => s!"⟨⟨{agentsStr as}⟩⟩F{f.toString}"
  | .canUntil as l r => s!"⟨⟨{agentsStr as}⟩⟩({l.toString} U {r.toString})"

instance : ToString Formula := ⟨Formula.toString⟩

/-- True if the formula contains no □ or ◇ (nor any other modal operator). -/
def isModalFree : Formula → Bool
  | .bot | .atomF _ => true
  | .not f => f.isModalFree
  | .and l r | .or l r | .implies l r | .iff l r => l.isModalFree && r.isModalFree
  | .box _ | .diamond _ | .futureBox _ | .futureDiamond _ | .pastBox _
  | .pastDiamond _ | .since _ _ | .until _ _ | .knowledge _ _ | .belief _ _
  | .rankedBelief _ _ _ | .announce _ _ | .stit _ _ | .choiceDiamond _ _
  | .groupStit _ | .next _ | .ought _ _ | .permitted _ _ | .coalition _ _
  | .canNext _ _ | .canAlways _ _ | .canEventually _ _ | .canUntil _ _ _ => false

/-- The set of atoms occurring in a formula. -/
def atoms : Formula → Std.TreeSet Atom
  | .bot => ∅
  | .atomF a => (∅ : Std.TreeSet Atom).insert a
  | .not f | .box f | .diamond f | .futureBox f | .futureDiamond f
  | .pastBox f | .pastDiamond f | .knowledge _ f | .belief _ f
  | .rankedBelief _ _ f | .stit _ f | .choiceDiamond _ f | .groupStit f
  | .next f | .ought _ f | .permitted _ f | .coalition _ f | .canNext _ f
  | .canAlways _ f | .canEventually _ f => f.atoms
  | .and l r | .or l r | .implies l r | .iff l r | .since l r | .until l r
  | .announce l r | .canUntil _ l r => l.atoms.insertMany r.atoms

mutual
/-- Negation normal form: push ¬ inward through connectives and dual
operators. Operators without a dual in `Formula` keep an outer ¬.

Differs from the Haskell text in two places, with identical results:
`iff` is expanded inline rather than via `toNNF (Implies l r)`, and the
"no dual" cases of `pushNeg` build `¬(Op (toNNF f))` directly rather than
calling `toNNF (Op f)`. Both rewrites are needed because Lean must see
every recursive call on a strict subterm to accept the definition as
terminating; the Haskell calls were on terms of the same size. -/
def toNNF : Formula → Formula
  | .bot => .bot
  | .atomF a => .atomF a
  | .not f => pushNeg f
  | .and l r => .and (toNNF l) (toNNF r)
  | .or l r => .or (toNNF l) (toNNF r)
  | .implies l r => .or (pushNeg l) (toNNF r)
  | .iff l r => .and (.or (pushNeg l) (toNNF r)) (.or (pushNeg r) (toNNF l))
  | .box f => .box (toNNF f)
  | .diamond f => .diamond (toNNF f)
  | .futureBox f => .futureBox (toNNF f)
  | .futureDiamond f => .futureDiamond (toNNF f)
  | .pastBox f => .pastBox (toNNF f)
  | .pastDiamond f => .pastDiamond (toNNF f)
  | .since l r => .since (toNNF l) (toNNF r)
  | .until l r => .until (toNNF l) (toNNF r)
  | .knowledge a f => .knowledge a (toNNF f)
  | .belief a f => .belief a (toNNF f)
  | .rankedBelief a n f => .rankedBelief a n (toNNF f)
  | .announce b c => .announce (toNNF b) (toNNF c)
  | .stit a f => .stit a (toNNF f)
  | .choiceDiamond a f => .choiceDiamond a (toNNF f)
  | .groupStit f => .groupStit (toNNF f)
  | .next f => .next (toNNF f)
  | .ought a f => .ought a (toNNF f)
  | .permitted a f => .permitted a (toNNF f)
  | .coalition c f => .coalition c (toNNF f)
  | .canNext c f => .canNext c (toNNF f)
  | .canAlways c f => .canAlways c (toNNF f)
  | .canEventually c f => .canEventually c (toNNF f)
  | .canUntil c l r => .canUntil c (toNNF l) (toNNF r)

/-- `pushNeg f` is the NNF of `¬f`. -/
def pushNeg : Formula → Formula
  | .bot => .not .bot
  | .atomF a => .not (.atomF a)
  | .not f => toNNF f                                   -- ¬¬f = f
  | .and l r => .or (pushNeg l) (pushNeg r)             -- de Morgan
  | .or l r => .and (pushNeg l) (pushNeg r)
  | .implies l r => .and (toNNF l) (pushNeg r)          -- ¬(l→r) = l ∧ ¬r
  | .iff l r => .or (.and (toNNF l) (pushNeg r)) (.and (toNNF r) (pushNeg l))
  | .box f => .diamond (pushNeg f)
  | .diamond f => .box (pushNeg f)
  | .futureBox f => .futureDiamond (pushNeg f)
  | .futureDiamond f => .futureBox (pushNeg f)
  | .pastBox f => .pastDiamond (pushNeg f)
  | .pastDiamond f => .pastBox (pushNeg f)
  | .stit a f => .choiceDiamond a (pushNeg f)
  | .choiceDiamond a f => .stit a (pushNeg f)
  | .ought a f => .permitted a (pushNeg f)
  | .permitted a f => .ought a (pushNeg f)
  | .knowledge a f => .not (.knowledge a (toNNF f))
  | .belief a f => .not (.belief a (toNNF f))
  | .rankedBelief a n f => .not (.rankedBelief a n (toNNF f))
  | .announce b c => .not (.announce (toNNF b) (toNNF c))
  | .groupStit f => .not (.groupStit (toNNF f))
  | .next f => .not (.next (toNNF f))
  | .since l r => .not (.since (toNNF l) (toNNF r))
  | .until l r => .not (.until (toNNF l) (toNNF r))
  | .coalition c f => .not (.coalition c (toNNF f))
  | .canNext c f => .not (.canNext c (toNNF f))
  | .canAlways c f => .not (.canAlways c (toNNF f))
  | .canEventually c f => .not (.canEventually c (toNNF f))
  | .canUntil c l r => .not (.canUntil c (toNNF l) (toNNF r))
end

/-- Is the formula in negation normal form? -/
def isNNF : Formula → Bool
  | .bot | .atomF _ => true
  | .not .bot | .not (.atomF _) => true
  | .not (.knowledge _ f) | .not (.belief _ f) | .not (.rankedBelief _ _ f)
  | .not (.groupStit f) | .not (.next f) | .not (.coalition _ f)
  | .not (.canNext _ f) | .not (.canAlways _ f) | .not (.canEventually _ f) => f.isNNF
  | .not (.announce a b) | .not (.since a b) | .not (.until a b)
  | .not (.canUntil _ a b) => a.isNNF && b.isNNF
  | .not _ => false
  | .and l r | .or l r => l.isNNF && r.isNNF
  | .implies _ _ | .iff _ _ => false
  | .box f | .diamond f | .futureBox f | .futureDiamond f | .pastBox f
  | .pastDiamond f | .knowledge _ f | .belief _ f | .rankedBelief _ _ f
  | .stit _ f | .choiceDiamond _ f | .groupStit f | .next f | .ought _ f
  | .permitted _ f | .coalition _ f | .canNext _ f | .canAlways _ f
  | .canEventually _ f => f.isNNF
  | .since l r | .until l r | .announce l r | .canUntil _ l r => l.isNNF && r.isNNF

end Formula
end Gamen
