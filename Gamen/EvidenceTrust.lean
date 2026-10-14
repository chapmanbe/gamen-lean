/-!
# Gamen.EvidenceTrust

DL-BET: the dynamic logic of belief, evidence and trust of Liu & Lorini, *Reasoning About
Belief, Evidence and Trust in a Multi-agent Setting*, PRIMA 2017. Lean-only. Issue #3, item 4.
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

end EvidenceTrust
end Gamen
