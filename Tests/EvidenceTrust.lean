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
      && errStarts ({ base with T := #[#[(3, 1), (3, 1)], #[(0, 1), (0, 1)]] }.validate) "bad_type")]




def cases : List (String × Bool) := constructorCases

end EvidenceTrustTests
