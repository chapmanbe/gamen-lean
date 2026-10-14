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
    valid? (movie 2) (.announce 3 p (.evidence 0 3 p)) == some false)]

def cases : List (String × Bool) := constructorCases ++ movieCases

end EvidenceTrustTests
