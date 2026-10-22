import Gamen.Input
import Plausible

/-!
# `Gamen.Input` (text parser for the epistemic fragment of the dynamic explorer)

Unicode and ASCII spellings must agree; precedence and associativity are
checked on small cases; the round trip `parseFormula f.toString = .ok f` is a
Plausible property over the supported fragment (`DynamicInputTests.EpiFormula`,
registered in `Tests/Main.lean`).
-/

namespace DynamicInputTests

open Gamen Plausible

/-- `Except` has no `BEq` in core; compare successes by value and failures by message. -/
instance {ε α : Type} [BEq ε] [BEq α] : BEq (Except ε α) where
  beq
    | .ok a, .ok b => a == b
    | .error a, .error b => a == b
    | _, _ => false

def isError {α : Type} (r : Except String α) : Bool :=
  match r with | .error _ => true | .ok _ => false

def tokens (s : String) : Option (List Input.Token) :=
  (Input.tokenize s).toOption.map (·.map (·.1))

def cases : List (String × Bool) := [
  ("parse atom", parseFormula "p" == .ok (.atom "p")),
  ("parse K", parseFormula "K[D] p" == .ok (.knowledge "D" (.atom "p"))),
  ("parse nested K", parseFormula "K[N] K[D] p" == .ok (.knowledge "N" (.knowledge "D" (.atom "p")))),
  ("ascii = unicode", parseFormula "K[D]p & ~K[N]K[D]p" == parseFormula "K[D]p ∧ ¬K[N]K[D]p"),
  ("∧ binds tighter than ∨", parseFormula "p ∨ q ∧ r" == .ok (.or (.atom "p") (.and (.atom "q") (.atom "r")))),
  ("→ is right-assoc", parseFormula "p → q → r" == .ok (.implies (.atom "p") (.implies (.atom "q") (.atom "r")))),
  ("announcement", parseFormula "[p]K[D]p" == .ok (.announce (.atom "p") (.knowledge "D" (.atom "p")))),
  ("empty is an error", isError (parseFormula "")),
  ("unbalanced is an error", isError (parseFormula "(p ∧ q")),
  ("K without agent is an error", isError (parseFormula "K[] p")),
  ("temporal rejected", isError (parseFormula "G p")),
  ("error names a position", match parseFormula "p ∧" with | .error e => e.startsWith "position" | _ => false),
  ("rejected operator says so", match parseFormula "G p" with
    | .error e => (e.splitOn "not available in this explorer").length == 2 | _ => false),
  ("↔ is looser than →", parseFormula "p → q ↔ r" == .ok (.iff (.implies (.atom "p") (.atom "q")) (.atom "r"))),
  ("ascii <-> and ->", parseFormula "p -> q <-> r" == parseFormula "p → q ↔ r"),
  ("⊥ and false", parseFormula "⊥" == .ok .bot && parseFormula "false" == .ok .bot),
  ("⊤ and true read as ¬⊥", parseFormula "⊤" == .ok (.not .bot) && parseFormula "true" == .ok (.not .bot)),
  ("box and diamond, both spellings",
    parseFormula "[]<>p" == parseFormula "□◇p" && parseFormula "□◇p" == .ok (.box (.diamond (.atom "p")))),
  ("prefix binds tighter than ∧", parseFormula "¬p ∧ q" == .ok (.and (.not (.atom "p")) (.atom "q"))),
  ("parentheses override precedence", parseFormula "(p ∨ q) ∧ r" == .ok (.and (.or (.atom "p") (.atom "q")) (.atom "r"))),
  ("multi-letter atoms", parseFormula "foo_1 ∧ bar" == .ok (.and (.atom "foo_1") (.atom "bar"))),
  ("agent of any case", parseFormula "K[alice] p" == .ok (.knowledge "alice" (.atom "p"))),
  ("trailing tokens are an error", isError (parseFormula "p q")),
  ("stray character is an error", isError (parseFormula "p # q")),
  ("tokenize: Task 2 symbols, ASCII",
    tokens "<<a,b>> { } : + - ( ) [ ]" ==
      some [.langle, .ident "a", .comma, .ident "b", .rangle, .lbrace, .rbrace, .colon, .plus, .minus,
            .lparen, .rparen, .lbrack, .rbrack]),
  ("tokenize: ⟨⟨ ⟩⟩ equal << >>", tokens "⟨⟨a⟩⟩" == tokens "<<a>>"),
  ("tokenize: positions", (Input.tokenize "p ∧ q").toOption.map (·.map (·.2)) == some [0, 2, 4]),
  ("tokenize: -> is one token, - alone is minus",
    tokens "a->b" == some [.ident "a", .imp, .ident "b"] && tokens "a-" == some [.ident "a", .minus])
]

/-! ## Round-trip property -/

/-- Formulas in the supported fragment: ⊥, atoms, ¬ ∧ ∨ → ↔, □ ◇, `K[a]`, `[φ]ψ`. -/
partial def genEpi : Nat → Gen Formula
  | 0 => Gen.frequency (pure .bot) [(1, pure .bot), (4, genAtom)]
  | n + 1 =>
    let h := (n + 1) / 2
    Gen.frequency (pure .bot) [
      (1, pure .bot), (4, genAtom),
      (3, .not <$> genEpi n),
      (3, .and <$> genEpi h <*> genEpi h),
      (2, .or <$> genEpi h <*> genEpi h),
      (2, .implies <$> genEpi h <*> genEpi h),
      (1, .iff <$> genEpi h <*> genEpi h),
      (2, .box <$> genEpi n),
      (2, .diamond <$> genEpi n),
      (3, .knowledge <$> genAgent <*> genEpi n),
      (2, .announce <$> genEpi h <*> genEpi h)]
where
  genAtom : Gen Formula := do
    let ⟨i, _⟩ ← Gen.choose Nat 0 2 (by omega)
    return .atom (["p", "q", "r"].getD i "p")
  genAgent : Gen String := do
    let ⟨i, _⟩ ← Gen.choose Nat 0 3 (by omega)
    return (["D", "N", "alice", "B2"].getD i "D")

structure EpiFormula where
  getFormula : Formula
  deriving Repr

instance : Arbitrary EpiFormula := ⟨EpiFormula.mk <$> Gen.sized fun n => genEpi (min n 12)⟩
instance : Shrinkable EpiFormula where shrink _ := []

def roundTrips (f : Formula) : Bool := parseFormula f.toString == .ok f

end DynamicInputTests
