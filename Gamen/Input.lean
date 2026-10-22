import Gamen.Formula

/-!
# Gamen.Input

Text input for the dynamic-scenarios explorer: a tokenizer shared by every
formula parser there, and a parser for the epistemic fragment of `Formula`.

Grammar (Unicode and ASCII spellings both accepted):

* atoms `[a-z][A-Za-z0-9_]*`; `⊥`/`false`; `⊤`/`true` (read as `¬⊥`)
* prefix: `¬`/`~`, `□`/`[]`, `◇`/`<>`, `K[a] φ` (agent: any identifier),
  announcement `[φ] ψ`
* binary, tightest first: `∧`/`&`, `∨`/`|`, `→`/`->`, `↔`/`<->`. All binary
  operators associate to the right; `p → q → r` is `p → (q → r)`.
* parentheses.

Anything else (e.g. `G`, `U`) is rejected with "not available in this
explorer". Errors read `position N: <what was expected>`, `N` a 0-based
character index. No `partial def`: recursion is on explicit fuel.
-/

namespace Gamen.Input

/-- Lexical tokens, shared by the epistemic parser and the ATL-D parser. -/
inductive Token where
  | ident (name : String)
  | bot | top
  | neg | and | or | imp | iff
  | box | dia
  | langle   -- `⟨⟨` or `<<`
  | rangle   -- `⟩⟩` or `>>`
  | lbrace | rbrace | comma | colon | plus | minus
  | lparen | rparen | lbrack | rbrack
  deriving BEq, Repr, Inhabited

def Token.describe : Token → String
  | .ident n => s!"'{n}'"
  | .bot => "'⊥'" | .top => "'⊤'"
  | .neg => "'¬'" | .and => "'∧'" | .or => "'∨'" | .imp => "'→'" | .iff => "'↔'"
  | .box => "'□'" | .dia => "'◇'"
  | .langle => "'⟨⟨'" | .rangle => "'⟩⟩'"
  | .lbrace => "'{'" | .rbrace => "'}'" | .comma => "','" | .colon => "':'"
  | .plus => "'+'" | .minus => "'-'"
  | .lparen => "'('" | .rparen => "')'" | .lbrack => "'['" | .rbrack => "']'"

private def isIdentStart (c : Char) : Bool := c.isAlpha
private def isIdentChar (c : Char) : Bool := c.isAlphanum || c == '_'

/-- Scan with `fuel` (the input length plus one; every step consumes a character). -/
private def scan : Nat → Nat → List Char → List (Token × Nat) → Except String (List (Token × Nat))
  | 0, _, _, _ => .error "internal error: tokenizer ran out of fuel"
  | _ + 1, _, [], acc => .ok acc.reverse
  | fuel + 1, pos, c :: cs, acc =>
    let emit (t : Token) (n : Nat) (rest : List Char) :=
      scan fuel (pos + n) rest ((t, pos) :: acc)
    if c.isWhitespace then scan fuel (pos + 1) cs acc
    else if isIdentStart c then
      let name := c :: cs.takeWhile isIdentChar
      let word := String.ofList name
      let t := match word with
        | "false" => Token.bot
        | "true" => Token.top
        | _ => Token.ident word
      emit t name.length (cs.dropWhile isIdentChar)
    else match c, cs with
      | '⊥', _ => emit .bot 1 cs
      | '⊤', _ => emit .top 1 cs
      | '¬', _ | '~', _ => emit .neg 1 cs
      | '∧', _ | '&', _ => emit .and 1 cs
      | '∨', _ | '|', _ => emit .or 1 cs
      | '→', _ => emit .imp 1 cs
      | '↔', _ => emit .iff 1 cs
      | '□', _ => emit .box 1 cs
      | '◇', _ => emit .dia 1 cs
      | '-', '>' :: r => emit .imp 2 r
      | '-', _ => emit .minus 1 cs
      | '<', '-' :: '>' :: r => emit .iff 3 r
      | '<', '>' :: r => emit .dia 2 r
      | '<', '<' :: r => emit .langle 2 r
      | '>', '>' :: r => emit .rangle 2 r
      | '⟨', '⟨' :: r => emit .langle 2 r
      | '⟩', '⟩' :: r => emit .rangle 2 r
      | '[', ']' :: r => emit .box 2 r
      | '{', _ => emit .lbrace 1 cs
      | '}', _ => emit .rbrace 1 cs
      | ',', _ => emit .comma 1 cs
      | ':', _ => emit .colon 1 cs
      | '+', _ => emit .plus 1 cs
      | '(', _ => emit .lparen 1 cs
      | ')', _ => emit .rparen 1 cs
      | '[', _ => emit .lbrack 1 cs
      | ']', _ => emit .rbrack 1 cs
      | _, _ => .error s!"position {pos}: unexpected character '{c}'"

/-- Split `s` into tokens, each with the 0-based character index where it starts. -/
def tokenize (s : String) : Except String (List (Token × Nat)) :=
  let cs := s.toList
  scan (cs.length + 1) 0 cs []

private abbrev Toks := List (Token × Nat)

private def unexpected (endPos : Nat) (what : String) : Toks → String
  | [] => s!"position {endPos}: expected {what}, found end of input"
  | (t, p) :: _ => s!"position {p}: expected {what}, found {t.describe}"

private def expect (endPos : Nat) (t : Token) (what : String) (ts : Toks) : Except String Toks :=
  match ts with
  | (t', _) :: rest => if t' == t then .ok rest else .error (unexpected endPos what ts)
  | [] => .error (unexpected endPos what ts)

/-- Operator at precedence level `k` (0 `↔`, 1 `→`, 2 `∨`, 3 `∧`), with its constructor. -/
private def binOp : Nat → Option (Token × (Formula → Formula → Formula))
  | 0 => some (.iff, .iff)
  | 1 => some (.imp, .implies)
  | 2 => some (.or, .or)
  | 3 => some (.and, .and)
  | _ => none

/-- Precedence climbing. Levels 0-3 are the binary operators, 4 is prefix/atoms.
`fuel` bounds the recursion depth; the caller passes `5 * (tokens + 2)`, which
every nesting of operators and parentheses stays under, since each nesting
level consumes a token and costs at most five fuel. -/
private def go (endPos : Nat) : Nat → Nat → Toks → Except String (Formula × Toks)
  | 0, _, _ => .error "internal error: parser ran out of fuel"
  | fuel + 1, level, ts =>
    if level < 4 then do
      let (l, rest) ← go endPos fuel (level + 1) ts
      match binOp level, rest with
      | some (tok, mk), (t, _) :: rest' =>
        if t == tok then do
          let (r, rest'') ← go endPos fuel level rest'
          pure (mk l r, rest'')
        else pure (l, rest)
      | _, _ => pure (l, rest)
    else match ts with
      | [] => .error (unexpected endPos "a formula" ts)
      | (t, p) :: rest =>
        match t with
        | .bot => pure (.bot, rest)
        | .top => pure (.not .bot, rest)
        | .neg => do let (f, r) ← go endPos fuel 4 rest; pure (.not f, r)
        | .box => do let (f, r) ← go endPos fuel 4 rest; pure (.box f, r)
        | .dia => do let (f, r) ← go endPos fuel 4 rest; pure (.diamond f, r)
        | .lparen => do
          let (f, r) ← go endPos fuel 0 rest
          let r ← expect endPos .rparen "')'" r
          pure (f, r)
        | .lbrack => do
          let (b, r) ← go endPos fuel 0 rest
          let r ← expect endPos .rbrack "']' closing the announcement" r
          let (c, r) ← go endPos fuel 4 r
          pure (.announce b c, r)
        | .ident "K" =>
          match rest with
          | (.lbrack, _) :: (.ident a, _) :: (.rbrack, _) :: r => do
            let (f, r) ← go endPos fuel 4 r
            pure (.knowledge a f, r)
          | (.lbrack, _) :: r => .error (unexpected endPos "an agent name" r)
          | _ => .error (unexpected endPos "'[' and an agent after K" rest)
        | .ident n =>
          match n.toList with
          | c :: _ =>
            if c.isLower then pure (.atom n, rest)
            else .error s!"position {p}: '{n}' is not available in this explorer (atoms start with a lowercase letter)"
          | [] => .error s!"position {p}: empty identifier"
        | _ => .error s!"position {p}: expected a formula, found {t.describe}"

end Gamen.Input

open Gamen.Input in
/-- Parse the epistemic fragment of `Formula` from text (see `Gamen.Input`). -/
def Gamen.parseFormula (s : String) : Except String Formula := do
  let ts ← tokenize s
  let (f, rest) ← go s.length (5 * (ts.length + 2)) 0 ts
  match rest with
  | [] => pure f
  | (t, p) :: _ => .error s!"position {p}: expected an operator or end of input, found {t.describe}"
