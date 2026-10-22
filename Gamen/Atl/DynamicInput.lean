import Gamen.Atl.Dynamic
import Gamen.Input

/-!
# Gamen.Atl.DynamicInput

Text input for ATL-D formulas (`DFormula`), and a printer that the parser reads
back: `parseDFormula f.toInput = .ok f`.

`DFormula.toString` prints `K_{a}φ`, which is ambiguous for multi-letter agents
(`K_Dp`), so the student syntax is `K[a]φ`. Grammar (Unicode and ASCII both
accepted; the token level is `Gamen.Input.tokenize`):

* atoms `[a-z][A-Za-z0-9_]*`; `⊥`/`false`; `⊤`/`true` (`DFormula` has no `top`,
  so `⊤` is read as `¬⊥`; the printer never emits `⊤`)
* `has(agent,action)`; `K[a] φ`
* coalitions `⟨⟨A⟩⟩` / `<<A>>` (`A` a comma-separated list, possibly empty)
  followed by `X φ`, `G φ`, `F φ`, `(φ U ψ)` or `(φ R ψ)`
* updates `[φ:α→{A}, ψ:β→{B},{C}]+χ` (grant) and `]-χ` (revoke); `{C}`, the
  informed set, is optional. The empty update list is not accepted.
* prefix `¬`/`~`; binary `∧ ∨ → ↔` as in `Gamen.Input` (right-associative).

Anything else (e.g. `□`) is rejected. Errors read `position N: ...`. Recursion is
on explicit fuel; no `partial def`.
-/

namespace Gamen.Atl.Dynamic

open Gamen.Input

private abbrev Toks := List (Token × Nat)

private def unexpected (endPos : Nat) (what : String) : Toks → String
  | [] => s!"position {endPos}: expected {what}, found end of input"
  | (t, p) :: _ => s!"position {p}: expected {what}, found {t.describe}"

private def expect (endPos : Nat) (t : Token) (what : String) (ts : Toks) : Except String Toks :=
  match ts with
  | (t', _) :: rest => if t' == t then .ok rest else .error (unexpected endPos what ts)
  | [] => .error (unexpected endPos what ts)

private def expectIdent (endPos : Nat) (what : String) : Toks → Except String (String × Toks)
  | (.ident a, _) :: rest => .ok (a, rest)
  | ts => .error (unexpected endPos what ts)

/-- One or more comma-separated identifiers. -/
private def identList (endPos : Nat) : Nat → Toks → Except String (List String × Toks)
  | 0, _ => .error "internal error: parser ran out of fuel"
  | fuel + 1, ts => do
    let (a, rest) ← expectIdent endPos "an agent name" ts
    match rest with
    | (.comma, _) :: rest' =>
      let (as, r) ← identList endPos fuel rest'
      pure (a :: as, r)
    | _ => pure ([a], rest)

/-- Zero or more identifiers, up to (not including) the closing token `close`. -/
private def identsUntil (endPos : Nat) (fuel : Nat) (close : Token) (ts : Toks) :
    Except String (List String × Toks) :=
  match ts with
  | (t, _) :: _ => if t == close then .ok ([], ts) else identList endPos fuel ts
  | [] => identList endPos fuel ts

/-- `{a,b}`, possibly empty. -/
private def braceSet (endPos fuel : Nat) (ts : Toks) : Except String (List String × Toks) := do
  let ts ← expect endPos .lbrace "'{'" ts
  let (as, ts) ← identsUntil endPos fuel .rbrace ts
  let ts ← expect endPos .rbrace "'}'" ts
  pure (as, ts)

private def binOp : Nat → Option (Token × (DFormula → DFormula → DFormula))
  | 0 => some (.iff, .iff)
  | 1 => some (.imp, .implies)
  | 2 => some (.or, .or)
  | 3 => some (.and, .and)
  | _ => none

mutual
/-- Precedence climbing, levels 0-3 binary and 4 prefix/atoms, as in `Gamen.Input`.
`fuel` bounds the recursion depth; the caller passes `8 * (tokens + 2)`, which
every nesting stays under (each level consumes a token and costs at most eight). -/
private def go (endPos : Nat) : Nat → Nat → Toks → Except String (DFormula × Toks)
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
        | .lparen => do
          let (f, r) ← go endPos fuel 0 rest
          let r ← expect endPos .rparen "')'" r
          pure (f, r)
        | .langle => do
          let (as, r) ← identsUntil endPos fuel .rangle rest
          let r ← expect endPos .rangle "'⟩⟩' closing the coalition" r
          match r with
          | (.ident "X", _) :: r' => do let (f, r) ← go endPos fuel 4 r'; pure (.canNext as f, r)
          | (.ident "G", _) :: r' => do let (f, r) ← go endPos fuel 4 r'; pure (.canAlways as f, r)
          | (.ident "F", _) :: r' => do let (f, r) ← go endPos fuel 4 r'; pure (.canEventually as f, r)
          | (.lparen, _) :: r' => do
            let (l, r) ← go endPos fuel 0 r'
            match r with
            | (.ident "U", _) :: r'' => do
              let (rt, r) ← go endPos fuel 0 r''
              let r ← expect endPos .rparen "')'" r
              pure (.canUntil as l rt, r)
            | (.ident "R", _) :: r'' => do
              let (rt, r) ← go endPos fuel 0 r''
              let r ← expect endPos .rparen "')'" r
              pure (.canRelease as l rt, r)
            | _ => .error (unexpected endPos "'U' or 'R'" r)
          | _ => .error (unexpected endPos "X, G, F or '(' after the coalition" r)
        | .lbrack => do
          let (us, r) ← updates endPos fuel rest
          let r ← expect endPos .rbrack "']' closing the update list" r
          match r with
          | (.plus, _) :: r' => do let (f, r) ← go endPos fuel 4 r'; pure (.grant us f, r)
          | (.minus, _) :: r' => do let (f, r) ← go endPos fuel 4 r'; pure (.revoke us f, r)
          | _ => .error (unexpected endPos "'+' or '-' after the update list" r)
        | .ident "K" =>
          match rest with
          | (.lbrack, _) :: (.ident a, _) :: (.rbrack, _) :: r => do
            let (f, r) ← go endPos fuel 4 r
            pure (.knows a f, r)
          | (.lbrack, _) :: r => .error (unexpected endPos "an agent name" r)
          | _ => .error (unexpected endPos "'[' and an agent after K" rest)
        | .ident "has" =>
          match rest with
          | (.lparen, _) :: r => do
            let (a, r) ← expectIdent endPos "an agent name" r
            let r ← expect endPos .comma "','" r
            let (α, r) ← expectIdent endPos "an action name" r
            let r ← expect endPos .rparen "')'" r
            pure (.has a α, r)
          | _ => pure (.atom "has", rest)
        | .ident n =>
          match n.toList with
          | c :: _ =>
            if c.isLower then pure (.atom n, rest)
            else .error s!"position {p}: '{n}' is not available in this explorer (atoms start with a lowercase letter)"
          | [] => .error s!"position {p}: empty identifier"
        | _ => .error s!"position {p}: expected a formula, found {t.describe}"

/-- `φ:α→{A}[,{B}]` clauses separated by commas. -/
private def updates (endPos : Nat) : Nat → Toks → Except String (UpdateList × Toks)
  | 0, _ => .error "internal error: parser ran out of fuel"
  | fuel + 1, ts => do
    let (c, r) ← go endPos fuel 0 ts
    let r ← expect endPos .colon "':' after the condition" r
    let (α, r) ← expectIdent endPos "an action name" r
    let r ← expect endPos .imp "'→'" r
    let (as, r) ← braceSet endPos fuel r
    let (bs, r) ← match r with
      | (.comma, _) :: (.lbrace, _) :: _ => braceSet endPos fuel r.tail
      | _ => pure ([], r)
    match r with
    | (.comma, _) :: r' => do
      let (rest, r'') ← updates endPos fuel r'
      pure (.cons c α as bs rest, r'')
    | _ => pure (.cons c α as bs .nil, r)
end

/-- Parse an ATL-D formula from text (see the module docstring). -/
def parseDFormula (s : String) : Except String DFormula := do
  let ts ← tokenize s
  let (f, rest) ← go s.length (8 * (ts.length + 2)) 0 ts
  match rest with
  | [] => pure f
  | (t, p) :: _ => .error s!"position {p}: expected an operator or end of input, found {t.describe}"

namespace DFormula

private def informedStr (bs : List String) : String :=
  if bs.isEmpty then "" else ",{" ++ ",".intercalate bs ++ "}"

mutual
/-- Print in the student syntax; `parseDFormula f.toInput = .ok f` for every `f`
whose update lists are non-empty and whose names are identifiers (atoms start
lowercase, none is `has`, `false` or `true`). -/
def toInput : DFormula → String
  | .bot => "⊥"
  | .atom n => n
  | .not f => "¬" ++ f.toInput
  | .and l r => "(" ++ l.toInput ++ " ∧ " ++ r.toInput ++ ")"
  | .or l r => "(" ++ l.toInput ++ " ∨ " ++ r.toInput ++ ")"
  | .implies l r => "(" ++ l.toInput ++ " → " ++ r.toInput ++ ")"
  | .iff l r => "(" ++ l.toInput ++ " ↔ " ++ r.toInput ++ ")"
  | .has a α => s!"has({a},{α})"
  | .knows a f => s!"K[{a}]" ++ f.toInput
  | .canNext as f => s!"⟨⟨{",".intercalate as}⟩⟩X " ++ f.toInput
  | .canAlways as f => s!"⟨⟨{",".intercalate as}⟩⟩G " ++ f.toInput
  | .canEventually as f => s!"⟨⟨{",".intercalate as}⟩⟩F " ++ f.toInput
  | .canUntil as l r => s!"⟨⟨{",".intercalate as}⟩⟩(" ++ l.toInput ++ " U " ++ r.toInput ++ ")"
  | .canRelease as l r => s!"⟨⟨{",".intercalate as}⟩⟩(" ++ l.toInput ++ " R " ++ r.toInput ++ ")"
  | .grant us f => "[" ++ updatesToInput us ++ "]+" ++ f.toInput
  | .revoke us f => "[" ++ updatesToInput us ++ "]-" ++ f.toInput

def updatesToInput : UpdateList → String
  | .nil => ""
  | .cons c α as bs .nil =>
      c.toInput ++ ":" ++ α ++ "→{" ++ ",".intercalate as ++ "}" ++ informedStr bs
  | .cons c α as bs rest =>
      c.toInput ++ ":" ++ α ++ "→{" ++ ",".intercalate as ++ "}" ++ informedStr bs ++ ", "
        ++ updatesToInput rest
end

end DFormula
end Gamen.Atl.Dynamic
