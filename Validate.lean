import Validate.Core

/-!
# gamen-validate (Lean port)

Port of `gamen-hs/validate/Main.hs`: a JSON Lines service on stdin/stdout.

    {"action": "ping"}
    {"action": "check_consistency", "formulas": [...]}
    {"action": "validate_formula", "formula": {...}}
    {"action": "validate_agent", "formula": {...}, "agent": "clinician"}
    {"action": "check_pairwise", "formulas": [...]}

Responses are `{"ok": true, "result": ...}` or `{"ok": false, "error": "..."}`.

**Backends.** gamen-hs dispatches consistency checks to two backends:
the KDt tableau with its doxastic-D and ranking-theory rules (for
`belief`/`ranked_belief`), and the deontic-STIT prover G3DS (for agent
operators). Both are ported. Fragment rejections ("unsupported operator …")
happen before dispatch and are fully ported. The one Lean-only reply,
`"prover error: …"`, is unreachable (see `classifyConsistency`).

There is no `deepseq` crash guard: the Lean code has no `error` calls to
guard against, and evaluation is strict.

The non-`IO` request/response logic lives in `Validate.Core`, so it can be
`import`ed from `Tests.Main` without this file's `main` and `Tests.Main`'s
`main` colliding.
-/

/-- Read JSON Lines until EOF; skip empty lines, as `BL.null` does in Haskell. -/
partial def main : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  let rec loop : IO Unit := do
    let line ← stdin.getLine
    if line.isEmpty then return  -- EOF
    let body := if line.endsWith "\n" then line.dropEnd 1 |>.toString else line
    unless body.isEmpty do
      stdout.putStrLn (processLine body).compress
      stdout.flush
    loop
  loop
