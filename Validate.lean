import Validate.Core
import Lean.Elab.Term

/-!
# gamen-validate (Lean port)

Port of `gamen-hs/validate/Main.hs`: a JSON Lines service on stdin/stdout.

    {"action": "ping"}
    {"action": "version"}                       (Lean-only; see below)
    {"action": "check_consistency", "formulas": [...]}
    {"action": "validate_formula", "formula": {...}}
    {"action": "validate_agent", "formula": {...}, "agent": "clinician"}
    {"action": "check_pairwise", "formulas": [...]}

Responses are `{"ok": true, "result": ...}` or `{"ok": false, "error": "..."}`.

**`version` (Lean-only, protocol 1).** Answers
`{"ok":true,"result":{"commit":"<rev>","implementation":"gamen-lean","protocol":1}}`
(keys in the order Lean's `Json.compress` writes them), so a caller can
check which binary answered: both implementations answer `ping` with the
same `"pong"`, and gamen-hs answers `version` with
`{"error":"Error in $: Unknown action: version","ok":false}` (checked
against gamen-hs's binary, 2026-09-30). The other five actions
are unchanged. Plan: `plans/downstream-migration-2026-09-29.md`, Phase 0a.

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

open Lean Elab Term in
/-- The git commit this file was compiled at: `git rev-parse --short=12
HEAD`, with `-dirty` if tracked files had uncommitted changes, or
`unknown` if git isn't available. Evaluated at compile time.

Lake recompiles this file whenever `gamen-validate`'s sources change, so a
new commit that changes none of them keeps the old stamp, which still
names a commit with the same code (though a `-dirty` stamp may outlive
the commit that cleaned it). `tools/install.sh` forces a recompile, so an
installed binary's stamp is current. -/
elab "build_commit%" : term => do
  let git (args : Array String) : IO (Option String) := do
    try
      let out ← IO.Process.output { cmd := "git", args }
      return if out.exitCode == 0 then some out.stdout.trimAscii.toString else none
    catch _ => return none
  let stamp := match ← git #["rev-parse", "--short=12", "HEAD"],
      ← git #["status", "--porcelain", "--untracked-files=no"] with
    | some rev, some changes => if changes.isEmpty then rev else rev ++ "-dirty"
    | some rev, none => rev
    | none, _ => "unknown"
  return mkStrLit stamp

/-- The commit `version` reports. -/
def buildCommit : String := build_commit%

/-- Read JSON Lines until EOF; skip empty lines, as `BL.null` does in Haskell. -/
partial def main : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  let rec loop : IO Unit := do
    let line ← stdin.getLine
    if line.isEmpty then return  -- EOF
    let body := if line.endsWith "\n" then line.dropEnd 1 |>.toString else line
    unless body.isEmpty do
      stdout.putStrLn (processLine body buildCommit).compress
      stdout.flush
    loop
  loop
