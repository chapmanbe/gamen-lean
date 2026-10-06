import DclegService.BuildInfo

/-!
# dcleg-service (Lean port)

Port of `gamen-hs/service/Main.hs`: a stateful JSON Lines service for DCLEG
model evaluation (`notes/dcleg-service-protocol.md` in gamen-hs).

    Request:  {"id": "<string>", "op": "<op>", ...args}
    Response: {"id": "<echoed>", "ok": true,  "result": ...}
              {"id": "<echoed>", "ok": false, "error": {"code": ..., "message": ...}}

Operations, the registry and every handler are in `DclegService.Core`; this
file is the loop. One reply line per non-empty input line, flushed at once;
an empty line gets no reply; the loop ends at end of input.
-/
open DclegService

/-- Read JSON Lines until EOF, keeping the registry in an `IO.Ref`. `partial`
because it loops until end of input, as `gamen-validate`'s `main` does. -/
partial def main : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  let state ← IO.mkRef ({} : ServiceState)
  let rec loop : IO Unit := do
    let line ← stdin.getLine
    if line.isEmpty then return  -- EOF
    let body := if line.endsWith "\n" then line.dropEnd 1 |>.toString else line
    let (st, out) := processLine dclegBuildCommit (← state.get) body
    state.set st
    if let some j := out then
      stdout.putStrLn (Gamen.Service.encode j)
      stdout.flush
    loop
  loop
