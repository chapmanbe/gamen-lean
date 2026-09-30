import Validate.Core

/-!
# The Lean-only `version` action (`Validate/Core.lean`)

Plan: `plans/downstream-migration-2026-09-29.md`, Phase 0a. `version` is a
protocol extension outside `compare.py`'s scope, so its contract is pinned
here: the exact reply, `ping` unchanged, and unknown actions still errors.
-/

namespace ValidateVersionTests

open Lean (Json)

def cases : List (String × Bool) := [
  ("version: reply names gamen-lean, the commit, and protocol 1 (exact bytes)",
    (processLine "{\"action\":\"version\"}" "abc123").compress
      == "{\"ok\":true,\"result\":{\"commit\":\"abc123\",\"implementation\":\"gamen-lean\",\"protocol\":1}}"),
  ("version: extra fields are ignored, as for ping",
    (processLine "{\"action\":\"version\",\"extra\":1}" "abc123").compress
      == (processLine "{\"action\":\"version\"}" "abc123").compress),
  ("version: the commit defaults to unknown",
    ((processLine "{\"action\":\"version\"}").compress.splitOn "\"commit\":\"unknown\"").length == 2),
  ("version: the protocol number is Gamen.Protocol.protocolVersion = 1",
    Gamen.Protocol.protocolVersion == 1),
  ("ping is unchanged by the version action (gamen-hs's exact reply)",
    (processLine "{\"action\":\"ping\"}" "abc123").compress == "{\"ok\":true,\"result\":\"pong\"}"),
  ("an unknown action is still an error",
    (processLine "{\"action\":\"versions\"}" "abc123").compress
      == "{\"error\":\"Unknown action: versions\",\"ok\":false}") ]

end ValidateVersionTests
