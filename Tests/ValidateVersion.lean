import Validate.BuildInfo

/-!
# The Lean-only `version` action (`Validate/Core.lean`)

Plan: `plans/downstream-migration-2026-09-29.md`, Phase 0a. `version` is a
protocol extension outside `compare.py`'s scope, so its contract is pinned
here: the exact reply, `ping` unchanged, unknown actions still errors, and
the commit stamp (`Validate/BuildInfo.lean`): its format, its `-dirty` rule,
and that the served reply carries it. `tools/install.sh` checks the built
binary's stamp against `HEAD`.
-/

namespace ValidateVersionTests

open Lean (Json)

def cases : List (String × Bool) := [
  ("version: reply names gamen-lean, the commit, and protocol 4 (exact bytes)",
    (processLine "{\"action\":\"version\"}" "abc123").compress
      == "{\"ok\":true,\"result\":{\"commit\":\"abc123\",\"implementation\":\"gamen-lean\",\"protocol\":4}}"),
  ("version: extra fields are ignored, as for ping",
    (processLine "{\"action\":\"version\",\"extra\":1}" "abc123").compress
      == (processLine "{\"action\":\"version\"}" "abc123").compress),
  ("version: the commit defaults to unknown",
    ((processLine "{\"action\":\"version\"}").compress.splitOn "\"commit\":\"unknown\"").length == 2),
  ("version: the protocol number is Gamen.Protocol.protocolVersion = 4",
    Gamen.Protocol.protocolVersion == 4),
  ("ping is unchanged by the version action (gamen-hs's exact reply)",
    (processLine "{\"action\":\"ping\"}" "abc123").compress == "{\"ok\":true,\"result\":\"pong\"}"),
  ("an unknown action is still an error",
    (processLine "{\"action\":\"versions\"}" "abc123").compress
      == "{\"error\":\"Unknown action: versions\",\"ok\":false}"),
  ("stampOf: clean, dirty, git status failed, no revision",
    stampOf (some "0123456789ab") (some "") == "0123456789ab"
      && stampOf (some "0123456789ab") (some " M Validate.lean") == "0123456789ab-dirty"
      && stampOf (some "0123456789ab") none == "0123456789ab"
      && stampOf none (some "") == "unknown"),
  ("buildCommit is a 12-digit hex revision, optionally -dirty (tests run in a git checkout)",
    let rev := (buildCommit.splitOn "-dirty").headD ""
    rev.length == 12 && rev.all (fun c => c.isDigit || ('a' ≤ c && c ≤ 'f'))
      && (buildCommit == rev || buildCommit == rev ++ "-dirty")),
  ("serveLine answers version with buildCommit, and ping as processLine does",
    (serveLine "{\"action\":\"version\"}").compress
        == (processLine "{\"action\":\"version\"}" buildCommit).compress
      && (((serveLine "{\"action\":\"version\"}").compress.splitOn
          s!"\"commit\":\"{buildCommit}\"").length == 2)
      && (serveLine "{\"action\":\"ping\"}").compress == "{\"ok\":true,\"result\":\"pong\"}") ]

end ValidateVersionTests
