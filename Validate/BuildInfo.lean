import Validate.Core
import Validate.Stamp

/-!
# Validate.BuildInfo

The git commit `gamen-validate`'s `version` action reports (plan:
`plans/downstream-migration-2026-09-29.md`, Phase 0a), stamped in when this
file is compiled. Kept out of `Validate.lean` so the tests can import it.
The `build_commit%` term itself lives in `Validate/Stamp.lean`, shared with
`dcleg-service`.

**When the stamp can be stale.** Lake recompiles this file only when it or
something it imports changes. A later commit that touches none of
`gamen-validate`'s sources keeps the earlier stamp, which then names a commit
with the same `gamen-validate` code; a `-dirty` stamp can likewise outlive
the commit that cleaned it. `tools/install.sh` forces a recompile and refuses
a stamp that doesn't match `HEAD`, so an installed binary's stamp is exact.
Lake's shared artifact cache would make stale stamps worse (it restores
builds by source hash alone), so `lakefile.toml` disables it for this
package.
-/
open Lean (Json)

/-- The commit `version` reports. -/
def buildCommit : String := build_commit%

/-- Answer one request line, as the running binary does. -/
def serveLine (line : String) : Json := processLine line buildCommit
