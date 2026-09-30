import Validate.Core
import Lean.Elab.Term

/-!
# Validate.BuildInfo

The git commit `gamen-validate`'s `version` action reports (plan:
`plans/downstream-migration-2026-09-29.md`, Phase 0a), stamped in when this
file is compiled. Kept out of `Validate.lean` so the tests can import it.

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

/-- The stamp for a `git rev-parse` result and a `git status --porcelain`
result: the short revision, `-dirty` if any source file differs from it,
`unknown` without a revision. -/
def stampOf : Option String → Option String → String
  | some rev, some changes => if changes.isEmpty then rev else rev ++ "-dirty"
  | some rev, none => rev
  | none, _ => "unknown"

/-- The files whose changes make a build `-dirty`: every Lean source,
tracked or not, and the build configuration. Edits to notes, plans or data
don't count, and neither do ignored files (such as `.lake/`). -/
def sourcePathspec : Array String :=
  #["*.lean", "lakefile.toml", "lean-toolchain", "lake-manifest.json"]

open Lean Elab Term in
/-- The commit this file is compiled at (see the module docstring). git runs
in this file's own directory, so building gamen-lean as a dependency of
another workspace still stamps gamen-lean's commit. -/
elab "build_commit%" : term => do
  let dir := (System.FilePath.mk (← getFileName)).parent.getD "."
  let git (args : Array String) : IO (Option String) := do
    try
      let out ← IO.Process.output { cmd := "git", args := #["-C", dir.toString] ++ args }
      return if out.exitCode == 0 then some out.stdout.trimAscii.toString else none
    catch _ => return none
  let rev ← git #["rev-parse", "--short=12", "HEAD"]
  let changes ← git (#["status", "--porcelain", "--untracked-files=all", "--"] ++ sourcePathspec)
  return mkStrLit (stampOf rev changes)

/-- The commit `version` reports. -/
def buildCommit : String := build_commit%

/-- Answer one request line, as the running binary does. -/
def serveLine (line : String) : Json := processLine line buildCommit
