import Lean.Elab.Term

/-!
# Validate.Stamp

The `build_commit%` term: the git commit a file is compiled at, for the
`version` replies of `gamen-validate` (`Validate/BuildInfo.lean`) and
`dcleg-service` (`DclegService/BuildInfo.lean`). Moved here unchanged from
`Validate/BuildInfo.lean`, so both executables stamp alike without
`dcleg-service` importing `gamen-validate`'s provers. The stamp is taken in
the file that *uses* `build_commit%`, so each `BuildInfo` file carries its
own; `Validate/BuildInfo.lean` says when a stamp can be stale.
-/

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
/-- The commit the file using this term is compiled at (see the module
docstring). git runs in that file's own directory, so building gamen-lean as
a dependency of another workspace still stamps gamen-lean's commit. -/
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
