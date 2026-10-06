import DclegService.Core
import Validate.Stamp

/-!
# DclegService.BuildInfo

The git commit `dcleg-service`'s Lean-only `version` op reports, stamped in
when this file is compiled (`build_commit%`, `Validate/Stamp.lean`). Kept
out of `DclegService.lean` so the tests can import it. The stamp can be
stale in the same way as `gamen-validate`'s (`Validate/BuildInfo.lean`);
`tools/install.sh` forces a recompile of this file and checks the stamp
against `HEAD`.
-/

/-- The commit `version` reports. -/
def dclegBuildCommit : String := build_commit%
