#!/usr/bin/env bash
# Build gamen-lean's gamen-validate and show how callers can use it.
#
# Plan: plans/downstream-migration-2026-09-29.md, Phase 0b.
#
#   tools/install.sh            build, print the version reply and the
#                               environment variables for each caller
#   tools/install.sh --link     also symlink it into ~/.local/bin (or
#                               --bin-dir DIR), i.e. onto PATH
#
# Migrate callers one at a time through their environment variable
# (GAMEN_VALIDATE_BIN, or CWYDE_GAMEN_BIN for cwyde). Every caller checks its
# variable, then PATH, before falling back to gamen-hs's cabal build, so
# --link switches every caller that is left. Use it only once each caller
# has been verified against the Lean binary.
#
# (Later: dcleg-service, once it is ported; migration Phase 0c.)
set -euo pipefail

link=false
bin_dir="$HOME/.local/bin"
while [ $# -gt 0 ]; do
  case "$1" in
    --link) link=true ;;
    --bin-dir) bin_dir="$2"; shift ;;
    -h|--help) sed -n '2,16p' "$0" | sed 's/^# \{0,1\}//'; exit 0 ;;
    *) echo "install.sh: unknown argument: $1" >&2; exit 2 ;;
  esac
  shift
done

repo="$(cd "$(dirname "$0")/.." && pwd)"
cd "$repo"

lake="$(command -v lake || true)"
[ -n "$lake" ] || lake="$HOME/.elan/bin/lake"
[ -x "$lake" ] || { echo "install.sh: lake not found (install elan)" >&2; exit 1; }

# Validate.lean stamps the git commit in at compile time, and Lake reuses
# the old build when no source changed. Removing its trace forces that one
# module to recompile, so the installed binary reports the current commit.
rm -f .lake/build/lib/lean/Validate.trace
"$lake" build gamen-validate

bin="$repo/.lake/build/bin/gamen-validate"
reply="$(printf '{"action":"version"}\n' | "$bin")"
echo "version: $reply"
case "$reply" in
  *'"implementation":"gamen-lean"'*) ;;
  *) echo "install.sh: unexpected version reply" >&2; exit 1 ;;
esac
case "$reply" in
  *'-dirty"'*) echo "note: built with uncommitted changes to tracked files" ;;
esac

if ! $link; then
  cat <<EOF

Built, not on PATH. To point one caller at it:
  guideline-validation:  export GAMEN_VALIDATE_BIN="$bin"
  cwyde:                 export CWYDE_GAMEN_BIN="$bin"
Once every caller is verified, run: tools/install.sh --link
EOF
  exit 0
fi

mkdir -p "$bin_dir"
ln -sfn "$bin" "$bin_dir/gamen-validate"
echo "linked: $bin_dir/gamen-validate -> $bin"

found="$(command -v gamen-validate || true)"
if [ "$found" != "$bin_dir/gamen-validate" ]; then
  echo "warning: 'gamen-validate' on PATH resolves to '${found:-nothing}', not $bin_dir/gamen-validate" >&2
fi
