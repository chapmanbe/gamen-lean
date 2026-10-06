#!/usr/bin/env bash
# Install gamen-lean's gamen-validate and dcleg-service for downstream callers.
#
# Plan: plans/downstream-migration-2026-09-29.md, Phases 0b and 0c.
#
#   tools/install.sh                 build, check, and copy both binaries to
#                                    ~/.local/share/gamen-lean/ (not on PATH);
#                                    print how each caller selects them
#   tools/install.sh --link          also symlink it into ~/.local/bin (on PATH)
#   options: --bin-dir DIR           where --link puts the symlink
#            --share-dir DIR         where the binary is copied
#            --allow-dirty           install a build with uncommitted source changes
#
# The copy is what callers run, so a later `lake build` in this checkout
# doesn't change it. Migrate callers one at a time through their environment
# variable (GAMEN_VALIDATE_BIN, or CWYDE_GAMEN_BIN for cwyde). Every caller
# checks its variable, then PATH, before falling back to gamen-hs's cabal
# build, so --link switches every caller that is left: use it only once each
# caller has been verified against the Lean binary.
#
# dcleg-service's one caller, gamen-simulations, passes the binary's path to
# DclegClient, so --link links gamen-validate only.
set -euo pipefail

die() { echo "install.sh: $*" >&2; exit 1; }

link=false
allow_dirty=false
bin_dir="$HOME/.local/bin"
share_dir="$HOME/.local/share/gamen-lean"
while [ $# -gt 0 ]; do
  case "$1" in
    --link) link=true ;;
    --allow-dirty) allow_dirty=true ;;
    --bin-dir|--share-dir)
      [ $# -ge 2 ] && [ -n "$2" ] && [ "${2#--}" = "$2" ] || die "$1 needs a directory"
      if [ "$1" = --bin-dir ]; then bin_dir="$2"; else share_dir="$2"; fi
      shift ;;
    -h|--help) sed -n '2,22p' "$0" | sed 's/^# \{0,1\}//'; exit 0 ;;
    *) die "unknown argument: $1" ;;
  esac
  shift
done

# Resolve relative directories against the caller's directory, before cd.
abspath() { case "$1" in /*) echo "$1" ;; *) echo "$PWD/$1" ;; esac; }
bin_dir="$(abspath "$bin_dir")"
share_dir="$(abspath "$share_dir")"

repo="$(cd "$(dirname "$0")/.." && pwd)"
cd "$repo"

lake="$(command -v lake || true)"
[ -n "$lake" ] || lake="$HOME/.elan/bin/lake"
[ -x "$lake" ] || die "lake not found (install elan)"

# Validate/BuildInfo.lean and DclegService/BuildInfo.lean stamp the commit
# in at compile time, and Lake reuses a build when no source changed.
# Removing their traces forces those two modules to recompile, so the stamps
# are taken now.
rm -f .lake/build/lib/lean/Validate/BuildInfo.trace \
      .lake/build/lib/lean/DclegService/BuildInfo.trace
"$lake" build gamen-validate dcleg-service

head="$(git rev-parse --short=12 HEAD)"
mkdir -p "$share_dir"

# install_bin NAME VERSION-REQUEST: check the built binary's version reply
# against HEAD, then copy (not link) it into the share directory, atomically.
install_bin() {
  local name="$1" request="$2" built reply target
  built="$repo/.lake/build/bin/$name"
  reply="$(printf '%s\n' "$request" | "$built")"
  echo "$name version: $reply"
  case "$reply" in
    *'"implementation":"gamen-lean"'*) ;;
    *) die "unexpected $name version reply" ;;
  esac
  case "$reply" in
    *"\"commit\":\"$head\""*) ;;
    *"\"commit\":\"$head-dirty\""*)
      $allow_dirty || die "built with uncommitted source changes; commit them, or pass --allow-dirty" ;;
    *) die "$name's commit stamp doesn't match HEAD ($head)" ;;
  esac
  target="$share_dir/$name"
  cp "$built" "$target.tmp.$$"
  mv -f "$target.tmp.$$" "$target"
  echo "installed: $target"
}

install_bin gamen-validate '{"action":"version"}'
install_bin dcleg-service '{"id":"version","op":"version"}'
target="$share_dir/gamen-validate"

if ! $link; then
  cat <<EOF

Not on PATH. To point one caller at it:
  guideline-validation:  export GAMEN_VALIDATE_BIN="$target"
  cwyde:                 export CWYDE_GAMEN_BIN="$target"
  gamen-simulations:     DclegClient("$share_dir/dcleg-service")
Once every caller is verified, run: tools/install.sh --link
EOF
  exit 0
fi

mkdir -p "$bin_dir"
dest="$bin_dir/gamen-validate"
if [ -e "$dest" ] && [ ! -L "$dest" ]; then
  die "$dest exists and is not a symlink; move it aside first"
fi
ln -sfn "$target" "$dest"
echo "linked: $dest -> $target"

found="$(command -v gamen-validate || true)"
if [ "$found" != "$dest" ]; then
  echo "warning: 'gamen-validate' on PATH resolves to '${found:-nothing}', not $dest" >&2
fi
