#!/usr/bin/env bash
# One-time setup of the local web editor for the gamen notebooks.
#   1. clone lean4web at the commit this was tested with (into web/lean4web,
#      which git ignores),
#   2. apply lean4web-localhost.patch (bind to 127.0.0.1; see README.md),
#   3. install its npm dependencies,
#   4. build the course project (and the gamen package it depends on).
set -e
HERE="$(cd "$(dirname "$0")" && pwd)"
LEAN4WEB_COMMIT=27e95901718055152e6d5468e251ca34c13d0b4a
export PATH="$HOME/.elan/bin:$PATH"

if [ ! -d "$HERE/lean4web" ]; then
  git clone https://github.com/leanprover-community/lean4web.git "$HERE/lean4web"
  git -C "$HERE/lean4web" checkout "$LEAN4WEB_COMMIT"
  git -C "$HERE/lean4web" apply "$HERE/lean4web-localhost.patch"
fi
( cd "$HERE/lean4web" && npm install )
"$HERE/projects/GamenCourse/leanweb-build.sh"
echo "Done. Start the editor with: $HERE/run-local.sh"
