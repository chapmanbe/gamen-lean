#!/usr/bin/env bash
# Build the doc-gen4 API reference for the Gamen and Widgets libraries and
# copy it to OUT_DIR.
#
#   bash tools/docs/build-api.sh OUT_DIR
#
# doc-gen4 lives in docbuild/ (its own Lake package), so the main
# lakefile.toml gains no dependency. Run from the repository root.
set -euo pipefail

if [ $# -ne 1 ]; then
  echo "usage: $0 OUT_DIR" >&2
  exit 2
fi
out="$1"
root="$(cd "$(dirname "$0")/../.." && pwd)"

(cd "$root/docbuild" && lake build Gamen:docs Widgets:docs)

mkdir -p "$out"
cp -R "$root/docbuild/.lake/build/doc/." "$out/"

# The entry points are the point of this step: never publish without them.
status=0
for f in index.html Gamen.html Widgets.html; do
  if [ ! -f "$out/$f" ]; then
    echo "::error::API reference is missing $f in $out"
    status=1
  fi
done
exit $status
