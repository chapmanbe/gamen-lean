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
export PATH="$HOME/.elan/bin:$PATH"  # lake, also from shells that skip ~/.zshrc

# `Widgets` has no root module (lakefile.toml: globs = ["Widgets.+"]), so
# `Widgets:docs` documents nothing; ask for each widget module instead.
widget_targets=()
while IFS= read -r f; do
  m="${f#"$root"/}"; m="${m%.lean}"; m="${m//\//.}"
  widget_targets+=("$m:docs")
done < <(find "$root/Widgets" -name '*.lean' | sort)

(cd "$root/docbuild" && lake build Gamen:docs "${widget_targets[@]}")

mkdir -p "$out"
cp -R "$root/docbuild/.lake/build/doc/." "$out/"

# The entry points are the point of this step: never publish without them.
status=0
for f in index.html Gamen.html Widgets/KripkeExplorer.html Widgets/StaticHtml.html; do
  if [ ! -f "$out/$f" ]; then
    echo "::error::API reference is missing $f in $out"
    status=1
  fi
done
exit $status
