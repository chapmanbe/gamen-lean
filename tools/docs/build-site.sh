#!/usr/bin/env bash
# Build the whole documentation site into _site/:
#
#   _site/index.html      landing page, from README.md
#   _site/api/            doc-gen4 API reference (Gamen, Widgets)
#   _site/notebooks/      read-only notebook pages, outputs computed by Lean
#
#   bash tools/docs/build-site.sh
#
# Needs elan (lake on PATH) and Python 3 with tools/docs/requirements.txt.
# Used by .github/workflows/docs.yml; run from anywhere.
set -euo pipefail

root="$(cd "$(dirname "$0")/../.." && pwd)"
cd "$root"
python="${PYTHON:-python3}"

rm -rf _site
lake build
"$python" tools/docs/landing.py README.md _site
bash tools/docs/build-api.sh _site/api
"$python" tools/docs/render.py --out _site/notebooks Notebooks/*.lean

status=0
for f in _site/index.html _site/api/index.html _site/notebooks/index.html; do
  if [ ! -f "$f" ]; then
    echo "::error::site is missing $f"
    status=1
  fi
done
exit $status
