#!/bin/sh
# Regenerate interactiveSvgQuiet.js from the pinned ProofWidgets4 release.
# ProofWidgets4 is Apache-2.0 (Copyright the ProofWidgets4 contributors).
# Modification: removes the debug line ("frame: …, state: …, mousePos: …")
# that the stock InteractiveSvg component prints under every widget.
set -e
SRC=../../.lake/packages/proofwidgets/widget/js/interactiveSvg.js
OUT=interactiveSvgQuiet.js
DEBUG='children:[t(l,{html:d}),e("div",{children:["frame: ",p,". state: ",c.current,", mousePos: ",h?h.join(", "):"none",", mouseButtonState: ",g]})]'
grep -qF "$DEBUG" "$SRC" || { echo "debug snippet not found; ProofWidgets version changed" >&2; exit 1; }
{ printf '// Modified from ProofWidgets4 widget/js/interactiveSvg.js (Apache-2.0): debug line removed. See make-quiet.sh.\n'
  python3 -c "import sys; s=open('$SRC').read(); print(s.replace(sys.argv[1], 'children:[t(l,{html:d})]'), end='')" "$DEBUG"; } > "$OUT"
echo "wrote $OUT"
