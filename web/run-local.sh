#!/usr/bin/env bash
# Run the gamen course in lean4web on THIS machine only (http://127.0.0.1:3000).
#
# Lean runs WITHOUT the bubblewrap sandbox here (macOS has none), so both
# processes are bound to 127.0.0.1. lean4web's own `npm start` passes
# `vite --host`, which exposes the editor to the whole network; don't use it.
# A classroom deployment needs a Linux server with bubblewrap (see
# lean4web/doc/Installation.md).
set -e
HERE="$(cd "$(dirname "$0")" && pwd)"
L4W="$HERE/lean4web"
[ -d "$L4W" ] || { echo "Run $HERE/setup.sh first." >&2; exit 1; }
export PATH="$HOME/.elan/bin:$PATH"
export PROJECTS_BASE_PATH=../projects            # relative to lean4web/
export LEAN4WEB_SERVER_PORT=${LEAN4WEB_SERVER_PORT:-8090}
cd "$L4W"
( cd server && NODE_ENV=development HOST=127.0.0.1 PORT=$LEAN4WEB_SERVER_PORT npx nodemon index.mjs ) &
SERVER=$!
trap 'kill $SERVER 2>/dev/null' EXIT
cd client && NODE_ENV=development npx vite --host 127.0.0.1 --port 3000
