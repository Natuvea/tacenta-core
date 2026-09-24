#!/usr/bin/env bash
# Refuse unresolved Git conflict markers in tracked repository files.
set -euo pipefail
cd "$(git rev-parse --show-toplevel)"

hits="$(git grep -I -n -E '^(<<<<<<<|=======|>>>>>>>)' -- . ':!*.patch' || true)"
if [ -n "$hits" ]; then
  echo "conflict-markers: unresolved marker(s) found:" >&2
  printf '%s\n' "$hits" >&2
  exit 1
fi
echo "conflict-markers: none"
