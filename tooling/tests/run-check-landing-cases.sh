#!/usr/bin/env bash
# Negative controls for tooling/check-landing.sh, on a disposable clone of the commit under test:
#
#   the tree as committed                                passes
#   a listed row dropped from tooling/gate-inventory.json  refused, the gate named
#   the generated inventory without a listed gate        refused
#   the obligations section dropped                      refused
#   a malformed line in tooling/landing-rows.txt         refused
set -euo pipefail

root="$(cd "$(dirname "$0")/../.." && pwd)"
work="$(mktemp -d "${TMPDIR:-/tmp}/landing-cases.XXXXXX")"
trap 'rm -rf "$work"' EXIT
clone="$work/clone"
git clone -q --shared --no-checkout "$root" "$clone"
git -C "$clone" checkout -q --detach "$(git -C "$root" rev-parse HEAD)"
cases=0
fail_case() {
  echo "WRONG  check-landing $1" >&2
  shift
  [ $# -eq 0 ] || printf '%s\n' "$@" >&2
  exit 1
}
run() {  # name want-exit needle
  local rc
  set +e
  out="$(cd "$clone" && bash tooling/check-landing.sh 2>&1)"
  rc=$?
  set -e
  cases=$((cases + 1))
  [ "$rc" -eq "$2" ] && grep -qF -- "$3" <<<"$out" || fail_case "$1: expected exit $2 and '$3', got exit $rc" "$out"
  git -C "$clone" checkout -q -- .
}
edit() {  # file program-over-t
  python3 - "$clone/$1" "$2" <<'PY'
import sys
path, program = sys.argv[1:]
t = open(path).read()
exec(program)
open(path, "w").write(t)
PY
}

run committed 0 "every listed row and section is present"
edit tooling/gate-inventory.json "t = '\n'.join(l for l in t.split('\n') if not l.startswith('  {\"gate\": \"tooling/check-merge-exactness.sh\"'))"
run row-dropped 1 "tooling/gate-inventory.json has no row for tooling/check-merge-exactness.sh"
edit tacenta-proofs/GATE-INVENTORY.md "t = t.replace('\`tooling/reflow-shared-lists.py\`', '\`tooling/elsewhere.py\`')"
run generated-without 1 "tacenta-proofs/GATE-INVENTORY.md does not name tooling/reflow-shared-lists.py"
edit ASSURANCE-OBLIGATIONS.md "t = t.replace('### Tooling for new proof modules and merges (2026-10-21)\n', '', 1)"
run section-dropped 1 "ASSURANCE-OBLIGATIONS.md has no line"
printf 'rows tooling/x.sh\n' >> "$clone/tooling/landing-rows.txt"
run malformed 1 "is not \`row <gate>\` or \`section <file> <heading>\`"

echo "check-landing-cases: $cases cases (the committed tree passed; a dropped row, a generated inventory without a listed gate, a dropped section and a malformed line refused) gave the expected result"
