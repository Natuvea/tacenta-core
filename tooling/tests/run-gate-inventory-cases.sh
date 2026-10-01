#!/usr/bin/env bash
# Negative controls for `tooling/gate-inventory.py`, the generator and checker of the gate inventory.
#
# The inventory is only evidence if it cannot go stale without a failure and cannot miss a gate. It is built
# here in a throwaway repository with one gate (`tooling/check-x.sh`), its control
# (`tooling/tests/run-check-x-cases.sh`) and a CI step list that runs both, and each case changes one thing:
#
#   the generated file edited by hand                 refused: not what the generator produces
#   a row's text changed, or a mutation added         refused: the file is stale
#   a CI step with an id that runs an unlisted script          refused: claimed by no row
#   a CI step with no id that runs an unlisted script          refused: the same, named as an unnamed step
#   a step that runs a listed script and an unlisted one      refused: no row names the unlisted one
#   a control that is not a file, one that does not mention its gate, a gate that is not a file   refused
#   a control marked local that a CI step runs                refused: a hand flag cannot contradict the walk
set -euo pipefail

root="$(cd "$(dirname "$0")/../.." && pwd)"
work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT
repo="$work/repo"
cases=0

git init -q -b main "$repo"
git -C "$repo" config user.name control
git -C "$repo" config user.email control@example.invalid
mkdir -p "$repo/tooling/tests" "$repo/tacenta-proofs"
cp "$root/tooling/gate-inventory.py" "$repo/tooling/"
printf '#!/usr/bin/env bash\necho x\n' > "$repo/tooling/check-x.sh"
printf '#!/usr/bin/env bash\nbash tooling/check-x.sh\n' > "$repo/tooling/tests/run-check-x-cases.sh"
printf '#!/usr/bin/env bash\necho new\n' > "$repo/tooling/new-gate.sh"
printf '{"mutations": []}\n' > "$repo/tooling/gate-mutations.json"
write_steps() {  # JSON array of steps
  python3 - "$repo/tooling/required-steps.json" "$1" <<'PY'
import json, sys
json.dump({"files": {".github/workflows/ci.yml": {"jobs": {"checks": {"steps": json.loads(sys.argv[2])}}}}},
          open(sys.argv[1], "w"))
PY
}
write_rows() {  # JSON array of rows
  python3 - "$repo/tooling/gate-inventory.json" "$1" <<'PY'
import json, sys
json.dump({"rows": json.loads(sys.argv[2])}, open(sys.argv[1], "w"))
PY
}
steps='[{"id": "s1", "run": "bash tooling/check-x.sh"}, {"id": "s2", "run": "bash tooling/tests/run-check-x-cases.sh"}]'
rows='[{"gate": "tooling/check-x.sh", "kind": "script", "what": "x holds", "controls": ["tooling/tests/run-check-x-cases.sh"]}]'
write_steps "$steps"
write_rows "$rows"
git -C "$repo" add -A
git -C "$repo" commit -q -m base
(cd "$repo" && python3 tooling/gate-inventory.py --write >/dev/null)
git -C "$repo" add -A
git -C "$repo" commit -q -m inventory

reset() { git -C "$repo" reset -q --hard HEAD && git -C "$repo" clean -fdq; }
check() {  # name want-exit needle
  local name="$1" want="$2" needle="${3:-}" out rc
  git -C "$repo" add -A
  set +e
  out="$(cd "$repo" && python3 tooling/gate-inventory.py --check 2>&1)"
  rc=$?
  set -e
  cases=$((cases + 1))
  if { [ "$want" = 0 ] && [ "$rc" -ne 0 ]; } || { [ "$want" != 0 ] && [ "$rc" -eq 0 ]; } \
     || { [ -n "$needle" ] && ! grep -qF -- "$needle" <<<"$out"; }; then
    echo "WRONG  gate-inventory $name: expected exit $want and '$needle', got exit $rc" >&2
    printf '%s\n' "$out" >&2
    exit 1
  fi
}

check 'the unchanged tree' 0 'is current'
reset
printf '\nA line added by hand.\n' >> "$repo/tacenta-proofs/GATE-INVENTORY.md"
check 'the file edited by hand' 1 'is not what the generator produces'
reset
write_rows '[{"gate": "tooling/check-x.sh", "kind": "script", "what": "x holds differently", "controls": ["tooling/tests/run-check-x-cases.sh"]}]'
check 'a row whose text changed' 1 'is not what the generator produces'
reset
printf '{"mutations": [{"id": "M1", "file": "tooling/check-x.sh"}]}\n' > "$repo/tooling/gate-mutations.json"
check 'a mutation added' 1 'is not what the generator produces'

reset
write_steps '[{"id": "s1", "run": "bash tooling/check-x.sh"}, {"id": "s2", "run": "bash tooling/tests/run-check-x-cases.sh"}, {"id": "s3", "run": "bash tooling/new-gate.sh"}]'
check 'a step with an id that runs an unlisted script' 1 'CI step s3'
reset
write_steps '[{"id": "s1", "run": "bash tooling/check-x.sh"}, {"id": "s2", "run": "bash tooling/tests/run-check-x-cases.sh"}, {"run": "bash tooling/new-gate.sh"}]'
check 'a step with no id that runs an unlisted script' 1 'unnamed step'
reset
write_steps '[{"id": "s1", "run": "bash tooling/check-x.sh"}, {"id": "s2", "run": "bash tooling/tests/run-check-x-cases.sh"}, {"id": "s4", "run": "bash tooling/new-gate.sh && bash tooling/check-x.sh"}]'
check 'a step that runs a listed script and an unlisted one' 1 'no row names tooling/new-gate.sh'
reset
write_steps '[{"id": "s1", "run": "bash tooling/check-x.sh"}, {"id": "s2", "run": "bash tooling/tests/run-check-x-cases.sh"}, {"id": "s5", "run": "cargo deny check"}]'
check 'a step with an id that runs no script' 1 'CI step s5'

reset
write_rows '[{"gate": "tooling/check-x.sh", "kind": "script", "what": "x holds", "controls": ["tooling/tests/run-no-such-cases.sh"]}]'
check 'a control that is not a file' 1 'is not in the tree'
reset
printf '#!/usr/bin/env bash\necho unrelated\n' > "$repo/tooling/tests/run-check-x-cases.sh"
check 'a control that does not mention its gate' 1 'does not mention the gate'
reset
write_rows '[{"gate": "tooling/check-missing.sh", "kind": "script", "what": "x holds", "controls": []}]'
check 'a gate that is not a file' 1 'is not in the tree'
reset
write_rows '[{"gate": "tooling/check-x.sh", "kind": "script", "what": "x holds", "controls": [{"path": "tooling/tests/run-check-x-cases.sh", "ci": false}]}]'
check 'a control marked local that a CI step runs' 1 'is marked local but CI step'

echo "gate-inventory-cases: $cases cases (a stale file, row or mutation; a step with or without an id that runs an unlisted script; a control or gate that is not a file; a hand flag against the walk) gave the expected result"
