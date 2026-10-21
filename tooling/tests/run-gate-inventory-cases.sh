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
#   a control or row that names a CI step the workflow does not have   refused (accepted while it has it)
#   a shell-script control whose named step does not run it             refused (accepted through a script)
#   a row's own step that does not run its gate, a verdict step that is gone   refused; a verdict step shown
#   two steps that run one script, in either order    the same inventory
#   a combining step                                  the gate shown at the step that runs it, not at the
#                                                     combining one, in either order; a combining step that
#                                                     lists a file its command does not run, or is not a step,
#                                                     refused
#   the real tree's workflow with its jobs reversed   the same inventory as the committed one
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
write_rows() {  # JSON array of rows [, JSON object of combining steps]
  python3 - "$repo/tooling/gate-inventory.json" "$1" "${2:-}" <<'PY'
import json, sys
doc = {"rows": json.loads(sys.argv[2])}
if sys.argv[3]:
    doc["combining_steps"] = json.loads(sys.argv[3])
json.dump(doc, open(sys.argv[1], "w"))
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
# A control named with the step that gives its verdict: accepted while the step exists, refused once it is gone,
# as when the job that combines a split run is deleted and the step that only produces its inputs is left.
reset
write_rows '[{"gate": "tooling/check-x.sh", "kind": "script", "what": "x holds", "controls": [{"path": "tooling/tests/run-check-x-cases.sh", "ci_steps": ["s2"]}]}]'
(cd "$repo" && python3 tooling/gate-inventory.py --write >/dev/null)
check 'a control named with a step the workflow has' 0 'is current'
write_steps '[{"id": "s1", "run": "bash tooling/check-x.sh"}, {"id": "s2b", "run": "bash tooling/tests/run-check-x-cases.sh"}]'
check 'a control named with a step the workflow no longer has' 1 'names CI step s2, which the workflow does not have'
reset
write_rows '[{"gate": "tooling/check-x.sh", "kind": "script", "what": "x holds", "ci_steps": ["s9"], "controls": ["tooling/tests/run-check-x-cases.sh"]}]'
check 'a row named with a step the workflow does not have' 1 'names CI step s9, which the workflow does not have'
# The named step must run the control. Repointed at another command it is refused; running it through a script
# of its own is accepted.
reset
write_rows '[{"gate": "tooling/check-x.sh", "kind": "script", "what": "x holds", "controls": [{"path": "tooling/tests/run-check-x-cases.sh", "ci_steps": ["s2"]}]}]'
write_steps '[{"id": "s1", "run": "bash tooling/check-x.sh"}, {"id": "s2", "run": "bash tooling/check-x.sh --again"}, {"id": "s3", "run": "bash tooling/tests/run-check-x-cases.sh"}]'
check 'a named step repointed at another command' 1 'names CI step s2, whose command does not run it'
reset
printf '#!/usr/bin/env bash\nbash tooling/tests/run-check-x-cases.sh\n' > "$repo/tooling/run-all.sh"
write_rows '[{"gate": "tooling/check-x.sh", "kind": "script", "what": "x holds", "controls": [{"path": "tooling/tests/run-check-x-cases.sh", "ci_steps": ["s2"]}]}, {"gate": "tooling/run-all.sh", "kind": "script", "what": "runs the cases", "controls": []}]'
write_steps '[{"id": "s1", "run": "bash tooling/check-x.sh"}, {"id": "s2", "run": "bash tooling/run-all.sh"}]'
(cd "$repo" && git add -A && python3 tooling/gate-inventory.py --write >/dev/null)
check 'a named step that runs the control through a script' 0 'is current'

# A row's own step must run its gate; the step that only gives a verdict is a verdict step.
reset
write_rows '[{"gate": "tooling/check-x.sh", "kind": "script", "what": "x holds", "ci_steps": ["s2"], "controls": ["tooling/tests/run-check-x-cases.sh"]}]'
write_steps '[{"id": "s1", "run": "bash tooling/check-x.sh"}, {"id": "s2", "run": "test \"$NEEDS_RESULT\" = success"}, {"id": "s3", "run": "bash tooling/tests/run-check-x-cases.sh"}]'
check 'a row named with a step that does not run its gate' 1 'names CI step s2, whose command does not run it'
write_rows '[{"gate": "tooling/check-x.sh", "kind": "script", "what": "x holds", "verdict_steps": ["s9"], "controls": ["tooling/tests/run-check-x-cases.sh"]}]'
check 'a verdict step the workflow does not have' 1 'names verdict step s9, which the workflow does not have'
write_rows '[{"gate": "tooling/check-x.sh", "kind": "script", "what": "x holds", "verdict_steps": ["s2"], "controls": ["tooling/tests/run-check-x-cases.sh"]}]'
(cd "$repo" && git add -A && python3 tooling/gate-inventory.py --write >/dev/null)
check 'a verdict step' 0 'is current'
grep -qF '| s1; verdict s2 |' "$repo/tacenta-proofs/GATE-INVENTORY.md" \
  || { echo "WRONG  gate-inventory a verdict step: not shown beside the step that runs the gate" >&2; exit 1; }

# Two steps run one script: the inventory is the same in either order.
reset
write_steps '[{"id": "s2", "run": "bash tooling/check-x.sh"}, {"id": "s1", "run": "bash tooling/check-x.sh --again"}, {"id": "s3", "run": "bash tooling/tests/run-check-x-cases.sh"}]'
(cd "$repo" && git add -A && python3 tooling/gate-inventory.py --write >/dev/null)
check 'two steps that run one script' 0 'is current'
write_steps '[{"id": "s1", "run": "bash tooling/check-x.sh --again"}, {"id": "s3", "run": "bash tooling/tests/run-check-x-cases.sh"}, {"id": "s2", "run": "bash tooling/check-x.sh"}]'
check 'the same steps in another order' 0 'is current'

# A combining step runs only what it lists: the gate is shown at the step that runs it, whichever comes first.
reset
printf '#!/usr/bin/env bash\nbash tooling/check-x.sh\n' > "$repo/tooling/run-all.sh"
combining='{"s0": {"runs": ["tooling/check-x.sh"], "why": "reads what s1 wrote"}}'
rows_c='[{"gate": "tooling/check-x.sh", "kind": "script", "what": "x holds", "verdict_steps": ["s0"], "controls": ["tooling/tests/run-check-x-cases.sh"]}, {"gate": "tooling/run-all.sh", "kind": "script", "what": "runs x", "controls": []}]'
write_rows "$rows_c" "$combining"
write_steps '[{"id": "s0", "run": "bash tooling/check-x.sh --combine"}, {"id": "s1", "run": "bash tooling/run-all.sh"}, {"id": "s3", "run": "bash tooling/tests/run-check-x-cases.sh"}]'
(cd "$repo" && git add -A && python3 tooling/gate-inventory.py --write >/dev/null)
check 'a combining step' 0 'is current'
grep -qF '| s1 (through run-all.sh); verdict s0 |' "$repo/tacenta-proofs/GATE-INVENTORY.md" \
  || { echo "WRONG  gate-inventory a combining step: the gate is not shown at the step that runs it" >&2; exit 1; }
write_steps '[{"id": "s1", "run": "bash tooling/run-all.sh"}, {"id": "s3", "run": "bash tooling/tests/run-check-x-cases.sh"}, {"id": "s0", "run": "bash tooling/check-x.sh --combine"}]'
check 'a combining step after the step that runs the gate' 0 'is current'
write_rows "$rows_c" '{"s0": {"runs": ["tooling/new-gate.sh"], "why": "reads what s1 wrote"}}'
check 'a combining step that lists a file its command does not run' 1 'combining step s0 lists tooling/new-gate.sh, which its command does not run'
write_rows "$rows_c" '{"s7": {"runs": ["tooling/check-x.sh"], "why": "reads what s1 wrote"}}'
check 'a combining step that is not a step' 1 'combining step s7 is not a step of the workflow'

# The real tree: its workflow's jobs reversed give the same inventory.
cases=$((cases + 1))
python3 - "$root/tooling/required-steps.json" "$work/reversed-steps.json" <<'PY'
import json, sys
doc = json.load(open(sys.argv[1]))
workflow = doc["files"][".github/workflows/ci.yml"]
workflow["jobs"] = dict(reversed(list(workflow["jobs"].items())))
json.dump(doc, open(sys.argv[2], "w"))
PY
(cd "$root" && python3 tooling/gate-inventory.py --print) > "$work/inventory-as-is.md"
(cd "$root" && python3 tooling/gate-inventory.py --print --steps "$work/reversed-steps.json") > "$work/inventory-reversed.md"
cmp -s "$work/inventory-as-is.md" "$work/inventory-reversed.md" \
  || { echo "WRONG  gate-inventory the real tree with its jobs reversed: another inventory" >&2
       diff "$work/inventory-as-is.md" "$work/inventory-reversed.md" | head -n 20 >&2; exit 1; }

echo "gate-inventory-cases: $cases cases (a stale file, row or mutation; a step with or without an id that runs an unlisted script; a control or gate that is not a file; a hand flag against the walk; a named verdict step that is gone or repointed; a row's own step and its verdict steps; the order of steps and jobs, a combining step, the real tree with its jobs reversed) gave the expected result"
