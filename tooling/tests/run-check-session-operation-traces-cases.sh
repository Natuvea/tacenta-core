#!/usr/bin/env bash
# Hold the P6 operation-trace structural checker to representative faults.
set -euo pipefail

here="$(cd "$(dirname "$0")" && pwd)"
root="$(cd "$here/../.." && pwd)"
work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT

make_case() {
  local name="$1"
  local dst="$work/$name"
  mkdir -p "$dst/tooling" "$dst/tacenta-test-vectors/traces"
  cp "$root/tooling/check-session-operation-traces.py" "$dst/tooling/"
  cp "$root/tacenta-test-vectors/traces/session-operation-trace.json" \
    "$dst/tacenta-test-vectors/traces/"
}

expect_fail() {
  local name="$1" needle="$2" out rc
  set +e
  out="$(python3 "$work/$name/tooling/check-session-operation-traces.py" 2>&1)"
  rc=$?
  set -e
  if [ "$rc" -eq 0 ]; then
    echo "WRONG  $name: expected refusal" >&2
    return 1
  fi
  if ! printf '%s' "$out" | grep -qF -- "$needle"; then
    echo "WRONG  $name: missing diagnostic '$needle'" >&2
    printf '%s\n' "$out" >&2
    return 1
  fi
}

make_case pass
python3 "$work/pass/tooling/check-session-operation-traces.py"

make_case missing-control
python3 - "$work/missing-control/tacenta-test-vectors/traces/session-operation-trace.json" <<'PY'
import json, pathlib, sys
path = pathlib.Path(sys.argv[1])
data = json.loads(path.read_text())
data['traces'] = [t for t in data['traces'] if t['id'] != 'control-missing-required-input']
path.write_text(json.dumps(data, indent=2) + '\n')
PY
expect_fail missing-control 'missing required trace(s): control-missing-required-input'

make_case missing-family-nine
python3 - "$work/missing-family-nine/tacenta-test-vectors/traces/session-operation-trace.json" <<'PY'
import json, pathlib, sys
path = pathlib.Path(sys.argv[1])
data = json.loads(path.read_text())
data['traces'] = [t for t in data['traces'] if t['id'] != 'establish-initiator-non-contributory-dh-refused']
path.write_text(json.dumps(data, indent=2) + '\n')
PY
expect_fail missing-family-nine 'missing required trace(s): establish-initiator-non-contributory-dh-refused'

make_case refused-changes-state
python3 - "$work/refused-changes-state/tacenta-test-vectors/traces/session-operation-trace.json" <<'PY'
import json, pathlib, sys
path = pathlib.Path(sys.argv[1])
data = json.loads(path.read_text())
for trace in data['traces']:
    if trace['id'] == 'last-resort-handshake-replay-refused':
        trace['steps'][0]['effect']['session'] = 'message-accepted'
path.write_text(json.dumps(data, indent=2) + '\n')
PY
expect_fail refused-changes-state 'a refused operation leaves store and session unchanged'

echo 'check-session-operation-traces-cases: pass case and 3 refusal cases gave the expected result'
