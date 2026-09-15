#!/usr/bin/env bash
# Exercise the receipt collector's source and applicability controls.
set -euo pipefail

here="$(cd "$(dirname "$0")" && pwd)"
root="$(cd "$here/../.." && pwd)"
work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT

write_receipts() {
  local directory="$1" event="$2"
  mkdir -p "$directory"
  for id in rust msrv armv7 vectors audit proofs translation checks; do
    GITHUB_EVENT_NAME="$event" GITHUB_RUN_ID=control GITHUB_RUN_ATTEMPT=1 \
      python3 "$root/tooling/write-assurance-receipt.py" --id "$id" --classification required \
      --command "control-$id" --output "$directory/$id.json" >/dev/null
  done
}

expect_fail() {
  local name="$1" needle="$2" directory="$3" event="$4" out rc
  set +e
  out="$(python3 "$root/tooling/collect-assurance-receipts.py" --event "$event" --input-dir "$directory" --output "$work/$name.out" 2>&1)"
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

mutate() {
  local path="$1" program="$2"
  python3 - "$path" "$program" <<'PY'
import json, pathlib, sys
path, program = map(pathlib.Path, sys.argv[1:])
data = json.loads(path.read_text())
exec(program.read_text(), {'data': data})
path.write_text(json.dumps(data, indent=2) + '\n')
PY
}

write_receipts "$work/pass" push
python3 "$root/tooling/collect-assurance-receipts.py" --event push --input-dir "$work/pass" --output "$work/pass.out" >/dev/null

cp -R "$work/pass" "$work/foreign"
printf "%s\n" "data['run']['commit'] = '0' * 40" > "$work/foreign.py"
mutate "$work/foreign/rust.json" "$work/foreign.py"
expect_fail foreign 'receipt rust was not produced for the selected candidate' "$work/foreign" push

cp -R "$work/pass" "$work/wrong-classification"
printf "%s\n" "data['classification'] = 'optional'" > "$work/wrong-classification.py"
mutate "$work/wrong-classification/audit.json" "$work/wrong-classification.py"
expect_fail wrong-classification 'required receipt audit must be an applicable required check' "$work/wrong-classification" push

cp -R "$work/pass" "$work/wrong-event"
printf "%s\n" "data['environment']['event'] = 'pull_request'" > "$work/wrong-event.py"
mutate "$work/wrong-event/vectors.json" "$work/wrong-event.py"
expect_fail wrong-event 'receipt vectors event does not match selected event push' "$work/wrong-event" push

cp -R "$work/pass" "$work/duplicate"
cp "$work/duplicate/rust.json" "$work/duplicate/duplicate.json"
expect_fail duplicate 'duplicate check receipt rust' "$work/duplicate" push

write_receipts "$work/pull-request" pull_request
expect_fail missing-signoff 'missing required conditional check receipt: sign-off' "$work/pull-request" pull_request
GITHUB_EVENT_NAME=pull_request GITHUB_RUN_ID=control GITHUB_RUN_ATTEMPT=1 \
  python3 "$root/tooling/write-assurance-receipt.py" --id sign-off --classification conditional \
  --command control-sign-off --output "$work/pull-request/sign-off.json" >/dev/null
python3 "$root/tooling/collect-assurance-receipts.py" --event pull_request --input-dir "$work/pull-request" --output "$work/pull-request.out" >/dev/null

echo 'collect-assurance-receipts-cases: 2 pass cases and 5 receipt refusals gave the expected result'
