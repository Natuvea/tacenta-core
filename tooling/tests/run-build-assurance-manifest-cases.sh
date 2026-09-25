#!/usr/bin/env bash
# Exercise the assurance-manifest receipt refusal paths against the production builder.
set -euo pipefail

here="$(cd "$(dirname "$0")" && pwd)"
root="$(cd "$here/../.." && pwd)"
work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT
fixture="$root/tooling/tests/assurance-receipts-fixture.json"
export ASSURANCE_FIXTURE_COMMIT="$(git -C "$root" rev-parse HEAD)"
export ASSURANCE_FIXTURE_TREE="$(git -C "$root" rev-parse 'HEAD^{tree}')"

expect_fail() {
  local name="$1" needle="$2" out rc
  set +e
  out="$(python3 "$root/tooling/build-assurance-manifest.py" --allow-dirty --receipts "$work/$name.json" --output "$work/$name.out" 2>&1)"
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

make_case() {
  local name="$1" program="$2"
  python3 - "$fixture" "$work/$name.json" "$program" <<'PY'
import json, pathlib, sys
source, output, program = map(pathlib.Path, sys.argv[1:])
data = json.loads(source.read_text())
data['candidate'] = {
    'commit': __import__('os').environ['ASSURANCE_FIXTURE_COMMIT'],
    'tree': __import__('os').environ['ASSURANCE_FIXTURE_TREE'],
}
for check in data['checks']:
    check['run'].update(commit=data['candidate']['commit'], tree=data['candidate']['tree'])
exec(program.read_text(), {'data': data})
output.write_text(json.dumps(data, indent=2) + '\n')
PY
}

printf '%s\n' '# pass fixture is rebound to this checkout by make_case' > "$work/pass.py"
make_case pass "$work/pass.py"
python3 "$root/tooling/build-assurance-manifest.py" --allow-dirty --receipts "$work/pass.json" --output "$work/pass.out"

printf "%s\n" "data['checks'] = [c for c in data['checks'] if c['id'] != 'proofs']" > "$work/missing.py"
make_case missing "$work/missing.py"
expect_fail missing 'missing required check receipts: proofs'

printf "%s\n" "next(c for c in data['checks'] if c['id'] == 'rust')['status'] = 'skipped'" > "$work/skipped.py"
make_case skipped "$work/skipped.py"
expect_fail skipped 'required applicable check rust is skipped'

printf "%s\n" "c = next(c for c in data['checks'] if c['id'] == 'audit'); c['applicable'] = False" > "$work/inapplicable.py"
make_case inapplicable "$work/inapplicable.py"
expect_fail inapplicable 'inapplicable check audit must be not_applicable'

printf "%s\n" "next(c for c in data['checks'] if c['id'] == 'audit')['classification'] = 'optional'" > "$work/downgraded.py"
make_case downgraded "$work/downgraded.py"
expect_fail downgraded 'required receipt audit must be an applicable required check'

printf "%s\n" "data['candidate']['commit'] = '0' * 40" > "$work/foreign.py"
make_case foreign "$work/foreign.py"
expect_fail foreign 'receipts candidate commit/tree does not match selected source'

echo 'build-assurance-manifest-cases: pass case and 5 receipt refusals gave the expected result'
