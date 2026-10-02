#!/usr/bin/env bash
# Negative controls for the build direction of `tooling/build-evidence-pack.py` (`--manifest --receipts --output`).
#
# `run-build-evidence-pack-cases.sh` holds the verifier (`--verify`) to 58 cases on fixture packs. The builder is
# what makes the pack the reviewer reads at the candidate, and removing each of its guards one at a time
# (`python3 tooling/mutate-gates.py --guards tooling/build-evidence-pack.py`) left six of them unneeded by any case.
# This builds a real pack for the commit under test from receipts written the way the workflow writes them and a
# manifest built by the real builder, requires `--verify` to accept it, and then changes one thing at a time:
#
#   a manifest that does not validate        the builder must refuse before it copies anything
#   receipts of another schema version       refused
#   receipts for another candidate           refused
#   receipts that no longer match the manifest   refused (one check's outcome edited in the receipts only)
#   a non-empty output directory             refused, and the directory is left as it was
#
# Two guards stay unreached by design: the clean-tree check (the manifest's own `--validate` refuses first) and an
# allowlisted source missing at build time (it needs a tree whose manifest is built after the file is gone).
set -euo pipefail

root="$(cd "$(dirname "$0")/../.." && pwd)"
work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT
fixture="$root/tooling/tests/assurance-receipts-fixture.json"
export ASSURANCE_FIXTURE_COMMIT="$(git -C "$root" rev-parse HEAD)"
export ASSURANCE_FIXTURE_TREE="$(git -C "$root" rev-parse 'HEAD^{tree}')"
cases=0

python3 - "$fixture" "$work/receipts.json" <<'PY'
import json, os, pathlib, sys
source, output = map(pathlib.Path, sys.argv[1:])
data = json.loads(source.read_text())
data['candidate'] = {'commit': os.environ['ASSURANCE_FIXTURE_COMMIT'], 'tree': os.environ['ASSURANCE_FIXTURE_TREE']}
sys.path.insert(0, str(source.resolve().parents[1]))
from assurance_validation import expected_step_outcomes
table = expected_step_outcomes()
for check in data['checks']:
    check['run'].update(commit=data['candidate']['commit'], tree=data['candidate']['tree'])
    check['environment'] = {'event': 'push'}
    check['step_outcomes'] = {step: 'success' for step in table[(check['id'], 'push')]}
output.write_text(json.dumps(data, indent=2) + '\n')
PY
python3 "$root/tooling/build-assurance-manifest.py" --allow-dirty --receipts "$work/receipts.json" --output "$work/manifest.json" >/dev/null
python3 -c 'import json, pathlib, sys; p=pathlib.Path(sys.argv[1]); d=json.loads(p.read_text()); d["identity"]["clean_tree"]=True; p.write_text(json.dumps(d, indent=2)+"\n")' "$work/manifest.json"

build() {  # name manifest receipts output -> sets out, rc
  set +e
  out="$(python3 "$root/tooling/build-evidence-pack.py" --manifest "$2" --receipts "$3" --output "$4" 2>&1)"
  rc=$?
  set -e
}
refused() {  # name needle manifest receipts output
  build "$1" "$3" "$4" "$5"
  cases=$((cases + 1))
  if [ "$rc" -eq 0 ] || ! grep -qF -- "$2" <<<"$out"; then
    echo "WRONG  evidence-pack build $1: expected a refusal naming '$2', got exit $rc" >&2
    printf '%s\n' "$out" | tail -8 >&2
    exit 1
  fi
}

build honest "$work/manifest.json" "$work/receipts.json" "$work/pack"
cases=$((cases + 1))
if [ "$rc" -ne 0 ]; then
  echo "WRONG  evidence-pack build honest: the real manifest and receipts were refused" >&2
  printf '%s\n' "$out" | tail -8 >&2
  exit 1
fi
python3 "$root/tooling/build-evidence-pack.py" --verify "$work/pack" >/dev/null \
  || { echo "WRONG  evidence-pack build honest: the pack that was built does not verify" >&2; exit 1; }

edit() {  # in out python-statements on d
  python3 - "$1" "$2" "$3" <<'PY'
import json, pathlib, sys
d = json.loads(pathlib.Path(sys.argv[1]).read_text())
exec(sys.argv[3], {'d': d})
pathlib.Path(sys.argv[2]).write_text(json.dumps(d, indent=2) + "\n")
PY
}

edit "$work/manifest.json" "$work/bad-digest.json" "d['sources'][0]['sha256'] = '0' * 64"
refused invalid-manifest 'candidate assurance manifest did not validate' "$work/bad-digest.json" "$work/receipts.json" "$work/out-invalid"
[ ! -e "$work/out-invalid" ] || { echo "WRONG  evidence-pack build: a pack was started for a manifest that does not validate" >&2; exit 1; }

edit "$work/receipts.json" "$work/receipts-schema.json" "d['schema_version'] = 2"
refused receipts-schema 'manifest and receipts must use schema version 1' "$work/manifest.json" "$work/receipts-schema.json" "$work/out-schema"

edit "$work/receipts.json" "$work/receipts-candidate.json" "d['candidate']['commit'] = '0' * 40"
refused receipts-candidate 'manifest and receipts name different candidates' "$work/manifest.json" "$work/receipts-candidate.json" "$work/out-candidate"
edit "$work/receipts.json" "$work/receipts-tree.json" "d['candidate']['tree'] = '0' * 40"
refused receipts-tree 'manifest and receipts name different candidates' "$work/manifest.json" "$work/receipts-tree.json" "$work/out-tree"

edit "$work/receipts.json" "$work/receipts-step.json" "d['checks'][0]['step_outcomes'][next(iter(d['checks'][0]['step_outcomes']))] = 'failure'"
refused receipts-step 'do not form one complete passing evidence set' "$work/manifest.json" "$work/receipts-step.json" "$work/out-step"

# Both documents validate on their own and disagree: one receipt's command text differs.
edit "$work/receipts.json" "$work/receipts-disagree.json" "d['checks'][0]['command'] = 'another-command'"
refused receipts-disagree 'do not form one complete passing evidence set: manifest and receipts disagree for check' "$work/manifest.json" "$work/receipts-disagree.json" "$work/out-disagree"

mkdir -p "$work/occupied"
printf 'x\n' > "$work/occupied/keep"
refused non-empty-output 'refusing non-empty pack output' "$work/manifest.json" "$work/receipts.json" "$work/occupied"
[ "$(cat "$work/occupied/keep")" = x ] && [ "$(ls "$work/occupied" | wc -l | tr -d ' ')" = 1 ] \
  || { echo "WRONG  evidence-pack build: a non-empty output directory was changed" >&2; exit 1; }

echo "build-evidence-pack-build-cases: a real pack builds and verifies; $((cases - 1)) refusals (invalid manifest, receipts of another schema or candidate, that fail, or that disagree with the manifest, a non-empty output) gave the expected result"
