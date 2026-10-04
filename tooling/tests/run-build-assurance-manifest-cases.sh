#!/usr/bin/env bash
# Exercise the assurance-manifest builder and its `--validate`: the receipt refusal
# paths, each field of a valid manifest changed once, and the clean-tree rule in
# a small candidate checkout made here.
set -euo pipefail

here="$(cd "$(dirname "$0")" && pwd)"
root="$(cd "$here/../.." && pwd)"
work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT
refusals=0
fixture="$root/tooling/tests/assurance-receipts-fixture.json"
export ASSURANCE_FIXTURE_COMMIT="$(git -C "$root" rev-parse HEAD)"
export ASSURANCE_FIXTURE_TREE="$(git -C "$root" rev-parse 'HEAD^{tree}')"

expect_fail() {
  local name="$1" needle="$2" out rc
  refusals=$((refusals + 1))
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

expect_validate_fail() {
  local name="$1" needle="$2" path="$3" out rc
  refusals=$((refusals + 1))
  set +e
  out="$(python3 "$root/tooling/build-assurance-manifest.py" --validate "$path" 2>&1)"
  rc=$?
  set -e
  if [ "$rc" -eq 0 ]; then
    echo "WRONG  $name: expected validation refusal" >&2
    return 1
  fi
  if ! printf '%s' "$out" | grep -qF -- "$needle"; then
    echo "WRONG  $name: missing diagnostic '$needle'" >&2
    printf '%s\n' "$out" >&2
    return 1
  fi
}

make_case() {
  local name="$1" program="$2" from="${3:-$fixture}"
  python3 - "$from" "$work/$name.json" "$program" <<'PY'
import json, pathlib, sys
source, output, program = map(pathlib.Path, sys.argv[1:])
data = json.loads(source.read_text())
data['candidate'] = {
    'commit': __import__('os').environ['ASSURANCE_FIXTURE_COMMIT'],
    'tree': __import__('os').environ['ASSURANCE_FIXTURE_TREE'],
}
import sys as _sys
_sys.path.insert(0, str(pathlib.Path(source).resolve().parents[1]))
from assurance_validation import expected_step_outcomes
table = expected_step_outcomes()
for check in data['checks']:
    check['run'].update(commit=data['candidate']['commit'], tree=data['candidate']['tree'])
    # The receipts a push to main would collect: the event, and success for
    # exactly the command steps the workflow runs for the check.
    check['environment'] = {'event': 'push'}
    check['step_outcomes'] = {step: 'success' for step in table[(check['id'], 'push')]}
exec(program.read_text(), {'data': data})
output.write_text(json.dumps(data, indent=2) + '\n')
PY
}

printf '%s\n' '# pass fixture is rebound to this checkout by make_case' > "$work/pass.py"
make_case pass "$work/pass.py"
python3 "$root/tooling/build-assurance-manifest.py" --allow-dirty --receipts "$work/pass.json" --output "$work/pass.out"
python3 -c 'import json, pathlib, sys; p=pathlib.Path(sys.argv[1]); d=json.loads(p.read_text()); d["identity"]["clean_tree"]=True; p.write_text(json.dumps(d, indent=2)+"\n")' "$work/pass.out"
python3 "$root/tooling/build-assurance-manifest.py" --validate "$work/pass.out" >/dev/null
cp "$work/pass.out" "$work/source-missing.out"
python3 -c 'import json, pathlib, sys; p=pathlib.Path(sys.argv[1]); d=json.loads(p.read_text()); d["sources"].pop(); p.write_text(json.dumps(d, indent=2)+"\n")' "$work/source-missing.out"
expect_validate_fail source-missing 'manifest source inventory does not match the repository-owned source set' "$work/source-missing.out"

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

printf "%s\n" "next(c for c in data['checks'] if c['id'] == 'rust')['step_outcomes']['rust_test'] = 'failure'" > "$work/failed-step.py"
make_case failed-step "$work/failed-step.py"
expect_fail failed-step 'receipt rust records command steps that did not succeed: rust_test=failure'

printf "%s\n" "del next(c for c in data['checks'] if c['id'] == 'vectors')['step_outcomes']['vectors_reader']" > "$work/missing-step.py"
make_case missing-step "$work/missing-step.py"
expect_fail missing-step 'receipt vectors does not record the command steps: vectors_reader'

printf "%s\n" "del next(c for c in data['checks'] if c['id'] == 'audit')['step_outcomes']" > "$work/no-outcomes.py"
make_case no-outcomes "$work/no-outcomes.py"
expect_fail no-outcomes 'receipt audit records no command step outcomes'

printf "%s\n" "next(c for c in data['checks'] if c['id'] == 'msrv')['step_outcomes']['msrv_extra'] = 'success'" > "$work/extra-step.py"
make_case extra-step "$work/extra-step.py"
expect_fail extra-step 'receipt msrv records steps the workflow does not run for push: msrv_extra'

printf "%s\n" "next(c for c in data['checks'] if c['id'] == 'checks')['environment']['event'] = 'pull_request'" > "$work/mixed-events.py"
make_case mixed-events "$work/mixed-events.py"
expect_fail mixed-events 'receipt checks records steps the workflow does not run for pull_request: checks_39'

printf "%s\n" "next(c for c in data['checks'] if c['id'] == 'rust')['run']['id'] = 'other-run'" > "$work/mixed-runs.py"
make_case mixed-runs "$work/mixed-runs.py"
expect_fail mixed-runs 'receipts come from more than one workflow run'

printf "%s\n" "data['checks'].append({'id': 'sign-off', 'classification': 'conditional', 'applicable': True, 'status': 'pass', 'command': 'tooling/check-signoff.sh', 'environment': {'event': 'push'}, 'run': {'id': 'fixture', 'commit': '0' * 40, 'tree': '0' * 40}, 'step_outcomes': {'signoff_check': 'success'}})" > "$work/foreign-signoff.py"
make_case foreign-signoff "$work/foreign-signoff.py"
expect_fail foreign-signoff 'receipt sign-off was not produced for the selected candidate'


# ---- the receipt set, one change at a time ----------------------------------
# The same validator reads the receipts when the builder builds and again, from
# the manifest, when `--validate` runs, so each refusal here protects both.
printf "%s\n" "data['candidate']['tree'] = '0' * 40" > "$work/foreign-tree.py"
make_case foreign-tree "$work/foreign-tree.py"
expect_fail foreign-tree 'receipts candidate commit/tree does not match selected source'

printf "%s\n" "next(c for c in data['checks'] if c['id'] == 'rust')['run']['tree'] = '0' * 40" > "$work/receipt-other-tree.py"
make_case receipt-other-tree "$work/receipt-other-tree.py"
expect_fail receipt-other-tree 'receipt rust was not produced for the selected candidate'

printf "%s\n" "next(c for c in data['checks'] if c['id'] == 'rust')['run']['commit'] = '0' * 40" > "$work/receipt-other-commit.py"
make_case receipt-other-commit "$work/receipt-other-commit.py"
expect_fail receipt-other-commit 'receipt rust was not produced for the selected candidate'

receipt_refusal() {
  local name="$1" needle="$2" program="$3"
  printf "%s\n" "$program" > "$work/$name.py"
  make_case "$name" "$work/$name.py"
  expect_fail "$name" "$needle"
}
receipt_refusal receipts-schema 'receipts schema_version must be 1' "data['schema_version'] = 2"
receipt_refusal checks-not-a-list 'receipts checks must be a list' "data['checks'] = {}"
receipt_refusal check-not-an-object 'receipt check must be an object' "data['checks'].append('rust')"
receipt_refusal check-without-command 'receipt check missing command' "del next(c for c in data['checks'] if c['id'] == 'rust')['command']"
receipt_refusal check-empty-command 'check rust has no command' "next(c for c in data['checks'] if c['id'] == 'rust')['command'] = ''"
receipt_refusal duplicate-check "duplicate or invalid check id 'rust'" "data['checks'].append(dict(next(c for c in data['checks'] if c['id'] == 'rust')))"
receipt_refusal invalid-classification 'check rust has invalid classification' "next(c for c in data['checks'] if c['id'] == 'rust')['classification'] = 'advisory'"
receipt_refusal applicable-not-boolean 'check rust applicable must be boolean' "next(c for c in data['checks'] if c['id'] == 'rust')['applicable'] = 'yes'"
receipt_refusal invalid-status 'check rust has invalid status' "next(c for c in data['checks'] if c['id'] == 'rust')['status'] = 'green'"
receipt_refusal environment-not-an-object 'check rust environment and run must be objects' "next(c for c in data['checks'] if c['id'] == 'rust')['environment'] = 'push'"
receipt_refusal optional-check-failed 'applicable non-required check docs is fail' "data['checks'].append({'id': 'docs', 'classification': 'optional', 'applicable': True, 'status': 'fail', 'command': 'docs', 'environment': {'event': 'push'}, 'run': {'id': 'fixture', 'commit': data['candidate']['commit'], 'tree': data['candidate']['tree']}})"
receipt_refusal optional-check-inapplicable-but-pass 'inapplicable check docs must be not_applicable' "data['checks'].append({'id': 'docs', 'classification': 'optional', 'applicable': False, 'status': 'pass', 'command': 'docs', 'environment': {'event': 'push'}, 'run': {'id': 'fixture'}})"

# ---- --validate, one change to a valid manifest at a time -------------------
# The manifest below is the pass case with `clean_tree` set. Each case changes
# one field of it and nothing else, and the diagnostic names that field, so a
# validator that stops looking at the field fails the case. A case that moves
# the identity moves it for the receipts too ("consistent"), so only the
# comparison with the selected commit and tree can refuse it.
tamper() {
  local name="$1" needle="$2" program="$3"
  printf '%s\n' "$program" > "$work/$name.py"
  python3 - "$work/pass.out" "$work/$name.out" "$work/$name.py" <<'PY'
import json, pathlib, sys
source, output, program = map(pathlib.Path, sys.argv[1:])
d = json.loads(source.read_text())
exec(program.read_text(), {'d': d})
output.write_text(json.dumps(d, indent=2) + '\n')
PY
  expect_validate_fail "$name" "$needle" "$work/$name.out"
}

tamper manifest-schema 'manifest schema_version must be 1' "d['schema_version'] = 2"
tamper manifest-extra-field 'manifest fields are not exactly' "d['approved'] = True"
tamper manifest-field-missing 'manifest fields are not exactly' "del d['sources']"
printf '[]\n' > "$work/manifest-array.out"
expect_validate_fail manifest-array 'manifest must be an object' "$work/manifest-array.out"
expect_validate_fail manifest-unreadable 'cannot read manifest' "$work/no-such-manifest.out"
tamper not-clean 'manifest does not assert a clean source tree' "d['identity']['clean_tree'] = False"
tamper clean-tree-truthy 'manifest does not assert a clean source tree' "d['identity']['clean_tree'] = 1"
tamper clean-tree-absent 'manifest does not assert a clean source tree' "del d['identity']['clean_tree']"
tamper identity-field-added 'manifest identity fields are not exactly' "d['identity']['signed_by'] = 'nobody'"
tamper identity-repository 'manifest names a repository other than' "d['identity']['repository'] = 'Someone/else'"
tamper identity-commit-short 'not a full git object id' "d['identity']['source_commit'] = d['identity']['source_commit'][:12]"
tamper identity-other-commit 'manifest candidate commit/tree does not match selected source' "d['identity']['source_commit'] = '0' * 40"
tamper identity-other-commit-consistent 'manifest candidate commit/tree does not match selected source' "d['identity']['source_commit'] = '0' * 40
for c in d['checks']:
    if 'commit' in c['run']: c['run']['commit'] = '0' * 40"
tamper identity-other-tree 'manifest candidate commit/tree does not match selected source' "d['identity']['source_tree'] = '0' * 40"
tamper identity-other-tree-consistent 'manifest candidate commit/tree does not match selected source' "d['identity']['source_tree'] = '0' * 40
for c in d['checks']:
    if 'tree' in c['run']: c['run']['tree'] = '0' * 40"
tamper generator-digest "manifest was not produced by this checkout's generator" "d['identity']['generator_sha256'] = '0' * 64"
tamper generator-path "manifest was not produced by this checkout's generator" "d['identity']['generator'] = 'tooling/other.py'"
tamper source-digest 'manifest source digest mismatch: ASSURANCE.md' "d['sources'][0]['sha256'] = '0' * 64"
tamper source-size 'manifest source digest mismatch: ASSURANCE.md' "d['sources'][0]['bytes'] += 1"
tamper source-entry-field-added 'manifest source entry is incomplete: ASSURANCE.md' "d['sources'][0]['note'] = 'x'"
tamper source-entry-no-digest 'manifest source entry is incomplete: ASSURANCE.md' "del d['sources'][0]['sha256']"
tamper source-added 'manifest source inventory does not match the repository-owned source set' "d['sources'].append({'path': 'README.md', 'sha256': '0' * 64, 'bytes': 0})"
tamper source-repeated 'manifest source inventory does not match the repository-owned source set' "d['sources'].append(dict(d['sources'][0]))"
tamper check-failed 'manifest checks are not a complete passing receipt set: required applicable check rust is fail' "next(c for c in d['checks'] if c['id'] == 'rust')['status'] = 'fail'"
tamper check-removed 'manifest checks are not a complete passing receipt set: missing required check receipts: proofs' "d['checks'] = [c for c in d['checks'] if c['id'] != 'proofs']"
tamper check-step-failed 'manifest checks are not a complete passing receipt set: receipt rust records command steps that did not succeed: rust_test=failure' "next(c for c in d['checks'] if c['id'] == 'rust')['step_outcomes']['rust_test'] = 'failure'"
tamper review-dropped 'manifest must retain exactly one pending independent review requirement' "d['review_requirements'] = []"
tamper review-accepted 'manifest must retain exactly one pending independent review requirement' "d['review_requirements'][0]['status'] = 'accepted'"
tamper review-retyped 'manifest must retain exactly one pending independent review requirement' "d['review_requirements'][0]['type'] = 'self-review'"
tamper review-second-entry 'manifest must retain exactly one pending independent review requirement' "d['review_requirements'].append({'type': 'independent-ledger-review', 'status': 'accepted'})"

# ---- a candidate checkout: the clean-tree rule ------------------------------
# The builder refuses a dirty tree unless told to allow it, and every case above
# passes `--allow-dirty` because the checkout this runner is in may be dirty. So
# the rule is tried in a small repository made here, with the builder and the
# source set copied in and one commit: clean, then dirty in each way the
# builder looks for. `.assurance/` is the one ignored path allowed, because the
# workflow writes the receipts there.
export PYTHONDONTWRITEBYTECODE=1
repo="$work/candidate"
python3 - "$root" "$repo" <<'PY'
import importlib.util, pathlib, shutil, subprocess, sys
root, dest = map(pathlib.Path, sys.argv[1:3])
sys.path.insert(0, str(root / "tooling"))
spec = importlib.util.spec_from_file_location("builder", root / "tooling/build-assurance-manifest.py")
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)
files = set(module.SOURCES) | {".gitignore"}
files |= {"tooling/" + p.name for p in (root / "tooling").iterdir() if p.is_file() and p.suffix in {".py", ".json"}}
for relative in sorted(files):
    target = dest / relative
    target.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(root / relative, target)
def git(*args):
    subprocess.run(["git", "-c", "user.name=case", "-c", "user.email=case@example.invalid", "-c", "commit.gpgsign=false", *args],
                   cwd=dest, check=True, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
git("init", "-q")
git("add", "-A")
git("commit", "-q", "-m", "candidate")
PY
repo_commit="$(git -C "$repo" rev-parse HEAD)"
repo_tree="$(git -C "$repo" rev-parse 'HEAD^{tree}')"
printf '%s\n' '# receipts for the candidate checkout' > "$work/repo-receipts.py"
ASSURANCE_FIXTURE_COMMIT="$repo_commit" ASSURANCE_FIXTURE_TREE="$repo_tree" make_case repo-receipts "$work/repo-receipts.py"

build_in_repo() {
  python3 "$repo/tooling/build-assurance-manifest.py" "$@" --receipts "$work/repo-receipts.json" --output "$work/repo-manifest.out" 2>&1
}
expect_dirty_refusal() {
  local name="$1" needle="$2" out rc
  refusals=$((refusals + 1))
  set +e
  out="$(build_in_repo)"
  rc=$?
  set -e
  if [ "$rc" -eq 0 ]; then
    echo "WRONG  $name: a dirty candidate was built without --allow-dirty" >&2
    return 1
  fi
  if ! printf '%s' "$out" | grep -qF -- "$needle"; then
    echo "WRONG  $name: missing diagnostic '$needle'" >&2
    printf '%s\n' "$out" >&2
    return 1
  fi
  rm -f "$work/repo-manifest.out"
}

# Clean: builds without --allow-dirty, asserts a clean tree, and validates.
build_in_repo >/dev/null
python3 - "$work/repo-manifest.out" "$repo_commit" "$repo_tree" <<'PY'
import json, sys
d = json.load(open(sys.argv[1]))
assert d["identity"]["clean_tree"] is True, d["identity"]
assert (d["identity"]["source_commit"], d["identity"]["source_tree"]) == tuple(sys.argv[2:4])
PY
python3 "$repo/tooling/build-assurance-manifest.py" --validate "$work/repo-manifest.out" >/dev/null

# The receipt workspace is ignored and allowed.
mkdir -p "$repo/.assurance/receipts"
echo '{}' > "$repo/.assurance/receipts/rust.json"
build_in_repo >/dev/null
python3 "$repo/tooling/build-assurance-manifest.py" --validate "$work/repo-manifest.out" >/dev/null
rm -rf "$repo/.assurance" "$work/repo-manifest.out"

echo '# edit' >> "$repo/ASSURANCE.md"
expect_dirty_refusal dirty-tracked 'candidate working tree is dirty: ASSURANCE.md'
git -C "$repo" checkout -q -- ASSURANCE.md

echo 'x' > "$repo/UNTRACKED-SENTINEL.txt"
expect_dirty_refusal dirty-untracked 'candidate working tree is dirty: UNTRACKED-SENTINEL.txt'
rm "$repo/UNTRACKED-SENTINEL.txt"

mkdir -p "$repo/target"
echo 'x' > "$repo/target/IGNORED-SENTINEL.txt"
expect_dirty_refusal dirty-ignored 'candidate working tree is dirty: target/'
rm -rf "$repo/target"

echo '# staged' >> "$repo/GAP-REGISTER.md"
git -C "$repo" add GAP-REGISTER.md
expect_dirty_refusal dirty-staged 'candidate working tree is dirty: GAP-REGISTER.md'
git -C "$repo" reset -q --hard

# A manifest built dirty with --allow-dirty says so, and --validate refuses it.
echo '# edit' >> "$repo/ASSURANCE.md"
python3 "$repo/tooling/build-assurance-manifest.py" --allow-dirty --receipts "$work/repo-receipts.json" --output "$work/repo-dirty.out" >/dev/null
python3 - "$work/repo-dirty.out" <<'PY'
import json, sys
assert json.load(open(sys.argv[1]))["identity"]["clean_tree"] is False
PY
set +e
dirty_validate="$(python3 "$repo/tooling/build-assurance-manifest.py" --validate "$work/repo-dirty.out" 2>&1)"
dirty_rc=$?
set -e
refusals=$((refusals + 1))
if [ "$dirty_rc" -eq 0 ] || ! printf '%s' "$dirty_validate" | grep -qF 'manifest does not assert a clean source tree'; then
  echo "WRONG  dirty-build-validates: $dirty_validate" >&2
  exit 1
fi
git -C "$repo" checkout -q -- ASSURANCE.md

# The command line.
set +e
both="$(python3 "$root/tooling/build-assurance-manifest.py" --validate "$work/pass.out" --output "$work/x" 2>&1)"
both_rc=$?
bare="$(python3 "$root/tooling/build-assurance-manifest.py" --receipts "$work/pass.json" 2>&1)"
bare_rc=$?
set -e
refusals=$((refusals + 2))
if [ "$both_rc" -eq 0 ] || ! printf '%s' "$both" | grep -qF -- '--validate cannot be combined with --receipts or --output'; then
  echo "WRONG  validate-with-build-arguments: $both" >&2
  exit 1
fi
if [ "$bare_rc" -eq 0 ] || ! printf '%s' "$bare" | grep -qF -- '--receipts and --output are required to build'; then
  echo "WRONG  build-without-output: $bare" >&2
  exit 1
fi

# The committed schema states the field names the validator holds, so that a
# reader of the schema is not told something the validator does not enforce.
python3 - "$root" <<'PY'
import importlib.util, json, pathlib, sys
root = pathlib.Path(sys.argv[1])
sys.path.insert(0, str(root / "tooling"))
spec = importlib.util.spec_from_file_location("builder", root / "tooling/build-assurance-manifest.py")
builder = importlib.util.module_from_spec(spec)
spec.loader.exec_module(builder)
schema = json.loads((root / "tooling/assurance-manifest.schema.json").read_text())
assert set(schema["required"]) == set(schema["properties"]) == builder.MANIFEST_FIELDS, "schema and validator disagree on the manifest fields"
identity = schema["properties"]["identity"]
assert set(identity["required"]) == set(identity["properties"]) == builder.IDENTITY_FIELDS, "schema and validator disagree on the identity fields"
assert identity["properties"]["repository"]["const"] == builder.REPOSITORY and identity["properties"]["generator"]["const"] == builder.GENERATOR
source = schema["properties"]["sources"]["items"]
assert set(source["required"]) == set(source["properties"]) == builder.SOURCE_FIELDS, "schema and validator disagree on the source fields"
assert schema["properties"]["review_requirements"]["items"]["const"] == builder.REVIEW_REQUIREMENTS[0]
assert schema["additionalProperties"] is False and identity["additionalProperties"] is False and source["additionalProperties"] is False
PY

echo "build-assurance-manifest-cases: pass case and $refusals refusals gave the expected result"
