#!/usr/bin/env bash
# Exercise the standalone evidence-pack verifier's containment and digest checks.
set -euo pipefail

here="$(cd "$(dirname "$0")" && pwd)"
root="$(cd "$here/../.." && pwd)"
work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT

write_pack() {
  local directory="$1" path="$2"
  PYTHONPATH="$root/tooling" python3 - "$directory" "$path" "$root" <<'PY'
import hashlib, json, pathlib, sys
root = pathlib.Path(sys.argv[1])
listed_path = sys.argv[2]
from assurance_validation import REQUIRED_CHECKS
import importlib.util
def load_script(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module
manifest_module = load_script('manifest_builder', pathlib.Path(sys.argv[3]) / 'tooling/build-assurance-manifest.py')
pack_module = load_script('pack_builder', pathlib.Path(sys.argv[3]) / 'tooling/build-evidence-pack.py')
SOURCES = manifest_module.SOURCES
EXTRA = pack_module.EXTRA

candidate = {'commit': 'a' * 40, 'tree': 'b' * 40}
root.mkdir(parents=True, exist_ok=True)
entries = []
all_sources = sorted(set(SOURCES) | set(EXTRA))
for relative in all_sources:
    target = root / 'source' / relative
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text('candidate evidence: ' + relative + '\n')
    entries.append({'path': 'source/' + relative,
                    'sha256': hashlib.sha256(target.read_bytes()).hexdigest(),
                    'bytes': target.stat().st_size})

checks = []
for cid in sorted(REQUIRED_CHECKS):
    checks.append({'id': cid, 'classification': 'required', 'applicable': True,
                   'status': 'pass', 'command': cid + '-command',
                   'environment': {'event': 'test'},
                   'run': {'id': '1', 'attempt': '1',
                           'commit': candidate['commit'], 'tree': candidate['tree']}})
manifest_sources = []
for relative in SOURCES:
    target = root / 'source' / relative
    manifest_sources.append({'path': relative,
                             'sha256': hashlib.sha256(target.read_bytes()).hexdigest(),
                             'bytes': target.stat().st_size})
manifest = {'schema_version': 1,
            'identity': {'source_commit': candidate['commit'],
                         'source_tree': candidate['tree'],
                         'clean_tree': True},
            'sources': manifest_sources, 'checks': checks,
            'review_requirements': [{'type': 'independent-ledger-review',
                                     'status': 'pending'}]}
receipts = {'schema_version': 1, 'candidate': candidate, 'checks': checks}
(root / 'assurance-manifest.json').write_text(json.dumps(manifest, indent=2, sort_keys=True) + '\n')
(root / 'assurance-receipts.json').write_text(json.dumps(receipts, indent=2, sort_keys=True) + '\n')
for name in ('assurance-manifest.json', 'assurance-receipts.json'):
    target = root / name
    entries.append({'path': name,
                    'sha256': hashlib.sha256(target.read_bytes()).hexdigest(),
                    'bytes': target.stat().st_size})
if listed_path != 'source/evidence.txt':
    entries[0]['path'] = listed_path
root.joinpath('PACK-MANIFEST.json').write_text(json.dumps({
    'schema_version': 1, 'candidate': candidate, 'files': entries,
}, indent=2, sort_keys=True) + '\n')
PY
}

expect_fail() {
  local name="$1" needle="$2" directory="$3" out rc
  set +e
  out="$(python3 "$root/tooling/build-evidence-pack.py" --verify "$directory" 2>&1)"
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

write_pack "$work/pass" source/evidence.txt
python3 "$root/tooling/build-evidence-pack.py" --verify "$work/pass" >/dev/null
echo unlisted > "$work/pass/UNLISTED-SENTINEL.txt"
expect_fail extra 'pack contains unlisted files: UNLISTED-SENTINEL.txt' "$work/pass"
rm "$work/pass/UNLISTED-SENTINEL.txt"

ln -s source/evidence.txt "$work/pass/SYMLINK-SENTINEL.txt"
expect_fail symlink 'pack contains a symlink: SYMLINK-SENTINEL.txt' "$work/pass"
rm "$work/pass/SYMLINK-SENTINEL.txt"

cp -R "$work/pass" "$work/tampered"
printf 'changed\n' > "$work/tampered/source/ASSURANCE.md"
expect_fail tampered 'pack digest mismatch: source/ASSURANCE.md' "$work/tampered"

write_pack "$work/escape" ../source/evidence.txt
expect_fail escape 'invalid pack file path: ../source/evidence.txt' "$work/escape"

echo 'build-evidence-pack-cases: complete pass case and 4 pack refusals gave the expected result'
