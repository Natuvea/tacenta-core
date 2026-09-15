#!/usr/bin/env bash
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
root="$(cd "$here/../.." && pwd)"
work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT
mkdir -p "$work/pack"
python3 - "$work" <<'PY'
import hashlib, json, pathlib, sys
root = pathlib.Path(sys.argv[1]); pack = root / 'pack'
manifest = {'schema_version': 1, 'candidate': {'commit': 'a' * 40, 'tree': 'b' * 40}, 'files': []}
(pack / 'PACK-MANIFEST.json').write_text(json.dumps(manifest) + '\n')
receipt = {'schema_version': 1, 'candidate': manifest['candidate'], 'evidence_pack': {'manifest_sha256': hashlib.sha256((pack / 'PACK-MANIFEST.json').read_bytes()).hexdigest()}, 'reviewer': {'identity': 'reviewer', 'independence_statement': 'Did not author the ledger.'}, 'artifacts_read': ['tacenta-proofs/CLAIMS.md'], 'claims': [{'reference': 'Claims introduction', 'disposition': 'accepted', 'finding': ''}]}
(root / 'pass.json').write_text(json.dumps(receipt) + '\n')
PY
python3 "$root/tooling/check-ledger-review-receipt.py" --receipt "$work/pass.json" --pack "$work/pack" >/dev/null
python3 - "$work/pass.json" "$work/foreign.json" <<'PY'
import json, pathlib, sys
d=json.loads(pathlib.Path(sys.argv[1]).read_text()); d['candidate']['commit']='c'*40; pathlib.Path(sys.argv[2]).write_text(json.dumps(d))
PY
expect_fail() {
  local name="$1" needle="$2" out rc
  set +e
  out="$(python3 "$root/tooling/check-ledger-review-receipt.py" --receipt "$work/$name.json" --pack "$work/pack" 2>&1)"
  rc=$?
  set -e
  [ "$rc" -ne 0 ] && printf '%s' "$out" | grep -qF -- "$needle"
}
expect_fail foreign 'candidate does not match evidence pack'
python3 - "$work/pass.json" "$work/missing-reviewer.json" <<'PY'
import json, pathlib, sys
d=json.loads(pathlib.Path(sys.argv[1]).read_text()); d['reviewer']={}; pathlib.Path(sys.argv[2]).write_text(json.dumps(d))
PY
expect_fail missing-reviewer 'lacks reviewer identity or independence statement'
python3 - "$work/pass.json" "$work/wrong-pack.json" <<'PY'
import json, pathlib, sys
d=json.loads(pathlib.Path(sys.argv[1]).read_text()); d['evidence_pack']['manifest_sha256']='0'*64; pathlib.Path(sys.argv[2]).write_text(json.dumps(d))
PY
expect_fail wrong-pack 'does not bind the evidence-pack manifest'
echo 'check-ledger-review-receipt-cases: pass case and 3 receipt refusals gave the expected result'
