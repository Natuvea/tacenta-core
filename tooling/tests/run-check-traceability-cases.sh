#!/usr/bin/env bash
# Hold `tooling/check-traceability.py` to a few deliberate drift cases.
set -euo pipefail

here="$(cd "$(dirname "$0")" && pwd)"
root="$(cd "$here/../.." && pwd)"
checker="$root/tooling/check-traceability.py"

work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT

make_case() {
  local dst="$1"
  mkdir -p "$dst/tacenta-spec"
  cp -R "$root/tacenta-spec/security-properties" "$dst/tacenta-spec/"
  cp -R "$root/tacenta-spec/threat-model" "$dst/tacenta-spec/"
  mkdir -p "$dst/tacenta-core/src/sessions" "$dst/tacenta-core/src/primitives" "$dst/tacenta-core/wire/src" "$dst/tacenta-core/ratchet/src" "$dst/tacenta-core/braid/src" "$dst/tooling" "$dst/tacenta-model/Model"
  mkdir -p "$dst/tacenta-core/tests"
  mkdir -p "$dst/tacenta-model/Properties"
  mkdir -p "$dst/tacenta-proofs/Proofs" "$dst/tacenta-proofs/translation/Translation"
  mkdir -p "$dst/tacenta-test-vectors/vectors/primitives" "$dst/tacenta-test-vectors/vectors/aead" "$dst/tacenta-test-vectors/vectors/malformed-input"
  cp "$root/tacenta-core/src/sessions/mod.rs" "$dst/tacenta-core/src/sessions/mod.rs"
  cp "$root/tacenta-core/src/sessions/lifecycle.rs" "$dst/tacenta-core/src/sessions/lifecycle.rs"
  cp "$root/tacenta-core/AUTHENTICATION-BOUNDARY.md" "$dst/tacenta-core/AUTHENTICATION-BOUNDARY.md"
  cp "$root/tooling/check_authentication_boundary.py" "$dst/tooling/check_authentication_boundary.py"
  cp "$root/tacenta-core/src/primitives/aead.rs" "$dst/tacenta-core/src/primitives/aead.rs"
  cp "$root/tacenta-core/src/primitives/xeddsa.rs" "$dst/tacenta-core/src/primitives/xeddsa.rs"
  cp "$root/tacenta-core/src/primitives/dh.rs" "$dst/tacenta-core/src/primitives/dh.rs"
  cp "$root/tacenta-core/wire/src/lib.rs" "$dst/tacenta-core/wire/src/lib.rs"
  cp "$root/tacenta-core/ratchet/src/lib.rs" "$dst/tacenta-core/ratchet/src/lib.rs"
  cp "$root/tacenta-core/braid/src/lib.rs" "$dst/tacenta-core/braid/src/lib.rs"
  cp "$root/tacenta-core/braid/src/tests.rs" "$dst/tacenta-core/braid/src/tests.rs"
  cp "$root/tacenta-core/tests/full_session.rs" "$dst/tacenta-core/tests/full_session.rs"
  cp "$root/tacenta-core/tests/agreement_and_bounds.rs" "$dst/tacenta-core/tests/agreement_and_bounds.rs"
  cp "$root/tacenta-core/tests/replay_record.rs" "$dst/tacenta-core/tests/replay_record.rs"
  cp "$root/tacenta-core/tests/failed_decrypt_changes_nothing.rs" "$dst/tacenta-core/tests/failed_decrypt_changes_nothing.rs"
  cp "$root/tacenta-core/tests/post_quantum_stack.rs" "$dst/tacenta-core/tests/post_quantum_stack.rs"
  cp "$root/tacenta-core/tests/store_eviction.rs" "$dst/tacenta-core/tests/store_eviction.rs"
  cp "$root/tacenta-core/tests/fuzz.rs" "$dst/tacenta-core/tests/fuzz.rs"
  cp "$root/tacenta-core/tests/canonical_curve_keys.rs" "$dst/tacenta-core/tests/canonical_curve_keys.rs"
  cp "$root/tacenta-core/tests/canonicality.rs" "$dst/tacenta-core/tests/canonicality.rs"
  cp "$root/tacenta-model/Properties/Authentication.lean" "$dst/tacenta-model/Properties/Authentication.lean"
  cp "$root/tacenta-model/Model/Triple.lean" "$dst/tacenta-model/Model/Triple.lean"
  cp "$root/tacenta-model/Model/Braid.lean" "$dst/tacenta-model/Model/Braid.lean"
  cp "$root/tacenta-proofs/Proofs/SessionEstablishment.lean" "$dst/tacenta-proofs/Proofs/SessionEstablishment.lean"
  cp "$root/tacenta-proofs/Proofs/KeyErasure.lean" "$dst/tacenta-proofs/Proofs/KeyErasure.lean"
  cp "$root/tacenta-proofs/translation/Translation/SessionT3.lean" "$dst/tacenta-proofs/translation/Translation/SessionT3.lean"
  cp "$root/tacenta-proofs/translation/Translation/T3.lean" "$dst/tacenta-proofs/translation/Translation/T3.lean"
  cp "$root/tacenta-proofs/translation/Translation/UnitTripleT3.lean" "$dst/tacenta-proofs/translation/Translation/UnitTripleT3.lean"
  cp "$root/tacenta-proofs/translation/Translation/BraidT3.lean" "$dst/tacenta-proofs/translation/Translation/BraidT3.lean"
  cp "$root/tacenta-proofs/translation/Translation/WireT3.lean" "$dst/tacenta-proofs/translation/Translation/WireT3.lean"
  cp "$root/tacenta-proofs/translation/Translation/WireInitialT3.lean" "$dst/tacenta-proofs/translation/Translation/WireInitialT3.lean"
  cp "$root/tacenta-proofs/translation/Translation/WireBundleT3.lean" "$dst/tacenta-proofs/translation/Translation/WireBundleT3.lean"
  cp "$root/tacenta-proofs/CLAIMS.md" "$dst/tacenta-proofs/CLAIMS.md"
  cp "$root/tacenta-test-vectors/vectors/primitives/xeddsa.json" "$dst/tacenta-test-vectors/vectors/primitives/xeddsa.json"
  cp "$root/tacenta-test-vectors/vectors/aead/aead-decrypt.json" "$dst/tacenta-test-vectors/vectors/aead/aead-decrypt.json"
  cp "$root/tacenta-test-vectors/vectors/aead/aead-encrypt.json" "$dst/tacenta-test-vectors/vectors/aead/aead-encrypt.json"
  cp "$root/tacenta-test-vectors/vectors/malformed-input/composite-header-decode.json" "$dst/tacenta-test-vectors/vectors/malformed-input/composite-header-decode.json"
  cp "$root/tacenta-test-vectors/vectors/malformed-input/initial-message-decode.json" "$dst/tacenta-test-vectors/vectors/malformed-input/initial-message-decode.json"
  cp "$root/tacenta-test-vectors/vectors/malformed-input/prekey-bundle-decode.json" "$dst/tacenta-test-vectors/vectors/malformed-input/prekey-bundle-decode.json"
  cp "$root/tacenta-test-vectors/vectors/malformed-input/ratchet-reject.json" "$dst/tacenta-test-vectors/vectors/malformed-input/ratchet-reject.json"
}

expect_fail() {
  local name="$1"
  local expect="$2"
  set +e
  out="$(python3 "$checker" --root "$work/$name" 2>&1)"
  rc=$?
  set -e
  if [ "$rc" -eq 0 ]; then
    echo "WRONG  $name: expected refused ($expect), was accepted" >&2
    return 1
  fi
  if ! printf '%s' "$out" | grep -qF -- "$expect"; then
    echo "WRONG  $name: refused, but not for '$expect':" >&2
    printf '  %s\n' "$out" >&2
    return 1
  fi
}

make_case "$work/pass"
python3 "$checker" --root "$work/pass"

make_case "$work/missing-status-row"
python3 - "$work/missing-status-row/tacenta-spec/security-properties/limitations.md" <<'PY'
import pathlib, sys
path = pathlib.Path(sys.argv[1])
lines = path.read_text().splitlines()
path.write_text("\n".join(line for line in lines if not line.startswith("| REQ-AUTH-01: ")) + "\n")
PY
expect_fail "missing-status-row" "missing status-table row for REQ-AUTH-01"

make_case "$work/unknown-assumption"
python3 - "$work/unknown-assumption/tacenta-spec/security-properties/authentication.md" <<'PY'
import pathlib, sys
path = pathlib.Path(sys.argv[1])
text = path.read_text()
text = text.replace("ASM-03, ASM-07, ASM-14, ASM-19", "ASM-99, ASM-07, ASM-14, ASM-19", 1)
path.write_text(text)
PY
expect_fail "unknown-assumption" "requirements cite unknown assumption ASM-99"

make_case "$work/missing-evidence-index"
rm "$work/missing-evidence-index/tacenta-spec/security-properties/evidence-index.json"
expect_fail "missing-evidence-index" "missing evidence index"

make_case "$work/bad-theorem-reference"
python3 - "$work/bad-theorem-reference/tacenta-spec/security-properties/evidence-index.json" <<'PY'
import json, pathlib, sys
path = pathlib.Path(sys.argv[1])
data = json.loads(path.read_text())
entry = next(req for req in data["requirements"] if req["id"] == "REQ-AUTH-04")
entry["model_properties"][0]["theorem"] = "associatedData_missing"
path.write_text(json.dumps(data, indent=2) + "\n")
PY
expect_fail "bad-theorem-reference" "theorem associatedData_missing not found"

make_case "$work/bad-vector-case"
python3 - "$work/bad-vector-case/tacenta-spec/security-properties/evidence-index.json" <<'PY'
import json, pathlib, sys
path = pathlib.Path(sys.argv[1])
data = json.loads(path.read_text())
entry = next(req for req in data["requirements"] if req["id"] == "REQ-AUTH-01")
entry["vectors"][0]["case_ids"][0] = "missing-xeddsa-case"
path.write_text(json.dumps(data, indent=2) + "\n")
PY
expect_fail "bad-vector-case" "vector case missing-xeddsa-case not found"

make_case "$work/unknown-missing-evidence-reference"
python3 - "$work/unknown-missing-evidence-reference/tacenta-spec/security-properties/evidence-index.json" <<'PY'
import json, pathlib, sys
path = pathlib.Path(sys.argv[1])
data = json.loads(path.read_text())
entry = next(req for req in data["requirements"] if req["id"] == "REQ-AUTH-03")
entry["missing_evidence"][0]["references"] = ["LIM-99"]
path.write_text(json.dumps(data, indent=2) + "\n")
PY
expect_fail "unknown-missing-evidence-reference" "missing_evidence cites unknown reference LIM-99"

make_case "$work/missing-required-field"
python3 - "$work/missing-required-field/tacenta-spec/security-properties/evidence-index.json" <<'PY'
import json, pathlib, sys
path = pathlib.Path(sys.argv[1])
data = json.loads(path.read_text())
entry = next(req for req in data["requirements"] if req["id"] == "REQ-AUTH-04")
del entry["property"]
path.write_text(json.dumps(data, indent=2) + "\n")
PY
expect_fail "missing-required-field" "evidence entry missing required field property"

make_case "$work/missing-coverage"
python3 - "$work/missing-coverage/tacenta-spec/security-properties/evidence-index.json" <<'PY'
import json, pathlib, sys
path = pathlib.Path(sys.argv[1])
data = json.loads(path.read_text())
entry = next(req for req in data["requirements"] if req["id"] == "REQ-AUTH-04")
del entry["model_properties"][0]["coverage"]
path.write_text(json.dumps(data, indent=2) + "\n")
PY
expect_fail "missing-coverage" "model property in tacenta-proofs/Proofs/SessionEstablishment.lean has no coverage"

make_case "$work/non-list-evidence-field"
python3 - "$work/non-list-evidence-field/tacenta-spec/security-properties/evidence-index.json" <<'PY'
import json, pathlib, sys
path = pathlib.Path(sys.argv[1])
data = json.loads(path.read_text())
entry = next(req for req in data["requirements"] if req["id"] == "REQ-AUTH-04")
entry["tests"] = {}
path.write_text(json.dumps(data, indent=2) + "\n")
PY
expect_fail "non-list-evidence-field" "evidence field tests must be a list"

echo "check-traceability-cases: pass case and 9 refusal cases gave the expected result"
