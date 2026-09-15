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
  cp -R "$root/tacenta-spec/protocol" "$dst/tacenta-spec/"
  mkdir -p "$dst/tacenta-core/src/sessions" "$dst/tacenta-core/src/primitives" "$dst/tacenta-core/wire/src" "$dst/tacenta-core/ratchet/src" "$dst/tacenta-core/braid/src" "$dst/tooling" "$dst/tacenta-model/Model"
  mkdir -p "$dst/tacenta-core/tests"
  mkdir -p "$dst/tacenta-core/spqr/src" "$dst/tacenta-core/triple/src"
  mkdir -p "$dst/tacenta-model/Properties"
  mkdir -p "$dst/tacenta-proofs/Proofs" "$dst/tacenta-proofs/translation/Translation"
  mkdir -p "$dst/tacenta-test-vectors/vectors/primitives" "$dst/tacenta-test-vectors/vectors/aead" "$dst/tacenta-test-vectors/vectors/malformed-input" "$dst/tacenta-test-vectors/vectors/post-quantum" "$dst/tacenta-test-vectors/vectors/persistence" "$dst/tacenta-test-vectors/vectors/session-establishment"
  cp "$root/tacenta-core/src/sessions/mod.rs" "$dst/tacenta-core/src/sessions/mod.rs"
  cp "$root/tacenta-core/src/sessions/lifecycle.rs" "$dst/tacenta-core/src/sessions/lifecycle.rs"
  cp "$root/tacenta-core/AUTHENTICATION-BOUNDARY.md" "$dst/tacenta-core/AUTHENTICATION-BOUNDARY.md"
  cp "$root/tooling/check_authentication_boundary.py" "$dst/tooling/check_authentication_boundary.py"
  cp "$root/tooling/check-constant-time-asm.sh" "$dst/tooling/check-constant-time-asm.sh"
  cp "$root/tacenta-core/src/primitives/aead.rs" "$dst/tacenta-core/src/primitives/aead.rs"
  cp "$root/tacenta-core/src/primitives/xeddsa.rs" "$dst/tacenta-core/src/primitives/xeddsa.rs"
  cp "$root/tacenta-core/src/primitives/dh.rs" "$dst/tacenta-core/src/primitives/dh.rs"
  cp "$root/tacenta-core/src/primitives/kem.rs" "$dst/tacenta-core/src/primitives/kem.rs"
  cp "$root/tacenta-core/wire/src/lib.rs" "$dst/tacenta-core/wire/src/lib.rs"
  cp "$root/tacenta-core/ratchet/src/lib.rs" "$dst/tacenta-core/ratchet/src/lib.rs"
  cp "$root/tacenta-core/braid/src/lib.rs" "$dst/tacenta-core/braid/src/lib.rs"
  cp "$root/tacenta-core/braid/src/tests.rs" "$dst/tacenta-core/braid/src/tests.rs"
  cp "$root/tacenta-core/spqr/src/lib.rs" "$dst/tacenta-core/spqr/src/lib.rs"
  cp "$root/tacenta-core/triple/src/lib.rs" "$dst/tacenta-core/triple/src/lib.rs"
  cp "$root/tacenta-core/tests/full_session.rs" "$dst/tacenta-core/tests/full_session.rs"
  cp "$root/tacenta-core/tests/agreement_and_bounds.rs" "$dst/tacenta-core/tests/agreement_and_bounds.rs"
  cp "$root/tacenta-core/tests/replay_record.rs" "$dst/tacenta-core/tests/replay_record.rs"
  cp "$root/tacenta-core/tests/failed_decrypt_changes_nothing.rs" "$dst/tacenta-core/tests/failed_decrypt_changes_nothing.rs"
  cp "$root/tacenta-core/tests/post_quantum_stack.rs" "$dst/tacenta-core/tests/post_quantum_stack.rs"
  cp "$root/tacenta-core/tests/handshake_to_ratchet.rs" "$dst/tacenta-core/tests/handshake_to_ratchet.rs"
  cp "$root/tacenta-core/tests/store_eviction.rs" "$dst/tacenta-core/tests/store_eviction.rs"
  cp "$root/tacenta-core/tests/fuzz.rs" "$dst/tacenta-core/tests/fuzz.rs"
  cp "$root/tacenta-core/tests/canonical_curve_keys.rs" "$dst/tacenta-core/tests/canonical_curve_keys.rs"
  cp "$root/tacenta-core/tests/canonicality.rs" "$dst/tacenta-core/tests/canonicality.rs"
  cp "$root/tacenta-core/tests/timing.rs" "$dst/tacenta-core/tests/timing.rs"
  cp "$root/tacenta-core/tests/session_lifecycle_property.rs" "$dst/tacenta-core/tests/session_lifecycle_property.rs"
  cp "$root/tacenta-core/tests/import_invariants.rs" "$dst/tacenta-core/tests/import_invariants.rs"
  cp "$root/tacenta-core/tests/session_persistence.rs" "$dst/tacenta-core/tests/session_persistence.rs"
  cp "$root/tacenta-model/Properties/Authentication.lean" "$dst/tacenta-model/Properties/Authentication.lean"
  cp "$root/tacenta-model/Properties/StateConsistency.lean" "$dst/tacenta-model/Properties/StateConsistency.lean"
  cp "$root/tacenta-model/Properties/Secrecy.lean" "$dst/tacenta-model/Properties/Secrecy.lean"
  cp "$root/tacenta-model/Properties/ForwardSecrecy.lean" "$dst/tacenta-model/Properties/ForwardSecrecy.lean"
  cp "$root/tacenta-model/Properties/PostCompromise.lean" "$dst/tacenta-model/Properties/PostCompromise.lean"
  cp "$root/tacenta-model/Model/Triple.lean" "$dst/tacenta-model/Model/Triple.lean"
  cp "$root/tacenta-model/Model/Braid.lean" "$dst/tacenta-model/Model/Braid.lean"
  cp "$root/tacenta-model/Model/SessionTrace.lean" "$dst/tacenta-model/Model/SessionTrace.lean"
  cp "$root/tacenta-proofs/Proofs/SessionEstablishment.lean" "$dst/tacenta-proofs/Proofs/SessionEstablishment.lean"
  cp "$root/tacenta-proofs/Proofs/KeyErasure.lean" "$dst/tacenta-proofs/Proofs/KeyErasure.lean"
  cp "$root/tacenta-proofs/Proofs/RatchetCorrectness.lean" "$dst/tacenta-proofs/Proofs/RatchetCorrectness.lean"
  cp "$root/tacenta-proofs/Proofs/MemorySafety.lean" "$dst/tacenta-proofs/Proofs/MemorySafety.lean"
  cp "$root/tacenta-proofs/Proofs/SparseRatchetCorrectness.lean" "$dst/tacenta-proofs/Proofs/SparseRatchetCorrectness.lean"
  cp "$root/tacenta-proofs/Proofs/SessionTrace.lean" "$dst/tacenta-proofs/Proofs/SessionTrace.lean"
  cp "$root/tacenta-proofs/translation/Translation/SessionT3.lean" "$dst/tacenta-proofs/translation/Translation/SessionT3.lean"
  cp "$root/tacenta-proofs/translation/Translation/T3.lean" "$dst/tacenta-proofs/translation/Translation/T3.lean"
  cp "$root/tacenta-proofs/translation/Translation/SpqrT3.lean" "$dst/tacenta-proofs/translation/Translation/SpqrT3.lean"
  cp "$root/tacenta-proofs/translation/Translation/UnitTripleT3.lean" "$dst/tacenta-proofs/translation/Translation/UnitTripleT3.lean"
  cp "$root/tacenta-proofs/translation/Translation/BraidT3.lean" "$dst/tacenta-proofs/translation/Translation/BraidT3.lean"
  cp "$root/tacenta-proofs/translation/Translation/WireT3.lean" "$dst/tacenta-proofs/translation/Translation/WireT3.lean"
  cp "$root/tacenta-proofs/translation/Translation/WireInitialT3.lean" "$dst/tacenta-proofs/translation/Translation/WireInitialT3.lean"
  cp "$root/tacenta-proofs/translation/Translation/WireBundleT3.lean" "$dst/tacenta-proofs/translation/Translation/WireBundleT3.lean"
  cp "$root/tacenta-proofs/CLAIMS.md" "$dst/tacenta-proofs/CLAIMS.md"
  cp "$root/tacenta-test-vectors/vectors/primitives/xeddsa.json" "$dst/tacenta-test-vectors/vectors/primitives/xeddsa.json"
  cp "$root/tacenta-test-vectors/vectors/aead/aead-decrypt.json" "$dst/tacenta-test-vectors/vectors/aead/aead-decrypt.json"
  cp "$root/tacenta-test-vectors/vectors/aead/aead-encrypt.json" "$dst/tacenta-test-vectors/vectors/aead/aead-encrypt.json"
  cp "$root/tacenta-test-vectors/vectors/post-quantum/triple.json" "$dst/tacenta-test-vectors/vectors/post-quantum/triple.json"
  cp "$root/tacenta-test-vectors/vectors/post-quantum/braid.json" "$dst/tacenta-test-vectors/vectors/post-quantum/braid.json"
  cp "$root/tacenta-test-vectors/vectors/post-quantum/spqr.json" "$dst/tacenta-test-vectors/vectors/post-quantum/spqr.json"
  cp "$root/tacenta-test-vectors/vectors/malformed-input/composite-header-decode.json" "$dst/tacenta-test-vectors/vectors/malformed-input/composite-header-decode.json"
  cp "$root/tacenta-test-vectors/vectors/malformed-input/initial-message-decode.json" "$dst/tacenta-test-vectors/vectors/malformed-input/initial-message-decode.json"
  cp "$root/tacenta-test-vectors/vectors/malformed-input/prekey-bundle-decode.json" "$dst/tacenta-test-vectors/vectors/malformed-input/prekey-bundle-decode.json"
  cp "$root/tacenta-test-vectors/vectors/malformed-input/ratchet-reject.json" "$dst/tacenta-test-vectors/vectors/malformed-input/ratchet-reject.json"
  cp "$root/tacenta-test-vectors/vectors/persistence/ratchet-state.json" "$dst/tacenta-test-vectors/vectors/persistence/ratchet-state.json"
  cp "$root/tacenta-test-vectors/vectors/persistence/sparse-ratchet-state.json" "$dst/tacenta-test-vectors/vectors/persistence/sparse-ratchet-state.json"
  cp "$root/tacenta-test-vectors/vectors/session-establishment/pqxdh-sk.json" "$dst/tacenta-test-vectors/vectors/session-establishment/pqxdh-sk.json"
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

make_case "$work/bad-conf-vector-case"
python3 - "$work/bad-conf-vector-case/tacenta-spec/security-properties/evidence-index.json" <<'PY'
import json, pathlib, sys
path = pathlib.Path(sys.argv[1])
data = json.loads(path.read_text())
entry = next(req for req in data["requirements"] if req["id"] == "REQ-CONF-05")
entry["vectors"][0]["case_ids"][0] = "missing-triple-combine-case"
path.write_text(json.dumps(data, indent=2) + "\n")
PY
expect_fail "bad-conf-vector-case" "vector case missing-triple-combine-case not found"

make_case "$work/missing-requirement-entry"
python3 - "$work/missing-requirement-entry/tacenta-spec/security-properties/evidence-index.json" <<'PY'
import json, pathlib, sys
path = pathlib.Path(sys.argv[1])
data = json.loads(path.read_text())
data["requirements"] = [entry for entry in data["requirements"] if entry["id"] != "REQ-PCS-03"]
path.write_text(json.dumps(data, indent=2) + "\n")
PY
expect_fail "missing-requirement-entry" "missing evidence entry for REQ-PCS-03"

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

make_case "$work/missing-requirement-status"
python3 - "$work/missing-requirement-status/tacenta-spec/security-properties/authentication.md" <<'PY'
import pathlib, sys
path = pathlib.Path(sys.argv[1])
text = path.read_text()
text = text.replace("- **Status: tested only.**", "- **Evidence:** tested only.", 1)
path.write_text(text)
PY
expect_fail "missing-requirement-status" "REQ-AUTH-01 has no '- **Status:**' line"

make_case "$work/missing-requirement-rests-on"
python3 - "$work/missing-requirement-rests-on/tacenta-spec/security-properties/authentication.md" <<'PY'
import pathlib, sys
path = pathlib.Path(sys.argv[1])
text = path.read_text()
text = text.replace("- **Rests on:** ASM-03, ASM-07, ASM-14, ASM-19.", "- **Dependencies:** ASM-03, ASM-07, ASM-14, ASM-19.", 1)
path.write_text(text)
PY
expect_fail "missing-requirement-rests-on" "REQ-AUTH-01 has no '- **Rests on:**' line"

make_case "$work/status-table-title-drift"
python3 - "$work/status-table-title-drift/tacenta-spec/security-properties/limitations.md" <<'PY'
import pathlib, sys
path = pathlib.Path(sys.argv[1])
text = path.read_text()
text = text.replace("| REQ-AUTH-01: prekey signatures are verified before use | Tested only |", "| REQ-AUTH-01: mutated title | Tested only |", 1)
path.write_text(text)
PY
expect_fail "status-table-title-drift" "REQ-AUTH-01 title differs"

make_case "$work/status-table-class-drift"
python3 - "$work/status-table-class-drift/tacenta-spec/security-properties/limitations.md" <<'PY'
import pathlib, sys
path = pathlib.Path(sys.argv[1])
text = path.read_text()
text = text.replace("| REQ-AUTH-01: prekey signatures are verified before use | Tested only |", "| REQ-AUTH-01: prekey signatures are verified before use | Assumed |", 1)
path.write_text(text)
PY
expect_fail "status-table-class-drift" "REQ-AUTH-01 status class differs"

make_case "$work/assumption-inverse-extra"
python3 - "$work/assumption-inverse-extra/tacenta-spec/threat-model/assumptions.md" <<'PY'
import pathlib, sys
path = pathlib.Path(sys.argv[1])
text = path.read_text()
text = text.replace("- **Relied on by:** REQ-AUTH-01, REQ-AUTH-03.", "- **Relied on by:** REQ-AUTH-01, REQ-AUTH-02, REQ-AUTH-03.", 1)
path.write_text(text)
PY
expect_fail "assumption-inverse-extra" "ASM-03 lists REQ-AUTH-02, but that requirement does not cite ASM-03"

make_case "$work/assumption-inverse-missing"
python3 - "$work/assumption-inverse-missing/tacenta-spec/threat-model/assumptions.md" <<'PY'
import pathlib, sys
path = pathlib.Path(sys.argv[1])
text = path.read_text()
text = text.replace("- **Relied on by:** REQ-AUTH-01, REQ-AUTH-03.", "- **Relied on by:** REQ-AUTH-01.", 1)
path.write_text(text)
PY
expect_fail "assumption-inverse-missing" "ASM-03 is cited by REQ-AUTH-03 but its relied-on list omits it"

for kind in LIM ADV AS EX; do
  make_case "$work/unknown-$kind-reference"
  case "$kind" in
    LIM) path="$work/unknown-$kind-reference/tacenta-spec/security-properties/limitations.md" ;;
    *) path="$work/unknown-$kind-reference/tacenta-spec/threat-model/assumptions.md" ;;
  esac
  printf '\nP9 mutation reference: %s-99.\n' "$kind" >> "$path"
  expect_fail "unknown-$kind-reference" "references unknown identifier $kind-99"
done

make_case "$work/missing-invariant-id"
python3 - "$work/missing-invariant-id/tacenta-spec/security-properties/evidence-index.json" <<'PY'
import json, pathlib, sys
path = pathlib.Path(sys.argv[1])
data = json.loads(path.read_text())
del data["invariants"][0]["id"]
path.write_text(json.dumps(data, indent=2) + "\n")
PY
expect_fail "missing-invariant-id" "invariant has invalid id None"

make_case "$work/duplicate-invariant-id"
python3 - "$work/duplicate-invariant-id/tacenta-spec/security-properties/evidence-index.json" <<'PY'
import json, pathlib, sys
path = pathlib.Path(sys.argv[1])
data = json.loads(path.read_text())
data["invariants"][1]["id"] = data["invariants"][0]["id"]
path.write_text(json.dumps(data, indent=2) + "\n")
PY
expect_fail "duplicate-invariant-id" "duplicate invariant id INV-AUTH-COMMIT"

make_case "$work/unknown-invariant-requirement"
python3 - "$work/unknown-invariant-requirement/tacenta-spec/security-properties/evidence-index.json" <<'PY'
import json, pathlib, sys
path = pathlib.Path(sys.argv[1])
data = json.loads(path.read_text())
data["invariants"][0]["requirements"] = ["REQ-AUTH-99"]
path.write_text(json.dumps(data, indent=2) + "\n")
PY
expect_fail "unknown-invariant-requirement" "INV-AUTH-COMMIT cites unknown requirement REQ-AUTH-99"

echo "check-traceability-cases: pass case and 22 refusal cases gave the expected result"
