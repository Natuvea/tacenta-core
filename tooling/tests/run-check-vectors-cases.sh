#!/usr/bin/env bash
# Hold the vector-schema checker to representative P9 mutation controls.
#
#   bash tooling/tests/run-check-vectors-cases.sh
#
# Each temporary root has the real checker, schemas, Rust runner dispatch
# source, and one valid known-answer file.  The mutations cover a schema
# refusal, a checker-only duplicate-ID refusal, and the fail-loudly rule for a
# schema constraint this validator does not implement.
set -euo pipefail

here="$(cd "$(dirname "$0")" && pwd)"
root="$(cd "$here/../.." && pwd)"
work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT

make_case() {
  local name="$1"
  local dst="$work/$name"
  mkdir -p "$dst/tooling" "$dst/tacenta-test-vectors/schema" \
    "$dst/tacenta-test-vectors/runners/rust/src" \
    "$dst/tacenta-test-vectors/vectors/primitives"
  cp "$root/tooling/check-vectors.py" "$dst/tooling/check-vectors.py"
  cp "$root/tacenta-test-vectors/schema/vector.schema.json" \
    "$root/tacenta-test-vectors/schema/ratchet-vector.schema.json" \
    "$dst/tacenta-test-vectors/schema/"
  cp "$root/tacenta-test-vectors/runners/rust/src/lib.rs" \
    "$dst/tacenta-test-vectors/runners/rust/src/lib.rs"
  cp "$root/tacenta-test-vectors/vectors/primitives/hmac-sha256.json" \
    "$dst/tacenta-test-vectors/vectors/primitives/hmac-sha256.json"
}

expect_fail() {
  local name="$1"
  local expect="$2"
  local out rc
  set +e
  out="$(python3 "$work/$name/tooling/check-vectors.py" 2>&1)"
  rc=$?
  set -e
  if [ "$rc" -eq 0 ]; then
    echo "WRONG  $name: expected refusal ($expect), was accepted" >&2
    return 1
  fi
  if ! printf '%s' "$out" | grep -qF -- "$expect"; then
    echo "WRONG  $name: refused, but not for '$expect':" >&2
    printf '  %s\n' "$out" >&2
    return 1
  fi
}

make_case pass
python3 "$work/pass/tooling/check-vectors.py"

make_case unexpected-field
python3 - "$work/unexpected-field/tacenta-test-vectors/vectors/primitives/hmac-sha256.json" <<'PY'
import json, pathlib, sys
path = pathlib.Path(sys.argv[1])
data = json.loads(path.read_text())
data["unexpected"] = True
path.write_text(json.dumps(data, indent=2) + "\n")
PY
expect_fail unexpected-field "unexpected field 'unexpected'"

make_case duplicate-id
python3 - "$work/duplicate-id/tacenta-test-vectors/vectors/primitives/hmac-sha256.json" <<'PY'
import json, pathlib, sys
path = pathlib.Path(sys.argv[1])
data = json.loads(path.read_text())
data["vectors"][1]["id"] = data["vectors"][0]["id"]
path.write_text(json.dumps(data, indent=2) + "\n")
PY
expect_fail duplicate-id "vector id 'rfc4231-tc2' is not unique in the file"

make_case unsupported-schema-keyword
python3 - "$work/unsupported-schema-keyword/tacenta-test-vectors/schema/vector.schema.json" <<'PY'
import json, pathlib, sys
path = pathlib.Path(sys.argv[1])
data = json.loads(path.read_text())
data["maxItems"] = 1
path.write_text(json.dumps(data, indent=2) + "\n")
PY
expect_fail unsupported-schema-keyword "schema uses keyword(s) this validator does not implement: maxItems"

# The prekey store's v1-v4 migration vectors carry the decoded fields and the
# v5 upgrade. A legacy vector is accepted only with both, and only when the
# upgrade is a longer v5 store that keeps the input's header; a current-version
# vector carries exactly one answer.
make_store_case() {
  local name="$1" version="$2" fields="$3" output="$4"
  make_case "$name"
  mkdir -p "$work/$name/tacenta-test-vectors/vectors/persistence"
  python3 - "$work/$name/tacenta-test-vectors/vectors/persistence/prekey-store-state.json" \
    "$version" "$fields" "$output" <<'PY'
import json, pathlib, sys
path, version, fields, output = pathlib.Path(sys.argv[1]), *sys.argv[2:5]
vector = {"id": "legacy", "comment": "case", "inputs": {"bytes": version + "aa" * 132 + "bb" * 4}}
if fields == "yes":
    vector["fields"] = {"next_id": "00000001"}
if output == "good":
    vector["output"] = "05" + "aa" * 132 + "bb" * 8
elif output == "garbage":
    vector["output"] = "05" + "00" * 136
elif output == "same-length":
    vector["output"] = "05" + "aa" * 132 + "bb" * 4
path.write_text(json.dumps({
    "schema_version": 1, "algorithm": "prekey-store-state", "source": "case",
    "vectors": [vector]}, indent=2) + "\n")
PY
}

make_store_case legacy-with-upgrade 04 yes good
python3 "$work/legacy-with-upgrade/tooling/check-vectors.py"

make_store_case legacy-without-upgrade 04 yes none
expect_fail legacy-without-upgrade "an accepted v1-v4 prekey store carries both"

make_store_case legacy-garbage-upgrade 03 yes garbage
expect_fail legacy-garbage-upgrade "the upgraded \`output\` is a v5 store that keeps the input's header"

make_store_case legacy-upgrade-not-longer 02 yes same-length
expect_fail legacy-upgrade-not-longer "is longer than the input"

make_store_case current-version-with-both 05 yes good
expect_fail current-version-with-both "a valid vector needs exactly one of"

echo 'check-vectors-cases: pass cases (plain, and a v1-v4 migration vector with its upgrade) and 7 refusal cases gave the expected result'
