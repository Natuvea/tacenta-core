#!/usr/bin/env bash
# Hold the vector-schema checker to representative P9 mutation controls.
#
#   bash tooling/tests/run-check-vectors-cases.sh
#
# Each temporary root has the real checker, schemas, Rust runner dispatch
# source, and one valid known-answer file.  The mutations cover a schema
# refusal, a checker-only duplicate-ID refusal, and the fail-loudly rule for a
# schema constraint this validator does not implement.  The group cases add
# the hosted-inventory files, whose shapes are closed in the checker itself:
# an unread field at the top of a case, inside a nested object, a binding
# with an extra field, and a refusal class the acceptance vectors do not name.
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

# The hosted-inventory group files: the real files, then one change each.
make_group_case() {
  local name="$1"
  make_case "$name"
  mkdir -p "$work/$name/tacenta-test-vectors/vectors/groups"
  cp "$root"/tacenta-test-vectors/vectors/groups/inventory-*.json \
    "$work/$name/tacenta-test-vectors/vectors/groups/"
}

edit_group_file() {
  local name="$1" file="$2" edit="$3"
  python3 - "$work/$name/tacenta-test-vectors/vectors/groups/$file" "$edit" <<'PY'
import json, pathlib, sys
path = pathlib.Path(sys.argv[1])
data = json.loads(path.read_text())
exec(sys.argv[2])
path.write_text(json.dumps(data, indent=2) + "\n")
PY
}

make_group_case group-pass
python3 "$work/group-pass/tooling/check-vectors.py"

make_group_case group-unread-field
edit_group_file group-unread-field inventory-acceptance-v1.json \
  'data["cases"][0]["note"] = "a field no runner reads"'
expect_fail group-unread-field "fields do not match the tacenta-inventory-acceptance-v1 schema"

make_group_case group-nested-unread-field
edit_group_file group-nested-unread-field inventory-acceptance-v1.json \
  'data["cases"][0]["policy"]["skip_freshness"] = True'
expect_fail group-nested-unread-field "policy: fields do not match the schema"

make_group_case group-binding-unread-field
edit_group_file group-binding-unread-field inventory-statements-v1.json \
  'data["cases"][1]["active"] = [{"device_id": 1, "identity_hex": "00" * 32, "capabilities": 1, "sort": 2}]'
expect_fail group-binding-unread-field "binding fields do not match the schema"

make_group_case group-unknown-refusal
edit_group_file group-unknown-refusal inventory-acceptance-v1.json \
  'data["cases"][0]["refusal"] = "unlucky"'
expect_fail group-unknown-refusal "refusal: neither null nor one of"

echo 'check-vectors-cases: pass cases and 7 refusal cases gave the expected result'

