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

echo "check-traceability-cases: pass case and 2 refusal cases gave the expected result"
