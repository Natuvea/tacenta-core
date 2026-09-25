#!/usr/bin/env bash
# Exercise the standalone evidence-pack verifier's containment and digest checks.
set -euo pipefail

here="$(cd "$(dirname "$0")" && pwd)"
root="$(cd "$here/../.." && pwd)"
work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT

write_pack() {
  local directory="$1" path="$2"
  mkdir -p "$directory/source"
  printf 'candidate evidence\n' > "$directory/source/evidence.txt"
  python3 - "$directory" "$path" <<'PY'
import hashlib, json, pathlib, sys
root, listed_path = map(pathlib.Path, sys.argv[1:])
source = root / 'source/evidence.txt'
root.joinpath('PACK-MANIFEST.json').write_text(json.dumps({
    'schema_version': 1,
    'candidate': {'commit': 'a' * 40, 'tree': 'b' * 40},
    'files': [{'path': str(listed_path), 'sha256': hashlib.sha256(source.read_bytes()).hexdigest(), 'bytes': source.stat().st_size}],
}, indent=2) + '\n')
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
printf 'changed\n' > "$work/tampered/source/evidence.txt"
expect_fail tampered 'pack digest mismatch: source/evidence.txt' "$work/tampered"

write_pack "$work/escape" ../source/evidence.txt
expect_fail escape 'invalid pack file path: ../source/evidence.txt' "$work/escape"

echo 'build-evidence-pack-cases: pass case and 4 pack refusals gave the expected result'
