#!/usr/bin/env bash
set -euo pipefail

here="$(cd "$(dirname "$0")" && pwd)"
root="$(cd "$here/../.." && pwd)"
checker="$root/tooling/check-signoff.sh"
work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT
repo="$work/repo"

git init -q -b main "$repo"
git -C "$repo" config user.name 'Control Author'
git -C "$repo" config user.email 'control@example.invalid'
printf 'base\n' > "$repo/file"
git -C "$repo" add file
git -C "$repo" commit -q -s -m base
git -C "$repo" tag base

expect_fail() {
  local name="$1" needle="$2" base="$3" out rc
  set +e
  out="$(cd "$repo" && bash "$checker" "$base" 2>&1)"
  rc=$?
  set -e
  if [ "$rc" -eq 0 ] || ! printf '%s' "$out" | grep -qF -- "$needle"; then
    echo "WRONG  $name: expected refusal containing '$needle'" >&2
    printf '%s\n' "$out" >&2
    return 1
  fi
}

printf 'signed\n' >> "$repo/file"
git -C "$repo" commit -q -s -am signed
(cd "$repo" && bash "$checker" base) >/dev/null

expect_fail missing-base 'required base absent is missing' absent

printf 'unsigned\n' >> "$repo/file"
git -C "$repo" commit -q -am unsigned
expect_fail unsigned-commit 'is not signed off by its author' base

git -C "$repo" reset -q --hard HEAD^
git -C "$repo" switch -q -c side base
printf 'side\n' > "$repo/side"
git -C "$repo" add side
git -C "$repo" commit -q -s -m side
git -C "$repo" switch -q main
git -C "$repo" merge -q --no-ff side -m 'unsigned merge'
expect_fail unsigned-merge 'is not signed off by its author' base

echo 'check-signoff-cases: pass plus missing-base, unsigned-commit and unsigned-merge refusals gave the expected result'
