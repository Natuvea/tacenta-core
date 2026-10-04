#!/usr/bin/env bash
# Negative control for `tooling/check-vectors-current.sh`: a committed vector that differs from the model's
# output must be refused, and the unchanged tree accepted.
#
# The case plants its change in a disposable worktree of the commit under test, with the model package's
# build directory linked in so that `lake exe genvectors` runs without a rebuild, flips one hex digit in one
# committed vector file and requires the check to fail and to name that file. Needs the model built. What is
# tested is the committed tree, as in `check-port-negatives.sh`.
set -euo pipefail

root="$(git rev-parse --show-toplevel)"
[ -d "$root/tacenta-model/.lake/build" ] || { echo "check-vectors-current cases: the model is not built; run 'lake build' in tacenta-model first" >&2; exit 1; }
work="$(mktemp -d)"
cleanup() { git -C "$root" worktree remove --force "$work/tree" >/dev/null 2>&1 || true; rm -rf "$work"; }
trap cleanup EXIT
git -C "$root" worktree add -q --detach "$work/tree" HEAD >/dev/null
tree="$work/tree"
ln -s "$root/tacenta-model/.lake" "$tree/tacenta-model/.lake"

run_check() {
  set +e
  out="$(cd "$tree" && bash tooling/check-vectors-current.sh 2>&1)"
  rc=$?
  set -e
}

run_check
if [ "$rc" -ne 0 ]; then
  echo "WRONG  vectors-current baseline: the unchanged tree was refused" >&2
  printf '%s\n' "$out" | tail -15 >&2
  exit 1
fi

# Flip the first hex digit of the first long hex string in the file.
target=tacenta-test-vectors/vectors/aead/aead-encrypt.json
python3 - "$tree/$target" <<'PY'
import pathlib, re, sys
path = pathlib.Path(sys.argv[1])
text = path.read_text()
match = re.search(r'"[0-9a-f]{32,}"', text)
if not match:
    raise SystemExit(f"control: no long hex string in {path}")
start = match.start() + 1
flipped = "0" if text[start] != "0" else "1"
path.write_text(text[:start] + flipped + text[start + 1:])
PY
# Committed, as it would be in CI: the check regenerates over the working tree, so an uncommitted change
# would be overwritten with the model's output and hidden.
git -C "$tree" -c user.name=control -c user.email=control@example.invalid commit -q -a --no-verify -m 'a changed committed vector'
run_check
if [ "$rc" -eq 0 ] || ! grep -qF "$target" <<<"$out" || ! grep -qF 'the committed vectors are not what the model generates' <<<"$out"; then
  echo "WRONG  vectors-current: a changed committed vector was not refused for that file (exit $rc)" >&2
  printf '%s\n' "$out" | tail -15 >&2
  exit 1
fi

echo "check-vectors-current cases: the unchanged tree was accepted and a changed committed vector was refused, naming its file"
