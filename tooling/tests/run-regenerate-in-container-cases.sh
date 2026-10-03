#!/usr/bin/env bash
# Negative controls for tacenta-proofs/scripts/regenerate-in-container.sh.
#
# The script runs a container for an hour, so these cases run the part of it that decides the verdict, with no
# Docker and no network:
#
#   --compare DIR   a regenerated tree is compared with the tracked files. The unchanged copy must be accepted
#                   first; then one byte changed in each of the eleven generated Translation/Tacenta*.lean, a
#                   generated file missing, an extra Tacenta*.lean, a change to Cargo.lock and to an assembled
#                   unit crate must each be refused with the script's own diagnostic, and the files a run writes
#                   by design (cargo's target directory, LLBC files, the scratch output) must not be refused.
#   --check         a release archive whose SHA-256 is not the pinned one is refused before docker is started
#                   (a stub docker records any call), a digest in REPRODUCING.md or a release in run-aeneas.sh
#                   that the script does not hold is refused, an unknown argument is a usage error, and the
#                   checkout is not written to.
#
# What these do not show: that the container run reproduces the committed files. Only a run of the script does
# that, and its record is in REPRODUCING.md. The script is run by hand and is in no workflow; these cases are
# run by hand too.
#
# The tree under test is a copy of the tracked files as they are on disk now, made into a throwaway repository,
# so the controls do not depend on what is committed. No Lean toolchain is needed.
set -euo pipefail

root="$(git rev-parse --show-toplevel)"
work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT
tree="$work/tree"
regen="$work/regen"
script=tacenta-proofs/scripts/regenerate-in-container.sh
gen=tacenta-proofs/translation/Translation
cases=0
accepted=0

mkdir -p "$tree" "$regen" "$work/bin"
(cd "$root" && git ls-files -z | tar --null -T - -cf -) | tar -xf - -C "$tree"
(cd "$root" && git ls-files -z | tar --null -T - -cf -) | tar -xf - -C "$regen"
git -C "$tree" init -q
git -C "$tree" add -A
git -C "$tree" -c user.name=control -c user.email=control@example.invalid commit -q -m tree

# A docker that records its use and does nothing.
cat >"$work/bin/docker" <<STUB
#!/bin/sh
echo "\$@" >>"$work/docker-calls"
exit 99
STUB
chmod +x "$work/bin/docker"

reset_regen() { rm -rf "$regen" && mkdir -p "$regen" && (cd "$tree" && git ls-files -z | tar --null -T - -cf -) | tar -xf - -C "$regen"; }

# change_byte FILE: change one byte (the one at offset 200, or the last of a shorter file).
change_byte() {
  python3 - "$1" <<'PY'
import sys
path = sys.argv[1]
data = bytearray(open(path, "rb").read())
at = min(200, len(data) - 1)
data[at] = data[at] ^ 0x01
open(path, "wb").write(bytes(data))
PY
}

# expect_refused NAME NEEDLE COMMAND...: the command must exit nonzero and say NEEDLE.
expect_refused() {
  local name="$1" needle="$2" out rc
  shift 2
  set +e
  out="$("$@" 2>&1)"
  rc=$?
  set -e
  cases=$((cases + 1))
  if [ "$rc" -eq 0 ] || ! grep -qF -- "$needle" <<<"$out"; then
    echo "regenerate-in-container negative $name: expected a refusal containing '$needle', got exit $rc" >&2
    printf '%s\n' "$out" | head -20 >&2
    exit 1
  fi
}

compare() { bash "$tree/$script" --compare "$regen"; }

# 1. The unchanged copy is accepted, so a refusal below is the change and not the script.
out="$(compare)" || { echo "regenerate-in-container negative: the unchanged tree was refused" >&2; printf '%s\n' "$out" >&2; exit 1; }
grep -qF "PASS: all" <<<"$out" || { echo "regenerate-in-container negative: no PASS line for the unchanged tree" >&2; exit 1; }
accepted=$((accepted + 1))

# 2. One changed byte in each generated file.
for path in $(cd "$tree" && git ls-files "$gen/Tacenta*.lean"); do
  change_byte "$regen/$path"
  expect_refused "changed-byte-${path##*/}" "differs: $path" compare
  cp "$tree/$path" "$regen/$path"
done
[ "$(cd "$tree" && git ls-files "$gen/Tacenta*.lean" | wc -l | tr -d ' ')" -eq 11 ] || { echo "regenerate-in-container negative: expected eleven generated files" >&2; exit 1; }

# 3. A generated file missing, and one more than the tree has.
rm "$regen/$gen/TacentaSpqr.lean"
expect_refused "missing-generated-file" "missing: $gen/TacentaSpqr.lean" compare
cp "$tree/$gen/TacentaSpqr.lean" "$regen/$gen/TacentaSpqr.lean"
cp "$tree/$gen/TacentaSpqr.lean" "$regen/$gen/TacentaExtra.lean"
expect_refused "extra-generated-file" "$gen/TacentaExtra.lean" compare
rm "$regen/$gen/TacentaExtra.lean"

# 4. A file that is not a translation: the lockfile, and an assembled unit crate.
change_byte "$regen/tacenta-core/Cargo.lock"
expect_refused "changed-lockfile" "differs: tacenta-core/Cargo.lock" compare
cp "$tree/tacenta-core/Cargo.lock" "$regen/tacenta-core/Cargo.lock"
unit="$(cd "$tree" && git ls-files tacenta-core/session-unit | head -1)"
change_byte "$regen/$unit"
expect_refused "changed-assembled-unit" "differs: $unit" compare
cp "$tree/$unit" "$regen/$unit"

# 5. What a run writes by design is not a difference.
mkdir -p "$regen/tacenta-core/target/debug" "$regen/tacenta-proofs/Generated/aeneas-output" "$regen/tacenta-proofs/scripts/__pycache__"
echo x >"$regen/tacenta-core/target/debug/artifact"
echo x >"$regen/tacenta-core/tacenta_ratchet.llbc"
echo x >"$regen/tacenta-proofs/Generated/aeneas-output/TacentaRatchet.lean"
echo x >"$regen/tacenta-proofs/scripts/__pycache__/x.pyc"
out="$(compare)" || { echo "regenerate-in-container negative: the run's own scratch files were refused" >&2; printf '%s\n' "$out" >&2; exit 1; }
accepted=$((accepted + 1))
reset_regen

# 6. A release archive that is not the pinned one is refused, before docker is started.
printf 'not the archive\n' >"$work/junk.tar.gz"
expect_refused "wrong-archive-digest" "archive SHA-256 is" env PATH="$work/bin:$PATH" bash "$tree/$script" --check --archive "$work/junk.tar.gz"
: >"$work/empty.tar.gz"
expect_refused "empty-archive" "refusing to use it" env PATH="$work/bin:$PATH" bash "$tree/$script" --check --archive "$work/empty.tar.gz"
if [ -e "$work/docker-calls" ]; then
  echo "regenerate-in-container negative: docker was called before the archive was refused:" >&2
  cat "$work/docker-calls" >&2
  exit 1
fi
if [ -n "$(git -C "$tree" status --porcelain)" ]; then
  echo "regenerate-in-container negative: a refused --check wrote into the checkout:" >&2
  git -C "$tree" status --porcelain >&2
  exit 1
fi

# 7. A pin the script holds that the repository does not.
sed -i.bak 's/bc26c30daf92679b57c264c630710096bd9d4428e28795fe0638afdb0c2df65f/0000000000000000000000000000000000000000000000000000000000000000/' "$tree/tacenta-proofs/REPRODUCING.md"
expect_refused "digest-not-in-reproducing" "is not the one REPRODUCING.md states" env PATH="$work/bin:$PATH" bash "$tree/$script" --check --archive "$work/junk.tar.gz"
mv "$tree/tacenta-proofs/REPRODUCING.md.bak" "$tree/tacenta-proofs/REPRODUCING.md"
sed -i.bak 's/nightly-2026.07.22-b1214ca/nightly-2000.01.01-0000000/' "$tree/tacenta-proofs/scripts/run-aeneas.sh"
expect_refused "release-not-in-run-aeneas" "run-aeneas.sh does not pin" env PATH="$work/bin:$PATH" bash "$tree/$script" --check --archive "$work/junk.tar.gz"
mv "$tree/tacenta-proofs/scripts/run-aeneas.sh.bak" "$tree/tacenta-proofs/scripts/run-aeneas.sh"

# 8. Arguments.
expect_refused "unknown-argument" "usage:" bash "$tree/$script" --regenerate
expect_refused "no-mode" "usage:" bash "$tree/$script"
expect_refused "compare-without-directory" "usage:" bash "$tree/$script" --compare

echo "regenerate-in-container negatives: $accepted trees were accepted as intended and $cases cases were refused as intended"
