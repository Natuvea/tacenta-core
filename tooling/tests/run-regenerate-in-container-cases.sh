#!/usr/bin/env bash
# Negative controls for tacenta-proofs/scripts/regenerate-in-container.sh.
#
# The script runs a container for an hour, so these cases run everything that decides its verdict with no real
# container and no network:
#
#   --compare DIR   a tree is compared with the tracked files. The unchanged copy must be accepted first; then one
#                   byte changed in each of the eleven generated Translation/Tacenta*.lean, a generated file
#                   missing, an extra Tacenta*.lean, a change to Cargo.lock and to an assembled unit crate, a changed
#                   executable bit, a symlink and a directory where a file is tracked must each be refused with the
#                   script's own diagnostic; the files a run writes by design (cargo's target directory, LLBC
#                   files, the scratch output) must not be refused.
#   --check, before docker
#                   a release archive that is not the pinned one is refused before docker is started (a stub docker
#                   records any call), and so is a value that REPRODUCING.md or run-aeneas.sh does not state (the
#                   archive, image, rustup-init and channel manifest digests, the compiler line, the release name).
#   --check, past the archive check
#                   a stub docker answers `image inspect`, `pull`, `version` and `rm`, and on `run` copies the
#                   directory mounted at /in/src into the directory mounted at /out, as the container would, with an
#                   optional fault. That drives the script from the archive check to its exit status: an unchanged
#                   copy is accepted, and a changed byte, a directory, a symlink, a changed mode, an extra file, a
#                   failed `docker run`, a run that writes no tree and a comparison that crashes, leaves no result or
#                   covers the wrong number of files are each refused and never printed as PASS. The container name
#                   is unique per run, the image on the command line is the pinned digest, only the container this
#                   run started is removed, the checkout is not written to and the work directory is gone after every
#                   run.
#   inside the container
#                   the lines of the container script that check the architecture, the archive, rustup-init and the
#                   channel manifest digests, the channel and the compiler version must be present, and the script
#                   must parse. No stub can run them (they run apt, rustup and the release's tools), so this holds
#                   their presence and not their behaviour.
#
# What these do not show: that the container run reproduces the committed files. Only a run of the script does that,
# and its record is in REPRODUCING.md.
#
# The tree under test is a copy of the tracked files the cases need, as they are on disk now, made into a throwaway
# repository, so the controls do not depend on what is committed. Everything is created under $TMPDIR and only that is removed. No
# Lean toolchain is needed.
set -euo pipefail

root="$(git rev-parse --show-toplevel)"
work="$(mktemp -d "${TMPDIR:-/tmp}/tacenta-regen-cases.XXXXXX")"
case "$work" in */tacenta-regen-cases.*) ;; *) echo "regenerate-in-container negative: unexpected work directory $work" >&2; exit 1 ;; esac
trap 'rm -rf "$work"' EXIT
tree="$work/tree"
regen="$work/regen"
script=tacenta-proofs/scripts/regenerate-in-container.sh
gen=tacenta-proofs/translation/Translation
spqr="$gen/TacentaSpqr.lean"
cases=0
accepted=0

# The tracked files the cases need: the script, what it reads, the eleven generated files, the lockfile and one
# assembled unit crate. The comparison and the checks around it behave the same on this set as on the whole tree,
# and a run of the script on the whole tree is the recorded one.
mkdir -p "$tree" "$regen" "$work/bin" "$work/tmp"
subset=(tacenta-proofs/scripts/regenerate-in-container.sh tacenta-proofs/scripts/run-aeneas.sh tacenta-proofs/REPRODUCING.md
  'tacenta-proofs/translation/Translation/Tacenta*.lean' tacenta-core/Cargo.lock tacenta-core/session-unit README.md)
(cd "$root" && git ls-files -z -- "${subset[@]}" | tar --null -T - -cf -) | tar -xf - -C "$tree"
(cd "$root" && git ls-files -z -- "${subset[@]}" | tar --null -T - -cf -) | tar -xf - -C "$regen"
git -C "$tree" init -q
git -C "$tree" add -A
git -C "$tree" -c user.name=control -c user.email=control@example.invalid commit -q -m tree

sha256() { if command -v sha256sum >/dev/null 2>&1; then sha256sum "$1" | cut -d' ' -f1; else shasum -a 256 "$1" | cut -d' ' -f1; fi; }

# A docker that records its use and does nothing, for the cases that must be refused before docker is started.
cat >"$work/bin/docker" <<STUB
#!/bin/sh
echo "\$@" >>"$work/docker-calls"
exit 99
STUB
chmod +x "$work/bin/docker"

# A docker that behaves like one for --check, as far as the script can tell. FAULT is run with \$out and \$src set,
# after the tree is copied. RUNFAIL makes `run` exit with that status; NOTREE makes it write nothing.
mkdir -p "$work/stubbin"
cat >"$work/stubbin/docker" <<'STUB'
#!/bin/sh
echo "$*" | tr '\n' ' ' >>"$STUBLOG"
echo >>"$STUBLOG"
case "$1" in
  image|pull|rm) exit 0 ;;
  version) echo "stub linux/amd64"; exit 0 ;;
  run)
    src=""; out=""; cid=""; prev=""
    for a in "$@"; do
      case "$a" in
        *:/in/src:ro) src="${a%:/in/src:ro}" ;;
        *:/out) out="${a%:/out}" ;;
      esac
      [ "$prev" = "--cidfile" ] && cid="$a"
      prev="$a"
    done
    [ -n "${RUNFAIL:-}" ] && exit "$RUNFAIL"
    [ -n "$cid" ] && echo stub-container-id >"$cid"
    [ "${NOTREE:-0}" = 1 ] && exit 0
    mkdir -p "$out/tree" && cp -R "$src/." "$out/tree/"
    eval "${FAULT:-:}"
    exit 0 ;;
esac
exit 0
STUB
chmod +x "$work/stubbin/docker"

# Pythons that fail in the ways the comparison must not survive: it crashes, it leaves no result, it reports a
# count that is not the number of tracked files.
mkdir -p "$work/py-crash" "$work/py-empty" "$work/py-short"
printf '#!/bin/sh\nexit 1\n' >"$work/py-crash/python3"
printf '#!/bin/sh\nexit 0\n' >"$work/py-empty/python3"
printf '#!/bin/sh\nprintf "compared 3\\n" >"$5"\nexit 0\n' >"$work/py-short/python3"
chmod +x "$work/py-crash/python3" "$work/py-empty/python3" "$work/py-short/python3"

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

# expect_refused NAME NEEDLE COMMAND...: the command must exit nonzero, say NEEDLE and never print PASS.
expect_refused() {
  local name="$1" needle="$2" out rc
  shift 2
  set +e
  out="$("$@" 2>&1)"
  rc=$?
  set -e
  cases=$((cases + 1))
  if [ "$rc" -eq 0 ] || ! grep -qF -- "$needle" <<<"$out" || grep -qF "PASS:" <<<"$out"; then
    echo "regenerate-in-container negative $name: expected a refusal containing '$needle' and no PASS, got exit $rc" >&2
    printf '%s\n' "$out" | head -20 >&2
    exit 1
  fi
}

# expect_accepted NAME COMMAND...: the command must exit 0 and print PASS.
expect_accepted() {
  local name="$1" out
  shift
  out="$("$@" 2>&1)" || { echo "regenerate-in-container negative $name: refused" >&2; printf '%s\n' "$out" | head -20 >&2; exit 1; }
  grep -qF "PASS: all" <<<"$out" || { echo "regenerate-in-container negative $name: no PASS line" >&2; exit 1; }
  accepted=$((accepted + 1))
}

compare() { bash "$tree/$script" --compare "$regen"; }

# 1. The unchanged copy is accepted, so a refusal below is the change and not the script, and it says how many
# tracked paths differ from HEAD.
out="$(compare)" || { echo "regenerate-in-container negative: the unchanged tree was refused" >&2; printf '%s\n' "$out" >&2; exit 1; }
grep -qF "PASS: all" <<<"$out" || { echo "regenerate-in-container negative: no PASS line for the unchanged tree" >&2; exit 1; }
grep -qF "0 tracked path(s) differ from HEAD" <<<"$out" || { echo "regenerate-in-container negative: the PASS line does not count the paths that differ from HEAD" >&2; exit 1; }
accepted=$((accepted + 1))

# 2. One changed byte in each generated file.
for path in $(cd "$tree" && git ls-files "$gen/Tacenta*.lean"); do
  change_byte "$regen/$path"
  expect_refused "changed-byte-${path##*/}" "differs: $path" compare
  cp "$tree/$path" "$regen/$path"
done
[ "$(cd "$tree" && git ls-files "$gen/Tacenta*.lean" | wc -l | tr -d ' ')" -eq 11 ] || { echo "regenerate-in-container negative: expected eleven generated files" >&2; exit 1; }

# 3. A generated file missing, and one more than the tree has.
rm "$regen/$spqr"
expect_refused "missing-generated-file" "missing: $spqr" compare
cp "$tree/$spqr" "$regen/$spqr"
cp "$tree/$spqr" "$regen/$gen/TacentaExtra.lean"
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

# 5. The executable bit, a symlink and a directory where a file is tracked.
chmod +x "$regen/$spqr"
expect_refused "changed-mode" "mode: $spqr" compare
chmod -x "$regen/$spqr"
rm "$regen/$spqr" && ln -s "$tree/$spqr" "$regen/$spqr"
expect_refused "symlink-to-the-checkout" "symlink: $spqr" compare
rm "$regen/$spqr" && ln -s "$work/nowhere" "$regen/$spqr"
expect_refused "dangling-symlink" "symlink: $spqr" compare
rm "$regen/$spqr" && mkdir "$regen/$spqr"
expect_refused "directory-for-a-file" "not-a-file: $spqr" compare
rmdir "$regen/$spqr" && cp "$tree/$spqr" "$regen/$spqr"
out="$(compare)" || { echo "regenerate-in-container negative: the restored tree was refused" >&2; printf '%s\n' "$out" >&2; exit 1; }
accepted=$((accepted + 1))

# 6. What a run writes by design is not a difference.
mkdir -p "$regen/tacenta-core/target/debug" "$regen/tacenta-proofs/Generated/aeneas-output" "$regen/tacenta-proofs/scripts/__pycache__"
echo x >"$regen/tacenta-core/target/debug/artifact"
echo x >"$regen/tacenta-core/tacenta_ratchet.llbc"
echo x >"$regen/tacenta-proofs/Generated/aeneas-output/TacentaRatchet.lean"
echo x >"$regen/tacenta-proofs/scripts/__pycache__/x.pyc"
out="$(compare)" || { echo "regenerate-in-container negative: the run's own scratch files were refused" >&2; printf '%s\n' "$out" >&2; exit 1; }
accepted=$((accepted + 1))
reset_regen

# 7. A tree edited after HEAD is compared as edited, and the PASS line says how many paths differ from HEAD.
echo "# edited after HEAD" >>"$tree/README.md"
echo "# edited after HEAD" >>"$regen/README.md"
out="$(compare)" || { echo "regenerate-in-container negative: the edited tree was refused" >&2; printf '%s\n' "$out" >&2; exit 1; }
grep -qF "1 tracked path(s) differ from HEAD" <<<"$out" || { echo "regenerate-in-container negative: an edited tree is not counted in the PASS line" >&2; printf '%s\n' "$out" >&2; exit 1; }
accepted=$((accepted + 1))
git -C "$tree" checkout -q -- README.md
reset_regen

# 8. A release archive that is not the pinned one is refused, before docker is started.
printf 'not the archive\n' >"$work/junk.tar.gz"
expect_refused "wrong-archive-digest" "archive SHA-256 is" env PATH="$work/bin:$PATH" bash "$tree/$script" --check --archive "$work/junk.tar.gz"
: >"$work/empty.tar.gz"
expect_refused "empty-archive" "refusing to use it" env PATH="$work/bin:$PATH" bash "$tree/$script" --check --archive "$work/empty.tar.gz"
expect_refused "archive-is-not-a-file" "is not a file" env PATH="$work/bin:$PATH" bash "$tree/$script" --check --archive "$work/no-such-archive"
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

# 9. A value the script holds that the repository does not state.
doc="$tree/tacenta-proofs/REPRODUCING.md"
for pair in "archive digest|bc26c30daf92679b57c264c630710096bd9d4428e28795fe0638afdb0c2df65f" \
  "image digest|sha256:a853f94d226358a79c740cfc7bce0c289748f3fe3488d921d038ccd752c61b60" \
  "rustup-init digest|dda7234360b7f578ca8b0ddcb80145646fa61a67c1720a5abc7051b35c9fcb71" \
  "channel manifest digest|aaf1cb59b5996dd51831c9114b6e3a4a176e197851de91194b473117e142b935" \
  "compiler version line|rustc 1.98.0-nightly (14210df0e 2026-05-31)"; do
  what="${pair%%|*}"
  value="${pair#*|}"
  grep -qF -- "$value" "$doc" || { echo "regenerate-in-container negative: REPRODUCING.md does not state the $what, so the control cannot plant its absence" >&2; exit 1; }
  cp "$doc" "$work/REPRODUCING.md.keep"
  python3 - "$doc" "$value" <<'PY'
import sys
path, value = sys.argv[1:3]
text = open(path).read()
open(path, "w").write(text.replace(value, "0" * len(value)))
PY
  expect_refused "not-in-reproducing-$what" "is not the one REPRODUCING.md states" env PATH="$work/bin:$PATH" bash "$tree/$script" --check --archive "$work/junk.tar.gz"
  cp "$work/REPRODUCING.md.keep" "$doc"
done
sed -i.bak 's/nightly-2026.07.22-b1214ca/nightly-2000.01.01-0000000/' "$tree/tacenta-proofs/scripts/run-aeneas.sh"
expect_refused "release-not-in-run-aeneas" "run-aeneas.sh does not pin" env PATH="$work/bin:$PATH" bash "$tree/$script" --check --archive "$work/junk.tar.gz"
mv "$tree/tacenta-proofs/scripts/run-aeneas.sh.bak" "$tree/tacenta-proofs/scripts/run-aeneas.sh"
git -C "$tree" status --porcelain | grep -q . && { echo "regenerate-in-container negative: the pin cases left the tree changed" >&2; exit 1; }

# 10. Arguments.
expect_refused "unknown-argument" "usage:" bash "$tree/$script" --regenerate
expect_refused "no-mode" "usage:" bash "$tree/$script"
expect_refused "compare-without-directory" "usage:" bash "$tree/$script" --compare

# 11. --check past the archive check, with a stub docker. The junk archive becomes the pinned one: its digest is
# written into a throwaway copy of the script and of REPRODUCING.md, which are committed in the throwaway repository.
junk_sha="$(sha256 "$work/junk.tar.gz")"
sed -i.bak "s/bc26c30daf92679b57c264c630710096bd9d4428e28795fe0638afdb0c2df65f/$junk_sha/" "$tree/$script" "$doc"
rm "$tree/$script.bak" "$doc.bak"
git -C "$tree" add -A
git -C "$tree" -c user.name=control -c user.email=control@example.invalid commit -q -m "junk archive pinned"
tracked_total="$(git -C "$tree" ls-files | wc -l | tr -d ' ')"

# check VAR=value... COMMAND...: the command with a fresh stub log and a private TMPDIR.
stub_log="$work/stub.log"
check() {
  : >"$stub_log"
  env STUBLOG="$stub_log" TMPDIR="$work/tmp" "$@"
}
leftovers() { find "$work/tmp" -mindepth 1 | head -3; }

expect_accepted "stub-unchanged" check PATH="$work/stubbin:$PATH" bash "$tree/$script" --check --archive "$work/junk.tar.gz"
image_digest="$(grep -o 'ubuntu@sha256:[0-9a-f]\{64\}' "$tree/tacenta-proofs/REPRODUCING.md" | head -1)"
run_line="$(grep '^run ' "$stub_log")"
name1="$(grep -o -e '--name tacenta-regen-[0-9]*-[0-9]*' <<<"$run_line")" || { echo "regenerate-in-container negative: the container name is not unique per run: $run_line" >&2; exit 1; }
grep -qF -- "$image_digest sh -c" <<<"$run_line" || { echo "regenerate-in-container negative: docker run does not use the pinned image $image_digest" >&2; echo "$run_line" | cut -c1-300 >&2; exit 1; }
grep -qF -- "--platform linux/amd64" <<<"$run_line" || { echo "regenerate-in-container negative: docker run is not linux/amd64" >&2; exit 1; }
grep -q '^rm -f stub-container-id *$' "$stub_log" || { echo "regenerate-in-container negative: the container this run started was not removed by its id" >&2; cat "$stub_log" | cut -c1-200 >&2; exit 1; }
[ -z "$(leftovers)" ] || { echo "regenerate-in-container negative: the work directory was not removed after a pass" >&2; exit 1; }
expect_accepted "stub-unchanged-again" check PATH="$work/stubbin:$PATH" bash "$tree/$script" --check --archive "$work/junk.tar.gz"
name2="$(grep -o -e '--name tacenta-regen-[0-9]*-[0-9]*' "$stub_log")"
[ "$name1" != "$name2" ] || { echo "regenerate-in-container negative: two runs used the container name $name1" >&2; exit 1; }
# A relative --archive is read as a file, not as a docker volume name.
(cd "$work" && expect_accepted "stub-relative-archive" check PATH="$work/stubbin:$PATH" bash "$tree/$script" --check --archive junk.tar.gz)
accepted=$((accepted + 1))
grep -q -e " -v $work/junk.tar.gz:/in/aeneas.tar.gz:ro " "$stub_log" || grep -q -e " -v $(cd "$work" && pwd -P)/junk.tar.gz:/in/aeneas.tar.gz:ro " "$stub_log" || { echo "regenerate-in-container negative: a relative archive reached docker unresolved" >&2; cut -c1-300 "$stub_log" >&2; exit 1; }

expect_refused "stub-changed-byte" "differs: $spqr" check PATH="$work/stubbin:$PATH" FAULT='printf x >>"$out/tree/tacenta-proofs/translation/Translation/TacentaSpqr.lean"' bash "$tree/$script" --check --archive "$work/junk.tar.gz"
expect_refused "stub-directory-for-a-file" "not-a-file: tacenta-core/Cargo.lock" check PATH="$work/stubbin:$PATH" FAULT='rm "$out/tree/tacenta-core/Cargo.lock"; mkdir "$out/tree/tacenta-core/Cargo.lock"' bash "$tree/$script" --check --archive "$work/junk.tar.gz"
expect_refused "stub-symlink-to-the-checkout" "symlink: tacenta-core/Cargo.lock" check PATH="$work/stubbin:$PATH" FAULT='rm "$out/tree/tacenta-core/Cargo.lock"; ln -s "$src/tacenta-core/Cargo.lock" "$out/tree/tacenta-core/Cargo.lock"' bash "$tree/$script" --check --archive "$work/junk.tar.gz"
expect_refused "stub-changed-mode" "mode: $spqr" check PATH="$work/stubbin:$PATH" FAULT='chmod +x "$out/tree/tacenta-proofs/translation/Translation/TacentaSpqr.lean"' bash "$tree/$script" --check --archive "$work/junk.tar.gz"
expect_refused "stub-extra-file" "$gen/TacentaExtra.lean" check PATH="$work/stubbin:$PATH" FAULT='cp "$out/tree/tacenta-proofs/translation/Translation/TacentaSpqr.lean" "$out/tree/tacenta-proofs/translation/Translation/TacentaExtra.lean"' bash "$tree/$script" --check --archive "$work/junk.tar.gz"
expect_refused "stub-comparison-crashes" "did not run to the end" check PATH="$work/py-crash:$work/stubbin:$PATH" bash "$tree/$script" --check --archive "$work/junk.tar.gz"
expect_refused "stub-comparison-leaves-no-result" "left no result" check PATH="$work/py-empty:$work/stubbin:$PATH" bash "$tree/$script" --check --archive "$work/junk.tar.gz"
expect_refused "stub-comparison-covers-too-few" "covered 3 of $tracked_total" check PATH="$work/py-short:$work/stubbin:$PATH" bash "$tree/$script" --check --archive "$work/junk.tar.gz"
expect_refused "stub-container-run-fails" "container run failed (exit 3); nothing was compared" check PATH="$work/stubbin:$PATH" RUNFAIL=3 bash "$tree/$script" --check --archive "$work/junk.tar.gz"
expect_refused "stub-container-writes-no-tree" "nothing was compared" check PATH="$work/stubbin:$PATH" NOTREE=1 bash "$tree/$script" --check --archive "$work/junk.tar.gz"
# A run that cannot start (the name is taken) removes nothing: no container id was recorded, so no `docker rm`.
expect_refused "stub-name-in-use" "container run failed (exit 125)" check PATH="$work/stubbin:$PATH" RUNFAIL=125 bash "$tree/$script" --check --archive "$work/junk.tar.gz"
if grep -q '^rm ' "$stub_log"; then echo "regenerate-in-container negative: a run that never started a container removed one: $(grep '^rm ' "$stub_log")" >&2; exit 1; fi
[ -z "$(leftovers)" ] || { echo "regenerate-in-container negative: a refused run left its work directory behind" >&2; exit 1; }
if [ -n "$(git -C "$tree" status --porcelain)" ]; then
  echo "regenerate-in-container negative: a --check run wrote into the checkout:" >&2
  git -C "$tree" status --porcelain >&2
  exit 1
fi

# 12. The lines of the container script that no stub can run must be there, and the script must parse.
sed -n "/^read -r -d '' inner <<'INNER' || true\$/,/^INNER\$/p" "$tree/$script" | sed '1d;$d' >"$work/inner.sh"
[ -s "$work/inner.sh" ] || { echo "regenerate-in-container negative: the container script was not found in the script" >&2; exit 1; }
sh -n "$work/inner.sh" || { echo "regenerate-in-container negative: the container script does not parse" >&2; exit 1; }
while IFS= read -r line; do
  grep -qxF -- "$line" "$work/inner.sh" || { echo "regenerate-in-container negative: the container script lacks the line: $line" >&2; exit 1; }
  cases=$((cases + 1))
done <<'GUARDS'
[ "$(uname -m)" = x86_64 ] || { say "this container is not x86_64: $(uname -m)"; exit 1; }
echo "$ARCHIVE_SHA256  /in/aeneas.tar.gz" | sha256sum -c - >/dev/null || { say "archive digest mismatch inside the container"; exit 1; }
[ "$channel" = "$RUST_CHANNEL" ] || { say "the archive names toolchain '$channel', not '$RUST_CHANNEL'"; exit 1; }
echo "$RUSTUP_INIT_SHA256  /tmp/rustup-init" | sha256sum -c - >/dev/null || { say "rustup-init digest mismatch"; exit 1; }
echo "$RUST_MANIFEST_SHA256  /tmp/channel.toml" | sha256sum -c - >/dev/null || { say "toolchain manifest digest mismatch"; exit 1; }
[ "$actual" = "$RUSTC_VERSION_LINE" ] || { say "rustc is '$actual', not '$RUSTC_VERSION_LINE'"; exit 1; }
GUARDS

echo "regenerate-in-container negatives: $accepted trees and runs were accepted as intended and $cases cases were refused or held as intended"
