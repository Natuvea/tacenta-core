#!/usr/bin/env bash
# Negative controls for the three CI installers that check what they fetch:
#
#   tooling/install-elan.sh           the elan archive matches ELAN_SHA256 before its installer runs
#   tooling/install-actionlint.sh     the actionlint archive matches its pinned digest before it is unpacked
#   tooling/seed-lake-packages.sh     a Lake dependency is cloned at the revision the manifest pins
#
# Each ran in CI for every job and none had a case that showed the check refusing. They need the network,
# so each case replaces `curl` with a stub that serves a local archive, and replaces `flock` (absent on
# macOS) and `sha256sum` (absent on macOS) with stubs, then runs the real script against the stubs. A
# wrong digest must stop the script before the installer inside the archive runs, which the archive proves
# by touching a sentinel file when it runs; a digest that matches must run it; an elan already at the pinned
# release must not fetch at all.
#
# What this does not show: that the digests pinned in the scripts and in the workflow are the digests of the
# real releases. Only a run that downloads them shows that, and the hosted `checks` and `proofs` jobs do.
set -euo pipefail

# The hosted job exports the pinned version and digest to every step. A case that sets only one of the two
# must see the other unset, or the 'no version' and 'no digest' cases pass for the caller's environment.
unset ELAN_VERSION ELAN_SHA256

root="$(cd "$(dirname "$0")/../.." && pwd)"
work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT
cases=0
bin="$work/bin"
mkdir -p "$bin"

cat >"$bin/curl" <<'STUB'
#!/usr/bin/env bash
out=""
url=""
while [ $# -gt 0 ]; do
  case "$1" in
    -o) out="$2"; shift ;;
    -*) ;;
    *) url="$1" ;;
  esac
  shift
done
echo "$url" >> "$STUB_URLS"
cp "$STUB_ARCHIVE" "$out"
STUB
cat >"$bin/flock" <<'STUB'
#!/usr/bin/env bash
echo "flock $*" >> "${STUB_FLOCK:-/dev/null}"
exit 0
STUB
cat >"$bin/sha256sum" <<'STUB'
#!/usr/bin/env bash
if [ "$1" = "-c" ]; then
  read -r want file
  got="$(shasum -a 256 "$file" | awk '{print $1}')"
  if [ "$want" = "$got" ]; then echo "$file: OK"; else echo "$file: FAILED" >&2; exit 1; fi
else
  exec shasum -a 256 "$@"
fi
STUB
chmod +x "$bin"/*

fail_case() {
  echo "WRONG  $1" >&2
  shift
  [ $# -eq 0 ] || printf '%s\n' "$@" >&2
  exit 1
}

# expect <name> <want: 0|nonzero> <needle> <script> [args...]: the environment is already exported by the caller.
expect() {
  local name="$1" want="$2" needle="$3" out rc
  shift 3
  set +e
  out="$(PATH="$bin:$PATH" "$@" 2>&1)"
  rc=$?
  set -e
  cases=$((cases + 1))
  if { [ "$want" = 0 ] && [ "$rc" -ne 0 ]; } || { [ "$want" != 0 ] && [ "$rc" -eq 0 ]; } || ! grep -qF -- "$needle" <<<"$out"; then
    fail_case "$name: expected exit $want and '$needle', got exit $rc" "$out"
  fi
}

# ---- elan -------------------------------------------------------------------------------------------------
elan_src="$work/elan-src"
mkdir -p "$elan_src"
cat >"$elan_src/elan-init" <<'STUB'
#!/usr/bin/env bash
echo "ran $*" > "$STUB_SENTINEL"
STUB
chmod +x "$elan_src/elan-init"
tar czf "$work/elan.tar.gz" -C "$elan_src" elan-init
good="$(shasum -a 256 "$work/elan.tar.gz" | awk '{print $1}')"
wrong='0000000000000000000000000000000000000000000000000000000000000000'
export STUB_ARCHIVE="$work/elan.tar.gz" STUB_URLS="$work/urls" STUB_SENTINEL="$work/sentinel" STUB_FLOCK="$work/flock"
installer="$root/tooling/install-elan.sh"

fresh_home() { rm -rf "$work/home" "$work/urls" "$work/sentinel" "$work/flock" "$work/ghpath"; mkdir -p "$work/home"; : > "$work/urls"; : > "$work/flock"; }

fresh_home
HOME="$work/home" ELAN_VERSION=v4.2.4 ELAN_SHA256="$good" GITHUB_PATH="$work/ghpath" expect 'elan: the right digest installs' 0 'elan v4.2.4 installed' bash "$installer"
[ -f "$work/sentinel" ] || fail_case 'elan: the installer inside the archive did not run for a matching digest'
# The installer is run as the script says: no default toolchain (the Lake packages' lean-toolchain files choose),
# no change to the shell profile, under the lock the second job on the self-hosted runner waits on, and the
# result on the runner's path.
[ "$(cat "$work/sentinel")" = 'ran -y --no-modify-path --default-toolchain none' ] \
  || fail_case 'elan: the installer inside the archive was not run with the arguments the script gives it' "$(cat "$work/sentinel")"
[ "$(wc -l < "$work/flock" | tr -d ' ')" = 1 ] || fail_case 'elan: the install did not take the lock' "$(cat "$work/flock")"
case "$(tail -n 1 "$work/ghpath")" in */.elan/bin) ;; *) fail_case 'elan: GITHUB_PATH does not end with the elan bin directory' "$(cat "$work/ghpath" 2>&1)" ;; esac
grep -qx 'https://github.com/leanprover/elan/releases/download/v4.2.4/elan-x86_64-unknown-linux-gnu.tar.gz' "$work/urls" \
  || fail_case 'elan: the archive was not fetched from the pinned release tag' "$(cat "$work/urls")"

fresh_home
HOME="$work/home" ELAN_VERSION=v4.2.4 ELAN_SHA256="$wrong" expect 'elan: a wrong digest is refused' nonzero 'did not match ELAN_SHA256; refusing to run it' bash "$installer"
[ ! -f "$work/sentinel" ] || fail_case 'elan: the installer ran although the digest did not match'

# The digest names a different archive from the one served: one byte appended.
fresh_home
cp "$work/elan.tar.gz" "$work/elan-tampered.tar.gz"
printf 'x' >> "$work/elan-tampered.tar.gz"
STUB_ARCHIVE="$work/elan-tampered.tar.gz" HOME="$work/home" ELAN_VERSION=v4.2.4 ELAN_SHA256="$good" \
  expect 'elan: a changed archive is refused' nonzero 'did not match ELAN_SHA256; refusing to run it' bash "$installer"
[ ! -f "$work/sentinel" ] || fail_case 'elan: the installer ran although the archive was changed'

# Already at the pinned release: nothing is fetched and nothing runs.
fresh_home
mkdir -p "$work/home/.elan/bin"
printf '#!/usr/bin/env bash\necho "elan 4.2.4 (stub)"\n' > "$work/home/.elan/bin/elan"
chmod +x "$work/home/.elan/bin/elan"
HOME="$work/home" ELAN_VERSION=v4.2.4 ELAN_SHA256="$wrong" expect 'elan: the pinned release already present is left alone' 0 'already installed' bash "$installer"
[ ! -s "$work/urls" ] && [ ! -f "$work/sentinel" ] || fail_case 'elan: it fetched or installed although the pinned release was present'
# A different release present is not the pinned one.
printf '#!/usr/bin/env bash\necho "elan 4.1.0 (stub)"\n' > "$work/home/.elan/bin/elan"
HOME="$work/home" ELAN_VERSION=v4.2.4 ELAN_SHA256="$wrong" expect 'elan: another release present is not the pinned one' nonzero 'did not match ELAN_SHA256' bash "$installer"

# The pin is the tag and the digest together, and both are required.
fresh_home
HOME="$work/home" ELAN_SHA256="$good" expect 'elan: no version is refused' nonzero 'set ELAN_VERSION' bash "$installer"
HOME="$work/home" ELAN_VERSION=v4.2.4 expect 'elan: no digest is refused' nonzero 'set ELAN_SHA256' bash "$installer"
# The digest is required even when the pinned release is already installed: the pin is the tag and the digest
# together, and a workflow that lost its digest must not pass on a runner that happens to hold the release.
mkdir -p "$work/home/.elan/bin"
printf '#!/usr/bin/env bash\necho "elan 4.2.4 (stub)"\n' > "$work/home/.elan/bin/elan"
chmod +x "$work/home/.elan/bin/elan"
HOME="$work/home" ELAN_VERSION=v4.2.4 expect 'elan: no digest is refused even when the pinned release is installed' nonzero 'set ELAN_SHA256' bash "$installer"

# ---- actionlint ---------------------------------------------------------------------------------------------
act_src="$work/act-src"
mkdir -p "$act_src"
printf 'not a release\n' > "$act_src/README"
tar czf "$work/actionlint.tar.gz" -C "$act_src" README
dest="$work/actionlint-bin"
expect 'actionlint: no destination is refused' nonzero 'usage:' bash "$root/tooling/install-actionlint.sh"
STUB_ARCHIVE="$work/actionlint.tar.gz" STUB_URLS="$work/urls" \
  expect 'actionlint: an archive with the wrong digest is refused' nonzero 'SHA-256 mismatch' bash "$root/tooling/install-actionlint.sh" "$dest"
[ ! -e "$dest/README" ] || fail_case 'actionlint: an archive with the wrong digest was unpacked'
printf '#!/usr/bin/env bash\ncase "$1" in -s) echo Plan9 ;; -m) echo mips ;; *) echo Plan9 ;; esac\n' > "$bin/uname"
chmod +x "$bin/uname"
expect 'actionlint: an unsupported platform is refused' nonzero 'unsupported platform' bash "$root/tooling/install-actionlint.sh" "$dest"
rm "$bin/uname"
# A digest that matches in every digit but the last is not a match. The script is copied with the archive's own
# digest, last hex digit changed, written in place of the digests it pins.
archive_digest="$(shasum -a 256 "$work/actionlint.tar.gz" | awk '{print $1}')"
last="${archive_digest#"${archive_digest%?}"}"
if [ "$last" = 0 ]; then other=1; else other=0; fi
near="${archive_digest%?}$other"
python3 - "$root/tooling/install-actionlint.sh" "$work/install-actionlint-near.sh" "$near" <<'PY'
import pathlib, re, sys
text = pathlib.Path(sys.argv[1]).read_text()
text, n = re.subn(r'digest="[0-9a-f]{64}"', 'digest="%s"' % sys.argv[3], text)
if n != 2:
    raise SystemExit("control: expected two pinned digests, found %d" % n)
pathlib.Path(sys.argv[2]).write_text(text)
PY
rm -rf "$dest"
STUB_ARCHIVE="$work/actionlint.tar.gz" STUB_URLS="$work/urls" \
  expect 'actionlint: a digest that differs in its last digit is refused' nonzero 'SHA-256 mismatch' bash "$work/install-actionlint-near.sh" "$dest"
[ ! -e "$dest/README" ] || fail_case 'actionlint: an archive whose digest differs in the last digit was unpacked'

# ---- seed-lake-packages ----------------------------------------------------------------------------------------
up="$work/upstream"
git init -q -b main "$up"
git -C "$up" config user.name control
git -C "$up" config user.email control@example.invalid
printf 'one\n' > "$up/file"
git -C "$up" add file
git -C "$up" commit -q -m one
pinned="$(git -C "$up" rev-parse HEAD)"
printf 'two\n' >> "$up/file"
git -C "$up" commit -q -am two
tip="$(git -C "$up" rev-parse HEAD)"
pkg="$work/package"
mirrors="$work/mirrors"
manifest() {  # rev
  mkdir -p "$pkg"
  python3 - "$pkg/lake-manifest.json" "$up" "$1" <<'PY'
import json, sys
json.dump({"packages": [
    {"type": "git", "name": "dep", "url": sys.argv[2], "rev": sys.argv[3]},
    {"type": "path", "name": "local", "dir": "../local"}]}, open(sys.argv[1], "w"))
PY
}
seed() { PATH="$bin:$PATH" bash "$root/tooling/seed-lake-packages.sh" "$pkg" "$mirrors"; }

manifest "$pinned"
expect 'seed: a dependency is cloned' 0 "dep: $pinned, cloned from the mirror" seed
[ "$(git -C "$pkg/.lake/packages/dep" rev-parse HEAD)" = "$pinned" ] \
  || fail_case 'seed: the dependency is not at the pinned revision, although upstream has moved on'
[ "$(git -C "$pkg/.lake/packages/dep" remote get-url origin)" = "$up" ] || fail_case 'seed: origin is not the manifest URL'
[ ! -e "$pkg/.lake/packages/local" ] || fail_case 'seed: a path dependency was cloned'
expect 'seed: a present dependency is left to Lake' 0 'already present, left to Lake' seed
rm -rf "$pkg/.lake"
manifest "$tip"
expect 'seed: a later pinned revision is fetched' 0 "dep: $tip, cloned from the mirror" seed
[ "$(git -C "$pkg/.lake/packages/dep" rev-parse HEAD)" = "$tip" ] || fail_case 'seed: the dependency is not at the second pinned revision'
rm -rf "$pkg/.lake"
manifest 0123456789abcdef0123456789abcdef01234567
expect 'seed: a revision the upstream lacks is refused' nonzero 'dep' seed
[ ! -e "$pkg/.lake/packages/dep" ] || fail_case 'seed: a dependency was cloned at a revision the upstream lacks'

# A revision the mirror lacked is fetched from the dependency's URL and kept under a named ref, so the mirror's
# own housekeeping cannot prune it.
up2="$work/upstream2"
git init -q -b main "$up2"
git -C "$up2" config user.name control
git -C "$up2" config user.email control@example.invalid
printf 'one\n' > "$up2/file"
git -C "$up2" add file
git -C "$up2" commit -q -m one
pkg2="$work/package2"
mirrors2="$work/mirrors2"
manifest2() {
  mkdir -p "$pkg2"
  python3 - "$pkg2/lake-manifest.json" "$up2" "$1" <<'PY'
import json, sys
json.dump({"packages": [{"type": "git", "name": "dep", "url": sys.argv[2], "rev": sys.argv[3]}]}, open(sys.argv[1], "w"))
PY
}
manifest2 "$(git -C "$up2" rev-parse HEAD)"
PATH="$bin:$PATH" bash "$root/tooling/seed-lake-packages.sh" "$pkg2" "$mirrors2" >/dev/null
printf 'two\n' >> "$up2/file"
git -C "$up2" commit -q -am two
later="$(git -C "$up2" rev-parse HEAD)"
rm -rf "$pkg2/.lake"
manifest2 "$later"
cases=$((cases + 1))
PATH="$bin:$PATH" bash "$root/tooling/seed-lake-packages.sh" "$pkg2" "$mirrors2" >/dev/null
[ "$(git -C "$mirrors2/dep.git" rev-parse "refs/pinned/$later")" = "$later" ] \
  || fail_case 'seed: a revision fetched into the mirror is not kept under refs/pinned'

echo "install-script-cases: $cases cases (elan and actionlint digest checks, the pinned release, seed-lake-packages revision pin) gave the expected result"
