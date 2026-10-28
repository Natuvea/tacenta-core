#!/usr/bin/env bash
# Negative controls for the three CI installers that check what they fetch, and for the retry they download under:
#
#   tooling/install-elan.sh           the elan archive matches ELAN_SHA256 before its installer runs; the Lean
#                                     toolchains the lean-toolchain files pin are fetched once each, only when elan
#                                     does not list them, only when they name a release, under the retry
#   tooling/install-actionlint.sh     the actionlint archive matches its pinned digest before it is unpacked
#   tooling/seed-lake-packages.sh     a Lake dependency is cloned at the revision the manifest pins
#   tooling/retry-download.sh         a transient network failure is tried again, at most RETRY_DOWNLOAD_ATTEMPTS
#                                     times with increasing waits; a digest or integrity failure, or any other
#                                     failure, is not; a failure is never turned into success; every attempt's
#                                     output is printed
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
unset ELAN_VERSION ELAN_SHA256 RETRY_DOWNLOAD_ATTEMPTS RETRY_DOWNLOAD_WAITS

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
# A transient failure, as many times as STUB_CURL_FAILS holds, before the archive is served.
n="$(cat "${STUB_CURL_FAILS:-/nonexistent}" 2>/dev/null || echo 0)"
if [ "$n" -gt 0 ]; then
  echo $((n - 1)) > "$STUB_CURL_FAILS"
  echo "curl: (35) OpenSSL SSL_connect: SSL_ERROR_SYSCALL" >&2
  exit 35
fi
cp "$STUB_ARCHIVE" "$out"
STUB
# The retry's waits are recorded, not waited.
cat >"$bin/sleep" <<'STUB'
#!/usr/bin/env bash
echo "$1" >> "${STUB_SLEEPS:-/dev/null}"
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
  RC_SEEN="$rc"
  OUT_SEEN="$out"
  if { [ "$want" = 0 ] && [ "$rc" -ne 0 ]; } || { [ "$want" != 0 ] && [ "$rc" -eq 0 ]; } \
    || { [ "$want" != 0 ] && [ "$want" != nonzero ] && [ "$rc" -ne "$want" ]; } || ! grep -qF -- "$needle" <<<"$out"; then
    fail_case "$name: expected exit $want and '$needle', got exit $rc" "$out"
  fi
}

# The number of lines of a file, 0 when it is absent.
count() { if [ -f "$1" ]; then wc -l < "$1" | tr -d ' '; else echo 0; fi; }

# ---- retry-download ---------------------------------------------------------------------------------------------
retry="$root/tooling/retry-download.sh"
# A command that fails as many times as $work/fails holds, printing $FAIL_TEXT and exiting $FAIL_RC, then succeeds.
cat >"$work/flaky" <<'STUB'
#!/usr/bin/env bash
echo "flaky $*" >> "$FLAKY_LOG"
echo "${LC_ALL-unset} ${LANG-unset}" >> "${FLAKY_LOCALE:-/dev/null}"
n="$(cat "$FLAKY_FAILS")"
if [ "$n" -gt 0 ]; then echo $((n - 1)) > "$FLAKY_FAILS"; echo "$FAIL_TEXT"; exit "$FAIL_RC"; fi
echo "fetched"
STUB
chmod +x "$work/flaky"
flaky() {  # name want needle fails text rc [command...]
  local name="$1" want="$2" needle="$3"
  echo "$4" > "$work/fails"
  : > "$work/flaky-log"; : > "$work/sleeps"
  FLAKY_FAILS="$work/fails" FLAKY_LOG="$work/flaky-log" FAIL_TEXT="$5" FAIL_RC="$6" STUB_SLEEPS="$work/sleeps" \
    expect "$name" "$want" "$needle" "${@:7}"
}
flaky 'retry: a success is one attempt' 0 'fetched' 0 '' 0 bash "$retry" -- "$work/flaky"
[ "$(count "$work/flaky-log")" = 1 ] || fail_case 'retry: a success ran more than once'
flaky 'retry: a transient failure is retried' 0 'attempt 3/4 succeeded' 2 'curl: (56) Connection reset by peer' 1 bash "$retry" -- "$work/flaky"
[ "$(tr '\n' ' ' < "$work/sleeps")" = '15 30 ' ] || fail_case 'retry: the waits did not increase 15, 30' "$(cat "$work/sleeps")"
for text in 'error during download' 'SSL connect error' 'Operation timed out after 30001 milliseconds' \
  'curl: (18) transfer closed with 500 bytes remaining to read' 'Partial file. Only a part of the file was transferred.'; do
  flaky "retry: '$text' is transient" 0 'attempt 2/4 succeeded' 1 "$text" 1 bash "$retry" -- "$work/flaky"
done
# A persistent transient failure is tried four times, every attempt's output printed, and fails with its status.
flaky 'retry: a persistent failure is not success' 7 'giving up after 4 attempts' 9 'SSL connect error' 7 bash "$retry" -- "$work/flaky"
[ "$RC_SEEN" = 7 ] || fail_case "retry: a persistent failure exited $RC_SEEN, not the command's 7"
[ "$(count "$work/flaky-log")" = 4 ] || fail_case 'retry: a persistent failure was not tried exactly four times'
[ "$(grep -c '^SSL connect error$' <<<"$OUT_SEEN")" = 4 ] || fail_case "retry: not every attempt's output was printed" "$OUT_SEEN"
[ "$(tr '\n' ' ' < "$work/sleeps")" = '15 30 60 ' ] || fail_case 'retry: the waits did not increase 15, 30, 60' "$(cat "$work/sleeps")"
# A digest or integrity failure is never retried, even when it also names a transient one, and keeps its status.
flaky 'retry: a hash mismatch is not retried' 3 'names a digest or integrity problem; not retrying' 9 \
  'sha256 checksum did not match after the connection timed out' 3 bash "$retry" -- "$work/flaky"
[ "$RC_SEEN" = 3 ] && [ "$(count "$work/flaky-log")" = 1 ] || fail_case 'retry: a hash mismatch was retried or lost its status'
# Any other failure is not retried.
flaky 'retry: another failure is not retried' 9 'not a transient network failure; not retrying' 9 'error: unknown package' 9 \
  bash "$retry" -- "$work/flaky"
[ "$RC_SEEN" = 9 ] && [ "$(count "$work/flaky-log")" = 1 ] || fail_case 'retry: another failure was retried or lost its status'
# curl's transient exit statuses count without the words, for curl only (a command whose name is curl).
mkdir -p "$work/curlbin"
cp "$work/flaky" "$work/curlbin/curl"
for code in 5 6 7 18 28 35 52 55 56; do
  flaky "retry: curl exit $code is transient" 0 'attempt 2/4 succeeded' 1 '' "$code" \
    bash "$retry" -- "$work/curlbin/curl" -o x https://example.invalid/
done
flaky 'retry: exit 35 of another command is not' 35 'not retrying' 1 '' 35 bash "$retry" -- "$work/flaky"
# Codes for a failure a second attempt would repeat: an HTTP error status, a certificate that did not verify, a
# malformed URL, a write error.
for code in 22 60 3 23; do
  flaky "retry: curl exit $code is not transient" "$code" 'not retrying' 1 '' "$code" \
    bash "$retry" -- "$work/curlbin/curl" -o x https://example.invalid/
done
# A hash mismatch from curl's own transient path is still not retried: the words win over the code.
flaky 'retry: a curl transient code with an integrity message is not retried' 56 'names a digest or integrity problem' 9 \
  'integrity check failed' 56 bash "$retry" -- "$work/curlbin/curl" -o x https://example.invalid/
[ "$(count "$work/flaky-log")" = 1 ] || fail_case 'retry: an integrity failure with a curl transient code was retried'
# For curl the exit code alone decides: a permanent code is not retried even when the words look transient.
flaky 'retry: curl exit 22 with transient words is not retried' 22 "curl's exit 22 is not one of its codes" 1 \
  'curl: (22) transfer closed' 22 bash "$retry" -- "$work/curlbin/curl" -o x https://example.invalid/
[ "$(count "$work/flaky-log")" = 1 ] || fail_case 'retry: curl exit 22 with transient words was retried'
# Only a command named curl gets the code list: curl through env is judged by its words, here none.
flaky 'retry: env curl is judged by its words' 18 'not a transient network failure; not retrying' 1 '' 18 \
  bash "$retry" -- env "$work/curlbin/curl" -o x https://example.invalid/
# The new words beside a digest message are refused at once.
flaky "retry: 'transfer closed' beside a hash mismatch is not retried" 4 'names a digest or integrity problem' 9 \
  'transfer closed with 10 bytes remaining; hash mismatch' 4 bash "$retry" -- "$work/flaky"
flaky "retry: 'partial file' beside a sha256 failure is not retried" 4 'names a digest or integrity problem' 9 \
  'partial file; sha256 failed' 4 bash "$retry" -- "$work/flaky"
[ "$(count "$work/flaky-log")" = 1 ] || fail_case "retry: 'partial file' beside a sha256 failure was retried"
# The words are matched byte by byte, so a byte that is not valid in the caller's UTF-8 locale does not hide them.
LC_ALL=en_US.UTF-8 flaky 'retry: an invalid byte does not hide a transient phrase' 0 'attempt 2/4 succeeded' 1 \
  $'caf\xe9 \xff Connection reset by peer' 1 bash "$retry" -- "$work/flaky"
LC_ALL=en_US.UTF-8 flaky 'retry: an invalid byte does not hide a digest phrase' 56 'names a digest or integrity problem' 9 \
  $'caf\xe9 \xff checksum mismatch' 56 bash "$retry" -- "$work/curlbin/curl" -o x https://example.invalid/
[ "$(count "$work/flaky-log")" = 1 ] || fail_case 'retry: a digest phrase beside an invalid byte was retried'
# The command runs in the C locale, whatever the caller's, so translated messages cannot hide a transient one.
: > "$work/locale"
LC_ALL=de_DE.UTF-8 LANG=de_DE.UTF-8 FLAKY_LOCALE="$work/locale" \
  flaky 'retry: the command runs in the C locale' 0 'fetched' 0 '' 0 bash "$retry" -- "$work/flaky"
[ "$(cat "$work/locale")" = 'C C' ] || fail_case 'retry: the command did not run with LC_ALL=C and LANG=C' "$(cat "$work/locale")"
# The bound is the one given, and an out-of-range or malformed setting is refused.
RETRY_DOWNLOAD_ATTEMPTS=2 flaky 'retry: the attempts are bounded as set' 1 'giving up after 2 attempts' 9 'timed out' 1 bash "$retry" -- "$work/flaky"
[ "$(count "$work/flaky-log")" = 2 ] || fail_case 'retry: RETRY_DOWNLOAD_ATTEMPTS=2 did not give two attempts'
RETRY_DOWNLOAD_ATTEMPTS=0 flaky 'retry: zero attempts is refused' nonzero 'must be 1 to 10' 0 '' 0 bash "$retry" -- "$work/flaky"
RETRY_DOWNLOAD_ATTEMPTS=11 flaky 'retry: eleven attempts is refused' nonzero 'must be 1 to 10' 0 '' 0 bash "$retry" -- "$work/flaky"
RETRY_DOWNLOAD_WAITS=' ' flaky 'retry: a setting with no wait is refused' nonzero 'names no wait' 0 '' 0 bash "$retry" -- "$work/flaky"
RETRY_DOWNLOAD_WAITS='5 x' flaky 'retry: a malformed wait is refused' nonzero 'whole seconds' 0 '' 0 bash "$retry" -- "$work/flaky"
flaky 'retry: a command without -- is refused' nonzero 'usage:' 0 '' 0 bash "$retry" "$work/flaky"

# ---- elan -------------------------------------------------------------------------------------------------
elan_src="$work/elan-src"
mkdir -p "$elan_src"
cat >"$elan_src/elan-init" <<'STUB'
#!/usr/bin/env bash
echo "ran $*" > "$STUB_SENTINEL"
mkdir -p "$HOME/.elan/bin"
cp "$STUB_ELAN" "$HOME/.elan/bin/elan"
STUB
chmod +x "$elan_src/elan-init"
# The elan the installer leaves: it lists STUB_TOOLCHAINS, records each install, and fails an install as many
# times as STUB_ELAN_FAILS holds, with STUB_ELAN_ERROR (a transient network error by default).
cat >"$work/stub-elan" <<'STUB'
#!/usr/bin/env bash
case "$1 ${2:-}" in
  "--version ") echo "elan 4.2.4 (stub)" ;;
  "toolchain list") cat "${STUB_TOOLCHAINS:-/nonexistent}" 2>/dev/null || true ;;
  "toolchain install")
    echo "install $3" >> "$STUB_ELAN_LOG"
    n="$(cat "${STUB_ELAN_FAILS:-/nonexistent}" 2>/dev/null || echo 0)"
    if [ "$n" -gt 0 ]; then
      echo $((n - 1)) > "$STUB_ELAN_FAILS"
      echo "${STUB_ELAN_ERROR:-error: could not download file: [35] SSL connect error}" >&2
      exit 1
    fi
    echo "info: installed $3" ;;
  *) echo "stub elan: unexpected $*" >&2; exit 9 ;;
esac
STUB
chmod +x "$work/stub-elan"
tar czf "$work/elan.tar.gz" -C "$elan_src" elan-init
good="$(shasum -a 256 "$work/elan.tar.gz" | awk '{print $1}')"
wrong='0000000000000000000000000000000000000000000000000000000000000000'
export STUB_ARCHIVE="$work/elan.tar.gz" STUB_URLS="$work/urls" STUB_SENTINEL="$work/sentinel" STUB_FLOCK="$work/flock"
export STUB_ELAN="$work/stub-elan" STUB_ELAN_LOG="$work/elan-log" STUB_SLEEPS="$work/sleeps"
installer="$root/tooling/install-elan.sh"
# The toolchain the repository's lean-toolchain files pin, read as the installer reads them.
pinned_toolchain="$(head -n 1 "$root/tacenta-model/lean-toolchain" | tr -d '[:space:]')"

fresh_home() {
  rm -rf "$work/home" "$work/urls" "$work/sentinel" "$work/flock" "$work/ghpath" "$work/elan-log" "$work/sleeps" \
    "$work/toolchains" "$work/curl-fails" "$work/elan-fails"
  mkdir -p "$work/home"
  : > "$work/urls"; : > "$work/flock"; : > "$work/elan-log"; : > "$work/sleeps"
}

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
# The pinned Lean toolchain is fetched once (three lean-toolchain files name one release), by elan, before the
# installer ends.
[ "$(cat "$work/elan-log")" = "install $pinned_toolchain" ] \
  || fail_case 'elan: the pinned Lean toolchain was not fetched exactly once' "$(cat "$work/elan-log")"
case "$pinned_toolchain" in leanprover/lean4:v[0-9]*) ;; *) fail_case "elan: the tree pins '$pinned_toolchain', not a release" ;; esac

# A toolchain elan already lists is not fetched again.
fresh_home
printf '%s (default)\n' "$pinned_toolchain" > "$work/toolchains"
STUB_TOOLCHAINS="$work/toolchains" HOME="$work/home" ELAN_VERSION=v4.2.4 ELAN_SHA256="$good" \
  expect 'elan: a listed toolchain is not fetched again' 0 "Lean toolchain $pinned_toolchain is already installed" bash "$installer"
[ ! -s "$work/elan-log" ] || fail_case 'elan: a toolchain elan lists was fetched again' "$(cat "$work/elan-log")"

# A dropped connection while fetching the toolchain is tried again, and the install then succeeds.
fresh_home
echo 2 > "$work/elan-fails"
STUB_ELAN_FAILS="$work/elan-fails" HOME="$work/home" ELAN_VERSION=v4.2.4 ELAN_SHA256="$good" \
  expect 'elan: a transient toolchain failure is retried' 0 'retry-download: attempt 3/4' bash "$installer"
[ "$(count "$work/elan-log")" = 3 ] || fail_case 'elan: the transient failures were not retried twice' "$(cat "$work/elan-log")"
[ "$(tr '\n' ' ' < "$work/sleeps")" = '15 30 ' ] || fail_case 'elan: the waits between attempts were not 15 then 30 seconds' "$(cat "$work/sleeps")"
# One that persists fails after four attempts, with the toolchain's error, and the installer fails.
fresh_home
echo 9 > "$work/elan-fails"
STUB_ELAN_FAILS="$work/elan-fails" HOME="$work/home" ELAN_VERSION=v4.2.4 ELAN_SHA256="$good" \
  expect 'elan: a persistent transient toolchain failure fails' nonzero 'retry-download: giving up after 4 attempts' bash "$installer"
[ "$(count "$work/elan-log")" = 4 ] || fail_case 'elan: the persistent failure was not tried exactly four times' "$(cat "$work/elan-log")"
# Any other toolchain error is not retried.
fresh_home
echo 1 > "$work/elan-fails"
STUB_ELAN_FAILS="$work/elan-fails" STUB_ELAN_ERROR="error: no such toolchain" HOME="$work/home" ELAN_VERSION=v4.2.4 \
  ELAN_SHA256="$good" expect 'elan: another toolchain error is not retried' nonzero 'not a transient network failure; not retrying' bash "$installer"
[ "$(count "$work/elan-log")" = 1 ] || fail_case 'elan: a non-transient toolchain error was retried' "$(cat "$work/elan-log")"

# A dropped connection while fetching the elan archive is tried again; the digest is then checked once.
fresh_home
echo 1 > "$work/curl-fails"
STUB_CURL_FAILS="$work/curl-fails" HOME="$work/home" ELAN_VERSION=v4.2.4 ELAN_SHA256="$good" \
  expect 'elan: a transient archive failure is retried' 0 'elan v4.2.4 installed' bash "$installer"
[ "$(count "$work/urls")" = 2 ] || fail_case 'elan: the archive was not fetched twice after one transient failure' "$(cat "$work/urls")"
fresh_home
echo 9 > "$work/curl-fails"
STUB_CURL_FAILS="$work/curl-fails" HOME="$work/home" ELAN_VERSION=v4.2.4 ELAN_SHA256="$good" \
  expect 'elan: a persistent archive failure fails' nonzero 'retry-download: giving up after 4 attempts' bash "$installer"
[ ! -f "$work/sentinel" ] || fail_case 'elan: the installer ran although the archive was never fetched'

# A lean-toolchain file that names a moving channel, not a release, is refused before anything is fetched.
moving="$work/moving"
mkdir -p "$moving/tooling" "$moving/pkg"
cp "$installer" "$root/tooling/retry-download.sh" "$moving/tooling/"
echo 'leanprover/lean4:stable' > "$moving/pkg/lean-toolchain"
git init -q "$moving"
git -C "$moving" add -A
fresh_home
HOME="$work/home" ELAN_VERSION=v4.2.4 ELAN_SHA256="$good" \
  expect 'elan: an unpinned toolchain is refused' nonzero "names 'leanprover/lean4:stable', not a pinned Lean release" bash "$moving/tooling/install-elan.sh"
[ ! -s "$work/elan-log" ] || fail_case 'elan: an unpinned toolchain was fetched' "$(cat "$work/elan-log")"

fresh_home
HOME="$work/home" ELAN_VERSION=v4.2.4 ELAN_SHA256="$wrong" expect 'elan: a wrong digest is refused' nonzero 'did not match ELAN_SHA256; refusing to run it' bash "$installer"
[ ! -f "$work/sentinel" ] || fail_case 'elan: the installer ran although the digest did not match'
[ "$(count "$work/urls")" = 1 ] || fail_case 'elan: a digest mismatch was fetched again' "$(cat "$work/urls")"

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
# A dropped connection is tried again; the mismatch that follows is refused once, not retried.
: > "$work/urls"
echo 1 > "$work/curl-fails"
STUB_CURL_FAILS="$work/curl-fails" STUB_ARCHIVE="$work/actionlint.tar.gz" STUB_URLS="$work/urls" STUB_SLEEPS=/dev/null \
  expect 'actionlint: a transient failure is retried' nonzero 'SHA-256 mismatch' bash "$root/tooling/install-actionlint.sh" "$dest"
[ "$(count "$work/urls")" = 2 ] || fail_case 'actionlint: the archive was not fetched twice after one transient failure' "$(cat "$work/urls")"
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
cp "$root/tooling/retry-download.sh" "$work/retry-download.sh"
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

echo "install-script-cases: $cases cases (elan and actionlint digest checks, the pinned release and Lean toolchain, the retry of transient download failures and the refusal to retry anything else, seed-lake-packages revision pin) gave the expected result"
