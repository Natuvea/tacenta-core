#!/usr/bin/env bash
# Run a download command again after a transient network failure, a bounded number of times, and never after
# any other failure.
#
#   bash tooling/retry-download.sh -- <command> [args...]
#
# Why. Hosted runs have failed on one dropped connection: on 2026-10-28 a pull request's run failed in "Fetch
# the Mathlib cache" and "Build the model" with "SSL connect error" while elan fetched the pinned Lean release
# from releases.lean-lang.org. A second attempt a few seconds later is the usual cure; anything else is not.
#
# What. The command runs up to RETRY_DOWNLOAD_ATTEMPTS times (default 4, at most 10), waiting
# RETRY_DOWNLOAD_WAITS seconds between attempts (default "15 30 60", one value per wait, increasing). Each
# attempt's output is printed as it runs, kept, and the attempt is numbered in the log. After a failure it runs
# again only when the failure is transient, which is one of:
#
#   * the command is curl and it exited with one of curl's codes for a network failure on the way: 5 or 6
#     (the proxy's or the host's name did not resolve), 7 (could not connect), 18 (partial file: the
#     transfer was cut off), 28 (timed out), 35 (TLS connect error), 52 (an empty reply), 55 (failure sending
#     data) or 56 (failure receiving data). For curl the exit code alone decides: any other code, such as 22
#     (an HTTP error status) or 60 (the certificate did not verify), is not retried whatever the output says.
#     Only a command whose own name is curl gets the code list; curl run through `env`, `timeout` or the like
#     is a command of another name and is judged by its words;
#   * for any other command, the output names a transient network failure: "error during download",
#     "Connection reset", "SSL connect error", "timed out", "transfer closed" or "partial file" (case ignored).
#
# The command runs with LC_ALL=C and LANG=C, so the C library's error text in elan's and Lake's output (for
# example "Connection reset by peer") is the untranslated English these words are matched against; curl's exit
# codes do not depend on the locale. The words are matched byte by byte (grep under LC_ALL=C), so a byte that is
# not valid in the caller's locale beside them cannot hide them.
#
# A failure is never retried when its output names a digest or integrity problem ("checksum", "sha256",
# "hash mismatch", "did not match", "integrity"; case ignored), even if it also names a transient one, and
# never when it is anything else. Such a failure ends the run at once with the command's own exit status. After
# the last attempt fails, the run ends with that attempt's exit status and prints a summary of every attempt and
# the last attempt's output again.
#
# What it does not do. It does not change the command beyond its locale: no TLS option is added or removed, no
# other source or version is tried, and a digest check that follows the download in the caller still runs once on what was
# downloaded. It cannot tell a transient failure from a persistent one that prints the same words; a persistent
# one is tried RETRY_DOWNLOAD_ATTEMPTS times and then fails.
#
# The cases are in tooling/tests/run-install-script-cases.sh (retry-download section).
set -euo pipefail

if [ "${1:-}" != "--" ] || [ "$#" -lt 2 ]; then
  echo "retry-download: usage: bash tooling/retry-download.sh -- <command> [args...]" >&2
  exit 2
fi
shift

attempts="${RETRY_DOWNLOAD_ATTEMPTS:-4}"
case "$attempts" in
  [1-9] | 10) ;;
  *) echo "retry-download: RETRY_DOWNLOAD_ATTEMPTS must be 1 to 10, not '$attempts'" >&2; exit 2 ;;
esac
read -r -a waits <<<"${RETRY_DOWNLOAD_WAITS:-15 30 60}"
if [ "${#waits[@]}" -eq 0 ]; then
  echo "retry-download: RETRY_DOWNLOAD_WAITS names no wait" >&2
  exit 2
fi
for w in "${waits[@]}"; do
  case "$w" in
    '' | *[!0-9]*) echo "retry-download: RETRY_DOWNLOAD_WAITS must be whole seconds, not '$w'" >&2; exit 2 ;;
  esac
done

TRANSIENT_TEXT='error during download|connection reset|ssl connect error|timed out|transfer closed|partial file'
INTEGRITY_TEXT='checksum|sha256|hash mismatch|did not match|integrity'
# curl's exit codes for a network failure on the way (see the header); 18 is a transfer cut off part way.
CURL_TRANSIENT=" 5 6 7 18 28 35 52 55 56 "

logs="$(mktemp -d)"
trap 'rm -rf "$logs"' EXIT
summary=""
command_name="${1##*/}"

attempt=1
while :; do
  echo "retry-download: attempt ${attempt}/${attempts}: $*" >&2
  log="$logs/attempt-$attempt.log"
  set +e
  LC_ALL=C LANG=C "$@" 2>&1 | tee "$log"
  rc="${PIPESTATUS[0]}"
  set -e
  if [ "$rc" -eq 0 ]; then
    if [ "$attempt" -gt 1 ]; then
      echo "retry-download: attempt ${attempt}/${attempts} succeeded after ${summary}" >&2
    fi
    exit 0
  fi

  reason=""
  why="not a transient network failure"
  if LC_ALL=C grep -Eiq -- "$INTEGRITY_TEXT" "$log"; then
    why="its output names a digest or integrity problem"
  elif [ "$command_name" = curl ]; then
    if [ "${CURL_TRANSIENT#* $rc }" != "$CURL_TRANSIENT" ]; then
      reason="curl exit $rc"
    else
      why="curl's exit $rc is not one of its codes for a transient network failure"
    fi
  elif matched="$(LC_ALL=C grep -Eio -m 1 -- "$TRANSIENT_TEXT" "$log")"; then
    reason="\"$matched\""
  fi
  summary="${summary}${summary:+; }attempt ${attempt}: exit ${rc}${reason:+ (transient: $reason)}"

  if [ -z "$reason" ]; then
    echo "retry-download: attempt ${attempt}/${attempts} failed with exit ${rc}, ${why}; not retrying" >&2
    exit "$rc"
  fi
  if [ "$attempt" -ge "$attempts" ]; then
    echo "retry-download: giving up after ${attempts} attempts: ${summary}" >&2
    echo "retry-download: the last attempt's output:" >&2
    sed 's/^/  | /' "$log" >&2
    exit "$rc"
  fi
  if [ "$attempt" -le "${#waits[@]}" ]; then
    wait_for="${waits[$((attempt - 1))]}"
  else
    wait_for="${waits[$((${#waits[@]} - 1))]}"
  fi
  echo "retry-download: attempt ${attempt}/${attempts} failed with exit ${rc} (transient: ${reason}); waiting ${wait_for}s" >&2
  sleep "$wait_for"
  attempt=$((attempt + 1))
done
