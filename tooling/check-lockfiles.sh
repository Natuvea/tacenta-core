#!/usr/bin/env bash
# Every Cargo.lock in the checkout is the lockfile its manifests resolve to, checked offline.
#
#   bash tooling/check-lockfiles.sh      every lockfile of the git checkout the working directory is in
#
# Why. The hosted jobs build with `--locked`, so a manifest edit whose lockfile was not updated fails there and
# nowhere earlier: the Rust loop of `tooling/ci.sh` and the diff-scoped steps of `tooling/fast.sh` build
# `tacenta-core` and the vectors runner, not every workspace that has a lockfile. On 2026-10-23
# `tacenta-core/kdf/Cargo.toml` stopped depending on its old RustCrypto crates, and the lockfiles of the vectors
# runner (`tacenta-test-vectors/runners/rust`) and of the fuzz workspace (`tacenta-core/fuzz`) still listed them;
# the hosted clippy run of the vectors runner refused the lockfile, and no local check had read either.
#
# What. The lockfiles are found, not listed here: every path git lists whose name is `Cargo.lock`, tracked or
# new and not ignored, so a workspace added later is read without anyone editing this file. The list is read
# NUL-separated with quotePath off, so a directory whose name git would quote (a space is fine either way; a
# non-ASCII byte, a quote or a backslash is not) is read too, not dropped. In the directory of
# each, `cargo metadata --locked --offline --format-version 1` runs with its output discarded. That resolves
# the manifests against the lockfile and the local cargo cache, builds nothing and fetches nothing (nor does
# rustup: RUSTUP_AUTO_INSTALL=0), and fails when the lockfile would have to change, the same verdict the hosted
# `--locked` builds reach. Each directory gets one line:
#
#   ok    cargo resolved the manifests to the lockfile as it is
#   FAIL  the lockfile would have to change; or the directory has no Cargo.toml (cargo would read a parent's
#         manifest instead); or the lockfile git lists is not in the working tree; or the manifest does not
#         parse; or cargo failed in any other way. The line names the directory and cargo's first error line
#   SKIP  `--offline` could not resolve because the cargo cache lacks a package or an index entry (cargo's
#         offline messages, and no lockfile or manifest error with them). The lockfile was NOT checked. Fetch
#         the cache once with `cargo fetch --locked` in that directory, or let any `--locked` build do it
#
# A machine with no `cargo` skips every directory. A skip is printed, counted in the last line, and, when
# FAST_SKIP_LOG names a file, appended to it so that `tooling/fast.sh` ends "ok WITH SKIPS" rather than plain
# "ok". With GITHUB_ACTIONS set a skip is a failure: a check that cannot run must not report green on a runner.
# A checkout with no lockfile at all is a failure, since a check that found nothing has checked nothing.
#
# Exit status: 0 when nothing failed (skips included, locally), 1 otherwise.
#
# What it does not see.
#   * A manifest edit that needs a package or a version the local cache does not hold is a SKIP, not a FAIL:
#     offline, cargo cannot tell a missing download from a missing package. That includes the common edit of
#     raising the version requirement of a dependency the lockfile already pins (`"0.4"` to `"0.5"`, with no
#     0.5 in the cache's index): the lockfile is stale, the hosted `--locked` build refuses it, and here it is a
#     loud SKIP locally (printed, counted, in FAST_SKIP_LOG) and a failure with GITHUB_ACTIONS set. The check is
#     only as strong as the cache is warm; with an empty cache every lockfile is a SKIP.
#   * A lockfile whose only stale entries are path packages is accepted, because cargo's `--locked` accepts it
#     (the hosted builds do too; the case `path-only-stale` records it).
#   * A Cargo.lock inside a member of another workspace is not read by cargo at all (cargo resolves the
#     workspace root's lockfile), so it is reported ok whatever it holds.
#   * A Cargo.toml with no Cargo.lock beside it (a new standalone workspace committed without its lockfile) is
#     not looked for: the check starts from lockfiles.
#   * It checks the lockfile against the manifests, not the dependencies against anything (that is `cargo audit`).
#
# The cases are tooling/tests/run-lockfile-check-cases.sh.
set -euo pipefail

cd "$(git rev-parse --show-toplevel)"
# A rustup proxy would otherwise download a toolchain a directory names that is not installed.
export RUSTUP_AUTO_INSTALL=0

in_ci=0
if [ "${GITHUB_ACTIONS:-}" = "true" ]; then
  in_ci=1
fi
ok=0
failed=0
skipped=0

skip() {  # directory, reason
  echo "lockfiles: SKIP $1: $2 (not checked)"
  skipped=$((skipped + 1))
  if [ -n "${FAST_SKIP_LOG:-}" ]; then
    echo "lockfile check of $1: $2" >> "$FAST_SKIP_LOG"
  fi
  if [ "$in_ci" -eq 1 ]; then
    echo "lockfiles: this is CI -- a check that cannot run is a failure, not a skip" >&2
    failed=$((failed + 1))
  fi
}
fail() {  # directory, reason
  echo "lockfiles: FAIL $1: $2" >&2
  failed=$((failed + 1))
}

dirs=()
while IFS= read -r -d '' path; do
  [ -n "$path" ] || continue
  [ "$(basename "$path")" = Cargo.lock ] || continue
  dirs+=("$(dirname "$path")")
done < <(git -c core.quotePath=false ls-files -z --cached --others --exclude-standard -- '*Cargo.lock' | sort -zu)

if [ "${#dirs[@]}" -eq 0 ]; then
  echo "lockfiles: no Cargo.lock in this checkout; a check that found nothing has checked nothing" >&2
  exit 1
fi

have_cargo=1
if ! command -v cargo >/dev/null 2>&1 || ! cargo --version >/dev/null 2>&1; then
  have_cargo=0
fi

err="$(mktemp)"
trap 'rm -f "$err"' EXIT
for dir in "${dirs[@]}"; do
  if [ ! -f "$dir/Cargo.lock" ]; then
    fail "$dir" "git lists $dir/Cargo.lock but the working tree has no such file"
    continue
  fi
  if [ ! -f "$dir/Cargo.toml" ]; then
    fail "$dir" "a Cargo.lock with no Cargo.toml beside it (cargo would resolve a parent directory's manifest)"
    continue
  fi
  if [ "$have_cargo" -eq 0 ]; then
    skip "$dir" "cargo not found or not runnable"
    continue
  fi
  if (cd "$dir" && cargo metadata --locked --offline --format-version 1 >/dev/null 2>"$err"); then
    echo "lockfiles: ok $dir"
    ok=$((ok + 1))
    continue
  fi
  first="$(grep -m 1 '^error' "$err" || true)"
  [ -n "$first" ] || first="$(head -n 1 "$err")"
  if grep -Eq 'needs to be updated but --locked|cannot update the lock file' "$err"; then
    fail "$dir" "the lockfile would have to change to match the manifests: ${first}"
  elif grep -Eq 'failed to parse manifest|failed to load manifest|could not parse input as TOML|^ *--> ([^ ]*/)?Cargo\.toml:[0-9]' "$err"; then
    fail "$dir" "a manifest does not parse: ${first}"
  elif grep -Eq 'attempting to make an HTTP request, but --offline was specified|offline mode \(via `--offline`\)|using offline mode|in the offline mode' "$err"; then
    skip "$dir" "--offline cannot resolve it from the local cargo cache (${first}); fetch it with 'cargo fetch --locked' there"
  else
    fail "$dir" "cargo metadata failed: ${first}"
  fi
  sed 's/^/  | /' "$err" >&2
done

echo "lockfiles: ${#dirs[@]} lockfile(s): ${ok} ok, ${failed} failed, ${skipped} skipped"
if [ "$failed" -gt 0 ]; then
  exit 1
fi
if [ "$skipped" -gt 0 ]; then
  echo "lockfiles: passed WITH SKIPS -- the skipped lockfiles above were not checked"
fi
