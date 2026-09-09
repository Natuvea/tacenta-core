#!/usr/bin/env bash
# Every fuzz target, briefly, against its committed corpus.
#
# **A regression gate, not a search.** Each target replays the corpus and then
# fuzzes for a few seconds, which is enough to catch a change that reintroduces
# a known input and nowhere near enough to find a new one. The search is the
# nightly fuzz workflow, with a corpus that grows.
#
# Kept out of `tooling/ci.sh`'s main body and called from it, because this needs
# a nightly toolchain and `cargo-fuzz`, and a runner without either should skip
# rather than fail: the every-push gate has to stay runnable on a plain stable
# toolchain. `ci.sh` decides that; this script assumes both are present.
set -euo pipefail

here="$(cd "$(dirname "$0")/.." && pwd)"
cd "$here/tacenta-core"

# Seconds per target. Six targets today, so the whole step is about a minute. Long
# enough to replay every corpus entry and take a few thousand fresh runs;
# short enough that nobody starts wondering whether to skip it.
seconds="${FUZZ_SMOKE_SECONDS:-10}"

# **Name the toolchain rather than relying on the default.** `cargo fuzz` passes
# `-Z` flags, so it needs nightly; a runner's default is usually stable, and
# installing `cargo-fuzz` does not change that. Newest installed nightly unless
# told otherwise, because the corpus is not toolchain-specific and pinning a
# date here would be a second pin to keep in step for no benefit.
toolchain="${FUZZ_TOOLCHAIN:-}"
if [ -z "$toolchain" ]; then
  toolchain="$(rustup toolchain list | awk '{print $1}' | grep '^nightly' | sort | tail -1)"
fi
if [ -z "$toolchain" ]; then
  echo "fuzz-smoke: no nightly toolchain; ci.sh should have skipped this" >&2
  exit 1
fi
echo "fuzz-smoke: using $toolchain"

# Every file under fuzz_targets/ is a target: enumerated rather than listed,
# so a target added to the crate cannot be left out of the smoke run by
# forgetting to name it here (the triple_receive target was, for one commit).
count=0
for target_file in fuzz/fuzz_targets/*.rs; do
  target="$(basename "$target_file" .rs)"
  count=$((count + 1))
  echo "-- fuzz: $target --"
  # A persisted session holding an ML-KEM key pair exports to about 14 KB,
  # and the persisted-state target restores one and drives it, so that target
  # needs inputs well past libFuzzer's default 4096-byte cap; the others do
  # not, and a cap keeps them fast.
  max_len=4096
  if [ "$target" = "persisted_state" ]; then max_len=32768; fi
  # `-runs` as well as `-max_total_time`: whichever comes first. A slow target
  # on a loaded runner should stop on time, and a fast one should not spin.
  cargo "+$toolchain" fuzz run "$target" -- \
    -runs=20000 \
    -max_len="$max_len" \
    -max_total_time="$seconds" \
    -print_final_stats=1
done

# A finding writes an artifact and a non-zero exit above, so reaching here means
# none did. Checked anyway: a target that fails to *start* could otherwise pass
# without a finding.
found="$(find fuzz/artifacts -type f 2>/dev/null | head -5)"
if [ -n "$found" ]; then
  echo "ERROR: fuzz artifacts present:" >&2
  echo "$found" >&2
  exit 1
fi

echo "fuzz-smoke: $count targets clean"
