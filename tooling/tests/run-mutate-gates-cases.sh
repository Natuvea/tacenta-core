#!/usr/bin/env bash
# Negative controls for the mutation harness itself, `tooling/mutate-gates.py`.
#
# The harness is the evidence that every other control goes red, so it must not report green when it cannot
# tell. It runs here in a throwaway repository with one gate (`gate.sh`, which refuses the input `bad`), one
# runner (`runner.sh`, which feeds it `ok` and `bad` and reports a failing case on a line beginning `WRONG`),
# and an edit file written by each case. Every case requires the harness's exit status and the word it prints:
#
#   a runner that is red before any edit        "baseline FAIL" and exit 1: no edit would mean anything
#   an edit that makes the gate accept `bad`    "accepted", exit 0
#   an edit that makes the gate refuse `ok`     "behaviour", exit 0
#   an edit that only changes the words         "message only", exit 1 unless listed `equivalent`, then 0
#   an edit the runner does not notice          "survived", exit 1 unless listed `uncovered`, then 0
#   an edit listed `equivalent` that a case sees   "STALE", exit 1
#   an edit whose runner fails for another reason  "WRONG-REASON", exit 1
#   an edit whose `old` text is not there once     exit 1, naming the edit
#   a runner that builds through a Cargo-like cache in `$CARGO_TARGET_DIR`, with the caller's
#   `CARGO_TARGET_DIR` naming a directory shared with a checkout: the edit is still seen ("accepted"), and
#   nothing is written to the shared directory (each worktree builds into a target directory of its own,
#   one per run, in the harness's temporary directory, and none is left there after the run)
set -euo pipefail

root="$(cd "$(dirname "$0")/../.." && pwd)"
work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT
repo="$work/repo"
cases=0

git init -q -b main "$repo"
git -C "$repo" config user.name control
git -C "$repo" config user.email control@example.invalid
mkdir -p "$repo/tooling"
cp "$root/tooling/mutate-gates.py" "$repo/tooling/"
cat >"$repo/gate.sh" <<'GATE'
#!/usr/bin/env bash
if [ "$(cat input.txt)" = ok ]; then echo accepted; else echo "bad input" >&2; exit 1; fi
GATE
cat >"$repo/runner.sh" <<'RUNNER'
#!/usr/bin/env bash
set -uo pipefail
printf ok > input.txt
bash gate.sh >/dev/null 2>&1 || { echo "WRONG  honest: expected acceptance, got exit 1" >&2; exit 1; }
printf bad > input.txt
out="$(bash gate.sh 2>&1)" && { echo "WRONG  refused-input: expected refusal, was accepted" >&2; exit 1; }
grep -qF 'bad input' <<<"$out" || { echo "WRONG  refused-input: refused, but not for 'bad input'" >&2; exit 1; }
echo "mini runner: both cases gave the expected result"
RUNNER
git -C "$repo" add -A
git -C "$repo" commit -q -m base

# edit <json fields...>: write tooling/gate-mutations.json with one edit and commit it.
write_edits() {
  printf '%s\n' "$1" > "$repo/tooling/gate-mutations.json"
  git -C "$repo" add -A
  git -C "$repo" commit -q -m "edits" --allow-empty
}
harness() {  # name want-exit needle...
  local name="$1" want="$2" out rc
  shift 2
  set +e
  out="$(cd "$repo" && python3 tooling/mutate-gates.py 2>&1)"
  rc=$?
  set -e
  cases=$((cases + 1))
  if [ "$rc" -ne "$want" ]; then
    echo "WRONG  mutate-gates $name: expected exit $want, got $rc" >&2
    printf '%s\n' "$out" >&2
    exit 1
  fi
  local needle
  for needle in "$@"; do
    if ! grep -qF -- "$needle" <<<"$out"; then
      echo "WRONG  mutate-gates $name: output lacks '$needle'" >&2
      printf '%s\n' "$out" >&2
      exit 1
    fi
  done
}
edit='"id": "E1", "file": "gate.sh", "what": "w", "runner": "bash runner.sh"'

write_edits '{"mutations": [{'"$edit"', "old": "exit 1", "new": "exit 0", "expect": "WRONG  refused-input"}]}'
harness 'an edit that makes the gate accept the input it must refuse' 0 'accepted ' '1 seen as accepted'
write_edits '{"mutations": [{'"$edit"', "old": "= ok ]", "new": "= nothing ]", "expect": "WRONG  honest"}]}'
harness 'an edit that makes the gate refuse an honest input' 0 'behaviour ' '1 as another wrong verdict'
write_edits '{"mutations": [{'"$edit"', "old": "bad input", "new": "bad data", "expect": "WRONG  refused-input"}]}'
harness 'an edit that only changes the diagnostic' 1 'message only' '[NOT CAUGHT]'
write_edits '{"mutations": [{'"$edit"', "old": "bad input", "new": "bad data", "expect": "WRONG  refused-input", "equivalent": "only the words differ"}]}'
harness 'the same edit, listed as equivalent' 0 'message only' '[listed: equivalent]'
write_edits '{"mutations": [{'"$edit"', "old": "echo accepted", "new": "echo accepted-it", "expect": "WRONG  honest"}]}'
harness 'an edit no case notices' 1 'survived' '[NOT CAUGHT]'
write_edits '{"mutations": [{'"$edit"', "old": "echo accepted", "new": "echo accepted-it", "expect": "WRONG  honest", "uncovered": "no case reads the word"}]}'
harness 'the same edit, listed as uncovered' 0 'survived' '[listed: uncovered]'
write_edits '{"mutations": [{'"$edit"', "old": "exit 1", "new": "exit 0", "expect": "WRONG  refused-input", "equivalent": "claimed"}]}'
harness 'an edit listed as equivalent that a case sees as accepted' 1 'STALE'
write_edits '{"mutations": [{'"$edit"', "old": "exit 1", "new": "exit 0", "expect": "a line the runner never prints"}]}'
harness 'an edit that turns the runner red for another reason' 1 'WRONG-REASON'
write_edits '{"mutations": [{'"$edit"', "old": "nowhere in the file", "new": "x", "expect": "WRONG"}]}'
harness 'an edit whose old text is not in the file' 1 'E1' 'holds the edit'

# A runner that builds the way Cargo does: into `$CARGO_TARGET_DIR` (default `target`), reusing a build that is
# already there, as Cargo reuses a workspace member's build whose relative path matches and whose sources are not
# newer. With the caller's CARGO_TARGET_DIR shared, the baseline's honest build would hide the edit (it survives),
# or an edit's build would be left for the next run in the checkout to reuse.
shared="$work/shared-target"
mkdir -p "$shared"
cat >"$repo/cached-runner.sh" <<'RUNNER'
#!/usr/bin/env bash
set -uo pipefail
target="${CARGO_TARGET_DIR:-target}"
[ -z "${CACHED_LOG:-}" ] || echo "$target" >> "$CACHED_LOG"
mkdir -p "$target"
[ -f "$target/gate.sh" ] || cp gate.sh "$target/gate.sh"
printf bad > input.txt
bash "$target/gate.sh" >/dev/null 2>&1 && { echo "WRONG  cached-refused-input: expected refusal, was accepted" >&2; exit 1; }
echo "cached runner: the bad input was refused"
RUNNER
git -C "$repo" add -A
git -C "$repo" commit -q -m "cached runner"
write_edits '{"mutations": [{"id": "cached-build", "file": "gate.sh", "what": "w", "runner": "bash cached-runner.sh", "old": "exit 1", "new": "exit 0", "expect": "WRONG  cached-refused-input"}]}'
set +e
harness_tmp="$work/harness-tmp"
mkdir -p "$harness_tmp"
: > "$work/targets.log"
out="$(cd "$repo" && CARGO_TARGET_DIR="$shared" TMPDIR="$harness_tmp" CACHED_LOG="$work/targets.log" \
  python3 tooling/mutate-gates.py 2>&1)"
rc=$?
set -e
cases=$((cases + 1))
if [ "$rc" -ne 0 ] || ! grep -qF '1 seen as accepted' <<<"$out"; then
  echo "WRONG  mutate-gates a shared CARGO_TARGET_DIR: expected the edit seen as accepted with exit 0, got exit $rc" >&2
  printf '%s\n' "$out" >&2
  exit 1
fi
cases=$((cases + 1))
if [ -n "$(ls -A "$shared")" ]; then
  echo "WRONG  mutate-gates a shared CARGO_TARGET_DIR: the harness built into the caller's target directory:" \
    "$(ls -A "$shared" | tr '\n' ' ')" >&2
  exit 1
fi
# Each run had a target directory of its own, in the harness's temporary directory, and none is left there.
cases=$((cases + 1))
used="$(sort -u "$work/targets.log")"
if [ "$(wc -l < "$work/targets.log" | tr -d ' ')" -lt 2 ] || [ "$(wc -l <<<"$used" | tr -d ' ')" -ne "$(wc -l < "$work/targets.log" | tr -d ' ')" ]; then
  echo "WRONG  mutate-gates target directories: expected one per run, at least two, got: $(tr '\n' ' ' < "$work/targets.log")" >&2
  exit 1
fi
cases=$((cases + 1))
for d in $used; do
  case "$d" in
    "$harness_tmp"/mutate-gates-target-*) ;;
    *) echo "WRONG  mutate-gates target directories: $d is not a target directory of the harness's own" >&2; exit 1 ;;
  esac
done
left="$(find "$harness_tmp" -maxdepth 1 -name 'mutate-gates-*' -print)"
if [ -n "$left" ]; then
  echo "WRONG  mutate-gates target directories: left behind after the run: $(tr '\n' ' ' <<<"$left")" >&2
  exit 1
fi

# A runner that is red before any edit: the harness stops and says so, and runs no edit.
write_edits '{"mutations": [{'"$edit"', "old": "exit 1", "new": "exit 0", "expect": "WRONG  refused-input"}]}'
printf 'exit 1\n' >> "$repo/runner.sh"
git -C "$repo" commit -q -a -m "broken runner"
harness 'a runner that is red before any edit' 1 'baseline FAIL' 'a baseline is red'
if grep -qF 'seen as accepted' <<<"$(cd "$repo" && python3 tooling/mutate-gates.py 2>&1)"; then
  echo "WRONG  mutate-gates: an edit was run against a red baseline" >&2
  exit 1
fi
cases=$((cases + 1))

echo "mutate-gates-cases: $cases cases (a red baseline, accepted, behaviour, message only and survived edits, listed and stale reasons, a wrong reason, an edit that does not apply, a build cache in a shared CARGO_TARGET_DIR, one target directory per run and none left behind) gave the expected result"
