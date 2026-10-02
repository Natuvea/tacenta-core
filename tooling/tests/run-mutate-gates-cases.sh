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

echo "mutate-gates-cases: $cases cases (a red baseline, accepted, behaviour, message only and survived edits, listed and stale reasons, a wrong reason, an edit that does not apply) gave the expected result"
