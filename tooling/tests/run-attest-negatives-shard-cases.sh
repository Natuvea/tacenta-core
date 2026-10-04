#!/usr/bin/env bash
# Negative controls for the sharding of `tacenta-proofs/scripts/check-attest-negatives.sh`.
#
# That script runs its cases in shards across the machine's cores, and a parent accepts the run only if the
# shards together show that every case ran once, in the shard its index selects, with the premise held in
# each shard's own worktree. A parent that accepts too much turns a slice that was never run into a green
# line, so each fault below is planted in a copy of the script, run on the real tree with the test seam
# `ATTEST_NEGATIVES_ONLY` (the first cases only), and must fail with the diagnostic of the check that
# notices it. The gate is the script as committed: commit a change to it before running this.
#
#   JOBS=1 and JOBS=4 accept the tree and report one count   the unplanted script, so a failure below is the plant's
#   a shard with the wrong modulus                           two equal slices swapped: every count is right, a case is run by no shard
#   every shard with the same wrong modulus                  the shards agree and each case is run once; the rule itself notices
#   every shard running the next shard's slice               each case is run once and the walks agree; the shard is not the owner
#   a case that reads what the one before it wrote           accepted in the shard of that case; refused when it is sent to another shard
#   a shard that runs no case and exits 0                    refused: it ran 0 cases, and the sum falls short
#   a shard that reports another total                       refused: the shards disagree
#   a shard that exits nonzero after a clean report          refused: its exit status
#   a wrong case inside a shard other than 0                 the WRONG line reaches the output, also when the shard exits 0
#                                                            or loses its label: the shard's list of cases marks the case wrong
#   two shards that report the same index                    refused: a shard names the wrong index
#   a shard killed with SIGKILL                              refused, and its worktree is removed by the parent
#   a shard that cannot enter its worktree                   the WRONG lines of its premise reach the output
#   a shard that skips the premise, or none runs it          refused: it checked less often than the premise comes up, or never
#   a shard that walks other cases than the rest             refused: the walks differ
#   an attest.py that is never run                           refused by the cases that expect a refusal
#   SIGINT and SIGTERM to the parent                         no worktree, process or directory is left
#   the seam and a hand-started shard in CI                  refused; a shard started by the parent is not
#   a partial run                                            never prints the line of a full run
#   the default number of shards                             the CPUs, at most 16, never below 1
#   a call of attest.py outside a counted helper             found in the text of the script, in four spellings (a call
#                                                            through eval, bash -c or a variable is not found, nor is python
#                                                            without the 3 or with a flag, nor a script run by its path)
#   the helpers that expect an acceptance                    each runs its tool: tools that refuse everything give a WRONG line from each
#   a refused run that wrote a file                          the check that follows it is a counted case, and the parent refuses
#   the environment of a single run or of the parent         a worktree directory, a revision and a list it does not read, and says so
#   a worktree add that git registered and then failed       the retry prunes it
#   the seam without its marker                              refused
#
# A fault that concerns only how the shards are shared out and reported is planted in a copy whose
# `attest.py` call is replaced by a stub that accepts, so that it takes seconds and not minutes. The stubbed
# copy without a plant is accepted first, and with a third case, which expects a refusal, it is refused
# (`never-run`), so the stub is seen to be a stub. The acceptance runs and the wrong case use the real
# `attest.py`. The cases run a few at a time, each in its own TMPDIR, and are judged one by one afterwards.
# As in the other runners of this directory the first case that goes wrong stops the run. Nothing here needs
# a Lean toolchain. The mutation harness reruns a runner with its `exit 1` and `set -e` lines removed, so the
# text of a plant never contains either.
set -euo pipefail

root="$(git rev-parse --show-toplevel)"
tmp_base="${TMPDIR:-/tmp}"
work="$(mktemp -d "$tmp_base/attest-shard-cases.XXXXXX")"
# The physical path: git prints worktrees by it, and this control compares those paths with its own.
work="$(cd "$work" && pwd -P)"
tree="$work/tree"
plants="$work/plants"
cleanup() {
  # A case still running when the control stops early (a plant that does not apply) is stopped first.
  if pgrep -f "$plants/" >/dev/null 2>&1; then
    pkill -TERM -f "$plants/" >/dev/null 2>&1 || true
    sleep 2
  fi
  git -C "$root" worktree remove --force "$tree" >/dev/null 2>&1 || true
  git -C "$root" worktree prune >/dev/null 2>&1 || true
  rm -rf "$work"
}
trap cleanup EXIT
git -C "$root" worktree add -q --detach "$tree" HEAD >/dev/null

gate="tacenta-proofs/scripts/check-attest-negatives.sh"
mkdir -p "$plants"
cases=0
full_line='each mutation refused for its stated reason'
attest_call='  (cd "$work" && env -u GITHUB_ACTIONS python3 tacenta-proofs/scripts/attest.py "$@" 2>&1)'
stub_call='  { (cd "$work" && echo "stub: attest.py $*"); } 2>&1'

# The number of cases run at once. The shards of one case already use two processes each.
parallel="$(getconf _NPROCESSORS_ONLN 2>/dev/null || echo 2)"
parallel=$((parallel / 2))
if [ "$parallel" -lt 1 ]; then parallel=1; fi
if [ "$parallel" -gt 4 ]; then parallel=4; fi
started=0

# fresh <name>: a copy of the script under test, which a plant may edit.
fresh() {
  cp "$tree/$gate" "$plants/$1.sh"
}

# plant <name> <old> <new>: replace a text that occurs exactly once in that copy.
plant() {
  python3 - "$plants/$1.sh" "$2" "$3" <<'PY' || exit 2
import pathlib, sys
path, old, new = pathlib.Path(sys.argv[1]), sys.argv[2], sys.argv[3]
text = path.read_text()
if text.count(old) != 1:
    raise SystemExit(f"control: {old!r} occurs {text.count(old)} times in the script under test; "
                     "this control is out of date with it")
path.write_text(text.replace(old, new))
PY
}

# stub <name>: make the attest.py call of that copy a call that accepts.
stub() {
  plant "$1" "$attest_call" "$stub_call"
}

# start <name> <jobs> <only> [VAR=value ...]: run the copy in the background in the real tree. The caller's
# CI and ATTEST_NEGATIVES_* variables are removed, so that only the ones given here are set.
start() {
  local name="$1" jobs="$2" only="$3"
  shift 3
  mkdir -p "$work/tmp-$name"
  (
    cd "${case_dir:-$tree}"
    set +e
    env -u GITHUB_ACTIONS -u ATTEST_NEGATIVES_JOBS -u ATTEST_NEGATIVES_ONLY -u ATTEST_NEGATIVES_SHARD \
      -u ATTEST_NEGATIVES_RESULTS -u ATTEST_NEGATIVES_WORKTREE -u ATTEST_NEGATIVES_REV -u ATTEST_NEGATIVES_PARENT -u ATTEST_NEGATIVES_TEST_ONLY -u ATTEST_NEGATIVES_SEAM \
      TMPDIR="$work/tmp-$name" ATTEST_NEGATIVES_JOBS="$jobs" ATTEST_NEGATIVES_ONLY="$only" \
      ATTEST_NEGATIVES_SEAM=tests-only "$@" \
      bash "$plants/$name.sh" > "$work/out-$name" 2>&1
    echo $? > "$work/rc-$name"
  ) &
  started=$((started + 1))
  while [ $((started - $(ls "$work" | grep -c '^rc-'))) -ge "$parallel" ]; do
    sleep 0.2
  done
}

wrong() {  # name message...
  local name="$1"
  shift
  echo "WRONG  shard control $name: $*" >&2
  if [ -f "$work/out-$name" ]; then
    sed 's/^/    | /' "$work/out-$name" >&2
  fi
  exit 1
}

# Whatever the case, the run leaves no directory in its TMPDIR and no registered worktree.
left_nothing() {
  local name="$1"
  if [ -n "$(ls -A "$work/tmp-$name")" ]; then
    wrong "$name" "left $(ls -A "$work/tmp-$name" | tr '\n' ' ') in its TMPDIR"
  fi
  if git -C "$tree" worktree list --porcelain | grep -qF "worktree $work/tmp-$name/"; then
    wrong "$name" "left a registered worktree"
  fi
}

# accepts <name>: the run succeeded, as a partial run, and says how many cases it covered.
accepts() {
  local name="$1"
  cases=$((cases + 1))
  if [ "$(cat "$work/rc-$name")" -ne 0 ]; then
    wrong "$name" "expected acceptance, was refused"
  fi
  if grep -qF -- "$full_line" "$work/out-$name"; then
    wrong "$name" "a partial run printed the line of a full run"
  fi
  if ! grep -q '^check-attest-negatives: PARTIAL RUN, not the gate (seam ATTEST_NEGATIVES_ONLY=[0-9]*): the first [0-9]* cases passed$' "$work/out-$name"; then
    wrong "$name" "the partial run did not end in its own line"
  fi
  left_nothing "$name"
}

# refuses <name> <needle>: the run failed, said the needle, and printed no line of success.
refuses() {
  local name="$1" needle="$2" out
  cases=$((cases + 1))
  out="$(cat "$work/out-$name")"
  if [ "$(cat "$work/rc-$name")" -eq 0 ]; then
    wrong "$name" "expected refusal containing '$needle', was accepted"
  fi
  if [[ "$out" != *"$needle"* ]]; then
    wrong "$name" "refused, but not for '$needle':"
  fi
  if grep -q 'PARTIAL RUN\|cases gave the expected result' "$work/out-$name"; then
    wrong "$name" "a refused run printed a line of success"
  fi
  left_nothing "$name"
}

# ---------------------------------------------------------------------------
# The unplanted script on the real tree, so that a failure below is the plant's. These are the slow runs,
# so they start first.
# ---------------------------------------------------------------------------

fresh jobs1
start jobs1 1 4
fresh jobs4
start jobs4 4 4

# (e) A case whose expected text does not occur, in shard 1: the fourth case, claimed-session-t1-without-pin.
planted_case='is not axiom-pinned'"'"' --check'
fresh wrong-case
plant wrong-case "$planted_case" 'is not axiom-pinned (planted)'"'"' --check'
start wrong-case 2 4

# A case that reads what the case before it wrote. Two cases are added after the premise: a regeneration of
# a stale manifest, and a `--check` of the regenerated manifest, written as the script writes such a case.
# With the follow-up in the shard of the regeneration the copy is accepted. Written as a plain case it goes
# to the other shard, whose worktree was never regenerated, and its `--check` is refused as stale.
follow_anchor='premise_pass "unmodified-translation" --check-translation
'
follow_pair='make_case
edit_json tacenta-proofs/manifests/source-commit-attestation.json '"'"'data["p9_mutation"] = "stale"'"'"'
expect_pass "regenerated-manifest"
expect_pass_after "regenerated-manifest-then-checked" --check
'
fresh follows
plant follows "$follow_anchor" "$follow_anchor$follow_pair"
start follows 2 4
fresh follow-lost
plant follow-lost "$follow_anchor" "$follow_anchor$follow_pair"
plant follow-lost '  if [ "${2:-}" = follows ] && [ "$case_index" -gt 0 ]; then' '  if false; then'
start follow-lost 2 4

# ---------------------------------------------------------------------------
# The planted faults, in copies with a stub for attest.py. Two shards and two cases are enough for each.
# ---------------------------------------------------------------------------

selects='    case_owner=$((case_index % jobs))'
runs='  if [ "$case_owner" -ne "$shard" ]; then'
report_line='    echo "shard $shard/$jobs: ran $ran of $seen"'

# The stubbed copy, unplanted; and with a third case, which expects a refusal.
fresh stubbed
stub stubbed
start stubbed 2 2
fresh never-run
stub never-run
start never-run 2 4

# A shard started by hand, as a run split over machines would: it reports and does not print a final line.
fresh handshard
stub handshard
start handshard 2 1 ATTEST_NEGATIVES_SHARD=0/2

# (a) Shard 1 selects the cases with the wrong modulus. With two cases and two shards each runs one, so
# every count is right, and the case shard 1 should run is run by no shard.
fresh modulus
stub modulus
plant modulus "$selects" '    case_owner=$(((case_index + (shard == 1 ? 1 : 0)) % jobs))'
start modulus 2 2

# (a') Every shard selects the cases with the same wrong modulus: the slices are swapped, each case is run
# once by the shard the list says, and the shards agree. Only the rule itself notices.
fresh swapped-slices
stub swapped-slices
plant swapped-slices "$selects" '    case_owner=$(((case_index + 1) % jobs))'
start swapped-slices 2 2

# (a'') Every shard runs the slice of the next shard, and the list still names the right owner: every case is
# run by exactly one shard and the shards agree, and only the shard that ran it differs from the owner.
fresh rotated-slices
stub rotated-slices
plant rotated-slices "$runs" '  if [ $(((case_owner + 1) % jobs)) -ne "$shard" ]; then'
start rotated-slices 2 2

# (b) Shard 1 runs no case and exits 0.
fresh runs-nothing
stub runs-nothing
plant runs-nothing "$runs" '  if [ "$shard" -eq 1 ] || [ "$case_owner" -ne "$shard" ]; then'
start runs-nothing 2 2

# (c) Shard 1 saw one case more than the others.
fresh other-total
stub other-total
plant other-total '    echo "shard $shard/$jobs: premise $premise of $premise_reached"' \
  '    if [ "$shard" -eq 1 ]; then seen=$((seen + 1)); fi
    echo "shard $shard/$jobs: premise $premise of $premise_reached"'
start other-total 2 2

# (d) Shard 1 reports cleanly and then exits 3.
fresh exits-three
stub exits-three
plant exits-three "$report_line" "$report_line"'
    if [ "$shard" -eq 1 ]; then exit 3; fi'
start exits-three 2 2

# (e') Shard 1 is refused by its attest.py and exits 0 whatever its cases gave: only its WRONG lines are
# left to notice.
fresh wrong-exit-0
stub wrong-exit-0
plant wrong-exit-0 "$stub_call" '  { (cd "$work" && echo "stub: attest.py $*" && [ "$shard" -ne 1 ]); } 2>&1'
plant wrong-exit-0 "$report_line" "$report_line"'
    if [ "$shard" -eq 1 ]; then exit 0; fi'
plant wrong-exit-0 '      verdict=wrong' '      verdict=ok'
start wrong-exit-0 2 2

# (e'') The same, with the WRONG label lost instead of the verdict: only the list of cases marks it.
fresh wrong-unlabelled
stub wrong-unlabelled
plant wrong-unlabelled "$stub_call" '  { (cd "$work" && echo "stub: attest.py $*" && [ "$shard" -ne 1 ]); } 2>&1'
plant wrong-unlabelled 'echo "WRONG  $1: expected acceptance, was refused:" >&2' 'echo "wrong  $1: expected acceptance, was refused:" >&2'
plant wrong-unlabelled "$report_line" "$report_line"'
    if [ "$shard" -eq 1 ]; then exit 0; fi'
start wrong-unlabelled 2 2

# (f) Shard 1 reports itself as shard 0.
fresh same-index
stub same-index
plant same-index "$report_line" \
  '    echo "shard $([ "$shard" -eq 1 ] && echo 0 || echo "$shard")/$jobs: ran $ran of $seen"'
start same-index 2 2

# (g) Shard 1 is killed with SIGKILL when it reaches its second case, which leaves its worktree behind.
fresh killed
stub killed
plant killed '  case_index=$seen
  case_name="$1"' '  case_index=$seen
  if [ "$shard" -eq 1 ] && [ "$case_index" -eq 1 ]; then kill -9 $$; fi
  case_name="$1"'
start killed 2 2

# (h) The `cd` into the worktree fails in shard 1.
fresh cd-fails
stub cd-fails
plant cd-fails "$stub_call" '  { (cd "$work$([ "$shard" -eq 1 ] && echo /absent)" && echo "stub: attest.py $*"); } 2>&1'
start cd-fails 2 2

# (i) Shard 1 does not check the premise for the case it does not own.
fresh premise-skipped
stub premise-skipped
plant premise-skipped '    owned=1
  fi' '    owned=1
  fi
  if [ "$owned" -eq 0 ] && [ "$shard" -eq 1 ]; then
    return 0
  fi'
start premise-skipped 2 2

# (i') No shard counts a premise check: the count of checks made is never raised.
fresh premise-never
stub premise-never
plant premise-never '  premise=$((premise + 1))' '  :'
start premise-never 2 2

# (i'') The premise checks are gone from the script: they are plain cases now.
fresh premise-gone
stub premise-gone
plant premise-gone 'premise_pass "unmodified-tree" --check
premise_pass "unmodified-translation" --check-translation
' 'expect_pass "unmodified-tree" --check
expect_pass "unmodified-translation" --check-translation
'
start premise-gone 2 2

# (q) Shard 1 walks a case that the others name differently.
fresh other-walk
stub other-walk
plant other-walk '  case_name="$1"
  seen=$((seen + 1))' '  case_name="$1$([ "$shard" -eq 1 ] && [ "$seen" -eq 1 ] && echo x)"
  seen=$((seen + 1))'
start other-walk 2 2

# The seam in CI is refused, and so is a shard started by hand; a shard started by the parent is not. The two
# copies below take the length of the walk from another variable, set after the check that refuses the seam,
# so that a parent in CI can be run on a short walk.
only_anchor='is_shard=0
shard=0
jobs=1
'
only_from_test='only="${ATTEST_NEGATIVES_TEST_ONLY:-}"
'
fresh ci-seam
stub ci-seam
start ci-seam 2 2 GITHUB_ACTIONS=true
fresh ci-hand-shard
stub ci-hand-shard
plant ci-hand-shard "$only_anchor" "$only_from_test$only_anchor"
start ci-hand-shard 2 "" GITHUB_ACTIONS=true ATTEST_NEGATIVES_SHARD=0/2 ATTEST_NEGATIVES_TEST_ONLY=1
fresh ci-parent
stub ci-parent
plant ci-parent "$only_anchor" "$only_from_test$only_anchor"
start ci-parent 2 "" GITHUB_ACTIONS=true ATTEST_NEGATIVES_TEST_ONLY=2

# The seam is read only with its marker.
fresh no-marker
stub no-marker
start no-marker 2 2 ATTEST_NEGATIVES_SEAM=

# Only a shard reads the worktree, the revision and the list of cases from the environment. The single run
# and the parent are given a directory that holds a file, a revision that does not exist and a list in a
# directory that does not: they ignore all three and say so, and the directory keeps its file. A shard started
# by hand is refused a directory that is not empty.
mkdir -p "$work/victim/sub" "$work/victim2/sub"
echo kept > "$work/victim/sub/file.txt"
echo kept > "$work/victim2/sub/file.txt"
stale_rev=0123456789abcdef0123456789abcdef01234567
fresh single-env
stub single-env
start single-env 1 2 ATTEST_NEGATIVES_WORKTREE="$work/victim" ATTEST_NEGATIVES_REV="$stale_rev" \
  ATTEST_NEGATIVES_RESULTS="$work/absent-directory/list"
fresh parent-env
stub parent-env
start parent-env 2 2 ATTEST_NEGATIVES_WORKTREE="$work/victim" ATTEST_NEGATIVES_REV="$stale_rev" \
  ATTEST_NEGATIVES_RESULTS="$work/absent-directory/list"
fresh shard-nonempty
stub shard-nonempty
plant shard-nonempty "$only_anchor" "$only_from_test$only_anchor"
start shard-nonempty 2 "" ATTEST_NEGATIVES_SHARD=0/2 ATTEST_NEGATIVES_TEST_ONLY=1 ATTEST_NEGATIVES_WORKTREE="$work/victim2"

# A worktree add that git registered and then failed: the retry has to prune it. The first add of the run is
# made to fail after the real one has registered the worktree.
real_git="$(command -v git)"
mkdir -p "$work/gitshim"
cat > "$work/gitshim/git" <<SHIM
#!/bin/sh
case " \$* " in
  *" worktree add "*)
    if [ ! -e "$work/gitshim-failed" ]; then
      : > "$work/gitshim-failed"
      "$real_git" "\$@"
      exit 128
    fi ;;
esac
exec "$real_git" "\$@"
SHIM
chmod +x "$work/gitshim/git"
# It runs in a clone of its own: the parent of another case prunes the stale registrations of the repository it
# shares, which would hide the failure that the retry has to survive.
git clone -q --no-hardlinks "$tree" "$work/retry-repo"
git -C "$work/retry-repo" checkout -q --detach "$(git -C "$tree" rev-parse HEAD)"
fresh retry-registered
stub retry-registered
case_dir="$work/retry-repo" start retry-registered 1 2 PATH="$work/gitshim:$PATH"

# The parent finds no count of cases, or a shard cannot write its list of cases.
fresh no-total
stub no-total
plant no-total '    total="$(cat "$parent_logs/total")"' '    total="$(cat "$parent_logs/total-absent" 2>/dev/null || true)"'
start no-total 2 2
fresh list-unwritable
stub list-unwritable
plant list-unwritable '      ATTEST_NEGATIVES_RESULTS="$parent_logs/results-$i" \' \
  '      ATTEST_NEGATIVES_RESULTS="$([ "$i" -eq 1 ] && echo "$parent_logs" || echo "$parent_logs/results-$i")" \'
start list-unwritable 2 2

# A refused run must leave a file alone, and the check of that is a case of its own that follows the run: it
# is accepted when the file is as it was, and the parent refuses the run when the file was written. A
# follower that is assigned to another shard than the case it follows is refused by the rule alone.
unchanged_pair='make_case
expect_fail "refused-run" "stub refused" --refresh-translation
expect_unchanged "refused-run-wrote-nothing" "$record"
'
fresh unchanged-ok
stub unchanged-ok
plant unchanged-ok "$stub_call" '  { (cd "$work" && echo "stub refused: $*" && case "$*" in *--refresh-translation*) false;; esac); } 2>&1'
plant unchanged-ok "$follow_anchor" "$follow_anchor$unchanged_pair"
start unchanged-ok 2 4
fresh unchanged-written
stub unchanged-written
plant unchanged-written "$stub_call" '  { (cd "$work" && echo "stub refused: $*" && case "$*" in *--refresh-translation*) echo x >> "$record"; false;; esac); } 2>&1'
plant unchanged-written "$follow_anchor" "$follow_anchor$unchanged_pair"
start unchanged-written 2 4
fresh follows-misowned
stub follows-misowned
plant follows-misowned "$follow_anchor" "$follow_anchor$follow_pair"
plant follows-misowned '    case_kind=follows
' '    case_kind=follows
    case_owner=$((case_index % jobs))
'
start follows-misowned 2 4

while [ $((started - $(ls "$work" | grep -c '^rc-'))) -gt 0 ]; do
  sleep 0.2
done

accepts jobs1
accepts jobs4
accepts follows
# One count: the same line from the single run and from four shards.
cases=$((cases + 1))
if [ "$(tail -n 1 "$work/out-jobs1")" != "$(tail -n 1 "$work/out-jobs4")" ]; then
  wrong jobs4 "the single run and four shards did not report the same count"
fi
accepts stubbed
accepts ci-parent
accepts unchanged-ok

# The single run and the parent ignore what only a shard reads, say so, and leave the directory alone.
for name in single-env parent-env; do
  accepts "$name"
  cases=$((cases + 1))
  for variable in ATTEST_NEGATIVES_REV ATTEST_NEGATIVES_RESULTS ATTEST_NEGATIVES_WORKTREE; do
    if ! grep -qF "ignoring $variable, which only a shard reads" "$work/out-$name"; then
      wrong "$name" "did not say that it ignores $variable"
    fi
  done
  if [ "$(cat "$work/victim/sub/file.txt")" != kept ]; then
    wrong "$name" "the directory in ATTEST_NEGATIVES_WORKTREE lost its file"
  fi
done
accepts retry-registered
cases=$((cases + 1))
if [ ! -e "$work/gitshim-failed" ]; then
  wrong retry-registered "the first worktree add was not made to fail"
fi
if [ "$(git -C "$work/retry-repo" worktree list | wc -l | tr -d ' ')" != 1 ]; then
  wrong retry-registered "left a registered worktree in its repository"
fi

cases=$((cases + 1))
if [ "$(cat "$work/rc-handshard")" -ne 0 ] || ! grep -qx 'shard 0/2: ran 1 of 1' "$work/out-handshard" \
   || grep -q 'PARTIAL RUN\|cases gave the expected result' "$work/out-handshard"; then
  wrong handshard "a hand-started shard must report and print no final line"
fi
left_nothing handshard

refuses wrong-case "WRONG  claimed-session-t1-without-pin: refused, but not for"
refuses follow-lost "WRONG  regenerated-manifest-then-checked: expected acceptance, was refused"
refuses never-run "WRONG  missing-claimed-theorem: expected refusal containing"
refuses modulus "was run by no shard"
refuses runs-nothing "shard 1/2 ran 0 of 2 cases"
refuses other-total "the shards disagree on the number of cases"
refuses exits-three "shard 1/2 exited with status 3"
refuses wrong-exit-0 "shard 1/2 printed 2 WRONG line(s)"
refuses same-index "shard 1/2 reported itself as shard 0/2"
refuses killed "shard 1/2 exited with status 137"
refuses cd-fails "WRONG  unmodified-tree: expected acceptance, was refused"
refuses premise-skipped "shard 1/2 checked that its worktree accepts the unmodified tree 1 time(s) of the 2 it reaches"
refuses premise-never "checked that its worktree accepts the unmodified tree 0 time(s) of the 2 it reaches"
refuses premise-gone "shard 0/2 reaches no premise check"
refuses swapped-slices "case 0 (unmodified-tree) is assigned to shard 1, not to shard 0, which its index selects"
refuses rotated-slices "shard 0/2 ran or skipped 2 case(s) against its slice, the first being case 0 (unmodified-tree)"
refuses wrong-unlabelled "shard 1/2 marks case 1 (unmodified-translation) wrong"
refuses other-walk "walked different cases from shard 0/2"
refuses ci-seam "so CI refuses it"
refuses ci-hand-shard "so CI refuses ATTEST_NEGATIVES_SHARD"
refuses no-marker "read only with ATTEST_NEGATIVES_SEAM=tests-only"
refuses shard-nonempty "is not an empty directory"
cases=$((cases + 1))
if [ "$(cat "$work/victim2/sub/file.txt" 2>/dev/null)" != kept ]; then
  wrong shard-nonempty "the directory that was refused lost its file"
fi
refuses no-total "the verification left no count of cases"
refuses list-unwritable "cannot write the list of cases to"
refuses unchanged-written "was written by the run before it"
refuses follows-misowned "follows the case before it and is assigned to shard"

# ---------------------------------------------------------------------------
# Every call that runs attest.py or another script is in a helper that counts the case first. A call outside
# one would run in every shard, uncounted, and the parent could not tell. The text of the script is read:
# each use of `attest`, `attest_in_ci` or `run_script` as a command (a substitution, a bare call, a line
# repeated in another function) must be inside a function whose body calls `begin_case`, and `python3` is
# run on `attest.py` by the two wrappers and by nothing else.
# ---------------------------------------------------------------------------

static_check() {  # file: prints each call that is not in a counted helper
  python3 - "$1" <<'PY'
import re, sys
lines = open(sys.argv[1], encoding="utf-8").read().split("\n")
problems, function, bodies, owner_of = [], None, {}, {}
for number, line in enumerate(lines, 1):
    opened = re.match(r"^([a-z_]+)\(\) \{", line)
    if opened:
        function = opened.group(1)
        bodies[function] = []
    if function is not None:
        bodies[function].append(line)
        owner_of[number] = function
    if line == "}":
        function = None
    stripped = line.strip()
    if stripped.startswith("#"):
        continue
    if (re.search(r"(^|[\s(;&|`$\"])(attest|attest_in_ci|run_script)(\s|\)|\"|$)", stripped)
            and not re.match(r"^(attest|attest_in_ci|run_script)\(\) \{", stripped)):
        owner = owner_of.get(number)
        if owner is None or not any("begin_case" in l for l in bodies[owner]):
            problems.append(f"line {number}: {stripped} is not in a helper that calls begin_case")
    if re.search(r"python3\s+\"?[^ ]*attest\.py", line) and owner_of.get(number) not in ("attest", "attest_in_ci"):
        problems.append(f"line {number}: attest.py is run outside the two wrappers: {stripped}")
print("\n".join(problems))
PY
}

cases=$((cases + 1))
found="$(static_check "$tree/$gate")"
if [ -n "$found" ]; then
  echo "WRONG  shard control static: a call of attest.py or of a script is not counted:" >&2
  printf '%s\n' "$found" >&2
  exit 1
fi
# Four spellings of an uncounted call, each appended to a copy of the script and each found.
static_spelling() {  # name text
  cp "$tree/$gate" "$plants/static-$1.sh"
  printf '\n%s\n' "$2" >> "$plants/static-$1.sh"
  cases=$((cases + 1))
  if [ -z "$(static_check "$plants/static-$1.sh")" ]; then
    echo "WRONG  shard control static: an uncounted call written as $1 was not found" >&2
    exit 1
  fi
}
static_spelling substitution 'out="$(attest --check)"'
static_spelling bare-call 'attest --check >/dev/null'
static_spelling repeated-line 'sneaky() {
  out="$(attest "$@")"
}'
static_spelling python-on-the-path 'python3 "$work/tacenta-proofs/scripts/attest.py" --check'

# ---------------------------------------------------------------------------
# Helpers that expect an acceptance must run their tool. A reduced copy of the script has tools that refuse
# everything; one call of each such helper must give a WRONG line, and a helper that ran nothing would give
# none. The same for a check that a run left a file alone: a tool writes the file, and the check must object.
# ---------------------------------------------------------------------------

python3 - "$tree/$gate" "$plants/canary.sh" <<'PY'
import pathlib, sys
text = pathlib.Path(sys.argv[1]).read_text()
head = text[:text.index('make_case\npremise_pass "unmodified-tree" --check')]
refuse = '{ (cd "$work" && echo "tool refused" && false); } 2>&1'
for call in ('(cd "$work" && env -u GITHUB_ACTIONS python3 tacenta-proofs/scripts/attest.py "$@" 2>&1)',
             '(cd "$work" && env -u GITHUB_ACTIONS bash "tacenta-proofs/scripts/$1" 2>&1)',
             '(cd "$work" && GITHUB_ACTIONS=true python3 tacenta-proofs/scripts/attest.py "$@" 2>&1)'):
    assert head.count(call) == 1, call
    head = head.replace(call, refuse)
body = """make_case
premise_pass "canary-premise" --check
expect_pass "canary-pass" --check
expect_pass_after "canary-after" --check
expect_pass_saying "canary-saying" "x" --check
expect_script_pass "canary-script-pass" check-lean-constructs.sh
(cd "$work" && echo x >> "$record")
expect_unchanged "canary-unchanged" "$record"
finish
"""
pathlib.Path(sys.argv[2]).write_text(head + body)
PY
mkdir -p "$work/tmp-canary"
(cd "$tree" && env -u GITHUB_ACTIONS TMPDIR="$work/tmp-canary" ATTEST_NEGATIVES_JOBS=1 bash "$plants/canary.sh") \
  > "$work/out-canary" 2>&1 || true
for name in canary-premise canary-pass canary-after canary-saying canary-script-pass canary-unchanged; do
  cases=$((cases + 1))
  if ! grep -q "^WRONG  $name:" "$work/out-canary"; then
    wrong canary "the helper of $name did not run its tool or did not check what it left"
  fi
done

# ---------------------------------------------------------------------------
# The default number of shards is the number of CPUs, at most 16, and never below 1. The function is read from
# the script and run with stand-ins for `getconf` and `nproc`.
# ---------------------------------------------------------------------------

sed -n '/^default_jobs() {/,/^}/p' "$tree/$gate" > "$work/default-jobs.sh"
default_jobs_for() {  # getconf-prints nproc-prints want
  local shim="$work/shim-$1-$2"
  mkdir -p "$shim"
  for tool in getconf nproc; do
    value="$1"
    if [ "$tool" = nproc ]; then value="$2"; fi
    if [ "$value" = absent ]; then
      printf '#!/bin/sh\nfalse\n' > "$shim/$tool"
    else
      printf '#!/bin/sh\necho %s\n' "$value" > "$shim/$tool"
    fi
    chmod +x "$shim/$tool"
  done
  cases=$((cases + 1))
  got="$(PATH="$shim:$PATH" bash -c 'source "$1"; default_jobs' _ "$work/default-jobs.sh")"
  if [ "$got" != "$3" ]; then
    wrong default-jobs "getconf $1 and nproc $2 gave $got shards, expected $3"
  fi
}
default_jobs_for 4 absent 4
default_jobs_for 16 absent 16
default_jobs_for 17 absent 16
default_jobs_for 64 absent 16
default_jobs_for 0 absent 1
default_jobs_for absent 6 6

# ---------------------------------------------------------------------------
# A signal to the parent mid-run: the shards and what they started stop, and nothing is left behind. The
# attest.py call sleeps, so that the signal arrives while every shard is inside it. The parent is started
# by Python, which does not make it ignore SIGINT as a background job of a shell would.
# ---------------------------------------------------------------------------

signal_case() {  # name signal expected-exit-status
  local name="$1" signal="$2" want="$3" rc
  fresh "$name"
  stub "$name"
  plant "$name" 'echo "stub: attest.py $*"' 'sleep 60; echo "stub: attest.py $*"'
  mkdir -p "$work/tmp-$name"
  set +e
  python3 - "$tree" "$plants/$name.sh" "$work/tmp-$name" "$work/out-$name" "$signal" <<'PY'
import os, signal, subprocess, sys, time
tree, script, tmp, out, sig = sys.argv[1:6]
env = {k: v for k, v in os.environ.items() if not k.startswith("ATTEST_NEGATIVES_") and k != "GITHUB_ACTIONS"}
env.update(TMPDIR=tmp, ATTEST_NEGATIVES_JOBS="4", ATTEST_NEGATIVES_ONLY="4", ATTEST_NEGATIVES_SEAM="tests-only")
# A control started in the background of a shell inherits SIGINT as ignored, and an ignored signal cannot be
# trapped by the script it is passed to; the parent under test gets the default disposition.
child = subprocess.Popen(["bash", script], cwd=tree, env=env, stdout=open(out, "w"), stderr=subprocess.STDOUT,
                         preexec_fn=lambda: [signal.signal(s, signal.SIG_DFL) for s in (signal.SIGINT, signal.SIGTERM)])
deadline = time.time() + 120
while time.time() < deadline:
    listing = subprocess.run(["git", "-C", tree, "worktree", "list", "--porcelain"],
                             capture_output=True, text=True).stdout
    if listing.count("worktree " + tmp + "/") >= 4:
        break
    time.sleep(0.2)
else:
    child.kill()
    sys.exit("control: the four shards never registered their worktrees")
time.sleep(3)   # every shard is inside its first call of attest.py
child.send_signal(getattr(signal, sig))
try:
    code = child.wait(timeout=120)
except subprocess.TimeoutExpired:
    child.kill()
    sys.exit("control: the parent did not stop within two minutes of the signal")
open(out + ".rc", "w").write(str(code) + "\n")
PY
  rc=$?
  set -e
  cases=$((cases + 1))
  if [ "$rc" -ne 0 ]; then
    wrong "$name" "the control could not deliver the signal"
  fi
  if [ "$(cat "$work/out-$name.rc")" != "$want" ]; then
    wrong "$name" "the parent exited with status $(cat "$work/out-$name.rc"), expected $want"
  fi
  left_nothing "$name"
  if pgrep -f "$plants/$name.sh" >/dev/null 2>&1; then
    wrong "$name" "a process of the run is still alive"
  fi
}

signal_case sigterm SIGTERM 143
signal_case sigint SIGINT 130

# Every worktree these cases registered is gone: only the repository's own and this control's remain.
leftover="$(git -C "$tree" worktree list --porcelain | grep -F "worktree $work/" | grep -vF "worktree $tree" || true)"
if [ -n "$leftover" ]; then
  echo "WRONG  shard control: worktrees left registered: $leftover" >&2
  exit 1
fi

echo "attest-negatives-shard-cases: $cases cases (JOBS=1 and JOBS=4 agree; the environment a shard alone reads, a worktree add that fails after it registered, the seam without its marker, a refused run that wrote a file, the helpers that expect an acceptance; a wrong modulus in one shard or in all, a shard that runs nothing, a different total, an exit status, a wrong case with and without its label, a repeated index, a killed shard, a failed cd, the premise skipped, never run or gone, a different walk, a case that reads the one before it, an attest.py never run, the seam and a hand-started shard in CI, SIGINT and SIGTERM) gave the expected result"
