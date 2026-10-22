#!/usr/bin/env bash
# Hold the claim and source-attestation gate to representative mutations.
#
# `attest.py` is intentionally rooted at its own repository path, so each
# mutation runs in a disposable detached worktree instead of changing the
# caller's tree. A worktree is made once per process and reset between cases.
# The expected diagnostic is part of every case: a nonzero exit alone could be
# caused by an unrelated stale manifest. The first check is that the unmodified
# tree is accepted, because a refusal is only evidence if acceptance is
# possible.
#
# The cases are grouped by what they hold:
#   claims and manifests   -- the claim ledger, the three manifests
#   translation record     -- the generated files against their recorded hashes
#   axiom allowlist        -- every axiom a generated file declares, by
#                             qualified name and type, as a multiset
#   scanner forms          -- spellings of a declaration that the text scan has
#                             to read the same way as the plain one
#   audit comparison       -- `--compare-audit` against the environment's list
#   allowlist writer       -- the only writer of the allowlist
#   construct scanner      -- `check-lean-constructs.sh` reads the same spellings
#   pin lists              -- a required pin deleted or left in a comment, a
#                             compiler-trust pin the script does not list, a
#                             pin block copied over another
#   statement pins         -- a required statement pin deleted, commented out,
#                             moved into a docstring or a string, left without
#                             its `#guard_msgs`, given an option that compares
#                             nothing, nested under another `... in`, written
#                             inside a namespace (also one that a `mutual` block
#                             follows), moved to a module no audit imports,
#                             dropped from the floor, or the floor's record
#                             missing, unreadable, keyless or emptied
#
# Sharding. Every case runs `attest.py` (or `check-lean-constructs.sh`) once, and
# that is where the time goes: it reads and hashes the tree. The cases are
# independent, so the run is spread over the machine's cores.
#
#   ATTEST_NEGATIVES_JOBS=N   the number of shards. The default is the number
#                             of CPUs (`getconf _NPROCESSORS_ONLN`), at most 16;
#                             an explicit value may be up to 64. 1 is the single
#                             in-process run, with no child process.
#
# With N above 1 this script is the parent. It starts N copies of itself, each
# with `ATTEST_NEGATIVES_SHARD=i/N`, its own worktree and its own log, waits for
# all of them, and accepts nothing that the shards do not show together. A shard
# walks every case in the same order and makes every case's mutation, so a
# mutation that no longer applies stops every shard, but it runs `attest.py`
# only for the cases whose global index (counted from 0) satisfies
# `index % N == i`. Every call that runs `attest.py` or another script of this
# directory goes through `begin_case`, which counts the case and says whether
# this shard runs it: the `expect_*` helpers and `premise_pass` below. Nothing
# else in this file runs one, and a new kind of case has to go through it too.
# So does a check that a refused run left a file alone (`expect_unchanged`): it
# is a case of its own, listed and counted, and goes to the shard of the run
# before it. That puts the check inside the counting: the per-case lists and the
# totals cover it, and a shard that skips it is refused. Deleting one of the
# two calls lowers the count of a full run by one, which the pinned case count
# (see below) refuses, as it refuses deleting any case, unless the same change
# updates the count.
#
# A case may read what the case before it wrote into the worktree: a `--check`
# of what a regeneration has just rewritten. Another shard's worktree holds
# none of that, so such a case is written with `expect_pass_after`, and goes to
# the shard of the case before it instead of the shard its index selects.
#
# What the parent requires, and prints the final line only if all of it holds:
#   - every shard exited 0 and printed no line beginning `WRONG`;
#   - every shard printed `shard i/N: ran R of T` once, with its own i and N,
#     the same T as the others, R above 0, and the R values add up to T;
#   - every shard printed `shard i/N: premise P of Q`, with Q above 0, the same
#     Q as the others and P equal to Q: the unmodified tree is accepted in every
#     shard's own worktree, because a refusal in a worktree is evidence only if
#     that worktree accepts;
#   - the list of cases each shard walked (the file named by
#     ATTEST_NEGATIVES_RESULTS, one line per case) is the same list in every
#     shard, each case is assigned to the shard its index selects (or, for a
#     case that follows, to the shard of the case before it), and each case is
#     marked as run by exactly one shard, the one it is assigned to. The counts
#     alone cannot show this: two shards of equal size that swap slices leave
#     every count right and skip a slice.
# On the first INT or TERM the parent stops each shard and what it started,
# waits up to ten seconds and then kills what is left, removes the shards'
# worktrees, prunes, and removes its logs. It does the same when the run ends
# and when a shard was killed. A second signal while it is cleaning up ends the
# parent at once, and so does KILL; either can leave shards running (each
# carries on with its walk until it ends), their worktrees and the logs
# directory. A shard started by hand (`ATTEST_NEGATIVES_SHARD=i/N`, for a split
# the caller combines by hand) prints only its report lines; combining those is
# then the caller's job, and CI refuses it. CI splits a run with the slices below.
#
# Only a shard reads ATTEST_NEGATIVES_WORKTREE, ATTEST_NEGATIVES_REV and
# ATTEST_NEGATIVES_RESULTS; the single run and the parent ignore them and say so,
# and a shard refuses a worktree directory that is not empty. The script removes
# only directories it made, or that it found empty.
#
# Slices. CI splits the run over machines, and does it through two modes of this
# script rather than through shards started by hand:
#
#   ATTEST_NEGATIVES_SLICE=k/K      slice k of K (k from 0). It is a parent of L
#   ATTEST_NEGATIVES_SLICE_DIR=d    shards (ATTEST_NEGATIVES_JOBS, or the default
#                                   above), and those are the shards k*L to
#                                   k*L+L-1 of a run of N = K*L shards, so that a
#                                   case goes to the shard `index % N` as in a
#                                   run on one machine. It gives no verdict on
#                                   the gate: it fails when one of its shards
#                                   exited nonzero or printed a WRONG line, and
#                                   otherwise writes into d, which must be empty
#                                   or absent, each shard's exit status, log and
#                                   list of cases, named by the shard's index in
#                                   the run, and `slice.json`: k, K, L, N, the
#                                   first shard, the commit and tree it ran on,
#                                   the sha256 of this script, and the length of
#                                   the walk when the test seam cut it.
#   ATTEST_NEGATIVES_COMBINE=d      the combiner: d holds exactly K slice
#   ATTEST_NEGATIVES_SLICES=K       directories, one per slice. It requires one K,
#                                   one L, every slice from 0 to K-1 once, each
#                                   with exactly the files of its own shards, the
#                                   commit and tree the combiner has checked out,
#                                   this script's sha256, and the walk length of
#                                   the combiner (a full walk, unless the seam is
#                                   set for both). It then gathers the shards'
#                                   files and holds them to `verify_shards`, the
#                                   check the parent above makes, with N shards,
#                                   and prints the final line of a full run only
#                                   if that holds too. It refuses
#                                   ATTEST_NEGATIVES_JOBS: N comes from the slices.
#
# CI may run both modes (a slice starts its own shards, so their parent check
# passes) and still refuses a shard started by hand and the test seam. The
# manifest is written by the slice about itself: the combiner can tell a slice
# of another commit, script or split, a slice missing, repeated, cut short or
# relabelled, but not a slice directory written to look right by something
# other than this script. The workflow runs the slices and the combiner in one
# run of one workflow, and the combiner downloads only that run's artifacts.
#
# Test seam. `ATTEST_NEGATIVES_ONLY=n` stops the walk after the first n cases,
# so that tooling/tests/run-attest-negatives-shard-cases.sh can exercise the
# sharding without the full run. It is read only together with
# `ATTEST_NEGATIVES_SEAM=tests-only`, which that control sets. A run that used
# it ends in a line that begins `PARTIAL RUN` and never prints the line of a full
# run, and CI refuses the variable (GITHUB_ACTIONS is set), so a partial run
# cannot stand for the gate.
#
# The case count. The number of cases of a full run must equal the number in
# `tacenta-proofs/scripts/attest-negatives-case-count.txt` (one whole number),
# which the single run, the parent and the combiner read from the tree they
# check before they print the final line; a run under the test seam does not
# read it. A walk that ends early, a block moved below `finish`, a deleted case
# or a case added without the count then fails, so every change to the number
# of cases carries a one-line diff of that file: **a change that adds or
# removes negative cases updates it.** The count catches a walk cut short and a
# walk padded, not a case replaced by another: a change that removes one case
# and adds another keeps the count. The number to write is what
#
#   ATTEST_NEGATIVES_COUNT=1 bash tacenta-proofs/scripts/check-attest-negatives.sh
#
# prints: it walks every case and makes its mutation in one process, runs no
# tool, and prints only the count, never a line of a run. CI refuses it, as it
# refuses the test seam, because it runs no case.
set -euo pipefail

self="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/$(basename "${BASH_SOURCE[0]}")"
root="$(git rev-parse --show-toplevel)"
tmp_base="${TMPDIR:-/tmp}"

usage_error() {
  echo "check-attest-negatives: $*" >&2
  exit 2
}

# A whole number from the environment, read in base 10 whatever its leading zeros.
whole_number() {
  [[ "$2" =~ ^[0-9]{1,6}$ ]] || usage_error "$1 must be a whole number, not '$2'"
  echo $((10#$2))
}

default_jobs() {
  local n
  n="$(getconf _NPROCESSORS_ONLN 2>/dev/null || true)"
  case "$n" in
    ''|*[!0-9]*) n="$(nproc 2>/dev/null || sysctl -n hw.ncpu 2>/dev/null || echo 1)" ;;
  esac
  case "$n" in
    ''|*[!0-9]*|0) n=1 ;;
  esac
  if [ "$n" -gt 16 ]; then
    n=16
  fi
  echo "$n"
}

count_file="$root/tacenta-proofs/scripts/attest-negatives-case-count.txt"

count_only=0
if [ -n "${ATTEST_NEGATIVES_COUNT:-}" ]; then
  [ "$ATTEST_NEGATIVES_COUNT" = 1 ] || usage_error "ATTEST_NEGATIVES_COUNT is 1 or unset, not '$ATTEST_NEGATIVES_COUNT'"
  [ -z "${GITHUB_ACTIONS:-}" ] || usage_error "ATTEST_NEGATIVES_COUNT walks the cases and runs none, so CI refuses it"
  for variable in ATTEST_NEGATIVES_SHARD ATTEST_NEGATIVES_SLICE ATTEST_NEGATIVES_COMBINE ATTEST_NEGATIVES_JOBS; do
    [ -z "${!variable:-}" ] \
      || usage_error "ATTEST_NEGATIVES_COUNT walks the cases in one process and runs none, so it does not take $variable"
  done
  count_only=1
fi

only=""
if [ -n "${ATTEST_NEGATIVES_ONLY:-}" ]; then
  only="$(whole_number ATTEST_NEGATIVES_ONLY "$ATTEST_NEGATIVES_ONLY")"
  [ "$only" -ge 1 ] || usage_error "ATTEST_NEGATIVES_ONLY must be at least 1"
  [ -z "${GITHUB_ACTIONS:-}" ] \
    || usage_error "ATTEST_NEGATIVES_ONLY stops the run after its first cases, so CI refuses it"
  [ "${ATTEST_NEGATIVES_SEAM:-}" = tests-only ] \
    || usage_error "ATTEST_NEGATIVES_ONLY is a test seam that makes a partial run; it is read only with ATTEST_NEGATIVES_SEAM=tests-only"
fi

is_shard=0
shard=0
jobs=1
is_slice=0      # this run is one slice of a run split over machines
slice=0
slices=0
slice_dir=""
combine_dir=""  # this run is the combiner of the slices in this directory
shard_first=0   # the global index of the first shard this parent starts
shard_count=0   # how many shards it starts: all of them, or a slice's
if [ -n "${ATTEST_NEGATIVES_SLICE:-}" ] || [ -n "${ATTEST_NEGATIVES_COMBINE:-}" ]; then
  [ -z "${ATTEST_NEGATIVES_SHARD:-}" ] \
    || usage_error "ATTEST_NEGATIVES_SHARD is set by the parent of a shard; a slice or the combiner does not take it"
  { [ -z "${ATTEST_NEGATIVES_SLICE:-}" ] || [ -z "${ATTEST_NEGATIVES_COMBINE:-}" ]; } \
    || usage_error "a run is a slice (ATTEST_NEGATIVES_SLICE) or the combiner (ATTEST_NEGATIVES_COMBINE), not both"
fi
if [ -n "${ATTEST_NEGATIVES_SLICE:-}" ]; then
  [[ "$ATTEST_NEGATIVES_SLICE" =~ ^([0-9]{1,6})/([0-9]{1,6})$ ]] \
    || usage_error "ATTEST_NEGATIVES_SLICE must look like 2/8, not '$ATTEST_NEGATIVES_SLICE'"
  slice=$((10#${BASH_REMATCH[1]}))
  slices=$((10#${BASH_REMATCH[2]}))
  { [ "$slices" -ge 1 ] && [ "$slice" -lt "$slices" ]; } \
    || usage_error "ATTEST_NEGATIVES_SLICE=$ATTEST_NEGATIVES_SLICE is not a slice of a run"
  slice_dir="${ATTEST_NEGATIVES_SLICE_DIR:-}"
  [ -n "$slice_dir" ] || usage_error "a slice writes its shards' reports to ATTEST_NEGATIVES_SLICE_DIR, which is not set"
  if [ -e "$slice_dir" ] && { [ ! -d "$slice_dir" ] || [ -n "$(ls -A "$slice_dir" 2>/dev/null)" ]; }; then
    usage_error "ATTEST_NEGATIVES_SLICE_DIR=$slice_dir is not an empty directory"
  fi
  if [ -n "${ATTEST_NEGATIVES_JOBS:-}" ]; then
    shard_count="$(whole_number ATTEST_NEGATIVES_JOBS "$ATTEST_NEGATIVES_JOBS")"
    { [ "$shard_count" -ge 1 ] && [ "$shard_count" -le 64 ]; } || usage_error "ATTEST_NEGATIVES_JOBS must be from 1 to 64"
  else
    shard_count="$(default_jobs)"
  fi
  # The shards of all the slices are the shards of one run: slice k starts the global shards k*L to k*L+L-1 of
  # N = K*L, so the rule that a case goes to the shard `index % N` is the rule of a run on one machine.
  jobs=$((slices * shard_count))
  [ "$jobs" -le 1024 ] || usage_error "ATTEST_NEGATIVES_SLICE and ATTEST_NEGATIVES_JOBS make $jobs shards, more than 1024"
  shard_first=$((slice * shard_count))
  is_slice=1
elif [ -n "${ATTEST_NEGATIVES_COMBINE:-}" ]; then
  combine_dir="$ATTEST_NEGATIVES_COMBINE"
  [ -d "$combine_dir" ] || usage_error "ATTEST_NEGATIVES_COMBINE=$combine_dir is not a directory"
  [ -n "${ATTEST_NEGATIVES_SLICES:-}" ] \
    || usage_error "the combiner is told how many slices there are by ATTEST_NEGATIVES_SLICES, which is not set"
  slices="$(whole_number ATTEST_NEGATIVES_SLICES "$ATTEST_NEGATIVES_SLICES")"
  [ "$slices" -ge 1 ] || usage_error "ATTEST_NEGATIVES_SLICES must be at least 1"
  [ -z "${ATTEST_NEGATIVES_JOBS:-}" ] \
    || usage_error "the combiner takes the number of shards from the slices, so it refuses ATTEST_NEGATIVES_JOBS"
elif [ -n "${ATTEST_NEGATIVES_SHARD:-}" ]; then
  [[ "$ATTEST_NEGATIVES_SHARD" =~ ^([0-9]{1,6})/([0-9]{1,6})$ ]] \
    || usage_error "ATTEST_NEGATIVES_SHARD must look like 2/8, not '$ATTEST_NEGATIVES_SHARD'"
  shard=$((10#${BASH_REMATCH[1]}))
  jobs=$((10#${BASH_REMATCH[2]}))
  { [ "$jobs" -ge 1 ] && [ "$shard" -lt "$jobs" ]; } \
    || usage_error "ATTEST_NEGATIVES_SHARD=$ATTEST_NEGATIVES_SHARD is not a shard of a run"
  is_shard=1
  if [ -n "${GITHUB_ACTIONS:-}" ] && [ "${ATTEST_NEGATIVES_PARENT:-}" != "$PPID" ]; then
    usage_error "a shard is started by this script and not by hand, so CI refuses ATTEST_NEGATIVES_SHARD"
  fi
elif [ -n "${ATTEST_NEGATIVES_JOBS:-}" ]; then
  jobs="$(whole_number ATTEST_NEGATIVES_JOBS "$ATTEST_NEGATIVES_JOBS")"
  { [ "$jobs" -ge 1 ] && [ "$jobs" -le 64 ]; } || usage_error "ATTEST_NEGATIVES_JOBS must be from 1 to 64"
elif [ -z "$combine_dir" ]; then
  jobs="$(default_jobs)"
fi
if [ "$count_only" -eq 1 ]; then
  # One process that owns no case: every case is walked and none is run.
  jobs=1
  shard=-1
fi
if [ "$is_slice" -eq 0 ]; then
  shard_count=$jobs
fi

# What a shard is given by its parent. Nothing else reads these, so that a value left in the environment cannot
# choose the revision that the single run checks or a directory that it removes.
if [ "$is_shard" -eq 0 ]; then
  for variable in ATTEST_NEGATIVES_REV ATTEST_NEGATIVES_RESULTS ATTEST_NEGATIVES_WORKTREE; do
    if [ -n "${!variable:-}" ]; then
      echo "check-attest-negatives: ignoring $variable, which only a shard reads" >&2
    fi
  done
fi
if [ "$is_slice" -eq 0 ] && [ -n "${ATTEST_NEGATIVES_SLICE_DIR:-}" ]; then
  echo "check-attest-negatives: ignoring ATTEST_NEGATIVES_SLICE_DIR, which only a slice reads" >&2
fi
if [ -z "$combine_dir" ] && [ -n "${ATTEST_NEGATIVES_SLICES:-}" ]; then
  echo "check-attest-negatives: ignoring ATTEST_NEGATIVES_SLICES, which only the combiner reads" >&2
fi

# The case count: exit 1 unless a full walk had exactly the number of cases the count file names.
check_case_count() {  # count
  local pinned
  pinned="$(cat "$count_file" 2>/dev/null)" \
    || { echo "check-attest-negatives: cannot read the case count $count_file" >&2; exit 1; }
  if ! [[ "$pinned" =~ ^[1-9][0-9]{0,6}$ ]]; then
    echo "check-attest-negatives: the case count $count_file does not hold one whole number" >&2
    exit 1
  fi
  if [ "$1" -ne "$pinned" ]; then
    echo "check-attest-negatives: the walk has $1 cases, not the $pinned in $count_file;" \
      "a walk cut short or padded is refused, and a change that adds or removes cases updates that file" \
      "to what ATTEST_NEGATIVES_COUNT=1 prints" >&2
    exit 1
  fi
}

# The line a run that holds the gate ends in. The seam never prints the first form, and the first form is
# printed only for a walk of the pinned number of cases.
final_line() {
  if [ -z "$only" ]; then
    check_case_count "$1"
  fi
  if [ -n "$only" ]; then
    echo "check-attest-negatives: PARTIAL RUN, not the gate (seam ATTEST_NEGATIVES_ONLY=$only): the first $1 cases passed"
  else
    echo "check-attest-negatives: $1 cases gave the expected result (the unmodified tree accepted; each mutation refused for its stated reason)"
  fi
}

# ---------------------------------------------------------------------------
# The parent: start the shards, wait for all of them, accept what they show together.
# ---------------------------------------------------------------------------

shard_pids=()
shard_works=()
parent_logs=""
ticker=""

kill_tree() {  # pid [signal]: stop a process and everything it started (TERM unless a signal is given)
  local child
  for child in $(pgrep -P "$1" 2>/dev/null || true); do
    kill_tree "$child" "${2:-TERM}"
  done
  kill -"${2:-TERM}" "$1" 2>/dev/null || true
}

parent_cleanup() {
  local i tries=0 alive
  trap - EXIT INT TERM
  if [ -n "$ticker" ]; then
    kill_tree "$ticker"
  fi
  i=0
  while [ "$i" -lt "${#shard_pids[@]}" ]; do
    if [ -n "${shard_pids[$i]}" ]; then
      kill_tree "${shard_pids[$i]}"
    fi
    i=$((i + 1))
  done
  # A shard runs its own cleanup when it is stopped; give it a moment, then force it.
  while [ "$tries" -lt 20 ]; do
    alive=0
    i=0
    while [ "$i" -lt "${#shard_pids[@]}" ]; do
      if [ -n "${shard_pids[$i]}" ] && kill -0 "${shard_pids[$i]}" 2>/dev/null; then
        alive=1
      fi
      i=$((i + 1))
    done
    [ "$alive" -eq 1 ] || break
    sleep 0.5
    tries=$((tries + 1))
  done
  i=0
  while [ "$i" -lt "${#shard_pids[@]}" ]; do
    # The tree again: a process the shard started after the first walk of its tree would outlive the shard.
    if [ -n "${shard_pids[$i]}" ]; then
      kill_tree "${shard_pids[$i]}" KILL
    fi
    i=$((i + 1))
  done
  i=0
  while [ "$i" -lt "${#shard_works[@]}" ]; do
    git -C "$root" worktree remove --force "${shard_works[$i]}" >/dev/null 2>&1 || rm -rf "${shard_works[$i]}"
    i=$((i + 1))
  done
  git -C "$root" worktree prune >/dev/null 2>&1 || true
  if [ -n "$parent_logs" ]; then
    rm -rf "$parent_logs"
  fi
}

# The cases walked so far by each shard, one number per shard.
shard_progress() {
  local i=0 line=""
  while [ "$i" -lt "$shard_count" ]; do
    line="$line $({ wc -l < "$parent_logs/results-$((shard_first + i))"; } 2>/dev/null | tr -d ' ' || true)"
    i=$((i + 1))
  done
  echo "$line"
}

# Everything the parent requires of the shards, in one place. Exit 1 names each problem; exit 0
# writes the number of cases to the file `total` and prints how the cases were shared.
verify_shards() {
  python3 - "$parent_logs" "$jobs" <<'PY'
import pathlib
import re
import sys

logs = pathlib.Path(sys.argv[1])
jobs = int(sys.argv[2])
problems = []
# The files are read strictly, because a slice's files cross a job boundary as artifacts before they reach the
# combiner: printable ASCII, tabs and newlines only (no carriage return, NUL, byte-order mark or other invisible
# character), numbers in canonical decimal (`\d` and `str.isdigit` take other scripts' digits; no leading zero),
# an exit status that is such a number and a newline, and a WRONG line in any case and after any indentation.
REPORT = re.compile(r"^shard ([0-9]+)/([0-9]+): ran ([0-9]+) of ([0-9]+)$", re.M)
PREMISE = re.compile(r"^shard ([0-9]+)/([0-9]+): premise ([0-9]+) of ([0-9]+)$", re.M)
NUMBER = re.compile(r"0|[1-9][0-9]*")  # a canonical decimal: no sign, no leading zero
WRONG_LINE = re.compile(r"\s*wrong", re.I)
PRINTABLE = re.compile(r"[\t\n -~]*")  # a NUL, a byte-order mark or a zero-width space would hide a WRONG line


def read(path):
    # newline="": a carriage return is kept as it is, not turned into a newline, so that it can be refused.
    try:
        with open(path, encoding="utf-8", errors="replace", newline="") as handle:
            return handle.read()
    except OSError:
        return None


def lines_of(text):
    """The lines of a file, split on newlines only (`splitlines` also splits on other separators)."""
    return text[:-1].split("\n") if text.endswith("\n") else (text.split("\n") if text else [])


reported = {}   # shard -> (cases it ran, cases it saw)
premises = {}   # shard -> (times it checked that its worktree accepts the unmodified tree, times it had to)
walks = {}      # shard -> [(index, ran or skip, verdict, seconds, shard the case belongs to, plain or follows, name)]
for i in range(jobs):
    label = f"shard {i}/{jobs}"
    status = read(logs / f"rc-{i}")
    if status is None:
        problems.append(f"{label} left no exit status")
    elif not re.fullmatch(r"(0|[1-9][0-9]{0,2})\n", status):
        problems.append(f"{label} left an exit status that is not a number: {status!r}")
    elif int(status) != 0:
        problems.append(f"{label} exited with status {int(status)}")
    log = read(logs / f"shard-{i}.log") or ""
    for name, content in (("log", log), ("list of cases", read(logs / f"results-{i}") or "")):
        if "\r" in content:
            problems.append(f"{label}: its {name} holds a carriage return")
        elif not PRINTABLE.fullmatch(content):
            problems.append(f"{label}: its {name} holds a character other than printable ASCII, a tab or a newline")
    wrong = [line for line in lines_of(log) if WRONG_LINE.match(line)]
    if wrong:
        problems.append(f"{label} printed {len(wrong)} WRONG line(s)")
    reports = REPORT.findall(log)
    if len(reports) != 1:
        problems.append(f"{label} printed {len(reports)} lines `shard i/N: ran R of T`, not exactly one")
    else:
        own, of, ran, seen = map(int, reports[0])
        # Distinct and complete follow: every shard names itself, and the launcher gave each one index.
        if (own, of) != (i, jobs):
            problems.append(f"{label} reported itself as shard {own}/{of}")
        reported[i] = (ran, seen)
        if ran == 0:
            problems.append(f"{label} ran 0 of {seen} cases")
    found = PREMISE.findall(log)
    if len(found) != 1:
        problems.append(f"{label} printed {len(found)} lines `shard i/N: premise P of Q`, not exactly one")
    else:
        premises[i] = (int(found[0][2]), int(found[0][3]))
    text = read(logs / f"results-{i}")
    if text is None:
        problems.append(f"{label} left no list of the cases it walked")
        continue
    rows = []
    for number, line in enumerate(lines_of(text), 1):
        parts = line.split("\t", 6)
        if (len(parts) != 7 or not NUMBER.fullmatch(parts[0]) or parts[1] not in ("ran", "skip")
                or parts[2] not in (("ok", "wrong") if parts[1] == "ran" else ("-",))
                or not NUMBER.fullmatch(parts[3]) or not NUMBER.fullmatch(parts[4])
                or parts[5] not in ("plain", "follows")):
            problems.append(f"{label}: line {number} of its list of cases is not a case")
            break
        # index, ran or skip, verdict, seconds, the shard the case belongs to, plain or follows, name
        rows.append((int(parts[0]), parts[1], parts[2], parts[3], int(parts[4]), parts[5], parts[6]))
    walks[i] = rows

# Counts: one T, and the R values add up to it.
totals = {seen for _, seen in reported.values()}
if len(totals) > 1:
    problems.append("the shards disagree on the number of cases: "
                    + ", ".join(f"shard {i} saw {seen}" for i, (_, seen) in sorted(reported.items())))
if len(totals) == 1 and len(reported) == jobs:
    total = totals.pop()
    ran_all = sum(ran for ran, _ in reported.values())
    if ran_all != total:
        problems.append(f"the shards ran {ran_all} cases between them, not the {total} there are")
else:
    total = None

for i, (checked, reached) in sorted(premises.items()):
    if reached < 1:
        problems.append(f"shard {i}/{jobs} reaches no premise check")
    elif checked != reached:
        problems.append(f"shard {i}/{jobs} checked that its worktree accepts the unmodified tree {checked} time(s) "
                        f"of the {reached} it reaches")
if len({reached for _, reached in premises.values()}) > 1:
    problems.append("the shards reach different numbers of premise checks: "
                    + ", ".join(f"shard {i} reaches {reached}" for i, (_, reached) in sorted(premises.items())))

# Cases: the same walk everywhere, and each case run once, by the shard its index selects.
owners = {}
reference = None
for i, rows in sorted(walks.items()):
    label = f"shard {i}/{jobs}"
    if [row[0] for row in rows] != list(range(len(rows))):
        problems.append(f"{label} did not walk the cases from 0 in order")
        continue
    if i in reported:
        ran, seen = reported[i]
        if len(rows) != seen:
            problems.append(f"{label} lists {len(rows)} cases and reports {seen}")
        if sum(1 for row in rows if row[1] == "ran") != ran:
            problems.append(f"{label} lists {sum(1 for row in rows if row[1] == 'ran')} cases it ran and reports {ran}")
    outside = [row for row in rows if (row[1] == "ran") != (row[4] == i)]
    if outside:
        problems.append(f"{label} ran or skipped {len(outside)} case(s) against its slice, the first being "
                        f"case {outside[0][0]} ({outside[0][6]})")
    for row in rows:
        if row[1] == "ran":
            owners.setdefault(row[0], []).append(i)
    walk = [(row[6], row[4], row[5]) for row in rows]
    if reference is None:
        reference = (i, walk)
    elif walk != reference[1]:
        first = next((n for n, (a, b) in enumerate(zip(walk, reference[1])) if a != b), min(len(walk), len(reference[1])))
        problems.append(f"{label} walked different cases from shard {reference[0]}/{jobs}, the first difference being case {first}")
if reference is not None:
    # The assignment: a case goes to the shard its index selects, except one that follows, which goes to the
    # shard of the case before it.
    bad = []
    for n, (name, owner, kind) in enumerate(reference[1]):
        if kind == "plain" and owner != n % jobs:
            bad.append(f"case {n} ({name}) is assigned to shard {owner}, not to shard {n % jobs}, which its index selects")
        elif kind == "follows" and (n == 0 or owner != reference[1][n - 1][1]):
            bad.append(f"case {n} ({name}) follows the case before it and is assigned to shard {owner}, "
                       f"not to the shard of that case")
    problems.extend(bad[:5])
    if len(bad) > 5:
        problems.append(f"{len(bad) - 5} more cases are assigned to the wrong shard")
    unrun = [n for n in range(len(reference[1])) if len(owners.get(n, [])) != 1]
    for n in unrun[:5]:
        who = owners.get(n, [])
        problems.append(f"case {n} ({reference[1][n][0]}) was run by "
                        + ("no shard" if not who else "shards " + " and ".join(map(str, who))))
    if len(unrun) > 5:
        problems.append(f"{len(unrun) - 5} more cases were not run exactly once")
    wrong_rows = [(i, row) for i, rows in walks.items() for row in rows if row[2] == "wrong"]
    for i, row in wrong_rows[:5]:
        problems.append(f"shard {i}/{jobs} marks case {row[0]} ({row[6]}) wrong")

if problems:
    for problem in problems:
        print(f"check-attest-negatives: {problem}", file=sys.stderr)
    sys.exit(1)

busy = [sum(int(row[3]) for row in walks[i] if row[1] == "ran") for i in range(jobs)]
ran_each = " + ".join(str(reported[i][0]) for i in range(jobs))
(logs / "total").write_text(f"{total}\n")
print(f"check-attest-negatives: {jobs} shards ran {ran_each} = {total} cases "
      f"(case time per shard {min(busy)} to {max(busy)} s)")
PY
}

run_parent() {
  local i g pid rc start rev total
  parent_logs="$(mktemp -d "$tmp_base/attest-negatives-logs.XXXXXX")"
  trap parent_cleanup EXIT
  trap 'exit 130' INT
  trap 'exit 143' TERM
  start=$SECONDS
  # One revision for every shard, read once, in case HEAD moves while they start.
  rev="$(git -C "$root" rev-parse HEAD)"
  if [ "$is_slice" -eq 1 ]; then
    echo "check-attest-negatives: slice $slice/$slices, shards $shard_first to $((shard_first + shard_count - 1)) of $jobs, on ${rev:0:7}"
  else
    echo "check-attest-negatives: $jobs shards on ${rev:0:7}"
  fi
  # Shard i of this parent is shard g of the run: the same number unless this run is a slice. Its files are named
  # by g, which is what the combiner of the slices reads.
  i=0
  while [ "$i" -lt "$shard_count" ]; do
    g=$((shard_first + i))
    shard_works[$i]="$(mktemp -d "$tmp_base/attest-negatives-wt.XXXXXX")"
    env -u ATTEST_NEGATIVES_SLICE -u ATTEST_NEGATIVES_SLICE_DIR \
      ATTEST_NEGATIVES_SHARD="$g/$jobs" \
      ATTEST_NEGATIVES_PARENT="$$" \
      ATTEST_NEGATIVES_REV="$rev" \
      ATTEST_NEGATIVES_WORKTREE="${shard_works[$i]}" \
      ATTEST_NEGATIVES_RESULTS="$parent_logs/results-$g" \
      "$BASH" "$self" > "$parent_logs/shard-$g.log" 2>&1 &
    shard_pids[$i]=$!
    i=$((i + 1))
  done
  # A line every five minutes, so that a long run is not silent.
  (
    while :; do
      sleep 300
      echo "check-attest-negatives: $(((SECONDS - start) / 60)) min in; cases walked by each shard:$(shard_progress)"
    done
  ) 2>/dev/null &
  ticker=$!
  disown "$ticker"
  # i counts the shards of the run that this parent started; their pids are kept from index 0.
  i=$shard_first
  while [ "$i" -lt "$((shard_first + shard_count))" ]; do
    pid="${shard_pids[$((i - shard_first))]}"
    wait "$pid" && rc=0 || rc=$?
    shard_pids[$((i - shard_first))]=""
    echo "$rc" > "$parent_logs/rc-$i"
    i=$((i + 1))
  done
  kill_tree "$ticker"
  ticker=""
  if [ "$is_slice" -eq 1 ]; then
    finish_slice "$rev" "$((SECONDS - start))"
    exit 1  # finish_slice ends in an exit of its own
  fi
  if verify_shards; then
    echo "check-attest-negatives: the shards took $((SECONDS - start)) s"
    total="$(cat "$parent_logs/total")"
    [[ "$total" =~ ^[1-9][0-9]*$ ]] || { echo "check-attest-negatives: the verification left no count of cases" >&2; exit 1; }
    final_line "$total"
    exit 0
  fi
  i=0
  while [ "$i" -lt "$jobs" ]; do
    echo "check-attest-negatives: ---- log of shard $i/$jobs ----" >&2
    cat "$parent_logs/shard-$i.log" >&2
    i=$((i + 1))
  done
  echo "check-attest-negatives: the sharded run does not hold the gate" >&2
  exit 1
}

# ---------------------------------------------------------------------------
# A run split over machines: slices, and the combiner that accepts what they show together.
# ---------------------------------------------------------------------------

# The sha256 of this script, which every slice records and the combiner compares with its own.
script_sha256() {
  python3 -c 'import hashlib, sys; print(hashlib.sha256(open(sys.argv[1], "rb").read()).hexdigest())' "$self"
}

# The end of a slice. A slice gives no verdict on the gate: it stops its own job, with the logs, when one of its
# shards exited nonzero or printed a WRONG line, and otherwise writes its shards' files (named by their index in
# the whole run) and a manifest to the slice directory. Whether the cases were all run, each once and by the
# shard it is assigned to, is asked of all the slices together by the combiner, with the parent's own check.
finish_slice() {  # revision seconds
  local i failed=0 last=$((shard_first + shard_count - 1))
  i=$shard_first
  while [ "$i" -le "$last" ]; do
    if [ "$(cat "$parent_logs/rc-$i")" != 0 ] || grep -q '^WRONG' "$parent_logs/shard-$i.log"; then
      failed=1
    fi
    i=$((i + 1))
  done
  if [ "$failed" -eq 1 ]; then
    i=$shard_first
    while [ "$i" -le "$last" ]; do
      echo "check-attest-negatives: ---- log of shard $i/$jobs (exit status $(cat "$parent_logs/rc-$i")) ----" >&2
      cat "$parent_logs/shard-$i.log" >&2
      i=$((i + 1))
    done
    echo "check-attest-negatives: slice $slice/$slices failed: a shard exited nonzero or printed a WRONG line" >&2
    exit 1
  fi
  if [ -e "$slice_dir" ] && { [ ! -d "$slice_dir" ] || [ -n "$(ls -A "$slice_dir" 2>/dev/null)" ]; }; then
    echo "check-attest-negatives: ATTEST_NEGATIVES_SLICE_DIR=$slice_dir was filled while the slice ran" >&2
    exit 1
  fi
  mkdir -p "$slice_dir"
  i=$shard_first
  while [ "$i" -le "$last" ]; do
    cp "$parent_logs/rc-$i" "$parent_logs/shard-$i.log" "$parent_logs/results-$i" "$slice_dir/"
    i=$((i + 1))
  done
  python3 - "$slice_dir/slice.json" "$slice" "$slices" "$shard_count" "$jobs" "$shard_first" \
      "$1" "$(git -C "$root" rev-parse "$1^{tree}")" "$(script_sha256)" "$only" <<'PY'
import json, pathlib, sys
path, slice_, slices, local, shards, first, commit, tree, script, only = sys.argv[1:]
manifest = {
    "format": 1,
    "slice": int(slice_), "slices": int(slices), "local_shards": int(local), "shards": int(shards),
    "first": int(first), "commit": commit, "tree": tree, "script_sha256": script,
    "partial": int(only) if only else None,
}
pathlib.Path(path).write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
PY
  echo "check-attest-negatives: slice $slice/$slices wrote the reports of shards $shard_first to $last of $jobs" \
    "to $slice_dir in $2 s; a slice is not the gate, which is the combination of all $slices slices"
  exit 0
}

# The combiner. It reads the K slice directories, requires that they are the K slices of one run (one K, one
# number of shards each, every slice once, the commit and tree it has checked out itself, this script's hash,
# and the same walk length), gathers their shards' files into one directory, and then holds them to
# `verify_shards`, the same check the parent of a run on one machine makes. It prints the final line of a full
# run only if all of that holds.
run_combine() {
  local rev tree total
  parent_logs="$(mktemp -d "$tmp_base/attest-negatives-logs.XXXXXX")"
  trap parent_cleanup EXIT
  trap 'exit 130' INT
  trap 'exit 143' TERM
  rev="$(git -C "$root" rev-parse HEAD)"
  tree="$(git -C "$root" rev-parse 'HEAD^{tree}')"
  echo "check-attest-negatives: combining $slices slice(s) on ${rev:0:7}"
  if ! python3 - "$combine_dir" "$slices" "$rev" "$tree" "$(script_sha256)" "$only" "$parent_logs" <<'PY'
import json
import pathlib
import shutil
import sys

source = pathlib.Path(sys.argv[1])
want = int(sys.argv[2])
commit, tree, script = sys.argv[3], sys.argv[4], sys.argv[5]
only = int(sys.argv[6]) if sys.argv[6] else None
out = pathlib.Path(sys.argv[7])
problems = []
FIELDS = {"format", "slice", "slices", "local_shards", "shards", "first", "commit", "tree", "script_sha256",
          "partial"}
NUMBERS = ("format", "slice", "slices", "local_shards", "shards", "first")


def walked(value):
    return "every case" if value is None else f"the first {value} cases (seam ATTEST_NEGATIVES_ONLY={value})"


entries = sorted(source.iterdir())
directories = [entry for entry in entries if entry.is_dir() and not entry.is_symlink()]
for entry in entries:
    if entry not in directories:
        problems.append(f"{entry.name} in {source} is not a slice directory")
if len(directories) != want:
    problems.append(f"{source} holds {len(directories)} slice directories, not the {want} the run is split into")

found = {}  # slice -> (directory, manifest)
for directory in directories:
    try:
        manifest = json.loads((directory / "slice.json").read_text())
    except (OSError, ValueError) as exc:
        problems.append(f"{directory.name} has no readable slice.json: {exc}")
        continue
    if not isinstance(manifest, dict) or set(manifest) != FIELDS:
        problems.append(f"{directory.name}/slice.json does not have the fields of a slice manifest")
        continue
    if (any(type(manifest[key]) is not int for key in NUMBERS)
            or not (manifest["partial"] is None or type(manifest["partial"]) is int)
            or not all(isinstance(manifest[key], str) for key in ("commit", "tree", "script_sha256"))):
        problems.append(f"{directory.name}/slice.json has a field of the wrong type")
        continue
    k, of, local = manifest["slice"], manifest["slices"], manifest["local_shards"]
    label = f"slice {k}/{of} ({directory.name})"
    if manifest["format"] != 1:
        problems.append(f"{label} has manifest format {manifest['format']}, not 1")
    if of != want:
        problems.append(f"{label} is a slice of a run split {of} ways, not {want}")
    if not 0 <= k < want:
        problems.append(f"{label} is not one of the slices 0 to {want - 1}")
    if local < 1 or manifest["shards"] != of * local or manifest["first"] != k * local:
        problems.append(f"{label} says it started shards {manifest['first']} to {manifest['first'] + local - 1} "
                        f"of {manifest['shards']}, which are not the shards of slice {k} of {of} with {local} each")
    if manifest["commit"] != commit:
        problems.append(f"{label} ran on commit {manifest['commit']}, not on {commit}, which the combiner has checked out")
    if manifest["tree"] != tree:
        problems.append(f"{label} ran on tree {manifest['tree']}, not on {tree}, which the combiner has checked out")
    if manifest["script_sha256"] != script:
        problems.append(f"{label} was made by a check-attest-negatives.sh with sha256 {manifest['script_sha256']}, "
                        f"not by this one ({script})")
    if manifest["partial"] != only:
        problems.append(f"{label} walked {walked(manifest['partial'])}, and the combiner requires {walked(only)}")
    if k in found:
        problems.append(f"two directories are slice {k}/{of}: {found[k][0].name} and {directory.name}")
        continue
    found[k] = (directory, manifest)

missing = [k for k in range(want) if k not in found]
if missing:
    problems.append("no directory is slice " + ", ".join(f"{k}/{want}" for k in missing))
sizes = sorted({manifest["local_shards"] for _, manifest in found.values()})
if len(sizes) > 1:
    problems.append("the slices start different numbers of shards: "
                    + ", ".join(f"slice {k} starts {m['local_shards']}" for k, (_, m) in sorted(found.items())))

# Each slice holds the three files of each of its shards and its manifest, and nothing else.
for k, (directory, manifest) in sorted(found.items()):
    label = f"slice {k}/{want} ({directory.name})"
    expected = {"slice.json"}
    for g in range(manifest["first"], manifest["first"] + manifest["local_shards"]):
        expected |= {f"rc-{g}", f"shard-{g}.log", f"results-{g}"}
    present = {}
    for entry in directory.iterdir():
        present[entry.name] = entry
    for name in sorted(expected - set(present)):
        problems.append(f"{label} has no {name}")
    for name in sorted(set(present) - expected):
        problems.append(f"{label} holds {name}, which is not a file of its own shards")
    for name in sorted(expected & set(present)):
        if present[name].is_symlink() or not present[name].is_file():
            problems.append(f"{label}: {name} is not a regular file")

if problems:
    for problem in problems:
        print(f"check-attest-negatives: {problem}", file=sys.stderr)
    sys.exit(1)

for k, (directory, manifest) in sorted(found.items()):
    for g in range(manifest["first"], manifest["first"] + manifest["local_shards"]):
        for name in (f"rc-{g}", f"shard-{g}.log", f"results-{g}"):
            shutil.copyfile(directory / name, out / name)
shards = sizes[0] * want
(out / "jobs").write_text(f"{shards}\n")
print(f"check-attest-negatives: {want} slice(s) of {sizes[0]} shard(s) make one run of {shards} shards")
PY
  then
    echo "check-attest-negatives: the slices are not the slices of one run, so they do not hold the gate" >&2
    exit 1
  fi
  jobs="$(cat "$parent_logs/jobs")"
  if verify_shards; then
    total="$(cat "$parent_logs/total" 2>/dev/null || true)"
    if ! [[ "$total" =~ ^[1-9][0-9]*$ ]]; then
      echo "check-attest-negatives: the verification of the slices left no count of cases" >&2
      exit 1
    fi
    final_line "$total"
    exit 0
  fi
  echo "check-attest-negatives: the combined slices do not hold the gate" >&2
  exit 1
}

if [ -n "$combine_dir" ]; then
  run_combine
  exit 1  # run_combine ends in an exit of its own; reaching here is a fault
fi
if [ "$is_shard" -eq 0 ] && { [ "$jobs" -gt 1 ] || [ "$is_slice" -eq 1 ]; }; then
  run_parent
  exit 1  # run_parent ends in an exit of its own; reaching here is a fault
fi

# ---------------------------------------------------------------------------
# One process: the single run (JOBS=1) or one shard of a sharded run.
# ---------------------------------------------------------------------------

work=""
seen=0          # cases walked, whoever runs them; the T of the report
ran=0           # cases this process ran
wrong=0
premise=0       # times the unmodified tree was checked in this process's worktree
premise_reached=0 # premise checks the walk reached, which is how many this process has to make
case_index=0    # the global index of the case in hand, from 0
case_owner=0    # the shard that runs the case in hand
case_kind=plain # plain, or follows: it reads what the case before it wrote, and goes to that case's shard
case_pending=0  # a case this process ran is waiting to be written to its list
case_start=0
case_end=0
case_wrong_at_start=0
case_name=""
if [ "$is_shard" -eq 1 ]; then
  shard_rev="${ATTEST_NEGATIVES_REV:-HEAD}"
  shard_results="${ATTEST_NEGATIVES_RESULTS:-}"
  shard_work="${ATTEST_NEGATIVES_WORKTREE:-}"
else
  shard_rev=HEAD
  shard_results=""
  shard_work=""
fi

cleanup() {
  if [ -n "$work" ]; then
    git -C "$root" worktree remove --force "$work" >/dev/null 2>&1 || rm -rf "$work"
  fi
}
trap cleanup EXIT
trap 'exit 130' INT
trap 'exit 143' TERM

add_worktree() {
  local attempt=1 failure
  # Shards add their worktrees to one repository at the same moment; retry rather than depend on its locking.
  until failure="$(git -C "$root" worktree add -q --detach "$work" "$shard_rev" 2>&1)"; do
    if [ "$attempt" -ge 5 ]; then
      echo "check-attest-negatives: cannot add a worktree at $work after $attempt tries: $failure" >&2
      exit 1
    fi
    attempt=$((attempt + 1))
    sleep "$attempt"
    # What is in the directory now was put there by the failed add: the directory was made by this script or found
    # empty. A worktree that git registered before it failed has to be pruned, or the next add refuses it.
    if [ -d "$work" ]; then
      find "$work" -mindepth 1 -delete 2>/dev/null || true
    fi
    git -C "$root" worktree prune >/dev/null 2>&1 || true
    mkdir -p "$work"
  done
}

make_case() {
  local candidate
  if [ -z "$work" ]; then
    # `work` is set only after the checks, because cleanup removes whatever it names.
    candidate="$shard_work"
    if [ -z "$candidate" ]; then
      candidate="$(mktemp -d "$tmp_base/attest-negatives.XXXXXX")"
    elif [ -n "$(ls -A "$candidate" 2>/dev/null)" ]; then
      usage_error "ATTEST_NEGATIVES_WORKTREE=$candidate is not an empty directory"
    fi
    work="$candidate"
    add_worktree
  else
    git -C "$work" checkout -q --force HEAD -- .
    git -C "$work" clean -fdq
  fi
}

# One line per case in the list the parent reads: index, ran or skip, ok or wrong, seconds, the shard the
# case belongs to, plain or follows, name.
note_case() {
  if [ -n "$shard_results" ]; then
    printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$1" "$2" "$3" "$4" "$5" "$6" "$7" >> "$shard_results" \
      || { echo "check-attest-negatives: cannot write the list of cases to $shard_results" >&2; exit 1; }
  fi
}

# Write the case this process ran last. It is written when the next case begins, so that a check that
# follows the case and belongs to it (a `git diff` of what a refused run left behind) can still mark it wrong.
flush_case() {
  local verdict=ok
  if [ "$case_pending" -eq 1 ]; then
    if [ "$wrong" -ne "$case_wrong_at_start" ]; then
      verdict=wrong
    fi
    note_case "$case_index" ran "$verdict" "$((case_end - case_start))" "$case_owner" "$case_kind" "$case_name"
    case_pending=0
  fi
}

# The end of the walk, or the seam. A shard reports to its parent; the single run prints the final line.
finish() {
  flush_case
  if [ "$count_only" -eq 1 ]; then
    echo "check-attest-negatives: the walk has $seen cases (ATTEST_NEGATIVES_COUNT: none was run, so this is not the gate)"
    exit 0
  fi
  if [ "$is_shard" -eq 1 ]; then
    echo "shard $shard/$jobs: premise $premise of $premise_reached"
    echo "shard $shard/$jobs: ran $ran of $seen"
    if [ "$wrong" -ne 0 ]; then
      echo "check-attest-negatives: shard $shard/$jobs gave $wrong wrong result(s) in the $ran cases it ran" >&2
      exit 1
    fi
    exit 0
  fi
  if [ "$wrong" -ne 0 ]; then
    echo "check-attest-negatives: $wrong of $seen cases gave the wrong result" >&2
    exit 1
  fi
  final_line "$seen"
  exit 0
}

# Every case passes through here, whichever process runs it, so that every shard counts the same
# cases in the same order. Returns 0 when this process runs the case and 1 when another shard does.
# The shard of a case is its index modulo the number of shards, except for a case that `follows`: it
# reads what the case before it wrote into the worktree, so it goes to that case's shard.
begin_case() {  # name [follows] [premise]
  flush_case
  if [ -n "$only" ] && [ "$seen" -ge "$only" ]; then
    finish
  fi
  if [ "${3:-}" = premise ]; then
    premise_reached=$((premise_reached + 1))
  fi
  case_index=$seen
  case_name="$1"
  seen=$((seen + 1))
  if [ "${2:-}" = follows ] && [ "$case_index" -gt 0 ]; then
    case_kind=follows
  else
    case_kind=plain
    case_owner=$((case_index % jobs))
  fi
  if [ "$case_owner" -ne "$shard" ]; then
    note_case "$case_index" skip - 0 "$case_owner" "$case_kind" "$case_name"
    return 1
  fi
  ran=$((ran + 1))
  case_pending=1
  case_start=$SECONDS
  case_wrong_at_start=$wrong
  return 0
}

end_case() {
  case_end=$SECONDS
}

# The cases must give the same result on a developer's machine and on the CI
# runner, where GITHUB_ACTIONS is set and the allowlist writer refuses to run;
# only the case that tests that refusal sets it.
attest() {
  (cd "$work" && env -u GITHUB_ACTIONS python3 tacenta-proofs/scripts/attest.py "$@" 2>&1)
}

attest_in_ci() {
  (cd "$work" && GITHUB_ACTIONS=true python3 tacenta-proofs/scripts/attest.py "$@" 2>&1)
}

# Run another script of this directory in the worktree; the same shape as attest.
run_script() {
  (cd "$work" && env -u GITHUB_ACTIONS bash "tacenta-proofs/scripts/$1" 2>&1)
}

# The verdicts. Each takes the name of the case, what it was run for, the output and the exit status.
judge_refusal() {
  if [ "$4" -eq 0 ]; then
    echo "WRONG  $1: expected refusal containing '$2', was accepted" >&2
    wrong=$((wrong + 1))
  elif [[ "$3" != *"$2"* ]]; then
    echo "WRONG  $1: refused, but not for '$2':" >&2
    printf '%s\n' "$3" >&2
    wrong=$((wrong + 1))
  fi
}

judge_acceptance() {
  if [ "$3" -ne 0 ]; then
    echo "WRONG  $1: expected acceptance, was refused:" >&2
    printf '%s\n' "$2" >&2
    wrong=$((wrong + 1))
  fi
}

judge_acceptance_saying() {
  if [ "$4" -ne 0 ] || [[ "$3" != *"$2"* ]]; then
    echo "WRONG  $1: rc=$4, expected acceptance printing '$2':" >&2
    printf '%s\n' "$3" >&2
    wrong=$((wrong + 1))
  fi
}

expect_fail() {
  local name="$1"
  local expected="$2"
  shift 2
  local out rc
  begin_case "$name" || return 0
  set +e
  out="$(attest "$@")"
  rc=$?
  set -e
  judge_refusal "$name" "$expected" "$out" "$rc"
  end_case
}

expect_pass() {
  local name="$1"
  shift
  local out rc
  begin_case "$name" || return 0
  set +e
  out="$(attest "$@")"
  rc=$?
  set -e
  judge_acceptance "$name" "$out" "$rc"
  end_case
}

# A case that must be accepted and reads what the case before it wrote into the worktree: a `--check` of
# what a regeneration has just rewritten. It runs in the shard that ran that case, because no other
# shard's worktree holds what that case wrote.
expect_pass_after() {
  local name="$1"
  shift
  local out rc
  begin_case "$name" follows || return 0
  set +e
  out="$(attest "$@")"
  rc=$?
  set -e
  judge_acceptance "$name" "$out" "$rc"
  end_case
}

# A run that must be accepted and must say something.
expect_pass_saying() {
  local name="$1"
  local expected="$2"
  shift 2
  local out rc
  begin_case "$name" || return 0
  set +e
  out="$(attest "$@")"
  rc=$?
  set -e
  judge_acceptance_saying "$name" "$expected" "$out" "$rc"
  end_case
}

# A run with GITHUB_ACTIONS set, as the runner has it.
expect_fail_in_ci() {
  local name="$1"
  local expected="$2"
  shift 2
  local out rc
  begin_case "$name" || return 0
  set +e
  out="$(attest_in_ci "$@")"
  rc=$?
  set -e
  judge_refusal "$name" "$expected" "$out" "$rc"
  end_case
}

# The unmodified tree must be accepted by the worktree of every shard, because a refusal in a
# worktree is evidence only if that worktree accepts. The case is counted once, where its index
# puts it; a shard that does not own it still runs the check and counts it in `premise`.
premise_pass() {
  local name="$1"
  shift
  local out rc owned=0
  if begin_case "$name" "" premise; then
    owned=1
  fi
  if [ "$count_only" -eq 1 ]; then
    return 0
  fi
  set +e
  out="$(attest "$@")"
  rc=$?
  set -e
  judge_acceptance "$name" "$out" "$rc"
  premise=$((premise + 1))
  if [ "$owned" -eq 1 ]; then
    end_case
  fi
}

# A refused run must leave a file as it was. It is a case of its own that follows the run before it, so that it
# is counted, listed and sent to the shard of that run, where the file was written; the parent sees it.
expect_unchanged() {  # name path
  local name="$1" path="$2" rc=0
  begin_case "$name" follows || return 0
  git -C "$work" diff --quiet -- "$path" || rc=$?
  if [ "$rc" -ne 0 ]; then
    echo "WRONG  $name: $path was written by the run before it" >&2
    wrong=$((wrong + 1))
  fi
  end_case
}

gen="tacenta-proofs/translation/Translation"
allowlist="tacenta-proofs/manifests/translation-axiom-allowlist.json"
record="tacenta-proofs/manifests/translation-attestation.json"

expect_script_fail() {
  local name="$1" expected="$2" script="$3" out rc
  begin_case "$name" || return 0
  set +e
  out="$(run_script "$script")"
  rc=$?
  set -e
  judge_refusal "$name" "$expected" "$out" "$rc"
  end_case
}

expect_script_pass() {
  local name="$1" script="$2" out rc
  begin_case "$name" || return 0
  set +e
  out="$(run_script "$script")"
  rc=$?
  set -e
  judge_acceptance "$name" "$out" "$rc"
  end_case
}

# Insert the text on stdin into a generated file just before the `end` that
# closes its namespace, which is where the translator's own declarations sit.
insert_in() {
  local text
  text="$(cat)"
  INSERT_TEXT="$text" python3 - "$work/$gen/$1" <<'PY'
import os, pathlib, re, sys
path = pathlib.Path(sys.argv[1])
text = path.read_text()
close = list(re.finditer(r"^end (\S+)\s*$", text, re.M))[-1]
path.write_text(text[:close.start()] + os.environ["INSERT_TEXT"] + "\n\n" + text[close.start():])
PY
}

# Run a Python program over a JSON file: `data` is the parsed document.
edit_json() {
  python3 - "$work/$1" "$2" <<'PY'
import json, pathlib, sys
path, program = pathlib.Path(sys.argv[1]), sys.argv[2]
data = json.loads(path.read_text())
exec(program, {"data": data})
path.write_text(json.dumps(data, indent=2) + "\n")
PY
}

# Replace `old` with `new` in a file, once, or stop.
replace_in() {
  python3 - "$work/$1" "$2" "$3" <<'PY'
import pathlib, sys
path, old, new = pathlib.Path(sys.argv[1]), sys.argv[2], sys.argv[3]
text = path.read_text()
assert text.count(old) == 1, (path, old, text.count(old))
path.write_text(text.replace(old, new))
PY
}

# The audit log an honest build of the recorded translation would print.
honest_audit_log() {
  python3 - "$work/$record" "$1" <<'PY'
import json, pathlib, sys
record = json.loads(pathlib.Path(sys.argv[1]).read_text())["generated_files"]
lines = []
for rel, item in sorted(record.items()):
    for name in item["axioms"]:
        lines.append("audit-axiom: Translation.%s %s" % (item["module"], name))
pathlib.Path(sys.argv[2]).write_text("\n".join(lines) + "\n")
PY
}

# ---------------------------------------------------------------------------
# Control: the unmodified tree is accepted.
# ---------------------------------------------------------------------------

make_case
premise_pass "unmodified-tree" --check
premise_pass "unmodified-translation" --check-translation

# ---------------------------------------------------------------------------
# Claims and manifests.
# ---------------------------------------------------------------------------

make_case
python3 - "$work/tacenta-proofs/CLAIMS.md" <<'PY'
import pathlib, sys
path = pathlib.Path(sys.argv[1])
path.write_text(path.read_text() + "\n## Proved P9 mutation\n\n**Location:** `tacenta-proofs/Proofs/SessionEstablishment.lean`\n\n- `P9MissingTheorem`: mutation control.\n")
PY
expect_fail "missing-claimed-theorem" 'CLAIMS.md claims `P9MissingTheorem` but no such theorem is declared' --check

make_case
python3 - "$work/tacenta-proofs/translation/Translation/UnitLifecyclePublicT1.lean" <<'PY'
import pathlib, re, sys
path = pathlib.Path(sys.argv[1])
text = path.read_text()
pattern = re.compile(
    r"/--\s*info: 'Tacenta\.UnitLifecycleT1\.encrypt_no_panic' depends on axioms: "
    r"\[.*?\]\s*-/\s*\n#guard_msgs in\s*\n"
    r"#print axioms\s+Tacenta\.UnitLifecycleT1\.encrypt_no_panic\n",
    re.S,
)
text, count = pattern.subn("", text)
if count != 1:
    raise SystemExit(f"expected one Session T1 pin, removed {count}")
path.write_text(text)
PY
expect_fail "claimed-session-t1-without-pin" 'claimed Session T1 theorem `Tacenta.UnitLifecycleT1.encrypt_no_panic` is not axiom-pinned' --check

make_case
rm "$work/tacenta-proofs/manifests/verification-manifest.json"
expect_fail "missing-verification-manifest" "tacenta-proofs/manifests/verification-manifest.json is missing" --check

make_case
edit_json tacenta-proofs/manifests/source-commit-attestation.json 'data["p9_mutation"] = "stale"'
expect_fail "stale-source-attestation" "tacenta-proofs/manifests/source-commit-attestation.json is stale" --check

# ---------------------------------------------------------------------------
# Pin lists. A pin block that is deleted, or edited to list a compiler-trust
# axiom, leaves a manifest that regenerates cleanly; the required-pin floor and
# the compiler-trust ceiling in attest.py are what refuse both. The mutations
# are made in the session lifecycle pins, and each is refused by the build of
# the manifest itself, so the expected text is the script's own diagnostic.
# ---------------------------------------------------------------------------

session_pins="tacenta-proofs/translation/Translation/UnitLifecyclePublicT1.lean"

for n in encrypt_no_panic decrypt_no_panic decrypt_ratchet_no_panic \
         establish_initiator_for_no_panic establish_responder_no_panic \
         invariant_gives_preconditions; do
  make_case
  python3 - "$work/$session_pins" "Tacenta.UnitLifecycleT1.$n" <<'PY'
import pathlib, re, sys
path = pathlib.Path(sys.argv[1])
text = path.read_text()
name = sys.argv[2]
block = re.compile(
    r"/--\s*info: '" + re.escape(name) + r"'.*?-/\s*\n#guard_msgs in\s*\n#print axioms\s+" + re.escape(name) + r"\n",
    re.S,
)
new, n = block.subn("", text)
assert n == 1, n
path.write_text(new)
PY
  expect_fail "required-pin-deleted-$n" "\`Tacenta.UnitLifecycleT1.$n\` is on REQUIRED_PINS and has no axiom pin" --check
  if [ "$n" = "encrypt_no_panic" ]; then
    expect_fail "required-pin-deleted-refused-by-refresh" "\`Tacenta.UnitLifecycleT1.$n\` is on REQUIRED_PINS and has no axiom pin"
  fi
done

vacuity_pins="tacenta-proofs/translation/Translation/SessionBraidReceiveVacuity.lean"
for n in decoderMessage_not_total braidReceiveContractsUnbounded_false decryptRatchetContractsUnbounded_false \
         establishResponderContractsUnbounded_empty message_eq_messageP all_tr_refute; do
  make_case
  python3 - "$work/$vacuity_pins" "Tacenta.SessionBraidReceiveVacuity.$n" <<'PY'
import pathlib, re, sys
path = pathlib.Path(sys.argv[1])
text = path.read_text()
name = sys.argv[2]
block = re.compile(
    r"/--\s*info: '" + re.escape(name) + r"'.*?-/\s*\n#guard_msgs in\s*\n#print axioms\s+" + re.escape(name) + r"\n",
    re.S,
)
new, n = block.subn("", text)
assert n == 1, n
path.write_text(new)
PY
  expect_fail "required-pin-deleted-vacuity-$n" "\`Tacenta.SessionBraidReceiveVacuity.$n\` is on REQUIRED_PINS and has no axiom pin" --check
done

repair_pins="tacenta-proofs/translation/Translation/SessionBraidReceiveRepair.lean"
for n in old_witness boundary_gt_max_codewords divCeilValue_shape_satisfiable \
         decoderMessageTotal_is DivCeilValue_is \
         old_witness_fails_bounded_premise old_witness_rejected_by_invariant \
         decoderMessageTotal_of_truncate bounded_holds_unbounded_fails \
         message_total_of_invariant boundary_exact mutant_premise_at_boundary_refuted; do
  make_case
  python3 - "$work/$repair_pins" "Tacenta.SessionBraidReceiveRepair.$n" <<'PY'
import pathlib, re, sys
path = pathlib.Path(sys.argv[1])
text = path.read_text()
name = sys.argv[2]
block = re.compile(
    r"/--\s*info: '" + re.escape(name) + r"'.*?-/\s*\n#guard_msgs in\s*\n#print axioms\s+" + re.escape(name) + r"\n",
    re.S,
)
new, n = block.subn("", text)
assert n == 1, n
path.write_text(new)
PY
  expect_fail "required-pin-deleted-repair-$n" "\`Tacenta.SessionBraidReceiveRepair.$n\` is on REQUIRED_PINS and has no axiom pin" --check
done

bound_pins="tacenta-proofs/translation/Translation/SessionUnitDecoderBound.lean"
for n in add_chunk_keeps_needed clone_keeps_needed invariant_true_needed_le new_needed_le; do
  make_case
  python3 - "$work/$bound_pins" "Tacenta.SessionUnitDecoderBound.$n" <<'PY'
import pathlib, re, sys
path = pathlib.Path(sys.argv[1])
text = path.read_text()
name = sys.argv[2]
block = re.compile(
    r"/--\s*info: '" + re.escape(name) + r"'.*?-/\s*\n#guard_msgs in\s*\n#print axioms\s+" + re.escape(name) + r"\n",
    re.S,
)
new, n = block.subn("", text)
assert n == 1, n
path.write_text(new)
PY
  expect_fail "required-pin-deleted-decoder-bound-$n" "\`Tacenta.SessionUnitDecoderBound.$n\` is on REQUIRED_PINS and has no axiom pin" --check
done

make_case
python3 - "$work/tacenta-proofs/translation/Translation/SessionUnitBraidImportInv.lean" <<'PY'
import pathlib, re, sys
path = pathlib.Path(sys.argv[1])
text = path.read_text()
name = "Tacenta.SessionUnitBraidImportInv.Braid.invariant_true_gives_decoders_bounded"
block = re.compile(
    r"/--\s*info: '" + re.escape(name) + r"'.*?-/\s*\n#guard_msgs in\s*\n#print axioms\s+" + re.escape(name) + r"\n",
    re.S,
)
new, n = block.subn("", text)
assert n == 1, n
path.write_text(new)
PY
expect_fail "required-pin-deleted-import-decoders-bounded" "\`Tacenta.SessionUnitBraidImportInv.Braid.invariant_true_gives_decoders_bounded\` is on REQUIRED_PINS and has no axiom pin" --check

# The inhabitation results: every pin of the UnitSatisfiability modules, each deleted in turn.
# One line per module: file, namespace, then the required names.
while IFS=' ' read -r file ns names; do
  for n in $names; do
    make_case
    python3 - "$work/tacenta-proofs/translation/Translation/$file.lean" "$ns.$n" <<'PY'
import pathlib, re, sys
path = pathlib.Path(sys.argv[1])
text = path.read_text()
name = sys.argv[2]
block = re.compile(
    r"/--\s*info: '" + re.escape(name) + r"'.*?-/\s*\n#guard_msgs in\s*\n#print axioms\s+" + re.escape(name) + r"\n",
    re.S,
)
new, n = block.subn("", text)
assert n == 1, n
path.write_text(new)
PY
    expect_fail "required-pin-deleted-$file-$n" "\`$ns.$n\` is on REQUIRED_PINS and has no axiom pin" --check
  done
done <<'LIST'
UnitSatisfiabilityBraidAgreements Tacenta.UnitSatisfiabilityBraidAgreements braid_agreement_shapes_are_predicates braid_agreements_have_a_model
UnitSatisfiabilityErasureAgrees Tacenta.UnitSatisfiabilityErasureAgrees erasureCloneAgrees erasureAgrees_iff_clauses erasureAgrees_encoder
UnitSatisfiabilityBraidStates Tacenta.UnitSatisfiabilityBraidStates ingredients twelve_states six_receive_witnesses initiator_refines responder_refines
UnitBraidEntryPoints Tacenta.UnitBraidEntryPoints defined_hypotheses_given_erasure Braid.receive_refines_given_erasure Braid.send_refines_given_erasure defined_hypotheses_of_laws Braid.receive_refines_of_laws Braid.send_refines_of_laws twelve_states_of_laws six_receive_witnesses_of_laws
UnitErasureRsStatements Tacenta.UnitErasureRs K_weights K_coefficients K_evaluate K_algebra E_new E_next D_add D_message M_recover
UnitErasureRsGlue Tacenta.UnitErasureRs.Glue erasureAgrees_decoder erasureAgrees
ErasureT3 Tacenta.ErasureT3 mul_refines
UnitSatisfiabilityRecords Tacenta.UnitSatisfiabilityRecords stdLaws_real_iff ratchetLaws_of_base encrypt_contracts_of_axiom_base decrypt_contracts_of_axiom_base initiator_contracts_of_axiom_base responder_contracts_of_axiom_base records_of_axiom_base axiom_base_satisfiable axiom_base_satisfiable_for_total_rng
UnitSatisfiabilityJoint Tacenta.UnitSatisfiabilityJoint all_shapes_are_predicates model_satisfies_all_axiom_shapes stdLaws_of_faithful model_Faithful model_StdLaws encrypt_iff_parts decrypt_iff_parts initiator_toParts_ofParts responder_toParts_ofParts encrypt_axiom_part_satisfiable decrypt_axiom_part_satisfiable initiator_axiom_part_satisfiable responder_axiom_part_satisfiable DecoderNewTotal_is decoderNewShape_of_stdLaws model_DecoderNew badRange_refutes badDeref_refutes_array badDeref_refutes_message_key badOptionClone_refutes badCap_refutes badSeal_refutes model_pop_empty model_capacity_ge model_truncate_is_take
UnitSatisfiabilityErasure Tacenta.UnitSatisfiabilityErasure decoderAddChunk_total encoderNextChunk_total encoderClone_total decoderClone_total decoderNew_iff encoderNew_iff divCeil32_of_value decoderNew_of_divCeilValue encoderNew_of_divCeilValue
UnitSatisfiabilityRatchet Tacenta.UnitSatisfiabilityRatchet kdfRkTotal kdfCkTotal kdfInitTotal spqrRemoveSkippedAtTotal ratchetRemoveSkippedAtTotal setChainsLoopTotal clearChainsLoop0Total clearSkippedLoopTotal vecRetainTotal defined_fields_hold spqrRemoveSkippedAtTotal_false_of_noop_pop ratchetRemoveSkippedAtTotal_false_of_noop_pop ratchetRemoveSkippedAtTotal_forces_blanketU32 setChainsLoopTotal_forces_asMut
UnitSatisfiabilitySession Tacenta.UnitSatisfiabilitySession vec_pop_satisfiable noop_pop_not_faithful VecPopLaw_is all_thirteen_contracts_satisfiable
UnitSatisfiabilityZeroizeScope Tacenta.UnitSatisfiabilityZeroizeScope zeroize_failure_propagation_conflicts braid_zeroize_failure_propagation_conflicts vec_zeroize_failure_propagation_conflicts faithful_propagates faithful_vec_propagates faithful_refutes_unscoped faithful_satisfies_all_axiom_shapes spqrZeroize_of_unscoped arrayZeroize_of_unscoped vecRetainAxiom_of_unscoped arrayZeroizeScoped_of_total
DispatchEvidenceVacuity Tacenta.DispatchEvidenceVacuity same_ephemeral_agreement_empty initialSameEphemeralEvidence_false codewordViewOf_false codewordViewOf_false_of_encoderNewTotal record_empty_of_nonempty_decoder record_empty_headerSent record_empty_ekSentCt1Received record_empty_noHeaderReceived record_empty_ct1Sampled_ek record_empty_ct1Sampled_ekCt1Ack record_empty_ct1Acknowledged keysSampled_receive_ct1_holds_chunk tripleConcreteEvidence_forces_constant_dhPublic aeadConcreteEvidence_forces_constant_dhPublic constant_dhPublic_false_of_publicKeyNotConstant tripleConcreteEvidence_false_of_publicKeyNotConstant aeadConcreteEvidence_false_of_publicKeyNotConstant oracleOf_kem_oracle_never_refuses oracleOf_kem_call_never_errs
BraidPreserve Tacenta.BraidPreserve Braid.step_send_sized Braid.step_receive_sized State.clone_sized Braid.send_sized Braid.receive_sized Braid.commit_sized Braid.initiator_sized Braid.responder_sized Braid.Run.sized Braid.Constructed.sized State.sized_ct1_bounded Braid.Run.exists_initiator Braid.Run.exists_responder Braid.Run.exists_send
SessionUnitBraidPreserve Tacenta.SessionUnitBraidPreserve Braid.step_send_sized Braid.step_receive_sized State.clone_sized Braid.send_sized Braid.receive_sized Braid.commit_sized Braid.initiator_sized Braid.responder_sized Braid.Run.sized Braid.Constructed.sized State.sized_ct1_bounded Braid.Run.exists_initiator Braid.Run.exists_responder Braid.Run.exists_send
BraidPreserveWitness Tacenta.BraidPreserveWitness newMsgLen_iff api_newMsgLen erasure_laws_satisfiable model_for_both_widths
BraidPreserveCorollary Tacenta.BraidPreserveCorollary Braid.Run.receive_no_panic Braid.Run.receive_refines
SessionUnitBraidPreserveDecoder Tacenta.SessionUnitBraidPreserveDecoder message_length_le Good.new Good.msg Good.add Good.clone
SessionUnitBraidPreserveFacts Tacenta.SessionUnitBraidPreserveFacts sized_decoders_bounded invariant_true_gives_sized from_bytes_sized Braid.Run.sized_of_start Braid.Run.inv Braid.Run.receive_no_panic Braid.Run.receive_refines inv_not_sized TruncateLen_is truncateLen_model laws_model
UnitHeadroomSatisfiable Tacenta.UnitHeadroomSatisfiable usize_max_ge plaintext_bound_at_widths freshTriple_headroom freshBraid_bounds decryptHeadroom_sessionOf_iff invariantPreconditions_sessionOf encryptHeadroom_sessionOf_iff initiatorHeadroom_iff responderHeadroom_iff decryptHeadroom_satisfiable encryptHeadroom_satisfiable encryptHeadroom_satisfiable_pending initiatorHeadroom_satisfiable responderHeadroom_satisfiable initiatorHeadroom_not_trivial responderHeadroom_not_trivial decryptHeadroom_not_trivial encryptHeadroom_not_trivial nonempty_privateKey_of_dhCodec nonempty_publicKey_of_dhCodec nonempty_derivedZeroizing encrypt_headroom_of_contracts decrypt_headroom_of_contracts initiator_headroom_of_contracts responder_headroom_of_contracts headroomInhabitants_is model_headroomInhabitants axiom_base_model headroom_of_axiom_base headroom_hypotheses_satisfiable
UnitHeadroomInvariant Tacenta.UnitHeadroomInvariant validKeyShape_is model_validKeyShape optionEqU64Shape_is optionEqImpl_shape structural_sessionOf freshTriple_invariant freshBraid_invariant sessionOf_invariant emptyChainTable_fails_invariant epochZero_braid_fails_invariant emptyChain_headroom epochZero_bounds session_emptyChainTable_fails_invariant session_epochZero_fails_invariant structural_gives_ad invariant_gives_ad_length decryptHeadroom_of_invariant encryptHeadroom_iff_of_invariant invariant_session_meets_both invariant_session_of_axiom_base invariant_hypotheses_satisfiable
NumericBoundary Tacenta.NumericBoundary both_widths classical_store_cap_fits classical_skip_cap_fits spqr_chain_cap_fits spqr_skip_cap_fits ratchet_codec_cap_fits spqr_codec_cap_fits erasure_cap_fits erasure_room_exact_at_32 clock_ceiling_excludes_only_parked epoch_ceiling_excludes_only_top
NumericBoundaryLeaf Tacenta.NumericBoundaryLeaf ratchet_constants spqr_constants erasure_constants protobuf_constants code_matches_model max_events_is_parked clock_ceiling_summary
NumericBoundaryTriple Tacenta.NumericBoundaryTriple unit_ratchet_constants unit_spqr_constants unit_code_matches_model
NumericBoundarySession Tacenta.NumericBoundarySession session_unit_ratchet_constants session_unit_spqr_constants session_unit_erasure_constants session_unit_code_matches_model
NumericShapeWitness Tacenta.NumericShapeWitness usize_max_cases every_shape_is_satisfiable
NumericWitnessLeaf Tacenta.NumericWitnessLeaf sat_T1_receive_no_panic sat_T3_receive_refines sat_ImportInv_Ratchet_decoded_receive_refines sat_SpqrT1_receive_no_panic sat_SpqrT1_send_no_panic sat_SpqrT3_receive_refines sat_SpqrT3_send_refines sat_BraidT1_Braid_receive_no_panic sat_BraidT1_Braid_step_receive_no_panic sat_BraidT3_Braid_receive_refines sat_BraidT3_step_receive_refines sat_BraidT3_Braid_send_refines sat_BraidT3_step_send_refines spqrS_inv ratS_inv spqr_receive_premises_at_witness spqr_send_premises_at_witness spqr_advance_premises_at_witness spqr_maybe_advance_premises_at_witness spqr_clear_old_epochs_premises_at_witness ratchet_receive_premises_at_witness braid_receive_premises_at_witness braid_step_receive_premises_at_witness
NumericWitnessTriple Tacenta.NumericWitnessTriple sat_UnitT1_receive_no_panic sat_UnitT3_receive_refines sat_UnitSpqrT1_receive_no_panic sat_UnitSpqrT1_send_no_panic sat_UnitSpqrT3_receive_refines sat_UnitSpqrT3_send_refines sat_UnitTripleT1_State_receive_no_panic sat_UnitTripleT1_State_send_no_panic sat_UnitTripleT3_receive_refines sat_UnitTripleT3_receive_refines_discharged sat_UnitTripleT3_send_refines sat_UnitTripleT3_send_refines_discharged
NumericWitnessSession Tacenta.NumericWitnessSession sat_SessionUnitT1_receive_no_panic sat_SessionUnitT3_receive_refines sat_SessionUnitRatchetImportInv_Ratchet_decoded_receive_refines sat_SessionUnitSpqrT1_receive_no_panic sat_SessionUnitSpqrT1_send_no_panic sat_SessionUnitSpqrT3_receive_refines sat_SessionUnitSpqrT3_send_refines sat_SessionUnitTripleT1_State_receive_no_panic sat_SessionUnitTripleT1_State_send_no_panic sat_SessionUnitTripleT3_receive_refines sat_SessionUnitTripleT3_receive_refines_discharged sat_SessionUnitTripleT3_send_refines sat_SessionUnitTripleT3_send_refines_discharged sat_SessionUnitBraidT1_Braid_receive_no_panic sat_SessionUnitBraidT1_Braid_step_receive_no_panic sat_SessionUnitBraidT3_Braid_receive_refines sat_SessionUnitBraidT3_step_receive_refines sat_SessionUnitBraidT3_Braid_send_refines sat_SessionUnitBraidT3_step_send_refines session_unit_spqrS_inv session_unit_ratS_inv session_unit_spqr_receive_premises_at_witness session_unit_spqr_send_premises_at_witness session_unit_spqr_advance_premises_at_witness session_unit_spqr_maybe_advance_premises_at_witness session_unit_spqr_clear_old_epochs_premises_at_witness session_unit_ratchet_receive_premises_at_witness session_unit_braid_receive_premises_at_witness session_unit_braid_step_receive_premises_at_witness triple_receive_premises_at_witness triple_send_premises_at_witness
DecodedStateDischarge Tacenta.DecodedStateDischarge spqr_epoch_family spqr_receive_premises spqr_send_premises spqr_advance_premises spqr_maybe_advance_premises spqr_clear_old_epochs_premises ratchet_receive_premises braid_receive_premises braid_step_receive_premises
SessionUnitDecodedStateDischarge Tacenta.SessionUnitDecodedStateDischarge session_unit_spqr_epoch_family session_unit_spqr_receive_premises session_unit_spqr_send_premises session_unit_spqr_advance_premises session_unit_spqr_maybe_advance_premises session_unit_spqr_clear_old_epochs_premises session_unit_ratchet_receive_premises session_unit_braid_receive_premises session_unit_braid_step_receive_premises triple_receive_premises triple_send_premises decrypt_headroom_of_invariant decrypt_ratchet_no_panic_of_invariant decrypt_no_panic_of_invariant
SatisfiabilitySpqrLaws Tacenta.SatisfiabilitySpqrLaws kdfRkTotal kdfCkTotal spqrRemoveSkippedAtTotal setChainsLoopTotal clearChainsLoop0Total clearSkippedLoopTotal vecRetainTotal defined_fields_hold removeSkippedAtAgrees setChainsAgrees clearOldEpochsAgrees vecRetainAgreesOfLaws vecRetainAgrees LawPop_is LawAsMut_is LawCapacity_is LawVecZeroize_is LawHkdf_is SpqrCodec_ZeroizingVecTotal_is zeroizing_vec_satisfiable laws_jointly_satisfiable defined_hyps_from_axiom_hyps spqr_zeroizeTotal_conflicts laws_of_shape hkdf_total_satisfiable pop_satisfiable capacity_satisfiable vec_zeroize_satisfiable vec_zeroize_conflicts
SatisfiabilityRatchetLaws Tacenta.SatisfiabilityRatchetLaws ratchetRemoveSkippedAtTotal LawPop_is LawBlanketU32_is ArrZU8_is RatchetCodec_ZeroizingVecTotal_is zeroizing_vec_satisfiable pop_satisfiable blanket_satisfiable arrZU8_satisfiable ratchet_laws_jointly_satisfiable
SatisfiabilityBraidZeroize Tacenta.SatisfiabilityBraidZeroize braid_arrayZeroizeTotal_conflicts
UnitSatisfiabilityTripleLaws Tacenta.UnitSatisfiabilityTripleLaws kdfRkTotal kdfCkTotal kdfInitTotal spqrRemoveSkippedAtTotal ratchetRemoveSkippedAtTotal setChainsLoopTotal clearChainsLoop0Total clearSkippedLoopTotal vecRetainTotal defined_fields_hold removeSkippedAtAgrees setChainsAgrees clearOldEpochsAgrees vecRetainAgreesOfLaws vecRetainAgrees LawPop_is LawAsMut_is LawCapacity_is LawVecZeroize_is LawBlanketU32_is LawHkdf_is laws_jointly_satisfiable laws_of_shape defined_hyps_from_axiom_hyps RoundTrips80_is roundTrips80_satisfiable TripleZeroizeTotal_is arrZ32_satisfiable arrZ32_of_general spqrZeroizeTotal_conflicts hkdf_total_satisfiable pop_satisfiable capacity_satisfiable vec_zeroize_satisfiable blanket_satisfiable vec_zeroize_conflicts
SpqrFromBytesWitness Tacenta.SpqrFromBytesWitness spqr_from_bytes_accepts_witness spqr_from_bytes_establishes_inv_nonvacuous
BraidFromBytesWitness Tacenta.BraidFromBytesWitness braid_from_bytes_accepts_witness braid_from_bytes_establishes_inv_nonvacuous
SessionUnitBraidFromBytesWitness Tacenta.SessionUnitBraidFromBytesWitness braid_from_bytes_accepts_witness braid_from_bytes_establishes_inv_nonvacuous
RatchetDecodedWitness Tacenta.RatchetDecodedWitness ratchet_witness_events decoded_receive_refines_premises_satisfiable
UnitLifecycleAtomicity Tacenta.UnitLifecycleAtomicity decrypt_ratchet_err_leaves_state decrypt_ratchet_ok_writes decrypt_err_leaves_state decrypt_ok_writes establish_responder_err_leaves_store encrypt_err_leaves_state encrypt_ok_writes
UnitLifecycleRepair Tacenta.UnitLifecycleRepair codewordViewSendOf_satisfiable scoped_chunk_fields_iff_consistent
UnitPins Tacenta.UnitT3 receive_store_full_refines
UnitPins Tacenta.UnitSpqrT3 receive_store_full_refines
UnitPins Tacenta.UnitTripleT3 receive_store_full_refines_discharged
AxiomAuditSessionUnit Tacenta.UnitLifecycleT3 concrete_receive_attempt_store_full_from_contracts concrete_receive_attempt_store_full_from_retry_bounds fullStoreOfReal_ne_of_generated_ne
UnitLifecycleIntegrationScreen Tacenta.UnitLifecycleIntegrationScreen concreteBranchEvidence_empty endToEndEvidence_empty agreementEndToEndEvidence_empty byte_random32 random32Clause_of_oracleOf sigSignClause_of_oracleOf kemClauses_of_oracleOf sigSignClause_of_law kemClauses_of_law changed_rng_clauses_have_a_model changed_rng_clauses_of_laws braid_send_keysUnsampled_generate braidSendTrace_conflicts_with_sigSign retryReceiveBounds_initAlice retryReceiveBounds_not_trivial generatedTripleRefusalConditions_initAlice generatedTripleSuccessConditions_initAlice oracleOf_dhAgree_off_view encodedEphemeralAgreement_unconstrained sameEphemeralAgreement_of_view_agree concreteBranchEvidenceRun_of_run_parts runRandomDraw_byte braid_send_keysUnsampled_byte_trace braidSendTraceCounted_with_sigSign_byte
UnitLifecycleRetryLoopT3 Tacenta.UnitLifecycleRetryLoopT3 receive_with_eviction_loop_refines receive_with_eviction_refines receiveWithEvictionLoopResult_stop shortfall_covers evict_for_retry_covers
UnitLifecycleDecryptRatchetT3 Tacenta.UnitLifecycleDecryptRatchetT3 DecryptOracleOf.of_oracleOf cMax_usize decrypt_ratchet_refines decrypt_ratchet_refines_statement RetryRunBounds.toRetryReceiveBounds DecryptPrefix.triple_refusal DecryptPrefix.aead_refusal DecryptPrefix.success tripleRefusalOpen_exactly tripleRefusalOpen_false_unless_triple decrypt_ratchet_refines_unless_open
UnitLifecycleDecryptRatchetScreen Tacenta.UnitLifecycleDecryptRatchetScreen sample_run_satisfiable decrypt_boundary_has_a_model decrypt_shapes_are_predicates run_draw_not_trivial retryRunBounds_not_trivial tripleRefusalOpen_false_of_ok tripleRefusalOpen_false_of_store_full decrypt_ratchet_refines_at_sample sample_model_refuses succ_model_accepts succ_run_satisfiable hypotheses_meet_refusal_and_success evict_decode_model evict_headroom evict_run_satisfiable evict_first_attempt_full hypotheses_meet_eviction_round decrypt_ratchet_refines_at_eviction decrypt_ratchet_refines_from_shapes evict_reaches_receive receiveWithEviction_first_round evict_loop_first_round decrypt_ratchet_refines_from_shapes_at_eviction
UnitLifecycleTripleRefusalT3 Tacenta.UnitLifecycleTripleRefusalT3 derive_chain_loop_ok derive_chain_refines_far ratchet_skip_refusal_refines ratchet_receive_tail_refusal_refines ratchet_receive_refusal_refines spqr_skip_refusal_refines spqr_receive_continuation_refusal_refines spqr_receive_refusal_refines triple_receive_refusal_refines
UnitLifecycleDecryptRatchetCompleteT3 Tacenta.UnitLifecycleDecryptRatchetCompleteT3 concrete_receive_attempt_refusal_from_retry_bounds openRefusal_closes receive_with_eviction_refines_complete decrypt_ratchet_refines_complete decrypt_ratchet_refines_complete_statement decrypt_ratchet_refines_complete_implies_refines
UnitLifecycleDecryptRatchetCompleteScreen Tacenta.UnitLifecycleDecryptRatchetCompleteScreen ref_model_triple_refuses ref_premises ref_triple_refuses ref_headroom ref_run_satisfiable ref_model_refuses hypotheses_meet_open_path decrypt_ratchet_refines_complete_at_refusal generated_reaches_open_path
UnitLifecycleDecryptRatchetT3 Tacenta.UnitLifecycleDecryptRatchetT3 decrypt_ratchet_refines_or_open or_unless_closed
UnitLifecycleEstablishInitiatorShape Tacenta.UnitLifecycleEstablishInitiatorShape singleton_length_le init_sender_ok braid_initiator_ok verify_bundle_ok establish_initiator_for_parts dhPublicValid_is model_dhPublicValid kemCiphertextLenOf_is model_kemCiphertextLen dhPublicValid_canonical dhPublicValid_valid identity_public_valid canonical_of_is_canonical_key initiatorTriple_invariant structural_parts parts_invariant establish_initiator_for_admissible counterHeadroom_parts counterHeadroom_of_established sessionRefines_parts sessionRefines_established sessionRefines_parts_unique sessionRefines_established_unique model_initiatorSuccess verify_successBundle shared_secret_successBundle establish_initiator_for_succeeds established_initiator_inhabited establishment_hypotheses_satisfiable
UnitLifecycleEstablishedDecrypt Tacenta.UnitLifecycleEstablishedDecrypt honestChunk_established established_initiator_decrypt_ratchet_hypotheses established_initiator_decrypt_ratchet_refines established_initiator_decrypt_refines EstablishedDecryptHypotheses.refines sampleMessage_real_type sampleMessage_chunk established_decrypt_hypotheses_jointly_satisfiable oneKey_length oneKey_canonical oneKey_ne_zero established_decrypt_laws_model
UnitLifecycleEstablishResponder Tacenta.UnitLifecycleEstablishResponder signed_prekey_err kem_slot_err curve_inputs_err one_time_key_err decapsulate_err contributory_break_err shared_secret_err replay_err commit_kem_step commit_one_time_step init_receiver_ok braid_responder_ok hdr_decoder_ok vecU8_clone_eq curve_inputs_ok ResponderPreparedParts.ratchetPrivate_eq ResponderPreparedParts.braidSecret_eq ResponderPreparedParts.ephemeralCopy_eq fresh_decoder_invariant hdr_decoder_checks responderTriple_invariant responder_structural responder_prepared_invariant counterHeadroom_responder_prepared sessionRefines_responder_prepared honestChunk_responder_iff decryptRatchet_oracle take_one_time_kem_loop_frame take_one_time_kem_frame take_one_time_loop_frame take_one_time_frame vec_push_ok responderCommit_effects replay_ok establish_responder_cases random32_draws responder_prepared_decrypt_refines establish_responder_refines readBe32_be32 takeSplit_append decodeInitial_encodeInitial wireKey_length wireKey_curve wireKey_key ephKey_length ephKey_curve ephKey_key successBytes_length successBytes_le decode_successMessage replay_fresh map_u8_inj u32_of_ofNat basePoint_length arrayOf_basePoint basePoint_canonical successMessage_decoded decode_ec_wireKey responder_shared_secret_ok responder_prepared_inhabited establish_responder_returns establish_responder_short_message_refused establish_responder_at_parts establish_responder_unknown_prekey_refused establish_responder_legacy_refused array_eq_decide replay_loop_absent seen_for_loop_all array_eq_self decode_ec_zeroWire establish_responder_noncontributory_refused ResponderRouteHypotheses.refines sampleMessage_le responder_route_hypotheses_jointly_satisfiable establish_responder_replay_refused full_record_length_le otherThan_ne establish_responder_record_full_refused responder_route_inner_refusal_reachable responder_route_laws_model
UnitLifecycleDecryptT3 Tacenta.UnitLifecycleDecryptT3 decrypt_refines_ratchet_frame decrypt_refines_ratchet_frame_statement decrypt_refines_ratchet_frame_of_invariant decrypt_refines_ratchet_frame_of_counter_headroom decrypt_frame_hypotheses_jointly_satisfiable decrypt_refines_ratchet_frame_of_hypotheses decrypt_frame_at_invReal succMessage_not_initial sampleMessage_not_initial decrypt_refines_ratchet_frame_at_refusal refReal_fails_invariant inv_sessionRefines inv_retryRunBounds inv_run_satisfiable inv_model_refuses decrypt_refines_ratchet_frame_of_invariant_at_sample decrypt_refines_ratchet_frame_of_invariant_exists pendReal_fails_invariant decrypt_refines_ratchet_frame_at_pending_success pend_model_clears generated_clears_at_pending_success
UnitLifecycleSessionCodec Tacenta.UnitLifecycleSessionCodec efs_val be32_length be64_length fromBEBytes_toNat_congr fromLEBytes_toNat_congr fromBEBytes_toBEBytes_toNat from_be32 drop_next slice_of_drop length_of_drop getElem_of_drop from_slice_eq index_usize_of read_key_of read_u32_of read_optional_key_loop_zero read_optional_key_of usize_add_eq usize_div_eq slice_len_eq arr32_len optKeyEnc_length ratchetEnc_length push_optional_key_enc ratchet_to_bytes_loop_empty ratchet_to_bytes_loop_empty_spec label_to_byte_spec zeroizing_new_spec ratchet_to_bytes_spec ratchet_from_bytes_of chain_len_eq chains_len_eq skipped_len_eq fixed_prefix_eq chainEnc_length spqrEnc_length push_optional_chain_some spqr_to_bytes_loop0_one spqr_to_bytes_loop1_empty direction_to_byte_spec spqr_encoded_len_eq spqr_to_bytes_spec from_be64 u64_eq_of_bv u32_eq_of_bv decode_chain_of decode_chains_entry_of spqr_from_bytes_loop0_one spqr_from_bytes_loop1_empty direction_from_byte_dirByte spqr_from_bytes_of tripleEnc_length triple_to_bytes_spec triple_take_len_prefixed_of triple_invariant_parts triple_from_bytes_of authEnc_length setSlice_app auth_to_bytes_spec auth_from_bytes_of head_len_eq epoch_and_auth_len_eq braidEnc_length braid_to_bytes_spec read_u64_of read_epoch_of read_auth_of decode_state_unsampled_of braid_from_bytes_of lifecycle_take_len_prefixed_of vecAsSliceImpl_shape dhPublicBytesRoundTrip_is model_dhPublicBytesRoundTrip dhPrivateBytesRoundTrip_is model_dhPrivateBytesRoundTrip zeroizingVecRoundTrip_is model_zeroizingVecRoundTrip cast_len_val lenEnc_length lifecycle_push_len_prefixed_spec pendEnc_length pending_to_bytes_spec pending_from_bytes_of
UnitLifecycleSessionRoundTrip Tacenta.UnitLifecycleSessionRoundTrip export_spec import_unchecked_spec slice_ne_self session_invariant_leaves export_import_of_shape identity_ad_length_of
UnitLifecycleRestoredSession Tacenta.UnitLifecycleRestoredSession import_ok_gives_invariant counterHeadroom_iff_check sessionRefines_restored sessionRefines_restored_unique honestChunk_restored RestoredDecryptHypotheses.ofInvariant RestoredDecryptHypotheses.refines restored_decrypt_refines model_kemCiphertextLenBound codecShape_parts export_import_established restored_established_continues restored_established_initiator_decrypt_refines restored_established_inhabited restored_laws_model restored_laws_model_established restored_decrypt_hypotheses_jointly_satisfiable restored_decrypt_laws_model
UnitLifecycleEstablishedEncrypt Tacenta.UnitLifecycleEstablishedEncrypt keyGenAnswers_is keyGenSeededFor_is keyGenSizes_wrapperKemOf keyGenSizes_wrapperKem step_send_keysUnsampled_pinned braid_send_keysUnsampled_pinned send_keysUnsampled_output sendAgreement_keysUnsampled_output two_of_length braidSendTraceCounted_of_keysUnsampled braidSendTraceCounted_established identityAd_length_parts kemCiphertext_length_parts encryptHeadroom_parts encryptHeadroom_established tripleStoreFacts_parts sparseOutput_none_of_evidence encryptProviders_established established_initiator_encrypt_refines established_triple_send_ok established_encrypt_model_cases state_failed_of_refines state_keysSampled_of_refines established_encrypt_outcomes established_triple_next_counters established_encrypt_successor_counterHeadroom established_encrypt_successor_refines EstablishedEncryptHypotheses.refines zeroizingKeys_is nil_length_le byteTrace_two established_encrypt_hypotheses_jointly_satisfiable two_draws_of_64 established_encrypt_outcomes_at_witness established_encrypt_success_reachable established_encrypt_refusal_reachable genFill_answers modelEncrypt_keyGenSeeded modelEncrypt_kemAgrees modelEncrypt_keyPairGenerate modelEncrypt_kemEncapsulate byteRng_rngTotal modelEncrypt_allT1 leValue_replicate_zero toyKemR_seeds toyKemR_sizes established_encrypt_laws_model encrypt_ok_parts array_eq_of_bytes triple_eq_sent sentTriple_invariant structural_sent keysSampled_invariant sent_invariant keyPairValid_of_header encoder_of_refines established_encrypt_successor_admissible established_encrypt_successor_hypotheses authOf_injective established_encrypt_successor_shape EstablishedEncryptSuccessorHypotheses.successor established_encrypt_successor_hypotheses_jointly_satisfiable established_encrypt_successor_reachable
UnitLifecycleResponderFirstFrame Tacenta.UnitLifecycleResponderFirstFrame bundle_with_own establish_initiator_for_secret dhAgreeSymmetric_is shared_secret_symmetric vec_index_last publish_parts one_time_kem_ids_spec u32_index_first peek_one_time_first canonicalKey_arrayOf view_of_public identity_public_of_dh_key ciphertext_le decode_first_frame decode_ec_public curve_inputs_of contains_u32 signed_prekey_own kem_slot_last_resort kem_slot_one_time decapsulate_current decapsulate_one_time one_time_key_absent one_time_key_last nodup_append_disjoint distinct_kem_last distinct_pool_last heldKemPair_last replay_loop_flag replay_refusal_cause establish_responder_slot_refused establish_responder_replay_refused_at parts_of_steps responder_first_frame_prepares responder_first_frame_admissible first_send_responder_prepares basePoint_ne_zero modelFirstFrame_dhCodec modelFirstFrame_dhAgree modelFirstFrame_symmetric first_frame_laws_model publish_reachStore reachStore_distinct random_secret_byte reach_establishment first_send_responder_reachable
UnitLifecycleResponderFirstReceipt Tacenta.UnitLifecycleResponderFirstReceipt first_send_key first_receive_key first_receive_with_eviction readBe64_be64_kernel readBe16_be16_kernel decode_encodeMessage first_frame_model_outcomes aeadRoundTrip_is dhAgreeContributory_is first_init_pair established_triple_first responder_triple_first first_kdf_model zeroized_eq parts_of_first_frame view_ratchet_public responder_first_agreement responder_candidate_agreement first_identityAd_eq arrayOf_arrayOfBytes aead_open_sealed attributedView_send firstFrame_attributedView first_receipt_run_inputs firstAd_length_le responder_first_frame_inner_outcomes responder_first_frame_inner_succeeds establish_responder_commit_of_inner establish_responder_refused_of_inner responder_first_frame_outcomes responder_first_frame_succeeds initiator_first_send_responder_receives initiator_first_send_responder_outcomes modelFirstReceipt_dhCodec modelFirstReceipt_dhAgree modelFirstReceipt_symmetric modelFirstReceipt_aeadOpen modelFirstReceipt_aeadSeal modelFirstReceipt_aeadRoundTrip modelFirstReceipt_contributory first_receipt_laws_model first_send_receive_reachable
UnitLifecycleResponderSuccessor Tacenta.UnitLifecycleResponderSuccessor decrypt_ratchet_ok_parts braid_receive_noHeader one_chunk_loop decoder_invariant_small add_chunk_fresh_have received_decoder_checks triple_eq_received receivedTriple_invariant structural_received received_invariant first_receipt_successor_shape received_counterHeadroom first_receipt_successor_facts responder_first_frame_successor initiator_first_send_responder_successor_hypotheses initiator_first_send_responder_successor_admissible initiator_first_send_responder_successor_counterHeadroom first_send_receive_successor_reachable
UnitLifecycleResponderReply Tacenta.UnitLifecycleResponderReply array_clone_u8 auth_clone_eq braid_send_noHeader sendAgreement_noHeader_output braidSendTraceCounted_of_noHeader reply_send_key replyFrame_with_draws reply_model_step sparseOutput_none_of_noHeader encryptProviders_reply encryptHeadroom_reply oracleOf_with_draws noHeader_of_receipt_refines pendingInitial_none_of_receipt_refines responder_reply_refines responder_first_frame_successor_keys initiator_first_send_responder_successor_keys initiator_first_send_responder_replies first_send_reply_reachable
UnitLifecycleResponderReplyReceipt Tacenta.UnitLifecycleResponderReplyReceipt reply_receive_key reply_receive_stale replyFrame_messageType replyFrame_decodeDetailed reply_receipt_model_outcomes fresh_public_of_draw initiator_reply_agreement initiator_candidate_agreement first_send_model_session replyAd_length_le initiator_receives_reply_outcomes initiator_receives_reply_two_outcomes initiator_receives_reply replyPub_canonical replyPub_ne_zero replyPub_basePoint replyPub_oneKey replyPub_zeros dhPublicNotConstant_is modelReply_dhCodec modelReply_dhAgree modelReply_symmetric modelReply_contributory modelFirstReceipt_not_notConstant modelReply_notConstant reply_receipt_laws_model byteTrace_one byteTrace_seed_extra two_draws_of_seed_extra reply_receipt_reach_run first_send_reply_receipt_reachable first_send_reply_stale_reachable
UnitTripleInvModel Tacenta.UnitTripleInvModel keyOf_injective keyOf_inj_iff canonicalKey_keyOf u32_max_eq_model u64_max_eq_model ratchet_inv_iff_model window_end_val spqr_inv_iff_model triple_invariant_true_iff rolesAgree_iff_model triple_invariant_iff_model
UnitLifecycleSendPreserve Tacenta.UnitLifecycleSendPreserve ratchet_send_frame modelRatchetInv_send findChains_mem spqr_send_frame mem_sent_chains modelSpqrInv_send modelTripleInv_send braid_send_no_draw_model encrypt_session_cases counterRoom_zero epoch_val_refines counterRoom_iff_model modelCounterRoom_encrypt sendsWithoutDraw_of_refines vec_clone_u8 encoder_clone_eq decoder_clone_eq next_chunk_keeps encoder_sized_congr key_pair_valid_clone braid_send_no_draw session_invariant_iff structural_congr encrypt_ok_not_failed encrypt_keeps_invariant_no_draw modelCounterRoom_firstReceipt initiator_first_send_responder_reply_successor initiator_first_send_responder_reply_admissible established_encrypt_triple_invariant_via_preservation
UnitLifecycleInitiatorSecondSend Tacenta.UnitLifecycleInitiatorSecondSend send_output_none_of_no_draw sparseOutput_none_of_no_draw encryptProviders_of_invariant braid_send_keysSampled braidSendTraceCounted_of_keysSampled second_send_key secondFrame_with_draws second_model_step initiator_second_send_refines first_send_model_session_encoder initiator_second_send_after_reply
LIST

# The joint decision of the clauses of `OracleOf` (UnitOracle*.lean): every axiom pin, every statement
# pin and every definition pin deleted in turn.
while IFS=' ' read -r file ns names; do
  for n in $names; do
    make_case
    python3 - "$work/tacenta-proofs/translation/Translation/$file.lean" "$ns.$n" <<'PY'
import pathlib, re, sys
path = pathlib.Path(sys.argv[1])
text = path.read_text()
name = sys.argv[2]
block = re.compile(
    r"/--\s*info: '" + re.escape(name) + r"'.*?-/\s*\n#guard_msgs in\s*\n#print axioms\s+" + re.escape(name) + r"\n",
    re.S,
)
new, n = block.subn("", text)
assert n == 1, n
path.write_text(new)
PY
    expect_fail "required-pin-deleted-$file-$n" "\`$ns.$n\` is on REQUIRED_PINS and has no axiom pin" --check
  done
done <<'LIST'
UnitOracleShape Tacenta.UnitOracleShape isValidIdentityKey_is oracleOf_iff_shape oracleOfShape_iff_clauses dhCodecOf_iff_shape generateFillsOnce64_iff_shape liftView_spec dhPublicClause_of_laws dhAgreeClause_of_laws identityValidClause_of_laws aeadSealClause_of_laws aeadOpenClause_of_laws kemDecapsulateClause_of_laws sigVerifyClause_of_laws
UnitOracleModel Tacenta.UnitOracleModel modelO_axiomBase modelO_laws
UnitOracleDh Tacenta.UnitOracleDh dh_clauses_in_model
UnitOracleAead Tacenta.UnitOracleAead aead_clauses_in_model
UnitOracleKemSig Tacenta.UnitOracleKemSig oracleOfGuarded_iff_shape kemGuardedClause_of_law kemClauses_of_guarded never_encapsulating_meets_kemClauses never_encapsulating_fails_guarded guarded_separates_never_encapsulating kem_sig_clauses_in_model
UnitOracleJoint Tacenta.UnitOracleJoint oracleLaws_real_iff oracleOfShape_of_oracleLaws oracleOfGuarded_of_laws oracleOf_of_laws oracleLaws_hold_jointly oracleOf_joint_model oracleOf_inhabited_jointly
LIST
while IFS=' ' read -r file ns names; do
  for n in $names; do
    make_case
    python3 - "$work/tacenta-proofs/translation/Translation/$file.lean" "$ns.$n" <<'PY'
import pathlib, re, sys
path = pathlib.Path(sys.argv[1])
text = path.read_text()
name = sys.argv[2]
block = re.compile(
    r"/--\s*info: (?:(?!-/).)*?-/\s*\n#guard_msgs in\s*\n#(?:print |check @)" + re.escape(name) + r"\n",
    re.S,
)
new, n = block.subn("", text)
assert n == 1, n
path.write_text(new)
PY
    expect_fail "statement-pin-deleted-$ns.$n" "\`$ns.$n\` is on REQUIRED_STATEMENT_PINS and has no statement pin" --check
  done
done <<'LIST'
UnitOracleShape Tacenta.UnitOracleShape DhViewInjective KemViewInjective GenerateFillsOnce64Shape oracleOfLaws DhPublicClause DhAgreeClause IdentityValidClause AeadSealClause AeadOpenClause KemDecapsulateClause SigVerifyClause
UnitOracleShape Tacenta.UnitOracleShape isValidIdentityKey_is oracleOf_iff_shape oracleOfShape_iff_clauses dhCodecOf_iff_shape generateFillsOnce64_iff_shape liftView_spec dhPublicClause_of_laws dhAgreeClause_of_laws identityValidClause_of_laws aeadSealClause_of_laws aeadOpenClause_of_laws kemDecapsulateClause_of_laws sigVerifyClause_of_laws
UnitOracleModel Tacenta.UnitOracleModel InterpO.model oracleM modelO_axiomBase modelO_laws
UnitOracleDh Tacenta.UnitOracleDh dh_clauses_in_model
UnitOracleAead Tacenta.UnitOracleAead aead_clauses_in_model
UnitOracleKemSig Tacenta.UnitOracleKemSig KemGuardedClause OracleOfGuarded oracleOfGuarded_iff_shape kemGuardedClause_of_law kemClauses_of_guarded never_encapsulating_meets_kemClauses never_encapsulating_fails_guarded guarded_separates_never_encapsulating kem_sig_clauses_in_model
UnitOracleJoint Tacenta.UnitOracleJoint OracleLaws oracleLaws_real_iff oracleOfShape_of_oracleLaws oracleOfGuarded_of_laws oracleOf_of_laws oracleLaws_hold_jointly oracleOf_joint_model oracleOf_inhabited_jointly
UnitOracleJoint Tacenta.UnitLifecycleT1 DhCodecTotal DhAgreeTotal DhIdentityTotal AeadSealBounded AeadOpenTotal KemDecapsulateTotal XeddsaVerifyTotal NoPanic
UnitOracleJoint Tacenta.UnitSatisfiabilityJoint DhCodecShape DhAgreeShape DhIdentityShape AeadSealBoundedShape AeadOpenShape KemDecapsulateShape XeddsaVerifyShape Np
LIST
# A definition the joint decision's laws rest on, held to the `#print` form: its pin rewritten as
# `#check @`, which prints the type and not the body, is refused, for two of the totality predicates
# and their shapes and for two of the integration screen's laws.
for spec in UnitOracleJoint:Tacenta.UnitLifecycleT1.AeadSealBounded \
  UnitOracleJoint:Tacenta.UnitSatisfiabilityJoint.AeadSealBoundedShape \
  UnitLifecycleIntegrationScreen:Tacenta.UnitLifecycleIntegrationScreen.SignFillsOnce64Of \
  UnitLifecycleIntegrationScreen:Tacenta.UnitLifecycleIntegrationScreen.KemShape; do
  file="tacenta-proofs/translation/Translation/${spec%%:*}.lean"
  name="${spec#*:}"
  make_case
  replace_in "$file" $'#guard_msgs in\n#print '"$name"$'\n' $'#guard_msgs in\n#check @'"$name"$'\n'
  expect_fail "definition-pin-check-form-$name" "\`$name\` is on REQUIRED_STATEMENT_PINS and its pin at $file:" --check
  expect_fail "definition-pin-check-form-$name-says-why" "is \`#check @$name\`, which prints the type and not the body" --check
done

# The sparse total bound's pins (Proofs/SparseReplacementBound.lean), each deleted in turn. They
# are in the proofs package, not the translation package, so they have their own block.
for n in mem_skipSurvivors_iff skipSurvivors_length_le skipMessageKeys_refused_iff \
         skipMessageKeys_leaves_survivors_then_batch skipMessageKeys_keeps_outside_range \
         skipMessageKeys_keeps_the_key_at_the_counter skipMessageKeys_replaces_the_range \
         replacement_accepts_where_the_count_before_the_deletion_refuses \
         witness_premises_hold witness_refused_one_key_further; do
  make_case
  python3 - "$work/tacenta-proofs/Proofs/SparseReplacementBound.lean" "Proofs.SparseReplacementBound.$n" <<'PY'
import pathlib, re, sys
path = pathlib.Path(sys.argv[1])
text = path.read_text()
name = sys.argv[2]
block = re.compile(
    r"/--\s*info: '" + re.escape(name) + r"'.*?-/\s*\n#guard_msgs in\s*\n#print axioms\s+" + re.escape(name) + r"\n",
    re.S,
)
new, n = block.subn("", text)
assert n == 1, n
path.write_text(new)
PY
  expect_fail "required-pin-deleted-SparseReplacementBound-$n" "\`Proofs.SparseReplacementBound.$n\` is on REQUIRED_PINS and has no axiom pin" --check
done

make_case
python3 - "$work/$session_pins" <<'PY'
import pathlib, re, sys
path = pathlib.Path(sys.argv[1])
text = path.read_text()
name = "Tacenta.UnitLifecycleT1.encrypt_no_panic"
block = re.compile(
    r"/--\s*info: '" + re.escape(name) + r"'.*?-/\s*\n#guard_msgs in\s*\n#print axioms\s+" + re.escape(name) + r"\n",
    re.S,
)
new, n = block.subn(lambda m: "/-\n" + m.group(0) + "-/\n", text)
assert n == 1, n
path.write_text(new)
PY
expect_fail "required-pin-commented-out" "sit inside a comment or a string" --check

# A lone carriage return inside a line comment, with every line of a pin joined
# by one: Python's default reading ends a line at each, Lean does not, so the pin
# was a live, counted axiom pin to a reader that translated newlines and one
# comment line to Lean (the eighteenth hostile read's H2). attest reads without
# translation and refuses the file outright.
make_case
python3 - "$work/$session_pins" <<'PY'
import pathlib, sys
path = pathlib.Path(sys.argv[1])
text = path.read_text()
forged = ("-- c\r/-- info: 'Tacenta.Forged.pin' depends on axioms: [propext]\r-/\r"
          "#guard_msgs in\r#print axioms Tacenta.Forged.pin\n")
with path.open("w", newline="") as fh:
    fh.write(text + forged)
PY
expect_fail "pin-after-carriage-return" "carriage return" --check

make_case
python3 - "$work/$session_pins" <<'PY'
import pathlib, sys
path = pathlib.Path(sys.argv[1])
text = path.read_text()
anchor = "info: 'Tacenta.UnitLifecycleT1.decrypt_no_panic' depends on axioms: [propext,"
assert text.count(anchor) == 1
path.write_text(text.replace(anchor, anchor + "\n Tacenta.UnitLifecycleT1.full_store_eq_no_panic._native.native_decide.ax_1_2,"))
PY
expect_fail "compiler-trust-pin-not-listed" "\`Tacenta.UnitLifecycleT1.decrypt_no_panic\` is pinned as compiler-trusted and is not on COMPILER_TRUSTED_PINS" --check
expect_fail "compiler-trust-pin-refused-by-refresh" "\`Tacenta.UnitLifecycleT1.decrypt_no_panic\` is pinned as compiler-trusted and is not on COMPILER_TRUSTED_PINS"

# The field's pins are kernel-only and are on no ceiling: a compiler-trust axiom put back under
# `interp_eq` (the case the stale ceiling entry used to accept) is refused, and so is deleting any
# of the three pins in `Proofs/TrustedBase.lean`; the fourth, `ErasureT3.mul_refines`, is in the LIST below.
make_case
python3 - "$work/tacenta-proofs/Proofs/TrustedBase.lean" <<'PY'
import pathlib, sys
path = pathlib.Path(sys.argv[1])
text = path.read_text()
old = "info: 'Model.Polynomial.interp_eq' depends on axioms: [propext, Classical.choice, Quot.sound]"
assert text.count(old) == 1
path.write_text(text.replace(old, "info: 'Model.Polynomial.interp_eq' depends on axioms: [propext,\n Classical.choice,\n Quot.sound,\n Model.Gf65536.mul_one._native.bv_decide.ax_1_9]"))
PY
expect_fail "field-pin-compiler-trust-returns" "\`Model.Polynomial.interp_eq\` is pinned as compiler-trusted and is not on COMPILER_TRUSTED_PINS" --check
expect_fail "field-pin-compiler-trust-refused-by-refresh" "\`Model.Polynomial.interp_eq\` is pinned as compiler-trusted and is not on COMPILER_TRUSTED_PINS"

for n in Model.Gf65536.mul_assoc Model.Gf65536.mul_inv_cancel Model.Polynomial.interp_eq; do
  make_case
  python3 - "$work/tacenta-proofs/Proofs/TrustedBase.lean" "$n" <<'PY'
import pathlib, re, sys
path = pathlib.Path(sys.argv[1])
text = path.read_text()
name = sys.argv[2]
block = re.compile(
    r"/--\s*info: '" + re.escape(name) + r"'.*?-/\s*\n#guard_msgs in\s*\n#print axioms\s+" + re.escape(name) + r"\n",
    re.S,
)
new, n = block.subn("", text)
assert n == 1, n
path.write_text(new)
PY
  expect_fail "required-pin-deleted-trustedbase-$n" "\`$n\` is on REQUIRED_PINS and has no axiom pin" --check
done

# The sparse ratchet's and the Triple's refinement constants, kernel proofs since 2026-10-21 (they were
# `native_decide`), and the results that rested on them: none is on COMPILER_TRUSTED_PINS any more, so a
# compiler-trust axiom put back under one, in a multi-line or a one-line pin, is refused; the ceiling is exact,
# so an entry whose pin lists no compiler-trust axiom (or that has no pin) is refused; and each newly required
# pin, deleted, is refused.
tr="tacenta-proofs/translation/Translation"
plant_native() {  # file theorem axiom
  python3 - "$work/$1" "$2" "$3" <<'PY'
import pathlib, sys
path, name, ax = pathlib.Path(sys.argv[1]), sys.argv[2], sys.argv[3]
text = path.read_text()
multi = f"info: '{name}' depends on axioms: [propext,\n"
one = f"info: '{name}' depends on axioms: [propext, Classical.choice, Quot.sound]"
if text.count(multi) == 1:
    text = text.replace(multi, multi + f" {ax},\n")
else:
    assert text.count(one) == 1, (name, text.count(one))
    text = text.replace(one, f"info: '{name}' depends on axioms: [propext,\n Classical.choice,\n Quot.sound,\n {ax}]")
path.write_text(text)
PY
}
kernel_constant_plants=(
  "SpqrT3.lean Tacenta.SpqrT3.receive_refines Tacenta.SpqrT3.receive_refines_continuation._native.native_decide.ax_1_29"
  "SessionT3.lean Tacenta.SessionT3.shared_secret_refines_some Tacenta.SessionT3.fPrefix_agrees._native.native_decide.ax_1_1"
  "UnitLifecycleDecryptRatchetCompleteT3.lean Tacenta.UnitLifecycleDecryptRatchetCompleteT3.decrypt_ratchet_refines_complete Tacenta.SessionUnitSpqrT3.max_skip_val._native.native_decide.ax_1_1"
  "UnitLifecycleEstablishedEncrypt.lean Tacenta.UnitLifecycleEstablishedEncrypt.established_encrypt_outcomes Tacenta.SessionUnitTripleT3.combine_info_agrees._native.native_decide.ax_1_1"
  "UnitLifecycleResponderFirstReceipt.lean Tacenta.UnitLifecycleResponderFirstReceipt.responder_first_frame_succeeds Tacenta.SessionUnitSpqrT3.protocol_info_agrees._native.native_decide.ax_1_1"
  "AxiomAuditSessionUnit.lean Tacenta.SessionUnitSpqrT3.protocol_info_agrees Tacenta.SessionUnitSpqrT3.protocol_info_agrees._native.native_decide.ax_1_1"
  "AxiomAuditSessionUnit.lean Tacenta.SessionUnitTripleT3.combine_info_agrees Tacenta.SessionUnitTripleT3.combine_info_agrees._native.native_decide.ax_1_1"
)
for spec in "${kernel_constant_plants[@]}"; do
  read -r file name ax <<< "$spec"
  make_case
  plant_native "$tr/$file" "$name" "$ax"
  expect_fail "kernel-constant-compiler-trust-returns-${name##*.}" "\`$name\` is pinned as compiler-trusted and is not on COMPILER_TRUSTED_PINS" --check
done
make_case
plant_native "$tr/AxiomAuditSessionUnit.lean" Tacenta.SessionUnitSpqrT3.max_skip_val Tacenta.SessionUnitSpqrT3.max_skip_val._native.native_decide.ax_1_1
expect_fail "kernel-constant-compiler-trust-refused-by-refresh" "\`Tacenta.SessionUnitSpqrT3.max_skip_val\` is pinned as compiler-trusted and is not on COMPILER_TRUSTED_PINS"

ceiling_add() {  # name
  python3 - "$work/tacenta-proofs/scripts/attest.py" "$1" <<'PY'
import pathlib, sys
path, name = pathlib.Path(sys.argv[1]), sys.argv[2]
text = path.read_text()
head = "COMPILER_TRUSTED_PINS = frozenset(\n    {\n"
assert text.count(head) == 1
path.write_text(text.replace(head, head + f'        "{name}",\n'))
PY
}
make_case
ceiling_add Tacenta.SpqrT3.receive_refines
expect_fail "compiler-ceiling-stale-entry" "\`Tacenta.SpqrT3.receive_refines\` is on COMPILER_TRUSTED_PINS and its pin lists no compiler-trust axiom" --check
expect_fail "compiler-ceiling-stale-entry-refused-by-refresh" "\`Tacenta.SpqrT3.receive_refines\` is on COMPILER_TRUSTED_PINS and its pin lists no compiler-trust axiom"
make_case
ceiling_add Tacenta.UnitLifecycleSessionRoundTrip.export_message_fits
expect_fail "compiler-ceiling-kernel-only-entry" "\`Tacenta.UnitLifecycleSessionRoundTrip.export_message_fits\` is on COMPILER_TRUSTED_PINS and its pin lists no compiler-trust axiom" --check
make_case
ceiling_add Tacenta.NoSuchModule.no_such_theorem
expect_fail "compiler-ceiling-unpinned-entry" "\`Tacenta.NoSuchModule.no_such_theorem\` is on COMPILER_TRUSTED_PINS and its pin lists no compiler-trust axiom" --check

kernel_constant_required=(
  "AxiomAuditSessionUnit.lean Tacenta.SessionUnitSpqrT3.protocol_info_agrees"
  "AxiomAuditSessionUnit.lean Tacenta.SessionUnitSpqrT3.chain_start_agrees"
  "AxiomAuditSessionUnit.lean Tacenta.SessionUnitSpqrT3.root_label_agrees"
  "AxiomAuditSessionUnit.lean Tacenta.SessionUnitSpqrT3.chain_label_agrees"
  "AxiomAuditSessionUnit.lean Tacenta.SessionUnitSpqrT3.max_skip_agrees"
  "AxiomAuditSessionUnit.lean Tacenta.SessionUnitSpqrT3.max_skipped_store_agrees"
  "AxiomAuditSessionUnit.lean Tacenta.SessionUnitSpqrT3.max_skip_val"
  "AxiomAuditSessionUnit.lean Tacenta.SessionUnitSpqrT3.receive_refines_continuation"
  "AxiomAuditSessionUnit.lean Tacenta.SessionUnitTripleT3.combine_info_agrees"
  "AxiomAuditSessionUnit.lean Tacenta.SessionUnitTripleT3.split_info_agrees"
  "AxiomAuditSessionUnit.lean Tacenta.SessionUnitTripleT3.split_secret_refines"
  "UnitLifecycleSessionRoundTrip.lean Tacenta.UnitLifecycleSessionRoundTrip.export_message_fits"
  "SessionT3.lean Tacenta.SessionT3.shared_secret_refines_some"
  "SpqrT3.lean Tacenta.SpqrT3.send_refines"
  "SpqrT3.lean Tacenta.SpqrT3.receive_refines"
  "UnitPins.lean Tacenta.UnitSpqrT3.send_refines"
  "UnitPins.lean Tacenta.UnitSpqrT3.receive_refines"
  "UnitPins.lean Tacenta.UnitTripleT3.send_refines_discharged"
  "UnitPins.lean Tacenta.UnitTripleT3.receive_refines_discharged"
  "UnitPins.lean Tacenta.UnitTripleT3.spqr_agrees_for"
)
for spec in "${kernel_constant_required[@]}"; do
  read -r file name <<< "$spec"
  make_case
  python3 - "$work/$tr/$file" "$name" <<'PY'
import pathlib, re, sys
path = pathlib.Path(sys.argv[1])
text = path.read_text()
name = sys.argv[2]
block = re.compile(
    r"/--\s*info: '" + re.escape(name) + r"'.*?-/\s*\n#guard_msgs in\s*\n#print axioms\s+" + re.escape(name) + r"\n",
    re.S,
)
new, n = block.subn("", text)
assert n == 1, n
path.write_text(new)
PY
  expect_fail "required-pin-deleted-kernel-constant-${name#Tacenta.}" "\`$name\` is on REQUIRED_PINS and has no axiom pin" --check
done

make_case
python3 - "$work/$session_pins" <<'PY'
import pathlib, re, sys
path = pathlib.Path(sys.argv[1])
text = path.read_text()
def block(name):
    return re.compile(
        r"/--\s*info: '" + re.escape(name) + r"'.*?-/\s*\n#guard_msgs in\s*\n#print axioms\s+" + re.escape(name) + r"\n",
        re.S,
    )
first = "Tacenta.UnitLifecycleT1.encrypt_no_panic"
second = "Tacenta.UnitLifecycleT1.decrypt_no_panic"
copy = block(second).search(text).group(0)
new, n = block(first).subn(lambda _m: copy, text)
assert n == 1, n
path.write_text(new)
PY
expect_fail "pin-block-copied-over-another" "theorems pinned more than once: Tacenta.UnitLifecycleT1.decrypt_no_panic" --check

# ---------------------------------------------------------------------------
# Statement pins. `#guard_msgs in #check @name` holds a theorem's statement, and
# only the Lean build compared it: a deleted pin is a smaller file that builds, and
# the pins are not axiom pins, so REQUIRED_PINS does not see them. The floor
# REQUIRED_STATEMENT_PINS does. One floor name stands for the class: each mutation
# is made to the statement pin of `record_empty_headerSent`, and every one must be
# refused by the floor's own message naming that declaration. Deleting each pin of
# the floor in turn would test the same loop once per name. The accepted spellings are
# cases too, because a refusal is only evidence if the pin can be accepted.
# ---------------------------------------------------------------------------

stmt_name="Tacenta.DispatchEvidenceVacuity.record_empty_headerSent"
stmt_file="tacenta-proofs/translation/Translation/DispatchEvidenceVacuity.lean"
stmt_head="\`$stmt_name\` is on REQUIRED_STATEMENT_PINS and"

# Rewrite the statement pin of $stmt_name in $stmt_file. `mode` picks the mutation;
# `option` is the text between the parentheses of `#guard_msgs` for mode `options`.
rewrite_statement_pin() {
  python3 - "$work/$stmt_file" "$stmt_name" "$1" "${2:-}" <<'PY'
import pathlib, re, sys
path, name, mode, option = pathlib.Path(sys.argv[1]), sys.argv[2], sys.argv[3], sys.argv[4]
text = path.read_text()
pin = re.compile(r"#guard_msgs in\n#check @?" + re.escape(name) + r"\n")
hits = pin.findall(text)
assert len(hits) == 1, hits
block = hits[0]
new = {
    "delete": "",
    "line-comment": "".join("-- " + line + "\n" for line in block.splitlines()),
    "block-comment": "/-\n" + block + "-/\n",
    # The inner `-/` closes only the inner comment, so the pin is still commented out.
    "nested-comment": "/- outer\n/- inner -/\n" + block + "-/\n",
    "docstring": "/-- the pin of the next theorem:\n" + block + "-/\ndef statement_pin_doc : Nat := 0\n",
    "string": 'def statement_pin_text : String := "\n' + block + '"\n',
    "no-guard": "#check @" + name + "\n",
    "options": "#guard_msgs (" + option + ") in\n#check @" + name + "\n",
    "rename": "#guard_msgs in\n#check @" + name + "_renamed\n",
    "namespace": "namespace StatementPinScope\n" + block + "end StatementPinScope\n",
    # A `mutual` block closes with `end`, which must not pop the namespace around the pin.
    "mutual": ("namespace StatementPinScope\nmutual\ndef statementPinA : Nat -> Nat\n  | 0 => 0\n"
               "  | n + 1 => statementPinB n\ndef statementPinB : Nat -> Nat\n  | 0 => 0\n"
               "  | n + 1 => statementPinA n\nend\n" + block + "end StatementPinScope\n"),
    # The pin as the argument of an earlier `... in`: the outer command can swallow the
    # pin's own mismatch (`drop`) or change what it prints (`set_option`, `open`).
    "wrapped-drop-error": "#guard_msgs (drop error) in\n" + block,
    "wrapped-drop-all": "#guard_msgs (drop all) in\n" + block,
    "wrapped-set-option": "set_option pp.deepTerms false in\n" + block,
    "wrapped-open": "open Nat in\n" + block,
    "term": "#guard_msgs in\n#check @" + name + " x\n",
    "at-sign": "#guard_msgs in\n#check @" + name + "\n",
}[mode]
path.write_text(text.replace(block, new))
PY
}

make_case
expect_pass "statement-pins-unmodified-tree" --check

make_case
rewrite_statement_pin delete
expect_fail "statement-pin-deleted" "$stmt_head has no statement pin: no active \`#guard_msgs in\` followed by \`#check @$stmt_name\`" --check
expect_fail "statement-pin-deleted-refused-by-refresh" "$stmt_head has no statement pin"

for mode in line-comment block-comment nested-comment docstring string; do
  make_case
  rewrite_statement_pin "$mode"
  expect_fail "statement-pin-$mode" "$stmt_head its statement pin at $stmt_file:" --check
  expect_fail "statement-pin-$mode-says-why" "sits inside a comment, a docstring or a string, where Lean does not check it" --check
done

make_case
rewrite_statement_pin no-guard
expect_fail "statement-pin-without-guard-msgs" "is not under \`#guard_msgs in\`, so the build compares nothing" --check

make_case
rewrite_statement_pin rename
expect_fail "statement-pin-renamed-declaration" "$stmt_head has no statement pin" --check

make_case
rewrite_statement_pin term
expect_fail "statement-pin-of-an-application-not-a-name" "$stmt_head has no statement pin" --check

make_case
rewrite_statement_pin namespace
expect_fail "statement-pin-inside-namespace" "its statement pin at $stmt_file:" --check
expect_fail "statement-pin-inside-namespace-says-why" "sits inside \`StatementPinScope\`; write it after \`end\` with the full name" --check

# The mutual block that follows a namespace is the same refusal as the namespace alone.
make_case
rewrite_statement_pin mutual
expect_fail "statement-pin-after-mutual-inside-namespace" "its statement pin at $stmt_file:" --check
expect_fail "statement-pin-after-mutual-inside-namespace-says-why" "sits inside \`StatementPinScope\`; write it after \`end\` with the full name" --check

# A pin that is the argument of an earlier `... in` is not the outermost command.
for mode in wrapped-drop-error wrapped-drop-all wrapped-set-option wrapped-open; do
  make_case
  rewrite_statement_pin "$mode"
  expect_fail "statement-pin-$mode" "its \`#guard_msgs\` at $stmt_file:" --check
  expect_fail "statement-pin-$mode-says-why" "is the argument of an earlier \`... in\`, which can swallow its mismatch or change what it prints; write the pin as its own command" --check
done

# Options that leave the `#check` message uncompared. `#guard_msgs` takes the first
# option that covers a kind of message, and a message no option covers passes through.
# Each is refused for its own reason, so a wrong reason string goes red.
covers="is the first option that covers \`info\` and it does not compare it, so the pin holds nothing"
uncovered="no option covers \`info\`, so the message \`#check\` prints passes through without being compared"
for entry in "drop all|$covers" "drop info|$covers" "pass info|$covers" "pass all|$covers" \
             "drop warning|$uncovered" "drop warning, drop error|$uncovered" "drop all, check info|$covers" \
             "whitespace := lax|compares the message with its whitespace removed" \
             "error := true|the option \`error := true\` is not one this gate reads, so it cannot say what is compared"; do
  option="${entry%%|*}"
  reason="${entry#*|}"
  make_case
  rewrite_statement_pin options "$option"
  expect_fail "statement-pin-option-$option" "its \`#guard_msgs ($option)\` at $stmt_file:" --check
  expect_fail "statement-pin-option-$option-says-why" "$reason" --check
done

# A pin whose expected message Lean cut off with `⋯` holds the statement only up to the cut, so
# a change after it builds. The headline of the send-preservation module, cut where Lean cut it
# before its module set `pp.deepTerms` (after the binder `AeadRoundTrip →`), is refused; so is an
# omitted proof printed without its proposition (`⟨[], ⋯⟩`, `pp.proofs.withType` off), while the
# same hole with its proposition, `(⋯ : P)`, is accepted by the unmodified tree above.
cut_name="Tacenta.UnitLifecycleSendPreserve.initiator_first_send_responder_reply_admissible"
cut_file="tacenta-proofs/translation/Translation/UnitLifecycleSendPreserve.lean"
make_case
python3 - "$work/$cut_file" "$cut_name" <<'PY'
import pathlib, re, sys
path, name = pathlib.Path(sys.argv[1]), sys.argv[2]
text = path.read_text()
pin = re.compile(r"(/--\ninfo: )((?:(?!-/).)*?)(\n-/\n#guard_msgs in\n#check @" + re.escape(name) + r"\n)", re.S)
hits = pin.findall(text)
assert len(hits) == 1, len(hits)
message = hits[0][1]
cut = message.index("AeadRoundTrip →") + len("AeadRoundTrip →")
assert "⋯" not in message
new, n = pin.subn(lambda m: m.group(1) + message[:cut] + "\n" + " " * 64 + "⋯" + m.group(3), text)
assert n == 1
path.write_text(new)
PY
expect_fail "statement-pin-cut-off" "the statement pin of \`$cut_name\` at $cut_file:" --check
expect_fail "statement-pin-cut-off-says-why" "prints \`⋯\` in its expected message" --check

make_case
replace_in "tacenta-proofs/translation/Translation/DispatchEvidenceVacuity.lean" \
  $'⟨[], (⋯ : 0 ≤ Usize.max)⟩ ⟨[], (⋯ : 0 ≤ Usize.max)⟩' $'⟨[], ⋯⟩ ⟨[], ⋯⟩'
expect_fail "statement-pin-untyped-proof-hole" "the statement pin of \`Tacenta.DispatchEvidenceVacuity.same_ephemeral_agreement_empty\` at tacenta-proofs/translation/Translation/DispatchEvidenceVacuity.lean:" --check

# A pretty-printer option other than the two that only widen a pin's message is refused wherever it
# is set: at file level before the pins (`pp.oneline` prints the first line and `[...]`, with no
# `⋯`), as an `... in` before a theorem, and inside a section.
for entry in "file|pp.oneline true" "file|pp.deepTerms false" "file|pp.maxSteps 100" \
             "file|pp.structureInstances.defaults false" "file|pp.proofs.withType false" \
             "in|pp.deepTerms false" "section|pp.proofs true"; do
  where="${entry%%|*}"
  option="${entry#*|}"
  make_case
  python3 - "$work/tacenta-proofs/translation/Translation/DispatchEvidenceVacuity.lean" "$where" "$option" <<'PY'
import pathlib, sys
path, where, option = pathlib.Path(sys.argv[1]), sys.argv[2], sys.argv[3]
text = path.read_text()
anchor = "set_option pp.deepTerms true\nset_option pp.proofs.withType true\n"
assert text.count(anchor) == 1
added = {"file": f"set_option {option}\n",
         "in": f"set_option {option} in\ntheorem pp_option_case : True := trivial\n",
         "section": f"section PpOptionCase\nset_option {option}\nend PpOptionCase\n"}[where]
path.write_text(text.replace(anchor, anchor + added))
PY
  expect_fail "pp-option-$where-${option// /-}" "\`set_option ${option}\` is a pretty-printer option PP_OPTIONS_ALLOWED does not hold" --check
done

# A definition pin (`#print`) with its `#guard_msgs` removed is refused for that, not as an
# absent pin.
print_name="Tacenta.BraidPreserve.Braid.sized"
print_file="tacenta-proofs/translation/Translation/BraidPreserve.lean"
make_case
replace_in "$print_file" $'#guard_msgs in\n#print '"$print_name"$'\n' $'#print '"$print_name"$'\n'
expect_fail "definition-pin-without-guard-msgs" "\`$print_name\` is on REQUIRED_STATEMENT_PINS and \`#print $print_name\` at $print_file:" --check
expect_fail "definition-pin-without-guard-msgs-says-why" "is not under \`#guard_msgs in\`, so the build compares nothing" --check

# The model's draw functions and the record bodies of the integration screen: each definition pin
# (and the one equation pin) deleted in turn is refused as a missing statement pin.
for name in Model.Lifecycle.braidSendDrawCount Model.Lifecycle.sendAgreement \
  Model.Lifecycle.braidSendNeedsDraw Model.Lifecycle.takeDraws Model.Lifecycle.takeDraws.eq_def \
  Model.Lifecycle.takeDraw Model.Lifecycle.braidRandomness Tacenta.UnitLifecycleT3.OracleOf \
  Tacenta.UnitLifecycleT3.BraidSendTraceAgreementCounted \
  Tacenta.UnitLifecycleT3.InitialRatchetTripleBranchContracts \
  Tacenta.UnitLifecycleT3.InitialRatchetAeadBranchContracts \
  Tacenta.UnitLifecycleT3.InitialRatchetBraidEvidenceContractsScoped \
  Tacenta.UnitLifecycleT3.verified; do
  make_case
  python3 - "$work/tacenta-proofs/translation/Translation/UnitLifecycleIntegrationScreen.lean" "$name" <<'PY'
import pathlib, re, sys
path = pathlib.Path(sys.argv[1])
text = path.read_text()
name = sys.argv[2]
block = re.compile(
    r"/--\s*info: (?:(?!-/).)*?-/\s*\n#guard_msgs in\s*\n#(?:print |check @)" + re.escape(name) + r"\n",
    re.S,
)
new, n = block.subn("", text)
assert n == 1, n
path.write_text(new)
PY
  expect_fail "statement-pin-deleted-$name" "\`$name\` is on REQUIRED_STATEMENT_PINS and has no statement pin" --check
done

# Package F (`UnitLifecycleRetryLoopT3.lean`, `UnitLifecycleDecryptRatchetT3.lean`,
# `UnitLifecycleDecryptRatchetScreen.lean`), and the three Session contract fields stated at the
# unit's instances (`UnitSatisfiabilityZeroizeScope.lean`): each statement pin and each definition
# pin, deleted in turn, is refused as a missing statement pin. One line per module: file, namespace,
# then the names.
while IFS=' ' read -r file ns names; do
  for n in $names; do
    make_case
    python3 - "$work/tacenta-proofs/translation/Translation/$file.lean" "$ns.$n" <<'PY'
import pathlib, re, sys
path = pathlib.Path(sys.argv[1])
text = path.read_text()
name = sys.argv[2]
block = re.compile(
    r"/--\s*info: (?:(?!-/).)*?-/\s*\n#guard_msgs in\s*\n#(?:print |check @)" + re.escape(name) + r"\n",
    re.S,
)
new, n = block.subn("", text)
assert n == 1, n
path.write_text(new)
PY
    expect_fail "statement-pin-deleted-$file-$n" "\`$ns.$n\` is on REQUIRED_STATEMENT_PINS and has no statement pin" --check
  done
done <<'LIST'
UnitLifecycleRetryLoopT3 Tacenta.UnitLifecycleRetryLoopT3 receive_with_eviction_loop_refines receive_with_eviction_refines receiveWithEvictionLoopResult_stop shortfall_covers evict_for_retry_covers LoopRel OutcomeRefines OpenRefusal BatchCovers halfLength evictHalf
UnitLifecycleDecryptRatchetT3 Tacenta.UnitLifecycleDecryptRatchetT3 DecryptOracleOf.of_oracleOf decrypt_ratchet_refines decrypt_ratchet_refines_statement RetryRunBounds.toRetryReceiveBounds DecryptPrefix.triple_refusal DecryptPrefix.aead_refusal DecryptPrefix.success tripleRefusalOpen_exactly tripleRefusalOpen_false_unless_triple DecryptOracleOf RetryRunBounds DecryptRatchetAgreements DecryptRatchetRun TripleRefusalOpen DecryptRatchetRefinesStatement DecryptPrefix decrypt_ratchet_refines_unless_open cMax_usize
UnitLifecycleDecryptRatchetT3 Tacenta.UnitLifecycleT3 StepRefines ResultRefines SessionRefines
UnitLifecycleDecryptRatchetT3 Tacenta.SessionUnitSpqrT3 VecRetainAgrees RemoveSkippedAtAgrees
UnitLifecycleDecryptRatchetScreen Tacenta.UnitLifecycleDecryptRatchetScreen sample_run_satisfiable decrypt_boundary_has_a_model decrypt_shapes_are_predicates run_draw_not_trivial retryRunBounds_not_trivial tripleRefusalOpen_false_of_ok tripleRefusalOpen_false_of_store_full decrypt_ratchet_refines_at_sample sample_model_refuses succ_model_accepts succ_run_satisfiable hypotheses_meet_refusal_and_success sampleComposite sampleReal modelOf sampleRng DhCodecOfShape DecryptOracleShape ZeroizeRoundTripShapes succTriple succReal succComposite succBytes oracleDecrypt evict_decode_model evict_headroom evict_run_satisfiable evict_first_attempt_full hypotheses_meet_eviction_round decrypt_ratchet_refines_at_eviction decrypt_ratchet_refines_from_shapes evictEntry evictSparseEntry evictTriple evictReal evictComposite evictBytes evictMessage evict_reaches_receive receiveWithEviction_first_round evict_loop_first_round decrypt_ratchet_refines_from_shapes_at_eviction
UnitSatisfiabilityZeroizeScope Tacenta.SessionUnitSpqrT1 ZeroizeTotal VecRetainTotal
UnitSatisfiabilityZeroizeScope Tacenta.SessionUnitBraidT1 ArrayZeroizeTotal
LIST

# Package F's open disjunct is on REQUIRED_PRINT_FORM: its pin rewritten as `#check @` is refused.
make_case
replace_in "tacenta-proofs/translation/Translation/UnitLifecycleDecryptRatchetT3.lean" $'#guard_msgs in\n#print Tacenta.UnitLifecycleDecryptRatchetT3.TripleRefusalOpen\n' $'#guard_msgs in\n#check @Tacenta.UnitLifecycleDecryptRatchetT3.TripleRefusalOpen\n'
expect_fail "definition-pin-check-form-TripleRefusalOpen" "is \`#check @Tacenta.UnitLifecycleDecryptRatchetT3.TripleRefusalOpen\`, which prints the type and not the body" --check
make_case
replace_in "tacenta-proofs/translation/Translation/UnitLifecycleDecryptRatchetT3.lean" $'#guard_msgs in\n#print Tacenta.UnitLifecycleT3.StepRefines\n' $'#guard_msgs in\n#check @Tacenta.UnitLifecycleT3.StepRefines\n'
expect_fail "definition-pin-check-form-StepRefines" "is \`#check @Tacenta.UnitLifecycleT3.StepRefines\`, which prints the type and not the body" --check

# Package F, the refusal closure (`UnitLifecycleTripleRefusalT3.lean`,
# `UnitLifecycleDecryptRatchetCompleteT3.lean`, `UnitLifecycleDecryptRatchetCompleteScreen.lean`, and the
# split form in `UnitLifecycleDecryptRatchetT3.lean`), and the public `decrypt` on frames that are not
# initial messages (`UnitLifecycleDecryptT3.lean`): each statement pin and each definition pin,
# deleted in turn, is refused as a missing statement pin.
while IFS=' ' read -r file ns names; do
  for n in $names; do
    make_case
    python3 - "$work/tacenta-proofs/translation/Translation/$file.lean" "$ns.$n" <<'PY'
import pathlib, re, sys
path = pathlib.Path(sys.argv[1])
text = path.read_text()
name = sys.argv[2]
block = re.compile(
    r"/--\s*info: (?:(?!-/).)*?-/\s*\n#guard_msgs in\s*\n#(?:print |check @)" + re.escape(name) + r"\n",
    re.S,
)
new, n = block.subn("", text)
assert n == 1, n
path.write_text(new)
PY
    expect_fail "statement-pin-deleted-$file-$n" "\`$ns.$n\` is on REQUIRED_STATEMENT_PINS and has no statement pin" --check
  done
done <<'LIST'
UnitLifecycleTripleRefusalT3 Tacenta.UnitLifecycleTripleRefusalT3 derive_chain_loop_ok derive_chain_refines_far ratchet_skip_refusal_refines ratchet_receive_tail_refusal_refines ratchet_receive_refusal_refines spqr_skip_refusal_refines spqr_receive_continuation_refusal_refines spqr_receive_refusal_refines triple_receive_refusal_refines TripleReceiveRefusalRefines
UnitLifecycleDecryptRatchetCompleteT3 Tacenta.UnitLifecycleDecryptRatchetCompleteT3 concrete_receive_attempt_refusal_from_retry_bounds openRefusal_closes receive_with_eviction_refines_complete decrypt_ratchet_refines_complete decrypt_ratchet_refines_complete_statement decrypt_ratchet_refines_complete_implies_refines DecryptRatchetRefinesCompleteStatement
UnitLifecycleDecryptRatchetCompleteScreen Tacenta.UnitLifecycleDecryptRatchetCompleteScreen ref_model_triple_refuses ref_premises ref_triple_refuses ref_headroom ref_run_satisfiable ref_model_refuses hypotheses_meet_open_path decrypt_ratchet_refines_complete_at_refusal generated_reaches_open_path refTriple refHeader refModelHeader refModel refReal
UnitLifecycleDecryptRatchetT3 Tacenta.UnitLifecycleDecryptRatchetT3 decrypt_ratchet_refines_or_open or_unless_closed OpenRefusalCloses
UnitLifecycleEstablishInitiatorShape Tacenta.UnitLifecycleEstablishInitiatorShape singleton_length_le initChains initiatorTriple init_sender_ok braid_initiator_ok verify_bundle_ok InitiatorOutputParts InitiatorOutputParts.session establish_initiator_for_parts DhPublicValidShape DhPublicValid dhPublicValid_is model_dhPublicValid KemCiphertextLenLawShape KemCiphertextLenOf kemCiphertextLenOf_is model_kemCiphertextLen dhPublicValid_canonical dhPublicValid_valid identity_public_valid canonical_of_is_canonical_key initiatorTriple_invariant structural_parts parts_invariant establish_initiator_for_admissible counterHeadroom_parts counterHeadroom_of_established unsampledModelOf establishedModelOf sessionRefines_parts sessionRefines_established sessionRefines_parts_unique sessionRefines_established_unique InitiatorSuccessShape model_initiatorSuccess successBundle verify_successBundle shared_secret_successBundle establish_initiator_for_succeeds established_initiator_inhabited establishment_hypotheses_satisfiable
UnitLifecycleEstablishedDecrypt Tacenta.UnitLifecycleEstablishedDecrypt honestChunk_established established_initiator_decrypt_ratchet_hypotheses established_initiator_decrypt_ratchet_refines established_initiator_decrypt_refines EstablishedDecryptHypotheses.refines sampleMessage_real_type sampleMessage_chunk established_decrypt_hypotheses_jointly_satisfiable oneKey_length oneKey_canonical oneKey_ne_zero established_decrypt_laws_model EstablishedDecryptHypotheses Interp.modelEstablished viewEstablished oneKey
UnitLifecycleEstablishResponder Tacenta.UnitLifecycleEstablishResponder signed_prekey_err kem_slot_err curve_inputs_err one_time_key_err decapsulate_err contributory_break_err shared_secret_err replay_err commit_kem_step commit_one_time_step init_receiver_ok braid_responder_ok hdr_decoder_ok vecU8_clone_eq curve_inputs_ok ResponderPreparedParts.ratchetPrivate_eq ResponderPreparedParts.braidSecret_eq ResponderPreparedParts.ephemeralCopy_eq fresh_decoder_invariant hdr_decoder_checks responderTriple_invariant responder_structural responder_prepared_invariant counterHeadroom_responder_prepared sessionRefines_responder_prepared honestChunk_responder_iff decryptRatchet_oracle take_one_time_kem_loop_frame take_one_time_kem_frame take_one_time_loop_frame take_one_time_frame vec_push_ok responderCommit_effects replay_ok establish_responder_cases random32_draws responder_prepared_decrypt_refines establish_responder_refines readBe32_be32 takeSplit_append decodeInitial_encodeInitial wireKey_length wireKey_curve wireKey_key ephKey_length ephKey_curve ephKey_key successBytes_length successBytes_le decode_successMessage replay_fresh map_u8_inj u32_of_ofNat basePoint_length arrayOf_basePoint basePoint_canonical successMessage_decoded decode_ec_wireKey responder_shared_secret_ok responder_prepared_inhabited establish_responder_returns establish_responder_short_message_refused establish_responder_at_parts establish_responder_unknown_prekey_refused establish_responder_legacy_refused array_eq_decide replay_loop_absent seen_for_loop_all array_eq_self decode_ec_zeroWire establish_responder_noncontributory_refused ResponderRouteHypotheses.refines sampleMessage_le responder_route_hypotheses_jointly_satisfiable establish_responder_replay_refused full_record_length_le otherThan_ne establish_responder_record_full_refused responder_route_inner_refusal_reachable responder_route_laws_model z32 fullSlice ResponderPreparedParts ResponderPreparedParts.session ResponderPreparedParts.message ResponderCommit PrepareRefusal responderChains responderTriple responderModelOf basePointBytes wireKey zeroWire ephKey successBytes successMessage basePoint ResponderSuccessShape ZeroKeyShape successStore ResponderRouteHypotheses otherThan
UnitLifecycleDecryptT3 Tacenta.UnitLifecycleDecryptT3 decrypt_refines_ratchet_frame decrypt_refines_ratchet_frame_statement decrypt_refines_ratchet_frame_of_invariant decrypt_refines_ratchet_frame_of_counter_headroom decrypt_frame_hypotheses_jointly_satisfiable decrypt_refines_ratchet_frame_of_hypotheses decrypt_frame_at_invReal succMessage_not_initial sampleMessage_not_initial decrypt_refines_ratchet_frame_at_refusal refReal_fails_invariant inv_sessionRefines inv_retryRunBounds inv_run_satisfiable inv_model_refuses decrypt_refines_ratchet_frame_of_invariant_at_sample decrypt_refines_ratchet_frame_of_invariant_exists pendReal_fails_invariant decrypt_refines_ratchet_frame_at_pending_success pend_model_clears generated_clears_at_pending_success DecryptRefinesRatchetFrameStatement invReal pendReal
UnitLifecycleSessionCodec Tacenta.UnitLifecycleSessionCodec efs_val be32_length be64_length fromBEBytes_toNat_congr fromLEBytes_toNat_congr fromBEBytes_toBEBytes_toNat from_be32 drop_next slice_of_drop length_of_drop getElem_of_drop from_slice_eq index_usize_of read_key_of read_u32_of read_optional_key_loop_zero read_optional_key_of usize_add_eq usize_div_eq slice_len_eq arr32_len optKeyEnc_length ratchetEnc_length push_optional_key_enc ratchet_to_bytes_loop_empty ratchet_to_bytes_loop_empty_spec label_to_byte_spec zeroizing_new_spec ratchet_to_bytes_spec ratchet_from_bytes_of chain_len_eq chains_len_eq skipped_len_eq fixed_prefix_eq chainEnc_length spqrEnc_length push_optional_chain_some spqr_to_bytes_loop0_one spqr_to_bytes_loop1_empty direction_to_byte_spec spqr_encoded_len_eq spqr_to_bytes_spec from_be64 u64_eq_of_bv u32_eq_of_bv decode_chain_of decode_chains_entry_of spqr_from_bytes_loop0_one spqr_from_bytes_loop1_empty direction_from_byte_dirByte spqr_from_bytes_of tripleEnc_length triple_to_bytes_spec triple_take_len_prefixed_of triple_invariant_parts triple_from_bytes_of authEnc_length setSlice_app auth_to_bytes_spec auth_from_bytes_of head_len_eq epoch_and_auth_len_eq braidEnc_length braid_to_bytes_spec read_u64_of read_epoch_of read_auth_of decode_state_unsampled_of braid_from_bytes_of lifecycle_take_len_prefixed_of vecAsSliceImpl_shape dhPublicBytesRoundTrip_is model_dhPublicBytesRoundTrip dhPrivateBytesRoundTrip_is model_dhPrivateBytesRoundTrip zeroizingVecRoundTrip_is model_zeroizingVecRoundTrip cast_len_val lenEnc_length lifecycle_push_len_prefixed_spec pendEnc_length pending_to_bytes_spec pending_from_bytes_of be32 be64 optKeyEnc ratchetEnc ZeroizingVecRoundTrip vecInst dirByte chainEnc spqrEnc tripleEnc authEnc braidEnc OptionBranchSomeShape OptionBranchSome optionBranchImpl VecAsSliceShape VecAsSlice vecAsSliceImpl DhPublicBytesRoundTripShape DhPublicBytesRoundTrip arrInst DhPrivateBytesRoundTripShape DhPrivateBytesRoundTrip ZeroizingVecRoundTripShape lenEnc pendEnc
UnitLifecycleSessionRoundTrip Tacenta.UnitLifecycleSessionRoundTrip export_spec import_unchecked_spec slice_ne_self session_invariant_leaves export_import_of_shape identity_ad_length_of CodecShape sessionEnc
UnitLifecycleRestoredSession Tacenta.UnitLifecycleRestoredSession import_ok_gives_invariant counterHeadroom_iff_check sessionRefines_restored sessionRefines_restored_unique honestChunk_restored RestoredDecryptHypotheses.ofInvariant RestoredDecryptHypotheses.refines restored_decrypt_refines model_kemCiphertextLenBound codecShape_parts export_import_established restored_established_continues restored_established_initiator_decrypt_refines restored_established_inhabited restored_laws_model restored_laws_model_established restored_decrypt_hypotheses_jointly_satisfiable restored_decrypt_laws_model headroomCheck RestoredScope restoredModelOf RestoredDecryptHypotheses KemCiphertextLenBoundShape KemCiphertextLenBound
UnitLifecycleEstablishedEncrypt Tacenta.UnitLifecycleEstablishedEncrypt keyGenAnswers_is keyGenSeededFor_is keyGenSizes_wrapperKemOf keyGenSizes_wrapperKem step_send_keysUnsampled_pinned braid_send_keysUnsampled_pinned send_keysUnsampled_output sendAgreement_keysUnsampled_output two_of_length braidSendTraceCounted_of_keysUnsampled braidSendTraceCounted_established identityAd_length_parts kemCiphertext_length_parts encryptHeadroom_parts encryptHeadroom_established tripleStoreFacts_parts sparseOutput_none_of_evidence encryptProviders_established established_initiator_encrypt_refines established_triple_send_ok established_encrypt_model_cases state_failed_of_refines state_keysSampled_of_refines established_encrypt_outcomes established_triple_next_counters established_encrypt_successor_counterHeadroom established_encrypt_successor_refines EstablishedEncryptHypotheses.refines zeroizingKeys_is nil_length_le byteTrace_two established_encrypt_hypotheses_jointly_satisfiable two_draws_of_64 established_encrypt_outcomes_at_witness established_encrypt_success_reachable established_encrypt_refusal_reachable genFill_answers modelEncrypt_keyGenSeeded modelEncrypt_kemAgrees modelEncrypt_keyPairGenerate modelEncrypt_kemEncapsulate byteRng_rngTotal modelEncrypt_allT1 leValue_replicate_zero toyKemR_seeds toyKemR_sizes established_encrypt_laws_model encrypt_ok_parts array_eq_of_bytes triple_eq_sent sentTriple_invariant structural_sent keysSampled_invariant sent_invariant keyPairValid_of_header encoder_of_refines established_encrypt_successor_admissible established_encrypt_successor_hypotheses authOf_injective established_encrypt_successor_shape EstablishedEncryptSuccessorHypotheses.successor established_encrypt_successor_hypotheses_jointly_satisfiable established_encrypt_successor_reachable KeyGenAnswersShape KeyGenAnswers KeyGenSeededForShape KeyGenSeededFor KeyGenSizesOf firstComposite firstFrame initialWire EstablishedEncryptHypotheses ZeroizingKeysShape EncryptExtraLawsShape EncryptExtraLaws emptyPlaintext toyKemR genFill encapResult encapFill Interp.modelEncrypt InterpO.modelEncrypt viewEncrypt dhViewEncrypt kemViewEncrypt zeroSeed oneSeed sentChains sentTriple sentSession EstablishedEncryptSuccessorHypotheses
UnitLifecycleResponderFirstFrame Tacenta.UnitLifecycleResponderFirstFrame bundle_with_own establish_initiator_for_secret dhAgreeSymmetric_is shared_secret_symmetric vec_index_last publish_parts one_time_kem_ids_spec u32_index_first peek_one_time_first canonicalKey_arrayOf view_of_public identity_public_of_dh_key ciphertext_le decode_first_frame decode_ec_public curve_inputs_of contains_u32 signed_prekey_own kem_slot_last_resort kem_slot_one_time decapsulate_current decapsulate_one_time one_time_key_absent one_time_key_last nodup_append_disjoint distinct_kem_last distinct_pool_last heldKemPair_last replay_loop_flag replay_refusal_cause establish_responder_slot_refused establish_responder_replay_refused_at parts_of_steps responder_first_frame_prepares responder_first_frame_admissible first_send_responder_prepares basePoint_ne_zero modelFirstFrame_dhCodec modelFirstFrame_dhAgree modelFirstFrame_symmetric first_frame_laws_model publish_reachStore reachStore_distinct random_secret_byte reach_establishment first_send_responder_reachable InitiatorSecretParts DhAgreeSymmetricShape DhAgreeSymmetric OneTimeMatches zPool PoolEntry KemEntry storeIds PrekeyIdsDistinct heldKemPair FirstKemAgrees StoreRefusal FirstFrameSuccessShape Interp.modelFirstFrame InterpO.modelFirstFrame viewFirstFrame dhViewFirstFrame kemViewFirstFrame reachStore reachBundle
UnitLifecycleResponderFirstReceipt Tacenta.UnitLifecycleResponderFirstReceipt first_send_key first_receive_key first_receive_with_eviction readBe64_be64_kernel readBe16_be16_kernel decode_encodeMessage first_frame_model_outcomes aeadRoundTrip_is dhAgreeContributory_is first_init_pair established_triple_first responder_triple_first first_kdf_model zeroized_eq parts_of_first_frame view_ratchet_public responder_first_agreement responder_candidate_agreement first_identityAd_eq arrayOf_arrayOfBytes aead_open_sealed attributedView_send firstFrame_attributedView first_receipt_run_inputs firstAd_length_le responder_first_frame_inner_outcomes responder_first_frame_inner_succeeds establish_responder_commit_of_inner establish_responder_refused_of_inner responder_first_frame_outcomes responder_first_frame_succeeds initiator_first_send_responder_receives initiator_first_send_responder_outcomes modelFirstReceipt_dhCodec modelFirstReceipt_dhAgree modelFirstReceipt_symmetric modelFirstReceipt_aeadOpen modelFirstReceipt_aeadSeal modelFirstReceipt_aeadRoundTrip modelFirstReceipt_contributory first_receipt_laws_model first_send_receive_reachable firstSenderTriple firstReceiverTriple firstHeader firstKey senderAfterFirst receiverAfterFirst firstAd firstOpen firstReceiptSession AeadRoundTripShape AeadRoundTrip DhAgreeContributoryShape DhAgreeContributory arrayOfBytes attributedView headerSource Interp.modelFirstReceipt InterpO.modelFirstReceipt viewFirstReceipt dhViewFirstReceipt kemViewFirstReceipt
UnitLifecycleResponderSuccessor Tacenta.UnitLifecycleResponderSuccessor decrypt_ratchet_ok_parts braid_receive_noHeader one_chunk_loop decoder_invariant_small add_chunk_fresh_have received_decoder_checks triple_eq_received receivedTriple_invariant structural_received received_invariant first_receipt_successor_shape received_counterHeadroom first_receipt_successor_facts responder_first_frame_successor initiator_first_send_responder_successor_hypotheses initiator_first_send_responder_successor_admissible initiator_first_send_responder_successor_counterHeadroom first_send_receive_successor_reachable receivedChains receivedTriple receivedSession
UnitLifecycleResponderReply Tacenta.UnitLifecycleResponderReply array_clone_u8 auth_clone_eq braid_send_noHeader sendAgreement_noHeader_output braidSendTraceCounted_of_noHeader reply_send_key replyFrame_with_draws reply_model_step sparseOutput_none_of_noHeader encryptProviders_reply encryptHeadroom_reply oracleOf_with_draws noHeader_of_receipt_refines pendingInitial_none_of_receipt_refines responder_reply_refines responder_first_frame_successor_keys initiator_first_send_responder_successor_keys initiator_first_send_responder_replies first_send_reply_reachable replierAfterSend replyKey replyComposite replyFrame
UnitLifecycleResponderReplyReceipt Tacenta.UnitLifecycleResponderReplyReceipt reply_receive_key reply_receive_stale replyFrame_messageType replyFrame_decodeDetailed reply_receipt_model_outcomes fresh_public_of_draw initiator_reply_agreement initiator_candidate_agreement first_send_model_session replyAd_length_le initiator_receives_reply_outcomes initiator_receives_reply_two_outcomes initiator_receives_reply replyPub_canonical replyPub_ne_zero replyPub_basePoint replyPub_oneKey replyPub_zeros dhPublicNotConstant_is modelReply_dhCodec modelReply_dhAgree modelReply_symmetric modelReply_contributory modelFirstReceipt_not_notConstant modelReply_notConstant reply_receipt_laws_model byteTrace_one byteTrace_seed_extra two_draws_of_seed_extra reply_receipt_reach_run first_send_reply_receipt_reachable first_send_reply_stale_reachable initiatorAfterReply replyAd replyReceiptSession replyPub Interp.modelReply InterpO.modelReply viewReply dhViewReply kemViewReply DhPublicNotConstantShape DhPublicNotConstant
UnitTripleInvModel Tacenta.UnitTripleInvModel keyOf_injective keyOf_inj_iff canonicalKey_keyOf u32_max_eq_model u64_max_eq_model ratchet_inv_iff_model window_end_val spqr_inv_iff_model triple_invariant_true_iff rolesAgree_iff_model triple_invariant_iff_model ModelRatchetInv ModelSpqrInv ModelRolesAgree ModelTripleInv RolesAgree
UnitLifecycleSendPreserve Tacenta.UnitLifecycleSendPreserve ratchet_send_frame modelRatchetInv_send findChains_mem spqr_send_frame mem_sent_chains modelSpqrInv_send modelTripleInv_send braid_send_no_draw_model encrypt_session_cases counterRoom_zero epoch_val_refines counterRoom_iff_model modelCounterRoom_encrypt sendsWithoutDraw_of_refines vec_clone_u8 encoder_clone_eq decoder_clone_eq next_chunk_keeps encoder_sized_congr key_pair_valid_clone braid_send_no_draw session_invariant_iff structural_congr encrypt_ok_not_failed encrypt_keeps_invariant_no_draw modelCounterRoom_firstReceipt initiator_first_send_responder_reply_successor initiator_first_send_responder_reply_admissible established_encrypt_triple_invariant_via_preservation CounterRoom ModelCounterRoom SendsWithoutDraw
UnitLifecycleInitiatorSecondSend Tacenta.UnitLifecycleInitiatorSecondSend send_output_none_of_no_draw sparseOutput_none_of_no_draw encryptProviders_of_invariant braid_send_keysSampled braidSendTraceCounted_of_keysSampled second_send_key secondFrame_with_draws second_model_step initiator_second_send_refines first_send_model_session_encoder initiator_second_send_after_reply initiatorAfterSecond secondHeader secondKey secondComposite secondFrame
LIST

# The closure's statement definitions, and the statement and state definitions of `UnitLifecycleDecryptT3.lean`,
# are on REQUIRED_PRINT_FORM: a pin rewritten as `#check @` is refused.
make_case
replace_in "tacenta-proofs/translation/Translation/UnitLifecycleTripleRefusalT3.lean" $'#guard_msgs in\n#print Tacenta.UnitLifecycleTripleRefusalT3.TripleReceiveRefusalRefines\n' $'#guard_msgs in\n#check @Tacenta.UnitLifecycleTripleRefusalT3.TripleReceiveRefusalRefines\n'
expect_fail "definition-pin-check-form-TripleReceiveRefusalRefines" "is \`#check @Tacenta.UnitLifecycleTripleRefusalT3.TripleReceiveRefusalRefines\`, which prints the type and not the body" --check
make_case
replace_in "tacenta-proofs/translation/Translation/UnitLifecycleDecryptRatchetT3.lean" $'#guard_msgs in\n#print Tacenta.UnitLifecycleDecryptRatchetT3.OpenRefusalCloses\n' $'#guard_msgs in\n#check @Tacenta.UnitLifecycleDecryptRatchetT3.OpenRefusalCloses\n'
expect_fail "definition-pin-check-form-OpenRefusalCloses" "is \`#check @Tacenta.UnitLifecycleDecryptRatchetT3.OpenRefusalCloses\`, which prints the type and not the body" --check
make_case
replace_in "tacenta-proofs/translation/Translation/UnitLifecycleDecryptT3.lean" $'#guard_msgs in\n#print Tacenta.UnitLifecycleDecryptT3.DecryptRefinesRatchetFrameStatement\n' $'#guard_msgs in\n#check @Tacenta.UnitLifecycleDecryptT3.DecryptRefinesRatchetFrameStatement\n'
expect_fail "definition-pin-check-form-DecryptRefinesRatchetFrameStatement" "is \`#check @Tacenta.UnitLifecycleDecryptT3.DecryptRefinesRatchetFrameStatement\`, which prints the type and not the body" --check
make_case
replace_in "tacenta-proofs/translation/Translation/UnitLifecycleDecryptT3.lean" $'#guard_msgs in\n#print Tacenta.UnitLifecycleDecryptT3.invReal\n' $'#guard_msgs in\n#check @Tacenta.UnitLifecycleDecryptT3.invReal\n'
expect_fail "definition-pin-check-form-invReal" "is \`#check @Tacenta.UnitLifecycleDecryptT3.invReal\`, which prints the type and not the body" --check
make_case
replace_in "tacenta-proofs/translation/Translation/UnitLifecycleDecryptT3.lean" $'#guard_msgs in\n#print Tacenta.UnitLifecycleDecryptT3.pendReal\n' $'#guard_msgs in\n#check @Tacenta.UnitLifecycleDecryptT3.pendReal\n'
expect_fail "definition-pin-check-form-pendReal" "is \`#check @Tacenta.UnitLifecycleDecryptT3.pendReal\`, which prints the type and not the body" --check

# The established initiator's law is on REQUIRED_PRINT_FORM: its pin rewritten as `#check @` is refused.
make_case
replace_in "tacenta-proofs/translation/Translation/UnitLifecycleEstablishInitiatorShape.lean" $'#guard_msgs in\n#print Tacenta.UnitLifecycleEstablishInitiatorShape.DhPublicValidShape\n' $'#guard_msgs in\n#check @Tacenta.UnitLifecycleEstablishInitiatorShape.DhPublicValidShape\n'
expect_fail "definition-pin-check-form-DhPublicValidShape" "is \`#check @Tacenta.UnitLifecycleEstablishInitiatorShape.DhPublicValidShape\`, which prints the type and not the body" --check

# The restored session's ciphertext bound law is on REQUIRED_PRINT_FORM: its pin rewritten as `#check @` is refused.
make_case
replace_in "tacenta-proofs/translation/Translation/UnitLifecycleRestoredSession.lean" $'#guard_msgs in\n#print Tacenta.UnitLifecycleRestoredSession.KemCiphertextLenBoundShape\n' $'#guard_msgs in\n#check @Tacenta.UnitLifecycleRestoredSession.KemCiphertextLenBoundShape\n'
expect_fail "definition-pin-check-form-KemCiphertextLenBoundShape" "is \`#check @Tacenta.UnitLifecycleRestoredSession.KemCiphertextLenBoundShape\`, which prints the type and not the body" --check
# The responder route's commit is on REQUIRED_PRINT_FORM: its pin rewritten as `#check @` is refused.
make_case
replace_in "tacenta-proofs/translation/Translation/UnitLifecycleEstablishResponder.lean" $'#guard_msgs in\n#print Tacenta.UnitLifecycleEstablishResponder.ResponderCommit\n' $'#guard_msgs in\n#check @Tacenta.UnitLifecycleEstablishResponder.ResponderCommit\n'
expect_fail "definition-pin-check-form-ResponderCommit" "is \`#check @Tacenta.UnitLifecycleEstablishResponder.ResponderCommit\`, which prints the type and not the body" --check

# The established encrypt's key-generation law is on REQUIRED_PRINT_FORM: its pin rewritten as `#check @` is refused.
make_case
replace_in "tacenta-proofs/translation/Translation/UnitLifecycleEstablishedEncrypt.lean" $'#guard_msgs in\n#print Tacenta.UnitLifecycleEstablishedEncrypt.KeyGenSeededForShape\n' $'#guard_msgs in\n#check @Tacenta.UnitLifecycleEstablishedEncrypt.KeyGenSeededForShape\n'
expect_fail "definition-pin-check-form-KeyGenSeededForShape" "is \`#check @Tacenta.UnitLifecycleEstablishedEncrypt.KeyGenSeededForShape\`, which prints the type and not the body" --check

# The first-frame route's per-run KEM premise is on REQUIRED_PRINT_FORM: its pin rewritten as `#check @` is refused.
make_case
replace_in "tacenta-proofs/translation/Translation/UnitLifecycleResponderFirstFrame.lean" $'#guard_msgs in\n#print Tacenta.UnitLifecycleResponderFirstFrame.FirstKemAgrees\n' $'#guard_msgs in\n#check @Tacenta.UnitLifecycleResponderFirstFrame.FirstKemAgrees\n'
expect_fail "definition-pin-check-form-FirstKemAgrees" "is \`#check @Tacenta.UnitLifecycleResponderFirstFrame.FirstKemAgrees\`, which prints the type and not the body" --check

# The first-receipt route's AEAD law is on REQUIRED_PRINT_FORM: its pin rewritten as `#check @` is refused.
make_case
replace_in "tacenta-proofs/translation/Translation/UnitLifecycleResponderFirstReceipt.lean" $'#guard_msgs in\n#print Tacenta.UnitLifecycleResponderFirstReceipt.AeadRoundTripShape\n' $'#guard_msgs in\n#check @Tacenta.UnitLifecycleResponderFirstReceipt.AeadRoundTripShape\n'
expect_fail "definition-pin-check-form-AeadRoundTripShape" "is \`#check @Tacenta.UnitLifecycleResponderFirstReceipt.AeadRoundTripShape\`, which prints the type and not the body" --check

# The responder successor's session definition is on REQUIRED_PRINT_FORM: its pin rewritten as `#check @` is refused.
make_case
replace_in "tacenta-proofs/translation/Translation/UnitLifecycleResponderSuccessor.lean" $'#guard_msgs in\n#print Tacenta.UnitLifecycleResponderSuccessor.receivedSession\n' $'#guard_msgs in\n#check @Tacenta.UnitLifecycleResponderSuccessor.receivedSession\n'
expect_fail "definition-pin-check-form-receivedSession" "is \`#check @Tacenta.UnitLifecycleResponderSuccessor.receivedSession\`, which prints the type and not the body" --check

# The responder reply's frame definition is on REQUIRED_PRINT_FORM: its pin rewritten as `#check @` is refused.
make_case
replace_in "tacenta-proofs/translation/Translation/UnitLifecycleResponderReply.lean" $'#guard_msgs in\n#print Tacenta.UnitLifecycleResponderReply.replyFrame\n' $'#guard_msgs in\n#check @Tacenta.UnitLifecycleResponderReply.replyFrame\n'
expect_fail "definition-pin-check-form-replyFrame" "is \`#check @Tacenta.UnitLifecycleResponderReply.replyFrame\`, which prints the type and not the body" --check

# The reply receipt's model session definition is on REQUIRED_PRINT_FORM: its pin rewritten as `#check @` is refused.
make_case
replace_in "tacenta-proofs/translation/Translation/UnitLifecycleResponderReplyReceipt.lean" $'#guard_msgs in\n#print Tacenta.UnitLifecycleResponderReplyReceipt.replyReceiptSession\n' $'#guard_msgs in\n#check @Tacenta.UnitLifecycleResponderReplyReceipt.replyReceiptSession\n'
expect_fail "definition-pin-check-form-replyReceiptSession" "is \`#check @Tacenta.UnitLifecycleResponderReplyReceipt.replyReceiptSession\`, which prints the type and not the body" --check

# The definitions of the bridge between `Triple::invariant` and the model, and of send preservation, are on
# REQUIRED_PRINT_FORM: each pin rewritten as `#check @` is refused.
make_case
replace_in "tacenta-proofs/translation/Translation/UnitTripleInvModel.lean" $'#guard_msgs in\n#print Tacenta.UnitTripleInvModel.ModelRatchetInv\n' $'#guard_msgs in\n#check @Tacenta.UnitTripleInvModel.ModelRatchetInv\n'
expect_fail "definition-pin-check-form-ModelRatchetInv" "is \`#check @Tacenta.UnitTripleInvModel.ModelRatchetInv\`, which prints the type and not the body" --check
make_case
replace_in "tacenta-proofs/translation/Translation/UnitTripleInvModel.lean" $'#guard_msgs in\n#print Tacenta.UnitTripleInvModel.ModelSpqrInv\n' $'#guard_msgs in\n#check @Tacenta.UnitTripleInvModel.ModelSpqrInv\n'
expect_fail "definition-pin-check-form-ModelSpqrInv" "is \`#check @Tacenta.UnitTripleInvModel.ModelSpqrInv\`, which prints the type and not the body" --check
make_case
replace_in "tacenta-proofs/translation/Translation/UnitTripleInvModel.lean" $'#guard_msgs in\n#print Tacenta.UnitTripleInvModel.ModelRolesAgree\n' $'#guard_msgs in\n#check @Tacenta.UnitTripleInvModel.ModelRolesAgree\n'
expect_fail "definition-pin-check-form-ModelRolesAgree" "is \`#check @Tacenta.UnitTripleInvModel.ModelRolesAgree\`, which prints the type and not the body" --check
make_case
replace_in "tacenta-proofs/translation/Translation/UnitTripleInvModel.lean" $'#guard_msgs in\n#print Tacenta.UnitTripleInvModel.ModelTripleInv\n' $'#guard_msgs in\n#check @Tacenta.UnitTripleInvModel.ModelTripleInv\n'
expect_fail "definition-pin-check-form-ModelTripleInv" "is \`#check @Tacenta.UnitTripleInvModel.ModelTripleInv\`, which prints the type and not the body" --check
make_case
replace_in "tacenta-proofs/translation/Translation/UnitTripleInvModel.lean" $'#guard_msgs in\n#print Tacenta.UnitTripleInvModel.RolesAgree\n' $'#guard_msgs in\n#check @Tacenta.UnitTripleInvModel.RolesAgree\n'
expect_fail "definition-pin-check-form-RolesAgree" "is \`#check @Tacenta.UnitTripleInvModel.RolesAgree\`, which prints the type and not the body" --check
make_case
replace_in "tacenta-proofs/translation/Translation/UnitLifecycleSendPreserve.lean" $'#guard_msgs in\n#print Tacenta.UnitLifecycleSendPreserve.CounterRoom\n' $'#guard_msgs in\n#check @Tacenta.UnitLifecycleSendPreserve.CounterRoom\n'
expect_fail "definition-pin-check-form-CounterRoom" "is \`#check @Tacenta.UnitLifecycleSendPreserve.CounterRoom\`, which prints the type and not the body" --check
make_case
replace_in "tacenta-proofs/translation/Translation/UnitLifecycleSendPreserve.lean" $'#guard_msgs in\n#print Tacenta.UnitLifecycleSendPreserve.ModelCounterRoom\n' $'#guard_msgs in\n#check @Tacenta.UnitLifecycleSendPreserve.ModelCounterRoom\n'
expect_fail "definition-pin-check-form-ModelCounterRoom" "is \`#check @Tacenta.UnitLifecycleSendPreserve.ModelCounterRoom\`, which prints the type and not the body" --check
make_case
replace_in "tacenta-proofs/translation/Translation/UnitLifecycleSendPreserve.lean" $'#guard_msgs in\n#print Tacenta.UnitLifecycleSendPreserve.SendsWithoutDraw\n' $'#guard_msgs in\n#check @Tacenta.UnitLifecycleSendPreserve.SendsWithoutDraw\n'
expect_fail "definition-pin-check-form-SendsWithoutDraw" "is \`#check @Tacenta.UnitLifecycleSendPreserve.SendsWithoutDraw\`, which prints the type and not the body" --check

# The initiator's second frame definition is on REQUIRED_PRINT_FORM: its pin rewritten as `#check @` is refused.
make_case
replace_in "tacenta-proofs/translation/Translation/UnitLifecycleInitiatorSecondSend.lean" $'#guard_msgs in\n#print Tacenta.UnitLifecycleInitiatorSecondSend.secondFrame\n' $'#guard_msgs in\n#check @Tacenta.UnitLifecycleInitiatorSecondSend.secondFrame\n'
expect_fail "definition-pin-check-form-secondFrame" "is \`#check @Tacenta.UnitLifecycleInitiatorSecondSend.secondFrame\`, which prints the type and not the body" --check

# A definition on REQUIRED_PRINT_FORM is held by `#print`: its pin rewritten as `#check @`, which
# prints the type and not the body, is refused, for a model definition and for a record. A floor
# name not on that list (`takeDraws`, whose body is held by its equation pin) may take either form.
screen="tacenta-proofs/translation/Translation/UnitLifecycleIntegrationScreen.lean"
for name in Model.Lifecycle.braidSendDrawCount Tacenta.UnitLifecycleT3.OracleOf; do
  make_case
  replace_in "$screen" $'#guard_msgs in\n#print '"$name"$'\n' $'#guard_msgs in\n#check @'"$name"$'\n'
  expect_fail "definition-pin-check-form-$name" "\`$name\` is on REQUIRED_STATEMENT_PINS and its pin at $screen:" --check
  expect_fail "definition-pin-check-form-$name-says-why" "is \`#check @$name\`, which prints the type and not the body" --check
  expect_fail "definition-pin-check-form-$name-refused-by-refresh" "is \`#check @$name\`, which prints the type and not the body"
done
make_case
replace_in "$screen" $'#guard_msgs in\n#print Model.Lifecycle.takeDraws\n' $'#guard_msgs in\n#check @Model.Lifecycle.takeDraws\n'
expect_pass "statement-pin-check-form-off-the-print-list"
expect_pass_after "statement-pin-check-form-off-the-print-list-then-checked" --check

# The spellings the floor accepts: the pin is the pin, not its exact form. The Lean file
# changed, so the source attestation is stale until it is regenerated; regenerating
# refuses on the same statement-pin problems `--check` does, so an accepted case is a
# regeneration that succeeds and a `--check` after it.
for option in "check info, drop warning" "whitespace := normalized" "ordering := sorted" "info"; do
  make_case
  rewrite_statement_pin options "$option"
  expect_pass "statement-pin-accepted-option-$option"
  expect_pass_after "statement-pin-accepted-option-$option-then-checked" --check
done

make_case
rewrite_statement_pin at-sign
expect_pass "statement-pin-accepted-with-at-sign"
expect_pass_after "statement-pin-accepted-with-at-sign-then-checked" --check

# A pin in a module that no audit module imports: the pin moves to a new file under the
# translation package, which nothing imports.
make_case
rewrite_statement_pin delete
cat > "$work/tacenta-proofs/translation/Translation/OrphanStatementPin.lean" <<EOF
import Translation.DispatchEvidenceVacuity

#guard_msgs in
#check @$stmt_name
EOF
expect_fail "statement-pin-in-a-module-no-audit-imports" "its statement pin is in tacenta-proofs/translation/Translation/OrphanStatementPin.lean, which no audit module imports" --check

# The floor cannot be shortened by deleting a pin and its name and regenerating: the
# verification manifest records the floor, and a floor shorter than the record is refused.
shorten_floor() {
  python3 - "$work/tacenta-proofs/scripts/attest.py" "$stmt_name" <<'PY'
import pathlib, sys
path, name = pathlib.Path(sys.argv[1]), sys.argv[2]
text = path.read_text()
start = text.index("REQUIRED_STATEMENT_PINS = frozenset(")
last = name.rsplit(".", 1)[1]
line = '        "' + last + '",\n'
at = text.index(line, start)
path.write_text(text[:at] + text[at + len(line):])
PY
}

make_case
shorten_floor
rewrite_statement_pin delete
expect_fail "statement-floor-shortened" "\`$stmt_name\` is on the statement-pin floor that verification-manifest.json records and is not on REQUIRED_STATEMENT_PINS" --check
expect_fail "statement-floor-shortened-refused-by-refresh" "is on the statement-pin floor that verification-manifest.json records and is not on REQUIRED_STATEMENT_PINS"

# The limit of the record: a floor entry is removed by editing the script, the pin and the
# manifest's own list together, a hand edit of a generated file that the diff shows. The
# case is here so that the limit is on record and not found by deleting.
make_case
shorten_floor
rewrite_statement_pin delete
edit_json tacenta-proofs/manifests/verification-manifest.json \
  "data['statement_pin_floor'].remove('$stmt_name')"
expect_pass "statement-floor-shortened-by-hand-edit-and-regenerated"
expect_pass_after "statement-floor-shortened-by-hand-edit-then-checked" --check

# The record does not fail open: with the script's floor shortened and its pin deleted, a
# manifest that is missing, unreadable, without a floor list or with an empty one leaves
# nothing to compare with, and is refused, by `--check` and by a regeneration alike.
floor_record="tacenta-proofs/manifests/verification-manifest.json"
shortened_floor_without_pin() {
  make_case
  shorten_floor
  rewrite_statement_pin delete
}
no_floor="so the statement-pin floor it records cannot be compared with REQUIRED_STATEMENT_PINS"

shortened_floor_without_pin
rm "$work/$floor_record"
expect_fail "statement-floor-record-missing" "$floor_record is missing, $no_floor" --check
expect_fail "statement-floor-record-missing-refused-by-refresh" "$floor_record is missing, $no_floor"

shortened_floor_without_pin
echo '{' > "$work/$floor_record"
expect_fail "statement-floor-record-unreadable" "$floor_record cannot be read (JSONDecodeError), $no_floor" --check
expect_fail "statement-floor-record-unreadable-refused-by-refresh" "cannot be read (JSONDecodeError), $no_floor"

shortened_floor_without_pin
edit_json "$floor_record" "del data['statement_pin_floor']"
expect_fail "statement-floor-record-keyless" "$floor_record has no \`statement_pin_floor\` list, $no_floor" --check
expect_fail "statement-floor-record-keyless-refused-by-refresh" "has no \`statement_pin_floor\` list, $no_floor"

shortened_floor_without_pin
edit_json "$floor_record" "data['statement_pin_floor'] = None"
expect_fail "statement-floor-record-null" "$floor_record has no \`statement_pin_floor\` list, $no_floor" --check

shortened_floor_without_pin
edit_json "$floor_record" "data['statement_pin_floor'] = []"
expect_fail "statement-floor-record-emptied" "$floor_record records an empty \`statement_pin_floor\`" --check
expect_fail "statement-floor-record-emptied-refused-by-refresh" "records an empty \`statement_pin_floor\`"

# The whole floor emptied in the script, and its record deleted with it, is not "0 on the floor".
make_case
replace_in tacenta-proofs/scripts/attest.py "def check_statement_pins(survey=None, reached=None):" \
  "REQUIRED_STATEMENT_PINS = frozenset()


def check_statement_pins(survey=None, reached=None):"
edit_json "$floor_record" "del data['statement_pin_floor']"
expect_fail "statement-floor-emptied" "REQUIRED_STATEMENT_PINS is empty, so no statement pin is required to exist" --check
expect_fail "statement-floor-emptied-refused-by-refresh" "REQUIRED_STATEMENT_PINS is empty"

# ---------------------------------------------------------------------------
# The translation record.
# ---------------------------------------------------------------------------

make_case
printf '\n-- P9 mutation --\n' >> "$work/$gen/TacentaRatchet.lean"
expect_fail "edited-generated-translation" "TacentaRatchet.lean differs from the recorded generation" --check-translation

make_case
python3 - "$work/$record" <<'PY'
import json, pathlib, subprocess, sys
path = pathlib.Path(sys.argv[1])
data = json.loads(path.read_text())
# A recorded file and a source hash must come from the same committed source
# tree. Select the oldest commit that contains the sparse source so this test
# remains valid when the branch is rebased or its history is pruned.
commits = subprocess.check_output(
    ["git", "rev-list", "--all", "--", "tacenta-core/spqr/src/lib.rs"],
    text=True,
).splitlines()
if len(commits) < 2:
    raise SystemExit("not enough sparse source history for the pairing control")
data["generated_at_commit"] = commits[-1]
path.write_text(json.dumps(data, indent=2) + "\n")
PY
expect_fail "mismatched-committed-source-hash" "commit the source tree before refreshing" --check-translation

make_case
python3 - "$work/$record" <<'PY'
import json, pathlib, subprocess, sys
path = pathlib.Path(sys.argv[1])
data = json.loads(path.read_text())
data["generated_at_commit"] = subprocess.check_output(
    ["git", "rev-parse", "HEAD^{tree}"], text=True
).strip()
path.write_text(json.dumps(data, indent=2) + "\n")
PY
expect_fail "generation-revision-not-commit" "is not an available commit" --check-translation

make_case
edit_json "$record" 'del data["generated_files"]["'"$gen"'/TacentaSessionUnit.lean"]["assembly"]["sources"]["tacenta-core/lifecycle"]'
expect_fail "missing-session-unit-leaf" "is recorded as assembled from" --check-translation

make_case
edit_json "$record" 'data["generated_files"]["'"$gen"'/TacentaSessionUnit.lean"]["assembly"]["script_sha256"] = "00" * 32'
expect_fail "stale-session-unit-assembler" "its assembly script" --check-translation

make_case
edit_json "$record" 'data["generated_files"]["'"$gen"'/TacentaRatchet.lean"]["axioms"].pop()'
expect_fail "record-lists-fewer-axioms" "declares a different axiom set from the recorded one" --check-translation

make_case
edit_json "$record" 'a = data["generated_files"]["'"$gen"'/TacentaRatchet.lean"]["axioms"]; a.append(a[0]); a.sort()'
expect_fail "record-lists-an-axiom-twice" "declares a different axiom set from the recorded one" --check-translation

make_case
edit_json "$record" 'data["schema_version"] = 3'
expect_fail "record-schema-is-old" "translation-attestation.json has schema_version 3" --check-translation

make_case
printf '\n// zone edit\n' >> "$work/tacenta-core/ratchet/src/lib.rs"
expect_fail "zone-source-edited" "translation is stale for tacenta-core/ratchet" --check-translation

make_case
printf '\n# workspace edit\n' >> "$work/tacenta-core/Cargo.toml"
expect_fail "workspace-input-edited" "the workspace inputs" --check-translation

make_case
printf 'namespace tacenta_nothing\nend tacenta_nothing\n' > "$work/$gen/TacentaNothing.lean"
expect_fail "generated-name-without-a-module" "is named like a generated file but scripts/run-aeneas.sh" --check-translation
expect_fail "generated-name-refused-by-refresh" "refusing to record a file the translation script does not produce" --refresh-translation

make_case
edit_json "$record" 'del data["generated_files"]["'"$gen"'/TacentaWire.lean"]'
expect_fail "record-lacks-a-file" "is a generated file with no record in translation-attestation.json" --check-translation

make_case
edit_json "$record" 'data["generated_files"]["'"$gen"'/TacentaNothing.lean"] = data["generated_files"]["'"$gen"'/TacentaWire.lean"]'
expect_fail "record-has-a-file-not-in-the-tree" "is recorded in translation-attestation.json but is not in the tree" --check-translation

# ---------------------------------------------------------------------------
# The axiom allowlist: every declaration, by qualified name and type.
# Each plant is tried through --refresh-translation, the one mode that
# would otherwise record it, and the last one checks nothing was recorded.
# ---------------------------------------------------------------------------

make_case
insert_in TacentaRatchet.lean <<'EOF'
axiom planted_false : False
EOF
expect_fail "planted-generated-axiom" "differ from the allowlist" --refresh-translation
expect_unchanged "planted-generated-axiom-wrote-nothing" "$record"

make_case
insert_in TacentaRatchet.lean <<'EOF'
namespace Other
axiom zeroize.Zeroizing.new : False
end Other
EOF
expect_fail "declaration-in-a-second-namespace" "added: tacenta_ratchet.Other.zeroize.Zeroizing.new" --refresh-translation

make_case
replace_in "$gen/TacentaErasure.lean" \
  "axiom core.num.Usize.div_ceil : Std.Usize → Std.Usize → Result Std.Usize" \
  "axiom core.num.Usize.div_ceil : False"
expect_fail "declaration-with-another-type" "tacenta_erasure.core.num.Usize.div_ceil : False" --refresh-translation

make_case
python3 - "$work/$gen/TacentaErasure.lean" <<'PY'
import pathlib, sys
path = pathlib.Path(sys.argv[1])
text = path.read_text()
line = "axiom core.num.Usize.div_ceil : Std.Usize → Std.Usize → Result Std.Usize\n"
assert text.count(line) == 1
path.write_text(text.replace(line, line + "\n" + line))
PY
expect_fail "declaration-repeated" "added: tacenta_erasure.core.num.Usize.div_ceil" --refresh-translation

make_case
replace_in "$gen/TacentaErasure.lean" \
  "axiom core.num.Usize.div_ceil : Std.Usize → Std.Usize → Result Std.Usize" \
  "-- removed"
expect_fail "declaration-removed" "removed: tacenta_erasure.core.num.Usize.div_ceil" --refresh-translation

make_case
insert_in TacentaRatchet.lean <<'EOF'
private axiom planted_false : False
EOF
expect_fail "private-declaration" "added: private tacenta_ratchet.planted_false" --refresh-translation

make_case
insert_in TacentaRatchet.lean <<'EOF'
@[simp] axiom planted_false : False
EOF
expect_fail "declaration-behind-an-attribute" "added: tacenta_ratchet.planted_false" --refresh-translation

make_case
insert_in TacentaRatchet.lean <<'EOF'
set_option maxRecDepth 100 in axiom planted_false : False
EOF
expect_fail "declaration-after-set-option" "added: tacenta_ratchet.planted_false" --refresh-translation

make_case
insert_in TacentaProtobuf.lean <<'EOF'
axiom planted_false : False
EOF
expect_fail "declaration-in-a-file-with-none" "added: tacenta_protobuf.planted_false" --refresh-translation

make_case
insert_in TacentaRatchet.lean <<'EOF'
axiom
  planted_false : False
EOF
expect_fail "declaration-name-on-the-next-line" "added: tacenta_ratchet.planted_false" --refresh-translation

make_case
insert_in TacentaRatchet.lean <<'EOF'
axiom _root_.planted_false : False
EOF
expect_fail "declaration-in-the-root-namespace" "added: planted_false" --refresh-translation

make_case
insert_in TacentaRatchet.lean <<'EOF'
axiom planted_false
  : False
  -- a comment
EOF
expect_fail "declaration-type-on-later-lines" "planted_false : False" --refresh-translation

# The allowlist file itself.

make_case
rm "$work/$allowlist"
expect_fail "allowlist-missing" "translation-axiom-allowlist.json is missing" --check-translation

make_case
printf '{ not json' > "$work/$allowlist"
expect_fail "allowlist-not-json" "translation-axiom-allowlist.json is not valid JSON" --check-translation

make_case
edit_json "$allowlist" 'data["schema_version"] = 1'
expect_fail "allowlist-schema" "has unsupported schema_version" --check-translation

make_case
edit_json "$allowlist" 'data["generated_files"] = []'
expect_fail "allowlist-without-files" "has no generated_files object" --check-translation

make_case
edit_json "$allowlist" 'data["generated_files"]["'"$gen"'/TacentaRatchet.lean"] = {"zeroize": "x"}'
expect_fail "allowlist-entry-not-a-list" "is not a list of declarations" --check-translation

make_case
edit_json "$allowlist" 'data["generated_files"]["'"$gen"'/TacentaRatchet.lean"][0]["note"] = "extra"'
expect_fail "allowlist-entry-shape" "has an allowlist entry that is not a name and a type" --check-translation

make_case
edit_json "$allowlist" 'data["generated_files"]["'"$gen"'/TacentaRatchet.lean"][0]["name"] += "ο"'
expect_fail "allowlist-name-characters" "characters outside" --check-translation

make_case
edit_json "$allowlist" 'data["generated_files"]["'"$gen"'/TacentaRatchet.lean"].reverse()'
expect_fail "allowlist-unsorted" "has unsorted declarations in the allowlist" --check-translation

make_case
edit_json "$allowlist" 'del data["generated_files"]["'"$gen"'/TacentaRatchet.lean"]'
expect_fail "allowlist-file-without-entry" "is a generated file with no entry in translation-axiom-allowlist.json" --check-translation

make_case
edit_json "$allowlist" 'data["generated_files"]["tacenta-proofs/translation/Translation/TacentaNothing.lean"] = []'
expect_fail "allowlist-entry-for-no-file" "is in translation-axiom-allowlist.json but is not a generated file" --check-translation

make_case
python3 - "$work/$allowlist" <<'PY'
import pathlib, sys
path = pathlib.Path(sys.argv[1])
text = path.read_text()
key = '"tacenta-proofs/translation/Translation/TacentaWire.lean": ['
assert text.count(key) == 1
path.write_text(text.replace(key, '"tacenta-proofs/translation/Translation/TacentaWire.lean": [],\n    ' + key))
PY
expect_fail "allowlist-repeats-a-key" "duplicate key" --check-translation

make_case
edit_json "$allowlist" 'data["generated_files"]["'"$gen"'/TacentaRatchet.lean"].pop()'
expect_fail "allowlist-lists-fewer" "removed: none" --check-translation

make_case
edit_json "$allowlist" 'e = data["generated_files"]["'"$gen"'/TacentaRatchet.lean"]; e.append(e[0]); e.sort(key=lambda x: (x["name"], x["type"]))'
expect_fail "allowlist-lists-a-declaration-twice" "removed: tacenta_ratchet" --check-translation

make_case
edit_json "$allowlist" 'data["generated_files"]["'"$gen"'/TacentaRatchet.lean"][0]["type"] += " -> False"'
expect_fail "allowlist-type-differs" "declares axioms that differ from the allowlist" --check-translation

# ---------------------------------------------------------------------------
# Scanner forms: spellings of a declaration that must be read as the plain
# one is. Numbered; each is an `axiom` the allowlist does not list.
# ---------------------------------------------------------------------------

make_case
insert_in TacentaRatchet.lean <<'EOF'
def scanner_form_01_a : Char := '"'
axiom scanner_form_01 : False
def scanner_form_01_b : Char := '"'
EOF
expect_fail "scanner-form-01" "added: tacenta_ratchet.scanner_form_01" --refresh-translation

make_case
insert_in TacentaRatchet.lean <<'EOF'
def scanner_form_02_a : String := r#"a"b"#
axiom scanner_form_02 : False
def scanner_form_02_b : String := r#"a"b"#
EOF
expect_fail "scanner-form-02" "added: tacenta_ratchet.scanner_form_02" --refresh-translation

make_case
insert_in TacentaRatchet.lean <<'EOF'
def «/-» : Nat := 1
axiom scanner_form_03 : False
def «-/» : Nat := 2
EOF
expect_fail "scanner-form-03" "added: tacenta_ratchet.scanner_form_03" --refresh-translation

make_case
insert_in TacentaRatchet.lean <<'EOF'
axiom«scanner_form_04» : False
EOF
expect_fail "scanner-form-04" "scanner_form_04" --refresh-translation

make_case
insert_in TacentaRatchet.lean <<'EOF'
def scanner_form_05 : Nat := 1
end scanner_form_05
EOF
expect_fail "scanner-form-05" "does not close the innermost scope" --refresh-translation

make_case
insert_in TacentaRatchet.lean <<'EOF'
namespace
axiom scanner_form_06 : False
EOF
expect_fail "scanner-form-06" "namespace without a name" --refresh-translation

make_case
printf '\naxiom\n' >> "$work/$gen/TacentaRatchet.lean"
expect_fail "scanner-form-07" "axiom without a name" --refresh-translation

make_case
printf '\naxiom planted_false : False\n' >> "$work/$gen/TacentaRatchet.lean"
expect_fail "declaration-after-the-namespace-closes" "added: planted_false : False" --refresh-translation

make_case
insert_in TacentaRatchet.lean <<'EOF'
section scanner_form_08
axiom scanner_form_08 : False
end scanner_form_08
EOF
expect_fail "scanner-form-08" "added: tacenta_ratchet.scanner_form_08 : False;" --refresh-translation

make_case
insert_in TacentaRatchet.lean <<'EOF'
axiom scanner_form_09_a : Nat
  axiom scanner_form_09_b : False
EOF
expect_fail "scanner-form-09" "added: tacenta_ratchet.scanner_form_09_a : Nat; tacenta_ratchet.scanner_form_09_b : False;" --refresh-translation

make_case
insert_in TacentaRatchet.lean <<'EOF'
def scanner_form_10_a : String := "a\"b"
axiom scanner_form_10 : False
def scanner_form_10_b : String := "a\"b"
EOF
expect_fail "scanner-form-10" "added: tacenta_ratchet.scanner_form_10 : False;" --refresh-translation

make_case
insert_in TacentaRatchet.lean <<'EOF'
def scanner_form_16_f'' (c : Char) : Char := c
def scanner_form_16_a := scanner_form_16_f'' '"'
axiom scanner_form_16 : False
def scanner_form_16_b := scanner_form_16_f'' '"'
EOF
expect_fail "scanner-form-16" "added: tacenta_ratchet.scanner_form_16 : False;" --refresh-translation

# Text that is not a declaration must not be read as one: the accepted side of
# the scanner. A keyword in a comment, a string, a character literal or a
# guillemet identifier, and a name that merely contains the keyword.
make_case
insert_in TacentaRatchet.lean <<'EOF'
-- axiom in_a_line_comment : False
/- axiom in_a_block_comment : False -/
/-- axiom in_a_doc_comment : False -/
def not_a_declaration_a : String := "axiom in_a_string : False"
def not_a_declaration_b : Char := 'a'
def «has an axiom inside» : Nat := 1
def axiomatic : Nat := 1
/- outer /- inner -/ axiom in_a_nested_comment : False -/
def not_a_declaration_c : Nat := 1
EOF
expect_pass "text-that-is-not-a-declaration" --refresh-translation
expect_pass_after "text-that-is-not-a-declaration-is-current" --check

# ---------------------------------------------------------------------------
# The audit comparison.
# ---------------------------------------------------------------------------

make_case
honest_audit_log "$work/audit.log"
expect_pass "audit-matches-the-record" --compare-audit "$work/audit.log"

make_case
honest_audit_log "$work/audit.log"
printf 'audit-axiom: Translation.TacentaRatchet Other.zeroize.Zeroizing.new\n' >> "$work/audit.log"
expect_fail "audit-has-an-extra-name" "in the environment but not in the recorded list: Other.zeroize.Zeroizing.new" --compare-audit "$work/audit.log"

make_case
honest_audit_log "$work/audit.log"
python3 - "$work/audit.log" <<'PY'
import pathlib, sys
path = pathlib.Path(sys.argv[1])
lines = path.read_text().splitlines()
i = next(n for n, l in enumerate(lines) if "TacentaRatchet zeroize.Zeroizing.new" in l or "TacentaRatchet tacenta_ratchet.zeroize.Zeroizing.new" in l)
lines[i] = lines[i].replace("TacentaRatchet ", "TacentaRatchet Other.")
path.write_text("\n".join(lines) + "\n")
PY
expect_fail "audit-name-only-ends-in-a-recorded-name" "in the environment but not in the recorded list: Other.tacenta_ratchet.zeroize.Zeroizing.new" --compare-audit "$work/audit.log"

make_case
honest_audit_log "$work/audit.log"
python3 - "$work/audit.log" <<'PY'
import pathlib, sys
path = pathlib.Path(sys.argv[1])
lines = path.read_text().splitlines()
i = next(n for n, l in enumerate(lines) if "TacentaRatchet" in l)
del lines[i]
path.write_text("\n".join(lines) + "\n")
PY
expect_fail "audit-lacks-a-recorded-name" "in the recorded list but not in the environment" --compare-audit "$work/audit.log"

make_case
honest_audit_log "$work/audit.log"
python3 - "$work/audit.log" <<'PY'
import pathlib, sys
path = pathlib.Path(sys.argv[1])
lines = path.read_text().splitlines()
i = next(n for n, l in enumerate(lines) if "TacentaRatchet" in l)
lines.append(lines[i])
path.write_text("\n".join(lines) + "\n")
PY
expect_fail "audit-repeats-a-name" "in the environment but not in the recorded list" --compare-audit "$work/audit.log"

make_case
honest_audit_log "$work/audit.log"
printf 'audit-axiom: Translation.TacentaNothing tacenta_nothing.x\n' >> "$work/audit.log"
expect_fail "audit-reports-an-unrecorded-module" "which has no record in translation-attestation.json" --compare-audit "$work/audit.log"

make_case
honest_audit_log "$work/audit.log"
grep -v ' Translation.TacentaRatchet ' "$work/audit.log" > "$work/audit.log.new"
mv "$work/audit.log.new" "$work/audit.log"
expect_fail "audit-omits-a-module" "carries no audit-axiom lines for Translation.TacentaRatchet" --compare-audit "$work/audit.log"

make_case
honest_audit_log "$work/audit.log"
edit_json "$allowlist" 'data["generated_files"]["'"$gen"'/TacentaRatchet.lean"].pop()'
expect_fail "audit-differs-from-the-allowlist" "not in the allowlist list" --compare-audit "$work/audit.log"

# ---------------------------------------------------------------------------
# The allowlist writer.
# ---------------------------------------------------------------------------

make_case
expect_pass "writer-leaves-a-current-allowlist-alone" --write-axiom-allowlist
expect_unchanged "writer-leaves-a-current-allowlist-alone-wrote-nothing" "$allowlist"

make_case
expect_fail_in_ci "writer-refuses-in-ci" "does not run in CI" --write-axiom-allowlist

make_case
insert_in TacentaRatchet.lean <<'EOF'
def writer_form : Nat := 1
end writer_form
EOF
expect_fail "writer-refuses-an-unreadable-file" "cannot be read" --write-axiom-allowlist

make_case
insert_in TacentaRatchet.lean <<'EOF'
axiom planted_false : False
EOF
expect_pass_saying "writer-reports-what-it-added" \
  "allowlist + TacentaRatchet.lean: tacenta_ratchet.planted_false : False" --write-axiom-allowlist

make_case
replace_in "$gen/TacentaErasure.lean" \
  "axiom core.num.Usize.div_ceil : Std.Usize → Std.Usize → Result Std.Usize" \
  "-- removed"
expect_pass_saying "writer-reports-what-it-removed" \
  "allowlist - TacentaErasure.lean: tacenta_erasure.core.num.Usize.div_ceil : Std.Usize" --write-axiom-allowlist

# ---------------------------------------------------------------------------
# The construct scanner reads hand-written Lean the way the attestation scan
# reads the generated files. Each plant goes at the end of a proof file.
# ---------------------------------------------------------------------------

proof="tacenta-proofs/Proofs/ErrorHandling.lean"

make_case
expect_script_pass "constructs-unmodified-tree" check-lean-constructs.sh

make_case
cat >> "$work/$proof" <<'EOF'

def scanner_form_11_a : Char := '"'
run_cmd pure ()
def scanner_form_11_b : Char := '"'
EOF
expect_script_fail "scanner-form-11" "elab-time-command" check-lean-constructs.sh

make_case
cat >> "$work/$proof" <<'EOF'

def scanner_form_12_a : String := r#"a"b"#
run_cmd pure ()
def scanner_form_12_b : String := r#"a"b"#
EOF
expect_script_fail "scanner-form-12" "elab-time-command" check-lean-constructs.sh

make_case
cat >> "$work/$proof" <<'EOF'

def «/-» : Nat := 1
run_cmd pure ()
def «-/» : Nat := 2
EOF
expect_script_fail "scanner-form-13" "elab-time-command" check-lean-constructs.sh

make_case
cat >> "$work/$proof" <<'EOF'

axiom«scanner_form_14» : False
EOF
expect_script_fail "scanner-form-14" ": axiom:" check-lean-constructs.sh

make_case
cat >> "$work/$proof" <<'EOF'

def scanner_form_15_a : Char := '"'
axiom scanner_form_15 : False
def scanner_form_15_b : Char := '"'
EOF
expect_script_fail "scanner-form-15" ": axiom:" check-lean-constructs.sh

make_case
cat >> "$work/$proof" <<'EOF'

-- run_cmd in_a_line_comment
/- run_cmd in_a_block_comment -/
def not_a_construct_a : String := "run_cmd in_a_string"
def not_a_construct_b : Char := 'a'
def «run_cmd in_a_name» : Nat := 1
def not_a_construct_c : String := r#"run_cmd in a raw string"#
def x' : Nat := 1
def axiomatic : Nat := 1
EOF
expect_script_pass "constructs-text-that-is-not-a-construct" check-lean-constructs.sh

finish
