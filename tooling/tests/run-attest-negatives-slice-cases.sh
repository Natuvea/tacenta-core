#!/usr/bin/env bash
# Negative controls for the slices and the combiner of `tacenta-proofs/scripts/check-attest-negatives.sh`.
#
# CI splits that script's run over machines: each job of a matrix runs one slice (`ATTEST_NEGATIVES_SLICE=k/K`),
# which starts its share of the run's shards and writes their reports to a directory, and one more job runs the
# combiner (`ATTEST_NEGATIVES_COMBINE`) over the K directories. The combiner prints the final line of a full
# run only when the slices are the K slices of one run of this commit and script, and their shards together
# pass the check the parent of a run on one machine makes. A combiner that accepts too much turns a slice
# that never ran into a green line, so each fault below is made in a copy of a genuine set of slice
# directories, or in a slice made for the purpose, and the combiner must refuse it with the diagnostic of the
# check that notices it. The gate is the script as committed: commit a change to it before running this.
#
#   the genuine set                          accepted, as a partial run, with the count of a run on one machine
#   the genuine set as the gate              refused: its slices are partial runs (the test seam)
#   a slice missing, repeated, or one more   refused: the number of directories, a slice twice, a slice absent
#   two slices' manifests swapped            refused: each holds files of shards that are not its own
#   two slices relabelled, files and all     refused: each shard's own report names its index
#   a slice of another commit, tree or script, made for the purpose or edited into the manifest
#                                            refused, by the commit, the tree and the sha256 of the script
#   another K, another L, another N          refused: the split, the number of shards per slice, the range
#   a shard that ran no case                 refused: it ran 0 cases
#   reports whose R values do not add up     refused: the sum
#   a case run by two shards, or by none     refused: each case is run once
#   a shard that walked other cases          refused: the walks differ
#   a WRONG line, an exit status             refused
#   a shard that skipped its premise check   refused: P is not Q
#   a file missing, a file more, a file that is a link, a manifest missing, a stray entry
#                                            refused
#   the variables in the wrong combination   refused: a shard index, a slice and the combiner, a number of
#                                            shards for the combiner, a slice directory not empty or not set
#   a slice whose shard fails                the slice fails and writes nothing
#   the test seam in CI                      refused for a slice and for the combiner
#   a slice and the combiner in CI           accepted: the shards a slice starts are its own
#   the real attest.py                       two slices of the first cases, combined, accepted
#   files read strictly                      refused: an exit status of `+0` or `0_0` or with a carriage return,
#                                            a WRONG line indented or in lower case, a verdict that is not
#                                            `ok`, `wrong` or `-`, a digit of another script, a carriage return
#   the case floor                           a walk cut short refused by the single run, the parent and the
#                                            combiner; a walk at the floor accepted, one below it refused; a
#                                            floor missing, not a number, zero, two numbers or with a carriage
#                                            return refused
#   the count of cases                       printed without running a tool or a line of a run; refused with
#                                            another mode or value
#
# Most slices are made by a copy of the script whose attest.py and script calls are stubs that accept and
# whose judge of an expected refusal accepts too, so that a slice of the first cases takes seconds; that copy
# is also what the combiner is run as, since the combiner compares the script's sha256 with its own. One set
# is made with the real attest.py. As in the other runners of this directory the first case that goes wrong
# stops the run. Nothing here needs a Lean toolchain. The mutation harness reruns a runner with its `exit 1`
# and `set -e` lines removed, so the text of a plant never contains either.
set -euo pipefail

root="$(git rev-parse --show-toplevel)"
tmp_base="${TMPDIR:-/tmp}"
work="$(mktemp -d "$tmp_base/attest-slice-cases.XXXXXX")"
# The physical path: git prints worktrees by it, and this control compares those paths with its own.
work="$(cd "$work" && pwd -P)"
tree="$work/tree"
plants="$work/plants"
cleanup() {
  if pgrep -f "$plants/" >/dev/null 2>&1; then
    pkill -TERM -f "$plants/" >/dev/null 2>&1 || true
    sleep 2
  fi
  git -C "$root" worktree remove --force "$tree" >/dev/null 2>&1 || true
  git -C "$root" worktree remove --force "$work/floor-tree" >/dev/null 2>&1 || true
  git -C "$root" worktree prune >/dev/null 2>&1 || true
  rm -rf "$work"
}
trap cleanup EXIT
git -C "$root" worktree add -q --detach "$tree" HEAD >/dev/null

gate="tacenta-proofs/scripts/check-attest-negatives.sh"
mkdir -p "$plants" "$work/tmp"
cases=0
full_line='each mutation refused for its stated reason'
partial_line='^check-attest-negatives: PARTIAL RUN, not the gate (seam ATTEST_NEGATIVES_ONLY=[0-9]*): the first [0-9]* cases passed$'

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

# fast <name>: the tools of that copy accept everything, and so does its judge of an expected refusal, so
# every case of a walk passes in a moment. What is left is the walk, the shards, the slices and the combiner.
fast() {
  plant "$1" '  (cd "$work" && env -u GITHUB_ACTIONS python3 tacenta-proofs/scripts/attest.py "$@" 2>&1)' \
    '  { (cd "$work" && echo "stub: attest.py $*"); } 2>&1'
  plant "$1" '  (cd "$work" && GITHUB_ACTIONS=true python3 tacenta-proofs/scripts/attest.py "$@" 2>&1)' \
    '  { (cd "$work" && echo "stub: attest.py in CI $*"); } 2>&1'
  plant "$1" '  (cd "$work" && env -u GITHUB_ACTIONS bash "tacenta-proofs/scripts/$1" 2>&1)' \
    '  { (cd "$work" && echo "stub: $1"); } 2>&1'
  plant "$1" 'judge_refusal() {' 'judge_refusal() {
  return 0
}
judge_refusal_unused() {'
  plant "$1" 'judge_acceptance_saying() {' 'judge_acceptance_saying() {
  return 0
}
judge_acceptance_saying_unused() {'
}

# The environment a case starts from: the caller's CI and ATTEST_NEGATIVES_* variables removed.
clean_env=(env -u GITHUB_ACTIONS -u ATTEST_NEGATIVES_JOBS -u ATTEST_NEGATIVES_ONLY -u ATTEST_NEGATIVES_SHARD
  -u ATTEST_NEGATIVES_RESULTS -u ATTEST_NEGATIVES_WORKTREE -u ATTEST_NEGATIVES_REV -u ATTEST_NEGATIVES_PARENT
  -u ATTEST_NEGATIVES_TEST_ONLY -u ATTEST_NEGATIVES_SEAM -u ATTEST_NEGATIVES_SLICE -u ATTEST_NEGATIVES_SLICE_DIR
  -u ATTEST_NEGATIVES_COMBINE -u ATTEST_NEGATIVES_SLICES -u ATTEST_NEGATIVES_COUNT)

# run <name> <script> [VAR=value ...]: run a copy in the tree (or in $case_dir), output to out-<name>, status to
# rc-<name>.
run() {
  local name="$1" script="$2"
  shift 2
  mkdir -p "$work/tmp-$name"
  set +e
  (cd "${case_dir:-$tree}" && "${clean_env[@]}" TMPDIR="$work/tmp-$name" "$@" bash "$plants/$script.sh") \
    > "$work/out-$name" 2>&1
  echo $? > "$work/rc-$name"
  set -e
}

# slice <name> <script> <k/K> <L> <only> <directory> [VAR=value ...]: one slice, in the background.
slice() {
  local name="$1" script="$2" spec="$3" jobs="$4" only="$5" dir="$6"
  shift 6
  if [ -n "$only" ]; then
    set -- ATTEST_NEGATIVES_ONLY="$only" ATTEST_NEGATIVES_SEAM=tests-only "$@"
  fi
  run "$name" "$script" ATTEST_NEGATIVES_SLICE="$spec" ATTEST_NEGATIVES_JOBS="$jobs" \
    ATTEST_NEGATIVES_SLICE_DIR="$dir" "$@" &
}

# combine <name> <script> <directory> <K> <only> [VAR=value ...]
combine() {
  local name="$1" script="$2" dir="$3" slices="$4" only="$5"
  shift 5
  if [ -n "$only" ]; then
    set -- ATTEST_NEGATIVES_ONLY="$only" ATTEST_NEGATIVES_SEAM=tests-only "$@"
  fi
  run "$name" "$script" ATTEST_NEGATIVES_COMBINE="$dir" ATTEST_NEGATIVES_SLICES="$slices" "$@"
}

wrong() {  # name message...
  local name="$1"
  shift
  echo "WRONG  slice control $name: $*" >&2
  if [ -f "$work/out-$name" ]; then
    sed 's/^/    | /' "$work/out-$name" >&2
  fi
  exit 1
}

# Whatever the case, the run leaves no directory in its TMPDIR and no registered worktree.
left_nothing() {
  local name="$1"
  if [ -d "$work/tmp-$name" ] && [ -n "$(ls -A "$work/tmp-$name")" ]; then
    wrong "$name" "left $(ls -A "$work/tmp-$name" | tr '\n' ' ') in its TMPDIR"
  fi
  if git -C "$tree" worktree list --porcelain | grep -qF "worktree $work/tmp-$name/"; then
    wrong "$name" "left a registered worktree"
  fi
}

# accepts <name>: a partial run that succeeded, ending in its own line and never in the line of a full run.
accepts() {
  local name="$1"
  cases=$((cases + 1))
  if [ "$(cat "$work/rc-$name")" -ne 0 ]; then
    wrong "$name" "expected acceptance, was refused"
  fi
  if grep -qF -- "$full_line" "$work/out-$name"; then
    wrong "$name" "a partial run printed the line of a full run"
  fi
  if ! grep -q "$partial_line" "$work/out-$name"; then
    wrong "$name" "the partial run did not end in its own line"
  fi
  left_nothing "$name"
}

# refuses <name> <needle>: the run failed, said the needle, and printed no line of success.
refuses() {
  local name="$1" needle="$2"
  cases=$((cases + 1))
  if [ "$(cat "$work/rc-$name")" -eq 0 ]; then
    wrong "$name" "expected refusal containing '$needle', was accepted"
  fi
  if ! grep -qF -- "$needle" "$work/out-$name"; then
    wrong "$name" "refused, but not for '$needle':"
  fi
  if grep -q 'PARTIAL RUN\|cases gave the expected result' "$work/out-$name"; then
    wrong "$name" "a refused run printed a line of success"
  fi
  left_nothing "$name"
}

# A slice that wrote its directory: exit 0, a line that says it is not the gate, no line of a run.
sliced() {
  local name="$1" dir="$2"
  cases=$((cases + 1))
  if [ "$(cat "$work/rc-$name")" -ne 0 ] || [ ! -f "$dir/slice.json" ]; then
    wrong "$name" "the slice did not write its directory"
  fi
  if ! grep -q 'a slice is not the gate' "$work/out-$name" \
     || grep -q 'PARTIAL RUN\|cases gave the expected result' "$work/out-$name"; then
    wrong "$name" "a slice must say it is not the gate and print no line of a run"
  fi
  left_nothing "$name"
}

# variant <name>: a copy of the genuine set to change.
variant() {
  rm -rf "$work/set-$1"
  cp -R "$work/set" "$work/set-$1"
  echo "$work/set-$1"
}

# edit <file> <python>: run a Python program over a text file; `text` is its content, and what it leaves in
# `text` is written back.
edit() {
  python3 - "$1" "$2" <<'PY' || exit 2
import pathlib, sys
path, program = pathlib.Path(sys.argv[1]), sys.argv[2]
scope = {"text": path.read_text()}
before = scope["text"]
exec(program, scope)
if scope["text"] == before:
    raise SystemExit(f"control: the edit of {path} changed nothing; this control is out of date")
path.write_text(scope["text"])
PY
}

# manifest <file> <python>: the same over a slice manifest; `data` is the parsed document.
manifest() {
  python3 - "$1" "$2" <<'PY' || exit 2
import json, pathlib, sys
path, program = pathlib.Path(sys.argv[1]), sys.argv[2]
data = json.loads(path.read_text())
exec(program, {"data": data})
path.write_text(json.dumps(data, indent=2, sort_keys=True) + "\n")
PY
}

# ---------------------------------------------------------------------------
# The genuine set: three slices of two shards each (a run of six shards), over the first eight cases, by the
# fast copy. Case n goes to shard n % 6, so shards 0 and 1 run two cases and the others one each. Beside it,
# the same eight cases in one process, and the slices made for the purpose below.
# ---------------------------------------------------------------------------

K=3
L=2
only=8
fresh fast
fast fast
mkdir -p "$work/set"
for k in 0 1 2; do
  slice "slice-$k" fast "$k/$K" "$L" "$only" "$work/set/s$k"
done
run single fast ATTEST_NEGATIVES_JOBS=1 ATTEST_NEGATIVES_ONLY="$only" ATTEST_NEGATIVES_SEAM=tests-only &

# Slice 2 again, by a copy of the script that differs in one comment line.
fresh other-script
fast other-script
plant other-script 'set -euo pipefail
' 'set -euo pipefail
# another script
'
mkdir -p "$work/other-script"
slice other-script-slice other-script "2/$K" "$L" "$only" "$work/other-script/s2"

# Slice 2 again, of another commit with the same tree: an empty commit in a clone of its own.
git clone -q --no-hardlinks "$tree" "$work/other-commit-repo"
git -C "$work/other-commit-repo" checkout -q --detach "$(git -C "$tree" rev-parse HEAD)"
git -C "$work/other-commit-repo" -c user.name=control -c user.email=control@example.invalid \
  commit -q --allow-empty -m "another commit, the same tree"
mkdir -p "$work/other-commit"
case_dir="$work/other-commit-repo" slice other-commit-slice fast "2/$K" "$L" "$only" "$work/other-commit/s2"

# Slice 2 again, with one shard instead of two: a run split three ways with another L.
mkdir -p "$work/other-l"
slice other-l-slice fast "2/$K" 1 "$only" "$work/other-l/s2"

# A slice whose shard 3 (the second of slice 1) is refused by its attest.py.
fresh shard-fails
fast shard-fails
plant shard-fails '  { (cd "$work" && echo "stub: attest.py $*"); } 2>&1' \
  '  { (cd "$work" && echo "stub: attest.py $*" && [ "$shard" -ne 3 ]); } 2>&1'
slice shard-fails shard-fails "1/$K" "$L" "$only" "$work/shard-fails-dir"

# A slice and the combiner in CI. The copy takes the length of the walk from another variable, read after the
# check that refuses the seam in CI.
fresh ci
fast ci
plant ci 'is_shard=0
shard=0
jobs=1
' 'only="${ATTEST_NEGATIVES_TEST_ONLY:-}"
is_shard=0
shard=0
jobs=1
'
mkdir -p "$work/ci-set"
for k in 0 1; do
  slice "ci-slice-$k" ci "$k/2" 1 "" "$work/ci-set/s$k" GITHUB_ACTIONS=true ATTEST_NEGATIVES_TEST_ONLY=2
done
# The seam itself in CI, for a slice.
slice ci-seam-slice fast "0/$K" "$L" "$only" "$work/ci-seam-dir" GITHUB_ACTIONS=true

# The real attest.py: two slices of one shard each over the first three cases (the two premise checks and
# a claim that names a theorem that does not exist).
fresh real
mkdir -p "$work/real-set"
for k in 0 1; do
  slice "real-slice-$k" real "$k/2" 1 3 "$work/real-set/s$k"
done
wait

for k in 0 1 2; do
  sliced "slice-$k" "$work/set/s$k"
done
sliced other-script-slice "$work/other-script/s2"
sliced other-commit-slice "$work/other-commit/s2"
sliced other-l-slice "$work/other-l/s2"
for k in 0 1; do
  sliced "ci-slice-$k" "$work/ci-set/s$k"
  sliced "real-slice-$k" "$work/real-set/s$k"
done

# The genuine set is accepted as a partial run, with the count of the same walk in one process.
combine genuine fast "$work/set" "$K" "$only"
accepts genuine
cases=$((cases + 1))
if ! grep -qx "check-attest-negatives: 6 shards ran 2 + 2 + 1 + 1 + 1 + 1 = 8 cases.*" "$work/out-genuine"; then
  wrong genuine "the six shards did not run 2 + 2 + 1 + 1 + 1 + 1 cases"
fi
if [ "$(tail -n 1 "$work/out-genuine")" != "$(tail -n 1 "$work/out-single")" ]; then
  wrong genuine "the combined slices and the run in one process did not report the same count"
fi

# The genuine set as the gate: its slices stopped at the seam.
combine as-gate fast "$work/set" "$K" ""
refuses as-gate "walked the first 8 cases (seam ATTEST_NEGATIVES_ONLY=8), and the combiner requires every case"

# A slice missing, repeated, or one more.
dir="$(variant missing)"
rm -rf "$dir/s2"
combine missing fast "$dir" "$K" "$only"
refuses missing "holds 2 slice directories, not the 3 the run is split into"
cases=$((cases + 1))
grep -qF "no directory is slice 2/3" "$work/out-missing" || wrong missing "did not name the missing slice"
dir="$(variant repeated)"
rm -rf "$dir/s2"
cp -R "$dir/s1" "$dir/s2"
combine repeated fast "$dir" "$K" "$only"
refuses repeated "two directories are slice 1/3: s1 and s2"
dir="$(variant one-more)"
cp -R "$dir/s1" "$dir/s3"
combine one-more fast "$dir" "$K" "$only"
refuses one-more "holds 4 slice directories, not the 3 the run is split into"

# Two slices' manifests swapped: slice 0's files under slice 1's name and the reverse.
dir="$(variant swapped)"
mv "$dir/s0/slice.json" "$dir/swap.json"
mv "$dir/s1/slice.json" "$dir/s0/slice.json"
mv "$dir/swap.json" "$dir/s1/slice.json"
combine swapped fast "$dir" "$K" "$only"
refuses swapped "slice 1/3 (s0) has no rc-2"

# Relabelled with the files: slice 0's shards 0 and 1 renamed 2 and 3, and the reverse, manifests swapped. The
# file set of each slice is right; the shards' own reports are not.
dir="$(variant relabelled)"
mkdir "$dir/t0" "$dir/t1"
for pair in "0 2" "1 3"; do
  set -- $pair
  for stem in rc- results-; do
    mv "$dir/s0/$stem$1" "$dir/t1/$stem$2"
    mv "$dir/s1/$stem$2" "$dir/t0/$stem$1"
  done
  mv "$dir/s0/shard-$1.log" "$dir/t1/shard-$2.log"
  mv "$dir/s1/shard-$2.log" "$dir/t0/shard-$1.log"
done
mv "$dir/s0/slice.json" "$dir/t1/slice.json"
mv "$dir/s1/slice.json" "$dir/t0/slice.json"
rm -rf "$dir/s0" "$dir/s1"
manifest "$dir/t0/slice.json" 'data["slice"] = 0; data["first"] = 0'
manifest "$dir/t1/slice.json" 'data["slice"] = 1; data["first"] = 2'
combine relabelled fast "$dir" "$K" "$only"
refuses relabelled "shard 0/6 reported itself as shard 2/6"

# A slice of another commit, tree or script.
dir="$(variant other-commit)"
rm -rf "$dir/s2"
cp -R "$work/other-commit/s2" "$dir/s2"
combine other-commit fast "$dir" "$K" "$only"
refuses other-commit "ran on commit $(git -C "$work/other-commit-repo" rev-parse HEAD), not on $(git -C "$tree" rev-parse HEAD)"
dir="$(variant other-commit-edited)"
manifest "$dir/s1/slice.json" 'data["commit"] = "0" * 40'
combine other-commit-edited fast "$dir" "$K" "$only"
refuses other-commit-edited "ran on commit 0000000000000000000000000000000000000000"
dir="$(variant other-tree)"
manifest "$dir/s1/slice.json" 'data["tree"] = "0" * 40'
combine other-tree fast "$dir" "$K" "$only"
refuses other-tree "ran on tree 0000000000000000000000000000000000000000"
dir="$(variant other-script)"
rm -rf "$dir/s2"
cp -R "$work/other-script/s2" "$dir/s2"
combine other-script fast "$dir" "$K" "$only"
refuses other-script "was made by a check-attest-negatives.sh with sha256"
dir="$(variant other-script-edited)"
manifest "$dir/s0/slice.json" 'data["script_sha256"] = "f" * 64'
combine other-script-edited fast "$dir" "$K" "$only"
refuses other-script-edited "was made by a check-attest-negatives.sh with sha256 ffff"

# Another K, another L, another N.
combine other-k fast "$work/set" 4 "$only"
refuses other-k "is a slice of a run split 3 ways, not 4"
dir="$(variant other-l)"
rm -rf "$dir/s2"
cp -R "$work/other-l/s2" "$dir/s2"
combine other-l fast "$dir" "$K" "$only"
refuses other-l "the slices start different numbers of shards"
dir="$(variant other-n)"
manifest "$dir/s1/slice.json" 'data["shards"] = 7'
combine other-n fast "$dir" "$K" "$only"
refuses other-n "which are not the shards of slice 1 of 3 with 2 each"
dir="$(variant other-walk-length)"
manifest "$dir/s1/slice.json" 'data["partial"] = 7'
combine other-walk-length fast "$dir" "$K" "$only"
refuses other-walk-length "walked the first 7 cases (seam ATTEST_NEGATIVES_ONLY=7), and the combiner requires the first 8"

# The shards' reports, through the check the parent makes.
dir="$(variant ran-zero)"
edit "$dir/s2/shard-4.log" 'text = text.replace("shard 4/6: ran 1 of 8", "shard 4/6: ran 0 of 8")'
edit "$dir/s2/results-4" 'text = text.replace("4\tran\tok", "4\tskip\t-")'
combine ran-zero fast "$dir" "$K" "$only"
refuses ran-zero "shard 4/6 ran 0 of 8 cases"
dir="$(variant sum)"
edit "$dir/s2/shard-5.log" 'text = text.replace("shard 5/6: ran 1 of 8", "shard 5/6: ran 2 of 8")'
combine sum fast "$dir" "$K" "$only"
refuses sum "the shards ran 9 cases between them, not the 8 there are"
dir="$(variant run-twice)"
edit "$dir/s0/results-1" 'text = text.replace("0\tskip\t-\t0\t0\t", "0\tran\tok\t0\t0\t", 1)'
edit "$dir/s0/shard-1.log" 'text = text.replace("ran 2 of 8", "ran 3 of 8")'
combine run-twice fast "$dir" "$K" "$only"
refuses run-twice "case 0 (unmodified-tree) was run by shards 0 and 1"
dir="$(variant run-by-none)"
edit "$dir/s0/results-0" 'text = text.replace("0\tran\tok\t", "0\tskip\t-\t", 1)'
edit "$dir/s0/shard-0.log" 'text = text.replace("ran 2 of 8", "ran 1 of 8")'
combine run-by-none fast "$dir" "$K" "$only"
refuses run-by-none "case 0 (unmodified-tree) was run by no shard"
dir="$(variant other-walk)"
edit "$dir/s1/results-3" 'text = text.replace("\tunmodified-translation\n", "\tanother-case\n")'
combine other-walk fast "$dir" "$K" "$only"
refuses other-walk "shard 3/6 walked different cases from shard 0/6"
dir="$(variant wrong-line)"
echo "WRONG  planted: a case gave the wrong result" >> "$dir/s1/shard-2.log"
combine wrong-line fast "$dir" "$K" "$only"
refuses wrong-line "shard 2/6 printed 1 WRONG line(s)"
dir="$(variant exit-status)"
echo 1 > "$dir/s1/rc-3"
combine exit-status fast "$dir" "$K" "$only"
refuses exit-status "shard 3/6 exited with status 1"
dir="$(variant premise)"
edit "$dir/s2/shard-4.log" 'text = text.replace("shard 4/6: premise 2 of 2", "shard 4/6: premise 1 of 2")'
combine premise fast "$dir" "$K" "$only"
refuses premise "shard 4/6 checked that its worktree accepts the unmodified tree 1 time(s) of the 2 it reaches"

# The files of a slice and the entries of the directory.
dir="$(variant file-missing)"
rm "$dir/s2/results-4"
combine file-missing fast "$dir" "$K" "$only"
refuses file-missing "slice 2/3 (s2) has no results-4"
dir="$(variant file-more)"
echo extra > "$dir/s1/extra"
combine file-more fast "$dir" "$K" "$only"
refuses file-more "holds extra, which is not a file of its own shards"
dir="$(variant file-link)"
mv "$dir/s1/rc-2" "$work/rc-2-of-file-link"
ln -s "$work/rc-2-of-file-link" "$dir/s1/rc-2"
combine file-link fast "$dir" "$K" "$only"
refuses file-link "slice 1/3 (s1): rc-2 is not a regular file"
dir="$(variant no-manifest)"
rm "$dir/s0/slice.json"
combine no-manifest fast "$dir" "$K" "$only"
refuses no-manifest "s0 has no readable slice.json"
dir="$(variant stray)"
echo notes > "$dir/notes.txt"
combine stray fast "$dir" "$K" "$only"
refuses stray "notes.txt in $dir is not a slice directory"

# The variables in the wrong combination.
combine with-jobs fast "$work/set" "$K" "$only" ATTEST_NEGATIVES_JOBS=2
refuses with-jobs "so it refuses ATTEST_NEGATIVES_JOBS"
combine no-count fast "$work/set" "" "$only"
refuses no-count "ATTEST_NEGATIVES_SLICES, which is not set"
run slice-and-shard fast ATTEST_NEGATIVES_SLICE=0/2 ATTEST_NEGATIVES_SHARD=0/2 ATTEST_NEGATIVES_SLICE_DIR="$work/unused-1"
refuses slice-and-shard "a slice or the combiner does not take it"
run slice-and-combiner fast ATTEST_NEGATIVES_SLICE=0/2 ATTEST_NEGATIVES_COMBINE="$work/set" ATTEST_NEGATIVES_SLICES=2
refuses slice-and-combiner "not both"
run no-slice-dir fast ATTEST_NEGATIVES_SLICE=0/2
refuses no-slice-dir "ATTEST_NEGATIVES_SLICE_DIR, which is not set"
mkdir -p "$work/victim/sub"
echo kept > "$work/victim/sub/file.txt"
run slice-dir-used fast ATTEST_NEGATIVES_SLICE=0/2 ATTEST_NEGATIVES_SLICE_DIR="$work/victim"
refuses slice-dir-used "is not an empty directory"
cases=$((cases + 1))
if [ "$(cat "$work/victim/sub/file.txt" 2>/dev/null)" != kept ]; then
  wrong slice-dir-used "the directory that was refused lost its file"
fi
run not-a-slice fast ATTEST_NEGATIVES_SLICE=2/2 ATTEST_NEGATIVES_SLICE_DIR="$work/unused-2"
refuses not-a-slice "is not a slice of a run"

# A slice whose shard fails stops its own job and writes nothing.
refuses shard-fails "slice 1/3 failed: a shard exited nonzero or printed a WRONG line"
cases=$((cases + 1))
if [ -e "$work/shard-fails-dir" ]; then
  wrong shard-fails "a failed slice wrote its directory"
fi

# The seam in CI: refused for a slice and for the combiner.
refuses ci-seam-slice "so CI refuses it"
combine ci-seam-combine fast "$work/set" "$K" "$only" GITHUB_ACTIONS=true
refuses ci-seam-combine "so CI refuses it"

# A slice and the combiner in CI: the slices above ran there, and the combiner accepts them.
combine ci-combine ci "$work/ci-set" 2 "" GITHUB_ACTIONS=true ATTEST_NEGATIVES_TEST_ONLY=2
accepts ci-combine

# The real attest.py.
combine real fast "$work/real-set" 2 3
refuses real "was made by a check-attest-negatives.sh with sha256"
combine real real "$work/real-set" 2 3
accepts real
cases=$((cases + 1))
if ! grep -qx "check-attest-negatives: 2 shards ran 2 + 1 = 3 cases.*" "$work/out-real"; then
  wrong real "the two shards did not run 2 + 1 cases"
fi

# ---------------------------------------------------------------------------
# The shards' files are read strictly: they cross a job boundary before the combiner reads them.
# ---------------------------------------------------------------------------

dir="$(variant rc-plus)"
printf '+0\n' > "$dir/s1/rc-3"
combine rc-plus fast "$dir" "$K" "$only"
refuses rc-plus "shard 3/6 left an exit status that is not a number: '+0\n'"
dir="$(variant rc-underscore)"
printf '0_0\n' > "$dir/s1/rc-3"
combine rc-underscore fast "$dir" "$K" "$only"
refuses rc-underscore "shard 3/6 left an exit status that is not a number: '0_0\n'"
dir="$(variant rc-cr)"
printf '0\r\n' > "$dir/s1/rc-3"
combine rc-cr fast "$dir" "$K" "$only"
refuses rc-cr "shard 3/6 left an exit status that is not a number"
dir="$(variant wrong-indented)"
echo " WRONG  planted: an indented WRONG line" >> "$dir/s1/shard-2.log"
combine wrong-indented fast "$dir" "$K" "$only"
refuses wrong-indented "shard 2/6 printed 1 WRONG line(s)"
dir="$(variant wrong-lower)"
echo "wrong  planted: a WRONG line in lower case" >> "$dir/s1/shard-2.log"
combine wrong-lower fast "$dir" "$K" "$only"
refuses wrong-lower "shard 2/6 printed 1 WRONG line(s)"
dir="$(variant verdict-upper)"
edit "$dir/s0/results-0" 'text = text.replace("0\tran\tok\t", "0\tran\tWRONG\t", 1)'
combine verdict-upper fast "$dir" "$K" "$only"
refuses verdict-upper "shard 0/6: line 1 of its list of cases is not a case"
dir="$(variant verdict-skip)"
edit "$dir/s0/results-1" 'text = text.replace("0\tskip\t-\t", "0\tskip\tok\t", 1)'
combine verdict-skip fast "$dir" "$K" "$only"
refuses verdict-skip "shard 1/6: line 1 of its list of cases is not a case"
dir="$(variant digit-other-script)"
edit "$dir/s1/results-2" 'text = text.replace("0\tskip", "٠\tskip", 1)'
combine digit-other-script fast "$dir" "$K" "$only"
refuses digit-other-script "shard 2/6: line 1 of its list of cases is not a case"
dir="$(variant results-crlf)"
edit "$dir/s2/results-4" 'text = text.replace("\n", "\r\n")'
combine results-crlf fast "$dir" "$K" "$only"
refuses results-crlf "shard 4/6: its list of cases holds a carriage return"
dir="$(variant log-cr)"
edit "$dir/s2/shard-5.log" 'text = text.replace("\n", "\r\n", 1)'
combine log-cr fast "$dir" "$K" "$only"
refuses log-cr "shard 5/6: its log holds a carriage return"

# ---------------------------------------------------------------------------
# The case floor. A copy whose walk ends after the two premise checks is refused wherever a full run would
# print its final line; in a worktree whose floor is 2 it is accepted, and with 3 refused. The floor is read
# from the tree under test, so the floor cases run in a worktree of their own.
# ---------------------------------------------------------------------------

floor_file="tacenta-proofs/scripts/attest-negatives-case-floor.txt"
real_floor="$(cat "$tree/$floor_file")"
fresh cut
fast cut
plant cut 'premise_pass "unmodified-translation" --check-translation
' 'premise_pass "unmodified-translation" --check-translation
finish
'
run cut-single cut ATTEST_NEGATIVES_JOBS=1
refuses cut-single "the walk has 2 cases, fewer than the floor of $real_floor"
run cut-parent cut ATTEST_NEGATIVES_JOBS=2
refuses cut-parent "the walk has 2 cases, fewer than the floor of $real_floor"
mkdir -p "$work/cut-set"
for k in 0 1; do
  slice "cut-slice-$k" cut "$k/2" 1 "" "$work/cut-set/s$k"
done
wait
for k in 0 1; do
  sliced "cut-slice-$k" "$work/cut-set/s$k"
done
combine cut-combine cut "$work/cut-set" 2 ""
refuses cut-combine "the walk has 2 cases, fewer than the floor of $real_floor"

floor_tree="$work/floor-tree"
git -C "$root" worktree add -q --detach "$floor_tree" HEAD >/dev/null
floor_case() {  # name floor-file-content (absent: no file) expected: accepts or a needle
  local name="$1" content="$2" want="$3"
  if [ "$content" = absent ]; then
    rm -f "$floor_tree/$floor_file"
  else
    printf '%b' "$content" > "$floor_tree/$floor_file"
  fi
  case_dir="$floor_tree" run "$name" cut ATTEST_NEGATIVES_JOBS=1
  if [ "$want" = accepts ]; then
    cases=$((cases + 1))
    if [ "$(cat "$work/rc-$name")" -ne 0 ] \
       || ! grep -qx "check-attest-negatives: 2 cases gave the expected result.*" "$work/out-$name"; then
      wrong "$name" "a walk at the floor was not accepted with the line of a full run"
    fi
    left_nothing "$name"
  else
    refuses "$name" "$want"
  fi
}
floor_case floor-at-count '2\n' accepts
floor_case floor-above-count '3\n' "the walk has 2 cases, fewer than the floor of 3"
floor_case floor-missing absent "cannot read the case floor"
floor_case floor-not-a-number 'many\n' "does not hold one whole number"
floor_case floor-zero '0\n' "does not hold one whole number"
floor_case floor-two-numbers '2 3\n' "does not hold one whole number"
floor_case floor-cr '2\r\n' "does not hold one whole number"
git -C "$root" worktree remove --force "$floor_tree" >/dev/null 2>&1

# ---------------------------------------------------------------------------
# The count of cases: walked in one process, with no tool run and no line of a run.
# ---------------------------------------------------------------------------

fresh count-probe
plant count-probe '  (cd "$work" && env -u GITHUB_ACTIONS python3 tacenta-proofs/scripts/attest.py "$@" 2>&1)' \
  '  { echo attest >> "$work_probe"; } 2>&1'
plant count-probe '  (cd "$work" && env -u GITHUB_ACTIONS bash "tacenta-proofs/scripts/$1" 2>&1)' \
  '  { echo script >> "$work_probe"; } 2>&1'
plant count-probe 'set -euo pipefail
' 'set -euo pipefail
work_probe="${COUNT_PROBE:?}"
'
run count count-probe ATTEST_NEGATIVES_COUNT=1 ATTEST_NEGATIVES_ONLY=5 ATTEST_NEGATIVES_SEAM=tests-only \
  COUNT_PROBE="$work/count-probe-calls"
cases=$((cases + 1))
if [ "$(cat "$work/rc-count")" -ne 0 ] || ! grep -qx "check-attest-negatives: the walk has 5 cases (ATTEST_NEGATIVES_COUNT: none was run, so this is not the gate)" "$work/out-count"; then
  wrong count "the count of the first five cases was not printed"
fi
if [ -e "$work/count-probe-calls" ] || grep -q 'PARTIAL RUN\|cases gave the expected result' "$work/out-count"; then
  wrong count "the count ran a tool or printed a line of a run"
fi
left_nothing count
run count-with-jobs fast ATTEST_NEGATIVES_COUNT=1 ATTEST_NEGATIVES_JOBS=2
refuses count-with-jobs "so it does not take ATTEST_NEGATIVES_JOBS"
run count-with-slice fast ATTEST_NEGATIVES_COUNT=1 ATTEST_NEGATIVES_SLICE=0/2 ATTEST_NEGATIVES_SLICE_DIR="$work/unused-3"
refuses count-with-slice "so it does not take ATTEST_NEGATIVES_SLICE"
run count-other-value fast ATTEST_NEGATIVES_COUNT=yes
refuses count-other-value "ATTEST_NEGATIVES_COUNT is 1 or unset"

# Every worktree these cases registered is gone: only the repository's own and this control's remain.
leftover="$(git -C "$tree" worktree list --porcelain | grep -F "worktree $work/" | grep -vF "worktree $tree" || true)"
if [ -n "$leftover" ]; then
  echo "WRONG  slice control: worktrees left registered: $leftover" >&2
  exit 1
fi

echo "attest-negatives-slice-cases: $cases cases (the genuine set accepted with the count of one process, and as the gate refused for its seam; a slice missing, repeated or one more, manifests swapped, slices relabelled with their files, another commit, tree or script, another K, L, N or walk length, a shard that ran nothing, a sum that is wrong, a case run twice or by none, another walk, a WRONG line, an exit status, a premise skipped, a file missing, extra or a link, a manifest missing, a stray entry, the variables combined wrongly, a failing shard, the seam in CI, a slice and the combiner in CI, the real attest.py, files read strictly, the case floor, the count of cases) gave the expected result"
