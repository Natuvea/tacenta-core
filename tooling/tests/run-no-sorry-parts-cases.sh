#!/usr/bin/env bash
# Negative controls for the parts and the combiner of `tacenta-proofs/scripts/no-sorry.sh`.
#
# CI splits that script's run over machines: each job of a matrix runs one part (`NO_SORRY_PART`), the
# prelude builds and its own phases, and writes its log and a manifest; one more job runs the combiner
# (`NO_SORRY_COMBINE`) over the part directories. The combiner prints the line of a full run only when the
# parts are those of one partition of `scripts/no-sorry-parts.txt`, of this commit, tree and script, all
# passed, and together ran every phase once and every control of the sliced dispatcher phase once. A
# combiner that accepts too much turns a part that never ran into a green line, so each fault below is made
# in a copy of a genuine set of part directories, or by a part run for the purpose, and the combiner must
# refuse it with the diagnostic of the check that notices it.
#
#   the genuine set of the `hosted` partition   accepted, with the final line the whole run prints
#   the `single` partition (one part, `*`)      accepted, with the same line
#   a build that fails, in the whole run and in a part   nonzero, no final line, nothing after it run, and the
#                                               part refused by the combiner
#   what the parts called                       each phase's script once over all parts, the prelude builds in
#                                               every part, the dispatcher once per slice: the calls of the
#                                               whole run and nothing else
#   a part missing, repeated, one more, or of another partition       refused
#   two manifests swapped, a part relabelled, two dispatcher slices' results swapped   refused
#   another commit (made for the purpose), another tree, script or parts file, another build cache
#   (made for the purpose), another toolchain, a checkout with a change (made for the purpose)   refused
#   a part whose phase failed (made for the purpose), a phase status or exit status edited   refused
#   a WRONG line, an `::error::` line (also after a carriage return), a closing line missing   refused
#   a part that ran fewer phases than its own        refused
#   the seam: a phase script's seam variable set     the part and the whole run refuse to start; a manifest
#                                                    that names a seam is refused
#   a dispatcher slice that selected other controls, recorded fewer, or lost a baseline, a log or a file,
#   or holds a link or another file                  refused
#   a manifest with a repeated key, a field more, a status that is a boolean, a byte outside printable
#   ASCII (in a dispatcher result too)             refused
#   a stray file or link in the directory or in a part   refused
#   the parts file: a phase in no part (the script given a phase the file does not assign, made for the
#   purpose: every part refuses before it runs, and so does the combiner), a phase in two parts, a slice
#   missing or twice, a phase sliced two ways, a plain or prelude phase named or sliced, more slices than
#   controls, a malformed line, a carriage return    refused
#   the variables in the wrong combination           refused
#
# The fixture is a git repository holding the real `no-sorry.sh`, `no-sorry-parts.py`, `no-sorry-parts.txt`
# and `check-translation-coverage.sh`, with every other script the run calls replaced by a stub that records
# its call and fails on request, `lake` replaced by a stub that prints a canned build log, and the dispatcher
# replaced by a stub with ten controls that keeps the real script's `--list`, `--slice` and result file. As in
# the other runners of this directory the first case that goes wrong stops the run. Nothing here needs a
# Lean toolchain. The mutation harness reruns a runner with its `exit 1` and `set -e` lines removed, so the
# text of a plant never contains either.
set -euo pipefail

root="$(git rev-parse --show-toplevel)"
scripts="$root/tacenta-proofs/scripts"
work="$(mktemp -d "${TMPDIR:-/tmp}/no-sorry-parts-cases.XXXXXX")"
work="$(cd "$work" && pwd -P)"
trap 'rm -rf "$work"' EXIT
cases=0

wrong() {  # name message...
  local name="$1"
  shift
  echo "WRONG  parts control $name: $*" >&2
  if [ -f "$work/out-$name" ]; then
    sed 's/^/    | /' "$work/out-$name" >&2
  fi
  exit 1
}

# ---- the fixture -------------------------------------------------------------------------------------
fx="$work/fixture"
proofs="$fx/tacenta-proofs"
mkdir -p "$proofs/scripts" "$proofs/translation/Translation" "$proofs/Proofs" \
  "$fx/tacenta-model/Model" "$fx/tacenta-model/Properties" "$work/bin" "$work/logs"
for f in no-sorry-parts.py no-sorry-parts.txt no-sorry.sh check-translation-coverage.sh; do
  cp "$scripts/$f" "$proofs/scripts/$f"
done
for m in Alpha Beta; do : > "$proofs/translation/Translation/$m.lean"; done
: > "$proofs/Proofs/Gamma.lean"
: > "$fx/tacenta-model/Model/Delta.lean"
: > "$fx/tacenta-model/Properties/Epsilon.lean"
printf 'name = "Translation"\n[[lean_lib]]\nname = "Translation"\nglobs = ["Translation.*"]\n' \
  > "$proofs/translation/lakefile.toml"
printf '.lake/\n' > "$fx/.gitignore"
lib="$proofs/translation/.lake/build/lib/lean/Translation"
mkdir -p "$lib"
for m in Alpha Beta; do : > "$lib/$m.olean"; done

stub_sh() {
  cat >"$proofs/scripts/$1" <<'STUB'
#!/usr/bin/env bash
echo "$(basename "$0") $*" >> "$STUB_CALLS"
[ "${STUB_FAIL:-}" = "$(basename "$0")" ] && { echo "stub $(basename "$0") fails as asked" >&2; exit 1; }
exit 0
STUB
}
stub_py() {
  cat >"$proofs/scripts/$1" <<'STUB'
#!/usr/bin/env python3
import os, sys
name = os.path.basename(sys.argv[0])
open(os.environ["STUB_CALLS"], "a").write(name + " " + " ".join(sys.argv[1:]) + "\n")
if os.environ.get("STUB_FAIL") == name:
    sys.stderr.write("stub %s fails as asked\n" % name)
    sys.exit(1)
STUB
}
for s in check-lifecycle-translation-coverage-negatives.sh check-refuted-records.sh \
  check-refuted-records-negatives.sh check-session-satisfiability-negatives.sh check-port-negatives.sh \
  check-lean-constructs.sh check-audit-reach.sh check-audit-reach-negatives.sh check-pin-negatives.sh \
  check-kernel-replay-negative.sh check-audit-negatives.sh check-precondition-witnesses.sh \
  check-hypothesis-witnesses.sh check-braid-agreement-negatives.sh; do
  stub_sh "$s"
done
# The Python scripts the run calls, one per line: `new-lifecycle-module.py scaffold` adds a new negatives script
# here after the entry its name sorts after, and the check below names any script the run calls that has no stub.
py_stubs=(
  check-lifecycle-translation-coverage.py
  check-receive-preservation-negatives.py
  check-atomicity-negatives.py
  check-repair-negatives.py
  check-responder-establish-replay-negatives.py
  check-send-refusal-negatives.py
  check-sparse-skip-kind-negatives.py
  check-sparse-store-full-negatives.py
  check-tampered-reply-negatives.py
  check-decrypt-ratchet-negatives.py
  check-established-negatives.py
  check-initiator-repeated-reply-negatives.py
  check-initiator-second-message-negatives.py
  check-restored-negatives.py
  check-encrypt-negatives.py
  check-responder-negatives.py
  check-responder-frame-negatives.py
  check-responder-receipt-negatives.py
  check-responder-repeated-frame-negatives.py
  check-responder-successor-negatives.py
  check-responder-reply-negatives.py
  check-responder-reply-receipt-negatives.py
  check-responder-second-receipt-negatives.py
  check-responder-second-send-negatives.py
  check-send-preservation-negatives.py
  check-discharge-native-decide-negatives.py
  check-initiator-second-send-negatives.py
  attest.py
)
for s in "${py_stubs[@]}"; do
  stub_py "$s"
done
# The dispatcher: ten controls over two sources, with the real script's options and result file.
cat >"$proofs/scripts/check-initial-dispatch-negatives.py" <<'STUB'
#!/usr/bin/env python3
import argparse, json, os, sys
from pathlib import Path
UNITS = [(f"control-{i}", "agreement" if i % 4 == 1 else "lifecycle") for i in range(10)]
parser = argparse.ArgumentParser()
parser.add_argument("--list", action="store_true")
parser.add_argument("--slice")
parser.add_argument("--log-dir", type=Path)
args = parser.parse_args()
if args.list:
    for name, source in UNITS:
        print(f"{name}\t{source}")
    sys.exit(0)
open(os.environ["STUB_CALLS"], "a").write("check-initial-dispatch-negatives.py " + " ".join(sys.argv[1:]) + "\n")
if os.environ.get("STUB_FAIL") == "check-initial-dispatch-negatives.py":
    sys.exit("stub check-initial-dispatch-negatives.py fails as asked")
k, count = map(int, args.slice.split("/")) if args.slice else (0, 1)
selected = [(n, s) for i, (n, s) in enumerate(UNITS) if i % count == k]
if args.log_dir:
    sources = sorted({s for _, s in selected})
    for s in sources:
        (args.log_dir / f"baseline-{s}.log").write_text("")
    for n, _ in selected:
        (args.log_dir / f"{n}.log").write_text("error\n")
    result = {"source_sha256": "0" * 64, "source_sha256s": {s: "0" * 64 for s in sources},
              "mutations": {n: {"exit": 1, "premise": "p"} for n, _ in selected},
              "slice": args.slice, "requested_mutations": "all", "selected": [n for n, _ in selected],
              "baseline_exits": {s: 0 for s in sources}, "baseline_exit": 0}
    (args.log_dir / "result.json").write_text(json.dumps(result, indent=2) + "\n")
print(f"{len(selected)} proof-dependency mutations rejected")
STUB

cat >"$work/bin/lake" <<'STUB'
#!/usr/bin/env bash
pkg="$(basename "$(pwd)")"
case "$1" in
  build)
    echo "lake build $pkg" >> "$STUB_CALLS"
    [ -f "$STUB_LOGS/$pkg.log" ] && cat "$STUB_LOGS/$pkg.log"
    [ "${STUB_BUILD_FAIL:-}" = "$pkg" ] && { echo "error: build failed as asked" >&2; exit 3; }
    exit 0 ;;
  env)
    echo "leanchecker $pkg $3" >> "$STUB_CALLS"
    exit 0 ;;
esac
exit 0
STUB
cat >"$work/bin/lean" <<'STUB'
#!/usr/bin/env bash
echo "Lean (version stub)"
STUB
chmod +x "$work/bin/lake" "$work/bin/lean"
printf 'building\naudit-axiom: Translation.TacentaX axiom foo : Nat\n' > "$work/logs/translation.log"

git -C "$fx" init -q
gitc=(git -C "$fx" -c user.name=control -c user.email=control@example.invalid -c commit.gpgsign=false)
"${gitc[@]}" add -A
"${gitc[@]}" commit -q -m fixture
c0="$(git -C "$fx" rev-parse HEAD)"

# The environment a case starts from: the caller's CI and NO_SORRY_* variables removed.
clean_env=(env -u GITHUB_ACTIONS -u GITHUB_STEP_SUMMARY -u NO_SORRY_LIST -u NO_SORRY_PART -u NO_SORRY_PART_DIR
  -u NO_SORRY_PART_RUN -u NO_SORRY_PART_SELECTION -u NO_SORRY_COMBINE -u NO_SORRY_PARTITION
  -u NO_SORRY_BUILD_CACHE -u REFUTED_RECORDS_BIN -u BRAIDNEG_FILTER -u HYPWIT_ROOT -u STUB_FAIL -u STUB_BUILD_FAIL)

# run <name> [VAR=value ...]: no-sorry.sh in the fixture; output to out-<name>, status to rc-<name>, calls
# to calls-<name>.
run() {
  local name="$1"
  shift
  : > "$work/calls-$name"
  set +e
  (cd "$proofs" && "${clean_env[@]}" PATH="$work/bin:$PATH" STUB_CALLS="$work/calls-$name" \
    STUB_LOGS="$work/logs" "$@" bash scripts/no-sorry.sh) > "$work/out-$name" 2>&1
  echo $? > "$work/rc-$name"
  set -e
}

# part <name> <part> <directory> [VAR=value ...]: one part, with the build cache of the genuine set.
part() {
  local name="$1" p="$2" dir="$3"
  shift 3
  run "$name" NO_SORRY_PART="$p" NO_SORRY_PART_DIR="$dir" NO_SORRY_BUILD_CACHE=lean-build-key-1 "$@"
}

# combine <name> <directory> [partition] [VAR=value ...]
combine() {
  local name="$1" dir="$2" partition="${3:-hosted}"
  shift 2
  [ $# -eq 0 ] || shift
  run "$name" NO_SORRY_COMBINE="$dir" NO_SORRY_PARTITION="$partition" "$@"
}

accepts() {  # name: the combiner printed the line of a full run, and nothing refused
  local name="$1"
  cases=$((cases + 1))
  if [ "$(cat "$work/rc-$name")" -ne 0 ]; then
    wrong "$name" "expected acceptance, was refused"
  fi
  if [ "$(tail -n 1 "$work/out-$name")" != "$full_line" ]; then
    wrong "$name" "accepted without ending in the line of a full run"
  fi
}

refuses() {  # name needle: the run failed, said the needle, and printed no line of a full run
  local name="$1" needle="$2"
  cases=$((cases + 1))
  if [ "$(cat "$work/rc-$name")" -eq 0 ]; then
    wrong "$name" "expected refusal containing '$needle', was accepted"
  fi
  if grep -qF -- "$full_line" "$work/out-$name"; then
    wrong "$name" "refused, but printed the line of a full run"
  fi
  if ! grep -qF -- "$needle" "$work/out-$name"; then
    wrong "$name" "refused, but without '$needle'"
  fi
}

ran_nothing() {  # name: no phase script was called (a refusal before anything ran)
  if grep -qv -- '--list$' "$work/calls-$1"; then
    wrong "$1" "refused, but only after calling $(grep -v -- '--list$' "$work/calls-$1" | head -n 1)"
  fi
}

# ---- the fixture against the script it copies -------------------------------------------------------------
# The line a full run prints names the number of phases the fixture's no-sorry.sh lists (read here, not written
# by hand, so that two branches that each add a phase do not change one line). So a phase dropped from both
# no-sorry.sh and the parts file is not caught here: run-proof-script-cases.sh holds that, since its honest run
# lists every stubbed script no-sorry.sh must call ("no-sorry honest: ... was not called") and requires the success
# line of the real check-translation-coverage.sh, which it does not stub. The stubs above are written by
# hand (and by `new-lifecycle-module.py scaffold`, for the script it adds): a called script added without one
# fails here, naming the edit, instead of later as a genuine part that fails.
(cd "$proofs" && "${clean_env[@]}" PATH="$work/bin:$PATH" STUB_CALLS="$work/calls-fixture-table" \
  NO_SORRY_LIST=1 bash scripts/no-sorry.sh) > "$work/fixture-table" 2>&1 \
  || wrong fixture-table "the fixture's no-sorry.sh did not list its phases"
cases=$((cases + 1))
listed="$(awk -F'\t' '$1 == "phase" { n++ } END { print n + 0 }' "$work/fixture-table")"
[ "$listed" -ge 10 ] || wrong fixture-phases "the fixture's no-sorry.sh lists $listed phases"
full_line="no-sorry: all $listed phases passed"
cases=$((cases + 1))
called="$(grep -vE '^[[:space:]]*#' "$proofs/scripts/no-sorry.sh" \
  | grep -oE '(python3|bash) scripts/[A-Za-z0-9_.-]+\.(py|sh)' | sed 's|.* scripts/||' | sort -u)"
for s in $called; do
  if [ ! -f "$proofs/scripts/$s" ]; then
    wrong fixture-stubs "no-sorry.sh calls scripts/$s, which has no stub here: add it to py_stubs (a .py) or to" \
      "the stub_sh loop (a .sh) in tooling/tests/run-no-sorry-parts-cases.sh"
  fi
done

# ---- the genuine sets ----------------------------------------------------------------------------------
hosted_parts="$(awk '$1 == "hosted" { sub(":", "", $2); print $2 }' "$proofs/scripts/no-sorry-parts.txt")"
[ "$(echo "$hosted_parts" | wc -l | tr -d ' ')" -ge 2 ] || { echo "control: no hosted partition" >&2; exit 2; }
genuine="$work/genuine"
mkdir -p "$genuine"
for p in $hosted_parts; do
  part "genuine-$p" "$p" "$genuine/translation-part-$p"
  cases=$((cases + 1))
  [ "$(cat "$work/rc-genuine-$p")" -eq 0 ] || wrong "genuine-$p" "a genuine part failed"
  grep -q "a part is not the gate" "$work/out-genuine-$p" || wrong "genuine-$p" "the part did not say it is not the gate"
  if grep -qF -- "$full_line" "$work/out-genuine-$p"; then wrong "genuine-$p" "a part printed the line of a full run"; fi
done
combine genuine "$genuine"
accepts genuine
grep -q "initial-dispatch: 10 controls, each once" "$work/out-genuine" || wrong genuine "no count of the sliced controls"

run whole
accepts whole

mkdir -p "$work/single"
part single-all all "$work/single/translation-part-all"
combine single "$work/single" single
accepts single

# A build that fails, in the whole run and in a part. A phase's body runs under the script's errexit, so the
# failed build pipeline stops the run there: nonzero, no final line, nothing after it called. The parent of a
# part still writes the manifest, with the child's status and only the phases that finished, and the combiner
# refuses it. This is what the call of each phase's function must keep: called in a condition, with `|| true`
# or under `set +e`, a body's failed command no longer stops it, and the build's scan reports it complete.
for pkg in translation tacenta-model; do
  run "build-fails-whole-$pkg" STUB_BUILD_FAIL="$pkg"
  cases=$((cases + 1))
  [ "$(cat "$work/rc-build-fails-whole-$pkg")" -ne 0 ] || wrong "build-fails-whole-$pkg" "a failed build exited 0"
  if grep -qF -- "$full_line" "$work/out-build-fails-whole-$pkg"; then
    wrong "build-fails-whole-$pkg" "a failed build printed the line of a full run"
  fi
  if grep -q '^check-kernel-replay-negative.sh' "$work/calls-build-fails-whole-$pkg"; then
    wrong "build-fails-whole-$pkg" "the run went on past the failed build"
  fi
done
part build-fails-part kernel "$work/build-fails-part" STUB_BUILD_FAIL=tacenta-model
cases=$((cases + 1))
[ "$(cat "$work/rc-build-fails-part")" -ne 0 ] || wrong build-fails-part "a part whose build failed exited 0"
if grep -q '^leanchecker ' "$work/calls-build-fails-part"; then
  wrong build-fails-part "the part went on past the failed build"
fi

# What the parts called, together: each phase script as often as the whole run calls it, the three
# builds in every part, and the dispatcher once per slice with its slice (the whole run calls it once,
# with no slice).
cases=$((cases + 1))
calls() {
  grep -v -e '^lake build ' -e '^check-initial-dispatch-negatives.py' "$@" \
    | sed 's/--compare-audit .*/--compare-audit LOG/' | sort
}
[ "$(grep -c '^check-initial-dispatch-negatives.py *$' "$work/calls-whole")" -eq 1 ] \
  || wrong calls "the whole run did not call the dispatcher once, unsliced"
calls "$work/calls-whole" > "$work/whole-calls"
cat $(for p in $hosted_parts; do echo "$work/calls-genuine-$p"; done) | calls > "$work/hosted-calls"
diff "$work/whole-calls" "$work/hosted-calls" > "$work/out-calls" || wrong calls "the parts called other scripts than the whole run"
for p in $hosted_parts; do
  [ "$(grep -c '^lake build ' "$work/calls-genuine-$p")" -eq 3 ] || wrong calls "part $p did not run the three builds"
done
slices="$(cat $(for p in $hosted_parts; do echo "$work/calls-genuine-$p"; done) \
  | grep '^check-initial-dispatch-negatives.py --slice' | awk '{ print $3 }' | sort | tr '\n' ' ')"
[ "$slices" = "0/8 1/8 2/8 3/8 4/8 5/8 6/8 7/8 " ] || wrong calls "the dispatcher ran the slices $slices"

# ---- refusals on a copy of the genuine set -------------------------------------------------------------
# copy <name>: a fresh copy of the genuine set, at $work/set-<name>.
copy() {
  rm -rf "$work/set-$1"
  cp -R "$genuine" "$work/set-$1"
}
# edit <name> <part> <python>: change one part's manifest (`m`) in that copy.
edit() {
  python3 - "$work/set-$1/translation-part-$2/part.json" "$3" <<'PY'
import json, sys
path, program = sys.argv[1], sys.argv[2]
m = json.load(open(path))
exec(program)
open(path, "w").write(json.dumps(m, indent=2) + "\n")
PY
}
refused_copy() {  # name needle: combine the copy and require the refusal
  combine "$1" "$work/set-$1"
  refuses "$1" "$2"
}

# The part whose build failed, above, is refused.
copy build-failed; rm -rf "$work/set-build-failed/translation-part-kernel"
cp -R "$work/build-fails-part" "$work/set-build-failed/translation-part-kernel"
refused_copy build-failed "exited with status"

first="$(echo "$hosted_parts" | head -n 1)"
copy missing; rm -rf "$work/set-missing/translation-part-$first"
refused_copy missing "holds 14 part directories, not the 15"

copy repeated; rm -rf "$work/set-repeated/translation-part-refuted"
cp -R "$work/set-repeated/translation-part-kernel" "$work/set-repeated/translation-part-kernel-again"
refused_copy repeated "are both part kernel"

copy one-more; cp -R "$work/single/translation-part-all" "$work/set-one-more/translation-part-all"
refused_copy one-more "holds 16 part directories"

copy other-partition; rm -rf "$work/set-other-partition/translation-part-refuted"
cp -R "$work/single/translation-part-all" "$work/set-other-partition/translation-part-all"
refused_copy other-partition "part 'all' of partition 'single' is not a part of partition hosted"

copy swapped
mv "$work/set-swapped/translation-part-braid/part.json" "$work/swapped-braid.json"
mv "$work/set-swapped/translation-part-decrypt/part.json" "$work/set-swapped/translation-part-braid/part.json"
mv "$work/swapped-braid.json" "$work/set-swapped/translation-part-decrypt/part.json"
refused_copy swapped "its log closes the phases"

copy relabelled; edit relabelled braid "m['part'] = 'responder'"
refused_copy relabelled "part responder (translation-part-braid) ran the phases"

copy relabelled-pair; edit relabelled-pair braid "m['part'] = 'decrypt'"; edit relabelled-pair decrypt "m['part'] = 'braid'"
refused_copy relabelled-pair "not the prelude and its own phases"

copy slices-swapped
mv "$work/set-slices-swapped/translation-part-dispatch-0/initial-dispatch" "$work/slice-0"
mv "$work/set-slices-swapped/translation-part-dispatch-1/initial-dispatch" "$work/set-slices-swapped/translation-part-dispatch-0/initial-dispatch"
mv "$work/slice-0" "$work/set-slices-swapped/translation-part-dispatch-1/initial-dispatch"
refused_copy slices-swapped "the result is of slice '1/8', not 0/8"

for f in tree script_sha256 parts_sha256; do
  copy "other-$f"; edit "other-$f" kernel "m['$f'] = 'f' * len(m['$f'])"
done
refused_copy other-tree "ran on tree ffff"
refused_copy other-script_sha256 "was run by a no-sorry.sh of sha256 ffff"
refused_copy other-parts_sha256 "was run with a parts file of sha256 ffff"
copy other-toolchain; edit other-toolchain kernel "m['toolchain'] = 'Lean (another version)'"
refused_copy other-toolchain "the parts ran on 2 toolchains"
copy no-toolchain; edit no-toolchain kernel "m['toolchain'] = ''"
refused_copy no-toolchain "toolchain is not a non-empty string"

# Another commit, made for the purpose: a part run on a later commit is refused by the combiner at the
# commit of the others.
"${gitc[@]}" commit -q --allow-empty -m later
part later-kernel kernel "$work/later-kernel"
git -C "$fx" checkout -q "$c0"
copy other-commit; rm -rf "$work/set-other-commit/translation-part-kernel"
cp -R "$work/later-kernel" "$work/set-other-commit/translation-part-kernel"
refused_copy other-commit "not $c0"
grep -q "part kernel (translation-part-kernel) ran on commit" "$work/out-other-commit" \
  || wrong other-commit "refused, but not for the part of the later commit"

# Another build cache, made for the purpose.
part cache-kernel kernel "$work/cache-kernel" NO_SORRY_BUILD_CACHE=lean-build-key-2
copy other-cache; rm -rf "$work/set-other-cache/translation-part-kernel"
cp -R "$work/cache-kernel" "$work/set-other-cache/translation-part-kernel"
refused_copy other-cache 'the parts restored 2 different build caches (lean-build-key-1, lean-build-key-2), as when main saved a newer one while the parts were starting; "Re-run failed jobs" combines the same parts again, so use "Re-run all jobs" or push again'

# A checkout with a change to a tracked file, made for the purpose.
echo "# changed" >> "$proofs/scripts/check-audit-reach.sh"
part dirty-kernel kernel "$work/dirty-kernel"
git -C "$fx" checkout -q -- tacenta-proofs/scripts/check-audit-reach.sh
copy changed-checkout; rm -rf "$work/set-changed-checkout/translation-part-kernel"
cp -R "$work/dirty-kernel" "$work/set-changed-checkout/translation-part-kernel"
refused_copy changed-checkout "ran in a checkout with changes to tracked files"

# A part whose phase fails, made for the purpose: the part fails, records the status, and is refused.
part failing-braid braid "$work/failing-braid" STUB_FAIL=check-atomicity-negatives.py
cases=$((cases + 1))
[ "$(cat "$work/rc-failing-braid")" -ne 0 ] || wrong failing-braid "a part whose phase failed exited 0"
grep -q "no-sorry: phase atomicity finished with status 1" "$work/failing-braid/part.log" \
  || wrong failing-braid "the log does not record the failed phase"
copy failed-phase; rm -rf "$work/set-failed-phase/translation-part-braid"
cp -R "$work/failing-braid" "$work/set-failed-phase/translation-part-braid"
refused_copy failed-phase "exited with status 1"

copy status-edited; edit status-edited braid "m['phases'][3]['status'] = 1"
refused_copy status-edited "finished with status 1"
copy status-boolean; edit status-boolean braid "m['phases'][3]['status'] = False"
refused_copy status-boolean "finished with status False"
copy exit-edited; edit exit-edited braid "m['exit'] = 1"
refused_copy exit-edited "exited with status 1"
copy exit-boolean; edit exit-boolean braid "m['exit'] = False"
refused_copy exit-boolean "exited with status False"
copy fewer-phases; edit fewer-phases braid "m['phases'] = [p for p in m['phases'] if p['id'] != 'repair']"
refused_copy fewer-phases "not the prelude and its own phases"
copy seam-named; edit seam-named braid "m['seam'] = ['BRAIDNEG_FILTER']"
refused_copy seam-named "ran with the test seam"
copy field-more; edit field-more braid "m['note'] = 'x'"
refused_copy field-more "does not hold exactly the fields"
copy not-ascii
python3 - "$work/set-not-ascii/translation-part-braid/part.json" <<'PY'
import json, sys
m = json.load(open(sys.argv[1]))
m["toolchain"] = "Lean (v\u00e9rsion stub)"
open(sys.argv[1], "w", encoding="utf-8").write(json.dumps(m, indent=2, ensure_ascii=False) + "\n")
PY
refused_copy not-ascii "holds a byte that is not printable ASCII or a newline"
copy result-cr; sed -i.bak 's/"slice"/"slice"\r/' "$work/set-result-cr/translation-part-dispatch-0/initial-dispatch/result.json"
rm -f "$work/set-result-cr/translation-part-dispatch-0/initial-dispatch/result.json.bak"
refused_copy result-cr "holds a byte that is not printable ASCII or a newline"
copy repeated-key
sed -i.bak 's/"exit": 0,/"exit": 0, "exit": 0,/' "$work/set-repeated-key/translation-part-braid/part.json"
rm -f "$work/set-repeated-key/translation-part-braid/part.json.bak"
refused_copy repeated-key "the key 'exit' is repeated"

# The log.
for kind in wrong-line error-line error-after-cr wrong-indented; do copy "$kind"; done
printf 'WRONG  something\n' >> "$work/set-wrong-line/translation-part-refuted/part.log"
printf '::error::something\n' >> "$work/set-error-line/translation-part-refuted/part.log"
printf 'progress\r::error::something\n' >> "$work/set-error-after-cr/translation-part-refuted/part.log"
printf '   wrong  something\n' >> "$work/set-wrong-indented/translation-part-refuted/part.log"
for kind in wrong-line error-line error-after-cr wrong-indented; do refused_copy "$kind" "failure line"; done
copy closing-missing
grep -v '^no-sorry: phase repair ' "$work/set-closing-missing/translation-part-braid/part.log" > "$work/log.tmp"
mv "$work/log.tmp" "$work/set-closing-missing/translation-part-braid/part.log"
refused_copy closing-missing "its log closes the phases"
copy closing-failed
sed -i.bak 's/^no-sorry: phase repair finished with status 0/no-sorry: phase repair finished with status 1/' \
  "$work/set-closing-failed/translation-part-braid/part.log"
rm -f "$work/set-closing-failed/translation-part-braid/part.log.bak"
refused_copy closing-failed "its log closes the phases"

# The dispatcher's slices.
d0="translation-part-dispatch-0/initial-dispatch"
result_edit() {  # name python: change the result file of slice 0 (`r`)
  copy "$1"
  python3 - "$work/set-$1/$d0/result.json" "$2" <<'PY'
import json, sys
path, program = sys.argv[1], sys.argv[2]
r = json.load(open(path))
exec(program)
open(path, "w").write(json.dumps(r, indent=2) + "\n")
PY
}
result_edit selected-other "r['selected'] = r['selected'][:-1]"
refused_copy selected-other "not the controls 0 modulo 8"
result_edit recorded-fewer "r['mutations'].pop(sorted(r['mutations'])[0])"
refused_copy recorded-fewer "not the 2 it selected"
result_edit control-accepted "r['mutations'][sorted(r['mutations'])[0]]['exit'] = 0"
refused_copy control-accepted "is not recorded as refused by Lean"
result_edit baseline-lost "r['baseline_exits'] = {}"
refused_copy baseline-lost "were not each accepted first"
result_edit named-controls "r['requested_mutations'] = ['control-0']"
refused_copy named-controls "named its controls"
copy log-lost; rm -f "$work/set-log-lost/$d0/control-0.log"
refused_copy log-lost "missing control-0.log"
copy file-more; : > "$work/set-file-more/$d0/notes.txt"
refused_copy file-more "extra notes.txt"
copy file-link; rm -f "$work/set-file-link/$d0/control-0.log"
ln -s "$genuine/$d0/control-0.log" "$work/set-file-link/$d0/control-0.log"
refused_copy file-link "control-0.log is not a regular file"
copy result-missing; rm -f "$work/set-result-missing/$d0/result.json"
refused_copy result-missing "result.json is not a regular file"

# Stray entries.
copy stray-file; : > "$work/set-stray-file/notes.txt"
refused_copy stray-file "notes.txt is not a part directory"
copy stray-link; ln -s "$genuine/translation-part-kernel" "$work/set-stray-link/translation-part-link"
refused_copy stray-link "translation-part-link is not a part directory"
copy part-file-more; : > "$work/set-part-file-more/translation-part-kernel/notes.txt"
refused_copy part-file-more "holds ['notes.txt', 'part.json', 'part.log']"
copy log-missing; rm -f "$work/set-log-missing/translation-part-kernel/part.log"
refused_copy log-missing "holds ['part.json'], not ['part.json', 'part.log']"
copy manifest-missing; rm -f "$work/set-manifest-missing/translation-part-kernel/part.json"
refused_copy manifest-missing "part.json is not a regular file"

# ---- the seam -------------------------------------------------------------------------------------------
for seam in REFUTED_RECORDS_BIN BRAIDNEG_FILTER HYPWIT_ROOT; do
  part "seam-$seam" braid "$work/seam-$seam" "$seam=x"
  refuses "seam-$seam" "$seam is set; it is a test seam"
  ran_nothing "seam-$seam"
  [ ! -e "$work/seam-$seam" ] || wrong "seam-$seam" "the refused part made its directory"
  run "seam-whole-$seam" "$seam="
  refuses "seam-whole-$seam" "$seam is set; it is a test seam"
  ran_nothing "seam-whole-$seam"
done

# ---- the variables --------------------------------------------------------------------------------------
part no-such-part no-such-part "$work/no-such-part"
refuses no-such-part "has no part 'no-such-part'"; ran_nothing no-such-part
run part-without-dir NO_SORRY_PART=kernel
refuses part-without-dir "NO_SORRY_PART needs NO_SORRY_PART_DIR"; ran_nothing part-without-dir
mkdir -p "$work/not-empty"; echo keep > "$work/not-empty/keep"
part not-empty kernel "$work/not-empty"
refuses not-empty "is not an empty directory"; ran_nothing not-empty
[ "$(cat "$work/not-empty/keep")" = keep ] || wrong not-empty "the existing file was not kept"
run dir-without-part NO_SORRY_PART_DIR="$work/x"
refuses dir-without-part "NO_SORRY_PART_DIR is set without NO_SORRY_PART"; ran_nothing dir-without-part
run part-and-combine NO_SORRY_PART=kernel NO_SORRY_PART_DIR="$work/y" NO_SORRY_COMBINE="$genuine"
refuses part-and-combine "three modes; set one"
run combine-without-partition NO_SORRY_COMBINE="$genuine"
refuses combine-without-partition "NO_SORRY_COMBINE needs NO_SORRY_PARTITION"
run partition-without-combine NO_SORRY_PARTITION=hosted
refuses partition-without-combine "NO_SORRY_PARTITION is set without NO_SORRY_COMBINE"
combine no-such-partition "$genuine" no-such-partition
refuses no-such-partition "has no partition 'no-such-partition'"
combine hosted-as-single "$genuine" single
refuses hosted-as-single "holds 15 part directories, not the 1 of partition single"
run list-other NO_SORRY_LIST=yes
refuses list-other "NO_SORRY_LIST takes the value 1"
run run-without-part NO_SORRY_PART_RUN="$work/z"
refuses run-without-part "NO_SORRY_PART_RUN is set without NO_SORRY_PART"

# ---- the parts file -------------------------------------------------------------------------------------
# A phase the script gains and the file does not assign, made for the purpose: every part refuses before
# it runs anything, and so does the combiner.
python3 - "$proofs/scripts/no-sorry.sh" <<'PY'
import sys
path = sys.argv[1]
text = open(path).read()
anchor = '  run_phase kernel-replay-negative plain'
assert text.count(anchor) == 1
text = text.replace(anchor, '  run_phase new-phase plain "a new phase" phase_kernel_replay_negative\n' + anchor)
open(path, "w").write(text)
PY
"${gitc[@]}" commit -q -a -m "a new phase"
part unassigned kernel "$work/unassigned"
refuses unassigned "partition hosted: phase new-phase is in no part"; ran_nothing unassigned
combine unassigned-combine "$genuine"
refuses unassigned-combine "partition hosted: phase new-phase is in no part"
git -C "$fx" checkout -q "$c0"

(cd "$proofs" && "${clean_env[@]}" PATH="$work/bin:$PATH" NO_SORRY_LIST=1 bash scripts/no-sorry.sh) > "$work/table"
# The helper is named through a variable: the gate inventory reads a call by its path as the step that runs
# it, and this runner is not where the combiner gives its verdict.
fixture_helper="$proofs/scripts/no-sorry-parts.py"
real_helper="$scripts/no-sorry-parts.py"
parts_case() {  # name needle python-edit-of-lines(l): resolve with an edited copy of the parts file
  local name="$1" needle="$2"
  python3 - "$proofs/scripts/no-sorry-parts.txt" "$work/parts-$name" "$3" <<'PY'
import sys
source, target, program = sys.argv[1:]
l = open(source).read().split("\n")
exec(program)
open(target, "w").write("\n".join(l))
PY
  set +e
  python3 "$fixture_helper" resolve --table "$work/table" --parts "$work/parts-$name" \
    --part kernel > "$work/out-$name" 2>&1
  echo $? > "$work/rc-$name"
  set -e
  refuses "$name" "$needle"
}
cases=$((cases + 1))
python3 "$fixture_helper" resolve --table "$work/table" \
  --parts "$proofs/scripts/no-sorry-parts.txt" --part kernel > "$work/out-parts-unchanged" 2>&1 \
  || wrong parts-unchanged "the committed parts file was refused"
parts_case phase-twice "partition hosted: phase repair is in parts" \
  "i = next(i for i, x in enumerate(l) if x.startswith('hosted kernel:')); l[i] += ' repair'"
parts_case phase-dropped "partition hosted: phase repair is in no part" \
  "l.remove('  repair')"
parts_case slice-missing "slice 7/8 of initial-dispatch is in no part" \
  "l[:] = [x for x in l if not x.startswith('hosted dispatch-7:')]"
parts_case slice-twice "slice 6/8 of initial-dispatch is in parts dispatch-6, dispatch-8" \
  "i = next(i for i, x in enumerate(l) if x.startswith('hosted dispatch-7:')); l.insert(i + 1, 'hosted dispatch-8: initial-dispatch@6/8')"
parts_case slice-replaced "slice 6/8 of initial-dispatch is in parts dispatch-6, dispatch-7" \
  "i = next(i for i, x in enumerate(l) if x.startswith('hosted dispatch-7:')); l[i] = 'hosted dispatch-7: initial-dispatch@6/8'"
parts_case sliced-two-ways "is sliced 8 and 9 ways" \
  "i = next(i for i, x in enumerate(l) if x.startswith('hosted dispatch-7:')); l[i] = 'hosted dispatch-7: initial-dispatch@7/9'"
parts_case sliced-and-whole "initial-dispatch is in part kernel and sliced in" \
  "i = next(i for i, x in enumerate(l) if x.startswith('hosted kernel:')); l[i] += ' initial-dispatch'"
parts_case plain-sliced "slices repair, which the script does not slice" \
  "l[l.index('  repair')] = '  repair@0/2'"
parts_case prelude-named "names build-model, a prelude phase every part runs" \
  "i = next(i for i, x in enumerate(l) if x.startswith('hosted braid:')); l[i] += ' build-model'"
parts_case unknown-phase "names no-such-phase, which the script does not run" \
  "i = next(i for i, x in enumerate(l) if x.startswith('hosted braid:')); l[i] += ' no-such-phase'"
parts_case too-many-slices "has 10 controls, too few for 11 slices" \
  "l[:] = [x for x in l if not x.startswith('hosted dispatch-')] + ['hosted dispatch-%d: initial-dispatch@%d/11' % (k, k) for k in range(11)]"
parts_case one-slice "is not a slice k/S with 0 <= k < S and S >= 2" \
  "l[:] = [x for x in l if not x.startswith('hosted dispatch-')] + ['hosted dispatch-0: initial-dispatch@0/1']"
parts_case part-twice "part kernel is named twice" \
  "l.append('single kernel: *')"
parts_case malformed "is not \`<partition> <part>: <phase>...\`" \
  "l.append('hosted Kernel2 repair')"
parts_case carriage-return "holds a carriage return" \
  "l[-2] = l[-2] + '\\r'"
parts_case named-twice-in-part "names repair twice" \
  "i = next(i for i, x in enumerate(l) if x.startswith('hosted braid:')); l[i] += ' repair'"
# A part over several lines (its header line, then one indented line per phase) is the same part as its one-line
# form, and a continuation line belongs to the line directly above it.
parts_case continuation-after-blank "is a continuation line that does not follow a part's line directly" \
  "i = l.index('  repair'); l.insert(i, '')"
parts_case continuation-after-comment "is a continuation line that does not follow a part's line directly" \
  "i = l.index('  repair'); l.insert(i, '# a comment')"
parts_case continuation-first "is a continuation line that does not follow a part's line directly" \
  "l.insert(0, '  repair')"
parts_case empty-part "part extra names no phase" \
  "l.insert(l.index('single all: *'), 'hosted extra:')"
parts_case header-without-phase "part braid names no phase" \
  "i = next(i for i, x in enumerate(l) if x.startswith('hosted braid:')); j = i + 1
while l[j].startswith('  '): del l[j]"
parts_case star-and-phase "'*' is not a phase or" \
  "l.insert(l.index('single all: *') + 1, '  repair')"
cases=$((cases + 1))
python3 - "$proofs/scripts/no-sorry-parts.txt" "$work/parts-one-line" <<'PY'
import sys
out = []
for line in open(sys.argv[1]).read().split("\n"):
    if line.startswith("  "):
        out[-1] += " " + line.strip()
    else:
        out.append(line)
open(sys.argv[2], "w").write("\n".join(out))
PY
for p in $(awk '/^[a-z]/ { sub(":", "", $2); print $2 }' "$proofs/scripts/no-sorry-parts.txt"); do
  python3 "$fixture_helper" resolve --table "$work/table" --parts "$work/parts-one-line" --part "$p" \
    > "$work/out-one-line-$p" 2>&1 || wrong one-line-form "the one-line form of the parts file was refused for $p"
  python3 "$fixture_helper" resolve --table "$work/table" --parts "$proofs/scripts/no-sorry-parts.txt" --part "$p" \
    > "$work/out-lines-$p" 2>&1 || wrong one-line-form "the committed parts file was refused for $p"
  cmp -s "$work/out-one-line-$p" "$work/out-lines-$p" \
    || wrong one-line-form "part $p reads differently in its one-line form"
done

# ---- the real script and parts file, without Lean ---------------------------------------------------
# The committed parts file covers the committed script: every part of every partition resolves against the
# phases the real no-sorry.sh lists (which asks the real dispatcher for its controls, and runs nothing).
(cd "$root/tacenta-proofs" && "${clean_env[@]}" NO_SORRY_LIST=1 bash scripts/no-sorry.sh) > "$work/real-table"
for p in $(awk '/^[a-z]/ { sub(":", "", $2); print $2 }' "$scripts/no-sorry-parts.txt"); do
  cases=$((cases + 1))
  python3 "$real_helper" resolve --table "$work/real-table" --parts "$scripts/no-sorry-parts.txt" \
    --part "$p" > "$work/out-real-$p" 2>&1 || wrong "real-$p" "the committed parts file does not resolve part $p"
done
# The real dispatcher's selection: the slices of the hosted partition select every control once.
python3 - "$work/real-table" <<'PY2' > "$work/out-real-slices" 2>&1 || wrong real-slices "the hosted slices do not cover the dispatcher"
import sys
units = [l.split("\t")[2] for l in open(sys.argv[1]).read().split("\n") if l.startswith("unit\tinitial-dispatch\t")]
picked = sorted(u for k in range(8) for i, u in enumerate(units) if i % 8 == k)
assert len(units) >= 8 and picked == sorted(units) and len(set(units)) == len(units), (len(units), picked)
PY2
cases=$((cases + 1))
dispatch_refuses() {  # name needle args...: the real dispatcher refuses an option before it runs Lean
  local name="$1" needle="$2"
  shift 2
  set +e
  (cd "$work" && python3 "$scripts/check-initial-dispatch-negatives.py" "$@") > "$work/out-$name" 2>&1
  echo $? > "$work/rc-$name"
  set -e
  refuses "$name" "$needle"
}
dispatch_refuses dispatch-slice-out-of-range "--slice must be k/S with 0 <= k < S, not '8/8'" --slice 8/8
dispatch_refuses dispatch-slice-zero "--slice must be k/S with 0 <= k < S, not '0/0'" --slice 0/0
dispatch_refuses dispatch-slice-digit "--slice must be k/S with 0 <= k < S" --slice "$(printf '\xd9\xa0')/8"
dispatch_refuses dispatch-slice-and-mutation "--mutation and --slice select controls two ways" \
  --slice 0/8 --mutation bypass-identity
dispatch_refuses dispatch-list-and-slice "--list takes no other option" --list --slice 0/8
dispatch_refuses dispatch-empty-slice "selects no control of the" --slice 60/61
# The real dispatcher's slice of its own list: for each S up to the number of controls and each k, the
# controls k modulo S, in order, so that the slices of one S select every control once.
cases=$((cases + 1))
python3 -B - "$scripts/check-initial-dispatch-negatives.py" > "$work/out-dispatch-select" 2>&1 <<'PY2' \
  || wrong dispatch-select "the real dispatcher's slices are not the controls k modulo S"
import importlib.util, sys
spec = importlib.util.spec_from_file_location("dispatch", sys.argv[1])
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)
table = module.mutant_table()
names = [m[0] for m in table]
for count in range(1, len(names) + 1):
    picked = []
    for k in range(count):
        chosen = [m[0] for m in module.select_slice(table, k, count)]
        assert chosen == [n for i, n in enumerate(names) if i % count == k], (k, count, chosen)
        picked += chosen
    assert sorted(picked) == sorted(names) and len(picked) == len(names), count
PY2

echo "no-sorry-parts-cases: $cases cases (the genuine hosted and single sets and the whole run, what the parts called; a part missing, repeated, relabelled or of another partition, commit, tree, script, parts file, cache, toolchain or checkout; a failed phase, a failure line; the dispatcher's slices; the seam; the variables; the parts file; the committed parts file against the committed script, the real dispatcher's options) gave the expected result"
