#!/usr/bin/env bash
# Hold the control-count record of the lifecycle negatives scripts, and their shared label check, to planted faults.
#
#   bash tooling/tests/run-check-negatives-control-counts-cases.sh
#
# check_complete, the shared completeness check each script's main calls, runs second, on simulated runs (no
# Lean runs here): a whole run accepted; a slice, a `continue`, a skipped emptied-proof run, baseline or
# projection record, and a fabricated run with no Lean run behind it, refused.
#
# Part 1 (run third), the count gate (`tacenta-proofs/scripts/check-negatives-control-counts.py`). Each case copies the gate,
# its record and the five negatives scripts into a fixture directory, changes one thing and runs the real gate
# there: the unmodified copy is accepted; a control deleted with its label, a control relabelled, a control added,
# a baseline added, the record missing a script or naming one too many, a record entry without a class, a sixth
# script defining `check_labels` and not recorded, and one copy of a shared helper changed are each refused for
# their own reason; a control deleted with its label and the record edited in the same change is accepted. The
# scaffold's template (`templates/lifecycle-negatives.py.in`) is held too: a helper of the template changed, its
# `main` without the completeness call or the projection record, a template that rebinds a name through
# `globals()`, and the template missing are each refused.
#
# Part 2 (run first), the shared `check_labels` of the five scripts, on the real module texts: a projection whose refusal
# list also names a declaration that is not a composing theorem is refused, in each script that has a projection
# (the reply script has none; the count gate holds its copy to the same text as the others), and the unmodified
# labels are accepted. Needs no Lean toolchain.
set -euo pipefail

here="$(cd "$(dirname "$0")" && pwd)"
root="$(cd "$here/../.." && pwd)"
scripts="$root/tacenta-proofs/scripts"
work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT
cases=0
five=(check-responder-successor-negatives.py check-responder-reply-negatives.py
  check-responder-reply-receipt-negatives.py check-send-preservation-negatives.py
  check-initiator-second-send-negatives.py)

make_case() {
  local dst="$work/$1"
  mkdir -p "$dst"
  cp "$scripts/check-negatives-control-counts.py" "$scripts/negatives-control-counts.json" "$dst/"
  mkdir -p "$dst/templates"
  cp "$scripts/templates/lifecycle-negatives.py.in" "$dst/templates/"
  for s in "${five[@]}"; do cp "$scripts/$s" "$dst/"; done
}

edit() {  # case file old new [count]
  python3 -B - "$work/$1/$2" "$3" "$4" "${5:-1}" <<'PY'
import pathlib, sys
path, old, new, count = pathlib.Path(sys.argv[1]), sys.argv[2], sys.argv[3], int(sys.argv[4])
text = path.read_text()
assert text.count(old) == count, (path.name, old, text.count(old))
path.write_text(text.replace(old, new))
PY
}

run_gate() {
  python3 -B "$work/$1/check-negatives-control-counts.py" 2>&1
}

expect_pass() {
  local out rc
  set +e
  out="$(run_gate "$1")"
  rc=$?
  set -e
  cases=$((cases + 1))
  if [ "$rc" -ne 0 ]; then
    echo "WRONG  $1: expected acceptance, got exit $rc" >&2
    printf '  %s\n' "$out" >&2
    exit 1
  fi
}

expect_fail() {
  local out rc
  set +e
  out="$(run_gate "$1")"
  rc=$?
  set -e
  cases=$((cases + 1))
  if [ "$rc" -eq 0 ]; then
    echo "WRONG  $1: expected refusal ($2), was accepted" >&2
    exit 1
  fi
  if ! grep -F -- "$2" >/dev/null <<<"$out"; then
    echo "WRONG  $1: refused, but not for '$2':" >&2
    printf '  %s\n' "$out" >&2
    exit 1
  fi
}

# Part 2 runs first, so a copy of check_labels that lost the rule fails its own case before the gate's
# identity check sees the copies differ: the shared check_labels on the real module texts.
for s in "${five[@]}"; do
  set +e
  out="$(python3 -B - "$scripts/$s" <<'PY' 2>&1
import importlib.util, sys
spec = importlib.util.spec_from_file_location("negatives", sys.argv[1])
m = importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)
text = m.without_pins(m.MODULE.read_text(), m.MODULE)
m.check_labels(text)
if not m.PROJECTION:
    print("NO-PROJECTION")
    sys.exit(0)
name = sorted(m.PROJECTION)[0]
leaf = next(d for mutant in m.MUTANTS if not isinstance(mutant[4], tuple) for d in mutant[4] if d not in m.COMPOSING)
m.MUTANTS = [mutant[:4] + (list(mutant[4]) + [leaf],) if mutant[1] == name else mutant for mutant in m.MUTANTS]
try:
    m.check_labels(text)
except SystemExit as refusal:
    print(refusal)
    sys.exit(3)
print("ACCEPTED")
PY
)"
  rc=$?
  set -e
  cases=$((cases + 1))
  if [ "$rc" -eq 0 ] && [ "$out" = NO-PROJECTION ] && [ "$s" = check-responder-reply-negatives.py ]; then
    continue
  fi
  if [ "$rc" -ne 3 ] || ! grep -F -- "which is not a composing proof" >/dev/null <<<"$out"; then
    echo "WRONG  projection-with-a-non-composing-place:$s: expected the label check to refuse it, got exit $rc" >&2
    printf '  %s\n' "$out" >&2
    exit 1
  fi
done


# check_complete itself, on SIMULATED runs: no Lean runs here. For each script, the results and the Lean
# exit statuses (RUNS) that `main` would leave after a whole run are built from its lists and accepted; then
# those of a run over a slice of MUTANTS, of one that skipped a leaf control with `continue`, of one that
# skipped an inside control's emptied-proof run, a baseline or a projection's record, and results with no
# Lean run behind them (a fabricated run), and a whole run whose results lost a control, are each refused,
# each for its own reason.
set +e
out="$(python3 -B - "$scripts" "${five[@]}" <<'PY' 2>&1
import ast, importlib.util, sys
scripts, names = sys.argv[1], sys.argv[2:]
ran = 0
for script in names:
    path = f"{scripts}/{script}"
    spec = importlib.util.spec_from_file_location("negatives", path)
    m = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(m)
    main = next(n for n in ast.parse(open(path).read()).body if isinstance(n, ast.FunctionDef) and n.name == "main")
    keys = next(n.value.keys for n in ast.walk(main) if isinstance(n, ast.Assign)
                and isinstance(n.value, ast.Dict) and any(getattr(t, "id", "") == "sources" for t in n.targets))
    sources = {k.value: None for k in keys}

    def run(mutants, skip_inside=False, skip_projection=False, baselines=None, lean=True):
        """The results and RUNS a run over `mutants` would leave."""
        accepted = list(sources) if baselines is None else baselines
        runs = [(b, 0) for b in accepted]
        rejected = {}
        for label, name, _, _, _ in mutants:
            r = {"exit": 1}
            runs.append((name, 1))
            if name in m.INSIDE and not skip_inside:
                r["inside"] = m.INSIDE[name]
                runs.append((name + "-emptied", 0))
            if name in m.PROJECTION and not skip_projection:
                r["projection_of"] = m.PROJECTION[name]
            if name in m.STATEMENT_SHAPE:
                r["projects"] = m.STATEMENT_SHAPE[name]
                runs.append((name + "-projected", 1))
            rejected[f"{label}/{name}"] = r
        return {"accepted": accepted, "rejected": rejected}, (runs if lean else [])

    results, runs = run(m.MUTANTS)
    m.RUNS[:] = runs
    m.check_complete(results, sources)
    ran += 1
    leaf = next(x for x in m.MUTANTS if x[1] not in m.INSIDE and x[1] not in m.PROJECTION
                and x[1] not in m.STATEMENT_SHAPE)
    trials = [("slice", run(m.MUTANTS[:-1]), "INCOMPLETE RUN"),
              ("continue", run([x for x in m.MUTANTS if x is not leaf]), "INCOMPLETE RUN"),
              ("emptied-run-skipped", run(m.MUTANTS, skip_inside=True), "emptied-proof run of an inside control"),
              ("baseline-skipped", run(m.MUTANTS, baselines=list(sources)[:-1]), "unmodified copies accepted"),
              ("fabricated", run(m.MUTANTS, lean=False), "Lean ran 0 accepting and 0 refusing times"),
              ("result-dropped", (run(m.MUTANTS[:-1])[0], run(m.MUTANTS)[1]), "controls refused, expected")]
    if m.PROJECTION:
        trials.append(("projection-unrecorded", run(m.MUTANTS, skip_projection=True), "place of a projection"))
    for what, (results, runs), reason in trials:
        m.RUNS[:] = runs
        try:
            m.check_complete(results, sources)
        except SystemExit as refusal:
            if "INCOMPLETE RUN" not in str(refusal) or reason not in str(refusal):
                sys.exit(f"WRONG  check-complete-{what}:{script}: refused, but not for '{reason}': {refusal}")
            ran += 1
            continue
        sys.exit(f"WRONG  check-complete-{what}:{script}: an incomplete run was accepted")
print(ran)
PY
)"
rc=$?
set -e
if [ "$rc" -ne 0 ]; then
  printf '%s\n' "$out" >&2
  exit 1
fi
cases=$((cases + out))

make_case unmodified
expect_pass unmodified

# A control deleted together with its label: the script's own start-up check has nothing to say about it.
sp=check-send-preservation-negatives.py
budget_label="    'budget-claimed-unspent': 'encrypt_keeps_invariant_no_draw',
"
budget_entry="$(python3 -B - "$scripts/$sp" <<'PY'
import sys
text = open(sys.argv[1]).read()
start = text.index("    ('module', 'budget-claimed-unspent',\n")
end = text.index("    ('module', ", start + 1)
print(text[start:end], end="")
PY
)"
make_case control-deleted-with-its-label
edit control-deleted-with-its-label "$sp" "$budget_entry" ""
edit control-deleted-with-its-label "$sp" "$budget_label" ""
expect_fail control-deleted-with-its-label "$sp has 6 inside control(s) and negatives-control-counts.json records 7"

# The same deletion with the record edited in the same change is accepted: the diff of the record shows it.
make_case control-deleted-and-recorded
edit control-deleted-and-recorded "$sp" "$budget_entry" ""
edit control-deleted-and-recorded "$sp" "$budget_label" ""
edit control-deleted-and-recorded negatives-control-counts.json \
  '"check-send-preservation-negatives.py": {"inside": 7,' '"check-send-preservation-negatives.py": {"inside": 6,'
expect_pass control-deleted-and-recorded

# A leaf control deleted (it carries no label).
leaf_entry="$(python3 -B - "$scripts/$sp" <<'PY'
import sys
text = open(sys.argv[1]).read()
start = text.index("    ('module', 'next-chunk-claimed-to-change-the-codewords',\n")
end = text.index("    ('module', ", start + 1)
print(text[start:end], end="")
PY
)"
make_case leaf-control-deleted
edit leaf-control-deleted "$sp" "$leaf_entry" ""
expect_fail leaf-control-deleted "$sp has 6 leaf control(s) and negatives-control-counts.json records 7"

# A control moved from one label class to another.
make_case control-relabelled
edit control-relabelled "$sp" "$budget_label" ""
edit control-relabelled "$sp" "PROJECTION = {
" "PROJECTION = {
    'budget-claimed-unspent': 'encrypt_keeps_invariant_no_draw',
"
expect_fail control-relabelled "$sp has 3 projection control(s) and negatives-control-counts.json records 2"

# A control added without editing the record.
make_case control-added
edit control-added "$sp" "$leaf_entry" "$leaf_entry${leaf_entry/next-chunk-claimed-to-change-the-codewords/next-chunk-claimed-again}"
expect_fail control-added "$sp has 8 leaf control(s) and negatives-control-counts.json records 7"

# A baseline copy added.
make_case baseline-added
edit baseline-added "$sp" "        'pinned': bridge,
" "        'pinned': bridge,
        'extra': bridge,
"
expect_fail baseline-added "$sp has 4 baselines control(s) and negatives-control-counts.json records 3"

# The record leaves a script out, or names one that is not here.
make_case record-misses-a-script
python3 -B - "$work/record-misses-a-script/negatives-control-counts.json" <<'PY'
import json, sys
path = sys.argv[1]
record = json.load(open(path))
del record["scripts"]["check-responder-reply-negatives.py"]
json.dump(record, open(path, "w"))
PY
expect_fail record-misses-a-script "check-responder-reply-negatives.py carries the shared check_labels and is not in negatives-control-counts.json"

make_case record-names-another-script
python3 -B - "$work/record-names-another-script/negatives-control-counts.json" <<'PY'
import json, sys
path = sys.argv[1]
record = json.load(open(path))
record["scripts"]["check-gone-negatives.py"] = dict(record["scripts"]["check-responder-reply-negatives.py"])
json.dump(record, open(path, "w"))
PY
expect_fail record-names-another-script "lists check-gone-negatives.py, which is not a script here carrying check_labels"

make_case record-entry-without-a-class
python3 -B - "$work/record-entry-without-a-class/negatives-control-counts.json" <<'PY'
import json, sys
path = sys.argv[1]
record = json.load(open(path))
del record["scripts"]["check-responder-reply-negatives.py"]["leaf"]
json.dump(record, open(path, "w"))
PY
expect_fail record-entry-without-a-class "the entry of check-responder-reply-negatives.py must give exactly the integer counts"

make_case record-entry-with-another-class
python3 -B - "$work/record-entry-with-another-class/negatives-control-counts.json" <<'PY'
import json, sys
path = sys.argv[1]
record = json.load(open(path))
record["scripts"]["check-responder-reply-negatives.py"]["total"] = 16
json.dump(record, open(path, "w"))
PY
expect_fail record-entry-with-another-class "the entry of check-responder-reply-negatives.py must give exactly the integer counts"

make_case record-unreadable
printf '{"scripts": ' > "$work/record-unreadable/negatives-control-counts.json"
expect_fail record-unreadable "negatives-control-counts.json cannot be read as a record of scripts"

# A sixth script that carries the shared label check is not left out of the record.
make_case sixth-script-unrecorded
cp "$work/sixth-script-unrecorded/$sp" "$work/sixth-script-unrecorded/check-new-step-negatives.py"
expect_fail sixth-script-unrecorded "check-new-step-negatives.py carries the shared check_labels and is not in negatives-control-counts.json"

# One copy of a shared helper changed.
make_case helper-copy-differs
edit helper-copy-differs check-initiator-second-send-negatives.py \
  "        others = [d for d in places if d not in COMPOSING]" \
  "        others = [d for d in places if d not in COMPOSING and False]"
expect_fail helper-copy-differs "check-initiator-second-send-negatives.py's copy of the shared check_labels differs from"

# Ways around the one-text check: a decorator, a second binding of a shared name of any kind, a name
# rebound through globals(), and a sixth script that carries check_labels under another spelling.
make_case decorated-helper
edit decorated-helper "$sp" $'\ndef check_labels(text):\n' $'\n@(lambda f: (lambda text: None))\ndef check_labels(text):\n'
expect_fail decorated-helper "$sp's copy of the shared check_labels differs"
make_case annotated-rebinding
edit annotated-rebinding "$sp" $'\n\ndef main():\n' $'\nNOT_A_REFUSAL: tuple = NOT_A_REFUSAL + (\'error\',)\n\n\ndef main():\n'
expect_fail annotated-rebinding "$sp binds the shared NOT_A_REFUSAL 2 time(s)"
make_case augmented-rebinding
edit augmented-rebinding "$sp" $'\n\ndef main():\n' $'\nTIMEOUT += (\'error\',)\n\n\ndef main():\n'
expect_fail augmented-rebinding "$sp binds the shared TIMEOUT 2 time(s)"
make_case global-rebinding-in-main
edit global-rebinding-in-main "$sp" $'\ndef main():\n' $'\ndef main():\n    global check_refused\n    check_refused = lambda *a, **k: None\n'
expect_fail global-rebinding-in-main "$sp binds the shared check_refused 3 time(s)"
make_case local-shadow-in-main
edit local-shadow-in-main "$sp" $'\ndef main():\n' $'\ndef main():\n    check_refused = lambda *a, **k: None\n'
expect_fail local-shadow-in-main "$sp binds the shared check_refused 2 time(s)"
make_case parameter-shadow
edit parameter-shadow "$sp" $'\ndef main():\n' $'\ndef main(check_refused=lambda *a, **k: None):\n'
expect_fail parameter-shadow "$sp binds the shared check_refused 2 time(s)"
make_case rebinding-through-globals
edit rebinding-through-globals "$sp" $'\ndef main():\n' $'\ndef main():\n    globals()[\'check_refused\'] = print\n'
expect_fail rebinding-through-globals "$sp uses globals"
for shape in $'def check_labels (text):\n    return None\n' $'from negatives import check_labels\n' $'import negatives\nnegatives.check_labels(\'\')\n'; do
  make_case sixth-script-spelling
  printf '%s' "$shape" > "$work/sixth-script-spelling/check-other-negatives.py"
  expect_fail sixth-script-spelling "check-other-negatives.py carries the shared check_labels and is not in"
done

# A main that does not run what the record counts: a stub, a missing or guarded completeness check,
# an early exit, a return, and another end of the script.
make_case stub-main
edit stub-main "$sp" $'\ndef main():\n' $'\ndef main():\n    sources = {}\n\n\ndef old_main():\n'
expect_fail stub-main "$sp has 0 baselines control(s)"
make_case completeness-check-removed
edit completeness-check-removed "$sp" $'    check_complete(results, sources)\n' ''
expect_fail completeness-check-removed "$sp: \`main\` must call \`check_complete(results, sources)\` exactly once"
make_case completeness-check-guarded
edit completeness-check-guarded "$sp" $'    check_complete(results, sources)\n' $'    try:\n        check_complete(results, sources)\n    except SystemExit:\n        pass\n'
expect_fail completeness-check-guarded "$sp: \`main\` must call \`check_complete(results, sources)\` exactly once"
make_case early-exit
edit early-exit "$sp" $'    check_complete(results, sources)\n' $'    sys.exit(0)\n    check_complete(results, sources)\n'
expect_fail early-exit "$sp: \`main\` calls an exit"
make_case early-return
edit early-return "$sp" $'    check_complete(results, sources)\n' $'    if results:\n        return 0\n    check_complete(results, sources)\n'
expect_fail early-return "$sp: \`main\` holds a \`return\`"
make_case other-end
edit other-end "$sp" $'    sys.exit(main())\n' $'    main()\n    sys.exit(0)\n'
expect_fail other-end "$sp: the script must end its run with exactly"

# Edits that skip controls without a binding the one-text check reads: a second binding of main, MUTANTS or
# INSIDE, a global, a raise that ends main early, a function's code replaced, a shared list changed in place,
# and the block that records a projection's place removed.
make_case main-rebound-to-a-lambda
edit main-rebound-to-a-lambda "$sp" $'\n\nif __name__ == \'__main__\':\n' $'\n\nmain = lambda: 0\n\n\nif __name__ == \'__main__\':\n'
expect_fail main-rebound-to-a-lambda "$sp binds main 2 time(s)"
make_case main-redefined-in-an-if
edit main-redefined-in-an-if "$sp" $'\n\nif __name__ == \'__main__\':\n' $'\n\nif True:\n    def main():\n        pass\n\n\nif __name__ == \'__main__\':\n'
expect_fail main-redefined-in-an-if "$sp binds main 2 time(s)"
make_case global-of-another-name
edit global-of-another-name "$sp" $'\ndef main():\n' $'\ndef main():\n    global ROOT\n    ROOT = ROOT.parent\n'
expect_fail global-of-another-name "$sp: a \`global ROOT\` statement rebinds a module-level name"
make_case raise-ends-main
edit raise-ends-main "$sp" $'\ndef main():\n' $'\ndef main():\n    raise SystemExit(0)\n'
expect_fail raise-ends-main "$sp: \`main\` raises \`raise SystemExit(0)\`"
make_case global-mutants-shortened
edit global-mutants-shortened "$sp" $'\ndef main():\n' $'\ndef main():\n    global MUTANTS\n    MUTANTS = [m for m in MUTANTS if m[1] in INSIDE]\n'
expect_fail global-mutants-shortened "$sp binds MUTANTS 3 time(s)"
make_case function-code-replaced
edit function-code-replaced "$sp" $'\n\ndef main():\n' $'\ncheck_complete.__code__ = (lambda results, sources: None).__code__\n\n\ndef main():\n'
expect_fail function-code-replaced "$sp uses __code__"
make_case runs-overwritten
edit runs-overwritten "$sp" $'    check_complete(results, sources)\n' $'    RUNS[:] = RUNS * 2\n    check_complete(results, sources)\n'
expect_fail runs-overwritten "$sp: \`RUNS[:]\` is assigned or deleted through the module-level name RUNS"
make_case shared-list-cleared
edit shared-list-cleared "$sp" $'\ndef main():\n' $'\ndef main():\n    INSIDE.clear()\n'
expect_fail shared-list-cleared "$sp: \`INSIDE.clear()\` changes the module-level INSIDE in place"
make_case mutants-popped
edit mutants-popped "$sp" $'\n\ndef main():\n' $'\nMUTANTS.pop()\n\n\ndef main():\n'
expect_fail mutants-popped "$sp: \`MUTANTS.pop()\` changes the module-level MUTANTS in place"
make_case label-deleted-by-subscript
edit label-deleted-by-subscript "$sp" $'\n\ndef main():\n' $'\ndel INSIDE[\'budget-claimed-unspent\']\n\n\ndef main():\n'
expect_fail label-deleted-by-subscript "is assigned or deleted through the module-level name INSIDE"
ss=check-initiator-second-send-negatives.py
make_case projection-record-removed
python3 -B - "$work/projection-record-removed/$ss" <<'PY'
import sys
path = sys.argv[1]
text = open(path).read()
start = text.index("            if name in PROJECTION:\n")
end = text.index("            if name in STATEMENT_SHAPE:\n", start)
open(path, "w").write(text[:start] + text[end:])
PY
expect_fail projection-record-removed "$ss: \`main\` never records \`projection_of\` for a control"

# The scaffold's template is held to the shared text and to the rules for `main`, so a script generated from it
# starts at the standard of the others.
tp=templates/lifecycle-negatives.py.in
make_case template-helper-differs
edit template-helper-differs "$tp" "'unknown namespace', 'does not contain')" "'unknown namespace')"
expect_fail template-helper-differs "$tp's copy of the shared NOT_A_REFUSAL differs from the copy in 5 of the other scripts"
make_case template-without-completeness
edit template-without-completeness "$tp" $'    check_complete(results, sources)\n' $'    pass\n'
expect_fail template-without-completeness "$tp: \`main\` must call \`check_complete(results, sources)\` exactly once"
make_case template-without-projection-record
python3 -B - "$work/template-without-projection-record/$tp" <<'PY'
import sys
path = sys.argv[1]
text = open(path).read()
start = text.index("            if name in PROJECTION:\n")
end = text.index("            if name in STATEMENT_SHAPE:\n", start)
open(path, "w").write(text[:start] + text[end:])
PY
expect_fail template-without-projection-record "$tp: \`main\` never records \`projection_of\` for a control"
make_case template-rebinds-through-globals
edit template-rebinds-through-globals "$tp" $'\n\ndef main():\n' $'\nglobals()[\'TIMEOUT\'] = ()\n\n\ndef main():\n'
expect_fail template-rebinds-through-globals "$tp uses globals, through which a shared helper can be rebound"
make_case template-missing
rm "$work/template-missing/$tp"
expect_fail template-missing "$tp cannot be read as Python"

echo "check-negatives-control-counts cases: $cases passed"
