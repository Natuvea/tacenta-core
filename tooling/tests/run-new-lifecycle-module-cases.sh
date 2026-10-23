#!/usr/bin/env bash
# Negative controls for tacenta-proofs/scripts/new-lifecycle-module.py and genpins.py, on a disposable clone of the
# commit under test, with no Lean toolchain:
#
#   refusals          a missing anchor, an anchor found twice, an unknown part, a bad name and a list not in the
#                     one-entry-per-line form are refused with nothing written
#   scaffold          a fake module is wired: exactly the expected files change, each new line sits after the entry
#                     its name sorts after, and the tree then passes `attest.py --check`, `gate-inventory.py
#                     --check`, `reflow-shared-lists.py --check`, `bash -n`, the parts resolution of the real
#                     `no-sorry.sh`, JSON parsing, the control-count gate (the script's entry is written with its
#                     counts) and the parts runner (the script among its stubs, the phase counted); the
#                     module carries the two pretty-printer options before its pins; a second run changes nothing
#   the template      the new negatives script refuses to run with no control planted, and its start-up checks
#                     refuse a label that does not match where its control is refused, a projection that may be
#                     refused outside a composing proof, and a guard that does not fire on any one of the six
#                     error spellings it lists; its completeness check refuses a run with no Lean run behind it
#                     (simulated: no Lean here); and the count gate follows it: a control planted without its
#                     record entry edited, and the entry deleted, are refused; the parts runner, with the new
#                     stub left out, names the edit to make
#   pins              from a pins section, the module's names land on the four lists of `attest.py` and nowhere
#                     else, in both deletion lists of the attestation negatives with a print-form case, and the
#                     case count moves by the cases added; a second run changes nothing; `attest.py` then refuses
#                     until the claims ledger names the new theorems (the step left by hand)
#   genpins           from Lean's messages (canned), the pins section is written; an error, a missing message and
#                     a stale section are refused
set -euo pipefail

root="$(cd "$(dirname "$0")/../.." && pwd)"
work="$(mktemp -d "${TMPDIR:-/tmp}/new-module-cases.XXXXXX")"
trap 'rm -rf "$work"' EXIT
clone="$work/clone"
git clone -q --shared --no-checkout "$root" "$clone"
git -C "$clone" checkout -q --detach "$(git -C "$root" rev-parse HEAD)"
g() { git -C "$clone" -c user.name=control -c user.email=control@example.invalid "$@"; }
tool="tacenta-proofs/scripts/new-lifecycle-module.py"
cases=0
last_want=0
# The scaffold's dry runs, whose "nothing written" is a case, run on a Python that writes bytecode next to the
# source, as the hosted runner's does (this machine's may not: PYTHONDONTWRITEBYTECODE, or a cache prefix), so a
# script of the tree the tool imports must not leave a __pycache__ there.
inplace=(env -u PYTHONDONTWRITEBYTECODE python3 -X pycache_prefix=)
M=UnitLifecycleScaffoldProbe
N=check-scaffold-probe-negatives.py
args=(scaffold --module "$M" --negatives "$N" --part decrypt --description "The probe's one-line description.")

fail_case() {  # the output under the line is indented, so that a runner's own WRONG lines in it (the parts runner
  # run as a case) are not read by mutate-gates.py as this runner's verdicts
  echo "WRONG  new-lifecycle-module $1" >&2
  shift
  [ $# -eq 0 ] || printf '%s\n' "$@" | sed 's/^/    | /' >&2
  exit 1
}
run() {  # name want-exit command...; output in $out
  local name="$1" want="$2" rc
  shift 2
  last_want="$want"
  set +e
  out="$(cd "$clone" && "$@" 2>&1)"
  rc=$?
  set -e
  cases=$((cases + 1))
  [ "$rc" -eq "$want" ] || fail_case "$name: expected exit $want, got $rc" "$out"
}
says() {  # after a run that had to fail, a missing needle is a refusal with other words
  cases=$((cases + 1))
  if [ "$last_want" -ne 0 ]; then
    grep -qF -- "$2" <<<"$out" || fail_case "$1: refused, but missing diagnostic '$2'" "$out"
  else
    grep -qF -- "$2" <<<"$out" || fail_case "$1: expected '$2'" "$out"
  fi
}
unchanged() {
  cases=$((cases + 1))
  [ -z "$(g status --porcelain)" ] || fail_case "$1: the tree changed" "$(g status --porcelain)"
}
reset() { g reset -q --hard; g clean -fdq; }
edit() {
  python3 - "$clone/$1" "$2" <<'PY'
import sys
path, program = sys.argv[1:]
t = open(path).read()
exec(program)
open(path, "w").write(t)
PY
}
next_line() {  # name file line expected-next-line
  cases=$((cases + 1))
  python3 - "$clone/$2" "$3" "$4" <<'PY' || fail_case "$1: in $2, '$4' does not follow '$3'"
import sys
lines = open(sys.argv[1]).read().split("\n")
k = lines.index(sys.argv[2])
assert lines[k + 1] == sys.argv[3], lines[k + 1]
PY
}

# ---- refusals ----------------------------------------------------------------------------------------------
audit=tacenta-proofs/translation/Translation/AxiomAuditSessionUnit.lean
edit "$audit" "t = '\n'.join(l for l in t.split('\n') if not l.startswith('\`UnitKemWrapperModel.lean\` builds that KEM model'))"
g commit -qam fixture
run anchor-missing 2 python3 "$tool" "${args[@]}"
says anchor-missing "found 0 times, not once"; says anchor-missing "nothing was written"
g reset -q --hard HEAD~1; unchanged anchor-missing
edit "$audit" "t = t.replace('\`UnitKemWrapperModel.lean\` builds that KEM model', '\`UnitKemWrapperModel.lean\` builds that KEM model x\n\`UnitKemWrapperModel.lean\` builds that KEM model', 1)"
g commit -qam fixture
run anchor-twice 2 python3 "$tool" "${args[@]}"
says anchor-twice "found 2 times, not once"
g reset -q --hard HEAD~1; unchanged anchor-twice
run unknown-part 2 python3 "$tool" scaffold --module "$M" --negatives "$N" --part no-such-part --description d
says unknown-part "the hosted partition has no part no-such-part"; unchanged unknown-part
run sliced-part 2 python3 "$tool" scaffold --module "$M" --negatives "$N" --part dispatch-0 --description d
says sliced-part "is \`*\` or a slice"; unchanged sliced-part
run bad-module 2 python3 "$tool" scaffold --module Foo --negatives "$N" --part decrypt --description d
says bad-module "is not a module name"; unchanged bad-module
run bad-script 2 python3 "$tool" scaffold --module "$M" --negatives probe.py --part decrypt --description d
says bad-script "is not a negatives script name"; unchanged bad-script
edit tooling/tests/run-proof-script-cases.sh "t = t.replace('py_controls=(\n  check-lifecycle-translation-coverage.py\n', 'py_controls=(check-lifecycle-translation-coverage.py\n', 1)"
g commit -qam fixture
run packed-list 2 python3 "$tool" "${args[@]}"
says packed-list "run \`python3 tooling/reflow-shared-lists.py --write\`"
g reset -q --hard HEAD~1; unchanged packed-list

# A script name that sorts after every evidence item of the obligations list goes before the last one.
run late-name 0 "${inplace[@]}" "$tool" scaffold --module UnitLifecycleZzProbe --negatives check-zz-probe-negatives.py \
  --part decrypt --description d --check
says late-name "+  \`check-zz-probe-negatives.py\` (SCAFFOLD-TODO: the copies accepted"
unchanged late-name

# ---- scaffold ------------------------------------------------------------------------------------------------
run dry-run 0 "${inplace[@]}" "$tool" "${args[@]}" --check
says dry-run "11 file(s) would change"; unchanged dry-run
run scaffold 0 python3 "$tool" "${args[@]}"
says scaffold "tooling/gate-inventory.py --write: exit 0"; says scaffold "tacenta-proofs/scripts/attest.py: exit 0"
cases=$((cases + 1))
want="ASSURANCE-OBLIGATIONS.md
tacenta-proofs/GATE-INVENTORY.md
tacenta-proofs/manifests/source-commit-attestation.json
tacenta-proofs/manifests/verification-manifest.json
tacenta-proofs/scripts/$N
tacenta-proofs/scripts/negatives-control-counts.json
tacenta-proofs/scripts/no-sorry-parts.txt
tacenta-proofs/scripts/no-sorry.sh
$audit
tacenta-proofs/translation/Translation/$M.lean
tooling/gate-inventory.json
tooling/gate-mutations.json
tooling/tests/run-no-sorry-parts-cases.sh
tooling/tests/run-proof-script-cases.sh"
got="$(g status --porcelain | awk '{print $2}' | sort)"
[ "$got" = "$(printf '%s\n' "$want" | sort)" ] || fail_case "scaffold: other files changed" "$got"
next_line import "$audit" "import Translation.UnitLifecycleRetryLoopT3" "import Translation.$M"
next_line parts tacenta-proofs/scripts/no-sorry-parts.txt "  responder-receipt" "  scaffold-probe"
next_line run-phase tacenta-proofs/scripts/no-sorry.sh \
  '  run_phase restored plain "restored session proof-dependency control" phase_restored' \
  '  run_phase scaffold-probe plain "scaffold-probe proof-dependency control" phase_scaffold_probe'
next_line function tacenta-proofs/scripts/no-sorry.sh "phase_scaffold_probe() {" "python3 scripts/$N || fail=1"
next_line stubs tooling/tests/run-proof-script-cases.sh "  check-restored-negatives.py" "  $N"
next_line called tooling/tests/run-proof-script-cases.sh "  check-restored-negatives.py \\" "  $N \\"
next_line build-controls tooling/gate-inventory.json '    "tacenta-proofs/scripts/check-restored-negatives.py",' \
  "    \"tacenta-proofs/scripts/$N\","
next_line gate-list ASSURANCE-OBLIGATIONS.md '  `check-restored-negatives.py`,' "  \`$N\`,"
next_line parts-stubs tooling/tests/run-no-sorry-parts-cases.sh "  check-restored-negatives.py" "  $N"
next_line record tacenta-proofs/scripts/negatives-control-counts.json \
  "$(grep '^    "check-responder-successor-negatives.py": ' "$root/tacenta-proofs/scripts/negatives-control-counts.json")" \
  "    \"$N\": {\"inside\": 0, \"projection\": 0, \"statement_shape\": 0, \"pin\": 0, \"leaf\": 0, \"baselines\": 2},"
cases=$((cases + 1))
grep -qx 'set_option pp.deepTerms true' "$clone/tacenta-proofs/translation/Translation/$M.lean" \
  && grep -qx 'set_option pp.proofs.withType true' "$clone/tacenta-proofs/translation/Translation/$M.lean" \
  || fail_case "module-pp-options: the module does not set the two options its whole-statement pins need"
cases=$((cases + 1))
grep -q "^    {\"id\": \"NS-drop-scaffold-probe\", " "$clone/tooling/gate-mutations.json" \
  && grep -q "^    {\"id\": \"NS-swallow-scaffold-probe\", " "$clone/tooling/gate-mutations.json" \
  && grep -q "^  {\"gate\": \"tacenta-proofs/scripts/$N\", \"kind\": \"script (control)\"" "$clone/tooling/gate-inventory.json" \
  || fail_case "scaffold: the mutation entries or the inventory row are missing"
run attest-check 0 env PATH="${PATH}" python3 tacenta-proofs/scripts/attest.py --check
run inventory-check 0 python3 tooling/gate-inventory.py --check
run reflow-check 0 python3 tooling/reflow-shared-lists.py --check
run bash-n 0 bash -n tacenta-proofs/scripts/no-sorry.sh
run bash-n-cases 0 bash -n tooling/tests/run-proof-script-cases.sh
run bash-n-parts 0 bash -n tooling/tests/run-no-sorry-parts-cases.sh
run counts-gate 0 python3 tacenta-proofs/scripts/check-negatives-control-counts.py
# The scaffolded script is one more than the scripts the committed record lists.
recorded="$(python3 -B -c 'import json, sys; print(len(json.load(open(sys.argv[1]))["scripts"]))' \
  "$root/tacenta-proofs/scripts/negatives-control-counts.json")"
says counts-gate "$((recorded + 1)) scripts match negatives-control-counts.json"
run parts-runner 0 bash tooling/tests/run-no-sorry-parts-cases.sh
says parts-runner "no-sorry-parts-cases:"
run json 0 python3 -c "import json; json.load(open('tooling/gate-inventory.json')); json.load(open('tooling/gate-mutations.json'))"
(cd "$clone/tacenta-proofs" && NO_SORRY_LIST=1 bash scripts/no-sorry.sh) > "$work/table"
run parts-resolve 0 python3 tacenta-proofs/scripts/no-sorry-parts.py resolve --table "$work/table" \
  --parts tacenta-proofs/scripts/no-sorry-parts.txt --part decrypt
says parts-resolve "scaffold-probe"
run idempotent 0 "${inplace[@]}" "$tool" "${args[@]}" --check
says idempotent "0 file(s) would change"
run preflight 1 python3 tooling/check-proof-module-preflight.py "$M"
says preflight "SCAFFOLD-TODO marker(s) to replace"

# ---- the template's start-up checks -----------------------------------------------------------------------
cp "$clone/tacenta-proofs/scripts/$N" "$work/script"
cp "$clone/tacenta-proofs/translation/Translation/$M.lean" "$work/module"
cp "$clone/tacenta-proofs/scripts/negatives-control-counts.json" "$work/record"
# The script reads the module without its pins, so the module gets a pins section first; and a `lake` that
# accepts every file stands in for Lean, so that only the script's own checks can refuse a run here.
printf '\n/-! ## Pins -/\n' >> "$clone/tacenta-proofs/translation/Translation/$M.lean"
mkdir -p "$work/fakebin"
printf '#!/usr/bin/env bash\nexit 0\n' > "$work/fakebin/lake"
chmod +x "$work/fakebin/lake"
run no-controls 1 env PATH="$work/fakebin:$PATH" python3 "tacenta-proofs/scripts/$N"
says no-controls "NO CONTROLS: MUTANTS is empty"
edit "tacenta-proofs/scripts/$N" "t = t.replace('MUTANTS = [\n', 'MUTANTS = [\n    (\'module\', \'c\', [(\'a\', \'b\')], r\'x\', [\'leaf\']),\n', 1).replace('INSIDE = {}', 'INSIDE = {\'c\': \'leaf\'}')"
run label-broken 1 python3 "tacenta-proofs/scripts/$N"
says label-broken "LABELS BROKEN: c is labelled inside leaf, which is not a composing proof"
# The count gate follows the script: a control planted without its record entry edited is refused.
run counts-follow 1 python3 tacenta-proofs/scripts/check-negatives-control-counts.py
says counts-follow "$N has 1 inside control(s) and negatives-control-counts.json records 0"
cp "$work/script" "$clone/tacenta-proofs/scripts/$N"
edit "tacenta-proofs/scripts/$N" "t = t.replace('MUTANTS = [\n', 'MUTANTS = [\n    (\'module\', \'c\', [(\'a\', \'b\')], r\'x\', [\'leaf\']),\n', 1).replace('PROJECTION = {}', 'PROJECTION = {\'c\': \'called\'}')"
run projection-place 1 python3 "tacenta-proofs/scripts/$N"
says projection-place "LABELS BROKEN: c is labelled a projection, but it may be refused in leaf, which is not a composing proof"
cp "$work/script" "$clone/tacenta-proofs/scripts/$N"
# The guard's self-test, one error spelling taken out of the guard at a time.
for spelling in "unknown identifier|\`Unknown identifier\`" "unknown constant|the kernel's \`unknown constant\`" \
  "unexpected token|\`unexpected token\`" "expected '|\`expected '\`" "unknown namespace|\`unknown namespace\`" \
  "does not contain|\`does not contain\`"; do
  word="${spelling%%|*}"
  python3 - "$clone/tacenta-proofs/scripts/$N" "$word" <<'PY'
import re, sys
path, word = sys.argv[1:]
t = open(path).read()
m = re.search(r"^NOT_A_REFUSAL = \(([^)]*)\)$", t, re.M)
items = [i.strip() for i in m.group(1).replace("\n", " ").split(",") if i.strip()]
kept = [i for i in items if i[1:-1] != word]
assert len(kept) == len(items) - 1, (word, items)
open(path, "w").write(t[:m.start()] + "NOT_A_REFUSAL = (" + ", ".join(kept) + ")" + t[m.end():])
PY
  run "guard-broken-${word// /-}" 1 python3 "tacenta-proofs/scripts/$N"
  says "guard-broken-${word// /-}" "GUARD BROKEN: the not-a-refusal guard does not fire on ${spelling#*|}"
  cp "$work/script" "$clone/tacenta-proofs/scripts/$N"
done
# The completeness check, on a simulated run that ran no Lean (no Lean here): refused.
run complete-no-lean 1 python3 -B - "$clone/tacenta-proofs/scripts/$N" <<'PY'
import importlib.util, sys
spec = importlib.util.spec_from_file_location("generated", sys.argv[1])
m = importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)
m.check_complete({"accepted": ["module", "pinned"], "rejected": {}}, {"module": None, "pinned": None})
PY
says complete-no-lean "INCOMPLETE RUN (not a passing control): Lean ran 0 accepting and 0 refusing times, expected 2 runs"
# The record entry deleted: the count gate refuses the script it no longer lists.
grep -vF "\"$N\": " "$work/record" > "$clone/tacenta-proofs/scripts/negatives-control-counts.json"
run record-missing 1 python3 tacenta-proofs/scripts/check-negatives-control-counts.py
says record-missing "$N carries the shared check_labels and is not in negatives-control-counts.json"
cp "$work/record" "$clone/tacenta-proofs/scripts/negatives-control-counts.json"
# The parts runner with the new script's stub left out names it.
cp "$clone/tooling/tests/run-no-sorry-parts-cases.sh" "$work/parts-runner"
grep -vx "  $N" "$work/parts-runner" > "$clone/tooling/tests/run-no-sorry-parts-cases.sh"
run parts-stub-missed 1 bash tooling/tests/run-no-sorry-parts-cases.sh
says parts-stub-missed "WRONG  parts control fixture-stubs: no-sorry.sh calls scripts/$N, which has no stub here"
cp "$work/parts-runner" "$clone/tooling/tests/run-no-sorry-parts-cases.sh"
cp "$work/module" "$clone/tacenta-proofs/translation/Translation/$M.lean"

# ---- pins ----------------------------------------------------------------------------------------------------
P="Tacenta.$M"
python3 - "$clone/tacenta-proofs/translation/Translation/$M.lean" "$P" <<'PY'
import sys
path, p = sys.argv[1:]
t = open(path).read()
t = t.replace(f"end {p}\n", f"""theorem probe_kernel : True := trivial
theorem probe_compiler : True := trivial
def ProbeShape : Prop := True

end {p}

/-! ## Pins -/

/--
info: '{p}.probe_kernel' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms {p}.probe_kernel

/--
info: '{p}.probe_compiler' depends on axioms: [propext, Lean.ofReduceBool]
-/
#guard_msgs in
#print axioms {p}.probe_compiler

/--
info: {p}.probe_kernel : True
-/
#guard_msgs in
#check @{p}.probe_kernel

/--
info: {p}.probe_compiler : True
-/
#guard_msgs in
#check @{p}.probe_compiler

/--
info: def {p}.ProbeShape : Prop :=
True
-/
#guard_msgs in
#print {p}.ProbeShape
""")
open(path, "w").write(t)
PY
count_before="$(cat "$clone/tacenta-proofs/scripts/attest-negatives-case-count.txt")"
cp "$clone/tacenta-proofs/scripts/attest.py" "$work/attest-before.py"
run pins 0 python3 "$tool" pins --module "$M" --no-regenerate
says pins "2 axiom pins, 3 statement pins, 1 definitions on the print form, 1 compiler-trusted; the attestation negatives gain 6 case(s)"
run pins-lists 0 python3 -B - "$work/attest-before.py" tacenta-proofs/scripts/attest.py "$P" <<'PY'
import importlib.util, sys
def load(path):
    spec = importlib.util.spec_from_file_location("a" + str(abs(hash(path))), path)
    m = importlib.util.module_from_spec(spec); spec.loader.exec_module(m); return m
old, new, p = load(sys.argv[1]), load(sys.argv[2]), sys.argv[3]
want = {"REQUIRED_PINS": {"probe_kernel", "probe_compiler"},
        "REQUIRED_STATEMENT_PINS": {"probe_kernel", "probe_compiler", "ProbeShape"},
        "REQUIRED_PRINT_FORM": {"ProbeShape"}, "COMPILER_TRUSTED_PINS": {"probe_compiler"}}
for name, names in want.items():
    assert getattr(new, name) - getattr(old, name) == {f"{p}.{n}" for n in names}, name
    assert getattr(old, name) <= getattr(new, name), name
PY
cases=$((cases + 1))
[ "$(cat "$clone/tacenta-proofs/scripts/attest-negatives-case-count.txt")" = "$((count_before + 6))" ] \
  || fail_case "pins: the case count did not move by 6"
cases=$((cases + 1))
grep -qxF "$M $P probe_kernel probe_compiler" "$clone/tacenta-proofs/scripts/check-attest-negatives.sh" \
  && grep -qxF "$M $P probe_kernel probe_compiler ProbeShape" "$clone/tacenta-proofs/scripts/check-attest-negatives.sh" \
  && grep -qF '"definition-pin-check-form-ProbeShape"' "$clone/tacenta-proofs/scripts/check-attest-negatives.sh" \
  || fail_case "pins: the deletion-list lines or the print-form case are missing"
run pins-bash-n 0 bash -n tacenta-proofs/scripts/check-attest-negatives.sh
run pins-idempotent 0 "${inplace[@]}" "$tool" pins --module "$M" --check
says pins-idempotent "0 file(s) would change"
run pins-ledger 1 python3 tacenta-proofs/scripts/attest.py --check
says pins-ledger "\`$P.probe_kernel\` is axiom-pinned in"
python3 - "$clone/tacenta-proofs/translation/Translation/$M.lean" "$P" <<'PY'
import sys
path, p = sys.argv[1:]
t = open(path).read()
open(path, "w").write(t + f"\n/--\ninfo: {p}.probe_kernel : True\n-/\n#guard_msgs in\n#check {p}.probe_kernel\n")
PY
run pins-other-form 2 python3 "$tool" pins --module "$M" --no-regenerate
says pins-other-form "4 \`#check\` or \`#print\` pins, of which 3 are in the form"
reset

# ---- genpins, from canned messages ---------------------------------------------------------------------------
mkdir -p "$work/pkg/Mod"
printf 'name = "probe"\n' > "$work/pkg/lakefile.toml"
printf 'namespace Probe\n\ntheorem t : True := trivial\n\ndef d : Nat := 1\n\nend Probe\n' > "$work/pkg/Mod/M.lean"
# The probe is the body (7 lines and a blank) then the three commands on lines 9, 10 and 11.
cat > "$work/lean.json" <<'EOF'
{"severity": "information", "pos": {"line": 9, "column": 0}, "data": "'Probe.t' depends on axioms: [propext]"}
{"severity": "information", "pos": {"line": 10, "column": 0}, "data": "Probe.t : True"}
{"severity": "information", "pos": {"line": 11, "column": 0}, "data": "def Probe.d : Nat :=\n1"}
EOF
run genpins 0 python3 tacenta-proofs/scripts/genpins.py "$work/pkg/Mod/M.lean" --lean-json "$work/lean.json"
says genpins "wrote 3 pins (1 theorems, 1 definitions)"
cases=$((cases + 1))
grep -qx '#print axioms Probe.t' "$work/pkg/Mod/M.lean" && grep -qx "info: 'Probe.t' depends on axioms: \[propext\]" "$work/pkg/Mod/M.lean" \
  && grep -qx '#check @Probe.t' "$work/pkg/Mod/M.lean" && grep -qx '#print Probe.d' "$work/pkg/Mod/M.lean" \
  || fail_case "genpins: the section does not hold the three pins" "$(cat "$work/pkg/Mod/M.lean")"
run genpins-current 0 python3 tacenta-proofs/scripts/genpins.py "$work/pkg/Mod/M.lean" --lean-json "$work/lean.json" --check
sed 's/\[propext\]/[propext, Quot.sound]/' "$work/lean.json" > "$work/lean2.json"
run genpins-stale 1 python3 tacenta-proofs/scripts/genpins.py "$work/pkg/Mod/M.lean" --lean-json "$work/lean2.json" --check
says genpins-stale "is not what Lean prints now"
sed 's/"severity": "information", "pos": {"line": 10/"severity": "warning", "pos": {"line": 10/' "$work/lean.json" > "$work/lean4.json"
run genpins-warning 2 python3 tacenta-proofs/scripts/genpins.py "$work/pkg/Mod/M.lean" --lean-json "$work/lean4.json"
says genpins-warning "got a warning message"
sed '/"line": 10/d' "$work/lean.json" > "$work/lean3.json"
run genpins-missing 2 python3 tacenta-proofs/scripts/genpins.py "$work/pkg/Mod/M.lean" --lean-json "$work/lean3.json"
says genpins-missing "got 0 messages"
printf '{"severity": "error", "pos": {"line": 3, "column": 0}, "data": "unsolved goals"}\n' >> "$work/lean3.json"
run genpins-error 2 python3 tacenta-proofs/scripts/genpins.py "$work/pkg/Mod/M.lean" --lean-json "$work/lean3.json"
says genpins-error "Lean reports an error at line 3"

echo "new-lifecycle-module-cases: $cases cases (a missing, a doubled and a packed anchor, an unknown or sliced part and bad names refused with nothing written; a late name placed before the last evidence item; the scaffold changed exactly the expected files at the expected places and the tree passed the attestation, inventory, form, shell, JSON and parts checks, the control-count gate and the parts runner, the module set the two pretty-printer options, and a second run changed nothing; the template refused no controls, a broken inside or projection label, a guard missing any one of its six spellings and a run with no Lean behind it, the count gate refused a control planted without its record entry and a missing entry, and the parts runner named a stub left out; the pins step placed the names on the four lists and the two deletion lists, moved the count by its cases, changed nothing the second time, left the ledger to be written and refused a pin it cannot read; genpins wrote, checked and refused an error, a missing and a warning message) gave the expected result"
