#!/usr/bin/env bash
# Negative controls for tooling/check-proof-module-preflight.py, on a disposable clone of the commit under test.
#
#   the tree as committed, with its baseline        passes (the known findings reported as known); the private-term
#                                                   scan says it was skipped
#   a baseline key that no longer occurs            a warning to delete it; an error with --strict
#   a baseline that omits a known finding           fails
#   a key the baseline gained since a base          fails with --baseline-base, unless `reasons` gives it a reason
#   a base that does not resolve to a commit        fails (it would let the baseline grow unseen); warnings alone
#                                                   do not fail the run
#   the results a section names first (in the       a named result with no pin, or matched only by a substring
#   section of UnitLifecycleResponderReply)         of a pin's name; a kernel-only result padded into the named
#                                                   list with the counts moved to match; an unnamed result made
#                                                   compiler-trusted with the counts moved to match; a count
#                                                   whose two parts do not add up: each named
#   a negatives script from the template, with one control planted, is the clean fixture of the mechanism check;
#   a stub that defines every name and calls nothing fails it; then, all planted at once and each required by name
#   in one run:
#     (b) the guard not lowered, `unknown constant` dropped from it, `check_labels` not called, the `pinned`
#         baseline dropped, the timeout sample dropped
#     (c) a section's count of results, its count of the results other than the ones it names first, a script's
#         count in ASSURANCE-OBLIGATIONS.md and a docstring's count of inside labels each off by one
#     (a) a not-shown item dropped from a module's docstring (a warning; an error with --strict)
#     (d) a SCAFFOLD marker left in a tracked file, a plan identifier and a private path (stand-ins the test seam
#         adds, which spell nothing real), and an attribution line in a commit message since --base
#     (e) a stand-in term on a local list given by TACENTA_PRIVATE_TERMS_FILE, planted with other separators, as one
#         word and split inside a word
set -euo pipefail

root="$(cd "$(dirname "$0")/../.." && pwd)"
work="$(mktemp -d "${TMPDIR:-/tmp}/preflight-cases.XXXXXX")"
trap 'rm -rf "$work"' EXIT
clone="$work/clone"
git clone -q --shared --no-checkout "$root" "$clone"
git -C "$clone" checkout -q --detach "$(git -C "$root" rev-parse HEAD)"
g() { git -C "$clone" -c user.name=control -c user.email=control@example.invalid "$@"; }
lint="tooling/check-proof-module-preflight.py"
baseline="tooling/proof-module-preflight-baseline.json"
cases=0

fail_case() {
  echo "WRONG  preflight $1" >&2
  shift
  [ $# -eq 0 ] || printf '%s\n' "$@" >&2
  exit 1
}
run() {  # name want-exit args... ; the output is in $out
  local name="$1" want="$2" rc
  shift 2
  set +e
  out="$(cd "$clone" && python3 "$lint" "$@" 2>&1)"
  rc=$?
  set -e
  cases=$((cases + 1))
  [ "$rc" -eq "$want" ] || fail_case "$name: expected exit $want, got $rc" "$out"
}
says() {  # name needle: the last run printed the needle
  cases=$((cases + 1))
  grep -qF -- "$2" <<<"$out" || fail_case "$1: expected '$2'" "$out"
}
edit() {  # file program-over-t
  python3 - "$clone/$1" "$2" <<'PY'
import sys
path, program = sys.argv[1:]
t = open(path).read()
exec(program)
open(path, "w").write(t)
PY
}

run committed 0 --all --baseline "$baseline"
says committed "0 error(s), 10 known"
says committed "private-term scan skipped: no list"
python3 - "$clone/$baseline" <<'PY'
import json, sys
d = json.load(open(sys.argv[1]))
d["findings"].append("UnitLifecycleNotAModule|terms|x")
json.dump(d, open(sys.argv[1], "w"))
PY
run stale-baseline-key 0 --all --baseline "$baseline"
says stale-baseline-key "warning  stale key: delete it from $baseline: UnitLifecycleNotAModule|terms|x"
run stale-baseline-key-strict 1 --all --baseline "$baseline" --strict
says stale-baseline-key-strict "ERROR    stale key: delete it from $baseline: UnitLifecycleNotAModule|terms|x"
g commit -qam "a key added"
run baseline-grew 1 --all --baseline "$baseline" --baseline-base HEAD~1
says baseline-grew "the baseline gained UnitLifecycleNotAModule|terms|x since HEAD~1 with no reason"
python3 - "$clone/$baseline" <<'PY'
import json, sys
d = json.load(open(sys.argv[1]))
d["reasons"]["UnitLifecycleNotAModule|terms|x"] = "a reviewed exception"
json.dump(d, open(sys.argv[1], "w"))
PY
run baseline-grew-with-reason 0 --all --baseline "$baseline" --baseline-base HEAD~1
says baseline-grew-with-reason "note     the baseline gained UnitLifecycleNotAModule|terms|x since HEAD~1: a reviewed exception"
run base-unresolved 1 --all --baseline "$baseline" --baseline-base refs/heads/no-such-base
says base-unresolved "ERROR    the base refs/heads/no-such-base does not resolve to a commit"
g reset -q --hard HEAD~1
python3 - "$clone/$baseline" <<'PY'
import json, sys
d = json.load(open(sys.argv[1]))
d["findings"] = [k for k in d["findings"] if not k.startswith("check-responder-receipt-negatives.py|mechanism")]
json.dump(d, open(sys.argv[1], "w"))
PY
run baseline-omits 1 --all --baseline "$baseline"
says baseline-omits "check-responder-receipt-negatives.py: lacks the hardened mechanism"
g checkout -q -- "$baseline"

# The results a section names first are excluded from its "of the other N results" by name. A named result with no
# pin is an error, and a name matches a pin only as its full name or its last parts after a dot.
lead="**Compiler trust and pins.** \`responder_reply_refines\`, "
edit tacenta-proofs/CLAIMS.md "t = t.replace('$lead', '$lead'.replace('refines', 'refines_unpinned'), 1)"
run named-without-pin 1 UnitLifecycleResponderReply --baseline "$baseline"
says named-without-pin "names \`responder_reply_refines_unpinned\` first, which has no pin in the section's modules"
g checkout -q -- tacenta-proofs/CLAIMS.md
edit tacenta-proofs/CLAIMS.md "t = t.replace('$lead', '$lead'.replace('responder_reply_refines', 'reply_refines'), 1)"
run named-substring 1 UnitLifecycleResponderReply --baseline "$baseline"
says named-substring "names \`reply_refines\` first, which has no pin in the section's modules"
g checkout -q -- tacenta-proofs/CLAIMS.md
# A kernel-only result padded into the named list, with the counts moved so that they still match: the paragraph
# says the named results rest on opaque constants, and this one does not.
edit tacenta-proofs/CLAIMS.md "t = t.replace(' and \`first_send_reply_reachable\`\napply', ', \`first_send_reply_reachable\` and \`array_clone_u8\`\napply', 1).replace('Of the other 14 results, 6 rest on', 'Of the other 13 results, 5 rest on', 1)"
run named-padded 1 UnitLifecycleResponderReply --baseline "$baseline"
says named-padded "names \`array_clone_u8\` first as resting on opaque constants; its pin rests on the kernel's axioms alone"
g checkout -q -- tacenta-proofs/CLAIMS.md
# An unnamed result made compiler-trusted, with the kernel-only count moved to match: the other results' sentence
# does not state it, so it is named as an error.
edit tacenta-proofs/translation/Translation/UnitLifecycleResponderReply.lean "t = t.replace(\"array_clone_u8' depends on axioms: [propext, Classical.choice, Quot.sound]\", \"array_clone_u8' depends on axioms: [propext, Classical.choice, Quot.sound, Lean.ofReduceBool]\", 1)"
edit tacenta-proofs/CLAIMS.md "t = t.replace('Of the other 14 results, 6 rest on', 'Of the other 14 results, 5 rest on', 1)"
run other-compiler 1 UnitLifecycleResponderReply --baseline "$baseline"
says other-compiler "\`array_clone_u8\` is compiler-trusted, and is not among the results named first"
g checkout -q -- tacenta-proofs/CLAIMS.md tacenta-proofs/translation/Translation/UnitLifecycleResponderReply.lean
# The two parts of the other results must add up to them.
edit tacenta-proofs/CLAIMS.md "t = t.replace(') and 8 on those and opaque constants of the unit. Each of the 19', ') and 7 on those and opaque constants of the unit. Each of the 19', 1)"
run other-sum 1 UnitLifecycleResponderReply --baseline "$baseline"
says other-sum "says 6 and 7 of the other 14 results, which do not add up"
g checkout -q -- tacenta-proofs/CLAIMS.md
# A warning alone does not fail the run (CI runs the check for its errors only).
edit tacenta-proofs/translation/Translation/UnitLifecycleResponderFirstReceipt.lean "t = t.replace('* That a tampered or foreign frame is refused: no AEAD authenticity law is assumed.\n', '', 1)"
run warning-only 0 UnitLifecycleResponderFirstReceipt --baseline "$baseline"
says warning-only "warning  UnitLifecycleResponderFirstReceipt: CLAIMS.md lists as not shown \"that a tampered or foreign frame is refused"
says warning-only "0 error(s)"
g checkout -q -- tacenta-proofs/translation/Translation/UnitLifecycleResponderFirstReceipt.lean

# The clean fixture of the mechanism: the template's script for a module, with one control planted.
module=UnitLifecyclePreflightProbe
script="tacenta-proofs/scripts/check-preflight-probe-negatives.py"
sed -e "s/@MODULE@/$module/g" -e 's/@IMPORT@/Translation.UnitLifecycleT3/g' -e 's/@DESCRIPTION@/A probe./g' \
  -e 's/@PROBE@/preflight-probe/g' "$clone/tacenta-proofs/scripts/templates/lifecycle-negatives.py.in" > "$clone/$script"
sed -e "s/@MODULE@/$module/g" -e 's/@IMPORT@/Translation.UnitLifecycleT3/g' -e 's/@DESCRIPTION@/A probe./g' \
  "$clone/tacenta-proofs/scripts/templates/lifecycle-module.lean.in" \
  | sed 's/SCAFFOLD-TODO: //' > "$clone/tacenta-proofs/translation/Translation/$module.lean"
edit "$script" "t = t.replace('MUTANTS = [\n', 'MUTANTS = [\n    (\'module\', \'a-planted-change\', [(\'a\', \'b\')], r\'x\', [\'composed\']),\n', 1).replace('COMPOSING = set()', 'COMPOSING = {\'composed\'}').replace('INSIDE = {}', 'INSIDE = {\'a-planted-change\': \'composed\'}').replace('SCAFFOLD-TODO: ', '')"
g add -A
run clean-template 0 "$module"
says clean-template "0 error(s)"
cases=$((cases + 1))
! grep -q "lacks the hardened mechanism" <<<"$out" || fail_case "clean-template: the template's mechanism was flagged" "$out"

# A stub that defines every name and sample of the mechanism and calls none of it.
cp "$clone/$script" "$work/template-script"
python3 - "$clone/$script" <<'PY'
import ast, sys
path = sys.argv[1]
tree = ast.parse(open(path).read())
for node in tree.body:
    if isinstance(node, ast.FunctionDef):
        doc = ast.get_docstring(node) or ""
        samples = [n.value for n in ast.walk(node) if isinstance(n, ast.Constant) and isinstance(n.value, str)]
        node.body = [ast.Expr(ast.Constant(" ".join(samples) + " " + doc)), ast.Pass()]
open(path, "w").write(ast.unparse(tree) if hasattr(ast, "unparse") else open(path).read())
PY
if python3 -c 'import ast, sys; sys.exit(0 if hasattr(ast, "unparse") else 1)'; then
  run stub-script 1 "$module"
  says stub-script "lacks the hardened mechanism (a structural check of names and call sites"
  says stub-script "a \`check_labels\` that reads the four labels and raises"
fi
cp "$work/template-script" "$clone/$script"

# Every fault at once; each must be named in one run.
edit "$script" "t = t.replace('heads = [head.lower() for head in', 'heads = [head for head in', 1)"
edit "$script" "t = t.replace(\"'unknown identifier', 'unknown constant',\", \"'unknown identifier',\", 1)"
edit "$script" "t = t.replace('    check_labels()\n    parser', '    parser', 1)"
edit "$script" "t = t.replace(\"        'pinned': module,\n\", '', 1)"
edit "$script" "t = t.replace('error: (deterministic) timeout at', 'error: (deterministic) stop at', 1)"
edit tacenta-proofs/scripts/check-responder-receipt-negatives.py "t = t.replace('\"\"\"', '\"\"\"Two controls are labelled inside. ', 1) + '\nCOMPOSING = set()\nINSIDE = {}\n'"
edit tacenta-proofs/CLAIMS.md "t = t.replace('Each of the 42 results carries an axiom pin', 'Each of the 43 results carries an axiom pin', 1)"
edit tacenta-proofs/CLAIMS.md "t = t.replace('other 35 results, 9 rest', 'other 36 results, 9 rest', 1)"
edit ASSURANCE-OBLIGATIONS.md "t = t.replace('\`check-responder-receipt-negatives.py\` (two unmodified copies accepted and twenty changes refused', '\`check-responder-receipt-negatives.py\` (two unmodified copies accepted and twenty-one changes refused', 1)"
edit tacenta-proofs/translation/Translation/UnitLifecycleResponderFirstReceipt.lean "t = t.replace('* That a tampered or foreign frame is refused: no AEAD authenticity law is assumed.\n', '', 1)"
edit "tacenta-proofs/translation/Translation/$module.lean" "t = t.replace('A probe.', 'A probe for item Q9, see zzdir/x/y.md, and the Zz_Forbidden.probe word.', 1)"
printf '# a local list\nzz-forbidden-probe\n' > "$work/terms"
printf 'SCAFFOLD''-TODO: a marker left behind\n' >> "$clone/CONTRIBUTING.md"
g add -A
g commit -q -m "planted" -m "Co-Authored-By: someone <someone@example.invalid>"
seam=(env PREFLIGHT_SEAM=tests-only PREFLIGHT_PLAN_ID='Q[0-9]' PREFLIGHT_PRIVATE_PATH=zzdir/ TACENTA_PRIVATE_TERMS_FILE="$work/terms")
run_seam() {  # name want-exit args...
  local name="$1" want="$2" rc
  shift 2
  set +e
  out="$(cd "$clone" && "${seam[@]}" python3 "$lint" "$@" 2>&1)"
  rc=$?
  set -e
  cases=$((cases + 1))
  [ "$rc" -eq "$want" ] || fail_case "$name: expected exit $want, got $rc" "$out"
}
run_seam planted 1 "$module" UnitLifecycleResponderFirstReceipt --baseline "$baseline" --base HEAD~1
for needle in \
  "the guard matched in lower case" \
  "\`unknown constant\` in NOT_A_REFUSAL" \
  "\`guard_self_test()\` and \`check_labels()\` called as statements of \`main\` before Lean runs" \
  "the two baselines (\`module\` and \`pinned\`)" \
  "a start-up sample of a heartbeat timeout" \
  "says 43 results with an axiom pin; there are 42" \
  "says 36 results other than the ones named first; there are 35" \
  "ASSURANCE-OBLIGATIONS.md: says 21 changes refused by check-responder-receipt-negatives.py; there are 20" \
  "check-responder-receipt-negatives.py docstring: says 2 controls labelled INSIDE; there are 0" \
  "warning  UnitLifecycleResponderFirstReceipt: CLAIMS.md lists as not shown \"that a tampered or foreign frame is refused" \
  "CONTRIBUTING.md: holds 1 SCAFFOLD-TODO marker(s) to replace" \
  "$module.lean: holds a plan identifier the repository keeps out of its text (Q9)" \
  "$module.lean: holds a private path the repository keeps out of its text (zzdir/...)" \
  "$module.lean: holds a private term the repository keeps out of its text (line 2 of the list)" \
  "its message holds an attribution the repository keeps out" \
  "a line added since HEAD~1 holds a plan identifier the repository keeps out (Q9)" ; do
  says planted "$needle"
done
# The stand-in term written as one word, and split inside a word, is caught too.
for form in "ZzForbiddenProbe" "zzforbid' + 'denprobe"; do
  edit "tacenta-proofs/translation/Translation/$module.lean" "import re; t = re.sub(r'the [^ ]* word', 'the $form word', t, count=1)"
  run_seam "no-separator ($form)" 1 "$module"
  says "no-separator ($form)" "$module.lean: holds a private term the repository keeps out of its text (line 2 of the list)"
done
# Without the seam the stand-ins are not refused: the seam only adds patterns.
run no-seam 1 "$module" --baseline "$baseline"
cases=$((cases + 1))
! grep -q "(Q9)\|zzdir/\|private term" <<<"$out" || fail_case "no-seam: a stand-in was refused without the seam" "$out"
cases=$((cases + 1))
out="$(cd "$clone" && PREFLIGHT_PLAN_ID=x python3 "$lint" --all 2>&1 || true)"
grep -qF "are a test seam" <<<"$out" || fail_case "seam-without-switch: the seam variable was read" "$out"
run planted-strict 1 UnitLifecycleResponderFirstReceipt --strict
says planted-strict "ERROR    UnitLifecycleResponderFirstReceipt: CLAIMS.md lists as not shown \"that a tampered or foreign frame is refused"

echo "check-proof-module-preflight-cases: $cases cases (the committed tree with its baseline passed; a stale key warned, and refused with --strict; a short baseline, a grown one without a reason and an unresolved base refused; warnings alone not failing; the template's mechanism passed and a stub of it refused; a first-named result with no pin or matched by a substring, a padded named list, an unnamed compiler-trusted result and other counts that do not add up named; a weakened guard, a dropped label check, baseline or timeout sample, four counts off by one, a dropped not-shown item, a marker, stand-in plan identifier, private path and private term, and an attribution line each named; the seam only adds) gave the expected result"
