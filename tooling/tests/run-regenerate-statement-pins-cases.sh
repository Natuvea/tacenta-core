#!/usr/bin/env bash
# Negative controls for tacenta-proofs/scripts/regenerate-statement-pins.py, with no Lean toolchain.
#
# The script rewrites a translation module's statement pins from what `lake env lean --json` prints. Here a stub
# `lake` stands in for Lean: it reads the module it is given and, for each pin, prints the message a canned table
# holds for its command (a cut message with `⋯` when the module does not set `pp.deepTerms true` before the pin,
# the whole one when it does), with Lean's "does not match" error at the `#guard_msgs` line when the docstring
# differs; a line holding `PLANTED_ERROR` gets an ordinary error. The cases, on a disposable clone of the commit
# under test:
#
#   check, cut        --check on a module whose pin holds the cut message and that lacks the two options: exit
#                     1, the options and the pin named, the module unchanged
#   rewrite           without --check: the options inserted once before the first statement pin, the pin's
#                     docstring replaced by the whole message, nothing else changed; --check then exits 0
#   other error       an error that is not a pin mismatch: refused, the module left as it was
#   not a statement   a mismatch at an axiom pin, which this script does not rewrite: refused, module unchanged,
#                     also when the script had inserted the options first (they are taken out again)
#   after the rewrite an error, or a warning more, that only the rewritten module has: refused
#   outside           a module outside tacenta-proofs/translation/Translation: refused
#
# What Lean itself prints, and that the rewrite then elaborates, is not checked here (no Lean): `attest.py`
# refuses a cut-off pin in CI, and the translation build compares every pin.
set -euo pipefail

root="$(cd "$(dirname "$0")/../.." && pwd)"
work="$(mktemp -d "${TMPDIR:-/tmp}/regenerate-statement-pins-cases.XXXXXX")"
trap 'rm -rf "$work"' EXIT
clone="$work/clone"
git clone -q --shared --no-checkout "$root" "$clone"
git -C "$clone" checkout -q --detach "$(git -C "$root" rev-parse HEAD)"
tool="$clone/tacenta-proofs/scripts/regenerate-statement-pins.py"
module="$clone/tacenta-proofs/translation/Translation/PinsProbe.lean"
cases=0

fail_case() {
  echo "WRONG  regenerate-statement-pins $1" >&2
  shift
  [ $# -eq 0 ] || printf '%s\n' "$@" | sed 's/^/    | /' >&2
  exit 1
}
run() {  # name want-exit args...; output in $out
  local name="$1" want="$2" rc
  shift 2
  set +e
  out="$(cd "$clone" && PATH="$work/bin:$PATH" python3 "$tool" "$@" 2>&1)"
  rc=$?
  set -e
  cases=$((cases + 1))
  [ "$rc" -eq "$want" ] || fail_case "$name: expected exit $want, got $rc" "$out"
}
says() {
  cases=$((cases + 1))
  grep -qF -- "$2" <<<"$out" || fail_case "$1: missing '$2'" "$out"
}
same() {  # name file: the module is byte for byte the file
  cases=$((cases + 1))
  cmp -s "$module" "$2" || fail_case "$1: the module changed" "$(diff "$2" "$module" || true)"
}

mkdir -p "$work/bin"
cat > "$work/bin/lake" <<'STUB'
#!/usr/bin/env python3
import json, re, sys
path = sys.argv[-1]
text = open(path).read()
table = {
    "#check @Tacenta.PinsProbe.t": ("Tacenta.PinsProbe.t :\n  ∀ (a : Nat), ⋯", "Tacenta.PinsProbe.t :\n  ∀ (a : Nat), a = a"),
    "#print axioms Tacenta.PinsProbe.t": ("'Tacenta.PinsProbe.t' depends on axioms: [propext]",) * 2,
}
pin = re.compile(r"/--\n(?P<doc>(?:(?!-/).)*?)\n?-/\n#guard_msgs in\n(?P<cmd>#[^\n]+)\n", re.S)
out = []
for m in pin.finditer(text):
    guard = text.count("\n", 0, m.start("cmd"))
    before = text[:m.start()]
    whole = "set_option pp.deepTerms true\nset_option pp.proofs.withType true\n" in before
    printed = table[m.group("cmd")][1 if whole else 0]
    out.append({"severity": "information", "pos": {"line": guard + 1, "column": 0}, "data": printed})
    if m.group("doc") != "info: " + printed:
        out.append({"severity": "error", "pos": {"line": guard, "column": 0},
                    "data": "❌️ Docstring on `#guard_msgs` does not match generated message"})
rewritten = "  ∀ (a : Nat), a = a\n-/" in text
for k, line in enumerate(text.split("\n"), 1):
    if "PLANTED_ERROR_AFTER" in line:
        if rewritten:
            out.append({"severity": "error", "pos": {"line": k, "column": 0}, "data": "unsolved goals"})
    elif "PLANTED_ERROR" in line:
        out.append({"severity": "error", "pos": {"line": k, "column": 0}, "data": "unsolved goals"})
    if "PLANTED_WARNING_AFTER" in line and rewritten:
        out.append({"severity": "warning", "pos": {"line": k, "column": 0}, "data": "unused variable"})
for o in out:
    print(json.dumps(o, ensure_ascii=False))
sys.exit(1 if any(o["severity"] == "error" for o in out) else 0)
STUB
chmod +x "$work/bin/lake"

write_module() {  # extra-line
  cat > "$module" <<EOF
namespace Tacenta.PinsProbe

theorem t : ∀ (a : Nat), a = a := fun _ => rfl
$1
end Tacenta.PinsProbe

/-! ## Pins -/

/--
info: 'Tacenta.PinsProbe.t' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Tacenta.PinsProbe.t

/--
info: Tacenta.PinsProbe.t :
  ∀ (a : Nat), ⋯
-/
#guard_msgs in
#check @Tacenta.PinsProbe.t
EOF
  cp "$module" "$work/before"
}

# check, cut
write_module ""
run check-cut 1 PinsProbe --check
says check-cut "PinsProbe.lean: the two pp options are not in place before the first statement pin"
says check-cut "PinsProbe.lean: would rewrite the pin of Tacenta.PinsProbe.t"
same check-cut "$work/before"

# rewrite
run rewrite 0 PinsProbe
says rewrite "PinsProbe.lean: rewrote the pin of Tacenta.PinsProbe.t"
cases=$((cases + 1))
python3 - "$work/before" "$module" <<'PY' || fail_case "rewrite: the module is not the old one with the options and the whole pin" "$(cat "$module")"
import sys
before, after = open(sys.argv[1]).read(), open(sys.argv[2]).read()
want = before.replace("/--\ninfo: Tacenta.PinsProbe.t :\n  ∀ (a : Nat), ⋯\n-/",
                      "set_option pp.deepTerms true\nset_option pp.proofs.withType true\n\n"
                      "/--\ninfo: Tacenta.PinsProbe.t :\n  ∀ (a : Nat), a = a\n-/")
assert after == want
assert after.count("set_option pp.deepTerms true") == 1
PY
run rewrite-then-check 0 PinsProbe --check

# other error
write_module "-- PLANTED_ERROR"
run other-error 1 PinsProbe
says other-error "Lean reported 1 error(s) that are not a pin mismatch"
same other-error "$work/before"

# an error, or one warning more, that only the rewritten module has: refused after the rewrite
write_module "-- PLANTED_ERROR_AFTER"
run error-after-rewrite 1 PinsProbe
says error-after-rewrite "after the rewrite Lean still reports 1 error(s)"
write_module "-- PLANTED_WARNING_AFTER"
run warning-after-rewrite 1 PinsProbe
says warning-after-rewrite "the rewrite changed the number of warnings Lean reports"

# a mismatch at an axiom pin in a module without the options: the options it inserted are taken out again
write_module ""
python3 - "$module" <<'PY'
import sys
p = sys.argv[1]
t = open(p).read().replace("depends on axioms: [propext]", "depends on axioms: [propext, Quot.sound]")
open(p, "w").write(t)
PY
cp "$module" "$work/before"
run axiom-pin-mismatch-restored 1 PinsProbe
says axiom-pin-mismatch-restored "that are not statement pins this script rewrites"
same axiom-pin-mismatch-restored "$work/before"

# not a statement pin
write_module ""
python3 - "$module" <<'PY'
import sys
p = sys.argv[1]
t = open(p).read().replace("depends on axioms: [propext]", "depends on axioms: [propext, Quot.sound]")
t = t.replace("/--\ninfo: Tacenta.PinsProbe.t :", "set_option pp.deepTerms true\nset_option pp.proofs.withType true\n\n/--\ninfo: Tacenta.PinsProbe.t :")
open(p, "w").write(t)
PY
cp "$module" "$work/before"
run axiom-pin-mismatch 1 PinsProbe
says axiom-pin-mismatch "that are not statement pins this script rewrites"
same axiom-pin-mismatch "$work/before"

# outside the translation package
run outside 1 "$clone/tacenta-model/Model/State.lean"
says outside "not a module of tacenta-proofs/translation/Translation"

echo "regenerate-statement-pins-cases: $cases cases (a cut pin and missing options reported by --check with nothing written; the options inserted once and the pin rewritten whole, then --check clean; an error that is not a pin mismatch and a mismatch at an axiom pin (with and without the options in place) refused with the module left as it was; an error or a warning more after the rewrite refused; a module outside the translation refused) gave the expected result"
