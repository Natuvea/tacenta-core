#!/usr/bin/env bash
# Negative controls for the proof-build scripts, with no Lean toolchain:
#
#   tacenta-proofs/scripts/no-sorry.sh                  the log scan, the audit-line guard, the kernel replay,
#                                                       and that every control script it names is called and
#                                                       its failure is a failure
#   tacenta-proofs/scripts/verify.sh                    the proofs build and hold no sorry or admit
#   tacenta-proofs/scripts/check-translation-coverage.sh  every translation module was built
#
# `no-sorry.sh` is the translation job's one long step, and the controls it runs (the port, satisfiability,
# initial-dispatch and audit controls) hold nothing if the line that calls one is deleted or its result is
# thrown away. The real script is copied, unchanged, into a fixture package, with `lake` and `leanchecker`
# replaced by a stub that prints a canned build log, and the sibling scripts replaced by stubs that record
# that they were called and fail on request. Each case then changes one thing in the log or in which stub
# fails and requires the script's own verdict.
#
# What this does not show: that a control script, run for real, would fail. Each of those has its own
# negative controls (`check-port-negatives.sh` and the others), which `no-sorry.sh` runs.
set -euo pipefail

root="$(cd "$(dirname "$0")/../.." && pwd)"
scripts="$root/tacenta-proofs/scripts"
work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT
cases=0

fail_case() {
  echo "WRONG  $1" >&2
  shift
  [ $# -eq 0 ] || printf '%s\n' "$@" >&2
  exit 1
}

# ---- the fixture package ---------------------------------------------------------------------
fx="$work/fixture"
proofs="$fx/tacenta-proofs"
mkdir -p "$proofs/scripts" "$proofs/translation/Translation" "$proofs/Proofs" \
  "$fx/tacenta-model/Model" "$fx/tacenta-model/Properties" "$work/bin" "$work/logs"
for f in no-sorry.sh verify.sh check-translation-coverage.sh; do cp "$scripts/$f" "$proofs/scripts/$f"; done
for m in Alpha Beta; do : > "$proofs/translation/Translation/$m.lean"; done
: > "$proofs/Proofs/Gamma.lean"
: > "$fx/tacenta-model/Model/Delta.lean"
: > "$fx/tacenta-model/Properties/Epsilon.lean"

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
sh_controls=(check-lifecycle-translation-coverage-negatives.sh check-session-satisfiability-negatives.sh
  check-port-negatives.sh check-lean-constructs.sh check-audit-reach.sh check-audit-reach-negatives.sh
  check-pin-negatives.sh check-kernel-replay-negative.sh check-audit-negatives.sh
  check-precondition-witnesses.sh check-hypothesis-witnesses.sh check-braid-agreement-negatives.sh)
py_controls=(check-lifecycle-translation-coverage.py check-initial-dispatch-negatives.py check-atomicity-negatives.py
  check-repair-negatives.py check-send-refusal-negatives.py check-sparse-store-full-negatives.py
  check-decrypt-ratchet-negatives.py attest.py)
for s in "${sh_controls[@]}"; do stub_sh "$s"; done
for s in "${py_controls[@]}"; do stub_py "$s"; done
# check-translation-coverage.sh is the real script in the no-sorry cases (its fixture is complete below).

cat >"$work/bin/lake" <<'STUB'
#!/usr/bin/env bash
pkg="$(basename "$(pwd)")"
case "$1" in
  build)
    echo "lake build $pkg" >> "$STUB_CALLS"
    [ -f "$STUB_LOGS/$pkg.log" ] && cat "$STUB_LOGS/$pkg.log"
    [ -f "$STUB_LOGS/$pkg.fail" ] && { echo "error: build failed" >&2; exit 1; }
    exit 0 ;;
  env)
    echo "leanchecker $pkg $3" >> "$STUB_CALLS"
    [ "${STUB_REPLAY_FAIL:-}" = "$3" ] && exit 1
    exit 0 ;;
esac
exit 0
STUB
chmod +x "$work/bin/lake"

# Built outputs for the real coverage script.
lib="$proofs/translation/.lake/build/lib/lean/Translation"
mkdir -p "$lib"
for m in Alpha Beta; do : > "$lib/$m.olean"; done
printf 'name = "Translation"\n[[lean_lib]]\nname = "Translation"\nglobs = ["Translation.*"]\n' > "$proofs/translation/lakefile.toml"

honest_logs() {
  rm -f "$work/logs"/*
  printf 'building\naudit-axiom: Translation.TacentaX axiom foo : Nat\n' > "$work/logs/translation.log"
  : > "$work/logs/tacenta-proofs.log"
  : > "$work/logs/tacenta-model.log"
}

# run_nosorry <name> <expected exit status class: 0|nonzero> <expected text> [VAR=value ...]
run_nosorry() {
  local name="$1" want="$2" needle="$3" out rc
  shift 3
  : > "$work/calls"
  set +e
  out="$(cd "$proofs" && env PATH="$work/bin:$PATH" STUB_CALLS="$work/calls" STUB_LOGS="$work/logs" "$@" \
    bash scripts/no-sorry.sh 2>&1)"
  rc=$?
  set -e
  cases=$((cases + 1))
  if { [ "$want" = 0 ] && [ "$rc" -ne 0 ]; } || { [ "$want" != 0 ] && [ "$rc" -eq 0 ]; } \
     || ! grep -qF -- "$needle" <<<"$out$(cat "$work/calls")"; then
    fail_case "no-sorry $name: expected exit $want and '$needle', got exit $rc" "$out"
  fi
}

# ---- no-sorry.sh --------------------------------------------------------------------------------
honest_logs
run_nosorry honest 0 'no-sorry: the model and its property theorems is complete'
# Every control the script owns is called, and the kernel replay reaches all three packages.
for called in check-translation-coverage.sh check-lifecycle-translation-coverage.py \
  check-lifecycle-translation-coverage-negatives.sh check-session-satisfiability-negatives.sh \
  check-port-negatives.sh check-initial-dispatch-negatives.py 'attest.py --compare-audit' \
  check-lean-constructs.sh check-audit-reach.sh check-audit-reach-negatives.sh check-pin-negatives.sh check-kernel-replay-negative.sh check-audit-negatives.sh \
  check-precondition-witnesses.sh check-hypothesis-witnesses.sh check-braid-agreement-negatives.sh \
  check-atomicity-negatives.py check-repair-negatives.py \
  check-send-refusal-negatives.py check-sparse-store-full-negatives.py check-decrypt-ratchet-negatives.py \
  'lake build translation' 'lake build tacenta-proofs' 'lake build tacenta-model' \
  'leanchecker translation Translation.Alpha' 'leanchecker translation Translation.Beta' \
  'leanchecker tacenta-proofs Proofs.Gamma' 'leanchecker tacenta-model Model.Delta' \
  'leanchecker tacenta-model Properties.Epsilon'; do
  case "$called" in
    check-translation-coverage.sh) continue ;;  # the real script runs; its own cases are below
  esac
  grep -qF -- "$called" "$work/calls" || fail_case "no-sorry honest: '$called' was not called" "$(cat "$work/calls")"
  cases=$((cases + 1))
done

# A failing control is a failing run, for each control script.
for s in "${sh_controls[@]}" "${py_controls[@]}"; do
  honest_logs
  run_nosorry "a failing $s" nonzero "stub $s fails as asked" STUB_FAIL="$s"
done

# The log scan: a first-party incomplete declaration in each package is a failure; a dependency's is not.
honest_logs
printf 'building\naudit-axiom: Translation.TacentaX axiom foo : Nat\nTranslation/Foo.lean:3:4: warning: declaration uses `sorry`\n' > "$work/logs/translation.log"
run_nosorry 'sorry in the translation package' nonzero 'the translation and its T1/T3 proofs contains an incomplete declaration'
honest_logs
printf 'Proofs/Gamma.lean:3:4: warning: declaration uses `sorry`\n' > "$work/logs/tacenta-proofs.log"
run_nosorry 'sorry in the proofs package' nonzero 'the model-layer proofs contains an incomplete declaration'
honest_logs
printf 'Model/Delta.lean:3:4: warning: declaration uses `sorry`\n' > "$work/logs/tacenta-model.log"
run_nosorry 'sorry in the model package' nonzero 'the model and its property theorems contains an incomplete declaration'
honest_logs
printf 'Properties/Epsilon.lean:3:4: warning: declaration uses `sorry`\n' > "$work/logs/tacenta-model.log"
run_nosorry 'sorry in a property theorem' nonzero 'the model and its property theorems contains an incomplete declaration'
honest_logs
printf 'building\naudit-axiom: Translation.TacentaX axiom foo : Nat\nAeneas/Std/Slice.lean:10:2: warning: declaration uses `sorry`\n.lake/packages/aeneas/Translation/Other.lean:1:1: warning: declaration uses `sorry`\n' > "$work/logs/translation.log"
run_nosorry 'a dependency declaration that uses sorry is not ours' 0 'the translation and its T1/T3 proofs is complete'

# A build that does not succeed stops the script, and the axiom audit must have printed its lines.
honest_logs
: > "$work/logs/translation.fail"
run_nosorry 'a failing translation build' nonzero 'error: build failed'
honest_logs
: > "$work/logs/tacenta-model.fail"
run_nosorry 'a failing model build' nonzero 'error: build failed'
honest_logs
printf 'building\n' > "$work/logs/translation.log"
run_nosorry 'a translation log with no audit lines' nonzero 'the translation build log carries no audit-axiom lines'

# The kernel replay: one module the kernel refuses is a failure, in each package.
for module in Translation.Beta Proofs.Gamma Properties.Epsilon; do
  honest_logs
  run_nosorry "the kernel refuses $module" nonzero "the kernel refused a declaration in" STUB_REPLAY_FAIL="$module"
done

# ---- verify.sh -------------------------------------------------------------------------------------
run_verify() {  # name expected-exit-class needle
  local name="$1" want="$2" needle="$3" out rc
  : > "$work/calls"
  set +e
  out="$(cd "$proofs" && env PATH="$work/bin:$PATH" STUB_CALLS="$work/calls" STUB_LOGS="$work/logs" sh scripts/verify.sh 2>&1)"
  rc=$?
  set -e
  cases=$((cases + 1))
  if { [ "$want" = 0 ] && [ "$rc" -ne 0 ]; } || { [ "$want" != 0 ] && [ "$rc" -eq 0 ]; } \
     || ! grep -qF -- "$needle" <<<"$out"; then
    fail_case "verify $name: expected exit $want and '$needle', got exit $rc" "$out"
  fi
}
honest_logs
run_verify honest 0 'verify: proofs built clean'
printf 'theorem t : True := by sorry\n' > "$proofs/Proofs/Gamma.lean"
run_verify 'a sorry in Proofs' nonzero 'verify: found sorry/admit in Proofs'
printf 'theorem t : True := by admit\n' > "$proofs/Proofs/Gamma.lean"
run_verify 'an admit in Proofs' nonzero 'verify: found sorry/admit in Proofs'
: > "$proofs/Proofs/Gamma.lean"
printf 'theorem sorry_free : True := trivial\n' > "$proofs/Proofs/Gamma.lean"
run_verify 'a name that merely contains sorry is not a use of it' 0 'verify: proofs built clean'
: > "$proofs/Proofs/Gamma.lean"
: > "$work/logs/tacenta-proofs.fail"
run_verify 'a failing build' nonzero 'error: build failed'
honest_logs

# ---- check-translation-coverage.sh ---------------------------------------------------------------------
run_coverage() {  # name expected-exit-class needle
  local name="$1" want="$2" needle="$3" out rc
  set +e
  out="$(cd "$proofs" && bash scripts/check-translation-coverage.sh 2>&1)"
  rc=$?
  set -e
  cases=$((cases + 1))
  if { [ "$want" = 0 ] && [ "$rc" -ne 0 ]; } || { [ "$want" != 0 ] && [ "$rc" -eq 0 ]; } \
     || ! grep -qF -- "$needle" <<<"$out"; then
    fail_case "check-translation-coverage $name: expected exit $want and '$needle', got exit $rc" "$out"
  fi
}
run_coverage honest 0 'translation-coverage: all 2 Translation/*.lean modules are in the build target and built'
: > "$proofs/translation/Translation/Orphan.lean"
run_coverage 'a module with no olean' nonzero 'translation module not built: Translation/Orphan.lean has no olean'
rm "$proofs/translation/Translation/Orphan.lean"
rm "$lib/Beta.olean"
run_coverage 'a built module whose olean is gone' nonzero 'translation module not built: Translation/Beta.lean has no olean'
: > "$lib/Beta.olean"
mkdir -p "$proofs/translation/Translation/Nested"
: > "$proofs/translation/Translation/Nested/Inner.lean"
run_coverage 'a module in a subdirectory' nonzero 'sits in a subdirectory of Translation/'
rm -r "$proofs/translation/Translation/Nested"
printf 'name = "Translation"\n[[lean_lib]]\nname = "Translation"\nglobs = ["Translation.Alpha"]\n' > "$proofs/translation/lakefile.toml"
run_coverage 'a glob narrowed to one module' nonzero 'no longer globs exactly Translation.*'
printf 'name = "Translation"\n[[lean_lib]]\nname = "Translation"\n' > "$proofs/translation/lakefile.toml"
run_coverage 'a library with no glob' nonzero 'no longer globs exactly Translation.*'

echo "proof-script-cases: $cases cases (no-sorry.sh: calls, failing controls, log scan, audit lines, kernel replay; verify.sh; check-translation-coverage.sh) gave the expected result"
