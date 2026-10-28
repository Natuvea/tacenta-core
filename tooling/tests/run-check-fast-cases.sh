#!/usr/bin/env bash
# Cases for the fast local check: `tooling/fast.sh`, the selection it makes in
# `tooling/fast-plan.py`, the fast mode of `tooling/ci.sh` and the opt-in
# `FAST_PRE_PUSH` mode of `.githooks/pre-push`.
#
# Each case builds what it needs in a disposable repository, with stub `cargo`, `lake`, `rustup`
# and (for the real `ci.sh`) `bash`, `sh` and `python3` that log their arguments and exit as told,
# so no toolchain is needed and nothing real is run. A case that fails prints `WRONG  <name>: ...`;
# the runner runs every case and exits 1 if any failed.
#
#   plan-*          the selection from a list of changed paths: Rust only, Lean only, specification
#                   only, workflow only, a manifest change, no change, mixed, a fuzz workspace
#   run-*           the steps run for a real git diff, with the arguments they were given
#   failing-*       a failing sub-check makes the run fail, and does not stop the others
#   run-uncovered   changed Rust no fast check reads ends "ok WITH UNCHECKED", not plain "ok"
#   missing-*       a missing tool prints SKIP and is not an unqualified pass; under
#                   GITHUB_ACTIONS it is a failure
#   ci-skip-*       a skip that a step of `ci.sh --fast` records in FAST_SKIP_LOG is listed under
#                   SKIPPED and ends the run "ok WITH SKIPS"
#   summary-*       the NOT RUN list, the "not CI" line and the wall time are printed, pass or fail
#   ci-fast-*       the real `tooling/ci.sh --fast` runs its cheap steps and none of the heavy ones,
#                   lists its deep_only case runners without --deep (an indented one too) and runs
#                   them with it, CI_FAST=1 in the environment does not make fast mode, and the
#                   same stubs show a run without `--fast` does run them all
#   prereq-*        the prerequisites of the full gate: check-gate-prerequisites.sh names a missing or
#                   broken tool and fails, and asks lake where a lean-toolchain file chooses Lean (a lake that
#                   answers only there passes; without the file, the missing default toolchain is named); `ci.sh` without `--fast` and run-gate-controls.sh fail at their
#                   first line on a PATH without cargo (and without lake, for ci.sh), naming it, before any
#                   step; `ci.sh --fast`, the reduced check, does not ask for them
#   hook-*          the pre-push hook runs the fast check only when asked to
set -euo pipefail

here="$(cd "$(dirname "$0")" && pwd)"
root="$(cd "$here/../.." && pwd)"
real_bash="$(command -v bash)"
work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT
failures=0
cases=0

wrong() {
  echo "WRONG  $1: $2" >&2
  failures=$((failures + 1))
}

# --- tools -------------------------------------------------------------------
# A directory of the real tools the scripts under test need and nothing else, so that "cargo" and
# "lake" are absent from a PATH made of it, whatever the machine has installed.
mkdir -p "$work/tools"
for tool in bash git python3 sed grep awk sort tr cat dirname basename mktemp rm mkdir wc head tail cut \
  env date uname find xargs chmod cp mv ls touch tee diff printf true false sleep readlink expr test; do
  found="$(command -v "$tool" 2>/dev/null || true)"
  case "$found" in
    /*) ln -s "$found" "$work/tools/$tool" ;;
  esac
done

mkdir -p "$work/stubs"
cat > "$work/stubs/cargo" <<'EOF'
#!/bin/sh
echo "cargo ${PWD#"$SANDBOX"/} | $*" >> "$STUB_LOG"
[ "$2" = "--version" ] && exit 0
[ "${STUB_FAIL:-}" = "$1" ] && exit 1
exit 0
EOF
cat > "$work/stubs/lake" <<'EOF'
#!/bin/sh
echo "lake ${PWD#"$SANDBOX"/} | $*" >> "$STUB_LOG"
[ "${STUB_FAIL:-}" = lake ] && exit 1
exit 0
EOF
cat > "$work/stubs/rustup" <<'EOF'
#!/bin/sh
echo "rustup $*" >> "$STUB_LOG"
exit 0
EOF
# For the real ci.sh only: its steps call `bash`, `sh` and `python3` by name. A directory of their
# own, so that the wrapper's cases keep the real ones.
mkdir -p "$work/cistubs"
for name in bash sh python3; do
  cat > "$work/cistubs/$name" <<EOF
#!/bin/sh
echo "$name \$*" >> "\$STUB_LOG"
exit 0
EOF
done
chmod +x "$work"/stubs/* "$work"/cistubs/*

# --- a disposable repository -------------------------------------------------
sandbox="$work/repo"
log="$work/stub.log"
new_sandbox() {
  rm -rf "$sandbox"
  mkdir -p "$sandbox/tooling" "$sandbox/.githooks"
  cp "$root/tooling/fast.sh" "$root/tooling/fast-plan.py" "$sandbox/tooling/"
  cat > "$sandbox/tooling/ci.sh" <<'EOF'
#!/usr/bin/env bash
# stub of tooling/ci.sh for the fast wrapper's cases
case "${1:-}" in
  --fast-not-run)
    [ -f "$SANDBOX/ci-list-broken" ] && exit 1
    echo "  Lean: the translation and its proofs use no sorry"
    echo "  Stub heavy step"
    exit 0 ;;
  --fast)
    echo "ci --fast deep=${FAST_DEEP:-0}" >> "$STUB_LOG"
    [ -f "$SANDBOX/ci-fails" ] && { echo "stub ci: a cheap check failed" >&2; exit 1; }
    [ -f "$SANDBOX/ci-skips" ] && echo "lockfile check of stub/ws: cargo not found" >> "$FAST_SKIP_LOG"
    echo "stub ci: the cheap section passed"
    exit 0 ;;
esac
exit 3
EOF
  cat > "$sandbox/tooling/gate-inventory.py" <<'STUB'
#!/usr/bin/env python3
# stub of tooling/gate-inventory.py for the fast wrapper's cases
import os, sys
with open(os.environ["STUB_LOG"], "a") as log:
    log.write("gate-inventory " + " ".join(sys.argv[1:]) + "\n")
sys.exit(1 if os.path.exists(os.path.join(os.environ["SANDBOX"], "inventory-fails")) else 0)
STUB
  printf '.lake/\n' > "$sandbox/.gitignore"
  mkdir -p "$sandbox/tacenta-core/kem/src" "$sandbox/tacenta-core/wire/src" "$sandbox/tacenta-core/src" \
    "$sandbox/tacenta-core/fuzz/fuzz_targets" "$sandbox/tacenta-test-vectors/runners/rust/src" \
    "$sandbox/tacenta-test-vectors/vectors" "$sandbox/tacenta-spec/pages" "$sandbox/.github/workflows" \
    "$sandbox/tacenta-model/Model" "$sandbox/tacenta-proofs/Proofs" "$sandbox/tacenta-proofs/translation/Translation"
  cat > "$sandbox/tacenta-core/Cargo.toml" <<'EOF'
[workspace]
members = ["kem", "wire"]

[package]
name = "tacenta-core"
EOF
  printf '[package]\nname = "tacenta-kem"\n' > "$sandbox/tacenta-core/kem/Cargo.toml"
  printf '[package]\nname = "tacenta-wire"\n' > "$sandbox/tacenta-core/wire/Cargo.toml"
  printf '[workspace]\n\n[package]\nname = "fuzz"\n' > "$sandbox/tacenta-core/fuzz/Cargo.toml"
  printf '[package]\nname = "tacenta-vectors-rust"\n' > "$sandbox/tacenta-test-vectors/runners/rust/Cargo.toml"
  : > "$sandbox/tacenta-core/Cargo.lock"
  for f in tacenta-core/kem/src/lib.rs tacenta-core/wire/src/lib.rs tacenta-core/src/lib.rs \
    tacenta-core/fuzz/fuzz_targets/t.rs tacenta-test-vectors/runners/rust/src/main.rs \
    tacenta-test-vectors/vectors/v.json tacenta-spec/pages/p.md .github/workflows/ci.yml \
    tacenta-model/Model/A.lean tacenta-proofs/Proofs/B.lean tacenta-proofs/translation/Translation/C.lean \
    tacenta-model/lakefile.lean tooling/check-labels.sh; do
    echo "// base" > "$sandbox/$f"
  done
  # The Lean projects are built (the directories lake would have made).
  mkdir -p "$sandbox/tacenta-model/.lake/build/lib/lean" "$sandbox/tacenta-proofs/.lake/build/lib/lean" \
    "$sandbox/tacenta-proofs/translation/.lake/build/lib/lean" \
    "$sandbox/tacenta-proofs/translation/.lake/packages/mathlib/.lake/build/lib/lean"
  : > "$sandbox/tacenta-proofs/translation/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean"
  git init -q -b main "$sandbox"
  git -C "$sandbox" config user.name 'Control Author'
  git -C "$sandbox" config user.email 'control@example.invalid'
  git -C "$sandbox" add -A
  git -C "$sandbox" commit -q -s -m base
  git -C "$sandbox" tag base
  : > "$log"
}

OUT=""
RC=0
# run_fast PATH-KIND [GITHUB_ACTIONS value] -- args...   (PATH-KIND: with-tools | no-cargo | no-lake | no-tools)
run_fast() {
  local kind="$1" gha="$2" path
  shift 2
  case "$kind" in
    with-tools) path="$work/stubs:$work/tools" ;;
    no-cargo) mkdir -p "$work/nocargo"; ln -sf "$work/stubs/lake" "$work/nocargo/lake"; path="$work/nocargo:$work/tools" ;;
    no-lake) mkdir -p "$work/nolake"; ln -sf "$work/stubs/cargo" "$work/nolake/cargo"; path="$work/nolake:$work/tools" ;;
    no-tools) path="$work/tools" ;;
  esac
  : > "$log"
  set +e
  OUT="$(cd "$sandbox" && env -u GITHUB_ACTIONS -u FAST_DEEP ${gha:+GITHUB_ACTIONS="$gha"} \
    ${DEEP_FOR_RUN:+FAST_DEEP="$DEEP_FOR_RUN"} PATH="$path" SANDBOX="$sandbox" \
    STUB_LOG="$log" STUB_FAIL="${STUB_FAIL:-}" "$real_bash" tooling/fast.sh "$@" 2>&1)"
  RC=$?
  set -e
}

# A here-string, not a pipe: `grep -q` stops reading at the first match, and under pipefail the writer's SIGPIPE
# would make a match read as a miss (it does with the BSD tools and bash 3.2 here, and can with GNU ones).
has_out() { cases=$((cases + 1)); grep -qF -- "$2" <<<"$OUT" || wrong "$1" "output lacks '$2'"; }
lacks_out() { cases=$((cases + 1)); ! grep -qF -- "$2" <<<"$OUT" || wrong "$1" "output has '$2'"; }
has_log() { cases=$((cases + 1)); grep -qF -- "$2" "$log" || wrong "$1" "no stub call '$2' (calls: $(tr '\n' ';' < "$log"))"; }
lacks_log() { cases=$((cases + 1)); ! grep -qF -- "$2" "$log" || wrong "$1" "stub call '$2' was made"; }
rc_is() { cases=$((cases + 1)); [ "$RC" -eq "$2" ] || wrong "$1" "exit $RC, expected $2"; }
rc_not0() { cases=$((cases + 1)); [ "$RC" -ne 0 ] || wrong "$1" "exit 0, expected a failure"; }

# --- plan-*: the selection from changed paths --------------------------------
new_sandbox
plan_of() {  # name, expected plan (newline separated), paths...
  local name="$1" want="$2" got
  cases=$((cases + 1))
  shift 2
  printf '%s\n' "$@" > "$work/paths"
  [ "$#" -eq 0 ] && : > "$work/paths"
  got="$(cd "$sandbox" && "$real_bash" tooling/fast.sh --plan --paths-from "$work/paths" 2>&1 \
    | sed -n '/^fast: plan$/,$p' | sed '1d; s/^  //')"
  if [ "$got" != "$want" ]; then
    wrong "$name" "plan was
$got
expected
$want"
  fi
}
nlj() { local IFS=$'\n'; printf '%s' "$*"; }

plan_of plan-rust-only "$(nlj ci-fast 'rust tacenta-core tacenta-kem,tacenta-wire')" \
  tacenta-core/kem/src/lib.rs tacenta-core/wire/src/lib.rs
plan_of plan-rust-root-package "$(nlj ci-fast 'rust tacenta-core tacenta-core')" tacenta-core/src/lib.rs
plan_of plan-lean-only "$(nlj ci-fast 'lean tacenta-model Model/A.lean' 'lean tacenta-proofs Proofs/B.lean' \
  'lean tacenta-proofs/translation Translation/C.lean')" \
  tacenta-model/Model/A.lean tacenta-proofs/Proofs/B.lean tacenta-proofs/translation/Translation/C.lean
plan_of plan-lean-config "$(nlj ci-fast 'lean-config tacenta-model lakefile.lean')" tacenta-model/lakefile.lean
plan_of plan-spec-only "$(nlj ci-fast 'covered spec')" tacenta-spec/pages/p.md tacenta-test-vectors/vectors/v.json
plan_of plan-workflow-only "$(nlj ci-fast 'covered workflows' deep gate-inventory)" .github/workflows/ci.yml
plan_of plan-tooling-script "$(nlj ci-fast deep gate-inventory 'other 1')" tooling/check-labels.sh
plan_of plan-regenerate-script "$(nlj ci-fast deep 'other 1')" tacenta-proofs/scripts/regenerate-in-container.sh
plan_of plan-gate-inventory-file "$(nlj ci-fast gate-inventory 'other 1')" tacenta-proofs/GATE-INVENTORY.md
plan_of plan-cargo-toml "$(nlj ci-fast 'rust tacenta-core ALL')" tacenta-core/kem/Cargo.toml
plan_of plan-cargo-lock "$(nlj ci-fast 'rust tacenta-core ALL')" tacenta-core/Cargo.lock tacenta-core/kem/src/lib.rs
plan_of plan-vectors-runner "$(nlj ci-fast 'rust tacenta-test-vectors/runners/rust ALL')" \
  tacenta-test-vectors/runners/rust/src/main.rs
plan_of plan-empty-diff "ci-fast"
plan_of plan-rust-config "$(nlj ci-fast 'uncovered tacenta-core 3')" tacenta-core/clippy.toml \
  tacenta-core/.cargo/config.toml tacenta-core/.config/nextest.toml
plan_of plan-root-rust-config "$(nlj ci-fast 'uncovered . 3')" rust-toolchain.toml .cargo/config.toml clippy.toml
plan_of plan-fuzz-workspace "$(nlj ci-fast 'uncovered tacenta-core/fuzz 2')" \
  tacenta-core/fuzz/fuzz_targets/t.rs tacenta-core/fuzz/corpus/a
plan_of plan-markdown-in-a-crate "$(nlj ci-fast 'other 1')" tacenta-core/kem/README.md
plan_of plan-mixed "$(nlj ci-fast 'covered spec' 'lean tacenta-model Model/A.lean' 'rust tacenta-core tacenta-wire')" \
  tacenta-core/wire/src/lib.rs tacenta-model/Model/A.lean tacenta-spec/pages/p.md

# --- run-*: the steps for a real git diff ------------------------------------
new_sandbox
echo '// changed' >> "$sandbox/tacenta-core/kem/src/lib.rs"
run_fast with-tools "" --base base
rc_is run-rust-only 0
has_log run-rust-only-ci "ci --fast"
has_log run-rust-only-fmt "cargo tacenta-core | fmt --check -p tacenta-kem"
has_log run-rust-only-clippy "cargo tacenta-core | clippy --locked --all-targets --quiet -p tacenta-kem -- -D warnings"
has_log run-rust-only-test "cargo tacenta-core | test --locked --quiet -p tacenta-kem"
lacks_log run-rust-only-no-wire "tacenta-wire"
lacks_log run-rust-only-no-lake "lake "
has_out run-rust-only "fast: ok (no step that ran failed"

# A new, untracked file is part of the diff.
new_sandbox
echo '// new' > "$sandbox/tacenta-core/wire/src/extra.rs"
run_fast with-tools "" --base base
has_log run-untracked-file "cargo tacenta-core | test --locked --quiet -p tacenta-wire"

# A change committed on the branch is part of the diff, and one already staged too.
new_sandbox
echo '// committed' >> "$sandbox/tacenta-core/wire/src/lib.rs"
git -C "$sandbox" commit -q -a -s -m 'change wire'
echo '// staged' >> "$sandbox/tacenta-core/kem/src/lib.rs"
git -C "$sandbox" add -A
run_fast with-tools "" --base base
has_log run-committed-change "cargo tacenta-core | fmt --check -p tacenta-kem -p tacenta-wire"

new_sandbox
echo '// changed' >> "$sandbox/tacenta-core/kem/Cargo.toml"
run_fast with-tools "" --base base
has_log run-cargo-toml-whole-workspace "cargo tacenta-core | clippy --locked --all-targets --quiet --workspace -- -D warnings"
has_log run-cargo-toml-test-whole "cargo tacenta-core | test --locked --quiet --workspace"

new_sandbox
echo '-- changed' >> "$sandbox/tacenta-model/Model/A.lean"
run_fast with-tools "" --base base
rc_is run-lean-only 0
has_log run-lean-only "lake tacenta-model | env lean Model/A.lean"
lacks_log run-lean-only-no-cargo "cargo "
has_log run-lean-only-ci "ci --fast"
has_out run-lean-only "fast: ok (no step that ran failed"

new_sandbox
echo '-- changed' >> "$sandbox/tacenta-proofs/translation/Translation/C.lean"
run_fast with-tools "" --base base
has_log run-lean-translation "lake tacenta-proofs/translation | env lean Translation/C.lean"

# A change under tooling/ or .github/ also runs the gate-inventory check, and it can fail the run.
new_sandbox
echo '# changed' >> "$sandbox/tooling/check-labels.sh"
run_fast with-tools "" --base base
rc_is run-tooling-change 0
has_log run-tooling-change-inventory "gate-inventory --check"
has_log run-tooling-change-ci "ci --fast"
has_log run-tooling-change-deep "ci --fast deep=1"
touch "$sandbox/inventory-fails"
run_fast with-tools "" --base base
rc_is failing-gate-inventory 1
has_out failing-gate-inventory-named "tooling/gate-inventory.py --check"
has_log failing-gate-inventory-ci-ran "ci --fast"
rm -f "$sandbox/inventory-fails"

new_sandbox
echo 'changed' >> "$sandbox/tacenta-spec/pages/p.md"
echo '{}' > "$sandbox/tacenta-test-vectors/vectors/v.json"
run_fast with-tools "" --base base
rc_is run-spec-only 0
has_log run-spec-only-ci "ci --fast"
lacks_log run-spec-only-no-cargo "cargo "
lacks_log run-spec-only-no-inventory "gate-inventory"
lacks_log run-spec-only-no-lake "lake "
has_log run-spec-only-not-deep "ci --fast deep=0"

new_sandbox
run_fast with-tools "" --base base
rc_is run-empty-diff 0
has_log run-empty-diff-ci "ci --fast"
lacks_log run-empty-diff-no-cargo "cargo "
lacks_log run-empty-diff-no-lake "lake "
has_out run-empty-diff "0 changed path(s)"
has_log run-empty-diff-not-deep "ci --fast deep=0"

# Changed Rust that no fast check reads is listed and the verdict is not the plain "ok".
new_sandbox
echo '// changed' >> "$sandbox/tacenta-core/fuzz/fuzz_targets/t.rs"
run_fast with-tools "" --base base
rc_is run-uncovered 0
has_out run-uncovered-listed "NOT CHECKED"
has_out run-uncovered-verdict "fast: ok WITH UNCHECKED"
lacks_out run-uncovered-not-plain "fast: ok (no step that ran failed"
run_fast with-tools "" --base base --deep
has_log run-empty-diff-deep-flag "ci --fast deep=1"
DEEP_FOR_RUN=1 run_fast with-tools "" --base base
has_log run-empty-diff-deep-env "ci --fast deep=1"

new_sandbox
run_fast with-tools "" --base no-such-ref
rc_is run-missing-base 1
has_out run-missing-base "does not exist here"
lacks_log run-missing-base-nothing-ran "ci --fast"

# --- failing-*: a failing sub-check fails the run, and the rest still run ----
new_sandbox
echo '// changed' >> "$sandbox/tacenta-core/kem/src/lib.rs"
echo '-- changed' >> "$sandbox/tacenta-model/Model/A.lean"
for failing in fmt clippy test; do
  STUB_FAIL="$failing" run_fast with-tools "" --base base
  rc_is "failing-cargo-$failing" 1
  has_out "failing-cargo-$failing" "fast: FAILED"
  has_out "failing-cargo-$failing-named" "cargo $failing"
  has_log "failing-cargo-$failing-rest-ran" "lake tacenta-model | env lean Model/A.lean"
  has_log "failing-cargo-$failing-ci-ran" "ci --fast"
done
STUB_FAIL=lake run_fast with-tools "" --base base
rc_is failing-lake 1
has_out failing-lake "lake env lean tacenta-model/Model/A.lean"
touch "$sandbox/ci-fails"
STUB_FAIL="" run_fast with-tools "" --base base
rc_is failing-ci-fast 1
has_out failing-ci-fast "FAILED:"
has_out failing-ci-fast-named "tooling/ci.sh --fast"
has_log failing-ci-fast-rest-ran "cargo tacenta-core | test --locked --quiet -p tacenta-kem"
has_out failing-ci-fast-notrun "NOT RUN"
rm -f "$sandbox/ci-fails"

# --- missing-*: a tool the diff needs is absent ------------------------------
new_sandbox
echo '// changed' >> "$sandbox/tacenta-core/kem/src/lib.rs"
run_fast no-cargo "" --base base
rc_is missing-cargo-local 0
has_out missing-cargo-local "fast: SKIP rust checks: cargo not found"
has_out missing-cargo-local-verdict "fast: ok WITH SKIPS"
lacks_out missing-cargo-local-not-plain-ok "fast: ok (no step"
has_out missing-cargo-local-listed "SKIPPED"
run_fast no-cargo true --base base
rc_not0 missing-cargo-in-ci
has_out missing-cargo-in-ci "this is CI -- a check that cannot run is a failure"
has_out missing-cargo-in-ci-failed "fast: FAILED"
lacks_out missing-cargo-in-ci-not-ok "fast: ok"

new_sandbox
echo '-- changed' >> "$sandbox/tacenta-model/Model/A.lean"
run_fast no-lake "" --base base
rc_is missing-lake-local 0
has_out missing-lake-local "fast: SKIP lake env lean: lake not found"
has_out missing-lake-local-verdict "fast: ok WITH SKIPS"
run_fast no-lake true --base base
rc_not0 missing-lake-in-ci
has_out missing-lake-in-ci "a failure, not a skip"

# A project with no build is a skip too, and lake is not run against it.
rm -rf "$sandbox/tacenta-model/.lake"
run_fast with-tools "" --base base
rc_is missing-lean-build-local 0
has_out missing-lean-build-local "SKIP lake env lean tacenta-model/Model/A.lean: no build of tacenta-model"
lacks_log missing-lean-build-no-lake "lake tacenta-model"
run_fast with-tools true --base base
rc_not0 missing-lean-build-in-ci

new_sandbox
echo '-- changed' >> "$sandbox/tacenta-proofs/translation/Translation/C.lean"
rm -f "$sandbox/tacenta-proofs/translation/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean"
run_fast with-tools "" --base base
has_out missing-mathlib-cache "the translation's Mathlib cache is not fetched"
lacks_log missing-mathlib-cache-no-lake "lake tacenta-proofs/translation"
has_out missing-mathlib-cache-verdict "fast: ok WITH SKIPS"

# A skip inside the cheap section (the offline lockfile check writes FAST_SKIP_LOG) is a skip of this run.
new_sandbox
touch "$sandbox/ci-skips"
run_fast with-tools "" --base base
rc_is ci-skip-local 0
has_out ci-skip-local "fast: SKIP in tooling/ci.sh --fast: lockfile check of stub/ws: cargo not found"
has_out ci-skip-listed "SKIPPED (the diff or the cheap section asked for these"
has_out ci-skip-verdict "fast: ok WITH SKIPS"
lacks_out ci-skip-not-plain-ok "fast: ok (no step that ran failed"
rm -f "$sandbox/ci-skips"
run_fast with-tools "" --base base
lacks_out ci-skip-none "SKIP in tooling/ci.sh --fast"

# A diff that needs neither tool is not held up by their absence.
new_sandbox
echo 'changed' >> "$sandbox/tacenta-spec/pages/p.md"
run_fast no-tools "" --base base
rc_is missing-tools-not-needed 0
has_out missing-tools-not-needed "fast: ok (no step that ran failed"

# --- summary-*: always printed, pass or fail ---------------------------------
new_sandbox
run_fast with-tools "" --base base
has_out summary-not-run "NOT RUN"
has_out summary-not-run-list "Lean: the translation and its proofs use no sorry"
has_out summary-not-run-extras "the CI-only steps"
has_out summary-not-ci "fast: this is not CI"
has_out summary-wall-time "fast: wall time"
touch "$sandbox/ci-fails"
run_fast with-tools "" --base base
rc_is summary-on-failure 1
has_out summary-not-run-on-failure "NOT RUN"
has_out summary-not-ci-on-failure "fast: this is not CI"
rm -f "$sandbox/ci-fails"
touch "$sandbox/ci-list-broken"
run_fast with-tools "" --base base
rc_not0 summary-unreadable-list
has_out summary-unreadable-list "could not be read from tooling/ci.sh"

# --- ci-fast-*: the real fast mode of ci.sh ----------------------------------
ci_sandbox="$work/ci"
rm -rf "$ci_sandbox"
mkdir -p "$ci_sandbox/tooling" "$ci_sandbox/tacenta-model" "$ci_sandbox/tacenta-proofs/scripts" \
  "$ci_sandbox/tacenta-core"
cp "$root/tooling/ci.sh" "$ci_sandbox/tooling/ci.sh"
printf '#!/bin/sh\necho "verify.sh" >> "$STUB_LOG"\n' > "$ci_sandbox/tacenta-proofs/scripts/verify.sh"
chmod +x "$ci_sandbox/tacenta-proofs/scripts/verify.sh"
run_ci() {  # args... ; env passes through
  : > "$log"
  set +e
  OUT="$(cd "$ci_sandbox" && env -u GITHUB_ACTIONS -u CI_FAST -u FAST_DEEP ${CI_FAST_FOR_RUN:+CI_FAST="$CI_FAST_FOR_RUN"} \
    ${DEEP_FOR_RUN:+FAST_DEEP="$DEEP_FOR_RUN"} \
    PATH="$work/cistubs:$work/stubs:$work/tools" SANDBOX="$ci_sandbox" STUB_LOG="$log" PROPTEST_CASES=1 \
    "$real_bash" tooling/ci.sh "$@" 2>&1)"
  RC=$?
  set -e
}
heavy_calls="lake tacenta-model | build
verify.sh
python3 tacenta-proofs/scripts/attest.py --check
bash tacenta-proofs/scripts/check-attest-negatives.sh
bash tooling/check-vectors-current.sh
bash tooling/check-constant-time-asm.sh
cargo "
cheap_calls="bash tooling/check-signoff.sh origin/main
bash tooling/check-lockfiles.sh
python3 tooling/check-vectors.py
python3 tooling/check-traceability.py
bash tooling/check-workflows.sh
python3 tooling/check-proof-module-preflight.py --all
python3 tacenta-test-vectors/runners/independent/reader/run.py"
# The slow case runners fast mode runs only with --deep (the full run always runs them).
deep_calls="bash tooling/tests/run-check-workflows-cases.sh
bash tooling/tests/run-lockfile-check-cases.sh
bash tooling/tests/run-regenerate-in-container-cases.sh
bash tooling/tests/run-build-assurance-manifest-cases.sh
bash tooling/tests/run-collect-assurance-receipts-cases.sh
bash tooling/tests/run-build-evidence-pack-cases.sh
bash tooling/tests/run-check-ledger-review-receipt-cases.sh"

for mode in flag; do
  CI_FAST_FOR_RUN="" run_ci --fast
  rc_is "ci-fast-$mode" 0
  has_out "ci-fast-$mode-summary" "fast mode: not run (the steps below this point"
  has_out "ci-fast-$mode-lists-translation" "Lean: the translation and its proofs use no sorry"
  has_out "ci-fast-$mode-lists-attest" "Claims and attestations cover what ships"
  has_out "ci-fast-$mode-not-the-gate" "fast mode: this is not the gate"
  lacks_out "ci-fast-$mode-no-green-line" "ci: all checks green"
  while IFS= read -r call; do
    [ -n "$call" ] && { has_log "ci-fast-$mode-cheap-step" "$call"; }
  done <<EOF
$cheap_calls
EOF
  while IFS= read -r call; do
    [ -n "$call" ] && { lacks_log "ci-fast-$mode-heavy-step" "$call"; }
  done <<EOF
$heavy_calls
EOF
  lacks_log "ci-fast-$mode-no-rustup" "rustup"
  lacks_log "ci-fast-$mode-no-prerequisites" "bash tooling/check-gate-prerequisites.sh"
  has_out "ci-fast-$mode-lists-prerequisites" "(fast mode never runs it; the full gate does)"
  while IFS= read -r call; do
    [ -n "$call" ] && { lacks_log "ci-fast-$mode-deep-step-not-run" "$call"; \
      has_out "ci-fast-$mode-deep-step-listed" "${call#bash } (fast mode runs it only with --deep)"; }
  done <<EOF
$deep_calls
EOF
done

# With --deep (or FAST_DEEP=1) fast mode runs them, still none of the heavy steps, and does not list them.
for mode in flag env; do
  if [ "$mode" = flag ]; then
    CI_FAST_FOR_RUN="" run_ci --fast --deep
  else
    CI_FAST_FOR_RUN="" DEEP_FOR_RUN=1 run_ci --fast
  fi
  rc_is "ci-fast-deep-$mode" 0
  while IFS= read -r call; do
    [ -n "$call" ] && { has_log "ci-fast-deep-$mode-runs" "$call"; \
      lacks_out "ci-fast-deep-$mode-not-listed" "${call#bash } (fast mode runs it only with --deep)"; }
  done <<EOF
$deep_calls
EOF
  lacks_log "ci-fast-deep-$mode-no-heavy" "verify.sh"
done

# CI_FAST=1 in the environment does not make fast mode: only the flag does, so the gate cannot end green on
# its cheap part by a variable left in an environment.
CI_FAST_FOR_RUN=1 run_ci
rc_is ci-env-not-fast 0
has_out ci-env-not-fast-green-line "ci: all checks green"
lacks_out ci-env-not-fast-no-fast-line "fast mode: not run"
has_log ci-env-not-fast-heavy-step "verify.sh"

# The same stubs without the switch run the heavy steps and end on the gate's own line: the control
# that the instrument above can see a heavy step at all.
CI_FAST_FOR_RUN="" run_ci
rc_is ci-full-control 0
has_out ci-full-control "ci: all checks green"
has_log ci-full-control-prerequisites "bash tooling/check-gate-prerequisites.sh the full gate (tooling/ci.sh) git python3 cargo cargo-fmt cargo-clippy lake"
lacks_out ci-full-control-no-fast-line "fast mode: not run"
while IFS= read -r call; do
  [ -n "$call" ] && { has_log "ci-full-control-heavy-step" "$call"; }
done <<EOF
$heavy_calls
EOF
while IFS= read -r call; do
  [ -n "$call" ] && { has_log "ci-full-control-deep-step" "$call"; }
done <<EOF
$deep_calls
EOF

CI_FAST_FOR_RUN="" run_ci --fast-not-run
rc_is ci-fast-not-run 0
has_out ci-fast-not-run-list "Lean: build the model"
lacks_out ci-fast-not-run-excludes-cheap "Workflows parse"
has_out ci-fast-not-run-lists-deep "tooling/tests/run-build-evidence-pack-cases.sh (fast mode runs it only with --deep)"
has_out ci-fast-not-run-lists-full-only 'bash tooling/check-gate-prerequisites.sh "the full gate (tooling/ci.sh)" git python3 cargo cargo-fmt cargo-clippy lake (fast mode never runs it; the full gate does)'
CI_FAST_FOR_RUN="" run_ci --fast-not-run --deep
has_out ci-fast-not-run-deep-list "Lean: build the model"
lacks_out ci-fast-not-run-deep-omits "(fast mode runs it only with --deep)"
# A deep_only call indented inside an `if` is listed too.
cp "$ci_sandbox/tooling/ci.sh" "$work/ci.sh.saved"
python3 - "$ci_sandbox/tooling/ci.sh" <<'PY'
import sys
path = sys.argv[1]
t = open(path).read()
old = "\ndeep_only bash tooling/tests/run-check-ledger-review-receipt-cases.sh\n"
assert old in t
t = t.replace(old, "\nif true; then\n  deep_only bash tooling/tests/run-check-ledger-review-receipt-cases.sh\nfi\n")
open(path, "w").write(t)
PY
CI_FAST_FOR_RUN="" run_ci --fast-not-run
has_out ci-fast-not-run-indented-deep "tooling/tests/run-check-ledger-review-receipt-cases.sh (fast mode runs it only with --deep)"
cp "$work/ci.sh.saved" "$ci_sandbox/tooling/ci.sh"
[ ! -s "$log" ] || wrong ci-fast-not-run-runs-nothing "stub calls were made: $(tr '\n' ';' < "$log")"

# --- prereq-*: the full gate's prerequisites ---------------------------------
pre_sandbox="$work/prereq"
rm -rf "$pre_sandbox"
mkdir -p "$pre_sandbox/tooling/tests" "$work/brokencargo"
cp "$root/tooling/ci.sh" "$root/tooling/check-gate-prerequisites.sh" "$root/tooling/retry-download.sh" "$pre_sandbox/tooling/"
mkdir -p "$pre_sandbox/tacenta-model" "$work/pkglake"
echo 'leanprover/lean4:v4.31.0' > "$pre_sandbox/tacenta-model/lean-toolchain"
# A lake as elan's proxy behaves with no default toolchain: it answers only where a lean-toolchain file chooses Lean.
cat > "$work/pkglake/lake" <<'STUB'
#!/bin/sh
if [ -f lean-toolchain ]; then echo "Lake version 5.0.0 (stub)"; exit 0; fi
echo "error: no default toolchain configured. run \`elan default stable\` to install & configure the latest Lean 4 stable release." >&2
exit 1
STUB
chmod +x "$work/pkglake/lake"
cp "$root/tooling/tests/run-gate-controls.sh" "$root/tooling/tests/with-no-git-identity.sh" "$pre_sandbox/tooling/tests/"
git init -q "$pre_sandbox"
printf '#!/bin/sh\nexit 1\n' > "$work/brokencargo/cargo"
chmod +x "$work/brokencargo/cargo"
run_pre() {  # PATH, then the command (run from the sandbox)
  local path="$1"
  shift
  : > "$log"
  set +e
  OUT="$(cd "$pre_sandbox" && env -u GITHUB_ACTIONS -u FAST_DEEP -u GATE_NO_GIT_IDENTITY PATH="$path" STUB_LOG="$log" \
    SANDBOX="$pre_sandbox" GATE_CONTROLS_PROBE_ONLY=1 "$real_bash" "$@" 2>&1)"
  RC=$?
  set -e
}
run_pre "$work/tools" tooling/check-gate-prerequisites.sh "a test gate" git cargo
rc_is prereq-missing 1
has_out prereq-missing "a test gate needs cargo, which is not on PATH: install a stable Rust toolchain"
has_out prereq-missing "This is a failure, not a skip"
lacks_out prereq-missing-git-present "needs git"
run_pre "$work/brokencargo:$work/tools" tooling/check-gate-prerequisites.sh "a test gate" git cargo
rc_is prereq-broken 1
has_out prereq-broken "a test gate needs cargo, which is on PATH but does not run"
run_pre "$work/stubs:$work/tools" tooling/check-gate-prerequisites.sh "a test gate" git cargo
rc_is prereq-present-first 0
run_pre "$work/tools" tooling/check-gate-prerequisites.sh "a test gate"
rc_is prereq-no-tools 2
has_out prereq-no-tools "give the gate's name and at least one tool"
run_pre "$work/stubs:$work/tools" tooling/check-gate-prerequisites.sh "a test gate" git cargo
rc_is prereq-present 0
has_out prereq-present "a test gate: git cargo present"
# lake is asked where a lean-toolchain file chooses Lean, so elan with no default toolchain (as install-elan.sh
# leaves it) passes; without that file the message names the missing default, not a missing lake.
run_pre "$work/pkglake:$work/tools" tooling/check-gate-prerequisites.sh "a test gate" git lake
rc_is prereq-lake-in-package 0
has_out prereq-lake-in-package "a test gate: git lake present"
mv "$pre_sandbox/tacenta-model/lean-toolchain" "$work/lean-toolchain.saved"
run_pre "$work/pkglake:$work/tools" tooling/check-gate-prerequisites.sh "a test gate" git lake
rc_is prereq-lake-no-default 1
has_out prereq-lake-no-default "elan reports no default toolchain configured where it was asked"
has_out prereq-lake-no-default-shown "no default toolchain configured. run"
mv "$work/lean-toolchain.saved" "$pre_sandbox/tacenta-model/lean-toolchain"
# The full ci.sh stops at its first line without cargo and lake, naming both, before its first step.
run_pre "$work/tools" tooling/ci.sh
rc_is prereq-ci-full 1
has_out prereq-ci-full "the full gate (tooling/ci.sh) needs cargo, which is not on PATH"
has_out prereq-ci-full "the full gate (tooling/ci.sh) needs lake, which is not on PATH"
lacks_out prereq-ci-full-before-steps "== Workflows parse =="
lacks_out prereq-ci-full-no-green "ci: all checks green"
# Fast mode is the reduced check: it does not ask for them (it fails here only because the sandbox lacks its steps).
run_pre "$work/tools" tooling/ci.sh --fast
lacks_out prereq-ci-fast-not-required "needs cargo"
has_out prereq-ci-fast-says-not-run "fast mode: not running bash tooling/check-gate-prerequisites.sh"
has_out prereq-ci-fast-runs-steps "== Workflows parse =="
# The gate controls stop before the identity probe without cargo, and reach it with one.
run_pre "$work/tools" tooling/tests/run-gate-controls.sh
rc_is prereq-controls 1
has_out prereq-controls "the gate controls (run-gate-controls.sh) needs cargo, which is not on PATH"
lacks_out prereq-controls-before-probe "no git identity here"
run_pre "$work/stubs:$work/tools" tooling/tests/run-gate-controls.sh
rc_is prereq-controls-present 0
has_out prereq-controls-present "no git identity here, as on the hosted runner"

# --- hook-*: the pre-push hook ------------------------------------------------
hook_sandbox="$work/hook"
rm -rf "$hook_sandbox"
mkdir -p "$hook_sandbox/tooling" "$hook_sandbox/.githooks"
cp "$root/.githooks/pre-push" "$hook_sandbox/.githooks/pre-push"
printf '#!/bin/sh\necho "check-workflows" >> "$STUB_LOG"\n' > "$hook_sandbox/tooling/check-workflows.sh"
printf '#!/bin/sh\necho "fast" >> "$STUB_LOG"\n[ -f "$SANDBOX/fast-fails" ] && exit 1\nexit 0\n' > "$hook_sandbox/tooling/fast.sh"
git init -q -b main "$hook_sandbox"
run_hook() {
  : > "$log"
  set +e
  OUT="$(cd "$hook_sandbox" && env -u FAST_PRE_PUSH ${1:+FAST_PRE_PUSH="$1"} PATH="$work/tools" SANDBOX="$hook_sandbox" \
    STUB_LOG="$log" "$real_bash" .githooks/pre-push 2>&1)"
  RC=$?
  set -e
}
run_hook ""
rc_is hook-default 0
has_log hook-default-workflows "check-workflows"
lacks_log hook-default-no-fast "fast"
run_hook 1
rc_is hook-opt-in 0
has_log hook-opt-in-workflows "check-workflows"
has_log hook-opt-in-fast "fast"
touch "$hook_sandbox/fast-fails"
run_hook 1
rc_not0 hook-opt-in-blocks-a-failing-push
run_hook ""
rc_is hook-default-ignores-fast-failure 0

if [ "$failures" -ne 0 ]; then
  echo "run-check-fast-cases: $failures case(s) went wrong" >&2
  exit 1
fi
echo "run-check-fast-cases: $cases checks (selection from changed paths, the steps run for a git diff, failing, missing-tool and CI cases, the summary, a skip inside ci.sh --fast, ci.sh --fast against the full run, with and without --deep, the full gate's prerequisites, the pre-push opt-in) gave the expected result"
