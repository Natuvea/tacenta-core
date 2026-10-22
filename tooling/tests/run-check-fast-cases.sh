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
#   missing-*       a missing tool prints SKIP and is not an unqualified pass; under
#                   GITHUB_ACTIONS it is a failure
#   summary-*       the NOT RUN list, the "not CI" line and the wall time are printed, pass or fail
#   ci-fast-*       the real `tooling/ci.sh --fast` runs its cheap steps and none of the heavy ones,
#                   and the same stubs show a run without `--fast` does run them
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
    echo "ci --fast" >> "$STUB_LOG"
    [ -f "$SANDBOX/ci-fails" ] && { echo "stub ci: a cheap check failed" >&2; exit 1; }
    echo "stub ci: the cheap section passed"
    exit 0 ;;
esac
exit 3
EOF
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
    tacenta-model/lakefile.lean; do
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
  OUT="$(cd "$sandbox" && env -u GITHUB_ACTIONS ${gha:+GITHUB_ACTIONS="$gha"} PATH="$path" SANDBOX="$sandbox" \
    STUB_LOG="$log" STUB_FAIL="${STUB_FAIL:-}" "$real_bash" tooling/fast.sh "$@" 2>&1)"
  RC=$?
  set -e
}

has_out() { cases=$((cases + 1)); printf '%s\n' "$OUT" | grep -qF -- "$2" || wrong "$1" "output lacks '$2'"; }
lacks_out() { cases=$((cases + 1)); ! printf '%s\n' "$OUT" | grep -qF -- "$2" || wrong "$1" "output has '$2'"; }
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
plan_of plan-workflow-only "$(nlj ci-fast 'covered workflows')" .github/workflows/ci.yml
plan_of plan-cargo-toml "$(nlj ci-fast 'rust tacenta-core ALL')" tacenta-core/kem/Cargo.toml
plan_of plan-cargo-lock "$(nlj ci-fast 'rust tacenta-core ALL')" tacenta-core/Cargo.lock tacenta-core/kem/src/lib.rs
plan_of plan-vectors-runner "$(nlj ci-fast 'rust tacenta-test-vectors/runners/rust ALL')" \
  tacenta-test-vectors/runners/rust/src/main.rs
plan_of plan-empty-diff "ci-fast"
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

new_sandbox
echo 'changed' >> "$sandbox/tacenta-spec/pages/p.md"
echo '{}' > "$sandbox/tacenta-test-vectors/vectors/v.json"
run_fast with-tools "" --base base
rc_is run-spec-only 0
has_log run-spec-only-ci "ci --fast"
lacks_log run-spec-only-no-cargo "cargo "
lacks_log run-spec-only-no-lake "lake "

new_sandbox
run_fast with-tools "" --base base
rc_is run-empty-diff 0
has_log run-empty-diff-ci "ci --fast"
lacks_log run-empty-diff-no-cargo "cargo "
lacks_log run-empty-diff-no-lake "lake "
has_out run-empty-diff "0 changed path(s)"

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
  OUT="$(cd "$ci_sandbox" && env -u GITHUB_ACTIONS -u CI_FAST ${CI_FAST_FOR_RUN:+CI_FAST="$CI_FAST_FOR_RUN"} \
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
python3 tooling/check-vectors.py
python3 tooling/check-traceability.py
bash tooling/check-workflows.sh
python3 tacenta-test-vectors/runners/independent/reader/run.py"

for mode in flag env; do
  if [ "$mode" = flag ]; then
    CI_FAST_FOR_RUN="" run_ci --fast
  else
    CI_FAST_FOR_RUN=1 run_ci
  fi
  rc_is "ci-fast-$mode" 0
  has_out "ci-fast-$mode-summary" "fast mode: not run"
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
done

# The same stubs without the switch run the heavy steps and end on the gate's own line: the control
# that the instrument above can see a heavy step at all.
CI_FAST_FOR_RUN="" run_ci
rc_is ci-full-control 0
has_out ci-full-control "ci: all checks green"
lacks_out ci-full-control-no-fast-line "fast mode: not run"
while IFS= read -r call; do
  [ -n "$call" ] && { has_log "ci-full-control-heavy-step" "$call"; }
done <<EOF
$heavy_calls
EOF

CI_FAST_FOR_RUN="" run_ci --fast-not-run
rc_is ci-fast-not-run 0
has_out ci-fast-not-run-list "Lean: build the model"
lacks_out ci-fast-not-run-excludes-cheap "Workflows parse"
[ ! -s "$log" ] || wrong ci-fast-not-run-runs-nothing "stub calls were made: $(tr '\n' ';' < "$log")"

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
echo "run-check-fast-cases: $cases checks (selection from changed paths, the steps run for a git diff, failing, missing-tool and CI cases, the summary, ci.sh --fast against the full run, the pre-push opt-in) gave the expected result"
