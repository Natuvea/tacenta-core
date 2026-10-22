#!/usr/bin/env bash
# The check to run before every commit: the cheap checks of the gate, plus the
# Rust and Lean checks for the files this change touched, in a few minutes.
#
#   bash tooling/fast.sh                  the diff against origin/main (committed, staged,
#                                         unstaged and untracked files)
#   bash tooling/fast.sh --base REF       the diff against another base (FAST_BASE does the same)
#   bash tooling/fast.sh --plan           print what would run for this diff and run nothing
#   bash tooling/fast.sh --paths-from F   take the changed paths from file F (one per line) instead
#                                         of git; for the case runner
#
# What it runs.
#
#   1. `bash tooling/ci.sh --fast`: the cheap section of the gate, which is every step of
#      `tooling/ci.sh` above its "fast mode stops here" line. That is one list, in that file; this
#      script does not repeat it. It already holds the checks that a change to the specification,
#      the vectors, the independent reader, a workflow or a tooling script needs (the reader, the
#      traceability checker, the vector-schema check, the workflow checkers and their cases), so a
#      diff in those areas adds nothing to run here.
#   2. For the Rust workspaces the diff touches (`tooling/fast-plan.py` decides which, and
#      which packages of each), `cargo fmt --check`, `cargo clippy` and `cargo test` as
#      `tooling/ci.sh` runs them, restricted to the touched packages with `-p`. A change to a
#      Cargo.toml or Cargo.lock selects the whole workspace.
#   3. When a file under tooling/ or .github/ changed, `tooling/gate-inventory.py --check`: every
#      step the required workflow runs has a row in the generated inventory. Hosted CI runs it
#      (through run-gate-controls.sh); no step of `tooling/ci.sh` does.
#   4. For each changed Lean module under tacenta-model, tacenta-proofs or the translation project,
#      `lake env lean <module>` from its project directory, which elaborates that one file against
#      the already-built modules it imports. It needs the project's build; without it the step is
#      skipped, loudly (see below).
#
# What it prints last, always, pass or fail: what ran and how long each took, what failed, what was
# skipped, a NOT RUN list (read from `tooling/ci.sh --fast-not-run` plus the CI-only and
# diff-unreachable steps it names itself), and the wall time. A pass here is not a pass of the
# gate: the full gate (`bash tooling/ci.sh`) and the hosted CI remain authoritative, and the
# last lines say so.
#
# A step the diff asks for and the machine cannot run (no cargo, no lake, no build of the Lean
# project) prints a SKIP line and is listed under SKIPPED, and the final verdict is "ok WITH
# SKIPS", never plain "ok". When GITHUB_ACTIONS is set the same step is a failure, the rule
# `tooling/ci.sh` and its siblings follow: a runner must not report green on a check it did not run.
#
# Exit status: 0 when no step failed, 1 otherwise (including a base that cannot be found).
# Environment: FAST_BASE (default origin/main), PROPTEST_CASES (default 256 here; ci.sh uses 2048).
#
# Limits, stated because they are the ways this can be green while the gate is not:
#
#   * A Rust change is checked in the packages it touches, not in the packages that depend on
#     them; a signature change in a leaf crate can break a caller this does not build.
#   * `lake env lean` checks one module against the modules built before the change; a module
#     that imports a changed module is not re-elaborated, and a changed module imported by another
#     changed one sees the older build of it. `lake build` is the check that follows imports.
#   * The sign-off check (a step of `ci.sh --fast`) reads origin/main whatever `--base` says.
#   * The cases for the selection, the failure rule and the skip rule are
#     `tooling/tests/run-check-fast-cases.sh`.
set -euo pipefail
root="$(cd "$(dirname "$0")/.." && pwd)"
cd "$root"
SECONDS=0

base="${FAST_BASE:-origin/main}"
mode=run
paths_from=""
while [ "$#" -gt 0 ]; do
  case "$1" in
    --base) base="${2:?--base needs a ref}"; shift 2 ;;
    --plan) mode=plan; shift ;;
    --paths-from) paths_from="${2:?--paths-from needs a file}"; shift 2 ;;
    -h|--help) sed -n '2,/^set -euo/p' "$0" | sed '$d' | sed 's/^# \{0,1\}//'; exit 0 ;;
    *) echo "fast: unknown argument $1 (see --help)" >&2; exit 2 ;;
  esac
done

work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT

# --- the changed paths -------------------------------------------------------
merge_base="-"
if [ -n "$paths_from" ]; then
  cp "$paths_from" "$work/paths"
else
  if ! git rev-parse --verify -q "${base}^{commit}" >/dev/null; then
    echo "fast: the base ${base} does not exist here; fetch it (git fetch origin main) or pass --base" >&2
    exit 1
  fi
  merge_base="$(git merge-base "$base" HEAD)" || {
    echo "fast: no merge base between ${base} and HEAD" >&2
    exit 1
  }
  {
    git diff --name-only --no-renames "$merge_base"
    git ls-files --others --exclude-standard
  } | sort -u > "$work/paths"
fi
python3 tooling/fast-plan.py --paths-from "$work/paths" > "$work/plan"
changed="$(wc -l < "$work/paths" | tr -d ' ')"

echo "fast: base ${base} (merge base ${merge_base}), ${changed} changed path(s)"
echo "fast: plan"
sed 's/^/  /' "$work/plan"
if [ "$mode" = plan ]; then
  exit 0
fi

# --- running and recording ---------------------------------------------------
nl='
'
ran=""
failed=""
skipped=""
note_ran() { ran="${ran}${ran:+$nl}$1"; }
note_failed() { failed="${failed}${failed:+$nl}$1"; }
note_skipped() { skipped="${skipped}${skipped:+$nl}$1"; }

# Run one step, keep going after a failure so that one run reports every failing step.
step() {
  local name="$1" started="$SECONDS"
  shift
  echo "== fast: ${name} =="
  if "$@" </dev/null; then
    note_ran "${name} ($((SECONDS - started))s)"
  else
    echo "fast: FAILED: ${name}" >&2
    note_failed "${name}"
  fi
}

# A requested step that cannot run: a skip locally, a failure on a runner.
cannot_run() {
  local name="$1" reason="$2"
  echo "fast: SKIP ${name}: ${reason}" >&2
  if [ "${GITHUB_ACTIONS:-}" = "true" ]; then
    echo "fast: this is CI -- a check that cannot run is a failure, not a skip" >&2
    note_failed "${name} (cannot run: ${reason})"
  else
    note_skipped "${name}: ${reason}"
  fi
}

have_cargo_tools() {
  if ! command -v cargo >/dev/null 2>&1; then
    cannot_run "rust checks" "cargo not found"
    return 1
  fi
  local sub
  for sub in fmt clippy; do
    if ! cargo "$sub" --version >/dev/null 2>&1; then
      cannot_run "rust checks" "cargo ${sub} is not installed (rustup component add)"
      return 1
    fi
  done
}

# --- 1. fmt first: seconds, and the commonest reason to be sent back ---------
if grep -q '^rust ' "$work/plan" && have_cargo_tools; then
  while read -r kind workspace packages; do
    [ "$kind" = rust ] || continue
    pkgs=()
    if [ "$packages" != ALL ]; then
      for p in $(echo "$packages" | tr ',' ' '); do pkgs+=(-p "$p"); done
    fi
    step "cargo fmt --check (${workspace}: ${packages})" \
      bash -c 'cd "$1" && shift && cargo fmt --check "$@"' _ "$workspace" ${pkgs[@]+"${pkgs[@]}"}
  done < "$work/plan"
  rust_ok=1
else
  rust_ok=0
fi

# --- 2. the cheap section of the gate ----------------------------------------
step "tooling/ci.sh --fast (the cheap section)" bash tooling/ci.sh --fast

# --- 2b. the gate inventory, when a gate, a workflow or the inventory itself changed ------
# Hosted CI checks that every step it runs has a row in tacenta-proofs/GATE-INVENTORY.md (the
# last line of run-gate-controls.sh); no step of tooling/ci.sh does.
if grep -qx 'gate-inventory' "$work/plan"; then
  step "tooling/gate-inventory.py --check" python3 tooling/gate-inventory.py --check
fi

# --- 3. clippy and tests of the touched Rust packages ------------------------
if [ "$rust_ok" = 1 ]; then
  export PROPTEST_CASES="${PROPTEST_CASES:-256}"
  while read -r kind workspace packages; do
    [ "$kind" = rust ] || continue
    scope=(--workspace)
    if [ "$packages" != ALL ]; then
      scope=()
      for p in $(echo "$packages" | tr ',' ' '); do scope+=(-p "$p"); done
    fi
    step "cargo clippy (${workspace}: ${packages})" \
      bash -c 'cd "$1" && shift && cargo clippy --locked --all-targets --quiet "$@" -- -D warnings' \
      _ "$workspace" "${scope[@]}"
    step "cargo test (${workspace}: ${packages})" \
      bash -c 'cd "$1" && shift && cargo test --locked --quiet "$@"' _ "$workspace" "${scope[@]}"
  done < "$work/plan"
fi

# --- 4. changed Lean modules -------------------------------------------------
lean_config=""
if grep -q '^lean ' "$work/plan"; then
  if ! command -v lake >/dev/null 2>&1; then
    cannot_run "lake env lean" "lake not found (install elan)"
  else
    while read -r kind project file; do
      [ "$kind" = lean ] || continue
      built="$project/.lake/build/lib/lean"
      if [ ! -d "$built" ]; then
        cannot_run "lake env lean ${project}/${file}" "no build of ${project} (run 'lake build' there)"
      elif [ "$project" = tacenta-proofs/translation ] \
        && [ ! -f "$project/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean" ]; then
        cannot_run "lake env lean ${project}/${file}" \
          "the translation's Mathlib cache is not fetched (cd ${project} && lake exe cache get)"
      elif [ ! -f "$project/$file" ]; then
        echo "fast: ${project}/${file} was deleted; nothing to elaborate"
      else
        step "lake env lean ${project}/${file}" bash -c 'cd "$1" && lake env lean "$2"' _ "$project" "$file"
      fi
    done < "$work/plan"
  fi
fi
while read -r kind project file; do
  [ "$kind" = lean-config ] || continue
  lean_config="${lean_config}${lean_config:+$nl}  ${project}/${file} changed: only a full 'lake build' shows what it did"
done < "$work/plan"

# --- the summary, always -----------------------------------------------------
echo
echo "== fast: summary =="
echo "RAN:"
if [ -n "$ran" ]; then echo "$ran" | sed 's/^/  /'; else echo "  (nothing)"; fi
if [ -n "$failed" ]; then
  echo "FAILED:"
  echo "$failed" | sed 's/^/  /'
fi
if [ -n "$skipped" ]; then
  echo "SKIPPED (the diff asked for these and this machine could not run them):"
  echo "$skipped" | sed 's/^/  /'
fi
if grep -q '^uncovered ' "$work/plan"; then
  echo "NOT CHECKED (changed Rust that no fast check reads):"
  grep '^uncovered ' "$work/plan" | sed 's/^uncovered /  /; s/ \([0-9]*\)$/ (\1 path(s))/'
fi
echo "NOT RUN (the full gate and the hosted CI run these):"
if not_run="$(bash tooling/ci.sh --fast-not-run)" && [ -n "$not_run" ]; then
  echo "$not_run"
else
  echo "  (the list could not be read from tooling/ci.sh; treat every step after its cheap section as not run)"
  note_failed "the NOT RUN list could not be read from tooling/ci.sh"
fi
echo "  Rust packages this diff did not touch, and the packages that depend on those it did"
echo "  the CI-only steps: the SPQR erasure regression, the portable-backend KEM tests, the 32-bit premises run,"
echo "    the gate-inventory and mutation-harness cases (run-gate-controls.sh)"
echo "  hosted jobs: the sliced attestation negatives, the translation parts, the assurance receipts"
echo "  the full 'lake build' of the translation, no-sorry.sh and attest-negatives, MSRV, armv7, cargo audit and the fuzz smoke run"
if [ -n "$lean_config" ]; then
  echo "$lean_config"
fi
echo "fast: wall time ${SECONDS}s"
echo "fast: this is not CI. A pass here does not stand in for 'bash tooling/ci.sh' or the hosted CI, which remain authoritative."
if [ -n "$failed" ]; then
  echo "fast: FAILED"
  exit 1
fi
if [ -n "$skipped" ]; then
  echo "fast: ok WITH SKIPS -- the skipped steps above were not checked"
  exit 0
fi
echo "fast: ok (no step that ran failed; see NOT RUN above)"
