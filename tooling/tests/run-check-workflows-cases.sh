#!/usr/bin/env bash
# Hold `tooling/check-workflows.sh` to its cases.
#
#   bash tooling/tests/run-check-workflows-cases.sh
#
# Each file under `check-workflows-cases/` is one small workflow. A `pass-*`
# file must be accepted; a `fail-*` file must be refused, and refused for the
# stated reason: its first line is `# expect: <text>`, and that text must
# appear in the checker's output, so a case that fails for some other reason
# (a typo that stops it parsing, say) is caught rather than counted. Each
# case is copied into a fresh temporary git repository as its only workflow,
# because the checker walks the tree it is run in from `git rev-parse`.
#
# The checker itself is not changed to run these: it checks the tree it is
# in, and this script is what `tooling/ci.sh` and the workflow's `checks` job
# run right after it, so a regex loosened by mistake fails the gate the same
# push. The cases live here and not under any `.github/workflows` path so the
# real checker never picks them up as workflows of this repository.
set -euo pipefail

here="$(cd "$(dirname "$0")" && pwd)"
root="$(cd "$here/../.." && pwd)"
checker="$root/tooling/check-workflows.sh"
cases="$here/check-workflows-cases"

# The same rule as the checker: without PyYAML the checker skips locally and
# every case would pass, which is not a result. Skip here for the same
# reason, and fail in CI for the same reason the checker does.
if ! command -v python3 >/dev/null 2>&1 || ! python3 -c 'import yaml' >/dev/null 2>&1; then
  echo "check-workflows-cases: python3 with pyyaml not found, skipping (pip install pyyaml)" >&2
  if [ "${GITHUB_ACTIONS:-}" = "true" ]; then
    echo "check-workflows-cases: this is CI -- a check that cannot run is a failure, not a skip" >&2
    exit 1
  fi
  exit 0
fi

work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT

wrong=0
total=0
for case in "$cases"/pass-*.yml "$cases"/fail-*.yml; do
  [ -e "$case" ] || continue
  total=$((total + 1))
  name="$(basename "$case" .yml)"
  repo="$work/$name"
  mkdir -p "$repo/.github/workflows"
  git -C "$repo" init -q
  cp "$case" "$repo/.github/workflows/t.yml"
  set +e
  # Not `GITHUB_ACTIONS`: the checker's own skip-or-fail rule is not under
  # test, and a case must see the same checker a developer's machine does.
  out="$(cd "$repo" && env -u GITHUB_ACTIONS bash "$checker" 2>&1)"
  rc=$?
  set -e
  case "$name" in
    pass-*)
      if [ "$rc" -ne 0 ]; then
        echo "WRONG  $name: expected accepted, was refused:" >&2
        printf '  %s\n' "$out" >&2
        wrong=$((wrong + 1))
      fi
      ;;
    fail-*)
      expect="$(sed -n '1s/^# expect: //p' "$case")"
      if [ -z "$expect" ]; then
        echo "WRONG  $name: a fail case's first line must be '# expect: <text>'" >&2
        wrong=$((wrong + 1))
      elif [ "$rc" -eq 0 ]; then
        echo "WRONG  $name: expected refused ($expect), was accepted" >&2
        wrong=$((wrong + 1))
      elif ! printf '%s' "$out" | grep -qF -- "$expect"; then
        echo "WRONG  $name: refused, but not for '$expect':" >&2
        printf '  %s\n' "$out" >&2
        wrong=$((wrong + 1))
      fi
      ;;
  esac
done

if [ "$wrong" -ne 0 ]; then
  echo "check-workflows-cases: $wrong of $total case(s) gave the wrong result" >&2
  exit 1
fi
echo "check-workflows-cases: $total case(s) gave the expected result"
