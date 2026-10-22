#!/usr/bin/env bash
# Negative control for `tooling/check-shell-portability.sh`: the gate refuses a pipeline that ends in a
# quiet grep, in every form the cases list, and accepts the safe forms beside it.
#
# Two kinds of case.
#
#   Fixture files under `tooling/tests/check-shell-portability-cases/*.case`, each handed to the gate with
#   `--files`. The first line of a fixture is `# expect: none` (the gate must accept every line) or
#   `# expect: N N ...` (the gate must refuse, and must name exactly those line numbers). A fixture is a
#   `.case` file and not a `.sh` so that the gate, which reads every tracked shell script, does not read
#   the text it is being shown. The `bad-*` fixtures are the forms that race; the `good-*` fixtures are the
#   forms that look like them and do not (a here-string, a grep that reads to the end, a quoted or commented
#   pipe, `grep -e q`, `grep -- -q`, a `case` alternation, `||` and `&&`).
#
#   Tracked-file selection, in a throwaway repository: which files the gate reads when it is given none. A
#   `.sh`, a script with a shell shebang and no extension, a file under `.githooks/`, and a `run:` line in a
#   workflow under `.github/` are read; a Markdown note, a `.case` file, a workflow-shaped file outside
#   `.github/` and a script that is not tracked are not. A tree with no shell script at all is refused,
#   since a gate that finds nothing to read has checked nothing.
#
# A case that goes wrong prints a line that starts `WRONG  `; the runner runs every case and exits 1 at the
# end if any did. It reads the gate as it stands in this tree.
set -euo pipefail

here="$(cd "$(dirname "$0")" && pwd)"
root="$(cd "$here/../.." && pwd)"
checker="$root/tooling/check-shell-portability.sh"
cases="$here/check-shell-portability-cases"
work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT

fail=0
wrong() { fail=$((fail + 1)); echo "WRONG  $1: $2" >&2; }

# run_gate <dir> <args...>: sets out and rc.
run_gate() {
  local dir="$1"
  shift
  set +e
  out="$(cd "$dir" && bash "$checker" "$@" 2>&1)"
  rc=$?
  set -e
}

# lines_named <path>: the line numbers the gate reported for that path, in order, space-separated.
lines_named() {
  awk -F: -v f="$1" '$1 == f { print $2 }' <<<"$out" | tr '\n' ' ' | sed 's/ $//'
}

# 1. The fixtures.
bad=0
good=0
count=0
for f in "$cases"/*.case; do
  [ -e "$f" ] || { wrong fixtures "no fixture file under $cases"; break; }
  name="$(basename "$f" .case)"
  count=$((count + 1))
  header="$(sed -n '1p' "$f")"
  case "$header" in
    '# expect: '*) expect="${header#'# expect: '}" ;;
    *) wrong "$name" "the first line is not '# expect: ...'"; continue ;;
  esac
  case "$name" in
    bad-*) bad=$((bad + 1)); [ "$expect" != none ] || { wrong "$name" "a bad fixture that expects none"; continue; } ;;
    good-*) good=$((good + 1)); [ "$expect" = none ] || { wrong "$name" "a good fixture that expects lines"; continue; } ;;
    *) wrong "$name" "a fixture must be named bad-* or good-*"; continue ;;
  esac
  run_gate "$root" --files "$f"
  got="$(lines_named "$f")"
  if [ "$expect" = none ]; then
    if [ "$rc" -ne 0 ] || [ -n "$got" ]; then
      wrong "$name" "a safe form was refused (exit $rc, lines [$got])"
      printf '%s\n' "$out" >&2
    fi
  else
    if [ "$rc" -eq 0 ]; then
      wrong "$name" "the racy form was accepted (expected lines [$expect])"
    elif [ "$rc" -ne 1 ]; then
      wrong "$name" "refused with exit $rc and not 1"
      printf '%s\n' "$out" >&2
    elif [ "$got" != "$expect" ]; then
      wrong "$name" "the gate reported lines [$got] and not [$expect]"
      printf '%s\n' "$out" >&2
    elif ! grep -qF 'check-shell-portability:' <<<"$out"; then
      wrong "$name" "refused, but without the gate's summary line"
    fi
  fi
done
[ "$bad" -ge 10 ] || wrong fixtures "only $bad bad fixture(s); the set has shrunk"
[ "$good" -ge 5 ] || wrong fixtures "only $good good fixture(s); the set has shrunk"

# 2. Arguments.
run_gate "$root" --files
{ [ "$rc" -eq 2 ] && grep -qF -- '--files needs at least one file' <<<"$out"; } \
  || wrong files-without-a-file "expected exit 2 and a message, got exit $rc"
run_gate "$root" --no-such-option
{ [ "$rc" -eq 2 ] && grep -qF 'unknown argument' <<<"$out"; } \
  || wrong unknown-argument "expected exit 2 and a message, got exit $rc"
run_gate "$root" --files "$work/does-not-exist.sh"
{ [ "$rc" -eq 2 ] && grep -qF 'cannot read' <<<"$out"; } \
  || wrong unreadable-file "a file the gate cannot read must be a failure, not a pass: exit $rc"

# 3. Which tracked files it reads.
repo="$work/repo"
git init -q -b main "$repo"
git -C "$repo" config user.name control
git -C "$repo" config user.email control@example.invalid
mkdir -p "$repo/tooling" "$repo/bin" "$repo/.githooks" "$repo/.github/workflows" "$repo/docs" "$repo/fixtures"
cp "$checker" "$repo/tooling/check-shell-portability.sh"
racy='printf %s "$x" | grep -q y'
select_gate() { out="$(cd "$repo" && bash tooling/check-shell-portability.sh 2>&1)" && rc=0 || rc=$?; }
track() { git -C "$repo" add "$1"; }

# No tracked shell script yet (the gate's own copy is not added): refused as checking nothing.
select_gate
if [ "$rc" -eq 1 ] && grep -qF 'this gate would check nothing' <<<"$out"; then :; else
  wrong no-shell-scripts "a tree with no shell script to read must be refused as checking nothing (exit $rc)"
  printf '%s\n' "$out" >&2
fi

# A clean script is accepted, and is counted.
printf '#!/usr/bin/env bash\nset -euo pipefail\ngrep -q y <<<"$x"\n' >"$repo/clean.sh"
track clean.sh
select_gate
if [ "$rc" -ne 0 ] || ! grep -qF '1 file(s) scanned' <<<"$out"; then
  wrong clean-tree "a tree with one clean script was not accepted and counted (exit $rc)"
  printf '%s\n' "$out" >&2
fi

# Not scripts: none of these is read, so none is refused.
printf '# notes\n\n    %s\n' "$racy" >"$repo/docs/notes.md"
printf '# expect: 2\n%s\n' "$racy" >"$repo/fixtures/bad.case"
printf 'jobs:\n  a:\n    steps:\n      - run: %s\n' "$racy" >"$repo/fixtures/workflow-shaped.yml"
printf 'plain text\n%s\n' "$racy" >"$repo/bin/no-shebang"
printf '#!/usr/bin/env python3\nprint("%s")\n' "$racy" >"$repo/bin/python-tool"
track docs/notes.md
track fixtures/bad.case
track fixtures/workflow-shaped.yml
track bin/no-shebang
track bin/python-tool
printf '#!/usr/bin/env bash\n%s\n' "$racy" >"$repo/untracked.sh"
select_gate
if [ "$rc" -ne 0 ]; then
  wrong not-scripts "a file that is not a tracked shell script was read (exit $rc)"
  printf '%s\n' "$out" >&2
fi
git -C "$repo" add untracked.sh
select_gate
if [ "$rc" -ne 1 ] || ! grep -qF 'untracked.sh:2:' <<<"$out"; then
  wrong tracked-script "a tracked .sh with the racy form was not refused at its line (exit $rc)"
  printf '%s\n' "$out" >&2
fi
git -C "$repo" rm -q --cached -f untracked.sh
rm -f "$repo/untracked.sh"

# A tracked file that has been deleted from the working tree, and a tracked symlink, are skipped and not
# read: neither is a failure.
printf '#!/usr/bin/env bash\n%s\n' "$racy" >"$repo/gone.sh"
track gone.sh
rm -f "$repo/gone.sh"
ln -s docs "$repo/link-to-dir.sh"
track link-to-dir.sh
select_gate
if [ "$rc" -ne 0 ]; then
  wrong deleted-or-symlink "a tracked file that is gone, or a tracked symlink, made the gate fail (exit $rc)"
  printf '%s\n' "$out" >&2
fi
git -C "$repo" rm -q --cached -f gone.sh link-to-dir.sh
rm -f "$repo/link-to-dir.sh"

# Run from a subdirectory, it still reads the whole repository.
printf '#!/usr/bin/env bash\n%s\n' "$racy" >"$repo/top.sh"
track top.sh
out="$(cd "$repo/docs" && bash ../tooling/check-shell-portability.sh 2>&1)" && rc=0 || rc=$?
if [ "$rc" -ne 1 ] || ! grep -qF 'top.sh:2:' <<<"$out"; then
  wrong from-a-subdirectory "run from docs/, the gate did not read the script at the root (exit $rc)"
  printf '%s\n' "$out" >&2
fi
git -C "$repo" rm -q --cached -f top.sh
rm -f "$repo/top.sh"

# Without python3 it cannot run, and that is a failure with a message, not a pass.
mkdir "$work/nobin"
out="$(PATH="$work/nobin" "$BASH" "$checker" --files "$cases/good-safe-forms.case" 2>&1)" && rc=0 || rc=$?
if [ "$rc" -ne 1 ] || ! grep -qF 'python3 not found' <<<"$out"; then
  wrong no-python "with no python3 the gate must fail with a message, not pass or skip (exit $rc)"
  printf '%s\n' "$out" >&2
fi

# Each way a script is recognised, with the racy form on a known line.
planted() {  # name path content
  local name="$1" path="$2" content="$3"
  mkdir -p "$(dirname "$repo/$path")"
  printf '%s' "$content" >"$repo/$path"
  track "$path"
  select_gate
  if [ "$rc" -ne 1 ] || ! grep -qF "$path:" <<<"$out"; then
    wrong "$name" "the racy form in $path was not refused and named (exit $rc)"
    printf '%s\n' "$out" >&2
  fi
  git -C "$repo" rm -q --cached -f "$path"
  rm -f "$repo/$path"
  select_gate
  [ "$rc" -eq 0 ] || wrong "$name-removed" "the tree was not accepted again after $path was removed (exit $rc)"
}
planted bash-extension scripts/a.sh $'set -e\n'"$racy"$'\n'
planted bash-extension-only bin/b.bash $'set -e\n'"$racy"$'\n'
planted zsh-extension bin/c.zsh $'set -e\n'"$racy"$'\n'
planted shebang-without-extension bin/run $'#!/usr/bin/env bash\n'"$racy"$'\n'
planted sh-shebang-without-extension bin/run2 $'#!/bin/sh\n'"$racy"$'\n'
planted zsh-shebang-without-extension bin/run3 $'#!/usr/bin/env zsh\n'"$racy"$'\n'
planted githooks-without-shebang .githooks/pre-commit $'set -e\n'"$racy"$'\n'
planted workflow-run-line .github/workflows/w.yml $'jobs:\n  a:\n    steps:\n      - run: '"$racy"$'\n'
planted workflow-run-block .github/workflows/w2.yaml $'jobs:\n  a:\n    steps:\n      - run: |\n          set -e\n          '"$racy"$'\n'
planted nested-github-dir tacenta-proofs/.github/workflows/v.yml $'jobs:\n  a:\n    steps:\n      - run: '"$racy"$'\n'
planted composite-action .github/actions/x/action.yml $'runs:\n  steps:\n    - run: '"$racy"$'\n      shell: bash\n'

if [ "$fail" -ne 0 ]; then
  echo "check-shell-portability cases: $fail case(s) went wrong" >&2
  exit 1
fi
echo "check-shell-portability cases: $count fixtures ($bad refused at their lines, $good accepted), the argument errors, and the file selection gave the expected result"
