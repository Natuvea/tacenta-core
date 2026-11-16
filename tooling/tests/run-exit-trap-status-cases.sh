#!/usr/bin/env bash
# The exit-status guard of the repository's shell scripts, and the tree check that keeps it in every script that
# needs it.
#
# Why. On macOS, /bin/bash 3.2 and /bin/sh (bash 3.2 in POSIX mode) exit 0 when a script running under `set -e`
# is stopped by a shell-fatal error while an EXIT trap whose last command succeeds is set. The errors are the ones
# that stop the shell itself rather than fail one command: an unset variable under `set -u` (an empty array too,
# on bash 3.2), `${x:?}`, sourcing a missing file or one that does not parse, assigning to a readonly variable, a
# bad substitution, an `eval` of a syntax error. Without the trap the same script exits nonzero; `$?` is already 0
# when the trap starts, so `rc=$?; ...; exit $rc` does not help. bash 5 and dash keep the status, so hosted Linux
# CI was not affected; a local run on a Mac could report success after such an abort.
#
# The guard. Every tracked shell script that sets an EXIT trap carries the same block, word for word, above its
# first EXIT trap (the canonical copy is the one in this file), whether or not `set -e` is in sight (see 4):
#
#   finished=no                        set before the trap, so the trap can read it under `set -u`
#   done_ok                            every deliberate early success (`exit 0`) goes through it
#   exit_guard <status>                exits 1 with a message when the status is 0 and `finished` is not yes;
#                                      any other status is kept, so `exit 3` still exits 3
#
# and its EXIT trap is `trap 'exit_guard_rc=$?; set +e; <cleanup>; exit_guard "$exit_guard_rc"' EXIT`, with
# the cleanup it had before unchanged and other signals trapped on a line of their own. `set +e` keeps a failing
# cleanup command from deciding the status. The script's last statement is `finished=yes`, or its success paths
# are done_ok, or `finished=yes` comes right before an `exit "$status"` that ends it. A script that `exec`s
# would set `finished=yes` first (no EXIT trap runs after an exec); none does today. The block is written into
# each script and not sourced from a helper, because a helper that fails to source is itself one of the fatal
# errors the guard is for.
#
# What it does not change: what any gate checks, and the status of an abort under bash 5 or dash. A script's end
# marker (the last line it prints) is still the plainer evidence of a full run; the guard makes the status agree
# with it on bash 3.2 too.
#
# The cases, each a fixture under tooling/tests/exit-trap-status-cases/ rendered with the guard of this file:
#
#   1. Each fatal error above, under each trap shape the tree uses (an inline body, a cleanup function with its
#      own INT/TERM trap, a trap set inside a function whose cleanup clears the traps, the POSIX form under
#      /bin/sh): nonzero, the lines after the error not reached, the cleanup run. An empty array under -u is
#      not an error on bash 4.4 and later; there the case requires the run to go on and pass.
#   2. The same fixtures without the guard, under an unset variable: exit 0 under bash 3.2 (the defect, shown
#      on this machine) and nonzero elsewhere.
#   3. Controls, under every shape: a run to the end exits 0, done_ok exits 0 at once, `exit 3` exits 3, and a
#      plain `exit 0` that bypasses done_ok exits 1 with the guard's message (the case that holds the guard on
#      every shell, since bash 5 never loses the status). Under the inline and POSIX shapes: `finished=yes` and
#      `exit "$s"` keep 0 and 4, and a failing command under `set -e` exits 1. A cleanup whose last command
#      fails changes neither a 0 nor a 3, and an abort still exits nonzero.
#   4. The tree check (exit-trap-status-cases/check-tree.py). It reads every tracked file that is a shell script:
#      a `.sh` or `.bash`, a file under `.githooks/`, a file whose `#!` line runs sh, bash, dash, ksh or zsh
#      (through `env` and its options too, `env -S bash -e` included), and a tracked executable with no `#!`.
#      It is conservative. Any `trap` in command position (at the start of a line, or after `;`, `&&`, `||`,
#      `|`, `{`, `(`, `!`, `then`, `do`, `else`, `command`, `builtin`, `exec` or `time`) must be a plain
#      `trap HANDLER SIGNAL...` line of its own, or the file is refused; signal names are read without regard
#      to case or a SIG prefix, and `0` is EXIT. A line that holds `trap` in command position only once the
#      quoting the shell would remove is taken out (`\trap`, `"trap"`, `t''rap`) is refused the same way. A
#      file with an EXIT trap needs the guard whether or not the check sees `set -e`, since errexit can come
#      from a shebang (`#!/bin/bash -ue`), from `bash -e` in a caller, or from a later line.
#      Refused, with the line: an EXIT trap with no guard; a guard that is not
#      word for word the one here or that comes after the first EXIT trap; an EXIT trap not of the guarded form
#      with EXIT alone (lower case or `0` included); a guarded cleanup that leaves through exit, exec or return;
#      a `finished=yes` that is not the last line of code and not right before an `exit` (or any other write
#      of `finished`); and no such `finished=yes` and no done_ok after the trap. The tree-*.case fixtures are
#      its negative and positive cases, then file selection in a throwaway repository, then the tree itself.
#      Two scripts are exempt by name, below, with the reason, and that list is the only escape; an exemption
#      that no longer names an exposed, unguarded script is refused.
#      Not seen: a trap set through `eval`, an alias, a variable or a function named otherwise; a cleanup
#      function that itself calls exit (only the trap's own text is read); a `trap` word inside quotes or a
#      heredoc is read as code (so a fixture that holds one lives in a `.case` file); a shell script that is
#      untracked, not executable and has neither a shell extension nor a shell `#!` line; a script run by
#      another interpreter than its `#!` names; anything a sourced file does at run time; and a spelling of the
#      word built at run time or by quoting other than the three forms above.
#      It is a tripwire against accidents, not against a determined edit: a script that sets `finished` by
#      other means (`printf -v finished yes`, `read`, `declare`) or redefines exit_guard or done_ok after the
#      guard defeats it, and the check does not look for either.
#
# A case that goes wrong prints a line that starts `WRONG  `; the runner runs every case, checks the number of
# cases against the count pinned below, and exits 1 at the end if anything went wrong.
set -euo pipefail
# Exit-status guard. With an EXIT trap set, macOS /bin/bash 3.2 and /bin/sh exit 0 when a shell-fatal error
# (an unset variable under -u, ${x:?}, a missing sourced file) stops a `set -e` script, so the trap refuses a
# run that reached neither `finished=yes` nor done_ok. Cases: tooling/tests/run-exit-trap-status-cases.sh.
finished=no
done_ok() { finished=yes; exit 0; }
exit_guard() {  # <status the EXIT trap began with>
  if [ "$1" -eq 0 ] && [ "$finished" != yes ]; then
    echo "$0: stopped before its end with status 0 (a shell-fatal error, a signal, or exit 0 without done_ok); not a pass" >&2
    exit 1
  fi
  exit "$1"
}

# The number of cases this runner makes; a change that adds or drops one changes this line too.
expected_cases=89

# Scripts with an EXIT trap under errexit that do not carry the guard, each with the reason.
exempt=(
  "tacenta-proofs/scripts/assemble-braid-unit.sh"
  "tacenta-proofs/scripts/assemble-triple-unit.sh"
)
exempt_reason="the translation attestation records its sha256 (tacenta-proofs/manifests/translation-attestation.json), so an edit to it is a change of its own with an attestation refresh"

here="$(cd "$(dirname "$0")" && pwd)"
root="$(cd "$here/../.." && pwd)"
self="$here/$(basename "$0")"
cases_dir="$here/exit-trap-status-cases"
work="$(mktemp -d)"
trap 'exit_guard_rc=$?; set +e; rm -rf "$work"; exit_guard "$exit_guard_rc"' EXIT

fail=0
cases=0
wrong() { fail=$((fail + 1)); echo "WRONG  $1: $2" >&2; }

# The guard, as this file holds it: from its first comment line to the closing brace of exit_guard.
guard_file="$work/guard"
sed -n '/^# Exit-status guard\. With an EXIT trap set/,/^}$/p' "$self" > "$guard_file"
if [ "$(wc -l < "$guard_file" | tr -d ' ')" -ne 12 ]; then
  echo "WRONG  guard: this file's own guard is not the 12 lines the cases expect" >&2
  exit 1
fi

# render <template> <body file> <out>: the template with @GUARD@ replaced by the guard and @BODY@ by the body,
# indented as the placeholder is.
render() {
  awk -v gf="$guard_file" -v bf="$2" '
    /^[[:space:]]*@GUARD@[[:space:]]*$/ { while ((getline l < gf) > 0) print l; close(gf); next }
    /^[[:space:]]*@BODY@[[:space:]]*$/ {
      match($0, /^[[:space:]]*/); ind = substr($0, 1, RLENGTH)
      while ((getline l < bf) > 0) print ind l; close(bf); next
    }
    { print }' "$1" > "$3"
}

# unguard <in> <out>: the same script with the guard taken out of its EXIT trap, as the tree had it before.
unguard() {
  sed -e 's/exit_guard_rc=\$?; set +e; //' -e 's/; exit_guard "\$exit_guard_rc"//' "$1" > "$2"
}

shell_of() {  # <shape>: the shell that runs it
  case "$1" in posix) echo /bin/sh ;; *) echo /bin/bash ;; esac
}
major_of() {  # <shape>: the major version of the bash that runs it, or "not" for another shell
  "$(shell_of "$1")" -c 'echo "${BASH_VERSION:-not bash}"' | cut -d. -f1
}

# run <name> <shape> <body> [unguarded]: renders and runs one fixture; sets out, rc and cleaned (yes or no).
run() {
  local name="$1" shape="$2" body="$3" script="$work/$1.sh" dir="$work/dir-$1"
  printf '%s\n' "$body" > "$work/$name.body"
  render "$cases_dir/shape-$shape.case" "$work/$name.body" "$script"
  if [ "${4:-}" = unguarded ]; then
    unguard "$script" "$script.unguarded"
    script="$script.unguarded"
  fi
  set +e
  out="$(cd "$work" && "$(shell_of "$shape")" "$script" "$dir" 2>&1)"
  rc=$?
  set -e
  if [ -e "$dir" ]; then cleaned=no; else cleaned=yes; fi
  cases=$((cases + 1))
}

# expect <name> <status: a number or nonzero> [reached: yes or no] [needle]: what the run in hand must show.
expect() {
  local name="$1" want="$2" reached="${3:-}" needle="${4:-}"
  if [ "$want" = nonzero ]; then
    [ "$rc" -ne 0 ] || { wrong "$name" "exit 0, expected a failure: $out"; return 0; }
  else
    [ "$rc" -eq "$want" ] || { wrong "$name" "exit $rc, expected $want: $out"; return 0; }
  fi
  case "$reached" in
    no) case "$out" in *PAST* | *END*) wrong "$name" "ran past the point it should have stopped at: $out"; return 0 ;; esac ;;
    yes) case "$out" in *END*) ;; *) wrong "$name" "did not run to its end: $out"; return 0 ;; esac ;;
  esac
  if [ -n "$needle" ]; then
    case "$out" in *"$needle"*) ;; *) wrong "$name" "does not say '$needle': $out"; return 0 ;; esac
  fi
  [ "$cleaned" = yes ] || wrong "$name" "the cleanup did not run (its directory is still there)"
  return 0
}

guard_message='stopped before its end with status 0'

# 1. The fatal errors, under each shape. Under a bash 3.2 the status was lost, so it is the guard that refuses the
# run, and it must say so; elsewhere the shell's own status stands.
kinds=(unset-variable required-parameter source-missing source-broken readonly bad-substitution eval-syntax)
fatal_body() {
  case "$1" in
    unset-variable) echo 'echo "value: $exit_trap_case_unset"' ;;
    required-parameter) echo ': "${exit_trap_case_unset:?is required}"' ;;
    source-missing) echo '. "$work/no-such-file.sh"' ;;
    source-broken) printf '%s\n' "printf 'if then\\n' > \"\$work/broken.sh\"" '. "$work/broken.sh"' ;;
    readonly) printf '%s\n' 'readonly exit_trap_case_fixed=1' 'exit_trap_case_fixed=2' ;;
    bad-substitution) echo 'echo "${%}"' ;;
    eval-syntax) echo "eval 'if then'" ;;
    empty-array) printf '%s\n' 'exit_trap_case_none=()' 'echo "values: ${exit_trap_case_none[@]}"' ;;
  esac
}
for shape in inline function nested posix; do
  needle=""
  if [ "$(major_of "$shape")" = 3 ]; then needle="$guard_message"; fi
  for kind in "${kinds[@]}"; do
    run "$shape-$kind" "$shape" "$(fatal_body "$kind")
echo PAST"
    expect "$shape-$kind" nonzero no "$needle"
  done
done
# An empty array under -u stops bash 3.2 (and 4.0 to 4.3) and is not an error from 4.4 on.
if /bin/bash -c 'set -u; a=(); : "${a[@]}"' 2>/dev/null; then array_fatal=no; else array_fatal=yes; fi
for shape in inline function nested; do
  run "$shape-empty-array" "$shape" "$(fatal_body empty-array)
echo PAST"
  if [ "$array_fatal" = yes ]; then
    needle=""
    if [ "$(major_of "$shape")" = 3 ]; then needle="$guard_message"; fi
    expect "$shape-empty-array" nonzero no "$needle"
  else
    expect "$shape-empty-array" 0 yes
  fi
done

# 2. The defect itself: the same fixtures with the guard taken out of the trap. Each shell is asked which bash it
# is; a 3.2 loses the status of the abort, any other keeps it.
for shape in inline function nested posix; do
  run "$shape-unguarded" "$shape" "$(fatal_body unset-variable)
echo PAST" unguarded
  if [ "$(major_of "$shape")" = 3 ]; then
    expect "$shape-unguarded" 0 no
  else
    expect "$shape-unguarded" nonzero no
  fi
done

# 3. Controls.
for shape in inline function nested posix; do
  run "$shape-to-the-end" "$shape" ':'
  expect "$shape-to-the-end" 0 yes
  run "$shape-done-ok" "$shape" 'done_ok
echo PAST'
  expect "$shape-done-ok" 0 no
  run "$shape-exit-3" "$shape" 'exit 3'
  expect "$shape-exit-3" 3 no
  run "$shape-plain-exit-0" "$shape" 'exit 0'
  expect "$shape-plain-exit-0" 1 no "$guard_message"
done
for shape in inline posix; do
  run "$shape-exit-status-0" "$shape" 'exit_trap_case_status=0
finished=yes
exit "$exit_trap_case_status"'
  expect "$shape-exit-status-0" 0 no
  run "$shape-exit-status-4" "$shape" 'exit_trap_case_status=4
finished=yes
exit "$exit_trap_case_status"'
  expect "$shape-exit-status-4" 4 no
  run "$shape-failing-command" "$shape" 'false
echo PAST'
  expect "$shape-failing-command" 1 no
done
run failing-cleanup-to-the-end failing-cleanup ':'
expect failing-cleanup-to-the-end 0 yes
run failing-cleanup-exit-3 failing-cleanup 'exit 3'
expect failing-cleanup-exit-3 3 no
run failing-cleanup-unset-variable failing-cleanup "$(fatal_body unset-variable)
echo PAST"
expect failing-cleanup-unset-variable nonzero no

# 4. The tree check.
# tree_check [--exempt PATH]... (--tree | --files FILE...): run from the current directory; sets out and rc.
tree_check() {
  set +e
  out="$(python3 -I "$cases_dir/check-tree.py" "$guard_file" "$@" 2>&1)"
  rc=$?
  set -e
  cases=$((cases + 1))
}

# The fixtures, rendered with the guard.
mkdir -p "$work/tree"
printf ':\n' > "$work/empty.body"
for f in "$cases_dir"/tree-*.case; do
  [ -e "$f" ] || { wrong tree-fixtures "no tree-*.case fixture under $cases_dir"; break; }
  name="$(basename "$f" .case)"
  render "$f" "$work/empty.body" "$work/tree/$name.sh"
  want="$(head -n 1 "$f")"
  cd "$work/tree"
  tree_check --files "$name.sh"
  case "$want" in
    "# expect: accept")
      [ "$rc" -eq 0 ] || wrong "$name" "the tree check refused it (exit $rc): $out" ;;
    "# expect: refuse "*)
      line="${want#\# expect: refuse }"
      if [ "$rc" -ne 1 ]; then
        wrong "$name" "the tree check did not refuse it with exit 1 (exit $rc): $out"
      elif ! grep -qxF -- "$name.sh:$line" <<<"$out"; then
        wrong "$name" "the tree check did not name '$name.sh:$line': $out"
      elif [ "$(grep -c "^$name\.sh:" <<<"$out")" -ne 1 ]; then
        wrong "$name" "the tree check named more than the one problem: $out"
      fi ;;
    *) wrong "$name" "its first line is not '# expect: accept' or '# expect: refuse <line>: <message>'" ;;
  esac
done

# Which files it reads when given none: a throwaway repository with an exposed script of each kind it selects
# (a script with a shebang and no extension, one whose shebang runs `env -S bash -e`, a hook without one, an
# executable with none), and the same text where it must not look (Markdown, a .case file, an executable with a
# Python shebang, a plain file with no shebang that is not executable, an untracked .sh). Exactly the four
# selected ones are refused; once they are gone, the guarded script alone is read and accepted.
repo="$work/selection"
mkdir -p "$repo/.githooks"
git init -q "$repo"
plain_trap="$(printf '%s\n%s' 'work="$(mktemp -d)"' "trap 'rm -rf \"\$work\"' EXIT")"
printf '#!/usr/bin/env bash\nset -euo pipefail\n%s\n' "$plain_trap" > "$repo/tool"
printf 'set -eu\n%s\n' "$plain_trap" > "$repo/.githooks/pre-commit"
printf 'set -e\n%s\n' "$plain_trap" > "$repo/notes.md"
printf 'set -e\n%s\n' "$plain_trap" > "$repo/fixture.case"
printf '#!/usr/bin/env -S bash -e\n%s\n' "$plain_trap" > "$repo/envtool"
printf 'set -e\n%s\n' "$plain_trap" > "$repo/runme"
chmod +x "$repo/runme"
printf '#!/usr/bin/env python3\n%s\n' "$plain_trap" > "$repo/pytool"
chmod +x "$repo/pytool"
printf 'set -e\n%s\n' "$plain_trap" > "$repo/data"
render "$cases_dir/tree-guarded.case" "$work/empty.body" "$repo/ok.sh"
git -C "$repo" add tool .githooks/pre-commit notes.md fixture.case envtool runme pytool data ok.sh
printf 'set -e\n%s\n' "$plain_trap" > "$repo/loose.sh"
cd "$repo"
tree_check --tree
if [ "$rc" -ne 1 ] || [ "$(grep -c ': an EXIT trap without the exit-status guard$' <<<"$out")" -ne 4 ] \
    || ! grep -qxF 'tool:4: an EXIT trap without the exit-status guard' <<<"$out" \
    || ! grep -qxF '.githooks/pre-commit:3: an EXIT trap without the exit-status guard' <<<"$out" \
    || ! grep -qxF 'envtool:3: an EXIT trap without the exit-status guard' <<<"$out" \
    || ! grep -qxF 'runme:3: an EXIT trap without the exit-status guard' <<<"$out"; then
  wrong selection "expected exactly tool:4, .githooks/pre-commit:3, envtool:3 and runme:3 refused (exit $rc): $out"
fi
git -C "$repo" rm -qf tool .githooks/pre-commit envtool runme
tree_check --tree
if [ "$rc" -ne 0 ] || ! grep -qF '1 file(s) read, 1 with an EXIT trap, 1 guarded, 0 exempt by name' <<<"$out"; then
  wrong selection-guarded "expected the guarded script alone read and accepted (exit $rc): $out"
fi

# The tree itself, with its exemptions; then an exemption that names a guarded script, and one that names a file
# the check does not read, each refused.
cd "$root"
exempt_args=()
for path in "${exempt[@]}"; do exempt_args+=(--exempt "$path"); done
tree_check "${exempt_args[@]}" --tree
if [ "$rc" -ne 0 ] || ! grep -qF "guarded, ${#exempt[@]} exempt by name" <<<"$out"; then
  wrong tree "the repository's own scripts were not all accepted (exit $rc): $out"
fi
tree_check "${exempt_args[@]}" --exempt tooling/fast.sh --tree
if [ "$rc" -ne 1 ] || ! grep -qxF 'tooling/fast.sh: exempt by name, but it carries the guard; drop the exemption' <<<"$out"; then
  wrong tree-stale-guarded "an exemption for a guarded script was not refused (exit $rc): $out"
fi
tree_check "${exempt_args[@]}" --exempt README.md --tree
if [ "$rc" -ne 1 ] || ! grep -qxF 'README.md: exempt by name, but it is not a file this check reads; drop the exemption' <<<"$out"; then
  wrong tree-stale-unread "an exemption for a file the check does not read was not refused (exit $rc): $out"
fi

if [ "$cases" -ne "$expected_cases" ]; then
  wrong case-count "$cases cases ran, and this runner pins $expected_cases"
fi
if [ "$fail" -ne 0 ]; then
  echo "exit-trap-status-cases: $fail of $cases cases went wrong" >&2
  exit 1
fi
echo "exit-trap-status-cases: $cases cases (seven shell-fatal errors and an empty array under four trap shapes, the same shapes without the guard, the controls for a full run, done_ok, exit 3, a plain exit 0, a kept status and a failing cleanup, and the tree check's fixtures, file selection, exemptions and the tree itself) gave the expected result"
finished=yes
