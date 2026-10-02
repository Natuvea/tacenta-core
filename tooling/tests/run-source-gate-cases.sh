#!/usr/bin/env bash
# Negative controls for three source checks that had none:
#
#   tooling/check-conflict-markers.sh             no tracked file holds a conflict marker
#   tooling/check-proof-hygiene.sh                no hand-written proof names a generated `_proof_<n>` constant
#   tooling/check_authentication_boundary.py      every receive path is registered under its signature
#
# Each case plants one change in a disposable worktree of the commit under test and runs that worktree's
# own copy of the gate. A refusal case names the diagnostic it must produce, so a case does not pass on
# an unrelated failure; an acceptance case holds the other side of a rule (a shape the gate must let
# through). The caller's tree is not touched, and, as in `check-port-negatives.sh`, what is tested is the
# committed tree: commit a gate change before running its controls.
set -euo pipefail

root="$(git rev-parse --show-toplevel)"
work="$(mktemp -d)"
cleanup() { git -C "$root" worktree remove --force "$work/tree" >/dev/null 2>&1 || true; rm -rf "$work"; }
trap cleanup EXIT
git -C "$root" worktree add -q --detach "$work/tree" HEAD >/dev/null
tree="$work/tree"
cases=0

reset() { git -C "$tree" reset -q --hard HEAD && git -C "$tree" clean -fdq; }

# plant <file> <python statements on t, the text of the file>: edit a tracked file in place, requiring
# the edit to change it.
plant() {
  python3 - "$tree/$1" "$2" <<'PY'
import pathlib, sys
path = pathlib.Path(sys.argv[1])
t = path.read_text()
scope = {'t': t}
exec(sys.argv[2], scope)
if scope['t'] == t:
    raise SystemExit(f"control: the edit to {path} changed nothing")
path.write_text(scope['t'])
PY
}

# once <file> <old> <new>: replace a text that occurs exactly once.
once() {
  python3 - "$tree/$1" "$2" "$3" <<'PY'
import pathlib, sys
path = pathlib.Path(sys.argv[1])
t = path.read_text()
if t.count(sys.argv[2]) != 1:
    raise SystemExit(f"control: {sys.argv[2]!r} occurs {t.count(sys.argv[2])} times in {path}")
path.write_text(t.replace(sys.argv[2], sys.argv[3]))
PY
}

# run <gate command...> inside the worktree; sets out and rc.
run_gate() {
  set +e
  out="$(cd "$tree/${GATE_DIR:-}" && "$@" 2>&1)"
  rc=$?
  set -e
}

refuse() {  # name needle gate command...
  local name="$1" needle="$2"
  shift 2
  run_gate "$@"
  cases=$((cases + 1))
  if [ "$rc" -eq 0 ] || ! grep -qF -- "$needle" <<<"$out"; then
    echo "WRONG  $name: expected a refusal naming '$needle', got exit $rc" >&2
    printf '%s\n' "$out" >&2
    exit 1
  fi
}

accept() {  # name gate command...
  local name="$1"
  shift
  run_gate "$@"
  cases=$((cases + 1))
  if [ "$rc" -ne 0 ]; then
    echo "WRONG  $name: expected acceptance, got exit $rc" >&2
    printf '%s\n' "$out" >&2
    exit 1
  fi
}

# ---- conflict markers --------------------------------------------------------
markers=(bash tooling/check-conflict-markers.sh)
accept markers-baseline "${markers[@]}"
for kind in start middle end; do
  case "$kind" in
    start) marker='<<<<<<< HEAD' ;;
    middle) marker='=======' ;;
    end) marker='>>>>>>> topic' ;;
  esac
  reset
  plant README.md "t += '\n$marker\n'"
  git -C "$tree" add -u
  refuse "markers-$kind" 'conflict-markers: unresolved marker(s) found' "${markers[@]}"
  case "$out" in *README.md*) ;; *) echo "WRONG  markers: the refusal does not name README.md: $out" >&2; exit 1 ;; esac
done
# A marker in a file added in the change, not only in one already tracked.
reset
printf '<<<<<<< ours\n' > "$tree/tacenta-spec/new-file.md"
git -C "$tree" add tacenta-spec/new-file.md
refuse markers-new-file 'tacenta-spec/new-file.md' "${markers[@]}"
# The shapes the gate lets through: an indented marker, a marker mid-line, a `.patch` file (a diff of a
# diff carries marker lines on purpose).
reset
plant README.md "t += '\n  <<<<<<< indented\nsee <<<<<<< in a sentence\n'"
printf '<<<<<<< a diff of a conflict\n' > "$tree/example.patch"
git -C "$tree" add -A
accept markers-allowed-shapes "${markers[@]}"

# The marker is refused whatever the file type: a pathspec that excluded more than `.patch` would let it through.
for file in tacenta-proofs/translation/Translation/T1.lean tacenta-core/braid/src/lib.rs tooling/required-steps.json \
  .github/workflows/ci.yml tooling/check-labels.sh; do
  reset
  printf '<<<<<<< HEAD\n' >> "$tree/$file"
  git -C "$tree" add -u
  refuse "markers-in-$(basename "$file")" "$file" "${markers[@]}"
done
# And from any directory of the repository, not only its root: the gate finds the root itself.
reset
plant README.md "t += '\n>>>>>>> topic\n'"
git -C "$tree" add -u
GATE_DIR=tacenta-spec refuse markers-from-a-subdirectory 'README.md' bash ../tooling/check-conflict-markers.sh

# ---- proof hygiene -------------------------------------------------------------
hygiene=(bash tooling/check-proof-hygiene.sh)
t_dir=tacenta-proofs/translation/Translation
accept hygiene-baseline "${hygiene[@]}"
reset
plant "$t_dir/T1.lean" "t += '\ntheorem control_probe : True := kdf_ck._proof_3\n'"
refuse hygiene-code-line 'a hand-written proof names a generated auxiliary constant' "${hygiene[@]}"
case "$out" in *T1.lean*) ;; *) echo "WRONG  hygiene: the refusal does not name T1.lean: $out" >&2; exit 1 ;; esac
reset
plant "$t_dir/T1.lean" "t += '\ntheorem control_probe : True := foo._proof_12 -- trailing note\n'"
refuse hygiene-code-before-comment 'a hand-written proof names a generated auxiliary constant' "${hygiene[@]}"
reset
printf 'theorem control_probe : True := kdf_ck._proof_5\n' > "$tree/$t_dir/ControlProbe.lean"
git -C "$tree" add -A
refuse hygiene-new-hand-written-file 'ControlProbe.lean' "${hygiene[@]}"
reset
plant "$t_dir/T1.lean" "t += '\n-- the name kdf_ck._proof_3 belongs to the translator\n'"
accept hygiene-comment-only "${hygiene[@]}"
reset
plant "$t_dir/TacentaRatchet.lean" "t += '\ndef control_probe := kdf_ck._proof_3\n'"
accept hygiene-generated-file-exempt "${hygiene[@]}"

# ---- authentication boundary -------------------------------------------------------
boundary=(python3 tooling/check_authentication_boundary.py)
registry=tacenta-core/AUTHENTICATION-BOUNDARY.md
braid=tacenta-core/braid/src/lib.rs
accept boundary-baseline "${boundary[@]}"
reset
plant "$braid" "t += '\npub fn handle_control_probe(_msg: &[u8]) {}\n'"
refuse boundary-new-receive-path 'handle_control_probe` consumes a message and is not registered' "${boundary[@]}"
reset
plant "$braid" "t += '\npub const fn parse_control_probe() {}\n'"
refuse boundary-const-fn-qualifier 'parse_control_probe` consumes a message and is not registered' "${boundary[@]}"
reset
plant "$braid" "t += '\nstruct Probe;\nimpl Probe { fn establish_control_probe(&self) {} }\n'"
refuse boundary-private-method 'establish_control_probe` consumes a message and is not registered' "${boundary[@]}"
reset
plant "$braid" "t += '\n#[cfg(test)]\nmod control_probe_tests { fn accept_inside_test_module() {} }\npub fn ingest_after_test_module() {}\n'"
refuse boundary-code-after-test-module 'ingest_after_test_module` consumes a message and is not registered' "${boundary[@]}"
reset
plant "$braid" "t += '\n// #[cfg(test)] in a comment exempts nothing\npub fn receive_control_probe(&self) {}\n'"
refuse boundary-cfg-test-in-a-comment 'receive_control_probe` consumes a message and is not registered' "${boundary[@]}"
reset
plant "$braid" "t += '\n#[cfg(test)]\nfn receive_under_cfg_test() {}\n'"
accept boundary-cfg-test-attribute-exempts "${boundary[@]}"
reset
once "$braid" 'pub fn receive(&self, msg: &Msg) -> (u64, Option<Output>, Braid) {' 'pub fn receive(&mut self, msg: &Msg) -> (u64, Option<Output>, Braid) {'
refuse boundary-shape-drift 'is registered as transactional (must take `&self`) but takes `&mut self`' "${boundary[@]}"
reset
plant "$registry" "t = t.replace('| \`tacenta-core/braid/src/lib.rs::Braid::step_receive\`', '| \`tacenta-core/braid/src/lib.rs::Braid::step_receive_gone\`', 1)"
refuse boundary-stale-row 'is registered but no such function was found' "${boundary[@]}"
case "$out" in *'Braid::step_receive_gone'*) ;; *) echo "WRONG  boundary-stale-row: the refusal does not name the stale row: $out" >&2; exit 1 ;; esac
# A row for a function that does not exist, with every real row kept: the stale row is the only fault.
reset
plant "$registry" "t = t.replace('| \`tacenta-core/braid/src/lib.rs::Braid::commit\` | the adopting half |\n', '| \`tacenta-core/braid/src/lib.rs::Braid::commit\` | the adopting half |\n| \`tacenta-core/braid/src/lib.rs::Braid::no_such_function\` | an extra row |\n', 1)"
refuse boundary-extra-row-for-a-missing-function 'Braid::no_such_function` is registered but no such function was found' "${boundary[@]}"
# A function the registry names, declared twice in one file: the second declaration is not covered by the row.
reset
plant "$braid" "t += '\nimpl Braid { pub fn commit(&mut self, _next: Braid) {} }\n'"
refuse boundary-registered-function-declared-twice 'Braid::commit` is declared more than once in that file' "${boundary[@]}"
reset
plant "$registry" "t = t.replace('| \`tacenta-core/braid/src/lib.rs::Braid::commit\` | the adopting half |\n', '', 1)"
refuse boundary-row-removed 'Braid::commit` consumes a message and is not registered' "${boundary[@]}"
reset
plant "$registry" "t = t.replace('| \`tacenta-core/braid/src/lib.rs::Braid::commit\` | the adopting half |\n', '| \`tacenta-core/braid/src/lib.rs::Braid::commit\` | the adopting half |\n| \`tacenta-core/braid/src/lib.rs::Braid::commit\` | again |\n', 1)"
refuse boundary-row-twice 'registry lists `tacenta-core/braid/src/lib.rs::Braid::commit` twice' "${boundary[@]}"
reset
plant "$braid" "t += '\nfn unbalanced_probe() {\n'"
refuse boundary-unbalanced-braces "braces do not balance outside strings and comments" "${boundary[@]}"
reset
plant "$braid" "t += '\nstruct DupProbe;\nimpl DupProbe { pub fn receive_dup(&self) {} }\nimpl DupProbe { pub fn receive_dup(&self) {} }\n'"
refuse boundary-duplicate-declaration 'is declared more than once in that file' "${boundary[@]}"
reset
mv "$tree/$registry" "$tree/$registry.gone"
refuse boundary-registry-missing 'missing' "${boundary[@]}"

echo "source-gate-cases: $cases cases (conflict markers, proof hygiene, authentication boundary) gave the expected result"
