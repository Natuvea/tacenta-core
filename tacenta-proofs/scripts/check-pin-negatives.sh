#!/usr/bin/env bash
# Hold the `#guard_msgs` pins to a pin that disagrees with Lean.
#
# A pinned theorem's axiom list, and the statement of each central theorem, is written out in a
# `#guard_msgs` docstring that the build checks against what Lean prints. The attestation scan
# (`attest.py`) refuses a pin that is deleted or commented out; it never asks whether a pin that is there
# can fail. `check-attest-negatives.sh` shows the scan refuse; nothing showed Lean refuse a pin whose text is
# wrong. A docstring that disagrees with Lean is refused by the cases below. A pin rewritten as
# `#guard_msgs (drop info) in` with its docstring deleted is not refused here, by Lean or by `attest.py` once
# the manifests are regenerated; the manifest diff is the only trace.
#
# Each case edits one pin in a disposable worktree of the commit under test, with the three packages' build
# directories linked in so that `lake env lean` finds every built import, and elaborates that one file:
#
#   a pin with an axiom missing           Lean must refuse: "does not match generated message"
#   a pin with an axiom added             the same
#   a statement pin with its text changed the same
#
# after first requiring the unchanged files to elaborate. Each file takes about three seconds. Needs the
# translation package built (`no-sorry.sh` runs this after its builds). What is tested is the committed tree.
set -euo pipefail

root="$(git rev-parse --show-toplevel)"
for package in tacenta-model tacenta-proofs tacenta-proofs/translation; do
  [ -d "$root/$package/.lake/build" ] \
    || { echo "pin negatives: $package is not built; run the builds first" >&2; exit 1; }
done
work="$(mktemp -d)"
cleanup() { git -C "$root" worktree remove --force "$work/tree" >/dev/null 2>&1 || true; rm -rf "$work"; }
trap cleanup EXIT
git -C "$root" worktree add -q --detach "$work/tree" HEAD >/dev/null
tree="$work/tree"
for package in tacenta-model tacenta-proofs tacenta-proofs/translation; do
  ln -s "$root/$package/.lake" "$tree/$package/.lake"
done
pins=Translation/UnitPins.lean
statements=Translation/UnitSatisfiabilityRecords.lean
cases=0

reset() { git -C "$tree" reset -q --hard HEAD && git -C "$tree" clean -fdq -e .lake; }

elaborate() {  # file
  set +e
  out="$(cd "$tree/tacenta-proofs/translation" && lake env lean "$1" 2>&1)"
  rc=$?
  set -e
}

# once <file> <old> <new>: replace the first occurrence of a text that occurs at least once.
first() {
  python3 - "$tree/tacenta-proofs/translation/$1" "$2" "$3" <<'PY'
import pathlib, sys
path = pathlib.Path(sys.argv[1])
text = path.read_text()
if sys.argv[2] not in text:
    raise SystemExit(f"control: {sys.argv[2]!r} is not in {path}")
path.write_text(text.replace(sys.argv[2], sys.argv[3], 1))
PY
}

accepted() {
  elaborate "$1"
  cases=$((cases + 1))
  if [ "$rc" -ne 0 ]; then
    echo "pin negative baseline: $1 did not elaborate" >&2
    printf '%s\n' "$out" | head -20 >&2
    exit 1
  fi
}

refused() {  # name file
  elaborate "$2"
  cases=$((cases + 1))
  if [ "$rc" -eq 0 ] || ! grep -qF 'does not match generated message' <<<"$out"; then
    echo "pin negative $1: Lean did not refuse the changed pin (exit $rc)" >&2
    printf '%s\n' "$out" | head -20 >&2
    exit 1
  fi
}

accepted "$pins"
accepted "$statements"
reset
first "$pins" $'axioms: [propext,\n Classical.choice,\n' $'axioms: [propext,\n'
refused 'an axiom pin missing an axiom' "$pins"
reset
first "$pins" $'axioms: [propext,\n Classical.choice,\n Quot.sound,\n' $'axioms: [propext,\n Classical.choice,\n Quot.sound,\n gate_control_extra_axiom,\n'
refused 'an axiom pin with an axiom added' "$pins"
reset
first "$statements" 'axiom_base_satisfiable : ∃ I R rc,' 'axiom_base_satisfiable : ∃ I R,'
refused 'a statement pin with its text changed' "$statements"

echo "pin negatives: $cases cases (two files elaborate unchanged; an axiom pin missing an axiom, one with an axiom added and a statement pin with changed text are each refused by Lean) gave the expected result"
