#!/usr/bin/env bash
# Hold the `--check` mode of every generated-unit script to a hand edit, a stale source and, for the ports,
# a moved rewrite target.
#
# Eleven scripts regenerate a committed file or tree from its sources and, with `--check`, fail on any
# difference: `assemble-{triple,braid,session}-unit.sh` (the three Rust units that Charon translates),
# `port-unit-proofs.sh` and `port-session-unit-proofs.sh` (which port several proofs each), and six
# one-proof `port-session-*.sh` scripts. A generated file nobody can edit without a failure is only as good
# as that failure, and none of the eleven had a retained case that showed it. (`check-port-negatives.sh`
# holds the unit-only edits of three of them to their anchors; this holds the rest.)
#
# Each case plants one change in a disposable worktree of the commit under test and requires `--check` (or,
# where it says so, the script without `--check`) to exit nonzero with the script's own diagnostic:
#
#   hand edit    a line appended to a generated file                              -> "differs" or "not what"
#   stale source a line inserted in the source the file is generated from         -> the same
#   moved target (ports) a text a rewrite counts, written once more in the source -> "expected" (a count)
#   extra file   a file added to a generated unit directory                       -> the assembler's refusal
#   missing file a generated unit file deleted                                    -> the same
#   write mode   an unknown argument (all eleven); a rewrite target written once more, run without --check
#                (the ports); for the triple and braid assemblers a leaf with no inner attribute block, one that
#                already holds the inserted `use` line and one that already holds the inserted block; for the
#                Session assembler a lifecycle root without its re-export
#
# Not held by any case: the assemblers' comparison of the stripped copy with the leaf and their check of where the
# inserted `use` landed. Both are self-checks of the script's own output that no leaf in the tree reaches
# (`tooling/gate-mutations.json`, `GA-*-diffq` and `GA-*-late`).
#
# The unchanged tree must be accepted first by every script, so a refusal is the change and not the script.
# What is tested is the committed tree, as in `check-port-negatives.sh`. No Lean toolchain is needed.
set -euo pipefail

root="$(git rev-parse --show-toplevel)"
work="$(mktemp -d)"
cleanup() { git -C "$root" worktree remove --force "$work/tree" >/dev/null 2>&1 || true; rm -rf "$work"; }
trap cleanup EXIT
git -C "$root" worktree add -q --detach "$work/tree" HEAD >/dev/null
tree="$work/tree"
t=tacenta-proofs/translation/Translation
s=tacenta-proofs/scripts
cases=0

reset() { git -C "$tree" reset -q --hard HEAD && git -C "$tree" clean -fdq; }

# insert <file> <before-anchor or empty to append> <text>: the text goes in one line before the anchor.
insert() {
  python3 - "$tree/$1" "$2" "$3" <<'PY'
import pathlib, sys
path = pathlib.Path(sys.argv[1])
text = path.read_text()
anchor, line = sys.argv[2], "-- gate control: " + sys.argv[3] + "\n"
if anchor == "":
    text += "\n" + line
else:
    if text.count(anchor) != 1:
        raise SystemExit(f"control: anchor {anchor!r} occurs {text.count(anchor)} times in {path}")
    text = text.replace(anchor, line + anchor)
path.write_text(text)
PY
}

# expect_refused <name> <needle> <command...>: run the script's --check in the worktree.
expect_refused() {
  local name="$1" needle="$2" out rc
  shift 2
  set +e
  out="$(cd "$tree" && "$@" --check 2>&1)"
  rc=$?
  set -e
  cases=$((cases + 1))
  if [ "$rc" -eq 0 ] || ! grep -qF -- "$needle" <<<"$out"; then
    echo "generation negative $name: expected a refusal containing '$needle', got exit $rc" >&2
    printf '%s\n' "$out" | head -20 >&2
    exit 1
  fi
}

# expect_refused_write <name> <needle> <command...>: the script without --check, which writes what it generates, so
# the guards it runs on its own output and on its arguments are the ones under test.
expect_refused_write() {
  local name="$1" needle="$2" out rc
  shift 2
  set +e
  out="$(cd "$tree" && "$@" 2>&1)"
  rc=$?
  set -e
  cases=$((cases + 1))
  if [ "$rc" -eq 0 ] || ! grep -qF -- "$needle" <<<"$out"; then
    echo "generation negative $name: expected a refusal containing '$needle', got exit $rc" >&2
    printf '%s\n' "$out" | head -20 >&2
    exit 1
  fi
}

expect_accepted() {
  local name="$1" out rc
  shift
  set +e
  out="$(cd "$tree" && "$@" --check 2>&1)"
  rc=$?
  set -e
  cases=$((cases + 1))
  if [ "$rc" -ne 0 ]; then
    echo "generation negative $name: the unchanged tree was refused" >&2
    printf '%s\n' "$out" | head -20 >&2
    exit 1
  fi
}

# ---- the three assemblers -------------------------------------------------------------------------
# assembler <name> <command> <unit dir> <needle> <copied sources...>
assembler() {
  local name="$1" cmd="$2" unit="$3" needle="$4" file
  shift 4
  reset
  expect_accepted "$name baseline" $cmd
  while IFS= read -r file; do
    reset
    case "$file" in
      *.toml) printf '\n# gate control\n' >> "$tree/$file" ;;
      *) printf '\n// gate control\n' >> "$tree/$file" ;;
    esac
    expect_refused "$name: hand edit of $file" "$needle" $cmd
  done < <(git -C "$tree" ls-files "$unit")
  reset
  printf '// gate control\n' > "$tree/$unit/src/gate_control_extra.rs"
  expect_refused "$name: an extra file in the unit" "$needle" $cmd
  reset
  file="$(git -C "$tree" ls-files "$unit" | grep -v 'Cargo.toml$' | head -n 1)"
  rm "$tree/$file"
  expect_refused "$name: $file deleted" "$needle" $cmd
  for file in "$@"; do
    reset
    printf '\n// gate control\n' >> "$tree/$file"
    expect_refused "$name: a line added to the source $file" "$needle" $cmd
  done
  reset
  expect_refused_write "$name: an unknown argument" 'usage:' $cmd --no-such-option
}

# The two smaller assemblers refuse, as they write, a leaf whose shape their insertion cannot read. Each input
# below is refused by exactly the guard named: the leaf has no inner attribute block (the insertion point is
# unknown), already carries the inserted `use` line (it would appear twice), or already carries the whole
# inserted block (the self-check finds it twice).
leaf_cases() {  # name script leaf unit-copy use-line
  local name="$1" cmd="sh $s/$2" leaf="$3" copy="$4" use="$5"
  reset
  printf 'pub struct GateControlFirst;\n%s' "$(cat "$tree/$leaf")" > "$tree/$leaf"
  expect_refused_write "$name: a leaf with no inner attribute block" 'no inner attribute block' $cmd
  reset
  printf '\n%s\n' "$use" >> "$tree/$leaf"
  expect_refused_write "$name: a leaf that already holds the inserted use line" 'expected exactly one inserted' $cmd
  reset
  python3 - "$tree/$copy" "$tree/$leaf" "$use" <<'PY'
import pathlib, sys
copy, leaf, use = pathlib.Path(sys.argv[1]), pathlib.Path(sys.argv[2]), sys.argv[3]
text = copy.read_text()
start = text.index("// Inserted by tacenta-proofs/scripts/")
end = text.index(use, start) + len(use) + 1
leaf.write_text(leaf.read_text() + "\n" + text[start:end])
PY
  expect_refused_write "$name: a leaf that already holds the inserted block" 'the inserted block occurs 2' $cmd
}
assembler triple "sh $s/assemble-triple-unit.sh" tacenta-core/triple-unit 'is not what the' \
  tacenta-core/triple/src/lib.rs
assembler braid "sh $s/assemble-braid-unit.sh" tacenta-core/braid-unit 'is not what the two' \
  tacenta-core/braid/src/lib.rs
leaf_cases triple assemble-triple-unit.sh tacenta-core/triple/src/lib.rs tacenta-core/triple-unit/src/tacenta_triple.rs 'use crate::{tacenta_ratchet, tacenta_spqr};'
leaf_cases braid assemble-braid-unit.sh tacenta-core/braid/src/lib.rs tacenta-core/braid-unit/src/tacenta_braid.rs 'use crate::tacenta_erasure;'
assembler session "sh $s/assemble-session-unit.sh" tacenta-core/session-unit 'generated unit is stale or hand-edited' \
  tacenta-core/lifecycle/src/lib.rs tacenta-core/lifecycle/src/lifecycle.rs \
  tacenta-core/lifecycle/src/serialization/mod.rs tacenta-core/lifecycle/src/serialization/composite.rs

# The Session assembler reads the lifecycle root for the one place its re-export is changed, and refuses a root
# that no longer has it, in write mode and not only against the committed unit.
reset
python3 - "$tree/tacenta-core/lifecycle/src/lib.rs" <<'PY'
import pathlib, sys
path = pathlib.Path(sys.argv[1])
text = path.read_text()
anchor = "pub mod ratchet {\n    pub use tacenta_ratchet::*;\n}"
if text.count(anchor) != 1:
    raise SystemExit("control: the lifecycle ratchet re-export is not where the control expects it")
path.write_text(text.replace(anchor, "pub mod ratchet {\n    pub use tacenta_ratchet::*;\n    pub const GATE_CONTROL: u8 = 0;\n}"))
PY
expect_refused_write 'session: a lifecycle root whose ratchet re-export changed' 'lifecycle ratchet re-export anchor changed' sh $s/assemble-session-unit.sh

# ---- the ports ------------------------------------------------------------------------------------------
# port <name> <command> <needle> <dest> <src> <before-anchor or empty> <rewrite target or empty>
port() {
  local name="$1" cmd="$2" needle="$3" dest="$4" src="$5" anchor="$6" target="$7"
  reset
  expect_accepted "$name: baseline" $cmd
  reset
  printf '\n-- gate control\n' >> "$tree/$t/$dest"
  expect_refused "$name: hand edit of $dest" "$needle" $cmd
  reset
  insert "$t/$src" "$anchor" "a line the port should carry over"
  expect_refused "$name: a line added to the source $src" "$needle" $cmd
  if [ -n "$target" ]; then
    reset
    insert "$t/$src" "$anchor" "$target"
    expect_refused "$name: the rewrite target '$target' written once more in $src" "expected" $cmd
    # Without --check the same source must be refused before anything is written; a count that is not checked
    # writes a copy that has silently stopped being the same theorem.
    expect_refused_write "$name: the same source, written and not checked" "expected" $cmd
  fi
  reset
  expect_refused_write "$name: an unknown argument" 'usage:' $cmd --no-such-option
}
cmd_unit="bash $s/port-unit-proofs.sh"
port port-unit-T1 "$cmd_unit" 'not what the leaf' UnitT1.lean T1.lean '' 'Tacenta.T1.control'
port port-unit-SpqrT1 "$cmd_unit" 'not what the leaf' UnitSpqrT1.lean SpqrT1.lean '' 'Tacenta.SpqrT1.control'
port port-unit-T3 "$cmd_unit" 'not what the leaf' UnitT3.lean T3.lean '' 'Tacenta.T3.control'
port port-unit-SpqrT3 "$cmd_unit" 'not what the leaf' UnitSpqrT3.lean SpqrT3.lean '' 'Tacenta.SpqrT3.control'

# `port-unit-proofs.sh` reports every copy that differs, not only the first: with two of its four copies edited, the
# difference of each is in the output.
reset
printf '\n-- gate control\n' >> "$tree/$t/UnitT1.lean"
printf '\n-- gate control\n' >> "$tree/$t/UnitSpqrT1.lean"
set +e
out="$(cd "$tree" && bash $s/port-unit-proofs.sh --check 2>&1)"
rc=$?
set -e
cases=$((cases + 1))
if [ "$rc" -eq 0 ] || ! grep -qF -- "$t/UnitT1.lean" <<<"$out" || ! grep -qF -- "$t/UnitSpqrT1.lean" <<<"$out"; then
  echo "generation negative port-unit: two edited copies were not both reported (exit $rc)" >&2
  printf '%s\n' "$out" | head -20 >&2
  exit 1
fi

cmd_session="bash $s/port-session-unit-proofs.sh"
reset
expect_refused_write 'port-session-unit: an unknown argument' 'usage:' $cmd_session --no-such-option
for pair in SessionUnitT1:UnitT1 SessionUnitSpqrT1:UnitSpqrT1 SessionUnitT3:UnitT3 SessionUnitSpqrT3:UnitSpqrT3 \
  SessionUnitTripleT1:UnitTripleT1 SessionUnitTripleT3:UnitTripleT3 SessionUnitWireT1:WireT1 \
  SessionUnitWireT3:WireT3 SessionUnitWireInitialT3:WireInitialT3; do
  dest="${pair%%:*}.lean"
  src="${pair##*:}.lean"
  reset
  expect_accepted "port-session-unit-$src: baseline" $cmd_session
  reset
  printf '\n-- gate control\n' >> "$tree/$t/$dest"
  expect_refused "port-session-unit-$src: hand edit of $dest" 'committed copies differ' $cmd_session
  case "$src" in
    Wire*) # a source that no other port script generates
      reset
      printf '\n-- gate control\n' >> "$tree/$t/$src"
      expect_refused "port-session-unit-$src: a line added to the source $src" 'committed copies differ' $cmd_session
      case "$src" in
        WireT1.lean) target='Translation.TacentaWire' ;;
        WireT3.lean) target='Translation.WireT1' ;;
        *) target='Translation.WireT3' ;;
      esac
      reset
      insert "$t/$src" '' "$target"
      expect_refused "port-session-unit-$src: the rewrite target '$target' written once more" 'expected' $cmd_session
      expect_refused_write "port-session-unit-$src: the same source, written and not checked" 'expected' $cmd_session ;;
  esac
done

diff_msg='committed copy differs'
port port-session-pqxdh "bash $s/port-session-pqxdh-proof.sh" "$diff_msg" SessionUnitSessionT1.lean SessionT1.lean '' 'Translation.TacentaSession'
port port-session-erasure "bash $s/port-session-erasure-proof.sh" "$diff_msg" SessionUnitErasureT1.lean ErasureT1.lean '' 'Translation.TacentaErasure'
port port-session-braid "bash $s/port-session-braid-proof.sh" "$diff_msg" SessionUnitBraidT1.lean BraidT1.lean '' 'open tacenta_braid'
port port-session-braid-refinement "bash $s/port-session-braid-refinement.sh" "$diff_msg" SessionUnitBraidT3.lean BraidT3.lean '' 'Translation.TacentaBraid'
# The two import ports each take one region of ImportInv.lean, so a line must land inside it: before the
# Braid section for the ratchet half, before its closing `end Braid` for the Braid half.
port port-session-ratchet-import "bash $s/port-session-ratchet-import-proof.sh" "$diff_msg" SessionUnitRatchetImportInv.lean ImportInv.lean '/-! # `tacenta-braid`' 'import Translation.T3'
port port-session-braid-import "bash $s/port-session-braid-import-proof.sh" "$diff_msg" SessionUnitBraidImportInv.lean ImportInv.lean $'\nend Braid' 'open tacenta_braid'

echo "generation negatives: $cases cases (three assemblers and eight port scripts: hand edit, stale source, moved rewrite target, extra and missing files) gave the expected result"
