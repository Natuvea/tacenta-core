#!/usr/bin/env bash
# Hold the unit-only edits of the three Session Braid port scripts to their anchors: break the
# standalone source proof at one anchor in a disposable worktree and require the port script to
# refuse, naming a unit edit.  The caller's tree is not touched.
set -euo pipefail

root="$(git rev-parse --show-toplevel)"
work="$(mktemp -d)"
cleanup() { git -C "$root" worktree remove --force "$work" >/dev/null 2>&1 || rm -rf "$work"; }
trap cleanup EXIT
git -C "$root" worktree add -q --detach "$work" HEAD >/dev/null
t=tacenta-proofs/translation/Translation

expect_refused() {  # name script source old new [expected text, default "unit edit"]
  git -C "$work" checkout -q --force HEAD -- .
  python3 - "$work/$3" "$4" "$5" <<'PY'
import pathlib, sys
path = pathlib.Path(sys.argv[1]); text = path.read_text()
if text.count(sys.argv[2]) != 1:
    raise SystemExit(f"port negative: anchor occurs {text.count(sys.argv[2])} times: {sys.argv[2]!r}")
path.write_text(text.replace(sys.argv[2], sys.argv[3]))
PY
  local out
  if out="$(cd "$work" && bash "tacenta-proofs/scripts/$2" --check 2>&1)"; then
    echo "port negative $1: the script accepted the broken source" >&2; exit 1
  fi
  local want="${6:-unit edit}"
  case "$out" in
    *"$want"*) ;;
    *) echo "port negative $1: refused, but not by '$want': $out" >&2; exit 1 ;;
  esac
}

expect_refused braid-hdmsg-renamed port-session-braid-proof.sh "$t/BraidT1.lean" \
  "hdmsg hdr_dec1; simp only [ho]" "hdmsg hdr_dec2; simp only [ho]"
expect_refused braid-clone-closer port-session-braid-proof.sh "$t/BraidT1.lean" \
  "simp_all [State.epoch_val, State.ct1_bounded])))" "simp_all [State.ct1_bounded, State.epoch_val])))"
expect_refused refinement-clone-step port-session-braid-refinement.sh "$t/BraidT3.lean" \
  "State.clone_bounds_refines hrel s_post" "State.clone_bounds_refines hrel s_post2"
expect_refused import-inv-field port-session-braid-import-proof.sh "$t/ImportInv.lean" \
  "  ct1_bounded : Tacenta.BraidT1.State.ct1_bounded b.state" "  ct1b : Tacenta.BraidT1.State.ct1_bounded b.state"
# The preservation port makes no unit edit: it is a count-checked substitution plus the unit's own
# pins, so its anchors are the substitution counts, the marker of the pin section and a declaration after
# the pins, which would be dropped from the unit.
expect_refused preserve-substitution-count port-session-braid-preserve.sh "$t/BraidPreserve.lean" \
  "open tacenta_braid
open Tacenta.BraidT1" "open tacenta_braid
open tacenta_braid
open Tacenta.BraidT1" "occurs"
expect_refused preserve-pin-marker port-session-braid-preserve.sh "$t/BraidPreserve.lean" \
  "/-! ## Axiom pins" "/-! ## Pins" "pin section marker changed"
expect_refused preserve-declaration-after-pins port-session-braid-preserve.sh "$t/BraidPreserve.lean" \
  "/-! ## Definition pins" "theorem appended_after_the_pins : (1 : Nat) = 1 := rfl

/-! ## Definition pins" "would be dropped from the unit"
echo "port negatives: each broken anchor is refused by the port script that edits it"
