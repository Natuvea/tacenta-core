#!/usr/bin/env bash
# Port ImportInv's Braid section onto the complete Session unit.
set -euo pipefail

cd "$(dirname "$0")/../.."

check=0
if [ "${1:-}" = "--check" ]; then
  check=1
elif [ $# -ne 0 ]; then
  echo "usage: port-session-braid-import-proof.sh [--check]" >&2
  exit 1
fi

src=tacenta-proofs/translation/Translation/ImportInv.lean
dest=tacenta-proofs/translation/Translation/SessionUnitBraidImportInv.lean
tmp=$(mktemp)
cleanup() { rm -f "$tmp"; }
trap cleanup EXIT INT TERM

python3 - "$src" "$tmp" <<'PY'
from pathlib import Path
import sys

src, dest = map(Path, sys.argv[1:3])
text = src.read_text()
start_marker = '/-! # `tacenta-braid`'
end_marker = '\nend Braid'
if text.count(start_marker) != 1:
    raise SystemExit("port-session-braid-import-proof: Braid section marker changed")
start = text.index(start_marker)
end = text.index(end_marker, start) + len(end_marker)
body = text[start:end]
substitutions = [
    ("Tacenta.BraidT1", "Tacenta.SessionUnitBraidT1", 5),
    ("open tacenta_braid", "open tacenta_session_unit.tacenta_braid", 1),
]
for old, new, expected in substitutions:
    found = body.count(old)
    if found != expected:
        raise SystemExit(
            f"port-session-braid-import-proof: {old!r} occurs {found} "
            f"time(s), expected {expected}; inspect the source proof before changing this count")
    body = body.replace(old, new)

# In the complete unit the erasure decoder is a translated definition, so `Braid::invariant`
# can be unfolded to the `Decoder::invariant` calls it makes, and that is what gives the receive
# theorems their decoder bound (`State.decoders_bounded`; `Decoder::message` returns only for a
# decoder that needs at most `MAX_CODEWORDS` chunks). The standalone ImportInv.lean has opaque
# erasure types and derives the `ct1_bounded` clause alone. Each edit below names the place it
# changes and fails if the source proof no longer has exactly that text.
def unit_edit(text, label, old, new, expected=1):
    found = text.count(old)
    if found != expected:
        raise SystemExit(
            f"port-session-braid-import-proof: unit edit {label!r}: text occurs {found} "
            f"time(s), expected {expected}; inspect the source proof before changing this edit")
    return text.replace(old, new)

body = unit_edit(body, "Inv docstring",
    """/-- What this module derives for the Braid: a partial mirror of the Rust
`invariant`, holding the one clause the theorems need. Deliberately not the
whole predicate -- the rest of it is about the erasure coders, which are
opaque here. -/""",
    """/-- What this module derives for the Braid: a partial mirror of the Rust
`invariant`, holding the two clauses the receive theorems need: the size cap on the stored
KEM ciphertext and, because the complete unit translates the erasure decoders, the bound on
every decoder's `needed`. Deliberately not the whole predicate -- the rest of it (the
encoders, the key pair, the decoders' other clauses) no theorem here uses. -/""")

body = unit_edit(body, "Inv structure",
    """structure Inv (b : Braid) : Prop where
  ct1_bounded : Tacenta.SessionUnitBraidT1.State.ct1_bounded b.state
""",
    """structure Inv (b : Braid) : Prop where
  ct1_bounded : Tacenta.SessionUnitBraidT1.State.ct1_bounded b.state
  /-- In the complete unit the erasure decoders are translated, and `Braid::invariant` calls
  `Decoder::invariant` on each one it holds; that rejects a `needed` above `MAX_CODEWORDS`. -/
  decoders_bounded : Tacenta.SessionUnitBraidT1.State.decoders_bounded b.state
""")

body = unit_edit(body, "decoders_bounded from the invariant",
    """/-- **The translated `invariant` returning `true` implies `Inv`.**""",
    """/-- **The translated `invariant` returning `true` bounds every decoder the state holds.**
Each arm that holds a decoder runs `Decoder::invariant` on it, and a decoder that passes needs
at most `MAX_CODEWORDS` chunks (`SessionUnitDecoderBound.invariant_true_needed_le`). No
assumption on any opaque operation. -/
theorem invariant_true_gives_decoders_bounded (b : Braid)
    (h : Braid.invariant b = ok true) :
    Tacenta.SessionUnitBraidT1.State.decoders_bounded b.state := by
  rw [Braid.invariant] at h
  rcases hst : b.state with _|_|_|_|_|_|_|_|_|_|_|_ <;>
    rw [hst] at h <;> simp only [Tacenta.SessionUnitBraidT1.State.decoders_bounded]
  all_goals (
    repeat' first
      | (replace h := bind_eq_ok_inv h; obtain ⟨_, hb, h⟩ := h)
      | split at h
      | simp at h
    all_goals first
      | trivial
      | exact Tacenta.SessionUnitDecoderBound.invariant_true_needed_le _ (by simp_all))

/-- **The translated `invariant` returning `true` implies `Inv`.**""")

body = unit_edit(body, "invariant_true_gives_inv constructor",
    """  obtain ⟨v, hv, hvle⟩ := hct1
  constructor
  rw [Braid.invariant] at h""",
    """  obtain ⟨v, hv, hvle⟩ := hct1
  refine ⟨?_, invariant_true_gives_decoders_bounded b h⟩
  rw [Braid.invariant] at h""")

body = unit_edit(body, "decoded_receive_no_panic decoder bound",
    """    (from_bytes_establishes_inv hct1len bytes self hdec').ct1_bounded
""",
    """    (from_bytes_establishes_inv hct1len bytes self hdec').ct1_bounded
    (from_bytes_establishes_inv hct1len bytes self hdec').decoders_bounded
""")

body = unit_edit(body, "decoded receive title",
    """/-- **Decoded Braid → `Inv` → `ct1_bounded` → `BraidT1.Braid.receive_no_panic`.**""",
    """/-- **Decoded Braid → `Inv` → `ct1_bounded` and `decoders_bounded` → `Braid.receive_no_panic`.**""")

header = """-- Generated by tacenta-proofs/scripts/port-session-braid-import-proof.sh
-- from the Braid section of Translation/ImportInv.lean. Do not edit: the
-- script's `--check` mode regenerates this count-checked aggregate proof. The named
-- `unit_edit`s add the field `decoders_bounded` to `Inv`, which the standalone proof lacks.

import Translation.SessionUnitBraidT3
import Translation.SessionUnitRatchetImportInv

open Aeneas Aeneas.Std Result

namespace Tacenta.SessionUnitBraidImportInv

-- Reuse only the generic Result-bind peeling lemmas from the ratchet import
-- port. The Braid declarations below are all in this file's namespace.
open Tacenta.SessionUnitRatchetImportInv

"""

guards = r'''

/-!
The complete unit makes the erasure implementation concrete. These exact
pins therefore omit the standalone Braid translation's opaque erasure
declarations and expose only the generated unit's remaining boundaries.
-/

/--
info: 'Tacenta.SessionUnitBraidImportInv.Braid.from_bytes_establishes_inv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kem.CT1_LEN,
 tacenta_session_unit.tacenta_kem.CT2_LEN,
 tacenta_session_unit.tacenta_kem.EK_VECTOR_LEN,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.HEADER_LEN,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.tacenta_kem.validate_ek,
 tacenta_session_unit.tacenta_kem.EncapsState.from_bytes,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.from_bytes,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.header,
 tacenta_session_unit.core.num.Usize.div_ceil]
-/
#guard_msgs in
#print axioms Tacenta.SessionUnitBraidImportInv.Braid.from_bytes_establishes_inv

/--
info: 'Tacenta.SessionUnitBraidImportInv.Braid.invariant_true_gives_decoders_bounded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kem.CT1_LEN,
 tacenta_session_unit.tacenta_kem.CT2_LEN,
 tacenta_session_unit.tacenta_kem.EK_VECTOR_LEN,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.HEADER_LEN,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.tacenta_kem.validate_ek,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.header,
 tacenta_session_unit.core.num.Usize.div_ceil]
-/
#guard_msgs in
#print axioms Tacenta.SessionUnitBraidImportInv.Braid.invariant_true_gives_decoders_bounded

/--
info: 'Tacenta.SessionUnitBraidImportInv.Braid.decoded_receive_no_panic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kdf.hkdf_sha256,
 tacenta_session_unit.tacenta_kdf.hmac_sha256,
 tacenta_session_unit.tacenta_kem.CT1_LEN,
 tacenta_session_unit.tacenta_kem.CT2_LEN,
 tacenta_session_unit.tacenta_kem.EK_VECTOR_LEN,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.HEADER_LEN,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.tacenta_kem.encapsulate2,
 tacenta_session_unit.tacenta_kem.validate_ek,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.tacenta_kem.EncapsState.from_bytes,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.from_bytes,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.header,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.alloc.vec.Vec.truncate,
 tacenta_session_unit.core.num.Usize.div_ceil,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 tacenta_session_unit.tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.core.option.Option.Insts.CoreCloneClone.clone,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.SessionUnitBraidImportInv.Braid.decoded_receive_no_panic

end Tacenta.SessionUnitBraidImportInv
'''
dest.write_text(header + body + guards)
PY

if [ "$check" -eq 0 ]; then
  mv "$tmp" "$dest"
  echo "port-session-braid-import-proof: wrote SessionUnitBraidImportInv.lean"
  exit 0
fi

if ! diff -u "$dest" "$tmp" >/dev/null; then
  diff -u "$dest" "$tmp" | head -40 >&2 || true
  echo "port-session-braid-import-proof: committed copy differs; regenerate and rebuild" >&2
  exit 1
fi
echo "port-session-braid-import-proof: the committed copy is deterministic"
