#!/usr/bin/env bash
# Port the Braid preservation theorems onto the complete Session translation unit.
set -euo pipefail

cd "$(dirname "$0")/../.."

check=0
if [ "${1:-}" = "--check" ]; then
  check=1
elif [ $# -ne 0 ]; then
  echo "usage: port-session-braid-preserve.sh [--check]" >&2
  exit 1
fi

src=tacenta-proofs/translation/Translation/BraidPreserve.lean
dest=tacenta-proofs/translation/Translation/SessionUnitBraidPreserve.lean
tmp=$(mktemp)
cleanup() { rm -f "$tmp"; }
trap cleanup EXIT INT TERM

python3 - "$src" "$tmp" <<'PY'
from pathlib import Path
import re
import sys

src, dest = map(Path, sys.argv[1:3])
text = src.read_text()

# The pins at the end of the standalone file hold the standalone translation's axioms and
# statements. The unit has its own, written out below; everything before the marker is the proof.
marker = "\n/-! ## Axiom pins"
if text.count(marker) != 1:
    raise SystemExit("port-session-braid-preserve: the pin section marker changed")
tail = text[text.index(marker):]
# Pins are comments and `#guard_msgs` commands; a declaration after the marker would be dropped
# from the unit without a word, so it is refused. Block comments are removed first because a
# pin's expected text can begin a line with `def` or `inductive`.
code = re.sub(r"/-[-!].*?-/", "", tail, flags=re.S)
if re.search(r"^(theorem|lemma|def|inductive|structure|instance|abbrev|axiom)\b", code, re.M):
    raise SystemExit(
        "port-session-braid-preserve: a declaration after the pin section marker "
        "would be dropped from the unit")
text = text[:text.index(marker)] + "\n"

# `Tacenta.BraidPreserveDecoder` first: `Tacenta.BraidPreserve` is a prefix of it.
substitutions = [
    ("import Translation.BraidPreserveDecoder",
     "import Translation.SessionUnitBraidPreserveDecoder", 1),
    ("Tacenta.BraidPreserveDecoder", "Tacenta.SessionUnitBraidPreserveDecoder", 1),
    ("Tacenta.BraidPreserve", "Tacenta.SessionUnitBraidPreserve", 2),
    ("Tacenta.BraidT1", "Tacenta.SessionUnitBraidT1", 1),
    ("open tacenta_braid", "open tacenta_session_unit.tacenta_braid", 1),
    ("tacenta_erasure.", "tacenta_session_unit.tacenta_erasure.", 3),
    ("tacenta_kem.", "tacenta_session_unit.tacenta_kem.", 2),
    ("rand_core_1.", "tacenta_session_unit.rand_core_1.", 8),
]
for old, new, expected in substitutions:
    found = text.count(old)
    if found != expected:
        raise SystemExit(
            f"port-session-braid-preserve: {old!r} occurs {found} time(s), "
            f"expected {expected}; inspect the source proof before changing this count")
    text = text.replace(old, new)

# The proof text is unchanged: on the unit a decoder is a translated definition, so `Good` and
# `Laws` are read off its fields (`SessionUnitBraidPreserveDecoder.lean`) and every use below is
# through the lemmas that module states with the same signatures.

unit_pins = r'''
/-! ## Axiom pins

The axiom base of each result, held by the build.  The erasure decoder is a translated definition
on the unit, so the opaque erasure constants of the standalone pins are gone and the two library
operations the decoder's body reaches, `Vec::truncate` and `usize::div_ceil`, appear where a
result reaches them. -/

/--
info: 'Tacenta.SessionUnitBraidPreserve.Braid.step_send_sized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kdf.hkdf_sha256,
 tacenta_session_unit.tacenta_kdf.hmac_sha256,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.tacenta_kem.encapsulate1,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.rand_core_1.error.Error,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.generate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.header,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.core.num.Usize.div_ceil,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.SessionUnitBraidPreserve.Braid.step_send_sized

/--
info: 'Tacenta.SessionUnitBraidPreserve.Braid.step_receive_sized' depends on axioms: [propext,
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
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.alloc.vec.Vec.truncate,
 tacenta_session_unit.core.num.Usize.div_ceil,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.SessionUnitBraidPreserve.Braid.step_receive_sized

/--
info: 'Tacenta.SessionUnitBraidPreserve.State.clone_sized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone]
-/
#guard_msgs in
#print axioms Tacenta.SessionUnitBraidPreserve.State.clone_sized

/--
info: 'Tacenta.SessionUnitBraidPreserve.Braid.send_sized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kdf.hkdf_sha256,
 tacenta_session_unit.tacenta_kdf.hmac_sha256,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.tacenta_kem.encapsulate1,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.rand_core_1.error.Error,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.generate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.header,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.core.num.Usize.div_ceil,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 tacenta_session_unit.tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.SessionUnitBraidPreserve.Braid.send_sized

/--
info: 'Tacenta.SessionUnitBraidPreserve.Braid.receive_sized' depends on axioms: [propext,
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
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
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
#print axioms Tacenta.SessionUnitBraidPreserve.Braid.receive_sized

/--
info: 'Tacenta.SessionUnitBraidPreserve.Braid.commit_sized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair]
-/
#guard_msgs in
#print axioms Tacenta.SessionUnitBraidPreserve.Braid.commit_sized

/--
info: 'Tacenta.SessionUnitBraidPreserve.Braid.initiator_sized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kdf.hkdf_sha256,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref]
-/
#guard_msgs in
#print axioms Tacenta.SessionUnitBraidPreserve.Braid.initiator_sized

/--
info: 'Tacenta.SessionUnitBraidPreserve.Braid.responder_sized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kdf.hkdf_sha256,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.HEADER_LEN,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.alloc.vec.Vec.truncate,
 tacenta_session_unit.core.num.Usize.div_ceil,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref]
-/
#guard_msgs in
#print axioms Tacenta.SessionUnitBraidPreserve.Braid.responder_sized

/--
info: 'Tacenta.SessionUnitBraidPreserve.Braid.Run.sized' depends on axioms: [propext,
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
 tacenta_session_unit.tacenta_kem.encapsulate1,
 tacenta_session_unit.tacenta_kem.encapsulate2,
 tacenta_session_unit.tacenta_kem.validate_ek,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.rand_core_1.error.Error,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.generate,
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
#print axioms Tacenta.SessionUnitBraidPreserve.Braid.Run.sized

/--
info: 'Tacenta.SessionUnitBraidPreserve.Braid.Constructed.sized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kdf.hkdf_sha256,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.HEADER_LEN,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.alloc.vec.Vec.truncate,
 tacenta_session_unit.core.num.Usize.div_ceil,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref]
-/
#guard_msgs in
#print axioms Tacenta.SessionUnitBraidPreserve.Braid.Constructed.sized

/--
info: 'Tacenta.SessionUnitBraidPreserve.State.sized_ct1_bounded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair]
-/
#guard_msgs in
#print axioms Tacenta.SessionUnitBraidPreserve.State.sized_ct1_bounded

/--
info: 'Tacenta.SessionUnitBraidPreserve.Braid.Run.exists_initiator' depends on axioms: [propext,
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
 tacenta_session_unit.tacenta_kem.encapsulate1,
 tacenta_session_unit.tacenta_kem.encapsulate2,
 tacenta_session_unit.tacenta_kem.validate_ek,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.rand_core_1.error.Error,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.generate,
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
#print axioms Tacenta.SessionUnitBraidPreserve.Braid.Run.exists_initiator

/--
info: 'Tacenta.SessionUnitBraidPreserve.Braid.Run.exists_responder' depends on axioms: [propext,
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
 tacenta_session_unit.tacenta_kem.encapsulate1,
 tacenta_session_unit.tacenta_kem.encapsulate2,
 tacenta_session_unit.tacenta_kem.validate_ek,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.rand_core_1.error.Error,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.generate,
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
#print axioms Tacenta.SessionUnitBraidPreserve.Braid.Run.exists_responder

/--
info: 'Tacenta.SessionUnitBraidPreserve.Braid.Run.exists_send' depends on axioms: [propext,
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
 tacenta_session_unit.tacenta_kem.encapsulate1,
 tacenta_session_unit.tacenta_kem.encapsulate2,
 tacenta_session_unit.tacenta_kem.validate_ek,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.rand_core_1.error.Error,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.generate,
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
#print axioms Tacenta.SessionUnitBraidPreserve.Braid.Run.exists_send

/-! ## Statement pins

The axiom pins hold the constants a result depends on and not what it says.  These hold the
statements of the results below; `attest.py` requires each statement pin to exist
(`REQUIRED_STATEMENT_PINS`) and does not read what it says. -/

/--
info: Tacenta.SessionUnitBraidPreserve.Braid.step_send_sized {R : Type} (rc : tacenta_session_unit.rand_core_1.RngCore R)
  (crc : tacenta_session_unit.rand_core_1.CryptoRng R) (hrng : RngTotal rc) (hencaps1 : Encapsulate1Total)
  (self : Braid) (state : State) (rng : R) {m : Msg} {out : Option Output} {s' : State} {rng' : R}
  (h : Braid.step_send rc crc self state rng = ok ((m, out, s'), rng'))
  (hs : Tacenta.SessionUnitBraidPreserve.State.sized state) : Tacenta.SessionUnitBraidPreserve.State.sized s'
-/
#guard_msgs in
#check Tacenta.SessionUnitBraidPreserve.Braid.step_send_sized

/--
info: Tacenta.SessionUnitBraidPreserve.Braid.step_receive_sized (hl : Laws) (hct1len : Ct1LenTotal) (hct2len : Ct2LenTotal)
  (hhdrlen : HeaderLenTotal) (hekveclen : EkVectorLenTotal) (self : Braid) (state : State) (msg : Msg)
  (out : Option Output) (s' : State) (h : self.step_receive state msg = ok (out, s'))
  (hs : Tacenta.SessionUnitBraidPreserve.State.sized state) : Tacenta.SessionUnitBraidPreserve.State.sized s'
-/
#guard_msgs in
#check Tacenta.SessionUnitBraidPreserve.Braid.step_receive_sized

/--
info: Tacenta.SessionUnitBraidPreserve.Braid.send_sized {R : Type} (rc : tacenta_session_unit.rand_core_1.RngCore R)
  (crc : tacenta_session_unit.rand_core_1.CryptoRng R) (hrng : RngTotal rc) (hencaps1 : Encapsulate1Total)
  (self : Braid) (rng : R) {msg : Msg} {ep : U64} {out : Option Output} {next : Braid} {rng' : R}
  (h : Braid.send rc crc self rng = ok ((msg, ep, out, next), rng'))
  (hs : Tacenta.SessionUnitBraidPreserve.Braid.sized self) : Tacenta.SessionUnitBraidPreserve.Braid.sized next
-/
#guard_msgs in
#check Tacenta.SessionUnitBraidPreserve.Braid.send_sized

/--
info: Tacenta.SessionUnitBraidPreserve.Braid.receive_sized (hl : Laws) (hct1len : Ct1LenTotal) (hct2len : Ct2LenTotal)
  (hhdrlen : HeaderLenTotal) (hekveclen : EkVectorLenTotal) (self : Braid) (msg : Msg) {ep : U64} {out : Option Output}
  {next : Braid} (h : self.receive msg = ok (ep, out, next)) (hs : Tacenta.SessionUnitBraidPreserve.Braid.sized self) :
  Tacenta.SessionUnitBraidPreserve.Braid.sized next
-/
#guard_msgs in
#check Tacenta.SessionUnitBraidPreserve.Braid.receive_sized

/--
info: Tacenta.SessionUnitBraidPreserve.Braid.Run.sized (hl : Laws) (hct1len : Ct1LenTotal) (hct2len : Ct2LenTotal)
  (hhdrlen : HeaderLenTotal) (hekveclen : EkVectorLenTotal) (hencaps1 : Encapsulate1Total) {Base : Braid → Prop}
  (hbase : ∀ (b : Braid), Base b → Tacenta.SessionUnitBraidPreserve.Braid.sized b) {b : Braid}
  (hr : Tacenta.SessionUnitBraidPreserve.Braid.Run Base b) : Tacenta.SessionUnitBraidPreserve.Braid.sized b
-/
#guard_msgs in
#check Tacenta.SessionUnitBraidPreserve.Braid.Run.sized

/--
info: Tacenta.SessionUnitBraidPreserve.Braid.Run.exists_initiator (hkdf : HkdfSha256Total) (hz : ZeroizingArrayRoundTrip)
  (secret : Slice U8) :
  ∃ b, Tacenta.SessionUnitBraidPreserve.Braid.Run Tacenta.SessionUnitBraidPreserve.Braid.Constructed b
-/
#guard_msgs in
#check Tacenta.SessionUnitBraidPreserve.Braid.Run.exists_initiator

/--
info: Tacenta.SessionUnitBraidPreserve.Braid.Run.exists_responder (hkdf : HkdfSha256Total) (hz : ZeroizingArrayRoundTrip)
  (hdnew : DecoderNewTotal) (hhdrlen : HeaderLenTotal) (secret : Slice U8) :
  ∃ b, Tacenta.SessionUnitBraidPreserve.Braid.Run Tacenta.SessionUnitBraidPreserve.Braid.Constructed b
-/
#guard_msgs in
#check Tacenta.SessionUnitBraidPreserve.Braid.Run.exists_responder

/--
info: Tacenta.SessionUnitBraidPreserve.Braid.Run.exists_send {R : Type} (rc : tacenta_session_unit.rand_core_1.RngCore R)
  (crc : tacenta_session_unit.rand_core_1.CryptoRng R) (hrng : RngTotal rc) (henc : EncoderCloneTotal)
  (hdec : DecoderCloneTotal) (hkp : KeyPairCloneTotal) (hes : EncapsStateCloneTotal) (hgen : KeyPairGenerateTotal)
  (hhdr : KeyPairHeaderTotal) (hmac : HmacSha256Total) (henew : EncoderNewTotal) (henext : EncoderNextChunkTotal)
  (hkdf : HkdfSha256Total) (hencaps1 : Encapsulate1Total) (hz : ZeroizingArrayRoundTrip) (hzz : ArrayZeroizeTotal)
  (hrf : RangeFullIndexTotal) (secret : Slice U8) (rng : R) :
  ∃ b b',
    Tacenta.SessionUnitBraidPreserve.Braid.Run Tacenta.SessionUnitBraidPreserve.Braid.Constructed b ∧
      Tacenta.SessionUnitBraidPreserve.Braid.Run Tacenta.SessionUnitBraidPreserve.Braid.Constructed b' ∧
        ∃ msg ep out rng', Braid.send rc crc b rng = ok ((msg, ep, out, b'), rng')
-/
#guard_msgs in
#check Tacenta.SessionUnitBraidPreserve.Braid.Run.exists_send

/--
info: Tacenta.SessionUnitBraidPreserve.State.clone_sized {self r : State} (h : State.Insts.CoreCloneClone.clone self = ok r)
  (hs : Tacenta.SessionUnitBraidPreserve.State.sized self) : Tacenta.SessionUnitBraidPreserve.State.sized r
-/
#guard_msgs in
#check Tacenta.SessionUnitBraidPreserve.State.clone_sized

/--
info: Tacenta.SessionUnitBraidPreserve.Braid.commit_sized {self next r : Braid} (h : self.commit next = ok r)
  (hs : Tacenta.SessionUnitBraidPreserve.Braid.sized next) : Tacenta.SessionUnitBraidPreserve.Braid.sized r
-/
#guard_msgs in
#check Tacenta.SessionUnitBraidPreserve.Braid.commit_sized

/--
info: Tacenta.SessionUnitBraidPreserve.Braid.initiator_sized {secret : Slice U8} {b : Braid}
  (h : Braid.initiator secret = ok b) : Tacenta.SessionUnitBraidPreserve.Braid.sized b
-/
#guard_msgs in
#check Tacenta.SessionUnitBraidPreserve.Braid.initiator_sized

/--
info: Tacenta.SessionUnitBraidPreserve.Braid.responder_sized (hl : Laws) (hhdrlen : HeaderLenTotal) {secret : Slice U8}
  {b : Braid} (h : Braid.responder secret = ok b) : Tacenta.SessionUnitBraidPreserve.Braid.sized b
-/
#guard_msgs in
#check Tacenta.SessionUnitBraidPreserve.Braid.responder_sized

/--
info: Tacenta.SessionUnitBraidPreserve.Braid.Constructed.sized (hl : Laws) (hhdrlen : HeaderLenTotal) {b : Braid}
  (h : Tacenta.SessionUnitBraidPreserve.Braid.Constructed b) : Tacenta.SessionUnitBraidPreserve.Braid.sized b
-/
#guard_msgs in
#check Tacenta.SessionUnitBraidPreserve.Braid.Constructed.sized

/--
info: Tacenta.SessionUnitBraidPreserve.State.sized_ct1_bounded {s : State}
  (h : Tacenta.SessionUnitBraidPreserve.State.sized s) : State.ct1_bounded s
-/
#guard_msgs in
#check Tacenta.SessionUnitBraidPreserve.State.sized_ct1_bounded

/-! ## Definition pins

The definitions that carry the claim.  A change to a clause, a constructor or a law fails the
build while its pin is present; `attest.py` requires each definition pin to exist
(`REQUIRED_STATEMENT_PINS`) and does not read what it says. -/

/--
info: def Tacenta.SessionUnitBraidPreserve.State.sized : State → Prop :=
fun x =>
  match x with
  | State.KeysUnsampled a a_1 => True
  | State.KeysSampled a a_1 a_2 a_3 => True
  | State.HeaderSent a a_1 a_2 ct1_dec a_3 => Good 4096 ct1_dec
  | State.Ct1Received a a_1 a_2 ct1 a_3 => ct1.length ≤ 4096
  | State.EkSentCt1Received a a_1 a_2 ct1 ct2_dec => ct1.length ≤ 4096 ∧ Good 4128 ct2_dec
  | State.NoHeaderReceived a a_1 hdr_dec => Good 4128 hdr_dec
  | State.HeaderReceived a a_1 a_2 ek_dec => Good 4128 ek_dec
  | State.Ct1Sampled a a_1 a_2 a_3 ct1 a_4 ek_dec => ct1.length ≤ 4096 ∧ Good 4128 ek_dec
  | State.EkReceivedCt1Sampled a a_1 a_2 ct1 a_3 a_4 => ct1.length ≤ 4096
  | State.Ct1Acknowledged a a_1 a_2 a_3 ct1 ek_dec => ct1.length ≤ 4096 ∧ Good 4128 ek_dec
  | State.Ct2Sampled a a_1 a_2 => True
  | State.Failed => True
-/
#guard_msgs in
#print Tacenta.SessionUnitBraidPreserve.State.sized

/--
info: def Tacenta.SessionUnitBraidPreserve.Braid.sized : Braid → Prop :=
fun b => Tacenta.SessionUnitBraidPreserve.State.sized b.state
-/
#guard_msgs in
#print Tacenta.SessionUnitBraidPreserve.Braid.sized

/--
info: inductive Tacenta.SessionUnitBraidPreserve.Braid.Run : (Braid → Prop) → Braid → Prop
number of parameters: 1
constructors:
Tacenta.SessionUnitBraidPreserve.Braid.Run.base : ∀ {Base : Braid → Prop} {b : Braid},
  Base b → Tacenta.SessionUnitBraidPreserve.Braid.Run Base b
Tacenta.SessionUnitBraidPreserve.Braid.Run.send : ∀ {Base : Braid → Prop} {R : Type}
  {rc : tacenta_session_unit.rand_core_1.RngCore R} {crc : tacenta_session_unit.rand_core_1.CryptoRng R},
  RngTotal rc →
    ∀ {self : Braid} {rng : R} {msg : Msg} {ep : U64} {out : Option Output} {next : Braid} {rng' : R},
      Tacenta.SessionUnitBraidPreserve.Braid.Run Base self →
        Braid.send rc crc self rng = ok ((msg, ep, out, next), rng') →
          Tacenta.SessionUnitBraidPreserve.Braid.Run Base next
Tacenta.SessionUnitBraidPreserve.Braid.Run.receive : ∀ {Base : Braid → Prop} {self : Braid} {msg : Msg} {ep : U64}
  {out : Option Output} {next : Braid},
  Tacenta.SessionUnitBraidPreserve.Braid.Run Base self →
    self.receive msg = ok (ep, out, next) → Tacenta.SessionUnitBraidPreserve.Braid.Run Base next
-/
#guard_msgs in
#print Tacenta.SessionUnitBraidPreserve.Braid.Run

/--
info: def Tacenta.SessionUnitBraidPreserve.Braid.Constructed : Braid → Prop :=
fun b => (∃ secret, Braid.initiator secret = ok b) ∨ ∃ secret, Braid.responder secret = ok b
-/
#guard_msgs in
#print Tacenta.SessionUnitBraidPreserve.Braid.Constructed
'''
note = (
    "-- Generated by tacenta-proofs/scripts/port-session-braid-preserve.sh from\n"
    "-- Translation/BraidPreserve.lean. Do not edit: the script's `--check` mode\n"
    "-- regenerates this count-checked port and rejects drift. The unit's own pins replace\n"
    "-- the standalone file's.\n\n"
)
dest.write_text(note + text + unit_pins)
PY

if [ "$check" -eq 0 ]; then
  mv "$tmp" "$dest"
  echo "port-session-braid-preserve: wrote SessionUnitBraidPreserve.lean"
  exit 0
fi

if ! diff -u "$dest" "$tmp" >/dev/null; then
  diff -u "$dest" "$tmp" | head -40 >&2
  echo "port-session-braid-preserve: committed copy differs; regenerate and rebuild" >&2
  exit 1
fi
echo "port-session-braid-preserve: the committed copy is deterministic"
