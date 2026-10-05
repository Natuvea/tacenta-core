#!/usr/bin/env bash
# Port Braid T3 onto the complete Session translation unit.
set -euo pipefail

cd "$(dirname "$0")/../.."

check=0
if [ "${1:-}" = "--check" ]; then
  check=1
elif [ $# -ne 0 ]; then
  echo "usage: port-session-braid-refinement.sh [--check]" >&2
  exit 1
fi

src=tacenta-proofs/translation/Translation/BraidT3.lean
dest=tacenta-proofs/translation/Translation/SessionUnitBraidT3.lean
tmp=$(mktemp)
cleanup() { rm -f "$tmp"; }
trap cleanup EXIT INT TERM

python3 - "$src" "$tmp" <<'PY'
from pathlib import Path
import sys

src, dest = map(Path, sys.argv[1:3])
text = src.read_text()
substitutions = [
    ("Translation.TacentaBraid", "Translation.TacentaSessionUnit", 1),
    ("Translation.BraidT1", "Translation.SessionUnitBraidT1", 1),
    ("Tacenta.BraidT3", "Tacenta.SessionUnitBraidT3", 6),
    ("Tacenta.BraidT1", "Tacenta.SessionUnitBraidT1", 118),
    ("open tacenta_braid", "open tacenta_session_unit.tacenta_braid", 1),
    ("tacenta_braid.", "tacenta_session_unit.tacenta_braid.", 8),
    ("tacenta_erasure.", "tacenta_session_unit.tacenta_erasure.", 67),
    ("tacenta_kem.", "tacenta_session_unit.tacenta_kem.", 65),
    ("tacenta_kdf.", "tacenta_session_unit.tacenta_kdf.", 7),
    ("rand_core_1.", "tacenta_session_unit.rand_core_1.", 10),
    ("zeroize.", "tacenta_session_unit.zeroize.", 8),
    ("Array.Insts.", "tacenta_session_unit.Array.Insts.", 2),
    ("core.option.", "tacenta_session_unit.core.option.", 1),
    ("core.ops.range.", "tacenta_session_unit.core.ops.range.", 12),
]
for old, new, expected in substitutions:
    found = text.count(old)
    if found != expected:
        raise SystemExit(
            f"port-session-braid-refinement: {old!r} occurs {found} time(s), "
            f"expected {expected}; inspect the source proof before changing this count")
    text = text.replace(old, new)

imports_end = "import Aeneas.Data.BitVec\n"
if text.count(imports_end) != 1:
    raise SystemExit("port-session-braid-refinement: import anchor changed")
text = text.replace(imports_end, imports_end + """

-- Imported leaf proofs register rules for the same aggregate primitives.
-- The erasure rule applies only to 32-byte decoder slices, and the ratchet's
-- Zeroizing boundary is unrelated to Braid's array wrapper.
attribute [-step] Tacenta.SessionUnitErasureT1.extend_slice32_spec
attribute [-step] Tacenta.SessionUnitT1.zeroizing_new_step
attribute [-step] Tacenta.SessionUnitT1.zeroizing_deref_step
""", 1)

# In the complete unit `Decoder::message` is a translated definition and returns only for a
# decoder with a protocol-sized output reservation and at most `MAX_CODEWORDS` chunks
# (`SessionUnitBraidT1.DecoderMessageTotal` states both, and `SessionBraidReceiveVacuity.lean`
# refutes the statement without the chunk bound). The refinement theorems therefore take the
# two bounds from the state (`State.decoders_sized` and `State.decoders_bounded`), carry them
# across `add_chunk` and across the state clone, and pass them to `hdmsg`. The
# standalone BraidT3.lean has an opaque `Decoder` and keeps its statements. Each edit below
# names the place it changes and fails if the source proof no longer has exactly that text.
def unit_edit(text, label, old, new, expected=1):
    found = text.count(old)
    if found != expected:
        raise SystemExit(
            f"port-session-braid-refinement: unit edit {label!r}: text occurs {found} time(s), "
            f"expected {expected}; inspect the source proof before changing this edit")
    return text.replace(old, new)

for name, count in [("ct1_dec1", 1), ("ek_dec1", 3), ("ct2_dec1", 1), ("hdr_dec1", 1)]:
    text = unit_edit(text, f"message call on {name}",
        f"obtain ⟨omsg, homsg⟩ := hdmsg {name}\n",
        f"obtain ⟨omsg, homsg⟩ := hdmsg {name} "
        f"(Tacenta.SessionUnitDecoderBound.size_le_after_add_chunk hadd hds) "
        f"(Tacenta.SessionUnitDecoderBound.needed_le_after_add_chunk hadd hdb)\n", count)

text = unit_edit(text, "step_receive_refines signature",
    """    (hct1b : Tacenta.SessionUnitBraidT1.State.ct1_bounded state)
    (hepoch : (Tacenta.SessionUnitBraidT1.State.epoch_val state).val + 1 < Std.U64.max)""",
    """    (hct1b : Tacenta.SessionUnitBraidT1.State.ct1_bounded state)
    (hdb : Tacenta.SessionUnitBraidT1.State.decoders_bounded state)
    (hds : Tacenta.SessionUnitBraidT1.State.decoders_sized state)
    (hepoch : (Tacenta.SessionUnitBraidT1.State.epoch_val state).val + 1 < Std.U64.max)""")

text = unit_edit(text, "receive_refines signature",
    """    (hct1b : Tacenta.SessionUnitBraidT1.State.ct1_bounded self.state)
    (hepoch : (Tacenta.SessionUnitBraidT1.State.epoch_val self.state).val + 1 < Std.U64.max)""",
    """    (hct1b : Tacenta.SessionUnitBraidT1.State.ct1_bounded self.state)
    (hdb : Tacenta.SessionUnitBraidT1.State.decoders_bounded self.state)
    (hds : Tacenta.SessionUnitBraidT1.State.decoders_sized self.state)
    (hepoch : (Tacenta.SessionUnitBraidT1.State.epoch_val self.state).val + 1 < Std.U64.max)""")

text = unit_edit(text, "receive_refines clone step",
    """  step with State.clone_refines hkcl hecl henc hdec hkp hes hrel
  obtain ⟨hepocheq, hct1bimp⟩ := State.clone_bounds_refines hrel s_post
""",
    """  step with Tacenta.SessionUnitDecoderBound.spec_and
    (State.clone_refines hkcl hecl henc hdec hkp hes hrel)
    (Tacenta.SessionUnitBraidT1.State.clone_no_panic henc hdec hkp hes self.state)
  have s_post : StateRefines K s model := s_post1
  obtain ⟨hepocheq, hct1bimp⟩ := State.clone_bounds_refines hrel s_post
""")

text = unit_edit(text, "receive_refines step_receive call",
    "self s msg (hct1bimp hct1b) (by rw [hepocheq]; exact hepoch)",
    "self s msg (hct1bimp hct1b) (s_post4 hdb) (s_post5 hds) (by rw [hepocheq]; exact hepoch)")

text = unit_edit(text, "step_receive_refines note on the decoder bound",
    """but `epoch + 1 < u64::MAX` is strictly more than that, and is the caller's
premise, not a fact about reachable states. -/""",
    """but `epoch + 1 < u64::MAX` is strictly more than that, and is the caller's
premise, not a fact about reachable states.

`hdb` is the decoder chunk bound (`SessionUnitBraidT1.State.decoders_bounded`) and `hds` is the
decoder output-size bound (`State.decoders_sized`). `hdmsg` is stated for decoders satisfying both,
because the unit's `Decoder::message` fails for a decoder that needs and holds
`(Usize.max + 1) / 32` chunks, and the Braid's bound `MAX_CODEWORDS` is far below that; `add_chunk` keeps `needed`
(`SessionUnitDecoderBound`) and `size`, so the state bounds give them for the decoder after the
chunk is added. -/""")

remove = [
    "tacenta_session_unit.tacenta_erasure.Decoder",
    "tacenta_session_unit.tacenta_erasure.Encoder",
    "tacenta_session_unit.tacenta_erasure.Decoder.add_chunk",
    "tacenta_session_unit.tacenta_erasure.Decoder.message",
    "tacenta_session_unit.tacenta_erasure.Decoder.new",
    "tacenta_session_unit.tacenta_erasure.Encoder.new",
    "tacenta_session_unit.tacenta_erasure.Encoder.next_chunk",
    "tacenta_session_unit.tacenta_erasure.Decoder.Insts.CoreCloneClone.clone",
    "tacenta_session_unit.tacenta_erasure.Encoder.Insts.CoreCloneClone.clone",
]
for name in ("send_refines", "receive_refines"):
    marker = f"info: 'Tacenta.SessionUnitBraidT3.Braid.{name}' depends on axioms: ["
    start = text.index(marker)
    end = text.index("]\n-/", start)
    block = text[start:end + 1]
    lines = block.splitlines()
    for item in remove:
        target = f" {item},"
        matches = [i for i, line in enumerate(lines) if line == target]
        if len(matches) != 1:
            raise SystemExit(f"port-session-braid-refinement: audit item {item!r} changed")
        lines.pop(matches[0])
    insert_at = next(i for i, line in enumerate(lines)
                     if "zeroize.Zeroize.Blanket.zeroize" in line)
    lines.insert(insert_at, " tacenta_session_unit.core.num.Usize.div_ceil,")
    lines.insert(insert_at, " tacenta_session_unit.alloc.vec.Vec.truncate,")
    text = text[:start] + "\n".join(lines) + text[end + 1:]

note = (
    "-- Generated by tacenta-proofs/scripts/port-session-braid-refinement.sh from\n"
    "-- Translation/BraidT3.lean. Do not edit: the script's `--check` mode\n"
    "-- regenerates this count-checked aggregate proof and rejects drift. The named\n"
    "-- `unit_edit`s add the hypothesis `hdb` (`State.decoders_bounded`) that the\n"
    "-- standalone proof does not take.\n\n"
)
dest.write_text(note + text)
PY

if [ "$check" -eq 0 ]; then
  mv "$tmp" "$dest"
  echo "port-session-braid-refinement: wrote SessionUnitBraidT3.lean"
  exit 0
fi

if ! diff -u "$dest" "$tmp" >/dev/null; then
  diff -u "$dest" "$tmp" | head -40 >&2 || true
  echo "port-session-braid-refinement: committed copy differs; regenerate and rebuild" >&2
  exit 1
fi
echo "port-session-braid-refinement: the committed copy is deterministic"
