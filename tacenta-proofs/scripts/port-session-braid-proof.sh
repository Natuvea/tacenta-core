#!/usr/bin/env bash
# Port Braid T1 onto the complete Session translation unit.
set -euo pipefail

cd "$(dirname "$0")/../.."

check=0
if [ "${1:-}" = "--check" ]; then
  check=1
elif [ $# -ne 0 ]; then
  echo "usage: port-session-braid-proof.sh [--check]" >&2
  exit 1
fi

src=tacenta-proofs/translation/Translation/BraidT1.lean
dest=tacenta-proofs/translation/Translation/SessionUnitBraidT1.lean
tmp=$(mktemp)
cleanup() { rm -f "$tmp"; }
trap cleanup EXIT INT TERM

python3 - "$src" "$tmp" <<'PY'
from pathlib import Path
import sys

src, dest = map(Path, sys.argv[1:3])
text = src.read_text()
substitutions = [
    ("import Translation.TacentaBraid\nimport Translation.SessionT1", """import Translation.TacentaSessionUnit
import Translation.SessionUnitSessionT1
import Translation.SessionUnitErasureT1
import Translation.SessionUnitDecoderBound

-- The complete unit imports proof modules whose global `step` rules target
-- the same generated primitives. These rules are intentionally narrower
-- than Braid's calls: the erasure decoder appends exactly 32-byte slices and
-- the ratchet uses its own `ZeroizingTotal` boundary. Leaving them registered
-- makes `step*` select an inapplicable side condition in this aggregate proof.
attribute [-step] Tacenta.SessionUnitErasureT1.extend_slice32_spec
attribute [-step] Tacenta.SessionUnitT1.zeroizing_new_step
attribute [-step] Tacenta.SessionUnitT1.zeroizing_deref_step""", 1),
    ("Tacenta.BraidT1", "Tacenta.SessionUnitBraidT1", 6),
    ("open tacenta_braid", "open tacenta_session_unit.tacenta_braid", 1),
    ("tacenta_erasure.", "tacenta_session_unit.tacenta_erasure.", 28),
    ("tacenta_kem.", "tacenta_session_unit.tacenta_kem.", 39),
    ("tacenta_kdf.", "tacenta_session_unit.tacenta_kdf.", 6),
    ("rand_core_1.", "tacenta_session_unit.rand_core_1.", 10),
    ("zeroize.", "tacenta_session_unit.zeroize.", 24),
    ("Array.Insts.", "tacenta_session_unit.Array.Insts.", 9),
    ("U8.Insts.", "tacenta_session_unit.U8.Insts.", 7),
    ("core.option.", "tacenta_session_unit.core.option.", 2),
    ("core.ops.range.", "tacenta_session_unit.core.ops.range.", 15),
]
for old, new, expected in substitutions:
    found = text.count(old)
    if found != expected:
        raise SystemExit(
            f"port-session-braid-proof: {old!r} occurs {found} time(s), "
            f"expected {expected}; inspect the source proof before changing this count")
    text = text.replace(old, new)

# The erasure decoder is concrete inside the complete unit, so `Decoder::message` is a
# translated definition and "it returns for every decoder" is false (a decoder that needs
# (Usize.max + 1) / 32 chunks overflows the output vector; see SessionBraidReceiveVacuity.lean).
# The standalone BraidT1.lean has an opaque `Decoder` and keeps its statement. In the unit the
# field is stated for decoders with both a protocol-sized output reservation and at most
# MAX_CODEWORDS chunks, and the receive theorems take those bounds from the state
# (`State.decoders_sized` and `State.decoders_bounded`). Each edit below names the place it changes and
# fails if the source proof no longer has exactly that text.
def unit_edit(text, label, old, new, expected=1):
    found = text.count(old)
    if found != expected:
        raise SystemExit(
            f"port-session-braid-proof: unit edit {label!r}: text occurs {found} time(s), "
            f"expected {expected}; inspect the source proof before changing this edit")
    return text.replace(old, new)

E = "tacenta_session_unit.tacenta_erasure."

text = unit_edit(text, "DecoderMessageTotal",
    f"""def DecoderMessageTotal : Prop :=
  ∀ (d : {E}Decoder), ∃ r, {E}Decoder.message d = ok r
""",
    f"""/-- `Decoder::message` returns for every protocol-sized decoder that needs at most
`MAX_CODEWORDS` (65536) chunks. Both bounds matter in the concrete unit: the translated function
reserves its output by `size`, while its reconstruction workspace is bounded by `needed`. The
old needed-only field admitted a decoder with a small `needed` and a huge `size`, which is not a
real reachable decoder but is enough to make the contract vacuous at the translated boundary.
The field is stated for `size <= 4128`, the largest Braid decoder, and `needed <= 65536`; the
preservation facts supply both. The unbounded statement remains false for the old witness in
`SessionBraidReceiveVacuity.lean`. -/
def DecoderMessageTotal : Prop :=
  ∀ (d : {E}Decoder), d.size.val ≤ 4128 → d.needed.val ≤ 65536 →
    ∃ r, {E}Decoder.message d = ok r

/-- `DecoderMessageTotal` without the bound on `needed`. It is false
(`Tacenta.SessionBraidReceiveVacuity.decoderMessage_not_total`) and nothing assumes it; it is
kept so that refutation stays a checked statement about the predicate the unit used to take. -/
def DecoderMessageTotalUnbounded : Prop :=
  ∀ (d : {E}Decoder), ∃ r, {E}Decoder.message d = ok r
""")

text = unit_edit(text, "State.decoders_bounded",
    """  | .Ct1Acknowledged _ _ _ _ ct1 _ => ct1.length ≤ 4096
  | _ => True

""",
    f"""  | .Ct1Acknowledged _ _ _ _ ct1 _ => ct1.length ≤ 4096
  | _ => True

/-- The decoder side of `State.ct1_bounded`: every erasure decoder the state holds needs at
most `MAX_CODEWORDS` (65536) chunks. `Braid::invariant` calls `Decoder::invariant` on each of
them and that rejects a larger `needed` (`SessionUnitBraidImportInv.Braid.Inv.decoders_bounded`);
`Decoder::add_chunk` and `Decoder::clone` keep `needed` (`SessionUnitDecoderBound`), and a
decoder `Decoder::new` builds from a protocol constant meets the bound given the value law of
`div_ceil` (`UnitLifecycleT1.braid_responder_headroom`). The receive theorems need it to call
`DecoderMessageTotal` on the decoder after a chunk is added. -/
def State.decoders_bounded : State → Prop
  | .HeaderSent _ _ _ ct1_dec _ => ct1_dec.needed.val ≤ 65536
  | .EkSentCt1Received _ _ _ _ ct2_dec => ct2_dec.needed.val ≤ 65536
  | .NoHeaderReceived _ _ hdr_dec => hdr_dec.needed.val ≤ 65536
  | .HeaderReceived _ _ _ ek_dec => ek_dec.needed.val ≤ 65536
  | .Ct1Sampled _ _ _ _ _ _ ek_dec => ek_dec.needed.val ≤ 65536
  | .Ct1Acknowledged _ _ _ _ _ ek_dec => ek_dec.needed.val ≤ 65536
  | _ => True

/-- The output reservation of every decoder held by a reachable Braid is at
most the largest protocol decoder (4128 bytes). This is separate from
`decoders_bounded`, whose name and callers retain the chunk-count fact. -/
def State.decoders_sized : State → Prop
  | .HeaderSent _ _ _ ct1_dec _ => ct1_dec.size.val ≤ 4128
  | .EkSentCt1Received _ _ _ _ ct2_dec => ct2_dec.size.val ≤ 4128
  | .NoHeaderReceived _ _ hdr_dec => hdr_dec.size.val ≤ 4128
  | .HeaderReceived _ _ _ ek_dec => ek_dec.size.val ≤ 4128
  | .Ct1Sampled _ _ _ _ _ _ ek_dec => ek_dec.size.val ≤ 4128
  | .Ct1Acknowledged _ _ _ _ _ ek_dec => ek_dec.size.val ≤ 4128
  | _ => True

""")

text = unit_edit(text, "State.clone_no_panic postcondition",
    """      ⦃ fun r => State.epoch_val r = State.epoch_val self ∧
                 (State.ct1_bounded self → State.ct1_bounded r) ⦄ := by""",
    """      ⦃ fun r => State.epoch_val r = State.epoch_val self ∧
                 (State.ct1_bounded self → State.ct1_bounded r) ∧
                 (State.decoders_bounded self → State.decoders_bounded r) ∧
                 (State.decoders_sized self → State.decoders_sized r) ⦄ := by""")

text = unit_edit(text, "State.clone_no_panic decoder clone",
    "all_goals (try (obtain ⟨r, hr⟩ := hdec ‹_›; simp only [hr]))",
    "all_goals (try (obtain ⟨r, hr⟩ := hdec ‹_›; simp only [hr]; "
    "have hrn := Tacenta.SessionUnitDecoderBound.clone_keeps_needed _ _ hr))")

text = unit_edit(text, "State.clone_no_panic redundant step",
    """       all_goals (try (step with vecU8_clone_no_panic))
       all_goals (try step*)
       all_goals (try (step with vecU8_clone_no_panic))""",
    """       all_goals (try (step with vecU8_clone_no_panic))
       all_goals (try (step with vecU8_clone_no_panic))""")

text = unit_edit(text, "State.clone_no_panic closer",
    "all_goals (try (simp_all [State.epoch_val, State.ct1_bounded])))",
    "all_goals (try (simp_all [State.epoch_val, State.ct1_bounded, State.decoders_bounded, State.decoders_sized])))")

for name, count in [("ct1_dec1", 1), ("ct2_dec1", 1), ("hdr_dec1", 1), ("ek_dec1", 2)]:
    text = unit_edit(text, f"step_receive_no_panic message call on {name}",
        f"hdmsg {name}; simp only [ho]",
        f"hdmsg {name} (Tacenta.SessionUnitDecoderBound.size_le_after_add_chunk hr hds) "
        f"(Tacenta.SessionUnitDecoderBound.needed_le_after_add_chunk hr hdb); "
        f"simp only [ho]", count)

text = unit_edit(text, "step_receive_no_panic signature",
    """    (self : Braid) (state : State) (msg : Msg) (hct1b : State.ct1_bounded state) :
    Braid.step_receive self state msg ⦃ fun _ => True ⦄ := by""",
    """    (self : Braid) (state : State) (msg : Msg) (hct1b : State.ct1_bounded state)
    (hdb : State.decoders_bounded state) (hds : State.decoders_sized state) :
    Braid.step_receive self state msg ⦃ fun _ => True ⦄ := by""")

text = unit_edit(text, "receive_no_panic signature",
    """    (self : Braid) (msg : Msg) (hct1b : State.ct1_bounded self.state) :
    Braid.receive self msg ⦃ fun _ => True ⦄ := by""",
    """    (self : Braid) (msg : Msg) (hct1b : State.ct1_bounded self.state)
    (hdb : State.decoders_bounded self.state) (hds : State.decoders_sized self.state) :
    Braid.receive self msg ⦃ fun _ => True ⦄ := by""")

text = unit_edit(text, "receive_no_panic step_receive call",
    "hencaps2 hz hzz hrf self ‹_› msg (by simp_all)))",
    "hencaps2 hz hzz hrf self ‹_› msg (by simp_all) (by simp_all) (by simp_all)))")

text = unit_edit(text, "what this covers: second premise",
    """single function); `BraidPreserve.lean` proves it for `State.sized`. The epoch
bound""",
    """single function); `BraidPreserve.lean` proves it for `State.sized`. In the complete
unit there is a second one,
`State.decoders_bounded`: the erasure decoder is a translated definition there, and
`DecoderMessageTotal` is stated only for a decoder that needs at most `MAX_CODEWORDS` chunks.
The translated `Decoder::message` fails for a decoder that needs and holds `(Usize.max + 1) / 32`
chunks (`SessionBraidReceiveRepair.old_witness`), and `MAX_CODEWORDS` is
the Braid's own bound far below that line (`SessionBraidReceiveRepair.boundary_exact`).
`Braid::invariant` supplies it (`SessionUnitBraidImportInv`), `add_chunk` and `clone` keep it,
and `State.sized`, which gives it together with `ct1_bounded`, is kept by every successful
send and receive (`SessionUnitBraidPreserve.lean`, under the two laws
`SessionUnitBraidPreserveDecoder` states). The epoch
bound""")

# The erasure operations are concrete inside the complete unit, so the Braid
# entry points no longer depend on the standalone translation's opaque erasure
# declarations. The generated unit exposes two concrete library operations in
# their place. Keep the kernel's exact audit output pinned.
for name, remove, add in [
    ("send_no_panic", [
        "tacenta_session_unit.tacenta_erasure.Decoder",
        "tacenta_session_unit.tacenta_erasure.Encoder",
        "tacenta_session_unit.tacenta_erasure.Encoder.new",
        "tacenta_session_unit.tacenta_erasure.Encoder.next_chunk",
        "tacenta_session_unit.tacenta_erasure.Decoder.Insts.CoreCloneClone.clone",
        "tacenta_session_unit.tacenta_erasure.Encoder.Insts.CoreCloneClone.clone",
    ], ["tacenta_session_unit.core.num.Usize.div_ceil"]),
    ("receive_no_panic", [
        "tacenta_session_unit.tacenta_erasure.Decoder",
        "tacenta_session_unit.tacenta_erasure.Encoder",
        "tacenta_session_unit.tacenta_erasure.Decoder.add_chunk",
        "tacenta_session_unit.tacenta_erasure.Decoder.message",
        "tacenta_session_unit.tacenta_erasure.Decoder.new",
        "tacenta_session_unit.tacenta_erasure.Encoder.new",
        "tacenta_session_unit.tacenta_erasure.Decoder.Insts.CoreCloneClone.clone",
        "tacenta_session_unit.tacenta_erasure.Encoder.Insts.CoreCloneClone.clone",
    ], [
        "tacenta_session_unit.alloc.vec.Vec.truncate",
        "tacenta_session_unit.core.num.Usize.div_ceil",
    ]),
]:
    marker = f"info: 'Tacenta.SessionUnitBraidT1.Braid.{name}' depends on axioms: ["
    start = text.index(marker)
    end = text.index("]\n-/", start)
    block = text[start:end + 1]
    lines = block.splitlines()
    for item in remove:
        target = f" {item},"
        target_last = f" {item}]"
        matches = [i for i, line in enumerate(lines) if line in (target, target_last)]
        if len(matches) != 1:
            raise SystemExit(f"port-session-braid-proof: audit item {item!r} changed")
        lines.pop(matches[0])
    insert_at = next(i for i, line in enumerate(lines)
                     if "zeroize.Zeroize.Blanket.zeroize" in line)
    for item in reversed(add):
        lines.insert(insert_at, f" {item},")
    new_block = "\n".join(lines)
    text = text[:start] + new_block + text[end + 1:]

note = (
    "-- Generated by tacenta-proofs/scripts/port-session-braid-proof.sh from\n"
    "-- Translation/BraidT1.lean. Do not edit: `port-session-braid-proof.sh --check`\n"
    "-- regenerates this file and fails on any difference. This count-checked\n"
    "-- port changes namespaces, pins aggregate tactic rules, audits the\n"
    "-- complete unit's concrete erasure dependencies and applies the named\n"
    "-- `unit_edit`s that restate `DecoderMessageTotal` for decoders with\n"
    "-- `needed <= 65536` and add the hypothesis `hdb` (`State.decoders_bounded`)\n"
    "-- to the receive theorems. The standalone file keeps its statements.\n\n"
)
dest.write_text(note + text)
PY

if [ "$check" -eq 0 ]; then
  mv "$tmp" "$dest"
  echo "port-session-braid-proof: wrote SessionUnitBraidT1.lean"
  exit 0
fi

if ! diff -u "$dest" "$tmp" >/dev/null; then
  diff -u "$dest" "$tmp" | head -40 >&2 || true
  echo "port-session-braid-proof: committed copy differs; regenerate and rebuild" >&2
  exit 1
fi
echo "port-session-braid-proof: the committed copy is deterministic"
