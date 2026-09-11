/-
Proofs.TrustedBase: what the model-layer proofs actually rest on, pinned so it
cannot drift.

`LIMITATIONS.md` describes the trusted computing base in prose. Prose goes stale,
and a trusted base that has gone stale is worse than none, because it is a claim
rather than a gap. This file states the same thing in a form the build checks:
`#print axioms` under `#guard_msgs`, so that any proof which starts depending on
something new fails here rather than being noticed by whoever greps for it next.

The T3 zone (`Translation.SessionT3`) does this for itself. This does it for
the model layer.

## What is being trusted, and why it is not obvious

Two tactics in this development discharge goals by *evaluation* rather than by
producing a kernel proof term.

`native_decide` compiles the proposition and runs it. Everyone expects this one
to widen the trust base, and it is used deliberately and rarely.

`bv_decide` is the surprise. It looks like an ordinary decision procedure for
bitvectors, and it settles goals over 2^32 values that no kernel reduction could
reach. It does that by bitblasting to SAT, and the reflection step it uses to get
there is *also* native evaluation: every axiom it introduces is named
`._native.bv_decide.ax_*`. So a proof by `bv_decide` trusts the Lean compiler in
the same way a proof by `native_decide` does.

That matters here more than anywhere else, because `bv_decide` is what makes the
GF(2^16) field proofs possible at all. `Model.Gf65536.mul_assoc` alone rests on
about forty such axioms. The field is proved, and it is proved by evaluation.

Stating that is not a hedge. It is the difference between "machine-checked" and
"machine-checked by the kernel alone", and it belongs written down.

## A caveat about the pins themselves

The evaluated axioms carry generated names with an index, and the index is not
stable: adding a lemma earlier in a file renumbers the ones after it, and this
file then fails with a diff that looks alarming and means nothing.

It is the safe direction to fail in. A pin that renumbers breaks the build
loudly; a pin that silently accepted a *new* axiom would be worthless. When
updating one of these, check that the axiom *set* is the same and only the
indices moved, which the diff makes obvious.
-/
import Model.Polynomial
import Model.Braid
import Model.SparseRatchet
import Model.TripleRatchet
import Proofs.RatchetCorrectness
import Proofs.Serialization
import Properties.Authentication
import Properties.ForwardSecrecy
import Properties.PostCompromise
import Properties.Secrecy
import Properties.StateConsistency
import Proofs.KeyErasure
import Proofs.MemorySafety
import Proofs.SparseRatchetCorrectness

namespace Proofs.TrustedBase

/-! ## Kernel only

These rest on nothing but `propext` and `Quot.sound`, which are the axioms Lean's
own standard library uses. Nothing is evaluated to reach them.

The Braid's epoch accounting is the one worth having on this footing: it is the
part of that protocol where both sides must agree exactly, and it is settled by
the kernel. -/

/--
info: 'Model.Braid.send_output_epoch' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Model.Braid.send_output_epoch

/--
info: 'Model.Braid.receive_output_epoch' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Model.Braid.receive_output_epoch

/--
info: 'Model.Braid.send_reports' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Model.Braid.send_reports

/--
info: 'Model.Braid.receive_reports' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Model.Braid.receive_reports

/- The classical Double Ratchet's functional properties: the chain-derivation
   length and contents, and the two bounds on the skipped-key store. `CLAIMS.md`
   says these rest on `propext` and `Quot.sound` alone; these pins are what make
   that a build fact rather than a sentence. -/

/--
info: 'Proofs.RatchetCorrectness.deriveChain_length' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Proofs.RatchetCorrectness.deriveChain_length

/--
info: 'Proofs.RatchetCorrectness.deriveChain_fst' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Proofs.RatchetCorrectness.deriveChain_fst

/--
info: 'Proofs.RatchetCorrectness.deriveChain_get' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Proofs.RatchetCorrectness.deriveChain_get

/--
info: 'Proofs.RatchetCorrectness.skipMessageKeys_growth' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Proofs.RatchetCorrectness.skipMessageKeys_growth

/--
info: 'Proofs.RatchetCorrectness.skipMessageKeys_store_bounded' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Proofs.RatchetCorrectness.skipMessageKeys_store_bounded

/- The four security properties, against the symbolic attacker of
   `Model.Adversary`. `CLAIMS.md` records what each states and the
   assumption behind all of them: that the attacker's rules are the only way
   to derive a key, which no proof here reaches. -/

/--
info: 'Properties.ForwardSecrecy.past_message_keys_are_safe' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Properties.ForwardSecrecy.past_message_keys_are_safe

/--
info: 'Properties.ForwardSecrecy.past_chain_keys_are_safe' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Properties.ForwardSecrecy.past_chain_keys_are_safe

/--
info: 'Properties.ForwardSecrecy.future_message_keys_are_exposed' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Properties.ForwardSecrecy.future_message_keys_are_exposed

/--
info: 'Properties.Secrecy.message_keys_are_independent' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Properties.Secrecy.message_keys_are_independent

/--
info: 'Properties.Secrecy.a_message_key_does_not_expose_its_chain' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Properties.Secrecy.a_message_key_does_not_expose_its_chain

/--
info: 'Properties.PostCompromise.fresh_agreement_heals' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Properties.PostCompromise.fresh_agreement_heals

/--
info: 'Properties.PostCompromise.fresh_agreement_heals_the_root' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Properties.PostCompromise.fresh_agreement_heals_the_root

/--
info: 'Properties.Authentication.ckAt_inj' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Properties.Authentication.ckAt_inj

/--
info: 'Properties.Authentication.mkAt_inj' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Properties.Authentication.mkAt_inj

/--
info: 'Properties.Authentication.no_cross_session_chain' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Properties.Authentication.no_cross_session_chain

/--
info: 'Properties.Authentication.no_cross_session_message' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Properties.Authentication.no_cross_session_message

/- The classical ratchet model's transitions: what each moves and what it
   leaves alone. `ageStore_preserves_the_rest` is proved by `rfl` and rests on
   no axiom, so `#print axioms` prints no list for it and it has no pin here. -/

/--
info: 'Properties.StateConsistency.send_none_iff' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Properties.StateConsistency.send_none_iff

/--
info: 'Properties.StateConsistency.send_advances_ns' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Properties.StateConsistency.send_advances_ns

/--
info: 'Properties.StateConsistency.send_header_is_pre_state' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Properties.StateConsistency.send_header_is_pre_state

/--
info: 'Properties.StateConsistency.send_preserves_the_rest' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Properties.StateConsistency.send_preserves_the_rest

/--
info: 'Properties.StateConsistency.dhRatchet_resets_counters' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Properties.StateConsistency.dhRatchet_resets_counters

/--
info: 'Properties.StateConsistency.dhRatchet_takes_header_key' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Properties.StateConsistency.dhRatchet_takes_header_key

/--
info: 'Properties.StateConsistency.skipMessageKeys_nr_monotone' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Properties.StateConsistency.skipMessageKeys_nr_monotone

/--
info: 'Properties.StateConsistency.skipMessageKeys_preserves_sending' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Properties.StateConsistency.skipMessageKeys_preserves_sending

/--
info: 'Properties.StateConsistency.ageStore_counts_one' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Properties.StateConsistency.ageStore_counts_one

/--
info: 'Properties.StateConsistency.ageStore_stays_at_stop' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Properties.StateConsistency.ageStore_stays_at_stop

/--
info: 'Properties.StateConsistency.trySkipped_preserves_counters' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Properties.StateConsistency.trySkipped_preserves_counters

/- The skipped-key stores in the model: what leaves the classical store, how
   far it grows over any sequence of steps, and what the sparse ratchet's
   skipped batches contain and how far one skip grows its store. -/

/--
info: 'Proofs.KeyErasure.trySkipped_removes_the_entry' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Proofs.KeyErasure.trySkipped_removes_the_entry

/--
info: 'Proofs.KeyErasure.trySkipped_is_once' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Proofs.KeyErasure.trySkipped_is_once

/--
info: 'Proofs.KeyErasure.ageStore_drops_the_expired' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Proofs.KeyErasure.ageStore_drops_the_expired

/--
info: 'Proofs.KeyErasure.ageStore_only_removes' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Proofs.KeyErasure.ageStore_only_removes

/--
info: 'Proofs.MemorySafety.step_preserves_bound' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Proofs.MemorySafety.step_preserves_bound

/--
info: 'Proofs.MemorySafety.reachable_stays_bounded' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Proofs.MemorySafety.reachable_stays_bounded

/--
info: 'Proofs.MemorySafety.a_session_stays_bounded' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Proofs.MemorySafety.a_session_stays_bounded

/--
info: 'Proofs.SparseRatchetCorrectness.deriveInto_length' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Proofs.SparseRatchetCorrectness.deriveInto_length

/--
info: 'Proofs.SparseRatchetCorrectness.deriveInto_num_gt' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Proofs.SparseRatchetCorrectness.deriveInto_num_gt

/--
info: 'Proofs.SparseRatchetCorrectness.deriveInto_num_le' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Proofs.SparseRatchetCorrectness.deriveInto_num_le

/--
info: 'Proofs.SparseRatchetCorrectness.deriveInto_nodup' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Proofs.SparseRatchetCorrectness.deriveInto_nodup

/--
info: 'Proofs.SparseRatchetCorrectness.deriveInto_get' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Proofs.SparseRatchetCorrectness.deriveInto_get

/--
info: 'Proofs.SparseRatchetCorrectness.skipMessageKeys_store_bounded' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Proofs.SparseRatchetCorrectness.skipMessageKeys_store_bounded

/--
info: 'Proofs.SparseRatchetCorrectness.clearOldEpochs_store_le' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Proofs.SparseRatchetCorrectness.clearOldEpochs_store_le

/--
info: 'Proofs.SparseRatchetCorrectness.trySkipped_store_lt' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Proofs.SparseRatchetCorrectness.trySkipped_store_lt

/--
info: 'Proofs.SparseRatchetCorrectness.skipMessageKeys_preserves_map' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Proofs.SparseRatchetCorrectness.skipMessageKeys_preserves_map

/- The Triple Ratchet's separation is not a proof obligation, and it is worth
   recording why rather than leaving the absence unexplained.

   A composition that concatenated both message keys into one derivation
   input would owe a theorem: both are exactly thirty-two bytes, therefore no
   two distinct pairs present the same bytes. Following §7.2's recommended
   parameters, `combine` instead puts the two keys in **different** arguments
   -- the post-quantum key as salt, the classical one as input keying material
   -- so distinct pairs are distinct inputs by construction. The obligation is
   discharged by the shape of the derivation instead of by the kernel.

   What sits at the trusted boundary: that `combine` cannot be inverted from a
   single input is a property of HKDF, not of anything proved here. -/

/-! ## Trusted by evaluation

Everything below is true, and everything below is true because a compiled program
said so. -/

/- Every nonzero element of the field inverts.

   Exhaustive over 65,535 elements, each requiring an exponentiation. There is no
   route to this through the kernel: `decide` cannot reduce it and `bv_decide`
   cannot model the exponentiation. So it is `native_decide`, and it is
   load-bearing rather than decorative, because interpolation divides by the
   difference of two distinct nodes and this is what makes that a division. -/
/--
info: 'Model.Gf65536.mul_inv_cancel' depends on axioms: [propext,
 Quot.sound,
 Model.Gf65536.mul_inv_cancel._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms Model.Gf65536.mul_inv_cancel

/- The delta property: interpolation reproduces the points it was given.

   The erasure code's correctness argument runs through this, and the list below
   is the whole of what it trusts. Five evaluated axioms: one `native_decide` for
   invertibility above, and four `bv_decide` reflections for the field identities
   the proof uses directly. -/
/--
info: 'Model.Polynomial.interp_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Model.Gf65536.clmul_comm._native.bv_decide.ax_1_6,
 Model.Gf65536.mul_inv_cancel._native.native_decide.ax_1_1,
 Model.Gf65536.mul_one._native.bv_decide.ax_1_9,
 Model.Polynomial.combine_at._native.bv_decide.ax_1_10,
 Model.Polynomial.combine_at._native.bv_decide.ax_1_5]
-/
#guard_msgs in
#print axioms Model.Polynomial.interp_eq

/- The composite header parses unambiguously.

   The Triple Ratchet's one obligation on its encoding, discharged. It is on the
   evaluated side rather than the kernel, and the reason is the three counter
   round-trips it rests on: a big-endian byte encoding is a bitvector identity,
   `bv_decide` is what settles those, and `bv_decide` reflects. Nothing else in
   the proof needs it. -/
/--
info: 'Proofs.Serialization.decode_encode_composite' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Model.CompositeHeader.readBe16_be16._native.bv_decide.ax_1_9,
 Model.CompositeHeader.readBe64_be64._native.bv_decide.ax_1_9,
 Serialization.readBe32_be32._native.bv_decide.ax_1_9]
-/
#guard_msgs in
#print axioms Proofs.Serialization.decode_encode_composite

end Proofs.TrustedBase
