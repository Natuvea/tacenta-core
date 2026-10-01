import Translation.T3
import Translation.SpqrT3
import Translation.BraidT3
import Translation.ImportInv

/-!
# Which numeric premises of the refinement theorems a decoded state gives

`ImportInv.lean` proves that a state `State::from_bytes` returns satisfies the crate's `invariant`
(`Inv`), and derives from it some of the numeric premises of the refinement theorems. This module
finishes that accounting for the sparse ratchet, the classical ratchet and the Braid. For each
theorem `T` named below, a discharge theorem states that the premises it names follow from `Inv`
together with the premises it takes as arguments. Its conclusion is the conjunction of those
premises of `T`, written as `T` writes them, and `tacenta-proofs/scripts/check-precondition-witnesses.sh`
compares it with `T`'s own signature, so a premise added to `T` or changed in `T` fails that check
until this module is changed to match.

The result that was not in the tree is for the sparse ratchet. `SpqrT3.receive_refines` takes five
premises about epochs that the earlier accounting called open: `hepoch`, `hcb`, `hsb`, `hnewb` and
`hcounter`. `hcb` and `hsb` (every chain epoch and every skipped-key epoch, plus `EPOCHS_KEPT`,
stays at or below `u64::MAX`) follow from `Inv` and `hepoch` (`epoch + 1 < u64::MAX`):
`Inv` puts every chain epoch at or below the current epoch, and every skipped key names a present
chain. What stays with the caller, as premises not discharged here, is `hepoch`,
`hnewb` (the epochs of the keys an operation adds) and `hcounter` (every chain's counter is below
`u64::MAX`). The same holds for `send_refines`, `advance_refines` and `maybe_advance_refines`
(`hroom`, `hcb`, `hsb` follow from `Inv` and `hepoch`) and for `clear_old_epochs_refines`
(`hcb`, `hsb` follow from `Inv` and `hepoch`).

Nothing here says `hepoch` holds of every state a decoder returns. It does not: the state at
`epoch = u64::MAX - 1` passes `invariant`, is one the crate's own operations produce, and fails it.
So `hepoch` is the caller's premise, and this module shows what it is needed for.

For the classical ratchet `T3.receive_refines` takes `hone`, `hs` and `hroom`. `hone` and `hs`
follow from `Inv` (`hroom`, `events + 1 < u32::MAX`, does not: the parked clock passes `invariant`).
For the Braid, `ct1_bounded` follows from `Braid.Inv`; the `epoch + 1 < u64::MAX` premise of
`receive_refines` and `step_receive_refines` does not.

Every result is conditional on the premises it takes and on `Inv`; none says a decoded state refines
the model. A discharge theorem whose own premises no state meets would be true and empty, and `Inv` is a premise
this package adds, so `NumericWitnessLeaf.lean` applies each theorem at a concrete state (the `*_at_witness`
theorems), where its premises, the invariant among them, are met together.
-/

namespace Tacenta.DecodedStateDischarge
open Aeneas Aeneas.Std

/-- With `epoch + 1 < u64::MAX`, the decoder invariant keeps every chain epoch and every
skipped-key epoch at most `u64::MAX - EPOCHS_KEPT`. -/
theorem spqr_epoch_family {s : tacenta_spqr.State} (hinv : ImportInv.Spqr.Inv s)
    (hepoch : s.epoch.val + 1 < U64.max) :
    (∀ p ∈ s.chains.val, p.1.val + Model.SparseRatchet.epochsKept ≤ U64.max) ∧
    (∀ sk ∈ s.skipped.val, sk.epoch.val + Model.SparseRatchet.epochsKept ≤ U64.max) := by
  constructor
  · intro p hp
    have h1 := (hinv.epoch_window p hp).1
    simp only [Model.SparseRatchet.epochsKept]
    scalar_tac
  · intro sk hsk
    obtain ⟨q, hq, hqe⟩ := hinv.skipped_chained sk hsk
    have h1 := (hinv.epoch_window q hq).1
    have h2 : (q.1 : U64).val = sk.epoch.val := by rw [hqe]
    simp only [Model.SparseRatchet.epochsKept]
    scalar_tac

/-- `SpqrT3.receive_refines`: `hroom`, `hcb`, `hsb`, `hskiproom` and `hone` follow from `Inv`,
`hrel` and `hepoch`. -/
theorem spqr_receive_premises {s : tacenta_spqr.State} {m : Model.SparseRatchet.State}
    (receiving_epoch n : U64) (hrel : SpqrT3.StateRefines s m)
    (hepoch : s.epoch.val + 1 < U64.max) (hinv : ImportInv.Spqr.Inv s) :
    s.chains.val.length + 2 < Usize.max ∧
    (∀ p ∈ s.chains.val, p.1.val + Model.SparseRatchet.epochsKept ≤ U64.max) ∧
    (∀ sk ∈ s.skipped.val, sk.epoch.val + Model.SparseRatchet.epochsKept ≤ U64.max) ∧
    s.skipped.val.length + tacenta_spqr.MAX_SKIP.val ≤ Usize.max ∧
    (m.skipped.filter (fun x => x.1 == receiving_epoch.val && x.2.1 == n.val)).length ≤ 1 :=
  ⟨ImportInv.Spqr.inv_gives_chain_room s hinv, (spqr_epoch_family hinv hepoch).1,
    (spqr_epoch_family hinv hepoch).2, ImportInv.Spqr.inv_gives_skip_room s hinv,
    ImportInv.Spqr.inv_gives_store_is_map s m hrel hinv receiving_epoch n⟩

/-- `SpqrT3.send_refines`: `hroom`, `hcb` and `hsb` follow from `Inv` and `hepoch`. -/
theorem spqr_send_premises {s : tacenta_spqr.State}
    (hepoch : s.epoch.val + 1 < U64.max) (hinv : ImportInv.Spqr.Inv s) :
    s.chains.val.length + 1 < Usize.max ∧
    (∀ p ∈ s.chains.val, p.1.val + Model.SparseRatchet.epochsKept ≤ U64.max) ∧
    (∀ sk ∈ s.skipped.val, sk.epoch.val + Model.SparseRatchet.epochsKept ≤ U64.max) :=
  ⟨by have := ImportInv.Spqr.inv_gives_chains_len s hinv; scalar_tac,
    (spqr_epoch_family hinv hepoch).1, (spqr_epoch_family hinv hepoch).2⟩

/-- `SpqrT3.advance_refines`: the same three premises as `send_refines`. -/
theorem spqr_advance_premises {s : tacenta_spqr.State}
    (hepoch : s.epoch.val + 1 < U64.max) (hinv : ImportInv.Spqr.Inv s) :
    s.chains.val.length + 1 < Usize.max ∧
    (∀ p ∈ s.chains.val, p.1.val + Model.SparseRatchet.epochsKept ≤ U64.max) ∧
    (∀ sk ∈ s.skipped.val, sk.epoch.val + Model.SparseRatchet.epochsKept ≤ U64.max) :=
  spqr_send_premises hepoch hinv

/-- `SpqrT3.maybe_advance_refines`: the same three premises as `send_refines`. -/
theorem spqr_maybe_advance_premises {s : tacenta_spqr.State}
    (hepoch : s.epoch.val + 1 < U64.max) (hinv : ImportInv.Spqr.Inv s) :
    s.chains.val.length + 1 < Usize.max ∧
    (∀ p ∈ s.chains.val, p.1.val + Model.SparseRatchet.epochsKept ≤ U64.max) ∧
    (∀ sk ∈ s.skipped.val, sk.epoch.val + Model.SparseRatchet.epochsKept ≤ U64.max) :=
  spqr_send_premises hepoch hinv

/-- `SpqrT3.clear_old_epochs_refines`: `hcb` and `hsb` follow from `Inv` and `hepoch`. -/
theorem spqr_clear_old_epochs_premises {s : tacenta_spqr.State}
    (hepoch : s.epoch.val + 1 < U64.max) (hinv : ImportInv.Spqr.Inv s) :
    (∀ p ∈ s.chains.val, p.1.val + Model.SparseRatchet.epochsKept ≤ U64.max) ∧
    (∀ sk ∈ s.skipped.val, sk.epoch.val + Model.SparseRatchet.epochsKept ≤ U64.max) :=
  spqr_epoch_family hinv hepoch

/-- `T3.receive_refines`: `hone` and `hs` follow from `Inv` and `hR`. -/
theorem ratchet_receive_premises (s : tacenta_ratchet.State) (m : Model.State.State)
    (mh : Model.State.Header) (hR : T3.StateR s m) (hinv : ImportInv.Ratchet.Inv s) :
    (m.skipped.filter (T3.matchesHeader mh)).length ≤ 1 ∧
    max s.skipped.val.length tacenta_ratchet.MAX_SKIPPED_STORE.val + tacenta_ratchet.MAX_SKIP.val ≤
      Usize.max :=
  ⟨ImportInv.Ratchet.inv_gives_store_is_map s m hR hinv mh,
    ImportInv.Ratchet.inv_gives_store_bound s hinv⟩

/-- `BraidT3.Braid.receive_refines`: `hct1b` follows from `Braid.Inv`. -/
theorem braid_receive_premises (self : tacenta_braid.Braid)
    (hinv : ImportInv.Braid.Inv self) : BraidT1.State.ct1_bounded self.state :=
  hinv.ct1_bounded

/-- `BraidT3.step_receive_refines`: `hct1b` follows from `Braid.Inv`. -/
theorem braid_step_receive_premises (state : tacenta_braid.State)
    (hinv : ImportInv.Braid.Inv ⟨state⟩) : BraidT1.State.ct1_bounded state :=
  hinv.ct1_bounded

end Tacenta.DecodedStateDischarge

/--
info: 'Tacenta.DecodedStateDischarge.spqr_epoch_family' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.DecodedStateDischarge.spqr_epoch_family

/--
info: 'Tacenta.DecodedStateDischarge.spqr_receive_premises' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.DecodedStateDischarge.spqr_receive_premises

/--
info: 'Tacenta.DecodedStateDischarge.spqr_send_premises' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.DecodedStateDischarge.spqr_send_premises

/--
info: 'Tacenta.DecodedStateDischarge.spqr_advance_premises' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.DecodedStateDischarge.spqr_advance_premises

/--
info: 'Tacenta.DecodedStateDischarge.spqr_maybe_advance_premises' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.DecodedStateDischarge.spqr_maybe_advance_premises

/--
info: 'Tacenta.DecodedStateDischarge.spqr_clear_old_epochs_premises' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.DecodedStateDischarge.spqr_clear_old_epochs_premises

/--
info: 'Tacenta.DecodedStateDischarge.ratchet_receive_premises' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.DecodedStateDischarge.ratchet_receive_premises

/--
info: 'Tacenta.DecodedStateDischarge.braid_receive_premises' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_braid.tacenta_erasure.Decoder,
 tacenta_braid.tacenta_erasure.Encoder,
 tacenta_braid.tacenta_kem.EncapsState,
 tacenta_braid.tacenta_kem.IncrementalKeyPair]
-/
#guard_msgs in
#print axioms Tacenta.DecodedStateDischarge.braid_receive_premises

/--
info: 'Tacenta.DecodedStateDischarge.braid_step_receive_premises' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_braid.tacenta_erasure.Decoder,
 tacenta_braid.tacenta_erasure.Encoder,
 tacenta_braid.tacenta_kem.EncapsState,
 tacenta_braid.tacenta_kem.IncrementalKeyPair]
-/
#guard_msgs in
#print axioms Tacenta.DecodedStateDischarge.braid_step_receive_premises
