import Translation.SessionUnitT3
import Translation.SessionUnitSpqrT3
import Translation.SessionUnitTripleT3
import Translation.SessionUnitBraidT3
import Translation.SessionUnitRatchetImportInv
import Translation.SessionUnitBraidImportInv
import Translation.UnitLifecyclePublicT1
import Translation.NumericBoundary

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
this package adds, so `NumericWitnessSession.lean` applies each ratchet, Braid and Triple theorem at a concrete
state (the `*_at_witness` theorems), where its premises, the invariant among them, are met together. The three
lifecycle theorems at the end have no such application: their premise `Session::invariant self = ok true` needs a
value of the session type, whose fields are opaque boundary types.
-/

namespace Tacenta.SessionUnitDecodedStateDischarge
open Aeneas Aeneas.Std
open tacenta_session_unit

/-- With `epoch + 1 < u64::MAX`, the decoder invariant keeps every chain epoch and every
skipped-key epoch at most `u64::MAX - EPOCHS_KEPT`. -/
theorem session_unit_spqr_epoch_family {s : tacenta_spqr.State} (hinv : SessionUnitRatchetImportInv.Spqr.Inv s)
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

/-- `SessionUnitSpqrT3.receive_refines`: `hroom`, `hcb`, `hsb`, `hskiproom` and `hone` follow from `Inv`,
`hrel` and `hepoch`. -/
theorem session_unit_spqr_receive_premises {s : tacenta_spqr.State} {m : Model.SparseRatchet.State}
    (receiving_epoch n : U64) (hrel : SessionUnitSpqrT3.StateRefines s m)
    (hepoch : s.epoch.val + 1 < U64.max) (hinv : SessionUnitRatchetImportInv.Spqr.Inv s) :
    s.chains.val.length + 2 < Usize.max ∧
    (∀ p ∈ s.chains.val, p.1.val + Model.SparseRatchet.epochsKept ≤ U64.max) ∧
    (∀ sk ∈ s.skipped.val, sk.epoch.val + Model.SparseRatchet.epochsKept ≤ U64.max) ∧
    s.skipped.val.length + tacenta_spqr.MAX_SKIP.val ≤ Usize.max ∧
    (m.skipped.filter (fun x => x.1 == receiving_epoch.val && x.2.1 == n.val)).length ≤ 1 :=
  ⟨SessionUnitRatchetImportInv.Spqr.inv_gives_chain_room s hinv, (session_unit_spqr_epoch_family hinv hepoch).1,
    (session_unit_spqr_epoch_family hinv hepoch).2, SessionUnitRatchetImportInv.Spqr.inv_gives_skip_room s hinv,
    SessionUnitRatchetImportInv.Spqr.inv_gives_store_is_map s m hrel hinv receiving_epoch n⟩

/-- `SessionUnitSpqrT3.send_refines`: `hroom`, `hcb` and `hsb` follow from `Inv` and `hepoch`. -/
theorem session_unit_spqr_send_premises {s : tacenta_spqr.State}
    (hepoch : s.epoch.val + 1 < U64.max) (hinv : SessionUnitRatchetImportInv.Spqr.Inv s) :
    s.chains.val.length + 1 < Usize.max ∧
    (∀ p ∈ s.chains.val, p.1.val + Model.SparseRatchet.epochsKept ≤ U64.max) ∧
    (∀ sk ∈ s.skipped.val, sk.epoch.val + Model.SparseRatchet.epochsKept ≤ U64.max) :=
  ⟨by have := SessionUnitRatchetImportInv.Spqr.inv_gives_chains_len s hinv; scalar_tac,
    (session_unit_spqr_epoch_family hinv hepoch).1, (session_unit_spqr_epoch_family hinv hepoch).2⟩

/-- `SessionUnitSpqrT3.advance_refines`: the same three premises as `send_refines`. -/
theorem session_unit_spqr_advance_premises {s : tacenta_spqr.State}
    (hepoch : s.epoch.val + 1 < U64.max) (hinv : SessionUnitRatchetImportInv.Spqr.Inv s) :
    s.chains.val.length + 1 < Usize.max ∧
    (∀ p ∈ s.chains.val, p.1.val + Model.SparseRatchet.epochsKept ≤ U64.max) ∧
    (∀ sk ∈ s.skipped.val, sk.epoch.val + Model.SparseRatchet.epochsKept ≤ U64.max) :=
  session_unit_spqr_send_premises hepoch hinv

/-- `SessionUnitSpqrT3.maybe_advance_refines`: the same three premises as `send_refines`. -/
theorem session_unit_spqr_maybe_advance_premises {s : tacenta_spqr.State}
    (hepoch : s.epoch.val + 1 < U64.max) (hinv : SessionUnitRatchetImportInv.Spqr.Inv s) :
    s.chains.val.length + 1 < Usize.max ∧
    (∀ p ∈ s.chains.val, p.1.val + Model.SparseRatchet.epochsKept ≤ U64.max) ∧
    (∀ sk ∈ s.skipped.val, sk.epoch.val + Model.SparseRatchet.epochsKept ≤ U64.max) :=
  session_unit_spqr_send_premises hepoch hinv

/-- `SessionUnitSpqrT3.clear_old_epochs_refines`: `hcb` and `hsb` follow from `Inv` and `hepoch`. -/
theorem session_unit_spqr_clear_old_epochs_premises {s : tacenta_spqr.State}
    (hepoch : s.epoch.val + 1 < U64.max) (hinv : SessionUnitRatchetImportInv.Spqr.Inv s) :
    (∀ p ∈ s.chains.val, p.1.val + Model.SparseRatchet.epochsKept ≤ U64.max) ∧
    (∀ sk ∈ s.skipped.val, sk.epoch.val + Model.SparseRatchet.epochsKept ≤ U64.max) :=
  session_unit_spqr_epoch_family hinv hepoch

/-- `SessionUnitT3.receive_refines`: `hone` and `hs` follow from `Inv` and `hR`. -/
theorem session_unit_ratchet_receive_premises (s : tacenta_ratchet.State) (m : Model.State.State)
    (mh : Model.State.Header) (hR : SessionUnitT3.StateR s m) (hinv : SessionUnitRatchetImportInv.Ratchet.Inv s) :
    (m.skipped.filter (SessionUnitT3.matchesHeader mh)).length ≤ 1 ∧
    max s.skipped.val.length tacenta_ratchet.MAX_SKIPPED_STORE.val + tacenta_ratchet.MAX_SKIP.val ≤
      Usize.max :=
  ⟨SessionUnitRatchetImportInv.Ratchet.inv_gives_store_is_map s m hR hinv mh,
    SessionUnitRatchetImportInv.Ratchet.inv_gives_store_bound s hinv⟩

/-- `SessionUnitBraidT3.Braid.receive_refines`: `hct1b` and `hdb` follow from `Braid.Inv`. -/
theorem session_unit_braid_receive_premises (self : tacenta_braid.Braid)
    (hinv : SessionUnitBraidImportInv.Braid.Inv self) :
    SessionUnitBraidT1.State.ct1_bounded self.state ∧
      SessionUnitBraidT1.State.decoders_bounded self.state :=
  ⟨hinv.ct1_bounded, hinv.decoders_bounded⟩

/-- `SessionUnitBraidT3.step_receive_refines`: `hct1b` and `hdb` follow from `Braid.Inv`. -/
theorem session_unit_braid_step_receive_premises (state : tacenta_braid.State)
    (hinv : SessionUnitBraidImportInv.Braid.Inv ⟨state⟩) :
    SessionUnitBraidT1.State.ct1_bounded state ∧ SessionUnitBraidT1.State.decoders_bounded state :=
  ⟨hinv.ct1_bounded, hinv.decoders_bounded⟩

/-! ## The composed Triple theorems

`SessionUnitTripleT3.receive_refines_discharged` and `send_refines_discharged` take the premises of
both inner ratchets, stated about the model state. Given the two inner invariants on the translated
state, `hrel` (the translated state refines the model state) and the two counter ceilings, most of
them follow. -/

/-- `SessionUnitTripleT3.receive_refines_discharged`: `hone`, `hs`, `hroom`, `hcb`, `hsb`,
`hskiproom` and `hone2` follow from the two inner invariants, `hrel` and `hepoch`. `hevents` is a
premise of the target that stays with the caller; it is an argument here so that the table matches
and no conclusion uses it. Four premises stay with the caller: `hevents`, `hepoch` (arguments here),
`hnewb` and `hcounter`; `hheader` relates a header to its model header and is also the caller's. -/
theorem triple_receive_premises {s : tacenta_triple.State} {m : Model.Triple.State}
    (header : tacenta_triple.Header) (mh : Model.State.Header)
    (hrel : SessionUnitTripleT3.StateRefines SessionUnitTripleT3.ratchetAbs
      SessionUnitTripleT3.spqrAbs s m)
    (hevents : m.classical.events + 1 < U32.max)
    (hepoch : m.postQuantum.epoch + 1 < U64.max)
    (hinv : SessionUnitRatchetImportInv.Ratchet.Inv s.classical ∧
      SessionUnitRatchetImportInv.Spqr.Inv s.post_quantum) :
    (m.classical.skipped.filter (fun x => x.1 == mh.dh && x.2.1 == mh.n)).length ≤ 1 ∧
    max m.classical.skipped.length Model.State.maxSkippedStore + Model.State.maxSkip ≤ Usize.max ∧
    m.postQuantum.chains.length + 2 < Usize.max ∧
    (∀ p ∈ m.postQuantum.chains, p.1 + Model.SparseRatchet.epochsKept ≤ U64.max) ∧
    (∀ sk ∈ m.postQuantum.skipped, sk.1 + Model.SparseRatchet.epochsKept ≤ U64.max) ∧
    m.postQuantum.skipped.length + Model.SparseRatchet.maxSkip ≤ Usize.max ∧
    (m.postQuantum.skipped.filter
      (fun x => x.1 == header.epoch.val && x.2.1 == header.pq_n.val)).length ≤ 1 := by
  obtain ⟨hirat, hispqr⟩ := hinv
  obtain ⟨mc, mp⟩ := m
  obtain ⟨h1, h2⟩ := hrel
  dsimp only at h1 h2 hevents hepoch
  subst h1 h2
  have hlenR : (SessionUnitTripleT3.ratchetAbs s.classical).skipped.length
      = s.classical.skipped.val.length := by simp [SessionUnitTripleT3.ratchetAbs]
  have hlenS : (SessionUnitTripleT3.spqrAbs s.post_quantum).skipped.length
      = s.post_quantum.skipped.val.length := by simp [SessionUnitTripleT3.spqrAbs]
  have hlenC : (SessionUnitTripleT3.spqrAbs s.post_quantum).chains.length
      = s.post_quantum.chains.val.length := by simp [SessionUnitTripleT3.spqrAbs]
  have hst := hirat.store_bound
  have hst2 := hispqr.store_bound
  have hc2 := SessionUnitRatchetImportInv.Spqr.inv_gives_chains_len s.post_quantum hispqr
  have hk : (tacenta_ratchet.MAX_SKIPPED_STORE).val = 2000 := by
    simp [tacenta_ratchet.MAX_SKIPPED_STORE]
  have hk2 : (tacenta_spqr.MAX_SKIPPED_STORE).val = 2000 := by
    simp [tacenta_spqr.MAX_SKIPPED_STORE]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact SessionUnitRatchetImportInv.Ratchet.inv_gives_store_is_map s.classical _
      (SessionUnitTripleT3.ratchetAbs_stateR _) hirat mh
  · simp only [Model.State.maxSkippedStore, Model.State.maxSkip]
    rw [hlenR]
    rcases NumericBoundary.both_widths with h | h <;> omega
  · rw [hlenC]
    rcases NumericBoundary.both_widths with h | h <;> omega
  · intro p hp
    simp only [SessionUnitTripleT3.spqrAbs, List.mem_map] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    have := (hispqr.epoch_window q hq).1
    simp only [SessionUnitSpqrT3.chainsEntryOf, Model.SparseRatchet.epochsKept]
    simp only [SessionUnitTripleT3.spqrAbs] at hepoch
    scalar_tac
  · intro sk hsk
    simp only [SessionUnitTripleT3.spqrAbs, List.mem_map] at hsk
    obtain ⟨a, ha, rfl⟩ := hsk
    obtain ⟨q, hq, hqe⟩ := hispqr.skipped_chained a ha
    have h1 := (hispqr.epoch_window q hq).1
    have h2 : (q.1 : U64).val = a.epoch.val := by rw [hqe]
    simp only [SessionUnitSpqrT3.skippedOf, Model.SparseRatchet.epochsKept]
    simp only [SessionUnitTripleT3.spqrAbs] at hepoch
    scalar_tac
  · simp only [Model.SparseRatchet.maxSkip, Model.State.maxSkip]
    rw [hlenS]
    rcases NumericBoundary.both_widths with h | h <;> omega
  · exact SessionUnitRatchetImportInv.Spqr.inv_gives_store_is_map s.post_quantum _
      (SessionUnitTripleT3.spqrAbs_refines _) hispqr header.epoch header.pq_n

/-- `SessionUnitTripleT3.send_refines_discharged`: `hroom`, `hcb` and `hsb` follow from the sparse
invariant, `hrel` and `hepoch`. `hnewb` and `hcounter` stay with the caller. -/
theorem triple_send_premises {s : tacenta_triple.State} {m : Model.Triple.State}
    (hrel : SessionUnitTripleT3.StateRefines SessionUnitTripleT3.ratchetAbs
      SessionUnitTripleT3.spqrAbs s m)
    (hepoch : m.postQuantum.epoch + 1 < U64.max)
    (hispqr : SessionUnitRatchetImportInv.Spqr.Inv s.post_quantum) :
    m.postQuantum.chains.length + 1 < Usize.max ∧
    (∀ p ∈ m.postQuantum.chains, p.1 + Model.SparseRatchet.epochsKept ≤ U64.max) ∧
    (∀ sk ∈ m.postQuantum.skipped, sk.1 + Model.SparseRatchet.epochsKept ≤ U64.max) := by
  obtain ⟨mc, mp⟩ := m
  obtain ⟨h1, h2⟩ := hrel
  dsimp only at h1 h2 hepoch
  subst h1 h2
  have hlenC : (SessionUnitTripleT3.spqrAbs s.post_quantum).chains.length
      = s.post_quantum.chains.val.length := by simp [SessionUnitTripleT3.spqrAbs]
  have hc2 := SessionUnitRatchetImportInv.Spqr.inv_gives_chains_len s.post_quantum hispqr
  refine ⟨?_, ?_, ?_⟩
  · rw [hlenC]
    rcases NumericBoundary.both_widths with h | h <;> omega
  · intro p hp
    simp only [SessionUnitTripleT3.spqrAbs, List.mem_map] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    have := (hispqr.epoch_window q hq).1
    simp only [SessionUnitSpqrT3.chainsEntryOf, Model.SparseRatchet.epochsKept]
    simp only [SessionUnitTripleT3.spqrAbs] at hepoch
    scalar_tac
  · intro sk hsk
    simp only [SessionUnitTripleT3.spqrAbs, List.mem_map] at hsk
    obtain ⟨a, ha, rfl⟩ := hsk
    obtain ⟨q, hq, hqe⟩ := hispqr.skipped_chained a ha
    have h1 := (hispqr.epoch_window q hq).1
    have h2 : (q.1 : U64).val = a.epoch.val := by rw [hqe]
    simp only [SessionUnitSpqrT3.skippedOf, Model.SparseRatchet.epochsKept]
    simp only [SessionUnitTripleT3.spqrAbs] at hepoch
    scalar_tac

/-! ## A session that passes its invariant meets the decrypt headroom

`UnitLifecycleT1.invariant_gives_preconditions` derives `InvariantPreconditions` from
`Session::invariant`, but the lifecycle theorems `decrypt_ratchet_no_panic` and `decrypt_no_panic`
take `DecryptRatchetHeadroom`, which is that record plus the associated-data bound. Nothing
connected the two. The bridge below does, and the two theorems after it apply the claimed T1
theorems with it, so that the invariant-to-headroom path ends at a claimed theorem. The one
bound that stays with the caller, `identity_ad.length + 106 ≤ usize::MAX`, is an argument.

These are conditional on the contract records (`DecryptRatchetContracts`) exactly as the theorems
they apply are; whether the records, or the headroom, are met by a real session is the subject of
`LIMITATIONS.md` and `GAP-REGISTER.md`, row `SESSION-CONTRACT-VACUITY`, not of this module. -/

/-- A session that passes `Session::invariant` meets `DecryptRatchetHeadroom` once the associated
data bound holds. -/
theorem decrypt_headroom_of_invariant
    (hct1 : SessionUnitBraidT1.Ct1LenTotal) (self : lifecycle.Session)
    (hdecoderSize : SessionUnitBraidT1.State.decoders_sized self.braid.state)
    (hinv : lifecycle.Session.invariant self = Result.ok true)
    (had : self.identity_ad.val.length + 106 ≤ Usize.max) :
    UnitLifecycleT1.DecryptRatchetHeadroom self := by
  obtain ⟨h1, h2, h3⟩ := UnitLifecycleT1.invariant_gives_preconditions hct1 self hinv
  exact ⟨h1, h2, h3, hdecoderSize, had⟩

/-- `UnitLifecycleT1.decrypt_ratchet_no_panic` for a session that passes `Session::invariant`. -/
theorem decrypt_ratchet_no_panic_of_invariant {R : Type}
    (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R)
    (boundary : UnitLifecycleT1.DecryptRatchetContracts rc)
    [SessionUnitT1.DerivedKeysModel]
    (self : lifecycle.Session) (message : Slice U8) (rng : R)
    (hdecoderSize : SessionUnitBraidT1.State.decoders_sized self.braid.state)
    (hinv : lifecycle.Session.invariant self = Result.ok true)
    (had : self.identity_ad.val.length + 106 ≤ Usize.max) :
    lifecycle.Session.decrypt_ratchet rc crc self message rng ⦃ fun _ => True ⦄ :=
  UnitLifecycleT1.decrypt_ratchet_no_panic rc crc boundary self message rng
    (decrypt_headroom_of_invariant boundary.braid.ct1Len self hdecoderSize hinv had)

/-- `UnitLifecycleT1.decrypt_no_panic` for a session that passes `Session::invariant`. -/
theorem decrypt_no_panic_of_invariant {R : Type}
    (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R)
    (boundary : UnitLifecycleT1.DecryptRatchetContracts rc)
    [SessionUnitT1.DerivedKeysModel]
    (self : lifecycle.Session) (message : Slice U8) (rng : R)
    (hdecoderSize : SessionUnitBraidT1.State.decoders_sized self.braid.state)
    (hinv : lifecycle.Session.invariant self = Result.ok true)
    (had : self.identity_ad.val.length + 106 ≤ Usize.max) :
    lifecycle.Session.decrypt rc crc self message rng ⦃ fun _ => True ⦄ :=
  UnitLifecycleT1.decrypt_no_panic rc crc boundary self message rng
    (decrypt_headroom_of_invariant boundary.braid.ct1Len self hdecoderSize hinv had)

end Tacenta.SessionUnitDecodedStateDischarge

/--
info: 'Tacenta.SessionUnitDecodedStateDischarge.session_unit_spqr_epoch_family' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.SessionUnitDecodedStateDischarge.session_unit_spqr_epoch_family

/--
info: 'Tacenta.SessionUnitDecodedStateDischarge.session_unit_spqr_receive_premises' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.SessionUnitDecodedStateDischarge.session_unit_spqr_receive_premises

/--
info: 'Tacenta.SessionUnitDecodedStateDischarge.session_unit_spqr_send_premises' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.SessionUnitDecodedStateDischarge.session_unit_spqr_send_premises

/--
info: 'Tacenta.SessionUnitDecodedStateDischarge.session_unit_spqr_advance_premises' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.SessionUnitDecodedStateDischarge.session_unit_spqr_advance_premises

/--
info: 'Tacenta.SessionUnitDecodedStateDischarge.session_unit_spqr_maybe_advance_premises' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.SessionUnitDecodedStateDischarge.session_unit_spqr_maybe_advance_premises

/--
info: 'Tacenta.SessionUnitDecodedStateDischarge.session_unit_spqr_clear_old_epochs_premises' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.SessionUnitDecodedStateDischarge.session_unit_spqr_clear_old_epochs_premises

/--
info: 'Tacenta.SessionUnitDecodedStateDischarge.session_unit_ratchet_receive_premises' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.SessionUnitDecodedStateDischarge.session_unit_ratchet_receive_premises

/--
info: 'Tacenta.SessionUnitDecodedStateDischarge.session_unit_braid_receive_premises' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair]
-/
#guard_msgs in
#print axioms Tacenta.SessionUnitDecodedStateDischarge.session_unit_braid_receive_premises

/--
info: 'Tacenta.SessionUnitDecodedStateDischarge.session_unit_braid_step_receive_premises' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair]
-/
#guard_msgs in
#print axioms Tacenta.SessionUnitDecodedStateDischarge.session_unit_braid_step_receive_premises

/--
info: 'Tacenta.SessionUnitDecodedStateDischarge.triple_receive_premises' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.SessionUnitDecodedStateDischarge.triple_receive_premises

/--
info: 'Tacenta.SessionUnitDecodedStateDischarge.triple_send_premises' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.SessionUnitDecodedStateDischarge.triple_send_premises

/--
info: 'Tacenta.SessionUnitDecodedStateDischarge.decrypt_headroom_of_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kem.CT1_LEN,
 tacenta_session_unit.tacenta_kem.CT2_LEN,
 tacenta_session_unit.tacenta_kem.EK_VECTOR_LEN,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.HEADER_LEN,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.tacenta_kem.validate_ek,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.dh.is_prime_order_public,
 tacenta_session_unit.tacenta_boundary.kem.ciphertext_len,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.header,
 tacenta_session_unit.core.num.Usize.div_ceil,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 tacenta_session_unit.core.option.Option.Insts.CoreCmpPartialEqOption.eq]
-/
#guard_msgs in
#print axioms Tacenta.SessionUnitDecodedStateDischarge.decrypt_headroom_of_invariant

/--
info: 'Tacenta.SessionUnitDecodedStateDischarge.decrypt_ratchet_no_panic_of_invariant' depends on axioms: [propext,
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
 tacenta_session_unit.rand_core_1.error.Error,
 tacenta_session_unit.tacenta_boundary.aead.decrypt,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.dh.is_prime_order_public,
 tacenta_session_unit.tacenta_boundary.kem.ciphertext_len,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.header,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.Pair.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.TupleABC.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.alloc.vec.Vec.capacity,
 tacenta_session_unit.alloc.vec.Vec.pop,
 tacenta_session_unit.alloc.vec.Vec.truncate,
 tacenta_session_unit.core.num.Usize.div_ceil,
 tacenta_session_unit.core.option.Option.as_mut,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.agree,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.to_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 tacenta_session_unit.tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 tacenta_session_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.core.option.Option.Insts.CoreCloneClone.clone,
 tacenta_session_unit.core.option.Option.Insts.CoreCmpPartialEqOption.eq,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.SessionUnitDecodedStateDischarge.decrypt_ratchet_no_panic_of_invariant

/--
info: 'Tacenta.SessionUnitDecodedStateDischarge.decrypt_no_panic_of_invariant' depends on axioms: [propext,
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
 tacenta_session_unit.rand_core_1.error.Error,
 tacenta_session_unit.tacenta_boundary.aead.decrypt,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.dh.is_prime_order_public,
 tacenta_session_unit.tacenta_boundary.kem.ciphertext_len,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.header,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.Pair.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.TupleABC.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.alloc.vec.Vec.capacity,
 tacenta_session_unit.alloc.vec.Vec.pop,
 tacenta_session_unit.alloc.vec.Vec.truncate,
 tacenta_session_unit.core.num.Usize.div_ceil,
 tacenta_session_unit.core.option.Option.as_mut,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.agree,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.to_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 tacenta_session_unit.tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 tacenta_session_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.core.option.Option.Insts.CoreCloneClone.clone,
 tacenta_session_unit.core.option.Option.Insts.CoreCmpPartialEqOption.eq,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.SessionUnitDecodedStateDischarge.decrypt_no_panic_of_invariant
