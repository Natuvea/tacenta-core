import Translation.ImportInv

/-!
# The premises of `Ratchet.decoded_receive_refines`, together

`Ratchet.decoded_receive_refines` takes the decode (`hdec`), the state relation, the header relation
and `hclock_unparked : events + 1 < U32.max`.  `ImportInv.lean` shows the decoder accepts
`witnessBytes` but not what clock the accepted state carries, and `hclock_unparked` is the premise
that excludes exactly the parked clock.  This file strengthens the acceptance proof (the same walk,
with the postcondition `events = 0`) and then exhibits all four premises on one state.
-/

open Aeneas Aeneas.Std Result
open tacenta_ratchet
open Tacenta.ImportInv
open Tacenta.ImportInv.Ratchet

namespace Tacenta.RatchetDecodedWitness

attribute [local step] read_key_of_zeros read_optional_key_present read_u32_of_zeros from_bytes_loop_empty
attribute [local simp] witnessBytes_val witnessBytes_length witnessBytes_len

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000 in
theorem ratchet_witness_events :
    ∃ s, State.from_bytes witnessBytes = ok (core.result.Result.Ok s) ∧ s.events.val = 0 := by
  have h : State.from_bytes witnessBytes
      ⦃ fun r => ∃ s, r = core.result.Result.Ok s ∧ s.events.val = 0 ⦄ := by
    unfold State.from_bytes
    simp only [fixed_len_eq, optional_key_len_eq, skipped_encoded_len_eq, bind_tc_ok]
    rw [if_neg (by decide), slice_index_eq witnessBytes 0#usize 1#u8 (by decide)]
    simp only [bind_tc_ok]
    rw [if_neg (by simp [STATE_VERSION])]
    step*
    all_goals first
      | (simp only [witnessBytes_val, witnessBytes_length, *]; first | omega | decide)
      | skip
    have hp : pos8.val = 180 := by omega
    have hq : witnessBytes.val[pos8.val]? = some 0#u8 := by
      simp only [witnessBytes_val, hp]; decide
    have hi4 : i4 = 0#u8 := by
      rw [i4_post]
      rw [List.getElem?_eq_getElem
        (h := by rw [hp, witnessBytes_val]; simp [witnessList_length])] at hq
      exact Option.some.inj hq
    rw [hi4, label_byte_zero]
    simp only [bind_tc_ok]
    step*
    all_goals first
      | (simp only [witnessBytes_val, witnessBytes_length, *]; first | omega | decide)
      | skip
    have hsc : skipped_count = 0#usize := by rw [skipped_count_post]; scalar_tac
    rw [hsc]
    step*
    all_goals simp only [Prod.mk.injEq] at pos11_post
    all_goals obtain ⟨h11, hsk, -⟩ := pos11_post
    all_goals subst h11
    all_goals subst hsk
    · exfalso; simp_all
    · rw [invariant_eq]
      simp only [bind_tc_ok]
      split
      · refine ⟨_, rfl, ?_⟩
        simpa using events_post
      · exfalso
        try clear i4_post
        try clear hi4
        try clear hq
        simp_all [InvB, chainsOk, storeOk, keysOk, canonical_zeros,
          alloc.vec.Vec.with_capacity, MAX_SKIPPED_STORE,
          Std.U32.max_eq]
  obtain ⟨r, hr, hre⟩ := Std.WP.spec_imp_exists h
  obtain ⟨s, rfl, hs⟩ := hre
  exact ⟨s, hr, hs⟩


/-- The model state a translated state is related to, read off it. -/
def absState (s : State) : Model.State.State :=
  { dhsPub := Tacenta.T3.keyOf s.dhs_pub, dhrPub := s.dhr_pub.map Tacenta.T3.keyOf,
    rk := Tacenta.T3.keyOf s.rk, cks := s.cks.map Tacenta.T3.keyOf, ckr := s.ckr.map Tacenta.T3.keyOf,
    ns := s.ns.val, nr := s.nr.val, pn := s.pn.val,
    skipped := s.skipped.val.map Tacenta.T3.skippedOf, events := s.events.val,
    labels := Tacenta.T3.labelsOf s.labels }

/-- Every premise of `Ratchet.decoded_receive_refines` (`hdec`, `hR`, `hH`, `hclock_unparked`) on one
state: the decoder accepts `witnessBytes` and the state it returns has a zero clock. -/
theorem decoded_receive_refines_premises_satisfiable :
    ∃ (bytes : Slice Std.U8) (s : State) (m : Model.State.State) (hdr : Header)
      (mh : Model.State.Header),
      State.from_bytes bytes = ok (core.result.Result.Ok s) ∧ Tacenta.T3.StateR s m ∧
      Tacenta.T3.HeaderR hdr mh ∧ s.events.val + 1 < U32.max := by
  obtain ⟨s, hs, hev⟩ := ratchet_witness_events
  refine ⟨witnessBytes, s, absState s, ⟨Std.Array.repeat 32#usize 0#u8, 0#u32, 0#u32⟩,
    ⟨Tacenta.T3.keyOf (Std.Array.repeat 32#usize 0#u8), 0, 0⟩, hs,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩, ?_⟩
  rw [hev]; scalar_tac

end Tacenta.RatchetDecodedWitness

/--
info: 'Tacenta.RatchetDecodedWitness.ratchet_witness_events' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.RatchetDecodedWitness.ratchet_witness_events

/--
info: Tacenta.RatchetDecodedWitness.ratchet_witness_events :
  ∃ s, State.from_bytes witnessBytes = ok (core.result.Result.Ok s) ∧ ↑s.events = 0
-/
#guard_msgs in
#check Tacenta.RatchetDecodedWitness.ratchet_witness_events

/--
info: 'Tacenta.RatchetDecodedWitness.decoded_receive_refines_premises_satisfiable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.RatchetDecodedWitness.decoded_receive_refines_premises_satisfiable

/--
info: Tacenta.RatchetDecodedWitness.decoded_receive_refines_premises_satisfiable :
  ∃ bytes s m hdr mh,
    State.from_bytes bytes = ok (core.result.Result.Ok s) ∧
      Tacenta.T3.StateR s m ∧ Tacenta.T3.HeaderR hdr mh ∧ ↑s.events + 1 < U32.max
-/
#guard_msgs in
#check Tacenta.RatchetDecodedWitness.decoded_receive_refines_premises_satisfiable
