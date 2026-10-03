import Translation.UnitLifecycleT3

/-!
# Every refusal of the Session unit's Triple receive is the model's detailed refusal

The leaf refinements of the classical and the sparse ratchet's `receive` relate a success to the model's
success and the full-store refusal to the model's full-store refusal
(`SessionUnitTripleT3.receive_refines_discharged`, `receive_store_full_refines_discharged`).  Every other
refusal was unrelated, which left one disjunct of `UnitLifecycleDecryptRatchetT3.decrypt_ratchet_refines`
open (`TripleRefusalOpen`).  This module relates every refusal: if the generated Triple receive refuses
with a reason, that reason's public mapping (`tripleReceiveRefusalOfReal`) is defined and is the refusal
`Model.Triple.receiveDetailed` returns, under the hypotheses the existing Triple receive refinement takes.

The statement is `TripleReceiveRefusalRefines`; its hypotheses are those of
`SessionUnitTripleT3.receive_store_full_refines_discharged`, whose numeric premises the session unit's
witness module shows met at a concrete state, at both platform widths
(`NumericWitnessSession.sat_SessionUnitTripleT3_receive_refines_discharged`, the same premises).

The proof follows the leaf proofs it extends: each leaf refusal theorem walks the same branches as
the leaf's success and full-store theorems and names, at each `Err`, the model's reason.  The
classical leaf refuses with `TooManySkipped` or `SkippedStoreFull` (the two skips), `OutOfOrder`,
`NoReceivingChain` or `ChainExhausted`, never `NoSendingChain`; the sparse leaf with
`EpochOutOfOrder` (its advance), every skip refusal, `NoChain`, `ChainRetired` or `OutOfOrder`.  The
sparse `ChainExhausted` of the advance and of the chain step is unreachable under the epoch and
counter bounds the success theorem already takes, as there.
-/

open Aeneas Aeneas.Std Result

namespace Tacenta.UnitLifecycleTripleRefusalT3

open tacenta_session_unit
open Tacenta.UnitLifecycleT3 (ratchetReceiveRefusalOfReal sparseReceiveRefusalOfReal
  tripleReceiveRefusalOfReal)

/-! ## The statement -/

/-- **Every refusal of the generated Triple receive at related states is the model's detailed
refusal, under the public mapping.**  The hypotheses are those of
`SessionUnitTripleT3.receive_store_full_refines_discharged`, in its order. -/
def TripleReceiveRefusalRefines : Prop :=
  ∀ (_hmac : Tacenta.SessionUnitT3.HmacAgrees) (_hkdf : Tacenta.SessionUnitT3.HkdfAgrees)
    (_hzr : Tacenta.SessionUnitT3.ZeroizingRoundTrips)
    (_hvr : Tacenta.SessionUnitT1.RemoveSkippedAtTotal)
    [Tacenta.SessionUnitT1.DerivedKeysModel]
    (_hz96 : Tacenta.SessionUnitSpqrT3.ZeroizingRoundTrips96)
    (_hz64 : Tacenta.SessionUnitSpqrT3.ZeroizingRoundTrips64)
    (_hret : Tacenta.SessionUnitSpqrT3.VecRetainAgrees)
    (_hret_total : Tacenta.SessionUnitSpqrT1.VecRetainTotal)
    (_hrm : Tacenta.SessionUnitSpqrT3.RemoveSkippedAtAgrees)
    (_hzs : Tacenta.SessionUnitSpqrT1.ZeroizeTotal)
    (_hopt : Tacenta.SessionUnitSpqrT1.OptionCloneTotal)
    (s : tacenta_triple.State) (m : Model.Triple.State),
    Tacenta.SessionUnitTripleT3.StateRefines
      Tacenta.SessionUnitTripleT3.ratchetAbs Tacenta.SessionUnitTripleT3.spqrAbs s m →
    ∀ (header : tacenta_triple.Header) (mh : Model.State.Header),
    Tacenta.SessionUnitTripleT3.RatchetHeaderR header.dr mh →
    ∀ (dh_out_recv dh_out_send new_dhs_pub : Array Std.U8 32#usize)
      (output : Option tacenta_spqr.Output),
    (m.classical.skipped.filter (fun x => x.1 == mh.dh && x.2.1 == mh.n)).length ≤ 1 →
    max m.classical.skipped.length Model.State.maxSkippedStore + Model.State.maxSkip ≤ Usize.max →
    m.classical.events + 1 < Std.U32.max →
    m.postQuantum.epoch + 1 < Std.U64.max →
    m.postQuantum.chains.length + 2 < Usize.max →
    (∀ p ∈ m.postQuantum.chains, p.1 + Model.SparseRatchet.epochsKept ≤ Std.U64.max) →
    (∀ sk ∈ m.postQuantum.skipped, sk.1 + Model.SparseRatchet.epochsKept ≤ Std.U64.max) →
    (∀ o : tacenta_spqr.Output, output = some o →
      o.key_epoch.val + Model.SparseRatchet.epochsKept ≤ Std.U64.max) →
    m.postQuantum.skipped.length + Model.SparseRatchet.maxSkip ≤ Usize.max →
    (m.postQuantum.skipped.filter
      (fun x => x.1 == header.epoch.val && x.2.1 == header.pq_n.val)).length ≤ 1 →
    (∀ p ∈ m.postQuantum.chains, ∀ ch : Model.SparseRatchet.Chain,
      (p.2.send = some ch ∨ p.2.receive = some ch) → ch.n < Std.U64.max) →
    tacenta_triple.State.receive s header dh_out_recv dh_out_send new_dhs_pub output ⦃ fun result =>
      ∀ realReason, result = core.result.Result.Err realReason →
        ∃ modelReason, tripleReceiveRefusalOfReal realReason = some modelReason ∧
          Model.Triple.receiveDetailed m
            { dr := mh, epoch := header.epoch.val, pqN := header.pq_n.val }
            (Tacenta.SessionUnitTripleT3.keyOf dh_out_recv)
            (Tacenta.SessionUnitTripleT3.keyOf dh_out_send)
            (Tacenta.SessionUnitTripleT3.keyOf new_dhs_pub)
            (output.map Tacenta.SessionUnitTripleT3.spqrOutputOf) = .error modelReason ⦄

/-! ## The classical ratchet -/

section Classical

open tacenta_session_unit.tacenta_ratchet
open Tacenta.SessionUnitT3
open Tacenta.SessionUnitT1 (DerivedKeysModel)

/-- Two specifications of one call give their conjunction. -/
theorem spec_and {α : Type} {x : Result α} {P Q : α → Prop}
    (hP : x ⦃ P ⦄) (hQ : x ⦃ Q ⦄) : x ⦃ fun r => P r ∧ Q r ⦄ := by
  obtain ⟨y, hy, hPy⟩ := Std.WP.spec_imp_exists hP
  obtain ⟨y', hy', hQy⟩ := Std.WP.spec_imp_exists hQ
  rw [hy] at hy'
  cases hy'
  rw [hy]
  exact Std.WP.spec_ok _ |>.mpr ⟨hPy, hQy⟩

/-- The chain derivation does not run out of message numbers when the last number it derives,
`start_n + count - 1`, is a `u32`.  Each step's `checked_add` is then below the ceiling, so the loop
returns its keys. -/
theorem derive_chain_loop_ok (h : Tacenta.SessionUnitT1.HmacTotal) [DerivedKeysModel]
    (iter : core.ops.range.Range Std.U32) (start_n : Std.U32)
    (cur : Array Std.U8 32#usize)
    (keys : zeroize.Zeroizing (alloc.vec.Vec (Std.U32 × Array Std.U8 32#usize)))
    (hb : (DerivedKeysModel.contents keys).val.length
          + (iter.end.val - iter.start.val) ≤ Usize.max)
    (hroom : start_n.val + iter.end.val ≤ Std.U32.max + 1) :
    derive_chain_loop iter start_n cur keys ⦃ fun r => ∃ p, r = core.result.Result.Ok p ⦄ := by
  unfold derive_chain_loop
  apply loop.spec_decr_nat
    (measure := fun x => (Prod.fst x).end.val - (Prod.fst x).start.val)
    (inv := fun x =>
      (DerivedKeysModel.contents (Prod.snd (Prod.snd x))).val.length
        + ((Prod.fst x).end.val - (Prod.fst x).start.val) ≤ Usize.max ∧
      start_n.val + (Prod.fst x).end.val ≤ Std.U32.max + 1)
  · rintro ⟨it, c, ks⟩ ⟨hinv, hroom'⟩
    simp only at hinv hroom'
    obtain ⟨⟨nx, mk⟩, hck⟩ := Tacenta.SessionUnitT1.kdf_ck_no_panic h c
    simp only [derive_chain_loop.body, hck]
    by_cases hlt : it.start.val < it.end.val
    · step*
      all_goals simp_all
      all_goals omega
    · step*
  · exact ⟨hb, hroom⟩

/-- `derive_chain_refines` with the exhaustion refusal located: the derivation refuses only when
the numbers it would derive pass `u32::MAX`. -/
theorem derive_chain_refines_far (h : HmacAgrees) [DerivedKeysModel]
    (ck : Array Std.U8 32#usize) (start_n count : Std.U32) :
    derive_chain ck start_n count ⦃ fun r =>
      match r with
      | core.result.Result.Ok p =>
        (keyOf p.1, keysOf (DerivedKeysModel.contents p.2))
          = Model.State.deriveChain (keyOf ck) start_n.val count.val
        ∧ (DerivedKeysModel.contents p.2).val.length ≤ count.val
      | core.result.Result.Err e =>
        e = RatchetError.ChainExhausted ∧ Std.U32.max < start_n.val + count.val ⦄ := by
  by_cases hroom : start_n.val + count.val ≤ Std.U32.max
  · have hok : derive_chain ck start_n count ⦃ fun r => ∃ p, r = core.result.Result.Ok p ⦄ := by
      unfold derive_chain
      simp only [lift, alloc.vec.Vec.with_capacity]
      step
      refine derive_chain_loop_ok h.total _ start_n ck _ ?_ ?_
      · simp_all
        scalar_tac
      · simp_all
        omega
    refine Std.WP.spec_mono (spec_and (derive_chain_refines h ck start_n count) hok) ?_
    rintro r ⟨hr, p, rfl⟩
    exact hr
  · refine Std.WP.spec_mono (derive_chain_refines h ck start_n count) ?_
    intro r hr
    cases r with
    | Ok p => exact hr
    | Err e => exact ⟨hr, by omega⟩

attribute [-step] Tacenta.SessionUnitT1.array_eq_total Tacenta.SessionUnitT1.array_ne_total
  Tacenta.SessionUnitT1.kdf_ck_step Tacenta.SessionUnitT1.zeroizing_deref_step
  Tacenta.SessionUnitT1.skip_message_keys_loop0_grows Tacenta.SessionUnitT1.skip_message_keys_loop0_bound
  Tacenta.SessionUnitT3.derive_chain_refines
attribute [local step] derive_chain_refines_far

/-- Every refusal of the classical skip is the model's detailed skip refusal. -/
theorem ratchet_skip_refusal_refines (h : HmacAgrees)
    (hrm : Tacenta.SessionUnitT1.RemoveSkippedAtTotal) [DerivedKeysModel]
    (s : State) (m : Model.State.State) (hR : StateR s m) (upto : Std.U32)
    (hs : s.skipped.val.length + MAX_SKIP.val ≤ Usize.max) :
    skip_message_keys s upto ⦃ fun r =>
      ∀ e, r.1 = core.result.Result.Err e →
        ∃ reason, ratchetReceiveRefusalOfReal e = some reason ∧
          Model.Ratchet.skipMessageKeysDetailed m upto.val = .error reason ⦄ := by
  have hht : Tacenta.SessionUnitT1.HmacTotal := h.total
  obtain ⟨_, hdhr, _, _, hckr, _, hnr, _, hskip, _, _⟩ := hR
  unfold skip_message_keys
  rcases hck : s.ckr with _ | ck
  · simp
  · rcases hdh : s.dhr_pub with _ | dhr
    · simp
    · have hmck : m.ckr = some (keyOf ck) := by rw [← hckr, hck]; rfl
      have hmdh : m.dhrPub = some (keyOf dhr) := by rw [← hdhr, hdh]; rfl
      by_cases hle : upto ≤ s.nr
      · simp [hle]
      · have hgtN : ¬ (upto.val ≤ m.nr) := by rw [← hnr]; scalar_tac
        simp only [hle, if_false, lift]
        by_cases hg : upto > core.num.U32.saturating_add s.nr MAX_SKIP
        · have hg' : (core.num.U32.saturating_add s.nr MAX_SKIP).val < upto.val := hg
          simp only [Std.bind_tc_ok]
          rw [if_pos hg, Std.WP.spec_ok]
          intro e he
          injection he with he
          subst e
          refine ⟨.tooManySkipped, rfl, ?_⟩
          have hsat := saturating_add_val s.nr MAX_SKIP
          have hupto := upto.hBounds
          have hfar : m.nr + Model.State.maxSkip < upto.val := by
            rw [← hnr]
            simp only [MAX_SKIP, Model.State.maxSkip] at *
            have : (core.num.U32.saturating_add s.nr 1000#u32).val = s.nr.val + 1000 := by
              rw [hsat]
              by_contra hne
              have hmin : min U32.max (s.nr.val + (1000#u32 : Std.U32).val) = U32.max := by
                simp only [show (1000#u32 : Std.U32).val = 1000 by rfl] at hne ⊢
                omega
              rw [hmin] at hsat
              have : upto.val ≤ U32.max := by scalar_tac
              omega
            omega
          have hnone : Model.State.skipMessageKeys m upto.val = none := by
            simp [Model.State.skipMessageKeys, hmck, hmdh, hgtN, show upto.val > m.nr + Model.State.maxSkip from hfar]
          unfold Model.Ratchet.skipMessageKeysDetailed
          rw [hnone]
          simp [hfar]
        have hgap := Tacenta.SessionUnitT1.skip_gap_le s.nr upto hg
        step*
        all_goals have hsmax := s.skipped.property
        all_goals simp_all [alloc.vec.Vec.with_capacity, alloc.vec.Vec.new]
        · have hlen := congrArg List.length skipped1_post
          have hfil := List.length_filter_le
            (keepOutside (keyOf dhr) s.nr.val upto.val)
            (List.map skippedOf s.skipped.val)
          simp only [List.length_map] at hlen hfil
          have hskiplen := congrArg List.length hskip
          simp only [List.length_map] at hskiplen
          have hpurge : skipped1.val.length ≤ s.skipped.val.length := by omega
          have hlenval : skipped1.len.val = skipped1.val.length := by
            simp [alloc.vec.Vec.len]
          have hlen2 := congrArg List.length skipped2_post
          rw [← hnr, ← hskip] at hlen2
          simp only [List.length_map] at hlen2
          have hpurge2 : skipped2.val.length ≤ s.skipped.val.length := by omega
          have hcast : (UScalar.cast .Usize i1).val = i1.val := by scalar_tac
          omega
        · refine ⟨.skippedStoreFull, rfl, ?_⟩
          have hg1 : ¬ (upto.val > m.nr + Model.State.maxSkip) := by
            rw [← hnr]
            simp only [MAX_SKIP, Model.State.maxSkip] at *
            scalar_tac
          have hkept : List.map skippedOf skipped2.val =
              Model.State.skipSurvivors m (keyOf dhr) upto.val := by
            rw [skipped2_post]
            change List.filter (fun e =>
              !(e.1 == keyOf dhr && decide (m.nr ≤ e.2.1)
                && decide (e.2.1 < upto.val))) m.skipped = _
            rfl
          have hkeptLen := congrArg List.length hkept
          simp only [List.length_map] at hkeptLen
          have hi1 : i1.val = upto.val - m.nr := by omega
          have hi4nat : i5.val = skipped2.val.length + i1.val := by omega
          have hg2 : (Model.State.skipSurvivors m (keyOf dhr) upto.val).length
              + (upto.val - m.nr) > Model.State.maxSkippedStore := by
            rw [← hkeptLen]
            have hreal : MAX_SKIPPED_STORE.val <
                skipped2.val.length + (upto.val - m.nr) := by assumption
            simpa [Model.State.maxSkippedStore, MAX_SKIPPED_STORE] using hreal
          have hnotle : ¬ upto.val ≤ m.nr := by omega
          have hnone : Model.State.skipMessageKeys m upto.val = none := by
            simp [Model.State.skipMessageKeys, hmck, hmdh, hnotle, hg1, hg2]
          unfold Model.Ratchet.skipMessageKeysDetailed
          rw [hnone]
          simp only [if_neg (by omega : ¬ m.nr + Model.State.maxSkip < upto.val)]
        · obtain ⟨ck2, keys⟩ := v
          obtain ⟨rp, rlen⟩ := r_post
          have rlen' : (DerivedKeysModel.contents keys).val.length ≤
              upto.val - m.nr := by simpa using rlen
          have hstorebound : skipped2.val.length + (upto.val - m.nr) ≤
              MAX_SKIPPED_STORE.val := by assumption
          have hlooproom : skipped2.val.length +
              (DerivedKeysModel.contents keys).val.length ≤ Usize.max := by
            have hcap : MAX_SKIPPED_STORE.val ≤ Usize.max := by scalar_tac
            omega
          step with Tacenta.SessionUnitT1.skip_message_keys_loop1_no_panic
            dhr skipped2 s.events keys 0#usize hlooproom
          simp

-- As in `SessionUnitT3` from its `receive_tail_refines` on: the receive-level calls are applied by
-- hand, so T1's weaker rules for them come out of the stepping set.
attribute [-step] Tacenta.SessionUnitT1.age_store_spec Tacenta.SessionUnitT1.skip_message_keys_room
  Tacenta.SessionUnitT1.dh_ratchet_spec

/-- Every refusal of the receive suffix both ratchet paths share is the model's: the skip's own
refusals, then `OutOfOrder`, `NoReceivingChain` and `ChainExhausted`, in the model's order. -/
theorem ratchet_receive_tail_refusal_refines (h : HmacAgrees)
    (hrm : Tacenta.SessionUnitT1.RemoveSkippedAtTotal) [DerivedKeysModel]
    (st : State) (mst : Model.State.State) (hR : StateR st mst) (n : Std.U32)
    (hs : st.skipped.val.length + MAX_SKIP.val ≤ Usize.max) :
    (do
      let (r1, state4) ← skip_message_keys st n
      match r1 with
      | core.result.Result.Ok _ =>
        if n < state4.nr
        then ok (core.result.Result.Err RatchetError.OutOfOrder, state4)
        else
          match state4.ckr with
          | none => ok (core.result.Result.Err RatchetError.NoReceivingChain, state4)
          | some ck =>
            let o2 ← lift (U32.checked_add state4.nr 1#u32)
            match o2 with
            | none => ok (core.result.Result.Err RatchetError.ChainExhausted, state4)
            | some next_nr =>
              let (ck2, mk) ← kdf_ck ck
              let state5 ← age_store { state4 with ckr := some ck2, nr := next_nr }
              ok (core.result.Result.Ok mk, state5)
      | core.result.Result.Err e => ok (core.result.Result.Err e, state4))
    ⦃ fun r => ∀ e, r.1 = core.result.Result.Err e →
      ∃ reason, ratchetReceiveRefusalOfReal e = some reason ∧
        (match Model.Ratchet.skipMessageKeysDetailed mst n.val with
         | .error reason => .error reason
         | .ok st2 =>
             if n.val < st2.nr then .error .outOfOrder
             else
               match st2.ckr with
               | none => .error .noReceivingChain
               | some ck =>
                   if st2.nr < Model.State.u32Max then
                     let (ck', mk) := Model.State.kdfCk ck
                     .ok (Model.State.ageStore { st2 with ckr := some ck', nr := st2.nr + 1 }, mk)
                   else
                     .error .chainExhausted :
          Except Model.Ratchet.ReceiveRefusal (Model.State.State × Model.State.Key)) =
          .error reason ⦄ := by
  have hht : Tacenta.SessionUnitT1.HmacTotal := h.total
  obtain ⟨rr, hrr⟩ := (Tacenta.SessionUnitT1.noPanic_iff _).mp
    (Tacenta.SessionUnitT1.skip_message_keys_no_panic hht hrm st n hs)
  obtain ⟨r1, state4⟩ := rr
  have hsk := Tacenta.SessionUnitT3.skip_message_keys_refines h hrm st mst hR n hs
  have href := ratchet_skip_refusal_refines h hrm st mst hR n hs
  rw [hrr] at hsk href ⊢
  simp only [Std.WP.spec_ok] at hsk href
  rcases r1 with _ | e
  · obtain ⟨m2, hm2, hSR2⟩ := hsk rfl
    have hdet := (Model.Ratchet.skipMessageKeysDetailed_ok_iff mst n.val m2).2 hm2
    step*
    · have hlt : n < state4.nr := by assumption
      intro e he
      injection he with he
      subst e
      have hlt' : n.val < m2.nr := by rw [← hSR2.nr]; scalar_tac
      exact ⟨.outOfOrder, rfl, by rw [hdet]; simp [hlt']⟩
    · have hlt : ¬ n < state4.nr := by assumption
      have hck : state4.ckr = none := by assumption
      intro e he
      injection he with he
      subst e
      have hnlt : ¬ n.val < m2.nr := by rw [← hSR2.nr]; scalar_tac
      have hmck : m2.ckr = none := by rw [← hSR2.ckr, hck]; rfl
      exact ⟨.noReceivingChain, rfl, by rw [hdet]; simp [hnlt, hmck]⟩
    · have hlt : ¬ n < state4.nr := by assumption
      rename_i ck _ _ _ _
      have hck : state4.ckr = some ck := by assumption
      have hmax : U32.max < state4.nr.val + 1 := by simp_all
      intro e he
      injection he with he
      subst e
      have hnlt : ¬ n.val < m2.nr := by rw [← hSR2.nr]; scalar_tac
      have hmck : m2.ckr = some (keyOf ck) := by rw [← hSR2.ckr, hck]; rfl
      have hmmax : ¬ m2.nr < Model.State.u32Max := by
        rw [← hSR2.nr, Model.State.u32Max_eq]
        scalar_tac
      exact ⟨.chainExhausted, rfl, by rw [hdet]; simp [hnlt, hmck, hmmax]⟩
    · step with Tacenta.SessionUnitT1.age_store_spec hrm
        { state4 with ckr := some ck2, nr := next_nr }
      simp
  · -- The skip's own refusal, passed through: `href` names its model reason.
    step*

/-- **Every refusal of the classical receive is the model's detailed refusal.**  The branches are
those of `SessionUnitT3.receive_store_full_refines`; at each refusal the model's reason is named and
the public mapping `ratchetReceiveRefusalOfReal` is defined there (so the receive never refuses with
`NoSendingChain`). -/
theorem ratchet_receive_refusal_refines (h : HmacAgrees) (hk : HkdfAgrees)
    (hz : ZeroizingRoundTrips) (hrm : Tacenta.SessionUnitT1.RemoveSkippedAtTotal)
    [DerivedKeysModel] (s : State) (m : Model.State.State) (hR : StateR s m)
    (hdr : Header) (mh : Model.State.Header) (hH : HeaderR hdr mh)
    (dh_out_recv dh_out_send new_dhs_pub : Array Std.U8 32#usize)
    (hone : (m.skipped.filter (matchesHeader mh)).length ≤ 1)
    (hs : max s.skipped.val.length MAX_SKIPPED_STORE.val + MAX_SKIP.val
            ≤ Usize.max) :
    receive s hdr dh_out_recv dh_out_send new_dhs_pub ⦃ fun r =>
      ∀ e, r.1 = core.result.Result.Err e →
        ∃ reason, ratchetReceiveRefusalOfReal e = some reason ∧
          Model.Ratchet.receiveDetailed m mh (keyOf dh_out_recv)
            (keyOf dh_out_send) (keyOf new_dhs_pub) = .error reason ⦄ := by
  have hht : Tacenta.SessionUnitT1.HmacTotal := h.total
  have hkt : Tacenta.SessionUnitT1.HkdfTotal := hk.total
  have hzt : Tacenta.SessionUnitT1.ZeroizingTotal := hz.total
  unfold receive
  obtain ⟨rr, hrr⟩ := (Tacenta.SessionUnitT1.noPanic_iff _).mp
    (Tacenta.SessionUnitT1.try_skipped_no_panic hrm s hdr)
  obtain ⟨o, state1⟩ := rr
  have hts := try_skipped_refines hrm s m hR hdr mh hH hone
  rw [hrr] at hts ⊢
  obtain ⟨hsome, hnone⟩ := hts
  rcases o with _ | mk0
  · obtain ⟨hmiss, hSR1⟩ := hnone rfl
    have hlen1 : state1.skipped.val.length = s.skipped.val.length := by
      have hh := congrArg List.length (hSR1.skipped.trans hR.skipped.symm)
      simpa using hh
    have hlen : state1.skipped.val.length + MAX_SKIP.val ≤ Usize.max := by
      simp only [MAX_SKIPPED_STORE] at *
      omega
    -- The two ratchet-step paths: the first skip, the step, then the shared suffix.
    have ratchetPath : ¬ (m.dhrPub = some mh.dh) →
        (do
          let (r, state2) ← skip_message_keys state1 hdr.pn
          match r with
          | core.result.Result.Ok _ =>
            let state3 ← dh_ratchet state2 hdr dh_out_recv dh_out_send new_dhs_pub
            let (r1, state4) ← skip_message_keys state3 hdr.n
            match r1 with
            | core.result.Result.Ok _ =>
              if hdr.n < state4.nr
              then ok (core.result.Result.Err RatchetError.OutOfOrder, state4)
              else
                match state4.ckr with
                | none => ok (core.result.Result.Err RatchetError.NoReceivingChain, state4)
                | some ck =>
                  let o2 ← lift (U32.checked_add state4.nr 1#u32)
                  match o2 with
                  | none => ok (core.result.Result.Err RatchetError.ChainExhausted, state4)
                  | some next_nr =>
                    let (ck2, mk) ← kdf_ck ck
                    let state5 ← age_store { state4 with ckr := some ck2, nr := next_nr }
                    ok (core.result.Result.Ok mk, state5)
            | core.result.Result.Err e => ok (core.result.Result.Err e, state4)
          | core.result.Result.Err e => ok (core.result.Result.Err e, state2)) ⦃ fun r =>
          ∀ e, r.1 = core.result.Result.Err e →
            ∃ reason, ratchetReceiveRefusalOfReal e = some reason ∧
              Model.Ratchet.receiveDetailed m mh (keyOf dh_out_recv)
                (keyOf dh_out_send) (keyOf new_dhs_pub) = .error reason ⦄ := by
      intro hnotsame
      have hcond : ¬ ((m.dhrPub == some mh.dh) = true) := by simpa using hnotsame
      obtain ⟨r2, hr2⟩ := (Tacenta.SessionUnitT1.noPanic_iff _).mp
        (Tacenta.SessionUnitT1.skip_message_keys_no_panic hht hrm state1 hdr.pn hlen)
      obtain ⟨rres2, state2⟩ := r2
      have hsk := Tacenta.SessionUnitT3.skip_message_keys_refines h hrm state1 m hSR1 hdr.pn hlen
      have hskRef := ratchet_skip_refusal_refines h hrm state1 m hSR1 hdr.pn hlen
      rw [hr2] at hsk hskRef ⊢
      simp only [Std.WP.spec_ok] at hsk hskRef
      rcases rres2 with _ | e2
      · obtain ⟨m2, hm2, hSR2⟩ := hsk rfl
        step*
        obtain ⟨r3, hr3, hdr3⟩ := Std.WP.spec_imp_exists
          (dh_ratchet_refines hk hz state2 m2 hSR2 hdr mh hH dh_out_recv
            dh_out_send new_dhs_pub)
        rw [hr3]
        have hlen3 : r3.skipped.val.length + MAX_SKIP.val ≤ Usize.max := by
          have hb := Tacenta.SessionUnitT1.skip_message_keys_bound hht hrm state1 hdr.pn hlen
          rw [hr2] at hb
          have hd3 := Tacenta.SessionUnitT1.dh_ratchet_spec hkt hzt state2 hdr dh_out_recv
            dh_out_send new_dhs_pub
          rw [hr3] at hd3
          have hb2 : state2.skipped.val.length
              ≤ max state1.skipped.val.length MAX_SKIPPED_STORE.val := hb
          have hd32 : r3.skipped.val.length = state2.skipped.val.length := hd3
          simp only [MAX_SKIPPED_STORE] at *
          omega
        refine Std.WP.spec_mono
          (ratchet_receive_tail_refusal_refines h hrm r3 _ hdr3 hdr.n hlen3) ?_
        intro result htail e he
        obtain ⟨reason, hmap, htailRes⟩ := htail e he
        refine ⟨reason, hmap, ?_⟩
        have hfirst := (Model.Ratchet.skipMessageKeysDetailed_ok_iff m hdr.pn.val m2).2 hm2
        rw [hH.pn] at hfirst
        rw [hH.n] at htailRes
        unfold Model.Ratchet.receiveDetailed
        rw [hmiss, if_neg hcond, hfirst]
        exact htailRes
      · step*
        obtain ⟨reason, hmap, hfirst⟩ := hskRef e2 rfl
        rw [hH.pn] at hfirst
        intro e he
        injection he with he
        subst e
        refine ⟨reason, hmap, ?_⟩
        unfold Model.Ratchet.receiveDetailed
        rw [hmiss, if_neg hcond, hfirst]
    step*
    rcases hd : state1.dhr_pub with _ | dhr <;> (try simp only) <;> step*
    -- No receiving ratchet key held yet, so the first message ratchets.
    · have hnotsame : ¬ (m.dhrPub = some mh.dh) := by
        have hc := hSR1.dhr_pub
        rw [hd] at hc
        simp only [Option.map] at hc
        rw [← hc]
        simp
      rw [← hd]
      exact ratchetPath hnotsame
    -- The peer moved to a ratchet key we do not hold, so the chain ratchets.
    · have hnotsame : ¬ (m.dhrPub = some mh.dh) := by
        have hxt : x = true := by assumption
        have hne : dhr ≠ hdr.dh := x_post.mp hxt
        have hc := hSR1.dhr_pub
        rw [hd] at hc
        simp only [Option.map] at hc
        rw [← hc]
        simp only [Option.some.injEq]
        intro heq
        rw [← hH.dh] at heq
        exact hne (keyOf_inj heq)
      rw [← hd]
      exact ratchetPath hnotsame
    -- The peer stayed on the ratchet key we hold: the shared suffix applies directly.
    · rw [← hd]
      refine Std.WP.spec_mono
        (ratchet_receive_tail_refusal_refines h hrm state1 m hSR1 hdr.n hlen) ?_
      intro result htail e he
      obtain ⟨reason, hmap, htailRes⟩ := htail e he
      refine ⟨reason, hmap, ?_⟩
      have hxf : ¬x = true := by assumption
      have hdheq : dhr = hdr.dh := by
        by_contra hc
        exact hxf (x_post.mpr hc)
      have hmdhr : m.dhrPub = some mh.dh := by
        have hc := hSR1.dhr_pub
        rw [hd] at hc
        simp only [Option.map] at hc
        rw [← hc, hdheq, hH.dh]
      rw [hH.n] at htailRes
      unfold Model.Ratchet.receiveDetailed
      rw [hmiss]
      simp only [hmdhr, beq_self_eq_true, if_pos]
      exact htailRes
  · step*
    step with Tacenta.SessionUnitT1.age_store_spec hrm state1
    simp

end Classical

/-! ## The sparse ratchet -/

section Sparse

open tacenta_session_unit.tacenta_spqr
open Tacenta.SessionUnitSpqrT3

-- As in `SessionUnitSpqrT3.skip_message_keys_refines`: the store loop is stepped by hand with its
-- refinement, so T1's returns-only rules for it come out of the stepping set.
attribute [-step] Tacenta.SessionUnitSpqrT1.skip_message_keys_loop1_no_panic
  Tacenta.SessionUnitSpqrT1.skip_message_keys_loop1_grows

-- The width split below closes one case by `simp_all` alone and the other with `scalar_tac`.
set_option linter.unnecessarySeqFocus false in
/-- Every refusal of the sparse skip is the model's detailed skip refusal, under the mapping
`sparseReceiveRefusalOfReal`.  The branches are those of `SessionUnitSpqrT3.skip_message_keys_refines`. -/
theorem spqr_skip_refusal_refines (hkr : SpqrHkdfAgrees) (hz64 : ZeroizingRoundTrips64)
    (hret : VecRetainAgrees)
    (hret_total : Tacenta.SessionUnitSpqrT1.VecRetainTotal)
    (hz : Tacenta.SessionUnitSpqrT1.ZeroizeTotal)
    (hopt : Tacenta.SessionUnitSpqrT1.OptionCloneTotal)
    {s : State} {m : Model.SparseRatchet.State} (hrel : StateRefines s m) (e upto : Std.U64)
    (hroom : s.chains.val.length < Usize.max)
    (hskiproom : s.skipped.val.length + MAX_SKIP.val ≤ Usize.max) :
    State.skip_message_keys s e upto ⦃ fun r =>
      ∀ err, r.1 = core.result.Result.Err err →
        Model.SparseRatchet.skipMessageKeysDetailed m e.val upto.val =
          .error (sparseReceiveRefusalOfReal err) ⦄ := by
  unfold State.skip_message_keys
  step with findChains_refines hrel e
  rcases ho : o with _ | cs
  · rw [ho] at o_post
    simp only [Option.map_none] at o_post
    step*
    intro err herr
    injection herr with herr
    subst err
    exact (Model.SparseRatchet.skipMessageKeysDetailed_no_chain_iff m e.val upto.val).2 o_post.symm
  · rw [ho] at o_post
    simp only [Option.map_some] at o_post
    step*
    step with Tacenta.SessionUnitSpqrT1.chains_clone_spec hopt cs
    rw [cs1_post]
    rcases hcsr : cs.receive with _ | ch
    · step*
      intro err herr
      injection herr with herr
      subst err
      exact (Model.SparseRatchet.skipMessageKeysDetailed_retired_iff m e.val upto.val).2
        ⟨chainsOf cs, o_post.symm, by simp [chainsOf, hcsr]⟩
    · step*
      · -- Too many skipped.
        have hnotA : ¬ upto.val ≤ (chainOf ch).n := by simp only [chainOf]; scalar_tac
        have hB : upto.val > (chainOf ch).n + Model.SparseRatchet.maxSkip := by
          simp only [chainOf]
          have := max_skip_agrees
          scalar_tac
        unfold Model.SparseRatchet.skipMessageKeysDetailed
        simp [Model.SparseRatchet.skipMessageKeys, ← o_post, chainsOf, hcsr, hnotA, hB,
          sparseReceiveRefusalOfReal]
      · have hi1 : i1.val = count.val := by
          have := max_skip_val
          rw [i1_post, UScalar.cast_val_eq]
          rcases System.Platform.numBits_eq with hbits | hbits <;> simp_all <;> scalar_tac
        scalar_tac
      · have hi1 : i1.val = count.val := by
          have := max_skip_val
          rw [i1_post, UScalar.cast_val_eq]
          rcases System.Platform.numBits_eq with hbits | hbits <;> simp_all <;> scalar_tac
        have hi4 : i4.val = count.val := by
          have := max_skip_val
          rw [i4_post, UScalar.cast_val_eq]
          rcases System.Platform.numBits_eq with hbits | hbits <;> simp_all <;> scalar_tac
        have hlen := congrArg List.length skipped1_post
        have hfil := List.length_filter_le
          (fun x : Skipped => !(x.epoch == e && decide (ch1.n < x.n) && decide (x.n ≤ upto)))
          s.skipped.val
        have hlenval : skipped1.len.val = skipped1.val.length := by
          simp [alloc.vec.Vec.len]
        have hgap : count.val ≤ MAX_SKIP.val := by scalar_tac
        scalar_tac
      · -- The store the skip would leave is over the bound.
        have hnotA : ¬ upto.val ≤ (chainOf ch).n := by simp only [chainOf]; scalar_tac
        have hnotB : ¬ upto.val > (chainOf ch).n + Model.SparseRatchet.maxSkip := by
          simp only [chainOf]
          have := max_skip_agrees
          scalar_tac
        have hi4 : i4.val = count.val := by
          have := max_skip_val
          rw [i4_post, UScalar.cast_val_eq]
          rcases System.Platform.numBits_eq with hbits | hbits <;> simp_all <;> scalar_tac
        have hsurv := skip_survivors_of_copy hrel e upto ch1.n skipped1 skipped1_post
        have hsurvlen : skipped1.val.length =
            (Model.SparseRatchet.skipSurvivors m e.val (chainOf ch).n upto.val).length := by
          have := congrArg List.length hsurv
          simpa [chainOf, ch1_post] using this
        have hlenval : skipped1.len.val = skipped1.val.length := by
          simp [alloc.vec.Vec.len]
        have hC : (Model.SparseRatchet.skipSurvivors m e.val (chainOf ch).n upto.val).length
            + (upto.val - (chainOf ch).n) > Model.SparseRatchet.maxSkippedStore := by
          have hmax := max_skipped_store_agrees
          have hn : (chainOf ch).n = ch1.n.val := by simp [chainOf, ch1_post]
          rw [← hsurvlen, hn]
          scalar_tac
        unfold Model.SparseRatchet.skipMessageKeysDetailed
        simp [Model.SparseRatchet.skipMessageKeys, ← o_post, chainsOf,
          hcsr, hnotA, hnotB, hC, sparseReceiveRefusalOfReal]
      · -- Room for the walk: the skip succeeds, so there is no refusal to name.
        have hi1 : i1.val = count.val := by
          have := max_skip_val
          rw [i1_post, UScalar.cast_val_eq]
          rcases System.Platform.numBits_eq with hbits | hbits <;> simp_all <;> scalar_tac
        have hi4 : i4.val = count.val := by
          have := max_skip_val
          rw [i4_post, UScalar.cast_val_eq]
          rcases System.Platform.numBits_eq with hbits | hbits <;> simp_all <;> scalar_tac
        step with skip_message_keys_loop1_derive_refines hkr hz64 hz e upto skipped1 ch1.ck ch1.n
          (by scalar_tac)
          (by
            have hlen := congrArg List.length skipped1_post
            have hfil := List.length_filter_le
              (fun x : Skipped => !(x.epoch == e && ch1.n < x.n && x.n ≤ upto))
              s.skipped.val
            have hpurge : skipped1.val.length ≤ s.skipped.val.length := by
              omega
            have := max_skip_agrees
            have hlenval : skipped1.len.val = skipped1.val.length := by
              simp [alloc.vec.Vec.len]
            have hslen : s.skipped.len.val = s.skipped.val.length := by
              simp [alloc.vec.Vec.len]
            have hgap : upto.val - ch1.n.val ≤ MAX_SKIP.val := by
              have := max_skip_agrees
              scalar_tac
            omega)
        obtain ⟨_, hskipped_zeroize⟩ := hret_total.2.1 Skipped.Insts.ZeroizeZeroize s.skipped
        simp only [hskipped_zeroize]
        have hcsend :
            core.option.Option.Insts.CoreCloneClone.clone Chain.Insts.CoreCloneClone cs.send
              ⦃ fun o => o = cs.send ⦄ :=
          hopt Chain.Insts.CoreCloneClone cs.send
            (fun x _ => Tacenta.SessionUnitSpqrT1.chain_clone_spec x)
        step with hcsend
        have hrel1 : StateRefines { s with skipped := skipped2 }
            { m with skipped := skipped2.val.map skippedOf } :=
          ⟨hrel.rk, hrel.epoch, hrel.chains, rfl, hrel.direction⟩
        step with set_chains_refines hret hret_total hrel1 e _ hroom
        intro err herr
        cases herr

/-- Every refusal of the part of the sparse `receive` after `maybe_advance` is the model's detailed
refusal at the advanced state.  The branches are those of `SessionUnitSpqrT3.receive_refines_continuation`;
the exhaustion branch of the chain step is refuted there by the counter bound, as here. -/
theorem spqr_receive_continuation_refusal_refines (hkr : SpqrHkdfAgrees)
    (hz64 : ZeroizingRoundTrips64)
    (hret : VecRetainAgrees)
    (hret_total : Tacenta.SessionUnitSpqrT1.VecRetainTotal)
    (hrm : RemoveSkippedAtAgrees) (hz : Tacenta.SessionUnitSpqrT1.ZeroizeTotal)
    (hopt : Tacenta.SessionUnitSpqrT1.OptionCloneTotal)
    {self1 : State} {m1 : Model.SparseRatchet.State} (hrel1 : StateRefines self1 m1)
    (receiving_epoch n : Std.U64)
    (hroom : self1.chains.val.length + 1 < Usize.max)
    (hskiproom : self1.skipped.val.length + MAX_SKIP.val ≤ Usize.max)
    (hone : (m1.skipped.filter
      (fun x => x.1 == receiving_epoch.val && x.2.1 == n.val)).length ≤ 1)
    (hccb1 : ChainCounterBounded m1.chains) :
    (do
      let (o, self2) ← State.try_skipped self1 receiving_epoch n
      match o with
      | none =>
        let i ← lift (core.num.U64.saturating_sub n 1#u64)
        let (r1, self3) ← self2.skip_message_keys receiving_epoch i
        let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
        match cf1 with
        | core.ops.control_flow.ControlFlow.Continue _ =>
          let o1 ← self3.find_chains receiving_epoch
          match o1 with
          | none => ok (core.result.Result.Err SpqrError.NoChain, self3)
          | some cs =>
            let cs1 ← Chains.Insts.CoreCloneClone.clone cs
            match cs1.receive with
            | none => ok (core.result.Result.Err SpqrError.ChainRetired, self3)
            | some ch =>
              let ch1 ← Chain.Insts.CoreCloneClone.clone ch
              -- The counter check is a `checked_add`, so this statement
              -- carries the exhaustion branch the generated code has. It
              -- is unreachable under `hccb1` and discharged as such below.
              let o2 ← lift (Std.U64.checked_add ch1.n 1#u64)
              match o2 with
              | none => ok (core.result.Result.Err SpqrError.ChainExhausted, self3)
              | some expected =>
                if n != expected then ok (core.result.Result.Err SpqrError.OutOfOrder, self3)
                else
                  let (next, mk) ← kdf_ck ch1.ck n
                  let o3 ← core.option.Option.Insts.CoreCloneClone.clone
                    Chain.Insts.CoreCloneClone cs1.send
                  let self4 ← self3.set_chains receiving_epoch
                    { send := o3, receive := some { ck := next, n } }
                  ok (core.result.Result.Ok mk, self4)
        | core.ops.control_flow.ControlFlow.Break residual =>
          let r2 ←
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
              (Array Std.U8 32#usize) (core.convert.FromSame SpqrError) residual
          ok (r2, self3)
      | some k => ok (core.result.Result.Ok k, self2)) ⦃ fun r =>
      ∀ err, r.1 = core.result.Result.Err err →
        Model.SparseRatchet.receiveDetailed m1 receiving_epoch.val none n.val =
          .error (sparseReceiveRefusalOfReal err) ⦄ := by
  step with try_skipped_refines hrm hrel1 receiving_epoch n hone
  rcases hts : Model.SparseRatchet.trySkipped m1 receiving_epoch.val n.val with _ | res
  · rw [hts] at o_post
    obtain ⟨hno, hself2⟩ := o_post
    simp only [hno]
    simp only [lift]
    step*
    have hchainlen1 := congrArg List.length hself2.chains
    have hchainlen2 := congrArg List.length hrel1.chains
    simp only [List.length_map] at hchainlen1 hchainlen2
    have hskiplen1 := congrArg List.length hself2.skipped
    have hskiplen2 := congrArg List.length hrel1.skipped
    simp only [List.length_map] at hskiplen1 hskiplen2
    have hnsub : (core.num.U64.saturating_sub n 1#u64).val = n.val - 1 := by
      unfold core.num.U64.saturating_sub UScalar.saturating_sub UScalar.val
      simp only [BitVec.toNat_ofNat]
      have h1 : (1#u64 : Std.U64).bv.toNat = 1 := rfl
      rw [h1]
      simp only [Nat.zero_max]
      have h2 : n.bv.toNat < 2 ^ UScalarTy.U64.numBits := n.bv.isLt
      rw [Nat.mod_eq_of_lt (by omega)]
    step with spec_and
      (skip_message_keys_refines hkr hz64 hret hret_total hz hopt hself2 receiving_epoch
        (core.num.U64.saturating_sub n 1#u64) (by scalar_tac) (by scalar_tac))
      (spqr_skip_refusal_refines hkr hz64 hret hret_total hz hopt hself2 receiving_epoch
        (core.num.U64.saturating_sub n 1#u64) (by scalar_tac) (by scalar_tac))
    step
    rw [hnsub] at r1_post1 r1_post2 r1_post3
    rcases hsmk : Model.SparseRatchet.skipMessageKeys m1 receiving_epoch.val (n.val - 1)
      with _ | st2
    · -- The skip refused: its reason is passed through.
      rw [hsmk] at r1_post1
      obtain ⟨err, herr, _⟩ := r1_post1
      rw [herr] at cf1_post
      simp only [cf1_post]
      intro err' hres
      simp only [core.convert.FromSame.from] at hres
      cases hres
      have hdetailed := r1_post3 err herr
      unfold Model.SparseRatchet.receiveDetailed
      simp only [Model.SparseRatchet.maybeAdvanceReceiveDetailed,
        Model.SparseRatchet.maybeAdvanceDetailed, hts, hdetailed]
    · rw [hsmk] at r1_post1
      obtain ⟨hrOk, hself3⟩ := r1_post1
      rw [hrOk] at cf1_post
      simp only [cf1_post]
      have hskipdet : Model.SparseRatchet.skipMessageKeysDetailed m1 receiving_epoch.val
          (n.val - 1) = .ok st2 :=
        (Model.SparseRatchet.skipMessageKeysDetailed_ok_iff _ _ _ _).2 hsmk
      have hsmklen := skipMessageKeys_chains_len_le m1 receiving_epoch.val (n.val - 1) st2 hsmk
      step with findChains_refines hself3 receiving_epoch
      rcases ho1 : o1 with _ | cs
      · -- No chain for the epoch after the skip.
        rw [ho1] at o1_post
        simp only [Option.map_none] at o1_post
        step*
        try (intro err herr; injection herr with herr; subst err)
        unfold Model.SparseRatchet.receiveDetailed
        simp [Model.SparseRatchet.maybeAdvanceReceiveDetailed,
          Model.SparseRatchet.maybeAdvanceDetailed, hts, hskipdet, ← o1_post,
          sparseReceiveRefusalOfReal]
      · rw [ho1] at o1_post
        simp only [Option.map_some] at o1_post
        step*
        step with Tacenta.SessionUnitSpqrT1.chains_clone_spec hopt cs
        rw [cs1_post]
        rcases hcsr : cs.receive with _ | ch
        · -- The chain's receiving side is retired.
          step*
          try (intro err herr; injection herr with herr; subst err)
          unfold Model.SparseRatchet.receiveDetailed
          simp [Model.SparseRatchet.maybeAdvanceReceiveDetailed,
            Model.SparseRatchet.maybeAdvanceDetailed, hts, hskipdet, ← o1_post, chainsOf, hcsr,
            sparseReceiveRefusalOfReal]
        · have hcnt : ch.n.val < Std.U64.max := by
            have hcb1 : ChainCounterBounded st2.chains :=
              skipMessageKeys_chain_counter_bounded m1 receiving_epoch.val (n.val - 1) st2
                (by scalar_tac) hsmk hccb1
            have hcsofeq : (chainsOf cs).receive = some (chainOf ch) := by simp [chainsOf, hcsr]
            have hmem := findChains_mem st2 receiving_epoch.val (chainsOf cs) o1_post.symm
            have := hcb1 (receiving_epoch.val, chainsOf cs) hmem (chainOf ch) (Or.inr hcsofeq)
            simpa [chainOf] using this
          have hcntModel : ch.n.val < Model.SparseRatchet.u64Max := by
            rw [Model.SparseRatchet.u64Max_eq]
            rw [Std.U64.max_eq] at hcnt
            exact hcnt
          step with Tacenta.SessionUnitSpqrT1.chain_clone_spec ch
          rcases hadd : r.n.checked_add 1#u64 with _ | expected
          · exfalso
            have hspec := Std.U64.checked_add_bv_spec r.n 1#u64
            rw [hadd, r_post] at hspec
            simp_all
            omega
          simp only
          have expected_post : expected.val = ch.n.val + 1 := by
            have hspec := Std.U64.checked_add_bv_spec r.n 1#u64
            rw [hadd] at hspec
            rw [← r_post]
            exact hspec.2.1
          step*
          · -- A number that is not the chain's next.
            have hne' : ¬ n.val = ch.n.val + 1 := by scalar_tac
            try (intro err herr; injection herr with herr; subst err)
            have hnotmax : ¬ Model.SparseRatchet.u64Max ≤ ch.n.val := by omega
            unfold Model.SparseRatchet.receiveDetailed
            simp [Model.SparseRatchet.maybeAdvanceReceiveDetailed,
              Model.SparseRatchet.maybeAdvanceDetailed, hts, hskipdet, ← o1_post, chainsOf, hcsr,
              chainOf, hnotmax, hne', sparseReceiveRefusalOfReal]
          · -- The chain steps: the receive succeeds, so there is no refusal to name.
            step with kdf_ck_refines hkr hz64 r.ck n
            step with hopt Chain.Insts.CoreCloneClone cs.send
              (fun x _ => Tacenta.SessionUnitSpqrT1.chain_clone_spec x)
            have hchainlen3 := congrArg List.length hself3.chains
            have hchainlen3' := congrArg List.length hself2.chains
            simp only [List.length_map] at hchainlen3 hchainlen3'
            have hroom3 : self3.chains.val.length < Usize.max := by scalar_tac
            step with set_chains_refines hret hret_total hself3 receiving_epoch
              ({ send := o3, receive := some { ck := next, n } } : Chains) hroom3
            intro err herr
            cases herr
  · rw [hts] at o_post
    obtain ⟨key, hokey, hkeyeq, hrefines⟩ := o_post
    rw [hokey]
    intro err herr
    cases herr

set_option maxHeartbeats 1000000 in
/-- **Every refusal of the sparse receive is the model's detailed refusal.**  The branches are those
of `SessionUnitSpqrT3.receive_store_full_refines`: a refused advance is `EpochOutOfOrder` on both sides
(the exhaustion refusal is excluded by `hepoch`, as there), and the rest is the continuation's. -/
theorem spqr_receive_refusal_refines (hkr : SpqrHkdfAgrees)
    (hz96 : ZeroizingRoundTrips96) (hz64 : ZeroizingRoundTrips64) (hret : VecRetainAgrees)
    (hret_total : Tacenta.SessionUnitSpqrT1.VecRetainTotal)
    (hrm : RemoveSkippedAtAgrees) (hz : Tacenta.SessionUnitSpqrT1.ZeroizeTotal)
    (hopt : Tacenta.SessionUnitSpqrT1.OptionCloneTotal)
    {s : State} {m : Model.SparseRatchet.State} (hrel : StateRefines s m)
    (receiving_epoch : Std.U64) (out : Option Output) (n : Std.U64)
    (hepoch : s.epoch.val + 1 < Std.U64.max)
    (hroom : s.chains.val.length + 2 < Usize.max)
    (hcb : ∀ p ∈ s.chains.val, p.1.val + Model.SparseRatchet.epochsKept ≤ Std.U64.max)
    (hsb : ∀ sk ∈ s.skipped.val, sk.epoch.val + Model.SparseRatchet.epochsKept ≤ Std.U64.max)
    (hnewb : ∀ o : Output, out = some o →
      o.key_epoch.val + Model.SparseRatchet.epochsKept ≤ Std.U64.max)
    (hskiproom : s.skipped.val.length + MAX_SKIP.val ≤ Usize.max)
    (hone : (m.skipped.filter (fun x => x.1 == receiving_epoch.val && x.2.1 == n.val)).length ≤ 1)
    (hcounter : ∀ p ∈ s.chains.val, ∀ ch : Chain,
      (p.2.send = some ch ∨ p.2.receive = some ch) → ch.n.val < Std.U64.max) :
    State.receive s receiving_epoch out n ⦃ fun r =>
      ∀ err, r.1 = core.result.Result.Err err →
        Model.SparseRatchet.receiveDetailed m receiving_epoch.val (out.map outputOf) n.val =
          .error (sparseReceiveRefusalOfReal err) ⦄ := by
  unfold State.receive
  step with maybe_advance_refines hkr hz96 hret hret_total hz hrel out hepoch (by scalar_tac) hcb hsb hnewb
  step
  rcases hout : out with _ | o
  · simp only [hout, Option.map_none] at r_post ⊢
    obtain ⟨hrOk, hrel1⟩ := r_post
    rw [hrOk] at cf_post
    simp only [cf_post]
    have hskiplen1 := congrArg List.length hrel1.skipped
    have hskiplen2 := congrArg List.length hrel.skipped
    simp only [List.length_map] at hskiplen1 hskiplen2
    have hchainlen1 := congrArg List.length hrel1.chains
    have hchainlen2 := congrArg List.length hrel.chains
    simp only [List.length_map] at hchainlen1 hchainlen2
    have hskiproom1 : self1.skipped.val.length + MAX_SKIP.val ≤ Usize.max := by scalar_tac
    exact spqr_receive_continuation_refusal_refines hkr hz64 hret hret_total hrm hz hopt hrel1
      receiving_epoch n (by scalar_tac) hskiproom1 hone (chainCounterBounded_of_real hrel hcounter)
  · simp only [hout, Option.map_some] at r_post ⊢
    rcases hadv : Model.SparseRatchet.advance m (outputOf o) with _ | m1
    · -- The advance refused: `EpochOutOfOrder` on both sides.
      rw [hadv] at r_post
      obtain ⟨o', hno, herr, hstate⟩ := r_post
      rw [herr] at cf_post
      simp only [cf_post]
      intro err hres
      simp only [core.convert.FromSame.from] at hres
      cases hres
      have hmepoch : m.epoch + 1 < Model.SparseRatchet.u64Max := by
        rw [← hrel.epoch, Model.SparseRatchet.u64Max_eq]
        simpa [Std.U64.max_eq] using hepoch
      have hkeyepoch : (outputOf o).keyEpoch ≠ m.epoch + 1 := by
        intro heq
        simp [Model.SparseRatchet.advance, heq, hmepoch] at hadv
      have hdetail : Model.SparseRatchet.advanceDetailed m (outputOf o) =
          .error .epochOutOfOrder :=
        (Model.SparseRatchet.advanceDetailed_epoch_iff m (outputOf o)).2 ⟨hmepoch, hkeyepoch⟩
      simp [Model.SparseRatchet.receiveDetailed, Model.SparseRatchet.maybeAdvanceReceiveDetailed,
        Model.SparseRatchet.maybeAdvanceDetailed, hdetail, Model.SparseRatchet.receiveRefusalOfSend,
        sparseReceiveRefusalOfReal]
    · rw [hadv] at r_post
      obtain ⟨hrOk, hrel1⟩ := r_post
      rw [hrOk] at cf_post
      simp only [cf_post]
      have hlen := advance_skipped_len_le m (outputOf o) m1 hadv
      have hclen := advance_chains_len_le m (outputOf o) m1 hadv
      have hskiplen1 := congrArg List.length hrel1.skipped
      have hskiplen2 := congrArg List.length hrel.skipped
      simp only [List.length_map] at hskiplen1 hskiplen2
      have hchainlen1 := congrArg List.length hrel1.chains
      have hchainlen2 := congrArg List.length hrel.chains
      simp only [List.length_map] at hchainlen1 hchainlen2
      have hskiproom1 : self1.skipped.val.length + MAX_SKIP.val ≤ Usize.max := by scalar_tac
      have hmskip := advance_skipped_eq m (outputOf o) m1 hadv
      have hone1 : (m1.skipped.filter
          (fun x => x.1 == receiving_epoch.val && x.2.1 == n.val)).length ≤ 1 := by
        rw [hmskip]
        exact le_trans (List.filter_filter_length_le m.skipped
          (fun x => decide ((outputOf o).keyEpoch < x.1 + Model.SparseRatchet.epochsKept))
          (fun x => x.1 == receiving_epoch.val && x.2.1 == n.val)) hone
      refine Std.WP.spec_mono
        (spqr_receive_continuation_refusal_refines hkr hz64 hret hret_total hrm hz hopt hrel1
          receiving_epoch n (by scalar_tac) hskiproom1 hone1
          (advance_chain_counter_bounded m (outputOf o) m1 hadv
            (chainCounterBounded_of_real hrel hcounter))) ?_
      intro result hresult err herr
      have htail := hresult err herr
      have hadvDetailed : Model.SparseRatchet.advanceDetailed m (outputOf o) = .ok m1 :=
        (Model.SparseRatchet.advanceDetailed_ok_iff m (outputOf o) m1).2 hadv
      simpa [Model.SparseRatchet.receiveDetailed,
        Model.SparseRatchet.maybeAdvanceReceiveDetailed,
        Model.SparseRatchet.maybeAdvanceDetailed, hadvDetailed] using htail

end Sparse



/-! ## The Triple receive -/

section Triple

open tacenta_session_unit.tacenta_triple
open Tacenta.SessionUnitTripleT3

set_option maxHeartbeats 2000000 in
/-- **`TripleReceiveRefusalRefines` holds.**  The branches are those of
`SessionUnitTripleT3.receive_store_full_refines_discharged`: a classical refusal is the model's
classical refusal, and a sparse refusal after a classical success is the model's sparse refusal. -/
theorem triple_receive_refusal_refines : TripleReceiveRefusalRefines := by
  intro hmac hkdf hzr hvr _ hz96 hz64 hret hret_total hrm hzs hopt s m hrel header mh hheader
    dh_out_recv dh_out_send new_dhs_pub output hone hs hevents hepoch hroom hcb hsb hnewb
    hskiproom hone2 hcounter
  have hz : ZeroizeTotal := fun a => hzs _ a
  have hkt : Tacenta.SessionUnitT1.HkdfTotal := hkdf.total
  have counter : ∀ q ∈ s.post_quantum.chains.val, ∀ ch : tacenta_spqr.Chain,
      (q.2.send = some ch ∨ q.2.receive = some ch) → ch.n.val < Std.U64.max := by
    intro q hq ch hch
    have hrelQ := hrel.2
    rw [← hrelQ] at hcounter
    exact hcounter (Tacenta.SessionUnitSpqrT3.chainsEntryOf q)
      (by simpa [spqrAbs] using (List.mem_map.2 ⟨q, hq, rfl⟩))
      (Tacenta.SessionUnitSpqrT3.chainOf ch)
      (by rcases hch with hch | hch <;>
          simp [Tacenta.SessionUnitSpqrT3.chainsEntryOf,
            Tacenta.SessionUnitSpqrT3.chainsOf, hch])
  obtain ⟨hrelC, hrelQ⟩ := hrel
  unfold State.receive State.Insts.CoreCloneClone.clone
  have hsc := Tacenta.SessionUnitTripleT1.ratchet_state_clone_id hopt s.classical
  have hsq := Tacenta.SessionUnitTripleT1.spqr_state_clone_id s.post_quantum
  simp only [hsc, hsq]
  step*
  rw [← hrelQ] at hepoch hroom hcb hsb hone2 hskiproom
  rw [← hrelC] at hone hs hevents
  have hsR : max s.classical.skipped.val.length tacenta_ratchet.MAX_SKIPPED_STORE.val +
      tacenta_ratchet.MAX_SKIP.val ≤ Usize.max := by
    simpa [ratchetAbs, Tacenta.SessionUnitT3.max_skipped_store_agrees,
      Tacenta.SessionUnitT3.max_skip_agrees] using hs
  have honeR : ((ratchetAbs s.classical).skipped.filter
      (Tacenta.SessionUnitT3.matchesHeader mh)).length ≤ 1 := by
    rw [← Tacenta.SessionUnitT3.matchesHeader_eta]; exact hone
  obtain ⟨r, hr, hrPost⟩ := Std.WP.spec_imp_exists
    (Tacenta.SessionUnitT3.receive_refines hmac hkdf hzr hvr s.classical
      (ratchetAbs s.classical) (ratchetAbs_stateR s.classical)
      header.dr mh ⟨hheader.dh, hheader.pn, hheader.n⟩
      dh_out_recv dh_out_send new_dhs_pub honeR hsR hevents)
  have hrRef := ratchet_receive_refusal_refines hmac hkdf hzr hvr
    s.classical (ratchetAbs s.classical) (ratchetAbs_stateR s.classical)
    header.dr mh ⟨hheader.dh, hheader.pn, hheader.n⟩
    dh_out_recv dh_out_send new_dhs_pub honeR hsR
  rw [hr, Std.WP.spec_ok] at hrRef
  simp only [hr]
  step*
  obtain ⟨r1, sr⟩ := r
  rcases r1 with v | e
  · step*
    obtain ⟨m1, hrecvEq, hstateEq⟩ := hrPost v rfl
    rw [hrelC] at hrecvEq
    have hskipR : s.post_quantum.skipped.val.length + tacenta_spqr.MAX_SKIP.val ≤ Usize.max := by
      simpa [spqrAbs, Tacenta.SessionUnitSpqrT3.max_skip_agrees] using hskiproom
    obtain ⟨r1', hr1, hr1Post⟩ := Std.WP.spec_imp_exists
      (Tacenta.SessionUnitSpqrT3.receive_refines hkdf hz96 hz64 hret hret_total hrm hzs hopt
        (spqrAbs_refines s.post_quantum)
        header.epoch output header.pq_n
        hepoch (by simpa [spqrAbs] using hroom)
        (fun p hp => hcb _ (List.mem_map.2 ⟨p, hp, rfl⟩))
        (fun sk hsk => hsb _ (List.mem_map.2 ⟨sk, hsk, rfl⟩))
        hnewb hskipR hone2 counter)
    have hr1Ref := spqr_receive_refusal_refines
      hkdf hz96 hz64 hret hret_total hrm hzs hopt
      (spqrAbs_refines s.post_quantum)
      header.epoch output header.pq_n
      hepoch (by simpa [spqrAbs] using hroom)
      (fun p hp => hcb _ (List.mem_map.2 ⟨p, hp, rfl⟩))
      (fun sk hsk => hsb _ (List.mem_map.2 ⟨sk, hsk, rfl⟩))
      hnewb hskipR hone2 counter
    rw [hr1, Std.WP.spec_ok] at hr1Ref
    simp only [hr1]
    step*
    obtain ⟨r1'', s1⟩ := r1'
    rcases r1'' with v1 | e1
    · -- Both leaves accepted: the receive succeeds, so there is no refusal to name.
      step*
    · step*
      intro realReason hresult
      injection hresult with hreason
      subst realReason
      have hpqDetailed := hr1Ref e1 rfl
      rw [hrelQ] at hpqDetailed
      have hclassDetailed := (Model.Ratchet.receiveDetailed_ok_iff
        m.classical mh (keyOf dh_out_recv) (keyOf dh_out_send)
          (keyOf new_dhs_pub) (m1, keyOf v)).2 hrecvEq
      refine ⟨.postQuantum (sparseReceiveRefusalOfReal e1), rfl, ?_⟩
      exact (Model.Triple.receiveDetailed_post_quantum_iff m
        { dr := mh, epoch := header.epoch.val, pqN := header.pq_n.val }
        (keyOf dh_out_recv) (keyOf dh_out_send) (keyOf new_dhs_pub)
        (output.map spqrOutputOf) _).2
          ⟨m1, keyOf v, hclassDetailed, hpqDetailed⟩
  · step*
    intro realReason hresult
    injection hresult with hreason
    subst realReason
    obtain ⟨reason, hmap, hclassDetailed⟩ := hrRef e rfl
    rw [hrelC] at hclassDetailed
    refine ⟨.classical reason, by simp [tripleReceiveRefusalOfReal, hmap], ?_⟩
    exact (Model.Triple.receiveDetailed_classical_iff m
      { dr := mh, epoch := header.epoch.val, pqN := header.pq_n.val }
      (keyOf dh_out_recv) (keyOf dh_out_send) (keyOf new_dhs_pub)
      (output.map spqrOutputOf) reason).2 hclassDetailed

end Triple

end Tacenta.UnitLifecycleTripleRefusalT3

/-! ## Pins

The refusal refinements, their statements, and the statement of the Triple-level theorem, pinned so
that a change to any of them, or a new dependency, fails the build here. -/

/--
info: 'Tacenta.UnitLifecycleTripleRefusalT3.derive_chain_loop_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kdf.hmac_sha256,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.Pair.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 tacenta_session_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleTripleRefusalT3.derive_chain_loop_ok

/--
info: 'Tacenta.UnitLifecycleTripleRefusalT3.derive_chain_refines_far' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kdf.hmac_sha256,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.Pair.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 tacenta_session_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleTripleRefusalT3.derive_chain_refines_far

/--
info: 'Tacenta.UnitLifecycleTripleRefusalT3.ratchet_skip_refusal_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kdf.hmac_sha256,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.Pair.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.alloc.vec.Vec.pop,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 tacenta_session_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleTripleRefusalT3.ratchet_skip_refusal_refines

/--
info: 'Tacenta.UnitLifecycleTripleRefusalT3.ratchet_receive_tail_refusal_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kdf.hmac_sha256,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.Pair.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.alloc.vec.Vec.pop,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 tacenta_session_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleTripleRefusalT3.ratchet_receive_tail_refusal_refines

/--
info: 'Tacenta.UnitLifecycleTripleRefusalT3.ratchet_receive_refusal_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kdf.hkdf_sha256,
 tacenta_session_unit.tacenta_kdf.hmac_sha256,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.Pair.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.alloc.vec.Vec.pop,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 tacenta_session_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleTripleRefusalT3.ratchet_receive_refusal_refines

/--
info: 'Tacenta.UnitLifecycleTripleRefusalT3.spqr_skip_refusal_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kdf.hkdf_sha256,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.Pair.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.alloc.vec.Vec.capacity,
 tacenta_session_unit.alloc.vec.Vec.pop,
 tacenta_session_unit.core.option.Option.as_mut,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 Tacenta.SessionUnitSpqrT3.chain_label_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.max_skip_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.max_skip_val._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.max_skipped_store_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.protocol_info_agrees._native.native_decide.ax_1_1,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.core.option.Option.Insts.CoreCloneClone.clone]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleTripleRefusalT3.spqr_skip_refusal_refines

/--
info: 'Tacenta.UnitLifecycleTripleRefusalT3.spqr_receive_continuation_refusal_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kdf.hkdf_sha256,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.Pair.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.alloc.vec.Vec.capacity,
 tacenta_session_unit.alloc.vec.Vec.pop,
 tacenta_session_unit.core.option.Option.as_mut,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 Tacenta.SessionUnitSpqrT3.chain_label_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.max_skip_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.max_skip_val._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.max_skipped_store_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.protocol_info_agrees._native.native_decide.ax_1_1,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.core.option.Option.Insts.CoreCloneClone.clone]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleTripleRefusalT3.spqr_receive_continuation_refusal_refines

/--
info: 'Tacenta.UnitLifecycleTripleRefusalT3.spqr_receive_refusal_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kdf.hkdf_sha256,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.Pair.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.alloc.vec.Vec.capacity,
 tacenta_session_unit.alloc.vec.Vec.pop,
 tacenta_session_unit.core.option.Option.as_mut,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 Tacenta.SessionUnitSpqrT3.chain_label_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.max_skip_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.max_skip_val._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.max_skipped_store_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.protocol_info_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.root_label_agrees._native.native_decide.ax_1_1,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.core.option.Option.Insts.CoreCloneClone.clone]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleTripleRefusalT3.spqr_receive_refusal_refines

/--
info: 'Tacenta.UnitLifecycleTripleRefusalT3.triple_receive_refusal_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kdf.hkdf_sha256,
 tacenta_session_unit.tacenta_kdf.hmac_sha256,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.Pair.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.alloc.vec.Vec.capacity,
 tacenta_session_unit.alloc.vec.Vec.pop,
 tacenta_session_unit.core.option.Option.as_mut,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 Tacenta.SessionUnitSpqrT3.chain_label_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.max_skip_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.max_skip_val._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.max_skipped_store_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.protocol_info_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.receive_refines_continuation._native.native_decide.ax_1_29,
 Tacenta.SessionUnitSpqrT3.root_label_agrees._native.native_decide.ax_1_1,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 tacenta_session_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.core.option.Option.Insts.CoreCloneClone.clone]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleTripleRefusalT3.triple_receive_refusal_refines

/--
info: Tacenta.UnitLifecycleTripleRefusalT3.derive_chain_loop_ok : Tacenta.SessionUnitT1.HmacTotal →
  ∀ [inst : Tacenta.SessionUnitT1.DerivedKeysModel] (iter : core.ops.range.Range U32) (start_n : U32)
    (cur : Std.Array U8 32#usize)
    (keys : tacenta_session_unit.zeroize.Zeroizing (alloc.vec.Vec (U32 × Std.Array U8 32#usize))),
    (↑(Tacenta.SessionUnitT1.DerivedKeysModel.contents keys)).length + (↑iter.end - ↑iter.start) ≤ Usize.max →
      ↑start_n + ↑iter.end ≤ U32.max + 1 →
        tacenta_session_unit.tacenta_ratchet.derive_chain_loop iter start_n cur keys ⦃ r =>
          ∃ p, r = core.result.Result.Ok p ⦄
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleTripleRefusalT3.derive_chain_loop_ok

/--
info: Tacenta.UnitLifecycleTripleRefusalT3.derive_chain_refines_far : Tacenta.SessionUnitT3.HmacAgrees →
  ∀ [inst : Tacenta.SessionUnitT1.DerivedKeysModel] (ck : Std.Array U8 32#usize) (start_n count : U32),
    tacenta_session_unit.tacenta_ratchet.derive_chain ck start_n count ⦃ r =>
      match r with
      | core.result.Result.Ok p =>
        (Tacenta.SessionUnitT3.keyOf p.1,
              Tacenta.SessionUnitT3.keysOf (Tacenta.SessionUnitT1.DerivedKeysModel.contents p.2)) =
            Model.State.deriveChain (Tacenta.SessionUnitT3.keyOf ck) ↑start_n ↑count ∧
          (↑(Tacenta.SessionUnitT1.DerivedKeysModel.contents p.2)).length ≤ ↑count
      | core.result.Result.Err e =>
        e = tacenta_session_unit.tacenta_ratchet.RatchetError.ChainExhausted ∧ U32.max < ↑start_n + ↑count ⦄
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleTripleRefusalT3.derive_chain_refines_far

/--
info: Tacenta.UnitLifecycleTripleRefusalT3.ratchet_skip_refusal_refines : Tacenta.SessionUnitT3.HmacAgrees →
  Tacenta.SessionUnitT1.RemoveSkippedAtTotal →
    ∀ [Tacenta.SessionUnitT1.DerivedKeysModel] (s : tacenta_session_unit.tacenta_ratchet.State) (m : Model.State.State),
      Tacenta.SessionUnitT3.StateR s m →
        ∀ (upto : U32),
          (↑s.skipped).length + ↑tacenta_session_unit.tacenta_ratchet.MAX_SKIP ≤ Usize.max →
            tacenta_session_unit.tacenta_ratchet.skip_message_keys s upto ⦃ r =>
              ∀ (e : tacenta_session_unit.tacenta_ratchet.RatchetError),
                r.1 = core.result.Result.Err e →
                  ∃ reason,
                    Tacenta.UnitLifecycleT3.ratchetReceiveRefusalOfReal e = some reason ∧
                      Model.Ratchet.skipMessageKeysDetailed m ↑upto = Except.error reason ⦄
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleTripleRefusalT3.ratchet_skip_refusal_refines

/--
info: Tacenta.UnitLifecycleTripleRefusalT3.ratchet_receive_tail_refusal_refines : Tacenta.SessionUnitT3.HmacAgrees →
  Tacenta.SessionUnitT1.RemoveSkippedAtTotal →
    ∀ [Tacenta.SessionUnitT1.DerivedKeysModel] (st : tacenta_session_unit.tacenta_ratchet.State)
      (mst : Model.State.State),
      Tacenta.SessionUnitT3.StateR st mst →
        ∀ (n : U32),
          (↑st.skipped).length + ↑tacenta_session_unit.tacenta_ratchet.MAX_SKIP ≤ Usize.max →
            (do
                let (r1, state4) ← tacenta_session_unit.tacenta_ratchet.skip_message_keys st n
                match r1 with
                  | core.result.Result.Ok a =>
                    if n < state4.nr then
                      ok (core.result.Result.Err tacenta_session_unit.tacenta_ratchet.RatchetError.OutOfOrder, state4)
                    else
                      match state4.ckr with
                      | none =>
                        ok
                          (core.result.Result.Err tacenta_session_unit.tacenta_ratchet.RatchetError.NoReceivingChain,
                            state4)
                      | some ck => do
                        let o2 ← lift (state4.nr.checked_add 1#u32)
                        match o2 with
                          | none =>
                            ok
                              (core.result.Result.Err tacenta_session_unit.tacenta_ratchet.RatchetError.ChainExhausted,
                                state4)
                          | some next_nr => do
                            let (ck2, mk) ← tacenta_session_unit.tacenta_ratchet.kdf_ck ck
                            let state5 ←
                              tacenta_session_unit.tacenta_ratchet.age_store
                                  { dhs_pub := state4.dhs_pub, dhr_pub := state4.dhr_pub, rk := state4.rk,
                                    cks := state4.cks, ckr := some ck2, ns := state4.ns, nr := next_nr, pn := state4.pn,
                                    skipped := state4.skipped, events := state4.events, labels := state4.labels }
                            ok (core.result.Result.Ok mk, state5)
                  | core.result.Result.Err e => ok (core.result.Result.Err e, state4)) ⦃
              r =>
              ∀ (e : tacenta_session_unit.tacenta_ratchet.RatchetError),
                r.1 = core.result.Result.Err e →
                  ∃ reason,
                    Tacenta.UnitLifecycleT3.ratchetReceiveRefusalOfReal e = some reason ∧
                      (match Model.Ratchet.skipMessageKeysDetailed mst ↑n with
                        | Except.error reason => Except.error reason
                        | Except.ok st2 =>
                          if ↑n < st2.nr then Except.error Model.Ratchet.ReceiveRefusal.outOfOrder
                          else
                            match st2.ckr with
                            | none => Except.error Model.Ratchet.ReceiveRefusal.noReceivingChain
                            | some ck =>
                              if st2.nr < Model.State.u32Max then
                                match Model.State.kdfCk ck with
                                | (ck', mk) =>
                                  Except.ok
                                    (Model.State.ageStore
                                        { dhsPub := st2.dhsPub, dhrPub := st2.dhrPub, rk := st2.rk, cks := st2.cks,
                                          ckr := some ck', ns := st2.ns, nr := st2.nr + 1, pn := st2.pn,
                                          skipped := st2.skipped, events := st2.events, labels := st2.labels },
                                      mk)
                              else Except.error Model.Ratchet.ReceiveRefusal.chainExhausted) =
                        Except.error reason ⦄
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleTripleRefusalT3.ratchet_receive_tail_refusal_refines

/--
info: Tacenta.UnitLifecycleTripleRefusalT3.ratchet_receive_refusal_refines : Tacenta.SessionUnitT3.HmacAgrees →
  Tacenta.SessionUnitT3.HkdfAgrees →
    Tacenta.SessionUnitT3.ZeroizingRoundTrips →
      Tacenta.SessionUnitT1.RemoveSkippedAtTotal →
        ∀ [Tacenta.SessionUnitT1.DerivedKeysModel] (s : tacenta_session_unit.tacenta_ratchet.State)
          (m : Model.State.State),
          Tacenta.SessionUnitT3.StateR s m →
            ∀ (hdr : tacenta_session_unit.tacenta_ratchet.Header) (mh : Model.State.Header),
              Tacenta.SessionUnitT3.HeaderR hdr mh →
                ∀ (dh_out_recv dh_out_send new_dhs_pub : Std.Array U8 32#usize),
                  (List.filter (Tacenta.SessionUnitT3.matchesHeader mh) m.skipped).length ≤ 1 →
                    max (↑s.skipped).length ↑tacenta_session_unit.tacenta_ratchet.MAX_SKIPPED_STORE +
                          ↑tacenta_session_unit.tacenta_ratchet.MAX_SKIP ≤
                        Usize.max →
                      tacenta_session_unit.tacenta_ratchet.receive s hdr dh_out_recv dh_out_send new_dhs_pub ⦃ r =>
                        ∀ (e : tacenta_session_unit.tacenta_ratchet.RatchetError),
                          r.1 = core.result.Result.Err e →
                            ∃ reason,
                              Tacenta.UnitLifecycleT3.ratchetReceiveRefusalOfReal e = some reason ∧
                                Model.Ratchet.receiveDetailed m mh (Tacenta.SessionUnitT3.keyOf dh_out_recv)
                                    (Tacenta.SessionUnitT3.keyOf dh_out_send)
                                    (Tacenta.SessionUnitT3.keyOf new_dhs_pub) =
                                  Except.error reason ⦄
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleTripleRefusalT3.ratchet_receive_refusal_refines

/--
info: Tacenta.UnitLifecycleTripleRefusalT3.spqr_skip_refusal_refines : Tacenta.SessionUnitSpqrT3.SpqrHkdfAgrees →
  Tacenta.SessionUnitSpqrT3.ZeroizingRoundTrips64 →
    Tacenta.SessionUnitSpqrT3.VecRetainAgrees →
      Tacenta.SessionUnitSpqrT1.VecRetainTotal →
        Tacenta.SessionUnitSpqrT1.ZeroizeTotal →
          Tacenta.SessionUnitSpqrT1.OptionCloneTotal →
            ∀ {s : tacenta_session_unit.tacenta_spqr.State} {m : Model.SparseRatchet.State},
              Tacenta.SessionUnitSpqrT3.StateRefines s m →
                ∀ (e upto : U64),
                  (↑s.chains).length < Usize.max →
                    (↑s.skipped).length + ↑tacenta_session_unit.tacenta_spqr.MAX_SKIP ≤ Usize.max →
                      s.skip_message_keys e upto ⦃ r =>
                        ∀ (err : tacenta_session_unit.tacenta_spqr.SpqrError),
                          r.1 = core.result.Result.Err err →
                            Model.SparseRatchet.skipMessageKeysDetailed m ↑e ↑upto =
                              Except.error (Tacenta.UnitLifecycleT3.sparseReceiveRefusalOfReal err) ⦄
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleTripleRefusalT3.spqr_skip_refusal_refines

/--
info: Tacenta.UnitLifecycleTripleRefusalT3.spqr_receive_continuation_refusal_refines : Tacenta.SessionUnitSpqrT3.SpqrHkdfAgrees →
  Tacenta.SessionUnitSpqrT3.ZeroizingRoundTrips64 →
    Tacenta.SessionUnitSpqrT3.VecRetainAgrees →
      Tacenta.SessionUnitSpqrT1.VecRetainTotal →
        Tacenta.SessionUnitSpqrT3.RemoveSkippedAtAgrees →
          Tacenta.SessionUnitSpqrT1.ZeroizeTotal →
            Tacenta.SessionUnitSpqrT1.OptionCloneTotal →
              ∀ {self1 : tacenta_session_unit.tacenta_spqr.State} {m1 : Model.SparseRatchet.State},
                Tacenta.SessionUnitSpqrT3.StateRefines self1 m1 →
                  ∀ (receiving_epoch n : U64),
                    (↑self1.chains).length + 1 < Usize.max →
                      (↑self1.skipped).length + ↑tacenta_session_unit.tacenta_spqr.MAX_SKIP ≤ Usize.max →
                        (List.filter (fun x => x.1 == ↑receiving_epoch && x.2.1 == ↑n) m1.skipped).length ≤ 1 →
                          Tacenta.SessionUnitSpqrT3.ChainCounterBounded m1.chains →
                            (do
                                let (o, self2) ← self1.try_skipped receiving_epoch n
                                match o with
                                  | none => do
                                    let i ← lift (core.num.U64.saturating_sub n 1#u64)
                                    let (r1, self3) ← self2.skip_message_keys receiving_epoch i
                                    let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
                                    match cf1 with
                                      | core.ops.control_flow.ControlFlow.Continue a => do
                                        let o1 ← self3.find_chains receiving_epoch
                                        match o1 with
                                          | none =>
                                            ok
                                              (core.result.Result.Err
                                                  tacenta_session_unit.tacenta_spqr.SpqrError.NoChain,
                                                self3)
                                          | some cs => do
                                            let cs1 ←
                                              tacenta_session_unit.tacenta_spqr.Chains.Insts.CoreCloneClone.clone cs
                                            match cs1.receive with
                                              | none =>
                                                ok
                                                  (core.result.Result.Err
                                                      tacenta_session_unit.tacenta_spqr.SpqrError.ChainRetired,
                                                    self3)
                                              | some ch => do
                                                let ch1 ←
                                                  tacenta_session_unit.tacenta_spqr.Chain.Insts.CoreCloneClone.clone ch
                                                let o2 ← lift (ch1.n.checked_add 1#u64)
                                                match o2 with
                                                  | none =>
                                                    ok
                                                      (core.result.Result.Err
                                                          tacenta_session_unit.tacenta_spqr.SpqrError.ChainExhausted,
                                                        self3)
                                                  | some expected =>
                                                    if (n != expected) = true then
                                                      ok
                                                        (core.result.Result.Err
                                                            tacenta_session_unit.tacenta_spqr.SpqrError.OutOfOrder,
                                                          self3)
                                                    else do
                                                      let (next, mk) ← tacenta_session_unit.tacenta_spqr.kdf_ck ch1.ck n
                                                      let o3 ←
                                                        tacenta_session_unit.core.option.Option.Insts.CoreCloneClone.clone
                                                            tacenta_session_unit.tacenta_spqr.Chain.Insts.CoreCloneClone
                                                            cs1.send
                                                      let self4 ←
                                                        self3.set_chains receiving_epoch
                                                            { send := o3, receive := some { ck := next, n := n } }
                                                      ok (core.result.Result.Ok mk, self4)
                                      | core.ops.control_flow.ControlFlow.Break residual => do
                                        let r2 ←
                                          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                              (Std.Array U8 32#usize)
                                              (core.convert.FromSame tacenta_session_unit.tacenta_spqr.SpqrError)
                                              residual
                                        ok (r2, self3)
                                  | some k => ok (core.result.Result.Ok k, self2)) ⦃
                              r =>
                              ∀ (err : tacenta_session_unit.tacenta_spqr.SpqrError),
                                r.1 = core.result.Result.Err err →
                                  Model.SparseRatchet.receiveDetailed m1 (↑receiving_epoch) none ↑n =
                                    Except.error (Tacenta.UnitLifecycleT3.sparseReceiveRefusalOfReal err) ⦄
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleTripleRefusalT3.spqr_receive_continuation_refusal_refines

/--
info: Tacenta.UnitLifecycleTripleRefusalT3.spqr_receive_refusal_refines : Tacenta.SessionUnitSpqrT3.SpqrHkdfAgrees →
  Tacenta.SessionUnitSpqrT3.ZeroizingRoundTrips96 →
    Tacenta.SessionUnitSpqrT3.ZeroizingRoundTrips64 →
      Tacenta.SessionUnitSpqrT3.VecRetainAgrees →
        Tacenta.SessionUnitSpqrT1.VecRetainTotal →
          Tacenta.SessionUnitSpqrT3.RemoveSkippedAtAgrees →
            Tacenta.SessionUnitSpqrT1.ZeroizeTotal →
              Tacenta.SessionUnitSpqrT1.OptionCloneTotal →
                ∀ {s : tacenta_session_unit.tacenta_spqr.State} {m : Model.SparseRatchet.State},
                  Tacenta.SessionUnitSpqrT3.StateRefines s m →
                    ∀ (receiving_epoch : U64) (out : Option tacenta_session_unit.tacenta_spqr.Output) (n : U64),
                      ↑s.epoch + 1 < U64.max →
                        (↑s.chains).length + 2 < Usize.max →
                          (∀ p ∈ ↑s.chains, ↑p.1 + Model.SparseRatchet.epochsKept ≤ U64.max) →
                            (∀ sk ∈ ↑s.skipped, ↑sk.epoch + Model.SparseRatchet.epochsKept ≤ U64.max) →
                              (∀ (o : tacenta_session_unit.tacenta_spqr.Output),
                                  out = some o → ↑o.key_epoch + Model.SparseRatchet.epochsKept ≤ U64.max) →
                                (↑s.skipped).length + ↑tacenta_session_unit.tacenta_spqr.MAX_SKIP ≤ Usize.max →
                                  (List.filter (fun x => x.1 == ↑receiving_epoch && x.2.1 == ↑n) m.skipped).length ≤ 1 →
                                    (∀ p ∈ ↑s.chains,
                                        ∀ (ch : tacenta_session_unit.tacenta_spqr.Chain),
                                          p.2.send = some ch ∨ p.2.receive = some ch → ↑ch.n < U64.max) →
                                      s.receive receiving_epoch out n ⦃ r =>
                                        ∀ (err : tacenta_session_unit.tacenta_spqr.SpqrError),
                                          r.1 = core.result.Result.Err err →
                                            Model.SparseRatchet.receiveDetailed m (↑receiving_epoch)
                                                (Option.map Tacenta.SessionUnitSpqrT3.outputOf out) ↑n =
                                              Except.error (Tacenta.UnitLifecycleT3.sparseReceiveRefusalOfReal err) ⦄
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleTripleRefusalT3.spqr_receive_refusal_refines

/--
info: Tacenta.UnitLifecycleTripleRefusalT3.triple_receive_refusal_refines : Tacenta.UnitLifecycleTripleRefusalT3.TripleReceiveRefusalRefines
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleTripleRefusalT3.triple_receive_refusal_refines

/--
info: def Tacenta.UnitLifecycleTripleRefusalT3.TripleReceiveRefusalRefines : Prop :=
Tacenta.SessionUnitT3.HmacAgrees →
  Tacenta.SessionUnitT3.HkdfAgrees →
    Tacenta.SessionUnitT3.ZeroizingRoundTrips →
      Tacenta.SessionUnitT1.RemoveSkippedAtTotal →
        ∀ [Tacenta.SessionUnitT1.DerivedKeysModel],
          Tacenta.SessionUnitSpqrT3.ZeroizingRoundTrips96 →
            Tacenta.SessionUnitSpqrT3.ZeroizingRoundTrips64 →
              Tacenta.SessionUnitSpqrT3.VecRetainAgrees →
                Tacenta.SessionUnitSpqrT1.VecRetainTotal →
                  Tacenta.SessionUnitSpqrT3.RemoveSkippedAtAgrees →
                    Tacenta.SessionUnitSpqrT1.ZeroizeTotal →
                      Tacenta.SessionUnitSpqrT1.OptionCloneTotal →
                        ∀ (s : tacenta_session_unit.tacenta_triple.State) (m : Model.Triple.State),
                          Tacenta.SessionUnitTripleT3.StateRefines Tacenta.SessionUnitTripleT3.ratchetAbs
                              Tacenta.SessionUnitTripleT3.spqrAbs s m →
                            ∀ (header : tacenta_session_unit.tacenta_triple.Header) (mh : Model.State.Header),
                              Tacenta.SessionUnitTripleT3.RatchetHeaderR header.dr mh →
                                ∀ (dh_out_recv dh_out_send new_dhs_pub : Std.Array U8 32#usize)
                                  (output : Option tacenta_session_unit.tacenta_spqr.Output),
                                  (List.filter (fun x => x.1 == mh.dh && x.2.1 == mh.n) m.classical.skipped).length ≤
                                      1 →
                                    max m.classical.skipped.length Model.State.maxSkippedStore + Model.State.maxSkip ≤
                                        Usize.max →
                                      m.classical.events + 1 < U32.max →
                                        m.postQuantum.epoch + 1 < U64.max →
                                          m.postQuantum.chains.length + 2 < Usize.max →
                                            (∀ p ∈ m.postQuantum.chains,
                                                p.1 + Model.SparseRatchet.epochsKept ≤ U64.max) →
                                              (∀ sk ∈ m.postQuantum.skipped,
                                                  sk.1 + Model.SparseRatchet.epochsKept ≤ U64.max) →
                                                (∀ (o : tacenta_session_unit.tacenta_spqr.Output),
                                                    output = some o →
                                                      ↑o.key_epoch + Model.SparseRatchet.epochsKept ≤ U64.max) →
                                                  m.postQuantum.skipped.length + Model.SparseRatchet.maxSkip ≤
                                                      Usize.max →
                                                    (List.filter
                                                            (fun x => x.1 == ↑header.epoch && x.2.1 == ↑header.pq_n)
                                                            m.postQuantum.skipped).length ≤
                                                        1 →
                                                      (∀ p ∈ m.postQuantum.chains,
                                                          ∀ (ch : Model.SparseRatchet.Chain),
                                                            p.2.send = some ch ∨ p.2.receive = some ch →
                                                              ch.n < U64.max) →
                                                        s.receive header dh_out_recv dh_out_send new_dhs_pub output ⦃
                                                          result =>
                                                          ∀
                                                            (realReason :
                                                              tacenta_session_unit.tacenta_triple.TripleError),
                                                            result = core.result.Result.Err realReason →
                                                              ∃ modelReason,
                                                                Tacenta.UnitLifecycleT3.tripleReceiveRefusalOfReal
                                                                      realReason =
                                                                    some modelReason ∧
                                                                  Model.Triple.receiveDetailed m
                                                                      { dr := mh, epoch := ↑header.epoch,
                                                                        pqN := ↑header.pq_n }
                                                                      (Tacenta.SessionUnitTripleT3.keyOf dh_out_recv)
                                                                      (Tacenta.SessionUnitTripleT3.keyOf dh_out_send)
                                                                      (Tacenta.SessionUnitTripleT3.keyOf new_dhs_pub)
                                                                      (Option.map
                                                                        Tacenta.SessionUnitTripleT3.spqrOutputOf
                                                                        output) =
                                                                    Except.error modelReason ⦄
-/
#guard_msgs in
#print Tacenta.UnitLifecycleTripleRefusalT3.TripleReceiveRefusalRefines

