-- A stand-in for `Translation/T3.lean`, cut to the four theorems the
-- classical bundle mirrors plus the two declarations the checker's bridges
-- name. Nothing builds these files and they are not meant to typecheck: they
-- exist so `check-bundle-drift.py` has a second side to compare against, and
-- they live here and not under any `Translation/` path so the real checker
-- never reads them as the repository's own proofs.
namespace Tacenta.T3

theorem max_skipped_store_agrees :
    MAX_SKIPPED_STORE.val = Model.State.maxSkippedStore := by simp

theorem max_skip_agrees : MAX_SKIP.val = Model.State.maxSkip := by simp

theorem matchesHeader_eta (mh : Model.State.Header) :
    (fun x => x.1 == mh.dh && x.2.1 == mh.n) = matchesHeader mh := rfl

theorem init_receiver_refines (sk our_pub : Array Std.U8 32#usize)
    (labels : LabelSet) :
    init_receiver sk our_pub labels ⦃ fun s =>
      StateR s (Model.Ratchet.initReceiver (keyOf sk) (keyOf our_pub)
        (labelsOf labels)) ⦄ := by simp

theorem init_sender_refines (h : HkdfAgrees) (hz : ZeroizingRoundTrips)
    (sk our_pub peer_pub dh_out : Array Std.U8 32#usize) (labels : LabelSet) :
    init_sender sk our_pub peer_pub dh_out labels ⦃ fun s =>
      StateR s (Model.Ratchet.initSender (keyOf sk) (keyOf our_pub)
        (keyOf peer_pub) (keyOf dh_out) (labelsOf labels)) ⦄ := by simp

theorem send_refines (h : HmacAgrees) (s : State) (m : Model.State.State)
    (hR : StateR s m) :
    send s ⦃ fun r =>
      (∀ hdr mk, r.1 = core.result.Result.Ok (hdr, mk) →
        ∃ m' mh, Model.Ratchet.send m = some (m', mh, keyOf mk)
          ∧ StateR r.2 m' ∧ HeaderR hdr mh)
      ∧ (r.1 = core.result.Result.Err RatchetError.NoSendingChain →
          Model.Ratchet.send m = none) ⦄ := by simp

theorem receive_refines (h : HmacAgrees) (hk : HkdfAgrees)
    (hz : ZeroizingRoundTrips) (hrm : Tacenta.T1.VecRemoveTotal)
    [DerivedKeysModel] (s : State) (m : Model.State.State) (hR : StateR s m)
    (hdr : Header) (mh : Model.State.Header) (hH : HeaderR hdr mh)
    (dh_out_recv dh_out_send new_dhs_pub : Array Std.U8 32#usize)
    (hone : (m.skipped.filter (matchesHeader mh)).length ≤ 1)
    (hs : max s.skipped.val.length MAX_SKIPPED_STORE.val + MAX_SKIP.val
            ≤ Usize.max)
    (hroom : s.events.val + 1 < U32.max) :
    receive s hdr dh_out_recv dh_out_send new_dhs_pub ⦃ fun r =>
      ∀ mk, r.1 = core.result.Result.Ok mk →
        ∃ m', Model.Ratchet.receive m mh (keyOf dh_out_recv) (keyOf dh_out_send)
              (keyOf new_dhs_pub) = some (m', keyOf mk)
          ∧ StateR r.2 m' ⦄ := by simp

end Tacenta.T3
