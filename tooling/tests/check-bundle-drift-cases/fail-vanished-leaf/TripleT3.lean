-- expect: no `theorem receive_refines_v2` in T3.lean
-- The marker names a theorem the leaf file does not declare -- a leaf
-- renamed without the bundle following.
-- The two bundles as the tree holds them, against the leaf files beside this
-- directory. Everything that follows in a `fail-*` case is one edit away from
-- this file, so a case says exactly what it is about.
namespace Tacenta.TripleT3

def RatchetAgreesFor (α : tacenta_ratchet.State → Model.State.State) : Prop :=
  -- mirrors: nothing -- no leaf theorem proves the derived `clone`
  (∀ s, ∃ r, tacenta_ratchet.State.Insts.CoreCloneClone.clone s = ok r ∧ α r = α s) ∧
  -- mirrors: nothing -- no leaf theorem proves this accessor
  (∀ s, ∃ r, tacenta_ratchet.State.send_count s = ok r ∧ r.val = (α s).ns) ∧
  -- mirrors: Tacenta.T3.init_sender_refines in T3.lean
  (∀ (ec our_pub peer_pub dh_out : Array Std.U8 32#usize) (labels : tacenta_ratchet.LabelSet),
    ∃ r, tacenta_ratchet.init_sender ec our_pub peer_pub dh_out labels = ok r ∧
      α r = Model.Ratchet.initSender (keyOf ec) (keyOf our_pub) (keyOf peer_pub) (keyOf dh_out)
        (ratchetLabelsOf labels)) ∧
  -- mirrors: Tacenta.T3.init_receiver_refines in T3.lean
  (∀ (ec our_pub : Array Std.U8 32#usize) (labels : tacenta_ratchet.LabelSet),
    ∃ r, tacenta_ratchet.init_receiver ec our_pub labels = ok r ∧
      α r = Model.Ratchet.initReceiver (keyOf ec) (keyOf our_pub) (ratchetLabelsOf labels)) ∧
  -- mirrors: Tacenta.T3.send_refines in T3.lean
  (∀ s, ∃ r, tacenta_ratchet.send s = ok r ∧
    (∀ hdr mk, r.1 = core.result.Result.Ok (hdr, mk) →
      ∃ m' mh, Model.Ratchet.send (α s) = some (m', mh, keyOf mk) ∧
        α r.2 = m' ∧ RatchetHeaderR hdr mh) ∧
    (r.1 = core.result.Result.Err tacenta_ratchet.RatchetError.NoSendingChain →
      Model.Ratchet.send (α s) = none)) ∧
  -- mirrors: Tacenta.T3.receive_refines_v2 in T3.lean
  (∀ (s : tacenta_ratchet.State) (hdr : tacenta_ratchet.Header) (mh : Model.State.Header),
    RatchetHeaderR hdr mh →
    ∀ (dh_out_recv dh_out_send new_dhs_pub : Array Std.U8 32#usize),
    ((α s).skipped.filter (fun x => x.1 == mh.dh && x.2.1 == mh.n)).length ≤ 1 →
    max (α s).skipped.length Model.State.maxSkippedStore + Model.State.maxSkip ≤ Usize.max →
    (α s).events + 1 < Std.U32.max →
    ∃ r, tacenta_ratchet.receive s hdr dh_out_recv dh_out_send new_dhs_pub = ok r ∧
      ∀ mk, r.1 = core.result.Result.Ok mk →
        ∃ m', Model.Ratchet.receive (α s) mh (keyOf dh_out_recv) (keyOf dh_out_send)
              (keyOf new_dhs_pub) = some (m', keyOf mk) ∧ α r.2 = m')

def SpqrAgreesFor (β : tacenta_spqr.State → Model.SparseRatchet.State) : Prop :=
  -- mirrors: nothing -- no leaf theorem proves the derived `clone`
  (∀ s, ∃ r, tacenta_spqr.State.Insts.CoreCloneClone.clone s = ok r ∧ β r = β s) ∧
  -- mirrors: Tacenta.SpqrT3.send_refines in SpqrT3.lean
  (∀ (s : tacenta_spqr.State) (e : Std.U64) (out : Option tacenta_spqr.Output),
    (β s).epoch + 1 < Std.U64.max →
    (β s).chains.length + 1 < Usize.max →
    (∀ p ∈ (β s).chains, p.1 + Model.SparseRatchet.epochsKept ≤ Std.U64.max) →
    (∀ sk ∈ (β s).skipped, sk.1 + Model.SparseRatchet.epochsKept ≤ Std.U64.max) →
    (∀ o : tacenta_spqr.Output, out = some o →
      o.key_epoch.val + Model.SparseRatchet.epochsKept ≤ Std.U64.max) →
    (∀ p ∈ (β s).chains, ∀ ch : Model.SparseRatchet.Chain,
      (p.2.send = some ch ∨ p.2.receive = some ch) → ch.n < Std.U64.max) →
    ∃ r, tacenta_spqr.State.send s e out = ok r ∧
      (∀ n mk, r.1 = core.result.Result.Ok (n, mk) →
        ∃ m', Model.SparseRatchet.send (β s) e.val (out.map spqrOutputOf)
            = some (m', n.val, keyOf mk) ∧ β r.2 = m') ∧
      (∀ err, r.1 = core.result.Result.Err err →
        Model.SparseRatchet.send (β s) e.val (out.map spqrOutputOf) = none)) ∧
  -- mirrors: Tacenta.SpqrT3.receive_refines in SpqrT3.lean
  (∀ (s : tacenta_spqr.State) (receiving_epoch : Std.U64) (out : Option tacenta_spqr.Output)
      (n : Std.U64),
    (β s).epoch + 1 < Std.U64.max →
    (β s).chains.length + 2 < Usize.max →
    (∀ p ∈ (β s).chains, p.1 + Model.SparseRatchet.epochsKept ≤ Std.U64.max) →
    (∀ sk ∈ (β s).skipped, sk.1 + Model.SparseRatchet.epochsKept ≤ Std.U64.max) →
    (∀ o : tacenta_spqr.Output, out = some o →
      o.key_epoch.val + Model.SparseRatchet.epochsKept ≤ Std.U64.max) →
    (β s).skipped.length + Model.SparseRatchet.maxSkip ≤ Usize.max →
    ((β s).skipped.filter
      (fun x => x.1 == receiving_epoch.val && x.2.1 == n.val)).length ≤ 1 →
    (∀ p ∈ (β s).chains, ∀ ch : Model.SparseRatchet.Chain,
      (p.2.send = some ch ∨ p.2.receive = some ch) → ch.n < Std.U64.max) →
    ∃ r, tacenta_spqr.State.receive s receiving_epoch out n = ok r ∧
      match Model.SparseRatchet.receive (β s) receiving_epoch.val (out.map spqrOutputOf) n.val with
      | none => ∃ err, r.1 = core.result.Result.Err err
      | some (m', k) => ∃ key, r.1 = core.result.Result.Ok key ∧ keyOf key = k ∧ β r.2 = m')

end Tacenta.TripleT3
