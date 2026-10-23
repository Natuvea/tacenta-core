import Translation.UnitLifecycleTripleRefusalT3

/-!
# The Session unit's sparse skip refines the model's detailed skip, refusal kind included

`sparse-pq-ratchet.md`, The store also has a total bound, orders a skip that steps a chain from its counter `c` to
`upto`: refused as `TooManySkipped` when `upto - c` passes `MAX_SKIP`; otherwise the keys stored for the epoch in the
range are deleted on a working copy, and the skip is refused as `SkippedStoreFull` when what remains plus `upto - c`
passes `MAX_SKIPPED_STORE`.  `Model.SparseRatchet.skipMessageKeysDetailed` names the refusal in that order: no chain,
no receiving chain, `tooManySkipped` when `chain.n + maxSkip < upto`, and `skippedStoreFull` otherwise.

Two results about the Session unit's translated `State::skip_message_keys` were already proved, under the same
hypotheses:
* `SessionUnitSpqrT3.skip_message_keys_refines`: where `Model.SparseRatchet.skipMessageKeys` refuses, the code returns
  an error and the state it was given; where it succeeds with `m'`, the code returns `Ok ()` and a state related to
  `m'`.  Its refusal case names no error; its second conjunct says only that a `SkippedStoreFull` result is the model's
  `skippedStoreFull`.
* `UnitLifecycleTripleRefusalT3.spqr_skip_refusal_refines`: every error the code returns is, under the public mapping
  `UnitLifecycleT3.sparseReceiveRefusalOfReal`, the refusal `skipMessageKeysDetailed` returns.

## What this module shows

* `skip_message_keys_refines_detailed` composes the two.  Under their hypotheses, the code's result is related to
  `skipMessageKeysDetailed`: where the model succeeds with `m'`, the code returns `Ok ()` and a state related to `m'`;
  where the model refuses with a reason, the code returns `Err err` with the state it was given, and
  `sparseReceiveRefusalOfReal err` is that reason.  The success case and the state in the refusal case come from the
  first theorem (the detailed model succeeds exactly when `skipMessageKeys` does,
  `Model.SparseRatchet.skipMessageKeysDetailed_ok_iff`); the kind comes from the second.
* `sparseReceiveRefusalOfReal_injective`: the mapping sends different errors to different reasons.

So the kind is fixed in both directions on related states: a refusal the model names is returned by the code as the
one error that maps to it, and an error the code returns is the model's refusal of that kind.  A request that steps
the chain past `MAX_SKIP` is refused as `TooManySkipped` whatever the store holds, and a request within `MAX_SKIP`
that the store bound refuses is refused as `SkippedStoreFull`: that reading of the two cases is from the definition of
`skipMessageKeysDetailed`, not a further theorem here.

## The laws and premises

* No new law and no new premise.  The hypotheses are those of `SessionUnitSpqrT3.skip_message_keys_refines`, which
  `spqr_skip_refusal_refines` takes in the same order: the hash agreement `SpqrHkdfAgrees`, `ZeroizingRoundTrips64`,
  the store agreement `VecRetainAgrees`, the totality records `VecRetainTotal`, `ZeroizeTotal` and `OptionCloneTotal`,
  the state relation, and the two room premises on the chain table and the store.
* `VecRetainAgrees` stays a hypothesis, as in the two theorems composed.
  `UnitSatisfiabilitySpqrSessionLaws.vecRetainAgrees_of_laws` derives it from five laws about opaque constants
  (`Vec::pop`, `Option::as_mut`, `Vec::capacity`, `Vec::zeroize`, `Array::zeroize`), which are assumed and not
  proved of the real functions (register row `SESSION-SPARSE-AGREEMENTS`).

## Non-vacuity

* The premises are exactly those of the two theorems composed, so the corollary holds wherever they do; this module
  exhibits no state of its own.  For a state that meets the Session unit's sparse decoder invariant (which
  `State::from_bytes` checks), `SessionUnitRatchetImportInv.Spqr.inv_gives_chain_room` gives
  `s.chains.val.length + 2 < Usize.max`, which implies `hroom`, and `inv_gives_skip_room` gives `hskiproom` as stated
  here.  The hash agreement, the round trip, `VecRetainAgrees` and the totality records are hypotheses this module
  does not discharge.
* Both refusal kinds are reached by the Rust source on states decoded through the public API, in
  `tacenta-core/tests/sparse_skip_order.rs` (tested only, against the source and not the translation).

## What it does not show

* The leaf statement `Tacenta.SpqrT3.skip_message_keys_refines` and the three-leaf unit's copy are unchanged: they
  still pin the kind in one direction only.  This module is about the Session unit's copy of the code, which is
  generated from the same source.
* It does not show that its hypotheses about the real functions hold: the hash agreement, the `Zeroizing` round
  trip, `VecRetainAgrees` and the three totality records are hypotheses here, as in the theorems it composes.
* It is about one skip, not a sparse `receive`, a sequence of skips, or the session's eviction and retry.
* No state is exhibited here at which the model refuses for each reason, and no vector pins either refusal kind.
* It says nothing about the Rust source as compiled: the runtime counterpart is
  `tacenta-core/tests/sparse_skip_order.rs`, which tests the source and not the translation.
-/

open Aeneas Aeneas.Std Result

namespace Tacenta.UnitLifecycleSparseSkipKindT3

open tacenta_session_unit tacenta_session_unit.tacenta_spqr
open Tacenta.SessionUnitSpqrT3
open Tacenta.UnitLifecycleT3 (sparseReceiveRefusalOfReal)

/-- The public mapping of the sparse ratchet's errors to the model's refusals sends different errors to different
reasons, so an error is fixed by the reason it maps to. -/
theorem sparseReceiveRefusalOfReal_injective : Function.Injective sparseReceiveRefusalOfReal := by
  intro a b h
  cases a <;> cases b <;> simp_all [sparseReceiveRefusalOfReal]

/-- **The Session unit's sparse skip refines the model's detailed skip.**  At related states, where
`Model.SparseRatchet.skipMessageKeysDetailed` succeeds with `m'` the translated skip returns `Ok ()` and a state related
to `m'`; where it refuses with a reason, the skip returns an error that maps to that reason and the state it was
given.  The hypotheses are those of `SessionUnitSpqrT3.skip_message_keys_refines` and
`UnitLifecycleTripleRefusalT3.spqr_skip_refusal_refines`, in their order. -/
theorem skip_message_keys_refines_detailed (hkr : SpqrHkdfAgrees) (hz64 : ZeroizingRoundTrips64)
    (hret : VecRetainAgrees)
    (hret_total : Tacenta.SessionUnitSpqrT1.VecRetainTotal)
    (hz : Tacenta.SessionUnitSpqrT1.ZeroizeTotal)
    (hopt : Tacenta.SessionUnitSpqrT1.OptionCloneTotal)
    {s : State} {m : Model.SparseRatchet.State} (hrel : StateRefines s m) (e upto : Std.U64)
    (hroom : s.chains.val.length < Usize.max)
    (hskiproom : s.skipped.val.length + MAX_SKIP.val ≤ Usize.max) :
    State.skip_message_keys s e upto ⦃ fun r =>
      match Model.SparseRatchet.skipMessageKeysDetailed m e.val upto.val with
      | .ok m' => r.1 = core.result.Result.Ok () ∧ StateRefines r.2 m'
      | .error reason => ∃ err, r.1 = core.result.Result.Err err ∧ r.2 = s ∧
          sparseReceiveRefusalOfReal err = reason ⦄ := by
  have hleaf := Tacenta.SessionUnitSpqrT3.skip_message_keys_refines hkr hz64 hret hret_total hz hopt
    hrel e upto hroom hskiproom
  have hkind := Tacenta.UnitLifecycleTripleRefusalT3.spqr_skip_refusal_refines hkr hz64 hret hret_total
    hz hopt hrel e upto hroom hskiproom
  obtain ⟨r, hr, hpost⟩ := WP.spec_imp_exists hleaf
  obtain ⟨r', hr', hpost'⟩ := WP.spec_imp_exists hkind
  rw [hr] at hr'
  cases hr'
  rw [hr]
  simp only [WP.spec_ok]
  obtain ⟨hmatch, -⟩ := hpost
  cases hd : Model.SparseRatchet.skipMessageKeysDetailed m e.val upto.val with
  | ok m' =>
      have hs : Model.SparseRatchet.skipMessageKeys m e.val upto.val = some m' :=
        (Model.SparseRatchet.skipMessageKeysDetailed_ok_iff m e.val upto.val m').1 hd
      rw [hs] at hmatch
      exact hmatch
  | error reason =>
      cases hs : Model.SparseRatchet.skipMessageKeys m e.val upto.val with
      | some m' =>
          have hok := (Model.SparseRatchet.skipMessageKeysDetailed_ok_iff m e.val upto.val m').2 hs
          rw [hd] at hok
          cases hok
      | none =>
          rw [hs] at hmatch
          obtain ⟨err, herr, hstate⟩ := hmatch
          refine ⟨err, herr, hstate, ?_⟩
          have hreason := hpost' err herr
          rw [hd] at hreason
          injection hreason with hreason
          exact hreason.symm

end Tacenta.UnitLifecycleSparseSkipKindT3

/-! ## Pins

The constants each result depends on, and the statement of each result and definition, held by the
build.  `attest.py` requires every one of them (`REQUIRED_PINS`, `REQUIRED_STATEMENT_PINS`,
`REQUIRED_PRINT_FORM`). -/

/--
info: 'Tacenta.UnitLifecycleSparseSkipKindT3.sparseReceiveRefusalOfReal_injective' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSparseSkipKindT3.sparseReceiveRefusalOfReal_injective

/--
info: 'Tacenta.UnitLifecycleSparseSkipKindT3.skip_message_keys_refines_detailed' depends on axioms: [propext,
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
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.core.option.Option.Insts.CoreCloneClone.clone]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSparseSkipKindT3.skip_message_keys_refines_detailed

set_option pp.deepTerms true
set_option pp.proofs.withType true

/--
info: Tacenta.UnitLifecycleSparseSkipKindT3.sparseReceiveRefusalOfReal_injective : Function.Injective
  Tacenta.UnitLifecycleT3.sparseReceiveRefusalOfReal
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSparseSkipKindT3.sparseReceiveRefusalOfReal_injective

/--
info: Tacenta.UnitLifecycleSparseSkipKindT3.skip_message_keys_refines_detailed : Tacenta.SessionUnitSpqrT3.SpqrHkdfAgrees →
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
                        match Model.SparseRatchet.skipMessageKeysDetailed m ↑e ↑upto with
                        | Except.ok m' => r.1 = core.result.Result.Ok () ∧ Tacenta.SessionUnitSpqrT3.StateRefines r.2 m'
                        | Except.error reason =>
                          ∃ err,
                            r.1 = core.result.Result.Err err ∧
                              r.2 = s ∧ Tacenta.UnitLifecycleT3.sparseReceiveRefusalOfReal err = reason ⦄
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSparseSkipKindT3.skip_message_keys_refines_detailed
