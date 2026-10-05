import Translation.UnitHeadroomSatisfiable

/-!
# A session that passes `Session::invariant` meets the receive and encrypt headroom together

`UnitHeadroomSatisfiable.lean` shows each headroom record is met by a session over fresh states.  A
session that is not a state the crate can hold would make the record satisfiable and the lifecycle
theorem empty for every session a caller can reach.  This module closes that gap in two directions.

## What is shown

* **Implication, for every session** (`invariant_gives_ad_length`, `decryptHeadroom_of_invariant`,
  `encryptHeadroom_iff_of_invariant`).  If `Session::invariant` returns `true`, then the associated data is 66 bytes
  (`structural_invariant` compares it with `identity_ad`, which is two 33-byte encodings), the Triple and Braid
  fields of the receive record hold (`invariant_gives_preconditions`), and so `DecryptRatchetHeadroom` holds
  with nothing left for the caller to supply.  For the encrypt record the session-dependent fields (the chain
  table and the associated data) hold, and what remains is the plaintext bound and the `initial` field.  With no
  pending initial message the `initial` field is `True`; with one, `structural_invariant` ties its ciphertext to
  `kem::ciphertext_len`, an opaque constant no record bounds, so that field stays a hypothesis there.
* **Responder establishment headroom** (`prekey_invariant_gives_establish_headroom`).  If
  `PrekeyStore::invariant` returns `true`, the store's replay-record vector has a free representable
  slot for the authenticated last-resort append.
* **Existence, at the real constants** (`sessionOf_invariant`, `invariant_session_meets_both`).  A session over fresh
  states passes `Session::invariant` and meets `DecryptRatchetHeadroom` and `EncryptHeadroom` (for every plaintext
  its own bound admits), under two assumptions about opaque constants that no record states:
  `ValidKeyShape` (a private key whose public key is canonical and of prime order exists) and `OptionEqU64Shape`
  (`Option::eq` on two `Some` values of `u64` compares them), and under `DhCodecTotal`, which every record carries.
* **The invariant is not a formality** (`emptyChain_headroom`, `epochZero_bounds`, `emptyChainTable_fails_invariant`,
  `epochZero_braid_fails_invariant`, `session_emptyChainTable_fails_invariant`, `session_epochZero_fails_invariant`): a
  Triple state with an empty chain table meets `ReceiveHeadroom`, a Braid at epoch 0 meets `ct1_bounded` and
  `decoders_bounded`, and a session holding either one fails `Session::invariant` (the sparse ratchet's and the Braid's
  own invariants fail already), so a witness that only met the headroom fields would not have shown this.
* **Satisfiability of the new assumptions** (`model_validKeyShape`, `optionEqImpl_shape`,
  `invariant_hypotheses_satisfiable`).  Each is a statement over the opaque constants, bound to the real ones by
  `Iff.rfl`.  `ValidKeyShape` is satisfied by the joint model of `UnitSatisfiabilityJoint.lean` together with the axiom base
  and `HeadroomInhabitants`.  `OptionEqU64Shape` is about a constant the joint model does not interpret (`Interp` has no
  field for `Option::eq`, and no record reaches it), and it is satisfied by `optionEqImpl`, a Lean function with the type
  of `Option::eq` and the definition the standard library gives it.

## The sense

The same as `UnitHeadroomSatisfiable.lean`: a statement at the real constants, under assumptions about the opaque
constants that an interpretation satisfies, so an argument about derivations and not a theorem about the real
primitives.  The assumptions are about the DH primitives and the standard library: that a valid identity key exists
(`ValidKeyShape`), which is checked by the identity-key vectors and not by Lean, and that `Option::eq` behaves.

## What it does not show

* That a send or a receive keeps the invariant.  The lifecycle theorems are single-step.
* That the witness session passes `Session::invariant` with a pending initial message or an established ephemeral
  key: it has neither.  Those arms call `kem::ciphertext_len` and `decode_ec`.
* That the witness is a session the crate can reach by `establish_initiator` or `establish_responder`.
-/

namespace Tacenta.UnitHeadroomInvariant

open Aeneas Aeneas.Std Result
open tacenta_session_unit
open Tacenta.UnitLifecycleT1
open Tacenta.UnitSatisfiabilityJoint
open Tacenta.UnitSatisfiabilityRecords
open Tacenta.UnitHeadroomSatisfiable
open Tacenta.SessionUnitRatchetImportInv

/-! The persistence invariant now records the one-slot condition required by
    the authenticated last-resort append.  Keep this implication at the
    lifecycle boundary so responder establishment does not need a separate
    headroom premise for a restored store. -/
theorem prekey_invariant_gives_establish_headroom
    (store : lifecycle.PrekeyStore)
    (h : lifecycle.PrekeyStore.invariant store = ok true) :
    EstablishResponderHeadroom store := by
  have hlen : store.last_resort_seen.val.length ≤ Usize.max :=
    store.last_resort_seen.property
  have hlt : store.last_resort_seen.val.length < Usize.max := by
    by_contra hnot
    have heq : store.last_resort_seen.val.length = Usize.max := by omega
    have hlen_val : (alloc.vec.Vec.len store.last_resort_seen).val = Usize.max := by
      simp [alloc.vec.Vec.len, heq]
    have hmax_val : (core.num.Usize.MAX).val = Usize.max := by
      simp [core.num.Usize.MAX]
    have hif : alloc.vec.Vec.len store.last_resort_seen = core.num.Usize.MAX := by
      apply UScalar.eq_of_val_eq
      exact hlen_val.trans hmax_val.symm
    have hnottrue : lifecycle.PrekeyStore.invariant store ≠ ok true := by
      simp [lifecycle.PrekeyStore.invariant, hif]
    exact False.elim (hnottrue h)
  exact ⟨by omega⟩

/-! ## Two assumptions about opaque constants -/

/-- A private key whose public key is canonical and of prime order, over an interpretation `I`. -/
def ValidKeyShape (I : Interp) : Prop :=
  ∃ (k : I.PrivateKey) (pkb : I.PublicKeyBytes) (a : Array U8 32#usize),
    I.dhPrivPublicKey k = ok pkb ∧ I.dhPubAsBytes pkb = ok a ∧
    Tacenta.SessionUnitT1.canonicalX25519 a = true ∧ I.dhIsPrimeOrderPublic pkb = ok true

/-- At the real constants, `ValidKeyShape` is the statement about the real functions. -/
theorem validKeyShape_is :
    ValidKeyShape Interp.real ↔
      ∃ (k : tacenta_boundary.dh.PrivateKey) (pkb : tacenta_boundary.dh.PublicKeyBytes)
        (a : Array U8 32#usize),
        tacenta_boundary.dh.PrivateKey.public_key k = ok pkb ∧
        tacenta_boundary.dh.PublicKeyBytes.as_bytes pkb = ok a ∧
        Tacenta.SessionUnitT1.canonicalX25519 a = true ∧
        tacenta_boundary.dh.is_prime_order_public pkb = ok true :=
  Iff.rfl

theorem model_validKeyShape : ValidKeyShape Interp.model :=
  ⟨(), (), zeros32, rfl, rfl, Ratchet.canonical_zeros, rfl⟩

/-- `Option::eq` on two `Some` values of `u64` compares them, for a function `f` standing for it. -/
def OptionEqU64Shape
    (f : {T : Type} → core.cmp.PartialEq T T → Option T → Option T → Result Bool) : Prop :=
  ∀ a b : U64, f core.cmp.PartialEqU64 (some a) (some b) = ok (decide (a = b))

theorem optionEqU64Shape_is :
    OptionEqU64Shape (@core.option.Option.Insts.CoreCmpPartialEqOption.eq) ↔
      ∀ a b : U64, core.option.Option.Insts.CoreCmpPartialEqOption.eq core.cmp.PartialEqU64
        (some a) (some b) = ok (decide (a = b)) :=
  Iff.rfl

/-- What `Option::eq` is: equal when both are `None`, or both are `Some` of equal values. -/
def optionEqImpl {T : Type} (inst : core.cmp.PartialEq T T) :
    Option T → Option T → Result Bool
  | some a, some b => inst.eq a b
  | none, none => ok true
  | _, _ => ok false

theorem optionEqImpl_shape : OptionEqU64Shape (@optionEqImpl) := by
  intro a b
  simp [optionEqImpl, liftFun2, core.cmp.impls.PartialEqU64.eq]

/-! ## Evaluating `Session::structural_invariant` on a session over fresh states -/

theorem canonical_session_eq (k : Array U8 32#usize) :
    Tacenta.SessionUnitSessionT1.canonicalX25519 k = Tacenta.SessionUnitT1.canonicalX25519 k := by
  unfold Tacenta.SessionUnitSessionT1.canonicalX25519 Tacenta.SessionUnitT1.canonicalX25519
  rfl

theorem is_canonical_key_eq (pk : tacenta_boundary.dh.PublicKeyBytes) (a : Array U8 32#usize)
    (h : tacenta_boundary.dh.PublicKeyBytes.as_bytes pk = ok a) :
    is_canonical_key pk = ok (Tacenta.SessionUnitT1.canonicalX25519 a) := by
  unfold is_canonical_key
  rw [h]
  obtain ⟨r, hr, hre⟩ :=
    Std.WP.spec_imp_exists (Tacenta.SessionUnitSessionT1.is_canonical_x25519_spec a)
  simp [hr, hre, canonical_session_eq]

theorem is_valid_identity_key_eq (pk : tacenta_boundary.dh.PublicKeyBytes) (a : Array U8 32#usize)
    (h : tacenta_boundary.dh.PublicKeyBytes.as_bytes pk = ok a)
    (hcan : Tacenta.SessionUnitT1.canonicalX25519 a = true)
    (hprime : tacenta_boundary.dh.is_prime_order_public pk = ok true) :
    is_valid_identity_key pk = ok true := by
  unfold is_valid_identity_key
  rw [is_canonical_key_eq pk a h, hcan]
  simpa using hprime

theorem vec_ne_self (v : alloc.vec.Vec U8) :
    alloc.vec.partial_eq.PartialEqVec.ne core.cmp.PartialEqU8 v v = ok false := by
  unfold alloc.vec.partial_eq.PartialEqVec.ne
  simp only [if_true]
  generalize v.val = l
  induction l with
  | nil => simp [pure]
  | cons x xs ih =>
    simpa [core.cmp.PartialEqU8, liftFun2, core.cmp.impls.PartialEqU8.ne] using ih

theorem array_ne_self (a : Array U8 32#usize) :
    core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8 a a = ok false := by
  obtain ⟨e, he, hiff⟩ := Std.WP.spec_imp_exists (Tacenta.SessionUnitT3.array_ne_val a a)
  rw [he]
  have : e = false := by
    cases e
    · rfl
    · exact absurd rfl (hiff.mp rfl)
  simp [this]

/-- `Session::structural_invariant` of a session over fresh states, with the keys, the associated data and the
`Option::eq` of the invariant given. -/
theorem structural_sessionOf
    (k : tacenta_boundary.dh.PrivateKey) (pkb : tacenta_boundary.dh.PublicKeyBytes)
    (a : Array U8 32#usize)
    (hpub : tacenta_boundary.dh.PrivateKey.public_key k = ok pkb)
    (hbytes : tacenta_boundary.dh.PublicKeyBytes.as_bytes pkb = ok a)
    (hcan : Tacenta.SessionUnitT1.canonicalX25519 a = true)
    (hprime : tacenta_boundary.dh.is_prime_order_public pkb = ok true)
    (hoeq : OptionEqU64Shape (@core.option.Option.Insts.CoreCmpPartialEqOption.eq))
    (ad : alloc.vec.Vec U8) (had : lifecycle.identity_ad pkb pkb = ok ad) :
    lifecycle.Session.structural_invariant (sessionOf k pkb pkb ad a none) = ok true := by
  have hv := is_valid_identity_key_eq pkb a hbytes hcan hprime
  unfold lifecycle.Session.structural_invariant
  simp [sessionOf, hpub, hbytes, tacenta_triple.State.sending_public, freshTriple,
    tacenta_ratchet.State.sending_public, array_ne_self, freshBraid, tacenta_braid.Braid.failed,
    tacenta_braid.Braid.is_initiator, tacenta_braid.State.epoch, lifecycle.Session.is_responder,
    had, vec_ne_self, tacenta_triple.State.direction, tacenta_spqr.State.impl.direction, hv,
    tacenta_braid.Braid.epoch, tacenta_triple.State.epoch, tacenta_spqr.State.impl.epoch,
    tacenta_braid.Braid.state_tag, lift, tacenta_spqr.Direction.Insts.CoreCmpPartialEqDirection.eq]
  have h01 : U64.checked_add 0#u64 1#u64 = some 1#u64 := by decide
  rw [h01, hoeq]
  rfl

theorem freshTriple_invariant (a : Array U8 32#usize)
    (hcan : Tacenta.SessionUnitT1.canonicalX25519 a = true) :
    tacenta_triple.State.invariant (freshTriple a) = ok true := by
  have h1 : tacenta_ratchet.State.invariant (freshTriple a).classical = ok true := by
    rw [Ratchet.invariant_true_iff]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [freshTriple, vecOf, tacenta_ratchet.MAX_SKIPPED_STORE]
    · simp [freshTriple, U32.max_eq]
    · simp [freshTriple, vecOf]
    · simp [freshTriple, vecOf]
    · simp [freshTriple]
    · simpa [freshTriple] using hcan
    · simp [freshTriple]
    · simp [freshTriple, vecOf]
  have h2 : tacenta_spqr.State.invariant (freshTriple a).post_quantum = ok true := by
    rw [Spqr.invariant_true_iff]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [freshTriple, vecOf, tacenta_spqr.MAX_SKIPPED_STORE]
    · simp [freshTriple, vecOf, core.num.U64.saturating_add, UScalar.saturating_add,
        tacenta_spqr.EPOCHS_KEPT, U64.max_eq]
      decide
    · simp [freshTriple, vecOf]
    · simp [freshTriple, vecOf]
    · simp [freshTriple, vecOf]
    · simp [freshTriple, vecOf]
  simp only [freshTriple] at h1 h2
  unfold tacenta_triple.State.invariant
  simp [h1, h2, freshTriple, tacenta_spqr.State.impl.direction,
    tacenta_ratchet.State.started_as_sender]

theorem freshBraid_invariant : tacenta_braid.Braid.invariant freshBraid = ok true := by
  simp [freshBraid, tacenta_braid.Braid.invariant]

/-- **`Session::invariant` returns `true` on a session over fresh states**, given a canonical prime-order key,
the associated data the invariant computes, and `Option::eq` on `u64`. -/
theorem sessionOf_invariant
    (k : tacenta_boundary.dh.PrivateKey) (pkb : tacenta_boundary.dh.PublicKeyBytes)
    (a : Array U8 32#usize)
    (hpub : tacenta_boundary.dh.PrivateKey.public_key k = ok pkb)
    (hbytes : tacenta_boundary.dh.PublicKeyBytes.as_bytes pkb = ok a)
    (hcan : Tacenta.SessionUnitT1.canonicalX25519 a = true)
    (hprime : tacenta_boundary.dh.is_prime_order_public pkb = ok true)
    (hoeq : OptionEqU64Shape (@core.option.Option.Insts.CoreCmpPartialEqOption.eq))
    (ad : alloc.vec.Vec U8) (had : lifecycle.identity_ad pkb pkb = ok ad) :
    lifecycle.Session.invariant (sessionOf k pkb pkb ad a none) = ok true := by
  unfold lifecycle.Session.invariant
  rw [structural_sessionOf k pkb a hpub hbytes hcan hprime hoeq ad had]
  simp only [Aeneas.Std.bind_tc_ok, if_true]
  unfold lifecycle.Session.leaf_invariants
  simp only [sessionOf]
  rw [freshTriple_invariant a hcan]
  simp [freshBraid_invariant]

/-! ## The invariant rejects the states a bare headroom witness could use

A chain table with no entry for the current epoch, and a Braid at epoch 0, satisfy every numeric field of the
receive record and are not states `Session::invariant` accepts.  `freshTriple` has one chain entry and `freshBraid`
sits at epoch 1 because of these two facts. -/

/-- A Triple state whose chain table is empty fails the sparse ratchet's invariant. -/
theorem emptyChainTable_fails_invariant (dhs : Array U8 32#usize) :
    tacenta_spqr.State.invariant
      { (freshTriple dhs).post_quantum with chains := vecOf [] (by simp) } ≠ ok true := by
  intro h
  rw [Spqr.invariant_true_iff] at h
  obtain ⟨q, hq, _⟩ := h.current_present
  simp [vecOf] at hq

/-- A Braid at epoch 0 fails the Braid invariant. -/
theorem epochZero_braid_fails_invariant :
    tacenta_braid.Braid.invariant
      ⟨tacenta_braid.State.KeysUnsampled 0#u64
        ⟨Array.repeat 32#usize 0#u8, Array.repeat 32#usize 0#u8⟩⟩ = ok false := by
  simp [tacenta_braid.Braid.invariant]

/-- A Triple state whose chain table is empty meets `ReceiveHeadroom`, every numeric field of the receive record that
concerns the Triple.  Its sparse ratchet fails the invariant (`emptyChainTable_fails_invariant`). -/
theorem emptyChain_headroom (dhs : Array U8 32#usize) :
    ReceiveHeadroom
      { freshTriple dhs with
        post_quantum := { (freshTriple dhs).post_quantum with chains := vecOf [] (by simp) } } := by
  have h := usize_max_ge
  unfold ReceiveHeadroom freshTriple
  simp [vecOf, tacenta_ratchet.MAX_SKIPPED_STORE, tacenta_ratchet.MAX_SKIP, tacenta_spqr.MAX_SKIP]
  omega

/-- A Braid at epoch 0, in `KeysUnsampled`, meets the two Braid fields of the receive record.  It fails the Braid
invariant (`epochZero_braid_fails_invariant`). -/
theorem epochZero_bounds :
    Tacenta.SessionUnitBraidT1.State.ct1_bounded
        (tacenta_braid.State.KeysUnsampled 0#u64
          ⟨Array.repeat 32#usize 0#u8, Array.repeat 32#usize 0#u8⟩) ∧
    Tacenta.SessionUnitBraidT1.State.decoders_bounded
        (tacenta_braid.State.KeysUnsampled 0#u64
          ⟨Array.repeat 32#usize 0#u8, Array.repeat 32#usize 0#u8⟩) := by
  simp [Tacenta.SessionUnitBraidT1.State.ct1_bounded,
    Tacenta.SessionUnitBraidT1.State.decoders_bounded]

/-- A Triple state that passes `Triple::invariant` has a sparse ratchet that passes the sparse ratchet's invariant. -/
theorem triple_invariant_gives_spqr (t : tacenta_triple.State)
    (h : tacenta_triple.State.invariant t = ok true) :
    tacenta_spqr.State.invariant t.post_quantum = ok true := by
  unfold tacenta_triple.State.invariant at h
  repeat' first
    | (replace h := Tacenta.SessionUnitRatchetImportInv.bind_eq_ok_inv h;
       obtain ⟨_, _, h⟩ := h)
    | split at h
    | simp at h
  all_goals simp_all

/-- **A session whose Triple has an empty chain table does not pass `Session::invariant`.**  The Triple is the one
of `emptyChain_headroom`. -/
theorem session_emptyChainTable_fails_invariant (k pkb a ad) :
    lifecycle.Session.invariant
      { sessionOf k pkb pkb ad a none with
        triple :=
          { freshTriple a with
            post_quantum := { (freshTriple a).post_quantum with chains := vecOf [] (by simp) } } }
      ≠ ok true := by
  intro h
  obtain ⟨ht, _⟩ := leaf_check_gives_leaf_invariants _ (session_invariant_gives_leaf_check _ h)
  exact emptyChainTable_fails_invariant a (triple_invariant_gives_spqr _ ht)

/-- **A session whose Braid is at epoch 0 does not pass `Session::invariant`.**  The Braid is the one of
`epochZero_bounds`. -/
theorem session_epochZero_fails_invariant (k pkb a ad) :
    lifecycle.Session.invariant
      { sessionOf k pkb pkb ad a none with
        braid := ⟨tacenta_braid.State.KeysUnsampled 0#u64
          ⟨Array.repeat 32#usize 0#u8, Array.repeat 32#usize 0#u8⟩⟩ } ≠ ok true := by
  intro h
  obtain ⟨_, hb⟩ := leaf_check_gives_leaf_invariants _ (session_invariant_gives_leaf_check _ h)
  have h0 := epochZero_braid_fails_invariant
  rw [hb] at h0
  simp at h0

/-! ## What `Session::invariant` gives, for every session -/

theorem vec_ne_false_eq (a b : alloc.vec.Vec U8)
    (h : alloc.vec.partial_eq.PartialEqVec.ne core.cmp.PartialEqU8 a b = ok false) :
    a.val = b.val := by
  unfold alloc.vec.partial_eq.PartialEqVec.ne at h
  split at h
  · rename_i hlen
    simp [liftFun2, core.cmp.impls.PartialEqU8.ne] at h
    exact anyM_ne_false _ _ (by simpa [alloc.vec.Vec.length] using hlen) h
  · simp at h
where
  anyM_ne_false (l1 l2 : List U8) (hl : l1.length = l2.length)
      (h : List.anyM (fun x : U8 × U8 => (ok (!decide (x.1.val = x.2.val)) : Result Bool))
        (l1.zip l2) = ok false) : l1 = l2 := by
    induction l1 generalizing l2 with
    | nil => cases l2 <;> simp_all
    | cons x xs ih =>
      cases l2 with
      | nil => simp at hl
      | cons y ys =>
        simp at h
        by_cases hxy : x.val = y.val
        · rw [if_pos hxy] at h
          have := ih ys (by simpa using hl) h
          rw [this, UScalar.eq_of_val_eq hxy]
        · rw [if_neg hxy] at h
          simp [pure] at h

theorem ad_prefix (hdh : DhCodecTotal) (self : lifecycle.Session) (b2 : Bool) (X : Result Bool)
    (h : (do
      let (initiator, responder) ←
        if b2 = true then ok (self.peer_identity_public, self.our_identity_public)
          else ok (self.our_identity_public, self.peer_identity_public)
      let v ← lifecycle.identity_ad initiator responder
      let b3 ← alloc.vec.partial_eq.PartialEqVec.ne core.cmp.PartialEqU8 self.identity_ad v
      if b3 = true then ok false else X) = ok true) :
    self.identity_ad.val.length = 66 := by
  replace h := bind2_eq_ok_inv h
  obtain ⟨i, r, _, h⟩ := h
  replace h := bind_eq_ok_inv h
  obtain ⟨v, hv, h⟩ := h
  replace h := bind_eq_ok_inv h
  obtain ⟨b3, hne, h⟩ := h
  by_cases hb3 : b3 = true
  · rw [if_pos hb3] at h
    cases h
  · have hb3' : b3 = false := by simpa using hb3
    subst hb3'
    have h1 := vec_ne_false_eq _ _ hne
    obtain ⟨v', hv', hlen⟩ := Std.WP.spec_imp_exists (identity_ad_length hdh i r)
    rw [hv] at hv'
    cases hv'
    rw [h1]
    exact hlen

/-- **A session that passes `structural_invariant` holds 66 bytes of associated data.** -/
theorem structural_gives_ad (hdh : DhCodecTotal) (self : lifecycle.Session)
    (h : lifecycle.Session.structural_invariant self = ok true) :
    self.identity_ad.val.length = 66 := by
  unfold lifecycle.Session.structural_invariant at h
  replace h := bind_eq_ok_inv h
  obtain ⟨pkb, _, h⟩ := h
  replace h := bind_eq_ok_inv h
  obtain ⟨a, _, h⟩ := h
  replace h := bind_eq_ok_inv h
  obtain ⟨a1, _, h⟩ := h
  replace h := bind_eq_ok_inv h
  obtain ⟨b, _, h⟩ := h
  by_cases hb : b = true
  · rw [if_pos hb] at h
    cases h
  · rw [if_neg hb] at h
    replace h := bind_eq_ok_inv h
    obtain ⟨b1, _, h⟩ := h
    by_cases hb1 : b1 = true
    · rw [if_pos hb1] at h
      replace h := bind_eq_ok_inv h
      obtain ⟨b2, _, h⟩ := h
      exact ad_prefix hdh self b2 _ h
    · rw [if_neg hb1] at h
      replace h := bind_eq_ok_inv h
      obtain ⟨be, _, h⟩ := h
      replace h := bind_eq_ok_inv h
      obtain ⟨folded, _, h⟩ := h
      replace h := bind_eq_ok_inv h
      obtain ⟨tag, _, h⟩ := h
      replace h := bind_eq_ok_inv h
      obtain ⟨related, _, h⟩ := h
      by_cases hr : related = true
      · rw [if_pos hr] at h
        replace h := bind_eq_ok_inv h
        obtain ⟨b2, _, h⟩ := h
        exact ad_prefix hdh self b2 _ h
      · rw [if_neg hr] at h
        cases h

theorem invariant_gives_ad_length (hdh : DhCodecTotal) (self : lifecycle.Session)
    (h : lifecycle.Session.invariant self = ok true) :
    self.identity_ad.val.length = 66 := by
  unfold lifecycle.Session.invariant at h
  replace h := bind_eq_ok_inv h
  obtain ⟨b, hb, h⟩ := h
  by_cases hbt : b = true
  · subst hbt
    exact structural_gives_ad hdh self hb
  · rw [if_neg hbt] at h
    cases h

/-- **`DecryptRatchetHeadroom` holds of every session that passes `Session::invariant`**, with nothing left
for the caller to supply.  `decrypt_headroom_of_invariant`-style bridge: the record is
`InvariantPreconditions`, the persisted decoder-size fact, and the associated-data bound.  The
decoder-size fact is explicit because the base invariant bridge deliberately does not import the
session-unit preservation package. -/
theorem decryptHeadroom_of_invariant (hdh : DhCodecTotal)
    (hct1 : Tacenta.SessionUnitBraidT1.Ct1LenTotal) (self : lifecycle.Session)
    (hdecoderSize : Tacenta.SessionUnitBraidT1.State.decoders_sized self.braid.state)
    (h : lifecycle.Session.invariant self = ok true) : DecryptRatchetHeadroom self := by
  obtain ⟨h1, h2, h3⟩ := invariant_gives_preconditions hct1 self h
  have hlen := invariant_gives_ad_length hdh self h
  have h4 := usize_max_ge
  exact ⟨h1, h2, h3, hdecoderSize, by omega⟩

/-- **For a session that passes `Session::invariant`, `EncryptHeadroom` is exactly the plaintext bound and the
`initial` field**: the chain table and the associated data are covered. -/
theorem encryptHeadroom_iff_of_invariant (hdh : DhCodecTotal)
    (hct1 : Tacenta.SessionUnitBraidT1.Ct1LenTotal) (self : lifecycle.Session)
    (hdecoderSize : Tacenta.SessionUnitBraidT1.State.decoders_sized self.braid.state)
    (h : lifecycle.Session.invariant self = ok true) (plaintext : Slice U8) :
    EncryptHeadroom self plaintext ↔
      102 + (plaintext.val.length + 48) ≤ Usize.max ∧
      (match self.pending_initial with
        | none => True
        | some p => 33 + 33 + p.kem_ciphertext.val.length +
            (102 + (plaintext.val.length + 48)) + 18 ≤ Usize.max) := by
  obtain ⟨h1, _, _⟩ := invariant_gives_preconditions hct1 self h
  obtain ⟨_, _, _, _, hA⟩ := decryptHeadroom_of_invariant hdh hct1 self hdecoderSize h
  constructor
  · rintro ⟨_, _, h2, h3⟩
    exact ⟨h2, h3⟩
  · rintro ⟨h2, h3⟩
    exact ⟨by have := h1.2.1; omega, hA, h2, h3⟩

/-! ## A session that passes the invariant and meets both records -/

/-- **A session that passes `Session::invariant` meets `DecryptRatchetHeadroom` and, for every plaintext its own
bound admits, `EncryptHeadroom`, at the real constants, given the two assumptions about opaque constants and
`DhCodecTotal`.**  The session has no pending initial message and no established ephemeral key. -/
theorem invariant_session_meets_both (hdh : DhCodecTotal)
    (hv : ValidKeyShape Interp.real)
    (hoeq : OptionEqU64Shape (@core.option.Option.Insts.CoreCmpPartialEqOption.eq)) :
    ∃ self : lifecycle.Session, lifecycle.Session.invariant self = ok true ∧
      self.pending_initial = none ∧ DecryptRatchetHeadroom self ∧
      ∀ plaintext : Slice U8, 102 + (plaintext.val.length + 48) ≤ Usize.max →
        EncryptHeadroom self plaintext := by
  obtain ⟨k, pkb, a, hpub, hbytes, hcan, hprime⟩ := hv
  obtain ⟨ad, had, hlen⟩ := Std.WP.spec_imp_exists (identity_ad_length hdh pkb pkb)
  have hinv := sessionOf_invariant k pkb a hpub hbytes hcan hprime hoeq ad had
  have h4 := usize_max_ge
  refine ⟨sessionOf k pkb pkb ad a none, hinv, rfl, ?_, ?_⟩
  · rw [decryptHeadroom_sessionOf_iff]
    omega
  · intro plaintext hpt
    rw [encryptHeadroom_sessionOf_iff]
    exact ⟨by omega, hpt, trivial⟩

/-- **At the real constants, the base, the two assumptions and the contract records give a session that passes
`Session::invariant` and meets the receive and encrypt headroom together.** -/
theorem invariant_session_of_axiom_base {R : Type} (rc : rand_core_1.RngCore R)
    (h : AxiomBase Interp.real rc) (hv : ValidKeyShape Interp.real)
    (hoeq : OptionEqU64Shape (@core.option.Option.Insts.CoreCmpPartialEqOption.eq)) :
    EncryptContracts rc ∧ DecryptRatchetContracts rc ∧
    ∃ self : lifecycle.Session, lifecycle.Session.invariant self = ok true ∧
      self.pending_initial = none ∧ DecryptRatchetHeadroom self ∧
      ∀ plaintext : Slice U8, 102 + (plaintext.val.length + 48) ≤ Usize.max →
        EncryptHeadroom self plaintext := by
  obtain ⟨he, hd, _, _, _⟩ := records_of_axiom_base rc h
  exact ⟨he, hd, invariant_session_meets_both he.dhCodec hv hoeq⟩

/-- **The joint model satisfies the axiom base, `HeadroomInhabitants` and `ValidKeyShape` together, and
`OptionEqU64Shape` is satisfied by `optionEqImpl`.**  The second conjunct is that existence alone: it does not mention the
base, because the joint model does not interpret `Option::eq` and no record reaches it. -/
theorem invariant_hypotheses_satisfiable :
    (∃ (I : Interp) (R : Type) (rc : rand_core_1.RngCore R),
      AxiomBase I rc ∧ HeadroomInhabitants I ∧ ValidKeyShape I) ∧
    ∃ f : {T : Type} → core.cmp.PartialEq T T → Option T → Option T → Result Bool,
      OptionEqU64Shape f :=
  ⟨⟨Interp.model, Unit, totalRngCore, axiom_base_model, model_headroomInhabitants,
    model_validKeyShape⟩, ⟨@optionEqImpl, optionEqImpl_shape⟩⟩

end Tacenta.UnitHeadroomInvariant

/-! ## Axiom pins

The constants each result depends on, held by the build.  A pin lists the constants that occur in the
statement and the proof; `attest.py` requires every one of them (`REQUIRED_PINS`). -/

/--
info: 'Tacenta.UnitHeadroomInvariant.validKeyShape_is' depends on axioms: [propext,
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
 tacenta_session_unit.tacenta_kem.encapsulate1,
 tacenta_session_unit.tacenta_kem.encapsulate2,
 tacenta_session_unit.tacenta_kem.validate_ek,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.rand_core_1.error.Error,
 tacenta_session_unit.tacenta_boundary.aead.decrypt,
 tacenta_session_unit.tacenta_boundary.aead.encrypt,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.dh.is_prime_order_public,
 tacenta_session_unit.tacenta_boundary.kem.KeyPair,
 tacenta_session_unit.tacenta_boundary.kem.decapsulate,
 tacenta_session_unit.tacenta_boundary.kem.encapsulate,
 tacenta_session_unit.tacenta_boundary.xeddsa.verify,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.generate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.header,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
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
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index]
-/
#guard_msgs in
#print axioms Tacenta.UnitHeadroomInvariant.validKeyShape_is

/--
info: 'Tacenta.UnitHeadroomInvariant.model_validKeyShape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitHeadroomInvariant.model_validKeyShape

/--
info: 'Tacenta.UnitHeadroomInvariant.optionEqU64Shape_is' depends on axioms: [tacenta_session_unit.core.option.Option.Insts.CoreCmpPartialEqOption.eq]
-/
#guard_msgs in
#print axioms Tacenta.UnitHeadroomInvariant.optionEqU64Shape_is

/--
info: 'Tacenta.UnitHeadroomInvariant.optionEqImpl_shape' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Tacenta.UnitHeadroomInvariant.optionEqImpl_shape

/--
info: 'Tacenta.UnitHeadroomInvariant.structural_sessionOf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.dh.is_prime_order_public,
 tacenta_session_unit.tacenta_boundary.kem.ciphertext_len,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 tacenta_session_unit.core.option.Option.Insts.CoreCmpPartialEqOption.eq]
-/
#guard_msgs in
#print axioms Tacenta.UnitHeadroomInvariant.structural_sessionOf

/--
info: 'Tacenta.UnitHeadroomInvariant.freshTriple_invariant' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitHeadroomInvariant.freshTriple_invariant

/--
info: 'Tacenta.UnitHeadroomInvariant.freshBraid_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kem.CT1_LEN,
 tacenta_session_unit.tacenta_kem.CT2_LEN,
 tacenta_session_unit.tacenta_kem.EK_VECTOR_LEN,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.HEADER_LEN,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.tacenta_kem.validate_ek,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.header,
 tacenta_session_unit.core.num.Usize.div_ceil]
-/
#guard_msgs in
#print axioms Tacenta.UnitHeadroomInvariant.freshBraid_invariant

/--
info: 'Tacenta.UnitHeadroomInvariant.sessionOf_invariant' depends on axioms: [propext,
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
#print axioms Tacenta.UnitHeadroomInvariant.sessionOf_invariant

/--
info: 'Tacenta.UnitHeadroomInvariant.emptyChainTable_fails_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitHeadroomInvariant.emptyChainTable_fails_invariant

/--
info: 'Tacenta.UnitHeadroomInvariant.epochZero_braid_fails_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kem.CT1_LEN,
 tacenta_session_unit.tacenta_kem.CT2_LEN,
 tacenta_session_unit.tacenta_kem.EK_VECTOR_LEN,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.HEADER_LEN,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.tacenta_kem.validate_ek,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.header,
 tacenta_session_unit.core.num.Usize.div_ceil]
-/
#guard_msgs in
#print axioms Tacenta.UnitHeadroomInvariant.epochZero_braid_fails_invariant

/--
info: 'Tacenta.UnitHeadroomInvariant.emptyChain_headroom' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitHeadroomInvariant.emptyChain_headroom

/--
info: 'Tacenta.UnitHeadroomInvariant.epochZero_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair]
-/
#guard_msgs in
#print axioms Tacenta.UnitHeadroomInvariant.epochZero_bounds

/--
info: 'Tacenta.UnitHeadroomInvariant.session_emptyChainTable_fails_invariant' depends on axioms: [propext,
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
#print axioms Tacenta.UnitHeadroomInvariant.session_emptyChainTable_fails_invariant

/--
info: 'Tacenta.UnitHeadroomInvariant.session_epochZero_fails_invariant' depends on axioms: [propext,
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
#print axioms Tacenta.UnitHeadroomInvariant.session_epochZero_fails_invariant

/--
info: 'Tacenta.UnitHeadroomInvariant.structural_gives_ad' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.dh.is_prime_order_public,
 tacenta_session_unit.tacenta_boundary.kem.ciphertext_len,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.to_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 tacenta_session_unit.core.option.Option.Insts.CoreCmpPartialEqOption.eq,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq]
-/
#guard_msgs in
#print axioms Tacenta.UnitHeadroomInvariant.structural_gives_ad

/--
info: 'Tacenta.UnitHeadroomInvariant.invariant_gives_ad_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kem.CT1_LEN,
 tacenta_session_unit.tacenta_kem.CT2_LEN,
 tacenta_session_unit.tacenta_kem.EK_VECTOR_LEN,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.HEADER_LEN,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.tacenta_kem.validate_ek,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.dh.is_prime_order_public,
 tacenta_session_unit.tacenta_boundary.kem.ciphertext_len,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.header,
 tacenta_session_unit.core.num.Usize.div_ceil,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.to_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 tacenta_session_unit.core.option.Option.Insts.CoreCmpPartialEqOption.eq,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq]
-/
#guard_msgs in
#print axioms Tacenta.UnitHeadroomInvariant.invariant_gives_ad_length

/--
info: 'Tacenta.UnitHeadroomInvariant.decryptHeadroom_of_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kem.CT1_LEN,
 tacenta_session_unit.tacenta_kem.CT2_LEN,
 tacenta_session_unit.tacenta_kem.EK_VECTOR_LEN,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.HEADER_LEN,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.tacenta_kem.validate_ek,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.dh.is_prime_order_public,
 tacenta_session_unit.tacenta_boundary.kem.ciphertext_len,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.header,
 tacenta_session_unit.core.num.Usize.div_ceil,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.to_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 tacenta_session_unit.core.option.Option.Insts.CoreCmpPartialEqOption.eq,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq]
-/
#guard_msgs in
#print axioms Tacenta.UnitHeadroomInvariant.decryptHeadroom_of_invariant

/--
info: 'Tacenta.UnitHeadroomInvariant.encryptHeadroom_iff_of_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kem.CT1_LEN,
 tacenta_session_unit.tacenta_kem.CT2_LEN,
 tacenta_session_unit.tacenta_kem.EK_VECTOR_LEN,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.HEADER_LEN,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.tacenta_kem.validate_ek,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.dh.is_prime_order_public,
 tacenta_session_unit.tacenta_boundary.kem.ciphertext_len,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.header,
 tacenta_session_unit.core.num.Usize.div_ceil,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.to_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 tacenta_session_unit.core.option.Option.Insts.CoreCmpPartialEqOption.eq,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq]
-/
#guard_msgs in
#print axioms Tacenta.UnitHeadroomInvariant.encryptHeadroom_iff_of_invariant

/--
info: 'Tacenta.UnitHeadroomInvariant.invariant_session_meets_both' depends on axioms: [propext,
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
 tacenta_session_unit.tacenta_kem.encapsulate1,
 tacenta_session_unit.tacenta_kem.encapsulate2,
 tacenta_session_unit.tacenta_kem.validate_ek,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.rand_core_1.error.Error,
 tacenta_session_unit.tacenta_boundary.aead.decrypt,
 tacenta_session_unit.tacenta_boundary.aead.encrypt,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.dh.is_prime_order_public,
 tacenta_session_unit.tacenta_boundary.kem.KeyPair,
 tacenta_session_unit.tacenta_boundary.kem.ciphertext_len,
 tacenta_session_unit.tacenta_boundary.kem.decapsulate,
 tacenta_session_unit.tacenta_boundary.kem.encapsulate,
 tacenta_session_unit.tacenta_boundary.xeddsa.verify,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.generate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.header,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
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
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index]
-/
#guard_msgs in
#print axioms Tacenta.UnitHeadroomInvariant.invariant_session_meets_both

/--
info: 'Tacenta.UnitHeadroomInvariant.invariant_session_of_axiom_base' depends on axioms: [propext,
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
 tacenta_session_unit.tacenta_kem.encapsulate1,
 tacenta_session_unit.tacenta_kem.encapsulate2,
 tacenta_session_unit.tacenta_kem.validate_ek,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.rand_core_1.error.Error,
 tacenta_session_unit.tacenta_boundary.aead.decrypt,
 tacenta_session_unit.tacenta_boundary.aead.encrypt,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.dh.is_prime_order_public,
 tacenta_session_unit.tacenta_boundary.kem.KeyPair,
 tacenta_session_unit.tacenta_boundary.kem.ciphertext_len,
 tacenta_session_unit.tacenta_boundary.kem.decapsulate,
 tacenta_session_unit.tacenta_boundary.kem.encapsulate,
 tacenta_session_unit.tacenta_boundary.xeddsa.verify,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.generate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.header,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
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
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index]
-/
#guard_msgs in
#print axioms Tacenta.UnitHeadroomInvariant.invariant_session_of_axiom_base

/--
info: 'Tacenta.UnitHeadroomInvariant.invariant_hypotheses_satisfiable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitHeadroomInvariant.invariant_hypotheses_satisfiable

/-! ## Statement pins

The axiom pins above hold the constants a result depends on and not what it says.  These hold the
statements of the results the documents cite. -/

/--
info: Tacenta.UnitHeadroomInvariant.invariant_session_meets_both (hdh : Tacenta.UnitLifecycleT1.DhCodecTotal)
  (hv : Tacenta.UnitHeadroomInvariant.ValidKeyShape Tacenta.UnitSatisfiabilityJoint.Interp.real)
  (hoeq :
    Tacenta.UnitHeadroomInvariant.OptionEqU64Shape
      @tacenta_session_unit.core.option.Option.Insts.CoreCmpPartialEqOption.eq) :
  ∃ self,
    self.invariant = Aeneas.Std.Result.ok true ∧
      self.pending_initial = none ∧
        Tacenta.UnitLifecycleT1.DecryptRatchetHeadroom self ∧
          ∀ (plaintext : Aeneas.Std.Slice Aeneas.Std.U8),
            102 + ((↑plaintext).length + 48) ≤ Aeneas.Std.Usize.max →
              Tacenta.UnitLifecycleT1.EncryptHeadroom self plaintext
-/
#guard_msgs in
#check Tacenta.UnitHeadroomInvariant.invariant_session_meets_both

/--
info: Tacenta.UnitHeadroomInvariant.invariant_session_of_axiom_base {R : Type}
  (rc : tacenta_session_unit.rand_core_1.RngCore R)
  (h : Tacenta.UnitSatisfiabilityRecords.AxiomBase Tacenta.UnitSatisfiabilityJoint.Interp.real rc)
  (hv : Tacenta.UnitHeadroomInvariant.ValidKeyShape Tacenta.UnitSatisfiabilityJoint.Interp.real)
  (hoeq :
    Tacenta.UnitHeadroomInvariant.OptionEqU64Shape
      @tacenta_session_unit.core.option.Option.Insts.CoreCmpPartialEqOption.eq) :
  Tacenta.UnitLifecycleT1.EncryptContracts rc ∧
    Tacenta.UnitLifecycleT1.DecryptRatchetContracts rc ∧
      ∃ self,
        self.invariant = Aeneas.Std.Result.ok true ∧
          self.pending_initial = none ∧
            Tacenta.UnitLifecycleT1.DecryptRatchetHeadroom self ∧
              ∀ (plaintext : Aeneas.Std.Slice Aeneas.Std.U8),
                102 + ((↑plaintext).length + 48) ≤ Aeneas.Std.Usize.max →
                  Tacenta.UnitLifecycleT1.EncryptHeadroom self plaintext
-/
#guard_msgs in
#check Tacenta.UnitHeadroomInvariant.invariant_session_of_axiom_base

/--
info: Tacenta.UnitHeadroomInvariant.invariant_hypotheses_satisfiable :
  (∃ I R rc,
      Tacenta.UnitSatisfiabilityRecords.AxiomBase I rc ∧
        Tacenta.UnitHeadroomSatisfiable.HeadroomInhabitants I ∧ Tacenta.UnitHeadroomInvariant.ValidKeyShape I) ∧
    ∃ f, Tacenta.UnitHeadroomInvariant.OptionEqU64Shape fun {T} => f
-/
#guard_msgs in
#check Tacenta.UnitHeadroomInvariant.invariant_hypotheses_satisfiable

/--
info: Tacenta.UnitHeadroomInvariant.decryptHeadroom_of_invariant (hdh : Tacenta.UnitLifecycleT1.DhCodecTotal)
  (hct1 : Tacenta.SessionUnitBraidT1.Ct1LenTotal) (self : tacenta_session_unit.lifecycle.Session)
  (hdecoderSize : Tacenta.SessionUnitBraidT1.State.decoders_sized self.braid.state)
  (h : self.invariant = Aeneas.Std.Result.ok true) : Tacenta.UnitLifecycleT1.DecryptRatchetHeadroom self
-/
#guard_msgs in
#check Tacenta.UnitHeadroomInvariant.decryptHeadroom_of_invariant

/--
info: Tacenta.UnitHeadroomInvariant.encryptHeadroom_iff_of_invariant (hdh : Tacenta.UnitLifecycleT1.DhCodecTotal)
  (hct1 : Tacenta.SessionUnitBraidT1.Ct1LenTotal) (self : tacenta_session_unit.lifecycle.Session)
  (hdecoderSize : Tacenta.SessionUnitBraidT1.State.decoders_sized self.braid.state)
  (h : self.invariant = Aeneas.Std.Result.ok true) (plaintext : Aeneas.Std.Slice Aeneas.Std.U8) :
  Tacenta.UnitLifecycleT1.EncryptHeadroom self plaintext ↔
    102 + ((↑plaintext).length + 48) ≤ Aeneas.Std.Usize.max ∧
      match self.pending_initial with
      | none => True
      | some p => 33 + 33 + (↑p.kem_ciphertext).length + (102 + ((↑plaintext).length + 48)) + 18 ≤ Aeneas.Std.Usize.max
-/
#guard_msgs in
#check Tacenta.UnitHeadroomInvariant.encryptHeadroom_iff_of_invariant

/--
info: Tacenta.UnitHeadroomInvariant.sessionOf_invariant (k : tacenta_session_unit.tacenta_boundary.dh.PrivateKey)
  (pkb : tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes) (a : Aeneas.Std.Array Aeneas.Std.U8 32#usize)
  (hpub : k.public_key = Aeneas.Std.Result.ok pkb) (hbytes : pkb.as_bytes = Aeneas.Std.Result.ok a)
  (hcan : Tacenta.SessionUnitT1.canonicalX25519 a = true)
  (hprime : tacenta_session_unit.tacenta_boundary.dh.is_prime_order_public pkb = Aeneas.Std.Result.ok true)
  (hoeq :
    Tacenta.UnitHeadroomInvariant.OptionEqU64Shape
      @tacenta_session_unit.core.option.Option.Insts.CoreCmpPartialEqOption.eq)
  (ad : Aeneas.Std.alloc.vec.Vec Aeneas.Std.U8)
  (had : tacenta_session_unit.lifecycle.identity_ad pkb pkb = Aeneas.Std.Result.ok ad) :
  (Tacenta.UnitHeadroomSatisfiable.sessionOf k pkb pkb ad a none).invariant = Aeneas.Std.Result.ok true
-/
#guard_msgs in
#check Tacenta.UnitHeadroomInvariant.sessionOf_invariant

/--
info: Tacenta.UnitHeadroomInvariant.emptyChain_headroom (dhs : Aeneas.Std.Array Aeneas.Std.U8 32#usize) :
  Tacenta.UnitLifecycleT1.ReceiveHeadroom
    (have __src := Tacenta.UnitHeadroomSatisfiable.freshTriple dhs;
    { classical := __src.classical,
      post_quantum :=
        have __src := (Tacenta.UnitHeadroomSatisfiable.freshTriple dhs).post_quantum;
        { rk := __src.rk, epoch := __src.epoch, chains := Tacenta.UnitHeadroomSatisfiable.vecOf [] ⋯,
          skipped := __src.skipped, direction := __src.direction } })
-/
#guard_msgs in
#check Tacenta.UnitHeadroomInvariant.emptyChain_headroom

/--
info: Tacenta.UnitHeadroomInvariant.epochZero_bounds :
  Tacenta.SessionUnitBraidT1.State.ct1_bounded
      (tacenta_session_unit.tacenta_braid.State.KeysUnsampled 0#u64
        { root_key := Aeneas.Std.Array.repeat 32#usize 0#u8, mac_key := Aeneas.Std.Array.repeat 32#usize 0#u8 }) ∧
    Tacenta.SessionUnitBraidT1.State.decoders_bounded
      (tacenta_session_unit.tacenta_braid.State.KeysUnsampled 0#u64
        { root_key := Aeneas.Std.Array.repeat 32#usize 0#u8, mac_key := Aeneas.Std.Array.repeat 32#usize 0#u8 })
-/
#guard_msgs in
#check Tacenta.UnitHeadroomInvariant.epochZero_bounds

/--
info: Tacenta.UnitHeadroomInvariant.session_emptyChainTable_fails_invariant
  (k : tacenta_session_unit.tacenta_boundary.dh.PrivateKey)
  (pkb : tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes) (a : Aeneas.Std.Array Aeneas.Std.U8 32#usize)
  (ad : Aeneas.Std.alloc.vec.Vec Aeneas.Std.U8) :
  (have __src := Tacenta.UnitHeadroomSatisfiable.sessionOf k pkb pkb ad a none;
      {
        triple :=
          have __src := Tacenta.UnitHeadroomSatisfiable.freshTriple a;
          { classical := __src.classical,
            post_quantum :=
              have __src := (Tacenta.UnitHeadroomSatisfiable.freshTriple a).post_quantum;
              { rk := __src.rk, epoch := __src.epoch, chains := Tacenta.UnitHeadroomSatisfiable.vecOf [] ⋯,
                skipped := __src.skipped, direction := __src.direction } },
        braid := __src.braid, ratchet_private := __src.ratchet_private, identity_ad := __src.identity_ad,
        our_identity_public := __src.our_identity_public, peer_identity_public := __src.peer_identity_public,
        pending_initial := __src.pending_initial, established_ephemeral := __src.established_ephemeral }).invariant ≠
    Aeneas.Std.Result.ok true
-/
#guard_msgs in
#check Tacenta.UnitHeadroomInvariant.session_emptyChainTable_fails_invariant

/--
info: Tacenta.UnitHeadroomInvariant.session_epochZero_fails_invariant
  (k : tacenta_session_unit.tacenta_boundary.dh.PrivateKey)
  (pkb : tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes) (a : Aeneas.Std.Array Aeneas.Std.U8 32#usize)
  (ad : Aeneas.Std.alloc.vec.Vec Aeneas.Std.U8) :
  (have __src := Tacenta.UnitHeadroomSatisfiable.sessionOf k pkb pkb ad a none;
      { triple := __src.triple,
        braid :=
          {
            state :=
              tacenta_session_unit.tacenta_braid.State.KeysUnsampled 0#u64
                { root_key := Aeneas.Std.Array.repeat 32#usize 0#u8,
                  mac_key := Aeneas.Std.Array.repeat 32#usize 0#u8 } },
        ratchet_private := __src.ratchet_private, identity_ad := __src.identity_ad,
        our_identity_public := __src.our_identity_public, peer_identity_public := __src.peer_identity_public,
        pending_initial := __src.pending_initial, established_ephemeral := __src.established_ephemeral }).invariant ≠
    Aeneas.Std.Result.ok true
-/
#guard_msgs in
#check Tacenta.UnitHeadroomInvariant.session_epochZero_fails_invariant
