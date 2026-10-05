import Translation.UnitSatisfiabilityRecords

/-!
# The lifecycle headroom records are satisfiable

`EncryptHeadroom`, `DecryptRatchetHeadroom`, `EstablishInitiatorHeadroom` and
`EstablishResponderHeadroom` (`UnitLifecyclePublicT1.lean`) are the conditions on the input of the five
lifecycle T1 theorems that are not contracts about primitives, and `InvariantPreconditions` is what
`invariant_gives_preconditions` concludes from `Session::invariant`.  A theorem whose headroom no input
meets is true and empty, so this module shows that each record is met by some input and, for the
numeric fields, says exactly where the boundary lies.

## What is shown

* Each record is a conjunction of numeric bounds on the length of a vector or of a caller's slice
  and, for the receive side, of facts about the Triple and Braid states.  The two establishment records are
  one bound each: `initiatorHeadroom_iff` and `responderHeadroom_iff` say they are exactly "this vector is not
  of length `Usize.max`".  `decryptHeadroom_sessionOf_iff`, `encryptHeadroom_sessionOf_iff` give the
  exact numeric condition on a session built from fresh Triple and Braid states.
* `freshTriple` and `freshBraid` are closed values of the translated state types (they contain no opaque
  value), and `freshTriple_headroom` and `freshBraid_bounds` show that they meet the Triple and Braid
  fields of the receive records.  The bounds are `MAX_SKIPPED_STORE + MAX_SKIP = 3000` and a one-entry chain table,
  and they hold at both platform widths because `Usize.max` is at least `2^32 - 1` on both
  (`usize_max_ge`, from `Usize.bounds_eq`).
* The witnesses are `sessionOf`, `bundleOf` and `storeOf`.  Each takes values of the opaque types the translated
  structures contain as arguments, and nothing else: `decryptHeadroom_satisfiable`,
  `encryptHeadroom_satisfiable`, `encryptHeadroom_satisfiable_pending`, `initiatorHeadroom_satisfiable`,
  `responderHeadroom_satisfiable`.
* `nonempty_privateKey_of_dhCodec` and `nonempty_publicKey_of_dhCodec`: `DhCodecTotal`, a field of every one of
  the four contract records, gives a value of each opaque key type.  So for a `Session` and a
  `PublishedBundle` the values are not an extra assumption, and `encrypt_headroom_of_contracts`,
  `decrypt_headroom_of_contracts` and `initiator_headroom_of_contracts` say: given the record, the headroom is
  met by some input.
* The records are not true of every input: `initiatorHeadroom_not_trivial`, `responderHeadroom_not_trivial`,
  `decryptHeadroom_not_trivial`, `encryptHeadroom_not_trivial`.  A bound that held of everything would
  satisfy any witness.  The controls hold of the Lean types, whose vector lengths run up to `Usize.max`.  A
  Rust allocation is at most `isize::MAX` bytes, so no real vector has such a length, and every bound on one
  length (all of `ReceiveHeadroom`, the associated-data bound, the plaintext bound, both establishment bounds)
  holds of every real input.  That is by reading and not by a theorem, because the Aeneas `Vec` carries no
  `isize::MAX` bound.  The pending-message arm of `EncryptHeadroom` bounds a sum of two lengths, which that
  limit alone does not settle on a 32-bit target.  The fields that are facts about a state and not about a size
  are `ct1_bounded` and `decoders_bounded`, which `Session::invariant` supplies.

## The sense

The lifecycle types are built from opaque types of the unit: `tacenta_boundary::dh::PrivateKey` and
`PublicKeyBytes` in `Session`, `PublishedBundle` and `PrekeyStore`, and `tacenta_boundary::kem::KeyPair` and
`zeroize::Zeroizing<Vec<(u32, [u8; 32])>>` in `PrekeyStore`.  Lean has no closed value of any of them in the
real environment, and, by reading and not by a theorem here, an interpretation of the unit's declarations in which one is
empty exists, so no theorem here can construct one: every witness takes values of those types as arguments.  A lifecycle theorem is empty in an interpretation in
which its input type is empty, whatever its headroom says.  Three kinds of value are needed:

* `PrivateKey` and `PublicKeyBytes` come from `DhCodecTotal` (above).  This is an assumption only to the extent
  that the contract record is.
* The wrapper around the one-time prekey vector comes from the class `SessionUnitT1.DerivedKeysModel`, which
  `establish_responder_no_panic` takes as an instance argument and the axiom base provides: `Zeroizing::new` returns for every
  vector (`nonempty_derivedZeroizing`).
* `kem.KeyPair` comes from nothing in any record, by reading: `KemDecapsulateTotal` takes a key pair and does not return
  one, and neither `KeyPair::generate` nor `KeyPair::from_bytes` occurs in a record.  `responder_headroom_of_contracts` takes
  one as an argument, and `HeadroomInhabitants` states it as one more assumption over an interpretation `I` of the opaque
  constants, bound to the real type by `Iff.rfl` (`headroomInhabitants_is`) and satisfied by `Interp.model`
  (`model_headroomInhabitants`: `Unit`).

That is the substitution argument of `UnitSatisfiabilityRecords.lean` again, with the inhabitedness of the opaque types in
the base.  The records are satisfiable in the sense that the four contract records are inhabited
(`records_of_axiom_base`, `axiom_base_satisfiable`) and, in the same interpretation, some input meets the headroom
(`headroom_hypotheses_satisfiable`).  It is an argument about derivations and not a theorem inside Lean, and it
says nothing about the real `PrivateKey`: whether the real type has a value is the question `DhCodecTotal`
puts to the real primitive.

## What it does not show

* That a session built here passes `Session::invariant`.  `UnitHeadroomInvariant.lean` does that, under further
  assumptions about the DH primitives and `Option::eq`.
* That a `PrekeyStore` passes `PrekeyStore::invariant`, or that the invariant bounds `last_resort_seen`.
* That `ct1_bounded` holds in the five states that carry an `EncapsState` or `IncrementalKeyPair`: the witnesses
  use `KeysUnsampled`, which carries neither.
* Anything about the Rust: the records are conditions on the translation's input.
-/

namespace Tacenta.UnitHeadroomSatisfiable

open Aeneas Aeneas.Std Result
open tacenta_session_unit
open Tacenta.UnitLifecycleT1
open Tacenta.UnitSatisfiabilityJoint
open Tacenta.UnitSatisfiabilityRecords

/-! ## Width and small values -/

/-- `usize` is at least 32 bits wide on both targets Aeneas models. -/
theorem usize_max_ge : 4294967295 ≤ Usize.max :=
  Tacenta.SessionUnitSessionT1.small_le_usize_max le_rfl

/-- A vector of at most `2^32 - 1` elements.  The length bound holds at both platform widths. -/
def vecOf {α : Type} (l : List α) (h : l.length ≤ 4294967295) : alloc.vec.Vec α :=
  ⟨l, Tacenta.SessionUnitSessionT1.small_le_usize_max h⟩

/-- The plaintext bound of `EncryptHeadroom` at each width: its largest admitted length is `Usize.max - 150`,
which is `2^32 - 151` on a 32-bit target and `2^64 - 151` on a 64-bit target.  Both are non-empty ranges. -/
theorem plaintext_bound_at_widths (n : Nat) :
    (Usize.max = 4294967295 → (102 + (n + 48) ≤ Usize.max ↔ n ≤ 4294967145)) ∧
    (Usize.max = 18446744073709551615 →
      (102 + (n + 48) ≤ Usize.max ↔ n ≤ 18446744073709551465)) :=
  ⟨fun h => by omega, fun h => by omega⟩

/-! ## Fresh states -/

/-- A Triple state with no skipped keys and one chain-table entry, built from concrete values only.
`dhs` is the ratchet's own public key. -/
def freshTriple (dhs : Array U8 32#usize) : tacenta_triple.State :=
  { classical :=
      { dhs_pub := dhs, dhr_pub := none, rk := Array.repeat 32#usize 0#u8,
        cks := some (Array.repeat 32#usize 0#u8), ckr := none,
        ns := 0#u32, nr := 0#u32, pn := 0#u32, skipped := vecOf [] (by simp), events := 0#u32,
        labels := tacenta_ratchet.LabelSet.Tacenta },
    post_quantum :=
      { rk := Array.repeat 32#usize 0#u8, epoch := 0#u64,
        chains := vecOf [(0#u64, { send := none, receive := none })] (by simp),
        skipped := vecOf [] (by simp), direction := tacenta_spqr.Direction.A2b } }

/-- A Braid in the state `KeysUnsampled`, which holds no decoder, no ciphertext and no KEM value. -/
def freshBraid : tacenta_braid.Braid :=
  ⟨tacenta_braid.State.KeysUnsampled 1#u64
    ⟨Array.repeat 32#usize 0#u8, Array.repeat 32#usize 0#u8⟩⟩

theorem freshTriple_headroom (dhs : Array U8 32#usize) : ReceiveHeadroom (freshTriple dhs) := by
  have h := usize_max_ge
  unfold ReceiveHeadroom freshTriple
  simp [vecOf, tacenta_ratchet.MAX_SKIPPED_STORE, tacenta_ratchet.MAX_SKIP, tacenta_spqr.MAX_SKIP]
  omega

theorem freshBraid_bounds :
    Tacenta.SessionUnitBraidT1.State.ct1_bounded freshBraid.state ∧
    Tacenta.SessionUnitBraidT1.State.decoders_bounded freshBraid.state := by
  simp [freshBraid, Tacenta.SessionUnitBraidT1.State.ct1_bounded,
    Tacenta.SessionUnitBraidT1.State.decoders_bounded]

theorem freshBraid_decoder_sized :
    Tacenta.SessionUnitBraidT1.State.decoders_sized freshBraid.state := by
  simp [freshBraid, Tacenta.SessionUnitBraidT1.State.decoders_sized]

/-! ## Sessions -/

/-- A session over fresh Triple and Braid states.  The opaque values are arguments. -/
def sessionOf (sk : tacenta_boundary.dh.PrivateKey) (our peer : tacenta_boundary.dh.PublicKeyBytes)
    (ad : alloc.vec.Vec U8) (dhs : Array U8 32#usize)
    (pending : Option lifecycle.PendingInitial) : lifecycle.Session :=
  { triple := freshTriple dhs, braid := freshBraid, ratchet_private := sk, identity_ad := ad,
    our_identity_public := our, peer_identity_public := peer, pending_initial := pending,
    established_ephemeral := none }

/-- A pending initial message carrying the given ciphertext. -/
def pendingOf (pk : tacenta_boundary.dh.PublicKeyBytes) (ct : alloc.vec.Vec U8) :
    lifecycle.PendingInitial :=
  ⟨pk, ct, 0#u32, 0#u32, 0#u32⟩

/-- **`DecryptRatchetHeadroom` of a session over fresh states is one numeric bound**: the length of the associated
data. -/
theorem decryptHeadroom_sessionOf_iff (sk our peer ad dhs pending) :
    DecryptRatchetHeadroom (sessionOf sk our peer ad dhs pending) ↔
      ad.val.length + 106 ≤ Usize.max := by
  constructor
  · rintro ⟨_, _, _, _, h⟩
    exact h
  · intro h
    exact ⟨freshTriple_headroom dhs, freshBraid_bounds.1, freshBraid_bounds.2,
      freshBraid_decoder_sized, h⟩

theorem invariantPreconditions_sessionOf (sk our peer ad dhs pending) :
    InvariantPreconditions (sessionOf sk our peer ad dhs pending) :=
  ⟨freshTriple_headroom dhs, freshBraid_bounds.1, freshBraid_bounds.2⟩

/-- **`EncryptHeadroom` of a session over fresh states is three numeric bounds**: the associated data, the
plaintext, and (when an initial message is pending) its ciphertext. -/
theorem encryptHeadroom_sessionOf_iff (sk our peer ad dhs pending) (pt : Slice U8) :
    EncryptHeadroom (sessionOf sk our peer ad dhs pending) pt ↔
      ad.val.length + 106 ≤ Usize.max ∧ 102 + (pt.val.length + 48) ≤ Usize.max ∧
      (match pending with
        | none => True
        | some p => 33 + 33 + p.kem_ciphertext.val.length +
            (102 + (pt.val.length + 48)) + 18 ≤ Usize.max) := by
  have h4 := usize_max_ge
  constructor
  · rintro ⟨_, h1, h2, h3⟩
    exact ⟨h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨?_, h1, h2, h3⟩
    simp [sessionOf, freshTriple, vecOf]
    omega

/-! ## Bundles and stores -/

/-- A published bundle whose key-encapsulation prekey is the given vector. -/
def bundleOf (pk : tacenta_boundary.dh.PublicKeyBytes) (kem : alloc.vec.Vec U8) :
    lifecycle.PublishedBundle :=
  { bundle :=
      { identity_key := pk, signed_prekey := pk,
        signed_prekey_signature := Array.repeat 64#usize 0#u8,
        kem_prekey := kem, kem_prekey_signature := Array.repeat 64#usize 0#u8,
        one_time_prekey := none },
    signed_prekey_id := 0#u32, one_time_prekey_id := 0#u32, kem_prekey_id := 0#u32 }

/-- **`EstablishInitiatorHeadroom` is exactly "the prekey vector is not of length `Usize.max`".** -/
theorem initiatorHeadroom_iff (b : lifecycle.PublishedBundle) :
    EstablishInitiatorHeadroom b ↔ b.bundle.kem_prekey.val.length < Usize.max :=
  ⟨fun h => by have := h.kemPrekey; omega, fun h => ⟨by omega⟩⟩

/-- A prekey store whose `last_resort_seen` is the given vector.  The opaque values are arguments. -/
def storeOf (pk : tacenta_boundary.dh.PublicKeyBytes) (kp : tacenta_boundary.kem.KeyPair)
    (z : zeroize.Zeroizing (alloc.vec.Vec (U32 × Array U8 32#usize)))
    (seen : alloc.vec.Vec (U32 × Array U8 32#usize)) : lifecycle.PrekeyStore :=
  { identity_public := pk, signed_prekey_secret := Array.repeat 32#usize 0#u8,
    signed_prekey_id := 0#u32, signed_prekey_sig := Array.repeat 64#usize 0#u8, one_time := z,
    kem := kp, kem_id := 0#u32, kem_sig := Array.repeat 64#usize 0#u8,
    kem_one_time := vecOf [] (by simp), previous_signed_prekey := none, previous_kem := none,
    next_id := 0#u32, last_resort_seen := seen, legacy_last_resort_blocked := vecOf [] (by simp) }

/-- **`EstablishResponderHeadroom` is exactly "`last_resort_seen` is not of length `Usize.max`".** -/
theorem responderHeadroom_iff (s : lifecycle.PrekeyStore) :
    EstablishResponderHeadroom s ↔ s.last_resort_seen.val.length < Usize.max :=
  ⟨fun h => by have := h.lastResortSeen; omega, fun h => ⟨by omega⟩⟩

/-! ## Witnesses, with the opaque values as arguments -/

/-- The receive records are met by a session over fresh states and any associated data of at most `2^32 - 107`
bytes (`2^32 - 107` and not `Usize.max - 106`: the bound holds at both widths). -/
theorem decryptHeadroom_satisfiable (sk : tacenta_boundary.dh.PrivateKey)
    (pk : tacenta_boundary.dh.PublicKeyBytes) (ad : alloc.vec.Vec U8)
    (had : ad.val.length ≤ 4294967189) :
    ∃ self : lifecycle.Session, DecryptRatchetHeadroom self ∧ InvariantPreconditions self := by
  have h4 := usize_max_ge
  exact ⟨sessionOf sk pk pk ad (Array.repeat 32#usize 0#u8) none,
    (decryptHeadroom_sessionOf_iff _ _ _ _ _ _).2 (by omega),
    invariantPreconditions_sessionOf _ _ _ _ _ _⟩

/-- `EncryptHeadroom` is met, with no pending initial message, by a session over fresh states and every plaintext
its own bound admits. -/
theorem encryptHeadroom_satisfiable (sk : tacenta_boundary.dh.PrivateKey)
    (pk : tacenta_boundary.dh.PublicKeyBytes) (plaintext : Slice U8)
    (hpt : 102 + (plaintext.val.length + 48) ≤ Usize.max) :
    ∃ self : lifecycle.Session, self.pending_initial = none ∧ EncryptHeadroom self plaintext := by
  have h4 := usize_max_ge
  refine ⟨sessionOf sk pk pk (vecOf [] (by simp)) (Array.repeat 32#usize 0#u8) none, rfl, ?_⟩
  rw [encryptHeadroom_sessionOf_iff]
  refine ⟨?_, hpt, trivial⟩
  simp [vecOf]
  omega

/-- The `some` arm of the `initial` field is satisfiable too: a session with a pending initial message whose
ciphertext is empty meets `EncryptHeadroom` for every plaintext of at most `Usize.max - 234` bytes. -/
theorem encryptHeadroom_satisfiable_pending (sk : tacenta_boundary.dh.PrivateKey)
    (pk : tacenta_boundary.dh.PublicKeyBytes) (plaintext : Slice U8)
    (hpt : plaintext.val.length + 234 ≤ Usize.max) :
    ∃ self : lifecycle.Session, self.pending_initial.isSome = true ∧
      EncryptHeadroom self plaintext := by
  have h4 := usize_max_ge
  refine ⟨sessionOf sk pk pk (vecOf [] (by simp)) (Array.repeat 32#usize 0#u8)
    (some (pendingOf pk (vecOf [] (by simp)))), rfl, ?_⟩
  rw [encryptHeadroom_sessionOf_iff]
  refine ⟨?_, by omega, ?_⟩
  · simp [vecOf]
    omega
  · simp [pendingOf, vecOf]
    omega

theorem initiatorHeadroom_satisfiable (pk : tacenta_boundary.dh.PublicKeyBytes)
    (kem : alloc.vec.Vec U8) (hkem : kem.val.length ≤ 4294967294) :
    EstablishInitiatorHeadroom (bundleOf pk kem) := by
  have h4 := usize_max_ge
  rw [initiatorHeadroom_iff]
  simp [bundleOf]
  omega

theorem responderHeadroom_satisfiable (pk : tacenta_boundary.dh.PublicKeyBytes)
    (kp : tacenta_boundary.kem.KeyPair)
    (z : zeroize.Zeroizing (alloc.vec.Vec (U32 × Array U8 32#usize)))
    (seen : alloc.vec.Vec (U32 × Array U8 32#usize)) (hseen : seen.val.length ≤ 4294967294) :
    EstablishResponderHeadroom (storeOf pk kp z seen) := by
  have h4 := usize_max_ge
  rw [responderHeadroom_iff]
  simp [storeOf]
  omega

/-! ## The records are not true of every input -/

theorem initiatorHeadroom_not_trivial (pk : tacenta_boundary.dh.PublicKeyBytes) :
    ∃ b : lifecycle.PublishedBundle, ¬ EstablishInitiatorHeadroom b :=
  ⟨bundleOf pk ⟨List.replicate Usize.max 0#u8, by simp⟩, by
    rw [initiatorHeadroom_iff]
    simp [bundleOf]⟩

theorem responderHeadroom_not_trivial (pk : tacenta_boundary.dh.PublicKeyBytes)
    (kp : tacenta_boundary.kem.KeyPair)
    (z : zeroize.Zeroizing (alloc.vec.Vec (U32 × Array U8 32#usize))) :
    ∃ s : lifecycle.PrekeyStore, ¬ EstablishResponderHeadroom s :=
  ⟨storeOf pk kp z ⟨List.replicate Usize.max (0#u32, Array.repeat 32#usize 0#u8), by simp⟩, by
    rw [responderHeadroom_iff]
    simp [storeOf]⟩

theorem decryptHeadroom_not_trivial (sk : tacenta_boundary.dh.PrivateKey)
    (pk : tacenta_boundary.dh.PublicKeyBytes) :
    ∃ self : lifecycle.Session, ¬ DecryptRatchetHeadroom self :=
  ⟨sessionOf sk pk pk ⟨List.replicate Usize.max 0#u8, by simp⟩ (Array.repeat 32#usize 0#u8) none, by
    rw [decryptHeadroom_sessionOf_iff]
    simp⟩

theorem encryptHeadroom_not_trivial (sk : tacenta_boundary.dh.PrivateKey)
    (pk : tacenta_boundary.dh.PublicKeyBytes) :
    ∃ (self : lifecycle.Session) (plaintext : Slice U8), ¬ EncryptHeadroom self plaintext :=
  ⟨sessionOf sk pk pk (vecOf [] (by simp)) (Array.repeat 32#usize 0#u8) none,
    ⟨List.replicate Usize.max 0#u8, by simp⟩, by
      rw [encryptHeadroom_sessionOf_iff]
      simp [vecOf]
      omega⟩

/-! ## The values of the two key types come from the DH codec contract -/

theorem nonempty_privateKey_of_dhCodec (h : DhCodecTotal) :
    Nonempty tacenta_boundary.dh.PrivateKey := by
  obtain ⟨k, _⟩ := h.1 (Array.repeat 32#usize 0#u8)
  exact ⟨k⟩

theorem nonempty_publicKey_of_dhCodec (h : DhCodecTotal) :
    Nonempty tacenta_boundary.dh.PublicKeyBytes := by
  obtain ⟨k, _⟩ := h.2.2.2.1 (Array.repeat 32#usize 0#u8)
  exact ⟨k⟩

/-- **Given `EncryptContracts`, the encrypt headroom is met** by a session with no pending initial message,
for every plaintext its own bound admits.  The two key values come from the record's `dhCodec`. -/
theorem encrypt_headroom_of_contracts {R : Type} {rc : rand_core_1.RngCore R}
    (c : EncryptContracts rc) (plaintext : Slice U8)
    (hpt : 102 + (plaintext.val.length + 48) ≤ Usize.max) :
    ∃ self : lifecycle.Session, self.pending_initial = none ∧ EncryptHeadroom self plaintext := by
  obtain ⟨sk⟩ := nonempty_privateKey_of_dhCodec c.dhCodec
  obtain ⟨pk⟩ := nonempty_publicKey_of_dhCodec c.dhCodec
  exact encryptHeadroom_satisfiable sk pk plaintext hpt

/-- **Given `DecryptRatchetContracts`, the receive headroom is met**, together with `InvariantPreconditions`. -/
theorem decrypt_headroom_of_contracts {R : Type} {rc : rand_core_1.RngCore R}
    (c : DecryptRatchetContracts rc) :
    ∃ self : lifecycle.Session, DecryptRatchetHeadroom self ∧ InvariantPreconditions self := by
  obtain ⟨sk⟩ := nonempty_privateKey_of_dhCodec c.dhCodec
  obtain ⟨pk⟩ := nonempty_publicKey_of_dhCodec c.dhCodec
  exact decryptHeadroom_satisfiable sk pk (vecOf [] (by simp)) (by simp [vecOf])

/-- **Given `EstablishInitiatorContracts`, the initiator headroom is met.** -/
theorem initiator_headroom_of_contracts {R : Type} {rc : rand_core_1.RngCore R}
    (c : EstablishInitiatorContracts rc) :
    ∃ b : lifecycle.PublishedBundle, EstablishInitiatorHeadroom b := by
  obtain ⟨pk⟩ := nonempty_publicKey_of_dhCodec c.dhCodec
  exact ⟨bundleOf pk (vecOf [] (by simp)),
    initiatorHeadroom_satisfiable pk _ (by simp [vecOf])⟩

/-- The class `SessionUnitT1.DerivedKeysModel` gives a value of the wrapper around the one-time prekey vector:
it says `Zeroizing::new` returns, for every vector and every `Zeroize` record. -/
theorem nonempty_derivedZeroizing [Tacenta.SessionUnitT1.DerivedKeysModel] :
    Nonempty (zeroize.Zeroizing (alloc.vec.Vec (U32 × Array U8 32#usize))) := by
  obtain ⟨z, _, _⟩ := Std.WP.spec_imp_exists
    (Tacenta.SessionUnitT1.DerivedKeysModel.new ⟨fun v => ok v⟩ (vecOf [] (by simp)))
  exact ⟨z⟩

/-- **Given `EstablishResponderContracts`, the class `DerivedKeysModel` and a key pair, the responder headroom is
met.**  The public key comes from the record's `dhCodec` and the wrapper from the class, which
`establish_responder_no_panic` takes as an instance argument.  The key pair is an argument
(`HeadroomInhabitants`). -/
theorem responder_headroom_of_contracts {R : Type} {rc : rand_core_1.RngCore R}
    [Tacenta.SessionUnitT1.DerivedKeysModel]
    (c : EstablishResponderContracts rc) (kp : tacenta_boundary.kem.KeyPair) :
    ∃ s : lifecycle.PrekeyStore, EstablishResponderHeadroom s := by
  obtain ⟨pk⟩ := nonempty_publicKey_of_dhCodec c.decrypt.dhCodec
  obtain ⟨z⟩ := nonempty_derivedZeroizing
  exact ⟨storeOf pk kp z (vecOf [] (by simp)),
    responderHeadroom_satisfiable pk kp z _ (by simp [vecOf])⟩

/-! ## The assumption no record states, and the base that satisfies it -/

/-- A value of the key-pair type of `PrekeyStore`, which no contract record produces, over an interpretation `I` of
the unit's opaque constants. -/
def HeadroomInhabitants (I : Interp) : Prop :=
  Nonempty I.KemKeyPair

/-- At the real constants, `HeadroomInhabitants` is the statement about the real type. -/
theorem headroomInhabitants_is :
    HeadroomInhabitants Interp.real ↔ Nonempty tacenta_boundary.kem.KeyPair :=
  Iff.rfl

theorem model_headroomInhabitants : HeadroomInhabitants Interp.model :=
  ⟨()⟩

/-- **The four headroom records are satisfiable, with their contract records, at the real constants.**  Under
the axiom base and `HeadroomInhabitants`, each contract record holds and some input meets the matching
headroom.  The first conjunct of each is `records_of_axiom_base`. -/
theorem headroom_of_axiom_base {R : Type} (rc : rand_core_1.RngCore R)
    (h : AxiomBase Interp.real rc) (hi : HeadroomInhabitants Interp.real) :
    (EncryptContracts rc ∧ ∀ plaintext : Slice U8, 102 + (plaintext.val.length + 48) ≤ Usize.max →
        ∃ self : lifecycle.Session, EncryptHeadroom self plaintext) ∧
    (DecryptRatchetContracts rc ∧ ∃ self : lifecycle.Session, DecryptRatchetHeadroom self) ∧
    (Nonempty (EstablishInitiatorContracts rc) ∧
      ∃ b : lifecycle.PublishedBundle, EstablishInitiatorHeadroom b) ∧
    (Nonempty (EstablishResponderContracts rc) ∧
      ∃ s : lifecycle.PrekeyStore, EstablishResponderHeadroom s) := by
  obtain ⟨he, hd, ⟨hini⟩, ⟨hresp⟩, ⟨hderived⟩⟩ := records_of_axiom_base rc h
  obtain ⟨kp⟩ := hi
  refine ⟨⟨he, fun pt hpt => ?_⟩, ⟨hd, ?_⟩, ⟨⟨hini⟩, initiator_headroom_of_contracts hini⟩,
    ⟨⟨hresp⟩, ?_⟩⟩
  · obtain ⟨self, _, hh⟩ := encrypt_headroom_of_contracts he pt hpt
    exact ⟨self, hh⟩
  · obtain ⟨self, hh, _⟩ := decrypt_headroom_of_contracts hd
    exact ⟨self, hh⟩
  · haveI := hderived
    exact responder_headroom_of_contracts hresp kp

/-- The joint model satisfies the axiom base at a concrete `RngCore`: the construction of
`axiom_base_satisfiable`, named so that other results can refer to it. -/
theorem axiom_base_model : AxiomBase Interp.model (totalRngCore) :=
  { encrypt := model_encryptAxiom totalRngCore_total
    decrypt := model_decryptAxiom (random32_of_rngTotal totalRngCore_total)
    initiator := ⟨model_initiatorAxiom totalRngCore_total
      (random32_of_rngTotal totalRngCore_total)⟩
    responder := ⟨model_responderAxiom (random32_of_rngTotal totalRngCore_total)⟩
    derivedKeys := ⟨model_ZeroizingModel DerivedZ⟩
    laws := model_StdLaws }

/-- **The base and the assumption are jointly satisfiable**: the joint model of `UnitSatisfiabilityJoint.lean`
satisfies both, so the conjunction `headroom_of_axiom_base` takes is not empty in the sense of
`axiom_base_satisfiable`. -/
theorem headroom_hypotheses_satisfiable :
    ∃ (I : Interp) (R : Type) (rc : rand_core_1.RngCore R), AxiomBase I rc ∧ HeadroomInhabitants I :=
  ⟨Interp.model, Unit, totalRngCore, axiom_base_model, model_headroomInhabitants⟩

end Tacenta.UnitHeadroomSatisfiable

/-! ## Axiom pins

The constants each result depends on, held by the build.  A pin lists the constants that occur in the
statement and the proof; `attest.py` requires every one of them (`REQUIRED_PINS`). -/

/--
info: 'Tacenta.UnitHeadroomSatisfiable.usize_max_ge' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitHeadroomSatisfiable.usize_max_ge

/--
info: 'Tacenta.UnitHeadroomSatisfiable.plaintext_bound_at_widths' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitHeadroomSatisfiable.plaintext_bound_at_widths

/--
info: 'Tacenta.UnitHeadroomSatisfiable.freshTriple_headroom' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitHeadroomSatisfiable.freshTriple_headroom

/--
info: 'Tacenta.UnitHeadroomSatisfiable.freshBraid_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair]
-/
#guard_msgs in
#print axioms Tacenta.UnitHeadroomSatisfiable.freshBraid_bounds

/--
info: 'Tacenta.UnitHeadroomSatisfiable.decryptHeadroom_sessionOf_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes]
-/
#guard_msgs in
#print axioms Tacenta.UnitHeadroomSatisfiable.decryptHeadroom_sessionOf_iff

/--
info: 'Tacenta.UnitHeadroomSatisfiable.invariantPreconditions_sessionOf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes]
-/
#guard_msgs in
#print axioms Tacenta.UnitHeadroomSatisfiable.invariantPreconditions_sessionOf

/--
info: 'Tacenta.UnitHeadroomSatisfiable.encryptHeadroom_sessionOf_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes]
-/
#guard_msgs in
#print axioms Tacenta.UnitHeadroomSatisfiable.encryptHeadroom_sessionOf_iff

/--
info: 'Tacenta.UnitHeadroomSatisfiable.initiatorHeadroom_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes]
-/
#guard_msgs in
#print axioms Tacenta.UnitHeadroomSatisfiable.initiatorHeadroom_iff

/--
info: 'Tacenta.UnitHeadroomSatisfiable.responderHeadroom_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.kem.KeyPair]
-/
#guard_msgs in
#print axioms Tacenta.UnitHeadroomSatisfiable.responderHeadroom_iff

/--
info: 'Tacenta.UnitHeadroomSatisfiable.decryptHeadroom_satisfiable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes]
-/
#guard_msgs in
#print axioms Tacenta.UnitHeadroomSatisfiable.decryptHeadroom_satisfiable

/--
info: 'Tacenta.UnitHeadroomSatisfiable.encryptHeadroom_satisfiable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes]
-/
#guard_msgs in
#print axioms Tacenta.UnitHeadroomSatisfiable.encryptHeadroom_satisfiable

/--
info: 'Tacenta.UnitHeadroomSatisfiable.encryptHeadroom_satisfiable_pending' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes]
-/
#guard_msgs in
#print axioms Tacenta.UnitHeadroomSatisfiable.encryptHeadroom_satisfiable_pending

/--
info: 'Tacenta.UnitHeadroomSatisfiable.initiatorHeadroom_satisfiable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes]
-/
#guard_msgs in
#print axioms Tacenta.UnitHeadroomSatisfiable.initiatorHeadroom_satisfiable

/--
info: 'Tacenta.UnitHeadroomSatisfiable.responderHeadroom_satisfiable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.kem.KeyPair]
-/
#guard_msgs in
#print axioms Tacenta.UnitHeadroomSatisfiable.responderHeadroom_satisfiable

/--
info: 'Tacenta.UnitHeadroomSatisfiable.initiatorHeadroom_not_trivial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes]
-/
#guard_msgs in
#print axioms Tacenta.UnitHeadroomSatisfiable.initiatorHeadroom_not_trivial

/--
info: 'Tacenta.UnitHeadroomSatisfiable.responderHeadroom_not_trivial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.kem.KeyPair]
-/
#guard_msgs in
#print axioms Tacenta.UnitHeadroomSatisfiable.responderHeadroom_not_trivial

/--
info: 'Tacenta.UnitHeadroomSatisfiable.decryptHeadroom_not_trivial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes]
-/
#guard_msgs in
#print axioms Tacenta.UnitHeadroomSatisfiable.decryptHeadroom_not_trivial

/--
info: 'Tacenta.UnitHeadroomSatisfiable.encryptHeadroom_not_trivial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes]
-/
#guard_msgs in
#print axioms Tacenta.UnitHeadroomSatisfiable.encryptHeadroom_not_trivial

/--
info: 'Tacenta.UnitHeadroomSatisfiable.nonempty_privateKey_of_dhCodec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.to_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq]
-/
#guard_msgs in
#print axioms Tacenta.UnitHeadroomSatisfiable.nonempty_privateKey_of_dhCodec

/--
info: 'Tacenta.UnitHeadroomSatisfiable.nonempty_publicKey_of_dhCodec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.to_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq]
-/
#guard_msgs in
#print axioms Tacenta.UnitHeadroomSatisfiable.nonempty_publicKey_of_dhCodec

/--
info: 'Tacenta.UnitHeadroomSatisfiable.nonempty_derivedZeroizing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitHeadroomSatisfiable.nonempty_derivedZeroizing

/--
info: 'Tacenta.UnitHeadroomSatisfiable.encrypt_headroom_of_contracts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kdf.hkdf_sha256,
 tacenta_session_unit.tacenta_kdf.hmac_sha256,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.tacenta_kem.encapsulate1,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.rand_core_1.error.Error,
 tacenta_session_unit.tacenta_boundary.aead.encrypt,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.generate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.header,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.TupleABC.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.alloc.vec.Vec.capacity,
 tacenta_session_unit.alloc.vec.Vec.pop,
 tacenta_session_unit.core.num.Usize.div_ceil,
 tacenta_session_unit.core.option.Option.as_mut,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.to_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 tacenta_session_unit.tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.core.option.Option.Insts.CoreCloneClone.clone,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index]
-/
#guard_msgs in
#print axioms Tacenta.UnitHeadroomSatisfiable.encrypt_headroom_of_contracts

/--
info: 'Tacenta.UnitHeadroomSatisfiable.decrypt_headroom_of_contracts' depends on axioms: [propext,
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
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
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
 tacenta_session_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.core.option.Option.Insts.CoreCloneClone.clone,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index]
-/
#guard_msgs in
#print axioms Tacenta.UnitHeadroomSatisfiable.decrypt_headroom_of_contracts

/--
info: 'Tacenta.UnitHeadroomSatisfiable.initiator_headroom_of_contracts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kdf.hkdf_sha256,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.rand_core_1.error.Error,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.dh.is_prime_order_public,
 tacenta_session_unit.tacenta_boundary.kem.encapsulate,
 tacenta_session_unit.tacenta_boundary.xeddsa.verify,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.agree,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.to_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index]
-/
#guard_msgs in
#print axioms Tacenta.UnitHeadroomSatisfiable.initiator_headroom_of_contracts

/--
info: 'Tacenta.UnitHeadroomSatisfiable.responder_headroom_of_contracts' depends on axioms: [propext,
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
 tacenta_session_unit.tacenta_boundary.kem.KeyPair,
 tacenta_session_unit.tacenta_boundary.kem.decapsulate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
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
#print axioms Tacenta.UnitHeadroomSatisfiable.responder_headroom_of_contracts

/--
info: 'Tacenta.UnitHeadroomSatisfiable.headroomInhabitants_is' depends on axioms: [propext,
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
#print axioms Tacenta.UnitHeadroomSatisfiable.headroomInhabitants_is

/--
info: 'Tacenta.UnitHeadroomSatisfiable.model_headroomInhabitants' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitHeadroomSatisfiable.model_headroomInhabitants

/--
info: 'Tacenta.UnitHeadroomSatisfiable.axiom_base_model' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitHeadroomSatisfiable.axiom_base_model

/--
info: 'Tacenta.UnitHeadroomSatisfiable.headroom_of_axiom_base' depends on axioms: [propext,
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
#print axioms Tacenta.UnitHeadroomSatisfiable.headroom_of_axiom_base

/--
info: 'Tacenta.UnitHeadroomSatisfiable.headroom_hypotheses_satisfiable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitHeadroomSatisfiable.headroom_hypotheses_satisfiable

/-! ## Statement pins

The axiom pins above hold the constants a result depends on and not what it says.  These hold the
statements of the results the documents cite. -/

/--
info: Tacenta.UnitHeadroomSatisfiable.headroom_of_axiom_base {R : Type} (rc : tacenta_session_unit.rand_core_1.RngCore R)
  (h : Tacenta.UnitSatisfiabilityRecords.AxiomBase Tacenta.UnitSatisfiabilityJoint.Interp.real rc)
  (hi : Tacenta.UnitHeadroomSatisfiable.HeadroomInhabitants Tacenta.UnitSatisfiabilityJoint.Interp.real) :
  (Tacenta.UnitLifecycleT1.EncryptContracts rc ∧
      ∀ (plaintext : Aeneas.Std.Slice Aeneas.Std.U8),
        102 + ((↑plaintext).length + 48) ≤ Aeneas.Std.Usize.max →
          ∃ self, Tacenta.UnitLifecycleT1.EncryptHeadroom self plaintext) ∧
    (Tacenta.UnitLifecycleT1.DecryptRatchetContracts rc ∧ ∃ self, Tacenta.UnitLifecycleT1.DecryptRatchetHeadroom self) ∧
      (Nonempty (Tacenta.UnitLifecycleT1.EstablishInitiatorContracts rc) ∧
          ∃ b, Tacenta.UnitLifecycleT1.EstablishInitiatorHeadroom b) ∧
        Nonempty (Tacenta.UnitLifecycleT1.EstablishResponderContracts rc) ∧
          ∃ s, Tacenta.UnitLifecycleT1.EstablishResponderHeadroom s
-/
#guard_msgs in
#check Tacenta.UnitHeadroomSatisfiable.headroom_of_axiom_base

/--
info: Tacenta.UnitHeadroomSatisfiable.headroom_hypotheses_satisfiable :
  ∃ I R rc, Tacenta.UnitSatisfiabilityRecords.AxiomBase I rc ∧ Tacenta.UnitHeadroomSatisfiable.HeadroomInhabitants I
-/
#guard_msgs in
#check Tacenta.UnitHeadroomSatisfiable.headroom_hypotheses_satisfiable

/--
info: Tacenta.UnitHeadroomSatisfiable.responder_headroom_of_contracts {R : Type}
  {rc : tacenta_session_unit.rand_core_1.RngCore R} [Tacenta.SessionUnitT1.DerivedKeysModel]
  (c : Tacenta.UnitLifecycleT1.EstablishResponderContracts rc)
  (kp : tacenta_session_unit.tacenta_boundary.kem.KeyPair) : ∃ s, Tacenta.UnitLifecycleT1.EstablishResponderHeadroom s
-/
#guard_msgs in
#check Tacenta.UnitHeadroomSatisfiable.responder_headroom_of_contracts

/--
info: Tacenta.UnitHeadroomSatisfiable.encrypt_headroom_of_contracts {R : Type}
  {rc : tacenta_session_unit.rand_core_1.RngCore R} (c : Tacenta.UnitLifecycleT1.EncryptContracts rc)
  (plaintext : Aeneas.Std.Slice Aeneas.Std.U8) (hpt : 102 + ((↑plaintext).length + 48) ≤ Aeneas.Std.Usize.max) :
  ∃ self, self.pending_initial = none ∧ Tacenta.UnitLifecycleT1.EncryptHeadroom self plaintext
-/
#guard_msgs in
#check Tacenta.UnitHeadroomSatisfiable.encrypt_headroom_of_contracts

/--
info: Tacenta.UnitHeadroomSatisfiable.decrypt_headroom_of_contracts {R : Type}
  {rc : tacenta_session_unit.rand_core_1.RngCore R} (c : Tacenta.UnitLifecycleT1.DecryptRatchetContracts rc) :
  ∃ self, Tacenta.UnitLifecycleT1.DecryptRatchetHeadroom self ∧ Tacenta.UnitLifecycleT1.InvariantPreconditions self
-/
#guard_msgs in
#check Tacenta.UnitHeadroomSatisfiable.decrypt_headroom_of_contracts

/--
info: Tacenta.UnitHeadroomSatisfiable.initiator_headroom_of_contracts {R : Type}
  {rc : tacenta_session_unit.rand_core_1.RngCore R} (c : Tacenta.UnitLifecycleT1.EstablishInitiatorContracts rc) :
  ∃ b, Tacenta.UnitLifecycleT1.EstablishInitiatorHeadroom b
-/
#guard_msgs in
#check Tacenta.UnitHeadroomSatisfiable.initiator_headroom_of_contracts

/--
info: Tacenta.UnitHeadroomSatisfiable.initiatorHeadroom_iff (b : tacenta_session_unit.lifecycle.PublishedBundle) :
  Tacenta.UnitLifecycleT1.EstablishInitiatorHeadroom b ↔ (↑b.bundle.kem_prekey).length < Aeneas.Std.Usize.max
-/
#guard_msgs in
#check Tacenta.UnitHeadroomSatisfiable.initiatorHeadroom_iff

/--
info: Tacenta.UnitHeadroomSatisfiable.responderHeadroom_iff (s : tacenta_session_unit.lifecycle.PrekeyStore) :
  Tacenta.UnitLifecycleT1.EstablishResponderHeadroom s ↔ (↑s.last_resort_seen).length < Aeneas.Std.Usize.max
-/
#guard_msgs in
#check Tacenta.UnitHeadroomSatisfiable.responderHeadroom_iff

/--
info: Tacenta.UnitHeadroomSatisfiable.encryptHeadroom_sessionOf_iff (sk : tacenta_session_unit.tacenta_boundary.dh.PrivateKey)
  (our peer : tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes) (ad : Aeneas.Std.alloc.vec.Vec Aeneas.Std.U8)
  (dhs : Aeneas.Std.Array Aeneas.Std.U8 32#usize) (pending : Option tacenta_session_unit.lifecycle.PendingInitial)
  (pt : Aeneas.Std.Slice Aeneas.Std.U8) :
  Tacenta.UnitLifecycleT1.EncryptHeadroom (Tacenta.UnitHeadroomSatisfiable.sessionOf sk our peer ad dhs pending) pt ↔
    (↑ad).length + 106 ≤ Aeneas.Std.Usize.max ∧
      102 + ((↑pt).length + 48) ≤ Aeneas.Std.Usize.max ∧
        match pending with
        | none => True
        | some p => 33 + 33 + (↑p.kem_ciphertext).length + (102 + ((↑pt).length + 48)) + 18 ≤ Aeneas.Std.Usize.max
-/
#guard_msgs in
#check Tacenta.UnitHeadroomSatisfiable.encryptHeadroom_sessionOf_iff
