import Translation.UnitLifecycleEstablishResponder
import Translation.UnitLifecycleEstablishedEncrypt

/-!
# `establish_responder` on the frame the initiator's first `encrypt` emits

The encrypt branch (`UnitLifecycleEstablishedEncrypt`) shows that the first public `encrypt` at a session
`establish_initiator_for` returned emits the model's initial message wrapping the first ratchet frame
(`initialWire`, `firstFrame`).  The generic responder route (`UnitLifecycleEstablishResponder`) shows, for
every input, which outcomes `establish_responder` has and that the session it hands to its inner
`decrypt_ratchet` meets that theorem's session-side hypotheses.  This module feeds the one into the other:
the bytes one party's call returns become the input of the other party's call, so two public roots are composed
in one run, each at the state its own route derives (the establishment output, the session the responder
builds).

## What is shown

* `establish_initiator_for_secret` (no hypothesis): every successful `establish_initiator_for` output is the
  session of an `InitiatorSecretParts` record, which extends the establishment's parts with what the run
  computed and the session does not hold: the identity key, the zeroized encapsulated secret, the shared
  secret `initiator_shared_secret` returned with its zeroized bytes and slices, the ratchet agreement, the
  `init_sender` and `Braid::initiator` calls, and `verify_bundle`'s acceptance of the bundle.
* `publish_parts` (no hypothesis): what `PrekeyStore::publish` names (the store's identity key, the public key
  of its signed prekey, the last-resort KEM key or the last one-time KEM entry, no one-time curve key or the
  last one-time curve entry).
* `responder_first_frame_prepares`: for every record `q` of an initiator's run, every frame, every responder
  identity whose public key is the store's identity key, every prekey store whose `publish` returned the
  bundle the initiator used, whose identifiers are distinct and not `ABSENT_ID` (`PrekeyIdsDistinct`, named),
  and at which the per-run premise `FirstKemAgrees` holds, and every source of randomness, `establish_responder`
  on the initiator's initial message either refuses with one of the three refusals the store decides
  (`StoreRefusal`: the legacy marker on the last-resort key, the handshake's fingerprint already recorded, or a
  non-empty record whose count for the key, `last_resort_seen_for`, has reached `MAX_LAST_RESORT_SEEN`), only when
  the bundle names the last-resort key, with the store and the source as given; or reaches the inner receive with
  parts whose shared secret, its zeroized bytes and slices, peer keys and decapsulated secret are the initiator's
  and whose frame is the one the message carries.  Every other refusal of the prepare phase (`Decode`,
  `UnknownPrekeyId`, `BadEncoding`, `InvalidIdentityKey`, `NonContributoryAgreement`, `Kem`) is excluded at this
  input: the theorem's disjunction has no arm for it; `Kem` is excluded by the premise `FirstKemAgrees`, not shown
  impossible.
  The shared secrets are equal because the responder's four agreements are the initiator's four agreements
  with the arguments swapped (`shared_secret_symmetric`), so the contributory checks pass on the responder's
  side because they passed on the initiator's.
* `responder_first_frame_admissible`: with, in the second arm, `Session::invariant`, the four counter ceilings
  and the relation to `responderModelOf dh p` of the session the call hands to `decrypt_ratchet`, from the
  generic responder route.
* `first_send_responder_prepares` (the composed statement): the bytes a successful first `encrypt` at an
  establishment output returns (`established_encrypt_outcomes`, success arm) are the initial message wrapping
  the first ratchet frame for some message key and chunk, and `establish_responder` on them is as above.  It
  lists no compiler-trust axiom: the encrypt wrapper's nine `native_decide` constants are kernel proofs since
  2026-10-21.
* Non-vacuity.  `first_frame_laws_model`: every law the statements take, with the decrypt, establishment,
  restore, encrypt and responder laws and shapes, holds in one interpretation, `InterpO.modelFirstFrame` (the
  encrypt branch's joint model with an agreement that is symmetric and contributory on the keys `public_key`
  returns), together with `FirstFrameSuccessShape`.  `first_send_responder_reachable`: at the real constants,
  under those laws and `FirstFrameSuccessShape` (assumed, used for this inhabitation only), one run from
  `publish` through the establishment and the first send to the inner receive exists, at a store that refuses
  nothing, with every premise of `first_send_responder_prepares` holding there.

## The laws and premises

* `DhAgreeSymmetric` (`DhAgreeSymmetricShape Interp.real`, new, assumed): for private keys `a`, `b` with
  public keys `pa`, `pb`, `agree a pb = agree b pa`.  True of X25519 by reading (both are the u-coordinate of
  the product of the two clamped scalars with the base point; the boundary refuses the all-zero output on both
  sides); not checked in Lean.  Model: `modelFirstFrame_symmetric`.
* `FirstKemAgrees` (per-run premise, not a law): the KEM key pair the store holds under the identifier the
  bundle names decapsulates the initiator's ciphertext to the initiator's encapsulated secret.  ML-KEM
  decapsulation of an honest ciphertext fails with small probability (FIPS 203) and the wrapper's implicit
  rejection then returns another secret, so a universal law would be false.
* `PrekeyIdsDistinct` (named store hypothesis): the identifiers `PrekeyStore::invariant`'s identifier loop
  checks are distinct and none is `ABSENT_ID`.  That `PrekeyStore::invariant store = ok true` implies it is not
  checked: the invariant's loops read the pools through `IntoIterator for &Vec`, which the translation leaves
  opaque and no law in the tree describes.
* Reused: `DhPublicValid` (the initiator's identity key passes the responder's identity check, the wire keys
  are canonical), `DhPublicBytesRoundTrip` (a decoded key is the key the initiator encoded),
  `KemCiphertextLenOf` and `KemCiphertextLenBound` (the decoder's ciphertext length), the view's codec relation
  `DhCodecOf dh`, the contracts of `establish_responder_no_panic`; for the second arm `OptionEqU64Shape` and the
  decrypt agreements; for the composed statement the hypotheses of `established_encrypt_outcomes`.

## What it does not show

* That the inner `decrypt_ratchet` succeeds on the first frame, or which plaintext it returns: that needs the
  first message key to agree on both sides in the model and the AEAD round trip, and is not here.  The parts
  reach the inner receive; the generic route's `establish_responder_at_parts` makes the call's success exactly the inner
  receive's success with the commit returning.
* The responder's successor, its invariant, the responder's draws, or anything after the first frame.
* The model's `establishResponder` equality.
* That `PrekeyStore::invariant` gives `PrekeyIdsDistinct` (above); that the real primitives meet
  `DhAgreeSymmetric`, `DhPublicValid`, the round trip, the boundary records or `FirstFrameSuccessShape`; that
  ML-KEM decapsulation agrees on a given run.  A source with no state of its own, such as `OsRng`, is outside
  the statements about draws.
-/

namespace Tacenta.UnitLifecycleResponderFirstFrame

open Aeneas Aeneas.Std Result
open tacenta_session_unit
open Tacenta.SessionUnitRatchetImportInv (bind_eq_ok_inv bind2_eq_ok_inv bind3_eq_ok_inv)
open Tacenta.UnitLifecycleT3 (DhView DhCodecOf vecOf sliceOf arrayOf pendingInitialOf SessionRefines)
open Tacenta.UnitLifecycleEstablishInitiatorShape (InitiatorOutputParts initiatorTriple init_sender_ok
  braid_initiator_ok verify_bundle_ok DhPublicValid establishedModelOf)
open Tacenta.UnitLifecycleEstablishResponder (z32 fullSlice ResponderPreparedParts)

/-! ## What the initiator's run computed, beyond its session -/

/-- **What a successful `establish_initiator_for` computed**, beyond the parts of the session it returned
(`InitiatorOutputParts`): the identity key, the encapsulated secret after the zeroizing wrapper, the shared
secret `initiator_shared_secret` returned, its zeroized bytes and the two slices the Triple and the Braid were
built from, the ratchet agreement with the bundle's signed prekey and its zeroized bytes, the `init_sender` and
`Braid::initiator` calls, and `verify_bundle`'s acceptance of the bundle.  Every field is read off the
generated function; none is assumed. -/
structure InitiatorSecretParts {R : Type} (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R)
    (our : lifecycle.Identity) (bundle : lifecycle.PublishedBundle)
    extends InitiatorOutputParts rc crc our bundle where
  identityKey : tacenta_boundary.dh.PrivateKey
  kemSecretZ : zeroize.Zeroizing (Array U8 32#usize)
  encapsulated : Array U8 32#usize
  shared : Array U8 32#usize
  sharedZ : zeroize.Zeroizing (Array U8 32#usize)
  sharedBytes : Array U8 32#usize
  sharedSlice : Slice U8
  dhOut : Array U8 32#usize
  dhOutZ : zeroize.Zeroizing (Array U8 32#usize)
  dhOutBytes : Array U8 32#usize
  braidSlice : Slice U8
  hDhKey : lifecycle.Identity.dh_key our = ok identityKey
  hKemSecretZ : zeroize.Zeroizing.new z32 kemSecret = ok kemSecretZ
  hEncapsulated : zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref z32 kemSecretZ = ok encapsulated
  hShared : initiator_shared_secret identityKey ephemeral bundle.bundle encapsulated =
    ok (core.result.Result.Ok shared)
  hSharedZ : zeroize.Zeroizing.new z32 shared = ok sharedZ
  hSharedBytes : zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref z32 sharedZ = ok sharedBytes
  hTriple : tacenta_triple.State.init_sender sharedSlice ratchetBytes peerRatchetBytes dhOutBytes
    tacenta_ratchet.LabelSet.Tacenta =
      ok (initiatorTriple ratchetBytes peerRatchetBytes rootKey sendChain sparseRoot sparseSend sparseReceive)
  hSharedSlice : fullSlice sharedBytes = ok sharedSlice
  hDhOutBytes : zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref z32 dhOutZ = ok dhOutBytes
  hDhOutZ : zeroize.Zeroizing.new z32 dhOut = ok dhOutZ
  hDhOut : tacenta_boundary.dh.PrivateKey.agree ratchetPrivate bundle.bundle.signed_prekey = ok (some dhOut)
  hBraid : tacenta_braid.Braid.initiator braidSlice = ok ⟨tacenta_braid.State.KeysUnsampled 1#u64 auth⟩
  hBraidSlice : fullSlice sharedBytes = ok braidSlice
  hVerify : verify_bundle bundle.bundle = ok (core.result.Result.Ok ())

/-- A `PreKeyBundle` rebuilt with its own fields and a one-time prekey equal to its own is itself. -/
theorem bundle_with_own (b : PreKeyBundle) (o : Option tacenta_boundary.dh.PublicKeyBytes)
    (h : b.one_time_prekey = o) :
    ({ identity_key := b.identity_key, signed_prekey := b.signed_prekey,
       signed_prekey_signature := b.signed_prekey_signature, kem_prekey := b.kem_prekey,
       kem_prekey_signature := b.kem_prekey_signature, one_time_prekey := o } : PreKeyBundle) = b := by
  subst h; rfl

/-- **What a successful `establish_initiator_for` computed**, for every identity, bundle, expected identity
and source of randomness: the session it returned is the session of an `InitiatorSecretParts` record.
Hypothesis-free. -/
theorem establish_initiator_for_secret {R : Type} (rc : rand_core_1.RngCore R)
    (crc : rand_core_1.CryptoRng R) (our : lifecycle.Identity) (bundle : lifecycle.PublishedBundle)
    (expected : tacenta_boundary.dh.PublicKeyBytes) (rng0 rng1 : R) (s : lifecycle.Session)
    (h : lifecycle.establish_initiator_for rc crc our bundle expected rng0 =
      ok (core.result.Result.Ok s, rng1)) :
    ∃ q : InitiatorSecretParts rc crc our bundle, s = q.session := by
  unfold lifecycle.establish_initiator_for at h
  repeat' first
    | (replace h := bind2_eq_ok_inv h; obtain ⟨_, _, _, h⟩ := h)
    | (replace h := bind_eq_ok_inv h; obtain ⟨_, _, h⟩ := h)
    | split at h
    | simp at h
  all_goals subst_vars
  all_goals
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨rk, cks, prk, c1, c2, rfl⟩ := init_sender_ok _ _ _ _ _ ‹_›
    obtain ⟨auth, rfl⟩ := braid_initiator_ok _ _ ‹_›
    have hv : is_valid_identity_key bundle.bundle.identity_key = ok true :=
      verify_bundle_ok _ _ ‹_›
    try rw [bundle_with_own bundle.bundle _ ‹_›] at *
    try rw [bundle_with_own bundle.bundle _ rfl] at *
    refine ⟨
      {
        ratchetPrivate := _
        ratchetPublic := _
        ratchetBytes := _
        peerRatchetBytes := _
        rootKey := _
        sendChain := _
        sparseRoot := _
        sparseSend := _
        sparseReceive := _
        auth := _
        identityAd := _
        ourPublic := _
        ephemeral := _
        ephemeralPublic := _
        kemCiphertext := _
        kemSecret := _
        rngBefore := _
        rngAfter := _
        identityKey := _
        kemSecretZ := _
        encapsulated := _
        shared := _
        sharedZ := _
        sharedBytes := _
        sharedSlice := _
        dhOut := _
        dhOutZ := _
        dhOutBytes := _
        braidSlice := _
        hRatchetPublic := ‹_›
        hRatchetBytes := ‹_›
        hPeerRatchetBytes := ‹_›
        hPeerRatchetCanonical := ‹_›
        hOurPublic := ‹_›
        hIdentityAd := ‹_›
        hPeerValid := hv
        hEphemeralPublic := ‹_›
        hEncapsulate := ‹_›
        hDhKey := ‹_›
        hKemSecretZ := ‹_›
        hEncapsulated := ‹_›
        hShared := ‹_›
        hSharedZ := ‹_›
        hSharedBytes := ‹_›
        hTriple := ‹_›
        hSharedSlice := ‹_›
        hDhOutBytes := ‹_›
        hDhOutZ := ‹_›
        hDhOut := ‹_›
        hBraid := ‹_›
        hBraidSlice := ‹_›
        hVerify := ‹_›
      }, rfl⟩

/-! ## The agreement law -/

open Tacenta.UnitSatisfiabilityJoint (Interp Interp.real)

/-- The agreement of a private key with another's public key is the agreement of the other with the first's
public key, over an interpretation `I`. -/
def DhAgreeSymmetricShape (I : Interp) : Prop :=
  ∀ (a b : I.PrivateKey) (pa pb : I.PublicKeyBytes), I.dhPrivPublicKey a = ok pa →
    I.dhPrivPublicKey b = ok pb → I.dhPrivAgree a pb = I.dhPrivAgree b pa

/-- **Assumed law**: `DhAgreeSymmetricShape` at the real constants. -/
def DhAgreeSymmetric : Prop := DhAgreeSymmetricShape Interp.real

/-- At the real constants, `DhAgreeSymmetric` is the statement about the real functions. -/
theorem dhAgreeSymmetric_is : DhAgreeSymmetric ↔
    ∀ (a b : tacenta_boundary.dh.PrivateKey) (pa pb : tacenta_boundary.dh.PublicKeyBytes),
      tacenta_boundary.dh.PrivateKey.public_key a = ok pa →
      tacenta_boundary.dh.PrivateKey.public_key b = ok pb →
      tacenta_boundary.dh.PrivateKey.agree a pb = tacenta_boundary.dh.PrivateKey.agree b pa := Iff.rfl

/-- The two halves of the one-time prekey agree: the bundle carries none and the responder holds none, or
the bundle carries the public key of the private key the responder holds. -/
def OneTimeMatches (bundleKey : Option tacenta_boundary.dh.PublicKeyBytes)
    (held : Option tacenta_boundary.dh.PrivateKey) : Prop :=
  (bundleKey = none ∧ held = none) ∨
    ∃ k pk, held = some k ∧ tacenta_boundary.dh.PrivateKey.public_key k = ok pk ∧ bundleKey = some pk

/-- **The responder's shared-secret computation is the initiator's**, under `DhAgreeSymmetric`, when the
bundle's identity key and signed prekey are the public keys of the responder's identity key and signed
prekey, the one-time halves match, the responder is given the initiator's identity and ephemeral public keys,
`verify_bundle` accepts the bundle and the initiator's identity key passes the identity check: the two calls
are equal as computations, so they refuse or succeed together, with the same secret. -/
theorem shared_secret_symmetric (hsym : DhAgreeSymmetric)
    (ikA eph ikB spk : tacenta_boundary.dh.PrivateKey) (pubA ephPub : tacenta_boundary.dh.PublicKeyBytes)
    (bundle : PreKeyBundle) (otk : Option tacenta_boundary.dh.PrivateKey) (enc : Array U8 32#usize)
    (hpubA : tacenta_boundary.dh.PrivateKey.public_key ikA = ok pubA)
    (hephPub : tacenta_boundary.dh.PrivateKey.public_key eph = ok ephPub)
    (hikB : tacenta_boundary.dh.PrivateKey.public_key ikB = ok bundle.identity_key)
    (hspk : tacenta_boundary.dh.PrivateKey.public_key spk = ok bundle.signed_prekey)
    (hotk : OneTimeMatches bundle.one_time_prekey otk)
    (hverify : verify_bundle bundle = ok (core.result.Result.Ok ()))
    (hvalid : is_valid_identity_key pubA = ok true) :
    responder_shared_secret ikB spk otk pubA ephPub enc = initiator_shared_secret ikA eph bundle enc := by
  have s1 := (dhAgreeSymmetric_is.mp hsym) ikA spk pubA bundle.signed_prekey hpubA hspk
  have s2 := (dhAgreeSymmetric_is.mp hsym) eph ikB ephPub bundle.identity_key hephPub hikB
  have s3 := (dhAgreeSymmetric_is.mp hsym) eph spk ephPub bundle.signed_prekey hephPub hspk
  unfold responder_shared_secret initiator_shared_secret
  rw [hverify, hvalid, ← s1, ← s2, ← s3]
  rcases hotk with ⟨hb, rfl⟩ | ⟨k, pk, rfl, hk, hb⟩
  · simp only [hb, Aeneas.Std.bind_tc_ok, if_true]
    rfl
  · have s4 := (dhAgreeSymmetric_is.mp hsym) eph k ephPub pk hephPub hk
    simp only [hb, Aeneas.Std.bind_tc_ok, if_true, ← s4]
    rfl

/-! ## What `publish` names -/

/-- The `Zeroize` instance of the one-time curve pool's vector, as the generated code spells it. -/
noncomputable abbrev zPool : zeroize.Zeroize (alloc.vec.Vec (U32 × Array U8 32#usize)) :=
  alloc.vec.Vec.Insts.ZeroizeZeroize (Pair.Insts.ZeroizeZeroize
    (zeroize.Zeroize.Blanket U32.Insts.ZeroizeDefaultIsZeroes)
    (Array.Insts.ZeroizeZeroize 32#usize (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)))

/-- Indexing a vector at its last position returns its last element. -/
theorem vec_index_last {α : Type} (v : alloc.vec.Vec α) (i : Usize) (x : α)
    (h : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice α) v i = ok x)
    (hi : i.val = v.val.length - 1) : v.val.getLast? = some x := by
  rw [alloc.vec.Vec.index_slice_index] at h
  simp only [alloc.vec.Vec.index_usize] at h
  split at h
  · cases h
  · rename_i y hy
    simp only [ok.injEq] at h
    subst h
    rw [List.getLast?_eq_getElem?, ← hi]
    simpa using hy

/-- **What `PrekeyStore::publish` names**: the store's signed prekey identifier and identity key, the public
key of its signed prekey, either the last-resort KEM key under its identifier or the last one-time KEM entry,
and either no one-time curve key (`ABSENT_ID`) or the last entry of the one-time curve pool with the public key
of its secret.  Hypothesis-free. -/
theorem publish_parts (store : lifecycle.PrekeyStore) (bundle : lifecycle.PublishedBundle)
    (h : lifecycle.PrekeyStore.publish store = ok bundle) :
    bundle.signed_prekey_id = store.signed_prekey_id ∧
    bundle.bundle.identity_key = store.identity_public ∧
    (∃ spk, tacenta_boundary.dh.PrivateKey.from_bytes store.signed_prekey_secret = ok spk ∧
      tacenta_boundary.dh.PrivateKey.public_key spk = ok bundle.bundle.signed_prekey) ∧
    ((bundle.kem_prekey_id = store.kem_id ∧
        tacenta_boundary.kem.KeyPair.public_key store.kem = ok bundle.bundle.kem_prekey) ∨
      (∃ e, store.kem_one_time.val.getLast? = some e ∧ bundle.kem_prekey_id = e.1 ∧
        tacenta_boundary.kem.KeyPair.public_key e.2.1 = ok bundle.bundle.kem_prekey)) ∧
    (∃ v, zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref zPool store.one_time = ok v ∧
      ((bundle.one_time_prekey_id = serialization.ABSENT_ID ∧ bundle.bundle.one_time_prekey = none) ∨
        (∃ e k pk, v.val.getLast? = some e ∧ bundle.one_time_prekey_id = e.1 ∧
          tacenta_boundary.dh.PrivateKey.from_bytes e.2 = ok k ∧
          tacenta_boundary.dh.PrivateKey.public_key k = ok pk ∧
          bundle.bundle.one_time_prekey = some pk))) := by
  unfold lifecycle.PrekeyStore.publish at h
  obtain ⟨v, hv, h⟩ := bind_eq_ok_inv h
  obtain ⟨b, -, h⟩ := bind_eq_ok_inv h
  obtain ⟨⟨oid, opk⟩, hone, h⟩ := bind_eq_ok_inv h
  obtain ⟨b1, -, h⟩ := bind_eq_ok_inv h
  obtain ⟨⟨kid, kpk, ksig⟩, hkem, h⟩ := bind_eq_ok_inv h
  obtain ⟨spk, hspk, h⟩ := bind_eq_ok_inv h
  obtain ⟨pkb, hpkb, h⟩ := bind_eq_ok_inv h
  simp only [ok.injEq] at h
  subst h
  refine ⟨rfl, rfl, ⟨spk, hspk, hpkb⟩, ?_, v, hv, ?_⟩
  · split at hkem
    · obtain ⟨v1, hv1, hkem⟩ := bind_eq_ok_inv hkem
      simp only [ok.injEq, Prod.mk.injEq] at hkem
      obtain ⟨rfl, rfl, rfl⟩ := hkem
      exact Or.inl ⟨rfl, hv1⟩
    · obtain ⟨index, hindex, hkem⟩ := bind_eq_ok_inv hkem
      obtain ⟨⟨id, pair, sig⟩, hx, hkem⟩ := bind_eq_ok_inv hkem
      obtain ⟨v1, hv1, hkem⟩ := bind_eq_ok_inv hkem
      simp only [ok.injEq, Prod.mk.injEq] at hkem
      obtain ⟨rfl, rfl, rfl⟩ := hkem
      have hi : index.val = store.kem_one_time.val.length - 1 := by
        have := UScalar.sub_equiv (alloc.vec.Vec.len store.kem_one_time) 1#usize
        rw [hindex] at this
        simp only [alloc.vec.Vec.len] at this
        scalar_tac
      exact Or.inr ⟨_, vec_index_last _ _ _ hx hi, rfl, hv1⟩
  · split at hone
    · simp only [ok.injEq, Prod.mk.injEq] at hone
      obtain ⟨rfl, rfl⟩ := hone
      exact Or.inl ⟨rfl, rfl⟩
    · obtain ⟨index, hindex, hone⟩ := bind_eq_ok_inv hone
      obtain ⟨⟨id, x⟩, hx, hone⟩ := bind_eq_ok_inv hone
      obtain ⟨⟨y, sec⟩, hy, hone⟩ := bind_eq_ok_inv hone
      obtain ⟨k, hk, hone⟩ := bind_eq_ok_inv hone
      obtain ⟨pk, hpk, hone⟩ := bind_eq_ok_inv hone
      simp only [ok.injEq, Prod.mk.injEq] at hone
      obtain ⟨rfl, rfl⟩ := hone
      have hi : index.val = v.val.length - 1 := by
        have := UScalar.sub_equiv (alloc.vec.Vec.len v) 1#usize
        rw [hindex] at this
        simp only [alloc.vec.Vec.len] at this
        scalar_tac
      have h1 := vec_index_last _ _ _ hx hi
      have h2 := vec_index_last _ _ _ hy hi
      rw [h1] at h2
      simp only [Option.some.injEq, Prod.mk.injEq] at h2
      obtain ⟨rfl, rfl⟩ := h2
      exact Or.inr ⟨_, k, pk, h1, rfl, hk, hpk, rfl⟩

/-! ## The store's lookups -/

/-- An entry of the one-time curve prekeys: an identifier and a secret. -/
abbrev PoolEntry := U32 × Array U8 32#usize

/-- An entry of the one-time KEM prekeys: an identifier, a key pair and a signature. -/
abbrev KemEntry := U32 × tacenta_boundary.kem.KeyPair × Array U8 64#usize

/-- `one_time_kem_ids` returns the identifiers of the one-time KEM prekeys, in order. -/
theorem one_time_kem_ids_spec (store : lifecycle.PrekeyStore) :
    lifecycle.PrekeyStore.one_time_kem_ids store ⦃ fun ids =>
      ids.val = store.kem_one_time.val.map (·.1) ⦄ := by
  unfold lifecycle.PrekeyStore.one_time_kem_ids lifecycle.PrekeyStore.one_time_kem_ids_loop
  apply loop.spec_decr_nat
    (measure := fun q => store.kem_one_time.val.length - q.2.val)
    (inv := fun q => q.2.val ≤ store.kem_one_time.val.length ∧
      q.1.val = (store.kem_one_time.val.take q.2.val).map (·.1))
  · rintro ⟨ids, index⟩ ⟨hi, hids⟩
    simp only at hi hids
    change lifecycle.PrekeyStore.one_time_kem_ids_loop.body store.kem_one_time ids index ⦃ _ ⦄
    simp only [lifecycle.PrekeyStore.one_time_kem_ids_loop.body]
    split
    · rename_i hlt
      have hlt' : index.val < store.kem_one_time.val.length := by
        simpa [alloc.vec.Vec.len] using hlt
      have hidx : alloc.vec.Vec.index
          (core.slice.index.SliceIndexUsizeSlice (U32 × tacenta_boundary.kem.KeyPair × Array U8 64#usize))
          store.kem_one_time index = ok (store.kem_one_time.val[index.val]'hlt') := by
        rw [alloc.vec.Vec.index_slice_index]
        obtain ⟨x, hx, hxv⟩ := Std.WP.spec_imp_exists
          (alloc.vec.Vec.index_usize_spec store.kem_one_time index hlt')
        rw [hx, hxv]
      rw [hidx]
      simp only [Aeneas.Std.bind_tc_ok]
      try dsimp only [Aeneas.Std.uncurry]
      have hlenmax : store.kem_one_time.val.length ≤ Usize.max := store.kem_one_time.property
      have hpush : alloc.vec.Vec.push ids (store.kem_one_time.val[index.val]'hlt').1 =
          ok ⟨ids.val ++ [(store.kem_one_time.val[index.val]'hlt').1], by
            simp [hids]; omega⟩ := by
        unfold alloc.vec.Vec.push
        simp only
        rw [dif_pos (by simp [hids]; omega)]
        simp [List.concat_eq_append]
      rw [hpush]
      simp only [Aeneas.Std.bind_tc_ok]
      obtain ⟨i1, hi1, hi1v⟩ := Std.WP.spec_imp_exists (Usize.add_spec (x := index) (y := 1#usize)
        (by simp; omega))
      rw [hi1]
      simp only [Aeneas.Std.bind_tc_ok, WP.spec_ok]
      refine ⟨⟨by simp at hi1v ⊢; omega, ?_⟩, by simp at hi1v ⊢; omega⟩
      have hi1v' : i1.val = index.val + 1 := by simpa using hi1v
      rw [hids, hi1v', List.take_add_one, List.map_append, List.getElem?_eq_getElem hlt']
      rfl
    · rename_i hge
      simp only [WP.spec_ok]
      have : index.val = store.kem_one_time.val.length := by
        have : ¬ index.val < store.kem_one_time.val.length := by
          simpa [alloc.vec.Vec.len] using hge
        omega
      rw [hids, this, List.take_length]
  · exact ⟨by simp, by simp [alloc.vec.Vec.with_capacity]⟩


/-- `u32_index` finds a needle at its first occurrence: past a prefix that does not hold it. -/
theorem u32_index_first (values : Slice U32) (needle : U32) (pre post : List U32)
    (hv : values.val = pre ++ needle :: post) (hpre : needle ∉ pre) :
    lifecycle.u32_index values needle ⦃ fun r => ∃ i : Usize, r = some i ∧ i.val = pre.length ⦄ := by
  unfold lifecycle.u32_index lifecycle.u32_index_loop
  have hlen : pre.length < values.val.length := by simp [hv]
  apply loop.spec_decr_nat
    (measure := fun i => values.val.length - i.val)
    (inv := fun i => i.val ≤ pre.length)
  · intro index hi
    simp only [lifecycle.u32_index_loop.body]
    have hlt' : index.val < values.val.length := by omega
    have hlt : index < Slice.len values := by simp [Slice.len]; scalar_tac
    rw [if_pos hlt]
    obtain ⟨x, hx, hxv⟩ := Std.WP.spec_imp_exists (Slice.index_usize_spec values index hlt')
    rw [hx]
    simp only [Aeneas.Std.bind_tc_ok]
    by_cases heq : index.val = pre.length
    · have : x = needle := by
        rw [hxv]; simp [hv, heq]
      rw [if_pos this]
      simp only [WP.spec_ok]
      exact ⟨index, rfl, heq⟩
    · have hlt2 : index.val < pre.length := by omega
      have hxp : x = pre[index.val] := by
        rw [hxv]; simp [hv, List.getElem_append_left hlt2]
      have : x ≠ needle := by
        rw [hxp]
        intro hc
        exact hpre (hc ▸ List.getElem_mem hlt2)
      rw [if_neg this]
      have hu := Tacenta.UnitHeadroomSatisfiable.usize_max_ge
      have hmax : values.val.length ≤ Usize.max := values.property
      obtain ⟨i1, hi1, hi1v⟩ := Std.WP.spec_imp_exists (Usize.add_spec (x := index) (y := 1#usize)
        (by simp; omega))
      rw [hi1]
      simp only [Aeneas.Std.bind_tc_ok, WP.spec_ok]
      have hi1v' : i1.val = index.val + 1 := by simpa using hi1v
      omega
  · simp

/-- `peek_one_time` finds an identifier at its first occurrence in the one-time curve prekeys, and returns the
secret stored there wrapped, under the zeroizing round trip. -/
theorem peek_one_time_first (hz : Tacenta.SessionUnitBraidT1.ZeroizingArrayRoundTrip)
    (store : lifecycle.PrekeyStore) (id : U32) (v : alloc.vec.Vec (U32 × Array U8 32#usize))
    (hv : zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref zPool store.one_time = ok v)
    (e : PoolEntry) (pre post : List PoolEntry)
    (hval : v.val = pre ++ e :: post) (he : e.1 = id) (hpre : id ∉ pre.map (·.1)) :
    lifecycle.PrekeyStore.peek_one_time store id ⦃ fun r => ∃ z, r = some z ∧
      zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref z32 z = ok e.2 ⦄ := by
  unfold lifecycle.PrekeyStore.peek_one_time lifecycle.PrekeyStore.peek_one_time_loop
  have hlen : pre.length < v.val.length := by simp [hval]
  apply loop.spec_decr_nat
    (measure := fun i => v.val.length - i.val)
    (inv := fun i => i.val ≤ pre.length)
  · intro index hi
    simp only [lifecycle.PrekeyStore.peek_one_time_loop.body]
    rw [hv]
    simp only [Aeneas.Std.bind_tc_ok]
    have hlt' : index.val < v.val.length := by omega
    have hlt : index < alloc.vec.Vec.len v := by simp only [alloc.vec.Vec.len]; scalar_tac
    rw [if_pos hlt]
    have hidx : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice (U32 × Array U8 32#usize))
        v index = ok (v.val[index.val]'hlt') := by
      rw [alloc.vec.Vec.index_slice_index]
      obtain ⟨x, hx, hxv⟩ := Std.WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec v index hlt')
      rw [hx, hxv]
    rw [hidx]
    simp only [Aeneas.Std.bind_tc_ok]
    try dsimp only [Aeneas.Std.uncurry]
    by_cases heq : index.val = pre.length
    · have hget : v.val[index.val]'hlt' = e := by simp [hval, heq]
      rw [hget]
      obtain ⟨e1, e2⟩ := e
      simp only at he
      subst he
      simp only [if_true]
      obtain ⟨z, hz1, hz2⟩ := hz 32#usize z32 e2
      rw [hz1]
      simp only [Aeneas.Std.bind_tc_ok, WP.spec_ok]
      exact ⟨z, rfl, hz2⟩
    · have hlt2 : index.val < pre.length := by omega
      have hget : v.val[index.val]'hlt' = pre[index.val] := by
        simp only [hval]; rw [List.getElem_append_left hlt2]
      rw [hget]
      have hne : pre[index.val].1 ≠ id := by
        intro hc
        exact hpre (hc ▸ List.mem_map_of_mem (List.getElem_mem hlt2))
      rw [if_neg hne]
      have hu := Tacenta.UnitHeadroomSatisfiable.usize_max_ge
      have hmax : v.val.length ≤ Usize.max := v.property
      obtain ⟨i1, hi1, hi1v⟩ := Std.WP.spec_imp_exists (Usize.add_spec (x := index) (y := 1#usize)
        (by simp; omega))
      rw [hi1]
      simp only [Aeneas.Std.bind_tc_ok, WP.spec_ok]
      have hi1v' : i1.val = index.val + 1 := by simpa using hi1v
      omega
  · simp


/-! ## The store facts the theorem is stated under -/

/-- The identifiers a prekey store holds, in the order `PrekeyStore::invariant` collects them: the signed
prekey's, the KEM key's, the previous signed prekey's and the previous KEM key's if any, then the one-time
curve prekeys' (from `pool`, the vector the zeroizing wrapper holds) and the one-time KEM prekeys'. -/
def storeIds (store : lifecycle.PrekeyStore) (pool : List PoolEntry) : List U32 :=
  store.signed_prekey_id :: store.kem_id ::
    ((store.previous_signed_prekey.map (·.2.1)).toList ++ (store.previous_kem.map (·.2.1)).toList ++
      pool.map (·.1) ++ store.kem_one_time.val.map (·.1))

/-- **The store's identifiers are distinct and none is `ABSENT_ID`**: what the identifier loop of
`PrekeyStore::invariant` checks of them, apart from the bound by `next_id`. -/
def PrekeyIdsDistinct (store : lifecycle.PrekeyStore) : Prop :=
  ∃ v, zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref zPool store.one_time = ok v ∧
    (storeIds store v.val).Nodup ∧ serialization.ABSENT_ID ∉ storeIds store v.val

/-- The KEM key pair a store holds under an identifier: the last-resort key under its own identifier,
otherwise the first one-time KEM entry with that identifier. -/
def heldKemPair (store : lifecycle.PrekeyStore) (id : U32) : Option tacenta_boundary.kem.KeyPair :=
  if id = store.kem_id then some store.kem else (store.kem_one_time.val.find? (·.1 = id)).map (·.2.1)

/-- **Per-run premise**: the KEM key pair the store holds under the identifier the bundle names decapsulates
the initiator's ciphertext to the initiator's encapsulated secret.  A premise about one run and not a law:
ML-KEM decapsulation of an honestly encapsulated ciphertext fails with small probability (FIPS 203), and the
wrapper's implicit rejection then returns another secret rather than an error. -/
def FirstKemAgrees (store : lifecycle.PrekeyStore) (id : U32) (ct : alloc.vec.Vec U8)
    (ss : Array U8 32#usize) : Prop :=
  ∃ pair, heldKemPair store id = some pair ∧
    tacenta_boundary.kem.decapsulate pair (alloc.vec.Vec.deref ct) = ok (core.result.Result.Ok ss)

/-! ## The initiator's bytes, decoded by the responder -/

/-- The model's canonicity of a 32-byte array's bytes is the code's. -/
theorem canonicalKey_arrayOf (a : Array U8 32#usize)
    (h : Tacenta.SessionUnitT1.canonicalX25519 a = true) :
    Model.Messages.canonicalKey (arrayOf a) = true := by
  have h1 := Tacenta.SessionUnitWireT3.canonicalKey_bytesOf a
  have h2 : Tacenta.SessionUnitWireT1.canonicalX25519 a = Tacenta.SessionUnitT1.canonicalX25519 a := by
    rw [← Tacenta.SessionUnitDecodeEc.canonicalX25519_session_eq_wire,
      Tacenta.UnitHeadroomInvariant.canonical_session_eq]
  have h3 : arrayOf a = Tacenta.SessionUnitWireT3.bytesOf a.val := by
    simp [arrayOf, Tacenta.SessionUnitWireT3.bytesOf, Tacenta.SessionUnitWireT3.byteOf,
      Tacenta.SessionUnitBraidT3.u8]
  rw [h3, h1, h2, h]

/-- The view of a public key the code made is its 32 bytes, which are canonical, under `DhPublicValid` and
the view's codec relation. -/
theorem view_of_public (hpub : DhPublicValid) {dh : DhView} (codec : DhCodecOf dh)
    {k : tacenta_boundary.dh.PrivateKey} {pk : tacenta_boundary.dh.PublicKeyBytes}
    (hk : tacenta_boundary.dh.PrivateKey.public_key k = ok pk) :
    ∃ a, tacenta_boundary.dh.PublicKeyBytes.as_bytes pk = ok a ∧
      Tacenta.SessionUnitT1.canonicalX25519 a = true ∧ dh.publicKey pk = arrayOf a := by
  obtain ⟨a, ha, hav⟩ := codec.asBytes pk
  exact ⟨a, ha, Tacenta.UnitLifecycleEstablishInitiatorShape.dhPublicValid_canonical hpub hk ha, hav.symm⟩

/-- `Identity::public` is the public key of `Identity::dh_key`. -/
theorem identity_public_of_dh_key {our : lifecycle.Identity} {k : tacenta_boundary.dh.PrivateKey}
    {pk : tacenta_boundary.dh.PublicKeyBytes} (hk : lifecycle.Identity.dh_key our = ok k)
    (hpk : lifecycle.Identity.public our = ok pk) :
    tacenta_boundary.dh.PrivateKey.public_key k = ok pk := by
  unfold lifecycle.Identity.public at hpk
  rw [hk, Aeneas.Std.bind_tc_ok] at hpk
  exact hpk

/-- A successful encapsulation's ciphertext is at most 65536 bytes, under the two ciphertext-length laws. -/
theorem ciphertext_le (hct : Tacenta.UnitLifecycleEstablishInitiatorShape.KemCiphertextLenOf)
    (hbound : Tacenta.UnitLifecycleRestoredSession.KemCiphertextLenBound) {R : Type}
    {rc : rand_core_1.RngCore R} {crc : rand_core_1.CryptoRng R} {pk : Slice U8} {rng rng' : R}
    {ct : alloc.vec.Vec U8} {ss : Array U8 32#usize}
    (h : tacenta_boundary.kem.encapsulate rc crc pk rng = ok (core.result.Result.Ok (ct, ss), rng')) :
    ct.val.length ≤ 65536 := by
  obtain ⟨n, hn, hlen⟩ := (Tacenta.UnitLifecycleEstablishInitiatorShape.kemCiphertextLenOf_is.mp hct) rc crc
    pk rng ct ss rng' h
  obtain ⟨n', hn', hle⟩ := hbound
  have hn : tacenta_boundary.kem.ciphertext_len = ok n := hn
  rw [hn] at hn'
  cases hn'
  omega

variable {R : Type} {rc : rand_core_1.RngCore R} {crc : rand_core_1.CryptoRng R}
  {our : lifecycle.Identity} {bundle : lifecycle.PublishedBundle}

/-- **The responder's decoder accepts the initiator's bytes and reads back the initiator's fields**: for an
initial message whose bytes are the model's encoding of the initiator's identity key, the pending ephemeral
key, the pending ciphertext, the bundle's three identifiers and any frame (`initialWire`, as the first send
emits it), `decode_initial` returns the identifiers, the ciphertext and the frame, and the two keys in
`EncodeEC` form.  Under `DhPublicValid`, the view's codec relation and the two ciphertext-length laws. -/
theorem decode_first_frame (hpub : DhPublicValid) {dh : DhView} (codec : DhCodecOf dh)
    (hct : Tacenta.UnitLifecycleEstablishInitiatorShape.KemCiphertextLenOf)
    (hbound : Tacenta.UnitLifecycleRestoredSession.KemCiphertextLenBound)
    (q : InitiatorSecretParts rc crc our bundle) (pending : Model.Lifecycle.PendingInitial)
    (hpend : (establishedModelOf dh q.session).pendingInitial = some pending)
    (frame : Model.Lifecycle.Bytes) (msg : Slice U8)
    (hmsg : sliceOf msg = Tacenta.UnitLifecycleEstablishedEncrypt.initialWire
      (establishedModelOf dh q.session) pending frame) :
    ∃ d, tacenta_wire.decode_initial msg = ok (core.result.Result.Ok d) ∧
      d.signed_prekey_id = bundle.signed_prekey_id ∧ d.one_time_prekey_id = bundle.one_time_prekey_id ∧
      d.kem_prekey_id = bundle.kem_prekey_id ∧
      alloc.vec.Vec.deref d.kem_ciphertext = alloc.vec.Vec.deref q.kemCiphertext ∧
      sliceOf (alloc.vec.Vec.deref d.message) = frame ∧
      sliceOf (alloc.vec.Vec.deref d.identity) =
        Model.PersistedState.SessionState.encodeEc (dh.publicKey q.ourPublic) ∧
      sliceOf (alloc.vec.Vec.deref d.ephemeral) =
        Model.PersistedState.SessionState.encodeEc (dh.publicKey q.ephemeralPublic) := by
  have hp : pending = pendingInitialOf dh
      { ephemeral_public := q.ephemeralPublic, kem_ciphertext := q.kemCiphertext,
        signed_prekey_id := bundle.signed_prekey_id, one_time_prekey_id := bundle.one_time_prekey_id,
        kem_prekey_id := bundle.kem_prekey_id } := by
    simp [establishedModelOf, InitiatorOutputParts.session] at hpend
    exact hpend.symm
  subst hp
  have hik : lifecycle.Identity.public our = ok q.ourPublic := q.hOurPublic
  have hidk := identity_public_of_dh_key q.hDhKey hik
  obtain ⟨ai, hai, hcani, hvi⟩ := view_of_public hpub codec hidk
  obtain ⟨ae, hae, hcane, hve⟩ := view_of_public hpub codec q.hEphemeralPublic
  have hctl := ciphertext_le hct hbound q.hEncapsulate
  have hmodel : Model.Messages.decodeInitialDetailed (sliceOf msg) =
      .ok { identity := Model.PersistedState.SessionState.encodeEc (dh.publicKey q.ourPublic),
            ephemeral := Model.PersistedState.SessionState.encodeEc (dh.publicKey q.ephemeralPublic),
            kemCiphertext := vecOf q.kemCiphertext,
            signedPrekeyId := UInt32.ofNat bundle.signed_prekey_id.val,
            oneTimeId := UInt32.ofNat bundle.one_time_prekey_id.val,
            kemPrekeyId := UInt32.ofNat bundle.kem_prekey_id.val, ratchetMessage := frame } := by
    rw [hmsg, Model.Messages.decodeInitialDetailed_ok_iff]
    simp only [Tacenta.UnitLifecycleEstablishedEncrypt.initialWire, establishedModelOf,
      InitiatorOutputParts.session, pendingInitialOf]
    rw [hvi, hve]
    have hl : ∀ a : Array U8 32#usize, (arrayOf a).length = 32 := fun a => by simp [arrayOf]
    exact Tacenta.UnitLifecycleEstablishResponder.decodeInitial_encodeInitial _ _ _ _ _ _ _
      (by simp [Model.PersistedState.SessionState.encodeEc, hl])
      (by simp [Model.PersistedState.SessionState.encodeEc, hl])
      (by simp [Model.PersistedState.SessionState.encodeEc, Model.Messages.checkCurve])
      (by simp [Model.PersistedState.SessionState.encodeEc, Model.Messages.checkCurve])
      (by simp [Model.PersistedState.SessionState.encodeEc, Model.Messages.checkKey,
            canonicalKey_arrayOf ai hcani])
      (by simp [Model.PersistedState.SessionState.encodeEc, Model.Messages.checkKey,
            canonicalKey_arrayOf ae hcane])
      (by simp [vecOf]; omega)
  obtain ⟨r, hr, hpost⟩ := Std.WP.spec_imp_exists
    (Tacenta.UnitLifecycleT3.decode_initial_refines_lifecycle msg)
  cases r with
  | Err e =>
      obtain ⟨reason, hreason⟩ := hpost
      rw [hmodel] at hreason
      cases hreason
  | Ok d =>
      rw [hmodel] at hpost
      have hinit := (Except.ok.inj hpost).symm
      refine ⟨d, hr, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · have h := congrArg Model.Messages.Initial.signedPrekeyId hinit
        apply UScalar.eq_of_val_eq
        exact Tacenta.UnitLifecycleEstablishResponder.u32_of_ofNat (by scalar_tac) h
      · have h := congrArg Model.Messages.Initial.oneTimeId hinit
        apply UScalar.eq_of_val_eq
        exact Tacenta.UnitLifecycleEstablishResponder.u32_of_ofNat (by scalar_tac) h
      · have h := congrArg Model.Messages.Initial.kemPrekeyId hinit
        apply UScalar.eq_of_val_eq
        exact Tacenta.UnitLifecycleEstablishResponder.u32_of_ofNat (by scalar_tac) h
      · have h := congrArg Model.Messages.Initial.kemCiphertext hinit
        apply Subtype.ext
        exact Tacenta.UnitLifecycleEstablishResponder.map_u8_inj h
      · exact congrArg Model.Messages.Initial.ratchetMessage hinit
      · exact congrArg Model.Messages.Initial.identity hinit
      · exact congrArg Model.Messages.Initial.ephemeral hinit

/-! ## Each step of the prepare phase at the initiator's frame -/

/-- `decode_ec` of an `EncodeEC` value whose key bytes are a public key's canonical bytes returns that public
key, under the public-key byte round trip. -/
theorem decode_ec_public (hrt : Tacenta.UnitLifecycleSessionCodec.DhPublicBytesRoundTrip)
    {pk : tacenta_boundary.dh.PublicKeyBytes} {a : Array U8 32#usize}
    (ha : tacenta_boundary.dh.PublicKeyBytes.as_bytes pk = ok a)
    (hcan : Tacenta.SessionUnitT1.canonicalX25519 a = true) (s : Slice U8)
    (hs : sliceOf s = Model.PersistedState.SessionState.encodeEc (arrayOf a)) :
    decode_ec s = ok (some pk) := by
  obtain ⟨r, hr, hnone, hsome⟩ := Tacenta.SessionUnitDecodeEc.session_decode_ec_characterization s
  have hdrop : (sliceOf s).drop 1 = arrayOf a := by
    rw [hs]; rfl
  cases r with
  | none =>
      exfalso
      rcases hnone.mp rfl with h | h | h
      · apply h; rw [hs]; simp [Model.PersistedState.SessionState.encodeEc, arrayOf]
      · apply h; rw [hs]; rfl
      · rw [hdrop, canonicalKey_arrayOf a hcan] at h; cases h
  | some k =>
      have hk : k = a := by
        have := hsome k rfl
        rw [hdrop] at this
        apply Subtype.ext
        exact Tacenta.UnitLifecycleEstablishResponder.map_u8_inj this
      subst hk
      obtain ⟨a', ha', hfb⟩ := (Tacenta.UnitLifecycleSessionCodec.dhPublicBytesRoundTrip_is.mp hrt) pk
      rw [ha] at ha'
      cases ha'
      simp [decode_ec, hr, hfb]

/-- `responder_curve_inputs` returns the two decoded keys when both decode and the identity key is valid. -/
theorem curve_inputs_of (identity ephemeral : Slice U8) (pi pe : tacenta_boundary.dh.PublicKeyBytes)
    (hi : decode_ec identity = ok (some pi)) (hvalid : is_valid_identity_key pi = ok true)
    (he : decode_ec ephemeral = ok (some pe)) :
    lifecycle.responder_curve_inputs identity ephemeral = ok (core.result.Result.Ok (pi, pe)) := by
  simp [lifecycle.responder_curve_inputs, hi, hvalid, he]

/-- `Slice::contains` on `u32` decides membership. -/
theorem contains_u32 (l : alloc.vec.Vec U32) (x : U32) :
    core.slice.Slice.contains core.cmp.PartialEqU32 (alloc.vec.Vec.deref l) x = ok (decide (x ∈ l.val)) := by
  simp only [core.slice.Slice.contains, alloc.vec.Vec.deref]
  generalize l.val = xs
  induction xs with
  | nil => rfl
  | cons y ys ih =>
    by_cases hy : x = y
    · subst hy; simp [List.anyM]; rfl
    · simp [List.anyM, hy, ih]

/-- The signed prekey lookup at the store's own signed prekey identifier returns its secret, wrapped. -/
theorem signed_prekey_own (store : lifecycle.PrekeyStore) (z : zeroize.Zeroizing (Array U8 32#usize))
    (hz : zeroize.Zeroizing.new z32 store.signed_prekey_secret = ok z) :
    lifecycle.responder_signed_prekey_secret store store.signed_prekey_id =
      ok (core.result.Result.Ok z) := by
  simp [lifecycle.responder_signed_prekey_secret, hz]

/-- The KEM lookup at the store's last-resort identifier: `LegacyLastResortRecord` when the legacy marker
lists it, otherwise the current key as a last-resort key. -/
theorem kem_slot_last_resort (store : lifecycle.PrekeyStore) :
    lifecycle.responder_kem_slot store store.kem_id =
      ok (if store.kem_id ∈ store.legacy_last_resort_blocked.val
        then core.result.Result.Err lifecycle.Error.LegacyLastResortRecord
        else core.result.Result.Ok (lifecycle.KemKeySlot.Current, true)) := by
  simp only [lifecycle.responder_kem_slot, contains_u32, Aeneas.Std.bind_tc_ok]
  by_cases h : store.kem_id ∈ store.legacy_last_resort_blocked.val <;> simp [h]

/-- The KEM lookup at the identifier of the last one-time KEM entry, when that identifier is not the
last-resort key's or the previous KEM key's and occurs nowhere before: the one-time slot at the last index. -/
theorem kem_slot_one_time (store : lifecycle.PrekeyStore)
    (pre : List KemEntry) (e : KemEntry)
    (hv : store.kem_one_time.val = pre ++ [e]) (hkem : e.1 ≠ store.kem_id)
    (hprev : ∀ x, store.previous_kem = some x → x.2.1 ≠ e.1) (hpre : e.1 ∉ pre.map (·.1)) :
    ∃ i : Usize, i.val = pre.length ∧
      lifecycle.responder_kem_slot store e.1 =
        ok (core.result.Result.Ok (lifecycle.KemKeySlot.OneTime i, false)) := by
  obtain ⟨ids, hids, hidsv⟩ := Std.WP.spec_imp_exists (one_time_kem_ids_spec store)
  have hval : (alloc.vec.Vec.deref ids).val = pre.map (·.1) ++ e.1 :: [] := by
    simp [alloc.vec.Vec.deref, hidsv, hv]
  obtain ⟨r, hr, i, rfl, hi⟩ := Std.WP.spec_imp_exists
    (u32_index_first (alloc.vec.Vec.deref ids) e.1 (pre.map (·.1)) [] hval hpre)
  refine ⟨i, by simpa using hi, ?_⟩
  unfold lifecycle.responder_kem_slot
  rw [if_neg hkem]
  rcases hpk : store.previous_kem with _ | ⟨kp, pid, sig⟩
  · simp only [hids, Aeneas.Std.bind_tc_ok]
    rw [hr]
    rfl
  · have hne : ¬ (pid = e.1) := hprev _ hpk
    simp only [hids, Aeneas.Std.bind_tc_ok]
    rw [hr]
    simp [hne]

/-- Decapsulation at the current key returns what the wrapper's `decapsulate` returns at it. -/
theorem decapsulate_current (store : lifecycle.PrekeyStore) (ct : Slice U8) (ss : Array U8 32#usize)
    (h : tacenta_boundary.kem.decapsulate store.kem ct = ok (core.result.Result.Ok ss)) :
    lifecycle.responder_decapsulate store lifecycle.KemKeySlot.Current ct = ok (core.result.Result.Ok ss) := by
  simp [lifecycle.responder_decapsulate, h]

/-- Decapsulation at the one-time slot of the last index uses the last entry's key pair. -/
theorem decapsulate_one_time (store : lifecycle.PrekeyStore) (pre : List KemEntry) (e : KemEntry)
    (hv : store.kem_one_time.val = pre ++ [e]) (i : Usize) (hi : i.val = pre.length) (ct : Slice U8)
    (ss : Array U8 32#usize)
    (h : tacenta_boundary.kem.decapsulate e.2.1 ct = ok (core.result.Result.Ok ss)) :
    lifecycle.responder_decapsulate store (lifecycle.KemKeySlot.OneTime i) ct =
      ok (core.result.Result.Ok ss) := by
  have hlt : i.val < store.kem_one_time.val.length := by simp [hv, hi]
  have hidx : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice KemEntry) store.kem_one_time i =
      ok e := by
    rw [alloc.vec.Vec.index_slice_index]
    obtain ⟨x, hx, hxv⟩ := Std.WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec store.kem_one_time i hlt)
    rw [hx, hxv]
    simp [hv, hi]
  obtain ⟨id, pair, sig⟩ := e
  simp only [lifecycle.responder_decapsulate]
  rw [hidx]
  simp only [Aeneas.Std.bind_tc_ok]
  simp [h]

/-- The one-time curve lookup at `ABSENT_ID` names no key. -/
theorem one_time_key_absent (store : lifecycle.PrekeyStore) :
    lifecycle.responder_one_time_key store serialization.ABSENT_ID = ok (core.result.Result.Ok none) := by
  simp [lifecycle.responder_one_time_key]

/-- The one-time curve lookup at the identifier of the last pool entry, when that identifier is not
`ABSENT_ID` and occurs nowhere before, returns the private key of that entry's secret, under the zeroizing
round trip. -/
theorem one_time_key_last (hz : Tacenta.SessionUnitBraidT1.ZeroizingArrayRoundTrip)
    (store : lifecycle.PrekeyStore) (v : alloc.vec.Vec PoolEntry)
    (hv : zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref zPool store.one_time = ok v)
    (pre : List PoolEntry) (e : PoolEntry) (hval : v.val = pre ++ [e])
    (habs : e.1 ≠ serialization.ABSENT_ID) (hpre : e.1 ∉ pre.map (·.1)) (k : tacenta_boundary.dh.PrivateKey)
    (hk : tacenta_boundary.dh.PrivateKey.from_bytes e.2 = ok k) :
    lifecycle.responder_one_time_key store e.1 = ok (core.result.Result.Ok (some k)) := by
  obtain ⟨r, hr, z, rfl, hzd⟩ := Std.WP.spec_imp_exists
    (peek_one_time_first hz store e.1 v hv e pre [] (by simpa using hval) rfl hpre)
  simp [lifecycle.responder_one_time_key, habs, hr, hzd, hk]

/-! ### The distinct identifiers, at the entries `publish` names -/

/-- Two parts of a list without repeats share no element. -/
theorem nodup_append_disjoint {α : Type} {l1 l2 : List α} (h : (l1 ++ l2).Nodup) {a : α}
    (h1 : a ∈ l1) (h2 : a ∈ l2) : False :=
  (List.nodup_append.mp h).2.2 a h1 a h2 rfl

/-- At a store with distinct identifiers, the last one-time KEM entry's identifier is not the last-resort
key's, not the previous KEM key's, and occurs nowhere earlier among the one-time KEM entries. -/
theorem distinct_kem_last {store : lifecycle.PrekeyStore} (hd : PrekeyIdsDistinct store)
    {pre : List KemEntry} {e : KemEntry} (hv : store.kem_one_time.val = pre ++ [e]) :
    e.1 ≠ store.kem_id ∧ (∀ x, store.previous_kem = some x → x.2.1 ≠ e.1) ∧ e.1 ∉ pre.map (·.1) := by
  obtain ⟨w, -, hnd, -⟩ := hd
  have hK : e.1 ∈ store.kem_one_time.val.map (·.1) := by simp [hv]
  unfold storeIds at hnd
  simp only [List.append_assoc] at hnd
  rw [List.nodup_cons, List.nodup_cons] at hnd
  obtain ⟨-, hb, hrest⟩ := hnd
  have hrest2 := (List.nodup_append.mp hrest).2.1
  have hrest3 := (List.nodup_append.mp hrest2).2.1
  have hKn := (List.nodup_append.mp hrest3).2.1
  refine ⟨fun heq => hb ?_, fun x hx heq => ?_, fun hmem => ?_⟩
  · rw [← heq]
    exact List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _ hK))
  · have hd' : x.2.1 ∈ (store.previous_kem.map (·.2.1)).toList := by simp [hx]
    refine nodup_append_disjoint hrest2 hd' ?_
    rw [heq]; exact List.mem_append_right _ hK
  · rw [hv, List.map_append] at hKn
    exact nodup_append_disjoint hKn hmem (by simp)

/-- At a store with distinct identifiers, the last one-time curve entry's identifier is not `ABSENT_ID` and
occurs nowhere earlier in the pool. -/
theorem distinct_pool_last {store : lifecycle.PrekeyStore} (hd : PrekeyIdsDistinct store)
    {v : alloc.vec.Vec PoolEntry}
    (hv : zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref zPool store.one_time = ok v)
    {pre : List PoolEntry} {e : PoolEntry} (hval : v.val = pre ++ [e]) :
    e.1 ≠ serialization.ABSENT_ID ∧ e.1 ∉ pre.map (·.1) := by
  obtain ⟨w, hw, hnd, habs⟩ := hd
  rw [hv] at hw
  cases hw
  have hP : e.1 ∈ v.val.map (·.1) := by simp [hval]
  have hmemIds : e.1 ∈ storeIds store v.val := by
    unfold storeIds
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_left _
      (List.mem_append_right _ hP)))
  refine ⟨fun heq => habs (heq ▸ hmemIds), fun hmem => ?_⟩
  unfold storeIds at hnd
  simp only [List.append_assoc] at hnd
  rw [List.nodup_cons, List.nodup_cons] at hnd
  obtain ⟨-, -, hrest⟩ := hnd
  have hrest3 := (List.nodup_append.mp (List.nodup_append.mp hrest).2.1).2.1
  have hPn := (List.nodup_append.mp hrest3).1
  rw [hval, List.map_append] at hPn
  exact nodup_append_disjoint hPn hmem (by simp)

/-- At a store with distinct identifiers, the key pair the store holds under the last one-time KEM entry's
identifier is that entry's. -/
theorem heldKemPair_last {store : lifecycle.PrekeyStore} (hd : PrekeyIdsDistinct store)
    {pre : List KemEntry} {e : KemEntry} (hv : store.kem_one_time.val = pre ++ [e]) :
    heldKemPair store e.1 = some e.2.1 := by
  obtain ⟨hk, -, hpre⟩ := distinct_kem_last hd hv
  unfold heldKemPair
  rw [if_neg hk, hv, List.find?_append]
  have : pre.find? (fun x => decide (x.1 = e.1)) = none := by
    rw [List.find?_eq_none]
    intro x hx hc
    exact hpre (List.mem_map.mpr ⟨x, hx, of_decide_eq_true hc⟩)
  simp [this]

/-- The replay record's loop, from the start with the flag cleared, returns the store's own fields and whether
some entry of the record holds the fingerprint. -/
theorem replay_loop_flag (store : lifecycle.PrekeyStore) (fp : Array U8 32#usize) :
    lifecycle.responder_replay_fingerprint_loop store fp false 0#usize ⦃ fun r =>
      r = (store.identity_public, store.signed_prekey_secret, store.signed_prekey_id,
        store.signed_prekey_sig, store.one_time, store.kem, store.kem_id, store.kem_sig,
        store.kem_one_time, store.previous_signed_prekey, store.previous_kem, store.next_id,
        store.last_resort_seen, store.legacy_last_resort_blocked,
        decide (∃ x ∈ store.last_resort_seen.val, x.2 = fp)) ⦄ := by
  unfold lifecycle.responder_replay_fingerprint_loop
  apply loop.spec_decr_nat
    (measure := fun (q : Bool × Usize) => store.last_resort_seen.val.length - q.2.val)
    (inv := fun (q : Bool × Usize) => q.2.val ≤ store.last_resort_seen.val.length ∧
      q.1 = decide (∃ x ∈ store.last_resort_seen.val.take q.2.val, x.2 = fp))
  · rintro ⟨replayed, index⟩ ⟨hi, hr⟩
    simp only at hr hi
    change lifecycle.responder_replay_fingerprint_loop.body store fp replayed index ⦃ _ ⦄
    simp only [lifecycle.responder_replay_fingerprint_loop.body]
    split
    · rename_i hlt
      have hlt' : index.val < store.last_resort_seen.val.length := by
        simpa [alloc.vec.Vec.len] using hlt
      have hidx : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice (U32 × Array U8 32#usize))
          store.last_resort_seen index = ok (store.last_resort_seen.val[index.val]'hlt') := by
        rw [alloc.vec.Vec.index_slice_index]
        obtain ⟨x, hx, hxv⟩ := Std.WP.spec_imp_exists
          (alloc.vec.Vec.index_usize_spec store.last_resort_seen index hlt')
        rw [hx, hxv]
      rw [hidx]
      simp only [Aeneas.Std.bind_tc_ok]
      try dsimp only [Aeneas.Std.uncurry]
      rw [Tacenta.UnitLifecycleEstablishResponder.array_eq_decide]
      simp only [Aeneas.Std.bind_tc_ok]
      have hu := Tacenta.UnitHeadroomSatisfiable.usize_max_ge
      have hmax : store.last_resort_seen.val.length ≤ Usize.max := store.last_resort_seen.property
      obtain ⟨i1, hi1, hi1v⟩ := Std.WP.spec_imp_exists (Usize.add_spec (x := index) (y := 1#usize)
        (by simp; omega))
      have hi1v' : i1.val = index.val + 1 := by simpa using hi1v
      have htake : store.last_resort_seen.val.take i1.val =
          store.last_resort_seen.val.take index.val ++ [store.last_resort_seen.val[index.val]'hlt'] := by
        rw [hi1v', List.take_add_one, List.getElem?_eq_getElem hlt']
        rfl
      by_cases heq : (store.last_resort_seen.val[index.val]'hlt').2 = fp
      · rw [if_pos (by simpa using heq)]
        simp only [Aeneas.Std.bind_tc_ok]
        rw [hi1]
        simp only [Aeneas.Std.bind_tc_ok, WP.spec_ok]
        refine ⟨⟨by omega, ?_⟩, by omega⟩
        rw [htake]
        exact (decide_eq_true ⟨_, List.mem_append_right _ (List.mem_singleton_self _), heq⟩).symm
      · rw [if_neg (by simpa using heq)]
        simp only [Aeneas.Std.bind_tc_ok]
        rw [hi1]
        simp only [Aeneas.Std.bind_tc_ok, WP.spec_ok]
        refine ⟨⟨by omega, ?_⟩, by omega⟩
        rw [htake, hr]
        apply decide_eq_decide.mpr
        constructor
        · rintro ⟨x, hx, hx2⟩; exact ⟨x, List.mem_append_left _ hx, hx2⟩
        · rintro ⟨x, hx, hx2⟩
          rcases List.mem_append.mp hx with hx | hx
          · exact ⟨x, hx, hx2⟩
          · rw [List.mem_singleton] at hx; subst hx; exact absurd hx2 heq
    · rename_i hge
      simp only [WP.spec_ok]
      have : index.val = store.last_resort_seen.val.length := by
        have : ¬ index.val < store.last_resort_seen.val.length := by
          simpa [alloc.vec.Vec.len] using hge
        omega
      rw [hr, this, List.take_length]
  · exact ⟨by simp, by simp⟩

/-- **Why the replay check refuses** on the last-resort path: it computed the handshake's fingerprint, and
either the record already holds an entry with that fingerprint (`ReplayedLastResort`), or no entry holds it and
the key's count in the record, `last_resort_seen_for`, is at least `MAX_LAST_RESORT_SEEN`, the record then not
being empty (`LastResortRecordFull`). -/
theorem replay_refusal_cause (store : lifecycle.PrekeyStore) (kemId : U32) (sk : Array U8 32#usize)
    (e : lifecycle.Error)
    (h : lifecycle.responder_replay_fingerprint store kemId sk true = ok (core.result.Result.Err e)) :
    ∃ fp, lifecycle.last_resort_fingerprint sk = ok fp ∧
      ((e = lifecycle.Error.ReplayedLastResort ∧ ∃ x ∈ store.last_resort_seen.val, x.2 = fp) ∨
        (e = lifecycle.Error.LastResortRecordFull ∧ (¬ ∃ x ∈ store.last_resort_seen.val, x.2 = fp) ∧
          store.last_resort_seen.val ≠ [] ∧
          ∃ n, lifecycle.PrekeyStore.last_resort_seen_for store kemId = ok n ∧
            lifecycle.MAX_LAST_RESORT_SEEN ≤ n)) := by
  unfold lifecycle.responder_replay_fingerprint at h
  rw [if_pos rfl] at h
  obtain ⟨fp, hfp, h⟩ := bind_eq_ok_inv h
  refine ⟨fp, hfp, ?_⟩
  obtain ⟨r, hr, rfl⟩ := Std.WP.spec_imp_exists (replay_loop_flag store fp)
  rw [hr, Aeneas.Std.bind_tc_ok] at h
  by_cases hex : ∃ x ∈ store.last_resort_seen.val, x.2 = fp
  · rw [decide_eq_true hex] at h
    have h' : (ok (core.result.Result.Err lifecycle.Error.ReplayedLastResort) :
        Result (core.result.Result (Option (Array U8 32#usize)) lifecycle.Error)) =
        ok (core.result.Result.Err e) := h
    simp only [ok.injEq, core.result.Result.Err.injEq] at h'
    exact Or.inl ⟨h'.symm, hex⟩
  · rw [decide_eq_false hex] at h
    have h' : (do
        let i3 ← lifecycle.PrekeyStore.last_resort_seen_for store kemId
        if i3 ≥ lifecycle.MAX_LAST_RESORT_SEEN then
          ok (core.result.Result.Err lifecycle.Error.LastResortRecordFull)
        else ok (core.result.Result.Ok (some fp))) = ok (core.result.Result.Err e) := h
    obtain ⟨i3, hi3', h⟩ := bind_eq_ok_inv h'
    split at h
    · rename_i hge
      simp only [ok.injEq, core.result.Result.Err.injEq] at h
      refine Or.inr ⟨h.symm, hex, fun hseen => ?_, i3, hi3', hge⟩
      have hcount : i3 = 0#usize := by
        unfold lifecycle.PrekeyStore.last_resort_seen_for lifecycle.PrekeyStore.last_resort_seen_for_loop
          at hi3'
        rw [loop.eq_def] at hi3'
        simp [lifecycle.PrekeyStore.last_resort_seen_for_loop.body, alloc.vec.Vec.len, hseen] at hi3'
        exact hi3'.symm
      subst hcount
      simp [lifecycle.MAX_LAST_RESORT_SEEN] at hge
    · simp at h

/-! ## The call at the initiator's frame -/

/-- A refusal of the KEM lookup, after the message decoded and the signed prekey was found, is the call's
refusal, with the store and the source as given. -/
theorem establish_responder_slot_refused {E : Type} (rcB : rand_core_1.RngCore E)
    (crcB : rand_core_1.CryptoRng E) (ourB : lifecycle.Identity) (store : lifecycle.PrekeyStore)
    (msg : Slice U8) (rng : E) (d : tacenta_wire.DecodedInitial)
    (hd : tacenta_wire.decode_initial msg = ok (core.result.Result.Ok d))
    (zs : zeroize.Zeroizing (Array U8 32#usize))
    (hs : lifecycle.responder_signed_prekey_secret store d.signed_prekey_id = ok (core.result.Result.Ok zs))
    (e : lifecycle.Error)
    (hk : lifecycle.responder_kem_slot store d.kem_prekey_id = ok (core.result.Result.Err e)) :
    lifecycle.establish_responder rcB crcB ourB store msg rng = ok (core.result.Result.Err e, store, rng) := by
  unfold lifecycle.establish_responder
  rw [hd]
  simp only [Aeneas.Std.bind_tc_ok, hs, hk, core.result.Result.Insts.CoreOpsTry.branch]
  rfl

/-- A refusal of the replay check, after every earlier step of the prepare phase returned, is the call's
refusal, with the store and the source as given. -/
theorem establish_responder_replay_refused_at {E : Type} (rcB : rand_core_1.RngCore E)
    (crcB : rand_core_1.CryptoRng E) (ourB : lifecycle.Identity) (store : lifecycle.PrekeyStore)
    (msg : Slice U8) (rng : E) (d : tacenta_wire.DecodedInitial)
    (hd : tacenta_wire.decode_initial msg = ok (core.result.Result.Ok d))
    (zs : zeroize.Zeroizing (Array U8 32#usize))
    (hs : lifecycle.responder_signed_prekey_secret store d.signed_prekey_id = ok (core.result.Result.Ok zs))
    (slot : lifecycle.KemKeySlot) (lr : Bool)
    (hslot : lifecycle.responder_kem_slot store d.kem_prekey_id = ok (core.result.Result.Ok (slot, lr)))
    (pi pe : tacenta_boundary.dh.PublicKeyBytes)
    (hcurve : lifecycle.responder_curve_inputs (alloc.vec.Vec.deref d.identity)
      (alloc.vec.Vec.deref d.ephemeral) = ok (core.result.Result.Ok (pi, pe)))
    (otk : Option tacenta_boundary.dh.PrivateKey)
    (hone : lifecycle.responder_one_time_key store d.one_time_prekey_id = ok (core.result.Result.Ok otk))
    (ks : Array U8 32#usize)
    (hdec : lifecycle.responder_decapsulate store slot (alloc.vec.Vec.deref d.kem_ciphertext) =
      ok (core.result.Result.Ok ks))
    (ksz : zeroize.Zeroizing (Array U8 32#usize)) (hksz : zeroize.Zeroizing.new z32 ks = ok ksz)
    (sb : Array U8 32#usize) (hsb : zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref z32 zs = ok sb)
    (spk : tacenta_boundary.dh.PrivateKey) (hspk : tacenta_boundary.dh.PrivateKey.from_bytes sb = ok spk)
    (ik : tacenta_boundary.dh.PrivateKey) (hik : lifecycle.Identity.dh_key ourB = ok ik)
    (enc : Array U8 32#usize) (henc : zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref z32 ksz = ok enc)
    (sh : Array U8 32#usize)
    (hsh : responder_shared_secret ik spk otk pi pe enc = ok (core.result.Result.Ok sh))
    (shz : zeroize.Zeroizing (Array U8 32#usize)) (hshz : zeroize.Zeroizing.new z32 sh = ok shz)
    (shb : Array U8 32#usize) (hshb : zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref z32 shz = ok shb)
    (e : lifecycle.Error)
    (hrep : lifecycle.responder_replay_fingerprint store d.kem_prekey_id shb lr =
      ok (core.result.Result.Err e)) :
    lifecycle.establish_responder rcB crcB ourB store msg rng = ok (core.result.Result.Err e, store, rng) := by
  unfold lifecycle.establish_responder
  rw [hd]
  simp only [Aeneas.Std.bind_tc_ok, hs, hslot, core.result.Result.Insts.CoreOpsTry.branch,
    Tacenta.UnitLifecycleT1.copy_bool_eq]
  try dsimp only [Aeneas.Std.uncurry]
  simp only [Aeneas.Std.bind_tc_ok, hcurve, hone]
  try dsimp only [Aeneas.Std.uncurry]
  simp only [Aeneas.Std.bind_tc_ok, hdec, hksz, hsb, hspk]
  rcases otk with _ | k <;>
  · simp only [hik, henc, hsh, Aeneas.Std.bind_tc_ok, hshz, hshb, hrep]
    rfl

/-- Parts for the call, from every step of the prepare phase up to an accepted replay check: the remaining
steps (the Triple and the Braid built from the secret, the identity, the associated data and the copy of the
ephemeral key) return under the contracts of `establish_responder_no_panic`. -/
theorem parts_of_steps {E : Type} (rcB : rand_core_1.RngCore E)
    (contracts : Tacenta.UnitLifecycleT1.EstablishResponderContracts rcB)
    (ourB : lifecycle.Identity) (store : lifecycle.PrekeyStore) (msg : Slice U8)
    (d : tacenta_wire.DecodedInitial)
    (hd : tacenta_wire.decode_initial msg = ok (core.result.Result.Ok d))
    (zs : zeroize.Zeroizing (Array U8 32#usize))
    (hs : lifecycle.responder_signed_prekey_secret store d.signed_prekey_id = ok (core.result.Result.Ok zs))
    (slot : lifecycle.KemKeySlot) (lr : Bool)
    (hslot : lifecycle.responder_kem_slot store d.kem_prekey_id = ok (core.result.Result.Ok (slot, lr)))
    (pi pe : tacenta_boundary.dh.PublicKeyBytes)
    (hcurve : lifecycle.responder_curve_inputs (alloc.vec.Vec.deref d.identity)
      (alloc.vec.Vec.deref d.ephemeral) = ok (core.result.Result.Ok (pi, pe)))
    (otk : Option tacenta_boundary.dh.PrivateKey)
    (hone : lifecycle.responder_one_time_key store d.one_time_prekey_id = ok (core.result.Result.Ok otk))
    (ks : Array U8 32#usize)
    (hdec : lifecycle.responder_decapsulate store slot (alloc.vec.Vec.deref d.kem_ciphertext) =
      ok (core.result.Result.Ok ks))
    (ksz : zeroize.Zeroizing (Array U8 32#usize)) (hksz : zeroize.Zeroizing.new z32 ks = ok ksz)
    (sb : Array U8 32#usize) (hsb : zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref z32 zs = ok sb)
    (spk : tacenta_boundary.dh.PrivateKey) (hspk : tacenta_boundary.dh.PrivateKey.from_bytes sb = ok spk)
    (ik : tacenta_boundary.dh.PrivateKey) (hik : lifecycle.Identity.dh_key ourB = ok ik)
    (enc : Array U8 32#usize) (henc : zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref z32 ksz = ok enc)
    (sh : Array U8 32#usize)
    (hsh : responder_shared_secret ik spk otk pi pe enc = ok (core.result.Result.Ok sh))
    (shz : zeroize.Zeroizing (Array U8 32#usize)) (hshz : zeroize.Zeroizing.new z32 sh = ok shz)
    (shb : Array U8 32#usize) (hshb : zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref z32 shz = ok shb)
    (r : Option (Array U8 32#usize))
    (hrep : lifecycle.responder_replay_fingerprint store d.kem_prekey_id shb lr =
      ok (core.result.Result.Ok r))
    (sl : Slice U8) (hsl : fullSlice shb = ok sl) :
    ∃ p : ResponderPreparedParts ourB store msg, p.decoded = d ∧ p.lastResort = lr ∧
      p.peerIdentity = pi ∧ p.peerEphemeral = pe ∧ p.oneTime = otk ∧ p.kemSecret = ks ∧
      p.signedPrekey = spk ∧ p.shared = sh ∧ p.secret = shb ∧ p.tripleSecret = sl ∧ p.braidSecret = sl := by
  let _ : Tacenta.SessionUnitSessionT1.ZeroizingModel := contracts.sessionZeroizing
  have hdh := contracts.decrypt.dhCodec
  have hz := contracts.decrypt.braid.zeroizingArray
  obtain ⟨rp, hrp, -⟩ := Std.WP.spec_imp_exists
    (Tacenta.UnitLifecycleT1.private_key_public_no_panic hdh spk)
  obtain ⟨rb, hrb, -⟩ := Std.WP.spec_imp_exists
    (Tacenta.UnitLifecycleT1.public_key_as_bytes_no_panic hdh rp)
  obtain ⟨triple, htriple, -⟩ := Std.WP.spec_imp_exists
    (Tacenta.SessionUnitTripleT1.State.init_receiver_no_panic contracts.decrypt.triple.hkdf
      contracts.decrypt.triple.zeroizing contracts.spqrKdfInit contracts.decrypt.triple.spqrZeroize sl rb
      tacenta_ratchet.LabelSet.Tacenta)
  obtain ⟨braid, hbraid, -⟩ := Std.WP.spec_imp_exists
    (Tacenta.SessionUnitBraidT1.Braid.responder_no_panic contracts.decrypt.braid.hkdf hz
      contracts.decrypt.braid.decoderNew contracts.decrypt.braid.headerLen sl)
  obtain ⟨op, hop, -⟩ := Std.WP.spec_imp_exists (Tacenta.UnitLifecycleT1.identity_public_no_panic hdh ourB)
  obtain ⟨ad, had, -⟩ := Std.WP.spec_imp_exists (Tacenta.UnitLifecycleT1.identity_ad_no_panic hdh pi op)
  obtain ⟨ec, hec, -⟩ := Std.WP.spec_imp_exists
    (Tacenta.SessionUnitBraidT1.vecU8_clone_no_panic d.ephemeral)
  refine ⟨
    { decoded := d, signedSecret := zs, kemSlot := slot, lastResort := lr, peerIdentity := pi,
      peerEphemeral := pe, oneTime := otk, kemSecret := ks, kemSecretZ := ksz, signedBytes := sb,
      signedPrekey := spk, shared := sh, secretZ := shz, secret := shb, replay := r, tripleSecret := sl,
      ratchetPublic := rp, ratchetBytes := rb, triple := triple, braidSecret := sl, braid := braid,
      ratchetPrivate := spk, ourPublic := op, identityAd := ad, ephemeralCopy := ec,
      hDecode := hd, hSigned := hs, hSlot := hslot, hCurve := hcurve, hOneTime := hone, hDecaps := hdec,
      hKemSecretZ := hksz, hSignedBytes := hsb, hSignedPrekey := hspk,
      hShared := ⟨ik, enc, hik, henc, hsh⟩, hSecretZ := hshz, hSecret := hshb, hReplay := hrep,
      hTripleSecret := hsl, hRatchetPublic := hrp, hRatchetBytes := hrb, hTriple := htriple,
      hBraidSecret := hsl, hBraid := hbraid, hRatchetPrivate := hspk, hOurPublic := hop,
      hIdentityAd := had, hEphemeralCopy := hec },
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The refusals the responder's store decides at the initiator's frame, each with what in the store decides
it: the legacy marker lists the last-resort key; the replay record already holds the fingerprint of this
handshake's secret; or no entry holds it, the record is not empty, and the key's count in it (`last_resort_seen_for`, the
count the code compares) is at least `MAX_LAST_RESORT_SEEN`. -/
def StoreRefusal (store : lifecycle.PrekeyStore) (secret : Array U8 32#usize) (e : lifecycle.Error) : Prop :=
  (e = lifecycle.Error.LegacyLastResortRecord ∧ store.kem_id ∈ store.legacy_last_resort_blocked.val) ∨
    (e = lifecycle.Error.ReplayedLastResort ∧ ∃ fp, lifecycle.last_resort_fingerprint secret = ok fp ∧
      ∃ x ∈ store.last_resort_seen.val, x.2 = fp) ∨
    (e = lifecycle.Error.LastResortRecordFull ∧
      (∃ fp, lifecycle.last_resort_fingerprint secret = ok fp ∧ ¬ ∃ x ∈ store.last_resort_seen.val, x.2 = fp) ∧
      store.last_resort_seen.val ≠ [] ∧
      ∃ n, lifecycle.PrekeyStore.last_resort_seen_for store store.kem_id = ok n ∧
        lifecycle.MAX_LAST_RESORT_SEEN ≤ n)

/-- **`establish_responder` on the initiator's first frame**, for every record `q` of a successful
`establish_initiator_for` run (identity, bundle, source), every frame the initial message carries, every
responder identity whose public key is the store's and every prekey store whose `publish` returned the bundle
the initiator used, whose identifiers are distinct (`PrekeyIdsDistinct`) and whose KEM key pair under the
named identifier decapsulates the initiator's ciphertext to the initiator's secret (`FirstKemAgrees`), and
every source of randomness: either

* the bundle names the store's last-resort KEM key and the call refuses with one of the three refusals the
  store decides (`StoreRefusal`), returning the store and the source as given; or
* the prepare phase reaches the inner receive with parts `p` whose shared secret, its zeroized bytes and its
  slice are the initiator's, whose peer keys are the initiator's identity key and pending ephemeral key,
  whose decapsulated secret is the initiator's encapsulated secret and whose frame is the one the message
  carries; `p.lastResort` holds exactly when the bundle names the last-resort key.

Under the contracts of `establish_responder_no_panic`, `DhPublicValid`, the agreement law `DhAgreeSymmetric`,
the public-key byte round trip, the view's codec relation and the two ciphertext-length laws. -/
theorem responder_first_frame_prepares {E : Type} (rcB : rand_core_1.RngCore E)
    (crcB : rand_core_1.CryptoRng E) (contracts : Tacenta.UnitLifecycleT1.EstablishResponderContracts rcB)
    (hpub : DhPublicValid) (hsym : DhAgreeSymmetric)
    (hrt : Tacenta.UnitLifecycleSessionCodec.DhPublicBytesRoundTrip)
    (hct : Tacenta.UnitLifecycleEstablishInitiatorShape.KemCiphertextLenOf)
    (hbound : Tacenta.UnitLifecycleRestoredSession.KemCiphertextLenBound)
    {dh : DhView} (codec : DhCodecOf dh)
    (q : InitiatorSecretParts rc crc our bundle) (pending : Model.Lifecycle.PendingInitial)
    (hpend : (establishedModelOf dh q.session).pendingInitial = some pending)
    (frame : Model.Lifecycle.Bytes) (msg : Slice U8)
    (hmsg : sliceOf msg = Tacenta.UnitLifecycleEstablishedEncrypt.initialWire
      (establishedModelOf dh q.session) pending frame)
    (ourB : lifecycle.Identity) (storeB : lifecycle.PrekeyStore)
    (hpublish : lifecycle.PrekeyStore.publish storeB = ok bundle)
    (hidentity : lifecycle.Identity.public ourB = ok storeB.identity_public)
    (hdistinct : PrekeyIdsDistinct storeB)
    (hkem : FirstKemAgrees storeB bundle.kem_prekey_id q.kemCiphertext q.kemSecret) (rngB : E) :
    (bundle.kem_prekey_id = storeB.kem_id ∧ ∃ e, StoreRefusal storeB q.sharedBytes e ∧
        lifecycle.establish_responder rcB crcB ourB storeB msg rngB =
          ok (core.result.Result.Err e, storeB, rngB)) ∨
      ∃ p : ResponderPreparedParts ourB storeB msg,
        p.shared = q.shared ∧ p.secret = q.sharedBytes ∧ p.tripleSecret = q.sharedSlice ∧
        p.braidSecret = q.sharedSlice ∧ p.peerIdentity = q.ourPublic ∧
        p.peerEphemeral = q.ephemeralPublic ∧ p.kemSecret = q.kemSecret ∧
        sliceOf (ResponderPreparedParts.message p) = frame ∧
        (p.lastResort = true ↔ bundle.kem_prekey_id = storeB.kem_id) := by
  have hz := contracts.decrypt.braid.zeroizingArray
  have hdh := contracts.decrypt.dhCodec
  obtain ⟨d, hd, hdsid, hdoid, hdkid, hdct, hdmsg, hdid, hdeph⟩ :=
    decode_first_frame hpub codec hct hbound q pending hpend frame msg hmsg
  obtain ⟨hpsid, hpik, ⟨spk, hspkB, hspkPub⟩, hkemArm, ⟨v, hv, hotArm⟩⟩ :=
    publish_parts storeB bundle hpublish
  -- the signed prekey
  obtain ⟨zs, hzs, hzsd⟩ := hz 32#usize z32 storeB.signed_prekey_secret
  have hSigned : lifecycle.responder_signed_prekey_secret storeB d.signed_prekey_id =
      ok (core.result.Result.Ok zs) := by
    rw [hdsid, hpsid]; exact signed_prekey_own storeB zs hzs
  -- the two curve keys
  have hikA := identity_public_of_dh_key q.hDhKey q.hOurPublic
  obtain ⟨ai, hai, hcani, hvi⟩ := view_of_public hpub codec hikA
  obtain ⟨ae, hae, hcane, hve⟩ := view_of_public hpub codec q.hEphemeralPublic
  have hvalidA : is_valid_identity_key q.ourPublic = ok true :=
    Tacenta.UnitLifecycleEstablishInitiatorShape.identity_public_valid hpub q.hOurPublic
  have hCurve : lifecycle.responder_curve_inputs (alloc.vec.Vec.deref d.identity)
      (alloc.vec.Vec.deref d.ephemeral) = ok (core.result.Result.Ok (q.ourPublic, q.ephemeralPublic)) :=
    curve_inputs_of _ _ _ _ (decode_ec_public hrt hai hcani _ (by rw [hdid, hvi])) hvalidA
      (decode_ec_public hrt hae hcane _ (by rw [hdeph, hve]))
  -- the one-time curve prekey
  obtain ⟨otk, hOneTime, hmatch⟩ : ∃ otk, lifecycle.responder_one_time_key storeB d.one_time_prekey_id =
      ok (core.result.Result.Ok otk) ∧ OneTimeMatches bundle.bundle.one_time_prekey otk := by
    rw [hdoid]
    rcases hotArm with ⟨hid, hnone⟩ | ⟨e, k, pk, hlast, hid, hk, hpk, hsome⟩
    · exact ⟨none, by rw [hid]; exact one_time_key_absent storeB, Or.inl ⟨hnone, rfl⟩⟩
    · obtain ⟨pre, hpre⟩ := List.getLast?_eq_some_iff.mp hlast
      obtain ⟨habs, hnot⟩ := distinct_pool_last hdistinct hv hpre
      exact ⟨some k, by rw [hid]; exact one_time_key_last hz storeB v hv pre e hpre habs hnot k hk,
        Or.inr ⟨k, pk, rfl, hpk, hsome⟩⟩
  -- the shared secret
  obtain ⟨ikB, hikB, -⟩ := Std.WP.spec_imp_exists (Tacenta.UnitLifecycleT1.identity_dh_key_no_panic hdh ourB)
  have hikBpub : tacenta_boundary.dh.PrivateKey.public_key ikB = ok bundle.bundle.identity_key := by
    rw [hpik]; exact identity_public_of_dh_key hikB hidentity
  have hShared : responder_shared_secret ikB spk otk q.ourPublic q.ephemeralPublic q.encapsulated =
      ok (core.result.Result.Ok q.shared) :=
    (shared_secret_symmetric hsym q.identityKey q.ephemeral ikB spk q.ourPublic q.ephemeralPublic
      bundle.bundle otk q.encapsulated hikA q.hEphemeralPublic hikBpub hspkPub hmatch q.hVerify
      hvalidA).trans q.hShared
  obtain ⟨pair, hheld, hdec⟩ := hkem
  rw [← hdct] at hdec
  have hshz := q.hSharedZ
  have hshb := q.hSharedBytes
  rcases hkemArm with ⟨hkid, -⟩ | ⟨e, hlast, hkid, -⟩
  · -- the last-resort path
    have hpair : pair = storeB.kem := by
      simp only [heldKemPair, hkid, if_true, Option.some.injEq] at hheld
      exact hheld.symm
    subst hpair
    have hslot : lifecycle.responder_kem_slot storeB d.kem_prekey_id =
        ok (if storeB.kem_id ∈ storeB.legacy_last_resort_blocked.val
          then core.result.Result.Err lifecycle.Error.LegacyLastResortRecord
          else core.result.Result.Ok (lifecycle.KemKeySlot.Current, true)) := by
      rw [hdkid, hkid]; exact kem_slot_last_resort storeB
    by_cases hleg : storeB.kem_id ∈ storeB.legacy_last_resort_blocked.val
    · rw [if_pos hleg] at hslot
      exact Or.inl ⟨hkid, _, Or.inl ⟨rfl, hleg⟩,
        establish_responder_slot_refused rcB crcB ourB storeB msg rngB d hd zs hSigned _ hslot⟩
    · rw [if_neg hleg] at hslot
      have hDecaps := decapsulate_current storeB _ q.kemSecret hdec
      obtain ⟨r6, hr6, -⟩ := Std.WP.spec_imp_exists
        (Tacenta.UnitLifecycleT1.responder_replay_fingerprint_no_panic contracts.decrypt.triple.hmac storeB
          d.kem_prekey_id q.sharedBytes true)
      cases r6 with
      | Err e =>
          obtain ⟨fp, hfp, he⟩ := replay_refusal_cause _ _ _ _ hr6
          refine Or.inl ⟨hkid, e, ?_, ?_⟩
          · rcases he with ⟨rfl, hx⟩ | ⟨rfl, hne⟩
            · exact Or.inr (Or.inl ⟨rfl, fp, hfp, hx⟩)
            · obtain ⟨hnx, hne', n, hn, hle⟩ := hne
              rw [hdkid, hkid] at hn
              exact Or.inr (Or.inr ⟨rfl, ⟨fp, hfp, hnx⟩, hne', n, hn, hle⟩)
          exact establish_responder_replay_refused_at rcB crcB ourB storeB msg rngB d hd zs hSigned _ _ hslot
            _ _ hCurve otk hOneTime _ hDecaps _ q.hKemSecretZ _ hzsd spk hspkB ikB hikB _ q.hEncapsulated
            _ hShared _ hshz _ hshb e hr6
      | Ok r =>
          obtain ⟨p, hpd, hplr, hppi, hppe, -, hpks, -, hpsh, hpsec, hpts, hpbs⟩ :=
            parts_of_steps rcB contracts ourB storeB msg d hd zs hSigned _ _ hslot _ _ hCurve otk hOneTime _
              hDecaps _ q.hKemSecretZ _ hzsd spk hspkB ikB hikB _ q.hEncapsulated _ hShared _ hshz _ hshb r
              hr6 _ q.hSharedSlice
          refine Or.inr ⟨p, hpsh, hpsec, hpts, hpbs, hppi, hppe, hpks, ?_, ?_⟩
          · simp only [ResponderPreparedParts.message, hpd]; exact hdmsg
          · rw [hplr]; exact ⟨fun _ => hkid, fun _ => rfl⟩
  · -- the one-time path
    obtain ⟨pre, hpre⟩ := List.getLast?_eq_some_iff.mp hlast
    obtain ⟨hne, hprev, hnot⟩ := distinct_kem_last hdistinct hpre
    have hpair : pair = e.2.1 := by
      rw [hkid, heldKemPair_last hdistinct hpre] at hheld
      exact (Option.some.inj hheld).symm
    subst hpair
    obtain ⟨i, hi, hslot⟩ := kem_slot_one_time storeB pre e hpre hne hprev hnot
    rw [← hkid, ← hdkid] at hslot
    have hDecaps := decapsulate_one_time storeB pre e hpre i hi _ q.kemSecret hdec
    have hr6 : lifecycle.responder_replay_fingerprint storeB d.kem_prekey_id q.sharedBytes false =
        ok (core.result.Result.Ok none) := by
      simp [lifecycle.responder_replay_fingerprint]
    obtain ⟨p, hpd, hplr, hppi, hppe, -, hpks, -, hpsh, hpsec, hpts, hpbs⟩ :=
      parts_of_steps rcB contracts ourB storeB msg d hd zs hSigned _ _ hslot _ _ hCurve otk hOneTime _
        hDecaps _ q.hKemSecretZ _ hzsd spk hspkB ikB hikB _ q.hEncapsulated _ hShared _ hshz _ hshb none
        hr6 _ q.hSharedSlice
    refine Or.inr ⟨p, hpsh, hpsec, hpts, hpbs, hppi, hppe, hpks, ?_, ?_⟩
    · simp only [ResponderPreparedParts.message, hpd]; exact hdmsg
    · rw [hplr, hkid]
      exact ⟨fun h => absurd h (by simp), fun h => absurd h hne⟩

open Tacenta.UnitHeadroomInvariant (OptionEqU64Shape) in
/-- **At the session the responder reaches the inner receive with, on the initiator's first frame, the
decrypt theorem's session-side hypotheses hold**: `responder_first_frame_prepares` with, in its second arm,
`Session::invariant` of the session, the four counter ceilings and the relation to `responderModelOf dh p`,
from the generic responder route (`responder_prepared_invariant`, `counterHeadroom_responder_prepared`,
`sessionRefines_responder_prepared`), under the recorded `OptionEqU64Shape` and the decrypt agreements
`DecryptRatchetAgreements K`. -/
theorem responder_first_frame_admissible {E : Type} (rcB : rand_core_1.RngCore E)
    (crcB : rand_core_1.CryptoRng E) (contracts : Tacenta.UnitLifecycleT1.EstablishResponderContracts rcB)
    (hpub : DhPublicValid) (hsym : DhAgreeSymmetric)
    (hrt : Tacenta.UnitLifecycleSessionCodec.DhPublicBytesRoundTrip)
    (hct : Tacenta.UnitLifecycleEstablishInitiatorShape.KemCiphertextLenOf)
    (hbound : Tacenta.UnitLifecycleRestoredSession.KemCiphertextLenBound)
    (hoeq : OptionEqU64Shape (@core.option.Option.Insts.CoreCmpPartialEqOption.eq))
    {K : Model.Braid.Kem} (agreements : Tacenta.UnitLifecycleDecryptRatchetT3.DecryptRatchetAgreements K)
    {dh : DhView} (codec : DhCodecOf dh)
    (q : InitiatorSecretParts rc crc our bundle) (pending : Model.Lifecycle.PendingInitial)
    (hpend : (establishedModelOf dh q.session).pendingInitial = some pending)
    (frame : Model.Lifecycle.Bytes) (msg : Slice U8)
    (hmsg : sliceOf msg = Tacenta.UnitLifecycleEstablishedEncrypt.initialWire
      (establishedModelOf dh q.session) pending frame)
    (ourB : lifecycle.Identity) (storeB : lifecycle.PrekeyStore)
    (hpublish : lifecycle.PrekeyStore.publish storeB = ok bundle)
    (hidentity : lifecycle.Identity.public ourB = ok storeB.identity_public)
    (hdistinct : PrekeyIdsDistinct storeB)
    (hkem : FirstKemAgrees storeB bundle.kem_prekey_id q.kemCiphertext q.kemSecret) (rngB : E) :
    (bundle.kem_prekey_id = storeB.kem_id ∧ ∃ e, StoreRefusal storeB q.sharedBytes e ∧
        lifecycle.establish_responder rcB crcB ourB storeB msg rngB =
          ok (core.result.Result.Err e, storeB, rngB)) ∨
      ∃ p : ResponderPreparedParts ourB storeB msg,
        p.shared = q.shared ∧ p.secret = q.sharedBytes ∧ p.tripleSecret = q.sharedSlice ∧
        p.braidSecret = q.sharedSlice ∧ p.peerIdentity = q.ourPublic ∧
        p.peerEphemeral = q.ephemeralPublic ∧ p.kemSecret = q.kemSecret ∧
        sliceOf (ResponderPreparedParts.message p) = frame ∧
        (p.lastResort = true ↔ bundle.kem_prekey_id = storeB.kem_id) ∧
        lifecycle.Session.invariant p.session = ok true ∧
        Tacenta.UnitLifecycleDecryptRunBounds.CounterHeadroom p.session ∧
        SessionRefines dh K p.session (Tacenta.UnitLifecycleEstablishResponder.responderModelOf dh p) := by
  rcases responder_first_frame_prepares rcB crcB contracts hpub hsym hrt hct hbound codec q pending hpend
      frame msg hmsg ourB storeB hpublish hidentity hdistinct hkem rngB with hl |
    ⟨p, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  · exact Or.inl hl
  · exact Or.inr ⟨p, h1, h2, h3, h4, h5, h6, h7, h8, h9,
      Tacenta.UnitLifecycleEstablishResponder.responder_prepared_invariant hpub hoeq contracts.divCeilValue
        contracts.decrypt.braid.headerLen p,
      Tacenta.UnitLifecycleEstablishResponder.counterHeadroom_responder_prepared p,
      Tacenta.UnitLifecycleEstablishResponder.sessionRefines_responder_prepared agreements.erasure
        agreements.kemLen (Tacenta.UnitLifecycleT3.braid_kdf_contracts_of_session agreements.hmac
          agreements.hkdf).2 contracts.decrypt.braid.zeroizingArray contracts.divCeilValue dh p⟩

/-- **The initiator's first send, then `establish_responder` on the bytes it emitted.**  For every successful
`establish_initiator_for` output `s` (any record `q` of that run), every plaintext and source under which
the first `encrypt` at `s` returns bytes (`established_encrypt_outcomes`, success arm), and every responder
identity and prekey store as in `responder_first_frame_prepares`: the bytes are the initial message wrapping
the first ratchet frame for some message key and chunk, and `establish_responder` on them either refuses
with one of the three store-decided refusals, the bundle naming the last-resort key, with the store and the
source as given, or reaches the inner receive with parts whose shared secret is the initiator's and whose
frame is that first ratchet frame; there `Session::invariant`, the four ceilings and the relation to
`responderModelOf dh p` hold.  Under the hypotheses of `established_encrypt_outcomes` (the encrypt boundary
records, the oracle record and the laws `KeyGenSeededFor`, `KemCiphertextLenOf`, `KemCiphertextLenBound`),
those of `responder_first_frame_admissible`, and the per-run premise `FirstKemAgrees`. -/
theorem first_send_responder_prepares [Tacenta.SessionUnitT1.DerivedKeysModel] {E F : Type}
    (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView) (kem : Tacenta.UnitLifecycleT3.KemView)
    (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
    (braid : Tacenta.UnitLifecycleT3.BraidSendRefinementContracts rc oracle.braidKem)
    (triple : Tacenta.UnitLifecycleT3.TripleSendRefinementContracts)
    (aead : Tacenta.UnitLifecycleT1.AeadSealBounded) (dhCodec : Tacenta.UnitLifecycleT1.DhCodecTotal)
    (oracleOf : Tacenta.UnitLifecycleT3.OracleOf rc crc dh kem trace oracle) (codec : DhCodecOf dh)
    (codewordView : Tacenta.UnitLifecycleT3.CodewordViewSendOf view)
    (hz80 : Tacenta.SessionUnitT3.ZeroizingRoundTrips80)
    (hz32 : Tacenta.UnitLifecycleT3.ZeroizingRoundTrips (Array Std.U8 32#usize))
    (hzKeys : Tacenta.UnitLifecycleT3.ZeroizingRoundTrips
      (Array Std.U8 32#usize × Array Std.U8 32#usize × Array Std.U8 16#usize))
    (hgen : Tacenta.UnitLifecycleEstablishedEncrypt.KeyGenSeededFor oracle.braidKem rc crc trace)
    (hct : Tacenta.UnitLifecycleEstablishInitiatorShape.KemCiphertextLenOf)
    (hbound : Tacenta.UnitLifecycleRestoredSession.KemCiphertextLenBound)
    (rcE : rand_core_1.RngCore E) (crcE : rand_core_1.CryptoRng E) (ourA : lifecycle.Identity)
    (bundleA : lifecycle.PublishedBundle) (expected : tacenta_boundary.dh.PublicKeyBytes) (rng0 rng1 : E)
    (s : lifecycle.Session)
    (h : lifecycle.establish_initiator_for rcE crcE ourA bundleA expected rng0 =
      ok (core.result.Result.Ok s, rng1))
    (q : InitiatorSecretParts rcE crcE ourA bundleA) (hq : s = q.session)
    (plaintext : Slice Std.U8) (hroom : plaintext.val.length + 65770 ≤ Usize.max)
    (rng : R) (htrace : trace rng = oracle.draws) (d1 d2 : Model.Lifecycle.Key)
    (rest : List Model.Lifecycle.Key) (hdraws : trace rng = d1 :: d2 :: rest)
    (bytes : alloc.vec.Vec Std.U8) (s' : lifecycle.Session) (rng' : R)
    (hcall : lifecycle.Session.encrypt rc crc s plaintext rng = ok (core.result.Result.Ok bytes, s', rng'))
    (rcB : rand_core_1.RngCore F) (crcB : rand_core_1.CryptoRng F)
    (contracts : Tacenta.UnitLifecycleT1.EstablishResponderContracts rcB)
    (hpub : DhPublicValid) (hsym : DhAgreeSymmetric)
    (hrt : Tacenta.UnitLifecycleSessionCodec.DhPublicBytesRoundTrip)
    (hoeq : Tacenta.UnitHeadroomInvariant.OptionEqU64Shape
      (@core.option.Option.Insts.CoreCmpPartialEqOption.eq))
    {K : Model.Braid.Kem} (agreements : Tacenta.UnitLifecycleDecryptRatchetT3.DecryptRatchetAgreements K)
    (ourB : lifecycle.Identity) (storeB : lifecycle.PrekeyStore)
    (hpublish : lifecycle.PrekeyStore.publish storeB = ok bundleA)
    (hidentity : lifecycle.Identity.public ourB = ok storeB.identity_public)
    (hdistinct : PrekeyIdsDistinct storeB)
    (hkem : FirstKemAgrees storeB bundleA.kem_prekey_id q.kemCiphertext q.kemSecret) (rngB : F) :
    ∃ messageKey chunk,
      (bundleA.kem_prekey_id = storeB.kem_id ∧ ∃ e, StoreRefusal storeB q.sharedBytes e ∧
          lifecycle.establish_responder rcB crcB ourB storeB (alloc.vec.Vec.deref bytes) rngB =
            ok (core.result.Result.Err e, storeB, rngB)) ∨
        ∃ p : ResponderPreparedParts ourB storeB (alloc.vec.Vec.deref bytes),
          p.shared = q.shared ∧ p.secret = q.sharedBytes ∧ p.tripleSecret = q.sharedSlice ∧
          p.braidSecret = q.sharedSlice ∧ p.peerIdentity = q.ourPublic ∧
          p.peerEphemeral = q.ephemeralPublic ∧ p.kemSecret = q.kemSecret ∧
          sliceOf (ResponderPreparedParts.message p) =
            Tacenta.UnitLifecycleEstablishedEncrypt.firstFrame view oracle (establishedModelOf dh s)
              (sliceOf plaintext) messageKey chunk ∧
          (p.lastResort = true ↔ bundleA.kem_prekey_id = storeB.kem_id) ∧
          lifecycle.Session.invariant p.session = ok true ∧
          Tacenta.UnitLifecycleDecryptRunBounds.CounterHeadroom p.session ∧
          SessionRefines dh K p.session (Tacenta.UnitLifecycleEstablishResponder.responderModelOf dh p) := by
  obtain ⟨output, hcall', -, hcases⟩ := Tacenta.UnitLifecycleEstablishedEncrypt.established_encrypt_outcomes rc
    crc trace dh kem view oracle braid triple aead dhCodec oracleOf codec codewordView hz80 hz32 hzKeys hgen
    hct hbound rcE crcE ourA bundleA expected rng0 rng1 s h plaintext hroom rng htrace d1 d2 rest hdraws
  rw [hcall] at hcall'
  cases hcall'
  rcases hcases with ⟨-, hres, -⟩ | ⟨dk, ekSeed, ekVector, -, bytes', hres, -, -, tripleNext, messageKey,
    chunk, encoder, pending, a, -, -, -, hpend, hwire, -⟩
  · cases hres
  · simp only [core.result.Result.Ok.injEq] at hres
    subst hres
    subst hq
    exact ⟨messageKey, chunk, responder_first_frame_admissible rcB crcB contracts hpub hsym hrt hct hbound
      hoeq agreements codec q pending hpend _ (alloc.vec.Vec.deref bytes) hwire ourB storeB hpublish
      hidentity hdistinct hkem rngB⟩

/-! ## The statements the reach rests on, and one interpretation of every law -/

open Tacenta.UnitLifecycleIntegrationScreen (byteRng byteCrc byteTrace)

/-- What one run of the initiator's establishment against a store's published bundle, and of the
responder's prepare phase on the resulting frame, needs from the opaque primitives beyond totality, over an
interpretation `I`, with two functions `Interp` has no field for (`KeyPair::public_key` as `kemPublic`, and
`Vec::is_empty` as `isEmpty`): a private key, given by its bytes, whose public key has canonical bytes, is of
prime order, equals itself, has a verifying signature for every message, and agrees contributorily with every
private key; a KEM key pair with a public key, and one byte stream at which encapsulation to that public key
returns a ciphertext and a secret that the key pair decapsulates back; a wrapper holding the empty one-time
curve pool; and `Vec::is_empty` returning `true` on an empty vector.  Used only to show the reach; no
result about every input takes it. -/
structure FirstFrameSuccessShape (I : Interp) (kemPublic : I.KemKeyPair → Result (alloc.vec.Vec U8))
    (isEmpty : {T : Type} → Type → alloc.vec.Vec T → Result Bool) : Prop where
  key : ∃ (sb : Array U8 32#usize) (k : I.PrivateKey) (pkb : I.PublicKeyBytes) (a : Array U8 32#usize),
    I.dhPrivFromBytes sb = ok k ∧ I.dhPrivPublicKey k = ok pkb ∧ I.dhPubAsBytes pkb = ok a ∧
    Tacenta.SessionUnitT1.canonicalX25519 a = true ∧ I.dhIsPrimeOrderPublic pkb = ok true ∧
    I.dhPubEq pkb pkb = ok true ∧
    (∀ m, ∃ sig, I.xeddsaVerify pkb m sig = ok (core.result.Result.Ok ())) ∧
    (∀ k', ∃ x, I.dhPrivAgree k' pkb = ok (some x))
  kem : ∃ (kp : I.KemKeyPair) (kemPk : alloc.vec.Vec U8) (stream : List U8) (ct : alloc.vec.Vec U8)
      (ss : Array U8 32#usize) (rest : List U8),
    kemPublic kp = ok kemPk ∧ kemPk.val.length + 1 ≤ Usize.max ∧
    I.kemEncapsulate byteRng byteCrc (alloc.vec.Vec.deref kemPk) stream =
      ok (core.result.Result.Ok (ct, ss), rest) ∧
    I.kemDecapsulate kp (alloc.vec.Vec.deref ct) = ok (core.result.Result.Ok ss)
  pool : ∃ z, I.zDeref zPool z = ok (alloc.vec.Vec.new PoolEntry)
  empty : ∀ (T A : Type), isEmpty A (alloc.vec.Vec.new T) = ok true

open Tacenta.UnitLifecycleEstablishedEncrypt (Interp.modelEncrypt InterpO.modelEncrypt viewEncrypt
  dhViewEncrypt kemViewEncrypt toyKemR zeroSeed oneSeed EncryptExtraLawsShape established_encrypt_laws_model
  encapResult encapFill)
open Tacenta.UnitLifecycleDecryptRatchetScreen (DhViewShape)
open Tacenta.UnitOracleShape (InterpO DhViewOf KemViewOf)

/-- `Interp.modelEncrypt` (the encrypt branch's joint model) with a public key that is the base point for
every private key and an agreement that refuses the zero key and otherwise returns the public key it was
given: symmetric, and contributory with every key `public_key` returns.  Every other field is
`Interp.modelEncrypt`'s. -/
noncomputable def Interp.modelFirstFrame : Interp :=
  { Interp.modelEncrypt with
    dhPrivPublicKey := fun _ => ok Tacenta.UnitLifecycleEstablishResponder.basePoint
    dhPrivAgree := fun _ p => ok (if p.val = Tacenta.UnitLifecycleDecryptRatchetScreen.zeros32.val then none
      else some p) }

/-- The joint interpretation with its signing function. -/
noncomputable def InterpO.modelFirstFrame : InterpO :=
  { Interp.modelFirstFrame with xeddsaSign := Tacenta.UnitOracleModel.signModelO }

/-- The view of the joint interpretation: both key types are their bytes. -/
def viewFirstFrame : DhViewShape Interp.modelFirstFrame := ⟨arrayOf, arrayOf⟩
/-- The DH view of the joint interpretation with its signing function. -/
def dhViewFirstFrame : DhViewOf InterpO.modelFirstFrame.toInterp :=
  ⟨viewFirstFrame.privateKey, viewFirstFrame.publicKey⟩
/-- The KEM view of the joint interpretation with its signing function. -/
def kemViewFirstFrame : KemViewOf InterpO.modelFirstFrame.toInterp := ⟨fun _ => []⟩

/-- The base point is not the zero key. -/
theorem basePoint_ne_zero :
    Tacenta.UnitLifecycleEstablishResponder.basePoint.val ≠
      Tacenta.UnitLifecycleDecryptRatchetScreen.zeros32.val := by decide

/-- The joint interpretation's DH codec functions return. -/
theorem modelFirstFrame_dhCodec : Tacenta.UnitSatisfiabilityJoint.DhCodecShape Interp.modelFirstFrame :=
  ⟨fun _ => ⟨_, rfl⟩, fun _ => ⟨_, rfl⟩, fun _ => ⟨_, rfl⟩, fun _ => ⟨_, rfl⟩, fun _ => ⟨_, rfl⟩,
    fun _ _ => ⟨_, rfl⟩⟩

/-- The joint interpretation's agreement returns. -/
theorem modelFirstFrame_dhAgree : Tacenta.UnitSatisfiabilityJoint.DhAgreeShape Interp.modelFirstFrame :=
  fun _ _ => ⟨_, rfl⟩

/-- The agreement law holds in the joint interpretation: both sides return the base point. -/
theorem modelFirstFrame_symmetric : DhAgreeSymmetricShape Interp.modelFirstFrame := by
  intro a b pa pb ha hb
  simp only [Interp.modelFirstFrame, ok.injEq] at ha hb
  subst ha hb
  rfl

open Tacenta.UnitSatisfiabilityJoint (InitiatorAxiom ResponderAxiom) in
open Tacenta.UnitLifecycleSessionCodec (ZeroizingVecRoundTripShape DhPrivateBytesRoundTripShape
  DhPublicBytesRoundTripShape OptionBranchSomeShape VecAsSliceShape optionBranchImpl vecAsSliceImpl) in
open Tacenta.UnitLifecycleRestoredSession (KemCiphertextLenBoundShape) in
open Tacenta.UnitLifecycleEstablishInitiatorShape (InitiatorSuccessShape DhPublicValidShape
  KemCiphertextLenLawShape) in
/-- **Every law the statements above take, with the decrypt, establishment, restore, encrypt and responder
laws, holds in one interpretation**, `InterpO.modelFirstFrame` (the encrypt branch's joint model with a
symmetric agreement that is contributory on every key `public_key` returns), with its views, the toy KEM
`toyKemR`, `optionEqImpl` for `Option::eq` and the constant `ok 0` for `kem::ciphertext_len`: the decrypt laws,
the initiator contract axioms, `InitiatorSuccessShape`, `DhPublicValidShape`, the ciphertext-length law, the
encrypt extra laws, the six laws of the restored session's round trip, the size law and the two seeds of the
encrypt branch, the responder contract axioms, `ResponderSuccessShape`, `ZeroKeyShape`, the agreement law
`DhAgreeSymmetricShape` and `FirstFrameSuccessShape` (with an empty public KEM key and `Vec::is_empty` as the
emptiness test).  In the substitution sense of `UnitSatisfiabilityRecords`; not a statement that the real
primitives meet them. -/
theorem first_frame_laws_model :
    Tacenta.UnitLifecycleDecryptScreen.DecryptJointLawsShape Interp.modelFirstFrame viewFirstFrame toyKemR
        @Tacenta.UnitHeadroomInvariant.optionEqImpl ∧
      Nonempty (InitiatorAxiom Interp.modelFirstFrame byteRng) ∧
      InitiatorSuccessShape Interp.modelFirstFrame byteRng byteCrc ∧
      DhPublicValidShape Interp.modelFirstFrame ∧
      KemCiphertextLenLawShape (ok 0#usize) Interp.modelFirstFrame ∧
      EncryptExtraLawsShape InterpO.modelFirstFrame dhViewFirstFrame kemViewFirstFrame toyKemR (ok 0#usize) ∧
      (ZeroizingVecRoundTripShape Interp.modelFirstFrame ∧
        DhPrivateBytesRoundTripShape Interp.modelFirstFrame ∧
        DhPublicBytesRoundTripShape Interp.modelFirstFrame ∧ OptionBranchSomeShape @optionBranchImpl ∧
        VecAsSliceShape @vecAsSliceImpl ∧ KemCiphertextLenBoundShape (ok 0#usize)) ∧
      Tacenta.UnitLifecycleEstablishedEncrypt.KeyGenSizesOf toyKemR ∧
      toyKemR.keyGen (Model.Lifecycle.braidRandomness
          (zeroSeed.map Tacenta.SessionUnitBraidT3.u8)) = none ∧
      toyKemR.keyGen (Model.Lifecycle.braidRandomness
          (oneSeed.map Tacenta.SessionUnitBraidT3.u8)) ≠ none ∧
      Nonempty (ResponderAxiom Interp.modelFirstFrame byteRng) ∧
      Tacenta.UnitLifecycleEstablishResponder.ResponderSuccessShape Interp.modelFirstFrame ∧
      Tacenta.UnitLifecycleEstablishResponder.ZeroKeyShape Interp.modelFirstFrame ∧
      DhAgreeSymmetricShape Interp.modelFirstFrame ∧
      FirstFrameSuccessShape Interp.modelFirstFrame (fun _ => ok (alloc.vec.Vec.new U8))
        (fun _ v => ok (decide (v.val = []))) := by
  obtain ⟨M, ⟨A⟩, -, -, C, X, ⟨r1, r2, r3, r4, r5, r6⟩, ks, s0, s1⟩ := established_encrypt_laws_model
  obtain ⟨-, ⟨RA⟩, -, -, -⟩ := Tacenta.UnitLifecycleEstablishResponder.responder_route_laws_model
  have hcodec := modelFirstFrame_dhCodec
  have hagree := modelFirstFrame_dhAgree
  have hb := basePoint_ne_zero
  refine ⟨?_, ⟨?_⟩, ?_, ?_, ?_, ?_, ⟨?_, ?_, ?_, r4, r5, r6⟩, ks, s0, s1, ⟨?_⟩, ?_, ?_,
    modelFirstFrame_symmetric, ?_⟩
  · exact
      { dhCodec := hcodec
        dhAgree := hagree
        aeadOpen := M.aeadOpen
        viewInjective := M.viewInjective
        codec := by have h := M.codec; cases h; constructor <;> assumption
        braid := by have h := M.braid; cases h; constructor <;> assumption
        triple := by have h := M.triple; cases h; constructor <;> assumption
        messageKeyMaterial := M.messageKeyMaterial
        laws := by have h := M.laws; cases h; constructor <;> assumption
        truncatePrefix := M.truncatePrefix
        derivedKeys := by
          obtain ⟨h⟩ := M.derivedKeys; cases h; exact ⟨by constructor <;> assumption⟩
        agreements := by have h := M.agreements; cases h; constructor <;> assumption
        roundTrips := by have h := M.roundTrips; cases h; constructor <;> assumption
        validKey := ⟨Tacenta.UnitLifecycleDecryptRatchetScreen.zeros32,
          Tacenta.UnitLifecycleEstablishResponder.basePoint, Tacenta.UnitLifecycleEstablishResponder.basePoint,
          rfl, rfl, Tacenta.UnitLifecycleEstablishResponder.basePoint_canonical, rfl⟩
        optionEq := M.optionEq }
  · exact
      { dhCodec := hcodec
        dhIdentity := A.dhIdentity
        dhAgree := hagree
        kemEncapsulate := A.kemEncapsulate
        xeddsaVerify := A.xeddsaVerify
        rngTotal := A.rngTotal
        random32 := A.random32
        sessionHkdf := A.sessionHkdf
        sessionZeroizing := by have h := A.sessionZeroizing; cases h; constructor <;> assumption
        tripleZeroizing := A.tripleZeroizing
        spqrZeroize := A.spqrZeroize
        braidHkdf := A.braidHkdf
        zeroizingArray := A.zeroizingArray
        rangeFullIndex := A.rangeFullIndex }
  · refine ⟨⟨Tacenta.UnitLifecycleEstablishedDecrypt.oneKey, Tacenta.UnitLifecycleEstablishedDecrypt.oneKey,
      rfl, Tacenta.UnitLifecycleEstablishedDecrypt.oneKey_canonical, rfl, ?_,
      fun _ => ⟨Array.repeat 64#usize 0#u8, rfl⟩, fun k => ⟨Tacenta.UnitLifecycleEstablishedDecrypt.oneKey, ?_⟩⟩,
      ⟨alloc.vec.Vec.new U8, by simp; scalar_tac, fun rng => ?_⟩⟩
    · show ok (decide (Tacenta.UnitLifecycleEstablishedDecrypt.oneKey.val =
        Tacenta.UnitLifecycleEstablishedDecrypt.oneKey.val)) = ok true
      simp
    · show ok (if Tacenta.UnitLifecycleEstablishedDecrypt.oneKey.val =
          Tacenta.UnitLifecycleDecryptRatchetScreen.zeros32.val then none
        else some Tacenta.UnitLifecycleEstablishedDecrypt.oneKey) =
        ok (some Tacenta.UnitLifecycleEstablishedDecrypt.oneKey)
      simp [Tacenta.UnitLifecycleEstablishedDecrypt.oneKey_ne_zero]
    · show ∃ ct ss rng', encapFill byteRng byteCrc _ rng = ok (core.result.Result.Ok (ct, ss), rng')
      simp only [encapFill, if_true]
      exact ⟨_, _, _, rfl⟩
  · intro k pkb h
    have hp : pkb = Tacenta.UnitLifecycleEstablishResponder.basePoint := by
      simpa [Interp.modelFirstFrame] using h.symm
    subst hp
    exact ⟨Tacenta.UnitLifecycleEstablishResponder.basePoint, rfl,
      Tacenta.UnitLifecycleEstablishResponder.basePoint_canonical, rfl⟩
  · exact C
  · exact
      { oracle :=
          { dhCodec := hcodec
            dhAgree := hagree
            dhIdentity := X.oracle.dhIdentity
            aeadSeal := X.oracle.aeadSeal
            aeadOpen := X.oracle.aeadOpen
            kemDecapsulate := X.oracle.kemDecapsulate
            xeddsaVerify := X.oracle.xeddsaVerify
            signLaw := X.oracle.signLaw
            kemLaw := X.oracle.kemLaw
            dhView := X.oracle.dhView
            kemView := X.oracle.kemView }
        encrypt :=
          { braid := by have h := X.encrypt.braid; cases h; constructor <;> assumption
            triple := by have h := X.encrypt.triple; cases h; constructor <;> assumption
            aeadSeal := X.encrypt.aeadSeal
            messageKeyMaterial := X.encrypt.messageKeyMaterial
            dhCodec := hcodec }
        keyGen := X.keyGen
        zeroizingKeys := X.zeroizingKeys
        ciphertextBound := X.ciphertextBound }
  · exact r1
  · exact r2
  · exact r3
  · exact
      { decrypt := ⟨hcodec, hagree, RA.decrypt.aeadOpen, RA.decrypt.random32,
          by have h := RA.decrypt.braid; cases h; constructor <;> assumption,
          by have h := RA.decrypt.triple; cases h; constructor <;> assumption,
          RA.decrypt.messageKeyMaterial⟩
        dhIdentity := RA.dhIdentity
        kemDecapsulate := RA.kemDecapsulate
        sessionHkdf := RA.sessionHkdf
        sessionZeroizing := by have h := RA.sessionZeroizing; cases h; constructor <;> assumption
        vecPop := RA.vecPop
        divCeilValue := RA.divCeilValue }
  · refine ⟨⟨Tacenta.UnitLifecycleEstablishResponder.basePoint, rfl, rfl, rfl,
      fun k => ⟨Tacenta.UnitLifecycleEstablishResponder.basePoint, ?_⟩⟩,
      ⟨(), alloc.vec.Vec.new U8, Tacenta.UnitSatisfiabilityBraidStates.zeros32, by simp, rfl⟩,
      ⟨alloc.vec.Vec.new _⟩⟩
    show ok (if Tacenta.UnitLifecycleEstablishResponder.basePoint.val =
        Tacenta.UnitLifecycleDecryptRatchetScreen.zeros32.val then none
      else some Tacenta.UnitLifecycleEstablishResponder.basePoint) =
      ok (some Tacenta.UnitLifecycleEstablishResponder.basePoint)
    simp [hb]
  · refine ⟨Tacenta.UnitSatisfiabilityBraidStates.zeros32, rfl, fun k => ?_⟩
    show (ok (if Tacenta.UnitSatisfiabilityBraidStates.zeros32.val =
        Tacenta.UnitLifecycleDecryptRatchetScreen.zeros32.val then none
      else some Tacenta.UnitSatisfiabilityBraidStates.zeros32)) = ok none
    simp [Tacenta.UnitSatisfiabilityBraidStates.zeros32, Tacenta.UnitLifecycleDecryptRatchetScreen.zeros32]
  · refine ⟨⟨Tacenta.UnitSatisfiabilityBraidStates.zeros32, Tacenta.UnitSatisfiabilityBraidStates.zeros32,
      Tacenta.UnitLifecycleEstablishResponder.basePoint, Tacenta.UnitLifecycleEstablishResponder.basePoint,
      rfl, rfl, rfl, Tacenta.UnitLifecycleEstablishResponder.basePoint_canonical, rfl, ?_,
      fun _ => ⟨Array.repeat 64#usize 0#u8, rfl⟩, fun k => ⟨Tacenta.UnitLifecycleEstablishResponder.basePoint, ?_⟩⟩,
      ⟨(), alloc.vec.Vec.new U8, List.replicate 32 0#u8, alloc.vec.Vec.new U8,
        Tacenta.UnitSatisfiabilityBraidStates.zeros32, [], rfl, by simp; scalar_tac, ?_, ?_⟩,
      ⟨alloc.vec.Vec.new PoolEntry, rfl⟩, fun _ _ => rfl⟩
    · show ok (decide (Tacenta.UnitLifecycleEstablishResponder.basePoint.val =
        Tacenta.UnitLifecycleEstablishResponder.basePoint.val)) = ok true
      simp
    · show ok (if Tacenta.UnitLifecycleEstablishResponder.basePoint.val =
          Tacenta.UnitLifecycleDecryptRatchetScreen.zeros32.val then none
        else some Tacenta.UnitLifecycleEstablishResponder.basePoint) =
        ok (some Tacenta.UnitLifecycleEstablishResponder.basePoint)
      simp [hb]
    · show encapFill byteRng byteCrc _ (List.replicate 32 0#u8) = _
      simp [encapFill, encapResult, byteRng, Tacenta.UnitLifecycleIntegrationScreen.zeros32,
        Tacenta.UnitLifecycleIntegrationScreen.zeroSlice]
      decide
    · rfl

/-! ## The reach: one run, from `publish` to the inner receive -/

/-- The prekey store the reach is shown at: one key as identity key and signed prekey (identifier 1), the
KEM key used as a last-resort key (identifier 2), no one-time prekeys of either kind, no previous keys, an
empty replay record and no legacy marker. -/
def reachStore (pkb : tacenta_boundary.dh.PublicKeyBytes) (sb : Array U8 32#usize)
    (sig1 sig2 : Array U8 64#usize) (z : zeroize.Zeroizing (alloc.vec.Vec PoolEntry))
    (kp : tacenta_boundary.kem.KeyPair) : lifecycle.PrekeyStore :=
  { identity_public := pkb, signed_prekey_secret := sb, signed_prekey_id := 1#u32,
    signed_prekey_sig := sig1, one_time := z, kem := kp, kem_id := 2#u32, kem_sig := sig2,
    kem_one_time := alloc.vec.Vec.new _, previous_signed_prekey := none, previous_kem := none,
    next_id := 3#u32, last_resort_seen := alloc.vec.Vec.new _, legacy_last_resort_blocked := alloc.vec.Vec.new _ }

/-- The bundle `publish` returns for `reachStore`. -/
def reachBundle (pkb : tacenta_boundary.dh.PublicKeyBytes) (sig1 sig2 : Array U8 64#usize)
    (kemPk : alloc.vec.Vec U8) : lifecycle.PublishedBundle :=
  { bundle :=
      { identity_key := pkb, signed_prekey := pkb, signed_prekey_signature := sig1, kem_prekey := kemPk,
        kem_prekey_signature := sig2, one_time_prekey := none },
    signed_prekey_id := 1#u32, one_time_prekey_id := serialization.ABSENT_ID, kem_prekey_id := 2#u32 }

/-- `publish` of `reachStore` returns `reachBundle`. -/
theorem publish_reachStore (pkb : tacenta_boundary.dh.PublicKeyBytes) (sb : Array U8 32#usize)
    (k : tacenta_boundary.dh.PrivateKey) (hk : tacenta_boundary.dh.PrivateKey.from_bytes sb = ok k)
    (hpkb : tacenta_boundary.dh.PrivateKey.public_key k = ok pkb) (sig1 sig2 : Array U8 64#usize)
    (z : zeroize.Zeroizing (alloc.vec.Vec PoolEntry))
    (hz : zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref zPool z = ok (alloc.vec.Vec.new PoolEntry))
    (hempty : ∀ (T A : Type), alloc.vec.Vec.is_empty A (alloc.vec.Vec.new T) = ok true)
    (kp : tacenta_boundary.kem.KeyPair) (kemPk : alloc.vec.Vec U8)
    (hkp : tacenta_boundary.kem.KeyPair.public_key kp = ok kemPk) :
    lifecycle.PrekeyStore.publish (reachStore pkb sb sig1 sig2 z kp) = ok (reachBundle pkb sig1 sig2 kemPk) := by
  unfold lifecycle.PrekeyStore.publish
  simp only [reachStore]
  rw [hz, Aeneas.Std.bind_tc_ok, hempty, Aeneas.Std.bind_tc_ok]
  simp [hempty, hkp, hk, hpkb, reachBundle]

/-- The store's identifiers, 1 and 2 with nothing else, are distinct and not `ABSENT_ID`. -/
theorem reachStore_distinct (pkb : tacenta_boundary.dh.PublicKeyBytes) (sb : Array U8 32#usize)
    (sig1 sig2 : Array U8 64#usize) (z : zeroize.Zeroizing (alloc.vec.Vec PoolEntry))
    (hz : zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref zPool z = ok (alloc.vec.Vec.new PoolEntry))
    (kp : tacenta_boundary.kem.KeyPair) : PrekeyIdsDistinct (reachStore pkb sb sig1 sig2 z kp) := by
  refine ⟨alloc.vec.Vec.new PoolEntry, hz, ?_, ?_⟩ <;>
    simp [storeIds, reachStore, serialization.ABSENT_ID]

/-- `random_secret` at the byte-stream source reads the first 32 bytes. -/
theorem random_secret_byte (crc : rand_core_1.CryptoRng (List U8)) (pre rest : List U8)
    (hpre : pre.length = 32) :
    ∃ a, lifecycle.random_secret byteRng crc (pre ++ rest) = ok (a, rest) := by
  simp only [lifecycle.random_secret, byteRng]
  simp only [lift, Aeneas.Std.bind_tc_ok, Array.to_slice_mut]
  simp [hpre]

open Tacenta.UnitLifecycleT1 in
/-- **The initiator's establishment against `reachBundle` succeeds**, at the byte-stream source holding 32
bytes for the ephemeral key followed by a stream at which encapsulation to the bundle's KEM key returns
`(ct, ss)`, under the initiator contracts, for a bundle key with canonical bytes, of prime order, equal to
itself, on which `verify_bundle` accepts the bundle and every private key agrees contributorily.  A record of
the run is exhibited, with that ciphertext and that secret. -/
theorem reach_establishment (c : EstablishInitiatorContracts byteRng) (ourA : lifecycle.Identity)
    (pkb : tacenta_boundary.dh.PublicKeyBytes) (a : Array U8 32#usize)
    (ha : tacenta_boundary.dh.PublicKeyBytes.as_bytes pkb = ok a)
    (hcan : Tacenta.SessionUnitT1.canonicalX25519 a = true)
    (heq : tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq pkb pkb = ok true)
    (sig1 sig2 : Array U8 64#usize) (kemPk : alloc.vec.Vec U8)
    (hverify : verify_bundle (reachBundle pkb sig1 sig2 kemPk).bundle = ok (core.result.Result.Ok ()))
    (hag : ∀ k, ∃ x, tacenta_boundary.dh.PrivateKey.agree k pkb = ok (some x))
    (stream rest : List U8) (ct : alloc.vec.Vec U8) (ss : Array U8 32#usize)
    (henc : tacenta_boundary.kem.encapsulate byteRng byteCrc (alloc.vec.Vec.deref kemPk) stream =
      ok (core.result.Result.Ok (ct, ss), rest)) :
    ∃ (q : InitiatorSecretParts byteRng byteCrc ourA (reachBundle pkb sig1 sig2 kemPk)) (rng1 : List U8),
      q.kemCiphertext = ct ∧ q.kemSecret = ss ∧
      lifecycle.establish_initiator_for byteRng byteCrc ourA (reachBundle pkb sig1 sig2 kemPk) pkb
        (List.replicate 32 0#u8 ++ stream) = ok (core.result.Result.Ok q.session, rng1) := by
  rcases c with ⟨hdh, hid, hagree, hkem, hx, hrngTotal, hrng, hkdf, hzero, htripleZero, hkdfInit,
    hspqrZero, hbraidKdf, hzeroArray, hindex⟩
  let _ : Tacenta.SessionUnitSessionT1.ZeroizingModel := hzero
  obtain ⟨a1, hr1⟩ := random_secret_byte byteCrc (List.replicate 32 0#u8) stream (by simp)
  obtain ⟨eph, heph, -⟩ := Std.WP.spec_imp_exists (private_key_from_bytes_no_panic hdh a1)
  obtain ⟨z1, hz1, hz1d⟩ := hzeroArray 32#usize z32 ss
  obtain ⟨ik, hik, -⟩ :=
    Std.WP.spec_imp_exists (Tacenta.UnitLifecycleT1.identity_dh_key_no_panic hdh ourA)
  have hsec := Tacenta.UnitLifecycleEstablishInitiatorShape.shared_secret_successBundle hzeroArray hkdf pkb
    sig1 sig2 kemPk hverify hag ik eph ss
  obtain ⟨sec, hsec⟩ := hsec
  obtain ⟨z2, hz2, hz2d⟩ := hzeroArray 32#usize z32 sec
  obtain ⟨⟨a2, r3⟩, hr3, -⟩ := Std.WP.spec_imp_exists (random_secret_no_panic byteRng byteCrc hrng rest)
  obtain ⟨rp, hrp, -⟩ := Std.WP.spec_imp_exists (private_key_from_bytes_no_panic hdh a2)
  obtain ⟨d, hd⟩ := hag rp
  obtain ⟨z3, hz3, hz3d⟩ := hzeroArray 32#usize z32 d
  obtain ⟨s1, hs1i, -⟩ := Std.WP.spec_imp_exists (Tacenta.SessionUnitBraidT1.index_full_spec hindex sec)
  obtain ⟨rpub, hrpub, -⟩ := Std.WP.spec_imp_exists (private_key_public_no_panic hdh rp)
  obtain ⟨a4, ha4, -⟩ := Std.WP.spec_imp_exists (public_key_as_bytes_no_panic hdh rpub)
  obtain ⟨triple, htriple, -⟩ := Std.WP.spec_imp_exists
    (Tacenta.SessionUnitTripleT1.State.init_sender_no_panic hkdf htripleZero hkdfInit hspqrZero s1 a4
      a d tacenta_ratchet.LabelSet.Tacenta)
  obtain ⟨rk, cks, prk, c1, c2, rfl⟩ := init_sender_ok _ _ _ _ _ htriple
  obtain ⟨braid, hbraid, -⟩ :=
    Std.WP.spec_imp_exists (Tacenta.SessionUnitBraidT1.Braid.initiator_no_panic hbraidKdf hzeroArray s1)
  obtain ⟨auth, rfl⟩ := braid_initiator_ok _ _ hbraid
  obtain ⟨opub, hopub, -⟩ :=
    Std.WP.spec_imp_exists (Tacenta.UnitLifecycleT1.identity_public_no_panic hdh ourA)
  obtain ⟨ad, had, -⟩ := Std.WP.spec_imp_exists (identity_ad_no_panic hdh opub pkb)
  obtain ⟨epub, hepub, -⟩ := Std.WP.spec_imp_exists (private_key_public_no_panic hdh eph)
  have hne : core.cmp.PartialEq.ne.trait_default
      tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes pkb pkb = ok false := by
    simp [core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default, heq]
  have hcanon : is_canonical_key pkb = ok true := by
    rw [Tacenta.UnitHeadroomInvariant.is_canonical_key_eq pkb a ha, hcan]
  have hvalid : is_valid_identity_key pkb = ok true := Tacenta.UnitLifecycleEstablishInitiatorShape.verify_bundle_ok _ _ hverify
  refine ⟨
    { ratchetPrivate := rp, ratchetPublic := rpub, ratchetBytes := a4, peerRatchetBytes := a, rootKey := rk,
      sendChain := cks, sparseRoot := prk, sparseSend := c1, sparseReceive := c2, auth := auth,
      identityAd := ad, ourPublic := opub, ephemeral := eph, ephemeralPublic := epub, kemCiphertext := ct,
      kemSecret := ss, rngBefore := stream, rngAfter := rest,
      hRatchetPublic := hrpub, hRatchetBytes := ha4, hPeerRatchetBytes := ha, hPeerRatchetCanonical := hcanon,
      hOurPublic := hopub, hIdentityAd := had, hPeerValid := hvalid, hEphemeralPublic := hepub,
      hEncapsulate := henc,
      identityKey := ik, kemSecretZ := z1, encapsulated := ss, shared := sec, sharedZ := z2,
      sharedBytes := sec, sharedSlice := s1, dhOut := d, dhOutZ := z3, dhOutBytes := d, braidSlice := s1,
      hDhKey := hik, hKemSecretZ := hz1, hEncapsulated := hz1d, hShared := hsec, hSharedZ := hz2,
      hSharedBytes := hz2d, hTriple := htriple, hSharedSlice := hs1i, hDhOutBytes := hz3d, hDhOutZ := hz3,
      hDhOut := hd, hBraid := hbraid, hBraidSlice := hs1i, hVerify := hverify }, r3, rfl, rfl, ?_⟩
  simp only [reachBundle, Tacenta.UnitLifecycleEstablishInitiatorShape.successBundle] at hverify hsec
  generalize List.replicate 32 0#u8 ++ stream = rng0 at hr1 ⊢
  simp [lifecycle.establish_initiator_for, reachBundle, hne, hcanon, hverify, hr1, heph, henc, hz1, hz1d,
    hik, hsec, hz2, hz2d, hr3, hrp, hd, hz3, hz3d, hs1i, hrpub, ha4, ha, htriple, hbraid, hopub, had, hepub,
    InitiatorOutputParts.session]

open Tacenta.UnitSatisfiabilityJoint (InitiatorAxiom ResponderAxiom) in
open Tacenta.UnitLifecycleEstablishedEncrypt (EstablishedEncryptHypotheses EncryptExtraLaws emptyPlaintext) in
/-- **The reach of the inner receive at the initiator's first frame**: at the real constants, under the
decrypt laws `DecryptJointLaws K dh`, the initiator and responder contract axioms, `InitiatorSuccessShape`,
`DhPublicValid`, `KemCiphertextLenOf`, the encrypt extra laws, the agreement law `DhAgreeSymmetric`, the
public-key byte round trip and `FirstFrameSuccessShape` (all assumed), for every initiator identity and every
64-byte source at whose bytes the model's key generation answers, there are a prekey store, its owner and
the bundle it publishes, a successful establishment against that bundle (with a record `q` of the run), a
first send that returns bytes, and parts at which `establish_responder` on those bytes reaches the inner
receive: every premise of `first_send_responder_prepares` holds there, the store refuses nothing (no legacy
marker, an empty replay record), and the parts carry the initiator's shared secret and the first frame, with
the invariant, the ceilings and the relation.  So that theorem's second arm is not about an empty set under
those assumptions.  Nothing here says the inner receive succeeds. -/
theorem first_send_responder_reachable (K : Model.Braid.Kem) (dh : DhView)
    (kem : Tacenta.UnitLifecycleT3.KemView) (L : Tacenta.UnitLifecycleDecryptScreen.DecryptJointLaws K dh)
    (A : Nonempty (InitiatorAxiom Interp.real byteRng))
    (S : Tacenta.UnitLifecycleEstablishInitiatorShape.InitiatorSuccessShape Interp.real byteRng byteCrc)
    (hpub : DhPublicValid) (hct : Tacenta.UnitLifecycleEstablishInitiatorShape.KemCiphertextLenOf)
    (X : EncryptExtraLaws K dh kem) (RA : Nonempty (ResponderAxiom Interp.real byteRng))
    (hsym : DhAgreeSymmetric) (hrt : Tacenta.UnitLifecycleSessionCodec.DhPublicBytesRoundTrip)
    (FS : FirstFrameSuccessShape Interp.real tacenta_boundary.kem.KeyPair.public_key
      @alloc.vec.Vec.is_empty)
    (ourA : lifecycle.Identity) (seed : List Std.U8) (hseed : seed.length = 64)
    (hkg : K.keyGen (Model.Lifecycle.braidRandomness (seed.map Tacenta.SessionUnitBraidT3.u8)) ≠ none) :
    ∃ (oracle : Model.Lifecycle.Oracle) (bundle : lifecycle.PublishedBundle) (rng0 rng1 : List Std.U8)
      (q : InitiatorSecretParts byteRng byteCrc ourA bundle) (bytes : alloc.vec.Vec Std.U8)
      (s' : lifecycle.Session) (rng' : List Std.U8) (ourB : lifecycle.Identity)
      (storeB : lifecycle.PrekeyStore) (messageKey : Model.Lifecycle.Key) (chunk : Model.Braid.Chunk)
      (p : ResponderPreparedParts ourB storeB (alloc.vec.Vec.deref bytes)),
      oracle.braidKem = K ∧
      EstablishedEncryptHypotheses byteRng byteCrc byteTrace dh kem Tacenta.UnitLifecycleRepair.witnessView
        oracle byteRng byteCrc ourA bundle bundle.bundle.identity_key rng0 rng1 q.session emptyPlaintext seed ∧
      lifecycle.Session.encrypt byteRng byteCrc q.session emptyPlaintext seed =
        ok (core.result.Result.Ok bytes, s', rng') ∧
      lifecycle.PrekeyStore.publish storeB = ok bundle ∧
      lifecycle.Identity.public ourB = ok storeB.identity_public ∧ PrekeyIdsDistinct storeB ∧
      FirstKemAgrees storeB bundle.kem_prekey_id q.kemCiphertext q.kemSecret ∧
      storeB.legacy_last_resort_blocked.val = [] ∧ storeB.last_resort_seen.val = [] ∧
      p.shared = q.shared ∧ p.peerIdentity = q.ourPublic ∧ p.peerEphemeral = q.ephemeralPublic ∧
      sliceOf (ResponderPreparedParts.message p) =
        Tacenta.UnitLifecycleEstablishedEncrypt.firstFrame Tacenta.UnitLifecycleRepair.witnessView oracle
          (establishedModelOf dh q.session) (sliceOf emptyPlaintext) messageKey chunk ∧
      lifecycle.Session.invariant p.session = ok true ∧
      Tacenta.UnitLifecycleDecryptRunBounds.CounterHeadroom p.session ∧
      SessionRefines dh K p.session (Tacenta.UnitLifecycleEstablishResponder.responderModelOf dh p) := by
  -- the run's keys and KEM pair
  obtain ⟨sb, kB, pkb, a, hkB, hpkb, ha, hcan, hprime, heq, hsig, hag⟩ := FS.key
  obtain ⟨kp, kemPk, stream, ct, ss, rest, hkp, hlen, henc, hdec⟩ := FS.kem
  obtain ⟨z, hz⟩ := FS.pool
  have hkB' : tacenta_boundary.dh.PrivateKey.from_bytes sb = ok kB := hkB
  have hpkb' : tacenta_boundary.dh.PrivateKey.public_key kB = ok pkb := hpkb
  have ha' : tacenta_boundary.dh.PublicKeyBytes.as_bytes pkb = ok a := ha
  have hprime' : tacenta_boundary.dh.is_prime_order_public pkb = ok true := hprime
  have heq' : tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq pkb pkb =
      ok true := heq
  have hsig' : ∀ m, ∃ sig, tacenta_boundary.xeddsa.verify pkb m sig = ok (core.result.Result.Ok ()) := hsig
  have hag' : ∀ k, ∃ x, tacenta_boundary.dh.PrivateKey.agree k pkb = ok (some x) := hag
  have henc' : tacenta_boundary.kem.encapsulate byteRng byteCrc (alloc.vec.Vec.deref kemPk) stream =
      ok (core.result.Result.Ok (ct, ss), rest) := henc
  have hdec' : tacenta_boundary.kem.decapsulate kp (alloc.vec.Vec.deref ct) = ok (core.result.Result.Ok ss) :=
    hdec
  have hz' : zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref zPool z = ok (alloc.vec.Vec.new PoolEntry) := hz
  -- the contracts
  obtain ⟨c⟩ := Tacenta.UnitSatisfiabilityRecords.initiator_contracts_of_axiom_base byteRng A
  obtain ⟨contracts⟩ := Tacenta.UnitSatisfiabilityRecords.responder_contracts_of_axiom_base byteRng RA L.laws
  have hdh := c.dhCodec
  -- the bundle's signatures
  obtain ⟨v, hv, -⟩ := Std.WP.spec_imp_exists (Tacenta.UnitLifecycleT1.encode_ec_spec hdh pkb)
  obtain ⟨sig1, hs1⟩ := hsig' (alloc.vec.Vec.deref v)
  obtain ⟨v1, hv1, -⟩ := Std.WP.spec_imp_exists
    (Tacenta.UnitLifecycleT1.encode_kem_no_panic (alloc.vec.Vec.deref kemPk) hlen)
  obtain ⟨sig2, hs2⟩ := hsig' (alloc.vec.Vec.deref v1)
  have hverify : verify_bundle (reachBundle pkb sig1 sig2 kemPk).bundle = ok (core.result.Result.Ok ()) :=
    Tacenta.UnitLifecycleEstablishInitiatorShape.verify_successBundle pkb a ha' hcan hprime' sig1 sig2 kemPk
      v v1 hv hs1 hv1 hs2
  -- the establishment
  obtain ⟨q, rng1, hqct, hqss, h⟩ := reach_establishment c ourA pkb a ha' hcan heq' sig1 sig2 kemPk hverify
    hag' stream rest ct ss henc'
  -- the encrypt record at that establishment, from the joint construction of the encrypt branch
  obtain ⟨oracle, bundle0, s0, rng10, hK, hdraws0, H0⟩ :=
    Tacenta.UnitLifecycleEstablishedEncrypt.established_encrypt_hypotheses_jointly_satisfiable K dh kem L A S
      hpub hct X ourA seed (by omega)
  have H : EstablishedEncryptHypotheses byteRng byteCrc byteTrace dh kem
      Tacenta.UnitLifecycleRepair.witnessView oracle byteRng byteCrc ourA (reachBundle pkb sig1 sig2 kemPk)
      (reachBundle pkb sig1 sig2 kemPk).bundle.identity_key (List.replicate 32 0#u8 ++ stream) rng1 q.session
      emptyPlaintext seed :=
    { braid := H0.braid, triple := H0.triple, derivedKeys := H0.derivedKeys, aead := H0.aead,
      dhCodec := H0.dhCodec, oracleOf := H0.oracleOf, codec := H0.codec, codewordView := H0.codewordView,
      zeroizing80 := H0.zeroizing80, zeroizing32 := H0.zeroizing32, zeroizingKeys := H0.zeroizingKeys,
      keyGen := H0.keyGen, kemCiphertextLen := H0.kemCiphertextLen,
      kemCiphertextBound := H0.kemCiphertextBound, established := h, room := H0.room,
      trace_eq := H0.trace_eq, draws := H0.draws }
  obtain ⟨inst⟩ := H.derivedKeys
  subst hK
  -- the first send's success
  obtain ⟨output, hcall, -, hcases⟩ := Tacenta.UnitLifecycleEstablishedEncrypt.established_encrypt_outcomes
    byteRng byteCrc byteTrace dh kem Tacenta.UnitLifecycleRepair.witnessView oracle H.braid H.triple H.aead
    H.dhCodec H.oracleOf H.codec H.codewordView H.zeroizing80 H.zeroizing32 H.zeroizingKeys H.keyGen
    H.kemCiphertextLen H.kemCiphertextBound byteRng byteCrc ourA _ _ _ rng1 q.session H.established
    emptyPlaintext H.room seed H.trace_eq _ _ _
    (Tacenta.UnitLifecycleEstablishedEncrypt.byteTrace_two seed (by omega))
  rw [Tacenta.UnitLifecycleEstablishedEncrypt.two_draws_of_64 seed hseed] at hcases
  obtain ⟨res, s', rng'⟩ := output
  rcases hcases with ⟨hnone, -⟩ | ⟨dk, ekSeed, ekVector, -, bytes, hres, -⟩
  · exact absurd hnone hkg
  simp only at hres
  subst hres
  -- the responder's side
  let ourB : lifecycle.Identity := { secret := sb }
  have hidentity : lifecycle.Identity.public ourB = ok pkb := by
    show (do let pk ← tacenta_boundary.dh.PrivateKey.from_bytes sb; tacenta_boundary.dh.PrivateKey.public_key pk)
      = ok pkb
    rw [hkB']; exact hpkb'
  let storeB := reachStore pkb sb sig1 sig2 z kp
  have hpublish := publish_reachStore pkb sb kB hkB' hpkb' sig1 sig2 z hz' FS.empty kp kemPk hkp
  have hdistinct := reachStore_distinct pkb sb sig1 sig2 z hz' kp
  have hkem : FirstKemAgrees storeB (reachBundle pkb sig1 sig2 kemPk).kem_prekey_id q.kemCiphertext
      q.kemSecret := by
    refine ⟨kp, by simp [heldKemPair, storeB, reachStore, reachBundle], ?_⟩
    rw [hqct, hqss]; exact hdec'
  have D := (Tacenta.UnitLifecycleEstablishedDecrypt.established_decrypt_hypotheses_jointly_satisfiable
    oracle.braidKem dh L A S hpub hct ourA)
  obtain ⟨oracle0, bundle1, s1, rng11, hK0, H1⟩ := D
  have ag : Tacenta.UnitLifecycleDecryptRatchetT3.DecryptRatchetAgreements oracle.braidKem :=
    hK0 ▸ (H1 Tacenta.UnitLifecycleRepair.witnessView).agreements
  obtain ⟨mk, chunk, hdisj⟩ := first_send_responder_prepares byteRng byteCrc byteTrace dh kem
    Tacenta.UnitLifecycleRepair.witnessView oracle H.braid H.triple H.aead H.dhCodec H.oracleOf H.codec
    H.codewordView H.zeroizing80 H.zeroizing32 H.zeroizingKeys H.keyGen H.kemCiphertextLen
    H.kemCiphertextBound byteRng byteCrc ourA _ _ _ rng1 q.session h q rfl emptyPlaintext H.room seed
    H.trace_eq _ _ _ (Tacenta.UnitLifecycleEstablishedEncrypt.byteTrace_two seed (by omega)) bytes s' rng'
    hcall byteRng byteCrc contracts hpub hsym hrt L.optionEq ag ourB storeB hpublish hidentity hdistinct
    hkem seed
  rcases hdisj with ⟨-, e, hrefuse, -⟩ | ⟨p, hpsh, -, -, -, hppi, hppe, -, hpmsg, -, hinv, hhead, hrel⟩
  · exfalso
    rcases hrefuse with ⟨-, hleg⟩ | ⟨-, fp, -, x, hx, -⟩ | ⟨-, -, hne, -⟩
    · simp [storeB, reachStore] at hleg
    · simp [storeB, reachStore] at hx
    · exact hne (by simp [storeB, reachStore])
  · exact ⟨oracle, _, _, rng1, q, bytes, s', rng', ourB, storeB, mk, chunk, p, rfl, H, hcall, hpublish,
      hidentity, hdistinct, hkem, by simp [storeB, reachStore], by simp [storeB, reachStore], hpsh, hppi,
      hppe, hpmsg, hinv, hhead, hrel⟩

end Tacenta.UnitLifecycleResponderFirstFrame

/-! ## Pins

The constants each result depends on, and the statement of each result and definition, held by the
build.  `attest.py` requires every one of them (`REQUIRED_PINS`, `REQUIRED_STATEMENT_PINS`,
`REQUIRED_PRINT_FORM`). -/

/--
info: 'Tacenta.UnitLifecycleResponderFirstFrame.bundle_with_own' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleResponderFirstFrame.bundle_with_own

/--
info: 'Tacenta.UnitLifecycleResponderFirstFrame.establish_initiator_for_secret' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
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
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 tacenta_session_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleResponderFirstFrame.establish_initiator_for_secret

/--
info: 'Tacenta.UnitLifecycleResponderFirstFrame.dhAgreeSymmetric_is' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
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
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleResponderFirstFrame.dhAgreeSymmetric_is

/--
info: 'Tacenta.UnitLifecycleResponderFirstFrame.shared_secret_symmetric' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
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
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleResponderFirstFrame.shared_secret_symmetric

/--
info: 'Tacenta.UnitLifecycleResponderFirstFrame.vec_index_last' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleResponderFirstFrame.vec_index_last

/--
info: 'Tacenta.UnitLifecycleResponderFirstFrame.publish_parts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.kem.KeyPair,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.Pair.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.alloc.vec.Vec.is_empty,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_session_unit.tacenta_boundary.kem.KeyPair.public_key,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleResponderFirstFrame.publish_parts

/--
info: 'Tacenta.UnitLifecycleResponderFirstFrame.one_time_kem_ids_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.kem.KeyPair]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleResponderFirstFrame.one_time_kem_ids_spec

/--
info: 'Tacenta.UnitLifecycleResponderFirstFrame.u32_index_first' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleResponderFirstFrame.u32_index_first

/--
info: 'Tacenta.UnitLifecycleResponderFirstFrame.peek_one_time_first' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.kem.KeyPair,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.Pair.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleResponderFirstFrame.peek_one_time_first

/--
info: 'Tacenta.UnitLifecycleResponderFirstFrame.canonicalKey_arrayOf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleResponderFirstFrame.canonicalKey_arrayOf

/--
info: 'Tacenta.UnitLifecycleResponderFirstFrame.view_of_public' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
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
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleResponderFirstFrame.view_of_public

/--
info: 'Tacenta.UnitLifecycleResponderFirstFrame.identity_public_of_dh_key' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.public_key]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleResponderFirstFrame.identity_public_of_dh_key

/--
info: 'Tacenta.UnitLifecycleResponderFirstFrame.ciphertext_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
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
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleResponderFirstFrame.ciphertext_le

/--
info: 'Tacenta.UnitLifecycleResponderFirstFrame.decode_first_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
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
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleResponderFirstFrame.decode_first_frame

/--
info: 'Tacenta.UnitLifecycleResponderFirstFrame.decode_ec_public' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
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
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleResponderFirstFrame.decode_ec_public

/--
info: 'Tacenta.UnitLifecycleResponderFirstFrame.curve_inputs_of' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.dh.is_prime_order_public,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.from_bytes]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleResponderFirstFrame.curve_inputs_of

/--
info: 'Tacenta.UnitLifecycleResponderFirstFrame.contains_u32' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleResponderFirstFrame.contains_u32

/--
info: 'Tacenta.UnitLifecycleResponderFirstFrame.signed_prekey_own' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.kem.KeyPair,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleResponderFirstFrame.signed_prekey_own

/--
info: 'Tacenta.UnitLifecycleResponderFirstFrame.kem_slot_last_resort' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.kem.KeyPair]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleResponderFirstFrame.kem_slot_last_resort

/--
info: 'Tacenta.UnitLifecycleResponderFirstFrame.kem_slot_one_time' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.kem.KeyPair]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleResponderFirstFrame.kem_slot_one_time

/--
info: 'Tacenta.UnitLifecycleResponderFirstFrame.decapsulate_current' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.kem.KeyPair,
 tacenta_session_unit.tacenta_boundary.kem.decapsulate]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleResponderFirstFrame.decapsulate_current

/--
info: 'Tacenta.UnitLifecycleResponderFirstFrame.decapsulate_one_time' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.kem.KeyPair,
 tacenta_session_unit.tacenta_boundary.kem.decapsulate]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleResponderFirstFrame.decapsulate_one_time

/--
info: 'Tacenta.UnitLifecycleResponderFirstFrame.one_time_key_absent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.kem.KeyPair,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.Pair.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleResponderFirstFrame.one_time_key_absent

/--
info: 'Tacenta.UnitLifecycleResponderFirstFrame.one_time_key_last' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.kem.KeyPair,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.Pair.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleResponderFirstFrame.one_time_key_last

/--
info: 'Tacenta.UnitLifecycleResponderFirstFrame.nodup_append_disjoint' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleResponderFirstFrame.nodup_append_disjoint

/--
info: 'Tacenta.UnitLifecycleResponderFirstFrame.distinct_kem_last' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.kem.KeyPair,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.Pair.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleResponderFirstFrame.distinct_kem_last

/--
info: 'Tacenta.UnitLifecycleResponderFirstFrame.distinct_pool_last' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.kem.KeyPair,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.Pair.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleResponderFirstFrame.distinct_pool_last

/--
info: 'Tacenta.UnitLifecycleResponderFirstFrame.heldKemPair_last' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.kem.KeyPair,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.Pair.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleResponderFirstFrame.heldKemPair_last

/--
info: 'Tacenta.UnitLifecycleResponderFirstFrame.replay_loop_flag' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.kem.KeyPair]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleResponderFirstFrame.replay_loop_flag

/--
info: 'Tacenta.UnitLifecycleResponderFirstFrame.replay_refusal_cause' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.kem.KeyPair]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleResponderFirstFrame.replay_refusal_cause

/--
info: 'Tacenta.UnitLifecycleResponderFirstFrame.establish_responder_slot_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
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
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 tacenta_session_unit.tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 tacenta_session_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.core.option.Option.Insts.CoreCloneClone.clone,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleResponderFirstFrame.establish_responder_slot_refused

/--
info: 'Tacenta.UnitLifecycleResponderFirstFrame.establish_responder_replay_refused_at' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
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
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 tacenta_session_unit.tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 tacenta_session_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.core.option.Option.Insts.CoreCloneClone.clone,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleResponderFirstFrame.establish_responder_replay_refused_at

/--
info: 'Tacenta.UnitLifecycleResponderFirstFrame.parts_of_steps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
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
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleResponderFirstFrame.parts_of_steps

/--
info: 'Tacenta.UnitLifecycleResponderFirstFrame.responder_first_frame_prepares' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
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
 tacenta_session_unit.Pair.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.TupleABC.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.alloc.vec.Vec.capacity,
 tacenta_session_unit.alloc.vec.Vec.is_empty,
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
 tacenta_session_unit.tacenta_boundary.kem.KeyPair.public_key,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 tacenta_session_unit.tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 tacenta_session_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.core.option.Option.Insts.CoreCloneClone.clone,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleResponderFirstFrame.responder_first_frame_prepares

/--
info: 'Tacenta.UnitLifecycleResponderFirstFrame.responder_first_frame_admissible' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
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
 tacenta_session_unit.Pair.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.TupleABC.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.alloc.vec.Vec.capacity,
 tacenta_session_unit.alloc.vec.Vec.is_empty,
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
 tacenta_session_unit.tacenta_boundary.kem.KeyPair.public_key,
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
#print axioms Tacenta.UnitLifecycleResponderFirstFrame.responder_first_frame_admissible

/--
info: 'Tacenta.UnitLifecycleResponderFirstFrame.first_send_responder_prepares' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
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
 tacenta_session_unit.tacenta_boundary.xeddsa.sign,
 tacenta_session_unit.tacenta_boundary.xeddsa.verify,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.generate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.header,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.Pair.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.TupleABC.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.alloc.vec.Vec.capacity,
 tacenta_session_unit.alloc.vec.Vec.is_empty,
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
 tacenta_session_unit.tacenta_boundary.kem.KeyPair.public_key,
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
#print axioms Tacenta.UnitLifecycleResponderFirstFrame.first_send_responder_prepares

/--
info: 'Tacenta.UnitLifecycleResponderFirstFrame.basePoint_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleResponderFirstFrame.basePoint_ne_zero

/--
info: 'Tacenta.UnitLifecycleResponderFirstFrame.modelFirstFrame_dhCodec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleResponderFirstFrame.modelFirstFrame_dhCodec

/--
info: 'Tacenta.UnitLifecycleResponderFirstFrame.modelFirstFrame_dhAgree' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleResponderFirstFrame.modelFirstFrame_dhAgree

/--
info: 'Tacenta.UnitLifecycleResponderFirstFrame.modelFirstFrame_symmetric' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleResponderFirstFrame.modelFirstFrame_symmetric

/--
info: 'Tacenta.UnitLifecycleResponderFirstFrame.first_frame_laws_model' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.rand_core_1.error.Error,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.Pair.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 tacenta_session_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleResponderFirstFrame.first_frame_laws_model

/--
info: 'Tacenta.UnitLifecycleResponderFirstFrame.publish_reachStore' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.kem.KeyPair,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.Pair.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.alloc.vec.Vec.is_empty,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_session_unit.tacenta_boundary.kem.KeyPair.public_key,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleResponderFirstFrame.publish_reachStore

/--
info: 'Tacenta.UnitLifecycleResponderFirstFrame.reachStore_distinct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.kem.KeyPair,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.Pair.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleResponderFirstFrame.reachStore_distinct

/--
info: 'Tacenta.UnitLifecycleResponderFirstFrame.random_secret_byte' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleResponderFirstFrame.random_secret_byte

/--
info: 'Tacenta.UnitLifecycleResponderFirstFrame.reach_establishment' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
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
 tacenta_session_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleResponderFirstFrame.reach_establishment

/--
info: 'Tacenta.UnitLifecycleResponderFirstFrame.first_send_responder_reachable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
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
 tacenta_session_unit.tacenta_boundary.xeddsa.sign,
 tacenta_session_unit.tacenta_boundary.xeddsa.verify,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.generate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.header,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.Pair.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.TupleABC.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.alloc.vec.Vec.capacity,
 tacenta_session_unit.alloc.vec.Vec.is_empty,
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
 tacenta_session_unit.tacenta_boundary.kem.KeyPair.public_key,
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
#print axioms Tacenta.UnitLifecycleResponderFirstFrame.first_send_responder_reachable

set_option pp.deepTerms true
set_option pp.proofs.withType true

/--
info: Tacenta.UnitLifecycleResponderFirstFrame.bundle_with_own : ∀ (b : tacenta_session_unit.PreKeyBundle)
  (o : Option tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes),
  b.one_time_prekey = o →
    { identity_key := b.identity_key, signed_prekey := b.signed_prekey,
        signed_prekey_signature := b.signed_prekey_signature, kem_prekey := b.kem_prekey,
        kem_prekey_signature := b.kem_prekey_signature, one_time_prekey := o } =
      b
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderFirstFrame.bundle_with_own

/--
info: @Tacenta.UnitLifecycleResponderFirstFrame.establish_initiator_for_secret : ∀ {R : Type}
  (rc : tacenta_session_unit.rand_core_1.RngCore R) (crc : tacenta_session_unit.rand_core_1.CryptoRng R)
  (our : tacenta_session_unit.lifecycle.Identity) (bundle : tacenta_session_unit.lifecycle.PublishedBundle)
  (expected : tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes) (rng0 rng1 : R)
  (s : tacenta_session_unit.lifecycle.Session),
  tacenta_session_unit.lifecycle.establish_initiator_for rc crc our bundle expected rng0 =
      Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok s, rng1) →
    ∃ q, s = q.session
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderFirstFrame.establish_initiator_for_secret

/--
info: Tacenta.UnitLifecycleResponderFirstFrame.dhAgreeSymmetric_is : Tacenta.UnitLifecycleResponderFirstFrame.DhAgreeSymmetric ↔
  ∀ (a b : tacenta_session_unit.tacenta_boundary.dh.PrivateKey)
    (pa pb : tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes),
    a.public_key = Aeneas.Std.Result.ok pa → b.public_key = Aeneas.Std.Result.ok pb → a.agree pb = b.agree pa
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderFirstFrame.dhAgreeSymmetric_is

/--
info: Tacenta.UnitLifecycleResponderFirstFrame.shared_secret_symmetric : Tacenta.UnitLifecycleResponderFirstFrame.DhAgreeSymmetric →
  ∀ (ikA eph ikB spk : tacenta_session_unit.tacenta_boundary.dh.PrivateKey)
    (pubA ephPub : tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes) (bundle : tacenta_session_unit.PreKeyBundle)
    (otk : Option tacenta_session_unit.tacenta_boundary.dh.PrivateKey) (enc : Aeneas.Std.Array Aeneas.Std.U8 32#usize),
    ikA.public_key = Aeneas.Std.Result.ok pubA →
      eph.public_key = Aeneas.Std.Result.ok ephPub →
        ikB.public_key = Aeneas.Std.Result.ok bundle.identity_key →
          spk.public_key = Aeneas.Std.Result.ok bundle.signed_prekey →
            Tacenta.UnitLifecycleResponderFirstFrame.OneTimeMatches bundle.one_time_prekey otk →
              tacenta_session_unit.verify_bundle bundle = Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok ()) →
                tacenta_session_unit.is_valid_identity_key pubA = Aeneas.Std.Result.ok true →
                  tacenta_session_unit.responder_shared_secret ikB spk otk pubA ephPub enc =
                    tacenta_session_unit.initiator_shared_secret ikA eph bundle enc
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderFirstFrame.shared_secret_symmetric

/--
info: @Tacenta.UnitLifecycleResponderFirstFrame.vec_index_last : ∀ {α : Type} (v : Aeneas.Std.alloc.vec.Vec α)
  (i : Aeneas.Std.Usize) (x : α),
  Aeneas.Std.alloc.vec.Vec.index (Aeneas.Std.core.slice.index.SliceIndexUsizeSlice α) v i = Aeneas.Std.Result.ok x →
    ↑i = (↑v).length - 1 → (↑v).getLast? = some x
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderFirstFrame.vec_index_last

/--
info: Tacenta.UnitLifecycleResponderFirstFrame.publish_parts : ∀ (store : tacenta_session_unit.lifecycle.PrekeyStore)
  (bundle : tacenta_session_unit.lifecycle.PublishedBundle),
  store.publish = Aeneas.Std.Result.ok bundle →
    bundle.signed_prekey_id = store.signed_prekey_id ∧
      bundle.bundle.identity_key = store.identity_public ∧
        (∃ spk,
            tacenta_session_unit.tacenta_boundary.dh.PrivateKey.from_bytes store.signed_prekey_secret =
                Aeneas.Std.Result.ok spk ∧
              spk.public_key = Aeneas.Std.Result.ok bundle.bundle.signed_prekey) ∧
          (bundle.kem_prekey_id = store.kem_id ∧ store.kem.public_key = Aeneas.Std.Result.ok bundle.bundle.kem_prekey ∨
              ∃ e,
                (↑store.kem_one_time).getLast? = some e ∧
                  bundle.kem_prekey_id = e.1 ∧ e.2.1.public_key = Aeneas.Std.Result.ok bundle.bundle.kem_prekey) ∧
            ∃ v,
              tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
                    Tacenta.UnitLifecycleResponderFirstFrame.zPool store.one_time =
                  Aeneas.Std.Result.ok v ∧
                (bundle.one_time_prekey_id = tacenta_session_unit.serialization.ABSENT_ID ∧
                    bundle.bundle.one_time_prekey = none ∨
                  ∃ e k pk,
                    (↑v).getLast? = some e ∧
                      bundle.one_time_prekey_id = e.1 ∧
                        tacenta_session_unit.tacenta_boundary.dh.PrivateKey.from_bytes e.2 = Aeneas.Std.Result.ok k ∧
                          k.public_key = Aeneas.Std.Result.ok pk ∧ bundle.bundle.one_time_prekey = some pk)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderFirstFrame.publish_parts

/--
info: Tacenta.UnitLifecycleResponderFirstFrame.one_time_kem_ids_spec : ∀ (store : tacenta_session_unit.lifecycle.PrekeyStore),
  Aeneas.Std.WP.spec store.one_time_kem_ids fun ids => ↑ids = List.map (fun x => x.1) ↑store.kem_one_time
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderFirstFrame.one_time_kem_ids_spec

/--
info: Tacenta.UnitLifecycleResponderFirstFrame.u32_index_first : ∀ (values : Aeneas.Std.Slice Aeneas.Std.U32)
  (needle : Aeneas.Std.U32) (pre post : List Aeneas.Std.U32),
  ↑values = pre ++ needle :: post →
    needle ∉ pre →
      Aeneas.Std.WP.spec (tacenta_session_unit.lifecycle.u32_index values needle) fun r =>
        ∃ i, r = some i ∧ ↑i = pre.length
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderFirstFrame.u32_index_first

/--
info: Tacenta.UnitLifecycleResponderFirstFrame.peek_one_time_first : Tacenta.SessionUnitBraidT1.ZeroizingArrayRoundTrip →
  ∀ (store : tacenta_session_unit.lifecycle.PrekeyStore) (id : Aeneas.Std.U32)
    (v : Aeneas.Std.alloc.vec.Vec (Aeneas.Std.U32 × Aeneas.Std.Array Aeneas.Std.U8 32#usize)),
    tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref Tacenta.UnitLifecycleResponderFirstFrame.zPool
          store.one_time =
        Aeneas.Std.Result.ok v →
      ∀ (e : Tacenta.UnitLifecycleResponderFirstFrame.PoolEntry)
        (pre post : List Tacenta.UnitLifecycleResponderFirstFrame.PoolEntry),
        ↑v = pre ++ e :: post →
          e.1 = id →
            id ∉ List.map (fun x => x.1) pre →
              Aeneas.Std.WP.spec (store.peek_one_time id) fun r =>
                ∃ z,
                  r = some z ∧
                    tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
                        Tacenta.UnitLifecycleEstablishResponder.z32 z =
                      Aeneas.Std.Result.ok e.2
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderFirstFrame.peek_one_time_first

/--
info: Tacenta.UnitLifecycleResponderFirstFrame.canonicalKey_arrayOf : ∀ (a : Aeneas.Std.Array Aeneas.Std.U8 32#usize),
  Tacenta.SessionUnitT1.canonicalX25519 a = true →
    Model.Messages.canonicalKey (Tacenta.UnitLifecycleT3.arrayOf a) = true
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderFirstFrame.canonicalKey_arrayOf

/--
info: Tacenta.UnitLifecycleResponderFirstFrame.view_of_public : Tacenta.UnitLifecycleEstablishInitiatorShape.DhPublicValid →
  ∀ {dh : Tacenta.UnitLifecycleT3.DhView},
    Tacenta.UnitLifecycleT3.DhCodecOf dh →
      ∀ {k : tacenta_session_unit.tacenta_boundary.dh.PrivateKey}
        {pk : tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes},
        k.public_key = Aeneas.Std.Result.ok pk →
          ∃ a,
            pk.as_bytes = Aeneas.Std.Result.ok a ∧
              Tacenta.SessionUnitT1.canonicalX25519 a = true ∧ dh.publicKey pk = Tacenta.UnitLifecycleT3.arrayOf a
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderFirstFrame.view_of_public

/--
info: @Tacenta.UnitLifecycleResponderFirstFrame.identity_public_of_dh_key : ∀ {our : tacenta_session_unit.lifecycle.Identity}
  {k : tacenta_session_unit.tacenta_boundary.dh.PrivateKey}
  {pk : tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes},
  our.dh_key = Aeneas.Std.Result.ok k → our.public = Aeneas.Std.Result.ok pk → k.public_key = Aeneas.Std.Result.ok pk
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderFirstFrame.identity_public_of_dh_key

/--
info: Tacenta.UnitLifecycleResponderFirstFrame.ciphertext_le : Tacenta.UnitLifecycleEstablishInitiatorShape.KemCiphertextLenOf →
  Tacenta.UnitLifecycleRestoredSession.KemCiphertextLenBound →
    ∀ {R : Type} {rc : tacenta_session_unit.rand_core_1.RngCore R} {crc : tacenta_session_unit.rand_core_1.CryptoRng R}
      {pk : Aeneas.Std.Slice Aeneas.Std.U8} {rng rng' : R} {ct : Aeneas.Std.alloc.vec.Vec Aeneas.Std.U8}
      {ss : Aeneas.Std.Array Aeneas.Std.U8 32#usize},
      tacenta_session_unit.tacenta_boundary.kem.encapsulate rc crc pk rng =
          Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok (ct, ss), rng') →
        (↑ct).length ≤ 65536
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderFirstFrame.ciphertext_le

/--
info: @Tacenta.UnitLifecycleResponderFirstFrame.decode_first_frame : ∀ {R : Type}
  {rc : tacenta_session_unit.rand_core_1.RngCore R} {crc : tacenta_session_unit.rand_core_1.CryptoRng R}
  {our : tacenta_session_unit.lifecycle.Identity} {bundle : tacenta_session_unit.lifecycle.PublishedBundle},
  Tacenta.UnitLifecycleEstablishInitiatorShape.DhPublicValid →
    ∀ {dh : Tacenta.UnitLifecycleT3.DhView},
      Tacenta.UnitLifecycleT3.DhCodecOf dh →
        Tacenta.UnitLifecycleEstablishInitiatorShape.KemCiphertextLenOf →
          Tacenta.UnitLifecycleRestoredSession.KemCiphertextLenBound →
            ∀ (q : Tacenta.UnitLifecycleResponderFirstFrame.InitiatorSecretParts rc crc our bundle)
              (pending : Model.Lifecycle.PendingInitial),
              (Tacenta.UnitLifecycleEstablishInitiatorShape.establishedModelOf dh q.session).pendingInitial =
                  some pending →
                ∀ (frame : Model.Lifecycle.Bytes) (msg : Aeneas.Std.Slice Aeneas.Std.U8),
                  Tacenta.UnitLifecycleT3.sliceOf msg =
                      Tacenta.UnitLifecycleEstablishedEncrypt.initialWire
                        (Tacenta.UnitLifecycleEstablishInitiatorShape.establishedModelOf dh q.session) pending frame →
                    ∃ d,
                      tacenta_session_unit.tacenta_wire.decode_initial msg =
                          Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok d) ∧
                        d.signed_prekey_id = bundle.signed_prekey_id ∧
                          d.one_time_prekey_id = bundle.one_time_prekey_id ∧
                            d.kem_prekey_id = bundle.kem_prekey_id ∧
                              d.kem_ciphertext.deref = q.kemCiphertext.deref ∧
                                Tacenta.UnitLifecycleT3.sliceOf d.message.deref = frame ∧
                                  Tacenta.UnitLifecycleT3.sliceOf d.identity.deref =
                                      Model.PersistedState.SessionState.encodeEc (dh.publicKey q.ourPublic) ∧
                                    Tacenta.UnitLifecycleT3.sliceOf d.ephemeral.deref =
                                      Model.PersistedState.SessionState.encodeEc (dh.publicKey q.ephemeralPublic)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderFirstFrame.decode_first_frame

/--
info: Tacenta.UnitLifecycleResponderFirstFrame.decode_ec_public : Tacenta.UnitLifecycleSessionCodec.DhPublicBytesRoundTrip →
  ∀ {pk : tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes} {a : Aeneas.Std.Array Aeneas.Std.U8 32#usize},
    pk.as_bytes = Aeneas.Std.Result.ok a →
      Tacenta.SessionUnitT1.canonicalX25519 a = true →
        ∀ (s : Aeneas.Std.Slice Aeneas.Std.U8),
          Tacenta.UnitLifecycleT3.sliceOf s =
              Model.PersistedState.SessionState.encodeEc (Tacenta.UnitLifecycleT3.arrayOf a) →
            tacenta_session_unit.decode_ec s = Aeneas.Std.Result.ok (some pk)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderFirstFrame.decode_ec_public

/--
info: Tacenta.UnitLifecycleResponderFirstFrame.curve_inputs_of : ∀ (identity ephemeral : Aeneas.Std.Slice Aeneas.Std.U8)
  (pi pe : tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes),
  tacenta_session_unit.decode_ec identity = Aeneas.Std.Result.ok (some pi) →
    tacenta_session_unit.is_valid_identity_key pi = Aeneas.Std.Result.ok true →
      tacenta_session_unit.decode_ec ephemeral = Aeneas.Std.Result.ok (some pe) →
        tacenta_session_unit.lifecycle.responder_curve_inputs identity ephemeral =
          Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok (pi, pe))
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderFirstFrame.curve_inputs_of

/--
info: Tacenta.UnitLifecycleResponderFirstFrame.contains_u32 : ∀ (l : Aeneas.Std.alloc.vec.Vec Aeneas.Std.U32)
  (x : Aeneas.Std.U32),
  Aeneas.Std.core.slice.Slice.contains Aeneas.Std.core.cmp.PartialEqU32 l.deref x =
    Aeneas.Std.Result.ok (decide (x ∈ ↑l))
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderFirstFrame.contains_u32

/--
info: Tacenta.UnitLifecycleResponderFirstFrame.signed_prekey_own : ∀ (store : tacenta_session_unit.lifecycle.PrekeyStore)
  (z : tacenta_session_unit.zeroize.Zeroizing (Aeneas.Std.Array Aeneas.Std.U8 32#usize)),
  tacenta_session_unit.zeroize.Zeroizing.new Tacenta.UnitLifecycleEstablishResponder.z32 store.signed_prekey_secret =
      Aeneas.Std.Result.ok z →
    tacenta_session_unit.lifecycle.responder_signed_prekey_secret store store.signed_prekey_id =
      Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok z)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderFirstFrame.signed_prekey_own

/--
info: Tacenta.UnitLifecycleResponderFirstFrame.kem_slot_last_resort : ∀ (store : tacenta_session_unit.lifecycle.PrekeyStore),
  tacenta_session_unit.lifecycle.responder_kem_slot store store.kem_id =
    Aeneas.Std.Result.ok
      (if store.kem_id ∈ ↑store.legacy_last_resort_blocked then
        Aeneas.Std.core.result.Result.Err tacenta_session_unit.lifecycle.Error.LegacyLastResortRecord
      else Aeneas.Std.core.result.Result.Ok (tacenta_session_unit.lifecycle.KemKeySlot.Current, true))
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderFirstFrame.kem_slot_last_resort

/--
info: Tacenta.UnitLifecycleResponderFirstFrame.kem_slot_one_time : ∀ (store : tacenta_session_unit.lifecycle.PrekeyStore)
  (pre : List Tacenta.UnitLifecycleResponderFirstFrame.KemEntry)
  (e : Tacenta.UnitLifecycleResponderFirstFrame.KemEntry),
  ↑store.kem_one_time = pre ++ [e] →
    e.1 ≠ store.kem_id →
      (∀
          (x :
            tacenta_session_unit.tacenta_boundary.kem.KeyPair ×
              Aeneas.Std.U32 × Aeneas.Std.Array Aeneas.Std.U8 64#usize),
          store.previous_kem = some x → x.2.1 ≠ e.1) →
        e.1 ∉ List.map (fun x => x.1) pre →
          ∃ i,
            ↑i = pre.length ∧
              tacenta_session_unit.lifecycle.responder_kem_slot store e.1 =
                Aeneas.Std.Result.ok
                  (Aeneas.Std.core.result.Result.Ok (tacenta_session_unit.lifecycle.KemKeySlot.OneTime i, false))
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderFirstFrame.kem_slot_one_time

/--
info: Tacenta.UnitLifecycleResponderFirstFrame.decapsulate_current : ∀ (store : tacenta_session_unit.lifecycle.PrekeyStore)
  (ct : Aeneas.Std.Slice Aeneas.Std.U8) (ss : Aeneas.Std.Array Aeneas.Std.U8 32#usize),
  tacenta_session_unit.tacenta_boundary.kem.decapsulate store.kem ct =
      Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok ss) →
    tacenta_session_unit.lifecycle.responder_decapsulate store tacenta_session_unit.lifecycle.KemKeySlot.Current ct =
      Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok ss)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderFirstFrame.decapsulate_current

/--
info: Tacenta.UnitLifecycleResponderFirstFrame.decapsulate_one_time : ∀ (store : tacenta_session_unit.lifecycle.PrekeyStore)
  (pre : List Tacenta.UnitLifecycleResponderFirstFrame.KemEntry)
  (e : Tacenta.UnitLifecycleResponderFirstFrame.KemEntry),
  ↑store.kem_one_time = pre ++ [e] →
    ∀ (i : Aeneas.Std.Usize),
      ↑i = pre.length →
        ∀ (ct : Aeneas.Std.Slice Aeneas.Std.U8) (ss : Aeneas.Std.Array Aeneas.Std.U8 32#usize),
          tacenta_session_unit.tacenta_boundary.kem.decapsulate e.2.1 ct =
              Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok ss) →
            tacenta_session_unit.lifecycle.responder_decapsulate store
                (tacenta_session_unit.lifecycle.KemKeySlot.OneTime i) ct =
              Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok ss)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderFirstFrame.decapsulate_one_time

/--
info: Tacenta.UnitLifecycleResponderFirstFrame.one_time_key_absent : ∀ (store : tacenta_session_unit.lifecycle.PrekeyStore),
  tacenta_session_unit.lifecycle.responder_one_time_key store tacenta_session_unit.serialization.ABSENT_ID =
    Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok none)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderFirstFrame.one_time_key_absent

/--
info: Tacenta.UnitLifecycleResponderFirstFrame.one_time_key_last : Tacenta.SessionUnitBraidT1.ZeroizingArrayRoundTrip →
  ∀ (store : tacenta_session_unit.lifecycle.PrekeyStore)
    (v : Aeneas.Std.alloc.vec.Vec Tacenta.UnitLifecycleResponderFirstFrame.PoolEntry),
    tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref Tacenta.UnitLifecycleResponderFirstFrame.zPool
          store.one_time =
        Aeneas.Std.Result.ok v →
      ∀ (pre : List Tacenta.UnitLifecycleResponderFirstFrame.PoolEntry)
        (e : Tacenta.UnitLifecycleResponderFirstFrame.PoolEntry),
        ↑v = pre ++ [e] →
          e.1 ≠ tacenta_session_unit.serialization.ABSENT_ID →
            e.1 ∉ List.map (fun x => x.1) pre →
              ∀ (k : tacenta_session_unit.tacenta_boundary.dh.PrivateKey),
                tacenta_session_unit.tacenta_boundary.dh.PrivateKey.from_bytes e.2 = Aeneas.Std.Result.ok k →
                  tacenta_session_unit.lifecycle.responder_one_time_key store e.1 =
                    Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok (some k))
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderFirstFrame.one_time_key_last

/--
info: @Tacenta.UnitLifecycleResponderFirstFrame.nodup_append_disjoint : ∀ {α : Type} {l1 l2 : List α},
  (l1 ++ l2).Nodup → ∀ {a : α}, a ∈ l1 → a ∈ l2 → False
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderFirstFrame.nodup_append_disjoint

/--
info: @Tacenta.UnitLifecycleResponderFirstFrame.distinct_kem_last : ∀ {store : tacenta_session_unit.lifecycle.PrekeyStore},
  Tacenta.UnitLifecycleResponderFirstFrame.PrekeyIdsDistinct store →
    ∀ {pre : List Tacenta.UnitLifecycleResponderFirstFrame.KemEntry}
      {e : Tacenta.UnitLifecycleResponderFirstFrame.KemEntry},
      ↑store.kem_one_time = pre ++ [e] →
        e.1 ≠ store.kem_id ∧
          (∀
              (x :
                tacenta_session_unit.tacenta_boundary.kem.KeyPair ×
                  Aeneas.Std.U32 × Aeneas.Std.Array Aeneas.Std.U8 64#usize),
              store.previous_kem = some x → x.2.1 ≠ e.1) ∧
            e.1 ∉ List.map (fun x => x.1) pre
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderFirstFrame.distinct_kem_last

/--
info: @Tacenta.UnitLifecycleResponderFirstFrame.distinct_pool_last : ∀ {store : tacenta_session_unit.lifecycle.PrekeyStore},
  Tacenta.UnitLifecycleResponderFirstFrame.PrekeyIdsDistinct store →
    ∀ {v : Aeneas.Std.alloc.vec.Vec Tacenta.UnitLifecycleResponderFirstFrame.PoolEntry},
      tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
            Tacenta.UnitLifecycleResponderFirstFrame.zPool store.one_time =
          Aeneas.Std.Result.ok v →
        ∀ {pre : List Tacenta.UnitLifecycleResponderFirstFrame.PoolEntry}
          {e : Tacenta.UnitLifecycleResponderFirstFrame.PoolEntry},
          ↑v = pre ++ [e] → e.1 ≠ tacenta_session_unit.serialization.ABSENT_ID ∧ e.1 ∉ List.map (fun x => x.1) pre
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderFirstFrame.distinct_pool_last

/--
info: @Tacenta.UnitLifecycleResponderFirstFrame.heldKemPair_last : ∀ {store : tacenta_session_unit.lifecycle.PrekeyStore},
  Tacenta.UnitLifecycleResponderFirstFrame.PrekeyIdsDistinct store →
    ∀ {pre : List Tacenta.UnitLifecycleResponderFirstFrame.KemEntry}
      {e : Tacenta.UnitLifecycleResponderFirstFrame.KemEntry},
      ↑store.kem_one_time = pre ++ [e] → Tacenta.UnitLifecycleResponderFirstFrame.heldKemPair store e.1 = some e.2.1
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderFirstFrame.heldKemPair_last

/--
info: Tacenta.UnitLifecycleResponderFirstFrame.replay_loop_flag : ∀ (store : tacenta_session_unit.lifecycle.PrekeyStore)
  (fp : Aeneas.Std.Array Aeneas.Std.U8 32#usize),
  Aeneas.Std.WP.spec (tacenta_session_unit.lifecycle.responder_replay_fingerprint_loop store fp false 0#usize) fun r =>
    r =
      (store.identity_public, store.signed_prekey_secret, store.signed_prekey_id, store.signed_prekey_sig,
        store.one_time, store.kem, store.kem_id, store.kem_sig, store.kem_one_time, store.previous_signed_prekey,
        store.previous_kem, store.next_id, store.last_resort_seen, store.legacy_last_resort_blocked,
        decide (∃ x ∈ ↑store.last_resort_seen, x.2 = fp))
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderFirstFrame.replay_loop_flag

/--
info: Tacenta.UnitLifecycleResponderFirstFrame.replay_refusal_cause : ∀ (store : tacenta_session_unit.lifecycle.PrekeyStore)
  (kemId : Aeneas.Std.U32) (sk : Aeneas.Std.Array Aeneas.Std.U8 32#usize) (e : tacenta_session_unit.lifecycle.Error),
  tacenta_session_unit.lifecycle.responder_replay_fingerprint store kemId sk true =
      Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Err e) →
    ∃ fp,
      tacenta_session_unit.lifecycle.last_resort_fingerprint sk = Aeneas.Std.Result.ok fp ∧
        ((e = tacenta_session_unit.lifecycle.Error.ReplayedLastResort ∧ ∃ x ∈ ↑store.last_resort_seen, x.2 = fp) ∨
          e = tacenta_session_unit.lifecycle.Error.LastResortRecordFull ∧
            (¬∃ x ∈ ↑store.last_resort_seen, x.2 = fp) ∧
              ↑store.last_resort_seen ≠ [] ∧
                ∃ n,
                  store.last_resort_seen_for kemId = Aeneas.Std.Result.ok n ∧
                    tacenta_session_unit.lifecycle.MAX_LAST_RESORT_SEEN ≤ n)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderFirstFrame.replay_refusal_cause

/--
info: @Tacenta.UnitLifecycleResponderFirstFrame.establish_responder_slot_refused : ∀ {E : Type}
  (rcB : tacenta_session_unit.rand_core_1.RngCore E) (crcB : tacenta_session_unit.rand_core_1.CryptoRng E)
  (ourB : tacenta_session_unit.lifecycle.Identity) (store : tacenta_session_unit.lifecycle.PrekeyStore)
  (msg : Aeneas.Std.Slice Aeneas.Std.U8) (rng : E) (d : tacenta_session_unit.tacenta_wire.DecodedInitial),
  tacenta_session_unit.tacenta_wire.decode_initial msg = Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok d) →
    ∀ (zs : tacenta_session_unit.zeroize.Zeroizing (Aeneas.Std.Array Aeneas.Std.U8 32#usize)),
      tacenta_session_unit.lifecycle.responder_signed_prekey_secret store d.signed_prekey_id =
          Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok zs) →
        ∀ (e : tacenta_session_unit.lifecycle.Error),
          tacenta_session_unit.lifecycle.responder_kem_slot store d.kem_prekey_id =
              Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Err e) →
            tacenta_session_unit.lifecycle.establish_responder rcB crcB ourB store msg rng =
              Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Err e, store, rng)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderFirstFrame.establish_responder_slot_refused

/--
info: @Tacenta.UnitLifecycleResponderFirstFrame.establish_responder_replay_refused_at : ∀ {E : Type}
  (rcB : tacenta_session_unit.rand_core_1.RngCore E) (crcB : tacenta_session_unit.rand_core_1.CryptoRng E)
  (ourB : tacenta_session_unit.lifecycle.Identity) (store : tacenta_session_unit.lifecycle.PrekeyStore)
  (msg : Aeneas.Std.Slice Aeneas.Std.U8) (rng : E) (d : tacenta_session_unit.tacenta_wire.DecodedInitial),
  tacenta_session_unit.tacenta_wire.decode_initial msg = Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok d) →
    ∀ (zs : tacenta_session_unit.zeroize.Zeroizing (Aeneas.Std.Array Aeneas.Std.U8 32#usize)),
      tacenta_session_unit.lifecycle.responder_signed_prekey_secret store d.signed_prekey_id =
          Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok zs) →
        ∀ (slot : tacenta_session_unit.lifecycle.KemKeySlot) (lr : Bool),
          tacenta_session_unit.lifecycle.responder_kem_slot store d.kem_prekey_id =
              Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok (slot, lr)) →
            ∀ (pi pe : tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes),
              tacenta_session_unit.lifecycle.responder_curve_inputs d.identity.deref d.ephemeral.deref =
                  Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok (pi, pe)) →
                ∀ (otk : Option tacenta_session_unit.tacenta_boundary.dh.PrivateKey),
                  tacenta_session_unit.lifecycle.responder_one_time_key store d.one_time_prekey_id =
                      Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok otk) →
                    ∀ (ks : Aeneas.Std.Array Aeneas.Std.U8 32#usize),
                      tacenta_session_unit.lifecycle.responder_decapsulate store slot d.kem_ciphertext.deref =
                          Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok ks) →
                        ∀ (ksz : tacenta_session_unit.zeroize.Zeroizing (Aeneas.Std.Array Aeneas.Std.U8 32#usize)),
                          tacenta_session_unit.zeroize.Zeroizing.new Tacenta.UnitLifecycleEstablishResponder.z32 ks =
                              Aeneas.Std.Result.ok ksz →
                            ∀ (sb : Aeneas.Std.Array Aeneas.Std.U8 32#usize),
                              tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
                                    Tacenta.UnitLifecycleEstablishResponder.z32 zs =
                                  Aeneas.Std.Result.ok sb →
                                ∀ (spk : tacenta_session_unit.tacenta_boundary.dh.PrivateKey),
                                  tacenta_session_unit.tacenta_boundary.dh.PrivateKey.from_bytes sb =
                                      Aeneas.Std.Result.ok spk →
                                    ∀ (ik : tacenta_session_unit.tacenta_boundary.dh.PrivateKey),
                                      ourB.dh_key = Aeneas.Std.Result.ok ik →
                                        ∀ (enc : Aeneas.Std.Array Aeneas.Std.U8 32#usize),
                                          tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
                                                Tacenta.UnitLifecycleEstablishResponder.z32 ksz =
                                              Aeneas.Std.Result.ok enc →
                                            ∀ (sh : Aeneas.Std.Array Aeneas.Std.U8 32#usize),
                                              tacenta_session_unit.responder_shared_secret ik spk otk pi pe enc =
                                                  Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok sh) →
                                                ∀
                                                  (shz :
                                                    tacenta_session_unit.zeroize.Zeroizing
                                                      (Aeneas.Std.Array Aeneas.Std.U8 32#usize)),
                                                  tacenta_session_unit.zeroize.Zeroizing.new
                                                        Tacenta.UnitLifecycleEstablishResponder.z32 sh =
                                                      Aeneas.Std.Result.ok shz →
                                                    ∀ (shb : Aeneas.Std.Array Aeneas.Std.U8 32#usize),
                                                      tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
                                                            Tacenta.UnitLifecycleEstablishResponder.z32 shz =
                                                          Aeneas.Std.Result.ok shb →
                                                        ∀ (e : tacenta_session_unit.lifecycle.Error),
                                                          tacenta_session_unit.lifecycle.responder_replay_fingerprint
                                                                store d.kem_prekey_id shb lr =
                                                              Aeneas.Std.Result.ok
                                                                (Aeneas.Std.core.result.Result.Err e) →
                                                            tacenta_session_unit.lifecycle.establish_responder rcB crcB
                                                                ourB store msg rng =
                                                              Aeneas.Std.Result.ok
                                                                (Aeneas.Std.core.result.Result.Err e, store, rng)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderFirstFrame.establish_responder_replay_refused_at

/--
info: @Tacenta.UnitLifecycleResponderFirstFrame.parts_of_steps : ∀ {E : Type}
  (rcB : tacenta_session_unit.rand_core_1.RngCore E)
  (contracts : Tacenta.UnitLifecycleT1.EstablishResponderContracts rcB) (ourB : tacenta_session_unit.lifecycle.Identity)
  (store : tacenta_session_unit.lifecycle.PrekeyStore) (msg : Aeneas.Std.Slice Aeneas.Std.U8)
  (d : tacenta_session_unit.tacenta_wire.DecodedInitial),
  tacenta_session_unit.tacenta_wire.decode_initial msg = Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok d) →
    ∀ (zs : tacenta_session_unit.zeroize.Zeroizing (Aeneas.Std.Array Aeneas.Std.U8 32#usize)),
      tacenta_session_unit.lifecycle.responder_signed_prekey_secret store d.signed_prekey_id =
          Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok zs) →
        ∀ (slot : tacenta_session_unit.lifecycle.KemKeySlot) (lr : Bool),
          tacenta_session_unit.lifecycle.responder_kem_slot store d.kem_prekey_id =
              Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok (slot, lr)) →
            ∀ (pi pe : tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes),
              tacenta_session_unit.lifecycle.responder_curve_inputs d.identity.deref d.ephemeral.deref =
                  Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok (pi, pe)) →
                ∀ (otk : Option tacenta_session_unit.tacenta_boundary.dh.PrivateKey),
                  tacenta_session_unit.lifecycle.responder_one_time_key store d.one_time_prekey_id =
                      Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok otk) →
                    ∀ (ks : Aeneas.Std.Array Aeneas.Std.U8 32#usize),
                      tacenta_session_unit.lifecycle.responder_decapsulate store slot d.kem_ciphertext.deref =
                          Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok ks) →
                        ∀ (ksz : tacenta_session_unit.zeroize.Zeroizing (Aeneas.Std.Array Aeneas.Std.U8 32#usize)),
                          tacenta_session_unit.zeroize.Zeroizing.new Tacenta.UnitLifecycleEstablishResponder.z32 ks =
                              Aeneas.Std.Result.ok ksz →
                            ∀ (sb : Aeneas.Std.Array Aeneas.Std.U8 32#usize),
                              tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
                                    Tacenta.UnitLifecycleEstablishResponder.z32 zs =
                                  Aeneas.Std.Result.ok sb →
                                ∀ (spk : tacenta_session_unit.tacenta_boundary.dh.PrivateKey),
                                  tacenta_session_unit.tacenta_boundary.dh.PrivateKey.from_bytes sb =
                                      Aeneas.Std.Result.ok spk →
                                    ∀ (ik : tacenta_session_unit.tacenta_boundary.dh.PrivateKey),
                                      ourB.dh_key = Aeneas.Std.Result.ok ik →
                                        ∀ (enc : Aeneas.Std.Array Aeneas.Std.U8 32#usize),
                                          tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
                                                Tacenta.UnitLifecycleEstablishResponder.z32 ksz =
                                              Aeneas.Std.Result.ok enc →
                                            ∀ (sh : Aeneas.Std.Array Aeneas.Std.U8 32#usize),
                                              tacenta_session_unit.responder_shared_secret ik spk otk pi pe enc =
                                                  Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok sh) →
                                                ∀
                                                  (shz :
                                                    tacenta_session_unit.zeroize.Zeroizing
                                                      (Aeneas.Std.Array Aeneas.Std.U8 32#usize)),
                                                  tacenta_session_unit.zeroize.Zeroizing.new
                                                        Tacenta.UnitLifecycleEstablishResponder.z32 sh =
                                                      Aeneas.Std.Result.ok shz →
                                                    ∀ (shb : Aeneas.Std.Array Aeneas.Std.U8 32#usize),
                                                      tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
                                                            Tacenta.UnitLifecycleEstablishResponder.z32 shz =
                                                          Aeneas.Std.Result.ok shb →
                                                        ∀ (r : Option (Aeneas.Std.Array Aeneas.Std.U8 32#usize)),
                                                          tacenta_session_unit.lifecycle.responder_replay_fingerprint
                                                                store d.kem_prekey_id shb lr =
                                                              Aeneas.Std.Result.ok
                                                                (Aeneas.Std.core.result.Result.Ok r) →
                                                            ∀ (sl : Aeneas.Std.Slice Aeneas.Std.U8),
                                                              Tacenta.UnitLifecycleEstablishResponder.fullSlice shb =
                                                                  Aeneas.Std.Result.ok sl →
                                                                ∃ p,
                                                                  p.decoded = d ∧
                                                                    p.lastResort = lr ∧
                                                                      p.peerIdentity = pi ∧
                                                                        p.peerEphemeral = pe ∧
                                                                          p.oneTime = otk ∧
                                                                            p.kemSecret = ks ∧
                                                                              p.signedPrekey = spk ∧
                                                                                p.shared = sh ∧
                                                                                  p.secret = shb ∧
                                                                                    p.tripleSecret = sl ∧
                                                                                      p.braidSecret = sl
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderFirstFrame.parts_of_steps

/--
info: @Tacenta.UnitLifecycleResponderFirstFrame.responder_first_frame_prepares : ∀ {R : Type}
  {rc : tacenta_session_unit.rand_core_1.RngCore R} {crc : tacenta_session_unit.rand_core_1.CryptoRng R}
  {our : tacenta_session_unit.lifecycle.Identity} {bundle : tacenta_session_unit.lifecycle.PublishedBundle} {E : Type}
  (rcB : tacenta_session_unit.rand_core_1.RngCore E) (crcB : tacenta_session_unit.rand_core_1.CryptoRng E)
  (contracts : Tacenta.UnitLifecycleT1.EstablishResponderContracts rcB),
  Tacenta.UnitLifecycleEstablishInitiatorShape.DhPublicValid →
    Tacenta.UnitLifecycleResponderFirstFrame.DhAgreeSymmetric →
      Tacenta.UnitLifecycleSessionCodec.DhPublicBytesRoundTrip →
        Tacenta.UnitLifecycleEstablishInitiatorShape.KemCiphertextLenOf →
          Tacenta.UnitLifecycleRestoredSession.KemCiphertextLenBound →
            ∀ {dh : Tacenta.UnitLifecycleT3.DhView},
              Tacenta.UnitLifecycleT3.DhCodecOf dh →
                ∀ (q : Tacenta.UnitLifecycleResponderFirstFrame.InitiatorSecretParts rc crc our bundle)
                  (pending : Model.Lifecycle.PendingInitial),
                  (Tacenta.UnitLifecycleEstablishInitiatorShape.establishedModelOf dh q.session).pendingInitial =
                      some pending →
                    ∀ (frame : Model.Lifecycle.Bytes) (msg : Aeneas.Std.Slice Aeneas.Std.U8),
                      Tacenta.UnitLifecycleT3.sliceOf msg =
                          Tacenta.UnitLifecycleEstablishedEncrypt.initialWire
                            (Tacenta.UnitLifecycleEstablishInitiatorShape.establishedModelOf dh q.session) pending
                            frame →
                        ∀ (ourB : tacenta_session_unit.lifecycle.Identity)
                          (storeB : tacenta_session_unit.lifecycle.PrekeyStore),
                          storeB.publish = Aeneas.Std.Result.ok bundle →
                            ourB.public = Aeneas.Std.Result.ok storeB.identity_public →
                              Tacenta.UnitLifecycleResponderFirstFrame.PrekeyIdsDistinct storeB →
                                Tacenta.UnitLifecycleResponderFirstFrame.FirstKemAgrees storeB bundle.kem_prekey_id
                                    q.kemCiphertext q.kemSecret →
                                  ∀ (rngB : E),
                                    (bundle.kem_prekey_id = storeB.kem_id ∧
                                        ∃ e,
                                          Tacenta.UnitLifecycleResponderFirstFrame.StoreRefusal storeB q.sharedBytes e ∧
                                            tacenta_session_unit.lifecycle.establish_responder rcB crcB ourB storeB msg
                                                rngB =
                                              Aeneas.Std.Result.ok
                                                (Aeneas.Std.core.result.Result.Err e, storeB, rngB)) ∨
                                      ∃ p,
                                        p.shared = q.shared ∧
                                          p.secret = q.sharedBytes ∧
                                            p.tripleSecret = q.sharedSlice ∧
                                              p.braidSecret = q.sharedSlice ∧
                                                p.peerIdentity = q.ourPublic ∧
                                                  p.peerEphemeral = q.ephemeralPublic ∧
                                                    p.kemSecret = q.kemSecret ∧
                                                      Tacenta.UnitLifecycleT3.sliceOf p.message = frame ∧
                                                        (p.lastResort = true ↔ bundle.kem_prekey_id = storeB.kem_id)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderFirstFrame.responder_first_frame_prepares

/--
info: @Tacenta.UnitLifecycleResponderFirstFrame.responder_first_frame_admissible : ∀ {R : Type}
  {rc : tacenta_session_unit.rand_core_1.RngCore R} {crc : tacenta_session_unit.rand_core_1.CryptoRng R}
  {our : tacenta_session_unit.lifecycle.Identity} {bundle : tacenta_session_unit.lifecycle.PublishedBundle} {E : Type}
  (rcB : tacenta_session_unit.rand_core_1.RngCore E) (crcB : tacenta_session_unit.rand_core_1.CryptoRng E)
  (contracts : Tacenta.UnitLifecycleT1.EstablishResponderContracts rcB),
  Tacenta.UnitLifecycleEstablishInitiatorShape.DhPublicValid →
    Tacenta.UnitLifecycleResponderFirstFrame.DhAgreeSymmetric →
      Tacenta.UnitLifecycleSessionCodec.DhPublicBytesRoundTrip →
        Tacenta.UnitLifecycleEstablishInitiatorShape.KemCiphertextLenOf →
          Tacenta.UnitLifecycleRestoredSession.KemCiphertextLenBound →
            Tacenta.UnitHeadroomInvariant.OptionEqU64Shape
                @tacenta_session_unit.core.option.Option.Insts.CoreCmpPartialEqOption.eq →
              ∀ {K : Model.Braid.Kem},
                Tacenta.UnitLifecycleDecryptRatchetT3.DecryptRatchetAgreements K →
                  ∀ {dh : Tacenta.UnitLifecycleT3.DhView},
                    Tacenta.UnitLifecycleT3.DhCodecOf dh →
                      ∀ (q : Tacenta.UnitLifecycleResponderFirstFrame.InitiatorSecretParts rc crc our bundle)
                        (pending : Model.Lifecycle.PendingInitial),
                        (Tacenta.UnitLifecycleEstablishInitiatorShape.establishedModelOf dh q.session).pendingInitial =
                            some pending →
                          ∀ (frame : Model.Lifecycle.Bytes) (msg : Aeneas.Std.Slice Aeneas.Std.U8),
                            Tacenta.UnitLifecycleT3.sliceOf msg =
                                Tacenta.UnitLifecycleEstablishedEncrypt.initialWire
                                  (Tacenta.UnitLifecycleEstablishInitiatorShape.establishedModelOf dh q.session) pending
                                  frame →
                              ∀ (ourB : tacenta_session_unit.lifecycle.Identity)
                                (storeB : tacenta_session_unit.lifecycle.PrekeyStore),
                                storeB.publish = Aeneas.Std.Result.ok bundle →
                                  ourB.public = Aeneas.Std.Result.ok storeB.identity_public →
                                    Tacenta.UnitLifecycleResponderFirstFrame.PrekeyIdsDistinct storeB →
                                      Tacenta.UnitLifecycleResponderFirstFrame.FirstKemAgrees storeB
                                          bundle.kem_prekey_id q.kemCiphertext q.kemSecret →
                                        ∀ (rngB : E),
                                          (bundle.kem_prekey_id = storeB.kem_id ∧
                                              ∃ e,
                                                Tacenta.UnitLifecycleResponderFirstFrame.StoreRefusal storeB
                                                    q.sharedBytes e ∧
                                                  tacenta_session_unit.lifecycle.establish_responder rcB crcB ourB
                                                      storeB msg rngB =
                                                    Aeneas.Std.Result.ok
                                                      (Aeneas.Std.core.result.Result.Err e, storeB, rngB)) ∨
                                            ∃ p,
                                              p.shared = q.shared ∧
                                                p.secret = q.sharedBytes ∧
                                                  p.tripleSecret = q.sharedSlice ∧
                                                    p.braidSecret = q.sharedSlice ∧
                                                      p.peerIdentity = q.ourPublic ∧
                                                        p.peerEphemeral = q.ephemeralPublic ∧
                                                          p.kemSecret = q.kemSecret ∧
                                                            Tacenta.UnitLifecycleT3.sliceOf p.message = frame ∧
                                                              (p.lastResort = true ↔
                                                                  bundle.kem_prekey_id = storeB.kem_id) ∧
                                                                p.session.invariant = Aeneas.Std.Result.ok true ∧
                                                                  Tacenta.UnitLifecycleDecryptRunBounds.CounterHeadroom
                                                                      p.session ∧
                                                                    Tacenta.UnitLifecycleT3.SessionRefines dh K
                                                                      p.session
                                                                      (Tacenta.UnitLifecycleEstablishResponder.responderModelOf
                                                                        dh p)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderFirstFrame.responder_first_frame_admissible

/--
info: @Tacenta.UnitLifecycleResponderFirstFrame.first_send_responder_prepares : ∀ {R : Type}
  [Tacenta.SessionUnitT1.DerivedKeysModel] {E F : Type} (rc : tacenta_session_unit.rand_core_1.RngCore R)
  (crc : tacenta_session_unit.rand_core_1.CryptoRng R) (trace : R → List Model.Lifecycle.Key)
  (dh : Tacenta.UnitLifecycleT3.DhView) (kem : Tacenta.UnitLifecycleT3.KemView) (view : Model.Lifecycle.CodewordView)
  (oracle : Model.Lifecycle.Oracle),
  Tacenta.UnitLifecycleT3.BraidSendRefinementContracts rc oracle.braidKem →
    Tacenta.UnitLifecycleT3.TripleSendRefinementContracts →
      Tacenta.UnitLifecycleT1.AeadSealBounded →
        Tacenta.UnitLifecycleT1.DhCodecTotal →
          Tacenta.UnitLifecycleT3.OracleOf rc crc dh kem trace oracle →
            Tacenta.UnitLifecycleT3.DhCodecOf dh →
              Tacenta.UnitLifecycleT3.CodewordViewSendOf view →
                Tacenta.SessionUnitT3.ZeroizingRoundTrips80 →
                  Tacenta.UnitLifecycleT3.ZeroizingRoundTrips (Aeneas.Std.Array Aeneas.Std.U8 32#usize) →
                    Tacenta.UnitLifecycleT3.ZeroizingRoundTrips
                        (Aeneas.Std.Array Aeneas.Std.U8 32#usize ×
                          Aeneas.Std.Array Aeneas.Std.U8 32#usize × Aeneas.Std.Array Aeneas.Std.U8 16#usize) →
                      Tacenta.UnitLifecycleEstablishedEncrypt.KeyGenSeededFor oracle.braidKem rc crc trace →
                        Tacenta.UnitLifecycleEstablishInitiatorShape.KemCiphertextLenOf →
                          Tacenta.UnitLifecycleRestoredSession.KemCiphertextLenBound →
                            ∀ (rcE : tacenta_session_unit.rand_core_1.RngCore E)
                              (crcE : tacenta_session_unit.rand_core_1.CryptoRng E)
                              (ourA : tacenta_session_unit.lifecycle.Identity)
                              (bundleA : tacenta_session_unit.lifecycle.PublishedBundle)
                              (expected : tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes) (rng0 rng1 : E)
                              (s : tacenta_session_unit.lifecycle.Session),
                              tacenta_session_unit.lifecycle.establish_initiator_for rcE crcE ourA bundleA expected
                                    rng0 =
                                  Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok s, rng1) →
                                ∀
                                  (q :
                                    Tacenta.UnitLifecycleResponderFirstFrame.InitiatorSecretParts rcE crcE ourA
                                      bundleA),
                                  s = q.session →
                                    ∀ (plaintext : Aeneas.Std.Slice Aeneas.Std.U8),
                                      (↑plaintext).length + 65770 ≤ Aeneas.Std.Usize.max →
                                        ∀ (rng : R),
                                          trace rng = oracle.draws →
                                            ∀ (d1 d2 : Model.Lifecycle.Key) (rest : List Model.Lifecycle.Key),
                                              trace rng = d1 :: d2 :: rest →
                                                ∀ (bytes : Aeneas.Std.alloc.vec.Vec Aeneas.Std.U8)
                                                  (s' : tacenta_session_unit.lifecycle.Session) (rng' : R),
                                                  tacenta_session_unit.lifecycle.Session.encrypt rc crc s plaintext
                                                        rng =
                                                      Aeneas.Std.Result.ok
                                                        (Aeneas.Std.core.result.Result.Ok bytes, s', rng') →
                                                    ∀ (rcB : tacenta_session_unit.rand_core_1.RngCore F)
                                                      (crcB : tacenta_session_unit.rand_core_1.CryptoRng F)
                                                      (contracts :
                                                        Tacenta.UnitLifecycleT1.EstablishResponderContracts rcB),
                                                      Tacenta.UnitLifecycleEstablishInitiatorShape.DhPublicValid →
                                                        Tacenta.UnitLifecycleResponderFirstFrame.DhAgreeSymmetric →
                                                          Tacenta.UnitLifecycleSessionCodec.DhPublicBytesRoundTrip →
                                                            Tacenta.UnitHeadroomInvariant.OptionEqU64Shape
                                                                @tacenta_session_unit.core.option.Option.Insts.CoreCmpPartialEqOption.eq →
                                                              ∀ {K : Model.Braid.Kem},
                                                                Tacenta.UnitLifecycleDecryptRatchetT3.DecryptRatchetAgreements
                                                                    K →
                                                                  ∀ (ourB : tacenta_session_unit.lifecycle.Identity)
                                                                    (storeB :
                                                                      tacenta_session_unit.lifecycle.PrekeyStore),
                                                                    storeB.publish = Aeneas.Std.Result.ok bundleA →
                                                                      ourB.public =
                                                                          Aeneas.Std.Result.ok storeB.identity_public →
                                                                        Tacenta.UnitLifecycleResponderFirstFrame.PrekeyIdsDistinct
                                                                            storeB →
                                                                          Tacenta.UnitLifecycleResponderFirstFrame.FirstKemAgrees
                                                                              storeB bundleA.kem_prekey_id
                                                                              q.kemCiphertext q.kemSecret →
                                                                            ∀ (rngB : F),
                                                                              ∃ messageKey chunk,
                                                                                (bundleA.kem_prekey_id = storeB.kem_id ∧
                                                                                    ∃ e,
                                                                                      Tacenta.UnitLifecycleResponderFirstFrame.StoreRefusal
                                                                                          storeB q.sharedBytes e ∧
                                                                                        tacenta_session_unit.lifecycle.establish_responder
                                                                                            rcB crcB ourB storeB
                                                                                            bytes.deref rngB =
                                                                                          Aeneas.Std.Result.ok
                                                                                            (Aeneas.Std.core.result.Result.Err
                                                                                                e,
                                                                                              storeB, rngB)) ∨
                                                                                  ∃ p,
                                                                                    p.shared = q.shared ∧
                                                                                      p.secret = q.sharedBytes ∧
                                                                                        p.tripleSecret = q.sharedSlice ∧
                                                                                          p.braidSecret =
                                                                                              q.sharedSlice ∧
                                                                                            p.peerIdentity =
                                                                                                q.ourPublic ∧
                                                                                              p.peerEphemeral =
                                                                                                  q.ephemeralPublic ∧
                                                                                                p.kemSecret =
                                                                                                    q.kemSecret ∧
                                                                                                  Tacenta.UnitLifecycleT3.sliceOf
                                                                                                        p.message =
                                                                                                      Tacenta.UnitLifecycleEstablishedEncrypt.firstFrame
                                                                                                        view oracle
                                                                                                        (Tacenta.UnitLifecycleEstablishInitiatorShape.establishedModelOf
                                                                                                          dh s)
                                                                                                        (Tacenta.UnitLifecycleT3.sliceOf
                                                                                                          plaintext)
                                                                                                        messageKey
                                                                                                        chunk ∧
                                                                                                    (p.lastResort =
                                                                                                          true ↔
                                                                                                        bundleA.kem_prekey_id =
                                                                                                          storeB.kem_id) ∧
                                                                                                      p.session.invariant =
                                                                                                          Aeneas.Std.Result.ok
                                                                                                            true ∧
                                                                                                        Tacenta.UnitLifecycleDecryptRunBounds.CounterHeadroom
                                                                                                            p.session ∧
                                                                                                          Tacenta.UnitLifecycleT3.SessionRefines
                                                                                                            dh K
                                                                                                            p.session
                                                                                                            (Tacenta.UnitLifecycleEstablishResponder.responderModelOf
                                                                                                              dh p)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderFirstFrame.first_send_responder_prepares

/--
info: Tacenta.UnitLifecycleResponderFirstFrame.basePoint_ne_zero : ↑Tacenta.UnitLifecycleEstablishResponder.basePoint ≠
  ↑Tacenta.UnitLifecycleDecryptRatchetScreen.zeros32
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderFirstFrame.basePoint_ne_zero

/--
info: Tacenta.UnitLifecycleResponderFirstFrame.modelFirstFrame_dhCodec : Tacenta.UnitSatisfiabilityJoint.DhCodecShape
  Tacenta.UnitLifecycleResponderFirstFrame.Interp.modelFirstFrame
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderFirstFrame.modelFirstFrame_dhCodec

/--
info: Tacenta.UnitLifecycleResponderFirstFrame.modelFirstFrame_dhAgree : Tacenta.UnitSatisfiabilityJoint.DhAgreeShape
  Tacenta.UnitLifecycleResponderFirstFrame.Interp.modelFirstFrame
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderFirstFrame.modelFirstFrame_dhAgree

/--
info: Tacenta.UnitLifecycleResponderFirstFrame.modelFirstFrame_symmetric : Tacenta.UnitLifecycleResponderFirstFrame.DhAgreeSymmetricShape
  Tacenta.UnitLifecycleResponderFirstFrame.Interp.modelFirstFrame
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderFirstFrame.modelFirstFrame_symmetric

/--
info: Tacenta.UnitLifecycleResponderFirstFrame.first_frame_laws_model : Tacenta.UnitLifecycleDecryptScreen.DecryptJointLawsShape
    Tacenta.UnitLifecycleResponderFirstFrame.Interp.modelFirstFrame
    Tacenta.UnitLifecycleResponderFirstFrame.viewFirstFrame Tacenta.UnitLifecycleEstablishedEncrypt.toyKemR
    @Tacenta.UnitHeadroomInvariant.optionEqImpl ∧
  Nonempty
      (Tacenta.UnitSatisfiabilityJoint.InitiatorAxiom Tacenta.UnitLifecycleResponderFirstFrame.Interp.modelFirstFrame
        Tacenta.UnitLifecycleIntegrationScreen.byteRng) ∧
    Tacenta.UnitLifecycleEstablishInitiatorShape.InitiatorSuccessShape
        Tacenta.UnitLifecycleResponderFirstFrame.Interp.modelFirstFrame Tacenta.UnitLifecycleIntegrationScreen.byteRng
        Tacenta.UnitLifecycleIntegrationScreen.byteCrc ∧
      Tacenta.UnitLifecycleEstablishInitiatorShape.DhPublicValidShape
          Tacenta.UnitLifecycleResponderFirstFrame.Interp.modelFirstFrame ∧
        Tacenta.UnitLifecycleEstablishInitiatorShape.KemCiphertextLenLawShape (Aeneas.Std.Result.ok 0#usize)
            Tacenta.UnitLifecycleResponderFirstFrame.Interp.modelFirstFrame ∧
          Tacenta.UnitLifecycleEstablishedEncrypt.EncryptExtraLawsShape
              Tacenta.UnitLifecycleResponderFirstFrame.InterpO.modelFirstFrame
              Tacenta.UnitLifecycleResponderFirstFrame.dhViewFirstFrame
              Tacenta.UnitLifecycleResponderFirstFrame.kemViewFirstFrame Tacenta.UnitLifecycleEstablishedEncrypt.toyKemR
              (Aeneas.Std.Result.ok 0#usize) ∧
            (Tacenta.UnitLifecycleSessionCodec.ZeroizingVecRoundTripShape
                  Tacenta.UnitLifecycleResponderFirstFrame.Interp.modelFirstFrame ∧
                Tacenta.UnitLifecycleSessionCodec.DhPrivateBytesRoundTripShape
                    Tacenta.UnitLifecycleResponderFirstFrame.Interp.modelFirstFrame ∧
                  Tacenta.UnitLifecycleSessionCodec.DhPublicBytesRoundTripShape
                      Tacenta.UnitLifecycleResponderFirstFrame.Interp.modelFirstFrame ∧
                    Tacenta.UnitLifecycleSessionCodec.OptionBranchSomeShape
                        @Tacenta.UnitLifecycleSessionCodec.optionBranchImpl ∧
                      Tacenta.UnitLifecycleSessionCodec.VecAsSliceShape
                          @Tacenta.UnitLifecycleSessionCodec.vecAsSliceImpl ∧
                        Tacenta.UnitLifecycleRestoredSession.KemCiphertextLenBoundShape
                          (Aeneas.Std.Result.ok 0#usize)) ∧
              Tacenta.UnitLifecycleEstablishedEncrypt.KeyGenSizesOf Tacenta.UnitLifecycleEstablishedEncrypt.toyKemR ∧
                Tacenta.UnitLifecycleEstablishedEncrypt.toyKemR.keyGen
                      (Model.Lifecycle.braidRandomness
                        (List.map Tacenta.SessionUnitBraidT3.u8 Tacenta.UnitLifecycleEstablishedEncrypt.zeroSeed)) =
                    none ∧
                  Tacenta.UnitLifecycleEstablishedEncrypt.toyKemR.keyGen
                        (Model.Lifecycle.braidRandomness
                          (List.map Tacenta.SessionUnitBraidT3.u8 Tacenta.UnitLifecycleEstablishedEncrypt.oneSeed)) ≠
                      none ∧
                    Nonempty
                        (Tacenta.UnitSatisfiabilityJoint.ResponderAxiom
                          Tacenta.UnitLifecycleResponderFirstFrame.Interp.modelFirstFrame
                          Tacenta.UnitLifecycleIntegrationScreen.byteRng) ∧
                      Tacenta.UnitLifecycleEstablishResponder.ResponderSuccessShape
                          Tacenta.UnitLifecycleResponderFirstFrame.Interp.modelFirstFrame ∧
                        Tacenta.UnitLifecycleEstablishResponder.ZeroKeyShape
                            Tacenta.UnitLifecycleResponderFirstFrame.Interp.modelFirstFrame ∧
                          Tacenta.UnitLifecycleResponderFirstFrame.DhAgreeSymmetricShape
                              Tacenta.UnitLifecycleResponderFirstFrame.Interp.modelFirstFrame ∧
                            Tacenta.UnitLifecycleResponderFirstFrame.FirstFrameSuccessShape
                              Tacenta.UnitLifecycleResponderFirstFrame.Interp.modelFirstFrame
                              (fun x => Aeneas.Std.Result.ok (Aeneas.Std.alloc.vec.Vec.new Aeneas.Std.U8))
                              fun {T} x v => Aeneas.Std.Result.ok (decide (↑v = []))
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderFirstFrame.first_frame_laws_model

/--
info: Tacenta.UnitLifecycleResponderFirstFrame.publish_reachStore : ∀
  (pkb : tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes) (sb : Aeneas.Std.Array Aeneas.Std.U8 32#usize)
  (k : tacenta_session_unit.tacenta_boundary.dh.PrivateKey),
  tacenta_session_unit.tacenta_boundary.dh.PrivateKey.from_bytes sb = Aeneas.Std.Result.ok k →
    k.public_key = Aeneas.Std.Result.ok pkb →
      ∀ (sig1 sig2 : Aeneas.Std.Array Aeneas.Std.U8 64#usize)
        (z :
          tacenta_session_unit.zeroize.Zeroizing
            (Aeneas.Std.alloc.vec.Vec Tacenta.UnitLifecycleResponderFirstFrame.PoolEntry)),
        tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
              Tacenta.UnitLifecycleResponderFirstFrame.zPool z =
            Aeneas.Std.Result.ok (Aeneas.Std.alloc.vec.Vec.new Tacenta.UnitLifecycleResponderFirstFrame.PoolEntry) →
          (∀ (T A : Type),
              tacenta_session_unit.alloc.vec.Vec.is_empty A (Aeneas.Std.alloc.vec.Vec.new T) =
                Aeneas.Std.Result.ok true) →
            ∀ (kp : tacenta_session_unit.tacenta_boundary.kem.KeyPair) (kemPk : Aeneas.Std.alloc.vec.Vec Aeneas.Std.U8),
              kp.public_key = Aeneas.Std.Result.ok kemPk →
                (Tacenta.UnitLifecycleResponderFirstFrame.reachStore pkb sb sig1 sig2 z kp).publish =
                  Aeneas.Std.Result.ok (Tacenta.UnitLifecycleResponderFirstFrame.reachBundle pkb sig1 sig2 kemPk)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderFirstFrame.publish_reachStore

/--
info: Tacenta.UnitLifecycleResponderFirstFrame.reachStore_distinct : ∀
  (pkb : tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes) (sb : Aeneas.Std.Array Aeneas.Std.U8 32#usize)
  (sig1 sig2 : Aeneas.Std.Array Aeneas.Std.U8 64#usize)
  (z :
    tacenta_session_unit.zeroize.Zeroizing
      (Aeneas.Std.alloc.vec.Vec Tacenta.UnitLifecycleResponderFirstFrame.PoolEntry)),
  tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref Tacenta.UnitLifecycleResponderFirstFrame.zPool
        z =
      Aeneas.Std.Result.ok (Aeneas.Std.alloc.vec.Vec.new Tacenta.UnitLifecycleResponderFirstFrame.PoolEntry) →
    ∀ (kp : tacenta_session_unit.tacenta_boundary.kem.KeyPair),
      Tacenta.UnitLifecycleResponderFirstFrame.PrekeyIdsDistinct
        (Tacenta.UnitLifecycleResponderFirstFrame.reachStore pkb sb sig1 sig2 z kp)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderFirstFrame.reachStore_distinct

/--
info: Tacenta.UnitLifecycleResponderFirstFrame.random_secret_byte : ∀
  (crc : tacenta_session_unit.rand_core_1.CryptoRng (List Aeneas.Std.U8)) (pre rest : List Aeneas.Std.U8),
  pre.length = 32 →
    ∃ a,
      tacenta_session_unit.lifecycle.random_secret Tacenta.UnitLifecycleIntegrationScreen.byteRng crc (pre ++ rest) =
        Aeneas.Std.Result.ok (a, rest)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderFirstFrame.random_secret_byte

/--
info: Tacenta.UnitLifecycleResponderFirstFrame.reach_establishment : ∀
  (c : Tacenta.UnitLifecycleT1.EstablishInitiatorContracts Tacenta.UnitLifecycleIntegrationScreen.byteRng)
  (ourA : tacenta_session_unit.lifecycle.Identity) (pkb : tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes)
  (a : Aeneas.Std.Array Aeneas.Std.U8 32#usize),
  pkb.as_bytes = Aeneas.Std.Result.ok a →
    Tacenta.SessionUnitT1.canonicalX25519 a = true →
      tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq pkb pkb =
          Aeneas.Std.Result.ok true →
        ∀ (sig1 sig2 : Aeneas.Std.Array Aeneas.Std.U8 64#usize) (kemPk : Aeneas.Std.alloc.vec.Vec Aeneas.Std.U8),
          tacenta_session_unit.verify_bundle
                (Tacenta.UnitLifecycleResponderFirstFrame.reachBundle pkb sig1 sig2 kemPk).bundle =
              Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok ()) →
            (∀ (k : tacenta_session_unit.tacenta_boundary.dh.PrivateKey),
                ∃ x, k.agree pkb = Aeneas.Std.Result.ok (some x)) →
              ∀ (stream rest : List Aeneas.Std.U8) (ct : Aeneas.Std.alloc.vec.Vec Aeneas.Std.U8)
                (ss : Aeneas.Std.Array Aeneas.Std.U8 32#usize),
                tacenta_session_unit.tacenta_boundary.kem.encapsulate Tacenta.UnitLifecycleIntegrationScreen.byteRng
                      Tacenta.UnitLifecycleIntegrationScreen.byteCrc kemPk.deref stream =
                    Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok (ct, ss), rest) →
                  ∃ q rng1,
                    q.kemCiphertext = ct ∧
                      q.kemSecret = ss ∧
                        tacenta_session_unit.lifecycle.establish_initiator_for
                            Tacenta.UnitLifecycleIntegrationScreen.byteRng
                            Tacenta.UnitLifecycleIntegrationScreen.byteCrc ourA
                            (Tacenta.UnitLifecycleResponderFirstFrame.reachBundle pkb sig1 sig2 kemPk) pkb
                            (List.replicate 32 0#u8 ++ stream) =
                          Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok q.session, rng1)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderFirstFrame.reach_establishment

/--
info: Tacenta.UnitLifecycleResponderFirstFrame.first_send_responder_reachable : ∀ (K : Model.Braid.Kem)
  (dh : Tacenta.UnitLifecycleT3.DhView) (kem : Tacenta.UnitLifecycleT3.KemView),
  Tacenta.UnitLifecycleDecryptScreen.DecryptJointLaws K dh →
    Nonempty
        (Tacenta.UnitSatisfiabilityJoint.InitiatorAxiom Tacenta.UnitSatisfiabilityJoint.Interp.real
          Tacenta.UnitLifecycleIntegrationScreen.byteRng) →
      Tacenta.UnitLifecycleEstablishInitiatorShape.InitiatorSuccessShape Tacenta.UnitSatisfiabilityJoint.Interp.real
          Tacenta.UnitLifecycleIntegrationScreen.byteRng Tacenta.UnitLifecycleIntegrationScreen.byteCrc →
        Tacenta.UnitLifecycleEstablishInitiatorShape.DhPublicValid →
          Tacenta.UnitLifecycleEstablishInitiatorShape.KemCiphertextLenOf →
            Tacenta.UnitLifecycleEstablishedEncrypt.EncryptExtraLaws K dh kem →
              Nonempty
                  (Tacenta.UnitSatisfiabilityJoint.ResponderAxiom Tacenta.UnitSatisfiabilityJoint.Interp.real
                    Tacenta.UnitLifecycleIntegrationScreen.byteRng) →
                Tacenta.UnitLifecycleResponderFirstFrame.DhAgreeSymmetric →
                  Tacenta.UnitLifecycleSessionCodec.DhPublicBytesRoundTrip →
                    Tacenta.UnitLifecycleResponderFirstFrame.FirstFrameSuccessShape
                        Tacenta.UnitSatisfiabilityJoint.Interp.real
                        tacenta_session_unit.tacenta_boundary.kem.KeyPair.public_key
                        @tacenta_session_unit.alloc.vec.Vec.is_empty →
                      ∀ (ourA : tacenta_session_unit.lifecycle.Identity) (seed : List Aeneas.Std.U8),
                        seed.length = 64 →
                          K.keyGen (Model.Lifecycle.braidRandomness (List.map Tacenta.SessionUnitBraidT3.u8 seed)) ≠
                              none →
                            ∃ oracle bundle rng0 rng1 q bytes s' rng' ourB storeB messageKey chunk p,
                              oracle.braidKem = K ∧
                                Tacenta.UnitLifecycleEstablishedEncrypt.EstablishedEncryptHypotheses
                                    Tacenta.UnitLifecycleIntegrationScreen.byteRng
                                    Tacenta.UnitLifecycleIntegrationScreen.byteCrc
                                    Tacenta.UnitLifecycleIntegrationScreen.byteTrace dh kem
                                    Tacenta.UnitLifecycleRepair.witnessView oracle
                                    Tacenta.UnitLifecycleIntegrationScreen.byteRng
                                    Tacenta.UnitLifecycleIntegrationScreen.byteCrc ourA bundle
                                    bundle.bundle.identity_key rng0 rng1 q.session
                                    Tacenta.UnitLifecycleEstablishedEncrypt.emptyPlaintext seed ∧
                                  tacenta_session_unit.lifecycle.Session.encrypt
                                        Tacenta.UnitLifecycleIntegrationScreen.byteRng
                                        Tacenta.UnitLifecycleIntegrationScreen.byteCrc q.session
                                        Tacenta.UnitLifecycleEstablishedEncrypt.emptyPlaintext seed =
                                      Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok bytes, s', rng') ∧
                                    storeB.publish = Aeneas.Std.Result.ok bundle ∧
                                      ourB.public = Aeneas.Std.Result.ok storeB.identity_public ∧
                                        Tacenta.UnitLifecycleResponderFirstFrame.PrekeyIdsDistinct storeB ∧
                                          Tacenta.UnitLifecycleResponderFirstFrame.FirstKemAgrees storeB
                                              bundle.kem_prekey_id q.kemCiphertext q.kemSecret ∧
                                            ↑storeB.legacy_last_resort_blocked = [] ∧
                                              ↑storeB.last_resort_seen = [] ∧
                                                p.shared = q.shared ∧
                                                  p.peerIdentity = q.ourPublic ∧
                                                    p.peerEphemeral = q.ephemeralPublic ∧
                                                      Tacenta.UnitLifecycleT3.sliceOf p.message =
                                                          Tacenta.UnitLifecycleEstablishedEncrypt.firstFrame
                                                            Tacenta.UnitLifecycleRepair.witnessView oracle
                                                            (Tacenta.UnitLifecycleEstablishInitiatorShape.establishedModelOf
                                                              dh q.session)
                                                            (Tacenta.UnitLifecycleT3.sliceOf
                                                              Tacenta.UnitLifecycleEstablishedEncrypt.emptyPlaintext)
                                                            messageKey chunk ∧
                                                        p.session.invariant = Aeneas.Std.Result.ok true ∧
                                                          Tacenta.UnitLifecycleDecryptRunBounds.CounterHeadroom
                                                              p.session ∧
                                                            Tacenta.UnitLifecycleT3.SessionRefines dh K p.session
                                                              (Tacenta.UnitLifecycleEstablishResponder.responderModelOf
                                                                dh p)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderFirstFrame.first_send_responder_reachable

/--
info: structure Tacenta.UnitLifecycleResponderFirstFrame.InitiatorSecretParts {R : Type}
  (rc : tacenta_session_unit.rand_core_1.RngCore R) (crc : tacenta_session_unit.rand_core_1.CryptoRng R)
  (our : tacenta_session_unit.lifecycle.Identity) (bundle : tacenta_session_unit.lifecycle.PublishedBundle) : Type
number of parameters: 5
parents:
  Tacenta.UnitLifecycleResponderFirstFrame.InitiatorSecretParts.toInitiatorOutputParts : Tacenta.UnitLifecycleEstablishInitiatorShape.InitiatorOutputParts
    rc crc our bundle
fields:
  Tacenta.UnitLifecycleEstablishInitiatorShape.InitiatorOutputParts.ratchetPrivate : tacenta_session_unit.tacenta_boundary.dh.PrivateKey
  Tacenta.UnitLifecycleEstablishInitiatorShape.InitiatorOutputParts.ratchetPublic : tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes
  Tacenta.UnitLifecycleEstablishInitiatorShape.InitiatorOutputParts.ratchetBytes : Aeneas.Std.Array Aeneas.Std.U8
      32#usize
  Tacenta.UnitLifecycleEstablishInitiatorShape.InitiatorOutputParts.peerRatchetBytes : Aeneas.Std.Array Aeneas.Std.U8
      32#usize
  Tacenta.UnitLifecycleEstablishInitiatorShape.InitiatorOutputParts.rootKey : Aeneas.Std.Array Aeneas.Std.U8 32#usize
  Tacenta.UnitLifecycleEstablishInitiatorShape.InitiatorOutputParts.sendChain : Aeneas.Std.Array Aeneas.Std.U8 32#usize
  Tacenta.UnitLifecycleEstablishInitiatorShape.InitiatorOutputParts.sparseRoot : Aeneas.Std.Array Aeneas.Std.U8 32#usize
  Tacenta.UnitLifecycleEstablishInitiatorShape.InitiatorOutputParts.sparseSend : Aeneas.Std.Array Aeneas.Std.U8 32#usize
  Tacenta.UnitLifecycleEstablishInitiatorShape.InitiatorOutputParts.sparseReceive : Aeneas.Std.Array Aeneas.Std.U8
      32#usize
  Tacenta.UnitLifecycleEstablishInitiatorShape.InitiatorOutputParts.auth : tacenta_session_unit.tacenta_braid.Auth
  Tacenta.UnitLifecycleEstablishInitiatorShape.InitiatorOutputParts.identityAd : Aeneas.Std.alloc.vec.Vec Aeneas.Std.U8
  Tacenta.UnitLifecycleEstablishInitiatorShape.InitiatorOutputParts.ourPublic : tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes
  Tacenta.UnitLifecycleEstablishInitiatorShape.InitiatorOutputParts.ephemeral : tacenta_session_unit.tacenta_boundary.dh.PrivateKey
  Tacenta.UnitLifecycleEstablishInitiatorShape.InitiatorOutputParts.ephemeralPublic : tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes
  Tacenta.UnitLifecycleEstablishInitiatorShape.InitiatorOutputParts.kemCiphertext : Aeneas.Std.alloc.vec.Vec
      Aeneas.Std.U8
  Tacenta.UnitLifecycleEstablishInitiatorShape.InitiatorOutputParts.kemSecret : Aeneas.Std.Array Aeneas.Std.U8 32#usize
  Tacenta.UnitLifecycleEstablishInitiatorShape.InitiatorOutputParts.rngBefore : R
  Tacenta.UnitLifecycleEstablishInitiatorShape.InitiatorOutputParts.rngAfter : R
  Tacenta.UnitLifecycleEstablishInitiatorShape.InitiatorOutputParts.hRatchetPublic : self.ratchetPrivate.public_key =
      Aeneas.Std.Result.ok self.ratchetPublic
  Tacenta.UnitLifecycleEstablishInitiatorShape.InitiatorOutputParts.hRatchetBytes : self.ratchetPublic.as_bytes =
      Aeneas.Std.Result.ok self.ratchetBytes
  Tacenta.UnitLifecycleEstablishInitiatorShape.InitiatorOutputParts.hPeerRatchetBytes : bundle.bundle.signed_prekey.as_bytes =
      Aeneas.Std.Result.ok self.peerRatchetBytes
  Tacenta.UnitLifecycleEstablishInitiatorShape.InitiatorOutputParts.hPeerRatchetCanonical : tacenta_session_unit.is_canonical_key
        bundle.bundle.signed_prekey =
      Aeneas.Std.Result.ok true
  Tacenta.UnitLifecycleEstablishInitiatorShape.InitiatorOutputParts.hOurPublic : our.public =
      Aeneas.Std.Result.ok self.ourPublic
  Tacenta.UnitLifecycleEstablishInitiatorShape.InitiatorOutputParts.hIdentityAd : tacenta_session_unit.lifecycle.identity_ad
        self.ourPublic bundle.bundle.identity_key =
      Aeneas.Std.Result.ok self.identityAd
  Tacenta.UnitLifecycleEstablishInitiatorShape.InitiatorOutputParts.hPeerValid : tacenta_session_unit.is_valid_identity_key
        bundle.bundle.identity_key =
      Aeneas.Std.Result.ok true
  Tacenta.UnitLifecycleEstablishInitiatorShape.InitiatorOutputParts.hEphemeralPublic : self.ephemeral.public_key =
      Aeneas.Std.Result.ok self.ephemeralPublic
  Tacenta.UnitLifecycleEstablishInitiatorShape.InitiatorOutputParts.hEncapsulate : tacenta_session_unit.tacenta_boundary.kem.encapsulate
        rc crc bundle.bundle.kem_prekey.deref self.rngBefore =
      Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok (self.kemCiphertext, self.kemSecret), self.rngAfter)
  Tacenta.UnitLifecycleResponderFirstFrame.InitiatorSecretParts.identityKey : tacenta_session_unit.tacenta_boundary.dh.PrivateKey
  Tacenta.UnitLifecycleResponderFirstFrame.InitiatorSecretParts.kemSecretZ : tacenta_session_unit.zeroize.Zeroizing
      (Aeneas.Std.Array Aeneas.Std.U8 32#usize)
  Tacenta.UnitLifecycleResponderFirstFrame.InitiatorSecretParts.encapsulated : Aeneas.Std.Array Aeneas.Std.U8 32#usize
  Tacenta.UnitLifecycleResponderFirstFrame.InitiatorSecretParts.shared : Aeneas.Std.Array Aeneas.Std.U8 32#usize
  Tacenta.UnitLifecycleResponderFirstFrame.InitiatorSecretParts.sharedZ : tacenta_session_unit.zeroize.Zeroizing
      (Aeneas.Std.Array Aeneas.Std.U8 32#usize)
  Tacenta.UnitLifecycleResponderFirstFrame.InitiatorSecretParts.sharedBytes : Aeneas.Std.Array Aeneas.Std.U8 32#usize
  Tacenta.UnitLifecycleResponderFirstFrame.InitiatorSecretParts.sharedSlice : Aeneas.Std.Slice Aeneas.Std.U8
  Tacenta.UnitLifecycleResponderFirstFrame.InitiatorSecretParts.dhOut : Aeneas.Std.Array Aeneas.Std.U8 32#usize
  Tacenta.UnitLifecycleResponderFirstFrame.InitiatorSecretParts.dhOutZ : tacenta_session_unit.zeroize.Zeroizing
      (Aeneas.Std.Array Aeneas.Std.U8 32#usize)
  Tacenta.UnitLifecycleResponderFirstFrame.InitiatorSecretParts.dhOutBytes : Aeneas.Std.Array Aeneas.Std.U8 32#usize
  Tacenta.UnitLifecycleResponderFirstFrame.InitiatorSecretParts.braidSlice : Aeneas.Std.Slice Aeneas.Std.U8
  Tacenta.UnitLifecycleResponderFirstFrame.InitiatorSecretParts.hDhKey : our.dh_key =
      Aeneas.Std.Result.ok self.identityKey
  Tacenta.UnitLifecycleResponderFirstFrame.InitiatorSecretParts.hKemSecretZ : tacenta_session_unit.zeroize.Zeroizing.new
        Tacenta.UnitLifecycleEstablishResponder.z32 self.kemSecret =
      Aeneas.Std.Result.ok self.kemSecretZ
  Tacenta.UnitLifecycleResponderFirstFrame.InitiatorSecretParts.hEncapsulated : tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
        Tacenta.UnitLifecycleEstablishResponder.z32 self.kemSecretZ =
      Aeneas.Std.Result.ok self.encapsulated
  Tacenta.UnitLifecycleResponderFirstFrame.InitiatorSecretParts.hShared : tacenta_session_unit.initiator_shared_secret
        self.identityKey self.ephemeral bundle.bundle self.encapsulated =
      Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok self.shared)
  Tacenta.UnitLifecycleResponderFirstFrame.InitiatorSecretParts.hSharedZ : tacenta_session_unit.zeroize.Zeroizing.new
        Tacenta.UnitLifecycleEstablishResponder.z32 self.shared =
      Aeneas.Std.Result.ok self.sharedZ
  Tacenta.UnitLifecycleResponderFirstFrame.InitiatorSecretParts.hSharedBytes : tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
        Tacenta.UnitLifecycleEstablishResponder.z32 self.sharedZ =
      Aeneas.Std.Result.ok self.sharedBytes
  Tacenta.UnitLifecycleResponderFirstFrame.InitiatorSecretParts.hTriple : tacenta_session_unit.tacenta_triple.State.init_sender
        self.sharedSlice self.ratchetBytes self.peerRatchetBytes self.dhOutBytes
        tacenta_session_unit.tacenta_ratchet.LabelSet.Tacenta =
      Aeneas.Std.Result.ok
        (Tacenta.UnitLifecycleEstablishInitiatorShape.initiatorTriple self.ratchetBytes self.peerRatchetBytes
          self.rootKey self.sendChain self.sparseRoot self.sparseSend self.sparseReceive)
  Tacenta.UnitLifecycleResponderFirstFrame.InitiatorSecretParts.hSharedSlice : Tacenta.UnitLifecycleEstablishResponder.fullSlice
        self.sharedBytes =
      Aeneas.Std.Result.ok self.sharedSlice
  Tacenta.UnitLifecycleResponderFirstFrame.InitiatorSecretParts.hDhOutBytes : tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
        Tacenta.UnitLifecycleEstablishResponder.z32 self.dhOutZ =
      Aeneas.Std.Result.ok self.dhOutBytes
  Tacenta.UnitLifecycleResponderFirstFrame.InitiatorSecretParts.hDhOutZ : tacenta_session_unit.zeroize.Zeroizing.new
        Tacenta.UnitLifecycleEstablishResponder.z32 self.dhOut =
      Aeneas.Std.Result.ok self.dhOutZ
  Tacenta.UnitLifecycleResponderFirstFrame.InitiatorSecretParts.hDhOut : self.ratchetPrivate.agree
        bundle.bundle.signed_prekey =
      Aeneas.Std.Result.ok (some self.dhOut)
  Tacenta.UnitLifecycleResponderFirstFrame.InitiatorSecretParts.hBraid : tacenta_session_unit.tacenta_braid.Braid.initiator
        self.braidSlice =
      Aeneas.Std.Result.ok { state := tacenta_session_unit.tacenta_braid.State.KeysUnsampled 1#u64 self.auth }
  Tacenta.UnitLifecycleResponderFirstFrame.InitiatorSecretParts.hBraidSlice : Tacenta.UnitLifecycleEstablishResponder.fullSlice
        self.sharedBytes =
      Aeneas.Std.Result.ok self.braidSlice
  Tacenta.UnitLifecycleResponderFirstFrame.InitiatorSecretParts.hVerify : tacenta_session_unit.verify_bundle
        bundle.bundle =
      Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok ())
constructor:
  Tacenta.UnitLifecycleResponderFirstFrame.InitiatorSecretParts.mk {R : Type}
    {rc : tacenta_session_unit.rand_core_1.RngCore R} {crc : tacenta_session_unit.rand_core_1.CryptoRng R}
    {our : tacenta_session_unit.lifecycle.Identity} {bundle : tacenta_session_unit.lifecycle.PublishedBundle}
    (toInitiatorOutputParts : Tacenta.UnitLifecycleEstablishInitiatorShape.InitiatorOutputParts rc crc our bundle)
    (identityKey : tacenta_session_unit.tacenta_boundary.dh.PrivateKey)
    (kemSecretZ : tacenta_session_unit.zeroize.Zeroizing (Aeneas.Std.Array Aeneas.Std.U8 32#usize))
    (encapsulated shared : Aeneas.Std.Array Aeneas.Std.U8 32#usize)
    (sharedZ : tacenta_session_unit.zeroize.Zeroizing (Aeneas.Std.Array Aeneas.Std.U8 32#usize))
    (sharedBytes : Aeneas.Std.Array Aeneas.Std.U8 32#usize) (sharedSlice : Aeneas.Std.Slice Aeneas.Std.U8)
    (dhOut : Aeneas.Std.Array Aeneas.Std.U8 32#usize)
    (dhOutZ : tacenta_session_unit.zeroize.Zeroizing (Aeneas.Std.Array Aeneas.Std.U8 32#usize))
    (dhOutBytes : Aeneas.Std.Array Aeneas.Std.U8 32#usize) (braidSlice : Aeneas.Std.Slice Aeneas.Std.U8)
    (hDhKey : our.dh_key = Aeneas.Std.Result.ok identityKey)
    (hKemSecretZ :
      tacenta_session_unit.zeroize.Zeroizing.new Tacenta.UnitLifecycleEstablishResponder.z32
          toInitiatorOutputParts.kemSecret =
        Aeneas.Std.Result.ok kemSecretZ)
    (hEncapsulated :
      tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref Tacenta.UnitLifecycleEstablishResponder.z32
          kemSecretZ =
        Aeneas.Std.Result.ok encapsulated)
    (hShared :
      tacenta_session_unit.initiator_shared_secret identityKey toInitiatorOutputParts.ephemeral bundle.bundle
          encapsulated =
        Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok shared))
    (hSharedZ :
      tacenta_session_unit.zeroize.Zeroizing.new Tacenta.UnitLifecycleEstablishResponder.z32 shared =
        Aeneas.Std.Result.ok sharedZ)
    (hSharedBytes :
      tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref Tacenta.UnitLifecycleEstablishResponder.z32
          sharedZ =
        Aeneas.Std.Result.ok sharedBytes)
    (hTriple :
      tacenta_session_unit.tacenta_triple.State.init_sender sharedSlice toInitiatorOutputParts.ratchetBytes
          toInitiatorOutputParts.peerRatchetBytes dhOutBytes tacenta_session_unit.tacenta_ratchet.LabelSet.Tacenta =
        Aeneas.Std.Result.ok
          (Tacenta.UnitLifecycleEstablishInitiatorShape.initiatorTriple toInitiatorOutputParts.ratchetBytes
            toInitiatorOutputParts.peerRatchetBytes toInitiatorOutputParts.rootKey toInitiatorOutputParts.sendChain
            toInitiatorOutputParts.sparseRoot toInitiatorOutputParts.sparseSend toInitiatorOutputParts.sparseReceive))
    (hSharedSlice : Tacenta.UnitLifecycleEstablishResponder.fullSlice sharedBytes = Aeneas.Std.Result.ok sharedSlice)
    (hDhOutBytes :
      tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref Tacenta.UnitLifecycleEstablishResponder.z32
          dhOutZ =
        Aeneas.Std.Result.ok dhOutBytes)
    (hDhOutZ :
      tacenta_session_unit.zeroize.Zeroizing.new Tacenta.UnitLifecycleEstablishResponder.z32 dhOut =
        Aeneas.Std.Result.ok dhOutZ)
    (hDhOut :
      toInitiatorOutputParts.ratchetPrivate.agree bundle.bundle.signed_prekey = Aeneas.Std.Result.ok (some dhOut))
    (hBraid :
      tacenta_session_unit.tacenta_braid.Braid.initiator braidSlice =
        Aeneas.Std.Result.ok
          { state := tacenta_session_unit.tacenta_braid.State.KeysUnsampled 1#u64 toInitiatorOutputParts.auth })
    (hBraidSlice : Tacenta.UnitLifecycleEstablishResponder.fullSlice sharedBytes = Aeneas.Std.Result.ok braidSlice)
    (hVerify :
      tacenta_session_unit.verify_bundle bundle.bundle = Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok ())) :
    Tacenta.UnitLifecycleResponderFirstFrame.InitiatorSecretParts rc crc our bundle
field notation resolution order:
  Tacenta.UnitLifecycleResponderFirstFrame.InitiatorSecretParts, Tacenta.UnitLifecycleEstablishInitiatorShape.InitiatorOutputParts
-/
#guard_msgs in
#print Tacenta.UnitLifecycleResponderFirstFrame.InitiatorSecretParts

/--
info: def Tacenta.UnitLifecycleResponderFirstFrame.DhAgreeSymmetricShape : Tacenta.UnitSatisfiabilityJoint.Interp → Prop :=
fun I =>
  ∀ (a b : I.PrivateKey) (pa pb : I.PublicKeyBytes),
    I.dhPrivPublicKey a = Aeneas.Std.Result.ok pa →
      I.dhPrivPublicKey b = Aeneas.Std.Result.ok pb → I.dhPrivAgree a pb = I.dhPrivAgree b pa
-/
#guard_msgs in
#print Tacenta.UnitLifecycleResponderFirstFrame.DhAgreeSymmetricShape

/--
info: def Tacenta.UnitLifecycleResponderFirstFrame.DhAgreeSymmetric : Prop :=
Tacenta.UnitLifecycleResponderFirstFrame.DhAgreeSymmetricShape Tacenta.UnitSatisfiabilityJoint.Interp.real
-/
#guard_msgs in
#print Tacenta.UnitLifecycleResponderFirstFrame.DhAgreeSymmetric

/--
info: def Tacenta.UnitLifecycleResponderFirstFrame.OneTimeMatches : Option
    tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes →
  Option tacenta_session_unit.tacenta_boundary.dh.PrivateKey → Prop :=
fun bundleKey held =>
  bundleKey = none ∧ held = none ∨ ∃ k pk, held = some k ∧ k.public_key = Aeneas.Std.Result.ok pk ∧ bundleKey = some pk
-/
#guard_msgs in
#print Tacenta.UnitLifecycleResponderFirstFrame.OneTimeMatches

/--
info: @[reducible] def Tacenta.UnitLifecycleResponderFirstFrame.zPool : tacenta_session_unit.zeroize.Zeroize
  (Aeneas.Std.alloc.vec.Vec (Aeneas.Std.U32 × Aeneas.Std.Array Aeneas.Std.U8 32#usize)) :=
tacenta_session_unit.alloc.vec.Vec.Insts.ZeroizeZeroize
  (tacenta_session_unit.Pair.Insts.ZeroizeZeroize
    (tacenta_session_unit.zeroize.Zeroize.Blanket tacenta_session_unit.U32.Insts.ZeroizeDefaultIsZeroes)
    (tacenta_session_unit.Array.Insts.ZeroizeZeroize 32#usize
      (tacenta_session_unit.zeroize.Zeroize.Blanket tacenta_session_unit.U8.Insts.ZeroizeDefaultIsZeroes)))
-/
#guard_msgs in
#print Tacenta.UnitLifecycleResponderFirstFrame.zPool

/--
info: @[reducible] def Tacenta.UnitLifecycleResponderFirstFrame.PoolEntry : Type :=
Aeneas.Std.U32 × Aeneas.Std.Array Aeneas.Std.U8 32#usize
-/
#guard_msgs in
#print Tacenta.UnitLifecycleResponderFirstFrame.PoolEntry

/--
info: @[reducible] def Tacenta.UnitLifecycleResponderFirstFrame.KemEntry : Type :=
Aeneas.Std.U32 × tacenta_session_unit.tacenta_boundary.kem.KeyPair × Aeneas.Std.Array Aeneas.Std.U8 64#usize
-/
#guard_msgs in
#print Tacenta.UnitLifecycleResponderFirstFrame.KemEntry

/--
info: def Tacenta.UnitLifecycleResponderFirstFrame.storeIds : tacenta_session_unit.lifecycle.PrekeyStore →
  List Tacenta.UnitLifecycleResponderFirstFrame.PoolEntry → List Aeneas.Std.U32 :=
fun store pool =>
  store.signed_prekey_id ::
    store.kem_id ::
      ((Option.map (fun x => x.2.1) store.previous_signed_prekey).toList ++
            (Option.map (fun x => x.2.1) store.previous_kem).toList ++
          List.map (fun x => x.1) pool ++
        List.map (fun x => x.1) ↑store.kem_one_time)
-/
#guard_msgs in
#print Tacenta.UnitLifecycleResponderFirstFrame.storeIds

/--
info: def Tacenta.UnitLifecycleResponderFirstFrame.PrekeyIdsDistinct : tacenta_session_unit.lifecycle.PrekeyStore → Prop :=
fun store =>
  ∃ v,
    tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref Tacenta.UnitLifecycleResponderFirstFrame.zPool
          store.one_time =
        Aeneas.Std.Result.ok v ∧
      (Tacenta.UnitLifecycleResponderFirstFrame.storeIds store ↑v).Nodup ∧
        tacenta_session_unit.serialization.ABSENT_ID ∉ Tacenta.UnitLifecycleResponderFirstFrame.storeIds store ↑v
-/
#guard_msgs in
#print Tacenta.UnitLifecycleResponderFirstFrame.PrekeyIdsDistinct

/--
info: def Tacenta.UnitLifecycleResponderFirstFrame.heldKemPair : tacenta_session_unit.lifecycle.PrekeyStore →
  Aeneas.Std.U32 → Option tacenta_session_unit.tacenta_boundary.kem.KeyPair :=
fun store id =>
  if id = store.kem_id then some store.kem
  else Option.map (fun x => x.2.1) (List.find? (fun x => decide (x.1 = id)) ↑store.kem_one_time)
-/
#guard_msgs in
#print Tacenta.UnitLifecycleResponderFirstFrame.heldKemPair

/--
info: def Tacenta.UnitLifecycleResponderFirstFrame.FirstKemAgrees : tacenta_session_unit.lifecycle.PrekeyStore →
  Aeneas.Std.U32 → Aeneas.Std.alloc.vec.Vec Aeneas.Std.U8 → Aeneas.Std.Array Aeneas.Std.U8 32#usize → Prop :=
fun store id ct ss =>
  ∃ pair,
    Tacenta.UnitLifecycleResponderFirstFrame.heldKemPair store id = some pair ∧
      tacenta_session_unit.tacenta_boundary.kem.decapsulate pair ct.deref =
        Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok ss)
-/
#guard_msgs in
#print Tacenta.UnitLifecycleResponderFirstFrame.FirstKemAgrees

/--
info: def Tacenta.UnitLifecycleResponderFirstFrame.StoreRefusal : tacenta_session_unit.lifecycle.PrekeyStore →
  Aeneas.Std.Array Aeneas.Std.U8 32#usize → tacenta_session_unit.lifecycle.Error → Prop :=
fun store secret e =>
  e = tacenta_session_unit.lifecycle.Error.LegacyLastResortRecord ∧ store.kem_id ∈ ↑store.legacy_last_resort_blocked ∨
    (e = tacenta_session_unit.lifecycle.Error.ReplayedLastResort ∧
        ∃ fp,
          tacenta_session_unit.lifecycle.last_resort_fingerprint secret = Aeneas.Std.Result.ok fp ∧
            ∃ x ∈ ↑store.last_resort_seen, x.2 = fp) ∨
      e = tacenta_session_unit.lifecycle.Error.LastResortRecordFull ∧
        (∃ fp,
            tacenta_session_unit.lifecycle.last_resort_fingerprint secret = Aeneas.Std.Result.ok fp ∧
              ¬∃ x ∈ ↑store.last_resort_seen, x.2 = fp) ∧
          ↑store.last_resort_seen ≠ [] ∧
            ∃ n,
              store.last_resort_seen_for store.kem_id = Aeneas.Std.Result.ok n ∧
                tacenta_session_unit.lifecycle.MAX_LAST_RESORT_SEEN ≤ n
-/
#guard_msgs in
#print Tacenta.UnitLifecycleResponderFirstFrame.StoreRefusal

/--
info: structure Tacenta.UnitLifecycleResponderFirstFrame.FirstFrameSuccessShape (I : Tacenta.UnitSatisfiabilityJoint.Interp)
  (kemPublic : I.KemKeyPair → Aeneas.Std.Result (Aeneas.Std.alloc.vec.Vec Aeneas.Std.U8))
  (isEmpty : {T : Type} → Type → Aeneas.Std.alloc.vec.Vec T → Aeneas.Std.Result Bool) : Prop
number of parameters: 3
fields:
  Tacenta.UnitLifecycleResponderFirstFrame.FirstFrameSuccessShape.key : ∃ sb k pkb a,
      I.dhPrivFromBytes sb = Aeneas.Std.Result.ok k ∧
        I.dhPrivPublicKey k = Aeneas.Std.Result.ok pkb ∧
          I.dhPubAsBytes pkb = Aeneas.Std.Result.ok a ∧
            Tacenta.SessionUnitT1.canonicalX25519 a = true ∧
              I.dhIsPrimeOrderPublic pkb = Aeneas.Std.Result.ok true ∧
                I.dhPubEq pkb pkb = Aeneas.Std.Result.ok true ∧
                  (∀ (m : Aeneas.Std.Slice Aeneas.Std.U8),
                      ∃ sig, I.xeddsaVerify pkb m sig = Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok ())) ∧
                    ∀ (k' : I.PrivateKey), ∃ x, I.dhPrivAgree k' pkb = Aeneas.Std.Result.ok (some x)
  Tacenta.UnitLifecycleResponderFirstFrame.FirstFrameSuccessShape.kem : ∃ kp kemPk stream ct ss rest,
      kemPublic kp = Aeneas.Std.Result.ok kemPk ∧
        (↑kemPk).length + 1 ≤ Aeneas.Std.Usize.max ∧
          I.kemEncapsulate Tacenta.UnitLifecycleIntegrationScreen.byteRng Tacenta.UnitLifecycleIntegrationScreen.byteCrc
                kemPk.deref stream =
              Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok (ct, ss), rest) ∧
            I.kemDecapsulate kp ct.deref = Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok ss)
  Tacenta.UnitLifecycleResponderFirstFrame.FirstFrameSuccessShape.pool : ∃ z,
      I.zDeref Tacenta.UnitLifecycleResponderFirstFrame.zPool z =
        Aeneas.Std.Result.ok (Aeneas.Std.alloc.vec.Vec.new Tacenta.UnitLifecycleResponderFirstFrame.PoolEntry)
  Tacenta.UnitLifecycleResponderFirstFrame.FirstFrameSuccessShape.empty : ∀ (T A : Type),
      isEmpty A (Aeneas.Std.alloc.vec.Vec.new T) = Aeneas.Std.Result.ok true
constructor:
  Tacenta.UnitLifecycleResponderFirstFrame.FirstFrameSuccessShape.mk {I : Tacenta.UnitSatisfiabilityJoint.Interp}
    {kemPublic : I.KemKeyPair → Aeneas.Std.Result (Aeneas.Std.alloc.vec.Vec Aeneas.Std.U8)}
    {isEmpty : {T : Type} → Type → Aeneas.Std.alloc.vec.Vec T → Aeneas.Std.Result Bool}
    (key :
      ∃ sb k pkb a,
        I.dhPrivFromBytes sb = Aeneas.Std.Result.ok k ∧
          I.dhPrivPublicKey k = Aeneas.Std.Result.ok pkb ∧
            I.dhPubAsBytes pkb = Aeneas.Std.Result.ok a ∧
              Tacenta.SessionUnitT1.canonicalX25519 a = true ∧
                I.dhIsPrimeOrderPublic pkb = Aeneas.Std.Result.ok true ∧
                  I.dhPubEq pkb pkb = Aeneas.Std.Result.ok true ∧
                    (∀ (m : Aeneas.Std.Slice Aeneas.Std.U8),
                        ∃ sig, I.xeddsaVerify pkb m sig = Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok ())) ∧
                      ∀ (k' : I.PrivateKey), ∃ x, I.dhPrivAgree k' pkb = Aeneas.Std.Result.ok (some x))
    (kem :
      ∃ kp kemPk stream ct ss rest,
        kemPublic kp = Aeneas.Std.Result.ok kemPk ∧
          (↑kemPk).length + 1 ≤ Aeneas.Std.Usize.max ∧
            I.kemEncapsulate Tacenta.UnitLifecycleIntegrationScreen.byteRng
                  Tacenta.UnitLifecycleIntegrationScreen.byteCrc kemPk.deref stream =
                Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok (ct, ss), rest) ∧
              I.kemDecapsulate kp ct.deref = Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok ss))
    (pool :
      ∃ z,
        I.zDeref Tacenta.UnitLifecycleResponderFirstFrame.zPool z =
          Aeneas.Std.Result.ok (Aeneas.Std.alloc.vec.Vec.new Tacenta.UnitLifecycleResponderFirstFrame.PoolEntry))
    (empty : ∀ (T A : Type), isEmpty A (Aeneas.Std.alloc.vec.Vec.new T) = Aeneas.Std.Result.ok true) :
    Tacenta.UnitLifecycleResponderFirstFrame.FirstFrameSuccessShape I kemPublic isEmpty
-/
#guard_msgs in
#print Tacenta.UnitLifecycleResponderFirstFrame.FirstFrameSuccessShape

/--
info: def Tacenta.UnitLifecycleResponderFirstFrame.Interp.modelFirstFrame : Tacenta.UnitSatisfiabilityJoint.Interp :=
let __src := Tacenta.UnitLifecycleEstablishedEncrypt.Interp.modelEncrypt;
{ PrivateKey := __src.PrivateKey, PublicKeyBytes := __src.PublicKeyBytes, KemKeyPair := __src.KemKeyPair,
  IncrementalKeyPair := __src.IncrementalKeyPair, EncapsState := __src.EncapsState, Zeroizing := __src.Zeroizing,
  dhPrivFromBytes := __src.dhPrivFromBytes,
  dhPrivPublicKey := fun x => Aeneas.Std.Result.ok Tacenta.UnitLifecycleEstablishResponder.basePoint,
  dhPrivAgree := fun x p =>
    Aeneas.Std.Result.ok (if ↑p = ↑Tacenta.UnitLifecycleDecryptRatchetScreen.zeros32 then none else some p),
  dhPrivToBytes := __src.dhPrivToBytes, dhPubFromBytes := __src.dhPubFromBytes, dhPubAsBytes := __src.dhPubAsBytes,
  dhPubEq := __src.dhPubEq, dhIsPrimeOrderPublic := __src.dhIsPrimeOrderPublic, aeadEncrypt := __src.aeadEncrypt,
  aeadDecrypt := __src.aeadDecrypt, kemEncapsulate := @Tacenta.UnitSatisfiabilityJoint.Interp.kemEncapsulate __src,
  kemDecapsulate := __src.kemDecapsulate, xeddsaVerify := __src.xeddsaVerify, hkdfSha256 := __src.hkdfSha256,
  hmacSha256 := __src.hmacSha256, HEADER_LEN := __src.HEADER_LEN, EK_VECTOR_LEN := __src.EK_VECTOR_LEN,
  CT1_LEN := __src.CT1_LEN, CT2_LEN := __src.CT2_LEN, ikpClone := __src.ikpClone,
  ikpGenerate := @Tacenta.UnitSatisfiabilityJoint.Interp.ikpGenerate __src, ikpHeader := __src.ikpHeader,
  ikpEkVector := __src.ikpEkVector, ikpDecapsulate := __src.ikpDecapsulate, esClone := __src.esClone,
  encapsulate1 := @Tacenta.UnitSatisfiabilityJoint.Interp.encapsulate1 __src, encapsulate2 := __src.encapsulate2,
  validateEk := __src.validateEk, blanketZeroize := @Tacenta.UnitSatisfiabilityJoint.Interp.blanketZeroize __src,
  arrayZeroize := @Tacenta.UnitSatisfiabilityJoint.Interp.arrayZeroize __src,
  tupleZeroize := @Tacenta.UnitSatisfiabilityJoint.Interp.tupleZeroize __src,
  pairZeroize := @Tacenta.UnitSatisfiabilityJoint.Interp.pairZeroize __src,
  vecZeroize := @Tacenta.UnitSatisfiabilityJoint.Interp.vecZeroize __src,
  zNew := @Tacenta.UnitSatisfiabilityJoint.Interp.zNew __src,
  zDeref := @Tacenta.UnitSatisfiabilityJoint.Interp.zDeref __src,
  zDerefMut := @Tacenta.UnitSatisfiabilityJoint.Interp.zDerefMut __src,
  vecPop := @Tacenta.UnitSatisfiabilityJoint.Interp.vecPop __src,
  vecCapacity := @Tacenta.UnitSatisfiabilityJoint.Interp.vecCapacity __src,
  vecTruncate := @Tacenta.UnitSatisfiabilityJoint.Interp.vecTruncate __src,
  optionClone := @Tacenta.UnitSatisfiabilityJoint.Interp.optionClone __src,
  optionAsMut := @Tacenta.UnitSatisfiabilityJoint.Interp.optionAsMut __src,
  rangeFullIndex := @Tacenta.UnitSatisfiabilityJoint.Interp.rangeFullIndex __src, divCeil := __src.divCeil }
-/
#guard_msgs in
#print Tacenta.UnitLifecycleResponderFirstFrame.Interp.modelFirstFrame

/--
info: def Tacenta.UnitLifecycleResponderFirstFrame.InterpO.modelFirstFrame : Tacenta.UnitOracleShape.InterpO :=
have __src := Tacenta.UnitLifecycleResponderFirstFrame.Interp.modelFirstFrame;
{ toInterp := __src, xeddsaSign := fun {R} => Tacenta.UnitOracleModel.signModelO }
-/
#guard_msgs in
#print Tacenta.UnitLifecycleResponderFirstFrame.InterpO.modelFirstFrame

/--
info: def Tacenta.UnitLifecycleResponderFirstFrame.viewFirstFrame : Tacenta.UnitLifecycleDecryptRatchetScreen.DhViewShape
  Tacenta.UnitLifecycleResponderFirstFrame.Interp.modelFirstFrame :=
{ privateKey := Tacenta.UnitLifecycleT3.arrayOf, publicKey := Tacenta.UnitLifecycleT3.arrayOf }
-/
#guard_msgs in
#print Tacenta.UnitLifecycleResponderFirstFrame.viewFirstFrame

/--
info: def Tacenta.UnitLifecycleResponderFirstFrame.dhViewFirstFrame : Tacenta.UnitOracleShape.DhViewOf
  Tacenta.UnitLifecycleResponderFirstFrame.InterpO.modelFirstFrame.toInterp :=
{ privateKey := Tacenta.UnitLifecycleResponderFirstFrame.viewFirstFrame.privateKey,
  publicKey := Tacenta.UnitLifecycleResponderFirstFrame.viewFirstFrame.publicKey }
-/
#guard_msgs in
#print Tacenta.UnitLifecycleResponderFirstFrame.dhViewFirstFrame

/--
info: def Tacenta.UnitLifecycleResponderFirstFrame.kemViewFirstFrame : Tacenta.UnitOracleShape.KemViewOf
  Tacenta.UnitLifecycleResponderFirstFrame.InterpO.modelFirstFrame.toInterp :=
{ keyPair := fun x => [] }
-/
#guard_msgs in
#print Tacenta.UnitLifecycleResponderFirstFrame.kemViewFirstFrame

/--
info: def Tacenta.UnitLifecycleResponderFirstFrame.reachStore : tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes →
  Aeneas.Std.Array Aeneas.Std.U8 32#usize →
    Aeneas.Std.Array Aeneas.Std.U8 64#usize →
      Aeneas.Std.Array Aeneas.Std.U8 64#usize →
        tacenta_session_unit.zeroize.Zeroizing
            (Aeneas.Std.alloc.vec.Vec Tacenta.UnitLifecycleResponderFirstFrame.PoolEntry) →
          tacenta_session_unit.tacenta_boundary.kem.KeyPair → tacenta_session_unit.lifecycle.PrekeyStore :=
fun pkb sb sig1 sig2 z kp =>
  { identity_public := pkb, signed_prekey_secret := sb, signed_prekey_id := 1#u32, signed_prekey_sig := sig1,
    one_time := z, kem := kp, kem_id := 2#u32, kem_sig := sig2,
    kem_one_time :=
      Aeneas.Std.alloc.vec.Vec.new
        (Aeneas.Std.U32 × tacenta_session_unit.tacenta_boundary.kem.KeyPair × Aeneas.Std.Array Aeneas.Std.U8 64#usize),
    previous_signed_prekey := none, previous_kem := none, next_id := 3#u32,
    last_resort_seen := Aeneas.Std.alloc.vec.Vec.new (Aeneas.Std.U32 × Aeneas.Std.Array Aeneas.Std.U8 32#usize),
    legacy_last_resort_blocked := Aeneas.Std.alloc.vec.Vec.new Aeneas.Std.U32 }
-/
#guard_msgs in
#print Tacenta.UnitLifecycleResponderFirstFrame.reachStore

/--
info: def Tacenta.UnitLifecycleResponderFirstFrame.reachBundle : tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes →
  Aeneas.Std.Array Aeneas.Std.U8 64#usize →
    Aeneas.Std.Array Aeneas.Std.U8 64#usize →
      Aeneas.Std.alloc.vec.Vec Aeneas.Std.U8 → tacenta_session_unit.lifecycle.PublishedBundle :=
fun pkb sig1 sig2 kemPk =>
  {
    bundle :=
      { identity_key := pkb, signed_prekey := pkb, signed_prekey_signature := sig1, kem_prekey := kemPk,
        kem_prekey_signature := sig2, one_time_prekey := none },
    signed_prekey_id := 1#u32, one_time_prekey_id := tacenta_session_unit.serialization.ABSENT_ID,
    kem_prekey_id := 2#u32 }
-/
#guard_msgs in
#print Tacenta.UnitLifecycleResponderFirstFrame.reachBundle
