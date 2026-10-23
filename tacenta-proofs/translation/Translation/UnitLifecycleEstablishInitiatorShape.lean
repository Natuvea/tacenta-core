import Translation.UnitLifecycleDecryptRunBounds

/-!
# What a successful `establish_initiator_for` returns: the invariant, the ceilings and the relation

The `decrypt_ratchet` refinement (`UnitLifecycleDecryptRunBounds.decrypt_ratchet_refines_of_invariant`) takes
`Session::invariant`, `SessionRefines` and `CounterHeadroom` of the session it runs on.  Until this module
every session those hypotheses were shown at was built for them (`UnitHeadroomInvariant.sessionOf`,
`UnitLifecycleDecryptScreen.invReal`).  This module derives them from an actual establishment result: for
every identity, published bundle, expected identity and source of randomness, every session `s` with
`establish_initiator_for rc crc our bundle expected rng0 = ok (.Ok s, rng1)`.  No concrete input is chosen.

## What is shown

* `establish_initiator_for_parts` (no hypothesis): such an `s` is `InitiatorOutputParts.session` of parts
  read off the generated function, with the facts the code checked or computed on the way
  (`InitiatorOutputParts`): the ratchet key's public bytes, the bundle's signed prekey bytes and its
  canonical check, our identity public key, the associated data, `verify_bundle`'s acceptance of the
  peer's identity key (`is_valid_identity_key`, by inversion of `verify_bundle`), the ephemeral public key
  and the encapsulation that produced the pending ciphertext.  The Triple is the one `init_sender` builds
  (`initiatorTriple`), the Braid is `KeysUnsampled` at epoch 1.
* `establish_initiator_for_admissible`: `Session::invariant s = ok true`, under two laws assumed here
  (`DhPublicValid`, `KemCiphertextLenOf`) and the recorded assumption `OptionEqU64Shape`.
* `counterHeadroom_of_established` (no hypothesis): all four fields of `CounterHeadroom` hold: the
  classical clock and both sparse chain counters are 0, the sparse epoch is 0, the Braid epoch is 1.
* `sessionRefines_established` (no hypothesis): `SessionRefines dh K s (establishedModelOf dh s)` for every
  DH view `dh` and KEM `K`; `sessionRefines_established_unique`: every model session `s` refines equals
  `establishedModelOf dh s`.  Both hold by definition for every session whose Braid is `KeysUnsampled`
  (each field of `SessionRefines` is an equation through the abstraction functions); what the
  establishment supplies to them is that Braid state.  The establishment-specific content of this module is
  the invariant and the ceilings.
* `establish_initiator_for_succeeds`, `established_initiator_inhabited`: under the axiom part of
  `EstablishInitiatorContracts` and `InitiatorSuccessShape` (a self-equal valid key on which a signature
  verifies and every agreement is contributory, and a KEM key on which encapsulation succeeds), a
  successful output exists, and the invariant, the ceilings and the relation hold at it.  The witness
  bundle uses one key as identity key and signed prekey and has no one-time prekey; the success branch
  with a one-time prekey is covered by the theorems above and not shown inhabited.
  `establishment_hypotheses_satisfiable`: those hypotheses and the three laws hold together in the joint
  model of `UnitSatisfiabilityJoint` (with `ok 0` for `kem::ciphertext_len`).

## Each clause of `Session::invariant` at the output

* **By construction** (the value the code stores, or a recomputation of the same opaque function on the
  same arguments): the ratchet private key's public bytes equal the Triple's sending key; the Braid has
  not failed; `is_initiator = some true` (epoch 1 is odd) differs from `is_responder = false` (no
  established ephemeral); the associated data is `identity_ad` of our and the peer's keys in initiator
  order; the sparse direction `A2b` agrees with the role and with `started_as_sender = some true` (a
  sending chain and no receiving chain); a pending initial message without an established ephemeral;
  the classical ratchet's invariant apart from its own key (empty store, clock 0, no receiving chain;
  the peer key canonical by the establishment's own `is_canonical_key` check of the signed prekey); the
  sparse invariant (one chain-table entry at epoch 0, empty store); the Braid invariant (epoch 1 ≥ 1).
  The epoch clause compares `checked_add 0 1` with `some 1` through `Option::eq`, and uses
  `OptionEqU64Shape` (assumed, recorded in `UnitHeadroomInvariant`).
  Two clauses hold vacuously because `established_ephemeral = none`: the `decode_ec` check of an established
  ephemeral in clause (f), and the responder branch of the orientation clause (c).
* **By inverting `verify_bundle`**: the peer identity key passes `is_valid_identity_key`.
* **By a law** (assumed): our identity public key passes `is_valid_identity_key`, the ratchet public key's
  bytes are canonical, and the pending ephemeral key is canonical (`DhPublicValid`); the pending
  ciphertext's length equals `kem::ciphertext_len` (`KemCiphertextLenOf`).

## The two laws

Both are assumed at the real constants and stated as shapes over an interpretation, with a model:
* `DhPublicValid` (`DhPublicValidShape Interp.real`): every public key `PrivateKey::public_key` returns has
  canonical bytes and is of prime order.  True of the boundary by reading (x25519-dalek multiplies a
  clamped scalar by the base point; `tacenta-core/boundary/src/dh.rs`); not checked in Lean.  Model:
  `model_dhPublicValid`.
* `KemCiphertextLenOf` (`KemCiphertextLenLawShape kem::ciphertext_len Interp.real`): a successful
  `kem::encapsulate` returns a ciphertext of length `kem::ciphertext_len`.  True of the wrapper by reading
  (`tacenta-core/boundary/src/kem.rs`); not checked in Lean.  `Interp` has no field for
  `kem::ciphertext_len`, so the shape takes the constant as an argument, as `OptionEqU64Shape` does for
  `Option::eq`.  Model: `model_kemCiphertextLen`, at the constant `ok 0`.

## What it does not show

* That `establishedModelOf dh s` is the model's own establishment output (`Model.Lifecycle.establishInitiator`):
  it is read off `s`, and the T3 refinement of `establish_initiator_for` against the model is not here.
* Anything about `establish_responder`, `Session::import`, `encrypt` or any later state.
* That the real primitives meet `DhPublicValid`, `KemCiphertextLenOf`, `OptionEqU64Shape`,
  `InitiatorSuccessShape` or the contracts: assumed, each with a model.
-/

namespace Tacenta.UnitLifecycleEstablishInitiatorShape

open Aeneas Aeneas.Std Result
open tacenta_session_unit
open Tacenta.SessionUnitRatchetImportInv (bind_eq_ok_inv bind2_eq_ok_inv bind3_eq_ok_inv)

/-- The side condition of a one-element `Vec`. -/
theorem singleton_length_le {α : Type} (x : α) : [x].length ≤ 4294967295 := by simp

/-- The sparse chain table `tacenta_spqr::State::init` builds for the sending side: one entry at epoch 0,
both chains at counter 0. -/
def initChains (c1 c2 : Array U8 32#usize) : alloc.vec.Vec (U64 × tacenta_spqr.Chains) :=
  Tacenta.UnitHeadroomSatisfiable.vecOf
    [(0#u64, { send := some { ck := c1, n := 0#u64 }, receive := some { ck := c2, n := 0#u64 } })]
    (singleton_length_le _)

/-- The Triple state `tacenta_triple::State::init_sender` builds, with the derived keys as arguments. -/
def initiatorTriple (a4 a5 rk cks prk c1 c2 : Array U8 32#usize) : tacenta_triple.State :=
  { classical :=
      { dhs_pub := a4, dhr_pub := some a5, rk := rk, cks := some cks, ckr := none,
        ns := 0#u32, nr := 0#u32, pn := 0#u32, skipped := alloc.vec.Vec.new tacenta_ratchet.SkippedKey,
        events := 0#u32, labels := tacenta_ratchet.LabelSet.Tacenta },
    post_quantum :=
      { rk := prk, epoch := 0#u64, chains := initChains c1 c2,
        skipped := alloc.vec.Vec.new tacenta_spqr.Skipped, direction := tacenta_spqr.Direction.A2b } }

/-- A successful `init_sender` returns `initiatorTriple` of its two public keys and some derived keys. -/
theorem init_sender_ok (sk : Slice U8) (a4 a5 dh : Array U8 32#usize) (t : tacenta_triple.State)
    (h : tacenta_triple.State.init_sender sk a4 a5 dh tacenta_ratchet.LabelSet.Tacenta = ok t) :
    ∃ rk cks prk c1 c2, t = initiatorTriple a4 a5 rk cks prk c1 c2 := by
  unfold tacenta_triple.State.init_sender tacenta_ratchet.init_sender tacenta_spqr.State.init_alice
    tacenta_spqr.State.init at h
  obtain ⟨ec, pq, -, h⟩ := bind2_eq_ok_inv h
  obtain ⟨cl, hcl, h⟩ := bind_eq_ok_inv h
  obtain ⟨rk, cks, -, hcl⟩ := bind2_eq_ok_inv hcl
  obtain ⟨s1, -, h⟩ := bind_eq_ok_inv h
  obtain ⟨pqs, hpq, h⟩ := bind_eq_ok_inv h
  obtain ⟨prk, k1, k2, -, hpq⟩ := bind3_eq_ok_inv hpq
  obtain ⟨-, -, h⟩ := bind_eq_ok_inv h
  obtain ⟨-, -, h⟩ := bind_eq_ok_inv h
  simp only [ok.injEq] at h
  simp at hcl
  simp [lift] at hpq
  subst h hcl hpq
  exact ⟨rk, cks, prk, k1, k2, rfl⟩

/-- A successful `Braid::initiator` returns a `KeysUnsampled` Braid at epoch 1. -/
theorem braid_initiator_ok (s : Slice U8) (b : tacenta_braid.Braid)
    (h : tacenta_braid.Braid.initiator s = ok b) :
    ∃ auth, b = ⟨tacenta_braid.State.KeysUnsampled 1#u64 auth⟩ := by
  unfold tacenta_braid.Braid.initiator at h
  obtain ⟨auth, _, h⟩ := bind_eq_ok_inv h
  simp at h
  exact ⟨auth, h.symm⟩

/-- `verify_bundle` accepts a bundle only if its identity key passes `is_valid_identity_key`. -/
theorem verify_bundle_ok (b : PreKeyBundle) (u : Unit)
    (h : verify_bundle b = ok (core.result.Result.Ok u)) :
    is_valid_identity_key b.identity_key = ok true := by
  unfold verify_bundle at h
  obtain ⟨v, hv, h⟩ := bind_eq_ok_inv h
  cases v
  · simp at h
  · exact hv

/-- The pieces a successful `establish_initiator_for` assembles its session from, with the facts the code
checked or computed on the way.  Every field is read off the generated function; none is assumed. -/
structure InitiatorOutputParts {R : Type} (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R)
    (our : lifecycle.Identity) (bundle : lifecycle.PublishedBundle) where
  ratchetPrivate : tacenta_boundary.dh.PrivateKey
  ratchetPublic : tacenta_boundary.dh.PublicKeyBytes
  ratchetBytes : Array U8 32#usize
  peerRatchetBytes : Array U8 32#usize
  rootKey : Array U8 32#usize
  sendChain : Array U8 32#usize
  sparseRoot : Array U8 32#usize
  sparseSend : Array U8 32#usize
  sparseReceive : Array U8 32#usize
  auth : tacenta_braid.Auth
  identityAd : alloc.vec.Vec U8
  ourPublic : tacenta_boundary.dh.PublicKeyBytes
  ephemeral : tacenta_boundary.dh.PrivateKey
  ephemeralPublic : tacenta_boundary.dh.PublicKeyBytes
  kemCiphertext : alloc.vec.Vec U8
  kemSecret : Array U8 32#usize
  rngBefore : R
  rngAfter : R
  hRatchetPublic : tacenta_boundary.dh.PrivateKey.public_key ratchetPrivate = ok ratchetPublic
  hRatchetBytes : tacenta_boundary.dh.PublicKeyBytes.as_bytes ratchetPublic = ok ratchetBytes
  hPeerRatchetBytes :
    tacenta_boundary.dh.PublicKeyBytes.as_bytes bundle.bundle.signed_prekey = ok peerRatchetBytes
  hPeerRatchetCanonical : is_canonical_key bundle.bundle.signed_prekey = ok true
  hOurPublic : lifecycle.Identity.public our = ok ourPublic
  hIdentityAd : lifecycle.identity_ad ourPublic bundle.bundle.identity_key = ok identityAd
  hPeerValid : is_valid_identity_key bundle.bundle.identity_key = ok true
  hEphemeralPublic : tacenta_boundary.dh.PrivateKey.public_key ephemeral = ok ephemeralPublic
  hEncapsulate : tacenta_boundary.kem.encapsulate rc crc (alloc.vec.Vec.deref bundle.bundle.kem_prekey)
    rngBefore = ok (core.result.Result.Ok (kemCiphertext, kemSecret), rngAfter)

/-- The session the parts make, field for field as `establish_initiator_for` builds it. -/
def InitiatorOutputParts.session {R : Type} {rc : rand_core_1.RngCore R}
    {crc : rand_core_1.CryptoRng R} {our : lifecycle.Identity} {bundle : lifecycle.PublishedBundle}
    (p : InitiatorOutputParts rc crc our bundle) : lifecycle.Session :=
  { triple := initiatorTriple p.ratchetBytes p.peerRatchetBytes p.rootKey p.sendChain p.sparseRoot
      p.sparseSend p.sparseReceive,
    braid := ⟨tacenta_braid.State.KeysUnsampled 1#u64 p.auth⟩,
    ratchet_private := p.ratchetPrivate, identity_ad := p.identityAd,
    our_identity_public := p.ourPublic, peer_identity_public := bundle.bundle.identity_key,
    pending_initial := some
      { ephemeral_public := p.ephemeralPublic, kem_ciphertext := p.kemCiphertext,
        signed_prekey_id := bundle.signed_prekey_id, one_time_prekey_id := bundle.one_time_prekey_id,
        kem_prekey_id := bundle.kem_prekey_id },
    established_ephemeral := none }

/-- **What a successful `establish_initiator_for` returns**, for every identity, bundle, expected identity
and source of randomness: a session assembled from `InitiatorOutputParts`.  Hypothesis-free. -/
theorem establish_initiator_for_parts {R : Type} (rc : rand_core_1.RngCore R)
    (crc : rand_core_1.CryptoRng R) (our : lifecycle.Identity) (bundle : lifecycle.PublishedBundle)
    (expected : tacenta_boundary.dh.PublicKeyBytes) (rng0 rng1 : R) (s : lifecycle.Session)
    (h : lifecycle.establish_initiator_for rc crc our bundle expected rng0 =
      ok (core.result.Result.Ok s, rng1)) :
    ∃ p : InitiatorOutputParts rc crc our bundle, s = p.session := by
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
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    on_goal 28 => rfl
    case refine_19 => assumption
    case refine_20 => assumption
    case refine_21 => assumption
    case refine_22 => assumption
    case refine_23 => assumption
    case refine_24 => assumption
    case refine_25 => assumption
    case refine_26 => assumption
    case refine_27 => assumption

/-! ## Two laws about opaque primitives -/

open Tacenta.UnitSatisfiabilityJoint (Interp Interp.real Interp.model zeros32)
open Tacenta.UnitHeadroomInvariant (OptionEqU64Shape is_canonical_key_eq is_valid_identity_key_eq
  vec_ne_self array_ne_self)

/-- Every public key `PrivateKey::public_key` returns has canonical bytes and is of prime order, over an
interpretation `I`: the two checks `is_valid_identity_key` makes. -/
def DhPublicValidShape (I : Interp) : Prop :=
  ∀ (k : I.PrivateKey) (pkb : I.PublicKeyBytes), I.dhPrivPublicKey k = ok pkb →
    ∃ a, I.dhPubAsBytes pkb = ok a ∧ Tacenta.SessionUnitT1.canonicalX25519 a = true ∧
      I.dhIsPrimeOrderPublic pkb = ok true

/-- **Assumed law**: `DhPublicValidShape` at the real constants. -/
def DhPublicValid : Prop := DhPublicValidShape Interp.real

/-- At the real constants, `DhPublicValid` is the statement about the real functions. -/
theorem dhPublicValid_is :
    DhPublicValid ↔
      ∀ (k : tacenta_boundary.dh.PrivateKey) (pkb : tacenta_boundary.dh.PublicKeyBytes),
        tacenta_boundary.dh.PrivateKey.public_key k = ok pkb →
        ∃ a, tacenta_boundary.dh.PublicKeyBytes.as_bytes pkb = ok a ∧
          Tacenta.SessionUnitT1.canonicalX25519 a = true ∧
          tacenta_boundary.dh.is_prime_order_public pkb = ok true :=
  Iff.rfl

/-- The joint model satisfies `DhPublicValidShape`: its public key's bytes are 32 zero bytes, canonical, and
its prime-order check returns `true`. -/
theorem model_dhPublicValid : DhPublicValidShape Interp.model :=
  fun _ _ _ => ⟨zeros32, rfl, Tacenta.SessionUnitRatchetImportInv.Ratchet.canonical_zeros, rfl⟩

/-- A successful encapsulation's ciphertext has the length `ciphertextLen` returns, for a constant
`ciphertextLen` standing for `kem::ciphertext_len`, over an interpretation `I`. -/
def KemCiphertextLenLawShape (ciphertextLen : Result Usize) (I : Interp) : Prop :=
  ∀ {R : Type} (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R) (pk : Slice U8)
    (rng : R) (ct : alloc.vec.Vec U8) (ss : Array U8 32#usize) (rng' : R),
    I.kemEncapsulate rc crc pk rng = ok (core.result.Result.Ok (ct, ss), rng') →
    ∃ n, ciphertextLen = ok n ∧ ct.val.length = n.val

/-- **Assumed law**: `KemCiphertextLenLawShape` at the real constants, `kem::ciphertext_len` and
`kem::encapsulate`. -/
def KemCiphertextLenOf : Prop :=
  KemCiphertextLenLawShape tacenta_boundary.kem.ciphertext_len Interp.real

/-- At the real constants, `KemCiphertextLenOf` is the statement about the real functions. -/
theorem kemCiphertextLenOf_is :
    KemCiphertextLenOf ↔
      ∀ {R : Type} (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R) (pk : Slice U8)
        (rng : R) (ct : alloc.vec.Vec U8) (ss : Array U8 32#usize) (rng' : R),
        tacenta_boundary.kem.encapsulate rc crc pk rng =
          ok (core.result.Result.Ok (ct, ss), rng') →
        ∃ n, tacenta_boundary.kem.ciphertext_len = ok n ∧ ct.val.length = n.val :=
  Iff.rfl

/-- The joint model, whose encapsulation returns an empty ciphertext, satisfies `KemCiphertextLenLawShape` with
the constant `ok 0`.  `Interp` has no field for `kem::ciphertext_len`, so the constant is chosen here. -/
theorem model_kemCiphertextLen : KemCiphertextLenLawShape (ok 0#usize) Interp.model := by
  intro R rc crc pk rng ct ss rng' h
  simp only [Interp.model, ok.injEq, Prod.mk.injEq, core.result.Result.Ok.injEq] at h
  obtain ⟨⟨rfl, -⟩, -⟩ := h
  exact ⟨0#usize, rfl, by simp⟩

/-! ## `Session::invariant` at every successful output -/

/-- Under `DhPublicValid`, the bytes of a public key `public_key` returned are canonical. -/
theorem dhPublicValid_canonical (hpub : DhPublicValid) {k : tacenta_boundary.dh.PrivateKey}
    {pkb : tacenta_boundary.dh.PublicKeyBytes} {a : Array U8 32#usize}
    (hk : tacenta_boundary.dh.PrivateKey.public_key k = ok pkb)
    (ha : tacenta_boundary.dh.PublicKeyBytes.as_bytes pkb = ok a) :
    Tacenta.SessionUnitT1.canonicalX25519 a = true := by
  obtain ⟨a', ha', hcan, -⟩ := dhPublicValid_is.mp hpub k pkb hk
  rw [ha] at ha'
  cases ha'
  exact hcan

/-- Under `DhPublicValid`, a public key `public_key` returned passes `is_valid_identity_key` and
`is_canonical_key`. -/
theorem dhPublicValid_valid (hpub : DhPublicValid) {k : tacenta_boundary.dh.PrivateKey}
    {pkb : tacenta_boundary.dh.PublicKeyBytes}
    (hk : tacenta_boundary.dh.PrivateKey.public_key k = ok pkb) :
    is_valid_identity_key pkb = ok true ∧ is_canonical_key pkb = ok true := by
  obtain ⟨a, ha, hcan, hprime⟩ := dhPublicValid_is.mp hpub k pkb hk
  exact ⟨is_valid_identity_key_eq pkb a ha hcan hprime, by rw [is_canonical_key_eq pkb a ha, hcan]⟩

/-- Under `DhPublicValid`, an identity's public key passes `is_valid_identity_key`. -/
theorem identity_public_valid (hpub : DhPublicValid) {our : lifecycle.Identity}
    {pkb : tacenta_boundary.dh.PublicKeyBytes} (h : lifecycle.Identity.public our = ok pkb) :
    is_valid_identity_key pkb = ok true := by
  unfold lifecycle.Identity.public at h
  obtain ⟨k, -, hk⟩ := bind_eq_ok_inv h
  exact (dhPublicValid_valid hpub hk).1

/-- `is_canonical_key` returning `true` gives the canonical test of the key's bytes. -/
theorem canonical_of_is_canonical_key {pk : tacenta_boundary.dh.PublicKeyBytes} {a : Array U8 32#usize}
    (ha : tacenta_boundary.dh.PublicKeyBytes.as_bytes pk = ok a) (h : is_canonical_key pk = ok true) :
    Tacenta.SessionUnitT1.canonicalX25519 a = true := by
  rw [is_canonical_key_eq pk a ha] at h
  simpa using h

/-- `Triple::invariant` of the Triple `init_sender` builds, given its two public keys are canonical. -/
theorem initiatorTriple_invariant (a4 a5 rk cks prk c1 c2 : Array U8 32#usize)
    (h4 : Tacenta.SessionUnitT1.canonicalX25519 a4 = true)
    (h5 : Tacenta.SessionUnitT1.canonicalX25519 a5 = true) :
    tacenta_triple.State.invariant (initiatorTriple a4 a5 rk cks prk c1 c2) = ok true := by
  have h1 : tacenta_ratchet.State.invariant
      (initiatorTriple a4 a5 rk cks prk c1 c2).classical = ok true := by
    rw [Tacenta.SessionUnitRatchetImportInv.Ratchet.invariant_true_iff]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [initiatorTriple, alloc.vec.Vec.new, tacenta_ratchet.MAX_SKIPPED_STORE]
    · simp [initiatorTriple, U32.max_eq]
    · simp [initiatorTriple, alloc.vec.Vec.new]
    · simp [initiatorTriple, alloc.vec.Vec.new]
    · simp [initiatorTriple]
    · simpa [initiatorTriple] using h4
    · simpa [initiatorTriple] using h5
    · simp [initiatorTriple, alloc.vec.Vec.new]
  have h2 : tacenta_spqr.State.invariant
      (initiatorTriple a4 a5 rk cks prk c1 c2).post_quantum = ok true := by
    rw [Tacenta.SessionUnitRatchetImportInv.Spqr.invariant_true_iff]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [initiatorTriple, alloc.vec.Vec.new, tacenta_spqr.MAX_SKIPPED_STORE]
    · simp [initiatorTriple, initChains, Tacenta.UnitHeadroomSatisfiable.vecOf,
        core.num.U64.saturating_add, UScalar.saturating_add, tacenta_spqr.EPOCHS_KEPT, U64.max_eq]
      decide
    · simp [initiatorTriple, initChains, Tacenta.UnitHeadroomSatisfiable.vecOf]
    · simp [initiatorTriple, initChains, Tacenta.UnitHeadroomSatisfiable.vecOf]
    · simp [initiatorTriple, alloc.vec.Vec.new]
    · simp [initiatorTriple, alloc.vec.Vec.new]
  simp only [initiatorTriple] at h1 h2
  unfold tacenta_triple.State.invariant
  simp [h1, h2, initiatorTriple, tacenta_spqr.State.impl.direction,
    tacenta_ratchet.State.started_as_sender]

/-- `Session::structural_invariant` of the session the parts make. -/
theorem structural_parts {R : Type} {rc : rand_core_1.RngCore R} {crc : rand_core_1.CryptoRng R}
    {our : lifecycle.Identity} {bundle : lifecycle.PublishedBundle}
    (hpub : DhPublicValid) (hct : KemCiphertextLenOf)
    (hoeq : OptionEqU64Shape (@core.option.Option.Insts.CoreCmpPartialEqOption.eq))
    (p : InitiatorOutputParts rc crc our bundle) :
    lifecycle.Session.structural_invariant p.session = ok true := by
  have hv := identity_public_valid hpub p.hOurPublic
  have hc := (dhPublicValid_valid hpub p.hEphemeralPublic).2
  obtain ⟨n, hctl, hlen0⟩ := kemCiphertextLenOf_is.mp hct rc crc _ _ _ _ _ p.hEncapsulate
  have hlen : alloc.vec.Vec.len p.kemCiphertext = n := by
    apply UScalar.eq_of_val_eq; simp [alloc.vec.Vec.len, hlen0]
  unfold lifecycle.Session.structural_invariant
  simp [InitiatorOutputParts.session, initiatorTriple, p.hRatchetPublic, p.hRatchetBytes,
    tacenta_triple.State.sending_public, tacenta_ratchet.State.sending_public, array_ne_self,
    tacenta_braid.Braid.failed, tacenta_braid.Braid.is_initiator, tacenta_braid.State.epoch,
    lifecycle.Session.is_responder, p.hIdentityAd, vec_ne_self, tacenta_triple.State.direction,
    tacenta_spqr.State.impl.direction, hv, p.hPeerValid, hc, hctl, hlen,
    tacenta_braid.Braid.epoch, tacenta_triple.State.epoch, tacenta_spqr.State.impl.epoch,
    tacenta_braid.Braid.state_tag, lift, tacenta_spqr.Direction.Insts.CoreCmpPartialEqDirection.eq]
  have h01 : U64.checked_add 0#u64 1#u64 = some 1#u64 := by decide
  rw [h01, hoeq]
  rfl

/-- `Session::invariant` of the session the parts make. -/
theorem parts_invariant {R : Type} {rc : rand_core_1.RngCore R} {crc : rand_core_1.CryptoRng R}
    {our : lifecycle.Identity} {bundle : lifecycle.PublishedBundle}
    (hpub : DhPublicValid) (hct : KemCiphertextLenOf)
    (hoeq : OptionEqU64Shape (@core.option.Option.Insts.CoreCmpPartialEqOption.eq))
    (p : InitiatorOutputParts rc crc our bundle) :
    lifecycle.Session.invariant p.session = ok true := by
  unfold lifecycle.Session.invariant
  rw [structural_parts hpub hct hoeq p]
  simp only [Aeneas.Std.bind_tc_ok, if_true]
  unfold lifecycle.Session.leaf_invariants
  have h4 := dhPublicValid_canonical hpub p.hRatchetPublic p.hRatchetBytes
  have h5 := canonical_of_is_canonical_key p.hPeerRatchetBytes p.hPeerRatchetCanonical
  simp only [InitiatorOutputParts.session]
  rw [initiatorTriple_invariant _ _ _ _ _ _ _ h4 h5]
  simp [tacenta_braid.Braid.invariant]

/-- **Every successful `establish_initiator_for` output passes `Session::invariant`**, for every identity,
bundle, expected identity and source of randomness, under the two assumed laws `DhPublicValid` and
`KemCiphertextLenOf` and the recorded assumption `OptionEqU64Shape`. -/
theorem establish_initiator_for_admissible {R : Type} (rc : rand_core_1.RngCore R)
    (crc : rand_core_1.CryptoRng R)
    (hpub : DhPublicValid) (hct : KemCiphertextLenOf)
    (hoeq : OptionEqU64Shape (@core.option.Option.Insts.CoreCmpPartialEqOption.eq))
    (our : lifecycle.Identity) (bundle : lifecycle.PublishedBundle)
    (expected : tacenta_boundary.dh.PublicKeyBytes) (rng0 rng1 : R) (s : lifecycle.Session)
    (h : lifecycle.establish_initiator_for rc crc our bundle expected rng0 =
      ok (core.result.Result.Ok s, rng1)) :
    lifecycle.Session.invariant s = ok true := by
  obtain ⟨p, rfl⟩ := establish_initiator_for_parts rc crc our bundle expected rng0 rng1 s h
  exact parts_invariant hpub hct hoeq p

/-! ## The four counter ceilings at every successful output -/

/-- `CounterHeadroom` of the session the parts make: clock 0, sparse epoch 0, both chain counters 0, Braid
epoch 1. -/
theorem counterHeadroom_parts {R : Type} {rc : rand_core_1.RngCore R}
    {crc : rand_core_1.CryptoRng R} {our : lifecycle.Identity} {bundle : lifecycle.PublishedBundle}
    (p : InitiatorOutputParts rc crc our bundle) :
    Tacenta.UnitLifecycleDecryptRunBounds.CounterHeadroom p.session := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [InitiatorOutputParts.session, initiatorTriple, U32.max_eq]
  · simp [InitiatorOutputParts.session, initiatorTriple, U64.max_eq]
  · intro q hq ch hch
    simp [InitiatorOutputParts.session, initiatorTriple, initChains,
      Tacenta.UnitHeadroomSatisfiable.vecOf] at hq
    subst hq
    rcases hch with h | h <;> (simp at h; subst h; simp [U64.max_eq])
  · simp only [InitiatorOutputParts.session, Tacenta.SessionUnitBraidT1.State.epoch_val]
    scalar_tac

/-- **All four counter ceilings hold at every successful `establish_initiator_for` output**, with no
hypothesis: the classical clock and both sparse chain counters are 0, the sparse epoch is 0, the Braid epoch
is 1. -/
theorem counterHeadroom_of_established {R : Type} (rc : rand_core_1.RngCore R)
    (crc : rand_core_1.CryptoRng R) (our : lifecycle.Identity) (bundle : lifecycle.PublishedBundle)
    (expected : tacenta_boundary.dh.PublicKeyBytes) (rng0 rng1 : R) (s : lifecycle.Session)
    (h : lifecycle.establish_initiator_for rc crc our bundle expected rng0 =
      ok (core.result.Result.Ok s, rng1)) :
    Tacenta.UnitLifecycleDecryptRunBounds.CounterHeadroom s := by
  obtain ⟨p, rfl⟩ := establish_initiator_for_parts rc crc our bundle expected rng0 rng1 s h
  exact counterHeadroom_parts p

/-! ## The model state, and the relation -/

open Tacenta.UnitLifecycleT3 (DhView SessionRefines vecOf pendingInitialOf)

/-- The model Braid state a translated `KeysUnsampled` state stands for.  Used here only at a
`KeysUnsampled` state; every other state is sent to `failed`, which no other state refines. -/
def unsampledModelOf : tacenta_braid.State → Model.Braid.BraidState
  | .KeysUnsampled epoch auth => .keysUnsampled epoch.val (Tacenta.SessionUnitBraidT3.AuthOf auth)
  | _ => .failed

/-- **The model session an established initiator session stands for**: every component read off `s`
through the DH view, the Triple through `ratchetAbs`/`spqrAbs`, the Braid through `unsampledModelOf`. -/
def establishedModelOf (dh : DhView) (s : lifecycle.Session) : Model.Lifecycle.Session :=
  { triple :=
      { classical := Tacenta.SessionUnitTripleT3.ratchetAbs s.triple.classical
        postQuantum := Tacenta.SessionUnitTripleT3.spqrAbs s.triple.post_quantum }
    braid := unsampledModelOf s.braid.state
    ratchetPrivate := dh.privateKey s.ratchet_private
    identityAd := vecOf s.identity_ad
    ourIdentityPublic := dh.publicKey s.our_identity_public
    peerIdentityPublic := dh.publicKey s.peer_identity_public
    pendingInitial := s.pending_initial.map (pendingInitialOf dh)
    establishedEphemeral := s.established_ephemeral.map vecOf }

/-- The session the parts make refines `establishedModelOf`. -/
theorem sessionRefines_parts {R : Type} {rc : rand_core_1.RngCore R}
    {crc : rand_core_1.CryptoRng R} {our : lifecycle.Identity} {bundle : lifecycle.PublishedBundle}
    (dh : DhView) (K : Model.Braid.Kem) (p : InitiatorOutputParts rc crc our bundle) :
    SessionRefines dh K p.session (establishedModelOf dh p.session) :=
  ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **Every successful `establish_initiator_for` output refines `establishedModelOf`**, for every DH view and
every KEM: no hypothesis. -/
theorem sessionRefines_established {R : Type} (rc : rand_core_1.RngCore R)
    (crc : rand_core_1.CryptoRng R) (dh : DhView) (K : Model.Braid.Kem)
    (our : lifecycle.Identity) (bundle : lifecycle.PublishedBundle)
    (expected : tacenta_boundary.dh.PublicKeyBytes) (rng0 rng1 : R) (s : lifecycle.Session)
    (h : lifecycle.establish_initiator_for rc crc our bundle expected rng0 =
      ok (core.result.Result.Ok s, rng1)) :
    SessionRefines dh K s (establishedModelOf dh s) := by
  obtain ⟨p, rfl⟩ := establish_initiator_for_parts rc crc our bundle expected rng0 rng1 s h
  exact sessionRefines_parts dh K p

/-- A model session the parts' session refines is `establishedModelOf`. -/
theorem sessionRefines_parts_unique {R : Type} {rc : rand_core_1.RngCore R}
    {crc : rand_core_1.CryptoRng R} {our : lifecycle.Identity} {bundle : lifecycle.PublishedBundle}
    (dh : DhView) (K : Model.Braid.Kem) (p : InitiatorOutputParts rc crc our bundle)
    (m : Model.Lifecycle.Session) (hrel : SessionRefines dh K p.session m) :
    m = establishedModelOf dh p.session := by
  obtain ⟨⟨htc, htp⟩, hb, hrp, had, hour, hpeer, hpend, hest⟩ := hrel
  obtain ⟨⟨mc, mp⟩, mb, mrp, mad, mour, mpeer, mpend, mest⟩ := m
  simp only at htc htp hb hrp had hour hpeer hpend hest
  subst htc htp hrp had hour hpeer hpend hest
  cases mb with
  | keysUnsampled e a =>
      obtain ⟨he, ha⟩ := hb
      subst he ha
      rfl
  | _ => simp [InitiatorOutputParts.session, Tacenta.SessionUnitBraidT3.StateRefines] at hb

/-- **`establishedModelOf` is the only model session a successful output refines**, for every DH view and
KEM: any related model session equals it. -/
theorem sessionRefines_established_unique {R : Type} (rc : rand_core_1.RngCore R)
    (crc : rand_core_1.CryptoRng R) (dh : DhView) (K : Model.Braid.Kem)
    (our : lifecycle.Identity) (bundle : lifecycle.PublishedBundle)
    (expected : tacenta_boundary.dh.PublicKeyBytes) (rng0 rng1 : R) (s : lifecycle.Session)
    (h : lifecycle.establish_initiator_for rc crc our bundle expected rng0 =
      ok (core.result.Result.Ok s, rng1))
    (m : Model.Lifecycle.Session) (hrel : SessionRefines dh K s m) :
    m = establishedModelOf dh s := by
  obtain ⟨p, rfl⟩ := establish_initiator_for_parts rc crc our bundle expected rng0 rng1 s h
  exact sessionRefines_parts_unique dh K p m hrel

/-! ## The success case is inhabited -/

/-- What one successful run needs from the opaque primitives beyond totality, over an interpretation `I`:
a public key with canonical bytes, of prime order and equal to itself, on which some signature verifies for
every message and every private key agrees contributorily; and a KEM public key on which encapsulation
succeeds from every source state. -/
structure InitiatorSuccessShape (I : Interp) {R : Type} (rc : rand_core_1.RngCore R)
    (crc : rand_core_1.CryptoRng R) : Prop where
  key : ∃ (pkb : I.PublicKeyBytes) (a : Array U8 32#usize),
    I.dhPubAsBytes pkb = ok a ∧ Tacenta.SessionUnitT1.canonicalX25519 a = true ∧
    I.dhIsPrimeOrderPublic pkb = ok true ∧ I.dhPubEq pkb pkb = ok true ∧
    (∀ m, ∃ sig, I.xeddsaVerify pkb m sig = ok (core.result.Result.Ok ())) ∧
    (∀ k, ∃ x, I.dhPrivAgree k pkb = ok (some x))
  kem : ∃ kemPk : alloc.vec.Vec U8, kemPk.val.length + 1 ≤ Usize.max ∧
    ∀ rng, ∃ ct ss rng', I.kemEncapsulate rc crc (alloc.vec.Vec.deref kemPk) rng =
      ok (core.result.Result.Ok (ct, ss), rng')

/-- The joint model satisfies `InitiatorSuccessShape` for every source of randomness. -/
theorem model_initiatorSuccess {R : Type} (rc : rand_core_1.RngCore R)
    (crc : rand_core_1.CryptoRng R) : InitiatorSuccessShape Interp.model rc crc :=
  ⟨⟨(), zeros32, rfl, Tacenta.SessionUnitRatchetImportInv.Ratchet.canonical_zeros, rfl, rfl,
      fun _ => ⟨Array.repeat 64#usize 0#u8, rfl⟩,
      fun _ => ⟨zeros32, rfl⟩⟩,
    ⟨alloc.vec.Vec.new U8, by simp; scalar_tac,
      fun rng => ⟨_, _, _, rfl⟩⟩⟩

/-- The bundle a successful run is shown for: one key as identity and signed prekey, no one-time prekey. -/
def successBundle (pkb : tacenta_boundary.dh.PublicKeyBytes) (sig1 sig2 : Array U8 64#usize)
    (kem : alloc.vec.Vec U8) : lifecycle.PublishedBundle :=
  { bundle :=
      { identity_key := pkb, signed_prekey := pkb, signed_prekey_signature := sig1,
        kem_prekey := kem, kem_prekey_signature := sig2, one_time_prekey := none },
    signed_prekey_id := 0#u32, one_time_prekey_id := serialization.ABSENT_ID,
    kem_prekey_id := 0#u32 }

/-- `verify_bundle` accepts `successBundle` when both signatures verify on the encoded keys. -/
theorem verify_successBundle (pkb : tacenta_boundary.dh.PublicKeyBytes) (a : Array U8 32#usize)
    (hbytes : tacenta_boundary.dh.PublicKeyBytes.as_bytes pkb = ok a)
    (hcan : Tacenta.SessionUnitT1.canonicalX25519 a = true)
    (hprime : tacenta_boundary.dh.is_prime_order_public pkb = ok true)
    (sig1 sig2 : Array U8 64#usize) (kem v v1 : alloc.vec.Vec U8)
    (hv : encode_ec pkb = ok v)
    (hs1 : tacenta_boundary.xeddsa.verify pkb (alloc.vec.Vec.deref v) sig1 =
      ok (core.result.Result.Ok ()))
    (hv1 : encode_kem (alloc.vec.Vec.deref kem) = ok v1)
    (hs2 : tacenta_boundary.xeddsa.verify pkb (alloc.vec.Vec.deref v1) sig2 =
      ok (core.result.Result.Ok ())) :
    verify_bundle (successBundle pkb sig1 sig2 kem).bundle = ok (core.result.Result.Ok ()) := by
  unfold verify_bundle
  simp [successBundle, is_valid_identity_key_eq pkb a hbytes hcan hprime, hv, hs1, hv1, hs2]

/-- `initiator_shared_secret` succeeds on `successBundle` when `verify_bundle` accepts it and every agreement with
its key is contributory. -/
theorem shared_secret_successBundle (hz : Tacenta.SessionUnitBraidT1.ZeroizingArrayRoundTrip)
    (hkdf : Tacenta.SessionUnitSessionT1.HkdfTotal) [Tacenta.SessionUnitSessionT1.ZeroizingModel]
    (pkb : tacenta_boundary.dh.PublicKeyBytes) (sig1 sig2 : Array U8 64#usize)
    (kem : alloc.vec.Vec U8)
    (hverify : verify_bundle (successBundle pkb sig1 sig2 kem).bundle = ok (core.result.Result.Ok ()))
    (hag : ∀ k, ∃ x, tacenta_boundary.dh.PrivateKey.agree k pkb = ok (some x))
    (ik eph : tacenta_boundary.dh.PrivateKey) (enc : Array U8 32#usize) :
    ∃ sec, initiator_shared_secret ik eph (successBundle pkb sig1 sig2 kem).bundle enc =
      ok (core.result.Result.Ok sec) := by
  obtain ⟨x1, hx1⟩ := hag ik
  obtain ⟨x2, hx2⟩ := hag eph
  obtain ⟨z1, hz1, hz1d⟩ := Std.WP.spec_imp_exists (Tacenta.SessionUnitBraidT1.zeroizing_new_spec hz x1)
  obtain ⟨z2, hz2, hz2d⟩ := Std.WP.spec_imp_exists (Tacenta.SessionUnitBraidT1.zeroizing_new_spec hz x2)
  obtain ⟨sh, hsh⟩ := (Tacenta.SessionUnitT1.noPanic_iff _).mp
    (Tacenta.SessionUnitSessionT1.shared_secret_no_panic hkdf x1 x2 x2 enc none)
  unfold initiator_shared_secret
  simp only [successBundle] at hverify ⊢
  simp [hverify, core.result.Result.Insts.CoreOpsTry.branch, hx1, hx2, contributory, hz1, hz2,
    hz1d, hz2d, hsh]

open Tacenta.UnitLifecycleT1 in
/-- **A successful `establish_initiator_for` exists**, at the real constants, under the axiom part of
`EstablishInitiatorContracts` and `InitiatorSuccessShape`: for every identity and source state there are a
bundle and a session with `establish_initiator_for ... = ok (.Ok s, rng1)`, the expected identity being the
bundle's own.  So the theorems above that quantify over successful outputs are not about an empty set under
those assumptions. -/
theorem establish_initiator_for_succeeds {R : Type} (rc : rand_core_1.RngCore R)
    (crc : rand_core_1.CryptoRng R)
    (axioms : Nonempty (Tacenta.UnitSatisfiabilityJoint.InitiatorAxiom Interp.real rc))
    (succ : InitiatorSuccessShape Interp.real rc crc) (our : lifecycle.Identity) (rng0 : R) :
    ∃ (bundle : lifecycle.PublishedBundle) (s : lifecycle.Session) (rng1 : R),
      lifecycle.establish_initiator_for rc crc our bundle bundle.bundle.identity_key rng0 =
        ok (core.result.Result.Ok s, rng1) := by
  obtain ⟨c⟩ := Tacenta.UnitSatisfiabilityRecords.initiator_contracts_of_axiom_base rc axioms
  rcases c with ⟨hdh, hid, hagree, hkem, hx, hrngTotal, hrng, hkdf, hzero, htripleZero, hkdfInit,
    hspqrZero, hbraidKdf, hzeroArray, hindex⟩
  let _ : Tacenta.SessionUnitSessionT1.ZeroizingModel := hzero
  obtain ⟨pkb, a, hbytes, hcan, hprime, heq, hsig, hag⟩ := succ.key
  obtain ⟨kem, hkemLen, henc⟩ := succ.kem
  have hbytes' : tacenta_boundary.dh.PublicKeyBytes.as_bytes pkb = ok a := hbytes
  have hprime' : tacenta_boundary.dh.is_prime_order_public pkb = ok true := hprime
  have heq' : tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq pkb pkb =
      ok true := heq
  have hsig' : ∀ m, ∃ sig, tacenta_boundary.xeddsa.verify pkb m sig = ok (core.result.Result.Ok ()) :=
    hsig
  have hag' : ∀ k, ∃ x, tacenta_boundary.dh.PrivateKey.agree k pkb = ok (some x) := hag
  have henc' : ∀ rng, ∃ ct ss rng', tacenta_boundary.kem.encapsulate rc crc
      (alloc.vec.Vec.deref kem) rng = ok (core.result.Result.Ok (ct, ss), rng') := henc
  obtain ⟨v, hv, -⟩ := Std.WP.spec_imp_exists (encode_ec_spec hdh pkb)
  obtain ⟨sig1, hs1⟩ := hsig' (alloc.vec.Vec.deref v)
  obtain ⟨v1, hv1, -⟩ := Std.WP.spec_imp_exists
    (Tacenta.UnitLifecycleT1.encode_kem_no_panic (alloc.vec.Vec.deref kem) hkemLen)
  obtain ⟨sig2, hs2⟩ := hsig' (alloc.vec.Vec.deref v1)
  have hverify := verify_successBundle pkb a hbytes' hcan hprime' sig1 sig2 kem v v1 hv hs1 hv1 hs2
  refine ⟨successBundle pkb sig1 sig2 kem, ?_⟩
  obtain ⟨⟨a1, r1⟩, hr1, -⟩ := Std.WP.spec_imp_exists (random_secret_no_panic rc crc hrng rng0)
  obtain ⟨eph, heph, -⟩ := Std.WP.spec_imp_exists (private_key_from_bytes_no_panic hdh a1)
  obtain ⟨ct, ss, r2, hencap⟩ := henc' r1
  obtain ⟨z1, hz1, hz1d⟩ :=
    Std.WP.spec_imp_exists (Tacenta.SessionUnitBraidT1.zeroizing_new_spec hzeroArray ss)
  obtain ⟨ik, hik, -⟩ :=
    Std.WP.spec_imp_exists (Tacenta.UnitLifecycleT1.identity_dh_key_no_panic hdh our)
  obtain ⟨sec, hsec⟩ :=
    shared_secret_successBundle hzeroArray hkdf pkb sig1 sig2 kem hverify hag' ik eph ss
  obtain ⟨z2, hz2, hz2d⟩ :=
    Std.WP.spec_imp_exists (Tacenta.SessionUnitBraidT1.zeroizing_new_spec hzeroArray sec)
  obtain ⟨⟨a2, r3⟩, hr3, -⟩ := Std.WP.spec_imp_exists (random_secret_no_panic rc crc hrng r2)
  obtain ⟨rp, hrp, -⟩ := Std.WP.spec_imp_exists (private_key_from_bytes_no_panic hdh a2)
  obtain ⟨d, hd⟩ := hag' rp
  obtain ⟨z3, hz3, hz3d⟩ :=
    Std.WP.spec_imp_exists (Tacenta.SessionUnitBraidT1.zeroizing_new_spec hzeroArray d)
  obtain ⟨s1, hs1i, -⟩ := Std.WP.spec_imp_exists (Tacenta.SessionUnitBraidT1.index_full_spec hindex sec)
  obtain ⟨rpub, hrpub, -⟩ := Std.WP.spec_imp_exists (private_key_public_no_panic hdh rp)
  obtain ⟨a4, ha4, -⟩ := Std.WP.spec_imp_exists (public_key_as_bytes_no_panic hdh rpub)
  obtain ⟨triple, htriple, -⟩ := Std.WP.spec_imp_exists
    (Tacenta.SessionUnitTripleT1.State.init_sender_no_panic hkdf htripleZero hkdfInit hspqrZero s1 a4
      a d tacenta_ratchet.LabelSet.Tacenta)
  obtain ⟨braid, hbraid, -⟩ :=
    Std.WP.spec_imp_exists (Tacenta.SessionUnitBraidT1.Braid.initiator_no_panic hbraidKdf hzeroArray s1)
  obtain ⟨opub, hopub, -⟩ :=
    Std.WP.spec_imp_exists (Tacenta.UnitLifecycleT1.identity_public_no_panic hdh our)
  obtain ⟨ad, had, -⟩ := Std.WP.spec_imp_exists (identity_ad_no_panic hdh opub pkb)
  obtain ⟨epub, hepub, -⟩ := Std.WP.spec_imp_exists (private_key_public_no_panic hdh eph)
  have hne : core.cmp.PartialEq.ne.trait_default
      tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes pkb pkb = ok false := by
    simp [core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default, heq']
  have hcanon : is_canonical_key pkb = ok true := by rw [is_canonical_key_eq pkb a hbytes', hcan]
  simp only [successBundle] at hverify hsec
  simp [lifecycle.establish_initiator_for, successBundle, hne, hcanon, hverify, hr1, heph, hencap, hz1, hz1d, hik, hsec, hz2, hz2d,
    hr3, hrp, hd, hz3, hz3d, hs1i, hrpub, ha4, hbytes', htriple, hbraid, hopub, had, hepub]

/-- **Under the axiom base, `InitiatorSuccessShape` and the three laws, a successful output exists and every
conclusion above holds at it**: the invariant, the four ceilings and the relation to `establishedModelOf`, for
every DH view and KEM. -/
theorem established_initiator_inhabited {R : Type} (rc : rand_core_1.RngCore R)
    (crc : rand_core_1.CryptoRng R)
    (axioms : Nonempty (Tacenta.UnitSatisfiabilityJoint.InitiatorAxiom Interp.real rc))
    (succ : InitiatorSuccessShape Interp.real rc crc)
    (hpub : DhPublicValid) (hct : KemCiphertextLenOf)
    (hoeq : OptionEqU64Shape (@core.option.Option.Insts.CoreCmpPartialEqOption.eq))
    (dh : DhView) (K : Model.Braid.Kem) (our : lifecycle.Identity) (rng0 : R) :
    ∃ (bundle : lifecycle.PublishedBundle) (s : lifecycle.Session) (rng1 : R),
      lifecycle.establish_initiator_for rc crc our bundle bundle.bundle.identity_key rng0 =
        ok (core.result.Result.Ok s, rng1) ∧
      lifecycle.Session.invariant s = ok true ∧
      Tacenta.UnitLifecycleDecryptRunBounds.CounterHeadroom s ∧
      SessionRefines dh K s (establishedModelOf dh s) := by
  obtain ⟨bundle, s, rng1, h⟩ := establish_initiator_for_succeeds rc crc axioms succ our rng0
  exact ⟨bundle, s, rng1, h,
    establish_initiator_for_admissible rc crc hpub hct hoeq our bundle _ rng0 rng1 s h,
    counterHeadroom_of_established rc crc our bundle _ rng0 rng1 s h,
    sessionRefines_established rc crc dh K our bundle _ rng0 rng1 s h⟩

/-- **The hypotheses of `established_initiator_inhabited` hold together in the joint model**, for the
byte-stream source of `UnitLifecycleIntegrationScreen`: the axiom part of the initiator contracts,
`InitiatorSuccessShape`, `DhPublicValidShape`, `KemCiphertextLenLawShape` at the constant `ok 0`, and
`OptionEqU64Shape` at `optionEqImpl`.  Each is a statement over the opaque constants that the real
constants instantiate, so this is an argument about derivations, not a statement that the real primitives
meet them. -/
theorem establishment_hypotheses_satisfiable :
    Nonempty (Tacenta.UnitSatisfiabilityJoint.InitiatorAxiom Interp.model
        Tacenta.UnitLifecycleIntegrationScreen.byteRng) ∧
      InitiatorSuccessShape Interp.model Tacenta.UnitLifecycleIntegrationScreen.byteRng
        Tacenta.UnitLifecycleIntegrationScreen.byteCrc ∧
      DhPublicValidShape Interp.model ∧
      KemCiphertextLenLawShape (ok 0#usize) Interp.model ∧
      OptionEqU64Shape (@Tacenta.UnitHeadroomInvariant.optionEqImpl) :=
  ⟨⟨Tacenta.UnitSatisfiabilityJoint.model_initiatorAxiom Tacenta.UnitOracleModel.byteRng_total
      (fun _ _ _ => ⟨_, rfl⟩)⟩,
    model_initiatorSuccess _ _, model_dhPublicValid, model_kemCiphertextLen,
    Tacenta.UnitHeadroomInvariant.optionEqImpl_shape⟩

end Tacenta.UnitLifecycleEstablishInitiatorShape


/-! ## Pins

The constants each result depends on, and the statement of each result and definition, held by the
build.  `attest.py` requires every one of them (`REQUIRED_PINS`, `REQUIRED_STATEMENT_PINS`,
`REQUIRED_PRINT_FORM`). -/

/--
info: 'Tacenta.UnitLifecycleEstablishInitiatorShape.singleton_length_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishInitiatorShape.singleton_length_le

/--
info: 'Tacenta.UnitLifecycleEstablishInitiatorShape.init_sender_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishInitiatorShape.init_sender_ok

/--
info: 'Tacenta.UnitLifecycleEstablishInitiatorShape.braid_initiator_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishInitiatorShape.braid_initiator_ok

/--
info: 'Tacenta.UnitLifecycleEstablishInitiatorShape.verify_bundle_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.dh.is_prime_order_public,
 tacenta_session_unit.tacenta_boundary.xeddsa.verify,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.as_bytes]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishInitiatorShape.verify_bundle_ok

/--
info: 'Tacenta.UnitLifecycleEstablishInitiatorShape.establish_initiator_for_parts' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleEstablishInitiatorShape.establish_initiator_for_parts

/--
info: 'Tacenta.UnitLifecycleEstablishInitiatorShape.dhPublicValid_is' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleEstablishInitiatorShape.dhPublicValid_is

/--
info: 'Tacenta.UnitLifecycleEstablishInitiatorShape.model_dhPublicValid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishInitiatorShape.model_dhPublicValid

/--
info: 'Tacenta.UnitLifecycleEstablishInitiatorShape.kemCiphertextLenOf_is' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleEstablishInitiatorShape.kemCiphertextLenOf_is

/--
info: 'Tacenta.UnitLifecycleEstablishInitiatorShape.model_kemCiphertextLen' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishInitiatorShape.model_kemCiphertextLen

/--
info: 'Tacenta.UnitLifecycleEstablishInitiatorShape.dhPublicValid_canonical' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleEstablishInitiatorShape.dhPublicValid_canonical

/--
info: 'Tacenta.UnitLifecycleEstablishInitiatorShape.dhPublicValid_valid' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleEstablishInitiatorShape.dhPublicValid_valid

/--
info: 'Tacenta.UnitLifecycleEstablishInitiatorShape.identity_public_valid' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleEstablishInitiatorShape.identity_public_valid

/--
info: 'Tacenta.UnitLifecycleEstablishInitiatorShape.canonical_of_is_canonical_key' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.as_bytes]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishInitiatorShape.canonical_of_is_canonical_key

/--
info: 'Tacenta.UnitLifecycleEstablishInitiatorShape.initiatorTriple_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishInitiatorShape.initiatorTriple_invariant

/--
info: 'Tacenta.UnitLifecycleEstablishInitiatorShape.structural_parts' depends on axioms: [propext,
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
 tacenta_session_unit.core.option.Option.Insts.CoreCmpPartialEqOption.eq,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishInitiatorShape.structural_parts

/--
info: 'Tacenta.UnitLifecycleEstablishInitiatorShape.parts_invariant' depends on axioms: [propext,
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
 tacenta_session_unit.core.option.Option.Insts.CoreCmpPartialEqOption.eq,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishInitiatorShape.parts_invariant

/--
info: 'Tacenta.UnitLifecycleEstablishInitiatorShape.establish_initiator_for_admissible' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleEstablishInitiatorShape.establish_initiator_for_admissible

/--
info: 'Tacenta.UnitLifecycleEstablishInitiatorShape.counterHeadroom_parts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.rand_core_1.error.Error,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.dh.is_prime_order_public,
 tacenta_session_unit.tacenta_boundary.kem.encapsulate,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.as_bytes]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishInitiatorShape.counterHeadroom_parts

/--
info: 'Tacenta.UnitLifecycleEstablishInitiatorShape.counterHeadroom_of_established' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleEstablishInitiatorShape.counterHeadroom_of_established

/--
info: 'Tacenta.UnitLifecycleEstablishInitiatorShape.sessionRefines_parts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.tacenta_kem.encapsulate2,
 tacenta_session_unit.rand_core_1.error.Error,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.dh.is_prime_order_public,
 tacenta_session_unit.tacenta_boundary.kem.encapsulate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.header,
 tacenta_session_unit.alloc.vec.Vec.truncate,
 tacenta_session_unit.core.num.Usize.div_ceil,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.as_bytes]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishInitiatorShape.sessionRefines_parts

/--
info: 'Tacenta.UnitLifecycleEstablishInitiatorShape.sessionRefines_established' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.tacenta_kem.encapsulate2,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.rand_core_1.error.Error,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.dh.is_prime_order_public,
 tacenta_session_unit.tacenta_boundary.kem.encapsulate,
 tacenta_session_unit.tacenta_boundary.xeddsa.verify,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.header,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.alloc.vec.Vec.truncate,
 tacenta_session_unit.core.num.Usize.div_ceil,
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
#print axioms Tacenta.UnitLifecycleEstablishInitiatorShape.sessionRefines_established

/--
info: 'Tacenta.UnitLifecycleEstablishInitiatorShape.sessionRefines_parts_unique' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.tacenta_kem.encapsulate2,
 tacenta_session_unit.rand_core_1.error.Error,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.dh.is_prime_order_public,
 tacenta_session_unit.tacenta_boundary.kem.encapsulate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.header,
 tacenta_session_unit.alloc.vec.Vec.truncate,
 tacenta_session_unit.core.num.Usize.div_ceil,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.as_bytes]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishInitiatorShape.sessionRefines_parts_unique

/--
info: 'Tacenta.UnitLifecycleEstablishInitiatorShape.sessionRefines_established_unique' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.tacenta_kem.encapsulate2,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.rand_core_1.error.Error,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.dh.is_prime_order_public,
 tacenta_session_unit.tacenta_boundary.kem.encapsulate,
 tacenta_session_unit.tacenta_boundary.xeddsa.verify,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.header,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.alloc.vec.Vec.truncate,
 tacenta_session_unit.core.num.Usize.div_ceil,
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
#print axioms Tacenta.UnitLifecycleEstablishInitiatorShape.sessionRefines_established_unique

/--
info: 'Tacenta.UnitLifecycleEstablishInitiatorShape.model_initiatorSuccess' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishInitiatorShape.model_initiatorSuccess

/--
info: 'Tacenta.UnitLifecycleEstablishInitiatorShape.verify_successBundle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.dh.is_prime_order_public,
 tacenta_session_unit.tacenta_boundary.xeddsa.verify,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.as_bytes]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishInitiatorShape.verify_successBundle

/--
info: 'Tacenta.UnitLifecycleEstablishInitiatorShape.shared_secret_successBundle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.dh.is_prime_order_public,
 tacenta_session_unit.tacenta_boundary.xeddsa.verify,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.agree,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 tacenta_session_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishInitiatorShape.shared_secret_successBundle

/--
info: 'Tacenta.UnitLifecycleEstablishInitiatorShape.establish_initiator_for_succeeds' depends on axioms: [propext,
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
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishInitiatorShape.establish_initiator_for_succeeds

/--
info: 'Tacenta.UnitLifecycleEstablishInitiatorShape.established_initiator_inhabited' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleEstablishInitiatorShape.established_initiator_inhabited

/--
info: 'Tacenta.UnitLifecycleEstablishInitiatorShape.establishment_hypotheses_satisfiable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishInitiatorShape.establishment_hypotheses_satisfiable

/-- info: @Tacenta.UnitLifecycleEstablishInitiatorShape.singleton_length_le : ∀ {α : Type} (x : α), [x].length ≤ 4294967295 -/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishInitiatorShape.singleton_length_le

set_option pp.deepTerms true
set_option pp.proofs.withType true

/--
info: Tacenta.UnitLifecycleEstablishInitiatorShape.init_sender_ok : ∀ (sk : Aeneas.Std.Slice Aeneas.Std.U8)
  (a4 a5 dh : Aeneas.Std.Array Aeneas.Std.U8 32#usize) (t : tacenta_session_unit.tacenta_triple.State),
  tacenta_session_unit.tacenta_triple.State.init_sender sk a4 a5 dh
        tacenta_session_unit.tacenta_ratchet.LabelSet.Tacenta =
      Aeneas.Std.Result.ok t →
    ∃ rk cks prk c1 c2, t = Tacenta.UnitLifecycleEstablishInitiatorShape.initiatorTriple a4 a5 rk cks prk c1 c2
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishInitiatorShape.init_sender_ok

/--
info: Tacenta.UnitLifecycleEstablishInitiatorShape.braid_initiator_ok : ∀ (s : Aeneas.Std.Slice Aeneas.Std.U8)
  (b : tacenta_session_unit.tacenta_braid.Braid),
  tacenta_session_unit.tacenta_braid.Braid.initiator s = Aeneas.Std.Result.ok b →
    ∃ auth, b = { state := tacenta_session_unit.tacenta_braid.State.KeysUnsampled 1#u64 auth }
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishInitiatorShape.braid_initiator_ok

/--
info: Tacenta.UnitLifecycleEstablishInitiatorShape.verify_bundle_ok : ∀ (b : tacenta_session_unit.PreKeyBundle) (u : Unit),
  tacenta_session_unit.verify_bundle b = Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok u) →
    tacenta_session_unit.is_valid_identity_key b.identity_key = Aeneas.Std.Result.ok true
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishInitiatorShape.verify_bundle_ok

/--
info: @Tacenta.UnitLifecycleEstablishInitiatorShape.establish_initiator_for_parts : ∀ {R : Type}
  (rc : tacenta_session_unit.rand_core_1.RngCore R) (crc : tacenta_session_unit.rand_core_1.CryptoRng R)
  (our : tacenta_session_unit.lifecycle.Identity) (bundle : tacenta_session_unit.lifecycle.PublishedBundle)
  (expected : tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes) (rng0 rng1 : R)
  (s : tacenta_session_unit.lifecycle.Session),
  tacenta_session_unit.lifecycle.establish_initiator_for rc crc our bundle expected rng0 =
      Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok s, rng1) →
    ∃ p, s = p.session
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishInitiatorShape.establish_initiator_for_parts

/--
info: Tacenta.UnitLifecycleEstablishInitiatorShape.dhPublicValid_is : Tacenta.UnitLifecycleEstablishInitiatorShape.DhPublicValid ↔
  ∀ (k : tacenta_session_unit.tacenta_boundary.dh.PrivateKey)
    (pkb : tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes),
    k.public_key = Aeneas.Std.Result.ok pkb →
      ∃ a,
        pkb.as_bytes = Aeneas.Std.Result.ok a ∧
          Tacenta.SessionUnitT1.canonicalX25519 a = true ∧
            tacenta_session_unit.tacenta_boundary.dh.is_prime_order_public pkb = Aeneas.Std.Result.ok true
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishInitiatorShape.dhPublicValid_is

/--
info: Tacenta.UnitLifecycleEstablishInitiatorShape.model_dhPublicValid : Tacenta.UnitLifecycleEstablishInitiatorShape.DhPublicValidShape
  Tacenta.UnitSatisfiabilityJoint.Interp.model
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishInitiatorShape.model_dhPublicValid

/--
info: Tacenta.UnitLifecycleEstablishInitiatorShape.kemCiphertextLenOf_is : Tacenta.UnitLifecycleEstablishInitiatorShape.KemCiphertextLenOf ↔
  ∀ {R : Type} (rc : tacenta_session_unit.rand_core_1.RngCore R) (crc : tacenta_session_unit.rand_core_1.CryptoRng R)
    (pk : Aeneas.Std.Slice Aeneas.Std.U8) (rng : R) (ct : Aeneas.Std.alloc.vec.Vec Aeneas.Std.U8)
    (ss : Aeneas.Std.Array Aeneas.Std.U8 32#usize) (rng' : R),
    tacenta_session_unit.tacenta_boundary.kem.encapsulate rc crc pk rng =
        Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok (ct, ss), rng') →
      ∃ n, tacenta_session_unit.tacenta_boundary.kem.ciphertext_len = Aeneas.Std.Result.ok n ∧ (↑ct).length = ↑n
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishInitiatorShape.kemCiphertextLenOf_is

/--
info: @Tacenta.UnitLifecycleEstablishInitiatorShape.model_kemCiphertextLen : Tacenta.UnitLifecycleEstablishInitiatorShape.KemCiphertextLenLawShape
  (Aeneas.Std.Result.ok 0#usize) Tacenta.UnitSatisfiabilityJoint.Interp.model
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishInitiatorShape.model_kemCiphertextLen

/--
info: Tacenta.UnitLifecycleEstablishInitiatorShape.dhPublicValid_canonical : Tacenta.UnitLifecycleEstablishInitiatorShape.DhPublicValid →
  ∀ {k : tacenta_session_unit.tacenta_boundary.dh.PrivateKey}
    {pkb : tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes} {a : Aeneas.Std.Array Aeneas.Std.U8 32#usize},
    k.public_key = Aeneas.Std.Result.ok pkb →
      pkb.as_bytes = Aeneas.Std.Result.ok a → Tacenta.SessionUnitT1.canonicalX25519 a = true
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishInitiatorShape.dhPublicValid_canonical

/--
info: Tacenta.UnitLifecycleEstablishInitiatorShape.dhPublicValid_valid : Tacenta.UnitLifecycleEstablishInitiatorShape.DhPublicValid →
  ∀ {k : tacenta_session_unit.tacenta_boundary.dh.PrivateKey}
    {pkb : tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes},
    k.public_key = Aeneas.Std.Result.ok pkb →
      tacenta_session_unit.is_valid_identity_key pkb = Aeneas.Std.Result.ok true ∧
        tacenta_session_unit.is_canonical_key pkb = Aeneas.Std.Result.ok true
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishInitiatorShape.dhPublicValid_valid

/--
info: Tacenta.UnitLifecycleEstablishInitiatorShape.identity_public_valid : Tacenta.UnitLifecycleEstablishInitiatorShape.DhPublicValid →
  ∀ {our : tacenta_session_unit.lifecycle.Identity} {pkb : tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes},
    our.public = Aeneas.Std.Result.ok pkb → tacenta_session_unit.is_valid_identity_key pkb = Aeneas.Std.Result.ok true
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishInitiatorShape.identity_public_valid

/--
info: @Tacenta.UnitLifecycleEstablishInitiatorShape.canonical_of_is_canonical_key : ∀
  {pk : tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes} {a : Aeneas.Std.Array Aeneas.Std.U8 32#usize},
  pk.as_bytes = Aeneas.Std.Result.ok a →
    tacenta_session_unit.is_canonical_key pk = Aeneas.Std.Result.ok true →
      Tacenta.SessionUnitT1.canonicalX25519 a = true
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishInitiatorShape.canonical_of_is_canonical_key

/--
info: Tacenta.UnitLifecycleEstablishInitiatorShape.initiatorTriple_invariant : ∀
  (a4 a5 rk cks prk c1 c2 : Aeneas.Std.Array Aeneas.Std.U8 32#usize),
  Tacenta.SessionUnitT1.canonicalX25519 a4 = true →
    Tacenta.SessionUnitT1.canonicalX25519 a5 = true →
      (Tacenta.UnitLifecycleEstablishInitiatorShape.initiatorTriple a4 a5 rk cks prk c1 c2).invariant =
        Aeneas.Std.Result.ok true
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishInitiatorShape.initiatorTriple_invariant

/--
info: @Tacenta.UnitLifecycleEstablishInitiatorShape.structural_parts : ∀ {R : Type}
  {rc : tacenta_session_unit.rand_core_1.RngCore R} {crc : tacenta_session_unit.rand_core_1.CryptoRng R}
  {our : tacenta_session_unit.lifecycle.Identity} {bundle : tacenta_session_unit.lifecycle.PublishedBundle},
  Tacenta.UnitLifecycleEstablishInitiatorShape.DhPublicValid →
    Tacenta.UnitLifecycleEstablishInitiatorShape.KemCiphertextLenOf →
      Tacenta.UnitHeadroomInvariant.OptionEqU64Shape
          @tacenta_session_unit.core.option.Option.Insts.CoreCmpPartialEqOption.eq →
        ∀ (p : Tacenta.UnitLifecycleEstablishInitiatorShape.InitiatorOutputParts rc crc our bundle),
          p.session.structural_invariant = Aeneas.Std.Result.ok true
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishInitiatorShape.structural_parts

/--
info: @Tacenta.UnitLifecycleEstablishInitiatorShape.parts_invariant : ∀ {R : Type}
  {rc : tacenta_session_unit.rand_core_1.RngCore R} {crc : tacenta_session_unit.rand_core_1.CryptoRng R}
  {our : tacenta_session_unit.lifecycle.Identity} {bundle : tacenta_session_unit.lifecycle.PublishedBundle},
  Tacenta.UnitLifecycleEstablishInitiatorShape.DhPublicValid →
    Tacenta.UnitLifecycleEstablishInitiatorShape.KemCiphertextLenOf →
      Tacenta.UnitHeadroomInvariant.OptionEqU64Shape
          @tacenta_session_unit.core.option.Option.Insts.CoreCmpPartialEqOption.eq →
        ∀ (p : Tacenta.UnitLifecycleEstablishInitiatorShape.InitiatorOutputParts rc crc our bundle),
          p.session.invariant = Aeneas.Std.Result.ok true
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishInitiatorShape.parts_invariant

/--
info: @Tacenta.UnitLifecycleEstablishInitiatorShape.establish_initiator_for_admissible : ∀ {R : Type}
  (rc : tacenta_session_unit.rand_core_1.RngCore R) (crc : tacenta_session_unit.rand_core_1.CryptoRng R),
  Tacenta.UnitLifecycleEstablishInitiatorShape.DhPublicValid →
    Tacenta.UnitLifecycleEstablishInitiatorShape.KemCiphertextLenOf →
      Tacenta.UnitHeadroomInvariant.OptionEqU64Shape
          @tacenta_session_unit.core.option.Option.Insts.CoreCmpPartialEqOption.eq →
        ∀ (our : tacenta_session_unit.lifecycle.Identity) (bundle : tacenta_session_unit.lifecycle.PublishedBundle)
          (expected : tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes) (rng0 rng1 : R)
          (s : tacenta_session_unit.lifecycle.Session),
          tacenta_session_unit.lifecycle.establish_initiator_for rc crc our bundle expected rng0 =
              Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok s, rng1) →
            s.invariant = Aeneas.Std.Result.ok true
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishInitiatorShape.establish_initiator_for_admissible

/--
info: @Tacenta.UnitLifecycleEstablishInitiatorShape.counterHeadroom_parts : ∀ {R : Type}
  {rc : tacenta_session_unit.rand_core_1.RngCore R} {crc : tacenta_session_unit.rand_core_1.CryptoRng R}
  {our : tacenta_session_unit.lifecycle.Identity} {bundle : tacenta_session_unit.lifecycle.PublishedBundle}
  (p : Tacenta.UnitLifecycleEstablishInitiatorShape.InitiatorOutputParts rc crc our bundle),
  Tacenta.UnitLifecycleDecryptRunBounds.CounterHeadroom p.session
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishInitiatorShape.counterHeadroom_parts

/--
info: @Tacenta.UnitLifecycleEstablishInitiatorShape.counterHeadroom_of_established : ∀ {R : Type}
  (rc : tacenta_session_unit.rand_core_1.RngCore R) (crc : tacenta_session_unit.rand_core_1.CryptoRng R)
  (our : tacenta_session_unit.lifecycle.Identity) (bundle : tacenta_session_unit.lifecycle.PublishedBundle)
  (expected : tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes) (rng0 rng1 : R)
  (s : tacenta_session_unit.lifecycle.Session),
  tacenta_session_unit.lifecycle.establish_initiator_for rc crc our bundle expected rng0 =
      Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok s, rng1) →
    Tacenta.UnitLifecycleDecryptRunBounds.CounterHeadroom s
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishInitiatorShape.counterHeadroom_of_established

/--
info: @Tacenta.UnitLifecycleEstablishInitiatorShape.sessionRefines_parts : ∀ {R : Type}
  {rc : tacenta_session_unit.rand_core_1.RngCore R} {crc : tacenta_session_unit.rand_core_1.CryptoRng R}
  {our : tacenta_session_unit.lifecycle.Identity} {bundle : tacenta_session_unit.lifecycle.PublishedBundle}
  (dh : Tacenta.UnitLifecycleT3.DhView) (K : Model.Braid.Kem)
  (p : Tacenta.UnitLifecycleEstablishInitiatorShape.InitiatorOutputParts rc crc our bundle),
  Tacenta.UnitLifecycleT3.SessionRefines dh K p.session
    (Tacenta.UnitLifecycleEstablishInitiatorShape.establishedModelOf dh p.session)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishInitiatorShape.sessionRefines_parts

/--
info: @Tacenta.UnitLifecycleEstablishInitiatorShape.sessionRefines_established : ∀ {R : Type}
  (rc : tacenta_session_unit.rand_core_1.RngCore R) (crc : tacenta_session_unit.rand_core_1.CryptoRng R)
  (dh : Tacenta.UnitLifecycleT3.DhView) (K : Model.Braid.Kem) (our : tacenta_session_unit.lifecycle.Identity)
  (bundle : tacenta_session_unit.lifecycle.PublishedBundle)
  (expected : tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes) (rng0 rng1 : R)
  (s : tacenta_session_unit.lifecycle.Session),
  tacenta_session_unit.lifecycle.establish_initiator_for rc crc our bundle expected rng0 =
      Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok s, rng1) →
    Tacenta.UnitLifecycleT3.SessionRefines dh K s (Tacenta.UnitLifecycleEstablishInitiatorShape.establishedModelOf dh s)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishInitiatorShape.sessionRefines_established

/--
info: @Tacenta.UnitLifecycleEstablishInitiatorShape.sessionRefines_parts_unique : ∀ {R : Type}
  {rc : tacenta_session_unit.rand_core_1.RngCore R} {crc : tacenta_session_unit.rand_core_1.CryptoRng R}
  {our : tacenta_session_unit.lifecycle.Identity} {bundle : tacenta_session_unit.lifecycle.PublishedBundle}
  (dh : Tacenta.UnitLifecycleT3.DhView) (K : Model.Braid.Kem)
  (p : Tacenta.UnitLifecycleEstablishInitiatorShape.InitiatorOutputParts rc crc our bundle)
  (m : Model.Lifecycle.Session),
  Tacenta.UnitLifecycleT3.SessionRefines dh K p.session m →
    m = Tacenta.UnitLifecycleEstablishInitiatorShape.establishedModelOf dh p.session
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishInitiatorShape.sessionRefines_parts_unique

/--
info: @Tacenta.UnitLifecycleEstablishInitiatorShape.sessionRefines_established_unique : ∀ {R : Type}
  (rc : tacenta_session_unit.rand_core_1.RngCore R) (crc : tacenta_session_unit.rand_core_1.CryptoRng R)
  (dh : Tacenta.UnitLifecycleT3.DhView) (K : Model.Braid.Kem) (our : tacenta_session_unit.lifecycle.Identity)
  (bundle : tacenta_session_unit.lifecycle.PublishedBundle)
  (expected : tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes) (rng0 rng1 : R)
  (s : tacenta_session_unit.lifecycle.Session),
  tacenta_session_unit.lifecycle.establish_initiator_for rc crc our bundle expected rng0 =
      Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok s, rng1) →
    ∀ (m : Model.Lifecycle.Session),
      Tacenta.UnitLifecycleT3.SessionRefines dh K s m →
        m = Tacenta.UnitLifecycleEstablishInitiatorShape.establishedModelOf dh s
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishInitiatorShape.sessionRefines_established_unique

/--
info: @Tacenta.UnitLifecycleEstablishInitiatorShape.model_initiatorSuccess : ∀ {R : Type}
  (rc : tacenta_session_unit.rand_core_1.RngCore R) (crc : tacenta_session_unit.rand_core_1.CryptoRng R),
  Tacenta.UnitLifecycleEstablishInitiatorShape.InitiatorSuccessShape Tacenta.UnitSatisfiabilityJoint.Interp.model rc crc
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishInitiatorShape.model_initiatorSuccess

/--
info: Tacenta.UnitLifecycleEstablishInitiatorShape.verify_successBundle : ∀
  (pkb : tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes) (a : Aeneas.Std.Array Aeneas.Std.U8 32#usize),
  pkb.as_bytes = Aeneas.Std.Result.ok a →
    Tacenta.SessionUnitT1.canonicalX25519 a = true →
      tacenta_session_unit.tacenta_boundary.dh.is_prime_order_public pkb = Aeneas.Std.Result.ok true →
        ∀ (sig1 sig2 : Aeneas.Std.Array Aeneas.Std.U8 64#usize) (kem v v1 : Aeneas.Std.alloc.vec.Vec Aeneas.Std.U8),
          tacenta_session_unit.encode_ec pkb = Aeneas.Std.Result.ok v →
            tacenta_session_unit.tacenta_boundary.xeddsa.verify pkb v.deref sig1 =
                Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok ()) →
              tacenta_session_unit.encode_kem kem.deref = Aeneas.Std.Result.ok v1 →
                tacenta_session_unit.tacenta_boundary.xeddsa.verify pkb v1.deref sig2 =
                    Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok ()) →
                  tacenta_session_unit.verify_bundle
                      (Tacenta.UnitLifecycleEstablishInitiatorShape.successBundle pkb sig1 sig2 kem).bundle =
                    Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok ())
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishInitiatorShape.verify_successBundle

/--
info: Tacenta.UnitLifecycleEstablishInitiatorShape.shared_secret_successBundle : Tacenta.SessionUnitBraidT1.ZeroizingArrayRoundTrip →
  Tacenta.SessionUnitSessionT1.HkdfTotal →
    ∀ [Tacenta.SessionUnitSessionT1.ZeroizingModel] (pkb : tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes)
      (sig1 sig2 : Aeneas.Std.Array Aeneas.Std.U8 64#usize) (kem : Aeneas.Std.alloc.vec.Vec Aeneas.Std.U8),
      tacenta_session_unit.verify_bundle
            (Tacenta.UnitLifecycleEstablishInitiatorShape.successBundle pkb sig1 sig2 kem).bundle =
          Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok ()) →
        (∀ (k : tacenta_session_unit.tacenta_boundary.dh.PrivateKey),
            ∃ x, k.agree pkb = Aeneas.Std.Result.ok (some x)) →
          ∀ (ik eph : tacenta_session_unit.tacenta_boundary.dh.PrivateKey)
            (enc : Aeneas.Std.Array Aeneas.Std.U8 32#usize),
            ∃ sec,
              tacenta_session_unit.initiator_shared_secret ik eph
                  (Tacenta.UnitLifecycleEstablishInitiatorShape.successBundle pkb sig1 sig2 kem).bundle enc =
                Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok sec)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishInitiatorShape.shared_secret_successBundle

/--
info: @Tacenta.UnitLifecycleEstablishInitiatorShape.establish_initiator_for_succeeds : ∀ {R : Type}
  (rc : tacenta_session_unit.rand_core_1.RngCore R) (crc : tacenta_session_unit.rand_core_1.CryptoRng R),
  Nonempty (Tacenta.UnitSatisfiabilityJoint.InitiatorAxiom Tacenta.UnitSatisfiabilityJoint.Interp.real rc) →
    Tacenta.UnitLifecycleEstablishInitiatorShape.InitiatorSuccessShape Tacenta.UnitSatisfiabilityJoint.Interp.real rc
        crc →
      ∀ (our : tacenta_session_unit.lifecycle.Identity) (rng0 : R),
        ∃ bundle s rng1,
          tacenta_session_unit.lifecycle.establish_initiator_for rc crc our bundle bundle.bundle.identity_key rng0 =
            Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok s, rng1)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishInitiatorShape.establish_initiator_for_succeeds

/--
info: @Tacenta.UnitLifecycleEstablishInitiatorShape.established_initiator_inhabited : ∀ {R : Type}
  (rc : tacenta_session_unit.rand_core_1.RngCore R) (crc : tacenta_session_unit.rand_core_1.CryptoRng R),
  Nonempty (Tacenta.UnitSatisfiabilityJoint.InitiatorAxiom Tacenta.UnitSatisfiabilityJoint.Interp.real rc) →
    Tacenta.UnitLifecycleEstablishInitiatorShape.InitiatorSuccessShape Tacenta.UnitSatisfiabilityJoint.Interp.real rc
        crc →
      Tacenta.UnitLifecycleEstablishInitiatorShape.DhPublicValid →
        Tacenta.UnitLifecycleEstablishInitiatorShape.KemCiphertextLenOf →
          Tacenta.UnitHeadroomInvariant.OptionEqU64Shape
              @tacenta_session_unit.core.option.Option.Insts.CoreCmpPartialEqOption.eq →
            ∀ (dh : Tacenta.UnitLifecycleT3.DhView) (K : Model.Braid.Kem)
              (our : tacenta_session_unit.lifecycle.Identity) (rng0 : R),
              ∃ bundle s rng1,
                tacenta_session_unit.lifecycle.establish_initiator_for rc crc our bundle bundle.bundle.identity_key
                      rng0 =
                    Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok s, rng1) ∧
                  s.invariant = Aeneas.Std.Result.ok true ∧
                    Tacenta.UnitLifecycleDecryptRunBounds.CounterHeadroom s ∧
                      Tacenta.UnitLifecycleT3.SessionRefines dh K s
                        (Tacenta.UnitLifecycleEstablishInitiatorShape.establishedModelOf dh s)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishInitiatorShape.established_initiator_inhabited

/--
info: Tacenta.UnitLifecycleEstablishInitiatorShape.establishment_hypotheses_satisfiable : Nonempty
    (Tacenta.UnitSatisfiabilityJoint.InitiatorAxiom Tacenta.UnitSatisfiabilityJoint.Interp.model
      Tacenta.UnitLifecycleIntegrationScreen.byteRng) ∧
  Tacenta.UnitLifecycleEstablishInitiatorShape.InitiatorSuccessShape Tacenta.UnitSatisfiabilityJoint.Interp.model
      Tacenta.UnitLifecycleIntegrationScreen.byteRng Tacenta.UnitLifecycleIntegrationScreen.byteCrc ∧
    Tacenta.UnitLifecycleEstablishInitiatorShape.DhPublicValidShape Tacenta.UnitSatisfiabilityJoint.Interp.model ∧
      Tacenta.UnitLifecycleEstablishInitiatorShape.KemCiphertextLenLawShape (Aeneas.Std.Result.ok 0#usize)
          Tacenta.UnitSatisfiabilityJoint.Interp.model ∧
        Tacenta.UnitHeadroomInvariant.OptionEqU64Shape @Tacenta.UnitHeadroomInvariant.optionEqImpl
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishInitiatorShape.establishment_hypotheses_satisfiable

/--
info: def Tacenta.UnitLifecycleEstablishInitiatorShape.initChains : Aeneas.Std.Array Aeneas.Std.U8 32#usize →
  Aeneas.Std.Array Aeneas.Std.U8 32#usize →
    Aeneas.Std.alloc.vec.Vec (Aeneas.Std.U64 × tacenta_session_unit.tacenta_spqr.Chains) :=
fun c1 c2 =>
  Tacenta.UnitHeadroomSatisfiable.vecOf
    [(0#u64, { send := some { ck := c1, n := 0#u64 }, receive := some { ck := c2, n := 0#u64 } })]
    (⋯ :
      [(0#u64, { send := some { ck := c1, n := 0#u64 }, receive := some { ck := c2, n := 0#u64 } })].length ≤
        4294967295)
-/
#guard_msgs in
#print Tacenta.UnitLifecycleEstablishInitiatorShape.initChains

/--
info: def Tacenta.UnitLifecycleEstablishInitiatorShape.initiatorTriple : Aeneas.Std.Array Aeneas.Std.U8 32#usize →
  Aeneas.Std.Array Aeneas.Std.U8 32#usize →
    Aeneas.Std.Array Aeneas.Std.U8 32#usize →
      Aeneas.Std.Array Aeneas.Std.U8 32#usize →
        Aeneas.Std.Array Aeneas.Std.U8 32#usize →
          Aeneas.Std.Array Aeneas.Std.U8 32#usize →
            Aeneas.Std.Array Aeneas.Std.U8 32#usize → tacenta_session_unit.tacenta_triple.State :=
fun a4 a5 rk cks prk c1 c2 =>
  {
    classical :=
      { dhs_pub := a4, dhr_pub := some a5, rk := rk, cks := some cks, ckr := none, ns := 0#u32, nr := 0#u32,
        pn := 0#u32, skipped := Aeneas.Std.alloc.vec.Vec.new tacenta_session_unit.tacenta_ratchet.SkippedKey,
        events := 0#u32, labels := tacenta_session_unit.tacenta_ratchet.LabelSet.Tacenta },
    post_quantum :=
      { rk := prk, epoch := 0#u64, chains := Tacenta.UnitLifecycleEstablishInitiatorShape.initChains c1 c2,
        skipped := Aeneas.Std.alloc.vec.Vec.new tacenta_session_unit.tacenta_spqr.Skipped,
        direction := tacenta_session_unit.tacenta_spqr.Direction.A2b } }
-/
#guard_msgs in
#print Tacenta.UnitLifecycleEstablishInitiatorShape.initiatorTriple

/--
info: structure Tacenta.UnitLifecycleEstablishInitiatorShape.InitiatorOutputParts {R : Type}
  (rc : tacenta_session_unit.rand_core_1.RngCore R) (crc : tacenta_session_unit.rand_core_1.CryptoRng R)
  (our : tacenta_session_unit.lifecycle.Identity) (bundle : tacenta_session_unit.lifecycle.PublishedBundle) : Type
number of parameters: 5
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
constructor:
  Tacenta.UnitLifecycleEstablishInitiatorShape.InitiatorOutputParts.mk {R : Type}
    {rc : tacenta_session_unit.rand_core_1.RngCore R} {crc : tacenta_session_unit.rand_core_1.CryptoRng R}
    {our : tacenta_session_unit.lifecycle.Identity} {bundle : tacenta_session_unit.lifecycle.PublishedBundle}
    (ratchetPrivate : tacenta_session_unit.tacenta_boundary.dh.PrivateKey)
    (ratchetPublic : tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes)
    (ratchetBytes peerRatchetBytes rootKey sendChain sparseRoot sparseSend sparseReceive :
      Aeneas.Std.Array Aeneas.Std.U8 32#usize)
    (auth : tacenta_session_unit.tacenta_braid.Auth) (identityAd : Aeneas.Std.alloc.vec.Vec Aeneas.Std.U8)
    (ourPublic : tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes)
    (ephemeral : tacenta_session_unit.tacenta_boundary.dh.PrivateKey)
    (ephemeralPublic : tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes)
    (kemCiphertext : Aeneas.Std.alloc.vec.Vec Aeneas.Std.U8) (kemSecret : Aeneas.Std.Array Aeneas.Std.U8 32#usize)
    (rngBefore rngAfter : R) (hRatchetPublic : ratchetPrivate.public_key = Aeneas.Std.Result.ok ratchetPublic)
    (hRatchetBytes : ratchetPublic.as_bytes = Aeneas.Std.Result.ok ratchetBytes)
    (hPeerRatchetBytes : bundle.bundle.signed_prekey.as_bytes = Aeneas.Std.Result.ok peerRatchetBytes)
    (hPeerRatchetCanonical :
      tacenta_session_unit.is_canonical_key bundle.bundle.signed_prekey = Aeneas.Std.Result.ok true)
    (hOurPublic : our.public = Aeneas.Std.Result.ok ourPublic)
    (hIdentityAd :
      tacenta_session_unit.lifecycle.identity_ad ourPublic bundle.bundle.identity_key = Aeneas.Std.Result.ok identityAd)
    (hPeerValid : tacenta_session_unit.is_valid_identity_key bundle.bundle.identity_key = Aeneas.Std.Result.ok true)
    (hEphemeralPublic : ephemeral.public_key = Aeneas.Std.Result.ok ephemeralPublic)
    (hEncapsulate :
      tacenta_session_unit.tacenta_boundary.kem.encapsulate rc crc bundle.bundle.kem_prekey.deref rngBefore =
        Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok (kemCiphertext, kemSecret), rngAfter)) :
    Tacenta.UnitLifecycleEstablishInitiatorShape.InitiatorOutputParts rc crc our bundle
-/
#guard_msgs in
#print Tacenta.UnitLifecycleEstablishInitiatorShape.InitiatorOutputParts

/--
info: def Tacenta.UnitLifecycleEstablishInitiatorShape.InitiatorOutputParts.session : {R : Type} →
  {rc : tacenta_session_unit.rand_core_1.RngCore R} →
    {crc : tacenta_session_unit.rand_core_1.CryptoRng R} →
      {our : tacenta_session_unit.lifecycle.Identity} →
        {bundle : tacenta_session_unit.lifecycle.PublishedBundle} →
          Tacenta.UnitLifecycleEstablishInitiatorShape.InitiatorOutputParts rc crc our bundle →
            tacenta_session_unit.lifecycle.Session :=
fun {R} {rc} {crc} {our} {bundle} p =>
  {
    triple :=
      Tacenta.UnitLifecycleEstablishInitiatorShape.initiatorTriple p.ratchetBytes p.peerRatchetBytes p.rootKey
        p.sendChain p.sparseRoot p.sparseSend p.sparseReceive,
    braid := { state := tacenta_session_unit.tacenta_braid.State.KeysUnsampled 1#u64 p.auth },
    ratchet_private := p.ratchetPrivate, identity_ad := p.identityAd, our_identity_public := p.ourPublic,
    peer_identity_public := bundle.bundle.identity_key,
    pending_initial :=
      some
        { ephemeral_public := p.ephemeralPublic, kem_ciphertext := p.kemCiphertext,
          signed_prekey_id := bundle.signed_prekey_id, one_time_prekey_id := bundle.one_time_prekey_id,
          kem_prekey_id := bundle.kem_prekey_id },
    established_ephemeral := none }
-/
#guard_msgs in
#print Tacenta.UnitLifecycleEstablishInitiatorShape.InitiatorOutputParts.session

/--
info: def Tacenta.UnitLifecycleEstablishInitiatorShape.DhPublicValidShape : Tacenta.UnitSatisfiabilityJoint.Interp → Prop :=
fun I =>
  ∀ (k : I.PrivateKey) (pkb : I.PublicKeyBytes),
    I.dhPrivPublicKey k = Aeneas.Std.Result.ok pkb →
      ∃ a,
        I.dhPubAsBytes pkb = Aeneas.Std.Result.ok a ∧
          Tacenta.SessionUnitT1.canonicalX25519 a = true ∧ I.dhIsPrimeOrderPublic pkb = Aeneas.Std.Result.ok true
-/
#guard_msgs in
#print Tacenta.UnitLifecycleEstablishInitiatorShape.DhPublicValidShape

/--
info: def Tacenta.UnitLifecycleEstablishInitiatorShape.DhPublicValid : Prop :=
Tacenta.UnitLifecycleEstablishInitiatorShape.DhPublicValidShape Tacenta.UnitSatisfiabilityJoint.Interp.real
-/
#guard_msgs in
#print Tacenta.UnitLifecycleEstablishInitiatorShape.DhPublicValid

/--
info: def Tacenta.UnitLifecycleEstablishInitiatorShape.KemCiphertextLenLawShape : Aeneas.Std.Result Aeneas.Std.Usize →
  Tacenta.UnitSatisfiabilityJoint.Interp → Prop :=
fun ciphertextLen I =>
  ∀ {R : Type} (rc : tacenta_session_unit.rand_core_1.RngCore R) (crc : tacenta_session_unit.rand_core_1.CryptoRng R)
    (pk : Aeneas.Std.Slice Aeneas.Std.U8) (rng : R) (ct : Aeneas.Std.alloc.vec.Vec Aeneas.Std.U8)
    (ss : Aeneas.Std.Array Aeneas.Std.U8 32#usize) (rng' : R),
    I.kemEncapsulate rc crc pk rng = Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok (ct, ss), rng') →
      ∃ n, ciphertextLen = Aeneas.Std.Result.ok n ∧ (↑ct).length = ↑n
-/
#guard_msgs in
#print Tacenta.UnitLifecycleEstablishInitiatorShape.KemCiphertextLenLawShape

/--
info: def Tacenta.UnitLifecycleEstablishInitiatorShape.KemCiphertextLenOf : Prop :=
Tacenta.UnitLifecycleEstablishInitiatorShape.KemCiphertextLenLawShape
  tacenta_session_unit.tacenta_boundary.kem.ciphertext_len Tacenta.UnitSatisfiabilityJoint.Interp.real
-/
#guard_msgs in
#print Tacenta.UnitLifecycleEstablishInitiatorShape.KemCiphertextLenOf

/--
info: def Tacenta.UnitLifecycleEstablishInitiatorShape.unsampledModelOf : tacenta_session_unit.tacenta_braid.State →
  Model.Braid.BraidState :=
fun x =>
  match x with
  | tacenta_session_unit.tacenta_braid.State.KeysUnsampled epoch auth =>
    Model.Braid.BraidState.keysUnsampled (↑epoch) (Tacenta.SessionUnitBraidT3.AuthOf auth)
  | x => Model.Braid.BraidState.failed
-/
#guard_msgs in
#print Tacenta.UnitLifecycleEstablishInitiatorShape.unsampledModelOf

/--
info: def Tacenta.UnitLifecycleEstablishInitiatorShape.establishedModelOf : Tacenta.UnitLifecycleT3.DhView →
  tacenta_session_unit.lifecycle.Session → Model.Lifecycle.Session :=
fun dh s =>
  {
    triple :=
      { classical := Tacenta.SessionUnitTripleT3.ratchetAbs s.triple.classical,
        postQuantum := Tacenta.SessionUnitTripleT3.spqrAbs s.triple.post_quantum },
    braid := Tacenta.UnitLifecycleEstablishInitiatorShape.unsampledModelOf s.braid.state,
    ratchetPrivate := dh.privateKey s.ratchet_private, identityAd := Tacenta.UnitLifecycleT3.vecOf s.identity_ad,
    ourIdentityPublic := dh.publicKey s.our_identity_public, peerIdentityPublic := dh.publicKey s.peer_identity_public,
    pendingInitial := Option.map (Tacenta.UnitLifecycleT3.pendingInitialOf dh) s.pending_initial,
    establishedEphemeral := Option.map Tacenta.UnitLifecycleT3.vecOf s.established_ephemeral }
-/
#guard_msgs in
#print Tacenta.UnitLifecycleEstablishInitiatorShape.establishedModelOf

/--
info: structure Tacenta.UnitLifecycleEstablishInitiatorShape.InitiatorSuccessShape
  (I : Tacenta.UnitSatisfiabilityJoint.Interp) {R : Type} (rc : tacenta_session_unit.rand_core_1.RngCore R)
  (crc : tacenta_session_unit.rand_core_1.CryptoRng R) : Prop
number of parameters: 4
fields:
  Tacenta.UnitLifecycleEstablishInitiatorShape.InitiatorSuccessShape.key : ∃ pkb a,
      I.dhPubAsBytes pkb = Aeneas.Std.Result.ok a ∧
        Tacenta.SessionUnitT1.canonicalX25519 a = true ∧
          I.dhIsPrimeOrderPublic pkb = Aeneas.Std.Result.ok true ∧
            I.dhPubEq pkb pkb = Aeneas.Std.Result.ok true ∧
              (∀ (m : Aeneas.Std.Slice Aeneas.Std.U8),
                  ∃ sig, I.xeddsaVerify pkb m sig = Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok ())) ∧
                ∀ (k : I.PrivateKey), ∃ x, I.dhPrivAgree k pkb = Aeneas.Std.Result.ok (some x)
  Tacenta.UnitLifecycleEstablishInitiatorShape.InitiatorSuccessShape.kem : ∃ kemPk,
      (↑kemPk).length + 1 ≤ Aeneas.Std.Usize.max ∧
        ∀ (rng : R),
          ∃ ct ss rng',
            I.kemEncapsulate rc crc kemPk.deref rng =
              Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok (ct, ss), rng')
constructor:
  Tacenta.UnitLifecycleEstablishInitiatorShape.InitiatorSuccessShape.mk {I : Tacenta.UnitSatisfiabilityJoint.Interp}
    {R : Type} {rc : tacenta_session_unit.rand_core_1.RngCore R} {crc : tacenta_session_unit.rand_core_1.CryptoRng R}
    (key :
      ∃ pkb a,
        I.dhPubAsBytes pkb = Aeneas.Std.Result.ok a ∧
          Tacenta.SessionUnitT1.canonicalX25519 a = true ∧
            I.dhIsPrimeOrderPublic pkb = Aeneas.Std.Result.ok true ∧
              I.dhPubEq pkb pkb = Aeneas.Std.Result.ok true ∧
                (∀ (m : Aeneas.Std.Slice Aeneas.Std.U8),
                    ∃ sig, I.xeddsaVerify pkb m sig = Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok ())) ∧
                  ∀ (k : I.PrivateKey), ∃ x, I.dhPrivAgree k pkb = Aeneas.Std.Result.ok (some x))
    (kem :
      ∃ kemPk,
        (↑kemPk).length + 1 ≤ Aeneas.Std.Usize.max ∧
          ∀ (rng : R),
            ∃ ct ss rng',
              I.kemEncapsulate rc crc kemPk.deref rng =
                Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok (ct, ss), rng')) :
    Tacenta.UnitLifecycleEstablishInitiatorShape.InitiatorSuccessShape I rc crc
-/
#guard_msgs in
#print Tacenta.UnitLifecycleEstablishInitiatorShape.InitiatorSuccessShape

/--
info: def Tacenta.UnitLifecycleEstablishInitiatorShape.successBundle : tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes →
  Aeneas.Std.Array Aeneas.Std.U8 64#usize →
    Aeneas.Std.Array Aeneas.Std.U8 64#usize →
      Aeneas.Std.alloc.vec.Vec Aeneas.Std.U8 → tacenta_session_unit.lifecycle.PublishedBundle :=
fun pkb sig1 sig2 kem =>
  {
    bundle :=
      { identity_key := pkb, signed_prekey := pkb, signed_prekey_signature := sig1, kem_prekey := kem,
        kem_prekey_signature := sig2, one_time_prekey := none },
    signed_prekey_id := 0#u32, one_time_prekey_id := tacenta_session_unit.serialization.ABSENT_ID,
    kem_prekey_id := 0#u32 }
-/
#guard_msgs in
#print Tacenta.UnitLifecycleEstablishInitiatorShape.successBundle
