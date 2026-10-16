import Translation.UnitLifecycleDecryptRunBounds
import Translation.UnitHeldKemWitness
import Translation.SessionUnitDecodeEc

/-!
# Sessions that pass `Session::invariant` and are not fresh, for the decrypt refinement's hypotheses

`UnitLifecycleDecryptRunBounds.decrypt_of_invariant_hypotheses_jointly_satisfiable` shows the hypotheses of
`decrypt_ratchet_refines_of_invariant` jointly satisfiable at `UnitLifecycleDecryptScreen.invReal`, a session
over fresh states: both skipped-key stores empty, no receiving chain, the classical clock at 0, the sparse
epoch at 0 with one chain-table entry and no chain, and the Braid at epoch 1.  There the four fields of
`CounterHeadroom` are met at the least values of their counters, the sparse counter field vacuously, and the
match and store fields of `RetryRunBounds` over empty stores.  This module builds sessions that pass
`Session::invariant` with stored keys, open chains, an established ephemeral key or a pending initial
message, and counters away from zero, and restates the joint theorem at one of them.

Every state here is built for the hypotheses.  None is shown to be produced by `establish_initiator`,
`establish_responder` or `import`, or to be reached by any sequence of operations.

## The states

* `responderSession` (a responder): `established_ephemeral = some (ephemeralOf a)`, the 33 bytes `0x05 :: a`
  (the curve byte, then the canonical key `a` of the key material), and no pending initial message.  Its
  Triple (`responderTriple`) is a classical receiver with no chain and no peer key, a sparse ratchet at
  epoch 1 with one empty chain-table entry for epoch 1, direction `B2a`; its Braid (`responderBraid`) is
  `KeysUnsampled` at epoch 2, the header-sending side of an even epoch, so the Braid reports the
  responder's role.  Clauses exercised beyond the fresh session's: (b) at sparse epoch 1 and Braid epoch
  2; (c) in the responder's orientation; (d) with both halves on the responder's side; (e) and (f) on the
  `established_ephemeral` arm (`decode_ec` accepts it); the Triple's role agreement with
  `started_as_sender = some false`.
* `pendingSession` (an initiator with a pending initial message): `sessionOf` with `pending_initial =
  some (pendingOf pkb ct)`, whose ephemeral is `pkb` and whose KEM ciphertext `ct` has the length `n`
  that `kem::ciphertext_len` returns (`ctOf n`, `n` zero bytes).  Clauses exercised: (e) with the pending
  message, (f) on the ciphertext-length arm, (h) on the pending ephemeral.
* `storedSession` (stored keys and open chains): its Triple `storedTriple a 2` has a classical ratchet with
  `dhs_pub = dhr_pub = a`, both chains open, `ns = 3`, `nr = 4`, `pn = 2`, `events = 5` and one stored key
  (`dh = a`, `n = 2`, `stored_at = 4`), and a sparse ratchet at epoch 2 with one chain-table entry for
  epoch 2 holding a send chain at counter 7 and a receive chain at counter 6, one stored key (epoch 2,
  `n = 3`) and direction `A2b`; its Braid (`storedBraid`) is `KeysUnsampled` at epoch 3.  Clauses
  exercised: every clause of the classical invariant on a non-empty store (bound, clock, `stored_at <=
  events`, no two keys sharing `(dh, n)`, a receiving chain only with a sending chain and a peer key, the
  peer key and the stored key canonical); every clause of the sparse invariant on a non-empty store
  (bound, the epoch window at 2, the current epoch present, every stored key's epoch in the table, no two
  keys sharing `(epoch, n)`); (b) at sparse epoch 2 and Braid epoch 3.  With both classical chains open
  `started_as_sender` is `none`, so the Triple's role agreement holds by its `None` arm.
* `heldStoredSession`: `storedTriple a 0` beside the Braid of `UnitHeldKemWitness` (`KeysSampled` at epoch
  1, holding a generated key pair and a header encoder), so (b) at sparse epoch 0 and Braid epoch 1.

## Assumptions

`pendingSession_invariant`, `storedSession_invariant` and `heldStoredSession_invariant` take what
`UnitHeadroomInvariant.sessionOf_invariant` takes: the key material of `ValidKeyShape` as hypotheses,
`OptionEqU64Shape`, and the associated data `identity_ad` returns.  Two states take one more fact each,
both already recorded elsewhere:

* `responderSession_invariant` takes `DhCodecTotal`, for `PublicKeyBytes::from_bytes` on the key
  `decode_ec` extracts.  `DhCodecTotal` is carried by every contract record and is a field of
  `DecryptJointLaws`; `invariant_session_meets_both` already takes it.
* `pendingSession_invariant` takes `kem::ciphertext_len = ok n`, and `pending_state_exists` takes
  `KemCiphertextLenTotal` (`UnitLifecycleT1`, satisfied in `UnitSatisfiabilitySession`).
  `kem::ciphertext_len` is an opaque constant: that it returns 1568, the ML-KEM-1024 ciphertext length, is
  not stated or checked here.
* `heldStoredSession_invariant` takes the held Braid's invariant, which
  `UnitHeldKemWitness.heldBraid_invariant` gives under that module's laws.

## What is shown at the stored-key state

* `storedSession_invariant`, `storedSession_sessionRefines` (to `storedModel`, the model read off the
  session with its Braid at `keysUnsampled 3`), `storedSession_counterHeadroom`, and
  `storedSession_retryRunBounds`, which is `retryRunBounds_of_invariant` instantiated there.
* `stored_classicalMatch_tight`, `stored_sparseMatch_tight`: for a header naming the stored key, each
  store's filter has exactly one entry, so the `<= 1` bounds of `RetryRunBounds.classicalMatch` and
  `sparseMatch` are met with equality there, where at `invReal` the filters are empty.
* `decrypt_of_invariant_hypotheses_jointly_satisfiable_at_stored_keys`: under `DecryptJointLaws K dh`,
  every field of `DecryptOfInvariantHypotheses` holds together at a session with the shape
  `StoredKeysShape 2 3`, for every codeword view.  `..._at_stored_keys_held` is the same under
  `DecryptWrapperLaws dh` and `LawGenerateSucceeds` at `heldStoredSession`, with `HeldKemAt`.

## Which ceilings are exercised away from zero, and which still hold vacuously

Of the four fields of `CounterHeadroom`, at `storedSession`: `classicalEvents` at 5, `sparseEpoch` at 2,
`sparseCounters` at two chains (send counter 7, receive counter 6; at `invReal` the table holds no chain,
so the field held vacuously there), `braidEpoch` at 3.  At `heldStoredSession`: `classicalEvents` at 5
and `sparseCounters` at the same two chains; `sparseEpoch` at 0 and `braidEpoch` at 1, their least values.

Of the eleven fields of `RetryRunBounds` at `storedSession`: `classicalMatch` and `sparseMatch` are tight
for the stored keys' headers; `classicalStore` and `sparseStore` are over one key each;
`sparseSkippedEpochs` is over one key (vacuous at `invReal`); `sparseChainEpochs` and `sparseChainsRoom`
are over one entry at epoch 2; `classicalEvents`, `sparseEpoch` and `sparseCounters` as above.
`sparseOutputEpoch` still holds vacuously at the run: the derivation covers every output, but the run's
Braid receive (no agreement chunk) returns no output.  Of `DecryptRatchetRunInputs`, `chunk` and `honest`
still hold only by the arm for a message without a chunk, and `draw` is one draw.  No counter is near its
ceiling at these states: the ceilings are exercised away from zero, not at their edge
(`UnitLifecycleDecryptRunBounds.parkedSession` is the edge for the clock).

## What it does not show

* That any of these states is produced by the code, or that an operation keeps the invariant.
* A run that carries an agreement chunk at these states.
* The restated theorem at the responder or the pending state: those are shown to pass the invariant only.
* That the run reads the stored keys: the message is the first witness's, whose ratchet key is 32 zero
  bytes, so the model's step refuses at the first agreement when the oracle's agreement refuses that key
  (`UnitLifecycleDecryptScreen.invReal_model_refuses_of_agreement`), before the Triple receive.

No proof here chooses a width of `usize`.
-/

namespace Tacenta.UnitLifecycleDecryptStates

open Aeneas Aeneas.Std Result
open tacenta_session_unit
open Tacenta.UnitLifecycleT3 hiding vecOf
open Tacenta.UnitLifecycleDecryptRatchetT3
open Tacenta.UnitHeadroomSatisfiable (vecOf sessionOf pendingOf freshTriple usize_max_ge)
open Tacenta.UnitHeadroomInvariant (OptionEqU64Shape is_valid_identity_key_eq array_ne_self vec_ne_self
  is_canonical_key_eq)

/-- Thirty-two zero bytes, the chain and root keys of the states here. -/
def zeros : Array U8 32#usize := Array.repeat 32#usize 0#u8

/-- An `EncodeEC` value: the curve byte `0x05` followed by the 32 bytes of `a`, 33 bytes. -/
def ephemeralOf (a : Array U8 32#usize) : alloc.vec.Vec U8 :=
  vecOf (5#u8 :: a.val) (by simp)

/-- The model's canonicity of the key after the curve byte is the code's canonicity of `a`. -/
theorem canonicalKey_ephemeral (a : Array U8 32#usize)
    (hcan : Tacenta.SessionUnitT1.canonicalX25519 a = true) :
    Model.Messages.canonicalKey ((sliceOf (alloc.vec.Vec.deref (ephemeralOf a))).drop 1) = true := by
  have h := Tacenta.SessionUnitWireT3.canonicalKey_bytesOf a
  have h2 : Tacenta.SessionUnitWireT1.canonicalX25519 a = Tacenta.SessionUnitT1.canonicalX25519 a := by
    rw [← Tacenta.SessionUnitDecodeEc.canonicalX25519_session_eq_wire,
      Tacenta.UnitHeadroomInvariant.canonical_session_eq]
  have h3 : (sliceOf (alloc.vec.Vec.deref (ephemeralOf a))).drop 1 =
      Tacenta.SessionUnitWireT3.bytesOf a.val := by
    simp [sliceOf, ephemeralOf, vecOf, alloc.vec.Vec.deref, Tacenta.SessionUnitWireT3.bytesOf,
      Tacenta.SessionUnitWireT3.byteOf, Tacenta.SessionUnitBraidT3.u8]
  rw [h3, h, h2, hcan]

/-- `tacenta_session::decode_ec` accepts `ephemeralOf a` when `a` is canonical. -/
theorem session_decode_ec_ephemeral (a : Array U8 32#usize)
    (hcan : Tacenta.SessionUnitT1.canonicalX25519 a = true) :
    ∃ k, tacenta_session.decode_ec (alloc.vec.Vec.deref (ephemeralOf a)) = ok (some k) := by
  obtain ⟨r, hr, hnone, -⟩ :=
    Tacenta.SessionUnitDecodeEc.session_decode_ec_characterization (alloc.vec.Vec.deref (ephemeralOf a))
  cases r with
  | some k => exact ⟨k, hr⟩
  | none =>
    exfalso
    have hc := canonicalKey_ephemeral a hcan
    rcases hnone.mp rfl with h | h | h
    · apply h
      simp [sliceOf, ephemeralOf, vecOf, alloc.vec.Vec.deref]
    · apply h
      simp [sliceOf, ephemeralOf, vecOf, alloc.vec.Vec.deref, Model.Messages.ecCurveByte,
        Tacenta.SessionUnitBraidT3.u8]
    · rw [hc] at h; cases h

/-- The unit's `decode_ec` on the ephemeral returns `some`, given that `from_bytes` returns. -/
theorem decode_ec_ephemeral (hdh : Tacenta.UnitLifecycleT1.DhCodecTotal) (a : Array U8 32#usize)
    (hcan : Tacenta.SessionUnitT1.canonicalX25519 a = true) :
    ∃ q, decode_ec (alloc.vec.Vec.deref (ephemeralOf a)) = ok (some q) := by
  obtain ⟨k, hk⟩ := session_decode_ec_ephemeral a hcan
  obtain ⟨q, hq⟩ := hdh.2.2.2.1 k
  exact ⟨q, by simp [decode_ec, hk, hq]⟩

/-- The Triple of the responder state: a classical receiver with no chain and no peer key, a sparse
ratchet at epoch 1 with one empty chain-table entry for epoch 1, direction `B2a`. -/
def responderTriple (a : Array U8 32#usize) : tacenta_triple.State :=
  { classical :=
      { dhs_pub := a, dhr_pub := none, rk := zeros, cks := none, ckr := none,
        ns := 0#u32, nr := 0#u32, pn := 0#u32, skipped := vecOf [] (by simp), events := 0#u32,
        labels := tacenta_ratchet.LabelSet.Tacenta },
    post_quantum :=
      { rk := zeros, epoch := 1#u64,
        chains := vecOf [(1#u64, { send := none, receive := none })] (by simp),
        skipped := vecOf [] (by simp), direction := tacenta_spqr.Direction.B2a } }

/-- The Braid of the responder state: `KeysUnsampled` at epoch 2, the header-sending side of an even epoch,
which `Braid::is_initiator` reports as the responder's. -/
def responderBraid : tacenta_braid.Braid :=
  ⟨tacenta_braid.State.KeysUnsampled 2#u64 ⟨zeros, zeros⟩⟩

/-- **The responder state**: an established ephemeral key and no pending initial message, built for the
hypotheses, not shown produced by `establish_responder` or `import`. -/
def responderSession (k : tacenta_boundary.dh.PrivateKey) (pkb : tacenta_boundary.dh.PublicKeyBytes)
    (ad : alloc.vec.Vec U8) (a : Array U8 32#usize) : lifecycle.Session :=
  { sessionOf k pkb pkb ad a none with
    triple := responderTriple a, braid := responderBraid,
    established_ephemeral := some (ephemeralOf a) }

/-- `Session::structural_invariant` of the responder state: clauses (a) to (h), with (c) and (d) on the
responder's side and (f) on the `established_ephemeral` arm. -/
theorem structural_responderSession (hdh : Tacenta.UnitLifecycleT1.DhCodecTotal)
    (k : tacenta_boundary.dh.PrivateKey) (pkb : tacenta_boundary.dh.PublicKeyBytes)
    (a : Array U8 32#usize)
    (hpub : tacenta_boundary.dh.PrivateKey.public_key k = ok pkb)
    (hbytes : tacenta_boundary.dh.PublicKeyBytes.as_bytes pkb = ok a)
    (hcan : Tacenta.SessionUnitT1.canonicalX25519 a = true)
    (hprime : tacenta_boundary.dh.is_prime_order_public pkb = ok true)
    (hoeq : OptionEqU64Shape (@core.option.Option.Insts.CoreCmpPartialEqOption.eq))
    (ad : alloc.vec.Vec U8) (had : lifecycle.identity_ad pkb pkb = ok ad) :
    lifecycle.Session.structural_invariant (responderSession k pkb ad a) = ok true := by
  have hv := is_valid_identity_key_eq pkb a hbytes hcan hprime
  obtain ⟨q, hq⟩ := decode_ec_ephemeral hdh a hcan
  unfold lifecycle.Session.structural_invariant
  simp [responderSession, responderTriple, responderBraid, sessionOf, hpub, hbytes,
    tacenta_triple.State.sending_public, tacenta_ratchet.State.sending_public, array_ne_self,
    tacenta_braid.Braid.failed, tacenta_braid.Braid.is_initiator, tacenta_braid.State.epoch,
    lifecycle.Session.is_responder, had, vec_ne_self, tacenta_triple.State.direction,
    tacenta_spqr.State.impl.direction, hv, hq,
    tacenta_braid.Braid.epoch, tacenta_triple.State.epoch, tacenta_spqr.State.impl.epoch,
    tacenta_braid.Braid.state_tag, lift, tacenta_spqr.Direction.Insts.CoreCmpPartialEqDirection.eq]
  have h12 : U64.checked_add 1#u64 1#u64 = some 2#u64 := by decide
  have h22 : (2#u64 % 2#u64 : Result U64) = ok 0#u64 := by rfl
  rw [h12, hoeq]
  simp [h22, tacenta_spqr.Direction.read_discriminant]

/-- `Triple::invariant` of the responder Triple: both ratchets' invariants, and the roles agree
(`started_as_sender = some false`, direction `B2a`). -/
theorem responderTriple_invariant (a : Array U8 32#usize)
    (hcan : Tacenta.SessionUnitT1.canonicalX25519 a = true) :
    tacenta_triple.State.invariant (responderTriple a) = ok true := by
  have h1 : tacenta_ratchet.State.invariant (responderTriple a).classical = ok true := by
    rw [Tacenta.SessionUnitRatchetImportInv.Ratchet.invariant_true_iff]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [responderTriple, vecOf, tacenta_ratchet.MAX_SKIPPED_STORE]
    · simp [responderTriple, U32.max_eq]
    · simp [responderTriple, vecOf]
    · simp [responderTriple, vecOf]
    · simp [responderTriple]
    · simpa [responderTriple] using hcan
    · simp [responderTriple]
    · simp [responderTriple, vecOf]
  have h2 : tacenta_spqr.State.invariant (responderTriple a).post_quantum = ok true := by
    rw [Tacenta.SessionUnitRatchetImportInv.Spqr.invariant_true_iff]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [responderTriple, vecOf, tacenta_spqr.MAX_SKIPPED_STORE]
    · simp [responderTriple, vecOf, core.num.U64.saturating_add, UScalar.saturating_add,
        tacenta_spqr.EPOCHS_KEPT, U64.max_eq]
      decide
    · simp [responderTriple, vecOf]
    · simp [responderTriple, vecOf]
    · simp [responderTriple, vecOf]
    · simp [responderTriple, vecOf]
  simp only [responderTriple] at h1 h2
  unfold tacenta_triple.State.invariant
  simp [h1, h2, responderTriple, tacenta_spqr.State.impl.direction,
    tacenta_ratchet.State.started_as_sender]

/-- **`Session::invariant` accepts the responder state**, under the key material of `ValidKeyShape`,
`OptionEqU64Shape` and `DhCodecTotal`. -/
theorem responderSession_invariant (hdh : Tacenta.UnitLifecycleT1.DhCodecTotal)
    (k : tacenta_boundary.dh.PrivateKey) (pkb : tacenta_boundary.dh.PublicKeyBytes)
    (a : Array U8 32#usize)
    (hpub : tacenta_boundary.dh.PrivateKey.public_key k = ok pkb)
    (hbytes : tacenta_boundary.dh.PublicKeyBytes.as_bytes pkb = ok a)
    (hcan : Tacenta.SessionUnitT1.canonicalX25519 a = true)
    (hprime : tacenta_boundary.dh.is_prime_order_public pkb = ok true)
    (hoeq : OptionEqU64Shape (@core.option.Option.Insts.CoreCmpPartialEqOption.eq))
    (ad : alloc.vec.Vec U8) (had : lifecycle.identity_ad pkb pkb = ok ad) :
    lifecycle.Session.invariant (responderSession k pkb ad a) = ok true := by
  unfold lifecycle.Session.invariant
  rw [structural_responderSession hdh k pkb a hpub hbytes hcan hprime hoeq ad had]
  simp only [Aeneas.Std.bind_tc_ok, if_true]
  unfold lifecycle.Session.leaf_invariants
  simp only [responderSession]
  rw [responderTriple_invariant a hcan]
  simp [responderBraid, tacenta_braid.Braid.invariant]

/-- A ciphertext of `n` zero bytes. -/
def ctOf (n : Usize) : alloc.vec.Vec U8 :=
  ⟨List.replicate n.val 0#u8, by simp; scalar_tac⟩

/-- The initiator state with a pending initial message: `sessionOf` with the pending message carrying our
public key as the ephemeral and `ct` as the KEM ciphertext. -/
def pendingSession (k : tacenta_boundary.dh.PrivateKey) (pkb : tacenta_boundary.dh.PublicKeyBytes)
    (ad : alloc.vec.Vec U8) (a : Array U8 32#usize) (ct : alloc.vec.Vec U8) : lifecycle.Session :=
  sessionOf k pkb pkb ad a (some (pendingOf pkb ct))

/-- `Session::structural_invariant` of the pending initiator state: (f) on the ciphertext-length arm and
(h) on the pending ephemeral. -/
theorem structural_pendingSession
    (k : tacenta_boundary.dh.PrivateKey) (pkb : tacenta_boundary.dh.PublicKeyBytes)
    (a : Array U8 32#usize)
    (hpub : tacenta_boundary.dh.PrivateKey.public_key k = ok pkb)
    (hbytes : tacenta_boundary.dh.PublicKeyBytes.as_bytes pkb = ok a)
    (hcan : Tacenta.SessionUnitT1.canonicalX25519 a = true)
    (hprime : tacenta_boundary.dh.is_prime_order_public pkb = ok true)
    (hoeq : OptionEqU64Shape (@core.option.Option.Insts.CoreCmpPartialEqOption.eq))
    (ad : alloc.vec.Vec U8) (had : lifecycle.identity_ad pkb pkb = ok ad)
    (n : Usize) (hctl : tacenta_boundary.kem.ciphertext_len = ok n)
    (ct : alloc.vec.Vec U8) (hct : ct.val.length = n.val) :
    lifecycle.Session.structural_invariant (pendingSession k pkb ad a ct) = ok true := by
  have hv := is_valid_identity_key_eq pkb a hbytes hcan hprime
  have hc : is_canonical_key pkb = ok true := by rw [is_canonical_key_eq pkb a hbytes, hcan]
  have hlen : alloc.vec.Vec.len ct = n := by
    apply UScalar.eq_of_val_eq; simp [alloc.vec.Vec.len, hct]
  unfold lifecycle.Session.structural_invariant
  simp [pendingSession, pendingOf, sessionOf, hpub, hbytes, freshTriple,
    tacenta_triple.State.sending_public, tacenta_ratchet.State.sending_public, array_ne_self,
    Tacenta.UnitHeadroomSatisfiable.freshBraid,
    tacenta_braid.Braid.failed, tacenta_braid.Braid.is_initiator, tacenta_braid.State.epoch,
    lifecycle.Session.is_responder, had, vec_ne_self, tacenta_triple.State.direction,
    tacenta_spqr.State.impl.direction, hv, hc, hctl, hlen,
    tacenta_braid.Braid.epoch, tacenta_triple.State.epoch, tacenta_spqr.State.impl.epoch,
    tacenta_braid.Braid.state_tag, lift, tacenta_spqr.Direction.Insts.CoreCmpPartialEqDirection.eq]
  have h01 : U64.checked_add 0#u64 1#u64 = some 1#u64 := by decide
  rw [h01, hoeq]
  rfl

/-- **`Session::invariant` accepts the pending initiator state**, under the assumptions of
`sessionOf_invariant` and `kem::ciphertext_len = ok n` with the ciphertext `n` bytes long. -/
theorem pendingSession_invariant
    (k : tacenta_boundary.dh.PrivateKey) (pkb : tacenta_boundary.dh.PublicKeyBytes)
    (a : Array U8 32#usize)
    (hpub : tacenta_boundary.dh.PrivateKey.public_key k = ok pkb)
    (hbytes : tacenta_boundary.dh.PublicKeyBytes.as_bytes pkb = ok a)
    (hcan : Tacenta.SessionUnitT1.canonicalX25519 a = true)
    (hprime : tacenta_boundary.dh.is_prime_order_public pkb = ok true)
    (hoeq : OptionEqU64Shape (@core.option.Option.Insts.CoreCmpPartialEqOption.eq))
    (ad : alloc.vec.Vec U8) (had : lifecycle.identity_ad pkb pkb = ok ad)
    (n : Usize) (hctl : tacenta_boundary.kem.ciphertext_len = ok n)
    (ct : alloc.vec.Vec U8) (hct : ct.val.length = n.val) :
    lifecycle.Session.invariant (pendingSession k pkb ad a ct) = ok true := by
  unfold lifecycle.Session.invariant
  rw [structural_pendingSession k pkb a hpub hbytes hcan hprime hoeq ad had n hctl ct hct]
  simp only [Aeneas.Std.bind_tc_ok, if_true]
  unfold lifecycle.Session.leaf_invariants
  simp only [pendingSession, sessionOf]
  rw [Tacenta.UnitHeadroomInvariant.freshTriple_invariant a hcan]
  simp [Tacenta.UnitHeadroomInvariant.freshBraid_invariant]

/-- A sparse chain at message counter `n`. -/
def chainAt (n : U64) : tacenta_spqr.Chain := { ck := zeros, n := n }

/-- The Triple state with stored keys and open chains, at sparse epoch `E`. -/
def storedTriple (a : Array U8 32#usize) (E : U64) : tacenta_triple.State :=
  { classical :=
      { dhs_pub := a, dhr_pub := some a, rk := zeros, cks := some zeros, ckr := some zeros,
        ns := 3#u32, nr := 4#u32, pn := 2#u32,
        skipped := vecOf [{ dh := a, n := 2#u32, stored_at := 4#u32, key := zeros }] (by simp),
        events := 5#u32, labels := tacenta_ratchet.LabelSet.Tacenta },
    post_quantum :=
      { rk := zeros, epoch := E,
        chains := vecOf [(E, ⟨some (chainAt 7#u64), some (chainAt 6#u64)⟩)] (by simp),
        skipped := vecOf [{ epoch := E, n := 3#u64, key := zeros }] (by simp),
        direction := tacenta_spqr.Direction.A2b } }

/-- The sparse epoch window at `E`: `E < E +sat EPOCHS_KEPT` when `E + 2` fits. -/
theorem window_of (E : U64) (hE : E.val + 2 ≤ U64.max) :
    E.val < (core.num.U64.saturating_add E tacenta_spqr.EPOCHS_KEPT).val := by
  have hv : (core.num.U64.saturating_add E tacenta_spqr.EPOCHS_KEPT).val =
      min (UScalar.max UScalarTy.U64) (E.val + 2) := by
    simp only [core.num.U64.saturating_add, UScalar.saturating_add, tacenta_spqr.EPOCHS_KEPT]
    simp only [UScalar.val, BitVec.toNat_ofNat]
    apply Nat.mod_eq_of_lt
    have : UScalar.max UScalarTy.U64 < 2 ^ UScalarTy.U64.numBits := by simp [U64.max_eq]
    have h2 : (2#u64 : U64).bv.toNat = 2 := rfl
    rw [h2]
    omega
  rw [hv]
  simp only [U64.max_eq] at hE
  have : UScalar.max UScalarTy.U64 = 18446744073709551615 := by simp [U64.max_eq]
  omega

/-- **`Triple::invariant` of the stored-key Triple**, at every sparse epoch `E` with `E + 2 <= u64::MAX`:
every clause of both ratchets' invariants on a store of one key each. -/
theorem storedTriple_invariant (a : Array U8 32#usize)
    (hcan : Tacenta.SessionUnitT1.canonicalX25519 a = true) (E : U64)
    (hE : E.val + 2 ≤ U64.max) :
    tacenta_triple.State.invariant (storedTriple a E) = ok true := by
  have h1 : tacenta_ratchet.State.invariant (storedTriple a E).classical = ok true := by
    rw [Tacenta.SessionUnitRatchetImportInv.Ratchet.invariant_true_iff]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [storedTriple, vecOf, tacenta_ratchet.MAX_SKIPPED_STORE]
    · simp [storedTriple, U32.max_eq]
    · simp [storedTriple, vecOf]
    · simp [storedTriple, vecOf]
    · simp [storedTriple]
    · simpa [storedTriple] using hcan
    · simpa [storedTriple] using hcan
    · simpa [storedTriple, vecOf] using hcan
  have h2 : tacenta_spqr.State.invariant (storedTriple a E).post_quantum = ok true := by
    rw [Tacenta.SessionUnitRatchetImportInv.Spqr.invariant_true_iff]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [storedTriple, vecOf, tacenta_spqr.MAX_SKIPPED_STORE]
    · simp only [storedTriple, vecOf, List.mem_singleton, forall_eq]
      refine ⟨le_rfl, ?_⟩
      exact window_of E hE
    · simp [storedTriple, vecOf]
    · simp [storedTriple, vecOf]
    · simp [storedTriple, vecOf]
    · simp [storedTriple, vecOf]
  simp only [storedTriple] at h1 h2
  unfold tacenta_triple.State.invariant
  simp [h1, h2, storedTriple, tacenta_spqr.State.impl.direction,
    tacenta_ratchet.State.started_as_sender]

/-- The Braid of the stored-key state: `KeysUnsampled` at epoch 3, the initiator's header-sending side. -/
def storedBraid : tacenta_braid.Braid :=
  ⟨tacenta_braid.State.KeysUnsampled 3#u64 ⟨zeros, zeros⟩⟩

/-- **The stored-key state**: `sessionOf` with `storedTriple a 2` and `storedBraid`, built for the
hypotheses, not shown produced by `establish_initiator`, `establish_responder` or `import`. -/
def storedSession (k : tacenta_boundary.dh.PrivateKey) (pkb : tacenta_boundary.dh.PublicKeyBytes)
    (ad : alloc.vec.Vec U8) (a : Array U8 32#usize) : lifecycle.Session :=
  { sessionOf k pkb pkb ad a none with triple := storedTriple a 2#u64, braid := storedBraid }

/-- `Session::structural_invariant` of the stored-key state: (b) at sparse epoch 2 and Braid epoch 3, (d) at
an odd epoch on the initiator's side. -/
theorem structural_storedSession
    (k : tacenta_boundary.dh.PrivateKey) (pkb : tacenta_boundary.dh.PublicKeyBytes)
    (a : Array U8 32#usize)
    (hpub : tacenta_boundary.dh.PrivateKey.public_key k = ok pkb)
    (hbytes : tacenta_boundary.dh.PublicKeyBytes.as_bytes pkb = ok a)
    (hcan : Tacenta.SessionUnitT1.canonicalX25519 a = true)
    (hprime : tacenta_boundary.dh.is_prime_order_public pkb = ok true)
    (hoeq : OptionEqU64Shape (@core.option.Option.Insts.CoreCmpPartialEqOption.eq))
    (ad : alloc.vec.Vec U8) (had : lifecycle.identity_ad pkb pkb = ok ad) :
    lifecycle.Session.structural_invariant (storedSession k pkb ad a) = ok true := by
  have hv := is_valid_identity_key_eq pkb a hbytes hcan hprime
  unfold lifecycle.Session.structural_invariant
  simp [storedSession, storedTriple, storedBraid, sessionOf, hpub, hbytes,
    tacenta_triple.State.sending_public, tacenta_ratchet.State.sending_public, array_ne_self,
    tacenta_braid.Braid.failed, tacenta_braid.Braid.is_initiator, tacenta_braid.State.epoch,
    lifecycle.Session.is_responder, had, vec_ne_self, tacenta_triple.State.direction,
    tacenta_spqr.State.impl.direction, hv,
    tacenta_braid.Braid.epoch, tacenta_triple.State.epoch, tacenta_spqr.State.impl.epoch,
    tacenta_braid.Braid.state_tag, lift, tacenta_spqr.Direction.Insts.CoreCmpPartialEqDirection.eq]
  have h23 : U64.checked_add 2#u64 1#u64 = some 3#u64 := by decide
  have h32 : (3#u64 % 2#u64 : Result U64) = ok 1#u64 := by rfl
  rw [h23, hoeq]
  simp [h32]

/-- **`Session::invariant` accepts the stored-key state**, under the assumptions of `sessionOf_invariant`. -/
theorem storedSession_invariant
    (k : tacenta_boundary.dh.PrivateKey) (pkb : tacenta_boundary.dh.PublicKeyBytes)
    (a : Array U8 32#usize)
    (hpub : tacenta_boundary.dh.PrivateKey.public_key k = ok pkb)
    (hbytes : tacenta_boundary.dh.PublicKeyBytes.as_bytes pkb = ok a)
    (hcan : Tacenta.SessionUnitT1.canonicalX25519 a = true)
    (hprime : tacenta_boundary.dh.is_prime_order_public pkb = ok true)
    (hoeq : OptionEqU64Shape (@core.option.Option.Insts.CoreCmpPartialEqOption.eq))
    (ad : alloc.vec.Vec U8) (had : lifecycle.identity_ad pkb pkb = ok ad) :
    lifecycle.Session.invariant (storedSession k pkb ad a) = ok true := by
  unfold lifecycle.Session.invariant
  rw [structural_storedSession k pkb a hpub hbytes hcan hprime hoeq ad had]
  simp only [Aeneas.Std.bind_tc_ok, if_true]
  unfold lifecycle.Session.leaf_invariants
  simp only [storedSession]
  rw [storedTriple_invariant a hcan 2#u64 (by simp [U64.max_eq])]
  simp [storedBraid, tacenta_braid.Braid.invariant]

/-! ## The three states exist under the recorded assumptions -/

/-- **A responder state passes `Session::invariant`**, under `ValidKeyShape`, `OptionEqU64Shape` and
`DhCodecTotal`: its established ephemeral is 33 bytes, the curve byte first. -/
theorem responder_state_exists (hdh : Tacenta.UnitLifecycleT1.DhCodecTotal)
    (hv : Tacenta.UnitHeadroomInvariant.ValidKeyShape Tacenta.UnitSatisfiabilityJoint.Interp.real)
    (hoeq : OptionEqU64Shape (@core.option.Option.Insts.CoreCmpPartialEqOption.eq)) :
    ∃ real : lifecycle.Session, lifecycle.Session.invariant real = ok true ∧
      real.pending_initial = none ∧
      ∃ e, real.established_ephemeral = some e ∧ e.val.length = 33 ∧ e.val.head? = some 5#u8 := by
  obtain ⟨k, pkb, a, hpub, hbytes, hcan, hprime⟩ := hv
  obtain ⟨ad, had, -⟩ :=
    Std.WP.spec_imp_exists (Tacenta.UnitLifecycleT1.identity_ad_length hdh pkb pkb)
  exact ⟨responderSession k pkb ad a,
    responderSession_invariant hdh k pkb a hpub hbytes hcan hprime hoeq ad had, rfl,
    ephemeralOf a, rfl, by simp [ephemeralOf, vecOf], rfl⟩

/-- **An initiator state with a pending initial message passes `Session::invariant`**, under
`ValidKeyShape`, `OptionEqU64Shape`, `DhCodecTotal` and `KemCiphertextLenTotal`: the pending message's
KEM ciphertext has the length `kem::ciphertext_len` returns. -/
theorem pending_state_exists (hdh : Tacenta.UnitLifecycleT1.DhCodecTotal)
    (hv : Tacenta.UnitHeadroomInvariant.ValidKeyShape Tacenta.UnitSatisfiabilityJoint.Interp.real)
    (hoeq : OptionEqU64Shape (@core.option.Option.Insts.CoreCmpPartialEqOption.eq))
    (hct : Tacenta.UnitLifecycleT1.KemCiphertextLenTotal) :
    ∃ real : lifecycle.Session, lifecycle.Session.invariant real = ok true ∧
      real.established_ephemeral = none ∧
      ∃ p n, real.pending_initial = some p ∧ tacenta_boundary.kem.ciphertext_len = ok n ∧
        p.kem_ciphertext.val.length = n.val := by
  obtain ⟨k, pkb, a, hpub, hbytes, hcan, hprime⟩ := hv
  obtain ⟨ad, had, -⟩ :=
    Std.WP.spec_imp_exists (Tacenta.UnitLifecycleT1.identity_ad_length hdh pkb pkb)
  obtain ⟨n, hn⟩ := hct
  have hlen : (ctOf n).val.length = n.val := by simp [ctOf]
  exact ⟨pendingSession k pkb ad a (ctOf n),
    pendingSession_invariant k pkb a hpub hbytes hcan hprime hoeq ad had n hn (ctOf n) hlen, rfl,
    pendingOf pkb (ctOf n), n, rfl, hn, hlen⟩

/-! ## The stored-key state: model, relation, ceilings, run bounds -/

/-- The model session of the stored-key state: the session read off `real` (`modelOf`) with the model
Braid at `keysUnsampled 3`. -/
def storedModel (dh : DhView) (real : lifecycle.Session) : Model.Lifecycle.Session :=
  { Tacenta.UnitLifecycleDecryptRatchetScreen.modelOf dh real with
    braid := .keysUnsampled 3 Tacenta.UnitSatisfiabilityBraidStates.modelAuth0 }

/-- `SessionRefines` at the stored-key state, at every Braid KEM model: the Triple relation is the
abstraction itself, and the Braid relation in `KeysUnsampled` fixes only the epoch and the authenticator. -/
theorem storedSession_sessionRefines (K : Model.Braid.Kem) (dh : DhView) (k pkb ad a) :
    SessionRefines dh K (storedSession k pkb ad a) (storedModel dh (storedSession k pkb ad a)) :=
  ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **`CounterHeadroom` holds at the stored-key state**, with every counter it bounds away from zero. -/
theorem storedSession_counterHeadroom (k pkb ad a) :
    Tacenta.UnitLifecycleDecryptRunBounds.CounterHeadroom (storedSession k pkb ad a) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [storedSession, storedTriple, U32.max_eq]
  · simp [storedSession, storedTriple, U64.max_eq]
  · intro p hp ch hch
    simp [storedSession, storedTriple, vecOf] at hp
    subst hp
    rcases hch with h | h <;> simp at h <;> subst h <;> simp [chainAt, U64.max_eq]
  · simp only [storedSession, storedBraid, Tacenta.SessionUnitBraidT1.State.epoch_val]
    scalar_tac

/-- **`RetryRunBounds` at the stored-key state**, by `retryRunBounds_of_invariant`, for every header and
the sparse output of every Braid receive. -/
theorem storedSession_retryRunBounds (K : Model.Braid.Kem) (dh : DhView)
    (k : tacenta_boundary.dh.PrivateKey) (pkb : tacenta_boundary.dh.PublicKeyBytes)
    (a : Array U8 32#usize)
    (hpub : tacenta_boundary.dh.PrivateKey.public_key k = ok pkb)
    (hbytes : tacenta_boundary.dh.PublicKeyBytes.as_bytes pkb = ok a)
    (hcan : Tacenta.SessionUnitT1.canonicalX25519 a = true)
    (hprime : tacenta_boundary.dh.is_prime_order_public pkb = ok true)
    (hoeq : OptionEqU64Shape (@core.option.Option.Insts.CoreCmpPartialEqOption.eq))
    (ad : alloc.vec.Vec U8) (had : lifecycle.identity_ad pkb pkb = ok ad)
    (header : Model.Triple.Header) (K' : Model.Braid.Kem) (st : Model.Braid.BraidState)
    (msg : Model.Braid.Msg) :
    RetryRunBounds (storedModel dh (storedSession k pkb ad a)).triple header
      (Model.Lifecycle.sparseOutputOf (Model.Braid.receive K' st msg).2.1) :=
  Tacenta.UnitLifecycleDecryptRunBounds.retryRunBounds_of_invariant
    (storedSession_invariant k pkb a hpub hbytes hcan hprime hoeq ad had)
    (storedSession_sessionRefines K dh k pkb ad a) (storedSession_counterHeadroom k pkb ad a)
    header K' st msg

/-- **The classical match bound is tight at the stored-key state**: for a header naming the stored key's
`(dh, n)`, the model store's filter has exactly one entry, so `classicalMatch`'s `≤ 1` is met with
equality. -/
theorem stored_classicalMatch_tight (dh : DhView) (k pkb ad a) (header : Model.Triple.Header)
    (hdh : header.dr.dh = Tacenta.SessionUnitT3.keyOf a) (hn : header.dr.n = 2) :
    ((storedModel dh (storedSession k pkb ad a)).triple.classical.skipped.filter
      (fun x => x.1 == header.dr.dh && x.2.1 == header.dr.n)).length = 1 := by
  simp [storedModel, Tacenta.UnitLifecycleDecryptRatchetScreen.modelOf, storedSession, storedTriple,
    vecOf, Tacenta.SessionUnitTripleT3.ratchetAbs, Tacenta.SessionUnitT3.skippedOf, hdh, hn]

/-- **The sparse match bound is tight at the stored-key state**: for a header naming the stored sparse
key's `(epoch, n)`, the model store's filter has exactly one entry. -/
theorem stored_sparseMatch_tight (dh : DhView) (k pkb ad a) (header : Model.Triple.Header)
    (he : header.epoch = 2) (hn : header.pqN = 3) :
    ((storedModel dh (storedSession k pkb ad a)).triple.postQuantum.skipped.filter
      (fun x => x.1 == header.epoch && x.2.1 == header.pqN)).length = 1 := by
  simp [storedModel, Tacenta.UnitLifecycleDecryptRatchetScreen.modelOf, storedSession, storedTriple,
    vecOf, Tacenta.SessionUnitTripleT3.spqrAbs, Tacenta.SessionUnitSpqrT3.skippedOf, he, hn]

/-- The run conditions `DecryptRatchetRunInputs` leaves to the caller, at the stored-key state and the
first witness's message (no agreement chunk) and source. -/
theorem storedSession_runInputs (dh : DhView) (k pkb ad a) (view : Model.Lifecycle.CodewordView)
    (oracle : Model.Lifecycle.Oracle) :
    Tacenta.UnitLifecycleDecryptRunBounds.DecryptRatchetRunInputs view oracle
      Tacenta.UnitLifecycleIntegrationScreen.byteTrace (storedSession k pkb ad a)
      (storedModel dh (storedSession k pkb ad a))
      Tacenta.UnitLifecycleDecryptRatchetScreen.sampleMessage
      Tacenta.UnitLifecycleDecryptRatchetScreen.sampleRng := by
  refine ⟨?_, ?_, ⟨_, [], Tacenta.UnitLifecycleDecryptRatchetScreen.sample_trace⟩⟩
  · intro realComposite modelComposite ciphertext hdecode hcomposite
    rw [Tacenta.UnitLifecycleDecryptRatchetScreen.sample_decode_model] at hdecode
    have hmc : Tacenta.UnitLifecycleDecryptRatchetScreen.sampleComposite = modelComposite :=
      (Prod.mk.inj (Except.ok.inj hdecode)).1
    subst hmc
    have hchunk := hcomposite.agChunk
    unfold IncomingChunkRefines
    cases hr : realComposite.ag_chunk with
    | none => simp [Tacenta.UnitLifecycleDecryptRatchetScreen.sampleComposite]
    | some c => simp [hr, Tacenta.UnitLifecycleDecryptRatchetScreen.sampleComposite] at hchunk
  · intro modelComposite ciphertext hdecode
    rw [Tacenta.UnitLifecycleDecryptRatchetScreen.sample_decode_model] at hdecode
    have hmc : Tacenta.UnitLifecycleDecryptRatchetScreen.sampleComposite = modelComposite :=
      (Prod.mk.inj (Except.ok.inj hdecode)).1
    subst hmc
    intro mc hmc
    simp [Model.Lifecycle.braidMessageOf, Tacenta.UnitLifecycleDecryptRatchetScreen.sampleComposite]
      at hmc

/-! ## The restated theorem's hypotheses at the stored-key state -/

/-- What sets a session apart from one over fresh states, as facts about the translated session: one
stored key in each store, both classical chains and a peer key, a sparse chain-table entry for the
current epoch with both chains open, and the counters away from zero. -/
structure StoredKeysShape (e b : Nat) (real : lifecycle.Session) : Prop where
  classicalStored : real.triple.classical.skipped.val.length = 1
  sparseStored : real.triple.post_quantum.skipped.val.length = 1
  classicalChains : real.triple.classical.cks.isSome = true ∧ real.triple.classical.ckr.isSome = true ∧
    real.triple.classical.dhr_pub.isSome = true
  sparseChains : ∃ p ∈ real.triple.post_quantum.chains.val, p.1 = real.triple.post_quantum.epoch ∧
    p.2.send.isSome = true ∧ p.2.receive.isSome = true
  events : real.triple.classical.events.val = 5
  classicalCounters : real.triple.classical.ns.val = 3 ∧ real.triple.classical.nr.val = 4 ∧
    real.triple.classical.pn.val = 2
  sparseEpoch : real.triple.post_quantum.epoch.val = e
  braidEpoch : (Tacenta.SessionUnitBraidT1.State.epoch_val real.braid.state).val = b

/-- `storedSession` has the shape `StoredKeysShape 2 3`. -/
theorem storedSession_shape (k pkb ad a) : StoredKeysShape 2 3 (storedSession k pkb ad a) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [storedSession, storedTriple, vecOf]
  · simp [storedSession, storedTriple, vecOf]
  · simp [storedSession, storedTriple]
  · simp [storedSession, storedTriple, vecOf]
  · simp [storedSession, storedTriple]
  · simp [storedSession, storedTriple]
  · simp [storedSession, storedTriple]
  · simp [storedSession, storedBraid, Tacenta.SessionUnitBraidT1.State.epoch_val]

/-- **A session with stored keys and open chains passes `Session::invariant` and meets `CounterHeadroom`**,
under `ValidKeyShape`, `OptionEqU64Shape` and `DhCodecTotal`. -/
theorem stored_state_exists (hdh : Tacenta.UnitLifecycleT1.DhCodecTotal)
    (hv : Tacenta.UnitHeadroomInvariant.ValidKeyShape Tacenta.UnitSatisfiabilityJoint.Interp.real)
    (hoeq : OptionEqU64Shape (@core.option.Option.Insts.CoreCmpPartialEqOption.eq)) :
    ∃ real : lifecycle.Session, lifecycle.Session.invariant real = ok true ∧
      StoredKeysShape 2 3 real ∧ Tacenta.UnitLifecycleDecryptRunBounds.CounterHeadroom real := by
  obtain ⟨k, pkb, a, hpub, hbytes, hcan, hprime⟩ := hv
  obtain ⟨ad, had, -⟩ :=
    Std.WP.spec_imp_exists (Tacenta.UnitLifecycleT1.identity_ad_length hdh pkb pkb)
  exact ⟨storedSession k pkb ad a, storedSession_invariant k pkb a hpub hbytes hcan hprime hoeq ad had,
    storedSession_shape k pkb ad a, storedSession_counterHeadroom k pkb ad a⟩

/-- **Every hypothesis of `decrypt_ratchet_refines_of_invariant` at the stored-key state**, at one
explicit witness: the oracle, the laws and the agreements of
`UnitLifecycleDecryptScreen.decrypt_hypotheses_at_invReal`, the session `storedSession k pkb ad a`, its
model `storedModel`, the first witness's message and source. -/
theorem decrypt_of_invariant_hypotheses_at_stored (K : Model.Braid.Kem) (dh : DhView)
    (L : Tacenta.UnitLifecycleDecryptScreen.DecryptJointLaws K dh) (oracle : Model.Lifecycle.Oracle)
    (hK : oracle.braidKem = K)
    (hdraws : oracle.draws = Tacenta.UnitLifecycleIntegrationScreen.byteTrace
      Tacenta.UnitLifecycleDecryptRatchetScreen.sampleRng)
    (horacle : DecryptOracleOf Tacenta.UnitLifecycleIntegrationScreen.byteRng
      Tacenta.UnitLifecycleIntegrationScreen.byteCrc dh Tacenta.UnitLifecycleIntegrationScreen.byteTrace
      oracle)
    (k : tacenta_boundary.dh.PrivateKey) (pkb : tacenta_boundary.dh.PublicKeyBytes)
    (a : Array U8 32#usize)
    (hpub : tacenta_boundary.dh.PrivateKey.public_key k = ok pkb)
    (hbytes : tacenta_boundary.dh.PublicKeyBytes.as_bytes pkb = ok a)
    (hcan : Tacenta.SessionUnitT1.canonicalX25519 a = true)
    (hprime : tacenta_boundary.dh.is_prime_order_public pkb = ok true)
    (ad : alloc.vec.Vec U8) (had : lifecycle.identity_ad pkb pkb = ok ad)
    (hlen : ad.val.length = 66) (view : Model.Lifecycle.CodewordView) :
    Tacenta.UnitLifecycleDecryptRunBounds.DecryptOfInvariantHypotheses
      Tacenta.UnitLifecycleIntegrationScreen.byteRng Tacenta.UnitLifecycleIntegrationScreen.byteCrc
      Tacenta.UnitLifecycleIntegrationScreen.byteTrace dh view oracle (storedSession k pkb ad a)
      (storedModel dh (storedSession k pkb ad a)) Tacenta.UnitLifecycleDecryptRatchetScreen.sampleMessage
      Tacenta.UnitLifecycleDecryptRatchetScreen.sampleRng := by
  have h0 := Tacenta.UnitLifecycleDecryptScreen.decrypt_hypotheses_at_invReal K dh L oracle hK hdraws
    horacle k pkb a hpub hbytes hcan hprime ad had hlen view
  exact ⟨h0.oracleOf, h0.codec, h0.contracts, h0.derivedKeys, h0.agreements,
    storedSession_invariant k pkb a hpub hbytes hcan hprime L.optionEq ad had,
    hK ▸ storedSession_sessionRefines K dh k pkb ad a, storedSession_counterHeadroom k pkb ad a,
    h0.trace_eq, storedSession_runInputs dh k pkb ad a view oracle⟩

/-- **The hypotheses of `decrypt_ratchet_refines_of_invariant` hold together at a session with stored keys
and open chains, under the named laws of `UnitLifecycleDecryptScreen`.**  For every Braid KEM model `K`
and DH view `dh` meeting `DecryptJointLaws K dh`, there are an oracle with `braidKem = K`, a session that
passes `Session::invariant` and has the shape `StoredKeysShape`, a related model session, a message that
is a ratchet frame, and a source, at which every field of `DecryptOfInvariantHypotheses` holds, for every
codeword view. -/
theorem decrypt_of_invariant_hypotheses_jointly_satisfiable_at_stored_keys (K : Model.Braid.Kem)
    (dh : DhView) (L : Tacenta.UnitLifecycleDecryptScreen.DecryptJointLaws K dh) :
    ∃ (oracle : Model.Lifecycle.Oracle) (real : lifecycle.Session)
      (model : Model.Lifecycle.Session) (message : Slice Std.U8) (rng : List Std.U8),
      oracle.braidKem = K ∧ StoredKeysShape 2 3 real ∧
      Model.Lifecycle.messageType (sliceOf message) = some .ratchet ∧
      ∀ view : Model.Lifecycle.CodewordView,
        Tacenta.UnitLifecycleDecryptRunBounds.DecryptOfInvariantHypotheses
          Tacenta.UnitLifecycleIntegrationScreen.byteRng Tacenta.UnitLifecycleIntegrationScreen.byteCrc
          Tacenta.UnitLifecycleIntegrationScreen.byteTrace dh view oracle real model message rng := by
  obtain ⟨oracle, hdraws, hK, horacle⟩ :=
    Tacenta.UnitOracleDecrypt.decryptOracleOf_of_laws dh L.dhCodec L.dhAgree L.aeadOpen
      L.viewInjective
      (Tacenta.UnitLifecycleIntegrationScreen.byteTrace
        Tacenta.UnitLifecycleDecryptRatchetScreen.sampleRng) K
  obtain ⟨k, pkb, a, hpub, hbytes, hcan, hprime⟩ := L.validKey
  obtain ⟨ad, had, hlen⟩ :=
    Std.WP.spec_imp_exists (Tacenta.UnitLifecycleT1.identity_ad_length L.dhCodec pkb pkb)
  exact ⟨oracle, storedSession k pkb ad a, storedModel dh (storedSession k pkb ad a),
    Tacenta.UnitLifecycleDecryptRatchetScreen.sampleMessage,
    Tacenta.UnitLifecycleDecryptRatchetScreen.sampleRng, hK, storedSession_shape k pkb ad a,
    Tacenta.UnitLifecycleDecryptScreen.sampleMessage_type,
    fun view => decrypt_of_invariant_hypotheses_at_stored K dh L oracle hK hdraws horacle k pkb a hpub
      hbytes hcan hprime ad had hlen view⟩

/-! ## The stored-key Triple beside a Braid that holds a key pair -/

open Tacenta.UnitHeldKemWitness (heldBraid heldModel heldModelBraid hdrMsgOf HeldKemAt
  LawGenerateSucceeds)

/-- The stored-key Triple at sparse epoch 0 beside the held Braid of `UnitHeldKemWitness`
(`KeysSampled` at epoch 1, holding a generated key pair and a header encoder).  Built for the hypotheses:
as for `UnitHeldKemWitness.heldReal`, the shipped code is not shown to produce this combination of Triple
and Braid states. -/
def heldStoredSession (k : tacenta_boundary.dh.PrivateKey) (pkb : tacenta_boundary.dh.PublicKeyBytes)
    (ad : alloc.vec.Vec U8) (a : Array U8 32#usize) (kp : tacenta_kem.IncrementalKeyPair)
    (enc : tacenta_erasure.Encoder) : lifecycle.Session :=
  { sessionOf k pkb pkb ad a none with triple := storedTriple a 0#u64, braid := heldBraid kp enc }

/-- `Session::structural_invariant` of `heldStoredSession`: (b) at sparse epoch 0 and Braid epoch 1, read
off `KeysSampled` as in `UnitHeldKemWitness.structural_held`. -/
theorem structural_heldStoredSession
    (k : tacenta_boundary.dh.PrivateKey) (pkb : tacenta_boundary.dh.PublicKeyBytes)
    (a : Array U8 32#usize)
    (hpub : tacenta_boundary.dh.PrivateKey.public_key k = ok pkb)
    (hbytes : tacenta_boundary.dh.PublicKeyBytes.as_bytes pkb = ok a)
    (hcan : Tacenta.SessionUnitT1.canonicalX25519 a = true)
    (hprime : tacenta_boundary.dh.is_prime_order_public pkb = ok true)
    (hoeq : OptionEqU64Shape (@core.option.Option.Insts.CoreCmpPartialEqOption.eq))
    (ad : alloc.vec.Vec U8) (had : lifecycle.identity_ad pkb pkb = ok ad)
    (kp : tacenta_kem.IncrementalKeyPair) (enc : tacenta_erasure.Encoder) :
    lifecycle.Session.structural_invariant (heldStoredSession k pkb ad a kp enc) = ok true := by
  have hv := is_valid_identity_key_eq pkb a hbytes hcan hprime
  unfold lifecycle.Session.structural_invariant
  simp [heldStoredSession, storedTriple, sessionOf, hpub, hbytes,
    tacenta_triple.State.sending_public, tacenta_ratchet.State.sending_public, array_ne_self, heldBraid,
    tacenta_braid.Braid.failed, tacenta_braid.Braid.is_initiator, tacenta_braid.State.epoch,
    lifecycle.Session.is_responder, had, vec_ne_self, tacenta_triple.State.direction,
    tacenta_spqr.State.impl.direction, hv,
    tacenta_braid.Braid.epoch, tacenta_triple.State.epoch, tacenta_spqr.State.impl.epoch,
    tacenta_braid.Braid.state_tag, lift, tacenta_spqr.Direction.Insts.CoreCmpPartialEqDirection.eq]
  have h01 : U64.checked_add 0#u64 1#u64 = some 1#u64 := by decide
  rw [h01, hoeq]
  rfl

/-- **`Session::invariant` accepts the stored-key Triple beside the held Braid**, given the held Braid's
invariant (`UnitHeldKemWitness.heldBraid_invariant`). -/
theorem heldStoredSession_invariant
    (k : tacenta_boundary.dh.PrivateKey) (pkb : tacenta_boundary.dh.PublicKeyBytes)
    (a : Array U8 32#usize)
    (hpub : tacenta_boundary.dh.PrivateKey.public_key k = ok pkb)
    (hbytes : tacenta_boundary.dh.PublicKeyBytes.as_bytes pkb = ok a)
    (hcan : Tacenta.SessionUnitT1.canonicalX25519 a = true)
    (hprime : tacenta_boundary.dh.is_prime_order_public pkb = ok true)
    (hoeq : OptionEqU64Shape (@core.option.Option.Insts.CoreCmpPartialEqOption.eq))
    (ad : alloc.vec.Vec U8) (had : lifecycle.identity_ad pkb pkb = ok ad)
    (kp : tacenta_kem.IncrementalKeyPair) (enc : tacenta_erasure.Encoder)
    (hbraid : tacenta_braid.Braid.invariant (heldBraid kp enc) = ok true) :
    lifecycle.Session.invariant (heldStoredSession k pkb ad a kp enc) = ok true := by
  unfold lifecycle.Session.invariant
  rw [structural_heldStoredSession k pkb a hpub hbytes hcan hprime hoeq ad had kp enc]
  simp only [Aeneas.Std.bind_tc_ok, if_true]
  unfold lifecycle.Session.leaf_invariants
  simp only [heldStoredSession]
  rw [storedTriple_invariant a hcan 0#u64 (by simp [U64.max_eq])]
  simp [hbraid]

/-- `SessionRefines` at `heldStoredSession`, from `FreshKeyPairRefines` and `EncoderRefines` at the held
key pair and encoder, as `UnitHeldKemWitness.held_sessionRefines`. -/
theorem heldStoredSession_sessionRefines (K : Model.Braid.Kem) (dh : DhView) (k pkb ad a)
    (kp : tacenta_kem.IncrementalKeyPair) (enc : tacenta_erasure.Encoder) (dk ekVector header : Bytes)
    (hfresh : Tacenta.SessionUnitBraidT3.FreshKeyPairRefines K kp dk ekVector)
    (henc : Tacenta.SessionUnitBraidT3.EncoderRefines enc ⟨hdrMsgOf header, 1⟩) :
    SessionRefines dh K (heldStoredSession k pkb ad a kp enc)
      (heldModel dh (heldStoredSession k pkb ad a kp enc) dk ekVector header) :=
  ⟨⟨rfl, rfl⟩, ⟨rfl, rfl, hfresh, henc⟩, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `CounterHeadroom` at `heldStoredSession`: clock 5, chain counters 7 and 6, sparse epoch 0, Braid
epoch 1. -/
theorem heldStoredSession_counterHeadroom (k pkb ad a) (kp : tacenta_kem.IncrementalKeyPair)
    (enc : tacenta_erasure.Encoder) :
    Tacenta.UnitLifecycleDecryptRunBounds.CounterHeadroom (heldStoredSession k pkb ad a kp enc) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [heldStoredSession, storedTriple, U32.max_eq]
  · simp [heldStoredSession, storedTriple, U64.max_eq]
  · intro p hp ch hch
    simp [heldStoredSession, storedTriple, vecOf] at hp
    subst hp
    rcases hch with h | h <;> simp at h <;> subst h <;> simp [chainAt, U64.max_eq]
  · simp only [heldStoredSession, heldBraid, Tacenta.SessionUnitBraidT1.State.epoch_val]
    scalar_tac

/-- `heldStoredSession` has the shape `StoredKeysShape 0 1`. -/
theorem heldStoredSession_shape (k pkb ad a) (kp : tacenta_kem.IncrementalKeyPair)
    (enc : tacenta_erasure.Encoder) : StoredKeysShape 0 1 (heldStoredSession k pkb ad a kp enc) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [heldStoredSession, storedTriple, vecOf]
  · simp [heldStoredSession, storedTriple, vecOf]
  · simp [heldStoredSession, storedTriple]
  · simp [heldStoredSession, storedTriple, vecOf]
  · simp [heldStoredSession, storedTriple]
  · simp [heldStoredSession, storedTriple]
  · simp [heldStoredSession, storedTriple]
  · simp [heldStoredSession, heldBraid, Tacenta.SessionUnitBraidT1.State.epoch_val]

/-- The run conditions left to the caller at `heldStoredSession` and the first witness's message: the
chunk and honest fields by the arm for a message without a chunk, and one draw. -/
theorem heldStoredSession_runInputs (dh : DhView) (k pkb ad a) (kp : tacenta_kem.IncrementalKeyPair)
    (enc : tacenta_erasure.Encoder) (dk ekVector header : Bytes)
    (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle) :
    Tacenta.UnitLifecycleDecryptRunBounds.DecryptRatchetRunInputs view oracle
      Tacenta.UnitLifecycleIntegrationScreen.byteTrace (heldStoredSession k pkb ad a kp enc)
      (heldModel dh (heldStoredSession k pkb ad a kp enc) dk ekVector header)
      Tacenta.UnitLifecycleDecryptRatchetScreen.sampleMessage
      Tacenta.UnitLifecycleDecryptRatchetScreen.sampleRng := by
  refine ⟨?_, ?_, ⟨_, [], Tacenta.UnitLifecycleDecryptRatchetScreen.sample_trace⟩⟩
  · intro realComposite modelComposite ciphertext hdecode hcomposite
    rw [Tacenta.UnitLifecycleDecryptRatchetScreen.sample_decode_model] at hdecode
    have hmc : Tacenta.UnitLifecycleDecryptRatchetScreen.sampleComposite = modelComposite :=
      (Prod.mk.inj (Except.ok.inj hdecode)).1
    subst hmc
    have hchunk := hcomposite.agChunk
    unfold IncomingChunkRefines
    cases hr : realComposite.ag_chunk with
    | none => simp [Tacenta.UnitLifecycleDecryptRatchetScreen.sampleComposite]
    | some c => simp [hr, Tacenta.UnitLifecycleDecryptRatchetScreen.sampleComposite] at hchunk
  · intro modelComposite ciphertext hdecode
    rw [Tacenta.UnitLifecycleDecryptRatchetScreen.sample_decode_model] at hdecode
    have hmc : Tacenta.UnitLifecycleDecryptRatchetScreen.sampleComposite = modelComposite :=
      (Prod.mk.inj (Except.ok.inj hdecode)).1
    subst hmc
    intro mc hmc
    simp [Model.Lifecycle.braidMessageOf, Tacenta.UnitLifecycleDecryptRatchetScreen.sampleComposite]
      at hmc

/-- **The hypotheses of `decrypt_ratchet_refines_of_invariant` hold together at the stored-key Triple
beside a Braid that holds a generated key pair, with the Braid KEM model read off the wrapper.**  Under
`DecryptWrapperLaws dh` and `LawGenerateSucceeds` (the laws of
`UnitHeldKemWitness.decrypt_hypotheses_jointly_satisfiable_at_wrapperKem_held`), there are an oracle
whose Braid KEM model is `wrapperKem`, a session that passes `Session::invariant`, has the shape
`StoredKeysShape 0 1` and holds a key pair as `HeldKemAt` states, a related model session, a message that
is a ratchet frame, and a source, at which every field of `DecryptOfInvariantHypotheses` holds, for every
codeword view. -/
theorem decrypt_of_invariant_hypotheses_jointly_satisfiable_at_stored_keys_held (dh : DhView)
    (L : Tacenta.UnitKemWrapperModel.DecryptWrapperLaws dh) (G : LawGenerateSucceeds) :
    ∃ (oracle : Model.Lifecycle.Oracle) (real : lifecycle.Session)
      (model : Model.Lifecycle.Session) (message : Slice Std.U8) (rng : List Std.U8),
      oracle.braidKem = Tacenta.UnitKemWrapperModel.wrapperKem ∧ StoredKeysShape 0 1 real ∧
      HeldKemAt real model ∧
      Model.Lifecycle.messageType (sliceOf message) = some .ratchet ∧
      ∀ view : Model.Lifecycle.CodewordView,
        Tacenta.UnitLifecycleDecryptRunBounds.DecryptOfInvariantHypotheses
          Tacenta.UnitLifecycleIntegrationScreen.byteRng Tacenta.UnitLifecycleIntegrationScreen.byteCrc
          Tacenta.UnitLifecycleIntegrationScreen.byteTrace dh view oracle real model message rng := by
  obtain ⟨oracle, hdraws, hK, horacle⟩ :=
    Tacenta.UnitOracleDecrypt.decryptOracleOf_of_laws dh L.dhCodec L.dhAgree L.aeadOpen
      L.viewInjective
      (Tacenta.UnitLifecycleIntegrationScreen.byteTrace
        Tacenta.UnitLifecycleDecryptRatchetScreen.sampleRng) Tacenta.UnitKemWrapperModel.wrapperKem
  obtain ⟨k, pkb, a, hpub, hbytes, hcan, hprime⟩ := L.validKey
  obtain ⟨ad, had, hlen⟩ :=
    Std.WP.spec_imp_exists (Tacenta.UnitLifecycleT1.identity_ad_length L.dhCodec pkb pkb)
  obtain ⟨seed, kp, rest, hslen, hgen⟩ := G
  obtain ⟨h, v, hh, hv, hhl, -, hkg, hhash, hkpv, hfresh⟩ :=
    Tacenta.UnitHeldKemWitness.held_key_agreements L.kem hslen hgen
  have hdiv : Tacenta.SessionUnitDecoderBound.DivCeilValue := L.laws.divCeil
  have hea : Tacenta.SessionUnitBraidT3.ErasureAgrees :=
    Tacenta.UnitErasureRs.Glue.erasureAgrees hdiv L.truncatePrefix
  obtain ⟨-, enc, -, -, -, -, -, henc, hencinv, hsized⟩ :=
    Tacenta.UnitHeldKemWitness.held_encoder hdiv hea (hdrMsgOf (Tacenta.SessionUnitBraidT3.vecOf h))
      (Tacenta.UnitHeldKemWitness.hdrMsgOf_length _ hhl)
  have hbraid := Tacenta.UnitHeldKemWitness.heldBraid_invariant L.kem.constants.1 kp enc hencinv
    hsized hkpv
  have hsend := Tacenta.UnitHeldKemWitness.heldModelBraid_is_send
    Tacenta.UnitKemWrapperModel.wrapperKem _ _ _ _ _ hkg hhash
  rw [List.take_append_drop] at hsend
  have hinv := heldStoredSession_invariant k pkb a hpub hbytes hcan hprime L.optionEq ad had kp enc
    hbraid
  refine ⟨oracle, heldStoredSession k pkb ad a kp enc,
    heldModel dh (heldStoredSession k pkb ad a kp enc) (seed.map Tacenta.SessionUnitBraidT3.u8)
      (Tacenta.SessionUnitBraidT3.vecOf v) (Tacenta.SessionUnitBraidT3.vecOf h),
    Tacenta.UnitLifecycleDecryptRatchetScreen.sampleMessage,
    Tacenta.UnitLifecycleDecryptRatchetScreen.sampleRng, hK, heldStoredSession_shape k pkb ad a kp enc,
    ⟨seed, kp, rest, enc, h, v, hslen, hgen, hh, hv, rfl, rfl, hsend.symm⟩,
    Tacenta.UnitLifecycleDecryptScreen.sampleMessage_type, fun view => ?_⟩
  have H := Tacenta.UnitLifecycleDecryptScreen.decrypt_hypotheses_at_invReal
    Tacenta.UnitKemWrapperModel.wrapperKem dh (Tacenta.UnitKemWrapperModel.decryptWrapperLaws_joint dh L)
    oracle hK hdraws horacle k pkb a hpub hbytes hcan hprime ad had hlen view
  exact ⟨H.oracleOf, H.codec, H.contracts, H.derivedKeys, H.agreements, hinv,
    hK ▸ heldStoredSession_sessionRefines _ dh k pkb ad a kp enc _ _ _ hfresh henc,
    heldStoredSession_counterHeadroom k pkb ad a kp enc, H.trace_eq,
    heldStoredSession_runInputs dh k pkb ad a kp enc _ _ _ view oracle⟩

end Tacenta.UnitLifecycleDecryptStates

/-! ## Pins

The constants each result depends on, and the statement of each result and definition, held by the
build.  `attest.py` requires every one of them (`REQUIRED_PINS`, `REQUIRED_STATEMENT_PINS`,
`REQUIRED_PRINT_FORM`). -/

/--
info: 'Tacenta.UnitLifecycleDecryptStates.canonicalKey_ephemeral' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleDecryptStates.canonicalKey_ephemeral

/--
info: 'Tacenta.UnitLifecycleDecryptStates.session_decode_ec_ephemeral' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleDecryptStates.session_decode_ec_ephemeral

/--
info: 'Tacenta.UnitLifecycleDecryptStates.decode_ec_ephemeral' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleDecryptStates.decode_ec_ephemeral

/--
info: 'Tacenta.UnitLifecycleDecryptStates.structural_responderSession' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleDecryptStates.structural_responderSession

/--
info: 'Tacenta.UnitLifecycleDecryptStates.responderTriple_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleDecryptStates.responderTriple_invariant

/--
info: 'Tacenta.UnitLifecycleDecryptStates.responderSession_invariant' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleDecryptStates.responderSession_invariant

/--
info: 'Tacenta.UnitLifecycleDecryptStates.structural_pendingSession' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleDecryptStates.structural_pendingSession

/--
info: 'Tacenta.UnitLifecycleDecryptStates.pendingSession_invariant' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleDecryptStates.pendingSession_invariant

/--
info: 'Tacenta.UnitLifecycleDecryptStates.window_of' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleDecryptStates.window_of

/--
info: 'Tacenta.UnitLifecycleDecryptStates.storedTriple_invariant' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleDecryptStates.storedTriple_invariant

/--
info: 'Tacenta.UnitLifecycleDecryptStates.structural_storedSession' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleDecryptStates.structural_storedSession

/--
info: 'Tacenta.UnitLifecycleDecryptStates.storedSession_invariant' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleDecryptStates.storedSession_invariant

/--
info: 'Tacenta.UnitLifecycleDecryptStates.responder_state_exists' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleDecryptStates.responder_state_exists

/--
info: 'Tacenta.UnitLifecycleDecryptStates.pending_state_exists' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleDecryptStates.pending_state_exists

/--
info: 'Tacenta.UnitLifecycleDecryptStates.storedSession_sessionRefines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.tacenta_kem.encapsulate2,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.header,
 tacenta_session_unit.alloc.vec.Vec.truncate,
 tacenta_session_unit.core.num.Usize.div_ceil]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleDecryptStates.storedSession_sessionRefines

/--
info: 'Tacenta.UnitLifecycleDecryptStates.storedSession_counterHeadroom' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleDecryptStates.storedSession_counterHeadroom

/--
info: 'Tacenta.UnitLifecycleDecryptStates.storedSession_retryRunBounds' depends on axioms: [propext,
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
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.dh.is_prime_order_public,
 tacenta_session_unit.tacenta_boundary.kem.ciphertext_len,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.header,
 tacenta_session_unit.alloc.vec.Vec.truncate,
 tacenta_session_unit.core.num.Usize.div_ceil,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 tacenta_session_unit.core.option.Option.Insts.CoreCmpPartialEqOption.eq]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleDecryptStates.storedSession_retryRunBounds

/--
info: 'Tacenta.UnitLifecycleDecryptStates.stored_classicalMatch_tight' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleDecryptStates.stored_classicalMatch_tight

/--
info: 'Tacenta.UnitLifecycleDecryptStates.stored_sparseMatch_tight' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleDecryptStates.stored_sparseMatch_tight

/--
info: 'Tacenta.UnitLifecycleDecryptStates.storedSession_runInputs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.core.num.Usize.div_ceil]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleDecryptStates.storedSession_runInputs

/--
info: 'Tacenta.UnitLifecycleDecryptStates.storedSession_shape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleDecryptStates.storedSession_shape

/--
info: 'Tacenta.UnitLifecycleDecryptStates.stored_state_exists' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleDecryptStates.stored_state_exists

/--
info: 'Tacenta.UnitLifecycleDecryptStates.decrypt_of_invariant_hypotheses_at_stored' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleDecryptStates.decrypt_of_invariant_hypotheses_at_stored

/--
info: 'Tacenta.UnitLifecycleDecryptStates.decrypt_of_invariant_hypotheses_jointly_satisfiable_at_stored_keys' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleDecryptStates.decrypt_of_invariant_hypotheses_jointly_satisfiable_at_stored_keys

/--
info: 'Tacenta.UnitLifecycleDecryptStates.structural_heldStoredSession' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleDecryptStates.structural_heldStoredSession

/--
info: 'Tacenta.UnitLifecycleDecryptStates.heldStoredSession_invariant' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleDecryptStates.heldStoredSession_invariant

/--
info: 'Tacenta.UnitLifecycleDecryptStates.heldStoredSession_sessionRefines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.tacenta_kem.encapsulate2,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.header,
 tacenta_session_unit.alloc.vec.Vec.truncate,
 tacenta_session_unit.core.num.Usize.div_ceil]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleDecryptStates.heldStoredSession_sessionRefines

/--
info: 'Tacenta.UnitLifecycleDecryptStates.heldStoredSession_counterHeadroom' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleDecryptStates.heldStoredSession_counterHeadroom

/--
info: 'Tacenta.UnitLifecycleDecryptStates.heldStoredSession_shape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleDecryptStates.heldStoredSession_shape

/--
info: 'Tacenta.UnitLifecycleDecryptStates.heldStoredSession_runInputs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.core.num.Usize.div_ceil]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleDecryptStates.heldStoredSession_runInputs

/--
info: 'Tacenta.UnitLifecycleDecryptStates.decrypt_of_invariant_hypotheses_jointly_satisfiable_at_stored_keys_held' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleDecryptStates.decrypt_of_invariant_hypotheses_jointly_satisfiable_at_stored_keys_held

/--
info: Tacenta.UnitLifecycleDecryptStates.canonicalKey_ephemeral : ∀ (a : Aeneas.Std.Array Aeneas.Std.U8 32#usize),
  Tacenta.SessionUnitT1.canonicalX25519 a = true →
    Model.Messages.canonicalKey
        (List.drop 1 (Tacenta.UnitLifecycleT3.sliceOf (Tacenta.UnitLifecycleDecryptStates.ephemeralOf a).deref)) =
      true
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptStates.canonicalKey_ephemeral

/--
info: Tacenta.UnitLifecycleDecryptStates.session_decode_ec_ephemeral : ∀ (a : Aeneas.Std.Array Aeneas.Std.U8 32#usize),
  Tacenta.SessionUnitT1.canonicalX25519 a = true →
    ∃ k,
      tacenta_session_unit.tacenta_session.decode_ec (Tacenta.UnitLifecycleDecryptStates.ephemeralOf a).deref =
        Aeneas.Std.Result.ok (some k)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptStates.session_decode_ec_ephemeral

/--
info: Tacenta.UnitLifecycleDecryptStates.decode_ec_ephemeral : Tacenta.UnitLifecycleT1.DhCodecTotal →
  ∀ (a : Aeneas.Std.Array Aeneas.Std.U8 32#usize),
    Tacenta.SessionUnitT1.canonicalX25519 a = true →
      ∃ q,
        tacenta_session_unit.decode_ec (Tacenta.UnitLifecycleDecryptStates.ephemeralOf a).deref =
          Aeneas.Std.Result.ok (some q)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptStates.decode_ec_ephemeral

/--
info: Tacenta.UnitLifecycleDecryptStates.structural_responderSession : Tacenta.UnitLifecycleT1.DhCodecTotal →
  ∀ (k : tacenta_session_unit.tacenta_boundary.dh.PrivateKey)
    (pkb : tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes) (a : Aeneas.Std.Array Aeneas.Std.U8 32#usize),
    k.public_key = Aeneas.Std.Result.ok pkb →
      pkb.as_bytes = Aeneas.Std.Result.ok a →
        Tacenta.SessionUnitT1.canonicalX25519 a = true →
          tacenta_session_unit.tacenta_boundary.dh.is_prime_order_public pkb = Aeneas.Std.Result.ok true →
            Tacenta.UnitHeadroomInvariant.OptionEqU64Shape
                @tacenta_session_unit.core.option.Option.Insts.CoreCmpPartialEqOption.eq →
              ∀ (ad : Aeneas.Std.alloc.vec.Vec Aeneas.Std.U8),
                tacenta_session_unit.lifecycle.identity_ad pkb pkb = Aeneas.Std.Result.ok ad →
                  (Tacenta.UnitLifecycleDecryptStates.responderSession k pkb ad a).structural_invariant =
                    Aeneas.Std.Result.ok true
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptStates.structural_responderSession

/--
info: Tacenta.UnitLifecycleDecryptStates.responderTriple_invariant : ∀ (a : Aeneas.Std.Array Aeneas.Std.U8 32#usize),
  Tacenta.SessionUnitT1.canonicalX25519 a = true →
    (Tacenta.UnitLifecycleDecryptStates.responderTriple a).invariant = Aeneas.Std.Result.ok true
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptStates.responderTriple_invariant

/--
info: Tacenta.UnitLifecycleDecryptStates.responderSession_invariant : Tacenta.UnitLifecycleT1.DhCodecTotal →
  ∀ (k : tacenta_session_unit.tacenta_boundary.dh.PrivateKey)
    (pkb : tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes) (a : Aeneas.Std.Array Aeneas.Std.U8 32#usize),
    k.public_key = Aeneas.Std.Result.ok pkb →
      pkb.as_bytes = Aeneas.Std.Result.ok a →
        Tacenta.SessionUnitT1.canonicalX25519 a = true →
          tacenta_session_unit.tacenta_boundary.dh.is_prime_order_public pkb = Aeneas.Std.Result.ok true →
            Tacenta.UnitHeadroomInvariant.OptionEqU64Shape
                @tacenta_session_unit.core.option.Option.Insts.CoreCmpPartialEqOption.eq →
              ∀ (ad : Aeneas.Std.alloc.vec.Vec Aeneas.Std.U8),
                tacenta_session_unit.lifecycle.identity_ad pkb pkb = Aeneas.Std.Result.ok ad →
                  (Tacenta.UnitLifecycleDecryptStates.responderSession k pkb ad a).invariant = Aeneas.Std.Result.ok true
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptStates.responderSession_invariant

/--
info: Tacenta.UnitLifecycleDecryptStates.structural_pendingSession : ∀
  (k : tacenta_session_unit.tacenta_boundary.dh.PrivateKey)
  (pkb : tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes) (a : Aeneas.Std.Array Aeneas.Std.U8 32#usize),
  k.public_key = Aeneas.Std.Result.ok pkb →
    pkb.as_bytes = Aeneas.Std.Result.ok a →
      Tacenta.SessionUnitT1.canonicalX25519 a = true →
        tacenta_session_unit.tacenta_boundary.dh.is_prime_order_public pkb = Aeneas.Std.Result.ok true →
          Tacenta.UnitHeadroomInvariant.OptionEqU64Shape
              @tacenta_session_unit.core.option.Option.Insts.CoreCmpPartialEqOption.eq →
            ∀ (ad : Aeneas.Std.alloc.vec.Vec Aeneas.Std.U8),
              tacenta_session_unit.lifecycle.identity_ad pkb pkb = Aeneas.Std.Result.ok ad →
                ∀ (n : Aeneas.Std.Usize),
                  tacenta_session_unit.tacenta_boundary.kem.ciphertext_len = Aeneas.Std.Result.ok n →
                    ∀ (ct : Aeneas.Std.alloc.vec.Vec Aeneas.Std.U8),
                      (↑ct).length = ↑n →
                        (Tacenta.UnitLifecycleDecryptStates.pendingSession k pkb ad a ct).structural_invariant =
                          Aeneas.Std.Result.ok true
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptStates.structural_pendingSession

/--
info: Tacenta.UnitLifecycleDecryptStates.pendingSession_invariant : ∀
  (k : tacenta_session_unit.tacenta_boundary.dh.PrivateKey)
  (pkb : tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes) (a : Aeneas.Std.Array Aeneas.Std.U8 32#usize),
  k.public_key = Aeneas.Std.Result.ok pkb →
    pkb.as_bytes = Aeneas.Std.Result.ok a →
      Tacenta.SessionUnitT1.canonicalX25519 a = true →
        tacenta_session_unit.tacenta_boundary.dh.is_prime_order_public pkb = Aeneas.Std.Result.ok true →
          Tacenta.UnitHeadroomInvariant.OptionEqU64Shape
              @tacenta_session_unit.core.option.Option.Insts.CoreCmpPartialEqOption.eq →
            ∀ (ad : Aeneas.Std.alloc.vec.Vec Aeneas.Std.U8),
              tacenta_session_unit.lifecycle.identity_ad pkb pkb = Aeneas.Std.Result.ok ad →
                ∀ (n : Aeneas.Std.Usize),
                  tacenta_session_unit.tacenta_boundary.kem.ciphertext_len = Aeneas.Std.Result.ok n →
                    ∀ (ct : Aeneas.Std.alloc.vec.Vec Aeneas.Std.U8),
                      (↑ct).length = ↑n →
                        (Tacenta.UnitLifecycleDecryptStates.pendingSession k pkb ad a ct).invariant =
                          Aeneas.Std.Result.ok true
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptStates.pendingSession_invariant

/--
info: Tacenta.UnitLifecycleDecryptStates.window_of : ∀ (E : Aeneas.Std.U64),
  ↑E + 2 ≤ Aeneas.Std.U64.max →
    ↑E < ↑(Aeneas.Std.core.num.U64.saturating_add E tacenta_session_unit.tacenta_spqr.EPOCHS_KEPT)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptStates.window_of

/--
info: Tacenta.UnitLifecycleDecryptStates.storedTriple_invariant : ∀ (a : Aeneas.Std.Array Aeneas.Std.U8 32#usize),
  Tacenta.SessionUnitT1.canonicalX25519 a = true →
    ∀ (E : Aeneas.Std.U64),
      ↑E + 2 ≤ Aeneas.Std.U64.max →
        (Tacenta.UnitLifecycleDecryptStates.storedTriple a E).invariant = Aeneas.Std.Result.ok true
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptStates.storedTriple_invariant

/--
info: Tacenta.UnitLifecycleDecryptStates.structural_storedSession : ∀
  (k : tacenta_session_unit.tacenta_boundary.dh.PrivateKey)
  (pkb : tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes) (a : Aeneas.Std.Array Aeneas.Std.U8 32#usize),
  k.public_key = Aeneas.Std.Result.ok pkb →
    pkb.as_bytes = Aeneas.Std.Result.ok a →
      Tacenta.SessionUnitT1.canonicalX25519 a = true →
        tacenta_session_unit.tacenta_boundary.dh.is_prime_order_public pkb = Aeneas.Std.Result.ok true →
          Tacenta.UnitHeadroomInvariant.OptionEqU64Shape
              @tacenta_session_unit.core.option.Option.Insts.CoreCmpPartialEqOption.eq →
            ∀ (ad : Aeneas.Std.alloc.vec.Vec Aeneas.Std.U8),
              tacenta_session_unit.lifecycle.identity_ad pkb pkb = Aeneas.Std.Result.ok ad →
                (Tacenta.UnitLifecycleDecryptStates.storedSession k pkb ad a).structural_invariant =
                  Aeneas.Std.Result.ok true
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptStates.structural_storedSession

/--
info: Tacenta.UnitLifecycleDecryptStates.storedSession_invariant : ∀ (k : tacenta_session_unit.tacenta_boundary.dh.PrivateKey)
  (pkb : tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes) (a : Aeneas.Std.Array Aeneas.Std.U8 32#usize),
  k.public_key = Aeneas.Std.Result.ok pkb →
    pkb.as_bytes = Aeneas.Std.Result.ok a →
      Tacenta.SessionUnitT1.canonicalX25519 a = true →
        tacenta_session_unit.tacenta_boundary.dh.is_prime_order_public pkb = Aeneas.Std.Result.ok true →
          Tacenta.UnitHeadroomInvariant.OptionEqU64Shape
              @tacenta_session_unit.core.option.Option.Insts.CoreCmpPartialEqOption.eq →
            ∀ (ad : Aeneas.Std.alloc.vec.Vec Aeneas.Std.U8),
              tacenta_session_unit.lifecycle.identity_ad pkb pkb = Aeneas.Std.Result.ok ad →
                (Tacenta.UnitLifecycleDecryptStates.storedSession k pkb ad a).invariant = Aeneas.Std.Result.ok true
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptStates.storedSession_invariant

/--
info: Tacenta.UnitLifecycleDecryptStates.responder_state_exists : Tacenta.UnitLifecycleT1.DhCodecTotal →
  Tacenta.UnitHeadroomInvariant.ValidKeyShape Tacenta.UnitSatisfiabilityJoint.Interp.real →
    Tacenta.UnitHeadroomInvariant.OptionEqU64Shape
        @tacenta_session_unit.core.option.Option.Insts.CoreCmpPartialEqOption.eq →
      ∃ real,
        real.invariant = Aeneas.Std.Result.ok true ∧
          real.pending_initial = none ∧
            ∃ e, real.established_ephemeral = some e ∧ (↑e).length = 33 ∧ (↑e).head? = some 5#u8
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptStates.responder_state_exists

/--
info: Tacenta.UnitLifecycleDecryptStates.pending_state_exists : Tacenta.UnitLifecycleT1.DhCodecTotal →
  Tacenta.UnitHeadroomInvariant.ValidKeyShape Tacenta.UnitSatisfiabilityJoint.Interp.real →
    Tacenta.UnitHeadroomInvariant.OptionEqU64Shape
        @tacenta_session_unit.core.option.Option.Insts.CoreCmpPartialEqOption.eq →
      Tacenta.UnitLifecycleT1.KemCiphertextLenTotal →
        ∃ real,
          real.invariant = Aeneas.Std.Result.ok true ∧
            real.established_ephemeral = none ∧
              ∃ p n,
                real.pending_initial = some p ∧
                  tacenta_session_unit.tacenta_boundary.kem.ciphertext_len = Aeneas.Std.Result.ok n ∧
                    (↑p.kem_ciphertext).length = ↑n
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptStates.pending_state_exists

/--
info: Tacenta.UnitLifecycleDecryptStates.storedSession_sessionRefines : ∀ (K : Model.Braid.Kem)
  (dh : Tacenta.UnitLifecycleT3.DhView) (k : tacenta_session_unit.tacenta_boundary.dh.PrivateKey)
  (pkb : tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes) (ad : Aeneas.Std.alloc.vec.Vec Aeneas.Std.U8)
  (a : Aeneas.Std.Array Aeneas.Std.U8 32#usize),
  Tacenta.UnitLifecycleT3.SessionRefines dh K (Tacenta.UnitLifecycleDecryptStates.storedSession k pkb ad a)
    (Tacenta.UnitLifecycleDecryptStates.storedModel dh (Tacenta.UnitLifecycleDecryptStates.storedSession k pkb ad a))
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptStates.storedSession_sessionRefines

/--
info: Tacenta.UnitLifecycleDecryptStates.storedSession_counterHeadroom : ∀
  (k : tacenta_session_unit.tacenta_boundary.dh.PrivateKey)
  (pkb : tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes) (ad : Aeneas.Std.alloc.vec.Vec Aeneas.Std.U8)
  (a : Aeneas.Std.Array Aeneas.Std.U8 32#usize),
  Tacenta.UnitLifecycleDecryptRunBounds.CounterHeadroom (Tacenta.UnitLifecycleDecryptStates.storedSession k pkb ad a)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptStates.storedSession_counterHeadroom

/--
info: Tacenta.UnitLifecycleDecryptStates.storedSession_retryRunBounds : ∀ (K : Model.Braid.Kem)
  (dh : Tacenta.UnitLifecycleT3.DhView) (k : tacenta_session_unit.tacenta_boundary.dh.PrivateKey)
  (pkb : tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes) (a : Aeneas.Std.Array Aeneas.Std.U8 32#usize),
  k.public_key = Aeneas.Std.Result.ok pkb →
    pkb.as_bytes = Aeneas.Std.Result.ok a →
      Tacenta.SessionUnitT1.canonicalX25519 a = true →
        tacenta_session_unit.tacenta_boundary.dh.is_prime_order_public pkb = Aeneas.Std.Result.ok true →
          Tacenta.UnitHeadroomInvariant.OptionEqU64Shape
              @tacenta_session_unit.core.option.Option.Insts.CoreCmpPartialEqOption.eq →
            ∀ (ad : Aeneas.Std.alloc.vec.Vec Aeneas.Std.U8),
              tacenta_session_unit.lifecycle.identity_ad pkb pkb = Aeneas.Std.Result.ok ad →
                ∀ (header : Model.Triple.Header) (K' : Model.Braid.Kem) (st : Model.Braid.BraidState)
                  (msg : Model.Braid.Msg),
                  Tacenta.UnitLifecycleDecryptRatchetT3.RetryRunBounds
                    (Tacenta.UnitLifecycleDecryptStates.storedModel dh
                        (Tacenta.UnitLifecycleDecryptStates.storedSession k pkb ad a)).triple
                    header (Model.Lifecycle.sparseOutputOf (Model.Braid.receive K' st msg).2.1)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptStates.storedSession_retryRunBounds

/--
info: Tacenta.UnitLifecycleDecryptStates.stored_classicalMatch_tight : ∀ (dh : Tacenta.UnitLifecycleT3.DhView)
  (k : tacenta_session_unit.tacenta_boundary.dh.PrivateKey)
  (pkb : tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes) (ad : Aeneas.Std.alloc.vec.Vec Aeneas.Std.U8)
  (a : Aeneas.Std.Array Aeneas.Std.U8 32#usize) (header : Model.Triple.Header),
  header.dr.dh = Tacenta.SessionUnitT3.keyOf a →
    header.dr.n = 2 →
      (List.filter (fun x => x.1 == header.dr.dh && x.2.1 == header.dr.n)
            (Tacenta.UnitLifecycleDecryptStates.storedModel dh
                    (Tacenta.UnitLifecycleDecryptStates.storedSession k pkb ad a)).triple.classical.skipped).length =
        1
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptStates.stored_classicalMatch_tight

/--
info: Tacenta.UnitLifecycleDecryptStates.stored_sparseMatch_tight : ∀ (dh : Tacenta.UnitLifecycleT3.DhView)
  (k : tacenta_session_unit.tacenta_boundary.dh.PrivateKey)
  (pkb : tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes) (ad : Aeneas.Std.alloc.vec.Vec Aeneas.Std.U8)
  (a : Aeneas.Std.Array Aeneas.Std.U8 32#usize) (header : Model.Triple.Header),
  header.epoch = 2 →
    header.pqN = 3 →
      (List.filter (fun x => x.1 == header.epoch && x.2.1 == header.pqN)
            (Tacenta.UnitLifecycleDecryptStates.storedModel dh
                    (Tacenta.UnitLifecycleDecryptStates.storedSession k pkb ad a)).triple.postQuantum.skipped).length =
        1
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptStates.stored_sparseMatch_tight

/--
info: Tacenta.UnitLifecycleDecryptStates.storedSession_runInputs : ∀ (dh : Tacenta.UnitLifecycleT3.DhView)
  (k : tacenta_session_unit.tacenta_boundary.dh.PrivateKey)
  (pkb : tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes) (ad : Aeneas.Std.alloc.vec.Vec Aeneas.Std.U8)
  (a : Aeneas.Std.Array Aeneas.Std.U8 32#usize) (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle),
  Tacenta.UnitLifecycleDecryptRunBounds.DecryptRatchetRunInputs view oracle
    Tacenta.UnitLifecycleIntegrationScreen.byteTrace (Tacenta.UnitLifecycleDecryptStates.storedSession k pkb ad a)
    (Tacenta.UnitLifecycleDecryptStates.storedModel dh (Tacenta.UnitLifecycleDecryptStates.storedSession k pkb ad a))
    Tacenta.UnitLifecycleDecryptRatchetScreen.sampleMessage Tacenta.UnitLifecycleDecryptRatchetScreen.sampleRng
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptStates.storedSession_runInputs

/--
info: Tacenta.UnitLifecycleDecryptStates.storedSession_shape : ∀ (k : tacenta_session_unit.tacenta_boundary.dh.PrivateKey)
  (pkb : tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes) (ad : Aeneas.Std.alloc.vec.Vec Aeneas.Std.U8)
  (a : Aeneas.Std.Array Aeneas.Std.U8 32#usize),
  Tacenta.UnitLifecycleDecryptStates.StoredKeysShape 2 3 (Tacenta.UnitLifecycleDecryptStates.storedSession k pkb ad a)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptStates.storedSession_shape

/--
info: Tacenta.UnitLifecycleDecryptStates.stored_state_exists : Tacenta.UnitLifecycleT1.DhCodecTotal →
  Tacenta.UnitHeadroomInvariant.ValidKeyShape Tacenta.UnitSatisfiabilityJoint.Interp.real →
    Tacenta.UnitHeadroomInvariant.OptionEqU64Shape
        @tacenta_session_unit.core.option.Option.Insts.CoreCmpPartialEqOption.eq →
      ∃ real,
        real.invariant = Aeneas.Std.Result.ok true ∧
          Tacenta.UnitLifecycleDecryptStates.StoredKeysShape 2 3 real ∧
            Tacenta.UnitLifecycleDecryptRunBounds.CounterHeadroom real
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptStates.stored_state_exists

/--
info: Tacenta.UnitLifecycleDecryptStates.decrypt_of_invariant_hypotheses_at_stored : ∀ (K : Model.Braid.Kem)
  (dh : Tacenta.UnitLifecycleT3.DhView),
  Tacenta.UnitLifecycleDecryptScreen.DecryptJointLaws K dh →
    ∀ (oracle : Model.Lifecycle.Oracle),
      oracle.braidKem = K →
        oracle.draws =
            Tacenta.UnitLifecycleIntegrationScreen.byteTrace Tacenta.UnitLifecycleDecryptRatchetScreen.sampleRng →
          Tacenta.UnitLifecycleDecryptRatchetT3.DecryptOracleOf Tacenta.UnitLifecycleIntegrationScreen.byteRng
              Tacenta.UnitLifecycleIntegrationScreen.byteCrc dh Tacenta.UnitLifecycleIntegrationScreen.byteTrace
              oracle →
            ∀ (k : tacenta_session_unit.tacenta_boundary.dh.PrivateKey)
              (pkb : tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes)
              (a : Aeneas.Std.Array Aeneas.Std.U8 32#usize),
              k.public_key = Aeneas.Std.Result.ok pkb →
                pkb.as_bytes = Aeneas.Std.Result.ok a →
                  Tacenta.SessionUnitT1.canonicalX25519 a = true →
                    tacenta_session_unit.tacenta_boundary.dh.is_prime_order_public pkb = Aeneas.Std.Result.ok true →
                      ∀ (ad : Aeneas.Std.alloc.vec.Vec Aeneas.Std.U8),
                        tacenta_session_unit.lifecycle.identity_ad pkb pkb = Aeneas.Std.Result.ok ad →
                          (↑ad).length = 66 →
                            ∀ (view : Model.Lifecycle.CodewordView),
                              Tacenta.UnitLifecycleDecryptRunBounds.DecryptOfInvariantHypotheses
                                Tacenta.UnitLifecycleIntegrationScreen.byteRng
                                Tacenta.UnitLifecycleIntegrationScreen.byteCrc
                                Tacenta.UnitLifecycleIntegrationScreen.byteTrace dh view oracle
                                (Tacenta.UnitLifecycleDecryptStates.storedSession k pkb ad a)
                                (Tacenta.UnitLifecycleDecryptStates.storedModel dh
                                  (Tacenta.UnitLifecycleDecryptStates.storedSession k pkb ad a))
                                Tacenta.UnitLifecycleDecryptRatchetScreen.sampleMessage
                                Tacenta.UnitLifecycleDecryptRatchetScreen.sampleRng
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptStates.decrypt_of_invariant_hypotheses_at_stored

/--
info: Tacenta.UnitLifecycleDecryptStates.decrypt_of_invariant_hypotheses_jointly_satisfiable_at_stored_keys : ∀
  (K : Model.Braid.Kem) (dh : Tacenta.UnitLifecycleT3.DhView),
  Tacenta.UnitLifecycleDecryptScreen.DecryptJointLaws K dh →
    ∃ oracle real model message rng,
      oracle.braidKem = K ∧
        Tacenta.UnitLifecycleDecryptStates.StoredKeysShape 2 3 real ∧
          Model.Lifecycle.messageType (Tacenta.UnitLifecycleT3.sliceOf message) =
              some Model.Lifecycle.MessageType.ratchet ∧
            ∀ (view : Model.Lifecycle.CodewordView),
              Tacenta.UnitLifecycleDecryptRunBounds.DecryptOfInvariantHypotheses
                Tacenta.UnitLifecycleIntegrationScreen.byteRng Tacenta.UnitLifecycleIntegrationScreen.byteCrc
                Tacenta.UnitLifecycleIntegrationScreen.byteTrace dh view oracle real model message rng
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptStates.decrypt_of_invariant_hypotheses_jointly_satisfiable_at_stored_keys

/--
info: Tacenta.UnitLifecycleDecryptStates.structural_heldStoredSession : ∀
  (k : tacenta_session_unit.tacenta_boundary.dh.PrivateKey)
  (pkb : tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes) (a : Aeneas.Std.Array Aeneas.Std.U8 32#usize),
  k.public_key = Aeneas.Std.Result.ok pkb →
    pkb.as_bytes = Aeneas.Std.Result.ok a →
      Tacenta.SessionUnitT1.canonicalX25519 a = true →
        tacenta_session_unit.tacenta_boundary.dh.is_prime_order_public pkb = Aeneas.Std.Result.ok true →
          Tacenta.UnitHeadroomInvariant.OptionEqU64Shape
              @tacenta_session_unit.core.option.Option.Insts.CoreCmpPartialEqOption.eq →
            ∀ (ad : Aeneas.Std.alloc.vec.Vec Aeneas.Std.U8),
              tacenta_session_unit.lifecycle.identity_ad pkb pkb = Aeneas.Std.Result.ok ad →
                ∀ (kp : tacenta_session_unit.tacenta_kem.IncrementalKeyPair)
                  (enc : tacenta_session_unit.tacenta_erasure.Encoder),
                  (Tacenta.UnitLifecycleDecryptStates.heldStoredSession k pkb ad a kp enc).structural_invariant =
                    Aeneas.Std.Result.ok true
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptStates.structural_heldStoredSession

/--
info: Tacenta.UnitLifecycleDecryptStates.heldStoredSession_invariant : ∀
  (k : tacenta_session_unit.tacenta_boundary.dh.PrivateKey)
  (pkb : tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes) (a : Aeneas.Std.Array Aeneas.Std.U8 32#usize),
  k.public_key = Aeneas.Std.Result.ok pkb →
    pkb.as_bytes = Aeneas.Std.Result.ok a →
      Tacenta.SessionUnitT1.canonicalX25519 a = true →
        tacenta_session_unit.tacenta_boundary.dh.is_prime_order_public pkb = Aeneas.Std.Result.ok true →
          Tacenta.UnitHeadroomInvariant.OptionEqU64Shape
              @tacenta_session_unit.core.option.Option.Insts.CoreCmpPartialEqOption.eq →
            ∀ (ad : Aeneas.Std.alloc.vec.Vec Aeneas.Std.U8),
              tacenta_session_unit.lifecycle.identity_ad pkb pkb = Aeneas.Std.Result.ok ad →
                ∀ (kp : tacenta_session_unit.tacenta_kem.IncrementalKeyPair)
                  (enc : tacenta_session_unit.tacenta_erasure.Encoder),
                  (Tacenta.UnitHeldKemWitness.heldBraid kp enc).invariant = Aeneas.Std.Result.ok true →
                    (Tacenta.UnitLifecycleDecryptStates.heldStoredSession k pkb ad a kp enc).invariant =
                      Aeneas.Std.Result.ok true
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptStates.heldStoredSession_invariant

/--
info: Tacenta.UnitLifecycleDecryptStates.heldStoredSession_sessionRefines : ∀ (K : Model.Braid.Kem)
  (dh : Tacenta.UnitLifecycleT3.DhView) (k : tacenta_session_unit.tacenta_boundary.dh.PrivateKey)
  (pkb : tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes) (ad : Aeneas.Std.alloc.vec.Vec Aeneas.Std.U8)
  (a : Aeneas.Std.Array Aeneas.Std.U8 32#usize) (kp : tacenta_session_unit.tacenta_kem.IncrementalKeyPair)
  (enc : tacenta_session_unit.tacenta_erasure.Encoder) (dk ekVector header : Tacenta.UnitLifecycleT3.Bytes),
  Tacenta.SessionUnitBraidT3.FreshKeyPairRefines K kp dk ekVector →
    Tacenta.SessionUnitBraidT3.EncoderRefines enc { source := Tacenta.UnitHeldKemWitness.hdrMsgOf header, next := 1 } →
      Tacenta.UnitLifecycleT3.SessionRefines dh K
        (Tacenta.UnitLifecycleDecryptStates.heldStoredSession k pkb ad a kp enc)
        (Tacenta.UnitHeldKemWitness.heldModel dh
          (Tacenta.UnitLifecycleDecryptStates.heldStoredSession k pkb ad a kp enc) dk ekVector header)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptStates.heldStoredSession_sessionRefines

/--
info: Tacenta.UnitLifecycleDecryptStates.heldStoredSession_counterHeadroom : ∀
  (k : tacenta_session_unit.tacenta_boundary.dh.PrivateKey)
  (pkb : tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes) (ad : Aeneas.Std.alloc.vec.Vec Aeneas.Std.U8)
  (a : Aeneas.Std.Array Aeneas.Std.U8 32#usize) (kp : tacenta_session_unit.tacenta_kem.IncrementalKeyPair)
  (enc : tacenta_session_unit.tacenta_erasure.Encoder),
  Tacenta.UnitLifecycleDecryptRunBounds.CounterHeadroom
    (Tacenta.UnitLifecycleDecryptStates.heldStoredSession k pkb ad a kp enc)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptStates.heldStoredSession_counterHeadroom

/--
info: Tacenta.UnitLifecycleDecryptStates.heldStoredSession_shape : ∀ (k : tacenta_session_unit.tacenta_boundary.dh.PrivateKey)
  (pkb : tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes) (ad : Aeneas.Std.alloc.vec.Vec Aeneas.Std.U8)
  (a : Aeneas.Std.Array Aeneas.Std.U8 32#usize) (kp : tacenta_session_unit.tacenta_kem.IncrementalKeyPair)
  (enc : tacenta_session_unit.tacenta_erasure.Encoder),
  Tacenta.UnitLifecycleDecryptStates.StoredKeysShape 0 1
    (Tacenta.UnitLifecycleDecryptStates.heldStoredSession k pkb ad a kp enc)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptStates.heldStoredSession_shape

/--
info: Tacenta.UnitLifecycleDecryptStates.heldStoredSession_runInputs : ∀ (dh : Tacenta.UnitLifecycleT3.DhView)
  (k : tacenta_session_unit.tacenta_boundary.dh.PrivateKey)
  (pkb : tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes) (ad : Aeneas.Std.alloc.vec.Vec Aeneas.Std.U8)
  (a : Aeneas.Std.Array Aeneas.Std.U8 32#usize) (kp : tacenta_session_unit.tacenta_kem.IncrementalKeyPair)
  (enc : tacenta_session_unit.tacenta_erasure.Encoder) (dk ekVector header : Tacenta.UnitLifecycleT3.Bytes)
  (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle),
  Tacenta.UnitLifecycleDecryptRunBounds.DecryptRatchetRunInputs view oracle
    Tacenta.UnitLifecycleIntegrationScreen.byteTrace
    (Tacenta.UnitLifecycleDecryptStates.heldStoredSession k pkb ad a kp enc)
    (Tacenta.UnitHeldKemWitness.heldModel dh (Tacenta.UnitLifecycleDecryptStates.heldStoredSession k pkb ad a kp enc) dk
      ekVector header)
    Tacenta.UnitLifecycleDecryptRatchetScreen.sampleMessage Tacenta.UnitLifecycleDecryptRatchetScreen.sampleRng
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptStates.heldStoredSession_runInputs

/--
info: Tacenta.UnitLifecycleDecryptStates.decrypt_of_invariant_hypotheses_jointly_satisfiable_at_stored_keys_held : ∀
  (dh : Tacenta.UnitLifecycleT3.DhView),
  Tacenta.UnitKemWrapperModel.DecryptWrapperLaws dh →
    Tacenta.UnitHeldKemWitness.LawGenerateSucceeds →
      ∃ oracle real model message rng,
        oracle.braidKem = Tacenta.UnitKemWrapperModel.wrapperKem ∧
          Tacenta.UnitLifecycleDecryptStates.StoredKeysShape 0 1 real ∧
            Tacenta.UnitHeldKemWitness.HeldKemAt real model ∧
              Model.Lifecycle.messageType (Tacenta.UnitLifecycleT3.sliceOf message) =
                  some Model.Lifecycle.MessageType.ratchet ∧
                ∀ (view : Model.Lifecycle.CodewordView),
                  Tacenta.UnitLifecycleDecryptRunBounds.DecryptOfInvariantHypotheses
                    Tacenta.UnitLifecycleIntegrationScreen.byteRng Tacenta.UnitLifecycleIntegrationScreen.byteCrc
                    Tacenta.UnitLifecycleIntegrationScreen.byteTrace dh view oracle real model message rng
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptStates.decrypt_of_invariant_hypotheses_jointly_satisfiable_at_stored_keys_held

/--
info: def Tacenta.UnitLifecycleDecryptStates.zeros : Aeneas.Std.Array Aeneas.Std.U8 32#usize :=
Aeneas.Std.Array.repeat 32#usize 0#u8
-/
#guard_msgs in
#print Tacenta.UnitLifecycleDecryptStates.zeros

/--
info: def Tacenta.UnitLifecycleDecryptStates.ephemeralOf : Aeneas.Std.Array Aeneas.Std.U8 32#usize →
  Aeneas.Std.alloc.vec.Vec Aeneas.Std.U8 :=
fun a => Tacenta.UnitHeadroomSatisfiable.vecOf (5#u8 :: ↑a) ⋯
-/
#guard_msgs in
#print Tacenta.UnitLifecycleDecryptStates.ephemeralOf

/--
info: def Tacenta.UnitLifecycleDecryptStates.responderTriple : Aeneas.Std.Array Aeneas.Std.U8 32#usize →
  tacenta_session_unit.tacenta_triple.State :=
fun a =>
  {
    classical :=
      { dhs_pub := a, dhr_pub := none, rk := Tacenta.UnitLifecycleDecryptStates.zeros, cks := none, ckr := none,
        ns := 0#u32, nr := 0#u32, pn := 0#u32,
        skipped := Tacenta.UnitHeadroomSatisfiable.vecOf [] Tacenta.UnitLifecycleDecryptStates.responderTriple._proof_2,
        events := 0#u32, labels := tacenta_session_unit.tacenta_ratchet.LabelSet.Tacenta },
    post_quantum :=
      { rk := Tacenta.UnitLifecycleDecryptStates.zeros, epoch := 1#u64,
        chains :=
          Tacenta.UnitHeadroomSatisfiable.vecOf [(1#u64, { send := none, receive := none })]
            Tacenta.UnitLifecycleDecryptStates.responderTriple._proof_4,
        skipped := Tacenta.UnitHeadroomSatisfiable.vecOf [] Tacenta.UnitLifecycleDecryptStates.responderTriple._proof_2,
        direction := tacenta_session_unit.tacenta_spqr.Direction.B2a } }
-/
#guard_msgs in
#print Tacenta.UnitLifecycleDecryptStates.responderTriple

/--
info: def Tacenta.UnitLifecycleDecryptStates.responderBraid : tacenta_session_unit.tacenta_braid.Braid :=
{
  state :=
    tacenta_session_unit.tacenta_braid.State.KeysUnsampled 2#u64
      { root_key := Tacenta.UnitLifecycleDecryptStates.zeros, mac_key := Tacenta.UnitLifecycleDecryptStates.zeros } }
-/
#guard_msgs in
#print Tacenta.UnitLifecycleDecryptStates.responderBraid

/--
info: def Tacenta.UnitLifecycleDecryptStates.responderSession : tacenta_session_unit.tacenta_boundary.dh.PrivateKey →
  tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes →
    Aeneas.Std.alloc.vec.Vec Aeneas.Std.U8 →
      Aeneas.Std.Array Aeneas.Std.U8 32#usize → tacenta_session_unit.lifecycle.Session :=
fun k pkb ad a =>
  have __src := Tacenta.UnitHeadroomSatisfiable.sessionOf k pkb pkb ad a none;
  { triple := Tacenta.UnitLifecycleDecryptStates.responderTriple a,
    braid := Tacenta.UnitLifecycleDecryptStates.responderBraid, ratchet_private := __src.ratchet_private,
    identity_ad := __src.identity_ad, our_identity_public := __src.our_identity_public,
    peer_identity_public := __src.peer_identity_public, pending_initial := __src.pending_initial,
    established_ephemeral := some (Tacenta.UnitLifecycleDecryptStates.ephemeralOf a) }
-/
#guard_msgs in
#print Tacenta.UnitLifecycleDecryptStates.responderSession

/--
info: def Tacenta.UnitLifecycleDecryptStates.ctOf : Aeneas.Std.Usize → Aeneas.Std.alloc.vec.Vec Aeneas.Std.U8 :=
fun n => ⟨List.replicate (↑n) 0#u8, ⋯⟩
-/
#guard_msgs in
#print Tacenta.UnitLifecycleDecryptStates.ctOf

/--
info: def Tacenta.UnitLifecycleDecryptStates.pendingSession : tacenta_session_unit.tacenta_boundary.dh.PrivateKey →
  tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes →
    Aeneas.Std.alloc.vec.Vec Aeneas.Std.U8 →
      Aeneas.Std.Array Aeneas.Std.U8 32#usize →
        Aeneas.Std.alloc.vec.Vec Aeneas.Std.U8 → tacenta_session_unit.lifecycle.Session :=
fun k pkb ad a ct =>
  Tacenta.UnitHeadroomSatisfiable.sessionOf k pkb pkb ad a (some (Tacenta.UnitHeadroomSatisfiable.pendingOf pkb ct))
-/
#guard_msgs in
#print Tacenta.UnitLifecycleDecryptStates.pendingSession

/--
info: def Tacenta.UnitLifecycleDecryptStates.chainAt : Aeneas.Std.U64 → tacenta_session_unit.tacenta_spqr.Chain :=
fun n => { ck := Tacenta.UnitLifecycleDecryptStates.zeros, n := n }
-/
#guard_msgs in
#print Tacenta.UnitLifecycleDecryptStates.chainAt

/--
info: def Tacenta.UnitLifecycleDecryptStates.storedTriple : Aeneas.Std.Array Aeneas.Std.U8 32#usize →
  Aeneas.Std.U64 → tacenta_session_unit.tacenta_triple.State :=
fun a E =>
  {
    classical :=
      { dhs_pub := a, dhr_pub := some a, rk := Tacenta.UnitLifecycleDecryptStates.zeros,
        cks := some Tacenta.UnitLifecycleDecryptStates.zeros, ckr := some Tacenta.UnitLifecycleDecryptStates.zeros,
        ns := 3#u32, nr := 4#u32, pn := 2#u32,
        skipped :=
          Tacenta.UnitHeadroomSatisfiable.vecOf
            [{ dh := a, n := 2#u32, stored_at := 4#u32, key := Tacenta.UnitLifecycleDecryptStates.zeros }] ⋯,
        events := 5#u32, labels := tacenta_session_unit.tacenta_ratchet.LabelSet.Tacenta },
    post_quantum :=
      { rk := Tacenta.UnitLifecycleDecryptStates.zeros, epoch := E,
        chains :=
          Tacenta.UnitHeadroomSatisfiable.vecOf
            [(E,
                { send := some (Tacenta.UnitLifecycleDecryptStates.chainAt 7#u64),
                  receive := some (Tacenta.UnitLifecycleDecryptStates.chainAt 6#u64) })]
            ⋯,
        skipped :=
          Tacenta.UnitHeadroomSatisfiable.vecOf
            [{ epoch := E, n := 3#u64, key := Tacenta.UnitLifecycleDecryptStates.zeros }] ⋯,
        direction := tacenta_session_unit.tacenta_spqr.Direction.A2b } }
-/
#guard_msgs in
#print Tacenta.UnitLifecycleDecryptStates.storedTriple

/--
info: def Tacenta.UnitLifecycleDecryptStates.storedBraid : tacenta_session_unit.tacenta_braid.Braid :=
{
  state :=
    tacenta_session_unit.tacenta_braid.State.KeysUnsampled 3#u64
      { root_key := Tacenta.UnitLifecycleDecryptStates.zeros, mac_key := Tacenta.UnitLifecycleDecryptStates.zeros } }
-/
#guard_msgs in
#print Tacenta.UnitLifecycleDecryptStates.storedBraid

/--
info: def Tacenta.UnitLifecycleDecryptStates.storedSession : tacenta_session_unit.tacenta_boundary.dh.PrivateKey →
  tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes →
    Aeneas.Std.alloc.vec.Vec Aeneas.Std.U8 →
      Aeneas.Std.Array Aeneas.Std.U8 32#usize → tacenta_session_unit.lifecycle.Session :=
fun k pkb ad a =>
  have __src := Tacenta.UnitHeadroomSatisfiable.sessionOf k pkb pkb ad a none;
  { triple := Tacenta.UnitLifecycleDecryptStates.storedTriple a 2#u64,
    braid := Tacenta.UnitLifecycleDecryptStates.storedBraid, ratchet_private := __src.ratchet_private,
    identity_ad := __src.identity_ad, our_identity_public := __src.our_identity_public,
    peer_identity_public := __src.peer_identity_public, pending_initial := __src.pending_initial,
    established_ephemeral := __src.established_ephemeral }
-/
#guard_msgs in
#print Tacenta.UnitLifecycleDecryptStates.storedSession

/--
info: def Tacenta.UnitLifecycleDecryptStates.storedModel : Tacenta.UnitLifecycleT3.DhView →
  tacenta_session_unit.lifecycle.Session → Model.Lifecycle.Session :=
fun dh real =>
  have __src := Tacenta.UnitLifecycleDecryptRatchetScreen.modelOf dh real;
  { triple := __src.triple,
    braid := Model.Braid.BraidState.keysUnsampled 3 Tacenta.UnitSatisfiabilityBraidStates.modelAuth0,
    ratchetPrivate := __src.ratchetPrivate, identityAd := __src.identityAd,
    ourIdentityPublic := __src.ourIdentityPublic, peerIdentityPublic := __src.peerIdentityPublic,
    pendingInitial := __src.pendingInitial, establishedEphemeral := __src.establishedEphemeral }
-/
#guard_msgs in
#print Tacenta.UnitLifecycleDecryptStates.storedModel

/--
info: structure Tacenta.UnitLifecycleDecryptStates.StoredKeysShape (e b : ℕ) (real : tacenta_session_unit.lifecycle.Session) :
  Prop
number of parameters: 3
fields:
  Tacenta.UnitLifecycleDecryptStates.StoredKeysShape.classicalStored : (↑real.triple.classical.skipped).length = 1
  Tacenta.UnitLifecycleDecryptStates.StoredKeysShape.sparseStored : (↑real.triple.post_quantum.skipped).length = 1
  Tacenta.UnitLifecycleDecryptStates.StoredKeysShape.classicalChains : real.triple.classical.cks.isSome = true ∧
      real.triple.classical.ckr.isSome = true ∧ real.triple.classical.dhr_pub.isSome = true
  Tacenta.UnitLifecycleDecryptStates.StoredKeysShape.sparseChains : ∃ p ∈ ↑real.triple.post_quantum.chains,
      p.1 = real.triple.post_quantum.epoch ∧ p.2.send.isSome = true ∧ p.2.receive.isSome = true
  Tacenta.UnitLifecycleDecryptStates.StoredKeysShape.events : ↑real.triple.classical.events = 5
  Tacenta.UnitLifecycleDecryptStates.StoredKeysShape.classicalCounters : ↑real.triple.classical.ns = 3 ∧
      ↑real.triple.classical.nr = 4 ∧ ↑real.triple.classical.pn = 2
  Tacenta.UnitLifecycleDecryptStates.StoredKeysShape.sparseEpoch : ↑real.triple.post_quantum.epoch = e
  Tacenta.UnitLifecycleDecryptStates.StoredKeysShape.braidEpoch : ↑(Tacenta.SessionUnitBraidT1.State.epoch_val
          real.braid.state) =
      b
constructor:
  Tacenta.UnitLifecycleDecryptStates.StoredKeysShape.mk {e b : ℕ} {real : tacenta_session_unit.lifecycle.Session}
    (classicalStored : (↑real.triple.classical.skipped).length = 1)
    (sparseStored : (↑real.triple.post_quantum.skipped).length = 1)
    (classicalChains :
      real.triple.classical.cks.isSome = true ∧
        real.triple.classical.ckr.isSome = true ∧ real.triple.classical.dhr_pub.isSome = true)
    (sparseChains :
      ∃ p ∈ ↑real.triple.post_quantum.chains,
        p.1 = real.triple.post_quantum.epoch ∧ p.2.send.isSome = true ∧ p.2.receive.isSome = true)
    (events : ↑real.triple.classical.events = 5)
    (classicalCounters : ↑real.triple.classical.ns = 3 ∧ ↑real.triple.classical.nr = 4 ∧ ↑real.triple.classical.pn = 2)
    (sparseEpoch : ↑real.triple.post_quantum.epoch = e)
    (braidEpoch : ↑(Tacenta.SessionUnitBraidT1.State.epoch_val real.braid.state) = b) :
    Tacenta.UnitLifecycleDecryptStates.StoredKeysShape e b real
-/
#guard_msgs in
#print Tacenta.UnitLifecycleDecryptStates.StoredKeysShape

/--
info: def Tacenta.UnitLifecycleDecryptStates.heldStoredSession : tacenta_session_unit.tacenta_boundary.dh.PrivateKey →
  tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes →
    Aeneas.Std.alloc.vec.Vec Aeneas.Std.U8 →
      Aeneas.Std.Array Aeneas.Std.U8 32#usize →
        tacenta_session_unit.tacenta_kem.IncrementalKeyPair →
          tacenta_session_unit.tacenta_erasure.Encoder → tacenta_session_unit.lifecycle.Session :=
fun k pkb ad a kp enc =>
  have __src := Tacenta.UnitHeadroomSatisfiable.sessionOf k pkb pkb ad a none;
  { triple := Tacenta.UnitLifecycleDecryptStates.storedTriple a 0#u64,
    braid := Tacenta.UnitHeldKemWitness.heldBraid kp enc, ratchet_private := __src.ratchet_private,
    identity_ad := __src.identity_ad, our_identity_public := __src.our_identity_public,
    peer_identity_public := __src.peer_identity_public, pending_initial := __src.pending_initial,
    established_ephemeral := __src.established_ephemeral }
-/
#guard_msgs in
#print Tacenta.UnitLifecycleDecryptStates.heldStoredSession
