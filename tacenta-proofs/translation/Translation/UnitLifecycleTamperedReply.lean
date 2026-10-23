import Translation.UnitLifecycleResponderReplyReceipt

/-!
# The initiator refuses a tampered reply: `Session::decrypt` of the reply with its ciphertext replaced

`UnitLifecycleResponderReplyReceipt` shows that, on the run of the initiator's first send, the responder's receipt of
it and the responder's reply, the initiator's public `Session::decrypt` at the session `s'` its first `encrypt` left,
from the source `rng'` that `encrypt` left, accepts the reply's bytes `bytesR`.  This module takes, on the same run,
every frame that keeps the reply's header (its first 102 bytes) and carries in place of the reply's ciphertext bytes
`cT` that no call of the boundary's `encrypt` returns under the reply's message keys and associated data, and shows
that the same `decrypt`, at the same `s'` from the same `rng'`, refuses it with `Aead`, takes exactly the one draw the
honest receipt takes, and leaves the session as it was.  It rests on one new assumed law about the boundary AEAD,
`AeadOpenSealUnique`, and one new per-run premise about the frame, `NotASealing`.

## How

* `open_none_of_not_sealing` (bridge): under `AeadOpenSealUnique` and the decrypt oracle record's open clause, the
  oracle's open of bytes that are no sealing under the keys and associated data is `none`.
* `tampered_reply_model_refusal` (model only): the model's public `decrypt` of the reply's header followed by any
  ciphertext, at the sender after its first message with the agreement at `keysSampled`, takes the same steps as for the
  reply (dispatch, decode, the agreement's receive, the first agreement, the draw, the draw's agreement, one
  Diffie-Hellman step on a fresh ratchet key) and refuses `aead` with the session unchanged when the open of that
  ciphertext is refused.
* `replyFrame_take`, `replyFrame_drop`: the reply frame's first 102 bytes are its header and the rest is the seal.
* `initiator_refuses_tampered_reply` composes them on the run: `initiator_receives_reply` gives the honest receipt,
  `initiator_first_send_responder_replies` and `established_encrypt_successor_hypotheses` on the same first send give
  the key equations and the invariant, relation, ceilings and honest chunks at `s'`, and
  `decrypt_refines_ratchet_frame_of_counter_headroom` relates the call on the tampered frame to the model's step.

## The statements

* `initiator_refuses_tampered_reply`: under the hypotheses of `initiator_receives_reply` and `AeadOpenSealUnique`, the
  responder's `encrypt` returns `bytesR` and the initiator's `decrypt` of `bytesR` at `s'` from `rng'` returns `Ok` of
  the responder's plaintext, taking exactly the draw `dA`; the reply's own ciphertext (the bytes after its first 102)
  is a sealing, so `NotASealing` excludes it; and for every slice `frame` whose bytes are the first 102 bytes of
  `bytesR` followed by bytes `cT` with `NotASealing` under the reply's message keys and associated data, the same call
  on `frame` returns `Err(Aead)` with the session `s'` unchanged and a source after exactly the draw `dA`.
* `tamper_laws_model`, `modelReply_openSealUnique`, `modelReply_notASealing_nil`, `modelReply_sealing_excluded`: the
  law and the round trip hold in the reply's joint model, the empty ciphertext is no sealing there, and the toy's seal of
  the empty plaintext is excluded by the premise.
* `lenient_roundTrip_not_unique`: an interpretation whose open skips the toy's check of its leading byte meets
  `AeadRoundTripShape` and fails `AeadOpenSealUniqueShape`: the new law is not implied by the round trip.

## The laws and premises

* `AeadOpenSealUnique` (new, **assumed**): `AeadOpenSealUniqueShape` at the real constants.  If the boundary's
  `decrypt` of a ciphertext `c` under keys, IV and associated data `ad` returns `Ok v`, then its `encrypt` of `v` under
  the same keys, IV and `ad` returns a ciphertext with the bytes of `c`.  A functional uniqueness law, not an
  unforgeability statement: it says what an opened ciphertext is, not who can compute one.  It is true of the shipping
  AEAD by reading below the top of the length range, and not proved.  At the top it is false: the open streams `ad` and
  the ciphertext into the MAC, but the seal's `mac` first copies `ad ‖ ct` into a `Vec`, which panics on a capacity
  overflow once their lengths sum past `isize::MAX` (about 2 GiB on a 32-bit target), so there the open can return
  `Ok v` and the reseal of `v` does not return; `LIMITATIONS.md` records the same edge for `AeadSealBounded`.  The
  run's associated data is a short header, and the law carries no length bound.  `tacenta-core/boundary/src/aead.rs`
  seals with AES-256-CBC and PKCS#7 under the given keys and IV, then appends the full 32-byte HMAC-SHA256 tag over `ad ‖ ct`; it opens by comparing that tag in
  constant time and only then decrypting and removing the padding.  An opened `c` is therefore `ct ‖ tag` with the tag
  the HMAC of `ad ‖ ct`, and resealing what `ct` decrypts to gives `c` again when three facts hold, each read and none
  proved: the locked `cipher` 0.4.4 refuses a ciphertext that is empty or not whole blocks, the locked `block-padding`
  0.3.3 removes PKCS#7 padding strictly (every padding byte checked), and AES-256 encryption inverts its decryption
  on a block.  The seal's tag (`tacenta_kdf::hmac_sha256`) and the open's check (RustCrypto `Mac`) are both
  HMAC-SHA256 over the locked `hmac` 0.12.1.  The law would be false of a truncated tag comparison, a lenient padding
  check, a decrypt that ignored trailing bytes or a random IV.  The model: `Interp.modelReply`, whose toy AEAD seals by
  putting a zero byte in front and opens exactly the strings that begin with one.
* `NotASealing` (new, **per-run premise**): no call of the real `encrypt` under the reply's message keys and
  associated data returns the bytes `cT`.  It is a condition on the frame, not a law.  That an attacker who does not
  hold the message key cannot produce a sealing is the unforgeability of HMAC-SHA256, which no theorem here states and
  none can prove of the real function; this premise is where that assumption sits.  In the model, the empty
  ciphertext meets it.  Together the law and the premise say no more than that the boundary's `decrypt` refuses those
  bytes under those keys and that associated data; what the theorem adds is the session around that call: that the
  call reaches the boundary's open with exactly the reply's message keys and associated data, and that the refusal is
  `Aead`, leaves the session as it was and takes one draw.
* The other premises are those of `initiator_receives_reply`, unchanged, `hfreshB` included.

## Trust

`initiator_refuses_tampered_reply` rests on the kernel and opaque constants of the unit (pins below), as
`initiator_receives_reply` does; it lists no compiler-trust axiom.

## Non-vacuity

`tamper_laws_model` puts the round trip, the new law and the per-run premise in `Interp.modelReply`, the interpretation
at which `reply_receipt_laws_model` puts every other law the reply's receipt takes.  The toy AEAD ignores keys, IV and
associated data, so a frame sealed under another key is a sealing there: the toy shows the law and the premise are
satisfiable together, not that any AEAD authenticates.  `lenient_roundTrip_not_unique` shows the law excludes an
interpretation the round trip admits.  On the run, the reply's own ciphertext fails the premise (a conjunct of the
headline), so the refusal and the honest receipt cannot both apply to one frame.  The run's other premises are reached
at the real constants under the laws by `first_send_reply_receipt_reachable`; no frame meeting `NotASealing` at the
real constants is exhibited.

## What it does not show

* That the shipping AEAD meets `AeadOpenSealUnique`: it is assumed, true by reading below the top of the length range
  and false at it, not proved; an independent verified implementation's statements (a bad tag refused, and the round
  trip given AES inversion) are of another shape and about another implementation.
* That a frame an attacker can produce meets `NotASealing`: that is the unforgeability of HMAC-SHA256, not stated here.
* A frame whose header bytes were changed (ratchet key, counters, epochs, agreement type or chunk), a frame shorter than
  the header, or a frame of another type: those reach other associated data, another Diffie-Hellman step or a decode
  refusal, and are not covered.
* The tampered frame's refusal when the reply's ratchet key is the peer key the initiator holds, or when the initiator's
  draw's agreement is refused: `hfreshB` and the contributory law are kept.
* That the source the refusal leaves equals the one the honest receipt leaves: both hold the rest of the draws after
  `dA`; equality of the source states is not shown.
* A run in which the tampered frame is refused and the honest reply then received: the refusal leaves the session as it
  was, but the receipt after it, from a source one draw further on, is not composed.
* Tamper refusal on any other route: the responder's receipt of the first frame, a restored session, later messages.
* Redelivery of the honest reply, here (its delivery a second time at the session the first receipt returns is refused
  by `initiator_repeated_reply_refused` in `UnitLifecycleInitiatorRepeatedReply`).
* That the real primitives meet the boundary records or the other laws (`AeadRoundTrip`, `DhAgreeContributory`,
  `DhAgreeSymmetric`, `DhPublicValid`), or that ML-KEM decapsulation agrees on a run (`FirstKemAgrees`).
-/

open Aeneas Aeneas.Std Result
open tacenta_session_unit

namespace Tacenta.UnitLifecycleTamperedReply

open Tacenta.UnitLifecycleT3 (DhView DhCodecOf KemView arrayOf vecOf sliceOf SessionRefines OracleOf
  ResultRefines)
open Tacenta.UnitSatisfiabilityJoint (Interp Interp.real)
open Tacenta.UnitLifecycleResponderFirstReceipt (senderAfterFirst firstHeader firstKey decode_encodeMessage
  arrayOfBytes arrayOf_arrayOfBytes AeadRoundTripShape)
open Tacenta.UnitLifecycleResponderReply (replyComposite replyFrame)
open Tacenta.UnitLifecycleResponderReplyReceipt (replyAd reply_receive_key)

/-! ## The law and the per-run premise -/

/-- The boundary AEAD opens only what it seals, over an interpretation `I`: if opening the ciphertext `c` with keys,
IV and associated data `ad` returns `v`, then sealing `v` with the same keys, IV and associated data returns a
ciphertext with the bytes of `c`.  A functional uniqueness law: it says nothing about who can compute a sealing. -/
def AeadOpenSealUniqueShape (I : Interp) : Prop :=
  ∀ (k1 k2 : Array U8 32#usize) (iv : Array U8 16#usize) (c ad : Slice U8) (v : alloc.vec.Vec U8),
    I.aeadDecrypt k1 k2 iv c ad = ok (core.result.Result.Ok v) →
    ∃ ct, I.aeadEncrypt k1 k2 iv (alloc.vec.Vec.deref v) ad = ok ct ∧ ct.val = c.val

/-- **Assumed law**: `AeadOpenSealUniqueShape` at the real constants. -/
def AeadOpenSealUnique : Prop := AeadOpenSealUniqueShape Interp.real

/-- At the real constants, `AeadOpenSealUnique` is the statement about the real functions. -/
theorem aeadOpenSealUnique_is : AeadOpenSealUnique ↔
    ∀ (k1 k2 : Array U8 32#usize) (iv : Array U8 16#usize) (c ad : Slice U8) (v : alloc.vec.Vec U8),
      tacenta_boundary.aead.decrypt k1 k2 iv c ad = ok (core.result.Result.Ok v) →
      ∃ ct, tacenta_boundary.aead.encrypt k1 k2 iv (alloc.vec.Vec.deref v) ad = ok ct ∧ ct.val = c.val :=
  Iff.rfl

/-- No plaintext seals to the bytes `c`, over an interpretation `I`: no call of the boundary's `encrypt` whose keys,
IV and associated data have the bytes `k1`, `k2`, `iv` and `ad` returns a ciphertext with the bytes `c`. -/
def NotASealingShape (I : Interp) (k1 k2 iv ad c : Model.Lifecycle.Bytes) : Prop :=
  ∀ (K1 K2 : Array U8 32#usize) (IV : Array U8 16#usize) (pt A : Slice U8) (ct : alloc.vec.Vec U8),
    arrayOf K1 = k1 → arrayOf K2 = k2 → arrayOf IV = iv → sliceOf A = ad →
    I.aeadEncrypt K1 K2 IV pt A = ok ct → vecOf ct ≠ c

/-- **Per-run premise**: `NotASealingShape` at the real constants. -/
def NotASealing (k1 k2 iv ad c : Model.Lifecycle.Bytes) : Prop := NotASealingShape Interp.real k1 k2 iv ad c

/-- At the real constants, `NotASealing` is the statement about the real `encrypt`. -/
theorem notASealing_is (k1 k2 iv ad c : Model.Lifecycle.Bytes) : NotASealing k1 k2 iv ad c ↔
    ∀ (K1 K2 : Array U8 32#usize) (IV : Array U8 16#usize) (pt A : Slice U8) (ct : alloc.vec.Vec U8),
      arrayOf K1 = k1 → arrayOf K2 = k2 → arrayOf IV = iv → sliceOf A = ad →
      tacenta_boundary.aead.encrypt K1 K2 IV pt A = ok ct → vecOf ct ≠ c :=
  Iff.rfl

/-! ## The open, through the oracle record -/

section Bridges

open Tacenta.UnitLifecycleDecryptRatchetT3 (DecryptOracleOf)

/-- **An oracle open of bytes that are no sealing is refused**: under `AeadOpenSealUnique` and the decrypt oracle
record's open clause, for keys of 32, 32 and 16 bytes and a ciphertext and associated data that fit a slice, if no
call of the real `encrypt` under those keys and associated data returns the ciphertext's bytes, then the oracle's
open of them returns `none`. -/
theorem open_none_of_not_sealing (hu : AeadOpenSealUnique) {R : Type} {rc : rand_core_1.RngCore R}
    {crc : rand_core_1.CryptoRng R} {dh : DhView} {trace : R → List Model.Lifecycle.Key}
    {oracle : Model.Lifecycle.Oracle} (oracleOf : DecryptOracleOf rc crc dh trace oracle)
    (k1 k2 iv : Model.Lifecycle.Bytes) (hk1 : k1.length = 32) (hk2 : k2.length = 32) (hiv : iv.length = 16)
    (c ad : Model.Lifecycle.Bytes) (hc : c.length ≤ Usize.max) (had : ad.length ≤ Usize.max)
    (hns : NotASealing k1 k2 iv ad c) :
    oracle.aeadOpen k1 k2 iv c ad = none := by
  let K1 : Array U8 32#usize := arrayOfBytes k1 hk1
  let K2 : Array U8 32#usize := arrayOfBytes k2 hk2
  let IV : Array U8 16#usize := arrayOfBytes iv hiv
  let C := Tacenta.UnitSatisfiabilityBraidStates.sliceOfBytes c hc
  let A := Tacenta.UnitSatisfiabilityBraidStates.sliceOfBytes ad had
  have hC : sliceOf C = c := Tacenta.UnitSatisfiabilityBraidStates.sliceOf_sliceOfBytes c hc
  have hA : sliceOf A = ad := Tacenta.UnitSatisfiabilityBraidStates.sliceOf_sliceOfBytes ad had
  obtain ⟨res, hres, hopen⟩ := oracleOf.aeadOpen K1 K2 IV C A
  simp only [K1, K2, IV, arrayOf_arrayOfBytes, hC, hA] at hopen
  rw [← hopen]
  cases res with
  | Err e => rfl
  | Ok v =>
    obtain ⟨ct, hct, hval⟩ := hu K1 K2 IV C A v hres
    exact absurd (by simp only [vecOf, hval]; exact hC) (hns K1 K2 IV (alloc.vec.Vec.deref v) A ct
      (arrayOf_arrayOfBytes (n := 32#usize) k1 hk1) (arrayOf_arrayOfBytes (n := 32#usize) k2 hk2) (arrayOf_arrayOfBytes (n := 16#usize) iv hiv) hA hct)

open Tacenta.UnitLifecycleT3 (OracleOf) in
/-- **A seal is a sealing**: for keys of 32, 32 and 16 bytes, a plaintext slice and associated data that fit a slice,
the oracle's seal is the bytes of a call of the real `encrypt` under those keys and associated data, so it is not
`NotASealing`.  Under the oracle record's seal clause alone. -/
theorem not_notASealing_of_seal {R : Type} {rc : rand_core_1.RngCore R} {crc : rand_core_1.CryptoRng R}
    {dh : DhView} {kem : KemView} {trace : R → List Model.Lifecycle.Key} {oracle : Model.Lifecycle.Oracle}
    (oracleOf : OracleOf rc crc dh kem trace oracle)
    (k1 k2 iv : Model.Lifecycle.Bytes) (hk1 : k1.length = 32) (hk2 : k2.length = 32) (hiv : iv.length = 16)
    (pt : Slice U8) (ad : Model.Lifecycle.Bytes) (had : ad.length ≤ Usize.max) :
    ¬ NotASealing k1 k2 iv ad (oracle.aeadSeal k1 k2 iv (sliceOf pt) ad) := by
  intro hns
  let K1 : Array U8 32#usize := arrayOfBytes k1 hk1
  let K2 : Array U8 32#usize := arrayOfBytes k2 hk2
  let IV : Array U8 16#usize := arrayOfBytes iv hiv
  let A := Tacenta.UnitSatisfiabilityBraidStates.sliceOfBytes ad had
  have hA : sliceOf A = ad := Tacenta.UnitSatisfiabilityBraidStates.sliceOf_sliceOfBytes ad had
  obtain ⟨ct, hct, hvec⟩ := oracleOf.aeadSeal K1 K2 IV pt A
  simp only [K1, K2, IV, arrayOf_arrayOfBytes, hA] at hvec
  exact hns K1 K2 IV pt A ct (arrayOf_arrayOfBytes (n := 32#usize) k1 hk1) (arrayOf_arrayOfBytes (n := 32#usize) k2 hk2)
    (arrayOf_arrayOfBytes (n := 16#usize) iv hiv) hA hct hvec

end Bridges

/-! ## The model's receipt of a reply frame with its ciphertext replaced -/

section Model
open Model.State (Key)

/-- The reply's header is 102 bytes, when its ratchet key is 32 bytes. -/
theorem replyHeader_length (newPub : Key) (hlen : newPub.length = 32) :
    (Model.CompositeHeader.encode (replyComposite newPub)).length = 102 := by
  simp only [Model.CompositeHeader.encode, replyComposite, Model.CompositeHeader.encodeChunk, List.length_append,
    List.length_cons, List.length_nil, List.length_replicate, Model.Messages.be32, Model.CompositeHeader.be64,
    Model.CompositeHeader.be16, Model.CompositeHeader.chunkBytes, hlen]

/-- The first 102 bytes of the reply frame are its header. -/
theorem replyFrame_take (oracle : Model.Lifecycle.Oracle) (ad : Model.Lifecycle.Bytes) (newPub mk : Key)
    (pt : Model.Lifecycle.Bytes) (hlen : newPub.length = 32) :
    (replyFrame oracle ad newPub mk pt).take 102 = Model.CompositeHeader.encode (replyComposite newPub) := by
  unfold replyFrame Model.CompositeHeader.encodeMessage
  rw [← replyHeader_length newPub hlen, List.take_left]

/-- The bytes after the reply frame's first 102 are its ciphertext: the seal of the plaintext under the AEAD keys of
the message key and the reply's associated data. -/
theorem replyFrame_drop (oracle : Model.Lifecycle.Oracle) (ad : Model.Lifecycle.Bytes) (newPub mk : Key)
    (pt : Model.Lifecycle.Bytes) (hlen : newPub.length = 32) :
    (replyFrame oracle ad newPub mk pt).drop 102 =
      oracle.aeadSeal (Model.State.messageKeys mk .tacenta).1 (Model.State.messageKeys mk .tacenta).2.1
        (Model.State.messageKeys mk .tacenta).2.2 pt (replyAd ad newPub) := by
  unfold replyFrame Model.CompositeHeader.encodeMessage
  rw [← replyHeader_length newPub hlen, List.drop_left]
  rfl

/-- **The model's public `decrypt` of a reply frame with its ciphertext replaced refuses `aead`**, model only.  For a
model session whose Triple is the sender pair form after the first message and whose agreement is at `keysSampled`,
the frame with the reply's header (ratchet key `newPub`, 32 canonical bytes) and any ciphertext `cT`: when the
session's first agreement with `newPub` returns `dSend`, the oracle's next draw `c` agrees with `newPub`, `newPub`
is not the peer key the session holds, and the oracle's open of `cT` under the AEAD keys of the message key the
receive derives and the reply's associated data is refused, the step refuses `aead`, consumes the draw and leaves the
session as it was. -/
theorem tampered_reply_model_refusal (view : Model.Lifecycle.CodewordView) (oracleA : Model.Lifecycle.Oracle)
    (mA : Model.Lifecycle.Session) (a4 peer rkA cksA prk k1 k2 : Key) (e : Nat) (auth : Model.Braid.Auth)
    (dk ekVector : Model.Braid.Bytes) (enc : Model.Braid.Encoder)
    (hA : mA.triple = senderAfterFirst a4 peer rkA cksA prk k1 k2)
    (hbraid : mA.braid = .keysSampled e auth dk ekVector enc)
    (newPub dSend : Key) (cT : Model.Lifecycle.Bytes)
    (hlen : newPub.length = 32) (hkey : Model.Messages.checkKey newPub = some ())
    (hagree : oracleA.dhAgree mA.ratchetPrivate newPub = some dSend)
    (c : Key) (rest : List Key) (x : Key) (hdr : oracleA.draws = c :: rest)
    (hcand : oracleA.dhAgree c newPub = some x) (hpeer : newPub ≠ peer)
    (hopen : oracleA.aeadOpen
        (Model.State.messageKeys (firstKey (Model.State.kdfRk rkA dSend .tacenta).2 k2) .tacenta).1
        (Model.State.messageKeys (firstKey (Model.State.kdfRk rkA dSend .tacenta).2 k2) .tacenta).2.1
        (Model.State.messageKeys (firstKey (Model.State.kdfRk rkA dSend .tacenta).2 k2) .tacenta).2.2
        cT (replyAd mA.identityAd newPub) = none) :
    Model.Lifecycle.decrypt view oracleA mA (Model.CompositeHeader.encodeMessage (replyComposite newPub) cT) =
      { session := mA, result := .error .aead, oracle := { oracleA with draws := rest } } := by
  have hdisp := Model.Lifecycle.dispatchDecrypt_passthrough oracleA mA
    (Model.CompositeHeader.encodeMessage (replyComposite newPub) cT)
    (by simp [Model.CompositeHeader.encodeMessage, Model.CompositeHeader.encode, Model.Lifecycle.messageType])
  have hdec : Model.CompositeHeader.decodeDetailed
      (Model.CompositeHeader.encodeMessage (replyComposite newPub) cT) = .ok (replyComposite newPub, cT) := by
    rw [Model.CompositeHeader.decodeDetailed_ok_iff]
    exact decode_encodeMessage _ _ hlen hkey (fun c hc => by simp [replyComposite] at hc)
  have hhdr : Model.Lifecycle.tripleHeaderOf (replyComposite newPub) = firstHeader newPub := by
    simp [Model.Lifecycle.tripleHeaderOf, replyComposite, firstHeader]
  have hbr : Model.Braid.receive oracleA.braidKem mA.braid
      (Model.Lifecycle.braidMessageOf view mA.braid (replyComposite newPub)) = (e - 1, none, mA.braid) := by
    rw [hbraid]
    simp [Model.Braid.receive, Model.Lifecycle.braidMessageOf, replyComposite, Model.Lifecycle.braidTypeOf,
      Model.Braid.BraidState.epoch]
  have hfail : Model.Lifecycle.agreementFailed mA = false := by
    simp [Model.Lifecycle.agreementFailed, hbraid]
  have hdh : (replyComposite newPub).dh = newPub := rfl
  have hout : Model.Lifecycle.sparseOutputOf none = none := rfl
  have hrand : Model.Lifecycle.random32 oracleA = some (c, { oracleA with draws := rest }) := by
    simp [Model.Lifecycle.random32, Model.Lifecycle.takeDraw, hdr]
  have hrecv : Model.Lifecycle.receiveWithEviction mA.triple (replyComposite newPub) (firstHeader newPub) dSend x
      (oracleA.dhPublic c) none =
      .ok (Tacenta.UnitLifecycleResponderReplyReceipt.initiatorAfterReply rkA prk k1 k2 dSend x newPub
          (oracleA.dhPublic c), firstKey (Model.State.kdfRk rkA dSend .tacenta).2 k2) := by
    unfold Model.Lifecycle.receiveWithEviction
    rw [hA, reply_receive_key a4 peer rkA cksA prk k1 k2 dSend x newPub _ hpeer]
  unfold Model.Lifecycle.decrypt Model.Lifecycle.decryptRatchet
  rw [hdisp]
  dsimp only
  rw [hfail, if_neg (by simp), hdec]
  dsimp only
  rw [hbr, hdh, hagree]
  dsimp only
  rw [hrand]
  dsimp only
  rw [hcand]
  dsimp only
  rw [hhdr, hout, hrecv]
  dsimp only
  rw [show Model.Messages.concatAd mA.identityAd (Model.CompositeHeader.encode (replyComposite newPub)) =
    replyAd mA.identityAd newPub from rfl, hopen]

end Model

/-! ## The initiator's receipt of a tampered reply, on the run -/

section Comp

open Tacenta.UnitLifecycleT3 (BraidSendRefinementContracts TripleSendRefinementContracts CodewordViewSendOf
  ZeroizingRoundTrips)
open Tacenta.UnitLifecycleResponderFirstReceipt (DhAgreeContributory AeadRoundTrip)
open Tacenta.UnitLifecycleResponderFirstFrame (InitiatorSecretParts DhAgreeSymmetric PrekeyIdsDistinct
  FirstKemAgrees)
open Tacenta.UnitLifecycleDecryptRatchetT3 (DecryptOracleOf DecryptRatchetAgreements)
open Tacenta.UnitLifecycleEstablishInitiatorShape (DhPublicValid establishedModelOf)
open Tacenta.UnitLifecycleResponderReply (oracleOf_with_draws initiator_first_send_responder_replies)
open Tacenta.UnitLifecycleResponderReplyReceipt (fresh_public_of_draw initiator_reply_agreement
  initiator_candidate_agreement first_send_model_session replyAd_length_le initiator_receives_reply)

/-- **The initiator's `decrypt` refuses a tampered reply, on the run of its first send.**  Under the hypotheses of
`initiator_receives_reply` (`hfreshB` included) and the assumed law `AeadOpenSealUnique`: the responder's `encrypt` at
`sB'` returns `bytesR`, the reply frame under the key the initiator's receiving chain derives, and the initiator's
public `decrypt` of `bytesR` at `s'` from `rng'` returns `Ok ptA` with `ptA` the bytes of `ptR`, taking exactly the draw
`dA`; the reply's own ciphertext, the bytes of `bytesR` after its first 102, is a sealing under the reply's message
keys and associated data, so `NotASealing` excludes it; and for every slice `frame` whose bytes are the first 102 bytes
of `bytesR` (the reply's header) followed by bytes `cT` that are `NotASealing` under those keys and associated data
(the per-run premise), the same call on `frame` at `s'` from `rng'` returns `Err(Aead)`, returns the session `s'` as
it was, and leaves a source holding exactly the draws after `dA`.  A frame whose header bytes differ is not covered.
No compiler-trust axiom (the pin). -/
theorem initiator_refuses_tampered_reply [Tacenta.SessionUnitT1.DerivedKeysModel] {R E F : Type}
    (hu : AeadOpenSealUnique) (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView) (kem : KemView)
    (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
    (braid : BraidSendRefinementContracts rc oracle.braidKem)
    (triple : TripleSendRefinementContracts)
    (aead : Tacenta.UnitLifecycleT1.AeadSealBounded) (dhCodec : Tacenta.UnitLifecycleT1.DhCodecTotal)
    (oracleOf : OracleOf rc crc dh kem trace oracle) (codec : DhCodecOf dh)
    (codewordView : CodewordViewSendOf view)
    (hz80 : Tacenta.SessionUnitT3.ZeroizingRoundTrips80)
    (hz32 : ZeroizingRoundTrips (Array Std.U8 32#usize))
    (hzKeys : ZeroizingRoundTrips
      (Array Std.U8 32#usize × Array Std.U8 32#usize × Array Std.U8 16#usize))
    (hgen : Tacenta.UnitLifecycleEstablishedEncrypt.KeyGenSeededFor oracle.braidKem rc crc trace)
    (hsizes : Tacenta.UnitLifecycleEstablishedEncrypt.KeyGenSizesOf oracle.braidKem)
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
    (contractsA : Tacenta.UnitLifecycleT1.DecryptRatchetContracts rc)
    (agreementsA : DecryptRatchetAgreements oracle.braidKem)
    (dA : Model.Lifecycle.Key) (restA : List Model.Lifecycle.Key) (hdrawA : trace rng' = dA :: restA)
    (rcB : rand_core_1.RngCore F) (crcB : rand_core_1.CryptoRng F)
    (contracts : Tacenta.UnitLifecycleT1.EstablishResponderContracts rcB)
    (hpub : DhPublicValid) (hsym : DhAgreeSymmetric) (hcon : DhAgreeContributory) (haead : AeadRoundTrip)
    (hrt : Tacenta.UnitLifecycleSessionCodec.DhPublicBytesRoundTrip)
    (hoeq : Tacenta.UnitHeadroomInvariant.OptionEqU64Shape
      (@core.option.Option.Insts.CoreCmpPartialEqOption.eq))
    (traceB : F → List Model.Lifecycle.Key) (oracleB : Model.Lifecycle.Oracle)
    (oracleOfB : OracleOf rcB crcB dh kem traceB oracleB)
    (braidB : BraidSendRefinementContracts rcB oracleB.braidKem)
    (agreements : DecryptRatchetAgreements oracleB.braidKem)
    (ourB : lifecycle.Identity) (storeB : lifecycle.PrekeyStore)
    (hpublish : lifecycle.PrekeyStore.publish storeB = ok bundleA)
    (hidentity : lifecycle.Identity.public ourB = ok storeB.identity_public)
    (hdistinct : PrekeyIdsDistinct storeB)
    (hkem : FirstKemAgrees storeB bundleA.kem_prekey_id q.kemCiphertext q.kemSecret)
    (rngB : F) (htraceB : traceB rngB = oracleB.draws) (dB : Model.Lifecycle.Key)
    (restB : List Model.Lifecycle.Key) (hdrawB : traceB rngB = dB :: restB)
    (ptB : alloc.vec.Vec U8) (sB' : lifecycle.Session) (storeB' : lifecycle.PrekeyStore) (rngB' : F)
    (hcallB : lifecycle.establish_responder rcB crcB ourB storeB (alloc.vec.Vec.deref bytes) rngB =
      ok (core.result.Result.Ok (sB', ptB), storeB', rngB'))
    (ptR : Slice Std.U8) (hroomR : 102 + (ptR.val.length + 48) ≤ Usize.max) (rngR : F)
    (hfreshB : oracleB.dhPublic dB ≠ arrayOf q.peerRatchetBytes) :
    ∃ (dSend : Model.Lifecycle.Key) (bytesR : alloc.vec.Vec Std.U8) (sB'' : lifecycle.Session)
      (ptA : alloc.vec.Vec Std.U8) (s'' : lifecycle.Session) (rngA' : R),
      oracleB.dhAgree dB (arrayOf q.ratchetBytes) = some dSend ∧
      lifecycle.Session.encrypt rcB crcB sB' ptR rngR = ok (core.result.Result.Ok bytesR, sB'', rngR) ∧
      vecOf bytesR = replyFrame oracleB (vecOf q.identityAd) (oracleB.dhPublic dB)
        (firstKey (Model.State.kdfRk (arrayOf q.rootKey) dSend .tacenta).2 (arrayOf q.sparseReceive)) (sliceOf ptR) ∧
      lifecycle.Session.decrypt rc crc s' (alloc.vec.Vec.deref bytesR) rng' =
        ok (core.result.Result.Ok ptA, s'', rngA') ∧ ptA.val = ptR.val ∧ trace rngA' = restA ∧
      ¬ NotASealing
        (Model.State.messageKeys (firstKey (Model.State.kdfRk (arrayOf q.rootKey) dSend .tacenta).2
          (arrayOf q.sparseReceive)) .tacenta).1
        (Model.State.messageKeys (firstKey (Model.State.kdfRk (arrayOf q.rootKey) dSend .tacenta).2
          (arrayOf q.sparseReceive)) .tacenta).2.1
        (Model.State.messageKeys (firstKey (Model.State.kdfRk (arrayOf q.rootKey) dSend .tacenta).2
          (arrayOf q.sparseReceive)) .tacenta).2.2
        (replyAd (vecOf q.identityAd) (oracleB.dhPublic dB)) ((vecOf bytesR).drop 102) ∧
      ∀ (frame : Slice Std.U8) (cT : Model.Lifecycle.Bytes),
        sliceOf frame = (vecOf bytesR).take 102 ++ cT →
        NotASealing
          (Model.State.messageKeys (firstKey (Model.State.kdfRk (arrayOf q.rootKey) dSend .tacenta).2
            (arrayOf q.sparseReceive)) .tacenta).1
          (Model.State.messageKeys (firstKey (Model.State.kdfRk (arrayOf q.rootKey) dSend .tacenta).2
            (arrayOf q.sparseReceive)) .tacenta).2.1
          (Model.State.messageKeys (firstKey (Model.State.kdfRk (arrayOf q.rootKey) dSend .tacenta).2
            (arrayOf q.sparseReceive)) .tacenta).2.2
          (replyAd (vecOf q.identityAd) (oracleB.dhPublic dB)) cT →
        ∃ rngT : R,
          lifecycle.Session.decrypt rc crc s' frame rng' =
            ok (core.result.Result.Err lifecycle.Error.Aead, s', rngT) ∧ trace rngT = restA := by
  -- the honest reply, accepted
  obtain ⟨dSend, -, bytesR, sB'', ptA, s'', rngA', hagreeB, -, hcallR, hbytesR, hcallA, hpt, hdr, -⟩ :=
    initiator_receives_reply rc crc trace dh kem view oracle braid triple aead dhCodec oracleOf codec
      codewordView hz80 hz32 hzKeys hgen hsizes hct hbound rcE crcE ourA bundleA expected rng0 rng1 s h q hq
      plaintext hroom rng htrace d1 d2 rest hdraws bytes s' rng' hcall contractsA agreementsA dA restA hdrawA rcB
      crcB contracts hpub hsym hcon haead hrt hoeq traceB oracleB oracleOfB braidB agreements ourB storeB hpublish
      hidentity hdistinct hkem rngB htraceB dB restB hdrawB ptB sB' storeB' rngB' hcallB ptR hroomR rngR hfreshB
  -- the same run: the key generation of the first send, and the responder's agreement
  obtain ⟨-, -, dSend', dk, ekSeed, ekVector, -, -, hkg, -, hagreeB', -⟩ :=
    initiator_first_send_responder_replies rc crc trace dh kem view oracle braid triple aead dhCodec oracleOf
      codec codewordView hz80 hz32 hzKeys hgen hsizes hct hbound rcE crcE ourA bundleA expected rng0 rng1 s h q hq
      plaintext hroom rng htrace d1 d2 rest hdraws bytes s' rng' hcall rcB crcB contracts hpub hsym hcon haead hrt
      hoeq traceB oracleB oracleOfB braidB agreements ourB storeB hpublish hidentity hdistinct hkem rngB htraceB dB
      restB hdrawB ptB sB' storeB' rngB' hcallB ptR hroomR rngR
  rw [hagreeB] at hagreeB'
  cases hagreeB'
  -- the session the first send left: invariant, relation, ceilings, honest chunks
  obtain ⟨hinv, hrel, hc, hhonest⟩ :=
    Tacenta.UnitLifecycleEstablishedEncrypt.established_encrypt_successor_hypotheses rc crc trace dh kem view
      oracle braid triple aead dhCodec oracleOf codec codewordView hz80 hz32 hzKeys hgen hct hbound hpub hoeq
      agreementsA.kemLen agreementsA.validateEk hsizes contracts.divCeilValue rcE crcE ourA bundleA expected rng0
      rng1 s h plaintext hroom rng htrace ⟨d1, d2, rest, hdraws⟩ bytes s' rng' hcall
  subst hq
  obtain ⟨encoder, hmA⟩ := first_send_model_session dh view oracle q (sliceOf plaintext) d1 d2 rest
    (htrace.symm.trans hdraws) dk ekSeed ekVector hkg
  -- the reply's ratchet key, the initiator's first agreement with it, and its draw's agreement with it
  obtain ⟨-, k, pk, b, -, -, hkd, hpk, -, hcan, hpkb, hnew⟩ :=
    fresh_public_of_draw hpub codec (DecryptOracleOf.of_oracleOf oracleOfB) rngB dB restB hdrawB
  let oracleA : Model.Lifecycle.Oracle := { oracle with draws := trace rng' }
  have oracleOfA : DecryptOracleOf rc crc dh trace oracleA :=
    DecryptOracleOf.of_oracleOf (oracleOf_with_draws oracleOf _)
  have hagreeA : oracleA.dhAgree (dh.privateKey q.ratchetPrivate) (oracleB.dhPublic dB) = some dSend := by
    rw [← hagreeB, hnew, ← hpkb, ← hkd]
    exact initiator_reply_agreement hsym codec oracleOfA (DecryptOracleOf.of_oracleOf oracleOfB) q k pk hpk
  obtain ⟨x, hx⟩ := initiator_candidate_agreement hcon codec oracleOfA rng' dA restA hdrawA k pk hpk
  rw [hpkb, ← hnew] at hx
  have hlen : (oracleB.dhPublic dB).length = 32 := by rw [hnew]; simp [arrayOf]
  have hkey : Model.Messages.checkKey (oracleB.dhPublic dB) = some () := by
    rw [hnew]
    simp [Model.Messages.checkKey, Tacenta.UnitLifecycleResponderFirstFrame.canonicalKey_arrayOf _ hcan]
  have hk1 : (Model.State.messageKeys (firstKey (Model.State.kdfRk (arrayOf q.rootKey) dSend .tacenta).2
      (arrayOf q.sparseReceive)) .tacenta).1.length = 32 := by
    simp [Model.State.messageKeys, Model.Kdf.hkdf_length]
  have hk2 : (Model.State.messageKeys (firstKey (Model.State.kdfRk (arrayOf q.rootKey) dSend .tacenta).2
      (arrayOf q.sparseReceive)) .tacenta).2.1.length = 32 := by
    simp [Model.State.messageKeys, Model.Kdf.hkdf_length]
  have hiv : (Model.State.messageKeys (firstKey (Model.State.kdfRk (arrayOf q.rootKey) dSend .tacenta).2
      (arrayOf q.sparseReceive)) .tacenta).2.2.length = 16 := by
    simp [Model.State.messageKeys, Model.Kdf.hkdf_length]
  have had := replyAd_length_le dhCodec q.toInitiatorOutputParts _ hlen
  refine ⟨dSend, bytesR, sB'', ptA, s'', rngA', hagreeB, hcallR, hbytesR, hcallA, hpt, hdr, ?_, ?_⟩
  -- the honest ciphertext is a sealing
  · rw [hbytesR, replyFrame_drop _ _ _ _ _ hlen]
    exact not_notASealing_of_seal oracleOfB _ _ _ hk1 hk2 hiv ptR _ had
  -- a frame with the reply's header and a ciphertext that is no sealing
  intro frame cT hframeT hns
  rw [hbytesR, replyFrame_take _ _ _ _ _ hlen] at hframeT
  have hmsg : sliceOf frame = Model.CompositeHeader.encodeMessage (replyComposite (oracleB.dhPublic dB)) cT :=
    hframeT
  have hcT : cT.length ≤ Usize.max := by
    have h1 : (sliceOf frame).length ≤ Usize.max := by simp [sliceOf]; exact frame.property
    rw [hmsg] at h1
    simp only [Model.CompositeHeader.encodeMessage, List.length_append] at h1
    omega
  have hopen := open_none_of_not_sealing hu oracleOfA _ _ _ hk1 hk2 hiv cT _ hcT had hns
  -- the decrypt refinement at the session the first send left, on the tampered frame
  let mA := (Model.Lifecycle.encrypt view oracle (establishedModelOf dh q.session) (sliceOf plaintext)).session
  have hadA : mA.identityAd = vecOf q.identityAd := by simp only [mA, hmA]; rfl
  have inputs : Tacenta.UnitLifecycleDecryptRunBounds.DecryptRatchetRunInputs view oracleA trace s' mA
      frame rng' := by
    refine ⟨?_, fun mc ct _ => hhonest _, ⟨dA, restA, hdrawA⟩⟩
    intro rcomp mcomp ct hd hcr
    rw [hmsg, (Model.CompositeHeader.decodeDetailed_ok_iff _ _).mpr
      (decode_encodeMessage _ _ hlen hkey (fun c hc => by simp [replyComposite] at hc))] at hd
    simp only [Except.ok.injEq, Prod.mk.injEq] at hd
    obtain ⟨rfl, -⟩ := hd
    have hag := hcr.agChunk
    unfold Tacenta.UnitLifecycleT3.IncomingChunkRefines
    simp only [replyComposite] at hag ⊢
    rcases hrc : rcomp.ag_chunk with _ | rch
    · trivial
    · rw [hrc] at hag; exact hag.elim
  have hframe : Model.Lifecycle.messageType (sliceOf frame) ≠ some .initial := by
    rw [hmsg]
    simp [Model.CompositeHeader.encodeMessage, Model.CompositeHeader.encode, Model.Lifecycle.messageType]
  obtain ⟨output, hcallT, hstep⟩ :=
    Tacenta.UnitLifecycleDecryptT3.decrypt_refines_ratchet_frame_of_counter_headroom rc crc trace dh view oracleA
      oracleOfA codec contractsA agreementsA s' mA frame rng' hframe hinv hrel hc rfl inputs
  -- the model's step: the tampered frame's open is refused
  have hdrA : oracleA.draws = dA :: restA := hdrawA
  have hM := tampered_reply_model_refusal view oracleA mA (arrayOf q.ratchetBytes)
    (arrayOf q.peerRatchetBytes) (arrayOf q.rootKey) (arrayOf q.sendChain) (arrayOf q.sparseRoot)
    (arrayOf q.sparseSend) (arrayOf q.sparseReceive) 1 (Tacenta.SessionUnitBraidT3.AuthOf q.auth) dk ekVector
    encoder (by simp only [mA, hmA]) (by simp only [mA, hmA]) (oracleB.dhPublic dB) dSend cT hlen hkey
    (by simp only [mA, hmA]; exact hagreeA) dA restA x hdrA hx hfreshB (by rw [hadA]; exact hopen)
  obtain ⟨res, sT, rngT⟩ := output
  have hres := hstep.result
  have hdrT := hstep.draws
  rw [hmsg, hM] at hres hdrT
  cases res with
  | Ok v => simp [ResultRefines] at hres
  | Err e =>
    simp only [ResultRefines] at hres
    have he : e = lifecycle.Error.Aead := Tacenta.UnitLifecycleT3.refusalOf_injective (hres.trans rfl)
    have hsT := Tacenta.UnitLifecycleAtomicity.decrypt_err_leaves_state rc crc _ _ _ _ sT rngT hcallT
    rw [he, hsT] at hcallT
    exact ⟨rngT, hcallT, hdrT⟩

end Comp

/-! ## The law in a model, and an AEAD that meets the round trip but not the law -/

section JointModel

open Tacenta.UnitOracleModel (sealModel openModel)
open Tacenta.UnitLifecycleResponderReplyReceipt (Interp.modelReply)

/-- The toy open accepts a ciphertext only when its first byte is zero, and returns the rest. -/
theorem openModel_ok (c : Slice U8) (v : alloc.vec.Vec U8) (h : openModel c = .Ok v) :
    c.val = 0#u8 :: v.val := by
  unfold openModel at h
  split at h
  · rename_i x rest hc
    split at h
    · rename_i hx
      cases h
      subst hx
      exact hc
    · cases h
  · cases h

/-- The toy seal puts a zero byte in front of a plaintext that leaves room for it. -/
theorem sealModel_val (p : Slice U8) (h : p.val.length + 1 ≤ Usize.max) :
    (sealModel p).val = 0#u8 :: p.val := by
  unfold sealModel
  rw [dif_pos h]

/-- **`AeadOpenSealUniqueShape` holds in the reply's joint model** (`Interp.modelReply`, whose AEAD is the toy of
`UnitOracleModel`: seal puts a zero byte in front, open accepts exactly a leading zero byte and returns the rest):
what the toy opens is the toy's seal of what it opened to.  The toy ignores keys, IV and associated data. -/
theorem modelReply_openSealUnique : AeadOpenSealUniqueShape Interp.modelReply := by
  intro k1 k2 iv c ad v h
  have h' : openModel c = .Ok v := by
    have h0 : ok (openModel c) = ok (core.result.Result.Ok v) := h
    injection h0
  have hc := openModel_ok c v h'
  have hlen : (alloc.vec.Vec.deref v).val.length + 1 ≤ Usize.max := by
    have := c.property
    rw [hc] at this
    simp at this
    show v.val.length + 1 ≤ Usize.max
    omega
  refine ⟨sealModel (alloc.vec.Vec.deref v), rfl, ?_⟩
  rw [sealModel_val _ hlen, hc]
  rfl

/-- **The empty ciphertext is no sealing in the reply's joint model**, under every key, IV and associated data: the
toy's seal is never empty.  So the per-run premise `NotASealingShape` holds there. -/
theorem modelReply_notASealing_nil (k1 k2 iv ad : Model.Lifecycle.Bytes) :
    NotASealingShape Interp.modelReply k1 k2 iv ad [] := by
  intro K1 K2 IV pt A ct _ _ _ _ hct
  have hct' : ok (sealModel pt) = ok ct := hct
  injection hct' with hct''
  subst hct''
  unfold sealModel
  split
  · simp [vecOf]
  · rename_i hlong
    intro hnil
    have : pt.val = [] := by simpa [vecOf] using hnil
    rw [this] at hlong
    have h1 : 1 ≤ Usize.max := by scalar_tac
    simp at hlong
    omega

/-- **The toy's sealing of the empty plaintext is a sealing**: for keys of 32, 32 and 16 bytes and associated data
that fits a slice, the one-byte ciphertext `[0]` is the toy's seal of the empty plaintext, so `NotASealingShape`
fails there.  The premise excludes the ciphertexts the model seals. -/
theorem modelReply_sealing_excluded (k1 k2 iv ad : Model.Lifecycle.Bytes) (hk1 : k1.length = 32)
    (hk2 : k2.length = 32) (hiv : iv.length = 16) (had : ad.length ≤ Usize.max) :
    ¬ NotASealingShape Interp.modelReply k1 k2 iv ad [0] := by
  intro hns
  let A := Tacenta.UnitSatisfiabilityBraidStates.sliceOfBytes ad had
  have hA : sliceOf A = ad := Tacenta.UnitSatisfiabilityBraidStates.sliceOf_sliceOfBytes ad had
  refine hns (arrayOfBytes k1 hk1) (arrayOfBytes k2 hk2) (arrayOfBytes iv hiv) (Slice.new U8) A
    (sealModel (Slice.new U8)) (arrayOf_arrayOfBytes (n := 32#usize) k1 hk1)
    (arrayOf_arrayOfBytes (n := 32#usize) k2 hk2) (arrayOf_arrayOfBytes (n := 16#usize) iv hiv) hA rfl ?_
  rw [vecOf, sealModel_val _ (by show ([] : List U8).length + 1 ≤ Usize.max; simp; scalar_tac)]
  rfl

/-- A lenient toy open: it accepts every ciphertext that is not empty, whatever its first byte, and returns the
rest.  The toy's check of its leading byte stands in for a tag check; this open skips it. -/
def openLenient (c : Slice U8) : core.result.Result (alloc.vec.Vec U8) tacenta_boundary.aead.DecryptError :=
  if c.val = [] then .Err () else .Ok ⟨c.val.tail, by have := c.property; simp; omega⟩

/-- `Interp.modelReply` with the lenient open. -/
noncomputable def Interp.modelLenient : Interp :=
  { Interp.modelReply with aeadDecrypt := fun _ _ _ c _ => ok (openLenient c) }

/-- **`AeadOpenSealUniqueShape` is not implied by the round trip**: the lenient interpretation opens what it seals
(`AeadRoundTripShape` holds) and opens the one-byte ciphertext `[1]`, which it never seals, so the law fails there.
The law excludes an AEAD that opens more than it seals; the round trip does not. -/
theorem lenient_roundTrip_not_unique :
    AeadRoundTripShape Interp.modelLenient ∧ ¬ AeadOpenSealUniqueShape Interp.modelLenient := by
  refine ⟨?_, ?_⟩
  · intro k1 k2 iv pt ad ct hpt hct
    have hct' : ok (sealModel pt) = ok ct := hct
    injection hct' with hct''
    subst hct''
    have hval := sealModel_val pt (by omega)
    refine ⟨⟨pt.val, pt.property⟩, ?_, rfl⟩
    show ok (openLenient (alloc.vec.Vec.deref (sealModel pt))) = _
    unfold openLenient
    have hd : (alloc.vec.Vec.deref (sealModel pt)).val = 0#u8 :: pt.val := hval
    rw [if_neg (by rw [hd]; simp)]
    congr 2
    apply Subtype.ext
    show (alloc.vec.Vec.deref (sealModel pt)).val.tail = pt.val
    rw [hd]
    rfl
  · intro hu
    let c : Slice U8 := ⟨[1#u8], by simp; scalar_tac⟩
    have hopen : Interp.modelLenient.aeadDecrypt (Array.repeat 32#usize 0#u8) (Array.repeat 32#usize 0#u8)
        (Array.repeat 16#usize 0#u8) c (Slice.new U8) =
        ok (core.result.Result.Ok ⟨[], by simp⟩) := by
      show ok (openLenient c) = _
      unfold openLenient
      rfl
    obtain ⟨ct, hct, hval⟩ := hu _ _ _ c (Slice.new U8) _ hopen
    have hct' : ok (sealModel (alloc.vec.Vec.deref ⟨[], by simp⟩)) = ok ct := hct
    injection hct' with hct''
    subst hct''
    rw [sealModel_val _ (by show ([] : List U8).length + 1 ≤ Usize.max; simp; scalar_tac)] at hval
    simp [c] at hval

/-- **The tamper laws hold together in the reply's joint model**: `AeadRoundTripShape` and `AeadOpenSealUniqueShape` hold
at `Interp.modelReply`, the interpretation at which `reply_receipt_laws_model` puts every other law the reply's receipt
takes, and the per-run premise `NotASealingShape` holds there of the empty ciphertext under every key, IV and associated
data.  In the substitution sense of `UnitSatisfiabilityRecords`; not a statement that the real AEAD meets them. -/
theorem tamper_laws_model :
    AeadRoundTripShape Interp.modelReply ∧ AeadOpenSealUniqueShape Interp.modelReply ∧
      ∀ k1 k2 iv ad : Model.Lifecycle.Bytes, NotASealingShape Interp.modelReply k1 k2 iv ad [] :=
  ⟨Tacenta.UnitLifecycleResponderFirstReceipt.modelFirstReceipt_aeadRoundTrip, modelReply_openSealUnique,
    modelReply_notASealing_nil⟩

end JointModel

end Tacenta.UnitLifecycleTamperedReply

/-! ## Pins

The constants each result depends on, and the statement of each result and definition, held by the
build.  `attest.py` requires every one of them (`REQUIRED_PINS`, `REQUIRED_STATEMENT_PINS`,
`REQUIRED_PRINT_FORM`). -/

/--
info: 'Tacenta.UnitLifecycleTamperedReply.aeadOpenSealUnique_is' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kdf.hkdf_sha256,
 tacenta_kdf.hmac_sha256,
 tacenta_kem.CT1_LEN,
 tacenta_kem.CT2_LEN,
 tacenta_kem.EK_VECTOR_LEN,
 tacenta_kem.EncapsState,
 tacenta_kem.HEADER_LEN,
 tacenta_kem.IncrementalKeyPair,
 tacenta_kem.encapsulate1,
 tacenta_kem.encapsulate2,
 tacenta_kem.validate_ek,
 zeroize.Zeroizing,
 rand_core_1.error.Error,
 tacenta_boundary.aead.decrypt,
 tacenta_boundary.aead.encrypt,
 tacenta_boundary.dh.PrivateKey,
 tacenta_boundary.dh.PublicKeyBytes,
 tacenta_boundary.dh.is_prime_order_public,
 tacenta_boundary.kem.KeyPair,
 tacenta_boundary.kem.decapsulate,
 tacenta_boundary.kem.encapsulate,
 tacenta_boundary.xeddsa.verify,
 tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_kem.IncrementalKeyPair.generate,
 tacenta_kem.IncrementalKeyPair.header,
 zeroize.Zeroizing.new,
 Array.Insts.ZeroizeZeroize.zeroize,
 Pair.Insts.ZeroizeZeroize.zeroize,
 TupleABC.Insts.ZeroizeZeroize.zeroize,
 alloc.vec.Vec.capacity,
 alloc.vec.Vec.pop,
 alloc.vec.Vec.truncate,
 core.num.Usize.div_ceil,
 core.option.Option.as_mut,
 tacenta_boundary.dh.PrivateKey.agree,
 tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_boundary.dh.PrivateKey.to_bytes,
 tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 zeroize.Zeroize.Blanket.zeroize,
 tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 core.option.Option.Insts.CoreCloneClone.clone,
 tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleTamperedReply.aeadOpenSealUnique_is

/--
info: 'Tacenta.UnitLifecycleTamperedReply.notASealing_is' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kdf.hkdf_sha256,
 tacenta_kdf.hmac_sha256,
 tacenta_kem.CT1_LEN,
 tacenta_kem.CT2_LEN,
 tacenta_kem.EK_VECTOR_LEN,
 tacenta_kem.EncapsState,
 tacenta_kem.HEADER_LEN,
 tacenta_kem.IncrementalKeyPair,
 tacenta_kem.encapsulate1,
 tacenta_kem.encapsulate2,
 tacenta_kem.validate_ek,
 zeroize.Zeroizing,
 rand_core_1.error.Error,
 tacenta_boundary.aead.decrypt,
 tacenta_boundary.aead.encrypt,
 tacenta_boundary.dh.PrivateKey,
 tacenta_boundary.dh.PublicKeyBytes,
 tacenta_boundary.dh.is_prime_order_public,
 tacenta_boundary.kem.KeyPair,
 tacenta_boundary.kem.decapsulate,
 tacenta_boundary.kem.encapsulate,
 tacenta_boundary.xeddsa.verify,
 tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_kem.IncrementalKeyPair.generate,
 tacenta_kem.IncrementalKeyPair.header,
 zeroize.Zeroizing.new,
 Array.Insts.ZeroizeZeroize.zeroize,
 Pair.Insts.ZeroizeZeroize.zeroize,
 TupleABC.Insts.ZeroizeZeroize.zeroize,
 alloc.vec.Vec.capacity,
 alloc.vec.Vec.pop,
 alloc.vec.Vec.truncate,
 core.num.Usize.div_ceil,
 core.option.Option.as_mut,
 tacenta_boundary.dh.PrivateKey.agree,
 tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_boundary.dh.PrivateKey.to_bytes,
 tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 zeroize.Zeroize.Blanket.zeroize,
 tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 core.option.Option.Insts.CoreCloneClone.clone,
 tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleTamperedReply.notASealing_is

/--
info: 'Tacenta.UnitLifecycleTamperedReply.open_none_of_not_sealing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kdf.hkdf_sha256,
 tacenta_kdf.hmac_sha256,
 tacenta_kem.CT1_LEN,
 tacenta_kem.CT2_LEN,
 tacenta_kem.EK_VECTOR_LEN,
 tacenta_kem.EncapsState,
 tacenta_kem.HEADER_LEN,
 tacenta_kem.IncrementalKeyPair,
 tacenta_kem.encapsulate1,
 tacenta_kem.encapsulate2,
 tacenta_kem.validate_ek,
 zeroize.Zeroizing,
 rand_core_1.error.Error,
 tacenta_boundary.aead.decrypt,
 tacenta_boundary.aead.encrypt,
 tacenta_boundary.dh.PrivateKey,
 tacenta_boundary.dh.PublicKeyBytes,
 tacenta_boundary.dh.is_prime_order_public,
 tacenta_boundary.kem.KeyPair,
 tacenta_boundary.kem.decapsulate,
 tacenta_boundary.kem.encapsulate,
 tacenta_boundary.xeddsa.verify,
 tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_kem.IncrementalKeyPair.generate,
 tacenta_kem.IncrementalKeyPair.header,
 zeroize.Zeroizing.new,
 Array.Insts.ZeroizeZeroize.zeroize,
 Pair.Insts.ZeroizeZeroize.zeroize,
 TupleABC.Insts.ZeroizeZeroize.zeroize,
 alloc.vec.Vec.capacity,
 alloc.vec.Vec.pop,
 alloc.vec.Vec.truncate,
 core.num.Usize.div_ceil,
 core.option.Option.as_mut,
 tacenta_boundary.dh.PrivateKey.agree,
 tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_boundary.dh.PrivateKey.to_bytes,
 tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 zeroize.Zeroize.Blanket.zeroize,
 tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 core.option.Option.Insts.CoreCloneClone.clone,
 tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleTamperedReply.open_none_of_not_sealing

/--
info: 'Tacenta.UnitLifecycleTamperedReply.not_notASealing_of_seal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kdf.hkdf_sha256,
 tacenta_kdf.hmac_sha256,
 tacenta_kem.CT1_LEN,
 tacenta_kem.CT2_LEN,
 tacenta_kem.EK_VECTOR_LEN,
 tacenta_kem.EncapsState,
 tacenta_kem.HEADER_LEN,
 tacenta_kem.IncrementalKeyPair,
 tacenta_kem.encapsulate1,
 tacenta_kem.encapsulate2,
 tacenta_kem.validate_ek,
 zeroize.Zeroizing,
 rand_core_1.error.Error,
 tacenta_boundary.aead.decrypt,
 tacenta_boundary.aead.encrypt,
 tacenta_boundary.dh.PrivateKey,
 tacenta_boundary.dh.PublicKeyBytes,
 tacenta_boundary.dh.is_prime_order_public,
 tacenta_boundary.kem.KeyPair,
 tacenta_boundary.kem.decapsulate,
 tacenta_boundary.kem.encapsulate,
 tacenta_boundary.xeddsa.sign,
 tacenta_boundary.xeddsa.verify,
 tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_kem.IncrementalKeyPair.generate,
 tacenta_kem.IncrementalKeyPair.header,
 zeroize.Zeroizing.new,
 Array.Insts.ZeroizeZeroize.zeroize,
 Pair.Insts.ZeroizeZeroize.zeroize,
 TupleABC.Insts.ZeroizeZeroize.zeroize,
 alloc.vec.Vec.capacity,
 alloc.vec.Vec.pop,
 alloc.vec.Vec.truncate,
 core.num.Usize.div_ceil,
 core.option.Option.as_mut,
 tacenta_boundary.dh.PrivateKey.agree,
 tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_boundary.dh.PrivateKey.to_bytes,
 tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 zeroize.Zeroize.Blanket.zeroize,
 tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 core.option.Option.Insts.CoreCloneClone.clone,
 tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleTamperedReply.not_notASealing_of_seal

/--
info: 'Tacenta.UnitLifecycleTamperedReply.replyHeader_length' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleTamperedReply.replyHeader_length

/--
info: 'Tacenta.UnitLifecycleTamperedReply.replyFrame_take' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleTamperedReply.replyFrame_take

/--
info: 'Tacenta.UnitLifecycleTamperedReply.replyFrame_drop' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleTamperedReply.replyFrame_drop

/--
info: 'Tacenta.UnitLifecycleTamperedReply.tampered_reply_model_refusal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleTamperedReply.tampered_reply_model_refusal

/--
info: 'Tacenta.UnitLifecycleTamperedReply.initiator_refuses_tampered_reply' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kdf.hkdf_sha256,
 tacenta_kdf.hmac_sha256,
 tacenta_kem.CT1_LEN,
 tacenta_kem.CT2_LEN,
 tacenta_kem.EK_VECTOR_LEN,
 tacenta_kem.EncapsState,
 tacenta_kem.HEADER_LEN,
 tacenta_kem.IncrementalKeyPair,
 tacenta_kem.encapsulate1,
 tacenta_kem.encapsulate2,
 tacenta_kem.validate_ek,
 zeroize.Zeroizing,
 rand_core_1.error.Error,
 tacenta_boundary.aead.decrypt,
 tacenta_boundary.aead.encrypt,
 tacenta_boundary.dh.PrivateKey,
 tacenta_boundary.dh.PublicKeyBytes,
 tacenta_boundary.dh.is_prime_order_public,
 tacenta_boundary.kem.KeyPair,
 tacenta_boundary.kem.ciphertext_len,
 tacenta_boundary.kem.decapsulate,
 tacenta_boundary.kem.encapsulate,
 tacenta_boundary.xeddsa.sign,
 tacenta_boundary.xeddsa.verify,
 tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_kem.IncrementalKeyPair.generate,
 tacenta_kem.IncrementalKeyPair.header,
 zeroize.Zeroizing.new,
 Array.Insts.ZeroizeZeroize.zeroize,
 Pair.Insts.ZeroizeZeroize.zeroize,
 TupleABC.Insts.ZeroizeZeroize.zeroize,
 alloc.vec.Vec.capacity,
 alloc.vec.Vec.is_empty,
 alloc.vec.Vec.pop,
 alloc.vec.Vec.truncate,
 core.num.Usize.div_ceil,
 core.option.Option.as_mut,
 tacenta_boundary.dh.PrivateKey.agree,
 tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_boundary.dh.PrivateKey.to_bytes,
 tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 tacenta_boundary.kem.KeyPair.public_key,
 zeroize.Zeroize.Blanket.zeroize,
 tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 core.option.Option.Insts.CoreCloneClone.clone,
 core.option.Option.Insts.CoreCmpPartialEqOption.eq,
 tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleTamperedReply.initiator_refuses_tampered_reply

/--
info: 'Tacenta.UnitLifecycleTamperedReply.openModel_ok' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleTamperedReply.openModel_ok

/--
info: 'Tacenta.UnitLifecycleTamperedReply.sealModel_val' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleTamperedReply.sealModel_val

/--
info: 'Tacenta.UnitLifecycleTamperedReply.modelReply_openSealUnique' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleTamperedReply.modelReply_openSealUnique

/--
info: 'Tacenta.UnitLifecycleTamperedReply.modelReply_notASealing_nil' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleTamperedReply.modelReply_notASealing_nil

/--
info: 'Tacenta.UnitLifecycleTamperedReply.modelReply_sealing_excluded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleTamperedReply.modelReply_sealing_excluded

/--
info: 'Tacenta.UnitLifecycleTamperedReply.lenient_roundTrip_not_unique' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleTamperedReply.lenient_roundTrip_not_unique

/--
info: 'Tacenta.UnitLifecycleTamperedReply.tamper_laws_model' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleTamperedReply.tamper_laws_model

set_option pp.deepTerms true
set_option pp.proofs.withType true

/--
info: Tacenta.UnitLifecycleTamperedReply.aeadOpenSealUnique_is : Tacenta.UnitLifecycleTamperedReply.AeadOpenSealUnique ↔
  ∀ (k1 k2 : Std.Array U8 32#usize) (iv : Std.Array U8 16#usize) (c ad : Slice U8) (v : alloc.vec.Vec U8),
    tacenta_boundary.aead.decrypt k1 k2 iv c ad = ok (core.result.Result.Ok v) →
      ∃ ct, tacenta_boundary.aead.encrypt k1 k2 iv v.deref ad = ok ct ∧ ↑ct = ↑c
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleTamperedReply.aeadOpenSealUnique_is

/--
info: Tacenta.UnitLifecycleTamperedReply.notASealing_is : ∀ (k1 k2 iv ad c : Model.Lifecycle.Bytes),
  Tacenta.UnitLifecycleTamperedReply.NotASealing k1 k2 iv ad c ↔
    ∀ (K1 K2 : Std.Array U8 32#usize) (IV : Std.Array U8 16#usize) (pt A : Slice U8) (ct : alloc.vec.Vec U8),
      Tacenta.UnitLifecycleT3.arrayOf K1 = k1 →
        Tacenta.UnitLifecycleT3.arrayOf K2 = k2 →
          Tacenta.UnitLifecycleT3.arrayOf IV = iv →
            Tacenta.UnitLifecycleT3.sliceOf A = ad →
              tacenta_boundary.aead.encrypt K1 K2 IV pt A = ok ct → Tacenta.UnitLifecycleT3.vecOf ct ≠ c
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleTamperedReply.notASealing_is

/--
info: Tacenta.UnitLifecycleTamperedReply.open_none_of_not_sealing : Tacenta.UnitLifecycleTamperedReply.AeadOpenSealUnique →
  ∀ {R : Type} {rc : rand_core_1.RngCore R} {crc : rand_core_1.CryptoRng R} {dh : Tacenta.UnitLifecycleT3.DhView}
    {trace : R → List Model.Lifecycle.Key} {oracle : Model.Lifecycle.Oracle},
    Tacenta.UnitLifecycleDecryptRatchetT3.DecryptOracleOf rc crc dh trace oracle →
      ∀ (k1 k2 iv : Model.Lifecycle.Bytes),
        List.length k1 = 32 →
          List.length k2 = 32 →
            List.length iv = 16 →
              ∀ (c ad : Model.Lifecycle.Bytes),
                List.length c ≤ Usize.max →
                  List.length ad ≤ Usize.max →
                    Tacenta.UnitLifecycleTamperedReply.NotASealing k1 k2 iv ad c → oracle.aeadOpen k1 k2 iv c ad = none
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleTamperedReply.open_none_of_not_sealing

/--
info: @Tacenta.UnitLifecycleTamperedReply.not_notASealing_of_seal : ∀ {R : Type} {rc : rand_core_1.RngCore R}
  {crc : rand_core_1.CryptoRng R} {dh : Tacenta.UnitLifecycleT3.DhView} {kem : Tacenta.UnitLifecycleT3.KemView}
  {trace : R → List Model.Lifecycle.Key} {oracle : Model.Lifecycle.Oracle},
  Tacenta.UnitLifecycleT3.OracleOf rc crc dh kem trace oracle →
    ∀ (k1 k2 iv : Model.Lifecycle.Bytes),
      List.length k1 = 32 →
        List.length k2 = 32 →
          List.length iv = 16 →
            ∀ (pt : Slice U8) (ad : Model.Lifecycle.Bytes),
              List.length ad ≤ Usize.max →
                ¬Tacenta.UnitLifecycleTamperedReply.NotASealing k1 k2 iv ad
                    (oracle.aeadSeal k1 k2 iv (Tacenta.UnitLifecycleT3.sliceOf pt) ad)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleTamperedReply.not_notASealing_of_seal

/--
info: Tacenta.UnitLifecycleTamperedReply.replyHeader_length : ∀ (newPub : Model.State.Key),
  List.length newPub = 32 →
    (Model.CompositeHeader.encode (Tacenta.UnitLifecycleResponderReply.replyComposite newPub)).length = 102
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleTamperedReply.replyHeader_length

/--
info: Tacenta.UnitLifecycleTamperedReply.replyFrame_take : ∀ (oracle : Model.Lifecycle.Oracle) (ad : Model.Lifecycle.Bytes)
  (newPub mk : Model.State.Key) (pt : Model.Lifecycle.Bytes),
  List.length newPub = 32 →
    List.take 102 (Tacenta.UnitLifecycleResponderReply.replyFrame oracle ad newPub mk pt) =
      Model.CompositeHeader.encode (Tacenta.UnitLifecycleResponderReply.replyComposite newPub)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleTamperedReply.replyFrame_take

/--
info: Tacenta.UnitLifecycleTamperedReply.replyFrame_drop : ∀ (oracle : Model.Lifecycle.Oracle) (ad : Model.Lifecycle.Bytes)
  (newPub mk : Model.State.Key) (pt : Model.Lifecycle.Bytes),
  List.length newPub = 32 →
    List.drop 102 (Tacenta.UnitLifecycleResponderReply.replyFrame oracle ad newPub mk pt) =
      oracle.aeadSeal (Model.State.messageKeys mk Model.State.LabelSet.tacenta).1
        (Model.State.messageKeys mk Model.State.LabelSet.tacenta).2.1
        (Model.State.messageKeys mk Model.State.LabelSet.tacenta).2.2 pt
        (Tacenta.UnitLifecycleResponderReplyReceipt.replyAd ad newPub)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleTamperedReply.replyFrame_drop

/--
info: Tacenta.UnitLifecycleTamperedReply.tampered_reply_model_refusal : ∀ (view : Model.Lifecycle.CodewordView)
  (oracleA : Model.Lifecycle.Oracle) (mA : Model.Lifecycle.Session) (a4 peer rkA cksA prk k1 k2 : Model.State.Key)
  (e : ℕ) (auth : Model.Braid.Auth) (dk ekVector : Model.Braid.Bytes) (enc : Model.Braid.Encoder),
  mA.triple = Tacenta.UnitLifecycleResponderFirstReceipt.senderAfterFirst a4 peer rkA cksA prk k1 k2 →
    mA.braid = Model.Braid.BraidState.keysSampled e auth dk ekVector enc →
      ∀ (newPub dSend : Model.State.Key) (cT : Model.Lifecycle.Bytes),
        List.length newPub = 32 →
          Model.Messages.checkKey newPub = some () →
            oracleA.dhAgree mA.ratchetPrivate newPub = some dSend →
              ∀ (c : Model.State.Key) (rest : List Model.State.Key) (x : Model.State.Key),
                oracleA.draws = c :: rest →
                  oracleA.dhAgree c newPub = some x →
                    newPub ≠ peer →
                      oracleA.aeadOpen
                            (Model.State.messageKeys
                                (Tacenta.UnitLifecycleResponderFirstReceipt.firstKey
                                  (Model.State.kdfRk rkA dSend Model.State.LabelSet.tacenta).2 k2)
                                Model.State.LabelSet.tacenta).1
                            (Model.State.messageKeys
                                  (Tacenta.UnitLifecycleResponderFirstReceipt.firstKey
                                    (Model.State.kdfRk rkA dSend Model.State.LabelSet.tacenta).2 k2)
                                  Model.State.LabelSet.tacenta).2.1
                            (Model.State.messageKeys
                                  (Tacenta.UnitLifecycleResponderFirstReceipt.firstKey
                                    (Model.State.kdfRk rkA dSend Model.State.LabelSet.tacenta).2 k2)
                                  Model.State.LabelSet.tacenta).2.2
                            cT (Tacenta.UnitLifecycleResponderReplyReceipt.replyAd mA.identityAd newPub) =
                          none →
                        Model.Lifecycle.decrypt view oracleA mA
                            (Model.CompositeHeader.encodeMessage
                              (Tacenta.UnitLifecycleResponderReply.replyComposite newPub) cT) =
                          { session := mA, result := Except.error Model.Lifecycle.Refusal.aead,
                            oracle :=
                              { draws := rest, braidKem := oracleA.braidKem, dhPublic := oracleA.dhPublic,
                                dhAgree := oracleA.dhAgree, identityValid := oracleA.identityValid,
                                aeadSeal := oracleA.aeadSeal, aeadOpen := oracleA.aeadOpen,
                                kemValid := oracleA.kemValid, kemEncaps := oracleA.kemEncaps,
                                kemDecaps := oracleA.kemDecaps, sigVerify := oracleA.sigVerify,
                                sigSign := oracleA.sigSign } }
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleTamperedReply.tampered_reply_model_refusal

/--
info: @Tacenta.UnitLifecycleTamperedReply.initiator_refuses_tampered_reply : ∀ [Tacenta.SessionUnitT1.DerivedKeysModel]
  {R E F : Type},
  Tacenta.UnitLifecycleTamperedReply.AeadOpenSealUnique →
    ∀ (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R) (trace : R → List Model.Lifecycle.Key)
      (dh : Tacenta.UnitLifecycleT3.DhView) (kem : Tacenta.UnitLifecycleT3.KemView)
      (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle),
      Tacenta.UnitLifecycleT3.BraidSendRefinementContracts rc oracle.braidKem →
        Tacenta.UnitLifecycleT3.TripleSendRefinementContracts →
          Tacenta.UnitLifecycleT1.AeadSealBounded →
            Tacenta.UnitLifecycleT1.DhCodecTotal →
              Tacenta.UnitLifecycleT3.OracleOf rc crc dh kem trace oracle →
                Tacenta.UnitLifecycleT3.DhCodecOf dh →
                  Tacenta.UnitLifecycleT3.CodewordViewSendOf view →
                    Tacenta.SessionUnitT3.ZeroizingRoundTrips80 →
                      Tacenta.UnitLifecycleT3.ZeroizingRoundTrips (Std.Array U8 32#usize) →
                        Tacenta.UnitLifecycleT3.ZeroizingRoundTrips
                            (Std.Array U8 32#usize × Std.Array U8 32#usize × Std.Array U8 16#usize) →
                          Tacenta.UnitLifecycleEstablishedEncrypt.KeyGenSeededFor oracle.braidKem rc crc trace →
                            Tacenta.UnitLifecycleEstablishedEncrypt.KeyGenSizesOf oracle.braidKem →
                              Tacenta.UnitLifecycleEstablishInitiatorShape.KemCiphertextLenOf →
                                Tacenta.UnitLifecycleRestoredSession.KemCiphertextLenBound →
                                  ∀ (rcE : rand_core_1.RngCore E) (crcE : rand_core_1.CryptoRng E)
                                    (ourA : lifecycle.Identity) (bundleA : lifecycle.PublishedBundle)
                                    (expected : tacenta_boundary.dh.PublicKeyBytes) (rng0 rng1 : E)
                                    (s : lifecycle.Session),
                                    lifecycle.establish_initiator_for rcE crcE ourA bundleA expected rng0 =
                                        ok (core.result.Result.Ok s, rng1) →
                                      ∀
                                        (q :
                                          Tacenta.UnitLifecycleResponderFirstFrame.InitiatorSecretParts rcE crcE ourA
                                            bundleA),
                                        s = q.session →
                                          ∀ (plaintext : Slice U8),
                                            (↑plaintext).length + 65770 ≤ Usize.max →
                                              ∀ (rng : R),
                                                trace rng = oracle.draws →
                                                  ∀ (d1 d2 : Model.Lifecycle.Key) (rest : List Model.Lifecycle.Key),
                                                    trace rng = d1 :: d2 :: rest →
                                                      ∀ (bytes : alloc.vec.Vec U8) (s' : lifecycle.Session) (rng' : R),
                                                        lifecycle.Session.encrypt rc crc s plaintext rng =
                                                            ok (core.result.Result.Ok bytes, s', rng') →
                                                          Tacenta.UnitLifecycleT1.DecryptRatchetContracts rc →
                                                            Tacenta.UnitLifecycleDecryptRatchetT3.DecryptRatchetAgreements
                                                                oracle.braidKem →
                                                              ∀ (dA : Model.Lifecycle.Key)
                                                                (restA : List Model.Lifecycle.Key),
                                                                trace rng' = dA :: restA →
                                                                  ∀ (rcB : rand_core_1.RngCore F)
                                                                    (crcB : rand_core_1.CryptoRng F)
                                                                    (contracts :
                                                                      Tacenta.UnitLifecycleT1.EstablishResponderContracts
                                                                        rcB),
                                                                    Tacenta.UnitLifecycleEstablishInitiatorShape.DhPublicValid →
                                                                      Tacenta.UnitLifecycleResponderFirstFrame.DhAgreeSymmetric →
                                                                        Tacenta.UnitLifecycleResponderFirstReceipt.DhAgreeContributory →
                                                                          Tacenta.UnitLifecycleResponderFirstReceipt.AeadRoundTrip →
                                                                            Tacenta.UnitLifecycleSessionCodec.DhPublicBytesRoundTrip →
                                                                              Tacenta.UnitHeadroomInvariant.OptionEqU64Shape
                                                                                  @core.option.Option.Insts.CoreCmpPartialEqOption.eq →
                                                                                ∀
                                                                                  (traceB :
                                                                                    F → List Model.Lifecycle.Key)
                                                                                  (oracleB : Model.Lifecycle.Oracle),
                                                                                  Tacenta.UnitLifecycleT3.OracleOf rcB
                                                                                      crcB dh kem traceB oracleB →
                                                                                    Tacenta.UnitLifecycleT3.BraidSendRefinementContracts
                                                                                        rcB oracleB.braidKem →
                                                                                      Tacenta.UnitLifecycleDecryptRatchetT3.DecryptRatchetAgreements
                                                                                          oracleB.braidKem →
                                                                                        ∀ (ourB : lifecycle.Identity)
                                                                                          (storeB :
                                                                                            lifecycle.PrekeyStore),
                                                                                          storeB.publish = ok bundleA →
                                                                                            ourB.public =
                                                                                                ok
                                                                                                  storeB.identity_public →
                                                                                              Tacenta.UnitLifecycleResponderFirstFrame.PrekeyIdsDistinct
                                                                                                  storeB →
                                                                                                Tacenta.UnitLifecycleResponderFirstFrame.FirstKemAgrees
                                                                                                    storeB
                                                                                                    bundleA.kem_prekey_id
                                                                                                    q.kemCiphertext
                                                                                                    q.kemSecret →
                                                                                                  ∀ (rngB : F),
                                                                                                    traceB rngB =
                                                                                                        oracleB.draws →
                                                                                                      ∀
                                                                                                        (dB :
                                                                                                          Model.Lifecycle.Key)
                                                                                                        (restB :
                                                                                                          List
                                                                                                            Model.Lifecycle.Key),
                                                                                                        traceB rngB =
                                                                                                            dB ::
                                                                                                              restB →
                                                                                                          ∀
                                                                                                            (ptB :
                                                                                                              alloc.vec.Vec
                                                                                                                U8)
                                                                                                            (sB' :
                                                                                                              lifecycle.Session)
                                                                                                            (storeB' :
                                                                                                              lifecycle.PrekeyStore)
                                                                                                            (rngB' : F),
                                                                                                            lifecycle.establish_responder
                                                                                                                  rcB
                                                                                                                  crcB
                                                                                                                  ourB
                                                                                                                  storeB
                                                                                                                  bytes.deref
                                                                                                                  rngB =
                                                                                                                ok
                                                                                                                  (core.result.Result.Ok
                                                                                                                      (sB',
                                                                                                                        ptB),
                                                                                                                    storeB',
                                                                                                                    rngB') →
                                                                                                              ∀
                                                                                                                (ptR :
                                                                                                                  Slice
                                                                                                                    U8),
                                                                                                                102 +
                                                                                                                      ((↑ptR).length +
                                                                                                                        48) ≤
                                                                                                                    Usize.max →
                                                                                                                  ∀
                                                                                                                    (rngR :
                                                                                                                      F),
                                                                                                                    oracleB.dhPublic
                                                                                                                          dB ≠
                                                                                                                        Tacenta.UnitLifecycleT3.arrayOf
                                                                                                                          q.peerRatchetBytes →
                                                                                                                      ∃
                                                                                                                        dSend
                                                                                                                        bytesR
                                                                                                                        sB''
                                                                                                                        ptA
                                                                                                                        s''
                                                                                                                        rngA',
                                                                                                                        oracleB.dhAgree
                                                                                                                              dB
                                                                                                                              (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                                                q.ratchetBytes) =
                                                                                                                            some
                                                                                                                              dSend ∧
                                                                                                                          lifecycle.Session.encrypt
                                                                                                                                rcB
                                                                                                                                crcB
                                                                                                                                sB'
                                                                                                                                ptR
                                                                                                                                rngR =
                                                                                                                              ok
                                                                                                                                (core.result.Result.Ok
                                                                                                                                    bytesR,
                                                                                                                                  sB'',
                                                                                                                                  rngR) ∧
                                                                                                                            Tacenta.UnitLifecycleT3.vecOf
                                                                                                                                  bytesR =
                                                                                                                                Tacenta.UnitLifecycleResponderReply.replyFrame
                                                                                                                                  oracleB
                                                                                                                                  (Tacenta.UnitLifecycleT3.vecOf
                                                                                                                                    q.identityAd)
                                                                                                                                  (oracleB.dhPublic
                                                                                                                                    dB)
                                                                                                                                  (Tacenta.UnitLifecycleResponderFirstReceipt.firstKey
                                                                                                                                    (Model.State.kdfRk
                                                                                                                                        (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                                                          q.rootKey)
                                                                                                                                        dSend
                                                                                                                                        Model.State.LabelSet.tacenta).2
                                                                                                                                    (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                                                      q.sparseReceive))
                                                                                                                                  (Tacenta.UnitLifecycleT3.sliceOf
                                                                                                                                    ptR) ∧
                                                                                                                              lifecycle.Session.decrypt
                                                                                                                                    rc
                                                                                                                                    crc
                                                                                                                                    s'
                                                                                                                                    bytesR.deref
                                                                                                                                    rng' =
                                                                                                                                  ok
                                                                                                                                    (core.result.Result.Ok
                                                                                                                                        ptA,
                                                                                                                                      s'',
                                                                                                                                      rngA') ∧
                                                                                                                                ↑ptA =
                                                                                                                                    ↑ptR ∧
                                                                                                                                  trace
                                                                                                                                        rngA' =
                                                                                                                                      restA ∧
                                                                                                                                    ¬Tacenta.UnitLifecycleTamperedReply.NotASealing
                                                                                                                                          (Model.State.messageKeys
                                                                                                                                              (Tacenta.UnitLifecycleResponderFirstReceipt.firstKey
                                                                                                                                                (Model.State.kdfRk
                                                                                                                                                    (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                                                                      q.rootKey)
                                                                                                                                                    dSend
                                                                                                                                                    Model.State.LabelSet.tacenta).2
                                                                                                                                                (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                                                                  q.sparseReceive))
                                                                                                                                              Model.State.LabelSet.tacenta).1
                                                                                                                                          (Model.State.messageKeys
                                                                                                                                                (Tacenta.UnitLifecycleResponderFirstReceipt.firstKey
                                                                                                                                                  (Model.State.kdfRk
                                                                                                                                                      (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                                                                        q.rootKey)
                                                                                                                                                      dSend
                                                                                                                                                      Model.State.LabelSet.tacenta).2
                                                                                                                                                  (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                                                                    q.sparseReceive))
                                                                                                                                                Model.State.LabelSet.tacenta).2.1
                                                                                                                                          (Model.State.messageKeys
                                                                                                                                                (Tacenta.UnitLifecycleResponderFirstReceipt.firstKey
                                                                                                                                                  (Model.State.kdfRk
                                                                                                                                                      (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                                                                        q.rootKey)
                                                                                                                                                      dSend
                                                                                                                                                      Model.State.LabelSet.tacenta).2
                                                                                                                                                  (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                                                                    q.sparseReceive))
                                                                                                                                                Model.State.LabelSet.tacenta).2.2
                                                                                                                                          (Tacenta.UnitLifecycleResponderReplyReceipt.replyAd
                                                                                                                                            (Tacenta.UnitLifecycleT3.vecOf
                                                                                                                                              q.identityAd)
                                                                                                                                            (oracleB.dhPublic
                                                                                                                                              dB))
                                                                                                                                          (List.drop
                                                                                                                                            102
                                                                                                                                            (Tacenta.UnitLifecycleT3.vecOf
                                                                                                                                              bytesR)) ∧
                                                                                                                                      ∀
                                                                                                                                        (frame :
                                                                                                                                          Slice
                                                                                                                                            U8)
                                                                                                                                        (cT :
                                                                                                                                          Model.Lifecycle.Bytes),
                                                                                                                                        Tacenta.UnitLifecycleT3.sliceOf
                                                                                                                                              frame =
                                                                                                                                            List.take
                                                                                                                                                102
                                                                                                                                                (Tacenta.UnitLifecycleT3.vecOf
                                                                                                                                                  bytesR) ++
                                                                                                                                              cT →
                                                                                                                                          Tacenta.UnitLifecycleTamperedReply.NotASealing
                                                                                                                                              (Model.State.messageKeys
                                                                                                                                                  (Tacenta.UnitLifecycleResponderFirstReceipt.firstKey
                                                                                                                                                    (Model.State.kdfRk
                                                                                                                                                        (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                                                                          q.rootKey)
                                                                                                                                                        dSend
                                                                                                                                                        Model.State.LabelSet.tacenta).2
                                                                                                                                                    (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                                                                      q.sparseReceive))
                                                                                                                                                  Model.State.LabelSet.tacenta).1
                                                                                                                                              (Model.State.messageKeys
                                                                                                                                                    (Tacenta.UnitLifecycleResponderFirstReceipt.firstKey
                                                                                                                                                      (Model.State.kdfRk
                                                                                                                                                          (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                                                                            q.rootKey)
                                                                                                                                                          dSend
                                                                                                                                                          Model.State.LabelSet.tacenta).2
                                                                                                                                                      (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                                                                        q.sparseReceive))
                                                                                                                                                    Model.State.LabelSet.tacenta).2.1
                                                                                                                                              (Model.State.messageKeys
                                                                                                                                                    (Tacenta.UnitLifecycleResponderFirstReceipt.firstKey
                                                                                                                                                      (Model.State.kdfRk
                                                                                                                                                          (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                                                                            q.rootKey)
                                                                                                                                                          dSend
                                                                                                                                                          Model.State.LabelSet.tacenta).2
                                                                                                                                                      (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                                                                        q.sparseReceive))
                                                                                                                                                    Model.State.LabelSet.tacenta).2.2
                                                                                                                                              (Tacenta.UnitLifecycleResponderReplyReceipt.replyAd
                                                                                                                                                (Tacenta.UnitLifecycleT3.vecOf
                                                                                                                                                  q.identityAd)
                                                                                                                                                (oracleB.dhPublic
                                                                                                                                                  dB))
                                                                                                                                              cT →
                                                                                                                                            ∃
                                                                                                                                              rngT,
                                                                                                                                              lifecycle.Session.decrypt
                                                                                                                                                    rc
                                                                                                                                                    crc
                                                                                                                                                    s'
                                                                                                                                                    frame
                                                                                                                                                    rng' =
                                                                                                                                                  ok
                                                                                                                                                    (core.result.Result.Err
                                                                                                                                                        lifecycle.Error.Aead,
                                                                                                                                                      s',
                                                                                                                                                      rngT) ∧
                                                                                                                                                trace
                                                                                                                                                    rngT =
                                                                                                                                                  restA
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleTamperedReply.initiator_refuses_tampered_reply

/--
info: Tacenta.UnitLifecycleTamperedReply.openModel_ok : ∀ (c : Slice U8) (v : alloc.vec.Vec U8),
  Tacenta.UnitOracleModel.openModel c = core.result.Result.Ok v → ↑c = 0#u8 :: ↑v
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleTamperedReply.openModel_ok

/--
info: Tacenta.UnitLifecycleTamperedReply.sealModel_val : ∀ (p : Slice U8),
  (↑p).length + 1 ≤ Usize.max → ↑(Tacenta.UnitOracleModel.sealModel p) = 0#u8 :: ↑p
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleTamperedReply.sealModel_val

/--
info: Tacenta.UnitLifecycleTamperedReply.modelReply_openSealUnique : Tacenta.UnitLifecycleTamperedReply.AeadOpenSealUniqueShape
  Tacenta.UnitLifecycleResponderReplyReceipt.Interp.modelReply
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleTamperedReply.modelReply_openSealUnique

/--
info: Tacenta.UnitLifecycleTamperedReply.modelReply_notASealing_nil : ∀ (k1 k2 iv ad : Model.Lifecycle.Bytes),
  Tacenta.UnitLifecycleTamperedReply.NotASealingShape Tacenta.UnitLifecycleResponderReplyReceipt.Interp.modelReply k1 k2
    iv ad []
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleTamperedReply.modelReply_notASealing_nil

/--
info: Tacenta.UnitLifecycleTamperedReply.modelReply_sealing_excluded : ∀ (k1 k2 iv ad : Model.Lifecycle.Bytes),
  List.length k1 = 32 →
    List.length k2 = 32 →
      List.length iv = 16 →
        List.length ad ≤ Usize.max →
          ¬Tacenta.UnitLifecycleTamperedReply.NotASealingShape
              Tacenta.UnitLifecycleResponderReplyReceipt.Interp.modelReply k1 k2 iv ad [0]
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleTamperedReply.modelReply_sealing_excluded

/--
info: Tacenta.UnitLifecycleTamperedReply.lenient_roundTrip_not_unique : Tacenta.UnitLifecycleResponderFirstReceipt.AeadRoundTripShape
    Tacenta.UnitLifecycleTamperedReply.Interp.modelLenient ∧
  ¬Tacenta.UnitLifecycleTamperedReply.AeadOpenSealUniqueShape Tacenta.UnitLifecycleTamperedReply.Interp.modelLenient
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleTamperedReply.lenient_roundTrip_not_unique

/--
info: Tacenta.UnitLifecycleTamperedReply.tamper_laws_model : Tacenta.UnitLifecycleResponderFirstReceipt.AeadRoundTripShape
    Tacenta.UnitLifecycleResponderReplyReceipt.Interp.modelReply ∧
  Tacenta.UnitLifecycleTamperedReply.AeadOpenSealUniqueShape
      Tacenta.UnitLifecycleResponderReplyReceipt.Interp.modelReply ∧
    ∀ (k1 k2 iv ad : Model.Lifecycle.Bytes),
      Tacenta.UnitLifecycleTamperedReply.NotASealingShape Tacenta.UnitLifecycleResponderReplyReceipt.Interp.modelReply
        k1 k2 iv ad []
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleTamperedReply.tamper_laws_model

/--
info: def Tacenta.UnitLifecycleTamperedReply.AeadOpenSealUniqueShape : Tacenta.UnitSatisfiabilityJoint.Interp → Prop :=
fun I =>
  ∀ (k1 k2 : Std.Array U8 32#usize) (iv : Std.Array U8 16#usize) (c ad : Slice U8) (v : alloc.vec.Vec U8),
    I.aeadDecrypt k1 k2 iv c ad = ok (core.result.Result.Ok v) →
      ∃ ct, I.aeadEncrypt k1 k2 iv v.deref ad = ok ct ∧ ↑ct = ↑c
-/
#guard_msgs in
#print Tacenta.UnitLifecycleTamperedReply.AeadOpenSealUniqueShape

/--
info: def Tacenta.UnitLifecycleTamperedReply.AeadOpenSealUnique : Prop :=
Tacenta.UnitLifecycleTamperedReply.AeadOpenSealUniqueShape Tacenta.UnitSatisfiabilityJoint.Interp.real
-/
#guard_msgs in
#print Tacenta.UnitLifecycleTamperedReply.AeadOpenSealUnique

/--
info: def Tacenta.UnitLifecycleTamperedReply.NotASealingShape : Tacenta.UnitSatisfiabilityJoint.Interp →
  Model.Lifecycle.Bytes →
    Model.Lifecycle.Bytes → Model.Lifecycle.Bytes → Model.Lifecycle.Bytes → Model.Lifecycle.Bytes → Prop :=
fun I k1 k2 iv ad c =>
  ∀ (K1 K2 : Std.Array U8 32#usize) (IV : Std.Array U8 16#usize) (pt A : Slice U8) (ct : alloc.vec.Vec U8),
    Tacenta.UnitLifecycleT3.arrayOf K1 = k1 →
      Tacenta.UnitLifecycleT3.arrayOf K2 = k2 →
        Tacenta.UnitLifecycleT3.arrayOf IV = iv →
          Tacenta.UnitLifecycleT3.sliceOf A = ad →
            I.aeadEncrypt K1 K2 IV pt A = ok ct → Tacenta.UnitLifecycleT3.vecOf ct ≠ c
-/
#guard_msgs in
#print Tacenta.UnitLifecycleTamperedReply.NotASealingShape

/--
info: def Tacenta.UnitLifecycleTamperedReply.NotASealing : Model.Lifecycle.Bytes →
  Model.Lifecycle.Bytes → Model.Lifecycle.Bytes → Model.Lifecycle.Bytes → Model.Lifecycle.Bytes → Prop :=
fun k1 k2 iv ad c =>
  Tacenta.UnitLifecycleTamperedReply.NotASealingShape Tacenta.UnitSatisfiabilityJoint.Interp.real k1 k2 iv ad c
-/
#guard_msgs in
#print Tacenta.UnitLifecycleTamperedReply.NotASealing

/--
info: def Tacenta.UnitLifecycleTamperedReply.openLenient : Slice U8 →
  core.result.Result (alloc.vec.Vec U8) tacenta_boundary.aead.DecryptError :=
fun c =>
  if ↑c = [] then core.result.Result.Err () else core.result.Result.Ok ⟨(↑c).tail, (⋯ : (↑c).tail.length ≤ Usize.max)⟩
-/
#guard_msgs in
#print Tacenta.UnitLifecycleTamperedReply.openLenient

/--
info: def Tacenta.UnitLifecycleTamperedReply.Interp.modelLenient : Tacenta.UnitSatisfiabilityJoint.Interp :=
have __src := Tacenta.UnitLifecycleResponderReplyReceipt.Interp.modelReply;
{ PrivateKey := __src.PrivateKey, PublicKeyBytes := __src.PublicKeyBytes, KemKeyPair := __src.KemKeyPair,
  IncrementalKeyPair := __src.IncrementalKeyPair, EncapsState := __src.EncapsState, Zeroizing := __src.Zeroizing,
  dhPrivFromBytes := __src.dhPrivFromBytes, dhPrivPublicKey := __src.dhPrivPublicKey, dhPrivAgree := __src.dhPrivAgree,
  dhPrivToBytes := __src.dhPrivToBytes, dhPubFromBytes := __src.dhPubFromBytes, dhPubAsBytes := __src.dhPubAsBytes,
  dhPubEq := __src.dhPubEq, dhIsPrimeOrderPublic := __src.dhIsPrimeOrderPublic, aeadEncrypt := __src.aeadEncrypt,
  aeadDecrypt := fun x x_1 x_2 c x_3 => ok (Tacenta.UnitLifecycleTamperedReply.openLenient c),
  kemEncapsulate := @Tacenta.UnitSatisfiabilityJoint.Interp.kemEncapsulate __src,
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
#print Tacenta.UnitLifecycleTamperedReply.Interp.modelLenient
