import Translation.UnitLifecycleResponderReplyReceipt

/-!
# The initiator refuses a tampered reply: `Session::decrypt` of the reply with its ciphertext replaced

`UnitLifecycleResponderReplyReceipt` shows that, on the run of the initiator's first send, the responder's receipt of
it and the responder's reply, the initiator's public `Session::decrypt` at the session `s'` its first `encrypt` left,
from the source `rng'` that `encrypt` left, accepts the reply's bytes `bytesR`.  This module takes, on the same run,
every frame that keeps the reply's header (its first 102 bytes) and carries in place of the reply's ciphertext bytes
`cT` that carry no HMAC-SHA256 tag under the reply's MAC key and associated data, and shows that the same `decrypt`, at
the same `s'` from the same `rng'`, refuses it with `Aead`, takes exactly the one draw the honest receipt takes, and
leaves the session as it was.  It rests on one new assumed law about the boundary AEAD, `AeadOpenChecksTag`, and one
new per-run premise about the frame, `NotTagged`.  Like every encrypt result here, it is conditional on the seal's
totality contracts (`AeadSealBounded` and the seal clause of `OracleOf`), which have no length premise and are false of
the shipping seal at the top of the length range (`LIMITATIONS.md`, the totality row).

## How

* `open_none_of_not_tagged` (bridge): under `AeadOpenChecksTag` and the decrypt oracle record's open clause, the
  oracle's open of bytes that carry no tag under the MAC key and associated data is `none`.
* `not_notTagged_of_seal` (bridge): under `AeadOpenChecksTag`, `AeadRoundTrip` and the oracle record's seal clause,
  the oracle's seal of a plaintext that leaves room for the seal carries its tag.
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

* `initiator_refuses_tampered_reply`: under the hypotheses of `initiator_receives_reply` and `AeadOpenChecksTag`, the
  responder's `encrypt` returns `bytesR` and the initiator's `decrypt` of `bytesR` at `s'` from `rng'` returns `Ok` of
  the responder's plaintext, taking exactly the draw `dA`; the reply's own ciphertext (the bytes after its first 102)
  carries its tag, so `NotTagged` excludes it; and for every slice `frame` whose bytes are the first 102 bytes of
  `bytesR` followed by bytes `cT` with `NotTagged` under the reply's MAC key and associated data, the same call on
  `frame` returns `Err(Aead)` with the session `s'` unchanged and a source after exactly the draw `dA`.
* `notTagged_of_short`, `tagMatches_append`: every ciphertext of fewer than 32 bytes meets the premise, under every key
  and associated data, at the real constants included; no body followed by its tag does.
* `tagged_reply_laws_model`, `tamper_laws_model`: every law of the reply's receipt, the round trip and the new law hold
  in one interpretation, `Interp.modelTagged`, whose toy AEAD binds the MAC key and the associated data, and the empty
  ciphertext meets the premise there.
* `taggedLenient_roundTrip_not_checksTag`: an interpretation whose open skips the tag check meets `AeadRoundTripShape`
  and fails `AeadOpenChecksTagShape`: the new law is not implied by the round trip.
* `taggedTop_checksTag_not_openSealUnique`: with a seal that fails once plaintext, associated data and tag pass
  `Usize.max / 2` (`isize::MAX` at both widths), the toy meets the new law and refutes the earlier one,
  `AeadOpenSealUniqueShape`, which is kept only for this contrast.

## The laws and premises

* `AeadOpenChecksTag` (new, **assumed**): `AeadOpenChecksTagShape` at the real constants.  If the boundary's `decrypt`
  of `c` under keys, IV and associated data `ad` returns a plaintext, then the last 32 bytes of `c` are `Model.Kdf.hmac`
  of the MAC key over `ad` followed by the bytes before them (`TagMatches`).  It says what an accepted ciphertext
  carries, not who can compute one, and mentions no seal and no length.  It is true of the shipping open by reading of
  `tacenta-core/boundary/src/aead.rs`, and not proved: the open refuses fewer than 32 bytes, compares the full 32-byte
  tag with RustCrypto `Mac::verify_slice` before it decrypts, and `hmac` 0.12.1 over `sha2` 0.10.9 computes RFC 2104
  HMAC-SHA256, which `Model.Kdf.hmac` defines (checked against RFC 4231 examples by `native_decide` in `tacenta-model`,
  not in any proof's base).  It would be false of a truncated or short-circuit comparison, of a tag over other bytes
  than `ad` and the ciphertext, or of an open that accepted on any other condition.  It is the AEAD half of
  REQ-AUTH-06.  The model: `Interp.modelTagged`, whose toy seal appends the model's HMAC tag and whose open checks it.
* `NotTagged` (new, **per-run premise**): the replaced bytes `cT` do not carry that tag under the reply's MAC key and
  associated data.  It is a condition on bytes, the same at every interpretation, not a law.  That an attacker who does
  not hold the message key cannot produce bytes that carry it is the unforgeability of HMAC-SHA256, which no theorem
  here states; this premise is where that assumption sits.  Together the law and the premise say no more than that the
  boundary's `decrypt` refuses those bytes under that key and that associated data; what the theorem adds is the
  session around that call: that the call reaches the boundary's open with exactly the reply's message keys and
  associated data, and that the refusal is `Aead`, leaves the session as it was and takes one draw.
* The other premises are those of `initiator_receives_reply`, unchanged, `hfreshB` and `AeadSealBounded` included.
* The earlier law, `AeadOpenSealUnique` (an opened ciphertext reseals to itself), is no longer assumed: it was false of
  the shipping functions at the top of the length range and under memory exhaustion, because the seal copies
  `ad ‖ ct` into one allocation and the open does not.

## Trust

`initiator_refuses_tampered_reply` rests on the kernel and opaque constants of the unit (pins below), as
`initiator_receives_reply` does; it lists no compiler-trust axiom.  `TagMatches` is irreducible, so that Lean compares
two mentions of it by their arguments and never evaluates the HMAC to tell them apart.

## Non-vacuity

`tagged_reply_laws_model` and `tamper_laws_model` put every law the theorem takes in `Interp.modelTagged`, which is
`Interp.modelReply` with a toy AEAD that binds the key and the associated data.  It encrypts nothing, so it shows the
laws are satisfiable together, not that any AEAD is confidential.  The premise is met at every interpretation, the real
constants included, by every ciphertext shorter than 32 bytes (`notTagged_of_short`), so the headline applies at the
real constants to the reply's header followed by up to 31 arbitrary bytes.  The premise excludes every body followed by
its tag (`tagMatches_append`) and the reply's own ciphertext (a conjunct of the headline), so the refusal and the honest
receipt cannot both apply to one frame.  The run's other premises are reached at the real constants under the laws by
`first_send_reply_receipt_reachable`.

## What it does not show

* That the shipping AEAD meets `AeadOpenChecksTag`: it is assumed, by reading, not proved; an independent verified
  implementation proves the same shape, a bad tag refused, of its own code and not of the shipping one.
* That a frame an attacker can produce meets `NotTagged`: that is the unforgeability of HMAC-SHA256, not stated.
* A frame whose tag verifies but whose padding is refused: refused by the shipping open, by reading, but outside the
  premise.
* That the responder's `encrypt` returns `bytesR` for reply plaintexts near `isize::MAX`, which the shipping seal does
  not: `AeadSealBounded` is assumed for every length; see `LIMITATIONS.md`, the totality row.
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

/-- The bytes `c` carry the full HMAC-SHA256 tag under `k2` over `ad` and the bytes before the tag: the last 32
bytes of `c` are `Model.Kdf.hmac k2 (ad ++ the rest)`.  When `c` is shorter than 32 bytes, `c.length - 32` is zero,
the "last 32 bytes" are all of `c`, and no 32-byte tag equals them.  Irreducible, so that Lean compares two
mentions by their arguments and never evaluates the HMAC to tell them apart; the proofs unfold it by name. -/
@[irreducible] def TagMatches (k2 ad c : Model.Lifecycle.Bytes) : Prop :=
  c.drop (c.length - 32) = Model.Kdf.hmac k2 (ad ++ c.take (c.length - 32))

/-- The boundary AEAD's open checks the full tag, over an interpretation `I`: if opening `c` under keys, IV and
associated data `ad` returns a plaintext, then `c` carries the HMAC-SHA256 tag under the MAC key `k2` over `ad` and
the bytes before the tag.  It says what an accepted ciphertext carries, not who can compute one. -/
def AeadOpenChecksTagShape (I : Interp) : Prop :=
  ∀ (k1 k2 : Array U8 32#usize) (iv : Array U8 16#usize) (c ad : Slice U8) (v : alloc.vec.Vec U8),
    I.aeadDecrypt k1 k2 iv c ad = ok (core.result.Result.Ok v) →
    TagMatches (arrayOf k2) (sliceOf ad) (sliceOf c)

/-- **Assumed law**: `AeadOpenChecksTagShape` at the real constants. -/
def AeadOpenChecksTag : Prop := AeadOpenChecksTagShape Interp.real

/-- At the real constants, `AeadOpenChecksTag` is the statement about the real `decrypt`. -/
theorem aeadOpenChecksTag_is : AeadOpenChecksTag ↔
    ∀ (k1 k2 : Array U8 32#usize) (iv : Array U8 16#usize) (c ad : Slice U8) (v : alloc.vec.Vec U8),
      tacenta_boundary.aead.decrypt k1 k2 iv c ad = ok (core.result.Result.Ok v) →
      TagMatches (arrayOf k2) (sliceOf ad) (sliceOf c) :=
  Iff.rfl

/-- **Per-run premise**: the bytes `c` carry no valid tag under `k2` over `ad`.  A condition on bytes, the same at
every interpretation. -/
def NotTagged (k2 ad c : Model.Lifecycle.Bytes) : Prop := ¬ TagMatches k2 ad c

/-- **Bytes shorter than a tag carry none**: the premise holds of every ciphertext of fewer than 32 bytes, under
every key and associated data, at every interpretation (the real constants included, since the premise names
none). -/
theorem notTagged_of_short (k2 ad c : Model.Lifecycle.Bytes) (h : c.length < 32) : NotTagged k2 ad c := by
  intro ht
  unfold TagMatches at ht
  have h1 := congrArg List.length ht
  rw [Model.Kdf.hmac_length] at h1
  simp only [List.length_drop] at h1
  simp [Model.Kdf.hashLen] at h1
  omega

/-- **Bytes made of a body and the tag of it carry that tag**: the premise excludes every byte string that is a body
followed by `Model.Kdf.hmac k2 (ad ++ body)`. -/
theorem tagMatches_append (k2 ad body : Model.Lifecycle.Bytes) :
    TagMatches k2 ad (body ++ Model.Kdf.hmac k2 (ad ++ body)) := by
  unfold TagMatches
  have hl : (body ++ Model.Kdf.hmac k2 (ad ++ body)).length - 32 = body.length := by
    simp [Model.Kdf.hmac_length, Model.Kdf.hashLen]
  rw [hl, List.drop_left, List.take_left]

/-- The earlier law, an opened ciphertext reseals to itself, over an interpretation `I`: if opening `c` with keys,
IV and associated data `ad` returns `v`, then sealing `v` with the same keys, IV and associated data returns a
ciphertext with the bytes of `c`.  Not assumed by any theorem: false of the shipping functions at the top of the
length range; `taggedTop_checksTag_not_openSealUnique` shows a seal that fails there refutes it while the tag law
holds. -/
def AeadOpenSealUniqueShape (I : Interp) : Prop :=
  ∀ (k1 k2 : Array U8 32#usize) (iv : Array U8 16#usize) (c ad : Slice U8) (v : alloc.vec.Vec U8),
    I.aeadDecrypt k1 k2 iv c ad = ok (core.result.Result.Ok v) →
    ∃ ct, I.aeadEncrypt k1 k2 iv (alloc.vec.Vec.deref v) ad = ok ct ∧ ct.val = c.val

/-! ## The open, through the oracle record -/

section Bridges

open Tacenta.UnitLifecycleDecryptRatchetT3 (DecryptOracleOf)
open Tacenta.UnitLifecycleResponderFirstReceipt (AeadRoundTrip)

/-- **An oracle open of bytes that carry no tag is refused**: under `AeadOpenChecksTag` and the decrypt oracle
record's open clause, for keys of 32, 32 and 16 bytes and a ciphertext and associated data that fit a slice, if the
ciphertext's bytes carry no HMAC-SHA256 tag under the MAC key over the associated data (`NotTagged`), then the
oracle's open of them returns `none`. -/
theorem open_none_of_not_tagged (hu : AeadOpenChecksTag) {R : Type} {rc : rand_core_1.RngCore R}
    {crc : rand_core_1.CryptoRng R} {dh : DhView} {trace : R → List Model.Lifecycle.Key}
    {oracle : Model.Lifecycle.Oracle} (oracleOf : DecryptOracleOf rc crc dh trace oracle)
    (k1 k2 iv : Model.Lifecycle.Bytes) (hk1 : k1.length = 32) (hk2 : k2.length = 32) (hiv : iv.length = 16)
    (c ad : Model.Lifecycle.Bytes) (hc : c.length ≤ Usize.max) (had : ad.length ≤ Usize.max)
    (hnt : NotTagged k2 ad c) :
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
    have ht := hu K1 K2 IV C A v hres
    rw [hC, hA, show arrayOf K2 = k2 from arrayOf_arrayOfBytes (n := 32#usize) k2 hk2] at ht
    exact absurd ht hnt

open Tacenta.UnitLifecycleT3 (OracleOf) in
/-- **A seal carries its tag**: under `AeadOpenChecksTag`, `AeadRoundTrip` and the oracle record's seal clause, for
keys of 32, 32 and 16 bytes, a plaintext slice of at most `Usize.max - 48` bytes and associated data that fit a
slice, the oracle's seal is not `NotTagged` under the MAC key and the associated data: the real `encrypt` returns it,
the real `decrypt` opens it (the round trip), and the law then gives its tag. -/
theorem not_notTagged_of_seal (hu : AeadOpenChecksTag) (haead : AeadRoundTrip) {R : Type}
    {rc : rand_core_1.RngCore R} {crc : rand_core_1.CryptoRng R}
    {dh : DhView} {kem : KemView} {trace : R → List Model.Lifecycle.Key} {oracle : Model.Lifecycle.Oracle}
    (oracleOf : OracleOf rc crc dh kem trace oracle)
    (k1 k2 iv : Model.Lifecycle.Bytes) (hk1 : k1.length = 32) (hk2 : k2.length = 32) (hiv : iv.length = 16)
    (pt : Slice U8) (hpt : pt.val.length + 48 ≤ Usize.max) (ad : Model.Lifecycle.Bytes)
    (had : ad.length ≤ Usize.max) :
    ¬ NotTagged k2 ad (oracle.aeadSeal k1 k2 iv (sliceOf pt) ad) := by
  intro hnt
  let K1 : Array U8 32#usize := arrayOfBytes k1 hk1
  let K2 : Array U8 32#usize := arrayOfBytes k2 hk2
  let IV : Array U8 16#usize := arrayOfBytes iv hiv
  let A := Tacenta.UnitSatisfiabilityBraidStates.sliceOfBytes ad had
  have hA : sliceOf A = ad := Tacenta.UnitSatisfiabilityBraidStates.sliceOf_sliceOfBytes ad had
  obtain ⟨ct, hct, hvec⟩ := oracleOf.aeadSeal K1 K2 IV pt A
  simp only [K1, K2, IV, arrayOf_arrayOfBytes, hA] at hvec
  obtain ⟨v, hv, -⟩ := haead K1 K2 IV pt A ct hpt hct
  have ht := hu K1 K2 IV (alloc.vec.Vec.deref ct) A v hv
  rw [hA, show arrayOf K2 = k2 from arrayOf_arrayOfBytes (n := 32#usize) k2 hk2] at ht
  apply hnt
  rw [← hvec]
  exact ht

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
`initiator_receives_reply` (`hfreshB` and `AeadSealBounded` included) and the assumed law `AeadOpenChecksTag`: the
responder's `encrypt` at `sB'` returns `bytesR`, the reply frame under the key the initiator's receiving chain derives,
and the initiator's public `decrypt` of `bytesR` at `s'` from `rng'` returns `Ok ptA` with `ptA` the bytes of `ptR`,
taking exactly the draw `dA`; the reply's own ciphertext, the bytes of `bytesR` after its first 102, carries its tag
under the reply's MAC key and associated data, so `NotTagged` excludes it; and for every slice `frame` whose bytes are
the first 102 bytes of `bytesR` (the reply's header) followed by bytes `cT` that are `NotTagged` under that MAC key and
that associated data (the per-run premise), the same call on `frame` at `s'` from `rng'` returns `Err(Aead)`, returns
the session `s'` as it was, and leaves a source holding exactly the draws after `dA`.  A frame whose header bytes
differ is not covered.  Conditional, like every encrypt result, on `AeadSealBounded`, which has no length premise and
is false of the shipping seal at the top of the length range.  No compiler-trust axiom (the pin). -/
theorem initiator_refuses_tampered_reply [Tacenta.SessionUnitT1.DerivedKeysModel] {R E F : Type}
    (hu : AeadOpenChecksTag) (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R)
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
      ¬ NotTagged
        (Model.State.messageKeys (firstKey (Model.State.kdfRk (arrayOf q.rootKey) dSend .tacenta).2
          (arrayOf q.sparseReceive)) .tacenta).2.1
        (replyAd (vecOf q.identityAd) (oracleB.dhPublic dB)) ((vecOf bytesR).drop 102) ∧
      ∀ (frame : Slice Std.U8) (cT : Model.Lifecycle.Bytes),
        sliceOf frame = (vecOf bytesR).take 102 ++ cT →
        NotTagged
          (Model.State.messageKeys (firstKey (Model.State.kdfRk (arrayOf q.rootKey) dSend .tacenta).2
            (arrayOf q.sparseReceive)) .tacenta).2.1
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
  -- the honest ciphertext carries its tag
  · rw [hbytesR, replyFrame_drop _ _ _ _ _ hlen]
    exact not_notTagged_of_seal hu haead oracleOfB _ _ _ hk1 hk2 hiv ptR (by omega) _ had
  -- a frame with the reply's header and a ciphertext that carries no tag
  intro frame cT hframeT hns
  rw [hbytesR, replyFrame_take _ _ _ _ _ hlen] at hframeT
  have hmsg : sliceOf frame = Model.CompositeHeader.encodeMessage (replyComposite (oracleB.dhPublic dB)) cT :=
    hframeT
  have hcT : cT.length ≤ Usize.max := by
    have h1 : (sliceOf frame).length ≤ Usize.max := by simp [sliceOf]; exact frame.property
    rw [hmsg] at h1
    simp only [Model.CompositeHeader.encodeMessage, List.length_append] at h1
    omega
  have hopen := open_none_of_not_tagged hu oracleOfA _ _ _ hk1 hk2 hiv cT _ hcT had hns
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


/-! ## The law in a model that binds the key and the associated data, and the contrasts -/

section JointModel

open Tacenta.UnitSatisfiabilityJoint (Interp Interp.real)
open Tacenta.UnitLifecycleIntegrationScreen (byteRng byteCrc byteTrace)
open Tacenta.UnitLifecycleResponderFirstFrame (DhAgreeSymmetricShape FirstFrameSuccessShape PoolEntry
  basePoint_ne_zero)
open Tacenta.UnitLifecycleResponderFirstReceipt (DhAgreeContributoryShape)
open Tacenta.UnitLifecycleEstablishedEncrypt (toyKemR zeroSeed oneSeed EncryptExtraLawsShape
  established_encrypt_laws_model encapResult encapFill)
open Tacenta.UnitLifecycleDecryptRatchetScreen (DhViewShape)
open Tacenta.UnitOracleShape (InterpO DhViewOf KemViewOf)
open Tacenta.UnitSatisfiabilityBraidAgreements (toU8 u8_toU8)
open Tacenta.UnitLifecycleResponderReplyReceipt (Interp.modelReply replyPub replyPub_canonical replyPub_zeros
  DhPublicNotConstantShape modelReply_dhCodec modelReply_dhAgree modelReply_symmetric modelReply_contributory
  modelReply_notConstant)

/-- The toy tag of a body under a MAC key and associated data: the model's HMAC of the key over the associated data
followed by the body, as bytes of the translation. -/
def toyTag (k2 : Array U8 32#usize) (ad : Slice U8) (body : List U8) : List U8 :=
  (Model.Kdf.hmac (arrayOf k2) (sliceOf ad ++ body.map Tacenta.SessionUnitBraidT3.u8)).map toU8

/-- The toy tag is 32 bytes. -/
theorem toyTag_length (k2 : Array U8 32#usize) (ad : Slice U8) (body : List U8) :
    (toyTag k2 ad body).length = 32 := by
  simp [toyTag, Model.Kdf.hmac_length, Model.Kdf.hashLen]

/-- The toy tag's bytes are the model's HMAC. -/
theorem toyTag_bytes (k2 : Array U8 32#usize) (ad : Slice U8) (body : List U8) :
    (toyTag k2 ad body).map Tacenta.SessionUnitBraidT3.u8 =
      Model.Kdf.hmac (arrayOf k2) (sliceOf ad ++ body.map Tacenta.SessionUnitBraidT3.u8) := by
  simp [toyTag, List.map_map, Function.comp_def, u8_toU8]

/-- The toy tagged seal: the plaintext followed by its toy tag, when that fits a slice; the plaintext itself
otherwise (a totality fallback the round trip's length premise excludes).  It encrypts nothing. -/
def sealTagged (k2 : Array U8 32#usize) (p ad : Slice U8) : alloc.vec.Vec U8 :=
  if h : p.val.length + 32 ≤ Usize.max then
    ⟨p.val ++ toyTag k2 ad p.val, by simp [toyTag_length]; omega⟩
  else ⟨p.val, p.property⟩

/-- The toy tagged open: it accepts exactly the bytes that carry the tag under the MAC key and the associated data
(the equation of `TagMatches`, written out so that it is decided by the equality of byte lists, with no instance of
its own), and returns the bytes before the tag. -/
def openTagged (k2 : Array U8 32#usize) (c ad : Slice U8) :
    core.result.Result (alloc.vec.Vec U8) Unit :=
  if (sliceOf c).drop ((sliceOf c).length - 32) =
      Model.Kdf.hmac (arrayOf k2) (sliceOf ad ++ (sliceOf c).take ((sliceOf c).length - 32)) then
    .Ok ⟨c.val.take (c.val.length - 32), by have := c.property; simp; omega⟩
  else .Err ()

/-- `Interp.modelReply` with the toy tagged AEAD: the seal appends the model's HMAC under the MAC key over the
associated data and the plaintext, and the open checks it.  Unlike `Interp.modelReply`'s, this AEAD binds the MAC
key and the associated data.  Every other field is `Interp.modelReply`'s.  A toy: it encrypts nothing. -/
noncomputable def Interp.modelTagged : Interp :=
  { Interp.modelReply with
    aeadEncrypt := fun _ k2 _ p ad => ok (sealTagged k2 p ad)
    aeadDecrypt := fun _ k2 _ c ad => ok (openTagged k2 c ad) }

/-- **`AeadOpenChecksTagShape` holds in the tagged model**: its open accepts only bytes that carry the tag. -/
theorem modelTagged_checksTag : AeadOpenChecksTagShape Interp.modelTagged := by
  intro k1 k2 iv c ad v h
  have h' : openTagged k2 c ad = .Ok v := by
    have h0 : ok (openTagged k2 c ad) = ok (core.result.Result.Ok v) := h
    injection h0
  unfold openTagged at h'
  split at h'
  · rename_i ht
    have ht' : TagMatches (arrayOf k2) (sliceOf ad) (sliceOf c) := by unfold TagMatches; exact ht
    exact ht'
  · cases h'

/-- The toy tagged seal of a plaintext that leaves room for the tag is the plaintext followed by its toy tag. -/
theorem sealTagged_val (k2 : Array U8 32#usize) (p ad : Slice U8) (h : p.val.length + 32 ≤ Usize.max) :
    (sealTagged k2 p ad).val = p.val ++ toyTag k2 ad p.val := by
  unfold sealTagged; rw [dif_pos h]

/-- **The round trip holds in the tagged model**: the open of a seal returns the plaintext. -/
theorem modelTagged_roundTrip : AeadRoundTripShape Interp.modelTagged := by
  intro k1 k2 iv pt ad ct hpt hct
  have hct' : ok (sealTagged k2 pt ad) = ok ct := hct
  injection hct' with hct''
  subst hct''
  have hval := sealTagged_val k2 pt ad (by omega)
  have hs : sliceOf (alloc.vec.Vec.deref (sealTagged k2 pt ad)) =
      sliceOf pt ++ Model.Kdf.hmac (arrayOf k2) (sliceOf ad ++ sliceOf pt) := by
    show (sealTagged k2 pt ad).val.map _ = _
    rw [hval, List.map_append, toyTag_bytes]; rfl
  have htag : TagMatches (arrayOf k2) (sliceOf ad) (sliceOf (alloc.vec.Vec.deref (sealTagged k2 pt ad))) := by
    unfold TagMatches
    rw [hs]
    have hl : (sliceOf pt ++ Model.Kdf.hmac (arrayOf k2) (sliceOf ad ++ sliceOf pt)).length - 32 =
        (sliceOf pt).length := by
      simp [Model.Kdf.hmac_length, Model.Kdf.hashLen]
    rw [hl, List.drop_left, List.take_left]
  refine ⟨⟨(alloc.vec.Vec.deref (sealTagged k2 pt ad)).val.take
      ((alloc.vec.Vec.deref (sealTagged k2 pt ad)).val.length - 32), ?_⟩, ?_, ?_⟩
  · have := (alloc.vec.Vec.deref (sealTagged k2 pt ad)).property; simp; omega
  · show ok (openTagged k2 (alloc.vec.Vec.deref (sealTagged k2 pt ad)) ad) = _
    unfold openTagged
    rw [if_pos (by unfold TagMatches at htag; exact htag)]
  · have hd : (alloc.vec.Vec.deref (sealTagged k2 pt ad)).val = (sealTagged k2 pt ad).val := rfl
    show List.take _ (alloc.vec.Vec.deref (sealTagged k2 pt ad)).val = pt.val
    rw [hd, hval]
    simp [toyTag_length]

/-- **The seal bound holds in the tagged model**: its seal returns, at most 48 bytes longer than the plaintext. -/
theorem modelTagged_sealBounded :
    Tacenta.UnitSatisfiabilityJoint.AeadSealBoundedShape Interp.modelTagged := by
  intro ek mk iv p ad
  refine ⟨sealTagged mk p ad, rfl, ?_⟩
  unfold sealTagged
  split
  · simp [toyTag_length]
  · simp

/-- **Open totality holds in the tagged model**: its open returns. -/
theorem modelTagged_open : Tacenta.UnitSatisfiabilityJoint.AeadOpenShape Interp.modelTagged :=
  fun _ _ _ _ _ => ⟨_, rfl⟩

/-- The tagged interpretation with its signing function. -/
noncomputable def InterpO.modelTagged : InterpO :=
  { Interp.modelTagged with xeddsaSign := Tacenta.UnitOracleModel.signModelO }

/-- The view of the tagged interpretation: both key types are their bytes. -/
def viewTagged : DhViewShape Interp.modelTagged := ⟨arrayOf, arrayOf⟩
/-- The DH view of the tagged interpretation with its signing function. -/
def dhViewTagged : DhViewOf InterpO.modelTagged.toInterp := ⟨viewTagged.privateKey, viewTagged.publicKey⟩
/-- The KEM view of the tagged interpretation with its signing function. -/
def kemViewTagged : KemViewOf InterpO.modelTagged.toInterp := ⟨fun _ => []⟩

open Tacenta.UnitSatisfiabilityJoint (InitiatorAxiom ResponderAxiom) in
open Tacenta.UnitLifecycleSessionCodec (ZeroizingVecRoundTripShape DhPrivateBytesRoundTripShape
  DhPublicBytesRoundTripShape OptionBranchSomeShape VecAsSliceShape optionBranchImpl vecAsSliceImpl) in
open Tacenta.UnitLifecycleRestoredSession (KemCiphertextLenBoundShape) in
open Tacenta.UnitLifecycleEstablishInitiatorShape (InitiatorSuccessShape DhPublicValidShape
  KemCiphertextLenLawShape) in
/-- **Every law `reply_receipt_laws_model` puts in `Interp.modelReply` holds again in `Interp.modelTagged`**: the
same conjuncts, in the same order, at the interpretation whose toy AEAD appends and checks the model's HMAC tag.  In
the substitution sense of `UnitSatisfiabilityRecords`; not a statement that the real primitives meet them. -/
theorem tagged_reply_laws_model :
    Tacenta.UnitLifecycleDecryptScreen.DecryptJointLawsShape Interp.modelTagged viewTagged toyKemR
        @Tacenta.UnitHeadroomInvariant.optionEqImpl ∧
      Nonempty (InitiatorAxiom Interp.modelTagged byteRng) ∧
      InitiatorSuccessShape Interp.modelTagged byteRng byteCrc ∧
      DhPublicValidShape Interp.modelTagged ∧
      KemCiphertextLenLawShape (ok 0#usize) Interp.modelTagged ∧
      EncryptExtraLawsShape InterpO.modelTagged dhViewTagged kemViewTagged toyKemR (ok 0#usize) ∧
      (ZeroizingVecRoundTripShape Interp.modelTagged ∧
        DhPrivateBytesRoundTripShape Interp.modelTagged ∧
        DhPublicBytesRoundTripShape Interp.modelTagged ∧ OptionBranchSomeShape @optionBranchImpl ∧
        VecAsSliceShape @vecAsSliceImpl ∧ KemCiphertextLenBoundShape (ok 0#usize)) ∧
      Tacenta.UnitLifecycleEstablishedEncrypt.KeyGenSizesOf toyKemR ∧
      toyKemR.keyGen (Model.Lifecycle.braidRandomness
          (zeroSeed.map Tacenta.SessionUnitBraidT3.u8)) = none ∧
      toyKemR.keyGen (Model.Lifecycle.braidRandomness
          (oneSeed.map Tacenta.SessionUnitBraidT3.u8)) ≠ none ∧
      Nonempty (ResponderAxiom Interp.modelTagged byteRng) ∧
      Tacenta.UnitLifecycleEstablishResponder.ResponderSuccessShape Interp.modelTagged ∧
      Tacenta.UnitLifecycleEstablishResponder.ZeroKeyShape Interp.modelTagged ∧
      DhAgreeSymmetricShape Interp.modelTagged ∧
      FirstFrameSuccessShape Interp.modelTagged (fun _ => ok (alloc.vec.Vec.new U8))
        (fun _ v => ok (decide (v.val = []))) ∧
      AeadRoundTripShape Interp.modelTagged ∧ DhAgreeContributoryShape Interp.modelTagged ∧
      DhPublicNotConstantShape Interp.modelTagged := by
  obtain ⟨M, ⟨A⟩, -, -, C, X, ⟨r1, r2, r3, r4, r5, r6⟩, ks, s0, s1⟩ := established_encrypt_laws_model
  obtain ⟨-, ⟨RA⟩, -, -, -⟩ := Tacenta.UnitLifecycleEstablishResponder.responder_route_laws_model
  have hcodec := modelReply_dhCodec
  have hagree := modelReply_dhAgree
  have hb := basePoint_ne_zero
  refine ⟨?_, ⟨?_⟩, ?_, ?_, ?_, ?_, ⟨?_, ?_, ?_, r4, r5, r6⟩, ks, s0, s1, ⟨?_⟩, ?_, ?_,
    modelReply_symmetric, ?_, modelTagged_roundTrip, modelReply_contributory, modelReply_notConstant⟩
  · exact
      { dhCodec := hcodec
        dhAgree := hagree
        aeadOpen := modelTagged_open
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
          congrArg ok replyPub_zeros, rfl,
          Tacenta.UnitLifecycleEstablishResponder.basePoint_canonical, rfl⟩
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
      fun _ => ⟨Array.repeat 64#usize 0#u8, rfl⟩, fun k => ⟨Tacenta.UnitLifecycleEstablishResponder.basePoint, ?_⟩⟩,
      ⟨alloc.vec.Vec.new U8, by simp; scalar_tac, fun rng => ?_⟩⟩
    · show ok (decide (Tacenta.UnitLifecycleEstablishedDecrypt.oneKey.val =
        Tacenta.UnitLifecycleEstablishedDecrypt.oneKey.val)) = ok true
      simp
    · show ok (if Tacenta.UnitLifecycleEstablishedDecrypt.oneKey.val =
          Tacenta.UnitLifecycleDecryptRatchetScreen.zeros32.val then none
        else some Tacenta.UnitLifecycleEstablishResponder.basePoint) =
        ok (some Tacenta.UnitLifecycleEstablishResponder.basePoint)
      simp [Tacenta.UnitLifecycleEstablishedDecrypt.oneKey_ne_zero]
    · show ∃ ct ss rng', encapFill byteRng byteCrc _ rng = ok (core.result.Result.Ok (ct, ss), rng')
      simp only [encapFill, if_true]
      exact ⟨_, _, _, rfl⟩
  · intro k pkb h
    have hp : pkb = replyPub k := by
      simpa [Interp.modelTagged, Interp.modelReply] using h.symm
    subst hp
    exact ⟨replyPub k, rfl, replyPub_canonical k, rfl⟩
  · exact C
  · exact
      { oracle :=
          { dhCodec := hcodec
            dhAgree := hagree
            dhIdentity := X.oracle.dhIdentity
            aeadSeal := modelTagged_sealBounded
            aeadOpen := modelTagged_open
            kemDecapsulate := X.oracle.kemDecapsulate
            xeddsaVerify := X.oracle.xeddsaVerify
            signLaw := X.oracle.signLaw
            kemLaw := X.oracle.kemLaw
            dhView := X.oracle.dhView
            kemView := X.oracle.kemView }
        encrypt :=
          { braid := by have h := X.encrypt.braid; cases h; constructor <;> assumption
            triple := by have h := X.encrypt.triple; cases h; constructor <;> assumption
            aeadSeal := modelTagged_sealBounded
            messageKeyMaterial := X.encrypt.messageKeyMaterial
            dhCodec := hcodec }
        keyGen := X.keyGen
        zeroizingKeys := X.zeroizingKeys
        ciphertextBound := X.ciphertextBound }
  · exact r1
  · exact r2
  · exact r3
  · exact
      { decrypt := ⟨hcodec, hagree, modelTagged_open, RA.decrypt.random32,
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
      else some Tacenta.UnitLifecycleEstablishResponder.basePoint)) = ok none
    simp [Tacenta.UnitSatisfiabilityBraidStates.zeros32, Tacenta.UnitLifecycleDecryptRatchetScreen.zeros32]
  · refine ⟨⟨Tacenta.UnitSatisfiabilityBraidStates.zeros32, Tacenta.UnitSatisfiabilityBraidStates.zeros32,
      Tacenta.UnitLifecycleEstablishResponder.basePoint, Tacenta.UnitLifecycleEstablishResponder.basePoint,
      rfl, ?_, rfl, Tacenta.UnitLifecycleEstablishResponder.basePoint_canonical, rfl, ?_,
      fun _ => ⟨Array.repeat 64#usize 0#u8, rfl⟩, fun k => ⟨Tacenta.UnitLifecycleEstablishResponder.basePoint, ?_⟩⟩,
      ⟨(), alloc.vec.Vec.new U8, List.replicate 32 0#u8, alloc.vec.Vec.new U8,
        Tacenta.UnitSatisfiabilityBraidStates.zeros32, [], rfl, by simp; scalar_tac, ?_, ?_⟩,
      ⟨alloc.vec.Vec.new PoolEntry, rfl⟩, fun _ _ => rfl⟩
    · exact congrArg ok replyPub_zeros
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

/-- A lenient toy open: it accepts every ciphertext of at least 32 bytes, whatever its last 32, and returns the
bytes before them.  It skips the tag check. -/
def openTaggedLenient (c : Slice U8) : core.result.Result (alloc.vec.Vec U8) Unit :=
  if 32 ≤ c.val.length then .Ok ⟨c.val.take (c.val.length - 32), by have := c.property; simp; omega⟩
  else .Err ()

/-- `Interp.modelTagged` with the lenient open. -/
noncomputable def Interp.modelTaggedLenient : Interp :=
  { Interp.modelTagged with aeadDecrypt := fun _ _ _ c _ => ok (openTaggedLenient c) }

/-- **`AeadOpenChecksTagShape` is not implied by the round trip**: the lenient interpretation opens what it seals
(`AeadRoundTripShape` holds) and opens two different 32-byte strings under one key and the empty associated data,
which cannot both be the one tag there, so the law fails. -/
theorem taggedLenient_roundTrip_not_checksTag :
    AeadRoundTripShape Interp.modelTaggedLenient ∧ ¬ AeadOpenChecksTagShape Interp.modelTaggedLenient := by
  refine ⟨?_, ?_⟩
  · intro k1 k2 iv pt ad ct hpt hct
    have hct' : ok (sealTagged k2 pt ad) = ok ct := hct
    injection hct' with hct''
    subst hct''
    have hval := sealTagged_val k2 pt ad (by omega)
    have hd : (alloc.vec.Vec.deref (sealTagged k2 pt ad)).val = pt.val ++ toyTag k2 ad pt.val := hval
    refine ⟨⟨(alloc.vec.Vec.deref (sealTagged k2 pt ad)).val.take
        ((alloc.vec.Vec.deref (sealTagged k2 pt ad)).val.length - 32), ?_⟩, ?_, ?_⟩
    · have := (alloc.vec.Vec.deref (sealTagged k2 pt ad)).property; simp; omega
    · show ok (openTaggedLenient (alloc.vec.Vec.deref (sealTagged k2 pt ad))) = _
      unfold openTaggedLenient
      rw [if_pos (by rw [hd]; simp [toyTag_length])]
    · show List.take _ (alloc.vec.Vec.deref (sealTagged k2 pt ad)).val = pt.val
      rw [hd]; simp [toyTag_length]
  · intro hu
    -- two different 32-byte strings both open; the law would make each the one model tag of the empty input
    let k : Array U8 32#usize := Array.repeat 32#usize 0#u8
    let iv : Array U8 16#usize := Array.repeat 16#usize 0#u8
    have hmax : 2 ^ 32 - 1 ≤ Usize.max := by scalar_tac
    have key : ∀ b : U8, Model.Kdf.hmac (arrayOf k) [] =
        (List.replicate 32 b).map Tacenta.SessionUnitBraidT3.u8 := by
      intro b
      let c : Slice U8 := ⟨List.replicate 32 b, by simp; omega⟩
      have hopen : Interp.modelTaggedLenient.aeadDecrypt k k iv c (Slice.new U8) =
          ok (core.result.Result.Ok ⟨c.val.take (c.val.length - 32), by have := c.property; simp; omega⟩) := by
        show ok (openTaggedLenient c) = _
        unfold openTaggedLenient
        rw [if_pos (by simp [c])]
      have ht := hu k k iv c (Slice.new U8) _ hopen
      unfold TagMatches at ht
      have hc : (sliceOf c).length = 32 := by simp [sliceOf, c]
      rw [hc] at ht
      simp only [Nat.sub_self, List.drop_zero, List.take_zero, List.append_nil] at ht
      have hA : sliceOf (Slice.new U8) = [] := rfl
      rw [hA] at ht
      exact ht.symm
    have h := (key 0#u8).symm.trans (key 1#u8)
    have h0 := congrArg List.head? h
    simp at h0
    revert h0
    decide

/-- `Interp.modelTagged` with a seal that fails once the plaintext, the associated data and the tag pass half the
`usize` range (`Usize.max / 2`, which is `isize::MAX` at both widths), as the shipping seal's copy of
`ad ‖ ct` into one allocation does.  The open is `Interp.modelTagged`'s. -/
noncomputable def Interp.modelTaggedTop : Interp :=
  { Interp.modelTagged with
    aeadEncrypt := fun _ k2 _ p ad =>
      if p.val.length + ad.val.length + 32 ≤ Usize.max / 2 then ok (sealTagged k2 p ad) else fail .panic }

/-- **The tag law survives a seal that fails at the top of the length range, and the earlier law does not**: with
`Interp.modelTaggedTop`'s seal, `AeadOpenChecksTagShape` holds and `AeadOpenSealUniqueShape` fails, at both widths.
The witness is a body of `Usize.max / 2 - 31` zero bytes followed by its toy tag, under the empty associated data:
the open accepts it, and the reseal of the body fails. -/
theorem taggedTop_checksTag_not_openSealUnique :
    AeadOpenChecksTagShape Interp.modelTaggedTop ∧ ¬ AeadOpenSealUniqueShape Interp.modelTaggedTop := by
  refine ⟨modelTagged_checksTag, ?_⟩
  intro hu
  let k : Array U8 32#usize := Array.repeat 32#usize 0#u8
  let iv : Array U8 16#usize := Array.repeat 16#usize 0#u8
  let n := Usize.max / 2 - 31
  let body : List U8 := List.replicate n 0#u8
  have hmax : 2 ^ 32 - 1 ≤ Usize.max := by scalar_tac
  have hn : n + 32 ≤ Usize.max := by simp only [n]; omega
  let c : Slice U8 := ⟨body ++ toyTag k (Slice.new U8) body, by simp [body, toyTag_length]; omega⟩
  have hsc : sliceOf c = sliceOf ⟨body, by simp [body]; omega⟩ ++
      Model.Kdf.hmac (arrayOf k) (sliceOf (Slice.new U8) ++ body.map Tacenta.SessionUnitBraidT3.u8) := by
    show (body ++ toyTag k (Slice.new U8) body).map _ = _
    rw [List.map_append, toyTag_bytes]; rfl
  have htag : TagMatches (arrayOf k) (sliceOf (Slice.new U8)) (sliceOf c) := by
    unfold TagMatches
    rw [hsc]
    have hl : (sliceOf (⟨body, by simp [body]; omega⟩ : Slice U8) ++ Model.Kdf.hmac (arrayOf k)
        (sliceOf (Slice.new U8) ++ body.map Tacenta.SessionUnitBraidT3.u8)).length - 32 =
        (sliceOf (⟨body, by simp [body]; omega⟩ : Slice U8)).length := by
      simp [Model.Kdf.hmac_length, Model.Kdf.hashLen]
    rw [hl, List.drop_left, List.take_left]
    rfl
  have hopen : Interp.modelTaggedTop.aeadDecrypt k k iv c (Slice.new U8) =
      ok (core.result.Result.Ok ⟨c.val.take (c.val.length - 32), by have := c.property; simp; omega⟩) := by
    show ok (openTagged k c (Slice.new U8)) = _
    unfold openTagged
    rw [if_pos (by unfold TagMatches at htag; exact htag)]
  obtain ⟨ct, hct, -⟩ := hu k k iv c (Slice.new U8) _ hopen
  have hlenv : (c.val.take (c.val.length - 32)).length = n := by
    simp [c, body, toyTag_length]
  have hbig : ¬ ((c.val.take (c.val.length - 32)).length + (Slice.new U8).val.length + 32 ≤ Usize.max / 2) := by
    rw [hlenv]; simp only [n, Slice.new]; simp; omega
  have : Interp.modelTaggedTop.aeadEncrypt k k iv
      (alloc.vec.Vec.deref ⟨c.val.take (c.val.length - 32), by have := c.property; simp; omega⟩) (Slice.new U8) =
      fail .panic := by
    exact if_neg hbig
  rw [this] at hct
  cases hct

/-- **The tamper laws hold together in the tagged model**: `AeadRoundTripShape` and `AeadOpenChecksTagShape` hold at
`Interp.modelTagged`, the interpretation at which `tagged_reply_laws_model` puts every other law the reply's receipt
takes, and the per-run premise `NotTagged` holds of the empty ciphertext under every key and associated data.  In the
substitution sense of `UnitSatisfiabilityRecords`; not a statement that the real AEAD meets them. -/
theorem tamper_laws_model :
    AeadRoundTripShape Interp.modelTagged ∧ AeadOpenChecksTagShape Interp.modelTagged ∧
      ∀ k2 ad : Model.Lifecycle.Bytes, NotTagged k2 ad [] :=
  ⟨modelTagged_roundTrip, modelTagged_checksTag, fun k2 ad => notTagged_of_short k2 ad [] (by simp)⟩

end JointModel

end Tacenta.UnitLifecycleTamperedReply

-- The pins `genpins.py` writes after this line print each statement whole: with no cut at depth 50
-- (`pp.deepTerms`) and each omitted proof with its proposition, `(⋯ : P)` (`pp.proofs.withType`). `attest.py`
-- refuses a statement pin that prints a bare `⋯`, and every other `pp` option.
set_option pp.deepTerms true
set_option pp.proofs.withType true

/-! ## Pins

The constants each result depends on, and the statement of each result and definition, held by the
build.  `attest.py` requires every one of them (`REQUIRED_PINS`, `REQUIRED_STATEMENT_PINS`,
`REQUIRED_PRINT_FORM`). -/

/--
info: 'Tacenta.UnitLifecycleTamperedReply.aeadOpenChecksTag_is' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
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
#print axioms Tacenta.UnitLifecycleTamperedReply.aeadOpenChecksTag_is

/--
info: 'Tacenta.UnitLifecycleTamperedReply.notTagged_of_short' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleTamperedReply.notTagged_of_short

/--
info: 'Tacenta.UnitLifecycleTamperedReply.tagMatches_append' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleTamperedReply.tagMatches_append

/--
info: 'Tacenta.UnitLifecycleTamperedReply.open_none_of_not_tagged' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
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
#print axioms Tacenta.UnitLifecycleTamperedReply.open_none_of_not_tagged

/--
info: 'Tacenta.UnitLifecycleTamperedReply.not_notTagged_of_seal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
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
#print axioms Tacenta.UnitLifecycleTamperedReply.not_notTagged_of_seal

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
info: 'Tacenta.UnitLifecycleTamperedReply.toyTag_length' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleTamperedReply.toyTag_length

/--
info: 'Tacenta.UnitLifecycleTamperedReply.toyTag_bytes' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleTamperedReply.toyTag_bytes

/--
info: 'Tacenta.UnitLifecycleTamperedReply.modelTagged_checksTag' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleTamperedReply.modelTagged_checksTag

/--
info: 'Tacenta.UnitLifecycleTamperedReply.sealTagged_val' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleTamperedReply.sealTagged_val

/--
info: 'Tacenta.UnitLifecycleTamperedReply.modelTagged_roundTrip' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleTamperedReply.modelTagged_roundTrip

/--
info: 'Tacenta.UnitLifecycleTamperedReply.modelTagged_sealBounded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleTamperedReply.modelTagged_sealBounded

/--
info: 'Tacenta.UnitLifecycleTamperedReply.modelTagged_open' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleTamperedReply.modelTagged_open

/--
info: 'Tacenta.UnitLifecycleTamperedReply.tagged_reply_laws_model' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 rand_core_1.error.Error,
 Array.Insts.ZeroizeZeroize.zeroize,
 Pair.Insts.ZeroizeZeroize.zeroize,
 zeroize.Zeroize.Blanket.zeroize,
 alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleTamperedReply.tagged_reply_laws_model

/--
info: 'Tacenta.UnitLifecycleTamperedReply.taggedLenient_roundTrip_not_checksTag' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleTamperedReply.taggedLenient_roundTrip_not_checksTag

/--
info: 'Tacenta.UnitLifecycleTamperedReply.taggedTop_checksTag_not_openSealUnique' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleTamperedReply.taggedTop_checksTag_not_openSealUnique

/--
info: 'Tacenta.UnitLifecycleTamperedReply.tamper_laws_model' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleTamperedReply.tamper_laws_model

/--
info: Tacenta.UnitLifecycleTamperedReply.aeadOpenChecksTag_is : Tacenta.UnitLifecycleTamperedReply.AeadOpenChecksTag ↔
  ∀ (k1 k2 : Std.Array U8 32#usize) (iv : Std.Array U8 16#usize) (c ad : Slice U8) (v : alloc.vec.Vec U8),
    tacenta_boundary.aead.decrypt k1 k2 iv c ad = ok (core.result.Result.Ok v) →
      Tacenta.UnitLifecycleTamperedReply.TagMatches (Tacenta.UnitLifecycleT3.arrayOf k2)
        (Tacenta.UnitLifecycleT3.sliceOf ad) (Tacenta.UnitLifecycleT3.sliceOf c)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleTamperedReply.aeadOpenChecksTag_is

/--
info: Tacenta.UnitLifecycleTamperedReply.notTagged_of_short : ∀ (k2 ad c : Model.Lifecycle.Bytes),
  List.length c < 32 → Tacenta.UnitLifecycleTamperedReply.NotTagged k2 ad c
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleTamperedReply.notTagged_of_short

/--
info: Tacenta.UnitLifecycleTamperedReply.tagMatches_append : ∀ (k2 ad body : Model.Lifecycle.Bytes),
  Tacenta.UnitLifecycleTamperedReply.TagMatches k2 ad (body ++ Model.Kdf.hmac k2 (ad ++ body))
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleTamperedReply.tagMatches_append

/--
info: Tacenta.UnitLifecycleTamperedReply.open_none_of_not_tagged : Tacenta.UnitLifecycleTamperedReply.AeadOpenChecksTag →
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
                    Tacenta.UnitLifecycleTamperedReply.NotTagged k2 ad c → oracle.aeadOpen k1 k2 iv c ad = none
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleTamperedReply.open_none_of_not_tagged

/--
info: Tacenta.UnitLifecycleTamperedReply.not_notTagged_of_seal : Tacenta.UnitLifecycleTamperedReply.AeadOpenChecksTag →
  Tacenta.UnitLifecycleResponderFirstReceipt.AeadRoundTrip →
    ∀ {R : Type} {rc : rand_core_1.RngCore R} {crc : rand_core_1.CryptoRng R} {dh : Tacenta.UnitLifecycleT3.DhView}
      {kem : Tacenta.UnitLifecycleT3.KemView} {trace : R → List Model.Lifecycle.Key} {oracle : Model.Lifecycle.Oracle},
      Tacenta.UnitLifecycleT3.OracleOf rc crc dh kem trace oracle →
        ∀ (k1 k2 iv : Model.Lifecycle.Bytes),
          List.length k1 = 32 →
            List.length k2 = 32 →
              List.length iv = 16 →
                ∀ (pt : Slice U8),
                  (↑pt).length + 48 ≤ Usize.max →
                    ∀ (ad : Model.Lifecycle.Bytes),
                      List.length ad ≤ Usize.max →
                        ¬Tacenta.UnitLifecycleTamperedReply.NotTagged k2 ad
                            (oracle.aeadSeal k1 k2 iv (Tacenta.UnitLifecycleT3.sliceOf pt) ad)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleTamperedReply.not_notTagged_of_seal

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
  Tacenta.UnitLifecycleTamperedReply.AeadOpenChecksTag →
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
                                                                                                                                    ¬Tacenta.UnitLifecycleTamperedReply.NotTagged
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
                                                                                                                                          Tacenta.UnitLifecycleTamperedReply.NotTagged
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
info: Tacenta.UnitLifecycleTamperedReply.toyTag_length : ∀ (k2 : Std.Array U8 32#usize) (ad : Slice U8) (body : List U8),
  (Tacenta.UnitLifecycleTamperedReply.toyTag k2 ad body).length = 32
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleTamperedReply.toyTag_length

/--
info: Tacenta.UnitLifecycleTamperedReply.toyTag_bytes : ∀ (k2 : Std.Array U8 32#usize) (ad : Slice U8) (body : List U8),
  List.map Tacenta.SessionUnitBraidT3.u8 (Tacenta.UnitLifecycleTamperedReply.toyTag k2 ad body) =
    Model.Kdf.hmac (Tacenta.UnitLifecycleT3.arrayOf k2)
      (Tacenta.UnitLifecycleT3.sliceOf ad ++ List.map Tacenta.SessionUnitBraidT3.u8 body)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleTamperedReply.toyTag_bytes

/--
info: Tacenta.UnitLifecycleTamperedReply.modelTagged_checksTag : Tacenta.UnitLifecycleTamperedReply.AeadOpenChecksTagShape
  Tacenta.UnitLifecycleTamperedReply.Interp.modelTagged
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleTamperedReply.modelTagged_checksTag

/--
info: Tacenta.UnitLifecycleTamperedReply.sealTagged_val : ∀ (k2 : Std.Array U8 32#usize) (p ad : Slice U8),
  (↑p).length + 32 ≤ Usize.max →
    ↑(Tacenta.UnitLifecycleTamperedReply.sealTagged k2 p ad) = ↑p ++ Tacenta.UnitLifecycleTamperedReply.toyTag k2 ad ↑p
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleTamperedReply.sealTagged_val

/--
info: Tacenta.UnitLifecycleTamperedReply.modelTagged_roundTrip : Tacenta.UnitLifecycleResponderFirstReceipt.AeadRoundTripShape
  Tacenta.UnitLifecycleTamperedReply.Interp.modelTagged
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleTamperedReply.modelTagged_roundTrip

/--
info: Tacenta.UnitLifecycleTamperedReply.modelTagged_sealBounded : Tacenta.UnitSatisfiabilityJoint.AeadSealBoundedShape
  Tacenta.UnitLifecycleTamperedReply.Interp.modelTagged
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleTamperedReply.modelTagged_sealBounded

/--
info: Tacenta.UnitLifecycleTamperedReply.modelTagged_open : Tacenta.UnitSatisfiabilityJoint.AeadOpenShape
  Tacenta.UnitLifecycleTamperedReply.Interp.modelTagged
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleTamperedReply.modelTagged_open

/--
info: Tacenta.UnitLifecycleTamperedReply.tagged_reply_laws_model : Tacenta.UnitLifecycleDecryptScreen.DecryptJointLawsShape
    Tacenta.UnitLifecycleTamperedReply.Interp.modelTagged Tacenta.UnitLifecycleTamperedReply.viewTagged
    Tacenta.UnitLifecycleEstablishedEncrypt.toyKemR @Tacenta.UnitHeadroomInvariant.optionEqImpl ∧
  Nonempty
      (Tacenta.UnitSatisfiabilityJoint.InitiatorAxiom Tacenta.UnitLifecycleTamperedReply.Interp.modelTagged
        Tacenta.UnitLifecycleIntegrationScreen.byteRng) ∧
    Tacenta.UnitLifecycleEstablishInitiatorShape.InitiatorSuccessShape
        Tacenta.UnitLifecycleTamperedReply.Interp.modelTagged Tacenta.UnitLifecycleIntegrationScreen.byteRng
        Tacenta.UnitLifecycleIntegrationScreen.byteCrc ∧
      Tacenta.UnitLifecycleEstablishInitiatorShape.DhPublicValidShape
          Tacenta.UnitLifecycleTamperedReply.Interp.modelTagged ∧
        Tacenta.UnitLifecycleEstablishInitiatorShape.KemCiphertextLenLawShape (ok 0#usize)
            Tacenta.UnitLifecycleTamperedReply.Interp.modelTagged ∧
          Tacenta.UnitLifecycleEstablishedEncrypt.EncryptExtraLawsShape
              Tacenta.UnitLifecycleTamperedReply.InterpO.modelTagged Tacenta.UnitLifecycleTamperedReply.dhViewTagged
              Tacenta.UnitLifecycleTamperedReply.kemViewTagged Tacenta.UnitLifecycleEstablishedEncrypt.toyKemR
              (ok 0#usize) ∧
            (Tacenta.UnitLifecycleSessionCodec.ZeroizingVecRoundTripShape
                  Tacenta.UnitLifecycleTamperedReply.Interp.modelTagged ∧
                Tacenta.UnitLifecycleSessionCodec.DhPrivateBytesRoundTripShape
                    Tacenta.UnitLifecycleTamperedReply.Interp.modelTagged ∧
                  Tacenta.UnitLifecycleSessionCodec.DhPublicBytesRoundTripShape
                      Tacenta.UnitLifecycleTamperedReply.Interp.modelTagged ∧
                    Tacenta.UnitLifecycleSessionCodec.OptionBranchSomeShape
                        @Tacenta.UnitLifecycleSessionCodec.optionBranchImpl ∧
                      Tacenta.UnitLifecycleSessionCodec.VecAsSliceShape
                          @Tacenta.UnitLifecycleSessionCodec.vecAsSliceImpl ∧
                        Tacenta.UnitLifecycleRestoredSession.KemCiphertextLenBoundShape (ok 0#usize)) ∧
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
                          Tacenta.UnitLifecycleTamperedReply.Interp.modelTagged
                          Tacenta.UnitLifecycleIntegrationScreen.byteRng) ∧
                      Tacenta.UnitLifecycleEstablishResponder.ResponderSuccessShape
                          Tacenta.UnitLifecycleTamperedReply.Interp.modelTagged ∧
                        Tacenta.UnitLifecycleEstablishResponder.ZeroKeyShape
                            Tacenta.UnitLifecycleTamperedReply.Interp.modelTagged ∧
                          Tacenta.UnitLifecycleResponderFirstFrame.DhAgreeSymmetricShape
                              Tacenta.UnitLifecycleTamperedReply.Interp.modelTagged ∧
                            (Tacenta.UnitLifecycleResponderFirstFrame.FirstFrameSuccessShape
                                Tacenta.UnitLifecycleTamperedReply.Interp.modelTagged
                                (fun x => ok (alloc.vec.Vec.new U8)) fun {T} x v => ok (decide (↑v = []))) ∧
                              Tacenta.UnitLifecycleResponderFirstReceipt.AeadRoundTripShape
                                  Tacenta.UnitLifecycleTamperedReply.Interp.modelTagged ∧
                                Tacenta.UnitLifecycleResponderFirstReceipt.DhAgreeContributoryShape
                                    Tacenta.UnitLifecycleTamperedReply.Interp.modelTagged ∧
                                  Tacenta.UnitLifecycleResponderReplyReceipt.DhPublicNotConstantShape
                                    Tacenta.UnitLifecycleTamperedReply.Interp.modelTagged
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleTamperedReply.tagged_reply_laws_model

/--
info: Tacenta.UnitLifecycleTamperedReply.taggedLenient_roundTrip_not_checksTag : Tacenta.UnitLifecycleResponderFirstReceipt.AeadRoundTripShape
    Tacenta.UnitLifecycleTamperedReply.Interp.modelTaggedLenient ∧
  ¬Tacenta.UnitLifecycleTamperedReply.AeadOpenChecksTagShape
      Tacenta.UnitLifecycleTamperedReply.Interp.modelTaggedLenient
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleTamperedReply.taggedLenient_roundTrip_not_checksTag

/--
info: Tacenta.UnitLifecycleTamperedReply.taggedTop_checksTag_not_openSealUnique : Tacenta.UnitLifecycleTamperedReply.AeadOpenChecksTagShape
    Tacenta.UnitLifecycleTamperedReply.Interp.modelTaggedTop ∧
  ¬Tacenta.UnitLifecycleTamperedReply.AeadOpenSealUniqueShape Tacenta.UnitLifecycleTamperedReply.Interp.modelTaggedTop
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleTamperedReply.taggedTop_checksTag_not_openSealUnique

/--
info: Tacenta.UnitLifecycleTamperedReply.tamper_laws_model : Tacenta.UnitLifecycleResponderFirstReceipt.AeadRoundTripShape
    Tacenta.UnitLifecycleTamperedReply.Interp.modelTagged ∧
  Tacenta.UnitLifecycleTamperedReply.AeadOpenChecksTagShape Tacenta.UnitLifecycleTamperedReply.Interp.modelTagged ∧
    ∀ (k2 ad : Model.Lifecycle.Bytes), Tacenta.UnitLifecycleTamperedReply.NotTagged k2 ad []
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleTamperedReply.tamper_laws_model

/--
info: @[irreducible] def Tacenta.UnitLifecycleTamperedReply.TagMatches : Model.Lifecycle.Bytes →
  Model.Lifecycle.Bytes → Model.Lifecycle.Bytes → Prop :=
fun k2 ad c => List.drop (List.length c - 32) c = Model.Kdf.hmac k2 (ad ++ List.take (List.length c - 32) c)
-/
#guard_msgs in
#print Tacenta.UnitLifecycleTamperedReply.TagMatches

/--
info: def Tacenta.UnitLifecycleTamperedReply.AeadOpenChecksTagShape : Tacenta.UnitSatisfiabilityJoint.Interp → Prop :=
fun I =>
  ∀ (k1 k2 : Std.Array U8 32#usize) (iv : Std.Array U8 16#usize) (c ad : Slice U8) (v : alloc.vec.Vec U8),
    I.aeadDecrypt k1 k2 iv c ad = ok (core.result.Result.Ok v) →
      Tacenta.UnitLifecycleTamperedReply.TagMatches (Tacenta.UnitLifecycleT3.arrayOf k2)
        (Tacenta.UnitLifecycleT3.sliceOf ad) (Tacenta.UnitLifecycleT3.sliceOf c)
-/
#guard_msgs in
#print Tacenta.UnitLifecycleTamperedReply.AeadOpenChecksTagShape

/--
info: def Tacenta.UnitLifecycleTamperedReply.AeadOpenChecksTag : Prop :=
Tacenta.UnitLifecycleTamperedReply.AeadOpenChecksTagShape Tacenta.UnitSatisfiabilityJoint.Interp.real
-/
#guard_msgs in
#print Tacenta.UnitLifecycleTamperedReply.AeadOpenChecksTag

/--
info: def Tacenta.UnitLifecycleTamperedReply.NotTagged : Model.Lifecycle.Bytes →
  Model.Lifecycle.Bytes → Model.Lifecycle.Bytes → Prop :=
fun k2 ad c => ¬Tacenta.UnitLifecycleTamperedReply.TagMatches k2 ad c
-/
#guard_msgs in
#print Tacenta.UnitLifecycleTamperedReply.NotTagged

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
info: def Tacenta.UnitLifecycleTamperedReply.toyTag : Std.Array U8 32#usize → Slice U8 → List U8 → List U8 :=
fun k2 ad body =>
  List.map Tacenta.UnitSatisfiabilityBraidAgreements.toU8
    (Model.Kdf.hmac (Tacenta.UnitLifecycleT3.arrayOf k2)
      (Tacenta.UnitLifecycleT3.sliceOf ad ++ List.map Tacenta.SessionUnitBraidT3.u8 body))
-/
#guard_msgs in
#print Tacenta.UnitLifecycleTamperedReply.toyTag

/--
info: def Tacenta.UnitLifecycleTamperedReply.sealTagged : Std.Array U8 32#usize → Slice U8 → Slice U8 → alloc.vec.Vec U8 :=
fun k2 p ad =>
  if h : (↑p).length + 32 ≤ Usize.max then
    ⟨↑p ++ Tacenta.UnitLifecycleTamperedReply.toyTag k2 ad ↑p,
      (⋯ : (↑p ++ Tacenta.UnitLifecycleTamperedReply.toyTag k2 ad ↑p).length ≤ Usize.max)⟩
  else ⟨↑p, (⋯ : (↑p).length ≤ Usize.max)⟩
-/
#guard_msgs in
#print Tacenta.UnitLifecycleTamperedReply.sealTagged

/--
info: def Tacenta.UnitLifecycleTamperedReply.openTagged : Std.Array U8 32#usize →
  Slice U8 → Slice U8 → core.result.Result (alloc.vec.Vec U8) Unit :=
fun k2 c ad =>
  if
      List.drop (List.length (Tacenta.UnitLifecycleT3.sliceOf c) - 32) (Tacenta.UnitLifecycleT3.sliceOf c) =
        Model.Kdf.hmac (Tacenta.UnitLifecycleT3.arrayOf k2)
          (Tacenta.UnitLifecycleT3.sliceOf ad ++
            List.take (List.length (Tacenta.UnitLifecycleT3.sliceOf c) - 32) (Tacenta.UnitLifecycleT3.sliceOf c)) then
    core.result.Result.Ok ⟨List.take ((↑c).length - 32) ↑c, (⋯ : (List.take ((↑c).length - 32) ↑c).length ≤ Usize.max)⟩
  else core.result.Result.Err ()
-/
#guard_msgs in
#print Tacenta.UnitLifecycleTamperedReply.openTagged

/--
info: def Tacenta.UnitLifecycleTamperedReply.Interp.modelTagged : Tacenta.UnitSatisfiabilityJoint.Interp :=
have __src := Tacenta.UnitLifecycleResponderReplyReceipt.Interp.modelReply;
{ PrivateKey := __src.PrivateKey, PublicKeyBytes := __src.PublicKeyBytes, KemKeyPair := __src.KemKeyPair,
  IncrementalKeyPair := __src.IncrementalKeyPair, EncapsState := __src.EncapsState, Zeroizing := __src.Zeroizing,
  dhPrivFromBytes := __src.dhPrivFromBytes, dhPrivPublicKey := __src.dhPrivPublicKey, dhPrivAgree := __src.dhPrivAgree,
  dhPrivToBytes := __src.dhPrivToBytes, dhPubFromBytes := __src.dhPubFromBytes, dhPubAsBytes := __src.dhPubAsBytes,
  dhPubEq := __src.dhPubEq, dhIsPrimeOrderPublic := __src.dhIsPrimeOrderPublic,
  aeadEncrypt := fun x k2 x_1 p ad => ok (Tacenta.UnitLifecycleTamperedReply.sealTagged k2 p ad),
  aeadDecrypt := fun x k2 x_1 c ad => ok (Tacenta.UnitLifecycleTamperedReply.openTagged k2 c ad),
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
#print Tacenta.UnitLifecycleTamperedReply.Interp.modelTagged

/--
info: def Tacenta.UnitLifecycleTamperedReply.InterpO.modelTagged : Tacenta.UnitOracleShape.InterpO :=
have __src := Tacenta.UnitLifecycleTamperedReply.Interp.modelTagged;
{ toInterp := __src, xeddsaSign := fun {R} => Tacenta.UnitOracleModel.signModelO }
-/
#guard_msgs in
#print Tacenta.UnitLifecycleTamperedReply.InterpO.modelTagged

/--
info: def Tacenta.UnitLifecycleTamperedReply.viewTagged : Tacenta.UnitLifecycleDecryptRatchetScreen.DhViewShape
  Tacenta.UnitLifecycleTamperedReply.Interp.modelTagged :=
{ privateKey := Tacenta.UnitLifecycleT3.arrayOf, publicKey := Tacenta.UnitLifecycleT3.arrayOf }
-/
#guard_msgs in
#print Tacenta.UnitLifecycleTamperedReply.viewTagged

/--
info: def Tacenta.UnitLifecycleTamperedReply.dhViewTagged : Tacenta.UnitOracleShape.DhViewOf
  Tacenta.UnitLifecycleTamperedReply.InterpO.modelTagged.toInterp :=
{ privateKey := Tacenta.UnitLifecycleTamperedReply.viewTagged.privateKey,
  publicKey := Tacenta.UnitLifecycleTamperedReply.viewTagged.publicKey }
-/
#guard_msgs in
#print Tacenta.UnitLifecycleTamperedReply.dhViewTagged

/--
info: def Tacenta.UnitLifecycleTamperedReply.kemViewTagged : Tacenta.UnitOracleShape.KemViewOf
  Tacenta.UnitLifecycleTamperedReply.InterpO.modelTagged.toInterp :=
{ keyPair := fun x => [] }
-/
#guard_msgs in
#print Tacenta.UnitLifecycleTamperedReply.kemViewTagged

/--
info: def Tacenta.UnitLifecycleTamperedReply.openTaggedLenient : Slice U8 → core.result.Result (alloc.vec.Vec U8) Unit :=
fun c =>
  if 32 ≤ (↑c).length then
    core.result.Result.Ok ⟨List.take ((↑c).length - 32) ↑c, (⋯ : (List.take ((↑c).length - 32) ↑c).length ≤ Usize.max)⟩
  else core.result.Result.Err ()
-/
#guard_msgs in
#print Tacenta.UnitLifecycleTamperedReply.openTaggedLenient

/--
info: def Tacenta.UnitLifecycleTamperedReply.Interp.modelTaggedLenient : Tacenta.UnitSatisfiabilityJoint.Interp :=
have __src := Tacenta.UnitLifecycleTamperedReply.Interp.modelTagged;
{ PrivateKey := __src.PrivateKey, PublicKeyBytes := __src.PublicKeyBytes, KemKeyPair := __src.KemKeyPair,
  IncrementalKeyPair := __src.IncrementalKeyPair, EncapsState := __src.EncapsState, Zeroizing := __src.Zeroizing,
  dhPrivFromBytes := __src.dhPrivFromBytes, dhPrivPublicKey := __src.dhPrivPublicKey, dhPrivAgree := __src.dhPrivAgree,
  dhPrivToBytes := __src.dhPrivToBytes, dhPubFromBytes := __src.dhPubFromBytes, dhPubAsBytes := __src.dhPubAsBytes,
  dhPubEq := __src.dhPubEq, dhIsPrimeOrderPublic := __src.dhIsPrimeOrderPublic, aeadEncrypt := __src.aeadEncrypt,
  aeadDecrypt := fun x x_1 x_2 c x_3 => ok (Tacenta.UnitLifecycleTamperedReply.openTaggedLenient c),
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
#print Tacenta.UnitLifecycleTamperedReply.Interp.modelTaggedLenient

/--
info: def Tacenta.UnitLifecycleTamperedReply.Interp.modelTaggedTop : Tacenta.UnitSatisfiabilityJoint.Interp :=
have __src := Tacenta.UnitLifecycleTamperedReply.Interp.modelTagged;
{ PrivateKey := __src.PrivateKey, PublicKeyBytes := __src.PublicKeyBytes, KemKeyPair := __src.KemKeyPair,
  IncrementalKeyPair := __src.IncrementalKeyPair, EncapsState := __src.EncapsState, Zeroizing := __src.Zeroizing,
  dhPrivFromBytes := __src.dhPrivFromBytes, dhPrivPublicKey := __src.dhPrivPublicKey, dhPrivAgree := __src.dhPrivAgree,
  dhPrivToBytes := __src.dhPrivToBytes, dhPubFromBytes := __src.dhPubFromBytes, dhPubAsBytes := __src.dhPubAsBytes,
  dhPubEq := __src.dhPubEq, dhIsPrimeOrderPublic := __src.dhIsPrimeOrderPublic,
  aeadEncrypt := fun x k2 x_1 p ad =>
    if (↑p).length + (↑ad).length + 32 ≤ Usize.max / 2 then ok (Tacenta.UnitLifecycleTamperedReply.sealTagged k2 p ad)
    else fail Error.panic,
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
#print Tacenta.UnitLifecycleTamperedReply.Interp.modelTaggedTop
