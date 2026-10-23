import Translation.UnitLifecycleResponderFirstFrame

/-!
# The responder's first receipt: `establish_responder` accepts the initiator's first frame

`UnitLifecycleResponderFirstFrame` feeds the bytes the initiator's first `encrypt` emits to the responder's
`establish_responder` and shows that only the three refusals the store decides remain before the inner receive.
This module finishes that route with the success outcome and its effects: on the same bytes, the inner
`decrypt_ratchet` returns the plaintext the initiator encrypted, and the whole call succeeds with its exact return
value, the store after `ResponderCommit`, and one draw from the responder's source.  Two public roots are composed
in one run: the bytes the initiator's `encrypt` returns are the input of the responder's `establish_responder`, each
at the state its own route derives.

## Auxiliary specification (the model alone)

The model's key derivations are concrete code, so the first message key needs no oracle assumption once the
receiver's classical root `ec` and the agreement `d` derive the sender's root and chain:
* `first_send_key`, `first_receive_key`, `first_receive_with_eviction`: the model Triple's first send from the
  sender pair form (`firstSenderTriple`) and its first receive at the receiver pair form (`firstReceiverTriple`)
  give the same key `firstKey`, when `kdfRk ec d = (rkA, cksA)`.
* `decode_encodeMessage`: the model's ratchet-message decoder inverts its encoder (on the kernel alone, through
  `readBe64_be64_kernel` and `readBe16_be16_kernel`; the model's own round trips are `bv_decide` proofs).
* `first_frame_model_outcomes`: every outcome of the model's `decryptRatchet` on the first frame at the receiver
  pair: `ceiling` (no draw), the candidate agreement refused, the AEAD open refused, or the open's plaintext with
  the successor `firstReceiptSession`.  The Braid's output at this step is `none` whatever chunk the view names.

## The composition

* Bridges, each from the two runs: `first_init_pair` (the two Triple initialisers on one secret give the pair
  form; no hypothesis), `established_triple_first`, `responder_triple_first`, `first_kdf_model` (the code's
  root-key step is the model's, under the agreements the decrypt refinement takes), `parts_of_first_frame`,
  `responder_first_agreement` (the responder's first agreement is the initiator's `dh_out`, by `DhAgreeSymmetric`
  and the initiator's own check), `responder_candidate_agreement` (`DhAgreeContributory`), `first_identityAd_eq`,
  `aead_open_sealed` (`AeadRoundTrip`, through the two oracle records).
* The received chunk: `first_receipt_run_inputs`, at `attributedView`, the view that reads the frame's codeword as
  the initiator's header source.  The codeword half of the chunk relation is derived (the decoded real codeword is
  a codeword of that source, `held_encoder`); the attribution half is the view's construction.  The real-level
  conclusions (bytes, store, draws, call result) do not mention the view; only the model session the successor is
  related to does.
* `responder_first_frame_inner_outcomes` and `responder_first_frame_outcomes`: without `DhAgreeContributory` and
  `AeadRoundTrip`, the inner receive (and so the whole call, past the store's refusals) returns exactly one of
  `Handshake(NonContributoryAgreement)` (the responder oracle refuses the draw's agreement with the initiator's
  ratchet key), `Aead` (the responder oracle's open of the initiator oracle's seal is refused), each with the store
  as given and one draw taken, or what the open returned.
* `responder_first_frame_inner_succeeds`, `responder_first_frame_succeeds`: with the two laws, success with the
  initiator's plaintext; the whole call returns `Ok (session, bytes)`, `ResponderCommit` of the bundle's
  identifiers (on the last-resort path with the fingerprint of the initiator's shared secret), one draw, and the
  session refines `firstReceiptSession`.
* `initiator_first_send_responder_receives` (the composed statement) and `initiator_first_send_responder_outcomes`:
  from a successful first `encrypt` at an establishment output (`established_encrypt_outcomes`), the two arms
  above on the bytes it returned, with the initiator's two draws, the message key and the header source pinned.
  Kernel-checked over the opaque externals their pins list; the nine `native_decide` constants the encrypt
  and decrypt refinements carried until 2026-10-21 are kernel proofs now.

## The laws and premises

* `AeadRoundTrip` (`AeadRoundTripShape Interp.real`, new, assumed): the boundary AEAD opens what it sealed, for a
  plaintext of at most `Usize.max - 48` bytes.  By reading `boundary/src/aead.rs` (CBC with PKCS#7 padding, then
  HMAC over the associated data and the ciphertext; open checks the tag, decrypts and unpads); not checked in
  Lean.  Model: `modelFirstReceipt_aeadRoundTrip`.
* `DhAgreeContributory` (`DhAgreeContributoryShape Interp.real`, new, assumed): an agreement of any private key
  with a public key `public_key` returned is not refused.  By reading for X25519 (a clamped scalar times a
  prime-order point is not the identity); not checked in Lean.  Model: `modelFirstReceipt_contributory`.
* Per run: the responder's trace is its oracle's and holds a draw; the store bound of
  `establish_responder_no_panic` (`EstablishResponderHeadroom`) for the commit.  `KeyGenSizesOf` of the initiator's
  oracle's KEM (a law of the encrypt branch) gives the header source its 96 bytes.
* Reused: everything `responder_first_frame_prepares` and `established_encrypt_outcomes` take, and the decrypt
  agreements at the responder oracle's KEM.

## Non-vacuity

* `first_receipt_laws_model`: every law above, with the decrypt, establishment, restore, encrypt and first-frame
  laws, holds in one interpretation, `InterpO.modelFirstReceipt` (the first-frame joint model with the toy seal and
  open of `UnitOracleModel`).
* `first_send_receive_reachable`: at the real constants, under those laws, one run from
  `publish` through the establishment and the first send to the responder's **success** exists (last-resort path,
  empty plaintext).

## What it does not show

* That a tampered or foreign frame is refused: no AEAD authenticity law is assumed.
* The successor's `Session::invariant` and its four counter ceilings: not here (`UnitLifecycleResponderSuccessor`
  derives both at the session the call returns).
* A second delivery of the same bytes here (`UnitLifecycleResponderRepeatedFrame` and
  `UnitLifecycleResponderEstablishReplay` take it, on the same run); the responder's reply (its `encrypt` is
  `UnitLifecycleResponderReply`'s), the initiator's receipt of it (`UnitLifecycleResponderReplyReceipt`'s), any later
  message.
* That the real primitives meet the laws, that ML-KEM decapsulation agrees on a run (`FirstKemAgrees`; by reading the
  wrapper's implicit rejection, a decapsulation failure returns another secret and would, barring an HMAC collision,
  surface as `Aead`, not `Kem`; not shown), `PrekeyIdsDistinct` from `PrekeyStore::invariant`, the one-time path in a
  run, the model's own `establishResponder` equality.  A source with no state of its own, such as `OsRng`, is outside
  the statements about draws.
-/

namespace Tacenta.UnitLifecycleResponderFirstReceipt

open Aeneas Aeneas.Std Result
open tacenta_session_unit
open Tacenta.SessionUnitRatchetImportInv (bind_eq_ok_inv bind2_eq_ok_inv bind3_eq_ok_inv)
open Tacenta.UnitLifecycleT3 (DhView DhCodecOf vecOf sliceOf arrayOf SessionRefines StepRefines ResultRefines)
open Tacenta.UnitLifecycleEstablishInitiatorShape (InitiatorOutputParts initiatorTriple initChains
  DhPublicValid establishedModelOf)
open Tacenta.UnitLifecycleEstablishResponder (z32 ResponderPreparedParts responderTriple responderChains
  responderModelOf ResponderCommit)
open Tacenta.UnitLifecycleEstablishedEncrypt (firstFrame firstComposite initialWire)
open Tacenta.UnitLifecycleResponderFirstFrame (InitiatorSecretParts DhAgreeSymmetric dhAgreeSymmetric_is
  PrekeyIdsDistinct FirstKemAgrees StoreRefusal)
open Tacenta.UnitLifecycleDecryptRatchetT3 (DecryptOracleOf DecryptRatchetAgreements)
open Tacenta.UnitLifecycleDecryptRunBounds (DecryptRatchetRunInputs)

/-! ## Auxiliary specification: the first message on both sides

Statements about the model's functions alone, with symbolic keys.  The model's key derivations are concrete
code (`Model.State.kdfRk`, `kdfCk`, `Model.SparseRatchet.kdfCk`), so that the first message key the receiver
derives equals the sender's is a computation once the receiver's classical root and the sender's root before its
derivation agree with the agreement value. -/

section Auxiliary
open Model.State (Key)

/-- The model Triple of a sender before its first message, in the form the initiator's establishment leaves:
our ratchet key `a4`, the peer's `peer`, root `rkA` and sending chain `cksA` after the first derivation, no
receiving chain, counters 0; one sparse chain entry at epoch 0, sending on `k1` and receiving on `k2`. -/
def firstSenderTriple (a4 peer rkA cksA prk k1 k2 : Key) : Model.Triple.State :=
  { classical :=
      { dhsPub := a4, dhrPub := some peer, rk := rkA, cks := some cksA, ckr := none, ns := 0, nr := 0,
        pn := 0, skipped := [], events := 0, labels := .tacenta }
    postQuantum :=
      { rk := prk, epoch := 0, chains := [(0, { send := some ⟨k1, 0⟩, receive := some ⟨k2, 0⟩ })],
        skipped := [], direction := .a2b } }

/-- The model Triple of a receiver before its first message, in the form the responder's preparation leaves:
our ratchet key `b`, no peer key, root `ec`, no chains, counters 0; one sparse chain entry at epoch 0, sending
on `k2` and receiving on `k1`. -/
def firstReceiverTriple (b ec prk k1 k2 : Key) : Model.Triple.State :=
  { classical :=
      { dhsPub := b, dhrPub := none, rk := ec, cks := none, ckr := none, ns := 0, nr := 0,
        pn := 0, skipped := [], events := 0, labels := .tacenta }
    postQuantum :=
      { rk := prk, epoch := 0, chains := [(0, { send := some ⟨k2, 0⟩, receive := some ⟨k1, 0⟩ })],
        skipped := [], direction := .b2a } }

/-- The Triple header of a first message: ratchet key `a4`, classical numbers 0 and 0, sparse epoch 0 and
sparse message number 1. -/
def firstHeader (a4 : Key) : Model.Triple.Header := ⟨⟨a4, 0, 0⟩, 0, 1⟩

/-- The first message key: the combination of the classical message key of `cksA` and the sparse message key
of `k1` at number 1. -/
def firstKey (cksA k1 : Key) : Key :=
  Model.TripleRatchet.combine (Model.State.kdfCk cksA).2 (Model.SparseRatchet.kdfCk k1 1).2

/-- The sender's Triple after its first message. -/
def senderAfterFirst (a4 peer rkA cksA prk k1 k2 : Key) : Model.Triple.State :=
  { classical :=
      { dhsPub := a4, dhrPub := some peer, rk := rkA, cks := some (Model.State.kdfCk cksA).1, ckr := none,
        ns := 1, nr := 0, pn := 0, skipped := [], events := 0, labels := .tacenta }
    postQuantum :=
      { rk := prk, epoch := 0,
        chains := [(0, { send := some ⟨(Model.SparseRatchet.kdfCk k1 1).1, 1⟩, receive := some ⟨k2, 0⟩ })],
        skipped := [], direction := .a2b } }

/-- The receiver's Triple after the first message, with agreement `d` from the header's key, `dSend` from
the fresh key and its public key `newPub`: one Diffie-Hellman step from root `ec` (receiving chain stepped
once, clock 1), the sparse receiving chain stepped once to number 1. -/
def receiverAfterFirst (ec prk k1 k2 a4 d dSend newPub : Key) : Model.Triple.State :=
  { classical :=
      { dhsPub := newPub, dhrPub := some a4,
        rk := (Model.State.kdfRk (Model.State.kdfRk ec d .tacenta).1 dSend .tacenta).1,
        cks := some (Model.State.kdfRk (Model.State.kdfRk ec d .tacenta).1 dSend .tacenta).2,
        ckr := some (Model.State.kdfCk (Model.State.kdfRk ec d .tacenta).2).1,
        ns := 0, nr := 1, pn := 0, skipped := [], events := 1, labels := .tacenta }
    postQuantum :=
      { rk := prk, epoch := 0,
        chains := [(0, { send := some ⟨k2, 0⟩, receive := some ⟨(Model.SparseRatchet.kdfCk k1 1).1, 1⟩ })],
        skipped := [], direction := .b2a } }

/-- **The model's first send from the sender pair form**: header `firstHeader a4`, key `firstKey cksA k1`,
successor `senderAfterFirst`.  Hypothesis-free. -/
theorem first_send_key (a4 peer rkA cksA prk k1 k2 : Key) :
    Model.Triple.sendDetailed (firstSenderTriple a4 peer rkA cksA prk k1 k2) 0 none =
      .ok (senderAfterFirst a4 peer rkA cksA prk k1 k2, firstHeader a4, firstKey cksA k1) := by
  simp [Model.Triple.sendDetailed, Model.Ratchet.sendDetailed, Model.SparseRatchet.sendDetailed,
    Model.SparseRatchet.maybeAdvanceDetailed, Model.SparseRatchet.findChains, firstSenderTriple,
    senderAfterFirst, firstHeader, firstKey, Model.State.u32Max, Model.SparseRatchet.u64Max,
    Model.SparseRatchet.setChains]

/-- **The model's first receive at the receiver pair form derives the sender's key**: if the receiver's root
`ec` and the agreement `d` derive the sender's root and sending chain (`kdfRk ec d = (rkA, cksA)`), then for
every fresh agreement `dSend` and public key `newPub` the receive of `firstHeader a4` succeeds with key
`firstKey cksA k1` and successor `receiverAfterFirst`. -/
theorem first_receive_key (b ec prk k1 k2 a4 d dSend newPub rkA cksA : Key)
    (hkdf : Model.State.kdfRk ec d .tacenta = (rkA, cksA)) :
    Model.Triple.receiveDetailed (firstReceiverTriple b ec prk k1 k2) (firstHeader a4) d dSend newPub none =
      .ok (receiverAfterFirst ec prk k1 k2 a4 d dSend newPub, firstKey cksA k1) := by
  simp [Model.Triple.receiveDetailed, Model.Ratchet.receiveDetailed, Model.Ratchet.trySkipped,
    Model.Ratchet.skipMessageKeysDetailed, Model.State.skipMessageKeys, Model.Ratchet.dhRatchet,
    Model.SparseRatchet.receiveDetailed, Model.SparseRatchet.maybeAdvanceReceiveDetailed,
    Model.SparseRatchet.maybeAdvanceDetailed, Model.SparseRatchet.trySkipped,
    Model.SparseRatchet.skipMessageKeysDetailed, Model.SparseRatchet.skipMessageKeys,
    Model.SparseRatchet.findChains, Model.SparseRatchet.setChains, firstReceiverTriple, firstHeader,
    receiverAfterFirst, firstKey, Model.State.ageStore, Model.State.u32Max, Model.SparseRatchet.u64Max,
    Model.State.maxEvents, hkdf]

/-- The same through the session's receive with eviction: its first arm, with no eviction. -/
theorem first_receive_with_eviction (b ec prk k1 k2 a4 d dSend newPub rkA cksA : Key)
    (composite : Model.CompositeHeader.Composite)
    (hkdf : Model.State.kdfRk ec d .tacenta = (rkA, cksA)) :
    Model.Lifecycle.receiveWithEviction (firstReceiverTriple b ec prk k1 k2) composite (firstHeader a4) d dSend
      newPub none = .ok (receiverAfterFirst ec prk k1 k2 a4 d dSend newPub, firstKey cksA k1) := by
  unfold Model.Lifecycle.receiveWithEviction
  rw [first_receive_key b ec prk k1 k2 a4 d dSend newPub rkA cksA hkdf]

/-- Reading eight big-endian bytes back gives the value written, on the kernel alone (the model's own
`readBe64_be64` is a `bv_decide` proof). -/
theorem readBe64_be64_kernel (n : UInt64) (rest : List UInt8) :
    Model.CompositeHeader.readBe64 (Model.CompositeHeader.be64 n ++ rest) = some (n, rest) := by
  rw [Tacenta.SessionUnitWireT3.readBe64_of_length _ (by simp [Model.CompositeHeader.be64])]
  simp only [Model.CompositeHeader.be64, List.cons_append, List.nil_append, List.getElem!_cons_zero,
    List.getElem!_cons_succ, List.drop_succ_cons, List.drop_zero, Option.some.injEq, Prod.mk.injEq,
    and_true]
  apply UInt64.toNat.inj
  simp only [UInt64.toNat_ofNat', UInt64.toNat_toUInt8, UInt64.toNat_shiftRight]
  have hn := n.toNat_lt
  simp only [show (56 : UInt64).toNat % 64 = 56 from rfl, show (48 : UInt64).toNat % 64 = 48 from rfl,
    show (40 : UInt64).toNat % 64 = 40 from rfl, show (32 : UInt64).toNat % 64 = 32 from rfl,
    show (24 : UInt64).toNat % 64 = 24 from rfl, show (16 : UInt64).toNat % 64 = 16 from rfl,
    show (8 : UInt64).toNat % 64 = 8 from rfl]
  simp only [Nat.shiftRight_eq_div_pow]
  omega

/-- Reading two big-endian bytes back gives the value written, on the kernel alone. -/
theorem readBe16_be16_kernel (n : UInt16) (rest : List UInt8) :
    Model.CompositeHeader.readBe16 (Model.CompositeHeader.be16 n ++ rest) = some (n, rest) := by
  rw [Tacenta.SessionUnitWireT3.readBe16_of_length _ (by simp [Model.CompositeHeader.be16])]
  simp only [Model.CompositeHeader.be16, List.cons_append, List.nil_append, List.getElem!_cons_zero,
    List.getElem!_cons_succ, List.drop_succ_cons, List.drop_zero, Option.some.injEq, Prod.mk.injEq,
    and_true]
  apply UInt16.toNat.inj
  simp only [UInt16.toNat_ofNat', UInt16.toNat_toUInt8, UInt16.toNat_shiftRight]
  have hn := n.toNat_lt
  simp only [show (8 : UInt16).toNat % 16 = 8 from rfl]
  simp only [Nat.shiftRight_eq_div_pow]
  omega

open Tacenta.UnitLifecycleEstablishResponder (takeSplit_append readBe32_be32) in
/-- **The model's ratchet-message decoder inverts its encoder**, for a header whose ratchet key is 32 canonical
bytes and whose codeword, if any, carries 32 bytes, and for every ciphertext. -/
theorem decode_encodeMessage (h : Model.CompositeHeader.Composite) (ct : List UInt8)
    (hdh : h.dh.length = 32) (hkey : Model.Messages.checkKey h.dh = some ())
    (hc : ∀ c, h.agChunk = some c → c.data.length = 32) :
    Model.CompositeHeader.decode (Model.CompositeHeader.encodeMessage h ct) = some (h, ct) := by
  obtain ⟨dh, pn, n, pqE, pqN, agE, agT, agC⟩ := h
  simp only at hdh hkey hc
  have htake : ∀ R : List UInt8, Model.Messages.take? 32 (dh ++ R) = some (dh, R) := fun R => by
    have := takeSplit_append dh R
    rwa [hdh] at this
  cases agC with
  | none =>
    simp only [Model.CompositeHeader.decode, Model.CompositeHeader.encodeMessage, Model.CompositeHeader.encode,
      List.append_assoc, List.cons_append, List.nil_append, Model.Messages.version, Model.Messages.typeRatchet,
      bne_self_eq_false, Bool.false_eq_true, if_false, Option.bind_eq_bind, htake, Option.bind_some, hkey,
      readBe32_be32, readBe64_be64_kernel]
    simp [Model.CompositeHeader.encodeChunk, Model.CompositeHeader.decode_encode_agreementType,
      readBe16_be16_kernel, Model.Messages.take?, Model.CompositeHeader.chunkBytes]
    rw [if_neg (by omega)]
    simp
  | some c =>
    have hcl := hc c rfl
    have h2 := takeSplit_append c.data ct
    rw [hcl] at h2
    simp only [Model.CompositeHeader.decode, Model.CompositeHeader.encodeMessage, Model.CompositeHeader.encode,
      List.append_assoc, List.cons_append, List.nil_append, Model.Messages.version, Model.Messages.typeRatchet,
      bne_self_eq_false, Bool.false_eq_true, if_false, Option.bind_eq_bind, htake, Option.bind_some, hkey,
      readBe32_be32, readBe64_be64_kernel]
    simp [Model.CompositeHeader.encodeChunk, Model.CompositeHeader.decode_encode_agreementType,
      readBe16_be16_kernel, Model.CompositeHeader.chunkBytes, h2]

/-- The associated data the first frame is sealed under: the sender's associated data, then the encoded
composite header. -/
def firstAd (view : Model.Lifecycle.CodewordView) (m : Model.Lifecycle.Session) (chunk : Model.Braid.Chunk) :
    Model.Lifecycle.Bytes :=
  Model.Messages.concatAd m.identityAd (Model.CompositeHeader.encode (firstComposite view m chunk))

/-- The receiver oracle's open of the sender oracle's seal of `pt` under the AEAD keys of the message key `mk`,
with associated data `ad` on both sides. -/
def firstOpen (oracleA oracleB : Model.Lifecycle.Oracle) (mk : Key) (pt ad : Model.Lifecycle.Bytes) :
    Option Model.Lifecycle.Bytes :=
  oracleB.aeadOpen (Model.State.messageKeys mk .tacenta).1 (Model.State.messageKeys mk .tacenta).2.1
    (Model.State.messageKeys mk .tacenta).2.2
    (oracleA.aeadSeal (Model.State.messageKeys mk .tacenta).1 (Model.State.messageKeys mk .tacenta).2.1
      (Model.State.messageKeys mk .tacenta).2.2 pt ad) ad

/-- The receiver's model session after the first message: the Triple `receiverAfterFirst`, the Braid still
waiting for the header with the received chunk `rcv` in its decoder, and the ratchet key replaced by the draw
`c` unless the new public key equals the old. -/
def firstReceiptSession (mB : Model.Lifecycle.Session) (secret : Model.Lifecycle.Bytes) (rcv : Model.Braid.Chunk)
    (ec prk k1 k2 a4 d dSend newPub c : Key) : Model.Lifecycle.Session :=
  { mB with
    triple := receiverAfterFirst ec prk k1 k2 a4 d dSend newPub
    braid := .noHeaderReceived 1 (Model.Braid.Auth.init 1 secret)
      ((Model.Braid.Decoder.new (Model.Braid.headerSize + Model.Braid.macSize)).addChunk rcv)
    ratchetPrivate := if newPub == mB.triple.classical.dhsPub then mB.ratchetPrivate else c }

/-- **Every outcome of the model's `decryptRatchet` on the first frame of the sender pair at the receiver pair**,
model only, without the draw, the candidate agreement or the AEAD as hypotheses (the first agreement, the root
relation, the associated data, the Braid and the decode side conditions as in `first_frame_model_decrypts`).  The
step is exactly one of:
* the oracle holds no draw: `ceiling`, session and oracle unchanged;
* the draw `c`'s agreement with the frame's ratchet key is refused: `handshake nonContributoryAgreement`, session
  unchanged, the draw consumed;
* that agreement returns `dSend` and the receiver's open of the sender's seal is refused: `aead`, session
  unchanged, the draw consumed;
* the open returns `x`: the step returns `x`, consumes the draw and leaves `firstReceiptSession`.
No other refusal (`agreementFailed`, `decode`, the first agreement, `triple`) occurs. -/
theorem first_frame_model_outcomes (viewA viewB : Model.Lifecycle.CodewordView)
    (oracleA oracleB : Model.Lifecycle.Oracle) (mA mB : Model.Lifecycle.Session)
    (a4 peer b rkA cksA prk k1 k2 ec : Model.State.Key) (secret pt : Model.Lifecycle.Bytes)
    (chunk : Model.Braid.Chunk) (d : Model.State.Key)
    (hA : mA.triple = firstSenderTriple a4 peer rkA cksA prk k1 k2)
    (hB : mB.triple = firstReceiverTriple b ec prk k1 k2)
    (hkdf : Model.State.kdfRk ec d .tacenta = (rkA, cksA))
    (hbraid : mB.braid = Model.Braid.initBob secret)
    (had : mB.identityAd = mA.identityAd)
    (hlen : a4.length = 32) (hkey : Model.Messages.checkKey a4 = some ())
    (hchunk : (viewA.send mA.braid chunk).data.length = 32)
    (hagree : oracleB.dhAgree mB.ratchetPrivate a4 = some d) :
    (oracleB.draws = [] ∧
      Model.Lifecycle.decryptRatchet viewB oracleB mB (firstFrame viewA oracleA mA pt (firstKey cksA k1) chunk) =
        { session := mB, result := .error .ceiling, oracle := oracleB }) ∨
    (∃ c rest, oracleB.draws = c :: rest ∧ oracleB.dhAgree c a4 = none ∧
      Model.Lifecycle.decryptRatchet viewB oracleB mB (firstFrame viewA oracleA mA pt (firstKey cksA k1) chunk) =
        { session := mB, result := .error (.handshake .nonContributoryAgreement),
          oracle := { oracleB with draws := rest } }) ∨
    (∃ c rest dSend, oracleB.draws = c :: rest ∧ oracleB.dhAgree c a4 = some dSend ∧
      firstOpen oracleA oracleB (firstKey cksA k1) pt (firstAd viewA mA chunk) = none ∧
      Model.Lifecycle.decryptRatchet viewB oracleB mB (firstFrame viewA oracleA mA pt (firstKey cksA k1) chunk) =
        { session := mB, result := .error .aead, oracle := { oracleB with draws := rest } }) ∨
    (∃ c rest dSend x, oracleB.draws = c :: rest ∧ oracleB.dhAgree c a4 = some dSend ∧
      firstOpen oracleA oracleB (firstKey cksA k1) pt (firstAd viewA mA chunk) = some x ∧
      Model.Lifecycle.decryptRatchet viewB oracleB mB (firstFrame viewA oracleA mA pt (firstKey cksA k1) chunk) =
        { session := firstReceiptSession mB secret
            (viewB.receive mB.braid (viewA.send mA.braid chunk).index (viewA.send mA.braid chunk).data)
            ec prk k1 k2 a4 d dSend (oracleB.dhPublic c) c
          result := .ok x
          oracle := { oracleB with draws := rest } }) := by
  have hdh : (firstComposite viewA mA chunk).dh = a4 := by
    simp [firstComposite, hA, firstSenderTriple]
  have hdec : Model.CompositeHeader.decodeDetailed (firstFrame viewA oracleA mA pt (firstKey cksA k1) chunk) =
      .ok (firstComposite viewA mA chunk,
        oracleA.aeadSeal (Model.State.messageKeys (firstKey cksA k1) .tacenta).1
          (Model.State.messageKeys (firstKey cksA k1) .tacenta).2.1
          (Model.State.messageKeys (firstKey cksA k1) .tacenta).2.2 pt (firstAd viewA mA chunk)) := by
    rw [Model.CompositeHeader.decodeDetailed_ok_iff]
    exact decode_encodeMessage _ _ (by rw [hdh]; exact hlen) (by rw [hdh]; exact hkey)
      (fun c hc => by simp [firstComposite] at hc; subst hc; exact hchunk)
  have hhdr : Model.Lifecycle.tripleHeaderOf (firstComposite viewA mA chunk) = firstHeader a4 := by
    simp [Model.Lifecycle.tripleHeaderOf, firstComposite, hA, firstSenderTriple, firstHeader]
  have hbr : Model.Braid.receive oracleB.braidKem mB.braid
      (Model.Lifecycle.braidMessageOf viewB mB.braid (firstComposite viewA mA chunk)) =
      (0, none, .noHeaderReceived 1 (Model.Braid.Auth.init 1 secret)
        ((Model.Braid.Decoder.new (Model.Braid.headerSize + Model.Braid.macSize)).addChunk
          (viewB.receive mB.braid (viewA.send mA.braid chunk).index (viewA.send mA.braid chunk).data))) := by
    rw [hbraid]
    simp [Model.Braid.receive, Model.Braid.initBob, Model.Lifecycle.braidMessageOf, firstComposite,
      Model.Lifecycle.braidTypeOf, Model.Braid.Decoder.addChunk, Model.Braid.Decoder.new,
      Model.Braid.Decoder.message, Model.Braid.Decoder.hasMessage, Model.Braid.chunkBytes,
      Model.Braid.headerSize, Model.Braid.macSize, Model.Braid.BraidState.epoch]
  have hfail : Model.Lifecycle.agreementFailed mB = false := by
    simp [Model.Lifecycle.agreementFailed, hbraid, Model.Braid.initBob]
  have had' : Model.Messages.concatAd mB.identityAd
      (Model.CompositeHeader.encode (firstComposite viewA mA chunk)) = firstAd viewA mA chunk := by
    rw [had]; rfl
  rcases hdr : oracleB.draws with _ | ⟨c, rest⟩
  · left
    refine ⟨rfl, ?_⟩
    have hrand : Model.Lifecycle.random32 oracleB = none := by
      simp [Model.Lifecycle.random32, Model.Lifecycle.takeDraw, hdr]
    unfold Model.Lifecycle.decryptRatchet
    rw [hfail, if_neg (by simp), hdec]
    dsimp only
    rw [hbr]
    dsimp only
    rw [hdh, hagree]
    dsimp only
    rw [hrand]
  have hrand : Model.Lifecycle.random32 oracleB = some (c, { oracleB with draws := rest }) := by
    simp [Model.Lifecycle.random32, Model.Lifecycle.takeDraw, hdr]
  rcases hcand : oracleB.dhAgree c a4 with _ | dSend
  · right; left
    refine ⟨c, rest, rfl, hcand, ?_⟩
    unfold Model.Lifecycle.decryptRatchet
    rw [hfail, if_neg (by simp), hdec]
    dsimp only
    rw [hbr]
    dsimp only
    rw [hdh, hagree]
    dsimp only
    rw [hrand]
    dsimp only
    rw [hcand]
  have hrecv := first_receive_with_eviction b ec prk k1 k2 a4 d dSend (oracleB.dhPublic c) rkA cksA
    (firstComposite viewA mA chunk) hkdf
  rw [← hB, ← hhdr] at hrecv
  rcases hopen : firstOpen oracleA oracleB (firstKey cksA k1) pt (firstAd viewA mA chunk) with _ | x
  · right; right; left
    refine ⟨c, rest, dSend, rfl, hcand, rfl, ?_⟩
    unfold Model.Lifecycle.decryptRatchet
    rw [hfail, if_neg (by simp), hdec]
    dsimp only
    rw [hbr]
    dsimp only
    rw [hdh, hagree]
    dsimp only
    rw [hrand]
    dsimp only
    rw [hcand]
    dsimp only
    rw [show Model.Lifecycle.sparseOutputOf none = none from rfl, hrecv]
    dsimp only
    simp only [firstOpen] at hopen
    rw [had', hopen]
  · right; right; right
    refine ⟨c, rest, dSend, x, rfl, hcand, rfl, ?_⟩
    unfold Model.Lifecycle.decryptRatchet
    rw [hfail, if_neg (by simp), hdec]
    dsimp only
    rw [hbr]
    dsimp only
    rw [hdh, hagree]
    dsimp only
    rw [hrand]
    dsimp only
    rw [hcand]
    dsimp only
    rw [show Model.Lifecycle.sparseOutputOf none = none from rfl, hrecv]
    dsimp only
    simp only [firstOpen] at hopen
    rw [had', hopen]
    dsimp only
    simp [firstReceiptSession, hB, firstReceiverTriple, receiverAfterFirst]

end Auxiliary

/-! ## The two laws -/

open Tacenta.UnitSatisfiabilityJoint (Interp Interp.real)

/-- The boundary AEAD opens what it sealed, over an interpretation `I`: for keys, a plaintext of at most
`Usize.max - 48` bytes and associated data, if sealing returns a ciphertext then opening that ciphertext with the
same keys and associated data returns the plaintext. -/
def AeadRoundTripShape (I : Interp) : Prop :=
  ∀ (k1 k2 : Array U8 32#usize) (iv : Array U8 16#usize) (pt ad : Slice U8) (ct : alloc.vec.Vec U8),
    pt.val.length + 48 ≤ Usize.max → I.aeadEncrypt k1 k2 iv pt ad = ok ct →
    ∃ v, I.aeadDecrypt k1 k2 iv (alloc.vec.Vec.deref ct) ad = ok (core.result.Result.Ok v) ∧ v.val = pt.val

/-- **Assumed law**: `AeadRoundTripShape` at the real constants. -/
def AeadRoundTrip : Prop := AeadRoundTripShape Interp.real

/-- At the real constants, `AeadRoundTrip` is the statement about the real functions. -/
theorem aeadRoundTrip_is : AeadRoundTrip ↔
    ∀ (k1 k2 : Array U8 32#usize) (iv : Array U8 16#usize) (pt ad : Slice U8) (ct : alloc.vec.Vec U8),
      pt.val.length + 48 ≤ Usize.max → tacenta_boundary.aead.encrypt k1 k2 iv pt ad = ok ct →
      ∃ v, tacenta_boundary.aead.decrypt k1 k2 iv (alloc.vec.Vec.deref ct) ad =
        ok (core.result.Result.Ok v) ∧ v.val = pt.val := Iff.rfl

/-- An agreement of any private key with a public key `public_key` returned is not refused, over an
interpretation `I`. -/
def DhAgreeContributoryShape (I : Interp) : Prop :=
  ∀ (a b : I.PrivateKey) (pb : I.PublicKeyBytes), I.dhPrivPublicKey b = ok pb →
    ∃ x, I.dhPrivAgree a pb = ok (some x)

/-- **Assumed law**: `DhAgreeContributoryShape` at the real constants. -/
def DhAgreeContributory : Prop := DhAgreeContributoryShape Interp.real

/-- At the real constants, `DhAgreeContributory` is the statement about the real functions. -/
theorem dhAgreeContributory_is : DhAgreeContributory ↔
    ∀ (a b : tacenta_boundary.dh.PrivateKey) (pb : tacenta_boundary.dh.PublicKeyBytes),
      tacenta_boundary.dh.PrivateKey.public_key b = ok pb →
      ∃ x, tacenta_boundary.dh.PrivateKey.agree a pb = ok (some x) := Iff.rfl


/-! ## From the two runs to the pair form -/

section Bridges

variable {R : Type} {rc : rand_core_1.RngCore R} {crc : rand_core_1.CryptoRng R}
  {our : lifecycle.Identity} {bundle : lifecycle.PublishedBundle}

/-- **The two Triple initialisers on one secret give the pair form**: if `init_sender` on a slice returned the
initiator's Triple with root `rk` and sending chain `cks` and `init_receiver` on the same slice returned `t`,
then for the first half `ec` of the split secret, `kdf_rk ec dh = (rk, cks)` and `t` is the responder's Triple
with classical root `ec` and the same sparse root and chain keys, the responder sending on the initiator's
receiving chain and receiving on its sending chain.  Both calls run the same `split_secret` and the same
`kdf_init` on the same slice.  Hypothesis-free. -/
theorem first_init_pair (sk : Slice U8) (a4 a5 dh b : Array U8 32#usize)
    (rk cks prk c1 c2 : Array U8 32#usize) (t : tacenta_triple.State)
    (hs : tacenta_triple.State.init_sender sk a4 a5 dh tacenta_ratchet.LabelSet.Tacenta =
      ok (initiatorTriple a4 a5 rk cks prk c1 c2))
    (hr : tacenta_triple.State.init_receiver sk b tacenta_ratchet.LabelSet.Tacenta = ok t) :
    ∃ ec, tacenta_ratchet.kdf_rk ec dh tacenta_ratchet.LabelSet.Tacenta = ok (rk, cks) ∧
      t = responderTriple b ec prk c1 c2 := by
  unfold tacenta_triple.State.init_sender tacenta_ratchet.init_sender tacenta_spqr.State.init_alice
    tacenta_spqr.State.init at hs
  unfold tacenta_triple.State.init_receiver tacenta_ratchet.init_receiver tacenta_spqr.State.init_bob
    tacenta_spqr.State.init at hr
  obtain ⟨ec, pq, hsplit, h⟩ := bind2_eq_ok_inv hs
  obtain ⟨cl, hcl, h⟩ := bind_eq_ok_inv h
  obtain ⟨rk', cks', hkdf, hcl⟩ := bind2_eq_ok_inv hcl
  obtain ⟨s1, hs1, h⟩ := bind_eq_ok_inv h
  obtain ⟨pqs, hpq, h⟩ := bind_eq_ok_inv h
  obtain ⟨prk', k1, k2, hinit, hpq⟩ := bind3_eq_ok_inv hpq
  obtain ⟨-, -, h⟩ := bind_eq_ok_inv h
  obtain ⟨-, -, h⟩ := bind_eq_ok_inv h
  obtain ⟨ec2, pq2, hsplit2, h2⟩ := bind2_eq_ok_inv hr
  rw [hsplit] at hsplit2
  simp only [ok.injEq, Prod.mk.injEq] at hsplit2
  obtain ⟨rfl, rfl⟩ := hsplit2
  obtain ⟨cl2, hcl2, h2⟩ := bind_eq_ok_inv h2
  obtain ⟨s2, hs2, h2⟩ := bind_eq_ok_inv h2
  rw [hs1] at hs2
  simp only [ok.injEq] at hs2
  subst hs2
  obtain ⟨pqs2, hpq2, h2⟩ := bind_eq_ok_inv h2
  obtain ⟨prk2, l1, l2, hinit2, hpq2⟩ := bind3_eq_ok_inv hpq2
  rw [hinit] at hinit2
  simp only [ok.injEq, Prod.mk.injEq] at hinit2
  obtain ⟨rfl, rfl, rfl⟩ := hinit2
  obtain ⟨-, -, h2⟩ := bind_eq_ok_inv h2
  obtain ⟨-, -, h2⟩ := bind_eq_ok_inv h2
  simp only [ok.injEq] at h h2
  simp at hcl hcl2
  simp [lift] at hpq hpq2
  subst hcl hcl2 hpq hpq2 h2
  simp only [initiatorTriple, tacenta_triple.State.mk.injEq, tacenta_ratchet.State.mk.injEq,
    tacenta_spqr.State.mk.injEq] at h
  obtain ⟨⟨-, -, hrk, hcks, -⟩, hprk, -, hch, -⟩ := h
  have hv := congrArg Subtype.val hch
  simp [initChains, Tacenta.UnitHeadroomSatisfiable.vecOf, alloc.slice.Slice.into_vec, Array.make,
    Array.to_slice] at hv
  obtain ⟨rfl, rfl⟩ := hv
  simp only [Option.some.injEq] at hcks
  subst hrk hcks hprk
  refine ⟨ec, hkdf, ?_⟩
  simp [responderTriple, responderChains, Tacenta.UnitHeadroomSatisfiable.vecOf, alloc.slice.Slice.into_vec,
    Array.make, Array.to_slice]

/-- The model Triple of an establishment output is the sender pair form of its keys.  Hypothesis-free. -/
theorem established_triple_first (dh : DhView) (p : InitiatorOutputParts rc crc our bundle) :
    (establishedModelOf dh p.session).triple =
      firstSenderTriple (arrayOf p.ratchetBytes) (arrayOf p.peerRatchetBytes) (arrayOf p.rootKey)
        (arrayOf p.sendChain) (arrayOf p.sparseRoot) (arrayOf p.sparseSend) (arrayOf p.sparseReceive) := by
  simp [establishedModelOf, InitiatorOutputParts.session, initiatorTriple, initChains, firstSenderTriple,
    Tacenta.SessionUnitTripleT3.ratchetAbs, Tacenta.SessionUnitTripleT3.spqrAbs,
    Tacenta.SessionUnitSpqrT3.chainsEntryOf, Tacenta.SessionUnitSpqrT3.chainsOf,
    Tacenta.SessionUnitSpqrT3.chainOf, Tacenta.UnitHeadroomSatisfiable.vecOf, Tacenta.SessionUnitT3.keyOf,
    Tacenta.SessionUnitSpqrT3.keyOf, arrayOf, Tacenta.SessionUnitT3.u8, Tacenta.SessionUnitSpqrT3.u8,
    Tacenta.SessionUnitBraidT3.u8, Tacenta.SessionUnitT3.labelsOf, Tacenta.SessionUnitSpqrT3.directionOf]

/-- The model Triple of the responder's intermediate session is the receiver pair form, when the code's Triple
is `responderTriple` of the given keys. -/
theorem responder_triple_first (dh : DhView) {ourB : lifecycle.Identity} {storeB : lifecycle.PrekeyStore}
    {msg : Slice U8} (p : ResponderPreparedParts ourB storeB msg) (ec prk c1 c2 : Array U8 32#usize)
    (h : p.triple = responderTriple p.ratchetBytes ec prk c1 c2) :
    (responderModelOf dh p).triple =
      firstReceiverTriple (arrayOf p.ratchetBytes) (arrayOf ec) (arrayOf prk) (arrayOf c1) (arrayOf c2) := by
  simp [responderModelOf, h, responderTriple, responderChains, firstReceiverTriple,
    Tacenta.SessionUnitTripleT3.ratchetAbs, Tacenta.SessionUnitTripleT3.spqrAbs,
    Tacenta.SessionUnitSpqrT3.chainsEntryOf, Tacenta.SessionUnitSpqrT3.chainsOf,
    Tacenta.SessionUnitSpqrT3.chainOf, Tacenta.UnitHeadroomSatisfiable.vecOf, Tacenta.SessionUnitT3.keyOf,
    Tacenta.SessionUnitSpqrT3.keyOf, arrayOf, Tacenta.SessionUnitT3.u8, Tacenta.SessionUnitSpqrT3.u8,
    Tacenta.SessionUnitBraidT3.u8, Tacenta.SessionUnitT3.labelsOf, Tacenta.SessionUnitSpqrT3.directionOf]

/-- **The code's root-key step is the model's**, under the KDF and zeroizing agreements the decrypt refinement
already takes (`kdf_rk_refines`). -/
theorem first_kdf_model (hkdf : Tacenta.SessionUnitT3.HkdfAgrees)
    (hz : Tacenta.SessionUnitT3.ZeroizingRoundTrips) {ec d rk cks : Array U8 32#usize}
    (h : tacenta_ratchet.kdf_rk ec d tacenta_ratchet.LabelSet.Tacenta = ok (rk, cks)) :
    Model.State.kdfRk (arrayOf ec) (arrayOf d) .tacenta = (arrayOf rk, arrayOf cks) := by
  obtain ⟨r, hr, hpost⟩ := Std.WP.spec_imp_exists
    (Tacenta.SessionUnitT3.kdf_rk_refines hkdf hz ec d tacenta_ratchet.LabelSet.Tacenta)
  rw [h] at hr
  cases hr
  have e : Tacenta.SessionUnitT3.u8 = Tacenta.SessionUnitBraidT3.u8 := rfl
  simpa [Tacenta.SessionUnitT3.keyOf, arrayOf, e, Tacenta.SessionUnitT3.labelsOf] using hpost.symm

/-- A 32-byte array wrapped and unwrapped is itself, under the zeroizing round trip. -/
theorem zeroized_eq (hz : Tacenta.SessionUnitBraidT1.ZeroizingArrayRoundTrip) {a b : Array U8 32#usize}
    {w : zeroize.Zeroizing (Array U8 32#usize)} (hn : zeroize.Zeroizing.new z32 a = ok w)
    (hd : zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref z32 w = ok b) : b = a := by
  obtain ⟨w', hw', hd'⟩ := hz 32#usize z32 a
  rw [hn] at hw'
  cases hw'
  rw [hd] at hd'
  cases hd'
  rfl

open Tacenta.UnitLifecycleResponderFirstFrame (decode_first_frame publish_parts signed_prekey_own) in
/-- **What the parts at the initiator's first frame read from the store**: the decoded KEM and one-time
identifiers are the bundle's, the ratchet key's public key is the bundle's signed prekey, and our public key
is the bundle's identity key.  Under the decode hypotheses of `decode_first_frame` and the zeroizing round
trip; the store's `publish` returned the bundle and the responder's identity is the store's. -/
theorem parts_of_first_frame (hz : Tacenta.SessionUnitBraidT1.ZeroizingArrayRoundTrip) (hpub : DhPublicValid)
    {dh : DhView} (codec : DhCodecOf dh)
    (hct : Tacenta.UnitLifecycleEstablishInitiatorShape.KemCiphertextLenOf)
    (hbound : Tacenta.UnitLifecycleRestoredSession.KemCiphertextLenBound)
    (q : InitiatorSecretParts rc crc our bundle) (pending : Model.Lifecycle.PendingInitial)
    (hpend : (establishedModelOf dh q.session).pendingInitial = some pending)
    (frame : Model.Lifecycle.Bytes) (msg : Slice U8)
    (hmsg : sliceOf msg = initialWire (establishedModelOf dh q.session) pending frame)
    (ourB : lifecycle.Identity) (storeB : lifecycle.PrekeyStore)
    (hpublish : lifecycle.PrekeyStore.publish storeB = ok bundle)
    (hidentity : lifecycle.Identity.public ourB = ok storeB.identity_public)
    (p : ResponderPreparedParts ourB storeB msg) :
    p.decoded.kem_prekey_id = bundle.kem_prekey_id ∧
      p.decoded.one_time_prekey_id = bundle.one_time_prekey_id ∧
      tacenta_boundary.dh.PrivateKey.public_key p.ratchetPrivate = ok bundle.bundle.signed_prekey ∧
      p.ourPublic = bundle.bundle.identity_key := by
  obtain ⟨d, hd, hdsid, hdoid, hdkid, -, -, -, -⟩ :=
    decode_first_frame hpub codec hct hbound q pending hpend frame msg hmsg
  have hpd : p.decoded = d := by
    have := p.hDecode
    rw [hd] at this
    simp only [ok.injEq, core.result.Result.Ok.injEq] at this
    exact this.symm
  obtain ⟨hpsid, hpik, ⟨spk, hspkB, hspkPub⟩, -, -⟩ := publish_parts storeB bundle hpublish
  obtain ⟨zs, hzs, hzsd⟩ := hz 32#usize z32 storeB.signed_prekey_secret
  have hsig := p.hSigned
  rw [hpd, hdsid, hpsid, signed_prekey_own storeB zs hzs] at hsig
  simp only [ok.injEq, core.result.Result.Ok.injEq] at hsig
  have hsb := p.hSignedBytes
  rw [← hsig, hzsd] at hsb
  simp only [ok.injEq] at hsb
  have hrp := p.hRatchetPrivate
  rw [← hsb, hspkB] at hrp
  simp only [ok.injEq] at hrp
  refine ⟨by rw [hpd, hdkid], by rw [hpd, hdoid], by rw [← hrp]; exact hspkPub, ?_⟩
  have hop := p.hOurPublic
  rw [hidentity] at hop
  simp only [ok.injEq] at hop
  rw [← hop, hpik]

/-- The view of the initiator's ratchet public key is its bytes, under the view's codec relation. -/
theorem view_ratchet_public {dh : DhView} (codec : DhCodecOf dh) (q : InitiatorSecretParts rc crc our bundle) :
    dh.publicKey q.ratchetPublic = arrayOf q.ratchetBytes := by
  obtain ⟨b, hb, hab⟩ := codec.asBytes q.ratchetPublic
  rw [q.hRatchetBytes] at hb
  cases hb
  exact hab.symm

/-- **The responder's first agreement is the initiator's ratchet agreement**, in the responder's oracle: for a
responder key whose public key is the bundle's signed prekey, the oracle's agreement of it with the initiator's
ratchet key is `some` of the initiator's `dh_out`.  Under the agreement law `DhAgreeSymmetric` and the
responder's oracle record; the initiator's own check returned `dh_out` (`q.hDhOut`), so no contributory law is
used. -/
theorem responder_first_agreement (hsym : DhAgreeSymmetric) {E : Type} {rcB : rand_core_1.RngCore E}
    {crcB : rand_core_1.CryptoRng E} {dh : DhView} (codec : DhCodecOf dh) {traceB : E → List Model.Lifecycle.Key}
    {oracleB : Model.Lifecycle.Oracle} (oracleOfB : DecryptOracleOf rcB crcB dh traceB oracleB)
    (q : InitiatorSecretParts rc crc our bundle) (k : tacenta_boundary.dh.PrivateKey)
    (hk : tacenta_boundary.dh.PrivateKey.public_key k = ok bundle.bundle.signed_prekey) :
    oracleB.dhAgree (dh.privateKey k) (arrayOf q.ratchetBytes) = some (arrayOf q.dhOut) := by
  obtain ⟨res, hres, hmap⟩ := oracleOfB.dhAgree k q.ratchetPublic
  have hs := (dhAgreeSymmetric_is.mp hsym) k q.ratchetPrivate _ _ hk q.hRatchetPublic
  rw [hs, q.hDhOut] at hres
  cases hres
  rw [← view_ratchet_public codec q, ← hmap]
  rfl

/-- **Every draw of the responder's source agrees contributorily with the initiator's ratchet key**, in the
responder's oracle, under the law `DhAgreeContributory`, the responder's oracle record and the view's codec
relation. -/
theorem responder_candidate_agreement (hcon : DhAgreeContributory) {E : Type} {rcB : rand_core_1.RngCore E}
    {crcB : rand_core_1.CryptoRng E} {dh : DhView} (codec : DhCodecOf dh) {traceB : E → List Model.Lifecycle.Key}
    {oracleB : Model.Lifecycle.Oracle} (oracleOfB : DecryptOracleOf rcB crcB dh traceB oracleB)
    (q : InitiatorSecretParts rc crc our bundle) (rngB : E) (dB : Model.Lifecycle.Key)
    (restB : List Model.Lifecycle.Key) (hdraw : traceB rngB = dB :: restB) :
    ∃ x, oracleB.dhAgree dB (arrayOf q.ratchetBytes) = some x := by
  obtain ⟨value, -, -, hval, -⟩ := oracleOfB.random32 rngB dB restB hdraw
  obtain ⟨k, -, hkv⟩ := codec.privateFromBytes value
  obtain ⟨res, hres, hmap⟩ := oracleOfB.dhAgree k q.ratchetPublic
  obtain ⟨x, hx⟩ := (dhAgreeContributory_is.mp hcon) k q.ratchetPrivate q.ratchetPublic q.hRatchetPublic
  rw [hx] at hres
  cases hres
  refine ⟨arrayOf x, ?_⟩
  rw [← hval, ← hkv, ← view_ratchet_public codec q, ← hmap]
  rfl

/-- **The responder's associated data is the initiator's**: both are `identity_ad` of (initiator identity key,
responder identity key).  Hypothesis-free beyond the two key equations. -/
theorem first_identityAd_eq (q : InitiatorSecretParts rc crc our bundle) {ourB : lifecycle.Identity}
    {storeB : lifecycle.PrekeyStore} {msg : Slice U8} (p : ResponderPreparedParts ourB storeB msg)
    (hpi : p.peerIdentity = q.ourPublic) (hop : p.ourPublic = bundle.bundle.identity_key) :
    p.identityAd = q.identityAd := by
  have h := p.hIdentityAd
  rw [hpi, hop, q.hIdentityAd] at h
  simp only [ok.injEq] at h
  exact h.symm

/-- A byte string of length `n` as an array of `n` bytes. -/
def arrayOfBytes {n : Usize} (l : Model.Lifecycle.Bytes) (h : l.length = n.val) : Array U8 n :=
  ⟨Tacenta.UnitSatisfiabilityBraidAgreements.bytesOf l, by
    simp [Tacenta.UnitSatisfiabilityBraidAgreements.bytesOf, h]⟩

/-- The bytes of `arrayOfBytes l` are `l`. -/
theorem arrayOf_arrayOfBytes {n : Usize} (l : Model.Lifecycle.Bytes) (h : l.length = n.val) :
    arrayOf (arrayOfBytes l h) = l :=
  Tacenta.UnitSatisfiabilityBraidAgreements.map_u8_bytesOf l

/-- **The responder's oracle opens the initiator's seal**: for keys of 32, 32 and 16 bytes, a plaintext of at
most `Usize.max - 48` bytes and associated data that fit a slice, the responder's oracle opens the initiator's
oracle's seal to the plaintext.  Under the law `AeadRoundTrip` and the two oracle records (the initiator's seal
clause, the responder's open clause); the two oracles need not be equal. -/
theorem aead_open_sealed (haead : AeadRoundTrip) {E : Type} {rcB : rand_core_1.RngCore E}
    {crcB : rand_core_1.CryptoRng E} {dh : DhView} {traceB : E → List Model.Lifecycle.Key}
    {oracleA oracleB : Model.Lifecycle.Oracle}
    (hsealA : Tacenta.UnitOracleShape.AeadSealClause Interp.real oracleA)
    (oracleOfB : DecryptOracleOf rcB crcB dh traceB oracleB)
    (k1 k2 iv : Model.Lifecycle.Bytes) (hk1 : k1.length = 32) (hk2 : k2.length = 32) (hiv : iv.length = 16)
    (pt : Slice U8) (hpt : pt.val.length + 48 ≤ Usize.max) (ad : Model.Lifecycle.Bytes)
    (had : ad.length ≤ Usize.max) :
    oracleB.aeadOpen k1 k2 iv (oracleA.aeadSeal k1 k2 iv (sliceOf pt) ad) ad = some (sliceOf pt) := by
  let K1 : Array U8 32#usize := arrayOfBytes k1 hk1
  let K2 : Array U8 32#usize := arrayOfBytes k2 hk2
  let IV : Array U8 16#usize := arrayOfBytes iv hiv
  let A := Tacenta.UnitSatisfiabilityBraidStates.sliceOfBytes ad had
  have hA : sliceOf A = ad := Tacenta.UnitSatisfiabilityBraidStates.sliceOf_sliceOfBytes ad had
  obtain ⟨ct, hct, hvec⟩ := hsealA K1 K2 IV pt A
  obtain ⟨v, hv, hvv⟩ := (aeadRoundTrip_is.mp haead) K1 K2 IV pt A ct hpt hct
  obtain ⟨res, hres, hopen⟩ := oracleOfB.aeadOpen K1 K2 IV (alloc.vec.Vec.deref ct) A
  rw [hv] at hres
  cases hres
  simp only [K1, K2, IV, arrayOf_arrayOfBytes, hA] at hvec hopen
  have hct' : sliceOf (alloc.vec.Vec.deref ct) = vecOf ct := rfl
  rw [hct', hvec] at hopen
  rw [← hopen]
  simp only [Tacenta.UnitLifecycleT3.resultOptionOf, Option.some.injEq]
  simp only [vecOf, sliceOf, hvv]

end Bridges


/-! ## The received chunk, at a view that attributes it -/

open Tacenta.UnitLifecycleT3 (modelChunkOf modelCodewordOf CodewordViewSendOf)

/-- A codeword view that reads the codeword `(idx, data)` as the model chunk `mc` and every other codeword as
`view` does; it sends as `view` does. -/
def attributedView (view : Model.Lifecycle.CodewordView) (idx : UInt16) (data : Model.Lifecycle.Bytes)
    (mc : Model.Braid.Chunk) : Model.Lifecycle.CodewordView :=
  { send := view.send
    receive := fun st i d => if i = idx ∧ d = data then mc else view.receive st i d }

/-- The attributed view sends as the view it was built from, so it keeps `CodewordViewSendOf`. -/
theorem attributedView_send {view : Model.Lifecycle.CodewordView} (h : CodewordViewSendOf view)
    (idx : UInt16) (data : Model.Lifecycle.Bytes) (mc : Model.Braid.Chunk) :
    CodewordViewSendOf (attributedView view idx data mc) :=
  ⟨h.send⟩

/-- The first frame reads only the view's send direction, so it is the same frame at the attributed view. -/
theorem firstFrame_attributedView (view : Model.Lifecycle.CodewordView) (idx : UInt16)
    (data : Model.Lifecycle.Bytes) (mc : Model.Braid.Chunk) :
    firstFrame (attributedView view idx data mc) = firstFrame view :=
  rfl

/-- **The run inputs of the inner receive at the first frame**, at the view that attributes the frame's
codeword to the initiator's header source: when the frame the parts carry is the first frame of a sender
model session whose ratchet key is 32 canonical bytes, sent with the chunk `modelChunkOf src c` of a real
codeword `c` of a 96-byte source `src` (as `CodewordViewSendOf` sends it), and the responder's source holds a
draw, then the chunk relation, `HonestChunk` and the draw hold.  The codeword half is derived (the decoded real
codeword is `c`, a codeword of `src`); the attribution half is the view's construction. -/
theorem first_receipt_run_inputs {E : Type} (view : Model.Lifecycle.CodewordView)
    (oracleA oracleB : Model.Lifecycle.Oracle) (traceB : E → List Model.Lifecycle.Key) (dh : DhView)
    {ourB : lifecycle.Identity} {storeB : lifecycle.PrekeyStore} {msg : Slice U8}
    (p : ResponderPreparedParts ourB storeB msg) (mA : Model.Lifecycle.Session) (pt : Model.Lifecycle.Bytes)
    (mk : Model.Lifecycle.Key) (src : Model.Lifecycle.Bytes)
    (hsrc : src.length = Model.Braid.headerSize + Model.Braid.macSize) (c : tacenta_erasure.Chunk)
    (hcw : Tacenta.SessionUnitBraidT3.CodewordOf src c)
    (hsend : view.send mA.braid (modelChunkOf src c) = modelCodewordOf c)
    (hlen : mA.triple.classical.dhsPub.length = 32)
    (hkey : Model.Messages.checkKey mA.triple.classical.dhsPub = some ())
    (hframe : sliceOf (ResponderPreparedParts.message p) = firstFrame view oracleA mA pt mk (modelChunkOf src c))
    (rngB : E) (dB : Model.Lifecycle.Key) (restB : List Model.Lifecycle.Key)
    (hdraw : traceB rngB = dB :: restB) :
    DecryptRatchetRunInputs
      (attributedView view (modelCodewordOf c).index (modelCodewordOf c).data (modelChunkOf src c))
      oracleB traceB p.session (responderModelOf dh p) p.message rngB := by
  have hdec : Model.CompositeHeader.decodeDetailed (sliceOf (ResponderPreparedParts.message p)) =
      .ok (firstComposite view mA (modelChunkOf src c),
        oracleA.aeadSeal (Model.State.messageKeys mk .tacenta).1 (Model.State.messageKeys mk .tacenta).2.1
          (Model.State.messageKeys mk .tacenta).2.2 pt (firstAd view mA (modelChunkOf src c))) := by
    rw [hframe, Model.CompositeHeader.decodeDetailed_ok_iff]
    exact decode_encodeMessage _ _ hlen hkey
      (fun w hw => by
        simp only [firstComposite, hsend, Option.some.injEq] at hw
        subst hw
        simp [modelCodewordOf, arrayOf])
  refine ⟨?_, ?_, ⟨dB, restB, hdraw⟩⟩
  · intro rc mc ct hd hrel
    rw [hdec] at hd
    simp only [Except.ok.injEq, Prod.mk.injEq] at hd
    obtain ⟨rfl, -⟩ := hd
    have hag := hrel.agChunk
    unfold Tacenta.UnitLifecycleT3.IncomingChunkRefines
    simp only [firstComposite, hsend] at hag ⊢
    rcases hrc : rc.ag_chunk with _ | rch
    · rw [hrc] at hag
      exact hag.elim
    · rw [hrc] at hag
      simp only
      obtain ⟨hi, hdat⟩ := hag
      have hidx : rch.index = c.index := by
        apply UScalar.eq_of_val_eq
        rw [hi]
        simp [modelCodewordOf]
      have hdata : rch.data = c.data := by
        apply Tacenta.UnitLifecycleEstablishedEncrypt.array_eq_of_bytes
        exact hdat
      refine ⟨src, ?_, ?_⟩
      · rw [hidx, hdata]
        exact hcw
      · simp [attributedView, hidx, modelChunkOf]
  · intro mc ct hd
    rw [hdec] at hd
    simp only [Except.ok.injEq, Prod.mk.injEq] at hd
    obtain ⟨rfl, -⟩ := hd
    rw [Tacenta.UnitLifecycleEstablishResponder.honestChunk_responder_iff]
    intro m hm _ _
    simp only [Model.Lifecycle.braidMessageOf, firstComposite, hsend, Option.map_some,
      Option.some.injEq, attributedView, and_self, if_true] at hm
    subst hm
    simpa [modelChunkOf] using hsrc


/-! ## The inner receive on the first frame -/

section Inner

variable {R : Type} {rc : rand_core_1.RngCore R} {crc : rand_core_1.CryptoRng R}
  {our : lifecycle.Identity} {bundle : lifecycle.PublishedBundle}

/-- The first frame's associated data fits a slice: four length bytes, the 66 bytes of `identity_ad` and the
102 bytes of the composite header. -/
theorem firstAd_length_le (hdh : Tacenta.UnitLifecycleT1.DhCodecTotal) (dh : DhView)
    (view : Model.Lifecycle.CodewordView) (q : InitiatorOutputParts rc crc our bundle)
    (src : Model.Lifecycle.Bytes) (c : tacenta_erasure.Chunk)
    (hsend : view.send (establishedModelOf dh q.session).braid (modelChunkOf src c) = modelCodewordOf c) :
    (firstAd view (establishedModelOf dh q.session) (modelChunkOf src c)).length ≤ Usize.max := by
  have h66 := Tacenta.UnitLifecycleEstablishedEncrypt.identityAd_length_parts hdh q
  have hA := established_triple_first dh q
  apply Tacenta.UnitSatisfiabilityBraidAgreements.usize_max_ge
  simp only [firstAd, Model.Messages.concatAd, Model.CompositeHeader.encode, firstComposite, hsend, hA,
    firstSenderTriple, Model.CompositeHeader.encodeChunk, List.length_append, List.length_cons,
    List.length_nil, Model.Messages.be32, Model.CompositeHeader.be64, Model.CompositeHeader.be16,
    modelCodewordOf, arrayOf, List.length_map]
  simp [establishedModelOf, InitiatorOutputParts.session, vecOf, h66]

/-- **Every outcome of the responder's inner receive on the initiator's first frame**, without the laws
`DhAgreeContributory` and `AeadRoundTrip`: for parts as in `responder_first_frame_inner_succeeds`, the inner
`decrypt_ratchet` returns, takes exactly the draw `dB`, and its result is exactly one of
* `Handshake(NonContributoryAgreement)`, exactly when the responder oracle's agreement of the draw with the
  initiator's ratchet key is refused;
* `Aead`, when that agreement returns and the responder oracle's open of the initiator oracle's seal of the
  plaintext (first message key, first frame's associated data) is refused;
* `Ok` of bytes that are what that open returned, and the session refines `firstReceiptSession`.
No other refusal of the inner receive occurs at this frame.  The empty trace (the model's `ceiling`) is excluded
by the per-run premise that the trace holds a draw, which the refinement itself takes. -/
theorem responder_first_frame_inner_outcomes [Tacenta.SessionUnitT1.DerivedKeysModel] {E : Type}
    (rcB : rand_core_1.RngCore E) (crcB : rand_core_1.CryptoRng E)
    (contracts : Tacenta.UnitLifecycleT1.EstablishResponderContracts rcB)
    (hpub : DhPublicValid) (hsym : DhAgreeSymmetric)
    (hoeq : Tacenta.UnitHeadroomInvariant.OptionEqU64Shape
      (@core.option.Option.Insts.CoreCmpPartialEqOption.eq))
    {dh : DhView} (codec : DhCodecOf dh) (view : Model.Lifecycle.CodewordView)
    (oracleA : Model.Lifecycle.Oracle)
    (traceB : E → List Model.Lifecycle.Key) (oracleB : Model.Lifecycle.Oracle)
    (oracleOfB : DecryptOracleOf rcB crcB dh traceB oracleB)
    (agreements : DecryptRatchetAgreements oracleB.braidKem)
    (q : InitiatorSecretParts rc crc our bundle) (plaintext : Slice U8)
    (src : Model.Lifecycle.Bytes) (hsrc : src.length = Model.Braid.headerSize + Model.Braid.macSize)
    (c : tacenta_erasure.Chunk) (hcw : Tacenta.SessionUnitBraidT3.CodewordOf src c)
    (hsend : view.send (establishedModelOf dh q.session).braid (modelChunkOf src c) = modelCodewordOf c)
    {ourB : lifecycle.Identity} {storeB : lifecycle.PrekeyStore} {msg : Slice U8}
    (p : ResponderPreparedParts ourB storeB msg)
    (hts : p.tripleSecret = q.sharedSlice) (hpi : p.peerIdentity = q.ourPublic)
    (hsp : tacenta_boundary.dh.PrivateKey.public_key p.ratchetPrivate = ok bundle.bundle.signed_prekey)
    (hop : p.ourPublic = bundle.bundle.identity_key)
    (hframe : sliceOf (ResponderPreparedParts.message p) =
      firstFrame view oracleA (establishedModelOf dh q.session) (sliceOf plaintext)
        (firstKey (arrayOf q.sendChain) (arrayOf q.sparseSend)) (modelChunkOf src c))
    (rngB : E) (htraceB : traceB rngB = oracleB.draws) (dB : Model.Lifecycle.Key)
    (restB : List Model.Lifecycle.Key) (hdrawB : traceB rngB = dB :: restB) :
    ∃ (ec : Array U8 32#usize)
      (inner : core.result.Result (alloc.vec.Vec U8) lifecycle.Error × lifecycle.Session × E),
      tacenta_ratchet.kdf_rk ec q.dhOutBytes tacenta_ratchet.LabelSet.Tacenta = ok (q.rootKey, q.sendChain) ∧
      lifecycle.Session.decrypt_ratchet rcB crcB p.session p.message rngB = ok inner ∧
      traceB inner.2.2 = restB ∧
      ((inner.1 = core.result.Result.Err (lifecycle.Error.Handshake SessionError.NonContributoryAgreement) ∧
          oracleB.dhAgree dB (arrayOf q.ratchetBytes) = none) ∨
        (inner.1 = core.result.Result.Err lifecycle.Error.Aead ∧
          ∃ dSend, oracleB.dhAgree dB (arrayOf q.ratchetBytes) = some dSend ∧
            firstOpen oracleA oracleB (firstKey (arrayOf q.sendChain) (arrayOf q.sparseSend))
              (sliceOf plaintext) (firstAd view (establishedModelOf dh q.session) (modelChunkOf src c)) = none) ∨
        (∃ ptB dSend x, inner.1 = core.result.Result.Ok ptB ∧
          oracleB.dhAgree dB (arrayOf q.ratchetBytes) = some dSend ∧
          firstOpen oracleA oracleB (firstKey (arrayOf q.sendChain) (arrayOf q.sparseSend))
              (sliceOf plaintext) (firstAd view (establishedModelOf dh q.session) (modelChunkOf src c)) = some x ∧
          vecOf ptB = x ∧
          SessionRefines dh oracleB.braidKem inner.2.1
            (firstReceiptSession (responderModelOf dh p) (sliceOf p.braidSecret) (modelChunkOf src c)
              (arrayOf ec) (arrayOf q.sparseRoot) (arrayOf q.sparseSend) (arrayOf q.sparseReceive)
              (arrayOf q.ratchetBytes) (arrayOf q.dhOut) dSend (oracleB.dhPublic dB) dB))) := by
  -- the pair form and the root-key relation
  obtain ⟨ec, hkdfr, htrip⟩ := first_init_pair q.sharedSlice q.ratchetBytes q.peerRatchetBytes q.dhOutBytes
    p.ratchetBytes q.rootKey q.sendChain q.sparseRoot q.sparseSend q.sparseReceive p.triple q.hTriple
    (by rw [← hts]; exact p.hTriple)
  have hA := established_triple_first dh q.toInitiatorOutputParts
  have hB := responder_triple_first dh p ec q.sparseRoot q.sparseSend q.sparseReceive htrip
  have hdo : q.dhOutBytes = q.dhOut :=
    zeroized_eq contracts.decrypt.braid.zeroizingArray q.hDhOutZ q.hDhOutBytes
  have hkdf := first_kdf_model agreements.hkdf agreements.zeroizing64 hkdfr
  rw [hdo] at hkdf
  have hagree := responder_first_agreement hsym codec oracleOfB q p.ratchetPrivate hsp
  have hdraws : oracleB.draws = dB :: restB := htraceB.symm.trans hdrawB
  obtain ⟨a, ha, hcan, -⟩ :=
    Tacenta.UnitLifecycleResponderFirstFrame.view_of_public hpub codec q.hRatchetPublic
  rw [q.hRatchetBytes] at ha
  cases ha
  have hkey : Model.Messages.checkKey (arrayOf q.ratchetBytes) = some () := by
    simp [Model.Messages.checkKey, Tacenta.UnitLifecycleResponderFirstFrame.canonicalKey_arrayOf _ hcan]
  have hlen : (arrayOf q.ratchetBytes).length = 32 := by simp [arrayOf]
  have hidad := first_identityAd_eq q p hpi hop
  let aview := attributedView view (modelCodewordOf c).index (modelCodewordOf c).data (modelChunkOf src c)
  have O := first_frame_model_outcomes view aview oracleA oracleB (establishedModelOf dh q.session)
    (responderModelOf dh p) (arrayOf q.ratchetBytes) (arrayOf q.peerRatchetBytes) (arrayOf p.ratchetBytes)
    (arrayOf q.rootKey) (arrayOf q.sendChain) (arrayOf q.sparseRoot) (arrayOf q.sparseSend)
    (arrayOf q.sparseReceive) (arrayOf ec) (sliceOf p.braidSecret) (sliceOf plaintext) (modelChunkOf src c)
    (arrayOf q.dhOut) hA hB hkdf rfl
    (by simp [responderModelOf, establishedModelOf, InitiatorOutputParts.session, hidad])
    hlen hkey (by rw [hsend]; simp [modelCodewordOf, arrayOf]) hagree
  have hrcv : aview.receive (responderModelOf dh p).braid
      (view.send (establishedModelOf dh q.session).braid (modelChunkOf src c)).index
      (view.send (establishedModelOf dh q.session).braid (modelChunkOf src c)).data = modelChunkOf src c := by
    simp [aview, attributedView, hsend]
  rw [hrcv] at O
  have inputs := first_receipt_run_inputs view oracleA oracleB traceB dh p (establishedModelOf dh q.session)
    (sliceOf plaintext) (firstKey (arrayOf q.sendChain) (arrayOf q.sparseSend)) src hsrc c hcw hsend
    (by rw [hA]; exact hlen) (by rw [hA]; exact hkey) hframe rngB dB restB hdrawB
  obtain ⟨inner, hinner, hstep⟩ := Tacenta.UnitLifecycleEstablishResponder.responder_prepared_decrypt_refines
    rcB crcB traceB dh aview oracleB oracleOfB codec contracts.decrypt agreements hpub hoeq
    contracts.divCeilValue p rngB htraceB inputs
  rw [hframe] at hstep
  refine ⟨ec, inner, hkdfr, hinner, ?_⟩
  obtain ⟨res, sB', rngB'⟩ := inner
  have hres := hstep.result
  have hdr := hstep.draws
  rcases O with ⟨hnil, -⟩ | ⟨c', rest', hdr', hnone, hM⟩ | ⟨c', rest', dSend, hdr', hsome, hopen, hM⟩ |
    ⟨c', rest', dSend, x, hdr', hsome, hopen, hM⟩
  · rw [hdraws] at hnil
    cases hnil
  · rw [hdraws] at hdr'
    obtain ⟨rfl, rfl⟩ := List.cons.inj hdr'
    rw [hM] at hres hdr
    refine ⟨hdr, Or.inl ⟨?_, hnone⟩⟩
    cases res with
    | Ok v => simp [ResultRefines] at hres
    | Err e =>
      simp only [ResultRefines] at hres
      have he : e = lifecycle.Error.Handshake SessionError.NonContributoryAgreement :=
        Tacenta.UnitLifecycleT3.refusalOf_injective (hres.trans rfl)
      rw [he]
  · rw [hdraws] at hdr'
    obtain ⟨rfl, rfl⟩ := List.cons.inj hdr'
    rw [hM] at hres hdr
    refine ⟨hdr, Or.inr (Or.inl ⟨?_, dSend, hsome, hopen⟩)⟩
    cases res with
    | Ok v => simp [ResultRefines] at hres
    | Err e =>
      simp only [ResultRefines] at hres
      have he : e = lifecycle.Error.Aead := Tacenta.UnitLifecycleT3.refusalOf_injective (hres.trans rfl)
      rw [he]
  · rw [hdraws] at hdr'
    obtain ⟨rfl, rfl⟩ := List.cons.inj hdr'
    have hsess := hstep.session
    rw [hM] at hres hdr hsess
    refine ⟨hdr, Or.inr (Or.inr ?_)⟩
    cases res with
    | Err e => simp [ResultRefines] at hres
    | Ok ptB => exact ⟨ptB, dSend, x, rfl, hsome, hopen, hres, hsess⟩

/-- **The responder's inner receive accepts the initiator's first frame and returns its plaintext**: for parts
`p` of the responder's prepare phase whose Triple secret is the initiator's shared slice, whose peer identity is
the initiator's identity key, whose ratchet key has the bundle's signed prekey as public key and whose own key
is the bundle's identity key, and whose frame is the initiator's first frame (the model's encoding of the first
composite header with the plaintext sealed under the first message key `firstKey` of the initiator's chains,
with the chunk `modelChunkOf src c` of a real codeword `c` of the 96-byte header source `src`): the inner
`decrypt_ratchet` returns `Ok` of bytes equal to the plaintext, takes exactly the draw `dB`, and the session it
returns refines `firstReceiptSession` (the model's step at the view that attributes the frame's codeword to
`src`), with `ec` the receiver's classical root (`kdf_rk ec dh_out` is the initiator's root and chain) and
`dSend` the oracle's agreement of the draw with the initiator's ratchet key.  Under the laws
`DhAgreeSymmetric`, `DhAgreeContributory`, `AeadRoundTrip`, `DhPublicValid`, `OptionEqU64Shape`, the
responder's contracts, oracle record and decrypt agreements, the initiator's seal clause, and the per-run
premises that the responder's trace is the oracle's and holds a draw. -/
theorem responder_first_frame_inner_succeeds [Tacenta.SessionUnitT1.DerivedKeysModel] {E : Type}
    (rcB : rand_core_1.RngCore E) (crcB : rand_core_1.CryptoRng E)
    (contracts : Tacenta.UnitLifecycleT1.EstablishResponderContracts rcB)
    (hpub : DhPublicValid) (hsym : DhAgreeSymmetric) (hcon : DhAgreeContributory) (haead : AeadRoundTrip)
    (hoeq : Tacenta.UnitHeadroomInvariant.OptionEqU64Shape
      (@core.option.Option.Insts.CoreCmpPartialEqOption.eq))
    {dh : DhView} (codec : DhCodecOf dh) (view : Model.Lifecycle.CodewordView)
    (oracleA : Model.Lifecycle.Oracle) (hsealA : Tacenta.UnitOracleShape.AeadSealClause Interp.real oracleA)
    (traceB : E → List Model.Lifecycle.Key) (oracleB : Model.Lifecycle.Oracle)
    (oracleOfB : DecryptOracleOf rcB crcB dh traceB oracleB)
    (agreements : DecryptRatchetAgreements oracleB.braidKem)
    (q : InitiatorSecretParts rc crc our bundle) (plaintext : Slice U8)
    (hroom : plaintext.val.length + 48 ≤ Usize.max)
    (src : Model.Lifecycle.Bytes) (hsrc : src.length = Model.Braid.headerSize + Model.Braid.macSize)
    (c : tacenta_erasure.Chunk) (hcw : Tacenta.SessionUnitBraidT3.CodewordOf src c)
    (hsend : view.send (establishedModelOf dh q.session).braid (modelChunkOf src c) = modelCodewordOf c)
    {ourB : lifecycle.Identity} {storeB : lifecycle.PrekeyStore} {msg : Slice U8}
    (p : ResponderPreparedParts ourB storeB msg)
    (hts : p.tripleSecret = q.sharedSlice) (hpi : p.peerIdentity = q.ourPublic)
    (hsp : tacenta_boundary.dh.PrivateKey.public_key p.ratchetPrivate = ok bundle.bundle.signed_prekey)
    (hop : p.ourPublic = bundle.bundle.identity_key)
    (hframe : sliceOf (ResponderPreparedParts.message p) =
      firstFrame view oracleA (establishedModelOf dh q.session) (sliceOf plaintext)
        (firstKey (arrayOf q.sendChain) (arrayOf q.sparseSend)) (modelChunkOf src c))
    (rngB : E) (htraceB : traceB rngB = oracleB.draws) (dB : Model.Lifecycle.Key)
    (restB : List Model.Lifecycle.Key) (hdrawB : traceB rngB = dB :: restB) :
    ∃ ec dSend ptB sB' rngB',
      tacenta_ratchet.kdf_rk ec q.dhOutBytes tacenta_ratchet.LabelSet.Tacenta = ok (q.rootKey, q.sendChain) ∧
      oracleB.dhAgree dB (arrayOf q.ratchetBytes) = some dSend ∧
      lifecycle.Session.decrypt_ratchet rcB crcB p.session p.message rngB =
        ok (core.result.Result.Ok ptB, sB', rngB') ∧
      ptB.val = plaintext.val ∧ traceB rngB' = restB ∧
      SessionRefines dh oracleB.braidKem sB'
        (firstReceiptSession (responderModelOf dh p) (sliceOf p.braidSecret) (modelChunkOf src c)
          (arrayOf ec) (arrayOf q.sparseRoot) (arrayOf q.sparseSend) (arrayOf q.sparseReceive)
          (arrayOf q.ratchetBytes) (arrayOf q.dhOut) dSend (oracleB.dhPublic dB) dB) := by
  obtain ⟨ec, inner, hkdfr, hinner, hdr, hcases⟩ := responder_first_frame_inner_outcomes rcB crcB contracts hpub
    hsym hoeq codec view oracleA traceB oracleB oracleOfB agreements q plaintext src hsrc c hcw hsend p hts hpi
    hsp hop hframe rngB htraceB dB restB hdrawB
  obtain ⟨dSend', hcand⟩ := responder_candidate_agreement hcon codec oracleOfB q rngB dB restB hdrawB
  have hadl := firstAd_length_le contracts.decrypt.dhCodec dh view q.toInitiatorOutputParts src c hsend
  have haead' := aead_open_sealed haead hsealA oracleOfB
    (Model.State.messageKeys (firstKey (arrayOf q.sendChain) (arrayOf q.sparseSend)) .tacenta).1
    (Model.State.messageKeys (firstKey (arrayOf q.sendChain) (arrayOf q.sparseSend)) .tacenta).2.1
    (Model.State.messageKeys (firstKey (arrayOf q.sendChain) (arrayOf q.sparseSend)) .tacenta).2.2
    (by simp [Model.State.messageKeys, Model.Kdf.hkdf_length])
    (by simp [Model.State.messageKeys, Model.Kdf.hkdf_length])
    (by simp [Model.State.messageKeys, Model.Kdf.hkdf_length]) plaintext hroom _ hadl
  have hopenA : firstOpen oracleA oracleB (firstKey (arrayOf q.sendChain) (arrayOf q.sparseSend))
      (sliceOf plaintext) (firstAd view (establishedModelOf dh q.session) (modelChunkOf src c)) =
      some (sliceOf plaintext) := haead'
  obtain ⟨res, sB', rngB'⟩ := inner
  rcases hcases with ⟨-, hnone⟩ | ⟨-, dSend, -, hopen⟩ | ⟨ptB, dSend, x, hres, hsome, hopen, hvec, hsess⟩
  · rw [hcand] at hnone
    cases hnone
  · rw [hopenA] at hopen
    cases hopen
  · rw [hopenA] at hopen
    cases hopen
    simp only at hres
    subst hres
    exact ⟨ec, dSend, ptB, sB', rngB', hkdfr, hsome, hinner, Tacenta.UnitLifecycleEstablishResponder.map_u8_inj hvec,
      hdr, hsess⟩

end Inner


/-! ## The whole call on the first frame -/

section WholeCall

variable {R : Type} {rc : rand_core_1.RngCore R} {crc : rand_core_1.CryptoRng R}
  {our : lifecycle.Identity} {bundle : lifecycle.PublishedBundle}

/-- **When the inner receive succeeds, the call returns its plaintext and session with the committed store**:
for parts `p` of an input at which the inner `decrypt_ratchet` returns `Ok`, every return of
`establish_responder` on that input is that plaintext and session, the store after `ResponderCommit` of the
message's identifiers, and the source the inner receive left.  Hypothesis-free. -/
theorem establish_responder_commit_of_inner {E : Type} (rcB : rand_core_1.RngCore E)
    (crcB : rand_core_1.CryptoRng E) {ourB : lifecycle.Identity} {storeB : lifecycle.PrekeyStore}
    {msg : Slice U8} (p : ResponderPreparedParts ourB storeB msg) (rngB : E) (ptB : alloc.vec.Vec U8)
    (sB' : lifecycle.Session) (rngB' : E)
    (hinner : lifecycle.Session.decrypt_ratchet rcB crcB p.session p.message rngB =
      ok (core.result.Result.Ok ptB, sB', rngB'))
    (out : core.result.Result (lifecycle.Session × alloc.vec.Vec U8) lifecycle.Error ×
      lifecycle.PrekeyStore × E)
    (h : lifecycle.establish_responder rcB crcB ourB storeB msg rngB = ok out) :
    ∃ storeB', ResponderCommit storeB p.decoded.kem_prekey_id p.decoded.one_time_prekey_id p.lastResort
        p.replay storeB' ∧ out = (core.result.Result.Ok (sB', ptB), storeB', rngB') := by
  rw [Tacenta.UnitLifecycleEstablishResponder.establish_responder_at_parts rcB crcB p rngB, hinner] at h
  simp only [Aeneas.Std.bind_tc_ok] at h
  replace h := bind_eq_ok_inv h
  obtain ⟨store1, hstore1, h⟩ := h
  replace h := bind_eq_ok_inv h
  obtain ⟨store2, hstore2, h⟩ := h
  have c1 := Tacenta.UnitLifecycleEstablishResponder.commit_kem_step _ _ _ _ hstore1
  have c2 := Tacenta.UnitLifecycleEstablishResponder.commit_one_time_step _ _ _ hstore2
  rcases hrep : p.replay with _ | fp <;> rw [hrep] at h
  · simp only [ok.injEq] at h
    exact ⟨store2, ⟨store1, store2, c1, c2, rfl⟩, h.symm⟩
  · simp only at h
    replace h := bind_eq_ok_inv h
    obtain ⟨count, hcount, h⟩ := h
    replace h := bind_eq_ok_inv h
    obtain ⟨u, hu, h⟩ := h
    replace h := bind_eq_ok_inv h
    obtain ⟨seen, hseen, h⟩ := h
    simp only [ok.injEq] at h
    have hlt : count < lifecycle.MAX_LAST_RESORT_SEEN := by
      unfold massert at hu; split at hu <;> simp_all
    exact ⟨_, ⟨store1, store2, c1, c2, count, seen, hcount, hlt, hseen, rfl⟩, h.symm⟩

/-- When the inner receive refuses, the call returns that refusal with the store as given and the source the
inner receive left.  Hypothesis-free. -/
theorem establish_responder_refused_of_inner {E : Type} (rcB : rand_core_1.RngCore E)
    (crcB : rand_core_1.CryptoRng E) {ourB : lifecycle.Identity} {storeB : lifecycle.PrekeyStore}
    {msg : Slice U8} (p : ResponderPreparedParts ourB storeB msg) (rngB : E) (e : lifecycle.Error)
    (sB' : lifecycle.Session) (rngB' : E)
    (hinner : lifecycle.Session.decrypt_ratchet rcB crcB p.session p.message rngB =
      ok (core.result.Result.Err e, sB', rngB')) :
    lifecycle.establish_responder rcB crcB ourB storeB msg rngB =
      ok (core.result.Result.Err e, storeB, rngB') := by
  rw [Tacenta.UnitLifecycleEstablishResponder.establish_responder_at_parts rcB crcB p rngB, hinner]
  rfl

open Tacenta.UnitLifecycleResponderFirstFrame (responder_first_frame_prepares) in
/-- **Every outcome of `establish_responder` on the initiator's first frame**, without the laws
`DhAgreeContributory` and `AeadRoundTrip`: under the other hypotheses of `responder_first_frame_succeeds`, the
call either refuses with one of the three refusals the store decides (store and source as given), or reaches the
inner receive with parts carrying the initiator's secrets and then returns exactly one of
* `Handshake(NonContributoryAgreement)`, store as given, exactly one draw taken, exactly when the responder
  oracle's agreement of the draw with the initiator's ratchet key is refused;
* `Aead`, store as given, exactly one draw taken, when that agreement returns and the responder oracle's open of
  the initiator oracle's seal (`firstOpen`) is refused;
* `Ok` of bytes that are what that open returned, exactly one draw taken, the store after `ResponderCommit` of
  the bundle's identifiers, and a session that refines `firstReceiptSession`.
So, beyond the store, the only refusals left at this frame are the two named, and each is the failure of one
premise of `responder_first_frame_succeeds` in the responder's oracle: `DhAgreeContributory` for the first,
`AeadRoundTrip` (with the agreement of the two oracles on the keys) for the second.  The model's `ceiling` (an
empty trace) is excluded by the per-run premise that the trace holds a draw. -/
theorem responder_first_frame_outcomes [Tacenta.SessionUnitT1.DerivedKeysModel] {E : Type}
    (rcB : rand_core_1.RngCore E) (crcB : rand_core_1.CryptoRng E)
    (contracts : Tacenta.UnitLifecycleT1.EstablishResponderContracts rcB)
    (hpub : DhPublicValid) (hsym : DhAgreeSymmetric)
    (hrt : Tacenta.UnitLifecycleSessionCodec.DhPublicBytesRoundTrip)
    (hct : Tacenta.UnitLifecycleEstablishInitiatorShape.KemCiphertextLenOf)
    (hbound : Tacenta.UnitLifecycleRestoredSession.KemCiphertextLenBound)
    (hoeq : Tacenta.UnitHeadroomInvariant.OptionEqU64Shape
      (@core.option.Option.Insts.CoreCmpPartialEqOption.eq))
    {dh : DhView} (codec : DhCodecOf dh) (view : Model.Lifecycle.CodewordView)
    (oracleA : Model.Lifecycle.Oracle)
    (traceB : E → List Model.Lifecycle.Key) (oracleB : Model.Lifecycle.Oracle)
    (oracleOfB : DecryptOracleOf rcB crcB dh traceB oracleB)
    (agreements : DecryptRatchetAgreements oracleB.braidKem)
    (q : InitiatorSecretParts rc crc our bundle) (pending : Model.Lifecycle.PendingInitial)
    (hpend : (establishedModelOf dh q.session).pendingInitial = some pending)
    (plaintext : Slice U8)
    (src : Model.Lifecycle.Bytes) (hsrc : src.length = Model.Braid.headerSize + Model.Braid.macSize)
    (c : tacenta_erasure.Chunk) (hcw : Tacenta.SessionUnitBraidT3.CodewordOf src c)
    (hsend : view.send (establishedModelOf dh q.session).braid (modelChunkOf src c) = modelCodewordOf c)
    (msg : Slice U8)
    (hmsg : sliceOf msg = initialWire (establishedModelOf dh q.session) pending
      (firstFrame view oracleA (establishedModelOf dh q.session) (sliceOf plaintext)
        (firstKey (arrayOf q.sendChain) (arrayOf q.sparseSend)) (modelChunkOf src c)))
    (ourB : lifecycle.Identity) (storeB : lifecycle.PrekeyStore)
    (hpublish : lifecycle.PrekeyStore.publish storeB = ok bundle)
    (hidentity : lifecycle.Identity.public ourB = ok storeB.identity_public)
    (hdistinct : PrekeyIdsDistinct storeB)
    (hkem : FirstKemAgrees storeB bundle.kem_prekey_id q.kemCiphertext q.kemSecret)
    (hhead : Tacenta.UnitLifecycleT1.EstablishResponderHeadroom storeB)
    (rngB : E) (htraceB : traceB rngB = oracleB.draws) (dB : Model.Lifecycle.Key)
    (restB : List Model.Lifecycle.Key) (hdrawB : traceB rngB = dB :: restB) :
    (bundle.kem_prekey_id = storeB.kem_id ∧ ∃ e, StoreRefusal storeB q.sharedBytes e ∧
        lifecycle.establish_responder rcB crcB ourB storeB msg rngB =
          ok (core.result.Result.Err e, storeB, rngB)) ∨
      ∃ (p : ResponderPreparedParts ourB storeB msg) (ec : Array U8 32#usize) (rngB' : E),
        p.shared = q.shared ∧ p.secret = q.sharedBytes ∧ p.tripleSecret = q.sharedSlice ∧
        p.peerIdentity = q.ourPublic ∧ p.peerEphemeral = q.ephemeralPublic ∧ p.kemSecret = q.kemSecret ∧
        (p.lastResort = true ↔ bundle.kem_prekey_id = storeB.kem_id) ∧
        tacenta_ratchet.kdf_rk ec q.dhOutBytes tacenta_ratchet.LabelSet.Tacenta = ok (q.rootKey, q.sendChain) ∧
        traceB rngB' = restB ∧
        ((lifecycle.establish_responder rcB crcB ourB storeB msg rngB =
            ok (core.result.Result.Err (lifecycle.Error.Handshake SessionError.NonContributoryAgreement), storeB,
              rngB') ∧
            oracleB.dhAgree dB (arrayOf q.ratchetBytes) = none) ∨
          (lifecycle.establish_responder rcB crcB ourB storeB msg rngB =
              ok (core.result.Result.Err lifecycle.Error.Aead, storeB, rngB') ∧
            ∃ dSend, oracleB.dhAgree dB (arrayOf q.ratchetBytes) = some dSend ∧
              firstOpen oracleA oracleB (firstKey (arrayOf q.sendChain) (arrayOf q.sparseSend))
                (sliceOf plaintext) (firstAd view (establishedModelOf dh q.session) (modelChunkOf src c)) = none) ∨
          (∃ ptB sB' storeB' dSend x,
            lifecycle.establish_responder rcB crcB ourB storeB msg rngB =
              ok (core.result.Result.Ok (sB', ptB), storeB', rngB') ∧
            oracleB.dhAgree dB (arrayOf q.ratchetBytes) = some dSend ∧
            firstOpen oracleA oracleB (firstKey (arrayOf q.sendChain) (arrayOf q.sparseSend))
              (sliceOf plaintext) (firstAd view (establishedModelOf dh q.session) (modelChunkOf src c)) = some x ∧
            vecOf ptB = x ∧
            ResponderCommit storeB bundle.kem_prekey_id bundle.one_time_prekey_id p.lastResort p.replay storeB' ∧
            SessionRefines dh oracleB.braidKem sB'
              (firstReceiptSession (responderModelOf dh p) (sliceOf p.braidSecret) (modelChunkOf src c)
                (arrayOf ec) (arrayOf q.sparseRoot) (arrayOf q.sparseSend) (arrayOf q.sparseReceive)
                (arrayOf q.ratchetBytes) (arrayOf q.dhOut) dSend (oracleB.dhPublic dB) dB))) := by
  rcases responder_first_frame_prepares rcB crcB contracts hpub hsym hrt hct hbound codec q pending hpend _ msg
      hmsg ourB storeB hpublish hidentity hdistinct hkem rngB with hl |
    ⟨p, h1, h2, h3, -, h5, h6, h7, h8, h9⟩
  · exact Or.inl hl
  obtain ⟨hkid, hoid, hsp, hop⟩ := parts_of_first_frame contracts.decrypt.braid.zeroizingArray hpub codec hct
    hbound q pending hpend _ msg hmsg ourB storeB hpublish hidentity p
  obtain ⟨ec, ⟨res, sB', rngB'⟩, hkdf, hinner, hdr, hcases⟩ := responder_first_frame_inner_outcomes rcB crcB
    contracts hpub hsym hoeq codec view oracleA traceB oracleB oracleOfB agreements q plaintext src hsrc c hcw
    hsend p h3 h5 hsp hop h8 rngB htraceB dB restB hdrawB
  refine Or.inr ⟨p, ec, rngB', h1, h2, h3, h5, h6, h7, h9, hkdf, hdr, ?_⟩
  rcases hcases with ⟨hres, hnone⟩ | ⟨hres, dSend, hsome, hopen⟩ |
    ⟨ptB, dSend, x, hres, hsome, hopen, hvec, hsess⟩
  · simp only at hres
    subst hres
    exact Or.inl ⟨establish_responder_refused_of_inner rcB crcB p rngB _ sB' rngB' hinner, hnone⟩
  · simp only at hres
    subst hres
    exact Or.inr (Or.inl ⟨establish_responder_refused_of_inner rcB crcB p rngB _ sB' rngB' hinner, dSend,
      hsome, hopen⟩)
  · simp only at hres
    subst hres
    obtain ⟨out, hout⟩ := Tacenta.UnitLifecycleEstablishResponder.establish_responder_returns rcB crcB contracts
      ourB storeB msg rngB hhead
    obtain ⟨storeB', hcommit, rfl⟩ := establish_responder_commit_of_inner rcB crcB p rngB ptB sB' rngB' hinner
      out hout
    rw [hkid, hoid] at hcommit
    exact Or.inr (Or.inr ⟨ptB, sB', storeB', dSend, x, hout, hsome, hopen, hvec, hcommit, hsess⟩)

open Tacenta.UnitLifecycleResponderFirstFrame (responder_first_frame_prepares) in
/-- **`establish_responder` on the initiator's first frame succeeds with the initiator's plaintext, or the
store refuses**: for every record `q` of an initiator's run, every plaintext and real codeword `c` of a 96-byte
source `src` sent as `CodewordViewSendOf` sends it, every message that is the initial message wrapping the first
frame (the plaintext sealed under `firstKey` of the initiator's chains, with chunk `modelChunkOf src c`), every
responder identity and prekey store as in `responder_first_frame_prepares` with the store bound of
`establish_responder_no_panic`, and every source of randomness whose trace is the responder oracle's and holds a
draw `dB`: either the store refuses as in `responder_first_frame_prepares` (store and source as given), or the
whole call returns `Ok` of the session and bytes equal to the plaintext, takes exactly the draw `dB`, commits
the store (`ResponderCommit` of the bundle's identifiers; on the one-time path no fingerprint, on the
last-resort path the fingerprint of the initiator's shared secret), and its session refines
`firstReceiptSession`. -/
theorem responder_first_frame_succeeds [Tacenta.SessionUnitT1.DerivedKeysModel] {E : Type}
    (rcB : rand_core_1.RngCore E) (crcB : rand_core_1.CryptoRng E)
    (contracts : Tacenta.UnitLifecycleT1.EstablishResponderContracts rcB)
    (hpub : DhPublicValid) (hsym : DhAgreeSymmetric) (hcon : DhAgreeContributory) (haead : AeadRoundTrip)
    (hrt : Tacenta.UnitLifecycleSessionCodec.DhPublicBytesRoundTrip)
    (hct : Tacenta.UnitLifecycleEstablishInitiatorShape.KemCiphertextLenOf)
    (hbound : Tacenta.UnitLifecycleRestoredSession.KemCiphertextLenBound)
    (hoeq : Tacenta.UnitHeadroomInvariant.OptionEqU64Shape
      (@core.option.Option.Insts.CoreCmpPartialEqOption.eq))
    {dh : DhView} (codec : DhCodecOf dh) (view : Model.Lifecycle.CodewordView)
    (oracleA : Model.Lifecycle.Oracle) (hsealA : Tacenta.UnitOracleShape.AeadSealClause Interp.real oracleA)
    (traceB : E → List Model.Lifecycle.Key) (oracleB : Model.Lifecycle.Oracle)
    (oracleOfB : DecryptOracleOf rcB crcB dh traceB oracleB)
    (agreements : DecryptRatchetAgreements oracleB.braidKem)
    (q : InitiatorSecretParts rc crc our bundle) (pending : Model.Lifecycle.PendingInitial)
    (hpend : (establishedModelOf dh q.session).pendingInitial = some pending)
    (plaintext : Slice U8) (hroom : plaintext.val.length + 48 ≤ Usize.max)
    (src : Model.Lifecycle.Bytes) (hsrc : src.length = Model.Braid.headerSize + Model.Braid.macSize)
    (c : tacenta_erasure.Chunk) (hcw : Tacenta.SessionUnitBraidT3.CodewordOf src c)
    (hsend : view.send (establishedModelOf dh q.session).braid (modelChunkOf src c) = modelCodewordOf c)
    (msg : Slice U8)
    (hmsg : sliceOf msg = initialWire (establishedModelOf dh q.session) pending
      (firstFrame view oracleA (establishedModelOf dh q.session) (sliceOf plaintext)
        (firstKey (arrayOf q.sendChain) (arrayOf q.sparseSend)) (modelChunkOf src c)))
    (ourB : lifecycle.Identity) (storeB : lifecycle.PrekeyStore)
    (hpublish : lifecycle.PrekeyStore.publish storeB = ok bundle)
    (hidentity : lifecycle.Identity.public ourB = ok storeB.identity_public)
    (hdistinct : PrekeyIdsDistinct storeB)
    (hkem : FirstKemAgrees storeB bundle.kem_prekey_id q.kemCiphertext q.kemSecret)
    (hhead : Tacenta.UnitLifecycleT1.EstablishResponderHeadroom storeB)
    (rngB : E) (htraceB : traceB rngB = oracleB.draws) (dB : Model.Lifecycle.Key)
    (restB : List Model.Lifecycle.Key) (hdrawB : traceB rngB = dB :: restB) :
    (bundle.kem_prekey_id = storeB.kem_id ∧ ∃ e, StoreRefusal storeB q.sharedBytes e ∧
        lifecycle.establish_responder rcB crcB ourB storeB msg rngB =
          ok (core.result.Result.Err e, storeB, rngB)) ∨
      ∃ (p : ResponderPreparedParts ourB storeB msg) (ec : Array U8 32#usize) (dSend : Model.Lifecycle.Key)
        (ptB : alloc.vec.Vec U8) (sB' : lifecycle.Session) (storeB' : lifecycle.PrekeyStore) (rngB' : E),
        p.shared = q.shared ∧ p.secret = q.sharedBytes ∧ p.tripleSecret = q.sharedSlice ∧
        p.peerIdentity = q.ourPublic ∧ p.peerEphemeral = q.ephemeralPublic ∧ p.kemSecret = q.kemSecret ∧
        (p.lastResort = true ↔ bundle.kem_prekey_id = storeB.kem_id) ∧
        tacenta_ratchet.kdf_rk ec q.dhOutBytes tacenta_ratchet.LabelSet.Tacenta = ok (q.rootKey, q.sendChain) ∧
        oracleB.dhAgree dB (arrayOf q.ratchetBytes) = some dSend ∧
        lifecycle.establish_responder rcB crcB ourB storeB msg rngB =
          ok (core.result.Result.Ok (sB', ptB), storeB', rngB') ∧
        ptB.val = plaintext.val ∧ traceB rngB' = restB ∧
        ResponderCommit storeB bundle.kem_prekey_id bundle.one_time_prekey_id p.lastResort p.replay storeB' ∧
        (p.lastResort = false → p.replay = none) ∧
        (p.lastResort = true → ∃ fp, p.replay = some fp ∧ lifecycle.last_resort_fingerprint q.sharedBytes = ok fp) ∧
        SessionRefines dh oracleB.braidKem sB'
          (firstReceiptSession (responderModelOf dh p) (sliceOf p.braidSecret) (modelChunkOf src c)
            (arrayOf ec) (arrayOf q.sparseRoot) (arrayOf q.sparseSend) (arrayOf q.sparseReceive)
            (arrayOf q.ratchetBytes) (arrayOf q.dhOut) dSend (oracleB.dhPublic dB) dB) := by
  rcases responder_first_frame_prepares rcB crcB contracts hpub hsym hrt hct hbound codec q pending hpend _ msg
      hmsg ourB storeB hpublish hidentity hdistinct hkem rngB with hl |
    ⟨p, h1, h2, h3, -, h5, h6, h7, h8, h9⟩
  · exact Or.inl hl
  obtain ⟨hkid, hoid, hsp, hop⟩ := parts_of_first_frame contracts.decrypt.braid.zeroizingArray hpub codec hct
    hbound q pending hpend _ msg hmsg ourB storeB hpublish hidentity p
  obtain ⟨ec, dSend, ptB, sB', rngB', hkdf, hcand, hinner, hpt, hdr, hrel⟩ :=
    responder_first_frame_inner_succeeds rcB crcB contracts hpub hsym hcon haead hoeq codec view oracleA hsealA
      traceB oracleB oracleOfB agreements q plaintext hroom src hsrc c hcw hsend p h3 h5 hsp hop h8 rngB
      htraceB dB restB hdrawB
  obtain ⟨out, hout⟩ := Tacenta.UnitLifecycleEstablishResponder.establish_responder_returns rcB crcB contracts
    ourB storeB msg rngB hhead
  obtain ⟨storeB', hcommit, rfl⟩ := establish_responder_commit_of_inner rcB crcB p rngB ptB sB' rngB' hinner out
    hout
  have hrep := Tacenta.UnitLifecycleEstablishResponder.replay_ok storeB p.decoded.kem_prekey_id p.secret
    p.lastResort p.replay p.hReplay
  rw [hkid, hoid] at hcommit
  refine Or.inr ⟨p, ec, dSend, ptB, sB', storeB', rngB', h1, h2, h3, h5, h6, h7, h9, hkdf, hcand, hout, hpt,
    hdr, hcommit, hrep.1, fun hl => ?_, hrel⟩
  obtain ⟨fp, hfp, hfpv⟩ := hrep.2 hl
  rw [h2] at hfpv
  exact ⟨fp, hfp, hfpv⟩

end WholeCall


/-! ## The initiator's first send, received by the responder -/

section Headline

/-- The header the initiator's Braid encodes at its first send, with the MAC: the key generation's seed and
hash, then the authenticator's header MAC at epoch 1 over them (96 bytes under `KeyGenSizesOf`). -/
def headerSource (K : Model.Braid.Kem) (a : Model.Braid.Auth) (ekSeed ekVector : Model.Braid.Bytes) :
    Model.Braid.Bytes :=
  (ekSeed ++ K.hashEk ekSeed ekVector) ++ a.macHdr 1 (ekSeed ++ K.hashEk ekSeed ekVector)

open Tacenta.UnitLifecycleT3 (OracleOf BraidSendRefinementContracts TripleSendRefinementContracts KemView) in
/-- **The initiator's first send, received by the responder.**  For every successful `establish_initiator_for`
output `s` (any record `q` of that run), every plaintext and source at which the first `encrypt` at `s` returns
bytes (`established_encrypt_outcomes`, success arm), and every responder identity, prekey store and source as in
`responder_first_frame_succeeds`: the initiator's source loses exactly its two draws, and `establish_responder`
on the bytes the initiator emitted either refuses with one of the three refusals the store decides (the bundle
naming the last-resort key; store and source as given), or succeeds: it returns the session and bytes equal to
the plaintext the initiator encrypted, takes exactly one draw from the responder's source, commits the store
(`ResponderCommit` of the bundle's identifiers; on the one-time path no fingerprint, on the last-resort path the
fingerprint of the initiator's shared secret), and the session it returns refines `firstReceiptSession`, the
model's step at the view that attributes the received codeword to the header source of the initiator's key
generation at its two draws (`headerSource`).  Under the hypotheses of `first_send_responder_prepares` with the
decrypt agreements at the responder's oracle's KEM, the laws `AeadRoundTrip`, `DhAgreeContributory` and
`KeyGenSizesOf` of the initiator's oracle's KEM, the responder's oracle record, the store bound of
`establish_responder_no_panic`, and the per-run premises that the responder's trace is its oracle's and holds a
draw.  No compiler-trust axiom (the pin): the constants of the encrypt and decrypt refinements are kernel proofs. -/
theorem initiator_first_send_responder_receives [Tacenta.SessionUnitT1.DerivedKeysModel] {R E F : Type}
    (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView) (kem : KemView)
    (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
    (braid : BraidSendRefinementContracts rc oracle.braidKem)
    (triple : TripleSendRefinementContracts)
    (aead : Tacenta.UnitLifecycleT1.AeadSealBounded) (dhCodec : Tacenta.UnitLifecycleT1.DhCodecTotal)
    (oracleOf : OracleOf rc crc dh kem trace oracle) (codec : DhCodecOf dh)
    (codewordView : CodewordViewSendOf view)
    (hz80 : Tacenta.SessionUnitT3.ZeroizingRoundTrips80)
    (hz32 : Tacenta.UnitLifecycleT3.ZeroizingRoundTrips (Array Std.U8 32#usize))
    (hzKeys : Tacenta.UnitLifecycleT3.ZeroizingRoundTrips
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
    (rcB : rand_core_1.RngCore F) (crcB : rand_core_1.CryptoRng F)
    (contracts : Tacenta.UnitLifecycleT1.EstablishResponderContracts rcB)
    (hpub : DhPublicValid) (hsym : DhAgreeSymmetric) (hcon : DhAgreeContributory) (haead : AeadRoundTrip)
    (hrt : Tacenta.UnitLifecycleSessionCodec.DhPublicBytesRoundTrip)
    (hoeq : Tacenta.UnitHeadroomInvariant.OptionEqU64Shape
      (@core.option.Option.Insts.CoreCmpPartialEqOption.eq))
    (traceB : F → List Model.Lifecycle.Key) (oracleB : Model.Lifecycle.Oracle)
    (oracleOfB : DecryptOracleOf rcB crcB dh traceB oracleB)
    (agreements : DecryptRatchetAgreements oracleB.braidKem)
    (ourB : lifecycle.Identity) (storeB : lifecycle.PrekeyStore)
    (hpublish : lifecycle.PrekeyStore.publish storeB = ok bundleA)
    (hidentity : lifecycle.Identity.public ourB = ok storeB.identity_public)
    (hdistinct : PrekeyIdsDistinct storeB)
    (hkem : FirstKemAgrees storeB bundleA.kem_prekey_id q.kemCiphertext q.kemSecret)
    (hhead : Tacenta.UnitLifecycleT1.EstablishResponderHeadroom storeB)
    (rngB : F) (htraceB : traceB rngB = oracleB.draws) (dB : Model.Lifecycle.Key)
    (restB : List Model.Lifecycle.Key) (hdrawB : traceB rngB = dB :: restB) :
    trace rng' = rest ∧
    ((bundleA.kem_prekey_id = storeB.kem_id ∧ ∃ e, StoreRefusal storeB q.sharedBytes e ∧
        lifecycle.establish_responder rcB crcB ourB storeB (alloc.vec.Vec.deref bytes) rngB =
          ok (core.result.Result.Err e, storeB, rngB)) ∨
      ∃ (p : ResponderPreparedParts ourB storeB (alloc.vec.Vec.deref bytes)) (ec : Array U8 32#usize)
        (dSend : Model.Lifecycle.Key) (dk ekSeed ekVector : Model.Braid.Bytes) (ptB : alloc.vec.Vec U8)
        (sB' : lifecycle.Session) (storeB' : lifecycle.PrekeyStore) (rngB' : F),
        oracle.braidKem.keyGen (Model.Lifecycle.braidRandomness (d1 ++ d2)) = some (dk, ekSeed, ekVector) ∧
        p.shared = q.shared ∧ p.secret = q.sharedBytes ∧ p.tripleSecret = q.sharedSlice ∧
        p.peerIdentity = q.ourPublic ∧ p.peerEphemeral = q.ephemeralPublic ∧ p.kemSecret = q.kemSecret ∧
        (p.lastResort = true ↔ bundleA.kem_prekey_id = storeB.kem_id) ∧
        tacenta_ratchet.kdf_rk ec q.dhOutBytes tacenta_ratchet.LabelSet.Tacenta = ok (q.rootKey, q.sendChain) ∧
        oracleB.dhAgree dB (arrayOf q.ratchetBytes) = some dSend ∧
        lifecycle.establish_responder rcB crcB ourB storeB (alloc.vec.Vec.deref bytes) rngB =
          ok (core.result.Result.Ok (sB', ptB), storeB', rngB') ∧
        ptB.val = plaintext.val ∧ traceB rngB' = restB ∧
        ResponderCommit storeB bundleA.kem_prekey_id bundleA.one_time_prekey_id p.lastResort p.replay storeB' ∧
        (p.lastResort = false → p.replay = none) ∧
        (p.lastResort = true → ∃ fp, p.replay = some fp ∧ lifecycle.last_resort_fingerprint q.sharedBytes = ok fp) ∧
        SessionRefines dh oracleB.braidKem sB'
          (firstReceiptSession (responderModelOf dh p) (sliceOf p.braidSecret)
            ⟨headerSource oracle.braidKem (Tacenta.SessionUnitBraidT3.AuthOf q.auth) ekSeed ekVector, 0⟩
            (arrayOf ec) (arrayOf q.sparseRoot) (arrayOf q.sparseSend) (arrayOf q.sparseReceive)
            (arrayOf q.ratchetBytes) (arrayOf q.dhOut) dSend (oracleB.dhPublic dB) dB)) := by
  obtain ⟨output, hcall', hdr, hcases⟩ := Tacenta.UnitLifecycleEstablishedEncrypt.established_encrypt_outcomes rc
    crc trace dh kem view oracle braid triple aead dhCodec oracleOf codec codewordView hz80 hz32 hzKeys hgen
    hct hbound rcE crcE ourA bundleA expected rng0 rng1 s h plaintext hroom rng htrace d1 d2 rest hdraws
  rw [hcall] at hcall'
  cases hcall'
  refine ⟨hdr, ?_⟩
  rcases hcases with ⟨-, hres, -⟩ | ⟨dk, ekSeed, ekVector, hkg, bytes', hres, -, -, tripleNext, messageKey,
    chunk, encoder, pending, a, ⟨header, hsendM⟩, hbraidA, hnc, hpend, hwire, -⟩
  · cases hres
  simp only [core.result.Result.Ok.injEq] at hres
  subst hres
  subst hq
  -- the message key is the first key of the initiator's chains
  have hmk : messageKey = firstKey (arrayOf q.sendChain) (arrayOf q.sparseSend) := by
    rw [established_triple_first dh q.toInitiatorOutputParts, first_send_key] at hsendM
    simp only [Except.ok.injEq, Prod.mk.injEq] at hsendM
    exact hsendM.2.2.symm
  -- the chunk is the first chunk of the header source
  have ha : a = Tacenta.SessionUnitBraidT3.AuthOf q.auth := by
    simp only [establishedModelOf, InitiatorOutputParts.session,
      Tacenta.UnitLifecycleEstablishInitiatorShape.unsampledModelOf, Model.Braid.BraidState.keysUnsampled.injEq]
      at hbraidA
    exact hbraidA.2.symm
  subst ha
  have hchunk : chunk = ⟨headerSource oracle.braidKem (Tacenta.SessionUnitBraidT3.AuthOf q.auth) ekSeed
      ekVector, 0⟩ := by
    simp only [Model.Braid.encode, Model.Braid.Encoder.nextChunk, Prod.mk.injEq] at hnc
    rw [← hnc.1]
    rfl
  obtain ⟨hs32, -, hhl⟩ := hsizes _ _ _ _ hkg
  have hsrc : (headerSource oracle.braidKem (Tacenta.SessionUnitBraidT3.AuthOf q.auth) ekSeed ekVector).length =
      Model.Braid.headerSize + Model.Braid.macSize := by
    simp [headerSource, Model.Braid.Auth.macHdr, Model.Kdf.hmac_length, Model.Kdf.hashLen, hs32, hhl,
      Model.Braid.headerSize, Model.Braid.macSize]
  obtain ⟨-, -, c, -, -, hc0, hcw, -⟩ := Tacenta.UnitHeldKemWitness.held_encoder contracts.divCeilValue
    agreements.erasure _ (by rw [hsrc]; rfl)
  have hmc : modelChunkOf (headerSource oracle.braidKem (Tacenta.SessionUnitBraidT3.AuthOf q.auth) ekSeed
      ekVector) c = ⟨headerSource oracle.braidKem (Tacenta.SessionUnitBraidT3.AuthOf q.auth) ekSeed ekVector, 0⟩ := by
    simp [modelChunkOf, hc0]
  have hsend := codewordView.send (establishedModelOf dh q.session).braid _ c hcw
  rw [hmk, hchunk, ← hmc] at hwire
  rcases responder_first_frame_succeeds rcB crcB contracts hpub hsym hcon haead hrt hct hbound hoeq codec view
      oracle oracleOf.aeadSeal traceB oracleB oracleOfB agreements q pending hpend plaintext (by omega) _ hsrc c
      hcw hsend (alloc.vec.Vec.deref bytes) hwire ourB storeB hpublish hidentity hdistinct hkem hhead rngB
      htraceB dB restB hdrawB with hl | ⟨p, ec, dSend, ptB, sB', storeB', rngB', hrest⟩
  · exact Or.inl hl
  · rw [hmc] at hrest
    exact Or.inr ⟨p, ec, dSend, dk, ekSeed, ekVector, ptB, sB', storeB', rngB', hkg, hrest⟩

open Tacenta.UnitLifecycleT3 (OracleOf BraidSendRefinementContracts TripleSendRefinementContracts KemView) in
/-- **The initiator's first send, at the responder: every outcome.**  Under the hypotheses of
`initiator_first_send_responder_receives` without the laws `DhAgreeContributory` and `AeadRoundTrip`: the
initiator's source loses exactly its two draws, and `establish_responder` on the bytes the initiator emitted
either refuses with one of the three refusals the store decides (store and source as given), or reaches the inner
receive with parts carrying the initiator's secrets and returns exactly one of `Handshake(NonContributoryAgreement)`
(the responder oracle refuses the draw's agreement with the initiator's ratchet key), `Aead` (that agreement
returns and the responder oracle's open of the initiator oracle's seal of the plaintext is refused), each with the
store as given and exactly one draw taken, or `Ok` of what that open returned, with the store committed and the
session related as in `initiator_first_send_responder_receives`.  The refusals are the named premises' failures; a
tampered frame is not considered (the bytes are the initiator's).  Its axioms are that theorem's (the pin). -/
theorem initiator_first_send_responder_outcomes [Tacenta.SessionUnitT1.DerivedKeysModel] {R E F : Type}
    (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView) (kem : KemView)
    (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
    (braid : BraidSendRefinementContracts rc oracle.braidKem)
    (triple : TripleSendRefinementContracts)
    (aead : Tacenta.UnitLifecycleT1.AeadSealBounded) (dhCodec : Tacenta.UnitLifecycleT1.DhCodecTotal)
    (oracleOf : OracleOf rc crc dh kem trace oracle) (codec : DhCodecOf dh)
    (codewordView : CodewordViewSendOf view)
    (hz80 : Tacenta.SessionUnitT3.ZeroizingRoundTrips80)
    (hz32 : Tacenta.UnitLifecycleT3.ZeroizingRoundTrips (Array Std.U8 32#usize))
    (hzKeys : Tacenta.UnitLifecycleT3.ZeroizingRoundTrips
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
    (rcB : rand_core_1.RngCore F) (crcB : rand_core_1.CryptoRng F)
    (contracts : Tacenta.UnitLifecycleT1.EstablishResponderContracts rcB)
    (hpub : DhPublicValid) (hsym : DhAgreeSymmetric)
    (hrt : Tacenta.UnitLifecycleSessionCodec.DhPublicBytesRoundTrip)
    (hoeq : Tacenta.UnitHeadroomInvariant.OptionEqU64Shape
      (@core.option.Option.Insts.CoreCmpPartialEqOption.eq))
    (traceB : F → List Model.Lifecycle.Key) (oracleB : Model.Lifecycle.Oracle)
    (oracleOfB : DecryptOracleOf rcB crcB dh traceB oracleB)
    (agreements : DecryptRatchetAgreements oracleB.braidKem)
    (ourB : lifecycle.Identity) (storeB : lifecycle.PrekeyStore)
    (hpublish : lifecycle.PrekeyStore.publish storeB = ok bundleA)
    (hidentity : lifecycle.Identity.public ourB = ok storeB.identity_public)
    (hdistinct : PrekeyIdsDistinct storeB)
    (hkem : FirstKemAgrees storeB bundleA.kem_prekey_id q.kemCiphertext q.kemSecret)
    (hhead : Tacenta.UnitLifecycleT1.EstablishResponderHeadroom storeB)
    (rngB : F) (htraceB : traceB rngB = oracleB.draws) (dB : Model.Lifecycle.Key)
    (restB : List Model.Lifecycle.Key) (hdrawB : traceB rngB = dB :: restB) :
    trace rng' = rest ∧
    ((bundleA.kem_prekey_id = storeB.kem_id ∧ ∃ e, StoreRefusal storeB q.sharedBytes e ∧
        lifecycle.establish_responder rcB crcB ourB storeB (alloc.vec.Vec.deref bytes) rngB =
          ok (core.result.Result.Err e, storeB, rngB)) ∨
      ∃ (p : ResponderPreparedParts ourB storeB (alloc.vec.Vec.deref bytes)) (ec : Array U8 32#usize)
        (dk ekSeed ekVector : Model.Braid.Bytes) (rngB' : F),
        oracle.braidKem.keyGen (Model.Lifecycle.braidRandomness (d1 ++ d2)) = some (dk, ekSeed, ekVector) ∧
        p.shared = q.shared ∧ p.secret = q.sharedBytes ∧ p.tripleSecret = q.sharedSlice ∧
        p.peerIdentity = q.ourPublic ∧ p.peerEphemeral = q.ephemeralPublic ∧ p.kemSecret = q.kemSecret ∧
        (p.lastResort = true ↔ bundleA.kem_prekey_id = storeB.kem_id) ∧
        tacenta_ratchet.kdf_rk ec q.dhOutBytes tacenta_ratchet.LabelSet.Tacenta = ok (q.rootKey, q.sendChain) ∧
        traceB rngB' = restB ∧
        ((lifecycle.establish_responder rcB crcB ourB storeB (alloc.vec.Vec.deref bytes) rngB =
            ok (core.result.Result.Err (lifecycle.Error.Handshake SessionError.NonContributoryAgreement), storeB,
              rngB') ∧
            oracleB.dhAgree dB (arrayOf q.ratchetBytes) = none) ∨
          (lifecycle.establish_responder rcB crcB ourB storeB (alloc.vec.Vec.deref bytes) rngB =
              ok (core.result.Result.Err lifecycle.Error.Aead, storeB, rngB') ∧
            ∃ dSend, oracleB.dhAgree dB (arrayOf q.ratchetBytes) = some dSend ∧
              firstOpen oracle oracleB (firstKey (arrayOf q.sendChain) (arrayOf q.sparseSend))
                (sliceOf plaintext) (firstAd view (establishedModelOf dh q.session)
                  ⟨headerSource oracle.braidKem (Tacenta.SessionUnitBraidT3.AuthOf q.auth) ekSeed ekVector, 0⟩) =
                none) ∨
          (∃ ptB sB' storeB' dSend x,
            lifecycle.establish_responder rcB crcB ourB storeB (alloc.vec.Vec.deref bytes) rngB =
              ok (core.result.Result.Ok (sB', ptB), storeB', rngB') ∧
            oracleB.dhAgree dB (arrayOf q.ratchetBytes) = some dSend ∧
            firstOpen oracle oracleB (firstKey (arrayOf q.sendChain) (arrayOf q.sparseSend))
              (sliceOf plaintext) (firstAd view (establishedModelOf dh q.session)
                ⟨headerSource oracle.braidKem (Tacenta.SessionUnitBraidT3.AuthOf q.auth) ekSeed ekVector, 0⟩) =
              some x ∧
            vecOf ptB = x ∧
            ResponderCommit storeB bundleA.kem_prekey_id bundleA.one_time_prekey_id p.lastResort p.replay
              storeB' ∧
            SessionRefines dh oracleB.braidKem sB'
              (firstReceiptSession (responderModelOf dh p) (sliceOf p.braidSecret)
                ⟨headerSource oracle.braidKem (Tacenta.SessionUnitBraidT3.AuthOf q.auth) ekSeed ekVector, 0⟩
                (arrayOf ec) (arrayOf q.sparseRoot) (arrayOf q.sparseSend) (arrayOf q.sparseReceive)
                (arrayOf q.ratchetBytes) (arrayOf q.dhOut) dSend (oracleB.dhPublic dB) dB)))) := by
  obtain ⟨output, hcall', hdr, hcases⟩ := Tacenta.UnitLifecycleEstablishedEncrypt.established_encrypt_outcomes rc
    crc trace dh kem view oracle braid triple aead dhCodec oracleOf codec codewordView hz80 hz32 hzKeys hgen
    hct hbound rcE crcE ourA bundleA expected rng0 rng1 s h plaintext hroom rng htrace d1 d2 rest hdraws
  rw [hcall] at hcall'
  cases hcall'
  refine ⟨hdr, ?_⟩
  rcases hcases with ⟨-, hres, -⟩ | ⟨dk, ekSeed, ekVector, hkg, bytes', hres, -, -, tripleNext, messageKey,
    chunk, encoder, pending, a, ⟨header, hsendM⟩, hbraidA, hnc, hpend, hwire, -⟩
  · cases hres
  simp only [core.result.Result.Ok.injEq] at hres
  subst hres
  subst hq
  have hmk : messageKey = firstKey (arrayOf q.sendChain) (arrayOf q.sparseSend) := by
    rw [established_triple_first dh q.toInitiatorOutputParts, first_send_key] at hsendM
    simp only [Except.ok.injEq, Prod.mk.injEq] at hsendM
    exact hsendM.2.2.symm
  have ha : a = Tacenta.SessionUnitBraidT3.AuthOf q.auth := by
    simp only [establishedModelOf, InitiatorOutputParts.session,
      Tacenta.UnitLifecycleEstablishInitiatorShape.unsampledModelOf, Model.Braid.BraidState.keysUnsampled.injEq]
      at hbraidA
    exact hbraidA.2.symm
  subst ha
  have hchunk : chunk = ⟨headerSource oracle.braidKem (Tacenta.SessionUnitBraidT3.AuthOf q.auth) ekSeed
      ekVector, 0⟩ := by
    simp only [Model.Braid.encode, Model.Braid.Encoder.nextChunk, Prod.mk.injEq] at hnc
    rw [← hnc.1]
    rfl
  obtain ⟨hs32, -, hhl⟩ := hsizes _ _ _ _ hkg
  have hsrc : (headerSource oracle.braidKem (Tacenta.SessionUnitBraidT3.AuthOf q.auth) ekSeed ekVector).length =
      Model.Braid.headerSize + Model.Braid.macSize := by
    simp [headerSource, Model.Braid.Auth.macHdr, Model.Kdf.hmac_length, Model.Kdf.hashLen, hs32, hhl,
      Model.Braid.headerSize, Model.Braid.macSize]
  obtain ⟨-, -, c, -, -, hc0, hcw, -⟩ := Tacenta.UnitHeldKemWitness.held_encoder contracts.divCeilValue
    agreements.erasure _ (by rw [hsrc]; rfl)
  have hmc : modelChunkOf (headerSource oracle.braidKem (Tacenta.SessionUnitBraidT3.AuthOf q.auth) ekSeed
      ekVector) c = ⟨headerSource oracle.braidKem (Tacenta.SessionUnitBraidT3.AuthOf q.auth) ekSeed ekVector, 0⟩ := by
    simp [modelChunkOf, hc0]
  have hsend := codewordView.send (establishedModelOf dh q.session).braid _ c hcw
  rw [hmk, hchunk, ← hmc] at hwire
  rcases responder_first_frame_outcomes rcB crcB contracts hpub hsym hrt hct hbound hoeq codec view oracle
      traceB oracleB oracleOfB agreements q pending hpend plaintext _ hsrc c hcw hsend
      (alloc.vec.Vec.deref bytes) hwire ourB storeB hpublish hidentity hdistinct hkem hhead rngB htraceB dB restB
      hdrawB with hl | ⟨p, ec, rngB', hrest⟩
  · exact Or.inl hl
  · rw [hmc] at hrest
    exact Or.inr ⟨p, ec, dk, ekSeed, ekVector, rngB', hkg, hrest⟩

end Headline


/-! ## One interpretation of every law -/

section JointModel

open Tacenta.UnitLifecycleIntegrationScreen (byteRng byteCrc byteTrace)
open Tacenta.UnitLifecycleResponderFirstFrame (DhAgreeSymmetricShape FirstFrameSuccessShape PoolEntry
  basePoint_ne_zero)
open Tacenta.UnitLifecycleEstablishedEncrypt (toyKemR zeroSeed oneSeed EncryptExtraLawsShape
  established_encrypt_laws_model encapResult encapFill)
open Tacenta.UnitLifecycleDecryptRatchetScreen (DhViewShape)
open Tacenta.UnitOracleShape (InterpO DhViewOf KemViewOf)

/-- `Interp.modelFirstFrame` (the first-frame joint model) with the toy seal and open of `UnitOracleModel`: sealing
puts a zero byte in front of the plaintext where that fits a `usize` length, and opening accepts exactly a string
whose first byte is zero and returns the rest.  Every other field is `Interp.modelFirstFrame`'s. -/
noncomputable def Interp.modelFirstReceipt : Interp :=
  { Tacenta.UnitLifecycleResponderFirstFrame.Interp.modelFirstFrame with
    aeadEncrypt := fun _ _ _ p _ => ok (Tacenta.UnitOracleModel.sealModel p)
    aeadDecrypt := fun _ _ _ c _ => ok (Tacenta.UnitOracleModel.openModel c) }

/-- The joint interpretation with its signing function. -/
noncomputable def InterpO.modelFirstReceipt : InterpO :=
  { Interp.modelFirstReceipt with xeddsaSign := Tacenta.UnitOracleModel.signModelO }

/-- The view of the joint interpretation: both key types are their bytes. -/
def viewFirstReceipt : DhViewShape Interp.modelFirstReceipt := ⟨arrayOf, arrayOf⟩
/-- The DH view of the joint interpretation with its signing function. -/
def dhViewFirstReceipt : DhViewOf InterpO.modelFirstReceipt.toInterp :=
  ⟨viewFirstReceipt.privateKey, viewFirstReceipt.publicKey⟩
/-- The KEM view of the joint interpretation with its signing function. -/
def kemViewFirstReceipt : KemViewOf InterpO.modelFirstReceipt.toInterp := ⟨fun _ => []⟩

/-- The joint interpretation's DH codec functions return. -/
theorem modelFirstReceipt_dhCodec : Tacenta.UnitSatisfiabilityJoint.DhCodecShape Interp.modelFirstReceipt :=
  ⟨fun _ => ⟨_, rfl⟩, fun _ => ⟨_, rfl⟩, fun _ => ⟨_, rfl⟩, fun _ => ⟨_, rfl⟩, fun _ => ⟨_, rfl⟩,
    fun _ _ => ⟨_, rfl⟩⟩
/-- The joint interpretation's agreement returns. -/
theorem modelFirstReceipt_dhAgree : Tacenta.UnitSatisfiabilityJoint.DhAgreeShape Interp.modelFirstReceipt :=
  fun _ _ => ⟨_, rfl⟩
/-- The agreement law holds in the joint interpretation: both sides return the base point. -/
theorem modelFirstReceipt_symmetric : DhAgreeSymmetricShape Interp.modelFirstReceipt := by
  intro a b pa pb ha hb
  simp only [Interp.modelFirstReceipt, Tacenta.UnitLifecycleResponderFirstFrame.Interp.modelFirstFrame, ok.injEq] at ha hb
  subst ha hb
  rfl
/-- The joint interpretation's open returns. -/
theorem modelFirstReceipt_aeadOpen : Tacenta.UnitSatisfiabilityJoint.AeadOpenShape Interp.modelFirstReceipt :=
  fun _ _ _ _ _ => ⟨_, rfl⟩
/-- The joint interpretation's seal returns at most 48 bytes more than the plaintext (it adds one). -/
theorem modelFirstReceipt_aeadSeal : Tacenta.UnitSatisfiabilityJoint.AeadSealBoundedShape Interp.modelFirstReceipt := by
  intro ek mk iv plaintext ad
  refine ⟨Tacenta.UnitOracleModel.sealModel plaintext, rfl, ?_⟩
  unfold Tacenta.UnitOracleModel.sealModel
  split <;> simp


/-- **`AeadRoundTripShape` holds in the joint interpretation**: the toy open returns what the toy seal was given. -/
theorem modelFirstReceipt_aeadRoundTrip : AeadRoundTripShape Interp.modelFirstReceipt := by
  intro k1 k2 iv pt ad ct hlen h
  simp only [Interp.modelFirstReceipt, ok.injEq] at h
  subst h
  have hle : pt.val.length + 1 ≤ Usize.max := by omega
  have hs : Tacenta.UnitOracleModel.sealModel pt = ⟨0#u8 :: pt.val, by simp; omega⟩ := by
    unfold Tacenta.UnitOracleModel.sealModel
    rw [dif_pos hle]
  refine ⟨⟨pt.val, pt.property⟩, ?_, rfl⟩
  show ok (Tacenta.UnitOracleModel.openModel
    (alloc.vec.Vec.deref (Tacenta.UnitOracleModel.sealModel pt))) = _
  rw [hs]
  simp [Tacenta.UnitOracleModel.openModel, alloc.vec.Vec.deref]

/-- **`DhAgreeContributoryShape` holds in the joint interpretation**: every public key is the base point, which
is not the zero key, so every agreement with it returns. -/
theorem modelFirstReceipt_contributory : DhAgreeContributoryShape Interp.modelFirstReceipt := by
  intro a b pb hb
  simp only [Interp.modelFirstReceipt, Tacenta.UnitLifecycleResponderFirstFrame.Interp.modelFirstFrame,
    ok.injEq] at hb
  subst hb
  refine ⟨Tacenta.UnitLifecycleEstablishResponder.basePoint, ?_⟩
  show ok (if Tacenta.UnitLifecycleEstablishResponder.basePoint.val =
      Tacenta.UnitLifecycleDecryptRatchetScreen.zeros32.val then none
    else some Tacenta.UnitLifecycleEstablishResponder.basePoint) =
    ok (some Tacenta.UnitLifecycleEstablishResponder.basePoint)
  simp [basePoint_ne_zero]

open Tacenta.UnitSatisfiabilityJoint (InitiatorAxiom ResponderAxiom) in
open Tacenta.UnitLifecycleSessionCodec (ZeroizingVecRoundTripShape DhPrivateBytesRoundTripShape
  DhPublicBytesRoundTripShape OptionBranchSomeShape VecAsSliceShape optionBranchImpl vecAsSliceImpl) in
open Tacenta.UnitLifecycleRestoredSession (KemCiphertextLenBoundShape) in
open Tacenta.UnitLifecycleEstablishInitiatorShape (InitiatorSuccessShape DhPublicValidShape
  KemCiphertextLenLawShape) in
/-- **Every law the statements above take, with the decrypt, establishment, restore, encrypt and responder
laws, holds in one interpretation**, `InterpO.modelFirstReceipt` (the first-frame joint model, whose agreement is
symmetric and contributory on every key `public_key` returns, with the toy seal and open), with its views, the toy KEM
`toyKemR`, `optionEqImpl` for `Option::eq` and the constant `ok 0` for `kem::ciphertext_len`: the decrypt laws,
the initiator contract axioms, `InitiatorSuccessShape`, `DhPublicValidShape`, the ciphertext-length law, the
encrypt extra laws, the six laws of the restored session's round trip, the size law and the two seeds of the
encrypt branch, the responder contract axioms, `ResponderSuccessShape`, `ZeroKeyShape`, the agreement law
`DhAgreeSymmetricShape`, `FirstFrameSuccessShape` (with an empty public KEM key and `Vec::is_empty` as the
emptiness test), and the two laws of this module, `AeadRoundTripShape` and `DhAgreeContributoryShape`.  In the substitution sense of `UnitSatisfiabilityRecords`; not a statement that the real
primitives meet them. -/
theorem first_receipt_laws_model :
    Tacenta.UnitLifecycleDecryptScreen.DecryptJointLawsShape Interp.modelFirstReceipt viewFirstReceipt toyKemR
        @Tacenta.UnitHeadroomInvariant.optionEqImpl ∧
      Nonempty (InitiatorAxiom Interp.modelFirstReceipt byteRng) ∧
      InitiatorSuccessShape Interp.modelFirstReceipt byteRng byteCrc ∧
      DhPublicValidShape Interp.modelFirstReceipt ∧
      KemCiphertextLenLawShape (ok 0#usize) Interp.modelFirstReceipt ∧
      EncryptExtraLawsShape InterpO.modelFirstReceipt dhViewFirstReceipt kemViewFirstReceipt toyKemR (ok 0#usize) ∧
      (ZeroizingVecRoundTripShape Interp.modelFirstReceipt ∧
        DhPrivateBytesRoundTripShape Interp.modelFirstReceipt ∧
        DhPublicBytesRoundTripShape Interp.modelFirstReceipt ∧ OptionBranchSomeShape @optionBranchImpl ∧
        VecAsSliceShape @vecAsSliceImpl ∧ KemCiphertextLenBoundShape (ok 0#usize)) ∧
      Tacenta.UnitLifecycleEstablishedEncrypt.KeyGenSizesOf toyKemR ∧
      toyKemR.keyGen (Model.Lifecycle.braidRandomness
          (zeroSeed.map Tacenta.SessionUnitBraidT3.u8)) = none ∧
      toyKemR.keyGen (Model.Lifecycle.braidRandomness
          (oneSeed.map Tacenta.SessionUnitBraidT3.u8)) ≠ none ∧
      Nonempty (ResponderAxiom Interp.modelFirstReceipt byteRng) ∧
      Tacenta.UnitLifecycleEstablishResponder.ResponderSuccessShape Interp.modelFirstReceipt ∧
      Tacenta.UnitLifecycleEstablishResponder.ZeroKeyShape Interp.modelFirstReceipt ∧
      DhAgreeSymmetricShape Interp.modelFirstReceipt ∧
      FirstFrameSuccessShape Interp.modelFirstReceipt (fun _ => ok (alloc.vec.Vec.new U8))
        (fun _ v => ok (decide (v.val = []))) ∧
      AeadRoundTripShape Interp.modelFirstReceipt ∧ DhAgreeContributoryShape Interp.modelFirstReceipt := by
  obtain ⟨M, ⟨A⟩, -, -, C, X, ⟨r1, r2, r3, r4, r5, r6⟩, ks, s0, s1⟩ := established_encrypt_laws_model
  obtain ⟨-, ⟨RA⟩, -, -, -⟩ := Tacenta.UnitLifecycleEstablishResponder.responder_route_laws_model
  have hcodec := modelFirstReceipt_dhCodec
  have hagree := modelFirstReceipt_dhAgree
  have hb := basePoint_ne_zero
  refine ⟨?_, ⟨?_⟩, ?_, ?_, ?_, ?_, ⟨?_, ?_, ?_, r4, r5, r6⟩, ks, s0, s1, ⟨?_⟩, ?_, ?_,
    modelFirstReceipt_symmetric, ?_, modelFirstReceipt_aeadRoundTrip, modelFirstReceipt_contributory⟩
  · exact
      { dhCodec := hcodec
        dhAgree := hagree
        aeadOpen := modelFirstReceipt_aeadOpen
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
      simpa [Interp.modelFirstReceipt, Tacenta.UnitLifecycleResponderFirstFrame.Interp.modelFirstFrame] using h.symm
    subst hp
    exact ⟨Tacenta.UnitLifecycleEstablishResponder.basePoint, rfl,
      Tacenta.UnitLifecycleEstablishResponder.basePoint_canonical, rfl⟩
  · exact C
  · exact
      { oracle :=
          { dhCodec := hcodec
            dhAgree := hagree
            dhIdentity := X.oracle.dhIdentity
            aeadSeal := modelFirstReceipt_aeadSeal
            aeadOpen := modelFirstReceipt_aeadOpen
            kemDecapsulate := X.oracle.kemDecapsulate
            xeddsaVerify := X.oracle.xeddsaVerify
            signLaw := X.oracle.signLaw
            kemLaw := X.oracle.kemLaw
            dhView := X.oracle.dhView
            kemView := X.oracle.kemView }
        encrypt :=
          { braid := by have h := X.encrypt.braid; cases h; constructor <;> assumption
            triple := by have h := X.encrypt.triple; cases h; constructor <;> assumption
            aeadSeal := modelFirstReceipt_aeadSeal
            messageKeyMaterial := X.encrypt.messageKeyMaterial
            dhCodec := hcodec }
        keyGen := X.keyGen
        zeroizingKeys := X.zeroizingKeys
        ciphertextBound := X.ciphertextBound }
  · exact r1
  · exact r2
  · exact r3
  · exact
      { decrypt := ⟨hcodec, hagree, modelFirstReceipt_aeadOpen, RA.decrypt.random32,
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

end JointModel


/-! ## The reach: one run, from `publish` to the responder's success -/

section Reach

open Tacenta.UnitLifecycleIntegrationScreen (byteRng byteCrc byteTrace)
open Tacenta.UnitLifecycleResponderFirstFrame (FirstFrameSuccessShape PoolEntry reachStore reachBundle
  publish_reachStore reachStore_distinct reach_establishment heldKemPair zPool)
open Tacenta.UnitSatisfiabilityJoint (InitiatorAxiom ResponderAxiom) in
open Tacenta.UnitLifecycleEstablishedEncrypt (EstablishedEncryptHypotheses EncryptExtraLaws emptyPlaintext) in
/-- **The reach of the responder's success at the initiator's first frame**: at the real constants, under the
laws of `first_send_responder_reachable` (the decrypt laws `DecryptJointLaws K dh`, the initiator and responder
contract axioms, `InitiatorSuccessShape`, `DhPublicValid`, `KemCiphertextLenOf`, the encrypt extra laws,
`DhAgreeSymmetric`, the public-key byte round trip and `FirstFrameSuccessShape`, all assumed), the size law
`KeyGenSizesOf K` and the two laws of this module, for every initiator identity and every 64-byte source at
whose bytes the model's key generation answers: there are a prekey store, its owner and the bundle it publishes, a
successful establishment against that bundle (a record `q`), a first send of the empty plaintext that returns
bytes, and a responder oracle record for the byte-stream source holding the same 64 bytes, at which every premise
of `initiator_first_send_responder_receives` holds (the store bound included) and `establish_responder` on the
bytes **succeeds**, returning the empty plaintext the initiator encrypted.  The store takes the last-resort path
(one key as identity and signed prekey, no one-time keys of either kind, an empty replay record, no legacy
marker); the one-time path has no exhibited run. -/
theorem first_send_receive_reachable (K : Model.Braid.Kem) (dh : DhView)
    (kem : Tacenta.UnitLifecycleT3.KemView) (L : Tacenta.UnitLifecycleDecryptScreen.DecryptJointLaws K dh)
    (A : Nonempty (InitiatorAxiom Interp.real byteRng))
    (S : Tacenta.UnitLifecycleEstablishInitiatorShape.InitiatorSuccessShape Interp.real byteRng byteCrc)
    (hpub : DhPublicValid) (hct : Tacenta.UnitLifecycleEstablishInitiatorShape.KemCiphertextLenOf)
    (X : EncryptExtraLaws K dh kem) (RA : Nonempty (ResponderAxiom Interp.real byteRng))
    (hsym : DhAgreeSymmetric) (hrt : Tacenta.UnitLifecycleSessionCodec.DhPublicBytesRoundTrip)
    (FS : FirstFrameSuccessShape Interp.real tacenta_boundary.kem.KeyPair.public_key
      @alloc.vec.Vec.is_empty)
    (hsizes : Tacenta.UnitLifecycleEstablishedEncrypt.KeyGenSizesOf K)
    (hcon : DhAgreeContributory) (haead : AeadRoundTrip)
    (ourA : lifecycle.Identity) (seed : List Std.U8) (hseed : seed.length = 64)
    (hkg : K.keyGen (Model.Lifecycle.braidRandomness (seed.map Tacenta.SessionUnitBraidT3.u8)) ≠ none) :
    ∃ (oracle : Model.Lifecycle.Oracle) (bundle : lifecycle.PublishedBundle) (rng0 rng1 : List Std.U8)
      (q : InitiatorSecretParts byteRng byteCrc ourA bundle) (bytes : alloc.vec.Vec Std.U8)
      (s' : lifecycle.Session) (rng' : List Std.U8) (ourB : lifecycle.Identity)
      (storeB : lifecycle.PrekeyStore) (sB' : lifecycle.Session) (ptB : alloc.vec.Vec Std.U8)
      (storeB' : lifecycle.PrekeyStore) (rngB' : List Std.U8),
      oracle.braidKem = K ∧
      EstablishedEncryptHypotheses byteRng byteCrc byteTrace dh kem Tacenta.UnitLifecycleRepair.witnessView
        oracle byteRng byteCrc ourA bundle bundle.bundle.identity_key rng0 rng1 q.session emptyPlaintext seed ∧
      lifecycle.Session.encrypt byteRng byteCrc q.session emptyPlaintext seed =
        ok (core.result.Result.Ok bytes, s', rng') ∧
      lifecycle.PrekeyStore.publish storeB = ok bundle ∧
      lifecycle.Identity.public ourB = ok storeB.identity_public ∧ PrekeyIdsDistinct storeB ∧
      FirstKemAgrees storeB bundle.kem_prekey_id q.kemCiphertext q.kemSecret ∧
      Tacenta.UnitLifecycleT1.EstablishResponderHeadroom storeB ∧
      DecryptOracleOf byteRng byteCrc dh byteTrace oracle ∧ byteTrace seed = oracle.draws ∧
      storeB.legacy_last_resort_blocked.val = [] ∧ storeB.last_resort_seen.val = [] ∧
      lifecycle.establish_responder byteRng byteCrc ourB storeB (alloc.vec.Vec.deref bytes) seed =
        ok (core.result.Result.Ok (sB', ptB), storeB', rngB') ∧
      ptB.val = emptyPlaintext.val := by
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
  have hhead : Tacenta.UnitLifecycleT1.EstablishResponderHeadroom storeB :=
    ⟨by simp [storeB, reachStore]; exact Tacenta.UnitSatisfiabilityBraidAgreements.usize_max_ge 1 (by norm_num)⟩
  have D := (Tacenta.UnitLifecycleEstablishedDecrypt.established_decrypt_hypotheses_jointly_satisfiable
    oracle.braidKem dh L A S hpub hct ourA)
  obtain ⟨oracle0, bundle1, s1, rng11, hK0, H1⟩ := D
  have ag : DecryptRatchetAgreements oracle.braidKem :=
    hK0 ▸ (H1 Tacenta.UnitLifecycleRepair.witnessView).agreements
  have oracleOfB : DecryptOracleOf byteRng byteCrc dh byteTrace oracle :=
    DecryptOracleOf.of_oracleOf H.oracleOf
  obtain ⟨d1, d2, rest2, hdrB⟩ : ∃ d1 d2 rest2, byteTrace seed = d1 :: d2 :: rest2 := by
    have := Tacenta.UnitLifecycleEstablishedEncrypt.byteTrace_two seed (by omega)
    exact ⟨_, _, _, this⟩
  obtain ⟨-, hdisj⟩ := initiator_first_send_responder_receives byteRng byteCrc byteTrace dh kem
    Tacenta.UnitLifecycleRepair.witnessView oracle H.braid H.triple H.aead H.dhCodec H.oracleOf H.codec
    H.codewordView H.zeroizing80 H.zeroizing32 H.zeroizingKeys H.keyGen hsizes H.kemCiphertextLen
    H.kemCiphertextBound byteRng byteCrc ourA _ _ _ rng1 q.session h q rfl emptyPlaintext H.room seed
    H.trace_eq _ _ _ (Tacenta.UnitLifecycleEstablishedEncrypt.byteTrace_two seed (by omega)) bytes s' rng'
    hcall byteRng byteCrc contracts hpub hsym hcon haead hrt L.optionEq byteTrace oracle oracleOfB ag ourB
    storeB hpublish hidentity hdistinct hkem hhead seed H.trace_eq d1 (d2 :: rest2) hdrB
  rcases hdisj with ⟨-, e, hrefuse, -⟩ |
    ⟨p, ec, dSend, dk', ekSeed', ekVector', ptB, sB', storeB', rngB', -, -, -, -, -, -, -, -, -, -, hcallB, hpt, -⟩
  · exfalso
    rcases hrefuse with ⟨-, hleg⟩ | ⟨-, fp, -, x, hx, -⟩ | ⟨-, -, hne, -⟩
    · simp [storeB, reachStore] at hleg
    · simp [storeB, reachStore] at hx
    · exact hne (by simp [storeB, reachStore])
  · exact ⟨oracle, _, _, rng1, q, bytes, s', rng', ourB, storeB, sB', ptB, storeB', rngB', rfl, H, hcall,
      hpublish, hidentity, hdistinct, hkem, hhead, oracleOfB, H.trace_eq, by simp [storeB, reachStore],
      by simp [storeB, reachStore], hcallB, hpt⟩

end Reach

end Tacenta.UnitLifecycleResponderFirstReceipt

/-! ## Pins

The constants each result depends on, and the statement of each result and definition, held by the
build.  `attest.py` requires every one of them (`REQUIRED_PINS`, `REQUIRED_STATEMENT_PINS`,
`REQUIRED_PRINT_FORM`). -/

/--
info: 'Tacenta.UnitLifecycleResponderFirstReceipt.first_send_key' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleResponderFirstReceipt.first_send_key

/--
info: 'Tacenta.UnitLifecycleResponderFirstReceipt.first_receive_key' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleResponderFirstReceipt.first_receive_key

/--
info: 'Tacenta.UnitLifecycleResponderFirstReceipt.first_receive_with_eviction' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleResponderFirstReceipt.first_receive_with_eviction

/--
info: 'Tacenta.UnitLifecycleResponderFirstReceipt.readBe64_be64_kernel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleResponderFirstReceipt.readBe64_be64_kernel

/--
info: 'Tacenta.UnitLifecycleResponderFirstReceipt.readBe16_be16_kernel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleResponderFirstReceipt.readBe16_be16_kernel

/--
info: 'Tacenta.UnitLifecycleResponderFirstReceipt.decode_encodeMessage' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleResponderFirstReceipt.decode_encodeMessage

/--
info: 'Tacenta.UnitLifecycleResponderFirstReceipt.first_frame_model_outcomes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleResponderFirstReceipt.first_frame_model_outcomes

/--
info: 'Tacenta.UnitLifecycleResponderFirstReceipt.aeadRoundTrip_is' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleResponderFirstReceipt.aeadRoundTrip_is

/--
info: 'Tacenta.UnitLifecycleResponderFirstReceipt.dhAgreeContributory_is' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleResponderFirstReceipt.dhAgreeContributory_is

/--
info: 'Tacenta.UnitLifecycleResponderFirstReceipt.first_init_pair' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kdf.hkdf_sha256,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleResponderFirstReceipt.first_init_pair

/--
info: 'Tacenta.UnitLifecycleResponderFirstReceipt.established_triple_first' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleResponderFirstReceipt.established_triple_first

/--
info: 'Tacenta.UnitLifecycleResponderFirstReceipt.responder_triple_first' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kdf.hkdf_sha256,
 tacenta_session_unit.tacenta_kdf.hmac_sha256,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.HEADER_LEN,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.dh.is_prime_order_public,
 tacenta_session_unit.tacenta_boundary.kem.KeyPair,
 tacenta_session_unit.tacenta_boundary.kem.decapsulate,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.Pair.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.core.num.Usize.div_ceil,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.agree,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 tacenta_session_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleResponderFirstReceipt.responder_triple_first

/--
info: 'Tacenta.UnitLifecycleResponderFirstReceipt.first_kdf_model' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kdf.hkdf_sha256,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleResponderFirstReceipt.first_kdf_model

/--
info: 'Tacenta.UnitLifecycleResponderFirstReceipt.zeroized_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleResponderFirstReceipt.zeroized_eq

/--
info: 'Tacenta.UnitLifecycleResponderFirstReceipt.parts_of_first_frame' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleResponderFirstReceipt.parts_of_first_frame

/--
info: 'Tacenta.UnitLifecycleResponderFirstReceipt.view_ratchet_public' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kdf.hkdf_sha256,
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
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 tacenta_session_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleResponderFirstReceipt.view_ratchet_public

/--
info: 'Tacenta.UnitLifecycleResponderFirstReceipt.responder_first_agreement' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleResponderFirstReceipt.responder_first_agreement

/--
info: 'Tacenta.UnitLifecycleResponderFirstReceipt.responder_candidate_agreement' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleResponderFirstReceipt.responder_candidate_agreement

/--
info: 'Tacenta.UnitLifecycleResponderFirstReceipt.first_identityAd_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kdf.hkdf_sha256,
 tacenta_session_unit.tacenta_kdf.hmac_sha256,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.HEADER_LEN,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.rand_core_1.error.Error,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.dh.is_prime_order_public,
 tacenta_session_unit.tacenta_boundary.kem.KeyPair,
 tacenta_session_unit.tacenta_boundary.kem.decapsulate,
 tacenta_session_unit.tacenta_boundary.kem.encapsulate,
 tacenta_session_unit.tacenta_boundary.xeddsa.verify,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.Pair.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.core.num.Usize.div_ceil,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.agree,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 tacenta_session_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleResponderFirstReceipt.first_identityAd_eq

/--
info: 'Tacenta.UnitLifecycleResponderFirstReceipt.arrayOf_arrayOfBytes' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleResponderFirstReceipt.arrayOf_arrayOfBytes

/--
info: 'Tacenta.UnitLifecycleResponderFirstReceipt.aead_open_sealed' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleResponderFirstReceipt.aead_open_sealed

/--
info: 'Tacenta.UnitLifecycleResponderFirstReceipt.attributedView_send' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.core.num.Usize.div_ceil]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleResponderFirstReceipt.attributedView_send

/--
info: 'Tacenta.UnitLifecycleResponderFirstReceipt.firstFrame_attributedView' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleResponderFirstReceipt.firstFrame_attributedView

/--
info: 'Tacenta.UnitLifecycleResponderFirstReceipt.first_receipt_run_inputs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kdf.hkdf_sha256,
 tacenta_session_unit.tacenta_kdf.hmac_sha256,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.HEADER_LEN,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.dh.is_prime_order_public,
 tacenta_session_unit.tacenta_boundary.kem.KeyPair,
 tacenta_session_unit.tacenta_boundary.kem.decapsulate,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.Pair.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.core.num.Usize.div_ceil,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.agree,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 tacenta_session_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleResponderFirstReceipt.first_receipt_run_inputs

/--
info: 'Tacenta.UnitLifecycleResponderFirstReceipt.firstAd_length_le' depends on axioms: [propext,
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
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.to_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleResponderFirstReceipt.firstAd_length_le

/--
info: 'Tacenta.UnitLifecycleResponderFirstReceipt.responder_first_frame_inner_outcomes' depends on axioms: [propext,
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
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleResponderFirstReceipt.responder_first_frame_inner_outcomes

/--
info: 'Tacenta.UnitLifecycleResponderFirstReceipt.responder_first_frame_inner_succeeds' depends on axioms: [propext,
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
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleResponderFirstReceipt.responder_first_frame_inner_succeeds

/--
info: 'Tacenta.UnitLifecycleResponderFirstReceipt.establish_responder_commit_of_inner' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleResponderFirstReceipt.establish_responder_commit_of_inner

/--
info: 'Tacenta.UnitLifecycleResponderFirstReceipt.establish_responder_refused_of_inner' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleResponderFirstReceipt.establish_responder_refused_of_inner

/--
info: 'Tacenta.UnitLifecycleResponderFirstReceipt.responder_first_frame_outcomes' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleResponderFirstReceipt.responder_first_frame_outcomes

/--
info: 'Tacenta.UnitLifecycleResponderFirstReceipt.responder_first_frame_succeeds' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleResponderFirstReceipt.responder_first_frame_succeeds

/--
info: 'Tacenta.UnitLifecycleResponderFirstReceipt.initiator_first_send_responder_receives' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleResponderFirstReceipt.initiator_first_send_responder_receives

/--
info: 'Tacenta.UnitLifecycleResponderFirstReceipt.initiator_first_send_responder_outcomes' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleResponderFirstReceipt.initiator_first_send_responder_outcomes

/--
info: 'Tacenta.UnitLifecycleResponderFirstReceipt.modelFirstReceipt_dhCodec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleResponderFirstReceipt.modelFirstReceipt_dhCodec

/--
info: 'Tacenta.UnitLifecycleResponderFirstReceipt.modelFirstReceipt_dhAgree' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleResponderFirstReceipt.modelFirstReceipt_dhAgree

/--
info: 'Tacenta.UnitLifecycleResponderFirstReceipt.modelFirstReceipt_symmetric' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleResponderFirstReceipt.modelFirstReceipt_symmetric

/--
info: 'Tacenta.UnitLifecycleResponderFirstReceipt.modelFirstReceipt_aeadOpen' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleResponderFirstReceipt.modelFirstReceipt_aeadOpen

/--
info: 'Tacenta.UnitLifecycleResponderFirstReceipt.modelFirstReceipt_aeadSeal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleResponderFirstReceipt.modelFirstReceipt_aeadSeal

/--
info: 'Tacenta.UnitLifecycleResponderFirstReceipt.modelFirstReceipt_aeadRoundTrip' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleResponderFirstReceipt.modelFirstReceipt_aeadRoundTrip

/--
info: 'Tacenta.UnitLifecycleResponderFirstReceipt.modelFirstReceipt_contributory' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleResponderFirstReceipt.modelFirstReceipt_contributory

/--
info: 'Tacenta.UnitLifecycleResponderFirstReceipt.first_receipt_laws_model' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.rand_core_1.error.Error,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.Pair.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 tacenta_session_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleResponderFirstReceipt.first_receipt_laws_model

/--
info: 'Tacenta.UnitLifecycleResponderFirstReceipt.first_send_receive_reachable' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleResponderFirstReceipt.first_send_receive_reachable

set_option pp.deepTerms true
set_option pp.proofs.withType true

/--
info: Tacenta.UnitLifecycleResponderFirstReceipt.first_send_key : ∀ (a4 peer rkA cksA prk k1 k2 : Model.State.Key),
  Model.Triple.sendDetailed (Tacenta.UnitLifecycleResponderFirstReceipt.firstSenderTriple a4 peer rkA cksA prk k1 k2) 0
      none =
    Except.ok
      (Tacenta.UnitLifecycleResponderFirstReceipt.senderAfterFirst a4 peer rkA cksA prk k1 k2,
        Tacenta.UnitLifecycleResponderFirstReceipt.firstHeader a4,
        Tacenta.UnitLifecycleResponderFirstReceipt.firstKey cksA k1)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderFirstReceipt.first_send_key

/--
info: Tacenta.UnitLifecycleResponderFirstReceipt.first_receive_key : ∀
  (b ec prk k1 k2 a4 d dSend newPub rkA cksA : Model.State.Key),
  Model.State.kdfRk ec d Model.State.LabelSet.tacenta = (rkA, cksA) →
    Model.Triple.receiveDetailed (Tacenta.UnitLifecycleResponderFirstReceipt.firstReceiverTriple b ec prk k1 k2)
        (Tacenta.UnitLifecycleResponderFirstReceipt.firstHeader a4) d dSend newPub none =
      Except.ok
        (Tacenta.UnitLifecycleResponderFirstReceipt.receiverAfterFirst ec prk k1 k2 a4 d dSend newPub,
          Tacenta.UnitLifecycleResponderFirstReceipt.firstKey cksA k1)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderFirstReceipt.first_receive_key

/--
info: Tacenta.UnitLifecycleResponderFirstReceipt.first_receive_with_eviction : ∀
  (b ec prk k1 k2 a4 d dSend newPub rkA cksA : Model.State.Key) (composite : Model.CompositeHeader.Composite),
  Model.State.kdfRk ec d Model.State.LabelSet.tacenta = (rkA, cksA) →
    Model.Lifecycle.receiveWithEviction (Tacenta.UnitLifecycleResponderFirstReceipt.firstReceiverTriple b ec prk k1 k2)
        composite (Tacenta.UnitLifecycleResponderFirstReceipt.firstHeader a4) d dSend newPub none =
      Except.ok
        (Tacenta.UnitLifecycleResponderFirstReceipt.receiverAfterFirst ec prk k1 k2 a4 d dSend newPub,
          Tacenta.UnitLifecycleResponderFirstReceipt.firstKey cksA k1)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderFirstReceipt.first_receive_with_eviction

/--
info: Tacenta.UnitLifecycleResponderFirstReceipt.readBe64_be64_kernel : ∀ (n : UInt64) (rest : List UInt8),
  Model.CompositeHeader.readBe64 (Model.CompositeHeader.be64 n ++ rest) = some (n, rest)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderFirstReceipt.readBe64_be64_kernel

/--
info: Tacenta.UnitLifecycleResponderFirstReceipt.readBe16_be16_kernel : ∀ (n : UInt16) (rest : List UInt8),
  Model.CompositeHeader.readBe16 (Model.CompositeHeader.be16 n ++ rest) = some (n, rest)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderFirstReceipt.readBe16_be16_kernel

/--
info: Tacenta.UnitLifecycleResponderFirstReceipt.decode_encodeMessage : ∀ (h : Model.CompositeHeader.Composite)
  (ct : List UInt8),
  List.length h.dh = 32 →
    Model.Messages.checkKey h.dh = some () →
      (∀ (c : Model.CompositeHeader.Codeword), h.agChunk = some c → c.data.length = 32) →
        Model.CompositeHeader.decode (Model.CompositeHeader.encodeMessage h ct) = some (h, ct)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderFirstReceipt.decode_encodeMessage

/--
info: Tacenta.UnitLifecycleResponderFirstReceipt.first_frame_model_outcomes : ∀ (viewA viewB : Model.Lifecycle.CodewordView)
  (oracleA oracleB : Model.Lifecycle.Oracle) (mA mB : Model.Lifecycle.Session)
  (a4 peer b rkA cksA prk k1 k2 ec : Model.State.Key) (secret pt : Model.Lifecycle.Bytes) (chunk : Model.Braid.Chunk)
  (d : Model.State.Key),
  mA.triple = Tacenta.UnitLifecycleResponderFirstReceipt.firstSenderTriple a4 peer rkA cksA prk k1 k2 →
    mB.triple = Tacenta.UnitLifecycleResponderFirstReceipt.firstReceiverTriple b ec prk k1 k2 →
      Model.State.kdfRk ec d Model.State.LabelSet.tacenta = (rkA, cksA) →
        mB.braid = Model.Braid.initBob secret →
          mB.identityAd = mA.identityAd →
            List.length a4 = 32 →
              Model.Messages.checkKey a4 = some () →
                (viewA.send mA.braid chunk).data.length = 32 →
                  oracleB.dhAgree mB.ratchetPrivate a4 = some d →
                    oracleB.draws = [] ∧
                        Model.Lifecycle.decryptRatchet viewB oracleB mB
                            (Tacenta.UnitLifecycleEstablishedEncrypt.firstFrame viewA oracleA mA pt
                              (Tacenta.UnitLifecycleResponderFirstReceipt.firstKey cksA k1) chunk) =
                          { session := mB, result := Except.error Model.Lifecycle.Refusal.ceiling, oracle := oracleB } ∨
                      (∃ c rest,
                          oracleB.draws = c :: rest ∧
                            oracleB.dhAgree c a4 = none ∧
                              Model.Lifecycle.decryptRatchet viewB oracleB mB
                                  (Tacenta.UnitLifecycleEstablishedEncrypt.firstFrame viewA oracleA mA pt
                                    (Tacenta.UnitLifecycleResponderFirstReceipt.firstKey cksA k1) chunk) =
                                { session := mB,
                                  result :=
                                    Except.error
                                      (Model.Lifecycle.Refusal.handshake
                                        Model.Lifecycle.HandshakeRefusal.nonContributoryAgreement),
                                  oracle :=
                                    { draws := rest, braidKem := oracleB.braidKem, dhPublic := oracleB.dhPublic,
                                      dhAgree := oracleB.dhAgree, identityValid := oracleB.identityValid,
                                      aeadSeal := oracleB.aeadSeal, aeadOpen := oracleB.aeadOpen,
                                      kemValid := oracleB.kemValid, kemEncaps := oracleB.kemEncaps,
                                      kemDecaps := oracleB.kemDecaps, sigVerify := oracleB.sigVerify,
                                      sigSign := oracleB.sigSign } }) ∨
                        (∃ c rest dSend,
                            oracleB.draws = c :: rest ∧
                              oracleB.dhAgree c a4 = some dSend ∧
                                Tacenta.UnitLifecycleResponderFirstReceipt.firstOpen oracleA oracleB
                                      (Tacenta.UnitLifecycleResponderFirstReceipt.firstKey cksA k1) pt
                                      (Tacenta.UnitLifecycleResponderFirstReceipt.firstAd viewA mA chunk) =
                                    none ∧
                                  Model.Lifecycle.decryptRatchet viewB oracleB mB
                                      (Tacenta.UnitLifecycleEstablishedEncrypt.firstFrame viewA oracleA mA pt
                                        (Tacenta.UnitLifecycleResponderFirstReceipt.firstKey cksA k1) chunk) =
                                    { session := mB, result := Except.error Model.Lifecycle.Refusal.aead,
                                      oracle :=
                                        { draws := rest, braidKem := oracleB.braidKem, dhPublic := oracleB.dhPublic,
                                          dhAgree := oracleB.dhAgree, identityValid := oracleB.identityValid,
                                          aeadSeal := oracleB.aeadSeal, aeadOpen := oracleB.aeadOpen,
                                          kemValid := oracleB.kemValid, kemEncaps := oracleB.kemEncaps,
                                          kemDecaps := oracleB.kemDecaps, sigVerify := oracleB.sigVerify,
                                          sigSign := oracleB.sigSign } }) ∨
                          ∃ c rest dSend x,
                            oracleB.draws = c :: rest ∧
                              oracleB.dhAgree c a4 = some dSend ∧
                                Tacenta.UnitLifecycleResponderFirstReceipt.firstOpen oracleA oracleB
                                      (Tacenta.UnitLifecycleResponderFirstReceipt.firstKey cksA k1) pt
                                      (Tacenta.UnitLifecycleResponderFirstReceipt.firstAd viewA mA chunk) =
                                    some x ∧
                                  Model.Lifecycle.decryptRatchet viewB oracleB mB
                                      (Tacenta.UnitLifecycleEstablishedEncrypt.firstFrame viewA oracleA mA pt
                                        (Tacenta.UnitLifecycleResponderFirstReceipt.firstKey cksA k1) chunk) =
                                    {
                                      session :=
                                        Tacenta.UnitLifecycleResponderFirstReceipt.firstReceiptSession mB secret
                                          (viewB.receive mB.braid (viewA.send mA.braid chunk).index
                                            (viewA.send mA.braid chunk).data)
                                          ec prk k1 k2 a4 d dSend (oracleB.dhPublic c) c,
                                      result := Except.ok x,
                                      oracle :=
                                        { draws := rest, braidKem := oracleB.braidKem, dhPublic := oracleB.dhPublic,
                                          dhAgree := oracleB.dhAgree, identityValid := oracleB.identityValid,
                                          aeadSeal := oracleB.aeadSeal, aeadOpen := oracleB.aeadOpen,
                                          kemValid := oracleB.kemValid, kemEncaps := oracleB.kemEncaps,
                                          kemDecaps := oracleB.kemDecaps, sigVerify := oracleB.sigVerify,
                                          sigSign := oracleB.sigSign } }
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderFirstReceipt.first_frame_model_outcomes

/--
info: Tacenta.UnitLifecycleResponderFirstReceipt.aeadRoundTrip_is : Tacenta.UnitLifecycleResponderFirstReceipt.AeadRoundTrip ↔
  ∀ (k1 k2 : Aeneas.Std.Array Aeneas.Std.U8 32#usize) (iv : Aeneas.Std.Array Aeneas.Std.U8 16#usize)
    (pt ad : Aeneas.Std.Slice Aeneas.Std.U8) (ct : Aeneas.Std.alloc.vec.Vec Aeneas.Std.U8),
    (↑pt).length + 48 ≤ Aeneas.Std.Usize.max →
      tacenta_session_unit.tacenta_boundary.aead.encrypt k1 k2 iv pt ad = Aeneas.Std.Result.ok ct →
        ∃ v,
          tacenta_session_unit.tacenta_boundary.aead.decrypt k1 k2 iv ct.deref ad =
              Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok v) ∧
            ↑v = ↑pt
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderFirstReceipt.aeadRoundTrip_is

/--
info: Tacenta.UnitLifecycleResponderFirstReceipt.dhAgreeContributory_is : Tacenta.UnitLifecycleResponderFirstReceipt.DhAgreeContributory ↔
  ∀ (a b : tacenta_session_unit.tacenta_boundary.dh.PrivateKey)
    (pb : tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes),
    b.public_key = Aeneas.Std.Result.ok pb → ∃ x, a.agree pb = Aeneas.Std.Result.ok (some x)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderFirstReceipt.dhAgreeContributory_is

/--
info: Tacenta.UnitLifecycleResponderFirstReceipt.first_init_pair : ∀ (sk : Aeneas.Std.Slice Aeneas.Std.U8)
  (a4 a5 dh b rk cks prk c1 c2 : Aeneas.Std.Array Aeneas.Std.U8 32#usize)
  (t : tacenta_session_unit.tacenta_triple.State),
  tacenta_session_unit.tacenta_triple.State.init_sender sk a4 a5 dh
        tacenta_session_unit.tacenta_ratchet.LabelSet.Tacenta =
      Aeneas.Std.Result.ok (Tacenta.UnitLifecycleEstablishInitiatorShape.initiatorTriple a4 a5 rk cks prk c1 c2) →
    tacenta_session_unit.tacenta_triple.State.init_receiver sk b tacenta_session_unit.tacenta_ratchet.LabelSet.Tacenta =
        Aeneas.Std.Result.ok t →
      ∃ ec,
        tacenta_session_unit.tacenta_ratchet.kdf_rk ec dh tacenta_session_unit.tacenta_ratchet.LabelSet.Tacenta =
            Aeneas.Std.Result.ok (rk, cks) ∧
          t = Tacenta.UnitLifecycleEstablishResponder.responderTriple b ec prk c1 c2
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderFirstReceipt.first_init_pair

/--
info: @Tacenta.UnitLifecycleResponderFirstReceipt.established_triple_first : ∀ {R : Type}
  {rc : tacenta_session_unit.rand_core_1.RngCore R} {crc : tacenta_session_unit.rand_core_1.CryptoRng R}
  {our : tacenta_session_unit.lifecycle.Identity} {bundle : tacenta_session_unit.lifecycle.PublishedBundle}
  (dh : Tacenta.UnitLifecycleT3.DhView)
  (p : Tacenta.UnitLifecycleEstablishInitiatorShape.InitiatorOutputParts rc crc our bundle),
  (Tacenta.UnitLifecycleEstablishInitiatorShape.establishedModelOf dh p.session).triple =
    Tacenta.UnitLifecycleResponderFirstReceipt.firstSenderTriple (Tacenta.UnitLifecycleT3.arrayOf p.ratchetBytes)
      (Tacenta.UnitLifecycleT3.arrayOf p.peerRatchetBytes) (Tacenta.UnitLifecycleT3.arrayOf p.rootKey)
      (Tacenta.UnitLifecycleT3.arrayOf p.sendChain) (Tacenta.UnitLifecycleT3.arrayOf p.sparseRoot)
      (Tacenta.UnitLifecycleT3.arrayOf p.sparseSend) (Tacenta.UnitLifecycleT3.arrayOf p.sparseReceive)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderFirstReceipt.established_triple_first

/--
info: Tacenta.UnitLifecycleResponderFirstReceipt.responder_triple_first : ∀ (dh : Tacenta.UnitLifecycleT3.DhView)
  {ourB : tacenta_session_unit.lifecycle.Identity} {storeB : tacenta_session_unit.lifecycle.PrekeyStore}
  {msg : Aeneas.Std.Slice Aeneas.Std.U8}
  (p : Tacenta.UnitLifecycleEstablishResponder.ResponderPreparedParts ourB storeB msg)
  (ec prk c1 c2 : Aeneas.Std.Array Aeneas.Std.U8 32#usize),
  p.triple = Tacenta.UnitLifecycleEstablishResponder.responderTriple p.ratchetBytes ec prk c1 c2 →
    (Tacenta.UnitLifecycleEstablishResponder.responderModelOf dh p).triple =
      Tacenta.UnitLifecycleResponderFirstReceipt.firstReceiverTriple (Tacenta.UnitLifecycleT3.arrayOf p.ratchetBytes)
        (Tacenta.UnitLifecycleT3.arrayOf ec) (Tacenta.UnitLifecycleT3.arrayOf prk) (Tacenta.UnitLifecycleT3.arrayOf c1)
        (Tacenta.UnitLifecycleT3.arrayOf c2)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderFirstReceipt.responder_triple_first

/--
info: Tacenta.UnitLifecycleResponderFirstReceipt.first_kdf_model : Tacenta.SessionUnitT3.HkdfAgrees →
  Tacenta.SessionUnitT3.ZeroizingRoundTrips →
    ∀ {ec d rk cks : Aeneas.Std.Array Aeneas.Std.U8 32#usize},
      tacenta_session_unit.tacenta_ratchet.kdf_rk ec d tacenta_session_unit.tacenta_ratchet.LabelSet.Tacenta =
          Aeneas.Std.Result.ok (rk, cks) →
        Model.State.kdfRk (Tacenta.UnitLifecycleT3.arrayOf ec) (Tacenta.UnitLifecycleT3.arrayOf d)
            Model.State.LabelSet.tacenta =
          (Tacenta.UnitLifecycleT3.arrayOf rk, Tacenta.UnitLifecycleT3.arrayOf cks)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderFirstReceipt.first_kdf_model

/--
info: Tacenta.UnitLifecycleResponderFirstReceipt.zeroized_eq : Tacenta.SessionUnitBraidT1.ZeroizingArrayRoundTrip →
  ∀ {a b : Aeneas.Std.Array Aeneas.Std.U8 32#usize}
    {w : tacenta_session_unit.zeroize.Zeroizing (Aeneas.Std.Array Aeneas.Std.U8 32#usize)},
    tacenta_session_unit.zeroize.Zeroizing.new Tacenta.UnitLifecycleEstablishResponder.z32 a = Aeneas.Std.Result.ok w →
      tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref Tacenta.UnitLifecycleEstablishResponder.z32
            w =
          Aeneas.Std.Result.ok b →
        b = a
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderFirstReceipt.zeroized_eq

/--
info: @Tacenta.UnitLifecycleResponderFirstReceipt.parts_of_first_frame : ∀ {R : Type}
  {rc : tacenta_session_unit.rand_core_1.RngCore R} {crc : tacenta_session_unit.rand_core_1.CryptoRng R}
  {our : tacenta_session_unit.lifecycle.Identity} {bundle : tacenta_session_unit.lifecycle.PublishedBundle},
  Tacenta.SessionUnitBraidT1.ZeroizingArrayRoundTrip →
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
                      ∀ (ourB : tacenta_session_unit.lifecycle.Identity)
                        (storeB : tacenta_session_unit.lifecycle.PrekeyStore),
                        storeB.publish = Aeneas.Std.Result.ok bundle →
                          ourB.public = Aeneas.Std.Result.ok storeB.identity_public →
                            ∀ (p : Tacenta.UnitLifecycleEstablishResponder.ResponderPreparedParts ourB storeB msg),
                              p.decoded.kem_prekey_id = bundle.kem_prekey_id ∧
                                p.decoded.one_time_prekey_id = bundle.one_time_prekey_id ∧
                                  p.ratchetPrivate.public_key = Aeneas.Std.Result.ok bundle.bundle.signed_prekey ∧
                                    p.ourPublic = bundle.bundle.identity_key
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderFirstReceipt.parts_of_first_frame

/--
info: @Tacenta.UnitLifecycleResponderFirstReceipt.view_ratchet_public : ∀ {R : Type}
  {rc : tacenta_session_unit.rand_core_1.RngCore R} {crc : tacenta_session_unit.rand_core_1.CryptoRng R}
  {our : tacenta_session_unit.lifecycle.Identity} {bundle : tacenta_session_unit.lifecycle.PublishedBundle}
  {dh : Tacenta.UnitLifecycleT3.DhView},
  Tacenta.UnitLifecycleT3.DhCodecOf dh →
    ∀ (q : Tacenta.UnitLifecycleResponderFirstFrame.InitiatorSecretParts rc crc our bundle),
      dh.publicKey q.ratchetPublic = Tacenta.UnitLifecycleT3.arrayOf q.ratchetBytes
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderFirstReceipt.view_ratchet_public

/--
info: @Tacenta.UnitLifecycleResponderFirstReceipt.responder_first_agreement : ∀ {R : Type}
  {rc : tacenta_session_unit.rand_core_1.RngCore R} {crc : tacenta_session_unit.rand_core_1.CryptoRng R}
  {our : tacenta_session_unit.lifecycle.Identity} {bundle : tacenta_session_unit.lifecycle.PublishedBundle},
  Tacenta.UnitLifecycleResponderFirstFrame.DhAgreeSymmetric →
    ∀ {E : Type} {rcB : tacenta_session_unit.rand_core_1.RngCore E}
      {crcB : tacenta_session_unit.rand_core_1.CryptoRng E} {dh : Tacenta.UnitLifecycleT3.DhView},
      Tacenta.UnitLifecycleT3.DhCodecOf dh →
        ∀ {traceB : E → List Model.Lifecycle.Key} {oracleB : Model.Lifecycle.Oracle},
          Tacenta.UnitLifecycleDecryptRatchetT3.DecryptOracleOf rcB crcB dh traceB oracleB →
            ∀ (q : Tacenta.UnitLifecycleResponderFirstFrame.InitiatorSecretParts rc crc our bundle)
              (k : tacenta_session_unit.tacenta_boundary.dh.PrivateKey),
              k.public_key = Aeneas.Std.Result.ok bundle.bundle.signed_prekey →
                oracleB.dhAgree (dh.privateKey k) (Tacenta.UnitLifecycleT3.arrayOf q.ratchetBytes) =
                  some (Tacenta.UnitLifecycleT3.arrayOf q.dhOut)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderFirstReceipt.responder_first_agreement

/--
info: @Tacenta.UnitLifecycleResponderFirstReceipt.responder_candidate_agreement : ∀ {R : Type}
  {rc : tacenta_session_unit.rand_core_1.RngCore R} {crc : tacenta_session_unit.rand_core_1.CryptoRng R}
  {our : tacenta_session_unit.lifecycle.Identity} {bundle : tacenta_session_unit.lifecycle.PublishedBundle},
  Tacenta.UnitLifecycleResponderFirstReceipt.DhAgreeContributory →
    ∀ {E : Type} {rcB : tacenta_session_unit.rand_core_1.RngCore E}
      {crcB : tacenta_session_unit.rand_core_1.CryptoRng E} {dh : Tacenta.UnitLifecycleT3.DhView},
      Tacenta.UnitLifecycleT3.DhCodecOf dh →
        ∀ {traceB : E → List Model.Lifecycle.Key} {oracleB : Model.Lifecycle.Oracle},
          Tacenta.UnitLifecycleDecryptRatchetT3.DecryptOracleOf rcB crcB dh traceB oracleB →
            ∀ (q : Tacenta.UnitLifecycleResponderFirstFrame.InitiatorSecretParts rc crc our bundle) (rngB : E)
              (dB : Model.Lifecycle.Key) (restB : List Model.Lifecycle.Key),
              traceB rngB = dB :: restB →
                ∃ x, oracleB.dhAgree dB (Tacenta.UnitLifecycleT3.arrayOf q.ratchetBytes) = some x
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderFirstReceipt.responder_candidate_agreement

/--
info: @Tacenta.UnitLifecycleResponderFirstReceipt.first_identityAd_eq : ∀ {R : Type}
  {rc : tacenta_session_unit.rand_core_1.RngCore R} {crc : tacenta_session_unit.rand_core_1.CryptoRng R}
  {our : tacenta_session_unit.lifecycle.Identity} {bundle : tacenta_session_unit.lifecycle.PublishedBundle}
  (q : Tacenta.UnitLifecycleResponderFirstFrame.InitiatorSecretParts rc crc our bundle)
  {ourB : tacenta_session_unit.lifecycle.Identity} {storeB : tacenta_session_unit.lifecycle.PrekeyStore}
  {msg : Aeneas.Std.Slice Aeneas.Std.U8}
  (p : Tacenta.UnitLifecycleEstablishResponder.ResponderPreparedParts ourB storeB msg),
  p.peerIdentity = q.ourPublic → p.ourPublic = bundle.bundle.identity_key → p.identityAd = q.identityAd
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderFirstReceipt.first_identityAd_eq

/--
info: @Tacenta.UnitLifecycleResponderFirstReceipt.arrayOf_arrayOfBytes : ∀ {n : Aeneas.Std.Usize} (l : Model.Lifecycle.Bytes)
  (h : List.length l = ↑n),
  Tacenta.UnitLifecycleT3.arrayOf (Tacenta.UnitLifecycleResponderFirstReceipt.arrayOfBytes l h) = l
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderFirstReceipt.arrayOf_arrayOfBytes

/--
info: Tacenta.UnitLifecycleResponderFirstReceipt.aead_open_sealed : Tacenta.UnitLifecycleResponderFirstReceipt.AeadRoundTrip →
  ∀ {E : Type} {rcB : tacenta_session_unit.rand_core_1.RngCore E} {crcB : tacenta_session_unit.rand_core_1.CryptoRng E}
    {dh : Tacenta.UnitLifecycleT3.DhView} {traceB : E → List Model.Lifecycle.Key}
    {oracleA oracleB : Model.Lifecycle.Oracle},
    Tacenta.UnitOracleShape.AeadSealClause Tacenta.UnitSatisfiabilityJoint.Interp.real oracleA →
      Tacenta.UnitLifecycleDecryptRatchetT3.DecryptOracleOf rcB crcB dh traceB oracleB →
        ∀ (k1 k2 iv : Model.Lifecycle.Bytes),
          List.length k1 = 32 →
            List.length k2 = 32 →
              List.length iv = 16 →
                ∀ (pt : Aeneas.Std.Slice Aeneas.Std.U8),
                  (↑pt).length + 48 ≤ Aeneas.Std.Usize.max →
                    ∀ (ad : Model.Lifecycle.Bytes),
                      List.length ad ≤ Aeneas.Std.Usize.max →
                        oracleB.aeadOpen k1 k2 iv (oracleA.aeadSeal k1 k2 iv (Tacenta.UnitLifecycleT3.sliceOf pt) ad)
                            ad =
                          some (Tacenta.UnitLifecycleT3.sliceOf pt)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderFirstReceipt.aead_open_sealed

/--
info: @Tacenta.UnitLifecycleResponderFirstReceipt.attributedView_send : ∀ {view : Model.Lifecycle.CodewordView},
  Tacenta.UnitLifecycleT3.CodewordViewSendOf view →
    ∀ (idx : UInt16) (data : Model.Lifecycle.Bytes) (mc : Model.Braid.Chunk),
      Tacenta.UnitLifecycleT3.CodewordViewSendOf
        (Tacenta.UnitLifecycleResponderFirstReceipt.attributedView view idx data mc)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderFirstReceipt.attributedView_send

/--
info: Tacenta.UnitLifecycleResponderFirstReceipt.firstFrame_attributedView : ∀ (view : Model.Lifecycle.CodewordView)
  (idx : UInt16) (data : Model.Lifecycle.Bytes) (mc : Model.Braid.Chunk),
  Tacenta.UnitLifecycleEstablishedEncrypt.firstFrame
      (Tacenta.UnitLifecycleResponderFirstReceipt.attributedView view idx data mc) =
    Tacenta.UnitLifecycleEstablishedEncrypt.firstFrame view
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderFirstReceipt.firstFrame_attributedView

/--
info: @Tacenta.UnitLifecycleResponderFirstReceipt.first_receipt_run_inputs : ∀ {E : Type}
  (view : Model.Lifecycle.CodewordView) (oracleA oracleB : Model.Lifecycle.Oracle)
  (traceB : E → List Model.Lifecycle.Key) (dh : Tacenta.UnitLifecycleT3.DhView)
  {ourB : tacenta_session_unit.lifecycle.Identity} {storeB : tacenta_session_unit.lifecycle.PrekeyStore}
  {msg : Aeneas.Std.Slice Aeneas.Std.U8}
  (p : Tacenta.UnitLifecycleEstablishResponder.ResponderPreparedParts ourB storeB msg) (mA : Model.Lifecycle.Session)
  (pt : Model.Lifecycle.Bytes) (mk : Model.Lifecycle.Key) (src : Model.Lifecycle.Bytes),
  List.length src = Model.Braid.headerSize + Model.Braid.macSize →
    ∀ (c : tacenta_session_unit.tacenta_erasure.Chunk),
      Tacenta.SessionUnitBraidT3.CodewordOf src c →
        view.send mA.braid (Tacenta.UnitLifecycleT3.modelChunkOf src c) = Tacenta.UnitLifecycleT3.modelCodewordOf c →
          List.length mA.triple.classical.dhsPub = 32 →
            Model.Messages.checkKey mA.triple.classical.dhsPub = some () →
              Tacenta.UnitLifecycleT3.sliceOf p.message =
                  Tacenta.UnitLifecycleEstablishedEncrypt.firstFrame view oracleA mA pt mk
                    (Tacenta.UnitLifecycleT3.modelChunkOf src c) →
                ∀ (rngB : E) (dB : Model.Lifecycle.Key) (restB : List Model.Lifecycle.Key),
                  traceB rngB = dB :: restB →
                    Tacenta.UnitLifecycleDecryptRunBounds.DecryptRatchetRunInputs
                      (Tacenta.UnitLifecycleResponderFirstReceipt.attributedView view
                        (Tacenta.UnitLifecycleT3.modelCodewordOf c).index
                        (Tacenta.UnitLifecycleT3.modelCodewordOf c).data (Tacenta.UnitLifecycleT3.modelChunkOf src c))
                      oracleB traceB p.session (Tacenta.UnitLifecycleEstablishResponder.responderModelOf dh p) p.message
                      rngB
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderFirstReceipt.first_receipt_run_inputs

/--
info: @Tacenta.UnitLifecycleResponderFirstReceipt.firstAd_length_le : ∀ {R : Type}
  {rc : tacenta_session_unit.rand_core_1.RngCore R} {crc : tacenta_session_unit.rand_core_1.CryptoRng R}
  {our : tacenta_session_unit.lifecycle.Identity} {bundle : tacenta_session_unit.lifecycle.PublishedBundle},
  Tacenta.UnitLifecycleT1.DhCodecTotal →
    ∀ (dh : Tacenta.UnitLifecycleT3.DhView) (view : Model.Lifecycle.CodewordView)
      (q : Tacenta.UnitLifecycleEstablishInitiatorShape.InitiatorOutputParts rc crc our bundle)
      (src : Model.Lifecycle.Bytes) (c : tacenta_session_unit.tacenta_erasure.Chunk),
      view.send (Tacenta.UnitLifecycleEstablishInitiatorShape.establishedModelOf dh q.session).braid
            (Tacenta.UnitLifecycleT3.modelChunkOf src c) =
          Tacenta.UnitLifecycleT3.modelCodewordOf c →
        List.length
            (Tacenta.UnitLifecycleResponderFirstReceipt.firstAd view
              (Tacenta.UnitLifecycleEstablishInitiatorShape.establishedModelOf dh q.session)
              (Tacenta.UnitLifecycleT3.modelChunkOf src c)) ≤
          Aeneas.Std.Usize.max
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderFirstReceipt.firstAd_length_le

/--
info: @Tacenta.UnitLifecycleResponderFirstReceipt.responder_first_frame_inner_outcomes : ∀ {R : Type}
  {rc : tacenta_session_unit.rand_core_1.RngCore R} {crc : tacenta_session_unit.rand_core_1.CryptoRng R}
  {our : tacenta_session_unit.lifecycle.Identity} {bundle : tacenta_session_unit.lifecycle.PublishedBundle}
  [Tacenta.SessionUnitT1.DerivedKeysModel] {E : Type} (rcB : tacenta_session_unit.rand_core_1.RngCore E)
  (crcB : tacenta_session_unit.rand_core_1.CryptoRng E)
  (contracts : Tacenta.UnitLifecycleT1.EstablishResponderContracts rcB),
  Tacenta.UnitLifecycleEstablishInitiatorShape.DhPublicValid →
    Tacenta.UnitLifecycleResponderFirstFrame.DhAgreeSymmetric →
      Tacenta.UnitHeadroomInvariant.OptionEqU64Shape
          @tacenta_session_unit.core.option.Option.Insts.CoreCmpPartialEqOption.eq →
        ∀ {dh : Tacenta.UnitLifecycleT3.DhView},
          Tacenta.UnitLifecycleT3.DhCodecOf dh →
            ∀ (view : Model.Lifecycle.CodewordView) (oracleA : Model.Lifecycle.Oracle)
              (traceB : E → List Model.Lifecycle.Key) (oracleB : Model.Lifecycle.Oracle),
              Tacenta.UnitLifecycleDecryptRatchetT3.DecryptOracleOf rcB crcB dh traceB oracleB →
                Tacenta.UnitLifecycleDecryptRatchetT3.DecryptRatchetAgreements oracleB.braidKem →
                  ∀ (q : Tacenta.UnitLifecycleResponderFirstFrame.InitiatorSecretParts rc crc our bundle)
                    (plaintext : Aeneas.Std.Slice Aeneas.Std.U8) (src : Model.Lifecycle.Bytes),
                    List.length src = Model.Braid.headerSize + Model.Braid.macSize →
                      ∀ (c : tacenta_session_unit.tacenta_erasure.Chunk),
                        Tacenta.SessionUnitBraidT3.CodewordOf src c →
                          view.send (Tacenta.UnitLifecycleEstablishInitiatorShape.establishedModelOf dh q.session).braid
                                (Tacenta.UnitLifecycleT3.modelChunkOf src c) =
                              Tacenta.UnitLifecycleT3.modelCodewordOf c →
                            ∀ {ourB : tacenta_session_unit.lifecycle.Identity}
                              {storeB : tacenta_session_unit.lifecycle.PrekeyStore}
                              {msg : Aeneas.Std.Slice Aeneas.Std.U8}
                              (p : Tacenta.UnitLifecycleEstablishResponder.ResponderPreparedParts ourB storeB msg),
                              p.tripleSecret = q.sharedSlice →
                                p.peerIdentity = q.ourPublic →
                                  p.ratchetPrivate.public_key = Aeneas.Std.Result.ok bundle.bundle.signed_prekey →
                                    p.ourPublic = bundle.bundle.identity_key →
                                      Tacenta.UnitLifecycleT3.sliceOf p.message =
                                          Tacenta.UnitLifecycleEstablishedEncrypt.firstFrame view oracleA
                                            (Tacenta.UnitLifecycleEstablishInitiatorShape.establishedModelOf dh
                                              q.session)
                                            (Tacenta.UnitLifecycleT3.sliceOf plaintext)
                                            (Tacenta.UnitLifecycleResponderFirstReceipt.firstKey
                                              (Tacenta.UnitLifecycleT3.arrayOf q.sendChain)
                                              (Tacenta.UnitLifecycleT3.arrayOf q.sparseSend))
                                            (Tacenta.UnitLifecycleT3.modelChunkOf src c) →
                                        ∀ (rngB : E),
                                          traceB rngB = oracleB.draws →
                                            ∀ (dB : Model.Lifecycle.Key) (restB : List Model.Lifecycle.Key),
                                              traceB rngB = dB :: restB →
                                                ∃ ec inner,
                                                  tacenta_session_unit.tacenta_ratchet.kdf_rk ec q.dhOutBytes
                                                        tacenta_session_unit.tacenta_ratchet.LabelSet.Tacenta =
                                                      Aeneas.Std.Result.ok (q.rootKey, q.sendChain) ∧
                                                    tacenta_session_unit.lifecycle.Session.decrypt_ratchet rcB crcB
                                                          p.session p.message rngB =
                                                        Aeneas.Std.Result.ok inner ∧
                                                      traceB inner.2.2 = restB ∧
                                                        (inner.1 =
                                                              Aeneas.Std.core.result.Result.Err
                                                                (tacenta_session_unit.lifecycle.Error.Handshake
                                                                  tacenta_session_unit.SessionError.NonContributoryAgreement) ∧
                                                            oracleB.dhAgree dB
                                                                (Tacenta.UnitLifecycleT3.arrayOf q.ratchetBytes) =
                                                              none ∨
                                                          (inner.1 =
                                                                Aeneas.Std.core.result.Result.Err
                                                                  tacenta_session_unit.lifecycle.Error.Aead ∧
                                                              ∃ dSend,
                                                                oracleB.dhAgree dB
                                                                      (Tacenta.UnitLifecycleT3.arrayOf q.ratchetBytes) =
                                                                    some dSend ∧
                                                                  Tacenta.UnitLifecycleResponderFirstReceipt.firstOpen
                                                                      oracleA oracleB
                                                                      (Tacenta.UnitLifecycleResponderFirstReceipt.firstKey
                                                                        (Tacenta.UnitLifecycleT3.arrayOf q.sendChain)
                                                                        (Tacenta.UnitLifecycleT3.arrayOf q.sparseSend))
                                                                      (Tacenta.UnitLifecycleT3.sliceOf plaintext)
                                                                      (Tacenta.UnitLifecycleResponderFirstReceipt.firstAd
                                                                        view
                                                                        (Tacenta.UnitLifecycleEstablishInitiatorShape.establishedModelOf
                                                                          dh q.session)
                                                                        (Tacenta.UnitLifecycleT3.modelChunkOf src c)) =
                                                                    none) ∨
                                                            ∃ ptB dSend x,
                                                              inner.1 = Aeneas.Std.core.result.Result.Ok ptB ∧
                                                                oracleB.dhAgree dB
                                                                      (Tacenta.UnitLifecycleT3.arrayOf q.ratchetBytes) =
                                                                    some dSend ∧
                                                                  Tacenta.UnitLifecycleResponderFirstReceipt.firstOpen
                                                                        oracleA oracleB
                                                                        (Tacenta.UnitLifecycleResponderFirstReceipt.firstKey
                                                                          (Tacenta.UnitLifecycleT3.arrayOf q.sendChain)
                                                                          (Tacenta.UnitLifecycleT3.arrayOf
                                                                            q.sparseSend))
                                                                        (Tacenta.UnitLifecycleT3.sliceOf plaintext)
                                                                        (Tacenta.UnitLifecycleResponderFirstReceipt.firstAd
                                                                          view
                                                                          (Tacenta.UnitLifecycleEstablishInitiatorShape.establishedModelOf
                                                                            dh q.session)
                                                                          (Tacenta.UnitLifecycleT3.modelChunkOf src
                                                                            c)) =
                                                                      some x ∧
                                                                    Tacenta.UnitLifecycleT3.vecOf ptB = x ∧
                                                                      Tacenta.UnitLifecycleT3.SessionRefines dh
                                                                        oracleB.braidKem inner.2.1
                                                                        (Tacenta.UnitLifecycleResponderFirstReceipt.firstReceiptSession
                                                                          (Tacenta.UnitLifecycleEstablishResponder.responderModelOf
                                                                            dh p)
                                                                          (Tacenta.UnitLifecycleT3.sliceOf
                                                                            p.braidSecret)
                                                                          (Tacenta.UnitLifecycleT3.modelChunkOf src c)
                                                                          (Tacenta.UnitLifecycleT3.arrayOf ec)
                                                                          (Tacenta.UnitLifecycleT3.arrayOf q.sparseRoot)
                                                                          (Tacenta.UnitLifecycleT3.arrayOf q.sparseSend)
                                                                          (Tacenta.UnitLifecycleT3.arrayOf
                                                                            q.sparseReceive)
                                                                          (Tacenta.UnitLifecycleT3.arrayOf
                                                                            q.ratchetBytes)
                                                                          (Tacenta.UnitLifecycleT3.arrayOf q.dhOut)
                                                                          dSend (oracleB.dhPublic dB) dB))
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderFirstReceipt.responder_first_frame_inner_outcomes

/--
info: @Tacenta.UnitLifecycleResponderFirstReceipt.responder_first_frame_inner_succeeds : ∀ {R : Type}
  {rc : tacenta_session_unit.rand_core_1.RngCore R} {crc : tacenta_session_unit.rand_core_1.CryptoRng R}
  {our : tacenta_session_unit.lifecycle.Identity} {bundle : tacenta_session_unit.lifecycle.PublishedBundle}
  [Tacenta.SessionUnitT1.DerivedKeysModel] {E : Type} (rcB : tacenta_session_unit.rand_core_1.RngCore E)
  (crcB : tacenta_session_unit.rand_core_1.CryptoRng E)
  (contracts : Tacenta.UnitLifecycleT1.EstablishResponderContracts rcB),
  Tacenta.UnitLifecycleEstablishInitiatorShape.DhPublicValid →
    Tacenta.UnitLifecycleResponderFirstFrame.DhAgreeSymmetric →
      Tacenta.UnitLifecycleResponderFirstReceipt.DhAgreeContributory →
        Tacenta.UnitLifecycleResponderFirstReceipt.AeadRoundTrip →
          Tacenta.UnitHeadroomInvariant.OptionEqU64Shape
              @tacenta_session_unit.core.option.Option.Insts.CoreCmpPartialEqOption.eq →
            ∀ {dh : Tacenta.UnitLifecycleT3.DhView},
              Tacenta.UnitLifecycleT3.DhCodecOf dh →
                ∀ (view : Model.Lifecycle.CodewordView) (oracleA : Model.Lifecycle.Oracle),
                  Tacenta.UnitOracleShape.AeadSealClause Tacenta.UnitSatisfiabilityJoint.Interp.real oracleA →
                    ∀ (traceB : E → List Model.Lifecycle.Key) (oracleB : Model.Lifecycle.Oracle),
                      Tacenta.UnitLifecycleDecryptRatchetT3.DecryptOracleOf rcB crcB dh traceB oracleB →
                        Tacenta.UnitLifecycleDecryptRatchetT3.DecryptRatchetAgreements oracleB.braidKem →
                          ∀ (q : Tacenta.UnitLifecycleResponderFirstFrame.InitiatorSecretParts rc crc our bundle)
                            (plaintext : Aeneas.Std.Slice Aeneas.Std.U8),
                            (↑plaintext).length + 48 ≤ Aeneas.Std.Usize.max →
                              ∀ (src : Model.Lifecycle.Bytes),
                                List.length src = Model.Braid.headerSize + Model.Braid.macSize →
                                  ∀ (c : tacenta_session_unit.tacenta_erasure.Chunk),
                                    Tacenta.SessionUnitBraidT3.CodewordOf src c →
                                      view.send
                                            (Tacenta.UnitLifecycleEstablishInitiatorShape.establishedModelOf dh
                                                q.session).braid
                                            (Tacenta.UnitLifecycleT3.modelChunkOf src c) =
                                          Tacenta.UnitLifecycleT3.modelCodewordOf c →
                                        ∀ {ourB : tacenta_session_unit.lifecycle.Identity}
                                          {storeB : tacenta_session_unit.lifecycle.PrekeyStore}
                                          {msg : Aeneas.Std.Slice Aeneas.Std.U8}
                                          (p :
                                            Tacenta.UnitLifecycleEstablishResponder.ResponderPreparedParts ourB storeB
                                              msg),
                                          p.tripleSecret = q.sharedSlice →
                                            p.peerIdentity = q.ourPublic →
                                              p.ratchetPrivate.public_key =
                                                  Aeneas.Std.Result.ok bundle.bundle.signed_prekey →
                                                p.ourPublic = bundle.bundle.identity_key →
                                                  Tacenta.UnitLifecycleT3.sliceOf p.message =
                                                      Tacenta.UnitLifecycleEstablishedEncrypt.firstFrame view oracleA
                                                        (Tacenta.UnitLifecycleEstablishInitiatorShape.establishedModelOf
                                                          dh q.session)
                                                        (Tacenta.UnitLifecycleT3.sliceOf plaintext)
                                                        (Tacenta.UnitLifecycleResponderFirstReceipt.firstKey
                                                          (Tacenta.UnitLifecycleT3.arrayOf q.sendChain)
                                                          (Tacenta.UnitLifecycleT3.arrayOf q.sparseSend))
                                                        (Tacenta.UnitLifecycleT3.modelChunkOf src c) →
                                                    ∀ (rngB : E),
                                                      traceB rngB = oracleB.draws →
                                                        ∀ (dB : Model.Lifecycle.Key) (restB : List Model.Lifecycle.Key),
                                                          traceB rngB = dB :: restB →
                                                            ∃ ec dSend ptB sB' rngB',
                                                              tacenta_session_unit.tacenta_ratchet.kdf_rk ec
                                                                    q.dhOutBytes
                                                                    tacenta_session_unit.tacenta_ratchet.LabelSet.Tacenta =
                                                                  Aeneas.Std.Result.ok (q.rootKey, q.sendChain) ∧
                                                                oracleB.dhAgree dB
                                                                      (Tacenta.UnitLifecycleT3.arrayOf q.ratchetBytes) =
                                                                    some dSend ∧
                                                                  tacenta_session_unit.lifecycle.Session.decrypt_ratchet
                                                                        rcB crcB p.session p.message rngB =
                                                                      Aeneas.Std.Result.ok
                                                                        (Aeneas.Std.core.result.Result.Ok ptB, sB',
                                                                          rngB') ∧
                                                                    ↑ptB = ↑plaintext ∧
                                                                      traceB rngB' = restB ∧
                                                                        Tacenta.UnitLifecycleT3.SessionRefines dh
                                                                          oracleB.braidKem sB'
                                                                          (Tacenta.UnitLifecycleResponderFirstReceipt.firstReceiptSession
                                                                            (Tacenta.UnitLifecycleEstablishResponder.responderModelOf
                                                                              dh p)
                                                                            (Tacenta.UnitLifecycleT3.sliceOf
                                                                              p.braidSecret)
                                                                            (Tacenta.UnitLifecycleT3.modelChunkOf src c)
                                                                            (Tacenta.UnitLifecycleT3.arrayOf ec)
                                                                            (Tacenta.UnitLifecycleT3.arrayOf
                                                                              q.sparseRoot)
                                                                            (Tacenta.UnitLifecycleT3.arrayOf
                                                                              q.sparseSend)
                                                                            (Tacenta.UnitLifecycleT3.arrayOf
                                                                              q.sparseReceive)
                                                                            (Tacenta.UnitLifecycleT3.arrayOf
                                                                              q.ratchetBytes)
                                                                            (Tacenta.UnitLifecycleT3.arrayOf q.dhOut)
                                                                            dSend (oracleB.dhPublic dB) dB)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderFirstReceipt.responder_first_frame_inner_succeeds

/--
info: @Tacenta.UnitLifecycleResponderFirstReceipt.establish_responder_commit_of_inner : ∀ {E : Type}
  (rcB : tacenta_session_unit.rand_core_1.RngCore E) (crcB : tacenta_session_unit.rand_core_1.CryptoRng E)
  {ourB : tacenta_session_unit.lifecycle.Identity} {storeB : tacenta_session_unit.lifecycle.PrekeyStore}
  {msg : Aeneas.Std.Slice Aeneas.Std.U8}
  (p : Tacenta.UnitLifecycleEstablishResponder.ResponderPreparedParts ourB storeB msg) (rngB : E)
  (ptB : Aeneas.Std.alloc.vec.Vec Aeneas.Std.U8) (sB' : tacenta_session_unit.lifecycle.Session) (rngB' : E),
  tacenta_session_unit.lifecycle.Session.decrypt_ratchet rcB crcB p.session p.message rngB =
      Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok ptB, sB', rngB') →
    ∀
      (out :
        Aeneas.Std.core.result.Result (tacenta_session_unit.lifecycle.Session × Aeneas.Std.alloc.vec.Vec Aeneas.Std.U8)
            tacenta_session_unit.lifecycle.Error ×
          tacenta_session_unit.lifecycle.PrekeyStore × E),
      tacenta_session_unit.lifecycle.establish_responder rcB crcB ourB storeB msg rngB = Aeneas.Std.Result.ok out →
        ∃ storeB',
          Tacenta.UnitLifecycleEstablishResponder.ResponderCommit storeB p.decoded.kem_prekey_id
              p.decoded.one_time_prekey_id p.lastResort p.replay storeB' ∧
            out = (Aeneas.Std.core.result.Result.Ok (sB', ptB), storeB', rngB')
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderFirstReceipt.establish_responder_commit_of_inner

/--
info: @Tacenta.UnitLifecycleResponderFirstReceipt.establish_responder_refused_of_inner : ∀ {E : Type}
  (rcB : tacenta_session_unit.rand_core_1.RngCore E) (crcB : tacenta_session_unit.rand_core_1.CryptoRng E)
  {ourB : tacenta_session_unit.lifecycle.Identity} {storeB : tacenta_session_unit.lifecycle.PrekeyStore}
  {msg : Aeneas.Std.Slice Aeneas.Std.U8}
  (p : Tacenta.UnitLifecycleEstablishResponder.ResponderPreparedParts ourB storeB msg) (rngB : E)
  (e : tacenta_session_unit.lifecycle.Error) (sB' : tacenta_session_unit.lifecycle.Session) (rngB' : E),
  tacenta_session_unit.lifecycle.Session.decrypt_ratchet rcB crcB p.session p.message rngB =
      Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Err e, sB', rngB') →
    tacenta_session_unit.lifecycle.establish_responder rcB crcB ourB storeB msg rngB =
      Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Err e, storeB, rngB')
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderFirstReceipt.establish_responder_refused_of_inner

/--
info: @Tacenta.UnitLifecycleResponderFirstReceipt.responder_first_frame_outcomes : ∀ {R : Type}
  {rc : tacenta_session_unit.rand_core_1.RngCore R} {crc : tacenta_session_unit.rand_core_1.CryptoRng R}
  {our : tacenta_session_unit.lifecycle.Identity} {bundle : tacenta_session_unit.lifecycle.PublishedBundle}
  [Tacenta.SessionUnitT1.DerivedKeysModel] {E : Type} (rcB : tacenta_session_unit.rand_core_1.RngCore E)
  (crcB : tacenta_session_unit.rand_core_1.CryptoRng E)
  (contracts : Tacenta.UnitLifecycleT1.EstablishResponderContracts rcB),
  Tacenta.UnitLifecycleEstablishInitiatorShape.DhPublicValid →
    Tacenta.UnitLifecycleResponderFirstFrame.DhAgreeSymmetric →
      Tacenta.UnitLifecycleSessionCodec.DhPublicBytesRoundTrip →
        Tacenta.UnitLifecycleEstablishInitiatorShape.KemCiphertextLenOf →
          Tacenta.UnitLifecycleRestoredSession.KemCiphertextLenBound →
            Tacenta.UnitHeadroomInvariant.OptionEqU64Shape
                @tacenta_session_unit.core.option.Option.Insts.CoreCmpPartialEqOption.eq →
              ∀ {dh : Tacenta.UnitLifecycleT3.DhView},
                Tacenta.UnitLifecycleT3.DhCodecOf dh →
                  ∀ (view : Model.Lifecycle.CodewordView) (oracleA : Model.Lifecycle.Oracle)
                    (traceB : E → List Model.Lifecycle.Key) (oracleB : Model.Lifecycle.Oracle),
                    Tacenta.UnitLifecycleDecryptRatchetT3.DecryptOracleOf rcB crcB dh traceB oracleB →
                      Tacenta.UnitLifecycleDecryptRatchetT3.DecryptRatchetAgreements oracleB.braidKem →
                        ∀ (q : Tacenta.UnitLifecycleResponderFirstFrame.InitiatorSecretParts rc crc our bundle)
                          (pending : Model.Lifecycle.PendingInitial),
                          (Tacenta.UnitLifecycleEstablishInitiatorShape.establishedModelOf dh
                                  q.session).pendingInitial =
                              some pending →
                            ∀ (plaintext : Aeneas.Std.Slice Aeneas.Std.U8) (src : Model.Lifecycle.Bytes),
                              List.length src = Model.Braid.headerSize + Model.Braid.macSize →
                                ∀ (c : tacenta_session_unit.tacenta_erasure.Chunk),
                                  Tacenta.SessionUnitBraidT3.CodewordOf src c →
                                    view.send
                                          (Tacenta.UnitLifecycleEstablishInitiatorShape.establishedModelOf dh
                                              q.session).braid
                                          (Tacenta.UnitLifecycleT3.modelChunkOf src c) =
                                        Tacenta.UnitLifecycleT3.modelCodewordOf c →
                                      ∀ (msg : Aeneas.Std.Slice Aeneas.Std.U8),
                                        Tacenta.UnitLifecycleT3.sliceOf msg =
                                            Tacenta.UnitLifecycleEstablishedEncrypt.initialWire
                                              (Tacenta.UnitLifecycleEstablishInitiatorShape.establishedModelOf dh
                                                q.session)
                                              pending
                                              (Tacenta.UnitLifecycleEstablishedEncrypt.firstFrame view oracleA
                                                (Tacenta.UnitLifecycleEstablishInitiatorShape.establishedModelOf dh
                                                  q.session)
                                                (Tacenta.UnitLifecycleT3.sliceOf plaintext)
                                                (Tacenta.UnitLifecycleResponderFirstReceipt.firstKey
                                                  (Tacenta.UnitLifecycleT3.arrayOf q.sendChain)
                                                  (Tacenta.UnitLifecycleT3.arrayOf q.sparseSend))
                                                (Tacenta.UnitLifecycleT3.modelChunkOf src c)) →
                                          ∀ (ourB : tacenta_session_unit.lifecycle.Identity)
                                            (storeB : tacenta_session_unit.lifecycle.PrekeyStore),
                                            storeB.publish = Aeneas.Std.Result.ok bundle →
                                              ourB.public = Aeneas.Std.Result.ok storeB.identity_public →
                                                Tacenta.UnitLifecycleResponderFirstFrame.PrekeyIdsDistinct storeB →
                                                  Tacenta.UnitLifecycleResponderFirstFrame.FirstKemAgrees storeB
                                                      bundle.kem_prekey_id q.kemCiphertext q.kemSecret →
                                                    Tacenta.UnitLifecycleT1.EstablishResponderHeadroom storeB →
                                                      ∀ (rngB : E),
                                                        traceB rngB = oracleB.draws →
                                                          ∀ (dB : Model.Lifecycle.Key)
                                                            (restB : List Model.Lifecycle.Key),
                                                            traceB rngB = dB :: restB →
                                                              (bundle.kem_prekey_id = storeB.kem_id ∧
                                                                  ∃ e,
                                                                    Tacenta.UnitLifecycleResponderFirstFrame.StoreRefusal
                                                                        storeB q.sharedBytes e ∧
                                                                      tacenta_session_unit.lifecycle.establish_responder
                                                                          rcB crcB ourB storeB msg rngB =
                                                                        Aeneas.Std.Result.ok
                                                                          (Aeneas.Std.core.result.Result.Err e, storeB,
                                                                            rngB)) ∨
                                                                ∃ p ec rngB',
                                                                  p.shared = q.shared ∧
                                                                    p.secret = q.sharedBytes ∧
                                                                      p.tripleSecret = q.sharedSlice ∧
                                                                        p.peerIdentity = q.ourPublic ∧
                                                                          p.peerEphemeral = q.ephemeralPublic ∧
                                                                            p.kemSecret = q.kemSecret ∧
                                                                              (p.lastResort = true ↔
                                                                                  bundle.kem_prekey_id =
                                                                                    storeB.kem_id) ∧
                                                                                tacenta_session_unit.tacenta_ratchet.kdf_rk
                                                                                      ec q.dhOutBytes
                                                                                      tacenta_session_unit.tacenta_ratchet.LabelSet.Tacenta =
                                                                                    Aeneas.Std.Result.ok
                                                                                      (q.rootKey, q.sendChain) ∧
                                                                                  traceB rngB' = restB ∧
                                                                                    (tacenta_session_unit.lifecycle.establish_responder
                                                                                            rcB crcB ourB storeB msg
                                                                                            rngB =
                                                                                          Aeneas.Std.Result.ok
                                                                                            (Aeneas.Std.core.result.Result.Err
                                                                                                (tacenta_session_unit.lifecycle.Error.Handshake
                                                                                                  tacenta_session_unit.SessionError.NonContributoryAgreement),
                                                                                              storeB, rngB') ∧
                                                                                        oracleB.dhAgree dB
                                                                                            (Tacenta.UnitLifecycleT3.arrayOf
                                                                                              q.ratchetBytes) =
                                                                                          none ∨
                                                                                      (tacenta_session_unit.lifecycle.establish_responder
                                                                                              rcB crcB ourB storeB msg
                                                                                              rngB =
                                                                                            Aeneas.Std.Result.ok
                                                                                              (Aeneas.Std.core.result.Result.Err
                                                                                                  tacenta_session_unit.lifecycle.Error.Aead,
                                                                                                storeB, rngB') ∧
                                                                                          ∃ dSend,
                                                                                            oracleB.dhAgree dB
                                                                                                  (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                    q.ratchetBytes) =
                                                                                                some dSend ∧
                                                                                              Tacenta.UnitLifecycleResponderFirstReceipt.firstOpen
                                                                                                  oracleA oracleB
                                                                                                  (Tacenta.UnitLifecycleResponderFirstReceipt.firstKey
                                                                                                    (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                      q.sendChain)
                                                                                                    (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                      q.sparseSend))
                                                                                                  (Tacenta.UnitLifecycleT3.sliceOf
                                                                                                    plaintext)
                                                                                                  (Tacenta.UnitLifecycleResponderFirstReceipt.firstAd
                                                                                                    view
                                                                                                    (Tacenta.UnitLifecycleEstablishInitiatorShape.establishedModelOf
                                                                                                      dh q.session)
                                                                                                    (Tacenta.UnitLifecycleT3.modelChunkOf
                                                                                                      src c)) =
                                                                                                none) ∨
                                                                                        ∃ ptB sB' storeB' dSend x,
                                                                                          tacenta_session_unit.lifecycle.establish_responder
                                                                                                rcB crcB ourB storeB msg
                                                                                                rngB =
                                                                                              Aeneas.Std.Result.ok
                                                                                                (Aeneas.Std.core.result.Result.Ok
                                                                                                    (sB', ptB),
                                                                                                  storeB', rngB') ∧
                                                                                            oracleB.dhAgree dB
                                                                                                  (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                    q.ratchetBytes) =
                                                                                                some dSend ∧
                                                                                              Tacenta.UnitLifecycleResponderFirstReceipt.firstOpen
                                                                                                    oracleA oracleB
                                                                                                    (Tacenta.UnitLifecycleResponderFirstReceipt.firstKey
                                                                                                      (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                        q.sendChain)
                                                                                                      (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                        q.sparseSend))
                                                                                                    (Tacenta.UnitLifecycleT3.sliceOf
                                                                                                      plaintext)
                                                                                                    (Tacenta.UnitLifecycleResponderFirstReceipt.firstAd
                                                                                                      view
                                                                                                      (Tacenta.UnitLifecycleEstablishInitiatorShape.establishedModelOf
                                                                                                        dh q.session)
                                                                                                      (Tacenta.UnitLifecycleT3.modelChunkOf
                                                                                                        src c)) =
                                                                                                  some x ∧
                                                                                                Tacenta.UnitLifecycleT3.vecOf
                                                                                                      ptB =
                                                                                                    x ∧
                                                                                                  Tacenta.UnitLifecycleEstablishResponder.ResponderCommit
                                                                                                      storeB
                                                                                                      bundle.kem_prekey_id
                                                                                                      bundle.one_time_prekey_id
                                                                                                      p.lastResort
                                                                                                      p.replay storeB' ∧
                                                                                                    Tacenta.UnitLifecycleT3.SessionRefines
                                                                                                      dh
                                                                                                      oracleB.braidKem
                                                                                                      sB'
                                                                                                      (Tacenta.UnitLifecycleResponderFirstReceipt.firstReceiptSession
                                                                                                        (Tacenta.UnitLifecycleEstablishResponder.responderModelOf
                                                                                                          dh p)
                                                                                                        (Tacenta.UnitLifecycleT3.sliceOf
                                                                                                          p.braidSecret)
                                                                                                        (Tacenta.UnitLifecycleT3.modelChunkOf
                                                                                                          src c)
                                                                                                        (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                          ec)
                                                                                                        (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                          q.sparseRoot)
                                                                                                        (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                          q.sparseSend)
                                                                                                        (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                          q.sparseReceive)
                                                                                                        (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                          q.ratchetBytes)
                                                                                                        (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                          q.dhOut)
                                                                                                        dSend
                                                                                                        (oracleB.dhPublic
                                                                                                          dB)
                                                                                                        dB))
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderFirstReceipt.responder_first_frame_outcomes

/--
info: @Tacenta.UnitLifecycleResponderFirstReceipt.responder_first_frame_succeeds : ∀ {R : Type}
  {rc : tacenta_session_unit.rand_core_1.RngCore R} {crc : tacenta_session_unit.rand_core_1.CryptoRng R}
  {our : tacenta_session_unit.lifecycle.Identity} {bundle : tacenta_session_unit.lifecycle.PublishedBundle}
  [Tacenta.SessionUnitT1.DerivedKeysModel] {E : Type} (rcB : tacenta_session_unit.rand_core_1.RngCore E)
  (crcB : tacenta_session_unit.rand_core_1.CryptoRng E)
  (contracts : Tacenta.UnitLifecycleT1.EstablishResponderContracts rcB),
  Tacenta.UnitLifecycleEstablishInitiatorShape.DhPublicValid →
    Tacenta.UnitLifecycleResponderFirstFrame.DhAgreeSymmetric →
      Tacenta.UnitLifecycleResponderFirstReceipt.DhAgreeContributory →
        Tacenta.UnitLifecycleResponderFirstReceipt.AeadRoundTrip →
          Tacenta.UnitLifecycleSessionCodec.DhPublicBytesRoundTrip →
            Tacenta.UnitLifecycleEstablishInitiatorShape.KemCiphertextLenOf →
              Tacenta.UnitLifecycleRestoredSession.KemCiphertextLenBound →
                Tacenta.UnitHeadroomInvariant.OptionEqU64Shape
                    @tacenta_session_unit.core.option.Option.Insts.CoreCmpPartialEqOption.eq →
                  ∀ {dh : Tacenta.UnitLifecycleT3.DhView},
                    Tacenta.UnitLifecycleT3.DhCodecOf dh →
                      ∀ (view : Model.Lifecycle.CodewordView) (oracleA : Model.Lifecycle.Oracle),
                        Tacenta.UnitOracleShape.AeadSealClause Tacenta.UnitSatisfiabilityJoint.Interp.real oracleA →
                          ∀ (traceB : E → List Model.Lifecycle.Key) (oracleB : Model.Lifecycle.Oracle),
                            Tacenta.UnitLifecycleDecryptRatchetT3.DecryptOracleOf rcB crcB dh traceB oracleB →
                              Tacenta.UnitLifecycleDecryptRatchetT3.DecryptRatchetAgreements oracleB.braidKem →
                                ∀ (q : Tacenta.UnitLifecycleResponderFirstFrame.InitiatorSecretParts rc crc our bundle)
                                  (pending : Model.Lifecycle.PendingInitial),
                                  (Tacenta.UnitLifecycleEstablishInitiatorShape.establishedModelOf dh
                                          q.session).pendingInitial =
                                      some pending →
                                    ∀ (plaintext : Aeneas.Std.Slice Aeneas.Std.U8),
                                      (↑plaintext).length + 48 ≤ Aeneas.Std.Usize.max →
                                        ∀ (src : Model.Lifecycle.Bytes),
                                          List.length src = Model.Braid.headerSize + Model.Braid.macSize →
                                            ∀ (c : tacenta_session_unit.tacenta_erasure.Chunk),
                                              Tacenta.SessionUnitBraidT3.CodewordOf src c →
                                                view.send
                                                      (Tacenta.UnitLifecycleEstablishInitiatorShape.establishedModelOf
                                                          dh q.session).braid
                                                      (Tacenta.UnitLifecycleT3.modelChunkOf src c) =
                                                    Tacenta.UnitLifecycleT3.modelCodewordOf c →
                                                  ∀ (msg : Aeneas.Std.Slice Aeneas.Std.U8),
                                                    Tacenta.UnitLifecycleT3.sliceOf msg =
                                                        Tacenta.UnitLifecycleEstablishedEncrypt.initialWire
                                                          (Tacenta.UnitLifecycleEstablishInitiatorShape.establishedModelOf
                                                            dh q.session)
                                                          pending
                                                          (Tacenta.UnitLifecycleEstablishedEncrypt.firstFrame view
                                                            oracleA
                                                            (Tacenta.UnitLifecycleEstablishInitiatorShape.establishedModelOf
                                                              dh q.session)
                                                            (Tacenta.UnitLifecycleT3.sliceOf plaintext)
                                                            (Tacenta.UnitLifecycleResponderFirstReceipt.firstKey
                                                              (Tacenta.UnitLifecycleT3.arrayOf q.sendChain)
                                                              (Tacenta.UnitLifecycleT3.arrayOf q.sparseSend))
                                                            (Tacenta.UnitLifecycleT3.modelChunkOf src c)) →
                                                      ∀ (ourB : tacenta_session_unit.lifecycle.Identity)
                                                        (storeB : tacenta_session_unit.lifecycle.PrekeyStore),
                                                        storeB.publish = Aeneas.Std.Result.ok bundle →
                                                          ourB.public = Aeneas.Std.Result.ok storeB.identity_public →
                                                            Tacenta.UnitLifecycleResponderFirstFrame.PrekeyIdsDistinct
                                                                storeB →
                                                              Tacenta.UnitLifecycleResponderFirstFrame.FirstKemAgrees
                                                                  storeB bundle.kem_prekey_id q.kemCiphertext
                                                                  q.kemSecret →
                                                                Tacenta.UnitLifecycleT1.EstablishResponderHeadroom
                                                                    storeB →
                                                                  ∀ (rngB : E),
                                                                    traceB rngB = oracleB.draws →
                                                                      ∀ (dB : Model.Lifecycle.Key)
                                                                        (restB : List Model.Lifecycle.Key),
                                                                        traceB rngB = dB :: restB →
                                                                          (bundle.kem_prekey_id = storeB.kem_id ∧
                                                                              ∃ e,
                                                                                Tacenta.UnitLifecycleResponderFirstFrame.StoreRefusal
                                                                                    storeB q.sharedBytes e ∧
                                                                                  tacenta_session_unit.lifecycle.establish_responder
                                                                                      rcB crcB ourB storeB msg rngB =
                                                                                    Aeneas.Std.Result.ok
                                                                                      (Aeneas.Std.core.result.Result.Err
                                                                                          e,
                                                                                        storeB, rngB)) ∨
                                                                            ∃ p ec dSend ptB sB' storeB' rngB',
                                                                              p.shared = q.shared ∧
                                                                                p.secret = q.sharedBytes ∧
                                                                                  p.tripleSecret = q.sharedSlice ∧
                                                                                    p.peerIdentity = q.ourPublic ∧
                                                                                      p.peerEphemeral =
                                                                                          q.ephemeralPublic ∧
                                                                                        p.kemSecret = q.kemSecret ∧
                                                                                          (p.lastResort = true ↔
                                                                                              bundle.kem_prekey_id =
                                                                                                storeB.kem_id) ∧
                                                                                            tacenta_session_unit.tacenta_ratchet.kdf_rk
                                                                                                  ec q.dhOutBytes
                                                                                                  tacenta_session_unit.tacenta_ratchet.LabelSet.Tacenta =
                                                                                                Aeneas.Std.Result.ok
                                                                                                  (q.rootKey,
                                                                                                    q.sendChain) ∧
                                                                                              oracleB.dhAgree dB
                                                                                                    (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                      q.ratchetBytes) =
                                                                                                  some dSend ∧
                                                                                                tacenta_session_unit.lifecycle.establish_responder
                                                                                                      rcB crcB ourB
                                                                                                      storeB msg rngB =
                                                                                                    Aeneas.Std.Result.ok
                                                                                                      (Aeneas.Std.core.result.Result.Ok
                                                                                                          (sB', ptB),
                                                                                                        storeB',
                                                                                                        rngB') ∧
                                                                                                  ↑ptB = ↑plaintext ∧
                                                                                                    traceB rngB' =
                                                                                                        restB ∧
                                                                                                      Tacenta.UnitLifecycleEstablishResponder.ResponderCommit
                                                                                                          storeB
                                                                                                          bundle.kem_prekey_id
                                                                                                          bundle.one_time_prekey_id
                                                                                                          p.lastResort
                                                                                                          p.replay
                                                                                                          storeB' ∧
                                                                                                        (p.lastResort =
                                                                                                              false →
                                                                                                            p.replay =
                                                                                                              none) ∧
                                                                                                          (p.lastResort =
                                                                                                                true →
                                                                                                              ∃ fp,
                                                                                                                p.replay =
                                                                                                                    some
                                                                                                                      fp ∧
                                                                                                                  tacenta_session_unit.lifecycle.last_resort_fingerprint
                                                                                                                      q.sharedBytes =
                                                                                                                    Aeneas.Std.Result.ok
                                                                                                                      fp) ∧
                                                                                                            Tacenta.UnitLifecycleT3.SessionRefines
                                                                                                              dh
                                                                                                              oracleB.braidKem
                                                                                                              sB'
                                                                                                              (Tacenta.UnitLifecycleResponderFirstReceipt.firstReceiptSession
                                                                                                                (Tacenta.UnitLifecycleEstablishResponder.responderModelOf
                                                                                                                  dh p)
                                                                                                                (Tacenta.UnitLifecycleT3.sliceOf
                                                                                                                  p.braidSecret)
                                                                                                                (Tacenta.UnitLifecycleT3.modelChunkOf
                                                                                                                  src c)
                                                                                                                (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                                  ec)
                                                                                                                (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                                  q.sparseRoot)
                                                                                                                (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                                  q.sparseSend)
                                                                                                                (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                                  q.sparseReceive)
                                                                                                                (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                                  q.ratchetBytes)
                                                                                                                (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                                  q.dhOut)
                                                                                                                dSend
                                                                                                                (oracleB.dhPublic
                                                                                                                  dB)
                                                                                                                dB)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderFirstReceipt.responder_first_frame_succeeds

/--
info: @Tacenta.UnitLifecycleResponderFirstReceipt.initiator_first_send_responder_receives : ∀
  [Tacenta.SessionUnitT1.DerivedKeysModel] {R E F : Type} (rc : tacenta_session_unit.rand_core_1.RngCore R)
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
                        Tacenta.UnitLifecycleEstablishedEncrypt.KeyGenSizesOf oracle.braidKem →
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
                                                            Tacenta.UnitLifecycleResponderFirstReceipt.DhAgreeContributory →
                                                              Tacenta.UnitLifecycleResponderFirstReceipt.AeadRoundTrip →
                                                                Tacenta.UnitLifecycleSessionCodec.DhPublicBytesRoundTrip →
                                                                  Tacenta.UnitHeadroomInvariant.OptionEqU64Shape
                                                                      @tacenta_session_unit.core.option.Option.Insts.CoreCmpPartialEqOption.eq →
                                                                    ∀ (traceB : F → List Model.Lifecycle.Key)
                                                                      (oracleB : Model.Lifecycle.Oracle),
                                                                      Tacenta.UnitLifecycleDecryptRatchetT3.DecryptOracleOf
                                                                          rcB crcB dh traceB oracleB →
                                                                        Tacenta.UnitLifecycleDecryptRatchetT3.DecryptRatchetAgreements
                                                                            oracleB.braidKem →
                                                                          ∀
                                                                            (ourB :
                                                                              tacenta_session_unit.lifecycle.Identity)
                                                                            (storeB :
                                                                              tacenta_session_unit.lifecycle.PrekeyStore),
                                                                            storeB.publish =
                                                                                Aeneas.Std.Result.ok bundleA →
                                                                              ourB.public =
                                                                                  Aeneas.Std.Result.ok
                                                                                    storeB.identity_public →
                                                                                Tacenta.UnitLifecycleResponderFirstFrame.PrekeyIdsDistinct
                                                                                    storeB →
                                                                                  Tacenta.UnitLifecycleResponderFirstFrame.FirstKemAgrees
                                                                                      storeB bundleA.kem_prekey_id
                                                                                      q.kemCiphertext q.kemSecret →
                                                                                    Tacenta.UnitLifecycleT1.EstablishResponderHeadroom
                                                                                        storeB →
                                                                                      ∀ (rngB : F),
                                                                                        traceB rngB = oracleB.draws →
                                                                                          ∀ (dB : Model.Lifecycle.Key)
                                                                                            (restB :
                                                                                              List Model.Lifecycle.Key),
                                                                                            traceB rngB = dB :: restB →
                                                                                              trace rng' = rest ∧
                                                                                                ((bundleA.kem_prekey_id =
                                                                                                      storeB.kem_id ∧
                                                                                                    ∃ e,
                                                                                                      Tacenta.UnitLifecycleResponderFirstFrame.StoreRefusal
                                                                                                          storeB
                                                                                                          q.sharedBytes
                                                                                                          e ∧
                                                                                                        tacenta_session_unit.lifecycle.establish_responder
                                                                                                            rcB crcB
                                                                                                            ourB storeB
                                                                                                            bytes.deref
                                                                                                            rngB =
                                                                                                          Aeneas.Std.Result.ok
                                                                                                            (Aeneas.Std.core.result.Result.Err
                                                                                                                e,
                                                                                                              storeB,
                                                                                                              rngB)) ∨
                                                                                                  ∃ p ec dSend dk ekSeed
                                                                                                    ekVector ptB sB'
                                                                                                    storeB' rngB',
                                                                                                    oracle.braidKem.keyGen
                                                                                                          (Model.Lifecycle.braidRandomness
                                                                                                            (d1 ++
                                                                                                              d2)) =
                                                                                                        some
                                                                                                          (dk, ekSeed,
                                                                                                            ekVector) ∧
                                                                                                      p.shared =
                                                                                                          q.shared ∧
                                                                                                        p.secret =
                                                                                                            q.sharedBytes ∧
                                                                                                          p.tripleSecret =
                                                                                                              q.sharedSlice ∧
                                                                                                            p.peerIdentity =
                                                                                                                q.ourPublic ∧
                                                                                                              p.peerEphemeral =
                                                                                                                  q.ephemeralPublic ∧
                                                                                                                p.kemSecret =
                                                                                                                    q.kemSecret ∧
                                                                                                                  (p.lastResort =
                                                                                                                        true ↔
                                                                                                                      bundleA.kem_prekey_id =
                                                                                                                        storeB.kem_id) ∧
                                                                                                                    tacenta_session_unit.tacenta_ratchet.kdf_rk
                                                                                                                          ec
                                                                                                                          q.dhOutBytes
                                                                                                                          tacenta_session_unit.tacenta_ratchet.LabelSet.Tacenta =
                                                                                                                        Aeneas.Std.Result.ok
                                                                                                                          (q.rootKey,
                                                                                                                            q.sendChain) ∧
                                                                                                                      oracleB.dhAgree
                                                                                                                            dB
                                                                                                                            (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                                              q.ratchetBytes) =
                                                                                                                          some
                                                                                                                            dSend ∧
                                                                                                                        tacenta_session_unit.lifecycle.establish_responder
                                                                                                                              rcB
                                                                                                                              crcB
                                                                                                                              ourB
                                                                                                                              storeB
                                                                                                                              bytes.deref
                                                                                                                              rngB =
                                                                                                                            Aeneas.Std.Result.ok
                                                                                                                              (Aeneas.Std.core.result.Result.Ok
                                                                                                                                  (sB',
                                                                                                                                    ptB),
                                                                                                                                storeB',
                                                                                                                                rngB') ∧
                                                                                                                          ↑ptB =
                                                                                                                              ↑plaintext ∧
                                                                                                                            traceB
                                                                                                                                  rngB' =
                                                                                                                                restB ∧
                                                                                                                              Tacenta.UnitLifecycleEstablishResponder.ResponderCommit
                                                                                                                                  storeB
                                                                                                                                  bundleA.kem_prekey_id
                                                                                                                                  bundleA.one_time_prekey_id
                                                                                                                                  p.lastResort
                                                                                                                                  p.replay
                                                                                                                                  storeB' ∧
                                                                                                                                (p.lastResort =
                                                                                                                                      false →
                                                                                                                                    p.replay =
                                                                                                                                      none) ∧
                                                                                                                                  (p.lastResort =
                                                                                                                                        true →
                                                                                                                                      ∃
                                                                                                                                        fp,
                                                                                                                                        p.replay =
                                                                                                                                            some
                                                                                                                                              fp ∧
                                                                                                                                          tacenta_session_unit.lifecycle.last_resort_fingerprint
                                                                                                                                              q.sharedBytes =
                                                                                                                                            Aeneas.Std.Result.ok
                                                                                                                                              fp) ∧
                                                                                                                                    Tacenta.UnitLifecycleT3.SessionRefines
                                                                                                                                      dh
                                                                                                                                      oracleB.braidKem
                                                                                                                                      sB'
                                                                                                                                      (Tacenta.UnitLifecycleResponderFirstReceipt.firstReceiptSession
                                                                                                                                        (Tacenta.UnitLifecycleEstablishResponder.responderModelOf
                                                                                                                                          dh
                                                                                                                                          p)
                                                                                                                                        (Tacenta.UnitLifecycleT3.sliceOf
                                                                                                                                          p.braidSecret)
                                                                                                                                        {
                                                                                                                                          source :=
                                                                                                                                            Tacenta.UnitLifecycleResponderFirstReceipt.headerSource
                                                                                                                                              oracle.braidKem
                                                                                                                                              (Tacenta.SessionUnitBraidT3.AuthOf
                                                                                                                                                q.auth)
                                                                                                                                              ekSeed
                                                                                                                                              ekVector,
                                                                                                                                          index :=
                                                                                                                                            0 }
                                                                                                                                        (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                                                          ec)
                                                                                                                                        (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                                                          q.sparseRoot)
                                                                                                                                        (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                                                          q.sparseSend)
                                                                                                                                        (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                                                          q.sparseReceive)
                                                                                                                                        (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                                                          q.ratchetBytes)
                                                                                                                                        (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                                                          q.dhOut)
                                                                                                                                        dSend
                                                                                                                                        (oracleB.dhPublic
                                                                                                                                          dB)
                                                                                                                                        dB))
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderFirstReceipt.initiator_first_send_responder_receives

/--
info: @Tacenta.UnitLifecycleResponderFirstReceipt.initiator_first_send_responder_outcomes : ∀
  [Tacenta.SessionUnitT1.DerivedKeysModel] {R E F : Type} (rc : tacenta_session_unit.rand_core_1.RngCore R)
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
                        Tacenta.UnitLifecycleEstablishedEncrypt.KeyGenSizesOf oracle.braidKem →
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
                                                                ∀ (traceB : F → List Model.Lifecycle.Key)
                                                                  (oracleB : Model.Lifecycle.Oracle),
                                                                  Tacenta.UnitLifecycleDecryptRatchetT3.DecryptOracleOf
                                                                      rcB crcB dh traceB oracleB →
                                                                    Tacenta.UnitLifecycleDecryptRatchetT3.DecryptRatchetAgreements
                                                                        oracleB.braidKem →
                                                                      ∀ (ourB : tacenta_session_unit.lifecycle.Identity)
                                                                        (storeB :
                                                                          tacenta_session_unit.lifecycle.PrekeyStore),
                                                                        storeB.publish = Aeneas.Std.Result.ok bundleA →
                                                                          ourB.public =
                                                                              Aeneas.Std.Result.ok
                                                                                storeB.identity_public →
                                                                            Tacenta.UnitLifecycleResponderFirstFrame.PrekeyIdsDistinct
                                                                                storeB →
                                                                              Tacenta.UnitLifecycleResponderFirstFrame.FirstKemAgrees
                                                                                  storeB bundleA.kem_prekey_id
                                                                                  q.kemCiphertext q.kemSecret →
                                                                                Tacenta.UnitLifecycleT1.EstablishResponderHeadroom
                                                                                    storeB →
                                                                                  ∀ (rngB : F),
                                                                                    traceB rngB = oracleB.draws →
                                                                                      ∀ (dB : Model.Lifecycle.Key)
                                                                                        (restB :
                                                                                          List Model.Lifecycle.Key),
                                                                                        traceB rngB = dB :: restB →
                                                                                          trace rng' = rest ∧
                                                                                            ((bundleA.kem_prekey_id =
                                                                                                  storeB.kem_id ∧
                                                                                                ∃ e,
                                                                                                  Tacenta.UnitLifecycleResponderFirstFrame.StoreRefusal
                                                                                                      storeB
                                                                                                      q.sharedBytes e ∧
                                                                                                    tacenta_session_unit.lifecycle.establish_responder
                                                                                                        rcB crcB ourB
                                                                                                        storeB
                                                                                                        bytes.deref
                                                                                                        rngB =
                                                                                                      Aeneas.Std.Result.ok
                                                                                                        (Aeneas.Std.core.result.Result.Err
                                                                                                            e,
                                                                                                          storeB,
                                                                                                          rngB)) ∨
                                                                                              ∃ p ec dk ekSeed ekVector
                                                                                                rngB',
                                                                                                oracle.braidKem.keyGen
                                                                                                      (Model.Lifecycle.braidRandomness
                                                                                                        (d1 ++ d2)) =
                                                                                                    some
                                                                                                      (dk, ekSeed,
                                                                                                        ekVector) ∧
                                                                                                  p.shared = q.shared ∧
                                                                                                    p.secret =
                                                                                                        q.sharedBytes ∧
                                                                                                      p.tripleSecret =
                                                                                                          q.sharedSlice ∧
                                                                                                        p.peerIdentity =
                                                                                                            q.ourPublic ∧
                                                                                                          p.peerEphemeral =
                                                                                                              q.ephemeralPublic ∧
                                                                                                            p.kemSecret =
                                                                                                                q.kemSecret ∧
                                                                                                              (p.lastResort =
                                                                                                                    true ↔
                                                                                                                  bundleA.kem_prekey_id =
                                                                                                                    storeB.kem_id) ∧
                                                                                                                tacenta_session_unit.tacenta_ratchet.kdf_rk
                                                                                                                      ec
                                                                                                                      q.dhOutBytes
                                                                                                                      tacenta_session_unit.tacenta_ratchet.LabelSet.Tacenta =
                                                                                                                    Aeneas.Std.Result.ok
                                                                                                                      (q.rootKey,
                                                                                                                        q.sendChain) ∧
                                                                                                                  traceB
                                                                                                                        rngB' =
                                                                                                                      restB ∧
                                                                                                                    (tacenta_session_unit.lifecycle.establish_responder
                                                                                                                            rcB
                                                                                                                            crcB
                                                                                                                            ourB
                                                                                                                            storeB
                                                                                                                            bytes.deref
                                                                                                                            rngB =
                                                                                                                          Aeneas.Std.Result.ok
                                                                                                                            (Aeneas.Std.core.result.Result.Err
                                                                                                                                (tacenta_session_unit.lifecycle.Error.Handshake
                                                                                                                                  tacenta_session_unit.SessionError.NonContributoryAgreement),
                                                                                                                              storeB,
                                                                                                                              rngB') ∧
                                                                                                                        oracleB.dhAgree
                                                                                                                            dB
                                                                                                                            (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                                              q.ratchetBytes) =
                                                                                                                          none ∨
                                                                                                                      (tacenta_session_unit.lifecycle.establish_responder
                                                                                                                              rcB
                                                                                                                              crcB
                                                                                                                              ourB
                                                                                                                              storeB
                                                                                                                              bytes.deref
                                                                                                                              rngB =
                                                                                                                            Aeneas.Std.Result.ok
                                                                                                                              (Aeneas.Std.core.result.Result.Err
                                                                                                                                  tacenta_session_unit.lifecycle.Error.Aead,
                                                                                                                                storeB,
                                                                                                                                rngB') ∧
                                                                                                                          ∃
                                                                                                                            dSend,
                                                                                                                            oracleB.dhAgree
                                                                                                                                  dB
                                                                                                                                  (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                                                    q.ratchetBytes) =
                                                                                                                                some
                                                                                                                                  dSend ∧
                                                                                                                              Tacenta.UnitLifecycleResponderFirstReceipt.firstOpen
                                                                                                                                  oracle
                                                                                                                                  oracleB
                                                                                                                                  (Tacenta.UnitLifecycleResponderFirstReceipt.firstKey
                                                                                                                                    (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                                                      q.sendChain)
                                                                                                                                    (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                                                      q.sparseSend))
                                                                                                                                  (Tacenta.UnitLifecycleT3.sliceOf
                                                                                                                                    plaintext)
                                                                                                                                  (Tacenta.UnitLifecycleResponderFirstReceipt.firstAd
                                                                                                                                    view
                                                                                                                                    (Tacenta.UnitLifecycleEstablishInitiatorShape.establishedModelOf
                                                                                                                                      dh
                                                                                                                                      q.session)
                                                                                                                                    {
                                                                                                                                      source :=
                                                                                                                                        Tacenta.UnitLifecycleResponderFirstReceipt.headerSource
                                                                                                                                          oracle.braidKem
                                                                                                                                          (Tacenta.SessionUnitBraidT3.AuthOf
                                                                                                                                            q.auth)
                                                                                                                                          ekSeed
                                                                                                                                          ekVector,
                                                                                                                                      index :=
                                                                                                                                        0 }) =
                                                                                                                                none) ∨
                                                                                                                        ∃
                                                                                                                          ptB
                                                                                                                          sB'
                                                                                                                          storeB'
                                                                                                                          dSend
                                                                                                                          x,
                                                                                                                          tacenta_session_unit.lifecycle.establish_responder
                                                                                                                                rcB
                                                                                                                                crcB
                                                                                                                                ourB
                                                                                                                                storeB
                                                                                                                                bytes.deref
                                                                                                                                rngB =
                                                                                                                              Aeneas.Std.Result.ok
                                                                                                                                (Aeneas.Std.core.result.Result.Ok
                                                                                                                                    (sB',
                                                                                                                                      ptB),
                                                                                                                                  storeB',
                                                                                                                                  rngB') ∧
                                                                                                                            oracleB.dhAgree
                                                                                                                                  dB
                                                                                                                                  (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                                                    q.ratchetBytes) =
                                                                                                                                some
                                                                                                                                  dSend ∧
                                                                                                                              Tacenta.UnitLifecycleResponderFirstReceipt.firstOpen
                                                                                                                                    oracle
                                                                                                                                    oracleB
                                                                                                                                    (Tacenta.UnitLifecycleResponderFirstReceipt.firstKey
                                                                                                                                      (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                                                        q.sendChain)
                                                                                                                                      (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                                                        q.sparseSend))
                                                                                                                                    (Tacenta.UnitLifecycleT3.sliceOf
                                                                                                                                      plaintext)
                                                                                                                                    (Tacenta.UnitLifecycleResponderFirstReceipt.firstAd
                                                                                                                                      view
                                                                                                                                      (Tacenta.UnitLifecycleEstablishInitiatorShape.establishedModelOf
                                                                                                                                        dh
                                                                                                                                        q.session)
                                                                                                                                      {
                                                                                                                                        source :=
                                                                                                                                          Tacenta.UnitLifecycleResponderFirstReceipt.headerSource
                                                                                                                                            oracle.braidKem
                                                                                                                                            (Tacenta.SessionUnitBraidT3.AuthOf
                                                                                                                                              q.auth)
                                                                                                                                            ekSeed
                                                                                                                                            ekVector,
                                                                                                                                        index :=
                                                                                                                                          0 }) =
                                                                                                                                  some
                                                                                                                                    x ∧
                                                                                                                                Tacenta.UnitLifecycleT3.vecOf
                                                                                                                                      ptB =
                                                                                                                                    x ∧
                                                                                                                                  Tacenta.UnitLifecycleEstablishResponder.ResponderCommit
                                                                                                                                      storeB
                                                                                                                                      bundleA.kem_prekey_id
                                                                                                                                      bundleA.one_time_prekey_id
                                                                                                                                      p.lastResort
                                                                                                                                      p.replay
                                                                                                                                      storeB' ∧
                                                                                                                                    Tacenta.UnitLifecycleT3.SessionRefines
                                                                                                                                      dh
                                                                                                                                      oracleB.braidKem
                                                                                                                                      sB'
                                                                                                                                      (Tacenta.UnitLifecycleResponderFirstReceipt.firstReceiptSession
                                                                                                                                        (Tacenta.UnitLifecycleEstablishResponder.responderModelOf
                                                                                                                                          dh
                                                                                                                                          p)
                                                                                                                                        (Tacenta.UnitLifecycleT3.sliceOf
                                                                                                                                          p.braidSecret)
                                                                                                                                        {
                                                                                                                                          source :=
                                                                                                                                            Tacenta.UnitLifecycleResponderFirstReceipt.headerSource
                                                                                                                                              oracle.braidKem
                                                                                                                                              (Tacenta.SessionUnitBraidT3.AuthOf
                                                                                                                                                q.auth)
                                                                                                                                              ekSeed
                                                                                                                                              ekVector,
                                                                                                                                          index :=
                                                                                                                                            0 }
                                                                                                                                        (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                                                          ec)
                                                                                                                                        (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                                                          q.sparseRoot)
                                                                                                                                        (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                                                          q.sparseSend)
                                                                                                                                        (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                                                          q.sparseReceive)
                                                                                                                                        (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                                                          q.ratchetBytes)
                                                                                                                                        (Tacenta.UnitLifecycleT3.arrayOf
                                                                                                                                          q.dhOut)
                                                                                                                                        dSend
                                                                                                                                        (oracleB.dhPublic
                                                                                                                                          dB)
                                                                                                                                        dB)))
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderFirstReceipt.initiator_first_send_responder_outcomes

/--
info: Tacenta.UnitLifecycleResponderFirstReceipt.modelFirstReceipt_dhCodec : Tacenta.UnitSatisfiabilityJoint.DhCodecShape
  Tacenta.UnitLifecycleResponderFirstReceipt.Interp.modelFirstReceipt
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderFirstReceipt.modelFirstReceipt_dhCodec

/--
info: Tacenta.UnitLifecycleResponderFirstReceipt.modelFirstReceipt_dhAgree : Tacenta.UnitSatisfiabilityJoint.DhAgreeShape
  Tacenta.UnitLifecycleResponderFirstReceipt.Interp.modelFirstReceipt
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderFirstReceipt.modelFirstReceipt_dhAgree

/--
info: Tacenta.UnitLifecycleResponderFirstReceipt.modelFirstReceipt_symmetric : Tacenta.UnitLifecycleResponderFirstFrame.DhAgreeSymmetricShape
  Tacenta.UnitLifecycleResponderFirstReceipt.Interp.modelFirstReceipt
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderFirstReceipt.modelFirstReceipt_symmetric

/--
info: Tacenta.UnitLifecycleResponderFirstReceipt.modelFirstReceipt_aeadOpen : Tacenta.UnitSatisfiabilityJoint.AeadOpenShape
  Tacenta.UnitLifecycleResponderFirstReceipt.Interp.modelFirstReceipt
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderFirstReceipt.modelFirstReceipt_aeadOpen

/--
info: Tacenta.UnitLifecycleResponderFirstReceipt.modelFirstReceipt_aeadSeal : Tacenta.UnitSatisfiabilityJoint.AeadSealBoundedShape
  Tacenta.UnitLifecycleResponderFirstReceipt.Interp.modelFirstReceipt
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderFirstReceipt.modelFirstReceipt_aeadSeal

/--
info: Tacenta.UnitLifecycleResponderFirstReceipt.modelFirstReceipt_aeadRoundTrip : Tacenta.UnitLifecycleResponderFirstReceipt.AeadRoundTripShape
  Tacenta.UnitLifecycleResponderFirstReceipt.Interp.modelFirstReceipt
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderFirstReceipt.modelFirstReceipt_aeadRoundTrip

/--
info: Tacenta.UnitLifecycleResponderFirstReceipt.modelFirstReceipt_contributory : Tacenta.UnitLifecycleResponderFirstReceipt.DhAgreeContributoryShape
  Tacenta.UnitLifecycleResponderFirstReceipt.Interp.modelFirstReceipt
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderFirstReceipt.modelFirstReceipt_contributory

/--
info: Tacenta.UnitLifecycleResponderFirstReceipt.first_receipt_laws_model : Tacenta.UnitLifecycleDecryptScreen.DecryptJointLawsShape
    Tacenta.UnitLifecycleResponderFirstReceipt.Interp.modelFirstReceipt
    Tacenta.UnitLifecycleResponderFirstReceipt.viewFirstReceipt Tacenta.UnitLifecycleEstablishedEncrypt.toyKemR
    @Tacenta.UnitHeadroomInvariant.optionEqImpl ∧
  Nonempty
      (Tacenta.UnitSatisfiabilityJoint.InitiatorAxiom
        Tacenta.UnitLifecycleResponderFirstReceipt.Interp.modelFirstReceipt
        Tacenta.UnitLifecycleIntegrationScreen.byteRng) ∧
    Tacenta.UnitLifecycleEstablishInitiatorShape.InitiatorSuccessShape
        Tacenta.UnitLifecycleResponderFirstReceipt.Interp.modelFirstReceipt
        Tacenta.UnitLifecycleIntegrationScreen.byteRng Tacenta.UnitLifecycleIntegrationScreen.byteCrc ∧
      Tacenta.UnitLifecycleEstablishInitiatorShape.DhPublicValidShape
          Tacenta.UnitLifecycleResponderFirstReceipt.Interp.modelFirstReceipt ∧
        Tacenta.UnitLifecycleEstablishInitiatorShape.KemCiphertextLenLawShape (Aeneas.Std.Result.ok 0#usize)
            Tacenta.UnitLifecycleResponderFirstReceipt.Interp.modelFirstReceipt ∧
          Tacenta.UnitLifecycleEstablishedEncrypt.EncryptExtraLawsShape
              Tacenta.UnitLifecycleResponderFirstReceipt.InterpO.modelFirstReceipt
              Tacenta.UnitLifecycleResponderFirstReceipt.dhViewFirstReceipt
              Tacenta.UnitLifecycleResponderFirstReceipt.kemViewFirstReceipt
              Tacenta.UnitLifecycleEstablishedEncrypt.toyKemR (Aeneas.Std.Result.ok 0#usize) ∧
            (Tacenta.UnitLifecycleSessionCodec.ZeroizingVecRoundTripShape
                  Tacenta.UnitLifecycleResponderFirstReceipt.Interp.modelFirstReceipt ∧
                Tacenta.UnitLifecycleSessionCodec.DhPrivateBytesRoundTripShape
                    Tacenta.UnitLifecycleResponderFirstReceipt.Interp.modelFirstReceipt ∧
                  Tacenta.UnitLifecycleSessionCodec.DhPublicBytesRoundTripShape
                      Tacenta.UnitLifecycleResponderFirstReceipt.Interp.modelFirstReceipt ∧
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
                          Tacenta.UnitLifecycleResponderFirstReceipt.Interp.modelFirstReceipt
                          Tacenta.UnitLifecycleIntegrationScreen.byteRng) ∧
                      Tacenta.UnitLifecycleEstablishResponder.ResponderSuccessShape
                          Tacenta.UnitLifecycleResponderFirstReceipt.Interp.modelFirstReceipt ∧
                        Tacenta.UnitLifecycleEstablishResponder.ZeroKeyShape
                            Tacenta.UnitLifecycleResponderFirstReceipt.Interp.modelFirstReceipt ∧
                          Tacenta.UnitLifecycleResponderFirstFrame.DhAgreeSymmetricShape
                              Tacenta.UnitLifecycleResponderFirstReceipt.Interp.modelFirstReceipt ∧
                            (Tacenta.UnitLifecycleResponderFirstFrame.FirstFrameSuccessShape
                                Tacenta.UnitLifecycleResponderFirstReceipt.Interp.modelFirstReceipt
                                (fun x => Aeneas.Std.Result.ok (Aeneas.Std.alloc.vec.Vec.new Aeneas.Std.U8))
                                fun {T} x v => Aeneas.Std.Result.ok (decide (↑v = []))) ∧
                              Tacenta.UnitLifecycleResponderFirstReceipt.AeadRoundTripShape
                                  Tacenta.UnitLifecycleResponderFirstReceipt.Interp.modelFirstReceipt ∧
                                Tacenta.UnitLifecycleResponderFirstReceipt.DhAgreeContributoryShape
                                  Tacenta.UnitLifecycleResponderFirstReceipt.Interp.modelFirstReceipt
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderFirstReceipt.first_receipt_laws_model

/--
info: Tacenta.UnitLifecycleResponderFirstReceipt.first_send_receive_reachable : ∀ (K : Model.Braid.Kem)
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
                      Tacenta.UnitLifecycleEstablishedEncrypt.KeyGenSizesOf K →
                        Tacenta.UnitLifecycleResponderFirstReceipt.DhAgreeContributory →
                          Tacenta.UnitLifecycleResponderFirstReceipt.AeadRoundTrip →
                            ∀ (ourA : tacenta_session_unit.lifecycle.Identity) (seed : List Aeneas.Std.U8),
                              seed.length = 64 →
                                K.keyGen
                                      (Model.Lifecycle.braidRandomness (List.map Tacenta.SessionUnitBraidT3.u8 seed)) ≠
                                    none →
                                  ∃ oracle bundle rng0 rng1 q bytes s' rng' ourB storeB sB' ptB storeB' rngB',
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
                                                  Tacenta.UnitLifecycleT1.EstablishResponderHeadroom storeB ∧
                                                    Tacenta.UnitLifecycleDecryptRatchetT3.DecryptOracleOf
                                                        Tacenta.UnitLifecycleIntegrationScreen.byteRng
                                                        Tacenta.UnitLifecycleIntegrationScreen.byteCrc dh
                                                        Tacenta.UnitLifecycleIntegrationScreen.byteTrace oracle ∧
                                                      Tacenta.UnitLifecycleIntegrationScreen.byteTrace seed =
                                                          oracle.draws ∧
                                                        ↑storeB.legacy_last_resort_blocked = [] ∧
                                                          ↑storeB.last_resort_seen = [] ∧
                                                            tacenta_session_unit.lifecycle.establish_responder
                                                                  Tacenta.UnitLifecycleIntegrationScreen.byteRng
                                                                  Tacenta.UnitLifecycleIntegrationScreen.byteCrc ourB
                                                                  storeB bytes.deref seed =
                                                                Aeneas.Std.Result.ok
                                                                  (Aeneas.Std.core.result.Result.Ok (sB', ptB), storeB',
                                                                    rngB') ∧
                                                              ↑ptB =
                                                                ↑Tacenta.UnitLifecycleEstablishedEncrypt.emptyPlaintext
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleResponderFirstReceipt.first_send_receive_reachable

/--
info: def Tacenta.UnitLifecycleResponderFirstReceipt.firstSenderTriple : Model.State.Key →
  Model.State.Key →
    Model.State.Key → Model.State.Key → Model.State.Key → Model.State.Key → Model.State.Key → Model.Triple.State :=
fun a4 peer rkA cksA prk k1 k2 =>
  {
    classical :=
      { dhsPub := a4, dhrPub := some peer, rk := rkA, cks := some cksA, ckr := none, ns := 0, nr := 0, pn := 0,
        skipped := [], events := 0, labels := Model.State.LabelSet.tacenta },
    postQuantum :=
      { rk := prk, epoch := 0,
        chains := [(0, { send := some { ck := k1, n := 0 }, receive := some { ck := k2, n := 0 } })], skipped := [],
        direction := Model.SparseRatchet.Direction.a2b } }
-/
#guard_msgs in
#print Tacenta.UnitLifecycleResponderFirstReceipt.firstSenderTriple

/--
info: def Tacenta.UnitLifecycleResponderFirstReceipt.firstReceiverTriple : Model.State.Key →
  Model.State.Key → Model.State.Key → Model.State.Key → Model.State.Key → Model.Triple.State :=
fun b ec prk k1 k2 =>
  {
    classical :=
      { dhsPub := b, dhrPub := none, rk := ec, cks := none, ckr := none, ns := 0, nr := 0, pn := 0, skipped := [],
        events := 0, labels := Model.State.LabelSet.tacenta },
    postQuantum :=
      { rk := prk, epoch := 0,
        chains := [(0, { send := some { ck := k2, n := 0 }, receive := some { ck := k1, n := 0 } })], skipped := [],
        direction := Model.SparseRatchet.Direction.b2a } }
-/
#guard_msgs in
#print Tacenta.UnitLifecycleResponderFirstReceipt.firstReceiverTriple

/--
info: def Tacenta.UnitLifecycleResponderFirstReceipt.firstHeader : Model.State.Key → Model.Triple.Header :=
fun a4 => { dr := { dh := a4, pn := 0, n := 0 }, epoch := 0, pqN := 1 }
-/
#guard_msgs in
#print Tacenta.UnitLifecycleResponderFirstReceipt.firstHeader

/--
info: def Tacenta.UnitLifecycleResponderFirstReceipt.firstKey : Model.State.Key → Model.State.Key → Model.State.Key :=
fun cksA k1 => Model.TripleRatchet.combine (Model.State.kdfCk cksA).2 (Model.SparseRatchet.kdfCk k1 1).2
-/
#guard_msgs in
#print Tacenta.UnitLifecycleResponderFirstReceipt.firstKey

/--
info: def Tacenta.UnitLifecycleResponderFirstReceipt.senderAfterFirst : Model.State.Key →
  Model.State.Key →
    Model.State.Key → Model.State.Key → Model.State.Key → Model.State.Key → Model.State.Key → Model.Triple.State :=
fun a4 peer rkA cksA prk k1 k2 =>
  {
    classical :=
      { dhsPub := a4, dhrPub := some peer, rk := rkA, cks := some (Model.State.kdfCk cksA).1, ckr := none, ns := 1,
        nr := 0, pn := 0, skipped := [], events := 0, labels := Model.State.LabelSet.tacenta },
    postQuantum :=
      { rk := prk, epoch := 0,
        chains :=
          [(0,
              { send := some { ck := (Model.SparseRatchet.kdfCk k1 1).1, n := 1 },
                receive := some { ck := k2, n := 0 } })],
        skipped := [], direction := Model.SparseRatchet.Direction.a2b } }
-/
#guard_msgs in
#print Tacenta.UnitLifecycleResponderFirstReceipt.senderAfterFirst

/--
info: def Tacenta.UnitLifecycleResponderFirstReceipt.receiverAfterFirst : Model.State.Key →
  Model.State.Key →
    Model.State.Key →
      Model.State.Key → Model.State.Key → Model.State.Key → Model.State.Key → Model.State.Key → Model.Triple.State :=
fun ec prk k1 k2 a4 d dSend newPub =>
  {
    classical :=
      { dhsPub := newPub, dhrPub := some a4,
        rk :=
          (Model.State.kdfRk (Model.State.kdfRk ec d Model.State.LabelSet.tacenta).1 dSend
              Model.State.LabelSet.tacenta).1,
        cks :=
          some
            (Model.State.kdfRk (Model.State.kdfRk ec d Model.State.LabelSet.tacenta).1 dSend
                Model.State.LabelSet.tacenta).2,
        ckr := some (Model.State.kdfCk (Model.State.kdfRk ec d Model.State.LabelSet.tacenta).2).1, ns := 0, nr := 1,
        pn := 0, skipped := [], events := 1, labels := Model.State.LabelSet.tacenta },
    postQuantum :=
      { rk := prk, epoch := 0,
        chains :=
          [(0,
              { send := some { ck := k2, n := 0 },
                receive := some { ck := (Model.SparseRatchet.kdfCk k1 1).1, n := 1 } })],
        skipped := [], direction := Model.SparseRatchet.Direction.b2a } }
-/
#guard_msgs in
#print Tacenta.UnitLifecycleResponderFirstReceipt.receiverAfterFirst

/--
info: def Tacenta.UnitLifecycleResponderFirstReceipt.firstAd : Model.Lifecycle.CodewordView →
  Model.Lifecycle.Session → Model.Braid.Chunk → Model.Lifecycle.Bytes :=
fun view m chunk =>
  Model.Messages.concatAd m.identityAd
    (Model.CompositeHeader.encode (Tacenta.UnitLifecycleEstablishedEncrypt.firstComposite view m chunk))
-/
#guard_msgs in
#print Tacenta.UnitLifecycleResponderFirstReceipt.firstAd

/--
info: def Tacenta.UnitLifecycleResponderFirstReceipt.firstOpen : Model.Lifecycle.Oracle →
  Model.Lifecycle.Oracle →
    Model.State.Key → Model.Lifecycle.Bytes → Model.Lifecycle.Bytes → Option Model.Lifecycle.Bytes :=
fun oracleA oracleB mk pt ad =>
  oracleB.aeadOpen (Model.State.messageKeys mk Model.State.LabelSet.tacenta).1
    (Model.State.messageKeys mk Model.State.LabelSet.tacenta).2.1
    (Model.State.messageKeys mk Model.State.LabelSet.tacenta).2.2
    (oracleA.aeadSeal (Model.State.messageKeys mk Model.State.LabelSet.tacenta).1
      (Model.State.messageKeys mk Model.State.LabelSet.tacenta).2.1
      (Model.State.messageKeys mk Model.State.LabelSet.tacenta).2.2 pt ad)
    ad
-/
#guard_msgs in
#print Tacenta.UnitLifecycleResponderFirstReceipt.firstOpen

/--
info: def Tacenta.UnitLifecycleResponderFirstReceipt.firstReceiptSession : Model.Lifecycle.Session →
  Model.Lifecycle.Bytes →
    Model.Braid.Chunk →
      Model.State.Key →
        Model.State.Key →
          Model.State.Key →
            Model.State.Key →
              Model.State.Key →
                Model.State.Key → Model.State.Key → Model.State.Key → Model.State.Key → Model.Lifecycle.Session :=
fun mB secret rcv ec prk k1 k2 a4 d dSend newPub c =>
  { triple := Tacenta.UnitLifecycleResponderFirstReceipt.receiverAfterFirst ec prk k1 k2 a4 d dSend newPub,
    braid :=
      Model.Braid.BraidState.noHeaderReceived 1 (Model.Braid.Auth.init 1 secret)
        ((Model.Braid.Decoder.new (Model.Braid.headerSize + Model.Braid.macSize)).addChunk rcv),
    ratchetPrivate := if (newPub == mB.triple.classical.dhsPub) = true then mB.ratchetPrivate else c,
    identityAd := mB.identityAd, ourIdentityPublic := mB.ourIdentityPublic, peerIdentityPublic := mB.peerIdentityPublic,
    pendingInitial := mB.pendingInitial, establishedEphemeral := mB.establishedEphemeral }
-/
#guard_msgs in
#print Tacenta.UnitLifecycleResponderFirstReceipt.firstReceiptSession

/--
info: def Tacenta.UnitLifecycleResponderFirstReceipt.AeadRoundTripShape : Tacenta.UnitSatisfiabilityJoint.Interp → Prop :=
fun I =>
  ∀ (k1 k2 : Aeneas.Std.Array Aeneas.Std.U8 32#usize) (iv : Aeneas.Std.Array Aeneas.Std.U8 16#usize)
    (pt ad : Aeneas.Std.Slice Aeneas.Std.U8) (ct : Aeneas.Std.alloc.vec.Vec Aeneas.Std.U8),
    (↑pt).length + 48 ≤ Aeneas.Std.Usize.max →
      I.aeadEncrypt k1 k2 iv pt ad = Aeneas.Std.Result.ok ct →
        ∃ v, I.aeadDecrypt k1 k2 iv ct.deref ad = Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok v) ∧ ↑v = ↑pt
-/
#guard_msgs in
#print Tacenta.UnitLifecycleResponderFirstReceipt.AeadRoundTripShape

/--
info: def Tacenta.UnitLifecycleResponderFirstReceipt.AeadRoundTrip : Prop :=
Tacenta.UnitLifecycleResponderFirstReceipt.AeadRoundTripShape Tacenta.UnitSatisfiabilityJoint.Interp.real
-/
#guard_msgs in
#print Tacenta.UnitLifecycleResponderFirstReceipt.AeadRoundTrip

/--
info: def Tacenta.UnitLifecycleResponderFirstReceipt.DhAgreeContributoryShape : Tacenta.UnitSatisfiabilityJoint.Interp →
  Prop :=
fun I =>
  ∀ (a b : I.PrivateKey) (pb : I.PublicKeyBytes),
    I.dhPrivPublicKey b = Aeneas.Std.Result.ok pb → ∃ x, I.dhPrivAgree a pb = Aeneas.Std.Result.ok (some x)
-/
#guard_msgs in
#print Tacenta.UnitLifecycleResponderFirstReceipt.DhAgreeContributoryShape

/--
info: def Tacenta.UnitLifecycleResponderFirstReceipt.DhAgreeContributory : Prop :=
Tacenta.UnitLifecycleResponderFirstReceipt.DhAgreeContributoryShape Tacenta.UnitSatisfiabilityJoint.Interp.real
-/
#guard_msgs in
#print Tacenta.UnitLifecycleResponderFirstReceipt.DhAgreeContributory

/--
info: def Tacenta.UnitLifecycleResponderFirstReceipt.arrayOfBytes : {n : Aeneas.Std.Usize} →
  (l : Model.Lifecycle.Bytes) → List.length l = ↑n → Aeneas.Std.Array Aeneas.Std.U8 n :=
fun {n} l h =>
  ⟨Tacenta.UnitSatisfiabilityBraidAgreements.bytesOf l,
    (⋯ : (Tacenta.UnitSatisfiabilityBraidAgreements.bytesOf l).length = ↑n)⟩
-/
#guard_msgs in
#print Tacenta.UnitLifecycleResponderFirstReceipt.arrayOfBytes

/--
info: def Tacenta.UnitLifecycleResponderFirstReceipt.attributedView : Model.Lifecycle.CodewordView →
  UInt16 → Model.Lifecycle.Bytes → Model.Braid.Chunk → Model.Lifecycle.CodewordView :=
fun view idx data mc =>
  { receive := fun st i d => if i = idx ∧ d = data then mc else view.receive st i d, send := view.send }
-/
#guard_msgs in
#print Tacenta.UnitLifecycleResponderFirstReceipt.attributedView

/--
info: def Tacenta.UnitLifecycleResponderFirstReceipt.headerSource : Model.Braid.Kem →
  Model.Braid.Auth → Model.Braid.Bytes → Model.Braid.Bytes → Model.Braid.Bytes :=
fun K a ekSeed ekVector => ekSeed ++ K.hashEk ekSeed ekVector ++ a.macHdr 1 (ekSeed ++ K.hashEk ekSeed ekVector)
-/
#guard_msgs in
#print Tacenta.UnitLifecycleResponderFirstReceipt.headerSource

/--
info: def Tacenta.UnitLifecycleResponderFirstReceipt.Interp.modelFirstReceipt : Tacenta.UnitSatisfiabilityJoint.Interp :=
have __src := Tacenta.UnitLifecycleResponderFirstFrame.Interp.modelFirstFrame;
{ PrivateKey := __src.PrivateKey, PublicKeyBytes := __src.PublicKeyBytes, KemKeyPair := __src.KemKeyPair,
  IncrementalKeyPair := __src.IncrementalKeyPair, EncapsState := __src.EncapsState, Zeroizing := __src.Zeroizing,
  dhPrivFromBytes := __src.dhPrivFromBytes, dhPrivPublicKey := __src.dhPrivPublicKey, dhPrivAgree := __src.dhPrivAgree,
  dhPrivToBytes := __src.dhPrivToBytes, dhPubFromBytes := __src.dhPubFromBytes, dhPubAsBytes := __src.dhPubAsBytes,
  dhPubEq := __src.dhPubEq, dhIsPrimeOrderPublic := __src.dhIsPrimeOrderPublic,
  aeadEncrypt := fun x x_1 x_2 p x_3 => Aeneas.Std.Result.ok (Tacenta.UnitOracleModel.sealModel p),
  aeadDecrypt := fun x x_1 x_2 c x_3 => Aeneas.Std.Result.ok (Tacenta.UnitOracleModel.openModel c),
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
#print Tacenta.UnitLifecycleResponderFirstReceipt.Interp.modelFirstReceipt

/--
info: def Tacenta.UnitLifecycleResponderFirstReceipt.InterpO.modelFirstReceipt : Tacenta.UnitOracleShape.InterpO :=
have __src := Tacenta.UnitLifecycleResponderFirstReceipt.Interp.modelFirstReceipt;
{ toInterp := __src, xeddsaSign := fun {R} => Tacenta.UnitOracleModel.signModelO }
-/
#guard_msgs in
#print Tacenta.UnitLifecycleResponderFirstReceipt.InterpO.modelFirstReceipt

/--
info: def Tacenta.UnitLifecycleResponderFirstReceipt.viewFirstReceipt : Tacenta.UnitLifecycleDecryptRatchetScreen.DhViewShape
  Tacenta.UnitLifecycleResponderFirstReceipt.Interp.modelFirstReceipt :=
{ privateKey := Tacenta.UnitLifecycleT3.arrayOf, publicKey := Tacenta.UnitLifecycleT3.arrayOf }
-/
#guard_msgs in
#print Tacenta.UnitLifecycleResponderFirstReceipt.viewFirstReceipt

/--
info: def Tacenta.UnitLifecycleResponderFirstReceipt.dhViewFirstReceipt : Tacenta.UnitOracleShape.DhViewOf
  Tacenta.UnitLifecycleResponderFirstReceipt.InterpO.modelFirstReceipt.toInterp :=
{ privateKey := Tacenta.UnitLifecycleResponderFirstReceipt.viewFirstReceipt.privateKey,
  publicKey := Tacenta.UnitLifecycleResponderFirstReceipt.viewFirstReceipt.publicKey }
-/
#guard_msgs in
#print Tacenta.UnitLifecycleResponderFirstReceipt.dhViewFirstReceipt

/--
info: def Tacenta.UnitLifecycleResponderFirstReceipt.kemViewFirstReceipt : Tacenta.UnitOracleShape.KemViewOf
  Tacenta.UnitLifecycleResponderFirstReceipt.InterpO.modelFirstReceipt.toInterp :=
{ keyPair := fun x => [] }
-/
#guard_msgs in
#print Tacenta.UnitLifecycleResponderFirstReceipt.kemViewFirstReceipt
