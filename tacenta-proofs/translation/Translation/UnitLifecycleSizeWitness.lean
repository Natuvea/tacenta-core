import Translation.UnitLifecycleResponderReplyReceipt
import Translation.UnitLifecycleSizeRule

/-!
# A joint padded witness for the received maximum and a reply route

`UnitLifecycleSizeRule` proves that a plaintext a receive returns is at most `MAX_PLAINTEXT_LEN` bytes for a result that
refines the model's step and under the assumed open-length law `Model.Lifecycle.AeadOpenLength`. No model in the tree
met that law: the toy AEADs open to the input less one byte or less 32 bytes. This module gives a padded toy AEAD
(PKCS#7-style padding to a 16-byte block and a 32-byte tag, `16 * (n / 16) + 48` bytes for an `n`-byte plaintext; the
open drops the tag and the padding its last byte names) and shows that the received maximum's hypotheses, the reply
receipt's and every law they rest on hold together: at the real constants under those laws on one run
(`size_witness_reachable`), and every law in one toy interpretation (`size_witness_laws_model`).

* `padSeal`, `padOpen`: the padded toy; `padOpen_length` (an open returns at least 33 bytes fewer than its input),
  `padOpen_padSeal` (the open returns what the seal was given).
* `Interp.modelPadded`: the reply receipt's joint model `Interp.modelReply` with the padded seal and open.
* `AeadOpenLengthShape`, `AeadOpenLengthLaw`: the open-length law at the code level, over an interpretation and at the
  real constants.
* `size_witness_laws_model`: every conjunct of `reply_receipt_laws_model` holds again at `Interp.modelPadded`,
  together with `AeadOpenLengthShape`.
* `aeadOpenLength_oracleOfLaws`, `oracleOfShape_open`, `established_encrypt_hypotheses_open`: the oracle the laws build
  meets `AeadOpenLength` when the interpretation's open meets the code-level law.
* `initiator_receives_reply_step`: the initiator's receipt of the reply, as a step refinement.
* `size_witness_reachable`: one run at which every hypothesis of `initiator_receives_reply` and of
  `decrypt_ok_plaintext_le_max` holds, at the same call.

## The laws and premises

* `AeadOpenLengthLaw` (assumed): the real open returns at least 33 bytes fewer than its input. The reach takes it with
  the laws of `first_send_reply_receipt_reachable` (all assumed), and `size_witness_laws_model` satisfies all of them in
  the padded toy interpretation.
* No per-run premise beyond the reach's own (the 64-byte seed at which key generation answers, 32 further bytes, a
  reply plaintext of at most 4096 bytes).

## Non-vacuity

* `size_witness_laws_model` puts every law in one interpretation, `InterpO.modelPadded`; `size_witness_reachable`
  exhibits, under those laws at the real constants, a successful receive at which `hstep`, `hok` and `hopen` of the
  received maximum hold together. In the substitution sense of `UnitSatisfiabilityRecords`: it shows the hypothesis set
  is consistent, not that the shipping AEAD meets it.

## What it does not show

* that the shipping AEAD meets the open-length law (read, not proved, to behave so; that reading closes nothing; the
  toy shows consistency only);
* a witness for the other received-maximum results (`ratchet_ok_plaintext_le_max`,
  `establish_responder_ok_plaintext_le_max`) or for the other eleven reply-route results that take `hfitR` or `hfitS`;
* a reply plaintext longer than 4096 bytes, or the one-time path;
* a repeated initial frame, for which nothing supplies the received maximum's `hstep`;
* the fifteen reply plaintext lengths of `SIZE-BOUND-REPLY-ROUTE-GAP`;
* that the toy AEAD encrypts or authenticates anything: it is the plaintext, its padding and 32 zero bytes.
-/

open Aeneas Aeneas.Std Result
open tacenta_session_unit

namespace Tacenta.UnitLifecycleSizeWitness

open Tacenta.UnitSatisfiabilityJoint (Interp Interp.real)

/-- The number of padding bytes PKCS#7 adds to an `n`-byte plaintext with 16-byte blocks: 1 to 16. -/
def padLen (n : Nat) : Nat := 16 - n % 16

theorem padLen_pos (n : Nat) : 1 ≤ padLen n := by unfold padLen; omega
theorem padLen_le (n : Nat) : padLen n ≤ 16 := by unfold padLen; omega
/-- The padded plaintext and the 32-byte tag take `16 * (n / 16) + 48` bytes. -/
theorem padded_total (n : Nat) : n + padLen n + 32 = 16 * (n / 16) + 48 := by unfold padLen; omega

/-- The byte of value `k`, for `k < 256`. -/
def byteOf (k : Nat) : U8 := UScalar.ofNat (k % 256) (by simp [UScalar.cMax, UScalar.rMax, U8.rMax]; omega)

theorem byteOf_toNat (k : Nat) (hk : k < 256) : (byteOf k).bv.toNat = k := by
  simp [byteOf, UScalar.ofNat]
  omega

/-- The toy sealed bytes: the plaintext, its PKCS#7 padding, and 32 zero bytes for the tag. -/
def padBody (p : List U8) : List U8 :=
  p ++ List.replicate (padLen p.length) (byteOf (padLen p.length)) ++ List.replicate 32 0#u8

theorem padBody_length (p : List U8) : (padBody p).length = p.length + padLen p.length + 32 := by
  simp [padBody]; omega

/-- **The padded toy seal**: the plaintext, its PKCS#7 padding and a 32-byte all-zero tag, `16 * (n / 16) + 48` bytes
for an `n`-byte plaintext, where that fits a `usize` length; the plaintext itself otherwise (a totality fallback the
round trip's length premise excludes).  It encrypts nothing and authenticates nothing. -/
def padSeal (p : Slice U8) : alloc.vec.Vec U8 :=
  if h : p.val.length + 48 ≤ Usize.max then
    ⟨padBody p.val, by rw [padBody_length]; have := padLen_le p.val.length; omega⟩
  else ⟨p.val, p.property⟩

/-- **The padded toy open**: an input of at least 33 bytes whose byte before the 32-byte tag is a padding length `b`
with `1 ≤ b` and `b + 32` at most the input's length opens to its first `length - 32 - b` bytes; every other input
is refused.  The tag is not checked. -/
def padOpen (c : Slice U8) : core.result.Result (alloc.vec.Vec U8) Unit :=
  match (c.val.drop (c.val.length - 33)).head? with
  | some b =>
      if 33 ≤ c.val.length ∧ 1 ≤ b.bv.toNat ∧ b.bv.toNat + 32 ≤ c.val.length then
        .Ok ⟨c.val.take (c.val.length - 32 - b.bv.toNat), by
          have := c.property; simp only [List.length_take]; omega⟩
      else .Err ()
  | none => .Err ()

/-- **What the toy open returns is at least 33 bytes shorter than its input.** -/
theorem padOpen_length (c : Slice U8) (v : alloc.vec.Vec U8) (h : padOpen c = .Ok v) :
    v.val.length + 33 ≤ c.val.length := by
  unfold padOpen at h
  split at h
  · rename_i b _
    split at h
    · rename_i hc
      simp only [core.result.Result.Ok.injEq] at h
      subst h
      simp only [List.length_take]
      omega
    · cases h
  · cases h

theorem padBody_drop (p : List U8) :
    (padBody p).drop ((padBody p).length - 33) = byteOf (padLen p.length) :: List.replicate 32 0#u8 := by
  have hk1 := padLen_pos p.length
  rw [padBody_length]
  have e : p.length + padLen p.length + 32 - 33 = p.length + (padLen p.length - 1) := by omega
  have e2 : padLen p.length - (padLen p.length - 1) = 1 := by omega
  rw [e, padBody, List.append_assoc, List.drop_append, List.drop_eq_nil_of_le (by omega), List.nil_append,
    Nat.add_sub_cancel_left, List.drop_append_of_le_length (by simp), List.drop_replicate, e2]
  rfl

theorem padBody_take (p : List U8) :
    (padBody p).take ((padBody p).length - 32 - padLen p.length) = p := by
  rw [padBody_length, show p.length + padLen p.length + 32 - 32 - padLen p.length = p.length by omega,
    padBody, List.append_assoc, List.take_left']
  rfl

/-- The toy open of the toy sealed bytes of `p` returns `p`. -/
theorem padOpen_of_body (c : Slice U8) (p : List U8) (hp : p.length ≤ Usize.max) (hc : c.val = padBody p) :
    padOpen c = .Ok ⟨p, hp⟩ := by
  have hk1 := padLen_pos p.length
  have hk2 := padLen_le p.length
  have hb : (byteOf (padLen p.length)).bv.toNat = padLen p.length := byteOf_toNat _ (by omega)
  obtain ⟨cv, hcv⟩ := c
  simp only at hc
  subst hc
  unfold padOpen
  simp only [padBody_drop, List.head?_cons, hb]
  rw [if_pos ⟨by rw [padBody_length]; omega, hk1, by rw [padBody_length]; omega⟩]
  simp only [padBody_take]

/-- **The toy open returns what the toy seal was given**, when the sealed output fits a `usize` length. -/
theorem padOpen_padSeal (p : Slice U8) (hlen : p.val.length + 48 ≤ Usize.max) :
    padOpen (alloc.vec.Vec.deref (padSeal p)) = .Ok ⟨p.val, p.property⟩ :=
  padOpen_of_body _ _ _ (by simp [padSeal, hlen, alloc.vec.Vec.deref])


/-! ## The padded joint model -/

section JointModel

open Tacenta.UnitLifecycleT3 (arrayOf)
open Tacenta.UnitLifecycleIntegrationScreen (byteRng byteCrc byteTrace)
open Tacenta.UnitLifecycleResponderFirstFrame (DhAgreeSymmetricShape FirstFrameSuccessShape PoolEntry
  basePoint_ne_zero)
open Tacenta.UnitLifecycleResponderFirstReceipt (AeadRoundTripShape DhAgreeContributoryShape)
open Tacenta.UnitLifecycleResponderReplyReceipt (replyPub replyPub_canonical replyPub_zeros
  DhPublicNotConstantShape)
open Tacenta.UnitLifecycleEstablishedEncrypt (toyKemR zeroSeed oneSeed EncryptExtraLawsShape
  established_encrypt_laws_model encapResult encapFill)
open Tacenta.UnitLifecycleDecryptRatchetScreen (DhViewShape)
open Tacenta.UnitOracleShape (InterpO DhViewOf KemViewOf)

/-- `Interp.modelReply` (the reply receipt's joint model) with the padded toy seal and open.  Every other field is
`Interp.modelReply`'s. -/
noncomputable def Interp.modelPadded : Interp :=
  { Tacenta.UnitLifecycleResponderReplyReceipt.Interp.modelReply with
    aeadEncrypt := fun _ _ _ p _ => ok (padSeal p)
    aeadDecrypt := fun _ _ _ c _ => ok (padOpen c) }

/-- The joint interpretation with its signing function. -/
noncomputable def InterpO.modelPadded : InterpO :=
  { Interp.modelPadded with xeddsaSign := Tacenta.UnitOracleModel.signModelO }

/-- The view of the joint interpretation: both key types are their bytes. -/
def viewPadded : DhViewShape Interp.modelPadded := ⟨arrayOf, arrayOf⟩
/-- The DH view of the joint interpretation with its signing function. -/
def dhViewPadded : DhViewOf InterpO.modelPadded.toInterp := ⟨viewPadded.privateKey, viewPadded.publicKey⟩
/-- The KEM view of the joint interpretation with its signing function. -/
def kemViewPadded : KemViewOf InterpO.modelPadded.toInterp := ⟨fun _ => []⟩

/-- The open-length law over an interpretation: what a successful open returns is at least 33 bytes shorter than
its input (ciphertext and 32-byte tag), the code-level form of `Model.Lifecycle.AeadOpenLength`. -/
def AeadOpenLengthShape (I : Interp) : Prop :=
  ∀ (k1 k2 : Array U8 32#usize) (iv : Array U8 16#usize) (c ad : Slice U8) (v : alloc.vec.Vec U8),
    I.aeadDecrypt k1 k2 iv c ad = ok (core.result.Result.Ok v) → v.val.length + 33 ≤ c.val.length

/-- **Assumed law**: `AeadOpenLengthShape` at the real constants. -/
def AeadOpenLengthLaw : Prop := AeadOpenLengthShape Interp.real

/-- At the real constants, `AeadOpenLengthLaw` is the statement about the real open. -/
theorem aeadOpenLengthLaw_is : AeadOpenLengthLaw ↔
    ∀ (k1 k2 : Array U8 32#usize) (iv : Array U8 16#usize) (c ad : Slice U8) (v : alloc.vec.Vec U8),
      tacenta_boundary.aead.decrypt k1 k2 iv c ad = ok (core.result.Result.Ok v) →
        v.val.length + 33 ≤ c.val.length := Iff.rfl

theorem modelPadded_dhCodec : Tacenta.UnitSatisfiabilityJoint.DhCodecShape Interp.modelPadded :=
  Tacenta.UnitLifecycleResponderReplyReceipt.modelReply_dhCodec
theorem modelPadded_dhAgree : Tacenta.UnitSatisfiabilityJoint.DhAgreeShape Interp.modelPadded :=
  Tacenta.UnitLifecycleResponderReplyReceipt.modelReply_dhAgree
theorem modelPadded_symmetric : DhAgreeSymmetricShape Interp.modelPadded :=
  Tacenta.UnitLifecycleResponderReplyReceipt.modelReply_symmetric
theorem modelPadded_contributory : DhAgreeContributoryShape Interp.modelPadded :=
  Tacenta.UnitLifecycleResponderReplyReceipt.modelReply_contributory
theorem modelPadded_notConstant : DhPublicNotConstantShape Interp.modelPadded :=
  Tacenta.UnitLifecycleResponderReplyReceipt.modelReply_notConstant

/-- The padded open returns. -/
theorem modelPadded_aeadOpen : Tacenta.UnitSatisfiabilityJoint.AeadOpenShape Interp.modelPadded :=
  fun _ _ _ _ _ => ⟨_, rfl⟩

/-- The padded seal returns at most 48 bytes more than the plaintext. -/
theorem modelPadded_aeadSeal : Tacenta.UnitSatisfiabilityJoint.AeadSealBoundedShape Interp.modelPadded := by
  intro ek mk iv plaintext ad
  refine ⟨padSeal plaintext, rfl, ?_⟩
  unfold padSeal
  split
  · rw [padBody_length]; have := padLen_le plaintext.val.length; omega
  · simp

/-- **`AeadRoundTripShape` holds at the padded model**: the padded open returns what the padded seal was given. -/
theorem modelPadded_aeadRoundTrip : AeadRoundTripShape Interp.modelPadded := by
  intro k1 k2 iv pt ad ct hlen h
  have h' : ok (padSeal pt) = ok ct := h
  injection h' with h''
  subst h''
  exact ⟨⟨pt.val, pt.property⟩, congrArg ok (padOpen_padSeal pt hlen), rfl⟩

/-- **`AeadOpenLengthShape` holds at the padded model**: the padded open drops the tag and at least one padding
byte. -/
theorem modelPadded_openLength : AeadOpenLengthShape Interp.modelPadded := by
  intro k1 k2 iv c ad v h
  have h' : ok (padOpen c) = ok (core.result.Result.Ok v) := h
  injection h' with h''
  exact padOpen_length c v h''

open Tacenta.UnitSatisfiabilityJoint (InitiatorAxiom ResponderAxiom) in
open Tacenta.UnitLifecycleSessionCodec (ZeroizingVecRoundTripShape DhPrivateBytesRoundTripShape
  DhPublicBytesRoundTripShape OptionBranchSomeShape VecAsSliceShape optionBranchImpl vecAsSliceImpl) in
open Tacenta.UnitLifecycleRestoredSession (KemCiphertextLenBoundShape) in
open Tacenta.UnitLifecycleEstablishInitiatorShape (InitiatorSuccessShape DhPublicValidShape
  KemCiphertextLenLawShape) in
/-- **Every law of the reply receipt's joint model holds again in `InterpO.modelPadded`, together with
`AeadOpenLengthShape`**: the conjuncts of `reply_receipt_laws_model`, in the same order, at the interpretation whose
AEAD is the padded toy, then the open-length law.  In the substitution sense of `UnitSatisfiabilityRecords`; not a
statement that the real primitives meet them, and the toy AEAD encrypts and authenticates nothing. -/
theorem size_witness_laws_model :
    Tacenta.UnitLifecycleDecryptScreen.DecryptJointLawsShape Interp.modelPadded viewPadded toyKemR
        @Tacenta.UnitHeadroomInvariant.optionEqImpl ∧
      Nonempty (InitiatorAxiom Interp.modelPadded byteRng) ∧
      InitiatorSuccessShape Interp.modelPadded byteRng byteCrc ∧
      DhPublicValidShape Interp.modelPadded ∧
      KemCiphertextLenLawShape (ok 0#usize) Interp.modelPadded ∧
      EncryptExtraLawsShape InterpO.modelPadded dhViewPadded kemViewPadded toyKemR (ok 0#usize) ∧
      (ZeroizingVecRoundTripShape Interp.modelPadded ∧
        DhPrivateBytesRoundTripShape Interp.modelPadded ∧
        DhPublicBytesRoundTripShape Interp.modelPadded ∧ OptionBranchSomeShape @optionBranchImpl ∧
        VecAsSliceShape @vecAsSliceImpl ∧ KemCiphertextLenBoundShape (ok 0#usize)) ∧
      Tacenta.UnitLifecycleEstablishedEncrypt.KeyGenSizesOf toyKemR ∧
      toyKemR.keyGen (Model.Lifecycle.braidRandomness
          (zeroSeed.map Tacenta.SessionUnitBraidT3.u8)) = none ∧
      toyKemR.keyGen (Model.Lifecycle.braidRandomness
          (oneSeed.map Tacenta.SessionUnitBraidT3.u8)) ≠ none ∧
      Nonempty (ResponderAxiom Interp.modelPadded byteRng) ∧
      Tacenta.UnitLifecycleEstablishResponder.ResponderSuccessShape Interp.modelPadded ∧
      Tacenta.UnitLifecycleEstablishResponder.ZeroKeyShape Interp.modelPadded ∧
      DhAgreeSymmetricShape Interp.modelPadded ∧
      FirstFrameSuccessShape Interp.modelPadded (fun _ => ok (alloc.vec.Vec.new U8))
        (fun _ v => ok (decide (v.val = []))) ∧
      AeadRoundTripShape Interp.modelPadded ∧ DhAgreeContributoryShape Interp.modelPadded ∧
      DhPublicNotConstantShape Interp.modelPadded ∧ AeadOpenLengthShape Interp.modelPadded := by
  obtain ⟨M, ⟨A⟩, -, -, C, X, ⟨r1, r2, r3, r4, r5, r6⟩, ks, s0, s1⟩ := established_encrypt_laws_model
  obtain ⟨-, ⟨RA⟩, -, -, -⟩ := Tacenta.UnitLifecycleEstablishResponder.responder_route_laws_model
  have hcodec := modelPadded_dhCodec
  have hagree := modelPadded_dhAgree
  have hb := basePoint_ne_zero
  refine ⟨?_, ⟨?_⟩, ?_, ?_, ?_, ?_, ⟨?_, ?_, ?_, r4, r5, r6⟩, ks, s0, s1, ⟨?_⟩, ?_, ?_,
    modelPadded_symmetric, ?_, modelPadded_aeadRoundTrip, modelPadded_contributory, modelPadded_notConstant, modelPadded_openLength⟩
  · exact
      { dhCodec := hcodec
        dhAgree := hagree
        aeadOpen := modelPadded_aeadOpen
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
      simpa [Interp.modelPadded, Tacenta.UnitLifecycleResponderReplyReceipt.Interp.modelReply] using h.symm
    subst hp
    exact ⟨replyPub k, rfl, replyPub_canonical k, rfl⟩
  · exact C
  · exact
      { oracle :=
          { dhCodec := hcodec
            dhAgree := hagree
            dhIdentity := X.oracle.dhIdentity
            aeadSeal := modelPadded_aeadSeal
            aeadOpen := modelPadded_aeadOpen
            kemDecapsulate := X.oracle.kemDecapsulate
            xeddsaVerify := X.oracle.xeddsaVerify
            signLaw := X.oracle.signLaw
            kemLaw := X.oracle.kemLaw
            dhView := X.oracle.dhView
            kemView := X.oracle.kemView }
        encrypt :=
          { braid := by have h := X.encrypt.braid; cases h; constructor <;> assumption
            triple := by have h := X.encrypt.triple; cases h; constructor <;> assumption
            aeadSeal := modelPadded_aeadSeal
            messageKeyMaterial := X.encrypt.messageKeyMaterial
            dhCodec := hcodec }
        keyGen := X.keyGen
        zeroizingKeys := X.zeroizingKeys
        ciphertextBound := X.ciphertextBound }
  · exact r1
  · exact r2
  · exact r3
  · exact
      { decrypt := ⟨hcodec, hagree, modelPadded_aeadOpen, RA.decrypt.random32,
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

end JointModel


/-! ## The oracle of the laws meets the open-length law -/

section Oracle

open Tacenta.UnitLifecycleT3
open Tacenta.UnitOracleShape
open Tacenta.UnitOracleModel
open Tacenta.UnitOracleKemSig (KemGuardedClause OracleOfGuarded kemGuardedClause_of_law
  oracleOfGuarded_iff_shape key1568)
open Tacenta.UnitOracleJoint
open Tacenta.UnitSatisfiabilityJoint (Interp DhCodecShape DhAgreeShape DhIdentityShape
  AeadSealBoundedShape AeadOpenShape KemDecapsulateShape XeddsaVerifyShape)
open Tacenta.UnitLifecycleIntegrationScreen (byteRng byteCrc byteTrace SignFillsOnce64Of
  KemShapeOf kemClauses_of_law sigSignClause_of_law byte_random32Clause kemModelValid)

/-- **The oracle the laws build meets the open-length law** when the interpretation's open does: at an input with
a preimage under the views it is the open of that preimage, whose result is at least 33 bytes shorter, and elsewhere
it refuses. -/
theorem aeadOpenLength_oracleOfLaws (I : InterpO) (dh : DhViewOf I.toInterp) (kem : KemViewOf I.toInterp)
    (valid : Model.Lifecycle.Bytes → Bool)
    (E : Model.Lifecycle.Bytes → Model.Lifecycle.Bytes → alloc.vec.Vec Std.U8 × Array Std.U8 32#usize)
    (S : Array Std.U8 32#usize → Slice Std.U8 → Slice Std.U8 → Array Std.U8 64#usize)
    (h : AeadOpenLengthShape I.toInterp) :
    Model.Lifecycle.AeadOpenLength (oracleOfLaws I dh kem valid E S) := by
  intro enc mac iv input ad pt hopen
  simp only [oracleOfLaws] at hopen
  unfold liftView at hopen
  split at hopen
  · rename_i hex
    have hspec := hex.choose_spec
    generalize hex.choose = x at hopen hspec
    obtain ⟨k1, k2, n, c, a⟩ := x
    simp only [Prod.map, Prod.mk.injEq] at hspec
    obtain ⟨-, -, -, hc, -⟩ := hspec
    cases hf : I.aeadDecrypt k1 k2 n c a with
    | ok r =>
      simp only [hf, okVal, Option.map_some, Option.getD_some] at hopen
      cases r with
      | Ok v =>
        simp only [resultOptionOf, Option.some.injEq] at hopen
        subst hopen hc
        have := h k1 k2 n c a v hf
        simpa [vecOf, sliceOf] using this
      | Err _ => simp [resultOptionOf] at hopen
    | fail e => simp [hf, okVal] at hopen
    | div => simp [hf, okVal] at hopen
  · cases hopen


/-- `UnitOracleJoint.oracleOfShape_of_oracleLaws` with the open-length law: the oracle the laws build has every
clause of `OracleOf` and, when the interpretation's open meets `AeadOpenLengthShape`, `AeadOpenLength`. -/
theorem oracleOfShape_open (I : InterpO) (dh : DhViewOf I.toInterp)
    (kem : KemViewOf I.toInterp) (h : OracleLaws I dh kem) (hlen : AeadOpenLengthShape I.toInterp) :
    ∃ oracle : Model.Lifecycle.Oracle,
      OracleOfShape I byteRng byteCrc dh kem byteTrace oracle ∧
      Model.Lifecycle.AeadOpenLength oracle := by
  obtain ⟨S, hS⟩ := h.signLaw
  obtain ⟨valid, E, hK⟩ := h.kemLaw
  let oracle := oracleOfLaws I dh kem valid E S
  refine ⟨oracle, (oracleOfShape_iff_clauses I byteRng byteCrc dh kem byteTrace oracle).mpr
    ⟨dhPublicClause_of_laws I dh kem valid E S h.dhCodec h.dhView.1,
     dhAgreeClause_of_laws I dh kem valid E S h.dhAgree h.dhView,
     identityValidClause_of_laws I dh kem valid E S h.dhCodec h.dhIdentity h.dhView.2,
     aeadSealClause_of_laws I dh kem valid E S h.aeadSeal,
     aeadOpenClause_of_laws I dh kem valid E S h.aeadOpen,
     kemClauses_of_law valid E (I.kemEncapsulate byteRng byteCrc)
       (fun pk rng => hK byteRng byteCrc pk rng) oracle rfl rfl,
     kemDecapsulateClause_of_laws I dh kem valid E S h.kemDecapsulate h.kemView,
     sigVerifyClause_of_laws I dh kem valid E S h.xeddsaVerify h.dhView.2,
     sigSignClause_of_law S (I.xeddsaSign byteRng byteCrc)
       (fun secret message rng => hS byteRng byteCrc secret message rng) oracle rfl,
     byte_random32Clause⟩,
    aeadOpenLength_oracleOfLaws I dh kem valid E S hlen⟩

end Oracle

/-! ## The encrypt premises together, with the open-length law -/

section Established

open Tacenta.UnitLifecycleT3
open Tacenta.UnitLifecycleEstablishInitiatorShape
open Tacenta.UnitLifecycleDecryptRatchetT3 (DecryptRatchetAgreements)
open Tacenta.UnitSatisfiabilityJoint (Interp Interp.real)
open Tacenta.UnitLifecycleRestoredSession (KemCiphertextLenBound)
open Tacenta.UnitLifecycleEstablishedEncrypt
open Tacenta.UnitLifecycleIntegrationScreen (byteRng byteCrc byteTrace)
open Tacenta.UnitSatisfiabilityJoint (InitiatorAxiom EncryptAxiom)
open Tacenta.UnitOracleShape (InterpO InterpO.real DhViewOf KemViewOf dhViewOf kemViewOf)
open Tacenta.UnitOracleJoint (OracleLaws)

/-- **`established_encrypt_hypotheses_jointly_satisfiable` with the open-length law**: under its laws and
`AeadOpenLengthLaw`, the same witness, whose oracle (the one the laws build) also meets `AeadOpenLength`. -/
theorem established_encrypt_hypotheses_open (K : Model.Braid.Kem) (dh : DhView)
    (kem : KemView) (L : Tacenta.UnitLifecycleDecryptScreen.DecryptJointLaws K dh)
    (A : Nonempty (InitiatorAxiom Interp.real byteRng))
    (S : InitiatorSuccessShape Interp.real byteRng byteCrc)
    (hpub : DhPublicValid) (hct : KemCiphertextLenOf) (X : EncryptExtraLaws K dh kem)
    (hopenLen : AeadOpenLengthLaw)
    (our : lifecycle.Identity) (seed : List Std.U8) (hseed : 64 ≤ seed.length) :
    ∃ (oracle : Model.Lifecycle.Oracle) (bundle : lifecycle.PublishedBundle) (s : lifecycle.Session)
      (rng1 : List Std.U8),
      oracle.braidKem = K ∧ oracle.draws = byteTrace seed ∧ Model.Lifecycle.AeadOpenLength oracle ∧
      EstablishedEncryptHypotheses byteRng byteCrc byteTrace dh kem
        Tacenta.UnitLifecycleRepair.witnessView oracle byteRng byteCrc our bundle
        bundle.bundle.identity_key [] rng1 s emptyPlaintext seed := by
  obtain ⟨oracle0, bundle, s, rng1, hK0, H0⟩ :=
    Tacenta.UnitLifecycleEstablishedDecrypt.established_decrypt_hypotheses_jointly_satisfiable K dh L A
      S hpub hct our
  have D := H0 Tacenta.UnitLifecycleRepair.witnessView
  have ag : DecryptRatchetAgreements K := hK0 ▸ D.agreements
  have E : Tacenta.UnitLifecycleT1.EncryptContracts byteRng :=
    Tacenta.UnitSatisfiabilityRecords.encrypt_contracts_of_axiom_base byteRng X.encrypt L.laws
  obtain ⟨oracle1, hshape, hlen1⟩ :=
    oracleOfShape_open InterpO.real (dhViewOf dh) (kemViewOf kem) X.oracle hopenLen
  have hO : OracleOf byteRng byteCrc dh kem byteTrace oracle1 :=
    (Tacenta.UnitOracleShape.oracleOf_iff_shape byteRng byteCrc dh kem byteTrace oracle1).mpr hshape
  let oracle : Model.Lifecycle.Oracle := { oracle1 with draws := byteTrace seed, braidKem := K }
  have hOracle : OracleOf byteRng byteCrc dh kem byteTrace oracle :=
    ⟨hO.dhPublic, hO.dhAgree, hO.identityValid, hO.aeadSeal, hO.aeadOpen, hO.kemEncapsulateSuccess,
      hO.kemInvalidKey, hO.kemEncapsulateError, hO.kemDecapsulate, hO.sigVerify, hO.sigSign,
      hO.random32⟩
  refine ⟨oracle, bundle, s, rng1, rfl, rfl, hlen1, ?_⟩
  exact
    { braid :=
        { hka := ag.kem, hea := ag.erasure, hmac := ag.hmac, hkdf := ag.hkdf
          header := E.braid.keyPairHeader, ekVector := D.contracts.braid.keyPairEkVector
          ct1Len := D.contracts.braid.ct1Len, ct2Len := D.contracts.braid.ct2Len
          kemClone := ag.kemClone
          erasureClone := Tacenta.UnitSatisfiabilityErasureAgrees.erasureCloneAgrees
          encoderClone := E.braid.encoderClone, decoderClone := E.braid.decoderClone
          keyPairClone := E.braid.keyPairClone, encapsStateClone := E.braid.encapsStateClone
          zeroizingArray := E.braid.zeroizingArray, arrayZeroize := E.braid.arrayZeroize
          rangeFullIndex := E.braid.rangeFullIndex, rng := E.braid.rng
          keyPairGenerate := E.braid.keyPairGenerate, encoderNew := E.braid.encoderNew
          encoderNext := E.braid.encoderNext, encapsulate1 := E.braid.encapsulate1 }
      triple :=
        { hmac := ag.hmac, hkdf := ag.hkdf, zeroizing := ag.zeroizing64
          ratchetRemove := D.contracts.triple.ratchetRemove, spqrZeroizing96 := ag.zeroizing96
          spqrZeroizing64 := ag.zeroizingSparse64
          vecRetain := ag.vecRetainAgrees D.contracts.triple
          vecRetainTotal := D.contracts.triple.vecRetain
          spqrRemove := Tacenta.UnitSatisfiabilitySpqrSessionLaws.removeSkippedAtAgrees_of_laws
            D.contracts.triple.spqrZeroize ag.pop
          spqrZeroize := D.contracts.triple.spqrZeroize
          optionClone := D.contracts.triple.optionClone }
      derivedKeys := D.derivedKeys
      aead := E.aeadSeal
      dhCodec := E.dhCodec
      oracleOf := hOracle
      codec := D.codec
      codewordView := Tacenta.UnitLifecycleRepair.witnessView_send
      zeroizing80 := ag.zeroizing80
      zeroizing32 := ag.zeroizing32
      zeroizingKeys := zeroizingKeys_is.mpr X.zeroizingKeys
      keyGen := X.keyGen
      kemCiphertextLen := hct
      kemCiphertextBound := X.ciphertextBound
      established := D.established
      room := by
        have := Tacenta.SessionUnitSessionT1.small_le_usize_max (n := 65770) (by decide)
        simpa [emptyPlaintext] using this
      trace_eq := rfl
      draws := ⟨_, _, _, byteTrace_two seed hseed⟩ }

end Established


/-! ## The receipt of the reply, as a step refinement -/

section Step

open Tacenta.UnitLifecycleResponderReplyReceipt
open Tacenta.UnitLifecycleT3 (DhView DhCodecOf KemView arrayOf vecOf sliceOf SessionRefines OracleOf StepRefines
  ResultRefines)
open Tacenta.UnitLifecycleResponderFirstReceipt (senderAfterFirst firstHeader firstKey firstOpen
  decode_encodeMessage)
open Tacenta.UnitLifecycleResponderReply (replyComposite replyFrame)
open Tacenta.UnitLifecycleT3 (BraidSendRefinementContracts TripleSendRefinementContracts CodewordViewSendOf
  ZeroizingRoundTrips)
open Tacenta.UnitLifecycleResponderFirstReceipt (headerSource DhAgreeContributory AeadRoundTrip aead_open_sealed)
open Tacenta.UnitLifecycleResponderFirstFrame (InitiatorSecretParts DhAgreeSymmetric PrekeyIdsDistinct
  FirstKemAgrees)
open Tacenta.UnitLifecycleDecryptRatchetT3 (DecryptOracleOf DecryptRatchetAgreements)
open Tacenta.UnitLifecycleEstablishInitiatorShape (DhPublicValid establishedModelOf)
open Tacenta.UnitLifecycleResponderReply (replyKey oracleOf_with_draws initiator_first_send_responder_replies)

/-- **The initiator's receipt of the reply refines the model's step**, on the run of the initiator's first send:
under the hypotheses of `initiator_receives_reply_outcomes`, the responder's `encrypt` returns bytes and the
initiator's public `decrypt` of them returns an output related by `StepRefines` to the model's public `decrypt` at the
model session the first send left, with the oracle holding the draws the initiator's source holds.  The first steps
of the proof of `initiator_receives_reply_outcomes`, which applies `decrypt_refines_ratchet_frame_of_counter_headroom`
there and keeps only the outcomes; this keeps the step, which the received maximum takes as a hypothesis. -/
theorem initiator_receives_reply_step [Tacenta.SessionUnitT1.DerivedKeysModel] {R E F : Type}
    (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R)
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
    (ptR : Slice Std.U8) (hroomR : 102 + (ptR.val.length + 48) ≤ Usize.max)
    (hfitR : (Tacenta.UnitLifecycleT3.sliceOf ptR).length + 150 ≤ Model.Lifecycle.maxRatchetFrameLen) (rngR : F) :
    ∃ (bytesR : alloc.vec.Vec Std.U8) (sB'' : lifecycle.Session) (mA : Model.Lifecycle.Session)
      (output : core.result.Result (alloc.vec.Vec Std.U8) lifecycle.Error × lifecycle.Session × R),
      lifecycle.Session.encrypt rcB crcB sB' ptR rngR = ok (core.result.Result.Ok bytesR, sB'', rngR) ∧
      lifecycle.Session.decrypt rc crc s' (alloc.vec.Vec.deref bytesR) rng' = ok output ∧
      StepRefines trace dh oracle.braidKem output
        (Model.Lifecycle.decrypt view { oracle with draws := trace rng' } mA
          (sliceOf (alloc.vec.Vec.deref bytesR))) := by
  have hlenR : (UnitLifecycleT3.sliceOf ptR).length ≤ Model.Lifecycle.maxPlaintextLen := by
    rw [Model.Lifecycle.maxRatchetFrameLen_value] at hfitR
    simp only [Model.Lifecycle.maxPlaintextLen]; omega
  -- the responder's reply, on the run
  obtain ⟨p, ec, dSend, dk, ekSeed, ekVector, bytesR, sB'', hkg, hkdf, hagreeB, -, hrelB0, hcallR, -, -, -, hbytes,
    -⟩ := initiator_first_send_responder_replies rc crc trace dh kem view oracle braid triple aead dhCodec oracleOf
      codec codewordView hz80 hz32 hzKeys hgen hsizes hct hbound rcE crcE ourA bundleA expected rng0 rng1 s h q hq
      plaintext hroom rng htrace d1 d2 rest hdraws bytes s' rng' hcall rcB crcB contracts hpub hsym hcon haead hrt
      hoeq traceB oracleB oracleOfB braidB agreements ourB storeB hpublish hidentity hdistinct hkem rngB htraceB dB
      restB hdrawB ptB sB' storeB' rngB' hcallB ptR hroomR hlenR rngR
  -- the session the initiator's first send left: invariant, relation, ceilings, honest chunks
  obtain ⟨hinv, hrel, hc, hhonest⟩ :=
    Tacenta.UnitLifecycleEstablishedEncrypt.established_encrypt_successor_hypotheses rc crc trace dh kem view
      oracle braid triple aead dhCodec oracleOf codec codewordView hz80 hz32 hzKeys hgen hct hbound hpub hoeq
      agreementsA.kemLen agreementsA.validateEk hsizes contracts.divCeilValue rcE crcE ourA bundleA expected rng0
      rng1 s h plaintext hroom rng htrace ⟨d1, d2, rest, hdraws⟩ bytes s' rng' hcall
  subst hq
  have hfits := Tacenta.UnitLifecycleT3.encrypt_ok_plaintext_fits rc crc q.session plaintext rng bytes s' rng'
    hcall
  obtain ⟨encoder, hmA⟩ := first_send_model_session dh view oracle q (sliceOf plaintext) hfits d1 d2 rest
    (htrace.symm.trans hdraws) dk ekSeed ekVector hkg
  -- the responder's fresh ratchet key and the initiator's first agreement with it
  obtain ⟨-, k, pk, b, -, -, hkd, hpk, -, hcan, hpkb, hnew⟩ :=
    fresh_public_of_draw hpub codec (DecryptOracleOf.of_oracleOf oracleOfB) rngB dB restB hdrawB
  let oracleA : Model.Lifecycle.Oracle := { oracle with draws := trace rng' }
  have oracleOfA : DecryptOracleOf rc crc dh trace oracleA :=
    DecryptOracleOf.of_oracleOf (oracleOf_with_draws oracleOf _)
  have hagreeA : oracleA.dhAgree (dh.privateKey q.ratchetPrivate) (oracleB.dhPublic dB) = some dSend := by
    rw [← hagreeB, hnew, ← hpkb, ← hkd]
    exact initiator_reply_agreement hsym codec oracleOfA (DecryptOracleOf.of_oracleOf oracleOfB) q k pk hpk
  have hlen : (oracleB.dhPublic dB).length = 32 := by rw [hnew]; simp [arrayOf]
  have hkey : Model.Messages.checkKey (oracleB.dhPublic dB) = some () := by
    rw [hnew]
    simp [Model.Messages.checkKey, Tacenta.UnitLifecycleResponderFirstFrame.canonicalKey_arrayOf _ hcan]
  -- the reply bytes, in the key the initiator's receive derives
  have hrk : replyKey (arrayOf ec) (arrayOf q.sparseReceive) (arrayOf q.dhOut) dSend =
      firstKey (Model.State.kdfRk (arrayOf q.rootKey) dSend .tacenta).2 (arrayOf q.sparseReceive) := by
    simp only [replyKey, hkdf]
  rw [hrk] at hbytes
  have hmsg : sliceOf (alloc.vec.Vec.deref bytesR) = vecOf bytesR := rfl
  rw [← hmsg] at hbytes
  -- the reply passes the initiator's size rule
  have hpendB : sB'.pending_initial = none := by
    have h := hrelB0.pendingInitial
    simpa [Tacenta.UnitLifecycleResponderFirstReceipt.firstReceiptSession,
      Tacenta.UnitLifecycleEstablishResponder.responderModelOf] using h
  have hsizeR := Tacenta.UnitLifecycleEstablishedEncrypt.reply_fits rcB crcB aead dhCodec sB' hpendB ptR rngR
    bytesR sB'' rngR (by rw [← Tacenta.UnitLifecycleT3.sliceOf_length]; exact hfitR) hcallR
  rw [hbytes] at hsizeR
  -- the decrypt refinement at that session, with the run's inputs
  let mA := (Model.Lifecycle.encrypt view oracle (establishedModelOf dh q.session) (sliceOf plaintext)).session
  have hadA : mA.identityAd = vecOf q.identityAd := by simp only [mA, hmA]; rfl
  have inputs : Tacenta.UnitLifecycleDecryptRunBounds.DecryptRatchetRunInputs view oracleA trace s' mA
      (alloc.vec.Vec.deref bytesR) rng' := by
    refine ⟨?_, fun mc ct _ => hhonest _, ⟨dA, restA, hdrawA⟩⟩
    intro rcomp mcomp ct hd hcr
    rw [hbytes, replyFrame_decodeDetailed _ _ _ _ _ hlen hkey] at hd
    simp only [Except.ok.injEq, Prod.mk.injEq] at hd
    obtain ⟨rfl, -⟩ := hd
    have hag := hcr.agChunk
    unfold Tacenta.UnitLifecycleT3.IncomingChunkRefines
    simp only [replyComposite] at hag ⊢
    rcases hrc : rcomp.ag_chunk with _ | rch
    · trivial
    · rw [hrc] at hag; exact hag.elim
  have hframe : Model.Lifecycle.messageType (sliceOf (alloc.vec.Vec.deref bytesR)) ≠ some .initial := by
    rw [hbytes, replyFrame_messageType]; simp
  obtain ⟨output, hcallA, hstep⟩ :=
    Tacenta.UnitLifecycleDecryptT3.decrypt_refines_ratchet_frame_of_counter_headroom rc crc trace dh view oracleA
      oracleOfA codec contractsA agreementsA s' mA (alloc.vec.Vec.deref bytesR) rng' hframe hinv hrel hc rfl inputs
  exact ⟨bytesR, sB'', mA, output, hcallR, hcallA, hstep⟩

end Step


/-! ## The reach: one run at which the received maximum's hypotheses and the reply receipt's hold together -/

section Reach

open Tacenta.UnitLifecycleResponderReplyReceipt
open Tacenta.UnitLifecycleT3 (arrayOf vecOf sliceOf StepRefines)
open Tacenta.UnitSatisfiabilityJoint (Interp Interp.real)
open Tacenta.UnitLifecycleIntegrationScreen (byteRng byteCrc byteTrace chunks32)
open Tacenta.UnitLifecycleResponderFirstFrame (FirstFrameSuccessShape PoolEntry reachStore reachBundle
  publish_reachStore reachStore_distinct reach_establishment heldKemPair zPool InitiatorSecretParts
  DhAgreeSymmetric FirstKemAgrees)
open Tacenta.UnitLifecycleResponderFirstReceipt (DhAgreeContributory AeadRoundTrip)
open Tacenta.UnitLifecycleDecryptRatchetT3 (DecryptOracleOf DecryptRatchetAgreements)
open Tacenta.UnitLifecycleEstablishInitiatorShape (DhPublicValid)
open Tacenta.UnitLifecycleResponderReply (oracleOf_with_draws)

open Tacenta.UnitSatisfiabilityJoint (InitiatorAxiom ResponderAxiom) in
open Tacenta.UnitLifecycleEstablishedEncrypt (EstablishedEncryptHypotheses EncryptExtraLaws emptyPlaintext) in
/-- **The received maximum's hypotheses and the reply receipt's, together on one run**: at the real constants, under
the laws of `first_send_reply_receipt_reachable` (all assumed) and the open-length law `AeadOpenLengthLaw` (assumed),
for every initiator identity, every 64-byte seed at whose bytes the model's key generation answers, every 32 further
bytes and every reply plaintext `ptR` of at most 4096 bytes: there is a run (last-resort path, the responder's source
chosen by `DhPublicNotConstant`) in which `establish_responder` on the initiator's first-send bytes succeeds, the
responder's `encrypt` of `ptR` returns bytes, and the initiator's public `decrypt` of those bytes returns `Ok ptA`
with `ptA` the bytes of `ptR` and the pending initial message cleared (every hypothesis of `initiator_receives_reply`
holds there, `hfitR` included), and at that same call every hypothesis of
`UnitLifecycleSizeRule.decrypt_ok_plaintext_le_max` holds: the output refines the model's public `decrypt` at a model
session (`hstep`), it is `Ok ptA` (`hok`), and the oracle with the initiator's draws meets `AeadOpenLength`
(`hopen`); so `ptA` is at most `MAX_PLAINTEXT_LEN` bytes by that theorem.  With `size_witness_laws_model`, which puts
every law taken here in one toy interpretation with a padded AEAD, this shows the hypothesis set is consistent; it
does not show that the shipping AEAD meets the laws.  No compiler-trust axiom (the pin). -/
theorem size_witness_reachable (K : Model.Braid.Kem) (dh : Tacenta.UnitLifecycleT3.DhView)
    (kem : Tacenta.UnitLifecycleT3.KemView) (L : Tacenta.UnitLifecycleDecryptScreen.DecryptJointLaws K dh)
    (A : Nonempty (InitiatorAxiom Interp.real byteRng))
    (S : Tacenta.UnitLifecycleEstablishInitiatorShape.InitiatorSuccessShape Interp.real byteRng byteCrc)
    (hpub : DhPublicValid) (hct : Tacenta.UnitLifecycleEstablishInitiatorShape.KemCiphertextLenOf)
    (X : EncryptExtraLaws K dh kem) (RA : Nonempty (ResponderAxiom Interp.real byteRng))
    (hsym : DhAgreeSymmetric) (hrt : Tacenta.UnitLifecycleSessionCodec.DhPublicBytesRoundTrip)
    (FS : FirstFrameSuccessShape Interp.real tacenta_boundary.kem.KeyPair.public_key
      @alloc.vec.Vec.is_empty)
    (hsizes : Tacenta.UnitLifecycleEstablishedEncrypt.KeyGenSizesOf K)
    (hcon : DhAgreeContributory) (haead : AeadRoundTrip) (hnc : DhPublicNotConstant)
    (hopenLen : AeadOpenLengthLaw)
    (ourA : lifecycle.Identity) (seed : List Std.U8) (hseed : seed.length = 64)
    (extra : List Std.U8) (hextra : extra.length = 32)
    (hkg : K.keyGen (Model.Lifecycle.braidRandomness (seed.map Tacenta.SessionUnitBraidT3.u8)) ≠ none)
    (ptR : Slice Std.U8) (hptR : ptR.val.length ≤ 4096) :
    ∃ (oracle : Model.Lifecycle.Oracle) (bundle : lifecycle.PublishedBundle)
      (q : InitiatorSecretParts byteRng byteCrc ourA bundle) (bytes : alloc.vec.Vec Std.U8)
      (s' : lifecycle.Session) (rng' : List Std.U8) (ourB : lifecycle.Identity)
      (storeB : lifecycle.PrekeyStore) (seedB : List Std.U8) (sB' : lifecycle.Session) (ptB : alloc.vec.Vec Std.U8)
      (storeB' : lifecycle.PrekeyStore) (rngB' : List Std.U8) (bytesR : alloc.vec.Vec Std.U8)
      (sB'' : lifecycle.Session) (ptA : alloc.vec.Vec Std.U8) (s'' : lifecycle.Session) (rngA' : List Std.U8)
      (mA : Model.Lifecycle.Session),
      oracle.braidKem = K ∧
      lifecycle.Session.encrypt byteRng byteCrc q.session emptyPlaintext (seed ++ extra) =
        ok (core.result.Result.Ok bytes, s', rng') ∧
      lifecycle.PrekeyStore.publish storeB = ok bundle ∧
      lifecycle.establish_responder byteRng byteCrc ourB storeB (alloc.vec.Vec.deref bytes) seedB =
        ok (core.result.Result.Ok (sB', ptB), storeB', rngB') ∧
      lifecycle.Session.encrypt byteRng byteCrc sB' ptR rngB' =
        ok (core.result.Result.Ok bytesR, sB'', rngB') ∧
      lifecycle.Session.decrypt byteRng byteCrc s' (alloc.vec.Vec.deref bytesR) rng' =
        ok (core.result.Result.Ok ptA, s'', rngA') ∧
      ptA.val = ptR.val ∧ s''.pending_initial = none ∧
      StepRefines byteTrace dh oracle.braidKem (core.result.Result.Ok ptA, s'', rngA')
        (Model.Lifecycle.decrypt Tacenta.UnitLifecycleRepair.witnessView { oracle with draws := byteTrace rng' } mA
          (sliceOf (alloc.vec.Vec.deref bytesR))) ∧
      Model.Lifecycle.AeadOpenLength { oracle with draws := byteTrace rng' } ∧
      ptA.val.length ≤ Model.Lifecycle.maxPlaintextLen := by
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
  -- the encrypt record at that establishment, from the seed followed by the 32 bytes
  have hlen96 : 64 ≤ (seed ++ extra).length := by simp [hseed]
  obtain ⟨oracle, bundle0, s0, rng10, hK, hdraws0, hOL, H0⟩ :=
    established_encrypt_hypotheses_open K dh kem L A S hpub hct X hopenLen ourA (seed ++ extra) hlen96
  have H : EstablishedEncryptHypotheses byteRng byteCrc byteTrace dh kem
      Tacenta.UnitLifecycleRepair.witnessView oracle byteRng byteCrc ourA (reachBundle pkb sig1 sig2 kemPk)
      (reachBundle pkb sig1 sig2 kemPk).bundle.identity_key (List.replicate 32 0#u8 ++ stream) rng1 q.session
      emptyPlaintext (seed ++ extra) :=
    { braid := H0.braid, triple := H0.triple, derivedKeys := H0.derivedKeys, aead := H0.aead,
      dhCodec := H0.dhCodec, oracleOf := H0.oracleOf, codec := H0.codec, codewordView := H0.codewordView,
      zeroizing80 := H0.zeroizing80, zeroizing32 := H0.zeroizing32, zeroizingKeys := H0.zeroizingKeys,
      keyGen := H0.keyGen, kemCiphertextLen := H0.kemCiphertextLen,
      kemCiphertextBound := H0.kemCiphertextBound, established := h, room := H0.room,
      trace_eq := H0.trace_eq, draws := H0.draws }
  obtain ⟨inst⟩ := H.derivedKeys
  subst hK
  have htr := byteTrace_seed_extra seed extra hseed hextra
  -- the first send's success, and the source it leaves
  obtain ⟨output, hcall, hrest, hcases⟩ := Tacenta.UnitLifecycleEstablishedEncrypt.established_encrypt_outcomes
    byteRng byteCrc byteTrace dh kem Tacenta.UnitLifecycleRepair.witnessView oracle H.braid H.triple H.aead
    H.dhCodec H.oracleOf H.codec H.codewordView H.zeroizing80 H.zeroizing32 H.zeroizingKeys H.keyGen
    H.kemCiphertextLen H.kemCiphertextBound byteRng byteCrc ourA _ _ _ rng1 q.session H.established
    emptyPlaintext H.room (by simp [Tacenta.UnitLifecycleEstablishedEncrypt.emptyPlaintext, Tacenta.UnitLifecycleT3.sliceOf])
    (seed ++ extra) H.trace_eq _ _ _ htr
  rw [two_draws_of_seed_extra seed extra hseed] at hcases
  obtain ⟨res, s', rng'⟩ := output
  rcases hcases with ⟨hnone, -⟩ | ⟨dk, ekSeed, ekVector, -, bytes, hres, -⟩
  · exact absurd hnone hkg
  simp only at hres hrest
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
  obtain ⟨oracle0, bundle1, s1, rng11, hK0, H1⟩ :=
    Tacenta.UnitLifecycleEstablishedDecrypt.established_decrypt_hypotheses_jointly_satisfiable
      oracle.braidKem dh L A S hpub hct ourA
  have ag : DecryptRatchetAgreements oracle.braidKem :=
    hK0 ▸ (H1 Tacenta.UnitLifecycleRepair.witnessView).agreements
  have hpeer : q.peerRatchetBytes = a := by
    have hp := q.hPeerRatchetBytes
    simp only [reachBundle] at hp
    rw [ha'] at hp
    cases hp
    rfl
  -- the oracle's public key of 32 bytes is the bytes of the boundary's public key of them
  have hpubOf : ∀ (sb' : Array U8 32#usize) (k : tacenta_boundary.dh.PrivateKey)
      (pk : tacenta_boundary.dh.PublicKeyBytes) (b : Array U8 32#usize),
      tacenta_boundary.dh.PrivateKey.from_bytes sb' = ok k →
      tacenta_boundary.dh.PrivateKey.public_key k = ok pk → tacenta_boundary.dh.PublicKeyBytes.as_bytes pk = ok b →
      oracle.dhPublic (arrayOf sb') = arrayOf b := by
    intro sb' k pk b hk hpk hb
    obtain ⟨k', hk', hkv⟩ := H.codec.privateFromBytes sb'
    rw [hk] at hk'; cases hk'
    obtain ⟨pk', hpk', hpkv⟩ := H.oracleOf.dhPublic k
    rw [hpk] at hpk'; cases hpk'
    obtain ⟨b', hb', hbv⟩ := H.codec.asBytes pk
    rw [hb] at hb'; cases hb'
    rw [← hkv, ← hpkv, hbv]
  -- the initiator's draw after its first send: the 32 bytes after the seed
  have hdrawA : byteTrace rng' = extra.map Tacenta.SessionUnitBraidT3.u8 :: [] := hrest
  have hu : 4294967295 ≤ Usize.max :=
    Tacenta.SessionUnitSessionT1.small_le_usize_max (le_refl _)
  -- the responder's 32-byte source: a key whose public key is not the peer key the initiator holds
  obtain ⟨sbB, kF, pkF, bF, hkF, hpkF, hbF, hne⟩ := (dhPublicNotConstant_is.mp hnc) q.peerRatchetBytes
  have hfresh : oracle.dhPublic (sbB.val.map Tacenta.SessionUnitBraidT3.u8) ≠ arrayOf q.peerRatchetBytes := by
    rw [show sbB.val.map Tacenta.SessionUnitBraidT3.u8 = arrayOf sbB from rfl, hpubOf sbB kF pkF bF hkF hpkF hbF]
    intro hab
    exact hne (Tacenta.UnitLifecycleEstablishedEncrypt.array_eq_of_bytes hab)
  have hseedB : sbB.val.length = 32 := by simp
  generalize hsB : sbB.val = seedB at hfresh hseedB
  -- the responder's oracle: the shared oracle with the responder source's draw
  let oracleB : Model.Lifecycle.Oracle := { oracle with draws := byteTrace seedB }
  have oracleOfB : Tacenta.UnitLifecycleT3.OracleOf byteRng byteCrc dh kem byteTrace oracleB :=
    oracleOf_with_draws H.oracleOf _
  have hdrB : byteTrace seedB = seedB.map Tacenta.SessionUnitBraidT3.u8 :: [] := byteTrace_one seedB hseedB
  obtain ⟨-, hdisj⟩ := Tacenta.UnitLifecycleResponderFirstReceipt.initiator_first_send_responder_receives byteRng
    byteCrc byteTrace dh kem Tacenta.UnitLifecycleRepair.witnessView oracle H.braid H.triple H.aead H.dhCodec
    H.oracleOf H.codec H.codewordView H.zeroizing80 H.zeroizing32 H.zeroizingKeys H.keyGen hsizes
    H.kemCiphertextLen H.kemCiphertextBound byteRng byteCrc ourA _ _ _ rng1 q.session h q rfl emptyPlaintext H.room
    (seed ++ extra) H.trace_eq _ _ _ htr bytes s' rng' hcall
    (Tacenta.UnitLifecycleEstablishedEncrypt.first_message_fits H.aead H.dhCodec H.kemCiphertextLen
      H.kemCiphertextBound byteRng byteCrc ourA _ _ _ rng1 q.session H.established byteRng byteCrc
      emptyPlaintext (seed ++ extra) bytes s' rng'
      (by simp [Tacenta.UnitLifecycleEstablishedEncrypt.emptyPlaintext,
        Model.Lifecycle.maxRatchetFrameLen_value]) hcall)
    byteRng byteCrc contracts hpub hsym hcon haead hrt
    L.optionEq byteTrace oracleB (DecryptOracleOf.of_oracleOf oracleOfB) ag ourB storeB hpublish hidentity
    hdistinct hkem hhead seedB rfl _ [] hdrB
  rcases hdisj with ⟨-, e, hrefuse, -⟩ |
    ⟨p, ec, dSend, dk', ekSeed', ekVector', ptB, sB', storeB', rngB', -, -, -, -, -, -, -, -, -, -, hcallB, -⟩
  · exfalso
    rcases hrefuse with ⟨-, hleg⟩ | ⟨-, fp, -, x, hx, -⟩ | ⟨-, -, hne', -⟩
    · simp [storeB, reachStore] at hleg
    · simp [storeB, reachStore] at hx
    · exact hne' (by simp [storeB, reachStore])
  -- the two outcomes of the initiator's receipt of the reply on this run
  obtain ⟨_dSend, _x, bytesR, sB'', res, s'', rngA', -, -, hcallR, -, hcallA, -, hcases⟩ :=
    initiator_receives_reply_two_outcomes byteRng byteCrc byteTrace dh kem Tacenta.UnitLifecycleRepair.witnessView
      oracle H.braid H.triple H.aead H.dhCodec H.oracleOf H.codec H.codewordView H.zeroizing80 H.zeroizing32
      H.zeroizingKeys H.keyGen hsizes H.kemCiphertextLen H.kemCiphertextBound byteRng byteCrc ourA _ _ _ rng1
      q.session H.established q rfl emptyPlaintext H.room (seed ++ extra) H.trace_eq _ _ _ htr bytes s' rng' hcall
      contracts.decrypt ag _ [] hdrawA byteRng byteCrc contracts hpub hsym hcon haead hrt L.optionEq byteTrace
      oracleB oracleOfB H.braid ag ourB storeB hpublish hidentity hdistinct hkem seedB rfl _ [] hdrB ptB sB'
      storeB' rngB' hcallB ptR (by omega)
      (by rw [Tacenta.UnitLifecycleT3.sliceOf_length, Model.Lifecycle.maxRatchetFrameLen_value]; omega) rngB'
  -- the same call, as a step refinement
  obtain ⟨bytesR', sB3, mA, output, hcallR', hcallA', hstep⟩ :=
    initiator_receives_reply_step byteRng byteCrc byteTrace dh kem Tacenta.UnitLifecycleRepair.witnessView
      oracle H.braid H.triple H.aead H.dhCodec H.oracleOf H.codec H.codewordView H.zeroizing80 H.zeroizing32
      H.zeroizingKeys H.keyGen hsizes H.kemCiphertextLen H.kemCiphertextBound byteRng byteCrc ourA _ _ _ rng1
      q.session H.established q rfl emptyPlaintext H.room (seed ++ extra) H.trace_eq _ _ _ htr bytes s' rng' hcall
      contracts.decrypt ag _ [] hdrawA byteRng byteCrc contracts hpub hsym hcon haead hrt L.optionEq byteTrace
      oracleB oracleOfB H.braid ag ourB storeB hpublish hidentity hdistinct hkem seedB rfl _ [] hdrB ptB sB'
      storeB' rngB' hcallB ptR (by omega)
      (by rw [Tacenta.UnitLifecycleT3.sliceOf_length, Model.Lifecycle.maxRatchetFrameLen_value]; omega) rngB'
  rw [hcallR] at hcallR'
  simp only [ok.injEq, Prod.mk.injEq, core.result.Result.Ok.injEq] at hcallR'
  obtain ⟨rfl, rfl, -⟩ := hcallR'
  rcases hcases with ⟨hpeer', -, -⟩ | ⟨-, ptA, hres, hpt, hpend, -, -⟩
  · exact absurd hpeer' hfresh
  subst hres
  rw [hcallA] at hcallA'
  simp only [ok.injEq] at hcallA'
  subst hcallA'
  have hmax := Tacenta.UnitLifecycleSizeRule.decrypt_ok_plaintext_le_max byteTrace dh oracle.braidKem
    Tacenta.UnitLifecycleRepair.witnessView { oracle with draws := byteTrace rng' } mA
    (alloc.vec.Vec.deref bytesR) (core.result.Result.Ok ptA, s'', rngA') ptA hstep rfl hOL
  exact ⟨oracle, _, q, bytes, s', rng', ourB, storeB, seedB, sB', ptB, storeB', rngB', bytesR, sB'', ptA, s'',
    rngA', mA, rfl, hcall, hpublish, hcallB, hcallR, hcallA, hpt, hpend, hstep, hOL, hmax⟩

end Reach

end Tacenta.UnitLifecycleSizeWitness

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
info: 'Tacenta.UnitLifecycleSizeWitness.padLen_pos' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSizeWitness.padLen_pos

/--
info: 'Tacenta.UnitLifecycleSizeWitness.padLen_le' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSizeWitness.padLen_le

/--
info: 'Tacenta.UnitLifecycleSizeWitness.padded_total' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSizeWitness.padded_total

/--
info: 'Tacenta.UnitLifecycleSizeWitness.byteOf_toNat' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSizeWitness.byteOf_toNat

/--
info: 'Tacenta.UnitLifecycleSizeWitness.padBody_length' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSizeWitness.padBody_length

/--
info: 'Tacenta.UnitLifecycleSizeWitness.padOpen_length' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSizeWitness.padOpen_length

/--
info: 'Tacenta.UnitLifecycleSizeWitness.padBody_drop' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSizeWitness.padBody_drop

/--
info: 'Tacenta.UnitLifecycleSizeWitness.padBody_take' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSizeWitness.padBody_take

/--
info: 'Tacenta.UnitLifecycleSizeWitness.padOpen_of_body' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSizeWitness.padOpen_of_body

/--
info: 'Tacenta.UnitLifecycleSizeWitness.padOpen_padSeal' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSizeWitness.padOpen_padSeal

/--
info: 'Tacenta.UnitLifecycleSizeWitness.aeadOpenLengthLaw_is' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleSizeWitness.aeadOpenLengthLaw_is

/--
info: 'Tacenta.UnitLifecycleSizeWitness.modelPadded_dhCodec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSizeWitness.modelPadded_dhCodec

/--
info: 'Tacenta.UnitLifecycleSizeWitness.modelPadded_dhAgree' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSizeWitness.modelPadded_dhAgree

/--
info: 'Tacenta.UnitLifecycleSizeWitness.modelPadded_symmetric' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSizeWitness.modelPadded_symmetric

/--
info: 'Tacenta.UnitLifecycleSizeWitness.modelPadded_contributory' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSizeWitness.modelPadded_contributory

/--
info: 'Tacenta.UnitLifecycleSizeWitness.modelPadded_notConstant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSizeWitness.modelPadded_notConstant

/--
info: 'Tacenta.UnitLifecycleSizeWitness.modelPadded_aeadOpen' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSizeWitness.modelPadded_aeadOpen

/--
info: 'Tacenta.UnitLifecycleSizeWitness.modelPadded_aeadSeal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSizeWitness.modelPadded_aeadSeal

/--
info: 'Tacenta.UnitLifecycleSizeWitness.modelPadded_aeadRoundTrip' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSizeWitness.modelPadded_aeadRoundTrip

/--
info: 'Tacenta.UnitLifecycleSizeWitness.modelPadded_openLength' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSizeWitness.modelPadded_openLength

/--
info: 'Tacenta.UnitLifecycleSizeWitness.size_witness_laws_model' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 rand_core_1.error.Error,
 Array.Insts.ZeroizeZeroize.zeroize,
 Pair.Insts.ZeroizeZeroize.zeroize,
 zeroize.Zeroize.Blanket.zeroize,
 alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSizeWitness.size_witness_laws_model

/--
info: 'Tacenta.UnitLifecycleSizeWitness.aeadOpenLength_oracleOfLaws' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSizeWitness.aeadOpenLength_oracleOfLaws

/--
info: 'Tacenta.UnitLifecycleSizeWitness.oracleOfShape_open' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSizeWitness.oracleOfShape_open

/--
info: 'Tacenta.UnitLifecycleSizeWitness.established_encrypt_hypotheses_open' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleSizeWitness.established_encrypt_hypotheses_open

/--
info: 'Tacenta.UnitLifecycleSizeWitness.initiator_receives_reply_step' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleSizeWitness.initiator_receives_reply_step

/--
info: 'Tacenta.UnitLifecycleSizeWitness.size_witness_reachable' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleSizeWitness.size_witness_reachable

/--
info: Tacenta.UnitLifecycleSizeWitness.padLen_pos : ∀ (n : ℕ), 1 ≤ Tacenta.UnitLifecycleSizeWitness.padLen n
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSizeWitness.padLen_pos

/--
info: Tacenta.UnitLifecycleSizeWitness.padLen_le : ∀ (n : ℕ), Tacenta.UnitLifecycleSizeWitness.padLen n ≤ 16
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSizeWitness.padLen_le

/--
info: Tacenta.UnitLifecycleSizeWitness.padded_total : ∀ (n : ℕ),
  n + Tacenta.UnitLifecycleSizeWitness.padLen n + 32 = 16 * (n / 16) + 48
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSizeWitness.padded_total

/--
info: Tacenta.UnitLifecycleSizeWitness.byteOf_toNat : ∀ k < 256, (Tacenta.UnitLifecycleSizeWitness.byteOf k).bv.toNat = k
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSizeWitness.byteOf_toNat

/--
info: Tacenta.UnitLifecycleSizeWitness.padBody_length : ∀ (p : List U8),
  (Tacenta.UnitLifecycleSizeWitness.padBody p).length = p.length + Tacenta.UnitLifecycleSizeWitness.padLen p.length + 32
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSizeWitness.padBody_length

/--
info: Tacenta.UnitLifecycleSizeWitness.padOpen_length : ∀ (c : Slice U8) (v : alloc.vec.Vec U8),
  Tacenta.UnitLifecycleSizeWitness.padOpen c = core.result.Result.Ok v → (↑v).length + 33 ≤ (↑c).length
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSizeWitness.padOpen_length

/--
info: Tacenta.UnitLifecycleSizeWitness.padBody_drop : ∀ (p : List U8),
  List.drop ((Tacenta.UnitLifecycleSizeWitness.padBody p).length - 33) (Tacenta.UnitLifecycleSizeWitness.padBody p) =
    Tacenta.UnitLifecycleSizeWitness.byteOf (Tacenta.UnitLifecycleSizeWitness.padLen p.length) :: List.replicate 32 0#u8
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSizeWitness.padBody_drop

/--
info: Tacenta.UnitLifecycleSizeWitness.padBody_take : ∀ (p : List U8),
  List.take
      ((Tacenta.UnitLifecycleSizeWitness.padBody p).length - 32 - Tacenta.UnitLifecycleSizeWitness.padLen p.length)
      (Tacenta.UnitLifecycleSizeWitness.padBody p) =
    p
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSizeWitness.padBody_take

/--
info: Tacenta.UnitLifecycleSizeWitness.padOpen_of_body : ∀ (c : Slice U8) (p : List U8) (hp : p.length ≤ Usize.max),
  ↑c = Tacenta.UnitLifecycleSizeWitness.padBody p →
    Tacenta.UnitLifecycleSizeWitness.padOpen c = core.result.Result.Ok ⟨p, hp⟩
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSizeWitness.padOpen_of_body

/--
info: Tacenta.UnitLifecycleSizeWitness.padOpen_padSeal : ∀ (p : Slice U8),
  (↑p).length + 48 ≤ Usize.max →
    Tacenta.UnitLifecycleSizeWitness.padOpen (Tacenta.UnitLifecycleSizeWitness.padSeal p).deref =
      core.result.Result.Ok ⟨↑p, (⋯ : (↑p).length ≤ Usize.max)⟩
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSizeWitness.padOpen_padSeal

/--
info: Tacenta.UnitLifecycleSizeWitness.aeadOpenLengthLaw_is : Tacenta.UnitLifecycleSizeWitness.AeadOpenLengthLaw ↔
  ∀ (k1 k2 : Std.Array U8 32#usize) (iv : Std.Array U8 16#usize) (c ad : Slice U8) (v : alloc.vec.Vec U8),
    tacenta_boundary.aead.decrypt k1 k2 iv c ad = ok (core.result.Result.Ok v) → (↑v).length + 33 ≤ (↑c).length
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSizeWitness.aeadOpenLengthLaw_is

/--
info: Tacenta.UnitLifecycleSizeWitness.modelPadded_dhCodec : Tacenta.UnitSatisfiabilityJoint.DhCodecShape
  Tacenta.UnitLifecycleSizeWitness.Interp.modelPadded
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSizeWitness.modelPadded_dhCodec

/--
info: Tacenta.UnitLifecycleSizeWitness.modelPadded_dhAgree : Tacenta.UnitSatisfiabilityJoint.DhAgreeShape
  Tacenta.UnitLifecycleSizeWitness.Interp.modelPadded
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSizeWitness.modelPadded_dhAgree

/--
info: Tacenta.UnitLifecycleSizeWitness.modelPadded_symmetric : Tacenta.UnitLifecycleResponderFirstFrame.DhAgreeSymmetricShape
  Tacenta.UnitLifecycleSizeWitness.Interp.modelPadded
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSizeWitness.modelPadded_symmetric

/--
info: Tacenta.UnitLifecycleSizeWitness.modelPadded_contributory : Tacenta.UnitLifecycleResponderFirstReceipt.DhAgreeContributoryShape
  Tacenta.UnitLifecycleSizeWitness.Interp.modelPadded
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSizeWitness.modelPadded_contributory

/--
info: Tacenta.UnitLifecycleSizeWitness.modelPadded_notConstant : Tacenta.UnitLifecycleResponderReplyReceipt.DhPublicNotConstantShape
  Tacenta.UnitLifecycleSizeWitness.Interp.modelPadded
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSizeWitness.modelPadded_notConstant

/--
info: Tacenta.UnitLifecycleSizeWitness.modelPadded_aeadOpen : Tacenta.UnitSatisfiabilityJoint.AeadOpenShape
  Tacenta.UnitLifecycleSizeWitness.Interp.modelPadded
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSizeWitness.modelPadded_aeadOpen

/--
info: Tacenta.UnitLifecycleSizeWitness.modelPadded_aeadSeal : Tacenta.UnitSatisfiabilityJoint.AeadSealBoundedShape
  Tacenta.UnitLifecycleSizeWitness.Interp.modelPadded
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSizeWitness.modelPadded_aeadSeal

/--
info: Tacenta.UnitLifecycleSizeWitness.modelPadded_aeadRoundTrip : Tacenta.UnitLifecycleResponderFirstReceipt.AeadRoundTripShape
  Tacenta.UnitLifecycleSizeWitness.Interp.modelPadded
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSizeWitness.modelPadded_aeadRoundTrip

/--
info: Tacenta.UnitLifecycleSizeWitness.modelPadded_openLength : Tacenta.UnitLifecycleSizeWitness.AeadOpenLengthShape
  Tacenta.UnitLifecycleSizeWitness.Interp.modelPadded
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSizeWitness.modelPadded_openLength

/--
info: Tacenta.UnitLifecycleSizeWitness.size_witness_laws_model : Tacenta.UnitLifecycleDecryptScreen.DecryptJointLawsShape
    Tacenta.UnitLifecycleSizeWitness.Interp.modelPadded Tacenta.UnitLifecycleSizeWitness.viewPadded
    Tacenta.UnitLifecycleEstablishedEncrypt.toyKemR @Tacenta.UnitHeadroomInvariant.optionEqImpl ∧
  Nonempty
      (Tacenta.UnitSatisfiabilityJoint.InitiatorAxiom Tacenta.UnitLifecycleSizeWitness.Interp.modelPadded
        Tacenta.UnitLifecycleIntegrationScreen.byteRng) ∧
    Tacenta.UnitLifecycleEstablishInitiatorShape.InitiatorSuccessShape
        Tacenta.UnitLifecycleSizeWitness.Interp.modelPadded Tacenta.UnitLifecycleIntegrationScreen.byteRng
        Tacenta.UnitLifecycleIntegrationScreen.byteCrc ∧
      Tacenta.UnitLifecycleEstablishInitiatorShape.DhPublicValidShape
          Tacenta.UnitLifecycleSizeWitness.Interp.modelPadded ∧
        Tacenta.UnitLifecycleEstablishInitiatorShape.KemCiphertextLenLawShape (ok 0#usize)
            Tacenta.UnitLifecycleSizeWitness.Interp.modelPadded ∧
          Tacenta.UnitLifecycleEstablishedEncrypt.EncryptExtraLawsShape
              Tacenta.UnitLifecycleSizeWitness.InterpO.modelPadded Tacenta.UnitLifecycleSizeWitness.dhViewPadded
              Tacenta.UnitLifecycleSizeWitness.kemViewPadded Tacenta.UnitLifecycleEstablishedEncrypt.toyKemR
              (ok 0#usize) ∧
            (Tacenta.UnitLifecycleSessionCodec.ZeroizingVecRoundTripShape
                  Tacenta.UnitLifecycleSizeWitness.Interp.modelPadded ∧
                Tacenta.UnitLifecycleSessionCodec.DhPrivateBytesRoundTripShape
                    Tacenta.UnitLifecycleSizeWitness.Interp.modelPadded ∧
                  Tacenta.UnitLifecycleSessionCodec.DhPublicBytesRoundTripShape
                      Tacenta.UnitLifecycleSizeWitness.Interp.modelPadded ∧
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
                          Tacenta.UnitLifecycleSizeWitness.Interp.modelPadded
                          Tacenta.UnitLifecycleIntegrationScreen.byteRng) ∧
                      Tacenta.UnitLifecycleEstablishResponder.ResponderSuccessShape
                          Tacenta.UnitLifecycleSizeWitness.Interp.modelPadded ∧
                        Tacenta.UnitLifecycleEstablishResponder.ZeroKeyShape
                            Tacenta.UnitLifecycleSizeWitness.Interp.modelPadded ∧
                          Tacenta.UnitLifecycleResponderFirstFrame.DhAgreeSymmetricShape
                              Tacenta.UnitLifecycleSizeWitness.Interp.modelPadded ∧
                            (Tacenta.UnitLifecycleResponderFirstFrame.FirstFrameSuccessShape
                                Tacenta.UnitLifecycleSizeWitness.Interp.modelPadded (fun x => ok (alloc.vec.Vec.new U8))
                                fun {T} x v => ok (decide (↑v = []))) ∧
                              Tacenta.UnitLifecycleResponderFirstReceipt.AeadRoundTripShape
                                  Tacenta.UnitLifecycleSizeWitness.Interp.modelPadded ∧
                                Tacenta.UnitLifecycleResponderFirstReceipt.DhAgreeContributoryShape
                                    Tacenta.UnitLifecycleSizeWitness.Interp.modelPadded ∧
                                  Tacenta.UnitLifecycleResponderReplyReceipt.DhPublicNotConstantShape
                                      Tacenta.UnitLifecycleSizeWitness.Interp.modelPadded ∧
                                    Tacenta.UnitLifecycleSizeWitness.AeadOpenLengthShape
                                      Tacenta.UnitLifecycleSizeWitness.Interp.modelPadded
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSizeWitness.size_witness_laws_model

/--
info: Tacenta.UnitLifecycleSizeWitness.aeadOpenLength_oracleOfLaws : ∀ (I : Tacenta.UnitOracleShape.InterpO)
  (dh : Tacenta.UnitOracleShape.DhViewOf I.toInterp) (kem : Tacenta.UnitOracleShape.KemViewOf I.toInterp)
  (valid : Model.Lifecycle.Bytes → Bool)
  (E : Model.Lifecycle.Bytes → Model.Lifecycle.Bytes → alloc.vec.Vec U8 × Std.Array U8 32#usize)
  (S : Std.Array U8 32#usize → Slice U8 → Slice U8 → Std.Array U8 64#usize),
  Tacenta.UnitLifecycleSizeWitness.AeadOpenLengthShape I.toInterp →
    Model.Lifecycle.AeadOpenLength (Tacenta.UnitOracleShape.oracleOfLaws I dh kem valid E S)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSizeWitness.aeadOpenLength_oracleOfLaws

/--
info: Tacenta.UnitLifecycleSizeWitness.oracleOfShape_open : ∀ (I : Tacenta.UnitOracleShape.InterpO)
  (dh : Tacenta.UnitOracleShape.DhViewOf I.toInterp) (kem : Tacenta.UnitOracleShape.KemViewOf I.toInterp),
  Tacenta.UnitOracleJoint.OracleLaws I dh kem →
    Tacenta.UnitLifecycleSizeWitness.AeadOpenLengthShape I.toInterp →
      ∃ oracle,
        Tacenta.UnitOracleShape.OracleOfShape I Tacenta.UnitLifecycleIntegrationScreen.byteRng
            Tacenta.UnitLifecycleIntegrationScreen.byteCrc dh kem Tacenta.UnitLifecycleIntegrationScreen.byteTrace
            oracle ∧
          Model.Lifecycle.AeadOpenLength oracle
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSizeWitness.oracleOfShape_open

/--
info: Tacenta.UnitLifecycleSizeWitness.established_encrypt_hypotheses_open : ∀ (K : Model.Braid.Kem)
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
              Tacenta.UnitLifecycleSizeWitness.AeadOpenLengthLaw →
                ∀ (our : lifecycle.Identity) (seed : List U8),
                  64 ≤ seed.length →
                    ∃ oracle bundle s rng1,
                      oracle.braidKem = K ∧
                        oracle.draws = Tacenta.UnitLifecycleIntegrationScreen.byteTrace seed ∧
                          Model.Lifecycle.AeadOpenLength oracle ∧
                            Tacenta.UnitLifecycleEstablishedEncrypt.EstablishedEncryptHypotheses
                              Tacenta.UnitLifecycleIntegrationScreen.byteRng
                              Tacenta.UnitLifecycleIntegrationScreen.byteCrc
                              Tacenta.UnitLifecycleIntegrationScreen.byteTrace dh kem
                              Tacenta.UnitLifecycleRepair.witnessView oracle
                              Tacenta.UnitLifecycleIntegrationScreen.byteRng
                              Tacenta.UnitLifecycleIntegrationScreen.byteCrc our bundle bundle.bundle.identity_key []
                              rng1 s Tacenta.UnitLifecycleEstablishedEncrypt.emptyPlaintext seed
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSizeWitness.established_encrypt_hypotheses_open

/--
info: @Tacenta.UnitLifecycleSizeWitness.initiator_receives_reply_step : ∀ [Tacenta.SessionUnitT1.DerivedKeysModel]
  {R E F : Type} (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R) (trace : R → List Model.Lifecycle.Key)
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
                  Tacenta.UnitLifecycleT3.ZeroizingRoundTrips (Std.Array U8 32#usize) →
                    Tacenta.UnitLifecycleT3.ZeroizingRoundTrips
                        (Std.Array U8 32#usize × Std.Array U8 32#usize × Std.Array U8 16#usize) →
                      Tacenta.UnitLifecycleEstablishedEncrypt.KeyGenSeededFor oracle.braidKem rc crc trace →
                        Tacenta.UnitLifecycleEstablishedEncrypt.KeyGenSizesOf oracle.braidKem →
                          Tacenta.UnitLifecycleEstablishInitiatorShape.KemCiphertextLenOf →
                            Tacenta.UnitLifecycleRestoredSession.KemCiphertextLenBound →
                              ∀ (rcE : rand_core_1.RngCore E) (crcE : rand_core_1.CryptoRng E)
                                (ourA : lifecycle.Identity) (bundleA : lifecycle.PublishedBundle)
                                (expected : tacenta_boundary.dh.PublicKeyBytes) (rng0 rng1 : E) (s : lifecycle.Session),
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
                                                                            ∀ (traceB : F → List Model.Lifecycle.Key)
                                                                              (oracleB : Model.Lifecycle.Oracle),
                                                                              Tacenta.UnitLifecycleT3.OracleOf rcB crcB
                                                                                  dh kem traceB oracleB →
                                                                                Tacenta.UnitLifecycleT3.BraidSendRefinementContracts
                                                                                    rcB oracleB.braidKem →
                                                                                  Tacenta.UnitLifecycleDecryptRatchetT3.DecryptRatchetAgreements
                                                                                      oracleB.braidKem →
                                                                                    ∀ (ourB : lifecycle.Identity)
                                                                                      (storeB : lifecycle.PrekeyStore),
                                                                                      storeB.publish = ok bundleA →
                                                                                        ourB.public =
                                                                                            ok storeB.identity_public →
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
                                                                                                        dB :: restB →
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
                                                                                                              rcB crcB
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
                                                                                                              Slice U8),
                                                                                                            102 +
                                                                                                                  ((↑ptR).length +
                                                                                                                    48) ≤
                                                                                                                Usize.max →
                                                                                                              List.length
                                                                                                                      (Tacenta.UnitLifecycleT3.sliceOf
                                                                                                                        ptR) +
                                                                                                                    150 ≤
                                                                                                                  Model.Lifecycle.maxRatchetFrameLen →
                                                                                                                ∀
                                                                                                                  (rngR :
                                                                                                                    F),
                                                                                                                  ∃
                                                                                                                    bytesR
                                                                                                                    sB''
                                                                                                                    mA
                                                                                                                    output,
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
                                                                                                                      lifecycle.Session.decrypt
                                                                                                                            rc
                                                                                                                            crc
                                                                                                                            s'
                                                                                                                            bytesR.deref
                                                                                                                            rng' =
                                                                                                                          ok
                                                                                                                            output ∧
                                                                                                                        Tacenta.UnitLifecycleT3.StepRefines
                                                                                                                          trace
                                                                                                                          dh
                                                                                                                          oracle.braidKem
                                                                                                                          output
                                                                                                                          (Model.Lifecycle.decrypt
                                                                                                                            view
                                                                                                                            {
                                                                                                                              draws :=
                                                                                                                                trace
                                                                                                                                  rng',
                                                                                                                              braidKem :=
                                                                                                                                oracle.braidKem,
                                                                                                                              dhPublic :=
                                                                                                                                oracle.dhPublic,
                                                                                                                              dhAgree :=
                                                                                                                                oracle.dhAgree,
                                                                                                                              identityValid :=
                                                                                                                                oracle.identityValid,
                                                                                                                              aeadSeal :=
                                                                                                                                oracle.aeadSeal,
                                                                                                                              aeadOpen :=
                                                                                                                                oracle.aeadOpen,
                                                                                                                              kemValid :=
                                                                                                                                oracle.kemValid,
                                                                                                                              kemEncaps :=
                                                                                                                                oracle.kemEncaps,
                                                                                                                              kemDecaps :=
                                                                                                                                oracle.kemDecaps,
                                                                                                                              sigVerify :=
                                                                                                                                oracle.sigVerify,
                                                                                                                              sigSign :=
                                                                                                                                oracle.sigSign }
                                                                                                                            mA
                                                                                                                            (Tacenta.UnitLifecycleT3.sliceOf
                                                                                                                              bytesR.deref))
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSizeWitness.initiator_receives_reply_step

/--
info: Tacenta.UnitLifecycleSizeWitness.size_witness_reachable : ∀ (K : Model.Braid.Kem) (dh : Tacenta.UnitLifecycleT3.DhView)
  (kem : Tacenta.UnitLifecycleT3.KemView),
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
                        Tacenta.UnitSatisfiabilityJoint.Interp.real tacenta_boundary.kem.KeyPair.public_key
                        @alloc.vec.Vec.is_empty →
                      Tacenta.UnitLifecycleEstablishedEncrypt.KeyGenSizesOf K →
                        Tacenta.UnitLifecycleResponderFirstReceipt.DhAgreeContributory →
                          Tacenta.UnitLifecycleResponderFirstReceipt.AeadRoundTrip →
                            Tacenta.UnitLifecycleResponderReplyReceipt.DhPublicNotConstant →
                              Tacenta.UnitLifecycleSizeWitness.AeadOpenLengthLaw →
                                ∀ (ourA : lifecycle.Identity) (seed : List U8),
                                  seed.length = 64 →
                                    ∀ (extra : List U8),
                                      extra.length = 32 →
                                        K.keyGen
                                              (Model.Lifecycle.braidRandomness
                                                (List.map Tacenta.SessionUnitBraidT3.u8 seed)) ≠
                                            none →
                                          ∀ (ptR : Slice U8),
                                            (↑ptR).length ≤ 4096 →
                                              ∃ oracle bundle q bytes s' rng' ourB storeB seedB sB' ptB storeB' rngB'
                                                bytesR sB'' ptA s'' rngA' mA,
                                                oracle.braidKem = K ∧
                                                  lifecycle.Session.encrypt
                                                        Tacenta.UnitLifecycleIntegrationScreen.byteRng
                                                        Tacenta.UnitLifecycleIntegrationScreen.byteCrc q.session
                                                        Tacenta.UnitLifecycleEstablishedEncrypt.emptyPlaintext
                                                        (seed ++ extra) =
                                                      ok (core.result.Result.Ok bytes, s', rng') ∧
                                                    storeB.publish = ok bundle ∧
                                                      lifecycle.establish_responder
                                                            Tacenta.UnitLifecycleIntegrationScreen.byteRng
                                                            Tacenta.UnitLifecycleIntegrationScreen.byteCrc ourB storeB
                                                            bytes.deref seedB =
                                                          ok (core.result.Result.Ok (sB', ptB), storeB', rngB') ∧
                                                        lifecycle.Session.encrypt
                                                              Tacenta.UnitLifecycleIntegrationScreen.byteRng
                                                              Tacenta.UnitLifecycleIntegrationScreen.byteCrc sB' ptR
                                                              rngB' =
                                                            ok (core.result.Result.Ok bytesR, sB'', rngB') ∧
                                                          lifecycle.Session.decrypt
                                                                Tacenta.UnitLifecycleIntegrationScreen.byteRng
                                                                Tacenta.UnitLifecycleIntegrationScreen.byteCrc s'
                                                                bytesR.deref rng' =
                                                              ok (core.result.Result.Ok ptA, s'', rngA') ∧
                                                            ↑ptA = ↑ptR ∧
                                                              s''.pending_initial = none ∧
                                                                Tacenta.UnitLifecycleT3.StepRefines
                                                                    Tacenta.UnitLifecycleIntegrationScreen.byteTrace dh
                                                                    oracle.braidKem
                                                                    (core.result.Result.Ok ptA, s'', rngA')
                                                                    (Model.Lifecycle.decrypt
                                                                      Tacenta.UnitLifecycleRepair.witnessView
                                                                      {
                                                                        draws :=
                                                                          Tacenta.UnitLifecycleIntegrationScreen.byteTrace
                                                                            rng',
                                                                        braidKem := oracle.braidKem,
                                                                        dhPublic := oracle.dhPublic,
                                                                        dhAgree := oracle.dhAgree,
                                                                        identityValid := oracle.identityValid,
                                                                        aeadSeal := oracle.aeadSeal,
                                                                        aeadOpen := oracle.aeadOpen,
                                                                        kemValid := oracle.kemValid,
                                                                        kemEncaps := oracle.kemEncaps,
                                                                        kemDecaps := oracle.kemDecaps,
                                                                        sigVerify := oracle.sigVerify,
                                                                        sigSign := oracle.sigSign }
                                                                      mA
                                                                      (Tacenta.UnitLifecycleT3.sliceOf bytesR.deref)) ∧
                                                                  Model.Lifecycle.AeadOpenLength
                                                                      {
                                                                        draws :=
                                                                          Tacenta.UnitLifecycleIntegrationScreen.byteTrace
                                                                            rng',
                                                                        braidKem := oracle.braidKem,
                                                                        dhPublic := oracle.dhPublic,
                                                                        dhAgree := oracle.dhAgree,
                                                                        identityValid := oracle.identityValid,
                                                                        aeadSeal := oracle.aeadSeal,
                                                                        aeadOpen := oracle.aeadOpen,
                                                                        kemValid := oracle.kemValid,
                                                                        kemEncaps := oracle.kemEncaps,
                                                                        kemDecaps := oracle.kemDecaps,
                                                                        sigVerify := oracle.sigVerify,
                                                                        sigSign := oracle.sigSign } ∧
                                                                    (↑ptA).length ≤ Model.Lifecycle.maxPlaintextLen
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSizeWitness.size_witness_reachable

/--
info: def Tacenta.UnitLifecycleSizeWitness.padLen : ℕ → ℕ :=
fun n => 16 - n % 16
-/
#guard_msgs in
#print Tacenta.UnitLifecycleSizeWitness.padLen

/--
info: def Tacenta.UnitLifecycleSizeWitness.byteOf : ℕ → U8 :=
fun k => UScalar.ofNat (k % 256) (⋯ : k % 256 ≤ UScalar.cMax UScalarTy.U8)
-/
#guard_msgs in
#print Tacenta.UnitLifecycleSizeWitness.byteOf

/--
info: def Tacenta.UnitLifecycleSizeWitness.padBody : List U8 → List U8 :=
fun p =>
  p ++
      List.replicate (Tacenta.UnitLifecycleSizeWitness.padLen p.length)
        (Tacenta.UnitLifecycleSizeWitness.byteOf (Tacenta.UnitLifecycleSizeWitness.padLen p.length)) ++
    List.replicate 32 0#u8
-/
#guard_msgs in
#print Tacenta.UnitLifecycleSizeWitness.padBody

/--
info: def Tacenta.UnitLifecycleSizeWitness.padSeal : Slice U8 → alloc.vec.Vec U8 :=
fun p =>
  if h : (↑p).length + 48 ≤ Usize.max then
    ⟨Tacenta.UnitLifecycleSizeWitness.padBody ↑p,
      (⋯ : (Tacenta.UnitLifecycleSizeWitness.padBody ↑p).length ≤ Usize.max)⟩
  else ⟨↑p, (⋯ : (↑p).length ≤ Usize.max)⟩
-/
#guard_msgs in
#print Tacenta.UnitLifecycleSizeWitness.padSeal

/--
info: def Tacenta.UnitLifecycleSizeWitness.padOpen : Slice U8 → core.result.Result (alloc.vec.Vec U8) Unit :=
fun c =>
  match (List.drop ((↑c).length - 33) ↑c).head? with
  | some b =>
    if 33 ≤ (↑c).length ∧ 1 ≤ b.bv.toNat ∧ b.bv.toNat + 32 ≤ (↑c).length then
      core.result.Result.Ok
        ⟨List.take ((↑c).length - 32 - b.bv.toNat) ↑c,
          (⋯ : (List.take ((↑c).length - 32 - b.bv.toNat) ↑c).length ≤ Usize.max)⟩
    else core.result.Result.Err ()
  | none => core.result.Result.Err ()
-/
#guard_msgs in
#print Tacenta.UnitLifecycleSizeWitness.padOpen

/--
info: def Tacenta.UnitLifecycleSizeWitness.Interp.modelPadded : Tacenta.UnitSatisfiabilityJoint.Interp :=
have __src := Tacenta.UnitLifecycleResponderReplyReceipt.Interp.modelReply;
{ PrivateKey := __src.PrivateKey, PublicKeyBytes := __src.PublicKeyBytes, KemKeyPair := __src.KemKeyPair,
  IncrementalKeyPair := __src.IncrementalKeyPair, EncapsState := __src.EncapsState, Zeroizing := __src.Zeroizing,
  dhPrivFromBytes := __src.dhPrivFromBytes, dhPrivPublicKey := __src.dhPrivPublicKey, dhPrivAgree := __src.dhPrivAgree,
  dhPrivToBytes := __src.dhPrivToBytes, dhPubFromBytes := __src.dhPubFromBytes, dhPubAsBytes := __src.dhPubAsBytes,
  dhPubEq := __src.dhPubEq, dhIsPrimeOrderPublic := __src.dhIsPrimeOrderPublic,
  aeadEncrypt := fun x x_1 x_2 p x_3 => ok (Tacenta.UnitLifecycleSizeWitness.padSeal p),
  aeadDecrypt := fun x x_1 x_2 c x_3 => ok (Tacenta.UnitLifecycleSizeWitness.padOpen c),
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
#print Tacenta.UnitLifecycleSizeWitness.Interp.modelPadded

/--
info: def Tacenta.UnitLifecycleSizeWitness.InterpO.modelPadded : Tacenta.UnitOracleShape.InterpO :=
have __src := Tacenta.UnitLifecycleSizeWitness.Interp.modelPadded;
{ toInterp := __src, xeddsaSign := fun {R} => Tacenta.UnitOracleModel.signModelO }
-/
#guard_msgs in
#print Tacenta.UnitLifecycleSizeWitness.InterpO.modelPadded

/--
info: def Tacenta.UnitLifecycleSizeWitness.viewPadded : Tacenta.UnitLifecycleDecryptRatchetScreen.DhViewShape
  Tacenta.UnitLifecycleSizeWitness.Interp.modelPadded :=
{ privateKey := Tacenta.UnitLifecycleT3.arrayOf, publicKey := Tacenta.UnitLifecycleT3.arrayOf }
-/
#guard_msgs in
#print Tacenta.UnitLifecycleSizeWitness.viewPadded

/--
info: def Tacenta.UnitLifecycleSizeWitness.dhViewPadded : Tacenta.UnitOracleShape.DhViewOf
  Tacenta.UnitLifecycleSizeWitness.InterpO.modelPadded.toInterp :=
{ privateKey := Tacenta.UnitLifecycleSizeWitness.viewPadded.privateKey,
  publicKey := Tacenta.UnitLifecycleSizeWitness.viewPadded.publicKey }
-/
#guard_msgs in
#print Tacenta.UnitLifecycleSizeWitness.dhViewPadded

/--
info: def Tacenta.UnitLifecycleSizeWitness.kemViewPadded : Tacenta.UnitOracleShape.KemViewOf
  Tacenta.UnitLifecycleSizeWitness.InterpO.modelPadded.toInterp :=
{ keyPair := fun x => [] }
-/
#guard_msgs in
#print Tacenta.UnitLifecycleSizeWitness.kemViewPadded

/--
info: def Tacenta.UnitLifecycleSizeWitness.AeadOpenLengthShape : Tacenta.UnitSatisfiabilityJoint.Interp → Prop :=
fun I =>
  ∀ (k1 k2 : Std.Array U8 32#usize) (iv : Std.Array U8 16#usize) (c ad : Slice U8) (v : alloc.vec.Vec U8),
    I.aeadDecrypt k1 k2 iv c ad = ok (core.result.Result.Ok v) → (↑v).length + 33 ≤ (↑c).length
-/
#guard_msgs in
#print Tacenta.UnitLifecycleSizeWitness.AeadOpenLengthShape

/--
info: def Tacenta.UnitLifecycleSizeWitness.AeadOpenLengthLaw : Prop :=
Tacenta.UnitLifecycleSizeWitness.AeadOpenLengthShape Tacenta.UnitSatisfiabilityJoint.Interp.real
-/
#guard_msgs in
#print Tacenta.UnitLifecycleSizeWitness.AeadOpenLengthLaw
