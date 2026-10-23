import Translation.KdfT3Kdf
import Translation.KdfBridgeHmac
import Translation.KdfBridgeHkdf
import Translation.UnitSatisfiabilityJoint
import Translation.UnitLifecycleDecryptRatchetCompleteT3
import Translation.UnitSatisfiabilityBraidAgreements
import Translation.UnitLifecycleDecryptScreen
import Translation.UnitLifecycleDecryptRatchetScreen
import Translation.UnitLifecycleResponderFirstReceipt
import Translation.UnitLifecycleEstablishedEncrypt
import Translation.UnitLifecycleEstablishedDecrypt
import Translation.UnitLifecycleResponderFirstFrame
import Translation.UnitLifecycleResponderReplyReceipt

/-!
# UnitLifecycleKdf

The Session unit's HMAC-SHA256 and HKDF-SHA256, now translated from the copied bodies of `tacenta-kdf`,
return and equal tacenta-model's: `HmacAgrees` and `HkdfAgrees` as theorems, the other KDF propositions the
lifecycle results take, and `decrypt_ratchet`'s complete refinement without them.

`tacenta-kdf`'s bodies are a SHA-256, an HMAC-SHA256 and an HKDF-SHA256 copied from a separate, unpublished
repository of this project's maintainer (`tacenta-core/kdf/src/lib.rs` pins it by commit and file digests and
says what changed). Charon translates them
into the Session unit (`run-aeneas.sh`, `--include-kdf`), so `tacenta_session_unit.tacenta_kdf.hmac_sha256`
and `hkdf_sha256` are definitions there, one-line wrappers over `hmac.hmac_sha256` and
`hkdf.hkdf_sha256`. The `Kdf*` modules are that repository's own proofs, copied and elaborated
against the unit's translation:

* `KdfT1Sha`, `KdfT1Kdf`: the translated functions never fail (HKDF for outputs of at most 8160 bytes);
* `KdfT3Compress`, `KdfT3Stream`, `KdfT3Kdf`: they compute a model of SHA-256, HMAC and HKDF written from
  FIPS 180-4, FIPS 198-1 and RFC 5869 (`KdfModel*`), `hmac_sha256_spec` and `hkdf_sha256_spec`;
* `KdfBridgeSha256`, `KdfBridgeHmac`, `KdfBridgeHkdf`: that model equals tacenta-model's `Model.Sha256.hash`,
  `Model.Kdf.hmac` and `Model.Kdf.hkdf` (`KdfBridge.hmac_eq`, `KdfBridge.hkdf_eq`).

This module composes them at the unit's own constants. `hmacAgrees` and `hkdfAgrees` state
`Tacenta.SessionUnitT3.HmacAgrees` and `Tacenta.SessionUnitT3.HkdfAgrees` by name, so their statements are the
tree's own definitions, not a restatement. Each unfolds the wrapper in one step and composes the T3
specification with the bridge. The eleven other propositions (the Braid, sparse-ratchet and Triple copies of
the agreements, the five totality hypotheses and the joint model's two shapes at the real interpretation)
follow from those two.

`DecryptRatchetAgreements.of_kdf` builds `decrypt_ratchet`'s agreement record from the record's other
fields (`KdfFreeAgreements`) and the two theorems, so any result that takes the record can be had without
its KDF fields. `decrypt_ratchet_refines_complete_of_kdf` is the complete refinement of
`UnitLifecycleDecryptRatchetCompleteT3` stated that way: the same hypotheses but for the two KDF fields.

## The laws and premises

* None new. The two theorems take no hypothesis; the corollary takes every hypothesis of
  `decrypt_ratchet_refines_complete` except the record's `hmac` and `hkdf` fields.

## Non-vacuity

* `hmacAgrees` and `hkdfAgrees` are unconditional statements about the unit's translated functions, so there
  is no premise to satisfy. The corollary's remaining premises are those of
  `decrypt_ratchet_refines_complete`, whose non-vacuity is that module's.

## What it does not show

* that the copied Rust agrees with the RustCrypto code it replaced: that is the workspace's tests and a differential
  test (`kdf/tests/differential.rs`), not a proof;
* that tacenta-model's KDF is RFC 4231's HMAC or RFC 5869's HKDF: it is checked against their vectors, not proved;
* any cryptographic property of HMAC or HKDF (pseudorandomness, key separation);
* constant time or erasure of the copied code's intermediates (the constant-time gate reads an inventory of its
  compiled branches, which is a review, not a proof, and nothing erases the intermediates);
* the other translations' KDF hypotheses, which `KdfLeafAgreements` and `KdfTripleUnitAgreements` prove, not this
  module;
* the SHA-256 and HMAC calls outside `tacenta-kdf`: the AEAD's tag check on decryption and the identity and group
  digests still call RustCrypto;
* that the translation is faithful to the compiled Rust (Charon and Aeneas are trusted, as for every translated result);
* the other fields of `DecryptRatchetAgreements` and every other premise of the lifecycle results, which stay open.
-/

namespace Tacenta.UnitLifecycleKdf

open Aeneas Aeneas.Std Result
open tacenta_session_unit

/-- **`HmacAgrees`, a theorem.** The Session unit's `tacenta_kdf.hmac_sha256` returns, for every key and
message, and returns tacenta-model's `Model.Kdf.hmac` of their bytes. -/
theorem hmacAgrees : Tacenta.SessionUnitT3.HmacAgrees := by
  intro key data
  obtain ⟨r, hr, hv⟩ := WP.spec_imp_exists (Tacenta.KdfProof.hmac_sha256_spec key data)
  refine ⟨r, by unfold tacenta_kdf.hmac_sha256; exact hr, ?_⟩
  have hk : Tacenta.SessionUnitT3.keyOf r = Tacenta.KdfProof.bytesOf r := rfl
  have hs : ∀ s, Tacenta.SessionUnitT3.sliceOf s = Tacenta.KdfProof.sliceBytes s := fun _ => rfl
  rw [hk, hv, hs, hs, KdfBridge.hmac_eq]

/-- **`HkdfAgrees`, a theorem.** The Session unit's `tacenta_kdf.hkdf_sha256` returns, for every output
length of at most 8160 bytes and every salt, input keying material and info, and returns tacenta-model's
`Model.Kdf.hkdf` of their bytes at that length. (`HkdfAgrees` names its slices `key salt info` in the Rust's
argument order: the first is the salt, the second the input keying material.) -/
theorem hkdfAgrees : Tacenta.SessionUnitT3.HkdfAgrees := by
  intro N key salt info hN
  obtain ⟨r, hr, hv⟩ := WP.spec_imp_exists (Tacenta.KdfProof.hkdf_sha256_spec N key salt info hN)
  refine ⟨r, by unfold tacenta_kdf.hkdf_sha256; exact hr, ?_⟩
  have hk : Tacenta.SessionUnitT3.keyOf r = Tacenta.KdfProof.bytesOf r := rfl
  have hs : ∀ s, Tacenta.SessionUnitT3.sliceOf s = Tacenta.KdfProof.sliceBytes s := fun _ => rfl
  rw [hk, hv, hs, hs, hs, KdfBridge.hkdf_eq]

/-! ## The other KDF propositions the unit's results take -/

theorem braidHmacAgrees : Tacenta.SessionUnitBraidT3.BraidHmacAgrees := by
  intro key data
  exact hmacAgrees key data

theorem braidHkdfAgrees : Tacenta.SessionUnitBraidT3.BraidHkdfAgrees := by
  intro N salt ikm info hN
  exact hkdfAgrees N salt ikm info hN

theorem spqrHkdfAgrees : Tacenta.SessionUnitSpqrT3.SpqrHkdfAgrees := by
  intro N salt ikm info hN
  exact hkdfAgrees N salt ikm info hN

theorem tripleHkdfAgrees : Tacenta.SessionUnitTripleT3.TripleHkdfAgrees := by
  intro N salt ikm info hN
  exact hkdfAgrees N salt ikm info hN

theorem hmacTotal : Tacenta.SessionUnitT1.HmacTotal :=
  Tacenta.SessionUnitT3.HmacAgrees.total hmacAgrees

theorem hkdfTotal : Tacenta.SessionUnitT1.HkdfTotal :=
  Tacenta.SessionUnitT3.HkdfAgrees.total hkdfAgrees

theorem sessionHkdfTotal : Tacenta.SessionUnitSessionT1.HkdfTotal := by
  intro N salt ikm info hN
  obtain ⟨r, hr, _⟩ := hkdfAgrees N salt ikm info hN
  exact ⟨r, hr⟩

theorem braidHkdfSha256Total : Tacenta.SessionUnitBraidT1.HkdfSha256Total :=
  Tacenta.SessionUnitBraidT3.BraidHkdfAgrees.total braidHkdfAgrees

theorem braidHmacSha256Total : Tacenta.SessionUnitBraidT1.HmacSha256Total := by
  intro key data
  obtain ⟨r, hr, _⟩ := hmacAgrees key data
  exact ⟨r, hr⟩

theorem hmacShape_real :
    Tacenta.UnitSatisfiabilityJoint.HmacShape Tacenta.UnitSatisfiabilityJoint.Interp.real :=
  Tacenta.UnitSatisfiabilityJoint.TripleHmacTotal_is.mp hmacTotal

theorem hkdfShape_real :
    Tacenta.UnitSatisfiabilityJoint.HkdfShape Tacenta.UnitSatisfiabilityJoint.Interp.real :=
  Tacenta.UnitSatisfiabilityJoint.TripleHkdfTotal_is.mp hkdfTotal

/-! ## `decrypt_ratchet`'s refinement without the KDF fields -/

open Tacenta.UnitLifecycleT3 Tacenta.UnitLifecycleDecryptRatchetT3 in
/-- The fields of `DecryptRatchetAgreements` other than `hmac` and `hkdf`, with the same names and types. -/
structure KdfFreeAgreements (K : Model.Braid.Kem) : Prop where
  zeroizing64 : Tacenta.SessionUnitT3.ZeroizingRoundTrips
  zeroizing80 : Tacenta.SessionUnitT3.ZeroizingRoundTrips80
  zeroizing96 : Tacenta.SessionUnitSpqrT3.ZeroizingRoundTrips96
  zeroizingSparse64 : Tacenta.SessionUnitSpqrT3.ZeroizingRoundTrips64
  pop : Tacenta.UnitSatisfiabilityRatchet.LawPop
  asMut : Tacenta.UnitSatisfiabilityRatchet.LawAsMut
  kem : Tacenta.SessionUnitBraidT3.KemAgreesFor K
  erasure : Tacenta.SessionUnitBraidT3.ErasureAgrees
  kemLen : Tacenta.SessionUnitBraidT3.KemLenAgrees K
  validateEk : Tacenta.SessionUnitBraidT3.ValidateEkAgrees K
  kemClone : Tacenta.SessionUnitBraidT3.KemCloneAgrees
  zeroizing32 : ZeroizingRoundTrips (Array Std.U8 32#usize)

/-- `decrypt_ratchet`'s agreement record from its other fields, with `hmac` and `hkdf` supplied by
`hmacAgrees` and `hkdfAgrees`. -/
theorem DecryptRatchetAgreements.of_kdf {K : Model.Braid.Kem} (rest : KdfFreeAgreements K) :
    Tacenta.UnitLifecycleDecryptRatchetT3.DecryptRatchetAgreements K :=
  ⟨hmacAgrees, hkdfAgrees, rest.zeroizing64, rest.zeroizing80, rest.zeroizing96,
    rest.zeroizingSparse64, rest.pop, rest.asMut, rest.kem, rest.erasure, rest.kemLen, rest.validateEk,
    rest.kemClone, rest.zeroizing32⟩

open Tacenta.UnitLifecycleT3 Tacenta.UnitLifecycleDecryptRatchetT3 in
/-- **`decrypt_ratchet` refines the model's decrypt step on every path, with no KDF premise.**
`UnitLifecycleDecryptRatchetCompleteT3.decrypt_ratchet_refines_complete` with its agreement record built by
`DecryptRatchetAgreements.of_kdf`: every hypothesis is that theorem's, except that the record's `hmac` and
`hkdf` fields are not asked for. -/
theorem decrypt_ratchet_refines_complete_of_kdf {R : Type}
    (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView)
    (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
    (oracleOf : DecryptOracleOf rngCore cryptoRng dh trace oracle)
    (codec : DhCodecOf dh)
    (contracts : Tacenta.UnitLifecycleT1.DecryptRatchetContracts rngCore)
    [Tacenta.SessionUnitT1.DerivedKeysModel]
    (rest : KdfFreeAgreements oracle.braidKem)
    (real : lifecycle.Session) (model : Model.Lifecycle.Session)
    (message : Slice Std.U8) (rng : R)
    (hrel : SessionRefines dh oracle.braidKem real model)
    (headroom : Tacenta.UnitLifecycleT1.DecryptRatchetHeadroom real)
    (htrace : trace rng = oracle.draws)
    (run : DecryptRatchetRun view oracle trace real model message rng) :
    ∃ output,
      lifecycle.Session.decrypt_ratchet rngCore cryptoRng real message rng = ok output ∧
      StepRefines trace dh oracle.braidKem output
        (Model.Lifecycle.decryptRatchet view oracle model (sliceOf message)) :=
  Tacenta.UnitLifecycleDecryptRatchetCompleteT3.decrypt_ratchet_refines_complete rngCore cryptoRng trace
    dh view oracle oracleOf codec contracts (DecryptRatchetAgreements.of_kdf rest) real model message rng
    hrel headroom htrace run

/-! ## The toy interpretations whose KDF is the model's

`Interp.modelT3` gives the two KDF fields the model's HMAC and HKDF as arrays (`hmacImpl`, `hkdfImpl`).
Since the unit's KDF is a definition, the substitution argument behind the joint models does not reach
those two fields; these theorems show that for `Interp.modelT3`, and for the seven interpretations built on
it, the fields are the real definitions on HMAC's whole domain and on HKDF's up to 8160 bytes. -/

/-- A translated byte read as a `UInt8` and written back is the same byte. -/
theorem toU8_u8 (x : Std.U8) :
    Tacenta.UnitSatisfiabilityBraidAgreements.toU8 (Tacenta.SessionUnitBraidT3.u8 x) = x := by
  cases x with
  | mk bv =>
    simp only [Tacenta.UnitSatisfiabilityBraidAgreements.toU8, Tacenta.SessionUnitBraidT3.u8,
      UScalar.val]
    congr 1
    simp

open Tacenta.UnitSatisfiabilityJoint Tacenta.UnitSatisfiabilityBraidAgreements in
/-- `Interp.modelT3`'s HMAC is the unit's real HMAC, on every key and message. -/
theorem modelT3_hmac_eq_real (key data : Slice Std.U8) :
    Interp.modelT3.hmacSha256 key data = Interp.real.hmacSha256 key data := by
  obtain ⟨r, hr, hv⟩ := hmacAgrees key data
  show ok (hmacImpl key data) = tacenta_kdf.hmac_sha256 key data
  rw [hr]
  congr 1
  apply Subtype.ext
  show (Model.Kdf.hmac (Tacenta.SessionUnitBraidT3.sliceOf key)
    (Tacenta.SessionUnitBraidT3.sliceOf data)).map toU8 = r.val
  have hv' : r.val.map Tacenta.SessionUnitBraidT3.u8 =
      Model.Kdf.hmac (Tacenta.SessionUnitBraidT3.sliceOf key) (Tacenta.SessionUnitBraidT3.sliceOf data) := hv
  rw [← hv', List.map_map]
  conv_rhs => rw [← List.map_id r.val]
  exact List.map_congr_left (fun x _ => toU8_u8 x)

open Tacenta.UnitSatisfiabilityJoint Tacenta.UnitSatisfiabilityBraidAgreements in
/-- `Interp.modelT3`'s HKDF is the unit's real HKDF, at every output length of at most 8160 bytes. -/
theorem modelT3_hkdf_eq_real (N : Usize) (salt ikm info : Slice Std.U8) (hN : N.val ≤ 8160) :
    Interp.modelT3.hkdfSha256 N salt ikm info = Interp.real.hkdfSha256 N salt ikm info := by
  obtain ⟨r, hr, hv⟩ := hkdfAgrees N salt ikm info hN
  show ok (hkdfImpl N salt ikm info) = tacenta_kdf.hkdf_sha256 N salt ikm info
  rw [hr]
  congr 1
  apply Subtype.ext
  show (Model.Kdf.hkdf (Tacenta.SessionUnitBraidT3.sliceOf salt) (Tacenta.SessionUnitBraidT3.sliceOf ikm)
    (Tacenta.SessionUnitBraidT3.sliceOf info) N.val).map toU8 = r.val
  have hv' : r.val.map Tacenta.SessionUnitBraidT3.u8 =
      Model.Kdf.hkdf (Tacenta.SessionUnitBraidT3.sliceOf salt) (Tacenta.SessionUnitBraidT3.sliceOf ikm)
        (Tacenta.SessionUnitBraidT3.sliceOf info) N.val := hv
  rw [← hv', List.map_map]
  conv_rhs => rw [← List.map_id r.val]
  exact List.map_congr_left (fun x _ => toU8_u8 x)

open Tacenta.UnitSatisfiabilityJoint Tacenta.UnitSatisfiabilityBraidAgreements in
/-- The seven interpretations of the lifecycle screens and models built on `Interp.modelT3` keep its two
KDF fields. -/
theorem toy_models_share_modelT3_kdf :
    (Tacenta.UnitLifecycleDecryptScreen.Interp.modelShipped).hmacSha256 = Interp.modelT3.hmacSha256 ∧
    (Tacenta.UnitLifecycleDecryptScreen.Interp.modelShipped).hkdfSha256 = Interp.modelT3.hkdfSha256 ∧
    (Tacenta.UnitLifecycleDecryptRatchetScreen.Interp.modelDecrypt).hmacSha256 = Interp.modelT3.hmacSha256 ∧
    (Tacenta.UnitLifecycleDecryptRatchetScreen.Interp.modelDecrypt).hkdfSha256 = Interp.modelT3.hkdfSha256 ∧
    (Tacenta.UnitLifecycleResponderFirstReceipt.Interp.modelFirstReceipt).hmacSha256 =
      Interp.modelT3.hmacSha256 ∧
    (Tacenta.UnitLifecycleResponderFirstReceipt.Interp.modelFirstReceipt).hkdfSha256 =
      Interp.modelT3.hkdfSha256 ∧
    (Tacenta.UnitLifecycleEstablishedEncrypt.Interp.modelEncrypt).hmacSha256 = Interp.modelT3.hmacSha256 ∧
    (Tacenta.UnitLifecycleEstablishedEncrypt.Interp.modelEncrypt).hkdfSha256 = Interp.modelT3.hkdfSha256 ∧
    (Tacenta.UnitLifecycleEstablishedDecrypt.Interp.modelEstablished).hmacSha256 =
      Interp.modelT3.hmacSha256 ∧
    (Tacenta.UnitLifecycleEstablishedDecrypt.Interp.modelEstablished).hkdfSha256 =
      Interp.modelT3.hkdfSha256 ∧
    (Tacenta.UnitLifecycleResponderFirstFrame.Interp.modelFirstFrame).hmacSha256 =
      Interp.modelT3.hmacSha256 ∧
    (Tacenta.UnitLifecycleResponderFirstFrame.Interp.modelFirstFrame).hkdfSha256 =
      Interp.modelT3.hkdfSha256 ∧
    (Tacenta.UnitLifecycleResponderReplyReceipt.Interp.modelReply).hmacSha256 = Interp.modelT3.hmacSha256 ∧
    (Tacenta.UnitLifecycleResponderReplyReceipt.Interp.modelReply).hkdfSha256 = Interp.modelT3.hkdfSha256 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end Tacenta.UnitLifecycleKdf

/-! ## Pins

The constants each result depends on, and the statement of each result and definition, held by the
build.  `attest.py` requires every one of them (`REQUIRED_PINS`, `REQUIRED_STATEMENT_PINS`,
`REQUIRED_PRINT_FORM`). -/

/--
info: 'Tacenta.UnitLifecycleKdf.hmacAgrees' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleKdf.hmacAgrees

/--
info: 'Tacenta.UnitLifecycleKdf.hkdfAgrees' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleKdf.hkdfAgrees

/--
info: 'Tacenta.UnitLifecycleKdf.braidHmacAgrees' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleKdf.braidHmacAgrees

/--
info: 'Tacenta.UnitLifecycleKdf.braidHkdfAgrees' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleKdf.braidHkdfAgrees

/--
info: 'Tacenta.UnitLifecycleKdf.spqrHkdfAgrees' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleKdf.spqrHkdfAgrees

/--
info: 'Tacenta.UnitLifecycleKdf.tripleHkdfAgrees' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleKdf.tripleHkdfAgrees

/--
info: 'Tacenta.UnitLifecycleKdf.hmacTotal' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleKdf.hmacTotal

/--
info: 'Tacenta.UnitLifecycleKdf.hkdfTotal' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleKdf.hkdfTotal

/--
info: 'Tacenta.UnitLifecycleKdf.sessionHkdfTotal' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleKdf.sessionHkdfTotal

/--
info: 'Tacenta.UnitLifecycleKdf.braidHkdfSha256Total' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleKdf.braidHkdfSha256Total

/--
info: 'Tacenta.UnitLifecycleKdf.braidHmacSha256Total' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleKdf.braidHmacSha256Total

/--
info: 'Tacenta.UnitLifecycleKdf.hmacShape_real' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleKdf.hmacShape_real

/--
info: 'Tacenta.UnitLifecycleKdf.hkdfShape_real' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleKdf.hkdfShape_real

/--
info: 'Tacenta.UnitLifecycleKdf.DecryptRatchetAgreements.of_kdf' depends on axioms: [propext,
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
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.generate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.header,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.alloc.vec.Vec.pop,
 tacenta_session_unit.alloc.vec.Vec.truncate,
 tacenta_session_unit.core.num.Usize.div_ceil,
 tacenta_session_unit.core.option.Option.as_mut,
 tacenta_session_unit.tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleKdf.DecryptRatchetAgreements.of_kdf

/--
info: 'Tacenta.UnitLifecycleKdf.decrypt_ratchet_refines_complete_of_kdf' depends on axioms: [propext,
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
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
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
#print axioms Tacenta.UnitLifecycleKdf.decrypt_ratchet_refines_complete_of_kdf

/--
info: 'Tacenta.UnitLifecycleKdf.toU8_u8' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleKdf.toU8_u8

/--
info: 'Tacenta.UnitLifecycleKdf.modelT3_hmac_eq_real' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleKdf.modelT3_hmac_eq_real

/--
info: 'Tacenta.UnitLifecycleKdf.modelT3_hkdf_eq_real' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleKdf.modelT3_hkdf_eq_real

/--
info: 'Tacenta.UnitLifecycleKdf.toy_models_share_modelT3_kdf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleKdf.toy_models_share_modelT3_kdf

/--
info: Tacenta.UnitLifecycleKdf.hmacAgrees : Tacenta.SessionUnitT3.HmacAgrees
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleKdf.hmacAgrees

/--
info: Tacenta.UnitLifecycleKdf.hkdfAgrees : Tacenta.SessionUnitT3.HkdfAgrees
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleKdf.hkdfAgrees

/--
info: Tacenta.UnitLifecycleKdf.braidHmacAgrees : Tacenta.SessionUnitBraidT3.BraidHmacAgrees
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleKdf.braidHmacAgrees

/--
info: Tacenta.UnitLifecycleKdf.braidHkdfAgrees : Tacenta.SessionUnitBraidT3.BraidHkdfAgrees
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleKdf.braidHkdfAgrees

/--
info: Tacenta.UnitLifecycleKdf.spqrHkdfAgrees : Tacenta.SessionUnitSpqrT3.SpqrHkdfAgrees
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleKdf.spqrHkdfAgrees

/--
info: Tacenta.UnitLifecycleKdf.tripleHkdfAgrees : Tacenta.SessionUnitTripleT3.TripleHkdfAgrees
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleKdf.tripleHkdfAgrees

/--
info: Tacenta.UnitLifecycleKdf.hmacTotal : Tacenta.SessionUnitT1.HmacTotal
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleKdf.hmacTotal

/--
info: Tacenta.UnitLifecycleKdf.hkdfTotal : Tacenta.SessionUnitT1.HkdfTotal
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleKdf.hkdfTotal

/--
info: Tacenta.UnitLifecycleKdf.sessionHkdfTotal : Tacenta.SessionUnitSessionT1.HkdfTotal
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleKdf.sessionHkdfTotal

/--
info: Tacenta.UnitLifecycleKdf.braidHkdfSha256Total : Tacenta.SessionUnitBraidT1.HkdfSha256Total
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleKdf.braidHkdfSha256Total

/--
info: Tacenta.UnitLifecycleKdf.braidHmacSha256Total : Tacenta.SessionUnitBraidT1.HmacSha256Total
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleKdf.braidHmacSha256Total

/--
info: Tacenta.UnitLifecycleKdf.hmacShape_real : Tacenta.UnitSatisfiabilityJoint.HmacShape
  Tacenta.UnitSatisfiabilityJoint.Interp.real
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleKdf.hmacShape_real

/--
info: Tacenta.UnitLifecycleKdf.hkdfShape_real : Tacenta.UnitSatisfiabilityJoint.HkdfShape
  Tacenta.UnitSatisfiabilityJoint.Interp.real
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleKdf.hkdfShape_real

/--
info: @Tacenta.UnitLifecycleKdf.DecryptRatchetAgreements.of_kdf : ∀ {K : Model.Braid.Kem},
  Tacenta.UnitLifecycleKdf.KdfFreeAgreements K → Tacenta.UnitLifecycleDecryptRatchetT3.DecryptRatchetAgreements K
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleKdf.DecryptRatchetAgreements.of_kdf

/--
info: @Tacenta.UnitLifecycleKdf.decrypt_ratchet_refines_complete_of_kdf : ∀ {R : Type}
  (rngCore : tacenta_session_unit.rand_core_1.RngCore R) (cryptoRng : tacenta_session_unit.rand_core_1.CryptoRng R)
  (trace : R → List Model.Lifecycle.Key) (dh : Tacenta.UnitLifecycleT3.DhView) (view : Model.Lifecycle.CodewordView)
  (oracle : Model.Lifecycle.Oracle),
  Tacenta.UnitLifecycleDecryptRatchetT3.DecryptOracleOf rngCore cryptoRng dh trace oracle →
    Tacenta.UnitLifecycleT3.DhCodecOf dh →
      Tacenta.UnitLifecycleT1.DecryptRatchetContracts rngCore →
        ∀ [Tacenta.SessionUnitT1.DerivedKeysModel],
          Tacenta.UnitLifecycleKdf.KdfFreeAgreements oracle.braidKem →
            ∀ (real : tacenta_session_unit.lifecycle.Session) (model : Model.Lifecycle.Session)
              (message : Aeneas.Std.Slice Aeneas.Std.U8) (rng : R),
              Tacenta.UnitLifecycleT3.SessionRefines dh oracle.braidKem real model →
                Tacenta.UnitLifecycleT1.DecryptRatchetHeadroom real →
                  trace rng = oracle.draws →
                    Tacenta.UnitLifecycleDecryptRatchetT3.DecryptRatchetRun view oracle trace real model message rng →
                      ∃ output,
                        tacenta_session_unit.lifecycle.Session.decrypt_ratchet rngCore cryptoRng real message rng =
                            Aeneas.Std.Result.ok output ∧
                          Tacenta.UnitLifecycleT3.StepRefines trace dh oracle.braidKem output
                            (Model.Lifecycle.decryptRatchet view oracle model (Tacenta.UnitLifecycleT3.sliceOf message))
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleKdf.decrypt_ratchet_refines_complete_of_kdf

/--
info: Tacenta.UnitLifecycleKdf.toU8_u8 : ∀ (x : Aeneas.Std.U8),
  Tacenta.UnitSatisfiabilityBraidAgreements.toU8 (Tacenta.SessionUnitBraidT3.u8 x) = x
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleKdf.toU8_u8

/--
info: Tacenta.UnitLifecycleKdf.modelT3_hmac_eq_real : ∀ (key data : Aeneas.Std.Slice Aeneas.Std.U8),
  Tacenta.UnitSatisfiabilityBraidAgreements.Interp.modelT3.hmacSha256 key data =
    Tacenta.UnitSatisfiabilityJoint.Interp.real.hmacSha256 key data
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleKdf.modelT3_hmac_eq_real

/--
info: Tacenta.UnitLifecycleKdf.modelT3_hkdf_eq_real : ∀ (N : Aeneas.Std.Usize)
  (salt ikm info : Aeneas.Std.Slice Aeneas.Std.U8),
  ↑N ≤ 8160 →
    Tacenta.UnitSatisfiabilityBraidAgreements.Interp.modelT3.hkdfSha256 N salt ikm info =
      Tacenta.UnitSatisfiabilityJoint.Interp.real.hkdfSha256 N salt ikm info
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleKdf.modelT3_hkdf_eq_real

/--
info: Tacenta.UnitLifecycleKdf.toy_models_share_modelT3_kdf : Tacenta.UnitLifecycleDecryptScreen.Interp.modelShipped.hmacSha256 =
    Tacenta.UnitSatisfiabilityBraidAgreements.Interp.modelT3.hmacSha256 ∧
  Tacenta.UnitLifecycleDecryptScreen.Interp.modelShipped.hkdfSha256 =
      Tacenta.UnitSatisfiabilityBraidAgreements.Interp.modelT3.hkdfSha256 ∧
    Tacenta.UnitLifecycleDecryptRatchetScreen.Interp.modelDecrypt.hmacSha256 =
        Tacenta.UnitSatisfiabilityBraidAgreements.Interp.modelT3.hmacSha256 ∧
      Tacenta.UnitLifecycleDecryptRatchetScreen.Interp.modelDecrypt.hkdfSha256 =
          Tacenta.UnitSatisfiabilityBraidAgreements.Interp.modelT3.hkdfSha256 ∧
        Tacenta.UnitLifecycleResponderFirstReceipt.Interp.modelFirstReceipt.hmacSha256 =
            Tacenta.UnitSatisfiabilityBraidAgreements.Interp.modelT3.hmacSha256 ∧
          Tacenta.UnitLifecycleResponderFirstReceipt.Interp.modelFirstReceipt.hkdfSha256 =
              Tacenta.UnitSatisfiabilityBraidAgreements.Interp.modelT3.hkdfSha256 ∧
            Tacenta.UnitLifecycleEstablishedEncrypt.Interp.modelEncrypt.hmacSha256 =
                Tacenta.UnitSatisfiabilityBraidAgreements.Interp.modelT3.hmacSha256 ∧
              Tacenta.UnitLifecycleEstablishedEncrypt.Interp.modelEncrypt.hkdfSha256 =
                  Tacenta.UnitSatisfiabilityBraidAgreements.Interp.modelT3.hkdfSha256 ∧
                Tacenta.UnitLifecycleEstablishedDecrypt.Interp.modelEstablished.hmacSha256 =
                    Tacenta.UnitSatisfiabilityBraidAgreements.Interp.modelT3.hmacSha256 ∧
                  Tacenta.UnitLifecycleEstablishedDecrypt.Interp.modelEstablished.hkdfSha256 =
                      Tacenta.UnitSatisfiabilityBraidAgreements.Interp.modelT3.hkdfSha256 ∧
                    Tacenta.UnitLifecycleResponderFirstFrame.Interp.modelFirstFrame.hmacSha256 =
                        Tacenta.UnitSatisfiabilityBraidAgreements.Interp.modelT3.hmacSha256 ∧
                      Tacenta.UnitLifecycleResponderFirstFrame.Interp.modelFirstFrame.hkdfSha256 =
                          Tacenta.UnitSatisfiabilityBraidAgreements.Interp.modelT3.hkdfSha256 ∧
                        Tacenta.UnitLifecycleResponderReplyReceipt.Interp.modelReply.hmacSha256 =
                            Tacenta.UnitSatisfiabilityBraidAgreements.Interp.modelT3.hmacSha256 ∧
                          Tacenta.UnitLifecycleResponderReplyReceipt.Interp.modelReply.hkdfSha256 =
                            Tacenta.UnitSatisfiabilityBraidAgreements.Interp.modelT3.hkdfSha256
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleKdf.toy_models_share_modelT3_kdf

/--
info: structure Tacenta.UnitLifecycleKdf.KdfFreeAgreements (K : Model.Braid.Kem) : Prop
number of parameters: 1
fields:
  Tacenta.UnitLifecycleKdf.KdfFreeAgreements.zeroizing64 : Tacenta.SessionUnitT3.ZeroizingRoundTrips
  Tacenta.UnitLifecycleKdf.KdfFreeAgreements.zeroizing80 : Tacenta.SessionUnitT3.ZeroizingRoundTrips80
  Tacenta.UnitLifecycleKdf.KdfFreeAgreements.zeroizing96 : Tacenta.SessionUnitSpqrT3.ZeroizingRoundTrips96
  Tacenta.UnitLifecycleKdf.KdfFreeAgreements.zeroizingSparse64 : Tacenta.SessionUnitSpqrT3.ZeroizingRoundTrips64
  Tacenta.UnitLifecycleKdf.KdfFreeAgreements.pop : Tacenta.UnitSatisfiabilityRatchet.LawPop
  Tacenta.UnitLifecycleKdf.KdfFreeAgreements.asMut : Tacenta.UnitSatisfiabilityRatchet.LawAsMut
  Tacenta.UnitLifecycleKdf.KdfFreeAgreements.kem : Tacenta.SessionUnitBraidT3.KemAgreesFor K
  Tacenta.UnitLifecycleKdf.KdfFreeAgreements.erasure : Tacenta.SessionUnitBraidT3.ErasureAgrees
  Tacenta.UnitLifecycleKdf.KdfFreeAgreements.kemLen : Tacenta.SessionUnitBraidT3.KemLenAgrees K
  Tacenta.UnitLifecycleKdf.KdfFreeAgreements.validateEk : Tacenta.SessionUnitBraidT3.ValidateEkAgrees K
  Tacenta.UnitLifecycleKdf.KdfFreeAgreements.kemClone : Tacenta.SessionUnitBraidT3.KemCloneAgrees
  Tacenta.UnitLifecycleKdf.KdfFreeAgreements.zeroizing32 : Tacenta.UnitLifecycleT3.ZeroizingRoundTrips
      (Aeneas.Std.Array Aeneas.Std.U8 32#usize)
constructor:
  Tacenta.UnitLifecycleKdf.KdfFreeAgreements.mk {K : Model.Braid.Kem}
    (zeroizing64 : Tacenta.SessionUnitT3.ZeroizingRoundTrips)
    (zeroizing80 : Tacenta.SessionUnitT3.ZeroizingRoundTrips80)
    (zeroizing96 : Tacenta.SessionUnitSpqrT3.ZeroizingRoundTrips96)
    (zeroizingSparse64 : Tacenta.SessionUnitSpqrT3.ZeroizingRoundTrips64)
    (pop : Tacenta.UnitSatisfiabilityRatchet.LawPop) (asMut : Tacenta.UnitSatisfiabilityRatchet.LawAsMut)
    (kem : Tacenta.SessionUnitBraidT3.KemAgreesFor K) (erasure : Tacenta.SessionUnitBraidT3.ErasureAgrees)
    (kemLen : Tacenta.SessionUnitBraidT3.KemLenAgrees K) (validateEk : Tacenta.SessionUnitBraidT3.ValidateEkAgrees K)
    (kemClone : Tacenta.SessionUnitBraidT3.KemCloneAgrees)
    (zeroizing32 : Tacenta.UnitLifecycleT3.ZeroizingRoundTrips (Aeneas.Std.Array Aeneas.Std.U8 32#usize)) :
    Tacenta.UnitLifecycleKdf.KdfFreeAgreements K
-/
#guard_msgs in
#print Tacenta.UnitLifecycleKdf.KdfFreeAgreements
