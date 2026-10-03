import Translation.UnitLifecycleIntegrationScreen
import Translation.UnitSatisfiabilityRecords

/-!
# The clauses of `OracleOf` over an interpretation of the unit's opaque constants

`OracleOf` (`UnitLifecycleT3.lean`) ties the model's lifecycle oracle to the translated primitives
in twelve clauses. `UnitLifecycleIntegrationScreen.lean` decides five of them under laws
(`random32`, `sigSign` and the three KEM clauses). This module states all twelve over an
interpretation of the opaque constants, so that the remaining seven can be decided by the
substitution argument of `UnitSatisfiabilityJoint.lean`, and derives each from a named law.

## What is here

* `InterpO`: #220's `Interp` and one more field, `xeddsaSign`, the one opaque constant `OracleOf`
  reaches that `Interp` does not interpret. `InterpO.real` packs the real constants.
* `OracleOfShape`: the record `OracleOf` with each real constant replaced by the field of an
  interpretation, and the two view records over the interpretation's types. `oracleOf_iff_shape`
  binds it to `OracleOf` at `InterpO.real` by repacking every field; the kernel accepts a field
  only if its two types unfold to the same proposition, so a field changed, added or removed on
  either side fails the build. `oracleOfShape_iff_clauses` cuts the shape into one named clause per
  field, so each clause can be decided on its own. `dhCodecOf_iff_shape` and
  `generateFillsOnce64_iff_shape` do the same for `DhCodecOf` and the key-generation law.
* The view laws `DhViewInjective` and `KemViewInjective`: a key is determined by its bytes.
* `oracleOfLaws`: the oracle a law-abiding interpretation determines, each primitive's verdict on
  the bytes its arguments view as (by choice of a preimage, which the view law makes unique), with
  the KEM and signing functions of #234's laws.
* One theorem per undecided clause, each from its totality shape and the view law, for that oracle:
  `dhPublicClause_of_laws`, `dhAgreeClause_of_laws`, `identityValidClause_of_laws`,
  `aeadSealClause_of_laws`, `aeadOpenClause_of_laws`, `kemDecapsulateClause_of_laws`,
  `sigVerifyClause_of_laws`.

## The sense

Each `_of_laws` result holds for every interpretation that meets its laws. At `InterpO.real` the
laws are the totality fields of the four contract records, which `UnitSatisfiabilityJoint.lean`
shows have a model, and the view laws, which are about the views the caller chooses and hold of
the real types (32-byte wrappers and a serialised key pair) by reading, not by any proof here. The
model in `UnitOracleModel.lean` meets every law at once.

**Platform width.** No proof here chooses a width of `usize`, and no result depends on a
compiler-trust axiom (the axiom pins), so nothing evaluates the platform width: every result holds
at both widths.
-/

open Aeneas Aeneas.Std Result
open tacenta_session_unit
open Tacenta.UnitLifecycleT3

namespace Tacenta.UnitOracleShape

open Tacenta.UnitSatisfiabilityJoint (Interp Np DhCodecShape DhAgreeShape DhIdentityShape
  AeadSealBoundedShape AeadOpenShape KemDecapsulateShape XeddsaVerifyShape)
open Tacenta.UnitLifecycleIntegrationScreen (byteRng byteCrc byteTrace zeros64 SignFillsOnce64Of
  KemShapeOf sigSignOf kemEncapsOf Random32Clause SigSignClause KemClauses)

/-- #220's interpretation and `xeddsa::sign`, the one opaque constant `OracleOf` reaches that
`Interp` does not interpret. Its type mentions no opaque type of the unit. -/
structure InterpO extends Interp where
  xeddsaSign : {R : Type} → rand_core_1.RngCore R → rand_core_1.CryptoRng R →
    Array U8 32#usize → Slice U8 → R → Result (Array U8 64#usize × R)

/-- The real constants. Each field elaborates only if the real axiom has exactly its type. -/
noncomputable def InterpO.real : InterpO :=
  { Interp.real with xeddsaSign := @tacenta_boundary.xeddsa.sign }

/-- `DhView` over an interpretation's two DH types. -/
structure DhViewOf (I : Interp) where
  privateKey : I.PrivateKey → Bytes
  publicKey : I.PublicKeyBytes → Bytes

/-- `KemView` over an interpretation's KEM key-pair type. -/
structure KemViewOf (I : Interp) where
  keyPair : I.KemKeyPair → Bytes

def dhViewOf (v : DhView) : DhViewOf Interp.real := ⟨v.privateKey, v.publicKey⟩
def kemViewOf (v : KemView) : KemViewOf Interp.real := ⟨v.keyPair⟩

/-- `is_canonical_key` over an interpretation: the same body, with `as_bytes` the interpretation's. -/
def isCanonicalKeyOf (I : Interp) (pk : I.PublicKeyBytes) : Result Bool := do
  let a ← I.dhPubAsBytes pk
  tacenta_session.is_canonical_x25519 a

/-- `is_valid_identity_key` over an interpretation: the same body. -/
def isValidIdentityKeyOf (I : Interp) (pk : I.PublicKeyBytes) : Result Bool := do
  let b ← isCanonicalKeyOf I pk
  if b then I.dhIsPrimeOrderPublic pk else ok false

/-- The real `is_valid_identity_key` is the interpreted body at the real constants. -/
theorem isValidIdentityKey_is (pk : tacenta_boundary.dh.PublicKeyBytes) :
    is_valid_identity_key pk = isValidIdentityKeyOf Interp.real pk := rfl

/-! ## The record over an interpretation -/

/-- `OracleOf`, field for field, with each opaque constant replaced by the interpretation's. -/
structure OracleOfShape (I : InterpO) {R : Type}
    (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (dh : DhViewOf I.toInterp) (kem : KemViewOf I.toInterp) (trace : R → List Model.Lifecycle.Key)
    (oracle : Model.Lifecycle.Oracle) : Prop where
  dhPublic : ∀ secret,
    ∃ publicKey, I.dhPrivPublicKey secret = ok publicKey ∧
      dh.publicKey publicKey = oracle.dhPublic (dh.privateKey secret)
  dhAgree : ∀ secret publicKey,
    ∃ result, I.dhPrivAgree secret publicKey = ok result ∧
      result.map arrayOf = oracle.dhAgree (dh.privateKey secret) (dh.publicKey publicKey)
  identityValid : ∀ publicKey,
    ∃ result,
      isValidIdentityKeyOf I.toInterp publicKey = ok result ∧
      result = oracle.identityValid (dh.publicKey publicKey)
  aeadSeal : ∀ key1 key2 iv ad plaintext,
    ∃ ciphertext,
      I.aeadEncrypt key1 key2 iv ad plaintext = ok ciphertext ∧
      vecOf ciphertext = oracle.aeadSeal (arrayOf key1) (arrayOf key2)
        (arrayOf iv) (sliceOf ad) (sliceOf plaintext)
  aeadOpen : ∀ key1 key2 iv ciphertext associatedData,
    ∃ result,
      I.aeadDecrypt key1 key2 iv ciphertext associatedData = ok result ∧
      resultOptionOf vecOf result = oracle.aeadOpen (arrayOf key1) (arrayOf key2)
        (arrayOf iv) (sliceOf ciphertext) (sliceOf associatedData)
  kemEncapsulateSuccess : ∀ publicKey rng draw rest expected,
    trace rng = draw :: rest →
    oracle.kemEncaps (sliceOf publicKey) draw = some expected →
    ∃ result rng',
      I.kemEncapsulate rngCore cryptoRng publicKey rng =
        ok (.Ok result, rng') ∧
      trace rng' = rest ∧
      encapsulationOf (.Ok result) = some expected
  kemInvalidKey : ∀ publicKey rng error,
    oracle.kemValid (sliceOf publicKey) = false →
    I.kemEncapsulate rngCore cryptoRng publicKey rng =
      ok (.Err error, rng)
  kemEncapsulateError : ∀ publicKey rng error,
    I.kemEncapsulate rngCore cryptoRng publicKey rng =
      ok (.Err error, rng) →
    oracle.kemValid (sliceOf publicKey) = false ∧
    ∀ draw, oracle.kemEncaps (sliceOf publicKey) draw = none
  kemDecapsulate : ∀ keyPair ciphertext,
    ∃ result,
      I.kemDecapsulate keyPair ciphertext = ok result ∧
      resultOptionOf arrayOf result =
        oracle.kemDecaps (kem.keyPair keyPair) (sliceOf ciphertext)
  sigVerify : ∀ publicKey message signature,
    ∃ result,
      I.xeddsaVerify publicKey message signature = ok result ∧
      verified result = oracle.sigVerify (dh.publicKey publicKey)
        (sliceOf message) (arrayOf signature)
  sigSign : ∀ secret message rng draw1 draw2 rest,
    trace rng = draw1 :: draw2 :: rest →
    ∃ signature rng',
      I.xeddsaSign rngCore cryptoRng secret message rng = ok (signature, rng') ∧
      trace rng' = rest ∧
      arrayOf signature = oracle.sigSign (arrayOf secret) (sliceOf message) draw1 draw2
  random32 : ∀ rng draw rest, trace rng = draw :: rest →
    ∃ value rng',
      lifecycle.random_secret rngCore cryptoRng rng = ok (value, rng') ∧
      arrayOf value = draw ∧ trace rng' = rest

/-- **The shape is `OracleOf`** at the real constants: every field is repacked, and the kernel
accepts each only if the two field types unfold to the same proposition. -/
theorem oracleOf_iff_shape {R : Type}
    (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R)
    (dh : DhView) (kem : KemView) (trace : R → List Model.Lifecycle.Key)
    (oracle : Model.Lifecycle.Oracle) :
    OracleOf rc crc dh kem trace oracle ↔
      OracleOfShape InterpO.real rc crc (dhViewOf dh) (kemViewOf kem) trace oracle :=
  ⟨fun h => ⟨h.dhPublic, h.dhAgree, h.identityValid, h.aeadSeal, h.aeadOpen,
      h.kemEncapsulateSuccess, h.kemInvalidKey, h.kemEncapsulateError, h.kemDecapsulate,
      h.sigVerify, h.sigSign, h.random32⟩,
   fun h => ⟨h.dhPublic, h.dhAgree, h.identityValid, h.aeadSeal, h.aeadOpen,
      h.kemEncapsulateSuccess, h.kemInvalidKey, h.kemEncapsulateError, h.kemDecapsulate,
      h.sigVerify, h.sigSign, h.random32⟩⟩

/-! ## One clause per field

The seven clauses #234 left undecided, each over an interpretation. The other five are the
screen's `Random32Clause`, `SigSignClause` and `KemClauses`, stated of a function argument. -/

def DhPublicClause (I : Interp) (dh : DhViewOf I) (oracle : Model.Lifecycle.Oracle) : Prop :=
  ∀ secret, ∃ publicKey, I.dhPrivPublicKey secret = ok publicKey ∧
    dh.publicKey publicKey = oracle.dhPublic (dh.privateKey secret)

def DhAgreeClause (I : Interp) (dh : DhViewOf I) (oracle : Model.Lifecycle.Oracle) : Prop :=
  ∀ secret publicKey, ∃ result, I.dhPrivAgree secret publicKey = ok result ∧
    result.map arrayOf = oracle.dhAgree (dh.privateKey secret) (dh.publicKey publicKey)

def IdentityValidClause (I : Interp) (dh : DhViewOf I) (oracle : Model.Lifecycle.Oracle) :
    Prop :=
  ∀ publicKey, ∃ result, isValidIdentityKeyOf I publicKey = ok result ∧
    result = oracle.identityValid (dh.publicKey publicKey)

def AeadSealClause (I : Interp) (oracle : Model.Lifecycle.Oracle) : Prop :=
  ∀ key1 key2 iv ad plaintext, ∃ ciphertext,
    I.aeadEncrypt key1 key2 iv ad plaintext = ok ciphertext ∧
    vecOf ciphertext = oracle.aeadSeal (arrayOf key1) (arrayOf key2)
      (arrayOf iv) (sliceOf ad) (sliceOf plaintext)

def AeadOpenClause (I : Interp) (oracle : Model.Lifecycle.Oracle) : Prop :=
  ∀ key1 key2 iv ciphertext associatedData, ∃ result,
    I.aeadDecrypt key1 key2 iv ciphertext associatedData = ok result ∧
    resultOptionOf vecOf result = oracle.aeadOpen (arrayOf key1) (arrayOf key2)
      (arrayOf iv) (sliceOf ciphertext) (sliceOf associatedData)

def KemDecapsulateClause (I : Interp) (kem : KemViewOf I) (oracle : Model.Lifecycle.Oracle) :
    Prop :=
  ∀ keyPair ciphertext, ∃ result, I.kemDecapsulate keyPair ciphertext = ok result ∧
    resultOptionOf arrayOf result = oracle.kemDecaps (kem.keyPair keyPair) (sliceOf ciphertext)

def SigVerifyClause (I : Interp) (dh : DhViewOf I) (oracle : Model.Lifecycle.Oracle) : Prop :=
  ∀ publicKey message signature, ∃ result,
    I.xeddsaVerify publicKey message signature = ok result ∧
    verified result = oracle.sigVerify (dh.publicKey publicKey)
      (sliceOf message) (arrayOf signature)

/-- **The twelve fields are exactly these ten clauses** (the three KEM fields are `KemClauses`).
A field of the shape without a clause, or a clause that is not the field, fails here. -/
theorem oracleOfShape_iff_clauses (I : InterpO) {R : Type}
    (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R)
    (dh : DhViewOf I.toInterp) (kem : KemViewOf I.toInterp)
    (trace : R → List Model.Lifecycle.Key) (oracle : Model.Lifecycle.Oracle) :
    OracleOfShape I rc crc dh kem trace oracle ↔
      DhPublicClause I.toInterp dh oracle ∧ DhAgreeClause I.toInterp dh oracle ∧
      IdentityValidClause I.toInterp dh oracle ∧ AeadSealClause I.toInterp oracle ∧
      AeadOpenClause I.toInterp oracle ∧ KemClauses (I.kemEncapsulate rc crc) trace oracle ∧
      KemDecapsulateClause I.toInterp kem oracle ∧ SigVerifyClause I.toInterp dh oracle ∧
      SigSignClause (I.xeddsaSign rc crc) trace oracle ∧ Random32Clause rc crc trace :=
  ⟨fun h => ⟨h.dhPublic, h.dhAgree, h.identityValid, h.aeadSeal, h.aeadOpen,
      ⟨h.kemEncapsulateSuccess, h.kemInvalidKey, h.kemEncapsulateError⟩, h.kemDecapsulate,
      h.sigVerify, h.sigSign, h.random32⟩,
   fun ⟨a, b, c, d, e, ⟨f1, f2, f3⟩, g, i, j, k⟩ => ⟨a, b, c, d, e, f1, f2, f3, g, i, j, k⟩⟩

/-! ## The DH codec and the key-generation law over an interpretation -/

/-- `DhCodecOf`, field for field, over an interpretation. -/
structure DhCodecOfShape (I : Interp) (view : DhViewOf I) : Prop where
  privateFromBytes : ∀ bytes, ∃ privateKey,
    I.dhPrivFromBytes bytes = ok privateKey ∧ view.privateKey privateKey = arrayOf bytes
  fromBytes : ∀ bytes, ∃ publicKey,
    I.dhPubFromBytes bytes = ok publicKey ∧ view.publicKey publicKey = arrayOf bytes
  asBytes : ∀ publicKey, ∃ bytes,
    I.dhPubAsBytes publicKey = ok bytes ∧ arrayOf bytes = view.publicKey publicKey

theorem dhCodecOf_iff_shape (view : DhView) :
    DhCodecOf view ↔ DhCodecOfShape Interp.real (dhViewOf view) :=
  ⟨fun h => ⟨h.privateFromBytes, h.fromBytes, h.asBytes⟩,
   fun h => ⟨h.privateFromBytes, h.fromBytes, h.asBytes⟩⟩

/-- The screen's `GenerateFillsOnce64Of`, over an interpretation's key-pair type. -/
def GenerateFillsOnce64Shape (I : Interp) : Prop :=
  ∃ G : Slice U8 → core.result.Result I.IncrementalKeyPair tacenta_kem.KemError,
  ∀ {R : Type} (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R) (rng : R),
    I.ikpGenerate rc crc rng =
      (do let (rng', seed) ← rc.fill_bytes rng zeros64; ok (G seed, rng'))

theorem generateFillsOnce64_iff_shape :
    Tacenta.UnitLifecycleIntegrationScreen.GenerateFillsOnce64 ↔
      GenerateFillsOnce64Shape Interp.real := Iff.rfl

/-! ## The view laws -/

/-- The two DH views are injective: a key is determined by its bytes. -/
def DhViewInjective {I : Interp} (dh : DhViewOf I) : Prop :=
  Function.Injective dh.privateKey ∧ Function.Injective dh.publicKey

/-- The KEM key-pair view is injective. -/
def KemViewInjective {I : Interp} (kem : KemViewOf I) : Prop :=
  Function.Injective kem.keyPair

theorem arrayOf_injective (n : Usize) : Function.Injective (arrayOf (n := n)) := by
  intro a b h
  unfold arrayOf at h
  exact Subtype.ext ((List.map_injective_iff.mpr
    (fun x y hxy => Tacenta.DispatchEvidenceVacuity.u8_inj hxy)) h)

theorem sliceOf_injective : Function.Injective sliceOf :=
  fun _ _ h => Tacenta.DispatchEvidenceVacuity.sliceOf_inj h

/-! ## The oracle a law-abiding interpretation determines -/

/-- The value of a call that returns. -/
def okVal {α : Type} : Result α → Option α
  | ok x => some x
  | _ => none

/-- A function of views read off a function on the viewed type: at a view with a preimage, the
view of the result at a chosen preimage; elsewhere a default. -/
noncomputable def liftView {A V B X : Type} (view : A → V) (f : A → Result B) (out : B → X)
    (d : X) (v : V) : X := by
  classical
  exact if h : ∃ a, view a = v then ((okVal (f h.choose)).map out).getD d else d

/-- With an injective view and a total function, the lifted function is the function on views. -/
theorem liftView_spec {A V B X : Type} {view : A → V} (hinj : Function.Injective view)
    (f : A → Result B) (hf : ∀ a, ∃ r, f a = ok r) (out : B → X) (d : X) (a : A) :
    ∃ r, f a = ok r ∧ out r = liftView view f out d (view a) := by
  obtain ⟨r, hr⟩ := hf a
  refine ⟨r, hr, ?_⟩
  have h : ∃ a', view a' = view a := ⟨a, rfl⟩
  unfold liftView
  rw [dif_pos h]
  have e : h.choose = a := hinj h.choose_spec
  rw [e, hr]
  rfl

/-- The oracle of an interpretation, given the two views and the functions #234's KEM and signing
laws name: each primitive's verdict on the bytes its arguments view as. The fields `OracleOf` does
not constrain (`draws`, `braidKem`) are those of `toyOracle []`. -/
noncomputable def oracleOfLaws (I : InterpO) (dh : DhViewOf I.toInterp)
    (kem : KemViewOf I.toInterp) (valid : Bytes → Bool)
    (E : Bytes → Bytes → alloc.vec.Vec Std.U8 × Array Std.U8 32#usize)
    (S : Array Std.U8 32#usize → Slice Std.U8 → Slice Std.U8 → Array Std.U8 64#usize) :
    Model.Lifecycle.Oracle :=
  { Model.Lifecycle.Examples.toyOracle [] with
    dhPublic := liftView dh.privateKey I.dhPrivPublicKey dh.publicKey []
    dhAgree := fun s p => liftView (Prod.map dh.privateKey dh.publicKey)
      (fun x => I.dhPrivAgree x.1 x.2) (Option.map arrayOf) none (s, p)
    identityValid := liftView dh.publicKey (isValidIdentityKeyOf I.toInterp) id false
    aeadSeal := fun k1 k2 iv b4 b5 =>
      liftView (Prod.map (arrayOf (n := 32#usize)) (Prod.map (arrayOf (n := 32#usize))
          (Prod.map (arrayOf (n := 16#usize)) (Prod.map sliceOf sliceOf))))
        (fun x => I.aeadEncrypt x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2) vecOf []
        (k1, k2, iv, b4, b5)
    aeadOpen := fun k1 k2 iv b4 b5 =>
      liftView (Prod.map (arrayOf (n := 32#usize)) (Prod.map (arrayOf (n := 32#usize))
          (Prod.map (arrayOf (n := 16#usize)) (Prod.map sliceOf sliceOf))))
        (fun x => I.aeadDecrypt x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2) (resultOptionOf vecOf) none
        (k1, k2, iv, b4, b5)
    kemValid := valid
    kemEncaps := kemEncapsOf valid E
    kemDecaps := fun k c => liftView (Prod.map kem.keyPair sliceOf)
      (fun x => I.kemDecapsulate x.1 x.2) (resultOptionOf arrayOf) none (k, c)
    sigVerify := fun p m s =>
      liftView (Prod.map dh.publicKey (Prod.map sliceOf (arrayOf (n := 64#usize))))
        (fun x => I.xeddsaVerify x.1 x.2.1 x.2.2) verified false (p, m, s)
    sigSign := sigSignOf S }

/-! ## Each undecided clause from its laws -/

section Clauses

variable (I : InterpO) (dh : DhViewOf I.toInterp) (kem : KemViewOf I.toInterp)
  (valid : Bytes → Bool) (E : Bytes → Bytes → alloc.vec.Vec Std.U8 × Array Std.U8 32#usize)
  (S : Array Std.U8 32#usize → Slice Std.U8 → Slice Std.U8 → Array Std.U8 64#usize)

theorem dhPublicClause_of_laws (hcodec : DhCodecShape I.toInterp)
    (hview : Function.Injective dh.privateKey) :
    DhPublicClause I.toInterp dh (oracleOfLaws I dh kem valid E S) :=
  fun secret => liftView_spec hview _ (fun k => hcodec.2.1 k) _ _ secret

theorem dhAgreeClause_of_laws (hagree : DhAgreeShape I.toInterp) (hview : DhViewInjective dh) :
    DhAgreeClause I.toInterp dh (oracleOfLaws I dh kem valid E S) :=
  fun secret publicKey => liftView_spec (hview.1.prodMap hview.2) _
    (fun x => hagree x.1 x.2) _ _ (secret, publicKey)

theorem isValidIdentityKeyOf_total (J : Interp) (hcodec : DhCodecShape J)
    (hid : DhIdentityShape J) (pk : J.PublicKeyBytes) :
    ∃ r, isValidIdentityKeyOf J pk = ok r := by
  obtain ⟨a, ha⟩ := hcodec.2.2.2.2.1 pk
  obtain ⟨c, hc, -⟩ :=
    Std.WP.spec_imp_exists (Tacenta.SessionUnitSessionT1.is_canonical_x25519_spec a)
  unfold isValidIdentityKeyOf isCanonicalKeyOf
  rw [ha]
  simp only [bind_tc_ok, hc]
  split
  · exact hid pk
  · exact ⟨false, rfl⟩

theorem identityValidClause_of_laws (hcodec : DhCodecShape I.toInterp)
    (hid : DhIdentityShape I.toInterp) (hview : Function.Injective dh.publicKey) :
    IdentityValidClause I.toInterp dh (oracleOfLaws I dh kem valid E S) := by
  intro publicKey
  obtain ⟨r, hr, hv⟩ := liftView_spec hview (isValidIdentityKeyOf I.toInterp)
    (isValidIdentityKeyOf_total I.toInterp hcodec hid) id false publicKey
  exact ⟨r, hr, hv⟩

theorem aeadSealClause_of_laws (hseal : AeadSealBoundedShape I.toInterp) :
    AeadSealClause I.toInterp (oracleOfLaws I dh kem valid E S) :=
  fun key1 key2 iv ad plaintext => liftView_spec
    ((arrayOf_injective _).prodMap ((arrayOf_injective _).prodMap ((arrayOf_injective _).prodMap
      (sliceOf_injective.prodMap sliceOf_injective)))) _
    (fun x => (hseal x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2).elim fun r h => ⟨r, h.1⟩) _ _
    (key1, key2, iv, ad, plaintext)

theorem aeadOpenClause_of_laws (hopen : AeadOpenShape I.toInterp) :
    AeadOpenClause I.toInterp (oracleOfLaws I dh kem valid E S) :=
  fun key1 key2 iv ciphertext associatedData => liftView_spec
    ((arrayOf_injective _).prodMap ((arrayOf_injective _).prodMap ((arrayOf_injective _).prodMap
      (sliceOf_injective.prodMap sliceOf_injective)))) _
    (fun x => hopen x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2) _ _
    (key1, key2, iv, ciphertext, associatedData)

theorem kemDecapsulateClause_of_laws (hdecaps : KemDecapsulateShape I.toInterp)
    (hview : KemViewInjective kem) :
    KemDecapsulateClause I.toInterp kem (oracleOfLaws I dh kem valid E S) :=
  fun keyPair ciphertext => liftView_spec (hview.prodMap sliceOf_injective) _
    (fun x => hdecaps x.1 x.2) _ _ (keyPair, ciphertext)

theorem sigVerifyClause_of_laws (hverify : XeddsaVerifyShape I.toInterp)
    (hview : Function.Injective dh.publicKey) :
    SigVerifyClause I.toInterp dh (oracleOfLaws I dh kem valid E S) :=
  fun publicKey message signature => liftView_spec
    (hview.prodMap (sliceOf_injective.prodMap (arrayOf_injective _))) _
    (fun x => hverify x.1 x.2.1 x.2.2) _ _ (publicKey, message, signature)

end Clauses

end Tacenta.UnitOracleShape

/-! ## Pins

The axiom list and the statement of each result, held by the build. `attest.py` requires them
(`REQUIRED_PINS`, `REQUIRED_STATEMENT_PINS`). -/

/--
info: 'Tacenta.UnitOracleShape.isValidIdentityKey_is' depends on axioms: [propext,
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
#print axioms Tacenta.UnitOracleShape.isValidIdentityKey_is

/--
info: Tacenta.UnitOracleShape.isValidIdentityKey_is : ∀ (pk : tacenta_boundary.dh.PublicKeyBytes),
  is_valid_identity_key pk = Tacenta.UnitOracleShape.isValidIdentityKeyOf Tacenta.UnitSatisfiabilityJoint.Interp.real pk
-/
#guard_msgs in
#check @Tacenta.UnitOracleShape.isValidIdentityKey_is

/--
info: 'Tacenta.UnitOracleShape.oracleOf_iff_shape' depends on axioms: [propext,
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
#print axioms Tacenta.UnitOracleShape.oracleOf_iff_shape

/--
info: @Tacenta.UnitOracleShape.oracleOf_iff_shape : ∀ {R : Type} (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R)
  (dh : DhView) (kem : KemView) (trace : R → List Model.Lifecycle.Key) (oracle : Model.Lifecycle.Oracle),
  OracleOf rc crc dh kem trace oracle ↔
    Tacenta.UnitOracleShape.OracleOfShape Tacenta.UnitOracleShape.InterpO.real rc crc
      (Tacenta.UnitOracleShape.dhViewOf dh) (Tacenta.UnitOracleShape.kemViewOf kem) trace oracle
-/
#guard_msgs in
#check @Tacenta.UnitOracleShape.oracleOf_iff_shape

/--
info: 'Tacenta.UnitOracleShape.oracleOfShape_iff_clauses' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitOracleShape.oracleOfShape_iff_clauses

/--
info: Tacenta.UnitOracleShape.oracleOfShape_iff_clauses : ∀ (I : Tacenta.UnitOracleShape.InterpO) {R : Type}
  (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R) (dh : Tacenta.UnitOracleShape.DhViewOf I.toInterp)
  (kem : Tacenta.UnitOracleShape.KemViewOf I.toInterp) (trace : R → List Model.Lifecycle.Key)
  (oracle : Model.Lifecycle.Oracle),
  Tacenta.UnitOracleShape.OracleOfShape I rc crc dh kem trace oracle ↔
    Tacenta.UnitOracleShape.DhPublicClause I.toInterp dh oracle ∧
      Tacenta.UnitOracleShape.DhAgreeClause I.toInterp dh oracle ∧
        Tacenta.UnitOracleShape.IdentityValidClause I.toInterp dh oracle ∧
          Tacenta.UnitOracleShape.AeadSealClause I.toInterp oracle ∧
            Tacenta.UnitOracleShape.AeadOpenClause I.toInterp oracle ∧
              Tacenta.UnitLifecycleIntegrationScreen.KemClauses (I.kemEncapsulate rc crc) trace oracle ∧
                Tacenta.UnitOracleShape.KemDecapsulateClause I.toInterp kem oracle ∧
                  Tacenta.UnitOracleShape.SigVerifyClause I.toInterp dh oracle ∧
                    Tacenta.UnitLifecycleIntegrationScreen.SigSignClause (I.xeddsaSign rc crc) trace oracle ∧
                      Tacenta.UnitLifecycleIntegrationScreen.Random32Clause rc crc trace
-/
#guard_msgs in
#check @Tacenta.UnitOracleShape.oracleOfShape_iff_clauses

/--
info: 'Tacenta.UnitOracleShape.dhCodecOf_iff_shape' depends on axioms: [propext,
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
#print axioms Tacenta.UnitOracleShape.dhCodecOf_iff_shape

/--
info: Tacenta.UnitOracleShape.dhCodecOf_iff_shape : ∀ (view : DhView),
  DhCodecOf view ↔
    Tacenta.UnitOracleShape.DhCodecOfShape Tacenta.UnitSatisfiabilityJoint.Interp.real
      (Tacenta.UnitOracleShape.dhViewOf view)
-/
#guard_msgs in
#check @Tacenta.UnitOracleShape.dhCodecOf_iff_shape

/--
info: 'Tacenta.UnitOracleShape.generateFillsOnce64_iff_shape' depends on axioms: [propext,
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
#print axioms Tacenta.UnitOracleShape.generateFillsOnce64_iff_shape

/--
info: Tacenta.UnitOracleShape.generateFillsOnce64_iff_shape : Tacenta.UnitLifecycleIntegrationScreen.GenerateFillsOnce64 ↔
  Tacenta.UnitOracleShape.GenerateFillsOnce64Shape Tacenta.UnitSatisfiabilityJoint.Interp.real
-/
#guard_msgs in
#check @Tacenta.UnitOracleShape.generateFillsOnce64_iff_shape

/--
info: 'Tacenta.UnitOracleShape.liftView_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitOracleShape.liftView_spec

/--
info: @Tacenta.UnitOracleShape.liftView_spec : ∀ {A V B X : Type} {view : A → V},
  Function.Injective view →
    ∀ (f : A → Result B),
      (∀ (a : A), ∃ r, f a = ok r) →
        ∀ (out : B → X) (d : X) (a : A),
          ∃ r, f a = ok r ∧ out r = Tacenta.UnitOracleShape.liftView view f out d (view a)
-/
#guard_msgs in
#check @Tacenta.UnitOracleShape.liftView_spec

/--
info: 'Tacenta.UnitOracleShape.isValidIdentityKeyOf_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitOracleShape.isValidIdentityKeyOf_total

/--
info: 'Tacenta.UnitOracleShape.dhPublicClause_of_laws' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitOracleShape.dhPublicClause_of_laws

/--
info: Tacenta.UnitOracleShape.dhPublicClause_of_laws : ∀ (I : Tacenta.UnitOracleShape.InterpO)
  (dh : Tacenta.UnitOracleShape.DhViewOf I.toInterp) (kem : Tacenta.UnitOracleShape.KemViewOf I.toInterp)
  (valid : Bytes → Bool) (E : Bytes → Bytes → alloc.vec.Vec U8 × Std.Array U8 32#usize)
  (S : Std.Array U8 32#usize → Slice U8 → Slice U8 → Std.Array U8 64#usize),
  Tacenta.UnitSatisfiabilityJoint.DhCodecShape I.toInterp →
    Function.Injective dh.privateKey →
      Tacenta.UnitOracleShape.DhPublicClause I.toInterp dh (Tacenta.UnitOracleShape.oracleOfLaws I dh kem valid E S)
-/
#guard_msgs in
#check @Tacenta.UnitOracleShape.dhPublicClause_of_laws

/--
info: 'Tacenta.UnitOracleShape.dhAgreeClause_of_laws' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitOracleShape.dhAgreeClause_of_laws

/--
info: Tacenta.UnitOracleShape.dhAgreeClause_of_laws : ∀ (I : Tacenta.UnitOracleShape.InterpO)
  (dh : Tacenta.UnitOracleShape.DhViewOf I.toInterp) (kem : Tacenta.UnitOracleShape.KemViewOf I.toInterp)
  (valid : Bytes → Bool) (E : Bytes → Bytes → alloc.vec.Vec U8 × Std.Array U8 32#usize)
  (S : Std.Array U8 32#usize → Slice U8 → Slice U8 → Std.Array U8 64#usize),
  Tacenta.UnitSatisfiabilityJoint.DhAgreeShape I.toInterp →
    Tacenta.UnitOracleShape.DhViewInjective dh →
      Tacenta.UnitOracleShape.DhAgreeClause I.toInterp dh (Tacenta.UnitOracleShape.oracleOfLaws I dh kem valid E S)
-/
#guard_msgs in
#check @Tacenta.UnitOracleShape.dhAgreeClause_of_laws

/--
info: 'Tacenta.UnitOracleShape.identityValidClause_of_laws' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitOracleShape.identityValidClause_of_laws

/--
info: Tacenta.UnitOracleShape.identityValidClause_of_laws : ∀ (I : Tacenta.UnitOracleShape.InterpO)
  (dh : Tacenta.UnitOracleShape.DhViewOf I.toInterp) (kem : Tacenta.UnitOracleShape.KemViewOf I.toInterp)
  (valid : Bytes → Bool) (E : Bytes → Bytes → alloc.vec.Vec U8 × Std.Array U8 32#usize)
  (S : Std.Array U8 32#usize → Slice U8 → Slice U8 → Std.Array U8 64#usize),
  Tacenta.UnitSatisfiabilityJoint.DhCodecShape I.toInterp →
    Tacenta.UnitSatisfiabilityJoint.DhIdentityShape I.toInterp →
      Function.Injective dh.publicKey →
        Tacenta.UnitOracleShape.IdentityValidClause I.toInterp dh
          (Tacenta.UnitOracleShape.oracleOfLaws I dh kem valid E S)
-/
#guard_msgs in
#check @Tacenta.UnitOracleShape.identityValidClause_of_laws

/--
info: 'Tacenta.UnitOracleShape.aeadSealClause_of_laws' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitOracleShape.aeadSealClause_of_laws

/--
info: Tacenta.UnitOracleShape.aeadSealClause_of_laws : ∀ (I : Tacenta.UnitOracleShape.InterpO)
  (dh : Tacenta.UnitOracleShape.DhViewOf I.toInterp) (kem : Tacenta.UnitOracleShape.KemViewOf I.toInterp)
  (valid : Bytes → Bool) (E : Bytes → Bytes → alloc.vec.Vec U8 × Std.Array U8 32#usize)
  (S : Std.Array U8 32#usize → Slice U8 → Slice U8 → Std.Array U8 64#usize),
  Tacenta.UnitSatisfiabilityJoint.AeadSealBoundedShape I.toInterp →
    Tacenta.UnitOracleShape.AeadSealClause I.toInterp (Tacenta.UnitOracleShape.oracleOfLaws I dh kem valid E S)
-/
#guard_msgs in
#check @Tacenta.UnitOracleShape.aeadSealClause_of_laws

/--
info: 'Tacenta.UnitOracleShape.aeadOpenClause_of_laws' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitOracleShape.aeadOpenClause_of_laws

/--
info: Tacenta.UnitOracleShape.aeadOpenClause_of_laws : ∀ (I : Tacenta.UnitOracleShape.InterpO)
  (dh : Tacenta.UnitOracleShape.DhViewOf I.toInterp) (kem : Tacenta.UnitOracleShape.KemViewOf I.toInterp)
  (valid : Bytes → Bool) (E : Bytes → Bytes → alloc.vec.Vec U8 × Std.Array U8 32#usize)
  (S : Std.Array U8 32#usize → Slice U8 → Slice U8 → Std.Array U8 64#usize),
  Tacenta.UnitSatisfiabilityJoint.AeadOpenShape I.toInterp →
    Tacenta.UnitOracleShape.AeadOpenClause I.toInterp (Tacenta.UnitOracleShape.oracleOfLaws I dh kem valid E S)
-/
#guard_msgs in
#check @Tacenta.UnitOracleShape.aeadOpenClause_of_laws

/--
info: 'Tacenta.UnitOracleShape.kemDecapsulateClause_of_laws' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitOracleShape.kemDecapsulateClause_of_laws

/--
info: Tacenta.UnitOracleShape.kemDecapsulateClause_of_laws : ∀ (I : Tacenta.UnitOracleShape.InterpO)
  (dh : Tacenta.UnitOracleShape.DhViewOf I.toInterp) (kem : Tacenta.UnitOracleShape.KemViewOf I.toInterp)
  (valid : Bytes → Bool) (E : Bytes → Bytes → alloc.vec.Vec U8 × Std.Array U8 32#usize)
  (S : Std.Array U8 32#usize → Slice U8 → Slice U8 → Std.Array U8 64#usize),
  Tacenta.UnitSatisfiabilityJoint.KemDecapsulateShape I.toInterp →
    Tacenta.UnitOracleShape.KemViewInjective kem →
      Tacenta.UnitOracleShape.KemDecapsulateClause I.toInterp kem
        (Tacenta.UnitOracleShape.oracleOfLaws I dh kem valid E S)
-/
#guard_msgs in
#check @Tacenta.UnitOracleShape.kemDecapsulateClause_of_laws

/--
info: 'Tacenta.UnitOracleShape.sigVerifyClause_of_laws' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitOracleShape.sigVerifyClause_of_laws

/--
info: Tacenta.UnitOracleShape.sigVerifyClause_of_laws : ∀ (I : Tacenta.UnitOracleShape.InterpO)
  (dh : Tacenta.UnitOracleShape.DhViewOf I.toInterp) (kem : Tacenta.UnitOracleShape.KemViewOf I.toInterp)
  (valid : Bytes → Bool) (E : Bytes → Bytes → alloc.vec.Vec U8 × Std.Array U8 32#usize)
  (S : Std.Array U8 32#usize → Slice U8 → Slice U8 → Std.Array U8 64#usize),
  Tacenta.UnitSatisfiabilityJoint.XeddsaVerifyShape I.toInterp →
    Function.Injective dh.publicKey →
      Tacenta.UnitOracleShape.SigVerifyClause I.toInterp dh (Tacenta.UnitOracleShape.oracleOfLaws I dh kem valid E S)
-/
#guard_msgs in
#check @Tacenta.UnitOracleShape.sigVerifyClause_of_laws

/--
info: def Tacenta.UnitOracleShape.DhViewInjective : {I : Tacenta.UnitSatisfiabilityJoint.Interp} →
  Tacenta.UnitOracleShape.DhViewOf I → Prop :=
fun {I} dh => Function.Injective dh.privateKey ∧ Function.Injective dh.publicKey
-/
#guard_msgs in
#print Tacenta.UnitOracleShape.DhViewInjective

/--
info: def Tacenta.UnitOracleShape.KemViewInjective : {I : Tacenta.UnitSatisfiabilityJoint.Interp} →
  Tacenta.UnitOracleShape.KemViewOf I → Prop :=
fun {I} kem => Function.Injective kem.keyPair
-/
#guard_msgs in
#print Tacenta.UnitOracleShape.KemViewInjective

/--
info: def Tacenta.UnitOracleShape.GenerateFillsOnce64Shape : Tacenta.UnitSatisfiabilityJoint.Interp → Prop :=
fun I =>
  ∃ G,
    ∀ {R : Type} (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R) (rng : R),
      I.ikpGenerate rc crc rng = do
        let (rng', seed) ← rc.fill_bytes rng Tacenta.UnitLifecycleIntegrationScreen.zeros64
        ok (G seed, rng')
-/
#guard_msgs in
#print Tacenta.UnitOracleShape.GenerateFillsOnce64Shape

/--
info: def Tacenta.UnitOracleShape.oracleOfLaws : (I : Tacenta.UnitOracleShape.InterpO) →
  Tacenta.UnitOracleShape.DhViewOf I.toInterp →
    Tacenta.UnitOracleShape.KemViewOf I.toInterp →
      (Bytes → Bool) →
        (Bytes → Bytes → alloc.vec.Vec U8 × Std.Array U8 32#usize) →
          (Std.Array U8 32#usize → Slice U8 → Slice U8 → Std.Array U8 64#usize) → Model.Lifecycle.Oracle :=
fun I dh kem valid E S =>
  have __src := Model.Lifecycle.Examples.toyOracle [];
  { draws := __src.draws, braidKem := __src.braidKem,
    dhPublic := Tacenta.UnitOracleShape.liftView dh.privateKey I.dhPrivPublicKey dh.publicKey [],
    dhAgree := fun s p =>
      Tacenta.UnitOracleShape.liftView (Prod.map dh.privateKey dh.publicKey) (fun x => I.dhPrivAgree x.1 x.2)
        (Option.map arrayOf) none (s, p),
    identityValid :=
      Tacenta.UnitOracleShape.liftView dh.publicKey (Tacenta.UnitOracleShape.isValidIdentityKeyOf I.toInterp) id false,
    aeadSeal := fun k1 k2 iv b4 b5 =>
      Tacenta.UnitOracleShape.liftView
        (Prod.map arrayOf (Prod.map arrayOf (Prod.map arrayOf (Prod.map sliceOf sliceOf))))
        (fun x => I.aeadEncrypt x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2) vecOf [] (k1, k2, iv, b4, b5),
    aeadOpen := fun k1 k2 iv b4 b5 =>
      Tacenta.UnitOracleShape.liftView
        (Prod.map arrayOf (Prod.map arrayOf (Prod.map arrayOf (Prod.map sliceOf sliceOf))))
        (fun x => I.aeadDecrypt x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2) (resultOptionOf vecOf) none (k1, k2, iv, b4, b5),
    kemValid := valid, kemEncaps := Tacenta.UnitLifecycleIntegrationScreen.kemEncapsOf valid E,
    kemDecaps := fun k c =>
      Tacenta.UnitOracleShape.liftView (Prod.map kem.keyPair sliceOf) (fun x => I.kemDecapsulate x.1 x.2)
        (resultOptionOf arrayOf) none (k, c),
    sigVerify := fun p m s =>
      Tacenta.UnitOracleShape.liftView (Prod.map dh.publicKey (Prod.map sliceOf arrayOf))
        (fun x => I.xeddsaVerify x.1 x.2.1 x.2.2) verified false (p, m, s),
    sigSign := Tacenta.UnitLifecycleIntegrationScreen.sigSignOf S }
-/
#guard_msgs in
#print Tacenta.UnitOracleShape.oracleOfLaws

/--
info: def Tacenta.UnitOracleShape.DhPublicClause : (I : Tacenta.UnitSatisfiabilityJoint.Interp) →
  Tacenta.UnitOracleShape.DhViewOf I → Model.Lifecycle.Oracle → Prop :=
fun I dh oracle =>
  ∀ (secret : I.PrivateKey),
    ∃ publicKey,
      I.dhPrivPublicKey secret = ok publicKey ∧ dh.publicKey publicKey = oracle.dhPublic (dh.privateKey secret)
-/
#guard_msgs in
#print Tacenta.UnitOracleShape.DhPublicClause

/--
info: def Tacenta.UnitOracleShape.DhAgreeClause : (I : Tacenta.UnitSatisfiabilityJoint.Interp) →
  Tacenta.UnitOracleShape.DhViewOf I → Model.Lifecycle.Oracle → Prop :=
fun I dh oracle =>
  ∀ (secret : I.PrivateKey) (publicKey : I.PublicKeyBytes),
    ∃ result,
      I.dhPrivAgree secret publicKey = ok result ∧
        Option.map arrayOf result = oracle.dhAgree (dh.privateKey secret) (dh.publicKey publicKey)
-/
#guard_msgs in
#print Tacenta.UnitOracleShape.DhAgreeClause

/--
info: def Tacenta.UnitOracleShape.IdentityValidClause : (I : Tacenta.UnitSatisfiabilityJoint.Interp) →
  Tacenta.UnitOracleShape.DhViewOf I → Model.Lifecycle.Oracle → Prop :=
fun I dh oracle =>
  ∀ (publicKey : I.PublicKeyBytes),
    ∃ result,
      Tacenta.UnitOracleShape.isValidIdentityKeyOf I publicKey = ok result ∧
        result = oracle.identityValid (dh.publicKey publicKey)
-/
#guard_msgs in
#print Tacenta.UnitOracleShape.IdentityValidClause

/--
info: def Tacenta.UnitOracleShape.AeadSealClause : Tacenta.UnitSatisfiabilityJoint.Interp → Model.Lifecycle.Oracle → Prop :=
fun I oracle =>
  ∀ (key1 key2 : Std.Array U8 32#usize) (iv : Std.Array U8 16#usize) (ad plaintext : Slice U8),
    ∃ ciphertext,
      I.aeadEncrypt key1 key2 iv ad plaintext = ok ciphertext ∧
        vecOf ciphertext = oracle.aeadSeal (arrayOf key1) (arrayOf key2) (arrayOf iv) (sliceOf ad) (sliceOf plaintext)
-/
#guard_msgs in
#print Tacenta.UnitOracleShape.AeadSealClause

/--
info: def Tacenta.UnitOracleShape.AeadOpenClause : Tacenta.UnitSatisfiabilityJoint.Interp → Model.Lifecycle.Oracle → Prop :=
fun I oracle =>
  ∀ (key1 key2 : Std.Array U8 32#usize) (iv : Std.Array U8 16#usize) (ciphertext associatedData : Slice U8),
    ∃ result,
      I.aeadDecrypt key1 key2 iv ciphertext associatedData = ok result ∧
        resultOptionOf vecOf result =
          oracle.aeadOpen (arrayOf key1) (arrayOf key2) (arrayOf iv) (sliceOf ciphertext) (sliceOf associatedData)
-/
#guard_msgs in
#print Tacenta.UnitOracleShape.AeadOpenClause

/--
info: def Tacenta.UnitOracleShape.KemDecapsulateClause : (I : Tacenta.UnitSatisfiabilityJoint.Interp) →
  Tacenta.UnitOracleShape.KemViewOf I → Model.Lifecycle.Oracle → Prop :=
fun I kem oracle =>
  ∀ (keyPair : I.KemKeyPair) (ciphertext : Slice U8),
    ∃ result,
      I.kemDecapsulate keyPair ciphertext = ok result ∧
        resultOptionOf arrayOf result = oracle.kemDecaps (kem.keyPair keyPair) (sliceOf ciphertext)
-/
#guard_msgs in
#print Tacenta.UnitOracleShape.KemDecapsulateClause

/--
info: def Tacenta.UnitOracleShape.SigVerifyClause : (I : Tacenta.UnitSatisfiabilityJoint.Interp) →
  Tacenta.UnitOracleShape.DhViewOf I → Model.Lifecycle.Oracle → Prop :=
fun I dh oracle =>
  ∀ (publicKey : I.PublicKeyBytes) (message : Slice U8) (signature : Std.Array U8 64#usize),
    ∃ result,
      I.xeddsaVerify publicKey message signature = ok result ∧
        verified result = oracle.sigVerify (dh.publicKey publicKey) (sliceOf message) (arrayOf signature)
-/
#guard_msgs in
#print Tacenta.UnitOracleShape.SigVerifyClause
