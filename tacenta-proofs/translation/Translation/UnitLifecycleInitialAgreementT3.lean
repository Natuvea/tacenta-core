import Translation.SessionUnitDecodeEc
import Translation.UnitLifecycleDecryptRatchetT3
import Translation.UnitLifecycleIntegrationScreen

/-!
# The repeated-initial ephemeral comparison refines the model's

`Session::decrypt` recognises a repeated initial message by comparing the message's `ephemeral`
with the session's `established_ephemeral` (`same_ephemeral_agreement`,
`tacenta-core/lifecycle/src/lifecycle.rs`; the Session unit's copy in
`session-unit/src/lifecycle.rs`): it decodes both with `decode_ec`, agrees the session's
`ratchet_private` with each decoded key, and compares the two outputs, `false` when either decode
or either agreement fails. `Model.Lifecycle.sameEphemeralAgreement` states the same rule from
session-establishment.md, Receiving the initial message, through the model's `DecodeEC`,
`Model.Lifecycle.decodeEc`.

* `same_ephemeral_agreement_refines_of_dhAgree`: on every private key and every two byte strings,
  the translated comparison returns exactly the model's verdict, given the agreement clause of the
  oracle and `DhCodecOf`.
* `same_ephemeral_agreement_refines`: the same under `DecryptOracleOf`, of which it reads only the
  `dhAgree` clause.
* `repeated_initial_agreement_refines`: the same at a related session and a decoded initial
  message, the shape the dispatch of `Session::decrypt` uses.
* `repeated_initial_agreement_true_iff`, `repeated_initial_agreement_false_iff`: the code's
  verdict is `true` (`false`) exactly when the model's is.
* `encoded_comparison_does_not_refine`, a control: the comparison the model made before its
  correction, on the two 33-byte encodings, disagrees with the code at some oracle that meets
  `OracleOf`, so no refinement of this shape holds of it.

## The hypotheses

Two, both about opaque operations and both assumed (`LIMITATIONS.md`): the agreement clause of the
oracle, `DecryptOracleOf.dhAgree` (`OracleOf.dhAgree` word for word), which ties
`PrivateKey::agree` to `oracle.dhAgree` at the byte views, and `DhCodecOf`, the byte views of the
two opaque key types. Nothing about a branch, a route or the model's verdict is a hypothesis.

## What it supersedes

The per-branch premises `hmodelSame` (the model's verdict is `true`) and `hagreementMismatch` (the
model's verdict is `false`) of `InitialDispatchBranchEvidence`, `SessionDecryptEvidence` and the
initial-frame branch lemmas of `UnitLifecycleT3.lean` asked the caller for the model's verdict on
the branch the run takes. `repeated_initial_agreement_true_iff` and
`repeated_initial_agreement_false_iff` derive each from the code's verdict under the two
hypotheses above. Those records and lemmas are kept, and no theorem in this module takes them.
`hagreementMismatch` was an inequality of `oracle.dhAgree` at the two 33-byte strings until the
model's comparison decoded them; it now states the model's verdict, `false`, as `hmodelSame` states
`true`.

## What it does not cover

It is the comparison alone. The composition of `Session::decrypt` on an initial frame, which would
case-split on this verdict instead of on byte equality, is not here.
-/

namespace Tacenta.UnitLifecycleInitialAgreementT3

open Aeneas Aeneas.Std Result
open tacenta_session_unit
open Tacenta.UnitLifecycleT3
open Tacenta.UnitLifecycleDecryptRatchetT3

theorem arrayOf_injective {n : Usize} {left right : Array Std.U8 n}
    (h : arrayOf left = arrayOf right) : left = right := by
  apply Subtype.ext
  exact List.map_injective_iff.mpr (fun _ _ => Tacenta.SessionUnitBraidT3.u8_injective) h

/-- The translated comparison of two agreement outputs is the model's `==` on their bytes. -/
theorem agreement_eq_refines (left right : Array Std.U8 32#usize) :
    core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8 left right =
      ok (arrayOf left == arrayOf right) := by
  obtain ⟨v, hv, hiff⟩ := Std.WP.spec_imp_exists (Tacenta.SessionUnitT3.array_eq_val left right)
  rw [hv]
  congr 1
  cases v with
  | true =>
      have h := hiff.1 rfl
      subst h
      simp
  | false =>
      symm
      rw [beq_eq_false_iff_ne]
      intro h
      exact absurd (hiff.2 (arrayOf_injective h)) (by simp)

/-- **The repeated-initial comparison refines the model's, given the agreement clause.** On every
private key and every two byte strings, the translated `same_ephemeral_agreement` returns, and
returns `Model.Lifecycle.sameEphemeralAgreement` at the private key's view and the two strings'
bytes. -/
theorem same_ephemeral_agreement_refines_of_dhAgree
    {dh : DhView} {oracle : Model.Lifecycle.Oracle}
    (hagree : ∀ secret publicKey,
      ∃ result, tacenta_boundary.dh.PrivateKey.agree secret publicKey = ok result ∧
        result.map arrayOf = oracle.dhAgree (dh.privateKey secret) (dh.publicKey publicKey))
    (codec : DhCodecOf dh) (privateKey : tacenta_boundary.dh.PrivateKey)
    (established incoming : Slice Std.U8) :
    lifecycle.same_ephemeral_agreement privateKey established incoming =
      ok (Model.Lifecycle.sameEphemeralAgreement oracle (dh.privateKey privateKey)
        (sliceOf established) (sliceOf incoming)) := by
  obtain ⟨r1, h1, hr1⟩ := Tacenta.SessionUnitDecodeEc.decode_ec_refines dh codec established
  obtain ⟨r2, h2, hr2⟩ := Tacenta.SessionUnitDecodeEc.decode_ec_refines dh codec incoming
  unfold lifecycle.same_ephemeral_agreement Model.Lifecycle.sameEphemeralAgreement
  rw [h1, ← hr1]
  cases r1 with
  | none => simp
  | some k1 =>
      rw [h2, ← hr2]
      cases r2 with
      | none => simp
      | some k2 =>
          obtain ⟨a1, ha1, hva1⟩ := hagree privateKey k1
          obtain ⟨a2, ha2, hva2⟩ := hagree privateKey k2
          simp only [bind_tc_ok, Option.map_some, ha1, ha2, ← hva1, ← hva2]
          cases a1 with
          | none => simp
          | some left =>
              cases a2 with
              | none => simp
              | some right =>
                  simp only [Option.map_some]
                  exact agreement_eq_refines left right

/-- **The repeated-initial comparison refines the model's.** `same_ephemeral_agreement_refines_of_dhAgree`
under `DecryptOracleOf`, the oracle record of `decrypt_ratchet`'s refinement; only its `dhAgree`
clause is read. -/
theorem same_ephemeral_agreement_refines {R : Type}
    {rngCore : rand_core_1.RngCore R} {cryptoRng : rand_core_1.CryptoRng R}
    {dh : DhView} {trace : R → List Model.Lifecycle.Key} {oracle : Model.Lifecycle.Oracle}
    (oracleOf : DecryptOracleOf rngCore cryptoRng dh trace oracle) (codec : DhCodecOf dh)
    (privateKey : tacenta_boundary.dh.PrivateKey) (established incoming : Slice Std.U8) :
    lifecycle.same_ephemeral_agreement privateKey established incoming =
      ok (Model.Lifecycle.sameEphemeralAgreement oracle (dh.privateKey privateKey)
        (sliceOf established) (sliceOf incoming)) :=
  same_ephemeral_agreement_refines_of_dhAgree oracleOf.dhAgree codec privateKey established incoming

/-- **At a related session and a decoded initial message.** The comparison `Session::decrypt` makes
between the session's `established_ephemeral` and the decoded message's `ephemeral` returns the
model's verdict at the model session's `ratchetPrivate` and the two byte strings, the arguments
`Model.Lifecycle.repeatedInitial` passes. -/
theorem repeated_initial_agreement_refines {R : Type}
    {rngCore : rand_core_1.RngCore R} {cryptoRng : rand_core_1.CryptoRng R}
    {dh : DhView} {trace : R → List Model.Lifecycle.Key} {oracle : Model.Lifecycle.Oracle}
    {K : Model.Braid.Kem} {real : lifecycle.Session} {model : Model.Lifecycle.Session}
    (oracleOf : DecryptOracleOf rngCore cryptoRng dh trace oracle) (codec : DhCodecOf dh)
    (hrel : SessionRefines dh K real model)
    (established : alloc.vec.Vec Std.U8) (decoded : tacenta_wire.DecodedInitial) :
    lifecycle.same_ephemeral_agreement real.ratchet_private
        established.deref decoded.ephemeral.deref =
      ok (Model.Lifecycle.sameEphemeralAgreement oracle model.ratchetPrivate
        (vecOf established) (Tacenta.SessionUnitWireT3.bytesOf decoded.ephemeral.val)) := by
  rw [same_ephemeral_agreement_refines oracleOf codec, hrel.ratchetPrivate]
  rfl

/-- The code's verdict is `true` exactly when the model's is: what `hmodelSame` asked for. -/
theorem repeated_initial_agreement_true_iff {R : Type}
    {rngCore : rand_core_1.RngCore R} {cryptoRng : rand_core_1.CryptoRng R}
    {dh : DhView} {trace : R → List Model.Lifecycle.Key} {oracle : Model.Lifecycle.Oracle}
    {K : Model.Braid.Kem} {real : lifecycle.Session} {model : Model.Lifecycle.Session}
    (oracleOf : DecryptOracleOf rngCore cryptoRng dh trace oracle) (codec : DhCodecOf dh)
    (hrel : SessionRefines dh K real model)
    (established : alloc.vec.Vec Std.U8) (decoded : tacenta_wire.DecodedInitial) :
    lifecycle.same_ephemeral_agreement real.ratchet_private
        established.deref decoded.ephemeral.deref = ok true ↔
      Model.Lifecycle.sameEphemeralAgreement oracle model.ratchetPrivate
        (vecOf established) (Tacenta.SessionUnitWireT3.bytesOf decoded.ephemeral.val) = true := by
  rw [repeated_initial_agreement_refines oracleOf codec hrel]
  exact ⟨fun h => Result.ok.inj h, fun h => by rw [h]⟩

/-- The code's verdict is `false` exactly when the model's is: what `hagreementMismatch` asked
for. -/
theorem repeated_initial_agreement_false_iff {R : Type}
    {rngCore : rand_core_1.RngCore R} {cryptoRng : rand_core_1.CryptoRng R}
    {dh : DhView} {trace : R → List Model.Lifecycle.Key} {oracle : Model.Lifecycle.Oracle}
    {K : Model.Braid.Kem} {real : lifecycle.Session} {model : Model.Lifecycle.Session}
    (oracleOf : DecryptOracleOf rngCore cryptoRng dh trace oracle) (codec : DhCodecOf dh)
    (hrel : SessionRefines dh K real model)
    (established : alloc.vec.Vec Std.U8) (decoded : tacenta_wire.DecodedInitial) :
    lifecycle.same_ephemeral_agreement real.ratchet_private
        established.deref decoded.ephemeral.deref = ok false ↔
      Model.Lifecycle.sameEphemeralAgreement oracle model.ratchetPrivate
        (vecOf established) (Tacenta.SessionUnitWireT3.bytesOf decoded.ephemeral.val) = false := by
  rw [repeated_initial_agreement_refines oracleOf codec hrel]
  exact ⟨fun h => Result.ok.inj h, fun h => by rw [h]⟩

/-- **The comparison the model made before its correction does not refine the code.** Given an
oracle that meets `OracleOf` and the DH codec, and two byte strings neither of which is 32 bytes long
(every `EncodeEC` string is 33), some oracle that also meets `OracleOf` makes the encoded comparison,
`UnitLifecycleIntegrationScreen.encodedEphemeralAgreement`, disagree with the translated one. So no
theorem of the shape of `same_ephemeral_agreement_refines` holds of it: a model that compared the
encodings again would not refine the code. It says nothing about whether an oracle meeting `OracleOf`
exists; it is a control, not a claim. -/
theorem encoded_comparison_does_not_refine {R : Type}
    {rc : rand_core_1.RngCore R} {crc : rand_core_1.CryptoRng R}
    {trace : R → List Model.Lifecycle.Key} {dh : DhView} {kem : KemView}
    {oracle : Model.Lifecycle.Oracle}
    (codec : DhCodecOf dh) (oracleOf : OracleOf rc crc dh kem trace oracle)
    (privateKey : tacenta_boundary.dh.PrivateKey) (established incoming : Slice Std.U8)
    (hestablished : (sliceOf established).length ≠ 32)
    (hincoming : (sliceOf incoming).length ≠ 32) :
    ∃ oracle', OracleOf rc crc dh kem trace oracle' ∧
      lifecycle.same_ephemeral_agreement privateKey established incoming ≠
        ok (Tacenta.UnitLifecycleIntegrationScreen.encodedEphemeralAgreement oracle'
          (dh.privateKey privateKey) (sliceOf established) (sliceOf incoming)) := by
  have hcode := same_ephemeral_agreement_refines (DecryptOracleOf.of_oracleOf oracleOf) codec
    privateKey established incoming
  obtain ⟨oracle', hof, _, hb⟩ :=
    Tacenta.UnitLifecycleIntegrationScreen.encodedEphemeralAgreement_unconstrained codec oracleOf
      (dh.privateKey privateKey) (sliceOf established) (sliceOf incoming) hestablished hincoming
      (!(Model.Lifecycle.sameEphemeralAgreement oracle (dh.privateKey privateKey)
        (sliceOf established) (sliceOf incoming)))
  refine ⟨oracle', hof, ?_⟩
  rw [hcode, hb]
  intro h
  have hv := Result.ok.inj h
  cases hc : Model.Lifecycle.sameEphemeralAgreement oracle (dh.privateKey privateKey)
      (sliceOf established) (sliceOf incoming) <;> simp [hc] at hv

end Tacenta.UnitLifecycleInitialAgreementT3

/-! ## Pins

The axiom list and the statement of each result, and the body of the model's comparison, held by
the build. `attest.py` requires them (`REQUIRED_PINS`, `REQUIRED_STATEMENT_PINS`,
`REQUIRED_PRINT_FORM`). The body pin means a model that compared the encodings again, without the
decode, fails the build here before any statement does. No result here lists a compiler-trust
axiom. -/

/--
info: def Model.Lifecycle.sameEphemeralAgreement : Model.Lifecycle.Oracle →
  Model.Lifecycle.Key → Model.Lifecycle.Key → Model.Lifecycle.Key → Bool :=
fun oracle secret established incoming =>
  match Model.Lifecycle.decodeEc established, Model.Lifecycle.decodeEc incoming with
  | some establishedKey, some incomingKey =>
    match oracle.dhAgree secret establishedKey, oracle.dhAgree secret incomingKey with
    | some left, some right => left == right
    | x, x_1 => false
  | x, x_1 => false
-/
#guard_msgs in
#print Model.Lifecycle.sameEphemeralAgreement

/--
info: 'Tacenta.UnitLifecycleInitialAgreementT3.arrayOf_injective' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleInitialAgreementT3.arrayOf_injective

/--
info: @Tacenta.UnitLifecycleInitialAgreementT3.arrayOf_injective : ∀ {n : Aeneas.Std.Usize}
  {left right : Aeneas.Std.Array Aeneas.Std.U8 n},
  Tacenta.UnitLifecycleT3.arrayOf left = Tacenta.UnitLifecycleT3.arrayOf right → left = right
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleInitialAgreementT3.arrayOf_injective

/--
info: 'Tacenta.UnitLifecycleInitialAgreementT3.agreement_eq_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleInitialAgreementT3.agreement_eq_refines

/--
info: Tacenta.UnitLifecycleInitialAgreementT3.agreement_eq_refines : ∀ (left right : Aeneas.Std.Array Aeneas.Std.U8 32#usize),
  Aeneas.Std.core.array.equality.PartialEqArray.eq Aeneas.Std.core.cmp.PartialEqU8 left right =
    Aeneas.Std.Result.ok (Tacenta.UnitLifecycleT3.arrayOf left == Tacenta.UnitLifecycleT3.arrayOf right)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleInitialAgreementT3.agreement_eq_refines

/--
info: 'Tacenta.UnitLifecycleInitialAgreementT3.same_ephemeral_agreement_refines_of_dhAgree' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.agree,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.from_bytes]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleInitialAgreementT3.same_ephemeral_agreement_refines_of_dhAgree

/--
info: @Tacenta.UnitLifecycleInitialAgreementT3.same_ephemeral_agreement_refines_of_dhAgree : ∀
  {dh : Tacenta.UnitLifecycleT3.DhView} {oracle : Model.Lifecycle.Oracle},
  (∀ (secret : tacenta_session_unit.tacenta_boundary.dh.PrivateKey)
      (publicKey : tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes),
      ∃ result,
        secret.agree publicKey = Aeneas.Std.Result.ok result ∧
          Option.map Tacenta.UnitLifecycleT3.arrayOf result =
            oracle.dhAgree (dh.privateKey secret) (dh.publicKey publicKey)) →
    Tacenta.UnitLifecycleT3.DhCodecOf dh →
      ∀ (privateKey : tacenta_session_unit.tacenta_boundary.dh.PrivateKey)
        (established incoming : Aeneas.Std.Slice Aeneas.Std.U8),
        tacenta_session_unit.lifecycle.same_ephemeral_agreement privateKey established incoming =
          Aeneas.Std.Result.ok
            (Model.Lifecycle.sameEphemeralAgreement oracle (dh.privateKey privateKey)
              (Tacenta.UnitLifecycleT3.sliceOf established) (Tacenta.UnitLifecycleT3.sliceOf incoming))
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleInitialAgreementT3.same_ephemeral_agreement_refines_of_dhAgree

/--
info: 'Tacenta.UnitLifecycleInitialAgreementT3.same_ephemeral_agreement_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.rand_core_1.error.Error,
 tacenta_session_unit.tacenta_boundary.aead.decrypt,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.agree,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.from_bytes]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleInitialAgreementT3.same_ephemeral_agreement_refines

/--
info: @Tacenta.UnitLifecycleInitialAgreementT3.same_ephemeral_agreement_refines : ∀ {R : Type}
  {rngCore : tacenta_session_unit.rand_core_1.RngCore R} {cryptoRng : tacenta_session_unit.rand_core_1.CryptoRng R}
  {dh : Tacenta.UnitLifecycleT3.DhView} {trace : R → List Model.Lifecycle.Key} {oracle : Model.Lifecycle.Oracle},
  Tacenta.UnitLifecycleDecryptRatchetT3.DecryptOracleOf rngCore cryptoRng dh trace oracle →
    Tacenta.UnitLifecycleT3.DhCodecOf dh →
      ∀ (privateKey : tacenta_session_unit.tacenta_boundary.dh.PrivateKey)
        (established incoming : Aeneas.Std.Slice Aeneas.Std.U8),
        tacenta_session_unit.lifecycle.same_ephemeral_agreement privateKey established incoming =
          Aeneas.Std.Result.ok
            (Model.Lifecycle.sameEphemeralAgreement oracle (dh.privateKey privateKey)
              (Tacenta.UnitLifecycleT3.sliceOf established) (Tacenta.UnitLifecycleT3.sliceOf incoming))
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleInitialAgreementT3.same_ephemeral_agreement_refines

/--
info: 'Tacenta.UnitLifecycleInitialAgreementT3.repeated_initial_agreement_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.tacenta_kem.encapsulate2,
 tacenta_session_unit.rand_core_1.error.Error,
 tacenta_session_unit.tacenta_boundary.aead.decrypt,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.header,
 tacenta_session_unit.alloc.vec.Vec.truncate,
 tacenta_session_unit.core.num.Usize.div_ceil,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.agree,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.from_bytes]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleInitialAgreementT3.repeated_initial_agreement_refines

/--
info: @Tacenta.UnitLifecycleInitialAgreementT3.repeated_initial_agreement_refines : ∀ {R : Type}
  {rngCore : tacenta_session_unit.rand_core_1.RngCore R} {cryptoRng : tacenta_session_unit.rand_core_1.CryptoRng R}
  {dh : Tacenta.UnitLifecycleT3.DhView} {trace : R → List Model.Lifecycle.Key} {oracle : Model.Lifecycle.Oracle}
  {K : Model.Braid.Kem} {real : tacenta_session_unit.lifecycle.Session} {model : Model.Lifecycle.Session},
  Tacenta.UnitLifecycleDecryptRatchetT3.DecryptOracleOf rngCore cryptoRng dh trace oracle →
    Tacenta.UnitLifecycleT3.DhCodecOf dh →
      Tacenta.UnitLifecycleT3.SessionRefines dh K real model →
        ∀ (established : Aeneas.Std.alloc.vec.Vec Aeneas.Std.U8)
          (decoded : tacenta_session_unit.tacenta_wire.DecodedInitial),
          tacenta_session_unit.lifecycle.same_ephemeral_agreement real.ratchet_private established.deref
              decoded.ephemeral.deref =
            Aeneas.Std.Result.ok
              (Model.Lifecycle.sameEphemeralAgreement oracle model.ratchetPrivate
                (Tacenta.UnitLifecycleT3.vecOf established) (Tacenta.SessionUnitWireT3.bytesOf ↑decoded.ephemeral))
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleInitialAgreementT3.repeated_initial_agreement_refines

/--
info: 'Tacenta.UnitLifecycleInitialAgreementT3.repeated_initial_agreement_true_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.tacenta_kem.encapsulate2,
 tacenta_session_unit.rand_core_1.error.Error,
 tacenta_session_unit.tacenta_boundary.aead.decrypt,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.header,
 tacenta_session_unit.alloc.vec.Vec.truncate,
 tacenta_session_unit.core.num.Usize.div_ceil,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.agree,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.from_bytes]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleInitialAgreementT3.repeated_initial_agreement_true_iff

/--
info: @Tacenta.UnitLifecycleInitialAgreementT3.repeated_initial_agreement_true_iff : ∀ {R : Type}
  {rngCore : tacenta_session_unit.rand_core_1.RngCore R} {cryptoRng : tacenta_session_unit.rand_core_1.CryptoRng R}
  {dh : Tacenta.UnitLifecycleT3.DhView} {trace : R → List Model.Lifecycle.Key} {oracle : Model.Lifecycle.Oracle}
  {K : Model.Braid.Kem} {real : tacenta_session_unit.lifecycle.Session} {model : Model.Lifecycle.Session},
  Tacenta.UnitLifecycleDecryptRatchetT3.DecryptOracleOf rngCore cryptoRng dh trace oracle →
    Tacenta.UnitLifecycleT3.DhCodecOf dh →
      Tacenta.UnitLifecycleT3.SessionRefines dh K real model →
        ∀ (established : Aeneas.Std.alloc.vec.Vec Aeneas.Std.U8)
          (decoded : tacenta_session_unit.tacenta_wire.DecodedInitial),
          tacenta_session_unit.lifecycle.same_ephemeral_agreement real.ratchet_private established.deref
                decoded.ephemeral.deref =
              Aeneas.Std.Result.ok true ↔
            Model.Lifecycle.sameEphemeralAgreement oracle model.ratchetPrivate
                (Tacenta.UnitLifecycleT3.vecOf established) (Tacenta.SessionUnitWireT3.bytesOf ↑decoded.ephemeral) =
              true
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleInitialAgreementT3.repeated_initial_agreement_true_iff

/--
info: 'Tacenta.UnitLifecycleInitialAgreementT3.repeated_initial_agreement_false_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.tacenta_kem.encapsulate2,
 tacenta_session_unit.rand_core_1.error.Error,
 tacenta_session_unit.tacenta_boundary.aead.decrypt,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.header,
 tacenta_session_unit.alloc.vec.Vec.truncate,
 tacenta_session_unit.core.num.Usize.div_ceil,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.agree,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.from_bytes]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleInitialAgreementT3.repeated_initial_agreement_false_iff

/--
info: @Tacenta.UnitLifecycleInitialAgreementT3.repeated_initial_agreement_false_iff : ∀ {R : Type}
  {rngCore : tacenta_session_unit.rand_core_1.RngCore R} {cryptoRng : tacenta_session_unit.rand_core_1.CryptoRng R}
  {dh : Tacenta.UnitLifecycleT3.DhView} {trace : R → List Model.Lifecycle.Key} {oracle : Model.Lifecycle.Oracle}
  {K : Model.Braid.Kem} {real : tacenta_session_unit.lifecycle.Session} {model : Model.Lifecycle.Session},
  Tacenta.UnitLifecycleDecryptRatchetT3.DecryptOracleOf rngCore cryptoRng dh trace oracle →
    Tacenta.UnitLifecycleT3.DhCodecOf dh →
      Tacenta.UnitLifecycleT3.SessionRefines dh K real model →
        ∀ (established : Aeneas.Std.alloc.vec.Vec Aeneas.Std.U8)
          (decoded : tacenta_session_unit.tacenta_wire.DecodedInitial),
          tacenta_session_unit.lifecycle.same_ephemeral_agreement real.ratchet_private established.deref
                decoded.ephemeral.deref =
              Aeneas.Std.Result.ok false ↔
            Model.Lifecycle.sameEphemeralAgreement oracle model.ratchetPrivate
                (Tacenta.UnitLifecycleT3.vecOf established) (Tacenta.SessionUnitWireT3.bytesOf ↑decoded.ephemeral) =
              false
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleInitialAgreementT3.repeated_initial_agreement_false_iff

/--
info: 'Tacenta.UnitLifecycleInitialAgreementT3.encoded_comparison_does_not_refine' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.rand_core_1.error.Error,
 tacenta_session_unit.tacenta_boundary.aead.decrypt,
 tacenta_session_unit.tacenta_boundary.aead.encrypt,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.dh.is_prime_order_public,
 tacenta_session_unit.tacenta_boundary.kem.KeyPair,
 tacenta_session_unit.tacenta_boundary.kem.decapsulate,
 tacenta_session_unit.tacenta_boundary.kem.encapsulate,
 tacenta_session_unit.tacenta_boundary.xeddsa.sign,
 tacenta_session_unit.tacenta_boundary.xeddsa.verify,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.agree,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.from_bytes]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleInitialAgreementT3.encoded_comparison_does_not_refine

/--
info: @Tacenta.UnitLifecycleInitialAgreementT3.encoded_comparison_does_not_refine : ∀ {R : Type}
  {rc : tacenta_session_unit.rand_core_1.RngCore R} {crc : tacenta_session_unit.rand_core_1.CryptoRng R}
  {trace : R → List Model.Lifecycle.Key} {dh : Tacenta.UnitLifecycleT3.DhView} {kem : Tacenta.UnitLifecycleT3.KemView}
  {oracle : Model.Lifecycle.Oracle},
  Tacenta.UnitLifecycleT3.DhCodecOf dh →
    Tacenta.UnitLifecycleT3.OracleOf rc crc dh kem trace oracle →
      ∀ (privateKey : tacenta_session_unit.tacenta_boundary.dh.PrivateKey)
        (established incoming : Aeneas.Std.Slice Aeneas.Std.U8),
        List.length (Tacenta.UnitLifecycleT3.sliceOf established) ≠ 32 →
          List.length (Tacenta.UnitLifecycleT3.sliceOf incoming) ≠ 32 →
            ∃ oracle',
              Tacenta.UnitLifecycleT3.OracleOf rc crc dh kem trace oracle' ∧
                tacenta_session_unit.lifecycle.same_ephemeral_agreement privateKey established incoming ≠
                  Aeneas.Std.Result.ok
                    (Tacenta.UnitLifecycleIntegrationScreen.encodedEphemeralAgreement oracle' (dh.privateKey privateKey)
                      (Tacenta.UnitLifecycleT3.sliceOf established) (Tacenta.UnitLifecycleT3.sliceOf incoming))
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleInitialAgreementT3.encoded_comparison_does_not_refine
