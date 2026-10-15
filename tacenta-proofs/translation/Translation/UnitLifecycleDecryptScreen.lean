import Translation.UnitOracleDecrypt
import Translation.UnitLifecycleDecryptRatchetCompleteT3
import Translation.UnitLifecycleDecryptRatchetScreen
import Translation.UnitHeadroomInvariant

/-!
# The hypotheses of the decrypt refinement hold together at the real constants

`UnitLifecycleDecryptRatchetCompleteT3.decrypt_ratchet_refines_complete` takes `DecryptOracleOf`,
`DhCodecOf`, `DecryptRatchetContracts`, the class `DerivedKeysModel`, `DecryptRatchetAgreements` at the
oracle's Braid KEM model, `SessionRefines`, `DecryptRatchetHeadroom`, the trace equation and
`DecryptRatchetRun`.  Earlier modules show parts of that set satisfiable in different places: the
four decrypt clauses with a toy oracle and `toyKem`
(`UnitLifecycleDecryptRatchetScreen.decrypt_boundary_has_a_model`), the oracle clauses from laws with
the code's oracle (`UnitOracleJoint.oracleOf_of_laws`, `UnitOracleDecrypt.decryptOracleOf_of_laws`),
and the per-run records at runs over sessions that fail `Session::invariant`.  This module shows the
whole set, with `Session::invariant` added, at one oracle, one state pair, one message and one
source.

## What is shown

* `DecryptHypotheses`: the theorem's hypotheses at one choice of every binder, with
  `Session::invariant real = ok true` added.  `DecryptHypotheses.refines` applies
  `decrypt_ratchet_refines_complete` to it, so a hypothesis added to that theorem and not here stops
  this module building.
* `decrypt_hypotheses_jointly_satisfiable` (statement `DecryptHypothesesJointlySatisfiableStatement`):
  at the real constants and the byte-stream source (`byteRng`, `byteTrace`), under the laws
  `DecryptJointLaws K dh`, there are an oracle whose Braid KEM model is `K`, a translated session that
  passes `Session::invariant`, a related model session, a message that decodes on both sides and is a
  ratchet frame, and a source, at which every field of `DecryptHypotheses` holds, for every codeword
  view.  The agreements are at that oracle's own `braidKem`.  The oracle is the one
  `decryptOracleOf_of_laws` builds (the code read through its byte views), with its `braidKem` set to
  `K`.  `decrypt_hypotheses_at_invReal` is the same at the explicit witness.
* `decrypt_joint_laws_model`, `decrypt_joint_laws_satisfiable`: one interpretation of the unit's
  opaque constants (`Interp.modelDecrypt`), with its view, the KEM model `toyKem` and the standard
  library's definition of `Option::eq`, satisfies every law of the bundle together.
* `decryptJointLaws_named`: the bundle at the real constants gives, by projection, the four laws of
  `decryptOracleOf_of_laws`, the three zeroize fields stated at the unit's instances, the five laws the
  two sparse agreements are derived from, and `KemAgreesFor K`.

## The laws, and where each is assumed

All are fields of `DecryptJointLawsShape` (the docstring lists them), assumed at the real constants
in `decrypt_hypotheses_jointly_satisfiable`'s hypothesis `L`: the four laws of
`decryptOracleOf_of_laws` (`DhCodecTotal`, `DhAgreeTotal`, `AeadOpenTotal`, the DH view law); `DhCodecOf`;
the axiom-level parts of `DecryptRatchetContracts` (with the three zeroize fields at the unit's
instances); `StdLaws` (with `LawPop` and `LawAsMut`) and `TruncatePrefix`; the class
`DerivedKeysModel` as a shape; the Braid KEM and KDF agreements at `K`; the five `zeroize` round
trips; `ValidKeyShape` and `OptionEqU64Shape`.  None is proved of the shipped functions.

## The sense

The theorem is a theorem in the real environment: under the laws, the hypothesis set holds at the
witness.  The laws have a model (`decrypt_joint_laws_model`), so, as in `UnitSatisfiabilityRecords`,
a derivation of `False` from them at the real constants would become, after the constants are
replaced by the model's terms, a derivation of `False` from facts that hold in the model.  That step
is an argument about derivations and not a theorem inside Lean.

## The Braid KEM model

`decryptOracleOf_of_laws` lets the caller choose the oracle's `braidKem`; this module chooses `K`, the
KEM model at which the agreements are assumed.  The oracle `oracleOfLaws` builds before that choice
carries the `braidKem` of `Model.Lifecycle.Examples.toyOracle`, which is `toyKem`.  The agreements are
not shown at `toyKem` at the real constants, and by reading they fail there: `KemLenAgrees toyKem`
asks the real `CT1_LEN` to be 64, and the crate's is 1408 (`tacenta-core/kem/src/lib.rs`).  So the
choice is what puts the agreements on the same oracle's `braidKem`.  The oracle's other KEM fields
(`kemValid`, `kemEncaps`, `kemDecaps`) are `oracleOfLaws`'s and are not related to `K`; the model's
`decrypt` reads none of them (`Model.Lifecycle.decrypt_oracle_frame`).  Whether some `K` meets the
agreements at the real constants is assumed; in the model it is `toyKem`.

## What the witness is not

* The state is built for the hypotheses: `invReal` is a session over fresh states
  (`UnitHeadroomSatisfiable.sessionOf`) with one key as both identities, no pending initial message,
  no established ephemeral key, no receiving chain and a Braid in `KeysUnsampled`.  It is not shown
  to be produced by `establish_initiator` or `establish_responder`, or by `import`.
* The laws are assumed, not proved of the shipped functions.
* The oracle is the code read through its byte views (`oracleOfLaws` over `InterpO.decrypt`), not a
  specification of X25519 or the AEAD; nothing here is shown of the primitives.
* The run carries no agreement chunk: the composite has `agChunk := none`, so the chunk and honest
  fields of `DecryptRatchetRun` hold by their arm for a message without a chunk.
* Which way the model's step at the witness goes is not fixed by the laws.  The composite's ratchet
  key is 32 zero bytes, so the step refuses at the first agreement with `nonContributoryAgreement`
  when the oracle's agreement refuses that key (`invReal_model_refuses_of_agreement`); at this
  oracle that agreement is the real `agree` on the key `from_bytes` returns for 32 zero bytes
  (`invReal_agreement_is_real`), a value no law states.  By reading the X25519 boundary
  (`tacenta-core/boundary/src/dh.rs`, `agree` returns `None` on a non-contributory result, which the
  all-zero key gives), it refuses; in the model interpretation it refuses too.  The witness does
  not exercise the Triple receive, the AEAD or a success.

## Platform width

No proof here chooses a width of `usize`: the bounds used hold at both (`usize_max_ge`, `cMax_usize`),
and no result depends on a compiler-trust axiom other than `DecryptHypotheses.refines`, which inherits
those of `decrypt_ratchet_refines_complete` (its pin).  So each result holds at both widths; no
hypothesis of the set is width-dependent at this witness.
-/

open Aeneas Aeneas.Std Result
open tacenta_session_unit
open Tacenta.UnitLifecycleT3
open Tacenta.UnitLifecycleDecryptRatchetT3
open Tacenta.UnitSatisfiabilityJoint
open Tacenta.UnitSatisfiabilityBraidAgreements
open Tacenta.UnitLifecycleDecryptRatchetScreen (DhViewShape DhCodecOfShape ZeroizeRoundTripShapes
  decrypt_shapes_are_predicates sampleMessage sampleRng sampleComposite sample_decode_model
  sample_decode_real sliceOf_sampleMessage sample_trace sample_braid_output modelOf
  Interp.modelDecrypt viewDecrypt modelDecrypt_allT1 modelDecrypt_stdLaws
  modelDecrypt_truncatePrefix modelDecrypt_zeroizingModel modelDecrypt_t3 modelDecrypt_codec
  modelDecrypt_zeroize)
open Tacenta.UnitLifecycleIntegrationScreen (byteRng byteCrc byteTrace)
open Tacenta.UnitHeadroomInvariant (ValidKeyShape OptionEqU64Shape optionEqImpl
  optionEqImpl_shape sessionOf_invariant)

namespace Tacenta.UnitLifecycleDecryptScreen

/-! ## The state: a session over fresh states that passes `Session::invariant` -/

/-- The translated session of the witness: `UnitHeadroomSatisfiable.sessionOf` with one key `pkb` as
both identities, the associated data `ad` and the ratchet's own public bytes `a`, no pending initial
message and no established ephemeral key. -/
def invReal (k : tacenta_boundary.dh.PrivateKey) (pkb : tacenta_boundary.dh.PublicKeyBytes)
    (ad : alloc.vec.Vec U8) (a : Array U8 32#usize) : lifecycle.Session :=
  Tacenta.UnitHeadroomSatisfiable.sessionOf k pkb pkb ad a none

theorem invReal_sessionRefines (K : Model.Braid.Kem) (dh : DhView) (k pkb ad a) :
    SessionRefines dh K (invReal k pkb ad a) (modelOf dh (invReal k pkb ad a)) :=
  ⟨⟨rfl, rfl⟩, (Tacenta.UnitSatisfiabilityBraidStates.good_keysUnsampled (K := K)).1,
    rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem invReal_headroom (k pkb a) (ad : alloc.vec.Vec U8) (hlen : ad.val.length = 66) :
    Tacenta.UnitLifecycleT1.DecryptRatchetHeadroom (invReal k pkb ad a) := by
  have h4 := Tacenta.UnitHeadroomSatisfiable.usize_max_ge
  rw [invReal, Tacenta.UnitHeadroomSatisfiable.decryptHeadroom_sessionOf_iff]
  omega

theorem invReal_retryRunBounds (k pkb ad a) (dh : DhView)
    (output : Option Model.SparseRatchet.Output) (houtput : output = none) :
    RetryRunBounds (modelOf dh (invReal k pkb ad a)).triple
      (Model.Lifecycle.tripleHeaderOf sampleComposite) output := by
  subst houtput
  have hu := Tacenta.UnitHeadroomSatisfiable.usize_max_ge
  constructor <;>
    simp [modelOf, invReal, Tacenta.UnitHeadroomSatisfiable.sessionOf,
      Tacenta.UnitHeadroomSatisfiable.freshTriple, Tacenta.UnitHeadroomSatisfiable.vecOf,
      Tacenta.SessionUnitTripleT3.ratchetAbs, Tacenta.SessionUnitTripleT3.spqrAbs,
      Model.State.maxSkippedStore, Model.SparseRatchet.maxSkippedStore,
      Model.SparseRatchet.epochsKept, U32.max_eq, U64.max_eq, cMax_usize,
      Tacenta.SessionUnitSpqrT3.chainsEntryOf, Tacenta.SessionUnitSpqrT3.chainsOf]
  all_goals omega

/-- The run record at the witness, for every codeword view and every oracle whose KEM model is `K`
and whose draws are the source's. -/
theorem invReal_run (K : Model.Braid.Kem) (dh : DhView) (k pkb ad a)
    (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
    (hK : oracle.braidKem = K) :
    DecryptRatchetRun view oracle byteTrace (invReal k pkb ad a)
      (modelOf dh (invReal k pkb ad a)) sampleMessage sampleRng := by
  have hmodelBraid : (modelOf dh (invReal k pkb ad a)).braid =
      .keysUnsampled 1 Tacenta.UnitSatisfiabilityBraidStates.modelAuth0 := rfl
  refine
    { chunk := ?_
      honest := ?_
      braidEpoch := ?_
      draw := ⟨_, [], sample_trace⟩
      retry := ?_ }
  · intro realComposite modelComposite ciphertext hdecode hcomposite
    rw [sample_decode_model] at hdecode
    have hmc : sampleComposite = modelComposite := (Prod.mk.inj (Except.ok.inj hdecode)).1
    subst hmc
    have hchunk := hcomposite.agChunk
    unfold IncomingChunkRefines
    cases hr : realComposite.ag_chunk with
    | none => simp [sampleComposite]
    | some c => simp [hr, sampleComposite] at hchunk
  · intro modelComposite ciphertext hdecode
    rw [sample_decode_model] at hdecode
    have hmc : sampleComposite = modelComposite := (Prod.mk.inj (Except.ok.inj hdecode)).1
    subst hmc
    intro mc hmc
    simp [Model.Lifecycle.braidMessageOf, sampleComposite] at hmc
  · simp only [invReal, Tacenta.UnitHeadroomSatisfiable.sessionOf,
      Tacenta.UnitHeadroomSatisfiable.freshBraid, Tacenta.SessionUnitBraidT1.State.epoch_val]
    scalar_tac
  · intro modelComposite ciphertext hdecode
    rw [sample_decode_model] at hdecode
    have hmc : sampleComposite = modelComposite := (Prod.mk.inj (Except.ok.inj hdecode)).1
    subst hmc
    apply invReal_retryRunBounds
    rw [hmodelBraid, hK, sample_braid_output]
    rfl

/-- The message is a ratchet frame, so the model's dispatch passes it to `decryptRatchet` unchanged. -/
theorem sampleMessage_type :
    Model.Lifecycle.messageType (sliceOf sampleMessage) = some .ratchet := by
  rw [sliceOf_sampleMessage]
  decide

/-! ## The laws, over an interpretation -/

/-- The laws the joint statement takes, over an interpretation `I` of the unit's opaque constants, a
DH view over it, a Braid KEM model `K` and a function `oeq` standing for `Option::eq`.  Each field is
a statement about opaque constants (or about the view); none mentions a translated function except
through `I`.  At the real constants (`DecryptJointLaws`) the fields are, by name:

* the four laws of `UnitOracleDecrypt.decryptOracleOf_of_laws`: `dhCodec` (`DhCodecTotal`),
  `dhAgree` (`DhAgreeTotal`), `aeadOpen` (`AeadOpenTotal`) and `viewInjective` (the DH view law);
* `codec`: `DhCodecOf`, a hypothesis of the refinement itself;
* the axiom-level fields of `DecryptRatchetContracts` other than those three: `braid`, `triple`
  and `messageKeyMaterial`.  The three zeroize fields stated at the unit's instances are among them:
  `braid.arrayZeroize` (`SessionUnitBraidT1.ArrayZeroizeTotal`), `triple.spqrZeroize`
  (`SessionUnitSpqrT1.ZeroizeTotal`) and the second conjunct of `triple.vecRetain` (the `Vec::zeroize`
  conjunct of `VecRetainTotal`);
* `laws`: `StdLaws`, whose `pop` and `asMut` are the two laws `DecryptRatchetAgreements` states, and
  whose `truncate` and `divCeil` the contract record's defined fields and the erasure agreement use.
  With `triple.vecRetain` (`LawCapacity`, `LawVecZeroize`) and `triple.spqrZeroize` they are the five
  laws `UnitSatisfiabilitySpqrSessionLaws` derives the two sparse agreements from;
* `truncatePrefix`: `TruncatePrefix`, which with `laws.divCeil` gives `ErasureAgrees`;
* `derivedKeys`: the class `DerivedKeysModel`, as a shape;
* `agreements`: the Braid KEM agreements at `K` (`KemLenAgrees K`, `KemAgreesFor K`,
  `ValidateEkAgrees K`, `KemCloneAgrees`) and the KDF agreements (`HkdfAgrees`, `HmacAgrees`);
* `roundTrips`: the five `zeroize` round trips of `DecryptRatchetAgreements`;
* `validKey` and `optionEq`: the two assumptions of `UnitHeadroomInvariant.sessionOf_invariant`
  (a canonical prime-order key exists; `Option::eq` on two `Some` values of `u64` compares them). -/
structure DecryptJointLawsShape (I : Interp) (dh : DhViewShape I) (K : Model.Braid.Kem)
    (oeq : {T : Type} → core.cmp.PartialEq T T → Option T → Option T → Result Bool) : Prop where
  dhCodec : DhCodecShape I
  dhAgree : DhAgreeShape I
  aeadOpen : AeadOpenShape I
  viewInjective : Function.Injective dh.privateKey ∧ Function.Injective dh.publicKey
  codec : DhCodecOfShape I dh
  braid : BraidReceiveAxiom I
  triple : TripleReceiveAxiom I
  messageKeyMaterial : MessageKeyMaterialRoundTripShape I
  laws : StdLaws I
  truncatePrefix : TruncatePrefixShape I
  derivedKeys : Nonempty (ZeroizingModelShape I DerivedZ)
  agreements : T3Agreements I K
  roundTrips : ZeroizeRoundTripShapes I
  validKey : ValidKeyShape I
  optionEq : OptionEqU64Shape oeq

/-- The laws at the real constants, the real `Option::eq`, a DH view and a Braid KEM model. -/
def DecryptJointLaws (K : Model.Braid.Kem) (dh : DhView) : Prop :=
  DecryptJointLawsShape Interp.real ⟨dh.privateKey, dh.publicKey⟩ K
    @core.option.Option.Insts.CoreCmpPartialEqOption.eq

/-- **Where each named law sits in the bundle.**  At the real constants the bundle gives, by
projection and with no proof step beyond unfolding, the four laws of `decryptOracleOf_of_laws`, the
three zeroize fields stated at the unit's instances, the five laws of the sparse agreements, and the
Braid KEM agreement at `K`. -/
theorem decryptJointLaws_named (K : Model.Braid.Kem) (dh : DhView) (L : DecryptJointLaws K dh) :
    (Tacenta.UnitLifecycleT1.DhCodecTotal ∧ Tacenta.UnitLifecycleT1.DhAgreeTotal ∧
      Tacenta.UnitLifecycleT1.AeadOpenTotal ∧
      (Function.Injective dh.privateKey ∧ Function.Injective dh.publicKey)) ∧
    (Tacenta.SessionUnitBraidT1.ArrayZeroizeTotal ∧ Tacenta.SessionUnitSpqrT1.ZeroizeTotal ∧
      Tacenta.UnitSatisfiabilityRatchet.LawVecZeroize) ∧
    (Tacenta.UnitSatisfiabilityRatchet.LawPop ∧ Tacenta.UnitSatisfiabilityRatchet.LawAsMut ∧
      Tacenta.UnitSatisfiabilityRatchet.LawCapacity ∧
      Tacenta.UnitSatisfiabilityRatchet.LawVecZeroize ∧ Tacenta.SessionUnitSpqrT1.ZeroizeTotal) ∧
    Tacenta.SessionUnitBraidT3.KemAgreesFor K :=
  ⟨⟨L.dhCodec, L.dhAgree, L.aeadOpen, L.viewInjective⟩,
    ⟨L.braid.arrayZeroize, L.triple.spqrZeroize, L.triple.vecRetain.2⟩,
    ⟨L.laws.pop, L.laws.asMut, L.triple.vecRetain.1, L.triple.vecRetain.2, L.triple.spqrZeroize⟩,
    L.agreements.kemAgrees⟩

/-! ## The statement -/

/-- The hypotheses of `UnitLifecycleDecryptRatchetCompleteT3.decrypt_ratchet_refines_complete`, at
one choice of every binder, with `Session::invariant` added: the hypothesis set this module shows
satisfiable together. -/
structure DecryptHypotheses {R : Type} (rngCore : rand_core_1.RngCore R)
    (cryptoRng : rand_core_1.CryptoRng R) (trace : R → List Model.Lifecycle.Key) (dh : DhView)
    (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
    (real : lifecycle.Session) (model : Model.Lifecycle.Session) (message : Slice Std.U8)
    (rng : R) : Prop where
  oracleOf : DecryptOracleOf rngCore cryptoRng dh trace oracle
  codec : DhCodecOf dh
  contracts : Tacenta.UnitLifecycleT1.DecryptRatchetContracts rngCore
  derivedKeys : Nonempty Tacenta.SessionUnitT1.DerivedKeysModel
  agreements : DecryptRatchetAgreements oracle.braidKem
  invariant : lifecycle.Session.invariant real = ok true
  related : SessionRefines dh oracle.braidKem real model
  headroom : Tacenta.UnitLifecycleT1.DecryptRatchetHeadroom real
  trace_eq : trace rng = oracle.draws
  run : DecryptRatchetRun view oracle trace real model message rng

/-- The hypothesis set is the theorem's: from it, `decrypt_ratchet_refines_complete` applies.  A
hypothesis added to that theorem and not to `DecryptHypotheses` stops this module building. -/
theorem DecryptHypotheses.refines {R : Type} {rngCore : rand_core_1.RngCore R}
    {cryptoRng : rand_core_1.CryptoRng R} {trace : R → List Model.Lifecycle.Key} {dh : DhView}
    {view : Model.Lifecycle.CodewordView} {oracle : Model.Lifecycle.Oracle}
    {real : lifecycle.Session} {model : Model.Lifecycle.Session} {message : Slice Std.U8} {rng : R}
    (h : DecryptHypotheses rngCore cryptoRng trace dh view oracle real model message rng) :
    ∃ output,
      lifecycle.Session.decrypt_ratchet rngCore cryptoRng real message rng = ok output ∧
      StepRefines trace dh oracle.braidKem output
        (Model.Lifecycle.decryptRatchet view oracle model (sliceOf message)) := by
  obtain ⟨inst⟩ := h.derivedKeys
  exact Tacenta.UnitLifecycleDecryptRatchetCompleteT3.decrypt_ratchet_refines_complete rngCore
    cryptoRng trace dh view oracle h.oracleOf h.codec h.contracts h.agreements real model message
    rng h.related h.headroom h.trace_eq h.run

/-- The statement of `decrypt_hypotheses_jointly_satisfiable`: under the laws at the real constants
and a Braid KEM model `K`, there are an oracle whose KEM model is `K`, a session that passes
`Session::invariant`, a related model session, a message that decodes on both sides and is a ratchet
frame, and a byte-stream source, at which every hypothesis of the decrypt refinement holds, for every
codeword view. -/
def DecryptHypothesesJointlySatisfiableStatement : Prop :=
  ∀ (K : Model.Braid.Kem) (dh : DhView), DecryptJointLaws K dh →
    ∃ (oracle : Model.Lifecycle.Oracle) (real : lifecycle.Session)
      (model : Model.Lifecycle.Session) (message : Slice Std.U8) (rng : List Std.U8),
      oracle.braidKem = K ∧
      (∃ decoded, tacenta_wire.decode_message message = ok (.Ok decoded)) ∧
      (∃ composite ciphertext,
        Model.CompositeHeader.decodeDetailed (sliceOf message) = .ok (composite, ciphertext)) ∧
      Model.Lifecycle.messageType (sliceOf message) = some .ratchet ∧
      ∀ view : Model.Lifecycle.CodewordView,
        DecryptHypotheses byteRng byteCrc byteTrace dh view oracle real model message rng

/-! ## The witness -/

/-- **Every hypothesis of the decrypt refinement at one explicit witness.**  The state is
`invReal k pkb ad a` for a key `k` whose public key `pkb` has the canonical prime-order bytes `a`, and
`ad` the associated data `identity_ad(pkb, pkb)` computes; the model state is `modelOf dh` of it;
the message is `sampleMessage`; the source is `sampleRng`, one 32-byte draw. -/
theorem decrypt_hypotheses_at_invReal (K : Model.Braid.Kem) (dh : DhView)
    (L : DecryptJointLaws K dh) (oracle : Model.Lifecycle.Oracle)
    (hK : oracle.braidKem = K) (hdraws : oracle.draws = byteTrace sampleRng)
    (horacle : DecryptOracleOf byteRng byteCrc dh byteTrace oracle)
    (k : tacenta_boundary.dh.PrivateKey) (pkb : tacenta_boundary.dh.PublicKeyBytes)
    (a : Array U8 32#usize)
    (hpub : tacenta_boundary.dh.PrivateKey.public_key k = ok pkb)
    (hbytes : tacenta_boundary.dh.PublicKeyBytes.as_bytes pkb = ok a)
    (hcan : Tacenta.SessionUnitT1.canonicalX25519 a = true)
    (hprime : tacenta_boundary.dh.is_prime_order_public pkb = ok true)
    (ad : alloc.vec.Vec U8) (had : lifecycle.identity_ad pkb pkb = ok ad)
    (hlen : ad.val.length = 66) (view : Model.Lifecycle.CodewordView) :
    DecryptHypotheses byteRng byteCrc byteTrace dh view oracle (invReal k pkb ad a)
      (modelOf dh (invReal k pkb ad a)) sampleMessage sampleRng := by
  have hb := decrypt_shapes_are_predicates
  have r32 : Tacenta.UnitLifecycleT1.Random32Total byteRng := fun _ _ _ => ⟨_, rfl⟩
  have ax : DecryptAxiom Interp.real byteRng :=
    ⟨L.dhCodec, L.dhAgree, L.aeadOpen, r32, L.braid, L.triple, L.messageKeyMaterial⟩
  have hz := hb.2.2.2 L.roundTrips
  have er : Tacenta.SessionUnitBraidT3.ErasureAgrees :=
    Tacenta.UnitErasureRs.Glue.erasureAgrees L.laws.divCeil L.truncatePrefix
  refine
    { oracleOf := horacle
      codec := (hb.1 dh).2 L.codec
      contracts := Tacenta.UnitSatisfiabilityRecords.decrypt_contracts_of_axiom_base byteRng ax L.laws
      derivedKeys := L.derivedKeys.elim fun s => ⟨s.toDerived⟩
      agreements := ?_
      invariant := sessionOf_invariant k pkb a hpub hbytes hcan hprime L.optionEq ad had
      related := hK ▸ invReal_sessionRefines K dh k pkb ad a
      headroom := invReal_headroom k pkb a ad hlen
      trace_eq := hdraws.symm
      run := invReal_run K dh k pkb ad a view oracle hK }
  rw [hK]
  exact ⟨L.agreements.hmac, L.agreements.hkdf, hz.1, hz.2.1, hz.2.2.1, hz.2.2.2.1, L.laws.pop,
    L.laws.asMut, L.agreements.kemAgrees, er, L.agreements.kemLen, L.agreements.validateEk,
    L.agreements.kemClone, hz.2.2.2.2⟩

/-- **The hypotheses of the decrypt refinement hold together at the real constants, under named
laws, with the agreements at the same oracle's KEM model.**  For every Braid KEM model `K` and DH view
`dh` meeting the laws `DecryptJointLaws K dh`, there are an oracle with `braidKem = K` (the code's
oracle, `decryptOracleOf_of_laws`), a session that passes `Session::invariant`, a related model
session, a message that decodes on both sides and is a ratchet frame, and a byte-stream source, at
which every hypothesis of `decrypt_ratchet_refines_complete` holds (`DecryptHypotheses`), for every
codeword view.

What it is not: the state is built for the hypotheses (a session over fresh states, not shown to be
produced by establishment or `import`); the laws are assumed; the oracle is the code read through its
byte views, not the primitives proved; the run carries no agreement chunk; and which way the model's
step at the witness goes is not fixed by the laws: it refuses at the first agreement if the real
agreement refuses the all-zero key (`invReal_model_refuses_of_agreement`, `invReal_agreement_is_real`),
which by reading the X25519 boundary it does, and no law states.  Both platform widths: no proof
chooses one. -/
theorem decrypt_hypotheses_jointly_satisfiable (K : Model.Braid.Kem) (dh : DhView)
    (L : DecryptJointLaws K dh) :
    ∃ (oracle : Model.Lifecycle.Oracle) (real : lifecycle.Session)
      (model : Model.Lifecycle.Session) (message : Slice Std.U8) (rng : List Std.U8),
      oracle.braidKem = K ∧
      (∃ decoded, tacenta_wire.decode_message message = ok (.Ok decoded)) ∧
      (∃ composite ciphertext,
        Model.CompositeHeader.decodeDetailed (sliceOf message) = .ok (composite, ciphertext)) ∧
      Model.Lifecycle.messageType (sliceOf message) = some .ratchet ∧
      ∀ view : Model.Lifecycle.CodewordView,
        DecryptHypotheses byteRng byteCrc byteTrace dh view oracle real model message rng := by
  obtain ⟨oracle, hdraws, hK, horacle⟩ :=
    Tacenta.UnitOracleDecrypt.decryptOracleOf_of_laws dh L.dhCodec L.dhAgree L.aeadOpen
      L.viewInjective (byteTrace sampleRng) K
  obtain ⟨k, pkb, a, hpub, hbytes, hcan, hprime⟩ := L.validKey
  obtain ⟨ad, had, hlen⟩ :=
    Std.WP.spec_imp_exists (Tacenta.UnitLifecycleT1.identity_ad_length L.dhCodec pkb pkb)
  obtain ⟨decoded, hdec, -⟩ := sample_decode_real
  exact ⟨oracle, invReal k pkb ad a, modelOf dh (invReal k pkb ad a), sampleMessage, sampleRng, hK,
    ⟨decoded, hdec⟩, ⟨_, _, sample_decode_model⟩, sampleMessage_type,
    fun view => decrypt_hypotheses_at_invReal K dh L oracle hK hdraws horacle k pkb a hpub hbytes
      hcan hprime ad had hlen view⟩

theorem decrypt_hypotheses_jointly_satisfiable_statement :
    DecryptHypothesesJointlySatisfiableStatement :=
  decrypt_hypotheses_jointly_satisfiable

/-! ## What the model does at the witness -/

/-- **The model's step at the witness refuses at the first agreement when the oracle's agreement
refuses the all-zero key** (the composite's ratchet key is 32 zero bytes). -/
theorem invReal_model_refuses_of_agreement (dh : DhView) (view : Model.Lifecycle.CodewordView)
    (oracle : Model.Lifecycle.Oracle) (k pkb ad a)
    (hnone : oracle.dhAgree (dh.privateKey k) (List.replicate 32 0) = none) :
    (Model.Lifecycle.decryptRatchet view oracle (modelOf dh (invReal k pkb ad a))
      (sliceOf sampleMessage)).result = .error (.handshake .nonContributoryAgreement) := by
  have hzero : sampleComposite.dh = List.replicate 32 0 := rfl
  simp [Model.Lifecycle.decryptRatchet, Model.Lifecycle.agreementFailed, modelOf, invReal,
    Tacenta.UnitHeadroomSatisfiable.sessionOf, sample_decode_model, hzero]
  simp only [List.replicate] at hnone
  simp [hnone]

/-- At an oracle meeting `DecryptOracleOf` with a view meeting `DhCodecOf`, the oracle's agreement on
the all-zero key is the real `agree` on the key `PublicKeyBytes::from_bytes` returns for 32 zero
bytes, read through the views.  So which way the model's step at the witness goes is fixed by that
one value of the real function, which no law states. -/
theorem invReal_agreement_is_real (dh : DhView) (oracle : Model.Lifecycle.Oracle)
    (horacle : DecryptOracleOf byteRng byteCrc dh byteTrace oracle) (hcodec : DhCodecOf dh)
    (k : tacenta_boundary.dh.PrivateKey) :
    ∃ p result, tacenta_boundary.dh.PublicKeyBytes.from_bytes
        Tacenta.UnitLifecycleDecryptRatchetScreen.zeros32 = ok p ∧
      tacenta_boundary.dh.PrivateKey.agree k p = ok result ∧
      oracle.dhAgree (dh.privateKey k) (List.replicate 32 0) = result.map arrayOf := by
  obtain ⟨p, hp, hview⟩ := hcodec.fromBytes Tacenta.UnitLifecycleDecryptRatchetScreen.zeros32
  obtain ⟨result, hr, hmap⟩ := horacle.dhAgree k p
  have hz : arrayOf Tacenta.UnitLifecycleDecryptRatchetScreen.zeros32 = List.replicate 32 0 := by
    simp [arrayOf, Tacenta.UnitLifecycleDecryptRatchetScreen.zeros32, Array.repeat,
      Tacenta.SessionUnitBraidT3.u8]
  refine ⟨p, result, hp, hr, ?_⟩
  rw [hmap, hview, hz]

/-! ## One interpretation satisfies the laws -/

theorem modelDecrypt_validKey : ValidKeyShape Interp.modelDecrypt :=
  ⟨Tacenta.UnitLifecycleDecryptRatchetScreen.zeros32, Tacenta.UnitLifecycleDecryptRatchetScreen.zeros32,
    Tacenta.UnitLifecycleDecryptRatchetScreen.zeros32, rfl, rfl,
    Tacenta.SessionUnitRatchetImportInv.Ratchet.canonical_zeros, rfl⟩

/-- **The laws have a model.**  `Interp.modelDecrypt` (`UnitLifecycleDecryptRatchetScreen.lean`), its
view `viewDecrypt`, the KEM model `toyKem` and `optionEqImpl` (the standard library's definition of
`Option::eq`) satisfy every field of `DecryptJointLawsShape` together. -/
theorem decrypt_joint_laws_model :
    DecryptJointLawsShape Interp.modelDecrypt viewDecrypt Model.Braid.toyKem @optionEqImpl where
  dhCodec := modelDecrypt_allT1.dhCodec
  dhAgree := modelDecrypt_allT1.dhAgree
  aeadOpen := modelDecrypt_allT1.aeadOpen
  viewInjective := ⟨fun _ _ h => Tacenta.DispatchEvidenceVacuity.arrayOf_inj h,
    fun _ _ h => Tacenta.DispatchEvidenceVacuity.arrayOf_inj h⟩
  codec := modelDecrypt_codec
  braid := ⟨modelDecrypt_allT1.ct1Len, modelDecrypt_allT1.ct2Len, modelDecrypt_allT1.headerLen,
    modelDecrypt_allT1.ekVectorLen, modelDecrypt_allT1.keyPairEkVector,
    modelDecrypt_allT1.keyPairDecapsulate, modelDecrypt_allT1.hkdf, modelDecrypt_allT1.hmac,
    modelDecrypt_allT1.validateEk, modelDecrypt_allT1.encapsulate2, modelDecrypt_allT1.keyPairClone,
    modelDecrypt_allT1.encapsStateClone, modelDecrypt_allT1.optionClone,
    modelDecrypt_allT1.zeroizingArray, modelDecrypt_allT1.arrayZeroize,
    modelDecrypt_allT1.rangeFullIndex⟩
  triple := ⟨modelDecrypt_allT1.hmac, modelDecrypt_allT1.hkdf, modelDecrypt_allT1.zeroizingTotal,
    modelDecrypt_allT1.spqrZeroize, modelDecrypt_allT1.vecRetainAxiom,
    modelDecrypt_allT1.optionClone, trivial⟩
  messageKeyMaterial := modelDecrypt_allT1.messageKeyMaterial
  laws := modelDecrypt_stdLaws
  truncatePrefix := modelDecrypt_truncatePrefix
  derivedKeys := ⟨modelDecrypt_zeroizingModel DerivedZ⟩
  agreements := modelDecrypt_t3
  roundTrips := modelDecrypt_zeroize
  validKey := modelDecrypt_validKey
  optionEq := optionEqImpl_shape

/-- The laws and the model, in one statement: some interpretation, view, KEM model and `Option::eq`
satisfy the bundle. -/
theorem decrypt_joint_laws_satisfiable :
    ∃ (I : Interp) (dh : DhViewShape I) (K : Model.Braid.Kem)
      (oeq : {T : Type} → core.cmp.PartialEq T T → Option T → Option T → Result Bool),
      DecryptJointLawsShape I dh K oeq :=
  ⟨Interp.modelDecrypt, viewDecrypt, Model.Braid.toyKem, @optionEqImpl, decrypt_joint_laws_model⟩

end Tacenta.UnitLifecycleDecryptScreen

/-! ## Pins

The axiom list and the statement of each result, and the bodies of the witness session, the law
bundle, the hypothesis set and the statement, held by the build.  `attest.py` requires them
(`REQUIRED_PINS`, `REQUIRED_STATEMENT_PINS`, `REQUIRED_PRINT_FORM`).  `DecryptHypotheses.refines`
lists the nine per-declaration `native_decide` axioms `decrypt_ratchet_refines_complete` rests on
(compiler-trusted, `COMPILER_TRUSTED_PINS`); no other result here lists one. -/

/--
info: 'Tacenta.UnitLifecycleDecryptScreen.invReal_sessionRefines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kem.EncapsState,
 tacenta_kem.IncrementalKeyPair,
 tacenta_kem.encapsulate2,
 tacenta_boundary.dh.PrivateKey,
 tacenta_boundary.dh.PublicKeyBytes,
 tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_kem.IncrementalKeyPair.header,
 alloc.vec.Vec.truncate,
 core.num.Usize.div_ceil]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleDecryptScreen.invReal_sessionRefines

/--
info: Tacenta.UnitLifecycleDecryptScreen.invReal_sessionRefines : ∀ (K : Model.Braid.Kem) (dh : DhView)
  (k : tacenta_boundary.dh.PrivateKey) (pkb : tacenta_boundary.dh.PublicKeyBytes) (ad : alloc.vec.Vec U8)
  (a : Std.Array U8 32#usize),
  SessionRefines dh K (Tacenta.UnitLifecycleDecryptScreen.invReal k pkb ad a)
    (modelOf dh (Tacenta.UnitLifecycleDecryptScreen.invReal k pkb ad a))
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptScreen.invReal_sessionRefines

/--
info: 'Tacenta.UnitLifecycleDecryptScreen.invReal_headroom' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kem.EncapsState,
 tacenta_kem.IncrementalKeyPair,
 tacenta_boundary.dh.PrivateKey,
 tacenta_boundary.dh.PublicKeyBytes]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleDecryptScreen.invReal_headroom

/--
info: Tacenta.UnitLifecycleDecryptScreen.invReal_headroom : ∀ (k : tacenta_boundary.dh.PrivateKey)
  (pkb : tacenta_boundary.dh.PublicKeyBytes) (a : Std.Array U8 32#usize) (ad : alloc.vec.Vec U8),
  (↑ad).length = 66 →
    Tacenta.UnitLifecycleT1.DecryptRatchetHeadroom (Tacenta.UnitLifecycleDecryptScreen.invReal k pkb ad a)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptScreen.invReal_headroom

/--
info: 'Tacenta.UnitLifecycleDecryptScreen.invReal_retryRunBounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kem.EncapsState,
 tacenta_kem.IncrementalKeyPair,
 tacenta_boundary.dh.PrivateKey,
 tacenta_boundary.dh.PublicKeyBytes]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleDecryptScreen.invReal_retryRunBounds

/--
info: Tacenta.UnitLifecycleDecryptScreen.invReal_retryRunBounds : ∀ (k : tacenta_boundary.dh.PrivateKey)
  (pkb : tacenta_boundary.dh.PublicKeyBytes) (ad : alloc.vec.Vec U8) (a : Std.Array U8 32#usize) (dh : DhView)
  (output : Option Model.SparseRatchet.Output),
  output = none →
    RetryRunBounds (modelOf dh (Tacenta.UnitLifecycleDecryptScreen.invReal k pkb ad a)).triple
      (Model.Lifecycle.tripleHeaderOf sampleComposite) output
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptScreen.invReal_retryRunBounds

/--
info: 'Tacenta.UnitLifecycleDecryptScreen.invReal_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kem.EncapsState,
 tacenta_kem.IncrementalKeyPair,
 tacenta_boundary.dh.PrivateKey,
 tacenta_boundary.dh.PublicKeyBytes,
 core.num.Usize.div_ceil]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleDecryptScreen.invReal_run

/--
info: Tacenta.UnitLifecycleDecryptScreen.invReal_run : ∀ (K : Model.Braid.Kem) (dh : DhView)
  (k : tacenta_boundary.dh.PrivateKey) (pkb : tacenta_boundary.dh.PublicKeyBytes) (ad : alloc.vec.Vec U8)
  (a : Std.Array U8 32#usize) (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle),
  oracle.braidKem = K →
    DecryptRatchetRun view oracle byteTrace (Tacenta.UnitLifecycleDecryptScreen.invReal k pkb ad a)
      (modelOf dh (Tacenta.UnitLifecycleDecryptScreen.invReal k pkb ad a)) sampleMessage sampleRng
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptScreen.invReal_run

/--
info: 'Tacenta.UnitLifecycleDecryptScreen.sampleMessage_type' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleDecryptScreen.sampleMessage_type

/--
info: Tacenta.UnitLifecycleDecryptScreen.sampleMessage_type : Model.Lifecycle.messageType (sliceOf sampleMessage) =
  some Model.Lifecycle.MessageType.ratchet
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptScreen.sampleMessage_type

/--
info: 'Tacenta.UnitLifecycleDecryptScreen.decryptJointLaws_named' depends on axioms: [propext,
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
 core.option.Option.Insts.CoreCmpPartialEqOption.eq,
 tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleDecryptScreen.decryptJointLaws_named

/--
info: Tacenta.UnitLifecycleDecryptScreen.decryptJointLaws_named : ∀ (K : Model.Braid.Kem) (dh : DhView),
  Tacenta.UnitLifecycleDecryptScreen.DecryptJointLaws K dh →
    (Tacenta.UnitLifecycleT1.DhCodecTotal ∧
        Tacenta.UnitLifecycleT1.DhAgreeTotal ∧
          Tacenta.UnitLifecycleT1.AeadOpenTotal ∧ Function.Injective dh.privateKey ∧ Function.Injective dh.publicKey) ∧
      (Tacenta.SessionUnitBraidT1.ArrayZeroizeTotal ∧
          Tacenta.SessionUnitSpqrT1.ZeroizeTotal ∧ Tacenta.UnitSatisfiabilityRatchet.LawVecZeroize) ∧
        (Tacenta.UnitSatisfiabilityRatchet.LawPop ∧
            Tacenta.UnitSatisfiabilityRatchet.LawAsMut ∧
              Tacenta.UnitSatisfiabilityRatchet.LawCapacity ∧
                Tacenta.UnitSatisfiabilityRatchet.LawVecZeroize ∧ Tacenta.SessionUnitSpqrT1.ZeroizeTotal) ∧
          Tacenta.SessionUnitBraidT3.KemAgreesFor K
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptScreen.decryptJointLaws_named

/--
info: 'Tacenta.UnitLifecycleDecryptScreen.DecryptHypotheses.refines' depends on axioms: [propext,
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
 tacenta_boundary.dh.PrivateKey,
 tacenta_boundary.dh.PublicKeyBytes,
 tacenta_boundary.dh.is_prime_order_public,
 tacenta_boundary.kem.ciphertext_len,
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
 Tacenta.SessionUnitSpqrT3.chain_label_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.chain_start_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.max_skip_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.max_skip_val._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.max_skipped_store_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.protocol_info_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.receive_refines_continuation._native.native_decide.ax_1_29,
 Tacenta.SessionUnitSpqrT3.root_label_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitTripleT3.combine_info_agrees._native.native_decide.ax_1_1,
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
#print axioms Tacenta.UnitLifecycleDecryptScreen.DecryptHypotheses.refines

/--
info: @Tacenta.UnitLifecycleDecryptScreen.DecryptHypotheses.refines : ∀ {R : Type} {rngCore : rand_core_1.RngCore R}
  {cryptoRng : rand_core_1.CryptoRng R} {trace : R → List Model.Lifecycle.Key} {dh : DhView}
  {view : Model.Lifecycle.CodewordView} {oracle : Model.Lifecycle.Oracle} {real : lifecycle.Session}
  {model : Model.Lifecycle.Session} {message : Slice U8} {rng : R},
  Tacenta.UnitLifecycleDecryptScreen.DecryptHypotheses rngCore cryptoRng trace dh view oracle real model message rng →
    ∃ output,
      lifecycle.Session.decrypt_ratchet rngCore cryptoRng real message rng = ok output ∧
        StepRefines trace dh oracle.braidKem output (Model.Lifecycle.decryptRatchet view oracle model (sliceOf message))
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptScreen.DecryptHypotheses.refines

/--
info: 'Tacenta.UnitLifecycleDecryptScreen.decrypt_hypotheses_at_invReal' depends on axioms: [propext,
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
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleDecryptScreen.decrypt_hypotheses_at_invReal

/--
info: Tacenta.UnitLifecycleDecryptScreen.decrypt_hypotheses_at_invReal : ∀ (K : Model.Braid.Kem) (dh : DhView),
  Tacenta.UnitLifecycleDecryptScreen.DecryptJointLaws K dh →
    ∀ (oracle : Model.Lifecycle.Oracle),
      oracle.braidKem = K →
        oracle.draws = byteTrace sampleRng →
          DecryptOracleOf byteRng byteCrc dh byteTrace oracle →
            ∀ (k : tacenta_boundary.dh.PrivateKey) (pkb : tacenta_boundary.dh.PublicKeyBytes)
              (a : Std.Array U8 32#usize),
              k.public_key = ok pkb →
                pkb.as_bytes = ok a →
                  Tacenta.SessionUnitT1.canonicalX25519 a = true →
                    tacenta_boundary.dh.is_prime_order_public pkb = ok true →
                      ∀ (ad : alloc.vec.Vec U8),
                        lifecycle.identity_ad pkb pkb = ok ad →
                          (↑ad).length = 66 →
                            ∀ (view : Model.Lifecycle.CodewordView),
                              Tacenta.UnitLifecycleDecryptScreen.DecryptHypotheses byteRng byteCrc byteTrace dh view
                                oracle (Tacenta.UnitLifecycleDecryptScreen.invReal k pkb ad a)
                                (modelOf dh (Tacenta.UnitLifecycleDecryptScreen.invReal k pkb ad a)) sampleMessage
                                sampleRng
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptScreen.decrypt_hypotheses_at_invReal

/--
info: 'Tacenta.UnitLifecycleDecryptScreen.decrypt_hypotheses_jointly_satisfiable' depends on axioms: [propext,
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
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleDecryptScreen.decrypt_hypotheses_jointly_satisfiable

/--
info: Tacenta.UnitLifecycleDecryptScreen.decrypt_hypotheses_jointly_satisfiable : ∀ (K : Model.Braid.Kem) (dh : DhView),
  Tacenta.UnitLifecycleDecryptScreen.DecryptJointLaws K dh →
    ∃ oracle real model message rng,
      oracle.braidKem = K ∧
        (∃ decoded, tacenta_wire.decode_message message = ok (core.result.Result.Ok decoded)) ∧
          (∃ composite ciphertext,
              Model.CompositeHeader.decodeDetailed (sliceOf message) = Except.ok (composite, ciphertext)) ∧
            Model.Lifecycle.messageType (sliceOf message) = some Model.Lifecycle.MessageType.ratchet ∧
              ∀ (view : Model.Lifecycle.CodewordView),
                Tacenta.UnitLifecycleDecryptScreen.DecryptHypotheses byteRng byteCrc byteTrace dh view oracle real model
                  message rng
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptScreen.decrypt_hypotheses_jointly_satisfiable

/--
info: 'Tacenta.UnitLifecycleDecryptScreen.decrypt_hypotheses_jointly_satisfiable_statement' depends on axioms: [propext,
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
 core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleDecryptScreen.decrypt_hypotheses_jointly_satisfiable_statement

/--
info: Tacenta.UnitLifecycleDecryptScreen.decrypt_hypotheses_jointly_satisfiable_statement : Tacenta.UnitLifecycleDecryptScreen.DecryptHypothesesJointlySatisfiableStatement
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptScreen.decrypt_hypotheses_jointly_satisfiable_statement

/--
info: 'Tacenta.UnitLifecycleDecryptScreen.invReal_model_refuses_of_agreement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kem.EncapsState,
 tacenta_kem.IncrementalKeyPair,
 tacenta_boundary.dh.PrivateKey,
 tacenta_boundary.dh.PublicKeyBytes]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleDecryptScreen.invReal_model_refuses_of_agreement

/--
info: Tacenta.UnitLifecycleDecryptScreen.invReal_model_refuses_of_agreement : ∀ (dh : DhView)
  (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle) (k : tacenta_boundary.dh.PrivateKey)
  (pkb : tacenta_boundary.dh.PublicKeyBytes) (ad : alloc.vec.Vec U8) (a : Std.Array U8 32#usize),
  oracle.dhAgree (dh.privateKey k) (List.replicate 32 0) = none →
    (Model.Lifecycle.decryptRatchet view oracle (modelOf dh (Tacenta.UnitLifecycleDecryptScreen.invReal k pkb ad a))
          (sliceOf sampleMessage)).result =
      Except.error (Model.Lifecycle.Refusal.handshake Model.Lifecycle.HandshakeRefusal.nonContributoryAgreement)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptScreen.invReal_model_refuses_of_agreement

/--
info: 'Tacenta.UnitLifecycleDecryptScreen.invReal_agreement_is_real' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 rand_core_1.error.Error,
 tacenta_boundary.aead.decrypt,
 tacenta_boundary.dh.PrivateKey,
 tacenta_boundary.dh.PublicKeyBytes,
 tacenta_boundary.dh.PrivateKey.agree,
 tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_boundary.dh.PublicKeyBytes.from_bytes]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleDecryptScreen.invReal_agreement_is_real

/--
info: Tacenta.UnitLifecycleDecryptScreen.invReal_agreement_is_real : ∀ (dh : DhView) (oracle : Model.Lifecycle.Oracle),
  DecryptOracleOf byteRng byteCrc dh byteTrace oracle →
    DhCodecOf dh →
      ∀ (k : tacenta_boundary.dh.PrivateKey),
        ∃ p result,
          tacenta_boundary.dh.PublicKeyBytes.from_bytes Tacenta.UnitLifecycleDecryptRatchetScreen.zeros32 = ok p ∧
            k.agree p = ok result ∧ oracle.dhAgree (dh.privateKey k) (List.replicate 32 0) = Option.map arrayOf result
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptScreen.invReal_agreement_is_real

/--
info: 'Tacenta.UnitLifecycleDecryptScreen.modelDecrypt_validKey' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleDecryptScreen.modelDecrypt_validKey

/--
info: Tacenta.UnitLifecycleDecryptScreen.modelDecrypt_validKey : ValidKeyShape Interp.modelDecrypt
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptScreen.modelDecrypt_validKey

/--
info: 'Tacenta.UnitLifecycleDecryptScreen.decrypt_joint_laws_model' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleDecryptScreen.decrypt_joint_laws_model

/--
info: Tacenta.UnitLifecycleDecryptScreen.decrypt_joint_laws_model : Tacenta.UnitLifecycleDecryptScreen.DecryptJointLawsShape
  Interp.modelDecrypt viewDecrypt Model.Braid.toyKem @optionEqImpl
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptScreen.decrypt_joint_laws_model

/--
info: 'Tacenta.UnitLifecycleDecryptScreen.decrypt_joint_laws_satisfiable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleDecryptScreen.decrypt_joint_laws_satisfiable

/--
info: Tacenta.UnitLifecycleDecryptScreen.decrypt_joint_laws_satisfiable : ∃ I dh K oeq,
  Tacenta.UnitLifecycleDecryptScreen.DecryptJointLawsShape I dh K fun {T} => oeq
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleDecryptScreen.decrypt_joint_laws_satisfiable

/--
info: def Tacenta.UnitLifecycleDecryptScreen.invReal : tacenta_boundary.dh.PrivateKey →
  tacenta_boundary.dh.PublicKeyBytes → alloc.vec.Vec U8 → Std.Array U8 32#usize → lifecycle.Session :=
fun k pkb ad a => Tacenta.UnitHeadroomSatisfiable.sessionOf k pkb pkb ad a none
-/
#guard_msgs in
#print Tacenta.UnitLifecycleDecryptScreen.invReal

/--
info: structure Tacenta.UnitLifecycleDecryptScreen.DecryptJointLawsShape (I : Interp) (dh : DhViewShape I)
  (K : Model.Braid.Kem) (oeq : {T : Type} → core.cmp.PartialEq T T → Option T → Option T → Result Bool) : Prop
number of parameters: 4
fields:
  Tacenta.UnitLifecycleDecryptScreen.DecryptJointLawsShape.dhCodec : DhCodecShape I
  Tacenta.UnitLifecycleDecryptScreen.DecryptJointLawsShape.dhAgree : DhAgreeShape I
  Tacenta.UnitLifecycleDecryptScreen.DecryptJointLawsShape.aeadOpen : AeadOpenShape I
  Tacenta.UnitLifecycleDecryptScreen.DecryptJointLawsShape.viewInjective : Function.Injective dh.privateKey ∧
      Function.Injective dh.publicKey
  Tacenta.UnitLifecycleDecryptScreen.DecryptJointLawsShape.codec : DhCodecOfShape I dh
  Tacenta.UnitLifecycleDecryptScreen.DecryptJointLawsShape.braid : BraidReceiveAxiom I
  Tacenta.UnitLifecycleDecryptScreen.DecryptJointLawsShape.triple : TripleReceiveAxiom I
  Tacenta.UnitLifecycleDecryptScreen.DecryptJointLawsShape.messageKeyMaterial : MessageKeyMaterialRoundTripShape I
  Tacenta.UnitLifecycleDecryptScreen.DecryptJointLawsShape.laws : StdLaws I
  Tacenta.UnitLifecycleDecryptScreen.DecryptJointLawsShape.truncatePrefix : TruncatePrefixShape I
  Tacenta.UnitLifecycleDecryptScreen.DecryptJointLawsShape.derivedKeys : Nonempty (ZeroizingModelShape I DerivedZ)
  Tacenta.UnitLifecycleDecryptScreen.DecryptJointLawsShape.agreements : T3Agreements I K
  Tacenta.UnitLifecycleDecryptScreen.DecryptJointLawsShape.roundTrips : ZeroizeRoundTripShapes I
  Tacenta.UnitLifecycleDecryptScreen.DecryptJointLawsShape.validKey : ValidKeyShape I
  Tacenta.UnitLifecycleDecryptScreen.DecryptJointLawsShape.optionEq : OptionEqU64Shape fun {T} => oeq
constructor:
  Tacenta.UnitLifecycleDecryptScreen.DecryptJointLawsShape.mk {I : Interp} {dh : DhViewShape I} {K : Model.Braid.Kem}
    {oeq : {T : Type} → core.cmp.PartialEq T T → Option T → Option T → Result Bool} (dhCodec : DhCodecShape I)
    (dhAgree : DhAgreeShape I) (aeadOpen : AeadOpenShape I)
    (viewInjective : Function.Injective dh.privateKey ∧ Function.Injective dh.publicKey) (codec : DhCodecOfShape I dh)
    (braid : BraidReceiveAxiom I) (triple : TripleReceiveAxiom I)
    (messageKeyMaterial : MessageKeyMaterialRoundTripShape I) (laws : StdLaws I)
    (truncatePrefix : TruncatePrefixShape I) (derivedKeys : Nonempty (ZeroizingModelShape I DerivedZ))
    (agreements : T3Agreements I K) (roundTrips : ZeroizeRoundTripShapes I) (validKey : ValidKeyShape I)
    (optionEq : OptionEqU64Shape fun {T} => oeq) : Tacenta.UnitLifecycleDecryptScreen.DecryptJointLawsShape I dh K oeq
-/
#guard_msgs in
#print Tacenta.UnitLifecycleDecryptScreen.DecryptJointLawsShape

/--
info: def Tacenta.UnitLifecycleDecryptScreen.DecryptJointLaws : Model.Braid.Kem → DhView → Prop :=
fun K dh =>
  Tacenta.UnitLifecycleDecryptScreen.DecryptJointLawsShape Interp.real
    { privateKey := dh.privateKey, publicKey := dh.publicKey } K @core.option.Option.Insts.CoreCmpPartialEqOption.eq
-/
#guard_msgs in
#print Tacenta.UnitLifecycleDecryptScreen.DecryptJointLaws

/--
info: structure Tacenta.UnitLifecycleDecryptScreen.DecryptHypotheses {R : Type} (rngCore : rand_core_1.RngCore R)
  (cryptoRng : rand_core_1.CryptoRng R) (trace : R → List Model.Lifecycle.Key) (dh : DhView)
  (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle) (real : lifecycle.Session)
  (model : Model.Lifecycle.Session) (message : Slice U8) (rng : R) : Prop
number of parameters: 11
fields:
  Tacenta.UnitLifecycleDecryptScreen.DecryptHypotheses.oracleOf : DecryptOracleOf rngCore cryptoRng dh trace oracle
  Tacenta.UnitLifecycleDecryptScreen.DecryptHypotheses.codec : DhCodecOf dh
  Tacenta.UnitLifecycleDecryptScreen.DecryptHypotheses.contracts : Tacenta.UnitLifecycleT1.DecryptRatchetContracts
      rngCore
  Tacenta.UnitLifecycleDecryptScreen.DecryptHypotheses.derivedKeys : Nonempty Tacenta.SessionUnitT1.DerivedKeysModel
  Tacenta.UnitLifecycleDecryptScreen.DecryptHypotheses.agreements : DecryptRatchetAgreements oracle.braidKem
  Tacenta.UnitLifecycleDecryptScreen.DecryptHypotheses.invariant : real.invariant = ok true
  Tacenta.UnitLifecycleDecryptScreen.DecryptHypotheses.related : SessionRefines dh oracle.braidKem real model
  Tacenta.UnitLifecycleDecryptScreen.DecryptHypotheses.headroom : Tacenta.UnitLifecycleT1.DecryptRatchetHeadroom real
  Tacenta.UnitLifecycleDecryptScreen.DecryptHypotheses.trace_eq : trace rng = oracle.draws
  Tacenta.UnitLifecycleDecryptScreen.DecryptHypotheses.run : DecryptRatchetRun view oracle trace real model message rng
constructor:
  Tacenta.UnitLifecycleDecryptScreen.DecryptHypotheses.mk {R : Type} {rngCore : rand_core_1.RngCore R}
    {cryptoRng : rand_core_1.CryptoRng R} {trace : R → List Model.Lifecycle.Key} {dh : DhView}
    {view : Model.Lifecycle.CodewordView} {oracle : Model.Lifecycle.Oracle} {real : lifecycle.Session}
    {model : Model.Lifecycle.Session} {message : Slice U8} {rng : R}
    (oracleOf : DecryptOracleOf rngCore cryptoRng dh trace oracle) (codec : DhCodecOf dh)
    (contracts : Tacenta.UnitLifecycleT1.DecryptRatchetContracts rngCore)
    (derivedKeys : Nonempty Tacenta.SessionUnitT1.DerivedKeysModel)
    (agreements : DecryptRatchetAgreements oracle.braidKem) (invariant : real.invariant = ok true)
    (related : SessionRefines dh oracle.braidKem real model)
    (headroom : Tacenta.UnitLifecycleT1.DecryptRatchetHeadroom real) (trace_eq : trace rng = oracle.draws)
    (run : DecryptRatchetRun view oracle trace real model message rng) :
    Tacenta.UnitLifecycleDecryptScreen.DecryptHypotheses rngCore cryptoRng trace dh view oracle real model message rng
-/
#guard_msgs in
#print Tacenta.UnitLifecycleDecryptScreen.DecryptHypotheses

/--
info: def Tacenta.UnitLifecycleDecryptScreen.DecryptHypothesesJointlySatisfiableStatement : Prop :=
∀ (K : Model.Braid.Kem) (dh : DhView),
  Tacenta.UnitLifecycleDecryptScreen.DecryptJointLaws K dh →
    ∃ oracle real model message rng,
      oracle.braidKem = K ∧
        (∃ decoded, tacenta_wire.decode_message message = ok (core.result.Result.Ok decoded)) ∧
          (∃ composite ciphertext,
              Model.CompositeHeader.decodeDetailed (sliceOf message) = Except.ok (composite, ciphertext)) ∧
            Model.Lifecycle.messageType (sliceOf message) = some Model.Lifecycle.MessageType.ratchet ∧
              ∀ (view : Model.Lifecycle.CodewordView),
                Tacenta.UnitLifecycleDecryptScreen.DecryptHypotheses byteRng byteCrc byteTrace dh view oracle real model
                  message rng
-/
#guard_msgs in
#print Tacenta.UnitLifecycleDecryptScreen.DecryptHypothesesJointlySatisfiableStatement
