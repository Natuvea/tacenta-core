import Translation.UnitLifecycleRestoredSession
import Translation.UnitLifecycleIntegrationScreen
import Translation.UnitLifecycleAtomicity
import Translation.UnitLifecycleRepair
import Translation.UnitOracleJoint
import Translation.UnitHeldKemWitness

/-!
# The public `Session::encrypt` at an established initiator session

`UnitLifecycleEstablishInitiatorShape` reads, off every successful `establish_initiator_for` output `s`, the
parts the session is built from, the four counter ceilings and the model session `establishedModelOf dh s`
(related by definition at the `KeysUnsampled` agreement).  This module composes those results with the
encrypt route of the dispatch layer (`UnitLifecycleT3.public_session_encrypt_of_send_contracts`, every outcome
of the public call): it composes an unfinished public root, success and refusal effects included, at a
state an actual establishment produced, and derives what the next operation on the session that sent
consumes about the session.

## The four named items

1. **Inputs and the successful result.**  For every identity, published bundle, expected identity and
   source `rng0` with `establish_initiator_for rcE crcE our bundle expected rng0 = ok (.Ok s, rng1)`, every
   plaintext of at most `Usize.max - 65770` bytes and every source state `rng` whose trace starts with two
   draws `d1`, `d2` (`trace rng = d1 :: d2 :: rest`).
2. **The model state.**  `establishedModelOf dh s`; the model step is
   `Model.Lifecycle.encrypt view oracle (establishedModelOf dh s) (sliceOf plaintext)`.
3. **The relation.**  `established_initiator_encrypt_refines`: `Session::encrypt` returns, and its result,
   its post-state and the draws it leaves refine the model's step (`PublicEncryptWitness`, so
   `StepRefines`).  `established_encrypt_outcomes` names the two outcomes and their effects:
   * key generation refuses (`K.keyGen (braidRandomness (d1 ++ d2)) = none`): the call returns
     `AgreementFailed` and the session `{ s with braid := ⟨Failed⟩ }`, nothing else changed.  This arm is
     reachable only for a model KEM whose key generation refuses; the shipping wrapper's key generation does
     not refuse, by reading (`tacenta-core/kem/src/lib.rs`, libcrux's only error there is an output buffer
     of the wrong length, which the wrapper never passes; `LIMITATIONS.md`), so at the shipping KEM this is
     a covered arm, not a reachable refusal;
   * key generation answers `(dk, ekSeed, ekVector)`: the call returns bytes equal to the model's initial
     message (`initialWire`) wrapping the first ratchet frame (`firstFrame`: classical numbers 0 and 0,
     sparse epoch 0 and number 1, agreement epoch 1 and type `hdr`), the session changes only in the Triple
     Ratchet and the agreement (so the pending initial message is kept), the agreement is `KeysSampled` at
     epoch 1, and the session relates to the model's next session, whose agreement holds `dk`, `ekVector`
     and the header encoder after one chunk.  At a `KeysSampled` agreement the relation is not
     definitional: its encoder half (provenance and simulation) is derived from the code's send under
     `ErasureAgrees`, and its key-pair half (decapsulation, vector and header agreement) is the content of
     `KeyGenSeededFor`, carried through.
   Both outcomes leave the source with the trace less its first two entries.  The terminal guard and every
   Triple refusal do not occur: the model's step at that state is computed (`established_encrypt_model_cases`,
   `established_triple_send_ok`) and has neither.
4. **What the next operation consumes.**  After a success: the four counter ceilings
   (`established_encrypt_successor_counterHeadroom`), the relation to the model step's session with the
   source's draws (`established_encrypt_successor_refines`), and `Session::invariant`
   (`established_encrypt_successor_admissible`): the session is the establishment's with the Triple after
   the send (`sentTriple`, recovered from the relation by `triple_eq_sent`) and the agreement at
   `KeysSampled` epoch 1, whose key pair has the header key generation returned (so `key_pair_valid`) and
   whose encoder is `Encoder::new` of that header and its MAC advanced once (so `Encoder::invariant` and
   `encoder_sized`).  `established_encrypt_successor_hypotheses` collects the session-side premises of the
   `decrypt` refinement at that session: invariant, relation and ceilings (and `HonestChunk`, which is
   `True` at a `keysSampled` agreement).  `established_encrypt_successor_shape` states the session exactly:
   the establishment's, with `sentTriple` (classical counter 1, sparse send counter 1, receive counter 0,
   clock 0, sparse epoch 0) and the agreement `KeysSampled 1` with the establishment's authenticator.

## The law, and the other premises

`KeyGenSeededFor K rc crc trace` (assumed; `KeyGenSeededForShape` at the real constants): from every source
state whose trace holds two draws, `IncrementalKeyPair::generate` leaves the trace without them and answers as
`K.keyGen` does at their little-endian value, two-sided, with the key pair's header, vector and
decapsulation agreeing with the model's.  It is the key-generation clause of `KemAgreesFor` with the
randomness fixed to the draws the model counts (`braidSendDrawCount`), so the counted draw record of the
dispatch layer is derived (`braidSendTraceCounted_established`), through a copy of the `KeysUnsampled` branch
of `step_send_refines` at that randomness (`step_send_keysUnsampled_pinned`).

The successor's invariant takes six more: the establishment's `DhPublicValid` and `OptionEqU64Shape` (as
for the establishment output), the KEM agreements `KemLenAgrees` and `ValidateEkAgrees` at `oracle.braidKem`
(both already premises of the `decrypt` refinement), `DivCeilValue`, and a size law of the model KEM,
`KeyGenSizesOf` (assumed: its key generation returns a 32-byte seed and a vector of `ekSize` bytes, and its
hash is 32 bytes).

The other premises are the caller's: the encrypt boundary records (`BraidSendRefinementContracts` at
`oracle.braidKem`, `TripleSendRefinementContracts`, `AeadSealBounded`, `DhCodecTotal`, the class
`DerivedKeysModel`), the oracle record `OracleOf`, `DhCodecOf`, `CodewordViewSendOf`, three `zeroize` round
trips, `KemCiphertextLenOf` and `KemCiphertextLenBound` (for the headroom record, with `DhCodecTotal` for the
66 bytes of associated data: `encryptHeadroom_established`), the trace equation and the two draws.

## Together, and not vacuously

`EstablishedEncryptHypotheses` is the premise list as one record and `EstablishedEncryptHypotheses.refines`
applies the theorem to it.  `established_encrypt_hypotheses_jointly_satisfiable`: at the real constants, under
the decrypt laws, the initiator contract axioms, `InitiatorSuccessShape`, `DhPublicValid`, `KemCiphertextLenOf`
and the extra laws `EncryptExtraLaws` (the laws `OracleOf` is derived from, the axiom part of the encrypt
contract record, the key-generation law at the byte-stream source, the message-key round trip and the
ciphertext bound), every field holds at once, for every identity and every byte-stream source of at least 64
bytes.  `established_encrypt_laws_model`: all of those laws, with the decrypt, establishment and restored-session
laws, hold in one interpretation, `InterpO.modelEncrypt` (`Interp.modelEstablished` with key generation that
fills one 64-byte seed and encapsulation that fills one 32-byte buffer), at the toy KEM `toyKemR`, which
refuses key generation at the all-zero seed.  `established_encrypt_success_reachable` and
`established_encrypt_refusal_reachable`: at the real constants, under the same laws, the success arm is
reached where the model's key generation answers at the source's bytes and the refusal arm where it refuses;
in the model both happen (`toyKemR_seeds`).  For the successor, `EstablishedEncryptSuccessorHypotheses`,
`established_encrypt_successor_hypotheses_jointly_satisfiable` (adding `KeyGenSizesOf K`) and
`established_encrypt_successor_reachable` (a success whose session passes the invariant and meets the
ceilings) do the same; `toyKemR_sizes` is the size law in the model.  The models are toys and show nothing
of the real primitives.

## What it does not show

* The responder's receipt of the frame (`establish_responder`), initial-frame `decrypt`, a second `encrypt`.
* That `establishedModelOf dh s` is the model's own establishment output.
* That the real primitives meet the boundary records, `OracleOf`'s laws, `KeyGenSeededFor` or the KEM
  agreements.  `KeyGenSizesOf` holds at the KEM model read off the wrapper under the wrapper laws
  (`keyGenSizes_wrapperKem`).
* A refusal the shipping `encrypt` can reach: at this state the only refusal is key generation refusing,
  which the shipping wrapper does not do, by reading; the terminal guard and the Triple refusals, reachable
  later in a session, do not occur here and are not covered.
* A restored copy of the session after the send (its agreement holds a key pair: outside `RestoredScope`).
* A random source with no state of its own, such as `OsRng`.
-/

namespace Tacenta.UnitLifecycleEstablishedEncrypt

open Aeneas Aeneas.Std Result
open tacenta_session_unit

/-! ## The law: key generation reads the two draws the model counts -/

section Law
open Tacenta.SessionUnitBraidT3 (vecOf sliceOf keyOf)

open Tacenta.UnitSatisfiabilityJoint (Interp Interp.real)

/-- What key generation answers from one source state `rng`, leaving `rng'`, against the model's key
generation at one randomness `rand`, over an interpretation `I`: either it returns a key pair and the
model's key generation returns a decapsulation key, a seed and a vector, with the key pair's header the seed
followed by the model's hash, its vector the model's vector and its decapsulation the model's; or it refuses
and so does the model's.  The inner clause of `KemAgreesFor`, with the randomness fixed. -/
def KeyGenAnswersShape (I : Interp) (K : Model.Braid.Kem) {R : Type} (rc : rand_core_1.RngCore R)
    (crc : rand_core_1.CryptoRng R) (rng : R) (rand : Nat) (rng' : R) : Prop :=
  (∃ kp dk ekSeed ekVector,
      I.ikpGenerate rc crc rng = ok (core.result.Result.Ok kp, rng') ∧
      K.keyGen rand = some (dk, ekSeed, ekVector) ∧
      (∃ h, I.ikpHeader kp = ok h ∧ vecOf h = ekSeed ++ K.hashEk ekSeed ekVector) ∧
      (∃ v, I.ikpEkVector kp = ok v ∧ vecOf v = ekVector) ∧
      (∀ ct1 ct2 : Slice Std.U8, ct1.length = K.ct1Size → ct2.length = K.ct2Size →
        (∃ raw : Array Std.U8 32#usize,
          I.ikpDecapsulate kp ct1 ct2 = ok (core.result.Result.Ok raw) ∧
          K.decaps dk (sliceOf ct1) (sliceOf ct2) = some (keyOf raw)) ∨
        ((∃ e, I.ikpDecapsulate kp ct1 ct2 = ok (core.result.Result.Err e)) ∧
          K.decaps dk (sliceOf ct1) (sliceOf ct2) = none))) ∨
  ((∃ e, I.ikpGenerate rc crc rng = ok (core.result.Result.Err e, rng')) ∧ K.keyGen rand = none)

/-- **What key generation answers**, at the real constants: `KeyGenAnswersShape` written over the real
functions. -/
def KeyGenAnswers (K : Model.Braid.Kem) {R : Type} (rc : rand_core_1.RngCore R)
    (crc : rand_core_1.CryptoRng R) (rng : R) (rand : Nat) (rng' : R) : Prop :=
  (∃ kp dk ekSeed ekVector,
      tacenta_kem.IncrementalKeyPair.generate rc crc rng = ok (core.result.Result.Ok kp, rng') ∧
      K.keyGen rand = some (dk, ekSeed, ekVector) ∧
      (∃ h, tacenta_kem.IncrementalKeyPair.header kp = ok h ∧
        vecOf h = ekSeed ++ K.hashEk ekSeed ekVector) ∧
      (∃ v, tacenta_kem.IncrementalKeyPair.ek_vector kp = ok v ∧ vecOf v = ekVector) ∧
      Tacenta.SessionUnitBraidT3.KeyPairRefines K kp dk) ∨
  ((∃ e, tacenta_kem.IncrementalKeyPair.generate rc crc rng =
      ok (core.result.Result.Err e, rng')) ∧ K.keyGen rand = none)

/-- At the real constants the shape is `KeyGenAnswers`. -/
theorem keyGenAnswers_is (K : Model.Braid.Kem) {R : Type} (rc : rand_core_1.RngCore R)
    (crc : rand_core_1.CryptoRng R) (rng : R) (rand : Nat) (rng' : R) :
    KeyGenAnswers K rc crc rng rand rng' ↔ KeyGenAnswersShape Interp.real K rc crc rng rand rng' :=
  Iff.rfl

/-- Key generation reads the two entries the model counts from the front of the trace and answers as the
model's key generation does at their little-endian value, two-sided, leaving the trace without them, over
an interpretation `I`, a source `rc` and a trace `trace`. -/
def KeyGenSeededForShape (I : Interp) (K : Model.Braid.Kem) {R : Type} (rc : rand_core_1.RngCore R)
    (crc : rand_core_1.CryptoRng R) (trace : R → List Model.Lifecycle.Key) : Prop :=
  ∀ rng d1 d2 rest, trace rng = d1 :: d2 :: rest → ∃ rng', trace rng' = rest ∧
    KeyGenAnswersShape I K rc crc rng (Model.Lifecycle.braidRandomness (d1 ++ d2)) rng'

/-- **Assumed law** (`KeyGenSeededForShape` at the real constants): from every source state whose trace
holds two draws, `IncrementalKeyPair::generate` leaves the trace without them and answers as the model's key
generation does at their little-endian value. -/
def KeyGenSeededFor (K : Model.Braid.Kem) {R : Type} (rc : rand_core_1.RngCore R)
    (crc : rand_core_1.CryptoRng R) (trace : R → List Model.Lifecycle.Key) : Prop :=
  ∀ rng d1 d2 rest, trace rng = d1 :: d2 :: rest → ∃ rng', trace rng' = rest ∧
    KeyGenAnswers K rc crc rng (Model.Lifecycle.braidRandomness (d1 ++ d2)) rng'

/-- At the real constants the shape is the law. -/
theorem keyGenSeededFor_is (K : Model.Braid.Kem) {R : Type} (rc : rand_core_1.RngCore R)
    (crc : rand_core_1.CryptoRng R) (trace : R → List Model.Lifecycle.Key) :
    KeyGenSeededFor K rc crc trace ↔ KeyGenSeededForShape Interp.real K rc crc trace :=
  Iff.rfl

end Law

/-- **Assumed law about the model KEM**: its key generation returns a 32-byte seed and a vector of
`K.ekSize` bytes, and its hash of them is 32 bytes (the layout of an ML-KEM-1024 header: seed and hash,
32 bytes each). -/
def KeyGenSizesOf (K : Model.Braid.Kem) : Prop :=
  ∀ rand dk ekSeed ekVector, K.keyGen rand = some (dk, ekSeed, ekVector) →
    ekSeed.length = 32 ∧ ekVector.length = K.ekSize ∧ (K.hashEk ekSeed ekVector).length = 32

/-! ## The size law at the KEM model read off the wrapper -/

section WrapperSizes
open Tacenta.UnitSatisfiabilityJoint (Interp)
open Tacenta.UnitSatisfiabilityBraidAgreements
open Tacenta.SessionUnitBraidT3 (vecOf keyOf sliceOf Bytes u8)
open Tacenta.UnitKemWrapperModel

/-- **`KeyGenSizesOf` holds at the KEM model read off the wrapper**, over every interpretation that meets the
wrapper laws: a generated pair's header is 64 bytes and its vector 1536, and the model hash of the header's
first 32 bytes and the vector is the header's last 32. -/
theorem keyGenSizes_wrapperKemOf {I : Interp} (W : WrapperKemLawsShape I) :
    KeyGenSizesOf (wrapperKemOf I) := by
  intro rand dk ekSeed ekVector h
  simp only [wrapperKemOf] at h
  have hlen : (streamOf 64 rand).length = 64 := by
    simp [streamOf, bytesOf, length_leBytes]
  split at h
  · rename_i kp rest hgen
    split at h
    · rename_i hd vd hh hv
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl, rfl⟩ := h
      obtain ⟨h', v', hh', hhl, hv', hvl, hval, -⟩ := W.generatedKeyPair _ kp rest hlen hgen
      rw [hh] at hh'; obtain rfl : hd = h' := Result.ok.inj hh'
      rw [hv] at hv'; obtain rfl : vd = v' := Result.ok.inj hv'
      have hvl' : (vecSlice vd).length = 1536 := hvl
      have hhl' : (vecOf hd).length = 64 := by simpa [vecOf] using hhl
      have htk : ((vecOf hd).take 32).length = 32 := by simp [hhl']
      have hdr : ((vecOf hd).drop 32).length = 32 := by simp [hhl']
      have hval' : I.validateEk (bytesSlice ((vecOf hd).take 32 ++ (vecOf hd).drop 32)) (vecSlice vd) =
          ok true := by
        rw [List.take_append_drop, ← sliceOf_vecSlice, bytesSlice_sliceOf]; exact hval
      have heq := hashEkOf_eq W htk hdr hvl' hval'
      refine ⟨htk, ?_, ?_⟩
      · show (vecOf vd).length = 1536
        simpa [vecOf] using hvl
      · show (hashEkOf I ((vecOf hd).take 32) (vecOf vd)).length = 32
        rw [← sliceOf_vecSlice vd, heq]; exact hdr
    · simp at h
  · simp at h

/-- **`KeyGenSizesOf wrapperKem`**, at the real constants, under the wrapper laws. -/
theorem keyGenSizes_wrapperKem (W : WrapperKemLaws) : KeyGenSizesOf wrapperKem :=
  keyGenSizes_wrapperKemOf W

end WrapperSizes

/-! ## The Braid send from `KeysUnsampled` at a fixed randomness

`SessionUnitBraidT3.step_send_refines` says that *some* randomness makes the model agree with the code's
send.  At `KeysUnsampled` the model's randomness enters only through key generation, so where the law fixes
it, the same walk gives the agreement at that randomness.  This is the `KeysUnsampled` branch of
`step_send_refines` with the key-generation clause taken at the given randomness. -/

section BraidPinned
open Tacenta.SessionUnitBraidT3
open tacenta_session_unit.tacenta_braid
open Tacenta.UnitLifecycleT3 (BraidSendRefinementContracts)

set_option maxHeartbeats 1000000 in
/-- **`step_send` from a `KeysUnsampled` state refines the model's send at the randomness key generation
answers to.** -/
theorem step_send_keysUnsampled_pinned {K : Model.Braid.Kem} (hea : ErasureAgrees)
    (hmac : BraidHmacAgrees) (hhdr : Tacenta.SessionUnitBraidT1.KeyPairHeaderTotal)
    {R : Type} (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R)
    (self : Braid) (state : State) (rng : R) {e : Nat} {a : Model.Braid.Auth}
    (hrel : StateRefines K state (.keysUnsampled e a)) (rand : Nat) (rng' : R)
    (hgenR : KeyGenAnswers K rc crc rng rand rng') :
    Braid.step_send rc crc self state rng ⦃ fun ((msg, out, next), _) =>
      (∀ modelMsg, (Model.Braid.send K rand (.keysUnsampled e a)).1 = some modelMsg →
          MsgRefines msg modelMsg) ∧
        ((Model.Braid.send K rand (.keysUnsampled e a)).1 = none → msg.data = none) ∧
        OptionOutputRefines out (Model.Braid.send K rand (.keysUnsampled e a)).2.2.1 ∧
        StateRefines K next (Model.Braid.send K rand (.keysUnsampled e a)).2.2.2 ∧
        (∀ e' a' kp enc, next = .KeysSampled e' a' kp enc → ∃ h,
          tacenta_kem.IncrementalKeyPair.header kp = ok h ∧ ∃ dk ekSeed ekVector,
            K.keyGen rand = some (dk, ekSeed, ekVector) ∧
            vecOf h = ekSeed ++ K.hashEk ekSeed ekVector) ⦄ := by
  rcases state with _|_|_|_|_|_|_|_|_|_|_|_ <;>
    (simp only [StateRefines] at hrel; try exact hrel.elim)
  rename_i epoch auth
  obtain ⟨he, ha⟩ := hrel
  rcases hgenR with
    ⟨kp, dk, ekSeed, ekVector, hgenkp, hkg, ⟨h, hh, hhval⟩, ⟨v, hv, hvval⟩, hdecap⟩ |
    ⟨⟨e, hgenerr⟩, hkg⟩
  swap
  · unfold Braid.step_send
    simp only [hgenerr]
    unfold Msg.empty
    step*
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro modelMsg hm; simp [Model.Braid.send, hkg] at hm
    · intro _; trivial
    · simp only [Model.Braid.send, hkg]; trivial
    · simp only [Model.Braid.send, hkg]; trivial
    · intro _ _ _ _ hnext; cases hnext
  obtain ⟨h', hh', hh'len⟩ := hhdr kp
  rw [hh] at hh'; injection hh' with hh'; subst hh'
  unfold Braid.step_send
  simp only [hgenkp]
  step*
  simp only [hh]
  step*
  have hsliceh : sliceOf h.deref = ekSeed ++ K.hashEk ekSeed ekVector := by
    simp [sliceOf, alloc.vec.Vec.deref, vecOf] at hhval ⊢; exact hhval
  step with Auth.mac_hdr_refines hmac auth epoch h.deref _ hsliceh
    (by simp [alloc.vec.Vec.deref]; scalar_tac)
  step*
  obtain ⟨hdr_enc, hdr_enc_eq, hdr_enc_sim⟩ := hea.1 header1.deref
  simp only [hdr_enc_eq]
  have hencR : EncoderRefines hdr_enc
      (Model.Braid.encode (sliceOf header1.deref)) := hdr_enc_sim
  have hlt : (Model.Braid.encode (sliceOf header1.deref)).next < 65536 := by
    simp [Model.Braid.encode]
  obtain ⟨chunk0, hdr_enc1_0, hnc_eq, hidx0, hsimtail⟩ := hencR.2 1 (by omega)
  have hstep0 := EncoderRefines.step hencR hlt hnc_eq
  step*
  simp only [hnc_eq]
  unfold Msg.with
  step*
  have hheader1val : sliceOf header1.deref =
      (ekSeed ++ K.hashEk ekSeed ekVector) ++
        (AuthOf auth).macHdr epoch.val (ekSeed ++ K.hashEk ekSeed ekVector) := by
    simp only [sliceOf, alloc.vec.Vec.deref] at header1_post ⊢
    simp only [header1_post, s1_post, List.map_append]
    simp only [sliceOf, alloc.vec.Vec.deref] at hsliceh
    rw [hsliceh]
    congr 1
  rw [he, ha] at hheader1val
  rw [hheader1val] at hencR
  have hmsg_ex : (Model.Braid.send K rand (Model.Braid.BraidState.keysUnsampled e a)).1 =
      some ⟨e, Model.Braid.MsgType.hdr,
        some (Model.Braid.encode (sliceOf header1.deref)).nextChunk.1⟩ := by
    unfold Model.Braid.send
    simp only [hkg]
    rw [← hheader1val]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro modelMsg hm; rw [hmsg_ex] at hm; injection hm with hm; subst hm
    exact ⟨he, trivial, hidx0, hstep0.2.1⟩
  · intro hnone; rw [hmsg_ex] at hnone; cases hnone
  · simp only [Model.Braid.send, hkg]; trivial
  · simp only [Model.Braid.send, hkg]
    exact ⟨he, ha, ⟨hdecap, ⟨v, hv, hvval⟩, ⟨h, _, hh, hhval⟩⟩,
      (EncoderRefines.step hencR hlt hnc_eq).2.2⟩
  · intro e' a' kp' enc' hnext
    injection hnext with _ _ hkp _
    subst hkp
    exact ⟨h, hh, dk, ekSeed, ekVector, hkg, hhval⟩

/-- **`Braid::send` from a `KeysUnsampled` state refines the model's send at the randomness key
generation answers to**: clone, the step above, the reported epoch. -/
theorem braid_send_keysUnsampled_pinned {K : Model.Braid.Kem}
    (contracts : BraidSendRefinementContracts rc K)
    {R : Type} {rc : rand_core_1.RngCore R} (crc : rand_core_1.CryptoRng R)
    (self : Braid) (rng : R) {e : Nat} {a : Model.Braid.Auth}
    (hrel : StateRefines K self.state (.keysUnsampled e a)) (rand : Nat) (rng' : R)
    (hgenR : KeyGenAnswers K rc crc rng rand rng') :
    Braid.send rc crc self rng ⦃ fun ((msg, i, out, next), _) =>
      (∀ modelMsg, (Model.Braid.send K rand (.keysUnsampled e a)).1 = some modelMsg →
          MsgRefines msg modelMsg) ∧
        i.val = (Model.Braid.send K rand (.keysUnsampled e a)).2.2.2.epoch - 1 ∧
        OptionOutputRefines out (Model.Braid.send K rand (.keysUnsampled e a)).2.2.1 ∧
        StateRefines K next.state (Model.Braid.send K rand (.keysUnsampled e a)).2.2.2 ∧
        (∀ e' a' kp enc, next.state = .KeysSampled e' a' kp enc → ∃ h,
          tacenta_kem.IncrementalKeyPair.header kp = ok h ∧ ∃ dk ekSeed ekVector,
            K.keyGen rand = some (dk, ekSeed, ekVector) ∧
            vecOf h = ekSeed ++ K.hashEk ekSeed ekVector) ⦄ := by
  unfold Braid.send
  step with State.clone_refines contracts.kemClone contracts.erasureClone contracts.encoderClone
    contracts.decoderClone contracts.keyPairClone contracts.encapsStateClone hrel
  step with step_send_keysUnsampled_pinned contracts.hea contracts.hmac contracts.header rc crc self s
    rng s_post rand rng' hgenR
  obtain ⟨hmsg, -, hout, hnext, htie⟩ := ‹_›
  step with Braid.reported_refines K { state := next } _ hnext
  exact ⟨hmsg, i_post, hout, hnext, htie⟩

end BraidPinned

open Tacenta.UnitLifecycleT3
open Tacenta.UnitLifecycleEstablishInitiatorShape
open Tacenta.UnitLifecycleDecryptRatchetT3 (DecryptRatchetAgreements)
open Tacenta.UnitSatisfiabilityJoint (Interp Interp.real)

/-! ## The counted draw record at a `KeysUnsampled` state -/

/-- At a `keysUnsampled` model Braid the send has no output, in both arms. -/
theorem send_keysUnsampled_output (K : Model.Braid.Kem) (rand e : Nat) (a : Model.Braid.Auth) :
    (Model.Braid.send K rand (.keysUnsampled e a)).2.2.1 = none := by
  simp only [Model.Braid.send]
  split <;> rfl

/-- At a `keysUnsampled` model Braid the lifecycle's agreement send has no output. -/
theorem sendAgreement_keysUnsampled_output (oracle oracleNext : Model.Lifecycle.Oracle) (e : Nat)
    (a : Model.Braid.Auth) (message : Option Model.Braid.Msg) (epoch : Nat)
    (output : Option Model.Braid.Output) (next : Model.Braid.BraidState)
    (h : Model.Lifecycle.sendAgreement oracle (.keysUnsampled e a) =
      some ((message, epoch, output, next), oracleNext)) :
    output = none := by
  simp only [Model.Lifecycle.sendAgreement, Model.Lifecycle.braidSendNeedsDraw, if_true,
    Option.bind_eq_bind] at h
  rcases ht : Model.Lifecycle.takeDraws (Model.Lifecycle.braidSendDrawCount
    (.keysUnsampled e a)) oracle with _ | ⟨draws, rest⟩ <;> rw [ht] at h
  · simp at h
  · simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
    have h1 := congrArg (fun x => x.2.2.1) h.1
    simp only at h1
    rw [← h1]
    exact send_keysUnsampled_output _ _ _ _

/-- A two-element list, from its length. -/
theorem two_of_length {α : Type} (l : List α) (h : l.length = 2) : ∃ x y, l = [x, y] := by
  match l, h with
  | [x, y], _ => exact ⟨x, y, rfl⟩

/-- **The counted draw record of the dispatch layer holds at every session whose Braid is `KeysUnsampled`**,
with the model Braid read off it, under the Braid send record, the law and two draws left: the send reads
the two draws key generation reads, and the model's send at their value is related to the code's. -/
theorem braidSendTraceCounted_of_keysUnsampled {R : Type} {rc : rand_core_1.RngCore R}
    {crc : rand_core_1.CryptoRng R} {trace : R → List Model.Lifecycle.Key} {K : Model.Braid.Kem}
    {oracle : Model.Lifecycle.Oracle} {real : lifecycle.Session} {model : Model.Lifecycle.Session}
    {rng : R} (contracts : BraidSendRefinementContracts rc K) (hgen : KeyGenSeededFor K rc crc trace)
    (hkem : oracle.braidKem = K) (epoch : Std.U64) (auth : tacenta_braid.Auth)
    (hreal : real.braid.state = .KeysUnsampled epoch auth)
    (hmodel : model.braid = .keysUnsampled epoch.val (Tacenta.SessionUnitBraidT3.AuthOf auth))
    (hdraws : ∃ d1 d2 rest, trace rng = d1 :: d2 :: rest) :
    BraidSendTraceAgreementCounted rc crc trace K oracle real model rng where
  encodersLive := by
    intro enc henc
    rw [hmodel] at henc
    simp [Tacenta.SessionUnitBraidT3.EncoderOf] at henc
  braidKem := hkem
  noDrawTrace := by
    intro _ _ _ _ _ _ hneeds
    rw [hmodel] at hneeds
    simp [Model.Lifecycle.braidSendNeedsDraw] at hneeds
  drawTrace := by
    intro m ep o b rngNext hsend _
    obtain ⟨d1, d2, rest, htr⟩ := hdraws
    obtain ⟨rng', htr', hans⟩ := hgen rng d1 d2 rest htr
    obtain ⟨r, hg⟩ := Tacenta.UnitLifecycleIntegrationScreen.braid_send_keysUnsampled_generate rc crc
      real.braid epoch auth hreal rng rngNext _ hsend
    have hnext : rngNext = rng' := by
      rcases hans with ⟨kp, -, -, -, hgk, -⟩ | ⟨⟨e, hgk⟩, -⟩ <;>
        · rw [hgk] at hg
          exact (congrArg Prod.snd (Result.ok.inj hg)).symm
    refine ⟨[d1, d2], rest, ?_, by simpa using htr, by rw [hnext]; exact htr'⟩
    rw [hmodel]; rfl
  drawPost := by
    intro m ep o b rngNext hsend _ draws rest hlen htr
    rw [hmodel] at hlen
    obtain ⟨d1, d2, rfl⟩ := two_of_length draws hlen
    obtain ⟨rng', -, hans⟩ := hgen rng d1 d2 rest (by simpa using htr)
    have hrel : Tacenta.SessionUnitBraidT3.StateRefines K real.braid.state
        (.keysUnsampled epoch.val (Tacenta.SessionUnitBraidT3.AuthOf auth)) := by
      rw [hreal]; exact ⟨rfl, rfl⟩
    obtain ⟨result, hcall, hpost⟩ := Std.WP.spec_imp_exists
      (braid_send_keysUnsampled_pinned contracts crc real.braid rng hrel
        (Model.Lifecycle.braidRandomness (d1 ++ d2)) rng' hans)
    have heq : result = ((m, ep, o, b), rngNext) := Result.ok.inj (hcall.symm.trans hsend)
    subst heq
    refine ⟨Model.Lifecycle.braidRandomness (d1 ++ d2), by simp, ?_⟩
    rw [hmodel]
    exact ⟨hpost.1, hpost.2.1, hpost.2.2.1, hpost.2.2.2.1⟩

/-- **The counted draw record at every successful `establish_initiator_for` output**, with the model session
`establishedModelOf dh s`. -/
theorem braidSendTraceCounted_established {R E : Type} {rc : rand_core_1.RngCore R}
    {crc : rand_core_1.CryptoRng R} {trace : R → List Model.Lifecycle.Key} (dh : DhView)
    {oracle : Model.Lifecycle.Oracle} (contracts : BraidSendRefinementContracts rc oracle.braidKem)
    (hgen : KeyGenSeededFor oracle.braidKem rc crc trace)
    (rcE : rand_core_1.RngCore E) (crcE : rand_core_1.CryptoRng E)
    (our : lifecycle.Identity) (bundle : lifecycle.PublishedBundle)
    (expected : tacenta_boundary.dh.PublicKeyBytes) (rng0 rng1 : E) (s : lifecycle.Session)
    (h : lifecycle.establish_initiator_for rcE crcE our bundle expected rng0 =
      ok (core.result.Result.Ok s, rng1))
    (rng : R) (hdraws : ∃ d1 d2 rest, trace rng = d1 :: d2 :: rest) :
    BraidSendTraceAgreementCounted rc crc trace oracle.braidKem oracle s (establishedModelOf dh s)
      rng := by
  obtain ⟨p, rfl⟩ := establish_initiator_for_parts rcE crcE our bundle expected rng0 rng1 s h
  exact braidSendTraceCounted_of_keysUnsampled contracts hgen rfl 1#u64 p.auth rfl rfl hdraws

/-! ## The headroom record -/

open Tacenta.UnitLifecycleRestoredSession (KemCiphertextLenBound)

/-- The associated data of a successful output is 66 bytes, under `DhCodecTotal`. -/
theorem identityAd_length_parts (hdh : Tacenta.UnitLifecycleT1.DhCodecTotal) {R : Type}
    {rc : rand_core_1.RngCore R} {crc : rand_core_1.CryptoRng R} {our : lifecycle.Identity}
    {bundle : lifecycle.PublishedBundle} (p : InitiatorOutputParts rc crc our bundle) :
    p.identityAd.val.length = 66 := by
  obtain ⟨ad, hcall, hlen⟩ := Std.WP.spec_imp_exists
    (Tacenta.UnitLifecycleT1.identity_ad_length hdh p.ourPublic bundle.bundle.identity_key)
  rw [p.hIdentityAd] at hcall
  cases hcall
  exact hlen

/-- The pending ciphertext of a successful output is at most 65536 bytes, under `KemCiphertextLenOf` and
`KemCiphertextLenBound`. -/
theorem kemCiphertext_length_parts (hct : KemCiphertextLenOf) (hbound : KemCiphertextLenBound)
    {R : Type} {rc : rand_core_1.RngCore R} {crc : rand_core_1.CryptoRng R} {our : lifecycle.Identity}
    {bundle : lifecycle.PublishedBundle} (p : InitiatorOutputParts rc crc our bundle) :
    p.kemCiphertext.val.length ≤ 65536 := by
  obtain ⟨n, hn, hlen⟩ := (kemCiphertextLenOf_is.mp hct) rc crc _ _ _ _ _ p.hEncapsulate
  obtain ⟨n', hn', hle⟩ := hbound
  rw [hn] at hn'
  cases hn'
  omega

/-- **`EncryptHeadroom` at the session the parts make**, for every plaintext of at most
`Usize.max - 65770` bytes: one chain entry, 66 bytes of associated data, a ciphertext of at most 65536
bytes. -/
theorem encryptHeadroom_parts (hdh : Tacenta.UnitLifecycleT1.DhCodecTotal) (hct : KemCiphertextLenOf)
    (hbound : KemCiphertextLenBound) {R : Type} {rc : rand_core_1.RngCore R}
    {crc : rand_core_1.CryptoRng R} {our : lifecycle.Identity} {bundle : lifecycle.PublishedBundle}
    (p : InitiatorOutputParts rc crc our bundle) (plaintext : Slice Std.U8)
    (hroom : plaintext.val.length + 65770 ≤ Usize.max) :
    Tacenta.UnitLifecycleT1.EncryptHeadroom p.session plaintext := by
  have hu : 4294967295 ≤ Usize.max :=
    Tacenta.SessionUnitSessionT1.small_le_usize_max (le_refl _)
  have had := identityAd_length_parts hdh p
  have hkc := kemCiphertext_length_parts hct hbound p
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [InitiatorOutputParts.session, initiatorTriple, initChains,
      Tacenta.UnitHeadroomSatisfiable.vecOf]
    omega
  · simp only [InitiatorOutputParts.session]; omega
  · omega
  · simp only [InitiatorOutputParts.session]; omega

/-- **`EncryptHeadroom` at every successful `establish_initiator_for` output**, for every plaintext of at
most `Usize.max - 65770` bytes, under `DhCodecTotal`, `KemCiphertextLenOf` and `KemCiphertextLenBound`. -/
theorem encryptHeadroom_established (hdh : Tacenta.UnitLifecycleT1.DhCodecTotal)
    (hct : KemCiphertextLenOf) (hbound : KemCiphertextLenBound) {E : Type}
    (rcE : rand_core_1.RngCore E) (crcE : rand_core_1.CryptoRng E)
    (our : lifecycle.Identity) (bundle : lifecycle.PublishedBundle)
    (expected : tacenta_boundary.dh.PublicKeyBytes) (rng0 rng1 : E) (s : lifecycle.Session)
    (h : lifecycle.establish_initiator_for rcE crcE our bundle expected rng0 =
      ok (core.result.Result.Ok s, rng1))
    (plaintext : Slice Std.U8) (hroom : plaintext.val.length + 65770 ≤ Usize.max) :
    Tacenta.UnitLifecycleT1.EncryptHeadroom s plaintext := by
  obtain ⟨p, rfl⟩ := establish_initiator_for_parts rcE crcE our bundle expected rng0 rng1 s h
  exact encryptHeadroom_parts hdh hct hbound p plaintext hroom

/-! ## The two Triple condition records -/

/-- The five finite-store facts both Triple condition records ask for, at the model session of the parts:
one chain entry at epoch 0 with both counters 0, no stored key, sparse epoch 0. -/
theorem tripleStoreFacts_parts (dh : DhView) {R : Type} {rc : rand_core_1.RngCore R}
    {crc : rand_core_1.CryptoRng R} {our : lifecycle.Identity} {bundle : lifecycle.PublishedBundle}
    (p : InitiatorOutputParts rc crc our bundle) :
    (establishedModelOf dh p.session).triple.postQuantum.chains.length + 1 < Usize.max ∧
    (∀ q ∈ (establishedModelOf dh p.session).triple.postQuantum.chains,
      q.1 + Model.SparseRatchet.epochsKept ≤ Std.U64.max) ∧
    (∀ sk ∈ (establishedModelOf dh p.session).triple.postQuantum.skipped,
      sk.1 + Model.SparseRatchet.epochsKept ≤ Std.U64.max) ∧
    (establishedModelOf dh p.session).triple.postQuantum.epoch + 1 < Std.U64.max ∧
    (∀ q ∈ (establishedModelOf dh p.session).triple.postQuantum.chains,
      ∀ ch : Model.SparseRatchet.Chain,
      (q.2.send = some ch ∨ q.2.receive = some ch) → ch.n < Std.U64.max) := by
  have hu : 4294967295 ≤ Usize.max :=
    Tacenta.SessionUnitSessionT1.small_le_usize_max (le_refl _)
  simp [establishedModelOf, InitiatorOutputParts.session, initiatorTriple, initChains,
    Tacenta.UnitHeadroomSatisfiable.vecOf, Tacenta.SessionUnitTripleT3.spqrAbs,
    Tacenta.SessionUnitSpqrT3.chainsEntryOf, Tacenta.SessionUnitSpqrT3.chainsOf,
    Tacenta.SessionUnitSpqrT3.chainOf, Model.SparseRatchet.epochsKept, U64.max_eq]
  refine ⟨by omega, ?_⟩
  rintro ch (h | h) <;> subst h <;> simp

/-- The sparse output the generated `encrypt` hands the Triple at a `keysUnsampled` model Braid is `none`:
the model's send there has no output, so the code's has none. -/
theorem sparseOutput_none_of_evidence {R : Type} {rc : rand_core_1.RngCore R}
    {crc : rand_core_1.CryptoRng R} {trace : R → List Model.Lifecycle.Key} {dh : DhView}
    {K : Model.Braid.Kem} {oracle : Model.Lifecycle.Oracle} {real : lifecycle.Session}
    {model : Model.Lifecycle.Session} {rng : R} {realMessage : tacenta_braid.Msg}
    {realEpoch : Std.U64} {realOutput : Option tacenta_braid.Output}
    {realBraidNext : tacenta_braid.Braid} {rngNext : R}
    {sparseOutput : Option tacenta_spqr.Output} (e : Nat) (a : Model.Braid.Auth)
    (hmodel : model.braid = .keysUnsampled e a)
    (hsparse : RealSparseConversion realOutput sparseOutput)
    (hevidence : Nonempty (GeneratedBraidSuccessEvidence rc crc trace dh K oracle real model rng
      realMessage realEpoch realOutput realBraidNext rngNext)) :
    sparseOutput = none := by
  obtain ⟨ev⟩ := hevidence
  have hsend := ev.modelSend
  rw [hmodel] at hsend
  have hout := sendAgreement_keysUnsampled_output _ _ _ _ _ _ _ _ hsend
  have hreal : realOutput = none := by
    have h := ev.output
    rw [hout] at h
    cases realOutput with
    | none => rfl
    | some o => exact h.elim
  cases hsparse with
  | none => rfl
  | some _ _ hsome _ => rw [hreal] at hsome; cases hsome

/-- **The providers of the route at every successful output**: both Triple condition records, for every
generated run, from the parts and the Braid evidence. -/
theorem encryptProviders_established [Tacenta.SessionUnitT1.DerivedKeysModel] {R E : Type}
    {rc : rand_core_1.RngCore R} {crc : rand_core_1.CryptoRng R}
    {trace : R → List Model.Lifecycle.Key} (dh : DhView) (kem : KemView) (K : Model.Braid.Kem)
    (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
    (rcE : rand_core_1.RngCore E) (crcE : rand_core_1.CryptoRng E)
    (our : lifecycle.Identity) (bundle : lifecycle.PublishedBundle)
    (expected : tacenta_boundary.dh.PublicKeyBytes) (rng0 rng1 : E) (s : lifecycle.Session)
    (h : lifecycle.establish_initiator_for rcE crcE our bundle expected rng0 =
      ok (core.result.Result.Ok s, rng1))
    (plaintext : Slice Std.U8) (rng : R) :
    Nonempty (EncryptNonterminalRouteProviders rc crc trace dh kem K view oracle s
      (establishedModelOf dh s) plaintext rng) := by
  obtain ⟨p, rfl⟩ := establish_initiator_for_parts rcE crcE our bundle expected rng0 rng1 s h
  obtain ⟨hroom, hcb, hsb, hepoch, hcounter⟩ := tripleStoreFacts_parts dh p
  have hmodel : (establishedModelOf dh p.session).braid =
      .keysUnsampled (1#u64 : Std.U64).val (Tacenta.SessionUnitBraidT3.AuthOf p.auth) := rfl
  exact ⟨{
    refusal := fun _ _ _ _ _ _ _ _ _ _ _ hsparse _ hev =>
      { derivedKeys := inferInstance, room := hroom, chainBound := hcb, skippedBound := hsb
        newBound := by
          intro o ho
          rw [sparseOutput_none_of_evidence _ _ hmodel hsparse hev] at ho
          cases ho
        epochBound := hepoch, counterBound := hcounter }
    success := fun _ _ _ _ _ _ _ _ _ _ _ _ hsparse _ hev =>
      { derivedKeys := inferInstance, room := hroom, chainBound := hcb, skippedBound := hsb
        newBound := by
          intro o ho
          rw [sparseOutput_none_of_evidence _ _ hmodel hsparse hev] at ho
          cases ho
        epochBound := hepoch, counterBound := hcounter } }⟩

/-! ## The public `Session::encrypt` at the established state -/

/-- **The public `Session::encrypt` at every successful `establish_initiator_for` output refines
`Model.Lifecycle.encrypt` at `establishedModelOf dh s`**, for every plaintext of at most
`Usize.max - 65770` bytes and every source state whose trace holds two draws: the call returns, and its
result, its post-state and the draws it leaves refine the model's step.  Under the encrypt boundary records,
the oracle record, `KeyGenSeededFor`, `KemCiphertextLenOf`, `KemCiphertextLenBound` and the trace
equation. -/
theorem established_initiator_encrypt_refines [Tacenta.SessionUnitT1.DerivedKeysModel] {R E : Type}
    (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView) (kem : KemView)
    (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
    (braid : BraidSendRefinementContracts rc oracle.braidKem) (triple : TripleSendRefinementContracts)
    (aead : Tacenta.UnitLifecycleT1.AeadSealBounded) (dhCodec : Tacenta.UnitLifecycleT1.DhCodecTotal)
    (oracleOf : OracleOf rc crc dh kem trace oracle) (codec : DhCodecOf dh)
    (codewordView : CodewordViewSendOf view)
    (hz80 : Tacenta.SessionUnitT3.ZeroizingRoundTrips80)
    (hz32 : ZeroizingRoundTrips (Array Std.U8 32#usize))
    (hzKeys : ZeroizingRoundTrips
      (Array Std.U8 32#usize × Array Std.U8 32#usize × Array Std.U8 16#usize))
    (hgen : KeyGenSeededFor oracle.braidKem rc crc trace) (hct : KemCiphertextLenOf)
    (hbound : KemCiphertextLenBound)
    (rcE : rand_core_1.RngCore E) (crcE : rand_core_1.CryptoRng E)
    (our : lifecycle.Identity) (bundle : lifecycle.PublishedBundle)
    (expected : tacenta_boundary.dh.PublicKeyBytes) (rng0 rng1 : E) (s : lifecycle.Session)
    (h : lifecycle.establish_initiator_for rcE crcE our bundle expected rng0 =
      ok (core.result.Result.Ok s, rng1))
    (plaintext : Slice Std.U8) (hroom : plaintext.val.length + 65770 ≤ Usize.max)
    (rng : R) (htrace : trace rng = oracle.draws)
    (hdraws : ∃ d1 d2 rest, trace rng = d1 :: d2 :: rest) :
    PublicEncryptWitness rc crc trace dh oracle.braidKem view oracle s (establishedModelOf dh s)
      plaintext rng := by
  obtain ⟨providers⟩ := encryptProviders_established dh kem oracle.braidKem view oracle rcE crcE our
    bundle expected rng0 rng1 s h plaintext rng
  exact public_session_encrypt_of_send_contracts braid
    (braidSendTraceCounted_established dh braid hgen rcE crcE our bundle expected rng0 rng1 s h rng
      hdraws)
    triple aead dhCodec
    (encryptHeadroom_established dhCodec hct hbound rcE crcE our bundle expected rng0 rng1 s h
      plaintext hroom)
    oracleOf codec codewordView braid.hkdf hz80 hz32 hzKeys
    (sessionRefines_established rcE crcE dh oracle.braidKem our bundle expected rng0 rng1 s h)
    htrace providers

/-! ## The model's step at the established state -/

/-- **The model Triple's first send at the model session of the parts succeeds**, at sending epoch 0 and no
sparse output, with classical message number 0, previous chain length 0, sparse epoch 0 and sparse message
number 1; the ratchet key is the session's own. -/
theorem established_triple_send_ok (dh : DhView) {R : Type} {rc : rand_core_1.RngCore R}
    {crc : rand_core_1.CryptoRng R} {our : lifecycle.Identity} {bundle : lifecycle.PublishedBundle}
    (p : InitiatorOutputParts rc crc our bundle) :
    ∃ tripleNext header messageKey,
      Model.Triple.sendDetailed (establishedModelOf dh p.session).triple 0 none =
        .ok (tripleNext, header, messageKey) ∧
      header.dr.dh = (establishedModelOf dh p.session).triple.classical.dhsPub ∧
      header.dr.n = 0 ∧ header.dr.pn = 0 ∧ header.epoch = 0 ∧ header.pqN = 1 := by
  simp [Model.Triple.sendDetailed, Model.Ratchet.sendDetailed, Model.SparseRatchet.sendDetailed,
    Model.SparseRatchet.maybeAdvanceDetailed, Model.SparseRatchet.findChains, establishedModelOf,
    InitiatorOutputParts.session, initiatorTriple, initChains, Tacenta.UnitHeadroomSatisfiable.vecOf,
    Tacenta.SessionUnitTripleT3.ratchetAbs, Tacenta.SessionUnitTripleT3.spqrAbs,
    Tacenta.SessionUnitSpqrT3.chainsEntryOf, Tacenta.SessionUnitSpqrT3.chainsOf,
    Tacenta.SessionUnitSpqrT3.chainOf, Model.State.u32Max, Model.SparseRatchet.u64Max]

/-- The composite header of the first ratchet frame from a model session `m` whose Braid emits `chunk`:
the session's ratchet key, classical numbers 0 and 0, sparse epoch 0 and message number 1, agreement epoch
1, agreement type `hdr`, the chunk as the view sends it from `m`'s Braid. -/
def firstComposite (view : Model.Lifecycle.CodewordView) (m : Model.Lifecycle.Session)
    (chunk : Model.Braid.Chunk) : Model.CompositeHeader.Composite :=
  { dh := m.triple.classical.dhsPub
    pn := UInt32.ofNat 0
    n := UInt32.ofNat 0
    pqEpoch := UInt64.ofNat 0
    pqN := UInt64.ofNat 1
    agEpoch := UInt64.ofNat 1
    agType := .hdr
    agChunk := some (view.send m.braid chunk) }

/-- The first ratchet frame: the composite header and the sealed plaintext under the message key, with the
session's associated data and the encoded header. -/
def firstFrame (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
    (m : Model.Lifecycle.Session) (plaintext : Model.Lifecycle.Bytes) (messageKey : Model.Lifecycle.Key)
    (chunk : Model.Braid.Chunk) : Model.Lifecycle.Bytes :=
  Model.CompositeHeader.encodeMessage (firstComposite view m chunk)
    (oracle.aeadSeal (Model.State.messageKeys messageKey .tacenta).1
      (Model.State.messageKeys messageKey .tacenta).2.1
      (Model.State.messageKeys messageKey .tacenta).2.2 plaintext
      (Model.Messages.concatAd m.identityAd
        (Model.CompositeHeader.encode (firstComposite view m chunk))))

/-- The initial message wrapping a ratchet frame, with the pending initial fields of a model session. -/
def initialWire (m : Model.Lifecycle.Session) (pending : Model.Lifecycle.PendingInitial)
    (frame : Model.Lifecycle.Bytes) : Model.Lifecycle.Bytes :=
  Model.Messages.encodeInitial
    (Model.PersistedState.SessionState.encodeEc m.ourIdentityPublic)
    (Model.PersistedState.SessionState.encodeEc pending.ephemeralPublic)
    pending.kemCiphertext (UInt32.ofNat pending.signedPrekeyId)
    (UInt32.ofNat pending.oneTimePrekeyId) (UInt32.ofNat pending.kemPrekeyId) frame

/-- **The model's `encrypt` at the model session of the parts has two outcomes**, for every codeword view,
oracle and plaintext, when the oracle holds two draws: it consumes both, and either the model's key
generation refuses at their little-endian value, and the step refuses `agreementFailed` with the Braid
committed in `failed` and nothing else changed; or it answers, and the step returns the initial message
wrapping the first ratchet frame, with the Triple advanced, the Braid at `keysSampled` holding the
decapsulation key, the vector and the header encoder after one chunk, and the pending initial message
kept. -/
theorem established_encrypt_model_cases (dh : DhView) (view : Model.Lifecycle.CodewordView)
    (oracle : Model.Lifecycle.Oracle) {R : Type} {rc : rand_core_1.RngCore R}
    {crc : rand_core_1.CryptoRng R} {our : lifecycle.Identity} {bundle : lifecycle.PublishedBundle}
    (p : InitiatorOutputParts rc crc our bundle) (plaintext : Model.Lifecycle.Bytes)
    (d1 d2 : Model.Lifecycle.Key) (rest : List Model.Lifecycle.Key)
    (hdraws : oracle.draws = d1 :: d2 :: rest) :
    (Model.Lifecycle.encrypt view oracle (establishedModelOf dh p.session) plaintext).oracle.draws =
      rest ∧
    ((oracle.braidKem.keyGen (Model.Lifecycle.braidRandomness (d1 ++ d2)) = none ∧
        (Model.Lifecycle.encrypt view oracle (establishedModelOf dh p.session) plaintext).result =
          .error .agreementFailed ∧
        (Model.Lifecycle.encrypt view oracle (establishedModelOf dh p.session) plaintext).session =
          { establishedModelOf dh p.session with braid := .failed }) ∨
      (∃ dk ekSeed ekVector,
        oracle.braidKem.keyGen (Model.Lifecycle.braidRandomness (d1 ++ d2)) =
          some (dk, ekSeed, ekVector) ∧
        ∃ tripleNext header messageKey chunk encoder pending,
          Model.Triple.sendDetailed (establishedModelOf dh p.session).triple 0 none =
            .ok (tripleNext, header, messageKey) ∧
          (Model.Braid.encode ((ekSeed ++ oracle.braidKem.hashEk ekSeed ekVector) ++
              (Tacenta.SessionUnitBraidT3.AuthOf p.auth).macHdr 1
                (ekSeed ++ oracle.braidKem.hashEk ekSeed ekVector))).nextChunk = (chunk, encoder) ∧
          (establishedModelOf dh p.session).pendingInitial = some pending ∧
          (Model.Lifecycle.encrypt view oracle (establishedModelOf dh p.session) plaintext).result =
            .ok (initialWire (establishedModelOf dh p.session) pending
              (firstFrame view oracle (establishedModelOf dh p.session) plaintext messageKey chunk)) ∧
          (Model.Lifecycle.encrypt view oracle (establishedModelOf dh p.session) plaintext).session =
            { establishedModelOf dh p.session with
              triple := tripleNext
              braid := .keysSampled 1 (Tacenta.SessionUnitBraidT3.AuthOf p.auth) dk ekVector
                encoder })) := by
  have hsa : Model.Lifecycle.sendAgreement oracle (establishedModelOf dh p.session).braid =
      some (Model.Braid.send oracle.braidKem (Model.Lifecycle.braidRandomness (d1 ++ d2))
          (establishedModelOf dh p.session).braid, { oracle with draws := rest }) := by
    have := Model.Lifecycle.sendAgreement_draws oracle (establishedModelOf dh p.session).braid
      [d1, d2] rest rfl rfl (by simpa using hdraws)
    simpa using this
  have hbraid : (establishedModelOf dh p.session).braid =
      .keysUnsampled 1 (Tacenta.SessionUnitBraidT3.AuthOf p.auth) := rfl
  have hready : Model.Lifecycle.agreementFailed (establishedModelOf dh p.session) = false := by
    simp [Model.Lifecycle.agreementFailed, hbraid]
  obtain ⟨tripleNext, header, messageKey, htriple, hdh, hn, hpn, hep, hpq⟩ :=
    established_triple_send_ok dh p
  rcases hkg : oracle.braidKem.keyGen (Model.Lifecycle.braidRandomness (d1 ++ d2)) with
    _ | ⟨dk, ekSeed, ekVector⟩
  · have hsend : Model.Braid.send oracle.braidKem (Model.Lifecycle.braidRandomness (d1 ++ d2))
        (establishedModelOf dh p.session).braid = (none, 0, none, .failed) := by
      rw [hbraid]; simp [Model.Braid.send, hkg]
    rw [hsend] at hsa
    have hstep := Model.Lifecycle.encrypt_braid_failure_commits view oracle
      { oracle with draws := rest } (establishedModelOf dh p.session) plaintext none 0 none .failed
      hready hsa rfl
    rw [hstep]
    exact ⟨rfl, Or.inl ⟨rfl, rfl, rfl⟩⟩
  · rcases hnc : (Model.Braid.encode ((ekSeed ++ oracle.braidKem.hashEk ekSeed ekVector) ++
        (Tacenta.SessionUnitBraidT3.AuthOf p.auth).macHdr 1
          (ekSeed ++ oracle.braidKem.hashEk ekSeed ekVector))).nextChunk with ⟨chunk, encoder⟩
    have hsend : Model.Braid.send oracle.braidKem (Model.Lifecycle.braidRandomness (d1 ++ d2))
        (establishedModelOf dh p.session).braid =
        (some ⟨1, .hdr, some chunk⟩, 0, none,
          .keysSampled 1 (Tacenta.SessionUnitBraidT3.AuthOf p.auth) dk ekVector encoder) := by
      rw [hbraid]; simp only [Model.Braid.send, hkg]; rw [hnc]; rfl
    rw [hsend, hbraid] at hsa
    obtain ⟨⟨hd, hpn', hn'⟩, hep', hpq'⟩ := header
    simp only at hdh hn hpn hep hpq
    subst hdh hn hpn hep hpq
    have hpending : (establishedModelOf dh p.session).pendingInitial =
        some (pendingInitialOf dh
          { ephemeral_public := p.ephemeralPublic, kem_ciphertext := p.kemCiphertext,
            signed_prekey_id := bundle.signed_prekey_id,
            one_time_prekey_id := bundle.one_time_prekey_id,
            kem_prekey_id := bundle.kem_prekey_id }) := rfl
    refine ⟨?_, Or.inr ⟨dk, ekSeed, ekVector, rfl, tripleNext, _, messageKey, chunk, encoder, _,
      htriple, hnc, hpending, ?_, ?_⟩⟩ <;>
      simp [Model.Lifecycle.encrypt, hready, hsa, Model.Lifecycle.braidFailed,
        Model.Lifecycle.sparseOutputOf, htriple, Model.Lifecycle.compositeOf,
        Model.Lifecycle.compositeTypeOf, hpending, initialWire, firstFrame, firstComposite, hbraid]

/-! ## The two outcomes of the real call, with their effects -/

/-- A translated Braid state related to the model's `failed` is `Failed`. -/
theorem state_failed_of_refines {K : Model.Braid.Kem} {st : tacenta_braid.State}
    (h : Tacenta.SessionUnitBraidT3.StateRefines K st .failed) : st = .Failed := by
  cases st <;> simp [Tacenta.SessionUnitBraidT3.StateRefines] at h ⊢

/-- A translated Braid state related to a model `keysSampled` state is `KeysSampled`, with the key pair's
decapsulation, vector and header agreement and the encoder's provenance. -/
theorem state_keysSampled_of_refines {K : Model.Braid.Kem} {st : tacenta_braid.State} {e : Nat}
    {a : Model.Braid.Auth} {dk ekVector : Model.Braid.Bytes} {enc : Model.Braid.Encoder}
    (h : Tacenta.SessionUnitBraidT3.StateRefines K st (.keysSampled e a dk ekVector enc)) :
    ∃ epoch auth kp encoder, st = .KeysSampled epoch auth kp encoder ∧ epoch.val = e ∧
      Tacenta.SessionUnitBraidT3.AuthOf auth = a ∧
      Tacenta.SessionUnitBraidT3.FreshKeyPairRefines K kp dk ekVector ∧
      Tacenta.SessionUnitBraidT3.EncoderRefines encoder enc := by
  cases st <;> simp [Tacenta.SessionUnitBraidT3.StateRefines] at h
  rename_i epoch auth kp encoder
  exact ⟨epoch, auth, kp, encoder, rfl, h⟩

/-- **The two outcomes of `Session::encrypt` at every successful `establish_initiator_for` output**, under
the hypotheses of `established_initiator_encrypt_refines`, for a source state whose trace starts with two
draws `d1`, `d2`.  The call returns, the source it leaves holds the trace without the two draws, and either
* the model's key generation refuses at `braidRandomness (d1 ++ d2)` and the call returns `AgreementFailed`
  with the session unchanged except that the agreement is `Failed`; or
* it answers `(dk, ekSeed, ekVector)` and the call returns bytes that are the model's initial message
  wrapping the first ratchet frame (`initialWire`, `firstFrame`), the session unchanged except for the
  Triple Ratchet and the agreement, the agreement `KeysSampled` at epoch 1, and the session related to the
  model's next session, whose agreement holds `dk`, `ekVector` and the header encoder after one chunk.

The terminal guard and every Triple refusal do not occur here: neither disjunct is one of them. -/
theorem established_encrypt_outcomes [Tacenta.SessionUnitT1.DerivedKeysModel] {R E : Type}
    (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView) (kem : KemView)
    (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
    (braid : BraidSendRefinementContracts rc oracle.braidKem) (triple : TripleSendRefinementContracts)
    (aead : Tacenta.UnitLifecycleT1.AeadSealBounded) (dhCodec : Tacenta.UnitLifecycleT1.DhCodecTotal)
    (oracleOf : OracleOf rc crc dh kem trace oracle) (codec : DhCodecOf dh)
    (codewordView : CodewordViewSendOf view)
    (hz80 : Tacenta.SessionUnitT3.ZeroizingRoundTrips80)
    (hz32 : ZeroizingRoundTrips (Array Std.U8 32#usize))
    (hzKeys : ZeroizingRoundTrips
      (Array Std.U8 32#usize × Array Std.U8 32#usize × Array Std.U8 16#usize))
    (hgen : KeyGenSeededFor oracle.braidKem rc crc trace) (hct : KemCiphertextLenOf)
    (hbound : KemCiphertextLenBound)
    (rcE : rand_core_1.RngCore E) (crcE : rand_core_1.CryptoRng E)
    (our : lifecycle.Identity) (bundle : lifecycle.PublishedBundle)
    (expected : tacenta_boundary.dh.PublicKeyBytes) (rng0 rng1 : E) (s : lifecycle.Session)
    (h : lifecycle.establish_initiator_for rcE crcE our bundle expected rng0 =
      ok (core.result.Result.Ok s, rng1))
    (plaintext : Slice Std.U8) (hroom : plaintext.val.length + 65770 ≤ Usize.max)
    (rng : R) (htrace : trace rng = oracle.draws)
    (d1 d2 : Model.Lifecycle.Key) (rest : List Model.Lifecycle.Key)
    (hdraws : trace rng = d1 :: d2 :: rest) :
    ∃ output, lifecycle.Session.encrypt rc crc s plaintext rng = ok output ∧ trace output.2.2 = rest ∧
      ((oracle.braidKem.keyGen (Model.Lifecycle.braidRandomness (d1 ++ d2)) = none ∧
          output.1 = core.result.Result.Err lifecycle.Error.AgreementFailed ∧
          output.2.1 = { s with braid := ⟨tacenta_braid.State.Failed⟩ }) ∨
        (∃ dk ekSeed ekVector,
          oracle.braidKem.keyGen (Model.Lifecycle.braidRandomness (d1 ++ d2)) =
            some (dk, ekSeed, ekVector) ∧
          ∃ bytes, output.1 = core.result.Result.Ok bytes ∧
          output.2.1 = { s with triple := output.2.1.triple, braid := output.2.1.braid } ∧
          (∃ auth kp encoder, output.2.1.braid.state = .KeysSampled 1#u64 auth kp encoder) ∧
          ∃ tripleNext messageKey chunk encoder pending a,
            (∃ header, Model.Triple.sendDetailed (establishedModelOf dh s).triple 0 none =
              .ok (tripleNext, header, messageKey)) ∧
            (establishedModelOf dh s).braid = .keysUnsampled 1 a ∧
            (Model.Braid.encode ((ekSeed ++ oracle.braidKem.hashEk ekSeed ekVector) ++
                a.macHdr 1 (ekSeed ++ oracle.braidKem.hashEk ekSeed ekVector))).nextChunk =
              (chunk, encoder) ∧
            (establishedModelOf dh s).pendingInitial = some pending ∧
            vecOf bytes = initialWire (establishedModelOf dh s) pending
              (firstFrame view oracle (establishedModelOf dh s) (sliceOf plaintext) messageKey chunk) ∧
            SessionRefines dh oracle.braidKem output.2.1
              { establishedModelOf dh s with
                triple := tripleNext
                braid := .keysSampled 1 a dk ekVector encoder })) := by
  have W := established_initiator_encrypt_refines rc crc trace dh kem view oracle braid triple aead
    dhCodec oracleOf codec codewordView hz80 hz32 hzKeys hgen hct hbound rcE crcE our bundle expected
    rng0 rng1 s h plaintext hroom rng htrace ⟨d1, d2, rest, hdraws⟩
  obtain ⟨p, rfl⟩ := establish_initiator_for_parts rcE crcE our bundle expected rng0 rng1 s h
  obtain ⟨output, hcall, hstep⟩ := W
  obtain ⟨hdr', hcases⟩ := established_encrypt_model_cases dh view oracle p (sliceOf plaintext) d1 d2
    rest (htrace.symm.trans hdraws)
  refine ⟨output, hcall, hstep.draws.trans hdr', ?_⟩
  obtain ⟨res, s', rng'⟩ := output
  have hres := hstep.result
  have hsess := hstep.session
  simp only at hres hsess hcall ⊢
  rcases hcases with ⟨hkg, hresM, hsessM⟩ |
    ⟨dk, ekSeed, ekVector, hkg, tripleNext, header, messageKey, chunk, encoder, pending, htriple, hnc,
      hpend, hresM, hsessM⟩
  · rw [hresM] at hres
    rw [hsessM] at hsess
    cases res with
    | Ok v => exact hres.elim
    | Err e =>
      have he : e = lifecycle.Error.AgreementFailed := refusalOf_injective hres
      subst he
      have hfailed := state_failed_of_refines hsess.braid
      rcases Tacenta.UnitLifecycleAtomicity.encrypt_err_leaves_state rc crc _ plaintext rng _ s' rng'
          hcall with hsame | ⟨-, b, hb, -⟩
      · subst hsame
        simp [InitiatorOutputParts.session] at hfailed
      · subst hb
        obtain ⟨bs⟩ := b
        simp only at hfailed
        subst hfailed
        exact Or.inl ⟨hkg, rfl, rfl⟩
  · rw [hresM] at hres
    rw [hsessM] at hsess
    cases res with
    | Err e => exact hres.elim
    | Ok bytes =>
      obtain ⟨epoch, auth, kp, enc, hst, hep, -, -, -⟩ := state_keysSampled_of_refines hsess.braid
      have hepoch : epoch = 1#u64 := by
        apply UScalar.eq_of_val_eq
        simpa using hep
      subst hepoch
      refine Or.inr ⟨dk, ekSeed, ekVector, hkg, bytes, rfl,
        Tacenta.UnitLifecycleAtomicity.encrypt_ok_writes rc crc _ plaintext rng bytes s' rng' hcall,
        ⟨auth, kp, enc, hst⟩, tripleNext, messageKey, chunk, encoder, pending,
        Tacenta.SessionUnitBraidT3.AuthOf p.auth, ⟨header, htriple⟩, rfl, hnc, hpend, hres, hsess⟩

/-! ## The session after a successful first send: its counter ceilings -/

/-- The model Triple after the first send at the model session of the parts: classical clock 0, sparse
epoch 0, every sparse chain counter at most 1. -/
theorem established_triple_next_counters (dh : DhView) {R : Type} {rc : rand_core_1.RngCore R}
    {crc : rand_core_1.CryptoRng R} {our : lifecycle.Identity} {bundle : lifecycle.PublishedBundle}
    (p : InitiatorOutputParts rc crc our bundle) (tripleNext : Model.Triple.State)
    (header : Model.Triple.Header) (messageKey : Model.Lifecycle.Key)
    (htriple : Model.Triple.sendDetailed (establishedModelOf dh p.session).triple 0 none =
      .ok (tripleNext, header, messageKey)) :
    tripleNext.classical.events = 0 ∧ tripleNext.postQuantum.epoch = 0 ∧
      ∀ q ∈ tripleNext.postQuantum.chains, ∀ ch : Model.SparseRatchet.Chain,
        (q.2.send = some ch ∨ q.2.receive = some ch) → ch.n ≤ 1 := by
  simp [Model.Triple.sendDetailed, Model.Ratchet.sendDetailed, Model.SparseRatchet.sendDetailed,
    Model.SparseRatchet.maybeAdvanceDetailed, Model.SparseRatchet.findChains, establishedModelOf,
    InitiatorOutputParts.session, initiatorTriple, initChains, Tacenta.UnitHeadroomSatisfiable.vecOf,
    Tacenta.SessionUnitTripleT3.ratchetAbs, Tacenta.SessionUnitTripleT3.spqrAbs,
    Tacenta.SessionUnitSpqrT3.chainsEntryOf, Tacenta.SessionUnitSpqrT3.chainsOf,
    Tacenta.SessionUnitSpqrT3.chainOf, Model.State.u32Max, Model.SparseRatchet.u64Max] at htriple
  obtain ⟨rfl, -, -⟩ := htriple
  simp [Model.SparseRatchet.setChains]
  rintro ch (h | h) <;> subst h <;> simp

/-- **The four counter ceilings at the session a successful first `encrypt` leaves**, under the
hypotheses of `established_encrypt_outcomes`.  Derived from the relation to the model's next session
(`established_encrypt_outcomes`), whose values the model computes (clock 0, sparse epoch 0, chain counters at
most 1, agreement epoch 1); the exact values are `established_encrypt_successor_shape`'s. -/
theorem established_encrypt_successor_counterHeadroom [Tacenta.SessionUnitT1.DerivedKeysModel]
    {R E : Type}
    (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView) (kem : KemView)
    (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
    (braid : BraidSendRefinementContracts rc oracle.braidKem) (triple : TripleSendRefinementContracts)
    (aead : Tacenta.UnitLifecycleT1.AeadSealBounded) (dhCodec : Tacenta.UnitLifecycleT1.DhCodecTotal)
    (oracleOf : OracleOf rc crc dh kem trace oracle) (codec : DhCodecOf dh)
    (codewordView : CodewordViewSendOf view)
    (hz80 : Tacenta.SessionUnitT3.ZeroizingRoundTrips80)
    (hz32 : ZeroizingRoundTrips (Array Std.U8 32#usize))
    (hzKeys : ZeroizingRoundTrips
      (Array Std.U8 32#usize × Array Std.U8 32#usize × Array Std.U8 16#usize))
    (hgen : KeyGenSeededFor oracle.braidKem rc crc trace) (hct : KemCiphertextLenOf)
    (hbound : KemCiphertextLenBound)
    (rcE : rand_core_1.RngCore E) (crcE : rand_core_1.CryptoRng E)
    (our : lifecycle.Identity) (bundle : lifecycle.PublishedBundle)
    (expected : tacenta_boundary.dh.PublicKeyBytes) (rng0 rng1 : E) (s : lifecycle.Session)
    (h : lifecycle.establish_initiator_for rcE crcE our bundle expected rng0 =
      ok (core.result.Result.Ok s, rng1))
    (plaintext : Slice Std.U8) (hroom : plaintext.val.length + 65770 ≤ Usize.max)
    (rng : R) (htrace : trace rng = oracle.draws)
    (hdraws : ∃ d1 d2 rest, trace rng = d1 :: d2 :: rest)
    (bytes : alloc.vec.Vec Std.U8) (s' : lifecycle.Session) (rng' : R)
    (hcall : lifecycle.Session.encrypt rc crc s plaintext rng =
      ok (core.result.Result.Ok bytes, s', rng')) :
    Tacenta.UnitLifecycleDecryptRunBounds.CounterHeadroom s' := by
  obtain ⟨d1, d2, rest, htr⟩ := hdraws
  obtain ⟨output, hcall', -, hcases⟩ := established_encrypt_outcomes rc crc trace dh kem view oracle
    braid triple aead dhCodec oracleOf codec codewordView hz80 hz32 hzKeys hgen hct hbound rcE crcE our
    bundle expected rng0 rng1 s h plaintext hroom rng htrace d1 d2 rest htr
  rw [hcall] at hcall'
  cases hcall'
  obtain ⟨p, rfl⟩ := establish_initiator_for_parts rcE crcE our bundle expected rng0 rng1 _ h
  rcases hcases with ⟨-, hres, -⟩ | ⟨dk, ekSeed, ekVector, hkg, bytes', hres, -, ⟨auth, kp, enc, hst⟩,
      tripleNext, messageKey, chunk, encoder, pending, a, htripleEx, -, -, -, -, hrel⟩
  · cases hres
  · obtain ⟨header, htriple⟩ := htripleEx
    obtain ⟨hev, hep, hch⟩ := established_triple_next_counters dh p tripleNext header messageKey htriple
    have hcl := congrArg Model.State.State.events hrel.triple.1
    have hpq := hrel.triple.2
    simp only [Tacenta.SessionUnitTripleT3.ratchetAbs] at hcl
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hcl, hev]; simp [U32.max_eq]
    · have := congrArg Model.SparseRatchet.State.epoch hpq
      simp only [Tacenta.SessionUnitTripleT3.spqrAbs] at this
      rw [this, hep]; simp [U64.max_eq]
    · intro q hq ch hch'
      have hc := congrArg Model.SparseRatchet.State.chains hpq
      simp only [Tacenta.SessionUnitTripleT3.spqrAbs] at hc
      have hmem : Tacenta.SessionUnitSpqrT3.chainsEntryOf q ∈ tripleNext.postQuantum.chains := by
        rw [← hc]; exact List.mem_map_of_mem hq
      have := hch _ hmem (Tacenta.SessionUnitSpqrT3.chainOf ch) (by
        rcases hch' with h | h <;> simp [Tacenta.SessionUnitSpqrT3.chainsEntryOf,
          Tacenta.SessionUnitSpqrT3.chainsOf, h])
      simp only [Tacenta.SessionUnitSpqrT3.chainOf] at this
      simp [U64.max_eq]; omega
    · rw [hst]
      simp [Tacenta.SessionUnitBraidT1.State.epoch_val, U64.max_eq]

/-- **After a successful first send, the session the call leaves is related to the model step's session**,
whose agreement is `keysSampled` at epoch 1, and the source it leaves holds the model step's draws: the
premises the next operation on that session takes about the session and the source, under the hypotheses of
`established_initiator_encrypt_refines`.  The relation at a `keysSampled` agreement is not definitional:
its encoder half is derived from the code's send under `ErasureAgrees`, its key-pair half is the content of
`KeyGenSeededFor`. -/
theorem established_encrypt_successor_refines [Tacenta.SessionUnitT1.DerivedKeysModel] {R E : Type}
    (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView) (kem : KemView)
    (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
    (braid : BraidSendRefinementContracts rc oracle.braidKem) (triple : TripleSendRefinementContracts)
    (aead : Tacenta.UnitLifecycleT1.AeadSealBounded) (dhCodec : Tacenta.UnitLifecycleT1.DhCodecTotal)
    (oracleOf : OracleOf rc crc dh kem trace oracle) (codec : DhCodecOf dh)
    (codewordView : CodewordViewSendOf view)
    (hz80 : Tacenta.SessionUnitT3.ZeroizingRoundTrips80)
    (hz32 : ZeroizingRoundTrips (Array Std.U8 32#usize))
    (hzKeys : ZeroizingRoundTrips
      (Array Std.U8 32#usize × Array Std.U8 32#usize × Array Std.U8 16#usize))
    (hgen : KeyGenSeededFor oracle.braidKem rc crc trace) (hct : KemCiphertextLenOf)
    (hbound : KemCiphertextLenBound)
    (rcE : rand_core_1.RngCore E) (crcE : rand_core_1.CryptoRng E)
    (our : lifecycle.Identity) (bundle : lifecycle.PublishedBundle)
    (expected : tacenta_boundary.dh.PublicKeyBytes) (rng0 rng1 : E) (s : lifecycle.Session)
    (h : lifecycle.establish_initiator_for rcE crcE our bundle expected rng0 =
      ok (core.result.Result.Ok s, rng1))
    (plaintext : Slice Std.U8) (hroom : plaintext.val.length + 65770 ≤ Usize.max)
    (rng : R) (htrace : trace rng = oracle.draws)
    (hdraws : ∃ d1 d2 rest, trace rng = d1 :: d2 :: rest)
    (bytes : alloc.vec.Vec Std.U8) (s' : lifecycle.Session) (rng' : R)
    (hcall : lifecycle.Session.encrypt rc crc s plaintext rng =
      ok (core.result.Result.Ok bytes, s', rng')) :
    SessionRefines dh oracle.braidKem s'
        (Model.Lifecycle.encrypt view oracle (establishedModelOf dh s) (sliceOf plaintext)).session ∧
      trace rng' =
        (Model.Lifecycle.encrypt view oracle (establishedModelOf dh s) (sliceOf plaintext)).oracle.draws ∧
      ∃ a dk ekVector encoder,
        (Model.Lifecycle.encrypt view oracle (establishedModelOf dh s) (sliceOf plaintext)).session.braid =
          .keysSampled 1 a dk ekVector encoder := by
  obtain ⟨d1, d2, rest, htr⟩ := hdraws
  obtain ⟨output, hcall', hstep⟩ := established_initiator_encrypt_refines rc crc trace dh kem view
    oracle braid triple aead dhCodec oracleOf codec codewordView hz80 hz32 hzKeys hgen hct hbound rcE
    crcE our bundle expected rng0 rng1 s h plaintext hroom rng htrace ⟨d1, d2, rest, htr⟩
  rw [hcall] at hcall'
  cases hcall'
  refine ⟨hstep.session, hstep.draws, ?_⟩
  have hres := hstep.result
  obtain ⟨p, rfl⟩ := establish_initiator_for_parts rcE crcE our bundle expected rng0 rng1 s h
  obtain ⟨-, hcases⟩ := established_encrypt_model_cases dh view oracle p (sliceOf plaintext) d1 d2
    rest (htrace.symm.trans htr)
  rcases hcases with ⟨-, hresM, -⟩ | ⟨dk, ekSeed, ekVector, -, tripleNext, header, messageKey, chunk,
      encoder, pending, -, -, -, -, hsessM⟩
  · rw [hresM] at hres; exact hres.elim
  · rw [hsessM]
    exact ⟨_, dk, ekVector, encoder, rfl⟩

/-! ## The premise list, as one record, holds together -/

/-- The hypotheses of `established_initiator_encrypt_refines` at one choice of every binder, the class
`DerivedKeysModel` as a `Nonempty`. -/
structure EstablishedEncryptHypotheses {R E : Type} (rc : rand_core_1.RngCore R)
    (crc : rand_core_1.CryptoRng R) (trace : R → List Model.Lifecycle.Key) (dh : DhView)
    (kem : KemView) (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
    (rcE : rand_core_1.RngCore E) (crcE : rand_core_1.CryptoRng E) (our : lifecycle.Identity)
    (bundle : lifecycle.PublishedBundle) (expected : tacenta_boundary.dh.PublicKeyBytes)
    (rng0 rng1 : E) (s : lifecycle.Session) (plaintext : Slice Std.U8) (rng : R) : Prop where
  braid : BraidSendRefinementContracts rc oracle.braidKem
  triple : TripleSendRefinementContracts
  derivedKeys : Nonempty Tacenta.SessionUnitT1.DerivedKeysModel
  aead : Tacenta.UnitLifecycleT1.AeadSealBounded
  dhCodec : Tacenta.UnitLifecycleT1.DhCodecTotal
  oracleOf : OracleOf rc crc dh kem trace oracle
  codec : DhCodecOf dh
  codewordView : CodewordViewSendOf view
  zeroizing80 : Tacenta.SessionUnitT3.ZeroizingRoundTrips80
  zeroizing32 : ZeroizingRoundTrips (Array Std.U8 32#usize)
  zeroizingKeys : ZeroizingRoundTrips
    (Array Std.U8 32#usize × Array Std.U8 32#usize × Array Std.U8 16#usize)
  keyGen : KeyGenSeededFor oracle.braidKem rc crc trace
  kemCiphertextLen : KemCiphertextLenOf
  kemCiphertextBound : KemCiphertextLenBound
  established : lifecycle.establish_initiator_for rcE crcE our bundle expected rng0 =
    ok (core.result.Result.Ok s, rng1)
  room : plaintext.val.length + 65770 ≤ Usize.max
  trace_eq : trace rng = oracle.draws
  draws : ∃ d1 d2 rest, trace rng = d1 :: d2 :: rest

/-- The record is the hypothesis list of `established_initiator_encrypt_refines`: from it, that theorem
applies. -/
theorem EstablishedEncryptHypotheses.refines {R E : Type} {rc : rand_core_1.RngCore R}
    {crc : rand_core_1.CryptoRng R} {trace : R → List Model.Lifecycle.Key} {dh : DhView}
    {kem : KemView} {view : Model.Lifecycle.CodewordView} {oracle : Model.Lifecycle.Oracle}
    {rcE : rand_core_1.RngCore E} {crcE : rand_core_1.CryptoRng E} {our : lifecycle.Identity}
    {bundle : lifecycle.PublishedBundle} {expected : tacenta_boundary.dh.PublicKeyBytes}
    {rng0 rng1 : E} {s : lifecycle.Session} {plaintext : Slice Std.U8} {rng : R}
    (H : EstablishedEncryptHypotheses rc crc trace dh kem view oracle rcE crcE our bundle expected
      rng0 rng1 s plaintext rng) :
    PublicEncryptWitness rc crc trace dh oracle.braidKem view oracle s (establishedModelOf dh s)
      plaintext rng := by
  obtain ⟨inst⟩ := H.derivedKeys
  exact established_initiator_encrypt_refines rc crc trace dh kem view oracle H.braid H.triple H.aead
    H.dhCodec H.oracleOf H.codec H.codewordView H.zeroizing80 H.zeroizing32 H.zeroizingKeys H.keyGen
    H.kemCiphertextLen H.kemCiphertextBound rcE crcE our bundle expected rng0 rng1 s H.established
    plaintext H.room rng H.trace_eq H.draws

open Tacenta.UnitLifecycleIntegrationScreen (byteRng byteCrc byteTrace)
open Tacenta.UnitSatisfiabilityJoint (InitiatorAxiom EncryptAxiom)
open Tacenta.UnitOracleShape (InterpO InterpO.real DhViewOf KemViewOf dhViewOf kemViewOf)
open Tacenta.UnitOracleJoint (OracleLaws)

/-- The `zeroize` round trip of the message-key triple at every instance, over an interpretation. -/
def ZeroizingKeysShape (I : Interp) : Prop :=
  ∀ inst : zeroize.Zeroize (Array Std.U8 32#usize × Array Std.U8 32#usize × Array Std.U8 16#usize),
    ∀ value, ∃ wrapped, I.zNew inst value = ok wrapped ∧ I.zDeref inst wrapped = ok value

/-- At the real constants the shape is the round trip `established_initiator_encrypt_refines` takes. -/
theorem zeroizingKeys_is :
    ZeroizingRoundTrips (Array Std.U8 32#usize × Array Std.U8 32#usize × Array Std.U8 16#usize) ↔
      ZeroizingKeysShape Interp.real :=
  Iff.rfl

/-- The laws the encrypt premises need beyond the decrypt and establishment laws, over an interpretation
`I` with its signing function, two views, a Braid KEM model `K` and a constant standing for
`kem::ciphertext_len`: the laws under which `OracleOf` holds, the axiom part of the encrypt contract
record at the byte-stream source, the key-generation law at the byte-stream source, the message-key round
trip and the ciphertext-length bound. -/
structure EncryptExtraLawsShape (I : InterpO) (dh : DhViewOf I.toInterp) (kem : KemViewOf I.toInterp)
    (K : Model.Braid.Kem) (ciphertextLen : Result Usize) : Prop where
  oracle : OracleLaws I dh kem
  encrypt : EncryptAxiom I.toInterp byteRng
  keyGen : KeyGenSeededForShape I.toInterp K byteRng byteCrc byteTrace
  zeroizingKeys : ZeroizingKeysShape I.toInterp
  ciphertextBound : Tacenta.UnitLifecycleRestoredSession.KemCiphertextLenBoundShape ciphertextLen

/-- The extra laws at the real constants. -/
def EncryptExtraLaws (K : Model.Braid.Kem) (dh : DhView) (kem : KemView) : Prop :=
  EncryptExtraLawsShape InterpO.real (dhViewOf dh) (kemViewOf kem) K
    tacenta_boundary.kem.ciphertext_len

/-- The side condition of `emptyPlaintext`. -/
theorem nil_length_le : ([] : List Std.U8).length ≤ Usize.max := by simp

/-- The empty plaintext. -/
def emptyPlaintext : Slice Std.U8 := ⟨[], nil_length_le⟩

/-- A byte-stream state of at least 64 bytes holds two draws. -/
theorem byteTrace_two (seed : List Std.U8) (h : 64 ≤ seed.length) :
    byteTrace seed = (seed.map Tacenta.SessionUnitBraidT3.u8).take 32 ::
      ((seed.map Tacenta.SessionUnitBraidT3.u8).drop 32).take 32 ::
        Tacenta.UnitLifecycleIntegrationScreen.chunks32
          (((seed.map Tacenta.SessionUnitBraidT3.u8).drop 32).drop 32) := by
  unfold byteTrace
  rw [Tacenta.UnitLifecycleIntegrationScreen.chunks32, if_pos (by simp; omega),
    Tacenta.UnitLifecycleIntegrationScreen.chunks32, if_pos (by simp; omega)]

/-- **Every hypothesis of `established_initiator_encrypt_refines` holds together at the real constants**,
under the decrypt laws `DecryptJointLaws K dh`, the axiom part of the initiator contract record,
`InitiatorSuccessShape`, `DhPublicValid`, `KemCiphertextLenOf` and the extra laws `EncryptExtraLaws K dh kem`,
all assumed: for every identity and every byte-stream source of at least 64 bytes there are an oracle with
`braidKem = K`, a bundle and a successful establishment from the empty source at which every field of
`EstablishedEncryptHypotheses` holds, for the empty plaintext and the codeword view of
`UnitLifecycleRepair`. -/
theorem established_encrypt_hypotheses_jointly_satisfiable (K : Model.Braid.Kem) (dh : DhView)
    (kem : KemView) (L : Tacenta.UnitLifecycleDecryptScreen.DecryptJointLaws K dh)
    (A : Nonempty (InitiatorAxiom Interp.real byteRng))
    (S : InitiatorSuccessShape Interp.real byteRng byteCrc)
    (hpub : DhPublicValid) (hct : KemCiphertextLenOf) (X : EncryptExtraLaws K dh kem)
    (our : lifecycle.Identity) (seed : List Std.U8) (hseed : 64 ≤ seed.length) :
    ∃ (oracle : Model.Lifecycle.Oracle) (bundle : lifecycle.PublishedBundle) (s : lifecycle.Session)
      (rng1 : List Std.U8),
      oracle.braidKem = K ∧ oracle.draws = byteTrace seed ∧
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
  obtain ⟨oracle1, hshape, -⟩ :=
    Tacenta.UnitOracleJoint.oracleOfShape_of_oracleLaws InterpO.real (dhViewOf dh) (kemViewOf kem)
      X.oracle
  have hO : OracleOf byteRng byteCrc dh kem byteTrace oracle1 :=
    (Tacenta.UnitOracleShape.oracleOf_iff_shape byteRng byteCrc dh kem byteTrace oracle1).mpr hshape
  let oracle : Model.Lifecycle.Oracle := { oracle1 with draws := byteTrace seed, braidKem := K }
  have hOracle : OracleOf byteRng byteCrc dh kem byteTrace oracle :=
    ⟨hO.dhPublic, hO.dhAgree, hO.identityValid, hO.aeadSeal, hO.aeadOpen, hO.kemEncapsulateSuccess,
      hO.kemInvalidKey, hO.kemEncapsulateError, hO.kemDecapsulate, hO.sigVerify, hO.sigSign,
      hO.random32⟩
  refine ⟨oracle, bundle, s, rng1, rfl, rfl, ?_⟩
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

/-- The two draws of a 64-byte source are its bytes. -/
theorem two_draws_of_64 (seed : List Std.U8) (h : seed.length = 64) :
    (seed.map Tacenta.SessionUnitBraidT3.u8).take 32 ++
        ((seed.map Tacenta.SessionUnitBraidT3.u8).drop 32).take 32 =
      seed.map Tacenta.SessionUnitBraidT3.u8 := by
  rw [← List.take_add]
  exact List.take_of_length_le (by simp [h])

/-- The outcome theorem at the witness of `established_encrypt_hypotheses_jointly_satisfiable`, for a
64-byte source: the two arms are told apart by the model's key generation at the source's bytes. -/
theorem established_encrypt_outcomes_at_witness (K : Model.Braid.Kem) (dh : DhView)
    (kem : KemView) (L : Tacenta.UnitLifecycleDecryptScreen.DecryptJointLaws K dh)
    (A : Nonempty (InitiatorAxiom Interp.real byteRng))
    (S : InitiatorSuccessShape Interp.real byteRng byteCrc)
    (hpub : DhPublicValid) (hct : KemCiphertextLenOf) (X : EncryptExtraLaws K dh kem)
    (our : lifecycle.Identity) (seed : List Std.U8) (hseed : seed.length = 64) :
    ∃ (oracle : Model.Lifecycle.Oracle) (bundle : lifecycle.PublishedBundle) (s : lifecycle.Session)
      (rng1 : List Std.U8)
      (output : core.result.Result (alloc.vec.Vec Std.U8) lifecycle.Error × lifecycle.Session ×
        List Std.U8),
      oracle.braidKem = K ∧
      EstablishedEncryptHypotheses byteRng byteCrc byteTrace dh kem
        Tacenta.UnitLifecycleRepair.witnessView oracle byteRng byteCrc our bundle
        bundle.bundle.identity_key [] rng1 s emptyPlaintext seed ∧
      lifecycle.Session.encrypt byteRng byteCrc s emptyPlaintext seed = ok output ∧
      ((K.keyGen (Model.Lifecycle.braidRandomness (seed.map Tacenta.SessionUnitBraidT3.u8)) = none ∧
          output.1 = core.result.Result.Err lifecycle.Error.AgreementFailed ∧
          output.2.1 = { s with braid := ⟨tacenta_braid.State.Failed⟩ }) ∨
        (K.keyGen (Model.Lifecycle.braidRandomness (seed.map Tacenta.SessionUnitBraidT3.u8)) ≠ none ∧
          ∃ bytes, output.1 = core.result.Result.Ok bytes ∧
          ∃ auth kp encoder, output.2.1.braid.state = .KeysSampled 1#u64 auth kp encoder)) := by
  obtain ⟨oracle, bundle, s, rng1, hK, hdraws, H⟩ :=
    established_encrypt_hypotheses_jointly_satisfiable K dh kem L A S hpub hct X our seed (by omega)
  obtain ⟨inst⟩ := H.derivedKeys
  subst hK
  obtain ⟨output, hcall, -, hcases⟩ := established_encrypt_outcomes byteRng byteCrc byteTrace dh kem
    Tacenta.UnitLifecycleRepair.witnessView oracle H.braid H.triple H.aead H.dhCodec H.oracleOf H.codec
    H.codewordView H.zeroizing80 H.zeroizing32 H.zeroizingKeys H.keyGen H.kemCiphertextLen
    H.kemCiphertextBound byteRng byteCrc our bundle _ [] rng1 s H.established emptyPlaintext H.room seed
    H.trace_eq _ _ _ (byteTrace_two seed (by omega))
  rw [two_draws_of_64 seed hseed] at hcases
  refine ⟨oracle, bundle, s, rng1, output, rfl, H, hcall, ?_⟩
  rcases hcases with hl | ⟨dk, ekSeed, ekVector, hkg, bytes, hres, -, hst, -⟩
  · exact Or.inl hl
  · exact Or.inr ⟨by rw [hkg]; simp, bytes, hres, hst⟩

/-- **The success arm is reached** at the real constants, under the laws of
`established_encrypt_hypotheses_jointly_satisfiable`, for every identity and every 64-byte source at whose
bytes the model's key generation answers: the call returns bytes and the agreement is `KeysSampled` at epoch
1, at a session and source where every premise of `established_initiator_encrypt_refines` holds. -/
theorem established_encrypt_success_reachable (K : Model.Braid.Kem) (dh : DhView)
    (kem : KemView) (L : Tacenta.UnitLifecycleDecryptScreen.DecryptJointLaws K dh)
    (A : Nonempty (InitiatorAxiom Interp.real byteRng))
    (S : InitiatorSuccessShape Interp.real byteRng byteCrc)
    (hpub : DhPublicValid) (hct : KemCiphertextLenOf) (X : EncryptExtraLaws K dh kem)
    (our : lifecycle.Identity) (seed : List Std.U8) (hseed : seed.length = 64)
    (hkg : K.keyGen (Model.Lifecycle.braidRandomness (seed.map Tacenta.SessionUnitBraidT3.u8)) ≠ none) :
    ∃ (oracle : Model.Lifecycle.Oracle) (bundle : lifecycle.PublishedBundle) (s : lifecycle.Session)
      (rng1 : List Std.U8) (bytes : alloc.vec.Vec Std.U8) (s' : lifecycle.Session) (rng' : List Std.U8),
      oracle.braidKem = K ∧
      EstablishedEncryptHypotheses byteRng byteCrc byteTrace dh kem
        Tacenta.UnitLifecycleRepair.witnessView oracle byteRng byteCrc our bundle
        bundle.bundle.identity_key [] rng1 s emptyPlaintext seed ∧
      lifecycle.Session.encrypt byteRng byteCrc s emptyPlaintext seed =
        ok (core.result.Result.Ok bytes, s', rng') ∧
      ∃ auth kp encoder, s'.braid.state = .KeysSampled 1#u64 auth kp encoder := by
  obtain ⟨oracle, bundle, s, rng1, ⟨res, s', rng'⟩, hK, H, hcall, hcases⟩ :=
    established_encrypt_outcomes_at_witness K dh kem L A S hpub hct X our seed hseed
  rcases hcases with ⟨hnone, -⟩ | ⟨-, bytes, hres, hst⟩
  · exact absurd hnone hkg
  · simp only at hres hst
    subst hres
    exact ⟨oracle, bundle, s, rng1, bytes, s', rng', hK, H, hcall, hst⟩

/-- **The key-generation refusal arm is reached** at the real constants, under the same laws, for every
identity and every 64-byte source at whose bytes the model's key generation refuses: the call returns
`AgreementFailed` and the session with its agreement `Failed` and nothing else changed. -/
theorem established_encrypt_refusal_reachable (K : Model.Braid.Kem) (dh : DhView)
    (kem : KemView) (L : Tacenta.UnitLifecycleDecryptScreen.DecryptJointLaws K dh)
    (A : Nonempty (InitiatorAxiom Interp.real byteRng))
    (S : InitiatorSuccessShape Interp.real byteRng byteCrc)
    (hpub : DhPublicValid) (hct : KemCiphertextLenOf) (X : EncryptExtraLaws K dh kem)
    (our : lifecycle.Identity) (seed : List Std.U8) (hseed : seed.length = 64)
    (hkg : K.keyGen (Model.Lifecycle.braidRandomness (seed.map Tacenta.SessionUnitBraidT3.u8)) = none) :
    ∃ (oracle : Model.Lifecycle.Oracle) (bundle : lifecycle.PublishedBundle) (s : lifecycle.Session)
      (rng1 : List Std.U8) (rng' : List Std.U8),
      oracle.braidKem = K ∧
      EstablishedEncryptHypotheses byteRng byteCrc byteTrace dh kem
        Tacenta.UnitLifecycleRepair.witnessView oracle byteRng byteCrc our bundle
        bundle.bundle.identity_key [] rng1 s emptyPlaintext seed ∧
      lifecycle.Session.encrypt byteRng byteCrc s emptyPlaintext seed =
        ok (core.result.Result.Err lifecycle.Error.AgreementFailed,
          { s with braid := ⟨tacenta_braid.State.Failed⟩ }, rng') := by
  obtain ⟨oracle, bundle, s, rng1, ⟨res, s', rng'⟩, hK, H, hcall, hcases⟩ :=
    established_encrypt_outcomes_at_witness K dh kem L A S hpub hct X our seed hseed
  rcases hcases with ⟨-, hres, hs⟩ | ⟨hsome, -⟩
  · simp only at hres hs
    subst hres hs
    exact ⟨oracle, bundle, s, rng1, rng', hK, H, hcall⟩
  · exact absurd hkg hsome

/-! ## One interpretation satisfies every law, with the decrypt, establishment and restore laws -/

section JointModel
open Tacenta.UnitSatisfiabilityJoint
open Tacenta.UnitSatisfiabilityBraidAgreements (KemAgreesShape T3Agreements AllT1Shapes seedOf ekVecOf
  vecOf_vecOfBytes keyOf_arr32 arr32)
open Tacenta.UnitLifecycleEstablishedDecrypt (Interp.modelEstablished oneKey oneKey_canonical
  oneKey_ne_zero established_decrypt_laws_model)
open Tacenta.UnitLifecycleDecryptRatchetScreen (DhViewShape modelDecrypt_allT1)
open Tacenta.UnitLifecycleSessionCodec (ZeroizingVecRoundTripShape DhPrivateBytesRoundTripShape
  DhPublicBytesRoundTripShape OptionBranchSomeShape VecAsSliceShape optionBranchImpl vecAsSliceImpl
  vecAsSliceImpl_shape)
open Tacenta.UnitLifecycleRestoredSession (KemCiphertextLenBoundShape model_kemCiphertextLenBound)

/-- `toyKem` with key generation refusing at the randomness 0, so that both arms of the first send occur in
one model. -/
def toyKemR : Model.Braid.Kem :=
  { Model.Braid.toyKem with
    keyGen := fun r => if r = 0 then none else Model.Braid.toyKem.keyGen r }

/-- Key generation that fills one 64-byte seed and returns its little-endian value as the key pair,
refusing the value 0. -/
def genFill : {R : Type} → rand_core_1.RngCore R → rand_core_1.CryptoRng R → R →
    Result (core.result.Result ℕ tacenta_kem.KemError × R) := fun rc _ rng => do
  let (rng', seed) ← rc.fill_bytes rng Tacenta.UnitLifecycleIntegrationScreen.zeros64
  let r := Model.Messages.leValue (sliceOf seed)
  ok (if r = 0 then .Err () else .Ok r, rng')

/-- The toy encapsulation's result: an empty ciphertext, the first 32 drawn bytes as the secret. -/
def encapResult (_publicKey m : Model.Lifecycle.Bytes) : alloc.vec.Vec U8 × Array U8 32#usize :=
  (alloc.vec.Vec.new U8, Tacenta.UnitOracleModel.bytesArr32 m)

/-- Encapsulation in the form of `KemShapeOf`: it accepts every key, fills one 32-byte buffer and returns
`encapResult` of the key and those bytes. -/
def encapFill : Tacenta.UnitLifecycleIntegrationScreen.EncapFn := fun rc _ publicKey rng =>
  if (fun _ => true : Model.Lifecycle.Bytes → Bool) (sliceOf publicKey) then
    (do let (rng', m) ← rc.fill_bytes rng Tacenta.UnitLifecycleIntegrationScreen.zeros32
        ok (core.result.Result.Ok (encapResult (sliceOf publicKey) (sliceOf m)), rng'))
  else ok (.Err (), rng)

/-- `Interp.modelEstablished` with key generation and encapsulation that read the source:
`genFill` and `encapFill`.  Every other field is `Interp.modelEstablished`'s. -/
noncomputable def Interp.modelEncrypt : Interp :=
  { Interp.modelEstablished with
    ikpGenerate := genFill
    kemEncapsulate := encapFill }

/-- The joint interpretation with its signing function, `UnitOracleModel.signModelO`. -/
noncomputable def InterpO.modelEncrypt : InterpO :=
  { Interp.modelEncrypt with xeddsaSign := Tacenta.UnitOracleModel.signModelO }

/-- The views of the joint interpretation: the key types are their bytes; the KEM key pair is `Unit`. -/
def viewEncrypt : DhViewShape Interp.modelEncrypt := ⟨arrayOf, arrayOf⟩
def dhViewEncrypt : DhViewOf InterpO.modelEncrypt.toInterp :=
  ⟨viewEncrypt.privateKey, viewEncrypt.publicKey⟩
def kemViewEncrypt : KemViewOf InterpO.modelEncrypt.toInterp := ⟨fun _ => []⟩

/-- What `genFill` answers from a fill. -/
theorem genFill_answers (r : ℕ) {R : Type} (rc : rand_core_1.RngCore R)
    (crc : rand_core_1.CryptoRng R) (rng rng' : R) (seed : Slice U8)
    (hf : rc.fill_bytes rng Tacenta.UnitLifecycleIntegrationScreen.zeros64 = ok (rng', seed))
    (hr : Model.Messages.leValue (sliceOf seed) = r) :
    KeyGenAnswersShape Interp.modelEncrypt toyKemR rc crc rng r rng' := by
  by_cases h0 : r = 0
  · right
    refine ⟨⟨(), ?_⟩, ?_⟩
    · show genFill rc crc rng = _
      simp [genFill, hf, hr, h0]; rfl
    · simp [toyKemR, h0]
  · left
    refine ⟨r, seedOf r, seedOf r, ekVecOf r, ?_, ?_, ⟨_, rfl, ?_⟩, ⟨_, rfl, ?_⟩, ?_⟩
    · show genFill rc crc rng = _
      simp [genFill, hf, hr, h0]; rfl
    · simp [toyKemR, h0, Model.Braid.toyKem, seedOf, ekVecOf]
    · rw [vecOf_vecOfBytes]; rfl
    · rw [vecOf_vecOfBytes]
    · intro ct1 ct2 _ _
      refine Or.inl ⟨arr32 (seedOf r), rfl, ?_⟩
      rw [keyOf_arr32 _ (by simp [seedOf])]; rfl

/-- The key-generation law holds in the joint interpretation at `toyKemR` and the byte-stream source. -/
theorem modelEncrypt_keyGenSeeded :
    KeyGenSeededForShape Interp.modelEncrypt toyKemR byteRng byteCrc byteTrace := by
  intro rng d1 d2 rest h
  obtain ⟨s, hf, htr, hs⟩ := Tacenta.UnitLifecycleIntegrationScreen.byte_fill_64 h
  exact ⟨_, htr, genFill_answers _ byteRng byteCrc rng _ s hf
    (by have hs' : sliceOf s = d1 ++ d2 := hs; rw [hs']; rfl)⟩

/-- The KEM agreement holds in the joint interpretation at `toyKemR`, both arms of key generation
included. -/
theorem modelEncrypt_kemAgrees : KemAgreesShape Interp.modelEncrypt toyKemR := by
  refine ⟨?_, ?_⟩
  · intro R rc crc rng hrng
    obtain ⟨⟨rng', seed⟩, hf⟩ := hrng rng Tacenta.UnitLifecycleIntegrationScreen.zeros64
    exact ⟨rng', _, genFill_answers _ rc crc rng rng' seed hf rfl⟩
  · intro R rc crc header rng _ _
    refine ⟨rng, 0, Or.inl ⟨(), _,
      arr32 ((Tacenta.SessionUnitBraidT3.sliceOf header).take 32), rfl, ?_⟩⟩
    intro ekSeed hek hlen hsplit
    refine ⟨ekSeed, ?_, ?_⟩
    · rw [vecOf_vecOfBytes, hsplit, List.take_left' hlen, keyOf_arr32 _ hlen]; rfl
    · intro ekVector _
      refine Or.inl ⟨_, rfl, ?_⟩
      rw [vecOf_vecOfBytes]; rfl

/-- Key generation returns in the joint interpretation for every source whose fills return. -/
theorem modelEncrypt_keyPairGenerate : KeyPairGenerateShape Interp.modelEncrypt := by
  intro R rc crc rng hrng
  obtain ⟨⟨rng', seed⟩, hf⟩ := hrng rng Tacenta.UnitLifecycleIntegrationScreen.zeros64
  exact ⟨_, show genFill rc crc rng = _ by simp [genFill, hf]; rfl⟩

/-- Encapsulation returns in the joint interpretation for every source whose fills return. -/
theorem modelEncrypt_kemEncapsulate : KemEncapsulateShape Interp.modelEncrypt := by
  intro R rc crc pk rng hrng
  obtain ⟨⟨rng', m⟩, hf⟩ := hrng rng Tacenta.UnitLifecycleIntegrationScreen.zeros32
  exact ⟨_, show encapFill rc crc pk rng = _ by simp [encapFill, hf]; rfl⟩

/-- The `NoPanic` form of the source law at the byte-stream source. -/
theorem byteRng_rngTotal : Tacenta.SessionUnitBraidT1.RngTotal byteRng := fun _ _ => ⟨_, rfl⟩

/-- Every axiom-level totality shape of the four records holds in the joint interpretation. -/
theorem modelEncrypt_allT1 : AllT1Shapes Interp.modelEncrypt where
  dhCodec := ⟨fun _ => ⟨_, rfl⟩, fun _ => ⟨_, rfl⟩, fun _ => ⟨_, rfl⟩, fun _ => ⟨_, rfl⟩,
    fun _ => ⟨_, rfl⟩, fun _ _ => ⟨_, rfl⟩⟩
  dhIdentity := modelDecrypt_allT1.dhIdentity
  dhAgree := modelDecrypt_allT1.dhAgree
  kemEncapsulate := modelEncrypt_kemEncapsulate
  kemDecapsulate := modelDecrypt_allT1.kemDecapsulate
  xeddsaVerify := modelDecrypt_allT1.xeddsaVerify
  aeadOpen := modelDecrypt_allT1.aeadOpen
  aeadSealBounded := modelDecrypt_allT1.aeadSealBounded
  messageKeyMaterial := modelDecrypt_allT1.messageKeyMaterial
  vecPop := modelDecrypt_allT1.vecPop
  hkdf := modelDecrypt_allT1.hkdf
  hmac := modelDecrypt_allT1.hmac
  zeroizingTotal := modelDecrypt_allT1.zeroizingTotal
  spqrZeroize := modelDecrypt_allT1.spqrZeroize
  vecRetainAxiom := modelDecrypt_allT1.vecRetainAxiom
  optionClone := modelDecrypt_allT1.optionClone
  ct1Len := modelDecrypt_allT1.ct1Len
  ct2Len := modelDecrypt_allT1.ct2Len
  headerLen := modelDecrypt_allT1.headerLen
  ekVectorLen := modelDecrypt_allT1.ekVectorLen
  keyPairEkVector := modelDecrypt_allT1.keyPairEkVector
  keyPairHeader := modelDecrypt_allT1.keyPairHeader
  keyPairDecapsulate := modelDecrypt_allT1.keyPairDecapsulate
  keyPairClone := modelDecrypt_allT1.keyPairClone
  encapsStateClone := modelDecrypt_allT1.encapsStateClone
  validateEk := modelDecrypt_allT1.validateEk
  keyPairGenerate := modelEncrypt_keyPairGenerate
  encapsulate1 := modelDecrypt_allT1.encapsulate1
  encapsulate2 := modelDecrypt_allT1.encapsulate2
  zeroizingArray := modelDecrypt_allT1.zeroizingArray
  arrayZeroize := modelDecrypt_allT1.arrayZeroize
  rangeFullIndex := modelDecrypt_allT1.rangeFullIndex
  divCeilValue := modelDecrypt_allT1.divCeilValue

/-- The 64 zero bytes, and the 64 bytes `1, 0, ..., 0`, as byte-stream sources. -/
def zeroSeed : List U8 := List.replicate 64 0#u8
def oneSeed : List U8 := 1#u8 :: List.replicate 63 0#u8

theorem leValue_replicate_zero (n : ℕ) : Model.Messages.leValue (List.replicate n 0) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, Model.Messages.leValue, ih]

/-- `toyKemR` refuses at the bytes of `zeroSeed` and answers at those of `oneSeed`. -/
theorem toyKemR_seeds :
    toyKemR.keyGen (Model.Lifecycle.braidRandomness
        (zeroSeed.map Tacenta.SessionUnitBraidT3.u8)) = none ∧
      toyKemR.keyGen (Model.Lifecycle.braidRandomness
        (oneSeed.map Tacenta.SessionUnitBraidT3.u8)) ≠ none := by
  have h0 : zeroSeed.map Tacenta.SessionUnitBraidT3.u8 = List.replicate 64 0 := by decide
  have h1 : oneSeed.map Tacenta.SessionUnitBraidT3.u8 = 1 :: List.replicate 63 0 := by decide
  refine ⟨?_, ?_⟩
  · simp only [Model.Lifecycle.braidRandomness]
    rw [h0, leValue_replicate_zero]
    simp [toyKemR]
  · simp only [Model.Lifecycle.braidRandomness]
    rw [h1, Model.Messages.leValue, leValue_replicate_zero]
    simp [toyKemR, Model.Braid.toyKem]

/-- `toyKemR`'s key generation returns a 32-byte seed, a vector of `ekSize` (64) bytes and a 32-byte
hash. -/
theorem toyKemR_sizes : KeyGenSizesOf toyKemR := by
  intro rand dk ekSeed ekVector h
  by_cases h0 : rand = 0
  · simp [toyKemR, h0] at h
  · simp only [toyKemR, h0, if_false, Model.Braid.toyKem, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl, rfl⟩ := h
    refine ⟨by simp, by simp [toyKemR, Model.Braid.toyKem], by simp [toyKemR, Model.Braid.toyKem]⟩

/-- **Every law the encrypt premise list rests on, with the decrypt, establishment and restore laws, holds
in one interpretation**, `InterpO.modelEncrypt` (`Interp.modelEstablished` with key generation and
encapsulation that read the byte-stream source, and its signing function), with its views, the toy KEM
`toyKemR`, `optionEqImpl` for `Option::eq` and the constant `ok 0` for `kem::ciphertext_len`: the decrypt
laws, the initiator contract axioms, `InitiatorSuccessShape`, `DhPublicValidShape`, the ciphertext-length
law, the encrypt extra laws (the `OracleOf` laws, the encrypt axiom part, the key-generation law at the
byte-stream source, the message-key round trip, the ciphertext bound), the six laws of the restored
session's round trip, and the two key-generation outcomes at `zeroSeed` and `oneSeed`.  In the
substitution sense of `UnitSatisfiabilityRecords`; not a statement that the real primitives meet them. -/
theorem established_encrypt_laws_model :
    Tacenta.UnitLifecycleDecryptScreen.DecryptJointLawsShape Interp.modelEncrypt viewEncrypt toyKemR
        @Tacenta.UnitHeadroomInvariant.optionEqImpl ∧
      Nonempty (InitiatorAxiom Interp.modelEncrypt byteRng) ∧
      InitiatorSuccessShape Interp.modelEncrypt byteRng byteCrc ∧
      DhPublicValidShape Interp.modelEncrypt ∧
      KemCiphertextLenLawShape (ok 0#usize) Interp.modelEncrypt ∧
      EncryptExtraLawsShape InterpO.modelEncrypt dhViewEncrypt kemViewEncrypt toyKemR (ok 0#usize) ∧
      (ZeroizingVecRoundTripShape Interp.modelEncrypt ∧ DhPrivateBytesRoundTripShape Interp.modelEncrypt ∧
        DhPublicBytesRoundTripShape Interp.modelEncrypt ∧ OptionBranchSomeShape @optionBranchImpl ∧
        VecAsSliceShape @vecAsSliceImpl ∧ KemCiphertextLenBoundShape (ok 0#usize)) ∧
      KeyGenSizesOf toyKemR ∧
      toyKemR.keyGen (Model.Lifecycle.braidRandomness
          (zeroSeed.map Tacenta.SessionUnitBraidT3.u8)) = none ∧
      toyKemR.keyGen (Model.Lifecycle.braidRandomness
          (oneSeed.map Tacenta.SessionUnitBraidT3.u8)) ≠ none := by
  obtain ⟨M, ⟨A⟩, S, P, -⟩ := established_decrypt_laws_model
  have T := modelEncrypt_allT1
  refine ⟨?_, ⟨?_⟩, ?_, ?_, ?_, ?_, ?_, toyKemR_sizes, toyKemR_seeds⟩
  · exact
      { dhCodec := T.dhCodec
        dhAgree := M.dhAgree
        aeadOpen := M.aeadOpen
        viewInjective := M.viewInjective
        codec := by have h := M.codec; cases h; constructor <;> assumption
        braid := by have h := M.braid; cases h; constructor <;> assumption
        triple := by have h := M.triple; cases h; constructor <;> assumption
        messageKeyMaterial := M.messageKeyMaterial
        laws := by have h := M.laws; cases h; constructor <;> assumption
        truncatePrefix := M.truncatePrefix
        derivedKeys := by
          obtain ⟨h⟩ := M.derivedKeys; cases h; exact ⟨by constructor <;> assumption⟩
        agreements :=
          { kemLen := M.agreements.kemLen
            kemAgrees := modelEncrypt_kemAgrees
            validateEk := M.agreements.validateEk
            kemClone := M.agreements.kemClone
            hkdf := M.agreements.hkdf
            hmac := M.agreements.hmac }
        roundTrips := by have h := M.roundTrips; cases h; constructor <;> assumption
        validKey := M.validKey
        optionEq := M.optionEq }
  · exact
      { dhCodec := T.dhCodec
        dhIdentity := T.dhIdentity
        dhAgree := T.dhAgree
        kemEncapsulate := T.kemEncapsulate
        xeddsaVerify := T.xeddsaVerify
        rngTotal := Tacenta.UnitOracleModel.byteRng_total
        random32 := fun _ _ _ => ⟨_, rfl⟩
        sessionHkdf := T.hkdf
        sessionZeroizing := by have h := A.sessionZeroizing; cases h; constructor <;> assumption
        tripleZeroizing := T.zeroizingTotal
        spqrZeroize := T.spqrZeroize
        braidHkdf := T.hkdf
        zeroizingArray := T.zeroizingArray
        rangeFullIndex := T.rangeFullIndex }
  · refine ⟨⟨oneKey, oneKey, rfl, oneKey_canonical, rfl, ?_, fun _ => ⟨Array.repeat 64#usize 0#u8, rfl⟩,
      fun k => ⟨k, ?_⟩⟩, ⟨alloc.vec.Vec.new U8, by simp; scalar_tac, fun rng => ⟨_, _, _, rfl⟩⟩⟩
    · show ok (decide (oneKey.val = oneKey.val)) = ok true
      simp
    · show ok (if oneKey.val = Tacenta.UnitLifecycleDecryptRatchetScreen.zeros32.val then none
        else some k) = ok (some k)
      simp [oneKey_ne_zero]
  · exact P
  · intro R rc crc pk rng ct ss rng' h
    simp only [Interp.modelEncrypt, encapFill, if_true] at h
    rcases hf : rc.fill_bytes rng Tacenta.UnitLifecycleIntegrationScreen.zeros32 with
      ⟨rngA, m⟩ | e | _ <;> rw [hf] at h <;> simp [encapResult] at h
    obtain ⟨⟨rfl, -⟩, -⟩ := h
    exact ⟨0#usize, rfl, by simp⟩
  · exact
      { oracle :=
          { dhCodec := T.dhCodec
            dhAgree := T.dhAgree
            dhIdentity := T.dhIdentity
            aeadSeal := T.aeadSealBounded
            aeadOpen := T.aeadOpen
            kemDecapsulate := T.kemDecapsulate
            xeddsaVerify := T.xeddsaVerify
            signLaw := Tacenta.UnitOracleModel.modelO_signLaw
            kemLaw := ⟨fun _ => true, encapResult, fun _ _ _ _ => rfl⟩
            dhView := ⟨Tacenta.UnitOracleShape.arrayOf_injective _,
              Tacenta.UnitOracleShape.arrayOf_injective _⟩
            kemView := fun _ _ _ => rfl }
        encrypt :=
          { braid :=
              { rng := byteRng_rngTotal, keyPairClone := T.keyPairClone
                encapsStateClone := T.encapsStateClone, keyPairGenerate := T.keyPairGenerate
                keyPairHeader := T.keyPairHeader, hmac := T.hmac, hkdf := T.hkdf
                encapsulate1 := T.encapsulate1, zeroizingArray := T.zeroizingArray
                arrayZeroize := T.arrayZeroize, rangeFullIndex := T.rangeFullIndex }
            triple :=
              { hmac := T.hmac, hkdf := T.hkdf, zeroize := T.spqrZeroize
                vecRetain := T.vecRetainAxiom, optionClone := T.optionClone }
            aeadSeal := T.aeadSealBounded
            messageKeyMaterial := T.messageKeyMaterial
            dhCodec := T.dhCodec }
        keyGen := modelEncrypt_keyGenSeeded
        zeroizingKeys := fun _ v => ⟨v, rfl, rfl⟩
        ciphertextBound := model_kemCiphertextLenBound }
  · exact ⟨fun _ _ => ⟨_, rfl, rfl⟩, fun _ => ⟨_, _, rfl, rfl, rfl⟩, fun _ => ⟨_, rfl, rfl⟩,
      (fun _ _ => rfl), vecAsSliceImpl_shape, model_kemCiphertextLenBound⟩

end JointModel

/-! ## After a successful first send: the session passes `Session::invariant` -/

section Successor
open Tacenta.SessionUnitRatchetImportInv (bind_eq_ok_inv bind3_eq_ok_inv)
open Tacenta.UnitHeadroomInvariant (OptionEqU64Shape vec_ne_self array_ne_self)

/-- A successful `encrypt` ran the agreement send and a Triple candidate send that succeeded, and returned
the session with the candidate and the agreement send's next state, and the source the agreement send
left. -/
theorem encrypt_ok_parts {R : Type} (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R)
    (s : lifecycle.Session) (plaintext : Slice Std.U8) (rng : R) (v : alloc.vec.Vec Std.U8)
    (s' : lifecycle.Session) (rng' : R)
    (h : lifecycle.Session.encrypt rc crc s plaintext rng = ok (core.result.Result.Ok v, s', rng')) :
    ∃ m e o b, tacenta_braid.Braid.send rc crc s.braid rng = ok ((m, e, o, b), rng') ∧
      ∃ sparse cand hdr mk, lifecycle.send_candidate s.triple e sparse = ok (cand, .Ok (hdr, mk)) ∧
        s' = { s with triple := cand, braid := b } := by
  unfold lifecycle.Session.encrypt at h
  obtain ⟨fb, hfb, h⟩ := bind_eq_ok_inv h
  split at h
  · simp at h
  obtain ⟨⟨⟨m, e, o, b⟩, rng1⟩, hsend, h⟩ := bind_eq_ok_inv h
  obtain ⟨fb1, hfb1, h⟩ := bind_eq_ok_inv h
  split at h
  · simp at h
  obtain ⟨sp, hsp, h⟩ := bind_eq_ok_inv h
  obtain ⟨⟨cand, sent⟩, hcand, h⟩ := bind_eq_ok_inv h
  rcases sent with ⟨hdr, mk⟩ | err
  · simp only at h
    have key : s' = { s with triple := cand, braid := b } ∧ rng' = rng1 := by
      repeat' first
        | (replace h := bind3_eq_ok_inv h; obtain ⟨_, _, _, _, h⟩ := h)
        | (replace h := bind_eq_ok_inv h; obtain ⟨_, _, h⟩ := h)
        | split at h
        | simp only [ok.injEq, Prod.mk.injEq] at h
      all_goals (obtain ⟨-, rfl, rfl⟩ := h; exact ⟨rfl, rfl⟩)
    obtain ⟨rfl, rfl⟩ := key
    exact ⟨m, e, o, b, hsend, sp, cand, hdr, mk, hcand, rfl⟩
  · simp at h

/-- The sparse chain table after the first send: the epoch-0 entry with its send chain at counter 1. -/
def sentChains (c1 c2 : Array U8 32#usize) : alloc.vec.Vec (U64 × tacenta_spqr.Chains) :=
  Tacenta.UnitHeadroomSatisfiable.vecOf
    [(0#u64, { send := some { ck := c1, n := 1#u64 }, receive := some { ck := c2, n := 0#u64 } })]
    (singleton_length_le _)

/-- The Triple state after the first send from `initiatorTriple`: one classical message counted, the
epoch-0 send chain at counter 1, with the chain keys as arguments. -/
def sentTriple (a4 a5 rk cks prk c1 c2 : Array U8 32#usize) : tacenta_triple.State :=
  { classical :=
      { dhs_pub := a4, dhr_pub := some a5, rk := rk, cks := some cks, ckr := none,
        ns := 1#u32, nr := 0#u32, pn := 0#u32, skipped := alloc.vec.Vec.new tacenta_ratchet.SkippedKey,
        events := 0#u32, labels := tacenta_ratchet.LabelSet.Tacenta },
    post_quantum :=
      { rk := prk, epoch := 0#u64, chains := sentChains c1 c2,
        skipped := alloc.vec.Vec.new tacenta_spqr.Skipped, direction := tacenta_spqr.Direction.A2b } }

/-- Two arrays with the same bytes, as `UnitT3`'s byte reading sees them, are equal. -/
theorem array_eq_of_bytes {n : Usize} {a b : Array U8 n}
    (h : a.val.map (fun x : Std.U8 => UInt8.ofNat x.val) = b.val.map (fun x => UInt8.ofNat x.val)) :
    a = b := by
  apply Subtype.ext
  refine (List.map_injective_iff.mpr ?_) h
  intro x y hxy
  have hx : x.val < 256 := by scalar_tac
  have hy : y.val < 256 := by scalar_tac
  have := congrArg UInt8.toNat hxy
  simp at this
  scalar_tac

theorem triple_eq_sent (dh : DhView) {R : Type} {rc : rand_core_1.RngCore R}
    {crc : rand_core_1.CryptoRng R} {our : lifecycle.Identity} {bundle : lifecycle.PublishedBundle}
    (p : InitiatorOutputParts rc crc our bundle) (tripleNext : Model.Triple.State)
    (header : Model.Triple.Header) (messageKey : Model.Lifecycle.Key)
    (htriple : Model.Triple.sendDetailed (establishedModelOf dh p.session).triple 0 none =
      .ok (tripleNext, header, messageKey))
    (t : tacenta_triple.State)
    (hrel : Tacenta.SessionUnitTripleT3.StateRefines Tacenta.SessionUnitTripleT3.ratchetAbs
      Tacenta.SessionUnitTripleT3.spqrAbs t tripleNext) :
    ∃ cks c1, t = sentTriple p.ratchetBytes p.peerRatchetBytes p.rootKey cks p.sparseRoot c1
      p.sparseReceive := by
  simp [Model.Triple.sendDetailed, Model.Ratchet.sendDetailed, Model.SparseRatchet.sendDetailed,
    Model.SparseRatchet.maybeAdvanceDetailed, Model.SparseRatchet.findChains, establishedModelOf,
    InitiatorOutputParts.session, initiatorTriple, initChains, Tacenta.UnitHeadroomSatisfiable.vecOf,
    Tacenta.SessionUnitTripleT3.ratchetAbs, Tacenta.SessionUnitTripleT3.spqrAbs,
    Tacenta.SessionUnitSpqrT3.chainsEntryOf, Tacenta.SessionUnitSpqrT3.chainsOf,
    Tacenta.SessionUnitSpqrT3.chainOf, Model.State.u32Max, Model.SparseRatchet.u64Max] at htriple
  obtain ⟨rfl, -, -⟩ := htriple
  obtain ⟨hc, hq⟩ := hrel
  obtain ⟨⟨dhs, dhr, rk, cks, ckr, ns, nr, pn, sk, ev, lab⟩, ⟨prk, ep, ch, ssk, dir⟩⟩ := t
  simp [Tacenta.SessionUnitTripleT3.ratchetAbs, Tacenta.SessionUnitTripleT3.spqrAbs,
    Model.SparseRatchet.setChains] at hc hq
  obtain ⟨rfl, rfl, rfl, ⟨cks', rfl, -⟩, rfl, hns, hnr, hpn, hsk, hev⟩ := hc
  obtain ⟨hprk, hep, ⟨a, ⟨bs, br⟩, hch, hab⟩, hssk, hdir⟩ := hq
  have hprk' : prk = p.sparseRoot := array_eq_of_bytes hprk
  simp only [Tacenta.SessionUnitSpqrT3.chainsEntryOf, Tacenta.SessionUnitSpqrT3.chainsOf,
    Prod.mk.injEq, Model.SparseRatchet.Chains.mk.injEq] at hab
  obtain ⟨ha, hbs, hbr⟩ := hab
  rcases bs with _ | ⟨sck, sn⟩
  · simp at hbs
  rcases br with _ | ⟨rck, rn⟩
  · simp at hbr
  simp only [Option.map_some, Option.some.injEq, Tacenta.SessionUnitSpqrT3.chainOf,
    Model.SparseRatchet.Chain.mk.injEq] at hbs hbr
  obtain ⟨-, hsn⟩ := hbs
  obtain ⟨hrck, hrn⟩ := hbr
  have hrck' : rck = p.sparseReceive := array_eq_of_bytes hrck
  cases lab
  cases dir <;> simp [Tacenta.SessionUnitSpqrT3.directionOf] at hdir
  refine ⟨cks', sck, ?_⟩
  subst hprk' hrck'
  have hns' : ns = 1#u32 := UScalar.eq_of_val_eq (by simpa using hns)
  have hnr' : nr = 0#u32 := UScalar.eq_of_val_eq (by simpa using hnr)
  have hpn' : pn = 0#u32 := UScalar.eq_of_val_eq (by simpa using hpn)
  have hev' : ev = 0#u32 := UScalar.eq_of_val_eq (by simpa using hev)
  have hep' : ep = 0#u64 := UScalar.eq_of_val_eq (by simpa using hep)
  have ha' : a = 0#u64 := UScalar.eq_of_val_eq (by simpa using ha)
  have hsn' : sn = 1#u64 := UScalar.eq_of_val_eq (by simpa using hsn)
  have hrn' : rn = 0#u64 := UScalar.eq_of_val_eq (by simpa using hrn)
  subst hns' hnr' hpn' hev' hep' ha' hsn' hrn'
  have hsk' : sk = alloc.vec.Vec.new tacenta_ratchet.SkippedKey := Subtype.ext hsk
  have hssk' : ssk = alloc.vec.Vec.new tacenta_spqr.Skipped := Subtype.ext hssk
  have hch' : ch = sentChains sck p.sparseReceive := Subtype.ext hch
  subst hsk' hssk' hch'
  rfl

/-- `Triple::invariant` of the Triple after the first send, given its two public keys are canonical. -/
theorem sentTriple_invariant (a4 a5 rk cks prk c1 c2 : Array U8 32#usize)
    (h4 : Tacenta.SessionUnitT1.canonicalX25519 a4 = true)
    (h5 : Tacenta.SessionUnitT1.canonicalX25519 a5 = true) :
    tacenta_triple.State.invariant (sentTriple a4 a5 rk cks prk c1 c2) = ok true := by
  have h1 : tacenta_ratchet.State.invariant
      (sentTriple a4 a5 rk cks prk c1 c2).classical = ok true := by
    rw [Tacenta.SessionUnitRatchetImportInv.Ratchet.invariant_true_iff]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [sentTriple, alloc.vec.Vec.new, tacenta_ratchet.MAX_SKIPPED_STORE]
    · simp [sentTriple, U32.max_eq]
    · simp [sentTriple, alloc.vec.Vec.new]
    · simp [sentTriple, alloc.vec.Vec.new]
    · simp [sentTriple]
    · simpa [sentTriple] using h4
    · simpa [sentTriple] using h5
    · simp [sentTriple, alloc.vec.Vec.new]
  have h2 : tacenta_spqr.State.invariant
      (sentTriple a4 a5 rk cks prk c1 c2).post_quantum = ok true := by
    rw [Tacenta.SessionUnitRatchetImportInv.Spqr.invariant_true_iff]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [sentTriple, alloc.vec.Vec.new, tacenta_spqr.MAX_SKIPPED_STORE]
    · simp [sentTriple, sentChains, Tacenta.UnitHeadroomSatisfiable.vecOf,
        core.num.U64.saturating_add, UScalar.saturating_add, tacenta_spqr.EPOCHS_KEPT, U64.max_eq]
      decide
    · simp [sentTriple, sentChains, Tacenta.UnitHeadroomSatisfiable.vecOf]
    · simp [sentTriple, sentChains, Tacenta.UnitHeadroomSatisfiable.vecOf]
    · simp [sentTriple, alloc.vec.Vec.new]
    · simp [sentTriple, alloc.vec.Vec.new]
  simp only [sentTriple] at h1 h2
  unfold tacenta_triple.State.invariant
  simp [h1, h2, sentTriple, tacenta_spqr.State.impl.direction,
    tacenta_ratchet.State.started_as_sender]

/-- The session after a successful first send, from the parts: the Triple after the send, the agreement
at `KeysSampled` epoch 1, every other field the establishment's. -/
def sentSession {R : Type} {rc : rand_core_1.RngCore R} {crc : rand_core_1.CryptoRng R}
    {our : lifecycle.Identity} {bundle : lifecycle.PublishedBundle}
    (p : InitiatorOutputParts rc crc our bundle) (cks c1 : Array U8 32#usize) (auth : tacenta_braid.Auth)
    (kp : tacenta_kem.IncrementalKeyPair) (enc : tacenta_erasure.Encoder) : lifecycle.Session :=
  { p.session with
    triple := sentTriple p.ratchetBytes p.peerRatchetBytes p.rootKey cks p.sparseRoot c1 p.sparseReceive
    braid := ⟨tacenta_braid.State.KeysSampled 1#u64 auth kp enc⟩ }

/-- `Session::structural_invariant` of the session after the first send: as at the establishment output,
with the agreement's epoch, tag and role read off `KeysSampled` at epoch 1. -/
theorem structural_sent {R : Type} {rc : rand_core_1.RngCore R} {crc : rand_core_1.CryptoRng R}
    {our : lifecycle.Identity} {bundle : lifecycle.PublishedBundle}
    (hpub : DhPublicValid) (hct : KemCiphertextLenOf)
    (hoeq : OptionEqU64Shape (@core.option.Option.Insts.CoreCmpPartialEqOption.eq))
    (p : InitiatorOutputParts rc crc our bundle) (cks c1 : Array U8 32#usize) (auth : tacenta_braid.Auth)
    (kp : tacenta_kem.IncrementalKeyPair) (enc : tacenta_erasure.Encoder) :
    lifecycle.Session.structural_invariant (sentSession p cks c1 auth kp enc) = ok true := by
  have hv := identity_public_valid hpub p.hOurPublic
  have hc := (dhPublicValid_valid hpub p.hEphemeralPublic).2
  obtain ⟨n, hctl, hlen0⟩ := kemCiphertextLenOf_is.mp hct rc crc _ _ _ _ _ p.hEncapsulate
  have hlen : alloc.vec.Vec.len p.kemCiphertext = n := by
    apply UScalar.eq_of_val_eq; simp [alloc.vec.Vec.len, hlen0]
  unfold lifecycle.Session.structural_invariant
  simp [sentSession, InitiatorOutputParts.session, sentTriple, p.hRatchetPublic, p.hRatchetBytes,
    tacenta_triple.State.sending_public, tacenta_ratchet.State.sending_public, array_ne_self,
    tacenta_braid.Braid.failed, tacenta_braid.Braid.is_initiator, tacenta_braid.State.epoch,
    lifecycle.Session.is_responder, p.hIdentityAd, vec_ne_self, tacenta_triple.State.direction,
    tacenta_spqr.State.impl.direction, hv, p.hPeerValid, hc, hctl, hlen,
    tacenta_braid.Braid.epoch, tacenta_triple.State.epoch, tacenta_spqr.State.impl.epoch,
    tacenta_braid.Braid.state_tag, lift, tacenta_spqr.Direction.Insts.CoreCmpPartialEqDirection.eq]
  have h01 : U64.checked_add 0#u64 1#u64 = some 1#u64 := by decide
  rw [h01, hoeq]
  rfl

/-- `Braid::invariant` of a `KeysSampled` agreement at epoch 1: the encoder passes `Encoder::invariant` and
is sized for `HEADER_LEN + MAC_LEN` bytes (96, with `HEADER_LEN` 64), and `key_pair_valid` returns
`true`. -/
theorem keysSampled_invariant (hk : tacenta_kem.HEADER_LEN = ok 64#usize) (auth : tacenta_braid.Auth)
    (kp : tacenta_kem.IncrementalKeyPair) (enc : tacenta_erasure.Encoder)
    (henc : tacenta_erasure.Encoder.invariant enc = ok true)
    (hsized : ∀ len : Usize, len.val = 96 → tacenta_braid.encoder_sized enc len = ok true)
    (hkp : tacenta_braid.key_pair_valid kp = ok true) :
    tacenta_braid.Braid.invariant ⟨tacenta_braid.State.KeysSampled 1#u64 auth kp enc⟩ = ok true := by
  unfold tacenta_braid.Braid.invariant
  simp only [henc, hk, bind_tc_ok, if_true]
  have h1 : (1#u64 : U64) >= 1#u64 := by decide
  simp only [h1, if_true]
  obtain ⟨x, hx, hxv⟩ : ∃ x : Usize, 64#usize + tacenta_braid.MAC_LEN = ok x ∧ x.val = 96 := by
    have : tacenta_braid.MAC_LEN.val = 32 := by simp [tacenta_braid.MAC_LEN]
    have h := Tacenta.UnitSatisfiabilityBraidAgreements.usize_max_ge 96 (by norm_num)
    obtain ⟨x, hx, hxv⟩ := Std.WP.spec_imp_exists (Usize.add_spec (x := 64#usize)
      (y := tacenta_braid.MAC_LEN) (by scalar_tac))
    exact ⟨x, hx, by scalar_tac⟩
  rw [hx]
  simp only [bind_tc_ok, hsized x hxv, if_true, hkp]

/-- `Session::invariant` of the session after the first send, given its agreement's invariant. -/
theorem sent_invariant {R : Type} {rc : rand_core_1.RngCore R} {crc : rand_core_1.CryptoRng R}
    {our : lifecycle.Identity} {bundle : lifecycle.PublishedBundle}
    (hpub : DhPublicValid) (hct : KemCiphertextLenOf)
    (hoeq : OptionEqU64Shape (@core.option.Option.Insts.CoreCmpPartialEqOption.eq))
    (p : InitiatorOutputParts rc crc our bundle) (cks c1 : Array U8 32#usize) (auth : tacenta_braid.Auth)
    (kp : tacenta_kem.IncrementalKeyPair) (enc : tacenta_erasure.Encoder)
    (hbraid : tacenta_braid.Braid.invariant ⟨tacenta_braid.State.KeysSampled 1#u64 auth kp enc⟩ =
      ok true) :
    lifecycle.Session.invariant (sentSession p cks c1 auth kp enc) = ok true := by
  unfold lifecycle.Session.invariant
  rw [structural_sent hpub hct hoeq p cks c1 auth kp enc]
  simp only [Aeneas.Std.bind_tc_ok, if_true]
  unfold lifecycle.Session.leaf_invariants
  have h4 := dhPublicValid_canonical hpub p.hRatchetPublic p.hRatchetBytes
  have h5 := canonical_of_is_canonical_key p.hPeerRatchetBytes p.hPeerRatchetCanonical
  simp only [sentSession]
  rw [sentTriple_invariant _ _ _ _ _ _ _ h4 h5]
  simpa using hbraid

/-- `key_pair_valid` returns `true` at a key pair whose header is a model seed followed by the model's hash
of it and its vector, of the sizes `KeyGenSizesOf` states, under `ValidateEkAgrees`. -/
theorem keyPairValid_of_header {K : Model.Braid.Kem}
    (hval : Tacenta.SessionUnitBraidT3.ValidateEkAgrees K) (kp : tacenta_kem.IncrementalKeyPair)
    (h v : alloc.vec.Vec Std.U8) (hh : tacenta_kem.IncrementalKeyPair.header kp = ok h)
    (hv : tacenta_kem.IncrementalKeyPair.ek_vector kp = ok v) (ekSeed ekVector : Model.Braid.Bytes)
    (hhval : Tacenta.SessionUnitBraidT3.vecOf h = ekSeed ++ K.hashEk ekSeed ekVector)
    (hvval : Tacenta.SessionUnitBraidT3.vecOf v = ekVector) (hs : ekSeed.length = 32)
    (hvl : ekVector.length = K.ekSize) (hhl : (K.hashEk ekSeed ekVector).length = 32) :
    tacenta_braid.key_pair_valid kp = ok true := by
  have hvlen : (alloc.vec.Vec.deref v).length = K.ekSize := by
    rw [← hvl, ← hvval]; simp [Tacenta.SessionUnitBraidT3.vecOf, alloc.vec.Vec.deref]
  obtain ⟨r, hr, hiff⟩ := hval (alloc.vec.Vec.deref h) (alloc.vec.Vec.deref v) ekSeed
    (K.hashEk ekSeed ekVector) hs hhl hvlen
    (by simpa [Tacenta.SessionUnitBraidT3.sliceOf, Tacenta.SessionUnitBraidT3.vecOf,
      alloc.vec.Vec.deref] using hhval)
  have hsv : Tacenta.SessionUnitBraidT3.sliceOf (alloc.vec.Vec.deref v) = ekVector := by
    simpa [Tacenta.SessionUnitBraidT3.sliceOf, Tacenta.SessionUnitBraidT3.vecOf,
      alloc.vec.Vec.deref] using hvval
  rw [hsv] at hiff
  have hrt : r = true := hiff.mpr rfl
  subst hrt
  unfold tacenta_braid.key_pair_valid
  simp only [hh, hv, bind_tc_ok]
  exact hr

/-- An encoder that refines the model encoder of a 96-byte message advanced once passes
`Encoder::invariant` and is sized for 96 bytes, under `DivCeilValue` and `ErasureAgrees`: its provenance
is `Encoder::new` of that message and one `next_chunk`. -/
theorem encoder_of_refines (hdiv : Tacenta.SessionUnitDecoderBound.DivCeilValue)
    (hea : Tacenta.SessionUnitBraidT3.ErasureAgrees) (enc : tacenta_erasure.Encoder)
    (m : Model.Braid.Bytes) (hm : m.length = 96)
    (hr : Tacenta.SessionUnitBraidT3.EncoderRefines enc (Model.Braid.encode m).nextChunk.2) :
    tacenta_erasure.Encoder.invariant enc = ok true ∧
      ∀ len : Usize, len.val = 96 → tacenta_braid.encoder_sized enc len = ok true := by
  obtain ⟨src, enc0, hsrc, hnew, hstep⟩ := hr.1
  simp only [Model.Braid.encode, Model.Braid.Encoder.nextChunk] at hsrc hstep
  obtain ⟨enc0', enc1', c, hnew', hnext', -, -, -, hinv, hsized⟩ :=
    Tacenta.UnitHeldKemWitness.held_encoder hdiv hea m hm
  have hsrc' : src = Tacenta.UnitSatisfiabilityBraidStates.sliceOfBytes m
      (by rw [hm]; exact Tacenta.UnitSatisfiabilityBraidAgreements.usize_max_ge 96 (by norm_num)) := by
    apply Subtype.ext
    simp only [Tacenta.UnitSatisfiabilityBraidStates.sliceOfBytes]
    rw [← hsrc]
    exact (Tacenta.UnitKemWrapperModel.bytesOf_map_u8 src.val).symm
  subst hsrc'
  rw [hnew'] at hnew
  cases hnew
  obtain ⟨c', e', hnc, he'⟩ := hstep
  rw [hnext'] at hnc
  cases hnc
  subst he'
  exact ⟨hinv, hsized⟩

/-- **After a successful first send, the session passes `Session::invariant`**, under the hypotheses of
`established_initiator_encrypt_refines` and, in addition, the establishment's laws `DhPublicValid` and
`OptionEqU64Shape` (as for the establishment output itself), the KEM agreements `KemLenAgrees` and
`ValidateEkAgrees` at `oracle.braidKem`, the size law `KeyGenSizesOf` of the model KEM, and `DivCeilValue`.
The session is the establishment's with the Triple after the send (`sentTriple`: one classical message
counted, the epoch-0 send chain at counter 1) and the agreement at `KeysSampled` epoch 1, whose key pair has
the header key generation returned and whose encoder is `Encoder::new` of that header and its MAC, advanced
once. -/
theorem established_encrypt_successor_admissible [Tacenta.SessionUnitT1.DerivedKeysModel]
    {R E : Type}
    (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView) (kem : KemView)
    (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
    (braid : BraidSendRefinementContracts rc oracle.braidKem) (triple : TripleSendRefinementContracts)
    (aead : Tacenta.UnitLifecycleT1.AeadSealBounded) (dhCodec : Tacenta.UnitLifecycleT1.DhCodecTotal)
    (oracleOf : OracleOf rc crc dh kem trace oracle) (codec : DhCodecOf dh)
    (codewordView : CodewordViewSendOf view)
    (hz80 : Tacenta.SessionUnitT3.ZeroizingRoundTrips80)
    (hz32 : ZeroizingRoundTrips (Array Std.U8 32#usize))
    (hzKeys : ZeroizingRoundTrips
      (Array Std.U8 32#usize × Array Std.U8 32#usize × Array Std.U8 16#usize))
    (hgen : KeyGenSeededFor oracle.braidKem rc crc trace) (hct : KemCiphertextLenOf)
    (hbound : KemCiphertextLenBound)
    (hpub : DhPublicValid)
    (hoeq : OptionEqU64Shape (@core.option.Option.Insts.CoreCmpPartialEqOption.eq))
    (hlen : Tacenta.SessionUnitBraidT3.KemLenAgrees oracle.braidKem)
    (hval : Tacenta.SessionUnitBraidT3.ValidateEkAgrees oracle.braidKem)
    (hsizes : KeyGenSizesOf oracle.braidKem) (hdiv : Tacenta.SessionUnitDecoderBound.DivCeilValue)
    (rcE : rand_core_1.RngCore E) (crcE : rand_core_1.CryptoRng E)
    (our : lifecycle.Identity) (bundle : lifecycle.PublishedBundle)
    (expected : tacenta_boundary.dh.PublicKeyBytes) (rng0 rng1 : E) (s : lifecycle.Session)
    (h : lifecycle.establish_initiator_for rcE crcE our bundle expected rng0 =
      ok (core.result.Result.Ok s, rng1))
    (plaintext : Slice Std.U8) (hroom : plaintext.val.length + 65770 ≤ Usize.max)
    (rng : R) (htrace : trace rng = oracle.draws)
    (hdraws : ∃ d1 d2 rest, trace rng = d1 :: d2 :: rest)
    (bytes : alloc.vec.Vec Std.U8) (s' : lifecycle.Session) (rng' : R)
    (hcall : lifecycle.Session.encrypt rc crc s plaintext rng =
      ok (core.result.Result.Ok bytes, s', rng')) :
    lifecycle.Session.invariant s' = ok true := by
  obtain ⟨d1, d2, rest, htr⟩ := hdraws
  obtain ⟨output, hcall', -, hcases⟩ := established_encrypt_outcomes rc crc trace dh kem view oracle
    braid triple aead dhCodec oracleOf codec codewordView hz80 hz32 hzKeys hgen hct hbound rcE crcE our
    bundle expected rng0 rng1 s h plaintext hroom rng htrace d1 d2 rest htr
  rw [hcall] at hcall'
  cases hcall'
  obtain ⟨p, rfl⟩ := establish_initiator_for_parts rcE crcE our bundle expected rng0 rng1 _ h
  rcases hcases with ⟨-, hres, -⟩ | ⟨dk, ekSeed, ekVector, hkg, bytes', -, hframe, ⟨auth, kp, enc, hst⟩,
      tripleNext, messageKey, chunk, encoder, pending, a, ⟨header, htriple⟩, hbraidM, hnc, -, -, hrel⟩
  · cases hres
  simp only at hframe hst hrel
  have ha : a = Tacenta.SessionUnitBraidT3.AuthOf p.auth := by
    have : (Model.Braid.BraidState.keysUnsampled 1 (Tacenta.SessionUnitBraidT3.AuthOf p.auth) :
        Model.Braid.BraidState) = .keysUnsampled 1 a := hbraidM
    injection this with _ h2
    exact h2.symm
  subst ha
  -- The Triple: the relation fixes it as `sentTriple` up to the two advanced chain keys.
  obtain ⟨cks', c1', hcand⟩ := triple_eq_sent dh p tripleNext header messageKey htriple s'.triple
    hrel.triple
  -- The agreement: the relation at `keysSampled` gives the vector and the encoder's provenance.
  have hb := hrel.braid
  simp only [hst] at hb
  obtain ⟨-, -, ⟨-, ⟨v, hv, hvval⟩, -⟩, hencR⟩ := hb
  -- The key pair's header is the one key generation returned: from the code's send at the fixed
  -- randomness.
  obtain ⟨m, e, o, b, hsend, -, cand, -, -, -, hs'⟩ :=
    encrypt_ok_parts rc crc p.session plaintext rng bytes s' rng' hcall
  obtain ⟨rng'', -, hans⟩ := hgen rng d1 d2 rest htr
  have hrel0 : Tacenta.SessionUnitBraidT3.StateRefines oracle.braidKem p.session.braid.state
      (.keysUnsampled (1#u64 : Std.U64).val (Tacenta.SessionUnitBraidT3.AuthOf p.auth)) := ⟨rfl, rfl⟩
  obtain ⟨res, hcallB, hpostB⟩ := Std.WP.spec_imp_exists
    (braid_send_keysUnsampled_pinned braid crc p.session.braid rng hrel0
      (Model.Lifecycle.braidRandomness (d1 ++ d2)) rng'' hans)
  rw [hsend] at hcallB
  cases hcallB
  have hbs : b.state = .KeysSampled 1#u64 auth kp enc := by
    rw [← hst, hs']
  obtain ⟨hh0, hhh, dk', ekSeed', ekVector', hkg', hhval⟩ := hpostB.2.2.2.2 _ _ _ _ hbs
  rw [hkg] at hkg'
  obtain ⟨rfl, rfl, rfl⟩ : dk = dk' ∧ ekSeed = ekSeed' ∧ ekVector = ekVector' := by
    simpa using hkg'
  obtain ⟨hs32, hvl, hhl⟩ := hsizes _ _ _ _ hkg
  have hkp := keyPairValid_of_header hval kp hh0 v hhh hv ekSeed ekVector hhval hvval hs32 hvl hhl
  -- The encoder: the model's header-plus-MAC message is 96 bytes.
  have hm : ((ekSeed ++ oracle.braidKem.hashEk ekSeed ekVector) ++
      (Tacenta.SessionUnitBraidT3.AuthOf p.auth).macHdr 1
        (ekSeed ++ oracle.braidKem.hashEk ekSeed ekVector)).length = 96 := by
    simp [Model.Braid.Auth.macHdr, Model.Kdf.hmac_length, Model.Kdf.hashLen, hs32, hhl]
  have hencoder : encoder = (Model.Braid.encode ((ekSeed ++ oracle.braidKem.hashEk ekSeed ekVector) ++
      (Tacenta.SessionUnitBraidT3.AuthOf p.auth).macHdr 1
        (ekSeed ++ oracle.braidKem.hashEk ekSeed ekVector))).nextChunk.2 := by
    rw [hnc]
  subst hencoder
  obtain ⟨henc, hsized⟩ := encoder_of_refines hdiv braid.hea enc _ hm hencR
  obtain ⟨⟨hv64, hhd, hhv⟩, -⟩ := hlen
  have hk : tacenta_kem.HEADER_LEN = ok 64#usize := by
    rw [hhd]; congr 1; exact UScalar.eq_of_val_eq (by simpa [Model.Braid.headerSize] using hhv)
  have hbraidInv := keysSampled_invariant hk auth kp enc henc hsized hkp
  -- The session is `sentSession`.
  have hbr : s'.braid = ⟨tacenta_braid.State.KeysSampled 1#u64 auth kp enc⟩ := by
    cases hb2 : s'.braid with
    | mk st => rw [hb2] at hst; simp only at hst; rw [hst]
  have hs'' : s' = sentSession p cks' c1' auth kp enc := by
    rw [hframe, hcand, hbr]
    rfl
  rw [hs'']
  exact sent_invariant hpub hct hoeq p cks' c1' auth kp enc hbraidInv

/-- **Every session-side premise the `decrypt` refinement takes holds at the session the first send leaves**,
with the model step's session: `Session::invariant`, the relation and the four counter ceilings, and
`HonestChunk` for every model message, which holds trivially (`True`) at a `keysSampled` agreement, which
feeds no decoder.  Under the
hypotheses of `established_encrypt_successor_admissible`.  The next call's boundary records, trace equation,
chunk relation and draw remain the caller's. -/
theorem established_encrypt_successor_hypotheses [Tacenta.SessionUnitT1.DerivedKeysModel]
    {R E : Type}
    (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView) (kem : KemView)
    (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
    (braid : BraidSendRefinementContracts rc oracle.braidKem) (triple : TripleSendRefinementContracts)
    (aead : Tacenta.UnitLifecycleT1.AeadSealBounded) (dhCodec : Tacenta.UnitLifecycleT1.DhCodecTotal)
    (oracleOf : OracleOf rc crc dh kem trace oracle) (codec : DhCodecOf dh)
    (codewordView : CodewordViewSendOf view)
    (hz80 : Tacenta.SessionUnitT3.ZeroizingRoundTrips80)
    (hz32 : ZeroizingRoundTrips (Array Std.U8 32#usize))
    (hzKeys : ZeroizingRoundTrips
      (Array Std.U8 32#usize × Array Std.U8 32#usize × Array Std.U8 16#usize))
    (hgen : KeyGenSeededFor oracle.braidKem rc crc trace) (hct : KemCiphertextLenOf)
    (hbound : KemCiphertextLenBound)
    (hpub : DhPublicValid)
    (hoeq : OptionEqU64Shape (@core.option.Option.Insts.CoreCmpPartialEqOption.eq))
    (hlen : Tacenta.SessionUnitBraidT3.KemLenAgrees oracle.braidKem)
    (hval : Tacenta.SessionUnitBraidT3.ValidateEkAgrees oracle.braidKem)
    (hsizes : KeyGenSizesOf oracle.braidKem) (hdiv : Tacenta.SessionUnitDecoderBound.DivCeilValue)
    (rcE : rand_core_1.RngCore E) (crcE : rand_core_1.CryptoRng E)
    (our : lifecycle.Identity) (bundle : lifecycle.PublishedBundle)
    (expected : tacenta_boundary.dh.PublicKeyBytes) (rng0 rng1 : E) (s : lifecycle.Session)
    (h : lifecycle.establish_initiator_for rcE crcE our bundle expected rng0 =
      ok (core.result.Result.Ok s, rng1))
    (plaintext : Slice Std.U8) (hroom : plaintext.val.length + 65770 ≤ Usize.max)
    (rng : R) (htrace : trace rng = oracle.draws)
    (hdraws : ∃ d1 d2 rest, trace rng = d1 :: d2 :: rest)
    (bytes : alloc.vec.Vec Std.U8) (s' : lifecycle.Session) (rng' : R)
    (hcall : lifecycle.Session.encrypt rc crc s plaintext rng =
      ok (core.result.Result.Ok bytes, s', rng')) :
    lifecycle.Session.invariant s' = ok true ∧
      SessionRefines dh oracle.braidKem s'
        (Model.Lifecycle.encrypt view oracle (establishedModelOf dh s) (sliceOf plaintext)).session ∧
      Tacenta.UnitLifecycleDecryptRunBounds.CounterHeadroom s' ∧
      ∀ msg, Tacenta.SessionUnitBraidT3.HonestChunk
        (Model.Lifecycle.encrypt view oracle (establishedModelOf dh s) (sliceOf plaintext)).session.braid
        msg := by
  obtain ⟨hrel, -, a, dk, ekVector, encoder, hb⟩ := established_encrypt_successor_refines rc crc trace
    dh kem view oracle braid triple aead dhCodec oracleOf codec codewordView hz80 hz32 hzKeys hgen hct
    hbound rcE crcE our bundle expected rng0 rng1 s h plaintext hroom rng htrace hdraws bytes s' rng'
    hcall
  refine ⟨established_encrypt_successor_admissible rc crc trace dh kem view oracle braid triple aead
      dhCodec oracleOf codec codewordView hz80 hz32 hzKeys hgen hct hbound hpub hoeq hlen hval hsizes
      hdiv rcE crcE our bundle expected rng0 rng1 s h plaintext hroom rng htrace hdraws bytes s' rng'
      hcall, hrel,
    established_encrypt_successor_counterHeadroom rc crc trace dh kem view oracle braid triple aead
      dhCodec oracleOf codec codewordView hz80 hz32 hzKeys hgen hct hbound rcE crcE our bundle expected
      rng0 rng1 s h plaintext hroom rng htrace hdraws bytes s' rng' hcall, ?_⟩
  intro msg mc _ _
  rw [hb]
  cases msg.type <;> trivial

/-- Two authenticators the model reads alike are equal. -/
theorem authOf_injective {a b : tacenta_braid.Auth}
    (h : Tacenta.SessionUnitBraidT3.AuthOf a = Tacenta.SessionUnitBraidT3.AuthOf b) : a = b := by
  obtain ⟨ar, am⟩ := a
  obtain ⟨br, bm⟩ := b
  simp only [Tacenta.SessionUnitBraidT3.AuthOf, Model.Braid.Auth.mk.injEq] at h
  obtain ⟨hr, hm⟩ := h
  have hr' : ar = br := array_eq_of_bytes hr
  have hm' : am = bm := array_eq_of_bytes hm
  subst hr' hm'
  rfl

/-- **The session a successful first send leaves, exactly**, under the hypotheses of
`established_initiator_encrypt_refines`: the establishment's session with the Triple after the send
(`sentTriple`: classical message counter 1, previous chain 0, clock 0, no stored key, the epoch-0 sparse entry
with its send chain at counter 1 and its receive chain at counter 0, sparse epoch 0) and the agreement at
`KeysSampled` epoch 1 with the establishment's own authenticator; only the two advanced chain keys, the key
pair and the encoder are left as values. -/
theorem established_encrypt_successor_shape [Tacenta.SessionUnitT1.DerivedKeysModel]
    {R E : Type}
    (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView) (kem : KemView)
    (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
    (braid : BraidSendRefinementContracts rc oracle.braidKem) (triple : TripleSendRefinementContracts)
    (aead : Tacenta.UnitLifecycleT1.AeadSealBounded) (dhCodec : Tacenta.UnitLifecycleT1.DhCodecTotal)
    (oracleOf : OracleOf rc crc dh kem trace oracle) (codec : DhCodecOf dh)
    (codewordView : CodewordViewSendOf view)
    (hz80 : Tacenta.SessionUnitT3.ZeroizingRoundTrips80)
    (hz32 : ZeroizingRoundTrips (Array Std.U8 32#usize))
    (hzKeys : ZeroizingRoundTrips
      (Array Std.U8 32#usize × Array Std.U8 32#usize × Array Std.U8 16#usize))
    (hgen : KeyGenSeededFor oracle.braidKem rc crc trace) (hct : KemCiphertextLenOf)
    (hbound : KemCiphertextLenBound)
    (rcE : rand_core_1.RngCore E) (crcE : rand_core_1.CryptoRng E)
    (our : lifecycle.Identity) (bundle : lifecycle.PublishedBundle)
    (expected : tacenta_boundary.dh.PublicKeyBytes) (rng0 rng1 : E) (s : lifecycle.Session)
    (h : lifecycle.establish_initiator_for rcE crcE our bundle expected rng0 =
      ok (core.result.Result.Ok s, rng1))
    (plaintext : Slice Std.U8) (hroom : plaintext.val.length + 65770 ≤ Usize.max)
    (rng : R) (htrace : trace rng = oracle.draws)
    (hdraws : ∃ d1 d2 rest, trace rng = d1 :: d2 :: rest)
    (bytes : alloc.vec.Vec Std.U8) (s' : lifecycle.Session) (rng' : R)
    (hcall : lifecycle.Session.encrypt rc crc s plaintext rng =
      ok (core.result.Result.Ok bytes, s', rng')) :
    ∃ (p : InitiatorOutputParts rcE crcE our bundle) (cks c1 : Array U8 32#usize)
      (kp : tacenta_kem.IncrementalKeyPair) (enc : tacenta_erasure.Encoder),
      s = p.session ∧ s' = sentSession p cks c1 p.auth kp enc := by
  obtain ⟨d1, d2, rest, htr⟩ := hdraws
  obtain ⟨output, hcall', -, hcases⟩ := established_encrypt_outcomes rc crc trace dh kem view oracle
    braid triple aead dhCodec oracleOf codec codewordView hz80 hz32 hzKeys hgen hct hbound rcE crcE our
    bundle expected rng0 rng1 s h plaintext hroom rng htrace d1 d2 rest htr
  rw [hcall] at hcall'
  cases hcall'
  obtain ⟨p, rfl⟩ := establish_initiator_for_parts rcE crcE our bundle expected rng0 rng1 _ h
  rcases hcases with ⟨-, hres, -⟩ | ⟨dk, ekSeed, ekVector, -, bytes', -, hframe, ⟨auth, kp, enc, hst⟩,
      tripleNext, messageKey, chunk, encoder, pending, a, ⟨header, htriple⟩, hbraidM, -, -, -, hrel⟩
  · cases hres
  simp only at hframe hst hrel
  have ha : a = Tacenta.SessionUnitBraidT3.AuthOf p.auth := by
    have : (Model.Braid.BraidState.keysUnsampled 1 (Tacenta.SessionUnitBraidT3.AuthOf p.auth) :
        Model.Braid.BraidState) = .keysUnsampled 1 a := hbraidM
    injection this with _ h2
    exact h2.symm
  subst ha
  obtain ⟨cks', c1', hcand⟩ := triple_eq_sent dh p tripleNext header messageKey htriple s'.triple
    hrel.triple
  have hb := hrel.braid
  simp only [hst] at hb
  obtain ⟨-, hauth, -, -⟩ := hb
  have hauth' : auth = p.auth := authOf_injective hauth
  subst hauth'
  have hbr : s'.braid = ⟨tacenta_braid.State.KeysSampled 1#u64 p.auth kp enc⟩ := by
    cases hb2 : s'.braid with
    | mk st => rw [hb2] at hst; simp only at hst; rw [hst]
  refine ⟨p, cks', c1', kp, enc, rfl, ?_⟩
  rw [hframe, hcand, hbr]
  rfl

end Successor


/-! ## The successor's premise list holds together, and the success arm reaches it -/

open Tacenta.UnitHeadroomInvariant (OptionEqU64Shape) in
/-- The hypotheses of `established_encrypt_successor_hypotheses` as one record: those of the call, and the
six the successor's invariant adds. -/
structure EstablishedEncryptSuccessorHypotheses {R E : Type} (rc : rand_core_1.RngCore R)
    (crc : rand_core_1.CryptoRng R) (trace : R → List Model.Lifecycle.Key) (dh : DhView)
    (kem : KemView) (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
    (rcE : rand_core_1.RngCore E) (crcE : rand_core_1.CryptoRng E) (our : lifecycle.Identity)
    (bundle : lifecycle.PublishedBundle) (expected : tacenta_boundary.dh.PublicKeyBytes)
    (rng0 rng1 : E) (s : lifecycle.Session) (plaintext : Slice Std.U8) (rng : R) : Prop
    extends EstablishedEncryptHypotheses rc crc trace dh kem view oracle rcE crcE our bundle expected
      rng0 rng1 s plaintext rng where
  dhPublicValid : DhPublicValid
  optionEq : OptionEqU64Shape (@core.option.Option.Insts.CoreCmpPartialEqOption.eq)
  kemLen : Tacenta.SessionUnitBraidT3.KemLenAgrees oracle.braidKem
  validateEk : Tacenta.SessionUnitBraidT3.ValidateEkAgrees oracle.braidKem
  keyGenSizes : KeyGenSizesOf oracle.braidKem
  divCeil : Tacenta.SessionUnitDecoderBound.DivCeilValue

/-- The record is the hypothesis list of `established_encrypt_successor_hypotheses`: from it, that theorem
applies to every successful call. -/
theorem EstablishedEncryptSuccessorHypotheses.successor {R E : Type} {rc : rand_core_1.RngCore R}
    {crc : rand_core_1.CryptoRng R} {trace : R → List Model.Lifecycle.Key} {dh : DhView}
    {kem : KemView} {view : Model.Lifecycle.CodewordView} {oracle : Model.Lifecycle.Oracle}
    {rcE : rand_core_1.RngCore E} {crcE : rand_core_1.CryptoRng E} {our : lifecycle.Identity}
    {bundle : lifecycle.PublishedBundle} {expected : tacenta_boundary.dh.PublicKeyBytes}
    {rng0 rng1 : E} {s : lifecycle.Session} {plaintext : Slice Std.U8} {rng : R}
    (H : EstablishedEncryptSuccessorHypotheses rc crc trace dh kem view oracle rcE crcE our bundle
      expected rng0 rng1 s plaintext rng)
    (bytes : alloc.vec.Vec Std.U8) (s' : lifecycle.Session) (rng' : R)
    (hcall : lifecycle.Session.encrypt rc crc s plaintext rng =
      ok (core.result.Result.Ok bytes, s', rng')) :
    lifecycle.Session.invariant s' = ok true ∧
      SessionRefines dh oracle.braidKem s'
        (Model.Lifecycle.encrypt view oracle (establishedModelOf dh s) (sliceOf plaintext)).session ∧
      Tacenta.UnitLifecycleDecryptRunBounds.CounterHeadroom s' ∧
      ∀ msg, Tacenta.SessionUnitBraidT3.HonestChunk
        (Model.Lifecycle.encrypt view oracle (establishedModelOf dh s) (sliceOf plaintext)).session.braid
        msg := by
  obtain ⟨inst⟩ := H.derivedKeys
  exact established_encrypt_successor_hypotheses rc crc trace dh kem view oracle H.braid H.triple H.aead
    H.dhCodec H.oracleOf H.codec H.codewordView H.zeroizing80 H.zeroizing32 H.zeroizingKeys H.keyGen
    H.kemCiphertextLen H.kemCiphertextBound H.dhPublicValid H.optionEq H.kemLen H.validateEk
    H.keyGenSizes H.divCeil rcE crcE our bundle expected rng0 rng1 s H.established plaintext H.room rng
    H.trace_eq H.draws bytes s' rng' hcall

/-- **Every hypothesis of `established_encrypt_successor_hypotheses` holds together at the real
constants**, under the laws of `established_encrypt_hypotheses_jointly_satisfiable` and the size law
`KeyGenSizesOf K` of the model KEM: the six the successor adds come from the decrypt laws (`OptionEqU64Shape`,
the KEM length and validation agreements, `DivCeilValue`), `DhPublicValid` and `KeyGenSizesOf K`. -/
theorem established_encrypt_successor_hypotheses_jointly_satisfiable (K : Model.Braid.Kem)
    (dh : DhView) (kem : KemView) (L : Tacenta.UnitLifecycleDecryptScreen.DecryptJointLaws K dh)
    (A : Nonempty (InitiatorAxiom Interp.real byteRng))
    (S : InitiatorSuccessShape Interp.real byteRng byteCrc)
    (hpub : DhPublicValid) (hct : KemCiphertextLenOf) (X : EncryptExtraLaws K dh kem)
    (hsizes : KeyGenSizesOf K) (our : lifecycle.Identity) (seed : List Std.U8)
    (hseed : 64 ≤ seed.length) :
    ∃ (oracle : Model.Lifecycle.Oracle) (bundle : lifecycle.PublishedBundle) (s : lifecycle.Session)
      (rng1 : List Std.U8),
      oracle.braidKem = K ∧ oracle.draws = byteTrace seed ∧
      EstablishedEncryptSuccessorHypotheses byteRng byteCrc byteTrace dh kem
        Tacenta.UnitLifecycleRepair.witnessView oracle byteRng byteCrc our bundle
        bundle.bundle.identity_key [] rng1 s emptyPlaintext seed := by
  obtain ⟨oracle, bundle, s, rng1, hK, hdr, H⟩ :=
    established_encrypt_hypotheses_jointly_satisfiable K dh kem L A S hpub hct X our seed hseed
  refine ⟨oracle, bundle, s, rng1, hK, hdr, ?_⟩
  subst hK
  exact
    { toEstablishedEncryptHypotheses := H
      dhPublicValid := hpub
      optionEq := L.optionEq
      kemLen := (Tacenta.UnitSatisfiabilityBraidAgreements.KemLenAgrees_is _).mpr L.agreements.kemLen
      validateEk :=
        (Tacenta.UnitSatisfiabilityBraidAgreements.ValidateEkAgrees_is _).mpr L.agreements.validateEk
      keyGenSizes := hsizes
      divCeil := Tacenta.UnitSatisfiabilityJoint.DivCeilValue_is.mpr L.laws.divCeil }

/-- **The success arm is reached and leaves a session that passes `Session::invariant` and meets the four
counter ceilings**, at the real constants, under the laws of
`established_encrypt_successor_hypotheses_jointly_satisfiable`, for every identity and every 64-byte source
at whose bytes the model's key generation answers. -/
theorem established_encrypt_successor_reachable (K : Model.Braid.Kem) (dh : DhView)
    (kem : KemView) (L : Tacenta.UnitLifecycleDecryptScreen.DecryptJointLaws K dh)
    (A : Nonempty (InitiatorAxiom Interp.real byteRng))
    (S : InitiatorSuccessShape Interp.real byteRng byteCrc)
    (hpub : DhPublicValid) (hct : KemCiphertextLenOf) (X : EncryptExtraLaws K dh kem)
    (hsizes : KeyGenSizesOf K) (our : lifecycle.Identity) (seed : List Std.U8)
    (hseed : seed.length = 64)
    (hkg : K.keyGen (Model.Lifecycle.braidRandomness (seed.map Tacenta.SessionUnitBraidT3.u8)) ≠ none) :
    ∃ (oracle : Model.Lifecycle.Oracle) (bundle : lifecycle.PublishedBundle) (s : lifecycle.Session)
      (rng1 : List Std.U8) (bytes : alloc.vec.Vec Std.U8) (s' : lifecycle.Session) (rng' : List Std.U8),
      oracle.braidKem = K ∧
      EstablishedEncryptSuccessorHypotheses byteRng byteCrc byteTrace dh kem
        Tacenta.UnitLifecycleRepair.witnessView oracle byteRng byteCrc our bundle
        bundle.bundle.identity_key [] rng1 s emptyPlaintext seed ∧
      lifecycle.Session.encrypt byteRng byteCrc s emptyPlaintext seed =
        ok (core.result.Result.Ok bytes, s', rng') ∧
      lifecycle.Session.invariant s' = ok true ∧
      Tacenta.UnitLifecycleDecryptRunBounds.CounterHeadroom s' := by
  obtain ⟨oracle, bundle, s, rng1, hK, -, H⟩ :=
    established_encrypt_successor_hypotheses_jointly_satisfiable K dh kem L A S hpub hct X hsizes our
      seed (by omega)
  obtain ⟨inst⟩ := H.derivedKeys
  subst hK
  obtain ⟨⟨res, s', rng'⟩, hcall, -, hcases⟩ := established_encrypt_outcomes byteRng byteCrc byteTrace
    dh kem Tacenta.UnitLifecycleRepair.witnessView oracle H.braid H.triple H.aead H.dhCodec H.oracleOf
    H.codec H.codewordView H.zeroizing80 H.zeroizing32 H.zeroizingKeys H.keyGen H.kemCiphertextLen
    H.kemCiphertextBound byteRng byteCrc our bundle _ [] rng1 s H.established emptyPlaintext H.room seed
    H.trace_eq _ _ _ (byteTrace_two seed (by omega))
  rw [two_draws_of_64 seed hseed] at hcases
  rcases hcases with ⟨hnone, -⟩ | ⟨dk, ekSeed, ekVector, -, bytes, hres, -⟩
  · exact absurd hnone hkg
  · simp only at hres
    subst hres
    obtain ⟨hinv, -, hcnt, -⟩ := H.successor bytes s' rng' hcall
    exact ⟨oracle, bundle, s, rng1, bytes, s', rng', rfl, H, hcall, hinv, hcnt⟩

end Tacenta.UnitLifecycleEstablishedEncrypt

/-! ## Pins

The constants each result depends on, and the statement of each result and definition, held by the
build.  `attest.py` requires every one of them (`REQUIRED_PINS`, `REQUIRED_STATEMENT_PINS`,
`REQUIRED_PRINT_FORM`). -/

/--
info: 'Tacenta.UnitLifecycleEstablishedEncrypt.keyGenAnswers_is' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleEstablishedEncrypt.keyGenAnswers_is

/--
info: 'Tacenta.UnitLifecycleEstablishedEncrypt.keyGenSeededFor_is' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleEstablishedEncrypt.keyGenSeededFor_is

/--
info: 'Tacenta.UnitLifecycleEstablishedEncrypt.keyGenSizes_wrapperKemOf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishedEncrypt.keyGenSizes_wrapperKemOf

/--
info: 'Tacenta.UnitLifecycleEstablishedEncrypt.keyGenSizes_wrapperKem' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleEstablishedEncrypt.keyGenSizes_wrapperKem

/--
info: 'Tacenta.UnitLifecycleEstablishedEncrypt.step_send_keysUnsampled_pinned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kdf.hkdf_sha256,
 tacenta_session_unit.tacenta_kdf.hmac_sha256,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.tacenta_kem.encapsulate1,
 tacenta_session_unit.tacenta_kem.encapsulate2,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.rand_core_1.error.Error,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.generate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.header,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.alloc.vec.Vec.truncate,
 tacenta_session_unit.core.num.Usize.div_ceil,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishedEncrypt.step_send_keysUnsampled_pinned

/--
info: 'Tacenta.UnitLifecycleEstablishedEncrypt.braid_send_keysUnsampled_pinned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kdf.hkdf_sha256,
 tacenta_session_unit.tacenta_kdf.hmac_sha256,
 tacenta_session_unit.tacenta_kem.CT1_LEN,
 tacenta_session_unit.tacenta_kem.CT2_LEN,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.tacenta_kem.encapsulate1,
 tacenta_session_unit.tacenta_kem.encapsulate2,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.rand_core_1.error.Error,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.generate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.header,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.alloc.vec.Vec.truncate,
 tacenta_session_unit.core.num.Usize.div_ceil,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 tacenta_session_unit.tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishedEncrypt.braid_send_keysUnsampled_pinned

/--
info: 'Tacenta.UnitLifecycleEstablishedEncrypt.send_keysUnsampled_output' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishedEncrypt.send_keysUnsampled_output

/--
info: 'Tacenta.UnitLifecycleEstablishedEncrypt.sendAgreement_keysUnsampled_output' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishedEncrypt.sendAgreement_keysUnsampled_output

/--
info: 'Tacenta.UnitLifecycleEstablishedEncrypt.two_of_length' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishedEncrypt.two_of_length

/--
info: 'Tacenta.UnitLifecycleEstablishedEncrypt.braidSendTraceCounted_of_keysUnsampled' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kdf.hkdf_sha256,
 tacenta_session_unit.tacenta_kdf.hmac_sha256,
 tacenta_session_unit.tacenta_kem.CT1_LEN,
 tacenta_session_unit.tacenta_kem.CT2_LEN,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.tacenta_kem.encapsulate1,
 tacenta_session_unit.tacenta_kem.encapsulate2,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.rand_core_1.error.Error,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.generate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.header,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.alloc.vec.Vec.truncate,
 tacenta_session_unit.core.num.Usize.div_ceil,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 tacenta_session_unit.tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishedEncrypt.braidSendTraceCounted_of_keysUnsampled

/--
info: 'Tacenta.UnitLifecycleEstablishedEncrypt.braidSendTraceCounted_established' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kdf.hkdf_sha256,
 tacenta_session_unit.tacenta_kdf.hmac_sha256,
 tacenta_session_unit.tacenta_kem.CT1_LEN,
 tacenta_session_unit.tacenta_kem.CT2_LEN,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.tacenta_kem.encapsulate1,
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
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.generate,
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
 tacenta_session_unit.tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
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
#print axioms Tacenta.UnitLifecycleEstablishedEncrypt.braidSendTraceCounted_established

/--
info: 'Tacenta.UnitLifecycleEstablishedEncrypt.identityAd_length_parts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
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
#print axioms Tacenta.UnitLifecycleEstablishedEncrypt.identityAd_length_parts

/--
info: 'Tacenta.UnitLifecycleEstablishedEncrypt.kemCiphertext_length_parts' depends on axioms: [propext,
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
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishedEncrypt.kemCiphertext_length_parts

/--
info: 'Tacenta.UnitLifecycleEstablishedEncrypt.encryptHeadroom_parts' depends on axioms: [propext,
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
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishedEncrypt.encryptHeadroom_parts

/--
info: 'Tacenta.UnitLifecycleEstablishedEncrypt.encryptHeadroom_established' depends on axioms: [propext,
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
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishedEncrypt.encryptHeadroom_established

/--
info: 'Tacenta.UnitLifecycleEstablishedEncrypt.tripleStoreFacts_parts' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleEstablishedEncrypt.tripleStoreFacts_parts

/--
info: 'Tacenta.UnitLifecycleEstablishedEncrypt.sparseOutput_none_of_evidence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kdf.hkdf_sha256,
 tacenta_session_unit.tacenta_kdf.hmac_sha256,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.tacenta_kem.encapsulate1,
 tacenta_session_unit.tacenta_kem.encapsulate2,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.rand_core_1.error.Error,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.generate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.header,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.alloc.vec.Vec.truncate,
 tacenta_session_unit.core.num.Usize.div_ceil,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 tacenta_session_unit.tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishedEncrypt.sparseOutput_none_of_evidence

/--
info: 'Tacenta.UnitLifecycleEstablishedEncrypt.encryptProviders_established' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kdf.hkdf_sha256,
 tacenta_session_unit.tacenta_kdf.hmac_sha256,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.tacenta_kem.encapsulate1,
 tacenta_session_unit.tacenta_kem.encapsulate2,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.rand_core_1.error.Error,
 tacenta_session_unit.tacenta_boundary.aead.encrypt,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.dh.is_prime_order_public,
 tacenta_session_unit.tacenta_boundary.kem.KeyPair,
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
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.as_bytes,
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
#print axioms Tacenta.UnitLifecycleEstablishedEncrypt.encryptProviders_established

/--
info: 'Tacenta.UnitLifecycleEstablishedEncrypt.established_initiator_encrypt_refines' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleEstablishedEncrypt.established_initiator_encrypt_refines

/--
info: 'Tacenta.UnitLifecycleEstablishedEncrypt.established_triple_send_ok' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleEstablishedEncrypt.established_triple_send_ok

/--
info: 'Tacenta.UnitLifecycleEstablishedEncrypt.established_encrypt_model_cases' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleEstablishedEncrypt.established_encrypt_model_cases

/--
info: 'Tacenta.UnitLifecycleEstablishedEncrypt.state_failed_of_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.tacenta_kem.encapsulate2,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.header,
 tacenta_session_unit.alloc.vec.Vec.truncate,
 tacenta_session_unit.core.num.Usize.div_ceil]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishedEncrypt.state_failed_of_refines

/--
info: 'Tacenta.UnitLifecycleEstablishedEncrypt.state_keysSampled_of_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.tacenta_kem.encapsulate2,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.header,
 tacenta_session_unit.alloc.vec.Vec.truncate,
 tacenta_session_unit.core.num.Usize.div_ceil]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishedEncrypt.state_keysSampled_of_refines

/--
info: 'Tacenta.UnitLifecycleEstablishedEncrypt.established_encrypt_outcomes' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleEstablishedEncrypt.established_encrypt_outcomes

/--
info: 'Tacenta.UnitLifecycleEstablishedEncrypt.established_triple_next_counters' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleEstablishedEncrypt.established_triple_next_counters

/--
info: 'Tacenta.UnitLifecycleEstablishedEncrypt.established_encrypt_successor_counterHeadroom' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleEstablishedEncrypt.established_encrypt_successor_counterHeadroom

/--
info: 'Tacenta.UnitLifecycleEstablishedEncrypt.established_encrypt_successor_refines' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleEstablishedEncrypt.established_encrypt_successor_refines

/--
info: 'Tacenta.UnitLifecycleEstablishedEncrypt.EstablishedEncryptHypotheses.refines' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleEstablishedEncrypt.EstablishedEncryptHypotheses.refines

/--
info: 'Tacenta.UnitLifecycleEstablishedEncrypt.zeroizingKeys_is' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleEstablishedEncrypt.zeroizingKeys_is

/--
info: 'Tacenta.UnitLifecycleEstablishedEncrypt.nil_length_le' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishedEncrypt.nil_length_le

/--
info: 'Tacenta.UnitLifecycleEstablishedEncrypt.byteTrace_two' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishedEncrypt.byteTrace_two

/--
info: 'Tacenta.UnitLifecycleEstablishedEncrypt.established_encrypt_hypotheses_jointly_satisfiable' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleEstablishedEncrypt.established_encrypt_hypotheses_jointly_satisfiable

/--
info: 'Tacenta.UnitLifecycleEstablishedEncrypt.two_draws_of_64' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishedEncrypt.two_draws_of_64

/--
info: 'Tacenta.UnitLifecycleEstablishedEncrypt.established_encrypt_outcomes_at_witness' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleEstablishedEncrypt.established_encrypt_outcomes_at_witness

/--
info: 'Tacenta.UnitLifecycleEstablishedEncrypt.established_encrypt_success_reachable' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleEstablishedEncrypt.established_encrypt_success_reachable

/--
info: 'Tacenta.UnitLifecycleEstablishedEncrypt.established_encrypt_refusal_reachable' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleEstablishedEncrypt.established_encrypt_refusal_reachable

/--
info: 'Tacenta.UnitLifecycleEstablishedEncrypt.genFill_answers' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishedEncrypt.genFill_answers

/--
info: 'Tacenta.UnitLifecycleEstablishedEncrypt.modelEncrypt_keyGenSeeded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishedEncrypt.modelEncrypt_keyGenSeeded

/--
info: 'Tacenta.UnitLifecycleEstablishedEncrypt.modelEncrypt_kemAgrees' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishedEncrypt.modelEncrypt_kemAgrees

/--
info: 'Tacenta.UnitLifecycleEstablishedEncrypt.modelEncrypt_keyPairGenerate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishedEncrypt.modelEncrypt_keyPairGenerate

/--
info: 'Tacenta.UnitLifecycleEstablishedEncrypt.modelEncrypt_kemEncapsulate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishedEncrypt.modelEncrypt_kemEncapsulate

/--
info: 'Tacenta.UnitLifecycleEstablishedEncrypt.byteRng_rngTotal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishedEncrypt.byteRng_rngTotal

/--
info: 'Tacenta.UnitLifecycleEstablishedEncrypt.modelEncrypt_allT1' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishedEncrypt.modelEncrypt_allT1

/--
info: 'Tacenta.UnitLifecycleEstablishedEncrypt.leValue_replicate_zero' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishedEncrypt.leValue_replicate_zero

/--
info: 'Tacenta.UnitLifecycleEstablishedEncrypt.toyKemR_seeds' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishedEncrypt.toyKemR_seeds

/--
info: 'Tacenta.UnitLifecycleEstablishedEncrypt.toyKemR_sizes' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishedEncrypt.toyKemR_sizes

/--
info: 'Tacenta.UnitLifecycleEstablishedEncrypt.established_encrypt_laws_model' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.rand_core_1.error.Error,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishedEncrypt.established_encrypt_laws_model

/--
info: 'Tacenta.UnitLifecycleEstablishedEncrypt.encrypt_ok_parts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kdf.hkdf_sha256,
 tacenta_session_unit.tacenta_kdf.hmac_sha256,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.tacenta_kem.encapsulate1,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.rand_core_1.error.Error,
 tacenta_session_unit.tacenta_boundary.aead.encrypt,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.generate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.header,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.Pair.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.TupleABC.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.alloc.vec.Vec.capacity,
 tacenta_session_unit.alloc.vec.Vec.pop,
 tacenta_session_unit.core.num.Usize.div_ceil,
 tacenta_session_unit.core.option.Option.as_mut,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 tacenta_session_unit.tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
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
#print axioms Tacenta.UnitLifecycleEstablishedEncrypt.encrypt_ok_parts

/--
info: 'Tacenta.UnitLifecycleEstablishedEncrypt.array_eq_of_bytes' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishedEncrypt.array_eq_of_bytes

/--
info: 'Tacenta.UnitLifecycleEstablishedEncrypt.triple_eq_sent' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleEstablishedEncrypt.triple_eq_sent

/--
info: 'Tacenta.UnitLifecycleEstablishedEncrypt.sentTriple_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishedEncrypt.sentTriple_invariant

/--
info: 'Tacenta.UnitLifecycleEstablishedEncrypt.structural_sent' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleEstablishedEncrypt.structural_sent

/--
info: 'Tacenta.UnitLifecycleEstablishedEncrypt.keysSampled_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kem.CT1_LEN,
 tacenta_session_unit.tacenta_kem.CT2_LEN,
 tacenta_session_unit.tacenta_kem.EK_VECTOR_LEN,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.HEADER_LEN,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.tacenta_kem.validate_ek,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.header,
 tacenta_session_unit.core.num.Usize.div_ceil]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishedEncrypt.keysSampled_invariant

/--
info: 'Tacenta.UnitLifecycleEstablishedEncrypt.sent_invariant' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleEstablishedEncrypt.sent_invariant

/--
info: 'Tacenta.UnitLifecycleEstablishedEncrypt.keyPairValid_of_header' depends on axioms: [propext,
 Quot.sound,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.tacenta_kem.validate_ek,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.header]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishedEncrypt.keyPairValid_of_header

/--
info: 'Tacenta.UnitLifecycleEstablishedEncrypt.encoder_of_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.alloc.vec.Vec.truncate,
 tacenta_session_unit.core.num.Usize.div_ceil]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishedEncrypt.encoder_of_refines

/--
info: 'Tacenta.UnitLifecycleEstablishedEncrypt.established_encrypt_successor_admissible' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleEstablishedEncrypt.established_encrypt_successor_admissible

/--
info: 'Tacenta.UnitLifecycleEstablishedEncrypt.established_encrypt_successor_hypotheses' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleEstablishedEncrypt.established_encrypt_successor_hypotheses

/--
info: 'Tacenta.UnitLifecycleEstablishedEncrypt.authOf_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishedEncrypt.authOf_injective

/--
info: 'Tacenta.UnitLifecycleEstablishedEncrypt.established_encrypt_successor_shape' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleEstablishedEncrypt.established_encrypt_successor_shape

/--
info: 'Tacenta.UnitLifecycleEstablishedEncrypt.EstablishedEncryptSuccessorHypotheses.successor' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleEstablishedEncrypt.EstablishedEncryptSuccessorHypotheses.successor

/--
info: 'Tacenta.UnitLifecycleEstablishedEncrypt.established_encrypt_successor_hypotheses_jointly_satisfiable' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleEstablishedEncrypt.established_encrypt_successor_hypotheses_jointly_satisfiable

/--
info: 'Tacenta.UnitLifecycleEstablishedEncrypt.established_encrypt_successor_reachable' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleEstablishedEncrypt.established_encrypt_successor_reachable

set_option pp.deepTerms true
set_option pp.proofs.withType true

/--
info: Tacenta.UnitLifecycleEstablishedEncrypt.keyGenAnswers_is : ∀ (K : Model.Braid.Kem) {R : Type}
  (rc : tacenta_session_unit.rand_core_1.RngCore R) (crc : tacenta_session_unit.rand_core_1.CryptoRng R) (rng : R)
  (rand : ℕ) (rng' : R),
  Tacenta.UnitLifecycleEstablishedEncrypt.KeyGenAnswers K rc crc rng rand rng' ↔
    Tacenta.UnitLifecycleEstablishedEncrypt.KeyGenAnswersShape Tacenta.UnitSatisfiabilityJoint.Interp.real K rc crc rng
      rand rng'
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishedEncrypt.keyGenAnswers_is

/--
info: Tacenta.UnitLifecycleEstablishedEncrypt.keyGenSeededFor_is : ∀ (K : Model.Braid.Kem) {R : Type}
  (rc : tacenta_session_unit.rand_core_1.RngCore R) (crc : tacenta_session_unit.rand_core_1.CryptoRng R)
  (trace : R → List Model.Lifecycle.Key),
  Tacenta.UnitLifecycleEstablishedEncrypt.KeyGenSeededFor K rc crc trace ↔
    Tacenta.UnitLifecycleEstablishedEncrypt.KeyGenSeededForShape Tacenta.UnitSatisfiabilityJoint.Interp.real K rc crc
      trace
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishedEncrypt.keyGenSeededFor_is

/--
info: @Tacenta.UnitLifecycleEstablishedEncrypt.keyGenSizes_wrapperKemOf : ∀ {I : Tacenta.UnitSatisfiabilityJoint.Interp},
  Tacenta.UnitKemWrapperModel.WrapperKemLawsShape I →
    Tacenta.UnitLifecycleEstablishedEncrypt.KeyGenSizesOf (Tacenta.UnitKemWrapperModel.wrapperKemOf I)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishedEncrypt.keyGenSizes_wrapperKemOf

/--
info: Tacenta.UnitLifecycleEstablishedEncrypt.keyGenSizes_wrapperKem : Tacenta.UnitKemWrapperModel.WrapperKemLaws →
  Tacenta.UnitLifecycleEstablishedEncrypt.KeyGenSizesOf Tacenta.UnitKemWrapperModel.wrapperKem
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishedEncrypt.keyGenSizes_wrapperKem

/--
info: @Tacenta.UnitLifecycleEstablishedEncrypt.step_send_keysUnsampled_pinned : ∀ {K : Model.Braid.Kem},
  Tacenta.SessionUnitBraidT3.ErasureAgrees →
    Tacenta.SessionUnitBraidT3.BraidHmacAgrees →
      Tacenta.SessionUnitBraidT1.KeyPairHeaderTotal →
        ∀ {R : Type} (rc : tacenta_session_unit.rand_core_1.RngCore R)
          (crc : tacenta_session_unit.rand_core_1.CryptoRng R) (self : tacenta_session_unit.tacenta_braid.Braid)
          (state : tacenta_session_unit.tacenta_braid.State) (rng : R) {e : ℕ} {a : Model.Braid.Auth},
          Tacenta.SessionUnitBraidT3.StateRefines K state (Model.Braid.BraidState.keysUnsampled e a) →
            ∀ (rand : ℕ) (rng' : R),
              Tacenta.UnitLifecycleEstablishedEncrypt.KeyGenAnswers K rc crc rng rand rng' →
                Aeneas.Std.WP.spec (tacenta_session_unit.tacenta_braid.Braid.step_send rc crc self state rng) fun x =>
                  match x with
                  | ((msg, out, next), snd) =>
                    (∀ (modelMsg : Model.Braid.Msg),
                        (Model.Braid.send K rand (Model.Braid.BraidState.keysUnsampled e a)).1 = some modelMsg →
                          Tacenta.SessionUnitBraidT3.MsgRefines msg modelMsg) ∧
                      ((Model.Braid.send K rand (Model.Braid.BraidState.keysUnsampled e a)).1 = none →
                          msg.data = none) ∧
                        Tacenta.SessionUnitBraidT3.OptionOutputRefines out
                            (Model.Braid.send K rand (Model.Braid.BraidState.keysUnsampled e a)).2.2.1 ∧
                          Tacenta.SessionUnitBraidT3.StateRefines K next
                              (Model.Braid.send K rand (Model.Braid.BraidState.keysUnsampled e a)).2.2.2 ∧
                            ∀ (e' : Aeneas.Std.U64) (a' : tacenta_session_unit.tacenta_braid.Auth)
                              (kp : tacenta_session_unit.tacenta_kem.IncrementalKeyPair)
                              (enc : tacenta_session_unit.tacenta_erasure.Encoder),
                              next = tacenta_session_unit.tacenta_braid.State.KeysSampled e' a' kp enc →
                                ∃ h,
                                  kp.header = Aeneas.Std.Result.ok h ∧
                                    ∃ dk ekSeed ekVector,
                                      K.keyGen rand = some (dk, ekSeed, ekVector) ∧
                                        Tacenta.SessionUnitBraidT3.vecOf h = ekSeed ++ K.hashEk ekSeed ekVector
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishedEncrypt.step_send_keysUnsampled_pinned

/--
info: @Tacenta.UnitLifecycleEstablishedEncrypt.braid_send_keysUnsampled_pinned : ∀ {Self : Type}
  {rc : tacenta_session_unit.rand_core_1.RngCore Self} {K : Model.Braid.Kem},
  Tacenta.UnitLifecycleT3.BraidSendRefinementContracts rc K →
    ∀ {R : Type} {rc : tacenta_session_unit.rand_core_1.RngCore R} (crc : tacenta_session_unit.rand_core_1.CryptoRng R)
      (self : tacenta_session_unit.tacenta_braid.Braid) (rng : R) {e : ℕ} {a : Model.Braid.Auth},
      Tacenta.SessionUnitBraidT3.StateRefines K self.state (Model.Braid.BraidState.keysUnsampled e a) →
        ∀ (rand : ℕ) (rng' : R),
          Tacenta.UnitLifecycleEstablishedEncrypt.KeyGenAnswers K rc crc rng rand rng' →
            Aeneas.Std.WP.spec (tacenta_session_unit.tacenta_braid.Braid.send rc crc self rng) fun x =>
              match x with
              | ((msg, i, out, next), snd) =>
                (∀ (modelMsg : Model.Braid.Msg),
                    (Model.Braid.send K rand (Model.Braid.BraidState.keysUnsampled e a)).1 = some modelMsg →
                      Tacenta.SessionUnitBraidT3.MsgRefines msg modelMsg) ∧
                  ↑i = (Model.Braid.send K rand (Model.Braid.BraidState.keysUnsampled e a)).2.2.2.epoch - 1 ∧
                    Tacenta.SessionUnitBraidT3.OptionOutputRefines out
                        (Model.Braid.send K rand (Model.Braid.BraidState.keysUnsampled e a)).2.2.1 ∧
                      Tacenta.SessionUnitBraidT3.StateRefines K next.state
                          (Model.Braid.send K rand (Model.Braid.BraidState.keysUnsampled e a)).2.2.2 ∧
                        ∀ (e' : Aeneas.Std.U64) (a' : tacenta_session_unit.tacenta_braid.Auth)
                          (kp : tacenta_session_unit.tacenta_kem.IncrementalKeyPair)
                          (enc : tacenta_session_unit.tacenta_erasure.Encoder),
                          next.state = tacenta_session_unit.tacenta_braid.State.KeysSampled e' a' kp enc →
                            ∃ h,
                              kp.header = Aeneas.Std.Result.ok h ∧
                                ∃ dk ekSeed ekVector,
                                  K.keyGen rand = some (dk, ekSeed, ekVector) ∧
                                    Tacenta.SessionUnitBraidT3.vecOf h = ekSeed ++ K.hashEk ekSeed ekVector
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishedEncrypt.braid_send_keysUnsampled_pinned

/--
info: Tacenta.UnitLifecycleEstablishedEncrypt.send_keysUnsampled_output : ∀ (K : Model.Braid.Kem) (rand e : ℕ)
  (a : Model.Braid.Auth), (Model.Braid.send K rand (Model.Braid.BraidState.keysUnsampled e a)).2.2.1 = none
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishedEncrypt.send_keysUnsampled_output

/--
info: Tacenta.UnitLifecycleEstablishedEncrypt.sendAgreement_keysUnsampled_output : ∀
  (oracle oracleNext : Model.Lifecycle.Oracle) (e : ℕ) (a : Model.Braid.Auth) (message : Option Model.Braid.Msg)
  (epoch : ℕ) (output : Option Model.Braid.Output) (next : Model.Braid.BraidState),
  Model.Lifecycle.sendAgreement oracle (Model.Braid.BraidState.keysUnsampled e a) =
      some ((message, epoch, output, next), oracleNext) →
    output = none
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishedEncrypt.sendAgreement_keysUnsampled_output

/--
info: @Tacenta.UnitLifecycleEstablishedEncrypt.two_of_length : ∀ {α : Type} (l : List α), l.length = 2 → ∃ x y, l = [x, y]
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishedEncrypt.two_of_length

/--
info: @Tacenta.UnitLifecycleEstablishedEncrypt.braidSendTraceCounted_of_keysUnsampled : ∀ {R : Type}
  {rc : tacenta_session_unit.rand_core_1.RngCore R} {crc : tacenta_session_unit.rand_core_1.CryptoRng R}
  {trace : R → List Model.Lifecycle.Key} {K : Model.Braid.Kem} {oracle : Model.Lifecycle.Oracle}
  {real : tacenta_session_unit.lifecycle.Session} {model : Model.Lifecycle.Session} {rng : R},
  Tacenta.UnitLifecycleT3.BraidSendRefinementContracts rc K →
    Tacenta.UnitLifecycleEstablishedEncrypt.KeyGenSeededFor K rc crc trace →
      oracle.braidKem = K →
        ∀ (epoch : Aeneas.Std.U64) (auth : tacenta_session_unit.tacenta_braid.Auth),
          real.braid.state = tacenta_session_unit.tacenta_braid.State.KeysUnsampled epoch auth →
            model.braid = Model.Braid.BraidState.keysUnsampled (↑epoch) (Tacenta.SessionUnitBraidT3.AuthOf auth) →
              (∃ d1 d2 rest, trace rng = d1 :: d2 :: rest) →
                Tacenta.UnitLifecycleT3.BraidSendTraceAgreementCounted rc crc trace K oracle real model rng
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishedEncrypt.braidSendTraceCounted_of_keysUnsampled

/--
info: @Tacenta.UnitLifecycleEstablishedEncrypt.braidSendTraceCounted_established : ∀ {R E : Type}
  {rc : tacenta_session_unit.rand_core_1.RngCore R} {crc : tacenta_session_unit.rand_core_1.CryptoRng R}
  {trace : R → List Model.Lifecycle.Key} (dh : Tacenta.UnitLifecycleT3.DhView) {oracle : Model.Lifecycle.Oracle},
  Tacenta.UnitLifecycleT3.BraidSendRefinementContracts rc oracle.braidKem →
    Tacenta.UnitLifecycleEstablishedEncrypt.KeyGenSeededFor oracle.braidKem rc crc trace →
      ∀ (rcE : tacenta_session_unit.rand_core_1.RngCore E) (crcE : tacenta_session_unit.rand_core_1.CryptoRng E)
        (our : tacenta_session_unit.lifecycle.Identity) (bundle : tacenta_session_unit.lifecycle.PublishedBundle)
        (expected : tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes) (rng0 rng1 : E)
        (s : tacenta_session_unit.lifecycle.Session),
        tacenta_session_unit.lifecycle.establish_initiator_for rcE crcE our bundle expected rng0 =
            Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok s, rng1) →
          ∀ (rng : R),
            (∃ d1 d2 rest, trace rng = d1 :: d2 :: rest) →
              Tacenta.UnitLifecycleT3.BraidSendTraceAgreementCounted rc crc trace oracle.braidKem oracle s
                (Tacenta.UnitLifecycleEstablishInitiatorShape.establishedModelOf dh s) rng
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishedEncrypt.braidSendTraceCounted_established

/--
info: Tacenta.UnitLifecycleEstablishedEncrypt.identityAd_length_parts : Tacenta.UnitLifecycleT1.DhCodecTotal →
  ∀ {R : Type} {rc : tacenta_session_unit.rand_core_1.RngCore R} {crc : tacenta_session_unit.rand_core_1.CryptoRng R}
    {our : tacenta_session_unit.lifecycle.Identity} {bundle : tacenta_session_unit.lifecycle.PublishedBundle}
    (p : Tacenta.UnitLifecycleEstablishInitiatorShape.InitiatorOutputParts rc crc our bundle),
    (↑p.identityAd).length = 66
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishedEncrypt.identityAd_length_parts

/--
info: Tacenta.UnitLifecycleEstablishedEncrypt.kemCiphertext_length_parts : Tacenta.UnitLifecycleEstablishInitiatorShape.KemCiphertextLenOf →
  Tacenta.UnitLifecycleRestoredSession.KemCiphertextLenBound →
    ∀ {R : Type} {rc : tacenta_session_unit.rand_core_1.RngCore R} {crc : tacenta_session_unit.rand_core_1.CryptoRng R}
      {our : tacenta_session_unit.lifecycle.Identity} {bundle : tacenta_session_unit.lifecycle.PublishedBundle}
      (p : Tacenta.UnitLifecycleEstablishInitiatorShape.InitiatorOutputParts rc crc our bundle),
      (↑p.kemCiphertext).length ≤ 65536
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishedEncrypt.kemCiphertext_length_parts

/--
info: Tacenta.UnitLifecycleEstablishedEncrypt.encryptHeadroom_parts : Tacenta.UnitLifecycleT1.DhCodecTotal →
  Tacenta.UnitLifecycleEstablishInitiatorShape.KemCiphertextLenOf →
    Tacenta.UnitLifecycleRestoredSession.KemCiphertextLenBound →
      ∀ {R : Type} {rc : tacenta_session_unit.rand_core_1.RngCore R}
        {crc : tacenta_session_unit.rand_core_1.CryptoRng R} {our : tacenta_session_unit.lifecycle.Identity}
        {bundle : tacenta_session_unit.lifecycle.PublishedBundle}
        (p : Tacenta.UnitLifecycleEstablishInitiatorShape.InitiatorOutputParts rc crc our bundle)
        (plaintext : Aeneas.Std.Slice Aeneas.Std.U8),
        (↑plaintext).length + 65770 ≤ Aeneas.Std.Usize.max → Tacenta.UnitLifecycleT1.EncryptHeadroom p.session plaintext
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishedEncrypt.encryptHeadroom_parts

/--
info: Tacenta.UnitLifecycleEstablishedEncrypt.encryptHeadroom_established : Tacenta.UnitLifecycleT1.DhCodecTotal →
  Tacenta.UnitLifecycleEstablishInitiatorShape.KemCiphertextLenOf →
    Tacenta.UnitLifecycleRestoredSession.KemCiphertextLenBound →
      ∀ {E : Type} (rcE : tacenta_session_unit.rand_core_1.RngCore E)
        (crcE : tacenta_session_unit.rand_core_1.CryptoRng E) (our : tacenta_session_unit.lifecycle.Identity)
        (bundle : tacenta_session_unit.lifecycle.PublishedBundle)
        (expected : tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes) (rng0 rng1 : E)
        (s : tacenta_session_unit.lifecycle.Session),
        tacenta_session_unit.lifecycle.establish_initiator_for rcE crcE our bundle expected rng0 =
            Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok s, rng1) →
          ∀ (plaintext : Aeneas.Std.Slice Aeneas.Std.U8),
            (↑plaintext).length + 65770 ≤ Aeneas.Std.Usize.max → Tacenta.UnitLifecycleT1.EncryptHeadroom s plaintext
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishedEncrypt.encryptHeadroom_established

/--
info: Tacenta.UnitLifecycleEstablishedEncrypt.tripleStoreFacts_parts : ∀ (dh : Tacenta.UnitLifecycleT3.DhView) {R : Type}
  {rc : tacenta_session_unit.rand_core_1.RngCore R} {crc : tacenta_session_unit.rand_core_1.CryptoRng R}
  {our : tacenta_session_unit.lifecycle.Identity} {bundle : tacenta_session_unit.lifecycle.PublishedBundle}
  (p : Tacenta.UnitLifecycleEstablishInitiatorShape.InitiatorOutputParts rc crc our bundle),
  (Tacenta.UnitLifecycleEstablishInitiatorShape.establishedModelOf dh p.session).triple.postQuantum.chains.length + 1 <
      Aeneas.Std.Usize.max ∧
    (∀ q ∈ (Tacenta.UnitLifecycleEstablishInitiatorShape.establishedModelOf dh p.session).triple.postQuantum.chains,
        q.1 + Model.SparseRatchet.epochsKept ≤ Aeneas.Std.U64.max) ∧
      (∀ sk ∈ (Tacenta.UnitLifecycleEstablishInitiatorShape.establishedModelOf dh p.session).triple.postQuantum.skipped,
          sk.1 + Model.SparseRatchet.epochsKept ≤ Aeneas.Std.U64.max) ∧
        (Tacenta.UnitLifecycleEstablishInitiatorShape.establishedModelOf dh p.session).triple.postQuantum.epoch + 1 <
            Aeneas.Std.U64.max ∧
          ∀
            q ∈
              (Tacenta.UnitLifecycleEstablishInitiatorShape.establishedModelOf dh p.session).triple.postQuantum.chains,
            ∀ (ch : Model.SparseRatchet.Chain), q.2.send = some ch ∨ q.2.receive = some ch → ch.n < Aeneas.Std.U64.max
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishedEncrypt.tripleStoreFacts_parts

/--
info: @Tacenta.UnitLifecycleEstablishedEncrypt.sparseOutput_none_of_evidence : ∀ {R : Type}
  {rc : tacenta_session_unit.rand_core_1.RngCore R} {crc : tacenta_session_unit.rand_core_1.CryptoRng R}
  {trace : R → List Model.Lifecycle.Key} {dh : Tacenta.UnitLifecycleT3.DhView} {K : Model.Braid.Kem}
  {oracle : Model.Lifecycle.Oracle} {real : tacenta_session_unit.lifecycle.Session} {model : Model.Lifecycle.Session}
  {rng : R} {realMessage : tacenta_session_unit.tacenta_braid.Msg} {realEpoch : Aeneas.Std.U64}
  {realOutput : Option tacenta_session_unit.tacenta_braid.Output}
  {realBraidNext : tacenta_session_unit.tacenta_braid.Braid} {rngNext : R}
  {sparseOutput : Option tacenta_session_unit.tacenta_spqr.Output} (e : ℕ) (a : Model.Braid.Auth),
  model.braid = Model.Braid.BraidState.keysUnsampled e a →
    Tacenta.UnitLifecycleT3.RealSparseConversion realOutput sparseOutput →
      Nonempty
          (Tacenta.UnitLifecycleT3.GeneratedBraidSuccessEvidence rc crc trace dh K oracle real model rng realMessage
            realEpoch realOutput realBraidNext rngNext) →
        sparseOutput = none
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishedEncrypt.sparseOutput_none_of_evidence

/--
info: @Tacenta.UnitLifecycleEstablishedEncrypt.encryptProviders_established : ∀ [Tacenta.SessionUnitT1.DerivedKeysModel]
  {R E : Type} {rc : tacenta_session_unit.rand_core_1.RngCore R} {crc : tacenta_session_unit.rand_core_1.CryptoRng R}
  {trace : R → List Model.Lifecycle.Key} (dh : Tacenta.UnitLifecycleT3.DhView) (kem : Tacenta.UnitLifecycleT3.KemView)
  (K : Model.Braid.Kem) (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
  (rcE : tacenta_session_unit.rand_core_1.RngCore E) (crcE : tacenta_session_unit.rand_core_1.CryptoRng E)
  (our : tacenta_session_unit.lifecycle.Identity) (bundle : tacenta_session_unit.lifecycle.PublishedBundle)
  (expected : tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes) (rng0 rng1 : E)
  (s : tacenta_session_unit.lifecycle.Session),
  tacenta_session_unit.lifecycle.establish_initiator_for rcE crcE our bundle expected rng0 =
      Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok s, rng1) →
    ∀ (plaintext : Aeneas.Std.Slice Aeneas.Std.U8) (rng : R),
      Nonempty
        (Tacenta.UnitLifecycleT3.EncryptNonterminalRouteProviders rc crc trace dh kem K view oracle s
          (Tacenta.UnitLifecycleEstablishInitiatorShape.establishedModelOf dh s) plaintext rng)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishedEncrypt.encryptProviders_established

/--
info: @Tacenta.UnitLifecycleEstablishedEncrypt.established_initiator_encrypt_refines : ∀
  [Tacenta.SessionUnitT1.DerivedKeysModel] {R E : Type} (rc : tacenta_session_unit.rand_core_1.RngCore R)
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
                        Tacenta.UnitLifecycleEstablishInitiatorShape.KemCiphertextLenOf →
                          Tacenta.UnitLifecycleRestoredSession.KemCiphertextLenBound →
                            ∀ (rcE : tacenta_session_unit.rand_core_1.RngCore E)
                              (crcE : tacenta_session_unit.rand_core_1.CryptoRng E)
                              (our : tacenta_session_unit.lifecycle.Identity)
                              (bundle : tacenta_session_unit.lifecycle.PublishedBundle)
                              (expected : tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes) (rng0 rng1 : E)
                              (s : tacenta_session_unit.lifecycle.Session),
                              tacenta_session_unit.lifecycle.establish_initiator_for rcE crcE our bundle expected rng0 =
                                  Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok s, rng1) →
                                ∀ (plaintext : Aeneas.Std.Slice Aeneas.Std.U8),
                                  (↑plaintext).length + 65770 ≤ Aeneas.Std.Usize.max →
                                    ∀ (rng : R),
                                      trace rng = oracle.draws →
                                        (∃ d1 d2 rest, trace rng = d1 :: d2 :: rest) →
                                          Tacenta.UnitLifecycleT3.PublicEncryptWitness rc crc trace dh oracle.braidKem
                                            view oracle s
                                            (Tacenta.UnitLifecycleEstablishInitiatorShape.establishedModelOf dh s)
                                            plaintext rng
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishedEncrypt.established_initiator_encrypt_refines

/--
info: Tacenta.UnitLifecycleEstablishedEncrypt.established_triple_send_ok : ∀ (dh : Tacenta.UnitLifecycleT3.DhView) {R : Type}
  {rc : tacenta_session_unit.rand_core_1.RngCore R} {crc : tacenta_session_unit.rand_core_1.CryptoRng R}
  {our : tacenta_session_unit.lifecycle.Identity} {bundle : tacenta_session_unit.lifecycle.PublishedBundle}
  (p : Tacenta.UnitLifecycleEstablishInitiatorShape.InitiatorOutputParts rc crc our bundle),
  ∃ tripleNext header messageKey,
    Model.Triple.sendDetailed (Tacenta.UnitLifecycleEstablishInitiatorShape.establishedModelOf dh p.session).triple 0
          none =
        Except.ok (tripleNext, header, messageKey) ∧
      header.dr.dh =
          (Tacenta.UnitLifecycleEstablishInitiatorShape.establishedModelOf dh p.session).triple.classical.dhsPub ∧
        header.dr.n = 0 ∧ header.dr.pn = 0 ∧ header.epoch = 0 ∧ header.pqN = 1
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishedEncrypt.established_triple_send_ok

/--
info: Tacenta.UnitLifecycleEstablishedEncrypt.established_encrypt_model_cases : ∀ (dh : Tacenta.UnitLifecycleT3.DhView)
  (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle) {R : Type}
  {rc : tacenta_session_unit.rand_core_1.RngCore R} {crc : tacenta_session_unit.rand_core_1.CryptoRng R}
  {our : tacenta_session_unit.lifecycle.Identity} {bundle : tacenta_session_unit.lifecycle.PublishedBundle}
  (p : Tacenta.UnitLifecycleEstablishInitiatorShape.InitiatorOutputParts rc crc our bundle)
  (plaintext : Model.Lifecycle.Bytes) (d1 d2 : Model.Lifecycle.Key) (rest : List Model.Lifecycle.Key),
  oracle.draws = d1 :: d2 :: rest →
    (Model.Lifecycle.encrypt view oracle (Tacenta.UnitLifecycleEstablishInitiatorShape.establishedModelOf dh p.session)
              plaintext).oracle.draws =
        rest ∧
      ((oracle.braidKem.keyGen (Model.Lifecycle.braidRandomness (d1 ++ d2)) = none ∧
          (Model.Lifecycle.encrypt view oracle
                  (Tacenta.UnitLifecycleEstablishInitiatorShape.establishedModelOf dh p.session) plaintext).result =
              Except.error Model.Lifecycle.Refusal.agreementFailed ∧
            (Model.Lifecycle.encrypt view oracle
                  (Tacenta.UnitLifecycleEstablishInitiatorShape.establishedModelOf dh p.session) plaintext).session =
              have __src := Tacenta.UnitLifecycleEstablishInitiatorShape.establishedModelOf dh p.session;
              { triple := __src.triple, braid := Model.Braid.BraidState.failed, ratchetPrivate := __src.ratchetPrivate,
                identityAd := __src.identityAd, ourIdentityPublic := __src.ourIdentityPublic,
                peerIdentityPublic := __src.peerIdentityPublic, pendingInitial := __src.pendingInitial,
                establishedEphemeral := __src.establishedEphemeral }) ∨
        ∃ dk ekSeed ekVector,
          oracle.braidKem.keyGen (Model.Lifecycle.braidRandomness (d1 ++ d2)) = some (dk, ekSeed, ekVector) ∧
            ∃ tripleNext header messageKey chunk encoder pending,
              Model.Triple.sendDetailed
                    (Tacenta.UnitLifecycleEstablishInitiatorShape.establishedModelOf dh p.session).triple 0 none =
                  Except.ok (tripleNext, header, messageKey) ∧
                (Model.Braid.encode
                        (ekSeed ++ oracle.braidKem.hashEk ekSeed ekVector ++
                          (Tacenta.SessionUnitBraidT3.AuthOf p.auth).macHdr 1
                            (ekSeed ++ oracle.braidKem.hashEk ekSeed ekVector))).nextChunk =
                    (chunk, encoder) ∧
                  (Tacenta.UnitLifecycleEstablishInitiatorShape.establishedModelOf dh p.session).pendingInitial =
                      some pending ∧
                    (Model.Lifecycle.encrypt view oracle
                            (Tacenta.UnitLifecycleEstablishInitiatorShape.establishedModelOf dh p.session)
                            plaintext).result =
                        Except.ok
                          (Tacenta.UnitLifecycleEstablishedEncrypt.initialWire
                            (Tacenta.UnitLifecycleEstablishInitiatorShape.establishedModelOf dh p.session) pending
                            (Tacenta.UnitLifecycleEstablishedEncrypt.firstFrame view oracle
                              (Tacenta.UnitLifecycleEstablishInitiatorShape.establishedModelOf dh p.session) plaintext
                              messageKey chunk)) ∧
                      (Model.Lifecycle.encrypt view oracle
                            (Tacenta.UnitLifecycleEstablishInitiatorShape.establishedModelOf dh p.session)
                            plaintext).session =
                        have __src := Tacenta.UnitLifecycleEstablishInitiatorShape.establishedModelOf dh p.session;
                        { triple := tripleNext,
                          braid :=
                            Model.Braid.BraidState.keysSampled 1 (Tacenta.SessionUnitBraidT3.AuthOf p.auth) dk ekVector
                              encoder,
                          ratchetPrivate := __src.ratchetPrivate, identityAd := __src.identityAd,
                          ourIdentityPublic := __src.ourIdentityPublic, peerIdentityPublic := __src.peerIdentityPublic,
                          pendingInitial := __src.pendingInitial, establishedEphemeral := __src.establishedEphemeral })
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishedEncrypt.established_encrypt_model_cases

/--
info: @Tacenta.UnitLifecycleEstablishedEncrypt.state_failed_of_refines : ∀ {K : Model.Braid.Kem}
  {st : tacenta_session_unit.tacenta_braid.State},
  Tacenta.SessionUnitBraidT3.StateRefines K st Model.Braid.BraidState.failed →
    st = tacenta_session_unit.tacenta_braid.State.Failed
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishedEncrypt.state_failed_of_refines

/--
info: @Tacenta.UnitLifecycleEstablishedEncrypt.state_keysSampled_of_refines : ∀ {K : Model.Braid.Kem}
  {st : tacenta_session_unit.tacenta_braid.State} {e : ℕ} {a : Model.Braid.Auth} {dk ekVector : Model.Braid.Bytes}
  {enc : Model.Braid.Encoder},
  Tacenta.SessionUnitBraidT3.StateRefines K st (Model.Braid.BraidState.keysSampled e a dk ekVector enc) →
    ∃ epoch auth kp encoder,
      st = tacenta_session_unit.tacenta_braid.State.KeysSampled epoch auth kp encoder ∧
        ↑epoch = e ∧
          Tacenta.SessionUnitBraidT3.AuthOf auth = a ∧
            Tacenta.SessionUnitBraidT3.FreshKeyPairRefines K kp dk ekVector ∧
              Tacenta.SessionUnitBraidT3.EncoderRefines encoder enc
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishedEncrypt.state_keysSampled_of_refines

/--
info: @Tacenta.UnitLifecycleEstablishedEncrypt.established_encrypt_outcomes : ∀ [Tacenta.SessionUnitT1.DerivedKeysModel]
  {R E : Type} (rc : tacenta_session_unit.rand_core_1.RngCore R) (crc : tacenta_session_unit.rand_core_1.CryptoRng R)
  (trace : R → List Model.Lifecycle.Key) (dh : Tacenta.UnitLifecycleT3.DhView) (kem : Tacenta.UnitLifecycleT3.KemView)
  (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle),
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
                        Tacenta.UnitLifecycleEstablishInitiatorShape.KemCiphertextLenOf →
                          Tacenta.UnitLifecycleRestoredSession.KemCiphertextLenBound →
                            ∀ (rcE : tacenta_session_unit.rand_core_1.RngCore E)
                              (crcE : tacenta_session_unit.rand_core_1.CryptoRng E)
                              (our : tacenta_session_unit.lifecycle.Identity)
                              (bundle : tacenta_session_unit.lifecycle.PublishedBundle)
                              (expected : tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes) (rng0 rng1 : E)
                              (s : tacenta_session_unit.lifecycle.Session),
                              tacenta_session_unit.lifecycle.establish_initiator_for rcE crcE our bundle expected rng0 =
                                  Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok s, rng1) →
                                ∀ (plaintext : Aeneas.Std.Slice Aeneas.Std.U8),
                                  (↑plaintext).length + 65770 ≤ Aeneas.Std.Usize.max →
                                    ∀ (rng : R),
                                      trace rng = oracle.draws →
                                        ∀ (d1 d2 : Model.Lifecycle.Key) (rest : List Model.Lifecycle.Key),
                                          trace rng = d1 :: d2 :: rest →
                                            ∃ output,
                                              tacenta_session_unit.lifecycle.Session.encrypt rc crc s plaintext rng =
                                                  Aeneas.Std.Result.ok output ∧
                                                trace output.2.2 = rest ∧
                                                  (oracle.braidKem.keyGen (Model.Lifecycle.braidRandomness (d1 ++ d2)) =
                                                        none ∧
                                                      output.1 =
                                                          Aeneas.Std.core.result.Result.Err
                                                            tacenta_session_unit.lifecycle.Error.AgreementFailed ∧
                                                        output.2.1 =
                                                          { triple := s.triple,
                                                            braid :=
                                                              {
                                                                state :=
                                                                  tacenta_session_unit.tacenta_braid.State.Failed },
                                                            ratchet_private := s.ratchet_private,
                                                            identity_ad := s.identity_ad,
                                                            our_identity_public := s.our_identity_public,
                                                            peer_identity_public := s.peer_identity_public,
                                                            pending_initial := s.pending_initial,
                                                            established_ephemeral := s.established_ephemeral } ∨
                                                    ∃ dk ekSeed ekVector,
                                                      oracle.braidKem.keyGen
                                                            (Model.Lifecycle.braidRandomness (d1 ++ d2)) =
                                                          some (dk, ekSeed, ekVector) ∧
                                                        ∃ bytes,
                                                          output.1 = Aeneas.Std.core.result.Result.Ok bytes ∧
                                                            output.2.1 =
                                                                { triple := output.2.1.triple,
                                                                  braid := output.2.1.braid,
                                                                  ratchet_private := s.ratchet_private,
                                                                  identity_ad := s.identity_ad,
                                                                  our_identity_public := s.our_identity_public,
                                                                  peer_identity_public := s.peer_identity_public,
                                                                  pending_initial := s.pending_initial,
                                                                  established_ephemeral := s.established_ephemeral } ∧
                                                              (∃ auth kp encoder,
                                                                  output.2.1.braid.state =
                                                                    tacenta_session_unit.tacenta_braid.State.KeysSampled
                                                                      1#u64 auth kp encoder) ∧
                                                                ∃ tripleNext messageKey chunk encoder pending a,
                                                                  (∃ header,
                                                                      Model.Triple.sendDetailed
                                                                          (Tacenta.UnitLifecycleEstablishInitiatorShape.establishedModelOf
                                                                              dh s).triple
                                                                          0 none =
                                                                        Except.ok (tripleNext, header, messageKey)) ∧
                                                                    (Tacenta.UnitLifecycleEstablishInitiatorShape.establishedModelOf
                                                                            dh s).braid =
                                                                        Model.Braid.BraidState.keysUnsampled 1 a ∧
                                                                      (Model.Braid.encode
                                                                              (ekSeed ++
                                                                                  oracle.braidKem.hashEk ekSeed
                                                                                    ekVector ++
                                                                                a.macHdr 1
                                                                                  (ekSeed ++
                                                                                    oracle.braidKem.hashEk ekSeed
                                                                                      ekVector))).nextChunk =
                                                                          (chunk, encoder) ∧
                                                                        (Tacenta.UnitLifecycleEstablishInitiatorShape.establishedModelOf
                                                                                dh s).pendingInitial =
                                                                            some pending ∧
                                                                          Tacenta.UnitLifecycleT3.vecOf bytes =
                                                                              Tacenta.UnitLifecycleEstablishedEncrypt.initialWire
                                                                                (Tacenta.UnitLifecycleEstablishInitiatorShape.establishedModelOf
                                                                                  dh s)
                                                                                pending
                                                                                (Tacenta.UnitLifecycleEstablishedEncrypt.firstFrame
                                                                                  view oracle
                                                                                  (Tacenta.UnitLifecycleEstablishInitiatorShape.establishedModelOf
                                                                                    dh s)
                                                                                  (Tacenta.UnitLifecycleT3.sliceOf
                                                                                    plaintext)
                                                                                  messageKey chunk) ∧
                                                                            Tacenta.UnitLifecycleT3.SessionRefines dh
                                                                              oracle.braidKem output.2.1
                                                                              (have __src :=
                                                                                Tacenta.UnitLifecycleEstablishInitiatorShape.establishedModelOf
                                                                                  dh s;
                                                                              { triple := tripleNext,
                                                                                braid :=
                                                                                  Model.Braid.BraidState.keysSampled 1 a
                                                                                    dk ekVector encoder,
                                                                                ratchetPrivate := __src.ratchetPrivate,
                                                                                identityAd := __src.identityAd,
                                                                                ourIdentityPublic :=
                                                                                  __src.ourIdentityPublic,
                                                                                peerIdentityPublic :=
                                                                                  __src.peerIdentityPublic,
                                                                                pendingInitial := __src.pendingInitial,
                                                                                establishedEphemeral :=
                                                                                  __src.establishedEphemeral }))
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishedEncrypt.established_encrypt_outcomes

/--
info: Tacenta.UnitLifecycleEstablishedEncrypt.established_triple_next_counters : ∀ (dh : Tacenta.UnitLifecycleT3.DhView)
  {R : Type} {rc : tacenta_session_unit.rand_core_1.RngCore R} {crc : tacenta_session_unit.rand_core_1.CryptoRng R}
  {our : tacenta_session_unit.lifecycle.Identity} {bundle : tacenta_session_unit.lifecycle.PublishedBundle}
  (p : Tacenta.UnitLifecycleEstablishInitiatorShape.InitiatorOutputParts rc crc our bundle)
  (tripleNext : Model.Triple.State) (header : Model.Triple.Header) (messageKey : Model.Lifecycle.Key),
  Model.Triple.sendDetailed (Tacenta.UnitLifecycleEstablishInitiatorShape.establishedModelOf dh p.session).triple 0
        none =
      Except.ok (tripleNext, header, messageKey) →
    tripleNext.classical.events = 0 ∧
      tripleNext.postQuantum.epoch = 0 ∧
        ∀ q ∈ tripleNext.postQuantum.chains,
          ∀ (ch : Model.SparseRatchet.Chain), q.2.send = some ch ∨ q.2.receive = some ch → ch.n ≤ 1
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishedEncrypt.established_triple_next_counters

/--
info: @Tacenta.UnitLifecycleEstablishedEncrypt.established_encrypt_successor_counterHeadroom : ∀
  [Tacenta.SessionUnitT1.DerivedKeysModel] {R E : Type} (rc : tacenta_session_unit.rand_core_1.RngCore R)
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
                        Tacenta.UnitLifecycleEstablishInitiatorShape.KemCiphertextLenOf →
                          Tacenta.UnitLifecycleRestoredSession.KemCiphertextLenBound →
                            ∀ (rcE : tacenta_session_unit.rand_core_1.RngCore E)
                              (crcE : tacenta_session_unit.rand_core_1.CryptoRng E)
                              (our : tacenta_session_unit.lifecycle.Identity)
                              (bundle : tacenta_session_unit.lifecycle.PublishedBundle)
                              (expected : tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes) (rng0 rng1 : E)
                              (s : tacenta_session_unit.lifecycle.Session),
                              tacenta_session_unit.lifecycle.establish_initiator_for rcE crcE our bundle expected rng0 =
                                  Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok s, rng1) →
                                ∀ (plaintext : Aeneas.Std.Slice Aeneas.Std.U8),
                                  (↑plaintext).length + 65770 ≤ Aeneas.Std.Usize.max →
                                    ∀ (rng : R),
                                      trace rng = oracle.draws →
                                        (∃ d1 d2 rest, trace rng = d1 :: d2 :: rest) →
                                          ∀ (bytes : Aeneas.Std.alloc.vec.Vec Aeneas.Std.U8)
                                            (s' : tacenta_session_unit.lifecycle.Session) (rng' : R),
                                            tacenta_session_unit.lifecycle.Session.encrypt rc crc s plaintext rng =
                                                Aeneas.Std.Result.ok
                                                  (Aeneas.Std.core.result.Result.Ok bytes, s', rng') →
                                              Tacenta.UnitLifecycleDecryptRunBounds.CounterHeadroom s'
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishedEncrypt.established_encrypt_successor_counterHeadroom

/--
info: @Tacenta.UnitLifecycleEstablishedEncrypt.established_encrypt_successor_refines : ∀
  [Tacenta.SessionUnitT1.DerivedKeysModel] {R E : Type} (rc : tacenta_session_unit.rand_core_1.RngCore R)
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
                        Tacenta.UnitLifecycleEstablishInitiatorShape.KemCiphertextLenOf →
                          Tacenta.UnitLifecycleRestoredSession.KemCiphertextLenBound →
                            ∀ (rcE : tacenta_session_unit.rand_core_1.RngCore E)
                              (crcE : tacenta_session_unit.rand_core_1.CryptoRng E)
                              (our : tacenta_session_unit.lifecycle.Identity)
                              (bundle : tacenta_session_unit.lifecycle.PublishedBundle)
                              (expected : tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes) (rng0 rng1 : E)
                              (s : tacenta_session_unit.lifecycle.Session),
                              tacenta_session_unit.lifecycle.establish_initiator_for rcE crcE our bundle expected rng0 =
                                  Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok s, rng1) →
                                ∀ (plaintext : Aeneas.Std.Slice Aeneas.Std.U8),
                                  (↑plaintext).length + 65770 ≤ Aeneas.Std.Usize.max →
                                    ∀ (rng : R),
                                      trace rng = oracle.draws →
                                        (∃ d1 d2 rest, trace rng = d1 :: d2 :: rest) →
                                          ∀ (bytes : Aeneas.Std.alloc.vec.Vec Aeneas.Std.U8)
                                            (s' : tacenta_session_unit.lifecycle.Session) (rng' : R),
                                            tacenta_session_unit.lifecycle.Session.encrypt rc crc s plaintext rng =
                                                Aeneas.Std.Result.ok
                                                  (Aeneas.Std.core.result.Result.Ok bytes, s', rng') →
                                              Tacenta.UnitLifecycleT3.SessionRefines dh oracle.braidKem s'
                                                  (Model.Lifecycle.encrypt view oracle
                                                      (Tacenta.UnitLifecycleEstablishInitiatorShape.establishedModelOf
                                                        dh s)
                                                      (Tacenta.UnitLifecycleT3.sliceOf plaintext)).session ∧
                                                trace rng' =
                                                    (Model.Lifecycle.encrypt view oracle
                                                          (Tacenta.UnitLifecycleEstablishInitiatorShape.establishedModelOf
                                                            dh s)
                                                          (Tacenta.UnitLifecycleT3.sliceOf plaintext)).oracle.draws ∧
                                                  ∃ a dk ekVector encoder,
                                                    (Model.Lifecycle.encrypt view oracle
                                                            (Tacenta.UnitLifecycleEstablishInitiatorShape.establishedModelOf
                                                              dh s)
                                                            (Tacenta.UnitLifecycleT3.sliceOf plaintext)).session.braid =
                                                      Model.Braid.BraidState.keysSampled 1 a dk ekVector encoder
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishedEncrypt.established_encrypt_successor_refines

/--
info: @Tacenta.UnitLifecycleEstablishedEncrypt.EstablishedEncryptHypotheses.refines : ∀ {R E : Type}
  {rc : tacenta_session_unit.rand_core_1.RngCore R} {crc : tacenta_session_unit.rand_core_1.CryptoRng R}
  {trace : R → List Model.Lifecycle.Key} {dh : Tacenta.UnitLifecycleT3.DhView} {kem : Tacenta.UnitLifecycleT3.KemView}
  {view : Model.Lifecycle.CodewordView} {oracle : Model.Lifecycle.Oracle}
  {rcE : tacenta_session_unit.rand_core_1.RngCore E} {crcE : tacenta_session_unit.rand_core_1.CryptoRng E}
  {our : tacenta_session_unit.lifecycle.Identity} {bundle : tacenta_session_unit.lifecycle.PublishedBundle}
  {expected : tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes} {rng0 rng1 : E}
  {s : tacenta_session_unit.lifecycle.Session} {plaintext : Aeneas.Std.Slice Aeneas.Std.U8} {rng : R},
  Tacenta.UnitLifecycleEstablishedEncrypt.EstablishedEncryptHypotheses rc crc trace dh kem view oracle rcE crcE our
      bundle expected rng0 rng1 s plaintext rng →
    Tacenta.UnitLifecycleT3.PublicEncryptWitness rc crc trace dh oracle.braidKem view oracle s
      (Tacenta.UnitLifecycleEstablishInitiatorShape.establishedModelOf dh s) plaintext rng
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishedEncrypt.EstablishedEncryptHypotheses.refines

/--
info: Tacenta.UnitLifecycleEstablishedEncrypt.zeroizingKeys_is : Tacenta.UnitLifecycleT3.ZeroizingRoundTrips
    (Aeneas.Std.Array Aeneas.Std.U8 32#usize ×
      Aeneas.Std.Array Aeneas.Std.U8 32#usize × Aeneas.Std.Array Aeneas.Std.U8 16#usize) ↔
  Tacenta.UnitLifecycleEstablishedEncrypt.ZeroizingKeysShape Tacenta.UnitSatisfiabilityJoint.Interp.real
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishedEncrypt.zeroizingKeys_is

/--
info: Tacenta.UnitLifecycleEstablishedEncrypt.nil_length_le : [].length ≤ Aeneas.Std.Usize.max
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishedEncrypt.nil_length_le

/--
info: Tacenta.UnitLifecycleEstablishedEncrypt.byteTrace_two : ∀ (seed : List Aeneas.Std.U8),
  64 ≤ seed.length →
    Tacenta.UnitLifecycleIntegrationScreen.byteTrace seed =
      List.take 32 (List.map Tacenta.SessionUnitBraidT3.u8 seed) ::
        List.take 32 (List.drop 32 (List.map Tacenta.SessionUnitBraidT3.u8 seed)) ::
          Tacenta.UnitLifecycleIntegrationScreen.chunks32
            (List.drop 32 (List.drop 32 (List.map Tacenta.SessionUnitBraidT3.u8 seed)))
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishedEncrypt.byteTrace_two

/--
info: Tacenta.UnitLifecycleEstablishedEncrypt.established_encrypt_hypotheses_jointly_satisfiable : ∀ (K : Model.Braid.Kem)
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
              ∀ (our : tacenta_session_unit.lifecycle.Identity) (seed : List Aeneas.Std.U8),
                64 ≤ seed.length →
                  ∃ oracle bundle s rng1,
                    oracle.braidKem = K ∧
                      oracle.draws = Tacenta.UnitLifecycleIntegrationScreen.byteTrace seed ∧
                        Tacenta.UnitLifecycleEstablishedEncrypt.EstablishedEncryptHypotheses
                          Tacenta.UnitLifecycleIntegrationScreen.byteRng Tacenta.UnitLifecycleIntegrationScreen.byteCrc
                          Tacenta.UnitLifecycleIntegrationScreen.byteTrace dh kem
                          Tacenta.UnitLifecycleRepair.witnessView oracle Tacenta.UnitLifecycleIntegrationScreen.byteRng
                          Tacenta.UnitLifecycleIntegrationScreen.byteCrc our bundle bundle.bundle.identity_key [] rng1 s
                          Tacenta.UnitLifecycleEstablishedEncrypt.emptyPlaintext seed
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishedEncrypt.established_encrypt_hypotheses_jointly_satisfiable

/--
info: Tacenta.UnitLifecycleEstablishedEncrypt.two_draws_of_64 : ∀ (seed : List Aeneas.Std.U8),
  seed.length = 64 →
    List.take 32 (List.map Tacenta.SessionUnitBraidT3.u8 seed) ++
        List.take 32 (List.drop 32 (List.map Tacenta.SessionUnitBraidT3.u8 seed)) =
      List.map Tacenta.SessionUnitBraidT3.u8 seed
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishedEncrypt.two_draws_of_64

/--
info: Tacenta.UnitLifecycleEstablishedEncrypt.established_encrypt_outcomes_at_witness : ∀ (K : Model.Braid.Kem)
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
              ∀ (our : tacenta_session_unit.lifecycle.Identity) (seed : List Aeneas.Std.U8),
                seed.length = 64 →
                  ∃ oracle bundle s rng1 output,
                    oracle.braidKem = K ∧
                      Tacenta.UnitLifecycleEstablishedEncrypt.EstablishedEncryptHypotheses
                          Tacenta.UnitLifecycleIntegrationScreen.byteRng Tacenta.UnitLifecycleIntegrationScreen.byteCrc
                          Tacenta.UnitLifecycleIntegrationScreen.byteTrace dh kem
                          Tacenta.UnitLifecycleRepair.witnessView oracle Tacenta.UnitLifecycleIntegrationScreen.byteRng
                          Tacenta.UnitLifecycleIntegrationScreen.byteCrc our bundle bundle.bundle.identity_key [] rng1 s
                          Tacenta.UnitLifecycleEstablishedEncrypt.emptyPlaintext seed ∧
                        tacenta_session_unit.lifecycle.Session.encrypt Tacenta.UnitLifecycleIntegrationScreen.byteRng
                              Tacenta.UnitLifecycleIntegrationScreen.byteCrc s
                              Tacenta.UnitLifecycleEstablishedEncrypt.emptyPlaintext seed =
                            Aeneas.Std.Result.ok output ∧
                          (K.keyGen (Model.Lifecycle.braidRandomness (List.map Tacenta.SessionUnitBraidT3.u8 seed)) =
                                none ∧
                              output.1 =
                                  Aeneas.Std.core.result.Result.Err
                                    tacenta_session_unit.lifecycle.Error.AgreementFailed ∧
                                output.2.1 =
                                  { triple := s.triple,
                                    braid := { state := tacenta_session_unit.tacenta_braid.State.Failed },
                                    ratchet_private := s.ratchet_private, identity_ad := s.identity_ad,
                                    our_identity_public := s.our_identity_public,
                                    peer_identity_public := s.peer_identity_public,
                                    pending_initial := s.pending_initial,
                                    established_ephemeral := s.established_ephemeral } ∨
                            K.keyGen (Model.Lifecycle.braidRandomness (List.map Tacenta.SessionUnitBraidT3.u8 seed)) ≠
                                none ∧
                              ∃ bytes,
                                output.1 = Aeneas.Std.core.result.Result.Ok bytes ∧
                                  ∃ auth kp encoder,
                                    output.2.1.braid.state =
                                      tacenta_session_unit.tacenta_braid.State.KeysSampled 1#u64 auth kp encoder)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishedEncrypt.established_encrypt_outcomes_at_witness

/--
info: Tacenta.UnitLifecycleEstablishedEncrypt.established_encrypt_success_reachable : ∀ (K : Model.Braid.Kem)
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
              ∀ (our : tacenta_session_unit.lifecycle.Identity) (seed : List Aeneas.Std.U8),
                seed.length = 64 →
                  K.keyGen (Model.Lifecycle.braidRandomness (List.map Tacenta.SessionUnitBraidT3.u8 seed)) ≠ none →
                    ∃ oracle bundle s rng1 bytes s' rng',
                      oracle.braidKem = K ∧
                        Tacenta.UnitLifecycleEstablishedEncrypt.EstablishedEncryptHypotheses
                            Tacenta.UnitLifecycleIntegrationScreen.byteRng
                            Tacenta.UnitLifecycleIntegrationScreen.byteCrc
                            Tacenta.UnitLifecycleIntegrationScreen.byteTrace dh kem
                            Tacenta.UnitLifecycleRepair.witnessView oracle
                            Tacenta.UnitLifecycleIntegrationScreen.byteRng
                            Tacenta.UnitLifecycleIntegrationScreen.byteCrc our bundle bundle.bundle.identity_key [] rng1
                            s Tacenta.UnitLifecycleEstablishedEncrypt.emptyPlaintext seed ∧
                          tacenta_session_unit.lifecycle.Session.encrypt Tacenta.UnitLifecycleIntegrationScreen.byteRng
                                Tacenta.UnitLifecycleIntegrationScreen.byteCrc s
                                Tacenta.UnitLifecycleEstablishedEncrypt.emptyPlaintext seed =
                              Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok bytes, s', rng') ∧
                            ∃ auth kp encoder,
                              s'.braid.state =
                                tacenta_session_unit.tacenta_braid.State.KeysSampled 1#u64 auth kp encoder
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishedEncrypt.established_encrypt_success_reachable

/--
info: Tacenta.UnitLifecycleEstablishedEncrypt.established_encrypt_refusal_reachable : ∀ (K : Model.Braid.Kem)
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
              ∀ (our : tacenta_session_unit.lifecycle.Identity) (seed : List Aeneas.Std.U8),
                seed.length = 64 →
                  K.keyGen (Model.Lifecycle.braidRandomness (List.map Tacenta.SessionUnitBraidT3.u8 seed)) = none →
                    ∃ oracle bundle s rng1 rng',
                      oracle.braidKem = K ∧
                        Tacenta.UnitLifecycleEstablishedEncrypt.EstablishedEncryptHypotheses
                            Tacenta.UnitLifecycleIntegrationScreen.byteRng
                            Tacenta.UnitLifecycleIntegrationScreen.byteCrc
                            Tacenta.UnitLifecycleIntegrationScreen.byteTrace dh kem
                            Tacenta.UnitLifecycleRepair.witnessView oracle
                            Tacenta.UnitLifecycleIntegrationScreen.byteRng
                            Tacenta.UnitLifecycleIntegrationScreen.byteCrc our bundle bundle.bundle.identity_key [] rng1
                            s Tacenta.UnitLifecycleEstablishedEncrypt.emptyPlaintext seed ∧
                          tacenta_session_unit.lifecycle.Session.encrypt Tacenta.UnitLifecycleIntegrationScreen.byteRng
                              Tacenta.UnitLifecycleIntegrationScreen.byteCrc s
                              Tacenta.UnitLifecycleEstablishedEncrypt.emptyPlaintext seed =
                            Aeneas.Std.Result.ok
                              (Aeneas.Std.core.result.Result.Err tacenta_session_unit.lifecycle.Error.AgreementFailed,
                                { triple := s.triple,
                                  braid := { state := tacenta_session_unit.tacenta_braid.State.Failed },
                                  ratchet_private := s.ratchet_private, identity_ad := s.identity_ad,
                                  our_identity_public := s.our_identity_public,
                                  peer_identity_public := s.peer_identity_public, pending_initial := s.pending_initial,
                                  established_ephemeral := s.established_ephemeral },
                                rng')
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishedEncrypt.established_encrypt_refusal_reachable

/--
info: Tacenta.UnitLifecycleEstablishedEncrypt.genFill_answers : ∀ (r : ℕ) {R : Type}
  (rc : tacenta_session_unit.rand_core_1.RngCore R) (crc : tacenta_session_unit.rand_core_1.CryptoRng R) (rng rng' : R)
  (seed : Aeneas.Std.Slice Aeneas.Std.U8),
  rc.fill_bytes rng Tacenta.UnitLifecycleIntegrationScreen.zeros64 = Aeneas.Std.Result.ok (rng', seed) →
    Model.Messages.leValue (Tacenta.UnitLifecycleT3.sliceOf seed) = r →
      Tacenta.UnitLifecycleEstablishedEncrypt.KeyGenAnswersShape
        Tacenta.UnitLifecycleEstablishedEncrypt.Interp.modelEncrypt Tacenta.UnitLifecycleEstablishedEncrypt.toyKemR rc
        crc rng r rng'
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishedEncrypt.genFill_answers

/--
info: Tacenta.UnitLifecycleEstablishedEncrypt.modelEncrypt_keyGenSeeded : Tacenta.UnitLifecycleEstablishedEncrypt.KeyGenSeededForShape
  Tacenta.UnitLifecycleEstablishedEncrypt.Interp.modelEncrypt Tacenta.UnitLifecycleEstablishedEncrypt.toyKemR
  Tacenta.UnitLifecycleIntegrationScreen.byteRng Tacenta.UnitLifecycleIntegrationScreen.byteCrc
  Tacenta.UnitLifecycleIntegrationScreen.byteTrace
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishedEncrypt.modelEncrypt_keyGenSeeded

/--
info: Tacenta.UnitLifecycleEstablishedEncrypt.modelEncrypt_kemAgrees : Tacenta.UnitSatisfiabilityBraidAgreements.KemAgreesShape
  Tacenta.UnitLifecycleEstablishedEncrypt.Interp.modelEncrypt Tacenta.UnitLifecycleEstablishedEncrypt.toyKemR
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishedEncrypt.modelEncrypt_kemAgrees

/--
info: @Tacenta.UnitLifecycleEstablishedEncrypt.modelEncrypt_keyPairGenerate : Tacenta.UnitSatisfiabilityJoint.KeyPairGenerateShape
  Tacenta.UnitLifecycleEstablishedEncrypt.Interp.modelEncrypt
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishedEncrypt.modelEncrypt_keyPairGenerate

/--
info: @Tacenta.UnitLifecycleEstablishedEncrypt.modelEncrypt_kemEncapsulate : Tacenta.UnitSatisfiabilityJoint.KemEncapsulateShape
  Tacenta.UnitLifecycleEstablishedEncrypt.Interp.modelEncrypt
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishedEncrypt.modelEncrypt_kemEncapsulate

/--
info: Tacenta.UnitLifecycleEstablishedEncrypt.byteRng_rngTotal : Tacenta.SessionUnitBraidT1.RngTotal
  Tacenta.UnitLifecycleIntegrationScreen.byteRng
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishedEncrypt.byteRng_rngTotal

/--
info: Tacenta.UnitLifecycleEstablishedEncrypt.modelEncrypt_allT1 : Tacenta.UnitSatisfiabilityBraidAgreements.AllT1Shapes
  Tacenta.UnitLifecycleEstablishedEncrypt.Interp.modelEncrypt
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishedEncrypt.modelEncrypt_allT1

/--
info: Tacenta.UnitLifecycleEstablishedEncrypt.leValue_replicate_zero : ∀ (n : ℕ),
  Model.Messages.leValue (List.replicate n 0) = 0
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishedEncrypt.leValue_replicate_zero

/--
info: Tacenta.UnitLifecycleEstablishedEncrypt.toyKemR_seeds : Tacenta.UnitLifecycleEstablishedEncrypt.toyKemR.keyGen
      (Model.Lifecycle.braidRandomness
        (List.map Tacenta.SessionUnitBraidT3.u8 Tacenta.UnitLifecycleEstablishedEncrypt.zeroSeed)) =
    none ∧
  Tacenta.UnitLifecycleEstablishedEncrypt.toyKemR.keyGen
      (Model.Lifecycle.braidRandomness
        (List.map Tacenta.SessionUnitBraidT3.u8 Tacenta.UnitLifecycleEstablishedEncrypt.oneSeed)) ≠
    none
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishedEncrypt.toyKemR_seeds

/--
info: Tacenta.UnitLifecycleEstablishedEncrypt.toyKemR_sizes : Tacenta.UnitLifecycleEstablishedEncrypt.KeyGenSizesOf
  Tacenta.UnitLifecycleEstablishedEncrypt.toyKemR
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishedEncrypt.toyKemR_sizes

/--
info: Tacenta.UnitLifecycleEstablishedEncrypt.established_encrypt_laws_model : Tacenta.UnitLifecycleDecryptScreen.DecryptJointLawsShape
    Tacenta.UnitLifecycleEstablishedEncrypt.Interp.modelEncrypt Tacenta.UnitLifecycleEstablishedEncrypt.viewEncrypt
    Tacenta.UnitLifecycleEstablishedEncrypt.toyKemR @Tacenta.UnitHeadroomInvariant.optionEqImpl ∧
  Nonempty
      (Tacenta.UnitSatisfiabilityJoint.InitiatorAxiom Tacenta.UnitLifecycleEstablishedEncrypt.Interp.modelEncrypt
        Tacenta.UnitLifecycleIntegrationScreen.byteRng) ∧
    Tacenta.UnitLifecycleEstablishInitiatorShape.InitiatorSuccessShape
        Tacenta.UnitLifecycleEstablishedEncrypt.Interp.modelEncrypt Tacenta.UnitLifecycleIntegrationScreen.byteRng
        Tacenta.UnitLifecycleIntegrationScreen.byteCrc ∧
      Tacenta.UnitLifecycleEstablishInitiatorShape.DhPublicValidShape
          Tacenta.UnitLifecycleEstablishedEncrypt.Interp.modelEncrypt ∧
        Tacenta.UnitLifecycleEstablishInitiatorShape.KemCiphertextLenLawShape (Aeneas.Std.Result.ok 0#usize)
            Tacenta.UnitLifecycleEstablishedEncrypt.Interp.modelEncrypt ∧
          Tacenta.UnitLifecycleEstablishedEncrypt.EncryptExtraLawsShape
              Tacenta.UnitLifecycleEstablishedEncrypt.InterpO.modelEncrypt
              Tacenta.UnitLifecycleEstablishedEncrypt.dhViewEncrypt
              Tacenta.UnitLifecycleEstablishedEncrypt.kemViewEncrypt Tacenta.UnitLifecycleEstablishedEncrypt.toyKemR
              (Aeneas.Std.Result.ok 0#usize) ∧
            (Tacenta.UnitLifecycleSessionCodec.ZeroizingVecRoundTripShape
                  Tacenta.UnitLifecycleEstablishedEncrypt.Interp.modelEncrypt ∧
                Tacenta.UnitLifecycleSessionCodec.DhPrivateBytesRoundTripShape
                    Tacenta.UnitLifecycleEstablishedEncrypt.Interp.modelEncrypt ∧
                  Tacenta.UnitLifecycleSessionCodec.DhPublicBytesRoundTripShape
                      Tacenta.UnitLifecycleEstablishedEncrypt.Interp.modelEncrypt ∧
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
                    none
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishedEncrypt.established_encrypt_laws_model

/--
info: @Tacenta.UnitLifecycleEstablishedEncrypt.encrypt_ok_parts : ∀ {R : Type}
  (rc : tacenta_session_unit.rand_core_1.RngCore R) (crc : tacenta_session_unit.rand_core_1.CryptoRng R)
  (s : tacenta_session_unit.lifecycle.Session) (plaintext : Aeneas.Std.Slice Aeneas.Std.U8) (rng : R)
  (v : Aeneas.Std.alloc.vec.Vec Aeneas.Std.U8) (s' : tacenta_session_unit.lifecycle.Session) (rng' : R),
  tacenta_session_unit.lifecycle.Session.encrypt rc crc s plaintext rng =
      Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok v, s', rng') →
    ∃ m e o b,
      tacenta_session_unit.tacenta_braid.Braid.send rc crc s.braid rng = Aeneas.Std.Result.ok ((m, e, o, b), rng') ∧
        ∃ sparse cand hdr mk,
          tacenta_session_unit.lifecycle.send_candidate s.triple e sparse =
              Aeneas.Std.Result.ok (cand, Aeneas.Std.core.result.Result.Ok (hdr, mk)) ∧
            s' =
              { triple := cand, braid := b, ratchet_private := s.ratchet_private, identity_ad := s.identity_ad,
                our_identity_public := s.our_identity_public, peer_identity_public := s.peer_identity_public,
                pending_initial := s.pending_initial, established_ephemeral := s.established_ephemeral }
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishedEncrypt.encrypt_ok_parts

/--
info: @Tacenta.UnitLifecycleEstablishedEncrypt.array_eq_of_bytes : ∀ {n : Aeneas.Std.Usize}
  {a b : Aeneas.Std.Array Aeneas.Std.U8 n},
  List.map (fun x => UInt8.ofNat ↑x) ↑a = List.map (fun x => UInt8.ofNat ↑x) ↑b → a = b
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishedEncrypt.array_eq_of_bytes

/--
info: Tacenta.UnitLifecycleEstablishedEncrypt.triple_eq_sent : ∀ (dh : Tacenta.UnitLifecycleT3.DhView) {R : Type}
  {rc : tacenta_session_unit.rand_core_1.RngCore R} {crc : tacenta_session_unit.rand_core_1.CryptoRng R}
  {our : tacenta_session_unit.lifecycle.Identity} {bundle : tacenta_session_unit.lifecycle.PublishedBundle}
  (p : Tacenta.UnitLifecycleEstablishInitiatorShape.InitiatorOutputParts rc crc our bundle)
  (tripleNext : Model.Triple.State) (header : Model.Triple.Header) (messageKey : Model.Lifecycle.Key),
  Model.Triple.sendDetailed (Tacenta.UnitLifecycleEstablishInitiatorShape.establishedModelOf dh p.session).triple 0
        none =
      Except.ok (tripleNext, header, messageKey) →
    ∀ (t : tacenta_session_unit.tacenta_triple.State),
      Tacenta.SessionUnitTripleT3.StateRefines Tacenta.SessionUnitTripleT3.ratchetAbs
          Tacenta.SessionUnitTripleT3.spqrAbs t tripleNext →
        ∃ cks c1,
          t =
            Tacenta.UnitLifecycleEstablishedEncrypt.sentTriple p.ratchetBytes p.peerRatchetBytes p.rootKey cks
              p.sparseRoot c1 p.sparseReceive
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishedEncrypt.triple_eq_sent

/--
info: Tacenta.UnitLifecycleEstablishedEncrypt.sentTriple_invariant : ∀
  (a4 a5 rk cks prk c1 c2 : Aeneas.Std.Array Aeneas.Std.U8 32#usize),
  Tacenta.SessionUnitT1.canonicalX25519 a4 = true →
    Tacenta.SessionUnitT1.canonicalX25519 a5 = true →
      (Tacenta.UnitLifecycleEstablishedEncrypt.sentTriple a4 a5 rk cks prk c1 c2).invariant = Aeneas.Std.Result.ok true
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishedEncrypt.sentTriple_invariant

/--
info: @Tacenta.UnitLifecycleEstablishedEncrypt.structural_sent : ∀ {R : Type}
  {rc : tacenta_session_unit.rand_core_1.RngCore R} {crc : tacenta_session_unit.rand_core_1.CryptoRng R}
  {our : tacenta_session_unit.lifecycle.Identity} {bundle : tacenta_session_unit.lifecycle.PublishedBundle},
  Tacenta.UnitLifecycleEstablishInitiatorShape.DhPublicValid →
    Tacenta.UnitLifecycleEstablishInitiatorShape.KemCiphertextLenOf →
      Tacenta.UnitHeadroomInvariant.OptionEqU64Shape
          @tacenta_session_unit.core.option.Option.Insts.CoreCmpPartialEqOption.eq →
        ∀ (p : Tacenta.UnitLifecycleEstablishInitiatorShape.InitiatorOutputParts rc crc our bundle)
          (cks c1 : Aeneas.Std.Array Aeneas.Std.U8 32#usize) (auth : tacenta_session_unit.tacenta_braid.Auth)
          (kp : tacenta_session_unit.tacenta_kem.IncrementalKeyPair)
          (enc : tacenta_session_unit.tacenta_erasure.Encoder),
          (Tacenta.UnitLifecycleEstablishedEncrypt.sentSession p cks c1 auth kp enc).structural_invariant =
            Aeneas.Std.Result.ok true
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishedEncrypt.structural_sent

/--
info: Tacenta.UnitLifecycleEstablishedEncrypt.keysSampled_invariant : tacenta_session_unit.tacenta_kem.HEADER_LEN =
    Aeneas.Std.Result.ok 64#usize →
  ∀ (auth : tacenta_session_unit.tacenta_braid.Auth) (kp : tacenta_session_unit.tacenta_kem.IncrementalKeyPair)
    (enc : tacenta_session_unit.tacenta_erasure.Encoder),
    enc.invariant = Aeneas.Std.Result.ok true →
      (∀ (len : Aeneas.Std.Usize),
          ↑len = 96 → tacenta_session_unit.tacenta_braid.encoder_sized enc len = Aeneas.Std.Result.ok true) →
        tacenta_session_unit.tacenta_braid.key_pair_valid kp = Aeneas.Std.Result.ok true →
          { state := tacenta_session_unit.tacenta_braid.State.KeysSampled 1#u64 auth kp enc }.invariant =
            Aeneas.Std.Result.ok true
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishedEncrypt.keysSampled_invariant

/--
info: @Tacenta.UnitLifecycleEstablishedEncrypt.sent_invariant : ∀ {R : Type} {rc : tacenta_session_unit.rand_core_1.RngCore R}
  {crc : tacenta_session_unit.rand_core_1.CryptoRng R} {our : tacenta_session_unit.lifecycle.Identity}
  {bundle : tacenta_session_unit.lifecycle.PublishedBundle},
  Tacenta.UnitLifecycleEstablishInitiatorShape.DhPublicValid →
    Tacenta.UnitLifecycleEstablishInitiatorShape.KemCiphertextLenOf →
      Tacenta.UnitHeadroomInvariant.OptionEqU64Shape
          @tacenta_session_unit.core.option.Option.Insts.CoreCmpPartialEqOption.eq →
        ∀ (p : Tacenta.UnitLifecycleEstablishInitiatorShape.InitiatorOutputParts rc crc our bundle)
          (cks c1 : Aeneas.Std.Array Aeneas.Std.U8 32#usize) (auth : tacenta_session_unit.tacenta_braid.Auth)
          (kp : tacenta_session_unit.tacenta_kem.IncrementalKeyPair)
          (enc : tacenta_session_unit.tacenta_erasure.Encoder),
          { state := tacenta_session_unit.tacenta_braid.State.KeysSampled 1#u64 auth kp enc }.invariant =
              Aeneas.Std.Result.ok true →
            (Tacenta.UnitLifecycleEstablishedEncrypt.sentSession p cks c1 auth kp enc).invariant =
              Aeneas.Std.Result.ok true
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishedEncrypt.sent_invariant

/--
info: @Tacenta.UnitLifecycleEstablishedEncrypt.keyPairValid_of_header : ∀ {K : Model.Braid.Kem},
  Tacenta.SessionUnitBraidT3.ValidateEkAgrees K →
    ∀ (kp : tacenta_session_unit.tacenta_kem.IncrementalKeyPair) (h v : Aeneas.Std.alloc.vec.Vec Aeneas.Std.U8),
      kp.header = Aeneas.Std.Result.ok h →
        kp.ek_vector = Aeneas.Std.Result.ok v →
          ∀ (ekSeed ekVector : Model.Braid.Bytes),
            Tacenta.SessionUnitBraidT3.vecOf h = ekSeed ++ K.hashEk ekSeed ekVector →
              Tacenta.SessionUnitBraidT3.vecOf v = ekVector →
                List.length ekSeed = 32 →
                  List.length ekVector = K.ekSize →
                    List.length (K.hashEk ekSeed ekVector) = 32 →
                      tacenta_session_unit.tacenta_braid.key_pair_valid kp = Aeneas.Std.Result.ok true
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishedEncrypt.keyPairValid_of_header

/--
info: Tacenta.UnitLifecycleEstablishedEncrypt.encoder_of_refines : Tacenta.SessionUnitDecoderBound.DivCeilValue →
  Tacenta.SessionUnitBraidT3.ErasureAgrees →
    ∀ (enc : tacenta_session_unit.tacenta_erasure.Encoder) (m : Model.Braid.Bytes),
      List.length m = 96 →
        Tacenta.SessionUnitBraidT3.EncoderRefines enc (Model.Braid.encode m).nextChunk.2 →
          enc.invariant = Aeneas.Std.Result.ok true ∧
            ∀ (len : Aeneas.Std.Usize),
              ↑len = 96 → tacenta_session_unit.tacenta_braid.encoder_sized enc len = Aeneas.Std.Result.ok true
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishedEncrypt.encoder_of_refines

/--
info: @Tacenta.UnitLifecycleEstablishedEncrypt.established_encrypt_successor_admissible : ∀
  [Tacenta.SessionUnitT1.DerivedKeysModel] {R E : Type} (rc : tacenta_session_unit.rand_core_1.RngCore R)
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
                        Tacenta.UnitLifecycleEstablishInitiatorShape.KemCiphertextLenOf →
                          Tacenta.UnitLifecycleRestoredSession.KemCiphertextLenBound →
                            Tacenta.UnitLifecycleEstablishInitiatorShape.DhPublicValid →
                              Tacenta.UnitHeadroomInvariant.OptionEqU64Shape
                                  @tacenta_session_unit.core.option.Option.Insts.CoreCmpPartialEqOption.eq →
                                Tacenta.SessionUnitBraidT3.KemLenAgrees oracle.braidKem →
                                  Tacenta.SessionUnitBraidT3.ValidateEkAgrees oracle.braidKem →
                                    Tacenta.UnitLifecycleEstablishedEncrypt.KeyGenSizesOf oracle.braidKem →
                                      Tacenta.SessionUnitDecoderBound.DivCeilValue →
                                        ∀ (rcE : tacenta_session_unit.rand_core_1.RngCore E)
                                          (crcE : tacenta_session_unit.rand_core_1.CryptoRng E)
                                          (our : tacenta_session_unit.lifecycle.Identity)
                                          (bundle : tacenta_session_unit.lifecycle.PublishedBundle)
                                          (expected : tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes)
                                          (rng0 rng1 : E) (s : tacenta_session_unit.lifecycle.Session),
                                          tacenta_session_unit.lifecycle.establish_initiator_for rcE crcE our bundle
                                                expected rng0 =
                                              Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok s, rng1) →
                                            ∀ (plaintext : Aeneas.Std.Slice Aeneas.Std.U8),
                                              (↑plaintext).length + 65770 ≤ Aeneas.Std.Usize.max →
                                                ∀ (rng : R),
                                                  trace rng = oracle.draws →
                                                    (∃ d1 d2 rest, trace rng = d1 :: d2 :: rest) →
                                                      ∀ (bytes : Aeneas.Std.alloc.vec.Vec Aeneas.Std.U8)
                                                        (s' : tacenta_session_unit.lifecycle.Session) (rng' : R),
                                                        tacenta_session_unit.lifecycle.Session.encrypt rc crc s
                                                              plaintext rng =
                                                            Aeneas.Std.Result.ok
                                                              (Aeneas.Std.core.result.Result.Ok bytes, s', rng') →
                                                          s'.invariant = Aeneas.Std.Result.ok true
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishedEncrypt.established_encrypt_successor_admissible

/--
info: @Tacenta.UnitLifecycleEstablishedEncrypt.established_encrypt_successor_hypotheses : ∀
  [Tacenta.SessionUnitT1.DerivedKeysModel] {R E : Type} (rc : tacenta_session_unit.rand_core_1.RngCore R)
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
                        Tacenta.UnitLifecycleEstablishInitiatorShape.KemCiphertextLenOf →
                          Tacenta.UnitLifecycleRestoredSession.KemCiphertextLenBound →
                            Tacenta.UnitLifecycleEstablishInitiatorShape.DhPublicValid →
                              Tacenta.UnitHeadroomInvariant.OptionEqU64Shape
                                  @tacenta_session_unit.core.option.Option.Insts.CoreCmpPartialEqOption.eq →
                                Tacenta.SessionUnitBraidT3.KemLenAgrees oracle.braidKem →
                                  Tacenta.SessionUnitBraidT3.ValidateEkAgrees oracle.braidKem →
                                    Tacenta.UnitLifecycleEstablishedEncrypt.KeyGenSizesOf oracle.braidKem →
                                      Tacenta.SessionUnitDecoderBound.DivCeilValue →
                                        ∀ (rcE : tacenta_session_unit.rand_core_1.RngCore E)
                                          (crcE : tacenta_session_unit.rand_core_1.CryptoRng E)
                                          (our : tacenta_session_unit.lifecycle.Identity)
                                          (bundle : tacenta_session_unit.lifecycle.PublishedBundle)
                                          (expected : tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes)
                                          (rng0 rng1 : E) (s : tacenta_session_unit.lifecycle.Session),
                                          tacenta_session_unit.lifecycle.establish_initiator_for rcE crcE our bundle
                                                expected rng0 =
                                              Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok s, rng1) →
                                            ∀ (plaintext : Aeneas.Std.Slice Aeneas.Std.U8),
                                              (↑plaintext).length + 65770 ≤ Aeneas.Std.Usize.max →
                                                ∀ (rng : R),
                                                  trace rng = oracle.draws →
                                                    (∃ d1 d2 rest, trace rng = d1 :: d2 :: rest) →
                                                      ∀ (bytes : Aeneas.Std.alloc.vec.Vec Aeneas.Std.U8)
                                                        (s' : tacenta_session_unit.lifecycle.Session) (rng' : R),
                                                        tacenta_session_unit.lifecycle.Session.encrypt rc crc s
                                                              plaintext rng =
                                                            Aeneas.Std.Result.ok
                                                              (Aeneas.Std.core.result.Result.Ok bytes, s', rng') →
                                                          s'.invariant = Aeneas.Std.Result.ok true ∧
                                                            Tacenta.UnitLifecycleT3.SessionRefines dh oracle.braidKem s'
                                                                (Model.Lifecycle.encrypt view oracle
                                                                    (Tacenta.UnitLifecycleEstablishInitiatorShape.establishedModelOf
                                                                      dh s)
                                                                    (Tacenta.UnitLifecycleT3.sliceOf
                                                                      plaintext)).session ∧
                                                              Tacenta.UnitLifecycleDecryptRunBounds.CounterHeadroom s' ∧
                                                                ∀ (msg : Model.Braid.Msg),
                                                                  Tacenta.SessionUnitBraidT3.HonestChunk
                                                                    (Model.Lifecycle.encrypt view oracle
                                                                          (Tacenta.UnitLifecycleEstablishInitiatorShape.establishedModelOf
                                                                            dh s)
                                                                          (Tacenta.UnitLifecycleT3.sliceOf
                                                                            plaintext)).session.braid
                                                                    msg
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishedEncrypt.established_encrypt_successor_hypotheses

/--
info: @Tacenta.UnitLifecycleEstablishedEncrypt.authOf_injective : ∀ {a b : tacenta_session_unit.tacenta_braid.Auth},
  Tacenta.SessionUnitBraidT3.AuthOf a = Tacenta.SessionUnitBraidT3.AuthOf b → a = b
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishedEncrypt.authOf_injective

/--
info: @Tacenta.UnitLifecycleEstablishedEncrypt.established_encrypt_successor_shape : ∀
  [Tacenta.SessionUnitT1.DerivedKeysModel] {R E : Type} (rc : tacenta_session_unit.rand_core_1.RngCore R)
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
                        Tacenta.UnitLifecycleEstablishInitiatorShape.KemCiphertextLenOf →
                          Tacenta.UnitLifecycleRestoredSession.KemCiphertextLenBound →
                            ∀ (rcE : tacenta_session_unit.rand_core_1.RngCore E)
                              (crcE : tacenta_session_unit.rand_core_1.CryptoRng E)
                              (our : tacenta_session_unit.lifecycle.Identity)
                              (bundle : tacenta_session_unit.lifecycle.PublishedBundle)
                              (expected : tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes) (rng0 rng1 : E)
                              (s : tacenta_session_unit.lifecycle.Session),
                              tacenta_session_unit.lifecycle.establish_initiator_for rcE crcE our bundle expected rng0 =
                                  Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok s, rng1) →
                                ∀ (plaintext : Aeneas.Std.Slice Aeneas.Std.U8),
                                  (↑plaintext).length + 65770 ≤ Aeneas.Std.Usize.max →
                                    ∀ (rng : R),
                                      trace rng = oracle.draws →
                                        (∃ d1 d2 rest, trace rng = d1 :: d2 :: rest) →
                                          ∀ (bytes : Aeneas.Std.alloc.vec.Vec Aeneas.Std.U8)
                                            (s' : tacenta_session_unit.lifecycle.Session) (rng' : R),
                                            tacenta_session_unit.lifecycle.Session.encrypt rc crc s plaintext rng =
                                                Aeneas.Std.Result.ok
                                                  (Aeneas.Std.core.result.Result.Ok bytes, s', rng') →
                                              ∃ p cks c1 kp enc,
                                                s = p.session ∧
                                                  s' =
                                                    Tacenta.UnitLifecycleEstablishedEncrypt.sentSession p cks c1 p.auth
                                                      kp enc
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishedEncrypt.established_encrypt_successor_shape

/--
info: @Tacenta.UnitLifecycleEstablishedEncrypt.EstablishedEncryptSuccessorHypotheses.successor : ∀ {R E : Type}
  {rc : tacenta_session_unit.rand_core_1.RngCore R} {crc : tacenta_session_unit.rand_core_1.CryptoRng R}
  {trace : R → List Model.Lifecycle.Key} {dh : Tacenta.UnitLifecycleT3.DhView} {kem : Tacenta.UnitLifecycleT3.KemView}
  {view : Model.Lifecycle.CodewordView} {oracle : Model.Lifecycle.Oracle}
  {rcE : tacenta_session_unit.rand_core_1.RngCore E} {crcE : tacenta_session_unit.rand_core_1.CryptoRng E}
  {our : tacenta_session_unit.lifecycle.Identity} {bundle : tacenta_session_unit.lifecycle.PublishedBundle}
  {expected : tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes} {rng0 rng1 : E}
  {s : tacenta_session_unit.lifecycle.Session} {plaintext : Aeneas.Std.Slice Aeneas.Std.U8} {rng : R},
  Tacenta.UnitLifecycleEstablishedEncrypt.EstablishedEncryptSuccessorHypotheses rc crc trace dh kem view oracle rcE crcE
      our bundle expected rng0 rng1 s plaintext rng →
    ∀ (bytes : Aeneas.Std.alloc.vec.Vec Aeneas.Std.U8) (s' : tacenta_session_unit.lifecycle.Session) (rng' : R),
      tacenta_session_unit.lifecycle.Session.encrypt rc crc s plaintext rng =
          Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok bytes, s', rng') →
        s'.invariant = Aeneas.Std.Result.ok true ∧
          Tacenta.UnitLifecycleT3.SessionRefines dh oracle.braidKem s'
              (Model.Lifecycle.encrypt view oracle
                  (Tacenta.UnitLifecycleEstablishInitiatorShape.establishedModelOf dh s)
                  (Tacenta.UnitLifecycleT3.sliceOf plaintext)).session ∧
            Tacenta.UnitLifecycleDecryptRunBounds.CounterHeadroom s' ∧
              ∀ (msg : Model.Braid.Msg),
                Tacenta.SessionUnitBraidT3.HonestChunk
                  (Model.Lifecycle.encrypt view oracle
                        (Tacenta.UnitLifecycleEstablishInitiatorShape.establishedModelOf dh s)
                        (Tacenta.UnitLifecycleT3.sliceOf plaintext)).session.braid
                  msg
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishedEncrypt.EstablishedEncryptSuccessorHypotheses.successor

/--
info: Tacenta.UnitLifecycleEstablishedEncrypt.established_encrypt_successor_hypotheses_jointly_satisfiable : ∀
  (K : Model.Braid.Kem) (dh : Tacenta.UnitLifecycleT3.DhView) (kem : Tacenta.UnitLifecycleT3.KemView),
  Tacenta.UnitLifecycleDecryptScreen.DecryptJointLaws K dh →
    Nonempty
        (Tacenta.UnitSatisfiabilityJoint.InitiatorAxiom Tacenta.UnitSatisfiabilityJoint.Interp.real
          Tacenta.UnitLifecycleIntegrationScreen.byteRng) →
      Tacenta.UnitLifecycleEstablishInitiatorShape.InitiatorSuccessShape Tacenta.UnitSatisfiabilityJoint.Interp.real
          Tacenta.UnitLifecycleIntegrationScreen.byteRng Tacenta.UnitLifecycleIntegrationScreen.byteCrc →
        Tacenta.UnitLifecycleEstablishInitiatorShape.DhPublicValid →
          Tacenta.UnitLifecycleEstablishInitiatorShape.KemCiphertextLenOf →
            Tacenta.UnitLifecycleEstablishedEncrypt.EncryptExtraLaws K dh kem →
              Tacenta.UnitLifecycleEstablishedEncrypt.KeyGenSizesOf K →
                ∀ (our : tacenta_session_unit.lifecycle.Identity) (seed : List Aeneas.Std.U8),
                  64 ≤ seed.length →
                    ∃ oracle bundle s rng1,
                      oracle.braidKem = K ∧
                        oracle.draws = Tacenta.UnitLifecycleIntegrationScreen.byteTrace seed ∧
                          Tacenta.UnitLifecycleEstablishedEncrypt.EstablishedEncryptSuccessorHypotheses
                            Tacenta.UnitLifecycleIntegrationScreen.byteRng
                            Tacenta.UnitLifecycleIntegrationScreen.byteCrc
                            Tacenta.UnitLifecycleIntegrationScreen.byteTrace dh kem
                            Tacenta.UnitLifecycleRepair.witnessView oracle
                            Tacenta.UnitLifecycleIntegrationScreen.byteRng
                            Tacenta.UnitLifecycleIntegrationScreen.byteCrc our bundle bundle.bundle.identity_key [] rng1
                            s Tacenta.UnitLifecycleEstablishedEncrypt.emptyPlaintext seed
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishedEncrypt.established_encrypt_successor_hypotheses_jointly_satisfiable

/--
info: Tacenta.UnitLifecycleEstablishedEncrypt.established_encrypt_successor_reachable : ∀ (K : Model.Braid.Kem)
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
              Tacenta.UnitLifecycleEstablishedEncrypt.KeyGenSizesOf K →
                ∀ (our : tacenta_session_unit.lifecycle.Identity) (seed : List Aeneas.Std.U8),
                  seed.length = 64 →
                    K.keyGen (Model.Lifecycle.braidRandomness (List.map Tacenta.SessionUnitBraidT3.u8 seed)) ≠ none →
                      ∃ oracle bundle s rng1 bytes s' rng',
                        oracle.braidKem = K ∧
                          Tacenta.UnitLifecycleEstablishedEncrypt.EstablishedEncryptSuccessorHypotheses
                              Tacenta.UnitLifecycleIntegrationScreen.byteRng
                              Tacenta.UnitLifecycleIntegrationScreen.byteCrc
                              Tacenta.UnitLifecycleIntegrationScreen.byteTrace dh kem
                              Tacenta.UnitLifecycleRepair.witnessView oracle
                              Tacenta.UnitLifecycleIntegrationScreen.byteRng
                              Tacenta.UnitLifecycleIntegrationScreen.byteCrc our bundle bundle.bundle.identity_key []
                              rng1 s Tacenta.UnitLifecycleEstablishedEncrypt.emptyPlaintext seed ∧
                            tacenta_session_unit.lifecycle.Session.encrypt
                                  Tacenta.UnitLifecycleIntegrationScreen.byteRng
                                  Tacenta.UnitLifecycleIntegrationScreen.byteCrc s
                                  Tacenta.UnitLifecycleEstablishedEncrypt.emptyPlaintext seed =
                                Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok bytes, s', rng') ∧
                              s'.invariant = Aeneas.Std.Result.ok true ∧
                                Tacenta.UnitLifecycleDecryptRunBounds.CounterHeadroom s'
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishedEncrypt.established_encrypt_successor_reachable

/--
info: def Tacenta.UnitLifecycleEstablishedEncrypt.KeyGenAnswersShape : Tacenta.UnitSatisfiabilityJoint.Interp →
  Model.Braid.Kem →
    {R : Type} →
      tacenta_session_unit.rand_core_1.RngCore R → tacenta_session_unit.rand_core_1.CryptoRng R → R → ℕ → R → Prop :=
fun I K {R} rc crc rng rand rng' =>
  (∃ kp dk ekSeed ekVector,
      I.ikpGenerate rc crc rng = Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok kp, rng') ∧
        K.keyGen rand = some (dk, ekSeed, ekVector) ∧
          (∃ h,
              I.ikpHeader kp = Aeneas.Std.Result.ok h ∧
                Tacenta.SessionUnitBraidT3.vecOf h = ekSeed ++ K.hashEk ekSeed ekVector) ∧
            (∃ v, I.ikpEkVector kp = Aeneas.Std.Result.ok v ∧ Tacenta.SessionUnitBraidT3.vecOf v = ekVector) ∧
              ∀ (ct1 ct2 : Aeneas.Std.Slice Aeneas.Std.U8),
                ct1.length = K.ct1Size →
                  ct2.length = K.ct2Size →
                    (∃ raw,
                        I.ikpDecapsulate kp ct1 ct2 = Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok raw) ∧
                          K.decaps dk (Tacenta.SessionUnitBraidT3.sliceOf ct1)
                              (Tacenta.SessionUnitBraidT3.sliceOf ct2) =
                            some (Tacenta.SessionUnitBraidT3.keyOf raw)) ∨
                      (∃ e, I.ikpDecapsulate kp ct1 ct2 = Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Err e)) ∧
                        K.decaps dk (Tacenta.SessionUnitBraidT3.sliceOf ct1) (Tacenta.SessionUnitBraidT3.sliceOf ct2) =
                          none) ∨
    (∃ e, I.ikpGenerate rc crc rng = Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Err e, rng')) ∧
      K.keyGen rand = none
-/
#guard_msgs in
#print Tacenta.UnitLifecycleEstablishedEncrypt.KeyGenAnswersShape

/--
info: def Tacenta.UnitLifecycleEstablishedEncrypt.KeyGenAnswers : Model.Braid.Kem →
  {R : Type} →
    tacenta_session_unit.rand_core_1.RngCore R → tacenta_session_unit.rand_core_1.CryptoRng R → R → ℕ → R → Prop :=
fun K {R} rc crc rng rand rng' =>
  (∃ kp dk ekSeed ekVector,
      tacenta_session_unit.tacenta_kem.IncrementalKeyPair.generate rc crc rng =
          Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok kp, rng') ∧
        K.keyGen rand = some (dk, ekSeed, ekVector) ∧
          (∃ h,
              kp.header = Aeneas.Std.Result.ok h ∧
                Tacenta.SessionUnitBraidT3.vecOf h = ekSeed ++ K.hashEk ekSeed ekVector) ∧
            (∃ v, kp.ek_vector = Aeneas.Std.Result.ok v ∧ Tacenta.SessionUnitBraidT3.vecOf v = ekVector) ∧
              Tacenta.SessionUnitBraidT3.KeyPairRefines K kp dk) ∨
    (∃ e,
        tacenta_session_unit.tacenta_kem.IncrementalKeyPair.generate rc crc rng =
          Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Err e, rng')) ∧
      K.keyGen rand = none
-/
#guard_msgs in
#print Tacenta.UnitLifecycleEstablishedEncrypt.KeyGenAnswers

/--
info: def Tacenta.UnitLifecycleEstablishedEncrypt.KeyGenSeededForShape : Tacenta.UnitSatisfiabilityJoint.Interp →
  Model.Braid.Kem →
    {R : Type} →
      tacenta_session_unit.rand_core_1.RngCore R →
        tacenta_session_unit.rand_core_1.CryptoRng R → (R → List Model.Lifecycle.Key) → Prop :=
fun I K {R} rc crc trace =>
  ∀ (rng : R) (d1 d2 : Model.Lifecycle.Key) (rest : List Model.Lifecycle.Key),
    trace rng = d1 :: d2 :: rest →
      ∃ rng',
        trace rng' = rest ∧
          Tacenta.UnitLifecycleEstablishedEncrypt.KeyGenAnswersShape I K rc crc rng
            (Model.Lifecycle.braidRandomness (d1 ++ d2)) rng'
-/
#guard_msgs in
#print Tacenta.UnitLifecycleEstablishedEncrypt.KeyGenSeededForShape

/--
info: def Tacenta.UnitLifecycleEstablishedEncrypt.KeyGenSeededFor : Model.Braid.Kem →
  {R : Type} →
    tacenta_session_unit.rand_core_1.RngCore R →
      tacenta_session_unit.rand_core_1.CryptoRng R → (R → List Model.Lifecycle.Key) → Prop :=
fun K {R} rc crc trace =>
  ∀ (rng : R) (d1 d2 : Model.Lifecycle.Key) (rest : List Model.Lifecycle.Key),
    trace rng = d1 :: d2 :: rest →
      ∃ rng',
        trace rng' = rest ∧
          Tacenta.UnitLifecycleEstablishedEncrypt.KeyGenAnswers K rc crc rng
            (Model.Lifecycle.braidRandomness (d1 ++ d2)) rng'
-/
#guard_msgs in
#print Tacenta.UnitLifecycleEstablishedEncrypt.KeyGenSeededFor

/--
info: def Tacenta.UnitLifecycleEstablishedEncrypt.KeyGenSizesOf : Model.Braid.Kem → Prop :=
fun K =>
  ∀ (rand : ℕ) (dk ekSeed ekVector : Model.Braid.Bytes),
    K.keyGen rand = some (dk, ekSeed, ekVector) →
      List.length ekSeed = 32 ∧ List.length ekVector = K.ekSize ∧ List.length (K.hashEk ekSeed ekVector) = 32
-/
#guard_msgs in
#print Tacenta.UnitLifecycleEstablishedEncrypt.KeyGenSizesOf

/--
info: def Tacenta.UnitLifecycleEstablishedEncrypt.firstComposite : Model.Lifecycle.CodewordView →
  Model.Lifecycle.Session → Model.Braid.Chunk → Model.CompositeHeader.Composite :=
fun view m chunk =>
  { dh := m.triple.classical.dhsPub, pn := UInt32.ofNat 0, n := UInt32.ofNat 0, pqEpoch := UInt64.ofNat 0,
    pqN := UInt64.ofNat 1, agEpoch := UInt64.ofNat 1, agType := Model.CompositeHeader.AgreementType.hdr,
    agChunk := some (view.send m.braid chunk) }
-/
#guard_msgs in
#print Tacenta.UnitLifecycleEstablishedEncrypt.firstComposite

/--
info: def Tacenta.UnitLifecycleEstablishedEncrypt.firstFrame : Model.Lifecycle.CodewordView →
  Model.Lifecycle.Oracle →
    Model.Lifecycle.Session → Model.Lifecycle.Bytes → Model.Lifecycle.Key → Model.Braid.Chunk → Model.Lifecycle.Bytes :=
fun view oracle m plaintext messageKey chunk =>
  Model.CompositeHeader.encodeMessage (Tacenta.UnitLifecycleEstablishedEncrypt.firstComposite view m chunk)
    (oracle.aeadSeal (Model.State.messageKeys messageKey Model.State.LabelSet.tacenta).1
      (Model.State.messageKeys messageKey Model.State.LabelSet.tacenta).2.1
      (Model.State.messageKeys messageKey Model.State.LabelSet.tacenta).2.2 plaintext
      (Model.Messages.concatAd m.identityAd
        (Model.CompositeHeader.encode (Tacenta.UnitLifecycleEstablishedEncrypt.firstComposite view m chunk))))
-/
#guard_msgs in
#print Tacenta.UnitLifecycleEstablishedEncrypt.firstFrame

/--
info: def Tacenta.UnitLifecycleEstablishedEncrypt.initialWire : Model.Lifecycle.Session →
  Model.Lifecycle.PendingInitial → Model.Lifecycle.Bytes → Model.Lifecycle.Bytes :=
fun m pending frame =>
  Model.Messages.encodeInitial (Model.PersistedState.SessionState.encodeEc m.ourIdentityPublic)
    (Model.PersistedState.SessionState.encodeEc pending.ephemeralPublic) pending.kemCiphertext
    (UInt32.ofNat pending.signedPrekeyId) (UInt32.ofNat pending.oneTimePrekeyId) (UInt32.ofNat pending.kemPrekeyId)
    frame
-/
#guard_msgs in
#print Tacenta.UnitLifecycleEstablishedEncrypt.initialWire

/--
info: structure Tacenta.UnitLifecycleEstablishedEncrypt.EstablishedEncryptHypotheses {R E : Type}
  (rc : tacenta_session_unit.rand_core_1.RngCore R) (crc : tacenta_session_unit.rand_core_1.CryptoRng R)
  (trace : R → List Model.Lifecycle.Key) (dh : Tacenta.UnitLifecycleT3.DhView) (kem : Tacenta.UnitLifecycleT3.KemView)
  (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
  (rcE : tacenta_session_unit.rand_core_1.RngCore E) (crcE : tacenta_session_unit.rand_core_1.CryptoRng E)
  (our : tacenta_session_unit.lifecycle.Identity) (bundle : tacenta_session_unit.lifecycle.PublishedBundle)
  (expected : tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes) (rng0 rng1 : E)
  (s : tacenta_session_unit.lifecycle.Session) (plaintext : Aeneas.Std.Slice Aeneas.Std.U8) (rng : R) : Prop
number of parameters: 19
fields:
  Tacenta.UnitLifecycleEstablishedEncrypt.EstablishedEncryptHypotheses.braid : Tacenta.UnitLifecycleT3.BraidSendRefinementContracts
      rc oracle.braidKem
  Tacenta.UnitLifecycleEstablishedEncrypt.EstablishedEncryptHypotheses.triple : Tacenta.UnitLifecycleT3.TripleSendRefinementContracts
  Tacenta.UnitLifecycleEstablishedEncrypt.EstablishedEncryptHypotheses.derivedKeys : Nonempty
      Tacenta.SessionUnitT1.DerivedKeysModel
  Tacenta.UnitLifecycleEstablishedEncrypt.EstablishedEncryptHypotheses.aead : Tacenta.UnitLifecycleT1.AeadSealBounded
  Tacenta.UnitLifecycleEstablishedEncrypt.EstablishedEncryptHypotheses.dhCodec : Tacenta.UnitLifecycleT1.DhCodecTotal
  Tacenta.UnitLifecycleEstablishedEncrypt.EstablishedEncryptHypotheses.oracleOf : Tacenta.UnitLifecycleT3.OracleOf rc
      crc dh kem trace oracle
  Tacenta.UnitLifecycleEstablishedEncrypt.EstablishedEncryptHypotheses.codec : Tacenta.UnitLifecycleT3.DhCodecOf dh
  Tacenta.UnitLifecycleEstablishedEncrypt.EstablishedEncryptHypotheses.codewordView : Tacenta.UnitLifecycleT3.CodewordViewSendOf
      view
  Tacenta.UnitLifecycleEstablishedEncrypt.EstablishedEncryptHypotheses.zeroizing80 : Tacenta.SessionUnitT3.ZeroizingRoundTrips80
  Tacenta.UnitLifecycleEstablishedEncrypt.EstablishedEncryptHypotheses.zeroizing32 : Tacenta.UnitLifecycleT3.ZeroizingRoundTrips
      (Aeneas.Std.Array Aeneas.Std.U8 32#usize)
  Tacenta.UnitLifecycleEstablishedEncrypt.EstablishedEncryptHypotheses.zeroizingKeys : Tacenta.UnitLifecycleT3.ZeroizingRoundTrips
      (Aeneas.Std.Array Aeneas.Std.U8 32#usize ×
        Aeneas.Std.Array Aeneas.Std.U8 32#usize × Aeneas.Std.Array Aeneas.Std.U8 16#usize)
  Tacenta.UnitLifecycleEstablishedEncrypt.EstablishedEncryptHypotheses.keyGen : Tacenta.UnitLifecycleEstablishedEncrypt.KeyGenSeededFor
      oracle.braidKem rc crc trace
  Tacenta.UnitLifecycleEstablishedEncrypt.EstablishedEncryptHypotheses.kemCiphertextLen : Tacenta.UnitLifecycleEstablishInitiatorShape.KemCiphertextLenOf
  Tacenta.UnitLifecycleEstablishedEncrypt.EstablishedEncryptHypotheses.kemCiphertextBound : Tacenta.UnitLifecycleRestoredSession.KemCiphertextLenBound
  Tacenta.UnitLifecycleEstablishedEncrypt.EstablishedEncryptHypotheses.established : tacenta_session_unit.lifecycle.establish_initiator_for
        rcE crcE our bundle expected rng0 =
      Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok s, rng1)
  Tacenta.UnitLifecycleEstablishedEncrypt.EstablishedEncryptHypotheses.room : (↑plaintext).length + 65770 ≤
      Aeneas.Std.Usize.max
  Tacenta.UnitLifecycleEstablishedEncrypt.EstablishedEncryptHypotheses.trace_eq : trace rng = oracle.draws
  Tacenta.UnitLifecycleEstablishedEncrypt.EstablishedEncryptHypotheses.draws : ∃ d1 d2 rest,
      trace rng = d1 :: d2 :: rest
constructor:
  Tacenta.UnitLifecycleEstablishedEncrypt.EstablishedEncryptHypotheses.mk {R E : Type}
    {rc : tacenta_session_unit.rand_core_1.RngCore R} {crc : tacenta_session_unit.rand_core_1.CryptoRng R}
    {trace : R → List Model.Lifecycle.Key} {dh : Tacenta.UnitLifecycleT3.DhView} {kem : Tacenta.UnitLifecycleT3.KemView}
    {view : Model.Lifecycle.CodewordView} {oracle : Model.Lifecycle.Oracle}
    {rcE : tacenta_session_unit.rand_core_1.RngCore E} {crcE : tacenta_session_unit.rand_core_1.CryptoRng E}
    {our : tacenta_session_unit.lifecycle.Identity} {bundle : tacenta_session_unit.lifecycle.PublishedBundle}
    {expected : tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes} {rng0 rng1 : E}
    {s : tacenta_session_unit.lifecycle.Session} {plaintext : Aeneas.Std.Slice Aeneas.Std.U8} {rng : R}
    (braid : Tacenta.UnitLifecycleT3.BraidSendRefinementContracts rc oracle.braidKem)
    (triple : Tacenta.UnitLifecycleT3.TripleSendRefinementContracts)
    (derivedKeys : Nonempty Tacenta.SessionUnitT1.DerivedKeysModel) (aead : Tacenta.UnitLifecycleT1.AeadSealBounded)
    (dhCodec : Tacenta.UnitLifecycleT1.DhCodecTotal)
    (oracleOf : Tacenta.UnitLifecycleT3.OracleOf rc crc dh kem trace oracle)
    (codec : Tacenta.UnitLifecycleT3.DhCodecOf dh) (codewordView : Tacenta.UnitLifecycleT3.CodewordViewSendOf view)
    (zeroizing80 : Tacenta.SessionUnitT3.ZeroizingRoundTrips80)
    (zeroizing32 : Tacenta.UnitLifecycleT3.ZeroizingRoundTrips (Aeneas.Std.Array Aeneas.Std.U8 32#usize))
    (zeroizingKeys :
      Tacenta.UnitLifecycleT3.ZeroizingRoundTrips
        (Aeneas.Std.Array Aeneas.Std.U8 32#usize ×
          Aeneas.Std.Array Aeneas.Std.U8 32#usize × Aeneas.Std.Array Aeneas.Std.U8 16#usize))
    (keyGen : Tacenta.UnitLifecycleEstablishedEncrypt.KeyGenSeededFor oracle.braidKem rc crc trace)
    (kemCiphertextLen : Tacenta.UnitLifecycleEstablishInitiatorShape.KemCiphertextLenOf)
    (kemCiphertextBound : Tacenta.UnitLifecycleRestoredSession.KemCiphertextLenBound)
    (established :
      tacenta_session_unit.lifecycle.establish_initiator_for rcE crcE our bundle expected rng0 =
        Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok s, rng1))
    (room : (↑plaintext).length + 65770 ≤ Aeneas.Std.Usize.max) (trace_eq : trace rng = oracle.draws)
    (draws : ∃ d1 d2 rest, trace rng = d1 :: d2 :: rest) :
    Tacenta.UnitLifecycleEstablishedEncrypt.EstablishedEncryptHypotheses rc crc trace dh kem view oracle rcE crcE our
      bundle expected rng0 rng1 s plaintext rng
-/
#guard_msgs in
#print Tacenta.UnitLifecycleEstablishedEncrypt.EstablishedEncryptHypotheses

/--
info: def Tacenta.UnitLifecycleEstablishedEncrypt.ZeroizingKeysShape : Tacenta.UnitSatisfiabilityJoint.Interp → Prop :=
fun I =>
  ∀
    (inst :
      tacenta_session_unit.zeroize.Zeroize
        (Aeneas.Std.Array Aeneas.Std.U8 32#usize ×
          Aeneas.Std.Array Aeneas.Std.U8 32#usize × Aeneas.Std.Array Aeneas.Std.U8 16#usize))
    (value :
      Aeneas.Std.Array Aeneas.Std.U8 32#usize ×
        Aeneas.Std.Array Aeneas.Std.U8 32#usize × Aeneas.Std.Array Aeneas.Std.U8 16#usize),
    ∃ wrapped, I.zNew inst value = Aeneas.Std.Result.ok wrapped ∧ I.zDeref inst wrapped = Aeneas.Std.Result.ok value
-/
#guard_msgs in
#print Tacenta.UnitLifecycleEstablishedEncrypt.ZeroizingKeysShape

/--
info: structure Tacenta.UnitLifecycleEstablishedEncrypt.EncryptExtraLawsShape (I : Tacenta.UnitOracleShape.InterpO)
  (dh : Tacenta.UnitOracleShape.DhViewOf I.toInterp) (kem : Tacenta.UnitOracleShape.KemViewOf I.toInterp)
  (K : Model.Braid.Kem) (ciphertextLen : Aeneas.Std.Result Aeneas.Std.Usize) : Prop
number of parameters: 5
fields:
  Tacenta.UnitLifecycleEstablishedEncrypt.EncryptExtraLawsShape.oracle : Tacenta.UnitOracleJoint.OracleLaws I dh kem
  Tacenta.UnitLifecycleEstablishedEncrypt.EncryptExtraLawsShape.encrypt : Tacenta.UnitSatisfiabilityJoint.EncryptAxiom
      I.toInterp Tacenta.UnitLifecycleIntegrationScreen.byteRng
  Tacenta.UnitLifecycleEstablishedEncrypt.EncryptExtraLawsShape.keyGen : Tacenta.UnitLifecycleEstablishedEncrypt.KeyGenSeededForShape
      I.toInterp K Tacenta.UnitLifecycleIntegrationScreen.byteRng Tacenta.UnitLifecycleIntegrationScreen.byteCrc
      Tacenta.UnitLifecycleIntegrationScreen.byteTrace
  Tacenta.UnitLifecycleEstablishedEncrypt.EncryptExtraLawsShape.zeroizingKeys : Tacenta.UnitLifecycleEstablishedEncrypt.ZeroizingKeysShape
      I.toInterp
  Tacenta.UnitLifecycleEstablishedEncrypt.EncryptExtraLawsShape.ciphertextBound : Tacenta.UnitLifecycleRestoredSession.KemCiphertextLenBoundShape
      ciphertextLen
constructor:
  Tacenta.UnitLifecycleEstablishedEncrypt.EncryptExtraLawsShape.mk {I : Tacenta.UnitOracleShape.InterpO}
    {dh : Tacenta.UnitOracleShape.DhViewOf I.toInterp} {kem : Tacenta.UnitOracleShape.KemViewOf I.toInterp}
    {K : Model.Braid.Kem} {ciphertextLen : Aeneas.Std.Result Aeneas.Std.Usize}
    (oracle : Tacenta.UnitOracleJoint.OracleLaws I dh kem)
    (encrypt : Tacenta.UnitSatisfiabilityJoint.EncryptAxiom I.toInterp Tacenta.UnitLifecycleIntegrationScreen.byteRng)
    (keyGen :
      Tacenta.UnitLifecycleEstablishedEncrypt.KeyGenSeededForShape I.toInterp K
        Tacenta.UnitLifecycleIntegrationScreen.byteRng Tacenta.UnitLifecycleIntegrationScreen.byteCrc
        Tacenta.UnitLifecycleIntegrationScreen.byteTrace)
    (zeroizingKeys : Tacenta.UnitLifecycleEstablishedEncrypt.ZeroizingKeysShape I.toInterp)
    (ciphertextBound : Tacenta.UnitLifecycleRestoredSession.KemCiphertextLenBoundShape ciphertextLen) :
    Tacenta.UnitLifecycleEstablishedEncrypt.EncryptExtraLawsShape I dh kem K ciphertextLen
-/
#guard_msgs in
#print Tacenta.UnitLifecycleEstablishedEncrypt.EncryptExtraLawsShape

/--
info: def Tacenta.UnitLifecycleEstablishedEncrypt.EncryptExtraLaws : Model.Braid.Kem →
  Tacenta.UnitLifecycleT3.DhView → Tacenta.UnitLifecycleT3.KemView → Prop :=
fun K dh kem =>
  Tacenta.UnitLifecycleEstablishedEncrypt.EncryptExtraLawsShape Tacenta.UnitOracleShape.InterpO.real
    (Tacenta.UnitOracleShape.dhViewOf dh) (Tacenta.UnitOracleShape.kemViewOf kem) K
    tacenta_session_unit.tacenta_boundary.kem.ciphertext_len
-/
#guard_msgs in
#print Tacenta.UnitLifecycleEstablishedEncrypt.EncryptExtraLaws

/--
info: def Tacenta.UnitLifecycleEstablishedEncrypt.emptyPlaintext : Aeneas.Std.Slice Aeneas.Std.U8 :=
⟨[], Tacenta.UnitLifecycleEstablishedEncrypt.nil_length_le⟩
-/
#guard_msgs in
#print Tacenta.UnitLifecycleEstablishedEncrypt.emptyPlaintext

/--
info: def Tacenta.UnitLifecycleEstablishedEncrypt.toyKemR : Model.Braid.Kem :=
have __src := Model.Braid.toyKem;
{ keyGen := fun r => if r = 0 then none else Model.Braid.toyKem.keyGen r, hashEk := __src.hashEk,
  encaps1 := __src.encaps1, encaps2 := __src.encaps2, decaps := __src.decaps, ekSize := __src.ekSize,
  ct1Size := __src.ct1Size, ct2Size := __src.ct2Size }
-/
#guard_msgs in
#print Tacenta.UnitLifecycleEstablishedEncrypt.toyKemR

/--
info: def Tacenta.UnitLifecycleEstablishedEncrypt.genFill : {R : Type} →
  tacenta_session_unit.rand_core_1.RngCore R →
    tacenta_session_unit.rand_core_1.CryptoRng R →
      R → Aeneas.Std.Result (Aeneas.Std.core.result.Result ℕ tacenta_session_unit.tacenta_kem.KemError × R) :=
fun {R} rc x rng => do
  let (rng', seed) ← rc.fill_bytes rng Tacenta.UnitLifecycleIntegrationScreen.zeros64
  have r : ℕ := Model.Messages.leValue (Tacenta.UnitLifecycleT3.sliceOf seed)
  Aeneas.Std.Result.ok
      (if r = 0 then Aeneas.Std.core.result.Result.Err () else Aeneas.Std.core.result.Result.Ok r, rng')
-/
#guard_msgs in
#print Tacenta.UnitLifecycleEstablishedEncrypt.genFill

/--
info: def Tacenta.UnitLifecycleEstablishedEncrypt.encapResult : Model.Lifecycle.Bytes →
  Model.Lifecycle.Bytes → Aeneas.Std.alloc.vec.Vec Aeneas.Std.U8 × Aeneas.Std.Array Aeneas.Std.U8 32#usize :=
fun _publicKey m => (Aeneas.Std.alloc.vec.Vec.new Aeneas.Std.U8, Tacenta.UnitOracleModel.bytesArr32 m)
-/
#guard_msgs in
#print Tacenta.UnitLifecycleEstablishedEncrypt.encapResult

/--
info: def Tacenta.UnitLifecycleEstablishedEncrypt.encapFill : Tacenta.UnitLifecycleIntegrationScreen.EncapFn :=
fun {R} rc x publicKey rng =>
  if (fun x => true) (Tacenta.UnitLifecycleT3.sliceOf publicKey) = true then do
    let (rng', m) ← rc.fill_bytes rng Tacenta.UnitLifecycleIntegrationScreen.zeros32
    Aeneas.Std.Result.ok
        (Aeneas.Std.core.result.Result.Ok
            (Tacenta.UnitLifecycleEstablishedEncrypt.encapResult (Tacenta.UnitLifecycleT3.sliceOf publicKey)
              (Tacenta.UnitLifecycleT3.sliceOf m)),
          rng')
  else Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Err (), rng)
-/
#guard_msgs in
#print Tacenta.UnitLifecycleEstablishedEncrypt.encapFill

/--
info: def Tacenta.UnitLifecycleEstablishedEncrypt.Interp.modelEncrypt : Tacenta.UnitSatisfiabilityJoint.Interp :=
let __src := Tacenta.UnitLifecycleEstablishedDecrypt.Interp.modelEstablished;
{ PrivateKey := __src.PrivateKey, PublicKeyBytes := __src.PublicKeyBytes, KemKeyPair := __src.KemKeyPair,
  IncrementalKeyPair := __src.IncrementalKeyPair, EncapsState := __src.EncapsState, Zeroizing := __src.Zeroizing,
  dhPrivFromBytes := __src.dhPrivFromBytes, dhPrivPublicKey := __src.dhPrivPublicKey, dhPrivAgree := __src.dhPrivAgree,
  dhPrivToBytes := __src.dhPrivToBytes, dhPubFromBytes := __src.dhPubFromBytes, dhPubAsBytes := __src.dhPubAsBytes,
  dhPubEq := __src.dhPubEq, dhIsPrimeOrderPublic := __src.dhIsPrimeOrderPublic, aeadEncrypt := __src.aeadEncrypt,
  aeadDecrypt := __src.aeadDecrypt, kemEncapsulate := fun {R} => Tacenta.UnitLifecycleEstablishedEncrypt.encapFill,
  kemDecapsulate := __src.kemDecapsulate, xeddsaVerify := __src.xeddsaVerify, hkdfSha256 := __src.hkdfSha256,
  hmacSha256 := __src.hmacSha256, HEADER_LEN := __src.HEADER_LEN, EK_VECTOR_LEN := __src.EK_VECTOR_LEN,
  CT1_LEN := __src.CT1_LEN, CT2_LEN := __src.CT2_LEN, ikpClone := __src.ikpClone,
  ikpGenerate := fun {R} => Tacenta.UnitLifecycleEstablishedEncrypt.genFill, ikpHeader := __src.ikpHeader,
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
#print Tacenta.UnitLifecycleEstablishedEncrypt.Interp.modelEncrypt

/--
info: def Tacenta.UnitLifecycleEstablishedEncrypt.InterpO.modelEncrypt : Tacenta.UnitOracleShape.InterpO :=
have __src := Tacenta.UnitLifecycleEstablishedEncrypt.Interp.modelEncrypt;
{ toInterp := __src, xeddsaSign := fun {R} => Tacenta.UnitOracleModel.signModelO }
-/
#guard_msgs in
#print Tacenta.UnitLifecycleEstablishedEncrypt.InterpO.modelEncrypt

/--
info: def Tacenta.UnitLifecycleEstablishedEncrypt.viewEncrypt : Tacenta.UnitLifecycleDecryptRatchetScreen.DhViewShape
  Tacenta.UnitLifecycleEstablishedEncrypt.Interp.modelEncrypt :=
{ privateKey := Tacenta.UnitLifecycleT3.arrayOf, publicKey := Tacenta.UnitLifecycleT3.arrayOf }
-/
#guard_msgs in
#print Tacenta.UnitLifecycleEstablishedEncrypt.viewEncrypt

/--
info: def Tacenta.UnitLifecycleEstablishedEncrypt.dhViewEncrypt : Tacenta.UnitOracleShape.DhViewOf
  Tacenta.UnitLifecycleEstablishedEncrypt.InterpO.modelEncrypt.toInterp :=
{ privateKey := Tacenta.UnitLifecycleEstablishedEncrypt.viewEncrypt.privateKey,
  publicKey := Tacenta.UnitLifecycleEstablishedEncrypt.viewEncrypt.publicKey }
-/
#guard_msgs in
#print Tacenta.UnitLifecycleEstablishedEncrypt.dhViewEncrypt

/--
info: def Tacenta.UnitLifecycleEstablishedEncrypt.kemViewEncrypt : Tacenta.UnitOracleShape.KemViewOf
  Tacenta.UnitLifecycleEstablishedEncrypt.InterpO.modelEncrypt.toInterp :=
{ keyPair := fun x => [] }
-/
#guard_msgs in
#print Tacenta.UnitLifecycleEstablishedEncrypt.kemViewEncrypt

/--
info: def Tacenta.UnitLifecycleEstablishedEncrypt.zeroSeed : List Aeneas.Std.U8 :=
List.replicate 64 0#u8
-/
#guard_msgs in
#print Tacenta.UnitLifecycleEstablishedEncrypt.zeroSeed

/--
info: def Tacenta.UnitLifecycleEstablishedEncrypt.oneSeed : List Aeneas.Std.U8 :=
1#u8 :: List.replicate 63 0#u8
-/
#guard_msgs in
#print Tacenta.UnitLifecycleEstablishedEncrypt.oneSeed

/--
info: def Tacenta.UnitLifecycleEstablishedEncrypt.sentChains : Aeneas.Std.Array Aeneas.Std.U8 32#usize →
  Aeneas.Std.Array Aeneas.Std.U8 32#usize →
    Aeneas.Std.alloc.vec.Vec (Aeneas.Std.U64 × tacenta_session_unit.tacenta_spqr.Chains) :=
fun c1 c2 =>
  Tacenta.UnitHeadroomSatisfiable.vecOf
    [(0#u64, { send := some { ck := c1, n := 1#u64 }, receive := some { ck := c2, n := 0#u64 } })]
    (⋯ :
      [(0#u64, { send := some { ck := c1, n := 1#u64 }, receive := some { ck := c2, n := 0#u64 } })].length ≤
        4294967295)
-/
#guard_msgs in
#print Tacenta.UnitLifecycleEstablishedEncrypt.sentChains

/--
info: def Tacenta.UnitLifecycleEstablishedEncrypt.sentTriple : Aeneas.Std.Array Aeneas.Std.U8 32#usize →
  Aeneas.Std.Array Aeneas.Std.U8 32#usize →
    Aeneas.Std.Array Aeneas.Std.U8 32#usize →
      Aeneas.Std.Array Aeneas.Std.U8 32#usize →
        Aeneas.Std.Array Aeneas.Std.U8 32#usize →
          Aeneas.Std.Array Aeneas.Std.U8 32#usize →
            Aeneas.Std.Array Aeneas.Std.U8 32#usize → tacenta_session_unit.tacenta_triple.State :=
fun a4 a5 rk cks prk c1 c2 =>
  {
    classical :=
      { dhs_pub := a4, dhr_pub := some a5, rk := rk, cks := some cks, ckr := none, ns := 1#u32, nr := 0#u32,
        pn := 0#u32, skipped := Aeneas.Std.alloc.vec.Vec.new tacenta_session_unit.tacenta_ratchet.SkippedKey,
        events := 0#u32, labels := tacenta_session_unit.tacenta_ratchet.LabelSet.Tacenta },
    post_quantum :=
      { rk := prk, epoch := 0#u64, chains := Tacenta.UnitLifecycleEstablishedEncrypt.sentChains c1 c2,
        skipped := Aeneas.Std.alloc.vec.Vec.new tacenta_session_unit.tacenta_spqr.Skipped,
        direction := tacenta_session_unit.tacenta_spqr.Direction.A2b } }
-/
#guard_msgs in
#print Tacenta.UnitLifecycleEstablishedEncrypt.sentTriple

/--
info: def Tacenta.UnitLifecycleEstablishedEncrypt.sentSession : {R : Type} →
  {rc : tacenta_session_unit.rand_core_1.RngCore R} →
    {crc : tacenta_session_unit.rand_core_1.CryptoRng R} →
      {our : tacenta_session_unit.lifecycle.Identity} →
        {bundle : tacenta_session_unit.lifecycle.PublishedBundle} →
          Tacenta.UnitLifecycleEstablishInitiatorShape.InitiatorOutputParts rc crc our bundle →
            Aeneas.Std.Array Aeneas.Std.U8 32#usize →
              Aeneas.Std.Array Aeneas.Std.U8 32#usize →
                tacenta_session_unit.tacenta_braid.Auth →
                  tacenta_session_unit.tacenta_kem.IncrementalKeyPair →
                    tacenta_session_unit.tacenta_erasure.Encoder → tacenta_session_unit.lifecycle.Session :=
fun {R} {rc} {crc} {our} {bundle} p cks c1 auth kp enc =>
  have __src := p.session;
  {
    triple :=
      Tacenta.UnitLifecycleEstablishedEncrypt.sentTriple p.ratchetBytes p.peerRatchetBytes p.rootKey cks p.sparseRoot c1
        p.sparseReceive,
    braid := { state := tacenta_session_unit.tacenta_braid.State.KeysSampled 1#u64 auth kp enc },
    ratchet_private := __src.ratchet_private, identity_ad := __src.identity_ad,
    our_identity_public := __src.our_identity_public, peer_identity_public := __src.peer_identity_public,
    pending_initial := __src.pending_initial, established_ephemeral := __src.established_ephemeral }
-/
#guard_msgs in
#print Tacenta.UnitLifecycleEstablishedEncrypt.sentSession

/--
info: structure Tacenta.UnitLifecycleEstablishedEncrypt.EstablishedEncryptSuccessorHypotheses {R E : Type}
  (rc : tacenta_session_unit.rand_core_1.RngCore R) (crc : tacenta_session_unit.rand_core_1.CryptoRng R)
  (trace : R → List Model.Lifecycle.Key) (dh : Tacenta.UnitLifecycleT3.DhView) (kem : Tacenta.UnitLifecycleT3.KemView)
  (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
  (rcE : tacenta_session_unit.rand_core_1.RngCore E) (crcE : tacenta_session_unit.rand_core_1.CryptoRng E)
  (our : tacenta_session_unit.lifecycle.Identity) (bundle : tacenta_session_unit.lifecycle.PublishedBundle)
  (expected : tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes) (rng0 rng1 : E)
  (s : tacenta_session_unit.lifecycle.Session) (plaintext : Aeneas.Std.Slice Aeneas.Std.U8) (rng : R) : Prop
number of parameters: 19
parents:
  Tacenta.UnitLifecycleEstablishedEncrypt.EstablishedEncryptSuccessorHypotheses.toEstablishedEncryptHypotheses : Tacenta.UnitLifecycleEstablishedEncrypt.EstablishedEncryptHypotheses
    rc crc trace dh kem view oracle rcE crcE our bundle expected rng0 rng1 s plaintext rng
fields:
  Tacenta.UnitLifecycleEstablishedEncrypt.EstablishedEncryptHypotheses.braid : Tacenta.UnitLifecycleT3.BraidSendRefinementContracts
      rc oracle.braidKem
  Tacenta.UnitLifecycleEstablishedEncrypt.EstablishedEncryptHypotheses.triple : Tacenta.UnitLifecycleT3.TripleSendRefinementContracts
  Tacenta.UnitLifecycleEstablishedEncrypt.EstablishedEncryptHypotheses.derivedKeys : Nonempty
      Tacenta.SessionUnitT1.DerivedKeysModel
  Tacenta.UnitLifecycleEstablishedEncrypt.EstablishedEncryptHypotheses.aead : Tacenta.UnitLifecycleT1.AeadSealBounded
  Tacenta.UnitLifecycleEstablishedEncrypt.EstablishedEncryptHypotheses.dhCodec : Tacenta.UnitLifecycleT1.DhCodecTotal
  Tacenta.UnitLifecycleEstablishedEncrypt.EstablishedEncryptHypotheses.oracleOf : Tacenta.UnitLifecycleT3.OracleOf rc
      crc dh kem trace oracle
  Tacenta.UnitLifecycleEstablishedEncrypt.EstablishedEncryptHypotheses.codec : Tacenta.UnitLifecycleT3.DhCodecOf dh
  Tacenta.UnitLifecycleEstablishedEncrypt.EstablishedEncryptHypotheses.codewordView : Tacenta.UnitLifecycleT3.CodewordViewSendOf
      view
  Tacenta.UnitLifecycleEstablishedEncrypt.EstablishedEncryptHypotheses.zeroizing80 : Tacenta.SessionUnitT3.ZeroizingRoundTrips80
  Tacenta.UnitLifecycleEstablishedEncrypt.EstablishedEncryptHypotheses.zeroizing32 : Tacenta.UnitLifecycleT3.ZeroizingRoundTrips
      (Aeneas.Std.Array Aeneas.Std.U8 32#usize)
  Tacenta.UnitLifecycleEstablishedEncrypt.EstablishedEncryptHypotheses.zeroizingKeys : Tacenta.UnitLifecycleT3.ZeroizingRoundTrips
      (Aeneas.Std.Array Aeneas.Std.U8 32#usize ×
        Aeneas.Std.Array Aeneas.Std.U8 32#usize × Aeneas.Std.Array Aeneas.Std.U8 16#usize)
  Tacenta.UnitLifecycleEstablishedEncrypt.EstablishedEncryptHypotheses.keyGen : Tacenta.UnitLifecycleEstablishedEncrypt.KeyGenSeededFor
      oracle.braidKem rc crc trace
  Tacenta.UnitLifecycleEstablishedEncrypt.EstablishedEncryptHypotheses.kemCiphertextLen : Tacenta.UnitLifecycleEstablishInitiatorShape.KemCiphertextLenOf
  Tacenta.UnitLifecycleEstablishedEncrypt.EstablishedEncryptHypotheses.kemCiphertextBound : Tacenta.UnitLifecycleRestoredSession.KemCiphertextLenBound
  Tacenta.UnitLifecycleEstablishedEncrypt.EstablishedEncryptHypotheses.established : tacenta_session_unit.lifecycle.establish_initiator_for
        rcE crcE our bundle expected rng0 =
      Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok s, rng1)
  Tacenta.UnitLifecycleEstablishedEncrypt.EstablishedEncryptHypotheses.room : (↑plaintext).length + 65770 ≤
      Aeneas.Std.Usize.max
  Tacenta.UnitLifecycleEstablishedEncrypt.EstablishedEncryptHypotheses.trace_eq : trace rng = oracle.draws
  Tacenta.UnitLifecycleEstablishedEncrypt.EstablishedEncryptHypotheses.draws : ∃ d1 d2 rest,
      trace rng = d1 :: d2 :: rest
  Tacenta.UnitLifecycleEstablishedEncrypt.EstablishedEncryptSuccessorHypotheses.dhPublicValid : Tacenta.UnitLifecycleEstablishInitiatorShape.DhPublicValid
  Tacenta.UnitLifecycleEstablishedEncrypt.EstablishedEncryptSuccessorHypotheses.optionEq : Tacenta.UnitHeadroomInvariant.OptionEqU64Shape
      @tacenta_session_unit.core.option.Option.Insts.CoreCmpPartialEqOption.eq
  Tacenta.UnitLifecycleEstablishedEncrypt.EstablishedEncryptSuccessorHypotheses.kemLen : Tacenta.SessionUnitBraidT3.KemLenAgrees
      oracle.braidKem
  Tacenta.UnitLifecycleEstablishedEncrypt.EstablishedEncryptSuccessorHypotheses.validateEk : Tacenta.SessionUnitBraidT3.ValidateEkAgrees
      oracle.braidKem
  Tacenta.UnitLifecycleEstablishedEncrypt.EstablishedEncryptSuccessorHypotheses.keyGenSizes : Tacenta.UnitLifecycleEstablishedEncrypt.KeyGenSizesOf
      oracle.braidKem
  Tacenta.UnitLifecycleEstablishedEncrypt.EstablishedEncryptSuccessorHypotheses.divCeil : Tacenta.SessionUnitDecoderBound.DivCeilValue
constructor:
  Tacenta.UnitLifecycleEstablishedEncrypt.EstablishedEncryptSuccessorHypotheses.mk {R E : Type}
    {rc : tacenta_session_unit.rand_core_1.RngCore R} {crc : tacenta_session_unit.rand_core_1.CryptoRng R}
    {trace : R → List Model.Lifecycle.Key} {dh : Tacenta.UnitLifecycleT3.DhView} {kem : Tacenta.UnitLifecycleT3.KemView}
    {view : Model.Lifecycle.CodewordView} {oracle : Model.Lifecycle.Oracle}
    {rcE : tacenta_session_unit.rand_core_1.RngCore E} {crcE : tacenta_session_unit.rand_core_1.CryptoRng E}
    {our : tacenta_session_unit.lifecycle.Identity} {bundle : tacenta_session_unit.lifecycle.PublishedBundle}
    {expected : tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes} {rng0 rng1 : E}
    {s : tacenta_session_unit.lifecycle.Session} {plaintext : Aeneas.Std.Slice Aeneas.Std.U8} {rng : R}
    (toEstablishedEncryptHypotheses :
      Tacenta.UnitLifecycleEstablishedEncrypt.EstablishedEncryptHypotheses rc crc trace dh kem view oracle rcE crcE our
        bundle expected rng0 rng1 s plaintext rng)
    (dhPublicValid : Tacenta.UnitLifecycleEstablishInitiatorShape.DhPublicValid)
    (optionEq :
      Tacenta.UnitHeadroomInvariant.OptionEqU64Shape
        @tacenta_session_unit.core.option.Option.Insts.CoreCmpPartialEqOption.eq)
    (kemLen : Tacenta.SessionUnitBraidT3.KemLenAgrees oracle.braidKem)
    (validateEk : Tacenta.SessionUnitBraidT3.ValidateEkAgrees oracle.braidKem)
    (keyGenSizes : Tacenta.UnitLifecycleEstablishedEncrypt.KeyGenSizesOf oracle.braidKem)
    (divCeil : Tacenta.SessionUnitDecoderBound.DivCeilValue) :
    Tacenta.UnitLifecycleEstablishedEncrypt.EstablishedEncryptSuccessorHypotheses rc crc trace dh kem view oracle rcE
      crcE our bundle expected rng0 rng1 s plaintext rng
field notation resolution order:
  Tacenta.UnitLifecycleEstablishedEncrypt.EstablishedEncryptSuccessorHypotheses, Tacenta.UnitLifecycleEstablishedEncrypt.EstablishedEncryptHypotheses
-/
#guard_msgs in
#print Tacenta.UnitLifecycleEstablishedEncrypt.EstablishedEncryptSuccessorHypotheses
