import Translation.UnitKemWrapperModel

/-!
# The decrypt refinement's hypotheses at a session whose Braid holds a key pair

`UnitLifecycleDecryptScreen.decrypt_hypotheses_jointly_satisfiable`, and its corollary at the KEM model
read off the wrapper (`UnitKemWrapperModel.decrypt_hypotheses_jointly_satisfiable_at_wrapperKem`), use
a witness whose Braid is in `KeysUnsampled`.  There `SessionRefines` holds at every Braid KEM model, the
run carries no agreement chunk, and the KEM model enters the hypotheses only through the agreements,
so the coupling of the agreements to the oracle's KEM model holds by construction.  This module gives a
second witness, built for the hypotheses as the first is, whose Braid holds a key pair and whose model
Braid holds that pair's bytes, so that `SessionRefines` at the KEM model read off the wrapper is asked
of a held value.

## What is shown

* **The held state.**  `heldReal` is the first witness's session (`invReal`, over
  `UnitHeadroomSatisfiable.sessionOf`) with its Braid replaced by `KeysSampled` at epoch 1
  (`heldBraid`), holding a key pair `kp` that `IncrementalKeyPair::generate` returned from a 64-byte
  stream and an encoder `enc` that `Encoder::new` built from the pair's header followed by a 32-byte MAC
  and that has emitted one chunk.  `heldModel` is the model session read off it (`modelOf`) with the
  model Braid `heldModelBraid dk ekVector header`: `keysSampled 1` holding the 64 drawn bytes as the
  private part `dk`, the bytes of the pair's `ek_vector` as `ekVector`, and the encoder of `header ++
  macHdr` advanced once.  `heldModelBraid_is_send`: that model state is what `Model.Braid.send
  wrapperKem` returns from the fresh initiator state at the randomness the 64 bytes are (transition
  (1)).  This is the shape `Braid::send` gives the initiator from `KeysUnsampled`
  (`tacenta-core/session-unit/src/tacenta_braid.rs`, the `KeysUnsampled` arm of `send`).
* **The agreements at the held key** (`held_key_agreements`), from `wrapperKem`'s definition and the
  wrapper laws `LawGeneratedKeyPair` and `LawValidateEkUnique`, and not by projecting
  `KemAgreesFor wrapperKem`: `wrapperKem.keyGen` at the held randomness returns the held private part,
  the header's first 32 bytes and the vector's bytes; the model hash of that seed and vector is the
  header's last 32 bytes; the header has 64 bytes and the vector `wrapperKem.ekSize`; `key_pair_valid kp`
  returns `true`; and `FreshKeyPairRefines wrapperKem kp dk ekVector`.  Which parts are definitional:
  `wrapperKem`'s operations call the real `generate` and `decapsulate` on the held bytes, so the
  key-generation part and the decapsulation clause (which compares `wrapperKem.decaps dk` with the
  real `decapsulate kp`, that is, the real `decapsulate` with itself) hold by unfolding `wrapperKem`,
  with only the totality of `decapsulate` on generated pairs taken from a law; so does `HeldKemAt`'s
  conjunct that the model Braid is the model's transition (1).  What the held value tests beyond the
  definitions: the vector by value (`held_relation_pins_vector`, at every KEM model), the header hash
  (through `hashEkOf`, `LawValidateEkUnique` and `validate_ek` accepting the generated pair), and the
  lengths.
* **`Session::invariant`** (`held_invariant`): the structural clauses (a) to (h) as for the first
  witness, with the Braid's epoch, tag and role read off `KeysSampled` at epoch 1
  (`structural_held`), and clause (g)'s Braid arm (`heldBraid_invariant`): `Encoder::invariant` of the
  encoder, `encoder_sized(enc, HEADER_LEN + MAC_LEN)` and `key_pair_valid(kp)` (`held_encoder`,
  `held_key_agreements`).
* **The relation is not met by construction.**  `held_sessionRefines` builds `SessionRefines` at the
  held state from `FreshKeyPairRefines` and `EncoderRefines`; `held_relation_pins_vector`: at every KEM
  model the relation fixes the model's vector to the bytes of the real `ek_vector`;
  `held_not_refines_toyKem`: at `toyKem` the relation is false, a length mismatch (`toyKem.decaps`
  returns the private part itself, and a private part that is not 32 bytes is no shared secret), not a
  comparison of held bytes.  At the first witness the relation holds at every model.
* **The joint statements.**  `decrypt_hypotheses_jointly_satisfiable_at_wrapperKem_held`: under
  `DecryptWrapperLaws dh` and `LawGenerateSucceeds`, there are an oracle whose Braid KEM model is
  `wrapperKem`, a session that passes `Session::invariant` and a related model session holding a key
  pair as `HeldKemAt` states, the first witness's message and source, at which every field of
  `DecryptHypotheses` holds, for every codeword view.
* **A caller-selected run carrying a chunk** (`decrypt_hypotheses_with_chunk_at_wrapperKem_held`; not a
  claim).  The same hypotheses at a message whose agreement part is a `ct1` message of epoch 1 carrying
  a chunk, with the chunk and the codeword view chosen together: the chunk is index 0 and 32 zero bytes,
  shown a codeword of 1408 zero bytes by the real encoder (`zero_chunk_codeword`), and the view is a
  constant that reads every chunk as that codeword.  1408 zero bytes is not a ciphertext `encapsulate1`
  produces, so no honest responder sends this chunk; `HonestChunk` asks nothing at `keysSampled`; and the
  model's refusal at the first agreement discards the Braid step.  It is not a non-vacuity statement for
  chunks, which would take every chunk that fits the real decoder (with its view derived from it), where
  this fixes one chunk and one view.
* **The model's step** (`held_model_refuses_of_agreement`): at either message it refuses at the first
  agreement with `nonContributoryAgreement` when the oracle's agreement refuses the all-zero key, the
  same condition as at the first witness (`invReal_agreement_is_real` applies unchanged: the session's
  ratchet private key is the first witness's).  At the chunk message the model also computes the Braid
  step it would commit (`chunk_braid_step`, transition (2) into `headerSent` with a decoder holding the
  chunk), and the refusal discards it.
* **The added law** (`LawGenerateSucceeds`): `generate` returns `Ok` from some 64-byte stream.  It is a
  law about one opaque constant; it follows from the key-generation half of `KemDrawsSucceed` with
  `LawGenerateSeeded` (`lawGenerateSucceeds_of_kemDrawsSucceed`), and `Interp.modelShipped` satisfies
  it with the wrapper bundle (`held_laws_satisfiable`).  The joint statement also uses `LawKemConstants`
  for `HEADER_LEN` and `CT1_LEN`, `StdLaws.divCeil` and `TruncatePrefix` for the encoder, and
  `ValidKeyShape`, `OptionEqU64Shape` and `DhCodecTotal` for the structural clauses, all fields of
  `DecryptWrapperLaws`.

## The fourteen agreement fields

The `agreements` field of `DecryptHypotheses` is the record `DecryptRatchetAgreements wrapperKem`, as
at the corollary of `UnitKemWrapperModel`: `kem`, `kemLen` and `validateEk` are derived from the eight
wrapper laws, `erasure` from `divCeil` and `TruncatePrefix`, and the other ten (`hmac`, `hkdf`, the five
round trips, `pop`, `asMut`, `kemClone`) are fields of the bundle, restated.  What this witness adds is
that the KEM clauses are now asked at a held value: `related` contains `FreshKeyPairRefines` at the held
key (its decapsulation clause, the vector and the header-hash clause), and `invariant` contains
`key_pair_valid kp`, and the proof establishes these from the definitions and the laws.  The record
itself is exactly the corollary's.  No field reads an encapsulation state: the witness is the
initiator's, so `EncapsRefines` is not asked.

## What it is not

* The state is built for the hypotheses; the shipped code does not produce this combination of Triple
  and Braid states; the invariant admits it.  `Session::encrypt` commits the Triple and the Braid
  together (`tacenta-core/session-unit/src/lifecycle.rs`, `self.triple = candidate; self.braid =
  braid_next`), so no session holds a Braid in `KeysSampled` beside a Triple that has sent nothing, as
  this one does.  `Session::invariant` reads neither the Braid's authenticator (here the zero keys, where
  `Auth::init` derives them by HKDF) nor the header its encoder carries, and `SessionRefines` does not
  relate that header to the key pair; only `HeldKemAt` does.  The encoder's message is the header
  followed by the model's MAC under the zero authenticator, where `send` computes it with the opaque
  HMAC.  That the real `Braid::send` from `KeysUnsampled` under the zero authenticator lands on this
  Braid state was not attempted.
* The chunk enters a fresh decoder: at `keysSampled` a `ct1` chunk starts the decoder of transition
  (2), and `HonestChunk` asks nothing there.  A run into a decoder that already holds a chunk is not
  shown: that state (`HeaderSent` and the others holding a decoder) has `Session::invariant` calling
  `Decoder::invariant`, a loop over the held chunks, and no result here evaluates it on such a decoder.
* The chunk statement chooses the chunk and the codeword view; the first statement holds for every
  view.
* The oracle's other KEM fields (`kemValid`, `kemEncaps`, `kemDecaps`) are `oracleOfLaws`'s and are not
  related to `wrapperKem`; the model's `decrypt` reads none of them.
* The laws are assumed, not proved of the shipped functions; nothing here is about ML-KEM, and a key
  pair restored by `from_bytes` has no model value at `wrapperKem`.
* Which way the model's step goes is fixed by one value of the real `agree` that no law states, as at
  the first witness; no Triple receive, AEAD open or success is reached.

## Platform width

No proof here chooses a width of `usize`: the bounds used are `usize_max_ge`, which holds at both.  No
result depends on a compiler-trust axiom (the pins).
-/

open Aeneas Aeneas.Std Result
open tacenta_session_unit
open Tacenta.UnitLifecycleT3 hiding vecOf
open Tacenta.UnitLifecycleDecryptRatchetT3
open Tacenta.UnitSatisfiabilityJoint
open Tacenta.UnitSatisfiabilityBraidAgreements
open Tacenta.SessionUnitBraidT3 (vecOf keyOf u8 EncoderRefines CodewordOf FreshKeyPairRefines
  KeyPairRefines ErasureAgrees AuthOf)
open Tacenta.UnitLifecycleIntegrationScreen (byteRng byteCrc byteTrace)
open Tacenta.UnitKemWrapperModel
open Tacenta.UnitLifecycleDecryptScreen
open Tacenta.UnitLifecycleDecryptRatchetScreen (sampleMessage sampleRng sampleComposite
  sample_decode_model sample_decode_real sliceOf_sampleMessage sample_trace modelOf
  decrypt_shapes_are_predicates)
open Tacenta.UnitSatisfiabilityBraidStates (auth0 modelAuth0 sliceOfBytes sliceOf_sliceOfBytes)
open Tacenta.UnitHeadroomInvariant (ValidKeyShape OptionEqU64Shape)

namespace Tacenta.UnitHeldKemWitness

/-! ## The law the held key pair needs -/

/-- Key generation returns a key pair from some 64 bytes: there is a 64-byte stream from which
`IncrementalKeyPair::generate` returns `Ok`.  A statement about one opaque constant of the unit (and
the Lean byte-stream source `byteRng`); none of the eight wrapper laws gives it, since each speaks of a
key pair only where `generate` has returned one. -/
def LawGenerateSucceeds : Prop :=
  ∃ (seed : List Std.U8) (kp : tacenta_kem.IncrementalKeyPair) (rest : List Std.U8),
    seed.length = 64 ∧
    tacenta_kem.IncrementalKeyPair.generate byteRng byteCrc seed = ok (.Ok kp, rest)

/-- `LawGenerateSucceeds` over an interpretation. -/
def LawGenerateSucceedsShape (I : Interp) : Prop :=
  ∃ (seed : List Std.U8) (kp : I.IncrementalKeyPair) (rest : List Std.U8),
    seed.length = 64 ∧ I.ikpGenerate byteRng byteCrc seed = ok (.Ok kp, rest)

theorem LawGenerateSucceeds_is : LawGenerateSucceeds ↔ LawGenerateSucceedsShape Interp.real := Iff.rfl

/-- `LawGenerateSucceeds` follows from the key-generation half of `KemDrawsSucceed` (a hypothesis the
Braid witnesses already take) with the wrapper law `LawGenerateSeeded`: a key pair generated from a
source that answers is generated from the byte stream of some 64 bytes. -/
theorem lawGenerateSucceeds_of_kemDrawsSucceed (W : WrapperKemLaws) (hd : KemDrawsSucceed) :
    LawGenerateSucceeds := by
  obtain ⟨⟨R, rc, crc, rng, hrt, kp, rng', hgen⟩, -⟩ := hd
  obtain ⟨seed, res, rng'', rest, hlen, hreal, hbyte⟩ := W.generateSeeded rc crc rng hrt
  have h := hgen.symm.trans hreal
  cases h
  exact ⟨seed, kp, rest, hlen, hbyte⟩

/-- In `Interp.modelShipped` key generation always returns, so the law holds there. -/
theorem modelShipped_generateSucceeds : LawGenerateSucceedsShape Interp.modelShipped :=
  ⟨List.replicate 64 0#u8, _, _, by simp, rfl⟩

/-- **The laws the held witness takes have a model**: `Interp.modelShipped`, its view and
`optionEqImpl` satisfy the wrapper bundle and `LawGenerateSucceeds` together, with the crate's four KEM
length constants. -/
theorem held_laws_satisfiable :
    ∃ (I : Interp) (dh : Tacenta.UnitLifecycleDecryptRatchetScreen.DhViewShape I)
      (oeq : {T : Type} → core.cmp.PartialEq T T → Option T → Option T → Result Bool),
      I.HEADER_LEN = ok 64#usize ∧ I.EK_VECTOR_LEN = ok 1536#usize ∧ I.CT1_LEN = ok 1408#usize ∧
      I.CT2_LEN = ok 160#usize ∧ DecryptWrapperLawsShape I dh oeq ∧ LawGenerateSucceedsShape I :=
  ⟨Interp.modelShipped, viewShipped, @Tacenta.UnitHeadroomInvariant.optionEqImpl, rfl, rfl, rfl, rfl,
    decrypt_wrapper_laws_model, modelShipped_generateSucceeds⟩

/-! ## The header message and the held states -/

/-- The header message transition (1) encodes at epoch 1 under the zero authenticator: the header
followed by its MAC (`Model.Braid.Auth.macHdr`). -/
def hdrMsgOf (header : Bytes) : Bytes := header ++ modelAuth0.macHdr 1 header

/-- A 64-byte header and its 32-byte MAC are 96 bytes, `HEADER_LEN + MAC_LEN`. -/
theorem hdrMsgOf_length (header : Bytes) (h : header.length = 64) : (hdrMsgOf header).length = 96 := by
  simp [hdrMsgOf, Model.Braid.Auth.macHdr, Model.Kdf.hmac_length, Model.Kdf.hashLen, h]

theorem hdrMsgOf_le (header : Bytes) (h : header.length = 64) : (hdrMsgOf header).length ≤ Usize.max := by
  rw [hdrMsgOf_length header h]; exact usize_max_ge 96 (by norm_num)

/-- The model Braid of the witness: `keysSampled` at epoch 1 under the zero authenticator, holding a
private part, a vector, and the encoder of the header message that has emitted one chunk. -/
def heldModelBraid (dk ekVector header : Bytes) : Model.Braid.BraidState :=
  .keysSampled 1 modelAuth0 dk ekVector ⟨hdrMsgOf header, 1⟩

/-- The translated Braid of the witness: `KeysSampled` at epoch 1 under the zero authenticator,
holding a key pair and a header encoder. -/
def heldBraid (kp : tacenta_kem.IncrementalKeyPair) (enc : tacenta_erasure.Encoder) :
    tacenta_braid.Braid :=
  ⟨.KeysSampled 1#u64 auth0 kp enc⟩

/-! ## The encoder -/

/-- The model's erasure code cuts a message into `⌈length / 32⌉` chunks. -/
theorem chunks_length (m : Bytes) : (Model.Erasure.chunks m).length = (m.length + 31) / 32 := by
  simp [Model.Erasure.chunks, Model.Erasure.chunkCount, Model.Erasure.chunkBytes]

/-- **The header encoder.**  For a 96-byte message, the real `Encoder::new` returns an encoder whose
first `next_chunk` returns the codeword of index 0 and an encoder that refines the model encoder of the
message advanced once, passes `Encoder::invariant`, and is sized for 96 bytes (`encoder_sized`). -/
theorem held_encoder (hdiv : Tacenta.SessionUnitDecoderBound.DivCeilValue) (hea : ErasureAgrees)
    (m : Bytes) (hm : m.length = 96) :
    ∃ (enc0 enc1 : tacenta_erasure.Encoder) (c : tacenta_erasure.Chunk),
      tacenta_erasure.Encoder.new (sliceOfBytes m (by rw [hm]; exact usize_max_ge 96 (by norm_num))) = ok enc0 ∧
      tacenta_erasure.Encoder.next_chunk enc0 = ok (some c, enc1) ∧
      c.index.val = 0 ∧ CodewordOf m c ∧ EncoderRefines enc1 ⟨m, 1⟩ ∧
      tacenta_erasure.Encoder.invariant enc1 = ok true ∧
      ∀ len : Usize, len.val = 96 → tacenta_braid.encoder_sized enc1 len = ok true := by
  have hle : m.length ≤ Usize.max := by rw [hm]; exact usize_max_ge 96 (by norm_num)
  set s := sliceOfBytes m hle with hs
  have hsl : Tacenta.SessionUnitBraidT3.sliceOf s = m := sliceOf_sliceOfBytes m hle
  obtain ⟨enc0, hnew, href⟩ := hea.1 s
  rw [hsl] at href
  obtain ⟨r0, hr0, hpost0⟩ := Std.WP.spec_imp_exists (Tacenta.UnitErasureRs.Encoder.E_new hdiv s)
  rw [hnew] at hr0; cases hr0
  obtain ⟨-, -, hstore⟩ := hpost0
  obtain ⟨hex0, hnext0⟩ := Tacenta.UnitSatisfiabilityErasureAgrees.new_shape s enc0 hnew
  obtain ⟨r1, hr1, ⟨data, hdata⟩, hchunks, -, hne⟩ :=
    Std.WP.spec_imp_exists (Tacenta.UnitSatisfiabilityErasureAgrees.next_chunk_shape' enc0 hex0)
  obtain ⟨o, enc1⟩ := r1
  simp only at hdata hchunks hne
  subst hdata
  have hnmax : enc0.next ≠ core.num.U16.MAX := by
    rw [hnext0]; decide
  obtain ⟨hex1, -⟩ := hne hnmax
  have hlive : (Model.Braid.encode m).next < 65536 := by simp [Model.Braid.encode]
  obtain ⟨hidx, hcw, href1⟩ := Tacenta.SessionUnitBraidT3.EncoderRefines.step href hlive hr1
  have hlen0 : enc0.chunks.val.length = 3 := by
    have := congrArg List.length hstore
    simp only [Tacenta.UnitErasureRs.storeBytes, List.length_map, List.length_take, chunks_length,
      hsl, hm] at this
    omega
  have hlen1 : enc1.chunks.val.length = 3 := by rw [hchunks]; exact hlen0
  refine ⟨enc0, enc1, _, hnew, hr1, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Model.Braid.encode, Model.Braid.Encoder.nextChunk, hnext0] at hidx ⊢
  · simpa [Model.Braid.encode] using hcw
  · simpa [Model.Braid.encode, Model.Braid.Encoder.nextChunk] using href1
  · unfold tacenta_erasure.Encoder.invariant
    have : alloc.vec.Vec.len enc1.chunks ≤ tacenta_erasure.MAX_CODEWORDS := by
      have h1 := alloc.vec.Vec.len_val enc1.chunks
      simp only [tacenta_erasure.MAX_CODEWORDS]
      scalar_tac
    simp [this, hex1]
  · intro len hlen
    obtain ⟨r, hr, hrv⟩ := hdiv len
    unfold tacenta_braid.encoder_sized tacenta_erasure.Encoder.needed
    simp only [Tacenta.UnitSatisfiabilityErasure.chunk_count_eq, hr, bind_tc_ok]
    have h1 := alloc.vec.Vec.len_val enc1.chunks
    have : alloc.vec.Vec.len enc1.chunks = r := by
      apply UScalar.eq_of_val_eq; rw [h1, hrv, hlen]; simpa [alloc.vec.Vec.length] using hlen1
    simp [this]

/-! ## The key pair, and the agreements at it -/

/-- **The KEM agreements at the held key, from `wrapperKem`'s definition and the laws.**  For a key
pair `generate` returned from 64 bytes: `wrapperKem.keyGen` at the randomness those bytes are returns
them as the private part, with the header's first 32 bytes and the vector's bytes; the model hash of
that seed and vector is the header's last 32 bytes; the header has 64 bytes and the vector
`wrapperKem.ekSize`; `key_pair_valid` returns `true`; and the pair refines the private part and the
vector at `wrapperKem` (`FreshKeyPairRefines`, decapsulation clause included). -/
theorem held_key_agreements (W : WrapperKemLaws) {seed : List Std.U8} {kp : tacenta_kem.IncrementalKeyPair}
    {rest : List Std.U8} (hlen : seed.length = 64)
    (hgen : tacenta_kem.IncrementalKeyPair.generate byteRng byteCrc seed = ok (.Ok kp, rest)) :
    ∃ (h v : alloc.vec.Vec Std.U8),
      tacenta_kem.IncrementalKeyPair.header kp = ok h ∧
      tacenta_kem.IncrementalKeyPair.ek_vector kp = ok v ∧
      (vecOf h).length = 64 ∧ (vecOf v).length = wrapperKem.ekSize ∧
      wrapperKem.keyGen (leNat (seed.map u8)) = some (seed.map u8, (vecOf h).take 32, vecOf v) ∧
      wrapperKem.hashEk ((vecOf h).take 32) (vecOf v) = (vecOf h).drop 32 ∧
      tacenta_braid.key_pair_valid kp = ok true ∧
      FreshKeyPairRefines wrapperKem kp (seed.map u8) (vecOf v) := by
  obtain ⟨h, v, hh, hhl, hv, hvl, hval, -⟩ := W.generatedKeyPair seed kp rest hlen hgen
  have hs : streamOf 64 (leNat (seed.map u8)) = seed := by
    have := streamOf_leNat seed
    rwa [hlen] at this
  have hdk : leBytes 64 (leNat (seed.map u8)) = seed.map u8 := by
    have := leBytes_leNat (seed.map u8)
    rwa [List.length_map, hlen] at this
  have hvl' : (vecSlice v).length = 1536 := hvl
  have hhl' : (vecOf h).length = 64 := by simpa [vecOf] using hhl
  have htk : ((vecOf h).take 32).length = 32 := by simp [hhl']
  have hdr : ((vecOf h).drop 32).length = 32 := by simp [hhl']
  have hval' : Interp.real.validateEk (bytesSlice ((vecOf h).take 32 ++ (vecOf h).drop 32))
      (vecSlice v) = ok true := by
    rw [List.take_append_drop, ← sliceOf_vecSlice, bytesSlice_sliceOf]; exact hval
  have heq := hashEkOf_eq W htk hdr hvl' hval'
  rw [sliceOf_vecSlice] at heq
  refine ⟨h, v, hh, hv, hhl', by simpa [vecOf, wrapperKem, wrapperKemOf] using hvl, ?_, heq, ?_, ?_⟩
  · show (wrapperKemOf Interp.real).keyGen _ = _
    simp only [wrapperKemOf, hs]
    rw [show Interp.real.ikpGenerate byteRng byteCrc seed = ok (.Ok kp, rest) from hgen]
    simp only
    rw [show Interp.real.ikpHeader kp = ok h from hh, show Interp.real.ikpEkVector kp = ok v from hv,
      hdk]
  · unfold tacenta_braid.key_pair_valid
    rw [show tacenta_kem.IncrementalKeyPair.header kp = ok h from hh,
      show tacenta_kem.IncrementalKeyPair.ek_vector kp = ok v from hv]
    exact (show tacenta_kem.validate_ek (vecSlice h) (vecSlice v) = ok true from hval)
  · refine ⟨decaps_clause W hlen hgen _ (bytesOf_map_u8 seed), ⟨v, hv, rfl⟩,
      ⟨h, (vecOf h).take 32, hh, ?_⟩⟩
    show vecOf h = (vecOf h).take 32 ++ hashEkOf Interp.real ((vecOf h).take 32) (vecOf v)
    rw [show hashEkOf Interp.real ((vecOf h).take 32) (vecOf v) = (vecOf h).drop 32 from heq,
      List.take_append_drop]

/-! ## The session -/

def heldReal (k : tacenta_boundary.dh.PrivateKey) (pkb : tacenta_boundary.dh.PublicKeyBytes)
    (ad : alloc.vec.Vec U8) (a : Array U8 32#usize) (kp : tacenta_kem.IncrementalKeyPair)
    (enc : tacenta_erasure.Encoder) : lifecycle.Session :=
  { invReal k pkb ad a with braid := heldBraid kp enc }

/-- The model session of the witness: the session read off `real`, with the held model Braid. -/
def heldModel (dh : DhView) (real : lifecycle.Session) (dk ekVector header : Bytes) :
    Model.Lifecycle.Session :=
  { modelOf dh real with braid := heldModelBraid dk ekVector header }

open Tacenta.UnitHeadroomInvariant in
/-- `Session::structural_invariant` of the held session: clauses (a) to (h) as for the first witness;
at `KeysSampled` epoch 1 the Braid reports epoch 1, tag 1 and the initiator's role, which the fresh
Triple state (sparse epoch 0, direction `A2b`) and the session with no established ephemeral key
match. -/
theorem structural_held
    (k : tacenta_boundary.dh.PrivateKey) (pkb : tacenta_boundary.dh.PublicKeyBytes)
    (a : Array U8 32#usize)
    (hpub : tacenta_boundary.dh.PrivateKey.public_key k = ok pkb)
    (hbytes : tacenta_boundary.dh.PublicKeyBytes.as_bytes pkb = ok a)
    (hcan : Tacenta.SessionUnitT1.canonicalX25519 a = true)
    (hprime : tacenta_boundary.dh.is_prime_order_public pkb = ok true)
    (hoeq : OptionEqU64Shape (@core.option.Option.Insts.CoreCmpPartialEqOption.eq))
    (ad : alloc.vec.Vec U8) (had : lifecycle.identity_ad pkb pkb = ok ad)
    (kp : tacenta_kem.IncrementalKeyPair) (enc : tacenta_erasure.Encoder) :
    lifecycle.Session.structural_invariant (heldReal k pkb ad a kp enc) = ok true := by
  have hv := is_valid_identity_key_eq pkb a hbytes hcan hprime
  unfold lifecycle.Session.structural_invariant
  simp [heldReal, invReal, Tacenta.UnitHeadroomSatisfiable.sessionOf, hpub, hbytes,
    tacenta_triple.State.sending_public, Tacenta.UnitHeadroomSatisfiable.freshTriple,
    tacenta_ratchet.State.sending_public, array_ne_self, heldBraid, tacenta_braid.Braid.failed,
    tacenta_braid.Braid.is_initiator, tacenta_braid.State.epoch, lifecycle.Session.is_responder,
    had, vec_ne_self, tacenta_triple.State.direction, tacenta_spqr.State.impl.direction, hv,
    tacenta_braid.Braid.epoch, tacenta_triple.State.epoch, tacenta_spqr.State.impl.epoch,
    tacenta_braid.Braid.state_tag, lift, tacenta_spqr.Direction.Insts.CoreCmpPartialEqDirection.eq]
  have h01 : U64.checked_add 0#u64 1#u64 = some 1#u64 := by decide
  rw [h01, hoeq]
  rfl

/-- `Braid::invariant` of the held Braid: the epoch is at least 1, the encoder passes
`Encoder::invariant` and is sized for `HEADER_LEN + MAC_LEN` bytes, and `key_pair_valid` returns
`true`. -/
theorem heldBraid_invariant (hk : tacenta_kem.HEADER_LEN = ok 64#usize)
    (kp : tacenta_kem.IncrementalKeyPair) (enc : tacenta_erasure.Encoder)
    (henc : tacenta_erasure.Encoder.invariant enc = ok true)
    (hsized : ∀ len : Usize, len.val = 96 → tacenta_braid.encoder_sized enc len = ok true)
    (hkp : tacenta_braid.key_pair_valid kp = ok true) :
    tacenta_braid.Braid.invariant (heldBraid kp enc) = ok true := by
  unfold tacenta_braid.Braid.invariant
  simp only [heldBraid, henc, hk, bind_tc_ok, if_true]
  have h1 : (1#u64 : U64) >= 1#u64 := by decide
  simp only [h1, if_true]
  obtain ⟨x, hx, hxv⟩ : ∃ x : Usize, 64#usize + tacenta_braid.MAC_LEN = ok x ∧ x.val = 96 := by
    have : tacenta_braid.MAC_LEN.val = 32 := by simp [tacenta_braid.MAC_LEN]
    have h := usize_max_ge 96 (by norm_num)
    obtain ⟨x, hx, hxv⟩ := Std.WP.spec_imp_exists (Usize.add_spec (x := 64#usize)
      (y := tacenta_braid.MAC_LEN) (by scalar_tac))
    exact ⟨x, hx, by scalar_tac⟩
  rw [hx]
  simp only [bind_tc_ok, hsized x hxv, if_true, hkp]

open Tacenta.UnitHeadroomInvariant in
/-- **`Session::invariant` returns `true` on the held session**, given the first witness's key
assumptions and the held Braid's invariant. -/
theorem held_invariant
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
    lifecycle.Session.invariant (heldReal k pkb ad a kp enc) = ok true := by
  unfold lifecycle.Session.invariant
  rw [structural_held k pkb a hpub hbytes hcan hprime hoeq ad had kp enc]
  simp only [Aeneas.Std.bind_tc_ok, if_true]
  unfold lifecycle.Session.leaf_invariants
  simp only [heldReal, invReal, Tacenta.UnitHeadroomSatisfiable.sessionOf]
  rw [freshTriple_invariant a hcan]
  simp [hbraid]

/-! ## The relation, the run and the hypotheses at the held state -/

theorem held_sessionRefines (K : Model.Braid.Kem) (dh : DhView) (k pkb ad a)
    (kp : tacenta_kem.IncrementalKeyPair) (enc : tacenta_erasure.Encoder) (dk ekVector header : Bytes)
    (hfresh : FreshKeyPairRefines K kp dk ekVector) (henc : EncoderRefines enc ⟨hdrMsgOf header, 1⟩) :
    SessionRefines dh K (heldReal k pkb ad a kp enc)
      (heldModel dh (heldReal k pkb ad a kp enc) dk ekVector header) :=
  ⟨⟨rfl, rfl⟩, ⟨rfl, rfl, hfresh, henc⟩, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- At the first witness's message (no agreement chunk) the model Braid stays and yields no key. -/
theorem held_braid_output (K : Model.Braid.Kem) (view : Model.Lifecycle.CodewordView)
    (dk ekVector header : Bytes) :
    (Model.Braid.receive K (heldModelBraid dk ekVector header)
      (Model.Lifecycle.braidMessageOf view (heldModelBraid dk ekVector header)
        sampleComposite)).2.1 = none := by
  simp [Model.Braid.receive, heldModelBraid, Model.Lifecycle.braidMessageOf, sampleComposite,
    Model.Lifecycle.braidTypeOf]

/-- The run record at the held state and the first witness's message, for every codeword view and
every oracle. -/
theorem held_run (dh : DhView) (k pkb ad a) (kp : tacenta_kem.IncrementalKeyPair)
    (enc : tacenta_erasure.Encoder) (dk ekVector header : Bytes)
    (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle) :
    DecryptRatchetRun view oracle byteTrace (heldReal k pkb ad a kp enc)
      (heldModel dh (heldReal k pkb ad a kp enc) dk ekVector header) sampleMessage sampleRng := by
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
  · simp only [heldReal, heldBraid, Tacenta.SessionUnitBraidT1.State.epoch_val]
    scalar_tac
  · intro modelComposite ciphertext hdecode
    rw [sample_decode_model] at hdecode
    have hmc : sampleComposite = modelComposite := (Prod.mk.inj (Except.ok.inj hdecode)).1
    subst hmc
    have hout := held_braid_output oracle.braidKem view dk ekVector header
    simp only [heldModel] at hout ⊢
    rw [hout]
    exact invReal_retryRunBounds k pkb ad a dh _ rfl

/-- Every hypothesis of the decrypt refinement at a state whose Braid holds a key pair, for any
message and run record at it. -/
theorem decrypt_hypotheses_at_held_of_run (dh : DhView) (L : DecryptWrapperLaws dh)
    (oracle : Model.Lifecycle.Oracle)
    (hK : oracle.braidKem = wrapperKem) (hdraws : oracle.draws = byteTrace sampleRng)
    (horacle : DecryptOracleOf byteRng byteCrc dh byteTrace oracle)
    (k : tacenta_boundary.dh.PrivateKey) (pkb : tacenta_boundary.dh.PublicKeyBytes)
    (a : Array U8 32#usize)
    (hpub : tacenta_boundary.dh.PrivateKey.public_key k = ok pkb)
    (hbytes : tacenta_boundary.dh.PublicKeyBytes.as_bytes pkb = ok a)
    (hcan : Tacenta.SessionUnitT1.canonicalX25519 a = true)
    (hprime : tacenta_boundary.dh.is_prime_order_public pkb = ok true)
    (ad : alloc.vec.Vec U8) (had : lifecycle.identity_ad pkb pkb = ok ad)
    (hlen : ad.val.length = 66)
    (kp : tacenta_kem.IncrementalKeyPair) (enc : tacenta_erasure.Encoder) (dk ekVector header : Bytes)
    (hfresh : FreshKeyPairRefines wrapperKem kp dk ekVector)
    (henc : EncoderRefines enc ⟨hdrMsgOf header, 1⟩)
    (hbraid : tacenta_braid.Braid.invariant (heldBraid kp enc) = ok true)
    (view : Model.Lifecycle.CodewordView) (message : Slice Std.U8)
    (hrun : DecryptRatchetRun view oracle byteTrace (heldReal k pkb ad a kp enc)
      (heldModel dh (heldReal k pkb ad a kp enc) dk ekVector header) message sampleRng) :
    DecryptHypotheses byteRng byteCrc byteTrace dh view oracle (heldReal k pkb ad a kp enc)
      (heldModel dh (heldReal k pkb ad a kp enc) dk ekVector header) message sampleRng := by
  have H := decrypt_hypotheses_at_invReal wrapperKem dh (decryptWrapperLaws_joint dh L) oracle hK hdraws
    horacle k pkb a hpub hbytes hcan hprime ad had hlen view
  have hinv := held_invariant k pkb a hpub hbytes hcan hprime L.optionEq ad had kp enc hbraid
  have hct1 : Tacenta.SessionUnitBraidT1.Ct1LenTotal := ⟨_, L.kem.constants.2.2.1, by decide⟩
  exact
    { oracleOf := H.oracleOf
      codec := H.codec
      contracts := H.contracts
      derivedKeys := H.derivedKeys
      agreements := H.agreements
      invariant := hinv
      related := hK ▸ held_sessionRefines wrapperKem dh k pkb ad a kp enc dk ekVector header hfresh henc
      headroom := Tacenta.UnitHeadroomInvariant.decryptHeadroom_of_invariant L.dhCodec hct1 _ hinv
      trace_eq := H.trace_eq
      run := hrun }

/-- **Every hypothesis of the decrypt refinement at a state whose Braid holds a key pair**, at the
message without an agreement chunk. -/
theorem decrypt_hypotheses_at_held (dh : DhView) (L : DecryptWrapperLaws dh)
    (oracle : Model.Lifecycle.Oracle)
    (hK : oracle.braidKem = wrapperKem) (hdraws : oracle.draws = byteTrace sampleRng)
    (horacle : DecryptOracleOf byteRng byteCrc dh byteTrace oracle)
    (k : tacenta_boundary.dh.PrivateKey) (pkb : tacenta_boundary.dh.PublicKeyBytes)
    (a : Array U8 32#usize)
    (hpub : tacenta_boundary.dh.PrivateKey.public_key k = ok pkb)
    (hbytes : tacenta_boundary.dh.PublicKeyBytes.as_bytes pkb = ok a)
    (hcan : Tacenta.SessionUnitT1.canonicalX25519 a = true)
    (hprime : tacenta_boundary.dh.is_prime_order_public pkb = ok true)
    (ad : alloc.vec.Vec U8) (had : lifecycle.identity_ad pkb pkb = ok ad)
    (hlen : ad.val.length = 66)
    (kp : tacenta_kem.IncrementalKeyPair) (enc : tacenta_erasure.Encoder) (dk ekVector header : Bytes)
    (hfresh : FreshKeyPairRefines wrapperKem kp dk ekVector)
    (henc : EncoderRefines enc ⟨hdrMsgOf header, 1⟩)
    (hbraid : tacenta_braid.Braid.invariant (heldBraid kp enc) = ok true)
    (view : Model.Lifecycle.CodewordView) :
    DecryptHypotheses byteRng byteCrc byteTrace dh view oracle (heldReal k pkb ad a kp enc)
      (heldModel dh (heldReal k pkb ad a kp enc) dk ekVector header) sampleMessage sampleRng :=
  decrypt_hypotheses_at_held_of_run dh L oracle hK hdraws horacle k pkb a hpub hbytes hcan hprime ad had
    hlen kp enc dk ekVector header hfresh henc hbraid view sampleMessage
    (held_run dh k pkb ad a kp enc dk ekVector header view oracle)

/-! ## The model state is the model's own key-generation step -/

/-- **The model Braid of the witness is transition (1) of the model.**  Where `K.keyGen rand` returns
`(dk, ekSeed, ekVector)` and `K.hashEk ekSeed ekVector = hek`, `Model.Braid.send K rand` from the fresh
initiator state at epoch 1 returns `heldModelBraid dk ekVector (ekSeed ++ hek)`. -/
theorem heldModelBraid_is_send (K : Model.Braid.Kem) (rand : ℕ) (dk ekSeed hek ekVector : Bytes)
    (hgen : K.keyGen rand = some (dk, ekSeed, ekVector)) (hhash : K.hashEk ekSeed ekVector = hek) :
    (Model.Braid.send K rand (.keysUnsampled 1 modelAuth0)).2.2.2 =
      heldModelBraid dk ekVector (ekSeed ++ hek) := by
  simp [Model.Braid.send, hgen, hhash, heldModelBraid, hdrMsgOf, Model.Braid.encode,
    Model.Braid.Encoder.nextChunk]

/-- The Braid of `real` holds a key pair `IncrementalKeyPair::generate` returned from 64 bytes, and the
Braid of `model` holds those 64 bytes as its private part and the bytes of the pair's `ek_vector` as
its vector, with an encoder of the pair's header and its MAC that has emitted one chunk: the state
`Model.Braid.send wrapperKem` reaches from the fresh initiator at the randomness those 64 bytes are. -/
def HeldKemAt (real : lifecycle.Session) (model : Model.Lifecycle.Session) : Prop :=
  ∃ (seed : List Std.U8) (kp : tacenta_kem.IncrementalKeyPair) (rest : List Std.U8)
    (enc : tacenta_erasure.Encoder) (h v : alloc.vec.Vec Std.U8),
    seed.length = 64 ∧
    tacenta_kem.IncrementalKeyPair.generate byteRng byteCrc seed = ok (.Ok kp, rest) ∧
    tacenta_kem.IncrementalKeyPair.header kp = ok h ∧
    tacenta_kem.IncrementalKeyPair.ek_vector kp = ok v ∧
    real.braid.state = .KeysSampled 1#u64 auth0 kp enc ∧
    model.braid = .keysSampled 1 modelAuth0 (seed.map u8) (vecOf v)
      ⟨vecOf h ++ modelAuth0.macHdr 1 (vecOf h), 1⟩ ∧
    model.braid = (Model.Braid.send wrapperKem (leNat (seed.map u8)) (.keysUnsampled 1 modelAuth0)).2.2.2

/-- **The hypotheses of the decrypt refinement hold together at a session whose Braid holds a key
pair, with the Braid KEM model read off the wrapper.**  Under `DecryptWrapperLaws dh` and
`LawGenerateSucceeds`, there are an oracle whose Braid KEM model is `wrapperKem` (the code's oracle,
`decryptOracleOf_of_laws`), a session that passes `Session::invariant` and a related model session whose
Braids hold a generated key pair and its bytes (`HeldKemAt`), a message that decodes on both sides and is
a ratchet frame, and a byte-stream source, at which every hypothesis of
`decrypt_ratchet_refines_complete` holds (`DecryptHypotheses`), for every codeword view.  The relation
at the held key (`held_key_agreements`) fixes the model's vector and the header hash to the real key
pair's; its key-generation and decapsulation parts hold by unfolding `wrapperKem`; it is false at
`toyKem` (`held_not_refines_toyKem`, a length mismatch).  The message carries no agreement chunk; the
model's step refuses at the first agreement if the real agreement refuses the all-zero key
(`held_model_refuses_of_agreement`). -/
theorem decrypt_hypotheses_jointly_satisfiable_at_wrapperKem_held (dh : DhView)
    (L : DecryptWrapperLaws dh) (G : LawGenerateSucceeds) :
    ∃ (oracle : Model.Lifecycle.Oracle) (real : lifecycle.Session)
      (model : Model.Lifecycle.Session) (message : Slice Std.U8) (rng : List Std.U8),
      oracle.braidKem = wrapperKem ∧
      HeldKemAt real model ∧
      (∃ decoded, tacenta_wire.decode_message message = ok (.Ok decoded)) ∧
      (∃ composite ciphertext,
        Model.CompositeHeader.decodeDetailed (sliceOf message) = .ok (composite, ciphertext)) ∧
      Model.Lifecycle.messageType (sliceOf message) = some .ratchet ∧
      ∀ view : Model.Lifecycle.CodewordView,
        DecryptHypotheses byteRng byteCrc byteTrace dh view oracle real model message rng := by
  obtain ⟨oracle, hdraws, hK, horacle⟩ :=
    Tacenta.UnitOracleDecrypt.decryptOracleOf_of_laws dh L.dhCodec L.dhAgree L.aeadOpen
      L.viewInjective (byteTrace sampleRng) wrapperKem
  obtain ⟨k, pkb, a, hpub, hbytes, hcan, hprime⟩ := L.validKey
  obtain ⟨ad, had, hlen⟩ :=
    Std.WP.spec_imp_exists (Tacenta.UnitLifecycleT1.identity_ad_length L.dhCodec pkb pkb)
  obtain ⟨decoded, hdec, -⟩ := sample_decode_real
  obtain ⟨seed, kp, rest, hslen, hgen⟩ := G
  obtain ⟨h, v, hh, hv, hhl, -, hkg, hhash, hkpv, hfresh⟩ := held_key_agreements L.kem hslen hgen
  have hdiv : Tacenta.SessionUnitDecoderBound.DivCeilValue := L.laws.divCeil
  have hea : ErasureAgrees := Tacenta.UnitErasureRs.Glue.erasureAgrees hdiv L.truncatePrefix
  obtain ⟨-, enc, -, -, -, -, -, henc, hencinv, hsized⟩ :=
    held_encoder hdiv hea (hdrMsgOf (vecOf h)) (hdrMsgOf_length _ hhl)
  have hbraid := heldBraid_invariant L.kem.constants.1 kp enc hencinv hsized hkpv
  have hsend := heldModelBraid_is_send wrapperKem _ _ _ _ _ hkg hhash
  rw [List.take_append_drop] at hsend
  refine ⟨oracle, heldReal k pkb ad a kp enc,
    heldModel dh (heldReal k pkb ad a kp enc) (seed.map u8) (vecOf v) (vecOf h), sampleMessage,
    sampleRng, hK, ⟨seed, kp, rest, enc, h, v, hslen, hgen, hh, hv, rfl, rfl, hsend.symm⟩,
    ⟨decoded, hdec⟩, ⟨_, _, sample_decode_model⟩, sampleMessage_type, fun view => ?_⟩
  exact decrypt_hypotheses_at_held dh L oracle hK hdraws horacle k pkb a hpub hbytes hcan hprime ad
    had hlen kp enc _ _ _ hfresh henc hbraid view

/-! ## A run carrying an agreement chunk -/

/-- A `ct1` source of the crate's length: 1408 zero bytes. -/
def ct1Zeros : Bytes := List.replicate 1408 0

/-- `ct1Zeros` has the crate's `CT1_LEN` bytes. -/
theorem ct1Zeros_length : ct1Zeros.length = 1408 := List.length_replicate

theorem ct1Zeros_le : ct1Zeros.length ≤ Usize.max := by
  rw [ct1Zeros_length]; exact usize_max_ge 1408 (by norm_num)

/-- The first codeword of a message of at least 32 bytes is its first 32 bytes (the code is
systematic). -/
theorem codeword_zero (m : Bytes) (h : 32 ≤ m.length) :
    Model.Erasure.codeword (List.take 65536 (Model.Erasure.chunks m)) 0 = m.take 32 := by
  have hl : 0 < (Model.Erasure.chunks m).length := by
    rw [chunks_length]; omega
  have hlt : 0 < (List.take 65536 (Model.Erasure.chunks m)).length := by
    rw [List.length_take]; omega
  rw [Model.Erasure.codeword_systematic _ _ hlt, List.getD_eq_getElem _ _ hlt, List.getElem_take]
  simp only [Model.Erasure.chunks, List.getElem_map, List.getElem_range, Nat.zero_mul, List.drop_zero,
    Model.Erasure.chunkBytes]
  have : (m.take 32).length = 32 := by simp; omega
  simp [this]

/-- The first chunk of `ct1Zeros`, as the model's erasure code cuts it, is 32 zero bytes. -/
theorem ct1Zeros_codeword0 :
    Model.Erasure.codeword (List.take 65536 (Model.Erasure.chunks ct1Zeros)) 0 =
      List.replicate 32 0 := by
  rw [codeword_zero _ (by rw [ct1Zeros_length]; norm_num), ct1Zeros, List.take_replicate]
  rfl

/-- The byte view of a list of `u8` values is injective. -/
theorem u8_map_inj {a b : List Std.U8} (h : a.map u8 = b.map u8) : a = b := by
  have := congrArg (List.map toU8) h
  simpa [List.map_map, Function.comp_def, toU8_u8] using this

/-- **A real chunk of index 0 carrying 32 zero bytes is a codeword of `ct1Zeros`**: the real
`Encoder::new` of those 1408 bytes emits it first (the code is systematic). -/
theorem zero_chunk_codeword (hdiv : Tacenta.SessionUnitDecoderBound.DivCeilValue)
    (c : tacenta_erasure.Chunk) (hidx : c.index.val = 0)
    (hdata : c.data.val.map u8 = List.replicate 32 0) : CodewordOf ct1Zeros c := by
  set s := sliceOfBytes ct1Zeros ct1Zeros_le with hs
  have hsl : Tacenta.SessionUnitBraidT3.sliceOf s = ct1Zeros := sliceOf_sliceOfBytes _ ct1Zeros_le
  obtain ⟨enc0, hnew, -, -, hstore⟩ :=
    Std.WP.spec_imp_exists (Tacenta.UnitErasureRs.Encoder.E_new hdiv s)
  obtain ⟨hex0, hnext0⟩ := Tacenta.UnitSatisfiabilityErasureAgrees.new_shape s enc0 hnew
  have hlen0 : enc0.chunks.val.length = 44 := by
    have := congrArg List.length hstore
    simp only [Tacenta.UnitErasureRs.storeBytes, List.length_map, List.length_take, chunks_length,
      hsl, ct1Zeros_length] at this
    omega
  obtain ⟨r1, hr1, hcb⟩ := Std.WP.spec_imp_exists
    (Tacenta.UnitErasureRs.Encoder.E_next enc0 hex0 (by rw [hlen0]; norm_num))
  obtain ⟨r1', hr1', ⟨d, hd⟩, -⟩ :=
    Std.WP.spec_imp_exists (Tacenta.UnitSatisfiabilityErasureAgrees.next_chunk_shape' enc0 hex0)
  rw [hr1] at hr1'; cases hr1'
  obtain ⟨o, enc1⟩ := r1
  simp only at hd hcb
  subst hd
  have hcw := hcb _ rfl
  rw [hstore, hnext0, hsl, show ((0#u16 : U16).val) = 0 from rfl, ct1Zeros_codeword0] at hcw
  have hdd : d = c.data := by
    apply Subtype.ext
    exact u8_map_inj (hcw.trans hdata.symm)
  have hci : c.index = 0#u16 := UScalar.eq_of_val_eq (by rw [hidx]; rfl)
  have hc : c = { index := enc0.next, data := d } := by
    cases c; simp only at hci hdd; subst hci; subst hdd; rw [hnext0]
  refine ⟨s, enc0, hsl, hnew, ?_⟩
  rw [hidx, hc]
  exact ⟨enc1, hr1⟩

/-- The composite of the run carrying a chunk: `sampleComposite`'s fields, with a `ct1` message of
the Braid's epoch 1 carrying the codeword of index 0 and 32 zero bytes. -/
def chunkComposite : Model.CompositeHeader.Composite :=
  { dh := List.replicate 32 0, pn := 0, n := 1, pqEpoch := 0, pqN := 1, agEpoch := 1,
    agType := .ct1, agChunk := some ⟨0, List.replicate 32 0⟩ }

def chunkBytes : Bytes := Model.CompositeHeader.encode chunkComposite

theorem chunkBytes_le : chunkBytes.length ≤ Usize.max := by
  have : chunkBytes.length ≤ 4096 := by decide
  exact le_trans this (usize_max_ge 4096 (by norm_num))

/-- The message: the encoded composite with an empty ciphertext. -/
def chunkMessage : Slice U8 := sliceOfBytes chunkBytes chunkBytes_le

theorem sliceOf_chunkMessage : sliceOf chunkMessage = chunkBytes :=
  sliceOf_sliceOfBytes chunkBytes chunkBytes_le

/-- The model decoder reads the chunk message as `chunkComposite` with an empty ciphertext. -/
theorem chunk_decode_model :
    Model.CompositeHeader.decodeDetailed (sliceOf chunkMessage) = .ok (chunkComposite, []) := by
  rw [sliceOf_chunkMessage, Model.CompositeHeader.decodeDetailed_ok_iff]
  decide

/-- The translated decoder accepts the chunk message, and its header refines `chunkComposite`. -/
theorem chunk_decode_real :
    ∃ decoded, tacenta_wire.decode_message chunkMessage = ok (.Ok decoded) ∧
      CompositeRefines decoded.header chunkComposite := by
  obtain ⟨r, hr, hpost⟩ := Std.WP.spec_imp_exists (decode_message_refines_lifecycle chunkMessage)
  have hmodel : Model.CompositeHeader.decode (sliceOf chunkMessage) = some (chunkComposite, []) :=
    (Model.CompositeHeader.decodeDetailed_ok_iff _ _).mp chunk_decode_model
  cases r with
  | Err e =>
      rw [hmodel] at hpost
      exact absurd hpost (by simp)
  | Ok decoded =>
      obtain ⟨mh, hdec, hrel⟩ := hpost
      rw [hmodel] at hdec
      have hmh : chunkComposite = mh := (Prod.mk.inj (Option.some.inj hdec)).1
      subst hmh
      exact ⟨decoded, hr, hrel⟩

/-- The chunk message is a ratchet frame. -/
theorem chunkMessage_type :
    Model.Lifecycle.messageType (sliceOf chunkMessage) = some .ratchet := by
  rw [sliceOf_chunkMessage]
  decide

/-- The codeword view of the run: every incoming chunk is read as the codeword of index 0 of
`ct1Zeros`. -/
def chunkView : Model.Lifecycle.CodewordView where
  receive := fun _ _ _ => ⟨ct1Zeros, 0⟩
  send := fun _ _ => default

/-- At the chunk message the model Braid takes transition (2): a `ct1` chunk of its epoch starts the
decoder of `K.ct1Size` bytes, holding the chunk, and no key is yielded. -/
theorem chunk_braid_step (K : Model.Braid.Kem) (dk ekVector header : Bytes) :
    Model.Braid.receive K (heldModelBraid dk ekVector header)
      (Model.Lifecycle.braidMessageOf chunkView (heldModelBraid dk ekVector header) chunkComposite) =
    (0, none, .headerSent 1 modelAuth0 dk ((Model.Braid.Decoder.new K.ct1Size).addChunk ⟨ct1Zeros, 0⟩)
      (Model.Braid.encode ekVector)) := by
  simp [Model.Braid.receive, heldModelBraid, Model.Lifecycle.braidMessageOf, chunkComposite,
    Model.Lifecycle.braidTypeOf, chunkView, Model.Braid.BraidState.epoch]

/-- The run record at the held state and the chunk message, with the chosen view `chunkView`: the
incoming chunk is a codeword of `ct1Zeros` (`zero_chunk_codeword`), so `IncomingChunkRefines` holds with
a chunk present; `HonestChunk` holds because a `ct1` chunk at `keysSampled` starts a fresh decoder. -/
theorem held_chunk_run (dh : DhView) (hdiv : Tacenta.SessionUnitDecoderBound.DivCeilValue) (k pkb ad a)
    (kp : tacenta_kem.IncrementalKeyPair) (enc : tacenta_erasure.Encoder) (dk ekVector header : Bytes)
    (oracle : Model.Lifecycle.Oracle) :
    DecryptRatchetRun chunkView oracle byteTrace (heldReal k pkb ad a kp enc)
      (heldModel dh (heldReal k pkb ad a kp enc) dk ekVector header) chunkMessage sampleRng := by
  refine
    { chunk := ?_
      honest := ?_
      braidEpoch := ?_
      draw := ⟨_, [], sample_trace⟩
      retry := ?_ }
  · intro realComposite modelComposite ciphertext hdecode hcomposite
    rw [chunk_decode_model] at hdecode
    have hmc : chunkComposite = modelComposite := (Prod.mk.inj (Except.ok.inj hdecode)).1
    subst hmc
    have hchunk := hcomposite.agChunk
    unfold IncomingChunkRefines
    cases hr : realComposite.ag_chunk with
    | none => simp [hr, chunkComposite] at hchunk
    | some c =>
      simp only [hr, chunkComposite] at hchunk ⊢
      obtain ⟨hidx, hdata⟩ := hchunk
      refine ⟨ct1Zeros, zero_chunk_codeword hdiv _ (by simpa using hidx) (by simpa [arrayOf] using hdata), ?_⟩
      simp only [chunkView, modelChunkOf]
      congr 1
      simpa using hidx.symm
  · intro modelComposite ciphertext hdecode
    rw [chunk_decode_model] at hdecode
    have hmc : chunkComposite = modelComposite := (Prod.mk.inj (Except.ok.inj hdecode)).1
    subst hmc
    intro mc _ _
    simp [heldModel, heldModelBraid, Model.Lifecycle.braidMessageOf, chunkComposite,
      Model.Lifecycle.braidTypeOf]
  · simp only [heldReal, heldBraid, Tacenta.SessionUnitBraidT1.State.epoch_val]
    scalar_tac
  · intro modelComposite ciphertext hdecode
    rw [chunk_decode_model] at hdecode
    have hmc : chunkComposite = modelComposite := (Prod.mk.inj (Except.ok.inj hdecode)).1
    subst hmc
    have hout := chunk_braid_step oracle.braidKem dk ekVector header
    simp only [heldModel] at hout ⊢
    rw [hout]
    exact invReal_retryRunBounds k pkb ad a dh _ rfl

/-- **A caller-selected run carrying an agreement chunk; not a claim.**  The message's agreement part is a
`ct1` message of the Braid's epoch carrying a chunk, and the chunk and the codeword view are chosen
together: the chunk is index 0 and 32 zero bytes, a codeword of 1408 zero bytes by the real encoder
(`zero_chunk_codeword`), and `chunkView` reads every chunk as that codeword.  1408 zero bytes is not a
ciphertext `encapsulate1` produces, so no honest responder sends this chunk.  `HonestChunk` asks nothing
of a chunk that starts a fresh decoder, and the model's refusal at the first agreement discards the
Braid step it would commit (`chunk_braid_step`).  It is not a non-vacuity statement for chunks: that
would take every chunk that fits the real decoder, with a view derived from it, where this fixes one
chunk and one view.  A decoder already holding a chunk is not reached here. -/
theorem decrypt_hypotheses_with_chunk_at_wrapperKem_held (dh : DhView)
    (L : DecryptWrapperLaws dh) (G : LawGenerateSucceeds) :
    ∃ (oracle : Model.Lifecycle.Oracle) (real : lifecycle.Session)
      (model : Model.Lifecycle.Session) (message : Slice Std.U8) (rng : List Std.U8)
      (view : Model.Lifecycle.CodewordView) (composite : Model.CompositeHeader.Composite)
      (ciphertext : Bytes) (chunk : Model.Braid.Chunk),
      oracle.braidKem = wrapperKem ∧
      HeldKemAt real model ∧
      (∃ decoded, tacenta_wire.decode_message message = ok (.Ok decoded)) ∧
      Model.CompositeHeader.decodeDetailed (sliceOf message) = .ok (composite, ciphertext) ∧
      Model.Lifecycle.messageType (sliceOf message) = some .ratchet ∧
      Model.Lifecycle.braidMessageOf view model.braid composite =
        ⟨model.braid.epoch, .ct1, some chunk⟩ ∧
      DecryptHypotheses byteRng byteCrc byteTrace dh view oracle real model message rng := by
  obtain ⟨oracle, hdraws, hK, horacle⟩ :=
    Tacenta.UnitOracleDecrypt.decryptOracleOf_of_laws dh L.dhCodec L.dhAgree L.aeadOpen
      L.viewInjective (byteTrace sampleRng) wrapperKem
  obtain ⟨k, pkb, a, hpub, hbytes, hcan, hprime⟩ := L.validKey
  obtain ⟨ad, had, hlen⟩ :=
    Std.WP.spec_imp_exists (Tacenta.UnitLifecycleT1.identity_ad_length L.dhCodec pkb pkb)
  obtain ⟨decoded, hdec, -⟩ := chunk_decode_real
  obtain ⟨seed, kp, rest, hslen, hgen⟩ := G
  obtain ⟨h, v, hh, hv, hhl, -, hkg, hhash, hkpv, hfresh⟩ := held_key_agreements L.kem hslen hgen
  have hdiv : Tacenta.SessionUnitDecoderBound.DivCeilValue := L.laws.divCeil
  have hea : ErasureAgrees := Tacenta.UnitErasureRs.Glue.erasureAgrees hdiv L.truncatePrefix
  obtain ⟨-, enc, -, -, -, -, -, henc, hencinv, hsized⟩ :=
    held_encoder hdiv hea (hdrMsgOf (vecOf h)) (hdrMsgOf_length _ hhl)
  have hbraid := heldBraid_invariant L.kem.constants.1 kp enc hencinv hsized hkpv
  have hsend := heldModelBraid_is_send wrapperKem _ _ _ _ _ hkg hhash
  rw [List.take_append_drop] at hsend
  refine ⟨oracle, heldReal k pkb ad a kp enc,
    heldModel dh (heldReal k pkb ad a kp enc) (seed.map u8) (vecOf v) (vecOf h), chunkMessage,
    sampleRng, chunkView, chunkComposite, [], ⟨ct1Zeros, 0⟩, hK,
    ⟨seed, kp, rest, enc, h, v, hslen, hgen, hh, hv, rfl, rfl, hsend.symm⟩,
    ⟨decoded, hdec⟩, chunk_decode_model, chunkMessage_type, ?_, ?_⟩
  · simp [heldModel, heldModelBraid, Model.Lifecycle.braidMessageOf, chunkComposite,
      Model.Lifecycle.braidTypeOf, chunkView, Model.Braid.BraidState.epoch]
  · exact decrypt_hypotheses_at_held_of_run dh L oracle hK hdraws horacle k pkb a hpub hbytes hcan
      hprime ad had hlen kp enc _ _ _ hfresh henc hbraid chunkView chunkMessage
      (held_chunk_run dh hdiv k pkb ad a kp enc _ _ _ oracle)

/-! ## What the relation at the held state asks of the KEM model -/

/-- At the held state the relation fixes the model's vector: for every KEM model `K`, a model state
that the held session refines holds the bytes of the key pair's `ek_vector`, and no other. -/
theorem held_relation_pins_vector (K : Model.Braid.Kem) (dh : DhView) (k pkb ad a)
    (kp : tacenta_kem.IncrementalKeyPair) (enc : tacenta_erasure.Encoder) (dk ekVector header : Bytes)
    (v : alloc.vec.Vec Std.U8) (hv : tacenta_kem.IncrementalKeyPair.ek_vector kp = ok v)
    (hrel : SessionRefines dh K (heldReal k pkb ad a kp enc)
      (heldModel dh (heldReal k pkb ad a kp enc) dk ekVector header)) :
    ekVector = vecOf v := by
  have hb := hrel.braid
  simp only [heldReal, heldBraid, heldModel, heldModelBraid,
    Tacenta.SessionUnitBraidT3.StateRefines] at hb
  obtain ⟨-, -, ⟨-, ⟨v', hv', hvv⟩, -⟩, -⟩ := hb
  rw [hv] at hv'; cases hv'
  exact hvv.symm

/-- **At the held state the relation fails at `toyKem`.**  `toyKem` decapsulates to its private part,
and a held private part of 64 bytes is no 32-byte shared secret, so no real decapsulation result
matches it, `Ok` or `Err`.  (At the `KeysUnsampled` witness the relation holds at every KEM model.) -/
theorem held_not_refines_toyKem (dh : DhView) (k pkb ad a)
    (kp : tacenta_kem.IncrementalKeyPair) (enc : tacenta_erasure.Encoder) (dk ekVector header : Bytes)
    (hdk : dk.length = 64) :
    ¬ SessionRefines dh Model.Braid.toyKem (heldReal k pkb ad a kp enc)
      (heldModel dh (heldReal k pkb ad a kp enc) dk ekVector header) := by
  intro hrel
  have hb := hrel.braid
  simp only [heldReal, heldBraid, heldModel, heldModelBraid,
    Tacenta.SessionUnitBraidT3.StateRefines] at hb
  obtain ⟨-, -, ⟨hkp, -, -⟩, -⟩ := hb
  have h64 : (List.replicate 64 (0 : UInt8)).length ≤ Usize.max := by
    simp; exact usize_max_ge 64 (by norm_num)
  have h32 : (List.replicate 32 (0 : UInt8)).length ≤ Usize.max := by
    simp; exact usize_max_ge 32 (by norm_num)
  have l1 : (sliceOfBytes _ h64).length = Model.Braid.toyKem.ct1Size := by
    simp [sliceOfBytes, bytesOf, Model.Braid.toyKem]
  have l2 : (sliceOfBytes _ h32).length = Model.Braid.toyKem.ct2Size := by
    simp [sliceOfBytes, bytesOf, Model.Braid.toyKem]
  rcases hkp _ _ l1 l2 with ⟨raw, -, hval⟩ | ⟨-, hval⟩
  · simp only [Model.Braid.toyKem, Option.some.injEq] at hval
    have := congrArg List.length hval
    simp [keyOf, hdk] at this
  · simp [Model.Braid.toyKem] at hval

/-! ## What the model does at the witness -/

/-- **The model's step at the held state refuses at the first agreement when the oracle's agreement
refuses the all-zero key**, at either message (both composites carry the all-zero ratchet key). -/
theorem held_model_refuses_of_agreement (dh : DhView) (view : Model.Lifecycle.CodewordView)
    (oracle : Model.Lifecycle.Oracle) (k pkb ad a) (kp : tacenta_kem.IncrementalKeyPair)
    (enc : tacenta_erasure.Encoder) (dk ekVector header : Bytes) (message : Slice Std.U8)
    (composite : Model.CompositeHeader.Composite) (ciphertext : Bytes)
    (hdec : Model.CompositeHeader.decodeDetailed (sliceOf message) = .ok (composite, ciphertext))
    (hzero : composite.dh = List.replicate 32 0)
    (hnone : oracle.dhAgree (dh.privateKey k) (List.replicate 32 0) = none) :
    (Model.Lifecycle.decryptRatchet view oracle
      (heldModel dh (heldReal k pkb ad a kp enc) dk ekVector header) (sliceOf message)).result =
      .error (.handshake .nonContributoryAgreement) := by
  simp [Model.Lifecycle.decryptRatchet, Model.Lifecycle.agreementFailed, heldModel, heldModelBraid,
    modelOf, heldReal, invReal, Tacenta.UnitHeadroomSatisfiable.sessionOf, hdec, hzero]
  simp only [List.replicate] at hnone
  simp [hnone]

end Tacenta.UnitHeldKemWitness

/-! ## Pins

The axiom list and the statement of each result, and the bodies of the added law, the held states, the
held-value predicate and the chunk message, held by the build.  `attest.py` requires them
(`REQUIRED_PINS`, `REQUIRED_STATEMENT_PINS`, `REQUIRED_PRINT_FORM`).  No result here lists a
compiler-trust axiom. -/

/--
info: 'Tacenta.UnitHeldKemWitness.LawGenerateSucceeds_is' depends on axioms: [propext,
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
#print axioms Tacenta.UnitHeldKemWitness.LawGenerateSucceeds_is

/--
info: Tacenta.UnitHeldKemWitness.LawGenerateSucceeds_is : Tacenta.UnitHeldKemWitness.LawGenerateSucceeds ↔
  Tacenta.UnitHeldKemWitness.LawGenerateSucceedsShape Interp.real
-/
#guard_msgs in
#check @Tacenta.UnitHeldKemWitness.LawGenerateSucceeds_is

/--
info: 'Tacenta.UnitHeldKemWitness.lawGenerateSucceeds_of_kemDrawsSucceed' depends on axioms: [propext,
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
#print axioms Tacenta.UnitHeldKemWitness.lawGenerateSucceeds_of_kemDrawsSucceed

/--
info: Tacenta.UnitHeldKemWitness.lawGenerateSucceeds_of_kemDrawsSucceed : WrapperKemLaws →
  KemDrawsSucceed → Tacenta.UnitHeldKemWitness.LawGenerateSucceeds
-/
#guard_msgs in
#check @Tacenta.UnitHeldKemWitness.lawGenerateSucceeds_of_kemDrawsSucceed

/--
info: 'Tacenta.UnitHeldKemWitness.modelShipped_generateSucceeds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitHeldKemWitness.modelShipped_generateSucceeds

/--
info: Tacenta.UnitHeldKemWitness.modelShipped_generateSucceeds : Tacenta.UnitHeldKemWitness.LawGenerateSucceedsShape
  Interp.modelShipped
-/
#guard_msgs in
#check @Tacenta.UnitHeldKemWitness.modelShipped_generateSucceeds

/--
info: 'Tacenta.UnitHeldKemWitness.held_laws_satisfiable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitHeldKemWitness.held_laws_satisfiable

/--
info: Tacenta.UnitHeldKemWitness.held_laws_satisfiable : ∃ I dh oeq,
  I.HEADER_LEN = ok 64#usize ∧
    I.EK_VECTOR_LEN = ok 1536#usize ∧
      I.CT1_LEN = ok 1408#usize ∧
        I.CT2_LEN = ok 160#usize ∧
          (DecryptWrapperLawsShape I dh fun {T} => oeq) ∧ Tacenta.UnitHeldKemWitness.LawGenerateSucceedsShape I
-/
#guard_msgs in
#check @Tacenta.UnitHeldKemWitness.held_laws_satisfiable

/--
info: 'Tacenta.UnitHeldKemWitness.hdrMsgOf_length' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitHeldKemWitness.hdrMsgOf_length

/--
info: Tacenta.UnitHeldKemWitness.hdrMsgOf_length : ∀ (header : Bytes),
  List.length header = 64 → List.length (Tacenta.UnitHeldKemWitness.hdrMsgOf header) = 96
-/
#guard_msgs in
#check @Tacenta.UnitHeldKemWitness.hdrMsgOf_length

/--
info: 'Tacenta.UnitHeldKemWitness.hdrMsgOf_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitHeldKemWitness.hdrMsgOf_le

/--
info: Tacenta.UnitHeldKemWitness.hdrMsgOf_le : ∀ (header : Bytes),
  List.length header = 64 → List.length (Tacenta.UnitHeldKemWitness.hdrMsgOf header) ≤ Usize.max
-/
#guard_msgs in
#check @Tacenta.UnitHeldKemWitness.hdrMsgOf_le

/--
info: 'Tacenta.UnitHeldKemWitness.chunks_length' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitHeldKemWitness.chunks_length

/--
info: Tacenta.UnitHeldKemWitness.chunks_length : ∀ (m : Bytes), (Model.Erasure.chunks m).length = (List.length m + 31) / 32
-/
#guard_msgs in
#check @Tacenta.UnitHeldKemWitness.chunks_length

/--
info: 'Tacenta.UnitHeldKemWitness.held_encoder' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 alloc.vec.Vec.truncate,
 core.num.Usize.div_ceil]
-/
#guard_msgs in
#print axioms Tacenta.UnitHeldKemWitness.held_encoder

/--
info: Tacenta.UnitHeldKemWitness.held_encoder : Tacenta.SessionUnitDecoderBound.DivCeilValue →
  ErasureAgrees →
    ∀ (m : Bytes) (hm : List.length m = 96),
      ∃ enc0 enc1 c,
        tacenta_erasure.Encoder.new (sliceOfBytes m ⋯) = ok enc0 ∧
          enc0.next_chunk = ok (some c, enc1) ∧
            ↑c.index = 0 ∧
              CodewordOf m c ∧
                EncoderRefines enc1 { source := m, next := 1 } ∧
                  enc1.invariant = ok true ∧ ∀ (len : Usize), ↑len = 96 → tacenta_braid.encoder_sized enc1 len = ok true
-/
#guard_msgs in
#check @Tacenta.UnitHeldKemWitness.held_encoder

/--
info: 'Tacenta.UnitHeldKemWitness.held_key_agreements' depends on axioms: [propext,
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
#print axioms Tacenta.UnitHeldKemWitness.held_key_agreements

/--
info: Tacenta.UnitHeldKemWitness.held_key_agreements : WrapperKemLaws →
  ∀ {seed : List U8} {kp : tacenta_kem.IncrementalKeyPair} {rest : List U8},
    seed.length = 64 →
      tacenta_kem.IncrementalKeyPair.generate byteRng byteCrc seed = ok (core.result.Result.Ok kp, rest) →
        ∃ h v,
          kp.header = ok h ∧
            kp.ek_vector = ok v ∧
              (vecOf h).length = 64 ∧
                (vecOf v).length = wrapperKem.ekSize ∧
                  wrapperKem.keyGen (leNat (List.map u8 seed)) =
                      some (List.map u8 seed, List.take 32 (vecOf h), vecOf v) ∧
                    wrapperKem.hashEk (List.take 32 (vecOf h)) (vecOf v) = List.drop 32 (vecOf h) ∧
                      tacenta_braid.key_pair_valid kp = ok true ∧
                        FreshKeyPairRefines wrapperKem kp (List.map u8 seed) (vecOf v)
-/
#guard_msgs in
#check @Tacenta.UnitHeldKemWitness.held_key_agreements

/--
info: 'Tacenta.UnitHeldKemWitness.structural_held' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kem.EncapsState,
 tacenta_kem.IncrementalKeyPair,
 tacenta_boundary.dh.PrivateKey,
 tacenta_boundary.dh.PublicKeyBytes,
 tacenta_boundary.dh.is_prime_order_public,
 tacenta_boundary.kem.ciphertext_len,
 tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 core.option.Option.Insts.CoreCmpPartialEqOption.eq]
-/
#guard_msgs in
#print axioms Tacenta.UnitHeldKemWitness.structural_held

/--
info: Tacenta.UnitHeldKemWitness.structural_held : ∀ (k : tacenta_boundary.dh.PrivateKey)
  (pkb : tacenta_boundary.dh.PublicKeyBytes) (a : Std.Array U8 32#usize),
  k.public_key = ok pkb →
    pkb.as_bytes = ok a →
      Tacenta.SessionUnitT1.canonicalX25519 a = true →
        tacenta_boundary.dh.is_prime_order_public pkb = ok true →
          OptionEqU64Shape @core.option.Option.Insts.CoreCmpPartialEqOption.eq →
            ∀ (ad : alloc.vec.Vec U8),
              lifecycle.identity_ad pkb pkb = ok ad →
                ∀ (kp : tacenta_kem.IncrementalKeyPair) (enc : tacenta_erasure.Encoder),
                  (Tacenta.UnitHeldKemWitness.heldReal k pkb ad a kp enc).structural_invariant = ok true
-/
#guard_msgs in
#check @Tacenta.UnitHeldKemWitness.structural_held

/--
info: 'Tacenta.UnitHeldKemWitness.heldBraid_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kem.CT1_LEN,
 tacenta_kem.CT2_LEN,
 tacenta_kem.EK_VECTOR_LEN,
 tacenta_kem.EncapsState,
 tacenta_kem.HEADER_LEN,
 tacenta_kem.IncrementalKeyPair,
 tacenta_kem.validate_ek,
 tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_kem.IncrementalKeyPair.header,
 core.num.Usize.div_ceil]
-/
#guard_msgs in
#print axioms Tacenta.UnitHeldKemWitness.heldBraid_invariant

/--
info: Tacenta.UnitHeldKemWitness.heldBraid_invariant : tacenta_kem.HEADER_LEN = ok 64#usize →
  ∀ (kp : tacenta_kem.IncrementalKeyPair) (enc : tacenta_erasure.Encoder),
    enc.invariant = ok true →
      (∀ (len : Usize), ↑len = 96 → tacenta_braid.encoder_sized enc len = ok true) →
        tacenta_braid.key_pair_valid kp = ok true → (Tacenta.UnitHeldKemWitness.heldBraid kp enc).invariant = ok true
-/
#guard_msgs in
#check @Tacenta.UnitHeldKemWitness.heldBraid_invariant

/--
info: 'Tacenta.UnitHeldKemWitness.held_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kem.CT1_LEN,
 tacenta_kem.CT2_LEN,
 tacenta_kem.EK_VECTOR_LEN,
 tacenta_kem.EncapsState,
 tacenta_kem.HEADER_LEN,
 tacenta_kem.IncrementalKeyPair,
 tacenta_kem.validate_ek,
 tacenta_boundary.dh.PrivateKey,
 tacenta_boundary.dh.PublicKeyBytes,
 tacenta_boundary.dh.is_prime_order_public,
 tacenta_boundary.kem.ciphertext_len,
 tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_kem.IncrementalKeyPair.header,
 core.num.Usize.div_ceil,
 tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 core.option.Option.Insts.CoreCmpPartialEqOption.eq]
-/
#guard_msgs in
#print axioms Tacenta.UnitHeldKemWitness.held_invariant

/--
info: Tacenta.UnitHeldKemWitness.held_invariant : ∀ (k : tacenta_boundary.dh.PrivateKey)
  (pkb : tacenta_boundary.dh.PublicKeyBytes) (a : Std.Array U8 32#usize),
  k.public_key = ok pkb →
    pkb.as_bytes = ok a →
      Tacenta.SessionUnitT1.canonicalX25519 a = true →
        tacenta_boundary.dh.is_prime_order_public pkb = ok true →
          OptionEqU64Shape @core.option.Option.Insts.CoreCmpPartialEqOption.eq →
            ∀ (ad : alloc.vec.Vec U8),
              lifecycle.identity_ad pkb pkb = ok ad →
                ∀ (kp : tacenta_kem.IncrementalKeyPair) (enc : tacenta_erasure.Encoder),
                  (Tacenta.UnitHeldKemWitness.heldBraid kp enc).invariant = ok true →
                    (Tacenta.UnitHeldKemWitness.heldReal k pkb ad a kp enc).invariant = ok true
-/
#guard_msgs in
#check @Tacenta.UnitHeldKemWitness.held_invariant

/--
info: 'Tacenta.UnitHeldKemWitness.held_sessionRefines' depends on axioms: [propext,
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
#print axioms Tacenta.UnitHeldKemWitness.held_sessionRefines

/--
info: Tacenta.UnitHeldKemWitness.held_sessionRefines : ∀ (K : Model.Braid.Kem) (dh : DhView)
  (k : tacenta_boundary.dh.PrivateKey) (pkb : tacenta_boundary.dh.PublicKeyBytes) (ad : alloc.vec.Vec U8)
  (a : Std.Array U8 32#usize) (kp : tacenta_kem.IncrementalKeyPair) (enc : tacenta_erasure.Encoder)
  (dk ekVector header : Bytes),
  FreshKeyPairRefines K kp dk ekVector →
    EncoderRefines enc { source := Tacenta.UnitHeldKemWitness.hdrMsgOf header, next := 1 } →
      SessionRefines dh K (Tacenta.UnitHeldKemWitness.heldReal k pkb ad a kp enc)
        (Tacenta.UnitHeldKemWitness.heldModel dh (Tacenta.UnitHeldKemWitness.heldReal k pkb ad a kp enc) dk ekVector
          header)
-/
#guard_msgs in
#check @Tacenta.UnitHeldKemWitness.held_sessionRefines

/--
info: 'Tacenta.UnitHeldKemWitness.held_braid_output' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitHeldKemWitness.held_braid_output

/--
info: Tacenta.UnitHeldKemWitness.held_braid_output : ∀ (K : Model.Braid.Kem) (view : Model.Lifecycle.CodewordView)
  (dk ekVector header : Bytes),
  (Model.Braid.receive K (Tacenta.UnitHeldKemWitness.heldModelBraid dk ekVector header)
          (Model.Lifecycle.braidMessageOf view (Tacenta.UnitHeldKemWitness.heldModelBraid dk ekVector header)
            sampleComposite)).2.1 =
    none
-/
#guard_msgs in
#check @Tacenta.UnitHeldKemWitness.held_braid_output

/--
info: 'Tacenta.UnitHeldKemWitness.held_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kem.EncapsState,
 tacenta_kem.IncrementalKeyPair,
 tacenta_boundary.dh.PrivateKey,
 tacenta_boundary.dh.PublicKeyBytes,
 core.num.Usize.div_ceil]
-/
#guard_msgs in
#print axioms Tacenta.UnitHeldKemWitness.held_run

/--
info: Tacenta.UnitHeldKemWitness.held_run : ∀ (dh : DhView) (k : tacenta_boundary.dh.PrivateKey)
  (pkb : tacenta_boundary.dh.PublicKeyBytes) (ad : alloc.vec.Vec U8) (a : Std.Array U8 32#usize)
  (kp : tacenta_kem.IncrementalKeyPair) (enc : tacenta_erasure.Encoder) (dk ekVector header : Bytes)
  (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle),
  DecryptRatchetRun view oracle byteTrace (Tacenta.UnitHeldKemWitness.heldReal k pkb ad a kp enc)
    (Tacenta.UnitHeldKemWitness.heldModel dh (Tacenta.UnitHeldKemWitness.heldReal k pkb ad a kp enc) dk ekVector header)
    sampleMessage sampleRng
-/
#guard_msgs in
#check @Tacenta.UnitHeldKemWitness.held_run

/--
info: 'Tacenta.UnitHeldKemWitness.decrypt_hypotheses_at_held_of_run' depends on axioms: [propext,
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
#print axioms Tacenta.UnitHeldKemWitness.decrypt_hypotheses_at_held_of_run

/--
info: Tacenta.UnitHeldKemWitness.decrypt_hypotheses_at_held_of_run : ∀ (dh : DhView),
  DecryptWrapperLaws dh →
    ∀ (oracle : Model.Lifecycle.Oracle),
      oracle.braidKem = wrapperKem →
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
                            ∀ (kp : tacenta_kem.IncrementalKeyPair) (enc : tacenta_erasure.Encoder)
                              (dk ekVector header : Bytes),
                              FreshKeyPairRefines wrapperKem kp dk ekVector →
                                EncoderRefines enc { source := Tacenta.UnitHeldKemWitness.hdrMsgOf header, next := 1 } →
                                  (Tacenta.UnitHeldKemWitness.heldBraid kp enc).invariant = ok true →
                                    ∀ (view : Model.Lifecycle.CodewordView) (message : Slice U8),
                                      DecryptRatchetRun view oracle byteTrace
                                          (Tacenta.UnitHeldKemWitness.heldReal k pkb ad a kp enc)
                                          (Tacenta.UnitHeldKemWitness.heldModel dh
                                            (Tacenta.UnitHeldKemWitness.heldReal k pkb ad a kp enc) dk ekVector header)
                                          message sampleRng →
                                        DecryptHypotheses byteRng byteCrc byteTrace dh view oracle
                                          (Tacenta.UnitHeldKemWitness.heldReal k pkb ad a kp enc)
                                          (Tacenta.UnitHeldKemWitness.heldModel dh
                                            (Tacenta.UnitHeldKemWitness.heldReal k pkb ad a kp enc) dk ekVector header)
                                          message sampleRng
-/
#guard_msgs in
#check @Tacenta.UnitHeldKemWitness.decrypt_hypotheses_at_held_of_run

/--
info: 'Tacenta.UnitHeldKemWitness.decrypt_hypotheses_at_held' depends on axioms: [propext,
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
#print axioms Tacenta.UnitHeldKemWitness.decrypt_hypotheses_at_held

/--
info: Tacenta.UnitHeldKemWitness.decrypt_hypotheses_at_held : ∀ (dh : DhView),
  DecryptWrapperLaws dh →
    ∀ (oracle : Model.Lifecycle.Oracle),
      oracle.braidKem = wrapperKem →
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
                            ∀ (kp : tacenta_kem.IncrementalKeyPair) (enc : tacenta_erasure.Encoder)
                              (dk ekVector header : Bytes),
                              FreshKeyPairRefines wrapperKem kp dk ekVector →
                                EncoderRefines enc { source := Tacenta.UnitHeldKemWitness.hdrMsgOf header, next := 1 } →
                                  (Tacenta.UnitHeldKemWitness.heldBraid kp enc).invariant = ok true →
                                    ∀ (view : Model.Lifecycle.CodewordView),
                                      DecryptHypotheses byteRng byteCrc byteTrace dh view oracle
                                        (Tacenta.UnitHeldKemWitness.heldReal k pkb ad a kp enc)
                                        (Tacenta.UnitHeldKemWitness.heldModel dh
                                          (Tacenta.UnitHeldKemWitness.heldReal k pkb ad a kp enc) dk ekVector header)
                                        sampleMessage sampleRng
-/
#guard_msgs in
#check @Tacenta.UnitHeldKemWitness.decrypt_hypotheses_at_held

/--
info: 'Tacenta.UnitHeldKemWitness.heldModelBraid_is_send' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitHeldKemWitness.heldModelBraid_is_send

/--
info: Tacenta.UnitHeldKemWitness.heldModelBraid_is_send : ∀ (K : Model.Braid.Kem) (rand : ℕ) (dk ekSeed hek ekVector : Bytes),
  K.keyGen rand = some (dk, ekSeed, ekVector) →
    K.hashEk ekSeed ekVector = hek →
      (Model.Braid.send K rand (Model.Braid.BraidState.keysUnsampled 1 modelAuth0)).2.2.2 =
        Tacenta.UnitHeldKemWitness.heldModelBraid dk ekVector (ekSeed ++ hek)
-/
#guard_msgs in
#check @Tacenta.UnitHeldKemWitness.heldModelBraid_is_send

/--
info: 'Tacenta.UnitHeldKemWitness.decrypt_hypotheses_jointly_satisfiable_at_wrapperKem_held' depends on axioms: [propext,
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
#print axioms Tacenta.UnitHeldKemWitness.decrypt_hypotheses_jointly_satisfiable_at_wrapperKem_held

/--
info: Tacenta.UnitHeldKemWitness.decrypt_hypotheses_jointly_satisfiable_at_wrapperKem_held : ∀ (dh : DhView),
  DecryptWrapperLaws dh →
    Tacenta.UnitHeldKemWitness.LawGenerateSucceeds →
      ∃ oracle real model message rng,
        oracle.braidKem = wrapperKem ∧
          Tacenta.UnitHeldKemWitness.HeldKemAt real model ∧
            (∃ decoded, tacenta_wire.decode_message message = ok (core.result.Result.Ok decoded)) ∧
              (∃ composite ciphertext,
                  Model.CompositeHeader.decodeDetailed (sliceOf message) = Except.ok (composite, ciphertext)) ∧
                Model.Lifecycle.messageType (sliceOf message) = some Model.Lifecycle.MessageType.ratchet ∧
                  ∀ (view : Model.Lifecycle.CodewordView),
                    DecryptHypotheses byteRng byteCrc byteTrace dh view oracle real model message rng
-/
#guard_msgs in
#check @Tacenta.UnitHeldKemWitness.decrypt_hypotheses_jointly_satisfiable_at_wrapperKem_held

/--
info: 'Tacenta.UnitHeldKemWitness.ct1Zeros_length' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Tacenta.UnitHeldKemWitness.ct1Zeros_length

/--
info: Tacenta.UnitHeldKemWitness.ct1Zeros_length : List.length Tacenta.UnitHeldKemWitness.ct1Zeros = 1408
-/
#guard_msgs in
#check @Tacenta.UnitHeldKemWitness.ct1Zeros_length

/--
info: 'Tacenta.UnitHeldKemWitness.ct1Zeros_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitHeldKemWitness.ct1Zeros_le

/--
info: Tacenta.UnitHeldKemWitness.ct1Zeros_le : List.length Tacenta.UnitHeldKemWitness.ct1Zeros ≤ Usize.max
-/
#guard_msgs in
#check @Tacenta.UnitHeldKemWitness.ct1Zeros_le

/--
info: 'Tacenta.UnitHeldKemWitness.codeword_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitHeldKemWitness.codeword_zero

/--
info: Tacenta.UnitHeldKemWitness.codeword_zero : ∀ (m : Bytes),
  32 ≤ List.length m → Model.Erasure.codeword (List.take 65536 (Model.Erasure.chunks m)) 0 = List.take 32 m
-/
#guard_msgs in
#check @Tacenta.UnitHeldKemWitness.codeword_zero

/--
info: 'Tacenta.UnitHeldKemWitness.ct1Zeros_codeword0' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitHeldKemWitness.ct1Zeros_codeword0

/--
info: Tacenta.UnitHeldKemWitness.ct1Zeros_codeword0 : Model.Erasure.codeword
    (List.take 65536 (Model.Erasure.chunks Tacenta.UnitHeldKemWitness.ct1Zeros)) 0 =
  List.replicate 32 0
-/
#guard_msgs in
#check @Tacenta.UnitHeldKemWitness.ct1Zeros_codeword0

/--
info: 'Tacenta.UnitHeldKemWitness.u8_map_inj' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitHeldKemWitness.u8_map_inj

/--
info: @Tacenta.UnitHeldKemWitness.u8_map_inj : ∀ {a b : List U8}, List.map u8 a = List.map u8 b → a = b
-/
#guard_msgs in
#check @Tacenta.UnitHeldKemWitness.u8_map_inj

/--
info: 'Tacenta.UnitHeldKemWitness.zero_chunk_codeword' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 core.num.Usize.div_ceil]
-/
#guard_msgs in
#print axioms Tacenta.UnitHeldKemWitness.zero_chunk_codeword

/--
info: Tacenta.UnitHeldKemWitness.zero_chunk_codeword : Tacenta.SessionUnitDecoderBound.DivCeilValue →
  ∀ (c : tacenta_erasure.Chunk),
    ↑c.index = 0 → List.map u8 ↑c.data = List.replicate 32 0 → CodewordOf Tacenta.UnitHeldKemWitness.ct1Zeros c
-/
#guard_msgs in
#check @Tacenta.UnitHeldKemWitness.zero_chunk_codeword

/--
info: 'Tacenta.UnitHeldKemWitness.chunkBytes_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitHeldKemWitness.chunkBytes_le

/--
info: Tacenta.UnitHeldKemWitness.chunkBytes_le : List.length Tacenta.UnitHeldKemWitness.chunkBytes ≤ Usize.max
-/
#guard_msgs in
#check @Tacenta.UnitHeldKemWitness.chunkBytes_le

/--
info: 'Tacenta.UnitHeldKemWitness.sliceOf_chunkMessage' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitHeldKemWitness.sliceOf_chunkMessage

/--
info: Tacenta.UnitHeldKemWitness.sliceOf_chunkMessage : sliceOf Tacenta.UnitHeldKemWitness.chunkMessage =
  Tacenta.UnitHeldKemWitness.chunkBytes
-/
#guard_msgs in
#check @Tacenta.UnitHeldKemWitness.sliceOf_chunkMessage

/--
info: 'Tacenta.UnitHeldKemWitness.chunk_decode_model' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitHeldKemWitness.chunk_decode_model

/--
info: Tacenta.UnitHeldKemWitness.chunk_decode_model : Model.CompositeHeader.decodeDetailed
    (sliceOf Tacenta.UnitHeldKemWitness.chunkMessage) =
  Except.ok (Tacenta.UnitHeldKemWitness.chunkComposite, [])
-/
#guard_msgs in
#check @Tacenta.UnitHeldKemWitness.chunk_decode_model

/--
info: 'Tacenta.UnitHeldKemWitness.chunk_decode_real' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitHeldKemWitness.chunk_decode_real

/--
info: Tacenta.UnitHeldKemWitness.chunk_decode_real : ∃ decoded,
  tacenta_wire.decode_message Tacenta.UnitHeldKemWitness.chunkMessage = ok (core.result.Result.Ok decoded) ∧
    CompositeRefines decoded.header Tacenta.UnitHeldKemWitness.chunkComposite
-/
#guard_msgs in
#check @Tacenta.UnitHeldKemWitness.chunk_decode_real

/--
info: 'Tacenta.UnitHeldKemWitness.chunkMessage_type' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitHeldKemWitness.chunkMessage_type

/--
info: Tacenta.UnitHeldKemWitness.chunkMessage_type : Model.Lifecycle.messageType
    (sliceOf Tacenta.UnitHeldKemWitness.chunkMessage) =
  some Model.Lifecycle.MessageType.ratchet
-/
#guard_msgs in
#check @Tacenta.UnitHeldKemWitness.chunkMessage_type

/--
info: 'Tacenta.UnitHeldKemWitness.chunk_braid_step' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitHeldKemWitness.chunk_braid_step

/--
info: Tacenta.UnitHeldKemWitness.chunk_braid_step : ∀ (K : Model.Braid.Kem) (dk ekVector header : Bytes),
  Model.Braid.receive K (Tacenta.UnitHeldKemWitness.heldModelBraid dk ekVector header)
      (Model.Lifecycle.braidMessageOf Tacenta.UnitHeldKemWitness.chunkView
        (Tacenta.UnitHeldKemWitness.heldModelBraid dk ekVector header) Tacenta.UnitHeldKemWitness.chunkComposite) =
    (0, none,
      Model.Braid.BraidState.headerSent 1 modelAuth0 dk
        ((Model.Braid.Decoder.new K.ct1Size).addChunk { source := Tacenta.UnitHeldKemWitness.ct1Zeros, index := 0 })
        (Model.Braid.encode ekVector))
-/
#guard_msgs in
#check @Tacenta.UnitHeldKemWitness.chunk_braid_step

/--
info: 'Tacenta.UnitHeldKemWitness.held_chunk_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kem.EncapsState,
 tacenta_kem.IncrementalKeyPair,
 tacenta_boundary.dh.PrivateKey,
 tacenta_boundary.dh.PublicKeyBytes,
 core.num.Usize.div_ceil]
-/
#guard_msgs in
#print axioms Tacenta.UnitHeldKemWitness.held_chunk_run

/--
info: Tacenta.UnitHeldKemWitness.held_chunk_run : ∀ (dh : DhView),
  Tacenta.SessionUnitDecoderBound.DivCeilValue →
    ∀ (k : tacenta_boundary.dh.PrivateKey) (pkb : tacenta_boundary.dh.PublicKeyBytes) (ad : alloc.vec.Vec U8)
      (a : Std.Array U8 32#usize) (kp : tacenta_kem.IncrementalKeyPair) (enc : tacenta_erasure.Encoder)
      (dk ekVector header : Bytes) (oracle : Model.Lifecycle.Oracle),
      DecryptRatchetRun Tacenta.UnitHeldKemWitness.chunkView oracle byteTrace
        (Tacenta.UnitHeldKemWitness.heldReal k pkb ad a kp enc)
        (Tacenta.UnitHeldKemWitness.heldModel dh (Tacenta.UnitHeldKemWitness.heldReal k pkb ad a kp enc) dk ekVector
          header)
        Tacenta.UnitHeldKemWitness.chunkMessage sampleRng
-/
#guard_msgs in
#check @Tacenta.UnitHeldKemWitness.held_chunk_run

/--
info: 'Tacenta.UnitHeldKemWitness.decrypt_hypotheses_with_chunk_at_wrapperKem_held' depends on axioms: [propext,
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
#print axioms Tacenta.UnitHeldKemWitness.decrypt_hypotheses_with_chunk_at_wrapperKem_held

/--
info: Tacenta.UnitHeldKemWitness.decrypt_hypotheses_with_chunk_at_wrapperKem_held : ∀ (dh : DhView),
  DecryptWrapperLaws dh →
    Tacenta.UnitHeldKemWitness.LawGenerateSucceeds →
      ∃ oracle real model message rng view composite ciphertext chunk,
        oracle.braidKem = wrapperKem ∧
          Tacenta.UnitHeldKemWitness.HeldKemAt real model ∧
            (∃ decoded, tacenta_wire.decode_message message = ok (core.result.Result.Ok decoded)) ∧
              Model.CompositeHeader.decodeDetailed (sliceOf message) = Except.ok (composite, ciphertext) ∧
                Model.Lifecycle.messageType (sliceOf message) = some Model.Lifecycle.MessageType.ratchet ∧
                  Model.Lifecycle.braidMessageOf view model.braid composite =
                      { epoch := model.braid.epoch, type := Model.Braid.MsgType.ct1, data := some chunk } ∧
                    DecryptHypotheses byteRng byteCrc byteTrace dh view oracle real model message rng
-/
#guard_msgs in
#check @Tacenta.UnitHeldKemWitness.decrypt_hypotheses_with_chunk_at_wrapperKem_held

/--
info: 'Tacenta.UnitHeldKemWitness.held_relation_pins_vector' depends on axioms: [propext,
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
#print axioms Tacenta.UnitHeldKemWitness.held_relation_pins_vector

/--
info: Tacenta.UnitHeldKemWitness.held_relation_pins_vector : ∀ (K : Model.Braid.Kem) (dh : DhView)
  (k : tacenta_boundary.dh.PrivateKey) (pkb : tacenta_boundary.dh.PublicKeyBytes) (ad : alloc.vec.Vec U8)
  (a : Std.Array U8 32#usize) (kp : tacenta_kem.IncrementalKeyPair) (enc : tacenta_erasure.Encoder)
  (dk ekVector header : Bytes) (v : alloc.vec.Vec U8),
  kp.ek_vector = ok v →
    SessionRefines dh K (Tacenta.UnitHeldKemWitness.heldReal k pkb ad a kp enc)
        (Tacenta.UnitHeldKemWitness.heldModel dh (Tacenta.UnitHeldKemWitness.heldReal k pkb ad a kp enc) dk ekVector
          header) →
      ekVector = vecOf v
-/
#guard_msgs in
#check @Tacenta.UnitHeldKemWitness.held_relation_pins_vector

/--
info: 'Tacenta.UnitHeldKemWitness.held_not_refines_toyKem' depends on axioms: [propext,
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
#print axioms Tacenta.UnitHeldKemWitness.held_not_refines_toyKem

/--
info: Tacenta.UnitHeldKemWitness.held_not_refines_toyKem : ∀ (dh : DhView) (k : tacenta_boundary.dh.PrivateKey)
  (pkb : tacenta_boundary.dh.PublicKeyBytes) (ad : alloc.vec.Vec U8) (a : Std.Array U8 32#usize)
  (kp : tacenta_kem.IncrementalKeyPair) (enc : tacenta_erasure.Encoder) (dk ekVector header : Bytes),
  List.length dk = 64 →
    ¬SessionRefines dh Model.Braid.toyKem (Tacenta.UnitHeldKemWitness.heldReal k pkb ad a kp enc)
        (Tacenta.UnitHeldKemWitness.heldModel dh (Tacenta.UnitHeldKemWitness.heldReal k pkb ad a kp enc) dk ekVector
          header)
-/
#guard_msgs in
#check @Tacenta.UnitHeldKemWitness.held_not_refines_toyKem

/--
info: 'Tacenta.UnitHeldKemWitness.held_model_refuses_of_agreement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kem.EncapsState,
 tacenta_kem.IncrementalKeyPair,
 tacenta_boundary.dh.PrivateKey,
 tacenta_boundary.dh.PublicKeyBytes]
-/
#guard_msgs in
#print axioms Tacenta.UnitHeldKemWitness.held_model_refuses_of_agreement

/--
info: Tacenta.UnitHeldKemWitness.held_model_refuses_of_agreement : ∀ (dh : DhView) (view : Model.Lifecycle.CodewordView)
  (oracle : Model.Lifecycle.Oracle) (k : tacenta_boundary.dh.PrivateKey) (pkb : tacenta_boundary.dh.PublicKeyBytes)
  (ad : alloc.vec.Vec U8) (a : Std.Array U8 32#usize) (kp : tacenta_kem.IncrementalKeyPair)
  (enc : tacenta_erasure.Encoder) (dk ekVector header : Bytes) (message : Slice U8)
  (composite : Model.CompositeHeader.Composite) (ciphertext : Bytes),
  Model.CompositeHeader.decodeDetailed (sliceOf message) = Except.ok (composite, ciphertext) →
    composite.dh = List.replicate 32 0 →
      oracle.dhAgree (dh.privateKey k) (List.replicate 32 0) = none →
        (Model.Lifecycle.decryptRatchet view oracle
              (Tacenta.UnitHeldKemWitness.heldModel dh (Tacenta.UnitHeldKemWitness.heldReal k pkb ad a kp enc) dk
                ekVector header)
              (sliceOf message)).result =
          Except.error (Model.Lifecycle.Refusal.handshake Model.Lifecycle.HandshakeRefusal.nonContributoryAgreement)
-/
#guard_msgs in
#check @Tacenta.UnitHeldKemWitness.held_model_refuses_of_agreement

/--
info: def Tacenta.UnitHeldKemWitness.LawGenerateSucceeds : Prop :=
∃ seed kp rest,
  seed.length = 64 ∧ tacenta_kem.IncrementalKeyPair.generate byteRng byteCrc seed = ok (core.result.Result.Ok kp, rest)
-/
#guard_msgs in
#print Tacenta.UnitHeldKemWitness.LawGenerateSucceeds

/--
info: def Tacenta.UnitHeldKemWitness.LawGenerateSucceedsShape : Interp → Prop :=
fun I => ∃ seed kp rest, seed.length = 64 ∧ I.ikpGenerate byteRng byteCrc seed = ok (core.result.Result.Ok kp, rest)
-/
#guard_msgs in
#print Tacenta.UnitHeldKemWitness.LawGenerateSucceedsShape

/--
info: def Tacenta.UnitHeldKemWitness.hdrMsgOf : Bytes → Bytes :=
fun header => header ++ modelAuth0.macHdr 1 header
-/
#guard_msgs in
#print Tacenta.UnitHeldKemWitness.hdrMsgOf

/--
info: def Tacenta.UnitHeldKemWitness.heldModelBraid : Bytes → Bytes → Bytes → Model.Braid.BraidState :=
fun dk ekVector header =>
  Model.Braid.BraidState.keysSampled 1 modelAuth0 dk ekVector
    { source := Tacenta.UnitHeldKemWitness.hdrMsgOf header, next := 1 }
-/
#guard_msgs in
#print Tacenta.UnitHeldKemWitness.heldModelBraid

/--
info: def Tacenta.UnitHeldKemWitness.heldBraid : tacenta_kem.IncrementalKeyPair →
  tacenta_erasure.Encoder → tacenta_braid.Braid :=
fun kp enc => { state := tacenta_braid.State.KeysSampled 1#u64 auth0 kp enc }
-/
#guard_msgs in
#print Tacenta.UnitHeldKemWitness.heldBraid

/--
info: def Tacenta.UnitHeldKemWitness.heldReal : tacenta_boundary.dh.PrivateKey →
  tacenta_boundary.dh.PublicKeyBytes →
    alloc.vec.Vec U8 →
      Std.Array U8 32#usize → tacenta_kem.IncrementalKeyPair → tacenta_erasure.Encoder → lifecycle.Session :=
fun k pkb ad a kp enc =>
  have __src := invReal k pkb ad a;
  { triple := __src.triple, braid := Tacenta.UnitHeldKemWitness.heldBraid kp enc,
    ratchet_private := __src.ratchet_private, identity_ad := __src.identity_ad,
    our_identity_public := __src.our_identity_public, peer_identity_public := __src.peer_identity_public,
    pending_initial := __src.pending_initial, established_ephemeral := __src.established_ephemeral }
-/
#guard_msgs in
#print Tacenta.UnitHeldKemWitness.heldReal

/--
info: def Tacenta.UnitHeldKemWitness.heldModel : DhView →
  lifecycle.Session → Bytes → Bytes → Bytes → Model.Lifecycle.Session :=
fun dh real dk ekVector header =>
  have __src := modelOf dh real;
  { triple := __src.triple, braid := Tacenta.UnitHeldKemWitness.heldModelBraid dk ekVector header,
    ratchetPrivate := __src.ratchetPrivate, identityAd := __src.identityAd,
    ourIdentityPublic := __src.ourIdentityPublic, peerIdentityPublic := __src.peerIdentityPublic,
    pendingInitial := __src.pendingInitial, establishedEphemeral := __src.establishedEphemeral }
-/
#guard_msgs in
#print Tacenta.UnitHeldKemWitness.heldModel

/--
info: def Tacenta.UnitHeldKemWitness.HeldKemAt : lifecycle.Session → Model.Lifecycle.Session → Prop :=
fun real model =>
  ∃ seed kp rest enc h v,
    seed.length = 64 ∧
      tacenta_kem.IncrementalKeyPair.generate byteRng byteCrc seed = ok (core.result.Result.Ok kp, rest) ∧
        kp.header = ok h ∧
          kp.ek_vector = ok v ∧
            real.braid.state = tacenta_braid.State.KeysSampled 1#u64 auth0 kp enc ∧
              model.braid =
                  Model.Braid.BraidState.keysSampled 1 modelAuth0 (List.map u8 seed) (vecOf v)
                    { source := vecOf h ++ modelAuth0.macHdr 1 (vecOf h), next := 1 } ∧
                model.braid =
                  (Model.Braid.send wrapperKem (leNat (List.map u8 seed))
                          (Model.Braid.BraidState.keysUnsampled 1 modelAuth0)).2.2.2
-/
#guard_msgs in
#print Tacenta.UnitHeldKemWitness.HeldKemAt

/--
info: def Tacenta.UnitHeldKemWitness.ct1Zeros : Bytes :=
List.replicate 1408 0
-/
#guard_msgs in
#print Tacenta.UnitHeldKemWitness.ct1Zeros

/--
info: def Tacenta.UnitHeldKemWitness.chunkComposite : Model.CompositeHeader.Composite :=
{ dh := List.replicate 32 0, pn := 0, n := 1, pqEpoch := 0, pqN := 1, agEpoch := 1,
  agType := Model.CompositeHeader.AgreementType.ct1, agChunk := some { index := 0, data := List.replicate 32 0 } }
-/
#guard_msgs in
#print Tacenta.UnitHeldKemWitness.chunkComposite

/--
info: def Tacenta.UnitHeldKemWitness.chunkMessage : Slice U8 :=
sliceOfBytes Tacenta.UnitHeldKemWitness.chunkBytes Tacenta.UnitHeldKemWitness.chunkBytes_le
-/
#guard_msgs in
#print Tacenta.UnitHeldKemWitness.chunkMessage

/--
info: def Tacenta.UnitHeldKemWitness.chunkView : Model.Lifecycle.CodewordView :=
{ receive := fun x x_1 x_2 => { source := Tacenta.UnitHeldKemWitness.ct1Zeros, index := 0 },
  send := fun x x_1 => default }
-/
#guard_msgs in
#print Tacenta.UnitHeldKemWitness.chunkView
