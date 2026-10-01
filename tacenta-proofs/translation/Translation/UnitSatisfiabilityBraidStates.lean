import Translation.UnitSatisfiabilityBraidAgreements

/-!
# The state-level hypotheses of the four Braid refinement theorems are satisfiable together

`step_send_refines`, `Braid.send_refines`, `step_receive_refines` and `Braid.receive_refines`
(`SessionUnitBraidT3.lean`) take, besides the agreements about opaque constants and the erasure
coder, hypotheses about the state they run on and the message they receive:

* `hrel : StateRefines K state model`,
* `hlive : EncodersLive model`   (send),
* `hct1b : State.ct1_bounded state`, `hdb : State.decoders_bounded state`,
  `hepoch : (State.epoch_val state).val + 1 < U64.max`   (receive),
* `hmsg : MsgRefines msg modelMsg`, `hhonest : HonestChunk model modelMsg`   (receive).

A theorem is vacuous if nothing satisfies its hypotheses together.  This module shows that, given
the agreements the theorems already take (`ErasureAgrees`, `KemAgreesFor K`, `KemLenAgrees K`),
the value law of `usize::div_ceil` at divisor 32 (`DivCeilValue`, which makes a fresh decoder's
`needed` small) and the three size shapes the receive records carry, **every one of the twelve
state constructors has a state and a model state satisfying `StateRefines`, `ct1_bounded`,
`decoders_bounded`, `hepoch` and `EncodersLive` at once** (`twelve_states`), and that for each of
the six state and message-type pairs in which `Model.Braid.receive` feeds a chunk to a decoder
there is a message satisfying `MsgRefines` and `HonestChunk` (`six_receive_witnesses`).  It also shows
that the states `Braid::initiator` and `Braid::responder` build satisfy the state-level hypotheses
(`initiator_refines`, `responder_refines`), so `hrel` holds of an honest fresh state and not only of
a state built to satisfy it.

The witnesses are built from the agreements, so they are as satisfiable as the agreements are:
the real key pairs and encapsulation states come from the `generate` and `encapsulate1` clauses of
`KemAgreesFor`, the encoders and decoders from the two clauses of `ErasureAgrees`.  Nothing is
assumed about a state beyond that.  `UnitSatisfiabilityBraidAgreements.lean` shows that the KEM and
KDF agreements are jointly satisfiable; `ErasureAgrees` is the one hypothesis here that no module
discharges without compiler trust (`UnitSatisfiabilityErasureAgrees.lean` has its encoder half).

## What it does not show

* It does not show that a send or a receive keeps `ct1_bounded`, `decoders_bounded`,
  `EncodersLive` or `hepoch`.  The witnesses show single-step non-vacuity, not that a run stays
  inside the hypotheses.
* It does not show that `MsgRefines` and `HonestChunk` hold of a message a peer sends.  `MsgRefines`
  holds of a real chunk of any content when the decoder needs at least one chunk, so `HonestChunk`
  is the only hypothesis that excludes a spliced stream.
* A decoder restored by `Decoder::from_bytes` that holds chunks of no common message refines no model
  decoder, so the refinement theorems apply to states reachable from a fresh Braid and to restored
  states equal to such a state.
-/

open Aeneas Aeneas.Std Result
open tacenta_session_unit

namespace Tacenta.UnitSatisfiabilityBraidStates

open Tacenta.UnitSatisfiabilityJoint
open Tacenta.UnitSatisfiabilityBraidAgreements
open Tacenta.SessionUnitBraidT3
open tacenta_session_unit.tacenta_braid (State Auth Msg MsgType)

/-! ## Small constructions -/

/-- Any natural number that fits 32 bits is the value of a `usize` (on either platform width). -/
theorem usize_exists (n : ℕ) (h : n ≤ 2 ^ 32 - 1) : ∃ v : Usize, v.val = n := by
  have h1 := usize_max_ge n h
  have hb : n < 2 ^ UScalarTy.Usize.numBits := by scalar_tac
  exact ⟨Usize.ofNatCore n hb, Usize.ofNatCore_val_eq hb⟩

/-- A byte string as a slice, for strings that fit. -/
def sliceOfBytes (l : Bytes) (h : l.length ≤ Usize.max) : Slice Std.U8 :=
  ⟨bytesOf l, by simpa [bytesOf] using h⟩

theorem sliceOf_sliceOfBytes (l : Bytes) (h : l.length ≤ Usize.max) :
    sliceOf (sliceOfBytes l h) = l := map_u8_bytesOf l

def zeros32 : Array Std.U8 32#usize := Array.repeat 32#usize 0#u8

def auth0 : Auth := ⟨zeros32, zeros32⟩

def modelAuth0 : Model.Braid.Auth := AuthOf auth0

/-- `AuthOf` of the zero authenticator is what the model state is told to hold. -/
theorem authOf_auth0 : AuthOf auth0 = modelAuth0 := rfl

/-! ## What a witness for a state is -/

/-- A real state and a model state satisfying every state-level hypothesis of the four
refinement theorems together. -/
def Good (K : Model.Braid.Kem) (s : State) (m : Model.Braid.BraidState) : Prop :=
  StateRefines K s m ∧ Tacenta.SessionUnitBraidT1.State.ct1_bounded s ∧
  Tacenta.SessionUnitBraidT1.State.decoders_bounded s ∧
  (Tacenta.SessionUnitBraidT1.State.epoch_val s).val + 1 < Std.U64.max ∧ EncodersLive m

/-- `Good` unfolds to the state-level hypotheses of the refinement theorems, by name:
`hrel`, `hct1b`, `hdb`, `hepoch` of `Braid.receive_refines` and `hlive` of `Braid.send_refines`.  A
`Good` that dropped a conjunct would make `twelve_states` weaker than the hypotheses it is meant to
satisfy, so this statement is pinned. -/
theorem Good_iff (K : Model.Braid.Kem) (s : State) (m : Model.Braid.BraidState) :
    Good K s m ↔
      (StateRefines K s m ∧ Tacenta.SessionUnitBraidT1.State.ct1_bounded s ∧
        Tacenta.SessionUnitBraidT1.State.decoders_bounded s ∧
        (Tacenta.SessionUnitBraidT1.State.epoch_val s).val + 1 < Std.U64.max ∧
        EncodersLive m) := Iff.rfl

/-- The ingredients every witness draws on, all consequences of the agreements. -/
structure Ingredients (K : Model.Braid.Kem) where
  /-- a fresh real encoder refining the model encoder of the empty message -/
  enc : tacenta_erasure.Encoder
  enc_ref : EncoderRefines enc (Model.Braid.encode [])
  /-- a fresh real decoder of `n` bytes, for each size the Braid builds -/
  dec : ∀ n : ℕ, n ≤ 2097152 → ∃ d : tacenta_erasure.Decoder,
    DecoderRefines d (Model.Braid.Decoder.new n) ∧ d.needed.val ≤ 65536
  /-- a real key pair refining some `dk` and `ekVector` -/
  kp : tacenta_kem.IncrementalKeyPair
  dk : Bytes
  ekVector : Bytes
  kp_fresh : FreshKeyPairRefines K kp dk ekVector
  /-- a real encapsulation state refining some seed and secret -/
  es : tacenta_kem.EncapsState
  es_seed : Bytes
  es_secret : Bytes
  es_ref : EncapsRefines K es es_seed es_secret
  es_seed_len : es_seed.length = 32

def totalRng_crc : rand_core_1.CryptoRng Unit := ⟨⟩

/-- Every ingredient exists, from the hypotheses the theorems already take plus the value law of
`div_ceil`.  The key pair comes from the `generate` clause of `KemAgreesFor` with an RNG that
answers; the encapsulation state from its `encapsulate1` clause with a 64-byte header. -/
theorem ingredients (K : Model.Braid.Kem) (hea : ErasureAgrees) (hka : KemAgreesFor K)
    (hdiv : Tacenta.SessionUnitDecoderBound.DivCeilValue) : Nonempty (Ingredients K) := by
  -- the encoder: ErasureAgrees, first clause, at the empty slice
  obtain ⟨enc, -, henc⟩ := hea.1 (Slice.new Std.U8)
  have henc' : EncoderRefines enc (Model.Braid.encode []) := by
    simpa [sliceOf, Slice.new] using henc
  -- the decoders: ErasureAgrees, second clause, at the size, plus the `div_ceil` law
  have hdec : ∀ n : ℕ, n ≤ 2097152 → ∃ d : tacenta_erasure.Decoder,
      DecoderRefines d (Model.Braid.Decoder.new n) ∧ d.needed.val ≤ 65536 := by
    intro n hn
    obtain ⟨v, hv⟩ := usize_exists n (by omega)
    obtain ⟨d, hd, hdr⟩ := hea.2 v
    obtain ⟨d', hd', hneed⟩ := Tacenta.SessionUnitDecoderBound.new_needed_le hdiv v (by omega)
    rw [hd] at hd'
    cases hd'
    refine ⟨d, ?_, hneed⟩
    rw [hv] at hdr
    exact hdr
  -- the key pair
  obtain ⟨kp, rng', rand, hgen, ⟨h, hh, hhv⟩, ⟨v, hv, hvv⟩, hdec'⟩ :=
    hka.1 totalRngCore totalRng_crc () (fun _ _ => ⟨_, rfl⟩)
  have hfresh : FreshKeyPairRefines K kp (K.keyGen rand).1 (K.keyGen rand).2.2 :=
    ⟨hdec', ⟨v, hv, hvv⟩, ⟨h, (K.keyGen rand).2.1, hh, hhv⟩⟩
  -- the encapsulation state, from the header of that key pair if it has the right length, and
  -- otherwise from the all-zero 64-byte header
  obtain ⟨es, ct1raw, ssraw, rng'', rand', -, hes⟩ :=
    hka.2 totalRngCore totalRng_crc
      (sliceOfBytes (List.replicate 64 0) (by simp; exact le64)) ()
      (fun _ _ => ⟨_, rfl⟩) (by simp [sliceOfBytes, bytesOf, Model.Braid.headerSize])
  have hsl : sliceOf (sliceOfBytes (List.replicate 64 0) (by simp; exact le64)) =
      List.replicate 32 0 ++ List.replicate 32 0 := by
    rw [sliceOf_sliceOfBytes]
    simp
  obtain ⟨-, -, hct2⟩ := hes (List.replicate 32 0) (List.replicate 32 0) (by simp) hsl
  exact ⟨Ingredients.mk enc henc' hdec kp _ _ hfresh es (List.replicate 32 0)
    ((K.encaps1 rand' (List.replicate 32 0) (List.replicate 32 0)).1)
    (fun ekVector hl => hct2 ekVector hl) (by simp)⟩


/-! ## Sizes -/

theorem sizes_le {K : Model.Braid.Kem} (hlens : KemLenAgrees K)
    (hek : Tacenta.SessionUnitBraidT1.EkVectorLenTotal)
    (hct1 : Tacenta.SessionUnitBraidT1.Ct1LenTotal)
    (hct2 : Tacenta.SessionUnitBraidT1.Ct2LenTotal) :
    K.ekSize ≤ 4096 ∧ K.ct1Size ≤ 4096 ∧ K.ct2Size ≤ 4096 := by
  obtain ⟨-, ⟨v1, h1, e1⟩, ⟨v2, h2, e2⟩, ⟨v3, h3, e3⟩⟩ := hlens
  obtain ⟨w1, g1, f1⟩ := hek
  obtain ⟨w2, g2, f2⟩ := hct1
  obtain ⟨w3, g3, f3⟩ := hct2
  rw [g1] at h1; rw [g2] at h2; rw [g3] at h3
  cases h1; cases h2; cases h3
  exact ⟨by omega, by omega, by omega⟩

/-- The model decoder for `n` bytes holds no chunk. -/
theorem decNew_chunks (n : ℕ) : (Model.Braid.Decoder.new n).chunks = [] := rfl
theorem decNew_size (n : ℕ) : (Model.Braid.Decoder.new n).size = n := rfl

/-- The constructor of a real state, as a number. -/
def stateTag : State → ℕ
  | .KeysUnsampled .. => 0
  | .KeysSampled .. => 1
  | .HeaderSent .. => 2
  | .Ct1Received .. => 3
  | .EkSentCt1Received .. => 4
  | .NoHeaderReceived .. => 5
  | .HeaderReceived .. => 6
  | .Ct1Sampled .. => 7
  | .EkReceivedCt1Sampled .. => 8
  | .Ct1Acknowledged .. => 9
  | .Ct2Sampled .. => 10
  | .Failed => 11

/-! ## One witness per state constructor -/

section Witnesses

variable {K : Model.Braid.Kem}

/-- The shared bookkeeping of every witness: epoch `1`, an encoder that has emitted nothing, and
the arithmetic of the epoch headroom. -/
theorem epoch_one_headroom : (1#u64 : Std.U64).val + 1 < Std.U64.max := by
  scalar_tac

theorem live_encode (m : Bytes) : (Model.Braid.encode m).next < 65536 := by
  simp [Model.Braid.encode]

theorem good_keysUnsampled : Good K (State.KeysUnsampled 1#u64 auth0) (.keysUnsampled 1 modelAuth0) := by
  refine ⟨⟨rfl, rfl⟩, trivial, trivial, ?_, ?_⟩
  · simpa [Tacenta.SessionUnitBraidT1.State.epoch_val] using epoch_one_headroom
  · intro e h; simp [EncoderOf] at h

theorem good_failed : Good K State.Failed .failed := by
  refine ⟨trivial, trivial, trivial, ?_, ?_⟩
  · simp only [Tacenta.SessionUnitBraidT1.State.epoch_val]; scalar_tac
  · intro e h; simp [EncoderOf] at h

theorem good_keysSampled (I : Ingredients K) :
    Good K (State.KeysSampled 1#u64 auth0 I.kp I.enc)
      (.keysSampled 1 modelAuth0 I.dk I.ekVector (Model.Braid.encode [])) := by
  refine ⟨⟨rfl, rfl, I.kp_fresh, I.enc_ref⟩, trivial, trivial, ?_, ?_⟩
  · simpa [Tacenta.SessionUnitBraidT1.State.epoch_val] using epoch_one_headroom
  · intro e h
    simp only [EncoderOf, Option.some.injEq] at h
    subst h; exact live_encode _

theorem good_headerSent (I : Ingredients K) (hlens : KemLenAgrees K)
    (hek : Tacenta.SessionUnitBraidT1.EkVectorLenTotal)
    (hct1 : Tacenta.SessionUnitBraidT1.Ct1LenTotal)
    (hct2 : Tacenta.SessionUnitBraidT1.Ct2LenTotal) :
    ∃ (s : State) (m : Model.Braid.BraidState), Good K s m ∧ stateTag s = 2 := by
  obtain ⟨h1, h2, h3⟩ := sizes_le hlens hek hct1 hct2
  obtain ⟨d, hd, hneed⟩ := I.dec K.ct1Size (by omega)
  refine ⟨State.HeaderSent 1#u64 auth0 I.kp d I.enc,
    .headerSent 1 modelAuth0 I.dk (Model.Braid.Decoder.new K.ct1Size) (Model.Braid.encode []),
    ⟨⟨rfl, rfl, I.kp_fresh.1, hd, rfl, I.enc_ref⟩, trivial, ?_, ?_, ?_⟩, rfl⟩
  · exact hneed
  · simpa [Tacenta.SessionUnitBraidT1.State.epoch_val] using epoch_one_headroom
  · intro e h
    simp only [EncoderOf, Option.some.injEq] at h
    subst h; exact live_encode _


/-- The six model states in which `Model.Braid.receive` feeds a chunk to a decoder, each with the
decoder it holds fresh and sized `n`: the data every receive witness below is built from. -/
theorem decoderOf_len (n : ℕ) : (Model.Braid.Decoder.new n).size = n ∧
    (Model.Braid.Decoder.new n).chunks = [] := ⟨rfl, rfl⟩

theorem good_ct1Received (I : Ingredients K) (hlens : KemLenAgrees K)
    (hek : Tacenta.SessionUnitBraidT1.EkVectorLenTotal)
    (hct1 : Tacenta.SessionUnitBraidT1.Ct1LenTotal)
    (hct2 : Tacenta.SessionUnitBraidT1.Ct2LenTotal) :
    ∃ (s : State) (m : Model.Braid.BraidState), Good K s m ∧ stateTag s = 3 := by
  obtain ⟨h1, h2, h3⟩ := sizes_le hlens hek hct1 hct2
  have hl : (List.replicate K.ct1Size (0 : UInt8)).length ≤ Usize.max := by
    simp; exact usize_max_ge _ (by omega)
  refine ⟨State.Ct1Received 1#u64 auth0 I.kp (vecOfBytes (List.replicate K.ct1Size 0) hl) I.enc,
    .ct1Received 1 modelAuth0 I.dk (List.replicate K.ct1Size 0) (Model.Braid.encode []),
    ⟨⟨rfl, rfl, I.kp_fresh.1, vecOf_vecOfBytes _ hl, by simp, I.enc_ref⟩, ?_, trivial, ?_, ?_⟩, rfl⟩
  · show (vecOfBytes _ hl).length ≤ 4096
    rw [length_vecOfBytes]; simpa using h2
  · simpa [Tacenta.SessionUnitBraidT1.State.epoch_val] using epoch_one_headroom
  · intro e h
    simp only [EncoderOf, Option.some.injEq] at h
    subst h; exact live_encode _

theorem good_ekSentCt1Received (I : Ingredients K) (hlens : KemLenAgrees K)
    (hek : Tacenta.SessionUnitBraidT1.EkVectorLenTotal)
    (hct1 : Tacenta.SessionUnitBraidT1.Ct1LenTotal)
    (hct2 : Tacenta.SessionUnitBraidT1.Ct2LenTotal) :
    ∃ (s : State) (m : Model.Braid.BraidState), Good K s m ∧ stateTag s = 4 := by
  obtain ⟨h1, h2, h3⟩ := sizes_le hlens hek hct1 hct2
  have hl : (List.replicate K.ct1Size (0 : UInt8)).length ≤ Usize.max := by
    simp; exact usize_max_ge _ (by omega)
  obtain ⟨d, hd, hneed⟩ := I.dec (K.ct2Size + Model.Braid.macSize) (by simp [Model.Braid.macSize]; omega)
  refine ⟨State.EkSentCt1Received 1#u64 auth0 I.kp (vecOfBytes (List.replicate K.ct1Size 0) hl) d,
    .ekSentCt1Received 1 modelAuth0 I.dk (List.replicate K.ct1Size 0)
      (Model.Braid.Decoder.new (K.ct2Size + Model.Braid.macSize)),
    ⟨⟨rfl, rfl, I.kp_fresh.1, vecOf_vecOfBytes _ hl, by simp, hd, rfl⟩, ?_, hneed, ?_, ?_⟩, rfl⟩
  · show (vecOfBytes _ hl).length ≤ 4096
    rw [length_vecOfBytes]; simpa using h2
  · simpa [Tacenta.SessionUnitBraidT1.State.epoch_val] using epoch_one_headroom
  · intro e h; simp [EncoderOf] at h

theorem good_noHeaderReceived (I : Ingredients K) :
    ∃ (s : State) (m : Model.Braid.BraidState), Good K s m ∧ stateTag s = 5 := by
  obtain ⟨d, hd, hneed⟩ := I.dec (Model.Braid.headerSize + Model.Braid.macSize)
    (by simp [Model.Braid.headerSize, Model.Braid.macSize])
  refine ⟨State.NoHeaderReceived 1#u64 auth0 d,
    .noHeaderReceived 1 modelAuth0 (Model.Braid.Decoder.new (Model.Braid.headerSize + Model.Braid.macSize)),
    ⟨⟨rfl, rfl, hd, rfl⟩, trivial, hneed, ?_, ?_⟩, rfl⟩
  · simpa [Tacenta.SessionUnitBraidT1.State.epoch_val] using epoch_one_headroom
  · intro e h; simp [EncoderOf] at h

theorem good_headerReceived (I : Ingredients K) (hlens : KemLenAgrees K)
    (hek : Tacenta.SessionUnitBraidT1.EkVectorLenTotal)
    (hct1 : Tacenta.SessionUnitBraidT1.Ct1LenTotal)
    (hct2 : Tacenta.SessionUnitBraidT1.Ct2LenTotal) :
    ∃ (s : State) (m : Model.Braid.BraidState), Good K s m ∧ stateTag s = 6 := by
  obtain ⟨h1, h2, h3⟩ := sizes_le hlens hek hct1 hct2
  have hl : (List.replicate 32 (0 : UInt8) ++ List.replicate 32 0).length ≤ Usize.max := by
    simp; exact le64
  obtain ⟨d, hd, hneed⟩ := I.dec K.ekSize (by omega)
  refine ⟨State.HeaderReceived 1#u64 auth0
      (vecOfBytes (List.replicate 32 0 ++ List.replicate 32 0) hl) d,
    .headerReceived 1 modelAuth0 (List.replicate 32 0) (List.replicate 32 0)
      (Model.Braid.Decoder.new K.ekSize),
    ⟨⟨rfl, rfl, vecOf_vecOfBytes _ hl, by simp, by simp, hd, rfl⟩, trivial, hneed, ?_, ?_⟩, rfl⟩
  · simpa [Tacenta.SessionUnitBraidT1.State.epoch_val] using epoch_one_headroom
  · intro e h; simp [EncoderOf] at h

theorem good_ct1Sampled (I : Ingredients K) (hlens : KemLenAgrees K)
    (hek : Tacenta.SessionUnitBraidT1.EkVectorLenTotal)
    (hct1 : Tacenta.SessionUnitBraidT1.Ct1LenTotal)
    (hct2 : Tacenta.SessionUnitBraidT1.Ct2LenTotal) :
    ∃ (s : State) (m : Model.Braid.BraidState), Good K s m ∧ stateTag s = 7 := by
  obtain ⟨h1, h2, h3⟩ := sizes_le hlens hek hct1 hct2
  have hl : (I.es_seed ++ List.replicate 32 (0 : UInt8)).length ≤ Usize.max := by
    simp [I.es_seed_len]; exact le64
  have hl1 : (List.replicate K.ct1Size (0 : UInt8)).length ≤ Usize.max := by
    simp; exact usize_max_ge _ (by omega)
  obtain ⟨d, hd, hneed⟩ := I.dec K.ekSize (by omega)
  refine ⟨State.Ct1Sampled 1#u64 auth0 (vecOfBytes (I.es_seed ++ List.replicate 32 0) hl) I.es
      (vecOfBytes (List.replicate K.ct1Size 0) hl1) I.enc d,
    .ct1Sampled 1 modelAuth0 I.es_seed (List.replicate 32 0) I.es_secret
      (List.replicate K.ct1Size 0) (Model.Braid.encode []) (Model.Braid.Decoder.new K.ekSize),
    ⟨⟨rfl, rfl, vecOf_vecOfBytes _ hl, I.es_seed_len, by simp, I.es_ref,
      vecOf_vecOfBytes _ hl1, I.enc_ref, hd, rfl⟩, ?_, hneed, ?_, ?_⟩, rfl⟩
  · show (vecOfBytes _ hl1).length ≤ 4096
    rw [length_vecOfBytes]; simpa using h2
  · simpa [Tacenta.SessionUnitBraidT1.State.epoch_val] using epoch_one_headroom
  · intro e h
    simp only [EncoderOf, Option.some.injEq] at h
    subst h; exact live_encode _

theorem good_ekReceivedCt1Sampled (I : Ingredients K) (hlens : KemLenAgrees K)
    (hek : Tacenta.SessionUnitBraidT1.EkVectorLenTotal)
    (hct1 : Tacenta.SessionUnitBraidT1.Ct1LenTotal)
    (hct2 : Tacenta.SessionUnitBraidT1.Ct2LenTotal) :
    ∃ (s : State) (m : Model.Braid.BraidState), Good K s m ∧ stateTag s = 8 := by
  obtain ⟨h1, h2, h3⟩ := sizes_le hlens hek hct1 hct2
  have hl1 : (List.replicate K.ct1Size (0 : UInt8)).length ≤ Usize.max := by
    simp; exact usize_max_ge _ (by omega)
  have hl2 : (List.replicate K.ekSize (0 : UInt8)).length ≤ Usize.max := by
    simp; exact usize_max_ge _ (by omega)
  refine ⟨State.EkReceivedCt1Sampled 1#u64 auth0 I.es
      (vecOfBytes (List.replicate K.ct1Size 0) hl1)
      (vecOfBytes (List.replicate K.ekSize 0) hl2) I.enc,
    .ekReceivedCt1Sampled 1 modelAuth0 I.es_secret (List.replicate K.ct1Size 0) I.es_seed
      (List.replicate K.ekSize 0) (Model.Braid.encode []),
    ⟨⟨rfl, rfl, I.es_ref, vecOf_vecOfBytes _ hl1, vecOf_vecOfBytes _ hl2, by simp,
      I.enc_ref⟩, ?_, trivial, ?_, ?_⟩, rfl⟩
  · show (vecOfBytes _ hl1).length ≤ 4096
    rw [length_vecOfBytes]; simpa using h2
  · simpa [Tacenta.SessionUnitBraidT1.State.epoch_val] using epoch_one_headroom
  · intro e h
    simp only [EncoderOf, Option.some.injEq] at h
    subst h; exact live_encode _

theorem good_ct1Acknowledged (I : Ingredients K) (hlens : KemLenAgrees K)
    (hek : Tacenta.SessionUnitBraidT1.EkVectorLenTotal)
    (hct1 : Tacenta.SessionUnitBraidT1.Ct1LenTotal)
    (hct2 : Tacenta.SessionUnitBraidT1.Ct2LenTotal) :
    ∃ (s : State) (m : Model.Braid.BraidState), Good K s m ∧ stateTag s = 9 := by
  obtain ⟨h1, h2, h3⟩ := sizes_le hlens hek hct1 hct2
  have hl : (I.es_seed ++ List.replicate 32 (0 : UInt8)).length ≤ Usize.max := by
    simp [I.es_seed_len]; exact le64
  have hl1 : (List.replicate K.ct1Size (0 : UInt8)).length ≤ Usize.max := by
    simp; exact usize_max_ge _ (by omega)
  obtain ⟨d, hd, hneed⟩ := I.dec K.ekSize (by omega)
  refine ⟨State.Ct1Acknowledged 1#u64 auth0 (vecOfBytes (I.es_seed ++ List.replicate 32 0) hl)
      I.es (vecOfBytes (List.replicate K.ct1Size 0) hl1) d,
    .ct1Acknowledged 1 modelAuth0 I.es_seed (List.replicate 32 0) I.es_secret
      (List.replicate K.ct1Size 0) (Model.Braid.Decoder.new K.ekSize),
    ⟨⟨rfl, rfl, vecOf_vecOfBytes _ hl, I.es_seed_len, by simp, I.es_ref,
      vecOf_vecOfBytes _ hl1, hd, rfl⟩, ?_, hneed, ?_, ?_⟩, rfl⟩
  · show (vecOfBytes _ hl1).length ≤ 4096
    rw [length_vecOfBytes]; simpa using h2
  · simpa [Tacenta.SessionUnitBraidT1.State.epoch_val] using epoch_one_headroom
  · intro e h; simp [EncoderOf] at h

theorem good_ct2Sampled (I : Ingredients K) :
    Good K (State.Ct2Sampled 1#u64 auth0 I.enc) (.ct2Sampled 1 modelAuth0 (Model.Braid.encode [])) := by
  refine ⟨⟨rfl, rfl, I.enc_ref⟩, trivial, trivial, ?_, ?_⟩
  · simpa [Tacenta.SessionUnitBraidT1.State.epoch_val] using epoch_one_headroom
  · intro e h
    simp only [EncoderOf, Option.some.injEq] at h
    subst h; exact live_encode _


/-! ## Messages -/

/-- A real chunk that is the first codeword of the message `src`, from the encoder clause of
`ErasureAgrees`.  Its index is `0`, and it is a codeword of `src` in the sense `MsgRefines`
uses. -/
theorem chunk_exists (hea : ErasureAgrees) (src : Bytes) (h : src.length ≤ Usize.max) :
    ∃ c : tacenta_erasure.Chunk, c.index.val = 0 ∧ CodewordOf src c := by
  obtain ⟨real, hnew, hrefs⟩ := hea.1 (sliceOfBytes src h)
  have hsim := hrefs.2 1 (by simp [Model.Braid.encode])
  obtain ⟨chunk, real', hn, hidx, -⟩ := hsim
  have hidx0 : chunk.index.val = 0 := by
    simpa [Model.Braid.encode, Model.Braid.Encoder.nextChunk] using hidx
  refine ⟨chunk, hidx0, sliceOfBytes src h, real, sliceOf_sliceOfBytes src h, hnew, ?_⟩
  rw [hidx0]
  exact ⟨real', hn⟩

/-- A message of any type carrying the first codeword of `src` and the epoch `e`, related to the
model message that carries `⟨src, 0⟩`. -/
theorem msg_exists (hea : ErasureAgrees) (ty : MsgType) (mty : Model.Braid.MsgType)
    (hty : MsgTypeRefines ty mty) (E : Std.U64) (src : Bytes) (h : src.length ≤ Usize.max) :
    ∃ (msg : Msg) (mm : Model.Braid.Msg), MsgRefines msg mm ∧ mm.epoch = E.val ∧
      mm.type = mty ∧ mm.data = some ⟨src, 0⟩ := by
  obtain ⟨c, hc0, hcw⟩ := chunk_exists hea src h
  exact ⟨⟨E, ty, some c⟩, ⟨E.val, mty, some ⟨src, 0⟩⟩, ⟨rfl, hty, hc0, hcw⟩, rfl, rfl, rfl⟩

/-- A message with no data: always honest, and related to the model message without data. -/
theorem msg_nodata (ty : MsgType) (mty : Model.Braid.MsgType) (hty : MsgTypeRefines ty mty)
    (E : Std.U64) :
    ∃ (msg : Msg) (mm : Model.Braid.Msg), MsgRefines msg mm ∧ mm.epoch = E.val ∧
      mm.type = mty ∧ mm.data = none :=
  ⟨⟨E, ty, none⟩, ⟨E.val, mty, none⟩, ⟨rfl, hty, trivial⟩, rfl, rfl, rfl⟩

/-! ### `HonestChunk` in the six state and message-type pairs where a chunk reaches a decoder

In each, the model decoder is fresh (no chunk) and sized for the message the chunk carries. -/

variable {e : ℕ} {a : Model.Braid.Auth}

theorem honest_headerSent {dk : Bytes} {enc : Model.Braid.Encoder} {mm : Model.Braid.Msg}
    (n : ℕ) (src : Bytes) (hn : src.length = n) (ht : mm.type = .ct1) (hd : mm.data = some ⟨src, 0⟩) :
    HonestChunk (.headerSent e a dk (Model.Braid.Decoder.new n) enc) mm := by
  subst hn
  intro mc hmc hep
  rw [hd] at hmc; cases hmc
  simp only [ht]
  exact ⟨rfl, by simp [Model.Braid.Decoder.new]⟩

theorem honest_ekSentCt1Received {dk ct1 : Bytes} {mm : Model.Braid.Msg}
    (n : ℕ) (src : Bytes) (hn : src.length = n) (ht : mm.type = .ct2) (hd : mm.data = some ⟨src, 0⟩) :
    HonestChunk (.ekSentCt1Received e a dk ct1 (Model.Braid.Decoder.new n)) mm := by
  subst hn
  intro mc hmc hep
  rw [hd] at hmc; cases hmc
  simp only [ht]
  exact ⟨rfl, by simp [Model.Braid.Decoder.new]⟩

theorem honest_noHeaderReceived {mm : Model.Braid.Msg}
    (n : ℕ) (src : Bytes) (hn : src.length = n) (ht : mm.type = .hdr) (hd : mm.data = some ⟨src, 0⟩) :
    HonestChunk (.noHeaderReceived e a (Model.Braid.Decoder.new n)) mm := by
  subst hn
  intro mc hmc hep
  rw [hd] at hmc; cases hmc
  simp only [ht]
  exact ⟨rfl, by simp [Model.Braid.Decoder.new]⟩

theorem honest_ct1Sampled_ek {ekSeed hek secret ct1 : Bytes} {enc : Model.Braid.Encoder}
    {mm : Model.Braid.Msg} (n : ℕ) (src : Bytes) (hn : src.length = n) (ht : mm.type = .ek) (hd : mm.data = some ⟨src, 0⟩) :
    HonestChunk (.ct1Sampled e a ekSeed hek secret ct1 enc (Model.Braid.Decoder.new n)) mm := by
  subst hn
  intro mc hmc hep
  rw [hd] at hmc; cases hmc
  simp only [ht]
  exact ⟨rfl, by simp [Model.Braid.Decoder.new]⟩

theorem honest_ct1Sampled_ack {ekSeed hek secret ct1 : Bytes} {enc : Model.Braid.Encoder}
    {mm : Model.Braid.Msg} (n : ℕ) (src : Bytes) (hn : src.length = n) (ht : mm.type = .ekCt1Ack) (hd : mm.data = some ⟨src, 0⟩) :
    HonestChunk (.ct1Sampled e a ekSeed hek secret ct1 enc (Model.Braid.Decoder.new n)) mm := by
  subst hn
  intro mc hmc hep
  rw [hd] at hmc; cases hmc
  simp only [ht]
  exact ⟨rfl, by simp [Model.Braid.Decoder.new]⟩

theorem honest_ct1Acknowledged {ekSeed hek secret ct1 : Bytes} {mm : Model.Braid.Msg}
    (n : ℕ) (src : Bytes) (hn : src.length = n) (ht : mm.type = .ekCt1Ack) (hd : mm.data = some ⟨src, 0⟩) :
    HonestChunk (.ct1Acknowledged e a ekSeed hek secret ct1 (Model.Braid.Decoder.new n)) mm := by
  subst hn
  intro mc hmc hep
  rw [hd] at hmc; cases hmc
  simp only [ht]
  exact ⟨rfl, by simp [Model.Braid.Decoder.new]⟩


/-! ## The receive witnesses -/

/-- The constructor of a model state, as a number (the same numbering as `stateTag`). -/
def modelTag : Model.Braid.BraidState → ℕ
  | .keysUnsampled .. => 0
  | .keysSampled .. => 1
  | .headerSent .. => 2
  | .ct1Received .. => 3
  | .ekSentCt1Received .. => 4
  | .noHeaderReceived .. => 5
  | .headerReceived .. => 6
  | .ct1Sampled .. => 7
  | .ekReceivedCt1Sampled .. => 8
  | .ct1Acknowledged .. => 9
  | .ct2Sampled .. => 10
  | .failed => 11

/-- The six state and message-type pairs in which `Model.Braid.receive` feeds a chunk to a
decoder. -/
def FeedsDecoder : Model.Braid.BraidState → Model.Braid.MsgType → Prop
  | .headerSent .., .ct1 => True
  | .ekSentCt1Received .., .ct2 => True
  | .noHeaderReceived .., .hdr => True
  | .ct1Sampled .., .ek => True
  | .ct1Sampled .., .ekCt1Ack => True
  | .ct1Acknowledged .., .ekCt1Ack => True
  | _, _ => False

/-- A witness for the receive theorems: a state and a message satisfying every state-level and
message-level hypothesis of `step_receive_refines` and `Braid.receive_refines` at once, in a pair
where the chunk reaches a decoder (so `HonestChunk` is not satisfied by its vacuous arm), with the
message in the state's epoch and carrying data. -/
def RecvWitness (K : Model.Braid.Kem) (c : ℕ) (ty : Model.Braid.MsgType) : Prop :=
  ∃ (s : State) (m : Model.Braid.BraidState) (msg : Msg) (mm : Model.Braid.Msg),
    Good K s m ∧ MsgRefines msg mm ∧ HonestChunk m mm ∧ mm.epoch = m.epoch ∧
    (∃ mc, mm.data = some mc) ∧ FeedsDecoder m mm.type ∧ modelTag m = c ∧ mm.type = ty

/-- `RecvWitness` unfolds to: the state-level hypotheses (`Good`), `hmsg`, `hhonest`, a message in the
state's epoch that carries a chunk (so `HonestChunk` is not satisfied by its vacuous arm), in a pair
where `Model.Braid.receive` feeds the chunk to a decoder, in the stated state constructor and
message type.  Pinned, so that a weaker `RecvWitness` is refused. -/
theorem RecvWitness_iff (K : Model.Braid.Kem) (c : ℕ) (ty : Model.Braid.MsgType) :
    RecvWitness K c ty ↔
      ∃ (s : State) (m : Model.Braid.BraidState) (msg : Msg) (mm : Model.Braid.Msg),
        Good K s m ∧ MsgRefines msg mm ∧ HonestChunk m mm ∧ mm.epoch = m.epoch ∧
        (∃ mc, mm.data = some mc) ∧ FeedsDecoder m mm.type ∧ modelTag m = c ∧ mm.type = ty :=
  Iff.rfl

theorem recv_noHeaderReceived (hea : ErasureAgrees) (I : Ingredients K) :
    RecvWitness K 5 .hdr := by
  obtain ⟨d, hd, hneed⟩ := I.dec (Model.Braid.headerSize + Model.Braid.macSize)
    (by simp [Model.Braid.headerSize, Model.Braid.macSize])
  have hl : (List.replicate (Model.Braid.headerSize + Model.Braid.macSize) (0 : UInt8)).length ≤ Usize.max := by
    simp [Model.Braid.headerSize, Model.Braid.macSize]; exact usize_max_ge _ (by norm_num)
  obtain ⟨msg, mm, hrel, hep, hty, hdat⟩ := msg_exists hea .Hdr .hdr trivial 1#u64 _ hl
  refine ⟨State.NoHeaderReceived 1#u64 auth0 d,
    .noHeaderReceived 1 modelAuth0 (Model.Braid.Decoder.new (Model.Braid.headerSize + Model.Braid.macSize)),
    msg, mm, ⟨⟨rfl, rfl, hd, rfl⟩, trivial, hneed, ?_, ?_⟩, hrel,
    honest_noHeaderReceived _ _ (by simp) hty hdat, ?_, ⟨_, hdat⟩, ?_, rfl, hty⟩
  · simpa [Tacenta.SessionUnitBraidT1.State.epoch_val] using epoch_one_headroom
  · intro e h; simp [EncoderOf] at h
  · simpa [Model.Braid.BraidState.epoch] using hep
  · simp [hty, FeedsDecoder]


theorem recv_headerSent (hea : ErasureAgrees) (I : Ingredients K) (hlens : KemLenAgrees K)
    (hek : Tacenta.SessionUnitBraidT1.EkVectorLenTotal)
    (hct1 : Tacenta.SessionUnitBraidT1.Ct1LenTotal)
    (hct2 : Tacenta.SessionUnitBraidT1.Ct2LenTotal) : RecvWitness K 2 .ct1 := by
  obtain ⟨h1, h2, h3⟩ := sizes_le hlens hek hct1 hct2
  obtain ⟨d, hd, hneed⟩ := I.dec K.ct1Size (by omega)
  have hl : (List.replicate K.ct1Size (0 : UInt8)).length ≤ Usize.max := by
    simp; exact usize_max_ge _ (by omega)
  obtain ⟨msg, mm, hrel, hep, hty, hdat⟩ := msg_exists hea .Ct1 .ct1 trivial 1#u64 _ hl
  refine ⟨State.HeaderSent 1#u64 auth0 I.kp d I.enc,
    .headerSent 1 modelAuth0 I.dk (Model.Braid.Decoder.new K.ct1Size) (Model.Braid.encode []),
    msg, mm, ⟨⟨rfl, rfl, I.kp_fresh.1, hd, rfl, I.enc_ref⟩, trivial, hneed, ?_, ?_⟩, hrel,
    honest_headerSent _ _ (by simp) hty hdat, ?_, ⟨_, hdat⟩, ?_, rfl, hty⟩
  · simpa [Tacenta.SessionUnitBraidT1.State.epoch_val] using epoch_one_headroom
  · intro e h
    simp only [EncoderOf, Option.some.injEq] at h
    subst h; exact live_encode _
  · simpa [Model.Braid.BraidState.epoch] using hep
  · simp [hty, FeedsDecoder]

theorem recv_ekSentCt1Received (hea : ErasureAgrees) (I : Ingredients K) (hlens : KemLenAgrees K)
    (hek : Tacenta.SessionUnitBraidT1.EkVectorLenTotal)
    (hct1 : Tacenta.SessionUnitBraidT1.Ct1LenTotal)
    (hct2 : Tacenta.SessionUnitBraidT1.Ct2LenTotal) : RecvWitness K 4 .ct2 := by
  obtain ⟨h1, h2, h3⟩ := sizes_le hlens hek hct1 hct2
  have hl1 : (List.replicate K.ct1Size (0 : UInt8)).length ≤ Usize.max := by
    simp; exact usize_max_ge _ (by omega)
  have hl : (List.replicate (K.ct2Size + Model.Braid.macSize) (0 : UInt8)).length ≤ Usize.max := by
    simp [Model.Braid.macSize]; exact usize_max_ge _ (by omega)
  obtain ⟨d, hd, hneed⟩ := I.dec (K.ct2Size + Model.Braid.macSize)
    (by simp [Model.Braid.macSize]; omega)
  obtain ⟨msg, mm, hrel, hep, hty, hdat⟩ := msg_exists hea .Ct2 .ct2 trivial 1#u64 _ hl
  refine ⟨State.EkSentCt1Received 1#u64 auth0 I.kp (vecOfBytes (List.replicate K.ct1Size 0) hl1) d,
    .ekSentCt1Received 1 modelAuth0 I.dk (List.replicate K.ct1Size 0)
      (Model.Braid.Decoder.new (K.ct2Size + Model.Braid.macSize)),
    msg, mm, ⟨⟨rfl, rfl, I.kp_fresh.1, vecOf_vecOfBytes _ hl1, by simp, hd, rfl⟩, ?_, hneed, ?_, ?_⟩,
    hrel, honest_ekSentCt1Received _ _ (by simp) hty hdat, ?_, ⟨_, hdat⟩, ?_, rfl, hty⟩
  · show (vecOfBytes _ hl1).length ≤ 4096
    rw [length_vecOfBytes]; simpa using h2
  · simpa [Tacenta.SessionUnitBraidT1.State.epoch_val] using epoch_one_headroom
  · intro e h; simp [EncoderOf] at h
  · simpa [Model.Braid.BraidState.epoch] using hep
  · simp [hty, FeedsDecoder]

theorem recv_ct1Sampled (hea : ErasureAgrees) (I : Ingredients K) (hlens : KemLenAgrees K)
    (hek : Tacenta.SessionUnitBraidT1.EkVectorLenTotal)
    (hct1 : Tacenta.SessionUnitBraidT1.Ct1LenTotal)
    (hct2 : Tacenta.SessionUnitBraidT1.Ct2LenTotal) (ty : MsgType)
    (mty : Model.Braid.MsgType) (hty : MsgTypeRefines ty mty)
    (hfeed : mty = .ek ∨ mty = .ekCt1Ack) : RecvWitness K 7 mty := by
  obtain ⟨h1, h2, h3⟩ := sizes_le hlens hek hct1 hct2
  have hl : (I.es_seed ++ List.replicate 32 (0 : UInt8)).length ≤ Usize.max := by
    simp [I.es_seed_len]; exact le64
  have hl1 : (List.replicate K.ct1Size (0 : UInt8)).length ≤ Usize.max := by
    simp; exact usize_max_ge _ (by omega)
  have hl2 : (List.replicate K.ekSize (0 : UInt8)).length ≤ Usize.max := by
    simp; exact usize_max_ge _ (by omega)
  obtain ⟨d, hd, hneed⟩ := I.dec K.ekSize (by omega)
  obtain ⟨msg, mm, hrel, hep, hmt, hdat⟩ := msg_exists hea ty mty hty 1#u64 _ hl2
  refine ⟨State.Ct1Sampled 1#u64 auth0 (vecOfBytes (I.es_seed ++ List.replicate 32 0) hl) I.es
      (vecOfBytes (List.replicate K.ct1Size 0) hl1) I.enc d,
    .ct1Sampled 1 modelAuth0 I.es_seed (List.replicate 32 0) I.es_secret
      (List.replicate K.ct1Size 0) (Model.Braid.encode []) (Model.Braid.Decoder.new K.ekSize),
    msg, mm, ⟨⟨rfl, rfl, vecOf_vecOfBytes _ hl, I.es_seed_len, by simp, I.es_ref,
      vecOf_vecOfBytes _ hl1, I.enc_ref, hd, rfl⟩, ?_, hneed, ?_, ?_⟩, hrel, ?_, ?_, ⟨_, hdat⟩, ?_, rfl, hmt⟩
  · show (vecOfBytes _ hl1).length ≤ 4096
    rw [length_vecOfBytes]; simpa using h2
  · simpa [Tacenta.SessionUnitBraidT1.State.epoch_val] using epoch_one_headroom
  · intro e h
    simp only [EncoderOf, Option.some.injEq] at h
    subst h; exact live_encode _
  · rcases hfeed with h | h
    · exact honest_ct1Sampled_ek _ _ (by simp) (hmt.trans h) hdat
    · exact honest_ct1Sampled_ack _ _ (by simp) (hmt.trans h) hdat
  · simpa [Model.Braid.BraidState.epoch] using hep
  · rcases hfeed with h | h <;> simp [hmt, h, FeedsDecoder]

theorem recv_ct1Acknowledged (hea : ErasureAgrees) (I : Ingredients K) (hlens : KemLenAgrees K)
    (hek : Tacenta.SessionUnitBraidT1.EkVectorLenTotal)
    (hct1 : Tacenta.SessionUnitBraidT1.Ct1LenTotal)
    (hct2 : Tacenta.SessionUnitBraidT1.Ct2LenTotal) : RecvWitness K 9 .ekCt1Ack := by
  obtain ⟨h1, h2, h3⟩ := sizes_le hlens hek hct1 hct2
  have hl : (I.es_seed ++ List.replicate 32 (0 : UInt8)).length ≤ Usize.max := by
    simp [I.es_seed_len]; exact le64
  have hl1 : (List.replicate K.ct1Size (0 : UInt8)).length ≤ Usize.max := by
    simp; exact usize_max_ge _ (by omega)
  have hl2 : (List.replicate K.ekSize (0 : UInt8)).length ≤ Usize.max := by
    simp; exact usize_max_ge _ (by omega)
  obtain ⟨d, hd, hneed⟩ := I.dec K.ekSize (by omega)
  obtain ⟨msg, mm, hrel, hep, hty, hdat⟩ := msg_exists hea .EkCt1Ack .ekCt1Ack trivial 1#u64 _ hl2
  refine ⟨State.Ct1Acknowledged 1#u64 auth0 (vecOfBytes (I.es_seed ++ List.replicate 32 0) hl)
      I.es (vecOfBytes (List.replicate K.ct1Size 0) hl1) d,
    .ct1Acknowledged 1 modelAuth0 I.es_seed (List.replicate 32 0) I.es_secret
      (List.replicate K.ct1Size 0) (Model.Braid.Decoder.new K.ekSize),
    msg, mm, ⟨⟨rfl, rfl, vecOf_vecOfBytes _ hl, I.es_seed_len, by simp, I.es_ref,
      vecOf_vecOfBytes _ hl1, hd, rfl⟩, ?_, hneed, ?_, ?_⟩, hrel,
    honest_ct1Acknowledged _ _ (by simp) hty hdat, ?_, ⟨_, hdat⟩, ?_, rfl, hty⟩
  · show (vecOfBytes _ hl1).length ≤ 4096
    rw [length_vecOfBytes]; simpa using h2
  · simpa [Tacenta.SessionUnitBraidT1.State.epoch_val] using epoch_one_headroom
  · intro e h; simp [EncoderOf] at h
  · simpa [Model.Braid.BraidState.epoch] using hep
  · simp [hty, FeedsDecoder]


/-! ## The twelve states -/

/-- **Every one of the twelve state constructors has a real state and a model state satisfying
`StateRefines`, `ct1_bounded`, `decoders_bounded`, the epoch headroom `hepoch` and `EncodersLive`
at once**, built from the agreements the theorems take (`ErasureAgrees`, `KemAgreesFor K`,
`KemLenAgrees K`), the value law of `div_ceil`, and the three size bounds the receive records
carry (`EkVectorLenTotal`, `Ct1LenTotal`, `Ct2LenTotal`). -/
theorem twelve_states (hea : ErasureAgrees) (hka : KemAgreesFor K) (hlens : KemLenAgrees K)
    (hdiv : Tacenta.SessionUnitDecoderBound.DivCeilValue)
    (hek : Tacenta.SessionUnitBraidT1.EkVectorLenTotal)
    (hct1 : Tacenta.SessionUnitBraidT1.Ct1LenTotal)
    (hct2 : Tacenta.SessionUnitBraidT1.Ct2LenTotal) :
    ∀ t : ℕ, t < 12 → ∃ (s : State) (m : Model.Braid.BraidState), Good K s m ∧ stateTag s = t := by
  obtain ⟨I⟩ := ingredients K hea hka hdiv
  intro t ht
  have : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 ∨ t = 6 ∨ t = 7 ∨ t = 8 ∨ t = 9 ∨
      t = 10 ∨ t = 11 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, _, good_keysUnsampled, rfl⟩
  · exact ⟨_, _, good_keysSampled I, rfl⟩
  · exact good_headerSent I hlens hek hct1 hct2
  · exact good_ct1Received I hlens hek hct1 hct2
  · exact good_ekSentCt1Received I hlens hek hct1 hct2
  · exact good_noHeaderReceived I
  · exact good_headerReceived I hlens hek hct1 hct2
  · exact good_ct1Sampled I hlens hek hct1 hct2
  · exact good_ekReceivedCt1Sampled I hlens hek hct1 hct2
  · exact good_ct1Acknowledged I hlens hek hct1 hct2
  · exact ⟨_, _, good_ct2Sampled I, rfl⟩
  · exact ⟨_, _, good_failed, rfl⟩

/-- **The six state and message-type pairs where a chunk reaches a decoder each have a witness
for the receive theorems' hypotheses**, in the state's epoch, with data, and not through the
vacuous arm of `HonestChunk`. -/
theorem six_receive_witnesses (hea : ErasureAgrees) (hka : KemAgreesFor K) (hlens : KemLenAgrees K)
    (hdiv : Tacenta.SessionUnitDecoderBound.DivCeilValue)
    (hek : Tacenta.SessionUnitBraidT1.EkVectorLenTotal)
    (hct1 : Tacenta.SessionUnitBraidT1.Ct1LenTotal)
    (hct2 : Tacenta.SessionUnitBraidT1.Ct2LenTotal) :
    RecvWitness K 2 .ct1 ∧ RecvWitness K 4 .ct2 ∧ RecvWitness K 5 .hdr ∧
    RecvWitness K 7 .ek ∧ RecvWitness K 7 .ekCt1Ack ∧ RecvWitness K 9 .ekCt1Ack := by
  obtain ⟨I⟩ := ingredients K hea hka hdiv
  exact ⟨recv_headerSent hea I hlens hek hct1 hct2, recv_ekSentCt1Received hea I hlens hek hct1 hct2,
    recv_noHeaderReceived hea I,
    recv_ct1Sampled hea I hlens hek hct1 hct2 .Ek .ek trivial (Or.inl rfl),
    recv_ct1Sampled hea I hlens hek hct1 hct2 .EkCt1Ack .ekCt1Ack trivial (Or.inr rfl),
    recv_ct1Acknowledged hea I hlens hek hct1 hct2⟩

end Witnesses


/-! ## The states the real constructors build

`Braid::initiator` and `Braid::responder` build the two fresh states of a Braid (`KeysUnsampled`
and `NoHeaderReceived`).  The witnesses above are built by hand for every constructor; these two
theorems show the same for the states the real code produces, against the model's own initial states
`Model.Braid.initAlice` and `Model.Braid.initBob`. -/

open tacenta_session_unit.tacenta_braid (Braid)

variable {K : Model.Braid.Kem}

/-- `Braid::initiator` builds a state that refines the model's initial state of the initiator. -/
theorem initiator_refines (hkdf : BraidHkdfAgrees)
    (hz : Tacenta.SessionUnitBraidT1.ZeroizingArrayRoundTrip) (secret : Slice Std.U8) :
    Braid.initiator secret ⦃ fun b =>
      StateRefines K b.state (Model.Braid.initAlice (sliceOf secret)) ∧
      Tacenta.SessionUnitBraidT1.State.ct1_bounded b.state ∧
      Tacenta.SessionUnitBraidT1.State.decoders_bounded b.state ∧
      (Tacenta.SessionUnitBraidT1.State.epoch_val b.state).val + 1 < Std.U64.max ∧
      EncodersLive (Model.Braid.initAlice (sliceOf secret)) ⦄ := by
  unfold Braid.initiator
  step with Auth.init_refines hkdf hz 1#u64 secret
  refine ⟨?_, trivial, trivial, ?_, ?_⟩
  · simpa [StateRefines, Model.Braid.initAlice] using a_post
  · simp only [Tacenta.SessionUnitBraidT1.State.epoch_val]; scalar_tac
  · intro e h; simp [EncoderOf, Model.Braid.initAlice] at h

/-- `Braid::responder` builds a state that refines the model's initial state of the responder,
given the agreements it takes: the decoder it holds is the one `ErasureAgrees` provides for the
header size, which `KemLenAgrees` fixes at 64 bytes plus the MAC. -/
theorem responder_refines (hea : ErasureAgrees) (hlens : KemLenAgrees K)
    (hkdf : BraidHkdfAgrees) (hz : Tacenta.SessionUnitBraidT1.ZeroizingArrayRoundTrip)
    (hdiv : Tacenta.SessionUnitDecoderBound.DivCeilValue) (secret : Slice Std.U8) :
    Braid.responder secret ⦃ fun b =>
      StateRefines K b.state (Model.Braid.initBob (sliceOf secret)) ∧
      Tacenta.SessionUnitBraidT1.State.ct1_bounded b.state ∧
      Tacenta.SessionUnitBraidT1.State.decoders_bounded b.state ∧
      (Tacenta.SessionUnitBraidT1.State.epoch_val b.state).val + 1 < Std.U64.max ∧
      EncodersLive (Model.Braid.initBob (sliceOf secret)) ⦄ := by
  obtain ⟨⟨hv, hhv, hheaderval⟩, -⟩ := hlens
  unfold Braid.responder
  step with Auth.init_refines hkdf hz 1#u64 secret
  unfold tacenta_braid.hdr_decoder
  rw [hhv]
  simp only [bind_tc_ok]
  have h96 : hv.val + tacenta_braid.MAC_LEN.val ≤ Usize.max := by
    have : tacenta_braid.MAC_LEN.val = 32 := by simp [tacenta_braid.MAC_LEN]
    have h64 : hv.val = 64 := by rw [hheaderval]; rfl
    have : (96 : ℕ) ≤ Usize.max := usize_max_ge 96 (by norm_num)
    omega
  step*
  have hMAC : tacenta_braid.MAC_LEN.val = 32 := by simp [tacenta_braid.MAC_LEN]
  have h64 : hv.val = 64 := by rw [hheaderval]; rfl
  have hxval : x.val = Model.Braid.headerSize + Model.Braid.macSize := by
    simp [Model.Braid.headerSize, Model.Braid.macSize]; omega
  obtain ⟨d, hd, hdr⟩ := hea.2 x
  obtain ⟨d', hd', hneed⟩ := Tacenta.SessionUnitDecoderBound.new_needed_le hdiv x
    (by rw [hxval]; simp [Model.Braid.headerSize, Model.Braid.macSize])
  rw [hd] at hd'; cases hd'
  rw [hd]
  simp only [bind_tc_ok, WP.spec_ok]
  refine ⟨?_, trivial, hneed, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · rfl
    · simpa [Model.Braid.initBob] using a_post
    · rw [hxval] at hdr; simpa [Model.Braid.initBob] using hdr
    · simp [Model.Braid.Decoder.new]
  · simp only [Tacenta.SessionUnitBraidT1.State.epoch_val]; scalar_tac
  · intro e h; simp [EncoderOf, Model.Braid.initBob] at h

end Tacenta.UnitSatisfiabilityBraidStates

/--
info: 'Tacenta.UnitSatisfiabilityBraidStates.ingredients' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kem.EncapsState,
 tacenta_kem.IncrementalKeyPair,
 tacenta_kem.encapsulate1,
 tacenta_kem.encapsulate2,
 rand_core_1.error.Error,
 tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_kem.IncrementalKeyPair.generate,
 tacenta_kem.IncrementalKeyPair.header,
 alloc.vec.Vec.truncate,
 core.num.Usize.div_ceil]
-/
#guard_msgs in
#print axioms Tacenta.UnitSatisfiabilityBraidStates.ingredients

/--
info: 'Tacenta.UnitSatisfiabilityBraidStates.twelve_states' depends on axioms: [propext,
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
 rand_core_1.error.Error,
 tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_kem.IncrementalKeyPair.generate,
 tacenta_kem.IncrementalKeyPair.header,
 alloc.vec.Vec.truncate,
 core.num.Usize.div_ceil]
-/
#guard_msgs in
#print axioms Tacenta.UnitSatisfiabilityBraidStates.twelve_states

/--
info: 'Tacenta.UnitSatisfiabilityBraidStates.six_receive_witnesses' depends on axioms: [propext,
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
 rand_core_1.error.Error,
 tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_kem.IncrementalKeyPair.generate,
 tacenta_kem.IncrementalKeyPair.header,
 alloc.vec.Vec.truncate,
 core.num.Usize.div_ceil]
-/
#guard_msgs in
#print axioms Tacenta.UnitSatisfiabilityBraidStates.six_receive_witnesses

/--
info: 'Tacenta.UnitSatisfiabilityBraidStates.initiator_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kdf.hkdf_sha256,
 tacenta_kem.EncapsState,
 tacenta_kem.IncrementalKeyPair,
 tacenta_kem.encapsulate2,
 zeroize.Zeroizing,
 tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_kem.IncrementalKeyPair.header,
 zeroize.Zeroizing.new,
 Array.Insts.ZeroizeZeroize.zeroize,
 alloc.vec.Vec.truncate,
 core.num.Usize.div_ceil,
 zeroize.Zeroize.Blanket.zeroize,
 zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref]
-/
#guard_msgs in
#print axioms Tacenta.UnitSatisfiabilityBraidStates.initiator_refines

/--
info: 'Tacenta.UnitSatisfiabilityBraidStates.responder_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_kdf.hkdf_sha256,
 tacenta_kem.CT1_LEN,
 tacenta_kem.CT2_LEN,
 tacenta_kem.EK_VECTOR_LEN,
 tacenta_kem.EncapsState,
 tacenta_kem.HEADER_LEN,
 tacenta_kem.IncrementalKeyPair,
 tacenta_kem.encapsulate2,
 zeroize.Zeroizing,
 tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_kem.IncrementalKeyPair.header,
 zeroize.Zeroizing.new,
 Array.Insts.ZeroizeZeroize.zeroize,
 alloc.vec.Vec.truncate,
 core.num.Usize.div_ceil,
 zeroize.Zeroize.Blanket.zeroize,
 zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref]
-/
#guard_msgs in
#print axioms Tacenta.UnitSatisfiabilityBraidStates.responder_refines

/--
info: Tacenta.UnitSatisfiabilityBraidStates.ingredients (K : Model.Braid.Kem) (hea : Tacenta.SessionUnitBraidT3.ErasureAgrees)
  (hka : Tacenta.SessionUnitBraidT3.KemAgreesFor K) (hdiv : Tacenta.SessionUnitDecoderBound.DivCeilValue) :
  Nonempty (Tacenta.UnitSatisfiabilityBraidStates.Ingredients K)
-/
#guard_msgs in
#check Tacenta.UnitSatisfiabilityBraidStates.ingredients

/--
info: Tacenta.UnitSatisfiabilityBraidStates.twelve_states {K : Model.Braid.Kem}
  (hea : Tacenta.SessionUnitBraidT3.ErasureAgrees) (hka : Tacenta.SessionUnitBraidT3.KemAgreesFor K)
  (hlens : Tacenta.SessionUnitBraidT3.KemLenAgrees K) (hdiv : Tacenta.SessionUnitDecoderBound.DivCeilValue)
  (hek : Tacenta.SessionUnitBraidT1.EkVectorLenTotal) (hct1 : Tacenta.SessionUnitBraidT1.Ct1LenTotal)
  (hct2 : Tacenta.SessionUnitBraidT1.Ct2LenTotal) (t : ℕ) :
  t < 12 →
    ∃ s m, Tacenta.UnitSatisfiabilityBraidStates.Good K s m ∧ Tacenta.UnitSatisfiabilityBraidStates.stateTag s = t
-/
#guard_msgs in
#check Tacenta.UnitSatisfiabilityBraidStates.twelve_states

/--
info: Tacenta.UnitSatisfiabilityBraidStates.six_receive_witnesses {K : Model.Braid.Kem}
  (hea : Tacenta.SessionUnitBraidT3.ErasureAgrees) (hka : Tacenta.SessionUnitBraidT3.KemAgreesFor K)
  (hlens : Tacenta.SessionUnitBraidT3.KemLenAgrees K) (hdiv : Tacenta.SessionUnitDecoderBound.DivCeilValue)
  (hek : Tacenta.SessionUnitBraidT1.EkVectorLenTotal) (hct1 : Tacenta.SessionUnitBraidT1.Ct1LenTotal)
  (hct2 : Tacenta.SessionUnitBraidT1.Ct2LenTotal) :
  Tacenta.UnitSatisfiabilityBraidStates.RecvWitness K 2 Model.Braid.MsgType.ct1 ∧
    Tacenta.UnitSatisfiabilityBraidStates.RecvWitness K 4 Model.Braid.MsgType.ct2 ∧
      Tacenta.UnitSatisfiabilityBraidStates.RecvWitness K 5 Model.Braid.MsgType.hdr ∧
        Tacenta.UnitSatisfiabilityBraidStates.RecvWitness K 7 Model.Braid.MsgType.ek ∧
          Tacenta.UnitSatisfiabilityBraidStates.RecvWitness K 7 Model.Braid.MsgType.ekCt1Ack ∧
            Tacenta.UnitSatisfiabilityBraidStates.RecvWitness K 9 Model.Braid.MsgType.ekCt1Ack
-/
#guard_msgs in
#check Tacenta.UnitSatisfiabilityBraidStates.six_receive_witnesses

/--
info: Tacenta.UnitSatisfiabilityBraidStates.initiator_refines {K : Model.Braid.Kem}
  (hkdf : Tacenta.SessionUnitBraidT3.BraidHkdfAgrees) (hz : Tacenta.SessionUnitBraidT1.ZeroizingArrayRoundTrip)
  (secret : Slice U8) :
  tacenta_braid.Braid.initiator secret ⦃ b =>
    Tacenta.SessionUnitBraidT3.StateRefines K b.state
        (Model.Braid.initAlice (Tacenta.SessionUnitBraidT3.sliceOf secret)) ∧
      Tacenta.SessionUnitBraidT1.State.ct1_bounded b.state ∧
        Tacenta.SessionUnitBraidT1.State.decoders_bounded b.state ∧
          ↑(Tacenta.SessionUnitBraidT1.State.epoch_val b.state) + 1 < U64.max ∧
            Tacenta.SessionUnitBraidT3.EncodersLive
              (Model.Braid.initAlice (Tacenta.SessionUnitBraidT3.sliceOf secret)) ⦄
-/
#guard_msgs in
#check Tacenta.UnitSatisfiabilityBraidStates.initiator_refines

/--
info: Tacenta.UnitSatisfiabilityBraidStates.responder_refines {K : Model.Braid.Kem}
  (hea : Tacenta.SessionUnitBraidT3.ErasureAgrees) (hlens : Tacenta.SessionUnitBraidT3.KemLenAgrees K)
  (hkdf : Tacenta.SessionUnitBraidT3.BraidHkdfAgrees) (hz : Tacenta.SessionUnitBraidT1.ZeroizingArrayRoundTrip)
  (hdiv : Tacenta.SessionUnitDecoderBound.DivCeilValue) (secret : Slice U8) :
  tacenta_braid.Braid.responder secret ⦃ b =>
    Tacenta.SessionUnitBraidT3.StateRefines K b.state
        (Model.Braid.initBob (Tacenta.SessionUnitBraidT3.sliceOf secret)) ∧
      Tacenta.SessionUnitBraidT1.State.ct1_bounded b.state ∧
        Tacenta.SessionUnitBraidT1.State.decoders_bounded b.state ∧
          ↑(Tacenta.SessionUnitBraidT1.State.epoch_val b.state) + 1 < U64.max ∧
            Tacenta.SessionUnitBraidT3.EncodersLive (Model.Braid.initBob (Tacenta.SessionUnitBraidT3.sliceOf secret)) ⦄
-/
#guard_msgs in
#check Tacenta.UnitSatisfiabilityBraidStates.responder_refines

/--
info: Tacenta.UnitSatisfiabilityBraidStates.Good_iff (K : Model.Braid.Kem) (s : tacenta_braid.State)
  (m : Model.Braid.BraidState) :
  Tacenta.UnitSatisfiabilityBraidStates.Good K s m ↔
    Tacenta.SessionUnitBraidT3.StateRefines K s m ∧
      Tacenta.SessionUnitBraidT1.State.ct1_bounded s ∧
        Tacenta.SessionUnitBraidT1.State.decoders_bounded s ∧
          ↑(Tacenta.SessionUnitBraidT1.State.epoch_val s) + 1 < U64.max ∧ Tacenta.SessionUnitBraidT3.EncodersLive m
-/
#guard_msgs in
#check Tacenta.UnitSatisfiabilityBraidStates.Good_iff

/--
info: Tacenta.UnitSatisfiabilityBraidStates.RecvWitness_iff (K : Model.Braid.Kem) (c : ℕ) (ty : Model.Braid.MsgType) :
  Tacenta.UnitSatisfiabilityBraidStates.RecvWitness K c ty ↔
    ∃ s m msg mm,
      Tacenta.UnitSatisfiabilityBraidStates.Good K s m ∧
        Tacenta.SessionUnitBraidT3.MsgRefines msg mm ∧
          Tacenta.SessionUnitBraidT3.HonestChunk m mm ∧
            mm.epoch = m.epoch ∧
              (∃ mc, mm.data = some mc) ∧
                Tacenta.UnitSatisfiabilityBraidStates.FeedsDecoder m mm.type ∧
                  Tacenta.UnitSatisfiabilityBraidStates.modelTag m = c ∧ mm.type = ty
-/
#guard_msgs in
#check Tacenta.UnitSatisfiabilityBraidStates.RecvWitness_iff

/--
info: def Tacenta.UnitSatisfiabilityBraidStates.stateTag : tacenta_braid.State → ℕ :=
fun x =>
  match x with
  | tacenta_braid.State.KeysUnsampled a a_1 => 0
  | tacenta_braid.State.KeysSampled a a_1 a_2 a_3 => 1
  | tacenta_braid.State.HeaderSent a a_1 a_2 a_3 a_4 => 2
  | tacenta_braid.State.Ct1Received a a_1 a_2 a_3 a_4 => 3
  | tacenta_braid.State.EkSentCt1Received a a_1 a_2 a_3 a_4 => 4
  | tacenta_braid.State.NoHeaderReceived a a_1 a_2 => 5
  | tacenta_braid.State.HeaderReceived a a_1 a_2 a_3 => 6
  | tacenta_braid.State.Ct1Sampled a a_1 a_2 a_3 a_4 a_5 a_6 => 7
  | tacenta_braid.State.EkReceivedCt1Sampled a a_1 a_2 a_3 a_4 a_5 => 8
  | tacenta_braid.State.Ct1Acknowledged a a_1 a_2 a_3 a_4 a_5 => 9
  | tacenta_braid.State.Ct2Sampled a a_1 a_2 => 10
  | tacenta_braid.State.Failed => 11
-/
#guard_msgs in
#print Tacenta.UnitSatisfiabilityBraidStates.stateTag

/--
info: def Tacenta.UnitSatisfiabilityBraidStates.modelTag : Model.Braid.BraidState → ℕ :=
fun x =>
  match x with
  | Model.Braid.BraidState.keysUnsampled epoch auth => 0
  | Model.Braid.BraidState.keysSampled epoch auth dk ekVector hdrEnc => 1
  | Model.Braid.BraidState.headerSent epoch auth dk ct1Dec ekEnc => 2
  | Model.Braid.BraidState.ct1Received epoch auth dk ct1 ekEnc => 3
  | Model.Braid.BraidState.ekSentCt1Received epoch auth dk ct1 ct2Dec => 4
  | Model.Braid.BraidState.noHeaderReceived epoch auth hdrDec => 5
  | Model.Braid.BraidState.headerReceived epoch auth ekSeed hek ekDec => 6
  | Model.Braid.BraidState.ct1Sampled epoch auth ekSeed hek encapsSecret ct1 ct1Enc ekDec => 7
  | Model.Braid.BraidState.ekReceivedCt1Sampled epoch auth encapsSecret ct1 ekSeed ekVector ct1Enc => 8
  | Model.Braid.BraidState.ct1Acknowledged epoch auth ekSeed hek encapsSecret ct1 ekDec => 9
  | Model.Braid.BraidState.ct2Sampled epoch auth ct2Enc => 10
  | Model.Braid.BraidState.failed => 11
-/
#guard_msgs in
#print Tacenta.UnitSatisfiabilityBraidStates.modelTag

/--
info: def Tacenta.UnitSatisfiabilityBraidStates.FeedsDecoder : Model.Braid.BraidState → Model.Braid.MsgType → Prop :=
fun x x_1 =>
  match x, x_1 with
  | Model.Braid.BraidState.headerSent epoch auth dk ct1Dec ekEnc, Model.Braid.MsgType.ct1 => True
  | Model.Braid.BraidState.ekSentCt1Received epoch auth dk ct1 ct2Dec, Model.Braid.MsgType.ct2 => True
  | Model.Braid.BraidState.noHeaderReceived epoch auth hdrDec, Model.Braid.MsgType.hdr => True
  | Model.Braid.BraidState.ct1Sampled epoch auth ekSeed hek encapsSecret ct1 ct1Enc ekDec, Model.Braid.MsgType.ek =>
    True
  | Model.Braid.BraidState.ct1Sampled epoch auth ekSeed hek encapsSecret ct1 ct1Enc ekDec,
    Model.Braid.MsgType.ekCt1Ack => True
  | Model.Braid.BraidState.ct1Acknowledged epoch auth ekSeed hek encapsSecret ct1 ekDec, Model.Braid.MsgType.ekCt1Ack =>
    True
  | x, x_2 => False
-/
#guard_msgs in
#print Tacenta.UnitSatisfiabilityBraidStates.FeedsDecoder
