import Translation.UnitLifecycleAtomicity
import Translation.UnitLifecycleEstablishResponder

/-!
# UnitLifecycleSizeRule

The message size bound (message-format.md, Message size) at the three public entries, on the eight-leaf unit:
`Session::encrypt` refuses a plaintext longer than `MAX_PLAINTEXT_LEN` (1,048,575 bytes) as its first step, and
`Session::decrypt` and `establish_responder` refuse a frame the size rule refuses as `Decode(TooLong)` as theirs.

* **The rule at the bytes.** `check_frame_size_refuses_iff`: the translated `check_frame_size` returns `Ok` or
  `Err(TooLong)` and nothing else, and refuses exactly when the frame is longer than `MAX_INITIAL_FRAME_LEN`
  (1,050,362) or the ratchet message its framing locates is longer than `MAX_RATCHET_FRAME_LEN` (1,048,710), the
  model's `frameTooLong` (through `UnitLifecycleT3.check_frame_size_refines`). `non_initial_limit`: a frame that
  is not an initial message passes exactly up to `MAX_RATCHET_FRAME_LEN`. `decoded_span`, `decoded_initial_limit`:
  an initial frame the decoder accepts passes exactly when the whole frame is within `MAX_INITIAL_FRAME_LEN` and the
  ratchet message inside it within `MAX_RATCHET_FRAME_LEN`, for every `kem_ciphertext_len` it declares; so
  `nested_too_long_refused`, the wrapper bypass is refused.
* **Exact effects.** `encrypt_size_refusal`, `decrypt_size_refusal`, `establish_responder_size_refusal`: the
  refusal returns the session (or the prekey store, one-time keys and last-resort record included) and the random
  source exactly as given, so nothing is written and nothing is drawn, with no hypothesis about the session, the
  store or the frame beyond its size. `encrypt_size_refusal_refines`, `decrypt_size_refusal_refines`: the model
  refuses with its session and oracle unchanged, and the generated refusal refines that step.
* **Precedence.** `encrypt_on_failed_agreement`, `decrypt_initial_decode_refusal_order`,
  `decrypt_not_a_repeat_order`, `establish_responder_decode_refusal_order`,
  `establish_responder_prekey_lookup_order`: where the size refusal and another refusal both apply, the size
  refusal is the result, and otherwise the other one is, each with no effect.
* **The nested bound on the receiving paths.** `decrypt_nested_too_long_refused`,
  `establish_responder_nested_too_long_refused`: an initial frame whose ratchet message is longer than
  `MAX_RATCHET_FRAME_LEN` is refused with no effect, on every session (a genuine repeat of the establishment
  message included) and every store.
* **The received maximum, under an assumed law.** `ratchet_ok_plaintext_le_max`, `decrypt_ok_plaintext_le_max`,
  `establish_responder_ok_plaintext_le_max`: a plaintext the inner receive, the public `decrypt` or the responder's
  establishment returns is at most `MAX_PLAINTEXT_LEN` bytes when the result refines the model's and the model's
  oracle has the open-length property `Model.Lifecycle.AeadOpenLength`.

## The laws and premises

* `Model.Lifecycle.AeadOpenLength` (assumed): an `input` (ciphertext and 32-byte tag) that the oracle's open accepts
  opens to at most `input.length − 33` bytes, the upper half of the AEAD's successful-open length property (a
  ciphertext of `C` bytes that authenticates opens to between `C − 16` and `C − 1` bytes). It is a premise of the
  three received-maximum results only, and is not shown of the shipping AEAD; the padding measurements are tested
  evidence for it, not a discharge.
* The received-maximum results also take, as a hypothesis, that the call's result refines the model's step
  (`hstep`), which only the T3 refinement results supply, under all their premises; for a repeated initial frame
  no theorem supplies it.
* The refinement results take the session relation and the trace at the call, as every T3 result does.
* No other law: the rule, the effects, the precedence and the nested bound hold for every interpretation of the
  opaque operations.

## Non-vacuity

* The refusals hold for every input past the bound; a frame or plaintext past it is a byte string of the right
  length, which exists at both platform widths (`Usize.max ≥ 2^32 − 1`).
* The received maximum is shown non-vacuous for `decrypt_ok_plaintext_le_max` at the reply's receipt, as consistency
  of its hypotheses, by the joint padded witness of `UnitLifecycleSizeWitness` (a padded toy AEAD meets
  `AeadOpenLength`; the earlier toys open to the input less 1 or less 32 bytes and do not). The shipping AEAD is read,
  not proved, to meet the law; that reading closes nothing. No witness for the other two received-maximum results.

## What it does not show

* that the AEAD has the open-length property: the received maximum is conditional on it;
* a joint witness for the received-maximum results other than `decrypt_ok_plaintext_le_max` at the reply's receipt
  (Non-vacuity, above);
* that every message `encrypt` returns passes the size rule: proved only under `AeadSealBounded` for plaintexts of
  at most `MAX_RATCHET_FRAME_LEN − 150` bytes (`UnitLifecycleEstablishedEncrypt.reply_fits`), and for the first
  message of an establishment under `KemCiphertextLenBound` for plaintexts of at most `MAX_RATCHET_FRAME_LEN −
  65,770` bytes (`first_message_fits`, a helper: the first-message routes take the size rule on the frame instead,
  and are not limited by it);
* the outcome of the reply routes for reply plaintexts of 1,048,561 to 1,048,575 bytes: they take `hfitR`/`hfitS`,
  and the size refusals start above 1,048,575, so no route result covers those fifteen lengths (each single call
  there is still related to the model's step by its own refinement result);
* memory and time per call, allocation failure or abort, and the build profile;
* callers that reach the AEAD, the decoders or the ratchet without going through the three public entries;
* the AEAD, KEM and Diffie-Hellman laws the success results rest on, which stay assumed.
-/

namespace Tacenta.UnitLifecycleSizeRule

open Aeneas Aeneas.Std Result
open tacenta_session_unit
open Tacenta.UnitLifecycleT3 (sliceOf vecOf DhView SessionRefines StepRefines ResultRefines
  check_frame_size_refines check_frame_size_refuses check_frame_size_admits sliceOf_length
  message_type_refines messageTypeOf wire_bytesOf_eq_sliceOf frameTooLong_false_of_le)

/-! ## The size rule on the bytes it reads -/

/-- **`check_frame_size` has two outcomes, and refuses exactly where the model's size rule does.** For every
byte string: it returns `Ok ()` or `Err TooLong` and nothing else, and it refuses exactly when the frame is
longer than `MAX_INITIAL_FRAME_LEN` or the ratchet message its framing locates is longer than
`MAX_RATCHET_FRAME_LEN`. -/
theorem check_frame_size_refuses_iff (bytes : Slice Std.U8) :
    (serialization.check_frame_size bytes = ok (core.result.Result.Ok ()) ∨
      serialization.check_frame_size bytes =
        ok (core.result.Result.Err tacenta_wire.DecodeError.TooLong)) ∧
    (serialization.check_frame_size bytes =
        ok (core.result.Result.Err tacenta_wire.DecodeError.TooLong) ↔
      (Model.Lifecycle.maxInitialFrameLen < bytes.val.length ∨
        ∃ span, Model.Lifecycle.ratchetSpan (sliceOf bytes) = some span ∧
          Model.Lifecycle.maxRatchetFrameLen < span)) := by
  rw [check_frame_size_refines]
  have hlen : (sliceOf bytes).length = bytes.val.length := sliceOf_length bytes
  cases hf : Model.Lifecycle.frameTooLong (sliceOf bytes) with
  | true =>
      refine ⟨Or.inr rfl, ?_⟩
      simp only [if_true, true_iff]
      simp only [Model.Lifecycle.frameTooLong, Bool.or_eq_true, decide_eq_true_eq] at hf
      rcases hf with h | h
      · exact Or.inl (by rw [← hlen]; exact h)
      · right
        cases hs : Model.Lifecycle.ratchetSpan (sliceOf bytes) with
        | none => rw [hs] at h; simp at h
        | some s => rw [hs] at h; exact ⟨s, rfl, by simpa using h⟩
  | false =>
      refine ⟨Or.inl rfl, ?_⟩
      simp only [Bool.false_eq_true, if_false]
      simp only [Model.Lifecycle.frameTooLong, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hf
      constructor
      · intro h; cases h
      · rintro (h | ⟨s, hs, h⟩)
        · exact absurd (by rw [hlen]; exact h) hf.1
        · rw [hs] at hf; simp at hf; omega

/-- **A frame that is not an initial message is admitted exactly up to `MAX_RATCHET_FRAME_LEN`**: of
1,048,710 bytes it passes, of one byte more it is refused, whatever its first two bytes say otherwise. -/
theorem non_initial_limit (bytes : Slice Std.U8) (t : Option serialization.MessageType)
    (ht : serialization.message_type bytes = ok t) (hnot : t ≠ some serialization.MessageType.Initial) :
    serialization.check_frame_size bytes = ok (core.result.Result.Ok ()) ↔
      bytes.val.length ≤ Model.Lifecycle.maxRatchetFrameLen := by
  have hrel := message_type_refines bytes
  rw [ht] at hrel
  have hm : Model.Lifecycle.messageType (sliceOf bytes) ≠ some .initial := by
    rw [← hrel]
    rcases t with _ | ⟨_ | _⟩
    · simp
    · simp [messageTypeOf]
    · exact absurd rfl hnot
  rw [check_frame_size_refines, Tacenta.UnitLifecycleT3.frameTooLong_of_noninitial _ hm, sliceOf_length]
  simp only [Tacenta.UnitLifecycleT3.frameTooLongOf, Bool.false_eq_true, if_false,
    Model.Lifecycle.maxRatchetFrameLen_value]
  by_cases h : bytes.val.length ≤ 1048710
  · have h2 : ¬ 1050362 < bytes.val.length := by omega
    have h3 : ¬ 1048710 < bytes.val.length := by omega
    simp [h, h2, h3]
  · have h3 : 1048710 < bytes.val.length := by omega
    simp [h, h3]

/-- The length of the ratchet message an initial frame the decoder accepts carries is the span the size rule
locates, whatever `kem_ciphertext_len` the frame declared. -/
theorem decoded_span (bytes : Slice Std.U8) (d : tacenta_wire.DecodedInitial)
    (hd : tacenta_wire.decode_initial bytes = ok (core.result.Result.Ok d)) :
    Model.Lifecycle.ratchetSpan (sliceOf bytes) = some d.message.val.length := by
  have h := Tacenta.SessionUnitWireInitialT3.decode_initial_refines bytes
  rw [hd] at h
  simp only [WP.spec_ok] at h
  rw [wire_bytesOf_eq_sliceOf] at h
  rw [Model.Lifecycle.decodeInitial_span _ _ h]
  simp [Tacenta.SessionUnitWireInitialT3.initialOf, Tacenta.SessionUnitWireT3.bytesOf]

/-- **The nested bound, at the bytes: an initial frame the decoder accepts is admitted exactly when the whole
frame is at most `MAX_INITIAL_FRAME_LEN` and the ratchet message inside is at most `MAX_RATCHET_FRAME_LEN`**,
for every `kem_ciphertext_len` the frame declares. So an inner message one byte over the ratchet bound is
refused even inside a frame within the outer bound (the wrapper bypass), and one at the bound is admitted. -/
theorem decoded_initial_limit (bytes : Slice Std.U8) (d : tacenta_wire.DecodedInitial)
    (hd : tacenta_wire.decode_initial bytes = ok (core.result.Result.Ok d)) :
    serialization.check_frame_size bytes = ok (core.result.Result.Ok ()) ↔
      bytes.val.length ≤ Model.Lifecycle.maxInitialFrameLen ∧
        d.message.val.length ≤ Model.Lifecycle.maxRatchetFrameLen := by
  have hs := decoded_span bytes d hd
  rw [check_frame_size_refines]
  simp only [Model.Lifecycle.frameTooLong, hs, sliceOf_length]
  by_cases h1 : Model.Lifecycle.maxInitialFrameLen < bytes.val.length
  · simp [h1]
  · by_cases h2 : Model.Lifecycle.maxRatchetFrameLen < d.message.val.length
    · simp [h1, h2]
    · simp [h1, h2]
      omega

/-- **The wrapper bypass is closed**: an initial frame the decoder accepts, whatever `kem_ciphertext_len` it
declares, whose ratchet message is longer than `MAX_RATCHET_FRAME_LEN` fails `check_frame_size` with
`TooLong`. -/
theorem nested_too_long_refused (bytes : Slice Std.U8) (d : tacenta_wire.DecodedInitial)
    (hd : tacenta_wire.decode_initial bytes = ok (core.result.Result.Ok d))
    (hlong : Model.Lifecycle.maxRatchetFrameLen < d.message.val.length) :
    serialization.check_frame_size bytes =
      ok (core.result.Result.Err tacenta_wire.DecodeError.TooLong) := by
  rcases (check_frame_size_refuses_iff bytes).1 with h | h
  · have := (decoded_initial_limit bytes d hd).mp h
    omega
  · exact h

/-! ## The early refusals: exact effects

Each refusal returns the session (or the prekey store) it was given and the random source as it was: nothing
is written, so there is nothing to persist, and no random value is drawn. No hypothesis about the session, the
store or the message beyond the size: a malformed message, an initial message that is not a repeat, one that
names unknown prekeys or replays a recorded last-resort message, and a session whose agreement has failed are
all included. -/

/-- **`Session::encrypt` refuses a plaintext longer than `MAX_PLAINTEXT_LEN` with no effect.** -/
theorem encrypt_size_refusal {R : Type} (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R)
    (s : lifecycle.Session) (plaintext : Slice Std.U8) (rng : R)
    (hlong : Model.Lifecycle.maxPlaintextLen < plaintext.val.length) :
    lifecycle.Session.encrypt rc crc s plaintext rng =
      ok (core.result.Result.Err lifecycle.Error.PlaintextTooLong, s, rng) :=
  Tacenta.UnitLifecycleAtomicity.encrypt_refuses_long_plaintext rc crc s plaintext rng
    (by simp only [serialization.MAX_PLAINTEXT_LEN, Model.Lifecycle.maxPlaintextLen] at hlong ⊢
        scalar_tac)

/-- **`Session::decrypt` refuses a frame the size rule refuses with no effect**, an ordinary frame and an
initial one alike. -/
theorem decrypt_size_refusal {R : Type} (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R)
    (s : lifecycle.Session) (message : Slice Std.U8) (rng : R)
    (hlong : Model.Lifecycle.frameTooLong (sliceOf message) = true) :
    lifecycle.Session.decrypt rc crc s message rng =
      ok (core.result.Result.Err (lifecycle.Error.Decode tacenta_wire.DecodeError.TooLong), s, rng) :=
  Tacenta.UnitLifecycleAtomicity.decrypt_refuses_long_frame rc crc s message rng
    (check_frame_size_refuses message hlong)

/-- **`establish_responder` refuses a frame the size rule refuses with no effect**: the prekey store (its signed,
one-time and KEM prekeys and its record of last-resort messages) and the random source are returned as they
were. -/
theorem establish_responder_size_refusal {R : Type} (rc : rand_core_1.RngCore R)
    (crc : rand_core_1.CryptoRng R) (our : lifecycle.Identity) (store : lifecycle.PrekeyStore)
    (message : Slice Std.U8) (rng : R)
    (hlong : Model.Lifecycle.frameTooLong (sliceOf message) = true) :
    lifecycle.establish_responder rc crc our store message rng =
      ok (core.result.Result.Err (lifecycle.Error.Decode tacenta_wire.DecodeError.TooLong), store, rng) :=
  Tacenta.UnitLifecycleAtomicity.establish_responder_refuses_long_frame rc crc our store message rng
    (check_frame_size_refuses message hlong)

/-- **The sender's refusal refines the model's**: the model refuses `plaintextTooLong` with its session and
oracle unchanged, and the generated result, session and remaining trace refine that step. -/
theorem encrypt_size_refusal_refines {R : Type} (rc : rand_core_1.RngCore R)
    (crc : rand_core_1.CryptoRng R) (trace : R → List Model.Lifecycle.Key) (dh : DhView)
    (K : Model.Braid.Kem) (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
    (real : lifecycle.Session) (model : Model.Lifecycle.Session) (plaintext : Slice Std.U8) (rng : R)
    (hrel : SessionRefines dh K real model) (htrace : trace rng = oracle.draws)
    (hlong : Model.Lifecycle.maxPlaintextLen < (sliceOf plaintext).length) :
    Model.Lifecycle.encrypt view oracle model (sliceOf plaintext) =
        { session := model, result := .error .plaintextTooLong, oracle := oracle } ∧
      StepRefines trace dh K (core.result.Result.Err lifecycle.Error.PlaintextTooLong, real, rng)
        (Model.Lifecycle.encrypt view oracle model (sliceOf plaintext)) :=
  ⟨(Tacenta.UnitLifecycleT3.encrypt_plaintext_too_long_refines rc crc view oracle real model plaintext rng
      hlong).2,
    (Tacenta.UnitLifecycleT3.encrypt_plaintext_too_long_step_refines rc crc trace dh K view oracle real model
      plaintext rng hrel htrace hlong).2⟩

/-- **The receiver's refusal refines the model's**: the model's `decrypt` refuses `decode tooLong` with its
session and oracle unchanged, and the generated refusal refines that step. -/
theorem decrypt_size_refusal_refines {R : Type} (rc : rand_core_1.RngCore R)
    (crc : rand_core_1.CryptoRng R) (trace : R → List Model.Lifecycle.Key) (dh : DhView)
    (K : Model.Braid.Kem) (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
    (real : lifecycle.Session) (model : Model.Lifecycle.Session) (message : Slice Std.U8) (rng : R)
    (hrel : SessionRefines dh K real model) (htrace : trace rng = oracle.draws)
    (hlong : Model.Lifecycle.frameTooLong (sliceOf message) = true) :
    Model.Lifecycle.decrypt view oracle model (sliceOf message) =
        { session := model, result := .error (.decode .tooLong), oracle := oracle } ∧
      StepRefines trace dh K
        (core.result.Result.Err (lifecycle.Error.Decode tacenta_wire.DecodeError.TooLong), real, rng)
        (Model.Lifecycle.decrypt view oracle model (sliceOf message)) :=
  ⟨(Tacenta.UnitLifecycleT3.decrypt_frame_too_long_refines rc crc view oracle real model message rng
      hlong).2,
    (Tacenta.UnitLifecycleT3.decrypt_frame_too_long_step_refines rc crc trace dh K view oracle real model
      message rng hrel htrace hlong).2⟩

/-! ## Precedence: the size checks come first

The order is observable where the size refusal and another refusal both apply; each theorem below gives the
call's exact result for every input of one such kind, so both arms are covered. -/

/-- **On a session whose agreement has failed, `encrypt` refuses `PlaintextTooLong` above the bound and
`AgreementFailed` at or below it**, with the session and the source unchanged either way. -/
theorem encrypt_on_failed_agreement {R : Type} (rc : rand_core_1.RngCore R)
    (crc : rand_core_1.CryptoRng R) (s : lifecycle.Session) (plaintext : Slice Std.U8) (rng : R)
    (hfailed : tacenta_braid.Braid.failed s.braid = ok true) :
    lifecycle.Session.encrypt rc crc s plaintext rng =
      ok (core.result.Result.Err (if Model.Lifecycle.maxPlaintextLen < plaintext.val.length
          then lifecycle.Error.PlaintextTooLong else lifecycle.Error.AgreementFailed), s, rng) := by
  by_cases hlong : Model.Lifecycle.maxPlaintextLen < plaintext.val.length
  · rw [if_pos hlong]
    exact encrypt_size_refusal rc crc s plaintext rng hlong
  · rw [if_neg hlong]
    exact Tacenta.UnitLifecycleAtomicity.encrypt_refuses_failed_agreement rc crc s plaintext rng
      (by simp only [serialization.MAX_PLAINTEXT_LEN, Model.Lifecycle.maxPlaintextLen] at hlong ⊢
          scalar_tac) hfailed

/-- **An initial frame the decoder refuses is refused by `decrypt` as `TooLong` when the size rule refuses it,
and with the decoder's reason otherwise**, with the session and the source unchanged either way. -/
theorem decrypt_initial_decode_refusal_order {R : Type} (rc : rand_core_1.RngCore R)
    (crc : rand_core_1.CryptoRng R) (s : lifecycle.Session) (message : Slice Std.U8) (rng : R)
    (htype : serialization.message_type message = ok (some serialization.MessageType.Initial))
    (reason : tacenta_wire.DecodeError)
    (hd : tacenta_wire.decode_initial message = ok (core.result.Result.Err reason)) :
    lifecycle.Session.decrypt rc crc s message rng =
      ok (core.result.Result.Err (lifecycle.Error.Decode
        (if Model.Lifecycle.frameTooLong (sliceOf message) then tacenta_wire.DecodeError.TooLong
          else reason)), s, rng) := by
  cases hlong : Model.Lifecycle.frameTooLong (sliceOf message) with
  | true => exact decrypt_size_refusal rc crc s message rng hlong
  | false =>
      simp [lifecycle.Session.decrypt, check_frame_size_admits message hlong, htype, hd]

/-- **An initial frame on a session with no establishment ephemeral is refused by `decrypt` as `TooLong` when
the size rule refuses it, and as `NotARepeatedInitial` otherwise.** -/
theorem decrypt_not_a_repeat_order {R : Type} (rc : rand_core_1.RngCore R)
    (crc : rand_core_1.CryptoRng R) (s : lifecycle.Session) (message : Slice Std.U8) (rng : R)
    (htype : serialization.message_type message = ok (some serialization.MessageType.Initial))
    (d : tacenta_wire.DecodedInitial)
    (hd : tacenta_wire.decode_initial message = ok (core.result.Result.Ok d))
    (hnone : s.established_ephemeral = none) :
    lifecycle.Session.decrypt rc crc s message rng =
      ok (core.result.Result.Err
        (if Model.Lifecycle.frameTooLong (sliceOf message)
          then lifecycle.Error.Decode tacenta_wire.DecodeError.TooLong
          else lifecycle.Error.NotARepeatedInitial), s, rng) := by
  cases hlong : Model.Lifecycle.frameTooLong (sliceOf message) with
  | true => exact decrypt_size_refusal rc crc s message rng hlong
  | false =>
      simp [lifecycle.Session.decrypt, check_frame_size_admits message hlong, htype, hd, hnone]

/-- **A frame the initial-message decoder refuses is refused by `establish_responder` as `TooLong` when the size
rule refuses it, and with the decoder's reason otherwise**, with the store and the source unchanged either
way. -/
theorem establish_responder_decode_refusal_order {R : Type} (rc : rand_core_1.RngCore R)
    (crc : rand_core_1.CryptoRng R) (our : lifecycle.Identity) (store : lifecycle.PrekeyStore)
    (message : Slice Std.U8) (rng : R) (reason : tacenta_wire.DecodeError)
    (hd : tacenta_wire.decode_initial message = ok (core.result.Result.Err reason)) :
    lifecycle.establish_responder rc crc our store message rng =
      ok (core.result.Result.Err (lifecycle.Error.Decode
        (if Model.Lifecycle.frameTooLong (sliceOf message) then tacenta_wire.DecodeError.TooLong
          else reason)), store, rng) := by
  cases hlong : Model.Lifecycle.frameTooLong (sliceOf message) with
  | true => exact establish_responder_size_refusal rc crc our store message rng hlong
  | false =>
      unfold lifecycle.establish_responder
      rw [check_frame_size_admits message hlong, hd]
      rfl

/-- **A decoded initial frame naming a signed prekey the store does not hold is refused by
`establish_responder` as `TooLong` when the size rule refuses it, and with the lookup's refusal otherwise**:
the size rule runs before any prekey is looked up. -/
theorem establish_responder_prekey_lookup_order {R : Type} (rc : rand_core_1.RngCore R)
    (crc : rand_core_1.CryptoRng R) (our : lifecycle.Identity) (store : lifecycle.PrekeyStore)
    (message : Slice Std.U8) (rng : R) (d : tacenta_wire.DecodedInitial)
    (hd : tacenta_wire.decode_initial message = ok (core.result.Result.Ok d)) (e : lifecycle.Error)
    (hs : lifecycle.responder_signed_prekey_secret store d.signed_prekey_id =
      ok (core.result.Result.Err e)) :
    lifecycle.establish_responder rc crc our store message rng =
      ok (core.result.Result.Err
        (if Model.Lifecycle.frameTooLong (sliceOf message)
          then lifecycle.Error.Decode tacenta_wire.DecodeError.TooLong else e), store, rng) := by
  cases hlong : Model.Lifecycle.frameTooLong (sliceOf message) with
  | true => exact establish_responder_size_refusal rc crc our store message rng hlong
  | false =>
      unfold lifecycle.establish_responder
      rw [check_frame_size_admits message hlong, hd]
      simp only [bind_tc_ok, hs, core.result.Result.Insts.CoreOpsTry.branch]
      rfl

/-! ## The nested bound on the receiving paths -/

/-- **`Session::decrypt` refuses an initial frame whose ratchet message is longer than `MAX_RATCHET_FRAME_LEN`,
whatever `kem_ciphertext_len` it declares, with no effect**: on every session, so also when the frame is a
genuine repeat of the session's establishment message and would otherwise reach the repeat path's inner
receive. -/
theorem decrypt_nested_too_long_refused {R : Type} (rc : rand_core_1.RngCore R)
    (crc : rand_core_1.CryptoRng R) (s : lifecycle.Session) (message : Slice Std.U8) (rng : R)
    (d : tacenta_wire.DecodedInitial)
    (hd : tacenta_wire.decode_initial message = ok (core.result.Result.Ok d))
    (hlong : Model.Lifecycle.maxRatchetFrameLen < d.message.val.length) :
    lifecycle.Session.decrypt rc crc s message rng =
      ok (core.result.Result.Err (lifecycle.Error.Decode tacenta_wire.DecodeError.TooLong), s, rng) :=
  Tacenta.UnitLifecycleAtomicity.decrypt_refuses_long_frame rc crc s message rng
    (nested_too_long_refused message d hd hlong)

/-- **`establish_responder` refuses an initial frame whose ratchet message is longer than
`MAX_RATCHET_FRAME_LEN`, whatever `kem_ciphertext_len` it declares, with no effect** on the store or the
source, before any prekey lookup or decapsulation. -/
theorem establish_responder_nested_too_long_refused {R : Type} (rc : rand_core_1.RngCore R)
    (crc : rand_core_1.CryptoRng R) (our : lifecycle.Identity) (store : lifecycle.PrekeyStore)
    (message : Slice Std.U8) (rng : R) (d : tacenta_wire.DecodedInitial)
    (hd : tacenta_wire.decode_initial message = ok (core.result.Result.Ok d))
    (hlong : Model.Lifecycle.maxRatchetFrameLen < d.message.val.length) :
    lifecycle.establish_responder rc crc our store message rng =
      ok (core.result.Result.Err (lifecycle.Error.Decode tacenta_wire.DecodeError.TooLong), store, rng) :=
  Tacenta.UnitLifecycleAtomicity.establish_responder_refuses_long_frame rc crc our store message rng
    (nested_too_long_refused message d hd hlong)

/-! ## The received plaintext maximum, under the open-length law -/

/-- The inner receive on a ratchet message of at most `MAX_RATCHET_FRAME_LEN` bytes returns at most
`MAX_PLAINTEXT_LEN` bytes, when its result refines the model's and the model's oracle has the open-length
property `Model.Lifecycle.AeadOpenLength` (assumed: a premise, not shown of the shipping AEAD). -/
theorem ratchet_ok_plaintext_le_max {R : Type} (trace : R → List Model.Lifecycle.Key) (dh : DhView)
    (K : Model.Braid.Kem) (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
    (model : Model.Lifecycle.Session) (message : Slice Std.U8)
    (output : core.result.Result (alloc.vec.Vec Std.U8) lifecycle.Error × lifecycle.Session × R)
    (plaintext : alloc.vec.Vec Std.U8)
    (hmessage : message.val.length ≤ Model.Lifecycle.maxRatchetFrameLen)
    (hstep : StepRefines trace dh K output
      (Model.Lifecycle.decryptRatchet view oracle model (sliceOf message)))
    (hok : output.1 = core.result.Result.Ok plaintext)
    (hopen : Model.Lifecycle.AeadOpenLength oracle) :
    plaintext.val.length ≤ Model.Lifecycle.maxPlaintextLen := by
  have hres := hstep.result
  rw [hok] at hres
  cases hm : (Model.Lifecycle.decryptRatchet view oracle model (sliceOf message)).result with
  | error reason => rw [hm] at hres; exact hres.elim
  | ok bytes =>
      rw [hm] at hres
      have hb : vecOf plaintext = bytes := hres
      have hl := Model.Lifecycle.decryptRatchet_ok_length view oracle model (sliceOf message) bytes hopen hm
      rw [sliceOf_length, ← hb] at hl
      simp only [vecOf, List.length_map] at hl
      rw [Model.Lifecycle.maxRatchetFrameLen_value] at hmessage
      simp only [Model.Lifecycle.maxPlaintextLen]
      omega

/-- **Every plaintext the public `decrypt` returns is at most `MAX_PLAINTEXT_LEN` bytes**, an ordinary frame and
a repeated initial frame alike, when its result refines the model's and the model's oracle has the
open-length property (`Model.Lifecycle.AeadOpenLength`, assumed). -/
theorem decrypt_ok_plaintext_le_max {R : Type} (trace : R → List Model.Lifecycle.Key) (dh : DhView)
    (K : Model.Braid.Kem) (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
    (model : Model.Lifecycle.Session) (message : Slice Std.U8)
    (output : core.result.Result (alloc.vec.Vec Std.U8) lifecycle.Error × lifecycle.Session × R)
    (plaintext : alloc.vec.Vec Std.U8)
    (hstep : StepRefines trace dh K output
      (Model.Lifecycle.decrypt view oracle model (sliceOf message)))
    (hok : output.1 = core.result.Result.Ok plaintext)
    (hopen : Model.Lifecycle.AeadOpenLength oracle) :
    plaintext.val.length ≤ Model.Lifecycle.maxPlaintextLen := by
  have hres := hstep.result
  rw [hok] at hres
  cases hm : (Model.Lifecycle.decrypt view oracle model (sliceOf message)).result with
  | error reason => rw [hm] at hres; exact hres.elim
  | ok bytes =>
      rw [hm] at hres
      have hb : vecOf plaintext = bytes := hres
      have hl := Model.Lifecycle.decrypt_plaintext_le_max view oracle model (sliceOf message) bytes hopen hm
      rw [← hb] at hl
      simpa [vecOf] using hl

/-- **The plaintext a responder's establishment returns is at most `MAX_PLAINTEXT_LEN` bytes**, under the same
law: the prepared parts carry the size rule's admission, so the inner ratchet message is at most
`MAX_RATCHET_FRAME_LEN` bytes (`decoded_initial_limit`), and the inner receive's plaintext is bounded as in
`ratchet_ok_plaintext_le_max`. -/
theorem establish_responder_ok_plaintext_le_max {R : Type} {our : lifecycle.Identity}
    {store : lifecycle.PrekeyStore} {msg : Slice Std.U8}
    (p : Tacenta.UnitLifecycleEstablishResponder.ResponderPreparedParts our store msg)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView)
    (K : Model.Braid.Kem) (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
    (model : Model.Lifecycle.Session)
    (output : core.result.Result (alloc.vec.Vec Std.U8) lifecycle.Error × lifecycle.Session × R)
    (plaintext : alloc.vec.Vec Std.U8)
    (hstep : StepRefines trace dh K output
      (Model.Lifecycle.decryptRatchet view oracle model (sliceOf p.message)))
    (hok : output.1 = core.result.Result.Ok plaintext)
    (hopen : Model.Lifecycle.AeadOpenLength oracle) :
    plaintext.val.length ≤ Model.Lifecycle.maxPlaintextLen := by
  have hlim := ((decoded_initial_limit msg p.decoded p.hDecode).mp p.hSize).2
  exact ratchet_ok_plaintext_le_max trace dh K view oracle model p.message output plaintext
    (by simpa [Tacenta.UnitLifecycleEstablishResponder.ResponderPreparedParts.message,
      alloc.vec.Vec.deref] using hlim) hstep hok hopen

end Tacenta.UnitLifecycleSizeRule

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
info: 'Tacenta.UnitLifecycleSizeRule.check_frame_size_refuses_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSizeRule.check_frame_size_refuses_iff

/--
info: 'Tacenta.UnitLifecycleSizeRule.non_initial_limit' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSizeRule.non_initial_limit

/--
info: 'Tacenta.UnitLifecycleSizeRule.decoded_span' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSizeRule.decoded_span

/--
info: 'Tacenta.UnitLifecycleSizeRule.decoded_initial_limit' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSizeRule.decoded_initial_limit

/--
info: 'Tacenta.UnitLifecycleSizeRule.nested_too_long_refused' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSizeRule.nested_too_long_refused

/--
info: 'Tacenta.UnitLifecycleSizeRule.encrypt_size_refusal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
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
#print axioms Tacenta.UnitLifecycleSizeRule.encrypt_size_refusal

/--
info: 'Tacenta.UnitLifecycleSizeRule.decrypt_size_refusal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
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
#print axioms Tacenta.UnitLifecycleSizeRule.decrypt_size_refusal

/--
info: 'Tacenta.UnitLifecycleSizeRule.establish_responder_size_refusal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
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
#print axioms Tacenta.UnitLifecycleSizeRule.establish_responder_size_refusal

/--
info: 'Tacenta.UnitLifecycleSizeRule.encrypt_size_refusal_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.tacenta_kem.encapsulate1,
 tacenta_session_unit.tacenta_kem.encapsulate2,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.rand_core_1.error.Error,
 tacenta_session_unit.tacenta_boundary.aead.encrypt,
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
#print axioms Tacenta.UnitLifecycleSizeRule.encrypt_size_refusal_refines

/--
info: 'Tacenta.UnitLifecycleSizeRule.decrypt_size_refusal_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
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
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
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
#print axioms Tacenta.UnitLifecycleSizeRule.decrypt_size_refusal_refines

/--
info: 'Tacenta.UnitLifecycleSizeRule.encrypt_on_failed_agreement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
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
#print axioms Tacenta.UnitLifecycleSizeRule.encrypt_on_failed_agreement

/--
info: 'Tacenta.UnitLifecycleSizeRule.decrypt_initial_decode_refusal_order' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
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
#print axioms Tacenta.UnitLifecycleSizeRule.decrypt_initial_decode_refusal_order

/--
info: 'Tacenta.UnitLifecycleSizeRule.decrypt_not_a_repeat_order' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
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
#print axioms Tacenta.UnitLifecycleSizeRule.decrypt_not_a_repeat_order

/--
info: 'Tacenta.UnitLifecycleSizeRule.establish_responder_decode_refusal_order' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
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
#print axioms Tacenta.UnitLifecycleSizeRule.establish_responder_decode_refusal_order

/--
info: 'Tacenta.UnitLifecycleSizeRule.establish_responder_prekey_lookup_order' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
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
#print axioms Tacenta.UnitLifecycleSizeRule.establish_responder_prekey_lookup_order

/--
info: 'Tacenta.UnitLifecycleSizeRule.decrypt_nested_too_long_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
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
#print axioms Tacenta.UnitLifecycleSizeRule.decrypt_nested_too_long_refused

/--
info: 'Tacenta.UnitLifecycleSizeRule.establish_responder_nested_too_long_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
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
#print axioms Tacenta.UnitLifecycleSizeRule.establish_responder_nested_too_long_refused

/--
info: 'Tacenta.UnitLifecycleSizeRule.ratchet_ok_plaintext_le_max' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.tacenta_kem.encapsulate2,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.header,
 tacenta_session_unit.alloc.vec.Vec.truncate,
 tacenta_session_unit.core.num.Usize.div_ceil]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSizeRule.ratchet_ok_plaintext_le_max

/--
info: 'Tacenta.UnitLifecycleSizeRule.decrypt_ok_plaintext_le_max' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.tacenta_kem.encapsulate2,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.header,
 tacenta_session_unit.alloc.vec.Vec.truncate,
 tacenta_session_unit.core.num.Usize.div_ceil]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleSizeRule.decrypt_ok_plaintext_le_max

/--
info: 'Tacenta.UnitLifecycleSizeRule.establish_responder_ok_plaintext_le_max' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.HEADER_LEN,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.tacenta_kem.encapsulate2,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.dh.is_prime_order_public,
 tacenta_session_unit.tacenta_boundary.kem.KeyPair,
 tacenta_session_unit.tacenta_boundary.kem.decapsulate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.header,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.Pair.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.alloc.vec.Vec.truncate,
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
#print axioms Tacenta.UnitLifecycleSizeRule.establish_responder_ok_plaintext_le_max

/--
info: Tacenta.UnitLifecycleSizeRule.check_frame_size_refuses_iff : ∀ (bytes : Aeneas.Std.Slice Aeneas.Std.U8),
  (tacenta_session_unit.serialization.check_frame_size bytes =
        Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok ()) ∨
      tacenta_session_unit.serialization.check_frame_size bytes =
        Aeneas.Std.Result.ok
          (Aeneas.Std.core.result.Result.Err tacenta_session_unit.tacenta_wire.DecodeError.TooLong)) ∧
    (tacenta_session_unit.serialization.check_frame_size bytes =
        Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Err tacenta_session_unit.tacenta_wire.DecodeError.TooLong) ↔
      Model.Lifecycle.maxInitialFrameLen < (↑bytes).length ∨
        ∃ span,
          Model.Lifecycle.ratchetSpan (Tacenta.UnitLifecycleT3.sliceOf bytes) = some span ∧
            Model.Lifecycle.maxRatchetFrameLen < span)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSizeRule.check_frame_size_refuses_iff

/--
info: Tacenta.UnitLifecycleSizeRule.non_initial_limit : ∀ (bytes : Aeneas.Std.Slice Aeneas.Std.U8)
  (t : Option tacenta_session_unit.serialization.MessageType),
  tacenta_session_unit.serialization.message_type bytes = Aeneas.Std.Result.ok t →
    t ≠ some tacenta_session_unit.serialization.MessageType.Initial →
      (tacenta_session_unit.serialization.check_frame_size bytes =
          Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok ()) ↔
        (↑bytes).length ≤ Model.Lifecycle.maxRatchetFrameLen)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSizeRule.non_initial_limit

/--
info: Tacenta.UnitLifecycleSizeRule.decoded_span : ∀ (bytes : Aeneas.Std.Slice Aeneas.Std.U8)
  (d : tacenta_session_unit.tacenta_wire.DecodedInitial),
  tacenta_session_unit.tacenta_wire.decode_initial bytes = Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok d) →
    Model.Lifecycle.ratchetSpan (Tacenta.UnitLifecycleT3.sliceOf bytes) = some (↑d.message).length
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSizeRule.decoded_span

/--
info: Tacenta.UnitLifecycleSizeRule.decoded_initial_limit : ∀ (bytes : Aeneas.Std.Slice Aeneas.Std.U8)
  (d : tacenta_session_unit.tacenta_wire.DecodedInitial),
  tacenta_session_unit.tacenta_wire.decode_initial bytes = Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok d) →
    (tacenta_session_unit.serialization.check_frame_size bytes =
        Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok ()) ↔
      (↑bytes).length ≤ Model.Lifecycle.maxInitialFrameLen ∧ (↑d.message).length ≤ Model.Lifecycle.maxRatchetFrameLen)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSizeRule.decoded_initial_limit

/--
info: Tacenta.UnitLifecycleSizeRule.nested_too_long_refused : ∀ (bytes : Aeneas.Std.Slice Aeneas.Std.U8)
  (d : tacenta_session_unit.tacenta_wire.DecodedInitial),
  tacenta_session_unit.tacenta_wire.decode_initial bytes = Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok d) →
    Model.Lifecycle.maxRatchetFrameLen < (↑d.message).length →
      tacenta_session_unit.serialization.check_frame_size bytes =
        Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Err tacenta_session_unit.tacenta_wire.DecodeError.TooLong)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSizeRule.nested_too_long_refused

/--
info: @Tacenta.UnitLifecycleSizeRule.encrypt_size_refusal : ∀ {R : Type} (rc : tacenta_session_unit.rand_core_1.RngCore R)
  (crc : tacenta_session_unit.rand_core_1.CryptoRng R) (s : tacenta_session_unit.lifecycle.Session)
  (plaintext : Aeneas.Std.Slice Aeneas.Std.U8) (rng : R),
  Model.Lifecycle.maxPlaintextLen < (↑plaintext).length →
    tacenta_session_unit.lifecycle.Session.encrypt rc crc s plaintext rng =
      Aeneas.Std.Result.ok
        (Aeneas.Std.core.result.Result.Err tacenta_session_unit.lifecycle.Error.PlaintextTooLong, s, rng)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSizeRule.encrypt_size_refusal

/--
info: @Tacenta.UnitLifecycleSizeRule.decrypt_size_refusal : ∀ {R : Type} (rc : tacenta_session_unit.rand_core_1.RngCore R)
  (crc : tacenta_session_unit.rand_core_1.CryptoRng R) (s : tacenta_session_unit.lifecycle.Session)
  (message : Aeneas.Std.Slice Aeneas.Std.U8) (rng : R),
  Model.Lifecycle.frameTooLong (Tacenta.UnitLifecycleT3.sliceOf message) = true →
    tacenta_session_unit.lifecycle.Session.decrypt rc crc s message rng =
      Aeneas.Std.Result.ok
        (Aeneas.Std.core.result.Result.Err
            (tacenta_session_unit.lifecycle.Error.Decode tacenta_session_unit.tacenta_wire.DecodeError.TooLong),
          s, rng)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSizeRule.decrypt_size_refusal

/--
info: @Tacenta.UnitLifecycleSizeRule.establish_responder_size_refusal : ∀ {R : Type}
  (rc : tacenta_session_unit.rand_core_1.RngCore R) (crc : tacenta_session_unit.rand_core_1.CryptoRng R)
  (our : tacenta_session_unit.lifecycle.Identity) (store : tacenta_session_unit.lifecycle.PrekeyStore)
  (message : Aeneas.Std.Slice Aeneas.Std.U8) (rng : R),
  Model.Lifecycle.frameTooLong (Tacenta.UnitLifecycleT3.sliceOf message) = true →
    tacenta_session_unit.lifecycle.establish_responder rc crc our store message rng =
      Aeneas.Std.Result.ok
        (Aeneas.Std.core.result.Result.Err
            (tacenta_session_unit.lifecycle.Error.Decode tacenta_session_unit.tacenta_wire.DecodeError.TooLong),
          store, rng)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSizeRule.establish_responder_size_refusal

/--
info: @Tacenta.UnitLifecycleSizeRule.encrypt_size_refusal_refines : ∀ {R : Type}
  (rc : tacenta_session_unit.rand_core_1.RngCore R) (crc : tacenta_session_unit.rand_core_1.CryptoRng R)
  (trace : R → List Model.Lifecycle.Key) (dh : Tacenta.UnitLifecycleT3.DhView) (K : Model.Braid.Kem)
  (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
  (real : tacenta_session_unit.lifecycle.Session) (model : Model.Lifecycle.Session)
  (plaintext : Aeneas.Std.Slice Aeneas.Std.U8) (rng : R),
  Tacenta.UnitLifecycleT3.SessionRefines dh K real model →
    trace rng = oracle.draws →
      Model.Lifecycle.maxPlaintextLen < List.length (Tacenta.UnitLifecycleT3.sliceOf plaintext) →
        Model.Lifecycle.encrypt view oracle model (Tacenta.UnitLifecycleT3.sliceOf plaintext) =
            { session := model, result := Except.error Model.Lifecycle.Refusal.plaintextTooLong, oracle := oracle } ∧
          Tacenta.UnitLifecycleT3.StepRefines trace dh K
            (Aeneas.Std.core.result.Result.Err tacenta_session_unit.lifecycle.Error.PlaintextTooLong, real, rng)
            (Model.Lifecycle.encrypt view oracle model (Tacenta.UnitLifecycleT3.sliceOf plaintext))
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSizeRule.encrypt_size_refusal_refines

/--
info: @Tacenta.UnitLifecycleSizeRule.decrypt_size_refusal_refines : ∀ {R : Type}
  (rc : tacenta_session_unit.rand_core_1.RngCore R) (crc : tacenta_session_unit.rand_core_1.CryptoRng R)
  (trace : R → List Model.Lifecycle.Key) (dh : Tacenta.UnitLifecycleT3.DhView) (K : Model.Braid.Kem)
  (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
  (real : tacenta_session_unit.lifecycle.Session) (model : Model.Lifecycle.Session)
  (message : Aeneas.Std.Slice Aeneas.Std.U8) (rng : R),
  Tacenta.UnitLifecycleT3.SessionRefines dh K real model →
    trace rng = oracle.draws →
      Model.Lifecycle.frameTooLong (Tacenta.UnitLifecycleT3.sliceOf message) = true →
        Model.Lifecycle.decrypt view oracle model (Tacenta.UnitLifecycleT3.sliceOf message) =
            { session := model,
              result := Except.error (Model.Lifecycle.Refusal.decode Model.Messages.DecodeRefusal.tooLong),
              oracle := oracle } ∧
          Tacenta.UnitLifecycleT3.StepRefines trace dh K
            (Aeneas.Std.core.result.Result.Err
                (tacenta_session_unit.lifecycle.Error.Decode tacenta_session_unit.tacenta_wire.DecodeError.TooLong),
              real, rng)
            (Model.Lifecycle.decrypt view oracle model (Tacenta.UnitLifecycleT3.sliceOf message))
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSizeRule.decrypt_size_refusal_refines

/--
info: @Tacenta.UnitLifecycleSizeRule.encrypt_on_failed_agreement : ∀ {R : Type}
  (rc : tacenta_session_unit.rand_core_1.RngCore R) (crc : tacenta_session_unit.rand_core_1.CryptoRng R)
  (s : tacenta_session_unit.lifecycle.Session) (plaintext : Aeneas.Std.Slice Aeneas.Std.U8) (rng : R),
  s.braid.failed = Aeneas.Std.Result.ok true →
    tacenta_session_unit.lifecycle.Session.encrypt rc crc s plaintext rng =
      Aeneas.Std.Result.ok
        (Aeneas.Std.core.result.Result.Err
            (if Model.Lifecycle.maxPlaintextLen < (↑plaintext).length then
              tacenta_session_unit.lifecycle.Error.PlaintextTooLong
            else tacenta_session_unit.lifecycle.Error.AgreementFailed),
          s, rng)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSizeRule.encrypt_on_failed_agreement

/--
info: @Tacenta.UnitLifecycleSizeRule.decrypt_initial_decode_refusal_order : ∀ {R : Type}
  (rc : tacenta_session_unit.rand_core_1.RngCore R) (crc : tacenta_session_unit.rand_core_1.CryptoRng R)
  (s : tacenta_session_unit.lifecycle.Session) (message : Aeneas.Std.Slice Aeneas.Std.U8) (rng : R),
  tacenta_session_unit.serialization.message_type message =
      Aeneas.Std.Result.ok (some tacenta_session_unit.serialization.MessageType.Initial) →
    ∀ (reason : tacenta_session_unit.tacenta_wire.DecodeError),
      tacenta_session_unit.tacenta_wire.decode_initial message =
          Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Err reason) →
        tacenta_session_unit.lifecycle.Session.decrypt rc crc s message rng =
          Aeneas.Std.Result.ok
            (Aeneas.Std.core.result.Result.Err
                (tacenta_session_unit.lifecycle.Error.Decode
                  (if Model.Lifecycle.frameTooLong (Tacenta.UnitLifecycleT3.sliceOf message) = true then
                    tacenta_session_unit.tacenta_wire.DecodeError.TooLong
                  else reason)),
              s, rng)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSizeRule.decrypt_initial_decode_refusal_order

/--
info: @Tacenta.UnitLifecycleSizeRule.decrypt_not_a_repeat_order : ∀ {R : Type}
  (rc : tacenta_session_unit.rand_core_1.RngCore R) (crc : tacenta_session_unit.rand_core_1.CryptoRng R)
  (s : tacenta_session_unit.lifecycle.Session) (message : Aeneas.Std.Slice Aeneas.Std.U8) (rng : R),
  tacenta_session_unit.serialization.message_type message =
      Aeneas.Std.Result.ok (some tacenta_session_unit.serialization.MessageType.Initial) →
    ∀ (d : tacenta_session_unit.tacenta_wire.DecodedInitial),
      tacenta_session_unit.tacenta_wire.decode_initial message =
          Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok d) →
        s.established_ephemeral = none →
          tacenta_session_unit.lifecycle.Session.decrypt rc crc s message rng =
            Aeneas.Std.Result.ok
              (Aeneas.Std.core.result.Result.Err
                  (if Model.Lifecycle.frameTooLong (Tacenta.UnitLifecycleT3.sliceOf message) = true then
                    tacenta_session_unit.lifecycle.Error.Decode tacenta_session_unit.tacenta_wire.DecodeError.TooLong
                  else tacenta_session_unit.lifecycle.Error.NotARepeatedInitial),
                s, rng)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSizeRule.decrypt_not_a_repeat_order

/--
info: @Tacenta.UnitLifecycleSizeRule.establish_responder_decode_refusal_order : ∀ {R : Type}
  (rc : tacenta_session_unit.rand_core_1.RngCore R) (crc : tacenta_session_unit.rand_core_1.CryptoRng R)
  (our : tacenta_session_unit.lifecycle.Identity) (store : tacenta_session_unit.lifecycle.PrekeyStore)
  (message : Aeneas.Std.Slice Aeneas.Std.U8) (rng : R) (reason : tacenta_session_unit.tacenta_wire.DecodeError),
  tacenta_session_unit.tacenta_wire.decode_initial message =
      Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Err reason) →
    tacenta_session_unit.lifecycle.establish_responder rc crc our store message rng =
      Aeneas.Std.Result.ok
        (Aeneas.Std.core.result.Result.Err
            (tacenta_session_unit.lifecycle.Error.Decode
              (if Model.Lifecycle.frameTooLong (Tacenta.UnitLifecycleT3.sliceOf message) = true then
                tacenta_session_unit.tacenta_wire.DecodeError.TooLong
              else reason)),
          store, rng)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSizeRule.establish_responder_decode_refusal_order

/--
info: @Tacenta.UnitLifecycleSizeRule.establish_responder_prekey_lookup_order : ∀ {R : Type}
  (rc : tacenta_session_unit.rand_core_1.RngCore R) (crc : tacenta_session_unit.rand_core_1.CryptoRng R)
  (our : tacenta_session_unit.lifecycle.Identity) (store : tacenta_session_unit.lifecycle.PrekeyStore)
  (message : Aeneas.Std.Slice Aeneas.Std.U8) (rng : R) (d : tacenta_session_unit.tacenta_wire.DecodedInitial),
  tacenta_session_unit.tacenta_wire.decode_initial message = Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok d) →
    ∀ (e : tacenta_session_unit.lifecycle.Error),
      tacenta_session_unit.lifecycle.responder_signed_prekey_secret store d.signed_prekey_id =
          Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Err e) →
        tacenta_session_unit.lifecycle.establish_responder rc crc our store message rng =
          Aeneas.Std.Result.ok
            (Aeneas.Std.core.result.Result.Err
                (if Model.Lifecycle.frameTooLong (Tacenta.UnitLifecycleT3.sliceOf message) = true then
                  tacenta_session_unit.lifecycle.Error.Decode tacenta_session_unit.tacenta_wire.DecodeError.TooLong
                else e),
              store, rng)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSizeRule.establish_responder_prekey_lookup_order

/--
info: @Tacenta.UnitLifecycleSizeRule.decrypt_nested_too_long_refused : ∀ {R : Type}
  (rc : tacenta_session_unit.rand_core_1.RngCore R) (crc : tacenta_session_unit.rand_core_1.CryptoRng R)
  (s : tacenta_session_unit.lifecycle.Session) (message : Aeneas.Std.Slice Aeneas.Std.U8) (rng : R)
  (d : tacenta_session_unit.tacenta_wire.DecodedInitial),
  tacenta_session_unit.tacenta_wire.decode_initial message = Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok d) →
    Model.Lifecycle.maxRatchetFrameLen < (↑d.message).length →
      tacenta_session_unit.lifecycle.Session.decrypt rc crc s message rng =
        Aeneas.Std.Result.ok
          (Aeneas.Std.core.result.Result.Err
              (tacenta_session_unit.lifecycle.Error.Decode tacenta_session_unit.tacenta_wire.DecodeError.TooLong),
            s, rng)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSizeRule.decrypt_nested_too_long_refused

/--
info: @Tacenta.UnitLifecycleSizeRule.establish_responder_nested_too_long_refused : ∀ {R : Type}
  (rc : tacenta_session_unit.rand_core_1.RngCore R) (crc : tacenta_session_unit.rand_core_1.CryptoRng R)
  (our : tacenta_session_unit.lifecycle.Identity) (store : tacenta_session_unit.lifecycle.PrekeyStore)
  (message : Aeneas.Std.Slice Aeneas.Std.U8) (rng : R) (d : tacenta_session_unit.tacenta_wire.DecodedInitial),
  tacenta_session_unit.tacenta_wire.decode_initial message = Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok d) →
    Model.Lifecycle.maxRatchetFrameLen < (↑d.message).length →
      tacenta_session_unit.lifecycle.establish_responder rc crc our store message rng =
        Aeneas.Std.Result.ok
          (Aeneas.Std.core.result.Result.Err
              (tacenta_session_unit.lifecycle.Error.Decode tacenta_session_unit.tacenta_wire.DecodeError.TooLong),
            store, rng)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSizeRule.establish_responder_nested_too_long_refused

/--
info: @Tacenta.UnitLifecycleSizeRule.ratchet_ok_plaintext_le_max : ∀ {R : Type} (trace : R → List Model.Lifecycle.Key)
  (dh : Tacenta.UnitLifecycleT3.DhView) (K : Model.Braid.Kem) (view : Model.Lifecycle.CodewordView)
  (oracle : Model.Lifecycle.Oracle) (model : Model.Lifecycle.Session) (message : Aeneas.Std.Slice Aeneas.Std.U8)
  (output :
    Aeneas.Std.core.result.Result (Aeneas.Std.alloc.vec.Vec Aeneas.Std.U8) tacenta_session_unit.lifecycle.Error ×
      tacenta_session_unit.lifecycle.Session × R)
  (plaintext : Aeneas.Std.alloc.vec.Vec Aeneas.Std.U8),
  (↑message).length ≤ Model.Lifecycle.maxRatchetFrameLen →
    Tacenta.UnitLifecycleT3.StepRefines trace dh K output
        (Model.Lifecycle.decryptRatchet view oracle model (Tacenta.UnitLifecycleT3.sliceOf message)) →
      output.1 = Aeneas.Std.core.result.Result.Ok plaintext →
        Model.Lifecycle.AeadOpenLength oracle → (↑plaintext).length ≤ Model.Lifecycle.maxPlaintextLen
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSizeRule.ratchet_ok_plaintext_le_max

/--
info: @Tacenta.UnitLifecycleSizeRule.decrypt_ok_plaintext_le_max : ∀ {R : Type} (trace : R → List Model.Lifecycle.Key)
  (dh : Tacenta.UnitLifecycleT3.DhView) (K : Model.Braid.Kem) (view : Model.Lifecycle.CodewordView)
  (oracle : Model.Lifecycle.Oracle) (model : Model.Lifecycle.Session) (message : Aeneas.Std.Slice Aeneas.Std.U8)
  (output :
    Aeneas.Std.core.result.Result (Aeneas.Std.alloc.vec.Vec Aeneas.Std.U8) tacenta_session_unit.lifecycle.Error ×
      tacenta_session_unit.lifecycle.Session × R)
  (plaintext : Aeneas.Std.alloc.vec.Vec Aeneas.Std.U8),
  Tacenta.UnitLifecycleT3.StepRefines trace dh K output
      (Model.Lifecycle.decrypt view oracle model (Tacenta.UnitLifecycleT3.sliceOf message)) →
    output.1 = Aeneas.Std.core.result.Result.Ok plaintext →
      Model.Lifecycle.AeadOpenLength oracle → (↑plaintext).length ≤ Model.Lifecycle.maxPlaintextLen
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSizeRule.decrypt_ok_plaintext_le_max

/--
info: @Tacenta.UnitLifecycleSizeRule.establish_responder_ok_plaintext_le_max : ∀ {R : Type}
  {our : tacenta_session_unit.lifecycle.Identity} {store : tacenta_session_unit.lifecycle.PrekeyStore}
  {msg : Aeneas.Std.Slice Aeneas.Std.U8}
  (p : Tacenta.UnitLifecycleEstablishResponder.ResponderPreparedParts our store msg)
  (trace : R → List Model.Lifecycle.Key) (dh : Tacenta.UnitLifecycleT3.DhView) (K : Model.Braid.Kem)
  (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle) (model : Model.Lifecycle.Session)
  (output :
    Aeneas.Std.core.result.Result (Aeneas.Std.alloc.vec.Vec Aeneas.Std.U8) tacenta_session_unit.lifecycle.Error ×
      tacenta_session_unit.lifecycle.Session × R)
  (plaintext : Aeneas.Std.alloc.vec.Vec Aeneas.Std.U8),
  Tacenta.UnitLifecycleT3.StepRefines trace dh K output
      (Model.Lifecycle.decryptRatchet view oracle model (Tacenta.UnitLifecycleT3.sliceOf p.message)) →
    output.1 = Aeneas.Std.core.result.Result.Ok plaintext →
      Model.Lifecycle.AeadOpenLength oracle → (↑plaintext).length ≤ Model.Lifecycle.maxPlaintextLen
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleSizeRule.establish_responder_ok_plaintext_le_max
