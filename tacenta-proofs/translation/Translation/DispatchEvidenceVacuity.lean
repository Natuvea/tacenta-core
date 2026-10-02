import Translation.UnitLifecycleInitialDispatch

/-!
# Hypotheses of the lifecycle dispatch layer that are false or empty

`UnitLifecycleT3.lean` and `UnitLifecycleInitialDispatch.lean` state the refinement lemmas for the
eight-leaf session unit's `encrypt` and `decrypt` as conditional on hypotheses and on evidence
records. A theorem whose hypothesis nothing satisfies is true and says nothing, and `#print axioms`
does not show it. This module proves that five of those hypotheses and records are false or empty,
each under the conditions stated below (results A to D), and says what one clause of the oracle
record costs inside the model (result E). The results are about hypotheses. None is a statement
about the product.

* **A.** `InitialSameEphemeralEvidence` is false for every `dh`, `oracle`, `real` and `model`
  (`initialSameEphemeralEvidence_false`). It asks the translated `same_ephemeral_agreement` to
  return `true` on every pair of equal byte strings, and it returns `false` on the two empty ones.
  The proof uses no hypothesis and no law.
* **B.** `CodewordViewOf` is false for every view whenever `Encoder::new` returns on two messages
  of one length `n` of at least 33 bytes that agree on their first 32 bytes and differ at byte 32
  (`codewordViewOf_false`). So it is false given `EncoderNewTotal`, a field of the encrypt contract
  records that `UnitSatisfiabilityErasure.encoderNew_iff` shows equivalent to the law `DivCeil32`,
  that `usize::div_ceil` returns at divisor 32 (`codewordViewOf_false_of_encoderNewTotal`, at
  `n = 33`). Its `receive` clause makes the source a function of the codeword, and the two messages
  share their codeword at index 0.
* **C.** `InitialRatchetBraidEvidenceContracts` has no term when the model Braid, with its epoch
  below 2^64, is in one of the six state and message-type pairs for which `Model.Braid.receive`
  feeds a chunk to an existing decoder, and that decoder holds a chunk
  (`record_empty_of_nonempty_decoder` and its six instances). The model Braid reaches the first of
  them in one receive step, from `keysSampled` on a ct1 chunk
  (`keysSampled_receive_ct1_holds_chunk`). The record quantifies over every incoming chunk, and two
  chunks that differ at index 0 cannot both be codewords of the one source the held chunk carries.
* **D.** `InitialRatchetTripleConcreteEvidence` and `InitialRatchetAeadConcreteEvidence` force the
  oracle's `dhPublic` to be constant (the two `forces_constant_dhPublic` results). With the DH codec
  and the oracle's `dhPublic` clause that contradicts `PublicKeyNotConstant`, a statement about the
  real X25519 public-key function that this repository tests and does not prove (the two
  `false_of_publicKeyNotConstant` results).
* **E.** `OracleOf.kemEncapsulateSuccess` makes the model's KEM oracle accept every public key at
  every draw that a trace has, and the translated `encapsulate` never return `Err` while the trace
  has a draw (`oracleOf_kem_oracle_never_refuses`, `oracleOf_kem_call_never_errs`). This is not a
  refutation: `encapsulate` is an opaque constant, and that the shipped function returns `Err` on a
  malformed key is read from `tacenta-core/boundary/src/kem.rs` and tested for a wrong length
  (`GAP-REGISTER.md`, row `E2E-04`).

**Platform width.** No result case-splits on the width of `usize`, and none uses a fact about
`Usize.max` other than the bounds Aeneas proves for the platform constant, which is `U32.max` or
`U64.max` (`Usize.bounds_eq`). `System.Platform.numBits` is an opaque constant of the kernel whose
value is 32 or 64, so a proof that does not choose between the two holds for both.

**What these results do not show.** They do not show that the product is wrong; each says that an
assumption of a Lean theorem is not met. They do not decide `InitialRatchetBraidEvidenceContracts`
for states whose decoder is empty or that are outside the six. Result D rests on
`PublicKeyNotConstant`, which no theorem here proves. They repair nothing: the theorems that take
these hypotheses are listed in `GAP-REGISTER.md`, row `DISPATCH-EVIDENCE-VACUITY`, which also says
what closes the row.
-/

open Aeneas Aeneas.Std Result

namespace Tacenta.DispatchEvidenceVacuity

section SameEphemeral
open tacenta_session_unit
open Tacenta.UnitLifecycleT3

/-! ## A. `InitialSameEphemeralEvidence` is false

`tacenta_session.decode_ec` returns `none` unless its slice has length `ENCODE_EC_LEN`, which is
33, so `lifecycle.same_ephemeral_agreement` returns `false` on two empty byte strings. The Rust
function does the same (`tacenta-core/lifecycle/src/lifecycle.rs`, the `None => return false`
arms). `InitialSameEphemeralEvidence` asks for `true` on every pair of equal byte strings. The
model's `sameEphemeralAgreement` also returns `false` when either agreement is `none`, so the
second conjunct of the definition fails on low-order keys too; that is not proved here. -/

/-- The translated `decode_ec` refuses a byte string of the wrong length. -/
theorem decode_ec_empty :
    tacenta_session.decode_ec ⟨[], by simp⟩ = ok none := by
  unfold tacenta_session.decode_ec
  have : (Slice.len (⟨[], by simp⟩ : Slice Std.U8)) ≠ tacenta_session.ENCODE_EC_LEN := by
    unfold tacenta_session.ENCODE_EC_LEN
    intro h
    have := congrArg UScalar.val h
    simp [Slice.len] at this
  simp [this]

theorem lifecycle_decode_ec_empty :
    decode_ec ⟨[], by simp⟩ = ok none := by
  unfold decode_ec
  rw [decode_ec_empty]
  simp

/-- On two empty byte strings the translated `same_ephemeral_agreement` returns `false`. -/
theorem same_ephemeral_agreement_empty (p : tacenta_boundary.dh.PrivateKey) :
    lifecycle.same_ephemeral_agreement p ⟨[], by simp⟩ ⟨[], by simp⟩ = ok false := by
  unfold lifecycle.same_ephemeral_agreement
  rw [lifecycle_decode_ec_empty]
  simp

/-- `InitialSameEphemeralEvidence` is false for every argument: it asks the translated
`same_ephemeral_agreement` to return `true` on every pair of equal byte strings, and it
returns `false` on the two empty ones. -/
theorem initialSameEphemeralEvidence_false (dh : DhView) (oracle : Model.Lifecycle.Oracle)
    (real : lifecycle.Session) (model : Model.Lifecycle.Session) :
    ¬ InitialSameEphemeralEvidence dh oracle real model := by
  intro h
  let est : alloc.vec.Vec Std.U8 := ⟨[], by simp⟩
  let dec : tacenta_wire.DecodedInitial :=
    { identity := est, ephemeral := est, kem_ciphertext := est, signed_prekey_id := 0#u32,
      one_time_prekey_id := 0#u32, kem_prekey_id := 0#u32, message := est }
  have h1 := (h est dec rfl).1
  have h2 : lifecycle.same_ephemeral_agreement real.ratchet_private est.deref dec.ephemeral.deref =
      ok false := same_ephemeral_agreement_empty real.ratchet_private
  rw [h2] at h1
  have := Result.ok.inj h1
  exact absurd this (by decide)



end SameEphemeral

section CodewordView
open tacenta_session_unit

/-! ## B. `CodewordViewOf` is false

The clause `receive` of `CodewordViewOf` says that for every codeword `chunk` of a source
`source` (`SessionUnitBraidT3.CodewordOf`), the view returns `modelChunkOf source chunk`, which
carries `source`. `CodewordOf` puts no condition on the length of the source. The first chunk
`Encoder::new` stores for a message is the translated inner loop over its first 32 bytes
(`new_loop0_head`, `inner_eq`), and `next_chunk` emits that chunk at index 0 (`next_chunk_first`,
`next_chunk_some`). So two messages that agree on their first 32 bytes have the same codeword at
index 0, and the view cannot return both sources. `SessionUnitBraidT3.lean` explains why its
`DecoderSim` is indexed by the message the decoder is collecting and not quantified over every
chunk with a given index; `IncomingChunkRefines` uses `∃ source` for the same reason, and
`CodewordViewOf.receive` does not. -/

/-- Partial correctness: if `x` returns `ok r`, then `Q r`. -/
def OK {α : Type} (x : Result α) (Q : α → Prop) : Prop := ∀ r, x = ok r → Q r

theorem OK.bind {α β : Type} {x : Result α} {f : α → Result β} {P : α → Prop} {Q : β → Prop}
    (hx : OK x P) (hf : ∀ r, P r → OK (f r) Q) : OK (x >>= f) Q := by
  intro r' h
  cases hxx : x with
  | ok a =>
    rw [hxx] at h
    exact hf a (hx a hxx) r' (by simpa using h)
  | fail e => rw [hxx] at h; simp at h
  | div => rw [hxx] at h; simp at h

theorem OK.ok {α : Type} (a : α) {Q : α → Prop} (h : Q a) : OK (Result.ok a) Q := by
  intro r hr
  have := Result.ok.inj hr
  subst this; exact h

theorem OK.any {α : Type} (x : Result α) : OK x (fun _ => True) := fun _ _ => trivial

theorem loop_OK {α β : Type} (measure : α → Nat) (inv : α → Prop) (post : β → Prop)
    (body : α → Result (ControlFlow α β))
    (hBody : ∀ x, inv x → ∀ r, body x = ok r →
      (∀ y, r = .done y → post y) ∧ (∀ x', r = .cont x' → inv x' ∧ measure x' < measure x)) :
    ∀ x, inv x → ∀ y, loop body x = ok y → post y := by
  suffices h : ∀ n x, measure x = n → inv x → ∀ y, loop body x = ok y → post y from
    fun x hx => h _ x rfl hx
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro x hn hx y hy
    rw [loop] at hy
    cases hbx : body x with
    | ok r =>
      rw [hbx] at hy
      have hq := hBody x hx r hbx
      cases r with
      | done z =>
        simp at hy
        subst hy
        exact hq.1 z rfl
      | cont x' =>
        obtain ⟨hi', hlt⟩ := hq.2 x' rfl
        simp at hy
        exact ih (measure x') (hn ▸ hlt) x' rfl hi' y hy
    | fail e => rw [hbx] at hy; simp at hy
    | div => rw [hbx] at hy; simp at hy

theorem chunk_bytes_eq : tacenta_erasure.CHUNK_BYTES = 32#usize := by
  unfold tacenta_erasure.CHUNK_BYTES; rfl

theorem index_usize_congr (s1 s2 : Slice Std.U8) (i : Usize) (h : s1.val[i.val]? = s2.val[i.val]?) :
    s1.index_usize i = s2.index_usize i := by
  unfold Slice.index_usize
  have h1 : s1[i]? = s1.val[i.val]? := rfl
  have h2 : s2[i]? = s2.val[i.val]? := rfl
  rw [h1, h2, h]

theorem inner_eq (s1 s2 : Slice Std.U8) (hlen : Slice.len s1 = Slice.len s2)
    (hag : ∀ i : Nat, i < 32 → s1.val[i]? = s2.val[i]?) (buf : Array Std.U8 32#usize) :
    tacenta_erasure.Encoder.new_loop0_loop0 s1 buf 0#usize 0#usize =
    tacenta_erasure.Encoder.new_loop0_loop0 s2 buf 0#usize 0#usize := by
  unfold tacenta_erasure.Encoder.new_loop0_loop0
  congr 1
  funext p
  rcases p with ⟨buf1, b1⟩
  simp only []
  unfold tacenta_erasure.Encoder.new_loop0_loop0.body
  by_cases hb : b1 < tacenta_erasure.CHUNK_BYTES
  · rw [if_pos hb, if_pos hb]
    have hb32 : b1.val < 32 := by
      rw [chunk_bytes_eq] at hb
      have := hb
      scalar_tac
    have hmax : (0#usize).val + b1.val ≤ Usize.max := by scalar_tac
    obtain ⟨i, hi, hiv⟩ := Std.WP.spec_imp_exists (Usize.add_spec hmax (x := 0#usize) (y := b1))
    rw [hi]
    simp only [bind_tc_ok]
    rw [hlen]
    by_cases hlt : i < s2.len
    · rw [if_pos hlt, if_pos hlt]
      have : s1.index_usize i = s2.index_usize i :=
        index_usize_congr s1 s2 i (hag i.val (by simp at hiv; omega))
      rw [this]
    · rw [if_neg hlt, if_neg hlt]
  · rw [if_neg hb, if_neg hb]


open Tacenta.SessionUnitRatchetImportInv (bind_eq_ok_inv)
open Tacenta.SessionUnitBraidT3

theorem u8_inj {a b : Std.U8} (h : u8 a = u8 b) : a = b := by
  have ha : a.val < 256 := by scalar_tac
  have hb : b.val < 256 := by scalar_tac
  unfold u8 at h
  have h' := congrArg UInt8.toNat h
  rw [UInt8.toNat_ofNat', UInt8.toNat_ofNat'] at h'
  apply UScalar.eq_of_val_eq
  omega

theorem sliceOf_inj {s1 s2 : Slice Std.U8} (h : sliceOf s1 = sliceOf s2) : s1 = s2 := by
  unfold sliceOf at h
  have hl : s1.val = s2.val :=
    (List.map_injective_iff.mpr (fun a b hab => u8_inj hab)) h
  exact Subtype.ext hl



theorem push_OK {α : Type} (v : alloc.vec.Vec α) (x : α) :
    OK (alloc.vec.Vec.push v x) (fun w => w.val = v.val ++ [x]) := by
  intro w hw
  unfold alloc.vec.Vec.push at hw
  dsimp only [] at hw
  split at hw
  · have := Result.ok.inj hw
    subst this
    simp [List.concat_eq_append]
  · simp at hw

/-- The first chunk the encoder builds, as a function of the message alone. -/
abbrev inner (m : Slice Std.U8) : Result (Array Std.U8 32#usize) :=
  tacenta_erasure.Encoder.new_loop0_loop0 m (Array.repeat 32#usize 0#u8) 0#usize 0#usize

def HeadInv (m : Slice Std.U8) (k : Usize) (c : alloc.vec.Vec (Array Std.U8 32#usize))
    (t : Usize) : Prop :=
  (c.val = [] ∧ t.val = 0) ∨ ∃ b, inner m = ok b ∧ c.val.head? = some b ∧ 0 < k.val

def HeadPost (m : Slice Std.U8) (k : Usize) (v : alloc.vec.Vec (Array Std.U8 32#usize)) : Prop :=
  (k.val = 0 ∧ v.val = []) ∨ ∃ b, inner m = ok b ∧ v.val.head? = some b ∧ 0 < k.val

theorem new_loop0_body_head (m : Slice Std.U8) (k : Usize)
    (c1 : alloc.vec.Vec (Array Std.U8 32#usize)) (t1 : Usize) (hinv : HeadInv m k c1 t1) :
    ∀ r, tacenta_erasure.Encoder.new_loop0.body m k c1 t1 = ok r →
      (∀ y, r = .done y → HeadPost m k y) ∧
      (∀ x', r = .cont x' → HeadInv m k x'.1 x'.2 ∧ k.val - x'.2.val < k.val - t1.val) := by
  intro r hr
  unfold tacenta_erasure.Encoder.new_loop0.body at hr
  by_cases ht : t1 < k
  · rw [if_pos ht] at hr
    obtain ⟨start, hstart, hr⟩ := bind_eq_ok_inv hr
    obtain ⟨buf1, hbuf1, hr⟩ := bind_eq_ok_inv hr
    obtain ⟨c2, hc2, hr⟩ := bind_eq_ok_inv hr
    obtain ⟨t2, ht2, hr⟩ := bind_eq_ok_inv hr
    have hr' := Result.ok.inj hr
    subst hr'
    have htk : t1.val < k.val := by simpa using ht
    have hk : k.val ≤ Usize.max := by scalar_tac
    have hmax : t1.val + 1 ≤ Usize.max := by omega
    obtain ⟨t2', ht2', ht2v⟩ := Std.WP.spec_imp_exists (Usize.add_spec hmax (x := t1) (y := 1#usize))
    rw [ht2'] at ht2
    have ht2eq := Result.ok.inj ht2
    subst ht2eq
    have ht2val : t2'.val = t1.val + 1 := by simpa using ht2v
    have hpush := push_OK c1 buf1 c2 hc2
    refine ⟨fun y h => (by cases h), fun x' h => ?_⟩
    cases h
    refine ⟨?_, by simp only []; omega⟩
    rcases hinv with ⟨hc, h0⟩ | ⟨b, hb, hh, hk0⟩
    · right
      refine ⟨buf1, ?_, ?_, by omega⟩
      · have ht0 : t1 = 0#usize := UScalar.eq_of_val_eq (by simpa using h0)
        subst ht0
        have hz : (0#usize * tacenta_erasure.CHUNK_BYTES) = ok 0#usize := by
          rw [chunk_bytes_eq]
          obtain ⟨z, hz, hzv⟩ := Std.WP.spec_imp_exists
            (Usize.mul_spec (x := 0#usize) (y := 32#usize) (by scalar_tac))
          have : z = 0#usize := UScalar.eq_of_val_eq (by simpa using hzv)
          rw [hz, this]
        rw [hz] at hstart
        have hs := Result.ok.inj hstart
        subst hs
        exact hbuf1
      · simp only [] at hpush ⊢
        rw [hpush, hc]; rfl
    · right
      refine ⟨b, hb, ?_, hk0⟩
      simp only [] at hpush ⊢
      rw [hpush]
      cases hv : c1.val with
      | nil => rw [hv] at hh; simp at hh
      | cons x xs => rw [hv] at hh; simpa using hh
  · rw [if_neg ht] at hr
    have hr' := Result.ok.inj hr
    subst hr'
    refine ⟨fun y h => ?_, fun x' h => (by cases h)⟩
    cases h
    rcases hinv with ⟨hc, h0⟩ | ⟨b, hb, hh, hk0⟩
    · left
      refine ⟨?_, hc⟩
      have : ¬ t1.val < k.val := by simpa using ht
      omega
    · exact Or.inr ⟨b, hb, hh, hk0⟩

theorem new_loop0_head (m : Slice Std.U8) (k : Usize)
    (c : alloc.vec.Vec (Array Std.U8 32#usize)) (hc : c.val = [])
    (v : alloc.vec.Vec (Array Std.U8 32#usize))
    (hv : tacenta_erasure.Encoder.new_loop0 m k c 0#usize = ok v) :
    HeadPost m k v := by
  unfold tacenta_erasure.Encoder.new_loop0 at hv
  refine (loop_OK (fun p => k.val - p.2.val) (fun p => HeadInv m k p.1 p.2) (HeadPost m k)
    (fun p => tacenta_erasure.Encoder.new_loop0.body m k p.1 p.2) ?_)
    (c, 0#usize) (Or.inl ⟨hc, rfl⟩) v hv
  intro x hx
  exact new_loop0_body_head m k x.1 x.2 hx

theorem next_chunk_first (e : tacenta_erasure.Encoder) (b : Array U8 32#usize)
    (h0 : e.next = 0#u16) (hex : e.exhausted = false) (hh : e.chunks.val.head? = some b) :
    tacenta_erasure.Encoder.next_chunk e =
      ok (some { index := 0#u16, data := b }, { e with next := 1#u16 }) := by
  unfold tacenta_erasure.Encoder.next_chunk
  have hlen : 0 < e.chunks.val.length := by
    cases hv : e.chunks.val with
    | nil => rw [hv] at hh; simp at hh
    | cons x xs => simp
  rw [hex]
  simp only [Bool.false_eq_true, if_false]
  rw [h0]
  have hcast : UScalar.cast UScalarTy.Usize 0#u16 = 0#usize :=
    UScalar.eq_of_val_eq (by simp)
  have hhead : e.chunks.val[0]'hlen = b := by
    have h' := hh
    rw [List.head?_eq_getElem?] at h'
    exact (List.getElem?_eq_some_iff.mp h').2
  have hidx : e.chunks.index_usize 0#usize = ok b := by
    obtain ⟨x, hx, hxv⟩ := Std.WP.spec_imp_exists
      (alloc.vec.Vec.index_usize_spec e.chunks 0#usize (by simpa using hlen))
    rw [hx]
    simp [hxv, hhead]
  have hne : ¬ ((0#u16 : U16) = core.num.U16.MAX) := by decide
  have h1 : (0#u16 : U16) + 1#u16 = ok 1#u16 := by
    obtain ⟨z, hz, hzv⟩ := Std.WP.spec_imp_exists
      (UScalar.add_spec (x := (0#u16 : U16)) (y := 1#u16) (by scalar_tac))
    have : z = 1#u16 := UScalar.eq_of_val_eq (by simpa using hzv)
    rw [hz, this]
  simp [lift, hcast, hlen, hidx, hne, h1]


theorem next_chunk_some (e : tacenta_erasure.Encoder) (hex : e.exhausted = false)
    (r : Option tacenta_erasure.Chunk × tacenta_erasure.Encoder)
    (h : tacenta_erasure.Encoder.next_chunk e = ok r) :
    ∃ d e', r = (some { index := e.next, data := d }, e') := by
  unfold tacenta_erasure.Encoder.next_chunk at h
  rw [hex] at h
  simp only [Bool.false_eq_true, if_false] at h
  repeat' first
    | exact ⟨_, _, (Result.ok.inj h).symm⟩
    | (obtain ⟨_, _, h⟩ := bind_eq_ok_inv h)
    | split at h



/-- The clamp `Encoder::new` applies to the chunk count. -/
def clamp (k : Usize) : Usize :=
  if k > tacenta_erasure.MAX_CODEWORDS then tacenta_erasure.MAX_CODEWORDS else k

theorem max_codewords_pos : 0 < tacenta_erasure.MAX_CODEWORDS.val := by
  have : tacenta_erasure.MAX_CODEWORDS = 65536#usize := by
    unfold tacenta_erasure.MAX_CODEWORDS; rfl
  rw [this]; simp

theorem new_shape (s : Slice Std.U8) (e : tacenta_erasure.Encoder)
    (h : tacenta_erasure.Encoder.new s = ok e) :
    e.next = 0#u16 ∧ e.exhausted = false ∧
      ∃ k, tacenta_erasure.chunk_count (Slice.len s) = ok k ∧
        ((clamp k).val = 0 ∧ e.chunks.val = [] ∨
          ∃ b, inner s = ok b ∧ e.chunks.val.head? = some b ∧ 0 < (clamp k).val) := by
  unfold tacenta_erasure.Encoder.new at h
  obtain ⟨k, hk, h⟩ := bind_eq_ok_inv h
  obtain ⟨k1, hk1, h⟩ := bind_eq_ok_inv h
  obtain ⟨v, hv, h⟩ := bind_eq_ok_inv h
  have he := (Result.ok.inj h)
  subst he
  have hk1c : k1 = clamp k := by
    unfold clamp
    by_cases hgt : k > tacenta_erasure.MAX_CODEWORDS
    · rw [if_pos hgt] at hk1 ⊢
      exact (Result.ok.inj hk1).symm
    · rw [if_neg hgt] at hk1 ⊢
      exact (Result.ok.inj hk1).symm
  subst hk1c
  have hhead := new_loop0_head s (clamp k) (alloc.vec.Vec.with_capacity (Array Std.U8 32#usize) (clamp k)) rfl v hv
  exact ⟨rfl, rfl, k, hk, hhead⟩


/-- Two slices of equal length that agree on their first 32 bytes yield encoders whose
first codeword is the same chunk. -/
theorem first_codeword_collision (s1 s2 : Slice Std.U8) (e1 e2 : tacenta_erasure.Encoder)
    (hlen : Slice.len s1 = Slice.len s2)
    (hag : ∀ i : Nat, i < 32 → s1.val[i]? = s2.val[i]?)
    (h1 : tacenta_erasure.Encoder.new s1 = ok e1)
    (h2 : tacenta_erasure.Encoder.new s2 = ok e2) :
    ∃ c : tacenta_erasure.Chunk, c.index.val = 0 ∧ NthChunk 0 e1 c ∧ NthChunk 0 e2 c := by
  obtain ⟨hn1, hx1, k1, hk1, hd1⟩ := new_shape s1 e1 h1
  obtain ⟨hn2, hx2, k2, hk2, hd2⟩ := new_shape s2 e2 h2
  rw [hlen] at hk1
  rw [hk1] at hk2
  have hkk : k1 = k2 := Result.ok.inj hk2
  subst hkk
  have hin : inner s1 = inner s2 := inner_eq s1 s2 hlen hag (Array.repeat 32#usize 0#u8)
  rcases hd1 with ⟨hz1, hc1⟩ | ⟨b1, hb1, hh1, hp1⟩
  · rcases hd2 with ⟨hz2, hc2⟩ | ⟨b2, hb2, hh2, hp2⟩
    · -- both encoders hold no chunk: they are the same encoder
      have hch : e1.chunks = e2.chunks := Subtype.ext (hc1.trans hc2.symm)
      have he : e1 = e2 := by
        cases e1; cases e2
        simp only [] at hch hn1 hn2 hx1 hx2
        simp [hch, hn1, hn2, hx1, hx2]
      subst he
      have hlt : e1.chunks.val.length < Usize.max := by rw [hc1]; simp; scalar_tac
      obtain ⟨r, hr⟩ := (Tacenta.SessionUnitErasureT1.noPanic_iff _).mp
        (Tacenta.SessionUnitErasureT1.next_chunk_no_panic e1 hlt)
      obtain ⟨d, e', hrc⟩ := next_chunk_some e1 hx1 r hr
      subst hrc
      have hidx : (({ index := e1.next, data := d } : tacenta_erasure.Chunk)).index.val = 0 := by
        simp [hn1]
      exact ⟨{ index := e1.next, data := d }, hidx, ⟨e', hr⟩, ⟨e', hr⟩⟩
    · omega
  · rcases hd2 with ⟨hz2, hc2⟩ | ⟨b2, hb2, hh2, hp2⟩
    · omega
    · have hb : b1 = b2 := by
        rw [hin] at hb1
        rw [hb1] at hb2
        exact Result.ok.inj hb2
      subst hb
      refine ⟨{ index := 0#u16, data := b1 }, rfl, ?_, ?_⟩
      · exact ⟨_, next_chunk_first e1 b1 hn1 hx1 hh1⟩
      · exact ⟨_, next_chunk_first e2 b1 hn2 hx2 hh2⟩


/-- A slice of length `n` whose `i`th byte is `f i`. -/
def mkSlice (n : Usize) (f : Nat → Std.U8) : Slice Std.U8 :=
  ⟨(List.range n.val).map f, by simp; scalar_tac⟩

def sliceA (n : Usize) : Slice Std.U8 := mkSlice n (fun _ => 0#u8)
def sliceB (n : Usize) : Slice Std.U8 := mkSlice n (fun i => if i = 32 then 1#u8 else 0#u8)

theorem sliceAB_len (n : Usize) : Slice.len (sliceA n) = Slice.len (sliceB n) := by
  apply UScalar.eq_of_val_eq
  simp [Slice.len, sliceA, sliceB, mkSlice]

theorem sliceAB_agree (n : Usize) (hn : 33 ≤ n.val) :
    ∀ i : Nat, i < 32 → (sliceA n).val[i]? = (sliceB n).val[i]? := by
  intro i hi
  simp only [sliceA, sliceB, mkSlice, List.getElem?_map]
  have : i < n.val := by omega
  simp [this, show i ≠ 32 by omega]

theorem sliceAB_ne (n : Usize) (hn : 33 ≤ n.val) : sliceA n ≠ sliceB n := by
  intro h
  have h' := congrArg (fun s : Slice Std.U8 => s.val[32]?) h
  simp only [sliceA, sliceB, mkSlice, List.getElem?_map] at h'
  have : 32 < n.val := by omega
  simp [this] at h'

/-- `CodewordViewOf` is false as soon as `Encoder::new` returns on two messages of one length
`n` above 32 bytes that agree on their first 32 bytes and differ afterwards (`sliceA n` is `n` zero
bytes, `sliceB n` the same with byte 32 set to one). Both messages then have the same codeword at
index 0, and the clause `receive` asks the view to name the one source it came from. The proof
does not depend on what `usize::div_ceil` returns, only on `Encoder::new` returning. -/
theorem codewordViewOf_false (view : Model.Lifecycle.CodewordView) (n : Usize)
    (hn : 33 ≤ n.val)
    (e1 e2 : tacenta_erasure.Encoder)
    (h1 : tacenta_erasure.Encoder.new (sliceA n) = ok e1)
    (h2 : tacenta_erasure.Encoder.new (sliceB n) = ok e2) :
    ¬ Tacenta.UnitLifecycleT3.CodewordViewOf view := by
  intro hview
  obtain ⟨c, hc0, hn1, hn2⟩ := first_codeword_collision (sliceA n) (sliceB n) e1 e2
    (sliceAB_len n) (sliceAB_agree n hn) h1 h2
  have cw1 : CodewordOf (sliceOf (sliceA n)) c := ⟨sliceA n, e1, rfl, h1, by rw [hc0]; exact hn1⟩
  have cw2 : CodewordOf (sliceOf (sliceB n)) c := ⟨sliceB n, e2, rfl, h2, by rw [hc0]; exact hn2⟩
  have r1 := hview.receive .failed _ c cw1
  have r2 := hview.receive .failed _ c cw2
  rw [r1] at r2
  have hsrc := congrArg (fun x : Model.Braid.Chunk => x.source) r2
  exact sliceAB_ne n hn (sliceOf_inj hsrc)

/-- With `Encoder::new` total, which the field `encoderNew` of every encrypt contract record
(`BraidSendRefinementContracts`) says it is, no view satisfies the structure. The hypothesis is
`SessionUnitBraidT1.EncoderNewTotal`, which `UnitSatisfiabilityErasure.encoderNew_iff` shows is
equivalent to the law that `usize::div_ceil` returns at divisor 32. The messages are the
33-byte ones of `codewordViewOf_false`. -/
theorem codewordViewOf_false_of_encoderNewTotal
    (hnew : Tacenta.SessionUnitBraidT1.EncoderNewTotal)
    (view : Model.Lifecycle.CodewordView) :
    ¬ Tacenta.UnitLifecycleT3.CodewordViewOf view := by
  obtain ⟨e1, h1⟩ := hnew (sliceA 33#usize)
  obtain ⟨e2, h2⟩ := hnew (sliceB 33#usize)
  exact codewordViewOf_false view 33#usize (by simp) e1 e2 h1 h2

end CodewordView

section BraidEvidenceRecord
open tacenta_session_unit
open Tacenta.SessionUnitBraidT3

/-! ## C. `InitialRatchetBraidEvidenceContracts` has no term on six states

The record has the fields `hchunk` and `hhonest`, and neither uses the record's `message`
parameter, so both quantify over every composite, where `braid_receive_evidence` takes them for the
one composite received. For a state whose decoder holds a chunk with source `m0`, `HonestChunk`
gives `ChunkFits d mc`, whose second conjunct says every chunk the decoder holds has the source
of `mc`. With `hchunk`, every incoming chunk at index 0 would then be a codeword of `m0`, and an
encoder has one codeword at index 0 for a given source (`codewordOf_functional`). The theorems
below feed the record two incoming composites that carry different chunks at index 0. -/

/-- `NthChunk` is functional in the chunk, for a fixed starting encoder. -/
theorem nthChunk_functional :
    ∀ (n : Nat) (enc : tacenta_erasure.Encoder) (c1 c2 : tacenta_erasure.Chunk),
      NthChunk n enc c1 → NthChunk n enc c2 → c1 = c2 := by
  intro n
  induction n with
  | zero =>
    intro enc c1 c2 h1 h2
    obtain ⟨e1, h1⟩ := h1
    obtain ⟨e2, h2⟩ := h2
    rw [h1] at h2
    have := Result.ok.inj h2
    have := (Prod.mk.inj this).1
    exact (Option.some.inj this)
  | succ n ih =>
    intro enc c1 c2 h1 h2
    obtain ⟨c, e1, hc1, h1⟩ := h1
    obtain ⟨c', e2, hc2, h2⟩ := h2
    rw [hc1] at hc2
    have hh := Result.ok.inj hc2
    have hpair := Prod.mk.inj hh
    have hcc : c = c' := Option.some.inj hpair.1
    have hee : e1 = e2 := hpair.2
    subst hcc; subst hee
    exact ih e1 c1 c2 h1 h2

/-- A chunk is a codeword of at most one message at a given index... of exactly
one chunk: for a fixed message and index, the codeword is unique. -/
theorem codewordOf_functional (m : Bytes) (c1 c2 : tacenta_erasure.Chunk)
    (h1 : CodewordOf m c1) (h2 : CodewordOf m c2) (hi : c1.index.val = c2.index.val) :
    c1 = c2 := by
  obtain ⟨s1, e1, hs1, hn1, hth1⟩ := h1
  obtain ⟨s2, e2, hs2, hn2, hth2⟩ := h2
  have hs : s1 = s2 := sliceOf_inj (hs1.trans hs2.symm)
  subst hs
  rw [hn1] at hn2
  have he : e1 = e2 := Result.ok.inj hn2
  subst he
  rw [← hi] at hth2
  exact nthChunk_functional _ _ _ _ hth1 hth2


open Tacenta.UnitLifecycleT3

theorem ofNatCore_val64 (e : Nat) (he : e < 2^64) :
    (UScalar.ofNatCore (ty := .U64) e (by simpa using he)).val = e := by
  simp [UScalar.ofNatCore]
  rfl


/-- A real composite carrying one codeword, index 0, of agreement type `ty`. -/
def rcomp (ty : tacenta_wire.AgreementType) (e : Nat) (he : e < 2 ^ 64)
    (a : Array Std.U8 32#usize) : tacenta_wire.Composite :=
  { dh := Array.repeat 32#usize 0#u8, pn := 0#u32, n := 0#u32, pq_epoch := 0#u64,
    pq_n := 0#u64, ag_epoch := UScalar.ofNatCore (ty := .U64) e (by simpa using he),
    ag_type := ty, ag_chunk := some { index := 0#u16, data := a } }

theorem rcomp_epoch (ty : tacenta_wire.AgreementType) (e : Nat) (he : e < 2 ^ 64)
    (a : Array Std.U8 32#usize) :
    (UInt64.ofNat (rcomp ty e he a).ag_epoch.val).toNat = e := by
  show (UInt64.ofNat (UScalar.ofNatCore (ty := .U64) e (by simpa using he)).val).toNat = e
  rw [ofNatCore_val64 e he, UInt64.toNat_ofNat']
  exact Nat.mod_eq_of_lt (by simpa using he)

def arr0 : Array Std.U8 32#usize := Array.repeat 32#usize 0#u8
def arr1 : Array Std.U8 32#usize := Array.repeat 32#usize 1#u8

theorem arr0_ne_arr1 : arr0 ≠ arr1 := by
  intro h
  have := congrArg (fun a => a.val) h
  simp [arr0, arr1] at this

/-- The two fields `hchunk` and `hhonest` of the record force every incoming
chunk to be a codeword of the one source a held chunk carries.  `st` is the
model's Braid state, `ty` the agreement type that the state feeds to a decoder
`d`, `hfit` that arm of `HonestChunk`. -/
theorem source_of_record
    {K : Model.Braid.Kem} {view : Model.Lifecycle.CodewordView}
    {real : lifecycle.Session} {model : Model.Lifecycle.Session} {message : Slice Std.U8}
    (ev : InitialRatchetBraidEvidenceContracts (K := K) view real model message)
    (st : Model.Braid.BraidState) (hmodel : model.braid = st)
    (he : st.epoch < 2 ^ 64) (ty : tacenta_wire.AgreementType)
    (d : Model.Braid.Decoder)
    (hfit : ∀ mc : Model.Braid.Chunk,
      HonestChunk st ⟨st.epoch,
        Model.Lifecycle.braidTypeOf (Tacenta.SessionUnitWireT3.agTypeOf ty), some mc⟩ →
        ChunkFits d mc)
    (c0 : Model.Braid.Chunk) (hc0 : c0 ∈ d.chunks) (a : Array Std.U8 32#usize) :
    CodewordOf c0.source { index := 0#u16, data := a } := by
  have hch := ev.hchunk (rcomp ty st.epoch he a)
    (Tacenta.SessionUnitWireT3.compositeOf (rcomp ty st.epoch he a))
    (composite_refines_wire_compositeOf _)
  have hho := ev.hhonest (Tacenta.SessionUnitWireT3.compositeOf (rcomp ty st.epoch he a))
  rw [hmodel] at hch hho
  simp only [IncomingChunkRefines, rcomp, Tacenta.SessionUnitWireT3.compositeOf,
    Option.map_some] at hch
  obtain ⟨source, hcw, hview⟩ := hch
  have hmsg : Model.Lifecycle.braidMessageOf view st
      (Tacenta.SessionUnitWireT3.compositeOf (rcomp ty st.epoch he a)) =
      ⟨st.epoch, Model.Lifecycle.braidTypeOf (Tacenta.SessionUnitWireT3.agTypeOf ty),
        some (view.receive st (UInt16.ofNat ↑(0#u16))
          (Tacenta.SessionUnitWireT3.bytesOf ↑a))⟩ := by
    simp only [Model.Lifecycle.braidMessageOf, Tacenta.SessionUnitWireT3.compositeOf,
      rcomp, Option.map_some]
    congr 1
    exact rcomp_epoch ty st.epoch he a
  rw [hmsg] at hho
  have hfits := hfit _ hho
  have hsrc := hfits.2 c0 hc0
  rw [hview] at hsrc
  have hsrc' : c0.source = source := hsrc
  rw [hsrc']
  exact hcw

/-- If a decoder holds a chunk, no assignment of the record's two fields exists:
two different incoming codewords at index 0 would both be codewords of the one
source that chunk carries, and an erasure encoder has one codeword at index 0
for a given source. -/
theorem record_empty_of_nonempty_decoder
    {K : Model.Braid.Kem} {view : Model.Lifecycle.CodewordView}
    {real : lifecycle.Session} {model : Model.Lifecycle.Session} {message : Slice Std.U8}
    (st : Model.Braid.BraidState) (hmodel : model.braid = st)
    (he : st.epoch < 2 ^ 64) (ty : tacenta_wire.AgreementType)
    (d : Model.Braid.Decoder)
    (hfit : ∀ mc : Model.Braid.Chunk,
      HonestChunk st ⟨st.epoch,
        Model.Lifecycle.braidTypeOf (Tacenta.SessionUnitWireT3.agTypeOf ty), some mc⟩ →
        ChunkFits d mc)
    (c0 : Model.Braid.Chunk) (hc0 : c0 ∈ d.chunks) :
    ¬ Nonempty (InitialRatchetBraidEvidenceContracts (K := K) view real model message) := by
  rintro ⟨ev⟩
  have h0 := source_of_record ev st hmodel he ty d hfit c0 hc0 arr0
  have h1 := source_of_record ev st hmodel he ty d hfit c0 hc0 arr1
  have heq := codewordOf_functional c0.source _ _ h0 h1 rfl
  have hd := congrArg (fun c : tacenta_erasure.Chunk => c.data) heq
  exact arr0_ne_arr1 hd

/-! The six arms of `HonestChunk`. -/

theorem record_empty_headerSent
    {K : Model.Braid.Kem} {view : Model.Lifecycle.CodewordView}
    {real : lifecycle.Session} {model : Model.Lifecycle.Session} {message : Slice Std.U8}
    (e : Nat) (he : e < 2 ^ 64) (auth : Model.Braid.Auth) (dk : Model.Braid.Bytes)
    (d : Model.Braid.Decoder) (enc : Model.Braid.Encoder)
    (hmodel : model.braid = .headerSent e auth dk d enc)
    (c0 : Model.Braid.Chunk) (hc0 : c0 ∈ d.chunks) :
    ¬ Nonempty (InitialRatchetBraidEvidenceContracts (K := K) view real model message) :=
  record_empty_of_nonempty_decoder (.headerSent e auth dk d enc) hmodel he .Ct1 d
    (fun mc h => h mc rfl rfl) c0 hc0

theorem record_empty_ekSentCt1Received
    {K : Model.Braid.Kem} {view : Model.Lifecycle.CodewordView}
    {real : lifecycle.Session} {model : Model.Lifecycle.Session} {message : Slice Std.U8}
    (e : Nat) (he : e < 2 ^ 64) (auth : Model.Braid.Auth) (dk ct1 : Model.Braid.Bytes)
    (d : Model.Braid.Decoder)
    (hmodel : model.braid = .ekSentCt1Received e auth dk ct1 d)
    (c0 : Model.Braid.Chunk) (hc0 : c0 ∈ d.chunks) :
    ¬ Nonempty (InitialRatchetBraidEvidenceContracts (K := K) view real model message) :=
  record_empty_of_nonempty_decoder (.ekSentCt1Received e auth dk ct1 d) hmodel he .Ct2 d
    (fun mc h => h mc rfl rfl) c0 hc0

theorem record_empty_noHeaderReceived
    {K : Model.Braid.Kem} {view : Model.Lifecycle.CodewordView}
    {real : lifecycle.Session} {model : Model.Lifecycle.Session} {message : Slice Std.U8}
    (e : Nat) (he : e < 2 ^ 64) (auth : Model.Braid.Auth)
    (d : Model.Braid.Decoder)
    (hmodel : model.braid = .noHeaderReceived e auth d)
    (c0 : Model.Braid.Chunk) (hc0 : c0 ∈ d.chunks) :
    ¬ Nonempty (InitialRatchetBraidEvidenceContracts (K := K) view real model message) :=
  record_empty_of_nonempty_decoder (.noHeaderReceived e auth d) hmodel he .Hdr d
    (fun mc h => h mc rfl rfl) c0 hc0

theorem record_empty_ct1Sampled_ek
    {K : Model.Braid.Kem} {view : Model.Lifecycle.CodewordView}
    {real : lifecycle.Session} {model : Model.Lifecycle.Session} {message : Slice Std.U8}
    (e : Nat) (he : e < 2 ^ 64) (auth : Model.Braid.Auth)
    (ekSeed hek encapsSecret ct1 : Model.Braid.Bytes) (enc : Model.Braid.Encoder)
    (d : Model.Braid.Decoder)
    (hmodel : model.braid = .ct1Sampled e auth ekSeed hek encapsSecret ct1 enc d)
    (c0 : Model.Braid.Chunk) (hc0 : c0 ∈ d.chunks) :
    ¬ Nonempty (InitialRatchetBraidEvidenceContracts (K := K) view real model message) :=
  record_empty_of_nonempty_decoder (.ct1Sampled e auth ekSeed hek encapsSecret ct1 enc d) hmodel he
    .Ek d (fun mc h => h mc rfl rfl) c0 hc0

theorem record_empty_ct1Sampled_ekCt1Ack
    {K : Model.Braid.Kem} {view : Model.Lifecycle.CodewordView}
    {real : lifecycle.Session} {model : Model.Lifecycle.Session} {message : Slice Std.U8}
    (e : Nat) (he : e < 2 ^ 64) (auth : Model.Braid.Auth)
    (ekSeed hek encapsSecret ct1 : Model.Braid.Bytes) (enc : Model.Braid.Encoder)
    (d : Model.Braid.Decoder)
    (hmodel : model.braid = .ct1Sampled e auth ekSeed hek encapsSecret ct1 enc d)
    (c0 : Model.Braid.Chunk) (hc0 : c0 ∈ d.chunks) :
    ¬ Nonempty (InitialRatchetBraidEvidenceContracts (K := K) view real model message) :=
  record_empty_of_nonempty_decoder (.ct1Sampled e auth ekSeed hek encapsSecret ct1 enc d) hmodel he
    .EkCt1Ack d (fun mc h => h mc rfl rfl) c0 hc0

theorem record_empty_ct1Acknowledged
    {K : Model.Braid.Kem} {view : Model.Lifecycle.CodewordView}
    {real : lifecycle.Session} {model : Model.Lifecycle.Session} {message : Slice Std.U8}
    (e : Nat) (he : e < 2 ^ 64) (auth : Model.Braid.Auth)
    (ekSeed hek encapsSecret ct1 : Model.Braid.Bytes) (d : Model.Braid.Decoder)
    (hmodel : model.braid = .ct1Acknowledged e auth ekSeed hek encapsSecret ct1 d)
    (c0 : Model.Braid.Chunk) (hc0 : c0 ∈ d.chunks) :
    ¬ Nonempty (InitialRatchetBraidEvidenceContracts (K := K) view real model message) :=
  record_empty_of_nonempty_decoder (.ct1Acknowledged e auth ekSeed hek encapsSecret ct1 d) hmodel he
    .EkCt1Ack d (fun mc h => h mc rfl rfl) c0 hc0

/-- The first of the six states is the one the model Braid reaches by transition (2) of
`Model.Braid.receive`: in `keysSampled`, receiving a ct1 chunk gives `headerSent`, with that chunk
in the decoder. So the hypotheses of `record_empty_headerSent` are met by a state one receive step
from `keysSampled`. -/
theorem keysSampled_receive_ct1_holds_chunk (K : Model.Braid.Kem) (epoch : Nat)
    (auth : Model.Braid.Auth) (dk ekVector : Model.Braid.Bytes) (hdrEnc : Model.Braid.Encoder)
    (c : Model.Braid.Chunk) :
    ∃ enc, (Model.Braid.receive K (.keysSampled epoch auth dk ekVector hdrEnc)
        ⟨epoch, .ct1, some c⟩).2.2 =
      .headerSent epoch auth dk ((Model.Braid.Decoder.new K.ct1Size).addChunk c) enc ∧
      c ∈ ((Model.Braid.Decoder.new K.ct1Size).addChunk c).chunks := by
  refine ⟨Model.Braid.encode ekVector, ?_, ?_⟩
  · simp [Model.Braid.receive]
  · simp [Model.Braid.Decoder.addChunk, Model.Braid.Decoder.new]



end BraidEvidenceRecord

section ConcreteEvidence
open tacenta_session_unit
open Tacenta.UnitLifecycleT3

/-! ## D. The concrete refusal evidence forces a constant `dhPublic`

The field `hmodelPublic` of the two records equates the run's new public key with
`oracle.dhPublic draw` for every `draw`. The run consumed one draw, and the field asks for every
list of bytes. -/

/-- The Triple-refusal evidence record forces the oracle's `dhPublic` to take one value. Its field
`hmodelPublic` equates the run's new public key with `oracle.dhPublic draw` for every draw, and
the run consumed one draw. -/
theorem tripleConcreteEvidence_forces_constant_dhPublic
    {R : Type} {rc : rand_core_1.RngCore R} {crc : rand_core_1.CryptoRng R}
    {trace : R → List Model.Lifecycle.Key} {dh : DhView} {K : Model.Braid.Kem}
    {view : Model.Lifecycle.CodewordView} {oracle : Model.Lifecycle.Oracle}
    {real : lifecycle.Session} {model : Model.Lifecycle.Session}
    {message : Slice Std.U8} {rng : R}
    {input : InitialRatchetRefusalBranchInput (rc := rc) (crc := crc)
      (trace := trace) (dh := dh) (K := K) (view := view) (oracle := oracle)
      (real := real) (model := model) message rng}
    {realReason : tacenta_triple.TripleError}
    {modelComposite : Model.CompositeHeader.Composite}
    {modelReason : Model.Triple.ReceiveRefusal}
    (ev : InitialRatchetTripleConcreteEvidence input realReason modelComposite modelReason)
    (pref : InitialRatchetTripleRefusalPrefix rc crc real input.decoded.message.deref rng
      input.rngNext realReason input.next) :
    ∀ d1 d2 : Model.Lifecycle.Key, oracle.dhPublic d1 = oracle.dhPublic d2 := fun d1 d2 =>
  (ev.hmodelPublic d1 pref).symm.trans (ev.hmodelPublic d2 pref)

/-- The same for the AEAD-refusal evidence record. -/
theorem aeadConcreteEvidence_forces_constant_dhPublic
    {R : Type} {rc : rand_core_1.RngCore R} {crc : rand_core_1.CryptoRng R}
    {trace : R → List Model.Lifecycle.Key} {dh : DhView} {K : Model.Braid.Kem}
    {view : Model.Lifecycle.CodewordView} {oracle : Model.Lifecycle.Oracle}
    {real : lifecycle.Session} {model : Model.Lifecycle.Session}
    {message : Slice Std.U8} {rng : R}
    {input : InitialRatchetRefusalBranchInput (rc := rc) (crc := crc)
      (trace := trace) (dh := dh) (K := K) (view := view) (oracle := oracle)
      (real := real) (model := model) message rng}
    {modelComposite : Model.CompositeHeader.Composite}
    {modelTripleCandidate : Model.Triple.State} {modelMk : Model.Lifecycle.Key}
    (ev : InitialRatchetAeadConcreteEvidence input modelComposite modelTripleCandidate modelMk)
    (pref : InitialRatchetAeadRefusalPrefix rc crc real input.decoded.message.deref rng
      input.rngNext input.next) :
    ∀ d1 d2 : Model.Lifecycle.Key, oracle.dhPublic d1 = oracle.dhPublic d2 := fun d1 d2 =>
  (ev.hmodelPublic d1 pref).symm.trans (ev.hmodelPublic d2 pref)

/-- The `dhPublic` clause of `OracleOf`, alone: the model oracle's public key for the view of a
private key is the view of the translated `PrivateKey::public_key`. -/
def OracleDhPublic (dh : DhView) (oracle : Model.Lifecycle.Oracle) : Prop :=
  ∀ secret, ∃ publicKey,
    tacenta_boundary.dh.PrivateKey.public_key secret = ok publicKey ∧
      dh.publicKey publicKey = oracle.dhPublic (dh.privateKey secret)

/-- A statement about the real X25519 public-key function: two 32-byte private keys that it maps
to different 32-byte public keys. The two private keys of RFC 7748 section 6.1 are two such keys, and
`the_fixed_secrets_have_the_table_keys` in `tacenta-core/tests/identity_boundary.rs` checks their
published public keys through `PrivateKey::public_key`. The translated `public_key` is an opaque
constant, so this repository tests the statement and does not prove it. -/
def PublicKeyNotConstant : Prop :=
  ∃ (b1 b2 : Array Std.U8 32#usize) (sk1 sk2 : tacenta_boundary.dh.PrivateKey)
    (pk1 pk2 : tacenta_boundary.dh.PublicKeyBytes) (q1 q2 : Array Std.U8 32#usize),
    tacenta_boundary.dh.PrivateKey.from_bytes b1 = ok sk1 ∧
    tacenta_boundary.dh.PrivateKey.from_bytes b2 = ok sk2 ∧
    tacenta_boundary.dh.PrivateKey.public_key sk1 = ok pk1 ∧
    tacenta_boundary.dh.PrivateKey.public_key sk2 = ok pk2 ∧
    tacenta_boundary.dh.PublicKeyBytes.as_bytes pk1 = ok q1 ∧
    tacenta_boundary.dh.PublicKeyBytes.as_bytes pk2 = ok q2 ∧
    q1 ≠ q2

theorem arrayOf_inj {a b : Array Std.U8 32#usize} (h : arrayOf a = arrayOf b) : a = b := by
  unfold arrayOf at h
  have hl : a.val = b.val :=
    (List.map_injective_iff.mpr (fun x y hxy => u8_inj hxy)) h
  exact Subtype.ext hl

/-- With the oracle's `dhPublic` clause and the DH codec, a constant `dhPublic` makes every two
32-byte private keys that `from_bytes` accepts have the same public-key bytes: it contradicts
`PublicKeyNotConstant`. -/
theorem constant_dhPublic_false_of_publicKeyNotConstant
    {dh : DhView} {oracle : Model.Lifecycle.Oracle}
    (codec : DhCodecOf dh) (hdh : OracleDhPublic dh oracle)
    (hfact : PublicKeyNotConstant)
    (hconst : ∀ d1 d2 : Model.Lifecycle.Key, oracle.dhPublic d1 = oracle.dhPublic d2) :
    False := by
  obtain ⟨b1, b2, sk1, sk2, pk1, pk2, q1, q2, hs1, hs2, hp1, hp2, hq1, hq2, hne⟩ := hfact
  obtain ⟨sk1', h1, v1⟩ := codec.privateFromBytes b1
  obtain ⟨sk2', h2, v2⟩ := codec.privateFromBytes b2
  rw [hs1] at h1
  rw [hs2] at h2
  have e1 := Result.ok.inj h1
  have e2 := Result.ok.inj h2
  subst e1; subst e2
  obtain ⟨p1, hpk1, w1⟩ := hdh sk1
  obtain ⟨p2, hpk2, w2⟩ := hdh sk2
  rw [hp1] at hpk1
  rw [hp2] at hpk2
  have f1 := Result.ok.inj hpk1
  have f2 := Result.ok.inj hpk2
  subst f1; subst f2
  obtain ⟨r1, hr1, x1⟩ := codec.asBytes pk1
  obtain ⟨r2, hr2, x2⟩ := codec.asBytes pk2
  rw [hq1] at hr1
  rw [hq2] at hr2
  have g1 := Result.ok.inj hr1
  have g2 := Result.ok.inj hr2
  subst g1; subst g2
  apply hne
  apply arrayOf_inj
  rw [x1, x2, w1, w2]
  exact hconst _ _

/-- The Triple-refusal evidence record cannot hold for a refusal run, given the DH codec, the
oracle's `dhPublic` clause and `PublicKeyNotConstant`. A prefix exists for every real Triple
refusal (`initial_ratchet_triple_refusal_prefix_of_result`). -/
theorem tripleConcreteEvidence_false_of_publicKeyNotConstant
    {R : Type} {rc : rand_core_1.RngCore R} {crc : rand_core_1.CryptoRng R}
    {trace : R → List Model.Lifecycle.Key} {dh : DhView} {K : Model.Braid.Kem}
    {view : Model.Lifecycle.CodewordView} {oracle : Model.Lifecycle.Oracle}
    {real : lifecycle.Session} {model : Model.Lifecycle.Session}
    {message : Slice Std.U8} {rng : R}
    {input : InitialRatchetRefusalBranchInput (rc := rc) (crc := crc)
      (trace := trace) (dh := dh) (K := K) (view := view) (oracle := oracle)
      (real := real) (model := model) message rng}
    {realReason : tacenta_triple.TripleError}
    {modelComposite : Model.CompositeHeader.Composite}
    {modelReason : Model.Triple.ReceiveRefusal}
    (ev : InitialRatchetTripleConcreteEvidence input realReason modelComposite modelReason)
    (pref : InitialRatchetTripleRefusalPrefix rc crc real input.decoded.message.deref rng
      input.rngNext realReason input.next)
    (codec : DhCodecOf dh) (hdh : OracleDhPublic dh oracle) (hfact : PublicKeyNotConstant) :
    False :=
  constant_dhPublic_false_of_publicKeyNotConstant codec hdh hfact
    (tripleConcreteEvidence_forces_constant_dhPublic ev pref)

/-- The same for the AEAD-refusal evidence record. -/
theorem aeadConcreteEvidence_false_of_publicKeyNotConstant
    {R : Type} {rc : rand_core_1.RngCore R} {crc : rand_core_1.CryptoRng R}
    {trace : R → List Model.Lifecycle.Key} {dh : DhView} {K : Model.Braid.Kem}
    {view : Model.Lifecycle.CodewordView} {oracle : Model.Lifecycle.Oracle}
    {real : lifecycle.Session} {model : Model.Lifecycle.Session}
    {message : Slice Std.U8} {rng : R}
    {input : InitialRatchetRefusalBranchInput (rc := rc) (crc := crc)
      (trace := trace) (dh := dh) (K := K) (view := view) (oracle := oracle)
      (real := real) (model := model) message rng}
    {modelComposite : Model.CompositeHeader.Composite}
    {modelTripleCandidate : Model.Triple.State} {modelMk : Model.Lifecycle.Key}
    (ev : InitialRatchetAeadConcreteEvidence input modelComposite modelTripleCandidate modelMk)
    (pref : InitialRatchetAeadRefusalPrefix rc crc real input.decoded.message.deref rng
      input.rngNext input.next)
    (codec : DhCodecOf dh) (hdh : OracleDhPublic dh oracle) (hfact : PublicKeyNotConstant) :
    False :=
  constant_dhPublic_false_of_publicKeyNotConstant codec hdh hfact
    (aeadConcreteEvidence_forces_constant_dhPublic ev pref)

end ConcreteEvidence

section KemOracle
open tacenta_session_unit
open Tacenta.UnitLifecycleT3

/-! ## E. What `OracleOf.kemEncapsulateSuccess` costs inside the model

The clause asserts, for every public key and every RNG state that still has a draw, that the
translated `encapsulate` returns `Ok` with the oracle's result. The shipped function returns
`Err(KemError)` for a wrong length or a failed `validate_public_key` before it draws
(`tacenta-core/boundary/src/kem.rs`). `GAP-REGISTER.md`, row `E2E-04`, records that. The two
theorems show what the clause asserts inside the model: the model's oracle never refuses an
encapsulation key at any draw, and the call never returns `Err` while the trace has a draw, so the
premise of the clause `kemEncapsulateError` cannot hold while a draw remains. -/

/-- `OracleOf.kemEncapsulateSuccess` is unguarded: for every public key and every RNG
state that still has a draw, the translated boundary call returns `Ok`.  So the clause
makes the model's oracle never refuse an encapsulation key at any draw. -/
theorem oracleOf_kem_oracle_never_refuses
    {R : Type} {rc : rand_core_1.RngCore R} {crc : rand_core_1.CryptoRng R}
    {trace : R → List Model.Lifecycle.Key} {dh : DhView} {kem : KemView}
    {oracle : Model.Lifecycle.Oracle}
    (oracleOf : OracleOf rc crc dh kem trace oracle)
    (publicKey : Slice Std.U8) (rng : R) (draw : Model.Lifecycle.Key)
    (rest : List Model.Lifecycle.Key) (h : trace rng = draw :: rest) :
    ∃ r, oracle.kemEncaps (sliceOf publicKey) draw = some r := by
  obtain ⟨result, rng', _, _, hres⟩ := oracleOf.kemEncapsulateSuccess publicKey rng draw rest h
  exact ⟨_, hres.symm⟩

/-- And the boundary call itself never returns `Err` while the RNG has a draw. -/
theorem oracleOf_kem_call_never_errs
    {R : Type} {rc : rand_core_1.RngCore R} {crc : rand_core_1.CryptoRng R}
    {trace : R → List Model.Lifecycle.Key} {dh : DhView} {kem : KemView}
    {oracle : Model.Lifecycle.Oracle}
    (oracleOf : OracleOf rc crc dh kem trace oracle)
    (publicKey : Slice Std.U8) (rng : R) (draw : Model.Lifecycle.Key)
    (rest : List Model.Lifecycle.Key) (h : trace rng = draw :: rest)
    (rng' : R) (error : tacenta_boundary.kem.KemError) :
    tacenta_boundary.kem.encapsulate rc crc publicKey rng ≠ ok (.Err error, rng') := by
  intro hcall
  obtain ⟨result, rng'', hok, _, _⟩ := oracleOf.kemEncapsulateSuccess publicKey rng draw rest h
  rw [hcall] at hok
  have := Result.ok.inj hok
  have := (Prod.mk.inj this).1
  cases this


end KemOracle

end Tacenta.DispatchEvidenceVacuity

/-! ## Pins

The axiom bases of the claimed results, and the statements of the refutations, held by the build.
The axiom lists name constants that occur in the statements of the results (the translated
operations the hypotheses are about), not assumptions the proofs make; the results that need no
constant list the three standard axioms only. The statement pins fix what each result says: a
weaker hypothesis list or a different conclusion fails the build here, and an axiom pin alone
would not notice it. `attest.py` lists the axiom pins in `REQUIRED_PINS` and the statement pins in
`REQUIRED_STATEMENT_PINS`, so deleting one fails it. -/

/--
info: 'Tacenta.DispatchEvidenceVacuity.same_ephemeral_agreement_empty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.agree,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.from_bytes]
-/
#guard_msgs in
#print axioms Tacenta.DispatchEvidenceVacuity.same_ephemeral_agreement_empty

/--
info: Tacenta.DispatchEvidenceVacuity.same_ephemeral_agreement_empty
  (p : tacenta_session_unit.tacenta_boundary.dh.PrivateKey) :
  tacenta_session_unit.lifecycle.same_ephemeral_agreement p ⟨[], ⋯⟩ ⟨[], ⋯⟩ = ok false
-/
#guard_msgs in
#check Tacenta.DispatchEvidenceVacuity.same_ephemeral_agreement_empty

/--
info: 'Tacenta.DispatchEvidenceVacuity.initialSameEphemeralEvidence_false' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.agree,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.from_bytes]
-/
#guard_msgs in
#print axioms Tacenta.DispatchEvidenceVacuity.initialSameEphemeralEvidence_false

/--
info: Tacenta.DispatchEvidenceVacuity.initialSameEphemeralEvidence_false (dh : Tacenta.UnitLifecycleT3.DhView)
  (oracle : Model.Lifecycle.Oracle) (real : tacenta_session_unit.lifecycle.Session) (model : Model.Lifecycle.Session) :
  ¬Tacenta.UnitLifecycleT3.InitialSameEphemeralEvidence dh oracle real model
-/
#guard_msgs in
#check Tacenta.DispatchEvidenceVacuity.initialSameEphemeralEvidence_false

/--
info: 'Tacenta.DispatchEvidenceVacuity.codewordViewOf_false' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.core.num.Usize.div_ceil]
-/
#guard_msgs in
#print axioms Tacenta.DispatchEvidenceVacuity.codewordViewOf_false

/--
info: Tacenta.DispatchEvidenceVacuity.codewordViewOf_false (view : Model.Lifecycle.CodewordView) (n : Usize) (hn : 33 ≤ ↑n)
  (e1 e2 : tacenta_session_unit.tacenta_erasure.Encoder)
  (h1 : tacenta_session_unit.tacenta_erasure.Encoder.new (Tacenta.DispatchEvidenceVacuity.sliceA n) = ok e1)
  (h2 : tacenta_session_unit.tacenta_erasure.Encoder.new (Tacenta.DispatchEvidenceVacuity.sliceB n) = ok e2) :
  ¬Tacenta.UnitLifecycleT3.CodewordViewOf view
-/
#guard_msgs in
#check Tacenta.DispatchEvidenceVacuity.codewordViewOf_false

/--
info: 'Tacenta.DispatchEvidenceVacuity.codewordViewOf_false_of_encoderNewTotal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.core.num.Usize.div_ceil]
-/
#guard_msgs in
#print axioms Tacenta.DispatchEvidenceVacuity.codewordViewOf_false_of_encoderNewTotal

/--
info: Tacenta.DispatchEvidenceVacuity.codewordViewOf_false_of_encoderNewTotal
  (hnew : Tacenta.SessionUnitBraidT1.EncoderNewTotal) (view : Model.Lifecycle.CodewordView) :
  ¬Tacenta.UnitLifecycleT3.CodewordViewOf view
-/
#guard_msgs in
#check Tacenta.DispatchEvidenceVacuity.codewordViewOf_false_of_encoderNewTotal

/--
info: 'Tacenta.DispatchEvidenceVacuity.record_empty_of_nonempty_decoder' depends on axioms: [propext,
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
 tacenta_session_unit.tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.core.option.Option.Insts.CoreCloneClone.clone,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index]
-/
#guard_msgs in
#print axioms Tacenta.DispatchEvidenceVacuity.record_empty_of_nonempty_decoder

/--
info: Tacenta.DispatchEvidenceVacuity.record_empty_of_nonempty_decoder {K : Model.Braid.Kem}
  {view : Model.Lifecycle.CodewordView} {real : tacenta_session_unit.lifecycle.Session}
  {model : Model.Lifecycle.Session} {message : Slice U8} (st : Model.Braid.BraidState) (hmodel : model.braid = st)
  (he : st.epoch < 2 ^ 64) (ty : tacenta_session_unit.tacenta_wire.AgreementType) (d : Model.Braid.Decoder)
  (hfit :
    ∀ (mc : Model.Braid.Chunk),
      Tacenta.SessionUnitBraidT3.HonestChunk st
          { epoch := st.epoch, type := Model.Lifecycle.braidTypeOf (Tacenta.SessionUnitWireT3.agTypeOf ty),
            data := some mc } →
        Tacenta.SessionUnitBraidT3.ChunkFits d mc)
  (c0 : Model.Braid.Chunk) (hc0 : c0 ∈ d.chunks) :
  ¬Nonempty (Tacenta.UnitLifecycleT3.InitialRatchetBraidEvidenceContracts view real model message)
-/
#guard_msgs in
#check Tacenta.DispatchEvidenceVacuity.record_empty_of_nonempty_decoder

/--
info: 'Tacenta.DispatchEvidenceVacuity.record_empty_headerSent' depends on axioms: [propext,
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
 tacenta_session_unit.tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.core.option.Option.Insts.CoreCloneClone.clone,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index]
-/
#guard_msgs in
#print axioms Tacenta.DispatchEvidenceVacuity.record_empty_headerSent

/--
info: Tacenta.DispatchEvidenceVacuity.record_empty_headerSent {K : Model.Braid.Kem} {view : Model.Lifecycle.CodewordView}
  {real : tacenta_session_unit.lifecycle.Session} {model : Model.Lifecycle.Session} {message : Slice U8} (e : ℕ)
  (he : e < 2 ^ 64) (auth : Model.Braid.Auth) (dk : Model.Braid.Bytes) (d : Model.Braid.Decoder)
  (enc : Model.Braid.Encoder) (hmodel : model.braid = Model.Braid.BraidState.headerSent e auth dk d enc)
  (c0 : Model.Braid.Chunk) (hc0 : c0 ∈ d.chunks) :
  ¬Nonempty (Tacenta.UnitLifecycleT3.InitialRatchetBraidEvidenceContracts view real model message)
-/
#guard_msgs in
#check Tacenta.DispatchEvidenceVacuity.record_empty_headerSent

/--
info: 'Tacenta.DispatchEvidenceVacuity.record_empty_ekSentCt1Received' depends on axioms: [propext,
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
 tacenta_session_unit.tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.core.option.Option.Insts.CoreCloneClone.clone,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index]
-/
#guard_msgs in
#print axioms Tacenta.DispatchEvidenceVacuity.record_empty_ekSentCt1Received

/--
info: Tacenta.DispatchEvidenceVacuity.record_empty_ekSentCt1Received {K : Model.Braid.Kem}
  {view : Model.Lifecycle.CodewordView} {real : tacenta_session_unit.lifecycle.Session}
  {model : Model.Lifecycle.Session} {message : Slice U8} (e : ℕ) (he : e < 2 ^ 64) (auth : Model.Braid.Auth)
  (dk ct1 : Model.Braid.Bytes) (d : Model.Braid.Decoder)
  (hmodel : model.braid = Model.Braid.BraidState.ekSentCt1Received e auth dk ct1 d) (c0 : Model.Braid.Chunk)
  (hc0 : c0 ∈ d.chunks) :
  ¬Nonempty (Tacenta.UnitLifecycleT3.InitialRatchetBraidEvidenceContracts view real model message)
-/
#guard_msgs in
#check Tacenta.DispatchEvidenceVacuity.record_empty_ekSentCt1Received

/--
info: 'Tacenta.DispatchEvidenceVacuity.record_empty_noHeaderReceived' depends on axioms: [propext,
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
 tacenta_session_unit.tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.core.option.Option.Insts.CoreCloneClone.clone,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index]
-/
#guard_msgs in
#print axioms Tacenta.DispatchEvidenceVacuity.record_empty_noHeaderReceived

/--
info: Tacenta.DispatchEvidenceVacuity.record_empty_noHeaderReceived {K : Model.Braid.Kem}
  {view : Model.Lifecycle.CodewordView} {real : tacenta_session_unit.lifecycle.Session}
  {model : Model.Lifecycle.Session} {message : Slice U8} (e : ℕ) (he : e < 2 ^ 64) (auth : Model.Braid.Auth)
  (d : Model.Braid.Decoder) (hmodel : model.braid = Model.Braid.BraidState.noHeaderReceived e auth d)
  (c0 : Model.Braid.Chunk) (hc0 : c0 ∈ d.chunks) :
  ¬Nonempty (Tacenta.UnitLifecycleT3.InitialRatchetBraidEvidenceContracts view real model message)
-/
#guard_msgs in
#check Tacenta.DispatchEvidenceVacuity.record_empty_noHeaderReceived

/--
info: 'Tacenta.DispatchEvidenceVacuity.record_empty_ct1Sampled_ek' depends on axioms: [propext,
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
 tacenta_session_unit.tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.core.option.Option.Insts.CoreCloneClone.clone,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index]
-/
#guard_msgs in
#print axioms Tacenta.DispatchEvidenceVacuity.record_empty_ct1Sampled_ek

/--
info: Tacenta.DispatchEvidenceVacuity.record_empty_ct1Sampled_ek {K : Model.Braid.Kem} {view : Model.Lifecycle.CodewordView}
  {real : tacenta_session_unit.lifecycle.Session} {model : Model.Lifecycle.Session} {message : Slice U8} (e : ℕ)
  (he : e < 2 ^ 64) (auth : Model.Braid.Auth) (ekSeed hek encapsSecret ct1 : Model.Braid.Bytes)
  (enc : Model.Braid.Encoder) (d : Model.Braid.Decoder)
  (hmodel : model.braid = Model.Braid.BraidState.ct1Sampled e auth ekSeed hek encapsSecret ct1 enc d)
  (c0 : Model.Braid.Chunk) (hc0 : c0 ∈ d.chunks) :
  ¬Nonempty (Tacenta.UnitLifecycleT3.InitialRatchetBraidEvidenceContracts view real model message)
-/
#guard_msgs in
#check Tacenta.DispatchEvidenceVacuity.record_empty_ct1Sampled_ek

/--
info: 'Tacenta.DispatchEvidenceVacuity.record_empty_ct1Sampled_ekCt1Ack' depends on axioms: [propext,
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
 tacenta_session_unit.tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.core.option.Option.Insts.CoreCloneClone.clone,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index]
-/
#guard_msgs in
#print axioms Tacenta.DispatchEvidenceVacuity.record_empty_ct1Sampled_ekCt1Ack

/--
info: Tacenta.DispatchEvidenceVacuity.record_empty_ct1Sampled_ekCt1Ack {K : Model.Braid.Kem}
  {view : Model.Lifecycle.CodewordView} {real : tacenta_session_unit.lifecycle.Session}
  {model : Model.Lifecycle.Session} {message : Slice U8} (e : ℕ) (he : e < 2 ^ 64) (auth : Model.Braid.Auth)
  (ekSeed hek encapsSecret ct1 : Model.Braid.Bytes) (enc : Model.Braid.Encoder) (d : Model.Braid.Decoder)
  (hmodel : model.braid = Model.Braid.BraidState.ct1Sampled e auth ekSeed hek encapsSecret ct1 enc d)
  (c0 : Model.Braid.Chunk) (hc0 : c0 ∈ d.chunks) :
  ¬Nonempty (Tacenta.UnitLifecycleT3.InitialRatchetBraidEvidenceContracts view real model message)
-/
#guard_msgs in
#check Tacenta.DispatchEvidenceVacuity.record_empty_ct1Sampled_ekCt1Ack

/--
info: 'Tacenta.DispatchEvidenceVacuity.record_empty_ct1Acknowledged' depends on axioms: [propext,
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
 tacenta_session_unit.tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.core.option.Option.Insts.CoreCloneClone.clone,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index]
-/
#guard_msgs in
#print axioms Tacenta.DispatchEvidenceVacuity.record_empty_ct1Acknowledged

/--
info: Tacenta.DispatchEvidenceVacuity.record_empty_ct1Acknowledged {K : Model.Braid.Kem} {view : Model.Lifecycle.CodewordView}
  {real : tacenta_session_unit.lifecycle.Session} {model : Model.Lifecycle.Session} {message : Slice U8} (e : ℕ)
  (he : e < 2 ^ 64) (auth : Model.Braid.Auth) (ekSeed hek encapsSecret ct1 : Model.Braid.Bytes)
  (d : Model.Braid.Decoder)
  (hmodel : model.braid = Model.Braid.BraidState.ct1Acknowledged e auth ekSeed hek encapsSecret ct1 d)
  (c0 : Model.Braid.Chunk) (hc0 : c0 ∈ d.chunks) :
  ¬Nonempty (Tacenta.UnitLifecycleT3.InitialRatchetBraidEvidenceContracts view real model message)
-/
#guard_msgs in
#check Tacenta.DispatchEvidenceVacuity.record_empty_ct1Acknowledged

/--
info: 'Tacenta.DispatchEvidenceVacuity.keysSampled_receive_ct1_holds_chunk' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.DispatchEvidenceVacuity.keysSampled_receive_ct1_holds_chunk

/--
info: Tacenta.DispatchEvidenceVacuity.keysSampled_receive_ct1_holds_chunk (K : Model.Braid.Kem) (epoch : ℕ)
  (auth : Model.Braid.Auth) (dk ekVector : Model.Braid.Bytes) (hdrEnc : Model.Braid.Encoder) (c : Model.Braid.Chunk) :
  ∃ enc,
    (Model.Braid.receive K (Model.Braid.BraidState.keysSampled epoch auth dk ekVector hdrEnc)
              { epoch := epoch, type := Model.Braid.MsgType.ct1, data := some c }).2.2 =
        Model.Braid.BraidState.headerSent epoch auth dk ((Model.Braid.Decoder.new K.ct1Size).addChunk c) enc ∧
      c ∈ ((Model.Braid.Decoder.new K.ct1Size).addChunk c).chunks
-/
#guard_msgs in
#check Tacenta.DispatchEvidenceVacuity.keysSampled_receive_ct1_holds_chunk

/--
info: 'Tacenta.DispatchEvidenceVacuity.tripleConcreteEvidence_forces_constant_dhPublic' depends on axioms: [propext,
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
#print axioms Tacenta.DispatchEvidenceVacuity.tripleConcreteEvidence_forces_constant_dhPublic

/--
info: Tacenta.DispatchEvidenceVacuity.tripleConcreteEvidence_forces_constant_dhPublic {R : Type}
  {rc : tacenta_session_unit.rand_core_1.RngCore R} {crc : tacenta_session_unit.rand_core_1.CryptoRng R}
  {trace : R → List Model.Lifecycle.Key} {dh : Tacenta.UnitLifecycleT3.DhView} {K : Model.Braid.Kem}
  {view : Model.Lifecycle.CodewordView} {oracle : Model.Lifecycle.Oracle}
  {real : tacenta_session_unit.lifecycle.Session} {model : Model.Lifecycle.Session} {message : Slice U8} {rng : R}
  {input : Tacenta.UnitLifecycleT3.InitialRatchetRefusalBranchInput message rng}
  {realReason : tacenta_session_unit.tacenta_triple.TripleError} {modelComposite : Model.CompositeHeader.Composite}
  {modelReason : Model.Triple.ReceiveRefusal}
  (ev : Tacenta.UnitLifecycleT3.InitialRatchetTripleConcreteEvidence input realReason modelComposite modelReason)
  (pref :
    Tacenta.UnitLifecycleT3.InitialRatchetTripleRefusalPrefix rc crc real input.decoded.message.deref rng input.rngNext
      realReason input.next)
  (d1 d2 : Model.Lifecycle.Key) : oracle.dhPublic d1 = oracle.dhPublic d2
-/
#guard_msgs in
#check Tacenta.DispatchEvidenceVacuity.tripleConcreteEvidence_forces_constant_dhPublic

/--
info: 'Tacenta.DispatchEvidenceVacuity.aeadConcreteEvidence_forces_constant_dhPublic' depends on axioms: [propext,
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
#print axioms Tacenta.DispatchEvidenceVacuity.aeadConcreteEvidence_forces_constant_dhPublic

/--
info: Tacenta.DispatchEvidenceVacuity.aeadConcreteEvidence_forces_constant_dhPublic {R : Type}
  {rc : tacenta_session_unit.rand_core_1.RngCore R} {crc : tacenta_session_unit.rand_core_1.CryptoRng R}
  {trace : R → List Model.Lifecycle.Key} {dh : Tacenta.UnitLifecycleT3.DhView} {K : Model.Braid.Kem}
  {view : Model.Lifecycle.CodewordView} {oracle : Model.Lifecycle.Oracle}
  {real : tacenta_session_unit.lifecycle.Session} {model : Model.Lifecycle.Session} {message : Slice U8} {rng : R}
  {input : Tacenta.UnitLifecycleT3.InitialRatchetRefusalBranchInput message rng}
  {modelComposite : Model.CompositeHeader.Composite} {modelTripleCandidate : Model.Triple.State}
  {modelMk : Model.Lifecycle.Key}
  (ev : Tacenta.UnitLifecycleT3.InitialRatchetAeadConcreteEvidence input modelComposite modelTripleCandidate modelMk)
  (pref :
    Tacenta.UnitLifecycleT3.InitialRatchetAeadRefusalPrefix rc crc real input.decoded.message.deref rng input.rngNext
      input.next)
  (d1 d2 : Model.Lifecycle.Key) : oracle.dhPublic d1 = oracle.dhPublic d2
-/
#guard_msgs in
#check Tacenta.DispatchEvidenceVacuity.aeadConcreteEvidence_forces_constant_dhPublic

/--
info: 'Tacenta.DispatchEvidenceVacuity.constant_dhPublic_false_of_publicKeyNotConstant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.from_bytes]
-/
#guard_msgs in
#print axioms Tacenta.DispatchEvidenceVacuity.constant_dhPublic_false_of_publicKeyNotConstant

/--
info: Tacenta.DispatchEvidenceVacuity.constant_dhPublic_false_of_publicKeyNotConstant {dh : Tacenta.UnitLifecycleT3.DhView}
  {oracle : Model.Lifecycle.Oracle} (codec : Tacenta.UnitLifecycleT3.DhCodecOf dh)
  (hdh : Tacenta.DispatchEvidenceVacuity.OracleDhPublic dh oracle)
  (hfact : Tacenta.DispatchEvidenceVacuity.PublicKeyNotConstant)
  (hconst : ∀ (d1 d2 : Model.Lifecycle.Key), oracle.dhPublic d1 = oracle.dhPublic d2) : False
-/
#guard_msgs in
#check Tacenta.DispatchEvidenceVacuity.constant_dhPublic_false_of_publicKeyNotConstant

/--
info: 'Tacenta.DispatchEvidenceVacuity.tripleConcreteEvidence_false_of_publicKeyNotConstant' depends on axioms: [propext,
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
#print axioms Tacenta.DispatchEvidenceVacuity.tripleConcreteEvidence_false_of_publicKeyNotConstant

/--
info: Tacenta.DispatchEvidenceVacuity.tripleConcreteEvidence_false_of_publicKeyNotConstant {R : Type}
  {rc : tacenta_session_unit.rand_core_1.RngCore R} {crc : tacenta_session_unit.rand_core_1.CryptoRng R}
  {trace : R → List Model.Lifecycle.Key} {dh : Tacenta.UnitLifecycleT3.DhView} {K : Model.Braid.Kem}
  {view : Model.Lifecycle.CodewordView} {oracle : Model.Lifecycle.Oracle}
  {real : tacenta_session_unit.lifecycle.Session} {model : Model.Lifecycle.Session} {message : Slice U8} {rng : R}
  {input : Tacenta.UnitLifecycleT3.InitialRatchetRefusalBranchInput message rng}
  {realReason : tacenta_session_unit.tacenta_triple.TripleError} {modelComposite : Model.CompositeHeader.Composite}
  {modelReason : Model.Triple.ReceiveRefusal}
  (ev : Tacenta.UnitLifecycleT3.InitialRatchetTripleConcreteEvidence input realReason modelComposite modelReason)
  (pref :
    Tacenta.UnitLifecycleT3.InitialRatchetTripleRefusalPrefix rc crc real input.decoded.message.deref rng input.rngNext
      realReason input.next)
  (codec : Tacenta.UnitLifecycleT3.DhCodecOf dh) (hdh : Tacenta.DispatchEvidenceVacuity.OracleDhPublic dh oracle)
  (hfact : Tacenta.DispatchEvidenceVacuity.PublicKeyNotConstant) : False
-/
#guard_msgs in
#check Tacenta.DispatchEvidenceVacuity.tripleConcreteEvidence_false_of_publicKeyNotConstant

/--
info: 'Tacenta.DispatchEvidenceVacuity.aeadConcreteEvidence_false_of_publicKeyNotConstant' depends on axioms: [propext,
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
#print axioms Tacenta.DispatchEvidenceVacuity.aeadConcreteEvidence_false_of_publicKeyNotConstant

/--
info: Tacenta.DispatchEvidenceVacuity.aeadConcreteEvidence_false_of_publicKeyNotConstant {R : Type}
  {rc : tacenta_session_unit.rand_core_1.RngCore R} {crc : tacenta_session_unit.rand_core_1.CryptoRng R}
  {trace : R → List Model.Lifecycle.Key} {dh : Tacenta.UnitLifecycleT3.DhView} {K : Model.Braid.Kem}
  {view : Model.Lifecycle.CodewordView} {oracle : Model.Lifecycle.Oracle}
  {real : tacenta_session_unit.lifecycle.Session} {model : Model.Lifecycle.Session} {message : Slice U8} {rng : R}
  {input : Tacenta.UnitLifecycleT3.InitialRatchetRefusalBranchInput message rng}
  {modelComposite : Model.CompositeHeader.Composite} {modelTripleCandidate : Model.Triple.State}
  {modelMk : Model.Lifecycle.Key}
  (ev : Tacenta.UnitLifecycleT3.InitialRatchetAeadConcreteEvidence input modelComposite modelTripleCandidate modelMk)
  (pref :
    Tacenta.UnitLifecycleT3.InitialRatchetAeadRefusalPrefix rc crc real input.decoded.message.deref rng input.rngNext
      input.next)
  (codec : Tacenta.UnitLifecycleT3.DhCodecOf dh) (hdh : Tacenta.DispatchEvidenceVacuity.OracleDhPublic dh oracle)
  (hfact : Tacenta.DispatchEvidenceVacuity.PublicKeyNotConstant) : False
-/
#guard_msgs in
#check Tacenta.DispatchEvidenceVacuity.aeadConcreteEvidence_false_of_publicKeyNotConstant

/--
info: 'Tacenta.DispatchEvidenceVacuity.oracleOf_kem_oracle_never_refuses' depends on axioms: [propext,
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
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.as_bytes]
-/
#guard_msgs in
#print axioms Tacenta.DispatchEvidenceVacuity.oracleOf_kem_oracle_never_refuses

/--
info: Tacenta.DispatchEvidenceVacuity.oracleOf_kem_oracle_never_refuses {R : Type}
  {rc : tacenta_session_unit.rand_core_1.RngCore R} {crc : tacenta_session_unit.rand_core_1.CryptoRng R}
  {trace : R → List Model.Lifecycle.Key} {dh : Tacenta.UnitLifecycleT3.DhView} {kem : Tacenta.UnitLifecycleT3.KemView}
  {oracle : Model.Lifecycle.Oracle} (oracleOf : Tacenta.UnitLifecycleT3.OracleOf rc crc dh kem trace oracle)
  (publicKey : Slice U8) (rng : R) (draw : Model.Lifecycle.Key) (rest : List Model.Lifecycle.Key)
  (h : trace rng = draw :: rest) : ∃ r, oracle.kemEncaps (Tacenta.UnitLifecycleT3.sliceOf publicKey) draw = some r
-/
#guard_msgs in
#check Tacenta.DispatchEvidenceVacuity.oracleOf_kem_oracle_never_refuses

/--
info: 'Tacenta.DispatchEvidenceVacuity.oracleOf_kem_call_never_errs' depends on axioms: [propext,
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
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.as_bytes]
-/
#guard_msgs in
#print axioms Tacenta.DispatchEvidenceVacuity.oracleOf_kem_call_never_errs

/--
info: Tacenta.DispatchEvidenceVacuity.oracleOf_kem_call_never_errs {R : Type}
  {rc : tacenta_session_unit.rand_core_1.RngCore R} {crc : tacenta_session_unit.rand_core_1.CryptoRng R}
  {trace : R → List Model.Lifecycle.Key} {dh : Tacenta.UnitLifecycleT3.DhView} {kem : Tacenta.UnitLifecycleT3.KemView}
  {oracle : Model.Lifecycle.Oracle} (oracleOf : Tacenta.UnitLifecycleT3.OracleOf rc crc dh kem trace oracle)
  (publicKey : Slice U8) (rng : R) (draw : Model.Lifecycle.Key) (rest : List Model.Lifecycle.Key)
  (h : trace rng = draw :: rest) (rng' : R) (error : tacenta_session_unit.tacenta_boundary.kem.KemError) :
  tacenta_session_unit.tacenta_boundary.kem.encapsulate rc crc publicKey rng ≠ ok (core.result.Result.Err error, rng')
-/
#guard_msgs in
#check Tacenta.DispatchEvidenceVacuity.oracleOf_kem_call_never_errs
