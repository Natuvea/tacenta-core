import Translation.TacentaSessionUnit
import Translation.SessionUnitSessionT1
import Translation.SessionUnitTripleT1
import Translation.SessionUnitWireT1

/-!
# Session lifecycle primitive boundary

The complete Session unit leaves primitive implementations opaque.  These nine
contracts state only that each call returns through Aeneas's outer `Result`;
an inner `Err` or a non-contributory `None` remains an ordinary result.  They
do not assume cryptographic correctness.

The DH codec operations share opaque key types and are deliberately one
contract.  This prevents separate non-vacuity witnesses from choosing
incompatible interpretations for construction, projection, derivation and
equality.
-/

namespace Tacenta.UnitLifecycleT1

open Aeneas Aeneas.Std Result
open tacenta_session_unit

abbrev NoPanic {α : Type} (e : Result α) : Prop := ∃ r, e = ok r

def DhCodecTotal : Prop :=
  (∀ a, NoPanic (tacenta_boundary.dh.PrivateKey.from_bytes a)) ∧
  (∀ k, NoPanic (tacenta_boundary.dh.PrivateKey.public_key k)) ∧
  (∀ k, NoPanic (tacenta_boundary.dh.PrivateKey.to_bytes k)) ∧
  (∀ a, NoPanic (tacenta_boundary.dh.PublicKeyBytes.from_bytes a)) ∧
  (∀ k, NoPanic (tacenta_boundary.dh.PublicKeyBytes.as_bytes k)) ∧
  (∀ a b, NoPanic
    (tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq a b))

def DhAgreeTotal : Prop :=
  ∀ k p, NoPanic (tacenta_boundary.dh.PrivateKey.agree k p)

def AeadOpenTotal : Prop :=
  ∀ ek mk nonce ciphertext ad,
    NoPanic (tacenta_boundary.aead.decrypt ek mk nonce ciphertext ad)

def KemEncapsulateTotal : Prop :=
  ∀ {R : Type} (rngCore : rand_core_1.RngCore R)
    (cryptoRng : rand_core_1.CryptoRng R) publicKey rng,
    NoPanic (tacenta_boundary.kem.encapsulate rngCore cryptoRng publicKey rng)

def KemDecapsulateTotal : Prop :=
  ∀ keyPair ciphertext,
    NoPanic (tacenta_boundary.kem.decapsulate keyPair ciphertext)

def KemCiphertextLenTotal : Prop :=
  NoPanic tacenta_boundary.kem.ciphertext_len

def XeddsaVerifyTotal : Prop :=
  ∀ publicKey message signature,
    NoPanic (tacenta_boundary.xeddsa.verify publicKey message signature)

def XeddsaSignTotal : Prop :=
  ∀ {R : Type} (rngCore : rand_core_1.RngCore R)
    (cryptoRng : rand_core_1.CryptoRng R) secret message rng,
    NoPanic (tacenta_boundary.xeddsa.sign rngCore cryptoRng secret message rng)

/-- Totality is required of the concrete RNG instance passed to a lifecycle
operation.  Quantifying over every possible `RngCore` record would be false:
the trait permits an implementation whose `fill_bytes` itself fails. -/
def Random32Total {R : Type} (rngCore : rand_core_1.RngCore R) : Prop :=
  ∀ rng bytes, bytes.val.length = 32 → NoPanic (rngCore.fill_bytes rng bytes)

/-! ## Primitive-boundary stepping rules -/

@[step] theorem private_key_from_bytes_no_panic (h : DhCodecTotal)
    (a : Array U8 32#usize) :
    tacenta_boundary.dh.PrivateKey.from_bytes a ⦃ fun _ => True ⦄ :=
  (Tacenta.SessionUnitT1.noPanic_iff _).2 (h.1 a)

@[step] theorem private_key_public_no_panic (h : DhCodecTotal)
    (k : tacenta_boundary.dh.PrivateKey) :
    tacenta_boundary.dh.PrivateKey.public_key k ⦃ fun _ => True ⦄ :=
  (Tacenta.SessionUnitT1.noPanic_iff _).2 (h.2.1 k)

@[step] theorem private_key_to_bytes_no_panic (h : DhCodecTotal)
    (k : tacenta_boundary.dh.PrivateKey) :
    tacenta_boundary.dh.PrivateKey.to_bytes k ⦃ fun _ => True ⦄ :=
  (Tacenta.SessionUnitT1.noPanic_iff _).2 (h.2.2.1 k)

@[step] theorem public_key_from_bytes_no_panic (h : DhCodecTotal)
    (a : Array U8 32#usize) :
    tacenta_boundary.dh.PublicKeyBytes.from_bytes a ⦃ fun _ => True ⦄ :=
  (Tacenta.SessionUnitT1.noPanic_iff _).2 (h.2.2.2.1 a)

@[step] theorem private_key_agree_no_panic (h : DhAgreeTotal)
    (k : tacenta_boundary.dh.PrivateKey)
    (p : tacenta_boundary.dh.PublicKeyBytes) :
    tacenta_boundary.dh.PrivateKey.agree k p ⦃ fun _ => True ⦄ :=
  (Tacenta.SessionUnitT1.noPanic_iff _).2 (h k p)

@[step] theorem aead_open_no_panic (h : AeadOpenTotal)
    (ek mk : Array U8 32#usize) (nonce : Array U8 16#usize)
    (ciphertext ad : Slice U8) :
    tacenta_boundary.aead.decrypt ek mk nonce ciphertext ad ⦃ fun _ => True ⦄ :=
  (Tacenta.SessionUnitT1.noPanic_iff _).2 (h ek mk nonce ciphertext ad)

@[step] theorem kem_encapsulate_no_panic {R : Type}
    (h : KemEncapsulateTotal) (rc : rand_core_1.RngCore R)
    (crc : rand_core_1.CryptoRng R) (pk : Slice U8) (rng : R) :
    tacenta_boundary.kem.encapsulate rc crc pk rng ⦃ fun _ => True ⦄ :=
  (Tacenta.SessionUnitT1.noPanic_iff _).2 (h rc crc pk rng)

@[step] theorem kem_decapsulate_no_panic (h : KemDecapsulateTotal)
    (kp : tacenta_boundary.kem.KeyPair) (ct : Slice U8) :
    tacenta_boundary.kem.decapsulate kp ct ⦃ fun _ => True ⦄ :=
  (Tacenta.SessionUnitT1.noPanic_iff _).2 (h kp ct)

@[step] theorem kem_ciphertext_len_no_panic (h : KemCiphertextLenTotal) :
    tacenta_boundary.kem.ciphertext_len ⦃ fun _ => True ⦄ :=
  (Tacenta.SessionUnitT1.noPanic_iff _).2 h

@[step] theorem xeddsa_verify_no_panic (h : XeddsaVerifyTotal)
    (pk : tacenta_boundary.dh.PublicKeyBytes) (message : Slice U8)
    (sig : Array U8 64#usize) :
    tacenta_boundary.xeddsa.verify pk message sig ⦃ fun _ => True ⦄ :=
  (Tacenta.SessionUnitT1.noPanic_iff _).2 (h pk message sig)

@[step] theorem xeddsa_sign_no_panic {R : Type} (h : XeddsaSignTotal)
    (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R)
    (secret : Array U8 32#usize) (message : Slice U8) (rng : R) :
    tacenta_boundary.xeddsa.sign rc crc secret message rng ⦃ fun _ => True ⦄ :=
  (Tacenta.SessionUnitT1.noPanic_iff _).2 (h rc crc secret message rng)

@[step] theorem random_secret_no_panic {R : Type}
    (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R)
    (h : Random32Total rc) (rng : R) :
    lifecycle.random_secret rc crc rng ⦃ fun _ => True ⦄ := by
  unfold lifecycle.random_secret
  step
  rename_i buffer back hbuffer hback
  have hlen : buffer.val.length = 32 := by
    rw [hbuffer]
    simp
  obtain ⟨result, hresult⟩ := h rng buffer hlen
  rw [hresult]
  rcases result
  simp

/-! ## Pure lifecycle adapters

These conversions sit above the primitive boundary and cannot fail.  Keeping
their panic-freedom explicit gives the later Session proofs named steps instead
of asking automation to unfold wire and Braid representations at every call.
-/

@[step]
theorem agreement_type_of_no_panic (t : tacenta_braid.MsgType) :
    lifecycle.agreement_type_of t ⦃ fun _ => True ⦄ := by
  rcases t with _ | _ | _ | _ | _ | _ <;>
    simp [lifecycle.agreement_type_of]

@[step]
theorem msg_type_of_no_panic (t : tacenta_wire.AgreementType) :
    lifecycle.msg_type_of t ⦃ fun _ => True ⦄ := by
  rcases t with _ | _ | _ | _ | _ | _ <;>
    simp [lifecycle.msg_type_of]

@[step]
theorem composite_of_no_panic (h : tacenta_triple.Header) (m : tacenta_braid.Msg) :
    lifecycle.composite_of h m ⦃ fun _ => True ⦄ := by
  unfold lifecycle.composite_of
  step
  rcases m.data with _ | _ <;> simp

@[step]
theorem msg_of_no_panic (c : tacenta_wire.Composite) :
    lifecycle.msg_of c ⦃ fun _ => True ⦄ := by
  unfold lifecycle.msg_of
  step
  rcases c.ag_chunk with _ | _ <;> simp

@[step]
theorem triple_header_of_no_panic (c : tacenta_wire.Composite) :
    lifecycle.triple_header_of c ⦃ fun _ => True ⦄ := by
  simp [lifecycle.triple_header_of]

@[step]
theorem public_key_as_bytes_no_panic (hdh : DhCodecTotal)
    (pk : tacenta_boundary.dh.PublicKeyBytes) :
    tacenta_boundary.dh.PublicKeyBytes.as_bytes pk ⦃ fun _ => True ⦄ := by
  exact (Tacenta.SessionUnitT1.noPanic_iff _).2 (hdh.2.2.2.2.1 pk)

@[step]
theorem encode_ec_spec (hdh : DhCodecTotal)
    (pk : tacenta_boundary.dh.PublicKeyBytes) :
    encode_ec pk ⦃ fun r => r.val.length = 33 ⦄ := by
  unfold encode_ec
  obtain ⟨a, ha⟩ := hdh.2.2.2.2.1 pk
  rw [ha]
  refine Std.WP.spec_mono
    (Tacenta.SessionUnitSessionT1.encode_ec_spec a) ?_
  intro r hr
  simp [hr]

@[step]
theorem identity_ad_no_panic (hdh : DhCodecTotal)
    (initiator responder : tacenta_boundary.dh.PublicKeyBytes) :
    lifecycle.identity_ad initiator responder ⦃ fun _ => True ⦄ := by
  unfold lifecycle.identity_ad
  step*
  change v.val.length + v1.val.length ≤ Usize.max
  rw [v_post, v1_post]
  exact Tacenta.SessionUnitSessionT1.small_le_usize_max (by omega)

@[step]
theorem message_type_no_panic (bytes : Slice U8) :
    serialization.message_type bytes ⦃ fun _ => True ⦄ := by
  unfold serialization.message_type
  step*

@[step]
theorem decode_initial_no_panic (bytes : Slice U8) :
    tacenta_wire.decode_initial bytes ⦃ fun _ => True ⦄ :=
  Tacenta.SessionUnitWireT1.decode_initial_no_panic bytes

@[step]
theorem decode_message_no_panic (bytes : Slice U8) :
    tacenta_wire.decode_message bytes ⦃ fun _ => True ⦄ :=
  Tacenta.SessionUnitWireT1.decode_message_no_panic bytes

@[step]
theorem agreement_type_to_byte_no_panic (t : tacenta_wire.AgreementType) :
    tacenta_wire.AgreementType.to_byte t ⦃ fun _ => True ⦄ := by
  rcases t with _ | _ | _ | _ | _ | _ <;>
    simp [tacenta_wire.AgreementType.to_byte]

@[step]
theorem encode_composite_no_panic (h : tacenta_wire.Composite) :
    tacenta_wire.encode_composite h ⦃ fun out => out.val.length = 102 ⦄ := by
  unfold tacenta_wire.encode_composite
  step*
  all_goals
    simp_all [alloc.vec.Vec.with_capacity, Array.repeat] <;>
      try (have hmax : 102 ≤ Usize.max :=
        Tacenta.SessionUnitSessionT1.small_le_usize_max (by omega); omega)

@[step]
theorem concat_ad_no_panic (ad : Slice U8) (header : tacenta_wire.Composite)
    (hroom : ad.val.length + 106 ≤ Usize.max) :
    serialization.concat_ad ad header ⦃ fun out =>
      out.val.length = ad.val.length + 106 ⦄ := by
  unfold serialization.concat_ad
  step with encode_composite_no_panic header
  have hencoded : encoded.deref.val.length = 102 := by
    change encoded.val.length = 102
    exact encoded_post
  step*
  all_goals (simp_all [alloc.vec.Vec.with_capacity]; omega)

@[step]
theorem encode_message_no_panic (header : tacenta_wire.Composite)
    (ciphertext : Slice U8)
    (hroom : 102 + ciphertext.val.length ≤ Usize.max) :
    serialization.encode_message header ciphertext ⦃ fun out =>
      out.val.length = 102 + ciphertext.val.length ⦄ := by
  unfold serialization.encode_message
  step*

@[step]
theorem encode_initial_no_panic
    (identity ephemeral kemCiphertext message : Slice U8)
    (signedPrekeyId oneTimePrekeyId kemPrekeyId : U32)
    (hroom : identity.val.length + ephemeral.val.length
      + kemCiphertext.val.length + message.val.length + 18 ≤ Usize.max) :
    serialization.encode_initial identity ephemeral kemCiphertext signedPrekeyId
      oneTimePrekeyId kemPrekeyId message ⦃ fun out =>
        out.val.length = identity.val.length + ephemeral.val.length
          + kemCiphertext.val.length + message.val.length + 18 ⦄ := by
  unfold serialization.encode_initial
  step*
  all_goals (simp_all; omega)

/-! ## Full-store retry helpers

The public receive path retries a Triple receive after evicting old skipped
keys.  These pure helpers choose the affected half and the first eviction
batch.  The explicit saturating conversion in Rust keeps the latter inside
the translated surface instead of introducing an eleventh primitive contract.
-/

@[step]
theorem full_store_no_panic (e : tacenta_triple.TripleError) :
    lifecycle.full_store e ⦃ fun _ => True ⦄ := by
  rcases e with e | e <;> rcases e <;> simp [lifecycle.full_store]

@[step]
theorem saturating_usize_from_u64_no_panic (value : U64) :
    lifecycle.saturating_usize_from_u64 value ⦃ fun _ => True ⦄ := by
  apply (Tacenta.SessionUnitT1.noPanic_iff _).2
  simp [lifecycle.saturating_usize_from_u64, lift]
  split <;> simp

@[step]
theorem receive_shortfall_no_panic
    (half : lifecycle.FullStore) (state : tacenta_triple.State)
    (composite : tacenta_wire.Composite) :
    lifecycle.receive_shortfall half state composite ⦃ fun _ => True ⦄ := by
  apply (Tacenta.SessionUnitT1.noPanic_iff _).2
  rcases half
  · simp [lifecycle.receive_shortfall,
      tacenta_triple.State.classical_skipped_len,
      tacenta_ratchet.State.skipped_len,
      tacenta_triple.State.receive_count,
      tacenta_ratchet.State.receive_count, lift]
    split <;> simp
  · obtain ⟨o, ho⟩ := (Tacenta.SessionUnitT1.noPanic_iff _).mp
      (Tacenta.SessionUnitTripleT1.State.post_quantum_receive_count_no_panic
        state composite.pq_epoch)
    rcases o with _ | received
    · simp [lifecycle.receive_shortfall, ho]
    · obtain ⟨held, hheld⟩ := (Tacenta.SessionUnitT1.noPanic_iff _).mp
        (Tacenta.SessionUnitTripleT1.State.post_quantum_skipped_len_no_panic state)
      obtain ⟨need, hneed⟩ := (Tacenta.SessionUnitT1.noPanic_iff _).mp
        (saturating_usize_from_u64_no_panic
          (core.num.U64.saturating_sub
            (core.num.U64.saturating_sub composite.pq_n 1#u64) received))
      simp [lifecycle.receive_shortfall, ho, hheld, lift, hneed]
      split <;> simp

/-! The classical eviction walks the skipped-key vector to find the oldest
entry, then removes exactly one entry per outer turn.  The inner invariant
keeps both indices in range; the outer measure is the requested count minus
the number already removed. -/

theorem ratchet_evict_find_no_panic
    (v : alloc.vec.Vec tacenta_ratchet.SkippedKey) (oldest i : Usize)
    (hold : oldest.val < v.val.length) (hi : i.val ≤ v.val.length) :
    tacenta_ratchet.State.evict_oldest_loop0_loop0 v oldest i ⦃ fun r =>
      r.val < v.val.length ⦄ := by
  unfold tacenta_ratchet.State.evict_oldest_loop0_loop0
  apply loop.spec_decr_nat
    (measure := fun p => v.val.length - (Prod.snd p).val)
    (inv := fun p => (Prod.fst p).val < v.val.length ∧
      (Prod.snd p).val ≤ v.val.length)
  · rintro ⟨oldest1, i1⟩ ⟨hold1, hi1⟩
    simp only [tacenta_ratchet.State.evict_oldest_loop0_loop0.body]
    by_cases hlt : i1.val < v.val.length
    · step* <;> simp_all
      all_goals (split <;> step* <;> simp_all <;> omega)
    · step*
  · exact ⟨hold, hi⟩

theorem ratchet_evict_loop_no_panic
    (hrm : Tacenta.SessionUnitT1.RemoveSkippedAtTotal)
    (self : tacenta_ratchet.State) (count evicted : Usize) :
    tacenta_ratchet.State.evict_oldest_loop0 self count evicted
      ⦃ fun r => r.2.skipped.val.length ≤ self.skipped.val.length ∧
        (evicted.val < r.1.val →
          r.2.skipped.val.length < self.skipped.val.length) ⦄ := by
  unfold tacenta_ratchet.State.evict_oldest_loop0
  apply loop.spec_decr_nat
    (measure := fun p => count.val - (Prod.snd p).val)
    (inv := fun p => evicted.val ≤ (Prod.snd p).val ∧
      (Prod.fst p).skipped.val.length ≤ self.skipped.val.length ∧
      (evicted.val < (Prod.snd p).val →
        (Prod.fst p).skipped.val.length < self.skipped.val.length))
  · rintro ⟨state, n⟩ hinv
    simp only at hinv
    simp only [tacenta_ratchet.State.evict_oldest_loop0.body]
    split
    · simp only [alloc.vec.Vec.len]
      split
      · step with ratchet_evict_find_no_panic state.skipped 0#usize 1#usize
          (by scalar_tac) (by scalar_tac)
        obtain ⟨⟨removed, skipped⟩, hremove, hshort⟩ :=
          hrm.lengths Global state.skipped oldest (by simpa using oldest_post)
        simp only [hremove]
        step* <;> simp_all <;> omega
      · simpa using And.intro hinv.2.1 hinv.2.2
    · simpa using And.intro hinv.2.1 hinv.2.2
  · exact ⟨le_refl _, le_refl _, fun h => (lt_irrefl _ h).elim⟩

@[step]
theorem ratchet_evict_oldest_no_panic
    (hrm : Tacenta.SessionUnitT1.RemoveSkippedAtTotal)
    (self : tacenta_ratchet.State) (count : Usize) :
    tacenta_ratchet.State.evict_oldest self count ⦃ fun r =>
      r.2.skipped.val.length ≤ self.skipped.val.length ∧
      (0 < r.1.val → r.2.skipped.val.length < self.skipped.val.length) ⦄ := by
  unfold tacenta_ratchet.State.evict_oldest
  exact ratchet_evict_loop_no_panic hrm self count 0#usize

/-! Sparse eviction delegates each removal to the leaf's already proved
wipe-before-pop helper, then wipes the discarded key value.  Reusing that
helper avoids adding a second assumption for the same opaque `Vec::pop`. -/

theorem spqr_evict_loop_no_panic
    (hrm : Tacenta.SessionUnitSpqrT1.RemoveSkippedAtTotal)
    (hz : Tacenta.SessionUnitSpqrT1.ZeroizeTotal)
    (self : tacenta_spqr.State) (count evicted : Usize) :
    tacenta_spqr.State.evict_oldest_loop self count evicted
      ⦃ fun r => r.2.chains = self.chains ∧
        r.2.skipped.val.length ≤ self.skipped.val.length ∧
        (evicted.val < r.1.val →
          r.2.skipped.val.length < self.skipped.val.length) ⦄ := by
  unfold tacenta_spqr.State.evict_oldest_loop
  apply loop.spec_decr_nat
    (measure := fun p => count.val - (Prod.snd p).val)
    (inv := fun p => evicted.val ≤ (Prod.snd p).val ∧
      (Prod.fst p).chains = self.chains ∧
      (Prod.fst p).skipped.val.length ≤ self.skipped.val.length ∧
      (evicted.val < (Prod.snd p).val →
        (Prod.fst p).skipped.val.length < self.skipped.val.length))
  · rintro ⟨state, n⟩ hinv
    simp only at hinv
    simp only [tacenta_spqr.State.evict_oldest_loop.body]
    split
    · simp only [alloc.vec.Vec.len]
      split
      · obtain ⟨⟨discarded, skipped⟩, hremove, hshort⟩ :=
          hrm state.skipped 0#usize (by scalar_tac)
        simp only [hremove]
        step*
      · simpa using ⟨hinv.2.1, hinv.2.2.1, hinv.2.2.2⟩
    · simpa using ⟨hinv.2.1, hinv.2.2.1, hinv.2.2.2⟩
  · exact ⟨le_refl _, rfl, le_refl _, fun h => (lt_irrefl _ h).elim⟩

@[step]
theorem spqr_evict_oldest_no_panic
    (hrm : Tacenta.SessionUnitSpqrT1.RemoveSkippedAtTotal)
    (hz : Tacenta.SessionUnitSpqrT1.ZeroizeTotal)
    (self : tacenta_spqr.State) (count : Usize) :
    tacenta_spqr.State.evict_oldest self count ⦃ fun r =>
      r.2.chains = self.chains ∧
      r.2.skipped.val.length ≤ self.skipped.val.length ∧
      (0 < r.1.val → r.2.skipped.val.length < self.skipped.val.length) ⦄ := by
  unfold tacenta_spqr.State.evict_oldest
  exact spqr_evict_loop_no_panic hrm hz self count 0#usize

@[step]
theorem triple_evict_oldest_classical_no_panic
    (hrm : Tacenta.SessionUnitT1.RemoveSkippedAtTotal)
    (self : tacenta_triple.State) (count : Usize) :
    tacenta_triple.State.evict_oldest_classical self count
      ⦃ fun r => r.2.classical.skipped.val.length ≤
        self.classical.skipped.val.length ∧
        (0 < r.1.val → r.2.classical.skipped.val.length <
          self.classical.skipped.val.length) ∧
        r.2.post_quantum = self.post_quantum ⦄ := by
  unfold tacenta_triple.State.evict_oldest_classical
  step with ratchet_evict_oldest_no_panic hrm self.classical count
  exact ⟨i_post1, i_post2⟩

@[step]
theorem triple_evict_oldest_post_quantum_no_panic
    (hrm : Tacenta.SessionUnitSpqrT1.RemoveSkippedAtTotal)
    (hz : Tacenta.SessionUnitSpqrT1.ZeroizeTotal)
    (self : tacenta_triple.State) (count : Usize) :
    tacenta_triple.State.evict_oldest_post_quantum self count
      ⦃ fun r => r.2.post_quantum.chains = self.post_quantum.chains ∧
        r.2.post_quantum.skipped.val.length ≤
          self.post_quantum.skipped.val.length ∧
        (0 < r.1.val → r.2.post_quantum.skipped.val.length <
          self.post_quantum.skipped.val.length) ∧
        r.2.classical = self.classical ⦄ := by
  unfold tacenta_triple.State.evict_oldest_post_quantum
  step with spqr_evict_oldest_no_panic hrm hz self.post_quantum count
  exact ⟨i_post1, i_post2, i_post3⟩


/-! ## Receive-with-eviction retry totality -/

def ReceiveHeadroom (state : tacenta_triple.State) : Prop :=
  max state.classical.skipped.val.length tacenta_ratchet.MAX_SKIPPED_STORE.val
      + tacenta_ratchet.MAX_SKIP.val ≤ Usize.max ∧
  state.post_quantum.chains.val.length + 2 < Usize.max ∧
  state.post_quantum.skipped.val.length + tacenta_spqr.MAX_SKIP.val ≤ Usize.max

def skippedTotal (state : tacenta_triple.State) : Nat :=
  state.classical.skipped.val.length + state.post_quantum.skipped.val.length

def retryMeasure {α : Type}
    (p : lifecycle.FullStore × tacenta_triple.State × Usize ×
      tacenta_triple.TripleError × Option α) : Nat :=
  skippedTotal (Prod.fst (Prod.snd p)) +
    match (Prod.snd (Prod.snd (Prod.snd (Prod.snd p)))) with
    | none => 1
    | some _ => 0

theorem receive_attempt_no_panic
    (hhmac : Tacenta.SessionUnitT1.HmacTotal)
    (hkdf : Tacenta.SessionUnitT1.HkdfTotal)
    (hzw : Tacenta.SessionUnitT1.ZeroizingTotal)
    [Tacenta.SessionUnitT1.DerivedKeysModel]
    (hz : Tacenta.SessionUnitSpqrT1.ZeroizeTotal)
    (hret : Tacenta.SessionUnitSpqrT1.VecRetainTotal)
    (hrk : Tacenta.SessionUnitSpqrT1.KdfRkTotal)
    (hck : Tacenta.SessionUnitSpqrT1.KdfCkTotal)
    (hopt : Tacenta.SessionUnitSpqrT1.OptionCloneTotal)
    (hrmRatchet : Tacenta.SessionUnitT1.RemoveSkippedAtTotal)
    (hrmSpqr : Tacenta.SessionUnitSpqrT1.RemoveSkippedAtTotal)
    (happ : Tacenta.SessionUnitSpqrT1.VecAppendTotal)
    (state : tacenta_triple.State) (header : tacenta_triple.Header)
    (dhOutRecv dhOutSend newDhsPub : Array U8 32#usize)
    (output : Option tacenta_spqr.Output) (hroom : ReceiveHeadroom state) :
    lifecycle.receive_attempt state header dhOutRecv dhOutSend newDhsPub output
      ⦃ fun _ => True ⦄ := by
  unfold lifecycle.receive_attempt ReceiveHeadroom at *
  exact Tacenta.SessionUnitTripleT1.State.receive_no_panic
    hhmac hkdf hzw hz hret hrk hck hopt hrmRatchet hrmSpqr happ
    state header dhOutRecv dhOutSend newDhsPub output hroom.1 hroom.2.1 hroom.2.2

theorem evict_for_retry_no_panic
    (hrmRatchet : Tacenta.SessionUnitT1.RemoveSkippedAtTotal)
    (hrmSpqr : Tacenta.SessionUnitSpqrT1.RemoveSkippedAtTotal)
    (hz : Tacenta.SessionUnitSpqrT1.ZeroizeTotal)
    (state : tacenta_triple.State) (half : lifecycle.FullStore) (count : Usize)
    (hroom : ReceiveHeadroom state) :
    lifecycle.evict_for_retry state half count ⦃ fun r =>
      ReceiveHeadroom r.1 ∧
      skippedTotal r.1 ≤ skippedTotal state ∧
      (0 < r.2.val → skippedTotal r.1 < skippedTotal state) ⦄ := by
  unfold lifecycle.evict_for_retry
  rcases half
  · step with triple_evict_oldest_classical_no_panic hrmRatchet state count
    rename_i nextState
    constructor
    · unfold ReceiveHeadroom at hroom ⊢
      simpa only [r_post3] using And.intro (by omega :
        max nextState.classical.skipped.val.length tacenta_ratchet.MAX_SKIPPED_STORE.val
          + tacenta_ratchet.MAX_SKIP.val ≤ Usize.max) hroom.2
    · constructor
      · unfold skippedTotal
        rw [r_post3]
        exact Nat.add_le_add_right r_post1 _
      · intro h
        unfold skippedTotal
        rw [r_post3]
        exact Nat.add_lt_add_right (r_post2 h) _
  · step with triple_evict_oldest_post_quantum_no_panic hrmSpqr hz state count
    rename_i nextState
    constructor
    · unfold ReceiveHeadroom at hroom ⊢
      rw [r_post4, r_post1]
      exact And.intro hroom.1 (And.intro hroom.2.1 (by omega))
    · constructor
      · unfold skippedTotal
        rw [r_post4]
        exact Nat.add_le_add_left r_post2 _
      · intro h
        unfold skippedTotal
        rw [r_post4]
        exact Nat.add_lt_add_left (r_post3 h) _


@[step]
theorem full_store_eq_no_panic (a b : lifecycle.FullStore) :
    lifecycle.FullStore.Insts.CoreCmpPartialEqFullStore.eq a b
      ⦃ fun r => r = true ↔ a = b ⦄ := by
  rcases a <;> rcases b <;>
    simp [lifecycle.FullStore.Insts.CoreCmpPartialEqFullStore.eq] <;> native_decide

@[step]
theorem full_store_ne_no_panic (a b : lifecycle.FullStore) :
    core.cmp.PartialEq.ne.trait_default
      lifecycle.FullStore.Insts.CoreCmpPartialEqFullStore a b
      ⦃ fun r => r = true ↔ a ≠ b ⦄ := by
  unfold core.cmp.PartialEq.ne.trait_default core.cmp.PartialEq.ne.default
  step with full_store_eq_no_panic a b
  rcases r <;> simp_all

theorem receive_with_eviction_loop_no_panic
    (hhmac : Tacenta.SessionUnitT1.HmacTotal)
    (hkdf : Tacenta.SessionUnitT1.HkdfTotal)
    (hzw : Tacenta.SessionUnitT1.ZeroizingTotal)
    [Tacenta.SessionUnitT1.DerivedKeysModel]
    (hz : Tacenta.SessionUnitSpqrT1.ZeroizeTotal)
    (hret : Tacenta.SessionUnitSpqrT1.VecRetainTotal)
    (hrk : Tacenta.SessionUnitSpqrT1.KdfRkTotal)
    (hck : Tacenta.SessionUnitSpqrT1.KdfCkTotal)
    (hopt : Tacenta.SessionUnitSpqrT1.OptionCloneTotal)
    (hrmRatchet : Tacenta.SessionUnitT1.RemoveSkippedAtTotal)
    (hrmSpqr : Tacenta.SessionUnitSpqrT1.RemoveSkippedAtTotal)
    (happ : Tacenta.SessionUnitSpqrT1.VecAppendTotal)
    (composite : tacenta_wire.Composite) (header : tacenta_triple.Header)
    (dhOutRecv dhOutSend newDhsPub : Array U8 32#usize)
    (output : Option tacenta_spqr.Output) (half : lifecycle.FullStore)
    (work : tacenta_triple.State) (batch : Usize)
    (pending : tacenta_triple.TripleError)
    (outcome : Option (core.result.Result
      (tacenta_triple.State × Array U8 32#usize) tacenta_triple.TripleError))
    (hroom : ReceiveHeadroom work) :
    lifecycle.receive_with_eviction_loop composite header dhOutRecv dhOutSend
      newDhsPub output half work batch pending outcome ⦃ fun _ => True ⦄ := by
  unfold lifecycle.receive_with_eviction_loop
  apply loop.spec_decr_nat
    (measure := retryMeasure)
    (inv := fun p => ReceiveHeadroom (Prod.fst (Prod.snd p)))
  · rintro ⟨half1, state, batch1, pending1, outcome1⟩ hinv
    simp only at hinv
    simp only [lifecycle.receive_with_eviction_loop.body]
    split
    · step with evict_for_retry_no_panic hrmRatchet hrmSpqr hz state half1 batch1 hinv
      rcases outcome1 with _ | value
      · split
        · rename_i hzero
          change ReceiveHeadroom next_work ∧
            skippedTotal next_work + 0 < skippedTotal state + 1
          exact ⟨next_work_post1, Nat.lt_succ_of_le next_work_post2⟩
        · rename_i hnonzero
          simp only [lift]
          step with receive_attempt_no_panic hhmac hkdf hzw hz hret hrk hck hopt
            hrmRatchet hrmSpqr happ next_work header dhOutRecv dhOutSend newDhsPub
            output next_work_post1
          have hevicted : 0 < evicted.val := by
            scalar_tac
          rcases batch1 with value | error
          · simp only
            change ReceiveHeadroom next_work ∧
              skippedTotal next_work + 0 < skippedTotal state + 1
            exact ⟨next_work_post1, Nat.lt_succ_of_le next_work_post2⟩
          · step with full_store_no_panic error
            rcases r with _ | next
            · simp only
              change ReceiveHeadroom next_work ∧
                skippedTotal next_work + 0 < skippedTotal state + 1
              exact ⟨next_work_post1, Nat.lt_succ_of_le next_work_post2⟩
            · step with full_store_ne_no_panic next half1
              split
              · step with receive_shortfall_no_panic next next_work composite
                change ReceiveHeadroom next_work ∧
                  skippedTotal next_work + 1 < skippedTotal state + 1
                exact ⟨next_work_post1, Nat.add_lt_add_right
                  (next_work_post3 hevicted) 1⟩
              · change ReceiveHeadroom next_work ∧
                  skippedTotal next_work + 1 < skippedTotal state + 1
                exact ⟨next_work_post1, Nat.add_lt_add_right
                  (next_work_post3 hevicted) 1⟩
      · simp_all [core.option.Option.is_none]
    · step*
  · simpa using hroom


theorem receive_with_eviction_no_panic
    (hhmac : Tacenta.SessionUnitT1.HmacTotal)
    (hkdf : Tacenta.SessionUnitT1.HkdfTotal)
    (hzw : Tacenta.SessionUnitT1.ZeroizingTotal)
    [Tacenta.SessionUnitT1.DerivedKeysModel]
    (hz : Tacenta.SessionUnitSpqrT1.ZeroizeTotal)
    (hret : Tacenta.SessionUnitSpqrT1.VecRetainTotal)
    (hrk : Tacenta.SessionUnitSpqrT1.KdfRkTotal)
    (hck : Tacenta.SessionUnitSpqrT1.KdfCkTotal)
    (hopt : Tacenta.SessionUnitSpqrT1.OptionCloneTotal)
    (hrmRatchet : Tacenta.SessionUnitT1.RemoveSkippedAtTotal)
    (hrmSpqr : Tacenta.SessionUnitSpqrT1.RemoveSkippedAtTotal)
    (happ : Tacenta.SessionUnitSpqrT1.VecAppendTotal)
    (state : tacenta_triple.State) (composite : tacenta_wire.Composite)
    (header : tacenta_triple.Header)
    (dhOutRecv dhOutSend newDhsPub : Array U8 32#usize)
    (output : Option tacenta_spqr.Output) (hroom : ReceiveHeadroom state) :
    lifecycle.receive_with_eviction state composite header dhOutRecv dhOutSend
      newDhsPub output ⦃ fun _ => True ⦄ := by
  unfold lifecycle.receive_with_eviction
  step with receive_attempt_no_panic hhmac hkdf hzw hz hret hrk hck hopt
    hrmRatchet hrmSpqr happ state header dhOutRecv dhOutSend newDhsPub output hroom
  rcases r with value | error
  · simp
  · step with full_store_no_panic error
    rename_i storeHalf
    rcases storeHalf with _ | half
    · simp
    · step with Tacenta.SessionUnitTripleT1.State.clone_spec hopt state
      rename_i cloned hclone
      simp only [hclone]
      step with receive_shortfall_no_panic half state composite
      step with receive_with_eviction_loop_no_panic hhmac hkdf hzw hz hret hrk hck
        hopt hrmRatchet hrmSpqr happ composite header dhOutRecv dhOutSend newDhsPub
        output half state batch error none hroom
      rcases outcome <;> simp

end Tacenta.UnitLifecycleT1
