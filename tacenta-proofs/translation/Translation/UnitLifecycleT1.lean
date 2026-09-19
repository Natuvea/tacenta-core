import Translation.TacentaSessionUnit
import Translation.SessionUnitSessionT1

/-!
# Session lifecycle primitive boundary

The complete Session unit leaves primitive implementations opaque.  These ten
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

def AeadSealTotal : Prop :=
  ∀ ek mk nonce plaintext ad,
    NoPanic (tacenta_boundary.aead.encrypt ek mk nonce plaintext ad)

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

end Tacenta.UnitLifecycleT1
