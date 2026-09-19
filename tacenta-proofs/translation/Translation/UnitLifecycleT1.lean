import Translation.TacentaSessionUnit

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

end Tacenta.UnitLifecycleT1
