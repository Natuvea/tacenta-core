/-
Model.SessionEstablishment: PQXDH, the agreement that produces the shared secret
the Double Ratchet starts from. Written from
tacenta-spec/protocol/session-establishment.md.

Same boundary as the ratchet model: the Diffie-Hellman agreements and the
post-quantum encapsulation are trusted primitives, so their outputs enter here as
byte strings. What the model computes concretely is the derivation that combines
them, which is the part PQXDH itself contributes. Given the DH outputs and the
encapsulated secret, the model produces the exact shared secret an implementation
must produce.
-/
import Model.Kdf
import Model.State

namespace Model.SessionEstablishment

open Model.State (Key)

/-- The domain-separation prefix on the KDF input: 32 bytes of `0xFF` for
    curve25519. It ensures the leading bytes of the input keying material are
    never a valid encoding of a scalar or a curve point, which is what keeps this
    derivation separate from XEdDSA's use of the same identity key. -/
def fPrefix : List UInt8 := List.replicate 32 0xFF

/-- The KDF `info`: the application string, the curve, the hash, and the KEM
    joined by underscores, so a secret derived under one parameter set cannot
    collide with another. The application string itself is wire-sensitive and is
    pinned in the conformance manifest; this model label keeps the model
    self-consistent (see the note in Model.State on the ratchet's labels). -/
def skInfo : List UInt8 :=
  -- "Tacenta_CURVE25519_SHA-256_ML-KEM-1024"
  [0x54,0x61,0x63,0x65,0x6e,0x74,0x61,0x5f,
   0x43,0x55,0x52,0x56,0x45,0x32,0x35,0x35,0x31,0x39,0x5f,
   0x53,0x48,0x41,0x2d,0x32,0x35,0x36,0x5f,
   0x4d,0x4c,0x2d,0x4b,0x45,0x4d,0x2d,0x31,0x30,0x32,0x34]

/-- `KDF(KM)`: 32 bytes of HKDF output, with input keying material `F || KM`, an
    all-zero salt the length of the hash output, and the parameter `info`. -/
def kdf (km : List UInt8) : Key :=
  Model.Kdf.hkdf (List.replicate 32 0) (fPrefix ++ km) skInfo 32

/-- `KM`, the input keying material: the Diffie-Hellman outputs in order, then
    the one-time curve output when the bundle carried a one-time prekey, then the
    encapsulated post-quantum secret, which is always last.

    Named rather than inlined into `sharedSecret` because the order and the
    optionality are the whole content of this part of the agreement, and because
    it is the thing worth proving unambiguous: two different tuples must never
    reach the KDF as the same bytes (`Proofs.SessionEstablishment`). -/
def km (dh1 dh2 dh3 : Key) (dh4 : Option Key) (ss : Key) : List UInt8 :=
  match dh4 with
  | none => dh1 ++ dh2 ++ dh3 ++ ss
  | some d4 => dh1 ++ dh2 ++ dh3 ++ d4 ++ ss

/-- The shared secret. `dh1`, `dh2`, `dh3` are the three Diffie-Hellman outputs
    always present; `dh4` is present exactly when the bundle carried a one-time
    curve prekey; `ss` is the encapsulated post-quantum secret, which is always
    last. -/
def sharedSecret (dh1 dh2 dh3 : Key) (dh4 : Option Key) (ss : Key) : Key :=
  kdf (km dh1 dh2 dh3 dh4 ss)

/-- The associated data binding both identities. The encoders are wire-sensitive
    and pinned elsewhere; the model takes the encoded forms as given. -/
def associatedData (encodedIkA encodedIkB : List UInt8) : List UInt8 :=
  encodedIkA ++ encodedIkB

/-- With a KEM that does not bind its public key into the ciphertext, the encoded
    KEM prekey is appended to the associated data as well. -/
def associatedDataWithKem (encodedIkA encodedIkB encodedPqPk : List UInt8) :
    List UInt8 :=
  encodedIkA ++ encodedIkB ++ encodedPqPk

-- Structural checks. These elaborate at build time.

/-- The secret is 32 bytes, with or without the one-time curve prekey. -/
example : (sharedSecret (List.replicate 32 0x11) (List.replicate 32 0x22)
    (List.replicate 32 0x33) none (List.replicate 32 0x55)).length = 32 := by
  native_decide

example : (sharedSecret (List.replicate 32 0x11) (List.replicate 32 0x22)
    (List.replicate 32 0x33) (some (List.replicate 32 0x44))
    (List.replicate 32 0x55)).length = 32 := by
  native_decide

/-- Including a one-time curve prekey changes the secret: the extra Diffie-Hellman
    output is genuinely folded in, not dropped. -/
example :
    (sharedSecret (List.replicate 32 0x11) (List.replicate 32 0x22)
      (List.replicate 32 0x33) none (List.replicate 32 0x55))
    ≠ (sharedSecret (List.replicate 32 0x11) (List.replicate 32 0x22)
      (List.replicate 32 0x33) (some (List.replicate 32 0x44))
      (List.replicate 32 0x55)) := by
  native_decide

/-- The encapsulated secret is folded in: changing it changes the shared secret.
    A derivation that ignored `ss` would not be post-quantum forward secret. -/
example :
    (sharedSecret (List.replicate 32 0x11) (List.replicate 32 0x22)
      (List.replicate 32 0x33) none (List.replicate 32 0x55))
    ≠ (sharedSecret (List.replicate 32 0x11) (List.replicate 32 0x22)
      (List.replicate 32 0x33) none (List.replicate 32 0x66)) := by
  native_decide

end Model.SessionEstablishment
