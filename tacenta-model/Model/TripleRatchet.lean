/-
Model.TripleRatchet: the composition of the Double Ratchet and the sparse
post-quantum ratchet, written from tacenta-spec/protocol/triple-ratchet.md.

This is the smallest file in the model layer, and the composition is where
the hybrid claim lives: every proof about either ratchet separately says
nothing about whether combining them preserves what each contributes. It
carries the largest claim.

## What is here and what is at the boundary

Two operations. `split`, which expands the handshake's single shared secret into
one secret per ratchet, and `combine`, which derives the encryption key from the
two message keys.

What can be proved about them is narrower than what the composition needs, and
the line matters. That `combine` cannot be inverted from one input is a property
of HKDF, and HKDF is a trusted primitive here as everywhere else. What is *not* a
cryptographic assumption, and what the specification explicitly claims is free, is
that the concatenation fed to it is unambiguous. That is proved below.

The distinction is the whole point. If the encoding were ambiguous, two different
pairs of message keys would present the same bytes to the derivation and produce
the same encryption key, and no property of HKDF would save it. Being free is not
the same as being true, and the specification says the argument "is proved there
rather than assumed" about the handshake's keying material. This makes the same
statement for this composition rather than pointing at the other one.
-/
import Model.Kdf
import Model.State

namespace Model.TripleRatchet

open Model.State (Key)

/-! ## Labels

Wire-sensitive, recorded in the conformance manifest rather than settled here,
and matching `tacenta-triple`. -/

/-- `TR_PROTOCOL_INFO`: "Tacenta_CURVE25519_SHA-256_MLKEM1024" as bytes.

    Named for the specification's own constant, and shaped like the Double
    Ratchet specification's own example -- a protocol identifier joined to
    its parameters by underscores, as in
    "MyProtocol_CURVE25519_SHA-512_CRYSTALS-KYBER-1024". §6.3 asks for a
    constant specifying "the protocol in use **and its parameters**".

    Naming the parameters is what makes the constant do its job. Two
    deployments differing only in hash would otherwise derive the same key from
    the same inputs, which is the confusion domain separation exists to
    prevent. -/
def combineInfo : List UInt8 :=
  [0x54,0x61,0x63,0x65,0x6e,0x74,0x61,0x5f,0x43,0x55,0x52,0x56,0x45,0x32,0x35,
   0x35,0x31,0x39,0x5f,0x53,0x48,0x41,0x2d,0x32,0x35,0x36,0x5f,0x4d,0x4c,0x4b,
   0x45,0x4d,0x31,0x30,0x32,0x34]

/-- "Tacenta_CURVE25519_SHA-256_MLKEM1024:Split" as bytes.

    The same protocol constant as `combineInfo`, with a literal suffix. That is
    the published pattern for a derivation the specification does not name its
    own constant for: §5.2's SCKA functions are `SPQR_PROTOCOL_INFO` joined to
    "Chain Start" and "Chain Add Epoch", and the ML-KEM Braid carries four more
    such suffixes.

    §7.1 mandates that the handshake secret is expanded into two, and does not
    give the constant that expands it. So this one is ours, and naming the
    parameters here is hygiene rather than conformance -- but it is the same
    hygiene, and leaving one constant parameterised and its neighbour not would
    be worse than either choice made consistently.

    `combineInfo` is a prefix of this, which is harmless: the two derivations
    take different salts and different input keying material, so the constant is
    not the only thing separating them, and HKDF's expand step appends a counter
    byte that differs in any case. -/
def splitInfo : List UInt8 :=
  [0x54,0x61,0x63,0x65,0x6e,0x74,0x61,0x5f,0x43,0x55,0x52,0x56,0x45,0x32,0x35,
   0x35,0x31,0x39,0x5f,0x53,0x48,0x41,0x2d,0x32,0x35,0x36,0x5f,0x4d,0x4c,0x4b,
   0x45,0x4d,0x31,0x30,0x32,0x34,0x3a,0x53,0x70,0x6c,0x69,0x74]

/-! ## Splitting the handshake secret

Each ratchet needs its own thirty-two bytes and the handshake produces one set,
so the secret is expanded rather than shared. Giving both ratchets the same
secret would make the hybrid claim false at initialisation, whatever it looked
like afterwards. -/

def splitSecret (sk : Key) : Key × Key :=
  let out := Model.Kdf.hkdf (List.replicate 32 0) sk splitInfo 64
  (out.take 32, (out.drop 32).take 32)

/-! ## Combining the message keys

Section 7.2 of the published specification recommends parameters, and the
model follows them: the post-quantum key is the **salt** and the classical one
is the input keying material. Section 6.3's definition is looser -- a derivation
keyed by the concatenation of the two secrets would also meet it -- so this is
the recommended construction rather than merely a permitted one. -/

/-- The encryption key.

    Salt is the post-quantum key, IKM the classical one, per §7.2. The
    inversion is the same one `KDF_RK` has and is easy to get backwards. -/
def combine (mkEc mkPq : Key) : Key :=
  Model.Kdf.hkdf mkPq mkEc combineInfo 32

/-! ## The separation is structural

A construction that concatenated the two keys into one input would need a
theorem: both are exactly thirty-two bytes, therefore no two distinct pairs
present the same bytes. §7.2's parameters make the property structural instead.

The two keys reach the derivation through *different arguments*, salt and IKM,
so distinct pairs are distinct inputs by construction and there is nothing to
prove. Making a property structural rather than proving it is the better
direction of travel, and it is worth naming: a length argument would be
load-bearing only because a construction needed it to be. -/

/-- Both halves of a split are thirty-two bytes, which is what lets a split
    secret be used where a handshake secret was. -/
theorem splitSecret_lengths (sk : Key) :
    (splitSecret sk).1.length = 32 ∧ (splitSecret sk).2.length = 32 := by
  simp only [splitSecret]
  constructor
  · rw [List.length_take, Model.Kdf.hkdf_length]; omega
  · rw [List.length_take, List.length_drop, Model.Kdf.hkdf_length]; omega

/-- The combined key is thirty-two bytes, so it can drive the same AEAD the
    Double Ratchet's message key drove before the composition existed. -/
theorem combine_length (a b : Key) : (combine a b).length = 32 := by
  simp only [combine]
  exact Model.Kdf.hkdf_length _ _ _ _

/-! ## Self-consistency

The two halves of a split differ, and the combination is neither input. Known
answers rather than theorems: they say the derivation was not written as a
projection, which a theorem about HKDF could not say without assuming HKDF. -/

private def sk : Key := List.replicate 32 0x01

example : (splitSecret sk).1 ≠ (splitSecret sk).2 := by native_decide

example : (splitSecret sk).1 ≠ sk := by native_decide

example : (splitSecret sk).2 ≠ sk := by native_decide

example :
    let a : Key := List.replicate 32 0x11
    let b : Key := List.replicate 32 0x22
    combine a b ≠ a ∧ combine a b ≠ b := by native_decide

/-- Not symmetric, so the two inputs are not interchangeable. A composition that
    sorted or xored its inputs would pass every length theorem above. -/
example :
    let a : Key := List.replicate 32 0x11
    let b : Key := List.replicate 32 0x22
    combine a b ≠ combine b a := by native_decide

end Model.TripleRatchet
