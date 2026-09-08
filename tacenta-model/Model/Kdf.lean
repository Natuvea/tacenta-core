/-
Model.Kdf: HMAC-SHA256 (RFC 2104) and HKDF-SHA256 (RFC 5869), built on
Model.Sha256. These are the derivations the Double Ratchet key schedule is
composed from, so the model computes chain keys, message keys, and root keys to
exact bytes. Correctness is anchored to the RFC known-answer values at the
bottom of this file, the same vectors tacenta-core is checked against.
-/
import Model.Sha256

namespace Model.Kdf

/-- HMAC block size for SHA-256, in bytes. -/
def blockSize : Nat := 64

/-- Output length of SHA-256, in bytes. -/
def hashLen : Nat := 32

/-- HMAC-SHA256 of `msg` under `key` (RFC 2104). -/
def hmac (key : List UInt8) (msg : List UInt8) : List UInt8 :=
  let k0 := if key.length > blockSize then Model.Sha256.hash key else key
  let k := k0 ++ List.replicate (blockSize - k0.length) 0
  let ipad := k.map (· ^^^ 0x36)
  let opad := k.map (· ^^^ 0x5c)
  Model.Sha256.hash (opad ++ Model.Sha256.hash (ipad ++ msg))

/-- HKDF-Extract (RFC 5869 §2.2): `PRK = HMAC(salt, IKM)`, with an all-zero salt
    of one hash length when `salt` is empty. -/
def extract (salt ikm : List UInt8) : List UInt8 :=
  let s := if salt.isEmpty then List.replicate hashLen 0 else salt
  hmac s ikm

/-- One expansion step: derive the next block from the previous one, the `info`,
    and the counter, and append it to the output. Named and folded rather than
    written as a loop so the output's length can be carried by induction
    (`expand_length`); the RFC known-answer checks below say the two compute the
    same thing. -/
def expandStep (prk info : List UInt8) (acc : List UInt8 × List UInt8) (i : Nat) :
    List UInt8 × List UInt8 :=
  let block := hmac prk (acc.1 ++ info ++ [UInt8.ofNat i])
  (block, acc.2 ++ block)

/-- HKDF-Expand (RFC 5869 §2.3): expand `prk` to `len` bytes under `info`. -/
def expand (prk info : List UInt8) (len : Nat) : List UInt8 :=
  let n := (len + hashLen - 1) / hashLen
  ((List.range' 1 n).foldl (expandStep prk info) ([], [])).2.take len

/-- HKDF-SHA256 (RFC 5869): extract then expand to `len` bytes. -/
def hkdf (salt ikm info : List UInt8) (len : Nat) : List UInt8 :=
  expand (extract salt ikm) info len

/-! ## Output lengths

Every caller copies a fixed number of bytes out of these, so a derivation that
returned fewer would be a bounds failure rather than a wrong key. The known-answer
checks below cover the lengths they happen to use; these cover all of them. -/

/-- HMAC-SHA256 is one hash length, whatever the key and message. -/
theorem hmac_length (key msg : List UInt8) : (hmac key msg).length = hashLen := by
  simp [hmac, hashLen, Model.Sha256.hash_length]

/-- Extraction is one hash length. -/
theorem extract_length (salt ikm : List UInt8) :
    (extract salt ikm).length = hashLen := by
  simp only [extract]
  split <;> exact hmac_length _ _

/-- Each expansion step appends exactly one block, so the accumulated output
grows by a hash length per counter value. -/
theorem expand_acc_length (prk info : List UInt8) (l : List Nat)
    (acc : List UInt8 × List UInt8) :
    ((l.foldl (expandStep prk info) acc).2).length
      = acc.2.length + l.length * hashLen := by
  induction l generalizing acc with
  | nil => simp
  | cons a t ih =>
    rw [List.foldl_cons, ih (expandStep prk info acc a)]
    simp only [expandStep, List.length_append, hmac_length, List.length_cons,
      hashLen]
    omega

/-- Expansion returns exactly the requested length: the block count is the
requested length rounded up, so there is always enough to take. -/
theorem expand_length (prk info : List UInt8) (len : Nat) :
    (expand prk info len).length = len := by
  simp only [expand, List.length_take, expand_acc_length, List.length_range',
    List.length_nil, Nat.zero_add, hashLen]
  omega

/-- HKDF returns exactly the requested length. -/
theorem hkdf_length (salt ikm info : List UInt8) (len : Nat) :
    (hkdf salt ikm info len).length = len :=
  expand_length _ _ _

-- Known-answer checks. These elaborate at build time; a wrong implementation
-- fails the build.

/-- RFC 4231 test case 2: HMAC-SHA256, key "Jefe", data "what do ya want for
    nothing?". -/
example :
    hmac [0x4a,0x65,0x66,0x65]
      [0x77,0x68,0x61,0x74,0x20,0x64,0x6f,0x20,0x79,0x61,0x20,0x77,0x61,0x6e,0x74,0x20,
       0x66,0x6f,0x72,0x20,0x6e,0x6f,0x74,0x68,0x69,0x6e,0x67,0x3f] =
    [0x5b,0xdc,0xc1,0x46,0xbf,0x60,0x75,0x4e,0x6a,0x04,0x24,0x26,0x08,0x95,0x75,0xc7,
     0x5a,0x00,0x3f,0x08,0x9d,0x27,0x39,0x83,0x9d,0xec,0x58,0xb9,0x64,0xec,0x38,0x43] := by
  native_decide

/-- RFC 5869 test case 1 (SHA-256): PRK from extract. -/
example :
    extract
      [0x00,0x01,0x02,0x03,0x04,0x05,0x06,0x07,0x08,0x09,0x0a,0x0b,0x0c]
      (List.replicate 22 0x0b) =
    [0x07,0x77,0x09,0x36,0x2c,0x2e,0x32,0xdf,0x0d,0xdc,0x3f,0x0d,0xc4,0x7b,0xba,0x63,
     0x90,0xb6,0xc7,0x3b,0xb5,0x0f,0x9c,0x31,0x22,0xec,0x84,0x4a,0xd7,0xc2,0xb3,0xe5] := by
  native_decide

/-- RFC 5869 test case 1 (SHA-256): OKM (42 bytes) from the full HKDF. -/
example :
    hkdf
      [0x00,0x01,0x02,0x03,0x04,0x05,0x06,0x07,0x08,0x09,0x0a,0x0b,0x0c]
      (List.replicate 22 0x0b)
      [0xf0,0xf1,0xf2,0xf3,0xf4,0xf5,0xf6,0xf7,0xf8,0xf9]
      42 =
    [0x3c,0xb2,0x5f,0x25,0xfa,0xac,0xd5,0x7a,0x90,0x43,0x4f,0x64,0xd0,0x36,0x2f,0x2a,
     0x2d,0x2d,0x0a,0x90,0xcf,0x1a,0x5a,0x4c,0x5d,0xb0,0x2d,0x56,0xec,0xc4,0xc5,0xbf,
     0x34,0x00,0x72,0x08,0xd5,0xb8,0x87,0x18,0x58,0x65] := by
  native_decide

end Model.Kdf
