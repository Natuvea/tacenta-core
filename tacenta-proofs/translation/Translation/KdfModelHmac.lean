/- Copied from a separate, unpublished repository of this project's maintainer that holds a SHA-256,
HMAC-SHA256 and HKDF-SHA256 with their proofs, the source of `tacenta-core/kdf/src` (pinned there by
commit and file digests): its model file `Hmac.lean`, at commit `646fcdadb943`. Elaborated
here against the Session unit's own translation of those bodies. Changes from the source: the
translated crate's namespace is `tacenta_session_unit.tacenta_kdf`, the Session unit's
translation of `tacenta-kdf`; the source's other namespaces are renamed `KdfStandardModel`,
`Tacenta.KdfProof` and `KdfBridge`; its imports name this package's `Kdf*` modules.
Of the source's model only the SHA-256, HMAC and HKDF files were copied. "This repository" in the
prose below means that implementation, and a path such as `scripts/...` or `std/...` names one of
its files. -/
import Translation.KdfModelSha256

/-!
# HMAC-SHA256 (FIPS 198-1, RFC 2104)

FIPS 198-1 §4, Table 1, steps 1–9, with H = SHA-256, so B = 64 and L = 32
(FIPS 198-1 §2: B is the hash's input block size in bytes, L its output size).
The output is the full L = 32 bytes; truncation (FIPS 198-1 §5) is left to
callers, and tacenta-spec's AEAD tag is not truncated.

FIPS 198-1 §2 bounds the text length n by 0 ≤ n < 2^B − 8B bits, B in bytes,
so n < 2^64 − 512 for B = 64: the inner hash input, B bytes of K0 ⊕ ipad plus
the text, must stay inside SHA-256's ℓ < 2^64. The model is total beyond it,
inheriting `sha256`'s out-of-domain behaviour (length taken mod 2^64).
-/

namespace KdfStandardModel

namespace Hmac

/-- FIPS 198-1 §2: B, the block size of the hash function in bytes; 64 for
SHA-256 (FIPS 180-4 §1, Figure 1: 512-bit blocks). -/
def B : Nat := 64

/-- FIPS 198-1 §2: L, the output size of the hash function in bytes; 32 for
SHA-256. -/
def L : Nat := 32

/-- FIPS 198-1 §2: ipad, "the byte x'36' repeated B times". -/
def ipad : Bytes := List.replicate B 0x36

/-- FIPS 198-1 §2: opad, "the byte x'5c' repeated B times". -/
def opad : Bytes := List.replicate B 0x5c

/-- FIPS 198-1 §4, steps 1–3: K0, the key after pre-processing to B bytes.
Step 1: if |K| = B, K0 = K. Step 2: if |K| > B, K0 = H(K) ‖ 00…00 (B − L zero
bytes). Step 3: if |K| < B, K0 = K followed by B − |K| zero bytes. -/
def K0 (K : Bytes) : Bytes :=
  if K.length = B then K
  else if K.length > B then sha256 K ++ List.replicate (B - L) 0
  else K ++ List.replicate (B - K.length) 0

end Hmac

open Hmac in
/-- FIPS 198-1 §4: HMAC(K, text) = H((K0 ⊕ opad) ‖ H((K0 ⊕ ipad) ‖ text)),
with H = SHA-256, as Table 1's steps:
step 4, K0 ⊕ ipad; step 5, append text; step 6, apply H;
step 7, K0 ⊕ opad; step 8, append step 6's result; step 9, apply H.
(RFC 2104 §2 gives the same definition.) -/
def hmac (K text : Bytes) : Bytes :=
  let k0 := K0 K
  let step4 := xorBytes k0 ipad
  let step5 := step4 ++ text
  let step6 := sha256 step5
  let step7 := xorBytes k0 opad
  let step8 := step7 ++ step6
  sha256 step8

/-- The HMAC-SHA256 output is L = 32 bytes. -/
theorem hmac_length (K text : Bytes) : (hmac K text).length = 32 :=
  sha256_length _

/-- K0 is always B = 64 bytes long, whatever the key's length. -/
theorem Hmac.K0_length (K : Bytes) : (Hmac.K0 K).length = 64 := by
  unfold Hmac.K0 Hmac.B Hmac.L
  split
  · assumption
  · split
    · simp [sha256_length]
    · simp; omega

end KdfStandardModel
