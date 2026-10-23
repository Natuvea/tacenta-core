/- Copied from a separate, unpublished repository, written by the maintainer with tool assistance and
read so far only by tool-assisted sessions (no human has yet read the three Rust files or their
proofs), that holds a SHA-256, HMAC-SHA256 and HKDF-SHA256 with their proofs, the source of `tacenta-core/kdf/src` (pinned there by
commit and file digests): its model file `Basic.lean`, at commit `646fcdadb943`. Elaborated
here against the Session unit's own translation of those bodies. Changes from the source: the
translated crate's namespace is `tacenta_session_unit.tacenta_kdf`, the Session unit's
translation of `tacenta-kdf`; the source's other namespaces are renamed `KdfStandardModel`,
`Tacenta.KdfProof` and `KdfBridge`; its imports name this package's `Kdf*` modules.
Of the source's model only the SHA-256, HMAC and HKDF files were copied. "This repository" in the
prose below means that implementation, and a path such as `scripts/...` or `std/...` names one of
its files. -/
/-!
# KdfStandardModel

A clean-room model of SHA-256 (FIPS 180-4), HMAC-SHA256 (FIPS 198-1,
RFC 2104), HKDF-SHA256 (RFC 5869), PKCS#7 padding (RFC 5652 §6.3), CBC mode
(NIST SP 800-38A §6.2) and the encrypt-then-MAC AEAD of tacenta-spec's
"Authenticated encryption" section, written from the standards' text. Each
definition cites the section and step it comes from.

This file holds the byte-string type and the two list helpers the standards
use without naming: cutting a string into fixed-size blocks, and XOR of two
equal-length strings.
-/

namespace KdfStandardModel

/-- A byte string, as the standards treat one. -/
abbrev Bytes := List UInt8

/-- The first `count` consecutive `size`-byte pieces of `xs`, in order: piece
`i` (from 0) is bytes `size*i` to `size*i + size - 1`. This is the "parse the
message into N m-bit blocks M(1), …, M(N)" of FIPS 180-4 §5.2 and the
"P_1 … P_n" of SP 800-38A §6.2 and tacenta-spec's AEAD section. It is
recursion on the block count, so it is structural and kernel-reducible; the
callers pass `count = xs.length / size`, so a trailing partial piece (if any)
is not included. -/
def chunks (size : Nat) : Nat → Bytes → List Bytes
  | 0, _ => []
  | count + 1, xs => xs.take size :: chunks size count (xs.drop size)

/-- Bytewise exclusive-or, `a ⊕ b` (FIPS 198-1 §2 "⊕", SP 800-38A §2.2
"X ⊕ Y"). The standards apply it only to strings of equal length; on unequal
lengths this is `List.zipWith`, i.e. the result has the shorter length. -/
def xorBytes (a b : Bytes) : Bytes := List.zipWith (· ^^^ ·) a b

end KdfStandardModel
