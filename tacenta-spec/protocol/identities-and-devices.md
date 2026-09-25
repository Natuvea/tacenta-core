# Identities and devices

Identity keys, devices, and how they relate.

Status: partial. The identity key's secret, XEdDSA signing and verification
under it, application signatures, and the bounded hosted inventory statement
profile are specified below. General device management remains outside this
document.

## The identity key's secret

An identity is one 32-byte secret, generated as 32 random bytes. Exporting an
identity yields those 32 bytes as they are, and importing takes the same 32
bytes back as they are. An imported identity carries no prekeys and no
sessions; those are persisted separately (session-persistence.md).

The same 32 bytes serve both roles the identity key has (ADR-0002):

- the X25519 private key, clamped when used, in every Diffie-Hellman
  computation under the identity key (session-establishment.md, Primitives);
- the XEdDSA private key, for every signature made under the identity key.
  Signing clamps the 32 bytes in the same way (Signing, below).

The secret is stored unclamped, and each use clamps it. The published identity
key is the X25519 public key of the clamped secret: 32 bytes, the little-endian
u-coordinate (RFC 7748). A verifier converts that u-coordinate to the Edwards
key it checks a signature under.

## Signing

`Sig(IK, M, Z)` (session-establishment.md, Notation) is XEdDSA as `xeddsa_sign`
defines it in the XEdDSA document, revision 1, section 3, over Curve25519
(section 5). This section fixes how the private key is read.

The notation is as follows:

- Integers are read and written little-endian.
- `B` is the edwards25519 base point, and `q` is its prime order,
  2^252 + 27742317777372353535851937790883648493.
- A point is encoded as RFC 8032, section 5.1.2, encodes one: the y-coordinate
  in 255 bits, with the sign of x in bit 255.

```
k   = clamp(secret) mod q         -- clamp: RFC 7748 section 5, decodeScalar25519
E   = kB
A   = encode(E) with bit 255 set to 0                   -- 32 bytes
a   = k        if bit 255 of encode(E) is 0
    = q - k    otherwise                                -- mod q
Z   = 64 fresh random bytes
r   = SHA-512(0xFE || 31 bytes of 0xFF || a || M || Z) mod q     -- a in 32 bytes
R   = encode(rB)                                        -- 32 bytes
h   = SHA-512(R || A || M) mod q
s   = r + h * a mod q                                   -- 32 bytes
Sig = R || s
```

`clamp` clears the low three bits of byte 0, clears the top bit of byte 31,
and sets the bit below it. `k`, `E`, `A` and `a` are the document's
`calculate_key_pair` (section 2.3), and `r`, `R`, `h` and `s` are
`xeddsa_sign`.

**Why the clamp.** Section 2.3 allows a Montgomery private key to be any
scalar, and `calculate_key_pair` multiplies the base point by it. Which scalar
the 32 bytes denote is the X25519 key's definition. X25519 uses the clamped
integer (RFC 7748, section 5), so only `k = clamp(secret)` gives an `A` whose
Montgomery u-coordinate is the published identity key. A signer that used the
bytes unclamped would make signatures that do not verify under that key.
Reducing the clamped integer mod q does not change `kB`, since `B` has order
q.

The 32 bytes before `a` are `hash_1`'s prefix, 2^256 - 2 in 32 bytes (section
2.5; CONSTANTS.md). `Z` is fresh for every signature, as the document requires.
`A`'s sign bit is always 0. `s` is below q, so below 2^253, and the top bit of
its last byte is therefore 0 in every signature this signer makes. That bit is
where a verifier reads a sign (below).

## Verifying a signature

A verifier holds a 32-byte identity key `u`, a message `M` and a 64-byte
signature. It accepts exactly when all of the following hold, and refuses
otherwise. The order in which it checks them is not fixed (error-handling.md).

1. `u` is a canonical encoding: bit 255 is clear and the value is below
   p = 2^255 - 19. This is `DecodeEC`'s rule (session-establishment.md),
   applied to the key a signature is checked under.
2. `u` is not p - 1, where the map below divides by zero, and
   `y = (u - 1) / (u + 1) mod p` is the y-coordinate of a point on
   edwards25519. Let `b` be bit 255 of the signature, the top bit of its last
   byte. `A` is the point with that y-coordinate whose x-coordinate has sign
   `b`.
3. `A` is not of small order: `8A` is not the identity. A point with
   x-coordinate 0 is of small order, so this step refuses it whatever `b` is.
4. `s`, the signature's last 32 bytes with bit 255 cleared, is below q.
5. Let `R` be the signature's first 32 bytes, `enc(A)` the 32-byte encoding of
   `A` (with sign `b`), and `h = SHA-512(R || enc(A) || M) mod q`. The 32-byte
   encoding of the point `sB - hA` equals `R` byte for byte, so `R` must be the
   canonical encoding of that point. Another spelling of the same point is
   refused.
6. The point `R` encodes is not of small order.

No step multiplies by the cofactor. For a prekey signature `M` is the tagged
key (session-establishment.md, Publishing keys); for an application signature
it is the labelled input below.

**Where this departs from revision 1's `xeddsa_verify`.** The accepted set
differs in both directions, by design (ADR-0002):

- **It is wider on the sign bit.** Revision 1 takes `A`'s sign to be 0 and
  refuses any `s` at or above 2^253, so it refuses a signature whose top bit is
  set. Here that bit is `A`'s sign (step 2), so a signer that does not
  normalise the sign still verifies. The convention is recorded in
  CONSTANTS.md, "XEdDSA signature sign bit".
- **It is narrower on `s`.** Revision 1 accepts any `s` below 2^253, which
  admits `s + q` as a second signature for most messages. Step 4 requires
  `s < q`.
- **It is narrower on small-order points.** Revision 1 evaluates the equation
  for whatever `A` and `R` decode to, and accepts where it holds. That admits
  signatures nobody holding a key made, under keys such as u = 0. Steps 3 and
  6 refuse them.
- **It agrees on the rest.** Both refuse u at or above p, both refuse a u with
  no point on the curve, and both compare `R` as bytes.

Every signature the signer above makes lies in both sets. The edges are pinned
by the verify-only vectors in
`tacenta-test-vectors/vectors/primitives/xeddsa.json`, and each vector's
comment gives revision 1's verdict on the same input.

## Application signatures

An identity also signs messages an application supplies, such as a server's
challenge to a device. The signature is XEdDSA under the identity key over the
message with a fixed label in front:

```
input     = "tacenta:application-signature:v1" || 0xFF || message
signature = Sig(IK, input, Z)
```

The label is 32 ASCII bytes, and with its `0xFF` terminator 33 (CONSTANTS.md).
A verifier rebuilds `input` from the message and verifies the signature under
the published identity key.

Prekey signatures carry no label (session-establishment.md, Publishing keys).
The label is what keeps the two uses of the one key apart: a signature made
for one is not accepted for the other.

## Hosted device-inventory statements

This section specifies the version-one statement format used by the bounded
hosted-device inventory profile. It is a signed inventory statement, not a
device-registration protocol, a membership protocol, or a proof that a caller
has authority over an account. The caller supplies the issuer-key lookup and
must enforce the product policy that associates an `issuer_key_id` with the
verification key and account.

The unsigned preimage is the following concatenation, all integer fields in
big-endian order:

```text
INVENTORY_DOMAIN
issuer_key_id                 u64
account_handle_length         u32
account_handle                UTF-8 bytes
inventory_generation          u64
active_count                  u32
active                        active_count × DeviceBinding
revocation_floor_generation   u64
revoked_count                 u32
revoked                       revoked_count × Revocation
```

`INVENTORY_DOMAIN` is the ASCII string `Tacenta Inventory Statement v1`.
The account handle is non-empty and at most `MAX_ACCOUNT_BYTES` (256) bytes;
invalid UTF-8 is refused. `active_count` is at most
`MAX_ACTIVE_BINDINGS` (8), and `revoked_count` is at most
`MAX_RECENT_REVOCATIONS` (8). The floor and every terminal generation are no
greater than `inventory_generation`.

`DeviceBinding` is:

```text
device_id                    u32
identity_public_key          32 bytes
capabilities                 u64
replacement_predecessor_tag  0 or 1 byte
replacement_predecessor      32 bytes when the tag is 1
```

Version one defines only capability bit `GROUP_EPOCH_V1` (`1`); the capability
word is non-zero and no other bit is accepted. Active bindings are strictly
sorted by the complete tuple above. A replacement predecessor is the
32-byte `binding_commitment` of the exact retired binding, not a device-id or
identity-key alias. The inventory codec treats `identity_public_key` as an
opaque 32-byte field; a product accepting it as an identity key must apply the
canonical-key, contributory-agreement and signature rules above before signing
or relying on a statement. The codec's canonical order does not by itself
establish one-device-per-identity policy: the product must reject duplicate
`device_id` values and define its identity/revocation policy explicitly.

`Revocation` appends `terminal_generation` (u64) to a `DeviceBinding`.
Revocations are strictly sorted by their complete encoded tuple, each terminal
generation is greater than `revocation_floor_generation` and no greater than
`inventory_generation`, and an exact binding cannot occur in both `active` and
`revoked`. These are canonicality/refusal rules; they do not decide account
ownership or freshness beyond the stated generation bounds.

The unsigned decoder must consume exactly the bytes above, reconstruct the
value, re-encode it, and refuse if the bytes differ. A signed statement is the
unsigned preimage followed by a 64-byte XEdDSA signature over:

```text
"Tacenta:inventory-statement:v1" || 0xFF || unsigned_preimage
```

The verifier resolves `issuer_key_id` through its caller-supplied issuer-key
binding and then verifies that signature. The statement does not contain that
binding and does not make the key lookup trustworthy by itself.

`binding_commitment(binding)` is the 32-byte SHA-256 digest of:

```text
"Tacenta:inventory-binding-commitment:v1" || 0xFF || encode(binding)
```

It commits to every binding field, including the predecessor. It is used only
to name the exact binding a replacement retires. The inventory profile has no
group cipher, sender-key ratchet, delivery guarantee, membership privacy
claim, or end-to-end proof attached to it.

## Sources

- The XEdDSA and VXEdDSA Signature Schemes (Trevor Perrin), **revision 1,
  2016-10-20**:
  - section 2.3, for `calculate_key_pair` and the Montgomery private key;
  - section 2.5, for `hash_1`;
  - section 3, for `xeddsa_sign` and `xeddsa_verify`;
  - section 5, for the Curve25519 parameters.
- RFC 7748, section 5, for X25519's clamping and the u-coordinate encoding.
- RFC 8032, section 5.1, for edwards25519's base point, group order and point
  encoding.
