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

## Identity keys

An identity key is the published X25519 public key of an identity secret (The
identity key's secret). The rule for what a party may admit as one is stated
once, in check 6 of Accepting a signed statement, below: a canonical curve
public key whose u-coordinate belongs to a point of the prime-order subgroup of
edwards25519. This section says where the rule applies, what a refusal is, and
why no honest key is refused. It does not state the rule again.

**Where the rule applies.** A party that admits a long-lived identity key
applies the rule to it before relying on the key for anything else:

- an initiator, to the `identity_key` of a prekey bundle, before either
  signature in the bundle is verified and before any random value is drawn,
  agreement computed or encapsulation made (session-establishment.md, Sending
  the initial message);
- a responder, to the `identity` of an initial message, before any private key
  is used on the message (session-establishment.md, Receiving the initial
  message);
- a reader of a stored session, to `our_identity_public` and
  `peer_identity_public`, and a reader of a stored prekey store, to
  `identity_public` (session-persistence.md, Stored curve public keys);
- a verifier of a signature, to the key the signature is checked under
  (Verifying a signature, step 3; Application signatures, below);
- a verifier of a signed inventory statement, to every `identity_public_key`
  in it (Accepting a signed statement, check 6).

An identity key read from any other encoding, such as the identity key field of
the protobuf profile's prekey envelope, is held to the same rule by the party
that admits it. A decoder reads bytes and does not apply the rule
(message-format.md, Curve public keys).

Other curve keys are outside the rule. Ephemeral keys, prekeys and ratchet keys
are held to the canonical encoding and to contributory agreement
(message-format.md, Curve public keys; session-establishment.md), which is all
an agreement input needs.

**A refusal.** A key that fails the rule is refused, and the input that named it
is refused with it. It is a third outcome beside decode failure and
authentication failure (error-handling.md): the input decoded, and no
signature failed, and the key it names is not one this specification admits.
The canonical rule is applied first. A key that is not canonical is refused as it
always was: as a decode failure where a wire encoding is read, and by the kind
that session-persistence.md, Rejection, names for a stored state. The refusal comes
before the work it protects: no random value is drawn, no agreement computed,
no private key used and no stored state changed. It is called *invalid identity
key* on the pages that name it.

**Why an honest key passes.** A published identity key is the X25519 public key
of a clamped secret, which is `kB` for the base point `B` and a scalar `k` (The
identity key's secret). Clamping clears the low three bits and sets bit 254, so
`k` is a multiple of 8 in [2^254, 2^255). The multiples of `q` in that interval
are `4q`, `5q`, `6q` and `7q`, and `q` is 5 modulo 8, so they are congruent to 4,
1, 6 and 3 modulo 8. None is a multiple of 8, so `q` does not divide `k`, `kB`
is not the identity, and it is a point of the subgroup `B` generates. So an
honest party's key is never refused, and no state an honest party's operations
produce is refused for holding it.

**A stored key the rule refuses.** A reader of stored state refuses a state
that holds one, whatever wrote it, and does not repair the state or substitute a
key (session-persistence.md, Stored curve public keys). Such a state can come
from corruption, or from a release that admitted the key when it was first
presented; an honest party's own operations do not produce one. What follows is
the caller's: the bytes are refused, not deleted, and the way forward is a new
session with that peer, established from a bundle whose identity key passes the
rule.

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
3. `A` is a point of the prime-order subgroup: `qA` is the identity. A point of
   small order fails this (`8A` is the identity), a point with x-coordinate 0
   among them whatever `b` is, and so does a point of mixed order, the sum of a
   point of the subgroup and a point of small order. The sign `b` does not
   change the answer. A key that passes steps 1 to 3 is an identity key
   (Identity keys, above).
4. `s`, the signature's last 32 bytes with bit 255 cleared, is below q.
5. Let `R` be the signature's first 32 bytes, `enc(A)` the 32-byte encoding of
   `A` (with sign `b`), and `h = SHA-512(R || enc(A) || M) mod q`. The 32-byte
   encoding of the point `sB - hA` equals `R` byte for byte, so `R` must be the
   canonical encoding of that point. Another spelling of the same point is
   refused.
6. The point `R` encodes is not of small order.

No step multiplies by the cofactor. For a prekey signature `M` is the tagged
key (session-establishment.md, Publishing keys); for an application signature
it is the labelled input below; for an inventory statement it is the labelled
input under Hosted device-inventory statements.

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
- **It is narrower on the order of `A` and `R`.** Revision 1 evaluates the
  equation for whatever `A` and `R` decode to, and accepts where it holds. That
  admits signatures nobody holding a key made, under keys such as u = 0, and
  signatures under a key of mixed order. Step 3 refuses every `A` outside the
  prime-order subgroup, and step 6 refuses a small-order `R`.
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
the published identity key. It first applies the identity-key rule to that key
(Identity keys, above) and accepts no signature under a key that fails it.

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

In this section "must" and "must not" state a requirement on the party named,
and "is refused" means the decoder or verifier stops and returns a refusal. A
refusal by an encoding rule is a decode failure, and a refusal by check 3
below is an authentication failure (error-handling.md). The other checks
refuse a statement that decodes: checks 1 and 2 before its signature has been
examined, checks 4 to 7 after it has verified. A statement that breaks an
encoding rule is refused before check 1, whether it arrived as bytes or was
built in memory.

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
`MAX_RECENT_REVOCATIONS` (8). The floor is no greater than
`inventory_generation`.

`DeviceBinding` is:

```text
device_id                    u32
identity_public_key          32 bytes
capabilities                 u64
replacement_predecessor_tag  u8, 0 or 1; any other value is refused
replacement_predecessor      32 bytes, present only when the tag is 1
```

Version one defines only capability bit `GROUP_EPOCH_V1` (`1`): the capability
word is non-zero and no other bit is set. Both lists are sorted in strictly
ascending order of their encodings, compared as unsigned byte strings from the
first byte, so each entry's encoding is greater than the one before it and no
entry repeats. `active` orders the `DeviceBinding` encodings and `revoked`
orders the `Revocation` encodings. The leading fields are fixed-width
big-endian integers and byte strings, so this is ascending `device_id`, then
ascending `identity_public_key`, then ascending `capabilities`, then a binding
without a predecessor before one with (tag 0 before tag 1), then ascending
`replacement_predecessor`; entries of `revoked` for one binding are then
ordered by ascending `terminal_generation`. No `DeviceBinding` encoding is a
prefix of another, so the comparison always ends on a differing byte.

Two bindings are the same exact binding when all four of their fields are equal
(`device_id`, `identity_public_key`, `capabilities`, and the predecessor tag
and value), that is, when their encodings are equal. A `terminal_generation`
belongs to a `Revocation`, not to its binding. A replacement predecessor is
the 32-byte `binding_commitment` of the exact retired binding, not a device-id
or identity-key alias. The encoding treats `identity_public_key` as an opaque
32-byte field; the checks a verifier applies to it are under "Accepting a
signed statement" below. Canonical order does not by itself establish
one-device-per-identity policy. Apart from the checks listed there, identity
and revocation policy is the verifier's.

`Revocation` appends `terminal_generation` (u64) to a `DeviceBinding`. Each
terminal generation is greater than `revocation_floor_generation` and no
greater than `inventory_generation`, and an exact binding cannot occur in both
`active` and `revoked`. The same binding can occur in `revoked` more than once
with different terminal generations, since the entries differ; the format does
not refuse that (see the unchecked properties below). These are
canonicality/refusal rules; they do not decide account ownership or freshness
beyond the stated generation bounds.

The unsigned decoder refuses an input that breaks any rule above. It must
consume exactly the bytes above, so trailing bytes are refused, and it must
refuse a value whose re-encoding differs from the input. A signed statement is
the unsigned preimage followed by a 64-byte XEdDSA signature. The last 64 bytes
are the signature and every byte before them is the unsigned preimage, which
must decode exactly, so an input shorter than 64 bytes or one whose remaining
bytes do not decode is a decode failure. The signature is over:

```text
"Tacenta:inventory-statement:v1" || 0xFF || unsigned_preimage
```

The verifier resolves `issuer_key_id` through its caller-supplied issuer-key
binding and then verifies that signature. The statement does not contain that
binding and does not make the key lookup trustworthy by itself. A statement
that decodes and whose signature verifies is not thereby accepted; see
"Accepting a signed statement" below.

An issuer must apply the encoding rules, check 5 and check 6 below to a
statement before it signs it, and must not sign one that fails any of them:
every verifier refuses such a statement.

`binding_commitment(binding)` is the 32-byte SHA-256 digest of:

```text
"Tacenta:inventory-binding-commitment:v1" || 0xFF || encode(binding)
```

where `encode(binding)` is the `DeviceBinding` encoding above. A binding whose
capability word breaks the rule above has no encoding, so it has no commitment
and the function refuses it. The commitment covers every binding field,
including the predecessor. It is used only to name the exact binding a
replacement retires. The inventory profile has no group cipher, sender-key
ratchet, delivery guarantee, membership privacy claim, or end-to-end proof
attached to it.

### Accepting a signed statement

Decoding establishes syntax and canonical form. Verifying the signature
establishes that the issuer key the verifier resolved signed exactly these
bytes. Neither establishes that the statement is one to act on. A verifier that
relies on a statement applies these checks in this order and refuses on the
first that fails:

1. `account_handle` equals, byte for byte, the account the verifier asked
   about. This comes before any lookup, so a valid statement for another
   account, signed under an issuer key that serves several accounts, is
   refused.
2. The verifier's issuer-key binding resolves `(issuer_key_id, account_handle)`
   to a verification key. An unbound issuer is refused.
3. The signature verifies under that key. The 32 bytes the binding returns are
   read as the key `u` of Verifying a signature, whatever they are, and the
   message `M` is the input above, so a key that fails steps 1 to 6 there is a
   signature that does not verify, not an unbound issuer.
4. The verifier's freshness rule accepts `inventory_generation` for the
   account. The format carries a generation and a floor but no freshness rule:
   equality with a stored value, a window, or any other rule is the
   verifier's. The format does not distinguish two different validly signed
   statements at one generation. The rule runs before checks 5 to 7, which can
   still refuse the statement, so it must have no effect of its own: a
   verifier records a generation as seen, or advances a stored one, only
   after check 7 has accepted the statement. Where statements can be verified
   concurrently, that step is one atomic step that evaluates the freshness rule
   again against the value then stored and, if the rule accepts, records the
   generation; if it does not, the statement is refused as this check refuses
   it. A stored value never decreases. Otherwise two statements can both pass
   this check and the later write can lower the record.
5. No two entries of `active` share a `device_id`. An active and a revoked
   binding may share one: that is a device whose key was replaced under its old
   id.
6. Every `identity_public_key`, in `active` and in `revoked`, is an identity
   key: a canonical curve public key (message-format.md, Curve public keys)
   whose u-coordinate belongs to a point of the prime-order subgroup of
   edwards25519, the subgroup that `B` generates, of order `q` (Signing). A
   verifier tests that in three steps. `u` is not p − 1. `y = (u − 1) / (u + 1)
   mod p` is the y-coordinate of a point `P` of edwards25519 (Verifying a
   signature, step 2). And `qP` is the identity; the two points with that
   y-coordinate give the same answer, so the sign of x does not matter.
   Besides the non-canonical spellings (message-format.md), this refuses:
   - the five low-order values: the u-coordinates 0, 1 and p − 1, and the two
     of order eight,
     `e0eb7a7c3b41b8ae1656e3faf19fc46ada098deb9c32b1fd866205165f49b800` and
     `5f9c95bca3508c24b1d0b1559c83ef5b04445cc4581c8e86d8224eddd09f1157` (32
     bytes each, little-endian). X25519 with any of them yields the all-zero
     string for every private key;
   - a u-coordinate that no point of the curve has, because it lies on the
     quadratic twist (u = 2 is one);
   - a u-coordinate of mixed torsion: the sum of a point of the subgroup and a
     low-order point. It agrees exactly as the subgroup point it was built
     from, so one key would have eight spellings, and a policy that
     compares keys by bytes could be evaded by respelling a key.

   A key an honest device publishes is the X25519 public key of a clamped
   secret, which is `kB` (The identity key's secret), so it passes. Exactly one
   spelling of a key passes, so check 7 can compare identity keys as bytes.
7. The verifier's own policy accepts each binding and then the statement as a
   whole. The verifier applies check 6 to every entry, those of `active` and
   then those of `revoked`, each in encoded order, before it applies check 7
   to any binding, so its binding and statement policies never run on a
   statement that carries an unsound key. It then applies the binding policy to the entries of `active`
   in encoded order and then to the entries of `revoked` in encoded order,
   telling it the binding and which list it came from, and stops at the first
   refusal. The statement policy runs only when every binding has been
   accepted, and it is given the whole statement as verified.

The format does not check the following, so a verifier that needs any of them
checks it itself:

- **Chain of custody for a replacement.** `replacement_predecessor` need not
  name a binding in this statement's `revoked` list, and nothing checks that it
  names a binding at all: a marker equal to the commitment of a binding that
  is still in `active` is accepted. Revocations at or below
  `revocation_floor_generation` are dropped from the statement, and the
  replacement stays in `active` with its marker, so the marker can outlive the
  tombstone it names. A replacement may also carry a new `device_id`. An
  honest issuer can therefore produce a statement whose marker names no listed
  tombstone. Checks 1 to 6 do not refuse it, and a verifier must not refuse it
  solely because the marker names no listed binding. Checking custody needs the
  verifier's own record of earlier statements.
- **Uniqueness and reactivation.** The same identity key on more than one
  binding, a revoked key listed again as active, a replacement identical to
  what it replaces, and the same binding listed more than once in `revoked`
  are all accepted by the format. Whether they are acceptable is the
  verifier's policy, and it needs the whole statement to decide (check 7). A
  binding leaves `revoked` once the floor reaches its terminal generation, so
  a verifier that must refuse reactivation beyond that window needs its own
  record of revoked keys.
- **Freshness and equivocation**, as check 4 states.

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
