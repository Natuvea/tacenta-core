# The Triple Ratchet

This page describes how the two message ratchets combine. It is our own
description, written from the published specification named in Sources.

The name counts ratchets, not steps: the symmetric-key and Diffie-Hellman
ratchets of the Double Ratchet, plus the sparse post-quantum ratchet. What the
composition adds is not a third mechanism but a rule for using the two it
already has together.

## The idea, and why it is the right shape

Run both ratchets in parallel and use **neither** of them to encrypt. Each is
asked only for a message key. The key that actually encrypts is derived from the
pair.

That gives hybrid security in the strict sense: an attacker must break *both*
the elliptic-curve assumptions and the post-quantum ones. Breaking either alone
yields one of the two inputs and nothing else.

It is worth being clear about what this rules out, because it is the reason we
do not deploy the sparse ratchet on its own. Replacing the Diffie-Hellman
ratchet with a post-quantum one *substitutes* one assumption for another. It
would leave us better off against a future quantum adversary and worse off
against a classical one, since the post-quantum agreement is younger and its
post-compromise recovery is slower. Running both is the only configuration where
every guarantee we have today is preserved and the post-quantum one is added.

## State

Nothing new: a Double Ratchet state and a sparse post-quantum ratchet state,
side by side and independent. Neither knows about the other.

This is the property that makes the composition tractable for us, and it is
worth saying plainly. **The Double Ratchet is unchanged.** Its state, its
derivations, its skipped-key handling, and everything proved about it carry over
untouched. What changes is only that its message key is no longer expanded
into the encryption key itself but is one of two inputs to the key that is.

## Initialisation

Both ratchets are initialised from the session establishment described on the
session-establishment page, but each needs its **own** thirty-two byte secret,
and the handshake produces one. So the shared secret is expanded into two by a
key derivation, and each ratchet is initialised from its own half.

The expansion is HKDF-SHA256 with a 32-byte zero salt, `SK` as input keying
material and `SPLIT_INFO` as `info` (CONSTANTS.md), producing 64 bytes. The
first 32 initialise the Double Ratchet ([ratchet.md](ratchet.md),
Initialisation) and the last 32 the sparse ratchet, in direction `A2b` for the
initiator and `B2a` for the responder
([sparse-pq-ratchet.md](sparse-pq-ratchet.md), Initialisation).

This is the single change the composition forces on the handshake, and it is
small: the derivation gains an expansion step and the two halves go to different
places. It is nonetheless a change to a part of the system that is already
specified, modelled, and proved, and it has to be made in all of those places
together.

Bob's signed prekey continues to serve as his initial ratchet public key, as it
does without the composition.

## Sending and receiving

Sending asks each ratchet for a message key, combines the two (below) into the
key that the message-key expansion turns into the encryption key, and builds a
header carrying **both** ratchets' headers: the Diffie-Hellman ratchet's public
key, previous chain length, and message number, alongside the sparse ratchet's
epoch and message number and the agreement's own epoch, message type and
codeword (message-format.md).

Receiving is the mirror: each half of the header goes to its own ratchet, each
returns a message key, and the two are combined the same way.

Both run the classical half first and the sparse half second, and neither
leaves one half moved without the other:

- **A send runs on a copy** of the state and adopts it only once both halves
  have produced their keys. A refusal from either half changes neither.
- **A receive yields a candidate** state along with the key, and changes
  nothing itself. The candidate is adopted only once the message has
  authenticated under that key. If either half refuses, or the message does
  not authenticate, the candidate is discarded, and with it every change it
  carried: keys used, stored, expired or evicted, and any Diffie-Hellman step.

In both, the session adopts the agreement's next state at the same moment, and
on a receive the ratchet private key a Diffie-Hellman step generated.

Every receive computes two Diffie-Hellman outputs with the header's
ratchet public key: one under the current ratchet private key, and one under
the freshly generated private key a step would adopt. If either is not
contributory (session-establishment.md, Notation), the message is refused and
nothing changes. The check runs whether or not the message would take a step,
before either ratchet runs and before the tag is checked. It covers the ratchet
message inside an initial message, where the current ratchet private key is
the signed prekey's.

The copy is what the leaf ratchets require of their callers. Either may have
moved when it returns an error -- the Double Ratchet having stored keys and
taken its Diffie-Hellman step, the sparse ratchet having folded in the
agreement's secret, before a later check refuses -- so a state that returned
an error is spent and is not kept.

The specification requires the composite header to be parsed unambiguously. That
is a requirement on the encoding, not on the ratchets, and it lands on the
message-format page, where the same requirement already governs the associated
data. It is the kind of obligation that is cheap to state and cheap to check,
and expensive only if left implicit.

**Partly discharged, and the part that is not is the part the requirement is
about.** The encoding is `Model.CompositeHeader`, and
`Proofs.Serialization.decode_encode_composite` proves that decoding an encoded
header returns the header and whatever followed it, for every header whose curve
key is thirty-two bytes and whose codeword, if it has one, is a full chunk.

That theorem does not say the parse is unambiguous. It quantifies over headers
and asks about the bytes the encoder produced, so it can say nothing about the
bytes the *decoder* accepts. A decoder that accepted every byte string and
returned a fixed header would satisfy it.

Unambiguity is the other direction: of the byte strings the decoder accepts, is
each one the encoding of what it decoded to? Both decoders are built to meet
it: a presence byte outside its two values is rejected, the index and chunk
bytes must be zero when the codeword is absent, and the Rust side has a test
that mutates every byte position and asserts that whatever the decoder accepts
re-encodes to itself.

What remains is the Lean statement, `decode bs = some (h, rest) → encode h ++
rest = bs`. It needs the inverse of each big-endian read, which `bv_decide`
settles one byte at a time. Until it is proved, the claim is that the decoder
is canonical by construction and by test, not by proof, and this obligation
stays open.

Unambiguity is bought rather than argued: every field has a width known before it
is read, including the agreement's optional codeword, which is a presence byte
followed by the full width regardless and zeroed when absent. That costs
thirty-four bytes on a message carrying no codeword and it means the decoder's
shape never depends on a value it has just read. The whole header is a hundred
and two bytes against the Double Ratchet's forty-two, which is the bandwidth
cost this page names below in the abstract and this is the number. Both figures
include the two-byte version-and-type prefix, so they are comparable: 2 + 40 for
the classical header, whose `HEADER_LEN` is the 40 without the prefix, and
2 + 100 for the composite, whose `COMPOSITE_LEN` is the 102 with it.

## What the combination must be

The published specification says this twice, at two strengths, and we follow
the stronger one.

**Section 6.3 defines it**: a key derivation keyed by the concatenation of the
two thirty-two byte secrets, applied to a unique constant naming the protocol
and its parameters. **Section 7.2 recommends parameters**: the post-quantum
message key as the **salt**, the classical one as the **input keying material**,
the protocol constant as `info`, and an output the AEAD's key length.

We follow §7.2's parameters. §6.3's definition alone would also be met by
concatenating both keys into the derivation's input, and a recommendation is
not a mandate, but following one costs nothing here and departing from one
would need a reason we do not have.

The combination's output is thirty-two bytes, the length of a Double Ratchet
message key, and it takes that key's place: the message-key expansion
([ratchet.md](ratchet.md), Derivations) turns it into the AES-256 key, the
HMAC-SHA256 key and the IV the AEAD uses. It is not itself the encryption key.

Note the salt and IKM are the other way round from the way they read. That
inversion is the same one `KDF_RK` has, and it is easy to write backwards.

The property the composition rests on is that the combination must not be
recoverable from one input alone, or the hybrid claim fails against an attacker
who has broken one side. That is a property of HKDF and sits at the trusted
primitive boundary.

No second property is needed of the derivation's input. A construction that
concatenated the two keys would need the concatenation to be unambiguous,
which the fixed thirty-two byte width of each key would give. Under §7.2 the
two keys reach the derivation through different arguments, so distinct pairs
are distinct inputs by construction and there is nothing to prove.

## What this costs

**Bandwidth.** Every message now carries the agreement's data as well as the
curve public key. The sparse agreement exists to keep that affordable, but it is
not free.

**Two ratchets' worth of state and failure modes.** Each maintains its own
chains, its own skipped-key store, and its own bounds. A message decrypts only
if *both* ratchets can produce their key, so the error surface is the union of
the two, not the intersection.

**Verification surface.** Roughly double, and slightly more than double once the
composition itself is counted.

## Sources

- Signal's published Double Ratchet specification (Trevor Perrin, editor; Moxie
  Marlinspike; Rolfe Schmidt), **revision 4, 2025-11-04**, Section 6 for the
  composition and Section 7.1 for the integration with the handshake, including
  the expansion of the session secret into one secret per ratchet. The archived
  copy this page was written from is pinned by SHA-256 in the conformance
  manifest.
- The sparse post-quantum ratchet is described on its own page, and the
  agreement beneath it on the ML-KEM Braid page.

The constant that names the protocol in the combination is `TR_PROTOCOL_INFO` in
the specification's terms, and is application-specific by design. Ours is
`Tacenta_CURVE25519_SHA-256_MLKEM1024`, recorded at tier `ours` in
[CONSTANTS.md](../CONSTANTS.md) alongside the other protocol identifiers.

It is not wire-sensitive: message-layer interoperability is not attempted,
so this constant is ours to choose rather than ours to discover.
