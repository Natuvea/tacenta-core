# The Double Ratchet

This page specifies the Double Ratchet as tacenta-core implements it. It is our
own description, written from the published specification named in Sources, and
it is the reference the Lean model and the Rust implementation are both written
against.

Two parties who already share a secret root key and one party's ratchet public
key (session establishment, X3DH or PQXDH, is a separate page) exchange messages
so that each message is encrypted under a fresh key. Compromising the state at
one moment does not expose past messages (forward secrecy) and does not expose
messages sent after both parties have taken a fresh Diffie-Hellman step
(post-compromise security). Two ratchets combine to give this: a symmetric-key
ratchet advances a chain of message keys, and a Diffie-Hellman ratchet reseeds
those chains from new key agreements.

## State

Each party keeps:

- `DHs`: its current ratchet Diffie-Hellman key pair (X25519).
- `DHr`: the other party's current ratchet public key, if known.
- `RK`: the 32-byte root key.
- `CKs`, `CKr`: the 32-byte sending and receiving chain keys, either possibly
  empty.
- `Ns`, `Nr`: the message numbers in the sending and receiving chains.
- `PN`: the length of the previous sending chain, sent so the other party can
  tell how many keys to skip.
- `MKSKIPPED`: message keys for messages that arrived out of order, kept by
  `(ratchet public key, message number)` up to a bounded count.

## Derivations

The published specification fixes the algorithms below and leaves the
`info` byte strings application-specific. Those strings, and any other
byte-level convention needed to interoperate with a specific peer, are pinned in
the conformance manifest rather than here, and where the published
specification does not give them they are determined by black-box research under
the interoperability boundary (see the decision records), never from another
implementation's source.

- **`KDF_RK(rk, dh_out)`**: root key derivation. HKDF-SHA256 with the salt set
  to `rk`, input keying material `dh_out` (a Diffie-Hellman output), and an
  application `info`, producing 64 bytes split into a new `RK` (first 32) and a
  chain key (next 32).
- **`KDF_CK(ck)`**: chain step. `HMAC-SHA256(ck, 0x01)` is the message key, and
  `HMAC-SHA256(ck, 0x02)` is the next chain key. The chain key advances one step
  per message and the previous chain key is discarded.
- **Message-key expansion**: the 32-byte message key is expanded by HKDF-SHA256,
  with a zero-filled salt and an application `info`, into an AES-256 key, an
  HMAC-SHA256 key, and a 16-byte IV, which the AEAD (see message-format) then
  uses.

The primitives themselves are implemented at the trusted boundary and named
in the proofs' trusted base (`tacenta-proofs/CLAIMS.md`); this page composes
them.

## The symmetric-key ratchet

To send, advance the sending chain: `(CKs, mk) = KDF_CK(CKs)`, increment `Ns`,
and encrypt under `mk`. To receive an in-order message, advance the receiving
chain the same way. A message key is used for exactly one message and then
discarded, which is what makes past messages unrecoverable from present state.

## The Diffie-Hellman ratchet

A message header carries the sender's current ratchet public key. When a party
receives a header whose ratchet key it has not seen, it takes a DH ratchet step:

1. Store any skipped message keys from the current receiving chain up to the
   header's counts (see Skipped keys).
2. Derive a new receiving chain: `(RK, CKr) = KDF_RK(RK, DH(DHs, header key))`,
   set `DHr` to the header key, reset `Nr`, and record `PN = Ns`, `Ns = 0`.
3. Generate a fresh `DHs`, and derive a new sending chain:
   `(RK, CKs) = KDF_RK(RK, DH(DHs, DHr))`.

Because each step folds a fresh Diffie-Hellman output into the root key, an
attacker who learns the state stops being able to derive keys once both parties
have stepped, which is post-compromise security.

## Message format

Each message carries a header and a ciphertext. The header is the sender's
ratchet public key, `PN`, and `Ns`. The ciphertext is the AEAD output over the
plaintext, with the serialized header bound in as associated data so it cannot
be altered without detection. The exact header and ciphertext encodings are
specified on the message-format page and pinned in the conformance manifest.

## Sending and receiving

- **Send**: `(CKs, mk) = KDF_CK(CKs)`; header is `(DHs.public, PN, Ns)`;
  increment `Ns`; output the header and the AEAD encryption of the plaintext
  under `mk` with the header as associated data.
- **Receive**: if the message matches a stored skipped key, use and remove it.
  Otherwise, if the header's ratchet key differs from `DHr`, take a DH ratchet
  step. Then skip and store keys up to the header's message number, advance the
  receiving chain to that number, decrypt, and discard the key.

## Skipped keys

Out-of-order delivery is expected. When a header shows more messages than the
receiver has processed on a chain, the receiver derives and stores the
intervening message keys in `MKSKIPPED`, so a later arrival still decrypts.

Two separate bounds keep this from exhausting memory, and both are required:

- **`MAX_SKIP`**, the most keys that may be skipped in a *single chain*. A header
  demanding more than this is rejected.
- **`MAX_SKIPPED_STORE`**, the most keys the store may hold *in total*. Because
  each Diffie-Hellman ratchet step starts a fresh chain, a per-chain bound alone
  does not bound the store: a peer that repeatedly ratchets and skips would grow
  it without limit. A step that would push the store past this bound is
  rejected. The published specification requires this directly, stating that
  `MKSKIPPED` raises if too many elements are stored.

Both are security parameters recorded with the implementation. Stored keys
also expire once they have outlived a fixed number of received messages
(`MAX_SKIPPED_AGE` in CONSTANTS.md; key-deletion.md).

## Scope

This page describes the Double Ratchet of Section 3, which is one of the two
ratchets we intend to run. One part of the published specification is out of
scope:

- **Header encryption.** The specification defines an optional
  header-encryption variant; we do not use it. Headers are sent as described
  above, with their integrity bound by the AEAD's associated data rather than
  encrypted.

The exclusion is recorded in the conformance manifest, so the coverage claim is
explicit rather than implied.

**The post-quantum ratchet is in scope, built, and running.** Post-quantum
protection at session establishment alone is not enough: the handshake
protects a session at the moment it is created and adds nothing afterwards, so
an attacker recording traffic against a future quantum computer would be
bounded by what the handshake mixed in and by nothing this ratchet does. A
long-lived session is exactly where that gap would be widest, and the Sparse
Post-Quantum Ratchet and the Triple Ratchet exist to close it.

The two are specified on their own pages, sparse-pq-ratchet.md and
triple-ratchet.md, and both ship: `Session` holds a `tacenta_triple::State` and
a `tacenta_braid::Braid` and drives them as one transaction, and the composite
header carries the agreement's message on every send. **Nothing on this page
changes as a result**: the Triple Ratchet composes this ratchet unaltered, and
its only effect here is that a message key derived by this ratchet becomes one
of two inputs to the encryption key rather than the encryption key itself.
What this page describes is what runs -- it is not *all* of what runs.

## Security properties

Forward secrecy comes from discarding each message key and each superseded chain
key. Post-compromise security comes from the Diffie-Hellman ratchet reseeding
the root key from fresh agreements. Post-compromise security is stated with its
assumptions and limits on the post-compromise-security page; the
forward-secrecy page is still a scaffold, and until it is written
`tacenta-proofs/CLAIMS.md` is the record of what is established about either
property and `key-deletion.md` of the deletions forward secrecy rests on.

## Sources

- Signal's published Double Ratchet specification (Trevor Perrin, editor;
  Moxie Marlinspike; Rolfe Schmidt, revision 3 and later), **revision 4,
  2025-11-04**. It defines the two ratchets, the `KDF_RK` and `KDF_CK`
  constructions, the state variables, the initialisation, encryption, and
  decryption procedures, the header contents, the skipped-key handling, and the
  recommended concrete algorithms (X25519, HKDF-SHA256, HMAC-SHA256, AES-256 in
  CBC mode with PKCS#7 padding, and HMAC over the associated data prepended to
  the ciphertext). The archived copy this page was written from is pinned by
  SHA-256 alongside the other references, so the implemented revision is
  fixed.
- RFC 5869 (HKDF) and RFC 2104 (HMAC), referenced by the above for the
  derivations.

Byte-level conventions that the published specification leaves open, and that a
specific peer requires for wire interoperability, are determined under the
interoperability research boundary and recorded in the conformance manifest.
