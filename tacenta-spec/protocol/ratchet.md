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
- The count of accepted receives, by which stored keys expire; each key in
  `MKSKIPPED` carries the count at which it was stored (Skipped keys).

## Derivations

The published specification fixes the algorithms below and leaves the
`info` byte strings application-specific. Ours are free choices, recorded at
tier `ours` in [CONSTANTS.md](../CONSTANTS.md): `RK_INFO` (`Tacenta RK`) and
`MK_INFO` (`Tacenta MK`). Message-layer interoperability with another
implementation is not attempted, so there is no peer's value for them to
match.

- **`KDF_RK(rk, dh_out)`**: root key derivation. HKDF-SHA256 with the salt set
  to `rk`, input keying material `dh_out` (a Diffie-Hellman output), and `info`
  `RK_INFO`, producing 64 bytes split into a new `RK` (first 32) and a chain
  key (next 32).
- **`KDF_CK(ck)`**: chain step. `HMAC-SHA256(ck, 0x01)` is the message key, and
  `HMAC-SHA256(ck, 0x02)` is the next chain key. The chain key advances one step
  per message and the previous chain key is discarded.
- **Message-key expansion**: the 32-byte message key is expanded by HKDF-SHA256,
  with a 32-byte zero salt, the message key as input keying material, and
  `info` `MK_INFO`, into 80 bytes: an AES-256 key (first 32), an HMAC-SHA256
  key (next 32), and a 16-byte IV (last 16), which the AEAD (see
  message-format) then uses.

The primitives themselves are implemented at the trusted boundary and named
in the proofs' trusted base (`tacenta-proofs/CLAIMS.md`); this page composes
them.

## Initialisation

Session establishment leaves both parties holding the same 32-byte secret
`SK`, which under the Triple Ratchet is the classical half of the split secret
(triple-ratchet.md, Initialisation), and leaves the party that sends first
holding the other party's signed prekey. The two roles start differently:

- **The party that sends first** (the initiator) generates a fresh ratchet key
  pair as `DHs`, sets `DHr` to the peer's signed prekey, and derives
  `(RK, CKs) = KDF_RK(SK, DH(DHs, DHr))`. It has no receiving chain.
- **The party that receives first** (the responder) sets `RK = SK` and `DHs` to
  its signed prekey key pair. It has neither chain, and `DHr` is absent.

Both start with `Ns`, `Nr`, `PN` and the count of accepted receives at zero,
and nothing stored. The responder cannot send until it has received: its first
receive finds `DHr` absent and takes a Diffie-Hellman step, whose receiving
chain comes from `KDF_RK(SK, DH(signed prekey, header key))`, the derivation
that gave the initiator its sending chain.

## The symmetric-key ratchet

To send, advance the sending chain: `(CKs, mk) = KDF_CK(CKs)`, increment `Ns`,
and encrypt under `mk`. To receive an in-order message, advance the receiving
chain the same way. A message key is used for exactly one message and then
discarded, which is what makes past messages unrecoverable from present state.

## The Diffie-Hellman ratchet

A message header carries the sender's current ratchet public key. When a party
receives a header that matches no stored key and whose ratchet key differs from
`DHr`, or `DHr` is absent, it takes a DH ratchet step. The comparison is with
`DHr` alone, so a header returning to an earlier ratchet key steps too.

1. If there is a receiving chain, store its skipped message keys from `Nr` up
   to the header's `PN`, exclusive (see Skipped keys). This skip is checked
   against `MAX_SKIP` on its own, before the step, and not together with the
   skip on the new chain that follows; the store's total bound covers both.
2. Derive a new receiving chain: `(RK, CKr) = KDF_RK(RK, DH(DHs, header key))`,
   set `DHr` to the header key, reset `Nr`, and record `PN = Ns`, `Ns = 0`.
3. Generate a fresh `DHs`, and derive a new sending chain:
   `(RK, CKs) = KDF_RK(RK, DH(DHs, DHr))`.

Because each step folds a fresh Diffie-Hellman output into the root key, an
attacker who learns the state stops being able to derive keys once both parties
have stepped, which is post-compromise security.

A header whose ratchet key equals `DHr` while there is no receiving chain is
refused (`NoReceivingChain`). Only the party that sent first holds that state,
before its first receive, while `DHr` is still the peer's signed prekey.

## Message format

Each message carries a header and a ciphertext. The header is the sender's
ratchet public key, `PN`, and `Ns`. The ciphertext is the AEAD output over the
plaintext, with the serialized header bound in as associated data so it cannot
be altered without detection. The exact header and ciphertext encodings are
specified on the message-format page, where under the Triple Ratchet this
header travels inside the composite header. The encodings are ours, not the
published specification's, and their values are recorded at tier `ours` in
[CONSTANTS.md](../CONSTANTS.md), as the Derivations labels are; the
model-generated vectors under `tacenta-test-vectors/vectors/serialization/` are
normative examples of them.

## Sending and receiving

- **Send**: refused, before anything changes, if there is no sending chain
  (`NoSendingChain`) or `Ns` is `u32::MAX` (`ChainExhausted`). Otherwise
  `(CKs, mk) = KDF_CK(CKs)`; header is `(DHs.public, PN, Ns)`; increment `Ns`;
  output the header and the AEAD encryption of the plaintext under `mk` with
  the header as associated data.
- **Receive**: if the header's ratchet key and message number `N` match a
  stored skipped key, use and remove it. Otherwise, if the header's ratchet key
  differs from `DHr`, or `DHr` is absent, take a DH ratchet step. Then skip and
  store keys from `Nr` up to `N`, exclusive; refuse if there is no receiving
  chain (`NoReceivingChain`) or `Nr` is now `u32::MAX` (`ChainExhausted`);
  advance the receiving chain once, increment `Nr`, decrypt, and discard the
  key.

So message number `u32::MAX` is never used on a chain. Nor is a key ever stored
under it: a skip stores keys numbered from `Nr` up to the header's `PN` or `N`,
exclusive, and both are 32-bit fields, so every number a key is stored under is
at most `u32::MAX - 1` and none can be out of range.

A message whose ratchet key equals `DHr`, whose number `N` is below `Nr`, and
whose key is not stored is not accepted: its key has already been used,
expired, or evicted.

**A refused receive may already have moved the state.** Keys on the old chain
may have been stored, and the Diffie-Hellman step taken, before a later check
refuses. A caller therefore runs a receive on a copy of the state and treats a
state that returned an error as spent. The Triple Ratchet and the session do
exactly that; their commit rules are on triple-ratchet.md, Sending and
receiving.

## Skipped keys

Out-of-order delivery is expected. When a header shows more messages than the
receiver has processed on a chain, the receiver derives and stores the
intervening message keys in `MKSKIPPED`, so a later arrival still decrypts.

Two separate bounds keep this from exhausting memory, and both are required:

- **`MAX_SKIP`**, the most keys that may be skipped in a *single chain*. A header
  demanding more than this is rejected (`TooManySkipped`). The skip to `PN` on
  the old chain and the skip to `N` on the new one are checked against it
  separately, so one message may store up to twice `MAX_SKIP` keys.
- **`MAX_SKIPPED_STORE`**, the most keys the store may hold *in total*. Because
  each Diffie-Hellman ratchet step starts a fresh chain, a per-chain bound alone
  does not bound the store: a peer that repeatedly ratchets and skips would grow
  it without limit. A skip that would push the store past this bound is refused
  by the ratchet (`SkippedStoreFull`). The published specification requires
  this directly, stating that `MKSKIPPED` raises if too many elements are
  stored. The receiver does not stop there: it makes room, below.

Both are security parameters recorded with the implementation.

**A full store makes room rather than refusing the message.** When a received
message is refused only because a store would pass `MAX_SKIPPED_STORE`, the
receiver (`Session::decrypt`) evicts that store's oldest keys and tries the
message again, on a working copy of the state that it adopts only if the
message then authenticates. It repeats until the message is accepted or refused
for another reason, and refuses it if the store is already empty. Oldest here
means the smallest stored count, ties going to the key stored first; the sparse
ratchet's store evicts the key stored first (sparse-pq-ratchet.md). How many
keys each attempt evicts is implementation-defined: this implementation starts
from the shortfall the header implies, where the state gives one, and doubles
on each further attempt. **The eviction is this implementation's addition**;
the published specification says only that the store raises. Its cost is that
a delayed message whose key was evicted can no longer be decrypted. A forged
header evicts nothing, since nothing is adopted without authentication, but a
peer holding the session can evict by skipping ahead, as it can already fill
the store.

Stored keys also expire. At the end of every accepted receive, after the
stored-key lookup, the count of accepted receives is incremented and every
stored key whose age -- the new count minus the count stored with it -- is at
least `MAX_SKIPPED_AGE` is deleted. The count stored with a key is the count at
the start of the receive that stored it. So a key stored during one accepted
receive can still be used by any of the next `MAX_SKIPPED_AGE - 1` accepted
receives, and is deleted at the end of the last of them if it has not been
(CONSTANTS.md; key-deletion.md). A receive that is refused, or whose message
does not authenticate, counts for nothing. The count stops at `u32::MAX - 1`,
after which keys no longer age (session-persistence.md, Principles).

**Storing a key for a pair already held replaces the held key**
(key-deletion.md). A skip first deletes every stored key under the chain's
ratchet key whose number is in the range it is about to store, `Nr` up to its
bound, exclusive, and then stores the range's keys, in number order, after
every key already in the store. So a replacing key is a new store in both
respects that can be observed. It carries the count at the start of the
receive that stored it, not the count of the key it replaced, so it expires
as late as any other key that receive stored. And it is last in the store's
order, which decides eviction ties and the persisted order
(session-persistence.md, Ratchet state). A skip replaces a key only when a
peer returns to a ratchet key it had left; a key stored under that ratchet key
at a number outside the range is kept.

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
its only effect here is that a message key derived by this ratchet is combined
with the sparse ratchet's before the message-key expansion, rather than being
expanded itself.
What this page describes is what runs -- it is not *all* of what runs.

## Security properties

Forward secrecy comes from discarding each message key and each superseded chain
key. Post-compromise security comes from the Diffie-Hellman ratchet reseeding
the root key from fresh agreements. Both are stated as numbered requirements.
Each requirement names the adversaries it holds against and the assumptions it
rests on, and says whether it is proved, assumed or tested only. They are
REQ-FS-01 to REQ-FS-06 in security-properties/forward-secrecy.md, and
REQ-PCS-01 to REQ-PCS-03 in security-properties/post-compromise-security.md.
`key-deletion.md` gives the deletions forward secrecy rests on, and
`tacenta-proofs/CLAIMS.md` is the record of what is proved.

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

Byte-level conventions that the published specification leaves open -- the
`info` strings and the header and ciphertext encodings -- are ours: their
values are recorded at tier `ours` in [CONSTANTS.md](../CONSTANTS.md), and the
encodings on the message-format page. Message-layer interoperability with
another implementation is not attempted, so none of them was determined
against a peer.
