# Assets

What the protocol protects. Each asset is numbered so that the adversaries,
assumptions and requirements can name it. For each, this page says where the
protocol holds it and what its loss costs. The requirements that protect it are
in `security-properties/`.

Group messaging and devices are unspecified (exclusions.md, EX-04 and EX-05),
so nothing they would hold is listed.

## Secrets

### AS-01: message plaintexts

The plaintexts an application passes to a session, including the first
plaintext an initial message carries. The protocol holds a plaintext only while
it encrypts or decrypts it. The session state holds no plaintext. What it keeps
of its initial message until the peer replies is the handshake's public fields
(session-persistence.md, Session).

Loss: the loss the protocol exists to prevent.

### AS-02: the identity secret

The 32 bytes that are at once a party's X25519 identity private key and its
XEdDSA signing key (identities-and-devices.md, The identity key's secret;
ADR-0002). Held for the life of the identity.

Loss: an attacker holding it computes `DH1` or `DH2` of every later handshake
in the party's name, and signs prekeys under it. It can therefore initiate as
the party, and publish bundles that verify as the party's. Together with
prekey secrets still held (AS-03), it reveals the shared secret of earlier
handshakes (REQ-FS-05). No ratchet repairs its loss.

### AS-03: prekey secrets

The private halves of a party's published prekeys (session-establishment.md,
Keys; key-deletion.md):

- the signed curve prekey, and the one the last rotation retired;
- the one-time curve prekeys;
- the last-resort KEM decapsulation key, and the one the last rotation retired;
- the one-time KEM decapsulation keys.

A one-time secret is held until the initial message naming it authenticates. A
signed or last-resort secret is held until the rotation after the one that
retires it.

Loss:

- **Signed prekey:** `DH3` of every handshake made against it. It also lets
  the attacker make an initial message its owner accepts as coming from any
  identity (REQ-AUTH-03).
- **Last-resort KEM key:** `SS` of every handshake made against it.
- **One-time prekey:** its part of the one handshake that used it.

### AS-04: handshake secrets

The initiator's ephemeral private key, the agreement outputs `DH1` to `DH4`,
the KEM shared secret `SS`, the shared secret `SK`, and the two halves
`split_secret` expands `SK` into (session-establishment.md; triple-ratchet.md,
Initialisation). All but `SK` are deleted once `SK` is derived. `SK` initialises
the two ratchets and the Braid's authenticator (key-deletion.md, Establishing a
session).

Loss: every key of the session from its start, until the session heals
(REQ-PCS-01, REQ-PCS-03).

### AS-05: classical ratchet secrets

The Double Ratchet's root key `RK`, chain keys `CKs` and `CKr`, the private key
of `DHs`, and the message keys stored in `MKSKIPPED` (ratchet.md, State).

Loss: see the forward-secrecy and post-compromise-security pages, which state
what each of these reveals.

### AS-06: sparse post-quantum ratchet secrets

The sparse ratchet's root key, the chain keys of every epoch it keeps, its
stored skipped keys, and the agreement outputs it folds into its root key
(sparse-pq-ratchet.md, State and Derivations).

Loss: as for AS-05, but healing waits on the agreement's next epoch
(REQ-PCS-03).

### AS-07: ML-KEM Braid secrets

The decapsulation key of the incremental key pair a party holds while it waits
for a ciphertext, the encapsulation state while it completes one, each epoch's
KEM shared secret `K` and epoch key `KDF_OK(K, e)`, and the ratcheted
authenticator's `root_key` and `mac_key` (mlkem-braid.md, Parameters and
derivations; key-deletion.md).

Loss: the epoch key of an epoch whose agreement the attacker took, and so no
post-quantum healing from that epoch. The authenticator keys also let an
attacker complete the agreement with the party in place of its peer
(REQ-PCS-03).

### AS-08: per-message keys

For each message: the classical message key, the sparse ratchet's message key,
their combination (triple-ratchet.md, What the combination must be), and the
`enc_key`, `mac_key` and `iv` the combination expands into (ratchet.md,
Derivations). Each is used for one message and then deleted.

Loss: that one message, and nothing else (REQ-CONF-07).

### AS-09: persisted state

A session's export and a prekey store's bytes (session-persistence.md). They
hold AS-02 to AS-07 in plaintext, as the state held them when written. The
prekey store also holds the last-resort replay record.

Loss of its confidentiality is ADV-02 taking the state. Loss of its integrity
is a store writer's (ADV-05), which is outside this specification (EX-07).

## Properties that are not secrets

### AS-10: authenticity of a conversation

That a session is bound to the identity key it was established with. That a
message a session accepts was made by that peer, for that session, and at that
position in it. And that a message is accepted at most once. Loss lets an
attacker be believed as the peer, move a message between sessions or positions,
or have a message delivered twice (security-properties/authentication.md).

### AS-11: authenticity of published keys

That a signed curve prekey and a KEM prekey in a bundle were published by the
holder of the bundle's identity key, and that every curve public key has one
encoding and so one identity (message-format.md, Curve public keys). Loss lets
a directory or network attacker substitute prekeys, or give one key two
identities in a signature, the associated data, a fingerprint or the
skipped-key store.

### AS-12: state integrity against unauthenticated input

That input nobody authenticated changes nothing durable. What the protocol
requires of it is REQ-AUTH-13: a message that is refused, or that does not
authenticate, leaves every one of the following as it was.

- **In the session:** the classical ratchet's counters `Ns`, `Nr` and `PN`,
  its root key and chain keys, its ratchet key pair and the peer ratchet key
  it holds, and whether it has taken a Diffie-Hellman step; the skipped-key
  store, both the keys in it and the evictions and expiry that take keys out
  of it; the sparse ratchet's epoch, its chains and its stored keys; and the
  Braid's state, including its epoch, its authenticator's two keys, and any
  transition it would take.
- **In the prekey store:** the one-time curve and KEM prekeys, which a
  handshake consumes only once the initial message naming it authenticates;
  the last-resort replay record; the prekeys a rotation retired; and the
  identifier counter `next_id`.

**Deriving is not committing.** A receive must derive a key before it can
check an authenticator at all, so what is required is that nothing durable
moves until the authenticator verifies, not that nothing is computed. The
rules that carry this are stated in triple-ratchet.md (Sending and receiving),
session-establishment.md (Receiving the initial message), key-deletion.md and
error-handling.md: a receive runs on a copy and the copy is adopted only after
the message authenticates, and a refusal changes nothing.

Loss lets anyone who can send bytes desynchronise a session, consume stored
keys, drain one-time prekeys, or fill the replay record.
