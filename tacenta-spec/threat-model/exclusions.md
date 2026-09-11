# Exclusions

What is outside this specification. Each exclusion is numbered. No requirement
holds against what is excluded here, and nothing here is a requirement.
security-properties/limitations.md lists the gaps inside the scope; this page
lists what is outside it.

## EX-01: metadata and traffic analysis

The protocol does not hide who communicates with whom, when, how often, or how
much.

On the wire:
- an initial message carries the initiator's identity key and the identifiers
  of the prekeys it used;
- every ratchet message carries its ratchet public key, message numbers, epochs
  and agreement data in the clear;
- a ciphertext's length gives the plaintext's length to within a block.

A directory sees who fetches whose bundle. The Double Ratchet's
header-encryption variant is not used (EX-13).

## EX-02: endpoint compromise beyond a point in time

ADV-02 takes a party's state once. The following are excluded:
- an adversary that controls a device, reads its state continuously or
  repeatedly, or remains in it;
- one that subverts a party's random number generator (ASM-01), its
  application or its user interface;
- one that reads plaintexts after `decrypt` returns them.

Such an adversary takes every agreement as it is made, so nothing heals
(REQ-PCS-01 requires an agreement it did not take).

## EX-03: denial of service beyond the stated bounds

The bounds this specification states are these:

- **Decoders and receive paths.** The decoders a peer's bytes reach, and the
  leaf crates' receive paths, cannot panic (CLAIMS.md, "Proved (tier T1, the
  message decoders cannot fail)" and the leaf crates' T1 sections).
- **Skipping.** A skip is refused beyond `MAX_SKIP` before any key is derived.
  Each skipped-key store is held to `MAX_SKIPPED_STORE` (ratchet.md, Skipped
  keys; CLAIMS.md, "Proved (tier T2, functional properties of the model)").
- **The replay record.** It holds at most `MAX_LAST_RESORT_SEEN` entries per
  last-resort key and fails closed (session-establishment.md, Replay, and why
  the ratchet must follow).
- **Cost of a forgery.** A forged message claiming a number 900 ahead was
  measured to cost a receiver about thirteen ordinary receives. `MAX_SKIP`
  caps the gap (LIMITATIONS.md, "Constant-time behaviour is assumed, not
  proven").

Everything else is outside this specification, including:
- an ADV-01 that drops or floods traffic;
- a directory that withholds bundles;
- a peer that stalls healing, ages or evicts stored keys, or fails the Braid
  (ADV-06);
- an attacker that fills the replay record, which refuses last-resort
  handshakes until the next rotation;
- work done per byte of input. No proof constrains it (LIMITATIONS.md, "What a
  green proof does not say about cost").

## EX-04: group messaging

Unspecified. protocol/group-messaging.md is an outline, marked as a scaffold,
and its mechanism is an open question. No requirement covers groups, sender
keys or group membership.

## EX-05: devices

Unspecified. How devices relate to identities, and how one identity uses
several devices, are unspecified: protocol/multi-device.md is a scaffold, and
the devices part of protocol/identities-and-devices.md is a scaffold. No
requirement covers more than one device per identity.

## EX-06: key registration and the directory's behaviour

Unspecified. How a party registers its identity key and prekeys is not yet
specified (protocol/key-registration.md is a scaffold). So is how a directory
authenticates the parties it serves, hands out one-time prekeys or rate-limits
fetches. key-deletion.md states what a client expects of the server
(Prekeys at rest), and ADV-04 is what the requirements assume the server may
do instead.

## EX-07: a writer of the persisted store, and protection at rest

Integrity of a persisted session or prekey store against an adversary that
writes it (ADV-05) is outside this specification (ADR-0007). This includes
rolling a store back to an earlier export. Confidentiality of persisted bytes
at rest is the caller's (ASM-12). The readers check against corruption only
(session-persistence.md, Principles).

## EX-08: side channels beyond what is assumed

Excluded, beyond the timing behaviour ASM-08 assumes and the erasure ASM-09
assumes:
- power, electromagnetic and acoustic emanations;
- cache and speculative-execution attacks beyond the constant-time behaviour
  assumed;
- fault injection;
- memory remanence, swap and crash dumps;
- recovery of deleted data from storage media.

## EX-09: trust in identity keys

How a user comes to trust that an identity key belongs to a contact is outside
this specification. That covers verification codes, trust on first use, and
what to do when a contact's key changes (ASM-14).

## EX-10: managing several sessions

Choosing among several sessions with one peer is left to the application:
- which session to keep after simultaneous initiation;
- whether a new session replaces an existing one;
- what to do with a message an existing session refuses.

session-establishment.md, Receiving the initial message, specifies the refusal
and nothing after it.

## EX-11: authentication against a quantum adversary

Mutual authentication rests on the discrete logarithm problem in this revision
(session-establishment.md). An adversary able to compute discrete logarithms on
curve25519 while a handshake runs can impersonate a party. ADV-03 is passive
until it has that power, and no requirement holds against one that is active
with it.

## EX-12: deniability

The published X3DH and PQXDH documents discuss deniability. This specification
states no requirement about it, and nothing in this project analyses or
establishes it.

## EX-13: protocol variants not specified

- **Plain X3DH.** Sessions with peers that omit the encapsulated secret
  (session-establishment.md, Scope).
- **Header encryption.** The Double Ratchet's header-encryption variant
  (ratchet.md, Scope).
- **Interoperability.** Message-layer interoperability with any other
  implementation (message-format.md, Wire-sensitive values).

## EX-14: subverted dependencies, toolchains and builds

An adversary that subverts a primitive library, the Rust or Lean toolchain,
the translation toolchain, or the build that produces a party's binary. The
assumptions ASM-02 to ASM-08 and ASM-15 to ASM-17 are that these are what they
claim to be. Nothing in this specification detects otherwise.
