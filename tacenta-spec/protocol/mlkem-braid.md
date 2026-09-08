# The ML-KEM Braid

The agreement the [sparse post-quantum ratchet](sparse-pq-ratchet.md) is
instantiated with. It produces a sequence of post-quantum shared secrets, one
per epoch, between two parties who can only exchange small messages.

This page does not restate the protocol. The published ML-KEM Braid
specification (Rolfe Schmidt, revision 1 dated 2025-02-21, last updated
2025-09-26, pinned by SHA-256 in the conformance manifest) defines the
incremental KEM interface (its section 1.2), chunking with erasure codes
(section 1.3), the parameters, messages, internal authentication, state
machine, transitions, and initialization (sections 2.2 through 2.6), and the
security considerations (section 3). Read it for the protocol. This page
records only what this implementation fixes where the specification leaves a
choice, and the properties of the composition that a caller needs to know.

## The shape, in one paragraph

An ML-KEM-1024 encapsulation key and ciphertext are each 1,568 bytes, and a
message on the wire has room for a few hundred bytes of overhead. So one key
agreement is spread across many messages: large values travel as codewords of
an erasure code, so a receiver needs enough chunks rather than particular ones,
and the ciphertext is computed in two halves so that both sides can transmit
at once. Each completed exchange is an epoch, each epoch yields one shared
secret, and the two sides swap roles at the end of every epoch. Both sides
authenticate the exchange internally with a ratcheted authenticator seeded from
a preshared secret, which for this implementation is the
[PQXDH](session-establishment.md) output.

## What this implementation fixes

- **KEM.** ML-KEM-1024, through the incremental interface, from `libcrux-ml-kem`
  (`tacenta-core/kem`). The KEM is at the trusted boundary.
- **Erasure code.** Reed-Solomon over GF(2^16), as the specification recommends,
  with a 32-byte chunk (`CHUNK_BYTES` in [CONSTANTS.md](../CONSTANTS.md)). The
  field and the interpolation the decoder performs are modelled in
  `Model/Gf65536.lean` and `Model/Polynomial.lean`; the delta property that
  decoding rests on is proved there, and the erasure recovery it implies is
  checked on an instance.
- **MAC.** HMAC-SHA256. Epochs are unsigned 64-bit integers, big-endian on the
  wire.
- **Labels.** The four derivation suffixes the specification states are used
  verbatim and recorded at tier `fact` in [CONSTANTS.md](../CONSTANTS.md).
  `PROTOCOL_INFO`, whose shape the specification gives by example and whose
  value it leaves to the implementation, is `Tacenta_MLKEM1024_SHA-256`, tier
  `ours`.
- **Message types on the wire.** The specification's message-type set minus
  `Ct1Ack`, which this implementation never produces and its decoder
  rejects. The byte
  assignment of the remaining types is ours (`AgreementType` in
  [CONSTANTS.md](../CONSTANTS.md)).
- **States.** The eleven live states of the specified machine plus a terminal
  `Failed` state. Their stable numbering, `state_tag`, is recorded in
  [CONSTANTS.md](../CONSTANTS.md) and is what persistence writes
  ([session-persistence.md](session-persistence.md)).
- **Verification failure is terminal.** The specification says to abandon the
  session on a MAC failure. This implementation makes that unrepresentable
  otherwise: a failed verification moves the Braid to `Failed`, and `Session`
  reports it through `agreement_failed()` until the session is re-established.
- **Epoch mismatch.** A message stamped with an epoch other than the one a
  state expects is ignored, as the specification prescribes for an unreliable
  transport. Liveness under a peer that never sends the expected epoch is
  therefore a property of the layer above, not of the Braid.

## Properties a caller must know

**A Braid output is not a session key.** The epoch key is derived from the KEM
shared secret and the epoch alone. The preshared secret seeds the ratcheted
authenticator and enters nothing else, so the epoch key carries no binding to
the handshake or to the peers. That is what a key agreement produces, and it
is safe only in composition: in the [Triple Ratchet](triple-ratchet.md) the
output is mixed into a root key that does depend on the handshake, and that
mixing is the only reason it is safe. A characterisation test in
`tacenta-core` pins this property so a change to the derivation is a visible
event.

**`ct1` is authenticated when `ct2` arrives, not when `ct1` does.** The
ciphertext MAC covers both halves. A decoded `ct1` is therefore not evidence
of anything until the epoch completes, and the implementation treats it that
way. A wrong `ct1` yields a wrong shared secret and the MAC then fails, so
nothing secret is exposed.

**Healing cost.** How long a compromise persists is the number of messages
that pass before an epoch completes, and an epoch cannot complete unless both
sides send. The minimum is a function of the chunk size and the KEM; the
maximum is a property of traffic. Measured for these parameters, at
ML-KEM-1024 with a 32-byte chunk and strict alternation, an epoch costs about a
hundred messages. The relationship to chunk size is close to linear, so a
larger chunk heals proportionally faster at the cost of per-message overhead;
32 bytes is chosen to fit a small envelope. The measurement lives in
`tacenta-core/tests/post_quantum_stack.rs`, asserted as a range so that a
change to the chunking has to be stated.

**Encoder lifetime.** An encoder emits at most 65,536 codewords. An epoch whose
peer never replies exhausts its encoder at that point; the refinement theorems
in `tacenta-proofs` take a live encoder as a precondition and `CLAIMS.md`
records it.

## Sources

- The published ML-KEM Braid specification (Rolfe Schmidt), **revision 1,
  2025-02-21, last updated 2025-09-26**, pinned by SHA-256 in
  `tacenta-test-vectors/conformance-manifest.md`. It is authoritative for the
  protocol; this page defers to it wherever the two could be read to differ.
- Signal's published Double Ratchet specification, revision 4, section 5, for
  the sparse continuous key agreement interface this protocol instantiates
  ([sparse-pq-ratchet.md](sparse-pq-ratchet.md)).
- FIPS 203 for ML-KEM.
