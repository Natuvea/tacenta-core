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
records what this implementation fixes where the specification leaves a
choice, specifies exactly what an implementation needs beyond it (the KEM
split, the erasure code, what a receive ignores, and every way into
`Failed`), and gives the properties of the composition that a caller needs to
know.

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
  with a 32-byte chunk (`CHUNK_BYTES` in [CONSTANTS.md](../CONSTANTS.md)),
  specified below under The erasure code. The field and the interpolation the
  decoder performs are modelled in `Model/Gf65536.lean` and
  `Model/Polynomial.lean`; the delta property that decoding rests on is proved
  there, and the erasure recovery it implies is checked on an instance.
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
  The other ways into `Failed` are listed below under Failure.
- **Epoch mismatch.** A message stamped with an epoch other than the one a
  state expects is ignored, as the specification prescribes for an unreliable
  transport. Liveness under a peer that never sends the expected epoch is
  therefore a property of the layer above, not of the Braid.

## The KEM split

The incremental interface is ML-KEM-1024 as FIPS 203 defines it, with the
encapsulation key and ciphertext cut into the pieces the Braid sends. `ek` is
the FIPS 203 encapsulation key, `ByteEncode12(t_hat) || rho` (1,568 bytes);
`H` is SHA3-256 and `G` is SHA3-512.

```
header    = rho (32) || H(ek) (32)   -- H over all of ek: t_hat, then rho
ek_vector = ByteEncode12(t_hat)      -- 1,536 bytes: ek without rho
ct1       = the ciphertext's first 1,408 bytes, the compressed u
ct2       = the ciphertext's last 160 bytes, the compressed v
```

- **Key generation** draws 64 random bytes `d || z` and runs FIPS 203
  `ML-KEM.KeyGen_internal(d, z)`.
- **The first half of encapsulation** draws 32 random bytes `m` and needs only
  `header`: it computes `(K, r) = G(m || H(ek))`, taking `H(ek)` from the
  header, and outputs `ct1` and the shared secret `K`.
- **The second half** draws nothing. From `ek_vector` and what the first half
  kept, it outputs `ct2`. For an `ek_vector` that validates against the
  header, `ct1 || ct2` is the ciphertext `ML-KEM.Encaps_internal(ek, m)`
  produces.
- **Decapsulation** is FIPS 203 `ML-KEM.Decaps` on `ct1 || ct2`, implicit
  rejection included: a wrong ciphertext yields a wrong secret, not an error.
- **Validation.** A completed `ek_vector` is accepted only if
  `H(ek_vector || rho)` equals the hash in the authenticated header and
  `ek_vector` passes the FIPS 203 section 7.2 modulus check,
  `ByteEncode12(ByteDecode12(ek_vector)) = ek_vector`.

## The erasure code

**The field.** An element of GF(2^16) is a 16-bit value whose bit `n` is the
coefficient of `x^n`. Addition is exclusive or. Multiplication is the
carry-less product of the two polynomials reduced modulo
`x^16 + x^12 + x^3 + x + 1` (`0x1100B`, [CONSTANTS.md](../CONSTANTS.md)).
Division by a nonzero `a` is multiplication by `a^(2^16 - 2)`. An integer
below 65,536 used as an element is the element with the same sixteen bits.

**Chunks.** A 32-byte chunk is 16 elements, element `j` being bytes `2j` and
`2j + 1` read big-endian. A value of `n` bytes is cut into `k = ceil(n / 32)`
chunks, `chunk_0` to `chunk_(k-1)` in order, the last padded with zero bytes.
Every value the Braid sends -- the header with its MAC (96 bytes),
`ek_vector` (1,536), `ct1` (1,408), and `ct2` with its MAC (192) -- is a whole
number of chunks, so here the padding is never used.

**Codewords.** A codeword is a 16-bit index `i`, carried as `chunk_index`
(message-format.md), and 32 bytes. For `i < k` the bytes are `chunk_i`. For
`i >= k`, element `j` of the bytes is `P_j(i)`, where `P_j` is the polynomial
of degree below `k` through the points `(t, element j of chunk_t)` for `t`
from 0 to `k - 1`:

```
P_j(x) = sum over t of   element_j(chunk_t)
                       * product over s != t of (x + s) / (t + s)
```

An encoder issues indices 0, 1, 2 and so on, one per message that carries a
codeword, and never issues an index twice. Once it has issued index 65,535 it
issues nothing more (Encoder lifetime, below).

**Decoding.** The receiver knows `n`, and so `k`, before any codeword
arrives. It keeps the first codeword it receives at each index; a later one
at an index it already holds is ignored, even when its bytes differ, and once
it holds `k` codewords every further one is ignored. With `k` codewords held
at distinct indices `x_1` to `x_k`, chunk `t` is the bytes of the codeword
held at index `t` if there is one, and otherwise element `j` of chunk `t` is

```
sum over m of   element_j(codeword at x_m)
              * product over l != m of (t + x_l) / (x_m + x_l)
```

The value is the `k` chunks in order, truncated to `n` bytes. A decoder for
zero bytes holds the empty value before any codeword arrives.

## What a receive ignores

A state acts only on a message stamped with its own epoch (in `Ct2Sampled`,
the next) and of a type it is waiting for; every other message leaves it
unchanged. Within that:

- A message of an awaited type that carries no codeword is ignored wherever
  the transition reads a codeword. That includes an `EkCt1Ack` in
  `Ct1Sampled`, which then takes neither transition (8) nor (9).
- In `EkReceivedCt1Sampled`, transition (12) reads only the type: an
  `EkCt1Ack` at the current epoch completes the encapsulation whether or not
  it carries a codeword.
- In `Ct1Acknowledged` only `EkCt1Ack` codewords are collected; an `Ek`
  message is ignored.
- In `Ct2Sampled`, transition (13) reads only the epoch: a message of any
  type stamped with the next epoch takes it.

## Failure

A MAC that does not verify moves the Braid to `Failed`. So does each of the
following, and nothing else:

- key generation failing, on the send that would take transition (1), or the
  first half of encapsulation failing, on the send that would take (7);
- decapsulation failing in transition (5), or the second half of
  encapsulation failing in (9), (11) or (12);
- a completed header with its MAC, or a completed `ct2` with its MAC, that is
  not 96 or 192 bytes respectively. A decoder sized for the value always
  yields that length, so this is a check that cannot fire;
- a completed `ek_vector` that fails validation against the authenticated
  header (The KEM split), in `Ct1Sampled` or `Ct1Acknowledged`;
- the step that would move the epoch to `u64::MAX`, which is reserved
  (session-persistence.md): completing `ct2` in `EkSentCt1Received` at epoch
  `u64::MAX - 1`, or, in `Ct2Sampled` at epoch `u64::MAX - 1`, a message
  stamped `u64::MAX`. Every other message in those states is handled or
  ignored as at any other epoch.

The KEM library fails only on inputs or buffers of the wrong length, which no
reachable state holds, so the KEM failures above are defensive.

From `Failed`, a send or a receive yields no key, reports epoch 0, and leaves
the Braid in `Failed`. `Session` puts nothing from a failed Braid on the
wire: it refuses `encrypt` and `decrypt` with `AgreementFailed` once the Braid
has failed, and when a send is what fails, it keeps the failed state and
refuses that send too. A receive's move to `Failed`, like any other
transition, is adopted only once the message carrying it has authenticated.

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
peer never replies exhausts its encoder at that point. From then on, a state
that would send a codeword from that encoder sends a message of type `None`,
stamped with its current epoch and carrying no codeword, and does not change
state. The refinement theorems in `tacenta-proofs` take a live encoder as a
precondition and `CLAIMS.md` records it.

## Sources

- The published ML-KEM Braid specification (Rolfe Schmidt), **revision 1,
  2025-02-21, last updated 2025-09-26**, pinned by SHA-256 in
  `tacenta-test-vectors/conformance-manifest.md`. It is authoritative for the
  protocol; this page defers to it wherever the two could be read to differ.
- Signal's published Double Ratchet specification, revision 4, section 5, for
  the sparse continuous key agreement interface this protocol instantiates
  ([sparse-pq-ratchet.md](sparse-pq-ratchet.md)).
- FIPS 203 for ML-KEM.
