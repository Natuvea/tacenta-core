# The ML-KEM Braid

The agreement the [sparse post-quantum ratchet](sparse-pq-ratchet.md) is
instantiated with. It produces a sequence of post-quantum shared secrets, one
per epoch, between two parties who can only exchange small messages.

This page states the protocol as this implementation builds it:
- its parameters and derivations, and the ratcheted authenticator;
- the KEM split and the erasure code;
- its messages and what they put on the wire;
- the state machine, with its thirteen transitions numbered;
- what a receive ignores, and every way into `Failed`.

It is written from the published ML-KEM Braid specification (Rolfe Schmidt,
revision 1 dated 2025-02-21, last updated 2025-09-26, pinned by SHA-256 in the
conformance manifest). That document defines:
- the sparse continuous key agreement interface (its section 1.1);
- the incremental KEM interface (section 1.2) and chunking with erasure codes
  (section 1.3);
- the parameters, messages, internal authentication, state machine,
  transitions and initialization (sections 2.2 through 2.6);
- the security considerations (section 3).

The transition numbers here are that document's. Where this page departs from
it, the page says so. The protocol can be built from this page with FIPS 203,
RFC 5869 and FIPS 180-4, and without that document. Section 3 is not
restated; the properties a caller needs are given at the end.

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
- **MAC and epochs.** HMAC-SHA256, with its full 32-byte output. Epochs are
  unsigned 64-bit integers. Wherever an epoch appears as bytes, on the wire or
  in a derivation or MAC input, it is eight bytes big-endian. The
  specification recommends all three and fixes none of them.
- **Labels.** The four derivation suffixes the specification states are used
  verbatim and recorded at tier `fact` in [CONSTANTS.md](../CONSTANTS.md).
  `PROTOCOL_INFO`, whose shape the specification gives by example and whose
  value it leaves to the implementation, is `Tacenta_MLKEM1024_SHA-256`, tier
  `ours`. Their bytes are under Parameters and derivations.
- **Message types on the wire.** The specification's message-type set minus
  `Ct1Ack`, which this implementation never produces and its decoder
  rejects. The byte
  assignment of the remaining types is ours (`AgreementType` in
  [CONSTANTS.md](../CONSTANTS.md)).
- **States.** The eleven live states of the specified machine plus a terminal
  `Failed` state (The state machine, below). Their stable numbering,
  `state_tag`, is recorded in [CONSTANTS.md](../CONSTANTS.md) and is what
  persistence writes ([session-persistence.md](session-persistence.md)).
- **Verification failure is terminal.** The specification says to abandon the
  session on a MAC failure, and raises an error when `ek_vector` fails its
  integrity check. This implementation makes that unrepresentable
  otherwise: a failed verification moves the Braid to `Failed`, and `Session`
  reports it through `agreement_failed()` until the session is re-established.
  The other ways into `Failed` are listed below under Failure.
- **Epoch mismatch.** A message stamped with an epoch other than the one a
  state expects is ignored, as the specification prescribes for an unreliable
  transport. Liveness under a peer that never sends the expected epoch is
  therefore a property of the layer above, not of the Braid.

## Parameters and derivations

**Sizes.** The KEM's values are those of The KEM split, below. `MAC_SIZE` is
32. Two values carry a MAC appended, and the erasure code carries each of the
four as a whole number of 32-byte chunks:

```
value                bytes   codewords needed
header || MacHdr     96      3
ek_vector            1,536   48
ct1                  1,408   44
ct2 || MacCt         192     6
```

**Bytes.** `ToBytes(e)` is the epoch `e` as eight bytes, big-endian.
`PROTOCOL_INFO` and the four suffixes are ASCII, with no terminator:

```
PROTOCOL_INFO            "Tacenta_MLKEM1024_SHA-256"  25 bytes
                         54 61 63 65 6e 74 61 5f 4d 4c 4b 45 4d 31 30 32
                         34 5f 53 48 41 2d 32 35 36
":SCKA Key"              3a 53 43 4b 41 20 4b 65 79                        9 bytes
":Authenticator Update"  3a 41 75 74 68 65 6e 74 69 63 61 74 6f 72 20 55
                         70 64 61 74 65                                    21 bytes
":ekheader"              3a 65 6b 68 65 61 64 65 72                        9 bytes
":ciphertext"            3a 63 69 70 68 65 72 74 65 78 74                  11 bytes
```

**The two derivations.** Each is HKDF (RFC 5869) with HMAC-SHA256. Its `info`
is `PROTOCOL_INFO`, then a suffix, then `ToBytes(e)`, joined with nothing
between them:

```
KDF_OK(K, e)       = HKDF-SHA256(salt = 32 zero bytes,
                                 IKM  = K,
                                 info = PROTOCOL_INFO || ":SCKA Key" || ToBytes(e),
                                 L    = 32)

KDF_AUTH(rk, u, e) = HKDF-SHA256(salt = rk,
                                 IKM  = u,
                                 info = PROTOCOL_INFO || ":Authenticator Update" || ToBytes(e),
                                 L    = 64)
```

**The epoch key.** `K` is the 32-byte ML-KEM shared secret an epoch's
encapsulation produces. The epoch's key is `KDF_OK(K, e)` for that epoch `e`.
It is computed as soon as `K` is, at transitions (7) and (5). `K` itself is
used for nothing else and is not kept.

**The ratcheted authenticator.** Each party holds a `root_key` and a
`mac_key`, 32 bytes each:

```
Init(e, s):     root_key = 32 zero bytes, then Update(e, s)
Update(e, u):   out      = KDF_AUTH(root_key, u, e)
                root_key = out[0..32]      -- the first 32 bytes
                mac_key  = out[32..64]     -- the last 32 bytes
MacHdr(e, hdr)  = HMAC-SHA256(mac_key, PROTOCOL_INFO || ":ekheader"   || ToBytes(e) || hdr)
MacCt(e, ct)    = HMAC-SHA256(mac_key, PROTOCOL_INFO || ":ciphertext" || ToBytes(e) || ct)
```

- **Initialisation.** Both parties run `Init(1, SK)`. `SK` is the PQXDH shared
  secret itself ([session-establishment.md](session-establishment.md)), not
  either half of the Triple Ratchet's split of it
  ([triple-ratchet.md](triple-ratchet.md), Initialisation). `Init` reads no
  `mac_key`: its `Update` sets both keys.
- **Update.** The authenticator is updated once per epoch on each side, with
  the epoch key and not `K`: at (7) by the party that encapsulates, and at (5)
  by the party that decapsulates. Nothing else updates it.
- **The header MAC.** `hdr` is the 64-byte KEM header. The MAC is appended to
  it by (1) and checked by the receive that completes the header in
  `NoHeaderReceived`.
- **The ciphertext MAC.** `ct` is `ct1 || ct2`, 1,568 bytes. The MAC is
  appended to `ct2` when the encapsulation completes, at (9), (11) or (12). It
  is checked by (5), after that transition's `Update`.
- **Verification.** A receiver recomputes the MAC and compares all 32 bytes;
  this implementation compares in constant time. Nothing is truncated. A
  mismatch moves the Braid to `Failed` (Failure).

The vectors `tacenta-test-vectors/vectors/post-quantum/braid.json` are
examples of `KDF_OK`. The vectors `auth.json` are examples of one `Update`
from a given `root_key`, output `root_key || mac_key`; its `from-zero` vector
is `Init(1, s)`. No vector pins a MAC.

**Where this reads the published document.** Its section 2.4 writes the epoch
in the two MAC inputs bare, where its section 2.2 writes `ToBytes(epoch)` in
the two derivations. Here the MAC inputs use `ToBytes` too. Its
`Authenticator.Init` gives `mac_key` no value, as here.

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

**This departs from the published document in two places.**
- **The hash input order.** The document writes the header's hash as
  `SHA3-256(ek_seed || ek_vector)`, seed first. What is computed here is FIPS
  203's `H(ek)`, whose input is `ek_vector || rho`, with `rho` as the seed: the
  same two parts in the other order, so the hashes differ. A peer that follows
  the published notation literally computes a different header, and its
  `ek_vector` fails this validation.
- **The modulus check.** The document's integrity check is the hash alone. The
  modulus check is added here: it refuses an `ek_vector` that matches the hash
  but is not a valid FIPS 203 encoding.

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

## Messages

A Braid message has three fields:
- an epoch, an unsigned 64-bit integer;
- a type;
- at most one codeword (The erasure code), a 16-bit index and 32 bytes.

```
type       what the codeword is from      also says
None       no codeword                    nothing
Hdr        header || MacHdr
Ek         ek_vector
EkCt1Ack   ek_vector                      the sender holds all of ct1
Ct1        ct1
Ct2        ct2 || MacCt
```

The published document's section 2.3 has a seventh type, `Ct1Ack`: an
acknowledgement of `ct1` with no codeword. No state here sends it. The
acknowledgement always rides on an `ek_vector` codeword, because the sender
never learns that `ek_vector` has arrived in full and so always has one to
send. The wire has no byte for it (message-format.md).

**On the wire.** Every ratchet message carries exactly one Braid message: the
one the Braid's send produced in the same `encrypt`. It fills the composite
header's last four fields (message-format.md, Ratchet message):

```
ag_epoch       = ToBytes(epoch)
ag_type        = the type's byte (AgreementType, CONSTANTS.md)
chunk_present  = 0x01 with a codeword, 0x00 without
chunk_index    = the codeword's index, 2 bytes big-endian; zero without
chunk          = the codeword's 32 bytes; zero without
```

A receive hands the Braid the message those four fields describe.

## The state machine

### States

Every live state holds the epoch being negotiated and an authenticator. Five
states belong to the party that, in the current epoch, generates the key pair
and decapsulates: it sends the header and `ek_vector`. Six belong to the party
that encapsulates: it waits for the header and sends `ct1` and `ct2`. The two
swap at the end of every epoch.

```
tag  state                  side          holds, besides epoch and authenticator
0    KeysUnsampled          key pair      nothing
1    KeysSampled            key pair      key pair, header encoder
2    HeaderSent             key pair      key pair, ct1 decoder, ek_vector encoder
3    Ct1Received            key pair      key pair, ct1, ek_vector encoder
4    EkSentCt1Received      key pair      key pair, ct1, ct2 decoder
5    NoHeaderReceived       encapsulate   header decoder
6    HeaderReceived         encapsulate   header, ek_vector decoder
7    Ct1Sampled             encapsulate   header, encapsulation state, ct1,
                                          ct1 encoder, ek_vector decoder
8    EkReceivedCt1Sampled   encapsulate   encapsulation state, ct1, ek_vector,
                                          ct1 encoder
9    Ct1Acknowledged        encapsulate   header, encapsulation state, ct1,
                                          ek_vector decoder
10   Ct2Sampled             encapsulate   ct2 encoder
11   Failed                 neither       nothing, not even an epoch
```

- The *encapsulation state* is what the first half of encapsulation keeps for
  the second (The KEM split).
- Each decoder is sized for its value: the header decoder for 96 bytes, the
  `ct1` decoder for 1,408, the `ek_vector` decoder for 1,536 and the `ct2`
  decoder for 192.
- The tag is `state_tag` ([session-persistence.md](session-persistence.md)).

### Initialisation

Both parties start at epoch 1, with an authenticator from `Init(1, SK)`
(Parameters and derivations).
- The session's initiator, which sent the initial message, starts in
  `KeysUnsampled`.
- The responder starts in `NoHeaderReceived`, with an empty header decoder.

### Sending

A send produces exactly one message, stamped with the state's epoch. The
message carries at most one codeword: the next index of the encoder the state
sends from (The erasure code, Codewords).

```
state                  type       codeword                              transition
KeysUnsampled          Hdr        index 0 of a new header encoder       (1)
KeysSampled            Hdr        next index of the header encoder
HeaderSent             Ek         next index of the ek_vector encoder
Ct1Received            EkCt1Ack   next index of the ek_vector encoder
EkSentCt1Received      None       none
NoHeaderReceived       None       none
HeaderReceived         Ct1        index 0 of a new ct1 encoder          (7)
Ct1Sampled             Ct1        next index of the ct1 encoder
EkReceivedCt1Sampled   Ct1        next index of the ct1 encoder
Ct1Acknowledged        None       none
Ct2Sampled             Ct2        next index of the ct2 encoder
```

- Only (1) and (7) change state on a send. Every other send advances its
  encoder and nothing else.
- `Ct1Received` sends from the `ek_vector` encoder that (2) started,
  continuing its indices. `EkReceivedCt1Sampled` likewise continues the `ct1`
  encoder that (7) started.
- A state whose encoder is exhausted sends `None` with no codeword and does
  not change (Encoder lifetime).
- `Failed` puts nothing on the wire (Failure).

The two sending transitions:

- **(1)**, `KeysUnsampled`:
  1. Generate a key pair (The KEM split), giving `header` (64 bytes) and
     `ek_vector`.
  2. Start an encoder over `header || MacHdr(epoch, header)`, 96 bytes.
  3. Send its codeword 0 as `Hdr`, and go to `KeysSampled`.
- **(7)**, `HeaderReceived`:
  1. Run the first half of encapsulation on the stored `header`, giving the
     encapsulation state, `ct1` and `K`.
  2. Let `key = KDF_OK(K, epoch)`, then `Update(epoch, key)`.
  3. Start an encoder over `ct1`, and send its codeword 0 as `Ct1`.
  4. Output `(epoch, key)`, and go to `Ct1Sampled`.

### Receiving

In what follows:
- "at its epoch" means the message's epoch equals the state's;
- "with a codeword" means the message carries one;
- to *collect* a codeword is to add it to the state's decoder, as The erasure
  code, Decoding, describes, and stay in the state unless a transition
  follows.

The receiving transitions:

- `KeysUnsampled` and `HeaderReceived` ignore every message.
- `KeysSampled`, on `Ct1` at its epoch with a codeword, takes **(2)**. It starts
  a `ct1` decoder holding that codeword and an encoder over `ek_vector`, and
  goes to `HeaderSent`. One codeword cannot complete `ct1`.
- `HeaderSent`, on `Ct1` at its epoch with a codeword, collects it. If the
  decoder then holds all of `ct1`, it takes **(3)** to `Ct1Received`, keeping
  `ct1` and the `ek_vector` encoder.
- `Ct1Received`, on `Ct2` at its epoch with a codeword, takes **(4)**. It starts
  a `ct2` decoder holding that codeword and goes to `EkSentCt1Received`.
- `EkSentCt1Received`, on `Ct2` at its epoch with a codeword, collects it. If
  the decoder then holds its 192 bytes, it runs the checks under Failure, and
  then takes **(5)**:
  1. Split the value into `ct2` (160 bytes) and `mac` (32).
  2. Decapsulate `ct1 || ct2`, giving `K`.
  3. Let `key = KDF_OK(K, epoch)`, then `Update(epoch, key)`.
  4. If `MacCt(epoch, ct1 || ct2)` is not `mac`, go to `Failed` instead.
  5. Otherwise output `(epoch, key)`. Go to `NoHeaderReceived` at `epoch + 1`,
     with the updated authenticator and an empty header decoder.
- `NoHeaderReceived`, on `Hdr` at its epoch with a codeword, collects it. If the
  decoder then holds its 96 bytes, it splits them into `header` (64) and
  `mac` (32).
  - If `MacHdr(epoch, header)` is not `mac`, it goes to `Failed`.
  - Otherwise it takes **(6)** to `HeaderReceived`, with `header` and an empty
    `ek_vector` decoder.
- `Ct1Sampled`, on `Ek` or `EkCt1Ack` at its epoch with a codeword, collects
  it. Then:
  - If the decoder now holds all of `ek_vector`, it validates it against
    `header` (The KEM split); failing that, it goes to `Failed`. On `EkCt1Ack`
    it takes **(9)**: complete the encapsulation. On `Ek` it takes **(10)** to
    `EkReceivedCt1Sampled`, keeping the encapsulation state, `ct1`, the `ct1`
    encoder and `ek_vector`.
  - If not, on `EkCt1Ack` it takes **(8)** to `Ct1Acknowledged`, keeping the
    decoder. On `Ek` it stays.
- `Ct1Acknowledged`, on `EkCt1Ack` at its epoch with a codeword, collects it.
  If the decoder then holds all of `ek_vector`, it validates it, going to
  `Failed` on failure. Otherwise it takes **(11)**: complete the encapsulation.
- `EkReceivedCt1Sampled`, on `EkCt1Ack` at its epoch, takes **(12)**: complete
  the encapsulation.
- `Ct2Sampled`, on a message of any type at `epoch + 1`, takes **(13)** to
  `KeysUnsampled` at `epoch + 1`, with its authenticator. The message is not
  otherwise read.

Every other message leaves the state as it was (What a receive ignores).

**Completing the encapsulation**, in (9), (11) and (12), does four things:
1. It runs the second half of encapsulation on the encapsulation state and
   `ek_vector`, giving `ct2` (160 bytes).
2. It starts an encoder over `ct2 || MacCt(epoch, ct1 || ct2)`, 192 bytes.
3. It goes to `Ct2Sampled`.
4. It does not update the authenticator, since (7) already did.

### What a send and a receive return

A send returns its message, a *sending epoch* and an optional output. A
receive returns a *receiving epoch* and an optional output. An output is an
epoch and a 32-byte key. Only (7) and (5) produce one.

- **A send's epoch** is the state's epoch less one: the latest epoch whose key
  the peer is sure to hold once it has this message. A send never changes the
  epoch. The value is 0 at epoch 1, and 0 from `Failed`.
- **A receive's epoch** is the epoch of the state the receive leaves the Braid
  in, less one. It is 0 when that state is `Failed`.

**This departs from the published document at transition (5), and ADR-0007
keeps the departure.**
- The document computes a receive's epoch before any transition, except in
  `Ct2Sampled`. A receive taking (5) there reports `epoch - 1`, which is the
  sending epoch the `ct2` message was sent with. That is the document's
  "epoch agreement" (its section 1.1).
- Here the receive taking (5) reports `epoch`: the epoch just completed, the
  same as its output's.
- On every other receive, and at (13), the two agree.
- `Session` does not use a receive's epoch (below), so nothing observable
  depends on the difference.

### When an epoch completes

Each epoch's key is output once on each side, labelled with that epoch.
1. The encapsulating party's send outputs it at (7).
2. The other party's receive outputs it later, at (5).
3. Each side updates its authenticator with the key at that transition. The
   next epoch's MACs are therefore keyed by what this epoch produced.
4. At (5) the decapsulating party moves to the next epoch, as the party that
   waits for a header. It sends `None` stamped with the new epoch.
5. The first message at that epoch to reach the encapsulating party takes
   (13). That party moves to the next epoch, as the party that will generate
   the key pair.

### What the session does with them

- **`encrypt`** runs the Braid's send before the Triple Ratchet. It hands the
  sparse ratchet the sending epoch, as the epoch whose sending chain is
  stepped, and any output, as the agreement's secret
  ([sparse-pq-ratchet.md](sparse-pq-ratchet.md), Sending).
- **`decrypt`** runs the Braid's receive first, and hands any output to the
  sparse ratchet (Receiving). The receiving epoch is not used.
- **Adoption.** A state either produces is adopted as Failure, below, and
  [triple-ratchet.md](triple-ratchet.md), Sending and receiving, describe.

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

The published document's pseudocode adds a message's codeword to a decoder
without asking whether it has one. The first rule above is this page's.

## Failure

A MAC that does not verify moves the Braid to `Failed` (The state machine,
Receiving). So does each of the following, and nothing else:

- key generation failing, on the send that would take transition (1), or the
  first half of encapsulation failing, on the send that would take (7);
- decapsulation failing in transition (5), or the second half of
  encapsulation failing in (9), (11) or (12);
- a completed header with its MAC, or a completed `ct2` with its MAC, that is
  not 96 or 192 bytes respectively. A decoder sized for the value always
  yields that length, so this is a check that cannot fire;
- a completed `ek_vector` that fails validation against the authenticated
  header (The KEM split), in `Ct1Sampled` or `Ct1Acknowledged`;
- reaching the reserved epoch `u64::MAX` (session-persistence.md), at epoch
  `u64::MAX - 1`:
  - in `EkSentCt1Received`, completing `ct2` fails, and every other message
    is handled as at any other epoch;
  - in `Ct2Sampled`, any received message fails, whatever its epoch or type,
    because that state checks the ceiling before it looks at the message.
  No honest run reaches either epoch.

In `EkSentCt1Received` the length check comes first, then the ceiling, and
both come before decapsulation.

The KEM library fails only on inputs or buffers of the wrong length, which no
reachable state holds, so the KEM failures above are defensive.

From `Failed`, a send or a receive yields no key, reports epoch 0, and leaves
the Braid in `Failed`. `Session` puts nothing from a failed Braid on the
wire: it refuses `encrypt` and `decrypt` with `AgreementFailed` once the Braid
has failed, and when a send is what fails, it keeps the failed state and
refuses that send too. A receive's move to `Failed`, like any other
transition, is adopted only once the message carrying it has authenticated.
That message is accepted and its plaintext returned; the refusals begin with
the next one.

## Properties a caller must know

**A Braid output is not a session key.** The epoch key is derived from the KEM
shared secret and the epoch alone (`KDF_OK`, Parameters and derivations). The
preshared secret seeds the ratcheted
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
  `tacenta-test-vectors/conformance-manifest.md`:
  - section 1.1 for the send and receive interface;
  - sections 2.2 to 2.4 for the parameters, derivations, messages and the
    ratcheted authenticator;
  - section 2.5 for the states and the transition numbering this page keeps;
  - section 2.6 for initialisation.

  This page is written from it and states where it departs from it. Under
  ADR-0006 this page, not that document, is what the tree implements.
- Signal's published Double Ratchet specification, revision 4, section 5, for
  the sparse continuous key agreement interface this protocol instantiates
  ([sparse-pq-ratchet.md](sparse-pq-ratchet.md)).
- FIPS 203 for ML-KEM.
- RFC 5869 for HKDF, RFC 2104 for HMAC, and FIPS 180-4 for SHA-256.
