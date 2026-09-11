# Session establishment (PQXDH)

This page specifies how two parties agree on the shared secret the message
ratchets start from. It is our own description, written from the published
specification named in Sources, and it is the reference the Lean model and the
Rust implementation are both written against.

**What consumes `SK` is the Triple Ratchet, not the Double Ratchet alone.**
`Session` expands `SK` with a key derivation into two thirty-two byte secrets
(`split_secret`; [triple-ratchet.md](triple-ratchet.md), Initialisation) and
starts one ratchet from each,
and it initialises the ML-KEM Braid's authenticator from `SK` directly
([mlkem-braid.md](mlkem-braid.md)). Nothing on this page changes as a result --
PQXDH still produces one secret and this page still specifies how -- but a
reader who took "the Double Ratchet starts from" literally would look for a
consumer that no longer exists on its own.

The setting is asynchronous: Bob is offline but has published keys to a server,
and Alice wants to send him an encrypted message and establish a shared secret
without a round trip. PQXDH combines several Diffie-Hellman computations with a
post-quantum key encapsulation, so the resulting secret is forward secret against
a classical attacker and against an attacker who records traffic now and gets a
quantum computer later. Mutual authentication still rests on the discrete log
problem in this revision.

## Scope

We implement PQXDH. X3DH, its predecessor, is described here only where PQXDH
builds on it (the four Diffie-Hellman computations), because understanding one
requires the other. Plain X3DH, whose shared secret omits the encapsulated
secret, is out of scope: we do not establish sessions with X3DH-only peers. The
exclusion is recorded in the conformance manifest.

## Parameters

An application must fix these. Ours are given in the right-hand column, and
[CONSTANTS.md](../CONSTANTS.md) carries each value's provenance.

| Name | Meaning | Ours |
|---|---|---|
| `curve` | A Montgomery curve with XEdDSA defined | curve25519 |
| `hash` | A 256 or 512-bit hash | SHA-256 |
| `info` | ASCII string identifying the application, at least 8 bytes | `Tacenta_CURVE25519_SHA-256_ML-KEM-1024`, tier `ours` |
| `pqkem` | A post-quantum KEM with IND-CCA security | ML-KEM-1024 |
| `aead` | An AEAD with IND-CPA and INT-CTXT security | AES-256-CBC with HMAC-SHA256 |
| `EncodeEC` / `DecodeEC` | Encode and decode a curve public key | type byte `0x05`, then the key: 33 bytes. Tier `nominated` |
| `EncodeKEM` / `DecodeKEM` | Encode and decode a KEM public key | type byte `0x08`, then the key: 1,569 bytes. Tier `nominated` |

The ranges of the encoding functions must be pairwise disjoint, so a byte
sequence can never be read as both a curve key and a KEM key. The recommended
shape for each encoder is a single implementer-defined byte identifying the
curve or the KEM, followed by that primitive's own encoding; a decoder that does
not recognise the leading byte fails.

## Notation

- `X || Y` is concatenation.
- `DH(PK1, PK2)` is the X25519 shared secret between the two key pairs.
- A `DH` output is *non-contributory* when all 32 of its bytes are zero. This
  is the X25519 library's definition (`was_contributory` in `x25519-dalek`),
  adopted here as the rule. A non-contributory output is refused wherever one
  is computed.
- `Sig(PK, M, Z)` is an XEdDSA signature over `M` by `PK`'s private key, using
  64 bytes of randomness `Z`, verifying under `PK`. How it is made and which
  signatures verify are stated in identities-and-devices.md (Signing;
  Verifying a signature).
- `KDF(KM)` is 32 bytes of HKDF output using `hash`, with input keying material
  `F || KM`, an all-zero salt the length of the hash output, and an `info` string
  described below. `F` is 32 bytes of `0xFF` for curve25519. `F` exists for
  domain separation: it ensures the first bytes of the input keying material are
  never a valid encoding of a scalar or a curve point, which is what keeps this
  KDF separate from XEdDSA's use of the same identity key.
- `(CT, SS) = PQKEM-ENC(PK)` encapsulates a fresh shared secret `SS` to `PK`,
  producing ciphertext `CT`. `PQKEM-DEC(PK, CT)` recovers `SS` with the private
  key.

The KDF's `info` is the `info` parameter from the table above, used
verbatim: `Tacenta_CURVE25519_SHA-256_ML-KEM-1024` (`SK_INFO` in the session
crate, registered in `tacenta-core/LABELS.md`). The specification recommends
the string name the application, the curve, the hash, and the KEM, which is
how ours is composed, so a secret derived under one parameter set cannot
collide with one derived under another; but the composition happened when the
constant was chosen, and the code passes the fixed string rather than
assembling it.

## Keys

Curve keys: Alice's identity `IKA` and ephemeral `EKA`; Bob's identity `IKB`,
signed prekey `SPKB`, and one-time prekeys `OPKB1, OPKB2, ...`.

KEM keys: Bob's signed last-resort prekey `PQSPKB`, and his signed one-time
prekeys `PQOPKB1, PQOPKB2, ...`. "Last-resort" means it is used only when the
one-time KEM prekeys are exhausted, which happens when bundles are fetched
faster than Bob replenishes.

Every prekey carries an identifier (`IdEC` for curve keys, `IdKEM` for KEM keys)
that uniquely names it on Bob's device, so Bob can find the right private key
when the message arrives. Note the asymmetry: the curve one-time prekeys are not
individually signed, while every KEM prekey is.

## Publishing keys

Bob uploads his identity key once, then publishes and periodically replaces:

- the signed curve prekey with its identifier, and `Sig(IKB, EncodeEC(SPKB), Z)`
- the signed last-resort KEM prekey with its identifier, and
  `Sig(IKB, EncodeKEM(PQSPKB), Z)`
- a set of one-time curve prekeys with identifiers
- a set of one-time KEM prekeys with identifiers, each with its own signature
  under `IKB`

Each signature uses fresh randomness. After rotating the signed prekeys Bob may
keep the previous private keys briefly to decrypt messages already in flight,
then must delete them for forward secrecy. One-time prekey private keys are
deleted as they are used.

## Sending the initial message

Alice fetches a prekey bundle: `IKB`, the signed curve prekey and its signature,
one KEM prekey and its signature (a one-time KEM prekey if any remain, otherwise
the last-resort one, called `PQPKB` either way), and optionally a one-time curve
prekey. The server hands out and deletes one-time keys, preferring one-time KEM
prekeys over the last-resort key.

Alice verifies every signature in the bundle and aborts if any fails. This is not
optional: without the prekey signature a malicious server could serve forged
prekeys and later compromise `IKB` to recover the secret, which would defeat
forward secrecy.

She also refuses a bundle before encapsulating when its identity key is not the
one she set out to reach (when she names one), or when its one-time curve
prekey and that prekey's identifier disagree about whether one is present
(message-format.md). Both sides refuse a Diffie-Hellman output that is not
contributory, which a low-order public key produces.

She then generates `EKA`, encapsulates `(CT, SS) = PQKEM-ENC(PQPKB)`, and
computes:

```
DH1 = DH(IKA, SPKB)
DH2 = DH(EKA, IKB)
DH3 = DH(EKA, SPKB)
DH4 = DH(EKA, OPKB)        # only when the bundle carried a one-time curve prekey

SK  = KDF(DH1 || DH2 || DH3 || SS)          # without a one-time curve prekey
SK  = KDF(DH1 || DH2 || DH3 || DH4 || SS)   # with one
```

`DH1` and `DH2` cross the identity keys with the other side's ephemeral or
prekey, which is what provides mutual authentication. `DH3` and `DH4` involve
only ephemeral and prekey material, which is what provides forward secrecy. `SS`
adds forward secrecy against a future quantum attacker.

Alice then deletes her ephemeral private key, the DH outputs, and `SS`.

The associated data binds both identities:

```
AD = EncodeEC(IKA) || EncodeEC(IKB)
```

If the chosen KEM does not already bind the public key into the ciphertext,
`EncodeKEM(PQPKB)` must be appended to `AD` as well. This implementation does
not append it. That relies on ML-KEM-1024 binding its encapsulation key into
the shared secret, and this page records the reliance as an open question
rather than settling it.

**`EncodeEC` must be fixed-width, and this is where that requirement lives.**
`AD` is a bare concatenation with no separator and no length prefix, so the two
identities are recoverable from it only if the first one's width is known in
advance. With variable-width encodings the same `AD` can be produced by two
different pairs of identities, and a binding that two different pairs satisfy
binds neither. Ours is fixed at thirty-three bytes, a curve byte and a
thirty-two byte key, which is what makes the concatenation safe.

This is a requirement on the encoder, not on `AD`, and it is stated here because
nothing in the shape of `AD` reveals that it depends on one.

**`DecodeEC` accepts exactly one encoding of each key.** The thirty-two key
bytes are the little-endian u-coordinate of RFC 7748, and X25519 ignores the top
bit of the last byte and reduces modulo p = 2^255 - 19. So, read loosely, several
byte strings name the same key. `DecodeEC` refuses every one but the canonical
encoding: a key whose top bit (bit 255) is set, and a key whose value is at least
p. An honest key generator never produces either, so no honest key is refused.
The requirement is message-format.md's single-encoding principle applied to curve
keys. It matters wherever a value is identified by its bytes rather than by the
key they name: a second spelling of the same key would otherwise give the same
value a second identity. The curve keys a prekey bundle and a ratchet message
carry raw, without the curve byte, are held to the same rule by their decoders
(message-format.md, Curve public keys).
`Proofs.SessionEstablishment` proves the recoverability from the fixed width and
gives the counterexample that shows it fails without it; the core pins the width
in a test.

Alice sends `IKA`, `EKA`, `CT`, identifiers naming which prekeys she used, and an
initial ciphertext. The message must be encoded unambiguously so the recipient
cannot confuse one field for another.

The initial ciphertext is the session's first ratchet message. Nothing is
encrypted under `SK` itself. The key comes from `SK` by this path:

1. `SK` is split into two 32-byte halves (triple-ratchet.md, Initialisation).
2. The first half is the Double Ratchet's `SK`. As the party that sends first,
   Alice generates a ratchet key pair `DHs` and derives
   `(RK, CKs) = KDF_RK(first half, DH(DHs, SPKB))` (ratchet.md,
   Initialisation). `KDF_CK(CKs)` gives the classical message key.
3. The second half initialises the sparse ratchet in direction `A2b`
   (sparse-pq-ratchet.md, Initialisation), and its first send gives the
   post-quantum message key.
4. The two message keys are combined into 32 bytes (triple-ratchet.md, What
   the combination must be).
5. The message-key expansion turns those 32 bytes into `enc_key`, `mac_key` and
   `iv` (ratchet.md, Derivations).
6. The AEAD encrypts under them (message-format.md, Authenticated encryption),
   with `CONCAT(AD, composite header)` as associated data (message-format.md,
   Associated data). `AD` is the value above.

The ML-KEM Braid's authenticator is also initialised from `SK` (mlkem-braid.md),
but it keys no encryption. `CT` is public, and Alice keeps it: the
session sends the initial message's fields again with every message until one
from Bob decrypts, and only then drops them (session-persistence.md,
`pending_initial`).

## Receiving the initial message

Bob reads `IKA` and `EKA`, uses the identifiers to load the matching private
keys, recovers `SS = PQKEM-DEC(PQPKB, CT)`, repeats the same DH and KDF
computations, and deletes the DH outputs and `SS`. He rebuilds `AD` and decrypts.
If decryption fails he aborts and deletes `SK`. On success he deletes `CT` and
any one-time prekey private keys that were used.

An initial message can also arrive on a session that already exists, since
Alice repeats it until Bob answers. It does not establish again. The session
accepts it only if it is a responder's session and the message's `ephemeral`
field equals, byte for byte, the `ephemeral` field carried by the initial
message that established the session (`established_ephemeral`,
session-persistence.md); no other field is compared. It then decrypts the
ratchet message inside. Otherwise, and always on an initiator's session, it
refuses the message (`NotARepeatedInitial`).

## Replay, and why the ratchet must follow

If the bundle carried no one-time curve prekey, Alice's initial message can be
replayed to Bob, and he will derive the same `SK` in different runs. Any protocol
built on PQXDH must therefore randomise the encryption key before Bob sends
anything under it. The Double Ratchet does exactly this: Bob's first
Diffie-Hellman ratchet step folds fresh material into the root key. Using `SK`
directly to encrypt Bob's replies would risk catastrophic key reuse.

That reasoning is about **key reuse**, and it says nothing about whether the
replay is accepted at all. The two are separate: a one-time KEM prekey is
deleted on use and so refuses its own replay, but the last-resort key is
reusable by design, and without a further defence a captured initial message
naming it -- with no one-time curve prekey, which is the steady state once
Bob's one-time pools are exhausted -- would be accepted on every delivery, each
time handing Bob's application Alice's first plaintext again as the opening
message of an apparently fresh session. Nothing leaks, but the message is
delivered twice.

Bob therefore keeps a **record of last-resort handshakes he has already
accepted** -- a fingerprint over `IKA`, `EKA`, `CT`, the one-time curve
prekey identifier and the KEM prekey identifier, the fields that vary per handshake among those that determine
`SK` (the signed prekey identifier also determines `SK`, but is bound by `SK`
itself and omitted), tagged with the last-resort KEM key the handshake was
made against -- and refuses a repeat. The record is
bounded at 1024 entries **per key**: the current last-resort key and the one
the last rotation retired each have a budget of their own, so the record holds
at most two of them. It fails closed rather than evicting: a new last-resort
handshake naming a key whose budget is spent is refused
(`LastResortRecordFull`) and nothing changes, so nobody can push a victim's
fingerprint out by completing handshakes of their own. A key's entries are
dropped when a rotation wipes the key.

Because each key is counted separately, **one rotation is enough to relieve a
spent budget**: the key `rotate_kem` opens starts empty and is the key every
bundle handed out afterwards names, so the next handshake to arrive is counted
against a clean budget, while the retired key keeps its entries and goes on
refusing their replays for as long as it can still decrypt. The relief is
brief against a peer who is filling the record deliberately -- they fetch the
new bundle too, and can spend a fresh budget in a fraction of a second -- so
the
durable defences remain a directory that rate-limits bundle fetches and
one-time KEM prekeys kept stocked. This is hardening beyond what the published
specification asks for, not a claim about it; `key-deletion.md` states what a
spent budget costs, why rotation buys a window rather than a reset, and which
accessor reports the room left.

### The fingerprint

A handshake is on the last-resort path when its `kem_prekey_id` names Bob's
current last-resort KEM prekey or the one the last rotation retired. Its
fingerprint is 32 bytes: HMAC-SHA256, keyed with a fixed label, over the
handshake fields of the initial message (message-format.md, Initial message).

```
input       = u32(33)                  || identity         -- EncodeEC(IKA)
           || u32(33)                  || ephemeral        -- EncodeEC(EKA)
           || u32(len(kem_ciphertext)) || kem_ciphertext   -- CT
           || one_time_prekey_id (4)
           || kem_prekey_id (4)
fingerprint = HMAC-SHA256(key = LAST_RESORT_HANDSHAKE_LABEL, data = input)
```

The input is built as follows:

- **Integers.** `u32(n)` and both identifiers are 4 bytes, big-endian.
- **Fields.** Each field is the bytes the initial message carries, in the
  order shown. `identity` and `ephemeral` keep their curve byte and are 33
  bytes each. `kem_ciphertext` is prefixed with its own length, the value of
  the message's `kem_ciphertext_len`. `one_time_prekey_id` is written as
  carried: `0` when no one-time curve prekey was used.
- **The key.** `LAST_RESORT_HANDSHAKE_LABEL` is the 32 ASCII bytes
  `tacenta last-resort handshake v1`, with no terminator (CONSTANTS.md). It is
  HMAC's key and is not secret: nothing in the fingerprint is. HMAC is used as
  a keyed hash, so that a fingerprint cannot equal any other digest computed
  over overlapping bytes.
- **What is left out.** `signed_prekey_id` and the ratchet message are not
  inputs. The ratchet message is authenticated under keys derived from `SK`,
  so nobody who cannot already derive `SK` can vary it. Leaving it out also
  means that re-framing a captured message does not give it a new
  fingerprint.

Bob computes the fingerprint before he decapsulates. He refuses the message
(`ReplayedLastResort`) if any entry in the record holds that fingerprint,
whatever key the entry is tagged with. The tag decides only which budget an
entry counts against and which rotation drops it. Bob adds the fingerprint,
tagged with `kem_prekey_id`, only once the initial ciphertext has
authenticated.

**The curve-key inputs are the canonical encodings.** A handshake is accepted
only if `DecodeEC` accepts both `identity` and `ephemeral` (Sending the initial
message), and `DecodeEC` accepts one encoding of each key. So every fingerprint
in the record is over the encodings `DecodeEC` accepted. Suppose a captured
message's `identity` or `ephemeral` is spelled another way, with bit 255 set or
with p added to its value. That message is refused and never recorded, rather
than fingerprinted afresh and accepted as a handshake Bob has not seen.

`CT` and the identifiers need no such rule:

- Decapsulation re-encrypts and compares the result with the ciphertext byte
  for byte (FIPS 203, Algorithm 18). Any other ciphertext yields the
  implicit-rejection secret, and so does not authenticate.
- The identifiers are fixed-width integers, with one spelling each.

## Primitives, and what is left to them

This page composes X25519, ML-KEM-1024, HKDF-SHA256 and XEdDSA. XEdDSA is
specified in identities-and-devices.md, and HKDF is RFC 5869's, as Notation
says. For X25519 and ML-KEM-1024, this section states what the protocol
requires and what it leaves to the standard. Whatever a standard leaves open
is left to the library that implements it. `tacenta-core` takes X25519 from
`x25519-dalek` and ML-KEM-1024 from `libcrux-ml-kem`, and nothing below
depends on that choice.

### X25519 (RFC 7748)

- **Private keys.** A curve private key is 32 bytes. It is generated as 32
  random bytes and stored as generated, unclamped. Each use clamps it as RFC
  7748, section 5, `decodeScalar25519`, does: it clears the low three bits of
  byte 0, clears the top bit of byte 31, and sets the bit below that. This
  holds for the identity key (identities-and-devices.md), the signed and
  one-time prekeys, the ephemeral key and every ratchet key pair.
- **Public keys.** A public key is `X25519(k, 9)`: 32 bytes, the little-endian
  u-coordinate.
- **Agreement.** `DH(PK1, PK2)` is `X25519(k1, u2)` (RFC 7748, section 5), 32
  bytes. A non-contributory output is refused (Notation). RFC 7748, section
  6.1, describes that check and leaves it to the protocol.
- **Decoding a peer's key is not left to X25519.** RFC 7748, section 5, has
  X25519 ignore bit 255 of a u-coordinate and accept a value at or above p,
  reducing it. No key a peer sends reaches X25519 in either form: every curve
  public key is refused unless it is the canonical encoding, a value below p
  with bit 255 clear, before it is used.
  - An initial message's `identity` and `ephemeral`, in `EncodeEC` form, are
    checked by `DecodeEC` (Sending the initial message).
  - A prekey bundle's `identity_key`, `signed_prekey` and `one_time_prekey`,
    and a composite header's `dh`, are checked by the decoders that read them
    (message-format.md, Curve public keys). A bundle with a re-spelled key, or
    a ratchet message with a re-spelled `dh`, does not decode.
  - The bundle's identity key meets the check a second time when its
    signatures are verified (identities-and-devices.md, Verifying a signature,
    step 1), which applies to whatever key a signature is verified under.

  So the masking and the reduction never apply to a peer's key, and the byte
  string that identifies a key, in a signature, the associated data, a
  fingerprint or the skipped-key store, is the only one that names it. An
  honest key generator never produces a refused form.
- **Left to the library:** the Montgomery ladder, the field arithmetic, and
  computing in time independent of the private key. Any implementation that
  follows RFC 7748, section 5, computes the same bytes from the same inputs.

### ML-KEM-1024 (FIPS 203)

- **Key generation.** A KEM prekey pair is generated from 64 random bytes
  `d || z` by `ML-KEM.KeyGen_internal(d, z)` (FIPS 203, Algorithm 16). The
  result is a 1,568-byte encapsulation key `ek` and a 3,168-byte decapsulation
  key `dk`. The prekey store persists both in FIPS 203's layout
  (session-persistence.md, Prekey store).
- **Validating the encapsulation key.** Before encapsulating, `PQKEM-ENC(PK)`
  applies FIPS 203 section 7.2's input checks to the bundle's KEM prekey:
  - its length is 1,568 bytes, which the bundle decoder already requires
    (message-format.md, Prekey bundle);
  - `ByteEncode12(ByteDecode12(ek[0:1536]))` equals `ek[0:1536]`.

  Alice refuses a bundle whose key fails either check. She has then computed no
  agreement and sent nothing.
- **Encapsulation** draws 32 random bytes `m` and runs
  `ML-KEM.Encaps_internal(ek, m)` (Algorithm 17). That is `ML-KEM.Encaps`, with
  `m` taken from the caller's random source. It produces a 1,568-byte `CT` and
  a 32-byte `SS`.
- **Decapsulation** refuses a `CT` of any length other than 1,568 bytes
  (message-format.md, Initial message), then runs
  `ML-KEM.Decaps_internal(dk, CT)` (Algorithm 18).
  - **Implicit rejection is kept.** A ciphertext that does not re-encrypt to
    itself yields the pseudorandom `J(z || CT)`, not an error, so `PQKEM-DEC`
    never fails on a ciphertext of the right length. A wrong `CT` surfaces as
    the initial ciphertext failing to authenticate, which is where PQXDH
    expects a failed handshake to surface.
  - **The hash check is made at load.** Section 7.3's hash check on `dk` is
    made when a stored key pair is read (session-persistence.md, Prekey store),
    not at each decapsulation. A pair the store generated itself is valid by
    construction.
- **The Braid.** The ML-KEM Braid uses the incremental form of the same
  algorithms, with the same randomness sizes (mlkem-braid.md, The KEM split).
- **Left to the library:** the algorithms' internals (sampling, the NTT,
  compression, SHA3-256, SHA3-512 and SHAKE) and constant-time execution. Any
  FIPS 203 implementation computes the same `ek`, `dk`, `CT` and `SS` from the
  same random bytes. The one thing another implementation cannot take from
  FIPS 203 is the Braid's persisted key pair and encapsulation state
  (session-persistence.md, Braid).

## Byte-level conventions

The published specification deliberately leaves the application `info` string,
the `EncodeEC` and `EncodeKEM` leading bytes, and the initial-message encoding to
the implementer. Those are exactly the values a specific peer must agree on for
wire interoperability, and all of them are recorded in
[CONSTANTS.md](../CONSTANTS.md).

The two encoding type bytes were determined by black-box observation of a pinned
build under the interoperability boundary, never by reading another
implementation's source, and are reproduced by our own parser against bundles
observed under that boundary. The `info` string is the other case: it is a
free choice at tier `ours`, because message-layer interoperability is not
attempted. The layer
that interoperates is the bundle, and every constant it needs travels on the
wire. [CONSTANTS.md](../CONSTANTS.md) is the record of each value's
provenance; the conformance manifest tracks vector coverage.

## Security properties

Mutual authentication comes from `DH1` and `DH2` and rests on the discrete log
problem, not on the KEM. Forward secrecy comes from `DH3`, `DH4`, and `SS`, and
from deleting ephemeral and one-time private keys once used. Resistance to
harvest-now-decrypt-later comes from `SS`. Deniability is retained: neither party
gets a publishable proof of the conversation. The security-properties pages
that would state these with their assumptions are scaffolds apart from
post-compromise security; until they are written, `tacenta-proofs/CLAIMS.md`
records what is established about session establishment and
`tacenta-proofs/LIMITATIONS.md` what is not.

## Sources

- Signal's published PQXDH specification (Ehren Kret and Rolfe Schmidt),
  **revision 3, 2023-05-24, last updated 2024-01-23**. It defines the
  parameters, the notation, the key set, the publishing, sending, and receiving
  procedures, and the security considerations.
- Signal's published X3DH specification (Moxie Marlinspike; Trevor Perrin,
  editor), **revision 1, 2016-11-04**, for the four Diffie-Hellman computations
  PQXDH extends and the replay discussion.
- The XEdDSA specification, revision 1, 2016-10-20, for the prekey signatures
  (identities-and-devices.md).
- RFC 5869 (HKDF), referenced by the above for the derivation.
- RFC 7748, sections 5 and 6.1, for X25519: scalar clamping, u-coordinate
  decoding, and the all-zero output check.
- FIPS 203 (ML-KEM), Algorithms 16 to 18 and sections 7.2 and 7.3, for key
  generation, encapsulation, decapsulation with implicit rejection, and the
  input checks.

Both archived copies are pinned by SHA-256 alongside the other references, so
the implemented revision is fixed.
