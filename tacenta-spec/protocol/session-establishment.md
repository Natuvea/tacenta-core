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
  64 bytes of randomness `Z`, verifying under `PK`.
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
value a second identity.
`Proofs.SessionEstablishment` proves the recoverability from the fixed width and
gives the counterexample that shows it fails without it; the core pins the width
in a test.

Alice sends `IKA`, `EKA`, `CT`, identifiers naming which prekeys she used, and an
initial ciphertext encrypted under `SK` (or a key derived from it) with `AD` as
associated data. The message must be encoded unambiguously so the recipient
cannot confuse one field for another. `CT` is public, and Alice keeps it: the
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
- The XEdDSA specification, revision 1, for the prekey signatures.
- RFC 5869 (HKDF), referenced by the above for the derivation.

Both archived copies are pinned by SHA-256 alongside the other references, so
the implemented revision is fixed.
