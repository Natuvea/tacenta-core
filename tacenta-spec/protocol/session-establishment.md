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
forward secrecy. She verifies them only under an `IKB` that is an identity key,
which she checks before either signature (below).

The KEM prekey's signature is over the type byte `0x08` followed by the
key's bytes as the bundle holds them (message-format.md, Prekey bundle: a
verifier re-tags the key it reads). For a key of 1,568 bytes, which is
every key the bundle decoder returns, that is `EncodeKEM` of the key. She
verifies both signatures before the KEM prekey's input checks (Primitives,
ML-KEM-1024), which are part of encapsulating
(security-properties/authentication.md, REQ-AUTH-01). So a bundle that
reaches her without the bundle decoder, with a KEM prekey that is not 1,568
bytes, is refused as an authentication failure when that signature does not
verify, and otherwise by the input checks.

She also refuses a bundle before encapsulating when its one-time curve prekey
and that prekey's identifier disagree about whether one is present
(message-format.md), or when its identity key, signed prekey or one-time curve
prekey is not the canonical encoding of a curve public key (message-format.md,
Curve public keys). A bundle the bundle decoder returned never holds such a
key. The check is for a bundle that reaches her some other way, and it keeps
every curve public key her session stores canonical (session-persistence.md,
Session, Semantic rules). Both sides refuse a Diffie-Hellman output that is not
contributory, which a low-order public key produces.

She checks the bundle's identity key against her expectation (Records,
expectations and attribution, below) after the bundle's presence and
canonical-key checks, and before the identity-key rule, the signature checks,
the KEM prekey's input checks and anything that draws randomness or computes
an agreement.

A bundle whose canonical `IKB` is not an identity key (identities-and-devices.md,
Identity keys) is refused as an invalid identity key. She makes that check after
the presence and canonical checks above and the check against her expectation,
and before she verifies either signature, draws a random value or encapsulates,
so nothing is spent on the bundle and nothing changes. The check against her
expectation applies the same rule to the key first (Records, expectations and
attribution, Classification), so such a bundle is refused as an invalid
identity key either way, unless her expectation is itself malformed. The other
keys of the bundle are not held to it: `SPKB` and a one-time curve prekey need
the canonical encoding and a contributory result, and no more.

Each of her refusals of a bundle is reported as its own kind, since this page
fixes an order among them and an order can be seen only between refusals that
are told apart (error-handling.md). Beside the invalid identity key and the
refusals of her expectation (Records, expectations and attribution), they are:
- an *inconsistent bundle*: the one-time curve prekey and its identifier
  disagree about presence (message-format.md, Prekey bundle);
- a *non-canonical key*: her own canonical-key check refuses a key. The bundle
  decoder refuses the same key as a decode failure, so her check meets one only
  in a bundle that did not come from the decoder;
- an *authentication failure*: a prekey signature does not verify;
- a *KEM input* refusal: the KEM prekey fails the input checks (Primitives,
  ML-KEM-1024);
- a *non-contributory* agreement (Notation).

No order is fixed between the first two. What an implementation calls them is
its own.

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
An identity key is held to a stricter rule than this one
(identities-and-devices.md, Identity keys), which no honest identity key fails
either. The requirement is message-format.md's single-encoding principle
applied to curve keys. It matters wherever a value is identified by its bytes rather than by the
key they name: a second spelling of the same key would otherwise give the same
value a second identity. The initial-message decoder applies the same rule to
`identity` and `ephemeral` before anything reads them, and refuses a re-spelled
one as a decode failure (message-format.md, Initial message), so `DecodeEC`
never meets a key in either field that it would refuse. The curve keys a
prekey bundle and a ratchet message carry raw, without the curve byte, are held
to the same rule by their decoders (message-format.md, Curve public keys).
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

Bob refuses the message as an invalid identity key when `IKA` is not an identity
key (identities-and-devices.md, Identity keys). He makes that check once he has
found the signed prekey and the KEM prekey the message names, and before he
looks up a one-time prekey, decapsulates, or uses any private key on the
message, so an unknown one-time identifier or a ciphertext of the wrong length
behind such an `IKA` is still refused for the identity. The refusal changes
nothing.

The prekey store is read-only until the ratchet message inside the initial
message has authenticated. Every refusal before or during that authentication
leaves the whole store exactly as it was. On success the only store change is
the one this page requires: remove the one-time curve prekey the message names,
when it names one; remove the one-time KEM prekey it names; and, on the
last-resort path in place of the KEM removal, append the accepted handshake's
replay identity. A last-resort handshake that also named a one-time curve
prekey therefore removes that prekey and appends the replay identity. No other
entry or store field changes during establishment.

An initial message can also arrive on a session that already exists, since
Alice repeats it until Bob answers. It does not establish again. It must first
decode, so a message whose `identity` or `ephemeral` is re-spelled is refused
as a decode failure (message-format.md, Initial message). The session then
accepts it only if it is a responder's session and both of these hold:

- the message's `ephemeral` field is in the same X25519 agreement class as the
  `ephemeral` field carried by the initial message that established the
  session (`established_ephemeral`, session-persistence.md). The class is
  taken under the session's current ratchet private key (`ratchet_private`,
  session-persistence.md): X25519 of that key with each of the two ephemerals
  must give an output that is contributory, and the two outputs must be equal.
  The signed-prekey secret is not the key: the persisted session does not hold
  it, and the prekey store drops it after the rotation that retires it;
- the message's `identity` field equals, byte for byte, `EncodeEC` of the
  peer's identity key the session holds (`peer_identity_public`,
  session-persistence.md), which is `IKA` as the establishing message carried
  it.

It then decrypts the ratchet message inside. Otherwise, and always on an
initiator's session, it refuses the message (`NotARepeatedInitial`); that includes
a message whose `identity` is not an identity key, since it does not equal the
peer's identity key the session holds. The
message's two fields are canonical encodings, since it decoded. So are
`established_ephemeral` and `peer_identity_public`, in every session
establishment builds and in every session a reader accepts
(session-persistence.md, Session, Semantic rules). Canonical encodings are
unique as bytes, but torsion-equivalent X25519 points can have distinct
canonical encodings with the same agreement. The repeat check therefore uses
the agreement class for `ephemeral` and byte equality for `identity`. Byte
equality is enough for `identity`, because the session holds only an identity
key, and an identity key has one canonical spelling (identities-and-devices.md,
Identity keys).

The other fields, `kem_ciphertext` and the three identifiers, are not
compared: the session keeps none of them, and keeping them would change its
persisted format. Ignoring them is safe, because none of them reaches what the
session does with the message:

- the ratchet message inside must authenticate under the session's own keys,
  which no field of the wrapper changes;
- its associated data comes from the session's state, `AD` as established and
  the ratchet message's own header, and not from the wrapper;
- the ratchet refuses a message it has already accepted, so a wrapper around a
  message already read yields nothing.

So a repeat whose `kem_ciphertext` or identifiers differ from the establishing
message's, around a ratchet message the session has not read, yields that
message's plaintext once, as the unaltered repeat would, and changes nothing
else.

**A refused initial message changes nothing.** Neither refusal, the decode
failure or `NotARepeatedInitial`, changes the session. The session does not
establish a new session from the message, and does not replace itself with
one. What happens next is the recipient's decision, not the session's:

- **Establishing afresh.** The recipient can establish a new session from the
  message as on first receipt, above. The message is then taken on its own:
  the prekeys it names must still be held, the one-time prekeys it used are
  deleted once it authenticates, and on the last-resort path its replay identity
  is recorded (Replay, below). `tacenta-core` provides this as
  `establish_responder`, which takes the party's identity, its prekey store
  and the message, and returns a new session and the first plaintext.
- **No relation between the sessions.** `tacenta-core` keeps no record of the
  sessions a party holds. It does not relate the new session to the one that
  refused the message, and does not change that one: both go on working, each
  with its own peer. Keeping one, the other or both, or dropping the message,
  is left to the application.
- **A repeat does not establish twice.** Against the store its establishment
  left, a repeat of a message that already established a session does not
  establish a second one. The one-time KEM prekey it named has been deleted,
  or, on the last-resort path, its replay identity is in the record.

For the two cases message-format.md names (Message type), and for
simultaneous initiation, the specification requires the refusal, and after it
only the attribution rules of Records, expectations and attribution:

- **A session reset, or a changed identity.** A peer that starts a new session
  with a party that still holds one sends an initial message with a new
  `ephemeral`, and, after a changed identity, a new `identity`. The existing
  session refuses it (`NotARepeatedInitial`). A session established from it
  holds the identity key the message carried, which `tacenta-core` reports as
  `Session::peer_identity`. The session is attributed by a lookup (Records,
  expectations and attribution). It replaces a contact's session only if it
  is that contact's. Whether it then replaces the old one is the
  application's decision.
- **Simultaneous initiation.** Two parties that each establish a session from
  the other's bundle, before either receives the other's initial message, both
  hold an initiator's session. Each refuses the other's initial message
  (`NotARepeatedInitial`). If each then establishes a responder's session from
  the message it refused, each holds two sessions with the other, and they
  pair across: one party's initiator's session with the other's responder's
  session, and the other way round. A message sent on one session is read only
  on the session it is paired with, and the recipient's other session refuses
  it. Neither the specification nor `tacenta-core` chooses between the two
  pairs. Settling on one is left to the application.

## Records, expectations and attribution

Which identity key belongs to which contact is a party's own knowledge,
kept in records it holds (threat-model/assumptions.md, ASM-14). This section
fixes how a key is classified against those records, when a session belongs
to a contact, and what an initiator expects. It adds no state to a session
or a prekey store.

**Records.** For each contact, a party's record is two finite sets of
32-byte keys, each the canonical encoding of a curve public key
(message-format.md, Curve public keys):
- *current*, the keys it accepts for the contact;
- *retired*, keys it no longer accepts for the contact, such as a key the
  contact replaced or a lost device's key.

A party *holds a record* for a contact when either set is non-empty. A
contact whose two sets are both empty is one it holds no record for.

A list given for a set denotes the set of its members, and duplicates are
ignored. How keys enter and leave a record is the party's act (exclusions.md,
EX-09). An inventory statement is not an authority over either set
(identities-and-devices.md, Hosted device-inventory statements). A key in
both sets is *retired*. To accept it again, the party removes it from
*retired*. This specification fixes no bound on the sets.

A member is held to the canonical encoding only, not to the identity-key rule
(identities-and-devices.md, Identity keys): a canonical member that is not an
identity key is not malformed, and it matches no presented key, since a
presented key must be an identity key.

**Classification.** A presented key `k` is classified against one record.
Before anything else, `k` must be an identity key:
- if `k` is not the canonical encoding of a curve public key
  (message-format.md, Curve public keys), the classification refuses it as
  `DecodeEC` refuses such a key (a decode failure);
- if `k` is canonical but not an identity key, the classification refuses it
  as an invalid identity key (identities-and-devices.md, Identity keys).

It then checks every member of both sets. If any of them is not a canonical
encoding, it refuses the classification as a malformed record
(`MalformedRecord`), even if `k` matches another member. That refusal reports
the party's own record, never a peer's bytes. Otherwise `k` is:
- *retired*, if it is in the retired set;
- otherwise *same*, if it is in the current set;
- otherwise *new*.

Membership is equality of the 32 bytes. An identity key has one canonical
spelling (identities-and-devices.md, Identity keys), so two equal identity
keys are equal bytes.

An implementation provides this classification, under any name.

**Lookup.** A key is looked up by classifying it against every record the
party holds. A key the classification refuses as a decode failure or as an
invalid identity key refuses the lookup in the same way, whether or not the
party holds any record, and the lookup reports no record. A record whose
classification is refused as a malformed record is skipped: it attributes
nothing, and it is reported. The others decide:
- *same* for exactly one contact: the key is that contact's;
- *same* for more than one contact: the key is *ambiguous*, and is no
  contact's;
- *same* for none and *retired* for one or more: the key is a *retired key*
  of those contacts, and is no contact's;
- *same* for none and *retired* for none: the key is *unattributed*.

Wherever a lookup finds the key *retired* for a contact, that is reported
alongside its result. An implementation provides this lookup, under any
name.

A lookup's result is three things:
- the attribution: the key is a contact's (and which contact), ambiguous, a
  retired key, or unattributed;
- the contacts the key is *retired* for, which for a retired key are the
  contacts it is a retired key of;
- the records skipped as malformed.

The two lists are sets: their order is not part of the result. A lookup may
also say which contacts an ambiguous key is *same* for. That is not part of
the result, and nothing on this page depends on it.

The classification and the lookup are required of an implementation, unlike
its error types (error-handling.md), because two implementations must reach
the same attribution from the same records. Their results are fixed here;
their names and signatures are not.

**Attribution.** A session is a contact's only when a lookup of its peer
identity key finds it that contact's. This specification fixes only whether
a session is a contact's now, against the records as they stand. How an
application shows a plaintext, including one it has already shown, is the
application's (exclusions.md, EX-09), except that it shows a plaintext as a
contact's only while a lookup finds its session that contact's (ASM-14).
- **The records as they stand.** Attribution is decided against the records
  as they stand whenever a plaintext is shown or the session is used. This
  includes plaintexts already shown:
  - moving a key to *retired* withdraws attribution from every session under
    it, past plaintexts included, even after an ordinary key change;
  - recording a key attributes that session's earlier plaintexts, including
    any received before a comparison.

  No session is ended by this specification.
- **Labels.** A sender label, handle, address or anything else a bundle, a
  message or the transport supplies never selects the record a session is
  classified against, and never chooses among contacts for an ambiguous key.
  Recording a key under a contact is the party's own choice (EX-09).

A session whose key the lookup finds ambiguous, a retired key (*same* for
no contact), or unattributed is no contact's. A session's peer identity key
is available to the party. Every plaintext and control payload a session
yields is attributed exactly as the session is, and no more. What a party
sends on a session that is no contact's reaches whoever holds its peer key.

**The initiator** establishes only with an expectation. An implementation
offers initiator establishment under both forms:
- *known*: the record of the contact she means to reach, which she selects
  herself. The record is non-empty: a contact she holds no record for is
  reached under *first contact*.
- *first contact*: for a peer she holds no record for. It carries all her
  records.

Stating *first contact* for a contact she holds a record for, or leaving some
of her records out of it, is the party's own failure, which no implementation
can see (ASM-14).

She refuses an expectation as a malformed record (`MalformedRecord`), before
any check of Sending the initial message, when it holds a non-canonical key,
in the record under *known* or in any of her records under *first contact*,
or when it is *known* with a record whose two sets are both empty.
Decoding the bundle is the decoder's (message-format.md), not a check of
Sending the initial message, and no order is fixed between decoding and this
refusal: for a malformed expectation and bundle bytes that do not decode,
either refusal conforms.

Then, after the bundle's presence and canonical-key checks, and before the
identity-key rule, the signature checks, the KEM prekey's input checks and
anything that draws randomness or computes an agreement, she checks the
bundle's identity key:
- **under *known*,** by classifying it against that record. *Retired* is
  refused as a retired identity (`RetiredIdentity`). *New* is refused as an
  unexpected identity (`UnexpectedIdentity`). *Same* goes on.
- **under *first contact*,** by looking it up in her records:
  - a key the lookup finds a contact's, or ambiguous, is refused as an
    unexpected identity (`UnexpectedIdentity`). It is a recorded contact's
    key, served under another name. That holds even when it is also
    *retired* for another contact.
  - a retired key (*same* for no contact) is refused as a retired identity
    (`RetiredIdentity`).
  - an unattributed key goes on.

Either way the check applies the identity-key rule to the key first, so a
key that is not an identity key is refused as an invalid identity key, as the
rule's own check would refuse it (Sending the initial message).

A bundle refused for its identity key is refused as such, even if a later
check would also have failed. Nothing is verified, drawn, computed or sent
for it.

The order is fixed for three reasons:
- **Nothing is spent on a key she already refuses.** The check needs only
  her own records and the key. Made ahead of the signatures, as the identity
  check against a named key was made before it, it costs no signature
  verification, no random value and no agreement for a bundle she will
  refuse.
- **Refusals by key are reported as such.** A bundle under a key her
  expectation refuses is reported as that refusal, even when a signature
  would fail, its KEM prekey would fail the input checks, or one of its
  prekeys would give a non-contributory agreement.
- **Malformed input is reported as such.** Under a well-formed expectation,
  a bundle that fails decoding, the presence check or the canonical-key check
  is reported as that, and a key that is not an identity key as an invalid
  identity key, never as a refused identity. A malformed expectation is
  reported first (`MalformedRecord`), except against a bundle that fails
  decoding, where either refusal conforms.

Her session is then attributed by a lookup, like any other. Under *known*,
a key that is *same* in her record and also *same* in another contact's
record goes on, and the session is ambiguous: no contact's (ASM-14).

**A contact she holds a record for is never a first contact.** To accept a
new key for it, she records the key in its current set and establishes under
*known*. That covers:
- an ordinary key change, refused as an unexpected identity under *known*;
- a contact whose keys are all retired;
- a contact whose recorded key the identity-key rule refuses, such as one a
  release admitted before the rule (identities-and-devices.md, A stored key
  the rule refuses). She records the new key, retires the refused one, and
  establishes under *known*.

She can take the key from the refused bundle. That refusal came before the
bundle's signatures, so it verifies nothing about the key. The recommended
way is to record it after the two people compare the verification number
computed from that key and her own (identities-and-devices.md, The identity
pair digest).

**The responder** establishes as Receiving the initial message states.
Whatever key the message carries, provided it passes the identity-key rule
there, once the message authenticates:
- the one-time prekeys it names are removed;
- on the last-resort path, its replay identity is recorded.

The session is attributed only by a lookup. A malformed record is skipped
and reported there; it does not refuse. This section adds no responder
refusal beyond the identity-key rule of Receiving the initial message.

**First contact, in either role,** gives a session whose key is in no
record: an unattributed session. The party may use it, as the paragraph on
attribution states. It attributes the session by recording the peer key in
a contact's current set. The recommended way is after the two people compare
the verification number computed from that session's keys. Recording a key
without that comparison is the party's policy, and a session attributed that
way rests on the directory's word for the key.

**Discarding a session** is the party's choice, and it is final for that
handshake. Its prekeys are consumed, or its replay identity recorded, so
neither the message nor any later delivery of it establishes again, and the
peer goes on sending into a session nobody holds. Keeping sessions that are
no contact's costs storage, and anyone can open them under fresh keys
(threat-model/adversaries.md, ADV-01). Discarding those whose key is in no
record is a legitimate bound, and loses only those handshakes.

**What a refusal, a classification or a lookup shows.**
- It compares a key with records, and shows nothing about when the key was
  made or why it differs.
- An initiator's refusal by her expectation comes before the bundle's
  signatures are verified, so it shows nothing about who signed the bundle.
- A session shows more. For the initiator, the holder of its peer key signed
  the bundle's prekeys at some time. For the responder, the initial
  message's author held that key's secret or the responder's signed-prekey
  secret (security-properties/authentication.md, REQ-AUTH-03).
- It does not show who delivered it. A directory or network attacker can
  relay another party's genuine bundle or message.
- A bundle carries no date (REQ-AUTH-01). A directory can present a key a
  contact has stopped using, which is *retired* only if a record says so.
- At the protocol level, a contact's new device cannot be told apart from a
  substituted key: both are *new*.

**What is sent.** No message carries an expectation, a classification or a
lookup's result. Whether an initiator sends an initial message after a
bundle does depend on her expectation, since a refusal sends nothing. So
for each bundle it serves, whoever served it learns whether her expectation
accepts that key:
- under *known*, whether the key is *same* in that record;
- under *first contact*, whether the key is unattributed in her records.

That costs the server nothing, is silent, and can be repeated on every
fetch. A probe she accepts is a working substitution (exclusions.md, EX-09;
security-properties/limitations.md, LIM-15).

**When a key differs.** A session's peer identity key is fixed for the
session's life. An existing session accepts a repeat of its initial message
only if its `identity` equals the session's, and then decrypts it as part of
that session (Receiving the initial message). So a different key reaches a
party only as a new session. It does not differ when the peer's identity
secret is copied, restored or taken. A further delivery of a handshake that
already established a session forms no new session: the existing session
takes it as a repeat, or, without that session, it is refused (Replay, and
why the ratchet must follow).

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
accepted** -- a replay identity derived from the agreed `SK`, tagged with the
last-resort KEM key the handshake was made against -- and refuses a repeat. The record is
bounded at 1024 entries **per key**: the current last-resort key and the one
the last rotation retired each have a budget of their own, so the record holds
at most two of them. It fails closed rather than evicting: a new last-resort
handshake naming a key whose budget is spent is refused
(`LastResortRecordFull`) and nothing changes, so nobody can push a victim's
replay identity out by completing handshakes of their own. A key's entries are
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

### The replay identity

A handshake is on the last-resort path when its `kem_prekey_id` names Bob's
current last-resort KEM prekey or the one the last rotation retired. Its
replay identity is 32 bytes: HMAC-SHA256, keyed with a fixed label, over the
agreed `SK`.

```
replay_identity = HMAC-SHA256(
    key  = LAST_RESORT_HANDSHAKE_LABEL,
    data = SK,
)
```

The input is built as follows:

- **The key.** `LAST_RESORT_HANDSHAKE_LABEL` is the 32 ASCII bytes
  `tacenta last-resort handshake v2`, with no terminator (CONSTANTS.md). It is
  HMAC's key and is not secret. HMAC is used as a keyed hash to domain-separate
  this replay identity from other digests.
- **Why `SK`.** The identity is computed after KEM decapsulation and the
  responder's DH combination, before the initial ciphertext is decrypted. It
  is therefore invariant under distinct canonical X25519 encodings that yield
  the same clamped agreement, including torsion-equivalent ephemerals.

Bob computes the replay identity after decapsulation and DH derivation but
before decrypting the initial ciphertext. He refuses the message
(`ReplayedLastResort`) if any entry in the record holds that identity, whatever
key the entry is tagged with. The tag decides only which budget an entry counts
against and which rotation drops it. Bob adds the identity, tagged with
`kem_prekey_id`, only once the initial ciphertext has authenticated.

**Canonical encodings still matter at the wire boundary.** An initial message
decodes only if both `identity` and `ephemeral` are canonical (message-format.md,
Initial message). That rejects alternate byte spellings, while the `SK`-bound
identity also handles distinct canonical encodings that belong to the same
X25519 agreement class.

`CT` and the identifiers need no such rule:

- Decapsulation re-encrypts and compares the result with the ciphertext byte
  for byte (FIPS 203, Algorithm 18). Any other ciphertext yields the
  implicit-rejection secret, and so does not authenticate.
- The identifiers are fixed-width integers, with one spelling each.

### A replay record imported from an earlier format

A store read from a v1-v4 format may hold a replay record whose entries are
fingerprints of public bytes. They cannot be compared with a replay identity
derived from `SK`, so the store cannot tell whether a handshake it is about to
accept was seen before. It does not guess. The last-resort keys the record may
cover are listed in the store's `legacy_blocked` (session-persistence.md,
Legacy markers), and a handshake whose `kem_prekey_id` names a listed key is
refused (`LegacyLastResortRecord`) once the identifier is resolved, before
decapsulation, with the store unchanged. That is a condition the caller acts
on: the key stays refused until a rotation wipes it, and `rotate_kem` opens a
new key that is not listed (key-deletion.md). A handshake that names a
one-time KEM prekey never consults the record and is not refused.

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
    checked by the initial-message decoder (message-format.md, Initial
    message), under the rule `DecodeEC` states (Sending the initial message).
  - A prekey bundle's `identity_key`, `signed_prekey` and `one_time_prekey`,
    and a composite header's `dh`, are checked by the decoders that read them
    (message-format.md, Curve public keys). Alice checks a bundle's three
    again before she uses it (Sending the initial message).
  - The bundle's identity key meets the check a second time when its
    signatures are verified (identities-and-devices.md, Verifying a signature,
    step 1), which applies to whatever key a signature is verified under.

  An initial message with a re-spelled `identity` or `ephemeral`, a bundle
  with a re-spelled key, or a ratchet message with a re-spelled `dh`, does not
  decode. So the masking and the reduction never apply to a peer's key, and the byte
  string that identifies a key, in a signature, the associated data, a
  replay identity or the skipped-key store, is the only one that names it. An
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
    (message-format.md, Prekey bundle). A bundle that did not come from the
    decoder can fail it, after its signatures are checked (Sending the
    initial message);
  - `ByteEncode12(ByteDecode12(ek[0:1536]))` equals `ek[0:1536]`.

  Alice refuses a bundle whose key fails either check. She has then computed no
  agreement and sent nothing. Whether she has drawn `EKA` before these checks
  is not fixed.
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
harvest-now-decrypt-later comes from `SS`. These are stated as numbered
requirements in security-properties/, each with the assumptions it rests on and
its status:
- authentication.md: REQ-AUTH-01 to REQ-AUTH-04, REQ-AUTH-10, REQ-AUTH-12,
  REQ-AUTH-15 and REQ-AUTH-16;
- confidentiality.md: REQ-CONF-03 and REQ-CONF-06;
- forward-secrecy.md: REQ-FS-05.

The published specification also discusses deniability. This specification
states no requirement about it, and nothing in this project establishes it
(threat-model/exclusions.md, EX-12).

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
