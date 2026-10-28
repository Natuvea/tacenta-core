# Message format

This page specifies the bytes that go on the wire: how a ratchet message, an
initial (prekey) message, and a published prekey bundle are encoded, and how a
header is bound into the AEAD's associated data. The ratchet and session-establishment pages describe what the
fields mean; this page fixes how they are written down.

Unlike the derivations, almost nothing here is fixed by a published
specification. The Double Ratchet specification defines `HEADER` and `CONCAT`
functionally and leaves the encoding to the application; PQXDH says only that the
initial message must be encoded unambiguously. So this format is ours. It is
designed so that the values a specific peer would require are isolated in one
place (see Wire-sensitive values), so that a change to one of them is a small
edit rather than a rewrite.

## Principles

- **Canonical.** Exactly one valid encoding of a given message. A decoder
  rejects anything else rather than accepting a second spelling, so a message
  cannot be re-encoded into a different byte string that still authenticates.
- **Unambiguous.** Every variable-length field is length-prefixed, so a decoder
  never has to guess where a field ends. The one exception is a field that runs
  to the end of its message -- a ratchet message's ciphertext, and the complete
  ratchet message an initial message ends with -- which needs no prefix because
  nothing follows it.
- **Fixed width where possible.** Counters are fixed-width big-endian rather
  than variable-length integers. This costs a few bytes and buys a decoder with
  no loop whose length depends on a value it has read (the one loop, over an
  absent field's zero padding, has a fixed width), which keeps it inside the
  subset the Charon and Aeneas translation models.
- **Versioned.** Every message starts with a version byte, so the format can
  change without ambiguity about which rules apply.

## Message type

Every message begins with a version byte and a type byte, so a receiver can tell
what it is holding without relying on the session state. This matters: a peer
that already has a session can still receive an initial message (a session reset,
or a changed identity), and must recognise it as one rather than trying to
decrypt it as a ratchet message. What the existing session does with it, and
what is left to the application, is stated in session-establishment.md,
Receiving the initial message.

```
type = 0x01   ratchet message
type = 0x02   initial (prekey) message
type = 0x03   prekey bundle
```

The bundle is not a message a peer decrypts; it is the published key material a
sender fetches before opening a session (session-establishment.md). It shares
the version-and-type framing because it travels the same path and a decoder
should reject a bundle handed to it as a message on the type byte rather than on
a length mismatch further in.

**These bytes are ours, not anyone else's.** The version and type bytes do not
have to match a value some other implementation emits: this is our own wire
format, the interoperating layer is the bundle, and
[CONSTANTS.md](../CONSTANTS.md) records `VERSION`, `TYPE_RATCHET`,
`TYPE_INITIAL`, and `TYPE_BUNDLE` at tier `ours` -- free choices authorised by
nobody but us. The constants that have to match a peer belong to the bundle
layer, and none of them appears in the framing above.

## Ratchet message

The header is the **composite** header: the Diffie-Hellman ratchet's, the
sparse post-quantum ratchet's position, and the agreement's own message, side
by side. The classical 40-byte header of the Double Ratchet alone is not a
message this decoder accepts.

```
message    = composite || ciphertext
composite  = version || type=0x01
           || dh (32) || pn (4) || n (4)
           || pq_epoch (8) || pq_n (8)
           || ag_epoch (8) || ag_type (1)
           || chunk_present (1) || chunk_index (2) || chunk (32)
```

All counters are big-endian. The composite header is **102 bytes**, framing
included, so a ratchet message is 102 bytes plus the ciphertext. A standalone
composite-header decoder is a public contract for vectors, associated-data
construction and implementations that parse the header before the ciphertext:
it accepts exactly those 102 bytes and refuses trailing bytes. `ciphertext` is
the AEAD output, which already carries its authentication tag, and runs to the
end of the ratchet message; it is not length-prefixed because nothing follows
it there. The ratchet-message decoder places no constraint on the ciphertext's
length or contents: the AEAD checks both (Authenticated encryption, below).
The whole message's length is bounded before any decoder reads it, by the size
rule (Message size, below), which is not part of the decoder.

`ag_type` names what the agreement's message carries, and its six values are
the ML-KEM Braid specification's members minus one:

```
ag_type = 0x00   none
        = 0x01   header
        = 0x02   ek
        = 0x03   ek + ct1 acknowledgement
        = 0x04   ct1
        = 0x05   ct2
```

A seventh member of the specification's set, `Ct1Ack`, is never produced by
this implementation -- the acknowledgement always rides on an `ek_vector`
chunk. It has no
byte here on purpose, so a peer emitting one fails to parse rather than being
ignored without error, as recorded on [the Braid's page](mlkem-braid.md). The
*set* of members is the specification's; the byte
assignment is ours, and [CONSTANTS.md](../CONSTANTS.md) records it at tier
`ours`.

The agreement's codeword is the one genuinely optional field, and it is
encoded the way an absent prekey is in a bundle: a presence byte, then the
field's full width regardless, zeroed when absent. That costs 34 bytes on a
message carrying no codeword and buys a canonical parse, since no field's
position depends on a value already read.

A decoder rejects a message shorter than its framing and header, and rejects an
unrecognised version or an unexpected type byte. It also rejects a `dh` that is
not the canonical encoding of a curve public key (Curve public keys, below), an
`ag_type` outside the six values above, a presence byte other than `0x00` or
`0x01`, and an absent codeword whose index or chunk bytes are not all zero.

Nothing in the encoding ties `ag_type` to the presence byte. A codeword carried
with a type that takes none decodes, and the agreement ignores it: it reads a
codeword only for the message type it is expecting. The header is authenticated
as associated data either way (below), so a codeword cannot be added or removed
in transit.

The vectors for this encoding (`tacenta-test-vectors/vectors/serialization/message-encoding.json`
and `tacenta-test-vectors/vectors/post-quantum/composite.json`) give the header
as named inputs, each the bytes of one field as encoded above, and the encoding
as `output`. Every input is named for its field except one: **the input
`chunk_data` is the field `chunk`**. The input `ciphertext`, in
`message-encoding.json` only, is the `ciphertext` field. The codeword's three
fields are three inputs, but they are one optional value and not independent
ones. `chunk_present` is the presence byte. When it is `01` the codeword is
present, with index `chunk_index` (two bytes, big-endian) and 32 bytes
`chunk_data`. When it is `00` the codeword is absent, and `chunk_index` and
`chunk_data` are its padding: all zero bytes, since the decoder refuses
anything else. No vector gives any other combination.

## Associated data

The Double Ratchet specification requires that the associated data given to the
AEAD is the application's own associated data with the serialized header
appended, and that the result is parseable as a unique pair. If the application's
part is not self-delimiting, concatenating the two is ambiguous: a different
split could produce the same bytes, which would let a header be reinterpreted.

So the length is written down:

```
CONCAT(ad, header) = len(ad) (4, big-endian) || ad || composite_header
```

**`header` here is the whole composite header, not the classical part of it,
and the difference is a security property rather than bookkeeping.** If the
associated data covered only the Diffie-Hellman header, an intermediary could
strip the agreement's message -- set the presence byte and codeword to absent
-- and the payload would still authenticate, removing the post-quantum half of
a conversation in flight without either party noticing. Binding the full
composite is what rules that out.

The composite header is fixed width, so with the length of `ad` recorded the
pair parses uniquely. For a session established by PQXDH, `ad` is the
associated data that page defines, binding both identity keys.

## Authenticated encryption

The AEAD is AES-256-CBC with PKCS#7 padding, followed by HMAC-SHA256 over the
associated data and the ciphertext (encrypt-then-MAC). Its keys are the output
of the message-key expansion (ratchet.md, Derivations): an AES-256 key
`enc_key`, an HMAC-SHA256 key `mac_key`, and a 16-byte `iv`. `AD` below is
`CONCAT(ad, header)` from the section above.

```
p          = 16 - (len(plaintext) mod 16)             -- 1 to 16
padded     = plaintext || p bytes, each of value p
ciphertext = AES-256-CBC-Encrypt(enc_key, iv, padded)
tag        = HMAC-SHA256(mac_key, AD || ciphertext)   -- 32 bytes
output     = ciphertext || tag
```

`enc_key`, `mac_key` and `iv` are bytes 0 to 31, 32 to 63 and 64 to 79 of the
expansion's 80-byte output, in that order. `AES-256-CBC-Encrypt` is the Cipher
Block Chaining mode of NIST SP 800-38A, section 6.2, over the AES-256 block
cipher of FIPS 197, with `iv` as the initialisation vector. With `padded` cut
into 16-byte blocks `P_1` to `P_n`:

```
C_0        = iv
C_i        = AES-256(enc_key, P_i XOR C_(i-1))          -- i = 1 .. n
ciphertext = C_1 || ... || C_n
```

Decryption is `P_i = AES-256-Inverse(enc_key, C_i) XOR C_(i-1)`, again with
`C_0 = iv`. The IV is not sent: it is not prepended to `ciphertext`, and no
header field carries it, because both sides derive it. Each message key is used
for one message (ratchet.md), so each `(enc_key, iv)` pair encrypts one
plaintext, and an IV derived from a secret is unpredictable to anyone without
the message key, which is what SP 800-38A, Appendix C, asks of a CBC IV.

A plaintext that is already a whole number of blocks gains a full block of
padding, so `ciphertext` is a nonzero multiple of 16 bytes and `output` is at
least 48 bytes. The HMAC input is `AD` then `ciphertext`, back to back, with
no length field for either: the length prefix `CONCAT` writes is what makes
the split unique. The tag is the full HMAC output, not truncated
(CONSTANTS.md). `output` is the ratchet message's `ciphertext` field.

A receiver holding `input` and `AD`:

1. refuses an `input` shorter than 32 bytes;
2. takes the last 32 bytes as `tag` and the rest as `ciphertext`, and refuses
   unless `HMAC-SHA256(mac_key, AD || ciphertext)` equals `tag`, compared in
   constant time;
3. only then decrypts: it refuses a `ciphertext` that is empty or whose length
   is not a multiple of 16, decrypts it with AES-256-CBC under `enc_key` and
   `iv`, and refuses unless the last byte `p` of the result is between 1 and
   16 and the last `p` bytes all equal `p`;
4. returns the result without its last `p` bytes.

Every refusal is an authentication failure, and none is a decode failure: the
ratchet-message decoder has already accepted the ciphertext whatever its
length. The failure is the same whichever step refused, so a padding refusal
cannot be told from a tag refusal, and nothing is decrypted until the tag has
verified.

**What is left to the primitives, and what is not.** The algorithms are
standard:

- the AES-256 block cipher (FIPS 197);
- CBC chaining (SP 800-38A, section 6.2);
- the padding above, which is the PKCS#7 scheme of RFC 5652, section 6.3;
- HMAC (RFC 2104) over SHA-256 (FIPS 180-4).

This section fixes every choice those algorithms leave open: the key and IV
and where they come from, the padding and its check, the tag's input and
length, and the order of the receiver's steps. Any conforming implementation of
them produces the same `output` and refuses the same inputs. Beyond the
algorithms, one requirement falls on the implementation itself: the tag
comparison in step 2 runs in constant time. The padding check needs no such
care, because it is reached only after a tag has verified.

`tacenta-core` takes AES-256, CBC and PKCS#7 padding from RustCrypto's `aes`
and `cbc`; it computes the tag with `tacenta-kdf`'s HMAC-SHA256 and checks it
with RustCrypto's `hmac` and `sha2`. Those libraries are one
implementation of these standards; this section, not they, defines the
behaviour.

## Initial message

The first message to a party carries what they need to complete the handshake,
followed by an ordinary ratchet message.

```
initial   = version || type=0x02 || identity (33) || ephemeral (33)
          || kem_ciphertext_len (4, big-endian) || kem_ciphertext
          || signed_prekey_id (4, big-endian)
          || one_time_prekey_id (4, big-endian)
          || kem_prekey_id (4, big-endian)
          || ratchet_message
```

The `ratchet_message` is a complete ratchet message, framing bytes and all, so it
still decodes on its own once the recipient has established the session.

`identity` and `ephemeral` are `EncodeEC` forms (the curve byte and the public
key), so they carry their own type byte. The KEM ciphertext is length-prefixed
because its size depends on the KEM. The identifiers name which of the
recipient's prekeys were used, so the recipient can load the matching private
keys.

`one_time_prekey_id` is the absent identifier (see below) when the bundle carried
no one-time curve prekey. The recipient must treat that as "no one-time prekey
was used" rather than as an identifier to look up.

A decoder refuses an initial message shorter than its two framing bytes, an
unrecognised version, a type byte other than `0x02`, input that ends inside
`identity`, `ephemeral`, `kem_ciphertext_len` or any of the three
identifiers, and a `kem_ciphertext_len` that runs past the end of the input.
It also refuses an `identity` or `ephemeral` whose first byte is not the
`EncodeEC` curve byte (session-establishment.md), since neither is then an
`EncodeEC` form, and an `identity` or `ephemeral` whose thirty-two key bytes
are not the canonical encoding of a curve public key (Curve public keys,
below). Each is a decode failure like the others. So an initial message with a
re-spelled `identity` or `ephemeral` does not decode, whether it would open a
session or repeat one (session-establishment.md, Receiving the initial
message), and every key this decoder returns is one `DecodeEC` accepts.

Everything after `kem_prekey_id` is `ratchet_message`, and the initial-message
decoder does not validate it: it may be empty, or not a ratchet message at
all. It is decoded, and refused if it does not decode, only when the recipient
decrypts it as a ratchet message. Nor does the decoder look at the identifier
values; Key identifiers, below, says how each is treated.

The decoder does not check `kem_ciphertext`'s length either. Decapsulation
refuses a ciphertext that is not the KEM's ciphertext length, 1,568 bytes for
ML-KEM-1024, and the recipient refuses the initial message at that point. The
refusal is not a decode failure. It comes before any secret is derived and
changes nothing. The size rule (Message size, below) reads `kem_ciphertext_len`
to find the ratchet message, whatever length it declares, and does not refuse a
length for being other than the KEM's.

## Message size

One protocol constant bounds every message, the same on every platform and for
every session. It is not negotiated and not configurable. An application may
refuse to send less than it allows; that is the application's own limit and
outside this specification.

```
MAX_PLAINTEXT_LEN      = 1,048,575 bytes   (2^20 - 1)
MAX_RATCHET_FRAME_LEN  = 150 + 16 * floor(MAX_PLAINTEXT_LEN / 16)
                       = 1,048,710 bytes
MAX_INITIAL_FRAME_LEN  = MAX_RATCHET_FRAME_LEN + 1,652
                       = 1,050,362 bytes
```

Only `MAX_PLAINTEXT_LEN` is chosen. The other two are derived from it and from
the formats above:

- A plaintext of `n` bytes gains 1 to 16 bytes of padding, so its AES-CBC
  ciphertext is `16 * (floor(n / 16) + 1)` bytes, and the tag adds 32
  (Authenticated encryption). The IV is derived, not sent. With the 102-byte
  composite header, a ratchet message carrying it is
  `102 + 16 * (floor(n / 16) + 1) + 32 = 150 + 16 * floor(n / 16)` bytes. That
  never decreases as `n` grows, so its largest value over the plaintexts a
  sender may encrypt is at `n = MAX_PLAINTEXT_LEN`.
- An initial message is its wrapper followed by a ratchet message
  (Initial message). With ML-KEM-1024's 1,568-byte ciphertext the wrapper is
  `2 + 33 + 33 + 4 + 1,568 + 4 + 4 + 4 = 1,652` bytes.

A frame, below, is the whole byte string a receiving operation is given.

**The sender's rule.** A session refuses to encrypt a plaintext longer than
`MAX_PLAINTEXT_LEN` bytes. This is the first check of the send, before every
other check of it, the refusal of a session whose agreement has failed
(mlkem-braid.md, Failure) included. The refusal is *plaintext too long*, a
condition the caller must act on (error-handling.md). It changes nothing: the
session is exactly as it was, the material for a pending initial message and
the agreement's state included, no random value is drawn, and there is nothing
to persist. The plaintext is not truncated and not split; carrying a longer
payload is the application's concern.

So a conforming sender never emits a ratchet message longer than
`MAX_RATCHET_FRAME_LEN`, or an initial message longer than
`MAX_INITIAL_FRAME_LEN`. Every message an initiator sends while its session is
pending is an initial message (session-establishment.md, Sending the initial
message), the first and the repeats alike.

**The receiver's rule (the size rule).** Every operation that receives a
frame applies it: a session's decrypt, and responder establishment from an
initial message (session-establishment.md, Receiving the initial message). Let
`L` be the frame's length. The frame is an *initial frame* when it has at least
two bytes and they are the version byte and the initial type byte (`0x01`,
`0x02`); every other frame, a ratchet message or anything unrecognised, is not.
The receiver refuses the frame as *too long*:

1. when `L > MAX_INITIAL_FRAME_LEN`, whatever the frame is;
2. when it is an initial frame, `L >= 72`, and, with `k` the big-endian value
   of bytes 68 to 71 (`kem_ciphertext_len`), `84 + k <= L` and
   `L - 84 - k > MAX_RATCHET_FRAME_LEN`. `L - 84 - k` is the length of the
   ratchet message the wrapper's own length field locates (Initial message),
   whatever `k` is;
3. when it is not an initial frame and `L > MAX_RATCHET_FRAME_LEN`.

An initial frame shorter than 72 bytes, or whose `84 + k` exceeds `L`, is
refused by rule 1 or not at all by this rule. Such a frame goes on to the
initial-message decoder, which refuses it as it would without the rule (Initial
message: input that ends inside a fixed field, or a `kem_ciphertext_len` that
runs past the end), so no ratchet message is ever taken from it. Every frame
the rule does not refuse goes on unchanged, and the checks after it refuse what
they refused before. The arithmetic is exact: an implementation with bounded
integers treats an `84 + k` that its integers cannot hold as exceeding `L`.

The rule reads only `L`, the first two bytes and, for an initial frame, bytes
68 to 71. It is the first check of the operation: before the frame is copied or
decoded, before the initial-message decoder and the repeat check
(`NotARepeatedInitial`), before the refusal of a session whose agreement has
failed, before any prekey is looked up, any ciphertext decapsulated, any
agreement computed and any random value drawn.

**Precedence.** So a frame the rule refuses is refused as too long whatever
else is wrong with it, and whatever state the receiver is in. In particular:

- an unknown version byte, or a type byte other than the initial message's
  (an unknown one, or the ratchet message's, which responder establishment
  refuses as the wrong type): such a frame is not an initial frame, so it is
  refused as too long when `L` exceeds `MAX_RATCHET_FRAME_LEN` (rule 3), and
  in any case when it exceeds `MAX_INITIAL_FRAME_LEN` (rule 1);
- an initial frame that is otherwise malformed (a key without its curve byte
  or not canonical, a `kem_ciphertext_len` that runs past the end) or that
  names prekeys the store does not hold, or is not a repeat of the session's
  own initial message: refused as too long under rule 1 or rule 2, before it
  is decoded and before any identifier is looked up;
- a session whose agreement has failed, or any other session that would
  refuse the frame for its own reasons: refused as too long first.

The same frames one byte within the bounds are not refused by this rule, and
each is then refused, or accepted, exactly as it would be without it: an
unknown version or a wrong type byte as a decode failure, an identifier the
store does not hold by the lookup that does not find it, and an initial frame that is not the session's repeat as `NotARepeatedInitial`
(on a session whose agreement has not failed; a failed session refuses a frame
that is not an initial frame with `AgreementFailed` before decoding it,
mlkem-braid.md, Failure).

The refusal is a decode failure (Rejection), and reveals no more to a peer than
any other. It changes nothing, whichever of the cases above applies: the
session is exactly as it was, its pending initial material and a failed
agreement's state included; on establishment the prekey store is exactly as it
was, its one-time prekeys and its last-resort replay record included; no random
value is drawn; nothing durable is written.

Rule 2 is why rule 1 is not enough. The initial-message decoder accepts any
`kem_ciphertext_len`, and a session receiving a repeated initial message never
looks at `kem_ciphertext` (session-establishment.md, Receiving the initial
message). Under rule 1 alone, an initial frame of `MAX_INITIAL_FRAME_LEN` bytes
with an empty `kem_ciphertext` would carry a ratchet message of
`MAX_INITIAL_FRAME_LEN - 84 = 1,050,278` bytes to that session. With rule 2 the
ratchet message a receiver decrypts is at most `MAX_RATCHET_FRAME_LEN` bytes,
standalone or inside an initial frame, on establishment and on a repeat alike.
Whether a `kem_ciphertext_len` other than the KEM's should be a decode failure
is a separate question, which this rule does not settle.

**The plaintext a receiver returns.** A ratchet message of `f` bytes carries an
AEAD `input` of `f - 102` bytes, so a ciphertext of `C = f - 134` bytes, and
`C <= 1,048,576 = 2^20` within the rule. The bound on what a receiver returns
then rests on this property of the AEAD:

> **Successful-open length property (relied on).** A ciphertext of `C` bytes
> that authenticates and whose padding is accepted opens to between `C - 16`
> and `C - 1` bytes of plaintext.

The receiver's steps 3 and 4 (Authenticated encryption) give it: `p` is between
1 and 16, and the result is `C - p` bytes. It is stated here because the bound
depends on it: an AEAD without it would let the rule admit longer plaintexts. With
it, every plaintext a receiver returns is at most `2^20 - 1 = MAX_PLAINTEXT_LEN`
bytes, which is why `MAX_PLAINTEXT_LEN` is one less than a multiple of 16. The
frame bounds fix the received maximum exactly, and no check after
authentication is needed. A peer that holds a message's keys and does not
follow the sender's rule still cannot make a receiver return more.

**Earlier revisions.** Revisions up to and including 0.2.0 had neither rule.
Their senders emit, and their receivers accept, longer messages. A receiver
that applies the size rule refuses a frame longer than the bounds from such a
sender as too long. The session that refused it goes on, since the refusal
changed nothing; a later message on the same chain skips past the refused one,
whose key is then held as any skipped key is (ratchet.md, Skipped keys). If the
refused frame was an initiator's first initial message, a later, smaller
initial message of the same handshake can still establish the session. A
receiver of an earlier revision accepts every message a sender that applies
the sender's rule emits, since none exceeds the bounds.

## Prekey bundle

What a party publishes and a sender fetches before opening a session: public
key material and the identifiers the sender echoes back in the initial
message. Nothing in it is secret, so the encoding needs no protection beyond
being unambiguous, and it is unambiguous the same way the messages above are.

```
bundle    = version || type=0x03
          || identity_key (32) || signed_prekey (32) || signed_prekey_signature (64)
          || kem_prekey_len (4, big-endian) || kem_prekey
          || kem_prekey_signature (64)
          || one_time_prekey_present (1) || one_time_prekey (32)
          || signed_prekey_id (4, big-endian)
          || one_time_prekey_id (4, big-endian)
          || kem_prekey_id (4, big-endian)
```

The curve keys are raw 32-byte values here, not `EncodeEC` forms: the framing
already says what the object is, and the position of each key says which it
is. The signatures are over the *tagged* forms, `EncodeEC(signed_prekey)` and
`EncodeKEM(kem_prekey)`, as session-establishment.md specifies, so a verifier
re-tags the key it reads before checking. `kem_prekey` is the KEM's own
encapsulation key, 1,568 bytes for ML-KEM-1024, and is the one variable-length
field; it is length-prefixed rather than assumed so a bundle produced under
one parameter set fails to decode under another instead of being read as a
shorter key followed by rubbish. So a decoder refuses a `kem_prekey_len` other
than the encapsulation-key length of the KEM it expects, as a decode failure.
A bundle is 1,811 bytes with that KEM.

The one-time curve prekey is the one optional field, and it is encoded the
way the ratchet message encodes its optional codeword: a presence byte, then
the full 32-byte width regardless. When the presence byte is `0x00` the 32
bytes must be zero and a decoder refuses anything else, so that one bundle
has one spelling; a presence byte other than `0x00` or `0x01` is refused too.
`one_time_prekey_id` is the absent identifier when the key is absent, and a
bundle in which the two disagree about presence is refused by the initiator
before any agreement is computed. The decoder does not compare the two: such
a bundle decodes, and the initiator's session establishment is what refuses
it, as an inconsistent bundle rather than a decode failure. Trailing bytes
are rejected: a bundle is a whole object, not a prefix of a stream.

A decoder also refuses a bundle whose `identity_key`, `signed_prekey` or
present `one_time_prekey` is not the canonical encoding of a curve public key
(Curve public keys, below), as a decode failure. The padding behind an absent
one-time prekey is not a key, and the rule above already fixes it to zeros.

## Curve public keys

A curve public key on the wire is 32 bytes, the little-endian u-coordinate of
RFC 7748, section 5. X25519 ignores bit 255 of those bytes and reduces a value
at or above p = 2^255 - 19, so, read loosely, several byte strings name one
key. A decoder accepts only the canonical one. Read the 32 bytes as a 256-bit
little-endian integer: the key is accepted exactly when that value is below p.
That refuses both other spellings, a key whose bit 255 is set and a key whose
value with bit 255 clear is at least p. An honest key generator produces
neither, so no honest key is refused. A refused key is a decode failure.

The rule covers every curve public key a peer sends:

- a ratchet message's `dh` (Ratchet message);
- a prekey bundle's `identity_key`, `signed_prekey` and, when present,
  `one_time_prekey` (Prekey bundle);
- an initial message's `identity` and `ephemeral`, the thirty-two key bytes
  after each one's curve byte (Initial message). These are `EncodeEC` forms,
  and the initial-message decoder refuses a re-spelled one, as the decoders
  above refuse theirs. `DecodeEC` states the same rule
  (session-establishment.md), so it refuses no key this decoder returned.

This is the Canonical principle applied to curve keys, which X25519 alone does
not enforce. A key's bytes serve as its identity in several places: a
signature covers a signed prekey's bytes, the associated data is computed over
bytes, and the ratchet keeps
skipped keys by a header's ratchet public key and takes a Diffie-Hellman step
when that key differs from `DHr` (ratchet.md). A second spelling of one key
would give it a second identity in each of them.

The rule is on what the wire's decoders accept. A decoder reads bytes and does
not test which keys are identity keys: a bundle's `identity_key` and an initial
message's `identity` are held to the identity-key rule after they decode, by the
party that admits them (identities-and-devices.md, Identity keys). The stored
formats hold every curve public key they carry to the same rule, and session-persistence.md
(Session, Semantic rules) says which reader refuses each and as what.

## Key identifiers

An identifier names one of a party's prekeys on their own device. It is a 4-byte
big-endian value, opaque to the sender: it is generated by the party that owns
the prekey and echoed back unchanged.

The value `0` is reserved to mean **absent** and is never assigned to a real
prekey. That gives the initial message a fixed shape whether or not a one-time
prekey was used, which avoids an optional field and the ambiguity that would come
with it.

Neither decoder looks at an identifier's value, so `0` decodes in every
position. In the `one_time_prekey_id` position it means no one-time curve
prekey. In the `signed_prekey_id` and `kem_prekey_id` positions it names no
prekey, since none is ever assigned it: an initiator does not check for it in
a bundle and echoes it, and the recipient refuses the initial message as
naming a prekey it does not hold, the same refusal as for any other unknown
identifier.

## Wire-sensitive values

These are the values a specific peer must agree on. They are gathered here, and
in one place in the model and the implementation, so that interoperability
findings change a table rather than a format:

| Value | Ours | Determined by |
|---|---|---|
| Message version byte | `0x01` | our choice, tier `ours` |
| Message type bytes | `0x01` ratchet, `0x02` initial, `0x03` bundle | our choice, tier `ours` |
| `EncodeEC` curve byte | see session-establishment.md | black-box research, tier `nominated` |
| `EncodeKEM` KEM byte | see session-establishment.md | black-box research, tier `nominated` |
| Field order and widths | as above | our choice |
| Absent-identifier sentinel | `0` | our choice |

The two encoding bytes are the values that must match a peer at the bundle
layer, which is the layer that interoperates. The rest are our own
conventions, and message-layer interoperability with any other implementation
is not claimed. The conformance manifest records that plainly rather than
implying compatibility.

## Rejection

A decoder rejects, rather than accepting and repairing: an unrecognised version;
a message too short for its fixed fields; a length prefix that overruns the
input; trailing bytes after a message that should have ended; and any encoding
that is not the canonical one, a curve public key's included (Curve public
keys). A receiver also rejects a frame the size rule refuses as too long
(Message size), before any decoder reads it. Rejection is a decode failure, distinct from an
authentication failure, and neither reveals more than that the message was not
acceptable. That restraint is about what a peer learns from a refusal. It does
not constrain the error types an implementation reports to its own caller,
which may be as specific as is useful (error-handling.md), beyond the AEAD's
one rule above that a padding refusal and a tag refusal are the same failure.

## Sources

The functional requirements come from Signal's published Double Ratchet
specification revision 4 (`HEADER` and `CONCAT`, and the requirement that the
pair parse uniquely) and the published PQXDH specification revision 3 (the
initial message's contents, and that it be encoded unambiguously). The concrete
encodings are ours, for the reasons given above, and are not derived from any
other implementation.

The authenticated encryption's primitives come from these standards:

- FIPS 197, for AES;
- NIST SP 800-38A, section 6.2, for CBC, and Appendix C, for its IV;
- RFC 5652, section 6.3, for the padding;
- RFC 2104, for HMAC, and FIPS 180-4, for SHA-256.
