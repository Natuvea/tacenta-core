# Protobuf profile

This page specifies the bounded protobuf profile: which byte strings are
accepted as the protobuf region of two external message types, a ratchet
message body and a prekey-message envelope, and what an accepted byte string
means. `Model.Protobuf` is the formal statement of everything here, and
`tacenta-core/protobuf` implements it.

## Role and status

The profile is a bounded wire profile for two message types, not a protobuf
implementation. It accepts a small subset of the protobuf wire encoding,
within declared limits, and refuses everything outside that subset rather
than skipping it. Nothing outside the subset is specified, because nothing
outside it is accepted.

The field numbers and wire types of the two message types follow an external
interoperability profile, determined by black-box observation of a pinned
build (ADR-0003), and [CONSTANTS.md](../CONSTANTS.md) records them at tier
`nominated`. Compatibility is claimed only by version and covered surface
(ADR-0004), and this page claims none: it fixes what the profile accepts, not
that any other implementation emits it. The limits and the refusal policies
are ours, at tier `ours`.

The profile covers the **protobuf region only**. A caller separates that
region before parsing it, and anything framing it is outside this page. For
the ratchet message body the region is followed by a trailing authenticator,
which the profile neither reads nor checks. The prekey envelope has no
trailing authenticator, so its region runs to the end of the input. No
version byte is read or written by the profile.

## Not the engine's message format

**The engine's own `Session` send and receive path does not use this
profile.** The bytes a peer sends are parsed by the `tacenta-wire` decoders
-- `decode_message` and `decode_composite` for a ratchet message,
`decode_initial` for a prekey message, and `decode_bundle` for a fetched
prekey bundle -- in the format [message-format.md](message-format.md)
specifies. That format is fixed-width and big-endian, and is not protobuf.

The profile's parser is proved to agree with `Model.Protobuf`, but it has no
caller on the live path: outside its own crate, this tree references it only
from a fuzz target (`tacenta-proofs/CLAIMS.md`, "The verified protobuf parser
has no caller"). Read this page as the definition of a profile the
implementation can parse, not as a description of what a Tacenta session puts
on the wire.

## Bounds

```
maxMessageLen   = 16384   bytes in the protobuf region
maxFieldNumber  = 15      largest field number a tag may carry
maxFields       = 32      most fields one parse reads or records
maxVarintBytes  = 5       longest varint
maxU32          = 4294967295   largest value a varint carries (2^32 - 1)
```

A region longer than `maxMessageLen` bytes is refused before any byte of it
is read. A region of exactly `maxMessageLen` bytes is within the bound.

## Varints

A varint is base-128 and little-endian: each byte carries seven bits of the
value, least significant group first, and its top bit says whether another
byte follows.

```
varint   = byte_0 || byte_1 || ... || byte_k        0 <= k <= 4
byte_i   = more_i (bit 7) || low_i (bits 0-6)
more_i   = 1 for i < k, and 0 for i = k
value    = low_0 + low_1 * 128 + ... + low_k * 128^k
```

A varint is refused when any of the following holds:

- **It is longer than five bytes.** A fifth byte with its top bit set is
  refused, and no sixth byte is read.
- **It is not minimal.** A final byte of `0x00` in any position but the
  first is refused. `0x00` on its own is zero; `0x80 0x00` is a second
  spelling of zero and is refused. This is the whole of the minimality rule,
  and it is sufficient: every accepted varint is exactly the minimal encoding
  of the value it decodes to (`varint_canonical`).
- **Its value does not fit 32 bits.** The value is refused as soon as the
  bytes read so far exceed `maxU32`. So a five-byte varint's final byte is
  one of `0x01` to `0x0F`.
- **The input ends first.** Input that ends before a final byte (one with its
  top bit clear) is refused.

Bytes after the final byte are not part of the varint and are left for what
follows it.

## Tags

A field starts with a tag, a varint whose value packs a field number and a
wire type:

```
tag      = varint                   value = field * 8 + wire
field    = value div 8              1 <= field <= maxFieldNumber
wire     = value mod 8              0 (varint) or 2 (length-delimited)
```

Reading a tag applies these checks in this order:

1. The tag is read as a varint, under every rule above.
2. A field number of `0` is refused, and a field number above
   `maxFieldNumber` is refused rather than skipped.
3. A wire type other than `0` or `2` is refused. That is types `1`, `3`, `4`,
   `5`, `6` and `7`.

Together these rules mean every accepted tag is a single byte, from `0x08`
(field 1, varint) to `0x7A` (field 15, length-delimited). A larger tag value
has a field number above the bound, and a multi-byte spelling of a smaller
one is not minimal.

A field whose tag passes these checks is not yet accepted. Its message type
then decides whether it may appear at all (below).

## Length-delimited fields

```
v_field   = tag (wire 0) || value (varint)
ld_field  = tag (wire 2) || len (varint) || bytes (len)
```

`len` is a varint under the rules above, so it is at most five bytes, fits 32
bits and is minimal. A `len` greater than the number of bytes left in the
region after it is refused, and nothing is taken. Otherwise exactly `len`
bytes are taken as the field's value, and parsing continues after them. A
`len` of zero is accepted and gives an empty value.

Because the whole region is at most `maxMessageLen` bytes, no
length-delimited value can exceed that bound.

## Fields in a message

A message's region is a sequence of fields, parsed one at a time until the
region is used up or a refusal occurs. For each field, in this order:

1. The tag is read (Tags, above).
2. **The field number is recorded.** A field number already recorded in this
   message is refused: a repeated field is not resolved by taking the first
   or the last. A field is also refused if `maxFields` field numbers are
   already recorded.
3. **The field number must belong to the message type**, with the wire type
   the message type gives it. A number the message type does not define is
   refused, and so is a defined number carrying the other wire type.
4. The value is read, as a varint or as a length-delimited field.

At most `maxFields` fields are read. After the fields, the message is refused
if bytes remain in the region, or if a required field was never recorded.

In the model a refused parse has a single outcome, so the order of the checks
does not change which byte strings are accepted. It decides only which
refusal an implementation reports (Refusal, below).

Each field that parses carries a distinct field number from its message
type's set. So a ratchet message body can hold at most five fields and an
envelope at most eight. For these two message types, neither the `maxFields`
bound on reads nor the one on recorded numbers is ever the limit reached.
Likewise, once every field number the message type defines has been recorded,
any byte that follows is read as a further field. That field is necessarily
refused at step 1, 2 or 3.

## Ratchet message body

```
field  name              wire type          presence
1      ratchetKey        length-delimited   required
2      counter           varint             required
3      previousCounter   varint             required
4      ciphertext        length-delimited   required
5      pq                length-delimited   required
```

- `ratchetKey`: the sender's ratchet public key, as bytes.
- `counter`: the message's number in its sending chain, a 32-bit unsigned
  value.
- `previousCounter`: the length of the sender's previous sending chain, a
  32-bit unsigned value.
- `ciphertext`: the encrypted payload, as bytes.
- `pq`: the post-quantum ratchet's part of the message, as bytes.

The field names are this project's own. Only the numbers and wire types come
from the external profile. The descriptions are informative: the profile gives
a field no meaning beyond its number, wire type and presence, and what a value
means is decided by whatever consumes the parsed fields.

**Every field is required.** A body missing any of the five is refused. A
missing field is never replaced by a default, because a default is a value
nobody sent. A field number of 6 to 15 passes the tag check and is then
refused at step 3. A repeated field number is refused at step 2. The body is
refused if any byte of the region is left over, so the region ends exactly at
the end of its last field.

## Prekey envelope

```
field  name              wire type          presence
1      prekeyId          varint             optional
2      baseKey           length-delimited   required
3      identityKey       length-delimited   required
4      message           length-delimited   required
5      registrationId    varint             required
6      signedPrekeyId    varint             required
7      pqPrekeyId        varint             required
8      kem               length-delimited   required
```

- `prekeyId`: the identifier of the recipient's one-time prekey, when one was
  used.
- `baseKey` and `identityKey`: the sender's base and identity public keys, as
  bytes.
- `message`: an inner message, carried as bytes. The profile does not parse
  inside it.
- `registrationId`: a registration identifier, a 32-bit unsigned value.
- `signedPrekeyId` and `pqPrekeyId`: identifiers of the recipient's signed
  prekey and post-quantum prekey, 32-bit unsigned values.
- `kem`: the KEM field, as bytes.

As with the ratchet body, the names are ours and the numbers and wire types
are the external profile's, and the descriptions are informative.

**Field 1, `prekeyId`, is optional, and it is the only optional field in
either message type.** When absent, the parsed envelope has no identifier.
That is not the same as an identifier of zero: a present field 1 with the
value `0` is accepted and gives the identifier `0`. Field 1 is optional
because the external profile omits it from well-formed messages that used no
one-time prekey, and requiring it would refuse them.

Fields 2 to 8 are required, and an envelope missing any of them is refused. A
field number of 9 to 15 passes the tag check and is then refused at step 3. A
repeated field number, including a repeated field 1, is refused at step 2.
The envelope's region runs to the end of the input, and it is refused if any
byte is left over.

## Field order and canonicality

**Field order is free.** A reader accepts a message type's fields in any
order, so one ratchet message body has up to 120 spellings, one for each
ordering of its five fields. Varints and tags each have exactly one accepted
spelling, but the profile is not canonical at the level of a message. That is
unlike [message-format.md](message-format.md), whose own format is.

The model defines no encoder for either message type, so the profile does not
fix an emission order. The implementation's encoders emit fields in ascending
field-number order and omit an absent `prekeyId` entirely. They do not emit
it as zero. A reader cannot rely on that order.

A parsed message re-encoded therefore need not reproduce the bytes it was
parsed from, and for an input whose fields are not in ascending order it does
not. Anything that covers these bytes with an authenticator has to be checked
over the bytes received, not over a re-encoding. Canonical emission and
raw-byte fidelity are not proved (`tacenta-proofs/CLAIMS.md`).

**Nothing inside a field is validated.** The profile checks structure only.
In particular:

- A length-delimited field of length zero is accepted for every field that
  has one, including the three key fields and `kem`.
- No key's length or form is checked.
- `counter`, `previousCounter`, `registrationId` and the three identifiers
  may take any 32-bit value, including zero.
- `message` and `pq` are not parsed.

Any such check belongs to whatever consumes the parsed fields.

## Refusal

The model has two outcomes: an accepted byte string with its parsed value,
or a refusal. Its parse state carries refusal as a single flag and names no
refusal categories. Which refusal a rejected byte string earns is left to the
implementation.

`tacenta-core/protobuf` reports one of five categories: `TooLong`,
`Truncated`, `BadVarint`, `NotInProfile` and `Duplicate`. **Which condition
produces which category is implementation-defined.** A conforming
implementation must refuse exactly the byte strings this page refuses, and a
category name carries no requirement beyond that. For the general rule, see
error-handling.md.

## Sources

`Model.Protobuf` (`tacenta-model/Model/Protobuf.lean`) is the formal statement
of this page: the bounds, `varint`, `decodeTag`, `lengthDelimited`, `admit`,
`parseRatchetBody` and `parsePrekeyBody`. Its `varint_canonical` theorem is the
minimality claim above. The refinement theorems in
`tacenta-proofs/translation/Translation/ProtobufT3.lean` prove that the
readers in `tacenta-core/protobuf` compute what the model says, on every
input. The encoders are covered by no theorem.

The field numbers and wire types of both message types are tier `nominated`.
They follow an external interoperability profile determined by black-box
observation of a pinned build (ADR-0003), and compatibility is claimed only by
version and covered surface (ADR-0004). No published specification defines
them, and they are not derived from any other implementation's source. The
varint and tag packing are the general protobuf wire encoding's. The
restrictions placed on it, and the bounds `maxMessageLen`, `maxFieldNumber`,
`maxFields` and `maxVarintBytes`, are tier `ours`: free choices recorded in
[CONSTANTS.md](../CONSTANTS.md).
