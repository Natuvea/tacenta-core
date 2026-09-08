# Message format

This page specifies the bytes that go on the wire: how a ratchet message and an
initial (prekey) message are encoded, and how a header is bound into the AEAD's
associated data. The ratchet and session-establishment pages describe what the
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
  never has to guess where a field ends.
- **Fixed width where possible.** Counters are fixed-width big-endian rather
  than variable-length integers. This costs a few bytes and buys a decoder with
  no loops, which keeps it inside the subset the Charon and Aeneas translation
  models.
- **Versioned.** Every message starts with a version byte, so the format can
  change without ambiguity about which rules apply.

## Message type

Every message begins with a version byte and a type byte, so a receiver can tell
what it is holding without relying on the session state. This matters: a peer
that already has a session can still receive an initial message (a session reset,
or a changed identity), and must recognise it as one rather than trying to
decrypt it as a ratchet message.

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
included, so a ratchet message is 102 bytes plus the ciphertext. `ciphertext`
is the AEAD output, which already carries its authentication tag, and runs to
the end of the message; it is not length-prefixed because nothing follows it.

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
unrecognised version or an unexpected type byte.

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

## Key identifiers

An identifier names one of a party's prekeys on their own device. It is a 4-byte
big-endian value, opaque to the sender: it is generated by the party that owns
the prekey and echoed back unchanged.

The value `0` is reserved to mean **absent** and is never assigned to a real
prekey. That gives the initial message a fixed shape whether or not a one-time
prekey was used, which avoids an optional field and the ambiguity that would come
with it.

## Wire-sensitive values

These are the values a specific peer must agree on. They are gathered here, and
in one place in the model and the implementation, so that interoperability
findings change a table rather than a format:

| Value | Ours | Determined by |
|---|---|---|
| Message version byte | `0x01` | our choice, tier `ours` |
| Message type bytes | `0x01` ratchet, `0x02` initial | our choice, tier `ours` |
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
that is not the canonical one. Rejection is a decode failure, distinct from an
authentication failure, and neither reveals more than that the message was not
acceptable.

## Sources

The functional requirements come from Signal's published Double Ratchet
specification revision 4 (`HEADER` and `CONCAT`, and the requirement that the
pair parse uniquely) and the published PQXDH specification revision 3 (the
initial message's contents, and that it be encoded unambiguously). The concrete
encodings are ours, for the reasons given above, and are not derived from any
other implementation.
