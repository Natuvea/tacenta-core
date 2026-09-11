# Constant provenance

Every constant this engine emits or accepts, with the source that authorises it.
Required because a policy about provenance that keeps no record of
provenance cannot be audited.

**A constant with no entry here is a finding.** A constant whose entry reads
"chosen by us" is fine, and is the honest answer for anything the specifications
leave free. There are several, and this file is what distinguishes them from
mandated values without reading the code.

The provenance tiers are: **fact** (standards, mathematics, public test vectors),
**nominated** (labels, tags, version bytes: proposed from published material,
authoritative only after specification, independent derivation, or black-box
verification), and **ours** (free choices, authorised by nobody but us).

## Wire encodings

| Constant | Value | Tier | Provenance |
|---|---|---|---|
| `EncodeEC` type byte | `0x05` | nominated | External interoperability profile, determined by black-box observation of a pinned build (ADR-0003). |
| `EncodeKEM` type byte | `0x08` | nominated | External interoperability profile, determined by black-box observation of a pinned build (ADR-0003). |
| PQXDH KEM parameter set | ML-KEM-1024 | fact | Published PQXDH specification. |
| External message version and field profile | see implementation | nominated | Determined by black-box observation of a pinned build (ADR-0003). |
| **Our own** `VERSION` | `0x01` | ours | Our wire format, not libsignal's. Free choice. |
| **Our own** `TYPE_RATCHET` / `TYPE_INITIAL` / `TYPE_BUNDLE` | `0x01` / `0x02` / `0x03` | ours | Free choice. |
| **Our own** AEAD tag length | 32 bytes | ours | The full HMAC-SHA256 output, not truncated (`primitives/aead.rs`). See the note below on MAC truncation. |
| **Our own** `AgreementType` bytes | `None` `0x00`, `Hdr` `0x01`, `Ek` `0x02`, `EkCt1Ack` `0x03`, `Ct1` `0x04`, `Ct2` `0x05` | ours | Our composite header's tagging of the Braid message. The *set* of members is the ML-KEM Braid specification's, minus `Ct1Ack` which no state produces (`wire/src/lib.rs`, re-exported by `serialization/composite.rs`); the byte assignment is a free choice. |
| **Our own** `CHUNK_BYTES` | 32 | ours | The erasure codeword size, chosen here and repeated in `wire/src/lib.rs` so the wire format does not depend on a crate the wire decoders otherwise need not know. |
| **Our own** presence byte | `0x00` absent / `0x01` present | ours | The composite header's `chunk_present` and the prekey bundle's `one_time_prekey_present` (message-format.md), each followed by its field's full width whether present or not. The storage formats below use the same convention. Free choice. |
| **Our own** `ABSENT_ID` | `0` | ours | The prekey identifier meaning "no prekey was used" in an initial message (message-format.md, Key identifiers). Prekey stores number identifiers from one, so zero is never assigned to a real prekey (`serialization/mod.rs`, `sessions/lifecycle.rs`). Free choice. |

**On MAC truncation.** This engine truncates nothing: `primitives/aead.rs`
appends the full 32-byte HMAC-SHA256 tag. The Double Ratchet specification
states a 64-bit floor for a truncated tag, and a peer that truncates emits a
length of its own; that length is a fact about the peer and not a constant
this engine emits or accepts, so it has no row here. The tables in this file are for this engine's own constants only, and
a peer's constant does not belong in them.

## Derivation labels

| Constant | Value | Tier | Provenance |
|---|---|---|---|
| SPQR initialisation suffix | `"Chain Start"` | fact | Double Ratchet revision 4 §5.2 states this literal, and the engine uses it (`spqr/src/lib.rs`, `CHAIN_START_LABEL`). |
| `PROTOCOL_INFO` (spqr) | `Tacenta SPQR` | ours | The prefix every sparse-ratchet derivation carries ahead of its suffix (`spqr/src/lib.rs`). `SPQR_PROTOCOL_INFO` in §5.2's terms; the specification requires a constant naming the protocol and gives no example. Identifier ours. |
| SPQR root and chain step suffixes | `"Root"`, `"Chain"` | ours | **Not the specification's literal.** Revision 4 §5.2 names the epoch-advance suffix `"Chain Add Epoch"`; the engine's root step derives under `"Root"` and its chain step under `"Chain"` (`ROOT_LABEL`, `CHAIN_LABEL`), and the model matches the engine (`Model/SparseRatchet.lean`, `rootLabel`/`chainLabel`). Vector-sensitive: changing the engine to the specification's literal would invalidate every SPQR vector and is a decision to take on its own, not an edit to make here. |
| Braid suffixes | `":SCKA Key"`, `":Authenticator Update"`, `":ekheader"`, `":ciphertext"` | fact | The ML-KEM Braid specification states these literals. |
| `SK_INFO` (session) | `Tacenta_CURVE25519_SHA-256_ML-KEM-1024` | ours | The *shape* is PQXDH's published example; the protocol identifier is ours. |
| `PROTOCOL_INFO` (braid) | `Tacenta_MLKEM1024_SHA-256` | ours | Shape from the ML-KEM Braid specification's example, which orders KEM then hash and omits the curve. Identifier ours. |
| `COMBINE_INFO` (triple) | `Tacenta_CURVE25519_SHA-256_MLKEM1024` | ours | `TR_PROTOCOL_INFO` in §7.2's terms. §6.3 requires a constant naming the protocol and its parameters; the specification gives no example shape for this one. See the note on protocol identifiers below. |
| `SPLIT_INFO` (triple) | `COMBINE_INFO ‖ ":Split"` | ours | §7.1 mandates the split and not its constant. Suffix pattern copied from §5.2's. |
| `RK_INFO`, `MK_INFO` (ratchet) | `Tacenta RK`, `Tacenta MK` | ours | The classical ratchet's `KDF_RK` info and the message-key expansion info (`ratchet/src/lib.rs`). The specification leaves both application-specific. Free choices. |

## Signatures

| Constant | Value | Tier | Provenance |
|---|---|---|---|
| XEdDSA signature sign bit | top bit of `signature[63]` | nominated | External interoperability profile, determined by black-box observation of a pinned build (ADR-0003); one of the intentional differences from XEdDSA Revision 1, the one that widens the accepted set; `verify` also narrows it through `verify_strict` (see `xeddsa.rs`). The accepted set's edges in both directions are pinned by the verify-only vectors in `tacenta-test-vectors/vectors/primitives/xeddsa.json`. |
| Signed-prekey signature input | the *tagged* key form (33-byte `EncodeEC`, 1,569-byte `EncodeKEM`) | nominated | External interoperability profile, determined by black-box observation of a pinned build (ADR-0003). |

## Storage formats

None of these travels on the wire (session-persistence.md); they are read back
only by the code that wrote them. Listed here anyway, because the provenance rule is
about every constant this engine emits, and a format version byte written to
disk is emitted.

| Constant | Value | Tier | Provenance |
|---|---|---|---|
| `STATE_VERSION` (ratchet, spqr, braid, triple) | `0x01` each | ours | Four independent version namespaces, one per crate's own format. Free choices. |
| `PREKEY_STORE_VERSION` | `0x04` written; `0x03`, `0x02` and `0x01` accepted on read | ours | The prekey store's own format, at the session layer (`sessions/lifecycle.rs`). v4 tags each last-resort replay-record entry with the KEM key it was made against; v3 added the retired prekeys a rotation keeps; v2 added the replay record; v1 is the original. A v2 or v3 store's untagged replay-record entries read back tagged with the current key, the conservative reading; a v1 store has no record and reads back with nothing remembered; a v1 or v2 store reads back with nothing retired, which is what it recorded (session-persistence.md, Prekey store). |
| `SESSION_VERSION` | `0x01` | ours | `Session::export`'s format, same file. |
| `Braid` `state_tag` | 0-11 | ours | The stable numbering `Braid::state_tag` already reported before persistence existed: eleven live states in declaration order, then `Failed` at 11. Free choice, and deliberately not an abstraction leak -- the tag is all a caller sees. |
| Presence tag | `0x00` absent / `0x01` present | ours | Used for every optional fixed-width field in these formats, as the wire's presence byte is above. Free choice; the fixed width is the canonicity argument, not the tag value. |
| `Direction` tag (spqr) | `0x00` `A2b`, `0x01` `B2a` | ours | Free choice. |
| `LabelSet` tag (ratchet) | `0x00` (`Tacenta`) | ours | One live variant today. Free choice. |
| `tacenta-kem` and `tacenta-erasure` sub-formats | no version byte | ours | Deliberate: these appear only length-prefixed inside the Braid's format, so the Braid's own `STATE_VERSION` versions them. A second version byte would imply an independent compatibility story they do not have. |

## Values this engine does not emit or accept

Another implementation's message-layer HKDF inputs are not obtainable by
black-box observation: the X3DH/PQXDH `info` string and its operand spellings,
`KDF_RK`'s `info` string, `KDF_CK`'s constant bytes, the message-key `info`
string, the SHA-256/SHA-512 hash choice, and the `SPQR_PROTOCOL_INFO` and
`TR_PROTOCOL_INFO` identifiers. None belongs in the tables above, which are
for constants this engine actually emits or accepts. These are values a
libsignal-byte-compatible message layer would need, which this engine does not
attempt: they are represented as fields of `ExternalKdfProfile`
(`tacenta-core/src/interop.rs`), a type with no constructor, so that no such
output path can be written.

## Bounds

| Constant | Value | Tier | Provenance |
|---|---|---|---|
| `MAX_SKIP` | 1000 | ours | Our denial-of-service bound, the same value in the classical ratchet (`ratchet/src/lib.rs`) and the sparse ratchet (`spqr/src/lib.rs`). The specification recommends a limit and fixes no number. |
| `MAX_SKIPPED_STORE` | 2000 | ours | Same, in both ratchets. The total bound is this implementation's addition to the sparse ratchet (conformance manifest). |
| `MAX_SKIPPED_AGE` | 1000 | ours | How many received messages a stored skipped key may outlive before the classical ratchet deletes it (`ratchet/src/lib.rs`; key-deletion.md). The specification asks for an interval and fixes none. |
| `EPOCHS_KEPT` | 2 | ours | How many epochs of chains and skipped keys the sparse ratchet keeps before retiring the rest (`spqr/src/lib.rs`). The specification's main-text approach, with a number of our choosing. |
| `MAX_LAST_RESORT_SEEN` | 1024 | ours | How many spent last-resort handshake fingerprints a prekey store remembers **for each** last-resort KEM key that can still decrypt: the current one and the one the last rotation retired, so at most two budgets in the record at once. Never evicted: a new last-resort handshake naming a key whose budget is spent is refused with `LastResortRecordFull`, and a key's entries leave the record when a rotation wipes the key (`sessions/lifecycle.rs`; key-deletion.md). Counting per key is what makes one rotation relieve a spent budget, since the key it opens starts empty and every bundle handed out afterwards names it. The specification has no such record. |
| `MAX_MESSAGE_LEN`, `MAX_FIELD_NUMBER`, `MAX_FIELDS`, `MAX_VARINT_BYTES` | see `tacenta-core/protobuf` | ours | Profile limits we chose. `MAX_FIELD_NUMBER` must cover the external profile's field 8, which it does. |

## Three protocol identifiers

`session` uses `Tacenta_CURVE25519_SHA-256_ML-KEM-1024`, `triple` uses
`Tacenta_CURVE25519_SHA-256_MLKEM1024`, and `braid` uses
`Tacenta_MLKEM1024_SHA-256`.

Each follows its own specification's example where one is given. The braid's
follows the ML-KEM Braid specification, whose example orders the KEM before the
hash and omits the curve. The session's follows PQXDH's example, which
hyphenates the KEM name. The Double Ratchet specification gives no example
shape for `TR_PROTOCOL_INFO`, and the triple's takes PQXDH's operand order with
the braid's unhyphenated KEM spelling.

All three are distinct strings, so domain separation holds, and each is a free
choice that no specification constrains. There is no single house form today;
adopting one is a future decision about what our identifier *is*, and making
it means choosing one form and regenerating vectors for whichever constants
change.
