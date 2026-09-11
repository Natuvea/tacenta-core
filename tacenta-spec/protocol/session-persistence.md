# Session persistence

This page specifies the bytes a storage layer writes when it saves a
`Session` to disk and reads back when it restores one, so a session survives
a process restart. The ratchet, sparse-ratchet, triple-ratchet, Braid, and
message-format pages describe what each piece of state means; this page
fixes how it is written down for storage rather than for the wire.

Unlike message-format.md, **nothing here is wire-sensitive.** These bytes are
never sent to a peer and never compared against another implementation: they
are read back by the same code that wrote them. The format still has to
survive an application upgrade that changes a field, and a partial write, so
it is versioned and length-checked the same way a wire format is, but its
obligations stop at surviving corruption and version skew, not at
interoperating with anyone.

## Principles

- **Canonical and length-prefixed**, for the same reason message-format.md
  gives: a decoder that accepts more than one spelling of the same value, or
  has to guess where a variable-length field ends, is a decoder with a bug
  waiting in it. Every variable-length field here carries an explicit
  four-byte big-endian length ahead of it, and every list a four-byte
  big-endian count of its entries.
- **Versioned**, with its own version byte per format (the KEM's and the
  erasure codec's sub-formats, which appear only length-prefixed inside the
  Braid's, have none: the Braid's version byte versions them, CONSTANTS.md),
  in a namespace
  separate from any on-the-wire message version (message-format.md). A
  session-persistence version change and a wire-format version change are
  unrelated events, and conflating their numbering would make one look like
  it implied the other.
- **Composed bottom-up.** Each of `tacenta-ratchet`, `tacenta-spqr`,
  `tacenta-braid`, and `tacenta-triple` owns its own `to_bytes`/`from_bytes`,
  encoding only its own fields. `Session::export`/`import` composes these
  rather than reaching into any of their internals, so each format can change
  size or shape without the others' code changing.
- **No new abstraction leak.** The format's `state_tag` identifies which of
  the Braid's twelve states was saved, and the Braid section below names all
  of them, but the API exposes no more than it did: a caller can read the tag
  (`Braid::state_tag`) and cannot construct a state or read its contents. A
  Braid is exported and imported only whole, the same restriction callers
  already have on a live `Braid`.
- **Validated, not only parsed.** A decoder that reads every field
  correctly can still hand back a state no constructor builds: a ratchet
  private key beside a public key that is not its own, an epoch pair the
  sparse ratchet cannot follow, an identifier namespace with a collision in
  it. Each such state re-encodes to the bytes it came from, so the canonical
  principle above does not see it, and none fails at import -- each fails on
  some later message, the first two for good. So each type carries an
  `invariant`, the relations between its fields that its constructors
  establish, its operations preserve, and the operations and their proofs
  rely on, and its decoder calls it last and refuses on it. An `invariant` is
  not a description of every reachable state: a state can satisfy it and
  still be one no constructor builds, and the reader accepts that state. The
  rules are listed below: for the session and the prekey
  store under each format's "Semantic rules", and for the leaf formats under
  "Semantic rules of the leaf formats". Each list is complete: a reader
  refuses a state that breaks a listed rule, and no other state, on
  semantic grounds. The rules are checked as an inductive
  invariant: the tests and the fuzz
  targets in `tacenta-core` assert the predicate after every operation, not
  only at import.
- **Being inductive constrains the operations, not only the predicates.** A
  decoder that refuses a state its own library can produce is worse than one
  that refuses nothing: the state exports, re-imports, and is refused from
  then on. So where an operation could carry a counter to a value its
  predicate excludes, the value is made unreachable rather than the predicate
  widened. Three counters are reserved at their ceiling for exactly that
  reason: the classical ratchet's received-message clock stops at
  `u32::MAX - 1` rather than saturating into `u32::MAX`; the sparse
  ratchet refuses the agreement output that would advance it to epoch
  `u64::MAX` -- an epoch its own retention window then reads as covering
  nothing, retiring the chains it had just opened -- with the
  counter-exhaustion error it already returns for a chain at the end of its
  range; and the ML-KEM Braid refuses, in each of the two transitions that
  advance an epoch, the step that would land on `u64::MAX`, which is the
  epoch its own reader refuses. The Braid's is the case where reader and
  transitions had drifted apart, which is what the principle is about. No
  ceiling is reachable in an honest run: the first needs 2^32 accepted
  receives, the others 2^64 completed agreements. Because the Braid's
  refusing transition is also the one that emits an epoch's output, the last
  epoch it can complete on both sides is `u64::MAX - 2`. All three are
  pinned by
  a test in the crate that owns the counter.
- **At-rest protection is out of scope.** This format is plaintext once
  decoded; it authenticates nothing against a hostile reader of the storage
  medium, only against corruption. See key-deletion.md's note on what
  persisting a session means for that page's in-memory-only erasure claim.
- **Ordering is the storage layer's obligation, and it is stated.** The
  formats are independent, but the moments they must be written are not.
  Three rules, each with a concrete failure behind it: persist a session
  *before* transmitting what `encrypt` produced (or the same message key and
  IV are spent twice after a crash); persist *before* acknowledging what
  `decrypt` produced; and after `establish_responder`, persist the session
  *before* the prekey store, atomically where the medium allows (store first
  loses the peer's first message for good; session first leaves a consumed
  one-time prekey reusable). `Session::export`'s documentation in
  `tacenta-core` carries the same three rules with the reasoning, and is the
  place to change them. A fourth follows from rotation: persist the store
  after `rotate_signed_prekey` or `rotate_kem` and before republishing, or a
  restart forgets the rotation while the directory serves the new key.

## Ratchet state

```
ratchet_state = version(1)
             || dhs_pub(32)
             || dhr_pub_present(1) || dhr_pub(32)
             || rk(32)
             || cks_present(1)    || cks(32)
             || ckr_present(1)    || ckr(32)
             || ns(4) || nr(4) || pn(4) || events(4)
             || labels(1)
             || skipped_count(4)
             || skipped[skipped_count]

skipped = dh(32) || n(4) || stored_at(4) || key(32)
```

An optional key is a one-byte presence tag (`0x00` absent, `0x01` present)
followed by its full 32-byte width regardless, zeroed when absent -- the same
choice message-format.md's associated-data length prefix makes for the same
reason: a fixed-width optional field is provably canonical, a variable-width
one only tested. `labels` is a one-byte tag naming the `LabelSet` variant
(`0x00` today, for the sole `Tacenta` set). The reader refuses as malformed a
presence tag other than `0x00` or `0x01`, an absent key whose 32 bytes are not
all zero, and a `labels` tag that names no variant (today, any value but
`0x00`).

Every integer is big-endian: `ns`, `nr`, `pn`, `events`, `skipped_count`, and
each entry's `n` and `stored_at`. The `skipped` entries are written in the
store's order, which is the order the keys were stored; a key that replaced
one already held counts as stored when it replaced it (ratchet.md, Skipped
keys). That order is
meaningful, since eviction breaks ties between equal `stored_at` values by it
(ratchet.md, Skipped keys), but the reader accepts the entries in any order and
keeps the order it read.

## Sparse ratchet state

```
spqr_state = version(1)
          || rk(32) || epoch(8) || direction(1)
          || chains_count(4) || chains[chains_count]
          || skipped_count(4) || skipped[skipped_count]

chains  = epoch_key(8) || send_chain || receive_chain
chain   = presence(1) || ck(32) || n(8)   -- present, or zeroed if absent
skipped = epoch(8) || n(8) || key(32)
```

`direction` is a one-byte tag (`0x00` `A2b`, `0x01` `B2a`).

Every integer is big-endian: `epoch`, `chains_count`, `skipped_count`, each
`epoch_key` and chain `n`, and each stored key's `epoch` and `n`.

The `chains` entries are written in the order their epochs' chains were last
replaced, most recent last: an advance opens an entry, and a send, or a
receive that steps a chain, rewrites it. That order carries no meaning, and
the reader accepts any. The `skipped` entries are written in the order the keys
were stored, oldest first, and that order is meaningful: it is the order
eviction takes them in (sparse-pq-ratchet.md). The reader accepts any order and
keeps the order it read.

A chain whose presence byte is `0x00` is absent. The reader accepts it, though
no operation produces one: retiring an epoch removes its whole entry. An
operation that needs an absent chain is refused (`ChainRetired`). The reader
refuses as malformed a `direction` tag other than `0x00` or `0x01`, a chain
presence byte other than `0x00` or `0x01`, and an absent chain whose `ck` and
`n` bytes are not all zero.

## Braid

```
braid = version(1) || state_tag(1) || fields

epoch = 8 bytes, big-endian
auth  = root_key(32) || mac_key(32)

state_tag  state                  fields
0          KeysUnsampled          epoch || auth
1          KeysSampled            epoch || auth || key_pair || hdr_enc
2          HeaderSent             epoch || auth || key_pair || ct1_dec || ek_enc
3          Ct1Received            epoch || auth || key_pair || ct1 || ek_enc
4          EkSentCt1Received      epoch || auth || key_pair || ct1 || ct2_dec
5          NoHeaderReceived       epoch || auth || hdr_dec
6          HeaderReceived         epoch || auth || header || ek_dec
7          Ct1Sampled             epoch || auth || header || encaps || ct1 || ct1_enc || ek_dec
8          EkReceivedCt1Sampled   epoch || auth || encaps || ct1 || ek_vector || ct1_enc
9          Ct1Acknowledged        epoch || auth || header || encaps || ct1 || ek_dec
10         Ct2Sampled             epoch || auth || ct2_enc
11         Failed                 (nothing)
```

`state_tag` is the same stable 0-11 numbering `Braid::state_tag` already
reports (`mlkem-braid.md`'s eleven live states, plus `Failed`, for twelve
tags in total). `auth` is the Ratcheted Authenticator's two keys back to
back, with no presence tag: every live state carries one.

Every field after `auth` is written `len(4) || bytes`, so a sub-format's own
decoder always sees exactly the slice it produced and nothing else:

- `header` (64 bytes), `ct1` (1,408 bytes) and `ek_vector` (1,536 bytes) are
  the KEM's header, first ciphertext half and encapsulation-key vector, raw.
- `key_pair` (11,872 bytes) and `encaps` (2,592 bytes) are `tacenta-kem`'s
  incremental key pair and encapsulation state: each is its underlying bytes,
  with no version byte and no layout this page defines, and each reader
  refuses any other length. A `key_pair` holds, among the rest, the `header`
  and `ek_vector` its party sends (mlkem-braid.md, The KEM split). The reader
  checks those two, as the Braid's semantic rules below state, and nothing
  else in `key_pair`. It checks nothing in `encaps` beyond its length: an
  encapsulation state is derived from the encapsulation randomness and holds
  no hash, and no copy of another value the state carries, to check it
  against.
- `hdr_enc`, `ek_enc`, `ct1_enc`, `ct2_enc` and `hdr_dec`, `ek_dec`, `ct1_dec`,
  `ct2_dec` are erasure encoders and decoders, in the formats below.

**`key_pair` and `encaps` are delegated, and that limits which states move
between implementations.** Their layouts are the incremental interface's
serialisations in `libcrux-ml-kem` 0.0.10 (CONSTANTS.md, "KEM key pair and
encapsulation state lengths"). This page does not define them. Neither does
FIPS 203, which has no incremental form, or the ML-KEM Braid document. This is
a deliberate delegation (ADR-0006, point 5), and the consequence for another
implementation is this:

- **Tags it cannot import or export.** An implementation without that
  serialisation can carry `key_pair` and `encaps` only as opaque,
  length-checked bytes: it cannot decapsulate with the one or finish the
  encapsulation the other holds, and it cannot find in `key_pair` the header
  and `ek_vector` that this format's semantic rules check. So it cannot
  import, and go on from, a Braid in any state that carries one of them:
  - `key_pair`: tags 1 (`KeysSampled`), 2 (`HeaderSent`), 3 (`Ct1Received`)
    and 4 (`EkSentCt1Received`);
  - `encaps`: tags 7 (`Ct1Sampled`), 8 (`EkReceivedCt1Sampled`) and 9
    (`Ct1Acknowledged`).

  Nor can it write a state with those tags that this format's reader would
  import and that goes on correctly.
- **Tags it can move.** Tags 0 (`KeysUnsampled`), 5 (`NoHeaderReceived`), 6
  (`HeaderReceived`), 10 (`Ct2Sampled`) and 11 (`Failed`) carry neither field.
  This page defines them completely, so another implementation can import
  and export them, and a session whose Braid is in one of them.
- **When a session can move.** A session can move between implementations only
  while its Braid is in one of those five states.

A library change that alters either layout needs a new Braid `STATE_VERSION`.

A reader refuses a tag above 11, a stored `epoch` of `u64::MAX` (see the
principles above), and any bytes left after the last field.

### Erasure coder sub-formats

```
encoder  = next(2) || exhausted(1) || count(4) || chunk(32)[count]
decoder  = size(8) || needed(8) || count(4) || codeword[count]
codeword = index(2) || chunk(32)
```

All integers are big-endian. `exhausted` is `0x00` or `0x01` and nothing else.
`size` and `needed` are 64-bit on every platform, so a state moves between
word sizes. A reader refuses a `needed` above 65,536 or a `size` above
2,097,152 (65,536 chunks of 32 bytes) before narrowing either to its own word
size, so a 32-bit reader never keeps the low half of a value a 64-bit reader
would refuse. A count larger than the buffer could hold is refused before any
entry is read, and bytes left after the last entry are refused. Neither
format has a version byte: they appear only inside the Braid's, which
versions them (CONSTANTS.md).

In the encoder, `chunk[count]` are the value's chunks, `chunk_0` to
`chunk_(count-1)` in order (mlkem-braid.md, The erasure code). `next` is the
index of the codeword the encoder issues next: 0 for a new encoder, and one
more after each codeword it issues. Issuing index 65,535 instead sets
`exhausted` to `0x01` and leaves `next` at 65,535, and an exhausted encoder
issues nothing more (mlkem-braid.md, Codewords).

In the decoder, `size` is the value's length `n` in bytes, `needed` is its
chunk count `k`, and `codeword[count]` are the codewords the decoder holds,
each as its index and its 32 bytes. They are written in the order the decoder
kept them, which is the order in which each index first arrived. That order
carries no meaning, since the decoded value does not depend on it. The reader
accepts any order and keeps the order it read.

## Triple ratchet state

```
triple_state = version(1)
            || len(4) || ratchet_state
            || len(4) || spqr_state
```

The two ratchets' own formats above, each length-prefixed and unmodified:
this format does not know or care what is inside either one.

## Session

```
session = version(1)
       || len(4) || triple_state
       || len(4) || braid
       || ratchet_private(32)
       || len(4) || identity_ad
       || our_identity_public(32)
       || peer_identity_public(32)
       || pending_initial_present(1) || len(4) || pending_initial             -- len and field only when present
       || established_ephemeral_present(1) || len(4) || established_ephemeral -- len and field only when present

pending_initial = ephemeral_public(32)
                || len(4) || kem_ciphertext
                || signed_prekey_id(4) || one_time_prekey_id(4) || kem_prekey_id(4)
```

`ratchet_private` is the Diffie-Hellman ratchet's current private key, raw
32 bytes (the underlying curve library zeroizes its own resident copy; this
format wraps the returned copy the same way). `identity_ad` is fixed at 66
bytes in practice (two `EncodeEC` values, session-establishment.md) but is
length-prefixed here rather than assumed, since nothing at this layer
enforces that invariant at the type level. `pending_initial` and
`established_ephemeral` are each a presence byte followed by a
length-prefixed field when present, and nothing (not even the length
prefix) when absent.

The reader refuses each of the following as *malformed*
(`SessionDecodeError::Malformed`), of the short-or-malformed kind (Rejection):
a `triple_state` or `braid` that its own reader refuses, whatever that
reader's reason, its semantic rules included; a `pending_initial_present` or
`established_ephemeral_present` byte other than `0x00` or `0x01`; a
`pending_initial` that is not the layout above; and bytes left after the last
field. These are field-by-field refusals, made before the re-encode check
below, so none of them is reported as non-canonical or inconsistent.

### Semantic rules

Having decoded, and re-encoded to check that the input is canonical -- refused
as *non-canonical* (`SessionDecodeError::NonCanonical`) otherwise, as the
prekey store's check below is -- the reader refuses the session as *inconsistent* -- `SessionDecodeError::Inconsistent`
in `tacenta-core`, a variant distinct from malformed and from non-canonical
-- unless every one of the following holds. Each is a relation between
fields that no field-by-field read sees, and each, accepted, fails later
rather than here.

- **The ratchet private key is the private half of the advertised public
  key**: `ratchet_private`'s public key equals the classical ratchet's
  `dhs_pub`. Otherwise the peer's next Diffie-Hellman step agrees against a
  key this side does not hold, and every message after it fails, for good.
- **The sparse ratchet's epoch follows the Braid's.** With the Braid
  negotiating epoch `e` (its `epoch` field; `mlkem-braid.md`), the sparse
  ratchet's `epoch` is `e` when the Braid is in `Ct1Sampled`,
  `EkReceivedCt1Sampled`, `Ct1Acknowledged` or `Ct2Sampled` (state tags 7
  to 10, the states past the point where the header-receiving side folds
  the epoch's secret) and `e - 1` in every other live state (tags 0 to 6).
  Both sides pass through both, since the roles swap each epoch, and the
  session commits both halves together, so there is no persistence point
  between. A failed Braid (tag 11) is exempt: the failure is terminal and
  persists as such. Outside the relation the sparse ratchet refuses the next
  agreement output on every message and the session never recovers.
- **The associated data is the two identities in the role's orientation**:
  `identity_ad = EncodeEC(initiator) || EncodeEC(responder)`, with the
  role read from `established_ephemeral`, which every responder carries for
  its whole life and no initiator ever has. (`pending_initial` would not do:
  an initiator drops it once the peer answers.) Wrong orientation is an
  AEAD failure on every message in both directions.
- **The halves agree on the role.** The Braid's role is read from its
  public state -- the initiator sends the first epoch's header and the roles
  swap each epoch, so at epoch `e` the session's initiator is the
  header-sending side (tags 0 to 4) exactly when `e` is odd -- and must
  match the session's; so must the sparse ratchet's `direction`, `A2b` for
  the initiator. A failed Braid (tag 11) has no role, so for it the Braid's
  half of this rule is not checked and the `direction` half still is. The
  classical ratchet shows its role only until its first Diffie-Hellman step,
  and the Triple Ratchet's own invariant checks it against the sparse
  ratchet's while it can.
- **An unanswered initiator is not also a responder**: `pending_initial`
  present implies `established_ephemeral` absent.
- **The optional fields have their shape**: `pending_initial`'s
  `kem_ciphertext` is exactly one ML-KEM-1024 ciphertext long (CONSTANTS.md),
  and `established_ephemeral` is an `EncodeEC` value, 33 bytes with the curve
  byte first. Neither is checked where it is used: `encode_initial`
  length-prefixes whatever it is given, and a repeated initial message is
  matched against `established_ephemeral` byte for byte.
- **Each half satisfies its own crate's invariant**: the Triple Ratchet's,
  which covers both ratchets, and the Braid's. Their decoders refuse on
  these already, so at import this is a second reading: a half that breaks
  them is refused as malformed by its own reader, above, before this rule is
  reached.

The same predicate holds after every operation: `tacenta-core`'s tests
drive an honest pair through some fifty Braid epochs, restarting one side
or the other every few messages, and assert it after every message and
every round trip.

## Prekey store

`PrekeyStore::to_bytes`/`from_bytes` persist a party's own prekeys between
restarts: the private halves of the signed and one-time prekeys, the
identifiers a bundle names them by, the signatures a bundle carries, and two
records that exist only to survive a restart, the last-resort replay
fingerprints and the prekeys a rotation retired. The identity's own secret is
not here; `Identity` is separate and is persisted by the caller on its own
terms.

```
prekey_store = version(1)
            || identity_public(32)
            || signed_prekey_secret(32) || signed_prekey_id(4) || signed_prekey_sig(64)
            || one_time_count(4) || one_time[one_time_count]
            || len(4) || kem_pair || kem_id(4) || kem_sig(64)
            || kem_one_time_count(4) || kem_one_time[kem_one_time_count]
            || next_id(4)
            || seen_count(4) || seen[seen_count]                          -- v2 and later
            || previous_signed_present(1) || previous_signed              -- v3 and later
            || previous_kem_present(1) || previous_kem                    -- v3 and later

one_time        = id(4) || secret(32)
kem_one_time    = id(4) || len(4) || kem_pair || sig(64)
seen            = kem_id(4) || fingerprint(32)              -- v4
                = fingerprint(32)                           -- v2 and v3
previous_signed = secret(32) || id(4) || sig(64)      -- only when present
previous_kem    = len(4) || kem_pair || id(4) || sig(64)   -- only when present
```

`kem_pair` is an ML-KEM-1024 key pair (FIPS 203), the decapsulation key first,
length-prefixed wherever it appears:

```
kem_pair = dk(3,168) || ek(1,568)                         -- 4,736 bytes
dk       = dk_pke(1,536) || ek(1,568) || h(32) || z(32)   -- FIPS 203's layout
```

The reader refuses a `kem_pair` as malformed unless all four hold: its length
is exactly 4,736 bytes; `ek` passes the FIPS 203 section 7.2 modulus check;
`dk` passes the FIPS 203 section 7.3 hash check, `h` equal to `H` over the
`ek` inside `dk`; and the `ek` inside `dk` equals `ek` byte for byte. Nothing
else in `dk` is checked. `next_id` is the
identifier the next key added to the store will take, so that replenishment
continues the sequence rather than restarting it (key-deletion.md). `seen`
is the record of spent last-resort handshakes, oldest first, each
`fingerprint` constructed as session-establishment.md, "The fingerprint",
states; from v4 each
entry carries the identifier of the last-resort KEM key the handshake was
made against, which is `kem_id` or the identifier inside `previous_kem`,
and which is what lets a rotation drop a wiped key's entries
(key-deletion.md). The bound the store enforces (`MAX_LAST_RESORT_SEEN`,
CONSTANTS.md) is per key, so no count on its own expresses it and the reader
checks it in two places: a count larger than what the version could possibly
have written is refused as malformed before it sizes anything -- two budgets
for v4, whose entries name a key each and where two keys can still decrypt,
one budget for v2 and v3, whose untagged entries all read back under
`kem_id` -- and the per-key bound itself is a rule over what was read, below. The two `previous_*` fields are the signed prekey and the
last-resort KEM prekey the most recent rotation retired, each behind a
presence byte and, like the session's `pending_initial`, followed by
nothing at all when absent.

**The one-time lists' order is meaningful.** `one_time` and `kem_one_time` are
written in the store's order, and the reader keeps the order it read.
`create_prekeys` builds each list in ascending identifier order, and
`replenish` appends to the end. Consuming an entry moves the list's last entry
into its place and removes the last position, so after a consumption the order
is no longer identifier order. The order decides what a bundle names:

- `publish` names the last entry of `one_time`, or no one-time curve prekey
  (identifier `0`) when that list is empty; and the last entry of
  `kem_one_time`, or the last-resort KEM prekey when that list is empty. The
  two choices are independent, and every call returns the same bundle until a
  message consumes what it names.
- `publish_one_time_batch` returns one bundle per pair of entries taken from
  the ends of both lists together -- the last of each, then the second to last
  of each, and so on -- as many as the shorter list holds. Each names both
  one-time prekeys.
- `publish_multi_use` names no one-time curve prekey (identifier `0`) and the
  last-resort KEM prekey.

Every bundle names the current signed prekey and, when it names the
last-resort KEM prekey, the current one; never a key a rotation retired.

**Four versions are read; one is written.** The writer always emits `0x04`.
The reader also accepts `0x03`, the format before the record was tagged by
key, whose entries are bare fingerprints and read back tagged with the
current `kem_id`. That is the conservative reading: the fingerprint alone
decides whether a handshake is a repeat, since it covers the identifier, so
every replay the older store refused is still refused, and the only effect
of a wrong tag is that an entry made under the retired key is dropped one
rotation later than it need be. The reader further accepts `0x02`, the
format before rotation, which ends after `seen` and reads back with nothing
retired; and `0x01`, the format before the replay record, which ends after
`next_id` and reads back with no fingerprints remembered. Each is the honest
answer, since those stores recorded no more. A store written by this version
and read by an earlier one fails on the version byte, which is the intended
direction of incompatibility.

Two refusals are specific to this format's framing. A presence byte is
`0x00` or `0x01` and nothing else: a `previous_signed_present` or
`previous_kem_present` carrying any other value is malformed, not
"present". And a v4 store must re-encode to the identical bytes: having
decoded the input, the reader runs `to_bytes` over what it read and refuses
the input if the result differs. That is the canonicality backstop, the
same one `Session::import` applies to the session format: it refuses any
second spelling of a value that the field-by-field checks did not
enumerate, at the cost of one encode, and it is what makes the "canonical"
principle above a property of the decoder rather than a promise about the
writer. It applies only to the version the writer emits. A v1, v2 or v3
store re-encodes to v4, gaining the fields the newer format added and the
tags on its record, so comparing there would refuse every honest upgrade,
and those three versions are read on the semantic rules alone.

### Semantic rules

Last, over the decoded store, the reader refuses as malformed any store for
which `PrekeyStore::invariant` is false. The rules are the identifier
namespace and the record's shape, which `create_prekeys` establishes, every
operation preserves, and no field-by-field read sees; they apply to all four
versions, the untagged ones having had their entries tagged with the current
key first.

- **Every identifier is below `next_id`.** `next_id` only climbs and is what
  every identifier was handed out from; one at or past it is corruption or a
  counter wound back, and the next key handed out would collide with a live
  one. A corrupted `next_id` accepted here would poison every future bundle
  and persist canonically.
- **No identifier is zero**, the absent-identifier sentinel
  (message-format.md). `create_prekeys` numbers from one; a one-time prekey
  under zero could never be named by an initial message, which reads zero
  as "none".
- **Every identifier is distinct**: `signed_prekey_id`, `kem_id`, the
  identifiers inside `previous_signed` and `previous_kem`, and each one-time
  entry's of either kind, pairwise. The store finds keys by their first
  match, so a repeated one-time identifier serves a one-time prekey twice
  (key-deletion.md); a retired identifier equal to the live one has the next
  rotation drop the live key's record entries; a one-time KEM identifier
  equal to a last-resort one is looked up on the last-resort path and never
  consumed. One counter numbers them all, so distinctness across every kind
  is what the constructor establishes.
- **Every record entry is tagged with `kem_id` or the identifier inside
  `previous_kem`, no key has more than `MAX_LAST_RESORT_SEEN` entries**
  (CONSTANTS.md)**, and no fingerprint appears twice.** The bound is counted
  per key rather than over the record as a whole, so a store with both keys
  live may legitimately hold two full budgets, and a file holding more than
  one budget under a single key is refused however plausible its count.
  The responder refuses the handshake that would take a key past its budget,
  and the repeat of one already in the record, before either could be
  recorded; a rotation drops a key's entries when it wipes the key; so the
  writer never emits anything else. (The count is also refused before it
  sizes anything, as noted above; the rule here is over what was read, which
  is the only point at which the tags can be counted by.)

## Semantic rules of the leaf formats

Each leaf format's reader, having read every field, refuses as malformed a
state its crate's `invariant` is false of. The rules are these, and they are
all of them: a reader refuses a state that breaks one, and accepts every state
that keeps them all.

The rules are not a description of the states the operations produce. A state
can keep every rule and still be one no operation produces, and the reader
accepts it (ADR-0007). Two examples. A ratchet state may have `nr` above zero and no
receiving chain, or `ns` above zero and no sending chain, because no rule
constrains `ns`, `nr` or `pn`. A sparse ratchet state may hold a stored key
numbered 0, or numbered at or past its epoch's receiving counter, because no
rule relates a stored key's number to its chain.

- **Ratchet state.** The skipped store holds at most `MAX_SKIPPED_STORE` keys;
  the received-message clock `events` is below `u32::MAX`; no stored key's
  `stored_at` is later than `events`; no two stored keys share a ratchet key
  and message number; and a receiving chain key is present only if a sending
  chain key and the peer's ratchet public key are.
- **Sparse ratchet state.** The skipped store holds at most
  `MAX_SKIPPED_STORE` keys; every chains entry's epoch `e` satisfies
  `e <= epoch < e + EPOCHS_KEPT`, the sum saturating; no two entries share an
  epoch; the current `epoch` has an entry; every stored key's epoch has an
  entry; and no two stored keys share an epoch and message number.
- **Triple ratchet state.** Both ratchets satisfy their own rules; and while
  the classical ratchet still shows the role it started in -- a sending chain
  and no receiving chain for the sender, neither for the receiver -- the sparse
  ratchet's `direction` is `A2b` exactly when that role is the sender's.
- **Braid.** Every live state's `epoch` is at least 1, and every `header`,
  `ct1` and `ek_vector` has the length given above. In tags 1 to 4, the
  `header` and `ek_vector` that `key_pair` holds pass the validation a
  completed `ek_vector` passes against a received header (mlkem-braid.md, The
  KEM split): `H(ek_vector || rho)` equals the header's `H(ek)`, which is FIPS
  203 section 7.3's hash check made on the incremental key pair, whose
  decapsulation uses that `H(ek)`; and `ek_vector` passes section 7.2's
  modulus check. Every erasure coder
  satisfies its own rules below and is sized for the value it carries: the
  `hdr` coders for the header and a 32-byte MAC (96 bytes), the `ek` coders for
  1,536 bytes, the `ct1` coders for 1,408, and the `ct2` coders for the second
  ciphertext half and a MAC (192 bytes). An encoder is sized for `n` bytes when
  it holds `ceil(n / 32)` chunks, and a decoder when its `size` is `n`. `Failed`
  is always accepted.
- **Erasure encoder.** It holds at most `MAX_CODEWORDS` (65,536) chunks, and it
  is `exhausted` only when `next` is `u16::MAX`.
- **Erasure decoder.** `needed` is `ceil(size / 32)` and at most 65,536; it
  holds at most `needed` codewords; and no two share an index.

## Rejection

A decoder rejects, the same way message-format.md's does: an unrecognised
version, a buffer too short for its fixed fields or a declared length that
overruns the input, and trailing bytes after a value that should have
ended; and, having read every field, a state its type's `invariant` is
false of (the semantic rules above). Each of the formats above
carries its own error
type, distinguishing "wrong version" from "short or malformed" where a
caller might act on the difference (refuse to start vs. treat as corrupt),
the session and the prekey store distinguish "non-canonical" from both,
and the session distinguishes "inconsistent" as well, since a stored
session that is well-formed and canonical but cannot go on is the one case
a storage layer could plausibly have written itself -- but none of them
promises more than that the bytes were unacceptable, the same restraint
message-format.md's rejection section takes for a different reason: there,
because revealing more helps an attacker; here, because there is no finer
recovery a storage layer can attempt either way.

## Sources

Unlike every other page in this directory, this format has no published
specification to derive from: the Double Ratchet, PQXDH, and Triple Ratchet
documents specify protocol state and its use, not how an implementation
persists it between restarts. This page and the formats above are entirely
ours, following this project's own house style for such formats
(message-format.md), not translated or adapted from any other
implementation's on-disk representation.
