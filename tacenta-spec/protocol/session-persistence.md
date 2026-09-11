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
- **No new abstraction leak.** The Braid's eleven live internal states are
  not named or exposed by this format: it can only be exported and imported
  whole, the same restriction callers already have on a live `Braid`.
- **Validated, not only parsed.** A decoder that reads every field
  correctly can still hand back a state no constructor builds: a ratchet
  private key beside a public key that is not its own, an epoch pair the
  sparse ratchet cannot follow, an identifier namespace with a collision in
  it. Each such state re-encodes to the bytes it came from, so the canonical
  principle above does not see it, and none fails at import -- each fails on
  some later message, the first two for good. So each type carries an
  `invariant`, the relations between its fields that its constructors
  establish and its operations preserve, and its decoder calls it last and
  refuses on it. The rules for the session and the prekey store are listed
  below, under "Semantic rules"; the leaf formats' rules are each crate's own
  `invariant`, which this page does not yet restate. They are checked as an inductive invariant: the tests and the fuzz
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
(`0x00` today, for the sole `Tacenta` set).

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

## Braid

```
braid = version(1) || state_tag(1) || fields...
```

`state_tag` is the same stable 0-11 numbering `Braid::state_tag` already
reports (`mlkem-braid.md`'s eleven live states, plus `Failed`, for twelve
tags in total). Each tag's fields
are that state's own, in declaration order; every variable-length field
(`Vec<u8>`, and each sub-format's own encoding: the KEM key pair, the
erasure codec's encoder/decoder state, the encapsulation state) is wrapped
`len(4) || bytes`, so a sub-format's own decoder always sees exactly the
slice it produced and nothing else. `Auth` (the Ratcheted Authenticator) is
its two 32-byte keys back to back, 64 bytes, no presence tag: every live
state carries one. `Failed` carries no fields at all.

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
  the initiator. The classical ratchet shows its role only until its first
  Diffie-Hellman step, and the Triple Ratchet's own invariant checks it
  against the sparse ratchet's while it can.
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
  these already, so at import this is a second reading.

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

`kem_pair` is `kem::KeyPair`'s own encoding, opaque here and length-prefixed
wherever it appears, as the Braid format treats it. `next_id` is the
identifier the next key added to the store will take, so that replenishment
continues the sequence rather than restarting it (key-deletion.md). `seen`
is the record of spent last-resort handshakes, oldest first; from v4 each
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

## Rejection

A decoder rejects, the same way message-format.md's does: an unrecognised
version, a buffer too short for its fixed fields or a declared length that
overruns the input, and trailing bytes after a value that should have
ended; and, having read every field, a state its type's `invariant` is
false of (the semantic rules above; the leaf formats' own predicates are
each crate's to state). Each of the formats above carries its own error
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
