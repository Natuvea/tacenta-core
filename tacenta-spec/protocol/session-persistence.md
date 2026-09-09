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
  four-byte big-endian length ahead of it.
- **Versioned**, with its own version byte per format, in a namespace
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
       || pending_initial_present(1) || len(4) || pending_initial
       || established_ephemeral_present(1) || len(4) || established_ephemeral

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
            || previous_signed_present(1) || previous_signed              -- v3
            || previous_kem_present(1) || previous_kem                    -- v3

one_time        = id(4) || secret(32)
kem_one_time    = id(4) || len(4) || kem_pair || sig(64)
seen            = fingerprint(32)
previous_signed = secret(32) || id(4) || sig(64)      -- only when present
previous_kem    = len(4) || kem_pair || id(4) || sig(64)   -- only when present
```

`kem_pair` is `kem::KeyPair`'s own encoding, opaque here and length-prefixed
wherever it appears, as the Braid format treats it. `next_id` is the
identifier the next key added to the store will take, so that replenishment
continues the sequence rather than restarting it (key-deletion.md). `seen`
is the record of spent last-resort handshakes, oldest first, and a count
larger than the bound the store enforces (`MAX_LAST_RESORT_SEEN`,
CONSTANTS.md) is refused as malformed before it sizes anything. The two
`previous_*` fields are the signed prekey and the last-resort KEM prekey the
most recent rotation retired, each behind a presence byte and, like the
session's `pending_initial`, followed by nothing at all when absent.

**Three versions are read; one is written.** The writer always emits `0x03`.
The reader also accepts `0x02`, the format before rotation, which ends after
`seen` and reads back with nothing retired; and `0x01`, the format before the
replay record, which ends after `next_id` and reads back with no fingerprints
remembered. Both are the honest answer, since those stores recorded neither.
A store written by this version and read by an earlier one fails on the
version byte, which is the intended direction of incompatibility.

Two refusals are specific to this format. A presence byte is `0x00` or
`0x01` and nothing else: a `previous_signed_present` or
`previous_kem_present` carrying any other value is malformed, not
"present". And a v3 store must re-encode to the identical bytes: having
decoded the input, the reader runs `to_bytes` over what it read and refuses
the input if the result differs. That is the canonicality backstop, the
same one `Session::import` applies to the session format: it refuses any
second spelling of a value that the field-by-field checks did not
enumerate, at the cost of one encode, and it is what makes the "canonical"
principle above a property of the decoder rather than a promise about the
writer. It applies only to the version the writer emits. A v1 or v2 store
re-encodes to v3, gaining the fields the newer format added, so comparing
there would refuse every honest upgrade, and those two versions are read
on the field-by-field checks alone.

## Rejection

A decoder rejects, the same way message-format.md's does: an unrecognised
version, a buffer too short for its fixed fields or a declared length that
overruns the input, and trailing bytes after a value that should have
ended. Each of the formats above carries its own error type, distinguishing
"wrong version" from "short or malformed" where a caller might act on the
difference (refuse to start vs. treat as corrupt) -- but none of them
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
