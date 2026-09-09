# Key deletion

This page gathers, in one place, every secret the protocol requires a party to
delete and the moment it becomes deletable. It is our own description, written
from the published specifications named in Sources, and it is the reference the
Lean model and the Rust implementation are both written against.

The requirements are scattered across the source documents because each is
stated where the key is used. Collected, they are what forward secrecy actually
rests on: the protocol's guarantee is that a device compromised at one moment
does not expose messages from before it, and that guarantee is only as good as
the deletions below.

**Three key schedules run, not one.** Alongside the classical Double Ratchet a
session runs the sparse post-quantum ratchet
([sparse-pq-ratchet.md](sparse-pq-ratchet.md)) and the ML-KEM Braid
([mlkem-braid.md](mlkem-braid.md)) beneath it, each with its own secrets and
its own deletion points. They are covered below in their own right rather than
left to be inferred from the classical case.

## What must be deleted, and when

### During a session

| Secret | Deletable once |
| --- | --- |
| A message key | the message it protects is encrypted or decrypted |
| A chain key | the next chain key is derived from it |
| A root key | the next root key is derived from it |
| A ratchet private key | a Diffie-Hellman step has produced a new one |
| A skipped message key | its message arrives, or the store's policy expires it |

Each message is encrypted under a key used once, which is the point of the
symmetric-key ratchet: the key can go as soon as it has done its work. The old
chain key goes with it, because the new chain key has already been derived.

### During a session, the other two ratchets

| Secret | Deletable once |
| --- | --- |
| A sparse-ratchet chain key | the next chain key is derived from it |
| A sparse-ratchet root key | the next root key is derived from it |
| A sparse-ratchet skipped key | its message arrives, or its epoch is retired |
| A Braid decapsulation key | the encapsulation it was sampled for completes |
| The Braid's authenticator keys | the authenticator is updated for the next epoch |
| A Braid agreement output | the ratchet above has consumed it |

The shapes match the classical ratchet's, with one structural difference worth
naming: the sparse ratchet retires whole *epochs* rather than expiring
individual keys on a counter, so its skipped store empties in blocks. The
`EPOCHS_KEPT` bound is the policy choice there, in the same sense the classical
expiry interval is one.

### Establishing a session

The initiator, after deriving the shared secret `SK`, deletes its ephemeral
private key, the Diffie-Hellman outputs, and the KEM shared secret `SS`. Only
`SK` survives into the ratchet.

The responder, after deriving `SK`, deletes the Diffie-Hellman outputs and `SS`.
Then:

- if the initial message fails to decrypt, it aborts and deletes `SK`, leaving
  no session behind;
- if it decrypts, it deletes the private half of every one-time prekey the
  message named, curve and KEM alike.

That last deletion is what makes a one-time prekey one-time. Without it the key
is a standing prekey with a misleading name, and an attacker who later
compromises the device recovers the secret for a session recorded long before.

### Prekeys at rest

- One-time prekey private keys are deleted as they are used, above.
- After the signed prekey is rotated, the previous private key may be kept
  briefly, to handle messages already in flight that named it, and must then be
  deleted.
- The server deletes one-time prekeys as it hands them out, so that each is
  offered once. It prefers one-time KEM prekeys and falls back to the last-resort
  key only when they are exhausted. The server is outside this implementation,
  but a client that assumes otherwise will hold keys it should not.

### Skipped message keys

Storing keys for messages that have not arrived carries two risks the source
document names: a malicious sender can induce a recipient to store many of them,
consuming storage; and the messages may have been recorded by an attacker who
later compromises the recipient and recovers the stored keys.

The first is met by a bound on how many are stored. The second is met by
deleting them after an interval, triggered by a timer or by counting events.

## What this implementation does

- Keys are **superseded** at every point the first table requires: a message key
  is derived and returned rather than retained, a chain key is overwritten by
  its successor, and a root key by its successor. The state never holds a key
  the protocol says is spent.
- Long-lived private keys are zeroed when dropped, by the underlying curve and
  signing crates. So are the buffers that concentrate secrets during a
  derivation: the expansion buffers inside the key derivations, and the
  concatenation the handshake feeds to the KDF. The last of those has a
  qualification: the concatenation is built by appending to a growing buffer,
  and only the allocation alive at the end is wiped. The smaller blocks the
  buffer moved through as it grew are handed back to the allocator as they
  were, which is the "copies the allocator makes" case
  `tacenta-proofs/LIMITATIONS.md` describes. The session crate is a
  translated zone, so sizing that buffer up front is a change to the
  generated Lean and waits for the next re-translation window.
- The skipped store is bounded twice over, per chain and in total, and it is a
  map: storing a key for a pair already held replaces it rather than
  accumulating, so a superseded key cannot linger unreachable behind a newer
  one.
- A one-time prekey, curve or KEM, is removed from the store once the initial
  message that names it has authenticated, and not before. Naming a prekey is
  free to anyone who fetched the bundle, so a store that deleted on the way in
  could be drained by messages nobody could have written, rejecting legitimate
  initial messages already in flight and forcing every later peer onto the
  reusable last-resort key. So the responder reads the private halves it
  needs, derives `SK`, decrypts the initial ciphertext, and deletes only if
  that succeeded; a message that fails to authenticate leaves the store as it
  found it. The curve secret is zeroed in place before its slot is released.
- **The ratchet state erases itself when dropped.** `State` and the stored
  skipped keys carry an erasing destructor, so the root key, both chain keys,
  and every stored message key are wiped when the state goes out of scope, not
  merely superseded.

  The ratchet is the formally verified zone and an erasing destructor is a
  `Drop` implementation, but the translation ignores `Drop` entirely: the
  generated Lean is byte for byte identical with and without it.

  That is the thing to carry away. **The erasure is outside what the proofs
  see.** T1 and T3 say nothing about it, and would say exactly the same thing
  if the destructor were absent. A static check in the ratchet's tests fails
  the build if the derive is removed, which is the only guard there is; it is
  a much weaker instrument than the proofs standing next to it, and it should
  not be mistaken for them.
- **The sparse ratchet erases what it holds.** Its root key is wiped by an
  explicit destructor, and its chain keys, skipped keys, and agreement outputs
  each carry an erasing destructor of their own, so dropping the state wipes
  all of them.
- **The Braid erases every secret it holds**, by a different route worth
  naming, because looking for the usual one and not finding it is misleading.
  Neither `Braid` nor its state enum carries a destructor and neither derives
  an erasing one -- the erasure is in the *field types* instead. `Auth` derives
  it; `IncrementalKeyPair` is a boxed `Zeroizing` array, so the wipe reaches
  through the `Box`; `EncapsState` is a `Zeroizing` vector. The remaining
  fields of every state are the encapsulation key, the ciphertext halves, and
  the erasure coders carrying them, which are public wire material and are not
  secrets to erase.
- **Session establishment erases too.** `Identity`'s thirty-two byte secret
  and `PrekeyStore`'s signed-prekey secret, retired signed-prekey secret, and
  one-time curve secrets are wiped on drop -- the store by a hand-written
  destructor, because the KEM key pairs it also holds erase themselves on
  drop rather than implementing the trait a derived destructor would need
  from every field. `kem::KeyPair` holds its pair as an erasing byte buffer
  rather than in libcrux's own type, which does not implement erasure.
- **The handshake's Diffie-Hellman outputs and the KEM shared secret are
  erased.** All four agreement outputs and the encapsulated secret are held in
  erasing wrappers for the life of the derivation and wiped when it returns,
  at both the encapsulating and the decapsulating side.
- **Skipped keys are expired, by counting received messages.** A stored key is
  deleted once it has outlived a fixed number of them. Nothing in the ratchet
  can read a clock, so the source document's "a timer, or by counting events"
  resolves to counting: the state carries the count, each stored key carries the
  count at which it was stored, and every accepted receive ages the store and
  drops what has expired. The boundary is pinned on both sides, in the model and
  in the core, so a change to one that is not made to the other fails a test.

  Two things travel with it. The interval is a **policy choice**, not something
  the specification fixes: too small and a legitimate message delayed behind
  many others cannot be decrypted, too large and keys stay recoverable longer
  than they need to. And a peer who can drive receives can age a store out
  deliberately, causing a genuine delayed message to be lost. That peer can
  already fill the store, and the alternative is keys that never expire, so this
  is the better of two exposures rather than the removal of one.
- **One-time prekeys are replenished, and identifiers never repeat.**
  `PrekeyStore::replenish` adds fresh one-time keys of both kinds, and
  `one_time_remaining` is what a caller polls to decide when. Without
  replenishment a party has exactly as many first contacts with one-time
  forward secrecy as `create_prekeys` gave it, and every peer after that falls
  back to the last-resort KEM key with no one-time curve prekey -- sound but
  weaker.

  Identifiers are numbered per store, from one, so refilling by building a
  second store and combining it would produce duplicates. Both lookups take the
  *first* match, so a duplicate would mean removing one entry exposes another
  under the same identifier, and a replayed initial message naming it would be
  served twice -- precisely what a one-time prekey exists to prevent.
  `replenish` continues from the store's `next_id` rather than building
  anything, which makes the collision impossible rather than merely avoided,
  and a test pins that the identifiers a store hands out never repeat across a
  replenishment.
- **A replayed last-resort handshake is refused, and the record that refuses
  it never evicts.** A one-time KEM prekey defends itself by being deleted on
  use, so replaying a message that names one fails. The last-resort key is
  reusable by design and has no such defence of its own: without a record, a
  captured initial message naming it -- with no one-time curve prekey either,
  which is the steady state of a store whose one-time pools are exhausted --
  would be accepted again on every delivery, and each acceptance hands the
  application the initiator's first plaintext a second time, as the opening
  message of what looks like a fresh session. That is duplicate delivery, not
  only a denial of service: the attacker learns nothing and cannot speak on
  either session, but the same message is received twice and nothing marks
  the second as a repeat.

  The store therefore remembers a fingerprint of each last-resort handshake it
  has accepted, over exactly the fields that determine `SK`, tagged with the
  identifier of the last-resort KEM key the handshake was made against, and
  refuses a repeat (`ReplayedLastResort`). **The record is bounded per key
  lifetime, and it fails closed.** It holds at most `MAX_LAST_RESORT_SEEN`
  entries across the current key and the one the last rotation retired, and
  it never evicts: a last-resort handshake it has not seen, arriving while it
  is full, is refused (`LastResortRecordFull`) before anything is decrypted or
  changed, and the store is left exactly as it was. It was once a window,
  oldest evicted first, and a window is a count an unauthenticated peer can
  drive: anyone holding the public bundle can complete a last-resort handshake
  under a fresh identity in about a millisecond and a half, so 1024 of them
  evicted a chosen victim's fingerprint in about two seconds, after which the
  captured message replayed. What the bound measures now is how many distinct
  last-resort handshakes a key has accepted over its lifetime, not how many
  arrived recently. A key's entries leave the record when the key is wiped,
  which is the rotation after the one that retires it; until then a replay
  against the retired key is still a replay.

  The cost of a full record falls on the last-resort path only; a handshake
  naming a one-time KEM prekey never consults it. The operator has two levers:
  replenishment, which keeps first contacts off this path and is the one to
  reach for first, and rotating the last-resort KEM key, which releases the
  key's share of the record once the next rotation wipes it. The record
  persists with the store, tags included, so a restart neither reopens the
  window nor loses the pruning.
- **Signed prekeys rotate, and the retired one is kept for exactly one
  rotation.** `PrekeyStore::rotate_signed_prekey` generates a fresh curve
  prekey, signs it under the identity, and gives it the next identifier; the
  key it replaces becomes the store's *previous* signed prekey, with its
  identifier and signature, and is honoured by `establish_responder` for an
  initial message that still names it. That is the brief retention the
  first section allows for, and its end is the next rotation: when a second
  rotation moves another key into the previous slot, the one already there
  is zeroed and dropped. So the rotation cadence is the grace period, and
  the retention is bounded by construction rather than by a timer. Both
  the current and the previous secret are wiped when the store is dropped,
  and both persist with the store (session-persistence.md, Prekey store),
  so a restart neither loses the grace period nor extends it.

  `rotate_kem` does the same for the signed last-resort KEM prekey, with
  more at stake, since that key is reusable by design and its compromise
  reaches every last-resort handshake made under it. The retired KEM pair
  erases itself when the next rotation drops it. The last-resort replay
  record above follows the key: entries made under the retired key stay
  while it can still decrypt, since a handshake against it is a last-resort
  handshake still and a replay of one is refused on the same terms as
  against the current key, and they are dropped when the next rotation wipes
  it, at which point a message naming it fails on the identifier before the
  record is consulted.

  Three consequences are the caller's to manage. A bundle a peer fetched
  before the rotation names the retired identifier and still establishes,
  but only until the rotation after that, so a directory holding dispensed
  bundles must be restocked after every rotation and rotation must not run
  twice inside one directory refresh. The one-time secrets those stranded
  bundles named stay in the store unconsumed, harmless but idle. And the
  identifier space has an end: both rotations take their identifier from
  the store's counter, the one `replenish` draws from, and once that counter
  stands at `u32::MAX` each of `rotate_signed_prekey` and `rotate_kem`
  returns without rotating, silently, the same quiet refusal `replenish`
  makes at the end of the space. Every key the store ever issued spent one
  identifier, so reaching that point is not a practical concern; but a
  caller that must know a rotation happened should observe it
  (`PrekeyStore::next_id` advanced, or the published bundle's signed-prekey
  identifier changed) rather than assume it from the call having returned.
  The `rotate_signed_prekey` documentation in `tacenta-core` carries the
  first two warnings with their reasoning and names the third.

## What this implementation does not do yet

Stated plainly, because a deletion requirement that is documented but not
implemented is worse than one that is neither.

- **Copies inside libcrux's own types are not erased by this crate.**
  `libcrux-ml-kem` does not implement erasure, so where its API takes
  or returns its own types there is a copy nothing wipes. Our wrappers keep key
  material in erasing buffers and hand libcrux a reconstructed value per call,
  so the window is one call rather than the life of a store; it is not zero, and
  closing it needs a change upstream.

- **Persisting a session writes secrets to storage, deliberately.**
  `Session::export` ([session-persistence.md](session-persistence.md)) produces
  plaintext bytes carrying every key above. That is a deliberate exception to
  this page's guarantee: the erasure claims here are about memory, and
  at-rest protection of the exported blob -- disk encryption, or an encryption
  layer in the caller's own storage -- is the caller's stated responsibility.

- **Erasure covers values, not their copies.** A value that has been moved,
  cloned, or spilled by the optimiser is erased where the destructor can see it
  and not where it cannot. Erasing destructors reduce the window in which a key
  is readable; they do not close it, and no in-language mechanism does.

- **Rotation is not scheduled by this crate.** `rotate_signed_prekey` and
  `rotate_kem` exist and bound the retired key's life to one rotation, but
  nothing here decides when a rotation happens: there is no clock and no
  policy, and a caller that never rotates keeps one signed prekey for the
  life of the store. The published specification's "periodically" is the
  caller's obligation, and the retention bound above only means anything if
  the caller meets it.
- **Erasure is in-memory only.** Secrets are zeroed when dropped, which defeats
  an attacker who reads process memory afterwards. It says nothing about data
  recovered from storage media, which the source document places outside its own
  scope, and which no amount of zeroing in this process addresses. Any claim
  about deletion must be bounded that way.

  `Session::export`/`import` (session-persistence.md) is a deliberate,
  explicit exception to this boundary, not a quiet expansion of it: a caller
  that persists the exported bytes is choosing to hold session secrets on
  storage media, and protecting that copy at rest -- disk encryption, or an
  encryption layer in the caller's own storage code -- is that caller's job.
  The export format itself provides no encryption of its own.

## Sources

- Signal's published Double Ratchet specification (Trevor Perrin, editor;
  Moxie Marlinspike; Rolfe Schmidt), **revision 4, 2025-11-04**. Its security
  considerations give secure deletion, the deletion of skipped message keys with
  the two risks and their mitigations, and the deletion of old KDF chain state;
  the ratchet sections give the points at which message and chain keys become
  deletable.
- Signal's published PQXDH specification (Ehren Kret and Rolfe Schmidt),
  **revision 3, 2023-05-24, last updated 2024-01-23**. It gives the initiator's
  and responder's deletions on deriving the shared secret, including the KEM
  shared secret, the responder's deletion of used one-time prekey private keys,
  the retention and eventual deletion of a rotated signed prekey, and the
  server's handling of one-time keys including the last-resort fallback.
- Signal's published X3DH specification (Moxie Marlinspike; Trevor Perrin,
  editor), **revision 1, 2016-11-04**, for the same deletions in the
  pre-quantum handshake, and for aborting and deleting the shared secret when
  the initial ciphertext fails to decrypt.
