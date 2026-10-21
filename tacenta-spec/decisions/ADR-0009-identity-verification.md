# ADR-0009: identity keys are checked against the party's records, and compared by a pair digest

## Status

Proposed.

## Context

- **What the pages left to the application.** EX-09 left identity
  verification wholly to it. REQ-AUTH-02 refused an unexpected identity only
  for an initiator that chose to name one. There was no common comparison
  value, no way to state a key the party no longer accepts, and no rule for
  which contact a session belongs to.
- **The identity-key rule was already in place.** identities-and-devices.md,
  Identity keys, refuses a key outside the prime-order subgroup at every
  session boundary: in a bundle, in an initial message and in stored state.
  It also fixed the initiator's order: the named identity, then the rule,
  then the signatures. Whether to refuse such keys in the protocol flows was
  therefore no longer open. What remained open was whether the new functions
  apply the rule.
- **`tacenta-core` has not changed yet.** It offers initiator establishment
  with a named key and without one, and has none of what this record
  decides. Until it changes, it does not conform to the pages this record
  amends.

## Decision

1. **One SHA-256 digest per unordered pair of identity keys,** under a fixed
   label. The keys are raw and sorted as unsigned bytes.
   - The digest applies the identity-key rule to both keys. Every key a
     session holds already passes it, so this refuses only keys typed,
     scanned or imported, and it means one key has one digest.
   - Keys only, and no identifier. A comparison is of keys, and what the keys
     belong to is the party's (ASM-14).
   - A 60-digit rendering is normative where digits are shown, so two
     implementations show the same number. Its bound is stated with the
     number of digits compared, because a partial comparison is much weaker.
2. **The initiator establishes only with an expectation.**
   - *Known*: the record of the contact she means to reach, which must be
     non-empty.
   - *First contact*: for a peer she holds no record for, carrying all her
     records. She goes on only when their lookup finds the key unattributed,
     so a recorded contact's key served under a new name is refused.

   A mandatory expectation leaves no establishment that skips the check.

   She refuses a malformed expectation before any check of Sending the
   initial message, because she must know her expectation before acting on
   it. She checks the bundle's identity key against her expectation after
   the bundle's presence and canonical-key checks, and before the
   identity-key rule, the signature checks, the KEM prekey's input checks
   and anything that draws randomness or computes an agreement. That is
   where the named identity was checked, so the order is kept. Nothing is
   spent on a key she already refuses. The check applies the identity-key
   rule to the key itself, so a key that fails the rule is refused for that
   reason whichever check meets it.
3. **Records belong to the party.**
   - A key is classified against a record, and looked up across records. A
     presented key is held to the identity-key rule, and a record's members
     only to the canonical encoding. A record holding a key an older release
     admitted then still works, and that key matches nothing.
   - A session, and everything it yields, is a contact's only when the lookup
     finds its peer key that contact's, against the records as they stand.
     Labels never select a record, since anything a bundle, message or
     transport supplies is the adversary's to choose.
   - Keys the lookup finds ambiguous or retired (*same* for no contact) are
     nobody's.
   - First contact gives an unattributed session in both roles.
   - The responder's establishment is unchanged. Its prekeys are consumed
     once a message authenticates, and the specification keeps that.
4. **The library keeps no record.** This specification defines no peer
   addressing, and the record's integrity belongs with the application's
   other storage.

## Rejected

1. **A role-ordered digest.** The two sides would compute different bytes,
   and simultaneous initiation would leave the roles undefined.
2. **Other sort orders**, such as by numeric value. Each is valid, but only
   one can be chosen. Raw bytes match how every stored key is used.
3. **`EncodeEC` input.** It adds a constant byte to both keys and changes
   nothing.
4. **Normalising keys.** It would give one number to two byte strings that
   every other comparison treats as different, against the single-encoding
   principle.
5. **A digest that accepts any canonical key.** It would give digests for
   keys no session can hold, and two digests for one key's spellings. The
   identity-key rule removes both.
6. **An identifier in the digest.** This specification defines none.
   Revisit with key transparency.
7. **Stretching.** At 60 digits the margin is about 2^100 without it, and it
   would cost every comparison.
8. **Digits left to applications.** Numbers would differ between
   implementations.
9. **A library-held record.** This specification defines no peer
   addressing, and the record's integrity is excluded by analogy with EX-07.
10. **A "changed" session status.** It would be one more state for a session
    to keep, and attribution by lookup already says what changed.
11. **A responder refusal after authentication.** By then the prekeys are
    consumed, so the refusal would discard a handshake nobody can repeat.
    Keeping one-time KEM prekeys alive behind a prompt works against forward
    secrecy.
12. **A responder refusal before authentication.** Every forged or replayed
    initial message would surface as a key change, which is a lever for
    social engineering.
13. **Agreement-class comparison.** An identity key has one spelling, so
    bytes decide, and bytes are what every other check compares.
14. **An optional expectation.** A second implementation could skip it and
    still conform, which makes the requirement empty.
15. **Refusing an overlapping record.** *Retired* taking precedence is
    simpler and fails closed.
16. **A specified record-update function.** How a record changes depends on
    the application's use of devices (EX-09).
17. **An evidence input that the pages ignore.** No state distinguishes it,
    so it could not be tested.
18. **Key-continuity statements** (deferred). They do nothing on device
    loss, and a stolen old key signs for the attacker.
19. **A record chosen by label.** A label is the adversary's to choose.
20. **Discarding as a specified outcome.** Whether to keep a session is the
    party's, and discarding consumes the handshake.
21. **A specified record byte format.** The record is the application's.
22. **Inventory statements as an authority over records.** A statement the
    directory issues proves no more about whose key it is than a bundle does
    (ASM-14).
23. **First contact for a peer with a record.** It would let a recorded
    contact's key be served under another name.
24. **First contact that refuses nothing, or that classifies against unions
    as one record.** The first misses keys she has recorded. The second
    loses which contact a key belongs to, and so whether it is retired or
    current.
25. **A label as a tiebreak for an ambiguous key.** It is the adversary's to
    choose.
26. **Attribution fixed at establishment.** A key retired later would go on
    being attributed.
27. **A first-match classification.** It would leave a malformed member
    undetected, depending on member order.
28. **Refusing a whole responder lookup for one malformed record.** The
    responder cannot refuse a message it has accepted, so the lookup skips
    the record and reports it instead.
29. **Refusing *known* when its key is also current in another record.** It
    would couple every establishment to every record. The directory cannot
    bring the overlap about, since only the party's own records can hold it
    (ASM-14).
30. **A membership callback for first contact.** Every key in the records
    has to be checked for canonical encoding before the bundle is, and a
    callback cannot promise that.
31. **Attribution at the time a plaintext arrives.** It keeps history, but it
    leaves the messages between a key's theft and its retirement attributed.

## Consequences

- **What `tacenta-core` will change.** It will drop initiator establishment
  without an expectation, and provide the classification, the lookup and the
  digest. Until then it does not conform to these pages.
- **Attribution follows the records as they stand.** A record change
  re-attributes past plaintexts. An application may show a plaintext as
  having been a contact's when it arrived.
- **Recommended records policy** (non-normative):
  - record a key after the people compare the verification number;
  - treat adding a device's key with the scrutiny of a replacement, since an
    accepted ghost key stays current and its later bundles establish
    silently;
  - move a lost, stolen or removed key to retired, rather than deleting it,
    so an emptied contact does not become a first contact again. Reach a
    contact whose keys are all retired under *known*, after recording a new
    key, never under first contact;
  - to re-accept a retired key, remove it from retired, never as an ordinary
    key-change prompt;
  - never fill a record from an inventory statement;
  - show a session that is no contact's, whose label names a contact, as
    "unknown, claims to be X".
- **`KeyEvidence`.** `tacenta-core` will reserve `KeyEvidence`, a type with
  no public constructor, in its API only. Giving it a constructor would add a
  check and a refusal, so it would be a specification-first change (ADR-0006
  point 3).
- **Stretching** was not adopted. Reopen it with the digit count if the
  margin is raised.
- **Reopen** for key transparency or key-continuity statements.
