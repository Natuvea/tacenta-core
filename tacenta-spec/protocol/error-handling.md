# Error handling

What the protocol requires when an input is refused, and what it leaves to an
implementation.

## What is required

- **Every refusal a page states is required.** An implementation that accepts
  what a page says to refuse does not conform, however it reports the refusal.
  Where a page also says the refusal leaves state unchanged, that is required
  too.
- **Decode failure and authentication failure are different outcomes**
  (message-format.md, Rejection). A decoder refuses bytes that are not a
  canonical encoding. Authentication refuses a well-formed message whose tag
  or signature does not verify. A peer learns neither which one happened nor
  why.
- **An invalid identity key is a third outcome.** A well-formed input that
  names an identity key the identity-key rule refuses is neither a decode
  failure nor an authentication failure: it decoded, and no signature failed
  (identities-and-devices.md, Identity keys). An implementation reports it as
  its own refusal wherever it can, and where a boundary can only say yes or no,
  such as a verifier of an application signature, it says no. A key that is not
  canonical is refused as it always was: as a decode failure where a wire
  encoding is read, and by the kind the stored state's page names for it.
- **A stored state's refusal says which kind it is**, to the extent
  session-persistence.md's Rejection section names kinds: wrong version, short
  or malformed, non-canonical, and, for a session, inconsistent or, for a prekey
  store, incoherent. A storage layer
  can act on those. A stored key that is not an identity key is refused as
  inconsistent in a session and as malformed in a prekey store.
- **Conditions a caller must act on are named** by the page that defines them.
  The last-resort handshake pages name three: a replayed handshake, a replay
  record with no room for the key a handshake names, and a pre-v5 replay record
  that cannot be compared with the v5 `SK`-bound identity. The last of these
  fails closed until the affected last-resort key is rotated
  (session-establishment.md, key-deletion.md). session-establishment.md names
  a third: an initial message that an existing session refuses as not a
  repeat of the one that established it (`NotARepeatedInitial`), after which
  establishing a new session from the message is the caller's decision
  (Receiving the initial message). An agreement that has failed is reported
  as failed (mlkem-braid.md).

## What is left to an implementation

- **The error types.** The set of variants, their names and payloads, and
  which variant reports a given refusal, beyond the kinds above. The variants
  `tacenta-core` exposes are its API, documented with its crates, and are not
  part of this specification.
- **The order of checks.** When an input fails more than one check, which
  refusal is reported, unless a page fixes an order because the order is
  observable in a way that matters.

## Why the line is here

A second implementation has to refuse what this one refuses and accept what it
accepts. It does not have to report refusals in the same words. Making error
variants normative would make an API shape part of the protocol, which the
project deliberately keeps independent (ADR-0003). It would also bind every
implementation to one check order, which no page needs.

What a peer can learn is a separate question, answered where it arises: on the
wire, message-format.md's Rejection section. Distinguishing refusals in a local
error type does not reveal them to a peer, provided nothing on the wire depends
on the distinction.
