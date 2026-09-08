# tacenta-spec

The protocol and security specification, written as prose.

The plain-language definition of the protocol (X3DH / PQXDH agreement, the
Double Ratchet, prekeys) and the security properties it must hold. Derived from
the public Signal specifications, it is the source that the model, proofs, and
implementation are all written against.

Status: eight written protocol pages cover everything the engine runs:
session-establishment.md (PQXDH), ratchet.md (the classical Double Ratchet),
sparse-pq-ratchet.md and mlkem-braid.md (the post-quantum ratchet and the
agreement beneath it), triple-ratchet.md (their composition), message-format.md,
key-deletion.md, and session-persistence.md; post-compromise-security.md is the
one written security-property page. group-messaging.md is an outline ahead of
the code (milestone M4). Every other page in protocol/, threat-model/ and
security-properties/ is a scaffold -- a title and a one-line scope, marked
"Status: scaffold" -- kept as the table of contents for what is still to be
written. Until a scaffold is written, the code, the model, and
tacenta-proofs/CLAIMS.md and LIMITATIONS.md are the record for that topic.

[CONSTANTS.md](CONSTANTS.md) records every constant this engine emits or
accepts with the source that authorises it, at one of three tiers; every
constant the engine emits or accepts is required to have an entry there.
[CHANGELOG.md](CHANGELOG.md) tracks
changes to the specification, versioned against the protocol rather than the
implementation.
