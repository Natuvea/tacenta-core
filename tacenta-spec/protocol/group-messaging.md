# Group messaging (sender keys)

In scope. Tacenta uses group messaging, and this outline assumes sender keys
as the mechanism (see the open questions below). Most of this page remains a
placeholder for work that is not yet scheduled. The bounded fan-out commitment
helper below is an explicit exception: it is specified first for the product's
one-authority validation profile, without selecting a sender-key mechanism.

A draft of signed group membership epochs is in group-epochs.md. It is not
ratified and has had no human review. It does not select a cipher or a
sender-key format, and it assumes that each accepted epoch starts a key epoch
(its Open decision D-2), which the open question below on sender keys or
pairwise fan-out does not assume. It lists several authorities and up to eight
devices per account, a different profile from the one-authority,
one-device-per-identity profile of the bounded fan-out helper below.

The mechanism, in outline (tier `nominated`: this is the shape of sender keys
that WhatsApp's white paper describes, listed under Published material): each
member holds a sender key for the group (a chain key that ratchets forward per
message, plus a signing key so recipients can authenticate the sender). A
member shares its sender key with the others over the one-to-one sessions.
Group messages are encrypted with the sender's current sender key and signed.
When membership changes, the sender keys are replaced so a removed member
cannot read later messages. The outline fixes no byte, label, constant,
derivation or state, and it is not a design decision: a decision record
settles the mechanism when the work is scheduled.

## Bounded fan-out commitment helper (version one)

This section specifies the standalone core helper used by the bounded
one-authority, one-device-per-identity fan-out experiment. It is not a group
cipher, a membership protocol, a wire envelope, or a production group profile.
The product validates and canonically encodes rosters, invitations and
application contexts. These helpers only bind those already validated bytes to
fixed, distinct SHA-256 domains.

`roster_commitment(preimage)` is the 32-byte SHA-256 digest of:

```text
"Tacenta:group:roster-commitment:v1\xff" || preimage
```

`preimage` is exactly the product's canonical roster preimage in its bounded
group roster contract. The helper neither parses this value nor supplies
defaults. A caller must refuse a malformed or noncanonical roster before
calling it.

`payload_commitment(context)` is the 32-byte SHA-256 digest of:

```text
"Tacenta:group:payload-commitment:v1\xff" || context
```

`context` is exactly the product's canonical authenticated application
context. The pairwise layer authenticates this context as plaintext; this
helper does not change pairwise associated data or establish peer identity.

Both labels and the SHA-256 primitive are Tacenta choices (`ours`). The labels
are prefix-free, end in `0xff`, and appear in the label registry and constant
ledger. The product must record the returned commitments with the exact
preimages they bind and must not replace the helper with an ad hoc product
hash. The helper gives domain separation, not membership authenticity,
delivery, privacy or removal guarantees.

## Published material

No Signal specification covers group messaging. Signal's specifications are
XEdDSA and VXEdDSA, X3DH, PQXDH, the Double Ratchet, Sesame and the ML-KEM
Braid, and none of them describes groups, sender keys or group membership.
What has been published is less than a specification, and each item covers a
different part of the problem.

| Source | What it covers | What it does not cover |
|---|---|---|
| Signal, "Private Group Messaging" (blog post, 5 May 2014) | Groups as pairwise fan-out: each message is encrypted to each member over the one-to-one sessions, and a large attachment is encrypted once under a fresh key that is then sent pairwise. Group management travels in pairwise messages, so the server holds no group state. | Sender keys. The post describes the alternative, and gives no wire format or derivation. |
| Signal, "Technology Preview: Signal Private Group System" (blog post, 9 December 2019); Chase, Perrin and Zaverucha, "The Signal Private Group System and Anonymous Credentials Supporting Efficient Verifiable Encryption" (IACR ePrint 2019/1416; ACM CCS 2020) | Group state and membership, stored by the server encrypted. Members authenticate with keyed-verification anonymous credentials, so the server enforces access control without learning who is in a group. | Encrypting messages to the group. |
| WhatsApp, "WhatsApp Encryption Overview" (technical white paper, edition of 4 April 2016) | One deployment's description of sender keys, which it calls a component of the Signal Protocol: a chain key ratcheted per message, a signature key, the sender key sent to the other members over the pairwise sessions, one ciphertext that the server fans out, and a reset when a member leaves. | A specification. It is a descriptive overview of another vendor's system, which Tacenta does not target, and it gives steps, not formats or derivations. |

RFC 9420, The Messaging Layer Security (MLS) Protocol (IETF, July 2023), is
named here because it is published work on group messaging. It is not one of the
sources in the table above, and this page states nothing about what it covers or
how it relates to this outline. This project's design has not been compared with
it, and a comparison is required before the key engine is fixed.
group-epochs.md, Related published work, says the same of its signed membership
epochs.

## Provenance rules for this page

- No Signal document specifies sender keys, so no mechanism detail on this
  page can be tier `fact` on Signal's authority (CONSTANTS.md). A detail
  taken from the white paper or a paper above is at most `nominated` until it
  is derived independently or verified. Anything else is `ours`. Each fact
  cites its source.
- Before a published description is used, check what its authors based it
  on. A description reconstructed from another implementation's source is
  derived material under the clean-room boundary, wherever it is published.
- Wire-level details needed for interoperability, if any, come from black-box
  research under the interoperability boundary (ADR-0003), never from another
  implementation's source.

## What this page rests on

- The bounded fan-out commitment helper is `ours`.
- The mechanism outline at the top is `nominated`, on WhatsApp's white paper
  (Published material), and it is the only item the outline is cited to. The
  white paper's authors are the operator of the deployment it describes. What
  the document itself was based on has not been checked (second rule above),
  so the outline is not treated as more than `nominated`.
- The open questions are questions, not choices. Where one says what a
  published item covers, that comes from the item's row under Published
  material: the fan-out description from the 2014 post, and the Private Group
  System's scope from the 2019 post and paper. The paper named in the last open
  question has no row; it is cited only for the layer it says it addresses.
- No wire detail, label, constant or derivation on this page is taken from any
  of these items.
- The repository records no check of what any item under Published material, or
  the paper named in the last open question, was based on beyond who wrote it,
  and records no finding that any of them was based on another
  implementation's source.

## Open questions

These are to be settled in a decision record when the work is scheduled, not
assumed before then.

- **Sender keys or pairwise fan-out.** This outline assumes sender keys, but
  the only group mechanism Signal has published is fan-out. Fan-out reuses
  the one-to-one sessions unchanged, together with their post-compromise
  security and their proofs, at the cost of one encryption per member. Sender
  keys cost one encryption per message, but add a second key hierarchy whose
  guarantees this project would have to state and prove itself.
- **Membership privacy against the server.** The Private Group System is a
  separate layer from message encryption. Whether Tacenta needs it is
  undecided.
- **Post-quantum security.** A sender key distributed over the one-to-one
  sessions inherits their post-quantum confidentiality in transit. The
  signature that authenticates each group message does not, unless the
  signing scheme is itself post-quantum. The Private Group System's
  credentials are likewise classical; "A Quantum-Safe Private Group System
  for Signal from Key Re-Randomizable Signatures" (IACR ePrint 2026/453)
  addresses that layer.

Status: the bounded fan-out commitment helper is specified and scheduled; the
sender-key/group-protocol outline remains scaffolded and unscheduled.
