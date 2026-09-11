# Group messaging (sender keys)

In scope. Tacenta uses group messaging, and this outline assumes sender keys
as the mechanism (see the open questions below). This page is a placeholder
for work that is not yet scheduled, and will be written spec-first before the
model and core.

The mechanism, in outline: each member holds a sender key for the group (a chain
key that ratchets forward per message, plus a signing key so recipients can
authenticate the sender). A member shares its sender key with the others by
sending a sender-key distribution message over the one-to-one sessions. Group
messages are encrypted with the sender's current sender key and signed. When
membership changes, sender keys rotate into a new epoch so a removed member
cannot read later messages.

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
| WhatsApp, "WhatsApp Encryption Overview" (technical white paper, edition of 4 April 2016) | One deployment's description of sender keys, which it calls a component of the Signal Protocol: a chain key ratcheted per message, a signature key, a distribution message sent over the pairwise sessions, one ciphertext that the server fans out, and a reset when a member leaves. | A specification. It is a descriptive overview of another vendor's system, which Tacenta does not target, and it gives steps, not formats or derivations. |
| Balbás, Collins and Gajland, "WhatsUpp with Sender Keys? Analysis, Improvements and Security Proofs" (IACR ePrint 2023/1385; ASIACRYPT 2023) | A formal model of sender keys, a proof of the guarantees the protocol achieves (which the authors find weak), and an improved variant, Sender Keys+. | A wire format. |

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

## Open questions

These are to be settled in a decision record when the work is scheduled, not
assumed before then.

- **Sender keys or pairwise fan-out.** This outline assumes sender keys, but
  the only group mechanism Signal has published is fan-out. Fan-out reuses
  the one-to-one sessions unchanged, together with their post-compromise
  security and their proofs, at the cost of one encryption per member. Sender
  keys cost one encryption per message, but add a second key hierarchy, and
  the analysis above finds their guarantees weak.
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

Status: scaffold. Not yet scheduled.
