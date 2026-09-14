# Group messaging (sender keys)

In scope. Tacenta uses group messaging, and this outline assumes sender keys
as the mechanism (see the open questions below). Most of this page remains a
placeholder for work that is not yet scheduled. The bounded fan-out commitment
helper below is an explicit exception: it is specified first for the product's
one-authority validation profile, without selecting a sender-key mechanism.

The mechanism, in outline: each member holds a sender key for the group (a chain
key that ratchets forward per message, plus a signing key so recipients can
authenticate the sender). A member shares its sender key with the others by
sending a sender-key distribution message over the one-to-one sessions. Group
messages are encrypted with the sender's current sender key and signed. When
membership changes, sender keys rotate into a new epoch so a removed member
cannot read later messages.

## Bounded fan-out commitment helper (version one)

This section specifies the standalone core helper used by the bounded
one-authority, one-device-per-identity fan-out experiment. It is not a group
cipher, a membership protocol, a wire envelope, or a production group profile.
The product validates and canonically encodes rosters, invitations and
application contexts. This helper only binds those already validated bytes to
fixed, distinct SHA-256 domains.

`roster_commitment(preimage)` is the 32-byte SHA-256 digest of:

```text
"Tacenta:group:roster-commitment:v1\xff" || preimage
```

`preimage` is exactly the product's canonical roster preimage in its bounded
group roster contract: it begins with `"Tacenta Group Roster v1"`, and contains
the framed group ID, revision, predecessor digest, authority binding, policy,
closed field and sorted member bindings. The helper neither parses this value
nor supplies defaults. A caller must refuse a malformed or noncanonical roster
before calling it; different byte strings always receive independently computed
digests, even when a product considers both malformed.

`payload_commitment(context)` is the 32-byte SHA-256 digest of:

```text
"Tacenta:group:payload-commitment:v1\xff" || context
```

`context` is exactly the product's canonical authenticated application context:
it begins with `"Tacenta Group Application v1"` and contains the framed group,
revision, roster digest, sender/device, recipient/device, logical sequence and
payload. The pairwise layer authenticates this context as plaintext; this helper
does not change pairwise associated data or establish peer identity.

Both labels and the SHA-256 primitive are Tacenta choices (`ours`). The labels
are prefix-free, end in `0xff`, and appear in the label registry and constant
ledger. The digest length follows SHA-256. The product must record the returned
commitments with the exact preimages they bind and must not replace the helper
with an ad hoc product hash.

The helper has no secret input and does not make a collision-resistance claim
beyond the SHA-256 assumption already named by the core threat model. It gives
the product stable domain separation, not membership authenticity, delivery,
privacy, or removal guarantees.

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

Status: the bounded fan-out commitment helper is specified and scheduled; the
sender-key/group-protocol outline remains scaffolded and unscheduled.
