# Group messaging (sender keys)

In scope. Tacenta uses group messaging, so sender keys are part of the
implementation. This page is a placeholder for the M4
slice and will be written spec-first before the model and core.

The mechanism, in outline: each member holds a sender key for the group (a chain
key that ratchets forward per message, plus a signing key so recipients can
authenticate the sender). A member shares its sender key with the others by
sending a sender-key distribution message over the one-to-one sessions. Group
messages are encrypted with the sender's current sender key and signed. When
membership changes, sender keys rotate into a new epoch so a removed member
cannot read later messages.

## Provenance note

Unlike the Double Ratchet and the agreement protocols, Signal does not publish a
formal specification document for sender keys. This page will therefore derive
from Signal's public descriptions of private group messaging, and the wire-level
details required for interoperability will be determined by black-box research
under the interoperability boundary (see the decision records), never from
another implementation's source. Each fact will cite what it derives from.

Status: scaffold. To be written in M4.
