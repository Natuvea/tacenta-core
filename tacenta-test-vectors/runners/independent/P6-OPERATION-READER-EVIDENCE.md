# P6 independent operation-reader evidence

Jie Sun independently authored and ran
[`session-operation-reader.py`](session-operation-reader.py) from the
specification-only packet `p6-reader-packet-session-trace-v4`. The packet
manifest SHA-256 was
`b53df65f00ad03da4d19a3f4e2fd83e4c1b83faf7bbd5c863e8953f34e178439`.
The reader source SHA-256 at delivery was
`6dce0b6321125abd20ebbc5b302db55213d95b57cfb5a016a863c3ba81d9eae2`.

The independent record is retained in planning as
`p6-reader-packet-session-trace-v4/JIE-SUN-V4-RECORD.md`. It records a
renewed clean-room declaration, manifest verification and a Darwin
arm64/Python 3.9.6 run; its SHA-256 is
`4be190a449a58f92141fc674a54c6c8d8a69293d1e71b0326721580fcfa2501d`.

The reader evaluates the committed 27-trace, 41-step session/prekey corpus
from `tacenta-test-vectors/traces/session-operation-trace.json`. Its 36
ordinary steps passed. All five controls failed as required: the original
wrong durable effect and missing responder message, an incorrectly accepted
duplicate, a missing terminal-failure receive message, and an incorrectly
pending malformed initiator bundle. Every diagnostic cites the source rule.

This is independent evidence for the committed corpus only. It now covers the
nine agreed operation families, including ordinary and reordered receive,
terminal Braid failure and persistence, and initiator signature,
non-contributory-DH and malformed-bundle refusals. Cryptographic verdicts are
declared fixture facts rather than independently computed results. The
maintainer must still reassess the full L2 obligation set; a reader pass alone
does not raise the target or complete the later ledger review.
