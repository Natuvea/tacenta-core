# P6 operation-reader evidence (related party, specification-only)

Jie Sun, a director of Natuvea Ltd and so a related party rather than an
independent one, wrote and ran
[`session-operation-reader.py`](session-operation-reader.py) from the
specification-only packet `p6-reader-packet-session-trace-v4`. The packet
manifest SHA-256 was
`b53df65f00ad03da4d19a3f4e2fd83e4c1b83faf7bbd5c863e8953f34e178439`.
The reader source SHA-256 at delivery was
`6dce0b6321125abd20ebbc5b302db55213d95b57cfb5a016a863c3ba81d9eae2`. The
committed file was changed later (#202) and no longer has that hash.

Jie Sun's record of that run is kept outside this repository as
`p6-reader-packet-session-trace-v4/JIE-SUN-V4-RECORD.md`. It records a
renewed clean-room declaration, manifest verification and a Darwin
arm64/Python 3.9.6 run; its SHA-256 is
`4be190a449a58f92141fc674a54c6c8d8a69293d1e71b0326721580fcfa2501d`.

Maintainer's note, 2026-11-19. The three SHA-256 values above were
recomputed on that date from the files kept in the project's private
records, and each matches the value recorded here. The reader as delivered
is identical to the file first committed here. The packet manifest lists 55
files; 54 of them match their listed hashes, and the trace corpus does not:
the corpus now kept with that packet has 27 traces and differs from
the one the manifest lists, and the corpus committed here differs from both.
So a match with the record's hash does not establish that the packet as it
stands today is the packet as manifested. The record does not state where
the reader's outputs were written, any exposure after the run, or any
context not retained, and it does not state what other context was in view at
the start of the work: it names the packet, the brief, the author's earlier
reader and earlier rounds, and declares in general terms that no excluded
source was consulted. The
record is kept privately and is not published here. This check was made by
the maintainer with tool assistance; it is project-controlled and is not an
independent review. Nothing was reconstructed.

The reader evaluates the committed 27-trace, 41-step session/prekey corpus
from `tacenta-test-vectors/traces/session-operation-trace.json`. Its 36
ordinary steps passed. All five controls failed as required: the original
wrong durable effect and missing responder message, an incorrectly accepted
duplicate, a missing terminal-failure receive message, and an incorrectly
pending malformed initiator bundle. Every diagnostic cites the source rule.
The corpus's `source` string was relabelled on 2026-10-28 ("independent
clean-room author" to "specification-only author (related party)"); no trace,
step or control changed.

This is related-party, specification-only evidence for the committed corpus
only; it is not independent review. It now covers the
nine agreed operation families, including ordinary and reordered receive,
terminal Braid failure and persistence, and initiator signature,
non-contributory-DH and malformed-bundle refusals. Cryptographic verdicts are
declared fixture facts rather than independently computed results. The
maintainer must still reassess the full L2 obligation set; a reader pass alone
does not raise the target or complete the later ledger review.
