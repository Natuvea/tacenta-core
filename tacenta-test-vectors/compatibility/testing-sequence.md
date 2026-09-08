# Testing sequence

The order to build up interoperability confidence, weakest assumptions first.
Against a third-party peer only the bundle layer is in scope (ADR-0004); the
message-layer steps below run Tacenta against Tacenta.

1. **Known-input differential.** Where the public interfaces permit controlled
   keys and randomness, feed both implementations identical inputs and compare
   outputs. Useful for the derivations that are meant to be deterministic; not
   applicable where randomness cannot be pinned.

2. **Cross-decryption.** The core interoperability test. Tacenta encrypts,
   the peer decrypts; the peer encrypts, Tacenta decrypts. Do not require
   identical ciphertext, only mutual decryptability.

3. **Stateful transcript.** Exchange many messages across an established
   session, including loss, reordering, duplication, and simultaneous sends,
   and assert both sides stay in step.

4. **Version matrix.** Run the suite against several pinned libsignal builds,
   and report results per version. A pass is a pass against a named version, not
   a universal claim.

5. **Property tests.** Assert behavioural properties (decryptability, ordering,
   forward progress of the ratchet, rejection of bad input) rather than byte
   equality, except where an encoding must be canonical.

6. **Negative tests.** Corrupt headers, MACs, keys, counters, and encodings, and
   compare the externally observable outcomes. The goal is predictable,
   matching failure behaviour, not a shared error string.

Every experiment that resolves a specification gap is written up as a research
record.
