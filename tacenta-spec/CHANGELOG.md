# Changelog

All notable changes to the specification. Format: Keep a Changelog; the version
is SemVer against the specified protocol (not the implementation).

## [Unreleased]

### Added
- `protocol/sparse-pq-ratchet.md`: the Sparse Post-Quantum Ratchet, written from
  the published Double Ratchet specification revision 4, Section 5. Specified
  generically over a sparse continuous key agreement, which is treated as a
  boundary in the same way Diffie-Hellman is.
- `protocol/triple-ratchet.md`: the composition of the two message ratchets,
  from Sections 6 and 7.1. Both produce message keys; the encryption key is
  derived from the pair, so an attacker must break both assumptions.
- `protocol/mlkem-braid.md`: the ML-KEM Braid, the sparse continuous key
  agreement the Sparse Post-Quantum Ratchet is specified over. Eleven live
  states plus a terminal failure; the `Ct1Ack` message type is not produced by
  this implementation and is rejected by its decoder.
- `protocol/session-persistence.md`: the bytes a storage layer writes to save a
  `Session` and reads back to restore one. The only page here with no published
  specification behind it -- the Double Ratchet, PQXDH, and Triple Ratchet
  documents specify protocol state and its use, not how an implementation
  persists it between restarts. Entirely ours.

### Changed
- `protocol/ratchet.md`: **the post-quantum ratchet is in scope.** Post-quantum
  protection at session establishment alone does not carry across a session's
  life: the handshake protects a session when it is created and adds nothing
  afterwards, so against an attacker recording traffic for a future quantum
  computer, a long-lived session would be protected by the handshake alone and
  by nothing the ratchet does. Signal's current specification ratchets
  post-quantum continuously, and so does this one -- see the note below.

  The Double Ratchet page itself is otherwise unchanged, and stays that way: the
  composition uses it unaltered.

### Decided
- Old epochs are retired by keeping chains for a bounded number of epochs, the
  approach in the specification's main text, rather than by sealing chains with
  a carried chain length. The second approach leaves the skipped-key store
  unbounded and requires the implementation to supply its own bound, which the
  specification warns about explicitly. We have had to build exactly that
  mechanism for the Double Ratchet; there is no reason to import the problem
  here in order to reuse the solution.

### Note
**Specified and implemented.** The Triple Ratchet and the Braid are integrated
into `Session`: `tacenta-spqr`, `tacenta-braid`, and `tacenta-triple` all ship,
all carry T1 panic-freedom and T3 refinement proofs, and the composite header
carries the agreement's message on every send. The conformance manifest records
the per-component state and is the reference for current coverage.
