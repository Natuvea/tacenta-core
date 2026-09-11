# tacenta-core

One implementation of the Tacenta specification (`../tacenta-spec`), in
Rust. The specification is normative and this crate is not: where the two
disagree, this crate is wrong until the specification is amended, and a
behaviour change starts in the specification
(`../tacenta-spec/decisions/ADR-0006-specification-is-normative.md`). The
specification builds on the same published protocols that libsignal
implements, so this is also an independent implementation of those.

Implemented clean-room from ../tacenta-spec and ../tacenta-model, never from
libsignal's source. Cryptography only: no product coupling, usable by any
caller. It is not yet packaged for installation from a registry. A fresh
implementation, not a port.

tacenta-core and Tacenta are not affiliated with, endorsed by, or sponsored by
Signal Messenger LLC or the Signal Foundation. "Signal" and "libsignal" are used
only to name the published protocols and the third-party software they refer to.

Status: the implementation is live. What ships: PQXDH session establishment, the classical Double Ratchet, the sparse
post-quantum ratchet and the ML-KEM Braid beneath it, their composition as the
Triple Ratchet, the wire and storage formats, and a protobuf profile. Seven
crates carry T1 panic-freedom and T3 refinement proofs (the erasure crate's T3
covers its field arithmetic only, not the encoder or decoder; the Braid's T3
takes a liveness and an unspliced-stream precondition besides its boundary
assumptions; the Triple's T1 is conditional on totality assumptions no leaf
theorem discharges); see
`../tacenta-proofs/CLAIMS.md` for the ledger and `../tacenta-proofs/LIMITATIONS.md`
for what is not covered.

Not built: group messaging and sender keys (not yet scheduled), and a storage
layer, each recorded where it matters rather than only here. Signed-prekey
and last-resort KEM prekey rotation are built (`PrekeyStore::rotate_signed_prekey`,
`rotate_kem`), but nothing here schedules them: when to rotate is the
caller's decision, and `../tacenta-spec/protocol/key-deletion.md` says what
the caller must do around one.
