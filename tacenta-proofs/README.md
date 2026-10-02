# tacenta-proofs

Lean proofs and a reproducible verification environment.

The machine-checked proofs relating the implementation to the model and the
model to the specified security properties (in a symbolic model of the attacker;
see `LIMITATIONS.md`, "Forward secrecy is proved, against a symbolic attacker"),
plus the pinned toolchain (Lean +
Charon/Aeneas) to reproduce them.

Status: live. A script checks that every theorem the ledger names exists in the
file it names and that every axiom-pinned theorem (608 at this commit) is named in
the ledger. Whether a pin is current is checked by the Lean build, which fails on a
wrong pin; the script does not check it. The other 83 claimed theorems carry no pin. No recorded review of the theorem
statements by a reader who did not write the ledger exists in this repository.
Three tiers of proof run here. **T1** is panic-freedom of the translated Rust; **T2** is
functional properties of the Lean model; **T3** is refinement of the translated
Rust against that model. `translation/Translation/` carries T1 and T3 for the
wire, ratchet, session, erasure, protobuf, sparse ratchet, Braid, and triple crates,
with two caveats worth stating here: the erasure crate's T3 covers its field
arithmetic only, not the encoder or decoder, whose entry points have T1 and no
refinement; the Braid's T3 theorems carry two preconditions (a live encoder,
an unspliced chunk stream) and, for the receive, the bound `ct1_bounded` (on the eight-leaf session unit also `decoders_bounded`; `CLAIMS.md` has theorems that every successful send and receive of the Braid keeps both, from a state that also meets a clause about the decoder that makes the stored ciphertext, under an assumed law about the erasure decoder (on the session unit, two laws about `Vec::truncate` and `usize::div_ceil`)), on top of the boundary agreements and totality
constants they take -- `CLAIMS.md` lists every hypothesis and records why; and the
Triple's T1 holds on the three-leaf unit, where the inner ratchets' totality is
proved from the leaf theorems, under four size preconditions that nothing on
the unit discharges (they are argued from the sizes involved, not proved) and
the boundary assumptions. `Proofs/` carries the model-layer work.

Read [CLAIMS.md](CLAIMS.md) for what is established and
[LIMITATIONS.md](LIMITATIONS.md) for what is not. `scripts/attest.py --check`
runs on every push and checks that every theorem CLAIMS.md names exists in the
file it names, that every axiom-pinned theorem is claimed, that the pins named in
`REQUIRED_PINS` exist as live code and that no pin is labelled compiler-trusted unless
`COMPILER_TRUSTED_PINS` names it, and that the attestation hashes are current; it does not read LIMITATIONS.md and it does
not compare theorem *statements* to the prose, which is a reviewer's job
(REPRODUCING.md says what a green `attest` does and does not establish).
[REPRODUCING.md](REPRODUCING.md) is the toolchain and the steps.

## Trademarks and non-affiliation

tacenta-core and Tacenta are not affiliated with, endorsed by, or sponsored by
Signal Messenger LLC or the Signal Foundation. "Signal" and "libsignal" are used
only to name the published protocols and the third-party software they refer to.
