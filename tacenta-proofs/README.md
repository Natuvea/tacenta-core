# tacenta-proofs

Lean proofs and a reproducible verification environment.

The machine-checked proofs relating the implementation to the model and the
model to the specified security properties, plus the pinned toolchain (Lean +
Charon/Aeneas) to reproduce them.

Status: live, and the claims are checked rather than asserted. Three tiers of
proof run here. **T1** is panic-freedom of the translated Rust; **T2** is
functional properties of the Lean model; **T3** is refinement of the translated
Rust against that model. `translation/Translation/` carries T1 and T3 for the
ratchet, session, erasure, protobuf, sparse ratchet, Braid, and triple crates,
with two caveats worth stating here: the erasure crate's T3 covers its field
arithmetic only, not the encoder or decoder, whose entry points have T1 and no
refinement; the Braid's T3 theorems carry two preconditions (a live encoder,
an unspliced chunk stream) on top of the boundary agreements and totality
constants they take -- `CLAIMS.md` lists every hypothesis and records why; and the
Triple's T1 is headed "Proved conditionally" there, on totality assumptions
no leaf theorem discharges. `Proofs/` carries the model-layer work.

Read [CLAIMS.md](CLAIMS.md) for what is established and
[LIMITATIONS.md](LIMITATIONS.md) for what is not. `scripts/attest.py --check`
runs on every push and checks that every theorem CLAIMS.md names exists in the
file it names, that every axiom-pinned theorem is claimed, and that the
attestation hashes are current; it does not read LIMITATIONS.md and it does
not compare theorem *statements* to the prose, which is a reviewer's job
(REPRODUCING.md says what a green `attest` does and does not establish).
[REPRODUCING.md](REPRODUCING.md) is the toolchain and the steps.
