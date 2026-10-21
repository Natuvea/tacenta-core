# tacenta-proofs

Lean proofs and a reproducible verification environment.

The machine-checked proofs relating the implementation to the model and the
model to the specified security properties (in a symbolic model of the attacker;
see `LIMITATIONS.md`, "Forward secrecy is proved, against a symbolic attacker"),
plus the pinned toolchain (Lean +
Charon/Aeneas) to reproduce them.

Status: live. A script checks that every theorem the ledger names exists in the
file it names and that every axiom-pinned theorem (the count is `counts.pinned_theorems` in `manifests/verification-manifest.json`, printed by `attest.py --check`) is named in
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
an unspliced chunk stream) and, for the receive, the bound `ct1_bounded` (on the eight-leaf session unit also `decoders_bounded`; `CLAIMS.md` has theorems that every successful send and receive of the Braid keeps both, from a state that also meets a clause about the decoder that makes the stored ciphertext, under an assumed law about the erasure decoder (on the session unit, two laws about `Vec::truncate` and `usize::div_ceil`)), and the four KEM refusals are refined against the model's `Failed` transitions (the state witnesses assume `KemDrawsSucceed`), on top of the boundary agreements and totality
constants they take -- `CLAIMS.md` lists every hypothesis and records why; and the
Triple's T1 holds on the three-leaf unit, where the inner ratchets' totality is
proved from the leaf theorems, under four size preconditions that nothing on
the unit discharges (they are argued from the sizes involved, not proved) and
the boundary assumptions. The lifecycle crate is translated into the eight-leaf session
unit, where it has conditional T1 theorems and a conditional T3 refinement of its private
`decrypt_ratchet` on every path (`decrypt_ratchet_refines_complete`, and a restated form that takes
`Session::invariant` in place of the run's bounds, five of whose eleven fields the invariant gives alone and two more with an
assumed sparse epoch ceiling, one the model, and four counter ceilings, assumed, the remaining three and a Braid epoch bound;
each ceiling excludes a state the invariant accepts, the clock case shown in Lean and the other three by reading of the Rust,
not checked in Lean; at a session `establish_initiator_for` returned, the invariant, under two assumed laws, and the four
ceilings follow from the establishment, the relation to the model session read off it holds by definition at its
`KeysUnsampled` Braid, and a restored copy of that session decrypts the responder's honest reply, which a test shows; that
`import` of the exported bytes returns that session unchanged, so the restated form applies to the copy given the caller's
boundary records, chunk relation and draw, is proved under nine assumed laws (six of its own, the establishment's two and the `Option::eq` law), and
every session `import` accepts passes `Session::invariant`, the ceilings staying a check on it; at that established session
the first `encrypt` is related to the model's step (its refusal arm only at a model KEM that refuses, since the shipping key
generation does not refuse, by reading), and the session a successful send leaves passes the invariant and meets the
ceilings, under the encrypt boundary records, the oracle record, three assumed laws (a new key-generation law, the
establishment's ciphertext-length law and the ciphertext bound) and six more assumptions for that session, compiler-trusted,
the responder's receipt of the frame covered only as below; for every input `establish_responder`'s outcomes, with their store and
random-source effects, are stated, and at the session it builds the invariant, under assumed and recorded laws, and the
ceilings follow from the construction, so the restated form applies to its inner `decrypt_ratchet`, at a model session read
off the code's session and not shown to be the model's own, for a frame meeting the caller's chunk premises with a draw left,
with no input exhibited there at which the whole call succeeds; and on the bytes the first `encrypt` returns, at a store that
published the bundle used, only the three refusals the store decides remain or the call reaches its inner receive with the
initiator's shared secret, under an assumed X25519 symmetry law, a premise about the run that ML-KEM decapsulation returns
the initiator's secret and a named hypothesis that the store's identifiers are distinct; past those refusals, two named
refusals (a non-contributory agreement of the responder's fresh key, the AEAD refusing the initiator's seal) or success,
and under two more assumed boundary laws (the AEAD round trip, contributory agreement), the model KEM's size law, a
store bound and per-run premises on the responder's source, success with the initiator's plaintext, one draw and the committed store, compiler-trusted, and at the
session it returns `Session::invariant` and the four counter ceilings, for that first receive only and with no assumption beyond the receipt's own
premises (without its store bound), compiler-trusted, and the responder's `encrypt` at that same session, on the same run,
with one outcome (the bare reply frame, no draw, the agreement kept) under the successor's premises, with the responder's
full oracle record, the Braid send contracts at its source and a plaintext-length bound, with no new law, compiler-trusted, and the initiator's `decrypt` of that reply at the session its
first `encrypt` left, on the same run, refusing `NoReceivingChain` exactly when the reply's ratchet key is the peer key the
initiator holds and otherwise returning the responder's plaintext with one draw (two of the four arms of the general
analysis excluded by the contributory and round-trip premises), under the receipt's laws with
the two oracles' roles swapped and two decrypt boundary records at the initiator's source, compiler-trusted; a tampered frame
being refused and later messages in either direction not covered);
`decrypt_ratchet_refines_complete` is
compiler-trusted, it takes two laws about `Vec::pop` and `Option::as_mut` (assumed; not
checked against the real functions) from which its proof derives the sparse ratchet's two
agreements, the three fields of the contract record it takes that were stronger than
the crate are now stated at the instances the unit passes (that the real `zeroize`
functions return there is assumed; not checked against the real functions); the same
result is carried through the public `Session::decrypt` on frames that are not initial
messages, under the same hypotheses and one premise on the input
(`decrypt_refines_ratchet_frame`, also in compiler-trusted forms that take `Session::invariant`
and the counter ceilings), and no theorem covers an initial message, so nothing
here proves `Session::encrypt` or `Session::decrypt` end to end. `Proofs/` carries the
model-layer work.

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
