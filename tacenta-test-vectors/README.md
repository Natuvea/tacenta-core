# tacenta-test-vectors

Known-answer and conformance vectors that pin the implementation to the
specification, and the runner that checks them.

Two kinds live here:

- **Primitive vectors** (`vectors/primitives/`): RFC known-answer values for
  HMAC-SHA256, HKDF-SHA256, X25519, and Ed25519, and one project-generated
  file for XEdDSA, which has no published vectors. Checked by
  `runners/rust/tests/primitives.rs`; `conformance-manifest.md` says, row by
  row, what each file is checked against, since Ed25519 is a trusted-boundary
  crate rather than a tacenta-core API. SHA-256 itself has no file here: its
  NIST examples are checked against the model at build time. Format:
  `schema/vector.schema.json`.
- **Protocol vectors**, generated from the model by `regenerate-vectors.sh`
  (all but `malformed-input/ratchet-reject.json`, whose `source` field says it
  is hand-authored) and checked against tacenta-core:
  - `vectors/ratchet/`: Double Ratchet scenarios, replayed by
    `runners/rust/tests/ratchet.rs`. Format: `schema/ratchet-vector.schema.json`.
  - `vectors/session-establishment/`: PQXDH shared secrets, checked by
    `runners/rust/tests/session_establishment.rs`. Format:
    `schema/vector.schema.json`.
  - `vectors/post-quantum/`: the field, interpolation, sparse-ratchet, Braid
    and Triple Ratchet derivations, checked by `runners/rust/tests/post_quantum.rs`.
  - `vectors/serialization/`: message and initial-message encodings, checked
    by `runners/rust/tests/serialization.rs`.
  - `vectors/malformed-input/`: inputs that must be refused, in two kinds of
    file, each file's `source` field saying which.
    - `ratchet-reject.json`: inputs the ratchet must reject, checked by
      `runners/rust/tests/ratchet.rs`. Hand-authored, not model output: the
      file pins a rejection rule the specification states (`MAX_SKIP`), not
      bytes the model produced.
    - `composite-header-decode.json` and `prekey-bundle-decode.json`: whole
      encodings given to the composite header's and the prekey bundle's
      decoders, a curve key in each position either reads. Each key is
      accepted in its canonical spelling and refused with bit 255 set or with
      p = 2^255 - 19 added (message-format.md, Curve public keys). Generated
      from the model's decoders, which give every vector its `result`; an
      accepted vector's `output` is the re-encoding of what its input decodes
      to. Checked by `runners/rust/tests/malformed_input.rs`. Format:
      `schema/vector.schema.json`.

`conformance-manifest.md` records exactly which specifications, revisions, and
components the vectors cover, and what is excluded. Peer interoperability is
scoped to the bundle layer, and the manifest says what that means.

## Checking the vectors

The runner is a Rust crate that loads every file and drives tacenta-core
against it:

    cd tacenta-test-vectors/runners/rust
    cargo test --locked

Every file also validates against its schema, including identifier uniqueness
and the rule that a valid vector carries an output:

    python3 tooling/check-vectors.py

Both run in the public CI and in `tooling/ci.sh`.

## Regenerating the protocol vectors

The model is the oracle. The protocol vector files are its byte output, so
after any change to the model they are regenerated and the result committed;
CI regenerates them too and fails on a difference between the model and the
committed files.

Prerequisite: the Lean toolchain `tacenta-model/lean-toolchain` names
(v4.31.0 at the time of writing), installed through elan, so that `lake` is
on the path and installs that toolchain on first use. Then:

    (cd tacenta-model && lake build)
    bash tacenta-test-vectors/regenerate-vectors.sh
    git diff --stat -- tacenta-test-vectors/vectors

`lake build` compiles the generator along with the model; the script runs it
once per file, writing each to a temporary path and moving it into place only
when the generator succeeds. An empty diff means the committed vectors are
current. Two things are not regenerated. The primitive vectors are
standards' known answers, plus the XEdDSA file, which is project-generated
by tacenta-core (`primitives/xeddsa.rs`) rather than by the model: its first
vector is the pin the crate's own test carries; the next two (the same key
under a different nonce, and a different key over an empty message) are
this implementation's output. The runner re-signs each with its recorded
nonce and compares, then verifies the result through ed25519-dalek's strict
verify, which is the check against an independent implementation; the
file's `source` field states the same. The remaining thirteen are
verify-only (`public`, `message`, `signature`, and a `result`): they pin the
edges of the accepted set, where `verify` differs from XEdDSA Revision 1 by
design -- narrower on `s` (`s < l`, not `s < 2^253`) and on small-order `R`
or `A`, wider on the sign bit the interoperability profile carries in
`signature[63]`, and in agreement on non-canonical encodings. Each such
comment opens with `Revision 1 accepts:` or `Revision 1 rejects:`, and a
test in tacenta-core runs a transcription of the specification's own
`xeddsa_verify` over the file so that column is checked, not asserted. The
transcription is in turn held to a second oracle it shares no code with,
ed25519-dalek's non-strict `verify` (the same equation without the cofactor,
no small-order refusal), on every vector where that oracle is defined
(`u < p`, an Edwards image, `s < l`), which includes the four small-order-`A`
vectors: those are the inputs on which a transcription that negates the
scalar rather than the point gives the wrong verdict, and the second oracle
is what catches it. And `malformed-input/ratchet-reject.json` is
hand-authored, as above.

## Status

Primitives, the Double Ratchet, PQXDH session establishment, the post-quantum
derivations, serialization, and malformed input all have vectors; see the
directory list above and `conformance-manifest.md` for exactly what each
covers and what it excludes.

What the vectors still do not cover is the **state machines**: nothing drives
the Braid or the sparse ratchet through a scenario the way the Double Ratchet's
vectors do. That gap is closed by proof rather than by this directory (T1 and
T3 on each crate), which the conformance manifest states in those terms.
Sender keys are not yet scheduled.

## Trademarks and non-affiliation

tacenta-core and Tacenta are not affiliated with, endorsed by, or sponsored by
Signal Messenger LLC or the Signal Foundation. "Signal" and "libsignal" are used
only to name the published protocols and the third-party software they refer to.
