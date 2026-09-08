# tacenta-test-vectors

Interoperability vectors and conformance tests.

Known-answer vectors and conformance tests that pin the implementation to the
specification. Two kinds live here:

- **Primitive vectors** (`vectors/primitives/`): RFC and NIST known-answer
  values for SHA-256, HMAC, HKDF, X25519, and Ed25519, checked against
  tacenta-core by `runners/rust/tests/primitives.rs`. Format:
  `schema/vector.schema.json`.
- **Protocol vectors**, all generated from the model by `regenerate-vectors.sh`
  and checked against tacenta-core:
  - `vectors/ratchet/`: Double Ratchet scenarios, replayed by
    `runners/rust/tests/ratchet.rs`. Format: `schema/ratchet-vector.schema.json`.
  - `vectors/session-establishment/`: PQXDH shared secrets, checked by
    `runners/rust/tests/session_establishment.rs`. Format:
    `schema/vector.schema.json`.
  - `vectors/post-quantum/`: the field, interpolation, sparse-ratchet, Braid
    and Triple Ratchet derivations, checked by `runners/rust/tests/post_quantum.rs`.
  - `vectors/serialization/`: message and initial-message encodings, checked
    by `runners/rust/tests/serialization.rs`.
  - `vectors/malformed-input/`: inputs the ratchet must reject, checked by
    `runners/rust/tests/ratchet.rs`.

`conformance-manifest.md` records exactly which specifications, revisions, and
components the vectors cover, and what is excluded.

Status: primitives, the Double Ratchet, PQXDH session establishment, the
post-quantum derivations, serialization, and malformed input all have vectors;
see the directory list above and
`conformance-manifest.md` for exactly what each covers and what it excludes.

What the vectors still do not cover is the **state machines**: nothing drives the
Braid or the sparse ratchet through a scenario the way the Double Ratchet's
vectors do. That gap is closed by proof rather than by this directory (T1 and T3 on each
crate), which the conformance manifest states in those terms. Sender
keys are milestone M4. Peer interoperability is scoped to the bundle layer.
