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
    and Triple Ratchet derivations, and the erasure code above the field
    (`erasure-encode.json`, `erasure-decode.json`, from `Model.Erasure`),
    checked by `runners/rust/tests/post_quantum.rs`.
  - `vectors/serialization/`: message and initial-message encodings, checked
    by `runners/rust/tests/serialization.rs`.
  - `vectors/protobuf/`: the bounded protobuf profile's two readers, accepted
    regions with the `fields` they decode to and refused regions, checked by
    `runners/rust/tests/protobuf.rs`.
  - `vectors/persistence/`: the erasure encoder's and decoder's persisted
    formats, the only persisted formats the model states, with the stored
    bytes their readers refuse; checked by `runners/rust/tests/persistence.rs`.
  - `vectors/aead/`: the authenticated encryption, both directions, with its
    refusals, checked by `runners/rust/tests/aead.rs`. Generated like the
    others, but the model has no AES: the generator computes the padding, the
    tag (with the model's HMAC) and the receiver's steps, and takes every
    AES-256 block value from NIST SP 800-38A (F.1.5 and F.2.5), choosing each
    IV so that the cipher's input is one of that standard's blocks. The files'
    `source` field says so, and the conformance manifest says what follows
    from it.
  - `vectors/malformed-input/`: inputs that must be refused, in two kinds of
    file, each file's `source` field saying which.
    - `ratchet-reject.json`: inputs the ratchet must reject, checked by
      `runners/rust/tests/ratchet.rs`. Hand-authored, not model output: the
      file pins a rejection rule the specification states (`MAX_SKIP`), not
      bytes the model produced.
    - `composite-header-decode.json`, `prekey-bundle-decode.json` and
      `initial-message-decode.json`: whole encodings given to the composite
      header's, the prekey bundle's and the initial message's decoders, a
      curve key in each position each of them reads. Each key is
      accepted in its canonical spelling and as p - 1, and refused with bit 255
      set, with p = 2^255 - 19 added, and as p itself (message-format.md, Curve
      public keys). Generated from the model's decoders, which give every
      vector its `result`; an accepted vector's `output` is the re-encoding of
      what its input decodes to. Checked by
      `runners/rust/tests/malformed_input.rs`. Layout: Vector layouts, below.

`conformance-manifest.md` records exactly which specifications, revisions, and
components the vectors cover, and what is excluded. Peer interoperability is
scoped to the bundle layer, and the manifest says what that means.

## Vector layouts

Every byte string is lowercase hex, and every integer is written as big-endian
bytes. Most known-answer files name their inputs for the fields or parameters
of the page they pin, and message-format.md, Ratchet message, says how the
composite-header vectors name theirs. The files below have layouts of their
own, written down here. `schema/vector.schema.json` points here.

### The decoders: `vectors/malformed-input/*-decode.json`

The page is message-format.md: Ratchet message, Initial message, Prekey
bundle, Curve public keys and Rejection.

- **`encoding`**, the one input, is the bytes handed to the decoder, whole.
  - In `composite-header-decode.json` it is a composite header alone, the
    102 bytes of `composite` in Ratchet message, with nothing after it. The
    page defines the ratchet-message decoder rather than a decoder of the
    header on its own. These 102 bytes are also a whole ratchet message with
    an empty `ciphertext`, which that decoder does not constrain, so it gives
    each vector the same verdict. No vector has bytes after the header, so
    none decides what a decoder of the header alone does with them.
    `tacenta-wire`'s `decode_composite`, which the Rust runner calls, returns
    them, as the ciphertext that follows.
  - In `prekey-bundle-decode.json` it is a whole bundle (Prekey bundle), 1,811
    bytes with ML-KEM-1024's `kem_prekey`.
  - In `initial-message-decode.json` it is a whole initial message (Initial
    message), 88 bytes: a two-byte `kem_ciphertext` and a two-byte
    `ratchet_message`, neither of which that decoder checks.
- **A valid vector carries `output`**, not `fields`. It is the re-encoding of
  what the decoder returned: the header (and the bytes after it, of which
  there are none), the bundle, or the initial message. Every accepted input is
  canonical, so `output` equals `encoding`.
- **An invalid vector's `encoding` is refused as a decode failure** (Curve
  public keys: "A refused key is a decode failure"), and not as any other
  refusal.

### The erasure code: `vectors/post-quantum/erasure-encode.json` and `erasure-decode.json`

The page is mlkem-braid.md, The erasure code.

- **`erasure-encode.json`.**
  - `message` is the value, whole.
  - `indices` is a run of 16-bit indices, two bytes each. A new encoder over
    `message` is run from index 0, and must issue each index in turn, up to the
    largest one listed.
  - `output` is the 32 bytes of the codeword at each listed index, in the order
    listed and back to back, with no index in front of each.
  - `stream_length`, when present, is a 32-bit count. The encoder is run to its
    end and must issue exactly that many codewords in all.
- **`erasure-decode.json`.**
  - `size` is the value's length `n` in bytes, as a 32-bit integer.
  - `codewords` is a run of codewords, each `index(2) || chunk(32)`. This is the
    persisted decoder's `codeword` layout (session-persistence.md, Erasure
    coder sub-formats). They are offered, in the order listed, to a new decoder
    for `size` bytes.
  - A valid vector's `output` is the value the decoder then holds.
  - **An invalid vector is a decoder that holds no value** after those
    codewords, because it holds fewer than `k`. That is not a refusal: nothing
    is rejected. This is the one file in which `result: invalid` does not mean
    that the input must be refused.

### The erasure coders' persisted formats: `vectors/persistence/`

The page is session-persistence.md, Erasure coder sub-formats and Semantic
rules of the leaf formats. A vector has one of two shapes.

- **Built by operations**, when the inputs are not `bytes`.
  - In `erasure-encoder-state.json`, `message` and `issued`, a 32-bit count: a
    new encoder over `message` issues that many codewords.
  - In `erasure-decoder-state.json`, `size`, 32-bit, and `codewords`, laid out
    as in `erasure-decode.json`: a new decoder for `size` bytes is offered those
    codewords in order.
  - `output` is the stored bytes of the coder so built. A reader must read them
    back to the same coder, and an encoder read back must issue the same next
    codeword.
- **Stored bytes**, when the one input is `bytes`: a stored coder offered to the
  reader. A valid vector's `output` is what the reader read, written back. An
  invalid vector's bytes are refused.

### The protobuf profile: `vectors/protobuf/`

The page is protobuf-profile.md.

- `region` is the protobuf region given to the reader: a ratchet message body's
  in `protobuf-ratchet-body.json`, and a prekey envelope's in
  `protobuf-prekey-envelope.json`.
- A valid vector carries `fields`, the values the region decodes to. A
  length-delimited field is its bytes, and a varint field is four big-endian
  bytes. A field decoded as absent is left out, and only `prekey_id` can be.
- An invalid vector's region is refused.
- Names are compared exactly, as well as values.

The vectors spell field names in snake_case, and the page in camelCase:

| Vector field | Page field | File |
|---|---|---|
| `ratchet_key` | `ratchetKey` | ratchet body |
| `counter` | `counter` | ratchet body |
| `previous_counter` | `previousCounter` | ratchet body |
| `ciphertext` | `ciphertext` | ratchet body |
| `pq` | `pq` | ratchet body |
| `prekey_id` | `prekeyId` | prekey envelope |
| `base_key` | `baseKey` | prekey envelope |
| `identity_key` | `identityKey` | prekey envelope |
| `message` | `message` | prekey envelope |
| `registration_id` | `registrationId` | prekey envelope |
| `signed_prekey_id` | `signedPrekeyId` | prekey envelope |
| `pq_prekey_id` | `pqPrekeyId` | prekey envelope |
| `kem` | `kem` | prekey envelope |

### The AEAD: `vectors/aead/`

The page is message-format.md, Authenticated encryption.

- `enc_key` (32 bytes), `mac_key` (32 bytes) and `iv` (16 bytes) are the
  section's keys.
- **The input `ad` is the section's `AD`**: the whole associated data that
  HMAC-SHA256 covers ahead of the ciphertext. It is not the application's `ad`
  from which `AD = CONCAT(ad, header)` is built, so a runner gives it to the
  AEAD as it is and applies no `CONCAT`. Where a vector's `AD` is a
  `CONCAT(ad, header)`, as in `aead-decrypt.json` `session-associated-data`,
  its comment says so, and the input is already `len(ad) || ad || composite
  header`.
- In `aead-encrypt.json`, `plaintext` is encrypted, and `output` is
  `ciphertext || tag`.
- In `aead-decrypt.json`, `input` is what the receiver holds,
  `ciphertext || tag`. A valid vector's `output` is the plaintext, and an
  invalid vector's input is refused.

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
file's `source` field states the same. The remaining seventeen are
verify-only (`public`, `message`, `signature`, and a `result`): they pin the
edges of the accepted set, where `verify` differs from XEdDSA Revision 1 by
design -- narrower on `s` (`s < l`, not `s < 2^253`) and on small-order `R`
or `A`, wider on the sign bit the interoperability profile carries in
`signature[63]`, and in agreement on non-canonical encodings. Four of the
eight small-order-`A` vectors use `R` the identity and `s = 0`, which rule 6
of identities-and-devices.md, Verifying a signature, refuses too. The other
four, whose ids contain `rule-3-only`, pair the same keys with an `R` that is
not of small order, `s < l` and an equation that holds, so rule 3 (`A` is
not of small order) is the only rule that refuses them. Like the rest of the
verify-only vectors, they are computed rather than model-generated. Each such
comment opens with `Revision 1 accepts:` or `Revision 1 rejects:`, and a
test in tacenta-core runs a transcription of the specification's own
`xeddsa_verify` over the file so that column is checked, not asserted. The
transcription is in turn held to a second oracle it shares no code with,
ed25519-dalek's non-strict `verify` (the same equation without the cofactor,
no small-order refusal), on every vector where that oracle is defined
(`u < p`, an Edwards image, `s < l`), which includes the eight small-order-`A`
vectors: those are the inputs on which a transcription that negates the
scalar rather than the point gives the wrong verdict, and the second oracle
is what catches it. And `malformed-input/ratchet-reject.json` is
hand-authored, as above.

## Status

Primitives, the Double Ratchet, PQXDH session establishment, the post-quantum
derivations, the erasure code, serialization, the protobuf profile, the
AEAD, the erasure coders' persisted formats, and malformed input all have
vectors; see the directory list above and `conformance-manifest.md` for
exactly what each covers and what it excludes. The other persisted formats
(ratchet, sparse ratchet, triple ratchet, Braid, session, prekey store) have
none, because the model states none of them.

Files with refusals mark them `result: invalid`. The one exception is
`erasure-decode.json`, whose invalid vectors are decoders that hold no value
rather than refusals (Vector layouts, above). A decoder's accepted vector
may carry `fields`, the named values its input decodes to, in place of
`output` (`schema/vector.schema.json`).

What the vectors still do not cover is the **state machines**: nothing drives
the Braid or the sparse ratchet through a scenario the way the Double Ratchet's
vectors do. That gap is closed by proof rather than by this directory (T1 and
T3 on each crate), which the conformance manifest states in those terms.
Sender keys are not yet scheduled.

## Trademarks and non-affiliation

tacenta-core and Tacenta are not affiliated with, endorsed by, or sponsored by
Signal Messenger LLC or the Signal Foundation. "Signal" and "libsignal" are used
only to name the published protocols and the third-party software they refer to.
