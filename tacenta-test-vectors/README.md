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
  - `vectors/persistence/`: the persisted formats the model states, with the
    stored bytes their readers refuse: the erasure encoder's and decoder's
    (`erasure-encoder-state.json`, `erasure-decoder-state.json`, from
    `Model.Erasure`), and the classical ratchet's, the sparse ratchet's, the
    Triple Ratchet's and the ML-KEM Braid's states (`ratchet-state.json`,
    `sparse-ratchet-state.json`, `triple-ratchet-state.json`,
    `braid-state.json`, from `Model.PersistedState`), whose refused vectors
    also name the refusal. Checked by `runners/rust/tests/persistence.rs`.
    Layout: Vector layouts, below.
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

### The erasure coders' persisted formats: `vectors/persistence/erasure-*-state.json`

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

### The ratchets' persisted states: `vectors/persistence/ratchet-state.json` and `sparse-ratchet-state.json`

The page is session-persistence.md: Ratchet state, Sparse ratchet state,
Semantic rules of the leaf formats, Stored curve public keys and Rejection. A
vector has one of two shapes.

- **Built by operations**, when the inputs include `steps`.
  - The operations start from a new state, or from `start`, stored bytes the
    reader accepts.
    - In `ratchet-state.json` a new state is named by `role`. `00` is the party
      that sends first (ratchet.md, Initialisation), from `sk`, `our_pub`,
      `peer_pub` and `dh_out`, the value of `DH(DHs, DHr)`. `01` is the party
      that receives first, from `sk` and `our_pub`. Both derive under the one
      label set, `labels` `0x00`.
    - In `sparse-ratchet-state.json` a new state is named by `direction`, `00`
      for `A2b` and `01` for `B2a`, from `sk` (sparse-pq-ratchet.md,
      Initialisation).
  - `steps` is the operations in order, back to back. It is empty when there
    are none. In a valid vector every operation in it is accepted. In an
    invalid vector every operation but the last is accepted and the last is
    refused, and its `refusal` is `counter-exhaustion`: a step past a
    counter's ceiling (ratchet.md, Sending and receiving; sparse-pq-ratchet.md,
    Sending and Receiving).
    - In `ratchet-state.json`, `00` is a send. `01` is a receive, followed by
      the header's `dh(32) || pn(4) || n(4)`, then `dh_recv(32) ||
      dh_send(32) || new_pub(32)`. Those three are `DH(DHs, header key)`,
      `DH(new DHs, header key)` and the new `DHs` public key, which a receive
      uses only when it takes a Diffie-Hellman step and which are zero where
      it does not. The Diffie-Hellman values are the generator's symmetric
      stand-in, not X25519, as in `vectors/ratchet/`.
    - In `sparse-ratchet-state.json`, each operation is `op(1) || epoch(8) ||
      output_present(1) || output_epoch(8) || output_key(32)`, and a receive
      has the message number `n(8)` after that. `op` `00` sends on `epoch`'s
      chain and `01` receives on it (sparse-pq-ratchet.md, Sending and
      Receiving). The output is the agreement's secret and its epoch, or
      `output_present` `00` and zeros when the agreement gave none.
  - In a valid vector, `output` is the stored bytes of the state reached. A
    runner must write
    that state as `output`, and read `output` back to a state it writes as
    `output` again.
- **Stored bytes**, when the one input is `bytes`: a stored state offered to
  the reader.
  - Each valid built-by-operations vector has one of these beside it, whose id is
    its own with `-read-back` added and whose `bytes` are its `output`.
  - A valid vector carries `fields`, the values the reader read. An accepted
    input is canonical, so the state read is written back as `bytes`.
  - In `ratchet-state.json` the fields are `dhs_pub`, `dhr_pub`, `rk`, `cks`,
    `ckr`, `ns`, `nr`, `pn`, `events`, `labels` and `skipped`, each named as
    on the page. An optional key read as absent is left out. An integer is its
    field's big-endian bytes, and `labels` is its tag byte. `skipped` is the
    stored keys in the order read, each `dh(32) || n(4) || stored_at(4) ||
    key(32)`, back to back, and empty when there are none.
  - In `sparse-ratchet-state.json` the fields are `rk`, `epoch`, `direction`,
    `chains` and `skipped`. `direction` is its tag byte. `chains` and
    `skipped` are the entries in the order read, laid out as the page lays out
    `chains` and `skipped` and back to back.
  - An invalid vector's bytes are refused, and its `refusal` names the refusal
    (Rejection). `wrong-version` is a version byte other than `0x01`.
    `short-or-malformed` is every other refusal, a state that breaks a
    semantic rule included.

Two things no vector here pins.

- **A short buffer with another version.** A buffer too short for its fixed
  fields that also has a version byte other than `0x01` may be refused as
  either, and which is left to the implementation (session-persistence.md,
  Rejection). `Model.PersistedState` reads the version byte first and
  `tacenta-core` checks the length first; both conform, and no vector here
  offers such a buffer.
- **A store of exactly `MAX_SKIPPED_STORE` keys.** 2,001 keys are refused in
  both files, but the accepted side of the bound is not pinned, since its
  vector would be about 290 kilobytes.

### The Triple Ratchet's state: `vectors/persistence/triple-ratchet-state.json`

The page is session-persistence.md, Triple ratchet state, its entry under
Semantic rules of the leaf formats, and Rejection. The two shapes are the
ratchets' above.

- **Built by operations**, when the inputs include `steps`. A new state is
  named by `role`, `00` the party that sends first and `01` the party that
  receives first, from `sk` and `our_pub` (and, for `00`, `peer_pub` and
  `dh_out`); or the operations start from `start`, stored bytes the reader
  accepts. `steps` is the operations back to back:
  - `00` is a send, followed by `sending_epoch(8)` and the agreement's output;
  - `01` is a receive, followed by the classical header's `dh(32) || pn(4) ||
    n(4)`, the step's `dh_recv(32) || dh_send(32) || new_pub(32)`, the sparse
    half's `epoch(8) || pq_n(8)`, and the output.

  An output is `output_present(1) || output_epoch(8) || output_key(32)`,
  zeroed when absent, as in `sparse-ratchet-state.json`. `output` is the
  stored bytes of the state reached.
- **Stored bytes**, when the one input is `bytes`. A valid vector's `fields`
  are `classical` and `post_quantum`, each half's own stored bytes; laid out
  as `version || len(4) || classical || len(4) || post_quantum` they are the
  input. An invalid vector's `refusal` is `wrong-version` for a first byte
  other than `0x01` and `short-or-malformed` for everything else -- including
  a half whose *own* version byte its own reader does not recognise, which is
  not passed through (session-persistence.md, Triple ratchet state).

### The Braid's state: `vectors/persistence/braid-state.json`

The page is session-persistence.md, Braid, its entry under Semantic rules of
the leaf formats, and Rejection.

- **Stored bytes**, when the one input is `bytes`. A valid vector's `fields`
  are `state_tag`, and for every live state `epoch`, `auth` and `fields`; laid
  out as `version || state_tag || epoch || auth || fields` they are the input.
  `fields` is the tag's own fields, each `len(4) || bytes`, back to back.
  `Failed` (tag 11) carries only `state_tag`: the format writes no epoch, no
  authenticator and no field for it.
- **Built by operations**, when the inputs are `start` and `steps`. Each step
  is one received Braid message, `epoch(8) || type(1) || chunk_present(1) ||
  chunk_index(2) || chunk(32)`, the type byte being `AgreementType`'s
  (CONSTANTS.md). `output` is the stored bytes of the state reached.

**Only two transitions are driven, and the reason is the reason tags 1 to 4
have no accepted vector.** `key_pair` (11,872 bytes) and `encaps` (2,592) are
`tacenta-kem`'s own serialisations, whose layout the page delegates to
`libcrux-ml-kem` (ADR-0006, point 5). The page has a reader validate the
`header` and `ek_vector` *inside* a stored `key_pair`, and scopes that clause
to a reader that knows the layout; finding them needs it. So
`Model.PersistedState` checks the field's length and accepts it -- what the
page asks of a reader outside the scope -- and therefore accepts key pairs
`tacenta-braid`, which has the layout, refuses. So:

- tags 1 to 4, which carry a `key_pair`, appear only in refusals, at a length
  both readers refuse;
- tags 7 to 9, which carry an `encaps`, are pinned in full, because checking
  `encaps`'s length and nothing else is the whole of the page's rule for it;
- tags 0, 5, 6, 10 and 11 carry neither and are pinned in full;
- the state machine is reached only from `Ct2Sampled`, whose two transitions
  read the stored epoch and the message and nothing else. Those are the
  `ct2-sampled-*` vectors, and they are what pin the Braid's epoch ceiling
  from the transitions' side; `epoch-u64-max` pins it from the reader's.

What no vector in this file pins, then, is **the `key_pair` content clause of
tags 1 to 4** -- and no vector can. A vector states one verdict every
conforming reader must reach; this clause has none, because a stored state
whose key pair fails it is refused by a reader inside the scope and accepted
by one outside, and both conform. A vector on the accepting side would need a
key pair that passes the validation, which means the library's serialisation,
which is what the page delegates. The clause is stated on the page,
implemented in `tacenta-braid`, and carried by that crate's own tests. What
every implementation must apply, the field's length, is pinned by
`key-pair-wrong-length`.

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

## Differential testing against the model

Every vector is a case someone chose. Beside them, a harness runs *generated*
operation sequences through `tacenta-model` and `tacenta-core` and compares
them step by step, so that a disagreement nobody thought to write down still
shows up (ADR-0008, practice 9). It has two halves:

- `tacenta-model/Difftest.lean`, which `lake build` compiles as
  `lake exe difftest`. It reads a start and a list of operations and prints,
  after the start and after every step, whether the model took or refused the
  step and the bytes `Model.PersistedState` writes the state as. It chooses
  nothing and checks nothing.
- `runners/rust/tests/differential.rs`, which generates the sequences from a
  seed, blind to what either side will answer, sends them to that executable,
  replays the same operations on `tacenta-ratchet`, `tacenta-spqr`,
  `tacenta-triple` and `tacenta-braid`, and compares the two transcripts.

The operations are encoded exactly as the `steps` input of the two
ratchet-state files above, so a sequence here means what a sequence there
means. A start is either initialisation parameters, which each side runs its
own initialisation on, or stored bytes both sides read: a counter at its
ceiling cannot be walked to, so the near-ceiling sequences start from bytes
the harness assembles from the layout in `session-persistence.md` rather than
from either implementation.

**What it compares**, at every step of every sequence:

- the outcome, taken or refused;
- the stored bytes of the state the step left, a refused step included. The
  model's operations leave the state alone when they refuse, and both crates
  document that a state which returned `Err` is spent and the caller works on a
  copy, so the harness replays on a copy and restores it. A skipped key not
  erased, or erased a message early, is a difference in these bytes;
- the export-and-import check, at every step rather than at chosen ones: each
  side reads back the bytes it has just written, and the two must agree on
  whether the reader accepts them and on which refusal it gives if not;
- the refusal kind, `wrong-version` against `short-or-malformed`, on the
  corrupted buffers made from each sequence's final state;
- counter exhaustion: a step `tacenta-core` refuses as `ChainExhausted` must be
  one the model refuses with the counter at its ceiling. The converse is not
  asserted and does not hold, since a receive at `nr = u32::MAX` numbered below
  it is out of order on both sides rather than exhaustion.

**What it does not compare.**

- **Message keys.** The harness compares states, not the keys an operation
  returns; `vectors/ratchet/double-ratchet.json` pins those.
- **The session and the prekey store.** The model states no stored format for
  them, so there is nothing to compare states by, and no generated sequence
  drives them.
- **Most of the Braid's state machine.** The Triple Ratchet is driven through
  generated sequences like the two ratchets, and the Braid's *decoder* is
  driven on generated stored states. Its transitions are reached only from
  `Ct2Sampled`, whose two -- transition (13) and the refusal at the reserved
  epoch -- read the stored epoch and the message and nothing else. Every other
  transition consumes a KEM key pair or encapsulation state, whose layout the
  page delegates, so neither side of the harness can build one.
- **The `key_pair` content clause of the Braid's tags 1 to 4.** The page
  scopes it to a reader that knows the delegated layout; the model is outside
  that scope, so it checks the field's length and accepts it, and accepts key
  pairs `tacenta-braid` refuses. The harness generates tags 1 to 4 only at a
  length both readers refuse: generating a well-formed one would be generating
  a difference the two sides are both entitled to, not a finding.
- **The store's total bound.** Reaching `MAX_SKIPPED_STORE` means deriving
  thousands of message keys in the model's Lean SHA-256 and then reading a
  state holding them back at every later step. The refused side of the bound
  is pinned by the `store-over-its-bound` vectors instead. The per-chain bound
  is driven: the step past `MAX_SKIP` in every run, and `MAX_SKIP` itself in
  the long run below.
- **The one refusal the specification leaves open.** A buffer too short for
  its fixed fields whose version byte is not `0x01` may be refused as either
  (session-persistence.md, Rejection), so the harness accepts both spellings
  for that buffer and no other.

Running it needs the model built, as regenerating the vectors does:

    (cd tacenta-model && lake build)
    (cd tacenta-test-vectors/runners/rust && cargo test --locked --test differential -- --nocapture)

The bounded run, which `tooling/ci.sh` and the CI vectors job run, is 48
sequences per algorithm of up to 20 operations each from a fixed seed: about
2,900 steps for the two ratchets and 960 for the Triple Ratchet, 384 corrupted
ratchet imports, 192 Triple Ratchet imports, 55 Braid imports and the Braid's
three `Ct2Sampled` steps, in about ten seconds. The seed and the sequence
count are printed, so a failure is reproducible, and a failing seed prints the
shortest sequence that still disagrees along with both sides' bytes. A longer
run is

    TACENTA_DIFF_SEQUENCES=2000 TACENTA_DIFF_LONG=1 cargo test --release --test differential -- --nocapture

where `TACENTA_DIFF_SEED` picks another seed and `TACENTA_DIFF_LONG=1` adds the
sequences that skip the whole of `MAX_SKIP`, which are minutes rather than
seconds and so are left out of the gate.

**A disagreement is a finding.** The model is normative (ADR-0006), so where
the two sides differ the harness reports the minimal sequence and the bytes,
and the difference is settled by a specification decision rather than by
editing whichever side is easier to change.

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
AEAD, the erasure coders' persisted formats, the classical ratchet's, the
sparse ratchet's, the Triple Ratchet's and the Braid's persisted states, and
malformed input all have vectors; see the directory list above and
`conformance-manifest.md` for exactly what each covers and what it excludes.
The session's and the prekey store's persisted formats have none, because the
model states neither.

Files with refusals mark them `result: invalid`. The one exception is
`erasure-decode.json`, whose invalid vectors are decoders that hold no value
rather than refusals (Vector layouts, above). In the two ratchet-state files
an invalid vector also names its `refusal`. A decoder's accepted vector
may carry `fields`, the named values its input decodes to, in place of
`output` (`schema/vector.schema.json`).

What the **vector files** still do not cover in full is the **state
machines**: no vector drives the Braid or the sparse ratchet through a
scenario the way the Double Ratchet's vectors do. For the two ratchets and the
Triple Ratchet that gap is now covered by the differential harness above as
well as by proof, since it drives each through generated sequences and
compares every step against the model; for all of the crates it is covered by
proof (T1 and T3 on each), which the conformance manifest states in those
terms.

The Braid is the partial case, and the line is worth stating exactly. Its
epoch ceiling, which `Model.Braid` states and `tacenta-braid` keeps, **is now
pinned from both sides**: `braid-state.json`'s `epoch-u64-max` pins the
reader's refusal of the reserved epoch, and its two `ct2-sampled-*` vectors
drive the two transitions that meet the ceiling, which the harness drives too.
What is still pinned by neither is the rest of the Braid's state machine and
the `key_pair` content clause of tags 1 to 4, both for the same reason: they
need the KEM layout the page delegates. The clause is additionally one no
vector could pin, since the page scopes it to implementations that have that
layout, so a state failing it is refused by one conforming reader and accepted
by another. Those rest on the proofs and the crate's own tests. Sender keys
are not yet scheduled.

## Trademarks and non-affiliation

tacenta-core and Tacenta are not affiliated with, endorsed by, or sponsored by
Signal Messenger LLC or the Signal Foundation. "Signal" and "libsignal" are used
only to name the published protocols and the third-party software they refer to.
