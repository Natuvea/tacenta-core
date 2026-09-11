# Assumptions

What the requirements in `security-properties/` rest on. Each assumption is
numbered, and says which requirements rely on it and which proofs take it.

The assumptions fall into two parts:
- **About the world:** ASM-01 to ASM-14 are what the protocol's security
  depends on, for any implementation.
- **About the evidence:** ASM-15 to ASM-19 are what a proof in `tacenta-proofs`
  depends on to say anything about `tacenta-core`. They are not assumptions of
  the protocol.

`tacenta-proofs/LIMITATIONS.md` is the record of what is trusted without proof.
This page states the assumptions and cites that record; it does not replace it.

## About the world

### ASM-01: randomness

Every random value the protocol draws is uniform and independent, and
unpredictable to every adversary. In `tacenta-core` that source is the caller's
generator: every public function that draws randomness takes an
`R: RngCore + CryptoRng` (`rand_core` 0.6; `tacenta-core/src/lib.rs`).

The values drawn:
- the identity secret;
- every curve prekey, and each KEM prekey's 64 key-generation bytes;
- the initiator's ephemeral key, and the 32 bytes of each encapsulation;
- every ratchet key pair;
- the 64 bytes `Z` of each XEdDSA signature;
- the Braid's key generation and encapsulation randomness.

A repeated or predictable value breaks every requirement that depends on a key
made from it.

- **Relied on by:** REQ-AUTH-03, REQ-AUTH-07, REQ-CONF-01, REQ-CONF-06,
  REQ-CONF-08, REQ-FS-05, REQ-FS-06, REQ-PCS-01, REQ-PCS-02, REQ-PCS-03.
- **Proofs:** the symbolic model represents fresh values as distinct leaves
  (`Model.Adversary.Sym.seed i`, `Sym.dhOut i`), which presumes they never
  coincide. `BraidT1.RngTotal rc`, taken by `Braid.send_no_panic` and
  `Braid.send_refines`, assumes only that the generator returns, and nothing
  about what it returns.

### ASM-02: X25519

The Diffie-Hellman assumptions on curve25519 that the published X3DH and PQXDH
analyses rest on hold against a classical adversary. `x25519-dalek` 2 and
`curve25519-dalek` 4 compute RFC 7748's function. Not assumed against ADV-03:
that is what ASM-04 is for.

- **Relied on by:** REQ-AUTH-03, REQ-AUTH-10, REQ-CONF-01, REQ-FS-05,
  REQ-FS-06, REQ-PCS-01, REQ-PCS-02.
- **Proofs:** none. Every proof takes agreement outputs as opaque bytes
  (`receive_refines` in `Translation/T3.lean`, `shared_secret_refines_some`)
  or as leaves (`Sym.dhOut`).

### ASM-03: XEdDSA signatures under the identity key

XEdDSA, with the verifier's accepted set of identities-and-devices.md, is
existentially unforgeable under chosen-message attack by a classical adversary.
Using one secret both as the X25519 identity key and as the signing key weakens
neither use (ADR-0002). The `F` prefix is what keeps the handshake's key
derivation separate from signing (session-establishment.md, Notation).

XEdDSA is implemented in `tacenta-core` over `curve25519-dalek` and
`ed25519-dalek`, not taken from a vetted crate. That is the deliberate exception
recorded in ADR-0002 and LIMITATIONS.md, "Trusted, not verified". Not assumed
against ADV-03.

- **Relied on by:** REQ-AUTH-01, REQ-AUTH-03.
- **Proofs:** none. The signature check is outside every translated crate
  (LIMITATIONS.md, "Eight verified zones on the shipping path, and the
  orchestration runs outside them").

### ASM-04: ML-KEM-1024

- ML-KEM-1024 is IND-CCA2 secure, against a classical adversary and against
  ADV-03.
- Decapsulation recovers the encapsulated secret except with the failure
  probability FIPS 203 bounds, 2^-174.
- The shared secret binds the encapsulation key. session-establishment.md
  relies on this in not appending `EncodeKEM(PQPKB)` to the associated data,
  and records the reliance as an open question.
- `libcrux-ml-kem` 0.0.10 computes FIPS 203, including the SHA-3 and SHAKE
  functions inside it.

- **Relied on by:** REQ-AUTH-14, REQ-CONF-01, REQ-CONF-06, REQ-FS-05,
  REQ-PCS-03.
- **Proofs:** the Braid's refinement takes `KemAgreesFor`, `ValidateEkAgrees`,
  `KemLenAgrees` and `KemCloneAgrees` (`Translation/BraidT3.lean`). The model's
  `Kem.Correct` rounds the failure probability to zero (LIMITATIONS.md, under
  the Braid's erasure and KEM hypotheses). `validate_ek` checks the public half
  of a stored key pair only. The PQXDH derivation takes `SS` as bytes.

### ASM-05: HMAC-SHA256 and HKDF-SHA256

HMAC-SHA256 is a pseudorandom function, and HKDF-SHA256 is a dual pseudorandom
function: its output is indistinguishable from random when either the salt or
the input keying material is secret and uniform. This holds against a classical
adversary and against ADV-03. `hkdf` 0.12, `hmac` 0.12 and `sha2` 0.10
(RustCrypto) compute RFC 2104 and RFC 5869. The translated leaf crates reach
them through the `tacenta-kdf` crate.

In particular:
- **`KDF_CK`:** neither the next chain key nor the message key reveals the
  chain key they came from.
- **`KDF_RK`, and the sparse ratchet's root step:** the output is secret if the
  root key or the agreement output is.
- **The Triple Ratchet's combination:** its output is secret if either message
  key is. The post-quantum key is the salt and the classical key the input
  keying material (triple-ratchet.md).
- **The PQXDH `KDF`:** `SK` is secret if any one agreement output or `SS` is.
- **Labels:** the derivation labels are distinct, and prefix-free apart from
  two registered pairs (`tacenta-core/LABELS.md`, checked by
  `tooling/check-labels.sh`).

- **Relied on by:** REQ-AUTH-03, REQ-AUTH-06, REQ-AUTH-14, REQ-CONF-01,
  REQ-CONF-04, REQ-CONF-05, REQ-CONF-06, REQ-CONF-07, REQ-FS-01, REQ-FS-05,
  REQ-FS-06, REQ-PCS-01, REQ-PCS-03.
- **Proofs:**
  - The refinements take agreement hypotheses saying the opaque operations
    compute what the model's HMAC and HKDF compute: `HmacAgrees` and
    `HkdfAgrees` (`Translation/T3.lean`), `SessionT3.HkdfAgrees`,
    `SpqrHkdfAgrees`, `BraidHmacAgrees` and `BraidHkdfAgrees`.
  - The model's own HMAC and HKDF are anchored to RFC 4231 and RFC 5869 values
    (CLAIMS.md, "Evidence, not proof").
  - The symbolic theorems take one-wayness as ASM-10.

### ASM-06: the AEAD, AES-256-CBC with HMAC-SHA256

AES-256 is a pseudorandom permutation, against a classical adversary and against
ADV-03. So AES-256-CBC is IND-CPA secure for a key that encrypts one plaintext
under an IV the adversary cannot predict. HMAC-SHA256 with its full 32-byte tag
is strongly unforgeable. Their encrypt-then-MAC composition (message-format.md,
Authenticated encryption) is therefore confidential and integrity-protecting for
a key used for one message. `aes` 0.8, `cbc` 0.1, `hmac` 0.12 and `sha2` 0.10
compute FIPS 197, SP 800-38A and RFC 2104.

- **Relied on by:** REQ-AUTH-03, REQ-AUTH-06, REQ-AUTH-07, REQ-CONF-01,
  REQ-CONF-06.
- **Proofs:** none. The AEAD is a boundary primitive in the model
  (LIMITATIONS.md, "Trusted, not verified").
  `Properties.Authentication` takes unforgeability as its premise, and says so
  in its closing section.

### ASM-07: SHA-2 and SHA-3, as used

These hash functions have the collision resistance, and the other properties,
that the published analyses of the constructions using them require:
- **SHA-256:** inside HMAC and HKDF, and in the last-resort fingerprint, used as
  a keyed hash.
- **SHA-512:** inside XEdDSA.
- **SHA3-256, SHA3-512 and SHAKE:** inside ML-KEM-1024 (`libcrux-ml-kem`),
  including the hash of the encapsulation key that a Braid header carries.

A collision between two fingerprints would make the record refuse a handshake it
has not seen. That is a refusal, not an acceptance.

- **Relied on by:** REQ-AUTH-01, REQ-AUTH-12, REQ-CONF-06, and through ASM-04
  and ASM-05 every requirement those support.
- **Proofs:** none. The model computes SHA-256 only to serve as the vectors'
  oracle, and `hash_length` says its output is thirty-two bytes.

### ASM-08: constant-time execution

An adversary that measures how long an operation takes, or which code paths it
runs, learns nothing secret from it. LIMITATIONS.md, "Constant-time behaviour
is assumed, not proven", states how far this is checked:
- the primitives (the dalek crates' X25519 and Ed25519 operations, and
  `libcrux-ml-kem`) are assumed constant-time;
- the AEAD's tag comparison uses `Mac::verify_slice`;
- `mac_eq` and `calculate_key_pair` are held branch-free by
  `tooling/check-constant-time-asm.sh`, on the host and on x86_64 and aarch64
  Linux;
- `tacenta-core`'s own composition is audited by reading to branch only on
  public data;
- four rejection paths are measured by `tacenta-core/tests/timing.rs`.

- **Relied on by:** REQ-CONF-09, and against a timing observer REQ-CONF-01 and
  REQ-AUTH-06.
- **Proofs:** none. No tier constrains timing.

### ASM-09: deleted secrets cannot be recovered

A secret the protocol deletes (key-deletion.md) cannot be recovered afterwards
by an adversary that takes the state (ADV-02). This holds only as far as
erasure reaches. `tacenta-core` wipes what its erasing types hold when they
drop. It does not wipe the following (LIMITATIONS.md, "Secret deletion is
partial"):
- copies the language makes of `[u8; 32]` keys;
- copies inside `libcrux-ml-kem`'s own types;
- allocations a growing vector abandoned;
- persisted bytes (ASM-12).

Recovery from storage media is outside this specification (EX-08).

- **Relied on by:** REQ-FS-01, REQ-FS-03, REQ-FS-05, REQ-FS-06.
- **Proofs:** none. The translation ignores `Drop`, so no theorem sees
  erasure.

### ASM-10: the symbolic model is faithful

Every security theorem in `tacenta-model/Properties/` is proved against the
symbolic attacker of `Model.Adversary`, not against a computational one. In
that model a key is a term recording how it was derived, and equal only to a key
derived the same way. The attacker derives keys only by the rules given, and no
rule runs a derivation backwards. Seeds and agreement outputs are leaves, known
only to an attacker that took them.

This assumption is that the idealisation is sound for the computational
setting. That requires the key derivations to be one-way, collision-resistant
and pseudorandom (ASM-05), and fresh values never to coincide (ASM-01). It is
not proved here or anywhere in this project (LIMITATIONS.md, "Forward secrecy
is proved, against a symbolic attacker").

- **Relied on by:** REQ-AUTH-07, REQ-CONF-07, REQ-CONF-08, REQ-FS-01,
  REQ-PCS-01.
- **Proofs:** `Properties.ForwardSecrecy`, `Properties.PostCompromise`,
  `Properties.Secrecy` and `Properties.Authentication`, through
  `Model.Adversary`.

### ASM-11: the clock

No requirement assumes a clock, and the protocol reads no wall-clock time.
- **Stored keys** expire by counting accepted receives (`MAX_SKIPPED_AGE`;
  ratchet.md, Skipped keys).
- **The sparse ratchet** retires epochs by count (`EPOCHS_KEPT`;
  sparse-pq-ratchet.md, Retiring old epochs).
- **The Braid** counts epochs.

Where a published specification says "periodically" or "after an interval", the
schedule is left to the caller. That covers rotating the signed and last-resort
prekeys, and so how long a retired prekey is held (key-deletion.md, What this
implementation does not do yet). So:
- **Rotation:** the forward secrecy a rotation gives (REQ-FS-05) arrives as
  often as the caller rotates.
- **Expiry:** expiry is not a time bound. A stored key stays for as long as
  `MAX_SKIPPED_AGE - 1` further accepted receives take. Once the count stops at
  `u32::MAX - 1`, keys no longer age (session-persistence.md, Principles).

- **Relied on by:** REQ-FS-04, REQ-FS-05.
- **Proofs:** no model has a notion of time or turn-taking. The expiry
  refinement `age_store_refines` holds while the count has a step of room
  (`hroom`).

### ASM-12: storage

- **Durability, atomicity and ordering are the caller's.** Writes must happen
  in the order session-persistence.md, Principles, states:
  - persist a session before transmitting what `encrypt` produced, or a message
    key and IV are used twice after a crash;
  - persist before acknowledging what `decrypt` produced;
  - after establishing as the responder, persist the session before the prekey
    store;
  - persist the store after a rotation and before republishing.
- **Confidentiality at rest is the caller's.** Persisted bytes are plaintext
  (key-deletion.md).
- **Integrity against a writer is out of scope** (ADV-05; ADR-0007). The
  readers check against corruption.

- **Relied on by:** REQ-AUTH-12, REQ-CONF-04, REQ-FS-03.
- **Proofs:** `Translation/ImportInv.lean` says what a leaf crate's decoded
  state satisfies. No proof reaches the session's or the prekey store's
  persistence, or the order of writes.

### ASM-13: the network

The network is ADV-01's: asynchronous, unreliable and adversarial. No
requirement that something is kept secret, authenticated or refused assumes
delivery, order or timeliness.

Recovery does depend on the network:
- a message is read only if it is delivered;
- healing (REQ-PCS-01, REQ-PCS-03) needs the peer's messages to be delivered
  and the peer to send;
- a Braid epoch completes only when enough chunks have arrived in both
  directions.

- **Relied on by:** every requirement, for the adversary it holds against;
  REQ-PCS-01 and REQ-PCS-03 for recovery.
- **Proofs:** none represents a network (adversaries.md). Loss is exercised by
  tests. `tacenta-core/braid/src/tests.rs` has
  `loss_delays_agreement_without_preventing_it`, and
  `tacenta-core/tests/post_quantum_stack.rs` has
  `agreement_messages_may_be_lost_without_stopping_the_conversation`.

### ASM-14: key authenticity

The identity key a party establishes a session with belongs to the peer the
party means to reach. It is verified out of band, or under the application's
own trust policy. The directory is not trusted for authenticity: a bundle's
signatures prove only that its prekeys were published by the holder of the
bundle's identity key.

The protocol gives the caller two things to build on:
- `establish_initiator_for` refuses a bundle whose identity key is not the one
  the caller names (REQ-AUTH-02);
- a session reports its peer's identity key (`Session::peer_identity`), for the
  application to compare with the one it holds for the contact.

How identity keys are verified is not specified (EX-09).

- **Relied on by:** REQ-AUTH-01, REQ-AUTH-02, REQ-AUTH-03, REQ-CONF-01,
  REQ-CONF-06.
- **Proofs:** none. Nothing anywhere in this project proves that an identity
  key belongs to the person a user means (LIMITATIONS.md, "Forward secrecy is
  proved, against a symbolic attacker", on authentication).

## About the evidence

A requirement whose status is proved is proved about the model, or about the
translated leaf crates of `tacenta-core`. These assumptions are what that proof
depends on.

### ASM-15: the platform

- **`usize` width.** `usize` is 32 or 64 bits wide, the two widths Aeneas
  models (`Std.Usize.bounds_eq`, which `Ratchet.store_plus_skip_fits` uses).
  `tacenta-core` is checked to compile for `armv7-linux-androideabi` in CI.
- **Slice length.** A Rust slice is at most `isize::MAX` bytes, which
  discharges the codecs' length premises, such as
  `bytes.length + 72 ≤ Usize.max` (CLAIMS.md, "Proved (tier T1, the Double
  Ratchet's persistence codec cannot fail)").
- **No `unsafe`.** Every library crate carries `#![forbid(unsafe_code)]`.
- **Release builds.** A release build compiles out the `debug_assert_eq!`
  checks that the translation turns into assertions the proofs discharge. On
  those lines the Lean is stricter than the binary (LIMITATIONS.md, "Secret
  deletion is partial").
- **Constant-time checks.** The assembly gate of ASM-08 reads three targets
  and no others.

- **Relied on by:** REQ-AUTH-04, REQ-AUTH-08, REQ-AUTH-14, REQ-CONF-02,
  REQ-FS-02, REQ-FS-04.
- **Proofs:** every theorem in `tacenta-proofs/translation/`.

### ASM-16: the translation toolchain

- **The translation is faithful.** Charon and Aeneas, pinned to the Aeneas
  release `nightly-2026.07.22-b1214ca` (CLAIMS.md, "Reproduce"), translate the
  verified crates faithfully.
- **The recorded generation is honest.** It was produced by that toolchain from
  the Rust it records. `attest.py --check` holds the tree to the record, and
  only regenerating shows that the record is honest (LIMITATIONS.md, "Trusted,
  not verified").
- **Translation units.** Compiling several crates as one translation unit
  changes no function body (LIMITATIONS.md, "The three-leaf translation unit
  is an eighth zone, and it ships to nobody").

- **Relied on by:** REQ-AUTH-04, REQ-AUTH-08, REQ-AUTH-14, REQ-CONF-02,
  REQ-FS-02, REQ-FS-04.
- **Proofs:** every theorem about `Translation/Tacenta*.lean`.

### ASM-17: the Lean kernel, and proofs checked by evaluation

- **The kernel.** The Lean 4 kernel of the pinned toolchain,
  `leanprover/lean4:v4.31.0`, is sound. `leanchecker` replays every
  first-party module through it.
- **The compiler.** Where a proof uses `native_decide`, `bv_decide` or
  `decide +native`, the Lean compiler's evaluation is trusted as well.
  LIMITATIONS.md, "The proofs are trusted by evaluation, not only by the
  kernel", lists where. For example, the sparse ratchet's receive theorems and
  the Triple Ratchet's discharged refinements are compiler-trusted.
- **Mathlib.** The prebuilt Mathlib artefacts fetched for the pinned commit are
  trusted.
- **No planted declarations.** No elaboration-time code plants a declaration.
  A textual rule excludes this, not the axiom audit.

- **Relied on by:** every requirement whose status is proved: REQ-AUTH-04,
  REQ-AUTH-07, REQ-AUTH-08, REQ-AUTH-14, REQ-CONF-02, REQ-CONF-03,
  REQ-CONF-07, REQ-CONF-08, REQ-FS-01, REQ-FS-02, REQ-FS-04, REQ-PCS-01.
- **Proofs:** all of them.

### ASM-18: the boundary hypotheses of the T1 and T3 proofs

The named hypotheses the T1 and T3 theorems take about operations the
translation cannot see into hold of the real operations. They cover:
- the key derivation's agreement with the model;
- the `zeroize` wrapper's round trips;
- `Vec::remove`, `retain` and `append`;
- `Option`'s clone;
- the KEM and erasure agreements.

Each is stated under the Rust operation's own precondition. Most are witnessed
satisfiable (`Translation/Satisfiability.lean`,
`Translation/UnitSatisfiabilityTriple.lean`, `Translation/ErasureWitness.lean`,
`Translation/KemWitness.lean`). A satisfiable hypothesis is still a hypothesis
(CLAIMS.md, "Read this first: what is not proved").

- **Relied on by:** REQ-AUTH-14, REQ-CONF-02, REQ-FS-02, REQ-FS-04.
- **Proofs:** the theorems whose signatures name them. The signature is the
  authoritative list.

### ASM-19: the untranslated orchestration

`tacenta-core/src/sessions`, which is neither translated nor modelled, does what
the protocol pages say. In particular it:
- pairs the old ratchet key pair with the receiving chain and a fresh one with
  the sending chain at a Diffie-Hellman step;
- runs each receive on a copy, and adopts the copy only after the message
  authenticates;
- verifies prekey signatures before deriving;
- meets the numeric preconditions the leaf theorems pass up to it. These are
  the Triple Ratchet's four size bounds and the counters' step of headroom
  (CLAIMS.md, "Read this first: what is not proved").

This is established by tests and by reading, not by proof.

- **Relied on by:** every requirement, as a statement about `tacenta-core`; in
  particular REQ-AUTH-01, REQ-AUTH-02, REQ-AUTH-05, REQ-AUTH-09 to
  REQ-AUTH-13, REQ-CONF-02, REQ-CONF-04, REQ-CONF-09, REQ-FS-03 and
  REQ-PCS-02, whose evidence is at that layer.
- **Proofs:** none. It is where their preconditions land.
