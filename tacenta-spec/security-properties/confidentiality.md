# Confidentiality

Confidentiality guarantees, as numbered requirements: message plaintexts, and
the keys that protect them, are kept from the adversaries of
threat-model/adversaries.md. What an adversary that has taken a party's state
can and cannot read is on the forward-secrecy and post-compromise-security
pages.

## How the requirements are stated

Each requirement has a statement and five entries:

- **Protects:** the assets (threat-model/assets.md).
- **Holds against:** the adversaries (threat-model/adversaries.md).
- **Rests on:** the assumptions (threat-model/assumptions.md).
- **Status:** one of three.
  - *Proved* names the theorem, its tier and the section of
    `tacenta-proofs/CLAIMS.md` that records it.
  - *Assumed* names the assumptions that carry it, and anything proved
    beneath it.
  - *Tested only* names the tests or vectors.
- **Does not cover:** what a reader might take it to cover.

A proved requirement is proved about the model, or about the translated leaf
crates of `tacenta-core`. It is not proved about that implementation's session
layer (ASM-19; limitations.md, LIM-05).

### REQ-CONF-01: messages are confidential against an outsider

An adversary that holds none of a session's secrets learns nothing about the
plaintext of a message sent in it, beyond its length to within a block and the
fact that it was sent.

- **Protects:** AS-01.
- **Holds against:** ADV-01, ADV-04. ADV-06 only in the victim's other
  sessions.
- **Rests on:** ASM-01, ASM-02, ASM-04, ASM-05, ASM-06, ASM-08, ASM-14.
- **Status: assumed.**
  - ASM-02 or ASM-04 carries the secrecy of `SK`.
  - ASM-05 carries the key schedule.
  - ASM-06 carries the encryption.

  REQ-CONF-02 is what is proved beneath it.
- **Does not cover:**
  - Metadata, and the length of a plaintext (EX-01).
  - An adversary that has taken a party's state (forward-secrecy.md,
    post-compromise-security.md).
  - A substituted identity key that nobody catches (ASM-14).
  - Persisted state (EX-07).

### REQ-CONF-02: the key schedule is the specified one

An implementation derives the keys the pages specify:
- `SK`, from the agreement outputs, and its split into two halves;
- both ratchets' root, chain and message keys;
- the combination of the two message keys;
- the expansion of the combination into `enc_key`, `mac_key` and `iv`;
- the Braid's epoch keys and authenticator.

- **Protects:** AS-04 to AS-08.
- **Holds against:** this is not a property against an adversary. It is the
  correctness the other requirements on this page rest on: a derivation that
  differed from its page would make them statements about a different
  protocol.
- **Rests on:** ASM-15, ASM-16, ASM-17, ASM-18, ASM-19.
- **Status: proved (T3),** for the translated leaf crates:
  - "Proved (tier T3, the PQXDH derivation refines the model)":
    `shared_secret_refines_none`, `shared_secret_refines_some`.
  - "Proved (tier T3, the classical Double Ratchet refines the model)":
    `kdf_ck_refines`, `kdf_rk_refines`, `message_keys_refines`,
    `send_refines`, `receive_refines`.
  - "Proved (tier T3, the sparse post-quantum ratchet's translated code refines
    the model)": `kdf_init_refines`, `send_refines`, `receive_refines`.
  - "Proved (tier T3, the Triple Ratchet's composed session on the unit, with
    both inner bundles discharged)": `Tacenta.UnitTripleT3.split_secret_refines`,
    `Tacenta.UnitTripleT3.combine_refines`,
    `Tacenta.UnitTripleT3.send_refines_discharged`,
    `Tacenta.UnitTripleT3.receive_refines_discharged`.
  - "Proved (tier T3, the ML-KEM Braid's translated code refines the model)":
    `Braid.send_refines`, `Braid.receive_refines`.

  The model-generated vectors pin the model's derivations against
  `tacenta-core` (CLAIMS.md, "Evidence, not proof").
- **Does not cover:**
  - The agreement outputs and the KEM shared secret. Every proof takes them as
    bytes.
  - Which key pair each Diffie-Hellman ratchet output is computed with
    (REQ-PCS-02).
  - The AEAD, which only the vectors in `tacenta-test-vectors/vectors/aead/`
    pin.
  - The Braid's MACs, which no vector pins (mlkem-braid.md, Parameters and
    derivations).
  - A state at a counter's last step, which the refinements' headroom premises
    exclude (limitations.md, LIM-07).
  - `Session::encrypt` and `Session::decrypt` as a whole (limitations.md,
    LIM-05).

### REQ-CONF-03: PQXDH's derivation input is unambiguous

Two different tuples of agreement outputs never reach PQXDH's key derivation as
the same input, with or without a one-time curve prekey
(session-establishment.md, Sending the initial message).

- **Protects:** AS-04.
- **Holds against:** an adversary that tries to make two handshakes present
  the same input to the key derivation.
- **Rests on:** ASM-17.
- **Status: proved (T2).**
  - `km_determines` and `km_none_ne_some` (CLAIMS.md, "Proved (tier T2,
    PQXDH's input keying material)").
  - The code builds the input as the model does: `km_refines_none` and
    `km_refines_some` (T3, "Proved (tier T3, the PQXDH derivation refines the
    model)").
- **Does not cover:** a collision of the key derivation itself (ASM-05).

### REQ-CONF-04: no key and IV encrypt twice

No `enc_key` and `iv` pair encrypts more than one plaintext.
- Each send advances the sending chains of both ratchets.
- Each message key is used for one message.
- A send at a counter's ceiling is refused rather than wrapped (ratchet.md,
  Sending and receiving; sparse-pq-ratchet.md, Sending).

- **Protects:** AS-01, AS-08.
- **Holds against:** ADV-01.
- **Rests on:** ASM-05, ASM-12, ASM-19.
- **Status: assumed (ASM-05, ASM-12).** Proved beneath it:
  - a send advances `Ns` by one:
    `Properties.StateConsistency.send_advances_ns` (T2, CLAIMS.md, "Proved
    (tier T2, the classical ratchet model's counters and transitions)");
  - the classical and sparse sends refine their models: `send_refines` (T3, in
    the two sections REQ-CONF-02 names);
  - message keys at distinct positions are distinct terms (REQ-AUTH-07).

  That distinct positions give distinct bytes is ASM-05. That a restart never
  makes a session send twice from one state is ASM-12.
- **Does not cover:** a store written out of order (ASM-12), or rolled back
  (EX-07). Either can bring back a state that has already sent.

### REQ-CONF-05: the encryption key needs both message keys

The key that encrypts a message is derived from both the classical and the
post-quantum message key (triple-ratchet.md, What the combination must be). An
adversary that knows one of the two, and not the other, learns nothing about
the result.

- **Protects:** AS-08, AS-01.
- **Holds against:** an adversary that has broken the classical half or the
  post-quantum half, including ADV-03.
- **Rests on:** ASM-05.
- **Status: assumed (ASM-05).** Proved beneath it: the code computes the
  combination as the model does. That is `Tacenta.UnitTripleT3.combine_refines`
  (T3, CLAIMS.md, "Proved (tier T3, the Triple Ratchet's composed session on
  the unit, with both inner bundles discharged)"); it is compiler-trusted and
  not pinned. The vectors in
  `tacenta-test-vectors/vectors/post-quantum/triple.json` pin the derivation.
- **Does not cover:** an adversary that knows both message keys.

### REQ-CONF-06: recorded traffic stays confidential against a future quantum adversary

Every message key combines a classical message key with a sparse ratchet key.
The sparse ratchet starts from the second half of `SK`, which depends on `SS`,
and it is reseeded by the Braid's epoch keys, which depend on ML-KEM shared
secrets. So an adversary that later computes every X25519 private key of the
recorded traffic, and breaks none of ML-KEM-1024, HKDF, HMAC or AES-256, learns
no plaintext.

- **Protects:** AS-01.
- **Holds against:** ADV-03.
- **Rests on:** ASM-01, ASM-04, ASM-05, ASM-06, ASM-07, ASM-14.
- **Status: assumed (ASM-04, ASM-05, ASM-06).** No proof covers it
  (limitations.md, LIM-04).
- **Does not cover:**
  - An adversary with a quantum computer while a handshake runs. It can
    impersonate a party, and then reads what it is sent (EX-11).
  - A compromise of a party's state (ADV-02). Post-quantum healing from one is
    REQ-PCS-03.
  - Metadata (EX-01).

### REQ-CONF-07: a message key reveals no other key

An adversary holding one message key derives no other message key, earlier or
later, and not the chain key it came from.

- **Protects:** AS-05, AS-08.
- **Holds against:** ADV-02 taking one message key, then acting as ADV-01.
- **Rests on:** ASM-05, ASM-10, ASM-17.
- **Status: proved, model-level, against the symbolic attacker.**
  `Properties.Secrecy.message_keys_are_independent` and
  `Properties.Secrecy.a_message_key_does_not_expose_its_chain` (T2, CLAIMS.md,
  "Proved (tier T2, model-level security properties against the symbolic
  attacker)").
- **Does not cover:**
  - Bytes, as opposed to terms (ASM-10).
  - The plaintext that key opens.
  - The sparse ratchet's message keys and their combination, which the
    symbolic model does not state (limitations.md, LIM-04).
  - A session, as opposed to one chain (limitations.md, LIM-03).

### REQ-CONF-08: one session reveals nothing of another

An adversary holding a chain key of one session derives no chain key, and no
message key, of a session seeded differently.

- **Protects:** AS-01, AS-05, AS-08.
- **Holds against:** ADV-02 taking one session's chain key; ADV-06, towards
  the victim's other sessions.
- **Rests on:** ASM-01, ASM-10, ASM-17.
- **Status: proved, model-level, against the symbolic attacker.**
  `Properties.Authentication.no_cross_session_chain` and
  `Properties.Authentication.no_cross_session_message` (T2, CLAIMS.md, "Proved
  (tier T2, model-level security properties against the symbolic attacker)").
- **Does not cover:**
  - What sessions share: a party's identity secret and its signed and
    last-resort prekeys (AS-02, AS-03), whose compromise reaches every session
    made with them (REQ-FS-05).
  - Bytes, as opposed to terms (ASM-10).
  - A session, as opposed to one chain (limitations.md, LIM-03).

### REQ-CONF-09: a refusal reveals only that it was a refusal

A refusal tells a peer only that its message was not accepted. The AEAD
compares its tag in constant time and decrypts nothing before the tag
verifies, so a padding refusal cannot be told from a tag refusal
(message-format.md, Authenticated encryption and Rejection).

- **Protects:** AS-01, AS-08.
- **Holds against:** ADV-01 observing refusals and how long they take.
- **Rests on:** ASM-08, ASM-19.
- **Status: tested only.**
  - The padding vectors in `tacenta-test-vectors/vectors/aead/aead-decrypt.json`:
    `padding-byte-zero`, `padding-byte-seventeen`, `padding-bytes-disagree` and
    `last-byte-sixteen-rest-not`.
  - Four timing tests in `tacenta-core/tests/timing.rs`, run nightly:
    `the_tag_comparison_does_not_leak_how_much_of_the_tag_was_right`,
    `a_forged_ciphertext_rejects_in_time_independent_of_its_contents`,
    `the_braid_header_mac_does_not_leak_how_much_of_the_mac_was_right` and
    `the_session_rejection_path_does_not_leak_how_much_of_the_tag_was_right`.
  - `tooling/check-constant-time-asm.sh`.
- **Does not cover:**
  - The primitives' own timing (ASM-08).
  - The cost of a forged message claiming a far-future number. It is
    observable, and bounded by `MAX_SKIP` (EX-03).
  - What an application reveals about a refusal.
