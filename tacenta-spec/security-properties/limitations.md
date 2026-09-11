# Limitations

The known gaps in the security properties this directory states: what is not
proved, not tested or not given, within the scope threat-model/exclusions.md
leaves. Each gap is numbered so that a requirement can name it.

`tacenta-proofs/LIMITATIONS.md` is the record of what the proofs trust and do
not reach. `tacenta-proofs/CLAIMS.md`, "Read this first: what is not proved",
summarises it. Each item below cites where that record discusses the gap.
Nothing here narrows a requirement; it says how far the evidence for one goes.

## How the requirements stand

Of the 32 requirements:
- **12 are proved.** Five of them are proved in the model against a symbolic
  attacker, and are not recorded in CLAIMS.md (LIM-01, LIM-02).
- **9 are assumed.**
- **11 are tested only.** One of them has no test yet (LIM-13).

| Requirement | Status |
|---|---|
| REQ-AUTH-01: prekey signatures are verified before use | Tested only |
| REQ-AUTH-02: a named identity is enforced | Tested only, no test yet |
| REQ-AUTH-03: the shared secret binds both identities | Assumed |
| REQ-AUTH-04: the associated data determines both identities | Proved (T2, T3) |
| REQ-AUTH-05: every message's associated data covers the whole header | Tested only |
| REQ-AUTH-06: a message is accepted only if its tag verifies | Assumed |
| REQ-AUTH-07: a key determines its session and position | Proved, model-level, symbolic |
| REQ-AUTH-08: decoders refuse re-spelled curve keys | Proved (T3, T1) |
| REQ-AUTH-09: decoders accept one encoding of each value | Tested only |
| REQ-AUTH-10: non-contributory agreements are refused | Tested only |
| REQ-AUTH-11: a ratchet message is accepted at most once | Tested only |
| REQ-AUTH-12: an initial message is not accepted twice | Tested only |
| REQ-AUTH-13: unauthenticated input changes nothing durable | Tested only |
| REQ-AUTH-14: an authenticator failure ends the agreement | Proved (T3) |
| REQ-CONF-01: messages are confidential against an outsider | Assumed |
| REQ-CONF-02: the key schedule is the specified one | Proved (T3) |
| REQ-CONF-03: PQXDH's derivation input is unambiguous | Proved (T2) |
| REQ-CONF-04: no key and IV encrypt twice | Assumed |
| REQ-CONF-05: the encryption key needs both message keys | Assumed |
| REQ-CONF-06: recorded traffic stays confidential against a future quantum adversary | Assumed |
| REQ-CONF-07: a message key reveals no other key | Proved, model-level, symbolic |
| REQ-CONF-08: one session reveals nothing of another | Proved, model-level, symbolic |
| REQ-CONF-09: a refusal reveals only that it was a refusal | Tested only |
| REQ-FS-01: a chain key does not reveal the chain's past | Proved, model-level, symbolic |
| REQ-FS-02: spent keys are replaced in the state | Proved (T3) |
| REQ-FS-03: spent secrets are erased from memory | Tested only |
| REQ-FS-04: stored keys are bounded and expire | Proved (T2, T3) |
| REQ-FS-05: the handshake is forward secret once a prekey secret is gone | Assumed |
| REQ-FS-06: replaced chains stay secret | Assumed |
| REQ-PCS-01: a fresh agreement heals the classical ratchet | Proved, model-level, symbolic |
| REQ-PCS-02: a step uses a fresh key pair, paired as specified | Tested only |
| REQ-PCS-03: a completed epoch heals the post-quantum ratchet | Assumed |

## The proofs

### LIM-01: the security theorems are symbolic

REQ-AUTH-07, REQ-CONF-07, REQ-CONF-08, REQ-FS-01 and REQ-PCS-01 are proved
against the symbolic attacker of `Model.Adversary`, not a computational one.
Against a real attacker they hold only if the idealisation is sound (ASM-10).
Nothing in this project proves that. See LIMITATIONS.md, "Forward secrecy is
proved, against a symbolic attacker" and "Not yet proven".

### LIM-02: model-level theorems not recorded in CLAIMS.md

Several theorems cited as proved are kernel-checked by the build.
`scripts/no-sorry.sh` builds and audits the model package, `Properties/`
included, and the `Proofs/` package. The theorems are these:
- in `tacenta-model/Properties/`: `Authentication`, `ForwardSecrecy`,
  `PostCompromise`, `Secrecy` and `StateConsistency`;
- in `tacenta-proofs/Proofs/`: `KeyErasure`, `MemorySafety` and
  `SparseRatchetCorrectness`.

None of them is recorded in CLAIMS.md. That ledger says the four security
properties are deliberately absent. No `#guard_msgs` pin fixes their axiom
bases, and `attest.py --check` does not check their names. So the
requirements' citations of them were checked by hand. Tracing them through
CLAIMS.md is not yet possible.

### LIM-03: one chain or one step, not a session

The symbolic theorems are about one chain, or one root step, as terms. They
are not related to `Model.State`, so nothing is proved about the following:
- a sequence of root steps;
- chains interleaving;
- a state holding several keys at once;
- the attacker holding more than one key.

REQ-FS-06 is assumed for that reason. See LIMITATIONS.md, "Forward secrecy is
proved, against a symbolic attacker".

### LIM-04: no security theorem about the post-quantum half

No symbolic model covers the sparse ratchet, the Braid or the combination of
message keys. So REQ-CONF-05, REQ-CONF-06 and REQ-PCS-03 are assumed. The
theorems of REQ-CONF-07 and REQ-FS-01 reach only the classical chain. What is
proved about the post-quantum half is refinement: T1 and T3.

### LIM-05: the session layer is not proved

`Session::encrypt`, `Session::decrypt` and the rest of
`tacenta-core/src/sessions` are neither translated nor modelled (CLAIMS.md,
"Read this first: what is not proved"; LIMITATIONS.md, "Eight verified zones
on the shipping path, and the orchestration runs outside them", and "Scope").
Several behaviours live there and are tested only:
- which key pair each Diffie-Hellman ratchet output is computed with
  (REQ-PCS-02);
- adopting a receive's state only after authentication (REQ-AUTH-13);
- verifying prekey signatures (REQ-AUTH-01);
- deleting one-time prekeys, and keeping the last-resort record (REQ-AUTH-12);
- refusing after the agreement fails (REQ-AUTH-14).

CLAIMS.md and LIMITATIONS.md say a session-level test of the key pairing "is
being added". `a_session_dh_step_pairs_the_old_key_with_the_peers_new_key`
exists, and checks the pairing by running a session rather than against a model
scenario.

### LIM-06: primitives and boundary hypotheses

X25519, XEdDSA, ML-KEM-1024, HMAC, HKDF, AES and the hashes are opaque in every
proof (ASM-02 to ASM-07). The T1 and T3 theorems take boundary hypotheses about
opaque operations (ASM-18). These are witnessed satisfiable, but not shown to
hold of the real operations.

The KEM carries two further limits:
- The model's `Kem.Correct` rounds ML-KEM's decapsulation-failure probability
  to zero.
- `validate_ek` checks the public half of a stored key pair only. About half of
  the private half cannot be checked from its bytes.

See LIMITATIONS.md, "Trusted, not verified", and its passages on the Braid's
erasure and KEM hypotheses.

### LIM-07: refinement premises are left with the caller

The T3 theorems behind REQ-CONF-02, REQ-FS-02, REQ-FS-04 and REQ-AUTH-14 carry
premises that no invariant discharges, and that land on the untranslated
session layer:
- **Counter headroom:** `events + 1 < u32::MAX` on the classical `receive`;
  `epoch + 1 < u64::MAX` on the sparse ratchet and the Braid; and the sparse
  ratchet's `hcounter`, `hcb`, `hsb` and `hnewb`.
- **Size bounds:** the Triple Ratchet's four size preconditions.
- **The Braid's `EncodersLive` and `HonestChunk`:** a sending encoder is live,
  and received chunks come from one message.

A premise that is satisfiable is not thereby satisfied by every state. The
parked expiry count is an ordinary state that the clock premise excludes. See
CLAIMS.md, "Read this first: what is not proved", and LIMITATIONS.md, "The
three-leaf translation unit is an eighth zone, and it ships to nobody".

### LIM-08: canonical decoding is not proved at the model level

The decoders refine models that are built to accept one spelling of each value
(REQ-AUTH-08). The model-level statement is not proved: that a decoded value
re-encodes to the bytes it was decoded from. So REQ-AUTH-09 is tested only. See
CLAIMS.md, "Proved (tier T2, the composite header's round trip)", and
triple-ratchet.md, Sending and receiving.

### LIM-09: less independence for the composition

`Model.Triple` is written from `tacenta-core/triple/src/lib.rs` as well as from
triple-ratchet.md. So the Triple Ratchet's refinement checks the crate against
a model read off the same crate.

Two further limits apply. The unit that refinement is proved on is one crate
where the shipping build has three. And its proofs are hand-written.

See CLAIMS.md, "Proved (tier T3, the Triple Ratchet's composed session on the
unit, with both inner bundles discharged)", and LIMITATIONS.md, "The three-leaf
translation unit is an eighth zone, and it ships to nobody".

### LIM-10: trusted toolchain and evaluation

Every proved requirement rests on the Lean kernel (ASM-17) and every T1 or T3
requirement on the translation toolchain (ASM-16).

Several cited theorems also trust the Lean compiler's evaluation:
- the sparse ratchet's `receive_refines`;
- `Tacenta.UnitTripleT3.send_refines_discharged` and
  `receive_refines_discharged`;
- `Tacenta.UnitTripleT3.combine_refines` and `split_secret_refines`.

See LIMITATIONS.md, "The proofs are trusted by evaluation, not only by the
kernel", and "Trusted, not verified".

## Implementation evidence

### LIM-11: erasure is partial and unproved

REQ-FS-03 rests on erasure the proofs cannot see (ASM-09), and it is partial:
- copies of `[u8; 32]` keys the language makes;
- copies inside `libcrux-ml-kem`;
- allocations a growing vector abandoned, including in the sparse ratchet's
  `from_bytes`;
- persisted bytes.

A compile-time test holds erasure in place for three places only: the
classical ratchet's `State`, the KEM `KeyPair`, and `Identity` with
`PrekeyStore`. The sparse ratchet's, the Triple Ratchet's and the Braid's types
erase through derived destructors that no test holds in place. LIMITATIONS.md,
"Secret deletion is partial", describes the guard as "a static check per
crate", which is more than the tree has.

### LIM-12: constant time is assumed, and measured in part

REQ-CONF-09 rests on ASM-08.
- **Measured:** four rejection paths, nightly. The two nanosecond-scale
  results recorded so far carry no provenance stamp.
- **Checked by the assembly gate:** two hand-written functions, on three
  targets.
- **Not measured:** the primitives.
- **Not wired:** a formal secret-independence check.

See LIMITATIONS.md, "Constant-time behaviour is assumed, not proven".

### LIM-13: a requirement with no test

REQ-AUTH-02 is stated by session-establishment.md and made by
`establish_initiator_for`. No test or vector in the tree exercises the refusal
(`UnexpectedIdentity`).

### LIM-14: no proof about cost

T1 and T3 are functional. No proof constrains running time, memory, or work
per byte of input. Denial of service is covered only by fuzzing and
measurement. See LIMITATIONS.md, "What a green proof does not say about cost",
and exclusions.md, EX-03.

## What the requirements give

### LIM-15: the limits of authentication

- REQ-AUTH-06 and REQ-AUTH-07 rest on the AEAD's unforgeability (ASM-06).
- Nothing proves that an identity key belongs to the person a user means
  (ASM-14; EX-09).
- An attacker holding a responder's signed prekey secret can make initial
  messages that responder accepts as coming from any identity, until the
  prekey is deleted (REQ-AUTH-03).
- One-time curve prekeys are not signed (REQ-AUTH-01).
- `EncodeKEM(PQPKB)` is left out of the associated data, which relies on
  ML-KEM binding its key. session-establishment.md records that as an open
  question.
- Authentication is classical only (EX-11).

See LIMITATIONS.md, "Forward secrecy is proved, against a symbolic attacker",
on authentication.

### LIM-16: healing has no bound

- A party that only sends never takes a Diffie-Hellman step.
- A Braid epoch needs traffic both ways, about a hundred messages at these
  parameters.
- An active attacker that holds the compromised state while the healing step
  happens can supply its own agreement, and nothing heals.
- An attacker holding a ratchet private key, or the Braid's authenticator
  keys, follows every step (REQ-PCS-01, REQ-PCS-03).

### LIM-17: a chain's future, and long-lived keys

An attacker holding a chain key derives every later key of that chain
(`Properties.ForwardSecrecy.future_message_keys_are_exposed`). Compromise of an
identity secret, a signed prekey or a last-resort KEM prekey is repaired by no
ratchet. Only rotation replaces a prekey, and the caller decides when
(ASM-11).

### LIM-18: stored keys and the expiry count

- A stored skipped key is exposed to ADV-02 until it is used, expired or
  evicted.
- Expiry counts accepted receives, not time.
- Once the count stops at `u32::MAX - 1`, keys no longer age, and stay until
  evicted.
- A peer can age out or evict stored keys, and a delayed message whose key was
  evicted is lost (REQ-FS-04).

See LIMITATIONS.md, "Not yet proven", on the store's clock.

### LIM-19: the last-resort replay record

The record's per-key budget fails closed. Anyone holding the bundle can fill it
cheaply, after which last-resort handshakes naming that key are refused.
Rotation opens a fresh budget, and a determined attacker spends that too.
Refusing replays depends on the persisted record being written in order and
not rolled back (REQ-AUTH-12; key-deletion.md).

### LIM-20: persistence

Persisted state is plaintext, and its protection at rest is the caller's. So
are the order and durability of writes. A crash between transmitting a message
and persisting the session can make a session encrypt twice under one key and
IV (REQ-CONF-04). No requirement holds against a writer of the store (ASM-12;
EX-07).

### LIM-21: the Braid

- **An epoch key is not a session key.** It is safe only mixed into the sparse
  ratchet. A test pins that it does not depend on the preshared secret:
  `the_epoch_key_does_not_depend_on_the_preshared_secret`
  (`tacenta-core/braid/src/tests.rs`).
- **Spliced chunks.** A spliced chunk is outside the refinement theorems.
- **A malicious peer can fail the agreement.** The session then refuses to
  encrypt or decrypt until it is established again.
- **Encoder lifetime.** An encoder emits at most 65,536 codewords.

See mlkem-braid.md, "Failure" and "Properties a caller must know", and
LIMITATIONS.md on the Braid's erasure and KEM hypotheses.

### LIM-22: not properties at all

Metadata (EX-01), deniability (EX-12), groups (EX-04) and devices (EX-05) are
outside this specification. No requirement here says anything about them.
