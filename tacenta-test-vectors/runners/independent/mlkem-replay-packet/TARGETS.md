# Targets: what to compute, from where, and against what

Companion to `README.md`. Paths are relative to the directory you were given.
Vector files are under `tacenta-test-vectors/vectors/`; pages are under
`tacenta-spec/protocol/`. `run.py` is
`tacenta-test-vectors/runners/independent/reader/run.py`.

Conventions the vectors use are in `tacenta-test-vectors/README.md`, Vector
layouts: every byte string is lowercase hex and every integer is big-endian.
The session vectors are in `session-establishment/session-e2e.json`, two vectors
(`one-time-prekeys-first-message` and `last-resort-first-message`), each with
`inputs` and `fields`. The identity vector is in `identity/initial-message-admission.json`.

The reader can already parse every stored and wire format named below
(`tacenta_reader/persistence.py`, `tacenta_reader/wire.py`). Use it for that, or
parse from the page.

## K: ML-KEM-1024 (FIPS 203)

Pages: `session-establishment.md`, Primitives, and what is left to them,
ML-KEM-1024 (FIPS 203); `session-persistence.md`, Prekey store (`kem_pair`);
`message-format.md`, Prekey bundle and Initial message. The standard is FIPS 203
(parameter set ML-KEM-1024, Table 2): ML-KEM.KeyGen_internal is Algorithm 16,
ML-KEM.Encaps_internal Algorithm 17, ML-KEM.Decaps_internal Algorithm 18.

| ID | Compute | From | Compare with | Today |
|---|---|---|---|---|
| K1 | The key pair from `d \|\| z`: `ek` (1,568 bytes) and `dk` (3,168 bytes) | `bob_last_resort_kem_d_z` in both vectors; `bob_one_time_kem_d_z` in `one-time-prekeys-first-message` | The KEM prekey in `bundle`. Then `bob_prekey_store_after_receipt`: its `kem_pair` is `dk \|\| ek` (4,736 bytes), the last-resort key. | Taken from the vector; only the FIPS 203 checks and the signature are made |
| K2 | Encapsulation of `m` to the bundle's `ek`: ciphertext (1,568) and shared secret (32) | The bundle's KEM prekey and `alice_kem_encapsulation_m` (32 bytes) | `kem_ciphertext` and `kem_shared_secret`; the same ciphertext is the `kem_ciphertext` field of `initial_message` | Both taken from the vector; ciphertext length checked |
| K3 | Decapsulation of the ciphertext with `dk` | `dk` from K1 (the first 3,168 bytes of a stored `kem_pair` is the same `dk`, but the one-time key is not stored after receipt, so only K1 reaches it) and `kem_ciphertext` | `kem_shared_secret`; it must equal K2's | Not computed |
| K4 | `SK` and everything after it, from the computed secret | K2 on the initiator's side, K3 on the responder's | `sk`, `split_ec`, `split_pq`, `mk_ec`, `mk_pq`, `mk`, `aead_output`, `initial_message` | Computed, but from the vector's `kem_shared_secret` |
| K5 | A control no vector pins: decapsulation of a ciphertext with one byte changed gives a 32-byte value, not an error, different from the real secret and equal to the page's `J(z \|\| CT)` (`session-establishment.md`, Decapsulation; FIPS 203 section 4.1 and Algorithm 18) | Any key pair and ciphertext | Report it as CHECKED (control, no vector) | Not computed |

Notes.

- In `one-time-prekeys-first-message` the bundle names the one-time KEM prekey
  (identifier 4) and the stored pair after receipt is the last-resort key
  (identifier 3). K1 therefore reaches the one-time key through the bundle and
  the last-resort key through the store. The one-time `dk` is not stored after
  receipt: K3 uses the `dk` from `bob_one_time_kem_d_z`.
- In `last-resort-first-message` the bundle names the last-resort key
  (identifier 2); its `ek` is the `ek` half of the stored pair.
- The prekey store's layout (`dk` then `ek`, and `dk`'s own layout) is in
  `session-persistence.md`, Prekey store. The reader's
  `persistence.prekey_store_from_bytes` returns the `kem_pair` field.
- Compare K1 to K3 against published FIPS 203 known-answer vectors first, if you
  can obtain them. Then a mismatch with the project vectors is not an error in
  your KEM.

## B: the Braid's key generation

Pages: `mlkem-braid.md`, The KEM split, Parameters and derivations (the
ratcheted authenticator, `Init`, `Update`, `MacHdr`), Sending (transition 1),
and The erasure code (Chunks); `session-persistence.md`, Session and Braid
(`KeysSampled`, tag 1, and the encoder layout); `message-format.md`, Ratchet
message. The input is `alice_braid_keygen_d_z` (64 bytes) in both vectors.

| ID | Compute | Compare with | Today |
|---|---|---|---|
| B1 | Key generation from `d \|\| z`; `header` = `rho \|\| H(ek)` (64 bytes) and `ek_vector` (1,536 bytes) | Used by B2. Self-check: `H(ek_vector \|\| rho)` equals the header's hash and `ek_vector` passes the modulus check (the page's validation) | Not computed |
| B2 | The 96-byte value `header \|\| MacHdr(1, header)`, with the authenticator from `Init(1, SK)` and `SK` from the vector's `sk` | The three chunks of the header encoder (`hdr_enc`) inside the Braid of `alice_session_after_first_send`, and codeword 0 in `composite_header` (the last four fields; chunk index 0, the first 32 bytes of the value) | The value is taken from the stored encoder and only its MAC is checked |
| B3 | `ek_vector` appears in no field except inside the stored `key_pair`; B1's self-check is the only check. Report MATCHED when the self-check passes, and say it is a self-check | Nothing in the vector outside `key_pair` | Not computed |
| B4 | The 11,872-byte `key_pair` of `alice_session_after_first_send`. Outside the task: its layout is delegated to the KEM library (`session-persistence.md`, Braid; ADR-0006 point 5), and the item excludes it | Not attempted. Report DELEGATED, and list in the gap report anything about the delegation that the text leaves unclear. Do not read the field's bytes to find the layout. | Not checked |

Notes.

- The authenticator's `Init(1, SK)` and the MAC are already in the reader
  (`braid.Auth`), as `session_e2e.py` uses them.

## I: the identity vector

Vector: `identity/initial-message-admission.json`, vector
`honest-initial-message`. Inputs `bob_identity_secret` (32 bytes),
`prekey_store` (a stored prekey store, `session-persistence.md`, Prekey store)
and `initial_message` (`message-format.md`, Initial message). The vector's
`output`, the plaintext the responder recovers, is 17 bytes.

Pages: `session-establishment.md`, Receiving the initial message and The replay
identity; `identities-and-devices.md`, Identity keys; `triple-ratchet.md`,
Initialisation; `ratchet.md`; `sparse-pq-ratchet.md`; `message-format.md`,
Authenticated encryption and Associated data.

| ID | Compute | Compare with | Today |
|---|---|---|---|
| I1 | The plaintext: find the KEM key the message names in the store, decapsulate (K3), derive the responder's Diffie-Hellman values and `SK`, initialise the responder and receive the ratchet message | The vector's `output` | Skipped. The reader runs the steps before decapsulation (`tacenta_reader/admission.py`) and stops. |
| I2 | The ten refused vectors in the same file keep their verdicts | Each vector's `refusal` | Pass today |

Notes.

- This store holds a one-time curve prekey, a one-time KEM prekey (the one the
  message names) and a last-resort KEM prekey. The `kem_pair` is stored, so no
  key generation is needed here, only decapsulation.
- The steps after `SK` are the ones `session_e2e.py` already runs for the
  session vectors, in the block headed "Bob: the session, from the message that
  opens it" (`triple.init_responder`, `triple.decrypt`, `braid.BraidAgreement`,
  `braid.init_responder`). The Braid's first receive on the responder's side
  needs no KEM.
- The vector has no input for the responder's fresh ratchet secret, which the
  first receive draws. Choose 32 bytes and say what you chose.
- The page says the prekey store is read-only until the ratchet message has
  authenticated. The vector pins only the plaintext.
- When this passes, remove the skip: `EXPECTED_SKIPS` in `run.py` holds the one
  label, `identity/initial-message-admission.json :: honest-initial-message`.

## R: keep the reader's gates true

| ID | Change | Why |
|---|---|---|
| R1 | Remove the vector's entry from `EXPECTED_SKIPS` in `run.py` once I1 passes, and move its reason out of the comment | The gate fails on an unexpected skip and on an expected one that does not occur |
| R2 | Update the tally sentences in `reader/README.md` that `run.py` checks (`documented_tally_problems`). They are in two places, the tally table and the bold sentence in the Pass 11 record, and the prose beside the table that speaks of the one skip is rewritten by hand. The run prints each missing sentence exactly. The check against `GAPS-11.md` does nothing in your directory, which does not hold that file | The gate compares them with the run's totals |
| R3 | Update `UNREAD_INPUTS` and the module docstring of `session_e2e.py` to what the code now reads. `UNREAD_INPUTS` names whole inputs; if you read only part of an input, the sweep has to learn byte ranges for inputs | The sweep requires every input and field the module says it reads to be noticed |
| R4 | Update the unchecked ranges in `test_session_e2e_sweep.py` (`unchecked_ranges`) to what remains unchecked. The sweep samples positions; once a region becomes checked, add sample positions inside it and require them to be noticed, or a green sweep says nothing about the newly covered bytes | The sweep fails if a byte called unchecked is noticed, and if a byte called checked is not |
| R5 | Run the three commands in `README.md`, Output, and save their output under `run-output/` | The record cites it |

## Order and effort

Order: K1 to K3 and K5 first (the largest item, and I and B depend on it), then
K4 on the project vectors, then B1 and B2, then B3 as the self-check and B4 as
delegated, then I1, then R1 to R5, then the record and the gap report.

The estimate below is the project's judgement, made after it ran this brief
itself. It is not measured on a person. It is for someone who has never seen the
project, has this packet and FIPS 203, and writes ML-KEM from the standard with
the published known answers to check it:

| Part | Hours | What drives it |
|---|---|---|
| Reading before starting: the packet, `session-establishment.md`, `mlkem-braid.md`, `session-persistence.md` (Prekey store, Braid), the vectors README sections, the reader's structure | 5 to 7 | About 3,500 lines, most of it not on the critical path; the reader's Provenance section is long and is only needed for the isolation form |
| K: ML-KEM-1024 from FIPS 203, a harness over the published files, then K1 to K5 on the project vectors | 8 to 14 | The NTT with its bit-reversed order, byte encoding and compression, the sampling procedures and the key-generation details account for most of it. The published files turn a wrong guess into a failing case quickly. Once K works the project vectors take 1 to 2 hours |
| B: B1 and B2, B3 as a self-check | 2 to 3 | B1 is a few lines once key generation exists. B2 needs the authenticator and the stored encoder layout, which the reader already parses |
| I: decapsulate, derive `SK`, receive the ratchet message, change the handler | 2 to 4 | Finding the responder block in `session_e2e.py`, and reading the handler's refusal paths so the ten refused vectors keep their verdicts |
| R: allowlist, README tallies, `UNREAD_INPUTS` and the sweep | 3 to 5 | The sweep change is most of it; each sweep run is about 40 seconds |
| Record and gap report | 3 to 5 | Judging severity takes time |
| **Total** | **23 to 38** | Three to five working days. A person who stops after K and B spends about 18 to 26 |

If a person were allowed an existing ML-KEM library the K line would fall to one
or two hours, and the isolation rule forbids it.
