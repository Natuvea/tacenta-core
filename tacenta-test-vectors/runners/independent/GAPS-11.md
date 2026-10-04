# Independent reader: pass 11 record

**Date:** 2026-09-27, revised 2026-09-29 after a hostile-lens review of the pull
request that added it.

This is a maintenance re-run of the independent reader after its handling of
`session-establishment/session-e2e.json` was rewritten and the prekey store's
`legacy_blocked` rules were added. **It is not a clean-room pass and has no
isolation record.** The changes were made in the repository, by people who could
read `tacenta-core`, the model, the proofs and the Rust runner (the reader's
README, Provenance, says so). It makes no claim of a new clean-room
implementation or of an independent review, and a reader written by someone who
has seen the implementation does not test whether the text alone is enough. What
it does test is that a value the vectors record can be computed again from their
inputs by code that shares nothing with the Rust runner's, and it is worth
exactly that.

## Scope

The reader executes `session-establishment/session-e2e.json`, both vectors
(`one-time-prekeys-first-message` and `last-resort-first-message`), by
derivation (`reader/session_e2e.py`). From the inputs alone it computes, and
compares with the vector:

- the encoded bundle, with both prekey signatures recomputed from their nonces
  and verified under the identity key;
- the four (three, on the last-resort path) X25519 agreements, the PQXDH secret
  and the two split halves, given the KEM shared secret;
- the first message's classical and sparse keys (`mk_ec`, `mk_pq`), their
  combination, the composite header, the associated data, the AEAD output, the
  ratchet message and the initial message, and the same for the second message
  and its repeat;
- the responder's agreements from each spelling of the ephemeral, which must
  give the same secret;
- Bob's persisted session after the first message and after the repeat, byte
  for byte, by running the reader's Triple Ratchet and Braid receive over the
  message;
- Alice's persisted session after her first send, byte for byte, given the
  Braid's stored key pair and header;
- the responder's prekey store after the first message, byte for byte, given its
  KEM key pair;
- on the last-resort path: the replay identity and the single record entry, the
  refusal of a replay in each spelling and its acceptance by a store without the
  record, the refusal of a low-order copy, the acceptance of the torsion-spelled
  repeat, and the refusal of the four wrappers an established session must
  refuse, with the session object unchanged afterwards.

## What it does not derive

**Not checked by the reader**, so that "partially replays" has a definition. The
sweep (`reader/test_session_e2e_sweep.py`) shows the list is exact: it corrupts
sampled bytes of every input and field, and the reader notices all of them
except these.

- ML-KEM-1024, in every form. The bundle's KEM prekey (`bundle`, beyond its
  length, the FIPS 203 modulus check and the signature over it), `kem_ciphertext`
  and `kem_shared_secret` are taken from the vector, and the inputs that feed
  them (`bob_last_resort_kem_d_z`, `bob_one_time_kem_d_z`,
  `alice_kem_encapsulation_m`) are not read.
- The Braid's key generation. The codeword in each first composite header is a
  chunk of a 96-byte value (header and MAC) that comes from the KEM's key
  generation: the reader takes the value from Alice's stored encoder, checks its
  MAC under the authenticator derived from SK, and checks that the wire codeword
  is the encoder's chunk. Alice's stored `key_pair` (11,872 bytes of
  `alice_session_after_first_send`, a layout the specification delegates) is not
  checked at all, and neither is the input `alice_braid_keygen_d_z`.
- The KEM key pair inside `bob_prekey_store_after_receipt`: only the FIPS 203
  hash and modulus checks and the signature over its public half. The first
  1,536 bytes of its decapsulation key and its last 32 are not checked.
- `bob_repeat_random`, and the `z` half of each `d || z` input: consumed by the
  implementation and never observable in an output.

## Gaps this pass exposed

The pass added rules to the reader that the specification did not state, and the
review found statements in the specification and the vector documentation that
were incomplete or wrong. Each is now stated in the specification or the vector
README by the pull request that carries this record. None is closed until a
clean-room pass reads the new text (`clean-room-pass`), so each is listed as open.

- **G11-01, AMBIGUOUS.** The v5
  `legacy_blocked` list: which identifiers migration writes, that the list is
  ascending with at most two entries, what a reader refuses, what a marker does,
  and when it leaves. The page said one sentence and gave the layout, and the
  reader, the model and `tacenta-core` had each filled in the rest, differently
  for an out-of-order list (the reader and the model accepted what
  `tacenta-core` refuses). Now `session-persistence.md`, Legacy markers, and
  `session-establishment.md`, A replay record imported from an earlier format.
- **G11-02, MINOR.** The repeated-initial rule named "the responder's
  signed-prekey secret" as the key of the agreement class. The persisted session
  does not hold that secret, and `tacenta-core` and the reader use the session's
  current `ratchet_private`. `session-establishment.md`, Receiving the initial
  message, now names that key. The rustdoc in `tacenta-core/lifecycle` still
  repeats the old wording and is a translated crate, so it is left for the next
  translation pass.
- **G11-03, MINOR.** The vector README did not say which message establishes the
  responder in `one-time-prekeys-first-message` (the torsion-spelled one), which
  torsion translate the spelling is, what "low-order" is, or that a fifth random
  draw exists. `tacenta-test-vectors/README.md`, Vector layouts, now does.
- **G11-04, MINOR.** `session-persistence.md`, Semantic rules, said the rules
  "apply to all four versions" of a format that reads five, and
  `error-handling.md` cited two pages for the pre-v5 condition that neither
  named. Both are corrected.
- **G11-05, MINOR.** `vectors/primitives/x25519.json` used `"result": "invalid"`
  for a refused agreement, a meaning `schema/vector.schema.json` did not give it.
  It does now.

## Run

From the repository root:

```text
python3 tacenta-test-vectors/runners/independent/reader/run.py
python3 tacenta-test-vectors/runners/independent/reader/test_skip_allowlist.py
python3 tacenta-test-vectors/runners/independent/reader/test_session_e2e_sweep.py
```

At this pass the run exited zero with 671 PASS, 0 FAIL, 0 SKIP: 450 vector
checks (in 39 vector files) and 221 derived cases. With the hosted-inventory
files and the pass-12 derived cases merged, it exits zero with **1025 PASS, 0 FAIL, 1 SKIP**: 762 vector checks
(lines that name a vector, in 45 vector files) and 264 derived cases
(the `negative ::` lines). The total is the sum of the two; the run prints all
three numbers. The session-e2e vectors are executed by their handler and are not
in the skip set. A later project-controlled ML-KEM dry run removes the one
identity-key admission skip and adds six derived ML-KEM cases: **1032 PASS, 0 FAIL, 0 SKIP**: 762 vector checks
(lines that name a vector, in 45 vector files) and 270 derived cases. That dry
run is not independent review and does not close the reader gap. The skip
allowlist controls and the sweep pass.

This record supersedes the tally in `GAPS-10.md` while leaving that historical
pass unchanged.
