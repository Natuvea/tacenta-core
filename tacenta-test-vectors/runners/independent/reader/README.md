# tacenta_reader: a clean-room reading of tacenta-spec

An independent implementation of parts of the Tacenta protocol specification,
written to test whether the specification alone is enough to build from.
Python 3, standard library only (`hashlib`, `hmac`, `json`, `copy`, `re`,
`dataclasses`).

**Specification revision.** Twelfth pass, against the tree as found:

- `SOURCE-REVISION` `1cac363f11305d675844af590a0840774a87656f`;
- `VERSION` `0.2.0`;
- every change under `CHANGELOG.md` `[Unreleased]`, whose first entry begins
  "`identities-and-devices.md`, hosted device-inventory statements: state what a
  verifier must check before it relies on a signed statement, as seven ordered
  checks".

The seventh pass, the last full clean-room pass before this one, read
`5ae44427d17d0e8bfa1d314780305690000ee770`; passes 8 to 10 were maintenance
re-runs (`../GAPS-8.md` to `../GAPS-10.md`). The sixth pass read
`c3a00471fbef23f514eca184aac56be7b76fbc8d`, the fifth
`1dd174609bc5b008564bddef45bee43d71589761` and the fourth
`24c602d375bbebe49c25d23c6a73d9ef8fe39df0` (`VERSION` `0.1.0`). This pass is
numbered 12 because another branch may use 11.

## Provenance

Written only from the specification in `../tacenta-spec` and the vectors,
schemas and conformance manifest in `../tacenta-test-vectors`. It also used the
public standards those documents name:

- RFC 2104, RFC 5869, FIPS 180-4, RFC 7748, RFC 8032;
- XEdDSA revision 1;
- FIPS 197 and NIST SP 800-38A, for AES-256 and CBC;
- FIPS 202 and FIPS 203, for SHA3, `ByteEncode12` and the ML-KEM
  encapsulation-key checks.

It was written without network access. It consulted no existing implementation
of these protocols: not tacenta-core, tacenta-model, tacenta-proofs, the Rust
vector runner, libsignal or anything else.

**That holds for passes 1 to 7 only.** Passes 8 to 11, and every change to this
directory since, were made inside the repository by people who could read
`tacenta-core`, the model, the proofs and the Rust runner. They are maintenance,
not clean-room passes: none has an isolation record, and none claims one. The
code they added is `session_e2e.py` (the derivation of the real-primitive
session vectors), `test_session_e2e_sweep.py`, `tacenta_reader/curve25519.py`'s
`montgomery_lift`, `torsion_related` and `torsion_translates`, the last-resort replay code in
`tacenta_reader/pqxdh.py`, and the prekey store's `legacy_blocked` rules in
`tacenta_reader/persistence.py`. They follow the pages they cite
(session-persistence.md, Legacy markers, and session-establishment.md, Receiving
the initial message and The replay identity), but a reader that follows a page
after its author has seen the implementation is not a test of whether the page
alone is enough, and nothing here should be read as one.

Where the spec does not state something, the code comment names the entry in
`../GAPS.md` (first pass), `../GAPS-2.md` (second), `../GAPS-3.md` (third),
`../GAPS-4.md` (fourth), `../GAPS-5.md` (fifth), `../GAPS-6.md` (sixth),
`../GAPS-7.md` (seventh) or `../GAPS-12.md` (twelfth).
A hypothesis that matches a vector is still recorded as a gap.

## Isolation

**Pass 2.** One shell command listed the file names of the scratch directory
that contains the clean-room directory. It listed names only. No file outside
the clean-room directory was opened or searched, and nothing from that listing
was used.

### Isolation, pass 3

- **Reads.** Nothing outside the clean-room directory was read, listed or
  searched.
- **A tool-output copy, not a read.** The output of one early command, a
  dump of the new vector files, was too long to display, and the tooling
  saved a copy outside this directory. That copy was not opened. The command
  was re-run with its output written to `../work/`, and the fault run's output
  was read from `../work/faults.txt`.
- **Unrelated notes, not used.** The working environment carried a short
  index of notes from other work. Nothing from it was used for any reading or
  decision here.
- **Writes.** Temporary files were written only inside the clean-room
  directory, under `../work/`.

### Isolation, pass 4

- **Reads.** Nothing outside the clean-room directory was read, listed or
  searched. Inside it, `GAPS.md` and `GAPS-2.md` were not opened beyond a
  line count.
- **Writes.** Only inside the clean-room directory:
  - this reader;
  - `../GAPS-4.md`;
  - `../work/`: run outputs, a dump of the three new vector files, `probe_stored_keys.py`, `faults4.py` and `faults4.txt`.

  The per-fault copies under `../work/faults4/` reached the vectors through a symbolic link inside this directory, and were removed after each run.
- **Not consulted.** No implementation, git history, other scratch files or
  web search. RFC 7748 section 5, which the pages cite, was used from
  knowledge for X25519's masking and reduction.
- **Unrelated notes, not used.** The working environment again carried a short
  index of notes from other work. Nothing from it was used.

### Isolation, pass 5

- **Reads.** Nothing outside the clean-room directory was read, listed or
  searched. Inside it:
  - `GAPS.md`, `GAPS-2.md` and `GAPS-3.md` were not opened beyond a line count;
  - ADR-0000 to ADR-0005, ADR-0007 and ADR-0008 were not opened.
- **Names treated as text.** The specification, the vectors README and the
  manifest name implementation files, tests, theorems and records
  (`tacenta-core`, `tacenta-proofs/CLAIMS.md`, `LIMITATIONS.md`,
  `AUTHENTICATION-BOUNDARY.md`, `LABELS.md`, the Rust runner). None was looked
  for (GAPS-5.md G5-07).
- **Writes.** Only inside the clean-room directory:
  - this reader, including the new `cases_stored.py`;
  - `../GAPS-5.md`;
  - `../work/`: `dump5.py` and the two dumps, run outputs, `check_new_vectors5.py`, `xref5.py`, `faults5.py` and their outputs.

  The per-fault copies under `../work/faults5/` reached the vectors through a symbolic link inside this directory, and were removed after each run.
- **Not consulted.** No implementation, git history, other scratch files or
  web search. RFC 7748 section 5 and FIPS 203 sections 7.2 and 7.3, which the
  pages cite, were used from knowledge.
- **Unrelated context, not used.** Unrelated material was present in the
  working environment: a short index of notes from other work, and a list of
  further material available. None of it was opened or used.

### Isolation, pass 6

- **Reads.** Inside the clean-room directory, with one exception below:
  `tacenta-spec/` apart from the ADRs, which were not opened;
  `tacenta-test-vectors/`; `reader/`; `GAPS-5.md` and `SOURCE-REVISION`.
  `GAPS.md`, `GAPS-2.md`, `GAPS-3.md` and `GAPS-4.md` were not opened at all.
- **One read outside the clean-room directory.** The deliberate-fault run was
  started as a backgrounded command, with its output redirected to
  `../work/faults6.txt`. The output file of that backgrounded command, which is
  written outside this directory, was opened once to see whether the run had
  finished. It was empty, because the output had been redirected into this
  directory, and nothing was taken from it. It held no specification, vector or
  implementation material; it was a record of a command this pass itself ran.
  No other path outside this directory was read, listed or searched.
- **Names treated as text.** The specification, the vectors README and the
  manifest name implementation files, tests, theorems and records
  (`tacenta-core`, `tacenta-model`, `tacenta-proofs/CLAIMS.md`,
  `LIMITATIONS.md`, `LABELS.md`, `Model.PersistedState`, `Model.Braid`, the
  Rust runner and the differential harness). None was looked for
  (GAPS-5.md G5-07).
- **Writes.** Only inside the clean-room directory:
  - this reader: `tacenta_reader/persistence.py`, `triple.py`, `run.py`,
    `cases_persistence.py`, `cases_ratchet.py`, `cases_triple.py` and this file;
  - `../GAPS-6.md`;
  - `../work/`: run outputs, `check_new_vectors6.py`, `xref6.py`, `faults6.py`
    and `faults6.txt`.

  The per-fault copies under `../work/faults6/` reached the vectors through a
  symbolic link inside this directory, and were removed after each run.
- **Not consulted.** No implementation, git history, other scratch files or web
  search. RFC 7748 section 5 and FIPS 203 sections 7.2 and 7.3, which the pages
  cite, were used from knowledge.
- **Unrelated context, not used.** The working environment again carried
  unrelated material: a short index of notes from other work, which names
  several of the repositories this pass must not consult, and a list of further
  material available. None of it was opened or used.

### Isolation, pass 7

- **Reads.** Inside the clean-room directory and nowhere else:
  `tacenta-spec/`, apart from the ADRs, of which only
  `ADR-0006-specification-is-normative.md` was opened, this pass's brief having
  named its new point 7; `tacenta-test-vectors/`; `reader/`; `GAPS-6.md` and
  `SOURCE-REVISION`. `GAPS.md`, `GAPS-2.md`, `GAPS-3.md`, `GAPS-4.md` and
  `GAPS-5.md` were not opened at all.
- **No read outside this directory.** Two commands produced output too large to
  display, and a copy of each was saved outside this directory. Neither copy was
  opened; both commands were re-run reading the same files from inside this
  directory. No other path outside this directory was read, listed or searched.
- **Names treated as text.** The specification, the vectors README and the
  manifest name implementation files, tests, theorems and records
  (`tacenta-core`, `tacenta-model`, `tacenta-proofs/CLAIMS.md`,
  `LIMITATIONS.md`, `LABELS.md`, `AUTHENTICATION-BOUNDARY.md`,
  `Model.PersistedState`, `libcrux-ml-kem`, the Rust runner and the
  differential harness). None was looked for (GAPS-5.md G5-07).
- **Writes.** Only inside the clean-room directory:
  - this reader: `tacenta_reader/persistence.py`, the new
    `tacenta_reader/prekeys.py`, `tacenta_reader/__init__.py`, `run.py`,
    `cases_persistence.py`, `cases_stored.py`, the new `cases_signed.py` and
    this file;
  - `../GAPS-7.md`;
  - `../work/`: run outputs, `check_new_vectors7.py`, `xref7.py`, `faults7.py`
    and `faults7.txt`.

  The per-fault copies under `../work/faults7/` reached the vectors through a
  symbolic link inside this directory, and were removed after each run.
- **Not consulted.** No implementation, git history, other scratch files or web
  search. RFC 7748 section 5, FIPS 203 sections 7.2 and 7.3 and XEdDSA's
  verification procedure, which the pages cite, were used from knowledge.
- **Unrelated context, not used.** The working environment again carried
  unrelated material: an index of notes from other work, which names several of
  the repositories this pass must not consult, and a list of further material
  available. None of it was opened, and nothing in it was used for any reading
  or decision here -- in particular nothing about the prekey store, the
  signature rule or the two new vector files.

### Isolation, pass 12

- **Reads.** Inside the clean-room directory:
  - `tacenta-spec/`: `protocol/identities-and-devices.md` in full;
    `error-handling.md` in full; `message-format.md`, Curve public keys and
    Rejection; the relevant rows and sections of `CONSTANTS.md`; `CHANGELOG.md`
    `[Unreleased]`; and, to re-assess the open gaps, the passages of
    `session-persistence.md` (Prekey store, Session's semantic rules,
    Rejection, the leaf formats' rules), `session-establishment.md` (Receiving
    the initial message, the replay identity), `ratchet.md` (Sending and
    receiving), `sparse-pq-ratchet.md` (Receiving, the total bound, retiring
    epochs), `triple-ratchet.md` (the commit rules), `key-deletion.md` (the
    prekey paragraphs), `threat-model/` (ADV-01, ADV-06, the exclusions'
    bounds, ASM-13, ASM-19), `security-properties/` (LIM-21, REQ-AUTH-11, the
    opening of `evidence-index-format.md`, and the top-level keys of
    `evidence-index.json`). No ADR was opened.
  - `tacenta-test-vectors/`: `README.md` (the directory list, the prekey
    store's, session's and inventory layout sections, Status),
    `conformance-manifest.md` (Hosted device-inventory statements), the five
    files under `vectors/groups/` in full, and the ids, comments and version
    bytes of `persistence/prekey-store-state.json` and `session-state.json`.
  - `reader/`; `GAPS-7.md`, `GAPS-8.md`, `GAPS-9.md`, `GAPS-10.md`; the G5-04
    to G5-10 entries of `GAPS-5.md`; `SOURCE-REVISION`. `GAPS.md`,
    `GAPS-2.md`, `GAPS-3.md`, `GAPS-4.md` and `GAPS-6.md` were not opened.
- **Outside this directory.** Nothing outside it was read, listed or searched,
  with two facts to record:
  - the first command of the pass was `ls -la` of the clean-room directory
    itself, which prints the standard `.` and `..` entries; the `..` line
    showed that entry's permissions, owner, size and date, and nothing inside
    it;
  - the deliberate-fault runs were started as background commands with their
    output redirected into `../work/`, and two waits on them used a watch
    command. Each background command and each watch also left an output file
    outside this directory; none was opened. Results were read from
    `../work/` only;
  - **one attempted read outside this directory.** Near the end of the pass, a
    command piped a copy of `../work/faults12_table.py` into Python through
    standard input, to compare two fault runs. Run that way the script took its
    root from the working directory's parent rather than from its own file, and
    tried to open `work/faults12-second-run.txt` one level above the clean-room
    directory, next to it. No such file existed; the open failed with "No such
    file or directory" and nothing was read. The comparison was redone with a
    script file inside `../work/`.
- **Names treated as text.** The pages, the vectors README, the manifest and
  `CONSTANTS.md` name implementation files and records: `groups/inventory.rs`,
  `tacenta_core::groups::inventory`, `tacenta-core/tests/group_commitments.rs`,
  `generate-inventory-vectors.py`, `tooling/check-vectors.py`,
  `tacenta-core/LABELS.md`, `HL-R1-SPARSE-TRANSLATION`,
  `session-operation-trace.md` and the evidence index's paths. None was looked
  for.
- **Writes.** Only inside the clean-room directory:
  - this reader: the new `tacenta_reader/inventory.py` and
    `tacenta_reader/inventory_vectors.py`, the new `cases_inventory.py`, CR-21
    appended to `cases_ratchet.py`, SE-08 appended to `cases_curvekeys.py`,
    `run.py` (the registration only) and this file;
  - `../GAPS-12.md`;
  - `../work/`: `accept_dump12.txt`, run outputs, `check_new_vectors12.py` and
    its output, `faults12.py`, `faults12_table.py`, `faults12.txt`,
    `faults12-first-run.txt` and `faults12-second-run.txt`.

  The per-fault copies were made under `../work/faults12/`, each reaching the
  vectors through a symbolic link inside this directory, and were removed after
  each run. Python wrote its usual `__pycache__` directories inside `reader/`.
- **Not consulted.** No implementation, no git history, no vector generator,
  no other scratch files, no web search, and no libsignal material. RFC 7748
  section 5, RFC 8032 section 5.1, the XEdDSA document's revision 1 and the
  UTF-8 definition Python's strict codec implements (RFC 3629) were used from
  knowledge. Nothing was fetched.
- **Unrelated notes, not used.** An index of notes from other work, and a list
  of further material, were available alongside the directory. None of it was
  opened, and nothing in it was used for any reading or decision here.

## What changed in pass 12

- **`tacenta_reader/inventory.py`, new: the hosted device-inventory
  statements** (identities-and-devices.md, Hosted device-inventory statements
  and Accepting a signed statement). The unsigned preimage, `DeviceBinding` and
  `Revocation`; every encoding rule, applied alike to bytes and to a statement
  built in memory; `binding_commitment`; the signed statement and its signing
  input; check 6's three-step identity-key test; the seven checks in the
  page's order, with the verifier's issuer binding, freshness rule, binding
  policy and statement policy supplied as a policy object, and a hook for
  recording a generation after check 7; the issuer's duty (`sign_statement`);
  three refusal kinds, each naming the check that refused.
- **`tacenta_reader/inventory_vectors.py`, new.** The four closed layouts of
  the vectors README, "The hosted-inventory statements", and its scripted
  policy with the hook-call strings. An acceptance case passes only when both
  `refusal` and `hook_calls` agree; the issuer signature is verified by this
  reader's own XEdDSA.
- **`run.py`: registration only.** One import, the four schemas in
  `GROUP_SCHEMAS`, and `cases_inventory` in `CASE_MODULES`. The earlier
  `h_inventory_statement` and its helpers (`_u32`, `_u64`,
  `_inventory_binding`, `_canonical_bindings`), which no pass record describes,
  are left in place but no longer registered.
- **Cases:** the new `cases_inventory.py` (IV-01 to IV-22); CR-21 in
  `cases_ratchet.py` (the sparse store's total bound, G12-05); SE-08 in
  `cases_curvekeys.py` (a repeat's agreement class, G12-06). IV-02 was
  strengthened during the fault run (F12-07).

**No existing protocol module changed.** `pqxdh.accept_repeated_initial`'s
docstring still quotes a sentence the current text has replaced
(`../GAPS-12.md`, G12-06).

## What changed in pass 7

- **`persistence.py`: the prekey store's sixth semantic rule.** Every stored
  signature is verified under `identity_public` -- `signed_prekey_sig` over
  `EncodeEC` of the public half of `signed_prekey_secret`, `kem_sig` over
  `EncodeKEM` of `kem_pair`'s `ek`, each `kem_one_time` entry's over its own
  pair's, and, in v3 and v4, `previous_signed`'s and `previous_kem`'s over
  theirs. The one-time curve prekeys carry none and are not covered. The
  signature is XEdDSA under the identity key, over an unlabelled message
  (session-establishment.md, Publishing keys; identities-and-devices.md,
  Signing, "Prekey signatures carry no label"), which is the one thing the
  rule's own sentence does not say (GAPS-7.md G7-03). It runs last of all:
  after the framing, after the v4 re-encode check and after the other five
  rules.
- **`persistence.py`: a fifth refusal kind, `Incoherent`.** Rejection: "the
  prekey store calls it 'incoherent' and gives it for its signature rule
  alone, its other rules being malformed".
- **`persistence.py`: the Braid's `key_pair` content clause is scoped.**
  `KEY_PAIR_VIEW` is now `None` by default. This reader does not have the KEM
  library's layout, so in tags 1 to 4 it checks the field's 11,872-byte length,
  accepts the content, and conforms -- which is what the page now says such a
  reader does. `GAPS-5.md` G5-02 is closed by that scope.
- **`prekeys.py`, new: `rotate_signed_prekey` and `rotate_kem`.** The two
  operations the new rule puts an obligation on. Each signs under the identity
  whose public key the store holds as `identity_public` and refuses, changing
  nothing, if handed any other; each takes the next identifier and returns the
  store unchanged, silently, once `next_id` stands at `u32::MAX`; `rotate_kem`
  drops the record entries of the key it wipes (key-deletion.md).
- **`run.py`:** handlers for `prekey-store-state` and `session-state`, reading
  stored bytes against `fields`, writing them back as the input, and checking
  the refusal each invalid vector names against four kinds rather than two.
- **Cases:** a new module `cases_signed.py`. `SK-08` and `BK-01` are rewritten
  for this revision's two decisions, `TM-01`'s note about `LABELS.md` is
  dropped, and `cases_persistence.py`'s prekey-store fixtures now carry
  signatures that verify.

**The session's format needed no change.** Its eight semantic rules, four
field-by-field refusals and three refusal kinds were implemented from the page
in pass 2 and extended in pass 5; the 13 session vectors passed against that
code unchanged.

## What changed in pass 6

- **`persistence.py`: a reader error, fixed.** session-persistence.md, Triple
  ratchet state, now states the refusals that format gives: a wrong version for
  its own first byte, and short or malformed for everything else it refuses,
  including "a `ratchet_state` or `spqr_state` that its own reader refuses,
  whatever that reader's reason. An unrecognised version inside a half is one
  of those reasons, and it is not passed through." This reader passed an inner
  wrong version through, which was reading (b) of GAPS-5.md G5-01, chosen while
  the page was silent. It now maps every inner refusal to malformed, as it
  already did for the session. PS-09 asserted the old behaviour and is
  rewritten; PS-24 states the decided rule.
- **`triple.py`: the Triple Ratchet's own operations**, with the agreement's
  results handed in rather than an agreement object: `init_halves` (the split
  of `SK`, triple-ratchet.md, Initialisation), `halves_send` and
  `halves_receive` ("Both run the classical half first and the sparse half
  second"). This is the shape `triple-ratchet-state.json`'s `steps` drive.
- **`run.py`: the Triple Ratchet's and the Braid's persisted states**
  (`vectors/persistence/triple-ratchet-state.json`, `braid-state.json`), laid
  out in the vectors README. For each vector the runner checks:
  - **stored bytes:** the reader's `fields`, names and values; the layout the
    README composes them into, which must be the input; the bytes written back;
    or the refusal the vector names;
  - **the triple state's operations:** replayed from a new state named by
    `role` or from `start`, written as `output`, read back and written again,
    with the `-read-back` vector beside each;
  - **the Braid's operations:** each step one received Braid message, from
    stored `start` bytes and with no KEM, since the two `Ct2Sampled`
    transitions read the stored epoch and the message and nothing else.
- **Cases:** PS-24 (the decided refusal rule), TR-11 (the Triple Ratchet's own
  send and receive, and the epoch the agreement names) and CR-19 (the sparse
  store's total bound as the page now states its evidence). PS-09 rewritten.

**Nothing else needed changing.** The Braid's stored format, its twelve tags,
its semantic rules and both its refusal kinds were implemented from the page in
earlier passes; the 33 Braid vectors passed against that code unchanged, as did
the 18 triple-ratchet-state vectors once the handler and the fix above were in.

## What changed in pass 5

- **`run.py`: the two ratchets' persisted states**
  (`vectors/persistence/ratchet-state.json`, `sparse-ratchet-state.json`),
  laid out in the vectors README, "The ratchets' persisted states". For each
  vector, the runner checks:
  - **stored bytes:** the reader's `fields`, names and values, and the bytes written back; or the refusal the vector names (`wrong-version` is `WrongVersion`, `short-or-malformed` is `Malformed`);
  - **operations:** replayed from a new state or from `start`; every step but an invalid vector's last is accepted, and that last is refused as `ChainExhausted`; the state reached is written as `output`, read back and written again, and a `-read-back` vector beside it offers `output`;
  - **the Diffie-Hellman stand-in:** zero exactly when no step is taken.
- **`persistence.py`: stored curve public keys** (session-persistence.md, Session, Semantic rules, "Stored curve public keys"):
  - the ratchet state's `dhs_pub`, `dhr_pub` and each skipped `dh` are refused as malformed;
  - the session's two identity keys, `pending_initial`'s ephemeral and `established_ephemeral`'s key are refused as inconsistent;
  - the prekey store's `identity_public` is refused as malformed, in v1 to v4.
- **`persistence.py`: the Braid key pair checked on load in tags 1 to 4**
  (`H(ek_vector || rho)` against the header's `H(ek)`, and the modulus check).
  It uses the test double's layout, since the library layout is delegated
  (GAPS-5.md G5-02).
- **`persistence.py`: a reader error fixed.** The session now refuses a
  `triple_state` or `braid` its own reader refuses "whatever that reader's
  reason" as malformed. It had passed an inner wrong version through.
- **`wire.py`:** the initiator refuses a bundle whose identity key, signed
  prekey or one-time curve prekey is not canonical (`BundleRefused`).
- **`erasure.py`:** an encoder over more than 65,536 chunks holds `chunk_0` to
  `chunk_65535`, and its stored form writes them.
- **`kem_double.py`:** `key_pair` is `ek_vector || header || z`, and decapsulation
  uses the stored `H(ek)`.
- **`spqr.py`:** the retention sum saturates (unobservable; GAPS-5.md G5-08).
- **Cases:**
  - new: `cases_stored.py` (15 cases) and EC-13;
  - rewritten: CK-03 (the initiator now refuses a re-spelled key) and PS-16 (the session's inner refusal kind);
  - strengthened: CR-03 (the stop written out) and PS-08 (an isolated duplicate epoch).

## What changed in pass 4

- **`wire.py`: canonical curve keys at every decoder** (message-format.md,
  Curve public keys).
  - `check_curve_key` accepts 32 bytes exactly when, read little-endian, they
    are below p.
  - It is applied to the composite header's `dh`, the bundle's
    `identity_key`, `signed_prekey` and present `one_time_prekey`, and the
    initial message's `identity` and `ephemeral`. A refusal is a
    `DecodeError`.
  - `DecodeEC` uses the same check. G3-05 is closed by the text.
- **`pqxdh.py`: the repeated-initial rule as now written.**
  - `accept_repeated_initial` requires the incoming and established
    ephemerals to produce the same successful X25519 agreement under the
    responder's ratchet private key, and `identity` to equal
    `EncodeEC(peer_identity_public)`, on a responder's session. If either
    agreement is unavailable, the check fails closed.
  - `receive_repeated_initial` decodes first, then compares, then decrypts the
    inner ratchet message.
- **`erasure.py`: G3-02, closed by the text.**
  - A live encoder over 65,536 chunks is not refused. Pass 3 refused it.
  - `persistence.encoder_to_bytes` does not write one, because which chunks it
    holds is unspecified and a stored one is refused.
  - A zero-chunk encoder's all-zero codewords are now asserted.
- **`run.py`:**
  - handlers for `composite-header-decode`, `prekey-bundle-decode` and
    `initial-message-decode`; RM-14 covers the standalone composite header's
    trailing-byte refusal;
  - the zero-chunk encoder comparison runs for every encoder-state vector.

## What it implements

| Module | Spec source | Pinned by |
|---|---|---|
| `kdf.py`: HMAC-SHA256, HKDF-SHA256 | RFC 2104, RFC 5869 | `primitives/hmac-sha256.json`, `hkdf-sha256.json` |
| `curve25519.py`: X25519, Ed25519, XEdDSA signing (with the clamp) and the six verifier rules | RFC 7748, RFC 8032, identities-and-devices.md Signing and Verifying a signature | `primitives/x25519.json`, `ed25519.json`, `xeddsa.json` (rule 3 not on its own: GAPS-3.md vector gaps) |
| `wire.py`: composite header, ratchet message, `CONCAT`, initial message, prekey bundle, `EncodeEC`/`EncodeKEM`, **the canonical curve-key rule in all three decoders** and `DecodeEC`, every stated decoder refusal, the initiator's bundle refusals | message-format.md (Curve public keys), session-establishment.md | `post-quantum/composite.json`, `serialization/*.json`, `malformed-input/composite-header-decode.json`, `prekey-bundle-decode.json`, `initial-message-decode.json` (the curve-key refusals); other refusals by derived cases only |
| `aes.py`, `aead.py`: AES-256, CBC, PKCS#7, the HMAC-SHA256 tag, the four receiver steps, one authentication failure | message-format.md Authenticated encryption | `aead/aead-encrypt.json`, `aead-decrypt.json` |
| `ratchet.py`: the Double Ratchet: initialisation, derivations, expansion, DH triggers, `MAX_SKIP`, store bound, replacement, stale same-chain refusal, ceilings, expiry, eviction | ratchet.md, CONSTANTS.md, key-deletion.md | `ratchet/double-ratchet.json`, `malformed-input/ratchet-reject.json` |
| `spqr.py`: the sparse ratchet: derivations, send counter, ceilings, refusals, total bound, eviction, retention, and **replacement order (fixed in pass 3, G2-01)** | sparse-pq-ratchet.md, session-persistence.md | `post-quantum/spqr.json` (chain step only) |
| `triple.py`: split, combination, encrypt/decrypt with the commit rules, the non-contributory check, eviction retry; the agreement runs before the ratchets; **the Triple Ratchet's own initialisation, send and receive with the agreement's results handed in (pass 6)** | triple-ratchet.md, mlkem-braid.md What the session does with them | `post-quantum/triple.json`, `split.json`, `persistence/triple-ratchet-state.json` |
| `pqxdh.py`: `KDF`, `AD`, DH1..DH4, the decapsulation-length refusal, the FIPS 203 section 7.2 check on a bundle's KEM prekey, **the repeated-initial rule (both comparisons, decode first; pass 4)**, the last-resort fingerprint and the replay record's refusals | session-establishment.md, key-deletion.md | `session-establishment/pqxdh-sk.json`; the fingerprint and the repeated-initial rule by derived cases only |
| `gf65536.py`, `erasure.py`: GF(2^16), chunking, codewords, first-copy-wins decoding, encoder exhaustion, **the zero-chunk and over-65,536-chunk encoders (pass 4)** | mlkem-braid.md The erasure code | `post-quantum/gf.json`, `inv.json`, `interp.json`, `erasure-encode.json`, `erasure-decode.json` |
| `braid.py`: **the ML-KEM Braid**: `ToBytes`, `KDF_OK`, `KDF_AUTH`, the authenticator and both MACs, `ek_vector` validation, messages, the eleven live states and `Failed`, all thirteen transitions, send and receive epochs, what a receive ignores, every way into `Failed`, the epoch ceiling; conversion to the persisted layout; `BraidAgreement` for `triple.py` | mlkem-braid.md | `post-quantum/braid.json`, `auth.json`; the rest by derived cases |
| `kem_double.py`: a **test double** for the incremental KEM interface, with the split's sizes, hash order and implicit rejection; its `key_pair` holds `ek_vector \|\| header \|\| z`. **Not ML-KEM**, and not the layout the page delegates: from pass 7 the persistence reader does not use it, the `key_pair` content clause being scoped to a reader that has the real one (GAPS-7.md, G5-02 closed) | mlkem-braid.md The KEM split | none |
| `persistence.py`: readers and writers with every stated refusal and semantic rule: ratchet, sparse ratchet and triple states, erasure sub-formats, Braid (12 tags), session, prekey store (v5 written, v1-v4 read, `kem_pair` checks, **and from pass 7 the sixth rule, every stored signature verifying under `identity_public`, refused as `incoherent`**) | session-persistence.md, CONSTANTS.md | every file under `persistence/`: the two erasure coders, `ratchet-state.json`, `sparse-ratchet-state.json` (pass 5), `triple-ratchet-state.json`, `braid-state.json` (pass 6), **`prekey-store-state.json`, `session-state.json` (pass 7)**. Not pinned by any: `non-canonical` for either format, and the Braid's `key_pair` content clause, which no vector can pin (GAPS-7.md, section 3). The prekey-store signature rule is pinned by `prekey-store-state/signed-prekey-signature-does-not-verify`. |
| `protobuf.py`: the bounded protobuf profile, both message types | protobuf-profile.md, CONSTANTS.md | `protobuf/protobuf-ratchet-body.json`, `protobuf-prekey-envelope.json` |
| `prekeys.py`: the two prekey-store rotations, each signing under `identity_public` and refusing any other identity, each stopping silently at `u32::MAX`, `rotate_kem` dropping the wiped key's record entries (pass 7) | key-deletion.md, session-persistence.md Prekey store Semantic rules | no vectors |
| `identity.py`: the identity secret, application signatures | identities-and-devices.md | no vectors |
| `inventory.py` (pass 12): the hosted device-inventory statement, its encoding rules for bytes and for built statements, `binding_commitment`, the signed form, check 6's identity-key test, the seven checks with a caller-supplied policy, the issuer's duty | identities-and-devices.md Hosted device-inventory statements, Accepting a signed statement; CONSTANTS.md | `groups/inventory-statements-v1.json`, `inventory-decode-refusals-v1.json`, `inventory-binding-commitments-v1.json`, `inventory-acceptance-v1.json`. Not pinned by any: the issuer's duty, recording a generation after check 7, a statement built in memory, the re-encode refusal (`../GAPS-12.md`, section 3) |
| `inventory_vectors.py` (pass 12): the four inventory layouts and the scripted policy | tacenta-test-vectors/README.md, The hosted-inventory statements | the same four files |

**The eight vector files new in pass 3 needed no module change.** Their 106
vectors pass on the modules pass 2 wrote. The runner gained handlers for them;
GAPS-3.md G3-01 to G3-04 record the input layouts it had to infer.

## Derived cases

Each case cites the page and sentence it tests. There is one module per area,
and each is a row in the runner's table.

| Module | Cases | Covers |
|---|---|---|
| `negative_cases.py` | 59 | wire decoders and refusals, bundle signatures, non-contributory DH, ratchet and sparse ratchet basics, field |
| `cases_ratchet.py` | 21 | the sparse store's total bound counted before and after the purge, on a stored state the two counts disagree about (CR-21, pass 12); counter ceilings, clock ceiling, stale same-chain refusal, DH triggers, `PN` skip rules, store bound, eviction order, sparse ceilings and eviction, sparse replacement order (CR-18); the sparse store's total bound as the page now states its evidence (CR-19, pass 6); the `Nr = u32::MAX` stale/exhaustion overlap and its adjacent cases (CR-20) |
| `cases_triple.py` | 11 | split halves, expansion of the combination, commit rules, AD binding, non-contributory check order, eviction retry, epoch advance; the Triple Ratchet's own send and receive, and the epoch the agreement names against the state's own (TR-11, pass 6) |
| `cases_aead.py` | 13 | FIPS 197 KAT, round trips, padding, tag input, every refusal, one failure kind, no decryption before the tag, key and IV positions and the IV not sent (AE-12) |
| `cases_erasure.py` | 13 | table arithmetic, chunking, codewords, decoding from any `k`, first copy wins, exhaustion; an encoder for zero bytes (EC-11) and over 65,536 chunks (EC-12); which chunks that encoder holds, and its stored form (EC-13, pass 5) |
| `cases_persistence.py` | 24 | round trips and every stated refusal and semantic rule of each format; the triple ratchet state's decided refusals, an inner half's unrecognised version included (PS-24, pass 6) |
| `cases_protobuf.py` | 9 | varints, tags, bounds, both field tables, free order |
| `cases_identity.py` | 19 | application signatures, clamping on use, the repeated-initial comparisons (SE-01, both fields, rewritten in pass 4), non-contributory definition; `DecodeEC` and the initial decoder's refusal (SE-03), X25519's masking against the decoders' refusals (SE-04), the section 7.2 KEM prekey check (SE-05); XEdDSA signing and the six verifier rules (XS-01 to XS-04); the fingerprint and replay record (LR-01 to LR-07, LR-06 through the bytes) |
| `cases_braid.py` | 18 | derivation bytes, authenticator and MACs, sizes and holdings, initialisation, the send table, epoch completion and roles, send and receive epochs, what a receive ignores, all thirteen transitions, MAC and validation failures, KEM failures and `Failed`, the epoch ceiling, encoder exhaustion, persistence of all twelve tags, the composite header, the Triple Ratchet over the Braid with `session-persistence.md`'s relations, `AgreementFailed` |
| `cases_curvekeys.py` | 8 | a repeat's agreement class is the same under the signed-prekey secret and under the session's ratchet private key (SE-08, pass 12); pass 4. The canonical-key rule at p and every value up to 2^255 - 1 (CK-01); the composite header's `dh`, including a live session refusing at decode (CK-02); the bundle's three keys, refused though signed, with low-order canonical keys left to the contributory check (CK-03); the initial message's two keys, and `DecodeEC` accepting every key the decoder returns (CK-04); why a second spelling is a second identity (CK-05); a repeat must first decode (SE-06); the repeated initial message over a live Triple Ratchet half: ignored fields, yield once, already-read messages, refusals before decryption, the initiator's session (SE-07) |
| `cases_stored.py` | 15 | pass 5. Stored curve public keys: the ratchet state's three positions, refused as malformed (SK-01), and why (SK-02); a triple state or session holding one, malformed before the session's rules (SK-03); the session's four keys, inconsistent (SK-04), so a genuine repeat always matches (SK-05); the sparse state and the Braid hold none (SK-06); no honest state refused (SK-07); the prekey store's identity in v1 to v4 (SK-08); the initiator's own bundle check (SK-09). The Rejection table's six persisted formats for the short-buffer/unknown-version overlap, plus the adjacent empty, recognised-version truncation and long enough unknown-version cases (RJ-01). The Braid key pair's load check (BK-01). Both ratchets inductive up to and at their ceilings (IN-01, IN-02). ASM-05's labels (TM-01, rewritten in pass 7) and REQ-AUTH-11 against the protocol pages (TM-02). BK-01 and SK-08 rewritten in pass 7 for the scoped `key_pair` clause and for `p - 1` as `identity_public` |
| `cases_inventory.py` | 22 | pass 12. The hosted device-inventory statements: the preimage (IV-01), both sort orders, byte boundaries included (IV-02), exact bindings (IV-03), generation ranges (IV-04), the UTF-8 handle (IV-22), a statement built in memory (IV-05), the three refusal kinds (IV-06), the issuer's duty (IV-07), check 4 having no effect of its own and the compare-and-advance (IV-08, IV-09), check 6 from its definition, its five low-order values, the twist, mixed torsion and single spelling (IV-10 to IV-14), check 6 before any policy (IV-15), check 5 (IV-16), check 7 (IV-17), checks 1 and 2 (IV-18), the signature input and the page's verifier (IV-19), `binding_commitment` (IV-20), the unchecked properties (IV-21) |
| `cases_signed.py` | 12 | pass 7. The prekey store's sixth semantic rule: every signed position (PK-01), what it does not bind (PK-02), `incoherent` as a kind of its own and the other five as malformed (PK-03), its place last of all in the order of checks (PK-04), the flipped byte at offset 69 and the two readers that disagree about it (PK-05), the rule across all five versions (PK-06). The obligation on the operations, and both rotations (PK-07), and forty rotations none of whose states is refused (PK-08). Rejection's paragraph on which format gives which refusal (RJ-02). The Principles' exception to the inductive invariant (IN-03). ADR-0006's point 7 against ASM-05 and AS-12 (TM-03). The epoch relation's boundary, all twelve tags under both readings (EP-01) |

## Deliberate faults

**Passes 1 and 2.** The runner was checked against 13 faults:

- the expiry boundary written as `>`;
- `MAX_SKIP` on `PN` without a receiving chain;
- eviction ties reversed;
- no stale same-chain refusal;
- three epochs kept;
- an unchecked padding byte;
- decrypting before the tag;
- last-copy-wins;
- the decoder bound removed;
- the Braid role parity flipped;
- non-minimal varints;
- the contributory check moved after the ratchets;
- a validating initial decoder.

Each produced FAILs that included the targeted case.

**Pass 3.** Eighteen faults, each a one-line textual change made in a fresh
copy of the reader by `../work/faults.py`, then the full runner:

| Fault | Caught by |
|---|---|
| F01 `KDF_OK` with a non-zero salt | `braid.json`, BR-01 |
| F02 `Update` swaps `root_key` and `mac_key` | `auth.json`, BR-02 |
| F03 MAC inputs with the epoch bare (the published document's notation) | BR-02 only |
| F04 (12) requires a codeword | BR-08 |
| F05 (5) reports the sending epoch | BR-07 |
| F06 `Ct2Sampled` checks the ceiling only on an advancing message | BR-13 |
| F07 `ek_vector` validation without the modulus check | BR-11 |
| F08 fingerprint without the ciphertext's length prefix | LR-01 |
| F09 record budget of 1,025 per key | LR-05 |
| F10 replay matched only under the named key's tag | LR-04 |
| F11 `DecodeEC` without the canonical refusals | SE-03, SE-04, LR-06 |
| F12 sparse replacement keeps the old place | CR-18 |
| F13 erasure decoder, last copy wins | `erasure-decode.json`, `erasure-decoder-state.json`, EC-06 |
| F14 persisted encoder writes `next` as 0 once exhausted | `erasure-encoder-state.json`, PS-10 |
| F15 protobuf accepts a repeated field 1 | both protobuf files, PF-07 |
| F16 AEAD checks only the last padding byte | `aead-decrypt.json`, AE-09 |
| F17 XEdDSA verifier accepts a small-order `A` | **missed at first** (no vector and no case failed); caught by XS-03 once it was given a small-order `A` with a full-order `R` |
| F18 the session hands the sparse ratchet the state's epoch | BR-17, BR-18 |

On the first run, 17 of 18 were caught. The miss showed that no `xeddsa.json`
vector isolates rule 3 (GAPS-3.md, vector gaps). After XS-03 was
strengthened, F17 is caught, so all 18 are. (Pass 3's `faults.py` was not in
the tree this pass was read from.)

**Pass 4.** Nineteen faults in `../work/faults4.py`, run the same way, four at
a time. **All 19 were caught on the first run.**

| Fault | Vector files that failed | Derived cases that failed |
|---|---|---|
| F4-01 composite header: `dh` not checked | `composite-header-decode.json` | SE-04, CK-02 |
| F4-02 the rule off by one: a key equal to p accepted | **none** | SE-03, CK-01, CK-02 |
| F4-03 the rule tests bit 255 only | all three decoder files | SE-03, SE-04, CK-01 to CK-04, SE-06 |
| F4-04 the rule masks bit 255 before comparing | all three decoder files | SE-03, SE-04, LR-06, CK-01 to CK-04, SE-06 |
| F4-05 bundle `identity_key` not checked at decode | `prekey-bundle-decode.json` | CK-03 |
| F4-06 bundle `signed_prekey` not checked | `prekey-bundle-decode.json` | SE-04, CK-03 |
| F4-07 bundle present `one_time_prekey` not checked | `prekey-bundle-decode.json` | CK-03 |
| F4-08 initial `identity` key bytes not checked | `initial-message-decode.json` | SE-03, CK-04, SE-06 |
| F4-09 initial `ephemeral` key bytes not checked | `initial-message-decode.json` | SE-03, SE-04, CK-04, SE-06 |
| F4-10 both left to establishment (pass 3's reading of G3-05) | `initial-message-decode.json` | SE-03, SE-04, CK-04, SE-06 |
| F4-11 a refused key reported as an encoding error | all three decoder files | RM-12, SE-03, SE-04, LR-06, CK-01 to CK-04, SE-06 |
| F4-12 repeat: `identity` not compared (pass 3's rule) | none | SE-01, SE-07 |
| F4-13 repeat: `ephemeral` not compared | none | SE-01, SE-07 |
| F4-14 repeat: `identity` compared with the raw key | none | SE-01, SE-06, SE-07 |
| F4-15 repeat: an initiator's session with an ephemeral accepts | none | SE-01 |
| F4-16 repeat: inner message decrypted before the comparisons | none | SE-07 |
| F4-17 repeat: an undecodable repeat reported as `NotARepeatedInitial` | none | SE-06 |
| F4-18 erasure: an encoder over 65,536 chunks refused again | none | EC-12 |
| F4-19 erasure: an encoder for zero bytes issues non-zero codewords | `erasure-encoder-state.json`, through the runner's stated rule | EC-11 |

The vector files catch 11 of the 19. They miss the boundary at exactly p
(F4-02), every repeated-initial fault, and the over-65,536-chunk encoder
(GAPS-4.md, vector gaps).

**Pass 5.** Forty-eight faults and one control in `../work/faults5.py`, run the
same way, six at a time. **All 48 were caught, 34 of them by a vector file.**
The control, a change the text allows, failed nothing.

| Fault | Vectors that failed | Derived cases that failed |
|---|---|---|
| F5-01 classical send allowed at `ns = u32::MAX` | `ratchet-state` send-at-u32-max-refused | CR-01, IN-01 |
| F5-02 classical receive allowed at `nr = u32::MAX` | `ratchet-state` receive-at-nr-u32-max-refused | CR-02, IN-01, IN-02 |
| F5-03 the clock saturates into `u32::MAX` | `ratchet-state` clock-stays-at-its-stop, clock-stays-at-its-stop-on-the-chain | CR-03, IN-01 |
| F5-04 the clock never stops | the same two | CR-03, IN-01 |
| F5-05 the clock stops one early | `ratchet-state` clock-reaches-its-stop and the two above | CR-03 (from the strengthened CR-03; none before) |
| F5-06 sparse send allowed past `n = u64::MAX` | `sparse-ratchet-state` send-past-u64-max-refused | CR-12 |
| F5-07 sparse receive at `u64::MAX` refused as out of order | `sparse-ratchet-state` receive-past-u64-max-refused | CR-13 |
| F5-08 sparse advance onto epoch `u64::MAX` allowed | `sparse-ratchet-state` advance-onto-u64-max-refused | SP-04 |
| F5-09 sparse advance refused one early | `sparse-ratchet-state` epoch-reaches-one-below-the-ceiling | IN-02 |
| F5-10 an unknown version refused as short or malformed | both files, version-zero, version-two | PS-02, PS-07, PS-09, PS-13, PS-16, PS-20, RJ-01 |
| F5-11 the empty buffer refused as a wrong version | both files, empty | RJ-01 |
| F5-12 ratchet store bound removed | `ratchet-state` store-over-its-bound | PS-04 |
| F5-13 ratchet store bound refuses exactly 2,000 | **none** | PS-04 |
| F5-14 events below `u32::MAX` not checked | `ratchet-state` clock-at-u32-max | PS-04 |
| F5-15 `stored_at` equal to `events` refused | `ratchet-state` stored-at-equal-to-events and three clock vectors | IN-01, PS-04 |
| F5-16 two stored keys for one pair accepted | `ratchet-state` two-keys-one-pair | PS-04 |
| F5-17 `ckr` without `cks` accepted | `ratchet-state` receiving-chain-without-a-sending-chain | PS-04 |
| F5-18 unknown `labels` tag accepted | `ratchet-state` labels-tag-one | PS-03 |
| F5-19 stored keys re-ordered on read | `ratchet-state` stored-keys-in-any-order | IN-01, IN-02, PS-05 |
| F5-20 `dhs_pub` not held canonical | `ratchet-state` dhs-pub-* (three) | SK-01, SK-03 |
| F5-21 `dhr_pub` not held canonical | `ratchet-state` dhr-pub-* (three) | SK-01, SK-02, SK-03 |
| F5-22 a stored `dh` not held canonical | `ratchet-state` stored-dh-* (three) | SK-01, SK-02 |
| F5-23 the stored-key rule accepts p | `ratchet-state` the three `*-equal-to-p` | SK-01, SK-04, SK-08 |
| F5-24 the stored-key rule tests bit 255 only | `ratchet-state` the `*-plus-p` and `*-equal-to-p` | CK-03, SK-01, SK-04, SK-08 |
| F5-25 session `our_identity_public` not held canonical | **none** | SK-04 |
| F5-26 session `peer_identity_public` not held canonical | **none** | SK-04 |
| F5-27 `pending_initial`'s `ephemeral_public` not held canonical | **none** | SK-04 |
| F5-28 `established_ephemeral`'s key not held canonical | **none** | SK-04, SK-05 |
| F5-29 a session stored-key refusal reported as malformed | **none** | SK-04, SK-05 |
| F5-30 prekey store `identity_public` not held canonical | **none** | SK-08 |
| F5-31 initiator: no canonical check of a bundle's keys | **none** | CK-03, SK-09 |
| F5-32 initiator: one-time curve prekey not checked | **none** | SK-09 |
| F5-33 sparse window sum does not saturate | `sparse-ratchet-state` epoch-at-the-ceiling | PS-08 |
| F5-34 sparse `e <= epoch` not checked | `sparse-ratchet-state` chains-epoch-after-the-current | PS-08 |
| F5-35 two chains entries for one epoch accepted | `sparse-ratchet-state` two-entries-one-epoch | PS-08 (from the strengthened PS-08; none before) |
| F5-36 current epoch without an entry accepted | `sparse-ratchet-state` current-epoch-without-an-entry | PS-08 |
| F5-37 a stored key's epoch without an entry accepted | `sparse-ratchet-state` stored-key-epoch-without-an-entry | PS-08 |
| F5-38 two sparse stored keys for one pair accepted | `sparse-ratchet-state` two-stored-keys-one-pair | PS-08 |
| F5-39 sparse store bound removed | `sparse-ratchet-state` store-over-its-bound | PS-08 |
| F5-40 an absent chain refused | `sparse-ratchet-state` absent-chain-accepted | PS-07 |
| F5-41 the Diffie-Hellman step's two outputs swapped | `ratchet-state`, `double-ratchet`, `ratchet-reject` | DR-07, TR-01, TR-04 to TR-08, TR-10 |
| F5-42 expiry at age above `MAX_SKIPPED_AGE` | **none** | DR-06 |
| F5-43 a sparse send does not move its chains entry last | `sparse-ratchet-state` alice-opens-an-epoch, bob-follows-into-the-epoch | CR-17 |
| F5-44 sparse retention keeps three epochs | `sparse-ratchet-state` bob-retires-an-epoch-with-its-keys, epoch-reaches-one-below-the-ceiling | IN-02, SP-07 |
| F5-45 Braid `key_pair` not checked on load | **none** | BK-01 |
| F5-46 Braid `key_pair` modulus check dropped | **none** | BK-01 |
| F5-47 an encoder holds every chunk of a longer value again | **none** | EC-13 |
| F5-48 the session passes an inner wrong version through (pass 4's behaviour) | **none** | PS-16 |
| C5-01 control: a short buffer with an unknown version refused as short | none, as Rejection allows | none |

The vector files catch every ceiling, every refusal kind and every rule of
the two leaf states, the value p included. They miss the rules no vector file
covers (GAPS-5.md, vector gaps): the session's, the prekey store's and the
initiator's stored-key rules; the Braid key pair; the longer encoder; expiry;
the accepted store of 2,000 keys; and the session's inner refusal kind.

**Pass 6.** Twenty-three faults and one control in `../work/faults6.py`, run
the same way. **Twenty-two were caught on the first run; F6-09 was missed, and
is caught once TR-11 was added for it, so all 23 are caught. 20 are caught by a
vector file.**

| Fault | Vectors that failed | Derived cases that failed |
|---|---|---|
| F6-01 an inner refusal passed through (pass 5's reading of G5-01) | `triple-ratchet-state` classical-half-with-an-unknown-version, sparse-half-with-an-unknown-version | PS-24 |
| F6-02 the triple state's own wrong version reported as short or malformed | `triple-ratchet-state` version-zero, version-two | PS-09, PS-24, RJ-01 |
| F6-03 the triple state's role rule removed | `triple-ratchet-state` halves-disagree-on-the-role | PS-09, PS-24 |
| F6-04 the triple state accepts bytes after the second half | `triple-ratchet-state` trailing-byte | PS-09, PS-24 |
| F6-05 the role rule reads the direction the other way round | `triple-ratchet-state` (seven) | BK-01, PS-09, PS-15, PS-17, PS-24, SK-03 to SK-05, ... |
| F6-06 initialisation does not split `SK` | `triple-ratchet-state` the four `role` vectors | **none** |
| F6-07 the responder initialises the sparse half in `A2b` | `triple-ratchet-state` fresh-responder, responder-after-a-receive | **none** |
| F6-08 a receive gives the sparse half the classical message number | `triple-ratchet-state` responder-after-a-receive | **none** |
| F6-09 a send gives the sparse half the state's epoch, not the agreement's | **none** | TR-11 (added for it; nothing caught it before) |
| F6-10 the Braid accepts a tag above 11 | `braid-state` tag-twelve, tag-255 | PS-13 |
| F6-11 the Braid accepts a stored epoch of `u64::MAX` | `braid-state` epoch-u64-max | PS-13 |
| F6-12 a live Braid state may have epoch 0 | `braid-state` epoch-zero | PS-14 |
| F6-13 `Failed` is written and read with an epoch | `braid-state` failed, ct2-sampled-at-the-ceiling-fails | BR-15, PS-12, PS-15, PS-17 |
| F6-14 the Braid's raw field lengths are not checked | `braid-state` the five `*-wrong-length` | PS-14 |
| F6-15 the Braid's coders are not sized for their values | `braid-state` decoder-sized-for-another-value, encoder-sized-for-another-value | PS-14 |
| F6-16 tag 8's fields are read in the other order | `braid-state` ek-received-ct1-sampled | BR-03 |
| F6-17 the Braid accepts bytes after its last field | `braid-state` trailing-byte, too-many-fields | PS-13 |
| F6-18 a coder its own reader refuses is accepted inside the Braid | `braid-state` coder-its-own-reader-refuses | **none** |
| F6-19 the Braid's wrong version reported as short or malformed | `braid-state` version-zero, version-two | PS-13, RJ-01 |
| F6-20 `Ct2Sampled` checks the ceiling only on a message that advances it | **none** | BR-13 |
| F6-21 transition (13) stays at the epoch it was at | `braid-state` ct2-sampled-below-the-ceiling-steps | BR-05, BR-06, BR-08, BR-09, BR-15, BR-17 |
| F6-22 transition (13) starts a fresh authenticator | `braid-state` ct2-sampled-below-the-ceiling-steps | BR-05 to BR-09, BR-15 to BR-17 |
| F6-23 the Braid key pair's content check dropped (pass 5's F5-45) | **none** | BK-01 |
| C6-01 control: a short buffer refused as short though its version is unknown | none, as Rejection allows | none |

The two new vector files catch every framing refusal, both refusal kinds, every
tag rule and every semantic rule of both formats, and the inner-refusal mapping
the page has now decided. They miss what `GAPS-6.md`, section 3, records: the
epoch a triple send names (F6-09), `Ct2Sampled` checking the ceiling before it
reads the message (F6-20), and the Braid key pair's content rule (F6-23).


**Pass 7.** Forty faults and one control (`../work/faults7.py`), each a
one-line or one-block change to a fresh copy of the reader, then the full
runner. **38 were caught, 27 of them by a vector file.** Each cell gives how
many failed and names the first few.

| Fault | Vectors that failed | Cases that failed |
|---|---|---|
| F7-01 no identifier is zero: dropped | 1: `prekey-store-state` identifier-zero | 4: PS-23, PK-03, PK-04, RJ-02 |
| F7-02 every identifier below next_id: dropped | 2: `prekey-store-state` identifier-at-next-id, `prekey-store-state` identifier-above-next-id | 2: PS-23, PK-03 |
| F7-03 every identifier below next_id: off by one, next_id itself allowed | 1: `prekey-store-state` identifier-at-next-id | 1: PS-23 |
| F7-04 identifiers pairwise distinct: dropped | 1: `prekey-store-state` identifiers-repeated | 1: PS-23 |
| F7-05 identifiers distinct across kinds only within a kind | 1: `prekey-store-state` identifiers-repeated | 1: PS-23 |
| F7-06 the bound counted over the whole record rather than per key | **none** | 1: PS-22 |
| F7-07 the bound made exclusive: a key at exactly MAX_LAST_RESORT_SEEN refused | 1: `prekey-store-state` record-at-budget | 2: PS-22, LR-05 |
| F7-08 the bound raised by one: a key one past its budget accepted | 1: `prekey-store-state` record-over-budget-for-one-key | 2: PS-22, PK-03 |
| F7-09 an entry tagged with a key that is neither live: accepted | 1: `prekey-store-state` record-entry-under-an-unknown-key | 2: PS-23, PK-03 |
| F7-10 a fingerprint twice: accepted | 1: `prekey-store-state` record-fingerprint-repeated | 2: PS-23, PK-03 |
| F7-11 the pre-sizing ceiling: v4 given one budget rather than two | **none** | 1: PS-22 |
| F7-12 the sparse epoch is the Braid's in every tag (the e - 1 branch dropped) | 3: `session-state` responder, `session-state` initiator-unanswered, `session-state` initiator-answered | 7: PS-15, SK-03, SK-04 , ... |
| F7-13 the epoch relation's boundary moved to tags 6 to 10 | 4: `session-state` tag-six-keeps-previous-sparse-epoch, `session-state` tag-seven-uses-current-sparse-epoch, `session-state` tag-six-with-current-sparse-epoch-refused, `session-state` tag-seven-with-previous-sparse-epoch-refused | 1: EP-01 |
| F7-14 the epoch relation dropped | 1: `session-state` sparse-epoch-does-not-follow-the-braid | 2: RJ-02, EP-01 |
| F7-15 a failed Braid no longer exempt from the epoch relation | 1: `session-state` failed-braid-exempts-sparse-epoch | 2: PS-15, EP-01 |
| F7-16 the Braid's half of the role rule dropped | 1: `session-state` halves-disagree-on-the-braid-role | 1: RJ-02 |
| F7-17 the sparse ratchet's half of the role rule dropped | 1: `session-state` halves-disagree-on-the-sparse-role | 1: RJ-02 |
| F7-18 the role parity inverted: the header-sending side is the initiator at even epochs | 3: `session-state` responder, `session-state` initiator-unanswered, `session-state` initiator-answered | 8: PS-15, SK-03, SK-04 , ... |
| F7-19 the role read from pending_initial rather than established_ephemeral | 1: `session-state` initiator-answered | 2: PS-15, EP-01 |
| F7-20 direction A2b read as the responder's | 4: `session-state` responder, `session-state` initiator-unanswered, `session-state` initiator-answered, `session-state` halves-disagree-on-the-sparse-role | 8: PS-15, SK-03 , ... |
| F7-21 the store's signature rule reported as malformed, not incoherent | 1: `prekey-store-state` signed-prekey-signature-does-not-verify | 9: SK-08, PK-01, PK-03, PK-04, ... |
| F7-22 the store's other five rules reported as incoherent, not malformed | 8: `prekey-store-state` identity-public-not-canonical, `prekey-store-state` identifier-zero, `prekey-store-state` identifier-at-next-id, `prekey-store-state` identifier-above-next-id, ... | 6: , ... |
| F7-23 the session's semantic rules reported as malformed, not inconsistent | 8: `session-state` sparse-epoch-does-not-follow-the-braid, `session-state` associated-data-wrong-orientation, `session-state` halves-disagree-on-the-sparse-role, `session-state` halves-disagree-on-the-braid-role, `session-state` unanswered-initiator-is-also-responder, ... | 4: , ... |
| F7-24 an unrecognised version reported as malformed, not wrong version | 11: `braid-state` version-zero, `braid-state` version-two, `prekey-store-state` version-unknown, `prekey-store-state` version-zero, ... | 9: , ... |
| F7-25 the session's re-encode check reported as inconsistent, not non-canonical | **none** | **none** |
| F7-26 the store's re-encode check reported as malformed, not non-canonical | **none** | **none** |
| F7-27 the signature rule dropped altogether | 1: `prekey-store-state` signed-prekey-signature-does-not-verify | 9: SK-08, PK-01, PK-03, PK-04, ... |
| F7-28 kem_sig verified over the whole kem_pair rather than EncodeKEM of its ek | 5: `prekey-store-state` current-version, `prekey-store-state` one-time-kem-prekey, `prekey-store-state` retired-signed-prekey, `prekey-store-state` retired-kem-prekey, `prekey-store-state` record-at-budget | 12: PS-18, PS-19 , ... |
| F7-29 the one-time KEM prekeys' signatures not checked | **none** | 1: PK-01 |
| F7-30 the retired pair's signatures not checked | **none** | 1: PK-01 |
| F7-31 the signature rule checked before the other five, not last of all | 1: `prekey-store-state` identity-public-not-canonical | 3: SK-08, PK-03, PK-04 |
| F7-32 the signed prekey's signature verified over its secret rather than its public half | 5: `prekey-store-state` current-version, `prekey-store-state` one-time-kem-prekey, `prekey-store-state` retired-signed-prekey, `prekey-store-state` retired-kem-prekey, `prekey-store-state` record-at-budget | 12: PS-18, PS-19 , ... |
| F7-33 identity_public's canonical rule dropped | 1: `prekey-store-state` identity-public-not-canonical | 2: SK-08, PK-03 |
| F7-34 the session's canonical stored-key rules dropped | **none** | 1: SK-04 |
| F7-35 established_ephemeral's shape rule dropped | 1: `session-state` established-ephemeral-wrong-curve-byte | 1: RJ-02 |
| F7-36 the associated data's orientation not checked | 1: `session-state` associated-data-wrong-orientation | 1: RJ-02 |
| F7-37 bytes left after the session's last field accepted | 1: `session-state` trailing-byte | 1: PS-16 |
| F7-38 bytes left after the store's last field accepted | 1: `prekey-store-state` trailing-byte | 3: PS-19, PS-20, PK-04 |
| F7-39 the Braid's key_pair content clause applied without the layout the page delegates | 2: `session-state` initiator-unanswered, `session-state` initiator-answered | 1: BK-01 |
| F7-40 the session's ratchet_private rule dropped | 1: `session-state` ratchet-private-does-not-match-dhs-pub | 1: RJ-02 |
| C7-01 control: the store's length checked before its version byte, which Rejection allows | **none** | **none** |

The two new vector files catch every framing refusal of both formats, all four
refusal kinds they use, the store's five cheap semantic rules and eight of the
session's top-level semantic rules, plus the two nested half-reader refusals
at the session boundary. What they miss is what `../GAPS-7.md`, section 3,
records: the remaining signature-rule edge cases (F7-29, F7-30), the per-key
bound read as a whole and the pre-sizing ceiling (F7-06, F7-11), the session's
remaining canonical-key clauses (F7-34).

**F7-13 was missed on the first run and is now vector-pinned.** The boundary
vectors carry accepted tag 6 and tag 7 neighbours and refused siblings on the
wrong side of the epoch relation; EP-01 remains as derived coverage across all
twelve tags.

**F7-25 and F7-26 are clean and cannot be otherwise.** They change the kind the
two re-encode checks report, and a reader that accepts only canonical
encodings never reaches either check, so no input tells the two readings apart.
The conformance manifest says the same of `non-canonical`: it is carried by no
vector, and cannot be.

**C7-01, the control**, checks the store's length before its version byte and
fails nothing, as Rejection allows (GAPS-5.md G5-03).

**Pass 12.** Seventy-two faults and two controls (`../work/faults12.py`), each a
textual change to a fresh copy of the reader, then the full runner. Where the
reader states a rule in two places (the decoder's field read, and the encoding
rules a built statement is held to) the fault breaks both, and says so.
**66 were caught, 61 of them by a vector file.** `../work/faults12.txt` is the
recorded run, against the final reader; `../work/faults12-first-run.txt` is the
first, which tried 66 and caught 58 (see below).

| Fault | Vectors that failed | Cases that failed |
|---|---|---|
| F12-01 active's order not checked | 7: inventory-acceptance-v1, inventory-decode-refusals-v1 | 3: IV-02, IV-05, IV-07 |
| F12-02 revoked's order not checked | 4: inventory-decode-refusals-v1 | 2: IV-02, IV-04 |
| F12-03 both orders non-strict: a repeated entry allowed | 2: inventory-decode-refusals-v1 | 1: IV-04 |
| F12-04 revoked ordered by binding alone, terminal_generation ignored | 2: inventory-acceptance-v1, inventory-statements-v1 | 3: IV-02, IV-04, IV-21 |
| F12-05 both orders descending | 77: inventory-acceptance-v1, inventory-decode-refusals-v1, inventory-statements-v1 | 10: IV-01, IV-02, IV-04, IV-05, IV-07, IV-08, ... |
| F12-06 a predecessor sorts before no predecessor (tag byte compared inverted) | 2: inventory-decode-refusals-v1, inventory-statements-v1 | 1: IV-16 |
| F12-07 order compared with device_id little-endian | **none** | 1: IV-02 |
| F12-08 order compared on device_id and key only, the rest ignored | 4: inventory-acceptance-v1, inventory-statements-v1 | 4: IV-02, IV-04, IV-16, IV-21 |
| F12-09 a tag other than 0 or 1 read as present | **none** | **none** |
| F12-10 a tag other than 0 or 1 read as absent | **none** | **none** |
| F12-09b a tag other than 0 or 1 read as present, and the re-encode check dropped | 2: inventory-acceptance-v1, inventory-decode-refusals-v1 | **none** |
| F12-10b a tag other than 0 or 1 read as absent, and the re-encode check dropped | 1: inventory-decode-refusals-v1 | **none** |
| F12-11 the predecessor read as 31 bytes | 10: inventory-acceptance-v1, inventory-statements-v1 | 4: IV-01, IV-07, IV-16, IV-21 |
| F12-12 capability word: only non-zero required (other bits allowed), decoder and encoder | 12: inventory-acceptance-v1, inventory-binding-commitments-v1, inventory-decode-refusals-v1 | 2: IV-05, IV-20 |
| F12-13 capability word: bit 0 set suffices, decoder and encoder | 5: inventory-binding-commitments-v1, inventory-decode-refusals-v1 | 2: IV-05, IV-20 |
| F12-14 capability rule dropped, decoder and encoder | 15: inventory-acceptance-v1, inventory-binding-commitments-v1, inventory-decode-refusals-v1 | 2: IV-05, IV-20 |
| F12-14e capability rule dropped from the encoder alone (so from binding_commitment and in-memory statements) | 4: inventory-binding-commitments-v1 | 2: IV-05, IV-20 |
| F12-15 capability word zero allowed (no other bit), decoder and encoder | 3: inventory-binding-commitments-v1, inventory-decode-refusals-v1 | 2: IV-05, IV-20 |
| F12-16 account bound off by one: 256 bytes refused, decoder and encoder | 3: inventory-acceptance-v1, inventory-statements-v1 | 1: IV-22 |
| F12-16b account bound dropped, decoder and encoder | 2: inventory-decode-refusals-v1 | 2: IV-22, IV-05 |
| F12-17 account UTF-8 not checked | 6: inventory-decode-refusals-v1 | 2: IV-22, IV-05 |
| F12-18 floor above generation allowed | 1: inventory-decode-refusals-v1 | 2: IV-04, IV-05 |
| F12-19 a terminal generation equal to the floor allowed | 2: inventory-decode-refusals-v1 | 2: IV-04, IV-05 |
| F12-20 a terminal generation above the generation allowed | 1: inventory-decode-refusals-v1 | 1: IV-04 |
| F12-21 an exact binding in both lists allowed | 1: inventory-decode-refusals-v1 | 2: IV-03, IV-05 |
| F12-22 "exact binding" compared on device_id and key only | **none** | 2: IV-03, IV-21 |
| F12-23 trailing bytes accepted | **none** | **none** |
| F12-23b trailing bytes accepted, and the re-encode check dropped | 3: inventory-acceptance-v1, inventory-decode-refusals-v1 | 1: IV-06 |
| F12-24 active_count above 8 accepted, decoder and encoder | 1: inventory-decode-refusals-v1 | 1: IV-05 |
| F12-24r revoked_count above 8 accepted, decoder and encoder | 1: inventory-decode-refusals-v1 | 1: IV-05 |
| F12-25 the re-encode check dropped | **none** | **none** |
| F12-26 check 1 dropped | 13: inventory-acceptance-v1 | 4: IV-22, IV-05, IV-06, IV-18 |
| F12-27 check 1 by prefix, not byte for byte | 3: inventory-acceptance-v1 | 1: IV-18 |
| F12-28 check 1 case-insensitive | 1: inventory-acceptance-v1 | 1: IV-18 |
| F12-29 check 2 resolves the asked account rather than the statement's (after check 1 they agree) | **none** | **none** |
| F12-30 check 2: an unbound issuer is not refused, and the signature is then not checked | 7: inventory-acceptance-v1 | 2: IV-06, IV-18 |
| F12-31 check 3 dropped | 19: inventory-acceptance-v1 | 2: IV-06, IV-19 |
| F12-32 check 4 dropped | 97: inventory-acceptance-v1 | 3: IV-06, IV-08, IV-09 |
| F12-33 check 5 dropped | 5: inventory-acceptance-v1 | 3: IV-07, IV-08, IV-16 |
| F12-34 check 5 over active and revoked together | 4: inventory-acceptance-v1 | 5: IV-07, IV-15, IV-16, IV-17, IV-21 |
| F12-35 check 6 dropped | 55: inventory-acceptance-v1 | 3: IV-07, IV-08, IV-15 |
| F12-36 check 7's binding policy dropped | 28: inventory-acceptance-v1 | 3: IV-06, IV-08, IV-17 |
| F12-37 check 7's statement policy dropped | 22: inventory-acceptance-v1 | 3: IV-06, IV-08, IV-17 |
| F12-38 check 2 before check 1 | 13: inventory-acceptance-v1 | 1: IV-18 |
| F12-39 check 4 before check 3 | 109: inventory-acceptance-v1 | 1: IV-09 |
| F12-40 check 6 before check 5 | 3: inventory-acceptance-v1 | 1: IV-16 |
| F12-41 check 6 interleaved with the binding policy: each key checked just before its binding's policy, not all keys first | 31: inventory-acceptance-v1 | 1: IV-15 |
| F12-42 check 6 after check 7 | 55: inventory-acceptance-v1 | 3: IV-07, IV-08, IV-15 |
| F12-43 the statement policy before the binding policy | 30: inventory-acceptance-v1 | 1: IV-17 |
| F12-44 binding policy: revoked before active | 8: inventory-acceptance-v1 | 1: IV-17 |
| F12-45 binding policy: active entries in reverse encoded order | 12: inventory-acceptance-v1 | 1: IV-17 |
| F12-46 binding policy: does not stop at the first refusal | 3: inventory-acceptance-v1 | 1: IV-17 |
| F12-47 binding policy told every entry is active | 8: inventory-acceptance-v1 | 1: IV-17 |
| F12-48 check 6: the subgroup test dropped (canonical only) | 31: inventory-acceptance-v1 | 7: IV-07, IV-08, IV-10, IV-11, IV-12, IV-13, ... |
| F12-49 check 6: small order refused (8P), mixed torsion accepted | 17: inventory-acceptance-v1 | 4: IV-10, IV-12, IV-13, IV-15 |
| F12-50 check 6: a u with no point accepted | 6: inventory-acceptance-v1 | 3: IV-07, IV-12, IV-15 |
| F12-51 check 6: u = p - 1 not excluded | **none** | **none** |
| F12-52 check 6: the canonical rule dropped, u read as X25519 reads it | 6: inventory-acceptance-v1 | 2: IV-07, IV-14 |
| F12-53 check 6 over active only | 25: inventory-acceptance-v1 | 2: IV-07, IV-15 |
| F12-54 check 6 over revoked only | 30: inventory-acceptance-v1 | 3: IV-07, IV-08, IV-15 |
| F12-55 check 6: the five listed low-order values accepted | 16: inventory-acceptance-v1 | 4: IV-07, IV-08, IV-11, IV-15 |
| F12-56 signed without the label | 98: inventory-acceptance-v1 | 1: IV-19 |
| F12-57 the label without its 0xFF terminator | 98: inventory-acceptance-v1 | 1: IV-19 |
| F12-58 the application-signature label | 98: inventory-acceptance-v1 | 1: IV-19 |
| F12-59 the signature taken from the front of the input | 136: inventory-acceptance-v1 | 11: IV-22, IV-06, IV-07, IV-08, IV-09, IV-15, ... |
| F12-60 revision 1's s bound: s below 2^253 rather than below q | 2: inventory-acceptance-v1, primitives/xeddsa | 2: XS-04, IV-19 |
| F12-61 revision 1's sign: A always taken with sign 0 | 3: inventory-acceptance-v1, primitives/xeddsa | 2: XS-02, IV-19 |
| F12-62 commitment label without its terminator | 6: inventory-binding-commitments-v1 | 1: IV-20 |
| F12-63 commitment over the binding without its predecessor | 4: inventory-binding-commitments-v1 | 1: IV-20 |
| F12-64 the generation recorded when check 4 accepts, before checks 5 to 7 | **none** | 2: IV-08, IV-17 |
| F12-65 the issuer signs without applying check 6 | **none** | 1: IV-07 |
| F12-66 a statement built in memory not held to the encoding rules | **none** | 2: IV-05, IV-07 |
| C12-01 control: check 6 walks revoked before active (the page fixes active first; no outcome depends on it) | **none** | **none** |
| C12-02 control: the signed input parsed from the front, then exactly 64 bytes required | **none** | **none** |

- **Not caught, six.** F12-09, F12-10 and F12-23 are each masked by the
  re-encode rule, which refuses any input whose re-encoding differs; with that
  check removed too (F12-09b, F12-10b, F12-23b) each is caught by vectors.
  F12-25, the re-encode check alone, is clean for the converse reason. F12-29
  is an equivalent change, check 1 having made the two accounts equal. F12-51
  is equivalent in this reader's arithmetic: without the explicit step,
  u = p - 1 gives y = 0 (1/0 is taken as 0), a point of order four, which the
  subgroup step refuses.
- **F12-07 was missed on the first run**: no vector and no case put two
  entries of one list on either side of a byte boundary. IV-02 was extended and
  now catches it (`../GAPS-12.md`, section 3).
- **F12-41 was written wrong on the first run** (it left check 6 in place), and
  the capability, account-length and count faults broke only the encoder's copy
  of their rule. All were rewritten; F12-14e keeps the encoder-only version.
- **Caught by cases only:** F12-07, F12-22, F12-64, F12-65, F12-66.
- **C12-01 and C12-02**, the controls, fail nothing: check 6's own order and
  the way a signed input is split change no outcome.

## Not implemented

- ML-KEM-1024 and its incremental split. The Braid runs over `kem_double.py`.
- The end-to-end `Session` implementation as a live object: the handshake with
  a real KEM, `pending_initial` resend, `established_ephemeral`, and
  export/import over live states. The real-primitive session vectors are
  handled by derivation instead (below).
- The real-primitive session vectors (`session-e2e.json`) are **derived**, not
  echoed: `session_e2e.py` computes from each vector's inputs both message keys,
  the composite headers, the AEAD, the initial message and its repeat, the
  bundle (with both signatures recomputed from their nonces), the responder's
  agreements for every spelling of the ephemeral, Bob's sessions after the
  first message and after the repeat byte for byte, Alice's session after her
  first send, the responder's prekey store after the first message, the
  last-resort replay identity and record, and each refusal, and compares each
  with the vector. **What it does not derive**, so that "partially" has a
  definition:
  - ML-KEM-1024 in every form. The bundle's KEM prekey, the encapsulation's
    ciphertext and shared secret are taken from the vector; the reader checks
    their length, the FIPS 203 encapsulation-key modulus check and the
    signatures over the keys. The inputs that feed them, `bob_last_resort_kem_d_z`,
    `bob_one_time_kem_d_z` and `alice_kem_encapsulation_m`, are not read.
  - The Braid's key generation: the header a first composite header carries a
    codeword of (the 96-byte value, header and MAC, is checked against its MAC
    under the authenticator derived from SK, not recomputed), Alice's stored
    Braid `key_pair` (11,872 bytes whose layout the specification delegates),
    and the input `alice_braid_keygen_d_z`.
  - The KEM key pair inside the responder's stored prekey store, apart from the
    FIPS 203 checks its reader makes and the signature over its public half:
    the first 1,536 and the last 32 bytes of its decapsulation key are not
    checked.
  - `bob_repeat_random`, and the `z` half of each `d || z` input: consumed by
    the implementation and unobservable in any output.
  `test_session_e2e_sweep.py` holds this list to the code: it corrupts sampled
  bytes of every input and field and requires the reader to notice all of them
  except these.
- Group messaging beyond the two fan-out commitments and the hosted inventory
  statement (pass 12), and device management, which identities-and-devices.md
  leaves outside itself.
- Prekey store operations other than the two rotations `prekeys.py` adds:
  `create_prekeys`'s numbering, `replenish`, `publish` selection,
  `establish_responder`. The rotations were added in pass 7 because the store's
  new sixth rule puts an obligation on the operations that sign a prekey, and
  the page states the refusal for them (GAPS-7.md G7-04 records that it states
  it for no other).

- A session router: which session an initial message goes to. What follows
  `NotARepeatedInitial` is now stated, and left to the application
  (GAPS-4.md G4-04, closed).
- The library layout of the Braid's `key_pair` and `encaps`. **This is no
  longer a shortfall.** The `key_pair` content clause of tags 1 to 4 is scoped
  to a reader that has that layout; this reader checks the field's length,
  accepts the content, and conforms (GAPS-7.md, G5-02 closed).

The reasons are in `../GAPS-3.md` to `../GAPS-7.md` ("Not attempted"). The
real-primitive `session-e2e.json` added after pass 9 is handled by derivation up
to the explicit ML-KEM and Braid-key-generation boundaries listed above.
`../GAPS-10.md` remains the historical record of the earlier skip.

## Running

```
python3 reader/run.py                        # from the clean-room directory
python3 reader/test_skip_allowlist.py        # the skip gate fails when it should
python3 reader/test_session_e2e_sweep.py     # corrupt the session vectors byte by byte
python3 work/faults12.py               # the pass-12 deliberate faults and controls
python3 work/check_new_vectors12.py    # pass 12: the 237 inventory vectors pass for the stated reasons
# the pass-4 to pass-7 scripts were not in the tree pass 12 was read from
```

The pass-4 to pass-7 fault scripts (`work/faults*.py` and the pass-7 checks) were
scratch files of the clean-room directories and are not in the repository.

The runner prints:

1. one line per vector (`PASS`, `FAIL` with a short diff, or `SKIP` with a reason);
2. one line per derived case;
3. a per-file table with a vectors subtotal, a derived-cases subtotal and a total.

The exit status is non-zero on any FAIL, or when the observed skips differ from
the checked allowlist in `run.py`. A full run takes about ten seconds on a
laptop; the sweep takes about thirty.

Current result. "Vector checks" are the lines that name a vector; "derived
cases" are the `negative ::` lines, each a case the reader's authors derived
from a sentence of the specification; the total is their sum, and the run's own
`vectors subtotal`, `derived cases subtotal` and `TOTAL` lines print the same
three numbers:

| | Count | PASS | FAIL | SKIP |
|---|---|---|---|---|
| Vector checks (42 files) | 688 | 688 | 0 | 0 |
| Derived cases (13 modules) | 245 | 245 | 0 | 0 |
| **Total** | 933 | 933 | 0 | 0 |

The run compares this table, the pass-11 record below and `../GAPS-11.md` with its own
totals and fails when they differ, so a count here cannot go stale silently.

## In this repository

Copied into `tacenta-test-vectors/runners/independent/` from the clean-room
reader, and changed in the repository since (Provenance, above). In this README,
`../tacenta-spec` and `../tacenta-test-vectors` name the clean-room directory it
was written in. In the repository they are the repository's own `tacenta-spec`
and `tacenta-test-vectors`. Run it from the repository root with

```
python3 tacenta-test-vectors/runners/independent/reader/run.py
```

`tooling/ci.sh` and the CI `vectors` job both run it.

**Keeping it independent** (ADR-0006). This is the rule for a clean-room pass;
passes 8 to 11 did not follow it, and the record above says so:

- A change to this reader is made from the specification and the vectors only,
  by someone who has not consulted `tacenta-core`, `tacenta-model`,
  `tacenta-proofs` or the Rust runner for that change.
- When a change to the specification, the model or the vectors breaks it, the
  breakage is a question about the specification. It is answered there, not by
  reading the implementation.

Each gap report re-assesses its predecessors against the revision it names:

- `../GAPS.md`: the first pass.
- `../GAPS-2.md`: the second pass.
- `../GAPS-3.md`: the third pass.
- `../GAPS-4.md`: the fourth pass.
- `../GAPS-5.md`: the fifth pass.
- `../GAPS-6.md`: the sixth pass.
- `../GAPS-7.md`: the seventh pass.
- `../GAPS-8.md` to `../GAPS-10.md`: maintenance records (below).
- `../GAPS-12.md`: the twelfth pass, the hosted device-inventory statements.

A gap is closed by changing the specification. Its entry is marked closed when
the reader is next updated from the new text.

### Pass 8 record

`../GAPS-8.md` records a maintenance re-run against the later vector and
specification changes. It leaves `GAPS-7.md` as the historical seventh-pass
record and places the four subsequent gap closures in the new pass instead.

### Pass 9 record

`../GAPS-9.md` records a maintenance re-run for the Double Ratchet
replacement-bound repair at implementation commit `3e2745f`. It reuses this
reader and makes no claim of a new clean-room implementation or independent
review.

### Pass 10 record

`../GAPS-10.md` records a maintenance re-run after the real-primitive
end-to-end session vector was added at `44409c6`. The reader's unchanged
handlers report
the new vector as one explicit skip because its documented boundary excludes
real ML-KEM and a live end-to-end session. It makes no claim of a new
clean-room implementation or independent review.

### Pass 11 record

Not a clean-room pass, and it has no isolation record (see Provenance). It
replaced the reader's earlier partial handling of
`session-establishment/session-e2e.json`, which took the message keys, the
composite header and most of the persisted state from the vector and checked
that the persisted sessions re-encoded, with a derivation of the whole vector
from its inputs (`session_e2e.py`) for both of its vectors, and it taught the
reader the `legacy_blocked` rules of `session-persistence.md`, Legacy markers.
`../GAPS-11.md` records the run, what the reader derives, and what it does not.
At this pass the run was 671 PASS, 0 FAIL, 0 SKIP (450 vector checks and
221 derived cases). With the four hosted-inventory files and the pass-12
derived cases merged, the current run is **933 PASS, 0 FAIL, 0 SKIP** (688 vector checks
and 245 derived cases). This supersedes the earlier pass-10 skip tally;
`GAPS-10.md` remains the historical record of that earlier run.

### Pass 12

`../GAPS-12.md` is a clean-room pass, the first since pass 7. It extends this
reader from the specification and the vectors alone to read the four
`vectors/groups/inventory-*.json` files, re-assesses every gap left open, and
records the deliberate-fault run. It is numbered 12 because another branch may
use 11.
