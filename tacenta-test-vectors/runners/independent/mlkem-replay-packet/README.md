# ML-KEM and Braid key-generation replay packet

This is the brief for a person who extends the independent reader to compute the
ML-KEM-1024 and Braid key-generation values of the session end-to-end vector and
the one identity vector the reader skips today. It exists to make that work
small and to say, before it starts, exactly what is asked.

It answers one open item, `HL-IMP-01-READER` in `GAP-REGISTER.md`:

> A reader that computes the ML-KEM and Braid key-generation values except the
> delegated `key_pair` (11,872 bytes in two vectors, never checked by an
> independent reader; ADR-0006 point 5), and the skipped identity vector, written
> or run by a person who did not write the model, with the run recorded; needed
> before the Gate 3 review.

The packet does not do that work and does not close the item. A person doing the
work, and the record they write at the end, are what the item asks for. The
maintainer reads the record and decides.

Files in this packet:

- `README.md`: this brief.
- `TARGETS.md`: every value to compute, with its inputs, where the vector pins
  it, the specification pages it comes from, what the reader does with it today,
  and the order and effort.
- `GAPS-TEMPLATE.md`: the form of the gap report.
- `RECORD-TEMPLATE.md`: the record to write at the end.
- `build-directory.py`: the maintainer's script that builds the directory below.
  The person does not need it.

## What you receive

Exactly these, and nothing else:

1. A directory built by `build-directory.py`. It holds the specification
   (`tacenta-spec/`), the vectors (`tacenta-test-vectors/vectors/`, `schema/`,
   `README.md`, `conformance-manifest.md`) and the existing reader
   (`tacenta-test-vectors/runners/independent/reader/`), in the repository's own
   layout so the reader runs unchanged. There is no git history, no
   implementation, no model, no proof and no Rust. The earlier gap reports
   (`GAPS*.md`) are not in it; the reader's comments cite them by number.
2. The manifest the script wrote beside the directory, a JSON file with the
   source `revision` and a `files` list of `path`, `bytes` and `sha256`. It is
   the one file outside the directory you may open. Check the directory against
   it before you start, from the directory's parent:

   ```text
   python3 - MANIFEST.json DIRECTORY <<'EOF'
   import hashlib, json, pathlib, sys
   m = json.load(open(sys.argv[1]))
   root = pathlib.Path(sys.argv[2])
   listed = {f["path"] for f in m["files"]}
   bad = [f["path"] for f in m["files"]
          if hashlib.sha256((root / f["path"]).read_bytes()).hexdigest() != f["sha256"]]
   extra = sorted(str(p.relative_to(root)) for p in root.rglob("*") if p.is_file()
                  and str(p.relative_to(root)) not in listed)
   print("revision", m["revision"], "files", len(listed), "differ", bad, "extra", extra)
   EOF
   ```

   It must print no differing and no extra file.
3. These documents: `README.md`, `TARGETS.md`, `GAPS-TEMPLATE.md` and
   `RECORD-TEMPLATE.md`.

The vectors contain no secrets. Every private value in them is a test value, a
byte repeated 32 or 64 times, chosen so a reader can reproduce the outputs.

On 2026-10-03 the project ran an earlier form of this brief itself, with a
program and not with a person who did not write the model. That dry run is project-controlled and is not
independent evidence. It matched every vector value it computed and 80 of 80
published NIST ML-KEM-1024 cases. Its record is held and will be published
together with yours. You are asked not to look for it, and your record asks
whether you did.

## Who may do this

A named person who did not write `tacenta-model`, `tacenta-proofs`,
`tacenta-core` or the reader's maintenance code (the reader's `README.md`,
Provenance, lists that code). The record carries your declaration. If a program
wrote any part of the code, say which part and which program. The item asks for a
person, and the maintainer decides whether that part counts.

## Isolation

Work only inside the directory you were given. The four documents of this packet
and the manifest are the only other things you read.

- Do not read, list or search anything outside it. In particular not
  `tacenta-core`, `tacenta-model`, `tacenta-proofs`, the Rust runner, any git
  history, or notes from other work on this project.
- Do not read libsignal, libcrux or any other ML-KEM, X25519 or Signal
  implementation, source, fixtures or transcripts.
- Allowed from outside: the published standards the specification cites (FIPS
  203 and FIPS 202 for the KEM and SHA-3, RFC 5869, RFC 7748, FIPS 180-4) and
  published known-answer vectors for those standards. The standards carry few
  worked values. NIST publishes ML-KEM known answers in the ACVP-Server
  repository, `usnistgov/ACVP-Server`, under `gen-val/json-files/`:
  `ML-KEM-keyGen-FIPS203/` and `ML-KEM-encapDecap-FIPS203/`, each with
  `prompt.json` and `expectedResults.json`, with groups for each parameter set
  (use ML-KEM-1024). Fetching those four files is allowed. Record the address,
  the date, the size and the SHA-256 of each, and the repository commit if you
  can: a branch name does not pin content.
- Use the Python standard library only; `hashlib` has `sha3_256`, `sha3_512`,
  `shake_128` and `shake_256`. The reader stays standard library only.
- You may run an existing FIPS 203 implementation as a black box, as an extra
  cross-check and nothing more: do not read its source, do not import it into the
  reader, and record which one, which version and how you ran it.
- Write temporary files only under `work/` in the directory.
- Where a value needs something the text does not give, do not work it out from
  the vector's bytes. Record a gap. A reading that a vector then confirms is
  still a gap. Guesses about the layout of a delegated field are not wanted; the
  gap is the finding.
- Do not ask the maintainer what a page means. The answer to "what does the page
  mean here" is "record it as a gap". Questions about the packet itself, about
  tooling, and about delivery are fine.
- If you read or list anything outside the directory, record exactly what in the
  record, in the isolation section, in plain words: what, where, and that it was
  or was not opened. Listing the directory itself prints its parent's entry, and
  a command run in the background may leave its console output elsewhere. Those
  are the usual events, and one line each is enough:
  "the output of one command was saved outside the directory and not opened".

## What the reader does and skips today

At the revision in the manifest,
`python3 tacenta-test-vectors/runners/independent/reader/run.py`, run from the
directory root, ends with `TOTAL 1027 0 1`: 1,027 pass, none fail, one skipped.
The reader was written in the repository by people who could see the
implementation, so it is maintenance, not a clean-room reading (its `README.md`,
Provenance). It computes a great deal of the session end-to-end vector from the
inputs (the Diffie-Hellman values, the shared secrets, the ratchets, the
authenticated encryption, the wire and stored bytes), and takes the following
from the vector instead, because it has no ML-KEM:

- **ML-KEM-1024 in every form.** The bundle's KEM prekey, `kem_ciphertext` and
  `kem_shared_secret` are read from the vector. The reader checks their length,
  the FIPS 203 modulus check on the key, and the signature over the key. The
  inputs that produce them (`bob_last_resort_kem_d_z`, `bob_one_time_kem_d_z`,
  `alice_kem_encapsulation_m`) are not read. `tacenta_reader/kem_double.py` is a
  test double for the Braid's state machine and its header says it is not
  ML-KEM.
- **The Braid's key generation.** The first message carries codeword 0 of a
  96-byte value (the 64-byte header and its 32-byte MAC). The reader takes that
  value from Alice's stored encoder, checks the MAC, and checks that the wire
  codeword is the encoder's first chunk. It does not check that the header is
  what key generation makes from `alice_braid_keygen_d_z`, which is not read.
  The stored `key_pair` (11,872 bytes in `alice_session_after_first_send`) is
  not checked.
- **The responder's stored KEM key pair.** In `bob_prekey_store_after_receipt`
  the reader checks the FIPS 203 hash and modulus rules the page states and the
  signature over the public half. It does not check the pair against the input
  that made it.
- **`bob_repeat_random`, and the `z` half of each `d || z` input.** The reader's
  notes call these consumed and not observable. Whether that holds for each of
  them is part of what you check.
- **One identity vector.** `vectors/identity/initial-message-admission.json`,
  vector `honest-initial-message`, is skipped, and `run.py` lists the skip in
  `EXPECTED_SKIPS` with its reason. The reader runs that vector up to the point
  just before decapsulation and stops: it does not decapsulate, derive `SK`,
  authenticate the ratchet message or recover the plaintext. The ten refused
  vectors beside it pass.

Why this is a gap: each of those values has been checked only by the code that
produced it. Until a reader written from the text computes them, a mismatch
between the text and the implementation in those places would go unseen.

## What you do

`TARGETS.md` has the full list with the pages and fields. In short:

1. **K: ML-KEM-1024.** Implement FIPS 203 key generation, encapsulation and
   decapsulation for ML-KEM-1024 as the specification states them
   (`session-establishment.md`, ML-KEM-1024 (FIPS 203); `session-persistence.md`,
   Prekey store). Check them against the published FIPS 203 known-answer vectors
   first, then against the project vectors: the bundle's key, the stored key
   pairs, `kem_ciphertext` and `kem_shared_secret`.
2. **B: the Braid's key generation.** Derive the 64-byte header from
   `alice_braid_keygen_d_z` as `mlkem-braid.md`, The KEM split, states, add the
   header MAC from the authenticator the page defines, and compare the 96-byte
   value with Alice's stored header encoder and with codeword 0 on the wire.
3. **I: the identity vector.** Run `honest-initial-message` to the plaintext:
   decapsulate with the stored key pair, derive `SK`, and receive the ratchet
   message. The reader already has the later steps, which the session end-to-end
   vector uses.

   The stored `key_pair` is outside the task. Its layout is delegated to the KEM
   library (`session-persistence.md`, Braid; ADR-0006 point 5) and the item
   excludes it.
4. **R: keep the reader's gates true.** When a skip or an unchecked region goes
   away, update what documents it: `EXPECTED_SKIPS` in `run.py`, the tally
   sentences in `reader/README.md`, and the lists in `session_e2e.py` and
   `test_session_e2e_sweep.py`. Each of those checks fails when the document and
   the run disagree.

Leave `kem_double.py` in place. The Braid's state-machine cases run on it.

Change nothing outside `tacenta-test-vectors/runners/independent/reader/`. Where
other documents (the vectors README, `conformance-manifest.md`, a specification
page) now say something your work shows to be stale or wrong, list it in the
record, in the section for documents made stale. Do not edit them.

Not asked: editing the specification or the vectors, opening a pull request,
touching any repository, or judging the project. If the text is wrong or silent,
the finding is a gap in your report.

## When the computed value does not match

A mismatch with a vector is a finding about one of three things: the
specification text, the vector, or your reading of the text. Do not search for a
variant that happens to match.

1. First check your ML-KEM against the published FIPS 203 vectors. If it fails
   there, the fault is yours; fix it.
2. If it passes there and the vector disagrees, record the mismatch: the target,
   the sentence you relied on (page, section), the expected and computed values
   (the first 16 bytes and the SHA-256 of the whole value), and which of the
   three you believe is at fault and why.
3. Where the text allows more than one reading, you may try each reading. Record
   every reading you tried and which one the vector accepted. That is a gap of
   severity AMBIGUOUS, even though a reading matched.

## Gap reports

Write `GAPS-MLKEM.md` at the directory root, in the form of `GAPS-TEMPLATE.md`.
The maintainer numbers it on import.

- **BLOCKING:** cannot be implemented from the text without guessing.
- **AMBIGUOUS:** more than one reading, or only a vector decided it.
- **MINOR:** wording, a pointer, or a value found only in the wrong place.

Also list vector gaps: rules the text states that no vector pins.

## Output

At the end the directory holds:

- your changes under `tacenta-test-vectors/runners/independent/reader/`, and
  nothing else changed;
- `RECORD.md`, from `RECORD-TEMPLATE.md`;
- `GAPS-MLKEM.md`;
- `run-output/`: the saved output of the three commands below, and any file the
  record's results table cites;
- `work/`: your scratch, which may be discarded.

The three commands, from the directory root, must exit 0 when the work is done.
Together they take about a minute (`run.py` about 20 seconds, the sweep about 40):

```text
python3 tacenta-test-vectors/runners/independent/reader/run.py
python3 tacenta-test-vectors/runners/independent/reader/test_skip_allowlist.py
python3 tacenta-test-vectors/runners/independent/reader/test_session_e2e_sweep.py
```

Return a `.tar.gz` of the directory, without `__pycache__` and without the
contents of `work/`, with the SHA-256 of the archive, and the SHA-256 of the
manifest you started from. If you could not finish, return what you have with
the record saying where you stopped; a partial record is useful.

## Effort

The estimate and the order of work are in `TARGETS.md`, Order and effort. If a
target takes far longer than its estimate, stop, record the gap or the blocker
and move to the next target. B needs only K's key generation, and I needs K's
decapsulation, so a person with limited time can stop after K, after B, or after
I.

## What the record can and cannot show

If the declarations in the record hold, the run is a person's reading of the
text, recorded, and the maintainer can weigh it against the item. It does not
show that the specification is complete, that the implementation is correct, or
that any other value in the vectors is right. It also does not itself close the
item, change any assurance level or satisfy any gate. Those are the maintainer's
decisions, taken after reading the record.
