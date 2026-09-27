# Independent reader: pass 11 record

**Date:** 2026-09-27

This is a maintenance re-run of the independent reader after the partial
session-e2e handler and its repeat-initial controls were completed. It does not
claim a new clean-room implementation or an independent review.

## Scope

The reader now executes `session-establishment/session-e2e.json` at the public
component boundary. It independently checks the bundle, all four classical
agreements, the PQXDH and split equations using the vector's KEM shared-secret
boundary, initial and ratchet wire encodings, associated data, AEAD composition,
and both persisted session states. For the repeated-initial extension it also
checks the inner ratchet dispatch and refuses the low-order control without
mutating the persisted responder state.

ML-KEM-1024 decapsulation and the full live `Session` implementation remain
outside this reader's scope. The KEM shared secret is therefore an explicit
input boundary; this record makes no independent claim about KEM decapsulation
or end-to-end Session execution.

## Run

From the repository root:

```text
python3 tacenta-test-vectors/runners/independent/reader/run.py
```

The run exits zero with **651 PASS, 0 FAIL, 0 SKIP**: 431 vector checks and 220
derived cases. The session-e2e vector is executed by its handler and is not in
the skip set. The skip allowlist mutation controls also pass:

```text
python3 tacenta-test-vectors/runners/independent/reader/test_skip_allowlist.py
```

This maintenance record supersedes the current tally in `GAPS-10.md` while
leaving that historical pass unchanged.
