# Session and prekey operation traces: supplement, version 2

This is a separately versioned supplement to the operation-trace grammar in
[`session-operation-trace.md`](session-operation-trace.md) (version 1). It adds
what version 1 cannot express about the message size bound
(tacenta-spec/protocol/message-format.md, Message size): the sender's refusal
of a plaintext that is too long, the size rule's refusal of a received frame,
their precedence over the refusal of a failed agreement, and the fact that
neither draws a random value.

## Provenance

**Not independently authored.** This supplement, its schema
([`schema/session-operation-trace-supplement.schema.json`](schema/session-operation-trace-supplement.schema.json))
and its traces
([`traces/session-operation-trace-supplement.json`](traces/session-operation-trace-supplement.json))
were added by the maintainer account with tool assistance, with
`tacenta-core`, the model and the Rust runner in view. They are a **temporary disposition**, to be accepted only as such, and only after review of the exact change that adds them, not part of the P6 operation reader's evidence (its author is a specification-only author and a related party). The supplement's traces remain **outside the specification-only reader's coverage** until a specification-only reader pass reads them.

**Why a supplement, not an edit of version 1.** Version 1, its schema and its
27-trace corpus are the input the P6 operation reader (specification-only author, related party) was written from and run against (`runners/independent/P6-OPERATION-READER-EVIDENCE.md`),
which records the packet's and the reader's digests and says it is evidence
for that committed corpus only. Editing version 1 would change the files that
record describes, and the reader would meet operations and refusals its author
never saw. So version 1 stays as it is, and this supplement is a second file
with its own schema version. `runners/independent/session-operation-reader.py`
does not read it, and nothing here counts as read by a specification-only reader: a specification-only reader pass must read this supplement before its traces are counted as covered by such a pass, and no such reading counts as independent review.

## What it adds to version 1

A supplement document has `schema_version` 2, `algorithm`
`session-operation-trace-supplement`, a `source` citing the pages, and a
`provenance` string that must say it is not independently authored. Its traces
have the shape of version 1's, and every rule of version 1 holds, with these
additions:

- **`expect.refusal`** may also be:
  - `PlaintextTooLong`, the sender's rule's refusal, a condition the caller
    must act on (error-handling.md, Conditions a caller must act on are
    named);
  - `AgreementFailed`, the refusal of a session whose agreement has failed
    (mlkem-braid.md, Failure), which version 1 leaves unnamed.

  The size rule's refusal of a received frame stays `decode-failure`, which is
  what the page says it is (message-format.md, Message size). A step that
  shows it names the frame's size in its fixture.
- **`effect.random_draws`**, optional, with the one value `none`: the
  operation draws no random value. Version 1 deliberately says nothing about
  random-source calls; this field is used only where a page states that an
  operation draws nothing, and the size refusals are such a case
  (message-format.md, Message size: "no random value is drawn"). An omitted
  field is outside the step's claim, as in version 1.
- **`inputs.plaintext_length`**, a decimal string: the length of the plaintext
  a `send` encrypts, where the trace's claim is about its length.

A step refused with `PlaintextTooLong`, and a step whose fixture is a frame the
size rule refuses, must state `random_draws: none` and leave the prekey store
and the session `unchanged`; a responder step must also state
`one_time_curve`, `one_time_kem` and `last_resort_record` as `unchanged`.

## Required traces

The committed supplement must contain:

1. a send refused as `PlaintextTooLong` on a pending initiator's session (the
   first initial message), and on an established session, each followed by an
   accepted send of `MAX_PLAINTEXT_LEN` bytes on the established session;
2. a send refused as `PlaintextTooLong` on a session whose agreement has
   failed, followed by a short send on the same session refused as
   `AgreementFailed` (the order the page fixes);
3. responder establishment refusing an initial message one byte over
   `MAX_INITIAL_FRAME_LEN`, then establishing from the genuine message, so the
   refusal is seen to have consumed nothing;
4. a receive refusing a ratchet frame one byte over `MAX_RATCHET_FRAME_LEN`,
   then accepting the genuine message;
5. a repeated initial message re-wrapped with an empty `kem_ciphertext` around
   a ratchet message one byte over `MAX_RATCHET_FRAME_LEN`, refused, then the
   genuine repeat accepted;
6. a receive on a session whose agreement has failed, refusing an oversized
   frame as too long (`decode-failure`) rather than as `AgreementFailed`;
7. within the bounds, on a session whose agreement has failed, the order
   mlkem-braid.md, Failure, fixes: a malformed and a well-formed frame that is
   not an initial frame refused with `AgreementFailed`, a malformed initial
   frame refused as a decode failure, another handshake's initial frame naming
   unknown prekeys refused as `NotARepeatedInitial`, and the repeat, with and
   without unknown prekey identifiers, refused with `AgreementFailed`, each
   with no change and no draw; and
8. a control the consumer must fail: an oversized plaintext declared accepted.

## Who reads it

- `tooling/check-session-operation-traces.py` checks its structure, its
  required traces and the rules above, as it does version 1's.
- `tacenta-test-vectors/runners/rust/tests/operation_trace_supplement.rs`
  drives every trace through `tacenta-core` and compares each step's outcome,
  refusal and effects (stored session and store bytes, random-source calls)
  with what the trace declares, and requires the control to disagree.
- The model states the same refusals and effects
  (`Model.Lifecycle.encrypt_plaintext_too_long`, `decrypt_frame_too_long`,
  `establishResponder_frame_too_long`; tacenta-model/docs/mapping-to-spec.md,
  Message size). It does not read the trace file.
- No specification-only reader reads it (Provenance, above).
