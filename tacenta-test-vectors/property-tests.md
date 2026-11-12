# Property-test index

Which specification sentence each generated-input test of this repository tests,
read from the test's assertions, and what each component row of `ASSURANCE.md`
has as property tests. Written on 2026-11-08 against an earlier `main` and
corrected the same day after a first read; re-checked against this tree, and
extended with the generated-input tests `main` gained since, on 2026-11-12.
Every file:line below is at the tree that contains this file, and a change that
moves a cited line updates it here. It was written with tool assistance under
the maintainer's account; the reads were by tool-assisted readers working for
the maintainer, and no reader independent of the maintainer has read it.

This file states what the tests check. It records no level and changes no tick:
`ASSURANCE.md` does that, and `GAP-REGISTER.md` records the deficits section 4
finds.

## 1. What counts, and how this index is used

ADR-0008's L1 asks for "Unit and property tests". A test is counted here as a
property test when it has all five of:

1. **A generator** over a stated domain that varies the input the property
   quantifies over: a `proptest` strategy, or a seeded generator in the test.
   One fixed scenario repeated under several seeds is not one.
2. **A stated property**: a predicate meant to hold for every input of the
   domain, written in the test's doc comment or its assertion messages. A test
   name alone does not state one.
3. **Traceability to a specification sentence**: the test's own doc comment or
   body names a page under `tacenta-spec/` with its section, a `REQ-`
   identifier, or quotes the sentence; or the file or module header names, for
   every test in the file, one page and section, so that the reference is
   unambiguous; or this index maps the test to one. A page named in a header
   without its section, a review identifier or a Lean file name does not count
   on its own. Where no page states the property (zeroization, a totality, an
   internal invariant), the test supports a tick only as an additional test, and
   the tables say "no sentence".
4. **Replay information**: a seed fixed in the source, or the failing input
   printed on failure. `proptest` shrinks a failing case and prints the minimal
   input; its default failure persistence writes the failing seed to a
   `*.proptest-regressions` file beside the test source, which the next local
   run replays first. No such file is committed, and no workflow keeps one.
5. **A stated case count**: a constant in the test, or `PROPTEST_CASES`, which
   the hosted `rust` job sets to 2,048 (`.github/workflows/ci.yml`) and
   `tooling/ci.sh` defaults to 2,048; proptest reads the variable over a file's
   own configuration. A bare `cargo test` uses the file's configuration, or
   proptest's default, 256, where the file sets none.

A test counts only where a gate that runs on every push runs it: the hosted
`rust` job (`cargo test --locked --workspace` in `tacenta-core`), its
`rust_spqr_erasure` step, or the hosted `vectors` job (`cargo test --locked
--workspace` in `tacenta-test-vectors/runners/rust`). That a gate runs a test is
not evidence that the test passed there: this file records no hosted run of any
test, and a `GAP-REGISTER.md` row that asks for one is met only by the run its
acceptance names.

**Whether the assertions test the sentence is judged, not read off a comment.**
Each row below says "tests it" when the assertions check what the sentence
states over the generated domain, "in part" with what is not checked, or
"does not test it" with the reason. A comment or an index row that names a page
does not by itself make a test evidence for that page.

**The differential harness is model-dependent evidence.**
`tacenta-test-vectors/runners/rust/tests/differential.rs` runs generated
operation sequences through `tacenta-core` and through the model
(`tacenta-model`) and compares outcomes and bytes. Where it meets the five
elements it is counted below, labelled "model-dependent": the oracle is the
model, so a rule the model states wrongly agrees with itself, and the harness
is not independent confirmation of the specification. It runs one fixed seed
(`SEED`, `0x7ace_07a0_d1ff_0008`) of 48 sequences of 20 steps on every push, in
the hosted `vectors` job, which fails rather than skips when the model's
executable is missing. Results from any harness or run outside this repository
are not evidence here and support no tick.

## 2. The generated-input tests that existed before this index

Elements: G generator, P property stated, S sentence cited in the test's own
text (before this index), R replay, N count. "Index" gives the sentence this
index maps the test to, where the assertions test it.

| # | Test | Subject | G P S R N | Sentence (page, section) | Assertions against the sentence |
|---|---|---|---|---|---|
| 1 | `tacenta-core/spqr/src/tests.rs:306` `no_operation_leaves_a_stored_key_at_or_past_its_chain_counter` | sparse ratchet send, receive, eviction | yes yes yes yes yes (40 seeds by 300 steps) | sparse-pq-ratchet.md, Receiving: "so no operation applied to a state the operations produced leaves a key stored at a number past its chain's counter" | Tests it, over hostile receive orders. Openings of epochs are honest only, so the page's own caveat about an epoch opened past the current one is not exercised |
| 2 | `tacenta-core/ratchet/src/lib.rs:1763` `the_invariant_holds_after_every_step_and_round_trip` | Double Ratchet send, receive, `invariant`, `to_bytes`/`from_bytes` | yes yes no yes yes (60 rounds) | session-persistence.md, Principles ("the tests and the fuzz targets in `tacenta-core` assert the predicate after every operation") and Semantic rules of the leaf formats, Ratchet state | In part: the predicate asserted is the crate's own `invariant()`, not a separate statement of the rules; honest runs only; the store cap, the counter ceiling and the canonical-key clause are not reached |
| 3 | `tacenta-core/spqr/src/tests.rs:931` same name | sparse ratchet, with `direction`, `epoch` | yes yes no yes yes (60 rounds) | session-persistence.md, Semantic rules of the leaf formats, Sparse ratchet state (the epoch window, retirement, no two stored keys at one epoch and number) | In part: honest runs; the 2,000-key cap is not approached |
| 4 | `tacenta-core/triple/src/tests.rs:424` same name | Triple Ratchet send, receive, `commit` | yes yes no yes yes (60 rounds) | session-persistence.md, Semantic rules of the leaf formats, Triple ratchet state (both ratchets' rules; `direction` against the starting role) | In part: the role clause is asserted directly only at the start, and later only through `invariant()` |
| 5 | `tacenta-core/erasure/src/lib.rs:941` `the_invariants_hold_after_every_step_and_round_trip` | erasure `Encoder`, `Decoder`, `to_bytes`/`from_bytes` | yes yes no yes yes (6 rounds) | session-persistence.md, Semantic rules of the leaf formats, Erasure encoder and Erasure decoder; mlkem-braid.md, The erasure code, Decoding | In part: repeats exercise index uniqueness; the 65,536 cap and exhaustion are not reachable at these sizes, and "at most `needed`" is not reached because the loop stops at the message |
| 6 | `tacenta-core/erasure/src/lib.rs:1038` `interpolate_agrees_with_the_barycentric_form` | `interpolate` against `weights`, `coefficients`, `evaluate` | yes yes no yes yes (4,000) | none | Does not test a sentence: it compares two forms in the crate with no value from the page, and draws duplicate nodes the page excludes. A refinement check; section 3 adds the page's formulas |
| 7 | `tacenta-core/protobuf/src/lib.rs:1168` `no_input_panics` | protobuf `Reader` | yes no no yes yes (4,096) | none | Does not test a sentence: no property is stated on it and it asserts nothing; a panic check only. Section 3 adds the profile's properties |
| 8 | `tacenta-core/boundary/src/dh.rs:348` `generated_public_keys_are_accepted` | `is_prime_order_public` on honest keys | yes yes no yes yes (512) | identities-and-devices.md, Accepting a signed statement, check 6: "A key an honest device publishes is the X25519 public key of a clamped secret, which is `kB`, so it passes." | Tests it, for the sampled honest keys |
| 9 | `tacenta-core/tests/identity_boundary.rs:465` `the_inventory_validator_and_the_session_rule_agree` (random half) | `validate_identity_key` against `is_valid_identity_key` | yes yes yes (check 6, by section) yes yes (3,000) | identities-and-devices.md, Accepting a signed statement, check 6 | In part: two implementations agree on the verdict, with no third oracle on the random half; low-order values are almost never drawn |
| 10 | `tacenta-core/tests/identity_boundary.rs:874` `honest_identities_are_accepted_everywhere` | `Identity::from_secret`, `is_valid_identity_key`, establishment, import, signing | yes yes no yes yes (2,304 secrets, 24 sessions) | identities-and-devices.md, Accepting a signed statement, check 6 (the honest-key sentence) and The identity key's secret | Tests it, over unclamped secrets, through each place the rule applies |
| 11 | `tacenta-core/tests/import_invariants.rs:86` `an_honest_session_satisfies_the_invariant_at_every_point` | `Session::encrypt`, `decrypt`, `export`, `import` | yes yes no yes yes (1,500 rounds) | session-persistence.md, Principles (the predicate after every operation) and Session, Semantic rules | In part: the crate's own predicate; bursts of honest messages with restarts; no loss, reordering or hostile input |
| 12 | `tacenta-core/tests/spqr_erasure_public.rs:148` `public_session_retirement_wipes_spqr_keys_before_release` | `Session::decrypt` with an allocator spy (feature `private-erasure-review`, step `rust_spqr_erasure`) | yes yes no yes yes (2,000 rounds) | key-deletion.md, During a session, the other two ratchets ("A sparse-ratchet skipped key \| its message arrives, its epoch is retired, or it is evicted to make room") | In part, and mostly an implementation property: freed allocations holding exported sparse keys; keys derived during the call and copies not freed are not tracked. `limitations.md` LIM-11 and REQ-FS-03 describe a narrower test position |
| 13 | `tacenta-core/tests/rng_fill_counts.rs:231` `the_totality_laws_hold_on_sampled_inputs` | `dh`, `aead`, `kem`, `xeddsa` boundary functions | yes yes no yes yes | session-establishment.md, ML-KEM-1024 (FIPS 203), Decapsulation (a ciphertext of any length but 1,568 bytes is refused) | In part: that refusal is tested; the totality assertions state contracts the proofs assume, which no page states |
| 13b | `tacenta-core/tests/rng_fill_counts.rs:157` `kem_encapsulate_refuses_before_reading_and_otherwise_fills_32_bytes` | `kem::encapsulate` | yes yes no yes yes (50 keys) | session-establishment.md, ML-KEM-1024 (FIPS 203), Validating the encapsulation key, and the 32 random bytes encapsulation draws | Tests it |
| 14 | `tacenta-core/kdf/tests/differential.rs:96` `hkdf_fixed_width_agrees` | `hkdf_sha256` against the RustCrypto `hkdf` crate | yes no no (RFC 5869 in the file header only) yes yes (200) | session-establishment.md, Primitives, and what is left to them ("HKDF is RFC 5869's") | In part: agreement with a reference crate on generated inputs, not the page's compositions |
| 15 | `tacenta-core/src/groups/inventory.rs:1266` `keys_the_crate_generates_are_never_refused` | `validate_identity_key` on generated keys | yes yes yes (check 6) yes (key printed; the generator is not seeded) yes (1,536) | identities-and-devices.md, Accepting a signed statement, check 6 (the honest-key sentence) | Tests it; a failure is replayed from the printed key, not from a seed |
| 16 | `tacenta-core/tests/fuzz.rs:91` `persisted_decoders_never_panic` | `PrekeyStore::from_bytes`, `Session::import` | yes yes no yes yes (`PROPTEST_CASES`) | none | Does not test a sentence: a totality check; random bytes rarely pass the version byte |
| 17 | `tacenta-core/tests/fuzz.rs:108` `prekey_store_accepted_mutations_reencode_identically` | `PrekeyStore::from_bytes`/`to_bytes` | yes yes no yes yes (`PROPTEST_CASES`) | session-persistence.md, Principles, "Canonical and length-prefixed" | In part, and not its canonical clause: since the change that added this index it checks single-bit changes of one fixed store, guarded to the version the fixture's writer emits; `mutations_are_accepted_at_the_current_version` (`tacenta-core/tests/fuzz.rs:250`) shows the assertion is reached. Mutation FC1 (section 5: the decoder's canonical re-encoding check removed) survives it, because no single-bit change of the fixture is a second spelling that the other checks accept; the clause is tested by `a_stored_blocked_list_is_accepted_only_in_its_canonical_spelling` (section 3). Before that change its guard read v4 while the store is written as v5, so the assertion was reached only by a change that relabelled the store v4: the test was vacuous until that change, and no hosted run of its repair is recorded |
| 18 | `tacenta-core/tests/fuzz.rs:126` `session_accepted_mutations_reencode_identically` | `Session::import`/`export` | yes yes no yes yes (`PROPTEST_CASES`) | session-persistence.md, Session, Semantic rules (re-encoded to check that the input is canonical) | In part: single-bit changes of one fixed snapshot; `mutations_are_accepted_at_the_current_version` shows that some are accepted, so the assertion is reached |
| 19 | `tacenta-core/tests/fuzz.rs:143` `decoders_never_panic` | `decode_message`, `decode_initial`, `message_type` | yes yes no yes yes (`PROPTEST_CASES`) | none | Does not test a sentence: a totality check |
| 20 | `tacenta-core/tests/fuzz.rs:153` `message_round_trips` | `encode_message`, `decode_message` | yes yes no yes yes (`PROPTEST_CASES`) | message-format.md, Ratchet message (the layout; "The ratchet-message decoder places no constraint on the ciphertext's length or contents") | In part: `ag_type` is only `None` or `Ek`; the crate's encoder and decoder are compared with each other. Section 3 checks the layout against the page |
| 21 | `tacenta-core/tests/fuzz.rs:192` `a_respelled_ratchet_key_never_decodes` | `decode_message` | yes yes no yes yes (`PROPTEST_CASES`) | message-format.md, Curve public keys ("That refuses both other spellings, a key whose bit 255 is set and a key whose value with bit 255 clear is at least p") | In part: only the bit-255 spelling is drawn. Section 3 draws both |
| 22 | `tacenta-core/tests/fuzz.rs:214` `a_truncated_message_is_refused_below_the_header_and_keeps_it_above` (named `truncation_is_rejected_cleanly` before the change that added this index) | `decode_message` | yes yes no yes yes (`PROPTEST_CASES`) | message-format.md, Ratchet message ("A decoder rejects a message shorter than its framing and header"; "places no constraint on the ciphertext's length") | Tests it since the change that added this index. Before it, the test said that no prefix decodes and asserted only that a decoded prefix's ciphertext was shorter, which every prefix satisfies: the test was vacuous until that change, and no hosted run of its repair is recorded |
| 23 | `tacenta-core/tests/fuzz.rs:235` `concat_ad_is_unambiguous` | `concat_ad` | yes yes no yes yes (`PROPTEST_CASES`) | message-format.md, Associated data (the length of `ad` recorded, so the pair parses uniquely) | In part: both sides use the same header; only `ad` varies |
| 24 | `tacenta-core/erasure/src/lib.rs:1253` `any_k_codewords_reconstruct` | `Encoder`, `Decoder` | yes no (comment only) no yes yes (`PROPTEST_CASES`) | mlkem-braid.md, The erasure code, Decoding ("The value is the `k` chunks in order, truncated to `n` bytes") | In part: indices stay small; the first-codeword rule is not drawn; encoder and decoder share the field code. Section 3 adds high indices, repeats and the page's formulas |
| 25 | `tacenta-core/erasure/src/lib.rs:1274` `a_decoder_short_by_one_reconstructs_nothing` | `Decoder` | yes no (name only) no yes yes (`PROPTEST_CASES`) | mlkem-braid.md, The erasure code, Decoding (stated for `k` codewords; the case below `k` is implied, not stated) | In part: only the first `k - 1` systematic codewords are fed |
| 26 | `tacenta-core/tests/message_size_preflight.rs:300` `nested_len_matches_the_reference` | `serialization::nested_ratchet_len` | yes yes (module header: each value function "is compared with a reference computed in `u128`") yes (module header: message-format.md, Message size, for every test in the file) yes yes (`PROPTEST_CASES`; 4,096 in the file when it is unset) | message-format.md, Message size (the nested ratchet message of an initial frame) | In part: the arithmetic on length values, against a `u128` restatement written in the test, over the whole `usize` and `u32` ranges; no real frame is read |
| 27 | `tacenta-core/tests/message_size_preflight.rs:305` `too_long_matches_the_reference` | `serialization::frame_too_long` | yes yes (module header) yes (module header) yes yes (`PROPTEST_CASES`; 4,096 unset) | message-format.md, Message size (`MAX_RATCHET_FRAME_LEN`, `MAX_INITIAL_FRAME_LEN`, the two frame kinds) | In part: as 26; draws are uniform over `usize`, so the bounds are reached only by 28 |
| 28 | `tacenta-core/tests/message_size_preflight.rs:314` `too_long_matches_the_reference_near_the_bounds` | `serialization::frame_too_long` | yes yes (module header) yes (module header) yes yes (`PROPTEST_CASES`; 4,096 unset) | message-format.md, Message size | In part: lengths within 4,000 bytes of the two bounds and KEM lengths below 4,000, against the same restatement |
| 29 | `tacenta-core/tests/message_size_preflight.rs:325` `the_byte_functions_read_what_the_value_functions_take` | `serialization::ratchet_span`, `check_frame_size` | yes yes (doc comment) yes (module header) yes yes (`PROPTEST_CASES`; 4,096 unset) | message-format.md, Message size | In part: frames under 120 bytes, so no frame is long enough to be refused; it compares the crate's byte functions with its value functions, not with the page |

Read and not counted, with the reason: `tacenta-core/braid/src/tests.rs:604`
(one fixed send/receive schedule; only the key material is random);
`tacenta-core/tests/restored_initiator_receives_reply.rs:29` (one scenario under
twenty seeds); `tacenta-core/tests/session_lifecycle_property.rs` (one trace);
`tacenta-core/tests/identity_expectation.rs:805` and `:882` (a wrapper-against-leaf
comparison over eight generated bundles beside a crafted table, and an
enumerated sweep); `tacenta-core/tests/canonicality.rs` and
`tacenta-core/tests/import_boundary.rs:59` (deterministic sweeps);
`tacenta-core/tests/failed_decrypt_changes_nothing.rs` (one forgery repeated);
`tacenta-core/kem/tests/malformed_stored_state.rs` (case tables, and three tests
that assert nothing); `tacenta-core/wire/src/lib.rs:1135` (every single-bit
change of one header: an enumerated sweep, which may be strong but has no
generator); `tacenta-core/tests/message_size.rs` and
`tacenta-core/tests/message_size_alloc.rs` (scenario and edge tests; their
seeded sources supply key material and count draws, not inputs the properties
quantify over); `tacenta-core/tests/fuzz_frame_size_seeds.rs` (a check of the
committed fuzz seeds); `tacenta-test-vectors/runners/rust/tests/operation_trace_supplement.rs`
(committed traces; its splitmix stream is a fixture source); the fuzz targets
under `tacenta-core/fuzz/fuzz_targets/`, which the hosted workflow does not run.

**The differential harness**, `the_model_and_the_core_agree_on_generated_sequences`
(`tacenta-test-vectors/runners/rust/tests/differential.rs:5143`), model-dependent,
by check:

| Check | Generated? | What it compares with the model | Sentence it is mapped to |
|---|---|---|---|
| `check_ratchet` (`:854`) | yes | each step's outcome, the persisted bytes (also after a refusal), the read-back, the counter ceiling | ratchet.md, Sending and receiving, Skipped keys; session-persistence.md, Ratchet state |
| `check_sparse` (`:1123`) | yes | outcome, bytes, read-back, the replacement bound at the cap, retirement, the ceilings | sparse-pq-ratchet.md, Receiving, Retiring old epochs; session-persistence.md, Sparse ratchet state |
| `check_triple` (`:2115`) | yes | outcome, bytes, read-back, the ceiling of either half | triple-ratchet.md, Sending and receiving; session-persistence.md, Triple ratchet state |
| `check_braid` (`:2897`) | at the ceiling only | outcome and bytes of steps at the reserved epoch | mlkem-braid.md, Failure (the reserved epoch); session-persistence.md, Braid |
| `check_composed` (`:2984`) | yes | Triple sequences, and Braid stored states per tag with generated corruptions, through both readers | session-persistence.md, Braid, Rejection |
| `check_imports` (`:5591`) | yes | generated corruptions of ratchet and sparse states: equal bytes, agreeing refusal kinds | session-persistence.md, Rejection |
| `check_identity_keys` (`:4971`) | yes | the identity-key verdict on 1,600 generated keys | identities-and-devices.md, Accepting a signed statement, check 6 |
| `check_prekey_imports` (`:3372`), `check_session_imports` (`:4873`) | no: committed vectors | read-back and refusal kinds | not counted as property tests |
| `check_prekey_lifecycle` (`:3498`), `check_initial_session_establishment` (`:4170`), `check_established_message_effects` (`:4305`) | no: one scenario each | persisted effects of operations | not counted as property tests |

## 3. Property tests added with this index

Each cites its sentence in its own doc comment, so element 3 is met in the test
itself. All are run by the hosted `rust` job, except the protobuf file, which is
in the conformance runner because that is the one test target outside the
translated crate that links `tacenta-protobuf`, and is run by the hosted
`vectors` job. No hosted run of them is recorded in this file. For the
`proptest` files the count is the file's `CASES` when `PROPTEST_CASES` is unset
and `PROPTEST_CASES` otherwise (proptest reads the variable over the file's
configuration); the hosted `rust` job and `tooling/ci.sh` set it to 2,048.

| File | Tests | Subject | Generator, replay, count | Sentences tested |
|---|---|---|---|---|
| `tacenta-core/tests/pqxdh_properties.rs` | `kdf_sk_is_the_pages_kdf` (`:117`), `the_secret_is_kdf_of_the_outputs_in_the_pages_order` (`:131`), `the_encodings_have_the_pages_layout` (`:163`), `the_associated_data_binds_both_identities` (`:192`), `decode_ec_accepts_exactly_the_canonical_encoding` (`:225`), `decode_ec_reads_only_encode_ec_forms` (`:249`), `no_honest_key_is_refused` (`:291`); unit test `the_boundary_values_are_on_the_sides_the_page_says` (`:311`) | all nine public functions of `tacenta-session` | `proptest`; 1,024 cases locally, 2,048 in the hosted `rust` job; proptest replay | session-establishment.md, Notation (`KDF(KM)`); Parameters (`EncodeEC`, `EncodeKEM`); Sending the initial message (`SK`, `AD`, "`EncodeEC` must be fixed-width", "`DecodeEC` accepts exactly one encoding of each key", "no honest key is refused"). Oracles: the RustCrypto `hkdf` crate fed the page's inputs, the page's layouts, a byte comparison with p. `associated_data_with_kem` is checked as written, but the page says this implementation does not append the KEM prekey, so that check covers an unused helper and not the associated data a session uses |
| `tacenta-core/tests/wire_codec_properties.rs` | `the_composite_header_has_the_pages_layout_and_round_trips` (`:190`), `the_composite_decoder_accepts_exactly_the_pages_headers` (`:245`), `the_bundle_has_the_pages_layout_and_round_trips` (`:294`), `a_flipped_bundle_decodes_only_as_its_one_spelling` (`:337`), `a_respelled_key_or_another_kem_length_is_refused` (`:373`), `a_bundle_with_trailing_or_missing_bytes_is_refused` (`:396`), `the_initial_message_round_trips_and_refuses_respelled_keys` (`:426`), `an_initial_message_is_refused_as_the_page_lists` (`:478`), `the_framing_names_the_message_type` (`:522`) | `encode_composite`, `decode_composite`, `encode_bundle`, `decode_bundle`, `encode_initial`, `decode_initial`, `message_type`, the last in its public copy and in the lifecycle's copy, which the session dispatches on | `proptest`; 512 cases locally, 2,048 in the hosted `rust` job; proptest replay | message-format.md, Principles (Canonical), Message type, Ratchet message (layout and refusals), Initial message (layout and every refusal the page lists), Prekey bundle, Curve public keys. Not tested: the standalone composite decoder's refusal of trailing bytes, which `decode_composite` leaves to its caller; the lifecycle's own copies of `encode_message`, `concat_ad` and `encode_initial`, which the session uses (`tacenta-core/lifecycle/src/serialization/mod.rs`), as distinct from the public copies in `tacenta-core/src/serialization/mod.rs` that these properties call |
| `tacenta-test-vectors/runners/rust/tests/protobuf_properties.rs` | `varints_are_the_pages_and_only_the_minimal_spelling_reads` (`:154`), `ratchet_bodies_parse_in_any_order_and_refuse_what_the_page_refuses` (`:227`), `prekey_envelopes_parse_in_any_order_and_refuse_what_the_page_refuses` (`:297`); unit test `the_outer_bound_is_the_pages` (`:184`) | `Reader::varint`, `encode_varint`, `parse_ratchet_body`, `parse_prekey_body`, `encode_ratchet_body`, `encode_prekey_body` | splitmix64, seed fixed in the file, 2,000 cases each; the case is named in every message | protobuf-profile.md, Bounds, Varints, Fields in a message (step 3, for every defined field of both types), Ratchet message body, Prekey envelope, Field order and canonicality. Oracle: an encoder written from the page. Not tested: tags on their own beyond the field numbers the bodies use |
| `tacenta-core/tests/erasure_properties.rs` | `the_field_is_the_pages` (`:117`), `the_encoder_issues_the_pages_codewords` (`:139`), `a_decoder_recovers_the_value_from_any_k_distinct_indices` (`:171`) | `gf::add`, `mul`, `pow`, `inv`; `Encoder::next_chunk`; `Decoder::add_chunk`, `message` | `proptest`; 256 cases locally, 2,048 in the hosted `rust` job; proptest replay | mlkem-braid.md, The erasure code: The field, Chunks, Codewords, Decoding (the first codeword at an index kept, codewords past `k` ignored, indices up to 65,535). Oracle: the page's field and Lagrange sums written here. Each encoder case compares only the last three indices it issues with the formula |
| `tacenta-core/tests/braid_properties.rs` | `honest_schedules_agree_on_every_epoch_key` (`:63`) | `Braid::send`, `receive`, `commit`, `invariant`, `epoch`, `failed`, `to_bytes` | `StdRng` seeded per run, 16 runs of 2,000 steps (each run ends at epoch 4 or 5); run and step in every message | mlkem-braid.md, The shape, in one paragraph ("each epoch yields one shared secret") with Parameters and derivations, The epoch key ("The epoch's key is `KDF_OK(K, e)`"), so both sides' keys for an epoch are equal; When an epoch completes ("Each epoch's key is output once on each side, labelled with that epoch"); What a send and a receive return ("A send never raises the epoch"); Failure (none of its causes is reached by an honest schedule); What a receive ignores (a message stamped with another epoch leaves the state unchanged; the type-based rules are not asserted). Generated delivery order, repeats and loss of honest messages; no forged message |
| `tacenta-core/tests/identity_records_properties.rs` | `the_digest_is_the_pages_hash_of_the_sorted_pair` (`:178`), `the_digest_refuses_exactly_what_the_rule_refuses` (`:207`), `the_number_is_the_digest_mod_ten_to_the_sixty` (`:231`), `classification_is_the_pages` (`:265`), `the_lookup_is_the_classification_against_every_record` (`:292`) | `identity_pair_digest`, `verification_number`, `verification_number_grouped`, `classify`, `lookup` | `proptest`; 512 cases locally, 2,048 in the hosted `rust` job; proptest replay | identities-and-devices.md, The identity pair digest, The verification number; session-establishment.md, Records, expectations and attribution (Classification, Lookup). The identity-key rule inside them is taken from `is_valid_identity_key`, not tested here |
| `tacenta-core/tests/identity_establishment_properties.rs` | `the_initiator_refuses_exactly_as_the_expectation_says` (`:194`), `the_responders_first_plaintext_is_attributed_as_its_session` (`:263`) | `establish_initiator` under both expectations, `establish_responder_unattributed`, `Unattributed::attribute` | `StdRng` seeded per run: 24 runs by 40 record sets under *first contact*, and under *known* when the set holds a record (about four in five); 96 responder establishments; run and set in every message | session-establishment.md, Records, expectations and attribution (The initiator; Lookup; Attribution; "Nothing is verified, drawn, computed or sent for it"). Both tests use a lookup written in the file from the page, not the crate's |
| `tacenta-core/tests/prekey_store_properties.rs` | `create_prekeys_numbers_the_store_as_the_page_says` (`:46`), `identifiers_never_repeat_and_used_prekeys_are_gone` (`:148`), `a_retired_prekey_is_honoured_for_exactly_one_rotation` (`:296`), `a_stored_blocked_list_is_accepted_only_in_its_canonical_spelling` (`:370`) | `create_prekeys`, `replenish`, `rotate_signed_prekey`, `rotate_kem`, `publish_one_time_batch`, `publish_multi_use`, consumption by `establish_responder`; `PrekeyStore::from_bytes`/`to_bytes` on the `legacy_blocked` list | `StdRng` seeded per case, seeds fixed in the file: 48 store sizes drawn from 0 to 40; 12 runs of 24 drawn operations; 24 runs of 8 drawn steps (a rotation of a drawn kind or a replenishment), each checking an initial message from a drawn earlier bundle against the number of rotations of each kind since it was published; 256 drawn lists of zero to three entries. Each property also asserts that its draws are not vacuous (enough sizes, both outcomes, repeated identifiers drawn) | key-deletion.md, What this implementation does ("identifiers never repeat", the numbering of `create_prekeys`, `replenish`'s curve prekeys numbered before its KEM prekeys, a one-time prekey deleted on use, "A replayed last-resort handshake is refused", "Signed prekeys rotate, and the retired one is kept for exactly one rotation", "`rotate_kem` does the same"); Establishing a session (nothing deleted for a message that fails to decrypt); session-establishment.md, Receiving the initial message ("A refused initial message changes nothing"); session-persistence.md, Legacy markers (the canonical list, and a list that is not strictly ascending refused) and Principles (Canonical). The list property draws only fresh stores, so `previous_kem` is absent and the last-resort identifier is the one entry a list may name |
| `tacenta-core/tests/fuzz.rs` | `mutations_are_accepted_at_the_current_version` (`:250`) | `PrekeyStore::from_bytes`, `Session::import` | a deterministic stride over single-bit changes of the two fixtures | not a property test: it shows that properties 17 and 18 reach their assertion |

## 4. By component row of `ASSURANCE.md`

"Reached" means every operation whose behaviour a page states is the subject of
at least one test in sections 2 or 3 that has the five elements and whose
assertions test, at least in part, the sentence it is mapped to. It never means
complete coverage: what the tests do not check is in the missing-coverage
column, and evidence that rests on the differential harness is labelled
model-dependent. "Not shown until `PT-...` meets its acceptance" means the
register row's conditions: a recorded successful hosted run on `main` naming the
commit, the run id, the jobs, the effective case counts and the results, and
then the row's other conditions; such a run alone does not close it. Accessors, counters and helpers no page
states are not counted either way. The targets are those of `ASSURANCE.md` and
are not changed here.

| Row (level now / target) | Property-test evidence | Missing coverage | Before the tests of section 3 | After them |
|---|---|---|---|---|
| Wire decoders (L4 / L4) | 17-23, 26-29; section 3, wire file | `encode_header` (no page states it); the trailing-byte refusal of the standalone composite decoder; the lifecycle's copies of `encode_message`, `concat_ad` and `encode_initial`, which the session uses; the size rule on real frames near the bounds (26 to 29 reach the bounds on length values only) | not reached: the bundle codec, the composite header on its own, the initial message and `message_type` had no property test in the five-element sense (test 19 checks only that `decode_initial` and `message_type` return, with no cited sentence; the fuzz target `fuzz_targets/wire_decoders.rs` reaches all four and asserts canonical re-encoding of what the bundle and composite decoders accept, but it is fuzzing and the hosted workflow does not run it), and test 22 was vacuous (it asserted nothing a prefix could fail; its repair has no hosted run) | reached in part by section 3; not shown until `GAP-REGISTER.md` `PT-WIRE` meets its acceptance |
| Double Ratchet (L4 / L4) | 2; differential `check_ratchet`, `check_imports` (model-dependent) | the receive rules over generated input rest on the model-dependent harness; test 2 asserts the crate's own predicate | reached in part through this index, the receive rules by model-dependent evidence only | the same |
| Sparse post-quantum ratchet (L4 / L4) | 1, 3; differential `check_sparse` (model-dependent) | epoch openings past the current one | reached in part (test 1 cites its page) | the same |
| Triple Ratchet (L4 / L4) | 4; differential `check_triple` (model-dependent) | the role clause after the start; `split_secret` and `combine` only through send and receive, and against the model | reached in part through this index, the receive rules by model-dependent evidence only | the same |
| ML-KEM Braid (L3 / L4) | section 3, Braid file; differential `check_braid`, `check_composed` (model-dependent, ceilings and stored states) | forged or altered messages; the type-based ignoring rules; persistence across a generated schedule | not reached: the one walk is a fixed schedule | reached in part by section 3; not shown until `PT-BRAID` meets its acceptance; the row stays below its L4 target for the reason `ASSURANCE-OBLIGATIONS.md` gives |
| Erasure code (L3 / L3) | 5, 24, 25; section 3, erasure file | the 65,536 cap and exhaustion | reached in part through this index | reached in part, with section 3 |
| Protobuf profile (L4 / L4) | section 3, protobuf file | tags beyond the bodies' field numbers | not reached: test 7 states no property, cites no sentence and asserts nothing; the fuzz target `fuzz_targets/protobuf_bodies.rs` feeds generated bytes to both body parsers and checks only that they return, and the hosted workflow does not run it; nothing generated reached the encoders | reached in part by section 3; not shown until `PT-PROTOBUF` meets its acceptance |
| PQXDH derivation (L4 / L4) | section 3, PQXDH file | each of the nine functions has a property test; what is not tested: the KEM-prekey associated data, checked only as an unused helper | not reached: no generated-input test had its functions as subject (the fuzz target `session_receive` and the differential harness reach them only through establishment) | reached in part by section 3; not shown until `PT-PQXDH` meets its acceptance |
| Session orchestration and prekey store (L2 / L2) | 10, 11, 16-18; section 3, identity-record, establishment and prekey-store files | refusals of `encrypt` and `decrypt` over generated forged input (scenario tests only); `establish_responder`'s refusals other than an altered authentication tag; reordered or lost delivery at the session level; the size refusals at the three entries over generated lengths (`tests/message_size.rs` tests them at chosen lengths) | not reached: the eight identity-record functions and the prekey operations had none | reached in part by section 3; for the prekey operations not shown until `PT-SESSION` meets its acceptance; for the eight identity-record functions `GAP-REGISTER.md`'s `SESSION-IDENTITY-L2-SHORTFALL` asks more than the five elements (its floor: each property stated in that row before its test lands, results compared with the model, 2,048 cases from a varying or proptest seed on each hosted run, retained failing inputs), which the identity-record and establishment files do not meet: their oracles are written from the pages, not the model, no property was stated in that row first, and the establishment file's seeds are fixed and its counts below 2,048; the row stays short of L2 for those functions for the reasons `ASSURANCE.md` gives |
| Persisted formats: ratchet, sparse ratchet (L3 / L3) | 2, 3; differential `check_imports` (model-dependent) | corrupted imports outside the harness | reached in part, the import refusals by model-dependent evidence only | the same |
| Persisted formats: erasure coders (L3 / L3) | 5 | the refusal kinds of `from_bytes`; section 3's erasure file does not call `to_bytes` or `from_bytes` | reached in part through this index | the same |
| Persisted formats: triple ratchet, Braid (L2 / L2) | 4; differential `check_composed` (model-dependent) | the Braid's round trip over a generated schedule | reached in part, the Braid half by model-dependent evidence only | the same |
| Persisted formats: prekey store (L2 / L2) | 17 (not its canonical clause); section 3, prekey-store file, the list property | changes of more than one bit to other fields; the list property draws only stores with no previous prekeys | not reached: test 17 was vacuous (it reached its assertion only for a v4 relabelling; its repair has no hosted run) | reached in part (single-bit changes of one store); not shown until `PT-SESSION` meets its acceptance |
| Persisted formats: session (L2 / L2) | 11, 18 | changes of more than one bit | reached in part | the same |

`tacenta-kdf`, `tacenta-kem` and `tacenta-boundary` have no row in the table;
tests 8 and 13 to 14 test them.

## 5. Mutation record

Each row is one change to the code under test, made in the working tree, followed
by the named test files (`cargo test --locked --test <file>`, one at a time, with
`PROPTEST_CASES` unset) and then a restore; none of the changes was committed.
"Caught" means that file failed. A `proptest` file draws fresh inputs on each
run, so a catch is one run's result, not a guarantee. First run on 2026-11-08 on
an earlier `main` (`8f8e02f6`); every row was run again on 2026-11-12 at the tree
that contains this file, by the same script, with the result shown for each. RD1
to RD9 are the changes of the first read of this index; the others were made when
the tests were written. After a second read, the prekey-store file was rewritten and
the lifecycle's `message_type` added to the wire file; RD4, RD5, QN1, QN2 and FC1
were run again against them and RT1, RT2 and ML1 added, on 2026-11-12.

| # | Code under test | Change | Files run: result |
|---|---|---|---|
| RD1 | `wire/src/lib.rs`, `decode_initial` | type `0x03` accepted as well as `0x02` | `wire_codec_properties`: caught; `fuzz`: survived |
| RD2 | `wire/src/lib.rs`, `decode_initial` | a `kem_ciphertext_len` past the end read as an empty ciphertext | `wire_codec_properties`: caught; `fuzz`: survived |
| RD3 | `wire/src/lib.rs`, `decode_message` | a ciphertext of 1 to 15 bytes refused | `fuzz`: caught; `wire_codec_properties`: survived |
| RD4 | `lifecycle/src/lifecycle.rs`, `replenish` | the curve prekeys numbered after the KEM prekeys | `prekey_store_properties`: caught (also after the rewrite of section 3's prekey-store file) |
| RD5 | `lifecycle/src/lifecycle.rs`, `establish_responder` | the one-time curve prekey deleted before the message authenticates | `prekey_store_properties`: caught; `identity_establishment_properties`: survived |
| RD6 | `src/sessions/identity.rs`, first-contact expectation | *retired* checked before *same* | `identity_establishment_properties`: caught |
| RD7 | `src/sessions/identity.rs`, `lookup` | ambiguous only when *same* for more than two records | `identity_records_properties`: caught; `identity_establishment_properties`: caught |
| RD8 | `protobuf/src/lib.rs`, envelope field 5 | the length-delimited form accepted and read as 0 | `protobuf_properties`: caught |
| RD9 | `session/src/lib.rs`, `decode_ec` | 33 or 34 bytes accepted | `pqxdh_properties`: caught |
| PQ1 | `session/src/lib.rs` | `F` of `0xFE` bytes | `pqxdh_properties`: caught |
| PQ2 | `session/src/lib.rs`, `km` | `DH2` and `DH3` swapped | `pqxdh_properties`: caught |
| PQ3 | `session/src/lib.rs`, `is_canonical_x25519` | bit 255 tested as `> 0x80` | `pqxdh_properties`: caught |
| PQ4 | `session/src/lib.rs`, `is_canonical_x25519` | p itself accepted (`> 0xed`) | `pqxdh_properties`: caught |
| PQ5 | `session/src/lib.rs`, `decode_ec` | any type byte from `0x05` up accepted | `pqxdh_properties`: caught |
| W1 | `wire/src/lib.rs`, bundle | non-zero padding behind an absent one-time prekey accepted | `wire_codec_properties`: caught |
| W2 | `wire/src/lib.rs`, bundle | a KEM prekey length below 1,568 accepted | `wire_codec_properties`: caught |
| W3 | `wire/src/lib.rs`, bundle | the signed prekey's canonical check removed | `wire_codec_properties`: caught |
| W4 | `wire/src/lib.rs`, bundle | the identity key's canonical check removed | `wire_codec_properties`: caught |
| W5 | `wire/src/lib.rs`, composite | `dh`'s canonical check removed | `wire_codec_properties`: caught |
| W6 | `wire/src/lib.rs`, bundle | trailing bytes accepted | `wire_codec_properties`: caught |
| W7 | `wire/src/lib.rs`, composite | `ag_type` `0x06` accepted | `wire_codec_properties`: caught |
| B1 | `protobuf/src/lib.rs`, varint | the minimality check removed | `protobuf_properties`: caught |
| B2 | `protobuf/src/lib.rs`, field set | a repeated field accepted | `protobuf_properties`: caught |
| B3 | `protobuf/src/lib.rs`, `Reader::new` | a region one byte over the bound accepted | `protobuf_properties`: caught |
| EC1 | `erasure/src/lib.rs`, field | reduction by `0x1100D` | `erasure_properties`: caught |
| EC2 | `erasure/src/lib.rs`, `add_chunk` | a later codeword at a held index replaces the first | `erasure_properties`: caught |
| EC3 | `erasure/src/lib.rs`, `add_chunk` | codewords past `k` kept | `erasure_properties`: caught |
| K1 | `braid/src/lib.rs`, transition (5) | the receiver's epoch key derived with `epoch ^ 1` | `braid_properties`: caught |
| K2 | `braid/src/lib.rs`, `step_receive` | messages of earlier epochs treated as current | `braid_properties`: caught |
| ID1 | `src/sessions/identity.rs`, pair digest | the byte order reversed | `identity_records_properties`: caught |
| ID2 | `src/sessions/identity.rs`, classification | *same* checked before *retired* | `identity_records_properties`: caught |
| ID4 | `src/sessions/identity.rs`, `verification_number` | 59 digits computed | `identity_records_properties`: caught |
| ID5 | `src/sessions/identity.rs`, pair digest | the second key's refusal skipped | `identity_records_properties`: caught |
| ID6 | `src/sessions/identity.rs`, `Record::is_malformed` | the retired set not checked | `identity_records_properties`: caught |
| AT1 | `src/sessions/identity.rs`, `Unattributed::attribute` | released beside a lookup in no records | `identity_establishment_properties`: caught |
| QN1 | `lifecycle/src/lifecycle.rs`, `replenish` | a KEM prekey takes the previous identifier | `prekey_store_properties`: caught |
| QN2 | `lifecycle/src/lifecycle.rs`, `replenish` | a curve prekey reuses an earlier identifier | `prekey_store_properties`: caught |
| FC1 | `lifecycle/src/lifecycle.rs`, `PrekeyStore::from_bytes` | the re-encode canonicality check removed | `fuzz`: survived (property 17's single-bit changes never reach that check); `prekey_store_properties`: caught, by the list property, which draws a repeated identifier that only that check refuses |
| RT1 | `lifecycle/src/lifecycle.rs`, `rotate_signed_prekey` | the retired signed prekey dropped at once instead of kept for one rotation | `prekey_store_properties`: caught |
| RT2 | `lifecycle/src/lifecycle.rs`, `rotate_signed_prekey` | the first retired signed prekey kept for ever | `prekey_store_properties`: caught |
| ML1 | `lifecycle/src/serialization/mod.rs`, `message_type` | any version byte accepted | `wire_codec_properties`: caught; `fuzz`: survived |
