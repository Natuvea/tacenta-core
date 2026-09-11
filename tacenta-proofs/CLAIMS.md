# Claims

Exactly what is proven, each claim tied to its proof. A claim appears here only
when a machine-checked proof backs it. Runtime evidence is listed separately so
the difference between a proof and a check stays explicit.

## Read this first: what is not proved

Everything below this section is accurate. A reader who works through it can
still finish with a stronger impression than the sum of its parts supports, so
this section says in one place what is not proved.

- **`Session::encrypt` and `Session::decrypt` are not proved end to end.** They
  are the functions a product actually calls. Their orchestration -- choosing a
  path, sequencing the crates, handling the failure branches -- has no theorem.
  What is proved lies underneath them, in the ratchet, the sparse post-quantum
  ratchet, the ML-KEM braid and their composition.
- **The composed Triple Ratchet proofs rest on stated opaque cross-crate
  assumptions.** They are declared rather than hidden, and each is named where
  it is used, but a composition proved under assumptions is a different object
  from one proved outright.
- **Totality is conditional.** The T1 results carry preconditions -- counter
  bounds, room in the epoch vector, capacity in the skipped-key store. Each is a
  real assumption about how far a session can run before it must be refreshed,
  not a formality, and **nothing in the type system enforces them**. It used to
  be the sharpest form of that point that `from_bytes` let an untrusted byte
  string establish a state violating them. For three crates that is now closed:
  `tacenta-ratchet`, `tacenta-spqr` and `tacenta-braid` each end `from_bytes`
  by checking the crate's own `invariant()`, and
  `Translation/ImportInv.lean` proves that a state the translated `from_bytes`
  returns satisfies that invariant and that the invariant yields the
  preconditions -- the classical ratchet's `hs` (given one platform-width
  fact) and `hone`; the sparse ratchet's `hroom`, `hskiproom` and `hone`; the
  Braid's `ct1_bounded`. See "Proved: what a decoded state satisfies" for the
  exact statements. What is **not** closed: `T3.receive_refines`'s `hroom`,
  `SpqrT3.receive_refines`'s `hepoch`, `hcb`, `hsb`, `hnewb` and `hcounter`,
  and `BraidT3.step_receive_refines`'s `epoch + 1 < u64::MAX` are not
  consequences of those crates' invariants and are still the caller's (the
  bullet below says why the three counter bounds cannot be); `tacenta-triple`,
  `tacenta-erasure`, `tacenta-session` and `tacenta-protobuf` have no such
  theorem; and the subject throughout is a leaf crate's own persistence
  format, not the session layer above it, which is untranslated. Wherever that
  chain does not reach, the sentence in bold still stands unchanged.
- **A decoded state is panic-free unconditionally; it refines the model
  provided the relevant counter has a step of headroom left.** That is the
  one-line shape of what `Translation/ImportInv.lean` gives, and the split is
  not an artefact of how the proofs are written. Each of the three crates
  reserves the top value of the counter it steps -- the classical ratchet's
  clock clamps at `MAX_EVENTS = u32::MAX - 1`, the sparse ratchet's `advance`
  refuses the step to `epoch == u64::MAX`, the Braid's `step_receive` refuses
  the same in transitions (5) and (13) -- so that no state a crate's own
  operations produce is one its own decoder refuses. The models reserve
  nothing: they count in `Nat`. So at the last unreserved value the code stops
  and the model goes on, and the refinement theorems ask for one step of
  headroom (`events + 1 < u32::MAX`, `epoch + 1 < u64::MAX`) where they used
  to ask for the plain ceiling bound. No `invariant()` can supply that step,
  because the state at the last unreserved value is an ordinary state the
  crate produces, decodes and goes on operating on; a clause excluding it
  would refuse a state the crate exports, which is the defect the reservation
  removed. So the headroom is the caller's premise, and is named as one
  wherever it appears -- an explicit argument on
  `Ratchet.decoded_receive_refines`, and an open premise for the other two.
  The panic-freedom theorems are untouched: every `decoded_*_no_panic` in
  `ImportInv.lean` is unconditional in the counters.
- **The primitives are opaque.** X25519, ML-KEM, SHA-256, HMAC and the AEAD are
  assumed at the boundary. No proof here says anything about them.
- **Every boundary hypothesis about an opaque operation is guarded by that
  operation's own precondition, and the build checks that each `Vec`-family
  one is satisfiable.** `VecAppendTotal`/`VecAppendAgrees` carry a length
  guard (Aeneas's `Vec` has no room for two full vectors); `VecRemoveTotal`
  in both `T1.lean` and `SpqrT1.lean` and `VecRemoveAgrees` carry the index
  guard `i.val < v.val.length →`, the one condition under which Rust's
  `Vec::remove` returns rather than panics, discharged in each proof from
  the loop guard the source checks first (the guard also removed the
  `[Inhabited]` bound the unguarded statements needed: stated for every
  index and every element type, including the empty one, they would imply
  `False`); every width-polymorphic HKDF hypothesis carries RFC 5869's `N.val ≤ 8160` (`SessionT3.HkdfAgrees` is fixed at 32 bytes and needs none), the
  bound the crate's `expect` enforces; `DivCeilTotal` carries `b.val ≠ 0`;
  and the KEM's two randomness-drawing totals and clauses carry
  `BraidT1.RngTotal rc`, that the caller's `fill_bytes` returns. A hypothesis
  that implies `False` in Lean turns every theorem taking it into a proof of
  `False → _`, kernel-checked and establishing nothing; the kernel does not
  flag this, and `#print axioms` does not either. The sparse ratchet's
  `receive_no_panic` and `receive_refines`, the classical ratchet's
  `receive_refines`, and everything composed from them on the three-leaf unit
  take these hypotheses, so
  `Translation/Satisfiability.lean` exhibits a model of each `Vec`-family
  one and a refutation of each unguarded shape, and the build fails if any
  of them becomes refutable; for `Vec::remove` the model is the real
  operation's own behaviour, the element in range and a panic otherwise. The
  same file witnesses every `zeroize`-wrapper hypothesis the sparse ratchet,
  the Braid and the classical ratchet take (`ZeroizingRoundTrips96`/`64`,
  `ZeroizingArrayRoundTrip`, `T3.lean`'s `ZeroizingRoundTrips` and
  `ZeroizingRoundTrips80`, `T1.DerivedKeysModel`), jointly where one theorem
  takes two about the same wrapper (`T1.ZeroizingTotal` or
  `T3.ZeroizingRoundTrips` with `T1.DerivedKeysModel`, and the sparse ratchet's
  two round trips), and every HMAC and HKDF agreement and `OptionCloneTotal` the
  classical, sparse, session and Braid refinements take, from the model's output
  lengths and the identity clone. The session's HKDF totality and wrapper model,
  the sparse ratchet's array wipe and the erasure crate's `div_ceil` and
  `truncate` are witnessed there too, and the remaining key-derivation totalities
  follow from witnessed agreements by named theorems.
  `Translation/UnitSatisfiabilityTriple.lean`, which cannot share an
  environment with the rest, does the same for the Triple Ratchet's two
  (`UnitT1.ZeroizingTotal`, `UnitTripleT3.ZeroizingRoundTrips`) and for the
  inner refinements' boundary as restated about the unit, jointly where two
  hypotheses there constrain one constant: the `zeroize` wrapper family with
  `DerivedKeysModel`, `Vec::remove`, `append` and `retain`, `Option`'s clone and
  the general array `ZeroizeTotal`, and the HMAC and HKDF agreements. A satisfiable hypothesis is still only
  a hypothesis (`LIMITATIONS.md`).
- **The ML-KEM Braid's T3 theorems carry two preconditions beyond the
  boundary agreements.** `step_send_refines`, `Braid.send_refines`,
  `step_receive_refines` and `Braid.receive_refines` take a live encoder
  (fewer than 65,536 codewords emitted) and an unspliced chunk stream
  (`HonestChunk`), and the erasure agreement they rest on is bounded to what
  a real erasure code can satisfy, as is the KEM agreement, since the
  revision the next bullet describes. The section below
  records every hypothesis; `Translation/Satisfiability.lean` refutes the
  unbounded shapes so they cannot be restated, and
  `Translation/ErasureWitness.lean` proves the erasure hypotheses have a
  model (a Reed-Solomon code over `GF(2^256)`, built from Mathlib).
- **The KEM agreement binds the model's randomness existentially per RNG
  state, for encapsulation as for key generation.** `Model.Braid.Kem.encaps1`
  takes a randomness argument, `Kem.Correct` quantifies over both parties'
  randomness, and the encapsulation clause of `BraidT3.lean`'s `KemAgreesFor`
  says that for each RNG state *some* model randomness makes `K.encaps1`'s
  ciphertext and shared secret the real `encapsulate1`'s -- the same shape
  the key-generation clause always had. An earlier revision's clause fixed
  one pair per header for every RNG state, which ML-KEM's fresh randomness
  makes false of the real operation, so the four Braid refinement theorems
  described a Braid over a derandomised KEM; `LIMITATIONS.md`'s KEM entry
  (under the Braid's erasure and KEM hypotheses) records that this was so
  and is closed. What the two randomness-drawing clauses assume beyond
  agreement is `BraidT1.RngTotal rc`, that the caller's `fill_bytes`
  returns; `step_send_refines` and `Braid.send_refines` take it.
- **A verified zone is not a verified library.** The zone is the ratchet and
  what it calls; orchestration, storage and lifecycle sit outside it.
- **The verified protobuf parser has no caller.** `tacenta-protobuf` carries
  T1 and T3 below, and nothing on the live path calls it: outside its own
  directory it is referenced only by a fuzz target. The bytes a peer sends are
  parsed by `decode_message` and `decode_composite`, for a ratchet message, and
  `decode_initial`, for a prekey message, and a fetched prekey bundle by
  `decode_bundle`; all four live in the `tacenta-wire` leaf crate and are proved
  below (T1 and T3). So received bytes are parsed by proved code for both kinds
  of message and for a bundle; what the session does with them afterwards is
  not translated.
- **Which private key is agreed with which public key at a Diffie-Hellman
  ratchet step is decided outside every proof and every vector.** The
  specification's rule -- the old key pair for the receiving chain, the fresh
  one for the sending chain -- is applied in `tacenta-core/src/sessions`,
  which is neither translated nor modelled. `Model.Ratchet.receive`, the
  refinement theorem and the ratchet vectors all take the two agreement
  outputs as opaque bytes, so a swap in the orchestration would pass every
  proof, every vector and `attest`. By inspection the code pairs them
  correctly; a session-level test that drives `Session` against a model
  scenario is being added so that this is checked by running rather than by
  reading.
- **Translated is not proved.** Every verified-zone crate carries
  persistence codecs and a few accessors that the translation contains and
  no T1 or T3 theorem names: `from_bytes`, `to_bytes`
  and their helpers (`take_len_prefixed`, `decode_state`, `read_auth`,
  `read_key`, `read_u32`, `read_u64`, `decode_skipped_entry`,
  `decode_chain`, `decode_chains_entry`), `init`,
  `init_alice`, `init_bob`, `Output::new`, `Encoder::new`, `Decoder::new`,
  `needed`, `received`, `encode_prekey_body`, the small accessors, and the
  `evict_oldest` calls. (The erasure crate's `weights`, `coefficients` and
  `evaluate` *are* proved:
  `ErasureT1.lean` carries a totality theorem for each and the two entry
  points that call them are re-stepped; and the classical ratchet's
  `message_keys`, the last derivation before the cipher, *is* proved, by
  `message_keys_refines` in `Translation/T3.lean`.) Any sentence below that says "every
  function" or "complete" for a crate is about the protocol functions, not
  these; the codecs in particular parse bytes from storage and are the next
  T1 target. Since `Translation/ImportInv.lean` the three `from_bytes` in
  `tacenta-ratchet`, `tacenta-spqr` and `tacenta-braid` are no longer
  theorem-free -- they have the constructor theorem described in "Proved: what
  a decoded state satisfies", which says what a state they return satisfies.
  That is not a T1 theorem: it says nothing about whether they can panic, only
  what is true of a state when they do return one. Three crates' codecs are
  the exception. `Translation/RatchetCodecT1.lean` proves `tacenta-ratchet`'s
  `from_bytes` and `to_bytes` panic-free, with `read_key`, `read_u32`,
  `read_optional_key` and `decode_skipped_entry`, and
  `Translation/SpqrCodecT1.lean` does the same for `tacenta-spqr`'s, with
  `decode_chain`, `decode_chains_entry` and `decode_skipped_entry`, and
  `Translation/ErasureCodecT1.lean` for `tacenta-erasure`'s `Encoder` and
  `Decoder` (see the three "persistence codec" sections). Every other codec
  named above still has no T1 theorem.
  `LIMITATIONS.md` says the same where each crate is discussed.
- **T3 carries a third hypothesis besides the two it names.** Besides "modulo
  KDF agreement" and "excluding where `u32` and `Nat` part company", every
  `receive_refines` (classical, sparse, triple) assumes the skipped store
  holds at most one entry matching the header (`hone`). It is proved
  preserved at the model level (`Proofs/StateInvariants.lean`), so it is
  benign, but it is a hypothesis.
- **The Braid's T3 assumes more agreements than its section leads with.**
  `KemCloneAgrees` and `ErasureCloneAgrees` in `BraidT3.lean` are hypotheses of
  `Braid.receive_refines` and `State.clone_refines`, in the same trust category
  as `ErasureAgrees`. `Braid.receive_refines` also
  takes `BraidHmacAgrees`, `BraidHkdfAgrees`, fourteen `Tacenta.BraidT1.*`
  constants (`Encapsulate2Total`, `DecoderAddChunkTotal`, `DecoderMessageTotal`,
  `Ct1LenTotal`, `Ct2LenTotal`, `HeaderLenTotal`, `EncoderCloneTotal`,
  `DecoderCloneTotal`, `KeyPairCloneTotal`, `EncapsStateCloneTotal`,
  `OptionCloneTotal`, and since CR-15 `ZeroizingArrayRoundTrip`,
  `ArrayZeroizeTotal` and `RangeFullIndexTotal`), and two preconditions:
  `State.ct1_bounded self.state`, which the T1 section names, and
  `epoch + 1 < U64.max`, which the T1 theorems no longer need (CR-03) and the
  T3 section says why the refinement still does. `Braid.send_refines` and
  `step_send_refines` take `BraidT1.RngTotal rc` for the RNG they are
  handed, as `Braid.send_no_panic`/`step_send_no_panic` do. The theorem's
  signature is the authoritative list.

The honest one-line summary: **the protocol core is proved to refine a model
under stated assumptions; the code path a customer's message actually travels
is not proved as a whole.** `LIMITATIONS.md` gives the detail behind each point
above.

## Proved (tier T2, functional properties of the model)

Location: `Proofs/RatchetCorrectness.lean`. Kernel-checked; each of the five
theorems rests only on `propext` and `Quot.sound`, pinned under `#guard_msgs`
in `Proofs/TrustedBase.lean`, so the build fails if one starts resting on
`native_decide`'s compiler trust or on anything else.

- `deriveChain_length`: deriving a chain of `c` steps stores exactly `c` message
  keys. The memory-bound invariant behind `MAX_SKIP`.
- `deriveChain_fst`: the chain key after `c` steps is the chain advanced `c`
  times, independent of the starting message number.
- `deriveChain_get`: the `i`-th stored key is the key of the chain advanced `i`
  steps, at number `start + i`. A skipped key equals the key an in-order receive
  derives, so out-of-order delivery recovers the right message.
- `skipMessageKeys_growth`: a successful skip advances `nr` to `upto` and grows
  the stored-key list by exactly `upto - nr`. It succeeds only within `maxSkip`
  on the chain and within `maxSkippedStore` in total.
- `skipMessageKeys_store_bounded`: any state a skip returns holds at most
  `maxSkippedStore` keys, given a state already within the bound. This is the
  memory-safety invariant: a per-chain bound alone does not bound the store,
  because every Diffie-Hellman ratchet step starts a fresh chain, so a peer that
  repeatedly ratchets and skips would otherwise grow it without limit.

## Proved (tier T3, the classical Double Ratchet refines the model)

Location: `Translation/T3.lean`, against `Model.Ratchet` and `Model.State` in
`tacenta-model`. This is the central refinement of the project, and until
this section existed it had no ledger entry and no pin, so nothing in it was
checked by `attest.py`; it is now, and the three headline theorems are
pinned under `#guard_msgs` at the end of the file.

Every theorem takes a state relation `StateR s m` (the translated state
refines the model state field by field, with the fixed-width arrays, `u32`
counters and `Vec` of records absorbed there) and says the translated
operation carries it to the model's operation.

- `send_refines`: a successful `send` returns a header and a message key that
  `Model.Ratchet.send` also returns, with the new state still related, and
  the `NoSendingChain` refusal is exactly the model's `none`. The `u32`
  counter wrapping (`ChainExhausted`) has no model counterpart and is left
  out of the correspondence deliberately. **Modulo `HmacAgrees`**; pinned
  base `propext`, `Classical.choice`, `Quot.sound` and the opaque
  `tacenta_kdf.hmac_sha256`.
- `receive_refines`: a successful `receive`, given the two agreement outputs
  and the fresh ratchet key as bytes, returns the key `Model.Ratchet.receive`
  returns and a state still related, across the skipped-key hit, the
  same-chain path and the Diffie-Hellman ratchet path. Under `HmacAgrees`,
  `HkdfAgrees` (stated under RFC 5869's `N.val ≤ 8160`, discharged at the
  64- and 80-byte literals), `ZeroizingRoundTrips`, `VecRemoveTotal`
  (stated under `i.val < v.val.length`, discharged from each scan's own loop
  guard) and `DerivedKeysModel` (the T1 section says what it is), the `hone`
  at-most-one hypothesis named in "what is not proved", a store-size
  precondition (`hs`) and a step of room in the expiry clock
  (`hroom : events + 1 < U32.max`, one step below the `u32` ceiling because
  `age_store` clamps the clock at `MAX_EVENTS = u32::MAX - 1` while the model
  counts in `Nat`); it says nothing about the failure branches. Pinned base: the kernel's three axioms and
  eleven opaque externals (`hkdf_sha256`, `hmac_sha256`, five declarations of
  the `zeroize` wrapper including `deref_mut`, the array, pair and `Vec`
  `Zeroize` instances, and `Vec::remove`), and no `native_decide`.
- `message_keys_refines`: the expansion of a message key into the AEAD key,
  the MAC key and the IV computes what `Model.State.messageKeys` says -- the
  zero salt, the `mkInfo` label and the 32/32/16 split -- for every key. This
  is the last derivation before the cipher, and the one a label or
  split-order error would change every ciphertext key through while every
  other theorem stayed true. Under `HkdfAgrees` and `ZeroizingRoundTrips80`,
  the wrapper round trip at the eighty-byte width this one call uses, stated
  separately so that no other theorem's hypothesis widened
  (`Translation/Satisfiability.lean` exhibits a model of it and of the
  sixty-four-byte `ZeroizingRoundTrips`). Pinned; the ratchet vectors record
  the same three values on every step.
- `kdf_ck_refines`, `kdf_rk_refines`: the chain-key and root-key steps
  compute `Model.State.kdfCk`/`kdfRk`, the first modulo `HmacAgrees` and the
  second modulo `HkdfAgrees` and `ZeroizingRoundTrips`. `rk_info_agrees` and
  `mk_info_agrees` are where the two sides' copies of the labels are checked
  byte for byte, by `rfl` rather than `native_decide`.
- `skip_message_keys_refines`: the skip step -- the purge scan, the forward
  derivation and the store insertion -- refines `Model.State.skipMessageKeys`
  on success, under `HmacAgrees`, `VecRemoveTotal` and `DerivedKeysModel`.
- `try_skipped_refines`: the skipped-key lookup returns the key the model's
  lookup returns and leaves the store the model leaves, and on a miss the
  model misses too, under `VecRemoveTotal` and `hone`.
- `dh_ratchet_refines`, `derive_chain_refines`, `age_store_refines`,
  `purge_chain_range_refines`, `init_sender_refines`, `init_receiver_refines`:
  the remaining operations the model defines, proved along the way since
  `receive` composes them.

What this section does not cover is what `T3.lean`'s own closing note lists:
the persistence codecs and accessors under "translated is not proved", and
the finite-width cases where `u32` and `Nat` part company.

## Proved (tier T2, PQXDH's input keying material)

Location: `Proofs/SessionEstablishment.lean`.

- `km_determines`: the keying material determines the tuple of agreement outputs
  that produced it, over all five components and both shapes. Two different
  tuples can never reach the key derivation as the same bytes. This is the
  property underneath the derivation's security: if it failed, the hash's
  strength would be beside the point, because the confusion would have happened
  before it.
- `km_none_ne_some`: a session established with a one-time curve prekey cannot
  present the same keying material as one established without.
- `associatedData_inj_of_length`: the two identities are recoverable from the
  associated data **given** the first encoding's width. The hypothesis is the
  claim's content: the file also carries a counterexample showing the property
  fails without it, and the width is pinned in the core by a test and stated in
  session-establishment.md. The safety lives in the encoder, not in the
  concatenation.
- `sharedSecret_length`, `hkdf_length` (in `tacenta-model/Model/Kdf.lean`),
  `hash_length` (in `tacenta-model/Model/Sha256.lean`): the derivation returns
  exactly thirty-two bytes, and SHA-256 exactly thirty-two, for every input,
  not only at the handful of lengths the known-answer vectors use.

## Proved (tier T3, the PQXDH derivation refines the model)

Location: `Translation/SessionT3.lean`, with panic-freedom in
`Translation/SessionT1.lean`.

- `shared_secret_refines_none` and `shared_secret_refines_some`: given the same
  agreement outputs, the core and the model produce the same thirty-two bytes,
  in both shapes. **Modulo `HkdfAgrees`**: the key derivation is opaque on both
  sides, so that the two agree is assumed, and the model-generated byte vectors
  are what covers it outside Lean. (`SessionT3.HkdfAgrees` is stated at the
  fixed 32-byte width the derivation uses, so it needs no length premise;
  `SessionT1.HkdfTotal` beneath it carries `N.val ≤ 8160` like the others.)
- `km_refines_none`, `km_refines_some`, `associated_data_refines`,
  `associated_data_with_kem_refines`: assumption-free, settled by structure.
- `decode_ec_after_encode_ec`: reading an encoding back gives what was encoded.
- Every function in the session zone is proven panic-free, with the value it
  produces rather than only that it returned.

## Proved (tier T2, wire encoding)

Location: `Proofs/RatchetCorrectness.lean` covers the ratchet; the encoding is in
`Proofs/Serialization.lean`.

- `readBe32_be32`: reading four big-endian bytes inverts writing them, for every
  one of the 2^32 values, discharged by `bv_decide`.
- `decode_encode`: **the round trip.** Decoding an encoded ratchet message
  returns exactly what was encoded, for every ratchet key of the right length,
  every pair of counters, and every ciphertext. This is the property a
  round-trip test can only sample.

These two rest on a weaker base than the ratchet theorems: `propext`,
`Classical.choice`, `Quot.sound`, and a `bv_decide` reflection axiom (the
bit-vector decision procedure, checked by a verified SAT certificate rather than
by the kernel alone). The ratchet theorems above use only `propext` and
`Quot.sound`. The distinction is recorded here rather than glossed.

## Proved (tier T2, the ML-KEM Braid's epoch accounting)

Location: `tacenta-model/Model/Braid.lean`.

The calculation on which both sides must agree exactly, and it rests on
`propext` and `Quot.sound` alone.

- `send_output_epoch`: a key is labelled with the epoch it was negotiated in, on
  the sending side. The responder emits at transition 7, when it samples `ct1`.
- `receive_output_epoch`: and with the same epoch on the receiving side. The
  initiator emits at transition 5, after advancing, and reads the label back off
  the advanced state. The two agreeing is what makes an epoch a shared name for
  a shared key.
- `send_reports`: the epoch a `Send` reports is the one before the state's, so
  it names the last epoch both parties are known to hold rather than the one
  being negotiated.

## Proved (tier T2, the field the erasure code is defined over)

Location: `tacenta-model/Model/Gf65536.lean` and
`tacenta-model/Model/Polynomial.lean`.

- `mul_inv_cancel`: every nonzero element has an inverse and `inv` returns it,
  for all sixty-five thousand five hundred and thirty-five. This doubles as an
  irreducibility check on the reduction polynomial. Established by exhaustion
  through `native_decide`, so it trusts the compiler; there is no kernel route,
  because `decide` cannot reduce that many exponentiations and `bv_decide`
  cannot model an exponentiation at all.
- `interp_eq`: the delta property in the form a decoder states it, which is what
  interpolation needs to recover a lost codeword.

## Not needed: a concatenation lemma for the Triple Ratchet's combination

There is no theorem that the concatenation of the two message keys is
unambiguous, and none is needed. Following §7.2 of the published Double
Ratchet specification, the combination puts the two keys in *different*
arguments -- the post-quantum key as salt, the classical one as input keying
material -- so distinct pairs are distinct inputs by construction.

A combination that concatenated both keys into one derivation input would
need such a lemma (provable from both being exactly thirty-two bytes). Here
the property is structural rather than proved, which is a smaller trusted
base and not a larger one; it is recorded so that its absence from the ledger
is not read as a gap.

## Proved (tier T2, the composite header's round trip)

Location: `tacenta-proofs/Proofs/Serialization.lean`.

- `decode_encode_composite`: decoding an encoded composite header returns the
  header and whatever followed it, for every header whose curve key is
  thirty-two bytes and whose codeword, if it has one, is a full chunk.

  **This is not the same as the parse being unambiguous.** The theorem quantifies over
  headers and asks about bytes the encoder produced, so it says nothing about
  which byte strings the decoder accepts. Canonicality is the other direction
  and is enforced by construction and by test, not yet by proof.

## Proved (tier T1, the translated code cannot fail)

Location: `tacenta-proofs/translation/Translation/T1.lean` and
`tacenta-proofs/translation/Translation/SessionT1.lean`.

- `kdf_ck_no_panic`: the chain-key step `kdf_ck` cannot panic. Its axiom base is
  pinned in `T1.lean` alongside `send_no_panic` and `receive_no_panic`.
- `send_no_panic`: sending on the classical ratchet cannot panic; the
  `ChainExhausted` refusal at the `u32` counter's limit is a returned error,
  not a failure. Pinned with the other two.
- `receive_no_panic`: the translated Double Ratchet receive cannot panic,
  under `HmacTotal`, `HkdfTotal` (stated for every output length within RFC
  5869's `N.val ≤ 8160`, which the crate's `expect` enforces; the two calls
  ask for 64 and 80 bytes), `ZeroizingTotal`, `VecRemoveTotal` (stated for
  an in-range index, `i.val < v.val.length →`, which is where `Vec::remove`
  returns; each of the three scans discharges it from its own loop guard)
  and `DerivedKeysModel`, plus the store-size precondition `hs`.
  Since CR-15 the forward derivation returns its keys in a `Zeroizing`
  wrapper and the store loop reads them back by index, so this and the
  `skip_message_keys`/`derive_chain` lemmas beneath it take
  `DerivedKeysModel`, a class in the shape of the session zone's
  `ZeroizingModel`: the wrapper is a transparent container whose `new`,
  `deref` and `deref_mut` return what was put in (`LIMITATIONS.md` says why
  totality alone is not enough). Its pinned base gained the wrapper's
  `deref_mut` and the two `Zeroize` instances the wrapper reaches.
  **This is the classical half only.** Since the triple-ratchet integration the session's receive
  path runs through `tacenta-triple`, which composes this with `tacenta-spqr`
  and `tacenta-braid`. `tacenta-triple` is translated and proved, and its own
  claims are below -- this theorem names only the classical half; the
  composition itself carries a proof under a different name, in a different
  file.
- `shared_secret_no_panic`: the translated PQXDH shared-secret derivation cannot
  panic, and needs no precondition, because the keying material is at most five
  fixed components so the bound it asks for is discharged from the value rather
  than passed to a caller.

## Proved (tier T1, the erasure coder's entry points cannot fail)

Location: `Translation/ErasureT1.lean`.

- `next_chunk_no_panic`: the encoder's entry point cannot panic, for every
  encoder state, and it needs no hypothesis at all. Pinned to `propext`,
  `Classical.choice` and `Quot.sound` alone: this crate has no opaque
  primitive of its own.
- `message_no_panic`: the decoder's entry point -- the one that consumes
  codewords an attacker supplies, with every index and length computed from
  what they sent -- cannot panic, given only that `Vec::truncate` returns
  (`TruncateTotal`, the one library call the translation does not see
  through). Pinned to the three kernel axioms plus that one external.
- `add_chunk_no_panic`, `has_message_no_panic`, `interpolate_no_panic`,
  `weights_no_panic`, `coefficients_no_panic`, `evaluate_no_panic`,
  `mul_no_panic`: the decoder's other public call, the field, and the
  barycentric helpers the two entry points step through.

`Encoder::new`, `Decoder::new`, `needed`, `received` and the codecs have no
theorem, as "translated is not proved" says, and `LIMITATIONS.md` records
what T3 does and does not reach in this crate. `chunk_count_no_panic` takes
`DivCeilTotal`, stated under `b.val ≠ 0` (the one input on which
`usize::div_ceil` panics) and discharged at its one use, the constant
`CHUNK_BYTES`.

## Proved (tier T1, the wire parser cannot fail)

Location: `Translation/ProtobufT1.lean`.

- `parse_ratchet_body_no_panic`, `parse_prekey_body_no_panic`: both message
  profiles drive every byte string within the declared limit to an `Ok` or
  an `Err` and never to a failure. Pinned to `propext`, `Classical.choice`
  and `Quot.sound` alone: the crate translates with no axiom at all.
- `encode_ratchet_body_no_panic`: the ratchet-body encoder likewise
  (`encode_prekey_body` has no theorem). Same pinned base.

**This parser has no caller on the live path**; see "what is not proved"
above. What these theorems establish is that a verified reader exists, not
that received bytes go through it.

## Proved (tier T1, the message decoders cannot fail)

Location: `Translation/WireT1.lean`.

`decode_message` is the first code the bytes of a ratchet message reach on the
live receive path: the session calls it before anything is authenticated, and
`decode_composite` is all of its parsing. Both live in `tacenta-core/wire`, a
leaf crate the translation covers, and `tacenta_core::serialization` re-exports
them, so this is the decoder the product runs.

- `decode_composite_no_panic`, `decode_message_no_panic`: every byte string
  decodes to an `Ok` or an `Err` and never to a failure, with no precondition,
  since the input is whatever arrived. Pinned to `propext`, `Classical.choice`
  and `Quot.sound` alone: the decoder calls no opaque operation.
- `decode_initial_no_panic`: the same for `decode_initial`, which decodes a
  prekey message. Each field's end is computed by `span_end`, whose full
  specification (`span_end_spec`: the end exactly when the field fits, nothing
  exactly when it does not, an overflowing addition included) is what bounds
  every later read. Same pinned base.
- `decode_bundle_no_panic`: the same for `decode_bundle`, which decodes a
  published prekey bundle. Its one optional field is decided by
  `one_time_prekey_at` (`one_time_prekey_at_no_panic`) over thirty-three bytes
  the decoder has already bounded. Same pinned base.

## Proved (tier T3, the ratchet-message decoder computes what the model says)

Location: `Translation/WireT3.lean`.

Against `Model.CompositeHeader.decode`, the model's decoder for the composite
header, which applies the same "exactly one spelling" rules as the code.

- `decode_composite_refines`: for every byte string, `decode_composite`
  returns `Ok` exactly when the model returns `some`, with the same header
  and the same unread bytes, and `Err` exactly when the model returns `none`.
  No hypothesis. Because the model accepts one spelling of each header, the
  code does too, for every input: the property `tests/canonicality.rs`
  samples, stated in full.
- `decode_message_refines`: the same for `decode_message`, whose ciphertext
  is exactly the bytes the model leaves after the header.

Both are pinned to `propext`, `Classical.choice` and `Quot.sound` alone.
The big-endian arithmetic relating the code's `from_be_bytes` to the model's
shifts and ORs is proved on the kernel in the same file; the model's own
round-trip lemmas settle the same identities with `bv_decide`, and neither
theorem depends on them.

**What this does not give.** An end-to-end claim from wire bytes to a ratchet
decision also needs the session's use of the decoded header, which is outside
the translated surface (`tacenta-core/src/sessions`).

## Proved (tier T3, the initial-message decoder computes what the model says)

Location: `Translation/WireInitialT3.lean`.

Against `Model.Messages.decodeInitial`.

- `decode_initial_refines`: for every byte string, `decode_initial` returns
  `Ok` exactly when the model returns `some`, with the same identity and
  ephemeral keys, KEM ciphertext, three prekey identifiers and trailing ratchet
  message, and `Err` exactly when the model returns `none`. No hypothesis.
  Pinned to `propext`, `Classical.choice` and `Quot.sound` alone.
- `decodeInitial_cases`: the model's decoder by cases, the lemma the refinement
  rewrites with. Too short, a wrong version or type byte, or no room for the two
  keys and the ciphertext length is `none`; otherwise the decoded message is one
  expression over fixed offsets and the ciphertext length read at offset 68.

**What this does not give.** The same limit as above: what the session does
with a decoded initial message is outside the translated surface.

## Proved (tier T3, the prekey bundle decoder computes what the model says)

Location: `Translation/WireBundleT3.lean`.

Against `Model.Messages.decodeBundle`. `decode_bundle` has no caller inside the
engine: an application calls it on a bundle it fetched, before any session
exists.

- `decode_bundle_refines`: for every byte string, `decode_bundle` returns `Ok`
  exactly when the model returns `some`, with the same identity key, signed
  prekey and signature, KEM prekey and signature, one-time prekey and three
  identifiers, and `Err` exactly when the model returns `none`. No hypothesis.
  Pinned to `propext`, `Classical.choice` and `Quot.sound` alone. Since the
  model accepts one spelling of each bundle, so does the code.
- `decodeBundle_cases`: the model's decoder by cases, the lemma the refinement
  rewrites with. Too short for the framing, a wrong version or type byte, or too
  short for the fixed prefix is `none`; otherwise the bundle is `some` exactly
  when the input is as long as the KEM prekey's length says and the one-time
  prekey's field is a valid spelling.
- `one_time_prekey_at_spec`: the code's decision on the one-time prekey's
  presence byte and thirty-two bytes is the model's `decodeOptionalKey`.

**The model was looser than the code, and now is not.** Until this proof the
model's `decodeBundle` accepted an absent one-time prekey over any thirty-two
bytes, while `message-format.md` and the Rust decoder both require them to be
zero, so the refinement could not have held. The model now refuses non-zero
padding through `decodeOptionalKey`, and
`Proofs.Serialization.decodeBundle_encodeBundle` still holds.

**What this does not give.** What is done with a decoded bundle -- verifying its
signatures and agreeing with its keys -- is outside the translated surface.

## Proved (tier T1, the sparse post-quantum ratchet's entry points cannot fail)

Location: `tacenta-proofs/translation/Translation/SpqrT1.lean`.

These three are in the `Tacenta.SpqrT1` namespace -- bare names shared with,
and distinct from, the classical ratchet's own theorems of the same name
above. All three carry stated room preconditions (the epoch table has space
for one or two more entries, the skipped-key store has room for one more
batch); none is unconditional totality. None carries an epoch or counter
bound any more: every epoch and per-chain counter increment in the source
is a `checked_add` whose `None` arm returns `ChainExhausted`, and the proofs
walk that arm as a value, as `BraidT1.lean`'s did after CR-03; the
refinement in `SpqrT3.lean` keeps `hepoch`/`hcounter` for the model's
reason (it counts in `Nat`), as that section says.

- `advance_no_panic`: the sparse post-quantum ratchet's DH-style epoch advance
  cannot panic.
- `send_no_panic`: sending on the sparse ratchet cannot panic.
- `receive_no_panic`: receiving on the sparse ratchet cannot panic. This is the
  one an attacker's header drives directly -- the epoch lookup, the
  skipped-key walk, and the forward-derivation count are all
  attacker-influenced, so this is what stands between a malformed message and
  a remote denial of service, for this one leaf crate. `tacenta-triple`, which
  composes this with the classical ratchet above, is translated and proved
  (see below).
- `send_no_panic` and `receive_no_panic` are pinned under `#guard_msgs` at the
  end of the file. `receive_no_panic` is not kernel-only: besides the crate's
  opaque-operation axioms it carries
  `SpqrT1.receive_no_panic._native.native_decide.ax_1_1`, one closed numeric
  fact in its proof settled by `native_decide`.
- Seven opaque-operation assumptions back these theorems (`VecRemoveTotal`,
  stated under the index guard `i.val < v.val.length →` and discharged from
  the skipped-key scan's own loop check; `KdfCkTotal`, `ZeroizeTotal`,
  `VecRetainTotal`, `KdfRkTotal`, `OptionCloneTotal`, `VecAppendTotal`), each
  a per-crate axiom Aeneas could not model, none shared with the classical
  ratchet's own copies of the same operations. See `SpqrT1.lean`'s own
  closing section for why the count is seven and not five.

## Proved (tier T1, the ML-KEM Braid's entry points cannot fail)

Location: `tacenta-proofs/translation/Translation/BraidT1.lean`.

- `mac_eq_no_panic`: the constant-time authenticator comparison cannot panic,
  given equal-length inputs -- the crate's only loop.
- `Braid.step_send_no_panic`, `Braid.send_no_panic`: the eleven-state
  machine's sending half, and its entry point, cannot panic, given an RNG
  whose `fill_bytes` returns (`RngTotal rc`, the premise the real
  `generate`/`encapsulate1` need, carried by `KeyPairGenerateTotal` and
  `Encapsulate1Total` and threaded through both theorems).
- `Braid.step_receive_no_panic`, `Braid.receive_no_panic`: the receiving half
  and its entry point cannot panic. This is the one an attacker's header,
  chunk data, and claimed lengths drive directly, so this is what stands
  between a malformed message and a remote denial of service, for this leaf
  crate. One real precondition travels with these two: `State.ct1_bounded`, a
  concrete size cap on the KEM ciphertext carried across the encapsulation
  exchange (an invariant `step_send` maintains but this file does not prove,
  since that would be a T3 claim about the whole state machine rather than a
  T1 one about a single function). The epoch bound they used to carry as well
  (`hepoch`, an epoch counter below `2^64`, the same shape of bound the
  classical ratchet and the sparse ratchet each need above) is no longer a
  hypothesis of either theorem: the two transitions that advance the epoch
  now use `checked_add` and answer `Failed` at the ceiling (CR-03), an
  outcome the theorems prove as a value rather than assume away.
  **Nothing below closes the `ct1_bounded` gap**, and it is worth
  being exact about why, since the obvious candidate does not apply:
  `tacenta-triple` is proved (T1 and T3, both further down this file), but it
  composes `tacenta-spqr` and `tacenta-ratchet`, not `tacenta-braid`. The Braid
  sits beneath the session alongside the Triple rather than inside it, so the
  Triple's proofs never see the Braid's state and cannot discharge an invariant
  about it. Closing this needs a T3 claim about the Braid's own state machine
  maintaining `ct1_bounded` across `step_send`, which `BraidT3.lean` does not
  currently make.
- `finish_encaps_no_panic`, and every helper the state machine calls
  (`info_no_panic`, `Auth.update_no_panic`/`mac_hdr_no_panic`/
  `mac_ct_no_panic`/`init_no_panic`, `kdf_ok_no_panic`, `State.clone_no_panic`,
  `Braid.clone_no_panic`, `Output.clone_no_panic`), are proved along the way,
  since `step_send`/`step_receive` call all of them.
- Twenty-six opaque-operation assumptions back these theorems, over the
  erasure coder, the KEM (its two randomness-drawing totals under
  `RngTotal rc`), the two KDF calls (`HkdfSha256Total` under RFC 5869's
  `N.val ≤ 8160`, discharged at the 32- and 64-byte literals), this crate's
  own copy of `Option::clone`, and, since CR-15, the `zeroize` crate's three
  touches
  (`ZeroizingArrayRoundTrip`, the wrapper's constructor and projection as one
  round trip at every width; `ArrayZeroizeTotal`, the in-place wipe of the
  raw KEM secret; `RangeFullIndexTotal`, the `key[..]` index the Aeneas
  library does not model) -- none shared with `SpqrT1.lean`'s or `T1.lean`'s
  copies of the same kinds of operation, and each of the three with a model
  in `Translation/Satisfiability.lean`. Several carry a concrete size cap
  (`≤ 4096`) rather than headroom below `Usize.max`, because `finish_encaps`
  sums two independently-capped values at one call site, and two facts each
  "under `Usize.max`" do not compose the way two concrete caps do. See
  `BraidT1.lean`'s own closing section for the full list.
- `Braid.send_no_panic` and `Braid.receive_no_panic` are pinned under
  `#guard_msgs` at the end of the file, to the kernel's three axioms and the
  crate's opaque constants; no `native_decide` reaches either.

## Proved (tier T1, the Double Ratchet's persistence codec cannot fail)

Location: `Translation/RatchetCodecT1.lean`.

`State::to_bytes` writes what a storage layer keeps, and `State::from_bytes`
parses it back after a restart and hands the ratchet a state to run on.

- `from_bytes_no_panic`: every byte string decodes to `Ok` or `Err` and never
  to a failure, under one precondition, `bytes.length + 72 ≤ Usize.max`. The
  skipped-key loop computes where the next 72-byte entry would end before it
  compares that end with the input, and Aeneas models a slice as anything up
  to `Usize.max` long. A Rust slice is at most `isize::MAX` bytes, so every
  buffer a caller can pass meets it; it is a constant beside `Usize.max`, not
  another type's maximum, so it forces nothing to zero on a 32-bit target.
  Pinned to `propext`, `Classical.choice` and `Quot.sound` alone.
- `to_bytes_no_panic`: encoding cannot fail when the buffer -- 185 bytes plus
  72 per skipped key -- fits a `usize`, under `ZeroizingVecTotal`: the
  `zeroize` crate's `Zeroizing::new` returns on a byte vector, the same kind of
  assumption as `ZeroizingTotal` above. Its pinned base adds the wrapper's
  opaque declarations and nothing else.
- `to_bytes_no_panic_of_inv`: the size precondition discharged for every state
  satisfying `ImportInv`'s `Inv`, whose store holds at most `MAX_SKIPPED_STORE`
  (2000) keys, so every state `from_bytes` returns can be written back. Same
  pinned base.

**Not covered.** The codecs of `tacenta-braid` and `tacenta-triple` still have
no T1 theorem (`tacenta-spqr`'s and `tacenta-erasure`'s have, below), and
neither function here has a round-trip or refinement theorem: this says they
return, not what they return.

## Proved (tier T1, the sparse post-quantum ratchet's persistence codec cannot fail)

Location: `Translation/SpqrCodecT1.lean`.

- `from_bytes_no_panic`: every byte string decodes to `Ok` or `Err` and never
  to a failure, under `bytes.length + 90 ≤ Usize.max`, for the classical
  ratchet's reason: the chains loop computes where the next 90-byte entry would
  end before it compares that end with the input. Every Rust slice meets it.
  Pinned to `propext`, `Classical.choice` and `Quot.sound` alone.
- `to_bytes_no_panic`: encoding cannot fail when the buffer -- 50 bytes plus
  90 per chains entry and 48 per skipped key -- fits a `usize`, under this
  crate's own `ZeroizingVecTotal`. The encoder ends by asserting the buffer is
  as long as `encoded_len` said, so the proof shows every write adds exactly
  what `encoded_len` counts, and the assertion cannot fire. Its pinned base
  adds the wrapper's opaque declarations and nothing else.
- `to_bytes_no_panic_of_inv`: the size precondition discharged for every state
  satisfying `ImportInv`'s `Inv`, which holds at most two chains entries
  (`inv_gives_chains_len`) and 2000 skipped keys. Same pinned base.

**Not covered.** This codec has no round-trip or refinement theorem either.

## Proved (tier T1, the erasure coder's persistence codecs cannot fail)

Location: `Translation/ErasureCodecT1.lean`.

`tacenta-erasure`'s `Encoder` and `Decoder` each persist a stream in progress
through a `to_bytes`/`from_bytes` pair, which the Braid calls.

- `encoder_from_bytes_no_panic`, `decoder_from_bytes_no_panic`: every byte
  string decodes to `Some` or `None`, under `bytes.length + 32 ≤ Usize.max`
  and `bytes.length + 34 ≤ Usize.max` respectively; each loop computes where
  the next entry would end before comparing it with the input. The decoder's
  final `invariant` reaches `usize::div_ceil`, which the translation cannot see
  inside, so it takes `ErasureT1`'s `DivCeilTotal` and its pin lists
  `core.num.Usize.div_ceil`. The encoder's is pinned to the kernel's three
  axioms alone.
- `encoder_to_bytes_no_panic`, `decoder_to_bytes_no_panic`: encoding cannot
  fail when the buffer -- 7 bytes plus 32 per chunk, and 20 plus 34 per
  codeword -- fits a `usize`. Each ends by asserting the buffer is as long as
  `encoded_len` said, and the proof shows the assertion cannot fire. Neither
  wraps its buffer in `Zeroizing`, so no `zeroize` assumption appears; both are
  pinned to the kernel's three axioms alone.

**Not covered.** These are the erasure crate's own translation. In the Braid's
translation the same four functions are opaque declarations (listed among its
externals in `translation-attestation.json`), so nothing proved here reaches
the Braid's calls to them, and the Braid's own codec has no T1 theorem. There
is no round-trip or refinement theorem, and the encoders' size preconditions
are not discharged from `invariant` here.

## Proved: what a decoded state satisfies

Location: `Translation/ImportInv.lean`. The **validated persistence
constructor**. Every leaf crate's `State::from_bytes` ends by calling that
crate's own `pub fn invariant(&self) -> bool` and returning the crate's
malformed error when it is false. Until this file existed, nothing in the tree
said what that buys: `from_bytes` had no theorem at all, so as far as the
proofs were concerned an untrusted byte string could hand back a state
violating the preconditions the T1 and T3 theorems take (`hs`, `hone`,
`hroom`, `hskiproom`, `ct1_bounded`). That is what "Read this first" recorded,
and this section is what closes it for three crates.

Read each crate's chain in one line: **decoded state → `Inv` → precondition →
theorem.** The subject throughout is the *translated* `from_bytes`, the same
artefact every other theorem in this package is about.

**What is not claimed: preservation.** Nothing in this section says the
predicates are *preserved by every operation*. Each `Inv` is a conjunction of
field conditions; the theorems below say a decoded state satisfies it, and
that it yields the preconditions the `receive` theorems take, and no more.
There is no theorem here of the form "`send`/`receive` carries a state
satisfying `Inv` to one satisfying `Inv`", for any of the three crates, and
`Inv s` therefore does not on its own say that any run of the crate built `s`.

That is worth stating because it decides how the decoder's refusal should be
read. Where a predicate is not maintained by the operations, `from_bytes` can
refuse a state an honest run could produce, and the refusal is a **policy**
rather than a consistency check. The property that makes it a consistency
check -- that no run of the crate produces a state the predicate rejects, so
the values the predicate excludes are values the operations never reach -- is
established by the crates, in the Rust, in the comments beside the counters
concerned and in their import tests, not here. Read it as the property the
crates establish; the Lean side would need a preservation theorem per
operation, and that is open work.

**What is not claimed: a step of counter headroom.** The three crates reserve
the top value of the counter each steps, so that no state their operations
produce is one their own decoder refuses; the models count in `Nat` and
reserve nothing. The refinement theorems are therefore stated one step below
the ceiling -- `T3.receive_refines`'s `hroom` is `events + 1 < u32::MAX`,
`SpqrT3`'s and `BraidT3`'s `hepoch` is `epoch + 1 < u64::MAX`, and
the Triple Ratchet's refinement on the unit passes the same two premises
through to its caller -- and no
`invariant()` can close that step, because the state at the last unreserved
value is one the crate produces, decodes and goes on operating on. The
panic-freedom corollaries here are unaffected and take no such premise; the
refinement corollary takes it as an explicit argument. "Read this first" gives
the one-line form.

Two hypotheses are carried rather than discharged, both named, neither new to
this file in substance:

- `Tacenta.BraidT1.Ct1LenTotal` for the Braid, which `BraidT1.lean` already
  states and already uses: `tacenta_kem::CT1_LEN` returns a value at most
  4096. The real constant is 1408 (`braid/src/lib.rs` says so where
  `ct1_bounded` is motivated).
- `hclock_unparked : s.events.val + 1 < U32.max` on
  `Ratchet.decoded_receive_refines`, the step of clock headroom
  `T3.receive_refines`'s `hroom` asks for. Unlike the other this one is
  **not** satisfied by every state the real Rust produces: it excludes exactly
  the parked clock, `events = MAX_EVENTS = u32::MAX - 1`, which `age_store`
  clamps to and which an honest run reaches after 2^32 accepted receives. It
  is an explicit argument for that reason, so a caller sees what is being
  asked.

### `tacenta-ratchet` -- complete

`Inv` mirrors `State::invariant`'s five clauses on the translated state: the
store is at most `MAX_SKIPPED_STORE`, `events` is below `u32::MAX`, no stored
entry's `stored_at` is ahead of `events`, the store is pairwise distinct on
`(dh, n)`, and a receiving chain implies a sending chain and a peer key.

- `Ratchet.invariant_eq : State.invariant s = ok (InvB s)` -- the translated
  Bool-valued `invariant` is total and computes an explicit Bool, on every
  state. Its two nested index loops are characterised by
  `invariant_inner_spec`/`invariant_inner_eq` and
  `invariant_outer_spec`/`invariant_outer_eq`, in the loop-invariant style
  `T1.lean` uses (`loop.spec_decr_nat` with a measure and an invariant,
  stepping the list with `List.drop_eq_getElem_cons`).
- `Ratchet.invariant_true_iff`: `State.invariant s = ok true ↔ Inv s`, an
  equivalence, not an implication.
- `Ratchet.from_bytes_establishes_inv`: `∀ bytes s, State.from_bytes bytes =
  ok (Ok s) → Inv s`. **No hypothesis of any kind.** The premise is that the
  decoder returned, so every fallible step it took returned and is peeled as
  an equation rather than assumed. Axioms: `propext`, `Classical.choice`,
  `Quot.sound`, pinned under `#guard_msgs`.
- Bridges -- two, each discharging a named premise:
  `Ratchet.inv_gives_store_bound` (`Inv` → T1's `hs`, with the constant part
  `MAX_SKIPPED_STORE + MAX_SKIP ≤ usize::MAX` proved outright by
  `Ratchet.store_plus_skip_fits` rather than assumed) and
  `Ratchet.inv_gives_store_is_map` (`Inv` + `StateR` → T3's `hone`).
- A recorded consequence of `Inv`, and **not** a bridge:
  `Ratchet.inv_gives_clock_room` (`Inv` → `events < u32::MAX`, the
  invariant's own clock clause). It is **one step short of T3's
  `hroom`** and deliberately stays there: `hroom` is now
  `events + 1 < u32::MAX`, and the clause cannot be strengthened to close the
  step, because `events = MAX_EVENTS` is a state `age_store` produces and the
  decoder accepts -- which is why `decoded_receive_refines` below takes that
  step as `hclock_unparked`, an explicit argument, rather than reading it off
  the invariant. What the clamp did buy is on the other side of the ledger:
  `age_store` now *preserves* `events < u32::MAX` rather than assuming it, so
  that clause holds of every state a run reaches and not only of every state
  the decoder admits.
- `Ratchet.decoded_receive_no_panic`, `Ratchet.decoded_receive_refines`: the
  chain end to end -- a `receive` on a decoded state does not panic, and,
  given a step of clock headroom, it refines `Model.Ratchet.receive` -- each
  taking the decode as its hypothesis and discharging the state-shaped
  preconditions itself. `decoded_receive_no_panic` is now unconditional: the
  boundary assumptions, the bytes and the decode, and nothing else.
  `decoded_receive_refines` takes one explicit argument,
  `hclock_unparked`, as described above. **Neither is
  kernel-only.** Each composes with a `T1`/`T3` `receive` theorem, so each
  carries that theorem's eleven `tacenta_ratchet.*` opaque-operation axioms
  (the two KDF calls, `Vec::remove`, and the `zeroize` wrapper's constructor,
  projections and `Zeroize` instances). Both are pinned under `#guard_msgs`
  with that list in the pin, so the base cannot widen unnoticed.
- `Ratchet.from_bytes_accepts_witness`: `∃ s, State.from_bytes witnessBytes =
  ok (Ok s)` -- the translated decoder accepts a concrete 185-byte string
  (`witnessBytes`: version byte, four keys with each `Option` tag present,
  four zero counters, the label byte, a zero skipped-key count). Axioms:
  `propext`, `Classical.choice`, `Quot.sound`, pinned. The concrete byte
  reads are `decide` on a list literal, so this is kernel work and not
  `native_decide`'s compiler trust.
- `Ratchet.from_bytes_establishes_inv_nonvacuous`: `∃ bytes s,
  State.from_bytes bytes = ok (Ok s) ∧ Inv s` -- so
  `from_bytes_establishes_inv` is **not vacuous**: its premise is
  satisfiable, and a decoder that rejected every buffer would not satisfy
  this. Same three axioms, pinned. This is the discipline
  `Translation/Satisfiability.lean` applies to the leaves' opaque-boundary hypotheses,
  applied to a decoder's premise. There is no counterpart for the sparse
  ratchet or the Braid: those `from_bytes` chains are longer, and the
  Braid's runs through the opaque erasure and KEM decoders, which no byte
  string can be shown to satisfy from inside the translation. Their
  `from_bytes_establishes_inv` are therefore **not** known to be
  non-vacuous, and the Rust-side round-trip tests
  (`ratchet/tests/audit_import.rs` and its siblings) are the only evidence
  that those decoders accept anything.

### `tacenta-spqr` -- the sparse ratchet, complete for T1 and for three of T3's premises

`Inv` mirrors `State::invariant`'s four clauses across its two pairs of nested
loops: the skipped store is at most `MAX_SKIPPED_STORE`; every chain's epoch
`q.1` satisfies `q.1 ≤ epoch ∧ epoch < saturating_add q.1 EPOCHS_KEPT` -- the
*current* epoch lies in the window starting at the chain's, which for
`EPOCHS_KEPT = 2` puts the chain epochs in `{epoch - 1, epoch}` -- with no two
chains sharing an epoch; the current epoch is among them; and every skipped
key names a present chain, with no two sharing `(epoch, n)`. Note the
direction: the clause is not "the chain's epoch is in a window above `epoch`".
`Spqr.inv_gives_chains_len` reads the two-value bound straight off it. The
window is written with `saturating_add` exactly as the Rust writes it.

- `Spqr.invariant_eq : State.invariant s = ok (InvB s)`, over five loop
  characterisations: `chains_inner_eq`, `chains_outer_eq`, `present_eq`,
  `skipped_inner_eq`, `skipped_outer_eq`.
- `Spqr.invariant_true_iff`: `State.invariant s = ok true ↔ Inv s`, the same
  equivalence as the ratchet's, over the six clauses above.
- `Spqr.from_bytes_establishes_inv`: `∀ bytes s, State.from_bytes bytes =
  ok (Ok s) → Inv s`. No hypothesis; same three axioms, pinned.
- Bridges -- three, each discharging a named premise:
  `Spqr.inv_gives_chain_room` (`Inv` → `SpqrT1`'s
  `hroom : chains.length + 2 < Usize.max`, which is also `SpqrT3`'s),
  `Spqr.inv_gives_skip_room` (`Inv` → `SpqrT1`'s `hskiproom`, likewise), and
  `Spqr.inv_gives_store_is_map` (`Inv` + `StateRefines` → `SpqrT3`'s `hone`).
  Both T1 bridges are
  unconditional: `Spqr.inv_gives_chains_len` derives `chains.length ≤ 2` from
  the window and the distinctness (the retention policy, read back off the
  invariant), and 4 and 3000 are below `Usize.max` on every target Aeneas
  models.
- A recorded consequence of `Inv`, and **not** a bridge:
  `Spqr.inv_gives_epoch_room` (`Inv` → `epoch < u64::MAX`). It **is no longer
  `SpqrT3`'s `hepoch`**: `advance` now reserves `u64::MAX` and
  refuses the step that would reach it -- at that epoch `clear_old_epochs`'s
  own window would retire every chain including the one just opened -- so
  `hepoch` reads `epoch + 1 < u64::MAX`, while `epoch = u64::MAX - 1` remains
  a fully usable epoch the operations produce and the invariant admits. So the
  lemma discharges no premise of anything: not `SpqrT3`'s `hepoch`, which is
  now a step stronger, and not the corollary below either, since
  `SpqrT1.receive_no_panic` takes no epoch bound at all. It is kept as a fact
  about `Inv` worth having on the record, listed apart from the bridges so the
  list of bridges stays a list of premises actually discharged.
- `Spqr.decoded_receive_no_panic`: the chain end to end -- a `receive` on a
  decoded state does not panic, with no side condition left for a caller.
  **Not kernel-only, and not only because of the opaque operations.** It
  carries ten `tacenta_spqr.*` opaque-operation axioms *and*
  `SpqrT1.receive_no_panic._native.native_decide.ax_1_1`, inherited from
  `SpqrT1.receive_no_panic`: one closed numeric fact in that proof is settled
  by `native_decide`, so the Lean compiler's evaluation is trusted where the
  kernel would otherwise check. This end-to-end statement is the point at
  which that compiler trust reaches a claim about a state read off disk. It is
  pinned under `#guard_msgs` with the axiom named in the pin, and it is the
  only compiler-trusted statement in `ImportInv.lean`. `LIMITATIONS.md` counts
  that `native_decide` use among the fourteen inside translation theorems.

**What this does not give.** `SpqrT3.receive_refines` also takes `hepoch`,
`hcb`, `hsb`, `hnewb` and `hcounter`, and those are **not** consequences of
the crate's `invariant`: a state with `epoch = u64::MAX - 1` and a chain at
that epoch passes `invariant` and fails both `hepoch` and `hcb`. `hepoch` is
on this list because the reserved ceiling moved it there -- it now asks for a
step of headroom, `epoch + 1 < u64::MAX`, and the invariant reaches only
`epoch < u64::MAX` (`Spqr.inv_gives_epoch_room`). There is deliberately no
`decoded_receive_refines` for this crate; those five premises stay with the
caller.

### `tacenta-braid` -- the one clause its theorems need

The Braid's `invariant` is a twelve-way match whose arms mostly delegate to
`tacenta-erasure`'s `Encoder::invariant` and `Decoder::invariant`. Those are a
different crate and reach this translation as opaque axioms, so there is no
full `Inv` to state here. What is read off the arms directly is the clause the
theorems take.

- `Braid.Inv b` -- a deliberately partial mirror, holding
  `Tacenta.BraidT1.State.ct1_bounded b.state`.
- `Braid.invariant_true_gives_inv : Ct1LenTotal → Braid.invariant b = ok true →
  Inv b`. One direction only; the converse would have to characterise the
  opaque erasure invariants.
- `Braid.from_bytes_establishes_inv`, with
  `Braid.from_bytes_establishes_invariant`: `Braid.from_bytes bytes = ok (Ok b)
  → Braid.invariant b = ok true`, and the second
  composing the two.
- `Braid.decoded_receive_no_panic`: the chain end to end -- a `receive` on a
  decoded Braid does not panic, given the boundary hypotheses
  `BraidT1.Braid.receive_no_panic` already takes. Kernel-only it is not: its
  axiom base is the union of the erasure coder's and the KEM's opaque
  constants with the Braid's own KDF calls and `zeroize` touches, and it is
  pinned under `#guard_msgs` with that list.

**What this does not give.** `BraidT3.step_receive_refines` also takes
`hepoch : epoch + 1 < u64::MAX`, which the Rust `invariant` does not check at
all (it checks `epoch >= 1` and nothing above), so there is no
`decoded_step_receive_refines`. `epoch < u64::MAX` is now a property of every
state a run of the Braid reaches (the Braid T3 section says how), but it is
still not derivable from `invariant`, which bounds the epoch only from below,
and it is one step short of what the refinement asks in any case.

### The crates still open

`tacenta-triple`, `tacenta-erasure`, `tacenta-session` and
`tacenta-protobuf` have no theorem here. `tacenta-triple` and
`tacenta-erasure` have an `invariant()` and a `from_bytes` that calls it, and
the same technique applies; they were not done. And in every case the subject
is a **leaf crate's own persistence format**. `Session::from_bytes` and the
storage layer that calls it live in `tacenta-core/src/sessions`, which is not
translated, so nothing here says what a session restored from disk satisfies.

## Proved (tier T1, the same two ratchets compiled as one crate with the Triple)

Location: `tacenta-proofs/translation/Translation/UnitT1.lean`,
`Translation/UnitSpqrT1.lean` and `Translation/UnitPins.lean`.

These are the theorems above, restated about
`Translation/TacentaTripleUnit.lean` -- the translation of
`tacenta-core/triple-unit`, which is the Triple Ratchet and both inner ratchets
compiled as one crate. They exist because a theorem about the Double Ratchet's
own translation says nothing about the Double Ratchet inside the unit: the
constants are different constants, and Lean has no reason to connect them.
`LIMITATIONS.md` says what the crate boundary does and does not cost, under
"The three-leaf translation unit".

The proof files are **generated** from the leaf proofs by
`scripts/port-unit-proofs.sh`, which rewrites the import, the namespace and the
`open` and copies every proof body unchanged. `--check` regenerates and diffs
in CI, so the copies cannot drift from the originals in either direction.

- `Tacenta.UnitT1.kdf_ck_no_panic`: `kdf_ck` compiled inside the unit cannot
  panic.
- `Tacenta.UnitT1.send_no_panic`: likewise for the classical ratchet's send.
- `Tacenta.UnitT1.receive_no_panic`: likewise for receive, under exactly the
  hypotheses the leaf theorem takes.
- `Tacenta.UnitSpqrT1.send_no_panic`: likewise for the sparse ratchet's send.
- `Tacenta.UnitSpqrT1.receive_no_panic`: likewise for the sparse ratchet's
  receive.

**What the pins add, which is the reason to have them.** Each of the five is
pinned in `UnitPins.lean`, and each base is the leaf theorem's base name for
name, with `tacenta_triple_unit.` in front of every translated axiom and
nothing else changed. That is a statement about the printed lists. A leaf file opens its
crate's namespace, so its pins print a translated axiom without the
crate's own prefix -- `tacenta_kdf.hmac_sha256` for what is fully
`tacenta_ratchet.tacenta_kdf.hmac_sha256` -- and the underlying names
differ by that prefix as well. Nothing appears that the leaf did not assume, nothing the
leaf assumed has quietly become a definition, and no proof that was kernel-only
has become compiler-trusted. `Tacenta.UnitSpqrT1.receive_no_panic` carries
`Tacenta.UnitSpqrT1.receive_no_panic._native.native_decide.ax_1_1`, the same
compiler-trust axiom its leaf twin carries and for the same closed numeric
fact; it is the one of the five that is not kernel-only, in the unit as in the
leaf.

**What these do not do on their own.** They say nothing about the composition:
that is the next section, `Translation/UnitTripleT1.lean`, which proves the
Triple Ratchet's composed path panic-free from these theorems.

## Proved (tier T1, the Triple Ratchet's composed path on that same unit)

Location: `tacenta-proofs/translation/Translation/UnitTripleT1.lean` and
`Translation/UnitPins.lean`.

The Triple Ratchet's panic-freedom, about `Translation/TacentaTripleUnit.lean`.
`tacenta-triple` composes the classical Double Ratchet and the sparse
post-quantum ratchet, and it is the crate the session's own
`Session::encrypt`/`Session::decrypt` call. The Triple translated on its own
saw both inner ratchets as opaque axioms, so the proof about that translation,
`TripleT1.lean`, had to **assume** seventeen `*Total : Prop` bundles about their
operations, unconditionally. This file **proves** all seventeen from the two
leaf theorems in the section above, under the leaves' real preconditions.
`TripleT1.lean`, the standalone translation and the proofs about it were
deleted after 2a89a7f, once this file and the next T3 section covered them.

This file is **hand-written**, not generated by `scripts/port-unit-proofs.sh`:
it began as `TripleT1.lean`, which wrote forty-nine translated names in
qualified form, and its proof bodies genuinely changed on the way.

**This is the claim that says anything about the composed path.**
`tacenta-core/src/sessions`, the product code that calls `tacenta-triple`, is
not translated or proved in its own right, so the claim stops at the crate
boundary below it.

- `Tacenta.UnitTripleT1.State.send_no_panic`: the composed send path cannot
  panic, given one precondition -- the sparse ratchet's chain table has room
  for the epoch `maybe_advance` may add plus the one `set_chains` writes
  (`self.post_quantum.chains.length + 1 < Usize.max`).
- `Tacenta.UnitTripleT1.State.receive_no_panic`: the composed receive path
  cannot panic, given three -- the classical ratchet's skipped-store bound
  (`max self.classical.skipped.val.length MAX_SKIPPED_STORE.val + MAX_SKIP.val ≤ Usize.max`),
  and the sparse ratchet's chain-table and skipped-store bounds
  (`self.post_quantum.chains.length + 2 < Usize.max` and
  `self.post_quantum.skipped.length + MAX_SKIP.val ≤ Usize.max`).
- `Tacenta.UnitTripleT1.State.clone_no_panic`: cloning the composed state
  cannot panic. Proved from the stronger fact that it returns `self` unchanged,
  which is what carries the four preconditions above from `self` to the
  `candidate` the two bodies actually call into.
- `Tacenta.UnitTripleT1.State.classical_skipped_len_no_panic`,
  `Tacenta.UnitTripleT1.State.post_quantum_skipped_len_no_panic` and
  `Tacenta.UnitTripleT1.State.post_quantum_receive_count_no_panic`: three of
  the seven public functions that had no T1 theorem while the Triple was
  translated on its own. Each wraps an inner operation that was opaque there
  and is a definition here, so each is a kernel-only one-liner with no boundary
  axiom at all.
- `Tacenta.UnitTripleT1.State.commit_no_panic`: committing the candidate state a
  successful `send` or `receive` returns cannot panic. Kernel-only.
- `Tacenta.UnitTripleT1.State.init_sender_no_panic` and
  `Tacenta.UnitTripleT1.State.init_receiver_no_panic`: the two constructors
  cannot panic. They rest on the HKDF and `zeroize` wrapper boundary, through
  `split_secret`.
- `Tacenta.UnitTripleT1.split_secret_no_panic` and
  `Tacenta.UnitTripleT1.combine_no_panic`: expanding the handshake secret into
  the two ratchets' secrets, and combining the two ratchets' message keys, cannot
  panic. `combine` rests on the HKDF boundary alone; `split_secret` also on the
  `zeroize` wrapper it wipes its expansion with.

These last five are not pinned. Their axiom bases were read off `#print axioms`
on 2026-09-10; the six above them are pinned in `UnitPins.lean`.

**Where the four preconditions land.** They are obligations, not decorations,
and nothing on the unit island discharges them: they land on the untranslated
session layer in `tacenta-core/src/sessions`, which decides how large a
skipped-key store and a chain table it lets a session carry. The classical one
is discharged in the *other* island -- `Ratchet.inv_gives_store_bound` in
`Translation/ImportInv.lean` gets it from the crate's own `invariant()`, and
`Ratchet.decoded_receive_no_panic` chains it from `from_bytes` -- so a state
read off disk satisfies it there. That route has not been ported to the unit,
which is why it does not help here. All four hold of any
state that could exist, at either platform width. That is a claim about every
realisable state and rests on the sizes involved, not on a proof: a witness
would show only that some state meets each bound, which is weaker, and none of
these four is proved to hold of every decoded state on the unit island. They are bounds against
`Usize.max` on quantities that a real session keeps in the low thousands, so
the way to violate one is to hold a vector with billions of entries.

**What the trust base became, honestly.** The standalone
`Tacenta.TripleT1.State.receive_no_panic` depended on twelve axioms and was
kernel-only, as measured on 2026-09-10 with `#print axioms`, before its
deletion; it was never pinned. This file's depends on eighteen and is not: it
inherits
`Tacenta.UnitSpqrT1.receive_no_panic._native.native_decide.ax_1_1`. Both halves
matter. The standalone theorem was kernel-only because it *assumed* the sparse
ratchet's receive is total rather than proving it, so its kernel-only status was
bought by assuming the hard part; this one proves that part and inherits the
one compiler-trusted numeric fact that proof rests on. Six axioms go and twelve arrive. Eleven of the
twelve are a substitution rather than a new kind of trust: the bare operation
axioms are replaced by KDF, `zeroize` and `Vec` boundary axioms that other
proofs in this tree already carry. The twelfth is the `native_decide` axiom
above, which is neither, and is the whole of the regression. `send` is quieter -- twelve axioms before and twelve
after, kernel-only on both sides. `Translation/UnitPins.lean` records all of it.

**Two more assumptions, and one trade.** `SpqrInitAliceTotal` and
`SpqrInitBobTotal` bottom out in `tacenta_spqr.kdf_init`, which no leaf proof
covers, so this file declares `KdfInitTotal` in the same shape as
`UnitSpqrT1.KdfRkTotal`. That replaces two opaque-crate-boundary assumptions
with one trusted-KDF assumption of the kind already relied on everywhere else.

**What is still not proved.** The four remaining public functions without a
T1 theorem -- `State.evict_oldest_classical`,
`State.evict_oldest_post_quantum`, `State.to_bytes` and `State.from_bytes`.
Being inside the unit does not make them fall out: the eviction loops and the
length-prefixed framing are their own proof obligations, unrelated to the crate
boundary this file removes.


## Proved (tier T3, the two inner ratchets' refinements restated about the unit)

Location: `tacenta-proofs/translation/Translation/UnitT3.lean`,
`Translation/UnitSpqrT3.lean` and `Translation/UnitPins.lean`.

`T3.lean` and `SpqrT3.lean` prove the classical and sparse ratchets refine their
models, about the constants those crates' own translations declare. These are
the same proofs, **generated** onto the three-leaf unit by
`scripts/port-unit-proofs.sh`, which rewrites the imports, the namespace and the
`open`, and renames qualified references to the leaf proofs' namespaces so they
name the unit's copies. The renames reach statements and proof bodies as well as
prose -- 45 references in `T3.lean` and 24 in `SpqrT3.lean`: hypothesis types,
cited lemmas, removed stepping rules -- and apart from them every statement and
proof body is copied as written. Each rewrite asserts how often it matches, and
`--check` regenerates and diffs in CI.

The sparse copy also carries one erasure its original does not. On the unit the
two ratchets share one set of `zeroize` constants, so
`UnitT1.zeroizing_deref_step`, a stepping rule `UnitT1.lean` registers for the
classical ratchet, reaches a goal in `UnitSpqrT3.lean` that it cannot reach in
the leaf island, and demands `UnitT1.ZeroizingTotal`, which no hypothesis there
provides. The generator removes that rule at the top of the copy, as `T3.lean`
removes its own copy of it. It is the only rule whose removal matters: two more
`UnitT1.lean` rules sit on constants the unit shares, and removing them as well
changes no proof term. The removal does not carry into a module that imports
the copy.

- `Tacenta.UnitT3.send_refines`: `send` on the classical ratchet, compiled inside
  the unit, refines the model's send.
- `Tacenta.UnitT3.receive_refines`: likewise for receive, under the hypotheses
  `T3.receive_refines` takes.
- `Tacenta.UnitT3.message_keys_refines`: likewise for the message-key expansion.
- `Tacenta.UnitSpqrT3.send_refines` and `Tacenta.UnitSpqrT3.receive_refines`:
  the sparse ratchet's two refinements, compiled inside the unit, under the
  hypotheses `SpqrT3.send_refines` and `SpqrT3.receive_refines` take.

Each is pinned in `UnitPins.lean`, and each prints exactly the axioms its leaf
twin prints, name for name, with `tacenta_triple_unit.` in front of every
translated axiom, each `native_decide` axiom of the two sparse refinements named
under the unit's copy of the lemma that carries it in the leaf, and nothing else
changed. That is a statement about the printed lists. A leaf file opens its
crate's namespace, so its pins print a translated axiom without the
crate's own prefix -- `tacenta_kdf.hmac_sha256` for what is fully
`tacenta_ratchet.tacenta_kdf.hmac_sha256` -- and the underlying names
differ by that prefix as well.

## Proved (tier T3, the Triple Ratchet's composed session on the unit, with both inner bundles discharged)

Location: `tacenta-proofs/translation/Translation/UnitTripleT3.lean` and
`Translation/UnitPins.lean`, against `Model.Triple` in
`tacenta-model/Model/Triple.lean` (the composed state machine;
`tacenta-model/Model/TripleRatchet.lean` carries only `splitSecret`/`combine`).

`UnitTripleT3.lean` proves the composed session refines `Model.Triple`, on the
three-leaf unit. It began as `TripleT3.lean`, the proof about the Triple
translated on its own, which had to assume two hand-written bundles,
`RatchetAgreesFor` and `SpqrAgreesFor`, because that translation could not see
either inner ratchet. On the unit both inner states are concrete and the inner
refinements restated about the unit import, and there both bundles are proved.
`TripleT3.lean` was deleted after 2a89a7f. This file is hand-written, not
generated; it keeps the bundle-taking theorems as the original stated them, and
its header lists every way it differs from that file.

**`Model.Triple` is transcribed from the crate it refines.** Its header says it
is written from `tacenta-spec/protocol/triple-ratchet.md` *and* from
`tacenta-core/triple/src/lib.rs`, because the clone-candidate-commit shape
(neither ratchet's step applied without the other's) is an implementation
decision the specification page does not carry. So these theorems check the
translated crate against a model read off the same crate, which is less
independence than the other tiers have: they establish that the composition does
what its own small, spec-derived description says, not a second, independently
written account of it. `tacenta-model/docs/mapping-to-spec.md` records the same.
The four security properties in `tacenta-model/Properties/` are deliberately
absent from this ledger; `LIMITATIONS.md` ("Forward secrecy is proved, against a
symbolic attacker") says how little they cover.

- `Tacenta.UnitTripleT3.ratchet_agrees_for`: the classical bundle holds at the
  abstraction `UnitT3.StateR` determines, from `UnitT3.lean`'s refinements under
  their boundary, with `OptionCloneTotal` for `clone`.
- `Tacenta.UnitTripleT3.spqr_agrees_for`: likewise for the sparse bundle, from
  `UnitSpqrT3.lean`'s refinements and a refinement of the sparse initialiser this
  file proves.
- `Tacenta.UnitTripleT3.send_refines_discharged`: the composed `send` refines
  `Model.Triple.send`, as the bundle-taking `send_refines` states it, with both
  bundles discharged. It assumes the receive path's boundary as well, because each bundle
  covers its ratchet's whole calling surface.
- `Tacenta.UnitTripleT3.receive_refines_discharged`: likewise for `receive`.

Each of these four is pinned in `UnitPins.lean`.

The two discharged theorems state what the bundle-taking theorems in the same
file state, and those are claimed as well. They carry two scopings worth reading
literally.

- `Tacenta.UnitTripleT3.send_refines`: the composed `send` refines
  `Model.Triple.send`, given the two bundles. It states the success case and a
  failure case, and the failure case is not symmetric: it holds for every
  post-quantum error and, on the classical side, only for `NoSendingChain`,
  because `T3.lean`'s own `send_refines` proves the model-failure correspondence
  for that error and no other -- `ChainExhausted`, the real `u32` send counter
  wrapping, has no counterpart in a model that counts in `Nat`.
- `Tacenta.UnitTripleT3.receive_refines`: likewise for `receive`, success case
  only, because `T3.lean`'s `receive_refines` carries no failure-branch fact to
  compose one from.
- `Tacenta.UnitTripleT3.commit_refines`: a bare projection on both sides.
  Kernel-only.
- `Tacenta.UnitTripleT3.split_secret_refines` and
  `Tacenta.UnitTripleT3.combine_refines`: proved outright against
  `Model.TripleRatchet.splitSecret`/`combine`, from the HKDF agreement and, for
  `split_secret`, the sixty-four-byte `zeroize` round trip, which on the unit are
  the classical ratchet's own `HkdfAgrees` and `ZeroizingRoundTrips`. Both are
  compiler-trusted: `combine_refines` carries `combine_info_agrees`'s
  `native_decide` axiom, and `split_secret_refines` carries `split_info_agrees`'s
  and one of its own.

None of these five is pinned; the axiom bases stated for them here and below
were read off `#print axioms` on 2026-09-10.

**What discharging changes in the trust base.** Measured on 2026-09-10 against
the standalone `TripleT3.send_refines`, before its deletion, the sixteen opaque
inner-crate declarations it rested on are absent, but that is the unit
translation's doing: `UnitTripleT3.send_refines`, with the bundles still as
hypotheses, already rests on none of them. What discharging the bundles adds at
the axiom level is exactly the eight `native_decide` compiler-trust axioms
`UnitSpqrT3.lean` carries, from its `chain_label_agrees`, `chain_start_agrees`,
`max_skip_agrees`, `max_skip_val`, `max_skipped_store_agrees`,
`protocol_info_agrees`, `receive_refines_continuation` and `root_label_agrees`.
The same holds for `receive`.

**What the two discharged theorems assume**, beyond the numeric preconditions
the bundle-taking theorems carry: `UnitT3.HmacAgrees`, `UnitT3.HkdfAgrees`,
`UnitT3.ZeroizingRoundTrips`, `UnitT1.VecRemoveTotal`, an instance of
`UnitT1.DerivedKeysModel`, `UnitSpqrT3.ZeroizingRoundTrips96` and
`ZeroizingRoundTrips64`, `UnitSpqrT3.VecRetainAgrees`, `VecAppendAgrees` and
`VecRemoveAgrees`, `UnitSpqrT1.ZeroizeTotal` and `UnitSpqrT1.OptionCloneTotal`.
`UnitSatisfiabilityTriple.lean` witnesses all twelve, jointly where two constrain
the same constant, and applies both theorems to exactly those hypotheses, so a
boundary hypothesis added ahead of the state relation stops it building.

## Proved (tier T3, the translated code refines the model)

Location: `tacenta-proofs/translation/Translation/SessionT3.lean`,
`tacenta-proofs/translation/Translation/ErasureT3.lean` and
`tacenta-proofs/translation/Translation/ProtobufT3.lean`.

- `shared_secret_refines_some`: the translated PQXDH derivation computes what
  the model says, modulo a stated agreement between the axiomatised HKDF and the
  model's.
- `mul_refines`: multiplication in the translated erasure crate's field computes
  what `Model.Gf65536` says, for every input rather than at the thirty-eight
  points the conformance vectors sample. It rests on one `bv_decide` reflection
  beyond the kernel's axioms.

  **The field only.** `interpolate`, the chunk helpers, and both entry points of
  the encoder and decoder have T1 and no refinement, so `Model.Polynomial`'s
  recovery theorems remain statements about a Lean definition rather than about
  the code that ships.

- `tag_refines`: reading a protobuf tag from attacker-chosen bytes -- the field
  number and wire type that select what a message means -- computes what
  `Model.Protobuf` says, for every byte string rather than for the fixtures.
  Composed from `varint_refines` and `decode_tag_refines`, and it rests on
  nothing beyond `propext`, `Classical.choice` and `Quot.sound`: no
  `native_decide`, no `bv_decide`, no opaque translated operation.

- `length_delimited_refines`: reading a length-delimited field agrees with
  `Model.Protobuf.lengthDelimited`, including on refusal, for every byte string
  and every attacker-chosen length. Same axiom base.

- `admit_refines`: the message-level field set agrees with
  `Model.Protobuf.admit`, including on both refusals -- a repeated field number
  and more fields than the profile carries. Same axiom base. This is where
  `MAX_FIELDS` is read and `ProtoError::Duplicate` is constructed, so both
  bounds exist as checked behaviour and not only as source text.

  This is `byte`, `varint`, `decode_tag`, `tag`, `length_delimited` and
  `admit`.

- `one_field_refines`: the ratchet profile's per-field step, proved against
  `Model.Protobuf.oneField`, including that a refused field leaves the code
  and the model refusing together.

- `parse_ratchet_body_loop_refines`, `parse_ratchet_body_refines`: the whole
  ratchet message. `parse_ratchet_body` computes what
  `Model.Protobuf.parseRatchetBody` says -- the length bound, the five-field
  loop over `one_field`, leftover bytes after it, and each of the five
  missing-field refusals -- on the accepted message and on every refusal, not
  merely that it cannot fail.

- `oneEnvelopeField_refines`, `parse_prekey_body_loop_refines`,
  `parse_prekey_body_refines`: the whole prekey envelope, the other half of
  item 5. `parse_prekey_body` computes what `Model.Protobuf.parsePrekeyBody`
  says -- the length bound, the eight-field loop over `one_envelope_field`,
  leftover bytes (an envelope has no trailing authenticator, so the protobuf
  region runs to the end and this checks the same way the ratchet message's
  does), and each of the seven missing-field refusals. `prekeyId`, the only
  optional field in either message type, is excluded from that check on both
  sides: the supported profile makes the one-time-prekey field optional, and
  requiring it would refuse a message allowed by that profile. Item 5 of the
  verified-core contract is closed for both message types.

  No boundary assumption anywhere in either message's proof, unlike every
  other T3 effort in this project -- the crate has no opaque primitive of its
  own to assume agreement at. **All nine are pinned** with `#print axioms`
  under `#guard_msgs` (`tag_refines`, `length_delimited_refines`,
  `admit_refines`, `one_field_refines`, `parse_ratchet_body_loop_refines`,
  `parse_ratchet_body_refines`, `oneEnvelopeField_refines`,
  `parse_prekey_body_loop_refines`, `parse_prekey_body_refines`) and rest on
  nothing beyond `propext`, `Classical.choice`, `Quot.sound`, so the sentence
  before this one is a build fact rather than an expectation.

  **Not the same as an end-to-end claim from wire bytes to a ratchet
  decision.** `tacenta-protobuf` is still called only by its own crate and by
  interoperability tests that are not part of this public tree; nothing
  in the live `Session`
  send/receive path calls into it yet, which still uses the older fixed-width
  `tacenta_core::serialization` format. The decoders a peer's bytes actually
  reach, `decode_message`, `decode_composite` and `decode_initial`, and the
  bundle decoder `decode_bundle`, are translated and proved (see the
  `tacenta-wire` sections). These proofs are what
  such a claim would need on the protobuf parsing side, not the claim itself.

  **Still not proved.** Canonical emission and raw-byte fidelity -- items 6
  and 7 of the verified-core contract.

## Proved (tier T3, the ML-KEM Braid's translated code refines the model)

Location: `tacenta-proofs/translation/Translation/BraidT3.lean`.

**Every boundary hypothesis here is bounded to what a real erasure code and
KEM can satisfy, and the build checks that the bounds are load-bearing.**
`Translation/Satisfiability.lean` refutes, against copies of them, the
unbounded shapes each hypothesis would otherwise take, so none can be
restated without its bound:

- The erasure agreement, `ErasureAgrees`, demands the encoder simulation
  for only as many steps as a `u16` chunk index allows. Demanded for *every*
  number of steps it would be refutable outright, and it is a conjunct of
  `StateRefines` for every state holding an encoder.
- The decoder simulation, `DecoderSim`, is parameterised by the one message
  the decoder is collecting. Quantified over every model chunk sharing a
  real chunk's index (model chunks carry the message they encode) it would be
  refutable jointly with `DecoderAddChunkTotal` and `DecoderMessageTotal`,
  the receive theorems' exact hypothesis set, since the real decoder's
  `message` is total and gives one answer.
- `KemAgreesFor K` and `ValidateEkAgrees K` fix the split of a header into
  `ekSeed ++ hek` at 32 bytes. Quantified over every split they would be
  refutable for every `K` that models a KEM, the model's own `toyKem`
  included (`kemEncaps1_unsplit_toyKem_refutable` and
  `validateEk_unsplit_toyKem_refutable`, both pinned at `toyKem`).
- A completed decode's length is a theorem of the model rather than an
  assumption. Assumed of every decoder it would be false of the model itself
  (a decoder holding one wrong-length chunk would "decode" to it).

What a reader has to grant:

- **The model's `Decoder.message` checks the length** the real decoder can
  only ever produce; the length fact is the theorem
  `Model.Braid.Decoder.message_length`, assumed by nothing.
- **Encoder fuel is bounded, and sending needs a live encoder.**
  `EncoderRefines` holds for as many further steps as the model's position
  leaves under 65,536, and `step_send_refines`/`Braid.send_refines` take
  `EncodersLive model`: the state's encoder, if any, has emitted fewer than
  65,536 codewords. That is the crate's real liveness limit (an epoch whose
  peer never replies exhausts its encoder), a stated precondition rather
  than an assumption made of every encoder.
- **A decoder's chunks belong to one message.** `DecoderSim m` is
  parameterised by the message the decoder is collecting and speaks only
  about real chunks that are codewords of `m` (`CodewordOf`, defined through
  the real encoder). `MsgRefines` says the real chunk is a codeword of
  the model chunk's source, and `step_receive_refines`/`Braid.receive_refines`
  take `HonestChunk model modelMsg`: for the six state/message-type pairs
  in which `Model.Braid.receive` feeds a chunk to a decoder, and only when
  the epochs match, the incoming chunk's source is a message of that
  decoder's size and the decoder holds nothing from another message. It
  says nothing about a chunk the model ignores -- a stale-epoch or
  wrong-type chunk -- so those benign, reachable steps stay inside the
  theorem. **This is the unspliced-stream assumption.**
  A chunk spliced in from a different encoding makes the real decoder
  reconstruct a wrong message the MAC then rejects (`Failed`), while the
  model's decoder returns nothing for mixed sources and keeps waiting; the
  two genuinely differ there, no relation makes that step refine, and the
  theorems say nothing about it (`LIMITATIONS.md`). A Braid message travels
  inside the ratchet's authenticated channel, so splicing needs the channel's
  key, not the network.
- **The header split is fixed at 32 bytes**, where the model itself splits
  (`ekSeed.length = 32` in `KemAgreesFor`'s `encaps1` clause and in
  `ValidateEkAgrees`; carried, with the hash half's 32 bytes, as conjuncts
  of `StateRefines` for the three header-holding states).
- **The KEM agreements are guarded by the lengths the real crate checks**:
  `decapsulate` is assumed to succeed only on a
  `ct1Size`/`ct2Size` pair, `encapsulate1` only on a 64-byte header,
  `encapsulate2` only on an `ekSize` vector, exactly where
  `tacenta_kem` returns `KemError` otherwise, and `validate_ek` is assumed
  to answer the hash comparison only on a 32-byte seed, a 32-byte hash and
  an `ekSize` vector, where libcrux's `validate_pk_bytes` returns `Err`
  (and `validate_ek` `false`) otherwise, before hashing. `StateRefines`
  carries the decoder sizes and decoded lengths that discharge the guards.
  Stated for every slice, the agreements would claim success where the
  crate returns an error -- not refutable, but stronger than the crate; for
  `ValidateEkAgrees`, which demands a definite answer rather than success,
  the unguarded statement was false of the real `validate_ek` for every
  `K` (`LIMITATIONS.md`). The two clauses that draw randomness -- key
  generation and `encapsulate1` -- are further guarded by
  `BraidT1.RngTotal rc`, since the real operations return only if the
  caller's `fill_bytes` does; `step_send_refines` and `Braid.send_refines`
  take it, and `KeyPairGenerateTotal`/`Encapsulate1Total` in `BraidT1.lean`
  carry the same premise.
- **What `validate_ek` covers, and what nothing covers.** The check is
  FIPS 203's `H(ek)`: it recomputes the hash of the *encapsulation* key
  embedded in the header and compares it with the stored hash, so it binds
  the public half to the header and nothing else. **The decapsulation half is
  not verified**, here or anywhere in the tree: roughly half of an ML-KEM
  decapsulation key -- the secret polynomial vector -- has no redundancy in
  the encoding to check it against, so it cannot be validated from the bytes
  alone, and neither `validate_ek`, nor `IncrementalKeyPair::from_bytes`
  (which checks only its input's length), nor `ValidateEkAgrees` says
  anything about it. A stored key pair whose private half has been altered
  passes every check made and fails only at decapsulation.
- **The model's `Decoder.message` returns the empty message for a decoder
  sized for zero bytes**, as the real decoder does; returning `none` there
  would make `ErasureAgrees` false of the crate at size zero (unreachable in
  the Braid, but a hypothesis stronger than the crate). A `Kem` whose
  operations produce outputs of lengths other than its declared sizes --
  possible for an arbitrary `Model.Braid.Kem`, not for `toyKem` or ML-KEM --
  stalls in the model; `KemLenAgrees` and `HonestChunk` keep such a `K` out
  of the theorems, and `LIMITATIONS.md` records the consequence.
- **`ErasureCloneAgrees` says a clone is equal** to its original, rather than
  that it simulates whatever the original did: `EncoderRefines` records
  where an encoder came from, which a behavioural clause cannot transfer.
- **The erasure hypotheses have a model, and the build checks it.**
  `Translation/ErasureWitness.lean` states `BraidT3.lean`'s erasure
  definitions over an arbitrary implementation of the five opaque operations
  (`Api`), proves the concrete `ErasureAgrees` is exactly that shape at the
  real operations (`erasureAgrees_iff`), and exhibits an implementation that
  satisfies it over the concrete 32-byte chunk: a Reed-Solomon code over
  `GF(2^256)`, one field element per chunk, blocks as coefficients, codeword
  `i` the value at the `i`-th point, decoding by Lagrange interpolation
  (`erasure_hypotheses_satisfiable`: `ErasureAgrees`, `ErasureCloneAgrees`
  and `BraidT1.lean`'s seven erasure totals, *jointly*, since satisfiability
  of a hypothesis set is a joint property). Mathlib supplies the field, the
  bijection between 32-byte data and field elements, and the interpolation
  theorem; the module is noncomputable throughout, which a witness may be.
  What it establishes is consistency -- assuming those hypotheses is not
  assuming `False` -- not that the real crate is this code. The Braid's
  `BraidHmacAgrees`/`BraidHkdfAgrees` and `OptionCloneTotal` are witnessed in
  `Translation/Satisfiability.lean`, from the model's own `hmac`/`hkdf`, which
  return exactly the requested lengths, and the identity clone.
- **The KEM hypotheses have a model too.** `Translation/KemWitness.lean`
  does the same for `KemAgreesFor`, `ValidateEkAgrees`, `KemLenAgrees`,
  `KemCloneAgrees` and every `BraidT1.lean` totality and size bound on the
  KEM operations, jointly: one implementation of the opaque calls, over the
  model's own `toyKem`, satisfies all of them at once
  (`kem_hypotheses_satisfiable`), and each concrete hypothesis is the shape
  at the real operations by `Iff.rfl`. Same caveat: consistency, not
  correctness of the real ML-KEM wrapper, which stays assumed. `toyKem`'s
  `encaps1` ignores its randomness argument, which is a legitimate model of
  a clause that asks only that *some* randomness make the model agree; the
  witness picks `0`.

- `step_send_refines`, `Braid.send_refines`: the eleven-state machine's
  sending half, and its entry point, compute what `Model.Braid.send` says --
  the message emitted, the state transitioned to, and the epoch reported --
  for every one of the eleven states' own branches, not just that sending
  cannot fail (`BraidT1.lean`'s claim).
- `step_receive_refines`, `Braid.receive_refines`: the receiving half and its
  entry point compute what `Model.Braid.receive` says, across all twelve
  states and every one of the message-type, epoch, and MAC-outcome branches
  each can take. This is the crate's largest theorem, and the one closest to
  an attacker's own input: every branch it proves is a shape
  of message a remote peer chooses. Both keep the precondition `hepoch`
  (`State.epoch_val _ + 1 < U64.max`) that `BraidT1.lean`'s
  `step_receive_no_panic`/`receive_no_panic` dropped with CR-03, and for a
  reason that is the model's rather than the code's: `Model.Braid` counts
  epochs in `Nat`, so where the real code stops the model's `epoch + 1` keeps
  counting. The premise is a step of headroom rather than the plain ceiling
  bound, because `u64::MAX` is now a **reserved** epoch: transitions (5) and
  (13) refuse the step that would land on it rather than taking it, so at
  `epoch = u64::MAX - 1` the code answers `Failed` and the model advances, and
  the refinement is stated one step below that. `epoch < u64::MAX` is thereby
  a property of every state a run reaches, not only of every state
  `from_bytes` admits -- the transitions keep it and `read_epoch` refuses it
  on the way in, so the ceiling is not constructible by any sequence of
  transitions at all, where before it was constructible in principle by
  2^64 - 1 of them. It is still not a clause of `invariant`, and it is one
  step short of `hepoch` in any case, so `hepoch` stays a hypothesis.
- `Braid.send_refines` and `Braid.receive_refines` are pinned under
  `#guard_msgs` at the end of the file, to the kernel's three axioms and the
  crate's opaque constants; no `native_decide` reaches either.
- **Carried over from T1, new with CR-15:** `ZeroizingArrayRoundTrip`,
  `ArrayZeroizeTotal` and `RangeFullIndexTotal`, `BraidT1.lean`'s own copies
  of the `zeroize` wrapper's round trip, the in-place wipe, and the
  `RangeFull` index, are hypotheses of every theorem that reaches
  `Auth.update` or transitions 5 and 7, `step_send_refines` through
  `Braid.receive_refines`. `Translation/Satisfiability.lean` exhibits a
  model of each.

  **`Braid.receive_refines` matches `Model.Braid.receive`'s next-state epoch
  (`(...).2.2.epoch - 1`), not the model's own leading `Nat`.** The model
  states `receive_reports_le : (receive K st msg).1 ≤ st.epoch`, an
  inequality rather than an equality, and it is not tight: on a MAC-mismatch
  transition the model's leading component preserves the *pre-failure* epoch
  minus one, while `Braid.reported`, the real function `Braid.receive` calls
  to produce the value the caller actually sees, is computed from the
  *post-failure* state, `State::Failed`, whose epoch is a fixed zero. The two
  agree everywhere a state is unchanged or an output is emitted (proved as
  `Model.Braid.receive_output_next_epoch` -- declared in `BraidT3.lean`
  inside `namespace Model.Braid`, so it lives in the Mathlib-dependent
  translation package rather than beside `receive_output_epoch` in
  `tacenta-model`, and is not covered by `TrustedBase`'s pins), and disagree
  exactly on failure with a
  pre-failure epoch above one. Nothing here changes either side: it is a
  record of which of two plausible readings of "the reported epoch" the real
  code implements, since the model states only the weaker of the two.

- `finish_encaps_refines`, `mac_eq_agrees`, `Model.Braid.receive_output_next_epoch`:
  proved outright rather than assumed, since `finish_encaps` and `mac_eq` are
  fully translated Rust (no opaque call in the ones that matter for value,
  only in the KEM/erasure primitives they call), and the epoch fact is a
  finite case split over the model alone.
- **The KEM boundary, `KemAgreesFor`:** one bundled existential -- a
  `Model.Braid.Kem` witness satisfying `Kem.Correct`, whose fields the real
  `IncrementalKeyPair`/`EncapsState` operations equal -- rather than one axiom
  per KEM operation, since the model's own `Kem` record is itself
  uninterpreted functions with no separate reference computation to equate a
  per-op axiom against. Two clauses, for the two operations that draw
  randomness (`generate`, `encapsulate1`), each binding the model's
  randomness existentially per RNG state and each under `RngTotal rc`; the
  encapsulation clause used to fix one `(ct1, ss)` per header across every
  RNG state, which only a derandomised KEM satisfies, and
  `Model.Braid.Kem.encaps1` now takes the randomness that makes the
  existential meaningful. A third clause, over every `IncrementalKeyPair`
  whether or not `generate` built it, was false of `from_bytes`-built pairs
  and applied by no proof, and is gone (`LIMITATIONS.md`'s KEM entry has the
  record).
- **The erasure boundary, `ErasureAgrees`:** one freestanding relational
  invariant over `tacenta_erasure`'s `Encoder`/`Decoder`, in the same trust
  category as the ratchet's `HmacAgrees`/`HkdfAgrees` -- an assumed agreement
  at an opaque boundary, not a proof chained through the erasure crate's own
  T1/T3 (a scope choice recorded in the file's own header, revisitable if the
  assumption ever needs to bear more weight than it does here).
- **A completed decode's length:** exactly as long as the decoder was sized
  for. This is a theorem and not an assumption: the model's `Decoder.message`
  checks the length, as the real decoder does, and the statement is
  `Model.Braid.Decoder.message_length`. (Assumed of *every* decoder over a
  bare definition that did not check, it would be false, since such a
  definition lets a decoder holding one wrong-length chunk "decode".) It is
  what lets `EkSentCt1Received`'s
  and `NoHeaderReceived`'s own real length guard -- returning `Failed` when
  the decoded length is not the expected one, dead in any reachable run --
  line up with the model.
- **The four size constants and `validate_ek`, `KemLenAgrees` and
  `ValidateEkAgrees`:** the four `tacenta_kem` size constants
  (`HEADER_LEN`/`EK_VECTOR_LEN`/`CT1_LEN`/`CT2_LEN`) equal the model's own
  `headerSize`/`K.ekSize`/`K.ct1Size`/`K.ct2Size`, and `validate_ek` agrees
  with `K.hashEk` -- four more opaque-boundary assumptions, distinct from
  `BraidT1.lean`'s bound-only copies of the same constants.

## Proved (tier T3, the sparse post-quantum ratchet's translated code refines the model)

Location: `tacenta-proofs/translation/Translation/SpqrT3.lean`.

- `send_refines`, `receive_refines`: the crate's two entry points compute what
  `Model.SparseRatchet.send`/`receive` say -- the key returned, the output
  reported, and the state transitioned to -- across every branch each can
  take, not merely that they cannot fail (`SpqrT1.lean`'s claim). `receive` is
  the larger of the two: the epoch lookup, the skipped-key walk, and the
  forward-derivation count are all attacker-influenced, and every branch
  proved is a shape of message a remote peer chooses.
- `kdf_init_refines`, `kdf_rk_refines`, `kdf_ck_refines`, `find_chains_refines`,
  `set_chains_refines`, `clear_old_epochs_refines`, `advance_refines`,
  `maybe_advance_refines`, `try_skipped_refines`, `skip_message_keys_refines`:
  proved outright rather than assumed, since each is translated Rust -- some
  bottoming out in the KDF boundary below, others in `Vec::retain`/`remove`
  instead, none in a boundary this file does not already name.
- **No KEM boundary and no erasure-coding boundary.** Unlike the ML-KEM
  Braid, this crate never computes a shared secret or touches a chunk codec
  -- `Output` arrives as a value from whichever crate produced it. The only
  opaque call this file assumes anything about the *value* of is
  `hkdf_sha256`; `Vec::retain`/`remove`/`append`, `Zeroize`, and
  `Option::clone` are opaque too and each carries its own assumption below.
- **The KDF boundary, `SpqrHkdfAgrees`:** one assumption, stated one level
  below `SpqrT1.lean`'s totality-only `KdfRkTotal`/`KdfCkTotal`, at the
  opaque `hkdf_sha256` call itself -- that when it returns, it returns what
  `Model.Kdf.hkdf` computes -- under RFC 5869's `N.val ≤ 8160`, discharged
  at the 64- and 96-byte literals. Subsumes both of `SpqrT1.lean`'s KDF
  assumptions, so this file states the boundary once rather than twice.
- **`VecRetainAgrees` and `VecRemoveAgrees`:** each states what `retain`/
  `remove` return, not only that they return, and each is strictly stronger
  than its `SpqrT1.lean` namesake, so neither older hypothesis is separately
  assumed here. `VecRemoveAgrees` is stated under the index guard
  `i.val < v.val.length`, where `Vec::remove` returns, and names the removed
  element as `v.val[i.val]` outright, with no `Inhabited` bound and no
  out-of-range value to name.
- **`VecAppendAgrees`:** genuinely new. `SpqrT1.lean` needed only
  `VecAppendTotal`, since nothing there depended on what
  `skip_message_keys`'s concatenation actually produced; this file does.
  **Both are guarded** by `v.length + w.length ≤ Usize.max →`. Stated
  unconditionally they would be refutable in Lean (Aeneas bounds every `Vec`
  by `Usize.max`, so two full vectors have no concatenation), which would
  make `skip_message_keys_refines`, `receive_refines_continuation` and
  `receive_refines` -- and `SpqrT1.lean`'s `skip_message_keys_no_panic` and
  `receive_no_panic` -- provable from `False`. The guard is discharged at
  each call from `hskiproom` and the loop's own length bound, exposed for the
  purpose.
- **Further preconditions on `send_refines`/`receive_refines`:** besides `hepoch`, `hroom`, `hskiproom`, `hone` and `hcounter`, both
  carry `hcb`, `hsb` and `hnewb`: every chain epoch, every skipped-entry epoch,
  and the incoming `Output.key_epoch` must satisfy `+ epochsKept ≤ U64.max`,
  so the retirement arithmetic cannot overflow. These propagate into the
  Triple Ratchet's refinement on the unit, through its sparse bundle. `hepoch` and `hcounter` are the model's
  requirements, not the code's: `SpqrT1.lean`'s `send_no_panic`/
  `receive_no_panic` no longer carry either, every epoch and counter
  increment being a `checked_add` whose `None` arm returns `ChainExhausted`,
  while `Model.SparseRatchet` counts in `Nat` and has nothing for that arm
  to refine against -- the same reason `BraidT3.lean` keeps its `hepoch`.
  `hepoch` is `epoch + 1 < U64.max`, a step of headroom rather than the plain
  ceiling bound: `advance` reserves `u64::MAX` and returns `ChainExhausted`
  rather than opening chains under an epoch its own retention window would
  immediately retire, so the model advances at `epoch = u64::MAX - 1` where
  the code refuses. `u64::MAX - 1` is otherwise a fully usable epoch, so what
  the reservation costs these theorems is one step of lookahead and not a
  state they can no longer speak about.
- **Axiom base:** beyond `propext`, `Classical.choice`, `Quot.sound`, and the
  per-crate opaque-operation axioms, `send_refines` rests on three
  `native_decide` reflection axioms, one per label agreement helper
  (`chain_label_agrees`, `protocol_info_agrees`, `root_label_agrees`), and
  `receive_refines` on seven: those three, the bound helpers
  `max_skip_agrees`, `max_skipped_store_agrees` and `max_skip_val`, and one
  step inside `receive_refines_continuation` (that `(1 : U64)` has value
  one). `LIMITATIONS.md`'s count of `native_decide` uses in this file is one
  higher because it includes `chain_start_agrees`, which neither entry point
  depends on. Both are pinned under `#guard_msgs` at the end of the file with
  exactly these lists.
- **Carried over from T1 unchanged:** `Tacenta.SpqrT1.ZeroizeTotal` and
  `Tacenta.SpqrT1.OptionCloneTotal`, since neither the buffer wipe nor the
  direction clone is ever read back from, only required to complete.
- **Zeroizing round trips:** `ZeroizingRoundTrips96` and
  `ZeroizingRoundTrips64`, one per width the sparse ratchet's key derivation
  wraps (CR-15 put `kdf_init`, `kdf_rk` and `kdf_ck`'s outputs in
  `Zeroizing`, and the translation sees the wrapper's `new` and `deref` as
  opaque). Each says wrapping then dereferencing returns the array that went
  in. `Translation/Satisfiability.lean` exhibits a model of each.
- **Eight assumptions in this file, six new constants and two reused
  outright**, none the same proposition as any other file's assumption of a
  similar shape -- the same per-crate counting rule `SpqrT1.lean` and
  `BraidT1.lean` describe. See `SpqrT3.lean`'s own closing section for the
  full account.

## Proved (model-level, about the specification alone)

Location: `tacenta-model/Model/Protobuf.lean`. These mention no Rust, and they
are what the refinement theorems are *about*.

- `varint_canonical`: **every byte string the decoder accepts is exactly the
  encoding of what it decodes to.** Not a round trip -- `decode (encode v) = v`
  constrains the encoder and says nothing about which byte strings the decoder
  accepts. This says the accepted set is exactly the canonical one, which is
  what an authenticator over exact bytes needs, and it is where the minimality
  rule earns its place: without it one value has two spellings and the theorem
  is false.

  It holds for place values of one or more. At factor zero it is false, which
  the induction forced into the open; every real call starts at one and only
  multiplies.

## Evidence, not proof

Runtime evidence: known-answer and self-consistency checks. These are build
gated but rely on `native_decide`'s compiler trust or on a test runner, not on a
kernel proof.

- Interoperability testing under the research boundary is not part of this
  public tree and is not claimed as evidence here.
- Primitive known-answer values: SHA-256 (NIST), HMAC-SHA256 (RFC 4231),
  HKDF-SHA256 (RFC 5869), in both tacenta-model and tacenta-core.
- Ratchet self-consistency: in-order, out-of-order, and bidirectional agreement,
  in tacenta-model `Model.Ratchet`.
- Model-to-core conformance: the ratchet vectors generated from the model,
  replayed against tacenta-core by the Rust runner in tacenta-test-vectors,
  including on every step the expansion of the message key into the AEAD
  key, the MAC key and the IV.

## Reproduce

`scripts/verify.sh` builds the model-layer proofs (`Proofs/`) on the pinned
toolchain and fails if any proof uses `sorry` or `admit`. **It does not
enter `translation/`.** The T1/T3 gates are `scripts/no-sorry.sh`, which the
public `translation` CI job and the verification workflow both run:
it builds the translation package, and that build covers every module under
`translation/Translation/` whether or not the root imports it
(`scripts/check-translation-coverage.sh` asserts each produced an `.olean`),
including `Translation/Satisfiability.lean` and
`Translation/UnitSatisfiabilityTriple.lean`, which fail if a witnessed
opaque-boundary hypothesis (the `Vec` operations, the `zeroize` wrapper, the
key-derivation agreements, `Option`'s clone and the rest they list) becomes
refutable,
`Translation/ErasureWitness.lean` and `Translation/KemWitness.lean`, which
fail if the Braid's erasure or KEM hypotheses lose their model, and
`Translation/AxiomAudit.lean` and `AxiomAuditTripleUnit.lean`, which walk the
elaborated environment and fail if any hand-written declaration is an
axiom, opaque, unsafe or partial, carries `implemented_by`/`extern`, or is
named into the compiler's `_native`/`_unsafe_rec` namespace outside the
exact shape the compiler produces -- the `native_decide`/`bv_decide` axioms
are accepted only as `<decl>._native.<tactic>.ax_*`, off a declaration in
the same module, stating that a compiled Boolean evaluation returned `true`
(`tacenta-model/Model/AxiomAudit.lean`; the proofs and model packages run
the same audit). The audit also prints every axiom the generated
`Translation.Tacenta*` modules hold in the built environment, and
`no-sorry.sh` fails if that list differs from the per-file sets
`manifests/translation-attestation.json` records, so the record is held to
what the text elaborated to and not only to the text.
`scripts/check-lean-constructs.sh`, the textual second line, strips
comments and strings and refuses those keywords wherever they sit on a
line, in every hand-written module including the package roots and
`Vectors.lean`, and refuses a lakefile that sets any Lean option. It also
refuses every elaboration-time construct (`run_cmd`, `#eval`, `elab`,
`macro`, `syntax`, `initialize`, `addDecl`, any reference to the `Lean`
namespace) outside `Model/AxiomAudit.lean`'s own implementation and the
four `run_cmd Model.AxiomAudit.run` lines, allow-listed by file path and
exact line content: the audit accepts the compiler-trust axioms by shape
and cannot tell a planted one, added by such code with its name assembled
from string literals, from a real one, so the absence of such code is what
excludes it (`LIMITATIONS.md`, "Trusted, not verified").
`scripts/check-audit-reach.sh` fails if any first-party module, generated
ones included, is outside the four audit modules' import closure, since
the audit walks only what its invoking module imports, and fails if the
four do not all run with the same first-party prefixes, since the audit's
waiver for an unmentioned compiler-trust axiom asks whether any first-party
declaration mentions it and only sees the modules in its own environment.
`scripts/check-audit-negatives.sh` plants twelve declarations: one for each
of the seven kinds the audit refuses, one for each condition a compiler-trust
axiom must meet, and one for the shape the waiver accepts. It fails if the
audit calls any of them wrongly. Its own comment carries the matrix of which
case goes red when which rule is deleted, because a test that passes on a
broken rule is worth nothing.
`no-sorry.sh` then replays every first-party module through the kernel
with `leanchecker`, which is the check against a declaration added with
kernel checking turned off.

The translation itself is regenerated only by the private verification
workflow, using the pinned Aeneas release
`nightly-2026.07.22-b1214ca` (commit `b1214ca0a024e8121f41fe2b2ed15e26af02373b`),
whose linux-x86_64 archive `aeneas-linux-x86_64.tar.gz` has SHA-256
`bc26c30daf92679b57c264c630710096bd9d4428e28795fe0638afdb0c2df65f`; that
workflow checks that digest before extracting, and fails if the committed
`Translation/Tacenta*.lean` differ from what that build produces. The digest
is stated here so that a reader reproducing the translation elsewhere can
check they hold the same binaries, not merely the same tag. The release ships
for linux-x86_64 only.

What the public tree can check about the translation is recorded in
`manifests/translation-attestation.json`, written only by
`scripts/attest.py --refresh-translation` immediately after a
`run-aeneas.sh` run: for each generated `Translation/Tacenta*.lean`, its
SHA-256, the `axiom` names it declares, the SHA-256 of the Rust crate it
was generated from, and the SHA-256 of the workspace inputs that shape what
Charon extracts from every crate (the workspace `Cargo.toml` and its
profiles, `Cargo.lock`, `.cargo/`, and the `kdf` and `kem` crates whose
signatures are the opaque externals), with the Aeneas pin. A green
`scripts/attest.py --check` (`scripts/check-generated-files.sh` runs the
translation half of it on its own) establishes exactly this: that every
file named `Translation/Tacenta*.lean` is a module `run-aeneas.sh`
produces, is byte for byte the file recorded at the last generation,
declares exactly the axioms recorded then (the `axiom` keyword read from
the comment-stripped text wherever it sits, compared as a set, so a removed
axiom fails as an added one does), and that the Rust it stands for and the
workspace inputs hash to what they hashed to when it was translated -- as
recorded by whoever ran the toolchain, which `--refresh-translation`
refuses to do for a file the script does not produce. It does not establish
that the toolchain was run on those bytes, or run honestly;
only regenerating with the pinned release and diffing does, which the
private workflow does on every push and which any linux-x86_64 reader can
do by hand (`REPRODUCING.md`). `attest.py --check` also checks the ledger
itself by name: every theorem a claim bullet names must exist, fully
qualified, in the file its section's `Location:` line names, every
`Location:` path must exist, and every pinned theorem must be claimed.
