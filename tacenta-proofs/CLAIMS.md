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
  not a formality, and **nothing in the type system enforces them**.
  `from_bytes` lets an untrusted byte string establish a state violating them,
  which is the sharp reason this distinction matters rather than being
  pedantry.
- **The primitives are opaque.** X25519, ML-KEM, SHA-256, HMAC and the AEAD are
  assumed at the boundary. No proof here says anything about them.
- **Every `Vec`-family boundary hypothesis is guarded, and the build checks
  that each is satisfiable.** `VecAppendTotal`/`VecAppendAgrees` carry a
  length guard (Aeneas's `Vec` has no room for two full vectors),
  `VecRemoveTotal` in both `T1.lean` and `SpqrT1.lean` carries an
  `[Inhabited]` bound (stated for every element type, including the empty
  one, it would imply `False`), and `VecRemoveAgrees` names the out-of-range
  element as `default` under that same bound. A hypothesis that implies
  `False` in Lean turns every theorem taking it into a proof of `False → _`,
  kernel-checked and establishing nothing; the kernel does not flag this, and
  `#print axioms` does not either. The sparse ratchet's `receive_no_panic`
  and `receive_refines`, the classical ratchet's `receive_refines`, and
  everything composed from them in `TripleT1.lean`/`TripleT3.lean` take these
  hypotheses, so `Translation/Satisfiability.lean` exhibits a model of each
  and a refutation of each unguarded shape, and the build fails if any of
  them becomes refutable. The same file witnesses every `zeroize`-wrapper
  hypothesis the sparse ratchet, the Braid and the classical ratchet take
  (`ZeroizingRoundTrips96`/`64`, `ZeroizingArrayRoundTrip`, `T3.lean`'s
  `ZeroizingRoundTrips` and `ZeroizingRoundTrips80`, `T1.DerivedKeysModel`),
  and `Translation/SatisfiabilityTriple.lean` the Triple Ratchet's two
  (`TripleT1.ZeroizingTotal`, `TripleT3.ZeroizingRoundTrips`), which cannot
  share an environment with the rest. A satisfiable hypothesis is still only
  a hypothesis: the `Remove` forms remain stronger than Rust for an
  out-of-range index (`LIMITATIONS.md`).
- **The ML-KEM Braid's T3 theorems carry two preconditions beyond the
  boundary agreements.** `step_send_refines`, `Braid.send_refines`,
  `step_receive_refines` and `Braid.receive_refines` take a live encoder
  (fewer than 65,536 codewords emitted) and an unspliced chunk stream
  (`HonestChunk`), and the erasure and KEM agreements they rest on are
  bounded to what a real erasure code and KEM can satisfy. The section below
  records every hypothesis; `Translation/Satisfiability.lean` refutes the
  unbounded shapes so they cannot be restated, and
  `Translation/ErasureWitness.lean` proves the erasure hypotheses have a
  model (a Reed-Solomon code over `GF(2^256)`, built from Mathlib).
- **A verified zone is not a verified library.** The zone is the ratchet and
  what it calls; orchestration, storage and lifecycle sit outside it.
- **The verified wire parser has no caller.** `tacenta-protobuf` carries T1
  and T3 below, and nothing on the live path calls it: outside its own
  directory it is referenced only by a fuzz target. The bytes a peer actually
  sends are parsed by `decode_message`, `decode_composite` and
  `decode_initial` in the root crate's `serialization` module, which are
  outside the translated surface and have no theorem. A reader who sees T1
  and T3 for a wire parser and concludes that received bytes are parsed by
  proved code would be wrong today; the proofs are what such a claim would
  need on the parsing side, not the claim.
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
  T1 target. `LIMITATIONS.md` says the same where each crate is discussed.
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
  `epoch < U64.max`, which the T1 theorems no longer need (CR-03) and the T3
  section says why the refinement still does. The theorem's signature is the
  authoritative list.

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
  `HkdfAgrees`, `ZeroizingRoundTrips`, `VecRemoveTotal` and
  `DerivedKeysModel` (the T1 section says what it is), the `hone`
  at-most-one hypothesis named in "what is not proved", a store-size
  precondition (`hs`) and room in the expiry clock (`hroom`); it says nothing
  about the failure branches. Pinned base: the kernel's three axioms and
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
  are what covers it outside Lean.
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
- `receive_no_panic`: the translated Double Ratchet receive cannot panic.
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
what T3 does and does not reach in this crate.

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

## Proved (tier T1, the sparse post-quantum ratchet's entry points cannot fail)

Location: `tacenta-proofs/translation/Translation/SpqrT1.lean`.

These three are in the `Tacenta.SpqrT1` namespace -- bare names shared with,
and distinct from, the classical ratchet's own theorems of the same name
above. All three carry stated room preconditions (the epoch table has space
for one or two more entries, an epoch counter and a per-chain message counter
are each below `2^64`, the skipped-key store has room for one more batch);
none is unconditional totality.

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
- Seven opaque-operation assumptions back these theorems (`VecRemoveTotal`,
  `KdfCkTotal`, `ZeroizeTotal`, `VecRetainTotal`, `KdfRkTotal`,
  `OptionCloneTotal`, `VecAppendTotal`), each a per-crate axiom Aeneas could not
  model, none shared with the classical ratchet's own copies of the same
  operations. See `SpqrT1.lean`'s own closing section for why the count is
  seven and not five.

## Proved (tier T1, the ML-KEM Braid's entry points cannot fail)

Location: `tacenta-proofs/translation/Translation/BraidT1.lean`.

- `mac_eq_no_panic`: the constant-time authenticator comparison cannot panic,
  given equal-length inputs -- the crate's only loop.
- `Braid.step_send_no_panic`, `Braid.send_no_panic`: the eleven-state
  machine's sending half, and its entry point, cannot panic.
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
  erasure coder, the KEM, the two KDF calls, this crate's own copy of
  `Option::clone`, and, since CR-15, the `zeroize` crate's three touches
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

## Proved conditionally (tier T1, the Triple Ratchet's composed session send/receive path, on hypotheses no leaf theorem discharges)

**Read the heading literally.** The theorems in this section are checked by
the kernel, but their hypotheses -- unconditional totality of the two
ratchets' calls -- are stronger than what the leaf files prove and are not
provable as stated in the Aeneas model, so nothing here is "proved" in the
sense the sections above use the word. Details below.

Location: `tacenta-proofs/translation/Translation/TripleT1.lean`.

`tacenta-triple` composes the classical Double Ratchet (`tacenta-ratchet`)
and the sparse post-quantum ratchet (`tacenta-spqr`), and since the triple-ratchet integration
it is the crate the session's own `Session::encrypt`/`Session::decrypt`
actually call -- not `tacenta-ratchet` alone, which the theorems above cover.
This file is the only one that says anything about the composition itself.

- `State.send_no_panic`, `State.receive_no_panic`, `State.commit_no_panic`:
  the composed session send and receive path, and the state-commit step
  after it, cannot panic, **given that the two ratchets' calls are total**.
  This crate never touches a vector, a chain, or a counter directly, only the
  two ratchets that do, through their public calling surface, matching on
  whether each call succeeded.

  **The totality it assumes is stronger than what the leaf files prove.**
  `RatchetReceiveTotal`
  and its siblings in `TripleT1.lean` are stated for *every* state, with no
  hypothesis. `T1.lean`'s `receive_no_panic` needs `hs` (the store size plus
  `U32.max` within `Usize.max`); `SpqrT1.lean`'s `send_no_panic` and
  `receive_no_panic` need `hroom`, `hepoch`, `hskiproom` and `hcounter`. So the
  Triple theorems rest on assumptions no leaf theorem discharges, and which
  are not provable as stated in the Aeneas model (a `Vec::push` at
  `Usize.max` fails). `TripleT3.lean` carries the leaf preconditions verbatim
  in its bundles; `TripleT1.lean` does not, and restating its assumptions with
  those preconditions is open work. Until then, read these three theorems as:
  *if* each ratchet call returns, the composition does not panic around it.
- `split_secret_no_panic`, `combine_no_panic`, `State.init_sender_no_panic`,
  `State.init_receiver_no_panic`, and `State`'s clone and small accessors,
  are proved along the way, since `State.send`/`State.receive` call some of
  them and a session has to start somewhere.
- Twenty opaque-operation assumptions back these theorems, seventeen of them
  totality claims about `tacenta_ratchet.State` or `tacenta_spqr.State`
  treated as opaque -- this crate only sees the public calling surface that
  `T1.lean` and `SpqrT1.lean` prove total, under their preconditions, against
  the real definitions, so none of these seventeen is the same proposition as
  either
  file's own theorems even where a name echoes one (`RatchetSendTotal` here
  assumes totality of a call across a crate boundary; `send_no_panic` in
  `T1.lean` proves it from the translated body). This crate's own copies of
  the KDF, `Zeroize` and `Zeroizing`-wrapper axioms (`HkdfSha256Total`,
  `ZeroizeTotal`, `ZeroizingTotal`) round out the count, the same per-crate
  counting rule `SpqrT1.lean` describes
  (`Translation/SatisfiabilityTriple.lean` exhibits a model of
  `ZeroizingTotal`). `ZeroizingTotal` is new with CR-15:
  `split_secret` now wipes its sixty-four-byte expansion on the way out, and
  the wrapper's constructor and projection are opaque to the translation, so
  `split_secret_no_panic` and the two initialisers that call it take it, in
  `T1.lean`'s shape and at that one width.
- **This is the proof that says anything about the composed path.**
  `tacenta-core/src/sessions`, the product code that calls `tacenta-triple`,
  is not translated or proved in its own right, so the claim stops at the
  crate boundary below it, but there is a claim to stop at.

## Proved (tier T3, the Triple Ratchet's composed session refines the model)

Location: `tacenta-proofs/translation/Translation/TripleT3.lean`, against
`Model.Triple` in `tacenta-model/Model/Triple.lean` (the composed state
machine; `tacenta-model/Model/TripleRatchet.lean` carries only
`splitSecret`/`combine` -- see `LIMITATIONS.md` for what each file covers).

**`Model.Triple` is transcribed from the crate it refines.** Its header says
it is written from `tacenta-spec/protocol/triple-ratchet.md` *and* from
`tacenta-core/triple/src/lib.rs`, because the clone-candidate-commit shape
(neither ratchet's step applied without the other's) is an implementation
decision the specification page does not carry. So the theorems below check
the translated crate against a model read off the same crate, which is less
independence than the other tiers have. What they establish is that the
composition does what its own small, spec-derived description says, and that
nothing is weaker than the leaf theorems (the agreement bundles carry the
leaf preconditions verbatim); what they do not bring is a second,
independently written account of the composition.
`tacenta-model/docs/mapping-to-spec.md` records the same. The four security
properties in `tacenta-model/Properties/` are deliberately absent from this
ledger: they are kernel-only theorems over a symbolic algebra whose attacker
holds a single term, and `LIMITATIONS.md` ("Forward secrecy is proved,
against a symbolic attacker") says exactly how little that covers.

- `send_refines`, `receive_refines`: the composed `send`/`receive` compute
  what `Model.Triple.send`/`receive` say, given the two inner ratchets agree
  with their own models (below). `send_refines` states the success case (the
  key returned, the header composed, the state transitioned to) and the
  failure case -- but the failure case is not "either ratchet failing means
  the model also fails" for both sides equally. It holds unconditionally for
  the post-quantum side, and for the classical ratchet only when the
  reported error is `NoSendingChain`. `Translation/T3.lean`'s own
  `send_refines` proves the model-failure correspondence for that one
  classical error and no other, because `ChainExhausted` -- the real `u32`
  send counter wrapping -- has no model counterpart: `Model.Ratchet.send`
  counts in `Nat` and cannot exhaust; `RatchetAgreesFor` below is narrowed
  to match.
  `receive_refines` states the success case only -- `Translation/T3.lean`'s
  own `receive_refines` for the classical ratchet carries no failure-branch
  fact at all, so there is nothing to compose a triple-level failure claim
  from. This is not a new gap this file introduces; it is the same limitation
  the leaf crate's own claim already has, now visible one layer up.
- `commit_refines`: trivial, a bare projection on both sides.
- **The two inner ratchets' own T3 proofs cannot be cited directly, and the
  reason is structural, not a shortcut.** `import Translation.TacentaTriple`
  together with anything that imports either inner crate's own standalone
  translation fails outright: Charon translates each crate separately, and
  `tacenta_ratchet.State`/`tacenta_spqr.State` are each a **bare opaque
  axiom** inside `tacenta-triple`'s own translation (no fields, since Charon
  translating `tacenta-triple` alone has no visibility across the crate
  boundary), where the same names are concrete structures in each crate's
  own standalone translation -- different declarations sharing a name, and
  the auto-generated instances collide if both are imported into one file.
  So `RatchetAgreesFor`/`SpqrAgreesFor` each bundle one existential
  abstraction function (`tacenta_ratchet.State`/`tacenta_spqr.State` to
  `Model.State.State`/`Model.SparseRatchet.State`) under which `clone`, both
  initialisers, the small accessors, `send`, and `receive` all agree with the
  corresponding model function -- the same bundled-existential shape
  `BraidT3.lean`'s `KemAgreesFor` already uses for its KEM boundary, for a
  different reason: a KEM is uninterpreted by design, where here each inner
  ratchet is already fully proven in its own file and unreachable
  from this one by this translation limit, not by design. `RatchetAgreesFor`/
  `SpqrAgreesFor` are not cryptographic trust assumptions the way
  `TripleHkdfAgrees` is -- they hold if and only if `T3.lean`'s/
  `SpqrT3.lean`'s own theorems hold of the real code, which they do, proved
  elsewhere; this file cannot make Lean say so directly, so it says the same
  content again as a fresh, independently-stated hypothesis.
- **The KDF boundary, `TripleHkdfAgrees`, and the wrapper,
  `ZeroizingRoundTrips`:** two assumptions, the only opaque primitives this
  crate calls that are genuinely its own (inside the translated, non-opaque
  `split_secret`/`combine`). `TripleHkdfAgrees` is stated the same way
  `SpqrHkdfAgrees`/`HkdfAgrees` are for the other two crates.
  `ZeroizingRoundTrips` is this crate's copy of `T3.lean`'s hypothesis of the
  same name, at sixty-four bytes and in the same two-conjunct shape (so it
  subsumes `TripleT1.lean`'s `ZeroizingTotal`, `ZeroizingRoundTrips.total`),
  needed since CR-15 wrapped `split_secret`'s expansion in `Zeroizing`:
  refinement needs the value to survive the wrapper, not just the return.
  `Translation/SatisfiabilityTriple.lean` exhibits a model of it.
- `split_secret_refines`, `combine_refines`: proved outright against
  `Model.TripleRatchet.splitSecret`/`combine`, translated Rust bottoming out
  only in the assumed KDF boundary and, for `split_secret`, the wrapper
  round trip.
- **Axiom base:** beyond `propext`, `Classical.choice`, `Quot.sound`, and the
  per-crate opaque-operation axioms named above, `send_refines` and
  `receive_refines` each also rest on one `native_decide` reflection axiom,
  from `combine_info_agrees`'s label/constant-equality check (both call
  `combine`) -- read off `#print axioms` by hand rather than pinned under
  `#guard_msgs`, as is the base of nineteen opaque `tacenta_triple.*`
  declarations each carries. `SpqrT3.lean`'s
  `send_refines`/`receive_refines` carry the analogous label-agreement
  `native_decide` axioms for the same reason; see that section below.

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
  `tacenta_core::serialization` format: `decode_message`, `decode_composite`
  and `decode_initial` in the root crate are the decoders a peer's bytes
  actually reach, they are outside the translated surface, and they have no
  theorem. These proofs are what such a claim would need on the parsing
  side, not the claim itself.

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
  `tacenta_kem` returns `KemError` otherwise. `StateRefines` carries the
  decoder sizes and decoded lengths that discharge the guards. Stated for
  every slice, the agreements would claim success where the crate returns an
  error -- not refutable, but stronger than the crate.
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
  assuming `False` -- not that the real crate is this code. Two boundary
  hypotheses of the Braid theorems have no witness yet: `BraidHmacAgrees`/
  `BraidHkdfAgrees` (satisfiable by the model's own `hmac`/`hkdf`, which
  return exactly the requested lengths) and `OptionCloneTotal`.
- **The KEM hypotheses have a model too.** `Translation/KemWitness.lean`
  does the same for `KemAgreesFor`, `ValidateEkAgrees`, `KemLenAgrees`,
  `KemCloneAgrees` and every `BraidT1.lean` totality and size bound on the
  KEM operations, jointly: one implementation of the opaque calls, over the
  model's own `toyKem`, satisfies all of them at once
  (`kem_hypotheses_satisfiable`), and each concrete hypothesis is the shape
  at the real operations by `Iff.rfl`. Same caveat: consistency, not
  correctness of the real ML-KEM wrapper, which stays assumed.

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
  (`State.epoch_val _ < U64.max`) that `BraidT1.lean`'s
  `step_receive_no_panic`/`receive_no_panic` dropped with CR-03, and for a
  reason that is the model's rather than the code's: `Model.Braid` counts
  epochs in `Nat`, so at the ceiling the real code's `checked_add` answers
  `Failed` where the model's `epoch + 1` keeps counting. The refinement holds
  below the ceiling and says nothing at it; `from_bytes` refuses `u64::MAX`,
  so no state `from_bytes` admits is there, and none is reachable in
  practice (`checked_add` at `u64::MAX - 1` does yield `u64::MAX`, so the
  ceiling is constructible only by 2^64 - 1 transitions).
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
  per-op axiom against.
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
  `Model.Kdf.hkdf` computes. Subsumes both of `SpqrT1.lean`'s KDF
  assumptions, so this file states the boundary once rather than twice.
- **`VecRetainAgrees` and `VecRemoveAgrees`:** each states what `retain`/
  `remove` return, not only that they return, and each is strictly stronger
  than its `SpqrT1.lean` namesake, so neither older hypothesis is separately
  assumed here.
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
  so the retirement arithmetic cannot overflow. These propagate verbatim into
  `TripleT3.lean`'s `SpqrAgreesFor` and so into its
  `send_refines`/`receive_refines`.
- **Axiom base:** beyond `propext`, `Classical.choice`, `Quot.sound`, and the
  per-crate opaque-operation axioms, `send_refines` rests on three
  `native_decide` reflection axioms, one per label agreement helper
  (`chain_label_agrees`, `protocol_info_agrees`, `root_label_agrees`), and
  `receive_refines` on seven: those three, the bound helpers
  `max_skip_agrees`, `max_skipped_store_agrees` and `max_skip_val`, and one
  step inside `receive_refines_continuation` (that `(1 : U64)` has value
  one). `LIMITATIONS.md`'s count of `native_decide` uses in this file is one
  higher because it includes `chain_start_agrees`, which neither entry point
  depends on. Read off `#print axioms` by hand; this file's theorems are not
  yet pinned under `#guard_msgs`.
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
`Translation/SatisfiabilityTriple.lean`, which fail if any `Vec`-family or
`zeroize`-wrapper boundary hypothesis becomes refutable,
`Translation/ErasureWitness.lean` and `Translation/KemWitness.lean`, which
fail if the Braid's erasure or KEM hypotheses lose their model, and
`Translation/AxiomAudit.lean` and `AxiomAuditTriple.lean`, which walk the
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
`Vectors.lean`, and refuses a lakefile that sets any Lean option.
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
