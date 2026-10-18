# Claims

Exactly what is proven, each claim tied to its proof. A claim appears here only
when a machine-checked proof backs it. Runtime evidence is listed separately so
the difference between a proof and a check stays explicit.

## Read this first: what is not proved

Everything below this section is intended to be accurate. `attest.py --check` confirms that each theorem it names exists in the file it names and that each axiom pin is current; this repository records no review, by a reader who did not write the ledger, of whether the statements say what this prose says. A reader who works through it can
still finish with a stronger impression than the sum of its parts supports, so
this section says in one place what is not proved.

- **`Session::encrypt` and `Session::decrypt` are not proved end to end.** They
  are the functions a product actually calls. On the eight-leaf session unit
  their orchestration now has panic-freedom theorems (T1, below), conditional
  on the contract records named in their statements (15 to 45 named hypotheses
  each; together the four records include twelve of the fourteen boundary
  contracts of `LIMITATIONS.md`, and any one record includes three to nine of
  them) and explicit headroom (three of the five, for `decrypt`, `decrypt_ratchet`
  and `establish_responder`, took a record that contained a false hypothesis,
  which has been restated for bounded decoders; the four records follow from an axiom base that one
  interpretation satisfies, under five laws about standard-library and `zeroize` operations, and the headroom records are
  satisfiable in the same sense with the inhabitedness of the opaque types (one of them, the key pair, an assumption) and two further assumptions in the base:
  `Translation/UnitSatisfiabilityRecords.lean`, `Translation/UnitHeadroomSatisfiable.lean`, `Translation/UnitHeadroomInvariant.lean`, `LIMITATIONS.md`,
  `GAP-REGISTER.md`, row `SESSION-CONTRACT-VACUITY`), and a set of
  refinement branch lemmas that each take the leaf outcomes as hypotheses
  (`Translation/UnitLifecycleT3.lean`; apart from the exact full-store adapter and retry
  prerequisites listed below, not accepted as claims here; only the Triple receive
  evidence in `UnitLifecycleInitialDispatch.lean` is derived from a leaf refinement
  that takes no contract record; the Braid receive evidence there takes
  `BraidReceiveContracts`, whose inhabitation is shown only in the sense of `LIMITATIONS.md`; the evidence
  records the accepted-initial decrypt lemmas take are asked of the run alone, and the one they replace is shown
  empty; the dispatch records are not shown satisfiable as a whole;
  see also `GAP-REGISTER.md`, rows `E2E-04`, `SESSION-CONTRACT-VACUITY` and `DISPATCH-EVIDENCE-VACUITY`). No theorem says what the two functions
  return as a whole, on every branch, against the model. For the private `decrypt_ratchet` that `Session::decrypt` runs on a
  ratchet message (and that `establish_responder` also calls), `decrypt_ratchet_refines_complete` relates the generated
  function's output to the model's step on every path of that function for a run that meets its hypotheses. Three fields
  of the contract record it takes are stated at the instances the unit passes to `Array::zeroize` and `Vec::zeroize`;
  that the real functions return there is assumed, not shown (`LIMITATIONS.md`). The paths are the terminal
  guard, a decode refusal, both Diffie-Hellman refusals, every Triple receive refusal the run's bounds admit (they exclude
  the sparse ratchet's `ChainExhausted`, which needs an epoch or a chain counter at `u64::MAX`), among them the refusal of
  a message whose key was already used (`OutOfOrder`), the skip-limit refusal (`TooManySkipped`) and a full store, after
  the eviction retry loop, an authentication refusal and a success. It holds only for a message whose agreement chunk is a
  codeword of one source that fits the receiving decoder; it takes two laws about `Vec::pop` and `Option::as_mut`, assumed
  and not proved of the real functions, from which, with three contract fields, its proof derives the sparse ratchet's two
  agreements about translated functions (`GAP-REGISTER.md`, row `SESSION-SPARSE-AGREEMENTS`); it reads the random source as a function of its
  state, which a source with no state of its own, such as `OsRng`, is not; and it is compiler-trusted (the section "Proved (tier T3, session lifecycle: every Triple receive refusal, and `decrypt_ratchet`
  on every path, on the eight-leaf unit)"). `decrypt_refines_ratchet_frame` carries that result through the public
  `Session::decrypt` on frames that are not initial messages, under the same hypotheses and one scope premise on the input,
  with the same limits; no claimed theorem covers an initial message (the conditional branch lemmas for its refusals in
  `Translation/UnitLifecycleT3.lean`, such as `decrypt_initial_decode_refusal_refines`, are not claims; the section "Proved (tier T3, session lifecycle: the public
  `decrypt` on frames that are not initial messages, on the eight-leaf unit)"). The first form of the `decrypt_ratchet` theorem, `decrypt_ratchet_refines`, left every Triple receive refusal other than a full
  store open, saying for it neither that the model refuses nor why (the section "Proved (tier T3, session lifecycle
  `decrypt_ratchet` with the eviction retry loop, on the eight-leaf unit)"). The decrypt lemmas that take the per-run evidence records cover a
  message only if the agreement chunk it carries is a codeword of one source that fits the decoder it is fed to, whether the
  message is refused or accepted. When the receiving decoder already holds a chunk, a message an attacker sends with an
  altered chunk falls outside them: `decrypt_ratchet` does not look at the chunk before the authentication tag, so such a
  message can reach a refusal that no theorem here describes. Most of the encrypt and decrypt lemmas also take the oracle
  record `OracleOf`. Its KEM, signing and `random32` clauses are shown to hold of the shipped functions, under laws read
  from the source. Its other clauses (DH, AEAD, KEM decapsulation, signature verification, identity validity) and the
  record as a whole are shown satisfiable at the real constants under eleven laws: seven totality assumptions of the
  contract records, the two random-source laws `SignFillsOnce64` and `KemShape`, and two assumptions that the byte views
  of the DH and KEM key types are injective, none of them proved of the shipped functions (a test,
  `tacenta-core/tests/rng_fill_counts.rs`, exercises the seven totality assumptions and the two random-source laws on
  sampled inputs; the two view assumptions are conditions on the caller's views, read from the source only), and only at a byte-stream random source ("Proved (the clauses of `OracleOf` decided jointly ...)"). The four clauses the `decrypt_ratchet` refinements take (`DecryptOracleOf`) follow from four of those laws
  (`DhCodecTotal`, `DhAgreeTotal`, `AeadOpenTotal` and the DH view assumption), without the KEM and signing laws, at the
  same source ("Proved (`DecryptOracleOf` from four laws ...)"). The whole hypothesis set of
  `decrypt_ratchet_refines_complete`, with `Session::invariant`, holds together at one witness built for it, under named
  laws that one interpretation satisfies, with the Braid agreements at the same oracle's KEM model ("Proved (the
  hypotheses of the `decrypt_ratchet` refinement together ...)"); the witness does not carry an agreement chunk, its
  model step is not fixed by the laws, the KEM agreements are fields of the laws, and the laws' models use toy primitives
  (one at the shipped KEM sizes). At a KEM model read off the shipped wrapper, `wrapperKem`, the KEM agreements follow
  from eight laws about the wrapper's opaque functions, assumed and not proved of them ("Proved (a Braid KEM model read off
  the `tacenta_kem` wrapper ...)"). At a second witness, also built for the hypotheses, whose Braid holds a generated key
  pair, the relation at `wrapperKem` fixes the model's vector and header hash to the real key pair's (its key-generation
  and decapsulation parts hold by unfolding that model) and is false at `toyKem`. The shipped code does not produce
  that combination of Triple and Braid states; the invariant admits it. It takes one more assumed law, and its model
  step is not fixed either; a run carrying a chunk there is caller-selected and not a claim ("Proved
  (the hypotheses of the `decrypt_ratchet` refinement at a session whose Braid holds a key pair ...)").
  At a session that `establish_initiator_for` returned, for every input, `Session::invariant` (under two assumed laws about
  X25519 public keys and the KEM ciphertext length) and the four counter ceilings follow from the establishment rather
  than being assumed; the relation to the model session read off it holds by definition at a `KeysUnsampled` Braid, which
  the establishment supplies, and that model session is not shown to be the model's own establishment output. The
  `decrypt_ratchet` refinement and the public `decrypt` for ratchet-type frames apply there, success and refusal alike, and
  their whole premise list holds together in one interpretation. A copy of that session, exported before its first
  `encrypt` and restored after the responder replied, decrypts the reply in an honest run (a test on the seeds it tries,
  `tacenta-core/tests/restored_initiator_receives_reply.rs`, not a proof). That `import` of the bytes `export` writes
  returns that session itself, so that the same refinements apply to the restored copy (given the caller's boundary
  records, chunk relation and draw, as for the session never copied), is proved under nine assumed laws (six of its own, the
  establishment's two and the `Option::eq` law), which hold with the decrypt laws in one interpretation; every session `import` accepts passes `Session::invariant` (no hypothesis), but acceptance does not give
  the counter ceilings, which stay a check on the accepted session, and the relation to a model session is claimed only
  when the restored Braid holds no KEM value, encoder or decoder ("Proved (tier T3, session lifecycle: what an accepted
  `Session::import` gives ...)"). Initial frames, `encrypt` and `establish_responder` are not covered by those two sections ("Proved (tier T3,
  session lifecycle: the invariant, the counter ceilings and the model relation at every successful
  `establish_initiator_for` output ...)"); `establish_responder` has its own.
  For every responder identity, prekey store, initial message and source of randomness, `establish_responder` returns
  a refusal before its inner receive (one of nine named errors, the store and the random source as given), a refusal of
  its inner `decrypt_ratchet` (the store as given), or that receive's success with the store changed only in the two
  one-time pools and, on the last-resort path, by one replay-record append (under the assumed wrapper model
  `DerivedKeysModel`; that the named entry is the one removed is not stated). At the session it builds,
  `Session::invariant` (under `DhPublicValid`, `OptionEqU64Shape`, `DivCeilValue` and a length bound of the decrypt
  contracts) and the four counter ceilings follow from the construction, and the relation to a model session read off the
  code's session holds with the model's initial responder Braid, so the `decrypt_ratchet` refinement applies to the inner
  call, for a frame whose agreement chunk, if any, meets the caller's chunk premises (`IncomingChunkRefines`,
  `HonestChunk`), with a draw left; that model session is not shown to be the model's prepared session. Under the
  contracts and two assumed shapes recorded in `LIMITATIONS.md` (`ResponderSuccessShape`, `ZeroKeyShape`), three
  refusals and an inner refusal are reached at an exhibited store at the real constants; three more are stated for every
  store of a given shape (only `Decode` for every store), of which no value is derivable without the first shape. The
  premise list holds together at an input that reaches the inner receive, with every law and shape in one model
  interpretation.
  No input at which the whole call succeeds is exhibited ("Proved (tier T3, session lifecycle: `establish_responder` over
  every input ...)").
  The oracle that inhabits the record is the code itself read through the byte views (`oracleOfLaws`), so the
  inhabitation shows only that each primitive returns, that its result depends only on the bytes of its arguments, and
  that it reads the random source in the stated order; it ties nothing to X25519, the AEAD, ML-KEM or XEdDSA. The KEM
  success clause is met as well by an oracle that never encapsulates; a guarded record that is not met by it is new, and
  no consumer takes it. One part of what they
  do is proved of the translated code alone, with no contract record, no headroom and no model: what a
  refused call leaves behind, and which fields a successful one writes (the
  section "Proved (what a refused lifecycle call leaves behind, on the translated code)"
  below). What is proved, each
  under the named boundary hypotheses, lies underneath them, in the ratchet, the sparse post-quantum
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
  preconditions -- the classical ratchet's `hs` (whose constant part,
  `MAX_SKIPPED_STORE + MAX_SKIP ≤ usize::MAX`, `Ratchet.store_plus_skip_fits`
  proves at both platform widths) and `hone`; the sparse ratchet's `hroom`, `hskiproom` and `hone`; the
  Braid's `ct1_bounded`. See "Proved: what a decoded state satisfies" for the
  exact statements. What is **not** closed: `T3.receive_refines`'s `hroom`,
  `SpqrT3.receive_refines`'s `hepoch`, `hnewb` and `hcounter`,
  and `BraidT3.step_receive_refines`'s `epoch + 1 < u64::MAX` are not
  consequences of those crates' invariants and are still the caller's (the
  bullet below says why the three counter bounds cannot be). `SpqrT3.receive_refines`'s
  `hcb` and `hsb` follow from the sparse invariant together with `hepoch`
  (`Translation/DecodedStateDischarge.lean`, section "Proved (which numeric premises
  of the refinement theorems a decoded state already gives)"), so the open premises
  of that theorem are those three and not five; `tacenta-triple`,
  `tacenta-erasure`, `tacenta-session` and `tacenta-protobuf` have no such
  theorem; and the subject throughout is a leaf crate's own persistence
  format, not the session layer above it. That layer now has a Phase 0
  translation and, on the eight-leaf session unit, conditional panic-freedom
  theorems for its entry points, all five conditional on records that are inhabited only in the
  sense of `LIMITATIONS.md` (the session lifecycle T1 section), three of them on a record that
  had a false field until it was restated, but no theorem about the import of a stored
  session. Wherever that
  chain does not reach, the sentence in bold still stands unchanged.
- **A decoded state is panic-free unconditionally; it refines the model
  provided the relevant counter has a step of headroom left.** That is the
  one-line shape of what `Translation/ImportInv.lean` gives, and the split is
  not an artefact of how the proofs are written. Each of the three crates
  reserves the top value of the counter it steps -- the classical ratchet's
  clock clamps at `MAX_EVENTS = u32::MAX - 1`, the sparse ratchet's `advance`
  refuses the step to `epoch == u64::MAX`, the Braid's `step_receive` refuses
  the same in transitions (5) and (13) -- so that no state a crate's own
  operations produce is one its own decoder refuses. The three models now
  reserve the same values and refuse the same steps, as the pages state. The
  refinement theorems ask for one step of headroom (`events + 1 < u32::MAX`,
  `epoch + 1 < u64::MAX`); for all three that premise is kept from before
  their models reserved anything, and whether it could now be dropped has not
  been checked. No `invariant()` can supply that step,
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
  operation's own precondition, and the build checks that those that remain
  are satisfiable.** The classical ratchet's `T1.RemoveSkippedAtTotal` and the sparse
  ratchet's `RemoveSkippedAtTotal`/`RemoveSkippedAtAgrees` carry the index guard
  `i.val < v.val.length →`, discharged in each proof from the loop guard the
  source checks first (the guard also removed the
  `[Inhabited]` bound the unguarded statements needed: stated for every
  index and every element type, including the empty one, they would imply
  `False`). **Those hypotheses are about the translated removal helpers, not about an opaque
  `Vec::remove`:** the leaf translations declare no `Vec::remove` and no `Vec::retain`, the helpers
  are a swap loop, a wipe and `Vec::pop`, and the retain scans are explicit loops, so no
  hypothesis about `Vec::remove` or `Vec::retain` remains. What the build checks about the removal and retain hypotheses is in the next
  paragraphs and in "Proved (hypotheses about translated functions in the leaf crates and the
  three-leaf unit, from named laws, and the decoder acceptance witnesses)". Every width-polymorphic HKDF hypothesis carries RFC 5869's `N.val ≤ 8160` (`SessionT3.HkdfAgrees` is fixed at 32 bytes and needs none), the
  bound the crate's `expect` enforces; `DivCeilTotal` carries `b.val ≠ 0`;
  and the KEM's two randomness-drawing totals and clauses carry
  `BraidT1.RngTotal rc`, that the caller's `fill_bytes` returns. A hypothesis
  that implies `False` in Lean turns every theorem taking it into a proof of
  `False → _`, kernel-checked and establishing nothing; the kernel does not
  flag this, and `#print axioms` does not either. These checks cover hypotheses
  about opaque operations. In the eight-leaf session unit the erasure coder is
  translated, and the hypothesis `DecoderMessageTotal` there is a statement about a
  definition, not an opaque operation; nothing in the build checked it until
  `Translation/SessionBraidReceiveVacuity.lean` refuted its unbounded form, which is why it is
  now stated for decoders that need at most `MAX_CODEWORDS` chunks (the session lifecycle T1
  section). `ErasureAgrees` and `ErasureCloneAgrees`, the hypotheses of the session unit's Braid
  refinements about the erasure coder, were in the same position: statements about translated
  definitions. Both are theorems now, `ErasureCloneAgrees` outright and `ErasureAgrees` under two laws about
  `Vec::truncate` and `usize::div_ceil` (the sections on the translated erasure coder and on the Braid agreements). The sparse ratchet's
  `receive_no_panic` and `receive_refines`, the classical ratchet's
  `receive_refines`, and everything composed from them on the three-leaf unit
  take the removal and retain hypotheses, which are of that kind. The witnesses
  `Translation/Satisfiability.lean` keeps for them are retired shapes of a
  `Vec::remove` and a `Vec::retain` that the translations no longer call, or bridges to a shape
  applied to the defined function (void: they say nothing about the body), so they establish
  nothing about the hypotheses as they now stand. That each of them holds follows, under named laws
  about the opaque constants the bodies reach, from the results in the section named above
  (`SatisfiabilityRatchetLaws.lean`, `SatisfiabilitySpqrLaws.lean`, `UnitSatisfiabilityTripleLaws.lean`).
  The same file witnesses every `zeroize`-wrapper hypothesis the sparse ratchet,
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
  `DerivedKeysModel`, `Option`'s clone and
  the general array `ZeroizeTotal`, and the HMAC and HKDF agreements; its pair of removal
  hypotheses is a void bridge, as above. A satisfiable hypothesis is still only
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
  takes a randomness argument, and the encapsulation clause of
  `BraidT3.lean`'s `KemAgreesFor` says that for each RNG state *some* model
  randomness makes `K.encaps1`'s ciphertext and shared secret the real
  `encapsulate1`'s -- the same shape the key-generation clause always had.
  An earlier revision's clause fixed
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
  one for the sending chain -- is applied in `tacenta-core/lifecycle/src`,
  which is translated in the lifecycle leaf but neither modelled nor proved.
  `Model.Ratchet.receive`, the
  refinement theorem and the ratchet vectors all take the two agreement
  outputs as opaque bytes, so a swap in the orchestration would pass every
  proof, every vector and `attest`. The pairing is tested, not proved:
  `a_session_dh_step_pairs_the_old_key_with_the_peers_new_key`
  (`tacenta-core/tests/handshake_to_ratchet.rs`) runs a real `Session` through
  a step. A message sent under the peer's new ratchet key decrypts only if the
  receiving chain was seeded from the old key pair with that key, and the
  test checks that it does and that the sending public key changes at the
  step. It checks the session by running it, not against a model scenario.
- **Translated is not proved.** Every verified-zone crate carries
  persistence codecs and a few accessors that the translation contains and
  no T1 or T3 theorem names: `from_bytes`, `to_bytes`
  and their helpers (`take_len_prefixed`, `decode_state`, `read_auth`,
  `read_key`, `read_u32`, `read_u64`, `decode_skipped_entry`,
  `decode_chain`, `decode_chains_entry`), `init`,
  `init_alice`, `init_bob`, `Output::new`, `Encoder::new`, `Decoder::new`,
  `needed`, `received`, `encode_prekey_body` and the small accessors; the
  `evict_oldest` calls carry a T1 theorem only on the session unit
  (`Translation/UnitLifecycleT1.lean`). (The erasure crate's `weights`, `coefficients` and
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
  named above still has no T1 theorem. The Braid-and-erasure translation
  unit, `tacenta-core/braid-unit`, is translated and audited and carries no
  theorem of any kind yet (`LIMITATIONS.md`). So is the session lifecycle
  leaf, `tacenta-core/lifecycle` (`Translation/TacentaLifecycle.lean`): all
  thirty public operations, `Session::encrypt` and `decrypt` among them, are
  translated and pass the axiom audit, and none has a theorem on this island; the
  theorems about them are on the eight-leaf session unit (the session lifecycle
  T1 section below), where the ratchets, the Braid, the wire codecs and the
  PQXDH derivation are real bodies (`LIMITATIONS.md`, "The lifecycle leaf is a
  tenth translated zone").
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
  signature is the authoritative list. In the complete Session unit, where the
  erasure coder is translated, `step_receive_refines` and `Braid.receive_refines`
  take a third precondition, `State.decoders_bounded`, and their `DecoderMessageTotal` is stated for
  decoders that need at most `MAX_CODEWORDS` chunks (the session lifecycle T1 section).

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
  the stored-key list by at most `upto - nr`, after replacing any entries in
  the re-derived range. The request is accepted only within `maxSkip` on the
  chain and when the resulting total stays within `maxSkippedStore`.
- `skipMessageKeys_store_bounded`: any state a skip returns holds at most
  `maxSkippedStore` keys, given a state already within the bound. This is the
  memory-safety invariant: a per-chain bound alone does not bound the store,
  because every Diffie-Hellman ratchet step starts a fresh chain, so a peer that
  repeatedly ratchets and skips would otherwise grow it without limit.

## Proved (tier T2, model-level security properties against the symbolic attacker)

Location: `tacenta-model/Properties/ForwardSecrecy.lean`,
`tacenta-model/Properties/Secrecy.lean`,
`tacenta-model/Properties/PostCompromise.lean` and
`tacenta-model/Properties/Authentication.lean`, against the attacker defined in
`tacenta-model/Model/Adversary.lean`.

**The attacker is symbolic.** In `Model.Adversary` a key is a term of `Sym`
that records how it was derived: `seed i`, a session's starting secret;
`dhOut i`, an agreement output; `chain ck` and `msg ck`, the next chain key and
the message key of `ck`; and `rootNext rk dh` and `chainOf rk dh`, the root key
and the chain key a root step derives. Two terms are equal only when they were
built the same way. `Knows held k` says the attacker derives `k` from the terms
`held` accepts, by one rule per derivation: it runs a chain forward, reads a
message key off a chain key, and takes a root step only when it knows both the
root key and the agreement output. No rule runs a derivation backwards.

What every theorem in this section rests on, besides its own hypotheses:
- **The fidelity assumption.** Against bytes these hold only if the key
  derivation is one-way and collision-resistant, so that the attacker learns
  nothing except by the rules above. Nothing in this repository proves that.
  `LIMITATIONS.md`, "Forward secrecy is proved, against a symbolic attacker",
  records it, and `tacenta-spec/threat-model/assumptions.md` states it as
  ASM-10.
- **The terms are not related to `Model.State`.** That `Sym`'s constructors
  mirror the model's `kdfCk` and `kdfRk` is by reading, not a theorem. Nothing
  relates `ckAt` below to a chain key a `Model.Ratchet` state holds, so these
  are statements about one chain or one root step, not about a session.
- **The attacker holds one term.** Every statement gives the attacker's
  holdings as `(· = t)` for a single term `t`. None speaks about an attacker
  holding two keys.
- **The classical ratchet only.** No term models the sparse ratchet, the Braid
  or the combination of message keys.
- **Not unforgeability.** No theorem here takes or proves that a ciphertext
  verifying under a key was made by a holder of that key.
  `Properties.Authentication`'s closing note names it as the premise
  authentication rests on.

`ckAt s n` is the chain key after `n` steps of the chain seeded by session `s`
(`seed s`, then `chain` applied `n` times), and `mkAt s n` is `msg (ckAt s n)`;
both are defined in `Properties.ForwardSecrecy`.

- `Properties.ForwardSecrecy.past_message_keys_are_safe`: for `m < n`, an
  attacker holding `ckAt s n` does not know `mkAt s m`.
- `Properties.ForwardSecrecy.past_chain_keys_are_safe`: for `m < n`, an
  attacker holding `ckAt s n` does not know `ckAt s m`.
- `Properties.ForwardSecrecy.future_message_keys_are_exposed`: an attacker
  holding `ckAt s n` knows `mkAt s (n + k)`, for every `k`. The chain's future
  is not protected, and this says so as a theorem.
- `Properties.Secrecy.message_keys_are_independent`: for `n ≠ m`, an attacker
  holding `mkAt s n` does not know `mkAt s m`.
- `Properties.Secrecy.a_message_key_does_not_expose_its_chain`: an attacker
  holding `mkAt s n` does not know `ckAt s m`, for any `m`.
- `Properties.PostCompromise.fresh_agreement_heals`: for any term `rk` and any
  `i` with `rk ≠ dhOut i`, an attacker holding `rk` does not know
  `chainOf rk (dhOut i)`. The hypothesis is that the one term the attacker
  holds is not that agreement output. The model has no private keys, so an
  attacker holding the ratchet private key behind the output is outside it.
- `Properties.PostCompromise.fresh_agreement_heals_the_root`: under the same
  hypothesis, it does not know `rootNext rk (dhOut i)`.
- `Properties.Authentication.ckAt_inj`: `ckAt s n = ckAt t m` implies `s = t`
  and `n = m`. A statement about terms, with no attacker in it.
- `Properties.Authentication.mkAt_inj`: the same for `mkAt`.
- `Properties.Authentication.no_cross_session_chain`: for `s ≠ t`, an attacker
  holding `ckAt s n` does not know `ckAt t m`.
- `Properties.Authentication.no_cross_session_message`: for `s ≠ t`, an attacker
  holding `ckAt s n` does not know `mkAt t m`.

Each is pinned under `#guard_msgs` in `Proofs/TrustedBase.lean`.
`future_message_keys_are_exposed`, the two `Secrecy` theorems and the four
`Authentication` theorems rest on `propext` alone; `past_message_keys_are_safe`,
`past_chain_keys_are_safe` and the two `PostCompromise` theorems on `propext`
and `Quot.sound`. No `native_decide` or `bv_decide` reaches any of them.

## Proved (tier T2, the classical ratchet model's counters and transitions)

Location: `tacenta-model/Properties/StateConsistency.lean`, about
`Model.Ratchet` and `Model.State`. There is no attacker here: each theorem is a
fact about one of the model's transitions. `dhRatchet`, `skipMessageKeys`,
`ageStore` and `trySkipped` are steps `Model.Ratchet.receive` composes; no
theorem in this section is about `receive` itself.

- `Properties.StateConsistency.send_none_iff`: `send st` is `none` exactly
  when `st` has no sending chain or `ns` is at least `u32::MAX`.
- `Properties.StateConsistency.send_advances_ns`: a send that succeeds sets
  `ns` to `ns + 1`.
- `Properties.StateConsistency.send_header_is_pre_state`: its header carries
  the `ns`, `pn` and `dhsPub` of the state before the send.
- `Properties.StateConsistency.send_preserves_the_rest`: it leaves `nr`, `pn`,
  the root key, the receiving chain, the skipped store, both ratchet public
  keys and the clock as they were.
- `Properties.StateConsistency.dhRatchet_resets_counters`: `dhRatchet`, for any
  header, any agreement outputs and any new sending public key, sets `pn` to
  the old `ns`, and `ns` and `nr` to zero.
- `Properties.StateConsistency.dhRatchet_takes_header_key`: under the same
  quantification, it sets `dhrPub` to `some` of the header's key and leaves the
  skipped store and the clock as they were.
- `Properties.StateConsistency.skipMessageKeys_nr_monotone`: a skip that
  succeeds leaves `nr` no lower than it was.
- `Properties.StateConsistency.skipMessageKeys_preserves_sending`: it leaves
  `ns`, the sending chain and `pn` as they were.
- `Properties.StateConsistency.ageStore_counts_one`: given
  `events + 1 < u32::MAX`, `ageStore` sets `events` to `events + 1`.
- `Properties.StateConsistency.ageStore_stays_at_stop`: given
  `events = maxEvents`, which is `u32::MAX - 1`, `ageStore` leaves `events` as
  it was.
- `Properties.StateConsistency.ageStore_preserves_the_rest`: `ageStore` leaves
  `ns`, `nr`, the root key, both chains and `pn` as they were.
- `Properties.StateConsistency.trySkipped_preserves_counters`: taking a stored
  key leaves `ns`, `nr`, both chains and the clock as they were.

All but one are pinned under `#guard_msgs` in `Proofs/TrustedBase.lean`, on
`propext` and `Quot.sound`, except `trySkipped_preserves_counters`, on
`propext` alone. `ageStore_preserves_the_rest` is proved by `rfl`, and
`#print axioms` reported no axiom for it when this was written. It has no pin,
so nothing in the build holds that: the pin shape `attest.py` reads records a
list of axioms.

## Proved (tier T2, the models' skipped-key stores)

Location: `Proofs/KeyErasure.lean` and `Proofs/MemorySafety.lean`, about
`Model.Ratchet` and `Model.State`, and `Proofs/SparseRatchetCorrectness.lean`,
about `Model.SparseRatchet`.

**What leaves the classical store.** Removal from the model's state. Whether
the bytes are overwritten in memory is not in the model, and `LIMITATIONS.md`,
"Secret deletion is partial", covers it.

- `Proofs.KeyErasure.trySkipped_removes_the_entry`: after `trySkipped st h`
  returns a key, no entry of the store it returns matches the header's ratchet
  key and message number.
- `Proofs.KeyErasure.trySkipped_is_once`: so `trySkipped` with the same header,
  on the state the first call returned, is `none`.
- `Proofs.KeyErasure.ageStore_drops_the_expired`: every entry left after
  `ageStore st` has an age below `maxSkippedAge`. The age is the clock after the
  step minus the count stored with the entry, subtracted as `Nat`, so an entry
  whose stored count is ahead of the clock has age zero.
- `Proofs.KeyErasure.ageStore_only_removes`: every entry left after
  `ageStore st` was in `st`'s store.

**How far the classical store grows.** `Proofs.MemorySafety.Step` relates a
state to the state one of five transitions returns: a `skipMessageKeys` that
succeeds, a `trySkipped` that succeeds, `ageStore`, a `send` that succeeds, and
`dhRatchet` with any header, any agreement outputs and any new sending public
key. `Reachable` is any finite
sequence of them. `Model.Ratchet.receive` is not a `Step`, and no theorem here
says that the state it returns is `Reachable` from its input.

- `Proofs.MemorySafety.step_preserves_bound`: a `Step` from a state whose store
  holds at most `maxSkippedStore` keys reaches a state whose store does too.
- `Proofs.MemorySafety.reachable_stays_bounded`: so does every state
  `Reachable` from such a state.
- `Proofs.MemorySafety.a_session_stays_bounded`: every state `Reachable` from
  `initReceiver sk pub labels` holds at most `maxSkippedStore` keys. The start
  is the receiver's initial state; none of these theorems starts from
  `initSender`.

**The sparse ratchet's store.** `skipMessageKeys.deriveInto` is the recursion
`Model.SparseRatchet.skipMessageKeys` uses to derive a skipped batch.
`keyAt ck start i` is defined as the message half of
`kdfCk (chainAfter ck start i) (start + 1 + i)`, where `chainAfter` advances the
chain key `i` times from `ck`. That this is the key an in-order
`Model.SparseRatchet.receive` derives at that offset is true by reading the two
definitions; no theorem relates `keyAt` to `receive`.

- `Proofs.SparseRatchetCorrectness.deriveInto_length`: a batch of `c` steps
  holds exactly `c` keys.
- `Proofs.SparseRatchetCorrectness.deriveInto_num_gt`,
  `Proofs.SparseRatchetCorrectness.deriveInto_num_le`: every key in it is
  numbered above `start` and at most `start + c`.
- `Proofs.SparseRatchetCorrectness.deriveInto_nodup`: no two keys in it share a
  number.
- `Proofs.SparseRatchetCorrectness.deriveInto_get`: for `i < c`, its `i`-th
  entry is numbered `start + 1 + i` and holds `keyAt ck start i`.
- `Proofs.SparseRatchetCorrectness.skipMessageKeys_store_bounded`: a skip that
  succeeds leaves the store holding at most the larger of its previous size
  and `maxSkippedStore`, with no premise on the store it started from. This is
  one skip. None of these theorems carries the bound across the sparse
  ratchet's `send`, `receive` or `advance`, or over a sequence of operations.
- `Proofs.SparseRatchetCorrectness.clearOldEpochs_store_le`: retiring old
  epochs never lengthens the store.
- `Proofs.SparseRatchetCorrectness.trySkipped_store_lt`: taking a stored key
  never lengthens it. Despite the name, the statement is `≤`.
- `Proofs.SparseRatchetCorrectness.skipMessageKeys_preserves_map`: a skip that
  succeeds, on a store in which no two entries share an epoch and a message
  number (`StoreIsMap`), leaves a store of which that is still true.

Each is pinned under `#guard_msgs` in `Proofs/TrustedBase.lean`, on `propext`
and `Quot.sound`, except `ageStore_drops_the_expired`, `ageStore_only_removes`
and `clearOldEpochs_store_le`, on `propext` alone.

## Proved (tier T2, in the model: the sparse ratchet's total bound counts the store a skip leaves)

Location: `Proofs/SparseReplacementBound.lean`, about `Model.SparseRatchet`.

`sparse-pq-ratchet.md`, The store also has a total bound, orders a skip that
steps a chain from its counter `c` to `upto`: refuse above `maxSkip`; delete the
keys stored for the epoch under a number `n` with `c < n ≤ upto`; refuse when
what remains plus `upto - c` passes `maxSkippedStore`; otherwise store the
derived keys after what remains. `Model.SparseRatchet.skipMessageKeys` states
that order, with `skipSurvivors` for what remains. The first two theorems below
are about `skipSurvivors` and take no premises. The others are about that model
definition. Their premises are that the epoch has a chain (`hc`), that its
receiving chain is present (`hr`), that the request steps the chain forward
(`hlo`) and, for the refusal characterisation, that it is within `maxSkip`
(`hhi`). `witness_premises_hold` below states that all four hold for one store.
They say nothing about the Rust, and nothing about a send, a receive or an
advance, or about a sequence of operations.

- `Proofs.SparseReplacementBound.mem_skipSurvivors_iff`: a stored key survives a
  skip from `start` to `upto` on epoch `e` exactly when it was stored and is
  not stored for `e` under a number `n` with `start < n ≤ upto`. The lower end
  is strict and the upper end is included, so a key at the chain's own number
  survives and a key at `upto` does not.
- `Proofs.SparseReplacementBound.skipSurvivors_length_le`: the survivors are no
  more than the store was.
- `Proofs.SparseReplacementBound.skipMessageKeys_refused_iff`: on a chain that
  steps forward within `maxSkip`, a skip is refused exactly when the survivors
  plus `upto - c` pass `maxSkippedStore`. Counted before the deletion the same
  skip is a different question: that is what the witness below separates.
- `Proofs.SparseReplacementBound.skipMessageKeys_leaves_survivors_then_batch`: a
  skip that steps the chain and succeeds leaves the survivors followed by the
  keys it derived, in that order, so the store it leaves holds the survivors
  plus `upto - c` keys, and at most `maxSkippedStore`.
- `Proofs.SparseReplacementBound.skipMessageKeys_keeps_outside_range`,
  `Proofs.SparseReplacementBound.skipMessageKeys_keeps_the_key_at_the_counter`,
  `Proofs.SparseReplacementBound.skipMessageKeys_replaces_the_range`: a stored
  key outside the range, a key of another epoch and a key at or below the
  chain's counter included, is still stored after a skip that steps the chain
  and succeeds; the second says so of the key at the counter itself; and the
  third that no earlier key remains in the range, since every key the skip
  leaves there is one it derived.
- `Proofs.SparseReplacementBound.replacement_accepts_where_the_count_before_the_deletion_refuses`:
  for any root key, chain key, stored key and direction, a store of
  `maxSkippedStore - 1` keys, two of them under numbers a skip from `0` to `2`
  re-derives, is accepted by `skipMessageKeys`, while the count made before the
  deletion, `1999 + 2`, passes the bound. It is a witness, and it is why the
  premises above are not vacuous: no key is evaluated, so it holds for every
  value the keys can take.
- `Proofs.SparseReplacementBound.witness_premises_hold`: for the same store, the
  four premises of `skipMessageKeys_refused_iff` hold together: the epoch has a
  chain, its receiving chain is present, `ch.n < 2` and `2 <= ch.n + maxSkip`.
  So the characterisation is about a set of states that is not empty, and so
  are the shared premises `hc`, `hr` and `hlo` of the other theorems. Their
  further premises (a key stored at the counter, a key left in the range) are
  not witnessed in this file.
- `Proofs.SparseReplacementBound.witness_refused_one_key_further`: the same store
  with a skip from `0` to `4`, which stores four keys, is refused: `1997 + 4`
  passes the bound. With the witness above, both sides of
  `skipMessageKeys_refused_iff` are shown inhabited. The edge itself, a skip to
  `3` that leaves exactly 2,000 keys, is covered by
  `skipMessageKeys_refused_iff` and tested by the vector and the unit test; no
  witness here sits on it.

Each is pinned under `#guard_msgs` in `Proofs/SparseReplacementBound.lean`, on
`propext` and `Quot.sound`, except `skipSurvivors_length_le`, on `propext`
alone, and the three witness theorems, on `propext`, `Classical.choice` and
`Quot.sound`. `attest.py` requires all ten pins (`REQUIRED_PINS`), so deleting
one fails the attestation. The statements of all ten are also pinned with
`#guard_msgs in #check` in the same file, so a change to a premise or a
conclusion fails the build where the proof would still go through. That is held
by the build: no gate yet requires a statement pin to exist, so deleting one and
refreshing the manifests passes `attest.py` and the other gates.

**What reaches the translated code.** `Tacenta.SpqrT3.skip_message_keys_refines`
(tier T3, "the sparse post-quantum ratchet's translated code refines the model")
has the hypotheses it had. Its statement is now two-part: the single-part
statement pinned with the total bound is its first conjunct, unchanged, and the
second, added by the session contract integration, says that a
`SkippedStoreFull` result is the detailed model refusal `skippedStoreFull`. The
model it names changed, so its refusal case is now the count above: when
`skipMessageKeys` refuses, the translated code returns an error and `r.2 = s`,
the state as it was, and when it succeeds the state refines the one the model
returns. The first conjunct's refusal case names no error, and the second speaks
only of a `SkippedStoreFull` result, so whether a full store is refused as
`TooManySkipped` or `SkippedStoreFull` is not in the statement. The order of the
two checks is pinned in one direction only: the second conjunct rules out a
`SkippedStoreFull` result for a request beyond `MAX_SKIP`. A full store refused
as `TooManySkipped` still passes the theorem after a one-token change to its proof. The session evicts only on `SkippedStoreFull`,
and the session proofs take the refusal kind as a hypothesis (`hreason`). The
refusal kind, and the order in the other direction, are tested only, by `tacenta-spqr`'s unit tests and
the differential harness. Its statement is pinned in
`Translation/SparseSkipStatementPin.lean`. No other proof reads the refusal
clause `r.2 = s` of this statement: `receive_refines_continuation` discards it, and
`receive_refines_continuation` and `receive_refines` state their refusals as an
error alone. The clause is held only by that pin's text,
which the build holds and no gate yet requires. Removing the clause from the
theorem and from the pin together passes the build and every gate, and so does
deleting the file and its import, once the manifests are refreshed. The unit
copies are generated from it (`port-unit-proofs.sh`,
`port-session-unit-proofs.sh`). Its hypotheses `hroom` and `hskiproom` are proved for a state
`State::from_bytes` returns ("Proved: what a decoded state satisfies"). Nothing in this change adds a
hypothesis, an axiom or an entry to the trusted base.

**Tested only.** That the Rust source, as distinct from its translation, refuses
and accepts where the model does at the edges: `tacenta-spqr`'s tests
`replacement_keys_make_room_at_the_exact_store_edge` (which also holds the
survivors' order),
`a_sparse_store_refusal_is_atomic_when_replacement_would_still_overflow`,
`a_sparse_store_with_nothing_to_replace_is_held_to_the_absolute_bound`,
`the_purge_range_is_above_the_chain_number_and_up_to_the_target_only` and
`a_skip_to_the_chain_number_stores_nothing_and_checks_nothing`; that the working
copy of a refused skip is erased, by
`a_skip_refused_for_the_total_bound_frees_no_secret` in
`tacenta-core/tests/spqr_erasure_public.rs` (it relies on `Skipped` erasing on
drop, which the translation ignores); the vectors
`replacement-bound-counts-resulting-store` and
`replacement-range-excludes-the-chain-counter` in `sparse-ratchet-state.json`;
and three one-step sequences in the differential harness. They pin the behaviour
of the source; they do not prove it, and none of them runs the translation. The
translation the T3 proof is about was regenerated with a macOS arm64 build of
the pinned release, and a Linux x86_64 regeneration, in an emulated container on 2026-10-03,
reproduced the four changed generated files (`TacentaSpqr.lean`,
`TacentaTripleUnit.lean`, `TacentaSessionUnit.lean` and, for docstring line
numbers only, `TacentaLifecycle.lean`) as committed, with the seven other
generated files and the three assembled unit crates. The rest of the tracked
files pass through the run and equal the committed ones, which shows that the
run changed nothing else. That is one run by the maintainer's tool-assisted
session, not a hosted job and not independent (`REPRODUCING.md`, "Regenerating
the translation on Linux x86_64, by hand"; `GAP-REGISTER.md`,
`HL-R1-SPARSE-TRANSLATION`).

Not proved, and not checked by `State::invariant`: that no operation leaves a
stored key at or past its epoch's receiving counter, and so that the counts
before and after the deletion agree on every state the operations produce. It is
read off the operations.
`no_operation_leaves_a_stored_key_at_or_past_its_chain_counter` runs 40 seeds of
300 randomised steps (sends, epoch openings, in-order and late receives,
duplicates, arbitrary numbers, stale epochs and eviction) and asserts it after
every step. That is a sample, not a proof.

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
  every refusal is `NoSendingChain` or the `u32` counter's exhaustion
  (`ChainExhausted`, at `ns = u32::MAX`), with `Model.Ratchet.sendDetailed`
  refusing for the same reason. **Modulo `HmacAgrees`**; pinned
  base `propext`, `Classical.choice`, `Quot.sound` and the opaque
  `tacenta_kdf.hmac_sha256`.
- `receive_refines`: a successful `receive`, given the two agreement outputs
  and the fresh ratchet key as bytes, returns the key `Model.Ratchet.receive`
  returns and a state still related, across the skipped-key hit, the
  same-chain path and the Diffie-Hellman ratchet path. The model refuses a
  same-chain message numbered below `nr` whose key is not stored, so a
  successful Rust `receive` is never such a message (the Rust returns
  `OutOfOrder` there). Under `HmacAgrees`,
  `HkdfAgrees` (stated under RFC 5869's `N.val ≤ 8160`, discharged at the
  64- and 80-byte literals), `ZeroizingRoundTrips`, `RemoveSkippedAtTotal`
  (stated under `i.val < v.val.length`, discharged from each scan's own loop
  guard) and `DerivedKeysModel` (the T1 section says what it is), the `hone`
  at-most-one hypothesis named in "what is not proved", a store-size
  precondition (`hs`) and a step of room in the expiry clock
  (`hroom : events + 1 < U32.max`, one step below the `u32` ceiling, a premise
  from when `age_store` clamped the clock at `MAX_EVENTS = u32::MAX - 1` and
  the model's clock did not stop; it now stops there too); it says nothing about the failure branches. Pinned base: the kernel's three axioms and
  eleven opaque externals (`hkdf_sha256`, `hmac_sha256`, five declarations of
  the `zeroize` wrapper including `deref_mut`, the array, pair and `Vec`
  `Zeroize` instances, and `Vec::pop`), and no `native_decide`.
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
  on success, under `HmacAgrees`, `RemoveSkippedAtTotal` and `DerivedKeysModel`.
- `try_skipped_refines`: the skipped-key lookup returns the key the model's
  lookup returns and leaves the store the model leaves, and on a miss the
  model misses too, under `RemoveSkippedAtTotal` and `hone`.
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
- `decode_ec_after_encode_ec`: when reading an encoding back succeeds, it gives
  what was encoded. It can refuse: `decode_ec` accepts only a key's canonical
  encoding (session-establishment.md, `DecodeEC`).
- `is_canonical_x25519_spec`: the canonicity check `decode_ec` applies computes
  exactly `canonicalX25519`, which holds when bit 255 is clear and the bytes are
  not the pattern of a value of at least p = 2^255 - 19. The check's value is
  proved, not only that it returns.
- Every function in the session zone is proven panic-free, with the value it
  produces rather than only that it returned.

## Proved (tier T2, wire encoding)

Location: `Proofs/RatchetCorrectness.lean` covers the ratchet; the encoding is in
`Proofs/Serialization.lean`.

- `readBe32_be32`: reading four big-endian bytes inverts writing them, for every
  one of the 2^32 values, discharged by `bv_decide`.
- `decode_encode`: **the round trip.** Decoding an encoded ratchet message --
  the composite header, then the ciphertext (message-format.md) -- returns
  exactly that header and that ciphertext, for every header whose curve key is
  thirty-two bytes and its canonical encoding (`Model.Messages.canonicalKey`,
  message-format.md, Curve public keys) and whose codeword, if present, is a
  full chunk, and for every ciphertext. The canonical-key hypothesis was added
  in 2026-09, when the decoder began refusing any other spelling of the key;
  without it the theorem would be false. It is `decode_encode_composite` read
  at the message's own
  type. Until 2026-09 this theorem was stated about the model's own encoding
  of the Double Ratchet's forty-byte header alone, a format the specification
  does not accept; the model's message functions and this statement now follow
  the composite header. This is the property a round-trip test can only
  sample.

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
- `send_reports`: the epoch a `Send` reports is the one before the state it
  lands in, so it names the last epoch both parties are known to hold rather
  than the one being negotiated. A send whose KEM call refuses lands in
  `Failed`, whose epoch is 0, and reports 0, as the implementation reads the
  report off the candidate state; `send_reports_of_ne_failed` gives the
  state's own epoch less one when the send does not fail.
- `receive_reports`: and the epoch a `Receive` reports is the one before the
  state it lands in, on every branch. A receive that fails lands in `Failed`,
  whose epoch is 0, and reports 0, as mlkem-braid.md's Failure section says.
- `send_epoch`, `send_epoch_of_ne_failed`: a send never raises the epoch, and
  keeps it whenever it does not land in `Failed`. That a KEM refusal on
  transition (1) or (7) lands there, at epoch 0, is the definition of `send`
  rather than a theorem.
- `send_reports_of_ne_failed`: from a state the send does not fail in, the
  report is that state's own epoch less one, by `send_reports` and
  `send_epoch_of_ne_failed`.
- `receive_epoch_lt`: a receive from a state whose epoch is below `u64::MAX`
  (`u64Max`) leaves the Braid below it. A send never raises the epoch
  (`send_epoch`), so no run from such a state reaches `u64::MAX`, the epoch
  session-persistence.md's reader refuses.
- `receive_advance_lt`: a receive that advances the epoch leaves it below
  `u64::MAX`, from any state. Transitions (5) and (13) refuse the step onto it
  and go to `Failed`, as mlkem-braid.md's Failure section says.
- `receive_output_epoch_lt`: an epoch whose key a receive outputs is at most
  `u64::MAX - 2`, so epoch `u64::MAX - 1` is never completed on the side that
  decapsulates, as session-persistence.md's Principles say.
- `receive_ct2Sampled_at_ceiling`: at an epoch whose successor is not below
  `u64::MAX`, `Ct2Sampled` goes to `Failed` on any message, before reading it.
- `receive_ekSentCt1Received_at_ceiling`: at such an epoch,
  `EkSentCt1Received` goes to `Failed` when a `Ct2` codeword at its epoch
  completes `ct2`, before decapsulating. This one is not on the kernel alone:
  `#print axioms` gives `propext`, `Classical.choice` and `Quot.sound`, and it
  is not pinned.

## Proved (tier T2, the field the erasure code is defined over)

Location: `tacenta-model/Model/Gf65536.lean` and
`tacenta-model/Model/Polynomial.lean`.

- `mul_assoc`: the last of the field laws, and the one that rested on about forty
  `bv_decide` certificates until 2026-10-01. Every law of `Model/Gf65536.lean`
  (the additive laws, commutativity, both distributive laws, associativity, the
  identities) is now proved by the kernel. The operations are linear over GF(2),
  so each law reduces to the sixteen single-bit values (`linear_ext_w`), which
  the kernel evaluates, and the exclusive-or arithmetic is settled one bit at a time.
- `mul_inv_cancel`: every nonzero element has an inverse and `inv` returns it,
  for all sixty-five thousand five hundred and thirty-five. This doubles as a
  check on the reduction polynomial: it needs two to have order exactly `size - 1`,
  so a reducible polynomial is refused and so is an irreducible one under which two
  has a smaller order. Proved by the kernel: two has
  multiplicative order exactly `65535` (five closed computations, at `65535` and at
  each of its four maximal divisors), so its powers are all the nonzero elements,
  and each is inverted by raising it to `65534`. Until 2026-10-01 this was
  established by exhaustion through `native_decide`, which trusts the compiler.
- `interp_eq`: the delta property in the form a decoder states it, which is what
  interpolation needs to recover a lost codeword. It rests on the kernel's three
  axioms alone, as does `unisolvence`, which has no pin of its own and is held through the pin on
  `M_recover`.

The three pins above list `propext`, `Classical.choice` and `Quot.sound` and nothing else. They are on the
`attest.py` floor of required pins (with the pin on `Tacenta.ErasureT3.mul_refines`), and `attest.py` no longer
lists any of the three among the pins that may be compiler-trusted, so a compiler-trust axiom under one of them is
refused.

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
  thirty-two bytes and its canonical encoding, and whose codeword, if it has
  one, is a full chunk. `Proofs.Serialization.decodeBundle_encodeBundle` is
  the bundle's round trip, for every bundle whose three curve keys are
  canonical, beside its length hypotheses. Both canonical-key hypotheses came
  with the decoders' refusal of a re-spelled key (message-format.md, Curve
  public keys).

  **This is not the same as the parse being unambiguous.** The theorem quantifies over
  headers and asks about bytes the encoder produced, so it says nothing about
  which byte strings the decoder accepts. Canonicality is the other direction
  and is enforced by construction and by test, not yet by proof.

## Proved (tier T1, the translated code cannot fail)

Location: `tacenta-proofs/translation/Translation/T1.lean` and
`tacenta-proofs/translation/Translation/SessionT1.lean`.

- `kdf_ck_no_panic`: the chain-key step `kdf_ck` cannot panic. Its axiom base is
  pinned in `T1.lean` alongside `send_no_panic` and `receive_no_panic`.
- `Tacenta.T1.is_canonical_x25519_spec`: the canonicity check
  `State::invariant` applies to every curve public key the ratchet state holds
  (session-persistence.md, Stored curve public keys) computes exactly
  `canonicalX25519`: bit 255 clear, and not the pattern of a value of at least
  p = 2^255 - 19. The check's value is proved, not only that it returns,
  because `ImportInv` characterises the invariant by its value. The function
  and these lemmas repeat `tacenta-session`'s (`Translation/SessionT1.lean`)
  and `tacenta-wire`'s, since this crate depends on nothing but the key
  derivation.
- `send_no_panic`: sending on the classical ratchet cannot panic; the
  `ChainExhausted` refusal at the `u32` counter's limit is a returned error,
  not a failure. Pinned with the other two.
- `receive_no_panic`: the translated Double Ratchet receive cannot panic,
  under `HmacTotal`, `HkdfTotal` (stated for every output length within RFC
  5869's `N.val ≤ 8160`, which the crate's `expect` enforces; the two calls
  ask for 64 and 80 bytes), `ZeroizingTotal`, `RemoveSkippedAtTotal` (stated for
  an in-range index, `i.val < v.val.length →`, where the removal helper's
  result is specified; each of the three scans discharges it from its own loop guard)
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
- `Tacenta.SessionUnitSessionT1.shared_secret_no_panic` (in
  `Translation/SessionUnitSessionT1.lean`): the count-checked Session-unit port
  proves the same statement against the complete eight-leaf generated
  namespace.

## Proved (tier T1, the erasure coder's entry points cannot fail)

Location: `Translation/ErasureT1.lean`.

- `next_chunk_no_panic`: the encoder's entry point cannot panic, for every
  encoder state, and it needs no hypothesis at all. Pinned to `propext`,
  `Classical.choice` and `Quot.sound` alone: this crate has no opaque
  primitive of its own.
- `Tacenta.SessionUnitErasureT1.next_chunk_no_panic` (in
  `Translation/SessionUnitErasureT1.lean`): the count-checked Session-unit port
  proves the same encoder statement against the complete eight-leaf generated
  namespace.
- `message_no_panic`: the decoder's entry point -- the one that consumes
  codewords an attacker supplies, with every index and length computed from
  what they sent -- cannot panic, given only that `Vec::truncate` returns
  (`TruncateTotal`, the one library call the translation does not see
  through). Pinned to the three kernel axioms plus that one external.
- `Tacenta.SessionUnitErasureT1.message_no_panic` (in
  `Translation/SessionUnitErasureT1.lean`): the count-checked Session-unit port
  proves the same decoder statement against the complete eight-leaf generated
  namespace.
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
  every later read, the thirty-two key bytes each canonicity check copies
  among them. Same pinned base.
- `decode_bundle_no_panic`: the same for `decode_bundle`, which decodes a
  published prekey bundle. Its one optional field is decided by
  `one_time_prekey_at` (`one_time_prekey_at_no_panic`) over thirty-three bytes
  the decoder has already bounded. Same pinned base.
- `Tacenta.SessionUnitWireT1.decode_composite_no_panic` (in
  `Translation/SessionUnitWireT1.lean`),
  `Tacenta.SessionUnitWireT1.decode_message_no_panic` (in
  `Translation/SessionUnitWireT1.lean`),
  `Tacenta.SessionUnitWireT1.decode_initial_no_panic` (in
  `Translation/SessionUnitWireT1.lean`), and
  `Tacenta.SessionUnitWireT1.decode_bundle_no_panic` (in
  `Translation/SessionUnitWireT1.lean`): the count-checked Session-unit port
  proves the same four totality statements against the complete eight-leaf
  generated namespace. The port changes namespaces only; its script rejects
  any unexpected source shape or replacement count.
- `is_canonical_x25519_spec`: the check `decode_composite`, `decode_initial`
  and `decode_bundle` apply to every curve key they read (message-format.md,
  Curve public keys)
  computes exactly `canonicalX25519`: bit 255 clear, and not the pattern of a
  value of at least p = 2^255 - 19. The check's value is proved, not only that
  it returns, because the refinements below need it. The function and these
  lemmas repeat `tacenta-session`'s (`Translation/SessionT1.lean`), since the
  wire crate has no dependencies.

## Proved (tier T3, the ratchet-message decoder computes what the model says)

Location: `Translation/WireT3.lean`.

Against `Model.CompositeHeader.decode`, the model's decoder for the composite
header, which applies the same "exactly one spelling" rules as the code. Its
`dh` among them: the model refuses a ratchet key whose bytes, read as a
little-endian integer, are not below p (`Model.Messages.canonicalKey`), and
`Model.Messages.canonicalKey_bytes` shows that comparison is the byte pattern
the code checks.

- `decode_composite_refines`: for every byte string, `decode_composite`
  returns `Ok` exactly when the model returns `some`, with the same header
  and the same unread bytes, and `Err` exactly when the model returns `none`.
  No hypothesis. Because the model accepts one spelling of each header, the
  code does too, for every input: the property `tests/canonicality.rs`
  samples, stated in full.
- `decode_message_refines`: the same for `decode_message`, whose ciphertext
  is exactly the bytes the model leaves after the header.
- `Tacenta.SessionUnitWireT3.decode_composite_refines` (in
  `Translation/SessionUnitWireT3.lean`) and
  `Tacenta.SessionUnitWireT3.decode_message_refines` (in
  `Translation/SessionUnitWireT3.lean`): a count-checked namespace-only port
  proves the same two decoder refinements against the complete eight-leaf
  Session translation. The porting script rejects an unexpected source shape
  or replacement count.

Both are pinned to `propext`, `Classical.choice` and `Quot.sound` alone.
The big-endian arithmetic relating the code's `from_be_bytes` to the model's
shifts and ORs is proved on the kernel in the same file; the model's own
round-trip lemmas settle the same identities with `bv_decide`, and neither
theorem depends on them.

**What this does not give.** An end-to-end claim from wire bytes to a ratchet
decision also needs the session's use of the decoded header. That outer
composition is in draft proof work and is not an accepted claim here.

## Proved (tier T3, the initial-message decoder computes what the model says)

Location: `Translation/WireInitialT3.lean`.

Against `Model.Messages.decodeInitial`, which refuses an `identity` or
`ephemeral` whose thirty-two key bytes are not a canonical curve key
(`Model.Messages.canonicalKey`; message-format.md, Initial message), as the
composite header's and the bundle's decoders refuse theirs.

- `decode_initial_refines`: for every byte string, `decode_initial` returns
  `Ok` exactly when the model returns `some`, with the same identity and
  ephemeral keys, KEM ciphertext, three prekey identifiers and trailing ratchet
  message, and `Err` exactly when the model returns `none`. No hypothesis.
  Pinned to `propext`, `Classical.choice` and `Quot.sound` alone. So the code
  refuses a re-spelled key in either position exactly when the model does.
- `Tacenta.SessionUnitWireInitialT3.decode_initial_refines` (in
  `Translation/SessionUnitWireInitialT3.lean`): a count-checked namespace-only
  port proves the same refinement against the complete eight-leaf Session
  translation. The porting script rejects an unexpected source shape or
  replacement count.
- `decodeInitial_cases`: the model's decoder by cases, the lemma the refinement
  rewrites with. Too short, a wrong version or type byte, no room for the two
  keys, an `identity` or `ephemeral` whose first byte is not the `EncodeEC`
  curve byte `0x05`, an `identity` whose key bytes (offsets 3 to 34) or an
  `ephemeral` whose key bytes (offsets 36 to 67) are not a canonical curve key,
  or no room for the ciphertext length is `none`; otherwise the decoded message
  is one expression over fixed offsets and the ciphertext length read at
  offset 68. The code's check meets the model's through
  `WireT3.canonicalKey_at`.

**What this does not give.** The lifecycle draft now imports this result and
relates the detailed model decoder's successful value. The established-session
repeat checks, refusal reasons and inner receive still need their outer
composition before an end-to-end claim is accepted.

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
  rewrites with. Too short for the framing, a wrong version or type byte, too
  short for the fixed prefix, or a KEM prekey length other than 1,568 bytes
  (the ML-KEM-1024 encapsulation-key length) is `none`; otherwise the bundle is
  `some` exactly when the input is as long as the KEM prekey's length says,
  the one-time prekey's field is a valid spelling, and the identity key and
  signed prekey are canonical curve keys.
- `one_time_prekey_at_spec`: the code's decision on the one-time prekey's
  presence byte and thirty-two bytes is the model's `decodeOptionalKey`, which
  refuses a present key that is not canonical.

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
refinement in `SpqrT3.lean` keeps `hepoch`/`hcounter`, as that section
says.

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
  end of the file. Both depend on the three standard axioms and the crate's
  opaque-operation axioms only; the
  one closed numeric fact in `receive_no_panic`'s proof (that `(1 : U64)` has
  value one) is settled by `decide`, not `native_decide`.
- Seven opaque-operation assumptions back these theorems
  (`RemoveSkippedAtTotal`, which describes the custom wipe-before-pop helper
  under `i.val < v.val.length →` and is discharged from the skipped-key
  scan's own loop check; `KdfCkTotal`, `ZeroizeTotal`,
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
  and its entry point cannot panic, under the totality hypotheses they take.
  One of those, `Encapsulate2Total`, was false of the shipped KEM wrapper for an
  encapsulation state restored from a corrupted store on libcrux's portable
  backend until the wrapper's coefficient bound; it now rests on libcrux's
  stated precondition, which the wrapper keeps on the state side, and is
  tested and not proved (`LIMITATIONS.md`, the Session unit's primitive
  contracts). This is the one an attacker's header,
  chunk data, and claimed lengths drive directly, so this is what stands
  between a malformed message and a remote denial of service, for this leaf
  crate. One real precondition travels with these two: `State.ct1_bounded`, a
  concrete size cap on the KEM ciphertext carried across the encapsulation
  exchange. Neither `step_send` nor `step_receive` keeps it alone: `step_send`
  makes a `ct1` with `encapsulate1`, and `step_receive` makes one from the
  `ct1` decoder. This file does not prove it is kept, since that would be a
  claim about the whole state machine rather than a T1 one about a single
  function; `BraidPreserve.lean` proves that every successful step keeps
  `State.sized`, which gives it. The epoch bound they used to carry as well
  (`hepoch`, an epoch counter below `2^64`, the same shape of bound the
  classical ratchet and the sparse ratchet each need above) is no longer a
  hypothesis of either theorem: the two transitions that advance the epoch
  now use `checked_add` and answer `Failed` at the ceiling (CR-03), an
  outcome the theorems prove as a value rather than assume away.
  **The `ct1_bounded` gap is not closed by `tacenta-triple`**, and it is worth
  being exact about why, since the obvious candidate does not apply:
  `tacenta-triple` is proved (T1 and T3, both further down this file), but it
  composes `tacenta-spqr` and `tacenta-ratchet`, not `tacenta-braid`. The Braid
  sits beneath the session alongside the Triple rather than inside it, so the
  Triple's proofs never see the Braid's state and cannot discharge an invariant
  about it. It is closed by the Braid's own results, in the section "Proved
  (the ML-KEM Braid keeps the two premises its receive theorems take)":
  `State.sized`, which gives `ct1_bounded` and adds the clause it needs to be
  closed under the transitions, is kept by every successful step.
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
- `Tacenta.SessionUnitBraidT1.Braid.send_no_panic` (in
  `Translation/SessionUnitBraidT1.lean`): the count-checked port of the send
  entry-point theorem to the complete eight-leaf Session namespace.
- `Tacenta.SessionUnitBraidT1.Braid.receive_no_panic` (in
  `Translation/SessionUnitBraidT1.lean`): the corresponding count-checked
  receive entry-point theorem. It takes one precondition more than the standalone
  theorem, `State.decoders_bounded` (every decoder the state holds needs at most
  `MAX_CODEWORDS` chunks), because in that unit `Decoder::message` is translated and its
  hypothesis `DecoderMessageTotal` is stated for such decoders only; the statement for every
  decoder is false (see the section on the unbounded decoder hypothesis). Like `ct1_bounded`,
  it is implied by `State.sized`, which every successful send and receive keeps (the section
  "Proved (the same preservation theorems on the session unit, with the decoded Braid)"), and
  `Braid::invariant` supplies it for a decoded Braid. In that unit the erasure functions are
  concrete translated code, so the pinned
  axiom lists drop the standalone Braid translation's opaque erasure
  declarations. The port explicitly unregisters three narrower global tactic
  rules from imported leaf proofs; its negative control checks that removing
  that aggregate adaptation makes the proof fail. Its step lemma `Braid.step_receive_no_panic` takes the same extra precondition.

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
For the Braid a preservation theorem exists for the clause set `State.sized`,
which implies `Braid.Inv`. `Braid.Inv` does not imply `State.sized`
(`inv_not_sized`), so the theorem is not about `Braid.Inv`. It is in the
sections "Proved (the ML-KEM Braid keeps the two premises its receive theorems
take)" and "Proved (the same preservation theorems on the session unit, with
the decoded Braid)".

That is worth stating because it decides how the decoder's refusal should be
read. Where a predicate is not maintained by the operations, `from_bytes` can
refuse a state an honest run could produce, and the refusal is a **policy**
rather than a consistency check. The property that makes it a consistency
check -- that no run of the crate produces a state the predicate rejects, so
the values the predicate excludes are values the operations never reach -- is
established by the crates, in the Rust, in the comments beside the counters
concerned and in their import tests, not here. Read it as the property the
crates establish; the Lean side would need a preservation theorem per
operation. For the Braid's `State.sized`, which gives the two receive premises,
that theorem now exists (see above); for the two ratchets it is open work.

**What is not claimed: a step of counter headroom.** The three crates reserve
the top value of the counter each steps, so that no state their operations
produce is one their own decoder refuses; their models reserve the same values,
but the refinements keep the premise from before they did. The refinement
theorems are stated one step below
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

`Inv` mirrors `State::invariant`'s six clauses on the translated state: the
store is at most `MAX_SKIPPED_STORE`, `events` is below `u32::MAX`, no stored
entry's `stored_at` is ahead of `events`, the store is pairwise distinct on
`(dh, n)`, a receiving chain implies a sending chain and a peer key, and every
curve public key the state holds -- `dhs_pub`, `dhr_pub` when present, and
each stored entry's `dh` -- is canonical (`dhs_canonical`, `dhr_canonical`,
`store_canonical`; session-persistence.md, Stored curve public keys). The last
clause was added in 2026-09 with the rule; the invariant's value on it is
`Tacenta.T1.canonicalX25519`, which `Tacenta.T1.is_canonical_x25519_spec` proves
the check computes, and `Ratchet.canonical_eq` restates as an equation.

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
  (the two KDF calls, `Vec::pop`, and the `zeroize` wrapper's constructor,
  projections and `Zeroize` instances). Both are pinned under `#guard_msgs`
  with that list in the pin, so the base cannot widen unnoticed.
- `Ratchet.from_bytes_accepts_witness`: `∃ s, State.from_bytes witnessBytes =
  ok (Ok s)` -- the translated decoder accepts a concrete 185-byte string
  (`witnessBytes`: version byte, four keys with each `Option` tag present,
  four zero counters, the label byte, a zero skipped-key count; every key is
  zero, which is canonical, as the invariant's key clause asks). Axioms:
  `propext`, `Classical.choice`, `Quot.sound`, pinned. The concrete byte
  reads are `decide` on a list literal, so this is kernel work and not
  `native_decide`'s compiler trust.
- `Ratchet.from_bytes_establishes_inv_nonvacuous`: `∃ bytes s,
  State.from_bytes bytes = ok (Ok s) ∧ Inv s` -- so
  `from_bytes_establishes_inv` is **not vacuous**: its premise is
  satisfiable, and a decoder that rejected every buffer would not satisfy
  this. Same three axioms, pinned. This is the discipline
  `Translation/Satisfiability.lean` applies to the leaves' opaque-boundary hypotheses,
  applied to a decoder's premise. The sparse ratchet and the Braid have
  counterparts for the leaf translation in their own modules (`SpqrFromBytesWitness.lean`, 140
  bytes; `BraidFromBytesWitness.lean`, 74 bytes, the `KeysUnsampled` state), and the Braid has one for
  the complete Session unit (`SessionUnitBraidFromBytesWitness.lean`); the session unit's sparse decoder
  has none. They are listed in "Proved (hypotheses about
  translated functions in the leaf crates and the three-leaf unit, from named laws, and
  the decoder acceptance witnesses)". For the Braid states that hold an erasure or KEM
  value (tags 1 to 10) there is no counterpart: their decode runs through the opaque
  erasure and KEM decoders, which no byte string can be shown to satisfy from inside the
  translation, so for those states `from_bytes_establishes_inv` is **not** known to be
  non-vacuous, and the Rust-side round-trip tests
  (`ratchet/tests/audit_import.rs` and its siblings) are the only evidence
  that the decoder accepts anything.

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
  It carries twelve `tacenta_spqr.*` opaque-operation axioms beside Lean's three,
  and no compiler-trust axiom. It used to carry
  `SpqrT1.receive_no_panic._native.native_decide.ax_1_1`, inherited from
  `SpqrT1.receive_no_panic`; since 2026-09-30 the closed numeric fact behind that
  axiom is settled by `decide`. It is pinned under `#guard_msgs`, and no
  statement in `ImportInv.lean` is compiler-trusted.

**What this does not give.** `SpqrT3.receive_refines` also takes `hepoch`,
`hcb`, `hsb`, `hnewb` and `hcounter`. `hcb` and `hsb` are **not** consequences
of the crate's `invariant` alone: a state with `epoch = u64::MAX - 1` and a
chain at that epoch passes `invariant` and fails both `hepoch` and `hcb`. They
are consequences of the invariant together with `hepoch`
(`spqr_receive_premises` in `Translation/DecodedStateDischarge.lean`), so what
stays with the caller is `hepoch`, `hnewb` and `hcounter`. `hepoch` is
on this list because the reserved ceiling moved it there -- it now asks for a
step of headroom, `epoch + 1 < u64::MAX`, and the invariant reaches only
`epoch < u64::MAX` (`Spqr.inv_gives_epoch_room`). There is deliberately no
`decoded_receive_refines` for this crate; `hepoch`, `hnewb` and `hcounter` stay
with the caller.

### `tacenta-braid` -- the clause its theorems need (two in the complete Session unit)

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
- `Tacenta.SessionUnitBraidImportInv.Braid.from_bytes_establishes_inv` (in
  `Translation/SessionUnitBraidImportInv.lean`): the decoded-state invariant
  theorem in the complete Session unit. Its exact pin omits the standalone
  Braid translation's opaque erasure declarations because that code is
  concrete in the aggregate translation. In the unit, `Braid.Inv` has two fields, `ct1_bounded` and
  `decoders_bounded`, and this theorem yields both; the standalone `Inv` has the first only.
- `Tacenta.SessionUnitBraidImportInv.Braid.decoded_receive_no_panic` (in
  `Translation/SessionUnitBraidImportInv.lean`): the aggregate decoded-state
  chain into the Session-unit Braid receive theorem, with its remaining KEM,
  KDF, zeroize and generated-library boundaries pinned exactly. It needs no side
  condition for the decoder bound: `Braid.Inv` carries it.
- `Tacenta.SessionUnitBraidImportInv.Braid.invariant_true_gives_decoders_bounded` (in
  `Translation/SessionUnitBraidImportInv.lean`): a Braid for which the translated
  `Braid::invariant` returns `true` holds only decoders that need at most `MAX_CODEWORDS`
  chunks. Each arm that holds a decoder runs `Decoder::invariant` on it, and
  `invariant_true_needed_le` (below) turns that into the bound. It assumes nothing about an
  opaque operation; its pin lists the constants `Braid::invariant` mentions.

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
storage layer that calls it live in `tacenta-core/lifecycle/src`. Its Phase 0
translation carries no theorem, so nothing here says what a session restored
from disk satisfies.

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
- `Tacenta.UnitT1.is_canonical_x25519_spec`: the classical ratchet's canonicity
  check compiled inside the unit computes exactly `canonicalX25519`, as its
  leaf twin does.
- `Tacenta.UnitT1.send_no_panic`: likewise for the classical ratchet's send.
- `Tacenta.UnitT1.receive_no_panic`: likewise for receive, under exactly the
  hypotheses the leaf theorem takes.
- `Tacenta.UnitSpqrT1.send_no_panic`: likewise for the sparse ratchet's send.
- `Tacenta.UnitSpqrT1.receive_no_panic`: likewise for the sparse ratchet's
  receive.

**What the pins add, which is the reason to have them.** Five of the six are
pinned in `UnitPins.lean` (`is_canonical_x25519_spec` is not), and each base is the leaf theorem's base name for
name, with `tacenta_triple_unit.` in front of every translated axiom and
nothing else changed. That is a statement about the printed lists. A leaf file opens its
crate's namespace, so its pins print a translated axiom without the
crate's own prefix -- `tacenta_kdf.hmac_sha256` for what is fully
`tacenta_ratchet.tacenta_kdf.hmac_sha256` -- and the underlying names
differ by that prefix as well. Nothing appears that the leaf did not assume, nothing the
leaf assumed has quietly become a definition, and no proof that was kernel-only
has become compiler-trusted. None of the five pinned ones carries a compiler-trust
axiom, in the unit as in the leaf.

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
`tacenta-core/lifecycle/src`, the product code that calls `tacenta-triple`, is
translated and has conditional T1 theorems on the eight-leaf session unit, all
conditional on contract records that are inhabited only in the sense of `LIMITATIONS.md` (the session
lifecycle T1 section below), three of them on a record that had a false field until it was restated, and no
refinement theorem, so the
refinement claim stops at the crate boundary below it.

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
session layer in `tacenta-core/lifecycle/src`, which decides how large a
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
`Tacenta.TripleT1.State.receive_no_panic` depended on twelve axioms, none of
them compiler-trusted, as measured on 2026-09-10 with `#print axioms`, before its
deletion; it was never pinned. This file's depends on seventeen, none of them
compiler-trusted. Both halves matter. The standalone theorem had fewer axioms
because it *assumed* the sparse ratchet's receive is total rather than proving it;
this one proves that part and inherits the boundary axioms proving it needs. Six
axioms go and eleven arrive, a substitution rather than a new kind of trust: the
bare operation axioms are replaced by KDF, `zeroize`, `Vec` and `Option` boundary
axioms that other proofs in this tree already carry. `send` is quieter: twelve
axioms before (measured on 2026-09-10) and sixteen after, none of them
compiler-trusted. `Translation/UnitPins.lean` records all of it.

**Two more assumptions, and one trade.** `SpqrInitAliceTotal` and
`SpqrInitBobTotal` bottom out in `tacenta_spqr.kdf_init`, which no leaf proof
covers, so this file declares `KdfInitTotal` in the same shape as
`UnitSpqrT1.KdfRkTotal`. That replaces two opaque-crate-boundary assumptions
with one trusted-KDF assumption of the kind already relied on everywhere else.

**What is still not proved.** The four remaining public functions without a
T1 theorem on this unit -- `State.evict_oldest_classical`,
`State.evict_oldest_post_quantum`, `State.to_bytes` and `State.from_bytes`
(the two eviction functions have one on the eight-leaf session unit,
`Translation/UnitLifecycleT1.lean`, under `RemoveSkippedAtTotal`).
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
- `Tacenta.UnitT3.receive_store_full_refines`: under the same explicit
  boundary and state hypotheses, a concrete `SkippedStoreFull` result fixes
  the detailed model receive result to the corresponding
  `skippedStoreFull` refusal.
- `Tacenta.UnitT3.message_keys_refines`: likewise for the message-key expansion.
- `Tacenta.UnitSpqrT3.send_refines` and `Tacenta.UnitSpqrT3.receive_refines`:
  the sparse ratchet's two refinements, compiled inside the unit, under the
  hypotheses `SpqrT3.send_refines` and `SpqrT3.receive_refines` take.
- `Tacenta.UnitSpqrT3.receive_store_full_refines`: under the sparse receive
  theorem's explicit bounds and boundary hypotheses, a concrete
  `SkippedStoreFull` result fixes the detailed sparse-model receive result to
  the corresponding `skippedStoreFull` refusal.

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
None of the security properties recorded under "Proved (tier T2, model-level
security properties against the symbolic attacker)" is about `Model.Triple`:
they speak about one classical chain or one root step, as terms, and
`LIMITATIONS.md` ("Forward secrecy is proved, against a symbolic attacker")
says how little they cover.

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
- `Tacenta.UnitTripleT3.receive_store_full_refines_discharged`: for the two
  retryable absolute-store refusals only, a concrete Triple receive refusal
  fixes `Model.Triple.receiveDetailed` to the corresponding classical or
  post-quantum `skippedStoreFull` refusal, under the same explicit leaf
  boundaries and counter bounds.

Each of these five is pinned in `UnitPins.lean`.

The success-side send and receive discharged theorems state what the
bundle-taking theorems in the same file state, and those are claimed as well.
The narrow store-full theorem supplies only the named failure correspondence;
it does not turn the success-side receive theorem into a catch-all failure
refinement. They carry two scopings worth reading literally.

- `Tacenta.UnitTripleT3.send_refines`: the composed `send` refines
  `Model.Triple.send`, given the two bundles. It states the success case and,
  for every error, the refusal `sendRefusalOfReal` maps it to, with
  `Model.Triple.sendDetailed` refusing for that reason: each inner ratchet's
  exact refusal, the classical `ChainExhausted` included, because `T3.lean`'s
  and `SpqrT3.lean`'s own `send_refines` now state the detailed refusal for
  every error their send returns.
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
`UnitT3.ZeroizingRoundTrips`, `UnitT1.RemoveSkippedAtTotal`, an instance of
`UnitT1.DerivedKeysModel`, `UnitSpqrT3.ZeroizingRoundTrips96` and
`ZeroizingRoundTrips64`, `UnitSpqrT3.VecRetainAgrees` with `UnitSpqrT1.VecRetainTotal`,
`UnitSpqrT3.RemoveSkippedAtAgrees`, `UnitSpqrT1.ZeroizeTotal` and
`UnitSpqrT1.OptionCloneTotal`.
`UnitSatisfiabilityTriple.lean` witnesses those that are about opaque constants, jointly where two
constrain the same constant, and applies both theorems to exactly those hypotheses, so a
boundary hypothesis added ahead of the state relation stops it building. The four that are about
translated functions (`UnitT1.RemoveSkippedAtTotal`, `UnitSpqrT3.RemoveSkippedAtAgrees`,
`UnitSpqrT3.VecRetainAgrees` and `UnitSpqrT1.VecRetainTotal`) have a void bridge or no witness there; they are shown to follow from
named laws in `UnitSatisfiabilityTripleLaws.lean` (the section "Proved (hypotheses about translated
functions in the leaf crates and the three-leaf unit, from named laws, and the decoder acceptance
witnesses)").

## Proved (tier T3, the translated code refines the model)

Location: `tacenta-proofs/translation/Translation/SessionT3.lean`,
`tacenta-proofs/translation/Translation/ErasureT3.lean` and
`tacenta-proofs/translation/Translation/ProtobufT3.lean`.

- `shared_secret_refines_some`: the translated PQXDH derivation computes what
  the model says, modulo a stated agreement between the axiomatised HKDF and the
  model's.
- `mul_refines`: multiplication in the translated erasure crate's field computes
  what `Model.Gf65536` says, for every input rather than at the thirty-eight
  points the conformance vectors sample. It rests on the kernel's three axioms
  alone; until 2026-10-01 it rested on one `bv_decide` reflection, in
  `clmulUpto_sixteen`, which is now two spellings of the same exclusive or.

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
  decision.** Outside its own crate, `tacenta-protobuf` is referenced in this
  tree only by a fuzz target, and nothing on the live `Session` send/receive
  path calls it: that path parses a peer's bytes in the fixed-width format
  message-format.md specifies, not in this profile. The
  decoders a peer's bytes actually
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
  `message` returns, for every decoder the crate builds, and gives one answer.
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
  anything about it. The Braid's reader applies `validate_ek` to a stored
  key pair's own header and `ek_vector` (`Braid::invariant`, register item
  J-4), so a stored pair's public half is checked at import; its private
  half still is not. A stored key pair whose private half has been altered
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
  `step_receive_no_panic`/`receive_no_panic` dropped with CR-03. It was kept
  for a reason that was the model's rather than the code's: `Model.Braid`
  counted epochs in `Nat`, so where the real code stopped the model's
  `epoch + 1` kept counting. The model now stops there too
  (`Model.Braid.u64Max`), and the proofs still use `hepoch` to rule out the
  refusing arms rather than relating them; whether the two theorems hold
  without it has not been checked. The premise is a step of headroom rather
  than the plain ceiling bound, because `u64::MAX` is a **reserved** epoch:
  transitions (5) and (13) refuse the step that would land on it rather than
  taking it, so at `epoch = u64::MAX - 1` the code and the model both answer
  `Failed`, and the refinement is stated one step below that. `epoch < u64::MAX` is thereby
  a property of every state a run reaches, not only of every state
  `from_bytes` admits -- the transitions keep it and `read_epoch` refuses it
  on the way in, so the ceiling is not constructible by any sequence of
  transitions at all, where before it was constructible in principle by
  2^64 - 1 of them. It is still not a clause of `invariant`, and it is one
  step short of `hepoch` in any case, so `hepoch` stays a hypothesis.
- `Braid.send_refines` and `Braid.receive_refines` are pinned under
  `#guard_msgs` at the end of the file, to the kernel's three axioms and the
  crate's opaque constants; no `native_decide` reaches either.
- `Tacenta.SessionUnitBraidT3.Braid.send_refines` (in
  `Translation/SessionUnitBraidT3.lean`): the count-checked Session-unit port
  proves the same send refinement against the complete eight-leaf generated
  namespace.
- `Tacenta.SessionUnitBraidT3.Braid.receive_refines` (in
  `Translation/SessionUnitBraidT3.lean`): the corresponding receive
  refinement. Like the receive entry-point theorem of the same unit it takes the
  precondition `State.decoders_bounded`, and its `DecoderMessageTotal` is stated for decoders
  that need at most `MAX_CODEWORDS` chunks. Both aggregate theorems use the concrete translated erasure
  implementation, so their pinned axiom lists omit the standalone Braid
  translation's opaque erasure declarations. In the session unit, `ErasureAgrees` and
  `ErasureCloneAgrees` are statements about the translated erasure code and no longer about opaque
  operations. The model of `Translation/ErasureWitness.lean` is a model of the standalone
  declarations and does not cover them. They are theorems of the unit now (`ErasureCloneAgrees` outright,
  `ErasureAgrees` under two laws; the sections on the translated erasure coder and on the Braid agreements), and
  they are not among the records of `SESSION-CONTRACT-VACUITY`.
- **Carried over from T1, new with CR-15:** `ZeroizingArrayRoundTrip`,
  `ArrayZeroizeTotal` and `RangeFullIndexTotal`, `BraidT1.lean`'s own copies
  of the `zeroize` wrapper's round trip, the in-place wipe, and the
  `RangeFull` index, are hypotheses of every theorem that reaches
  `Auth.update` or transitions 5 and 7, `step_send_refines` through
  `Braid.receive_refines`. `Translation/Satisfiability.lean` exhibits a
  model of each.

  **`Braid.receive_refines` states the reported epoch as
  `Model.Braid.receive`'s next-state epoch minus one (`(...).2.2.epoch - 1`),
  and that is the model's own leading `Nat`:** `Model.Braid.receive_reports`
  proves the two equal on every branch. They were not equal before 2026-09.
  A failing receive (a MAC mismatch, or an `ek_vector` failing the header
  hash) made the model report the epoch before the one it failed at, while
  `Braid.reported`, which the real `Braid.receive` calls, reads the
  post-failure state, `State::Failed`, whose epoch is a fixed zero. The model
  now reports 0 there, as the specification's Failure section and the code
  do. Where an output is emitted, the real code reports the output's own
  `key_epoch`, and `Model.Braid.receive_output_next_epoch` gives the same
  number. That lemma is declared in `BraidT3.lean` inside
  `namespace Model.Braid`, so it lives in the Mathlib-dependent translation
  package rather than beside `receive_output_epoch` in `tacenta-model`, and
  is not covered by `TrustedBase`'s pins.

- `finish_encaps_refines`, `mac_eq_agrees`, `Model.Braid.receive_output_next_epoch`:
  `mac_eq_agrees` and `Model.Braid.receive_output_next_epoch` take no boundary hypothesis;
  `finish_encaps_refines` takes `BraidHmacAgrees` and `ErasureAgrees`, since `finish_encaps` and `mac_eq`
  are fully translated Rust (no opaque call in the ones that matter for value,
  only in the KEM/erasure primitives they call), and the epoch fact is a
  finite case split over the model alone. Its conclusion is the model's
  `Model.Braid.finishEncaps`, which includes the `Failed` arm: when the real
  `encapsulate2` refuses, the two-sided `EncapsRefines` says the model's
  `encaps2` is `none`, and both sides land in `Failed`. Its length premise is
  over the `some` case only.
- **The KEM agreements are two-sided.** Each clause of `KemAgreesFor`, of
  `KeyPairRefines` and of `EncapsRefines` says the real call and the model
  answer alike: either the real call returns `Ok` and the model `some` of
  the converted bytes, or the real call returns `Err` and the model `none`.
  So the four `Err` arms of the Rust (`generate` and `encapsulate1` in
  `step_send`, `encapsulate2` in `finish_encaps`, `decapsulate` in
  transition (5)) are refined against the model's `Failed` transitions
  (mlkem-braid.md, Failure) rather than excluded by hypothesis, as an earlier
  revision did ("the real `Err` arm never fires"). Nothing in the records
  says the real KEM never refuses: a KEM that refused every call, with a `K`
  that refused every call, satisfies them, which is why the state witnesses
  below take `KemDrawsSucceed`. `KemCloneAgrees` carries the whole `Result`
  of `decapsulate` and `encapsulate2` across a clone, refusals included.
- **The KEM boundary, `KemAgreesFor`:** two relations between a specific
  `Model.Braid.Kem` witness and the real `IncrementalKeyPair`/`EncapsState`
  operations, rather than one axiom per KEM operation, since the model's own
  `Kem` record is itself uninterpreted functions with no separate reference
  computation to equate a per-op axiom against. The two clauses cover the
  operations that draw
  randomness (`generate`, `encapsulate1`), each binding the model's
  randomness existentially per RNG state and each under `RngTotal rc`; the
  encapsulation clause used to fix one `(ct1, ss)` per header across every
  RNG state, which only a derandomised KEM satisfies, and
  `Model.Braid.Kem.encaps1` now takes the randomness that makes the
  existential meaningful. A third clause, over every `IncrementalKeyPair`
  whether or not `generate` built it, was false of `from_bytes`-built pairs
  and applied by no proof, and is gone (`LIMITATIONS.md`'s KEM entry has the
  record). A former `K.Correct` conjunct was also applied by no proof and was
  false of ML-KEM's probabilistic correctness bound; it has been removed from
  the refinement boundary while `toyKem_correct` remains a separate model
  fact.
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

## Proved (the ML-KEM Braid keeps the two premises its receive theorems take)

Location: `Translation/BraidPreserve.lean`.

`Braid.receive_no_panic` and `Braid.receive_refines` take `State.ct1_bounded` as a premise: the KEM
ciphertext a state stores is at most 4096 bytes. Until these results no theorem showed that a
send or a receive keeps it. They show that every successful step of the standalone Braid
translation keeps a clause set `State.sized`: `ct1_bounded`; `Good 4096` for the decoder that
`HeaderSent` holds, the clause `ct1_bounded` needs before it is closed under the transitions; and
`Good 4128` for each other decoder a state holds, which on the session unit carries the `needed`
bound of `decoders_bounded`. `ct1_bounded` alone is not preserved: `ct1` is the
message of the decoder that `HeaderSent` holds, which is as long as the decoder was sized for, and
`ct1_bounded` does not say that decoder is sized for at most 4096 bytes. A `HeaderSent` state
whose decoder is sized for 4097 bytes meets `ct1_bounded`, and the chunk that completes the
decoder makes a `ct1` of 4097 bytes. That step is not a Lean theorem: the translated
`Decoder::message` is not computed in Lean, and the real one returns as many bytes as the decoder
was sized for. It was run on the real crate, and the test is recorded under "Waiting on the next
re-translation window" in `LIMITATIONS.md`, because it is not committed.
`Braid::invariant` states the missing clause as `decoder_sized(ct1_dec, CT1_LEN)`, so a restored
Braid is not such a state, and `State.sized` states it as `Good 4096 ct1_dec`.

- `Braid.step_send_sized`, `Braid.step_receive_sized`: a successful `step_send` or `step_receive`
  carries a state that has `State.sized` to one that has it, for all twelve states. The hypotheses
  are values the opaque operations return and never that a step returns, so the theorems are about
  the steps that do.
- `State.clone_sized`: a state's clone has it too, so the clone that `send` and `receive` step is no
  gap.
- `Braid.send_sized`, `Braid.receive_sized`, `Braid.commit_sized`: the same for the two entry points and
  for adopting a candidate.
- `Braid.initiator_sized`, `Braid.responder_sized`: the two constructors build a Braid that has it.
  The responder's one decoder is `hdr_decoder`.
- `Braid.Run.sized`: every Braid that a run reaches from Braids that have `State.sized`, by any
  number of `send` (with an RNG that answers) and `receive`, has it. `Braid.Run Base` is the
  closure, and `Braid.Run.sized` takes `Base` as an argument.
- `Braid.Constructed.sized`: the constructors' Braids are such a base.
- `State.sized_ct1_bounded`: `State.sized` gives `ct1_bounded`, the premise the receive theorems take.
- `Braid.Run.exists_initiator`, `Braid.Run.exists_responder`, `Braid.Run.exists_send`: the closure
  is not empty. An initiator and a responder exist under the totality hypotheses each theorem
  takes, and two Braids exist that the closure reaches, the second the result of a `send` from the
  first. Each takes its own totality hypotheses and not those of `Braid.Run.sized`, so they do not
  show that the hypotheses of `Braid.Run.sized` hold together; the length constants and
  `Encapsulate1Total` have a model in `KemWitness.lean` and `Laws` has one in
  `BraidPreserveWitness.lean`, and no theorem combines the two.

**Assumed, and where recorded.** `step_receive_sized` and what is built on it take `Laws`
(`BraidPreserveDecoder.lean`): a decoder that `Decoder::new(m)` builds never returns a message
longer than `m`, however many chunks it is given and however often it is cloned. It is new and
it is assumed. The real `Decoder::message` ends in `out.truncate(self.size)`, and the session
unit proves the analogue from the translated body, given `TruncateLen` (below). It has a model
together with the three erasure hypotheses `BraidT1` and `BraidT3` already take (next section). The
theorems take four of `BraidT1`'s KEM length constants (`Ct1LenTotal`, `Ct2LenTotal`,
`HeaderLenTotal`, `EkVectorLenTotal`, each at most 4096; the real ones are 1408, 160, 64 and 1536),
and the send theorems take `Encapsulate1Total` with `RngTotal rc`, which caps the ciphertext
`encapsulate1` returns. Those five are existing hypotheses, modelled by `KemWitness.lean`.

**What is not claimed.** No theorem here says a step returns: `BraidT1` does, for a state with
`ct1_bounded`, and `State.sized` now supplies that premise for every Braid a run reaches.
`State.sized` is not `Braid::invariant`: it has none of the clauses of `Braid::invariant` that the
receive theorems do not use (the exact lengths of `header`, `ct1` and `ek_vector`, the encoders'
sizes, `epoch >= 1`, the key pair's validity). On the standalone translation a decoded Braid is not
shown to have it, because `Decoder::invariant` and `Decoder::size` are opaque there; the session
unit shows it (below). The epoch headroom `epoch + 1 < u64::MAX` that the refinements take is not a
clause of `State.sized` and is not discharged. A clone of a Braid (`Braid` derives `Clone`) is not a
step of `Braid.Run`; `State.clone_sized` covers the state clone that `send` and `receive` take. The
three non-vacuity theorems exhibit an initiator, a responder and one send from an initiator. None
of those Braids holds a stored `ct1` or a `ct1` decoder, so no theorem here exhibits a Braid in the
closure for which `ct1.length <= 4096` or `Good 4096 ct1_dec` is more than `True`.

## Proved (the law the Braid's preservation theorems add has a model, and the receive corollaries)

Location: `Translation/BraidPreserveWitness.lean` and `Translation/BraidPreserveCorollary.lean`.

- `newMsgLen_iff`: `Laws` is `NewMsgLenShape` at the real erasure operations, so a model of the
  shape is a model of the law, and a change to the statement stops the file from building.
- `api_newMsgLen`: the Reed-Solomon implementation of `ErasureWitness.lean` never returns a message
  longer than the size it was built for.
- `erasure_laws_satisfiable`: one implementation of the opaque erasure operations satisfies
  `ErasureAgrees`, `ErasureCloneAgrees`, the seven erasure totality assumptions and `NewMsgLen`
  together. This is consistency of the statements and not a statement about the real crate.
- `model_for_both_widths`: `Usize.max` is `U32.max` or `U64.max` (`Usize.bounds_eq`), and the model
  satisfies `NewMsgLenShape` for an arbitrary `Usize`, so it satisfies it at each width. The proof of
  `api_newMsgLen` uses no fact about the width (its axioms are `propext`, `Classical.choice`,
  `Quot.sound`).
- `Braid.Run.receive_no_panic`, `Braid.Run.receive_refines`: `BraidT1.Braid.receive_no_panic` and
  `BraidT3.Braid.receive_refines` for a Braid that a run reaches. The premise `ct1_bounded` is
  replaced by `Braid.Run Base self`, with `Base` having `State.sized`, and by `Laws`,
  `Encapsulate1Total` and `EkVectorLenTotal`. Every other premise of `receive_refines` stays, among
  them the epoch headroom, the honest-chunk condition and the relation of the real state to a model
  state.

## Proved (the same preservation theorems on the session unit, with the decoded Braid)

Location: `Translation/SessionUnitBraidPreserve.lean`, `Translation/SessionUnitBraidPreserveDecoder.lean` and `Translation/SessionUnitBraidPreserveFacts.lean`.

`SessionUnitBraidPreserve.lean` is the count-checked port of `BraidPreserve.lean`
(`scripts/port-session-braid-preserve.sh`, run by CI with `--check`), so its theorems have the same
names and the same text, and its negative controls are in `scripts/check-port-negatives.sh`. The
unit translates the erasure decoder with a body, so a decoder is read off its fields: `Good n d` is
`d.size <= n` and `d.needed <= MAX_CODEWORDS`, and `Laws` is two laws about standard-library
operations, `TruncateLen` (`Vec::truncate` of `n` returns at most `n` elements) and `DivCeilValue`
(`usize::div_ceil a 32` is `(a + 31) / 32`, the law `SessionUnitDecoderBound.lean` already states).
Both are assumed. `LIMITATIONS.md` records them.

- `Braid.step_send_sized`, `Braid.step_receive_sized`, `State.clone_sized`, `Braid.send_sized`,
  `Braid.receive_sized`, `Braid.commit_sized`, `Braid.initiator_sized`, `Braid.responder_sized`,
  `Braid.Run.sized`, `Braid.Constructed.sized`, `State.sized_ct1_bounded`,
  `Braid.Run.exists_initiator`, `Braid.Run.exists_responder`, `Braid.Run.exists_send`: the fourteen
  results of the previous sections, on the unit.
- `message_length_le`: a message `Decoder::message` returns is at most `size` bytes, given
  `TruncateLen`. The function ends in `truncate(size)`.
- `Good.new`, `Good.msg`, `Good.add`, `Good.clone`: a decoder that `Decoder::new` builds from a protocol
  constant is `Good` (it takes `DivCeilValue`, for `needed`), a `Good` decoder returns messages of
  at most `n` bytes (it takes `TruncateLen`), and adding a chunk or cloning keeps `Good`
  (they use `SessionUnitDecoderBound.lean`'s lemmas and no law).
- `sized_decoders_bounded`: `State.sized` gives `State.decoders_bounded`, so it supplies both premises
  of the unit's receive theorems.
- `invariant_true_gives_sized`, `from_bytes_sized`: a Braid whose translated `invariant` returns
  `true`, and so a Braid that `Braid::from_bytes` returns, has `State.sized`. The clauses are read off the
  arms of `Braid::invariant`: `Vec::len ct1 = CT1_LEN`, `Decoder::invariant` on every decoder, and
  `decoder_sized` against the protocol constant each decoder is built with. The hypotheses are the
  four KEM length constants being at most 4096.
- `Braid.Run.sized_of_start`, `Braid.Run.inv`: every Braid that a run reaches from the constructors and
  from decoded Braids has `State.sized`, and so `Braid.Inv`, the two-field mirror that
  `SessionUnitBraidImportInv.lean` states.
- `Braid.Run.receive_no_panic`, `Braid.Run.receive_refines`: the unit's receive theorems for such a
  Braid. The premises `ct1_bounded` and `decoders_bounded` are replaced by
  `Braid.Run Braid.Start self`, `Laws`, `Encapsulate1Total` and `EkVectorLenTotal`. Every other
  premise of `receive_refines` stays.
- `inv_not_sized`: `Braid.Inv` does not say what `State.sized` says. A `HeaderSent` state with a
  decoder that is sized for 4097 bytes and needs 129 chunks meets `ct1_bounded` and
  `decoders_bounded`, so it meets `Braid.Inv`, and it does not have `State.sized`. The statement
  quantifies over every key pair, so it needs no inhabitant of the opaque key-pair type. That the
  step then breaks `ct1_bounded` is not a theorem either, for the reason given above.
- `TruncateLen_is`, `truncateLen_model`, `laws_model`: `TruncateLen` is `TruncateLenShape` at the
  unit's `Vec::truncate` by `Iff.rfl`; the joint model of `UnitSatisfiabilityJoint.lean`, which satisfies
  every axiom-level field of the four session records and the five laws of `LIMITATIONS.md` at once,
  satisfies it (its `truncate` is a prefix) and `DivCeilValue`'s shape. This is consistency of the
  statements in one interpretation of the unit's opaque constants, as `LIMITATIONS.md` records for
  the five laws, and not a model of the real `Vec::truncate` or `usize::div_ceil`.

**What holds these results in place.** Each result named in the three sections above has an axiom
pin under `#guard_msgs`, and `attest.py` requires all of the axiom pins (`REQUIRED_PINS`), so
deleting one fails it. The axiom lists name constants that occur in the statements, not assumptions
made by the proofs, and the results that take `Laws` say so in their statements. An axiom pin does
not hold a statement. Statements are held by `#guard_msgs in #check` pins, and the definitions that
carry the claim by
`#guard_msgs in #print` pins (`State.sized`, `Braid.sized`, `Braid.Run` with its constructors,
`Braid.Constructed`, `Braid.Start`, `Braid.Decoded`, `Reach`, `Good`, `NewMsgLen`, `TruncateLen`,
`TruncateLenShape`, `Laws`, in the standalone and unit files that define them). These are held by the
build and by the axiom pin. `attest.py` requires each of these pins to exist (`REQUIRED_STATEMENT_PINS`),
so deleting one, commenting one out, removing its `#guard_msgs` or giving it an option that compares
nothing fails it. It does not read what a pin says, so a statement changed together with its pin's
expected message is accepted, and weakening a result whose statement has no pin changes nothing a gate
reads. The results whose statements are held only by the build and the axiom pin, with no statement pin, are
`api_newMsgLen`, `model_for_both_widths`, `message_length_le`, `Good.msg`, `Good.add` and `Good.clone`.

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
  each is about translated Rust and refines the model under the boundary this file names:
  the KDF boundary below, `RemoveSkippedAtAgrees` and `VecRetainAgrees`.
  **`set_chains_refines` and `clear_old_epochs_refines` are not proved outright.** Each is
  `VecRetainAgrees` (its first and its second conjunct) applied to its arguments, so each is that
  hypothesis and no more, and every theorem that calls them (`advance_refines`,
  `maybe_advance_refines`, `send_refines`, `skip_message_keys_refines`, `receive_refines` and the
  Triple's discharged theorems, and, on the session unit, `SessionUnitTripleT3`'s discharged theorems and
  the `vecRetain` and `spqrRemove` fields of the contract records in `UnitLifecycleT3.lean`) rests on it. `VecRetainAgrees` and `RemoveSkippedAtAgrees` are
  statements about translated functions (`State::set_chains`, `State::clear_old_epochs`,
  `State::remove_skipped_at`); `SatisfiabilitySpqrLaws.vecRetainAgrees` and
  `SatisfiabilitySpqrLaws.removeSkippedAtAgrees` prove them from named laws about opaque constants
  (the section "Proved (hypotheses about translated functions in the leaf crates and the three-leaf
  unit, from named laws, and the decoder acceptance witnesses)"), but the theorems of this file still
  take them as hypotheses.
- **No KEM boundary and no erasure-coding boundary.** Unlike the ML-KEM
  Braid, this crate never computes a shared secret or touches a chunk codec
  -- `Output` arrives as a value from whichever crate produced it. The only
  opaque call this file assumes anything about the *value* of is
  `hkdf_sha256`; `Vec::pop`, `Zeroize` and
  `Option::clone` are opaque too and each carries its own assumption below; the retain and removal scans
  are translated loops whose results `VecRetainAgrees` and `RemoveSkippedAtAgrees` assume.
- **The KDF boundary, `SpqrHkdfAgrees`:** one assumption, stated one level
  below `SpqrT1.lean`'s totality-only `KdfRkTotal`/`KdfCkTotal`, at the
  opaque `hkdf_sha256` call itself -- that when it returns, it returns what
  `Model.Kdf.hkdf` computes -- under RFC 5869's `N.val ≤ 8160`, discharged
  at the 64- and 96-byte literals. Subsumes both of `SpqrT1.lean`'s KDF
  assumptions, so this file states the boundary once rather than twice.
- **`VecRetainAgrees` and `RemoveSkippedAtAgrees`:** each states what the
  operation returns, not only that it returns. `RemoveSkippedAtAgrees` is strictly stronger than
  `SpqrT1.RemoveSkippedAtTotal`, so that one is not separately assumed here; `VecRetainAgrees` does not cover
  the capacity and wipe calls, so `SpqrT1.VecRetainTotal` is carried beside it (`hret_total`).
  `RemoveSkippedAtAgrees` is stated under the index guard
  `i.val < v.val.length`, and says the custom wipe-before-pop helper returns
  the indexed key and the vector with that index erased.
- **No `VecAppendAgrees`.** `LIMITATIONS.md` and earlier text of this ledger named a hypothesis
  `VecAppendAgrees` about the skip step's concatenation. No theorem of this file takes it and no proof file
  defines it. The translated `skip_message_keys` builds its result with `Vec::with_capacity`, two `Vec::push`
  loops and `core::mem::replace`, and `SpqrT1.VecAppendTotal` is `True`, kept as a name for the downstream
  files.
- **Further preconditions on `send_refines`/`receive_refines`:** besides `hepoch`, `hroom`, `hskiproom`, `hone` and `hcounter`, both
  carry `hcb`, `hsb` and `hnewb`: every chain epoch, every skipped-entry epoch,
  and the incoming `Output.key_epoch` must satisfy `+ epochsKept ≤ U64.max`,
  so the retirement arithmetic cannot overflow. (For a decoded state `hcb` and `hsb`
  follow from the invariant and `hepoch`; `hnewb` does not.) These propagate into the
  Triple Ratchet's refinement on the unit, through its sparse bundle. `hepoch` and `hcounter` are the model's
  requirements, not the code's: `SpqrT1.lean`'s `send_no_panic`/
  `receive_no_panic` no longer carry either, every epoch and counter
  increment being a `checked_add` whose `None` arm returns `ChainExhausted`,
  and `Model.SparseRatchet` now refuses at those ceilings too, so the two may
  no longer be needed here; that has not been checked, and they are kept.
  `BraidT3.lean` keeps its `hepoch` on the same terms: `Model.Braid` now
  refuses at its epoch ceiling too, and whether that `hepoch` could be
  dropped has not been checked either.
  `hepoch` is `epoch + 1 < U64.max`, a step of headroom rather than the plain
  ceiling bound: `advance` reserves `u64::MAX` and returns `ChainExhausted`
  rather than opening chains under an epoch its own retention window would
  immediately retire, and the model refuses the same step with `none`, so at
  `epoch = u64::MAX - 1` the two refusals differ. `u64::MAX - 1` is otherwise a fully usable epoch, so what
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
- **Eight assumptions in this file, five new constants and three reused
  outright** (`SpqrT1.VecRetainTotal`, `ZeroizeTotal` and `OptionCloneTotal`), none the same proposition as any
  other file's assumption of a similar shape -- the same per-crate counting rule `SpqrT1.lean` and
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

## Proved (tier T1, the session lifecycle on the eight-leaf unit, under its contracts)

Location: `Translation/UnitLifecyclePublicT1.lean`.

The four entry points a
product calls and the private `decrypt_ratchet`, translated inside `tacenta-core/session-unit` where the
ratchets, the Braid, the wire codecs and the PQXDH derivation are real
bodies rather than axioms. Each theorem is conditional on the contract record named in its
statement, on an explicit headroom record and, for `decrypt_no_panic`,
`decrypt_ratchet_no_panic` and `establish_responder_no_panic`, on the class
`SessionUnitT1.DerivedKeysModel`, which no record contains. The records are `EncryptContracts`
(25 named hypotheses), `DecryptRatchetContracts` (38, taken by `decrypt_no_panic`
and `decrypt_ratchet_no_panic`), `EstablishInitiatorContracts` (15) and
`EstablishResponderContracts` (45), counting the fields of nested records. Twelve
of the fourteen boundary contracts of `LIMITATIONS.md` ("The Session unit's
primitive contracts") appear among those fields; `KemCiphertextLenTotal` and
`XeddsaSignTotal` appear in none of the four records. The others are contracts
on the ratchets, the Braid, the Triple Ratchet and the session layer; `invariant_gives_preconditions` derives the
leaf preconditions from `Session::invariant`. Nothing here relates a result
to the model: that is `UnitLifecycleT3.lean`'s conditional branch lemmas,
which are not listed as claims.

**A false field was restated for bounded decoders; the records now follow from an axiom base that has
a model, under five laws (the two sections after the repair, below).** `BraidReceiveContracts`, which `DecryptRatchetContracts` contains and
`EstablishResponderContracts` contains through it, used to include
`SessionUnitBraidT1.DecoderMessageTotal` stated for every `Decoder`: the hypothesis that
`Decoder::message` returns for every decoder. That is false: a decoder that needs
`(Usize.max + 1) / 32` chunks and holds that many has a message, and assembling it appends
more bytes than a vector can hold (`decoderMessage_not_total`, in the next section). So
`decrypt_ratchet_no_panic`, `decrypt_no_panic` and `establish_responder_no_panic` took a
hypothesis that nothing satisfied, and so did five Braid theorems of the same unit
(`SessionUnitBraidT1.Braid.step_receive_no_panic` and `Braid.receive_no_panic`,
`SessionUnitBraidImportInv.Braid.decoded_receive_no_panic`, and
`SessionUnitBraidT3.step_receive_refines` and `Braid.receive_refines`) and the sixteen (and two
more, on one branch) theorems of `UnitLifecycleInitialDispatch.lean` that take the records
(`GAP-REGISTER.md`, row `SESSION-CONTRACT-VACUITY`).

The field is now stated for the decoders that need at most `MAX_CODEWORDS = 65536` chunks, a
clause `Decoder::invariant` checks (`DecoderMessageTotal`; the old statement remains as
`DecoderMessageTotalUnbounded`). The bound reaches the receive theorems through the state: a new
predicate `State.decoders_bounded` is an extra precondition of `Braid.step_receive_no_panic`,
`Braid.receive_no_panic`, `step_receive_refines` and `Braid.receive_refines`; `DecryptRatchetHeadroom`
and `InvariantPreconditions` carry it as a field, `braidDecoders`; and `Braid::invariant` supplies
it (`Braid.Inv.decoders_bounded`, from `invariant_true_gives_decoders_bounded`), so
`invariant_gives_preconditions` produces it and `decoded_receive_no_panic` needs no side
condition. `Decoder::add_chunk` and `Decoder::clone` keep `needed`, which the proofs show
(`SessionUnitDecoderBound.lean`). The decoder a freshly built responder Braid holds is bounded
by the value of `usize::div_ceil` at divisor 32, a new field `divCeilValue` of
`EstablishResponderContracts` (45 fields, one more than before; the decrypt theorems do not take it).
The statements of the three lifecycle theorems did not change; the records they take did, and
the four Braid theorems above each gained the precondition `decoders_bounded`.

What this does and does not show. The repaired field is true given the one law that
`Vec::truncate` returns, and the old argument does not touch it
(`Translation/SessionBraidReceiveRepair.lean`, below). The statement is about the translation,
where allocation does not fail. That
`BraidReceiveContracts` and the other three records follow from an axiom base that has a model is shown, in the
sense and under the five laws recorded in `LIMITATIONS.md`, in the sections "Proved (the records' fields about
translated functions, from named laws)" and "Proved (one interpretation of the unit's opaque constants, and
the four records from it)" below; `divCeilValue` is one of those laws, an assumption about an
opaque standard-library function. That a send or a receive keeps
`State.sized`, which gives `decoders_bounded` and `ct1_bounded`, is shown for the Braid's own operations in the sections
"Proved (the ML-KEM Braid keeps the two premises its receive theorems take)" and "Proved (the
same preservation theorems on the session unit, with the decoded Braid)", and not for a session
state, which the single-step lifecycle theorems do not reach. The three theorems that were vacuous
no longer fail for a hypothesis in their records, in the sense and under the five laws of the sections named
above. The headroom they take is met by some input, in the sense and under the assumptions recorded in
`LIMITATIONS.md` ("The headroom records"); no theorem shows that a session the crate produces meets it. The dispatch theorems compile
against the repaired record and are not claims. The evidence hypotheses of the lifecycle dispatch layer are a
separate matter, which the section "Proved (a negative result: five evidence hypotheses and records of the
lifecycle dispatch layer are false or empty)" below gives. The standalone Braid theorems in `BraidT1.lean`
and `BraidT3.lean` are not affected, because there the decoder is an opaque type and the field
can be satisfied (`Translation/ErasureWitness.lean`, `erasure_hypotheses_satisfiable`, proves the
standalone Braid's seven erasure totals jointly satisfiable). The decoders the Braid holds are
bounded, by reading the source: the Braid calls `Decoder::new` only with protocol constants, and a
decoder's `have` grows only through `add_chunk` (one chunk per `u16` index) or `from_bytes` (which
refuses `needed > MAX_CODEWORDS` and calls `Decoder::invariant`), so a decoder that has a message has
`needed <= 65536`. The public `Decoder::new(usize::MAX)` builds a decoder that needs
`(Usize.max + 1) / 32` chunks, but it can never hold that many, so it never has a message. The
proofs now state the parts of that which concern the translated definitions (`add_chunk`, `clone`,
`invariant`, `new` given the `div_ceil` law); the reading of `from_bytes` and of the Braid's calls
of `Decoder::new` is not a theorem.

- `encrypt_no_panic`, `decrypt_no_panic`, `decrypt_ratchet_no_panic`: (`decrypt_no_panic` and
  `decrypt_ratchet_no_panic` took a record with a false field until the repair, see above) `Session::encrypt`,
  `Session::decrypt` and `decrypt_ratchet` return, given the
  headroom records in their statements (`EncryptHeadroom`,
  `DecryptRatchetHeadroom`). `invariant_gives_preconditions` yields three of the
  four receive-headroom fields. The fourth, a bound on the associated data
  length, follows from `Session::invariant` too: clause (c) fixes the associated data at the
  66 bytes that `identity_ad_length` proves (`invariant_gives_ad_length`, `decryptHeadroom_of_invariant`, in the section
  "Proved (the lifecycle headroom records are satisfiable, and what `Session::invariant` gives)").
- `establish_initiator_for_no_panic`, `establish_responder_no_panic`:
  (`establish_responder_no_panic` took a record with a false field until the repair, see above) the two establishment
  entry points return, the responder's with room in its
  last-resort record.
- `invariant_gives_preconditions`: given `Ct1LenTotal` (the translated `CT1_LEN`
  returns a value of at most 4096), a session for which `Session::invariant`
  returns `true` has the preconditions the inner Triple and Braid theorems carry.
  It takes that one contract and no headroom record.

None of the six theorems depends on a compiler-trust axiom. Two closed facts that
were settled by `native_decide` are now settled in the kernel: that `(1 : U64)` has
value one, in the sparse ratchet's `receive_no_panic`, by `decide`, and that the
two `FullStore` discriminants differ, in `full_store_eq_no_panic`, by `simp`. Each
of the six carries an axiom pin under `#guard_msgs` at the end of
`Translation/UnitLifecyclePublicT1.lean`, and `attest.py` lists the six in
`REQUIRED_PINS`, which also lists the results of the next section, so deleting a pin
block, or leaving it inside a comment, fails it. The pins hold axiom lists only. A change to a contract record, to the class
`SessionUnitT1.DerivedKeysModel` or to a headroom record, or a weaker theorem
statement, fails a pin only if it names an operation the pin does not list. Nor do they show that the records can be met by themselves:
`Translation/UnitSatisfiabilitySession.lean` exhibits a model for each of thirteen boundary contracts
separately (the fourteenth, `DivCeilValue`, has `divCeilValue_shape_satisfiable` in
`Translation/SessionBraidReceiveRepair.lean`). That the four records and the class follow from an axiom base that has a model, in the sense
of the section "Proved (one interpretation of the unit's opaque constants, and the four records from it)"
below, under five laws and without the headroom records, is shown by other results. Two of the four,
`DecryptRatchetContracts` and `EstablishResponderContracts`, contained a field that was false, which the repair
restated for decoders that need at most `MAX_CODEWORDS` chunks (above, and `LIMITATIONS.md`, "Trusted, not
verified" for the bound and "The four contract records follow from an axiom base that has a model, under five laws" for the inhabitation).

## Proved (a negative result: the unbounded decoder hypothesis is false)

Location: `Translation/SessionBraidReceiveVacuity.lean`.

- `decoderMessage_not_total`: `SessionUnitBraidT1.DecoderMessageTotalUnbounded`, the statement
  that `Decoder::message` returns for every decoder, is false. A
  decoder with `needed = (Usize.max + 1) / 32` that holds that many chunks has a
  message, and `Decoder::message` fails on it, because the output vector would hold
  `Usize.max + 1` bytes. The proof assumes no property of any opaque operation. It holds on
  both platform widths: `usize_max_facts` supplies the chunk count, 2^27 or 2^59, by cases on
  `Usize.bounds_eq`, and nothing after it depends on which case applies. Until the repair this
  statement was the unit's `DecoderMessageTotal`.
- `braidReceiveContractsUnbounded_false`, `decryptRatchetContractsUnbounded_false`,
  `establishResponderContractsUnbounded_empty`: `BraidReceiveContractsUnbounded`, and the two records
  that contain it, cannot be satisfied. These three records are restated in this file as they stood
  before the repair (the same fields in the same order, with the unbounded `decoderMessage`); the
  live records are not refuted by this argument (next section).
- `message_eq_messageP`, `all_tr_refute`: `Decoder::message` is the function `messageP` with
  the unit's `Vec::truncate` in its last step, and with that step replaced by any function
  whatever, `messageP` still fails to return for some decoder. So the refutation
  does not depend on how `Vec::truncate` behaves; `all_tr_refute` depends on the three
  standard axioms only.

These are results about our hypotheses, not security claims about the product. They
show that `decrypt_ratchet_no_panic`, `decrypt_no_panic` and `establish_responder_no_panic`,
named in the session lifecycle T1 section, and the five Braid theorems of the session unit
were vacuous as stated before the repair. Each of the six results is pinned under
`#guard_msgs` at the end of the file. The axiom lists in the first five pins name constants
that occur in their statements (`Vec::truncate`, and the constants the contract records mention),
and the proofs use none of them as assumptions. The sixth, `all_tr_refute`, lists the three
standard axioms only.

## Proved (the repaired decoder hypothesis: what the bound buys, and what it does not)

Location: `Translation/SessionBraidReceiveRepair.lean`, `Translation/SessionUnitDecoderBound.lean`.

The first group, in `SessionBraidReceiveRepair.lean`, is about the field
`SessionUnitBraidT1.DecoderMessageTotal` after the repair: `Decoder::message` returns for every
decoder with `needed <= 65536`. This is a statement about the translated `Decoder::message`, in which
`Vec::with_capacity` never fails. The Rust function reserves `size` bytes and panics or aborts for a
decoder with a small `needed` and a huge `size` (for example `size = usize::MAX`, `needed = 1` and one
chunk held). `Decoder::invariant` rejects that decoder through `needed == chunk_count(size)`;
`State.decoders_bounded` does not carry that clause, so the receive theorems are stated for such a
state too, and about it they say something about the translation only. No state a peer can build has it.

- `old_witness`: there is a decoder with `32 * needed = Usize.max + 1` on which
  `Decoder::message` cannot return a value (the decoder of the refutation above).
- `boundary_gt_max_codewords`: `65536 < (Usize.max + 1) / 32` on both platform widths.
- `old_witness_fails_bounded_premise`: that decoder needs more than 65536 chunks, so the repaired
  premise excludes it.
- `old_witness_rejected_by_invariant`: there is a decoder with `32 * needed = Usize.max + 1` on which
  `Decoder::message` cannot return and on which the translated `Decoder::invariant` does not return
  `true`. With `invariant_true_gives_decoders_bounded`, a Braid that passed its invariant holds no
  decoder that needs more than 65536 chunks.
- `decoderMessageTotal_of_truncate`: the repaired field follows from the one law `TruncateTotal`
  (`Vec::truncate` returns; the real operation never panics). The law is the only assumption about
  an opaque operation.
- `bounded_holds_unbounded_fails`: under that law, the repaired field is true and the unbounded
  statement is false.
- `message_total_of_invariant`: under that law, every decoder for which the translated
  `Decoder::invariant` returns `true` has a returning `Decoder::message`.
- `boundary_exact`: the field holds for every `needed < (Usize.max + 1) / 32` and fails at
  `needed = (Usize.max + 1) / 32`, so the line between true and false is exactly that value and
  65536 lies well below it.
- `mutant_premise_at_boundary_refuted`: raising the premise from 65536 to `(Usize.max + 1) / 32`
  gives a false statement, whatever the unit's opaque operations do. It is the second half of
  `boundary_exact` stated without the law, and it shows that 65536 cannot be raised to the line.
- `divCeilValue_shape_satisfiable`: the new law `DivCeilValue`, the value `(a + 31) / 32` of
  `usize::div_ceil` at divisor 32, is consistent: a function with that property exists. This is a
  model of the shape of the statement, not of the unit's opaque `div_ceil`.
- `decoderMessageTotal_is`: the field `SessionUnitBraidT1.DecoderMessageTotal` is
  `DecoderMessageTotalAt 65536`, by `Iff.rfl`. It ties the statements refuted by `boundary_exact`
  and `mutant_premise_at_boundary_refuted` to the field, so a change to the field stops the file from
  building.
- `DivCeilValue_is`: `SessionUnitDecoderBound.DivCeilValue` is `DivCeilValueShape` at the unit's
  `usize::div_ceil`, by `Iff.rfl`. It ties the consistency result above to the statement of
  `DivCeilValue`, so the two cannot differ.

The second group, in `SessionUnitDecoderBound.lean`, is the part of the argument that concerns
the translated definitions of the decoder. None assumes anything about an opaque operation, except that `new_needed_le` takes the value law `DivCeilValue` as a hypothesis.

- `add_chunk_keeps_needed`, `clone_keeps_needed`: a successful `Decoder::add_chunk` or
  `Decoder::clone` returns a decoder with the same `needed` and `size`, so a bound on a state's
  decoder carries to the decoder after a chunk is added and to a clone of the state.
- `invariant_true_needed_le`: a decoder for which the translated `Decoder::invariant` returns
  `true` needs at most `MAX_CODEWORDS = 65536` chunks. If the `div_ceil` inside `chunk_count`
  fails the invariant does not return `true`, so no law on `div_ceil` is used.
- `new_needed_le`: given `DivCeilValue`, `Decoder::new` on a size of at most 2 MiB returns a
  decoder that needs at most 65536 chunks. This is the one place the new law is used, for the
  decoder of a freshly built responder Braid.

These results alone do not show that `BraidReceiveContracts` or any other record is inhabited (the two
sections that follow do, in one sense and under five laws), and they say nothing about the product beyond what the translated definitions say. Each is pinned under
`#guard_msgs`, and `attest.py` requires all seventeen pins of the repair (`REQUIRED_PINS`), so
deleting one fails it; the axiom lists name constants that occur in the statements, not assumptions made
by the proofs, and the results that take `TruncateTotal` or `DivCeilValue` say so in their
statements.

## Proved (the records' fields about translated functions, from named laws)

Location: `Translation/UnitSatisfiabilityErasure.lean`, `Translation/UnitSatisfiabilityRatchet.lean`.

The four contract records of the session lifecycle T1 section contain thirteen distinct predicates that
are statements about functions the Session unit translates with a body, and not about opaque
constants: seven about the erasure coder (`DecoderNewTotal`, `DecoderAddChunkTotal`,
`DecoderMessageTotal`, `EncoderNewTotal`, `EncoderCloneTotal`, `DecoderCloneTotal`,
`EncoderNextChunkTotal`), the two removal helpers (`SessionUnitT1.RemoveSkippedAtTotal` and
`SessionUnitSpqrT1.RemoveSkippedAtTotal`), the three key derivations (`KdfRkTotal`, `KdfCkTotal`,
`SessionUnitTripleT1.KdfInitTotal`) and `VecRetainTotal`, whose first two conjuncts are about
opaque constants and whose three loop conjuncts are about translated loops. A model of the
unit's opaque constants cannot change what such a field says: its truth is fixed by the body and by
the opaque operations the body reaches. The results below settle twelve of the thirteen from named laws about the
opaque constants the bodies reach. The thirteenth, `DecoderMessageTotal`, follows from the one
law `TruncateTotal` (`decoderMessageTotal_of_truncate`, in the previous section). Each result
is conditional on exactly the laws its statement names, and they are results about hypotheses,
not about the product. The five laws that the inhabitation result of the next section assumes, four of which no record states, are
recorded in `LIMITATIONS.md` ("The four contract records follow from an axiom base that has a model, under five laws").

- `decoderAddChunk_total`, `encoderNextChunk_total`, `encoderClone_total`, `decoderClone_total`:
  `SessionUnitBraidT1.DecoderAddChunkTotal`, `EncoderNextChunkTotal`, `EncoderCloneTotal` and
  `DecoderCloneTotal` hold, with no assumption about any opaque operation (each pin lists the three
  standard axioms only). The length premises of the existing `add_chunk_no_panic` and
  `next_chunk_no_panic` are not needed: a vector of `Usize.max` elements makes `add_chunk` return
  at once and makes `next_chunk` copy a stored chunk.
- `decoderNew_iff`, `encoderNew_iff`: `DecoderNewTotal` holds if and only if `usize::div_ceil` returns at
  divisor 32, and so does `EncoderNewTotal`. The two fields are exactly that one law, not more.
- `divCeil32_of_value`, `decoderNew_of_divCeilValue`, `encoderNew_of_divCeilValue`: the value law
  `DivCeilValue` (`usize::div_ceil a 32` returns `(a + 31) / 32`, the field `divCeilValue` of
  `EstablishResponderContracts`) implies that law, and so implies both fields. The records keep both
  fields as they are; whether they can be removed from the records is not checked.
- `kdfRkTotal`, `kdfCkTotal`, `kdfInitTotal`: `SessionUnitSpqrT1.KdfRkTotal`, `KdfCkTotal` and
  `SessionUnitTripleT1.KdfInitTotal` follow from the HKDF returning for output lengths up to 8160
  bytes (`LawHkdf`, the field `HkdfTotal`) and the `Zeroizing` wrapper reading back what it wraps at 96
  and at 64 bytes (the field `ZeroizingArrayRoundTrip`). `kdfInitTotal` holds for every slice `sk`.
- `spqrRemoveSkippedAtTotal`, `ratchetRemoveSkippedAtTotal`: `SessionUnitSpqrT1.RemoveSkippedAtTotal`
  follows from `SessionUnitSpqrT1.ZeroizeTotal` and `LawPop`, and `SessionUnitT1.RemoveSkippedAtTotal`
  from the same two and `LawBlanketU32`.
- `setChainsLoopTotal`, `clearChainsLoop0Total`, `clearSkippedLoopTotal`: the three loop contracts
  inside `VecRetainTotal` follow from `ZeroizeTotal` and `LawPop`, and the first two also from
  `LawAsMut`. They terminate only because `Vec::pop` shortens the vector.
- `vecRetainTotal`: `VecRetainTotal` follows from `Vec::capacity` returning and `Vec::zeroize` returning at the
  three instances the unit passes to it (its own first two conjuncts), `ZeroizeTotal`, `LawAsMut` and `LawPop`.
- `defined_fields_hold`: the six fields (both removal helpers, the three key derivations and `VecRetainTotal`)
  together follow from the structure `Laws`.
  It has nine laws: four are fields of the records (`HkdfTotal`, the wrapper round trip at two lengths,
  `ZeroizeTotal`), two are conjuncts of the field `VecRetainTotal`, and three are stated by no record.
- `spqrRemoveSkippedAtTotal_false_of_noop_pop`, `ratchetRemoveSkippedAtTotal_false_of_noop_pop`: given
  `ZeroizeTotal`, if `Vec::pop` returns and leaves the vector unchanged then
  `SessionUnitSpqrT1.RemoveSkippedAtTotal` is false, and so is `SessionUnitT1.RemoveSkippedAtTotal` given also
  `LawBlanketU32`. That function was the witness `UnitSatisfiabilitySession.lean` used for `VecPopTotal`
  until it was replaced, so the thirteen separate witnesses did not compose.
- `ratchetRemoveSkippedAtTotal_forces_blanketU32`, `setChainsLoopTotal_forces_asMut`: given
  `ZeroizeTotal`, the classical removal field implies `LawBlanketU32`, and `SetChainsLoopTotal` implies that
  `Option::as_mut` returns at `Option<Chain>`, the one type the proofs use `LawAsMut` at. Two of the three laws
  that no record states are therefore needed by a field, at the types the proofs use, and are not spare.
  For `LawPop` the result is the exclusion of the no-op, not an equivalence.

The pins of the `div_ceil` results list `usize::div_ceil` because it occurs in their statements; the pins of the
ratchet results list the opaque constants their statements and
their law hypotheses are about (`Array::zeroize`, `Vec::pop`, `Option::as_mut`, the blanket
`Zeroize`, the pair `Zeroize` inside the chain table's instance, the HKDF, the `Zeroizing` wrapper). None depends on a compiler-trust axiom. The proofs are
statements about the translation: `Vec::with_capacity` never fails in the Aeneas model, where the
real function panics for an absurd capacity, so a result that reaches it (`Encoder::new`,
`Decoder::message`) holds of the translated code and says nothing about a request for more memory
than the machine has.

## Proved (one interpretation of the unit's opaque constants, and the four records from it)

Location: `Translation/UnitSatisfiabilityJoint.lean`, `Translation/UnitSatisfiabilityRecords.lean`, `Translation/UnitSatisfiabilitySession.lean`.

`UnitSatisfiabilityJoint.lean` interprets 49 of the opaque axioms of `TacentaSessionUnit.lean` that the
four contract records reach (6 types, 4 constants, 39 functions; of the unit's other 39 axioms, 38 are reached
by no field and the error type inside `RngCore` is reached and not interpreted) in one structure `Interp`, and shows that one interpretation satisfies every field of the four
records that mentions only those constants, both model classes and the five laws of `StdLaws`.
`UnitSatisfiabilityRecords.lean` proves, at the real constants, that the four records follow from that
base. The sense of "inhabited" is the substitution argument and no other: every axiom that a record reaches is an
uninterpreted constant (the unit also holds 143 compiler-trust facts about format-string lengths, none of
which mentions an interpreted constant), so a derivation of `False` from a record at the real constants would,
after the constants are replaced by the model's terms, become a derivation of `False` from facts that hold in
the model. That last step is an argument about derivations and not a theorem inside Lean. It does not show that
the real primitives, or the real standard-library and `zeroize` functions, satisfy any field or any law, and it does not cover the headroom records, which
`UnitHeadroomSatisfiable.lean` and `UnitHeadroomInvariant.lean` take up (the section "Proved (the lifecycle headroom records are satisfiable, and what `Session::invariant` gives)" below). The
exact residual is in `LIMITATIONS.md`.

- `all_shapes_are_predicates`: each of 37 predicates of the session proofs is, at `Interp.real`, the shape
  over an interpretation that replaces it. Thirty-six bridges are `Iff.rfl`, so the kernel checks that the two
  sides unfold to the same proposition. The thirty-seventh, `VecRetainTotal_is`, regroups the five conjuncts of
  `VecRetainTotal` into its axiom half and its three loop contracts, and the kernel checks that proof.
  `check-session-satisfiability-negatives.sh` requires this theorem to name every `_is` bridge except the
  illustration `DecoderNewTotal_is`. (A shape that differs from the predicate by a constant, a premise or a
  conjunct is rejected: the three controls inside the module, each stated as a definition, and the four bridge cases
  of `check-session-satisfiability-negatives.sh`.)
- `model_satisfies_all_axiom_shapes`: `Interp.model` satisfies every shape, `ZeroizingModel` at
  `Vec U8` and `DerivedKeysModel` at `Vec (U32 × Array U8 32)`, the value law of `div_ceil`, `FaithfulShape`
  and `StdLaws`. The theorem names every witness, so removing one breaks the build.
- `stdLaws_of_faithful`, `model_Faithful`, `model_StdLaws`, `model_pop_empty`, `model_capacity_ge`,
  `model_truncate_is_take`: the model implements `Vec::pop` (last element,
  shortened vector), `Vec::truncate` (a prefix), `usize::div_ceil` (ceiling division; the model fails on a zero
  divisor, which `FaithfulShape` does not require), `Option::as_mut` (the identity borrow) and `Vec::capacity` (at
  least the length) as the real operations do, and the laws the proofs use follow (given that the blanket
  `Zeroize` returns at `u32`). The empty-vector case of `pop`, the `capacity` bound and the `truncate` prefix are also
  held by statement (`model_pop_empty`, `model_capacity_ge`, `model_truncate_is_take`), so weakening the matching
  clause of `FaithfulShape` is refused. So the model is not a degenerate function with the weak property. The blanket
  `Zeroize` and the array, vector, pair and tuple `Zeroize` are modelled as the identity, which is not what they do; only
  the returning of the blanket one is used by a law. `UnitSatisfiabilityZeroizeScope.lean` gives a second interpretation
  in which the array, vector and pair ones zeroize element by element and propagate a failing element's failure, and
  which satisfies every shape too.
- `encrypt_iff_parts`, `decrypt_iff_parts`, `initiator_toParts_ofParts`, `responder_toParts_ofParts`: each
  record is exactly an axiom part over `Interp` and a defined part over the translated functions
  (the `Iff` for the two `Prop` records, a round trip by `rfl` for the two that carry the model class's data).
  The repacking functions name every field, so a field left out of both parts fails to build.
- `encrypt_axiom_part_satisfiable`, `decrypt_axiom_part_satisfiable`, `initiator_axiom_part_satisfiable`,
  `responder_axiom_part_satisfiable`: one interpretation satisfies each axiom part, under the hypothesis on the
  supplied `RngCore` that the record itself carries as a field (`RngTotal` for the encrypt record, `Random32Total`
  for the decrypt and responder records, both for the initiator record).
- `DecoderNewTotal_is`, `decoderNewShape_of_stdLaws`, `model_DecoderNew`: an illustration of the
  alternative to the substitution argument for one function: `Decoder::new` copied over the
  interpretation, bound to the real body by `Iff.rfl`, and proved for every interpretation that satisfies
  `StdLaws`. It is done for one function only, because it costs a copy of every body the record fields reach.
- `badRange_refutes`, `badDeref_refutes_array`, `badDeref_refutes_message_key`, `badOptionClone_refutes`,
  `badCap_refutes`, `badSeal_refutes`: controls. A model that breaks one faithful field (a `RangeFull::index`
  that forgets its slice, a failing `Zeroizing::deref`, an `Option::clone` that drops its content, a header
  constant above its cap, an AEAD seal that adds more than forty-eight bytes) makes the matching shape false, so
  the faithful parts of the model are held to something. Of the cap shapes, this shows `HeaderLen` and
  `AeadSealBounded` falsifiable; the `Ct1Len` cap is also held by a gate case.
- `stdLaws_real_iff`: `StdLaws` at the real constants is exactly the five laws: `LawPop`, `LawAsMut`,
  `LawBlanketU32`, `TruncateTotal` and `DivCeilValue`.
- `ratchetLaws_of_base`: the nine laws of the ratchet results follow from the base at the real constants.
- `encrypt_contracts_of_axiom_base`, `decrypt_contracts_of_axiom_base`, `initiator_contracts_of_axiom_base`,
  `responder_contracts_of_axiom_base`: `EncryptContracts` follows from its axiom part and `StdLaws`;
  `DecryptRatchetContracts` likewise, with the bounded `decoderMessage` from the truncate law;
  `EstablishInitiatorContracts` follows from its axiom part alone (its one defined field, `KdfInitTotal`, needs
  no law of `StdLaws`); `EstablishResponderContracts` follows from its axiom part and `StdLaws`. The two
  records that carry model-class data are stated with `Nonempty`.
- `records_of_axiom_base`: the base at the real constants gives all four records and the class
  `SessionUnitT1.DerivedKeysModel` together, the hypotheses of the five Session T1 theorems apart from their
  headroom records.
- `axiom_base_satisfiable`, `axiom_base_satisfiable_for_total_rng`: the base is satisfied by `Interp.model` with a
  concrete `RngCore`, and by the same interpretation for every `RngCore` whose `fill_bytes` returns (`RngTotal`). These
  two results and `records_of_axiom_base` are the two halves of the substitution argument.
- `vec_pop_satisfiable`, `noop_pop_not_faithful`, `VecPopLaw_is`, `all_thirteen_contracts_satisfiable`: the
  witness for `VecPopTotal` among the thirteen separate boundary witnesses is now a `pop` that satisfies the
  drop-last law (the witness `popImpl` also returns the last element), and the shape carries `LawPop` as well as the totality, bound to the
  real `Vec::pop` by `Iff.rfl`. The function that returns and leaves the vector unchanged satisfies
  `VecPopShape` and not the law. The coverage theorem still names all thirteen witnesses. These thirteen
  witnesses are separate, one for each contract of the first Session proof layer; that the contracts hold together is the joint model.

Each result is pinned under `#guard_msgs`, and `attest.py` requires every one of these pins (`REQUIRED_PINS`), so
deleting one fails it. The pins of the results about `Interp.real` and the records list the 49 interpreted
constants and the error type inside `RngCore`; the pins of the results about the model list the three standard
axioms and that error type. None depends on a compiler-trust axiom. The pins hold axiom lists, not statements.
The statements of `axiom_base_satisfiable`, `axiom_base_satisfiable_for_total_rng` and `records_of_axiom_base`
(in `UnitSatisfiabilityRecords.lean`) and of `vec_pop_satisfiable` (in `UnitSatisfiabilitySession.lean`) are pinned by
`#guard_msgs in #check`, and `attest.py` requires each of those four pins to exist as an active `#guard_msgs in #check`
whose options still compare the printed message (`REQUIRED_STATEMENT_PINS`). It does not read what a pin says, so a
statement weakened together with its pin's expected message is accepted by that check, and only the build, which compares
the text, and the diff of the pin show it. No other statement in these modules is held, so a weaker statement that
keeps its axiom list is not refused. What the pins do not hold is the classification itself, which fields are axiom-level and which are about
translated functions: the audit text in `tacenta-proofs/scripts/check-session-satisfiability-negatives.sh`
checks it against the elaborated environment, and it runs there and not in `lake build`, because `check-lean-constructs.sh` refuses elaboration-time code in the translation
package.

## Proved (the translated erasure coder of the Session unit refines the model: `ErasureAgrees`)

Location: `Translation/UnitErasureRsStatements.lean`, `Translation/UnitErasureRsGlue.lean`.

The proofs are in `UnitErasureRsDefs.lean` (the specification functions), `UnitErasureRsKernel.lean`, `UnitErasureRsAlgebra.lean`, `UnitErasureRsModel.lean`, `UnitErasureRsEncoder.lean` and `UnitErasureRsDecoder.lean`; the statements module restates each of the nine and the glue assembles them.

In the complete Session unit the erasure coder is translated Rust, so `ErasureAgrees`, the hypothesis of the four
Braid refinement theorems, is a statement about definitions: `Encoder::new` of any message and `Decoder::new` of any
size build values that refine the model's encoder and decoder (`Model.Braid.encode`, `Model.Braid.Decoder.new`), the
decoder for every message the model decoder could still be collecting. Its encoder clause was a theorem already
(`erasureAgrees_encoder`); the decoder clause needed that decoding the codewords of a message at distinct indices
returns the message, which no theorem of the model stated before `M_recover`. The proof is cut into nine statements,
proved independently and restated in `UnitErasureRsStatements.lean` so that the kernel checks that each proved
theorem has exactly the statement the glue was written against.

- `K_weights`, `K_coefficients`, `K_evaluate`: the translated barycentric kernels `weights`, `coefficients` and
  `evaluate` compute their pure specifications over `Model.Gf65536.Elem`, for every input slice. The field part
  carries the argument of `ErasureT3.lean` over to the unit's constants.
- `K_algebra`: the Lagrange evaluation they compute is `Model.Polynomial.interp` for distinct nodes.
- `E_new`, `E_next`: `Encoder::new` builds the padded chunks of `Model.Erasure.chunks`, and `next_chunk` emits
  `Model.Erasure.codeword` at the index `next`.
- `D_add`, `D_message`: `Decoder::add_chunk` refines `Model.Erasure.Decoder.add`, and `Decoder::message` refines
  `Model.Erasure.Decoder.message`.
- `M_recover`: `Model.Erasure.Decoder.message` of the codewords of a message at distinct indices is the message.
- `erasureAgrees_decoder`, `erasureAgrees`: the decoder clause, and `ErasureAgrees`, under the two laws
  `DivCeilValue` and `TruncatePrefix`. The proof carries a decoder invariant (`DInv`) over every sequence of
  chunks (`dinv_add`): a duplicate index, and a chunk offered after the decoder is complete, change nothing the
  message depends on, and a decoder that holds fewer chunks than it needs returns no message in the translation
  and in the model (`message_not_full`), which covers a decoder sized for `usize::MAX` bytes. The statements hold
  at both platform widths, because the proofs use only that `Usize.max` is at least `2^32 - 1`.

Each is pinned under `#guard_msgs` (axioms and statement), and `attest.py` requires every axiom pin; the statement
pins are held by the build alone (see the section on the Braid agreements). The axiom pins list
`propext`, `Classical.choice` and `Quot.sound`, and the two opaque constants the laws are about (`usize::div_ceil` in
`E_new` and `erasureAgrees`, `Vec::truncate` in `D_message` and the glue); none depends on a compiler-trust axiom.
The proof of the statements through the field used compiler-trust axioms (about fifty `bv_decide` and `native_decide`
certificates in the model's field lemmas) until the field lemmas became kernel proofs (the section on the field
above).

What this does not show: that the real `usize::div_ceil` and `Vec::truncate` meet the two laws (they are the
documented behaviour of the standard library functions, and both hold in one interpretation of the unit's opaque
constants, `UnitSatisfiabilityBraidAgreements.lean`); and anything about `Vec::with_capacity`, which never fails in
the translation where the real function panics for an absurd capacity, so the results are about the translation. The
laws are the whole interface between this proof and the standard library.

## Proved (the Braid refinement agreements of the Session unit: a model, the hypotheses that have witnesses, and what is discharged)

Location: `Translation/UnitSatisfiabilityBraidAgreements.lean`, `Translation/UnitSatisfiabilityErasureAgrees.lean`, `Translation/UnitSatisfiabilityBraidStates.lean`, `Translation/UnitBraidEntryPoints.lean`.

`step_send_refines`, `Braid.send_refines`, `step_receive_refines` and `Braid.receive_refines` of the complete
Session unit (`SessionUnitBraidT3.lean`) take, besides the contract fields: six agreements about
the unit's opaque KEM and KDF constants (`KemAgreesFor`, `KemLenAgrees`, `ValidateEkAgrees`, `KemCloneAgrees`,
`BraidHkdfAgrees`, `BraidHmacAgrees`), thirteen totality or size shapes, six statements about the translated
erasure coder, and the hypotheses about the state and the message (`StateRefines`, `EncodersLive`, `ct1_bounded`,
`decoders_bounded`, the epoch headroom, `MsgRefines` and `HonestChunk`). The standalone witnesses
(`KemWitness.lean`, `Satisfiability.lean`) are about the constants of the standalone Braid translation, which
are different Lean constants, so before these modules none of the six agreements, none of the state-level
hypotheses and neither erasure agreement had a witness for the unit. The sense of "has a model" is the
substitution argument of the section above and no other: a derivation of `False` from statements about
uninterpreted constants would become one from facts that hold in the model, which is an argument about
derivations and not a theorem inside Lean. Nothing here is shown of the real ML-KEM wrapper, libcrux or the
real KDF: the six agreements are assumed, and `LIMITATIONS.md` records where.

- `braid_agreement_shapes_are_predicates`: each of the six agreements, and the law `TruncatePrefix`, is at
  `Interp.real` the shape over an interpretation that replaces it. Each bridge is `Iff.rfl`, so the kernel
  checks that the shape unfolds to the very proposition the refinement theorems take. A shape that differs
  from the predicate by a constant or a premise is rejected: `check-braid-agreement-negatives.sh` makes
  such changes one at a time and requires the bridge to fail, and requires this theorem to name every
  `_is` bridge of the module.
- `braid_agreements_have_a_model`: one interpretation, `Interp.modelT3`, a conservative extension of
  `Interp.model` that changes only the KEM family, the two KDFs and their sizes, satisfies the six agreements
  (at `Model.Braid.toyKem`, because `K` is existential in `KemAgreesFor K`), the 33 axiom-level shapes of the
  session records, the laws of `StdLaws` and `TruncatePrefix`. So the agreements are consistent with each
  other and with every axiom-level contract field. The proofs hold on both platform widths: they use only
  that `Usize.max` is at least `2^32 - 1`. `ValidateEkAgrees K` holds of the real call only for a `K` whose
  `hashEk` folds in the coefficient check that `validate_ek` makes after the hash; such a `K` exists because
  `K` is existential. The interpretation also satisfies `KemDrawsSucceedShape`, so the one premise the
  state witnesses add is in the same model as the agreements rather than shown separately.
- `modelT3_kemDrawsSucceed`: `Interp.modelT3` satisfies `KemDrawsSucceedShape`: its key generation and
  first encapsulation half each return `Ok` for some RNG. Together with `KemDrawsSucceed_is`, the
  `Iff.rfl` bridge to the real-constant premise, this is what puts the state witnesses' extra premise
  inside the model above. It says nothing about the real wrapper.
- `erasureCloneAgrees`: `ErasureCloneAgrees` is a theorem of the translated unit, outright: a clone of an
  encoder or a decoder equals it. No law about an opaque constant is used.
- `erasureAgrees_iff_clauses`, `erasureAgrees_encoder`: `ErasureAgrees` is its encoder clause and its decoder
  clause, by `Iff.rfl`, and the encoder clause is a theorem given that `usize::div_ceil` returns at divisor 32
  (`DivCeil32`, which `DivCeilValue` implies): `Encoder::new` of any message refines the model encoder of the
  same bytes, for every number of steps a `u16` index allows. The decoder clause is the section above.
- `ingredients`, `twelve_states`, `six_receive_witnesses`: given `ErasureAgrees`, `KemAgreesFor K`,
  `KemLenAgrees K`, `KemDrawsSucceed`, `DivCeilValue` and the three size shapes the receive records carry, every one of the twelve
  state constructors has a real state and a model state satisfying `StateRefines`, `ct1_bounded`,
  `decoders_bounded`, the epoch headroom and `EncodersLive` at once (`Good`, which `Good_iff` unfolds), and
  each of the six state and message-type pairs in which `Model.Braid.receive` feeds a chunk to a decoder has
  a message satisfying `MsgRefines` and `HonestChunk`, in the state's epoch, with data, and not through the
  vacuous arm of `HonestChunk`. The witnesses are built from the agreements and one more premise: the key
  pairs and encapsulation states from `KemDrawsSucceed`, that the real `generate` and `encapsulate1` each
  succeed for some RNG (the two-sided `KemAgreesFor` alone admits a KEM that refuses every call), related to
  the model through the success arms of `KemAgreesFor`; the encoders and decoders from the two clauses of
  `ErasureAgrees` (discharged under the two laws by `twelve_states_of_laws`). So these hypotheses are
  satisfiable together whenever the agreements and `KemDrawsSucceed` are, and a model of them is the one
  above (`modelT3_kemDrawsSucceed`). `KemDrawsSucceed` is assumed of the real wrapper, not proved.
- `initiator_refines`, `responder_refines`: the states `Braid::initiator` and `Braid::responder` build refine
  the model's initial states `Model.Braid.initAlice` and `Model.Braid.initBob` and satisfy `ct1_bounded`,
  `decoders_bounded`, the epoch headroom and `EncodersLive`, so `hrel` holds of an honest fresh state and not
  only of a state built to satisfy it. The responder's decoder is the one `ErasureAgrees` provides for the
  header size.
- `defined_hypotheses_given_erasure`, `Braid.receive_refines_given_erasure`, `Braid.send_refines_given_erasure`: the
  receive takes six hypotheses about translated functions and the send takes four of them (`ErasureAgrees`,
  `ErasureCloneAgrees`, `EncoderCloneTotal`, `DecoderCloneTotal`); `DecoderAddChunkTotal` and `DecoderMessageTotal`
  occur only in the receive. All but `ErasureAgrees` are theorems: `ErasureCloneAgrees`, `DecoderAddChunkTotal`,
  `EncoderCloneTotal` and `DecoderCloneTotal` outright, and the bounded `DecoderMessageTotal` from the one
  law `TruncateTotal` (`Vec::truncate` returns). The two entry points are restated with those hypotheses
  replaced: the send needs no law, the receive needs `TruncateTotal`, and `ErasureAgrees` stays a premise. No
  statement of `SessionUnitBraidT3.lean` changed; each restatement is a corollary of the entry point it
  restates, with fewer premises.
- `defined_hypotheses_of_laws`, `Braid.receive_refines_of_laws`, `Braid.send_refines_of_laws`: with
  `ErasureAgrees` from the section above, all six hypotheses of the receive and all four of the send are theorems
  under the two laws `DivCeilValue` and `TruncatePrefix`, and the two entry points are restated with them replaced
  by the laws.
  What remains of their hypotheses is what a model of the unit's opaque constants can satisfy (the six agreements and
  the totality shapes), the two laws, and the hypotheses about state and message.
- `twelve_states_of_laws`, `six_receive_witnesses_of_laws`: the state witnesses with `ErasureAgrees` supplied by the
  laws, so the hypotheses of `Braid.receive_refines_of_laws` are satisfiable together under the agreements,
  `KemDrawsSucceed` and the two laws alone. With `braid_agreements_have_a_model`, no hypothesis of the four refinement theorems is left
  without a witness for the unit, in the sense of the substitution argument. The state and message witnesses are
  derived from the agreements and the two laws, so they exist in the model because the agreements hold there;
  the step from the model to the real constants is the substitution argument and not a theorem inside Lean.

Each result is pinned under `#guard_msgs`, and `attest.py` requires every one of these axiom pins
(`REQUIRED_PINS`), so deleting one fails it. The pins of `braid_agreement_shapes_are_predicates` and the entry
points list the opaque constants their statements mention; none depends on a compiler-trust axiom. The statements
of every claimed theorem here are pinned by `#guard_msgs in #check`, and so are `Good_iff` and `RecvWitness_iff`,
which unfold the two definitions the state theorems are stated through, and the three definitions that fix which
constructor and which message pair each witness is for (`stateTag`, `modelTag`, `FeedsDecoder`, by
`#guard_msgs in #print`). Those statement pins are held by the build alone: `attest.py` reads the axiom pins, so
deleting a statement pin, or weakening a statement together with its pin, is refused by no gate. A statement
weakened without its pin is refused by the build, and `check-braid-agreement-negatives.sh` shows it in five of the
modules (the four of this section and the glue).

What these results do not show: that the real KEM and KDF meet the six agreements; that a send or a receive
keeps `ct1_bounded`, `decoders_bounded`, `EncodersLive` or the epoch headroom (the witnesses are single steps
and a run is not shown to stay inside the hypotheses); that `MsgRefines` and `HonestChunk` hold of a message
a peer sends (`MsgRefines` holds of a real chunk of any content when the decoder needs at least one chunk, so
`HonestChunk` is the only hypothesis that excludes a spliced stream); that a decoder restored by
`Decoder::from_bytes` refines a model decoder (one that holds chunks of no common message refines none, so the
refinement theorems apply to states reachable from a fresh Braid and to restored states equal to such a state);
and that the witnesses reach a state with the relation hypotheses over values of a real ML-KEM key pair, because
the key pairs are the ones the agreements provide, under `KemDrawsSucceed` (assumed of the real wrapper, not proved).

## Proved (why three Session contract fields are stated at the unit's instances)

Location: `Translation/UnitSatisfiabilityZeroizeScope.lean`.

`SessionUnitSpqrT1.ZeroizeTotal`, `SessionUnitBraidT1.ArrayZeroizeTotal` and the `Vec::zeroize` conjunct of
`SessionUnitSpqrT1.VecRetainTotal` are stated at the instances the Session unit passes to `Array::zeroize` and
`Vec::zeroize`: the blanket `u8` instance on a 32-byte array, and the chain table (`Vec<(u64, Chains)>`), the sparse
skipped-key store (`Vec<Skipped>`) and the classical one (`Vec<SkippedKey>`). A walk of the elaborated definitions of
`TacentaSessionUnit.lean` finds 34 calls of `Array::zeroize`, all at that instance and width, and 5 of `Vec::zeroize`,
at those three instances (2, 2 and 1); the walk is kept outside this tree, was run when the fields were restated, and no gate
repeats it, so the count is a reading, not a check. Before,
the three said the operations return for every `Zeroize` record, including one whose `zeroize` fails, which the real
functions, which call the record's `zeroize` on each element, do not support. That the real functions return at the
unit's instances is assumed (`LIMITATIONS.md`). The statements of the three fields are pinned by `#print` in this module
and `attest.py` requires the pins (`REQUIRED_STATEMENT_PINS`, `REQUIRED_PRINT_FORM`).

- `zeroize_failure_propagation_conflicts`, `braid_zeroize_failure_propagation_conflicts`,
  `vec_zeroize_failure_propagation_conflicts`: no interpretation satisfies the general form a field had
  (`SpqrZeroizeUnscopedShape`, `ArrayZeroizeUnscopedShape`, `VecZeroizeUnscopedShape`) and also lets the operation
  propagate the failure of a failing instance, which is what the real function does. They are kept as the record of
  why the fields were restated.
- `spqrZeroize_of_unscoped`, `arrayZeroize_of_unscoped`, `vecRetainAxiom_of_unscoped`: over every interpretation,
  each general form implies the field's shape as now stated, so the restatement weakens a hypothesis of every theorem
  that takes the records and strengthens no result.
- `arrayZeroizeScoped_of_total`: the general form of `ZeroizeTotal` implies the form with the premise that the
  instance's `zeroize` returns on every element.
- `faithful_propagates`, `faithful_vec_propagates`, `faithful_refutes_unscoped`, `faithful_satisfies_all_axiom_shapes`:
  a second interpretation implements `Array::zeroize`, `Vec::zeroize` and the pair `Zeroize` as the crate does
  (zeroize each element in order, fail if one fails; `Vec::zeroize` leaves an empty vector). It propagates a failing
  element's failure through `Array::zeroize` and `Vec::zeroize`, falsifies the general form of `ZeroizeTotal`, and
  satisfies every axiom-level shape of the joint model, the three restated fields among them, both model classes and
  `StdLaws`. Like the joint model it is a model of the shapes: the blanket `Zeroize` is the identity, and nothing here
  shows that the real functions satisfy any of it.
- `faithful_SpqrSessionLaws`: the same interpretation satisfies the five laws the Session unit's two sparse agreements are
  derived from (`UnitSatisfiabilitySpqrSessionLaws.SpqrSessionLawsShape`, the next section), so they are not met only by
  a wipe that ignores its instance record. It rests on no axiom of the unit but `rand_core`'s error type.

This section was made by its author with tool assistance and read by tool-assisted readers working for the maintainer; no reader independent of the maintainer has read it.

## Proved (the Session unit's two sparse agreements, from named laws about opaque operations)

Location: `Translation/UnitSatisfiabilitySpqrSessionLaws.lean`.

`SessionUnitSpqrT3.VecRetainAgrees` and `SessionUnitSpqrT3.RemoveSkippedAtAgrees` are statements about functions the
Session unit translates with a body: that `State::set_chains` and `State::clear_old_epochs` return a state related to the
model's `setChains` and `clearOldEpochs`, and that `State::remove_skipped_at`, at an in-range index, returns the key at
that index and the vector with that index erased. A model of the opaque constants cannot change what they say. The
results below show both follow, by stepping through the translated code, from five laws about the opaque constants the
bodies reach. The proofs are the three-leaf unit's (`UnitSatisfiabilityTripleLaws.lean`) under the Session unit's
constants, built on the removal and loop specifications of `UnitSatisfiabilityRatchet.lean`, and are generic in the
platform width. They are results about hypotheses and not about the product: each is conditional on exactly the laws its
statement names.

The five laws are assumed, each stated once as a named definition (the copies, in `StdLaws`, `SpqrSessionLawsShape` and
the first two conjuncts of `VecRetainTotal`, are bound to it by the kernel: `spqrSessionLaws_iff` by unfolding,
`triple.vecRetain.1` passed as `LawCapacity`, `hL.pop` as `LawPop`), and none is proved of the real functions (`LIMITATIONS.md`, "The laws, as
assumptions about the real standard-library and `zeroize` functions"): `UnitSatisfiabilityRatchet.LawPop` (`Vec::pop` of a
non-empty vector returns the vector without its last element), `LawAsMut` (`Option::as_mut` returns, at every type),
`LawCapacity` (`Vec::capacity` returns), `UnitSatisfiabilityRatchet.LawVecZeroize` (`Vec::zeroize` returns at the chain
table and the two skipped-key stores; not the general `LawVecZeroize` of the leaf crate and the three-leaf unit) and
`SessionUnitSpqrT1.ZeroizeTotal` (`Array::zeroize` returns at the blanket `u8` instance on a
32-byte array). The last three are fields of `DecryptRatchetContracts` (`ZeroizeTotal`, and the first two conjuncts of
`VecRetainTotal`); `LawPop` and `LawAsMut` are stated by no contract record and are fields of `DecryptRatchetAgreements`.

- `removeSkippedAtAgrees_of_laws`: `RemoveSkippedAtAgrees`, from `ZeroizeTotal` and `LawPop`. Its pin lists
  `Array::zeroize`, `Vec::pop` and the blanket `Zeroize`.
- `setChainsAgrees`, `clearOldEpochsAgrees`, `vecRetainAgrees_of_laws`: the two halves of `VecRetainAgrees`, and the
  agreement from the five laws. The chain-table scans and the skipped-key scan are proved to keep exactly the entries
  their guard names, in order, and to leave the other fields of the state alone; `set_chains`' capacity copy takes
  `VecRetainTotal`, which `UnitSatisfiabilityRatchet.vecRetainTotal` builds from the laws. The pin of
  `vecRetainAgrees_of_laws` lists the seven opaque constants the five laws' statements mention: `Vec::pop`,
  `Option::as_mut`, `Vec::capacity`, `Vec::zeroize`, `Array::zeroize`, and the blanket and pair `Zeroize`.
- `sparse_agreements_of_laws`: both agreements from the bundle `SpqrSessionLaws` of the five laws.
- `spqrSessionLaws_iff`, `spqrSessionLawsShape_of_parts`, `spqrSessionLaws_model`: the five laws as a shape over an
  interpretation of the unit's opaque constants (`SpqrSessionLawsShape`, reusing `UnitSatisfiabilityJoint`'s
  `VecRetainAxiomShape` and `SpqrZeroizeShape` and stating `pop` and `asMut` as `StdLaws` does), bound to the bundle at
  `Interp.real` (the kernel accepts the binding only if the two unfold to the same propositions), and met by
  `Interp.model`, the interpretation in which every axiom-level field of the four contract records holds. So the five
  laws are consistent with each other and with those fields in the substitution sense of `UnitSatisfiabilityJoint.lean`,
  an argument about derivations and not a theorem inside Lean. `UnitSatisfiabilityZeroizeScope.faithful_SpqrSessionLaws`
  (the previous section) gives a second interpretation that meets them. The binding's pin lists the 49 interpreted
  constants and `rand_core`'s error type; the model's lists only the error type.
- `spqrSessionLawsShape_fails_of_noop_pop`: an interpretation whose `Vec::pop` returns every vector unchanged fails the
  shape, so the shape is not met by every interpretation.

None rests on a compiler-trust axiom; each carries an axiom pin and a statement pin that `attest.py` requires, and the
bundle, the shape and the four laws of `UnitSatisfiabilityRatchet.lean` carry `#print` pins it requires in that form.
`check-session-satisfiability-negatives.sh` refuses each law removed from the bundle, each weakened where
`vecRetainAgrees_of_laws` takes it (`Vec::pop` only returning, `Option::as_mut` at one type, `Vec::capacity` at one element
type, `Vec::zeroize` without the chain table, `Array::zeroize` at 16 bytes), each field of the shape dropped and its pop
law weakened (refused by the binding), and the model witness removed (refused by its pins). This section was
made by its author with tool assistance and read by tool-assisted readers working for the maintainer; no reader independent of the maintainer has read it.

What is not shown. That the real `Vec::pop`, `Option::as_mut`, `Vec::capacity`, `Vec::zeroize` and `Array::zeroize` satisfy
the laws. That the theorems that still take the two agreements as hypotheses (the Session unit's sparse refinement
theorems, `SessionUnitTripleT3`'s discharged theorems, the loop theorems of the `decrypt_ratchet` section, the refusal
theorems of the section after it, and `TripleSendRefinementContracts`) hold under the laws instead: none of their
statements is changed. Only `DecryptRatchetAgreements` and the two screen theorems that build it
(`decrypt_ratchet_refines_from_shapes`, `decrypt_ratchet_refines_from_shapes_at_eviction`) moved from the agreements to
the laws. `check-hypothesis-witnesses.sh` does not read the Session unit.

## Proved (a negative result: five evidence hypotheses and records of the lifecycle dispatch layer are false or empty)

Location: `Translation/DispatchEvidenceVacuity.lean`.

`UnitLifecycleT3.lean` and `UnitLifecycleInitialDispatch.lean` state refinement lemmas for the
eight-leaf session unit's `encrypt` and `decrypt` as conditional on hypotheses and on evidence
records. These results are about those hypotheses and records, not about the product. They show
that five of them are false or empty under the conditions stated in the bullets below. When they were
added, seventeen theorem statements of the two modules took one of them. Since the restatement of three
records and the integration of the session contract branch, no theorem of the two modules takes any of
the five, nor the old KEM field of the last bullet: each is kept unchanged, with a doc comment naming
its replacement, so that these results still elaborate (`GAP-REGISTER.md`, row
`DISPATCH-EVIDENCE-VACUITY`, says what replaced each and what is still open). A gate holds the five
records of the first four bullets untaken: `scripts/check-refuted-records.sh`, run by `no-sorry.sh`,
runs the walk `Model.AxiomAudit.takersReport` as a compiled executable (`refuted-records`, the
model package) once per translation audit module, loading that module and so its import closure at
run time. The walk lists from the loaded environment every first-party declaration whose statement
or value names one of the five, or a constant the `structure` command declared for it (constructor,
recursor, `casesOn`, `recOn`, projections, flat constructor), and refuses unless the list is exactly
the declarations it is given; the script then compares the printed lines with a recorded block
(over the Session unit's closure: the five records' modules and fifteen theorems of this module;
over the other four closures: every record absent). The executable's source is compiled once from
`Model/AxiomAudit.lean`, so nothing a module of the tree declares is parsed where the walk is
called; the modules it loads are data to it and their initializers are not run (`importModules`
with its default `loadExts := false`); and the script reads the executable's output rather than a
build log, so a line a module prints at build time is
not read. Every translation module is in some audit module's closure (`check-audit-reach.sh`,
whose lists of audit modules and of first-party roots the script holds itself to; the three
lakefiles are pinned by content in `check-lean-constructs.sh`, so no library, glob or root is added
without a reviewed diff), so the five runs walk
them all, and a declaration that names a record or its machinery, or an alias of a record, fails
the gate whatever its spelling. Adding a theorem of this module to the recorded block is a
diff only review catches. What the walk does not see: a theorem that restates the body of the `def`
record `InitialSameEphemeralEvidence` without naming it (it takes the proposition, not the record),
a mention in a comment or a string (not a declaration), and an `example` (no constant; nothing can
take an example). A declaration that takes an alias is not itself listed, the alias is. The
refutations' statements are held by `attest.py`'s pins; the lemma `source_of_record`, listed with
them, has no statement pin. The gate says nothing about the records that replaced the five, nor
about the KEM field of the last bullet. The
last bullet is a sixth point and not a refutation.

- `same_ephemeral_agreement_empty`, `initialSameEphemeralEvidence_false`: the translated
  `same_ephemeral_agreement` returns `false` on two empty byte strings, because `decode_ec`
  refuses a string whose length is not 33, so `InitialSameEphemeralEvidence`, which asks for `true`
  on every pair of equal byte strings, is false for every `dh`, `oracle`, `real` and `model`. The
  proof uses no hypothesis and no law. No theorem takes it now: the dispatch theorems take the
  per-branch `InitialDispatchBranchEvidence` instead.
- `codewordViewOf_false`, `codewordViewOf_false_of_encoderNewTotal`: if `Encoder::new` returns on
  two messages of one length `n` of at least 33 bytes that agree on their first 32 bytes and differ
  at byte 32, no view satisfies `CodewordViewOf`, because both messages have the same codeword at
  index 0 and the `receive` clause asks the view to name the one source it came from. The first
  theorem takes the two returns; the second takes `EncoderNewTotal`, the field `encoderNew` of the
  encrypt contract records, which `UnitSatisfiabilityErasure.encoderNew_iff` shows equivalent to
  the law that `usize::div_ceil` returns at divisor 32, and uses `n = 33`. No theorem takes
  `CodewordViewOf` now; the encrypt-side theorems take its send direction, `CodewordViewSendOf`
  (`UnitLifecycleT3.lean`). When ten theorems took it, none of them took `EncoderNewTotal`, so
  for them the result rested on that law, which no theorem proves of the opaque constant.
- `record_empty_of_nonempty_decoder`, `record_empty_headerSent`, `record_empty_ekSentCt1Received`,
  `record_empty_noHeaderReceived`, `record_empty_ct1Sampled_ek`, `record_empty_ct1Sampled_ekCt1Ack`,
  `record_empty_ct1Acknowledged`: `InitialRatchetBraidEvidenceContracts` has no term when the model
  Braid, with its epoch below 2^64, is in one of the six state and message-type pairs for which
  `Model.Braid.receive` feeds a chunk to an existing decoder and that decoder holds a chunk. The
  record quantifies over every incoming
  composite, and two chunks that differ at index 0 cannot both be codewords of the one source the
  held chunk carries. The first theorem is the general statement and the other six are its
  instances. The record is not decided for a state whose decoder is empty or that is outside the six.
- `keysSampled_receive_ct1_holds_chunk`: the model Braid in `keysSampled` that receives a ct1 chunk
  moves to `headerSent` with that chunk in its decoder (transition (2) of `Model.Braid.receive`),
  so the hypotheses of `record_empty_headerSent` are met by a state one receive step from
  `keysSampled`.
- `tripleConcreteEvidence_forces_constant_dhPublic`, `aeadConcreteEvidence_forces_constant_dhPublic`:
  `InitialRatchetTripleConcreteEvidence` and `InitialRatchetAeadConcreteEvidence`, given a prefix of
  the refusal run, force the oracle's `dhPublic` to be constant, because their field
  `hmodelPublic` equates the run's new public key with `oracle.dhPublic draw` for every draw and the
  run consumed one.
- `constant_dhPublic_false_of_publicKeyNotConstant`,
  `tripleConcreteEvidence_false_of_publicKeyNotConstant`,
  `aeadConcreteEvidence_false_of_publicKeyNotConstant`: a constant `dhPublic` contradicts
  `PublicKeyNotConstant`, given the DH codec and the oracle's `dhPublic` clause, so neither record
  holds for a refusal run that has a prefix. `PublicKeyNotConstant` says that two 32-byte private
  keys have different public keys under the real `PrivateKey::public_key`. It is not proved:
  `public_key` is an opaque constant. It is tested, at the two RFC 7748 section 6.1 private keys, by
  `the_fixed_secrets_have_the_table_keys` in `tacenta-core/tests/identity_boundary.rs`. These three
  results are conditional on it, on the codec and on the clause, and none of the three is shown
  satisfiable inside Lean.
- `oracleOf_kem_oracle_never_refuses`, `oracleOf_kem_call_never_errs`: the KEM success clause
  `OracleOf` had before it was restated, kept as `KemEncapsulateUnguarded`, makes the model's KEM oracle
  accept every public key at every draw that a trace has, and the translated `encapsulate` never
  return `Err` while the trace has a draw. This is not a refutation, because `encapsulate` is an
  opaque constant: the shipped function returns `Err` on a key of the wrong length (tested by
  `malformed_inputs_are_rejected`) and on a key that fails `validate_public_key` (read from
  `tacenta-core/boundary/src/kem.rs`; `GAP-REGISTER.md`, row `E2E-04`). The two statements took
  `OracleOf` before the restatement and take the kept field now, which is the old field's text
  unchanged; their statement pins and axiom pins changed with them, which makes them two of the three
  pinned statements the integration of the session contract branch changed (the third is
  `Tacenta.SpqrT3.skip_message_keys_refines`, above). `OracleOf` asks for success only where the
  model's `kemEncaps` returns `some`.

No step of these proofs case-splits on the width of `usize`, and the only facts they use about
`Usize.max` are the bounds Aeneas proves for the platform constant. `System.Platform.numBits` is an
opaque constant of the kernel whose value is 32 or 64, so a proof that does not choose between the
two holds for both. Each of the nineteen results is pinned under `#guard_msgs` twice at the end of the
file, once as an axiom list and once as its statement (`#check`), and `attest.py` requires every axiom
pin (`REQUIRED_PINS`), so deleting one fails it. The build compares the text of each statement pin, and
`attest.py` requires each of the nineteen to exist as an active `#guard_msgs in #check` whose options still compare the
printed message (`REQUIRED_STATEMENT_PINS`), so deleting one, commenting one out, removing its `#guard_msgs`, nesting it
under another `... in` or giving it an option such as `(drop info)` fails it; removing its expected message fails the
build, not this check. `attest.py` does not read what a statement pin says, so a statement that is weakened together with
its pin's expected message is accepted by this check, and only the build, which compares the text, and the diff of the
pin show it; a pin holds the printed statement, in which a definition appears by name, so changing a definition changes
no pin unless the definition has its own `#print` pin. The axiom lists name the opaque constants that the statements mention,
directly or through the definitions they unfold, and the proofs use none of them as assumptions;
`keysSampled_receive_ct1_holds_chunk` mentions none and lists the three standard axioms only. None
depends on a compiler-trust axiom. These results repair nothing, and they do not show that any other
hypothesis of the two modules can be met.

## Proved (the lifecycle headroom records are satisfiable, and what `Session::invariant` gives)

Location: `Translation/UnitHeadroomSatisfiable.lean`, `Translation/UnitHeadroomInvariant.lean`.

`EncryptHeadroom`, `DecryptRatchetHeadroom`, `EstablishInitiatorHeadroom` and `EstablishResponderHeadroom` are the
conditions on the input of the five lifecycle T1 theorems that are not contracts about primitives, and
`InvariantPreconditions` is what `invariant_gives_preconditions` concludes from `Session::invariant`; a theorem whose
hypothesis no input meets is true and empty. These results show that each is met by some input, say exactly which
numeric bounds they are, and show what `Session::invariant` gives.

The sense. The lifecycle types are built from opaque types of the unit, and no closed value of any of them exists in the
real environment: Lean cannot show that `tacenta_boundary::dh::PrivateKey` is inhabited, and an interpretation in which
it is empty, which is by reading and not by a theorem here, satisfies the unit's axioms (and falsifies `DhCodecTotal`). So every witness takes values of those types as arguments. For `PrivateKey`
and `PublicKeyBytes` the values come from `DhCodecTotal`, a field of all four contract records. For `PrekeyStore`, the
wrapper around the one-time prekey vector comes from the class `DerivedKeysModel`, which `establish_responder_no_panic`
takes as an instance argument. One more value is needed, a `kem::KeyPair`, and, by reading, no record gives it:
`HeadroomInhabitants` states it as one more assumption over an interpretation of the opaque constants. The session that
passes `Session::invariant` needs two further assumptions that no record states (`ValidKeyShape`, `OptionEqU64Shape`).
Each assumption is a statement over the opaque constants, bound to the real ones by `Iff.rfl`. The joint model satisfies
`HeadroomInhabitants` and `ValidKeyShape`. `OptionEqU64Shape` is about a constant the joint model does not interpret and no
record reaches, and a Lean function of the same type satisfies it. That is the substitution argument of the section "Proved
(one interpretation of the unit's opaque constants, and the four records from it)" again, with `PrivateKey`, `PublicKeyBytes`
and the wrapper around the one-time prekey vector inhabited by the contract records, and these three statements in the base:
an argument about derivations and not a theorem inside Lean, and not a statement that the real `PrivateKey` has a value
or that the real primitives satisfy the assumptions. The exact residual is in `LIMITATIONS.md`.

- `usize_max_ge`, `plaintext_bound_at_widths`: `Usize.max` is at least `2^32 - 1` (from `Usize.bounds_eq`, so at both
  platform widths), and the plaintext bound of `EncryptHeadroom` admits exactly the lengths up to `2^32 - 151` on a 32-bit
  target and `2^64 - 151` on a 64-bit target.
- `freshTriple_headroom`, `freshBraid_bounds`: a Triple state built from concrete values (no skipped keys, one chain-table
  entry) meets `ReceiveHeadroom`, whose bounds are `MAX_SKIPPED_STORE + MAX_SKIP = 3000` and a chain table of one entry; a
  Braid in `KeysUnsampled`, which holds no decoder, ciphertext or KEM value, meets `ct1_bounded` and `decoders_bounded`.
- `decryptHeadroom_sessionOf_iff`, `invariantPreconditions_sessionOf`, `encryptHeadroom_sessionOf_iff`: for a session over
  those states, `DecryptRatchetHeadroom` is exactly the bound `associated_data.length + 106 <= Usize.max`, `InvariantPreconditions`
  holds outright, and `EncryptHeadroom` is exactly that bound, the plaintext bound `102 + (plaintext.length + 48) <= Usize.max`
  and, when an initial message is pending, `33 + 33 + ciphertext.length + (102 + (plaintext.length + 48)) + 18 <= Usize.max`.
- `initiatorHeadroom_iff`, `responderHeadroom_iff`: `EstablishInitiatorHeadroom` is exactly `kem_prekey.length < Usize.max`
  and `EstablishResponderHeadroom` exactly `last_resort_seen.length < Usize.max`: each is a single bound that fails only at
  the largest length a Lean vector can have (a Rust allocation is smaller; see the controls below).
- `decryptHeadroom_satisfiable`, `encryptHeadroom_satisfiable`, `encryptHeadroom_satisfiable_pending`,
  `initiatorHeadroom_satisfiable`, `responderHeadroom_satisfiable`: witnesses. Given a private key and a public key, a
  session over fresh states meets `DecryptRatchetHeadroom` and `InvariantPreconditions` for associated data of at most
  `2^32 - 107` bytes and meets `EncryptHeadroom`, with no pending initial message for every plaintext its own bound admits
  and with one (an empty ciphertext) for every plaintext of at most `Usize.max - 234` bytes; a bundle meets `EstablishInitiatorHeadroom` for a prekey of at most `2^32 - 2` bytes; a store, given a
  key pair and a wrapper around the one-time prekey vector as well, meets `EstablishResponderHeadroom`. None of the sessions is claimed to pass
  `Session::invariant` here.
- `initiatorHeadroom_not_trivial`, `responderHeadroom_not_trivial`, `decryptHeadroom_not_trivial`,
  `encryptHeadroom_not_trivial`: controls. Each record is false of some input (a vector of length `Usize.max`), so the
  witnesses above do not show a record that holds of everything. The controls hold of the Lean types, whose vector lengths
  run up to `Usize.max`. A Rust allocation is at most `isize::MAX` bytes, so no real vector has such a length, and every
  bound on one length (all of `ReceiveHeadroom`, the associated-data bound, the plaintext bound, both establishment bounds)
  holds of every real input. That is by reading and not a theorem, because the Aeneas `Vec` carries no `isize::MAX` bound. The
  pending-message arm of `EncryptHeadroom` bounds a sum of two lengths, which that limit alone does not settle on a 32-bit
  target. The fields that are facts about a state and not about a size are `ct1_bounded` and `decoders_bounded`, which
  `Session::invariant` supplies.
- `nonempty_privateKey_of_dhCodec`, `nonempty_publicKey_of_dhCodec`, `nonempty_derivedZeroizing`,
  `encrypt_headroom_of_contracts`, `decrypt_headroom_of_contracts`, `initiator_headroom_of_contracts`,
  `responder_headroom_of_contracts`: `DhCodecTotal` gives a value of each of the two key types, and `DerivedKeysModel` a
  value of the wrapper around the one-time prekey vector, so, given `EncryptContracts`, `DecryptRatchetContracts` or
  `EstablishInitiatorContracts`, the matching headroom is met (the encrypt one for every plaintext its bound admits). For
  `EstablishResponderContracts` with the class, a key pair is an argument.
- `headroomInhabitants_is`, `model_headroomInhabitants`, `axiom_base_model`, `headroom_of_axiom_base`,
  `headroom_hypotheses_satisfiable`: `HeadroomInhabitants` at the real constants is the statement that `kem::KeyPair` has a
  value (`Iff.rfl`); the joint model of `UnitSatisfiabilityJoint.lean` satisfies it (`Unit`) and satisfies the axiom base at a
  concrete `RngCore`. Under the base and `HeadroomInhabitants`, each of the
  four contract records holds and the matching headroom is met, at the real constants; and the base and the assumption are
  satisfied together.
- `validKeyShape_is`, `model_validKeyShape`, `optionEqU64Shape_is`, `optionEqImpl_shape`: the two assumptions the session
  that passes the invariant needs. `ValidKeyShape` says a private key exists whose public key is canonical and of prime order
  (the identity-key rule, which the identity-key vectors check and Lean does not); `OptionEqU64Shape` says `Option::eq` on
  two `Some` values of `u64` compares them. Each is bound to the real constants by `Iff.rfl`. The joint model satisfies the
  first. The second is about `Option::eq`, which the joint model does not interpret; `optionEqImpl`, a Lean function with the
  type of `Option::eq` and the definition the standard library gives it, satisfies it.
- `structural_sessionOf`, `freshTriple_invariant`, `freshBraid_invariant`, `sessionOf_invariant`: a session over fresh states,
  with one key as both identity keys, the associated data the invariant computes, a canonical key as the ratchet public key,
  and a Braid at epoch 1, passes `Session::structural_invariant` and `Session::invariant` at the real constants, given the two
  assumptions. Both the Triple and the Braid invariant are evaluated through the translated functions; no clause is assumed.
- `emptyChainTable_fails_invariant`, `epochZero_braid_fails_invariant`, `emptyChain_headroom`, `epochZero_bounds`,
  `session_emptyChainTable_fails_invariant`, `session_epochZero_fails_invariant`: controls. A sparse-ratchet state with an
  empty chain table fails the sparse ratchet's invariant, and a Braid at epoch 0 fails `Braid::invariant`. A Triple state with
  an empty chain table meets `ReceiveHeadroom`, and a Braid at epoch 0 meets `ct1_bounded` and `decoders_bounded`. A session
  that holds either one fails `Session::invariant`. So a session that only met the headroom fields would not have been shown to
  pass `Session::invariant`.
- `structural_gives_ad`, `invariant_gives_ad_length`, `decryptHeadroom_of_invariant`, `encryptHeadroom_iff_of_invariant`:
  `Session::structural_invariant` compares the associated data with `identity_ad`, so a session that passes it, or
  `Session::invariant`, holds exactly 66 bytes of associated data (given `DhCodecTotal`). With
  `invariant_gives_preconditions` (given `Ct1LenTotal`), `DecryptRatchetHeadroom` holds of every session that passes
  `Session::invariant`, with nothing left for the caller; and for such a session `EncryptHeadroom` is exactly the plaintext
  bound and the `initial` field, which is `True` with no pending initial message and otherwise bounds the ciphertext that the
  invariant ties to the opaque `kem::ciphertext_len`.
- `invariant_session_meets_both`, `invariant_session_of_axiom_base`, `invariant_hypotheses_satisfiable`: at the real
  constants, given `DhCodecTotal`, `ValidKeyShape` and `OptionEqU64Shape`, there is a session that passes `Session::invariant`,
  has no pending initial message, meets `DecryptRatchetHeadroom` and meets `EncryptHeadroom` for every plaintext its bound
  admits. The base gives `EncryptContracts` and `DecryptRatchetContracts` and `DhCodecTotal` with them. The joint model
  satisfies the base, `HeadroomInhabitants` and `ValidKeyShape` together, and `optionEqImpl` satisfies `OptionEqU64Shape`.
  The second conjunct of `invariant_hypotheses_satisfiable` is that existence alone. It does not mention the base, because no
  record, and neither of the other two assumptions, reaches `Option::eq`, by reading: it is not among the 49 interpreted
  constants.

Each result has an axiom pin under `#guard_msgs`, and `attest.py` requires every one of the 51 (`REQUIRED_PINS`), so
deleting one fails it. An axiom pin holds the list of axioms a result depends on and not its statement, and none depends on
a compiler-trust axiom. The statements of `headroom_of_axiom_base`, `headroom_hypotheses_satisfiable`,
`responder_headroom_of_contracts`, `encrypt_headroom_of_contracts`, `decrypt_headroom_of_contracts`,
`initiator_headroom_of_contracts`, `initiatorHeadroom_iff`, `responderHeadroom_iff`, `encryptHeadroom_sessionOf_iff`,
`invariant_session_meets_both`, `invariant_session_of_axiom_base`, `invariant_hypotheses_satisfiable`,
`decryptHeadroom_of_invariant`, `encryptHeadroom_iff_of_invariant`, `sessionOf_invariant`, `emptyChain_headroom`,
`epochZero_bounds`, `session_emptyChainTable_fails_invariant` and `session_epochZero_fails_invariant` are also pinned by
`#guard_msgs in #check`, which the build holds and `attest.py` requires to exist (`REQUIRED_STATEMENT_PINS`), so deleting
one of those pins is refused; `attest.py` does not read what a pin says, so a statement changed together with its pin's
expected message is accepted. The other 32 results are held only by the build, which accepts whatever statement is written if it proves it, and
by their axiom pin, which lists axioms and not the statement, so a weaker statement of any of them that keeps its axiom list
passes every gate: `usize_max_ge`, `plaintext_bound_at_widths`, `freshTriple_headroom`, `freshBraid_bounds`,
`decryptHeadroom_sessionOf_iff`, `invariantPreconditions_sessionOf`, `decryptHeadroom_satisfiable`,
`encryptHeadroom_satisfiable`, `encryptHeadroom_satisfiable_pending`, `initiatorHeadroom_satisfiable`,
`responderHeadroom_satisfiable`, `initiatorHeadroom_not_trivial`, `responderHeadroom_not_trivial`,
`decryptHeadroom_not_trivial`, `encryptHeadroom_not_trivial`, `nonempty_privateKey_of_dhCodec`,
`nonempty_publicKey_of_dhCodec`, `nonempty_derivedZeroizing`, `headroomInhabitants_is`, `model_headroomInhabitants`,
`axiom_base_model`, `validKeyShape_is`, `model_validKeyShape`, `optionEqU64Shape_is`, `optionEqImpl_shape`,
`structural_sessionOf`, `freshTriple_invariant`, `freshBraid_invariant`, `emptyChainTable_fails_invariant`,
`epochZero_braid_fails_invariant`, `structural_gives_ad` and `invariant_gives_ad_length`.
Among them are the figures `2^32 - 151` and `2^64 - 151` of `plaintext_bound_at_widths`, `2^32 - 107` of
`decryptHeadroom_satisfiable`, `Usize.max - 234` of `encryptHeadroom_satisfiable_pending`, `2^32 - 2` of
`initiatorHeadroom_satisfiable` and the 66 bytes of `invariant_gives_ad_length`, and the four `*_not_trivial` controls. The text of the three assumptions `HeadroomInhabitants`,
`ValidKeyShape` and `OptionEqU64Shape` is held only through their bridges `headroomInhabitants_is`, `validKeyShape_is` and
`optionEqU64Shape_is`, which have axiom pins and no statement pin.
Not shown: that a store passes `PrekeyStore::invariant` or that the invariant bounds `last_resort_seen`; that a session with
a pending initial message or an established ephemeral key passes `Session::invariant`; that any session here is one
`establish_initiator` or `establish_responder` returns; that a send or a receive keeps the invariant.

## Proved (what a refused lifecycle call leaves behind, on the translated code)

Location: `Translation/UnitLifecycleAtomicity.lean`.

Seven results about the Session unit's translation of `Session::decrypt_ratchet`, `Session::decrypt`,
`Session::encrypt` and `establish_responder`. They take **no hypothesis about any opaque operation**: not a contract record,
not a headroom record, not `OracleOf`, not the model. Each quantifies over every interpretation of the unit's opaque
constants (the primitives, the random source, the key types, the standard-library calls), so none can be made empty by a
hypothesis that nothing satisfies. Each is of one form: if the call returns normally as `ok (result, state', rng')`, and the
result is a refusal (or a success), then `state'` is the state the call was given (or differs from it in the named
fields). A call that fails or does not terminate has no such result; the lifecycle T1 theorems say, under their records, that
the calls return.

- `decrypt_ratchet_err_leaves_state`, `decrypt_err_leaves_state`: a refused call returns the session it was given, every
  field. For `decrypt` that covers the initial-message dispatch, the repeat recognition and the inner receive; the one write
  after the inner receive clears `pending_initial` and is on the success path.
- `decrypt_ratchet_ok_writes`, `decrypt_ok_writes`: a successful call returns a session that differs from the given one in at
  most the Triple Ratchet, the agreement and the ratchet private key, and for `decrypt` also the pending initial message,
  which is cleared. The associated data, both identities and the established ephemeral are the ones given.
- `encrypt_err_leaves_state`: a refused call returns the session it was given, or the error is `AgreementFailed` and the
  only change is the agreement field, to a state that `Braid::failed` reports true of. That is the recorded exception, an
  agreement send that reaches the terminal state and is committed so that every later call refuses (`triple-ratchet.md`).
- `encrypt_ok_writes`: a successful call writes the Triple Ratchet and the agreement and nothing else. It never clears
  `pending_initial`: an initiator keeps wrapping its messages until a decrypt succeeds.
- `establish_responder_err_leaves_store`: a refused call returns the prekey store it was given, every field. The one-time
  removals and the replay-record append come after the inner authenticated receive.

What these do not say.

- They relate nothing to `Model.Lifecycle`. The model has the same properties of itself (`decrypt_refusal_keeps_session`,
  `establishResponder_refusal_keeps_store`, `encrypt_triple_refusal_keeps_state`); that the translated code refines the model,
  on every branch, is the open T3 work (`GAP-REGISTER.md`, row `E2E-04`). They say which error a refusal carries only by
  its being a refusal.
- They say nothing about the random source: a refused call may have drawn from it, and `rng'` is unconstrained. For
  `establish_responder` the random source is stated in "Proved (tier T3, session lifecycle: `establish_responder` over every
  input ...)": as given on a refusal before the inner receive, and otherwise the source the inner `decrypt_ratchet` returned.
- They say nothing about heap residue. The translation ignores `Drop` and `zeroize`, so what a discarded candidate state
  leaves in memory is outside them.
- They do not say what a successful `establish_responder` does to the prekey store beyond what the model and the tests say:
  which entries are removed and in which order is not proved of the code. The model now removes a consumed one-time prekey
  by moving the last entry into its slot, as the code and `session-persistence.md` do (`Model.swapRemove`;
  `GAP-REGISTER.md`, row `E2E-03`), so it can be the other side of such a theorem. The differential harness compares the real
  store bytes with `consumeOneTimeOk` for one entry that is not last, and an example in `Model/Lifecycle.lean` holds
  `consumeResponderPrekeys` for a three-entry store. What the success commit of the translated function may change, and
  that it changes nothing else, is now stated under the assumed wrapper model `DerivedKeysModel` (`responderCommit_effects`, in "Proved (tier T3, session lifecycle:
  `establish_responder` over every input ...)"); which entry a removal takes is still not proved of the code.
- They hold of the Session unit's copy of the lifecycle, which is assembled from the shipping leaf by `#[path]` and a
  count-checked copy, and of its Charon and Aeneas translation, which `LIMITATIONS.md` lists as trusted.
- They do not show that a refusal is reached, and none shows that a success is. The terminal refusals are shown for every
  session whose agreement reports failed: `encrypt_refuses_failed_agreement`, `decrypt_ratchet_refuses_failed_agreement` and
  `decrypt_empty_message_refuses_failed_agreement` (`decrypt` on an empty message goes to `decrypt_ratchet`), and
  `braid_failed_of_failed_state` shows that `Braid::failed` reports true of the closed value `State::Failed`. These are stated
  of every such session and do not exhibit one: `lifecycle.Session` has fields of the opaque key types, no inhabitant of which is
  derivable in Lean, so that a session value exists is not shown. No premise of the two `_ok_writes` theorems is shown to
  hold of any run. The premise of the `establish_responder` theorem holds of a message shorter than two bytes at every
  identity, store and source (`establish_responder_short_message_refused`), and a store value is exhibited under
  `ResponderSuccessShape` (`responder_prepared_inhabited`; both in "Proved (tier T3, session lifecycle: `establish_responder`
  over every input ...)"). Whether the other arms are reached by honest sessions is shown by the
  Rust tests that refuse a message and compare the exported session (`failed_decrypt_changes_nothing.rs`,
  `a_failed_triple_send_does_not_commit_the_agreement`, `a_failed_initial_message_does_not_burn_prekeys`; `GAP-REGISTER.md`,
  row `E2E-07`), not by a theorem. These four lemmas carry no axiom pin and are not on `REQUIRED_PINS`.

None of the seven depends on a compiler-trust axiom. Each carries an axiom pin under `#guard_msgs`, and the statement of each is
pinned under `#guard_msgs in #check` as well, so a weaker statement that keeps its axiom list fails the module while that pin
stands. `attest.py` lists the seven in `REQUIRED_PINS` and `REQUIRED_STATEMENT_PINS`, so deleting either pin fails it; it does
not read what a statement pin says, so a statement weakened together with its pin's expected message is shown only by the build
and the diff. `check-attest-negatives.sh` deletes each axiom pin in turn. The axiom lists are long because the statements
unfold the generated bodies; they are the unit's opaque constants that those bodies mention, not hypotheses.

`tacenta-proofs/scripts/check-atomicity-negatives.py`, run from `no-sorry.sh`, holds the proofs against a changed body. They
are one walk over each generated body, so a walk that could not tell a write before a refusal from none would prove the same
statements of any body. The script extracts each of the four bodies from the generated file, requires the unmodified copy to be
accepted by the module's proof, plants one change in a copy (the agreement committed before the AEAD check, the ratchet key
committed on a Triple refusal, `pending_initial` cleared on a refusal or on a successful encrypt, the established ephemeral
dropped on a refused repeat, the store changed on a refusal after the inner receive, among twelve) and requires the proof to
fail with an unsolved goal that shows the planted field. Two of the twelve are in the recorded `encrypt` exception arm (a write
to `pending_initial`, and a different error); the proof refuses those as an application type mismatch that shows the planted value. Each plant is at a place where the field can differ: two of the ten sit in the second of two
textual matches, because the first is in the arm of a match on that field where the field is already empty. The controls do not
test a refusal that rewinds the random source, a success of `decrypt_ratchet` or `decrypt` that writes the ratchet private key
(those statements allow it), a success of `encrypt` that writes it (no distinct key is in scope to plant), or the exception arm
taken without the committed state's `Braid::failed` being true. These are proof-dependency controls on copies of the generated Lean, not mutations of the Rust: a
changed Rust source needs the pinned Linux toolchain to regenerate (`REPRODUCING.md`).

## Proved (restated dispatch records: a view for the send direction, and when the scoped chunk fields can be met)

Location: `Translation/UnitLifecycleRepair.lean`, and `Translation/UnitLifecycleT3.lean` for the definition
`CodewordViewSendOf` and the lemma `candidate_public_eq_draw`.

Three records of the lifecycle T3 and dispatch layer ask more than a run can supply, on the readings below, so the theorems that
take them are not claims. None of the readings is a theorem of this tree: each is read from the definition, and the one that
needs a fact about the primitives names it.

- The `receive` clause of `CodewordViewOf` asks a view to name one source for each wire chunk. Two messages that agree on their
  first 32 bytes have the same codeword at index 0, so, given that `Encoder::new` returns on both, no view meets the clause.
- The two chunk fields of `InitialRatchetBraidEvidenceContracts` ask, of every composite, that its chunk be a codeword of the
  source the decoder holds, including the chunk of a composite no peer sends.
- Two fields of `InitialRatchetTripleConcreteEvidence` and `InitialRatchetAeadConcreteEvidence` are quantified over every draw.
  Read with the oracle's `random32` and `dhPublic` clauses they ask `dhPublic` to take one value over all draws, and the real
  X25519 public key is not constant, a property no theorem here states.

Each is restated under a new name (`CodewordViewSendOf`, `InitialRatchetBraidEvidenceContractsScoped`,
`InitialRatchetTripleConcreteEvidenceScoped`, `InitialRatchetAeadConcreteEvidenceScoped`), the dispatch theorems that took the
old records take the new ones, and the old definitions stay, with their statements unchanged. Two results about the restated records are claimed.

- `codewordViewSendOf_satisfiable`: some `Model.Lifecycle.CodewordView` satisfies `CodewordViewSendOf`. For every Braid
  state, source and chunk that is a codeword of that source, the view's send of the model chunk (the source and the index) is
  that chunk's wire codeword. The witness is chosen by classical choice, and the proof uses that the translated encoder is a
  function, so that a codeword of one source at one index is unique. It takes no hypothesis about any opaque operation. It
  holds for any deterministic encoder, so it shows that the clause is consistent and states nothing about a property of the
  shipped one.
- `scoped_chunk_fields_iff_consistent`: for a Braid state, a wire composite and a model composite related by `CompositeRefines`,
  some view meets `IncomingChunkRefines` and `HonestChunk` (the two chunk fields of the scoped record, as statements about the
  state and the two composites) if and only if the run is consistent: the chunk it receives is a codeword of one source, and that
  source fits the decoder the chunk is fed to. It is a normalisation lemma, whose right side is the left side specialised to a
  view that names the source. It does not mention the record, the message or `decodeDetailed`, it says nothing about the code, and
  a well-formed chunk from a dishonest sender is consistent as well. It is not a statement that any real session is.

What these do not show.

- That the theorems taking the restated records are claims. The encrypt-side theorems that took `CodewordViewOf` take
  `CodewordViewSendOf` now, and most also take `OracleOf`. Its KEM and signing clauses are restated, and they follow from two
  laws about the shipped functions at a byte-stream source (`changed_rng_clauses_of_laws`, in the section on the integration's
  hypotheses below); its other clauses are not shown to hold. `public_session_encrypt_of_send_contracts` also takes
  `BraidSendTraceAgreementCounted`, whose draw clause holds together with `OracleOf.sigSign` under two laws at a Braid send from
  `KeysUnsampled` (`braidSendTraceCounted_with_sigSign_byte`); the one-draw form the session contract branch introduced
  contradicted it (`braidSendTrace_conflicts_with_sigSign`). The dispatch theorems no longer take the same-ephemeral evidence records; they take
  the per-branch `InitialDispatchBranchEvidence`, whose model-side premises state the model's repeat verdict on the branch;
  the code's verdict gives each (`repeated_initial_agreement_true_iff`, `repeated_initial_agreement_false_iff`), and no
  dispatch theorem uses that yet.
- That the consumer structure is satisfiable in general. The old `InitialRatchetConcreteBranchEvidence` is empty at any model
  state at which one inner message passes the first agreement, given `OracleOf` (`concreteBranchEvidence_empty`), and it asked the
  scoped Braid record of every inner message that reaches a refusal, an inconsistent one included. The seven dispatch theorems
  that reached it (five through the end-to-end records, `public_session_decrypt_end_to_end` and its `_with_atomicity` form through
  two constructors of `SessionDecryptEvidence`) take `InitialRatchetConcreteBranchEvidenceRun` now, whose fields are asked of the
  run's own inner message and RNG state. The two chunk fields of its scoped Braid record are met exactly when the run is
  consistent (`scoped_chunk_fields_iff_consistent`); the record's other fields (`BraidReceiveContracts`, the Braid agreement laws
  and the epoch bound) are not decided here, so that the record can be supplied for any run is not shown. Its Braid field, and
  the success provider of its result field, can be met for a consistent run and not for a run whose chunk is inconsistent,
  whether the run is refused or accepted (`scoped_record_gives_consistent`), which those theorems therefore do not cover;
  `decrypt_ratchet` checks nothing about the agreement chunk before the AEAD tag, so such a run can reach a refusal. That the
  record's Triple and AEAD branch contracts can be supplied for a run is not shown.
- The agreement hypotheses of the Braid in the session unit, which are not decided here.

A view that meets the send clause and the scoped chunk fields of one consistent run together exists
(`send_and_scoped_chunk_fields_joint`, unpinned), because the two constrain different fields of a `CodewordView`. Whether one
view meets the scoped fields for every inner message is the consumer-structure item above.

The seven results of the previous section and the T1 results do not depend on any of this. `candidate_public_eq_draw` is the
lemma that replaces the two dropped draw-quantified fields: the public bytes of the run's candidate ratchet key are
`oracle.dhPublic` of the run's draw, from the oracle's `random32` and `dhPublic` clauses and the key codec. It is not pinned or
claimed; it takes `OracleOf` and `DhCodecOf`, which are hypotheses and not shown to hold of the shipped primitives.

Each of the two claimed results carries an axiom pin and its statement pinned under `#guard_msgs in #check`, so a weaker
statement that keeps its axiom list fails the module while that pin stands. `attest.py` lists them in `REQUIRED_PINS` and
`REQUIRED_STATEMENT_PINS`, so deleting either pin fails it; it does not read what a statement pin says, so a statement weakened
together with its pin's expected message is shown only by the build and the diff. `check-attest-negatives.sh` deletes each axiom
pin in turn. `send_and_scoped_chunk_fields_joint` and `scoped_record_gives_consistent` carry no axiom pin and are not on
`REQUIRED_PINS`.
`tacenta-proofs/scripts/check-repair-negatives.py`, run from `no-sorry.sh`, holds them against a changed statement: it requires
the unmodified module and the unmodified lemma to be accepted, then makes one change to a copy (a witness that does not send the
codeword, a claim of the old two-sided statement, a consistent-run definition without the codeword or without the fit, a weakened
link between the draw and the candidate key) and requires Lean to refuse it.

## Proved (tier T3, session lifecycle retry prerequisites, on the eight-leaf unit)

Location: `Translation/UnitLifecycleInitialDispatch.lean` and
`Translation/AxiomAuditSessionUnit.lean`.

- `Tacenta.UnitLifecycleT3.concrete_receive_attempt_store_full_from_contracts`:
  if the generated `receive_attempt` returns one of the two errors the
  lifecycle classifies as a full-store refusal, then, under the explicit leaf
  contracts, state relation and receive bounds, there is one corresponding
  model refusal: `Model.Triple.receiveDetailed` returns it, the public refusal
  mapping names it, and `Model.Lifecycle.fullStore` selects the same classical
  or post-quantum half as the concrete classifier.
- `Tacenta.UnitLifecycleT3.concrete_receive_attempt_store_full_from_retry_bounds`:
  the same exact failure-side result when the eleven leaf premises are supplied
  by the preserved `RetryReceiveBounds` package. It does not derive the
  separate switch-half shortfall reachability or machine-width premise.
- `Tacenta.UnitLifecycleT3.fullStoreOfReal_ne_of_generated_ne`: an actual
  successful translated `PartialEq::ne` comparison between concrete
  full-store halves implies inequality of their model images. The map is
  injective; this adapter reuses the generated enum comparison theorem, which
  on this tree is kernel-checked, so the Session unit axiom pin names the three
  standard axioms only.

These are prerequisites for the bounded eviction retry. They do not prove that
the retry loop terminates or refines its model, do not compose the success
path, and do not prove public `Session::decrypt` end to end. The section
"Proved (tier T3, session lifecycle `decrypt_ratchet` with the eviction retry loop,
on the eight-leaf unit)" below proves the first two from them.

`concrete_receive_attempt_store_full_from_contracts` and
`concrete_receive_attempt_store_full_from_retry_bounds` are compiler-trusted:
their axiom lists include eight per-declaration `native_decide` axioms, seven
from the Session unit's sparse ratchet refinement (its labels, its `MAX_SKIP`
constants and one step of `receive_refines_continuation`) and one from the
Triple's `combine_info_agrees`. `fullStoreOfReal_ne_of_generated_ne` is
kernel-only.

## Proved (tier T3, session lifecycle `decrypt_ratchet` with the eviction retry loop, on the eight-leaf unit)

Location: `Translation/UnitLifecycleRetryLoopT3.lean`, `Translation/UnitLifecycleDecryptRatchetT3.lean`,
`Translation/UnitLifecycleDecryptRatchetScreen.lean`.

`Session::decrypt_ratchet` is the private transaction the shipped `Session::decrypt` runs on a ratchet message;
`establish_responder` calls it too. These results relate its translation on the eight-leaf unit to
`Model.Lifecycle.decryptRatchet`, including the eviction retry loop of `receive_with_eviction`. Each is conditional on
the hypotheses in its statement. The screen below shows the hypotheses this section introduces consistent with each other
and with the session contract records, and meets the per-run ones at three runs. It does not show them true of the
shipped code. It does not decide a run that carries an agreement chunk; it does not show the real `zeroize` functions
return at the instances three fields of the contract records are stated at, or that the real `Vec::pop` and
`Option::as_mut` meet the two laws `DecryptRatchetAgreements` states (`LIMITATIONS.md`, the sections on the four contract
records and on this refinement). No gate reads these hypotheses: `check-hypothesis-witnesses.sh` leaves out the sections
whose heading names a session lifecycle, so what shows them satisfiable is `Translation/UnitLifecycleDecryptRatchetScreen.lean`
alone, in the senses stated below. They are not results about `Session::decrypt` or `Session::encrypt`.

- `receive_with_eviction_loop_refines`: for every fuel larger than the number of skipped keys the model Triple state holds
  (classical plus sparse), from a generated loop state related to a model one by `LoopRel` (the Triple state relation, the
  batch relation `BatchCovers`, the pending refusal's public mapping, `ReceiveHeadroom`, `RetryReceiveBounds`, and each
  skipped-key store at most `2^32 - 1 - 2000` long), and under the contract record `TripleReceiveContracts`, the HMAC,
  HKDF and three `zeroize` round-trip agreements and the two sparse agreements `VecRetainAgrees` and
  `RemoveSkippedAtAgrees`, the generated retry loop returns, and the model loop's result at that fuel
  (`Model.Lifecycle.ReceiveWithEvictionLoopResult`) is related to the generated outcome: a success with related state and
  key, a refusal whose public mapping is the model's refusal (an empty eviction returns the pending full-store refusal on
  both sides), or `OpenRefusal`. `OpenRefusal` is a refusal that `full_store` does not classify, returned by one Triple
  receive at a working state related to a model state; the theorem says that if that one refusal is the model's detailed
  refusal, the two loop results agree, and it does not say that it is. So the loop is related to the model loop, not
  shown equal to it. `receive_with_eviction_refines_complete` (the next section) closes that case for
  `receive_with_eviction` as a whole, from the first attempt through every retry. `BatchCovers` relates the saturating `usize` batch to the model's natural number by equality or by
  both covering the store, so the theorem takes no bound on a header's counters.
- `receive_with_eviction_refines`: the first attempt and the loop composed: at related Triple states with the receive and
  store bounds, the generated `receive_with_eviction` returns, and its result is related to
  `Model.Lifecycle.receiveWithEviction` in the same three ways (the model's own fuel is one more than the keys it holds).
- `receiveWithEvictionLoopResult_stop`: in the model, a retry refused for a reason `fullStore` does not classify ends the
  loop with that refusal. `Model/Lifecycle.lean` keeps the loop private and exposes no such lemma, so this proof names the
  private loop through Batteries' `open private`; no model definition changes.
- `shortfall_covers`, `evict_for_retry_covers`: the generated first batch of each half covers the model's, and one
  generated eviction at a covering batch refines the model's eviction, keeps the headroom and shrinks the store when it
  removes a key.
- `decrypt_ratchet_refines`, `decrypt_ratchet_refines_statement`: for every input meeting the hypotheses of
  `DecryptRatchetRefinesStatement` (the four `OracleOf` clauses the transaction uses, `DecryptOracleOf`; `DhCodecOf`;
  `DecryptRatchetContracts`; the instance `SessionUnitT1.DerivedKeysModel`; the agreements `DecryptRatchetAgreements` at
  the oracle's KEM model, which hold the KDF and wrapper agreements, two laws about `Vec::pop` and `Option::as_mut`, and
  the Braid's KEM and erasure agreements; `SessionRefines`; `DecryptRatchetHeadroom`; the trace equation; and the per-run record
  `DecryptRatchetRun`), the generated `decrypt_ratchet` returns, and either `StepRefines` holds between its result, the
  session it leaves and the remaining trace and the model's step, or the output satisfies `TripleRefusalOpen`.
  `StepRefines` is proved on the terminal guard, a decode refusal, both DH refusals, a Triple refusal whose reason is a
  full store (after an empty eviction), an AEAD refusal and a success, with or without eviction rounds. On a refusal the
  session it returns refines the model's unchanged session, and `UnitLifecycleAtomicity.decrypt_ratchet_err_leaves_state`
  shows it is the given session; a success commits the Triple and Braid candidates and, when the sending key changed, the
  drawn private key.
- `DecryptRatchetAgreements.vecRetainAgrees`, `DecryptRatchetAgreements.removeSkippedAtAgrees`:
  `SessionUnitSpqrT3.VecRetainAgrees` and `SessionUnitSpqrT3.RemoveSkippedAtAgrees` follow from the record's two laws, `pop`
  (`LawPop`) and `asMut` (`LawAsMut`), and three axiom-level fields of `TripleReceiveContracts`: `spqrZeroize` and the
  first two conjuncts of `vecRetain` (`Vec::capacity` returns; `Vec::zeroize` returns at the unit's three instances). The
  proof of `decrypt_ratchet_refines` passes them to the loop theorem, so neither agreement, each a statement about
  translated functions, is a hypothesis of the decrypt theorems; the two laws are, and they are assumed
  (`UnitSatisfiabilitySpqrSessionLaws.lean`; the section on the Session unit's sparse agreements). Each rests on 31 of the
  unit's axioms, the opaque constants the types of the record and of `TripleReceiveContracts` mention. Every theorem
  that takes `DecryptRatchetAgreements` (`decrypt_ratchet_refines` and its `_statement`, `_or_open`, `_unless_open`,
  `_at_sample` and `_at_eviction`, `decrypt_ratchet_refines_complete` and its `_complete_statement` and
  `_complete_at_refusal`, and `generated_reaches_open_path`) therefore states a formally different proposition under
  unchanged text, carried by the record's `#print` pin: `LawPop` and `LawAsMut` in place of the two agreements; with
  `contracts.triple` the new hypotheses imply the old, and the converse is not shown (the laws quantify over every type).
- `decrypt_ratchet_refines_unless_open`: under the same hypotheses, for every output that does not satisfy
  `TripleRefusalOpen`, `StepRefines` holds. A conclusion widened at the theorem level, with `TripleRefusalOpen` as it is,
  breaks this proof and not only a pin.
- `tripleRefusalOpen_exactly`, `tripleRefusalOpen_false_unless_triple`: `TripleRefusalOpen` holds of an output exactly
  when it is a Triple refusal whose reason is neither `Classical SkippedStoreFull` nor `PostQuantum SkippedStoreFull`;
  it is false of every generated success and of every other generated refusal. It constrains only the generated output:
  it can hold on an input on which the model's step succeeds, and it says nothing about the session returned.
- `DecryptPrefix.triple_refusal`, `DecryptPrefix.aead_refusal`, `DecryptPrefix.success`: the generated result once every
  call before the Triple receive is fixed, for a Triple refusal, an AEAD refusal and a success.
- `RetryRunBounds.toRetryReceiveBounds`, `DecryptOracleOf.of_oracleOf`, `cMax_usize`: the run's model-side receive bounds
  give the generated-side ones, `OracleOf` gives `DecryptOracleOf`, and Aeneas' bound on a `usize` is `2^32 - 1`.
- `sample_run_satisfiable`, `succ_run_satisfiable`: two runs meet every per-run hypothesis together, each with a message
  that decodes on both sides, for every Braid KEM model, codeword view and oracle with that KEM model and the source's
  draws: a session over fresh states, and one over a Triple state that already receives on both halves. Neither holds a
  skipped key or carries an agreement chunk. The values of the two opaque key types are arguments.
- `sample_model_refuses`, `succ_model_accepts`, `hypotheses_meet_refusal_and_success`: with the oracle of the model below,
  the model step refuses at the first agreement at the first run and succeeds at the second, so the per-run hypotheses are
  met at a run whose model step is a refusal and at one whose model step is a success. The oracle clauses hold of that
  oracle in the interpretation below and not at the real constants, so this shows the model side of each run and not
  which branch the shipped code takes. No proof here chooses a width of `usize`, so each holds at both widths.
- `evict_decode_model`, `evict_headroom`, `evict_run_satisfiable`, `evict_first_attempt_full`,
  `hypotheses_meet_eviction_round`: a third run, over a Triple state whose classical store holds 1001 keys and whose sparse
  store holds one, with message number 1000 on the classical chain, meets every per-run hypothesis with both stores
  non-empty. There the model's first Triple receive refuses with the classical full store (1001 kept keys and 1000 new
  ones pass the cap of 2000), the first batch is one key and the first eviction removes one key. This is the model side
  of the run, as above. It shows one eviction round reached under these hypotheses, the first, with its retry taken:
  that the model step passes the agreements and the draw before the loop (`evict_reaches_receive`) and that the loop then
  evicts one key and retries (`evict_loop_first_round`). It does not show the outcome of the retry, and no run here
  reaches an empty eviction, a second round or a switch between the two stores. A run record which asked both stores to
  be empty would be refused here. The witness states are built for these hypotheses and not for `Ratchet::invariant`:
  the third run's classical store repeats one key, and the second and third runs hold a receiving chain without a
  sending chain, both of which the invariant refuses. They show the hypotheses satisfiable, not that a session the
  shipped code accepts reaches these branches.
- `evict_reaches_receive`, `receiveWithEviction_first_round`, `evict_loop_first_round`: with the oracle below, the model
  step at the third run passes the terminal guard, the decode, both agreements and the draw; at any state whose first
  receive refuses with the classical full store, whose first batch is one key and whose first eviction removes a key,
  `receiveWithEviction` is that one round followed by the receive on the evicted state; and the third run's state is
  such a state, with fuel 1003. These name the private model loop through `open private`, as
  `receiveWithEvictionLoopResult_stop` does.
- `decrypt_boundary_has_a_model`, `decrypt_shapes_are_predicates`: one interpretation of the unit's opaque constants
  (`Interp.modelDecrypt`, `Interp.modelT3` with the two key types read as 32-byte arrays), one DH view and one oracle meet
  together every axiom-level shape of the session contract records, `StdLaws`, `FaithfulShape`, `TruncatePrefix`, the two
  model classes, the six Braid agreements at `toyKem`, the five `zeroize` round trips, `DhCodecOf` and the four clauses of
  `DecryptOracleOf`, with an agreement and an AEAD that each refuse one input and accept another; each shape is the
  theorem's predicate at the real constants. This is the substitution argument of `UnitSatisfiabilityJoint.lean`, an
  argument about derivations and not a theorem inside Lean.
- `decrypt_ratchet_refines_from_shapes`, `decrypt_ratchet_refines_from_shapes_at_eviction`: the composition inside Lean:
  from those shapes read at the real constants (the record's two laws about `Vec::pop` and `Option::as_mut` among them,
  read from `StdLaws`), every hypothesis of `decrypt_ratchet_refines` holds at the first run and at the third, and so does
  its conclusion. So the substitution step is the only part of the joint claim outside Lean. Neither theorem takes
  `VecRetainAgrees` or `RemoveSkippedAtAgrees`.
- `run_draw_not_trivial`, `retryRunBounds_not_trivial`, `tripleRefusalOpen_false_of_ok`,
  `tripleRefusalOpen_false_of_store_full`: the run record fails at an exhausted source, the receive bounds fail at a sparse
  epoch of `u64::MAX` and at a classical store with less than 2000 below the bound, and the open disjunct is false of a
  success and of the two full-store refusals. The chunk fields have no such control: every witness carries no chunk and
  meets them by their vacuous arm.
- `decrypt_ratchet_refines_at_sample`, `decrypt_ratchet_refines_at_eviction`: the theorem at the first run and at the third,
  with every per-run hypothesis discharged by the witnesses and only the boundary records left as arguments.

**What the disjunct leaves open.** On a run whose generated output is a Triple refusal with a reason other than a full
store (a classical `TooManySkipped`, `NoReceivingChain`, `OutOfOrder` or `ChainExhausted`, or any sparse refusal but
`SkippedStoreFull`; the predicate also admits a classical `NoSendingChain`, which, read from the source, only
`ratchet::send` returns, and which `tripleReceiveRefusalOfReal` maps to no model refusal), from the first attempt or from a
retry inside the loop, the theorem says nothing about the model's step: not its refusal reason, not that it refuses, and
not the session or trace it returns. Among these are the refusal of a message whose key was already used (`OutOfOrder`)
and the skip-limit refusal (`TooManySkipped`). The missing piece is a refusal refinement of one Triple receive at related
states, which the theorems this section composes do not give: the leaf refinements relate a success and the full-store
refusal only. `UnitLifecycleAtomicity.decrypt_ratchet_err_leaves_state` says separately that such a refusal returns the
session it was given. The next section supplies that
refinement and closes the path (`decrypt_ratchet_refines_complete`); `decrypt_ratchet_refines` keeps its statement.

**What the hypotheses cover.** The per-run record asks the run's agreement chunk to be a codeword of one source that fits
the decoder it is fed to (`IncomingChunkRefines`, `HonestChunk`), so a run that carries a spliced or inconsistent chunk is
not covered, refused or accepted; it asks the random source to hold at least one draw, read through a function of the
source's state (so a source with no state of its own, such as `OsRng`, is outside the statement); and it bounds each
skipped-key store by `2^32 - 1 - 2000` and the model state as `RetryReceiveBounds` does. The screen does not reach a run
carrying a chunk. The theorem takes `DecryptRatchetContracts`, three of whose fields (`SessionUnitSpqrT1.ZeroizeTotal`,
`SessionUnitBraidT1.ArrayZeroizeTotal` and the `Vec::zeroize` conjunct of `SessionUnitSpqrT1.VecRetainTotal`) say that
`Array::zeroize` and `Vec::zeroize` return at the instances the unit passes to them (the blanket `u8` instance on 32-byte
arrays; the chain table and the two skipped-key stores); that the real functions do is assumed. The
agreements hold two laws about opaque standard-library operations, `LawPop` (`Vec::pop` of a non-empty vector returns the
vector without its last element) and `LawAsMut` (`Option::as_mut` returns), from which with three contract fields the
proof derives `SessionUnitSpqrT3.VecRetainAgrees` and `SessionUnitSpqrT3.RemoveSkippedAtAgrees`; the laws hold in the
joint model and in an interpretation whose wipes propagate a failing element's failure, and are not proved of the real
functions. The loop theorems `receive_with_eviction_loop_refines` and `receive_with_eviction_refines` still take the two
agreements as hypotheses (`GAP-REGISTER.md`, row `SESSION-SPARSE-AGREEMENTS`). `LIMITATIONS.md`, section "The
`decrypt_ratchet` refinement", lists what is assumed.

**Compiler trust and pins.** `receive_with_eviction_loop_refines`, `receive_with_eviction_refines`, `decrypt_ratchet_refines`,
`decrypt_ratchet_refines_statement`, `decrypt_ratchet_refines_unless_open`, `decrypt_ratchet_refines_at_sample`,
`decrypt_ratchet_refines_at_eviction`, `decrypt_ratchet_refines_from_shapes` and
`decrypt_ratchet_refines_from_shapes_at_eviction` are compiler-trusted. Their axiom lists include nine per-declaration
`native_decide` axioms, the nine that `UnitTripleT3.receive_refines_discharged` lists for the three-leaf unit, under the
Session unit's names (`SessionUnitTripleT3.receive_refines_discharged` has no axiom pin of its own): eight from the Session
unit's sparse ratchet refinement (its four labels, its `MAX_SKIP` constants, its store cap and one step of
`receive_refines_continuation`) and the Triple's `combine_info_agrees`. The two full-store correspondences of #203 list
eight of the nine (all but `chain_start_agrees`, which the success path adds); that ninth fact, a closed fact about the
sparse ratchet's chain-start label, is new to the pinned results of the Session unit. These nine results are on
`COMPILER_TRUSTED_PINS`, which grows from 13 to 22 names: each composes the Session unit's discharged Triple receive
refinement, directly or through the loop theorems, and so inherits its nine constants; no other constant is added. The
other 32 results here rest on no compiler-evaluated constant: seven (`receiveWithEvictionLoopResult_stop`,
`shortfall_covers`, `cMax_usize`, `RetryRunBounds.toRetryReceiveBounds`, `retryRunBounds_not_trivial`,
`evict_decode_model` and `receiveWithEviction_first_round`) are kernel-only, and the other 25 each rest on between 1 and
49 of the Session unit's opaque-operation axioms, as the T1 theorems do. Each result carries an axiom pin and a statement
pin. The definitions this package adds carry `#print` pins, except six that pinned texts name (`wrap32`, `zeros32`,
`ones32`, `DhViewShape`, `sampleMessage` and `succMessage`), and five earlier ones its statements are written in carry them
too (`StepRefines`, `ResultRefines`, `SessionRefines`, `VecRetainAgrees` and `RemoveSkippedAtAgrees`). The other earlier
definitions they use carry none, among them `refusalOf`, `tripleReceiveRefusalOfReal`, `IncomingChunkRefines`,
`HonestChunk`, `DecryptRatchetHeadroom`, `ReceiveHeadroom`, `RetryReceiveBounds`, `DhCodecOf`, `DecryptRatchetContracts` and
the model's `decryptRatchet`, `receiveWithEviction` and `receiveDetailed`; a pin shows their names and not their meaning.
`attest.py` requires the axiom pins and statement pins of these results; a name leaves the axiom-pin list or the `#print`
list by an edit of `attest.py` alone, and only the statement-pin list is also recorded in the manifest.
`check-decrypt-ratchet-negatives.py` plants a fault in a copy of the loop, of the composition, or of the composition and
the screen together, and requires Lean to refuse each at a named declaration: four in the loop correspondence, two that
make the open disjunct broader (each refused in `tripleRefusalOpen_exactly`), two in the run record, one that widens the
conclusion (refused in `decrypt_ratchet_refines_unless_open`) and one that asks the run record for empty stores (refused
in `evict_run_satisfiable`); an eleventh makes the disjunct broader with the pins kept and requires the pin of
`TripleRefusalOpen` itself to refuse it.

## Proved (tier T3, session lifecycle: every Triple receive refusal, and `decrypt_ratchet` on every path, on the eight-leaf unit)

Location: `Translation/UnitLifecycleTripleRefusalT3.lean`, `Translation/UnitLifecycleDecryptRatchetCompleteT3.lean`,
`Translation/UnitLifecycleDecryptRatchetCompleteScreen.lean`, and the split form in
`Translation/UnitLifecycleDecryptRatchetT3.lean`.

These close the path the previous section leaves open. Each is conditional on the hypotheses in its statement, and none
adds a hypothesis to the result it extends. They are not results about `Session::decrypt` or `Session::encrypt`.

- `triple_receive_refusal_refines`: the statement `TripleReceiveRefusalRefines`. Under the hypotheses of
  `SessionUnitTripleT3.receive_store_full_refines_discharged` (the leaf agreements, the Triple state relation, the classical
  header relation and the eleven numeric and store premises), if the generated Triple receive refuses with a reason, the
  reason's public mapping `tripleReceiveRefusalOfReal` is defined and `Model.Triple.receiveDetailed` returns that refusal.
  So at those states the generated receive never refuses with the classical `NoSendingChain`, which has no receive
  counterpart, and every refusal it returns is the model's, the two full-store refusals included. Two of its
  hypotheses, `SessionUnitSpqrT1.ZeroizeTotal` and `VecRetainTotal`, are among the three contract fields stated at the
  instances the unit passes to `Array::zeroize` and `Vec::zeroize`; that the real functions return there is assumed
  ("What is not shown" below).
- `ratchet_receive_refusal_refines`, `ratchet_receive_tail_refusal_refines`, `ratchet_skip_refusal_refines`: the same for the
  classical ratchet's receive, its shared suffix and its skip: `TooManySkipped` and `SkippedStoreFull` from either skip,
  then `OutOfOrder`, `NoReceivingChain` and `ChainExhausted`, each the model's detailed refusal, in the model's order.
- `derive_chain_refines_far`, `derive_chain_loop_ok`: the chain derivation refuses with `ChainExhausted` only if
  `start_n + count` exceeds `u32::MAX`, and the derivation loop returns its keys whenever `start_n + count` is at most
  `u32::MAX + 1`. The skip derives no number past its target, so that refusal does not reach the skip; the success
  theorems did not need this, because their conclusion is about a success only.
- `spqr_receive_refusal_refines`, `spqr_receive_continuation_refusal_refines`, `spqr_skip_refusal_refines`: the same for the
  sparse ratchet: a refused advance is `EpochOutOfOrder` on both sides; then every skip refusal (`NoChain`, `ChainRetired`,
  `TooManySkipped`, `SkippedStoreFull`), and `NoChain`, `ChainRetired` and `OutOfOrder` after the skip. The sparse
  `ChainExhausted` of the advance and of the chain step is excluded by the epoch and counter premises, as in the success
  theorem.
- `concrete_receive_attempt_refusal_from_retry_bounds`: the Triple result at the bounds record the retry loop keeps.
- `openRefusal_closes`: under the Triple receive's agreements, `OpenRefusalCloses` holds: a refusal the loop theorem
  reduces to one Triple receive (`OpenRefusal`), at a header related to the model's, is a refined outcome.
- `receive_with_eviction_refines_complete`: under the hypotheses of `receive_with_eviction_refines`, the generated
  `receive_with_eviction` returns and its result is related to `Model.Lifecycle.receiveWithEviction` with no case left
  open: a success with related state and key, or a refusal whose public mapping is the model's refusal.
- `decrypt_ratchet_refines_or_open`, `or_unless_closed`: the proof of `decrypt_ratchet_refines`, with its open case
  conditioned on the failure of `OpenRefusalCloses`. `decrypt_ratchet_refines` is that theorem with the condition
  dropped; its statement is unchanged.
- `decrypt_ratchet_refines_complete`, `decrypt_ratchet_refines_complete_statement`: under exactly the hypotheses of
  `decrypt_ratchet_refines` (`DecryptRatchetRefinesCompleteStatement`), the generated `decrypt_ratchet` returns and
  `StepRefines` holds between its result, the session it leaves and the remaining trace and the model's step, on every
  path: the terminal guard, a decode refusal, both DH refusals, every Triple receive refusal the run's bounds admit (from
  the first attempt or a retry; the bounds exclude the sparse `ChainExhausted`), an AEAD refusal and a success, with or
  without eviction rounds. Three fields of the contract record it takes are stated at the instances the unit passes to
  `Array::zeroize` and `Vec::zeroize`, and that the real functions return there is assumed.
- `decrypt_ratchet_refines_complete_implies_refines`: the complete statement implies the first form's statement, so the
  complete form assumes no hypothesis beyond the first form's (by proof); that the hypotheses are identical, not only
  included, is shown by the two forms' statement pins, which differ in the conclusion alone.
- `ref_premises`, `ref_model_triple_refuses`, `ref_triple_refuses`: at a Triple state whose classical receiving chain is at
  message number 1, and a header for message number 0 on that chain, every premise of the refusal theorem holds, the model
  refuses with the classical `outOfOrder`, which is not a full store, and, under the boundary the theorem takes, the
  generated receive refuses with a reason whose public mapping is that refusal. The success theorem rules out a generated
  success there.
- `ref_headroom`, `ref_run_satisfiable`, `ref_model_refuses`, `hypotheses_meet_open_path`,
  `decrypt_ratchet_refines_complete_at_refusal`: a `decrypt_ratchet` run over that Triple state meets every per-run
  hypothesis, and with the oracle of the previous section's model its model step is the Triple refusal `outOfOrder`,
  returned by the first attempt; the last is the complete theorem at that run. No proof here chooses a width of `usize`,
  so each holds at both widths. Its state, like those of the previous section, meets these hypotheses and not
  `Ratchet::invariant`, which refuses a receiving chain without a sending chain.
- `generated_reaches_open_path`: with that oracle and under the boundary records, the generated `decrypt_ratchet` at that
  run returns the Triple refusal `Classical OutOfOrder`, so its output satisfies `TripleRefusalOpen`: the run is on the
  path `decrypt_ratchet_refines` left open. This is the generated side of the run, conditional on those records, not a
  statement about the real primitives.

**What is not shown.** Which branch the shipped code takes at the screen's run with the real primitives: the oracle
clauses hold of the model interpretation, not at the real constants. The hypotheses are those of the previous section,
with the same limits: a spliced or inconsistent agreement chunk is not covered; the random source is read as a function of
its state, so a source with no state of its own, such as `OsRng`, is outside the statement; that the real `zeroize`
functions return at the instances three fields of the contract records are stated at is assumed; and the two laws of
`DecryptRatchetAgreements` about `Vec::pop` and `Option::as_mut`, from which the proof derives the sparse store's two
agreements, are assumed (`LIMITATIONS.md`, the section on the `decrypt_ratchet` refinement). `triple_receive_refusal_refines`,
`receive_with_eviction_refines_complete`, `openRefusal_closes`, `ref_triple_refuses` and the `spqr_*_refusal_refines`
family still take the two agreements as hypotheses (row `SESSION-SPARSE-AGREEMENTS`). The screen's run refuses on the classical side at the
first attempt; no run here reaches a sparse refusal or a refusal returned by a retry inside the eviction loop, and unlike
the first and third runs of the previous section this run is not composed with the boundary model inside Lean.

No gate reads these hypotheses. `check-hypothesis-witnesses.sh` reads, by its existing convention, only the leaf and
three-leaf-unit sections, and leaves out every section whose heading names a session lifecycle. This section's heading
carries those words so that the gate routes its theorems out: the gate files every `Unit` namespace, `UnitLifecycle`
included, under the three-leaf unit, where these theorems are not declared, so with any other heading it would refuse to
run. The theorems of this section are therefore not covered by that gate. A hypothesis-witness gate for the Session unit is
planned to cover them; until it exists, what shows their hypotheses satisfiable is the two screen modules alone, in the
senses stated here and in the previous section.

**Compiler trust and pins.** `decrypt_ratchet_refines_complete`, `decrypt_ratchet_refines_complete_statement`,
`decrypt_ratchet_refines_or_open`, `decrypt_ratchet_refines_complete_at_refusal` and `generated_reaches_open_path` have
exactly the axioms of `decrypt_ratchet_refines`, including its nine `native_decide` constants.
`receive_with_eviction_refines_complete` and `ref_triple_refuses` list the same nine. `triple_receive_refusal_refines`,
`concrete_receive_attempt_refusal_from_retry_bounds` and `openRefusal_closes` list seven of them (three of the sparse
ratchet's four labels, its two `MAX_SKIP` constants, its store cap and one step of `receive_refines_continuation`), and the
three sparse refusal theorems five or six. These thirteen are compiler-trusted, each because it composes the Session
unit's Triple receive refinement or the sparse ratchet's own refinement and inherits their constants; no other constant is
added. The other thirteen results here rest on no compiler-evaluated constant: three (`ref_premises`,
`ref_model_triple_refuses` and `or_unless_closed`) are kernel-only, and ten each rest on between 4 and 49 of the Session
unit's opaque-operation axioms. The count of compiler-trusted pinned results is `attest.py`'s
(`counts.compiler_trusted` in the verification manifest); with this section and the previous one it is 35, against 13
before package F. The compiler-trust class of these results is expected to change: if the nine constants are settled by
the kernel rather than by the compiler, as is planned separately, these results become kernel-checked against the
opaque operations and the count falls accordingly.

Each result carries an axiom pin and a statement pin. The definitions this section adds carry `#print` pins
(`TripleReceiveRefusalRefines`, `DecryptRatchetRefinesCompleteStatement`, `OpenRefusalCloses` and the screen's states
and headers). The definitions their statements use carry none beyond the previous section's pins; among those without one
are the previous section's list and, new to the leaf refusal statements, `ratchetReceiveRefusalOfReal`,
`sparseReceiveRefusalOfReal`, `StateR`, `HeaderR`, the sparse `StateRefines`, and the model's classical and sparse
`receiveDetailed` and `skipMessageKeysDetailed`. A pin shows their names and not their meaning. `attest.py` requires the
axiom pins and statement pins of these results; a name leaves the axiom-pin list or the `#print` list by an edit of
`attest.py` alone. `check-decrypt-ratchet-negatives.py` plants a fault in a copy of the refusal refinement (a refusal
named as another, the derivation refusal no longer located, the sparse epoch bound weakened, the Triple model reason
fixed), of the closure (the bridge without the public mapping, and the complete statement with the open disjunct put back,
with its pins kept) and of the screen (the model's refusal there named as another), and requires Lean to refuse each at a
named declaration, or the pin of `DecryptRatchetRefinesCompleteStatement` for the one kept with its pins.

## Proved (tier T3, session lifecycle: the per-run receive bounds of `decrypt_ratchet` from `Session::invariant`, on the eight-leaf unit)

Location: `Translation/UnitLifecycleDecryptRunBounds.lean`.

`decrypt_ratchet_refines_complete` (previous section) takes `DecryptRatchetHeadroom` and the run record
`DecryptRatchetRun`, whose `retry` field asks the eleven fields of `RetryRunBounds` of the model Triple state and whose
`braidEpoch` field asks a Braid epoch ceiling. These results derive `RetryRunBounds` from `Session::invariant`, the session
relation and four counter ceilings, `CounterHeadroom`, which stay assumed, and restate the complete theorem with them. The
complete theorem and `RetryRunBounds` are unchanged. They are not results about `Session::decrypt` or `Session::encrypt`.

Which field comes from where. Of the eleven fields of `RetryRunBounds`, five follow from the invariant alone: `classicalMatch`
and `sparseMatch` (each store's clause that no two keys share a header), `sparseChainsRoom` (at most two chain-table entries),
and `classicalStore` and `sparseStore` (each store holds at most 2000 keys, and `2000 + 2000 <= 2^32 - 1`, at both widths).
Two more, `sparseChainEpochs` and `sparseSkippedEpochs`, follow from the invariant (the epoch window and the chained-key clause)
together with the assumed sparse epoch ceiling; the invariant alone gives `epoch < u64::MAX`, which does not give them. One,
`sparseOutputEpoch`, follows from the model alone: a key `Model.Braid.receive` outputs is labelled with an epoch
of at most `u64::MAX - 2` for every state and message (`Model.Braid.receive_output_epoch_lt`). Three are fields of
`CounterHeadroom`: `classicalEvents` (`events + 1 < u32::MAX`; the invariant gives `events < u32::MAX`), `sparseEpoch`
(`epoch + 1 < u64::MAX`; the invariant gives `epoch < u64::MAX`) and `sparseCounters` (each chain counter below `u64::MAX`; no
invariant clause bounds it). The fourth field of `CounterHeadroom`, `braidEpoch`, is the run record's own Braid epoch ceiling
(`epoch + 1 < u64::MAX`), which the Braid invariant (`epoch >= 1`, no upper bound) does not give.

The record `CounterHeadroom` holds the four ceilings, stated of the translated session, and is assumed. Each ceiling excludes a
state `Session::invariant` accepts: a classical clock at `u32::MAX - 1`, where the crate's clamp holds it (`MAX_EVENTS`); a
sparse epoch at `u64::MAX - 1`; a sparse chain counter at `u64::MAX`; a Braid epoch at `u64::MAX - 1`. The clock case is shown
in Lean (`invariant_does_not_give_counterHeadroom`, below); the other three are by reading of the Rust, not checked in Lean.
They are counter ceilings, not capacity bounds, and an exclusion is permanent for a session: once the clock parks it stays, so
every later `decrypt_ratchet` of that session is outside the theorem, and one exhausted chain counter, a send chain's included,
excludes every receive until its epoch retires. By reading only, not proved: under clause (b) of `Session::invariant`
(`tacenta-core/lifecycle/src/lifecycle.rs`, the Braid-epoch relation) the sparse epoch equals the Braid epoch or is one below
it while the Braid has not failed, and `decrypt_ratchet` refuses a failed Braid before the Triple step, so wherever the run
bounds are used the Braid epoch ceiling covers the sparse one; the field is kept because `DecryptRatchetRun.retry` asks
`RetryRunBounds` of every run.

- `retryRunBounds_of_triple_invariant`: if `Triple::invariant` returns `true` of a translated Triple state related to a model
  state, and the clock, sparse epoch and chain-counter ceilings hold of it, then `RetryRunBounds` holds of the model state for
  every header and every sparse output labelled with an epoch below `u64::MAX - 1`.
- `retryRunBounds_of_invariant`: if `Session::invariant` returns `true`, `SessionRefines` holds and `CounterHeadroom` holds,
  then `RetryRunBounds` holds of the model Triple state for every header and the sparse output of every Braid receive, at
  every Braid KEM model, state and message.
- `classicalMatch_of_inv`, `sparseMatch_of_inv`, `sparseCounters_transport`, `store_room`, `sparseOutputOf_epoch`: the steps
  of that derivation: the two match bounds from the stores' map clauses, the counter ceiling carried to the model's chain
  table, the store room under `cMax Usize`, and the epoch label of a Braid receive's output.
- `decryptRatchetRun_of_invariant`: `DecryptRatchetRun` from `Session::invariant`, `SessionRefines`, `CounterHeadroom` and
  `DecryptRatchetRunInputs`, the run record's three remaining fields word for word (the chunk relation, `HonestChunk`, one
  draw left in the trace).
- `decrypt_ratchet_refines_of_invariant`, `decrypt_ratchet_refines_of_invariant_statement`: under the oracle, codec, contract,
  derived-key and agreement hypotheses of `decrypt_ratchet_refines_complete`, `Session::invariant`, `SessionRefines`,
  `CounterHeadroom`, the trace equation and `DecryptRatchetRunInputs`
  (`DecryptRatchetRefinesOfInvariantStatement`), the generated `decrypt_ratchet` returns and `StepRefines` holds between its
  result and the model's step. `DecryptRatchetHeadroom` is not a hypothesis: it is `decryptHeadroom_of_invariant`, from two
  fields of the contract record.
- `counterHeadroom_sessionOf`: `CounterHeadroom` holds at every session over fresh states (clock 0, sparse epoch 0, no chain
  counter, Braid epoch 1). It exercises no ceiling away from zero, and `sparseCounters` holds vacuously there, the one
  chain-table entry holding no chain.
- `decrypt_inputs_at_invReal`, `DecryptOfInvariantHypotheses.refines`, `decrypt_of_invariant_hypotheses_jointly_satisfiable`:
  under the laws `DecryptJointLaws K dh` of `UnitLifecycleDecryptScreen`, every hypothesis of the restated theorem holds
  together at that module's witness session, for every codeword view; `DecryptOfInvariantHypotheses` is the hypothesis list,
  and the restated theorem applies to it. The witness state is built for the hypotheses, and the laws are assumed, as there.
  The witness is that fresh session, so no ceiling is exercised away from zero there; the next section gives a witness with
  stored keys, open chains and counters away from zero, and one beside the held-KEM Braid.
- `parkedTriple_invariant`, `structural_parkedSession`, `parkedSession_invariant`, `parkedSession_not_counterHeadroom`,
  `invariant_does_not_give_counterHeadroom`: a session over fresh states with the classical clock at `u32::MAX - 1` passes
  `Session::invariant` (under `ValidKeyShape`, `OptionEqU64Shape` and `DhCodecTotal`, as `sessionOf_invariant`) and fails
  `CounterHeadroom`, so the invariant does not give the ceilings.

**What is not shown.** That `CounterHeadroom` holds of any session a caller holds: it is a per-run hypothesis. That the
crate's operations produce the parked session: that the clamp parks the clock at `u32::MAX - 1` is the Rust's documented
behaviour, not a theorem here. That the other three ceilings exclude states the invariant accepts is by reading the sparse
ratchet's and the Braid's `invariant` documentation, not checked in Lean. That the Braid epoch ceiling covers the sparse one
where the bounds are used is by reading only. Whether any of the four ceilings could be dropped
from the refinement theorems that take them is not checked. The chunk, `HonestChunk` and draw conditions stay the caller's,
with the limits of the previous two sections. No proof here chooses a width of `usize`. As for the previous section, no gate
reads these hypotheses: `check-hypothesis-witnesses.sh` routes a section whose heading names a session lifecycle out.

**Compiler trust and pins.** `decrypt_ratchet_refines_of_invariant`, `decrypt_ratchet_refines_of_invariant_statement` and
`DecryptOfInvariantHypotheses.refines` are compiler-trusted: they apply `decrypt_ratchet_refines_complete` and list its nine
`native_decide` constants, and their pins list three more opaque constants than its pin, `Option::eq`,
`is_prime_order_public` and `kem::ciphertext_len`, each of which occurs in `Session::invariant`. The other sixteen results
rest on no compiler-evaluated constant: `classicalMatch_of_inv`, `sparseMatch_of_inv`, `sparseCounters_transport`,
`retryRunBounds_of_triple_invariant` and `parkedTriple_invariant` on `propext`, `Classical.choice` and `Quot.sound` alone,
`store_room` and `sparseOutputOf_epoch` on `propext` and `Quot.sound`, and the other nine on those three and between 4 and
52 opaque constants of the unit, which the types and definitions they mention refer to. Each result carries an axiom pin and a statement pin, and each definition the section adds
a `#print` pin (`CounterHeadroom`, `DecryptRatchetRunInputs`, `DecryptRatchetRefinesOfInvariantStatement`,
`DecryptOfInvariantHypotheses`, `parkedTriple`, `parkedSession`). `check-decrypt-ratchet-negatives.py` plants six faults in a
copy of the module (the sparse epoch ceiling dropped, the clock ceiling weakened to the invariant's, the output label dropped
from the Triple derivation, the parked clock moved one below the park, and the Braid ceiling weakened to the decoder's, once
without the pins, refused in `decryptRatchetRun_of_invariant`, and once with them, refused at the pin of `CounterHeadroom`) and
requires Lean to refuse each at a named declaration or at that pin.

## Proved (tier T3, session lifecycle: the invariant, the counter ceilings and the model relation at every successful `establish_initiator_for` output, and the receive at that session, on the eight-leaf unit)

Location: `Translation/UnitLifecycleEstablishInitiatorShape.lean`, `Translation/UnitLifecycleEstablishedDecrypt.lean`.

`decrypt_ratchet_refines_of_invariant` (previous section) takes `Session::invariant`, `SessionRefines` and `CounterHeadroom`
of the session it runs on, and until these results every session they were shown at was built for them (`sessionOf`,
`invReal`). These results derive the three from an actual establishment result: for every identity, published bundle,
expected identity and source of randomness, every session `s` with
`establish_initiator_for rc crc our bundle expected rng0 = ok (.Ok s, rng1)`; no concrete input is chosen. The model session
is `establishedModelOf dh s`, read off `s` through the DH view (the Triple through `ratchetAbs`/`spqrAbs`, the Braid through
`unsampledModelOf`); it is not shown to be the model's own `establishInitiator` output, and the T3 refinement of
`establish_initiator_for` is not here. `SessionRefines dh K s (establishedModelOf dh s)` holds by definition for every session
whose Braid is `KeysUnsampled` (each field of the relation is an equation through the abstraction functions), and its
uniqueness follows the same way; what the establishment supplies to the relation is that Braid state. The
establishment-specific content is `Session::invariant` and the four ceilings.

Of the clauses of `Session::invariant` at the output, these hold by construction (the value the code stores, or a recomputation
of the same opaque function on the same arguments): the ratchet key equals the Triple's sending key, the Braid has not failed,
its role (`is_initiator = some true` at epoch 1) differs from `is_responder = false`, the associated data is in initiator order,
the sparse direction `A2b` agrees with the role and with `started_as_sender = some true`, a pending initial message without an
established ephemeral, the classical invariant apart from its own key (the peer key canonical by the establishment's own check
of the signed prekey), the sparse invariant and the Braid invariant; the epoch clause also uses `OptionEqU64Shape` (assumed,
recorded in the headroom section). Two clauses hold vacuously at this state because `established_ephemeral = none`: the
`decode_ec` check of an established ephemeral in clause (f), and the responder branch of the orientation clause (c). The peer identity key passes `is_valid_identity_key` by inversion of `verify_bundle`. Our
identity key's validity, the ratchet key's canonical bytes and the pending ephemeral key's canonical bytes use the law
`DhPublicValid` (every public key `PrivateKey::public_key` returns has canonical bytes and is of prime order), and the pending
ciphertext's length uses the law `KemCiphertextLenOf` (a successful `kem::encapsulate` returns a ciphertext of length
`kem::ciphertext_len`). Both laws are assumed, true by reading of `tacenta-core/boundary/src/dh.rs` and
`tacenta-core/boundary/src/kem.rs`, not checked in Lean, and each has a model (`LIMITATIONS.md`, "The headroom records").

- `establish_initiator_for_parts`: every successful output is the session `InitiatorOutputParts.session` assembles from
  parts read off the generated function, with the facts the code checked or computed on the way; no hypothesis.
- `establish_initiator_for_admissible`: every successful output passes `Session::invariant`, under `DhPublicValid`,
  `KemCiphertextLenOf` and `OptionEqU64Shape`, all assumed.
- `counterHeadroom_of_established`: all four fields of `CounterHeadroom` hold at every successful output (the classical clock
  and both sparse chain counters 0, the sparse epoch 0, the Braid epoch 1); no hypothesis.
- `sessionRefines_established`: every successful output refines `establishedModelOf dh s`, for every DH view and KEM; no
  hypothesis. It holds by definition once the Braid is `KeysUnsampled` (above).
- `sessionRefines_established_unique`: every model session a successful output refines equals `establishedModelOf dh s`; no
  hypothesis, and by definition in the same way.
- `structural_parts`, `parts_invariant`, `initiatorTriple_invariant`, `counterHeadroom_parts`, `sessionRefines_parts`,
  `sessionRefines_parts_unique`: the same facts of the session the parts make; `initiatorTriple_invariant` is
  `Triple::invariant` of the Triple `init_sender` builds, given its two public keys are canonical.
- `init_sender_ok`, `braid_initiator_ok`, `verify_bundle_ok`: a successful `init_sender` returns that Triple, a successful
  `Braid::initiator` a `KeysUnsampled` Braid at epoch 1, and `verify_bundle` accepts only an identity key that passes
  `is_valid_identity_key`; no hypothesis.
- `dhPublicValid_canonical`, `dhPublicValid_valid`, `identity_public_valid`, `canonical_of_is_canonical_key`: under
  `DhPublicValid`, a public key `public_key` returns, our identity key among them, has canonical bytes and passes
  `is_valid_identity_key`; and `is_canonical_key` returning `true` gives the canonical test of the key's bytes, with no
  hypothesis.
- `singleton_length_le`, `verify_successBundle`, `shared_secret_successBundle`: steps of the inhabitation below: the side
  condition of a one-element vector, and `verify_bundle` and `initiator_shared_secret` succeeding on the bundle it uses
  when the signatures verify and the agreements are contributory.
- `dhPublicValid_is`, `kemCiphertextLenOf_is`, `model_dhPublicValid`, `model_kemCiphertextLen`: each law is its shape over
  an interpretation at the real constants, and the joint model satisfies each shape (`KemCiphertextLenLawShape` at the constant
  `ok 0`, since `Interp` has no field for `kem::ciphertext_len`).
- `establish_initiator_for_succeeds`, `established_initiator_inhabited`: under the axiom part of the initiator contract
  record and `InitiatorSuccessShape` (a self-equal valid key on which a signature verifies and every agreement is
  contributory, and a KEM key on which encapsulation succeeds), both assumed, a successful output exists for every identity
  and source state, and the invariant (under the three laws), the ceilings and the relation hold at it. The witness bundle
  uses one key as identity key and signed prekey and has no one-time prekey; the success branch with a one-time prekey is
  covered by the universal theorems above and is not shown inhabited.
- `establishment_hypotheses_satisfiable`, `model_initiatorSuccess`: those hypotheses and the three laws hold together in the
  joint model at the byte-stream source, in the substitution sense of `LIMITATIONS.md`; not a statement that the real
  primitives meet them.
- `honestChunk_established`: `HonestChunk` of the model session's Braid holds for every model message; no hypothesis.
- `established_initiator_decrypt_ratchet_hypotheses`: `DecryptOfInvariantHypotheses` holds at every successful output and
  `establishedModelOf dh s`, for every message and source state, given the boundary records (`DecryptOracleOf`, `DhCodecOf`,
  `DecryptRatchetContracts`, `DerivedKeysModel`, `DecryptRatchetAgreements oracle.braidKem`), the trace equation, the chunk
  relation and one draw, which are the caller's, and the three laws, all assumed.
- `established_initiator_decrypt_ratchet_refines`: under the same hypotheses, `decrypt_ratchet` at every successful output
  returns and its result refines the model's step, refusals included.
- `established_initiator_decrypt_refines`: under the same hypotheses, the public `Session::decrypt` at every successful
  output refines the model's `decrypt` for every message whose type byte is the ratchet type.
- `EstablishedDecryptHypotheses.refines`: the record `EstablishedDecryptHypotheses`, every hypothesis of
  `established_initiator_decrypt_refines` at one choice of every binder, gives that theorem's conclusion.
- `established_decrypt_hypotheses_jointly_satisfiable`, `sampleMessage_real_type`, `sampleMessage_chunk`: at the real
  constants, under the decrypt laws `DecryptJointLaws K dh` of `UnitLifecycleDecryptScreen`, the axiom part of the initiator
  contract record, `InitiatorSuccessShape`, `DhPublicValid` and `KemCiphertextLenOf`, all assumed, every field of the record
  holds together for every identity and codeword view: an oracle whose Braid KEM model is `K`, a successful establishment from
  the empty byte-stream source, and the sample ratchet frame (no agreement chunk) with one draw.
- `established_decrypt_laws_model`, `oneKey_length`, `oneKey_canonical`, `oneKey_ne_zero`: one interpretation,
  `Interp.modelEstablished` (`Interp.modelDecrypt` with a constant canonical public key), satisfies the shapes of all of those
  hypotheses together, with `toyKem`, `optionEqImpl` and the constant `ok 0` for `kem::ciphertext_len`, in the substitution
  sense of `LIMITATIONS.md`. `Interp.modelDecrypt` itself, the model of `DecryptJointLaws`, does not satisfy
  `DhPublicValidShape` (its public key is the private key's bytes, which need not be canonical), which is why the variant is
  needed; neither shows anything of the real primitives.

**What this establishes at a real state, and what it does not.** The success arm at an established initiator is
reached in an honest run through a copy of the session: a snapshot exported before the initiator's first `encrypt` and
restored after the responder replied decrypts that reply (`tacenta-core/tests/restored_initiator_receives_reply.rs`, on the
20 seeds it tries; a test, not a proof). A session value never copied leaves this state at its own first `encrypt`, which the
peer needs before it can reply. So the composed results cover success and refusal at this state. What they say of a step is
`StepRefines`: the result, the post-state and the draws left refine the model's step; for `decrypt_ratchet`, the model step
it is related to keeps the session on a refusal (`Model.Lifecycle.decryptRatchet_refusal_keeps_session`), so the real
post-state of a refusal refines the unchanged model session. "Every frame" is bounded by the caller's premises: a ratchet-type frame whose
agreement chunk, if it has one, meets `IncomingChunkRefines`, with at least one draw left. The chunk premise is not benign for
a frame from a sender who is not honest: a spliced or inconsistent chunk is outside the theorem whether the frame is refused
or accepted. Initial-type frames, `encrypt` and `establish_responder` are not covered; `import` is covered in the next section only. The two laws `DhPublicValid`
and `KemCiphertextLenOf` are assumed, as are `OptionEqU64Shape`, the boundary records, the chunk relation and the draw. As for
the previous sections, no gate reads these hypotheses: `check-hypothesis-witnesses.sh` routes a section whose heading names a
session lifecycle out.

**Compiler trust and pins.** `established_initiator_decrypt_ratchet_refines` and `established_initiator_decrypt_refines` are
compiler-trusted, and so is `EstablishedDecryptHypotheses.refines`: they apply `decrypt_ratchet_refines_of_invariant` and list
its nine `native_decide` constants and 57 opaque constants of the unit. Of the other 38 results, six rest on `propext`,
`Classical.choice` and `Quot.sound` alone (`singleton_length_le`, `initiatorTriple_invariant`, `sampleMessage_real_type`,
`oneKey_length`, `oneKey_canonical`, `oneKey_ne_zero`), and the other 32 on those three and between 1 and 57 opaque constants
of the unit, which the types and definitions they mention refer to. Each of the 41 results carries an axiom pin and a statement
pin, and each of the sixteen definitions the section adds a `#print` pin (`initChains`, `initiatorTriple`,
`InitiatorOutputParts`, `InitiatorOutputParts.session`, `DhPublicValidShape`, `DhPublicValid`, `KemCiphertextLenLawShape`,
`KemCiphertextLenOf`, `unsampledModelOf`, `establishedModelOf`, `InitiatorSuccessShape`, `successBundle`,
`EstablishedDecryptHypotheses`, `Interp.modelEstablished`, `viewEstablished`, `oneKey`). `check-established-negatives.py` plants
thirteen faults in copies of the two modules and requires Lean to refuse each at a named declaration or pin: the walk's Triple with its clock at 1 (refused in `init_sender_ok`); the structural invariant without
`DhPublicValid` for our identity key, without it for the ephemeral key, without `KemCiphertextLenOf` and without the
`verify_bundle` inversion (each refused in `structural_parts`); `DhPublicValid` without its prime-order clause (refused in
`dhPublicValid_valid`, and with the pins kept at the pin of `DhPublicValidShape`); the ceiling lemma restated at the output
with the clock parked at `u32::MAX - 1` and with the Braid epoch at `u64::MAX - 1` (each refused in `counterHeadroom_parts`);
the model session with the Braid epoch one higher and with empty associated data (each refused in `sessionRefines_parts`);
`InitiatorSuccessShape` without the key's self-equality (refused in `establish_initiator_for_succeeds`); and the joint model
with `Interp.modelDecrypt`'s public key (refused in `established_decrypt_laws_model`).

## Proved (tier T3, session lifecycle: `establish_responder` over every input, its outcomes and effects, and its inner receive, on the eight-leaf unit)

Location: `Translation/UnitLifecycleEstablishResponder.lean`.

The responder's public root `establish_responder` decodes the initial message, looks up the prekeys it names, computes the
shared secret, checks the last-resort replay record, builds a session, and only then runs `decrypt_ratchet` on the ratchet
frame the message carries; on success it commits the prekey store. These results compose that root for every responder
identity, prekey store, initial message and source of randomness, with no concrete input chosen, and derive the three
premises the `decrypt_ratchet` refinement takes about a session (`Session::invariant`, `CounterHeadroom`, `SessionRefines`)
for the session it builds, from that construction and not as assumptions. The parts of that session,
`ResponderPreparedParts`, are read off the generated function with the facts the code checked or computed on the way; the
model session is `responderModelOf dh p`, read off the parts through the DH view, with the Braid as the model's initial
responder state `Model.Braid.initBob` of the secret `Braid::responder` was given. It is not shown to be the session
`Model.Lifecycle.prepareResponder` builds, and the T3 refinement of the responder's establishment is not here.

**The outcomes and their effects.** Every return of the translated call is one of three outcomes
(`establish_responder_cases`, no hypothesis):

| Outcome | Result | Prekey store after | Random source after |
| --- | --- | --- | --- |
| refusal before the inner receive | one of the nine errors of `PrepareRefusal`: `Decode`, `UnknownPrekeyId`, `LegacyLastResortRecord`, `BadEncoding`, `Handshake(InvalidIdentityKey)`, `Handshake(NonContributoryAgreement)`, `Kem`, `ReplayedLastResort`, `LastResortRecordFull` | as given | as given |
| inner `decrypt_ratchet` refusal | its error | as given | the source `decrypt_ratchet` returned |
| inner success | `Ok (session', plaintext)` from `decrypt_ratchet` | `ResponderCommit` of the message's identifiers | the source `decrypt_ratchet` returned |

When the call reaches the inner receive (parts exist), it is exactly that receive followed by the commit, so such an input
is never refused before it (`establish_responder_at_parts`). Under the hypotheses of the `decrypt_ratchet` refinement the inner
step refines `Model.Lifecycle.decryptRatchet` at `responderModelOf dh p` (result, successor and draws, `StepRefines`): an inner
refusal maps to the model's refusal reason, the model step keeps its session, and the draws are unchanged or one shorter; an
inner success takes exactly one draw (`establish_responder_refines`). The success commit (`responderCommit_effects`, under
`DerivedKeysModel`) leaves every field of the store but the one-time curve prekeys, the one-time KEM prekeys and the replay
record unchanged; leaves the one-time KEM prekeys unchanged on the last-resort path and the one-time curve prekeys unchanged
when the message names none; leaves the replay record unchanged on the one-time path and, on the last-resort path, appends
exactly `(kem_id, fp)`, `fp` being `last_resort_fingerprint` of the shared secret (`replay_ok`). Which entry the two removals
take, and that the right one leaves, is not stated (`GAP-REGISTER.md`, row `E2E-03`).

**The intermediate session.** Of the clauses of `Session::invariant` at the session the call builds, these hold by
construction: the ratchet key's public bytes equal the Triple's sending key (both are computed from the same signed-prekey
bytes; the code computes the private key twice, `ResponderPreparedParts.ratchetPrivate_eq`), the Braid has not failed, its role
(`is_initiator = some false` at `NoHeaderReceived` epoch 1) differs from `is_responder = true`, the associated data is
`identity_ad` of the initiator's and our keys in that order, the sparse direction `B2a` agrees with the role, no pending
initial message with the established ephemeral, the classical invariant apart from its own key (no chain, no peer key, clock
0), the sparse invariant (one chain-table entry at epoch 0) and the Braid invariant's epoch clause. The initiator's identity
key passes `is_valid_identity_key` and the established ephemeral decodes by the code's own checks (`curve_inputs_ok`, and the
copy is the decoded bytes, `ResponderPreparedParts.ephemeralCopy_eq`). Our identity key's validity and the ratchet key's
canonical bytes use the law `DhPublicValid`; the epoch clause uses `OptionEqU64Shape`; the fresh header decoder's invariant
and size clause use the value law `DivCeilValue` and the `HEADER_LEN` bound `HeaderLenTotal` (a field of the decrypt
contracts). All four are assumed and recorded (`LIMITATIONS.md`). The four ceilings hold with no hypothesis (clock 0, sparse
epoch 0, both chain counters 0, Braid epoch 1). The relation's Braid half is the constructor's refinement
(`UnitSatisfiabilityBraidStates.responder_refines`, under `ErasureAgrees`, `KemLenAgrees`, `BraidHkdfAgrees`,
`ZeroizingArrayRoundTrip`, which the decrypt records carry, and `DivCeilValue`); every other field is an equation through the
abstraction functions.

- `establish_responder_cases`: every return is one of the three outcomes above, with the effects in the table; no hypothesis.
- `establish_responder_at_parts`: for every parts value of an input, the call equals the inner `decrypt_ratchet` on `p.session`
  and `p.message` followed by the store commit; no hypothesis.
- `responderCommit_effects`, `replay_ok`: what the success commit does to the store, under `DerivedKeysModel`, and what the
  replay check returns on each path; the second with no hypothesis.
- `signed_prekey_err`, `kem_slot_err`, `curve_inputs_err`, `one_time_key_err`, `decapsulate_err`, `shared_secret_err`,
  `replay_err`, `contributory_break_err`: the refusals each helper of the prepare phase can return; no hypothesis.
- `commit_kem_step`, `commit_one_time_step`, `take_one_time_kem_loop_frame`, `take_one_time_kem_frame`,
  `take_one_time_loop_frame`, `take_one_time_frame`, `vec_push_ok`: the commit's steps read off the code; the two removal
  steps change at most their own pool (the curve one under `DerivedKeysModel`); no other hypothesis.
- `responder_prepared_invariant`: the session handed to `decrypt_ratchet` passes `Session::invariant`, for every input that
  reaches it, under `DhPublicValid`, `OptionEqU64Shape`, `DivCeilValue` and `HeaderLenTotal`, all assumed.
- `responder_structural`, `responderTriple_invariant`, `fresh_decoder_invariant`, `hdr_decoder_checks`: its structural
  invariant under the first two, `Triple::invariant` of the Triple `init_receiver` builds given its key is canonical, and the
  fresh decoder's invariant and size clause under the last two.
- `init_receiver_ok`, `braid_responder_ok`, `hdr_decoder_ok`, `curve_inputs_ok`, `vecU8_clone_eq`,
  `ResponderPreparedParts.ratchetPrivate_eq`, `ResponderPreparedParts.braidSecret_eq`,
  `ResponderPreparedParts.ephemeralCopy_eq`: the shapes and facts the construction gives; no hypothesis.
- `counterHeadroom_responder_prepared`: all four ceilings at the intermediate session; no hypothesis.
- `sessionRefines_responder_prepared`: the intermediate session refines `responderModelOf dh p`, for every DH view and KEM,
  under the Braid agreements above, all assumed.
- `honestChunk_responder_iff`: `HonestChunk` at that model session asks exactly that a header chunk of epoch 1 comes from a
  96-byte message; no hypothesis. It stays the caller's.
- `decryptRatchet_oracle`, `random32_draws`: the model's `decryptRatchet` keeps the oracle or takes exactly one draw, and a
  success takes exactly one; no hypothesis.
- `responder_prepared_decrypt_refines`: at the intermediate session, under the boundary records of the `decrypt_ratchet`
  refinement (`DecryptOracleOf`, `DhCodecOf`, `DecryptRatchetContracts`, `DerivedKeysModel`, `DecryptRatchetAgreements`),
  `DhPublicValid`, `OptionEqU64Shape`, `DivCeilValue`, the trace equation and the run's inputs (the chunk relation,
  `HonestChunk`, one draw), all the caller's or assumed, the inner `decrypt_ratchet` returns and its result refines the model's
  step.
- `establish_responder_refines`: the three outcomes with the inner step refined and the draws stated, under the same
  hypotheses, the run's inputs asked of every parts value of the input.
- `ResponderRouteHypotheses.refines`: the record `ResponderRouteHypotheses` (every hypothesis of
  `establish_responder_refines`, the call's return, and that the call reaches the inner receive) gives that theorem's
  conclusion.
- `establish_responder_returns`: the call returns for every input under the contracts and the store bound of
  `establish_responder_no_panic`, so the outcome theorem speaks of every input there.
- `establish_responder_short_message_refused`, `establish_responder_unknown_prekey_refused`: a message shorter than two bytes
  is refused as `Decode(TooShort)` at every prekey store, and a well-formed message naming signed prekey 0 at every store
  whose signed prekey is another with no previous one as `UnknownPrekeyId`, each with the store and the source as given;
  no hypothesis. These are statements over stores; no store value is derivable in Lean without `ResponderSuccessShape`.
- `establish_responder_legacy_refused`: at every store whose KEM key 0 carries the legacy marker (and whose signed prekey
  is 0) the message is refused as `LegacyLastResortRecord`, store and source as given, under the zeroizing round trip only;
  a statement over stores, as above.
- `establish_responder_noncontributory_refused`, `establish_responder_replay_refused`, `establish_responder_record_full_refused`:
  under the contracts of `establish_responder_no_panic`, `ResponderSuccessShape` and, for the first, `ZeroKeyShape`, all
  assumed, the call is refused as `Handshake(NonContributoryAgreement)` at a message whose ephemeral key is the zero key, as
  `ReplayedLastResort` at a store whose record holds that handshake's fingerprint, and as `LastResortRecordFull` at a store
  whose record holds 1024 other entries for the key, each with the store and the source as given. All these premises hold
  together in one model interpretation (`responder_route_laws_model`, with the contracts from its axiom part and laws).
- `responder_prepared_inhabited`: under the same contracts and `ResponderSuccessShape`, for every identity and every frame of
  at most 4096 bytes, an input reaching the inner receive exists, at a store with an empty replay record and a last-resort KEM
  key.
- `responder_route_hypotheses_jointly_satisfiable`, `sampleMessage_le`: at the real constants, under the decrypt laws
  `DecryptJointLaws K dh`, the axiom part of the responder contract record, `ResponderSuccessShape` and `DhPublicValid`, all
  assumed, every field of `ResponderRouteHypotheses` holds together for every identity and codeword view, at an input that
  reaches the inner receive with the sample ratchet frame (no agreement chunk) and one draw.
- `responder_route_inner_refusal_reachable`: there, with `ZeroKeyShape`, the call returns the inner refusal that maps to the
  model's `NonContributoryAgreement`, with the store as given; its whole premise list holds in `responder_route_laws_model`.
- `responder_route_laws_model`: one interpretation, `Interp.modelEstablished`, satisfies the shapes of the decrypt laws, the
  responder contract axioms, `ResponderSuccessShape`, `DhPublicValidShape` and `ZeroKeyShape` together, in the substitution sense of
  `LIMITATIONS.md`; not a statement that the real primitives meet them.
- `readBe32_be32`, `takeSplit_append`, `decodeInitial_encodeInitial`: the model's initial-message decoder returns the fields its
  encoder wrote, for two canonical 33-byte keys and a ciphertext shorter than `2^32` bytes; no hypothesis.
- `wireKey_length`, `wireKey_curve`, `wireKey_key`, `ephKey_length`, `ephKey_curve`, `ephKey_key`, `successBytes_length`,
  `successBytes_le`, `decode_successMessage`, `successMessage_decoded`, `decode_ec_wireKey`, `decode_ec_zeroWire`,
  `replay_fresh`, `map_u8_inj`, `u32_of_ofNat`, `basePoint_length`, `arrayOf_basePoint`, `basePoint_canonical`,
  `responder_shared_secret_ok`, `array_eq_decide`, `replay_loop_absent`, `seen_for_loop_all`, `array_eq_self`,
  `full_record_length_le`, `otherThan_ne`: steps of the inhabitations above (the message they use, its decode by the real
  `decode_initial`, the key decodes, the replay check on an empty, a one-entry and a 1024-entry record, the shared secret, the
  array equality); hypothesis-free except `decode_ec_wireKey` and `decode_ec_zeroWire` (a `from_bytes` result),
  `responder_shared_secret_ok` (the zeroizing round trip and model, the session HKDF, an identity check that passes and
  contributory agreements) and `replay_fresh`
  (HMAC totality).

**What this establishes, and what it does not.** For every input the three outcomes and their store and random-source
effects are proved of the translated function, and at the session it builds the `decrypt_ratchet` refinement applies, with its
session premises derived. These were not stated before for this root: the earlier frame result
(`establish_responder_err_leaves_store`) said nothing about the random source and no theorem stated the success store effect.
Reached, at the real constants, under the contracts and `ResponderSuccessShape` (and `ZeroKeyShape` for two of them),
all in one model interpretation: the refusals `Handshake(NonContributoryAgreement)`, `ReplayedLastResort` and
`LastResortRecordFull`, the inner receive, and an inner refusal. Stated over stores: `Decode(TooShort)` is returned, with no
hypothesis, at every prekey store; `UnknownPrekeyId` (no hypothesis) and `LegacyLastResortRecord` (the zeroizing round trip)
at every store of a stated shape. The prekey store has fields of the opaque key types, of which no value is derivable in Lean,
so a store value at which these three are returned is exhibited only under `ResponderSuccessShape`. **Not shown:** a success of the whole call. No input is
exhibited at which the inner `decrypt_ratchet` succeeds; `establish_responder_at_parts` makes the condition exact. Honest
successes are tested only (`tacenta-core/tests/full_session.rs` and the other responder tests, `GAP-REGISTER.md`, row
`E2E-07`). Not shown reached: `BadEncoding` (not reachable once `decode_initial` has accepted, by reading
`tacenta-core/wire/src/lib.rs`, whose canonical-key checks precede `decode_ec`'s; not checked in Lean),
`Handshake(InvalidIdentityKey)` and `Kem` (the joint model's prime-order check and KEM decapsulation accept every input, so a
shape that refuses could not be shown satisfiable there). The run's chunk relation, `HonestChunk`, the trace equation and the
draw are the caller's and are asked of every parts value of the input; an attacker chooses the chunk. Not covered: the
initiator's frame and the plaintext, the successor's invariant, the responder's next operation, that
`responderModelOf dh p` is the model's prepared session, the model's `establishResponder` equality, which entry a removal
takes, and a source with no state of its own such as `OsRng`.

**Compiler trust and pins.** `responder_prepared_decrypt_refines`, `establish_responder_refines`,
`ResponderRouteHypotheses.refines` and `responder_route_inner_refusal_reachable` are compiler-trusted: they apply
`decrypt_ratchet_refines_of_invariant` and list its nine `native_decide` constants and 57 opaque constants of the unit. Of the
other 76 results, 29 rest on `propext`, `Classical.choice` and `Quot.sound` alone (some on a subset of them), and 47 on those
three and between 1 and 57 opaque constants of the unit, which the types and definitions they mention refer to. Each of the 80
results carries an axiom pin and a statement pin, and each of the 22 definitions the section adds a `#print` pin (`z32`,
`fullSlice`, `ResponderPreparedParts`, `ResponderPreparedParts.session`, `ResponderPreparedParts.message`, `ResponderCommit`,
`PrepareRefusal`, `responderChains`, `responderTriple`, `responderModelOf`, `basePointBytes`, `wireKey`, `zeroWire`,
`ephKey`, `successBytes`, `successMessage`, `basePoint`, `ResponderSuccessShape`, `ZeroKeyShape`, `successStore`,
`ResponderRouteHypotheses`, `otherThan`). `check-responder-negatives.py` plants nineteen faults in a copy of the module and
requires Lean to refuse each at a named declaration or pin, against a message naming the change: the structural invariant
without our identity law, the initiator's identity check or the ephemeral decode check, and the session without its
established ephemeral (each refused in `responder_structural`); the decoder sized without the MAC and without the `HEADER_LEN`
bound (refused in `hdr_decoder_checks`) and the fresh decoder without its chunk bound (refused in `fresh_decoder_invariant`);
the ceilings at the parked clock (refused in `counterHeadroom_responder_prepared`); the model's Braid as the initiator's and
its associated data empty (refused in `sessionRefines_responder_prepared`); `ReplayedLastResort` dropped from the refusals, the
success commit without its removals, and an inner refusal returning the given source (refused in `establish_responder_cases`);
the commit leaving the replay record unchanged with a fingerprint and the one-time KEM prekeys unchanged on the one-time path
(refused in `responderCommit_effects`); an inner success giving a draw back (refused in `establish_responder_refines`); a model
success keeping the oracle (refused in `decryptRatchet_oracle`); the joint model at the zero base point (refused in
`responder_route_laws_model`); and the commit recording key identifier 0 in the replay record with its pins kept (refused at
the pin of `ResponderCommit`). The first three and the decoder check without the `HEADER_LEN` bound are proof-dependency
controls: they replace a step of a proof and leave the statement unchanged, so they show the proof uses the fact, not that the
statement needs it; the other fifteen change a statement or a definition. An error that is not a refusal (an unresolved name, a
syntax error) voids a run anywhere in the copy, compared without regard to case.

## Proved (tier T3 witnesses, session lifecycle: invariant-passing session states that are not fresh, and the restated `decrypt_ratchet` hypotheses at stored keys, on the eight-leaf unit)

Location: `Translation/UnitLifecycleDecryptStates.lean`.

The joint witness of the previous section is a session over fresh states (empty stores, no receiving chain, clock 0, sparse
epoch 0, no chain, Braid epoch 1). These results build sessions that `Session::invariant` accepts and that are not fresh,
and show the hypotheses of `decrypt_ratchet_refines_of_invariant` together at one of them. Every state is built for the
hypotheses, not shown produced by the code: none is shown to come from `establish_initiator`, `establish_responder` or
`import`, or from any sequence of operations.

The states. `responderSession`: an established ephemeral key (`ephemeralOf a`, the curve byte `0x05` then the 32 bytes of
the canonical key `a`), no pending initial message, a classical receiver with no chain, sparse epoch 1, direction `B2a`, and a
Braid in `KeysUnsampled` at epoch 2. `pendingSession`: the fresh session with a pending initial message whose ephemeral is the
identity key and whose KEM ciphertext has the length `kem::ciphertext_len` returns. `storedSession`: a Triple
(`storedTriple a 2`) with both classical chains open, a peer key, `ns = 3`, `nr = 4`, `pn = 2`, `events = 5` and one stored
classical key (`n = 2`, `stored_at = 4`), and a sparse ratchet at epoch 2 with one chain-table entry holding a send chain at
counter 7 and a receive chain at counter 6 and one stored sparse key (epoch 2, `n = 3`); the Braid is `KeysUnsampled` at
epoch 3. `heldStoredSession`: `storedTriple a 0` beside the Braid of `UnitHeldKemWitness` (`KeysSampled` at epoch 1, holding
a generated key pair). Every state is a session with itself: `ValidKeyShape` gives one valid key, so both identities are the
key `pkb`, and in `storedTriple` the peer ratchet key `dhr_pub` and the stored classical key's `dh` are our own ratchet key
`a`, the bytes of that identity key. The "peer key" below is that key, not a second party's.

What each state assumes. `pendingSession_invariant`, `storedSession_invariant` and `heldStoredSession_invariant` take what
`sessionOf_invariant` takes: the key material of `ValidKeyShape` as hypotheses, `OptionEqU64Shape` and the associated data
`identity_ad` returns. `responderSession_invariant` also takes `DhCodecTotal` (assumed; carried by every contract record and a
field of `DecryptJointLaws`), for `PublicKeyBytes::from_bytes` on the key `decode_ec` extracts. `pendingSession_invariant`
also takes `kem::ciphertext_len = ok n`, and `pending_state_exists` takes `KemCiphertextLenTotal` (assumed; a T1 contract of
`UnitLifecycleT1`). `kem::ciphertext_len` is opaque: that it returns 1568 is not stated or checked. `heldStoredSession_invariant`
also takes the held Braid's invariant, which `heldBraid_invariant` gives under that module's laws.

- `responderSession_invariant`, `structural_responderSession`, `responderTriple_invariant`: `Session::invariant` returns `true`
  at the responder state: clause (b) at sparse epoch 1 and Braid epoch 2, (c) on the responder's branch (both identities are
  `pkb`, so the orientation is not distinguished, and a swapped orientation would pass as well), (d) with both halves on the
  responder's side, (e) and (f) on the `established_ephemeral` arm, and the Triple's role agreement with
  `started_as_sender = some false`.
- `canonicalKey_ephemeral`, `session_decode_ec_ephemeral`, `decode_ec_ephemeral`: the steps of the (f) arm: the translated
  `decode_ec` accepts `ephemeralOf a` when `a` is canonical, and the unit's `decode_ec` returns `some` under `DhCodecTotal`.
- `classicalStore_nil_le`, `sparseStore_nil_le`, `responderChains_le`: the length side conditions of the responder Triple's
  three vectors, stated as named results so that the definition and its `#print` pin carry no auxiliary proof constant.
- `pendingSession_invariant`, `structural_pendingSession`: `Session::invariant` returns `true` at the pending state, for every
  ciphertext of the length `kem::ciphertext_len` returns: (e) with the pending message, (f) on the ciphertext-length arm, (h)
  on the pending ephemeral.
- `storedSession_invariant`, `structural_storedSession`, `storedTriple_invariant`, `window_of`: `Session::invariant` returns
  `true` at the stored-key state, and `Triple::invariant` at `storedTriple a E` for every sparse epoch `E` with
  `E + 2 <= u64::MAX`: every clause of the classical and sparse invariants on a store of one key each, (b) at sparse epoch 2
  and Braid epoch 3. The three clauses that no two entries collide (`store_map`, `chains_distinct`, `skipped_map`) hold
  vacuously on those one-element lists; the repeated-header negative below shows the classical one can fail. With both classical chains open `started_as_sender` is `none`, so the role agreement holds by that arm.
- `responder_state_exists`, `pending_state_exists`, `stored_state_exists`: under `ValidKeyShape`, `OptionEqU64Shape` and
  `DhCodecTotal` (with `KemCiphertextLenTotal` for the second), each kind of state exists; the third also meets
  `CounterHeadroom` and has the shape `StoredKeysShape 2 3`.
- `storedSession_sessionRefines`, `storedSession_counterHeadroom`, `storedSession_retryRunBounds`: at the stored-key state,
  `SessionRefines` holds to `storedModel` at every Braid KEM model, `CounterHeadroom` holds, and `RetryRunBounds` holds by
  `retryRunBounds_of_invariant` for every header and the sparse output of every Braid receive.
- `stored_classicalMatch_tight`, `stored_sparseMatch_tight`: for a header chosen to name a stored key, the model store's
  filter has exactly one entry, so the `<= 1` bounds of `RetryRunBounds.classicalMatch` and `sparseMatch` are met with
  equality there. This is not the run's header.
- `stored_run_header_names_no_stored_key`: at the header of the run the joint statement instantiates (the first witness's
  message: classical `n = 1`, sparse `(0, 1)`), both filters of the stored-key model are empty, against the stored keys'
  classical `n = 2` and sparse `(2, 3)`.
- `stored_model_refuses_of_agreement`: the model's step at the stored-key state refuses at the first agreement when the
  oracle's agreement refuses the all-zero ratchet key. No law states that premise; that the real agreement refuses that key
  is by reading the X25519 boundary (`invReal_agreement_is_real`).
- `storedSession_runInputs`, `storedSession_shape`, `decrypt_of_invariant_hypotheses_at_stored`,
  `decrypt_of_invariant_hypotheses_jointly_satisfiable_at_stored_keys`: under the laws `DecryptJointLaws K dh` (assumed, as in
  `UnitLifecycleDecryptScreen`), every field of `DecryptOfInvariantHypotheses` holds together at a session with the shape
  `StoredKeysShape 2 3` and its model, at the first witness's message and source, for every codeword view. The chunk and
  honest fields of `DecryptRatchetRunInputs` are met only by the arm for a message without a chunk. `StoredKeysShape` fixes
  the stores, the open chains, the classical counters and the two epochs, and not the sparse chain counters: the joint
  statements do not carry the counters 7 and 6, which only `storedSession_counterHeadroom` and
  `heldStoredSession_counterHeadroom`, at the concrete states, use.
- `structural_heldStoredSession`, `heldStoredSession_invariant`, `heldStoredSession_sessionRefines`,
  `heldStoredSession_counterHeadroom`, `heldStoredSession_shape`, `heldStoredSession_runInputs`,
  `decrypt_of_invariant_hypotheses_jointly_satisfiable_at_stored_keys_held`: the same at the stored-key Triple beside the held
  Braid, under `DecryptWrapperLaws dh` and `LawGenerateSucceeds` (assumed, as in `UnitHeldKemWitness`), with `HeldKemAt` and
  the shape `StoredKeysShape 0 1`.

**Which ceilings are exercised.** At `storedSession` the four fields of `CounterHeadroom` are met away from zero: the clock at
5, the sparse epoch at 2, two chain counters (7 and 6; at the fresh witness the table holds no chain and that field held
vacuously) and the Braid epoch at 3. At `heldStoredSession` the clock and the two chain counters are away from zero; the
sparse epoch (0) and the Braid epoch (1) are at their least values. Of the eleven fields of `RetryRunBounds` at
`storedSession`, ten are met over non-empty data: both match bounds (tight for headers naming a stored key, not the run's,
at which both filters are empty), both stores and the chain-table room (each at length 1, far from binding), the chain-table
and stored-key epoch fields, and the counters; `sparseOutputEpoch` still holds vacuously at the run, whose Braid receive
returns no output. No counter
is near its ceiling: the parked session of the previous section is the edge for the clock.

**What is not shown.** That any of these states is produced by the code, or kept by an operation. A run that carries an
agreement chunk at them. The restated theorem at the responder or the pending state, which are shown to pass the invariant
only. That the run reads the stored keys: it does not, because the run's header names neither
(`stored_run_header_names_no_stored_key`); and the model's step refuses at the first agreement if the oracle's agreement
refuses the all-zero key (`stored_model_refuses_of_agreement`), a premise that holds only by reading. A session between two
distinct identities. No proof
here chooses a width of `usize`. As for the previous section, `check-hypothesis-witnesses.sh` routes this section out.

**Compiler trust and pins.** No result here rests on a compiler-evaluated constant. `canonicalKey_ephemeral`,
`session_decode_ec_ephemeral`, `classicalStore_nil_le`, `sparseStore_nil_le`, `responderChains_le`,
`responderTriple_invariant`, `window_of` and `storedTriple_invariant` rest on `propext`, `Classical.choice` and `Quot.sound`
alone; the other twenty-eight on those three and between 4 and 52 opaque constants of the
unit (`stored_run_header_names_no_stored_key` and `stored_model_refuses_of_agreement` list 4). `storedSession_invariant`, `pendingSession_invariant` and `heldStoredSession_invariant` list eighteen, among them
`is_prime_order_public`, `kem::ciphertext_len`, `PublicKeyBytes::from_bytes` and `Option::eq`; `responderSession_invariant`
lists twenty-two, adding `PrivateKey::from_bytes`, `PrivateKey::to_bytes`, the `PublicKeyBytes` equality and `Zeroizing`,
which `DhCodecTotal` names; the three existence theorems and the three joint statements list fifty-two. Each result carries an
axiom pin and a statement pin, and each of the fourteen definitions a `#print` pin. `check-decrypt-ratchet-negatives.py`
plants nine faults in a copy of the module without its pins (a second stored classical key under the same header, the stored
key ahead of the clock, the sparse stored key at an epoch the table does not hold, the clock at the park `u32::MAX - 1`, the
sparse epoch off the Braid's relation (clause (b) alone), the Braid at an even epoch with the sparse epoch moved to keep (b)
(clause (d) alone), the responder on the initiator's sparse direction, the pending ciphertext one byte longer than
`kem::ciphertext_len`, the ephemeral's curve byte wrong) and requires Lean to refuse each at a named declaration. At the
parked clock the invariant proofs still pass and `storedSession_counterHeadroom` is refused.

## Proved (tier T3, session lifecycle: what an accepted `Session::import` gives, the restored session's relation and receive, and the round trip of an established initiator session, on the eight-leaf unit)

Location: `Translation/UnitLifecycleRestoredSession.lean`, `Translation/UnitLifecycleSessionRoundTrip.lean`, `Translation/UnitLifecycleSessionCodec.lean`.

These results start from the bytes `Session::import` accepted: for every byte string `b` and every session `s` with
`lifecycle.Session.import b = ok (.Ok s)` (`import` takes no randomness, so that is its success form). The model session is
`restoredModelOf dh s`, a function of `s` and so of `b`: the same reading as `establishedModelOf` (Triple through
`ratchetAbs`/`spqrAbs`, Braid through `unsampledModelOf`, the other fields through the DH view). It is not the model's own
imported session, because `Model.Lifecycle` has none: the model's `Model.PersistedState.SessionState.ofBytes` returns the
stored format, whose Braid is bytes. **Acceptance and continuation are kept apart.** Of what the next operation consumes,
acceptance gives only `Session::invariant` (acceptance also means `export` writes the accepted bytes back unchanged, the
`NonCanonical` check, which no theorem here uses); the next operation also consumes the scope and the four counter ceilings,
which are premises, stated as such. The relation is claimed only in scope, `RestoredScope s`: the Braid is in `KeysUnsampled` or in `Failed` (which
`Session::invariant` accepts: the failure is terminal and persists). It excludes the seven Braid states that hold a key
pair or an encapsulation state, because a key pair restored by `IncrementalKeyPair::from_bytes` or a state restored by
`EncapsState::from_bytes` has no model value at the wrapper's KEM model (`UnitKemWrapperModel.lean`), and the three that
hold an erasure encoder or decoder and no KEM value (`Ct2Sampled`, `NoHeaderReceived`, `HeaderReceived`), because
`EncoderRefines` and `DecoderRefines` record a history (a source slice and a number of steps; answers to future chunks
against one source) that a restored value does not have and no law here supplies. In practice the scope is narrow. The first `encrypt` from `KeysUnsampled` moves the Braid to `KeysSampled`
(`tacenta-core/braid/src/lib.rs:706-724`), a responder starts in `NoHeaderReceived` (`lib.rs:420-428`), and a Braid returns
to `KeysUnsampled` only on the side that sent the last ciphertext, when it learns the next epoch has begun
(`lib.rs:1355-1368`). So the restored relation covers a snapshot taken on the side holding `KeysUnsampled` before its first send in that
epoch (at epoch 1, the established initiator, which the round trip below and the test cover), and a failed session; most
snapshots taken mid-conversation are out of scope.

- `import_ok_gives_invariant`: every session `import` accepts passes `Session::invariant`; no hypothesis (the generated
  body reaches `Ok` only after `invariant` returned `true`; every other branch returns an `Err`).
- `counterHeadroom_iff_check`: `CounterHeadroom s` holds exactly when the decidable
  `headroomCheck s` does (the classical clock, the sparse epoch, every sparse chain counter and the Braid epoch, each below
  its ceiling), for every session and so at every accepted import; no hypothesis. Acceptance does not give it:
  `invariant_does_not_give_counterHeadroom` (previous sections) has a session with the classical clock parked at
  `u32::MAX - 1` pass the invariant, and `import` checks nothing about counters beyond the invariant. That `import` accepts
  such a session's bytes is not shown here.
- `sessionRefines_restored`, `sessionRefines_restored_unique`: in scope, `SessionRefines dh K s (restoredModelOf dh s)` for
  every DH view and KEM, and every related model session equals `restoredModelOf dh s`; no hypothesis. Both hold **by
  definition**, as at an established session: each field of the relation is an equation through the abstraction functions,
  the `KeysUnsampled` arm compares the epoch and the authenticator, and the `Failed` arm is `True`.
- `honestChunk_restored`: in scope, `HonestChunk` of the model Braid holds for every model message; no hypothesis.
- `RestoredDecryptHypotheses.ofInvariant`, `RestoredDecryptHypotheses.refines`, `restored_decrypt_refines`: the record
  `RestoredDecryptHypotheses` packs the accepted import, the scope, `CounterHeadroom`, the boundary records
  (`DecryptOracleOf`, `DhCodecOf`, `DecryptRatchetContracts`, `DerivedKeysModel`, `DecryptRatchetAgreements oracle.braidKem`),
  the trace equation, the frame's ratchet type, the chunk relation and one draw, all of them the caller's and assumed; from it
  `DecryptOfInvariantHypotheses` holds at `s` and `restoredModelOf dh s` (the invariant from acceptance, the relation and
  `HonestChunk` from the scope), and the public `Session::decrypt` at `s` on that frame refines `Model.Lifecycle.decrypt` at
  `restoredModelOf dh s`, refusals included (through `decrypt_ratchet_refines_of_invariant` and
  `decrypt_ratchet_message_refines`).
- `export_import_established`: for every success output `s` of `establish_initiator_for`, `export s` returns, and `import`
  of the exported bytes accepts and returns `s` itself, every field equal; under nine assumed laws, the six below and the
  establishment's `KemCiphertextLenOf`, `DhPublicValid` and `OptionEqU64Shape`. No field differs: the ratchet private key and the three public keys
  come back through the byte-codec laws, everything else is read back by the translated decoders.
- `restored_established_continues`, `restored_established_initiator_decrypt_refines`: under the same nine laws, that accepted
  copy is in scope and meets `CounterHeadroom` (it is the establishment output), and `restored_decrypt_refines` applies to
  it: the public `Session::decrypt` of the restored copy on every ratchet-type frame refines the model's `decrypt` at
  `restoredModelOf dh s`, given the caller's boundary records, trace equation, chunk relation and draw, all assumed. This is
  the theorem form of what `tacenta-core/tests/restored_initiator_receives_reply.rs` tests on the shipping crate (that a
  restored copy decrypts the reply, a test on the seeds it tries); the theorem is about the translated session unit, says
  nothing about what an honest peer sends, and nothing about whether restoring an older snapshot is safe.
- `codecShape_parts`: the session an establishment's parts make has the shape the round trip covers (Braid `KeysUnsampled`
  at epoch 1, no stored key in either ratchet, the one sparse chain-table entry with both chains, a pending initial
  message, no established ephemeral, 66 bytes of associated data, a ciphertext of `kem::ciphertext_len` bytes), under
  `DhPublicBytesRoundTrip`, `KemCiphertextLenOf` and `KemCiphertextLenBound`, all assumed.
- `restored_established_inhabited`: under the axiom part of the initiator contract record and `InitiatorSuccessShape`
  (which give a successful establishment, previous section) and the laws above, all assumed, such an established session
  and its accepted copy exist for every identity and source state.
- `restored_laws_model`, `model_kemCiphertextLenBound`: one interpretation satisfies the nine laws' shapes together
  (`Interp.model` for the byte-codec laws, `optionBranchImpl` and `vecAsSliceImpl` for the two library functions,
  `optionEqImpl`, and `ok 0` for `kem::ciphertext_len`), in the substitution sense of `LIMITATIONS.md`; not a statement that
  the real functions meet them. It is not a model of the decrypt laws.
- `restored_decrypt_hypotheses_jointly_satisfiable`: every field of `RestoredDecryptHypotheses` holds together at the real
  constants, under the decrypt laws `DecryptJointLaws K dh` (which include `OptionEqU64Shape`), the axiom part of the
  initiator contract record and `InitiatorSuccessShape` at the byte-stream source, `DhPublicValid`, `KemCiphertextLenOf` and
  the six laws below, all assumed: for every identity and codeword view there are an oracle with `braidKem = K`, a session
  and the bytes `export` writes for it, which `import` accepts with that session, in scope and with the ceilings, with every
  boundary record, the trace equation, the frame type, the chunk relation and the draw, at the sample ratchet frame and
  source. The session is the established one of `established_decrypt_hypotheses_jointly_satisfiable`, restored by
  `restored_established_continues`.
- `restored_decrypt_laws_model`, `restored_laws_model_established`: the whole premise list of that statement holds in one
  interpretation, `Interp.modelEstablished` (previous section), with its view, `toyKem`, `optionEqImpl` and `ok 0` for
  `kem::ciphertext_len` in both ciphertext laws: `established_decrypt_laws_model` for the decrypt laws, the contract axioms,
  `InitiatorSuccessShape`, `DhPublicValid` and `KemCiphertextLenOf`, and `restored_laws_model_established` for the six laws
  of the round trip at the same interpretation. In the substitution sense of `LIMITATIONS.md`; neither shows anything of the
  real primitives.
- `export_import_of_shape`, `export_spec`, `import_unchecked_spec`, `session_invariant_leaves`, `slice_ne_self`,
  `identity_ad_length_of`: the round trip for every session with `CodecShape` that passes `Session::invariant`, under the
  five laws of `UnitLifecycleSessionCodec.lean`, all assumed: `export` returns the bytes `sessionEnc` of the leaf encodings,
  the field-by-field decode returns the session, the canonical re-encode compares a slice with itself, and the invariant is
  the session's own; `Session::invariant` gives the Triple's and the Braid's own invariants (which the leaf decoders
  re-check); the associated data is 66 bytes once the public-key byte view returns.
- `ratchet_to_bytes_spec`, `ratchet_from_bytes_of`, `spqr_to_bytes_spec`, `spqr_from_bytes_of`, `triple_to_bytes_spec`,
  `triple_from_bytes_of`, `braid_to_bytes_spec`, `braid_from_bytes_of`, `pending_to_bytes_spec`, `pending_from_bytes_of`:
  for the classical ratchet with no stored key, the sparse ratchet with one chain-table entry (both chains present) and no
  stored key, the Triple of the two, the Braid in `KeysUnsampled` below epoch `u64::MAX` (which its reader refuses) and the
  pending initial message, the translated encoder writes the list `ratchetEnc`, `spqrEnc`, `tripleEnc`, `braidEnc`,
  `pendEnc`, and the translated decoder reads that list back to the value, given the leaf's own invariant; the encoders under
  `ZeroizingVecRoundTrip` (assumed) where they wrap their output, the session-level reader under `OptionBranchSome`
  (assumed).
- `read_key_of`, `read_u32_of`, `read_u64_of`, `read_epoch_of`, `read_auth_of`, `read_optional_key_of`,
  `read_optional_key_loop_zero`, `index_usize_of`, `decode_chain_of`, `decode_chains_entry_of`,
  `decode_state_unsampled_of`, `triple_take_len_prefixed_of`, `lifecycle_take_len_prefixed_of`, `auth_from_bytes_of`,
  `direction_from_byte_dirByte`, `spqr_from_bytes_loop0_one`, `spqr_from_bytes_loop1_empty`, `triple_invariant_parts`:
  each translated reading step returns the value written at the position it reads, stated through `List.drop`, with no
  hypothesis (the session-level `take_len_prefixed` under `OptionBranchSome`, assumed); the Triple's invariant gives both
  ratchets' invariants.
- `push_optional_key_enc`, `push_optional_chain_some`, `lifecycle_push_len_prefixed_spec`, `auth_to_bytes_spec`,
  `ratchet_to_bytes_loop_empty`, `ratchet_to_bytes_loop_empty_spec`, `spqr_to_bytes_loop0_one`, `spqr_to_bytes_loop1_empty`,
  `spqr_encoded_len_eq`, `label_to_byte_spec`, `direction_to_byte_spec`, `efs_val`, `zeroizing_new_spec`: each translated
  writing step appends the bytes stated; no hypothesis, except `zeroizing_new_spec` under `ZeroizingVecRoundTrip`.
- `from_be32`, `from_be64`, `u32_eq_of_bv`, `u64_eq_of_bv`, `fromBEBytes_toBEBytes_toNat`, `fromBEBytes_toNat_congr`,
  `fromLEBytes_toNat_congr`, `drop_next`, `slice_of_drop`, `length_of_drop`, `getElem_of_drop`, `from_slice_eq`,
  `setSlice_app`, `usize_add_eq`, `usize_div_eq`, `slice_len_eq`, `cast_len_val`, `arr32_len`, `be32_length`,
  `be64_length`, `optKeyEnc_length`, `ratchetEnc_length`, `chainEnc_length`, `spqrEnc_length`, `tripleEnc_length`,
  `authEnc_length`, `braidEnc_length`, `lenEnc_length`, `pendEnc_length`, `chain_len_eq`, `chains_len_eq`,
  `skipped_len_eq`, `fixed_prefix_eq`, `head_len_eq`, `epoch_and_auth_len_eq`: byte, list and length facts the steps use
  (big-endian bytes read back to the integer written, lengths of the encodings, the codec length constants); no
  hypothesis.
- `dhPublicBytesRoundTrip_is`, `dhPrivateBytesRoundTrip_is`, `zeroizingVecRoundTrip_is`, `model_dhPublicBytesRoundTrip`,
  `model_dhPrivateBytesRoundTrip`, `model_zeroizingVecRoundTrip`, `vecAsSliceImpl_shape`: each byte-codec law is its shape at
  the real constants, and `Interp.model` (or `vecAsSliceImpl`) satisfies each shape.

**The laws.** Six of the round trip's own, all assumed, none checked in Lean, each with a model (`LIMITATIONS.md`, "A
restored session"), besides the three the establishment's invariant takes (`DhPublicValid`, `KemCiphertextLenOf`,
`OptionEqU64Shape`), nine in all:
`ZeroizingVecRoundTrip` (`Zeroizing::new` then `deref` on a byte vector gives it back), `OptionBranchSome`
(`Option::branch` on `Some x` continues with `x`), `VecAsSlice` (`Vec::as_slice` is the slice view), `DhPrivateBytesRoundTrip`
(`PrivateKey::to_bytes`, read out of its wrapper, then `PrivateKey::from_bytes` gives the key back),
`DhPublicBytesRoundTrip` (`PublicKeyBytes::as_bytes` then `from_bytes` gives the key back), and `KemCiphertextLenBound`
(`kem::ciphertext_len` is at most 65536, so the pending ciphertext's length prefix and the size arithmetic of `export` do not
wrap). The first three are about `zeroize`, `core` and `alloc` functions the translation declares without a body, the next
two about `tacenta-core/boundary/src/dh.rs`, the last about `tacenta-core/boundary/src/kem.rs` (1568 bytes, by reading).

**What it does not show.** A restored Braid holding a KEM value, an encoder or a decoder (no relation is claimed there);
any session shape other than the covered one in the round trip (stored skipped keys, another sparse table, an absent
pending message, a present established ephemeral, any other Braid state); that a decoder refuses what it should; the
model's own imported session; initial-type frames, `encrypt`, the responder, and the T3 refinement of establishment. As for
the previous sections, no gate reads these hypotheses: `check-hypothesis-witnesses.sh` routes a section whose heading names a
session lifecycle out.

**Compiler trust and pins.** Every statement that names `Session::export` or `Session::import` lists one compiler-trust
axiom, carried by the `toStr` of a panic message in the generated `export` (Aeneas discharges its length bound
`by decide +native`), not by the argument: `import_ok_gives_invariant`, `RestoredDecryptHypotheses.ofInvariant`,
`export_import_established`, `restored_established_continues`, `restored_established_inhabited`,
`restored_decrypt_hypotheses_jointly_satisfiable`, `export_spec` and `export_import_of_shape` list that one;
`RestoredDecryptHypotheses.refines`, `restored_decrypt_refines` and `restored_established_initiator_decrypt_refines` list it
and the nine `native_decide` constants of `decrypt_ratchet_refines_of_invariant`. These eleven are compiler-trusted. Of the
other 96 results, 68 rest on `propext`, `Classical.choice` and `Quot.sound` alone (`slice_ne_self`,
`model_kemCiphertextLenBound` and 66 of the codec module's), and 28 on those three and between 1 and 51 opaque constants of the
unit, which the types and definitions they mention refer to. Each of the 107 results carries an axiom pin and a statement
pin, and each of the 34 definitions the three modules add a `#print` pin. `check-restored-negatives.py` plants twelve faults in
copies of the three modules and requires Lean to refuse each at a named declaration or pin, with a message that names the
fact removed (an unsolved goal stating it, or the mismatch or pin text), not a failure of the proof script's shape: the
invariant inversion against a copy of `import` with the `Inconsistent` refusal removed, with the proof adapted to that body
(refused in `import_ok_gives_invariant`, the invariant goal unsolved); `headroomCheck` without its sparse-epoch clause, with
the proof adapted (refused in `counterHeadroom_iff_check`, the sparse-epoch goal unsolved); `RestoredScope` widened to a
`KeysSampled` Braid (refused in `sessionRefines_restored`); the round trip concluding a session with its associated data
emptied, and without the `VecAsSlice` law (each refused in `export_import_of_shape`); the classical ratchet encoding with two
counters swapped (refused in `ratchet_to_bytes_spec`); the Braid epoch reader without the hypothesis that the epoch is not
`u64::MAX` (refused in `read_epoch_of`, that goal unsolved); `OptionBranchSomeShape` weakened to let `branch` on `Some x`
break, with the proof adapted to both cases (refused in `lifecycle_take_len_prefixed_of`, the break cases unsolved); the
established shape without the ciphertext bound (refused in `codecShape_parts`); the round-trip half of the joint model at an
interpretation whose public-key reader drops the key (refused in `restored_laws_model_established`); `KemCiphertextLenBoundShape`
without its bound, with the pins kept (refused at its `#print` pin); and the joint model of the composed premise list with
its round-trip half at `Interp.model`, two interpretations, with the pins kept (it compiles, and is refused at the statement
pin of `restored_decrypt_laws_model`).

## Proved (tier T3, session lifecycle: the repeated-initial ephemeral comparison of `Session::decrypt`, and the translated `decode_ec` on every input, on the eight-leaf unit)

Location: `Translation/SessionUnitDecodeEc.lean`, `Translation/UnitLifecycleInitialAgreementT3.lean`.

`Session::decrypt` recognises a repeated initial message by comparing its `ephemeral` with the session's
`established_ephemeral`: `same_ephemeral_agreement` decodes both with `decode_ec`, agrees the session's `ratchet_private` with
each decoded key, and compares the two outputs, `false` when either decode or either agreement fails. The model's
`Model.Lifecycle.sameEphemeralAgreement` now states the same rule, from session-establishment.md, Receiving the initial
message, through the model's `DecodeEC`, `Model.Lifecycle.decodeEc` (33 bytes, the curve type byte, a canonical key, by the
initial-message decoder's own `checkCurve` and `checkKey`). Before the decode was added the model handed the two 33-byte strings to the
agreement without decoding them, and no theorem could relate it to the code (`GAP-REGISTER.md`, row
`E2E-04-SAME-EPHEMERAL-MODEL`). This section was made by its author with tool assistance and has not been read by anyone else.

- `decodeEc_eq_some_iff`, `decodeEc_eq_none_iff`, `decodeEc_length`: `Model.Lifecycle.decodeEc e = some k` exactly when `e` is
  33 bytes long, its first byte is `Model.Messages.ecCurveByte` and `Model.Messages.canonicalKey (e.drop 1)` holds, with
  `k = e.drop 1`; `none` exactly when one of the three fails; a returned key is 32 bytes long. Model facts; the axioms are
  `propext` and `Quot.sound`.
- `session_decode_ec_refines`, `session_decode_ec_characterization`: the translated `tacenta_session::decode_ec` returns on
  every slice, and what it returns, carried across the byte boundary, is `Model.Lifecycle.decodeEc` of the slice's bytes. In
  three arms: `none` exactly when the slice is not 33 bytes long, its first byte is not the curve type byte, or its last 32
  bytes are not a canonical curve public key; otherwise `some k` with `k` those 32 bytes. This adds the rejecting direction to
  `decode_ec_spec` (`Translation/SessionUnitSessionT1.lean`), which says only what a successful decode returns. No hypothesis;
  the three standard axioms.
- `canonicalX25519_session_eq_wire`, `key_eq_drop`, `arrayOf_eq_drop`, `head_sliceOf`, `u8_eq_curve_iff`: the steps of that
  proof: the Session crate's and the wire crate's ports define the same canonicity predicate (so the wire decoder's
  `canonicalKey_bytesOf` applies), the decoder's loop copies the 32 bytes after the curve byte, and the curve-byte test is the
  model's. The three standard axioms or fewer.
- `decode_ec_refines`: the Session unit's `decode_ec`, which wraps the key in the opaque `PublicKeyBytes`, returns on every slice
  a result whose image under the DH view is the model's `decodeEc`. It takes `DhCodecOf` (the byte views of the two opaque key
  types); its axioms add the two DH types and the three codec functions that record names.
- `same_ephemeral_agreement_refines_of_dhAgree`, `same_ephemeral_agreement_refines`: for every private key and every two byte
  strings, the translated `same_ephemeral_agreement` returns `ok` of `Model.Lifecycle.sameEphemeralAgreement` at the private
  key's view and the two strings' bytes. Hypotheses: the agreement clause of the oracle (`OracleOf.dhAgree`, word for word; the
  second form takes `DecryptOracleOf` and reads only that clause) and `DhCodecOf`, both assumed (`LIMITATIONS.md`, "The
  repeated-initial comparison"). No hypothesis is about a branch, a route or the model's verdict. The first lists, beyond the
  three standard axioms, the two DH types, `PrivateKey::agree` and the three codec functions; the second adds the constants
  `DecryptOracleOf`'s other clauses name (`PrivateKey::public_key`, `aead::decrypt`, `rand_core`'s error type).
- `repeated_initial_agreement_refines`, `repeated_initial_agreement_true_iff`, `repeated_initial_agreement_false_iff`: at a session
  and model session related by `SessionRefines`, the comparison of `established_ephemeral` with a decoded message's `ephemeral`
  returns the model's verdict at `model.ratchetPrivate` and the two byte strings `Model.Lifecycle.repeatedInitial` passes; the
  code's verdict is `true` (`false`) exactly when the model's is. These derive what the per-branch premises `hmodelSame`
  (`= true`) and `hagreementMismatch` (`= false`) of `InitialDispatchBranchEvidence`, `SessionDecryptEvidence` and the
  initial-frame branch lemmas of `UnitLifecycleT3.lean` ask the caller for. Those records and lemmas are kept, and no theorem
  takes these results yet. The axiom lists add the opaque KEM and standard-library constants `SessionRefines` names.
- `arrayOf_injective`, `agreement_eq_refines`: the byte view of a translated array is injective, and the translated equality of
  two 32-byte agreement outputs is the model's `==` on their bytes. The three standard axioms or fewer.
- `encoded_comparison_does_not_refine`: a control, not a claim. For every oracle that meets `OracleOf`, given `DhCodecOf`, and
  every two byte strings neither of which is 32 bytes long, some oracle that also meets `OracleOf` makes the comparison the
  model made before the decode was added (`UnitLifecycleIntegrationScreen.encodedEphemeralAgreement`, on the two encodings) disagree
  with the translated one, so no refinement of the shape above holds of it. It says nothing about whether an oracle meeting
  `OracleOf` exists.

What these do not show. That the two hypotheses hold of the real `tacenta_boundary::dh`: they are assumptions about opaque
operations, with models in `UnitOracleModel.lean` and `UnitLifecycleDecryptRatchetScreen.lean` and no proof about X25519. That
`Session::decrypt` refines the model on an initial frame: the composition that would split the repeated-initial route on this
verdict instead of on byte equality is not in the tree, and the dispatch theorems of `UnitLifecycleInitialDispatch.lean` still
take caller-selected branch evidence. On a state the shipped readers accept, both strings decode (the initial-message decoder
checks `ephemeral`, and clause (f) of `Session::invariant` checks `established_ephemeral`), so the decode-refusal arms of the
comparison are reached only on other states; this is read from the code and not proved here. No proof chooses a width of
`usize`, and none lists a compiler-trust axiom. Each of the 19 theorems has an axiom pin and a statement pin, and the bodies of
`Model.Lifecycle.decodeEc` and `Model.Lifecycle.sameEphemeralAgreement` have `#print` pins, so a model that compared the
encodings again fails the build at the pin; `attest.py` requires them all. `check-initial-dispatch-negatives.py` restates the
refinement of a model comparison that leaves the incoming string undecoded, the established one undecoded, or agrees on the two
encodings, and each is refused because the existing proof script fails inside its body (in each case at its first rewrite by
a model decode); that shows the script reads each decode, not that the restated statement is unprovable. For the third,
`encoded_comparison_does_not_refine` shows the statement false at some oracle meeting `OracleOf`, if some oracle meeting
`OracleOf` exists; for the two one-sided restatements nothing shows the statement false. Nothing in this section is a claim
that `Session::decrypt` refines the model on an initial frame.

## Proved (tier T3, session lifecycle: the public `decrypt` on frames that are not initial messages, on the eight-leaf unit)

Location: `Translation/UnitLifecycleDecryptT3.lean`.

This is the first result here whose subject is the generated public `Session::decrypt` with the inner step discharged by
a proof rather than taken as a hypothesis. It covers only frames that are not initial messages, and it is conditional on
the hypotheses of `decrypt_ratchet_refines_complete` (listed in the first item below) and on
one scope premise. It says nothing
about an initial message, so `Session::decrypt` is still not proved end to end.

- `decrypt_refines_ratchet_frame`, `decrypt_refines_ratchet_frame_statement`: the statement
  `DecryptRefinesRatchetFrameStatement`. Under the hypotheses of `decrypt_ratchet_refines_complete`, exactly
  (`DecryptOracleOf`, `DhCodecOf`, `DecryptRatchetContracts`, the class `DerivedKeysModel`, `DecryptRatchetAgreements` at
  `oracle.braidKem`, `SessionRefines`, `DecryptRatchetHeadroom`, the trace equation and `DecryptRatchetRun`), and the
  scope premise `hframe`, that the model's reading of the message is not an initial message, the generated
  `lifecycle.Session.decrypt` returns some output and `StepRefines` holds between that output and
  `Model.Lifecycle.decrypt`: the result (a success's plaintext, or a refusal whose public mapping is the model's), the
  session it leaves (with `pending_initial` cleared exactly on a success, as the model clears it) and the remaining
  trace. The frames `hframe` admits are a ratchet message, a message of fewer than two bytes, one with another
  version byte and one with an unknown type byte; on each the model's dispatch passes the message through unchanged. The
  paths are those of the complete `decrypt_ratchet` refinement, reached through the public root. `hframe` is decidable from the message alone
  and selects no branch: the proof derives the generated message type from it (`message_type_refines`). The proof joins
  `UnitLifecycleT3.decrypt_passthrough_refines`, whose inner step is a hypothesis, with
  `decrypt_ratchet_refines_complete`, which proves that step: the Braid KEM model is `oracle.braidKem`, the generated
  type and its equation come from `message_type_refines`, and the inner output is the one the complete theorem gives.
  Its boundary records are the restated ones described in the sections above: the three zeroize fields of the contract record
  are stated at the instances the unit passes to `Array::zeroize` and `Vec::zeroize`, with the real functions' returning
  there assumed, and `DecryptRatchetAgreements` holds the two laws about `Vec::pop` and `Option::as_mut` from which the
  inner proof derives the sparse store's two agreements. The text of the statement is unchanged; what these records
  say changed under it. They are assumed, not shown true of the crate.
- `decrypt_refines_ratchet_frame_of_invariant`: the same, with `DecryptRatchetHeadroom` replaced by
  `Session::invariant` returning `true`, which gives the headroom through two fields of the contract record
  (`decryptHeadroom_of_invariant`). `Session::import` refuses a session that fails that check (read from the source),
  but no theorem connects `import`'s output to this result, and applying it to an imported session would carry every
  field of the contract records, including the one the restore row tracks.
- `decrypt_refines_ratchet_frame_of_counter_headroom`: the same again, with `DecryptRatchetRun` also replaced, by
  `CounterHeadroom` and `DecryptRatchetRunInputs` of the section on the per-run receive bounds (the run's receive bounds derived from
  `Session::invariant`, through `decryptRatchetRun_of_invariant`). Its hypotheses are those of
  `decrypt_ratchet_refines_of_invariant` and `hframe`. `CounterHeadroom` is assumed per run, and each of its four ceilings
  excludes states `Session::invariant` accepts and a long session reaches.
- `decrypt_frame_hypotheses_jointly_satisfiable`: under the laws `DecryptJointLaws K dh`, every hypothesis of
  `decrypt_refines_ratchet_frame_of_counter_headroom`, the boundary records included, holds together at the witness of
  `decrypt_of_invariant_hypotheses_jointly_satisfiable`, for every codeword view; its message is a ratchet frame, so it
  meets `hframe`. The laws are assumed, with the models of that section, and the witness keeps that section's limits: the
  state is built for the hypotheses, carries no agreement chunk, and its model step refuses at the first agreement if the real
  agreement refuses the all-zero key, which, by reading the X25519 boundary, it does. Its conclusion is the record
  `DecryptOfInvariantHypotheses` of the section on the per-run receive bounds, with `hframe`; the next result ties that record to the corollary.
- `decrypt_refines_ratchet_frame_of_hypotheses`: from `DecryptOfInvariantHypotheses` and `hframe`,
  `decrypt_refines_ratchet_frame_of_counter_headroom` applies, so the generated `lifecycle.Session.decrypt` returns and
  `StepRefines` holds against `Model.Lifecycle.decrypt`. The record with `hframe` is the corollary's hypothesis set by
  this theorem, not by reading: a hypothesis added to the corollary that the record does not supply breaks its proof.
- `decrypt_frame_at_invReal`: the two composed. Under `DecryptJointLaws K dh`, at the witness of
  `decrypt_frame_hypotheses_jointly_satisfiable`, for every codeword view, the generated public `decrypt` returns and its
  output refines the model's step. The laws are assumed; the limits of that witness stay (built for the hypotheses, no
  agreement chunk, a model step that refuses at the first agreement if the real agreement refuses the all-zero key).
- `refReal_fails_invariant`, `succMessage_not_initial`, `decrypt_refines_ratchet_frame_at_refusal`: the theorem at the run
  of the complete refinement's screen (`UnitLifecycleDecryptRatchetCompleteScreen`) whose model step is the Triple refusal `outOfOrder`. That state fails
  `Session::invariant` (its associated data is empty, and a state that passes holds 66 bytes there, under `DhCodecTotal`),
  so this run shows the hypotheses consistent, not met by a state the crate admits.
- `sampleMessage_not_initial`, `inv_sessionRefines`, `inv_retryRunBounds`, `inv_run_satisfiable`, `inv_model_refuses`,
  `decrypt_refines_ratchet_frame_of_invariant_at_sample`, `decrypt_refines_ratchet_frame_of_invariant_exists`: the earlier
  screen's first run, rebased on the session of `sessionOf_invariant` (`UnitLifecycleDecryptT3.invReal`: fresh Triple and Braid states, the
  ratchet key's own public bytes, the associated data `identity_ad` computes, and as the identity key on both sides the
  public key of that same ratchet key, so the session's peer is itself; it is the same state as
  `UnitLifecycleDecryptScreen.invReal`, the session of the joint witness above, with the last two arguments swapped, and
  unifying the two definitions is a follow-up). That session passes `Session::invariant` under the two
  assumptions `sessionOf_invariant` takes, `ValidKeyShape` (a canonical prime-order key) and `OptionEqU64Shape`
  (`LIMITATIONS.md`, "The headroom records"); `SessionRefines`, the trace equation and the five fields of
  `DecryptRatchetRun` hold there, for each Braid KEM model, view and oracle with the source's draws; and the `Session::invariant` corollary applies at it. The boundary records are
  arguments of the last result and are not discharged at the run. With the toy oracle of the earlier screen the model's
  step there refuses at the first agreement (`inv_model_refuses`), as the first run's does.
  `decrypt_refines_ratchet_frame_of_invariant_exists` states this as one existential: under `ValidKeyShape` at the real
  constants, `OptionEqU64Shape` and the boundary records, some session passes `Session::invariant`, holds no pending
  initial message and no established ephemeral key, and has an output of the generated `decrypt` related to the model's
  step at the sample message. The state is built for the
  hypotheses: it has no pending initial message, no receiving chain and no established ephemeral key, while an initiator's
  session holds a pending initial message from establishment until its first successful decrypt (read from the source), and it is not shown to be produced by
  `establish_initiator_for` or `establish_responder`; its message carries no agreement chunk.
- `pendReal_fails_invariant`, `decrypt_refines_ratchet_frame_at_pending_success`, `pend_model_clears`,
  `generated_clears_at_pending_success`: the one run here that reaches the effect the join adds over the complete
  theorem, clearing `pending_initial` on a success. Its state (`pendReal`) is the earlier screen's success run with a
  pending initial message added. The theorem applies there with the boundary records as arguments. With the earlier
  screen's toy oracle (`oracleDecrypt`: the identity public key, an agreement that returns the private key and refuses the all-zero
  public key, an AEAD open that returns the empty plaintext and refuses the empty ciphertext), the model's step succeeds and clears the pending initial message the input holds
  (`pend_model_clears`); under the boundary records at that oracle, which are not discharged here, the generated
  `decrypt` succeeds and returns a session with no pending initial message (`generated_clears_at_pending_success`). This
  is the generated side of the run, conditional on those records, which hold together at that oracle only in the toy
  interpretation `decrypt_boundary_has_a_model` gives (at exactly `oracleDecrypt (byteTrace sampleRng)` and `toyKem`) and
  are not true of the real primitives (an agreement that returns the private key is not X25519); the run says nothing
  about the shipped functions. The state
  fails `Session::invariant` (empty associated data), so it shows the hypotheses consistent at a success, not met by a
  state the crate admits.

**What is not shown.** Any initial message: the repeated-initial branch is outside `hframe`; the model's comparison on
that branch is now refined by the translated one (previous section), but the composition that splits the route on it is
not proved. That any state the shipped code produces meets the
per-run hypotheses: no witness here is such a state, and the one witness that passes `Session::invariant` does so only
under the two assumptions above, at a state the shipped code is not shown to reach. A run carrying an agreement chunk: no
witness here carries one, so the chunk fields of `DecryptRatchetRun` are met by their vacuous arm. The random source is read
as a function of its state; for a source with no state of its own, such as `OsRng`, the hypotheses cannot all hold, and
the theorem makes no claim about such a call. Which branch the shipped code takes at any of the runs with the real
primitives; the one success here is reached with a toy oracle at a state that fails `Session::invariant`. The theorem quantifies over the oracle; `DecryptOracleOf` binds its four clauses, `DecryptRatchetAgreements`
its KEM model and the trace equation its draws. The model lemma `decrypt_oracle_frame` (`tacenta-model/Model/LifecycleFrame.lean`)
shows that `Model.Lifecycle.decrypt` reads only the oracle's `draws`, `braidKem`, `dhPublic`, `dhAgree` and `aeadOpen`; no
theorem here applies it. The hypotheses keep the limits of the complete `decrypt_ratchet` refinement: the agreement chunk must be consistent, the two laws
`DecryptRatchetAgreements` holds in place of the sparse store's two agreements (row `SESSION-SPARSE-AGREEMENTS`) are
assumed, and the three restated zeroize fields assume that the real functions return at the unit's instances
(`LIMITATIONS.md`, the section on the public `decrypt`).

No gate reads these hypotheses. This section's heading names a session lifecycle, so `check-hypothesis-witnesses.sh`
routes its theorems out, as for the other session-lifecycle sections; what shows them satisfiable is the screen results above, in
the senses stated.

**Compiler trust and pins.** `decrypt_refines_ratchet_frame`, `decrypt_refines_ratchet_frame_statement`,
`decrypt_refines_ratchet_frame_at_refusal`, `decrypt_refines_ratchet_frame_at_pending_success` and
`generated_clears_at_pending_success` have exactly the axioms of `decrypt_ratchet_refines_complete`, 61, including its
nine `native_decide` constants; the generated `decrypt` and `message_type` add none.
`decrypt_refines_ratchet_frame_of_invariant`, `decrypt_refines_ratchet_frame_of_counter_headroom`,
`decrypt_refines_ratchet_frame_of_hypotheses` and `decrypt_refines_ratchet_frame_of_invariant_at_sample` add three opaque
operations that `Session::invariant` mentions (`is_prime_order_public`, `kem::ciphertext_len` and `Option::eq`), 64 in all;
`decrypt_refines_ratchet_frame_of_invariant_exists` and `decrypt_frame_at_invReal` add five more that the real
interpretation names (`aead::encrypt`, `kem::KeyPair`, `kem::encapsulate`, `kem::decapsulate` and `xeddsa::verify`), 69 in
all; each has the same nine. These eleven are compiler-trusted; the class is expected to change as for the complete `decrypt_ratchet`
refinement. Of the other ten, `succMessage_not_initial` and `sampleMessage_not_initial` are kernel-only, seven rest on
between 4 and 22 of the Session unit's opaque-operation axioms, and `decrypt_frame_hypotheses_jointly_satisfiable` on 52
(55 in all), those the laws and the witness name. Each result carries an axiom pin and a statement pin, and
`DecryptRefinesRatchetFrameStatement`, `UnitLifecycleDecryptT3.invReal` and `pendReal` carry `#print` pins; `attest.py` requires them.
`check-decrypt-ratchet-negatives.py` holds the join against nine planted faults: five in a renamed copy of the generated
`decrypt` compiled with copies of `decrypt_passthrough_step_refines`, `decrypt_passthrough_refines` and the join (a
success that keeps `pending_initial`, a refusal that clears it, a `none` arm that refuses without calling
`decrypt_ratchet`, a refusal that returns the input random source, an inner call given the message without its first
byte), each refused in the copied step lemma; and four on a copy of the module (the target replaced by
`Model.Lifecycle.decryptRatchet`, `hframe` deleted with its one use left open, and `decrypt_ratchet_refines_complete`
replaced by the first form `decrypt_ratchet_refines`, each refused in the join; and, with the pins kept, the recorded
statement without its `draws` conjunct, refused at its pin). No planted fault covers the four results added with the run
bounds derived (`decrypt_refines_ratchet_frame_of_counter_headroom`, `decrypt_frame_hypotheses_jointly_satisfiable`,
`decrypt_refines_ratchet_frame_of_hypotheses`, `decrypt_frame_at_invReal`); each is a short composition held by its
axiom and statement pins.

## Proved (the hypotheses the session contract integration adds: which are empty, which have a model)

Location: `Translation/UnitLifecycleIntegrationScreen.lean`.

The integration of the session contract branch changed the oracle record `OracleOf` (a KEM success clause that holds only where
the model's `kemEncaps` returns `some`, a pre-draw refusal clause `kemInvalidKey`, two draws for signing) and added evidence
records to the dispatch layer. These results decide some of them. They are about hypotheses, not about the product.

- `concreteBranchEvidence_empty`, `endToEndEvidence_empty`, `agreementEndToEndEvidence_empty`: refutations of the form the
  session contract branch introduced. The form the dispatch layer had before the integration (a `ceiling` field in place of
  `randomDraw`) differs and is not decided here.
  The field `randomDraw` of `InitialRatchetConcreteBranchEvidence` asks that every RNG state, not only the run's, has a trace with
  a head once one inner message decodes to a composite whose first agreement succeeds. With `OracleOf.random32`, which turns a
  state whose trace has a head into a state whose trace is the tail, the trace of every state would be longer than every number,
  so the record has no term, given `OracleOf`, one such message and one RNG state, and the two old end-to-end records that
  contain it are empty under the same premises. The proof uses no law. No theorem takes these three records now: the dispatch
  theorems and the two accepted constructors of `SessionDecryptEvidence` take `InitialRatchetConcreteBranchEvidenceRun` and the
  two `...EndToEndEvidenceRun` records, whose fields are asked of the run's own inner message and RNG state (below).
- `byte_random32`: at `byteRng`, a random source that reads a list of bytes from the front, with `byteTrace` reading it as 32-byte
  draws, the translated `random_secret` meets the `random32` clause.
- `random32Clause_of_oracleOf`, `sigSignClause_of_oracleOf`, `kemClauses_of_oracleOf`: `Random32Clause`, `SigSignClause` and
  `KemClauses` are the fields of `OracleOf` with the shipped function replaced by an argument, so the results below speak about
  those fields.
- `sigSignClause_of_law`, `kemClauses_of_law`: for a signing function that fills one 64-byte buffer and touches the RNG nowhere
  else, the two-draw `sigSign` clause holds at the byte-stream source, for the oracle whose signing function the law determines;
  for an encapsulation function that refuses a key a predicate rejects before it reads the RNG and otherwise fills one 32-byte
  buffer, the three KEM clauses hold, for the oracle whose `kemValid` is that predicate.
- `changed_rng_clauses_have_a_model`: there are a signing function, a key-generation function and an encapsulation function that
  meet the three laws (`SignFillsOnce64Of`, `GenerateFillsOnce64Of`, `KemShapeOf`), and an oracle whose KEM refuses the empty key,
  such that `random32`, `sigSign` and the three KEM clauses hold together at the byte-stream source. So the changed clauses are
  not met only by an oracle that never refuses, and a byte-stream source meets the two-draw signing clause. They are also met by
  an oracle whose `kemEncaps` never returns `some`, because the success clause binds the code only where the model predicts a
  success, so `OracleOf` does not tie the model's encapsulation to the code on a key the code accepts. The pinned statement does
  not show a KEM that ever succeeds.
- `changed_rng_clauses_of_laws`: the same derivation at the shipped constants. Under `SignFillsOnce64` and `KemShape`, the laws
  stated of `xeddsa::sign` and `kem::encapsulate`, there is an oracle for which the changed clauses and `random32` hold at the
  byte-stream source. The two laws are assumptions read from `tacenta-core/boundary/src/xeddsa.rs` and
  `tacenta-core/boundary/src/kem.rs`; no theorem proves them of the opaque constants, and
  `tacenta-core/tests/rng_fill_counts.rs` tests them on the shipped source.
- `braid_send_keysUnsampled_generate`, `braidSendTrace_conflicts_with_sigSign`: a translated Braid send from `KeysUnsampled`
  returns the RNG state that key generation returned. A refutation of the form the session contract branch introduced (the
  dispatch layer had no such record before it): `BraidSendTraceAgreement` lets such a send
  consume one trace entry, and `OracleOf.sigSign` lets a signature consume two. Under `SignFillsOnce64` and `GenerateFillsOnce64`
  (each function fills one 64-byte buffer; the second is read from `IncrementalKeyPair::generate`, `tacenta-core/kem/src/lib.rs`,
  whose seed is 64 bytes), both are one 64-byte fill from the same state, so the old agreement contradicts `OracleOf.sigSign` at
  any send from `KeysUnsampled` whose trace has two entries. No theorem takes that agreement now: the model's `sendAgreement`
  takes two draws in that state, and `public_session_encrypt_of_send_contracts` takes `BraidSendTraceAgreementCounted`. The
  model change corrects the model against `mlkem-braid.md`, which already said that key generation draws 64 bytes:
  `sendAgreement` read one 32-byte draw at `KeysUnsampled` from #161 until this integration, and the tags
  `tacenta-assurance-v0.4.2` to `tacenta-assurance-v0.4.5` contain that one-draw model. No claimed theorem took it.
- `concreteBranchEvidenceRun_of_run_parts`, `runRandomDraw_byte`: the first is the record's constructor. It packages given parts
  into the run's evidence record (one scoped Braid record for the inner message the run's initial message decodes to, the Triple
  and AEAD branch contracts of the run's refusal inputs, and a draw at the run's RNG state), so the record holds exactly when its
  four parts do, and each part names only the run's inner message and RNG state. Because this module builds the record from
  those parts, a field added to the record that the parts do not give fails the build. The second restates that a byte-stream
  state with a draw left has one, together with `byte_random32`: the draw part asks only that the run's state has a draw, which
  `random32` does not contradict. Neither shows that any part can be supplied. The two chunk fields of the scoped Braid record
  are met exactly when the run is consistent (`scoped_chunk_fields_iff_consistent`); the record's other fields
  (`BraidReceiveContracts`, the Braid agreement laws and the epoch bound) are not decided here. Its Braid field, and the success
  provider of its result field, can be met for a consistent run and not for a run whose chunk is inconsistent, whether the run is
  refused or accepted, which the theorems that take it therefore do not cover. That the Triple and AEAD branch contracts of a run
  can be supplied is not shown here.
- `braid_send_keysUnsampled_byte_trace`, `braidSendTraceCounted_with_sigSign_byte`: at the byte-stream source, under
  `GenerateFillsOnce64`, a translated Braid send from `KeysUnsampled` leaves the trace without its first two entries; with
  `SignFillsOnce64` as well, the draw clause of `BraidSendTraceAgreementCounted` and the two-draw signing clause hold together at
  such a send with two draws left. The result restates the draw clause and does not name `BraidSendTraceAgreementCounted`, and
  no theorem constructs the record; its body carries a `#print` pin (below), so a stronger record, an empty one included, fails
  the build at that pin. Its other clauses (the refinement of the model send by the generated result, and the `headerReceived`
  draw, a 32-byte `encapsulate1` fill by reading) are not decided here.
- `retryReceiveBounds_initAlice`, `retryReceiveBounds_not_trivial`, `generatedTripleRefusalConditions_initAlice`,
  `generatedTripleSuccessConditions_initAlice`: `RetryReceiveBounds` and the two finite-store condition records hold at the
  initiator's initial Triple state, `Model.Triple.initAlice` (the responder's, `Model.Triple.initBob`, is not decided), the last two given the class `SessionUnitT1.DerivedKeysModel` that the axiom base provides, and
  the first fails at a sparse epoch of `u64::MAX`. That they hold at the states the retry loop reaches is not shown here.
- `oracleOf_dhAgree_off_view`, `encodedEphemeralAgreement_unconstrained`, `sameEphemeralAgreement_of_view_agree`: given the
  DH codec, `OracleOf` still holds when the oracle's `dhAgree` is changed at second arguments that are not 32 bytes long. So the
  comparison the model made before it decoded the two ephemerals, kept word for word as `encodedEphemeralAgreement`, can be made
  either value on two strings that are not 32 bytes long by an oracle that meets `OracleOf`. The corrected
  `Model.Lifecycle.sameEphemeralAgreement` decodes both first, and two oracles that agree at every 32-byte argument give it the
  same verdict on every pair of strings, so that change cannot move it. Its refinement by the code is in the section on the
  repeated-initial comparison above (`GAP-REGISTER.md`, row `E2E-04-SAME-EPHEMERAL-MODEL`).

What these do not show: that `OracleOf` as a whole is satisfiable (its `dh`, `aead`, `kemDecapsulate`, `sigVerify` and
`identityValid` clauses are not decided here; the next section decides them); that the shipped functions meet the three laws; that any dispatch theorem is
non-vacuous. No proof here chooses a width of `usize`; the one fact used, that `Usize.max` is at least `2^32 - 1`, is proved for
both widths by `small_le_usize_max`. None depends on a compiler-trust axiom. Each result carries an axiom pin and a statement
pin, and the definitions of the three clauses and the three laws, with the laws at the shipped constants (`SignFillsOnce64`,
`GenerateFillsOnce64`, `KemShape`), carry `#print` pins, as do the model's `braidSendDrawCount`, `braidSendNeedsDraw`,
`takeDraw`, `braidRandomness` and `sendAgreement` (and `takeDraws`, whose body is pinned through its equation
`takeDraws.eq_def`, because `#print` shows a structurally recursive definition only in compiled form), so a change to the draw
count, or to how the drawn bytes become the Braid's randomness, fails the translation build (the model package builds without
the pin). The bodies of the five records the dispatch layer takes and no theorem here constructs (`OracleOf`,
`BraidSendTraceAgreementCounted`, `InitialRatchetTripleBranchContracts`, `InitialRatchetAeadBranchContracts`,
`InitialRatchetBraidEvidenceContractsScoped`) carry `#print` pins too, so a field added to, removed from or changed in one of
them fails the build. The pins hold the text of each record, in which every definition it mentions appears by name, so a change
to the body of one of those definitions changes no record pin. A proof that uses the definition still notices (strengthening
`EncodersLive` fails `BraidT3.lean`), and the other definitions the records name are held by the proofs that use them, not by a
pin; `verified`, which only the `sigVerify` clause of `OracleOf` mentions and no proof uses, has its own `#print` pin, without
which a change to it passed the build and every gate. These are text pins: they hold what the records say, not that they can be
met. `attest.py` requires all of them (`REQUIRED_PINS`, `REQUIRED_STATEMENT_PINS`) and requires the `#print` form for the 89
definition pins (`REQUIRED_PRINT_FORM`), because `#check @name` holds the type of a definition and not its body; `takeDraws`
is held by its equation pin and may take either form. `check-attest-negatives.sh` deletes each axiom pin, and each of the model
and record definition pins, in turn, and plants the `#check` form for eight of them. In the model package, examples in
`Model/Lifecycle.lean` hold `braidSendDrawCount` to `mlkem-braid.md` at one state of each of the twelve kinds and check the draws
an initiator's establishment and first send consume; they fail if the count at `keysUnsampled` returns to one. They are
anonymous, so no gate requires them; the pin on `braidSendDrawCount` is the part that is required.

## Proved (the clauses of `OracleOf` decided jointly: inhabited under named laws, with a model)

Location: `Translation/UnitOracleShape.lean`, `Translation/UnitOracleModel.lean`, `Translation/UnitOracleDh.lean`,
`Translation/UnitOracleAead.lean`, `Translation/UnitOracleKemSig.lean`, `Translation/UnitOracleJoint.lean`.

The screen above decides five clauses of `OracleOf` under laws and leaves seven undecided (`dhPublic`, `dhAgree`,
`identityValid`, `aeadSeal`, `aeadOpen`, `kemDecapsulate`, `sigVerify`). These results decide the seven, and `OracleOf` as a
whole. None of the seven is refuted, and each is satisfiable as stated. The KEM success clause, which the screen showed too
weak, has a guarded companion here, `OracleOfGuarded`, and `OracleOf` still leaves `dhAgree` free off 32-byte arguments
(`E2E-04-SAME-EPHEMERAL-MODEL`). `OracleOf` and every pinned statement of the tree are unchanged. The oracle that inhabits
the record is the code read through the byte views (`oracleOfLaws`): each primitive's verdict is the code's answer on
arguments with those bytes. So `OracleOf` asks of the code only that each primitive returns, that its result depends only on
the bytes of its arguments, and that it reads the random source in the stated order. It ties the dispatch theorems to the
code's own primitives and to no specification of X25519, the AEAD, ML-KEM or XEdDSA. These results are about a hypothesis
of the dispatch theorems, not about the product. The `decrypt_ratchet` section above shows `DhCodecOf` and the four clauses `decrypt_ratchet` uses satisfiable in a
separate interpretation, with a fixed toy oracle (`decrypt_boundary_has_a_model`); this section decides all twelve clauses
together, with the oracle read off the code, and does not repeat that result. Its writer and tool-assisted readers working for the maintainer have read it; no reviewer
independent of the maintainer has.

- `isValidIdentityKey_is`, `oracleOf_iff_shape`, `oracleOfShape_iff_clauses`, `dhCodecOf_iff_shape`,
  `generateFillsOnce64_iff_shape`: `OracleOfShape` is `OracleOf` with each opaque constant replaced by a field of an
  interpretation `InterpO`, which is the joint interpretation of `UnitSatisfiabilityJoint.lean` and one more field for
  `xeddsa::sign`, the one opaque constant `OracleOf` reaches that the joint interpretation leaves out. The first binds the
  translated `is_valid_identity_key` to its body over an interpretation by `rfl`. The second binds the shape to `OracleOf`
  at the real constants by repacking each of the twelve fields, which the kernel accepts only if the two field types
  unfold to the same proposition. The third cuts the shape into one named clause per field (the three KEM fields are the
  screen's `KemClauses`). The last two bind `DhCodecOf` and the key-generation law the same way.
- `liftView_spec`: a function that returns on every input of a type whose view is injective determines a function on views
  that agrees with it at every view. `oracleOfLaws` builds an oracle this way from an interpretation, with the KEM and
  signing functions that the screen's two laws name.
- `dhPublicClause_of_laws`, `dhAgreeClause_of_laws`, `identityValidClause_of_laws`, `aeadSealClause_of_laws`,
  `aeadOpenClause_of_laws`, `kemDecapsulateClause_of_laws`, `sigVerifyClause_of_laws`: for every interpretation, each of
  the seven clauses holds for that oracle, given that its primitive returns (the totality field of the contract records
  that says so: `DhCodecTotal`, `DhAgreeTotal`, `DhIdentityTotal`, `AeadSealBounded`, `AeadOpenTotal`,
  `KemDecapsulateTotal`, `XeddsaVerifyTotal`) and, for the DH, decapsulation and verification clauses, that the byte views
  of their opaque argument types are injective (`DhViewInjective`, `KemViewInjective`). The identity clause also uses
  `is_canonical_x25519_spec`, which shows that the translated canonical-encoding test returns.
- `modelO_axiomBase`, `modelO_laws`: `InterpO.model`, the joint interpretation with 32-byte DH and KEM key types and toy
  primitives that refuse some inputs, satisfies the axiom base of the four contract records (`AxiomBase`, with the
  byte-stream source), the DH codec, both view laws and the screen's three random-source laws, together.
- `dh_clauses_in_model`, `aead_clauses_in_model`: there the DH and AEAD clauses hold for `oracleM`, the oracle
  `oracleOfLaws` gives, and it is not degenerate in this sense: it refuses and accepts inputs of each primitive that can
  refuse. Its public key is the model's. Agreement gives the two sides of an exchange the same answer, refuses a key
  paired with itself and accepts another pair. The identity test refuses the zero key and accepts another. It opens what
  it seals, for a plaintext shorter than `usize::MAX`, and refuses the empty ciphertext. Its AEAD ignores the keys, the
  nonce and the associated data, and the inputs it refuses are not the ones the real primitives refuse: the real agreement
  refuses a low-order peer key and agrees a key with its own public key, and the model's witnesses `zero32` and `one32` are
  low-order points that the real agreement and identity test both refuse.
- `oracleOfGuarded_iff_shape`, `kemGuardedClause_of_law`, `kemClauses_of_guarded`: `OracleOfGuarded` is `OracleOf` with one
  more field, `KemGuardedClause` at the shipped `encapsulate`: whenever the oracle accepts the key and the trace has a
  draw, the code encapsulates, consumes that draw and returns what `kemEncaps` names. The guarded clause follows from the
  screen's `KemShapeOf` at the byte-stream source, for the oracle whose `kemValid` and `kemEncaps` the law determines
  (`kemGuardedClause_of_law`); the record as a whole needs all eleven laws (`oracleOfGuarded_of_laws`). With `OracleOf`'s
  two refusal clauses the guarded clause gives `OracleOf`'s conditional success clause, so the new record is stronger than
  the old.
- `never_encapsulating_meets_kemClauses`, `never_encapsulating_fails_guarded`, `guarded_separates_never_encapsulating`: an
  oracle whose `kemEncaps` never returns `some` meets `OracleOf`'s three KEM clauses at any encapsulation that meets the
  screen's law, when its validity verdict is the law's, and fails the guarded clause once it accepts one key at a state
  with a draw; at the model's encapsulation one oracle does both.
- `kem_sig_clauses_in_model`: at the joint interpretation the decapsulation and verification clauses and the guarded
  clause hold for `oracleM`. Its KEM accepts a 1568-byte key and refuses the empty one, and `kemEncaps` returns `some` at
  the accepted key for every draw, so by the guarded clause the code encapsulates there at every state with a draw. It
  decapsulates what it encapsulates from a 32-byte draw and refuses the empty ciphertext. Verification accepts the
  oracle's signature from two 32-byte draws under the oracle's public key of the signing secret, and refuses an all-zero
  signature under another key. Its encapsulation reads only the length of the key, its 32-byte ciphertext is the draw
  (an ML-KEM-1024 ciphertext is 1568 bytes), its decapsulation ignores the key pair, and its signature and verification
  ignore the message.
- `oracleLaws_real_iff`, `oracleOfShape_of_oracleLaws`: `OracleLaws` collects eleven laws under which `OracleOf` holds,
  sufficient and not shown necessary (some, such as the totality of `PrivateKey::to_bytes` inside `DhCodecTotal`, are
  stronger than any clause requires). At the real constants they are the seven totality fields above, the screen's
  `SignFillsOnce64` and `KemShape`, and the two view laws. Over every interpretation they give one oracle for which the
  twelve clauses and the guarded clause hold at the byte-stream source.
- `oracleOfGuarded_of_laws`, `oracleOf_of_laws`: at the real constants, under those laws, for any DH and KEM views whose
  maps are injective, `OracleOfGuarded`, and so `OracleOf` as it is stated, is inhabited at the byte-stream source.
- `oracleLaws_hold_jointly`, `oracleOf_joint_model`, `oracleOf_inhabited_jointly`: one interpretation meets the eleven
  laws, the axiom base of the four records, the DH codec and the screen's key-generation law together, and there the
  twelve clauses and the guarded clause hold for one oracle that refuses an input of each primitive that can refuse and
  whose KEM encapsulates at an accepted key. The last is the existential form.

What these do not show. Over injective views, the twelve clauses of `OracleOf` say that each primitive returns and that the
view of its result depends only on the views of its arguments, together with the draw laws for the random source. The
oracle that `oracleOf_of_laws` supplies is read off the shipped primitives through those views (`oracleOfLaws`,
`liftView`), so the clauses hold of it by construction; the inhabitation shows that the record is consistent with the
totality assumptions and the two view laws, and shows nothing about what the oracle computes. That the real primitives meet
any law: seven are totality fields the records already assume, and they hold of the real functions only on the inputs a
Rust program can supply and memory allows (`LIMITATIONS.md`); `SignFillsOnce64` and `KemShape` are read from the source and
tested by `tacenta-core/tests/rng_fill_counts.rs`, which counts the random source's calls, and not proved; and the two view
laws are about the views a caller chooses. By reading, each real type has an injective view (its wrapped bytes), which also
meets `DhCodecOf`; a result applies to a caller's view only if that view is injective, and Lean cannot show that an
injective view of an opaque type exists. The inhabitation is in the sense of the substitution argument (`LIMITATIONS.md`,
"The four contract records follow from an axiom base that has a model, under five laws"): `oracleOf_of_laws` holds for
every assignment of the opaque constants and the laws hold in one; that a derivation of `False` from them at the real
constants would become one in the model is an argument about derivations, not a theorem inside Lean. Only the byte-stream
source is covered: `OracleOf` reads the RNG through a trace, and no result here concerns another source. No consumer takes
`OracleOfGuarded`; the dispatch theorems take `OracleOf`, and their other records (the per-run evidence, the counted Braid
agreement) are not decided here, so no dispatch theorem is shown non-vacuous by these results alone. None depends on a
compiler-trust axiom: the generic and model results list the three standard axioms, most of them with
`rand_core_1.error.Error` (`liftView_spec`, `kemClauses_of_guarded` and `never_encapsulating_fails_guarded` list the three
alone), and the
bridges and the results at the real constants also list the opaque constants they mention. No proof chooses a width of
`usize` (`oracleOf_joint_model` records `Usize.bounds_eq`), so each holds at both widths. Each has an axiom pin and a
statement pin. The ten clause and law definitions, `oracleOfLaws`, `KemGuardedClause`, `OracleOfGuarded`, `OracleLaws`,
`InterpO.model` and `oracleM` have `#print` pins (sixteen in all), and so do the seven totality predicates of the records,
their seven shapes over an interpretation and the two abbreviations they print through, `NoPanic` and `Np` (sixteen more,
in `UnitOracleJoint.lean`), so a change to a law's text, such as the 48 bytes of `AeadSealBounded`, fails the build at a
pin. `attest.py` requires them all (`REQUIRED_PINS`, `REQUIRED_STATEMENT_PINS`, `REQUIRED_PRINT_FORM`); only
`REQUIRED_STATEMENT_PINS` is recorded in the verification manifest, and the other two lists can be shortened by editing
`attest.py` alone. `attest.py` does not read what a pin says, so a statement weakened together with its pin's expected
message is accepted by it; only the build, which compares the text, and the diff show it. A pin holds the printed
statement, in which a definition appears by name, so a change to the body of `OracleOfShape`, `InterpO`,
`isValidIdentityKeyOf`, `liftView` or one of the model's toy primitives changes no pin; the bridges and the model theorems
are what hold those. `check-session-satisfiability-negatives.sh` removes each witness in turn, changes nine primitives and
the private-key view of the model one at a time (agreement, the prime-order test, seal, open, encapsulation,
decapsulation, verification, signing and key generation), each refused by the result, the lemma or the law of the model
that needs it, and changes one field of a bridge or a record; the model's `to_bytes` of a private key and equality of
public keys are not held, and no clause of `OracleOf` uses them.

## Proved (`DecryptOracleOf` from four laws, and the oracle fields the model's `decrypt` reads)

Location: `Translation/UnitOracleDecrypt.lean`, `tacenta-model/Model/LifecycleFrame.lean`.

`DecryptOracleOf` (`UnitLifecycleDecryptRatchetT3.lean`) is the part of `OracleOf` that `decrypt_ratchet_refines` and
`decrypt_ratchet_refines_complete` take: the `dhPublic`, `dhAgree`, `aeadOpen` and `random32` clauses. Before these results
the only route from laws to it was `oracleOf_of_laws` and `DecryptOracleOf.of_oracleOf`, which takes all eleven laws of the
section above, because `OracleOf` also has the identity, seal, KEM and signing clauses the other laws serve. These results
show that four of the laws suffice for the record (they are not shown necessary: of `DhCodecTotal` the proof uses only the
`public_key` conjunct, and the view law is stronger than the clauses need), and show from the model's definitions which oracle fields `Model.Lifecycle.decrypt` reads. They
are about a hypothesis of the decrypt refinements, not about the product. No theorem takes the narrowed lemma yet: the
refinements take `DecryptOracleOf` as a hypothesis. This section was made by its author with tool assistance and read by tool-assisted readers working for the maintainer; no reader independent of the maintainer has read it.

- `decryptOracleOf_of_laws`: for every `dh : DhView`, under `DhCodecTotal`, `DhAgreeTotal`, `AeadOpenTotal` and
  `Function.Injective dh.privateKey ∧ Function.Injective dh.publicKey`, and for every `draws : List Model.Lifecycle.Key` and
  `braidKem : Model.Braid.Kem`, some oracle with `oracle.draws = draws` and `oracle.braidKem = braidKem` meets
  `DecryptOracleOf byteRng byteCrc dh byteTrace oracle`. The oracle is `oracleOfLaws` at `InterpO.decrypt` with those two
  fields set; its three DH and AEAD clauses are `dhPublicClause_of_laws`, `dhAgreeClause_of_laws` and
  `aeadOpenClause_of_laws` there, and `random32` is `byte_random32Clause`, which needs no law. It does not go through
  `oracleOf_of_laws`. Its axioms are the three standard axioms, `rand_core_1.error.Error`, `zeroize.Zeroizing`,
  `tacenta_boundary.aead.decrypt`, the two DH types and the seven DH functions `DhCodecTotal` and `DhAgreeTotal` name
  (`PrivateKey::from_bytes`, `public_key`, `agree`, `to_bytes`, `PublicKeyBytes::from_bytes`, `as_bytes` and its equality);
  the other five conjuncts of `DhCodecTotal` are in the list because the statement names it, not because a clause uses
  them. The list names no KEM, signing, identity-test, AEAD-seal or KDF constant; that is a property of this proof, not of
  the statement: a proof of the same statement over the real constants (`InterpO.real`) lists all of them and still takes
  only the four laws.
- `decryptInterp_laws_iff`, `dhViewInjective_real_iff`: `InterpO.decrypt` is the joint model's interpretation
  (`InterpO.model`) with the two DH types, `zeroize::Zeroizing`, the seven DH functions and `aead::decrypt` replaced by the
  real constants, and five fields whose types name those real types and which no clause of `DecryptOracleOf` reads
  (`is_prime_order_public`, `xeddsa::verify` and three `Zeroizing` methods) replaced by refusals; its body carries a `#print`
  pin. The first shows, by `Iff.rfl`, that the three totality shapes over it are `DhCodecTotal`, `DhAgreeTotal` and
  `AeadOpenTotal`, so the kernel accepts it only if each field those shapes read is the real constant; it lists the same
  axioms as the lemma. The second shows that `DhViewInjective` at the real constants is the conjunction the lemma takes; it
  names `dhViewOf`, over `Interp.real`, and so lists every opaque constant `Interp.real` interprets.
- `decrypt_oracle_frame`, `decryptRatchet_oracle_frame`, `dispatchDecrypt_oracle_frame`: in the model, for every codeword
  view, session and message, and two oracles with equal `draws`, `braidKem`, `dhPublic`, `dhAgree` and `aeadOpen`,
  `decrypt view oracle' session message` is `decrypt view oracle session message` with its returned oracle replaced by
  `oracle'` carrying the same remaining draws: the same session, the same result and the same remaining draws. The same holds
  of `decryptRatchet`, and `dispatchDecrypt` reads only `dhAgree`. So `decrypt` reads no other oracle field: not the identity
  rule, the AEAD seal, or the KEM and signing primitives. Proved from the definitions; the axioms are `propext` and
  `Quot.sound`. They are lemmas added to the model (`Model/LifecycleFrame.lean`); no model definition changed.

What these do not show. The four laws are assumed, as in the section above and `LIMITATIONS.md` ("The clauses of
`OracleOf`"): three are totality fields of the contract records, and the view law is about the view the caller chooses.
The oracle on the three primitives `DecryptOracleOf` reads is the code read through the byte views, as in `oracleOfLaws`, so
the result ties the decrypt clauses to the code's own primitives and to no specification of X25519 or the AEAD. Its other
fields (`identityValid`, `aeadSeal`, `kemValid`, `kemEncaps`, `kemDecaps`, `sigVerify`, `sigSign`) come from the model's
toy primitives or from refusals and say nothing about the real ones; `DecryptOracleOf` does not constrain them and, by the
frame lemma, the model's `decrypt` does not read them. Every theorem that takes `OracleOf` (the lifecycle and dispatch
theorems of `UnitLifecycleT3.lean` and `UnitLifecycleInitialDispatch.lean`) still has only `oracleOf_of_laws` and its eleven
laws. Only the byte-stream source is covered; a source with no state of its own, such as `OsRng`, is outside the `random32`
clause (`LIMITATIONS.md`, "The random source"). Not checked: which KEMs meet those agreements; the lemma lets the caller
choose the KEM and shows nothing about it. That the four laws, the contract records and `DecryptRatchetAgreements` at the oracle's
`braidKem` hold together, at one witness and under named laws with a model, is the next section's
(`decrypt_hypotheses_jointly_satisfiable`). The frame lemma is about the model; what the translated
`decrypt_ratchet` calls is what the refinement theorems state. No proof chooses a width of `usize` and none depends on a
compiler-trust axiom, so each result holds at both widths. Each of the six theorems has an axiom pin and a statement pin,
in `UnitOracleDecrypt.lean`, and `InterpO.decrypt` and `dhViewD` have `#print` pins; `attest.py` requires them all
(`REQUIRED_PINS`, `REQUIRED_STATEMENT_PINS`, `REQUIRED_PRINT_FORM`). The statement takes only the four laws, so the other
seven are not hypotheses of this route; that is held by its statement pin and the build. Its axiom pin holds only that the
witness oracle is built without the KEM, signing, identity-test, AEAD-seal and KDF constants.
`check-session-satisfiability-negatives.sh` moves the proof onto the real constants (`InterpO.real`) with the statement
unchanged, which only the axiom pin refuses (the signing constant among the added axioms); routes it through
`oracleOf_of_laws`, which needs seven more hypotheses and is refused by both pins; changes `aead::decrypt` and `agree` in
`InterpO.decrypt` and halves the view law, each refused by the lemma; and swaps each of the five equalities of the helper
`decryptRatchet_oracle_frame` for one about a field `decrypt` does not read, each refused because the proof then fails.
That shows the proof uses each equality, not that the swapped statement is false; `decrypt_oracle_frame` fails with it only
because it calls the helper, and `dispatchDecrypt_oracle_frame` is not mutated.

## Proved (the hypotheses of the `decrypt_ratchet` refinement together at one witness, under named laws with a model)

Location: `Translation/UnitLifecycleDecryptScreen.lean`.

`decrypt_ratchet_refines_complete` takes `DecryptOracleOf`, `DhCodecOf`, `DecryptRatchetContracts`, the class
`DerivedKeysModel`, `DecryptRatchetAgreements` at the oracle's Braid KEM model, `SessionRefines`, `DecryptRatchetHeadroom`,
the trace equation and `DecryptRatchetRun`. Before these results, parts of that set were shown satisfiable in different
places: the four oracle clauses with a toy oracle at `toyKem` (`decrypt_boundary_has_a_model`), the clauses with the code's
oracle from laws (`oracleOf_of_laws`, `decryptOracleOf_of_laws`), and the per-run records at runs over sessions that fail
`Session::invariant`. These results show the whole set, with `Session::invariant` added, at one oracle, one state pair, one
message and one source, under named laws, and show the laws satisfiable together in one interpretation. They are about the
hypotheses of the refinement, not about the product. Their writer, a tool-assisted agent working for the maintainer, and
one tool-assisted reader working for the maintainer have read them, and the reader's findings were applied; no reviewer
independent of the maintainer has.

- `decrypt_hypotheses_jointly_satisfiable`, `decrypt_hypotheses_jointly_satisfiable_statement`: the second is the first
  as the proposition `DecryptHypothesesJointlySatisfiableStatement`. For every Braid KEM model `K` and DH view `dh` that meet
  `DecryptJointLaws K dh`, there are an oracle with `oracle.braidKem = K`, a translated session `real` with
  `Session::invariant real = ok true`, a model session, a message that the translated and model decoders both accept and
  that is a ratchet frame (`Model.Lifecycle.messageType` returns `ratchet`, so the model's dispatch passes it through), and
  a byte-stream source, at which every field of `DecryptHypotheses` holds, for every codeword view, at `byteRng`, `byteCrc`
  and `byteTrace`. `DecryptHypotheses` is the hypothesis list of `decrypt_ratchet_refines_complete` at one choice of every
  binder, with `Session::invariant` added; its agreements field is at the same oracle's `braidKem`. The oracle is the one
  `decryptOracleOf_of_laws` builds (`oracleOfLaws` over `InterpO.decrypt`, the code read through its byte views) with its
  draws set to the source's and its `braidKem` set to `K`. Its axioms are the three standard axioms and the 52 opaque
  constants of the unit its statement and proof name (the 49 interpreted constants of `Interp.real` with the error type
  inside `RngCore`, `Option::eq` on `u64`, and `kem::ciphertext_len`, which `Session::invariant` calls); no compiler-trust
  axiom.
- `decrypt_hypotheses_at_invReal`, `invReal_sessionRefines`, `invReal_headroom`, `invReal_retryRunBounds`, `invReal_run`,
  `sampleMessage_type`: the first is the same at the explicit witness, and the other five are its parts. The session is `invReal k pkb ad a`, which is
  `UnitHeadroomSatisfiable.sessionOf` with one key `pkb` as both identities, `pkb = public_key(k)` with canonical
  prime-order bytes `a`, `ad = identity_ad(pkb, pkb)` (66 bytes), no pending initial message, no established ephemeral
  key, a Triple state over fresh chains and a Braid in `KeysUnsampled`. The model session is `modelOf dh` of it. The message
  is `sampleMessage`, a composite whose ratchet key is 32 zero bytes, with no agreement chunk and an empty ciphertext. The
  source is `sampleRng`, one 32-byte draw. `invReal_run` holds for every view and every oracle with that KEM model.
- `DecryptHypotheses.refines`: `decrypt_ratchet_refines_complete` applies to every `DecryptHypotheses`, so the record is
  the theorem's hypothesis list and a hypothesis added to the theorem and not to the record stops the module building. It
  is compiler-trusted: it lists the nine per-declaration `native_decide` axioms the theorem rests on.
- `decryptJointLaws_named`: the bundle at the real constants gives, by projection, `DhCodecTotal`, `DhAgreeTotal`,
  `AeadOpenTotal` and the DH view law (the four laws of `decryptOracleOf_of_laws`); `SessionUnitBraidT1.ArrayZeroizeTotal`,
  `SessionUnitSpqrT1.ZeroizeTotal` and `LawVecZeroize` (the three zeroize fields stated at the unit's instances);
  `LawPop`, `LawAsMut`, `LawCapacity`, `LawVecZeroize` and `ZeroizeTotal` (the five laws the two sparse agreements are
  derived from); and `KemAgreesFor K`.
- `decrypt_joint_laws_model`, `decrypt_joint_laws_satisfiable`, `modelDecrypt_validKey`: one interpretation,
  `Interp.modelDecrypt` (`UnitLifecycleDecryptRatchetScreen.lean`), with its view `viewDecrypt`, the KEM model `toyKem` and
  `optionEqImpl` (the standard library's definition of `Option::eq`), satisfies every field of `DecryptJointLawsShape`
  together. In it the four KEM length constants are `toyKem`'s sizes (`CT1_LEN` 64, `CT2_LEN` 32, `HEADER_LEN` 64,
  `EK_VECTOR_LEN` 64, against the crate's 1408, 160, 64 and 1536), and the KEM, the X25519 agreement and the AEAD open are
  toys. Their axioms are the three standard axioms and `rand_core_1.error.Error`.
- `decrypt_joint_laws_model_at_shipped_sizes`, `decrypt_joint_laws_satisfiable_at_shipped_sizes`, `modelShipped_sizes`,
  `modelShipped_kemLen`, `modelShipped_kemAgrees`, `modelShipped_validateEk`, `modelShipped_kemClone`, `modelShipped_t3`,
  `modelShipped_validKey`, `shippedHeader_le`, `ekVecShipped_le`, `ct1Shipped_le`, `ct2Shipped_le`: a second
  interpretation, `Interp.modelShipped`, whose four KEM length constants are the crate's
  (`HEADER_LEN` 64, `EK_VECTOR_LEN` 1536, `CT1_LEN` 1408, `CT2_LEN` 160, `tacenta-core/kem/src/lib.rs`), with
  `shippedSizeKem`, a model KEM of those sizes (its key pair, header, encapsulation and validation functions produce byte
  strings of those lengths), its view and `optionEqImpl`, satisfies every field of `DecryptJointLawsShape` together; the
  second states the sizes of the interpretation and the KEM in its statement. The KEM is not ML-KEM: it never refuses and
  its outputs are constant bytes. The X25519 agreement, the AEAD open and the KDFs are `Interp.modelDecrypt`'s toys and
  model bytes. So the laws are shown consistent with the shipped KEM sizes; that the real ML-KEM wrapper meets the
  agreements at some `K` is shown by neither model; at `wrapperKem` it follows from eight assumed laws (the next section). Their axioms are the three standard axioms and
  `rand_core_1.error.Error`.
- `invReal_model_refuses_of_agreement`, `invReal_agreement_is_real`: at the witness, the model's step refuses at the first
  agreement with `nonContributoryAgreement` if the oracle's agreement refuses the all-zero key; at an oracle meeting
  `DecryptOracleOf`, with a view meeting `DhCodecOf`, that agreement is the real `agree` on the key
  `PublicKeyBytes::from_bytes` returns for 32 zero bytes, read through the views.

The laws, `DecryptJointLawsShape` at `Interp.real` (`DecryptJointLaws`), are fifteen fields, each assumed, none proved of
the shipped functions: `dhCodec`, `dhAgree`, `aeadOpen`, `viewInjective` (the four laws of `decryptOracleOf_of_laws`);
`codec` (`DhCodecOf`); `braid`, `triple`, `messageKeyMaterial` (the axiom-level parts of `DecryptRatchetContracts` other
than its three primitive fields; they hold the three zeroize fields at the unit's instances, `LawCapacity` and
`LawVecZeroize`); `laws` (`StdLaws`, with `LawPop` and `LawAsMut`); `truncatePrefix` (`TruncatePrefix`); `derivedKeys` (the
class `DerivedKeysModel`); `agreements` (the Braid KEM agreements at `K` and the KDF agreements); `roundTrips` (the five
`zeroize` round trips); `validKey` and `optionEq` (the two assumptions of `sessionOf_invariant`). Fifteen is a count of
fields, not of distinct statements: a field can hold several laws, `SessionUnitSpqrT1.ZeroizeTotal` and
`SessionUnitBraidT1.ArrayZeroizeTotal` (inside `triple` and `braid`) have the same statement, and `decryptJointLaws_named`
lists `ZeroizeTotal` and `LawVecZeroize` in two groups each. The fields are sufficient and not shown necessary.

What the proof establishes, and what it restates. Of the ten fields of `DecryptHypotheses`, `codec`, `derivedKeys`, the
axiom-level fields of `contracts` and thirteen of the fourteen fields of `agreements` are fields of the bundle, restated.
The proof derives the defined fields of `contracts` and `ErasureAgrees`, and establishes `oracleOf` (from the four laws)
and, at the witness, `invariant`, `related`, `headroom`, `trace_eq` and `run`.

The Braid KEM model. `decryptOracleOf_of_laws` lets the caller choose the oracle's `braidKem`; these results choose `K`, the
model at which the agreements are assumed, so the agreements are stated at the same oracle's `braidKem`. Before that choice
the oracle `oracleOfLaws` builds carries `toyKem` (from `Model.Lifecycle.Examples.toyOracle`); by reading, the agreements
fail there for the real KEM (`KemLenAgrees toyKem` asks the real `CT1_LEN` to be 64; the crate's is 1408). At this witness
the coupling holds by construction: `K` enters the hypotheses only through `agreements` (fields of the bundle), `related`
(which holds for every `K`, because the Braid is in `KeysUnsampled`) and `run` (which does not depend on `K`, because the
run carries no chunk). Nothing in Lean tells `toyKem` apart from any other `K` here; the theorem holds at `K := toyKem`
under `DecryptJointLaws toyKem dh`. At this witness the coupling is not tested; a second witness whose Braid holds a key
pair tests it ("Proved (the hypotheses of the `decrypt_ratchet` refinement at a session whose Braid holds a key pair
...)"). The oracle's other KEM fields
(`kemValid`, `kemEncaps`, `kemDecaps`) are `oracleOfLaws`'s and are not related to `K`; the model's `decrypt` does not read
them (`decrypt_oracle_frame`). Not checked here: that some `K` meets the agreements at the real constants; it is assumed. In
the two models it is `toyKem` and `shippedSizeKem`. The next section gives one such `K`, `wrapperKem`, read off the wrapper,
at which the KEM agreements follow from eight laws about the wrapper's functions, themselves assumed.

What these do not show. The state is built for the hypotheses: it is not shown to be produced by `establish_initiator`,
`establish_responder` or `import`, and it has no pending initial message, no established ephemeral key and no receiving
chain. The laws are assumed. The oracle is the code read through its byte views, not a specification of X25519 or the
AEAD, and nothing is shown of the primitives. The run carries no agreement chunk, so the chunk and honest fields of
`DecryptRatchetRun` hold by their arm for a message without one. Which way the model's step at the witness goes is not
fixed by the laws: it refuses at the first agreement if the real agreement refuses the all-zero key, which no law states;
by reading `tacenta-core/boundary/src/dh.rs` (`agree` returns `None` on a non-contributory result, which the all-zero key
gives) it does, and in the model interpretation it does too. So the witness does not exercise the Triple receive, the
AEAD, an eviction round or a success. The substitution step, from a model of the laws to the hypotheses at the real
constants, is an argument about derivations and not a theorem inside Lean (`LIMITATIONS.md`). Only the byte-stream source is
covered. No proof chooses a width of `usize` (the bounds used, `usize_max_ge` and `cMax_usize`, hold at both) and only
`DecryptHypotheses.refines` depends on a compiler-trust axiom, so each result holds at both widths; no hypothesis of the
set is width-dependent at this witness. Each of the twenty-eight theorems has an axiom pin and a statement pin, and `invReal`,
`DecryptJointLawsShape`, `DecryptJointLaws`, `DecryptHypotheses`, `DecryptHypothesesJointlySatisfiableStatement`,
`shippedSizeKem`, `ekVecShipped`, `ct1Shipped`, `ct2Shipped`, `Interp.modelShipped` and `viewShipped` have `#print` pins;
`attest.py` requires them all. `check-session-satisfiability-negatives.sh` removes each of the fifteen laws
from the bundle, in a copy holding only the two theorems that consume it, each refused; moves the agreements of
`DecryptHypotheses` to another oracle's KEM model, refused by `DecryptHypotheses.refines` and, with that link and its pins
removed and the proof adjusted so that it builds, by the statement pin of `DecryptHypotheses` alone; builds the oracle at
`toyKem` in place of `K`, refused by the main theorem; renames the model witness, refused by its pins; and sets the
shipped-size model's `CT1_LEN`, and its KEM's first-ciphertext size, to the toy size, refused by `modelShipped_sizes` and
by `modelShipped_kemLen`.

## Proved (a Braid KEM model read off the `tacenta_kem` wrapper, and the KEM agreements at it, under eight laws with a model)

Location: `Translation/UnitKemWrapperModel.lean`.

The Braid refinement agreements `KemLenAgrees K`, `KemAgreesFor K` and `ValidateEkAgrees K` relate the unit's opaque
`tacenta_kem` functions to a Braid KEM model `K`. The section above takes them as a field of its law bundle at a free `K`,
and before these results no `K` in the tree was related to the shipped wrapper (`toyKem` and `shippedSizeKem` never refuse
and return constant bytes). These results build one `K` from the wrapper's functions and prove the agreements of it from
eight laws about those functions, assumed. They are about opaque constants read through byte views, not about ML-KEM.
Their writer, a tool-assisted agent working for the maintainer, has read them; no other reader has.

- `wrapperKemOf` (a definition, `#print`-pinned) and `wrapperKem`, which is `wrapperKemOf Interp.real`: a
  `Model.Braid.Kem` whose four operations call the wrapper's functions on byte views of their arguments. The model's
  randomness `n` is read as the byte-stream source `byteRng` holding the little-endian digits of `n` (64 bytes for key
  generation, 32 for encapsulation). The private part is the 64 key-generation bytes, from which `decaps` calls `generate`
  again and then `decapsulate`; the encapsulation secret is the 32 encapsulation bytes followed by the header, from which
  `encaps2` calls `encapsulate1` again and then `encapsulate2`. Each operation returns `none` exactly where the call it
  makes returns `Err` or does not return. `hashEk` (`hashEkOf`) is read off `validate_ek`: the 32-byte `hek` it accepts
  after the seed, where there is one, and the empty string where there is none. The sizes are the crate's: 1536, 1408 and
  160.
- `kemLenAgrees_wrapperKem`, `kemAgreesFor_wrapperKem`, `validateEkAgrees_wrapperKem`, `kemCloneAgrees_wrapperKem`,
  `t3Agreements_wrapperKem`: under `WrapperKemLaws`, `KemLenAgrees`, `KemAgreesFor` (both clauses, two-sided: the model
  answers `none` exactly where the wrapper's call returns `Err`) and `ValidateEkAgrees` hold at `wrapperKem`, by proof from
  the laws; `KemCloneAgrees` mentions no KEM model and is the law `LawKemClone` restated; the last gives the record
  `T3Agreements Interp.real wrapperKem` with the two KDF agreements taken as given. The axioms of each are the three
  standard axioms and the 49 constants `Interp.real` interprets with the error type inside `RngCore`; no compiler-trust
  axiom.
- `kemLen_wrapperKemOf`, `kemAgrees_wrapperKemOf`, `validateEkAgrees_wrapperKemOf`, `t3Agreements_wrapperKemOf`,
  `hashEkOf_eq`, `validate_of_hashEkOf`, `decaps_clause`, `encaps2_clause`: the first four are the same over any
  interpretation of the unit's opaque constants and its `WrapperKemLawsShape`, and the last four are their steps: where
  `validate_ek` accepts a 32-byte hash the model's hash is it, and conversely; the decapsulation clause for a key pair
  generated from 64 bytes; the second-half clause for a state the first half produced. Their axioms are the three standard
  axioms and `rand_core_1.error.Error`.
- `keyPairRefines_wrapperKem`, `encapsRefines_wrapperKem`: under the laws, a key pair `generate` returns from any source
  that answers, and an encapsulation state `encapsulate1` returns from any source that answers on a 64-byte header
  `ekSeed ++ hek`, refine at `wrapperKem` some private part or secret (`KeyPairRefines`, `EncapsRefines`), refusing exactly
  where the model refuses.
- `LawKemConstants_is`, `LawGenerateSeeded_is`, `LawGeneratedKeyPair_is`, `LawEncapsulate1Seeded_is`,
  `LawEncapsulate2Fresh_is`, `LawValidateEkTotal_is`, `LawValidateEkUnique_is`, `LawKemClone_is`, `wrapperKemLaws_iff`:
  each law at the real constants is its shape at `Interp.real` (`Iff.rfl`), and `WrapperKemLaws` is the eight together.
- `decrypt_hypotheses_jointly_satisfiable_at_wrapperKem`, `decryptWrapperLaws_joint`, `DecryptWrapperLawsShape.toJoint`:
  `decrypt_hypotheses_jointly_satisfiable` at `K := wrapperKem`, with the joint bundle's `agreements` field (the KEM
  agreements at a free `K` and the KDF agreements) replaced by the eight laws and the two KDF agreements
  (`DecryptWrapperLaws dh`); its other fourteen fields are the joint bundle's. Under `DecryptWrapperLaws dh` there are an
  oracle with `oracle.braidKem = wrapperKem` and the rest of the section above's conclusion. Its axioms are the three
  standard axioms and the same 52 opaque constants as `decrypt_hypotheses_jointly_satisfiable`'s; no compiler-trust axiom.
- `decrypt_wrapper_laws_model`, `decrypt_joint_laws_model_at_wrapperKemOf`, `decrypt_wrapper_laws_satisfiable`,
  `modelShipped_wrapperKemLaws`: one interpretation, `Interp.modelShipped` (the section above), whose four KEM length
  constants are the crate's, with its view and `optionEqImpl`, satisfies the wrapper bundle, and so the joint bundle at
  `wrapperKemOf Interp.modelShipped`, whose agreements come from the same proof as at `wrapperKem`. Its key generation and
  encapsulation ignore the source and return constant bytes and it never refuses, so it is not ML-KEM and exercises no
  refusing arm. Their axioms are the three standard axioms and `rand_core_1.error.Error`.
- `toU8_u8`, `bytesOf_sliceOf`, `bytesOf_map_u8`, `length_bytesOf_le`, `length_nil_le`, `bytesSlice_sliceOf`,
  `length_bytesSlice_of`, `sliceOf_bytesSlice`, `sliceOf_vecSlice`, `append_le_usize`, `length_leBytes`, `leBytes_leNat`,
  `streamOf_leNat`: the byte views. A slice read as bytes and back is itself; every byte stream of length `k` is the stream
  of some number's `k` digits, so the model's randomness reaches every seed.

The eight laws (`WrapperKemLaws`, each `#print`-pinned), each a statement about opaque `tacenta_kem` constants of the unit
and the Lean byte-stream source `byteRng`, none about translated code, each assumed and none proved of the shipped wrapper:
`LawKemConstants` (the four length constants are 64, 1536, 1408 and 160); `LawGenerateSeeded` (from any source that
answers, `generate` returns what it returns from the byte stream of some 64 bytes); `LawGeneratedKeyPair` (a key pair
generated from 64 bytes has a 64-byte header and a 1536-byte vector that `validate_ek` accepts together, and `decapsulate`
returns on it for any two ciphertext halves of 1408 and 160 bytes); `LawEncapsulate1Seeded` (from any source that answers
and a 64-byte header, `encapsulate1` returns what it returns from the byte stream of some 32 bytes);
`LawEncapsulate2Fresh` (`encapsulate2` returns on a state `encapsulate1` produced and any 1536-byte vector);
`LawValidateEkTotal` (`validate_ek` returns on a 64-byte header and a 1536-byte vector); `LawValidateEkUnique` (two
64-byte headers with the same first 32 bytes that `validate_ek` accepts with one vector are the same bytes); and
`LawKemClone` (`KemCloneAgrees`). "Returns" means the call is `ok`, whether its value is `Ok` or `Err`. The
coefficient-bound refusal of `encapsulate2` is inside that opaque function, so it enters only through
`LawEncapsulate2Fresh`, which says nothing of whether `encapsulate2` refuses a fresh state. The corollary also takes, through the bundle's `braid` field (`BraidReceiveAxiom`), `SessionUnitBraidT1.KeyPairDecapsulateTotal`, `Encapsulate2Total` and `ValidateEkTotal`, which say that `decapsulate`, `encapsulate2` and `validate_ek` return on every value, restored key pairs and states and inputs of any length included; the eight laws do not narrow them, and those three imply the totality parts of `LawGeneratedKeyPair`, `LawEncapsulate2Fresh` and `LawValidateEkTotal`. They were in the bundle before these results and are not shown false; the first is the statement `GAP-REGISTER.md`, row `KEM-STORED-STATE-TOTALITY`, records as sampled and not shown total.

What these do not show. Nothing about ML-KEM: the operations are whatever the wrapper's functions are. A key pair or
state restored by `IncrementalKeyPair::from_bytes` or `EncapsState::from_bytes` has no model value at `wrapperKem`, so the
two refinement relations are shown for values `generate` and `encapsulate1` produce, not for imported ones.
`KemDrawsSucceed` and `Model.Braid.Kem.Correct` are not shown at `wrapperKem`. At the witness of the corollary the Braid is in
`KeysUnsampled`, so no state there holds a key pair or an encapsulation state and the relation of `wrapperKem` to a held
value is not exercised; the corollary holds at `toyKem` under the joint bundle at `toyKem` as well. The next section
exercises the relation at a held key pair. The KDF agreements stay
assumed. The interpretation is a model in the substitution sense (`LIMITATIONS.md`), an argument about derivations and
not a theorem inside Lean. No proof chooses a width of `usize` (`le64`, `usize_max_ge`), and no result depends on a
compiler-trust axiom. Each of the forty-four theorems has an axiom pin and a statement pin; `wrapperKemOf`, `wrapperKem`,
`hashEkOf`, the eight laws, `WrapperKemLawsShape`, `WrapperKemLaws`, `DecryptWrapperLawsShape`, `DecryptWrapperLaws`,
`bytesSlice`, `vecSlice`, `leBytes`, `leNat` and `streamOf` have `#print` pins; `attest.py` requires them all.
`check-session-satisfiability-negatives.sh` removes each of the eight laws, and each of the three fields that replace the
joint bundle's agreements, in a copy without the pins, `wrapperKemLaws_iff` and the model, each refused by a proof that
projects it; makes each refusing arm of the model (key generation, the second half of encapsulation, decapsulation) answer
`some`, gives the hash a 32-byte fallback and sets the first-ciphertext size to the toy size, each refused by the agreement
proofs; restates the corollary at `toyKem` under the joint bundle at `toyKem`, refused by its statement pin alone; and
renames the model witness, refused by its pins.

## Proved (the hypotheses of the `decrypt_ratchet` refinement at a session whose Braid holds a key pair, with the KEM model read off the wrapper)

Location: `Translation/UnitHeldKemWitness.lean`.

The two sections above show the hypotheses of `decrypt_ratchet_refines_complete` together at a witness whose Braid is in
`KeysUnsampled`, where the relation holds at every Braid KEM model and the run carries no agreement chunk. These results
show them together at a second witness whose Braid holds a key pair, so that the relation at the KEM model read off the
wrapper is asked of a held value. The witness is built for the hypotheses, as the first is; the shipped code does not
produce this combination of Triple and Braid states; the invariant admits it. Their writer, a tool-assisted agent working for the maintainer, has read them; no other
reader has.

- The definitions `heldReal`, `heldModel`, `heldBraid`, `heldModelBraid`, `hdrMsgOf` and `HeldKemAt` (`#print`-pinned):
  the first witness's session with its Braid replaced by `KeysSampled` at epoch 1 under the zero authenticator, holding a key
  pair `IncrementalKeyPair::generate` returned from a 64-byte stream and an encoder `Encoder::new` built from the pair's
  header followed by a 32-byte MAC, advanced by one `next_chunk`; and the model session read off it with the model Braid
  `keysSampled 1` holding the 64 drawn bytes as the private part, the bytes of the pair's `ek_vector` as the vector, and
  the encoder of the header message advanced once. `HeldKemAt real model` says exactly that, and that the model Braid is
  what `Model.Braid.send wrapperKem` returns from the fresh initiator state at the randomness the 64 bytes are
  (`heldModelBraid_is_send`, transition (1)).
- `heldModelBraid_is_send`: for any KEM model `K`, where `K.keyGen rand` returns `(dk, ekSeed, ekVector)` and
  `K.hashEk ekSeed ekVector = hek`, `Model.Braid.send K rand` from `keysUnsampled` at epoch 1 under the zero
  authenticator ends in `heldModelBraid dk ekVector (ekSeed ++ hek)`.
- `held_key_agreements`: under `WrapperKemLaws`, for a key pair `generate` returned from 64 bytes, `wrapperKem.keyGen` at
  that randomness returns the 64 bytes, the header's first 32 bytes and the vector's bytes; `wrapperKem.hashEk` of that
  seed and vector is the header's last 32 bytes; the header has 64 bytes and the vector `wrapperKem.ekSize`;
  `key_pair_valid` returns `true`; and `FreshKeyPairRefines wrapperKem` holds of the pair, the private part and the
  vector, its decapsulation clause comparing `wrapperKem.decaps` with the real `decapsulate` on every pair of ciphertext
  halves of 1408 and 160 bytes. Proved from `wrapperKem`'s definition and the laws `LawGeneratedKeyPair` and
  `LawValidateEkUnique`, not by projecting `KemAgreesFor wrapperKem`. Which parts are definitional: `wrapperKem`'s
  operations call the real `generate` and `decapsulate` on the held bytes, so the key-generation part and the
  decapsulation clause (the real `decapsulate kp` compared with itself) hold by unfolding `wrapperKem`, with only the
  totality of `decapsulate` on generated pairs taken from `LawGeneratedKeyPair`; so does `HeldKemAt`'s conjunct that
  the model Braid is the model's transition (1). What compares real bytes beyond the definitions: the vector, by value
  at every KEM model (`held_relation_pins_vector`), the header hash (through `hashEkOf`, `LawValidateEkUnique` and
  `validate_ek` accepting the generated pair), and the lengths. Axioms: the three standard axioms and the 49
  constants `Interp.real` interprets with `rand_core_1.error.Error`.
- `held_encoder`, `chunks_length`, `hdrMsgOf_length`, `hdrMsgOf_le`: under `DivCeilValue` and `ErasureAgrees`, the real
  `Encoder::new` of a 96-byte message returns an encoder whose first `next_chunk` returns the codeword of index 0 and an
  encoder that refines the model encoder advanced once, passes `Encoder::invariant` and is sized for 96 bytes.
- `held_invariant`, `structural_held`, `heldBraid_invariant`: `Session::invariant` returns `true` on the held session.
  In the joint statement it rests on `ValidKeyShape`, `OptionEqU64Shape` and `DhCodecTotal` (as for the first witness),
  `HEADER_LEN = 64` (`LawKemConstants`), `DivCeilValue` (the encoder's size) and `LawGeneratedKeyPair`
  (`key_pair_valid`), with `LawGenerateSucceeds` for the key pair itself. The structural clauses read epoch 1, tag 1
  and the initiator's role off `KeysSampled`; clause (g)'s Braid arm calls `Encoder::invariant`, `encoder_sized` and
  `key_pair_valid`.
- `held_sessionRefines`, `held_relation_pins_vector`, `held_not_refines_toyKem`: the relation at the held state at any
  KEM model from the key pair's and the encoder's refinements; at every KEM model the relation fixes the model's vector to
  the real `ek_vector`'s bytes; and at `toyKem` the relation is false, because `toyKem` decapsulates to the 64-byte private
  part and no 32-byte shared secret is that: a length mismatch, not a comparison of held bytes. At the first witness the
  relation holds at every model.
- `decrypt_hypotheses_jointly_satisfiable_at_wrapperKem_held`, `decrypt_hypotheses_at_held`,
  `decrypt_hypotheses_at_held_of_run`, `held_run`, `held_braid_output`: under `DecryptWrapperLaws dh` and
  `LawGenerateSucceeds`, there are an oracle with `oracle.braidKem = wrapperKem` (the code's oracle,
  `decryptOracleOf_of_laws`), a session that passes `Session::invariant` and a related model session with `HeldKemAt`,
  the first witness's message and source, at which every field of `DecryptHypotheses` holds, for every codeword view.
  Axioms: the three standard axioms and the same 52 opaque constants as
  `decrypt_hypotheses_jointly_satisfiable_at_wrapperKem`; no compiler-trust axiom.
- `held_model_refuses_of_agreement`: at either message the model's step refuses at the first agreement with
  `nonContributoryAgreement` when the oracle's agreement refuses the all-zero key. `invReal_agreement_is_real` applies
  unchanged: the session's ratchet private key is the first witness's.
- `LawGenerateSucceeds_is`, `lawGenerateSucceeds_of_kemDrawsSucceed`, `modelShipped_generateSucceeds`,
  `held_laws_satisfiable`: the added law at the real constants is its shape at `Interp.real`; it follows from the
  key-generation half of `KemDrawsSucceed` with `LawGenerateSeeded`; and `Interp.modelShipped` satisfies it together with
  the wrapper bundle, with the crate's four KEM length constants.

Pinned, and so listed, but not a claim:

- `decrypt_hypotheses_with_chunk_at_wrapperKem_held`, `held_chunk_run`, `chunk_braid_step`, `zero_chunk_codeword`,
  `codeword_zero`, `ct1Zeros_codeword0`, `ct1Zeros_length`, `ct1Zeros_le`, `u8_map_inj`, `chunk_decode_model`,
  `chunk_decode_real`, `chunkMessage_type`, `chunkBytes_le`, `sliceOf_chunkMessage`: not a claim; listed because each is
  pinned. A caller-selected run: the hypotheses at the held state and a message carrying a `ct1` chunk
  (`chunkComposite`, `chunkMessage`), with the chunk and the codeword view (`chunkView`) chosen together. The chunk is
  index 0 and 32 zero bytes, which the real encoder makes a codeword of 1408 zero bytes (`zero_chunk_codeword`, a
  theorem about translated code); the view is a constant that reads every chunk as that codeword. 1408 zero bytes is
  not a ciphertext `encapsulate1` produces, so no honest responder sends this chunk; `HonestChunk` asks nothing at
  `keysSampled`; and the model's refusal at the first agreement discards the Braid step. It is not a non-vacuity
  statement for chunks, which would take every chunk that fits the real decoder, with its view derived from it.

The added law, assumed and not proved of the shipped wrapper: `LawGenerateSucceeds` (`IncrementalKeyPair::generate`
returns `Ok` from the byte stream of some 64 bytes), a statement about one opaque `tacenta_kem` constant and the Lean
byte-stream source. None of the eight wrapper laws gives it: each speaks of a key pair only where `generate` has returned
one. By reading `tacenta-core/kem/src/lib.rs` (`generate` draws one 64-byte seed and passes it to libcrux's key
generation), it does not refuse at that length; that reading is not checked by a test in the tree. Everything else the
witness uses is a field of `DecryptWrapperLaws`.

The fourteen agreement fields. The `agreements` field of `DecryptHypotheses` is the record `DecryptRatchetAgreements
wrapperKem`, as at the corollary of the section above: `kem`, `kemLen` and `validateEk` are derived from the eight wrapper
laws, `erasure` from `divCeil` and `TruncatePrefix`, and the other ten (`hmac`, `hkdf`, the five round trips, `pop`,
`asMut`, `kemClone`) are fields of the bundle, restated; the record is exactly the corollary's. What this witness adds is
that the KEM clauses are asked at a held value: `related` contains `FreshKeyPairRefines` at the held key (the
decapsulation clause, the vector and the header-hash clause), `invariant` contains `key_pair_valid kp`, and the proof
establishes these (`held_key_agreements`). No field reads an encapsulation state: the witness is the initiator's, so `EncapsRefines` is not
asked.

What these do not show. The state is built for the hypotheses; the shipped code does not produce this combination of
Triple and Braid states; the invariant admits it. `Session::encrypt` commits the Triple and the Braid together
(`tacenta-core/session-unit/src/lifecycle.rs`, `self.triple = candidate; self.braid = braid_next`), so no session holds
a Braid in `KeysSampled` beside a Triple that has sent nothing, as this one does. `Session::invariant` reads neither the
Braid's authenticator (here the zero keys; `Auth::init` derives them by HKDF) nor the header its encoder carries, and
`SessionRefines` does not relate that header to the key pair; only `HeldKemAt` does. The header message carries the
model's MAC under the zero authenticator, where `Braid::send` computes it with the opaque HMAC; that the real
`Braid::send` from `KeysUnsampled` under the zero authenticator lands on this Braid state was not attempted. A run
carrying an honest chunk is not shown: the chunk run above is caller-selected, and a run into a decoder that already
holds a chunk is not reached, since `Session::invariant` at such a state calls `Decoder::invariant`, a loop over the held
chunks that no result here evaluates. The oracle's other KEM fields are not related to `wrapperKem`.
Which way the model's step goes is fixed by one value of the real `agree` that no law states, so no Triple receive, AEAD
open or success is reached. Nothing about ML-KEM, and a key pair restored by `from_bytes` has no model value at
`wrapperKem`. The interpretation is a model in the substitution sense (`LIMITATIONS.md`). No proof chooses a width of
`usize` (`usize_max_ge`), and no result depends on a compiler-trust axiom. Each of the thirty-six theorems has an axiom
pin and a statement pin; `LawGenerateSucceeds`, `LawGenerateSucceedsShape`, `hdrMsgOf`, `heldModelBraid`, `heldBraid`,
`heldReal`, `heldModel`, `HeldKemAt`, `ct1Zeros`, `chunkComposite`, `chunkMessage` and `chunkView` have `#print` pins;
`attest.py` requires them all. `check-session-satisfiability-negatives.sh` alters the held vector, the held private part
and the header's hash each in one byte where `held_key_agreements` states them, each refused by its proof; moves the joint
statement to `toyKem`, refused only because `decrypt_hypotheses_at_held` takes `oracle.braidKem = wrapperKem` (the
evidence that the relation fails at `toyKem` is the theorem `held_not_refines_toyKem`, not this negative), and moves the
refutation at `toyKem` to `wrapperKem`, refused by its proof; removes the added law, refused; alters the chunk in one byte and gives
it another index, each refused by the run's codeword proof; and drops from `HeldKemAt` its conjunct that the model holds
the real bytes, with the proofs adjusted, refused by its `#print` pin alone (10 cases, 1 of them an acceptance).

## Proved (bounded P6 session lifecycle observations)

Location: `Proofs/SessionTrace.lean`. These are the three narrow theorems for
`SESSION-LIFECYCLE-01`, over `Model.SessionTrace`'s explicit abstract state.
They are part of the recorded P6 L2 evidence, not a new public security
requirement and not a refinement of `tacenta-core`'s session orchestration.
The abstract crypto verdicts and the committed joint snapshot are assumptions
of the model; the concrete lifecycle test and operation corpus are separate,
bounded evidence that selected Rust traces fit this boundary.

- `refusal_restore_preserves_continuation`: adding an ordinary abstract
  refusal and restoration from the same committed snapshot before a later
  honest suffix leaves that suffix's final abstract observation unchanged.
  It excludes crash windows, hostile rollback and product-store transaction
  semantics.
- `terminal_failure_preserves_refusal`: once an abstract terminal agreement
  failure is committed, every later abstract lifecycle suffix remains in the
  failed phase. It does not say a caller cannot replace storage with an older
  hostile snapshot.
- `replay_has_no_second_acceptance`: receiving a message already in the
  committed accepted observation has no abstract operation effect. Concrete
  P6 traces separately check the public replay refusal they return.

## Proved (the numeric premises of the central theorems hold together at a concrete state)

Location: `Translation/NumericWitnessLeaf.lean`, `Translation/NumericWitnessTriple.lean`, `Translation/NumericWitnessSession.lean`.

A theorem whose premises no state meets is true and says nothing. For 44 theorems (13 in the standalone
translations, 12 on the three-leaf unit, 19 on the eight-leaf session unit), the receive and send
panic-freedom and refinement theorems of the classical ratchet, the sparse ratchet, the Triple Ratchet and the
ML-KEM Braid and the decoded-state receive refinement, each module proves that one concrete state meets, at once, the theorem's
numeric premises (bounds on lengths, counters and epochs written against `usize::MAX`, `u32::MAX` and
`u64::MAX`), its numeric predicates about a state (`ct1_bounded`, `decoders_bounded`, `EncodersLive`) and its
relations between a translated value and a model value (`StateRefines`, `StateR`, `HeaderR`; for the Braid theorems the
relations are left out, as set out below). Every proof is
about the constant `Usize.max`, of which Lean knows only that it is `2^32 - 1` or `2^64 - 1`, so each holds at
both platform widths and none appeals to a width.

The statement of each witness is checked against its theorem and not trusted. `scripts/check-precondition-witnesses.sh` reads the
theorem's type from the built environment, rebuilds the conjunction of the premises its table puts inside the
witness, requires the module's `Premises.T` to equal it and `sat_T` to prove exactly `Premises.T`, and requires
every other premise of `T` to be classified as `boundary` or `unwitnessed`, so a premise added to a theorem
later is refused until it is classified. It runs inside `no-sorry.sh` with 36 cases, 10 that must be accepted and 26 that apply one change and must be refused (a bound weakened
in a statement, a witness deleted or replaced by `True`, a statement or a table row removed, a premise left
unclassified, a numeric premise listed as outside, a premise added to a theorem, a `sat_` theorem or an `*_at_witness`
theorem that the table does not account for). The check is a script and
not a Lean theorem because `check-lean-constructs.sh` refuses elaboration-time code in this package; it
trusts the script's reading of the environment, and classifies a hypothesis as numeric by a comparison on a
natural number or an integer in its propositional skeleton or by the name of a numeric state predicate, so a
numeric bound hidden behind a definition whose name is not on the script's list of numeric state predicates is
classified by the table's author; `ChainCounterBounded`, a bound on a chain's counter, is such a name and is on the list.
A numeric premise stated through a definition whose name is not on the list is not recognised, and if the table classifies it
as `boundary` the check accepts it: a toy theorem with `(h2 : Roomy n)`, where `Roomy n := n + 1 < Usize.max`, passes. A scan of
the 44 witness rows and the 18 discharge rows with definitions unfolded found no such premise in the tree; the only hypotheses
it flagged were the contract bundles `RatchetAgreesFor` and `SpqrAgreesFor`, whose numeric content is in implication antecedents.
The check also does not tie the state a `sat_` proof uses to the state `spqrS_inv` and `ratS_inv` are about, or to the sizes
described below.

All 66 theorems named below are pinned with `#guard_msgs in #print axioms`. 54 list only `propext`, `Classical.choice` and
`Quot.sound`. The other 12 are the Braid theorems, whose statements mention opaque types: the six standalone ones also list
`tacenta_braid.tacenta_erasure.Decoder` and `Encoder` and `tacenta_braid.tacenta_kem.EncapsState` and `IncrementalKeyPair`, and the
six on the session unit also list `tacenta_session_unit.tacenta_kem.EncapsState` and `IncrementalKeyPair`. No pin lists a
compiler-trust axiom. The pin list is `REQUIRED_PINS` in `scripts/attest.py`.

**What this is not.** A witness says a premise is not vacuous. It does not say a reachable state meets it:
among the values the decoder's invariant allows, `events + 1 < u32::MAX` fails only at `u32::MAX - 1` and
`epoch + 1 < u64::MAX` only at `u64::MAX - 1` (`NumericBoundary.lean`), and each of those values is an ordinary state. The witnesses exclude two groups of
premises, named per theorem in the script's table and in each module's docstring: the `boundary` premises, which
are statements about opaque operations or translated functions (`HmacAgrees`, `VecRetainTotal`, `KemAgreesFor`, ...,
recorded in `LIMITATIONS.md` and, in part, given a model in `Satisfiability.lean`), and the `unwitnessed` ones, which
are the Braid's relations between a translated and a model Braid (`StateRefines`, `MsgRefines`, `HonestChunk`), which
need a value of an opaque type (the KEM), and `hdec` of `decoded_receive_refines`, that a byte string decodes to the
state. On the standalone leaves the Braid witnesses are at `KeysUnsampled`, where `ct1_bounded` holds by its `True` arm; the
arms of `ct1_bounded` that bound a stored ciphertext hold values of opaque types and are **not shown**, and that stays open.
On the session unit `decoders_bounded` is witnessed in its real arm, a decoder at the cap its invariant admits
(`needed = 65536`); the arms that hold a KEM value stay open there too. The states are small, not extremal (one chain and one
skipped key, one stored skipped key, a counter at 1 or 5). That is what the proofs use; no gate checks it, and no gate checks
that the state a `sat_` proof uses is the one `spqrS_inv` and `ratS_inv` are about. The bounds up to their caps are in the next
sections.

- `sat_T1_receive_no_panic`, `sat_T3_receive_refines`, `sat_ImportInv_Ratchet_decoded_receive_refines`: the classical ratchet's
  receive (the panic-freedom theorem, the refinement, and the decoded-state refinement), standalone translations.
  The decoded-state theorem's `hdec` is outside the witness.
- `sat_SpqrT1_receive_no_panic`, `sat_SpqrT1_send_no_panic`, `sat_SpqrT3_receive_refines`, `sat_SpqrT3_send_refines`:
  the sparse ratchet's receive and send, standalone. The witness state has one chain and one skipped key, and the
  refinements' `hepoch`, `hroom`, `hcb`, `hsb`, `hnewb`, `hskiproom`, `hone` and `hcounter` hold there together.
- `sat_BraidT1_Braid_receive_no_panic`, `sat_BraidT1_Braid_step_receive_no_panic`, `sat_BraidT3_Braid_receive_refines`,
  `sat_BraidT3_step_receive_refines`, `sat_BraidT3_Braid_send_refines`, `sat_BraidT3_step_send_refines`: the Braid's
  `ct1_bounded`, `epoch + 1 < u64::MAX` and `EncodersLive`, standalone, at the states described above. The relations between
  a translated and a model Braid are not witnessed.
- `spqrS_inv`, `ratS_inv`: the two ratchet states the standalone witnesses use satisfy the decoder's invariant
  (`ImportInv.Spqr.Inv`, `ImportInv.Ratchet.Inv`), the predicate every state `from_bytes` returns satisfies. One direction only.
- `sat_UnitT1_receive_no_panic`, `sat_UnitT3_receive_refines`, `sat_UnitSpqrT1_receive_no_panic`, `sat_UnitSpqrT1_send_no_panic`,
  `sat_UnitSpqrT3_receive_refines`, `sat_UnitSpqrT3_send_refines`, `sat_UnitTripleT1_State_receive_no_panic`,
  `sat_UnitTripleT1_State_send_no_panic`, `sat_UnitTripleT3_receive_refines`, `sat_UnitTripleT3_receive_refines_discharged`,
  `sat_UnitTripleT3_send_refines`, `sat_UnitTripleT3_send_refines_discharged`: the same for the three-leaf unit, including the
  Triple's four size premises (`hone`, `hs`, `hroom`, `hskiproom` and their model-state forms) with the epoch and counter premises.
  The unit has no decoder-invariant module, so nothing is shown about a decoder there.
- `sat_SessionUnitT1_receive_no_panic`, `sat_SessionUnitT3_receive_refines`,
  `sat_SessionUnitRatchetImportInv_Ratchet_decoded_receive_refines`, `sat_SessionUnitSpqrT1_receive_no_panic`,
  `sat_SessionUnitSpqrT1_send_no_panic`, `sat_SessionUnitSpqrT3_receive_refines`, `sat_SessionUnitSpqrT3_send_refines`,
  `sat_SessionUnitTripleT1_State_receive_no_panic`, `sat_SessionUnitTripleT1_State_send_no_panic`,
  `sat_SessionUnitTripleT3_receive_refines`, `sat_SessionUnitTripleT3_receive_refines_discharged`,
  `sat_SessionUnitTripleT3_send_refines`, `sat_SessionUnitTripleT3_send_refines_discharged`,
  `sat_SessionUnitBraidT1_Braid_receive_no_panic`, `sat_SessionUnitBraidT1_Braid_step_receive_no_panic`,
  `sat_SessionUnitBraidT3_Braid_receive_refines`, `sat_SessionUnitBraidT3_step_receive_refines`,
  `sat_SessionUnitBraidT3_Braid_send_refines`, `sat_SessionUnitBraidT3_step_send_refines`: the same for the eight-leaf session
  unit, with `decoders_bounded` for the Braid. The lifecycle theorems (`encrypt_no_panic` and the others) are not here: their
  headroom records hold values of opaque boundary types.
- `session_unit_spqrS_inv`, `session_unit_ratS_inv`: the session unit's two ratchet witness states satisfy the decoder invariant.
- `spqr_receive_premises_at_witness`, `spqr_send_premises_at_witness`, `spqr_advance_premises_at_witness`,
  `spqr_maybe_advance_premises_at_witness`, `spqr_clear_old_epochs_premises_at_witness`, `ratchet_receive_premises_at_witness`,
  `braid_receive_premises_at_witness`, `braid_step_receive_premises_at_witness`,
  `session_unit_spqr_receive_premises_at_witness`, `session_unit_spqr_send_premises_at_witness`,
  `session_unit_spqr_advance_premises_at_witness`, `session_unit_spqr_maybe_advance_premises_at_witness`,
  `session_unit_spqr_clear_old_epochs_premises_at_witness`, `session_unit_ratchet_receive_premises_at_witness`,
  `session_unit_braid_receive_premises_at_witness`, `session_unit_braid_step_receive_premises_at_witness`,
  `triple_receive_premises_at_witness`, `triple_send_premises_at_witness`: the first eight are in the standalone translations and
  the other ten on the session unit; each is a discharge theorem of the next section applied at the
  witness state, with its type read off the application (`type_of%`). A discharge theorem takes the decoder invariant and other
  premises beyond its theorem's own, and one whose premises no state meets would be true and empty; these show the state relation, the
  epoch step and the invariant met together at a state. They stop building if a premise they apply is changed so that the witness
  state no longer meets it. A premise added after the last argument of a discharge theorem leaves one building, at a function type,
  so the build does not hold that case; `scripts/check-precondition-witnesses.sh` refuses an `*_at_witness` theorem whose type is a
  function type, and refuses one the script's list does not name. The lifecycle theorems of `SessionUnitDecodedStateDischarge.lean` (`decrypt_headroom_of_invariant` and the two that
  apply it) have no such application: their premise `Session::invariant self = ok true` needs a value of the session type, whose
  fields are opaque boundary types (`GAP-REGISTER.md`, row `SESSION-CONTRACT-VACUITY`), and `invariant_gives_preconditions` has the same premise.

## Proved (which numeric premises of the refinement theorems a decoded state already gives)

Location: `Translation/DecodedStateDischarge.lean`, `Translation/SessionUnitDecodedStateDischarge.lean`.

`ImportInv.lean` proves that a state `State::from_bytes` returns satisfies the crate's `invariant`, and derives some of the
numeric premises of the refinement theorems from it. These two modules finish that accounting, for the standalone
translations and for the session unit. For each theorem `T` named below, a discharge theorem concludes exactly the
conjunction of the premises of `T` that it names, written in `T`'s own variables, from the decoder invariant and the
premises it takes as arguments. `scripts/check-precondition-witnesses.sh` reads `T`'s type from the built environment and
requires that, requires the theorem to take each premise the script's table calls given and no other premise of `T`, and
requires the table to classify every premise of `T`, so a premise added to `T` or changed in it is refused until the table
and the theorem are changed to match. Every result is conditional on the invariant and the premises it takes; none says a
decoded state refines the model. The gate looks only at the premise names the table lists, so a premise added under a new name to a
discharge theorem is refused only where the theorem has an `*_at_witness` application (the previous section); the three lifecycle
theorems and the two `epoch_family` theorems have no table row and no application.

The 23 theorems named below are pinned with `#guard_msgs in #print axioms`. 16 list only `propext`, `Classical.choice` and
`Quot.sound`. Seven list more: the four Braid discharge theorems add the opaque erasure and KEM types their statements mention
(`Decoder`, `Encoder`, `EncapsState`, `IncrementalKeyPair`); `decrypt_headroom_of_invariant` adds 18 opaque constants of the session
unit's KEM, DH and boundary layers; and `decrypt_ratchet_no_panic_of_invariant` and `decrypt_no_panic_of_invariant` add 50,
among them `hkdf_sha256`, `hmac_sha256`, `zeroize` operations, `Vec` and `Option` operations and the AEAD boundary. No pin lists a
compiler-trust axiom. The pin list is `REQUIRED_PINS` in `scripts/attest.py`.

The result that was not in this ledger is for the sparse ratchet. `SpqrT3.receive_refines` takes `hroom`, `hskiproom` and `hone`,
which `ImportInv.lean` derives from the invariant, and five premises that were recorded as open: `hepoch`, `hcb`, `hsb`,
`hnewb` and `hcounter`. `hcb` and `hsb` (every chain epoch, and every skipped key's epoch, plus `EPOCHS_KEPT` is at most
`u64::MAX`) follow from the invariant together with `hepoch` (`epoch + 1 < u64::MAX`), so the premises that stay with the
caller are three: `hepoch`, `hnewb` (the epochs of the keys an operation adds) and `hcounter` (every chain's counter is below
`u64::MAX`). The invariant alone still does not give `hcb`: the state at `epoch = u64::MAX - 1` with a chain at that epoch
passes `invariant` and fails `hcb`, and it fails `hepoch` too. The same holds for `send_refines`, `advance_refines`,
`maybe_advance_refines` (`hroom`, `hcb`, `hsb` follow from the invariant and `hepoch`) and `clear_old_epochs_refines`
(`hcb` and `hsb`, from the invariant and `epoch + 1 < u64::MAX`, a bound that theorem does not itself state). `hepoch` is not discharged: it excludes one honest value, and that value is an ordinary state.

- `spqr_epoch_family`, `session_unit_spqr_epoch_family`: given the sparse ratchet's decoder invariant and `epoch + 1 < u64::MAX`,
  every chain epoch and every skipped key's epoch plus `EPOCHS_KEPT` is at most `u64::MAX`.
- `spqr_receive_premises`, `session_unit_spqr_receive_premises`: `hroom`, `hcb`, `hsb`, `hskiproom` and `hone` of
  `SpqrT3.receive_refines` follow from the invariant, `hrel` and `hepoch`. Caller: `hepoch`, `hnewb`, `hcounter`.
- `spqr_send_premises`, `session_unit_spqr_send_premises`, `spqr_advance_premises`, `session_unit_spqr_advance_premises`,
  `spqr_maybe_advance_premises`, `session_unit_spqr_maybe_advance_premises`: `hroom`, `hcb` and `hsb` of `send_refines`,
  `advance_refines` and `maybe_advance_refines` follow from the invariant and `hepoch`. Caller: `hrel`, `hepoch`, `hnewb`
  and, for `send_refines`, `hcounter`.
- `spqr_clear_old_epochs_premises`, `session_unit_spqr_clear_old_epochs_premises`: `hcb` and `hsb` of
  `clear_old_epochs_refines` follow from the invariant and `epoch + 1 < u64::MAX`.
- `ratchet_receive_premises`, `session_unit_ratchet_receive_premises`: `hone` and `hs` of the classical `receive_refines` follow from the
  invariant and `hR`. `hroom` (`events + 1 < u32::MAX`) does not: the parked clock passes `invariant`.
- `braid_receive_premises`, `braid_step_receive_premises`, `session_unit_braid_receive_premises`,
  `session_unit_braid_step_receive_premises`: `ct1_bounded` (and on the session unit `decoders_bounded`) follows from the Braid's
  `Inv`; the `epoch + 1 < u64::MAX` premise does not, and is not claimed. The Braid's `Inv` is the partial mirror
  `ImportInv.lean` describes. The standalone `Braid.Inv` has that one field, so for the standalone translations
  `braid_receive_premises` is the projection of its own hypothesis; the substantive step is `Braid.from_bytes_establishes_inv`,
  which takes `Ct1LenTotal`.
- `triple_receive_premises`, `triple_send_premises`: on the session unit, the Triple's composed refinements
  (`receive_refines_discharged`, `send_refines_discharged`) take the premises of both inner ratchets stated about the model state. The
  receive theorem's `hone`, `hs`, `hroom`, `hcb`, `hsb`, `hskiproom` and `hone2` follow from the two inner invariants, `hrel` and `hepoch`.
  `hevents` is a premise of the target that stays with the caller; it is an argument of the discharge theorem so that the table matches,
  and no conclusion uses it. The send theorem's `hroom`, `hcb` and `hsb` follow from the sparse invariant, `hrel` and `hepoch`. What stays with the caller
  is `hevents`, `hepoch`, `hnewb` and `hcounter` (receive) and `hepoch`, `hnewb` and `hcounter` (send), and `hheader`, which relates
  the header to its model header. Proved for the session unit's copy only: the three-leaf unit has no decoder-invariant module.
- `decrypt_headroom_of_invariant`, `decrypt_ratchet_no_panic_of_invariant`, `decrypt_no_panic_of_invariant`: a session that passes
  `Session::invariant` meets `DecryptRatchetHeadroom` once `Ct1LenTotal` and `identity_ad.length + 106 ≤ usize::MAX` hold, and the two lifecycle
  panic-freedom theorems apply with it. `invariant_gives_preconditions` derived the record without the associated-data bound and no
  theorem used it; this is the connection. The theorems are conditional on `DecryptRatchetContracts` exactly as the ones they apply are.

## Proved (the numeric bounds against the caps they are compared with, at both platform widths)

Location: `Translation/NumericBoundary.lean`, `Translation/NumericBoundaryLeaf.lean`, `Translation/NumericBoundaryTriple.lean`, `Translation/NumericBoundarySession.lean`, `Translation/NumericShapeWitness.lean`.

Every numeric bound that depends on a platform width or on a ceiling is written against `usize::MAX`, `u32::MAX`, `u64::MAX` or a
fixed cap of the code. Eleven of the 61 shapes below compare two lengths or counters with each other and mention none of these.
Of these only `usize::MAX` depends on
the platform, and Lean knows of it that it is `2^32 - 1` or `2^64 - 1`; each statement below is proved by a case
split on that, so it holds at both widths, and a bound that held at 64 bits and not at 32 (the defect of 2026-09-10) would fail in
the 32-bit case. These are statements about arithmetic and about the translations' constants. They are not statements that a
real run reaches a size, or that the Rust source has the constant the translation evaluates.

- `both_widths`: `Usize.max` is `2^32 - 1` or `2^64 - 1`.
- `classical_store_cap_fits`, `classical_skip_cap_fits`, `spqr_chain_cap_fits`, `spqr_skip_cap_fits`, `ratchet_codec_cap_fits`,
  `spqr_codec_cap_fits`, `erasure_cap_fits`: the room bounds the theorems take hold for every size the code's caps allow
  (a store of up to 2000 keys, at most two chains, an erasure decoder of up to 65536 chunks), at both widths.
- `erasure_room_exact_at_32`: at 32 bits `32 * needed < usize::MAX` is exactly `needed ≤ 2^27 - 1`, so the bound is not slack.
- `clock_ceiling_excludes_only_parked`, `epoch_ceiling_excludes_only_top`: `events + 1 < u32::MAX` fails, among the values
  the decoder's invariant allows, only at `u32::MAX - 1`, and `epoch + 1 < u64::MAX` only at `u64::MAX - 1`. These are the two
  ceilings the invariant leaves open on the clock and the epoch, and each excludes exactly one value among those the decoder's
  invariant allows. `hnewb` and `hcounter` have no such theorem.
- `ratchet_constants`, `spqr_constants`, `erasure_constants`, `protobuf_constants`, `code_matches_model`, `max_events_is_parked`,
  `clock_ceiling_summary`: in the standalone translations, the constants the bounds mention have the values the
  arithmetic uses, and the ratchet's and the sparse ratchet's equal the model's copies (the erasure and protobuf constants are
  evaluated and compared with nothing). The clock premise of `T3.receive_refines` is satisfiable, is failed by the
  parked clock, and by no other value the decoder's invariant allows (`PreconditionShapes.lean`'s two theorems about it are the
  summary's first two conjuncts).
- `unit_ratchet_constants`, `unit_spqr_constants`, `unit_code_matches_model`, `session_unit_ratchet_constants`,
  `session_unit_spqr_constants`, `session_unit_erasure_constants`, `session_unit_code_matches_model`: the same on the
  three-leaf unit and the session unit, which cannot share an environment with the standalone translations.
- `usize_max_cases`, `every_shape_is_satisfiable`: as enumerated once from the built environment, 61 shapes of numeric premise
  occur (`S01` to `S61` in the module: a comparison between sums and products of lengths, scalars and model numbers, a constant
  and an operator). The enumeration is not complete: hypotheses of the codec theorems such as `pos + 41 ≤ usize::MAX` and
  `len + 48 ≤ usize::MAX` have no shape here, and the script that made it is not in this tree, so nothing checks that the list is
  complete or stays complete. Each shape is satisfiable at both widths. For 54 of the 61 the first atom is at the largest value
  the shape admits with the other atoms as chosen, and nothing larger meets the shape with the other atoms held. S10 uses `0` for
  its first atom, S32, S33 and S41 prove only existence, and S45, S47 and S48 are over unbounded counters, so their witnesses are
  not at a bound (S48's second atom is a length with no `≤ um` bound, so its witness is above `usize::MAX` at both widths). The
  aggregate theorem names every shape theorem so that deleting one is an error. The shape theorems are about shapes and not about
  theorems: nothing in the tree joins a shape to the premises that have it, so a premise added to a theorem with a shape outside
  the 61 is not noticed there. The statement of each shape theorem and of the two theorems at the end is held by a
  `#guard_msgs in #check` pin in the module, so a changed statement stops the build until its pin is changed too;
  `attest.py` requires each of these pins to exist (`REQUIRED_STATEMENT_PINS`) and does not read what a pin says, so a
  statement changed together with its pin's expected message is accepted. The join to the central
  theorems is the witness section above.

The 27 theorems of the five bound modules are pinned with `#guard_msgs in #print axioms`; each lists only `propext`,
`Classical.choice` and `Quot.sound`, or fewer of them. No pin lists a compiler-trust axiom.

## Proved (hypotheses about translated functions in the leaf crates and the three-leaf unit, from named laws, and the decoder acceptance witnesses)

Location: `Translation/SatisfiabilitySpqrLaws.lean`, `Translation/SatisfiabilityRatchetLaws.lean`, `Translation/SatisfiabilityBraidZeroize.lean`, `Translation/UnitSatisfiabilityTripleLaws.lean`, `Translation/SpqrFromBytesWitness.lean`, `Translation/BraidFromBytesWitness.lean`, `Translation/SessionUnitBraidFromBytesWitness.lean`, `Translation/RatchetDecodedWitness.lean`.

Most boundary hypotheses of the leaf and three-leaf-unit theorems are statements about opaque
constants, and `Translation/Satisfiability.lean` and `Translation/UnitSatisfiabilityTriple.lean`
witness them. Some are statements about functions the translation defines, with a body: the two
removal helpers (`T1.RemoveSkippedAtTotal`, `SpqrT1.RemoveSkippedAtTotal` and the unit's copies), the
three key derivations, `SpqrT1.VecRetainTotal` with its three loop contracts, and the agreements
`SpqrT3.RemoveSkippedAtAgrees` and `SpqrT3.VecRetainAgrees` (and the unit's copies). A model of the
opaque constants cannot change what such a statement says. The witnesses those files hold for the
removal helpers are bridged by `Iff.rfl` to a shape applied to the defined function, which is
satisfiable for any function and says nothing about the body; the others had none, except `SpqrT1.KdfRkTotal`
and `KdfCkTotal`, which `Satisfiability.lean` derives from the witnessed HKDF agreement and the two round trips.
`SpqrT3.set_chains_refines` and `clear_old_epochs_refines`, and their copies on the unit, are
`VecRetainAgrees` applied to its arguments. Before these results they were an assumed agreement of
two translated loops with the model and not a proof of it, and the sparse refinements of `advance`,
`maybe_advance`, `skip_message_keys`, `send` and `receive` rest on it. The results below show each of
these hypotheses follows, by stepping through the translated code, from named laws about the opaque
constants its body reaches. They are results about hypotheses and not about the product: each is
conditional on exactly the laws its statement names, no theorem statement is changed, and the
theorems that take the hypotheses still take them.

The laws are assumptions about standard-library and `zeroize` operations, tested against the real
functions only by reading, and nothing here shows that the real functions satisfy them: `Vec::pop`
of a non-empty vector returns the vector without its last element (`LawPop`), `Option::as_mut`
returns (`LawAsMut`), `Vec::capacity` returns (`LawCapacity`), the `Vec` `Zeroize` implementation
returns (`LawVecZeroize` of these modules, stated for every `Zeroize` record, which is stronger than the crate, as below;
the Session unit's `UnitSatisfiabilityRatchet.LawVecZeroize` is stated at that unit's three instances), the blanket `Zeroize` implementation returns at `u32` (`LawBlanketU32`,
classical removal helper), the array `Zeroize` implementation returns (the existing hypotheses
`SpqrT1.ZeroizeTotal` and `UnitSpqrT1.ZeroizeTotal`, and `ArrZU8` at the byte instance for the
classical leaf), the HKDF returns for output lengths up to 8160 bytes (`LawHkdf`), and the
`Zeroizing` wrapper reads back what it wraps at 96 and 64 bytes (`LawZeroizing`). The sparse T3
theorems already take the HKDF agreement and the two round trips, which give `LawHkdf` and `LawZeroizing`
at the two widths, and
`LawCapacity` and `LawVecZeroize` are conjuncts of `VecRetainTotal`, which they take too, so beyond
the hypotheses those theorems take the sparse results add `LawPop` and `LawAsMut` (and
`LawBlanketU32` for the classical removal helper), which no hypothesis states. The proofs are generic
in the platform width.

- `SatisfiabilitySpqrLaws.kdfRkTotal`, `SatisfiabilitySpqrLaws.kdfCkTotal`,
  `SatisfiabilitySpqrLaws.spqrRemoveSkippedAtTotal`, `SatisfiabilitySpqrLaws.setChainsLoopTotal`,
  `SatisfiabilitySpqrLaws.clearChainsLoop0Total`, `SatisfiabilitySpqrLaws.clearSkippedLoopTotal`,
  `SatisfiabilitySpqrLaws.vecRetainTotal`, `SatisfiabilitySpqrLaws.defined_fields_hold`: the leaf
  sparse ratchet's `SpqrT1.KdfRkTotal`, `KdfCkTotal`, `RemoveSkippedAtTotal`, the three loop
  contracts inside `VecRetainTotal`, and `VecRetainTotal` itself follow from the laws; the last result
  gives the four hypotheses together from the structure `Laws`.
- `UnitSatisfiabilityTripleLaws.kdfRkTotal`, `UnitSatisfiabilityTripleLaws.kdfCkTotal`,
  `UnitSatisfiabilityTripleLaws.kdfInitTotal`, `UnitSatisfiabilityTripleLaws.spqrRemoveSkippedAtTotal`,
  `UnitSatisfiabilityTripleLaws.ratchetRemoveSkippedAtTotal`,
  `UnitSatisfiabilityTripleLaws.setChainsLoopTotal`, `UnitSatisfiabilityTripleLaws.clearChainsLoop0Total`,
  `UnitSatisfiabilityTripleLaws.clearSkippedLoopTotal`, `UnitSatisfiabilityTripleLaws.vecRetainTotal`,
  `UnitSatisfiabilityTripleLaws.defined_fields_hold`: the same on the three-leaf unit, where the two
  ratchets share the constants, with `UnitTripleT1.KdfInitTotal` and `UnitT1.RemoveSkippedAtTotal` added;
  the last result gives the six hypotheses together from the nine laws of its `Laws`.
- `SatisfiabilitySpqrLaws.removeSkippedAtAgrees`, `SatisfiabilitySpqrLaws.setChainsAgrees`,
  `SatisfiabilitySpqrLaws.clearOldEpochsAgrees`, `SatisfiabilitySpqrLaws.vecRetainAgreesOfLaws`,
  `SatisfiabilitySpqrLaws.vecRetainAgrees`: `SpqrT3.RemoveSkippedAtAgrees` and `SpqrT3.VecRetainAgrees`
  hold, as statements about the translated `remove_skipped_at`, `set_chains` and `clear_old_epochs` for
  all inputs the theorems' own premises allow (a chain table at the largest length they admit,
  duplicate epochs, `current` at `u64::MAX` and empty containers included). The retain loops are proved to keep exactly the entries their guard names, in
  order, and to leave the other fields alone. `vecRetainAgreesOfLaws` takes the five laws one by one
  (`LawCapacity`, `LawVecZeroize`, the array wipe, `LawAsMut`, `LawPop`), so its pin lists no HKDF
  and no `Zeroizing` constant; `vecRetainAgrees` takes the bundle `Laws`, whose other fields add those
  two to its pin although the proof does not use them. The array wipe is applied at
  the byte instance on 32-byte arrays only.
- `UnitSatisfiabilityTripleLaws.removeSkippedAtAgrees`, `UnitSatisfiabilityTripleLaws.setChainsAgrees`,
  `UnitSatisfiabilityTripleLaws.clearOldEpochsAgrees`, `UnitSatisfiabilityTripleLaws.vecRetainAgreesOfLaws`,
  `UnitSatisfiabilityTripleLaws.vecRetainAgrees`: the same on the unit, for `UnitSpqrT3.RemoveSkippedAtAgrees`
  and `UnitSpqrT3.VecRetainAgrees`, which the Triple's discharged theorems take.
- `SatisfiabilitySpqrLaws.defined_hyps_from_axiom_hyps`,
  `UnitSatisfiabilityTripleLaws.defined_hyps_from_axiom_hyps`: the defined-function T1 hypotheses follow
  from the hypotheses the T3 theorems already take (`ZeroizeTotal`, `SpqrHkdfAgrees`, the two round
  trips) and the four laws that are not among them (five on the unit), so the defined-function
  hypotheses add no assumption about the HKDF or the wrapper.
- `SatisfiabilitySpqrLaws.LawPop_is`, `SatisfiabilitySpqrLaws.LawAsMut_is`,
  `SatisfiabilitySpqrLaws.LawCapacity_is`, `SatisfiabilitySpqrLaws.LawVecZeroize_is`,
  `SatisfiabilitySpqrLaws.LawHkdf_is`, `SatisfiabilitySpqrLaws.hkdf_total_satisfiable`,
  `SatisfiabilitySpqrLaws.laws_jointly_satisfiable`, `SatisfiabilitySpqrLaws.laws_of_shape`: five of the laws are the statement
  about the real constant (`Iff.rfl` against its shape, so the build compares them), and the array wipe and the
  wrapper reach `Laws` through `laws_of_shape`, which is an implication; `LawsShape` bundles the eight laws over arbitrary
  functions of the constants' types, with the array wipe, the HKDF and the wrapper in their general form,
  which implies the instances `Laws` uses; one assignment satisfies all of it at once; and if the real
  constants satisfied `LawsShape` then `Laws` would hold. So, as statements about arbitrary functions of the
  constants' types, the laws do not conflict with one another.
- `UnitSatisfiabilityTripleLaws.LawPop_is`, `UnitSatisfiabilityTripleLaws.LawAsMut_is`,
  `UnitSatisfiabilityTripleLaws.LawCapacity_is`, `UnitSatisfiabilityTripleLaws.LawVecZeroize_is`,
  `UnitSatisfiabilityTripleLaws.LawBlanketU32_is`, `UnitSatisfiabilityTripleLaws.LawHkdf_is`,
  `UnitSatisfiabilityTripleLaws.hkdf_total_satisfiable`,
  `UnitSatisfiabilityTripleLaws.laws_jointly_satisfiable`, `UnitSatisfiabilityTripleLaws.laws_of_shape`:
  the same for the nine laws of the unit. That the laws hold together with the other hypotheses of a
  particular theorem is argued from the constants the statements mention, which are different constants
  (the pop, as-mut, capacity and wipe operations against the HKDF and the wrapper), and is not a Lean
  theorem.
- `SatisfiabilitySpqrLaws.pop_satisfiable`, `SatisfiabilitySpqrLaws.as_mut_satisfiable`,
  `SatisfiabilitySpqrLaws.capacity_satisfiable`, `SatisfiabilitySpqrLaws.vec_zeroize_satisfiable`,
  `UnitSatisfiabilityTripleLaws.pop_satisfiable`, `UnitSatisfiabilityTripleLaws.as_mut_satisfiable`,
  `UnitSatisfiabilityTripleLaws.capacity_satisfiable`, `UnitSatisfiabilityTripleLaws.vec_zeroize_satisfiable`,
  `UnitSatisfiabilityTripleLaws.blanket_satisfiable`: each law's shape is satisfied by some function.
  `check-hypothesis-witnesses.sh` reads them as the existence theorems of the bridges. `as_mut_satisfiable`
  depends on no axiom, so its `#print axioms` output has no list to pin; it has a pin on its statement.
- `SatisfiabilityRatchetLaws.ratchetRemoveSkippedAtTotal`, `SatisfiabilityRatchetLaws.LawPop_is`,
  `SatisfiabilityRatchetLaws.LawBlanketU32_is`, `SatisfiabilityRatchetLaws.ArrZU8_is`,
  `SatisfiabilityRatchetLaws.pop_satisfiable`, `SatisfiabilityRatchetLaws.blanket_satisfiable`,
  `SatisfiabilityRatchetLaws.arrZU8_satisfiable`, `SatisfiabilityRatchetLaws.ratchet_laws_jointly_satisfiable`:
  the leaf classical ratchet's `T1.RemoveSkippedAtTotal`, which `Satisfiability.lean` witnesses only
  through a void bridge, follows from `LawPop`, `LawBlanketU32` and `ArrZU8` (the array wipe returns at
  the byte instance, at every length). Each law is the shape applied to the real constant and is
  satisfiable, and one assignment satisfies the three, which are on three different constants. The
  classical crate's `pop` is a different constant from the sparse crate's, so the law is stated again
  for it.
- `SatisfiabilityRatchetLaws.RatchetCodec_ZeroizingVecTotal_is`,
  `SatisfiabilityRatchetLaws.zeroizing_vec_satisfiable`, `SatisfiabilitySpqrLaws.SpqrCodec_ZeroizingVecTotal_is`,
  `SatisfiabilitySpqrLaws.zeroizing_vec_satisfiable`: `RatchetCodecT1.ZeroizingVecTotal` and
  `SpqrCodecT1.ZeroizingVecTotal`, which had no witness, are each the shape of `Zeroizing::new` at
  `Vec<u8>` and are satisfiable.
- `UnitSatisfiabilityTripleLaws.RoundTrips80_is`, `UnitSatisfiabilityTripleLaws.roundTrips80_satisfiable`,
  `UnitSatisfiabilityTripleLaws.TripleZeroizeTotal_is`, `UnitSatisfiabilityTripleLaws.arrZ32_satisfiable`,
  `UnitSatisfiabilityTripleLaws.arrZ32_of_general`: `UnitT3.ZeroizingRoundTrips80` and
  `UnitTripleT3.ZeroizeTotal`, which `UnitSatisfiabilityTriple.lean` leaves without a witness, are each
  the shape of the real constant and satisfiable, and the scoped `UnitTripleT3.ZeroizeTotal` follows from
  the general `UnitSpqrT1.ZeroizeTotal`.
- `SatisfiabilitySpqrLaws.spqr_zeroizeTotal_conflicts`, `UnitSatisfiabilityTripleLaws.spqrZeroizeTotal_conflicts`,
  `SatisfiabilityBraidZeroize.braid_arrayZeroizeTotal_conflicts`, `SatisfiabilitySpqrLaws.vec_zeroize_conflicts`,
  `UnitSatisfiabilityTripleLaws.vec_zeroize_conflicts`: `SpqrT1.ZeroizeTotal`,
  `UnitSpqrT1.ZeroizeTotal` and `BraidT1.ArrayZeroizeTotal` quantify over every `Zeroize` record
  (`Zeroize U8` for the Braid), including one whose `zeroize` fails, and no `Array::zeroize` that
  propagates the failure of a failing element satisfies them. The `Vec::zeroize` conjunct of
  `SpqrT1.VecRetainTotal` and `UnitSpqrT1.VecRetainTotal`, which `LawVecZeroize` restates, is the same
  kind of statement, and no `Vec::zeroize` that propagates the failure of a failing element satisfies it.
  The real functions do propagate it (`PropagatesFailure` and `PropagatesFailureVec` are assumptions about
  the real functions, tested only by reading), so the four hypotheses are stronger than the crate. They are
  satisfiable (the identity wipe in `Satisfiability.lean` for the sparse and Braid wipes, and in
  `UnitSatisfiabilityTriple.lean` for the unit's), and the proofs apply them only at the `Blanket U8`
  instance, whose element wipe returns, and, for the `Vec` conjunct, at the instances for
  `(u64, Chains)` and `Skipped`. They are **documented and unchanged here**: no theorem statement and no
  hypothesis is altered by this section, and no result in it replaces any of them. The session unit's
  corresponding fields (its two array fields and its `Vec` conjunct) are stated at the instances that unit uses, and
  the same result about their former general forms is in `UnitSatisfiabilityZeroizeScope.lean`.
- `SpqrFromBytesWitness.spqr_from_bytes_accepts_witness`,
  `SpqrFromBytesWitness.spqr_from_bytes_establishes_inv_nonvacuous`: the translated
  `tacenta_spqr::State::from_bytes` accepts a concrete 140-byte string (version 1, an all-zero root key, epoch 0, one
  chains entry at epoch 0 with both chains absent, no skipped keys), and the state it returns satisfies
  `Spqr.Inv`, so `Spqr.from_bytes_establishes_inv` is not vacuous. The pins list the three standard axioms
  only; no hypothesis about an opaque constant is used on the decode path.
- `BraidFromBytesWitness.braid_from_bytes_accepts_witness`,
  `BraidFromBytesWitness.braid_from_bytes_establishes_inv_nonvacuous`,
  `SessionUnitBraidFromBytesWitness.braid_from_bytes_accepts_witness`,
  `SessionUnitBraidFromBytesWitness.braid_from_bytes_establishes_inv_nonvacuous`: the translated
  `tacenta_braid::Braid::from_bytes`, in the standalone leaf and in the complete Session unit, accepts a
  concrete 74-byte string (version 1, state tag 0 (`KeysUnsampled`), epoch 1, a zero authenticator), and
  the state it returns satisfies `Braid.Inv` under the one hypothesis the existing theorem carries
  (`Ct1LenTotal`, which acceptance itself does not use). `Braid.Inv` has one clause, a ciphertext-length
  bound that is `True` outside tags 3, 4, 7, 8 and 9, so on this state it is trivial: the result shows
  that the decoder accepts a string and that the premise of `from_bytes_establishes_inv` is satisfiable,
  and it does not exercise the clause. That state holds no erasure or KEM value, so the
  decode path calls no opaque constant; the pins list `tacenta_erasure.*` and `tacenta_kem.*` constants only
  because those names occur in the definitions of the decoder's other arms and of `Braid.invariant`, which
  the statement mentions. **For the states that hold an erasure or KEM value (tags 1 to 10) no byte string
  is shown accepted**, because their decode runs through the opaque erasure and KEM decoders. Tag 11
  (`Failed`) holds no such value and has no witness either; one would be a two-byte string.
- `RatchetDecodedWitness.ratchet_witness_events`,
  `RatchetDecodedWitness.decoded_receive_refines_premises_satisfiable`: the translated classical decoder
  accepts `witnessBytes` and returns a state whose clock is zero, so the four premises of
  `Ratchet.decoded_receive_refines` that are about the decoded state (`hdec`, `hR`, `hH`,
  `hclock_unparked`) hold together on one state. The theorem's other premises, the HMAC and HKDF
  agreements, the wrapper round trip, `T1.RemoveSkippedAtTotal` and `DerivedKeysModel`, are not part of
  this result.

- `T3.HmacAgrees.total` (in `Translation/T3.lean`), `T3.HkdfAgrees.total` (in `Translation/T3.lean`),
  `BraidT3.BraidHmacAgrees.total` (in `Translation/BraidT3.lean`), `BraidT3.BraidHkdfAgrees.total`
  (in `Translation/BraidT3.lean`), `UnitT3.HmacAgrees.total` (in `Translation/UnitT3.lean`),
  `UnitT3.HkdfAgrees.total` (in `Translation/UnitT3.lean`), `UnitTripleT3.TripleHkdfAgrees.total`
  (in `Translation/UnitTripleT3.lean`): the HMAC and HKDF totality hypotheses of the T1 theorems
  (`HmacTotal`, `HkdfTotal`, `HmacSha256Total`, `HkdfSha256Total` and the unit's copies) follow from the
  agreements the T3 theorems take, so they add no assumption beyond those agreements, which
  `Satisfiability.lean` and `UnitSatisfiabilityTriple.lean` witness. These existing theorems are named
  here because `check-hypothesis-witnesses.sh` accepts a hypothesis as derived only through a derivation
  that the ledger names. That script checks that each closed hypothesis of the claimed T1 and T3 theorems of
  the leaf crates and the three-leaf unit is connected to a bridge to a satisfiable shape, to a derivation
  the ledger names, or to `True`, and that no such theorem takes a closed hypothesis that names no predicate
  or quantifies over a variable only hypotheses mention. It does not show that a connected hypothesis is
  satisfiable (an existence theorem is recognised by its shape, so a weakened one passes unless its
  statement is pinned), that the hypotheses of one theorem hold together, or anything about a
  hypothesis with a free variable that mentions real state. Its mutation controls are run by hand; no
  workflow runs them.

What is not shown. That the real standard-library and `zeroize` functions satisfy the laws. That the
hypotheses that have a free variable (the state relations such as `StateR` and `StateRefines`, and the
numeric bounds) hold together with these hypotheses on any state: this section covers the closed boundary
hypotheses only. That the leaf Braid's erasure and KEM agreements hold of states that carry such
values. That `SessionUnitSpqrT3.VecRetainAgrees` and `SessionUnitSpqrT3.RemoveSkippedAtAgrees` follow from
laws is not in this section, which covers the leaf crates and the three-leaf unit; the section on the Session unit's
sparse agreements shows it, `check-hypothesis-witnesses.sh` does not read the Session unit, and the session unit's
refinement theorems, `SessionUnitTripleT3`'s discharged theorems and the lifecycle contract
`TripleSendRefinementContracts` still take those two as hypotheses. That any of the four over-strong zeroize hypotheses of the leaf
crates and the three-leaf unit (the three array wipes and the `Vec::zeroize` conjunct) is replaced: only the
session unit's fields are stated at the instances that unit uses.

## Evidence, not proof

Runtime evidence: known-answer and self-consistency checks. These are build
gated but rely on `native_decide`'s compiler trust or on a test runner, not on a
kernel proof.

- Interoperability testing under the research boundary is not part of this
  public tree and is not claimed as evidence here.
- Primitive known-answer values: SHA-256 (NIST), HMAC-SHA256 (RFC 4231),
  HKDF-SHA256 (RFC 5869), in both tacenta-model and tacenta-core.
- Ratchet self-consistency: in-order, out-of-order, and bidirectional agreement,
  and the refusal of a message delivered a second time on the chain already
  held (after an in-order receive and after a stored-key receive) with the
  next message still received, in tacenta-model `Model.Ratchet`.
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
fail if the Braid's erasure or KEM hypotheses lose their model,
`scripts/check-precondition-witnesses.sh`, which fails if a numeric-precondition
witness or discharge theorem (`Translation/NumericWitness*.lean`,
`Translation/*DecodedStateDischarge.lean`) no longer states its theorem's own
premises, by reading each theorem's type from the built environment (36 cases hold
that comparison to mutations), and
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
The same audit refuses every first-party declaration whose type or proof value
reaches Lean's `sorryAx`, including when `warn.sorry` is disabled or the
diagnostic is consumed by `#guard_msgs`; this is the semantic check behind the
no-sorry claim rather than a token-pattern workaround.
`scripts/check-lean-constructs.sh`, the textual second line, strips
comments and strings and refuses those keywords wherever they sit on a
line, in every hand-written module including the package roots and
`Vectors.lean`, and refuses a lakefile that sets any Lean option. It also
refuses every elaboration-time construct (`run_cmd`, `#eval`, `elab`,
`macro`, `syntax`, `initialize`, `addDecl`, any reference to the `Lean`
namespace) outside `Model/AxiomAudit.lean`'s own implementation and the
seven `run_cmd _root_.Model.AxiomAudit.run` lines, allow-listed by file path and
exact line content: the audit accepts the compiler-trust axioms by shape
and cannot tell a planted one, added by such code with its name assembled
from string literals, from a real one, so the absence of such code is what
excludes it (`LIMITATIONS.md`, "Trusted, not verified").
`scripts/check-audit-reach.sh` fails if any first-party module, generated
ones included, is outside the seven audit modules' import closure, since
the audit walks only what its invoking module imports, and fails if the
seven do not all run with the same first-party prefixes, since the audit's
waiver for an unmentioned compiler-trust axiom asks whether any first-party
declaration mentions it and only sees the modules in its own environment.
`scripts/check-audit-negatives.sh` plants thirteen declarations: one for each
of the seven kinds the audit refuses, one for each condition a compiler-trust
axiom must meet, and one for the shape the waiver accepts. It fails if the
audit calls any of them wrongly. Its own comment carries the matrix of which
case goes red when which rule is deleted, because a test that passes on a
broken rule is worth nothing.
`no-sorry.sh` then replays every first-party module through the kernel
with `leanchecker`, which is the check against a declaration added with
kernel checking turned off.

The translation itself is regenerated in CI only by the private verification
workflow, using the pinned Aeneas release
`nightly-2026.07.22-b1214ca` (commit `b1214ca0a024e8121f41fe2b2ed15e26af02373b`),
whose linux-x86_64 archive `aeneas-linux-x86_64.tar.gz` has SHA-256
`bc26c30daf92679b57c264c630710096bd9d4428e28795fe0638afdb0c2df65f`; that
workflow checks that digest before extracting, and fails if the committed
`Translation/Tacenta*.lean` differ from what that build produces. The digest
is stated here so that a reader reproducing the translation elsewhere can
check they hold the same binaries, not merely the same tag. The release page
lists archives for Linux and macOS on two architectures each. The digest above
is the Linux x86_64 one, which the verification workflow checks; the macOS arm64
archive used for the regeneration recorded under `HL-R1-SPARSE-TRANSLATION` in
`GAP-REGISTER.md` is not covered by that check. `scripts/regenerate-in-container.sh`
checks the Linux x86_64 digest too, and runs the regeneration by hand in a
container; `REPRODUCING.md` records one run of it.

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
do by hand (`REPRODUCING.md`; `scripts/regenerate-in-container.sh` does it in a
container). `attest.py --check` also checks the ledger
itself by name: every theorem a claim bullet names must exist, fully
qualified, in the file its section's `Location:` line names, every
`Location:` path must exist, and every pinned theorem must be claimed.
