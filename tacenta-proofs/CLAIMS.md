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
  (`Translation/UnitLifecycleT3.lean`; not accepted as claims here; only the Triple receive
  evidence in `UnitLifecycleInitialDispatch.lean` is derived from a leaf refinement
  that takes no contract record; the Braid receive evidence there takes
  `BraidReceiveContracts`, whose inhabitation is shown only in the sense of `LIMITATIONS.md`; seventeen of
  the lemmas are affected by a hypothesis or evidence record that is shown false or empty under stated conditions,
  sixteen of them vacuous as stated;
  see also `GAP-REGISTER.md`, rows `E2E-04`, `SESSION-CONTRACT-VACUITY` and `DISPATCH-EVIDENCE-VACUITY`). No theorem says what the two functions
  return as a whole, on every branch, against the model. What is proved
  outright lies underneath them, in the ratchet, the sparse post-quantum
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
  operation's own precondition, and the build checks that each `Vec`-family
  one is satisfiable.** `VecAppendTotal`/`VecAppendAgrees` carry a length
  guard (Aeneas's `Vec` has no room for two full vectors); the classical
  ratchet's `VecRemoveTotal`/`VecRemoveAgrees` and the sparse ratchet's
  `RemoveSkippedAtTotal`/`RemoveSkippedAtAgrees` carry the index guard
  `i.val < v.val.length →`, discharged in each proof from the loop guard the
  source checks first (the guard also removed the
  `[Inhabited]` bound the unguarded statements needed: stated for every
  index and every element type, including the empty one, they would imply
  `False`); every width-polymorphic HKDF hypothesis carries RFC 5869's `N.val ≤ 8160` (`SessionT3.HkdfAgrees` is fixed at 32 bytes and needs none), the
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
  refinements about the erasure coder, are in the same position: statements about translated
  definitions, which no theorem shows can be met. The sparse ratchet's
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
  counter's exhaustion (`ChainExhausted`) is refused by the model too, at
  `ns = u32::MAX`, but the statement does not relate the two refusals. **Modulo `HmacAgrees`**; pinned
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
  64- and 80-byte literals), `ZeroizingRoundTrips`, `VecRemoveTotal`
  (stated under `i.val < v.val.length`, discharged from each scan's own loop
  guard) and `DerivedKeysModel` (the T1 section says what it is), the `hone`
  at-most-one hypothesis named in "what is not proved", a store-size
  precondition (`hs`) and a step of room in the expiry clock
  (`hroom : events + 1 < U32.max`, one step below the `u32` ceiling, a premise
  from when `age_store` clamped the clock at `MAX_EVENTS = u32::MAX - 1` and
  the model's clock did not stop; it now stops there too); it says nothing about the failure branches. Pinned base: the kernel's three axioms and
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
- `send_reports`: the epoch a `Send` reports is the one before the state's, so
  it names the last epoch both parties are known to hold rather than the one
  being negotiated.
- `receive_reports`: and the epoch a `Receive` reports is the one before the
  state it lands in, on every branch. A receive that fails lands in `Failed`,
  whose epoch is 0, and reports 0, as mlkem-braid.md's Failure section says.
- `receive_epoch_lt`: a receive from a state whose epoch is below `u64::MAX`
  (`u64Max`) leaves the Braid below it. A send never changes the epoch
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
  and its entry point cannot panic. This is the one an attacker's header,
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
  (the two KDF calls, `Vec::remove`, and the `zeroize` wrapper's constructor,
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

Each of these four is pinned in `UnitPins.lean`.

The two discharged theorems state what the bundle-taking theorems in the same
file state, and those are claimed as well. They carry two scopings worth reading
literally.

- `Tacenta.UnitTripleT3.send_refines`: the composed `send` refines
  `Model.Triple.send`, given the two bundles. It states the success case and a
  failure case, and the failure case is not symmetric: it holds for every
  post-quantum error and, on the classical side, only for `NoSendingChain`,
  because `T3.lean`'s own `send_refines` proves the model-failure correspondence
  for that error and no other -- `ChainExhausted`, the real `u32` send counter's
  exhaustion, which the model now refuses too but which that theorem does not
  relate to the model's `none`.
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
`RemoveSkippedAtAgrees`, `UnitSpqrT1.ZeroizeTotal` and
`UnitSpqrT1.OptionCloneTotal`.
`UnitSatisfiabilityTriple.lean` witnesses all eleven, jointly where two constrain
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
  declarations and does not cover them. No theorem shows that they can be met, and they are not
  among the records of `SESSION-CONTRACT-VACUITY`.
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
  proved outright rather than assumed, since `finish_encaps` and `mac_eq` are
  fully translated Rust (no opaque call in the ones that matter for value,
  only in the KEM/erasure primitives they call), and the epoch fact is a
  finite case split over the model alone.
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
build and by the axiom pin, and **no gate requires a statement pin or a definition pin to exist**: deleting
one fails nothing, and weakening a result whose statement has no pin changes nothing a gate reads. The
results whose statements are held only by the build and the axiom pin, with no statement pin, are
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
- **`VecRetainAgrees` and `RemoveSkippedAtAgrees`:** each states what the
  operation returns, not only that it returns, and each is strictly stronger
  than its `SpqrT1.lean` namesake, so neither older hypothesis is separately
  assumed here. `RemoveSkippedAtAgrees` is stated under the index guard
  `i.val < v.val.length`, and says the custom wipe-before-pop helper returns
  the indexed key and the vector with that index erased.
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
against the repaired record and are not claims. Seventeen theorems of the two modules, ten of them encrypt-side
lemmas of `UnitLifecycleT3.lean`, are affected for a different reason, which the section "Proved (a negative
result: five evidence hypotheses and records of the lifecycle dispatch layer are false or empty)" below gives. The standalone Braid theorems in `BraidT1.lean`
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
- `vecRetainTotal`: `VecRetainTotal` follows from `Vec::capacity` and `Vec::zeroize` returning (its own
  first two conjuncts), `ZeroizeTotal`, `LawAsMut` and `LawPop`.
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
`Zeroize`, the HKDF, the `Zeroizing` wrapper). None depends on a compiler-trust axiom. The proofs are
statements about the translation: `Vec::with_capacity` never fails in the Aeneas model, where the
real function panics for an absurd capacity, so a result that reaches it (`Encoder::new`,
`Decoder::message`) holds of the translated code and says nothing about a request for more memory
than the machine has.

## Proved (one interpretation of the unit's opaque constants, and the four records from it)

Location: `Translation/UnitSatisfiabilityJoint.lean`, `Translation/UnitSatisfiabilityRecords.lean`, `Translation/UnitSatisfiabilitySession.lean`.

`UnitSatisfiabilityJoint.lean` interprets 48 of the opaque axioms of `TacentaSessionUnit.lean` that the
four contract records reach (6 types, 4 constants, 38 functions; of the unit's other 40 axioms, 39 are reached
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
  `Zeroize` and the array, vector and tuple `Zeroize` are modelled as the identity, which is not what they do; only the
  returning of the blanket one is used by a law, and the array and vector ones are the three over-strong fields.
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
deleting one fails it. The pins of the results about `Interp.real` and the records list the 48 interpreted
constants and the error type inside `RngCore`; the pins of the results about the model list the three standard
axioms and that error type. None depends on a compiler-trust axiom. The pins hold axiom lists, not statements.
The statements of `axiom_base_satisfiable`, `axiom_base_satisfiable_for_total_rng`, `records_of_axiom_base` and
`vec_pop_satisfiable` (in `UnitSatisfiabilitySession.lean`) are pinned by `#guard_msgs in #check`, and `attest.py` requires
each of those four pins to exist and to compare the printed statement (`REQUIRED_STATEMENT_PINS`); no other statement in these modules is held, so a weaker statement that
keeps its axiom list is not refused. What the pins do not hold is the classification itself, which fields are axiom-level and which are about
translated functions: the audit text in `tacenta-proofs/scripts/check-session-satisfiability-negatives.sh`
checks it against the elaborated environment, and it runs there and not in `lake build`, because `check-lean-constructs.sh` refuses elaboration-time code in the translation
package.

## Proved (evidence about three fields that quantify over every Zeroize record)

Location: `Translation/UnitSatisfiabilityZeroizeScope.lean`.

`SessionUnitSpqrT1.ZeroizeTotal`, `SessionUnitBraidT1.ArrayZeroizeTotal` and the `Vec::zeroize` conjunct of
`SessionUnitSpqrT1.VecRetainTotal` say that `Array::zeroize` and `Vec::zeroize` return for every instance
record `inst : Zeroize Z`, including one whose `zeroize` fails. The joint model satisfies them, so they do not make
a record empty. The real functions call `inst.zeroize` on each element, so for a failing instance the statement is false of the
crate: the fields are stronger than the code supports. This module changes no record and no theorem.

- `zeroize_failure_propagation_conflicts`: no interpretation satisfies `ZeroizeTotal` and also lets
  `Array::zeroize` propagate the failure of a failing instance, which is what the real function does.
- `faithful_propagates`, `faithful_refutes_unscoped`, `faithful_satisfies_rest`: a second interpretation
  implements `Array::zeroize` and `Vec::zeroize` as the crate does (zeroize each element in order, fail if one
  fails; `Vec::zeroize` leaves an empty vector). It propagates the failure, falsifies the unscoped field, and
  satisfies the scoped replacements together with every other shape, both model classes and `StdLaws`.
- `arrayZeroizeScoped_of_total`, `ArrayZeroizeU8Total_of_spqr`, `ArrayZeroizeU8Total_of_braid`: the scoped
  statements (the same, with the premise that the instance's `zeroize` returns, and the form at the one
  instance the code uses, `Blanket U8`) follow from the fields as they stand, so replacing the fields by them
  weakens a hypothesis.
- `VecZeroizeChainsTotal_of_vecRetain`, `VecZeroizeSkippedTotal_of_vecRetain`: the `Vec::zeroize` conjunct implies its
  scoped forms at the two instances the proofs apply it at, the chain table and the skipped-key store. A
  replacement needs both: with the chain table alone, `skip_message_keys_no_panic` stops building (measured
  in a copy; `LIMITATIONS.md`). That the scoped forms hold in the second interpretation is not shown, because
  they mention the translated `Chains::zeroize` and `Skipped::zeroize`, whose totality there is not proved.

## Proved (a negative result: five evidence hypotheses and records of the lifecycle dispatch layer are false or empty)

Location: `Translation/DispatchEvidenceVacuity.lean`.

`UnitLifecycleT3.lean` and `UnitLifecycleInitialDispatch.lean` state refinement lemmas for the
eight-leaf session unit's `encrypt` and `decrypt` as conditional on hypotheses and on evidence
records. These results are about those hypotheses and records, not about the product. They show
that five of them are false or empty under the conditions stated in the bullets below, which
affects seventeen theorem statements of the two modules: sixteen are vacuous as stated, and the
seventeenth has no term of its evidence record in the cases the third bullet gives
(`GAP-REGISTER.md`, row `DISPATCH-EVIDENCE-VACUITY`, lists them and the conditions). The last bullet
is a sixth point and not a refutation. None of the seventeen is listed in this ledger or carries an
axiom pin, so no existing entry changes.

- `same_ephemeral_agreement_empty`, `initialSameEphemeralEvidence_false`: the translated
  `same_ephemeral_agreement` returns `false` on two empty byte strings, because `decode_ec`
  refuses a string whose length is not 33, so `InitialSameEphemeralEvidence`, which asks for `true`
  on every pair of equal byte strings, is false for every `dh`, `oracle`, `real` and `model`. The
  proof uses no hypothesis and no law. Six theorems and three of the eleven constructors of
  `SessionDecryptEvidence` (`initialAccepted`, `initialTerminal`, `initialMalformed`) take it.
- `codewordViewOf_false`, `codewordViewOf_false_of_encoderNewTotal`: if `Encoder::new` returns on
  two messages of one length `n` of at least 33 bytes that agree on their first 32 bytes and differ
  at byte 32, no view satisfies `CodewordViewOf`, because both messages have the same codeword at
  index 0 and the `receive` clause asks the view to name the one source it came from. The first
  theorem takes the two returns; the second takes `EncoderNewTotal`, the field `encoderNew` of the
  encrypt contract records, which `UnitSatisfiabilityErasure.encoderNew_iff` shows equivalent to
  the law that `usize::div_ceil` returns at divisor 32, and uses `n = 33`. Ten theorems take
  `CodewordViewOf`, and none of them takes `EncoderNewTotal`, so for them the result rests on that
  law, which no theorem proves of the opaque constant.
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
- `oracleOf_kem_oracle_never_refuses`, `oracleOf_kem_call_never_errs`: `OracleOf.kemEncapsulateSuccess`
  makes the model's KEM oracle accept every public key at every draw that a trace has, and the
  translated `encapsulate` never return `Err` while the trace has a draw. This is not a refutation,
  because `encapsulate` is an opaque constant: the shipped function returns `Err` on a key of the
  wrong length (tested by `malformed_inputs_are_rejected`) and on a key that fails
  `validate_public_key` (read from `tacenta-core/boundary/src/kem.rs`; `GAP-REGISTER.md`, row
  `E2E-04`).

No step of these proofs case-splits on the width of `usize`, and the only facts they use about
`Usize.max` are the bounds Aeneas proves for the platform constant. `System.Platform.numBits` is an
opaque constant of the kernel whose value is 32 or 64, so a proof that does not choose between the
two holds for both. Each of the nineteen results is pinned under `#guard_msgs` twice at the end of the
file, once as an axiom list and once as its statement (`#check`), and `attest.py` requires every axiom
pin (`REQUIRED_PINS`), so deleting one fails it. The build compares the text of each statement pin, and
`attest.py` requires each of the nineteen to exist as an active `#guard_msgs in #check` whose options still compare the
printed message (`REQUIRED_STATEMENT_PINS`), so deleting one, commenting one out or dropping its message fails it. `attest.py` does
not read what a statement pin says. The axiom lists name the opaque constants that the statements mention,
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
  record, and neither of the other two assumptions, reaches `Option::eq`, by reading: it is not among the 48 interpreted
  constants.

Each result has an axiom pin under `#guard_msgs`, and `attest.py` requires every one of the 51 (`REQUIRED_PINS`), so
deleting one fails it. An axiom pin holds the list of axioms a result depends on and not its statement, and none depends on
a compiler-trust axiom. The statements of `headroom_of_axiom_base`, `headroom_hypotheses_satisfiable`,
`responder_headroom_of_contracts`, `encrypt_headroom_of_contracts`, `decrypt_headroom_of_contracts`,
`initiator_headroom_of_contracts`, `initiatorHeadroom_iff`, `responderHeadroom_iff`, `encryptHeadroom_sessionOf_iff`,
`invariant_session_meets_both`, `invariant_session_of_axiom_base`, `invariant_hypotheses_satisfiable`,
`decryptHeadroom_of_invariant`, `encryptHeadroom_iff_of_invariant`, `sessionOf_invariant`, `emptyChain_headroom`,
`epochZero_bounds`, `session_emptyChainTable_fails_invariant` and `session_epochZero_fails_invariant` are also pinned by
`#guard_msgs in #check`, which the build holds and which no gate requires to exist, so deleting one of those pins is not
refused. The other 32 results are held only by the build, which accepts whatever statement is written if it proves it, and
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
relations between a translated value and a model value (`StateRefines`, `StateR`, `HeaderR`). Every proof is
about the constant `Usize.max`, of which Lean knows only that it is `2^32 - 1` or `2^64 - 1`, so each holds at
both platform widths and none appeals to a width.

The statement of each witness is checked against its theorem and not trusted. `scripts/check-precondition-witnesses.sh` reads the
theorem's type from the built environment, rebuilds the conjunction of the premises its table puts inside the
witness, requires the module's `Premises.T` to equal it and `sat_T` to prove exactly `Premises.T`, and requires
every other premise of `T` to be classified as `boundary` or `unwitnessed`, so a premise added to a theorem
later is refused until it is classified. It runs inside `no-sorry.sh` with 28 cases, 7 that must be accepted and 21 that apply one change and must be refused (a bound weakened
in a statement, a witness deleted or replaced by `True`, a statement or a table row removed, a premise left
unclassified, a numeric premise listed as outside, a premise added to a theorem). The check is a script and
not a Lean theorem because `check-lean-constructs.sh` refuses elaboration-time code in this package; it
trusts the script's reading of the environment, and classifies a hypothesis as numeric by a comparison on a
natural number or an integer in its propositional skeleton or by the name of a numeric state predicate, so a
numeric bound hidden behind a definition whose name is not on the script's list of numeric state predicates is
classified by the table's author; `ChainCounterBounded`, a bound on a chain's counter, is such a name and is on the list.

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
(`needed = 65536`); the arms that hold a KEM value stay open there too. The states are small (one chain and one skipped
key, one stored skipped key); the bounds up to their caps are in the next sections.

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
  epoch step and the invariant met together at a state, and they stop building if a premise is added to the discharge theorem or made
  unsatisfiable. The lifecycle theorems of `SessionUnitDecodedStateDischarge.lean` (`decrypt_headroom_of_invariant` and the two that
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
decoded state refines the model.

The result that was not in this ledger is for the sparse ratchet. `SpqrT3.receive_refines` takes `hroom`, `hskiproom` and `hone`,
which `ImportInv.lean` derives from the invariant, and five premises that were recorded as open: `hepoch`, `hcb`, `hsb`,
`hnewb` and `hcounter`. `hcb` and `hsb` (every chain epoch, and every skipped key's epoch, plus `EPOCHS_KEPT` is at most
`u64::MAX`) follow from the invariant together with `hepoch` (`epoch + 1 < u64::MAX`), so the premises that stay with the
caller are three: `hepoch`, `hnewb` (the epochs of the keys an operation adds) and `hcounter` (every chain's counter is below
`u64::MAX`). The invariant alone still does not give `hcb`: the state at `epoch = u64::MAX - 1` with a chain at that epoch
passes `invariant` and fails `hcb`, and it fails `hepoch` too. The same holds for `send_refines`, `advance_refines`,
`maybe_advance_refines` (`hroom`, `hcb`, `hsb` follow from the invariant and `hepoch`) and `clear_old_epochs_refines`
(`hcb`, `hsb`). `hepoch` is not discharged: it excludes one honest value, and that value is an ordinary state.

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
  `ImportInv.lean` describes.
- `triple_receive_premises`, `triple_send_premises`: on the session unit, the Triple's composed refinements
  (`receive_refines_discharged`, `send_refines_discharged`) take the premises of both inner ratchets stated about the model state. Given the two
  inner decoder invariants, `hrel`, `hevents` and `hepoch`, the receive theorem's `hone`, `hs`, `hroom`, `hcb`, `hsb`, `hskiproom` and `hone2`
  follow, and the send theorem's `hroom`, `hcb` and `hsb` follow from the sparse invariant, `hrel` and `hepoch`. What stays with the caller
  is `hevents`, `hepoch`, `hnewb` and `hcounter` (receive) and `hepoch`, `hnewb` and `hcounter` (send), and `hheader`, which relates
  the header to its model header. Proved for the session unit's copy only: the three-leaf unit has no decoder-invariant module.
- `decrypt_headroom_of_invariant`, `decrypt_ratchet_no_panic_of_invariant`, `decrypt_no_panic_of_invariant`: a session that passes
  `Session::invariant` meets `DecryptRatchetHeadroom` once `identity_ad.length + 106 ≤ usize::MAX` holds, and the two lifecycle
  panic-freedom theorems apply with it. `invariant_gives_preconditions` derived the record without the associated-data bound and no
  theorem used it; this is the connection. The theorems are conditional on `DecryptRatchetContracts` exactly as the ones they apply are.

## Proved (the numeric bounds against the caps they are compared with, at both platform widths)

Location: `Translation/NumericBoundary.lean`, `Translation/NumericBoundaryLeaf.lean`, `Translation/NumericBoundaryTriple.lean`, `Translation/NumericBoundarySession.lean`, `Translation/NumericShapeWitness.lean`.

Every numeric bound is written against `usize::MAX`, `u32::MAX`, `u64::MAX` or a fixed cap of the code. Only the first depends on
the platform, and Lean knows of `usize::MAX` that it is `2^32 - 1` or `2^64 - 1`; each statement below is proved by a case
split on that, so it holds at both widths, and a bound that held at 64 bits and not at 32 (the defect of 2026-09-10) would fail in
the 32-bit case. These are statements about arithmetic and about the translations' constants. They are not statements that a
real run reaches a size, or that the Rust source has the constant the translation evaluates.

- `both_widths`: `Usize.max` is `2^32 - 1` or `2^64 - 1`.
- `classical_store_cap_fits`, `classical_skip_cap_fits`, `spqr_chain_cap_fits`, `spqr_skip_cap_fits`, `ratchet_codec_cap_fits`,
  `spqr_codec_cap_fits`, `erasure_cap_fits`: the room bounds the theorems take hold for every size the code's caps allow
  (a store of up to 2000 keys, at most two chains, an erasure decoder of up to 65536 chunks), at both widths.
- `erasure_room_exact_at_32`: at 32 bits `32 * needed < usize::MAX` is exactly `needed ≤ 2^27 - 1`, so the bound is not slack.
- `clock_ceiling_excludes_only_parked`, `epoch_ceiling_excludes_only_top`: `events + 1 < u32::MAX` fails, among the values
  the decoder's invariant allows, only at `u32::MAX - 1`, and `epoch + 1 < u64::MAX` only at `u64::MAX - 1`. Each ceiling
  that stays a caller's premise excludes exactly one honest value.
- `ratchet_constants`, `spqr_constants`, `erasure_constants`, `protobuf_constants`, `code_matches_model`, `max_events_is_parked`,
  `clock_ceiling_summary`: in the standalone translations, the constants the bounds mention have the values the
  arithmetic uses, equal the model's copies, and the clock premise of `T3.receive_refines` is satisfiable, is failed by the
  parked clock, and by no other value (`PreconditionShapes.lean`'s two theorems about it are the summary's first two conjuncts).
- `unit_ratchet_constants`, `unit_spqr_constants`, `unit_code_matches_model`, `session_unit_ratchet_constants`,
  `session_unit_spqr_constants`, `session_unit_erasure_constants`, `session_unit_code_matches_model`: the same on the
  three-leaf unit and the session unit, which cannot share an environment with the standalone translations.
- `usize_max_cases`, `every_shape_is_satisfiable`: as enumerated once from the built environment (the script is not in this tree, so
  nothing here checks that the list is complete or stays complete), the numeric premises of the theorems of this package fall into 61 shapes
  (`S01` to `S61` in the module: a comparison between sums and products of lengths, scalars and model numbers, a constant and an
  operator), and each is satisfiable at both widths, with its first atom at the largest value the shape admits and, where that
  value is bounded, nothing larger meeting the shape. The aggregate theorem names every shape theorem so that deleting one is an
  error. The shape theorems are about shapes and not about theorems: nothing in the tree joins a shape to the premises that have
  it, so a premise added to a theorem with a shape outside the 61 is not noticed there. The statements of the individual shape
  theorems are not pinned. The join to the central theorems is the witness section above.

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
premises, by reading each theorem's type from the built environment (28 cases hold
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
seven `run_cmd Model.AxiomAudit.run` lines, allow-listed by file path and
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
