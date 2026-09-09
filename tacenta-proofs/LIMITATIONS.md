# Limitations

The trusted computing base, and what is deliberately not proven yet. Kept honest
so a claim never reads as stronger than its evidence.

## The proofs are trusted by evaluation, not only by the kernel

The first thing an external reviewer should know, because it is the thing an
external reviewer will find first.

Two tactics used throughout this development discharge goals by **running a
compiled program** rather than by producing a proof term the Lean kernel checks.

`native_decide` is the expected one. It compiles a proposition and evaluates it,
and it is used deliberately and rarely.

`bv_decide` is the one that surprises people, and it is the one that matters
here. It looks like an ordinary decision procedure for bitvectors, and it settles
goals over 2^32 values that no kernel reduction could reach. It gets there by
bitblasting to SAT, and its reflection step is *also* native evaluation: every
axiom it introduces is named `._native.bv_decide.ax_*`. A proof by `bv_decide`
trusts the Lean compiler exactly as a proof by `native_decide` does.

That is load-bearing rather than incidental. `bv_decide` is what makes the
GF(2^16) field proofs possible at all: `Model.Gf65536.mul_assoc`, the statement
that this is a field and not merely probably a field, rests on about forty such
axioms. `Model.Gf65536.mul_inv_cancel`, that every nonzero element inverts, is
`native_decide` and there is no kernel route to it, because `decide` cannot
reduce sixty-five thousand exponentiations and `bv_decide` cannot model an
exponentiation at all. Interpolation divides by the difference of two distinct
nodes, so the erasure code's correctness runs through that axiom.

**Where this is and is not the case is pinned by the build, not described.**
`Proofs.TrustedBase` prints the axioms of the load-bearing theorems under
`#guard_msgs`, so a proof that starts trusting something new fails there: the
Braid's epoch accounting, the classical ratchet's five T2 theorems, the field
and interpolation results, and the composite header. `Translation.T1` and
`Translation.T3` do the same for the classical ratchet's T1 and T3 headline
theorems (`send_refines`, `receive_refines`, `message_keys_refines`),
`Translation.SessionT1`/`SessionT3` for the session's,
`Translation.ErasureT1`/`ErasureT3` for the erasure coder's two entry points
and its field, and `Translation.ProtobufT1`/`ProtobufT3` for both message
parsers, the encoder and all nine refinement theorems. The sparse ratchet's,
the Braid's and the Triple's T1/T3 files are **not yet pinned**, so the axiom
bases stated for them below are read off `#print axioms` by hand rather than
held by the build. Some results are on the
kernel alone and are worth knowing as such. The ML-KEM Braid's epoch accounting
depends on `propext` and `Quot.sound`, nothing more. That is the calculation on
which both sides must agree exactly, so having it on the kernel rather than on
a compiler is worth the line.

Most other uses of `native_decide` (about a hundred) are in `example`
declarations. Those are build-time known-answer checks: they fail the build if
wrong, and no theorem depends on them, so they widen no proof's trust base.

**Fourteen are inside translation theorems.** They are: `fPrefix_agrees` and `skInfo_agrees` in
`Translation.SessionT3`; in `Translation.SpqrT3`, `protocol_info_agrees`,
`chain_start_agrees`, `root_label_agrees`, `chain_label_agrees`,
`max_skip_agrees`, `max_skipped_store_agrees`, `max_skip_val`, and one step of
`receive_refines_continuation`; in `Translation.TripleT3`, `split_info_agrees`,
`combine_info_agrees`, and one step of `split_secret_refines`; and one step of
`Translation.SpqrT1.receive_no_panic` (that `(1 : U64)` has value 1). A
fifteenth, `Model.Gf65536.mul_inv_cancel`, lives in the model and is pinned in
`Proofs.TrustedBase`. `u8_zero`, `zeroSalt_agrees` and
`decode_ec_after_encode_ec` are **not** among them: each is written `first |
rfl | decide | native_decide` and closes on `rfl`/`decide`, so they are
kernel-only. Each of
the fourteen is a closed numeric or byte-string fact that `decide` could in
principle settle and `native_decide` settles faster. On Lean v4.31.0 the axiom
each use adds is the per-declaration `<decl>._native.native_decide.ax_*` (and
`…bv_decide.ax_*` for `bv_decide`), not `Lean.ofReduceBool`; either way it
puts the compiler into the axiom base of every theorem downstream: in
particular the sparse ratchet's T1 headline theorem and every T3 refinement
that uses a label lemma are compiler-trusted, not kernel-only, and `CLAIMS.md`
should be read with that in mind. Counted by a `#print axioms` sweep over
every theorem; pinning the sparse ratchet's, the Braid's and the Triple's
headline theorems under `#guard_msgs` is open work (the classical ratchet's,
the session's, the erasure coder's and the parser's are pinned).

## Trusted, not verified

- The recorded generation of the translation is trusted.
  `manifests/translation-attestation.json` says which bytes each generated
  `Translation/Tacenta*.lean` had, which `axiom` names it declared, and which
  Rust it came from, as of the last time someone ran `scripts/run-aeneas.sh`
  on the pinned toolchain and then `attest.py --refresh-translation`.
  `attest.py --check` holds the tree to that record, so a generated file
  edited by hand, a new opaque external, or a Rust change nobody
  re-translated each fail in the public tree with a message naming the file
  or the crate. That the recorded generation was produced by the pinned
  toolchain, and honestly, is not something the public tree can check: it is
  what the private verification workflow's drift step checks by
  regenerating, and what any linux-x86_64 reader can check the same way.
- A declaration added with `set_option debug.skipKernelTC true` is checked
  by the elaborator and not by the kernel, and nothing in the environment
  says so afterwards. `Model.AxiomAudit`, which every package's build runs,
  refuses axioms, opaques, unsafe and partial declarations and
  `implemented_by`/`extern` from the elaborated environment, but cannot see
  this one; `scripts/check-lean-constructs.sh` refuses the option textually,
  and `no-sorry.sh` replays every first-party module through the kernel with
  `leanchecker`, which is the check that actually settles it. `leanchecker`
  is Lean's own kernel rerun over the oleans, not an independent checker.
- The Mathlib build artifacts the T1/T3 build loads are trusted. `lake exe cache
  get` fetches prebuilt `.olean` files for the pinned Mathlib commit from
  Mathlib's cache over HTTPS with no signature, and Lean loads an olean without
  re-checking it against its source. The manifest pins which Mathlib commit is
  *meant*; the cache decides what is *loaded*. Building Mathlib from source
  removes this edge and costs hours, which is why it is a trust rather than a
  step.
- The cryptographic primitives are trusted. tacenta-core uses vetted crates for
  X25519, HKDF, HMAC, SHA-256, AES-256-CBC, and Ed25519, and ML-KEM-1024 from
  libcrux-ml-kem, which is itself formally verified, its source carrying hax and
  F* contracts. XEdDSA is the one exception: it is implemented here over
  curve25519-dalek and ed25519-dalek rather than taken from a vetted crate, the
  deliberate exception recorded in ADR-0002. The model computes SHA-256, HMAC, and HKDF
  itself only to serve as the vector oracle, and those are anchored to RFC and
  NIST values.
- Diffie-Hellman agreement and the AEAD are boundary primitives in the model: it
  consumes DH outputs as bytes and stops at the AEAD material. The model's
  vectors therefore assert the key schedule, not ciphertext bytes.
- **Several boundary hypotheses are stronger than the Rust they stand for.**
  Each opaque operation the translation cannot see is assumed total, and some
  of them are not total in Rust: `HkdfTotal` and `SpqrHkdfAgrees` assume
  `hkdf_sha256` returns for *every* output length, where the crate `expect`s
  the RFC 5869 bound `N ≤ 8160` (every call site asks for 32, 64 or 96;
  `KdfCkTotal` and `KdfRkTotal` are about the crate's own fixed-length
  wrappers and are total in Rust, so they do not belong in this list); the
  two `VecRemoveTotal`s
  and `VecRemoveAgrees`
  assume `Vec::remove` returns at every index, where Rust panics out of
  range (every call site checks the index first); the erasure crate's
  `usize::div_ceil` is assumed total including at a zero divisor (its only
  divisor is the constant `CHUNK_BYTES`); and the RNG's `fill_bytes` is
  assumed to return (a failing RNG panics). Each hypothesis is sound *as
  used*, because the call sites stay inside the region where Rust agrees,
  and none of that is stated in the hypothesis itself; a reader checking a
  theorem against the code has to check the call sites too. Restating them
  with the Rust precondition is open work.

## Secret deletion is partial

Both specifications call for deleting key material once it has been used: the
Diffie-Hellman outputs and the encapsulated secret after the handshake derives
its secret, and each message key and superseded chain key as the ratchet
advances. What is implemented is the cheap and meaningful part: the buffers that
concentrate secret material are wiped on the way out (the handshake's
concatenated key material and its KDF input, the ratchet's 64-byte and 80-byte
KDF outputs, and the KEM's seed and encapsulation randomness).

**Whole-state erasure.** Every state that holds a secret wipes it on drop:
the classical ratchet's `State` and `SkippedKey`, the sparse ratchet's
`State`, `Chain`, `Skipped` and `Output`, the Braid's `Auth` and, through
their representations, the incremental key pair and encapsulation state
beneath it, and the session-establishment types `Identity`, `PrekeyStore`,
and the ML-KEM `KeyPair`.

Four things are not erased, and they are the honest remainder:

- **Copies the language makes.** Keys are typed as `[u8; 32]`, which is `Copy`,
  so copies can remain in stack slots and registers after a value is moved or
  replaced, and nothing wipes those. Doing this properly means non-`Copy` secret
  types throughout, which would ripple through the API and has to be weighed
  against keeping the ratchet inside the subset the Charon and Aeneas
  translation models.
- **Copies libcrux makes.** `libcrux-ml-kem` does not implement `zeroize`, so a
  value held in its own types stays resident until the allocator reuses the
  memory. Our wrappers hold
  key material as erasing byte buffers and hand libcrux a reconstructed value
  per call, which bounds the window to one call rather than to the lifetime of a
  store -- but the value inside that window is libcrux's and is not wiped.
  Closing this means a change upstream, not here.
- **Anything persisted.** `Session::export` and the prekey store's own
  serialization produce plaintext bytes by design; at-rest protection is the
  caller's, and session-persistence.md says so.
- **Copies the allocator makes.** A `Vec` that grows by pushing moves its
  contents to a larger allocation and hands the smaller one back un-wiped;
  `Zeroizing` reaches only the allocation alive at the end. The classical
  ratchet's `to_bytes`, `Session::export` and `PrekeyStore::to_bytes` size
  their buffer exactly before the first write, so they never grow. The sparse
  ratchet's and the Braid's `to_bytes` grow by pushing: those crates are
  translated, a source change there is a translation change, and it waits for
  the next re-translation window. Every `Vec` inside libcrux is libcrux's.

**None of it is proved.** Charon and Aeneas ignore `Drop` entirely, so the
generated Lean is byte for byte identical with and without every destructor
above, and no T1 or T3 theorem says anything about erasure. What guards it is a
static check per crate that fails the build if the property is removed -- a much
weaker instrument than the proofs standing next to it, and it should not be
mistaken for them. The Double Ratchet specification's own secure-deletion
section notes that recovering deleted data is platform-dependent and outside its
scope; the same caveat applies here. Treat forward secrecy as resting on the key
schedule, not on guaranteed erasure of every in-memory copy.

## Undefined behaviour: forbidden statically, checked dynamically where it can be

Every crate in `tacenta-core` carries `#![forbid(unsafe_code)]`. None
contains `unsafe`, and the attribute is what keeps that true rather than merely
observed. It bounds our own crates only; the primitives are the trusted
boundary and are unaffected.

`tooling/miri.sh` is the dynamic half. Miri interprets MIR and reports
undefined behaviour: out-of-bounds access, invalid aliasing, uninitialised
reads, misaligned pointers. With `unsafe` forbidden the interesting result is
not UB in our own unsafe code -- there is none -- but that the *safe* code and
everything it calls in `core` and `alloc` executes cleanly, which catches an
`unsafe` block inside a dependency reached on one path, or a std API used in a
way that is unsound.

**Clean across `tacenta-protobuf`, `tacenta-kdf`, `tacenta-ratchet`,
`tacenta-session`, and `tacenta-triple`** (`tooling/miri.sh`), with no undefined
behaviour reported. The first three run in seconds; `tacenta-triple`'s
conversation tests take minutes under the interpreter, so the script runs
nightly rather than on every push.

Three limits, stated because a scoped check read as a whole-codebase one is
worse than no check:

- **Anything touching the primitives is out**, mechanically rather than by
  choice: Miri cannot execute the SIMD intrinsics `libcrux-ml-kem` and the
  dalek crates use, so `tacenta-kem`, `tacenta-braid`, and `tacenta-core`
  itself cannot run under it at all.
- **`tacenta-spqr` and `tacenta-erasure` are excluded on cost.** Their suites
  are dominated by deliberate bound-stress tests -- thousand-key skips, epoch
  retirement, polynomial interpolation over GF(2^16) -- which run for half an
  hour or more under an interpreter. They are runnable on demand and the script
  says how.
- **The stress tests are filtered even where the crate runs.** Skipping them
  took `tacenta-ratchet` from over forty-five minutes to under six seconds.
  What is lost is UB coverage of a loop repeating an operation the same test
  already performs once; what is kept is every decoder, state transition, and
  indexing path.

## What a green proof does not say about cost

T1 says a function cannot panic. T3 says it computes what the model says.
**Neither says anything about how long it takes**, and that distinction is
not theoretical.

Three decoders here have their early loop exits removed so that Charon and
Aeneas translate them. That shape keeps both properties exactly -- same
accepted inputs, same results, still no panic -- and neither property
constrains the loop count, which is four attacker-chosen bytes. A loop of
that shape with no early exit would run four billion times on an eight-byte
input, with both proofs green, correctly; the bound on it is the decoder's
own business and no theorem's.

The general statement, and it applies to every theorem in `CLAIMS.md`: these
are proofs of *functional* properties. Termination in reasonable time,
memory used, and work done per byte of input are outside every one of them. A
decoder that is proved panic-free and proved to refine its model can still be a
denial of service, and the instrument for that is the fuzzing in
`tacenta-core/fuzz/`, not anything in this directory.

## Constant-time behaviour is assumed, not proven

An attacker who can measure how long an operation takes must learn nothing secret
from it. This holds here by delegation and discipline, not by proof.

- **The secret-touching work is at the trusted boundary, assumed constant-time.**
  X25519 and Ed25519 (dalek) are constant-time; ML-KEM (libcrux) is formally
  verified and ships a `check-secret-independence` mode; the AEAD tag is checked
  with a constant-time comparison (`Mac::verify_slice`), not a byte-wise `==`.
  These properties are inherited from the crates, and assumed rather than
  re-established here.
- **The Braid's MAC comparison is a hand-written loop.** `mac_eq` in
  `tacenta-braid` ORs the XOR of every byte pair and tests the accumulator
  once at the end -- the textbook shape -- but nothing in the language stops
  a compiler from recognising the shape and shortening it, and the crate
  carries no `subtle` because every dependency it has is a translation
  boundary. Moving the comparison behind the `kdf` boundary, where
  `subtle::ConstantTimeEq` is available and the translation sees an opaque
  call, changes the translated source and so waits for the next
  re-translation window. Until then the guarantee is
  the loop's shape and an inspection of the generated code, not a library's.
- **Our own composition is audited to not reintroduce a leak.** tacenta-core's
  ratchet, session, and serialization code branches on and compares only public
  data: ratchet public keys, message numbers, and wire bytes, whose timing
  reveals nothing secret. On no path a peer can time does it perform a
  byte-wise `==` on a message key, chain key, root key, or shared secret. Two
  benign exceptions: the ratchet, sparse ratchet and Triple states derive
  `PartialEq`, which compares their keys
  byte-wise and which only tests use; and `Session::import` re-encodes the
  state it decoded and compares the bytes to the input, a canonicality check
  over the caller's own persisted blob, where the only observer is the caller.
  This was checked by reading the code, not by a timing experiment.
- **Two of the claims above are measured in CI, not only read.**
  `tacenta-core/tests/timing.rs` times two input classes and asks whether their
  rejection times differ by an *exploitable* margin -- an effect size in
  nanoseconds. Representative results from the isolated measurement core:

  | What | Class A median | Class B median | effect size |
  | --- | --- | --- | --- |
  | Tag comparison, by how much of the tag was right | wrong at byte 0: 213 ns | wrong at byte 31: 215 ns | 2 ns |
  | Rejection, by forged ciphertext contents | all-zero: 261 ns | all-ones: 263 ns | 2 ns |

  The classes differ by ~2 ns -- the integer-nanosecond timer's quantization
  floor -- against a 5 ns leak floor. A byte-wise `==` that short-circuited on the
  first wrong byte would differ by ~10 ns, and an attacker who saw that would
  recover a tag one byte at a time; the constant-time `Mac::verify_slice` does not.

  **This raises those two from assumed to measured, not to proven.** A measurement
  covers the inputs it draws on the machine it runs on; a proof covers all of
  them. What it buys is that a regression becomes visible, which reading the code
  cannot. The tests are `#[ignore]`d out of the per-push run and run nightly in
  release mode by a nightly timing workflow. Run them by hand with
  `cargo test -p tacenta-core --test timing -- --ignored --nocapture`.

  **Why the gate is a median gap on an isolated core.** Two choices in the
  test are load-bearing, environment and statistic.

  *The environment.* A timing job co-scheduled with other load on a shared,
  frequency-scaling machine fails a *different* assertion from one run to the
  next with the two classes' medians equal to the nanosecond -- the signature
  of contention, not a leak. The measurement therefore runs on a dedicated
  core, isolated at boot and held at a fixed clock, so it is immune to
  everything else on the machine.

  *The statistic.* Even on that isolated core a dudect Welch t-statistic is
  not the right instrument: at ~200 ns per operation it reports a |t| of 60 for
  a 1 ns quantization gap as readily as for a real leak, and its same-input
  null still bounces to triple digits on a stray housekeeping tick. A p-value
  is not an effect size, and a timing leak *is* an effect size. So the gate
  decides on the class median gap in nanoseconds: a 5 ns floor, set from the
  measured 0-2 ns constant-time noise and a real short-circuit's ~10 ns -- from
  what the operations physically cost, **not** a number tuned to pass. A
  negative control, fast-head cropping, order balancing, and setting Apple
  Silicon's DIT bit are kept as diagnostics and robustness; the t-statistics
  are printed but do not gate. Drawing more samples and keeping fewer does not
  help on a contended runner, because a larger N gives Welch's t more power to
  resolve systematic drift; the test's own comments record the alternatives
  considered. The gate stays in CI, on the quantity that actually matters.

- **Still assumed: the primitives, and everything not in that table.** X25519,
  Ed25519, and ML-KEM are the trusted boundary and are not measured here;
  timing them would report on dalek and libcrux rather than on this codebase. A
  formal secret-independence check across the whole path is still not wired.
  None of this is in the proof scope either: T1, T2, and T3 constrain
  correctness, totality, and refinement, and none of them constrains timing.

- **One measured cost that is not a leak, and is worth knowing.** The Double
  Ratchet cannot check a message's authenticator until it has derived that
  message's key, so a forged message claiming a far-future number makes the
  receiver work before it can discover the forgery. `MAX_SKIP` bounds that, and
  the same test measures what the bound permits:

  | Forged message at | Cost | Against baseline |
  | --- | --- | --- |
  | the next number | 145 µs | 1x |
  | a gap of 900, inside `MAX_SKIP` | 1.86 ms | **12.8x** |
  | a gap of 1,200, beyond it | 43 µs | 0.3x |

  Two things follow. **The bound is enforced ahead of the derivation**, since
  asking for more than it allows costs *less* than an ordinary message rather
  than more -- had it been checked afterwards, exceeding the limit would have
  been the cheapest way to buy work. And **one forged packet can cost a
  receiver about thirteen ordinary ones**, which is inherent to the protocol
  rather than particular to this implementation, but is a number an operator
  sizing a relay should
  have rather than discover.

## Forward secrecy is proved, against a symbolic attacker

`Properties.ForwardSecrecy` proves that an attacker who takes a party's chain key
cannot derive any earlier message key. It is worth stating precisely, including
what it is not.

**It is against a symbolic attacker.** In `Model.Adversary` a key is a term
recording how it was derived, not the bytes it evaluates to, and the attacker
derives keys only by the rules given -- one per way the protocol derives a key,
and none that runs a chain backwards. Over byte strings the claim is not provable
and barely statable: it reduces to "SHA-256 cannot be inverted", which is an
assumption about a primitive rather than a fact about this protocol.

**So the fidelity assumption is real and is the whole gap.** A symbolic model
says the attacker learns nothing except by its rules; against the real protocol
that holds only if the key derivation is one-way and collision-resistant, which
is not proved here or anywhere in this repository. What is proved is the
protocol's own half: *given* such a derivation, the ratchet's structure leaks
nothing about its past. That is exactly the part that is the protocol's own
responsibility, and exactly what the byte-level vectors cannot check.

**It is one chain, not a session.** A session interleaves chains, root steps and
Diffie-Hellman outputs and holds several keys at once. What is proved is a single
chain in isolation, which is where forward secrecy within an epoch comes from.
Carrying it to a whole session means relating these terms to `Model.State`, and
that relation is not written.

**Compromise going forward is total, and that is a theorem too.** An attacker
holding the chain key at a step derives every message key after it. That is the
design: recovery is the Diffie-Hellman ratchet's job, not the chain's. It is
stated so that the theorem above is not read for more than it says.

**Post-compromise security is proved too**, against the same attacker and with
the same assumption: having taken a party's root key, an attacker cannot derive
the next epoch's keys unless it also took that epoch's agreement output. The
argument is the arity of the rule -- the derivation needs both halves, and an
agreement output is a leaf available only to whoever took it.

It carries one condition that is the condition rather than a detail. An attacker
holding a *ratchet private key* computes the agreement output itself and nothing
heals. Compromise of long-lived key material is worse in kind than compromise of
a chain, and no ratchet repairs it.

Neither result says anything about *when*. A step heals; how many messages pass
before one happens is a property of the conversation, and a party that only sends
never takes one. These models have no notion of time or turn-taking.

**Message keys are proved independent.** A message key that escapes -- handed to
the encryption layer, logged, left in a buffer the ratchet no longer controls --
costs nothing beyond the one message it opened. Nothing in the key schedule takes
a message key as input, so it is a dead end: an attacker holding one reaches
neither the chain it came from nor any sibling. This is a smaller compromise
than the two above and a likelier one, which is why it is worth its own
statement.

**Authentication is the one where the assumption is the larger half, and the file
says so.** That a ciphertext verifying under a key was made by someone holding
that key is assumed, not proved, and cannot be proved in a symbolic model: it is
the premise. What is proved is the protocol's contribution given that premise --
that the key doing the authenticating is bound to one session and one position,
and unavailable outside it. Sessions never share a key, and an attacker who takes
a whole session learns nothing in another. Without that, unforgeability would
hold and authentication would still fail, because a message made for one
conversation would verify in another.

Two things it does not cover. The identity binding in the associated data is
proved elsewhere, in `Proofs.SessionEstablishment`, and neither half suffices
alone. And nothing anywhere in this project proves that an identity key belongs to
the person a user means: that is trust on first use and the directory's problem,
and it is the assumption a user actually bears.

## Seven verified zones, and the shipping path's orchestration runs outside them

**Read this before the list.** Integrating the Triple Ratchet
moved `Session::encrypt` and `Session::decrypt` off `tacenta-ratchet::send` and
onto `tacenta-triple`, which drives `tacenta-spqr` and `tacenta-braid`.

`tacenta-spqr` and `tacenta-braid` are **translated**, with no `sorry` and
no body Aeneas gave up on, so a change that breaks their translatability fails
the retranslation in the verification workflow rather than passing quietly.

**T1 covers all of `tacenta-spqr`'s protocol surface** (not the
persistence codecs `from_bytes`/`to_bytes` and their entry decoders, nor
`init`/`init_alice`/`init_bob`, `Output::new`, `epoch`, `skipped_len` or
`evict_oldest`, which are translated and have no theorem; see CLAIMS.md's
"Translated is not proved"): the three loops
(`find_chains`, `try_skipped`, `skip_message_keys` -- the last being the one
that would be a remote memory exhaustion if the gap it walks were unbounded),
`set_chains`, `clear_old_epochs`, `advance`, `maybe_advance`, and the two entry
points that compose all of it, `send` and `receive`. Each carries stated
preconditions rather than unconditional totality: room for the epoch vector to
grow by one or two (`EPOCHS_KEPT` keeps this true in practice but does not
establish it as a length fact the translation can see), an epoch counter and a
per-chain message counter each below `2^64`, and the skipped-key store having
room for one more batch. None of these is checked by the type system; each is
a real assumption about how far a session can run before it must be
refreshed, not a formality.

**`tacenta-spqr` also has T3**: `send`/`receive` compute what
`Model.SparseRatchet.send`/`receive` say -- the key returned, the output
reported, and the state transitioned to -- across every branch each can
take, not merely that they cannot fail. Unlike the ML-KEM Braid this crate
has no KEM boundary and no erasure-coding boundary to assume agreement at;
the only opaque call this file assumes anything about the *value* of is
`hkdf_sha256` -- `Vec::retain`/`remove`/`append`, `Zeroize`, and
`Option::clone` are opaque too, each its own assumption below -- and
everything built out of translated code around it -- `find_chains`,
`set_chains`, `clear_old_epochs`, `advance`/`maybe_advance`, `try_skipped`,
`skip_message_keys` -- is proved outright, not assumed.
`Model.SparseRatchet.lean` carries its own lemma library, as `Model.Braid.lean`
does: how far `advance` can shrink the skipped-key store,
how a chain-vector length bound survives `set_chains`/`skip_message_keys`,
and a left-peeling split for the forward-derivation walk `skip_message_keys`
performs. Six assumptions back it: `SpqrHkdfAgrees` (one level below
`SpqrT1.lean`'s `KdfRkTotal`/`KdfCkTotal`, subsuming both), `VecRetainAgrees`
and `VecRemoveAgrees` (each strictly stronger than its `SpqrT1.lean`
namesake), `VecAppendAgrees` (genuinely new, since nothing in T1 needed to
know what `skip_message_keys`'s concatenation actually produced), and
`Tacenta.SpqrT1.ZeroizeTotal`/`OptionCloneTotal` carried over unchanged. See
`SpqrT3.lean`'s own closing section and `CLAIMS.md`'s spqr T3 entry for the
full account.

**The `hcounter` precondition is scoped to the input state's own chains
table.** `send_no_panic`/`receive_no_panic` (`SpqrT1.lean`) and
`send_refines`/`receive_refines` (`SpqrT3.lean`) each carry an `hcounter`
hypothesis saying "the chain this call is about to step forward has not yet
sent 2^64 messages." It is stated over the real input state's own chains
table, the same shape `hcb`/`hsb` use, and not as `∀ ch : Chain, ∀ cs :
Chains, cs.send = some ch → ch.n.val < Std.U64.max`, quantified over *every*
value the `Chain`/`Chains` types can hold: a `Chain` with `n = Std.U64.max`
is a value of the type, so that hypothesis would be unsatisfiable, and a
theorem that takes an unsatisfiable hypothesis is true but has no proof term
any real caller can construct. Nothing in `lake build`, `#print axioms`, or
the `sorry`/`admit` grep in `scripts/verify.sh` says anything about whether
a stated hypothesis is *satisfiable*, only about whether the proof compiles,
which is why the scoping is worth stating here and why
`Translation/Satisfiability.lean` exists.

That scoping needs a `ChainCounterBounded` model-level invariant and two
preservation lemmas in `SpqrT3.lean` (`advance`/`skipMessageKeys` only ever
carry an existing counter through or open a fresh one at zero), and the
real-level counterpart in `SpqrT1.lean` -- `VecRetainTotal` carries a
membership clause (`retain` cannot fabricate an element, only drop one), and
`find_chains_no_panic`/`set_chains_no_panic`/`clear_old_epochs_no_panic`/
`advance_no_panic`/`maybe_advance_no_panic`/`skip_message_keys_no_panic`
each carry that membership fact one call further. The precondition is one
every real caller satisfies.

**`tacenta-triple` has T3, against a composed model of its own.**
`Model.TripleRatchet.lean` carries `splitSecret`/`combine`, the two
opaque-KDF calls this composition makes on its own; `Model.Triple.lean` is
the composed `State`/`send`/`receive`/`commit` state machine, mirroring the
real crate's clone-candidate-commit shape (`receive` returns a candidate
state without mutating its input; `commit` is a separate, near-trivial step,
so that state never advances on an unauthenticated message).

**The two inner ratchets' own T3 proofs cannot be imported into this file,
and it is a real toolchain limit, not a style choice.** `Translation/T3.lean`'s
and `Translation/SpqrT3.lean`'s own `send_refines`/`receive_refines` cannot be
composed directly, the way `TripleT1.lean` composes their totality facts.
`import Translation.TacentaTriple` together with either inner crate's own
standalone translation fails outright: Charon translates each crate
separately, and `tacenta_ratchet.State`/`tacenta_spqr.State` are each a
**bare opaque axiom** inside `tacenta-triple`'s own translation (Charon
translating that crate alone has no visibility across the crate boundary
into either dependency's real struct), where the same names are concrete,
field-bearing structures in each crate's own standalone translation --
different declarations sharing a name, and the auto-generated instances
collide if both are imported into one file. There is also no field to
project even where the collision is set aside: a `StateR`-style relation
needs fields that are not visible from here.

So, in `TripleT3.lean`, `RatchetAgreesFor`/`SpqrAgreesFor` each bundle
one existential abstraction function under which `clone`, both initialisers,
the small accessors, `send`, and `receive` agree with the corresponding
model function -- the same bundled-existential shape `BraidT3.lean`'s
`KemAgreesFor` already uses, for a different reason: a KEM is uninterpreted
by design, where each inner ratchet here is already fully proven in its own
file and unreachable from this one by a translation limit, not by
design. Stated plainly so that it does not read as a weaker proof than
intended: `RatchetAgreesFor`/`SpqrAgreesFor` hold if and only if `T3.lean`'s/
`SpqrT3.lean`'s own theorems hold of the real code, which they do, proved
elsewhere; this file cannot make Lean say so directly, so it states the same
content again as a fresh, independently-stated hypothesis rather than a
derived one.

**`receive_refines` claims the success case only, and that traces back to
`T3.lean`'s own claim, not a new gap.** `Translation/T3.lean`'s
`receive_refines` for the classical ratchet states no failure-branch fact at
all, so there is nothing for `TripleT3.lean`'s own `receive_refines` to
compose a triple-level failure claim from.

**`send_refines`'s failure branch is not symmetric between the two
ratchets.** `RatchetAgreesFor`'s send clause states a failure-implies-model-
failure fact for `NoSendingChain` only, matching `Translation/T3.lean`'s own
`send_refines` -- the theorem this bundle exists to mirror -- which proves
that fact for that one classical `RatchetError` and no other. It says nothing
about `ChainExhausted`, the real `u32` send counter wrapping, because
`Model.Ratchet.send` counts in `Nat` and has no failure mode there to
correspond to. A send clause covering *every* classical error would be
satisfiable (by a witness that lies about the ratchet's `cks` field exactly
at the exhausted state) but would not hold of the honest abstraction; a
conclusion asked of a hypothesis that ranges wider than what is provable is
an overclaim even when the bundle is true, so the clause is narrowed to what
`T3.lean` proves. `send_refines`'s own stated postcondition matches: it
proves the failure correspondence for every post-quantum error and for the
classical ratchet's `NoSendingChain` refusal, and proves nothing about a
classical `ChainExhausted` failure -- the same finite-width boundary
`T3.lean` already excludes, one layer up rather than newly introduced here.
`SpqrAgreesFor`'s analogous clause is unconditional and genuinely holds:
`hcounter` already rules out the post-quantum counter's own exhaustion.

One assumption is genuinely this crate's own: `TripleHkdfAgrees`, at the one
opaque primitive `split_secret`/`combine` call that is not just the two
ratchets' public calling surface.

**`tacenta-braid` has T1 for its whole public surface, not just its one
loop.** The eleven-state machine's `step_send` and `step_receive`, their entry
points `send`, `receive` and `commit`, and every helper the state machine
calls are proved panic-free, alongside the constant-time authenticator
comparison that is this crate's only loop. `step_receive` is the one an
attacker's header, chunk data and claimed lengths drive directly, so this is
what stands between a malformed message and a remote denial of service for
this leaf crate. Two real preconditions travel with it: a concrete size cap on
the KEM ciphertext carried across the encapsulation exchange (an invariant
`step_send` maintains but this file does not prove, since that would be a T3
claim about the whole state machine rather than a T1 one about a single
function), and an epoch counter below `2^64`, the same shape of bound the
classical ratchet and the sparse ratchet each needed for their own counters.

**`tacenta-braid` also has T3**: `step_send`/`send` and `step_receive`/
`receive` compute what `Model.Braid.send`/`Model.Braid.receive` say, across
every state and every message-type/epoch/MAC-outcome branch each can take,
not merely that they cannot fail. The KEM and the erasure coder stay opaque
boundaries (one bundled existential for the KEM, one freestanding relation
for the erasure coder, in the same trust category as the classical ratchet's
`HmacAgrees`/`HkdfAgrees` -- not a proof chained through the erasure crate's
own, separately translated T1/T3). That a completed decode is exactly as
long as the decoder was sized for is not an assumption: the model's
`Decoder.message` checks the length, as the real decoder does, and the
statement is the theorem `Model.Braid.Decoder.message_length`.

**The Braid's erasure and KEM hypotheses carry explicit bounds, and two
consequences of those bounds are limitations in their own right.**
`ErasureAgrees` demands the encoder simulation only for as many steps as a
`u16` chunk index allows (demanded for every number of steps it would be
refutable on its own); the decoder simulation is parameterised by the one
message the decoder is collecting (quantified over every model chunk sharing
a real index it would be refutable jointly with `DecoderAddChunkTotal` and
`DecoderMessageTotal`, since the real `message` gives one answer); and
`KemAgreesFor K`/`ValidateEkAgrees K` fix the header split where the model
splits it (quantified over every split of the header they would be refutable
for every `K` that models a KEM). `CLAIMS.md` has the full record of what a
reader has to grant. The two consequences that belong here:

- **Sending refines only while the encoder is live.** A real chunk index is
  sixteen bits, so an epoch's encoder is exhausted after 65,536 codewords;
  `step_send_refines` takes `EncodersLive` as a precondition and says
  nothing past that point. The real code returns no chunk there and the
  model keeps counting; the divergence is the crate's own liveness limit,
  reachable only by a peer that never replies for 65,536 sends.
- **Receiving refines only on an unspliced stream.** `HonestChunk` assumes
  the incoming chunk is a codeword of the message the decoder is collecting.
  A chunk from a different encoding, injected with a valid index, makes the
  real decoder reconstruct a wrong message that the MAC rejects, sending the
  real Braid to `Failed`, while the model's decoder -- which returns nothing
  for mixed sources -- keeps waiting. No relation makes that step refine,
  and the theorems do not claim to. In this protocol a Braid message rides
  inside the ratchet's authenticated channel, so the splice needs the
  channel's key; with it, the effect is that the session's post-quantum
  agreement fails loudly (`Error::AgreementFailed`), not that anything is
  learned.

`Translation/Satisfiability.lean` holds refutations of the unbounded shapes
of these hypotheses, so the build fails if one is restated without its bound,
and `Translation/ErasureWitness.lean` proves the erasure hypotheses have a
model over the concrete
32-byte chunk type: a Reed-Solomon code over `GF(2^256)` built from Mathlib,
which is the same maximum-distance-separable property the crate's sixteen
Reed-Solomon lanes over `GF(2^16)` provide. A model shows the hypothesis is
consistent; it does not show the crate satisfies it, which stays assumed.
`Translation/KemWitness.lean` does the same for the KEM hypotheses, jointly
with `BraidT1.lean`'s totality bounds, over the model's own `toyKem`; the
erasure witness covers `ErasureAgrees`, `ErasureCloneAgrees` and the seven
erasure totals *jointly*, since satisfiability of a hypothesis set is a joint
property and not a per-hypothesis one.

Two further consequences belong here. The model's `Decoder.message` checks
the reconstructed length, and returns the empty message for a decoder sized
for zero bytes (which the real decoder does); so a `Kem` whose operations
produce outputs of lengths other than its declared
`ekSize`/`ct1Size`/`ct2Size` -- possible for an arbitrary `Model.Braid.Kem`,
not for `toyKem` or ML-KEM -- stalls in the model. The refinement theorems
exclude such a `K` through `KemLenAgrees` and `HonestChunk`; nothing in
`Kem.Correct` does, and a whole-run composition of the Braid theorems would
need size laws on `K` (`hashEk` output 32 bytes, `keyGen` seed 32 bytes,
`encaps1`'s `ct1` of `ct1Size`, and so on) that the model does not state --
an open item, not a falsity. And the KEM agreements are guarded by the
lengths the real crate checks (`decapsulate` on `ct1Size`/`ct2Size`,
`encapsulate1` on the 64-byte header, `encapsulate2` on `ekSize`); stated
for every slice they would claim success where the crate returns an error.

Two more sit beside it in `BraidT3.lean`: `KemCloneAgrees` and
`ErasureCloneAgrees` (a clone of an opaque KEM or erasure value behaves as,
respectively is, the original), hypotheses of `Braid.receive_refines` and
`State.clone_refines`. Each is the same shape of boundary fact as the KDF
agreements.

**One reporting mismatch between the model and the code is recorded rather
than patched.** The model states only `receive_reports_le : (receive K st
msg).1 ≤ st.epoch`, an inequality. On a MAC-mismatch transition specifically,
that leading component preserves the pre-failure epoch, while the real
`Braid.receive` reports the epoch of the state it actually lands in --
`State::Failed`, whose epoch is a fixed zero -- so the two disagree whenever
a mismatch occurs above epoch one. `Braid.receive_refines` is stated and
proved against the state the real code actually reports from, not the
model's own leading `Nat`, which is why the model needed only the weaker
inequality to begin with. See `BraidT3.lean`'s own header on
`Braid.receive_refines` and `CLAIMS.md`'s braid T3 entry for the full
account.

**An assumption is per translated crate, not per operation.** `VecRemoveTotal`
is listed once below. There are two:
each translation unit declares its own opaque `alloc.vec.Vec.remove`, so the
ratchet's assumption and the sparse ratchet's are about *different constants*
and neither discharges the other. One modelling gap in Aeneas becomes one
assumption per crate that touches it. Anyone counting the trusted base by name
rather than by constant will undercount.

`VecRetainTotal` and `KdfRkTotal` join them. `VecRetainTotal` carries a length
clause as well as totality, because `set_chains` pushes after retaining and
without knowing the retain did not grow the vector there is nothing to bound the
push against.

`KdfCkTotal` and `ZeroizeTotal` are there for the same reason: the sparse
ratchet's chain-key derivation bottoms out in its own copy of the opaque
`hkdf_sha256`, and its buffer wipe in its own copy of the `Zeroize` blanket
implementation. `send` and `receive` need two more:
`OptionCloneTotal`, since both functions clone the *other* direction's chain
through an `Option`, which has no clone specification in Aeneas's own library;
and `VecAppendTotal`, since `skip_message_keys` (which `receive` calls)
concatenates the derived keys onto the retained store. **Seven assumptions in
that one file, none of them the same proposition as its namesake elsewhere.**

**So both `tacenta-spqr` and `tacenta-braid` are fully covered by T1.**
`tacenta-braid` alone assumes twenty-three named constants over twenty-three
distinct opaque operations -- the erasure coder, the KEM, the two KDF calls,
and `Option::clone` -- each a per-crate axiom Aeneas could not model, none
shared with any other crate's copy of the same operation. Several carry a
concrete size cap rather than mere headroom below `Usize.max`, because more
than one capped value gets summed at a single call site and two facts each
individually "under `Usize.max`" do not compose the way two concrete small
caps do.

**Two leaf crates proved is not the whole agreement**, since `tacenta-triple`
is the crate that actually composes them with the classical ratchet.

**`tacenta-triple` is translated, and carries its T1 proofs.**
`run-aeneas.sh` stages it alongside the other six leaf crates, and it carries
no `sorry` and no body Aeneas gave up on, the same bar the rest of this list
holds to.

**Translated is proved, too.** `State.send`, `State.receive`,
`State.commit`, and the rest of `tacenta-triple`'s public surface, all carry
T1 theorems (`TripleT1.lean`). Neither the classical ratchet's own
`receive_no_panic` nor the sparse ratchet's `send_no_panic`/`receive_no_panic`
said anything about what happens when the two are composed, and the
composition is what ships since the triple-ratchet integration -- this is that composition's
own proof. No precondition beyond totality is stated anywhere in it: this
crate never touches a vector, a chain, or a counter directly, only the two
ratchets that do, through their public calling surface, so it carries no room
or counter bound of its own to state. Nineteen opaque-operation assumptions
back it, every one a totality claim about `tacenta_ratchet.State` or
`tacenta_spqr.State` treated as opaque.

**And that is the gap.** Those nineteen are stated *unconditionally* -- "for
every state, `receive` returns" -- while the theorems in `T1.lean` and
`SpqrT1.lean` that are supposed to discharge them carry preconditions (`hs`;
`hroom`, `hepoch`, `hskiproom`, `hcounter`). The Triple T1 result therefore
rests on assumptions strictly stronger than anything proved, and unprovable
as stated in the Aeneas model. `TripleT3.lean` carries the leaf preconditions
verbatim and is not affected; restating `TripleT1.lean` the same way is open
work.

**So the session's send and receive path has a claim resting under it, at
the crate that actually carries it.** `Session::encrypt` and
`Session::decrypt` themselves live in `tacenta-core/src/sessions`, the product
code that calls `tacenta-triple`, and that layer is not translated or proved
in its own right -- a separate question this does not answer.

The proof tiers cover **seven** leaf crates, and a claim that names only the
ratchet understates what is proven while a claim that says "the protocol"
overstates it. In every crate below, "complete" and "every function" mean the
protocol functions: the persistence codecs (`from_bytes`, `to_bytes`, their
entry decoders and length helpers) and a few accessors are translated and
carry no theorem, as CLAIMS.md's "Translated is not proved" lists.

- `tacenta-core/ratchet` (`tacenta-ratchet`): the Double Ratchet state machine.
  T1, T2, T3. T3 includes `message_keys`, the expansion of a message key into
  the AEAD key, the MAC key and the IV (`message_keys_refines`, pinned); the
  codecs and accessors remain the exception.

  **Which private key is agreed with which public key at a Diffie-Hellman
  ratchet step is outside every proof and every vector.** `receive` takes the
  two agreement outputs as bytes -- `dh_out_recv` for the receiving chain,
  `dh_out_send` for the sending chain -- and so do `Model.Ratchet.receive`,
  `receive_refines` and the ratchet vectors. The choice of which key pair
  produces which output (the old pair for the receiving chain, the fresh one
  for the sending chain, as the specification requires) is made in
  `tacenta-core/src/sessions/lifecycle.rs`, which is neither translated nor
  modelled, so a swap there would pass every proof, every vector and
  `attest`. By inspection the pairing is right; a session-level test that
  drives `Session` against a model scenario is being added so that it is
  checked by running rather than by reading.
- `tacenta-core/session` (`tacenta-session`): the PQXDH derivation. T1, T2, T3.
- `tacenta-core/erasure` (`tacenta-erasure`): Reed-Solomon over GF(2^16).
  Translates with no gap, and **T1 complete for the coding functions**: the
  field arithmetic, interpolation, the chunk helpers, and both public entry
  points of each of the encoder and the decoder are proved panic-free. Not
  `Encoder::new`, `Decoder::new`, `needed`, `received`, `to_bytes` or
  `from_bytes`, which have no theorem; `Decoder::from_bytes` refuses by
  construction a restored `size` that `message()` could not serve, and that
  refusal is unproved.

  **The barycentric form.** `Encoder::next_chunk` and `Decoder::message`
  call three functions, `weights`, `coefficients` and `evaluate`, which
  compute the Lagrange coefficients once per node set and per target instead
  of re-inverting inside the innermost loop for every lane. All three carry
  T1 theorems with no hypotheses (`weights_no_panic`,
  `coefficients_no_panic`, `evaluate_no_panic` in `ErasureT1.lean`), and
  `next_chunk_no_panic` and `message_no_panic` step through those calls.
  `interpolate` remains the specification the conformance vectors and
  `interp_eq` are written against. What is *not* yet
  a theorem is the equality `interpolate(nodes, vals, x) =
  evaluate(coefficients(nodes, weights(nodes), x), vals)`: it is a test on
  random inputs (`interpolate_agrees_with_the_barycentric_form`). That
  theorem is the intended refinement target -- a plain equality in the field
  -- and once it holds the decoder's correctness argument runs through
  `interpolate` exactly as before.

  **T3 covers the field and stops there.** `add`, `clmul`, `reduce` and `mul` in
  the translated crate are proved to compute what `Model.Gf65536` says, for
  every input rather than at the thirty-eight sampled points the conformance
  vectors check. The decoder above them is not: `interpolate`, the chunk
  helpers, and the two entry points have T1 and no refinement, so the model's
  `unisolvence` is still a theorem about a Lean definition rather than about
  the code that ships. Nothing in the manifest may say otherwise until that
  gap closes.

  The refinement rests on one axiom beyond the kernel's, and only one: a
  `bv_decide` reflection in the step that relates the loop's sixteen turns to
  the model's sixteen written terms. It is pinned under `#guard_msgs` in
  `Translation/ErasureT3.lean`, so a fourth cannot appear unnoticed.

  Worth naming because this is the crate where the claim is worth most and was
  cheapest to get. A decoder consumes codewords an attacker supplies, and every
  index and length in it is computed from what they sent. The crate has no
  dependencies, so most of its theorems carry no boundary assumption at all:
  `next_chunk_no_panic` rests on `propext`, `Classical.choice` and `Quot.sound`
  and nothing else, where the ratchet's carry three.

  Two assumptions in the file, and the axiom lists say which theorems carry
  them. `usize::div_ceil` and `Vec::truncate` are both functions the translation
  does not model, so they arrive as axioms and nothing can be said about them,
  including that they return. Both are the toolchain not seeing through a core
  library function rather than a primitive we chose to trust, and neither guards
  a secret.

  A third looks like a boundary and is not. `Vec::extend_from_slice` clones
  through a `Clone` instance, which for a byte is concrete and reducible, so it
  is proved rather than assumed: an opaque-looking trait method is not
  necessarily opaque, and assuming one that is not weakens every theorem
  downstream for nothing.

  **Why `Decoder::message` reserves at the message length.** A reservation
  of `needed * CHUNK_BYTES` is `2^64` exactly for `Decoder::new(usize::MAX)`.
  Reaching it would need 2^59 stored codewords, so it is unreachable in
  practice, but nothing in the code would say so and the proof cannot use
  what the code does not say. The capacity is only a hint, so it reserves at
  the message length instead, which is the better hint of the two and cannot
  overflow.

  Indexing is written as explicit bounds checks and indexes rather than
  `get`, to make this reachable. Identical behaviour, and the difference is
  that a guarded index steps through the proof while `get` arrives as an
  opaque library call with no specification. There is no `Slice.get` anywhere
  in the translated crate. This is one of several places where the code is
  written in the form the proofs can use, and the source says so where it
  happens.

- `tacenta-core/protobuf` (`tacenta-protobuf`): the bounded wire-format reader.
  Translates with **no axioms at all**, and **T1 is complete for the parsers
  and the ratchet-body encoder** (`encode_prekey_body` has no theorem):
  the reader primitives, the two that allocate, the field set, **both message
  profiles** -- the ratchet message and the prekey envelope -- and the encoder
  are all proved to drive every byte string within the declared
  limit to an `Ok` or an `Err` and never to a failure. This is the crate where
  that matters most, because it is the only one that parses what an attacker
  sends rather than what a peer produced under a protocol.

  **T3 covers the reader primitives, the field set, and both message types
  in full.** `byte`, `varint`, `decode_tag`, `tag`, `length_delimited`
  and `admit` are proved to compute what `Model.Protobuf` says, for every
  byte string. `parse_ratchet_body` -- the length bound, the loop over
  `one_field`, leftover bytes, and each of the five missing-field refusals --
  is proved against `Model.Protobuf.parseRatchetBody`, on the accepted
  message and every refusal. `parse_prekey_body` -- the same shape, eight
  fields and seven missing-field refusals rather than five, `prekeyId`
  excluded from the check as the one optional field in either message type
  -- is proved against `Model.Protobuf.parsePrekeyBody` the same way. No
  boundary assumption anywhere in either. All nine refinement theorems are
  pinned under `#guard_msgs` in `ProtobufT3.lean`, and both parsers and the
  encoder in `ProtobufT1.lean`, to nothing beyond `propext`,
  `Classical.choice`, `Quot.sound`. Canonical
  emission and raw-byte fidelity are not proved, so **there is still no
  end-to-end claim from wire bytes to a ratchet decision** -- both because
  those two pieces are missing and because `tacenta-protobuf` is not yet
  called from the live `Session` send/receive path, which still uses the
  older fixed-width `tacenta_core::serialization` format.

  **The verified reader has no caller.** Outside its own directory
  `tacenta-protobuf` is referenced only by the `protobuf_bodies` fuzz target.
  The decoders a peer's bytes actually reach are `decode_message`,
  `decode_composite` and `decode_initial` in the root crate's
  `serialization` module, which `scripts/run-aeneas.sh` deliberately does not
  translate and which have no theorem. So the crate's T1 and T3 are a
  verified reader the product does not yet use, and a sentence anywhere that
  says refinement begins at received bytes describes the design's intent,
  not the shipping path. `decode_composite` is fixed-width and loop-free,
  already in the translatable style; moving it into a leaf crate is what
  would make the claim true.

  **Why the parser state is one struct and the loop body one call, because
  it is the transferable part.** Charon joins the branches of an `if`/`else`
  by returning every local the branches may write. With eight mutable locals
  each join would be a seven-wide tuple, bound with a pure `let (a, b, ..) :=
  x` that no stepping tactic enters, and no amount of tactic work reaches it.

  Collecting the state into one struct makes every join a single value, and
  lifting the per-turn work into its own function makes the loop body a single
  call -- and permits early returns, which Aeneas forbids inside a loop but
  not inside a function a loop calls. The translated crate contains no such
  binding anywhere. The form rather than the arithmetic is the obstacle here,
  and the diagnosis comes from reading what the translation emits rather than
  from trying tactics against it.

  **The encoder is bounded, and that is why it is total.** A `Vec` push can fail
  at the allocator, so an encoder that pushed unconditionally would be total
  only because of a fact about its callers -- a shape this repository avoids.
  `push_bounded` refuses at `MAX_MESSAGE_LEN`, so every
  encoding function is fallible and total on its own terms, and refuses exactly
  what the reader would refuse to read back.

  **T3 does not reach the encoder.** `varint_canonical` is proved about the
  *model*: every byte string the decoder accepts is exactly the encoding of what
  it decodes to. Nothing yet proves the Rust encoder computes that model's
  encoding. The public tree makes no byte-compatibility claim for the
  encoder; interoperability testing under the research boundary (ADR-0003,
  ADR-0005) is not part of this tree.

  **How the loop invariant is stated, because it is the transferable part.**
  `one_field` is proved against `Model.Protobuf.oneField`; the loop over it
  and `parse_ratchet_body` are proved by stating the invariant against turns
  *taken*, not fuel *remaining*. (Two tactic shapes are avoided in these
  proofs because they read as progress without being any: a `try` that
  consumes a goal while the proof inside it errors, and a `constructor <;>
  simp_all` that succeeds without closing, so `first` never reaches the
  alternative.) The lemma `Model.Protobuf.parseFrom_add` (running the fold
  for `n` turns and then `m` more is the same as `n + m` at once), lets the
  invariant say "the model, run for exactly as many turns as the code has
  taken so far, agrees with the real state" -- true by `rfl` at the start, and
  preserved by `one_field_refines`'s own two-part postcondition applied to one
  more turn, without needing to case on whether that turn is the one that
  refuses. `parseFrom_refused`/`parseFrom_stuck` (extra fuel changes nothing
  once refused or empty) turn this into the theorem's own claim at each of the
  loop's three exits. `parse_ratchet_body_refines` composes this with the
  length bound, the leftover-bytes check, and the five missing-field checks
  against `FieldSet.contains`/`Model.Protobuf.seen`.

  **The prekey envelope needed a second, small model rather than a
  generalization of the first.** `EnvelopeParse` nests a `body : PrekeyBody`
  field where `Parse` carries its fields flat, and `prekey_id` is optional
  where every ratchet-message field is required. `Model.PrekeyBody`,
  `EnvelopeParseState`, `oneEnvelopeField`, and `envelopeParseFrom` (with its
  own `_refused`/`_stuck`/`_add` lemmas) mirror the ratchet-message model's
  shape rather than generalizing `ParseState`/`parseFrom` to cover both: the
  existing fold and its lemmas already ship and are depended on, and a
  second, directly-analogous definition cost less than a shared abstraction
  would have. `parse_prekey_body_loop_refines`'s proof is close to a literal
  copy of `parse_ratchet_body_loop_refines`'s once stated against the new
  fold -- the turns-taken technique transferred without needing to be
  rediscovered.

  The public model is checked with synthetic and model-generated inputs.

  **The supported message profile is fully parsed.** The proofs cover the
  profile expressed in the model and implementation; the profile itself is
  determined by black-box observation under the research boundary
  (`tacenta-spec/CONSTANTS.md`).

  The verified-core design puts the wire parser inside the verified core.
  Item 5 of its contract is closed, and items 6 and 7 -- canonical emission
  and raw-byte fidelity -- are what remain of it.

What is **outside** all three, and therefore unproven by these tiers: the Diffie-Hellman
agreements, the KEM, the signature check, the prekey stores, randomness, session
persistence, and every orchestration path in `tacenta-core` that joins them. The
session zone holds the derivation PQXDH itself contributes, not the handshake.

The session zone's assumptions differ from the ratchet's in two ways worth
stating rather than folding into the general list:

- **`ZeroizingModel`** is stronger than the ratchet's `ZeroizingTotal`. Totality
  is enough when the wrapper is used once; the derivation writes through it
  twice and a length has to travel between the writes, so the assumption says
  the wrapper is a transparent container rather than only that its operations
  return. It is a class so that instance resolution can supply it to stepping
  rules whose postconditions mention it.
- **No `VecRemoveTotal` analogue.** `Vec::extend_from_slice` is modelled by the
  Aeneas library rather than left an axiom, so this zone adds no trusted
  boundary that nobody chose. The ratchet's does.
- **Two `native_decide` uses reach the theorem**, for the constant comparisons: that the domain
  separator and the parameter label written as Rust byte strings are the ones
  the model writes as lists of code points. Decided by evaluation, so they trust
  the compiler and not only the kernel. They are listed in the audited axiom
  set in `Translation/SessionT3.lean`, which is where that becomes visible.

## The erasure coding's field is proved

`Model.Gf65536` implements GF(2^16), which the post-quantum agreement's chunking
is defined over. It is a proved field, not a probable one.

**Proved for every input.** The additive laws, commutativity, distributivity on
both sides, and associativity.

**Established by exhaustion.** That every nonzero element has the inverse `inv`
returns, all sixty-five thousand five hundred and thirty-five. This doubles as an
irreducibility check on the reduction polynomial, since a reducible one would
leave some nonzero element a zero divisor with no inverse to return. Verified
live by substituting a reducible polynomial and watching it fail.

The one thing still assumed is the reduction polynomial itself, which is ours
rather than the specification's: the published document fixes the field and not
which irreducible polynomial defines it, so it is wire-sensitive in the way the
derivation labels are and is recorded in the conformance manifest.

The rule that governs the solver here is worth carrying to any future work
with it: **it settles statements mentioning one product and none mentioning
two.** Every call in that file has
a single product with the other factor constant, and the general laws are
assembled from those by linearity. `Model.Gf65536.linear_ext` -- a linear map is
determined by its values on the sixteen basis elements -- is the piece that makes
that assembly possible.

## Not yet proven

- T1 (panic-freedom and memory safety of the core's verified zone via the
  Charon and Aeneas translation) **is proven**, under the stated assumptions and
  for the verified zone only, which is the seven leaf crates and not the
  product. The assumptions it rests on are not all ones anybody chose. Where
  it stands, precisely:
  - **The ratchet, the verified zone, translates.** Charon extracts and Aeneas
    translates the ratchet functions with the primitives opaque at the boundary.
  - **The verified zone is isolated, and it translates.** The ratchet and
    the key derivation it calls live in their own leaf crate,
    `tacenta-core/ratchet` (`tacenta-ratchet`), whose only dependencies are the
    trusted primitive boundary. `scripts/run-aeneas.sh` translates that crate,
    not all of tacenta-core, and the run is clean: Charon extracts it and Aeneas
    translates every transparent function, with the primitives opaque.
    A whole-crate run would fail on constructs Aeneas does not model, all of
    them in orchestration rather than in the ratchet (a closure in
    `create_prekeys`, a slice pattern in `message_type`, a generated-name clash
    on the lifecycle `Error`). Isolating the zone makes the translated surface
    exactly the surface intended for proof, and keeps orchestration free to use
    ordinary Rust.
  - **Counter arithmetic is total by construction.** The message counters
    (`ns`, `nr`) use `checked_add` and return `ChainExhausted`, rather than
    incrementing without bound, which would overflow after 2^32 messages on
    one chain (a panic in a checked build); so that arithmetic is panic-free
    without an unprovable bound. `derive_chain`'s `start_n + i` is bounded
    below `upto` by its caller's checks and is safe by that invariant.
  - **The Lean environment is provisioned.** `tacenta-proofs/translation/` is a
    lake package for the translated code, kept separate from `Proofs/` so the
    functional-property proofs stay fast and Mathlib-free. Mathlib is fetched
    prebuilt with `lake exe cache get` (not compiled), and that fetch succeeds,
    so the build reaches and elaborates the generated file.
  - **`?` is banned in the verified zone.** The operator desugars through the
    `Try` trait, which the translation emits as universe-polymorphic
    definitions that fail to typecheck (`Result.{0}` where `Result.{1}` is
    expected). The ratchet uses `let`-`else` and explicit `if let Err(..)`,
    with `clippy::question_mark` allowed crate-wide because the lint asks for
    precisely the construct that breaks the proof. This is a property of the
    toolchain rather than of this codebase.
  - **No field is named `mk`.** `mk` is the name Lean gives a structure's
    auto-generated constructor. A struct field of that name (the shape a
    nine-line dependency-free reproducer isolates) has its projection
    rejected, the structure stops elaborating, and everything containing it
    is pushed to `Type 1`, which surfaces as `Result.{0}` against `Result.{1}`
    universe mismatches far from the cause. `SkippedKey`'s key field is
    therefore named `key`. The reproducer, its control, and a drafted upstream
    issue are in `upstream/aeneas-mk-field-collision/`.
  - **The trusted primitives are opaque, and the translation builds.** The
    key derivation is its own crate, `tacenta-core/kdf` (`tacenta-kdf`), which
    puts it outside the translated package and therefore opaque:
    `hkdf_sha256` and `hmac_sha256` appear in the generated Lean as axioms,
    which is what a trusted boundary should look like in a proof. Inside the
    leaf crate it would make the translation elaborate RustCrypto's trait
    hierarchy (`FixedOutputCore`, the typenum-encoded block sizes), which
    does not go through. The generated file is 1,127 lines rather than the
    57,272 that hierarchy would add, contains no RustCrypto machinery at
    all, and **`lake build` on it succeeds**, from the git-pinned Aeneas
    library rather than a local path.
  - **T1 is complete for the verified zone's protocol functions** (the
    persistence codecs and accessors listed under "Translated is not proved"
    in CLAIMS.md are translated and unproved). Every protocol function in it is proven
    panic-free: the chain-key and root-key steps, sending, the chain-derivation
    and skip loops with their wrappers, the skipped-key scan, the DH ratchet
    step, and `receive`, which composes the rest. There is no `sorry`, and a
    `#guard_msgs` audit pins the chain-key step, `send` and `receive` to an
    explicit axiom list, so a later change that smuggled in an
    assumption would fail the build rather than pass quietly.

    Two things are worth stating precisely, because "panic-free" on its own
    would overstate them.

    First, **what the proofs rest on.** Nothing about our own code is assumed.
    Three boundaries are, each a named hypothesis: `HmacTotal` and `HkdfTotal`
    for the key-derivation primitives, which are opaque by design; `ZeroizingTotal`
    for the external `zeroize` crate, whose wrapper and projection cannot fail;
    and `VecRemoveTotal`, which is a gap in what Aeneas models rather than a
    choice, discussed below. The `zeroize` boundary is the reminder that every
    external crate on a proven path becomes an assumption whether or not
    anyone intended it.

    Second, **`receive` carries a precondition, and it is a real one.** The
    skipped-key store must be small enough that its length plus the whole `u32`
    range still fits a `usize`, measured at the largest the store can reach.
    On a 64-bit target any store that could exist satisfies it. On a 32-bit
    target it does not hold automatically, because Aeneas models `usize` at the
    platform width, so the statement keeps it as a hypothesis rather than
    discharging it. A caller on a 32-bit platform is owed that check.

    Third, **the refinement of `receive` also assumes the store's clock has
    room.** Skipped-key expiry counts received messages, in `u32` in the core
    and in the naturals in the model. They agree until the counter reaches
    `u32::MAX`, where the core saturates and the model does not, so the
    refinement is stated below that point and says nothing at or past it. What
    the core does there is documented and safe rather than unspecified: a
    saturated counter expires every skipped key immediately, which loses
    out-of-order messages and leaks nothing. It is the same finite-width
    boundary the message counters already carry, and it is worth restating that
    a bound of this kind is not a formality: `receive` is the function an
    attacker drives.

- **Unmodelled standard-library operations are a recurring hazard.** Aeneas
  leaves several `core`/`alloc` operations as axioms, and each one that lands on
  a path we want to prove becomes an assumption rather than a theorem. The
  branch test compares arrays rather than `Option`s for that reason, since the
  translation models the array comparison and not the `Option` one. The one
  that remains is below, and should go the same way.

- **A trusted boundary that is not a deliberate one.**
  `Vec::remove` reaches the generated Lean as an axiom, because Aeneas does not
  model it, so the skipped-key scan's proofs carry `VecRemoveTotal` as a stated
  hypothesis, which also asserts that removing an element does not lengthen
  the vector. Rust's `Vec::remove` panics only on an out-of-bounds index, which
  the scan's own length check rules out, and it plainly shortens the vector.
  **The hypothesis as stated does not carry that bound** -- it is `∀ i`, so it
  is not true of Rust for an out-of-range index; it is sound *as used*,
  because every call site checks `i < len` first, and tightening it to
  `i.val < v.length →` is open work. It carries an `[Inhabited T]` bound so
  that it is consistent: quantified over every element type, at `T := Empty`
  it would ask for an element of an empty type, imply `False`, and make the
  ratchet's `receive_refines` provable for nothing.
  `Translation/Satisfiability.lean` holds a model of it and a refutation of
  the unbounded shape, so the build fails if the bound is dropped.
  It is still
  worth removing: unlike the HMAC, this is a standard-library operation rather
  than a chosen primitive, and the verified zone should not rest on something
  the translation cannot see into. Removing the dependency in the Rust would be
  the same move as making `derive_chain`'s arithmetic total.

- **The skipped-key store is a map, and storing replaces rather than
  accumulates.** The header carries the ratchet public key, so the peer
  chooses it, and nothing requires it to be one not seen before: a peer that
  leaves a key and returns to it gets a fresh chain numbered from zero under a
  ratchet key already in the store. A store that accumulated would then hold
  colliding entries with *different* keys, the second unreachable -- never
  found, never deleted, holding a slot against the store cap -- while a
  genuine later message on that chain was answered with the other key. So
  storing replaces, in both the model and the core, and
  `tacenta-model/Properties/Invariants.lean` asserts the property as a
  regression test, so losing it fails the build.

  Two costs worth stating. The core carries a purge scan inside the verified
  zone, which the translation contains and T1 covers, including its loop. And
  T3's refinement of the skip step has to relate both sides through that
  scan; `Translation/T3.lean` records what that needs.

- **`VecRemoveTotal` states three things, and wants a fourth.** It states
  totality, that removal does not lengthen the vector, and that removing an
  index in range shortens the vector by exactly one, which the purge scan
  needs because it removes without advancing its index
  and so has nothing else to make its measure decrease. The honest end point is
  to state the operation's semantics outright, that removal returns the element
  and the list with that index erased; the length facts would then be derived
  rather than assumed piecemeal, and T3's purge refinement needs it anyway. This
  is the recurring shape of the whole exercise: T1 needed only that an
  unmodelled operation returns, and refinement needs to know what it returned.

- **The label set is a parameter of the verified zone.** The KDF `info`
  labels are a choice rather than a computation, so they are a `LabelSet`
  carried in the state
  and threaded through the derivations, in the core, the model and the
  refinement relation. Message-layer wire compatibility is not attempted;
  carrying the label set in the state keeps a later change from costing a
  migration.

  The constraint worth carrying: **a function returning `&'static [u8]` does not
  translate.** Charon and Aeneas give up on any body that calls one, and it has
  nothing to do with enums, matches or threading, all of which are fine. Select
  the labels with a `match` bound to a `let` **inside** the function that uses
  them. Aeneas keeps the parameter and constant-folds the one-variant match, so
  the generated `kdf_rk` takes the label set and uses the constant.

  Aeneas exits non-zero when it gives up, and it also writes a partial file
  with `sorry` in place of the body at the destination path. A staging step
  that copied that over the good file would leave the proofs building green
  against an artefact that no longer matched the source, so
  `scripts/run-aeneas.sh` refuses to stage a file containing `sorry`. Use its
  exit code; do not grep its output, which is ANSI-coloured and easy to
  mis-match.

- **Panic-freedom alone does not compose, and that shaped the whole of T1.**
  The leaf proofs each stand on their own, but no caller could be closed from
  them: entering the store loop needs to know how many keys the chain derivation
  produced, and a postcondition of "it did not panic" says nothing about that.
  Closing T1 meant strengthening each function to state what it *produced*: the
  chain's length, the store's bound after skipping, that the scan never grows the
  store, that the DH ratchet leaves it untouched. That is functional-property
  work of the kind T2 does, rather than more panic-freedom reasoning. Anyone
  reading the theorem list should expect that shape: the panic-freedom results
  are the visible part, and the postconditions carrying them are most of the
  work.

- T3 (refinement: the core's ratchet step refines the model's) **is proven**
  for every protocol operation the model defines -- both key-derivation
  steps, the message-key expansion, both initialisers, `send`, the
  Diffie-Hellman step, chain derivation, the skip step with its purge scan,
  the skipped-key lookup, and `receive` -- with no `sorry`. The persistence
  codecs and the small accessors are translated and have no refinement
  theorem, as `CLAIMS.md`'s "translated is not proved" lists. It holds modulo
  agreement of the opaque key-derivation primitives, which is the same
  deliberate boundary T1 rests on and is not closed by anything in Lean: the
  model-generated byte vectors are what covers it. It also excludes the cases
  where the Rust's `u32` counters and the model's `Nat` part company, which are
  real behaviours rather than gaps in the proof. The isolated-verified-zone
  translation it needs is in place, and it depends on the same Mathlib-backed
  Lean environment as T1. The vectors generated from the model give byte-level
  conformance evidence across the boundary it does not close.
- The security properties are formalised against a symbolic attacker and not
  against a computational one, which the forward-secrecy section above states in
  full.

## Waiting on the next re-translation window

A source change inside a translated crate is a change to the generated Lean,
which only the pinned Aeneas release in the verification workflow can regenerate,
and the T1/T3 proofs over the regenerated code have to be re-stepped. So
changes that live inside `spqr`, `braid` or the other verified zones are
batched into one re-translation rather than made one at a time, and the open
ones are listed here so nobody mistakes "not yet" for "not known":

- `tacenta_spqr::State::to_bytes` and `tacenta_braid::Braid::to_bytes` grow
  their buffer by pushing (see "Secret deletion is partial").
- `tacenta_braid`'s `mac_eq` is a hand-written comparison loop (see
  "Constant-time behaviour is assumed, not proven").
- `tacenta_braid::Auth::keys` is a public accessor returning the root and MAC
  keys, used only by tests; it should be `#[cfg(test)]`.
- The Braid computes `epoch + 1` unchecked in two places, so a persisted
  state carrying `u64::MAX` panics on the next receive under
  `overflow-checks = true`; the sparse ratchet uses `checked_add` for the
  same shape. Reachable only through `from_bytes` on a hostile blob, which is
  already outside the T1 theorems' preconditions.

## Scope

**One-to-one sessions are implemented. Group messaging and multi-device are
not.** `tacenta-spec/protocol/group-messaging.md` and `multi-device.md` are
outline pages, `Model/MultiDevice.lean` is a stub, and there is no sender-key
implementation anywhere in the core.

Also not implemented, and listed here because a reader comparing this to
libsignal will look for them: persistent storage, platform bindings, and an
identity trust store are not in this crate at all. A caller is handed the
peer's identity key and is expected to remember and compare it, which is a
much easier interface to misuse than an address-keyed store that does it for
them.

**The post-quantum ratchet is in the session.** `Session` holds `triple:
tacenta_triple::State` and `braid: tacenta_braid::Braid` directly, rather
than a classical-only `ratchet::State`, and `encrypt`/`decrypt` drive both
halves as one transaction. So healing after a compromise does not rest on the
classical agreement alone.

What is *not* done for that integration is separate and open: proofs about
`Session::encrypt`/`Session::decrypt` themselves, the orchestration around
the crates. `TripleT1.lean` and `TripleT3.lean` cover the composition; only
the session-layer orchestration remains uncovered.

Optional variants such as the Double Ratchet's header-encryption mode are out of
scope and recorded in the conformance manifest.

The distinction that matters: *implemented* is not *specified*
is not *proved*, and this document has to keep the three apart. An outline page
is not an implementation, and a passing test on an isolated crate is not a
feature of the library.
